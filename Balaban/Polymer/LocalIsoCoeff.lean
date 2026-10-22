/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Polymer.LocalIsoBridge
public import Balaban.Fluctuation.NewLevelCoeffLoc
import Mathlib.Tactic.Linarith

/-!
# Local generating sets on two tori: the local formula of the coefficient

The coefficient of a polymer recomputed from the labels inside it (`newLevelCoeffLoc`) is the
determinant part plus the interpolation integral of the activities of the labels inside the polymer
at the configuration restricted to their blocks (`locAct`) and the marks of the anchors inside the
polymer at the configuration restricted to the blocks of their label (`truncMark`).  On two tori:

* `Gsum_fun_transport`: the transport of the sum of the local terms of the marked cluster expansion
  (`gsumCoeff_transport` at one value of the interpolation parameter) for activities and marks given
  as functions with their locality;
* `locAct_dep`: the activities of the labels inside the polymer depend only on the blocks of their
  label;
* `relBox_restrConf`: block variables corresponding at the unit points of the box stay
  corresponding after the restriction to a set of blocks of the box and to its image (with
  corresponding reference configurations);
* `newLevelCoeffLoc_twoTorus`: the local formulas of the steps `hatStepKG` on two tori agree for a
  polymer of the box and its image, when the determinant parts agree, the active labels and the
  anchors of the polymer correspond, and their activities and marks agree at block variables
  corresponding at the unit points of the box.
-/

@[expose] public section

noncomputable section

open scoped Classical

namespace Balaban.Polymer.LocalIso

open Balaban Balaban.Localization Balaban.Background Balaban.Multiscale Balaban.Polymer
  Balaban.Polymer.TwoTorusStep Balaban.Fluctuation Balaban.SmallField Balaban.SmallField.Def6
  Balaban.Analysis Matrix MeasureTheory

section GsumFun

variable {d L N₁ N₁' m₁ K : ℕ} [NeZero L] [NeZero N₁] [NeZero N₁'] {m₀ j : ℕ}
  {Ω : Set (CTorus d L N₁ m₁ K)} {Ω' : Set (CTorus d L N₁' m₁ K)}
  {Lb Lb' : Type*} [Fintype Lb] [Fintype Lb']

local notation "𝔅" => CubeB (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ j Ω
local notation "𝔅'" => CubeB (L := L) (N₁ := N₁') (m₁ := m₁) (K := K) m₀ j Ω'

/-- **The sum of the local terms of the marked cluster expansion on two tori**, for activities and
marks given as functions (`gsumCoeff_transport` at one value of the interpolation parameter):
the correspondence `ψ` of the active labels, `κ` of the anchors with blocks in `T`, the agreement
of the activities and marks at related configurations, and the transport of the integrals of
functions of the blocks of `T` (`hint`). -/
theorem Gsum_fun_transport {Ωb : 𝔅 → Type*} [∀ b, MeasurableSpace (Ωb b)]
    {Ωb' : 𝔅' → Type*} [∀ b, MeasurableSpace (Ωb' b)]
    (μ : ∀ b, Measure (Ωb b)) [∀ b, IsProbabilityMeasure (μ b)]
    (μ' : ∀ b, Measure (Ωb' b)) [∀ b, IsProbabilityMeasure (μ' b)]
    (Lab : CubeLabels m₀ j Ω Lb) (Lab' : CubeLabels m₀ j Ω' Lb')
    (H : Lb → (∀ b, Ωb b) → ℂ) (H' : Lb' → (∀ b, Ωb' b) → ℂ)
    (hHdep : ∀ y, DepOn (blocksOf m₀ j Ω (Lab.ysite y)) (H y))
    {ι ι' : Type*} [Fintype ι] [Fintype ι'] (y0 : ι → Lb) (y0' : ι' → Lb')
    (G : ι → (∀ b, Ωb b) → ℂ) (G' : ι' → (∀ b, Ωb' b) → ℂ)
    (hGdep : ∀ i, DepOn (blocksOf m₀ j Ω (Lab.ysite (y0 i))) (G i))
    (σ : 𝔅 → 𝔅') (T : Finset 𝔅) (hσ : Set.InjOn σ (T : Set 𝔅))
    (Rel : (∀ b, Ωb b) → (∀ b, Ωb' b) → Prop)
    (hint : ∀ Z ⊆ T, ∀ (F : (∀ b, Ωb b) → ℂ) (F' : (∀ b, Ωb' b) → ℂ), DepOn Z F →
      (∀ Φ Φ', Rel Φ Φ' → F' Φ' = F Φ) →
        ∫ Φ', F' Φ' ∂(Measure.pi μ') = ∫ Φ, F Φ ∂(Measure.pi μ))
    (P : Lb → Prop) (P' : Lb' → Prop) (hH0 : ∀ y, ¬ P y → ∀ Φ, H y Φ = 0)
    (hH0' : ∀ y', ¬ P' y' → ∀ Φ', H' y' Φ' = 0)
    (ψ : ∀ y, P y → blocksOf m₀ j Ω (Lab.ysite y) ⊆ T → Lb')
    (hψP : ∀ y hP hy, P' (ψ y hP hy))
    (hψb : ∀ y hP hy, blocksOf m₀ j Ω' (Lab'.ysite (ψ y hP hy)) =
      (blocksOf m₀ j Ω (Lab.ysite y)).image σ)
    (hψinj : ∀ y₁ hP₁ hy₁ y₂ hP₂ hy₂, ψ y₁ hP₁ hy₁ = ψ y₂ hP₂ hy₂ → y₁ = y₂)
    (hψsurj : ∀ y', P' y' → blocksOf m₀ j Ω' (Lab'.ysite y') ⊆ T.image σ →
      ∃ y hP hy, ψ y hP hy = y')
    (hH : ∀ y hP hy, ∀ Φ Φ', Rel Φ Φ' → H' (ψ y hP hy) Φ' = H y Φ)
    (κ : ∀ i, blocksOf m₀ j Ω (Lab.ysite (y0 i)) ⊆ T → ι')
    (hκb : ∀ i hi, blocksOf m₀ j Ω' (Lab'.ysite (y0' (κ i hi))) =
      (blocksOf m₀ j Ω (Lab.ysite (y0 i))).image σ)
    (hκinj : ∀ i₁ hi₁ i₂ hi₂, κ i₁ hi₁ = κ i₂ hi₂ → i₁ = i₂)
    (hκsurj : ∀ i', blocksOf m₀ j Ω' (Lab'.ysite (y0' i')) ⊆ T.image σ → ∃ i hi, κ i hi = i')
    (hG : ∀ i hi, ∀ Φ Φ', Rel Φ Φ' → G' (κ i hi) Φ' = G i Φ) :
    Gsum μ' Lab' H' y0' G' (T.image σ) = Gsum μ Lab H y0 G T := by
  classical
  unfold Gsum
  rw [← Finset.sum_filter_of_ne (p := fun i' => blocksOf m₀ j Ω' (Lab'.ysite (y0' i')) ⊆ T.image σ)
    (fun i' _ h => by_contra fun hn => h (Gst_eq_zero_of_not_subset _ _ _ _ hn)),
    ← Finset.sum_filter_of_ne (p := fun i => blocksOf m₀ j Ω (Lab.ysite (y0 i)) ⊆ T)
    (fun i _ h => by_contra fun hn => h (Gst_eq_zero_of_not_subset _ _ _ _ hn))]
  symm
  refine Finset.sum_bij (fun i hi => κ i (Finset.mem_filter.1 hi).2) (fun i hi => ?_)
    (fun i₁ hi₁ i₂ hi₂ h => hκinj i₁ _ i₂ _ h) (fun i' hi' => ?_) (fun i hi => ?_)
  · have hiT := (Finset.mem_filter.1 hi).2
    refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩
    rw [hκb i hiT]
    exact Finset.image_subset_image hiT
  · obtain ⟨i, hiT, rfl⟩ := hκsurj i' (Finset.mem_filter.1 hi').2
    exact ⟨i, Finset.mem_filter.2 ⟨Finset.mem_univ _, hiT⟩, rfl⟩
  · have hiT := (Finset.mem_filter.1 hi).2
    show Gst μ Lab H (blocksOf m₀ j Ω (Lab.ysite (y0 i))) (G i) T =
      Gst μ' Lab' H' (blocksOf m₀ j Ω' (Lab'.ysite (y0' (κ i hiT)))) (G' (κ i hiT)) (T.image σ)
    rw [hκb i hiT]
    exact (Gst_transport μ μ' Lab Lab' H H' hHdep σ T hσ Rel hint P P' hH0 hH0' ψ hψP hψb hψinj
      hψsurj hH hiT (hGdep i) (hG i hiT)).symm

end GsumFun

section Loc

variable {d L N₁ m₁ k : ℕ} [NeZero L] [NeZero N₁]

local notation "𝔅" => CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) 1 (k + 1)
  Set.univ

/-- **The activities of the labels inside a polymer depend only on the blocks of their label.** -/
theorem locAct_dep {Ωb : 𝔅 → Type*} {Lb E : Type*}
    (Lab : CubeLabels (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) 1 (k + 1) Set.univ Lb)
    (T : Finset 𝔅) (Φ₀ : ∀ b, Ωb b) (H : E → ℂ → Lb → (∀ b, Ωb b) → ℂ) (θ : E) (u : ℂ)
    (y : Lb) : DepOn (blocksOf 1 (k + 1) Set.univ (Lab.ysite y)) (locAct Lab T Φ₀ H θ u y) := by
  intro Φ Φ' h
  by_cases hy : InPoly T (Lab.ysite y)
  · rw [locAct_of_pos Lab Φ₀ H θ u hy, locAct_of_pos Lab Φ₀ H θ u hy]
    exact congrArg (H θ u y) (restrConf_eq_of_agree Φ₀ h)
  · rw [locAct_of_neg Lab Φ₀ H θ u hy, locAct_of_neg Lab Φ₀ H θ u hy]

end Loc

section Steps

open Balaban.Inhabited.LevelStep

variable {d L N₁ N₁' m₁ k N : ℕ} [NeZero N₁] [NeZero N₁'] [NeZero L] {ϱ : ℝ}

set_option hygiene false in
local notation "bk" => boxMap ((N₁ * L ^ m₁) * L ^ (k + 1)) ((N₁' * L ^ m₁) * L ^ (k + 1))
set_option hygiene false in
local notation "GA" => levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ)
  (k + 1) le_rfl
set_option hygiene false in
local notation "GB" => levelGS (d := d) (L := L) (N₁ := N₁') (m₁ := m₁) (k := k + 1) (ϱ := ϱ)
  (k + 1) le_rfl
set_option hygiene false in
local notation "SA" => hatStepKG (d := d) (L := L) (N := N) (N₁ := N₁) hN2 k m₁ ϱ hk νS β p₁ δ
set_option hygiene false in
local notation "SB" => hatStepKG (d := d) (L := L) (N := N) (N₁ := N₁') hN2 k m₁ ϱ hk νS β p₁ δ
set_option hygiene false in
local notation "𝔅A" => CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) 1 (k + 1)
  Set.univ
set_option hygiene false in
local notation "σc" => cubeMap (d := d) (L := L) (N₁ := N₁) (N₁' := N₁') (m₁ := m₁) (K := k + 1)
  (m₀ := 1) hN hN' (le_refl (k + 1))
set_option hygiene false in
local notation "aK" => cellSide L 1 m₁ (k + 1)

/-- **The cube of the unit point of the image of a site**: `cubeMap` of the cube of the site, for a
site of the box of radius `R` (margins with the cube side). -/
theorem cellOf_unitPt_boxMap (hN2 : 2 ≤ N) (hk : 1 ≤ k) (νS β p₁ δ : ℝ) (hN : L ^ 1 ∣ N₁)
    (hN' : L ^ 1 ∣ N₁') {R : ℕ} (hn : 2 * (R + aK) + 1 < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hnc : 2 * (R + aK) + aK < (N₁ * L ^ m₁) * L ^ (k + 1))
    {x : CTorus d L N₁ m₁ (k + 1)} (hx : InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x) :
    (SB).cellOf 1 (unitPt (SB).hG' (bk x)) = σc ((SA).cellOf 1 (unitPt (SA).hG' x)) := by
  rw [(SB).cellOf_unitPt 1 (bk x), (SA).cellOf_unitPt 1 x]
  apply Subtype.ext
  rw [TwoTorusStep.cubeMap_val]
  show cbase aK (bk x) = bk (cbase aK x)
  exact (cbase_boxMap (cellSide_dvd (K := k + 1) (m₁ := m₁) hN le_rfl)
    (cellSide_dvd (K := k + 1) (m₁ := m₁) hN' le_rfl) (cellSide_pos 1 m₁ _) hnc x
    (fun y hy => inBox_of_mem_cell hn hx hy)).symm

/-- **Corresponding block variables stay corresponding after restriction.**  If `Φ`, `Φ'` and the
reference configurations `Φ₀`, `Φ₀'` correspond at the unit points of the box of radius `R`, so do
the restrictions of `Φ` to a set `B` of cubes of the box and of `Φ'` to `cubeMap '' B`. -/
theorem relBox_restrConf (hN2 : 2 ≤ N) (hk : 1 ≤ k) (νS β p₁ δ : ℝ) (hN : L ^ 1 ∣ N₁)
    (hN' : L ^ 1 ∣ N₁') {R : ℕ} (hn : 2 * (R + aK) + 1 < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hnc : 2 * (R + aK) + aK < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hn' : 2 * (R + aK) + 1 < (N₁' * L ^ m₁) * L ^ (k + 1))
    (hp : 0 < (SA).p₁) (hp' : 0 < (SB).p₁) {B : Finset (𝔅A)}
    (hB : ∀ b ∈ B, ∀ x ∈ box b.1 aK, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x)
    {Φ Φ₀ : ∀ c, ((SA).blockSplit 1 hp).Ωb c} {Φ' Φ₀' : ∀ c, ((SB).blockSplit 1 hp').Ωb c}
    (hΦ : ∀ x, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x →
      Φ' ((SB).cellOf 1 (unitPt (SB).hG' (bk x))) ⟨unitPt (SB).hG' (bk x), rfl⟩ =
        Φ ((SA).cellOf 1 (unitPt (SA).hG' x)) ⟨unitPt (SA).hG' x, rfl⟩)
    (hΦ₀ : ∀ x, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x →
      Φ₀' ((SB).cellOf 1 (unitPt (SB).hG' (bk x))) ⟨unitPt (SB).hG' (bk x), rfl⟩ =
        Φ₀ ((SA).cellOf 1 (unitPt (SA).hG' x)) ⟨unitPt (SA).hG' x, rfl⟩) :
    ∀ x, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x →
      restrConf (B.image σc) Φ₀' Φ' ((SB).cellOf 1 (unitPt (SB).hG' (bk x)))
          ⟨unitPt (SB).hG' (bk x), rfl⟩ =
        restrConf B Φ₀ Φ ((SA).cellOf 1 (unitPt (SA).hG' x)) ⟨unitPt (SA).hG' x, rfl⟩ := by
  intro x hx
  have hc := cellOf_unitPt_boxMap (ϱ := ϱ) hN2 hk νS β p₁ δ hN hN' hn hnc hx
  have hcR : ∀ y ∈ box ((SA).cellOf 1 (unitPt (SA).hG' x)).1 aK,
      InBox d (R + aK) ((N₁ * L ^ m₁) * L ^ (k + 1)) y := by
    intro y hy
    rw [(SA).cellOf_unitPt 1 x] at hy
    exact inBox_of_mem_cell hn hx hy
  have hmem : (SB).cellOf 1 (unitPt (SB).hG' (bk x)) ∈ B.image σc ↔
      (SA).cellOf 1 (unitPt (SA).hG' x) ∈ B := by
    rw [hc]
    constructor
    · intro h
      obtain ⟨b, hb, hbe⟩ := Finset.mem_image.1 h
      have hbR := hB b hb b.1 (mem_box_self _ (cellSide_pos 1 m₁ (k + 1)))
      have hcR' := hcR _ (mem_box_self _ (cellSide_pos 1 m₁ (k + 1)))
      have h1 := congrArg Subtype.val hbe
      rw [TwoTorusStep.cubeMap_val, TwoTorusStep.cubeMap_val] at h1
      have : b = (SA).cellOf 1 (unitPt (SA).hG' x) :=
        Subtype.ext (boxMap_inj (hm' := (by omega : 2 * (R + aK) + 1 < (N₁' * L ^ m₁) * L ^ (k + 1)))
          (inBox_mono (by omega) hbR) hcR' h1)
      rw [← this]
      exact hb
    · intro h
      exact Finset.mem_image_of_mem _ h
  unfold restrConf
  by_cases hin : (SA).cellOf 1 (unitPt (SA).hG' x) ∈ B
  · have hin' := hmem.2 hin
    simp only [hin, hin', ↓reduceIte]
    exact hΦ x hx
  · have hin' : (SB).cellOf 1 (unitPt (SB).hG' (bk x)) ∉ B.image σc := fun h => hin (hmem.1 h)
    simp only [hin, hin', ↓reduceIte]
    exact hΦ₀ x hx


/-- **The local formulas of the coefficient on two tori** (steps `hatStepKG`).  For a polymer `T` of
the box of radius `R` and its image: if the determinant parts agree (`hdet`), the reference
configurations correspond at the unit points of the box (`hΦ₀`), the active labels `P` (outside of
which the activities vanish) with blocks in `T` correspond by `ψ` to those of the second torus with
blocks in `cubeMap '' T`, the anchors with blocks in `T` by `κ`, and the activities and marks agree
at block variables corresponding at the unit points of the box (`hA`, `hG`; for `s ∈ [0, 1]`), then
the local formulas `newLevelCoeffLoc` agree. -/
theorem newLevelCoeffLoc_twoTorus (hN2 : 2 ≤ N) (hk : 1 ≤ k) (νS β p₁ δ : ℝ) (hN : L ^ 1 ∣ N₁)
    (hN' : L ^ 1 ∣ N₁') {R : ℕ}
    (hn : 2 * (R + aK) + 3 * L ^ (k + 1) + 5 < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hn' : 2 * (R + aK) + 3 * L ^ (k + 1) + 5 < (N₁' * L ^ m₁) * L ^ (k + 1))
    (hnc : 2 * (R + aK) + aK < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hGA : IsLevel (GA) (k + 1)) (hGB : IsLevel (GB) (k + 1))
    (hp : 0 < (SA).p₁) (hp' : 0 < (SB).p₁) {ϱb ϱb' : ℝ}
    {Gb : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱb}
    {Gb' : GeneratingSet d L (N₁' * L ^ m₁) (k + 1) ϱb'}
    {Lb Lb' : Type*} [Fintype Lb] [Fintype Lb']
    (Lab : CubeLabels (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) 1 (k + 1) Set.univ Lb)
    (Lab' : CubeLabels (d := d) (L := L) (N₁ := N₁') (m₁ := m₁) (K := k + 1) 1 (k + 1) Set.univ
      Lb')
    {ι ι' : Type*} [Fintype ι] [Fintype ι'] (y0 : ι → Lb) (y0' : ι' → Lb')
    (a : ℕ → ℝ) (aT ν ρb : ℝ) (Zb : Finset (unitPts Gb)) (Zb' : Finset (unitPts Gb'))
    (Φ₀ : ∀ c, ((SA).blockSplit 1 hp).Ωb c) (Φ₀' : ∀ c, ((SB).blockSplit 1 hp').Ωb c)
    (H : physParamBg N Gb → ℂ → Lb → (∀ c, ((SA).blockSplit 1 hp).Ωb c) → ℂ)
    (H' : physParamBg N Gb' → ℂ → Lb' → (∀ c, ((SB).blockSplit 1 hp').Ωb c) → ℂ)
    (G : physParamBg N Gb → ι → ℂ → (∀ c, ((SA).blockSplit 1 hp).Ωb c) → ℂ)
    (G' : physParamBg N Gb' → ι' → ℂ → (∀ c, ((SB).blockSplit 1 hp').Ωb c) → ℂ)
    (θ : physParamBg N Gb) (θ' : physParamBg N Gb') (T : Finset (𝔅A))
    (hT : ∀ b ∈ T, ∀ x ∈ box b.1 aK, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x)
    (hdet : newLevelDetBg Gb' a aT ν ρb Zb' θ' (T.image σc) = newLevelDetBg Gb a aT ν ρb Zb θ T)
    (hΦ₀ : (∀ x, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x →
        Φ₀' ((SB).cellOf 1 (unitPt (SB).hG' (bk x))) ⟨unitPt (SB).hG' (bk x), rfl⟩ =
          Φ₀ ((SA).cellOf 1 (unitPt (SA).hG' x)) ⟨unitPt (SA).hG' x, rfl⟩))
    (P : Lb → Prop) (P' : Lb' → Prop)
    (hA0 : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ y, ¬ P y → ∀ Φ, H θ (s : ℂ) y Φ = 0)
    (hA0' : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ y', ¬ P' y' → ∀ Φ', H' θ' (s : ℂ) y' Φ' = 0)
    (ψ : ∀ y, P y → blocksOf 1 (k + 1) Set.univ (Lab.ysite y) ⊆ T → Lb')
    (hψP : ∀ y hP hy, P' (ψ y hP hy))
    (hψb : ∀ y hP hy, blocksOf 1 (k + 1) Set.univ (Lab'.ysite (ψ y hP hy)) =
      (blocksOf 1 (k + 1) Set.univ (Lab.ysite y)).image σc)
    (hψinj : ∀ y₁ hP₁ hy₁ y₂ hP₂ hy₂, ψ y₁ hP₁ hy₁ = ψ y₂ hP₂ hy₂ → y₁ = y₂)
    (hψsurj : ∀ y', P' y' → blocksOf 1 (k + 1) Set.univ (Lab'.ysite y') ⊆ T.image σc →
      ∃ y hP hy, ψ y hP hy = y')
    (hA : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ y hP hy, ∀ Φ Φ', (∀ x, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x →
        Φ' ((SB).cellOf 1 (unitPt (SB).hG' (bk x))) ⟨unitPt (SB).hG' (bk x), rfl⟩ =
          Φ ((SA).cellOf 1 (unitPt (SA).hG' x)) ⟨unitPt (SA).hG' x, rfl⟩) →
        H' θ' (s : ℂ) (ψ y hP hy) Φ' = H θ (s : ℂ) y Φ)
    (κ : ∀ i, blocksOf 1 (k + 1) Set.univ (Lab.ysite (y0 i)) ⊆ T → ι')
    (hκb : ∀ i hi, blocksOf 1 (k + 1) Set.univ (Lab'.ysite (y0' (κ i hi))) =
      (blocksOf 1 (k + 1) Set.univ (Lab.ysite (y0 i))).image σc)
    (hκinj : ∀ i₁ hi₁ i₂ hi₂, κ i₁ hi₁ = κ i₂ hi₂ → i₁ = i₂)
    (hκsurj : ∀ i', blocksOf 1 (k + 1) Set.univ (Lab'.ysite (y0' i')) ⊆ T.image σc →
      ∃ i hi, κ i hi = i')
    (hG : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ i hi, ∀ Φ Φ', (∀ x, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x →
        Φ' ((SB).cellOf 1 (unitPt (SB).hG' (bk x))) ⟨unitPt (SB).hG' (bk x), rfl⟩ =
          Φ ((SA).cellOf 1 (unitPt (SA).hG' x)) ⟨unitPt (SA).hG' x, rfl⟩) →
        G' θ' (κ i hi) (s : ℂ) Φ' = G θ i (s : ℂ) Φ) :
    newLevelCoeffLoc Gb' ((SB).blockSplit 1 hp').μ a aT ν ρb Zb' Lab' Φ₀' H' y0' G' θ'
        (T.image σc) =
      newLevelCoeffLoc Gb ((SA).blockSplit 1 hp).μ a aT ν ρb Zb Lab Φ₀ H y0 G θ T := by
  have hm' : 2 * R + 1 < (N₁' * L ^ m₁) * L ^ (k + 1) := by omega
  have hnI : 2 * R + 3 * L ^ (k + 1) + 5 < (N₁ * L ^ m₁) * L ^ (k + 1) := by omega
  have hnI' : 2 * R + 3 * L ^ (k + 1) + 5 < (N₁' * L ^ m₁) * L ^ (k + 1) := by omega
  have hσ : Set.InjOn σc (T : Set (𝔅A)) := by
    intro b₁ hb₁ b₂ hb₂ h
    have hb₁R := hT b₁ hb₁ b₁.1 (mem_box_self _ (cellSide_pos 1 m₁ (k + 1)))
    have hb₂R := hT b₂ hb₂ b₂.1 (mem_box_self _ (cellSide_pos 1 m₁ (k + 1)))
    have h1 := congrArg Subtype.val h
    rw [TwoTorusStep.cubeMap_val, TwoTorusStep.cubeMap_val] at h1
    exact Subtype.ext (boxMap_inj (hm' := hm') hb₁R hb₂R h1)
  have hBox : ∀ B ⊆ T, ∀ b ∈ B, ∀ x ∈ box b.1 aK, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x :=
    fun B hB b hb => hT b (hB hb)
  rw [newLevelCoeffLoc_eq, newLevelCoeffLoc_eq]
  refine congrArg₂ (· + ·) hdet (intervalIntegral.integral_congr fun s hs => ?_)
  rw [Set.uIcc_of_le zero_le_one] at hs
  refine Gsum_fun_transport _ _ Lab Lab' _ _ (locAct_dep Lab T Φ₀ H θ (s : ℂ)) y0 y0' _ _
    (fun i => truncMark_dep Lab (InPoly T) y0 Φ₀ G θ i (s : ℂ)) σc T hσ _
    (fun Z hZ F F' hF hFF => integral_blockSplit_twoTorus hN2 hk νS β p₁ δ hnI hnI' hGA hGB hp hp'
      Z (fun b hb => hT b (hZ hb)) hF hFF) P P' (fun y hy Φ => ?_) (fun y hy Φ => ?_) ψ hψP hψb
    hψinj hψsurj (fun y hP hy Φ Φ' hΦ => ?_) κ hκb hκinj hκsurj (fun i hi Φ Φ' hΦ => ?_)
  · by_cases hpo : InPoly T (Lab.ysite y)
    · rw [locAct_of_pos Lab Φ₀ H θ (s : ℂ) hpo]
      exact hA0 s hs y hy _
    · rw [locAct_of_neg Lab Φ₀ H θ (s : ℂ) hpo]
  · by_cases hpo : InPoly (T.image σc) (Lab'.ysite y)
    · rw [locAct_of_pos Lab' Φ₀' H' θ' (s : ℂ) hpo]
      exact hA0' s hs y hy _
    · rw [locAct_of_neg Lab' Φ₀' H' θ' (s : ℂ) hpo]
  · have hpo' : InPoly (T.image σc) (Lab'.ysite (ψ y hP hy)) := by
      show blocksOf 1 (k + 1) Set.univ (Lab'.ysite (ψ y hP hy)) ⊆ T.image σc
      rw [hψb y hP hy]
      exact Finset.image_subset_image hy
    rw [locAct_of_pos Lab' Φ₀' H' θ' (s : ℂ) hpo', locAct_of_pos Lab Φ₀ H θ (s : ℂ) hy,
      hψb y hP hy]
    exact hA s hs y hP hy _ _ (relBox_restrConf (ϱ := ϱ) hN2 hk νS β p₁ δ hN hN' (by omega) hnc
      (by omega) hp hp' (hBox _ hy) hΦ hΦ₀)
  · have hpo' : InPoly (T.image σc) (Lab'.ysite (y0' (κ i hi))) := by
      show blocksOf 1 (k + 1) Set.univ (Lab'.ysite (y0' (κ i hi))) ⊆ T.image σc
      rw [hκb i hi]
      exact Finset.image_subset_image hi
    show truncMark Lab' (InPoly (T.image σc)) y0' Φ₀' G' θ' (κ i hi) (s : ℂ) Φ' =
      truncMark Lab (InPoly T) y0 Φ₀ G θ i (s : ℂ) Φ
    rw [truncMark_of_pos Lab' y0' Φ₀' G' θ' (s : ℂ) hpo', truncMark_of_pos Lab y0 Φ₀ G θ (s : ℂ) hi]
    show G' θ' (κ i hi) (s : ℂ) (restrConf (blocksOf 1 (k + 1) Set.univ (Lab'.ysite (y0' (κ i hi))))
      Φ₀' Φ') = G θ i (s : ℂ) (restrConf (blocksOf 1 (k + 1) Set.univ (Lab.ysite (y0 i))) Φ₀ Φ)
    rw [hκb i hi]
    exact hG s hs i hi _ _ (relBox_restrConf (ϱ := ϱ) hN2 hk νS β p₁ δ hN hN' (by omega) hnc
      (by omega) hp hp' (hBox _ hi) hΦ hΦ₀)

end Steps

end Balaban.Polymer.LocalIso
