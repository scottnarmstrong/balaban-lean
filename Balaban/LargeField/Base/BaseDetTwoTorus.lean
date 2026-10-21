/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Base.BaseDetActivity
public import Balaban.LargeField.Base.BaseTwoTorusLogShift
public import Balaban.Polymer.TwoTorusDet
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The determinant activities of the first step on two tori

For the whole-lattice generating sets `levelGS 1` of two first-step tori identified on a centred
box, the rooted trace `rootTraceBase` of the first step at a cut point `1_I` (the cut parameter is
the indicator of a set `I` of parameter cubes) is the same on both tori when the cubes of `I` and
the root site lie in the box and the fields agree on the box.  The reading set of the shifted
logarithm at the root is the set `V = ({root} ∪ ⋃_{P ∈ I} P) ∩ Ω₁`: an active interaction cube
sees only cubes of `I`, so its thickened cube lies in `V` (`subI_vset_of_active`); the neighbour
closure of `V` is the set `Y` of `BaseTwoTorusLogShift`.

* `extS_cutPt_eq_zero`: the cut parameter vanishes on the parameter cubes off `I`;
* `subI_vset_of_active`: the interaction cube of an active centre lies in `V`;
* `inBox_of_mem_nbrClosure`: the neighbour closure of a set of the box of radius `R` lies in the
  box of radius `R + L`;
* `rootTraceBase_cutPt_twoTorus`: the rooted traces at corresponding cut points agree;
* `baseDetActivity_twoTorus`: the determinant activities of corresponding polymers agree (the
  mixed differences correspond by `mixDiff_twoTorus_of_cutPt`, the polymers by
  `detActivityOf_twoTorus`).
-/

@[expose] public section

noncomputable section

open scoped Classical

namespace Balaban.LargeField.Base.XC

open Balaban Balaban.Localization Balaban.Fluctuation Balaban.SmallField.Def6 Balaban.Polymer
  Balaban.Multiscale Balaban.Background Matrix Balaban.Polymer.TwoTorusStep Balaban.Analysis
  MeasureTheory Set

section Generic

variable {d L N₁ m₁ k : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}

/-- **The cut parameter vanishes on the parameter cubes off `I`.** -/
theorem extS_cutPt_eq_zero {G : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ} (I : Finset (cubeIdx G))
    {P : ℕ × Balaban.Localization.CTorus d L N₁ m₁ (k + 1)} (hPc : P ∈ cubeIdx G)
    (hPI : P ∉ patches I) : extS G (cutPt I) P = 0 := by
  have h : (⟨P, hPc⟩ : cubeIdx G) ∉ I := fun h => hPI (mem_patches.2 ⟨hPc, h⟩)
  simp [extS, hPc, cutPt, h]

/-- **The interaction cube of an active centre lies in the cut region.**  If the cut parameter
vanishes on the parameter cubes off `I` (it is `extS (cutPt I)`), every centre `q` with non-zero
cut weight has its interaction cube inside `V = (X₁ ∪ ⋃_{P ∈ I} P) ∩ Ω₁`. -/
theorem subI_vset_of_active {G : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ} {a : ℕ → ℝ} {ν : ℝ}
    (hdg : DGSetting G a ν) (X₁ : Finset (Balaban.Localization.CTorus d L N₁ m₁ (k + 1)))
    (I : Finset (cubeIdx G)) {q : ℕ × Balaban.Localization.CTorus d L N₁ m₁ (k + 1)}
    (h0 : sProd G (extS G (cutPt I)) q ≠ 0) :
    SubI G (intBox q) ((Vset X₁ (patches I)).filter fun x => x ∈ G.Ω 1) := by
  have hact := hact_aux (G := G) (X₁ := X₁) (𝒞 := patches I) (extS G (cutPt I))
    (fun P hP hPC => by
      have hPc : P ∈ cubeIdx G := (Finset.mem_filter.1 hP).1
      exact extS_cutPt_eq_zero I hPc hPC) q h0
  have hhat := hhat_aux hdg q hact
  intro t ht
  exact hhat (Finset.mem_filter.2 ⟨box_subset_hatBox q ht, t.2⟩)

end Generic

section TwoTori

variable {d L N₁ N₁' m₁ N : ℕ} [NeZero N₁] [NeZero N₁'] [NeZero L] {ϱ : ℝ} {Cx : ℝ}

set_option hygiene false in
local notation "bm" => boxMap ((N₁ * L ^ m₁) * L ^ 1) ((N₁' * L ^ m₁) * L ^ 1)
set_option hygiene false in
local notation "GA" => levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := 1) (ϱ := ϱ) 1 le_rfl
set_option hygiene false in
local notation "GB" => levelGS (d := d) (L := L) (N₁ := N₁') (m₁ := m₁) (k := 1) (ϱ := ϱ) 1 le_rfl
set_option hygiene false in
local notation "ιb" x:max => Subtype.mk (bm (x : Balaban.Localization.CTorus d L N₁ m₁ 1))
  (levelGS_mem_Ω_one (d := d) (L := L) (N₁ := N₁') (m₁ := m₁) (K := 1) (ϱ := ϱ)
    (le_refl 1) le_rfl _)
set_option hygiene false in
local notation "ιu" b:max => Subtype.mk
  (boxMap ((N₁ * L ^ m₁) * L ^ (0 + 1 - 0)) ((N₁' * L ^ m₁) * L ^ (0 + 1 - 0))
    (b : UnitTorus d L N₁ m₁ 0))
  (mem_unitPts_levelTop (d := d) (L := L) (N₁ := N₁') (m₁ := m₁) (k := 0) (ϱ := ϱ) _)

/-- **The neighbour closure of a set of the box lies in a slightly larger box**: the closure under
lattice neighbours and the layer block (side `L`) of a set of the box of radius `R` lies in the box
of radius `R + L`. -/
theorem inBox_of_mem_nbrClosure {R : ℕ}
    {Sr : Finset (Balaban.Localization.CTorus d L N₁ m₁ 1)}
    (hSR : ∀ x ∈ Sr, InBox d R ((N₁ * L ^ m₁) * L ^ 1) x)
    (hn : 2 * (R + L ^ 1) + 1 < (N₁ * L ^ m₁) * L ^ 1)
    {x : Balaban.Localization.CTorus d L N₁ m₁ 1} (hx : x ∈ nbrClosure (GA) Sr) :
    InBox d (R + L ^ 1) ((N₁ * L ^ m₁) * L ^ 1) x := by
  have hL1 : 1 ≤ L ^ 1 := Nat.one_le_pow _ _ (Nat.pos_of_ne_zero (NeZero.ne L))
  obtain ⟨-, p, hp, hcase⟩ := Finset.mem_filter.1 hx
  have hpR := hSR _ hp
  rcases hcase with h | ⟨μ, h | h⟩ | h
  · rw [h]; exact inBox_mono (by omega) hpR
  · rw [h]
    exact inBox_mono (by omega) (inBox_add_single (by omega) hpR μ)
  · rw [h]
    exact inBox_mono (by omega) (inBox_sub_single (by omega) hpR μ)
  · obtain ⟨h1, h2, hl⟩ := (GA).layerIndex_spec p.2
    have hn1 : (GA).layerIndex (p : Balaban.Localization.CTorus d L N₁ m₁ 1) = 1 := by omega
    rw [hn1] at h
    exact inBox_of_jBlock_eq (k := 0) (N₁ := N₁) (m := 1) (by omega)
      (by have h1 : L ^ (0 + 1) = L ^ 1 := rfl; rw [h1]; omega) hpR (GeneratingSet.mem_blk.1 h)

variable {a : ℕ → ℝ} {aT ν κ δ : ℝ}
  {α : (GA).Ω 1 → ℂ} {α' : (GB).Ω 1 → ℂ}
  {φ : Balaban.Localization.CTorus d L N₁ m₁ 1 → Fin N → ℂ}
  {φ' : Balaban.Localization.CTorus d L N₁' m₁ 1 → Fin N → ℂ}

/-- **The rooted trace of the first step at a cut point, on two tori.**  Let `I` be a set of
parameter cubes of the first torus and `I'` the corresponding set of the second
(`patches I' = Prod.map id bm '' patches I`), with the cubes of `I` and the root site of the unit
point `y` in the box of radius `R`, and let the potentials and the constraint fields correspond on
the box of radius `R + L`.  Then `rootTraceBase` of `ιu y` at `1_{I'}` equals that of `y` at
`1_I`.  The reading set is `V = ({root} ∪ ⋃_{P ∈ I} P) ∩ Ω₁`
(`subI_vset_of_active`), its closure under neighbours and layer blocks is the set `Y` of
`baseCovXLogShift_rows_twoTorus`.  Margins: `4 (R + L) + 12 L^(1+m₁) + 3 L + 5` and
`2 R₁ + 5 L · cellSide L 0 m₁ 1`, `R₁ = R + (3 L^(1+m₁) + 3 L^3) + L^(1+m₁)`, below
`N₁ L^m₁ L` (and for `N₁'`). -/
theorem rootTraceBase_cutPt_twoTorus
    (hdgA : DGSetting (GA) a ν) (hdgB : DGSetting (GB) a ν)
    (SA : Dec2.XCover (coverOf (GA)) (GA) a aT ν Cx)
    (SB : Dec2.XCover (coverOf (GB)) (GB) a aT ν Cx) (hCx : 0 ≤ Cx) (hκ : 0 ≤ κ)
    (hM : Dec2.cstarX d L Cx * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) (hδ : 0 ≤ δ)
    (hsm : δ ^ 2 * smallConstX d L κ ≤ 1 / 4) (hαA : AdmPot (GA) α) (hαB : AdmPot (GB) α')
    (hφA : IsConstraintField (GA) δ φ) (hφB : IsConstraintField (GB) δ φ')
    (I : Finset (cubeIdx (GA))) (I' : Finset (cubeIdx (GB)))
    (hI' : patches I' = (patches I).image (Prod.map id bm))
    (y : unitPts (GA)) {R : ℕ}
    (hyR : InBox d R ((N₁ * L ^ m₁) * L ^ 1)
      (baseUnitSite (GA) y : Balaban.Localization.CTorus d L N₁ m₁ 1))
    (hIR : ∀ P ∈ patches I, ∀ x ∈ cubeP P, InBox d R ((N₁ * L ^ m₁) * L ^ 1) x)
    (hn : 4 * (R + L ^ 1) + 12 * L ^ (1 + m₁) + 3 * L ^ 1 + 5 < (N₁ * L ^ m₁) * L ^ 1)
    (hn' : 4 * (R + L ^ 1) + 12 * L ^ (1 + m₁) + 3 * L ^ 1 + 5 < (N₁' * L ^ m₁) * L ^ 1)
    (hnS : 2 * (R + (3 * L ^ (1 + m₁) + 3 * L ^ (1 + 2)) + L ^ (1 + m₁)) +
      5 * (L * cellSide L 0 m₁ 1) < (N₁ * L ^ m₁) * L ^ 1)
    (hnS' : 2 * (R + (3 * L ^ (1 + m₁) + 3 * L ^ (1 + 2)) + L ^ (1 + m₁)) +
      5 * (L * cellSide L 0 m₁ 1) < (N₁' * L ^ m₁) * L ^ 1)
    (hα : ∀ x : (GA).Ω 1, InBox d R ((N₁ * L ^ m₁) * L ^ 1)
      (x : Balaban.Localization.CTorus d L N₁ m₁ 1) → α' (ιb x) = α x)
    (hφ : ∀ u : Balaban.Localization.CTorus d L N₁ m₁ 1,
      InBox d (R + L ^ 1) ((N₁ * L ^ m₁) * L ^ 1) u → φ' (bm u) = φ u) :
    rootTraceBase (GB) a aT ν φ' α' (ιu y) (cutPt I') =
      rootTraceBase (GA) a aT ν φ α y (cutPt I) := by
  classical
  have hL1 : 1 ≤ L ^ 1 := Nat.one_le_pow _ _ (Nat.pos_of_ne_zero (NeZero.ne L))
  have hLm : L ^ 1 ≤ L ^ (1 + m₁) :=
    Nat.pow_le_pow_right (Nat.pos_of_ne_zero (NeZero.ne L)) (by omega)
  have hΩA : ∀ x : Balaban.Localization.CTorus d L N₁ m₁ 1, x ∈ (GA).Ω 1 :=
    levelGS_mem_Ω_one (le_refl 1) le_rfl
  have hΩB : ∀ x : Balaban.Localization.CTorus d L N₁' m₁ 1, x ∈ (GB).Ω 1 :=
    levelGS_mem_Ω_one (le_refl 1) le_rfl
  set x0 : (GA).Ω 1 := baseUnitSite (GA) y with hx0
  -- the root site of the image
  have hxB : baseUnitSite (GB) (ιu y) = ιb x0 := by
    apply Subtype.ext
    apply unitBlock_injective_one
    rw [unitBlock_baseUnitSite]
    have := unitBlock_boxMap (k := 0) (ρ := R) (N₁ := N₁) (N₁' := N₁') (m₁ := m₁) (L := L) (d := d)
      (by have h1 : L ^ (0 + 1) = L ^ 1 := rfl; rw [h1]; omega) hyR
    refine Eq.trans ?_ this.symm
    show boxMap ((N₁ * L ^ m₁) * L ^ (0 + 1 - 0)) ((N₁' * L ^ m₁) * L ^ (0 + 1 - 0))
      (y : UnitTorus d L N₁ m₁ 0) = _
    rw [hx0, unitBlock_baseUnitSite]
  -- the reading set
  set X₁ : Finset (Balaban.Localization.CTorus d L N₁ m₁ 1) :=
    {(x0 : Balaban.Localization.CTorus d L N₁ m₁ 1)} with hX₁
  set V : Finset (Balaban.Localization.CTorus d L N₁ m₁ 1) :=
    (Vset X₁ (patches I)).filter fun x => x ∈ (GA).Ω 1 with hV
  have hVA : V = Vset X₁ (patches I) := Finset.filter_true_of_mem fun x _ => hΩA x
  have hx0V : (x0 : Balaban.Localization.CTorus d L N₁ m₁ 1) ∈ V := by
    rw [hVA]; exact Finset.mem_union_left _ (Finset.mem_singleton_self _)
  have hVR : ∀ x ∈ V, InBox d R ((N₁ * L ^ m₁) * L ^ 1) x := by
    intro x hx
    rw [hVA] at hx
    rcases Finset.mem_union.1 hx with hx | hx
    · rw [hX₁, Finset.mem_singleton] at hx
      rw [hx]; exact hyR
    · obtain ⟨P, hP, hxP⟩ := Finset.mem_biUnion.1 hx
      exact hIR P hP x hxP
  have hYR : ∀ u ∈ nbrClosure (GA) V, InBox d (R + L ^ 1) ((N₁ * L ^ m₁) * L ^ 1) u :=
    fun u hu => inBox_of_mem_nbrClosure hVR (by omega) hu
  have hSY : V ⊆ nbrClosure (GA) V := fun t ht =>
    mem_nbrClosure_of_nbr (p := ⟨t, hΩA t⟩) (q := ⟨t, hΩA t⟩) ht (Or.inl rfl)
  have hnbr := fun (p q : (GA).Ω 1) (hp : (p : Balaban.Localization.CTorus d L N₁ m₁ 1) ∈ V)
    (h : (q : Balaban.Localization.CTorus d L N₁ m₁ 1) = p ∨
      (∃ μ : Fin d, (q : Balaban.Localization.CTorus d L N₁ m₁ 1) =
          (p : Balaban.Localization.CTorus d L N₁ m₁ 1) + Pi.single μ 1 ∨
        (q : Balaban.Localization.CTorus d L N₁ m₁ 1) =
          (p : Balaban.Localization.CTorus d L N₁ m₁ 1) - Pi.single μ 1) ∨
      (q : Balaban.Localization.CTorus d L N₁ m₁ 1) ∈
        (GA).blk ((GA).layerIndex (p : Balaban.Localization.CTorus d L N₁ m₁ 1)) p) =>
    mem_nbrClosure_of_nbr hp h
  -- the image of the reading set
  have hρS : 2 * R + 5 * (L * cellSide L 0 m₁ 1) < (N₁ * L ^ m₁) * L ^ 1 := by omega
  have hPcR : ∀ P ∈ patches I, InBox d R ((N₁ * L ^ m₁) * L ^ 1) P.2 := fun P hP =>
    hIR P hP P.2 (mem_cubeP.2 (SameCell.refl _ _))
  have hVB : V.image bm = (Vset (X₁.image bm) (patches I')).filter fun x => x ∈ (GB).Ω 1 := by
    rw [Finset.filter_true_of_mem fun x _ => hΩB x, hI', hVA]
    exact (vset_image_top (k := 0) (N₁' := N₁') hρS X₁
      (fun P hP => ⟨(mem_patches.1 hP).1, hPcR P hP⟩)).symm
  have hdich : ∀ q ∈ (coverOf (GA)).cubeIdx, (coverOf (GA)).sProd (extS (GA) (cutPt I)) q ≠ 0 →
      SubI (GA) (intBox q) V ∨ DisjI (GA) (intBox q) (nbrClosure (GA) V) :=
    fun q _ h0 => Or.inl (subI_vset_of_active hdgA X₁ I h0)
  have hdich' : ∀ q ∈ (coverOf (GB)).cubeIdx, (coverOf (GB)).sProd (extS (GB) (cutPt I')) q ≠ 0 →
      SubI (GB) (intBox q) (V.image bm) ∨ DisjI (GB) (intBox q) ((nbrClosure (GA) V).image bm) :=
    fun q _ h0 => Or.inl (by rw [hVB]; exact subI_vset_of_active hdgB (X₁.image bm) I' h0)
  -- the cut parameters correspond
  have hsP := extS_cutPt_twoTorus (k := 0) I I' hI' hPcR hnS'
  have hagree := hagree_boxMap (ϱ := ϱ) (N₁' := N₁') (le_refl 1) le_rfl hnS hnS'
    (subset_refl V) hVR hsP
  have hrow : ∀ i : Fin N,
      baseCovXLogShift (GB) a aT ν α' (extS (GB) (cutPt I')) φ' (ιb x0, i) (ιb x0, i) =
      baseCovXLogShift (GA) a aT ν α (extS (GA) (cutPt I)) φ (x0, i) (x0, i) := fun i =>
    (baseCovXLogShift_rows_twoTorus (Sr := V) (Y := nbrClosure (GA) V) (R := R + L ^ 1)
      hCx hκ hM hδ hsm hαA hαB (fun P => norm_extS_cutPt_le hκ I P)
      (fun P => norm_extS_cutPt_le hκ I' P) hφA hφB hSY hYR hn hn'
      (fun x hx => hα x (hVR _ hx)) hdich hdich' hnbr hagree (fun u hu => hφ u (hYR u hu)) SA SB x0 x0
      (hSY hx0V) (hSY hx0V) i i).2
  unfold rootTraceBase
  rw [hxB, Finset.sum_congr rfl fun i _ => hrow i]


variable {m₀ : ℕ}

set_option hygiene false in
local notation "aK" => cellSide L m₀ m₁ 1

/-- **The determinant activity of a polymer of the first step on two tori.**  Let `Y` be a polymer
(a set of cubes of the paving of side `a_K`) of the first torus with sites in the box of radius
`r`, containing the root cube of the unit point `y`, and `Y' = cubeMap '' Y`.  If the potentials
and constraint fields correspond on the box of radius `r + L`, the activities agree:
`baseDetActivity (ιu y) Y' = baseDetActivity y Y`.  The sets `J` of parameter cubes with hull `Y`
correspond to those with hull `Y'` (`detActivityOf_twoTorus`), and the mixed differences of the
rooted trace agree (`mixDiff_twoTorus_of_cutPt` and `rootTraceBase_cutPt_twoTorus`: the patches of
`J` lie in the sites of the hull, `inBox_hull_facts`).  Margins: `4 (r + L) + 12 L^(1+m₁) + 3 L + 5`,
`2 r₁ + 5 L · cellSide L 0 m₁ 1` (`r₁ = r + (3 L^(1+m₁) + 3 L^3) + L^(1+m₁)`) and
`2 (r + 2 L a_K) + L a_K`, below `N₁ L^m₁ L` and `N₁' L^m₁ L`. -/
theorem baseDetActivity_twoTorus (hN : L ^ m₀ ∣ N₁) (hN' : L ^ m₀ ∣ N₁')
    (hdgA : DGSetting (GA) a ν) (hdgB : DGSetting (GB) a ν)
    (SA : Dec2.XCover (coverOf (GA)) (GA) a aT ν Cx)
    (SB : Dec2.XCover (coverOf (GB)) (GB) a aT ν Cx) (hCx : 0 ≤ Cx) (hκ : 0 ≤ κ)
    (hM : Dec2.cstarX d L Cx * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) (hδ : 0 ≤ δ)
    (hsm : δ ^ 2 * smallConstX d L κ ≤ 1 / 4) (hαA : AdmPot (GA) α) (hαB : AdmPot (GB) α')
    (hφA : IsConstraintField (GA) δ φ) (hφB : IsConstraintField (GB) δ φ')
    (y : unitPts (GA))
    (Y : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := 1) m₀ 1 Set.univ))
    (hyY : rootCube (m₀ := m₀) (rootIdxOf y) ∈ Y) {r : ℕ}
    (hYr : ∀ x ∈ sitesOf Y, InBox d r ((N₁ * L ^ m₁) * L ^ 1) x)
    (hn : 4 * (r + L ^ 1) + 12 * L ^ (1 + m₁) + 3 * L ^ 1 + 5 < (N₁ * L ^ m₁) * L ^ 1)
    (hn' : 4 * (r + L ^ 1) + 12 * L ^ (1 + m₁) + 3 * L ^ 1 + 5 < (N₁' * L ^ m₁) * L ^ 1)
    (hnS : 2 * (r + (3 * L ^ (1 + m₁) + 3 * L ^ (1 + 2)) + L ^ (1 + m₁)) +
      5 * (L * cellSide L 0 m₁ 1) < (N₁ * L ^ m₁) * L ^ 1)
    (hnS' : 2 * (r + (3 * L ^ (1 + m₁) + 3 * L ^ (1 + 2)) + L ^ (1 + m₁)) +
      5 * (L * cellSide L 0 m₁ 1) < (N₁' * L ^ m₁) * L ^ 1)
    (hnH : 2 * (r + 2 * (L * aK)) + L * aK < (N₁ * L ^ m₁) * L ^ 1)
    (hnH' : 2 * (r + 2 * (L * aK)) + L * aK < (N₁' * L ^ m₁) * L ^ 1)
    (hα : ∀ x : (GA).Ω 1, InBox d r ((N₁ * L ^ m₁) * L ^ 1)
      (x : Balaban.Localization.CTorus d L N₁ m₁ 1) → α' (ιb x) = α x)
    (hφ : ∀ u : Balaban.Localization.CTorus d L N₁ m₁ 1,
      InBox d (r + L ^ 1) ((N₁ * L ^ m₁) * L ^ 1) u → φ' (bm u) = φ u) :
    baseDetActivity m₀ (GB) a aT ν φ' α' (ιu y) (Y.image (Balaban.Polymer.TwoTorusStep.cubeMap hN hN' le_rfl)) =
      baseDetActivity m₀ (GA) a aT ν φ α y Y := by
  classical
  have e1 : L ^ (0 + 1) = L ^ 1 := rfl
  have e2 : cellSide L 0 m₁ (0 + 1) = cellSide L 0 m₁ 1 := rfl
  have hn1 : 2 * r + 3 * L ^ (0 + 1) + 5 < (N₁ * L ^ m₁) * L ^ (0 + 1) := by
    rw [e1]; omega
  have hn1' : 2 * r + 3 * L ^ (0 + 1) + 5 < (N₁' * L ^ m₁) * L ^ (0 + 1) := by
    rw [e1]; omega
  have hn3 : 2 * r + 5 * (L * cellSide L 0 m₁ (0 + 1)) < (N₁ * L ^ m₁) * L ^ (0 + 1) := by
    rw [e1, e2]; omega
  have hn3' : 2 * r + 5 * (L * cellSide L 0 m₁ (0 + 1)) < (N₁' * L ^ m₁) * L ^ (0 + 1) := by
    rw [e1, e2]; omega
  unfold baseDetActivity
  refine detActivityOf_twoTorus (k := 0) hN hN' y Y hyY hYr hn1 hn1' hn3 hn3' hnH hnH' ?_
  intro J hJY J' hJ'
  obtain ⟨hbR, hJR⟩ := inBox_hull_facts (k := 0) hN y Y hyY hYr J hJY
  refine mixDiff_twoTorus_of_cutPt (k := 0) (R := r) J J' hJ' (by rw [e1]; omega)
    (fun P hP => hJR P hP P.2 (mem_cubeP.2 (SameCell.refl _ _))) ?_
  intro I hIJ I' hI'
  exact rootTraceBase_cutPt_twoTorus hdgA hdgB SA SB hCx hκ hM hδ hsm hαA hαB hφA hφB I I' hI' y
    (hbR _ (by rw [unitBlock_baseUnitSite]))
    (fun P hP => hJR P (Finset.image_subset_image hIJ hP)) hn hn' hnS hnS' hα hφ

end TwoTori

end Balaban.LargeField.Base.XC
