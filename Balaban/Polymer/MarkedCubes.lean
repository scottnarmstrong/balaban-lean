/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.CubeSystem
public import Balaban.Polymer.MayerMarked
public import Balaban.Polymer.MarkedTermwise
public import Balaban.Polymer.MarkedDeriv
public import Balaban.Polymer.Mayer
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Theorem 3.4: the marked cluster expansion on the cubes of `Ω` (FLUCTUATION.md §3.4)

Stage 1: labels and their pre-summation into one term per support (via (G4)).
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Localization Balaban.Polymer MeasureTheory

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {m₀ j : ℕ} {Ω : Set (CTorus d L N₁ m₁ K)}

local notation "𝔅" => CubeB (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ j Ω

open Classical in
/-- The blocks (cubes of `Ω`) contained in a set of sites. -/
noncomputable def blocksOf (m₀ j : ℕ) (Ω : Set (CTorus d L N₁ m₁ K)) (Y : Set (CTorus d L N₁ m₁ K)) :
    Finset (CubeB (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ j Ω) :=
  Finset.univ.filter fun b => box b.1 (cellSide L m₀ m₁ j) ⊆ Y

theorem mem_blocksOf {Y : Set (CTorus d L N₁ m₁ K)} {b : 𝔅} :
    b ∈ blocksOf m₀ j Ω Y ↔ box b.1 (cellSide L m₀ m₁ j) ⊆ Y := by
  classical
  simp [blocksOf]

theorem sitesOf_blocksOf (hN : L ^ m₀ ∣ N₁) (hj : j ≤ K) (hΩ : IsPiUnion m₀ j Ω)
    {Y : Set (CTorus d L N₁ m₁ K)} (hY : IsPiPrimeUnion m₀ j Y) :
    sitesOf (blocksOf m₀ j Ω Y) = Y ∩ Ω := by
  have hdvd := cellSide_dvd (K := K) (m₁ := m₁) hN hj
  have ha0 := cellSide_pos (L := L) m₀ m₁ j
  ext z
  constructor
  · intro hz
    obtain ⟨b, hb, hzb⟩ := mem_sitesOf.1 hz
    exact ⟨mem_blocksOf.1 hb hzb, b.2.2 hzb⟩
  · rintro ⟨hzY, hzΩ⟩
    obtain ⟨c, hc1, hc2, hc3⟩ := hY z hzY
    have hcell : box (cbase (cellSide L m₀ m₁ j) z) (cellSide L m₀ m₁ j) ⊆ Y :=
      (cell_subset_cube hdvd ha0 hc1 hc2).trans hc3
    have hcellΩ : box (cbase (cellSide L m₀ m₁ j) z) (cellSide L m₀ m₁ j) ⊆ Ω := by
      rcases cell_dichotomy hN hj hΩ (aligned_cbase (a := cellSide L m₀ m₁ j) z) with h | h
      · exact h
      · exact absurd (h (mem_box_cbase ha0 z)) (fun hh => hh hzΩ)
    exact mem_sitesOf.2 ⟨⟨cbase (cellSide L m₀ m₁ j) z, aligned_cbase z, hcellΩ⟩,
      mem_blocksOf.2 hcell, mem_box_cbase ha0 z⟩

variable (m₀ j Ω) in
/-- The labels of Theorem 3.4: connected sets `Y` of `π_j`-cubes meeting `Ω`, with the size
`𝗱(Y)` equal to `d^cov_j(Y)` or (for `Y ∈ 𝒟_j(mod Ω^c)`) to `d^cov_j(Y mod Ω^c)`. -/
structure CubeLabels (Lb : Type*) where
  /-- the set of sites of a label -/
  ysite : Lb → Set (CTorus d L N₁ m₁ K)
  /-- its size `𝗱` -/
  dl : Lb → ℝ
  isDj : ∀ y, IsDj m₀ j (ysite y)
  meets : ∀ y, (ysite y ∩ Ω).Nonempty
  size : ∀ y, dl y = treeLenCovOne m₀ j (ysite y) ∨
    (DjMod m₀ j Ω (ysite y) ∧ dl y = dcovMod m₀ j Ω (ysite y))

section Presum

variable {Lb : Type*} (Lab : CubeLabels m₀ j Ω Lb)

theorem CubeLabels.blocksOf_nonempty (hN : L ^ m₀ ∣ N₁) (hj : j ≤ K) (hΩ : IsPiUnion m₀ j Ω)
    (y : Lb) : (blocksOf m₀ j Ω (Lab.ysite y)).Nonempty := by
  obtain ⟨z, hz⟩ := Lab.meets y
  have := sitesOf_blocksOf hN hj hΩ (Lab.isDj y).2.1
  by_contra h
  rw [Finset.not_nonempty_iff_eq_empty] at h
  rw [h] at this
  have hz' : z ∈ sitesOf (∅ : Finset 𝔅) := by rw [this]; exact hz
  simp [sitesOf] at hz'

omit [NeZero N₁] [NeZero L] in
theorem CubeLabels.dl_nonneg (y : Lb) : 0 ≤ Lab.dl y := by
  rcases Lab.size y with h | ⟨-, h⟩
  · rw [h]; exact treeLenCovOne_nonneg _ _ _
  · rw [h]; exact dcovMod_nonneg _ _

/-- **(G4) for labels**: `d_Ω` of the support is at most the size of the label. -/
theorem CubeLabels.dExt_le (hN : L ^ m₀ ∣ N₁) (hj : j ≤ K) (hΩ : IsPiUnion m₀ j Ω) (y : Lb) :
    dExt (blocksOf m₀ j Ω (Lab.ysite y)) ≤ Lab.dl y := by
  have hs := sitesOf_blocksOf hN hj hΩ (Lab.isDj y).2.1
  have hle : dOmega m₀ j Ω (sitesOf (blocksOf m₀ j Ω (Lab.ysite y))) ≤
      ENNReal.ofReal (Lab.dl y) := by
    rw [hs]
    rcases Lab.size y with h | ⟨hm, h⟩
    · rw [h]; exact G4_dOmega_le (Lab.isDj y) (Lab.meets y)
    · rw [h]; exact G4_dOmega_le_mod hm (Lab.meets y)
  have hfin : dOmega m₀ j Ω (sitesOf (blocksOf m₀ j Ω (Lab.ysite y))) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hle
  rw [dExt_eq_toReal hfin]
  have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hle
  rwa [ENNReal.toReal_ofReal (Lab.dl_nonneg y)] at this

variable [Fintype Lb]

open Classical in
/-- The pre-summed term of the support `S`: the sum of the labels `Y` with `blocksOf Y = S`. -/
noncomputable def presum {Ωb : 𝔅 → Type*} (H : Lb → (∀ b, Ωb b) → ℂ) (S : NePoly 𝔅)
    (Φ : ∀ b, Ωb b) : ℂ :=
  ∑ y ∈ Finset.univ.filter (fun y => blocksOf m₀ j Ω (Lab.ysite y) = S.1), H y Φ

open Classical in
/-- **Pre-summation bound** (proof of Theorem 3.4):
`|H̃(S)| ≤ ε_H K₀ e^{-(κ_H - κ₀) d_Ω(S)}`. -/
theorem presum_bound (hN : L ^ m₀ ∣ N₁) (hj : j ≤ K) (hΩ : IsPiUnion m₀ j Ω)
    {Ωb : 𝔅 → Type*} (H : Lb → (∀ b, Ωb b) → ℂ) {εH κH κ0 K0 : ℝ} (hε : 0 ≤ εH)
    (hκ : κ0 ≤ κH)
    (hH : ∀ y Φ, ‖H y Φ‖ ≤ εH * Real.exp (-κH * Lab.dl y))
    (hlab : ∀ b : 𝔅, ∑ y : Lb, (if box b.1 (cellSide L m₀ m₁ j) ⊆ Lab.ysite y then
      Real.exp (-κ0 * Lab.dl y) else 0) ≤ K0) (S : NePoly 𝔅) (Φ : ∀ b, Ωb b) :
    ‖presum Lab H S Φ‖ ≤ εH * K0 * Real.exp (-(κH - κ0) * dExt S.1) := by
  obtain ⟨b, hb⟩ := S.2
  set F := Finset.univ.filter (fun y => blocksOf m₀ j Ω (Lab.ysite y) = S.1) with hF
  have hterm : ∀ y ∈ F, ‖H y Φ‖ ≤ εH * Real.exp (-(κH - κ0) * dExt S.1) *
      Real.exp (-κ0 * Lab.dl y) := by
    intro y hy
    have hyS : blocksOf m₀ j Ω (Lab.ysite y) = S.1 := (Finset.mem_filter.1 hy).2
    have hd : dExt S.1 ≤ Lab.dl y := hyS ▸ Lab.dExt_le hN hj hΩ y
    refine (hH y Φ).trans ?_
    rw [mul_assoc, ← Real.exp_add]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hε
    nlinarith [sub_nonneg.2 hκ]
  have hsum : ∑ y ∈ F, Real.exp (-κ0 * Lab.dl y) ≤ K0 := by
    refine le_trans ?_ (hlab b)
    rw [← Finset.sum_filter]
    refine Finset.sum_le_sum_of_subset_of_nonneg (fun y hy => ?_) (fun _ _ _ => Real.exp_nonneg _)
    have hyS : blocksOf m₀ j Ω (Lab.ysite y) = S.1 := (Finset.mem_filter.1 hy).2
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact mem_blocksOf.1 (hyS ▸ hb)
  have hc : 0 ≤ εH * Real.exp (-(κH - κ0) * dExt S.1) := by positivity
  unfold presum
  calc ‖∑ y ∈ F, H y Φ‖ ≤ ∑ y ∈ F, ‖H y Φ‖ := norm_sum_le _ _
    _ ≤ ∑ y ∈ F, εH * Real.exp (-(κH - κ0) * dExt S.1) * Real.exp (-κ0 * Lab.dl y) :=
        Finset.sum_le_sum hterm
    _ = εH * Real.exp (-(κH - κ0) * dExt S.1) * ∑ y ∈ F, Real.exp (-κ0 * Lab.dl y) := by
        rw [Finset.mul_sum]
    _ ≤ εH * Real.exp (-(κH - κ0) * dExt S.1) * K0 := mul_le_mul_of_nonneg_left hsum hc
    _ = _ := by ring

end Presum

section Activities

variable {Lb : Type*} [Fintype Lb]

open Classical in
/-- The activities of the labels: measurable, depending on `Φ` only through the cubes of
`Y ∩ Ω`, bounded by `ε_H e^{-κ_H 𝗱(Y)}`, with the entropy bound `∑_{Y ⊃ b} e^{-κ₀ 𝗱(Y)} ≤ K₀`. -/
structure LabelAct (Lab : CubeLabels m₀ j Ω Lb) (Ωb : 𝔅 → Type*) [∀ b, MeasurableSpace (Ωb b)]
    (εH κH κ0 Kc : ℝ) where
  /-- the activity `H(Y; Φ)` -/
  H : Lb → (∀ b, Ωb b) → ℂ
  meas : ∀ y, Measurable (H y)
  dep : ∀ y, DepOn (blocksOf m₀ j Ω (Lab.ysite y)) (H y)
  bound : ∀ y Φ, ‖H y Φ‖ ≤ εH * Real.exp (-κH * Lab.dl y)
  entropy : ∀ b : 𝔅, ∑ y : Lb, (if box b.1 (cellSide L m₀ m₁ j) ⊆ Lab.ysite y then
    Real.exp (-κ0 * Lab.dl y) else 0) ≤ Kc

variable {Lab : CubeLabels m₀ j Ω Lb} {εH κH κ0 Kc : ℝ}

theorem LabelAct.presum_meas {Ωb : 𝔅 → Type*} [∀ b, MeasurableSpace (Ωb b)] (A : LabelAct Lab Ωb εH κH κ0 Kc) (S : NePoly 𝔅) :
    Measurable (presum Lab A.H S) := by
  unfold presum
  exact Finset.measurable_sum _ (fun y _ => A.meas y)

theorem LabelAct.presum_dep {Ωb : 𝔅 → Type*} [∀ b, MeasurableSpace (Ωb b)] (A : LabelAct Lab Ωb εH κH κ0 Kc) (S : NePoly 𝔅) :
    DepOn S.1 (presum Lab A.H S) := by
  intro Φ Φ' h
  unfold presum
  refine Finset.sum_congr rfl fun y hy => ?_
  have hyS : blocksOf m₀ j Ω (Lab.ysite y) = S.1 := (Finset.mem_filter.1 hy).2
  exact A.dep y Φ Φ' (fun b hb => h b (hyS ▸ hb))

theorem LabelAct.presum_bound {Ωb : 𝔅 → Type*} [∀ b, MeasurableSpace (Ωb b)] (hN : L ^ m₀ ∣ N₁) (hj : j ≤ K) (hΩ : IsPiUnion m₀ j Ω)
    (A : LabelAct Lab Ωb εH κH κ0 Kc) (hε : 0 ≤ εH) (hκ : κ0 ≤ κH) (S : NePoly 𝔅)
    (Φ : ∀ b, Ωb b) :
    ‖presum Lab A.H S Φ‖ ≤ εH * Kc * Real.exp (-(κH - κ0) * dExt S.1) :=
  Balaban.Fluctuation.presum_bound Lab hN hj hΩ A.H hε hκ A.bound A.entropy S Φ

theorem presum_sum {Ωb : 𝔅 → Type*} (Lab : CubeLabels m₀ j Ω Lb) (hN : L ^ m₀ ∣ N₁) (hj : j ≤ K)
    (hΩ : IsPiUnion m₀ j Ω) (H : Lb → (∀ b, Ωb b) → ℂ) (Φ : ∀ b, Ωb b) :
    ∑ S : NePoly 𝔅, presum Lab H S Φ = ∑ y, H y Φ := by
  classical
  let toNe : Lb → NePoly 𝔅 := fun y => ⟨blocksOf m₀ j Ω (Lab.ysite y), Lab.blocksOf_nonempty hN hj hΩ y⟩
  rw [← Finset.sum_fiberwise (s := Finset.univ) (g := toNe) (f := fun y => H y Φ)]
  refine Finset.sum_congr rfl fun S _ => ?_
  unfold presum
  refine Finset.sum_congr ?_ (fun _ _ => rfl)
  ext y
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, toNe, Subtype.ext_iff]

end Activities

section Numerics

/-- The numerical conditions (3.5) imply the hypotheses `hq`, `hα`, `H₀ ≤ log 2` of
`mayer_marked`. -/
theorem numerics_PE {εH Kc c1v cGv κH κ0 κ' : ℝ} (hεpos : 0 < εH) (hKc1 : 1 ≤ Kc)
    (hc1 : 1 ≤ c1v) (hcG : 0 ≤ cGv) (hκ' : 0 ≤ κ') (hκ1nn : 0 ≤ κH - 2 * κ0)
    (hε : εH ≤ 1 / (8 * Kc ^ 3 * c1v * Real.exp ((κH - 2 * κ0) * cGv + c1v + κ' * cGv))) :
    2 * (2 * (2 * εH * Kc) * Kc * Real.exp ((κH - 2 * κ0) * cGv)) * c1v * Kc *
        Real.exp (c1v + κ' * cGv) ≤ 1 ∧
      2 * (2 * εH * Kc) * Kc * Real.exp ((κH - 2 * κ0) * cGv) * c1v ≤ 1 / 2 ∧
      2 * εH * Kc ≤ Real.log 2 := by
  have hKc0 : 0 < Kc := by linarith
  have hexp1 : 1 ≤ Real.exp (c1v + κ' * cGv) :=
    Real.one_le_exp (by nlinarith [mul_nonneg hκ' hcG])
  have hexpκ : 1 ≤ Real.exp ((κH - 2 * κ0) * cGv) :=
    Real.one_le_exp (by nlinarith [mul_nonneg hκ1nn hcG])
  have hE1 : Real.exp ((κH - 2 * κ0) * cGv + c1v + κ' * cGv) =
      Real.exp ((κH - 2 * κ0) * cGv) * Real.exp (c1v + κ' * cGv) := by
    rw [← Real.exp_add]; congr 1; ring
  set X := Real.exp ((κH - 2 * κ0) * cGv) with hX
  set Y := Real.exp (c1v + κ' * cGv) with hY
  have hQ : εH * (8 * Kc ^ 3 * c1v * (X * Y)) ≤ 1 := by
    rw [← hE1]
    have h := hε
    rwa [le_div_iff₀ (by positivity)] at h
  have hXY : 1 ≤ X * Y := one_le_mul_of_one_le_of_one_le hexpκ hexp1
  have hK3 : 0 < Kc ^ 3 := by positivity
  refine ⟨?_, ?_, ?_⟩
  · nlinarith [mul_pos hεpos hK3]
  · have hu : 0 < εH * Kc ^ 3 * c1v * X := by positivity
    nlinarith
  · have h1 : εH * (8 * Kc ^ 3) ≤ 1 := by
      have h1c : 1 ≤ c1v * (X * Y) := by nlinarith
      have : 8 * Kc ^ 3 ≤ 8 * Kc ^ 3 * c1v * (X * Y) := by
        have := mul_le_mul_of_nonneg_left h1c (by positivity : (0 : ℝ) ≤ 8 * Kc ^ 3)
        nlinarith
      nlinarith [mul_pos hεpos hK3]
    have h2 : 2 * εH * Kc ≤ 1 / 4 := by nlinarith [mul_pos hεpos hKc0, sq_nonneg Kc]
    have := Real.log_two_gt_d9
    linarith

end Numerics

section Mark

variable {Lb : Type*}

open Classical in
/-- The mark `G`, attached to the term of the support `S0`. -/
noncomputable def gMark {Ωb : 𝔅 → Type*} (S0 : Finset 𝔅) (G : (∀ b, Ωb b) → ℂ) :
    Unit → NePoly 𝔅 → (∀ b, Ωb b) → ℂ :=
  fun _ t Φ => if t.1 = S0 then G Φ else 0

omit [NeZero N₁] [NeZero L] in
theorem gMark_measurable {Ωb : 𝔅 → Type*} [∀ b, MeasurableSpace (Ωb b)] (S0 : Finset 𝔅)
    {G : (∀ b, Ωb b) → ℂ} (hG : Measurable G) (t : NePoly 𝔅) :
    Measurable (gMark S0 G () t) := by
  classical
  by_cases h : t.1 = S0
  · have : gMark S0 G () t = G := by funext Φ; simp [gMark, h]
    rw [this]; exact hG
  · have : gMark S0 G () t = fun _ => 0 := by funext Φ; simp [gMark, h]
    rw [this]; exact measurable_const

omit [NeZero N₁] [NeZero L] in
theorem gMark_bdd {Ωb : 𝔅 → Type*} (S0 : Finset 𝔅) {G : (∀ b, Ωb b) → ℂ} {C : ℝ}
    (hC : 0 ≤ C) (hG : ∀ Φ, ‖G Φ‖ ≤ C) (t : NePoly 𝔅) : Bdd (gMark S0 G () t) := by
  classical
  refine ⟨C, fun Φ => ?_⟩
  by_cases h : t.1 = S0
  · simpa [gMark, h] using hG Φ
  · simpa [gMark, h] using hC

omit [NeZero N₁] [NeZero L] in
theorem gMark_dep {Ωb : 𝔅 → Type*} (S0 : Finset 𝔅) {G : (∀ b, Ωb b) → ℂ}
    (hG : DepOn S0 G) (t : NePoly 𝔅) : DepOn t.1 (gMark S0 G () t) := by
  classical
  by_cases h : t.1 = S0
  · have : gMark S0 G () t = G := by funext Φ; simp [gMark, h]
    rw [this, h]; exact hG
  · intro Φ Φ' _; simp [gMark, h]

omit [NeZero N₁] [NeZero L] in
theorem gMark_zero {Ωb : 𝔅 → Type*} (S0 : Finset 𝔅) (G : (∀ b, Ωb b) → ℂ) (t : NePoly 𝔅)
    (Φ : ∀ b, Ωb b) (h : ¬ S0 ⊆ t.1) : gMark S0 G () t Φ = 0 := by
  classical
  have : ¬ t.1 = S0 := fun h' => h (h' ▸ subset_rfl)
  simp [gMark, this]

theorem sum_gMark {Ωb : 𝔅 → Type*} (S0 : Finset 𝔅) (hS0 : S0.Nonempty) (G : (∀ b, Ωb b) → ℂ)
    (Φ : ∀ b, Ωb b) : ∑ t : NePoly 𝔅, gMark S0 G () t Φ = G Φ := by
  classical
  rw [Finset.sum_eq_single (⟨S0, hS0⟩ : NePoly 𝔅)]
  · simp [gMark]
  · intro t _ ht
    have : ¬ t.1 = S0 := fun h => ht (Subtype.ext h)
    simp [gMark, this]
  · simp

end Mark

section Main

/-- The constant `C_PE = 8 K₀² c₁ e^{(κ_H - 2κ₀) c_G + c₁ + κ' c_G}` of (3.6). -/
noncomputable def CPE (d L : ℕ) (Kc κH κ0 κ' : ℝ) : ℝ :=
  8 * Kc ^ 2 * c1 d L * Real.exp ((κH - 2 * κ0) * cG d L + c1 d L + κ' * cG d L)

variable {Lb : Type*} [Fintype Lb]

open Classical in
theorem hHlam_bound {Ωb : 𝔅 → Type*} [∀ b, MeasurableSpace (Ωb b)]
    (hN : L ^ m₀ ∣ N₁) (hj : j ≤ K) (hΩ : IsPiUnion m₀ j Ω)
    {Lab : CubeLabels m₀ j Ω Lb} {εH κH κG κ0 Kc F0 : ℝ}
    (A : LabelAct Lab Ωb εH κH κ0 Kc) (y0 : Lb) (G : (∀ b, Ωb b) → ℂ)
    (hG : ∀ Φ, ‖G Φ‖ ≤ F0 * Real.exp (-κG * Lab.dl y0)) (hεpos : 0 < εH) (hF0 : 0 < F0)
    (hKc0 : 0 < Kc) (hκHge : κ0 ≤ κH) (hκG : κH ≤ κG)
    (l : Unit → ℂ) (hl : ‖l ()‖ < εH * Kc * Real.exp (κ0 * Lab.dl y0) / F0)
    (t : NePoly 𝔅) (Φ : ∀ b, Ωb b) :
    ‖Hlam (presum Lab A.H) (gMark (blocksOf m₀ j Ω (Lab.ysite y0)) G) l t Φ‖ ≤
      (2 * εH * Kc) * Real.exp (-(κ0 + (κH - 2 * κ0)) * dExt t.1) := by
  set S0 := blocksOf m₀ j Ω (Lab.ysite y0) with hS0
  set r0 : ℝ := εH * Kc * Real.exp (κ0 * Lab.dl y0) / F0 with hr0
  have hr0pos : 0 < r0 := by positivity
  have hb0 := A.presum_bound hN hj hΩ hεpos.le hκHge t Φ
  have hexpo : -(κ0 + (κH - 2 * κ0)) = -(κH - κ0) := by ring
  rw [hexpo]
  have hHl : Hlam (presum Lab A.H) (gMark S0 G) l t Φ =
      presum Lab A.H t Φ + l () * gMark S0 G () t Φ := by simp [Hlam]
  rw [hHl]
  by_cases h : t.1 = S0
  · have hGt : ‖gMark S0 G () t Φ‖ ≤ F0 * Real.exp (-κG * Lab.dl y0) := by
      simpa [gMark, h] using hG Φ
    have h1 : ‖l () * gMark S0 G () t Φ‖ ≤ εH * Kc * Real.exp (-(κH - κ0) * dExt t.1) := by
      rw [norm_mul]
      calc ‖l ()‖ * ‖gMark S0 G () t Φ‖ ≤ r0 * (F0 * Real.exp (-κG * Lab.dl y0)) :=
            mul_le_mul hl.le hGt (norm_nonneg _) hr0pos.le
        _ = εH * Kc * Real.exp (κ0 * Lab.dl y0 - κG * Lab.dl y0) := by
            rw [hr0, Real.exp_sub, show -κG * Lab.dl y0 = -(κG * Lab.dl y0) by ring, Real.exp_neg]
            field_simp
        _ ≤ εH * Kc * Real.exp (-(κH - κ0) * dExt t.1) := by
            refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (by positivity)
            have hd : dExt S0 ≤ Lab.dl y0 := Lab.dExt_le hN hj hΩ y0
            have : dExt t.1 ≤ Lab.dl y0 := h ▸ hd
            nlinarith [Lab.dl_nonneg y0]
    calc ‖presum Lab A.H t Φ + l () * gMark S0 G () t Φ‖
        ≤ ‖presum Lab A.H t Φ‖ + ‖l () * gMark S0 G () t Φ‖ := norm_add_le _ _
      _ ≤ εH * Kc * Real.exp (-(κH - κ0) * dExt t.1) +
          εH * Kc * Real.exp (-(κH - κ0) * dExt t.1) := add_le_add hb0 h1
      _ = _ := by ring
  · have : gMark S0 G () t Φ = 0 := by simp [gMark, h]
    rw [this, mul_zero, add_zero]
    refine hb0.trans ?_
    have : 0 ≤ εH * Kc * Real.exp (-(κH - κ0) * dExt t.1) := by positivity
    nlinarith

open Classical in
/-- The Mayer-layer hypotheses for the cube system, and its conclusions (before translating to
the statement of Theorem 3.4). -/
theorem marked_cubes_core {Ωb : 𝔅 → Type*} [∀ b, MeasurableSpace (Ωb b)]
    (μ : ∀ b, Measure (Ωb b)) [∀ b, IsProbabilityMeasure (μ b)]
    (hN : L ^ m₀ ∣ N₁) (hj : j ≤ K) (hΩ : IsPiUnion m₀ j Ω)
    {Lab : CubeLabels m₀ j Ω Lb} {εH κH κG κ0 κ' Kc F0 : ℝ}
    (A : LabelAct Lab Ωb εH κH κ0 Kc) (y0 : Lb) (G : (∀ b, Ωb b) → ℂ)
    (hGm : Measurable G) (hGdep : DepOn (blocksOf m₀ j Ω (Lab.ysite y0)) G)
    (hG : ∀ Φ, ‖G Φ‖ ≤ F0 * Real.exp (-κG * Lab.dl y0))
    (hκ0 : aEnt d L + 1 ≤ κ0) (hKc : K0 d L κ0 + 1 ≤ Kc) (hεpos : 0 < εH) (hF0 : 0 < F0)
    (hκ' : 0 ≤ κ') (hκG : κH ≤ κG)
    (hκ : κ' + 3 * κ0 + c1 d L + 3 / 2 ≤ κH)
    (hε : εH ≤ 1 / (8 * Kc ^ 3 * c1 d L *
      Real.exp ((κH - 2 * κ0) * cG d L + c1 d L + κ' * cG d L))) :
    marksXi μ (presum Lab A.H) (gMark (blocksOf m₀ j Ω (Lab.ysite y0)) G) 0 = Complex.exp (∑ Y : Finset 𝔅,
        Ff (shareBlock (Subtype.val : NePoly 𝔅 → Finset 𝔅)) Subtype.val (marksK μ Subtype.val (presum Lab A.H) (gMark (blocksOf m₀ j Ω (Lab.ysite y0)) G)) Y 0) ∧
      (∀ (b : 𝔅) (Y : Finset 𝔅), b ∈ Y →
        ‖Ff (shareBlock (Subtype.val : NePoly 𝔅 → Finset 𝔅)) Subtype.val (marksK μ Subtype.val (presum Lab A.H) (gMark (blocksOf m₀ j Ω (Lab.ysite y0)) G)) Y 0‖ *
          Real.exp (κ' * (dExt Y + cG d L)) ≤ εH * Kc * CPE d L Kc κH κ0 κ') ∧
      (D1 () (marksXi μ (presum Lab A.H) (gMark (blocksOf m₀ j Ω (Lab.ysite y0)) G)) / marksXi μ (presum Lab A.H) (gMark (blocksOf m₀ j Ω (Lab.ysite y0)) G) 0 = ∑ Y : Finset 𝔅, D1 ()
        (Ff (shareBlock (Subtype.val : NePoly 𝔅 → Finset 𝔅)) Subtype.val (marksK μ Subtype.val (presum Lab A.H) (gMark (blocksOf m₀ j Ω (Lab.ysite y0)) G)) Y)) ∧
      (∀ Y : Finset 𝔅, ¬ blocksOf m₀ j Ω (Lab.ysite y0) ⊆ Y → D1 ()
        (Ff (shareBlock (Subtype.val : NePoly 𝔅 → Finset 𝔅)) Subtype.val
          (marksK μ Subtype.val (presum Lab A.H) (gMark (blocksOf m₀ j Ω (Lab.ysite y0)) G)) Y) = 0) ∧
      ∀ {b : 𝔅}, b ∈ blocksOf m₀ j Ω (Lab.ysite y0) → ∀ Y : Finset 𝔅, b ∈ Y →
        ‖D1 () (Ff (shareBlock (Subtype.val : NePoly 𝔅 → Finset 𝔅)) Subtype.val
          (marksK μ Subtype.val (presum Lab A.H) (gMark (blocksOf m₀ j Ω (Lab.ysite y0)) G)) Y)‖ * Real.exp (κ' * (dExt Y + cG d L)) ≤
          CPE d L Kc κH κ0 κ' * F0 * Real.exp (-κ0 * Lab.dl y0) := by
  set S0 := blocksOf m₀ j Ω (Lab.ysite y0) with hS0
  set a := presum Lab A.H with ha
  set g := gMark S0 G with hg
  set r0 := εH * Kc * Real.exp (κ0 * Lab.dl y0) / F0 with hr0
  have hKgeo : 0 < K0 d L κ0 := by
    unfold K0
    have : Real.exp (-1) < 1 := by rw [Real.exp_lt_one_iff]; norm_num
    exact div_pos (Real.exp_pos _) (by linarith)
  have hKc1 : 1 ≤ Kc := by linarith
  have hKc0 : 0 ≤ Kc := by linarith
  have hc1 := one_le_c1 d L
  have hcG : 0 ≤ cG d L := by unfold cG; positivity
  have haent := aEnt_nonneg d L
  have hκ0nn : 0 ≤ κ0 := by linarith
  have hκHge : κ0 ≤ κH := by linarith
  have hκ1nn : 0 ≤ κH - 2 * κ0 := by linarith
  have hκHnn : 0 ≤ κH := by linarith
  have hκGnn : 0 ≤ κG := by linarith
  have hS0ne : S0.Nonempty := Lab.blocksOf_nonempty hN hj hΩ y0
  have hr0pos : 0 < r0 := by positivity
  obtain ⟨hα1, hq, hH0log⟩ := numerics_PE hεpos hKc1 hc1 hcG hκ' hκ1nn hε
  have hexp_le : ∀ (κ x : ℝ), 0 ≤ κ → 0 ≤ x → Real.exp (-κ * x) ≤ 1 := fun κ x hκ hx =>
    Real.exp_le_one_iff.2 (by nlinarith)
  have hab : ∀ t, Bdd (a t) := fun t => ⟨εH * Kc, fun Φ =>
    (A.presum_bound hN hj hΩ hεpos.le hκHge t Φ).trans (by
      have := hexp_le (κH - κ0) (dExt t.1) (by linarith) (dExt_nonneg t.1)
      have h0 : 0 ≤ εH * Kc := by positivity
      nlinarith)⟩
  have hGC : ∀ Φ, ‖G Φ‖ ≤ F0 := fun Φ => (hG Φ).trans (by
    have := hexp_le κG (Lab.dl y0) hκGnn (Lab.dl_nonneg y0)
    nlinarith)
  have hG2c := fun b : 𝔅 => (sum_exp_dExt_le hN hj b hκ0).trans hKc
  have hHb : ∀ l ∈ Balaban.Analysis.polydisc (0 : Unit → ℂ) (fun _ : Unit => r0), ∀ (t : NePoly 𝔅) (Φ : ∀ b, Ωb b),
      ‖Hlam a g l t Φ‖ ≤ (2 * εH * Kc) * Real.exp (-(κ0 + (κH - 2 * κ0)) * dExt t.1) :=
    fun l hl t Φ => hHlam_bound hN hj hΩ A y0 G hG hεpos hF0 (by linarith) hκHge hκG l
      (by simpa using hl ()) t Φ
  have hG3T : ∀ C : Finset (NePoly 𝔅), ConnSet (Subtype.val : NePoly 𝔅 → Finset 𝔅) C →
      dExt (unionCs (Subtype.val : NePoly 𝔅 → Finset 𝔅) C) ≤
        ∑ t ∈ C, dExt t.1 + cG d L * ((C.card : ℝ) - 1) := fun C hC => dExt_unionCs_le C hC
  have hG3P : ∀ (n : ℕ) (X : Fin (n + 1) → NePoly 𝔅),
      (clusterGraph (shareBlock (Subtype.val : NePoly 𝔅 → Finset 𝔅)) X).Connected →
        dExt (unionOf (Subtype.val : NePoly 𝔅 → Finset 𝔅) X) ≤ ∑ i, dExt (X i).1 + cG d L * n :=
    fun n X hX => dExt_union_cluster X hX
  have hG1 : ∀ Y : NePoly 𝔅, (Y.1.card : ℝ) ≤ c1 d L * (1 + dExt Y.1) :=
    fun Y => card_le_dExt hN hj Y.1
  have hκ1 : κ' + κ0 + c1 d L ≤ (κH - 2 * κ0) - 3 / 2 := by linarith
  have hH0 : 0 ≤ 2 * εH * Kc := by positivity
  have hmain := mayer_marked_termwise (μ := μ) (Subtype.val : NePoly 𝔅 → Finset 𝔅) (a := a) (g := g)
    (d := dExt) (H0 := 2 * εH * Kc) (κ0 := κ0) (κ1 := κH - 2 * κ0) (c := cG d L) (K0 := Kc)
    (c1 := c1 d L) (κ' := κ') (κ0P := κ0) (K0P := Kc) (cP := cG d L) (r := fun _ => r0)
    (S := fun _ => S0)
    (fun t => t.2) (fun _ => hr0pos) (fun t => A.presum_meas t) hab
    (fun _ t => gMark_measurable S0 hGm t) (fun _ t => gMark_bdd S0 hF0.le hGC t)
    (fun t => A.presum_dep t) (fun _ t => gMark_dep S0 hGdep t)
    (fun _ t Φ hn => gMark_zero S0 G t Φ hn) hH0 hH0log hκ0nn hκ1nn hcG
    (fun Y => dExt_nonneg Y) hHb hKc0 (fun b => by rw [Finset.sum_filter]; convert hG2c b) hG3T (by linarith) hq hG1 hκ' hcG (fun b => by convert hG2c b) hG3P hκ1 hα1
  obtain ⟨h1, h2, h3, h3', h4⟩ := hmain
  have hαeq : 2 * (2 * (2 * εH * Kc) * Kc * Real.exp ((κH - 2 * κ0) * cG d L)) * c1 d L * Kc *
      Real.exp (c1 d L + κ' * cG d L) = εH * Kc * CPE d L Kc κH κ0 κ' := by
    unfold CPE
    rw [show Real.exp ((κH - 2 * κ0) * cG d L + c1 d L + κ' * cG d L) =
      Real.exp ((κH - 2 * κ0) * cG d L) * Real.exp (c1 d L + κ' * cG d L) by
      rw [← Real.exp_add]; congr 1; ring]
    ring
  refine ⟨h1, fun b Y hb => (h2 b Y hb).trans (le_of_eq hαeq), h3 (), fun Y hY => h3' () Y hY, fun {b} hb Y hbY => ?_⟩
  refine (h4 () hb Y hbY).trans (le_of_eq ?_)
  rw [hαeq, hr0]
  have e : Real.exp (-κ0 * Lab.dl y0) = (Real.exp (κ0 * Lab.dl y0))⁻¹ := by
    rw [← Real.exp_neg]; congr 1; ring
  rw [e]
  have h1 : εH * Kc ≠ 0 := by positivity
  have h2 : Real.exp (κ0 * Lab.dl y0) ≠ 0 := (Real.exp_pos _).ne'
  field_simp

theorem le_of_mul_exp_le {x B u : ℝ} (h : x * Real.exp u ≤ B) : x ≤ B * Real.exp (-u) := by
  have := mul_le_mul_of_nonneg_right h (Real.exp_nonneg (-u))
  rwa [mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one] at this

theorem marksXi_zero_eq {Ωb : 𝔅 → Type*} [∀ b, MeasurableSpace (Ωb b)]
    (μ : ∀ b, Measure (Ωb b)) (hN : L ^ m₀ ∣ N₁) (hj : j ≤ K) (hΩ : IsPiUnion m₀ j Ω)
    (Lab : CubeLabels m₀ j Ω Lb) (H : Lb → (∀ b, Ωb b) → ℂ) (S0 : Finset 𝔅) (hS0 : S0.Nonempty)
    (G : (∀ b, Ωb b) → ℂ) (l : Unit → ℂ) :
    marksXi μ (presum Lab H) (gMark S0 G) l =
      ∫ Φ, Complex.exp (∑ y, H y Φ + l () * G Φ) ∂(Measure.pi μ) := by
  unfold marksXi
  refine integral_congr_ae (Filter.Eventually.of_forall fun Φ => ?_)
  simp only []
  congr 1
  have : ∀ t : NePoly 𝔅, Hlam (presum Lab H) (gMark S0 G) l t Φ =
      presum Lab H t Φ + l () * gMark S0 G () t Φ := fun t => by simp [Hlam]
  rw [Finset.sum_congr rfl (fun t _ => this t), Finset.sum_add_distrib, ← Finset.mul_sum,
    sum_gMark S0 hS0 G Φ, presum_sum Lab hN hj hΩ H Φ]

open Classical in
/-- **Theorem 3.4 (marked cluster expansion on the cubes of `Ω`), one mark.**

Let `Ξ = ∫ exp (∑_Y H(Y)) dν` and `⟨G⟩ = Ξ⁻¹ ∫ G exp (∑_Y H(Y)) dν`.  Then `Ξ ≠ 0`,
`Ξ = exp (∑_S P(S))` with `|P(S)| ≤ ε_H K₀ C_PE e^{-κ' d_Ω(S)}`, and `⟨G⟩ = ∑_S G*(S)` where
`G*(S) = 0` unless `S ⊃ Y₀ ∩ Ω` and `|G*(S)| ≤ C_PE F₀ e^{-κ₀ 𝗱(Y₀)} e^{-κ' d_Ω(S)}`.  Here
`d_Ω = dExt` is the real extension of `d_Ω` of Definition 1.1 (equal to `d_Ω` where finite). -/
theorem marked_cubes {Ωb : 𝔅 → Type*} [∀ b, MeasurableSpace (Ωb b)] (μ : ∀ b, Measure (Ωb b))
    [∀ b, IsProbabilityMeasure (μ b)]
    (hN : L ^ m₀ ∣ N₁) (hj : j ≤ K) (hΩ : IsPiUnion m₀ j Ω)
    {Lab : CubeLabels m₀ j Ω Lb} {εH κH κG κ0 κ' Kc F0 : ℝ}
    (A : LabelAct Lab Ωb εH κH κ0 Kc) (y0 : Lb) (G : (∀ b, Ωb b) → ℂ)
    (hGm : Measurable G) (hGdep : DepOn (blocksOf m₀ j Ω (Lab.ysite y0)) G)
    (hG : ∀ Φ, ‖G Φ‖ ≤ F0 * Real.exp (-κG * Lab.dl y0))
    (hκ0 : aEnt d L + 1 ≤ κ0) (hKc : K0 d L κ0 + 1 ≤ Kc) (hεpos : 0 < εH) (hF0 : 0 < F0)
    (hκ' : 0 ≤ κ') (hκG : κH ≤ κG)
    (hκ : κ' + 3 * κ0 + c1 d L + 3 / 2 ≤ κH)
    (hε : εH ≤ 1 / (8 * Kc ^ 3 * c1 d L *
      Real.exp ((κH - 2 * κ0) * cG d L + c1 d L + κ' * cG d L))) :
    (∫ Φ, Complex.exp (∑ y, A.H y Φ) ∂(Measure.pi μ) ≠ 0) ∧
    (∃ P : Finset 𝔅 → ℂ,
      ∫ Φ, Complex.exp (∑ y, A.H y Φ) ∂(Measure.pi μ) = Complex.exp (∑ Y, P Y) ∧
      ∀ Y : Finset 𝔅, Y.Nonempty →
        ‖P Y‖ ≤ εH * Kc * CPE d L Kc κH κ0 κ' * Real.exp (-κ' * dExt Y)) ∧
    (∃ Gs : Finset 𝔅 → ℂ,
      (∫ Φ, G Φ * Complex.exp (∑ y, A.H y Φ) ∂(Measure.pi μ)) /
        (∫ Φ, Complex.exp (∑ y, A.H y Φ) ∂(Measure.pi μ)) = ∑ Y, Gs Y ∧
      (∀ Y : Finset 𝔅, ¬ blocksOf m₀ j Ω (Lab.ysite y0) ⊆ Y → Gs Y = 0) ∧
      ∀ Y : Finset 𝔅, ‖Gs Y‖ ≤
        CPE d L Kc κH κ0 κ' * F0 * Real.exp (-κ0 * Lab.dl y0) * Real.exp (-κ' * dExt Y)) := by
  have hcore := marked_cubes_core μ hN hj hΩ A y0 G hGm hGdep hG hκ0 hKc hεpos hF0 hκ' hκG hκ hε
  obtain ⟨h1, h2, h3, h3', h4⟩ := hcore
  have hKgeo : 0 < K0 d L κ0 := by
    unfold K0
    have : Real.exp (-1) < 1 := by rw [Real.exp_lt_one_iff]; norm_num
    exact div_pos (Real.exp_pos _) (by linarith [aEnt_nonneg d L])
  have hS0ne : (blocksOf m₀ j Ω (Lab.ysite y0)).Nonempty := Lab.blocksOf_nonempty hN hj hΩ y0
  have hcG : 0 ≤ cG d L := by unfold cG; positivity
  have hXi0 : marksXi μ (presum Lab A.H) (gMark (blocksOf m₀ j Ω (Lab.ysite y0)) G) 0 =
      ∫ Φ, Complex.exp (∑ y, A.H y Φ) ∂(Measure.pi μ) := by
    rw [marksXi_zero_eq μ hN hj hΩ Lab A.H _ hS0ne G 0]
    simp
  have hne : ∫ Φ, Complex.exp (∑ y, A.H y Φ) ∂(Measure.pi μ) ≠ 0 := by
    rw [← hXi0, h1]; exact Complex.exp_ne_zero _
  refine ⟨hne, ⟨fun Y => Ff (shareBlock (Subtype.val : NePoly 𝔅 → Finset 𝔅)) Subtype.val
      (marksK μ Subtype.val (presum Lab A.H) (gMark (blocksOf m₀ j Ω (Lab.ysite y0)) G)) Y 0,
      by rw [← hXi0, h1], fun Y hY => ?_⟩, ?_⟩
  · obtain ⟨b, hb⟩ := hY
    have := h2 b Y hb
    have hexp : Real.exp (κ' * dExt Y) ≤ Real.exp (κ' * (dExt Y + cG d L)) :=
      Real.exp_le_exp.2 (by nlinarith [mul_nonneg hκ' hcG])
    have h5 : ‖Ff (shareBlock (Subtype.val : NePoly 𝔅 → Finset 𝔅)) Subtype.val
        (marksK μ Subtype.val (presum Lab A.H) (gMark (blocksOf m₀ j Ω (Lab.ysite y0)) G)) Y 0‖ *
        Real.exp (κ' * dExt Y) ≤ εH * Kc * CPE d L Kc κH κ0 κ' :=
      (mul_le_mul_of_nonneg_left hexp (norm_nonneg _)).trans this
    have := le_of_mul_exp_le h5
    rwa [show -κ' * dExt Y = -(κ' * dExt Y) by ring]
  · -- the first moment
    have hc1 := one_le_c1 d L
    have hκHnn : 0 ≤ κH := by linarith [aEnt_nonneg d L]
    have hκGnn : 0 ≤ κG := by linarith
    have hGC : ∀ Φ, ‖G Φ‖ ≤ F0 := fun Φ => (hG Φ).trans (by
      have : Real.exp (-κG * Lab.dl y0) ≤ 1 := Real.exp_le_one_iff.2 (by
        nlinarith [Lab.dl_nonneg y0, hκGnn])
      nlinarith)
    have hAb : ∀ Φ, ‖∑ y, A.H y Φ‖ ≤ ∑ y : Lb, εH := fun Φ =>
      (norm_sum_le _ _).trans (Finset.sum_le_sum fun y _ => (A.bound y Φ).trans (by
        have : Real.exp (-κH * Lab.dl y) ≤ 1 := Real.exp_le_one_iff.2 (by
          nlinarith [Lab.dl_nonneg y, hκHnn])
        nlinarith))
    have hAm : Measurable (fun Φ => ∑ y, A.H y Φ) := Finset.measurable_sum _ (fun y _ => A.meas y)
    have hD1 := D1_expMark (Measure.pi μ) (fun Φ => ∑ y, A.H y Φ) G hAm hGm hF0.le hAb hGC
    have hfun : marksXi μ (presum Lab A.H) (gMark (blocksOf m₀ j Ω (Lab.ysite y0)) G) =
        fun l : Unit → ℂ => ∫ Φ, Complex.exp (∑ y, A.H y Φ + l () * G Φ) ∂(Measure.pi μ) :=
      funext fun l => marksXi_zero_eq μ hN hj hΩ Lab A.H _ hS0ne G l
    refine ⟨fun Y => D1 () (Ff (shareBlock (Subtype.val : NePoly 𝔅 → Finset 𝔅)) Subtype.val
      (marksK μ Subtype.val (presum Lab A.H) (gMark (blocksOf m₀ j Ω (Lab.ysite y0)) G)) Y),
      ?_, h3', fun Y => ?_⟩
    · rw [← hXi0, ← h3, hfun, hD1]
    · by_cases hY : blocksOf m₀ j Ω (Lab.ysite y0) ⊆ Y
      · obtain ⟨b, hb⟩ := hS0ne
        have := h4 hb Y (hY hb)
        have hexp : Real.exp (κ' * dExt Y) ≤ Real.exp (κ' * (dExt Y + cG d L)) :=
          Real.exp_le_exp.2 (by nlinarith [mul_nonneg hκ' hcG])
        have h5 := (mul_le_mul_of_nonneg_left hexp (norm_nonneg _)).trans this
        have := le_of_mul_exp_le h5
        rwa [show -κ' * dExt Y = -(κ' * dExt Y) by ring]
      · dsimp only
        rw [h3' Y hY]
        simp only [norm_zero]
        unfold CPE
        have := one_le_c1 d L
        positivity

end Main

end Balaban.Fluctuation
