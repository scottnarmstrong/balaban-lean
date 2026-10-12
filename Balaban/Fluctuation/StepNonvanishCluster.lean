/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.StepNonvanishId
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The cluster expansion of a product-measure integral of label activities

`labelAct_integral_eq_exp`: for label activities obeying the numerical hypotheses (3.5) of
Theorem 3.4 (the hypotheses of `mayer_pe`, COMPLETE-STEP (2.1)-(2.2)),
`∫ exp (∑_y H(y; Φ)) d⨂_b ν_b = exp 𝓛` with `‖𝓛‖ ≤ |𝔅| · ε_H K_c C_PE` (COMPLETE-STEP (2.3)), for
complex activities.  In particular the integral is nonzero.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Localization Balaban.Polymer MeasureTheory

section Cluster

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {m₀ : ℕ}

open Classical in
/-- **Cluster expansion of the integral of complex label activities** (COMPLETE-STEP (2.3)):
`∫ exp (∑_y H(y; Φ)) dν = exp 𝓛` with a convergent cluster sum, `‖𝓛‖ ≤ |𝔅| ε_H K_c C_PE`. -/
theorem labelAct_integral_eq_exp
    {Ωb : CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ K Set.univ → Type}
    [∀ b, MeasurableSpace (Ωb b)]
    (μ : ∀ b, Measure (Ωb b)) [∀ b, IsProbabilityMeasure (μ b)]
    (hN : L ^ m₀ ∣ N₁) {Lb : Type} [Fintype Lb]
    {Lab : CubeLabels (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ K Set.univ Lb}
    {εH κH κ0 κ' Kc : ℝ} (A : LabelAct Lab Ωb εH κH κ0 Kc)
    (hκ0 : aEnt d L + 1 ≤ κ0) (hKc : K0 d L κ0 + 1 ≤ Kc) (hεpos : 0 < εH) (hκ' : 0 ≤ κ')
    (hκ : κ' + 3 * κ0 + c1 d L + 3 / 2 ≤ κH)
    (hε : εH ≤ 1 / (8 * Kc ^ 3 * c1 d L *
      Real.exp ((κH - 2 * κ0) * cG d L + c1 d L + κ' * cG d L))) :
    ∃ Lg : ℂ, ∫ Φ, Complex.exp (∑ y, A.H y Φ) ∂(Measure.pi μ) = Complex.exp Lg ∧
      ‖Lg‖ ≤ Fintype.card (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ K Set.univ) *
        (εH * Kc * CPE d L Kc κH κ0 κ') := by
  have hΩ : IsPiUnion m₀ K (Set.univ : Set (CTorus d L N₁ m₁ K)) :=
    fun z _ => ⟨cbase (cellSide L m₀ m₁ K) z, aligned_cbase z,
      mem_box_cbase (cellSide_pos (L := L) m₀ m₁ K) z, Set.subset_univ _⟩
  have hKgeo : 0 < K0 d L κ0 := by
    unfold K0
    have : Real.exp (-1) < 1 := by rw [Real.exp_lt_one_iff]; norm_num
    exact div_pos (Real.exp_pos _) (by linarith [aEnt_nonneg d L])
  have hKc1 : 1 ≤ Kc := by linarith
  have hKc0 : 0 ≤ Kc := by linarith
  have hc1 := one_le_c1 d L
  have hcG : 0 ≤ cG d L := by unfold cG; positivity
  have haent := aEnt_nonneg d L
  have hκ0nn : 0 ≤ κ0 := by linarith
  have hκHge : κ0 ≤ κH := by linarith
  have hκ1nn : 0 ≤ κH - 2 * κ0 := by linarith
  obtain ⟨hα1, hq, hH0log⟩ := numerics_PE hεpos hKc1 hc1 hcG hκ' hκ1nn hε
  have hG2c := fun b : CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ K Set.univ =>
    (sum_exp_dExt_le hN le_rfl b hκ0).trans hKc
  have hG3T : ∀ C : Finset (NePoly (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ K
      Set.univ)), ConnSet (Subtype.val) C →
      dExt (unionCs (Subtype.val) C) ≤ ∑ t ∈ C, dExt t.1 + cG d L * ((C.card : ℝ) - 1) :=
    fun C hC => dExt_unionCs_le C hC
  have hG3P : ∀ (n : ℕ) (X : Fin (n + 1) → NePoly (CubeB (d := d) (L := L) (N₁ := N₁)
      (m₁ := m₁) (K := K) m₀ K Set.univ)),
      (clusterGraph (shareBlock (Subtype.val)) X).Connected →
        dExt (unionOf (Subtype.val) X) ≤ ∑ i, dExt (X i).1 + cG d L * n :=
    fun n X hX => dExt_union_cluster X hX
  have hG1 : ∀ Y : NePoly (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ K Set.univ),
      (Y.1.card : ℝ) ≤ c1 d L * (1 + dExt Y.1) := fun Y => card_le_dExt hN le_rfl Y.1
  have hH0 : 0 ≤ 2 * εH * Kc := by positivity
  have hκ1 : κ' + κ0 + c1 d L ≤ (κH - 2 * κ0) - 3 / 2 := by linarith
  have hHb : ∀ (t : NePoly (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ K
      Set.univ)) (Φ : ∀ b, Ωb b),
      ‖presum Lab A.H t Φ‖ ≤ (2 * εH * Kc) * Real.exp (-(κ0 + (κH - 2 * κ0)) * dExt t.1) := by
    intro t Φ
    refine (A.presum_bound hN le_rfl hΩ hεpos.le hκHge t Φ).trans ?_
    have : -(κ0 + (κH - 2 * κ0)) = -(κH - κ0) + 2 * κ0 - 2 * κ0 := by ring
    have h2 : 0 ≤ εH * Kc := by positivity
    have : -(κ0 + (κH - 2 * κ0)) * dExt t.1 = -(κH - κ0) * dExt t.1 := by ring
    rw [this]
    nlinarith [Real.exp_pos (-(κH - κ0) * dExt t.1)]
  have hbdd : ∀ t, Bdd (presum Lab A.H t) := fun t => ⟨2 * εH * Kc, fun Φ => by
    refine (hHb t Φ).trans ?_
    have := Real.exp_le_one_iff.2 (show -(κ0 + (κH - 2 * κ0)) * dExt t.1 ≤ 0 by
      nlinarith [dExt_nonneg t.1])
    nlinarith⟩
  have hmain := mayer_pe (μ := μ) (sup := fun T : NePoly (CubeB (d := d) (L := L) (N₁ := N₁)
      (m₁ := m₁) (K := K) m₀ K Set.univ) => T.1) (H := presum Lab A.H) (d := dExt)
    (H0 := 2 * εH * Kc) (κ0 := κ0) (κ1 := κH - 2 * κ0) (c := cG d L) (K0 := Kc)
    (c1 := c1 d L) (κ' := κ') (κ0P := κ0) (K0P := Kc) (cP := cG d L)
    (fun t => t.2) (fun t => A.presum_dep t) (fun t => A.presum_meas t) hH0 hH0log hκ0nn hκ1nn hcG
    (fun Y => dExt_nonneg Y) hHb hKc0 (fun b => by rw [Finset.sum_filter]; convert hG2c b)
    hG3T (by linarith) hq hG1 hKc0 hκ' hcG (fun b => by convert hG2c b) hG3P hκ1 hα1
  obtain ⟨h1, -, h3⟩ := hmain
  have hαeq : 2 * (2 * (2 * εH * Kc) * Kc * Real.exp ((κH - 2 * κ0) * cG d L)) * c1 d L * Kc *
      Real.exp (c1 d L + κ' * cG d L) = εH * Kc * CPE d L Kc κH κ0 κ' := by
    unfold CPE
    rw [show Real.exp ((κH - 2 * κ0) * cG d L + c1 d L + κ' * cG d L) =
      Real.exp ((κH - 2 * κ0) * cG d L) * Real.exp (c1 d L + κ' * cG d L) by
      rw [← Real.exp_add]; congr 1; ring]
    ring
  refine ⟨_, ?_, h3.trans (le_of_eq (by rw [hαeq]))⟩
  have hsum : ∀ Φ : ∀ b, Ωb b, ∑ y, A.H y Φ = ∑ T, presum Lab A.H T Φ := fun Φ =>
    (presum_sum Lab hN le_rfl hΩ A.H Φ).symm
  simp_rw [hsum]
  exact h1

end Cluster

end Balaban.Fluctuation
