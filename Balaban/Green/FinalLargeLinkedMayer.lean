/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Polymer.Mayer

/-!
# Linked terms with separate activation and footprint

The landed Mayer theorem gives a connected footprint after local potentials are put on a
product measure. Activation by a selected bad set is tracked separately. The physical P7
covariance, determinant and crossing potentials must still be constructed and estimated.
-/

@[expose] public section

noncomputable section

open scoped Classical
open Finset MeasureTheory Balaban.Polymer

namespace Balaban.Green

/-- A cluster may have a disconnected activation set, but its activation sites lie in its
footprint when each local term is supported at its activating site. -/
theorem linked_activation_subset_footprint
    {B T : Type*} [Fintype B] [Fintype T]
    (foot : T → Finset B) (act : T → B)
    (hact : ∀ t, act t ∈ foot t) (C : Finset T) :
    C.image act ⊆ unionCs foot C := by
  intro b hb
  obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hb
  exact mem_unionCs.mpr ⟨t, ht, hact t⟩

/-- In a linked Mayer cluster every elementary term must be activated. Its activation set is
the image of its term family under `act`, while its footprint is `unionCs foot C`. -/
theorem linked_mayerAct_eq_sum_active
    {B T : Type*} [Fintype B] [Fintype T]
    {Ω : B → Type*} (foot : T → Finset B) (act : T → B)
    (H : T → (∀ b, Ω b) → ℂ) (Z : Finset B)
    (Y : NePoly B) (Φ : ∀ b, Ω b) :
    mayerAct foot (fun t Φ => if act t ∈ Z then H t Φ else 0) Y Φ =
      ∑ C ∈ Cfam foot (fun _ : Finset T => True) Y.1,
        if C.image act ⊆ Z then ∏ t ∈ C, (Complex.exp (H t Φ) - 1) else 0 := by
  classical
  unfold mayerAct polyAct
  apply Finset.sum_congr rfl
  intro C _
  by_cases hC : C.image act ⊆ Z
  · rw [ite_eq_left hC]
    apply Finset.prod_congr rfl
    intro t ht
    have hat : act t ∈ Z := hC (Finset.mem_image.mpr ⟨t, ht, rfl⟩)
    simp [hat]
  · rw [ite_eq_right hC]
    obtain ⟨b, hb, hbZ⟩ := Finset.not_subset.mp hC
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hb
    apply Finset.prod_eq_zero ht
    simp [hbZ]

/-- After the good variables are integrated, each connected footprint has fixed linked
coefficients. Selection of the bad family enters only through `C.image act ⊆ Z`; the
coefficients themselves do not depend on `Z`. -/
theorem linked_mayerK_eq_sum_fixed
    {B T : Type*} [Fintype B] [Fintype T]
    {Ω : B → Type*} [∀ b, MeasurableSpace (Ω b)]
    (μ : ∀ b, Measure (Ω b)) [∀ b, IsProbabilityMeasure (μ b)]
    (foot : T → Finset B) (act : T → B)
    (H : T → (∀ b, Ω b) → ℂ) (Z : Finset B)
    (hmeas : ∀ t, Measurable (H t)) (hbdd : ∀ t, Bdd (H t))
    (Y : NePoly B) :
    mayerK μ foot (fun t Φ => if act t ∈ Z then H t Φ else 0) Y =
      ∑ C ∈ Cfam foot (fun _ : Finset T => True) Y.1,
        if C.image act ⊆ Z then
          ∫ Φ, (∏ t ∈ C, (Complex.exp (H t Φ) - 1)) ∂(Measure.pi μ)
        else 0 := by
  let HC : Finset T → (∀ b, Ω b) → ℂ :=
    fun C Φ => ∏ t ∈ C, (Complex.exp (H t Φ) - 1)
  have hint : ∀ C : Finset T, Integrable (HC C) (Measure.pi μ) := by
    intro C
    have hm : Measurable (HC C) :=
      Finset.measurable_prod _ (fun t _ =>
        (Complex.measurable_exp.comp (hmeas t)).sub_const 1)
    obtain ⟨M, hM⟩ : Bdd (HC C) :=
      Bdd.prod C (fun t _ => bdd_expm1 (hbdd t))
    exact Integrable.of_bound hm.aestronglyMeasurable M (Filter.Eventually.of_forall hM)
  have hfun : (fun Φ => mayerAct foot
      (fun t Φ => if act t ∈ Z then H t Φ else 0) Y Φ) =
      fun Φ => ∑ C ∈ Cfam foot (fun _ : Finset T => True) Y.1,
        if C.image act ⊆ Z then HC C Φ else 0 := by
    funext Φ
    exact linked_mayerAct_eq_sum_active foot act H Z Y Φ
  change ∫ Φ, mayerAct foot
    (fun t Φ => if act t ∈ Z then H t Φ else 0) Y Φ ∂(Measure.pi μ) = _
  rw [hfun]
  rw [integral_finsetSum _ (fun C _ => by
    by_cases hC : C.image act ⊆ Z
    · simpa [hC] using hint C
    · simp [hC])]
  apply Finset.sum_congr rfl
  intro C _
  by_cases hC : C.image act ⊆ Z
  · simp [hC, HC]
  · simp [hC]

/-- Each fixed connected-cluster coefficient has exponential decay in its whole footprint.
This is the bound needed before summing clusters with the same activation and footprint.
The one-term smallness condition is explicit and independent of the volume. -/
theorem linked_cluster_integral_bound
    {B T : Type*} [Fintype B] [Fintype T]
    {Ω : B → Type*} [∀ b, MeasurableSpace (Ω b)]
    (μ : ∀ b, Measure (Ω b)) [∀ b, IsProbabilityMeasure (μ b)]
    (foot : T → Finset B) (H : T → (∀ b, Ω b) → ℂ)
    (dist : Finset B → ℝ) {H0 κ0 κ1 c : ℝ}
    (hH0 : 0 ≤ H0) (hH0' : H0 ≤ Real.log 2)
    (hκ0 : 0 ≤ κ0) (hκ1 : 0 ≤ κ1) (hc : 0 ≤ c)
    (hdist : ∀ Y, 0 ≤ dist Y)
    (hH : ∀ t Φ, ‖H t Φ‖ ≤ H0 * Real.exp (-(κ0 + κ1) * dist (foot t)))
    (hG3 : ∀ C : Finset T, ConnSet foot C →
      dist (unionCs foot C) ≤ ∑ t ∈ C, dist (foot t) + c * ((C.card : ℝ) - 1))
    (hsmall : 2 * H0 * Real.exp (κ1 * c) ≤ 1)
    (C : Finset T) (hC : ConnSet foot C) :
    ‖∫ Φ, (∏ t ∈ C, (Complex.exp (H t Φ) - 1)) ∂(Measure.pi μ)‖ ≤
      Real.exp (-κ1 * dist (unionCs foot C)) := by
  have hρ : ∀ t, 0 ≤ mayerRho foot dist κ0 H0 t :=
    mayerRho_nonneg (sup := foot) (d := dist) (κ0 := κ0) hH0
  have hterm : ∀ t,
      0 ≤ mayerRho foot dist κ0 H0 t * Real.exp (κ1 * c) ∧
      mayerRho foot dist κ0 H0 t * Real.exp (κ1 * c) ≤ 1 := by
    intro t
    have he : Real.exp (-κ0 * dist (foot t)) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by nlinarith [hdist (foot t)])
    constructor
    · exact mul_nonneg (hρ t) (Real.exp_pos _).le
    · unfold mayerRho
      calc
        (2 * H0 * Real.exp (-κ0 * dist (foot t))) * Real.exp (κ1 * c) ≤
            (2 * H0 * 1) * Real.exp (κ1 * c) := by
              apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
              exact mul_le_mul_of_nonneg_left he (by positivity)
        _ = 2 * H0 * Real.exp (κ1 * c) := by ring
        _ ≤ 1 := hsmall
  have hprod : ∏ t ∈ C, (mayerRho foot dist κ0 H0 t * Real.exp (κ1 * c)) ≤ 1 :=
    Finset.prod_le_one₀ (fun t _ => (hterm t).1) (fun t _ => (hterm t).2)
  have hpoint : ∀ Φ : ∀ b, Ω b,
      ‖∏ t ∈ C, (Complex.exp (H t Φ) - 1)‖ ≤
        Real.exp (-κ1 * dist (unionCs foot C)) := by
    intro Φ
    have hmajor := prod_a_le (sup := foot) (d := dist) (κ0 := κ0)
      (κ1 := κ1) (c := c) (H0 := H0) hκ1 hρ hG3 hC
    have hEc : Real.exp (-κ1 * c) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by nlinarith)
    calc
      ‖∏ t ∈ C, (Complex.exp (H t Φ) - 1)‖ =
          ∏ t ∈ C, ‖Complex.exp (H t Φ) - 1‖ := norm_prod _ _
      _ ≤ ∏ t ∈ C, (mayerRho foot dist κ0 H0 t *
          Real.exp (-κ1 * dist (foot t))) :=
        Finset.prod_le_prod₀ (fun t _ => norm_nonneg _)
          (fun t _ => norm_expm1_le_rho (sup := foot) (H := H) (d := dist)
            hH0 hH0' hκ0 hκ1 hdist t Φ (hH t Φ))
      _ ≤ Real.exp (-κ1 * dist (unionCs foot C)) * Real.exp (-κ1 * c) *
          ∏ t ∈ C, (mayerRho foot dist κ0 H0 t * Real.exp (κ1 * c)) := hmajor
      _ ≤ Real.exp (-κ1 * dist (unionCs foot C)) * Real.exp (-κ1 * c) := by
        simpa using mul_le_mul_of_nonneg_left hprod (by positivity :
          0 ≤ Real.exp (-κ1 * dist (unionCs foot C)) * Real.exp (-κ1 * c))
      _ ≤ Real.exp (-κ1 * dist (unionCs foot C)) := by
        simpa using mul_le_mul_of_nonneg_left hEc (Real.exp_pos _).le
  have hbound := norm_integral_le_of_norm_le_const (μ := Measure.pi μ)
    (C := Real.exp (-κ1 * dist (unionCs foot C))) (Filter.Eventually.of_forall hpoint)
  simpa using hbound

/-- With bounded local potentials, activating a term exactly when its marked site is bad
preserves the landed Mayer expansion and its volume-independent footprint bound. The linked
coefficient is `mayerK` of the activated potentials; its footprint is the union of a
connected family of the `foot t`. -/
theorem linked_mayer_of_activated_local_terms
    {B T : Type*} [Fintype B] [Fintype T]
    {Ω : B → Type*} [∀ b, MeasurableSpace (Ω b)]
    (μ : ∀ b, Measure (Ω b)) [∀ b, IsProbabilityMeasure (μ b)]
    (foot : T → Finset B) (act : T → B)
    (H : T → (∀ b, Ω b) → ℂ) (Z : Finset B)
    (hne : ∀ t, (foot t).Nonempty)
    (hloc : ∀ t, DepOn (foot t) (H t))
    (hmeas : ∀ t, Measurable (H t))
    (dist : Finset B → ℝ) {H0 κ0 κ1 c K0 c1 : ℝ}
    (hH0 : 0 ≤ H0) (hH0' : H0 ≤ Real.log 2) (hκ0 : 0 ≤ κ0)
    (hκ1 : 0 ≤ κ1) (hc : 0 ≤ c) (hdist : ∀ Y, 0 ≤ dist Y)
    (hH : ∀ t Φ, ‖H t Φ‖ ≤ H0 * Real.exp (-(κ0 + κ1) * dist (foot t)))
    (hG2 : ∀ b : B, ∑ t ∈ Finset.univ.filter (fun t => b ∈ foot t),
      Real.exp (-κ0 * dist (foot t)) ≤ K0)
    (hG3 : ∀ C : Finset T, ConnSet foot C →
      dist (unionCs foot C) ≤ ∑ t ∈ C, dist (foot t) + c * ((C.card : ℝ) - 1))
    (hc1 : 0 ≤ c1) (hq : 2 * H0 * K0 * Real.exp (κ1 * c) * c1 ≤ 1 / 2)
    (hG1 : ∀ Y : NePoly B, (Y.1.card : ℝ) ≤ c1 * (1 + dist Y.1)) :
    (∫ Φ, Complex.exp (∑ t : T, (if act t ∈ Z then H t Φ else 0)) ∂(Measure.pi μ)) =
      Xi (shareBlock (Subtype.val : NePoly B → Finset B))
        (mayerK μ foot (fun t Φ => if act t ∈ Z then H t Φ else 0)) ∧
    ∀ Y : NePoly B,
      ‖mayerK μ foot (fun t Φ => if act t ∈ Z then H t Φ else 0) Y‖ ≤
        2 * (2 * H0 * K0 * Real.exp (κ1 * c)) * c1 *
          Real.exp (-(κ1 - 3 / 2) * dist Y.1) := by
  let HZ : T → (∀ b, Ω b) → ℂ := fun t Φ => if act t ∈ Z then H t Φ else 0
  have hlocZ : ∀ t, DepOn (foot t) (HZ t) := by
    intro t Φ Φ' hΦ
    by_cases ht : act t ∈ Z
    · simp only [HZ, ite_eq_left ht]
      exact hloc t Φ Φ' hΦ
    · simp [HZ, ht]
  have hmeasZ : ∀ t, Measurable (HZ t) := by
    intro t
    by_cases ht : act t ∈ Z
    · simpa only [HZ, ite_eq_left ht] using hmeas t
    · simp [HZ, ht]
  have hHZ : ∀ t Φ, ‖HZ t Φ‖ ≤ H0 * Real.exp (-(κ0 + κ1) * dist (foot t)) := by
    intro t Φ
    by_cases ht : act t ∈ Z
    · simpa only [HZ, ite_eq_left ht] using hH t Φ
    · simp only [HZ, ite_eq_right ht, norm_zero]
      positivity
  have hbddZ : ∀ t, Bdd (HZ t) := fun t =>
    ⟨H0 * Real.exp (-(κ0 + κ1) * dist (foot t)), fun Φ => hHZ t Φ⟩
  constructor
  · exact mayer_integral_eq (μ := μ) (sup := foot) (H := HZ)
      hne hlocZ hmeasZ hbddZ
  · intro Y
    exact mayer_activity_bound (μ := μ) (sup := foot) (H := HZ) (d := dist)
      hH0 hH0' hκ0 hκ1 hc hdist hne hHZ
      hG2 hG3 hc1 hq Y (hG1 Y)

end Balaban.Green
