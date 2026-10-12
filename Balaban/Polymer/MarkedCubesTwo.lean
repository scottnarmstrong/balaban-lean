/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Polymer.MarkedCubesLocal
public import Balaban.Polymer.MarkedTermwise2
public import Balaban.Polymer.MarkedDeriv2
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Theorem 3.4, two marks (OBS X2) (FLUCTUATION.md §3.4)

The truncated expectation of two marks `G₁, G₂` is `∑_{S ⊇ (Y₁ ∪ Y₂) ∩ Ω} G**(S)`.

**The activity hypothesis is strengthened.**  The statement printed in FLUCTUATION.md, with
`ε_H ≤ ε_PE` and two marks of radius `ε_PE / 2`, is false (audit FL-A06): the one-mark application
already saturates the condition `hα` of `mayer_marked` at `ε_H = ε_PE`.  Here `ε_H ≤ ε_PE / 2`,
i.e. `ε_H ≤ 1 / (16 K₀³ c₁ E)` with `E = e^{(κ_H - 2κ₀) c_G + c₁ + κ' c_G}`, and the marks have
radii `ρ e^{κ₀ 𝗱(Y_i)} / F_i` with `ρ = 1 / (16 K₀² c₁ E)`.  The constant is `ρ⁻² = (16 K₀² c₁ E)²`.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Localization Balaban.Polymer MeasureTheory

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {m₀ j : ℕ} {Ω : Set (CTorus d L N₁ m₁ K)}

local notation "𝔅" => CubeB (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ j Ω

section Numerics

/-- The numerical conditions for two marks of radius `ρ` and `ε_H ≤ ε_PE / 2`. -/
theorem numerics_two {εH Kc c1v X Y : ℝ} (hεpos : 0 < εH) (hKc1 : 1 ≤ Kc) (hc1 : 1 ≤ c1v)
    (hX : 1 ≤ X) (hY : 1 ≤ Y) (hε : εH ≤ 1 / (16 * Kc ^ 3 * c1v * (X * Y))) :
    2 * (2 * (εH * Kc + 2 * (1 / (16 * Kc ^ 2 * c1v * (X * Y)))) * Kc * X) * c1v * Kc * Y ≤ 1 ∧
      2 * (εH * Kc + 2 * (1 / (16 * Kc ^ 2 * c1v * (X * Y)))) * Kc * X * c1v ≤ 1 / 2 ∧
      εH * Kc + 2 * (1 / (16 * Kc ^ 2 * c1v * (X * Y))) ≤ Real.log 2 := by
  have hKc0 : 0 < Kc := by linarith
  have hc0 : 0 < c1v := by linarith
  have hX0 : 0 < X := by linarith
  have hY0 : 0 < Y := by linarith
  have hP : 0 < 16 * Kc ^ 2 * c1v * (X * Y) := by positivity
  set ρ : ℝ := 1 / (16 * Kc ^ 2 * c1v * (X * Y)) with hρ
  have hρ0 : 0 < ρ := by positivity
  have hρP : ρ * (16 * Kc ^ 2 * c1v * (X * Y)) = 1 := by rw [hρ]; field_simp
  have hεK : εH * Kc ≤ ρ := by
    have h1 : εH * (16 * Kc ^ 3 * c1v * (X * Y)) ≤ 1 := by
      have := hε
      rwa [le_div_iff₀ (by positivity)] at this
    have h2 : (εH * Kc) * (16 * Kc ^ 2 * c1v * (X * Y)) ≤ ρ * (16 * Kc ^ 2 * c1v * (X * Y)) := by
      rw [hρP]; nlinarith
    exact le_of_mul_le_mul_right h2 hP
  have hH0 : εH * Kc + 2 * ρ ≤ 3 * ρ := by linarith
  have hH0n : 0 ≤ εH * Kc + 2 * ρ := by positivity
  refine ⟨?_, ?_, ?_⟩
  · have : 2 * (2 * (εH * Kc + 2 * ρ) * Kc * X) * c1v * Kc * Y =
        4 * (εH * Kc + 2 * ρ) * (Kc ^ 2 * c1v * (X * Y)) := by ring
    rw [this]
    have h3 : 4 * (εH * Kc + 2 * ρ) * (Kc ^ 2 * c1v * (X * Y)) ≤
        4 * (3 * ρ) * (Kc ^ 2 * c1v * (X * Y)) := by gcongr
    have h4 : 4 * (3 * ρ) * (Kc ^ 2 * c1v * (X * Y)) = 12 / 16 := by
      have : 4 * (3 * ρ) * (Kc ^ 2 * c1v * (X * Y)) = (12 / 16) * (ρ * (16 * Kc ^ 2 * c1v * (X * Y))) := by
        ring
      rw [this, hρP]; ring
    linarith
  · have hu : ρ * Kc * X * c1v ≤ 1 / 16 := by
      have h1 : ρ * Kc * X * c1v * (16 * (Kc * Y)) = 1 := by
        have : ρ * Kc * X * c1v * (16 * (Kc * Y)) = ρ * (16 * Kc ^ 2 * c1v * (X * Y)) := by ring
        rw [this, hρP]
      have h2 : 16 ≤ 16 * (Kc * Y) := by nlinarith
      have h3 : 0 ≤ ρ * Kc * X * c1v := by positivity
      nlinarith
    calc 2 * (εH * Kc + 2 * ρ) * Kc * X * c1v ≤ 2 * (3 * ρ) * Kc * X * c1v := by gcongr
      _ = 6 * (ρ * Kc * X * c1v) := by ring
      _ ≤ 1 / 2 := by linarith
  · have hρ16 : ρ ≤ 1 / 16 := by
      have h1 : 16 ≤ 16 * Kc ^ 2 * c1v * (X * Y) := by
        have : 1 ≤ Kc ^ 2 * c1v * (X * Y) := by
          have a1 : 1 ≤ Kc ^ 2 := one_le_pow₀ hKc1
          have a2 : 1 ≤ X * Y := one_le_mul_of_one_le_of_one_le hX hY
          have a3 : 1 ≤ Kc ^ 2 * c1v := one_le_mul_of_one_le_of_one_le a1 hc1
          exact one_le_mul_of_one_le_of_one_le a3 a2
        nlinarith
      nlinarith
    have := Real.log_two_gt_d9
    linarith

end Numerics

section Marks

variable {Lb : Type*} [Fintype Lb]

open Classical in
/-- The two marks, attached to the terms of `S₀` and `S₁`; index `false` is the first mark. -/
noncomputable def gMarks {Ωb : 𝔅 → Type*} (S₀ S₁ : Finset 𝔅) (G₀ G₁ : (∀ b, Ωb b) → ℂ) :
    Bool → NePoly 𝔅 → (∀ b, Ωb b) → ℂ :=
  fun i => cond i (gMark S₁ G₁ ()) (gMark S₀ G₀ ())

/-- **The local term `G**(S)`** (Theorem 3.4, two marks): the mixed derivative at `0` of the
`S`-term of the cluster sum when the marks `λ₀ G₀`, `λ₁ G₁` are added to the terms of `S₀`, `S₁`. -/
noncomputable def Gst2 {Ωb : 𝔅 → Type*} [∀ b, MeasurableSpace (Ωb b)]
    (μ : ∀ b, Measure (Ωb b)) [∀ b, IsProbabilityMeasure (μ b)] (Lab : CubeLabels m₀ j Ω Lb)
    (H : Lb → (∀ b, Ωb b) → ℂ) (S₀ S₁ : Finset 𝔅) (G₀ G₁ : (∀ b, Ωb b) → ℂ)
    (S : Finset 𝔅) : ℂ :=
  D2 false true (Ff (shareBlock (Subtype.val : NePoly 𝔅 → Finset 𝔅)) Subtype.val
    (marksK μ Subtype.val (presum Lab H) (gMarks S₀ S₁ G₀ G₁)) S)

omit [NeZero N₁] [NeZero L] in
theorem Hlam_two {Ωb : 𝔅 → Type*} (a : NePoly 𝔅 → (∀ b, Ωb b) → ℂ) (S₀ S₁ : Finset 𝔅)
    (G₀ G₁ : (∀ b, Ωb b) → ℂ) (l : Bool → ℂ) (t : NePoly 𝔅) (Φ : ∀ b, Ωb b) :
    Hlam a (gMarks S₀ S₁ G₀ G₁) l t Φ =
      a t Φ + l false * gMark S₀ G₀ () t Φ + l true * gMark S₁ G₁ () t Φ := by
  unfold Hlam
  rw [Fintype.sum_bool]
  simp only [gMarks, Bool.cond_true, Bool.cond_false]
  ring

omit [Fintype Lb] in
/-- A single mark term obeys `|λ G(t)| ≤ ρ e^{-(κ_H - κ₀) d_Ω(t)}` for `|λ| < ρ e^{κ₀ 𝗱(Y₀)}/F₀`. -/
theorem mark_term_bound {Ωb : 𝔅 → Type*} (hN : L ^ m₀ ∣ N₁) (hj : j ≤ K) (hΩ : IsPiUnion m₀ j Ω)
    (Lab : CubeLabels m₀ j Ω Lb) {κH κG κ0 F0 ρ : ℝ} (y0 : Lb) (G : (∀ b, Ωb b) → ℂ)
    (hG : ∀ Φ, ‖G Φ‖ ≤ F0 * Real.exp (-κG * Lab.dl y0)) (hF0 : 0 < F0) (hρ : 0 ≤ ρ)
    (hκHge : κ0 ≤ κH) (hκG : κH ≤ κG) (l : ℂ)
    (hl : ‖l‖ < ρ * Real.exp (κ0 * Lab.dl y0) / F0) (t : NePoly 𝔅) (Φ : ∀ b, Ωb b) :
    ‖l * gMark (blocksOf m₀ j Ω (Lab.ysite y0)) G () t Φ‖ ≤
      ρ * Real.exp (-(κH - κ0) * dExt t.1) := by
  classical
  set S0 := blocksOf m₀ j Ω (Lab.ysite y0) with hS0
  set r0 : ℝ := ρ * Real.exp (κ0 * Lab.dl y0) / F0 with hr0
  have hr0pos : 0 ≤ r0 := by positivity
  by_cases h : t.1 = S0
  · have hGt : ‖gMark S0 G () t Φ‖ ≤ F0 * Real.exp (-κG * Lab.dl y0) := by
      simpa [gMark, h] using hG Φ
    rw [norm_mul]
    calc ‖l‖ * ‖gMark S0 G () t Φ‖ ≤ r0 * (F0 * Real.exp (-κG * Lab.dl y0)) :=
          mul_le_mul hl.le hGt (norm_nonneg _) hr0pos
      _ = ρ * Real.exp (κ0 * Lab.dl y0 - κG * Lab.dl y0) := by
          rw [hr0, Real.exp_sub, show -κG * Lab.dl y0 = -(κG * Lab.dl y0) by ring, Real.exp_neg]
          field_simp
      _ ≤ ρ * Real.exp (-(κH - κ0) * dExt t.1) := by
          refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hρ
          have hd : dExt S0 ≤ Lab.dl y0 := Lab.dExt_le hN hj hΩ y0
          have : dExt t.1 ≤ Lab.dl y0 := h ▸ hd
          nlinarith [Lab.dl_nonneg y0]
  · have : gMark S0 G () t Φ = 0 := by simp [gMark, h]
    rw [this, mul_zero, norm_zero]
    positivity

/-- The constant `ρ⁻² = (16 K₀² c₁ E)²` of the two-mark bound, `E = e^{(κ_H - 2κ₀) c_G + c₁ + κ' c_G}`. -/
noncomputable def CPE2 (d L : ℕ) (Kc κH κ0 κ' : ℝ) : ℝ :=
  (16 * Kc ^ 2 * c1 d L * Real.exp ((κH - 2 * κ0) * cG d L + c1 d L + κ' * cG d L)) ^ 2

theorem marksXi_two_eq {Ωb : 𝔅 → Type*} [∀ b, MeasurableSpace (Ωb b)]
    (μ : ∀ b, Measure (Ωb b)) (hN : L ^ m₀ ∣ N₁) (hj : j ≤ K) (hΩ : IsPiUnion m₀ j Ω)
    (Lab : CubeLabels m₀ j Ω Lb) (H : Lb → (∀ b, Ωb b) → ℂ) (S₀ S₁ : Finset 𝔅)
    (hS₀ : S₀.Nonempty) (hS₁ : S₁.Nonempty) (G₀ G₁ : (∀ b, Ωb b) → ℂ) :
    marksXi μ (presum Lab H) (gMarks S₀ S₁ G₀ G₁) =
      Psi (Measure.pi μ) (fun Φ => ∑ y, H y Φ) (fun i : Bool => cond i G₁ G₀) := by
  funext l
  unfold marksXi Psi
  refine integral_congr_ae (Filter.Eventually.of_forall fun Φ => ?_)
  simp only []
  congr 1
  simp only [Hlam_two, Finset.sum_add_distrib, ← Finset.mul_sum, sum_gMark S₀ hS₀,
    sum_gMark S₁ hS₁, presum_sum Lab hN hj hΩ H Φ, Fintype.sum_bool, Bool.cond_true,
    Bool.cond_false]
  ring

open Classical in
/-- **Theorem 3.4, two marks (OBS X2), with the strengthened activity bound.**

For the activity bound `ε_H ≤ ε_PE / 2`, i.e. `ε_H ≤ 1 / (16 K₀³ c₁ E)` (the printed
`ε_H ≤ ε_PE` is not enough, audit FL-A06), the truncated expectation of `G₀, G₁` is
`⟨G₀ G₁⟩ - ⟨G₀⟩⟨G₁⟩ = ∑_S G**(S)`, where `G**(S) = 0` unless `S ⊇ S₀ ∪ S₁`
(`S_i = Y_i ∩ Ω`) and `|G**(S)| ≤ ρ⁻² F₀ F₁ e^{-κ₀(𝗱(Y₀) + 𝗱(Y₁))} e^{-κ' d_Ω(S)}`. -/
theorem marked_cubes_two {Ωb : 𝔅 → Type*} [∀ b, MeasurableSpace (Ωb b)]
    (μ : ∀ b, Measure (Ωb b)) [∀ b, IsProbabilityMeasure (μ b)]
    (hN : L ^ m₀ ∣ N₁) (hj : j ≤ K) (hΩ : IsPiUnion m₀ j Ω)
    {Lab : CubeLabels m₀ j Ω Lb} {εH κH κG₀ κG₁ κ0 κ' Kc F₀ F₁ : ℝ}
    (A : LabelAct Lab Ωb εH κH κ0 Kc) (y₀ y₁ : Lb) (G₀ G₁ : (∀ b, Ωb b) → ℂ)
    (hG₀m : Measurable G₀) (hG₁m : Measurable G₁)
    (hG₀dep : DepOn (blocksOf m₀ j Ω (Lab.ysite y₀)) G₀)
    (hG₁dep : DepOn (blocksOf m₀ j Ω (Lab.ysite y₁)) G₁)
    (hG₀ : ∀ Φ, ‖G₀ Φ‖ ≤ F₀ * Real.exp (-κG₀ * Lab.dl y₀))
    (hG₁ : ∀ Φ, ‖G₁ Φ‖ ≤ F₁ * Real.exp (-κG₁ * Lab.dl y₁))
    (hκ0 : aEnt d L + 1 ≤ κ0) (hKc : K0 d L κ0 + 1 ≤ Kc) (hεpos : 0 < εH)
    (hF₀ : 0 < F₀) (hF₁ : 0 < F₁) (hκ' : 0 ≤ κ') (hκG₀ : κH ≤ κG₀) (hκG₁ : κH ≤ κG₁)
    (hκ : κ' + 3 * κ0 + c1 d L + 3 / 2 ≤ κH)
    (hε : εH ≤ 1 / (16 * Kc ^ 3 * c1 d L *
      Real.exp ((κH - 2 * κ0) * cG d L + c1 d L + κ' * cG d L))) :
    (∫ Φ, Complex.exp (∑ y, A.H y Φ) ∂(Measure.pi μ) ≠ 0) ∧
    (((∫ Φ, G₀ Φ * (G₁ Φ * Complex.exp (∑ y, A.H y Φ)) ∂(Measure.pi μ)) /
        (∫ Φ, Complex.exp (∑ y, A.H y Φ) ∂(Measure.pi μ)) -
      ((∫ Φ, G₀ Φ * Complex.exp (∑ y, A.H y Φ) ∂(Measure.pi μ)) /
        (∫ Φ, Complex.exp (∑ y, A.H y Φ) ∂(Measure.pi μ))) *
      ((∫ Φ, G₁ Φ * Complex.exp (∑ y, A.H y Φ) ∂(Measure.pi μ)) /
        (∫ Φ, Complex.exp (∑ y, A.H y Φ) ∂(Measure.pi μ)))) =
        ∑ Y, Gst2 μ Lab A.H (blocksOf m₀ j Ω (Lab.ysite y₀)) (blocksOf m₀ j Ω (Lab.ysite y₁))
          G₀ G₁ Y ∧
      (∀ Y : Finset 𝔅, ¬ (blocksOf m₀ j Ω (Lab.ysite y₀) ⊆ Y ∧
          blocksOf m₀ j Ω (Lab.ysite y₁) ⊆ Y) →
        Gst2 μ Lab A.H (blocksOf m₀ j Ω (Lab.ysite y₀)) (blocksOf m₀ j Ω (Lab.ysite y₁))
          G₀ G₁ Y = 0) ∧
      ∀ Y : Finset 𝔅, ‖Gst2 μ Lab A.H (blocksOf m₀ j Ω (Lab.ysite y₀))
          (blocksOf m₀ j Ω (Lab.ysite y₁)) G₀ G₁ Y‖ ≤
        CPE2 d L Kc κH κ0 κ' * F₀ * F₁ * Real.exp (-κ0 * (Lab.dl y₀ + Lab.dl y₁)) *
          Real.exp (-κ' * dExt Y)) := by
  set S₀ := blocksOf m₀ j Ω (Lab.ysite y₀) with hS₀
  set S₁ := blocksOf m₀ j Ω (Lab.ysite y₁) with hS₁
  have hS₀ne : S₀.Nonempty := Lab.blocksOf_nonempty hN hj hΩ y₀
  have hS₁ne : S₁.Nonempty := Lab.blocksOf_nonempty hN hj hΩ y₁
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
  have hκHnn : 0 ≤ κH := by linarith
  set X : ℝ := Real.exp ((κH - 2 * κ0) * cG d L) with hX
  set Yc : ℝ := Real.exp (c1 d L + κ' * cG d L) with hYc
  have hE1 : Real.exp ((κH - 2 * κ0) * cG d L + c1 d L + κ' * cG d L) = X * Yc := by
    rw [hX, hYc, ← Real.exp_add]; congr 1; ring
  have hX1 : 1 ≤ X := Real.one_le_exp (by nlinarith [mul_nonneg hκ1nn hcG])
  have hY1 : 1 ≤ Yc := Real.one_le_exp (by nlinarith [mul_nonneg hκ' hcG])
  rw [hE1] at hε
  obtain ⟨hα1, hq, hH0log⟩ := numerics_two hεpos hKc1 hc1 hX1 hY1 hε
  set ρ : ℝ := 1 / (16 * Kc ^ 2 * c1 d L * (X * Yc)) with hρ
  have hρpos : 0 < ρ := by positivity
  set H0 : ℝ := εH * Kc + 2 * ρ with hH0
  have hH0nn : 0 ≤ H0 := by positivity
  -- the radii
  let dli : Bool → ℝ := fun i => cond i (Lab.dl y₁) (Lab.dl y₀)
  let Fi : Bool → ℝ := fun i => cond i F₁ F₀
  let rr : Bool → ℝ := fun i => ρ * Real.exp (κ0 * dli i) / Fi i
  have hFi : ∀ i, 0 < Fi i := fun i => by cases i <;> simpa [Fi]
  have hrr : ∀ i, 0 < rr i := fun i => by
    have := hFi i
    simp only [rr]; positivity
  have hexp_le : ∀ (κ x : ℝ), 0 ≤ κ → 0 ≤ x → Real.exp (-κ * x) ≤ 1 := fun κ x hκ hx =>
    Real.exp_le_one_iff.2 (by nlinarith)
  have hGC₀ : ∀ Φ, ‖G₀ Φ‖ ≤ F₀ := fun Φ => (hG₀ Φ).trans (by
    have := hexp_le κG₀ (Lab.dl y₀) (by linarith) (Lab.dl_nonneg y₀)
    nlinarith)
  have hGC₁ : ∀ Φ, ‖G₁ Φ‖ ≤ F₁ := fun Φ => (hG₁ Φ).trans (by
    have := hexp_le κG₁ (Lab.dl y₁) (by linarith) (Lab.dl_nonneg y₁)
    nlinarith)
  have hG2c := fun b : 𝔅 => (sum_exp_dExt_le hN hj b hκ0).trans hKc
  have hab : ∀ t, Bdd ((presum Lab A.H) t) := fun t => ⟨εH * Kc, fun Φ =>
    (A.presum_bound hN hj hΩ hεpos.le hκHge t Φ).trans (by
      have := hexp_le (κH - κ0) (dExt t.1) (by linarith) (dExt_nonneg t.1)
      have h0 : 0 ≤ εH * Kc := by positivity
      nlinarith)⟩
  have hH : ∀ l ∈ Balaban.Analysis.polydisc (0 : Bool → ℂ) rr, ∀ (t : NePoly 𝔅) (Φ : ∀ b, Ωb b),
      ‖Hlam (presum Lab A.H) (gMarks S₀ S₁ G₀ G₁) l t Φ‖ ≤
        H0 * Real.exp (-(κ0 + (κH - 2 * κ0)) * dExt t.1) := by
    intro l hl t Φ
    have hl0 : ‖l false‖ < ρ * Real.exp (κ0 * Lab.dl y₀) / F₀ := by simpa [rr, dli, Fi] using hl false
    have hl1 : ‖l true‖ < ρ * Real.exp (κ0 * Lab.dl y₁) / F₁ := by simpa [rr, dli, Fi] using hl true
    have b0 := A.presum_bound hN hj hΩ hεpos.le hκHge t Φ
    have b1 := mark_term_bound hN hj hΩ Lab y₀ G₀ hG₀ hF₀ hρpos.le hκHge hκG₀ (l false) hl0 t Φ
    have b2 := mark_term_bound hN hj hΩ Lab y₁ G₁ hG₁ hF₁ hρpos.le hκHge hκG₁ (l true) hl1 t Φ
    rw [Hlam_two]
    have hexpo : -(κ0 + (κH - 2 * κ0)) = -(κH - κ0) := by ring
    rw [hexpo, hH0]
    calc ‖presum Lab A.H t Φ + l false * gMark S₀ G₀ () t Φ + l true * gMark S₁ G₁ () t Φ‖
        ≤ ‖presum Lab A.H t Φ‖ + ‖l false * gMark S₀ G₀ () t Φ‖ +
          ‖l true * gMark S₁ G₁ () t Φ‖ := norm_add₃_le
      _ ≤ εH * Kc * Real.exp (-(κH - κ0) * dExt t.1) + ρ * Real.exp (-(κH - κ0) * dExt t.1) +
          ρ * Real.exp (-(κH - κ0) * dExt t.1) := add_le_add (add_le_add b0 b1) b2
      _ = _ := by ring
  have hg : ∀ (i : Bool) (t : NePoly 𝔅), Measurable (gMarks S₀ S₁ G₀ G₁ i t) := fun i t => by
    cases i
    · exact gMark_measurable S₀ hG₀m t
    · exact gMark_measurable S₁ hG₁m t
  have hgb : ∀ (i : Bool) (t : NePoly 𝔅), Bdd (gMarks S₀ S₁ G₀ G₁ i t) := fun i t => by
    cases i
    · exact gMark_bdd S₀ hF₀.le hGC₀ t
    · exact gMark_bdd S₁ hF₁.le hGC₁ t
  have hlocg : ∀ (i : Bool) (t : NePoly 𝔅), DepOn t.1 (gMarks S₀ S₁ G₀ G₁ i t) := fun i t => by
    cases i
    · exact gMark_dep S₀ hG₀dep t
    · exact gMark_dep S₁ hG₁dep t
  have hSz : ∀ (i : Bool) (t : NePoly 𝔅) (Φ : ∀ b, Ωb b), ¬ (cond i S₁ S₀) ⊆ t.1 →
      gMarks S₀ S₁ G₀ G₁ i t Φ = 0 := fun i t Φ h => by
    cases i
    · exact gMark_zero S₀ G₀ t Φ h
    · exact gMark_zero S₁ G₁ t Φ h
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
  obtain ⟨hana, hΨ0, hD2, hD2z, hD2b⟩ := mayer_marked_second (μ := μ)
    (Subtype.val : NePoly 𝔅 → Finset 𝔅) (a := presum Lab A.H) (g := gMarks S₀ S₁ G₀ G₁)
    (d := dExt) (H0 := H0) (κ0 := κ0) (κ1 := κH - 2 * κ0) (c := cG d L) (K0 := Kc)
    (c1 := c1 d L) (κ' := κ') (κ0P := κ0) (K0P := Kc) (cP := cG d L) (r := rr)
    (S := fun i => cond i S₁ S₀)
    (fun t => t.2) hrr (fun t => A.presum_meas t) hab hg hgb (fun t => A.presum_dep t) hlocg hSz
    hH0nn hH0log hκ0nn hκ1nn hcG (fun Y => dExt_nonneg Y) hH hKc0
    (fun b => by rw [Finset.sum_filter]; convert hG2c b) hG3T (by linarith) hq hG1 hκ' hcG
    (fun b => by convert hG2c b) hG3P hκ1 hα1
  -- identification of the partition function with marks
  have hXiEq := marksXi_two_eq μ hN hj hΩ Lab A.H S₀ S₁ hS₀ne hS₁ne G₀ G₁
  have hAm : Measurable (fun Φ => ∑ y, A.H y Φ) :=
    Finset.measurable_sum _ (fun y _ => A.meas y)
  have hκHnn' : 0 ≤ κH := hκHnn
  have hAb : ∀ Φ, ‖∑ y, A.H y Φ‖ ≤ ∑ y : Lb, εH := fun Φ =>
    (norm_sum_le _ _).trans (Finset.sum_le_sum fun y _ => (A.bound y Φ).trans (by
      have : Real.exp (-κH * Lab.dl y) ≤ 1 := Real.exp_le_one_iff.2 (by
        nlinarith [Lab.dl_nonneg y, hκHnn'])
      nlinarith))
  have hGm : ∀ k : Bool, Measurable (fun Φ => cond k G₁ G₀ Φ) := fun k => by
    cases k
    · exact hG₀m
    · exact hG₁m
  have hCG : 0 ≤ max F₀ F₁ := le_max_of_le_left hF₀.le
  have hGb : ∀ (k : Bool) Φ, ‖(cond k G₁ G₀) Φ‖ ≤ max F₀ F₁ := fun k Φ => by
    cases k
    · exact (hGC₀ Φ).trans (le_max_left _ _)
    · exact (hGC₁ Φ).trans (le_max_right _ _)
  have hana' : AnalyticOnNhd ℂ (Psi (Measure.pi μ) (fun Φ => ∑ y, A.H y Φ)
      (fun i : Bool => cond i G₁ G₀)) (Balaban.Analysis.polydisc 0 rr) := hXiEq ▸ hana
  have hD1f := D1_Psi hrr hana' hAm (fun k => hGm k) hCG hAb (fun k Φ => hGb k Φ) false
  have hD1t := D1_Psi hrr hana' hAm (fun k => hGm k) hCG hAb (fun k Φ => hGb k Φ) true
  have hD2ft := D2_Psi hrr hana' hAm (fun k => hGm k) hCG hAb (fun k Φ => hGb k Φ) false true
  have hΨ0' : marksXi μ (presum Lab A.H) (gMarks S₀ S₁ G₀ G₁) 0 =
      ∫ Φ, Complex.exp (∑ y, A.H y Φ) ∂(Measure.pi μ) := by
    rw [hXiEq]; unfold Psi; simp
  have hne : ∫ Φ, Complex.exp (∑ y, A.H y Φ) ∂(Measure.pi μ) ≠ 0 := by
    rw [← hΨ0']; exact hΨ0
  refine ⟨hne, ?_, ?_, ?_⟩
  · have h := hD2 (i := false) (j := true) (by simp)
    rw [hXiEq] at h
    have hPsi0 : Psi (Measure.pi μ) (fun Φ => ∑ y, A.H y Φ) (fun i : Bool => cond i G₁ G₀) 0 =
        ∫ Φ, Complex.exp (∑ y, A.H y Φ) ∂(Measure.pi μ) := by unfold Psi; simp
    simp only [Bool.cond_false, Bool.cond_true] at hD1f hD1t hD2ft
    rw [hD1f, hD1t, hD2ft, hPsi0] at h
    exact h
  · intro Y hY
    exact hD2z (i := false) (j := true) (Y := Y) (not_and_or.1 hY)
  · intro Y
    have hconst : 1 / rr false / rr true =
        CPE2 d L Kc κH κ0 κ' * F₀ * F₁ * Real.exp (-κ0 * (Lab.dl y₀ + Lab.dl y₁)) := by
      unfold CPE2
      rw [hE1]
      simp only [rr, dli, Fi, Bool.cond_true, Bool.cond_false]
      have e : Real.exp (-κ0 * (Lab.dl y₀ + Lab.dl y₁)) =
          (Real.exp (κ0 * Lab.dl y₀) * Real.exp (κ0 * Lab.dl y₁))⁻¹ := by
        rw [← Real.exp_add, ← Real.exp_neg]; congr 1; ring
      rw [e, hρ]
      have h1 := Real.exp_pos (κ0 * Lab.dl y₀)
      have h2 := Real.exp_pos (κ0 * Lab.dl y₁)
      have h3 : 0 < X * Yc := by positivity
      field_simp
    by_cases hY : S₀ ⊆ Y ∧ S₁ ⊆ Y
    · obtain ⟨b, hb⟩ := hS₀ne
      have h : ‖D2 false true (Ff (shareBlock (Subtype.val : NePoly 𝔅 → Finset 𝔅)) Subtype.val
          (marksK μ Subtype.val (presum Lab A.H) (gMarks S₀ S₁ G₀ G₁)) Y)‖ *
          Real.exp (κ' * (dExt Y + cG d L)) ≤
          (2 * (2 * H0 * Kc * Real.exp ((κH - 2 * κ0) * cG d L)) * c1 d L * Kc *
            Real.exp (c1 d L + κ' * cG d L)) / rr false / rr true :=
        hD2b (i := false) (j := true) (by simp) (b := b) hb Y (hY.1 hb)
      have hαle : (2 * (2 * H0 * Kc * Real.exp ((κH - 2 * κ0) * cG d L)) * c1 d L * Kc *
          Real.exp (c1 d L + κ' * cG d L)) / rr false / rr true ≤ 1 / rr false / rr true := by
        refine div_le_div_of_nonneg_right (div_le_div_of_nonneg_right hα1 (hrr false).le)
          (hrr true).le
      have hexp : Real.exp (κ' * dExt Y) ≤ Real.exp (κ' * (dExt Y + cG d L)) :=
        Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hcG) hκ')
      have h5 : ‖D2 false true (Ff (shareBlock (Subtype.val : NePoly 𝔅 → Finset 𝔅)) Subtype.val
          (marksK μ Subtype.val (presum Lab A.H) (gMarks S₀ S₁ G₀ G₁)) Y)‖ *
          Real.exp (κ' * dExt Y) ≤ 1 / rr false / rr true := by
        refine le_trans ?_ (h.trans hαle)
        exact mul_le_mul_of_nonneg_left hexp (norm_nonneg _)
      have h6 := le_of_mul_exp_le h5
      rw [hconst] at h6
      unfold Gst2
      rwa [show -κ' * dExt Y = -(κ' * dExt Y) by ring]
    · have h0 : Gst2 μ Lab A.H S₀ S₁ G₀ G₁ Y = 0 := by
        exact hD2z (i := false) (j := true) (Y := Y) (not_and_or.1 hY)
      rw [h0, norm_zero]
      unfold CPE2
      positivity

end Marks

end Balaban.Fluctuation
