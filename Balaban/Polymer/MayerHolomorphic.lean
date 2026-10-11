module

public import Balaban.Polymer.Mayer

/-!
# Holomorphy of the Mayer activities (MY (ii))

If the local terms `H t u Φ` are holomorphic in a complex parameter `u` on an open set `U` and
uniformly bounded, then the activities `K(Y, u) = ∫ ∑_C ∏_{t ∈ C} (e^{H t u Φ} - 1) dν` are
holomorphic on `U` (`differentiableOn_mayerK`).  The proof differentiates under the integral sign,
the derivative being dominated through the Cauchy estimate on a small circle
(`differentiableOn_integral_of_bound`).
-/

@[expose] public section

noncomputable section

open scoped Classical

open Finset MeasureTheory Metric Filter

namespace Balaban.Polymer

section Integral

variable {Ω' : Type*} [MeasurableSpace Ω'] (ν : Measure Ω') [IsFiniteMeasure ν]

/-- A uniformly bounded family of holomorphic functions has a holomorphic integral. -/
theorem differentiableOn_integral_of_bound {U : Set ℂ} (hU : IsOpen U) {F : ℂ → Ω' → ℂ} {M : ℝ}
    (hmeas : ∀ u, Measurable (F u)) (hdiff : ∀ Φ, DifferentiableOn ℂ (fun u => F u Φ) U)
    (hbd : ∀ u ∈ U, ∀ Φ, ‖F u Φ‖ ≤ M) :
    DifferentiableOn ℂ (fun u => ∫ Φ, F u Φ ∂ν) U := by
  intro u0 hu0
  refine DifferentiableAt.differentiableWithinAt ?_
  obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.mp hU u0 hu0
  set r : ℝ := ε / 4 with hr
  have hr0 : 0 < r := by positivity
  have hball : closedBall u0 (2 * r) ⊆ U := fun z hz =>
    hεU (by rw [mem_ball]; have := mem_closedBall.mp hz; linarith)
  have hsub : ∀ u ∈ ball u0 r, closedBall u r ⊆ U := fun u hu z hz => hball (by
    rw [mem_closedBall] at hz ⊢; rw [mem_ball] at hu
    calc dist z u0 ≤ dist z u + dist u u0 := dist_triangle _ _ _
      _ ≤ 2 * r := by linarith)
  have hderiv : ∀ Φ, ∀ u ∈ ball u0 r, HasDerivAt (fun v => F v Φ) (deriv (fun v => F v Φ) u) u := by
    intro Φ u hu
    have hUu : U ∈ nhds u := hU.mem_nhds (hsub u hu (mem_closedBall_self hr0.le))
    exact ((hdiff Φ).differentiableAt hUu).hasDerivAt
  have hcauchy : ∀ Φ, ∀ u ∈ ball u0 r, ‖deriv (fun v => F v Φ) u‖ ≤ M / r := by
    intro Φ u hu
    refine Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hr0 ?_ (fun z hz =>
      hbd z (hsub u hu (sphere_subset_closedBall hz)) Φ)
    refine DifferentiableOn.diffContOnCl ?_
    rw [closure_ball u hr0.ne']
    exact (hdiff Φ).mono (hsub u hu)
  have hmeas' : Measurable (fun Φ => deriv (fun v => F v Φ) u0) := by
    refine measurable_of_tendsto_metrizable (f := fun (n : ℕ) Φ =>
      ((1 / ((n : ℂ) + 1))⁻¹) • (F (u0 + 1 / ((n : ℂ) + 1)) Φ - F u0 Φ)) (fun n => ?_) ?_
    · exact ((hmeas _).sub (hmeas _)).const_smul ((1 / ((n : ℂ) + 1))⁻¹)
    · rw [tendsto_pi_nhds]
      intro Φ
      have h1 := (hasDerivAt_iff_tendsto_slope_zero.mp (hderiv Φ u0 (mem_ball_self hr0)))
      refine h1.comp ?_
      rw [tendsto_nhdsWithin_iff]
      refine ⟨tendsto_one_div_add_atTop_nhds_zero_nat, Eventually.of_forall (fun n => ?_)⟩
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      exact one_div_ne_zero (by exact_mod_cast Nat.succ_ne_zero n)
  have hint : Integrable (F u0) ν :=
    Integrable.of_bound (hmeas u0).aestronglyMeasurable M (Eventually.of_forall (hbd u0 hu0))
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := ν) (x₀ := u0)
    (F := fun u Φ => F u Φ) (F' := fun u Φ => deriv (fun v => F v Φ) u) (s := ball u0 r)
    (bound := fun _ => M / r) (ball_mem_nhds u0 hr0)
    (Eventually.of_forall (fun u => (hmeas u).aestronglyMeasurable)) hint hmeas'.aestronglyMeasurable
    (Eventually.of_forall (fun Φ u hu => hcauchy Φ u hu)) (integrable_const _)
    (Eventually.of_forall (fun Φ u hu => hderiv Φ u hu))
  exact key.2.differentiableAt

end Integral

section Mayer

variable {B : Type*} [Fintype B] {Ω : B → Type*} [∀ b, MeasurableSpace (Ω b)]
  (μ : ∀ b, Measure (Ω b)) [∀ b, IsProbabilityMeasure (μ b)]
  {T : Type*} [Fintype T] {sup : T → Finset B}

omit [Fintype B] in
omit [∀ b, MeasurableSpace (Ω b)] in
theorem bdd_polyAct_expm1 {X : Type*} (f : T → X → ℂ) (hf : ∀ t, Bdd (f t)) (Y : NePoly B) :
    Bdd (fun x => polyAct sup (fun _ : Finset T => True) (fun t => Complex.exp (f t x) - 1) Y) := by
  unfold polyAct
  refine Bdd.sum _ (fun C _ => Bdd.prod _ (fun t _ => ?_))
  obtain ⟨C, hC⟩ := hf t
  refine ⟨Real.exp C + 1, fun x => ?_⟩
  refine (norm_sub_le _ _).trans ?_
  rw [norm_one]
  exact add_le_add ((Complex.norm_exp_le_exp_norm _).trans (Real.exp_le_exp.mpr (hC x))) le_rfl

/-- **MY (ii)**: holomorphy of the Mayer activities in a complex parameter. -/
theorem differentiableOn_mayerK {U : Set ℂ} (hU : IsOpen U) {H : ℂ → T → (∀ b, Ω b) → ℂ}
    (hmeas : ∀ u t, Measurable (H u t))
    (hdiff : ∀ t Φ, DifferentiableOn ℂ (fun u => H u t Φ) U)
    (hbd : ∀ t, ∃ M : ℝ, ∀ u ∈ U, ∀ Φ, ‖H u t Φ‖ ≤ M) (Y : NePoly B) :
    DifferentiableOn ℂ (fun u => mayerK μ sup (H u) Y) U := by
  have hB : ∀ t, Bdd (fun p : {p : ℂ × (∀ b, Ω b) // p.1 ∈ U} => H p.1.1 t p.1.2) := fun t => by
    obtain ⟨M, hM⟩ := hbd t
    exact ⟨M, fun p => hM p.1.1 p.2 p.1.2⟩
  obtain ⟨M, hM⟩ := bdd_polyAct_expm1 (sup := sup) _ hB Y
  unfold mayerK
  refine differentiableOn_integral_of_bound (Measure.pi μ) hU (M := M) (F := fun u Φ => mayerAct sup (H u) Y Φ)
    (fun u => measurable_mayerAct (hmeas u) Y) (fun Φ => ?_) (fun u hu Φ => hM ⟨(u, Φ), hu⟩)
  unfold mayerAct polyAct
  refine DifferentiableOn.fun_sum (fun C _ => DifferentiableOn.fun_finsetProd (fun t _ => ?_))
  exact (Complex.differentiable_exp.comp_differentiableOn (hdiff t Φ)).sub_const 1

end Mayer

end Balaban.Polymer
