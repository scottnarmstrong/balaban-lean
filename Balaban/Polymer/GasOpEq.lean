/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Polymer.GasOpCore
public import Balaban.Polymer.Mayer

/-!
# GAS with a general activation rule, for weights that are functions of the configuration

The operator-valued gas of `GasOperator.lean` (Lean item P10) with the activation rule of
`GasOpCore.lean`.  The configuration `Φ ∈ ∏_b Ω_b` carries a product `⨂_b μ_b` of probability
measures; a heavy weight `τ Z` is the kernel of an operator acting on the variables of the blocks
`zs Z` (it depends on `Φ` only through them), and a coupling `β Y` depends on `Φ` through `cy Y`,
which may meet the supports of the heavy objects: the couplings read the variables that the heavy
operators integrate.  A σ-finite reference measure written as a density times a probability
measure (`LargeField.pi_withDensity_eq`) enters through the density, which is part of `τ`; so the
heavy weights are integrable, not bounded.  The couplings are bounded only where the heavy weights
that activate them do not vanish.

* `integrable_prod_depOn`: the product of integrable functions with pairwise disjoint dependence
  sets is integrable (with `integral_prod_depOn`, the multiplicativity of the expectation).
* `integrable_prod_gasW_of_actGasA`: the product of the weights of an admissible family is
  integrable.
* `actGasXiOp_eq`: the expectation of the partition function is the partition function of the
  polymer gas whose activities are the expectations of the cluster activities (pointwise this is
  `actGasXi_eq`).
-/

@[expose] public section

noncomputable section

open scoped Classical

open Finset MeasureTheory ProbabilityTheory

namespace Balaban.Polymer

section Independence

variable {B : Type*} [Fintype B] {Ω : B → Type*} [∀ b, MeasurableSpace (Ω b)]
  (μ : ∀ b, Measure (Ω b)) [∀ b, IsProbabilityMeasure (μ b)]

/-- The product of integrable functions with pairwise disjoint dependence sets is integrable for
the product measure. -/
theorem integrable_prod_depOn {ι : Type*} (Γ : Finset ι) (S : ι → Finset B)
    (F : ι → (∀ b, Ω b) → ℂ) (hdisj : ∀ i ∈ Γ, ∀ j ∈ Γ, i ≠ j → Disjoint (S i) (S j))
    (hdep : ∀ i ∈ Γ, DepOn (S i) (F i)) (hmeas : ∀ i, Measurable (F i))
    (hint : ∀ i ∈ Γ, Integrable (F i) (Measure.pi μ)) :
    Integrable (fun Φ => ∏ i ∈ Γ, F i Φ) (Measure.pi μ) := by
  induction Γ using Finset.induction_on with
  | empty => simp
  | insert i Γ hi ih =>
    have hdisj' : ∀ a ∈ Γ, ∀ b ∈ Γ, a ≠ b → Disjoint (S a) (S b) := fun a ha b hb hab =>
      hdisj a (Finset.mem_insert_of_mem ha) b (Finset.mem_insert_of_mem hb) hab
    have hdep' : ∀ a ∈ Γ, DepOn (S a) (F a) := fun a ha => hdep a (Finset.mem_insert_of_mem ha)
    have hint' : ∀ a ∈ Γ, Integrable (F a) (Measure.pi μ) := fun a ha =>
      hint a (Finset.mem_insert_of_mem ha)
    have hT : DepOn (Γ.biUnion S) (fun Φ => ∏ j ∈ Γ, F j Φ) := fun Φ Φ' hΦ => by
      refine Finset.prod_congr rfl (fun j hj => hdep' j hj Φ Φ' (fun b hb => hΦ b ?_))
      exact Finset.mem_biUnion.mpr ⟨j, hj, hb⟩
    have hdisjT : Disjoint (S i) (Γ.biUnion S) := by
      rw [Finset.disjoint_biUnion_right]
      exact fun j hj => hdisj i (Finset.mem_insert_self _ _) j (Finset.mem_insert_of_mem hj)
        (fun h => hi (h ▸ hj))
    have hmT : Measurable (fun Φ => ∏ j ∈ Γ, F j Φ) :=
      Finset.measurable_prod _ (fun j _ => hmeas j)
    have hind := indepFun_of_depOn μ hdisjT (hmeas i) hmT (hdep i (Finset.mem_insert_self _ _)) hT
    simp_rw [Finset.prod_insert hi]
    exact hind.integrable_mul (hint i (Finset.mem_insert_self _ _)) (ih hdisj' hdep' hint')

/-- The expectation of a product of norms of functions with pairwise disjoint dependence sets is
the product of the expectations. -/
theorem integral_prod_norm_depOn {ι : Type*} (Γ : Finset ι) (S : ι → Finset B)
    (F : ι → (∀ b, Ω b) → ℂ) (hdisj : ∀ i ∈ Γ, ∀ j ∈ Γ, i ≠ j → Disjoint (S i) (S j))
    (hdep : ∀ i ∈ Γ, DepOn (S i) (F i)) (hmeas : ∀ i, Measurable (F i)) :
    ∫ Φ, ∏ i ∈ Γ, ‖F i Φ‖ ∂(Measure.pi μ) = ∏ i ∈ Γ, ∫ Φ, ‖F i Φ‖ ∂(Measure.pi μ) := by
  have h := integral_prod_depOn μ Γ S (fun i Φ => ((‖F i Φ‖ : ℝ) : ℂ)) hdisj
    (fun i hi Φ Φ' hΦ => congrArg (fun w => ((‖w‖ : ℝ) : ℂ)) (hdep i hi Φ Φ' hΦ))
    (fun i => (hmeas i).norm.complex_ofReal)
  have e1 : ∀ Φ : ∀ b, Ω b, ∏ i ∈ Γ, ((‖F i Φ‖ : ℝ) : ℂ) = ((∏ i ∈ Γ, ‖F i Φ‖ : ℝ) : ℂ) :=
    fun Φ => (Complex.ofReal_prod _ _).symm
  have e2 : ∀ i, ∫ Φ, ((‖F i Φ‖ : ℝ) : ℂ) ∂(Measure.pi μ) =
      ((∫ Φ, ‖F i Φ‖ ∂(Measure.pi μ) : ℝ) : ℂ) := fun i => integral_ofReal
  have e3 : ∫ Φ, ((∏ i ∈ Γ, ‖F i Φ‖ : ℝ) : ℂ) ∂(Measure.pi μ) =
      ((∫ Φ, ∏ i ∈ Γ, ‖F i Φ‖ ∂(Measure.pi μ) : ℝ) : ℂ) := integral_ofReal
  simp only [e1, e2] at h
  rw [e3, ← Complex.ofReal_prod] at h
  exact_mod_cast h

end Independence

section Operator

variable {B Yt Zt : Type*} [Fintype B] [Fintype Yt] [Fintype Zt]
  {Ω : B → Type*} [∀ b, MeasurableSpace (Ω b)]
  (act : Yt → Finset Zt → Prop) (cy : Yt → Finset B) (zs : Zt → Finset B)
  (β : Yt → (∀ b, Ω b) → ℂ) (τ : Zt → (∀ b, Ω b) → ℂ)

/-- The activity integrand of the polymer `X` at the configuration `Φ`. -/
def actGasActOp (X : NePoly B) (Φ : ∀ b, Ω b) : ℂ :=
  actGasK act cy zs (fun y => β y Φ) (fun z => τ z Φ) X

variable (μ : ∀ b, Measure (Ω b))

/-- The activity of the polymer `X`: the expectation of the activity integrand. -/
def actGasKOp (X : NePoly B) : ℂ := ∫ Φ, actGasActOp act cy zs β τ X Φ ∂(Measure.pi μ)

/-- The partition function: the expectation of the pointwise partition function. -/
def actGasXiOp : ℂ :=
  ∫ Φ, actGasXi act zs (fun y => β y Φ) (fun z => τ z Φ) ∂(Measure.pi μ)

variable {act cy zs β τ μ}

omit [Fintype B] [Fintype Yt] [Fintype Zt] [(b : B) → MeasurableSpace (Ω b)] in
theorem gasW_inl (Φ : ∀ b, Ω b) (y : Yt) :
    gasW (fun y => β y Φ) (fun z => τ z Φ) (Sum.inl y) = Complex.exp (β y Φ) - 1 := rfl

omit [Fintype B] [Fintype Yt] [Fintype Zt] [(b : B) → MeasurableSpace (Ω b)] in
theorem gasW_inr (Φ : ∀ b, Ω b) (z : Zt) :
    gasW (fun y => β y Φ) (fun z => τ z Φ) (Sum.inr z) = τ z Φ := rfl

omit [Fintype B] [Fintype Yt] [Fintype Zt] in
theorem measurable_gasW (hβ : ∀ y, Measurable (β y)) (hτ : ∀ z, Measurable (τ z))
    (t : Yt ⊕ Zt) :
    Measurable (fun Φ : ∀ b, Ω b => gasW (fun y => β y Φ) (fun z => τ z Φ) t) := by
  rcases t with y | z
  · exact (Complex.measurable_exp.comp (hβ y)).sub_const 1
  · exact hτ z

omit [Fintype B] in
theorem measurable_actGasActOp (hβm : ∀ y, Measurable (β y)) (hτm : ∀ z, Measurable (τ z))
    (X : NePoly B) : Measurable (actGasActOp act cy zs β τ X) := by
  unfold actGasActOp actGasK polyAct
  exact Finset.measurable_fun_sum _ (fun C _ =>
    Finset.measurable_fun_prod _ (fun t _ => measurable_gasW hβm hτm t))

omit [Fintype B] [(b : B) → MeasurableSpace (Ω b)] in
theorem depOn_actGasActOp (hβ : ∀ y, DepOn (cy y) (β y)) (hτ : ∀ z, DepOn (zs z) (τ z))
    (X : NePoly B) : DepOn X.1 (actGasActOp act cy zs β τ X) := by
  intro Φ Φ' hΦ
  unfold actGasActOp actGasK polyAct
  refine Finset.sum_congr rfl (fun C hC => Finset.prod_congr rfl (fun t ht => ?_))
  have hsub : gasCs cy zs t ⊆ X.1 := sub_of_mem_Cfam hC ht
  rcases t with y | z
  · simp only [gasCs_inl] at hsub
    rw [gasW_inl, gasW_inl, hβ y Φ Φ' (fun b hb => hΦ b (hsub hb))]
  · simp only [gasCs_inr] at hsub
    rw [gasW_inr, gasW_inr, hτ z Φ Φ' (fun b hb => hΦ b (hsub hb))]

omit [Fintype B] [Fintype Yt] [Fintype Zt] [(b : B) → MeasurableSpace (Ω b)] in
/-- Pointwise bound of the product of the weights of a family: where the heavy weights of the
family do not vanish the coupling weights are bounded by `s`. -/
theorem norm_prod_gasW_le {s : Yt → ℝ} {C : Finset (Yt ⊕ Zt)} (Φ : ∀ b, Ω b)
    (hs : (∀ z ∈ C.toRight, τ z Φ ≠ 0) → ∀ y ∈ C.toLeft, ‖Complex.exp (β y Φ) - 1‖ ≤ s y) :
    ‖∏ t ∈ C, gasW (fun y => β y Φ) (fun z => τ z Φ) t‖ ≤
      (∏ y ∈ C.toLeft, s y) * ∏ z ∈ C.toRight, ‖τ z Φ‖ := by
  rw [prod_gasW, norm_mul, norm_prod, norm_prod]
  by_cases h : ∀ z ∈ C.toRight, τ z Φ ≠ 0
  · exact mul_le_mul_of_nonneg_right
      (Finset.prod_le_prod₀ (fun y _ => norm_nonneg _) (hs h))
      (Finset.prod_nonneg (fun z _ => norm_nonneg _))
  · push Not at h
    obtain ⟨z, hz, h0⟩ := h
    have : ∏ z ∈ C.toRight, ‖τ z Φ‖ = 0 := Finset.prod_eq_zero hz (by simp [h0])
    rw [this, mul_zero, mul_zero]

variable [∀ b, IsProbabilityMeasure (μ b)]

omit [Fintype Yt] [Fintype Zt] in
/-- The product of the weights of an admissible family is integrable. -/
theorem integrable_prod_gasW_of_actGasA {s : Yt → ℝ}
    (hτd : ∀ z, DepOn (zs z) (τ z)) (hβm : ∀ y, Measurable (β y)) (hτm : ∀ z, Measurable (τ z))
    (hτi : ∀ z, Integrable (τ z) (Measure.pi μ))
    (hB : ∀ Γ : Finset Zt, (∀ z ∈ Γ, ∀ z' ∈ Γ, z ≠ z' → Disjoint (zs z) (zs z')) →
      ∀ y, act y Γ → ∀ Φ, (∀ z ∈ Γ, τ z Φ ≠ 0) → ‖Complex.exp (β y Φ) - 1‖ ≤ s y)
    {C : Finset (Yt ⊕ Zt)} (hC : actGasA act zs C) :
    Integrable (fun Φ => ∏ t ∈ C, gasW (fun y => β y Φ) (fun z => τ z Φ) t) (Measure.pi μ) := by
  have hT := integrable_prod_depOn μ C.toRight zs τ hC.1 (fun z _ => hτd z) hτm
    (fun z _ => hτi z)
  refine Integrable.mono' (hT.norm.const_mul (∏ y ∈ C.toLeft, s y))
    (Finset.measurable_prod _ (fun t _ => measurable_gasW hβm hτm t)).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun Φ => ?_))
  exact (norm_prod_gasW_le Φ (fun h y hy => hB _ hC.1 y (hC.2 y hy) Φ h)).trans_eq
    (by rw [norm_prod])

theorem integrable_actGasActOp {s : Yt → ℝ}
    (hτd : ∀ z, DepOn (zs z) (τ z)) (hβm : ∀ y, Measurable (β y)) (hτm : ∀ z, Measurable (τ z))
    (hτi : ∀ z, Integrable (τ z) (Measure.pi μ))
    (hB : ∀ Γ : Finset Zt, (∀ z ∈ Γ, ∀ z' ∈ Γ, z ≠ z' → Disjoint (zs z) (zs z')) →
      ∀ y, act y Γ → ∀ Φ, (∀ z ∈ Γ, τ z Φ ≠ 0) → ‖Complex.exp (β y Φ) - 1‖ ≤ s y)
    (X : NePoly B) : Integrable (actGasActOp act cy zs β τ X) (Measure.pi μ) := by
  unfold actGasActOp actGasK polyAct
  exact integrable_finsetSum _ (fun C hC =>
    integrable_prod_gasW_of_actGasA hτd hβm hτm hτi hB (mem_Cfam.mp hC).2.1)

/-- **GAS with a general activation rule, for functions of the configuration (identity).**  The
expectation of the partition function is the partition function of the polymer gas of connected
clusters, with the expected activities.  The heavy weights are integrable and the couplings are
bounded where the heavy weights activating them do not vanish. -/
theorem actGasXiOp_eq (hz : ∀ z, (zs z).Nonempty)
    (hloc : ∀ y Γ, act y Γ ↔ act y (Γ.filter (fun z => ¬ Disjoint (cy y) (zs z))))
    (hmeet : ∀ y Γ, act y Γ → ∃ z ∈ Γ, ¬ Disjoint (cy y) (zs z))
    (hβd : ∀ y, DepOn (cy y) (β y)) (hτd : ∀ z, DepOn (zs z) (τ z))
    (hβm : ∀ y, Measurable (β y)) (hτm : ∀ z, Measurable (τ z))
    (hτi : ∀ z, Integrable (τ z) (Measure.pi μ)) {s : Yt → ℝ}
    (hB : ∀ Γ : Finset Zt, (∀ z ∈ Γ, ∀ z' ∈ Γ, z ≠ z' → Disjoint (zs z) (zs z')) →
      ∀ y, act y Γ → ∀ Φ, (∀ z ∈ Γ, τ z Φ ≠ 0) → ‖Complex.exp (β y Φ) - 1‖ ≤ s y) :
    actGasXiOp act zs β τ μ =
      Xi (shareBlock (Subtype.val : NePoly B → Finset B)) (actGasKOp act cy zs β τ μ) := by
  unfold actGasXiOp
  have hpt : ∀ Φ : ∀ b, Ω b,
      actGasXi act zs (fun y => β y Φ) (fun z => τ z Φ) =
        Xi (shareBlock (Subtype.val : NePoly B → Finset B))
          (fun X => actGasActOp act cy zs β τ X Φ) :=
    fun Φ => actGasXi_eq (fun y => β y Φ) (fun z => τ z Φ) hz hloc hmeet
  simp_rw [hpt]
  unfold Xi
  have hdisj : ∀ Γ ∈ (Finset.univ : Finset (Finset (NePoly B))).filter
      (Compat (shareBlock (Subtype.val : NePoly B → Finset B))),
      ∀ X ∈ Γ, ∀ X' ∈ Γ, X ≠ X' → Disjoint X.1 X'.1 := by
    intro Γ hΓ X hX X' hX' hne'
    have := (Finset.mem_filter.mp hΓ).2 X hX X' hX' hne'
    rw [lnk_shareBlock] at this
    exact not_not.mp this
  rw [integral_finsetSum _ (fun Γ hΓ => integrable_prod_depOn μ Γ (fun X => X.1)
    (fun X => actGasActOp act cy zs β τ X) (hdisj Γ hΓ) (fun X _ => depOn_actGasActOp hβd hτd X)
    (measurable_actGasActOp hβm hτm) (fun X _ => integrable_actGasActOp hτd hβm hτm hτi hB X))]
  refine Finset.sum_congr rfl (fun Γ hΓ => ?_)
  exact integral_prod_depOn μ Γ (fun X => X.1) (fun X => actGasActOp act cy zs β τ X)
    (hdisj Γ hΓ) (fun X _ => depOn_actGasActOp hβd hτd X) (measurable_actGasActOp hβm hτm)

end Operator

end Balaban.Polymer
