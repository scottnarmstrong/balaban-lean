/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Polymer.HoleOperator
public import Balaban.Polymer.Holomorphic
public import Balaban.Analysis.ParamIntegralDominated

/-!
# Analyticity and locality of GAS with a general activation rule in a parameter

The weights of `GasOpEq.lean` and `HoleOperator.lean` depending on a parameter `g` in a
finite-dimensional complex normed space (a source): couplings `β Y g Φ` and heavy weights
`τ Z g Φ`.

* `analyticOnNhd_actGasKOp`, `analyticOnNhd_actGasHoleKOp`: if the weights are analytic in `g` on an
  open set `U`, the couplings are bounded on the support of the heavy weights activating them
  uniformly for `g ∈ U`, and the heavy weights are dominated by integrable functions `T Z` of `Φ`
  with the dependence sets `zs Z`, the activities are analytic on `U`
  (`Analysis.analyticOnNhd_integral_of_dominated`).
* `analyticOnNhd_PY_actGas`, `analyticOnNhd_PY_actGasHole`: under the hypotheses of
  `actGasOp_pe` (resp. `actGasOp_pe_hole`) at every `g ∈ U` the local terms `P_g(Y)` are analytic on
  `U` (`pe_PY_analyticOnNhd` with the Kotecký–Preiss data of `pe_size`, resp. `pe_hole`).
* `PY_actGasKOp_congr`, `PY_actGasHoleKOp_congr`: the local term `P(Y)` depends only on the
  weights of the elementary objects supported in `Y`; for weights depending on `g` only on their
  supports, `P_g(Y)` reads `g` on `Y` only.
-/

@[expose] public section

noncomputable section

open scoped Classical

open Finset MeasureTheory

namespace Balaban.Polymer

section Local

variable {B Yt Zt : Type*} [Fintype B] [Fintype Yt] [Fintype Zt]
  {Ω : B → Type*} [∀ b, MeasurableSpace (Ω b)]
  {act : Yt → Finset Zt → Prop} {cy : Yt → Finset B} {zs : Zt → Finset B}
  {μ : ∀ b, Measure (Ω b)}

/-- The activity of `X` depends only on the weights of the elementary objects supported in `X`. -/
theorem actGasKOp_congr {β β' : Yt → (∀ b, Ω b) → ℂ} {τ τ' : Zt → (∀ b, Ω b) → ℂ}
    (X : NePoly B) (hβ : ∀ y, cy y ⊆ X.1 → β y = β' y) (hτ : ∀ z, zs z ⊆ X.1 → τ z = τ' z) :
    actGasKOp act cy zs β τ μ X = actGasKOp act cy zs β' τ' μ X := by
  unfold actGasKOp actGasActOp actGasK polyAct
  refine integral_congr_ae (Filter.Eventually.of_forall fun Φ => ?_)
  refine Finset.sum_congr rfl fun C hC => Finset.prod_congr rfl fun t ht => ?_
  have hsub := sub_of_mem_Cfam hC ht
  rcases t with y | z
  · simp only [gasCs_inl] at hsub
    rw [gasW_inl, gasW_inl, hβ y hsub]
  · simp only [gasCs_inr] at hsub
    rw [gasW_inr, gasW_inr, hτ z hsub]

/-- **Locality of the local terms**: `P(Y)` depends only on the weights of the elementary objects
supported in `Y`. -/
theorem PY_actGasKOp_congr {β β' : Yt → (∀ b, Ω b) → ℂ} {τ τ' : Zt → (∀ b, Ω b) → ℂ}
    (Y : Finset B) (hβ : ∀ y, cy y ⊆ Y → β y = β' y) (hτ : ∀ z, zs z ⊆ Y → τ z = τ' z) :
    PY (shareBlock (Subtype.val : NePoly B → Finset B)) Subtype.val
        (actGasKOp act cy zs β τ μ) Y =
      PY (shareBlock (Subtype.val : NePoly B → Finset B)) Subtype.val
        (actGasKOp act cy zs β' τ' μ) Y :=
  PY_congr _ _ Y fun X hX =>
    actGasKOp_congr X (fun y hy => hβ y (hy.trans hX)) (fun z hz => hτ z (hz.trans hX))

variable {H : SimpleGraph B} {S₀ : Finset B} {cyF : Yt → Finset B} {zsF : Zt → Finset B}

/-- The activity of a hole polymer `X` depends only on the weights of the elementary objects whose
charged supports lie in the charged support of `X`. -/
theorem actGasHoleKOp_congr {β β' : Yt → (∀ b, Ω b) → ℂ} {τ τ' : Zt → (∀ b, Ω b) → ℂ}
    (X : HolePolymer H S₀) (hβ : ∀ y, cy y ⊆ holeSupp H S₀ X → β y = β' y)
    (hτ : ∀ z, zs z ⊆ holeSupp H S₀ X → τ z = τ' z) :
    actGasHoleKOp H S₀ cyF zsF act cy zs β τ μ X = actGasHoleKOp H S₀ cyF zsF act cy zs β' τ' μ X := by
  unfold actGasHoleKOp actGasHoleActOp
  refine integral_congr_ae (Filter.Eventually.of_forall fun Φ => ?_)
  refine Finset.sum_congr rfl fun C hC => ?_
  congr 1
  refine Finset.prod_congr rfl fun t ht => ?_
  have hsub := sub_of_mem_Cfam hC ht
  rcases t with y | z
  · simp only [gasCs_inl] at hsub
    rw [gasW_inl, gasW_inl, hβ y hsub]
  · simp only [gasCs_inr] at hsub
    rw [gasW_inr, gasW_inr, hτ z hsub]

/-- **Locality of the local terms with a hole**: `P(Y)` depends only on the weights of the
elementary objects whose charged supports lie in `Y`. -/
theorem PY_actGasHoleKOp_congr {β β' : Yt → (∀ b, Ω b) → ℂ} {τ τ' : Zt → (∀ b, Ω b) → ℂ}
    (Y : Finset B) (hβ : ∀ y, cy y ⊆ Y → β y = β' y) (hτ : ∀ z, zs z ⊆ Y → τ z = τ' z) :
    PY (shareBlock (holeSupp H S₀)) (holeSupp H S₀)
        (actGasHoleKOp H S₀ cyF zsF act cy zs β τ μ) Y =
      PY (shareBlock (holeSupp H S₀)) (holeSupp H S₀)
        (actGasHoleKOp H S₀ cyF zsF act cy zs β' τ' μ) Y :=
  PY_congr _ _ Y fun X hX =>
    actGasHoleKOp_congr X (fun y hy => hβ y (hy.trans hX)) (fun z hz => hτ z (hz.trans hX))

end Local

section Analytic

variable {B Yt Zt : Type*} [Fintype B] [Fintype Yt] [Fintype Zt]
  {Ω : B → Type*} [∀ b, MeasurableSpace (Ω b)]
  {act : Yt → Finset Zt → Prop} {cy : Yt → Finset B} {zs : Zt → Finset B}
  {μ : ∀ b, Measure (Ω b)} [∀ b, IsProbabilityMeasure (μ b)]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  {β : Yt → E → (∀ b, Ω b) → ℂ} {τ : Zt → E → (∀ b, Ω b) → ℂ} {U : Set E}

omit [Fintype B] [Fintype Yt] [Fintype Zt] [(b : B) → MeasurableSpace (Ω b)]
  [FiniteDimensional ℂ E] [∀ b, IsProbabilityMeasure (μ b)] in
/-- The product of the weights of a family is analytic in the parameter. -/
theorem analyticOnNhd_prod_gasW (hβa : ∀ y Φ, AnalyticOnNhd ℂ (fun g => β y g Φ) U)
    (hτa : ∀ z Φ, AnalyticOnNhd ℂ (fun g => τ z g Φ) U) (C : Finset (Yt ⊕ Zt))
    (Φ : ∀ b, Ω b) :
    AnalyticOnNhd ℂ (fun g => ∏ t ∈ C, gasW (fun y => β y g Φ) (fun z => τ z g Φ) t) U := by
  refine Finset.analyticOnNhd_fun_prod _ fun t _ => ?_
  rcases t with y | z
  · exact ((hβa y Φ).cexp).sub analyticOnNhd_const
  · exact hτa z Φ

omit [Fintype B] [Fintype Yt] [Fintype Zt] [(b : B) → MeasurableSpace (Ω b)]
  [∀ b, IsProbabilityMeasure (μ b)] [NormedAddCommGroup E] [NormedSpace ℂ E]
  [FiniteDimensional ℂ E] in
/-- The dominating function of the product of the weights of an admissible family. -/
theorem norm_prod_gasW_le_dom {s : Yt → ℝ} {T : Zt → (∀ b, Ω b) → ℝ} (hs0 : ∀ y, 0 ≤ s y)
    (hB : ∀ g ∈ U, ∀ Γ : Finset Zt, (∀ z ∈ Γ, ∀ z' ∈ Γ, z ≠ z' → Disjoint (zs z) (zs z')) →
      ∀ y, act y Γ → ∀ Φ, (∀ z ∈ Γ, τ z g Φ ≠ 0) → ‖Complex.exp (β y g Φ) - 1‖ ≤ s y)
    (hT : ∀ g ∈ U, ∀ z Φ, ‖τ z g Φ‖ ≤ T z Φ) {C : Finset (Yt ⊕ Zt)} (hC : actGasA act zs C)
    {g : E} (hg : g ∈ U) (Φ : ∀ b, Ω b) :
    ‖∏ t ∈ C, gasW (fun y => β y g Φ) (fun z => τ z g Φ) t‖ ≤
      (∏ y ∈ C.toLeft, s y) * ∏ z ∈ C.toRight, T z Φ :=
  (norm_prod_gasW_le (β := fun y => β y g) (τ := fun z => τ z g) Φ
    (fun h y hy => hB g hg _ hC.1 y (hC.2 y hy) Φ h)).trans
    (mul_le_mul_of_nonneg_left (Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
      (fun z _ => hT g hg z Φ)) (Finset.prod_nonneg fun y _ => hs0 y))

omit [Fintype Yt] [Fintype Zt] [NormedAddCommGroup E] [NormedSpace ℂ E]
  [FiniteDimensional ℂ E] in
theorem integrable_prod_dom {T : Zt → (∀ b, Ω b) → ℝ}
    (hTd : ∀ z, DepOn (zs z) (fun Φ => (T z Φ : ℂ))) (hTm : ∀ z, Measurable (T z))
    (hTi : ∀ z, Integrable (T z) (Measure.pi μ)) {C : Finset (Yt ⊕ Zt)} (hC : actGasA act zs C)
    (c : ℝ) :
    Integrable (fun Φ => c * ∏ z ∈ C.toRight, T z Φ) (Measure.pi μ) := by
  have h := integrable_prod_depOn μ C.toRight zs (fun z Φ => (T z Φ : ℂ)) hC.1 (fun z _ => hTd z)
    (fun z => (hTm z).complex_ofReal) (fun z _ => (hTi z).ofReal)
  have h' : Integrable (fun Φ => ∏ z ∈ C.toRight, T z Φ) (Measure.pi μ) := by
    have := h.re
    simpa [← Complex.ofReal_prod] using this
  exact h'.const_mul c

/-- **The activities are analytic in the parameter.** -/
theorem analyticOnNhd_actGasKOp (hU : IsOpen U) {s : Yt → ℝ} {T : Zt → (∀ b, Ω b) → ℝ}
    (hβa : ∀ y Φ, AnalyticOnNhd ℂ (fun g => β y g Φ) U)
    (hτa : ∀ z Φ, AnalyticOnNhd ℂ (fun g => τ z g Φ) U)
    (hβm : ∀ g ∈ U, ∀ y, Measurable (β y g)) (hτm : ∀ g ∈ U, ∀ z, Measurable (τ z g))
    (hs0 : ∀ y, 0 ≤ s y)
    (hB : ∀ g ∈ U, ∀ Γ : Finset Zt, (∀ z ∈ Γ, ∀ z' ∈ Γ, z ≠ z' → Disjoint (zs z) (zs z')) →
      ∀ y, act y Γ → ∀ Φ, (∀ z ∈ Γ, τ z g Φ ≠ 0) → ‖Complex.exp (β y g Φ) - 1‖ ≤ s y)
    (hT : ∀ g ∈ U, ∀ z Φ, ‖τ z g Φ‖ ≤ T z Φ)
    (hTd : ∀ z, DepOn (zs z) (fun Φ => (T z Φ : ℂ))) (hTm : ∀ z, Measurable (T z))
    (hTi : ∀ z, Integrable (T z) (Measure.pi μ)) (X : NePoly B) :
    AnalyticOnNhd ℂ (fun g => actGasKOp act cy zs (fun y => β y g) (fun z => τ z g) μ X) U := by
  unfold actGasKOp actGasActOp actGasK polyAct
  refine Balaban.Analysis.analyticOnNhd_integral_of_dominated hU
    (fun Φ => Finset.analyticOnNhd_fun_sum _ fun C _ => analyticOnNhd_prod_gasW hβa hτa C Φ)
    (fun g hg => Finset.measurable_fun_sum _ fun C _ => Finset.measurable_fun_prod _ fun t _ =>
      measurable_gasW (hβm g hg) (hτm g hg) t)
    (integrable_finsetSum (Cfam (gasCs cy zs) (actGasA act zs) X.1) fun C hC =>
      integrable_prod_dom hTd hTm hTi (mem_Cfam.mp hC).2.1 (∏ y ∈ C.toLeft, s y))
    (fun g hg Φ => ?_)
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun C hC => ?_)
  exact norm_prod_gasW_le_dom hs0 hB hT (mem_Cfam.mp hC).2.1 hg Φ

/-- **The local terms are analytic in the parameter.**  If the hypotheses of `actGasOp_pe` hold at
every `g ∈ U` (with numerical data independent of `g`), the weights are analytic in `g` and the
heavy weights are dominated by integrable functions `T Z` with dependence sets `zs Z`, then
`g ↦ P_g(Y)` is analytic on `U` for every `Y`. -/
theorem analyticOnNhd_PY_actGas {d : Finset B → ℝ} {B0 κ'' c c1 c2 p h : ℝ}
    {κg K0g K0h κ' κ0P K0P cP : ℝ} (hU : IsOpen U) {T : Zt → (∀ b, Ω b) → ℝ}
    (hB0 : 0 ≤ B0) (hκg : 0 ≤ κg) (hκ'' : κg ≤ κ'') (hc : 0 ≤ c) (hc1 : 0 ≤ c1) (hp : 0 ≤ p)
    (hd : ∀ Y, 0 ≤ d Y) (hz : ∀ z, (zs z).Nonempty)
    (hmeet : ∀ y Γ, act y Γ → ∃ z ∈ Γ, ¬ Disjoint (cy y) (zs z))
    (hτd : ∀ g ∈ U, ∀ z, DepOn (zs z) (τ z g))
    (hβa : ∀ y Φ, AnalyticOnNhd ℂ (fun g => β y g Φ) U)
    (hτa : ∀ z Φ, AnalyticOnNhd ℂ (fun g => τ z g Φ) U)
    (hβm : ∀ g ∈ U, ∀ y, Measurable (β y g)) (hτm : ∀ g ∈ U, ∀ z, Measurable (τ z g))
    (hT : ∀ g ∈ U, ∀ z Φ, ‖τ z g Φ‖ ≤ T z Φ)
    (hTd : ∀ z, DepOn (zs z) (fun Φ => (T z Φ : ℂ))) (hTm : ∀ z, Measurable (T z))
    (hTi : ∀ z, Integrable (T z) (Measure.pi μ))
    (hB : ∀ g ∈ U, ∀ Γ : Finset Zt, (∀ z ∈ Γ, ∀ z' ∈ Γ, z ≠ z' → Disjoint (zs z) (zs z')) →
      ∀ y, act y Γ → ∀ Φ, (∀ z ∈ Γ, τ z g Φ ≠ 0) → ‖β y g Φ‖ ≤ B0 * Real.exp (-κ'' * d (cy y)))
    (hzd : ∀ z, d (zs z) ≤ c2 * (zs z).card)
    (hG3 : ∀ C : Finset (Yt ⊕ Zt), ConnSet (gasCs cy zs) C → actGasA act zs C →
      d (unionCs (gasCs cy zs) C) ≤ ∑ t ∈ C, d (gasCs cy zs t) + c * ((C.card : ℝ) - 1))
    (hK0g : 0 ≤ K0g)
    (hent : ∀ Γ : Finset Zt, (∀ z ∈ Γ, ∀ z' ∈ Γ, z ≠ z' → Disjoint (zs z) (zs z')) →
      ∀ b : B, ∑ y ∈ Finset.univ.filter (fun y => act y Γ ∧ b ∈ cy y),
        Real.exp (-(κ'' - κg) * d (cy y)) ≤ K0g)
    (hK1 : 1 ≤ K0h)
    (hcount : ∀ g ∈ U, ∀ (b : B) (v : ℕ),
      ∑ z ∈ Finset.univ.filter (fun z => b ∈ zs z ∧ (zs z).card = v),
        ∫ Φ, ‖τ z g Φ‖ ∂(Measure.pi μ) ≤ K0h ^ v * Real.exp (-p - h * v))
    (hh : B0 * Real.exp B0 * Real.exp (κg * c) * K0g + κg * (c2 + c) + c1 + 3 +
      Real.log K0h ≤ h)
    (hG1 : ∀ X : NePoly B, (X.1.card : ℝ) ≤ c1 * (1 + d X.1))
    (hκ' : 0 ≤ κ') (hcP : 0 ≤ cP)
    (hG2P : ∀ b : B, ∑ Y : NePoly B, (if b ∈ Y.1 then Real.exp (-κ0P * d Y.1) else 0) ≤ K0P)
    (hκ : κ' + κ0P + c1 ≤ κg - 2)
    (hα : 3 * c1 * Real.exp (-p) * K0P * Real.exp (c1 + κ' * cP) ≤ 1) (Y : Finset B) :
    AnalyticOnNhd ℂ (fun g => PY (shareBlock (Subtype.val : NePoly B → Finset B)) Subtype.val
      (actGasKOp act cy zs (fun y => β y g) (fun z => τ z g) μ) Y) U := by
  have hε : 0 ≤ 3 * c1 * Real.exp (-p) := by positivity
  have hτi : ∀ g ∈ U, ∀ z, Integrable (τ z g) (Measure.pi μ) := fun g hg z =>
    (hTi z).mono' (hτm g hg z).aestronglyMeasurable
      (Filter.Eventually.of_forall fun Φ => hT g hg z Φ)
  have hKP := kp_of_entropy (Subtype.val : NePoly B → Finset B)
    (sizeW (Subtype.val : NePoly B → Finset B) d (3 * c1 * Real.exp (-p)) (κg - 2) κ' cP)
    (sizeW_nonneg _ d hε)
    (size_entropy (Subtype.val : NePoly B → Finset B) d hε hd hG1 hG2P hκ hα)
  have hbound : ∀ (X : NePoly B) (g : E), g ∈ U →
      ‖actGasKOp act cy zs (fun y => β y g) (fun z => τ z g) μ X‖ ≤
        sizeW (Subtype.val : NePoly B → Finset B) d (3 * c1 * Real.exp (-p)) (κg - 2) κ' cP X := by
    intro X g hg
    refine (actGasKOp_activity_bound hB0 hκg hκ'' hc hc1 hp hd hz hmeet (hτd g hg) (hβm g hg)
      (hτm g hg) (hτi g hg) (hB g hg) hzd hG3 hK0g hent hK1 (hcount g hg) hh X (hG1 X)).trans ?_
    unfold sizeW
    calc 3 * c1 * Real.exp (-p) * Real.exp (-(κg - 2) * d X.1)
        = 3 * c1 * Real.exp (-p) * Real.exp (-(κg - 2) * d X.1) * 1 := by rw [mul_one]
      _ ≤ _ := mul_le_mul_of_nonneg_left (Real.one_le_exp (by
          have := hd X.1
          positivity)) (by positivity)
  exact pe_PY_analyticOnNhd (shareBlock (Subtype.val : NePoly B → Finset B))
    (Subtype.val : NePoly B → Finset B) hKP hU
    (fun X g => actGasKOp act cy zs (fun y => β y g) (fun z => τ z g) μ X)
    (fun X => analyticOnNhd_actGasKOp hU hβa hτa hβm hτm
      (s := fun y => B0 * Real.exp B0 * Real.exp (-κ'' * d (cy y)))
      (fun y => by positivity)
      (fun g hg Γ hΓ y hy Φ hΦ => norm_expm1_le (β := fun y => β y g Φ) hB0 (hκg.trans hκ'') hd y
        (hB g hg Γ hΓ y hy Φ hΦ)) hT hTd hTm hTi X)
    hbound Y

variable {H : SimpleGraph B} {S₀ : Finset B} {cyF : Yt → Finset B} {zsF : Zt → Finset B}

/-- **The activities of the hole polymers are analytic in the parameter.** -/
theorem analyticOnNhd_actGasHoleKOp (hU : IsOpen U) {s : Yt → ℝ} {T : Zt → (∀ b, Ω b) → ℝ}
    (hβa : ∀ y Φ, AnalyticOnNhd ℂ (fun g => β y g Φ) U)
    (hτa : ∀ z Φ, AnalyticOnNhd ℂ (fun g => τ z g Φ) U)
    (hβm : ∀ g ∈ U, ∀ y, Measurable (β y g)) (hτm : ∀ g ∈ U, ∀ z, Measurable (τ z g))
    (hs0 : ∀ y, 0 ≤ s y)
    (hB : ∀ g ∈ U, ∀ Γ : Finset Zt, (∀ z ∈ Γ, ∀ z' ∈ Γ, z ≠ z' → Disjoint (zs z) (zs z')) →
      ∀ y, act y Γ → ∀ Φ, (∀ z ∈ Γ, τ z g Φ ≠ 0) → ‖Complex.exp (β y g Φ) - 1‖ ≤ s y)
    (hT : ∀ g ∈ U, ∀ z Φ, ‖τ z g Φ‖ ≤ T z Φ)
    (hTd : ∀ z, DepOn (zs z) (fun Φ => (T z Φ : ℂ))) (hTm : ∀ z, Measurable (T z))
    (hTi : ∀ z, Integrable (T z) (Measure.pi μ)) (X : HolePolymer H S₀) :
    AnalyticOnNhd ℂ (fun g => actGasHoleKOp H S₀ cyF zsF act cy zs (fun y => β y g)
      (fun z => τ z g) μ X) U := by
  unfold actGasHoleKOp actGasHoleActOp
  refine Balaban.Analysis.analyticOnNhd_integral_of_dominated hU
    (fun Φ => Finset.analyticOnNhd_fun_sum _ fun C _ => ?_)
    (fun g hg => Finset.measurable_fun_sum _ fun C _ => ?_)
    (integrable_finsetSum (Cfam (gasCs cy zs) (actGasA act zs) (holeSupp H S₀ X)) fun C hC =>
      integrable_prod_dom hTd hTm hTi (mem_Cfam.mp hC).2.1 (∏ y ∈ C.toLeft, s y))
    (fun g hg Φ => ?_)
  · by_cases hc : unionCs (gasCs cyF zsF) C = X.1
    · simp only [hc, ite_true]
      exact analyticOnNhd_prod_gasW hβa hτa C Φ
    · simp only [hc, ite_false]
      exact analyticOnNhd_const
  · by_cases hc : unionCs (gasCs cyF zsF) C = X.1
    · simp only [hc, ite_true]
      exact Finset.measurable_fun_prod _ fun t _ => measurable_gasW (hβm g hg) (hτm g hg) t
    · simp only [hc, ite_false]
      exact measurable_const
  · refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun C hC => ?_)
    have hdom := norm_prod_gasW_le_dom hs0 hB hT (mem_Cfam.mp hC).2.1 hg Φ
    by_cases hc : unionCs (gasCs cyF zsF) C = X.1
    · simpa only [hc, ite_true] using hdom
    · simp only [hc, ite_false, norm_zero]
      exact (norm_nonneg _).trans hdom

/-- **The local terms with a hole are analytic in the parameter.**  If the hypotheses of
`actGasOp_pe_hole` hold at every `g ∈ U` (with numerical data independent of `g`), the weights are
analytic in `g` and the heavy weights are dominated by integrable functions `T Z` with dependence
sets `zs Z`, then `g ↦ P_g(Y)` is analytic on `U` for every `Y`. -/
theorem analyticOnNhd_PY_actGasHole {Δ : ℕ} (hdeg : ∀ v, H.degree v ≤ Δ) {B0 κ'' c c2 p h : ℝ}
    {κg κp α : ℝ} (hU : IsOpen U) {T : Zt → (∀ b, Ω b) → ℝ}
    (hB0 : 0 ≤ B0) (hκg : 0 ≤ κg) (hκ'' : κg ≤ κ'') (hc : 0 ≤ c) (hp : 0 ≤ p) (hκp : 0 ≤ κp)
    (hz : ∀ z, (zs z).Nonempty)
    (hmeet : ∀ y Γ, act y Γ → ∃ z ∈ Γ, ¬ Disjoint (cy y) (zs z))
    (hτd : ∀ g ∈ U, ∀ z, DepOn (zs z) (τ z g))
    (hβa : ∀ y Φ, AnalyticOnNhd ℂ (fun g => β y g Φ) U)
    (hτa : ∀ z Φ, AnalyticOnNhd ℂ (fun g => τ z g Φ) U)
    (hβm : ∀ g ∈ U, ∀ y, Measurable (β y g)) (hτm : ∀ g ∈ U, ∀ z, Measurable (τ z g))
    (hT : ∀ g ∈ U, ∀ z Φ, ‖τ z g Φ‖ ≤ T z Φ)
    (hTd : ∀ z, DepOn (zs z) (fun Φ => (T z Φ : ℂ))) (hTm : ∀ z, Measurable (T z))
    (hTi : ∀ z, Integrable (T z) (Measure.pi μ))
    (hB : ∀ g ∈ U, ∀ Γ : Finset Zt, (∀ z ∈ Γ, ∀ z' ∈ Γ, z ≠ z' → Disjoint (zs z) (zs z')) →
      ∀ y, act y Γ → ∀ Φ, (∀ z ∈ Γ, τ z g Φ ≠ 0) →
        ‖β y g Φ‖ ≤ B0 * Real.exp (-κ'' * (steiner H (cy y) : ℝ)))
    (hzd : ∀ z, (steiner H (zs z) : ℝ) ≤ c2 * (zs z).card)
    (hG3 : ∀ C : Finset (Yt ⊕ Zt), ConnSet (gasCs cy zs) C → actGasA act zs C →
      (steiner H (unionCs (gasCs cy zs) C) : ℝ) ≤
        ∑ t ∈ C, (steiner H (gasCs cy zs t) : ℝ) + c * ((C.card : ℝ) - 1))
    {K0g K0h : ℝ} (hK0g : 0 ≤ K0g)
    (hent : ∀ Γ : Finset Zt, (∀ z ∈ Γ, ∀ z' ∈ Γ, z ≠ z' → Disjoint (zs z) (zs z')) →
      ∀ b : B, ∑ y ∈ Finset.univ.filter (fun y => act y Γ ∧ b ∈ cy y),
        Real.exp (-(κ'' - κg) * (steiner H (cy y) : ℝ)) ≤ K0g)
    (hK1 : 1 ≤ K0h)
    (hcount : ∀ g ∈ U, ∀ (b : B) (v : ℕ),
      ∑ z ∈ Finset.univ.filter (fun z => b ∈ zs z ∧ (zs z).card = v),
        ∫ Φ, ‖τ z g Φ‖ ∂(Measure.pi μ) ≤ K0h ^ v * Real.exp (-p - h * v))
    (hh : B0 * Real.exp B0 * Real.exp (κg * c) * K0g + κg * (c2 + c) + 1 + 3 + Real.log K0h ≤ h)
    (hq : (Δ : ℝ) ^ 2 * 2 ^ (Δ + 1) * Real.exp (-((κg - 2) - κp - α)) < 1)
    (hcond : 3 * Real.exp (-p) * 2 ^ (Δ + 1) * Real.exp (-((κg - 2) - κp - α)) /
      (1 - (Δ : ℝ) ^ 2 * 2 ^ (Δ + 1) * Real.exp (-((κg - 2) - κp - α))) ≤ α)
    (Y : Finset B) :
    AnalyticOnNhd ℂ (fun g => PY (shareBlock (holeSupp H S₀)) (holeSupp H S₀)
      (actGasHoleKOp H S₀ cyF zsF act cy zs (fun y => β y g) (fun z => τ z g) μ) Y) U := by
  have hd : ∀ Y : Finset B, 0 ≤ (steiner H Y : ℝ) := fun Y => Nat.cast_nonneg _
  have hε : 0 ≤ 3 * Real.exp (-p) := by positivity
  have hα : 0 ≤ α := by
    refine le_trans ?_ hcond
    have : 0 < 1 - (Δ : ℝ) ^ 2 * 2 ^ (Δ + 1) * Real.exp (-((κg - 2) - κp - α)) := by linarith
    positivity
  have hτi : ∀ g ∈ U, ∀ z, Integrable (τ z g) (Measure.pi μ) := fun g hg z =>
    (hTi z).mono' (hτm g hg z).aestronglyMeasurable
      (Filter.Eventually.of_forall fun Φ => hT g hg z Φ)
  have hKP := sized_kp (holeSupp H S₀) (fun X => (steiner H (holeSupp H S₀ X) : ℝ))
    (fun Y => κp * (steiner H Y : ℝ)) hε hα
    (fun X => by exact_mod_cast card_le_steiner (exists_animal_of_holePolymer X))
    (fun X => le_rfl) (entropy_hole (S₀ := S₀) hdeg hε hq hcond)
  have hbound : ∀ (X : HolePolymer H S₀) (g : E), g ∈ U →
      ‖actGasHoleKOp H S₀ cyF zsF act cy zs (fun y => β y g) (fun z => τ z g) μ X‖ ≤
        sizedW (holeSupp H S₀) (fun X => (steiner H (holeSupp H S₀ X) : ℝ))
          (fun Y => κp * (steiner H Y : ℝ)) (3 * Real.exp (-p)) (κg - 2) X := by
    intro X g hg
    have h1 := norm_actGasHoleKOp_le (cyF := cyF) (zsF := zsF)
      (d := fun Y : Finset B => (steiner H Y : ℝ)) (c1 := 1) hB0 hκg hκ'' hc zero_le_one hp hd hz
      hmeet (hτd g hg) (hβm g hg) (hτm g hg) (hτi g hg) (hB g hg) hzd hG3 hK0g hent hK1
      (hcount g hg) hh X (by
        have h1 := card_le_steiner (exists_animal_of_holePolymer X)
        have h2 : ((holeSupp H S₀ X).card : ℝ) ≤ (steiner H (holeSupp H S₀ X) : ℝ) := by
          exact_mod_cast h1
        simp only [one_mul]
        linarith)
    refine h1.trans ?_
    unfold sizedW
    rw [mul_one]
    calc 3 * Real.exp (-p) * Real.exp (-(κg - 2) * (steiner H (holeSupp H S₀ X) : ℝ))
        = 3 * Real.exp (-p) * Real.exp (-(κg - 2) * (steiner H (holeSupp H S₀ X) : ℝ)) * 1 := by
          rw [mul_one]
      _ ≤ _ := mul_le_mul_of_nonneg_left (Real.one_le_exp (by
          have := hd (holeSupp H S₀ X)
          simp only [add_zero]
          positivity)) (by positivity)
  exact pe_PY_analyticOnNhd (shareBlock (holeSupp H S₀)) (holeSupp H S₀) hKP hU
    (fun X g => actGasHoleKOp H S₀ cyF zsF act cy zs (fun y => β y g) (fun z => τ z g) μ X)
    (fun X => analyticOnNhd_actGasHoleKOp hU hβa hτa hβm hτm
      (s := fun y => B0 * Real.exp B0 * Real.exp (-κ'' * (steiner H (cy y) : ℝ)))
      (fun y => by positivity)
      (fun g hg Γ hΓ y hy Φ hΦ => norm_expm1_le (β := fun y => β y g Φ) hB0 (hκg.trans hκ'') hd y
        (hB g hg Γ hΓ y hy Φ hΦ)) hT hTd hTm hTi X)
    hbound Y

end Analytic

end Balaban.Polymer
