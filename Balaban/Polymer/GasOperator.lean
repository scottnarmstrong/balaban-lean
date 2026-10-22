module

public import Balaban.Polymer.GasOpBound
public import Balaban.Polymer.MayerAnalytic
public import Balaban.Polymer.MayerPE

/-!
# GAS for weights that are integrands on disjoint sets of variables

POLYMER.md §2.6 (GAS) with *operator-valued* weights (`notes/phase1/LF-RECONSTRUCTION.md`
§III.10, Lemma III.10.5, Lean item P10).  Fix the external variables; then an integral operator
acting on the internal variables of a heavy object `Z` is the function `τ Z` of the internal
configuration `Φ ∈ ∏_b Ω_b` obtained by integrating its kernel against the other factors: it
depends on `Φ` only through the blocks `zs Z`.  Likewise a coupling is a function `β Y` of `Φ`
depending only on the blocks `cy Y`.  The reference measure is a product `⨂_b μ_b` of probability
measures (a Gaussian reference measure is of this form).

The structure used is the commutative algebra of bounded measurable functions of `Φ`, together with
the expectation `E = ∫ · d⨂μ_b`, which is **multiplicative on functions with disjoint dependence
sets** (`integral_prod_depOn`).  The operator norm of (3.10″) of a heavy weight is
`E |τ Z|`, and that of a coupling is `sup_Φ |β Y Φ|`.

* `gasOp_eq`: the partition function `E Ξ(Φ)` is the partition function of the polymer gas whose
  activities are the expectations `E K(X)(Φ)` (pointwise in `Φ` this is the scalar `gas_eq`).
* `gasOp_activity_bound`: the activity bound of `gas_activity_bound` holds for these activities
  (reduction to the scalar bound for the weights `e^{-p-h|Z|}`, `B₀ e^{-κ'' d(Y)}`).
* `gasOp_pe`: the combination with `pe_size`, as `gas_pe`.

These are the instances, for the activation rule `coreAct` of `Gas.lean`, of the statements of
`GasOpEq.lean` and `GasOpBound.lean` (`actGasXiOp_eq`, `norm_integral_prod_gasW_le`,
`actGasKOp_activity_bound`, `actGasOp_pe`), which allow integrable heavy weights, couplings bounded
on the support of the heavy weights activating them, general activation rules and weighted counts.
-/

@[expose] public section

noncomputable section

open scoped Classical

open Finset MeasureTheory

namespace Balaban.Polymer

section Operator

variable {B Yt Zt : Type*} [Fintype B] [Fintype Yt] [Fintype Zt]
  {Ω : B → Type*} [∀ b, MeasurableSpace (Ω b)]
  (cy : Yt → Finset B) (zs cr : Zt → Finset B)
  (β : Yt → (∀ b, Ω b) → ℂ) (τ : Zt → (∀ b, Ω b) → ℂ)

/-- The activity integrand of the polymer `X` at the configuration `Φ`. -/
def gasActOp (X : NePoly B) (Φ : ∀ b, Ω b) : ℂ := actGasActOp (coreAct cy cr) cy zs β τ X Φ

variable (μ : ∀ b, Measure (Ω b))

/-- The activity of the polymer `X`: the expectation of the activity integrand. -/
def gasKOp (X : NePoly B) : ℂ := actGasKOp (coreAct cy cr) cy zs β τ μ X

/-- The partition function of GAS with weights that are functions of the configuration:
the expectation of the pointwise partition function (`gasXiOp_eq_integral`). -/
def gasXiOp : ℂ := actGasXiOp (coreAct cy cr) zs β τ μ

variable {cy zs cr β τ μ}

theorem gasXiOp_eq_integral :
    gasXiOp cy zs cr β τ μ =
      ∫ Φ, gasXi cy zs cr (fun y => β y Φ) (fun z => τ z Φ) ∂(Measure.pi μ) := by
  unfold gasXiOp actGasXiOp
  simp_rw [gasXi_eq_actGasXi]

omit [Fintype B] [Fintype Yt] [Fintype Zt] [(b : B) → MeasurableSpace (Ω b)] in
theorem bdd_gasW (hβ : ∀ y, Bdd (β y)) (hτ : ∀ z, Bdd (τ z)) (t : Yt ⊕ Zt) :
    Bdd (fun Φ : ∀ b, Ω b => gasW (fun y => β y Φ) (fun z => τ z Φ) t) := by
  rcases t with y | z
  · exact bdd_expm1 (H := β) (t := y) (hβ y)
  · exact hτ z

omit [Fintype B] in
theorem measurable_gasActOp (hβ : ∀ y, Measurable (β y)) (hτ : ∀ z, Measurable (τ z))
    (X : NePoly B) : Measurable (gasActOp cy zs cr β τ X) :=
  measurable_actGasActOp hβ hτ X

omit [Fintype B] [(b : B) → MeasurableSpace (Ω b)] in
theorem bdd_gasActOp (hβ : ∀ y, Bdd (β y)) (hτ : ∀ z, Bdd (τ z)) (X : NePoly B) :
    Bdd (gasActOp cy zs cr β τ X) := by
  unfold gasActOp actGasActOp actGasK polyAct
  exact Bdd.sum _ (fun C _ => Bdd.prod _ (fun t _ => bdd_gasW hβ hτ t))

omit [Fintype B] [(b : B) → MeasurableSpace (Ω b)] in
theorem depOn_gasActOp (hβ : ∀ y, DepOn (cy y) (β y)) (hτ : ∀ z, DepOn (zs z) (τ z))
    (X : NePoly B) : DepOn X.1 (gasActOp cy zs cr β τ X) :=
  depOn_actGasActOp hβ hτ X

theorem norm_expm1_le_exp (w : ℂ) {b : ℝ} (hw : ‖w‖ ≤ b) :
    ‖Complex.exp w - 1‖ ≤ Real.exp b - 1 := by
  have h1 := Complex.norm_exp_sub_sum_le_exp_norm_sub_sum w 1
  simp only [Finset.range_one, Finset.sum_singleton, pow_zero, Nat.factorial_zero, Nat.cast_one,
    div_one] at h1
  have := Real.exp_le_exp.mpr hw
  linarith

variable [∀ b, IsProbabilityMeasure (μ b)]

/-- **GAS for functions of the configuration (identity)**: the expectation of the partition
function with non-small boundary terms is the partition function of the polymer gas of connected
clusters, with the expected activities. -/
theorem gasOp_eq (hz : ∀ z, (zs z).Nonempty) (hcr : ∀ z, cr z ⊆ zs z)
    (hβd : ∀ y, DepOn (cy y) (β y)) (hτd : ∀ z, DepOn (zs z) (τ z))
    (hβm : ∀ y, Measurable (β y)) (hτm : ∀ z, Measurable (τ z))
    (hβb : ∀ y, Bdd (β y)) (hτb : ∀ z, Bdd (τ z)) :
    gasXiOp cy zs cr β τ μ =
      Xi (shareBlock (Subtype.val : NePoly B → Finset B)) (gasKOp cy zs cr β τ μ) := by
  have hβb' : ∀ y, ∃ M : ℝ, ∀ Φ, ‖β y Φ‖ ≤ M := hβb
  choose M hM using hβb'
  exact actGasXiOp_eq (s := fun y => Real.exp (M y) - 1) hz
    (coreAct_local (fun _ => Finset.Subset.rfl) hcr) (coreAct_meets (fun _ => Finset.Subset.rfl) hcr)
    hβd hτd hβm hτm (fun z => integrable_of_bdd μ (hτm z) (hτb z))
    (fun _ _ y _ Φ _ => norm_expm1_le_exp _ (hM y Φ))

section Bound

variable (cy) in
/-- The scalar coupling weight dominating the sup bound `B₀ e^{-κ'' d(Y)}`. -/
def gasBetaBound (B0 κ'' : ℝ) (d : Finset B → ℝ) : Yt → ℂ :=
  fun y => ((B0 * Real.exp (-κ'' * d (cy y)) : ℝ) : ℂ)

variable (zs) in
/-- The scalar heavy weight dominating the integral bound `e^{-p-h|Z|}`. -/
def gasTauBound (p h : ℝ) : Zt → ℂ :=
  fun z => ((Real.exp (-p - h * (zs z).card) : ℝ) : ℂ)

variable {d : Finset B → ℝ} {B0 κ' κ'' c c1 c2 p h : ℝ}

omit [Fintype B] in
theorem gasK_bound_eq (X : NePoly B) :
    gasK cy zs cr (gasBetaBound cy B0 κ'' d) (gasTauBound zs p h) X =
      ((∑ C ∈ Cfam (gasCs cy zs) (gasA cy zs cr) X.1,
        ((∏ y ∈ C.toLeft, (Real.exp (B0 * Real.exp (-κ'' * d (cy y))) - 1)) *
          ∏ z ∈ C.toRight, Real.exp (-p - h * (zs z).card)) : ℝ) : ℂ) := by
  unfold gasK polyAct
  push_cast
  refine Finset.sum_congr rfl (fun C _ => ?_)
  rw [prod_gasW]
  simp [gasBetaBound, gasTauBound, Complex.ofReal_exp]

omit [Fintype B] in
theorem norm_gasK_bound (hB0 : 0 ≤ B0) (X : NePoly B) :
    ‖gasK cy zs cr (gasBetaBound cy B0 κ'' d) (gasTauBound zs p h) X‖ =
      ∑ C ∈ Cfam (gasCs cy zs) (gasA cy zs cr) X.1,
        ((∏ y ∈ C.toLeft, (Real.exp (B0 * Real.exp (-κ'' * d (cy y))) - 1)) *
          ∏ z ∈ C.toRight, Real.exp (-p - h * (zs z).card)) := by
  rw [gasK_bound_eq, Complex.norm_real, Real.norm_eq_abs]
  refine abs_of_nonneg (Finset.sum_nonneg (fun C _ => mul_nonneg
    (Finset.prod_nonneg (fun y _ => ?_)) (Finset.prod_nonneg (fun z _ => (Real.exp_pos _).le))))
  simp only [sub_nonneg]; exact Real.one_le_exp (by positivity)

/-- The expectation of the product over a connected admissible family is bounded by the product
of the scalar bounds: the sup norms of the couplings and the integral norms of the heavy weights
(which act on pairwise disjoint sets of blocks). -/
theorem norm_integral_family_le (hB0 : 0 ≤ B0)
    (hβm : ∀ y, Measurable (β y)) (hτm : ∀ z, Measurable (τ z))
    (hτd : ∀ z, DepOn (zs z) (τ z)) (hτb : ∀ z, Bdd (τ z))
    (hB : ∀ y Φ, ‖β y Φ‖ ≤ B0 * Real.exp (-κ'' * d (cy y)))
    (hτ : ∀ z, ∫ Φ, ‖τ z Φ‖ ∂(Measure.pi μ) ≤ Real.exp (-p - h * (zs z).card))
    {X : Finset B} {C : Finset (Yt ⊕ Zt)}
    (hC : C ∈ Cfam (gasCs cy zs) (gasA cy zs cr) X) :
    ‖∫ Φ, ∏ t ∈ C, gasW (fun y => β y Φ) (fun z => τ z Φ) t ∂(Measure.pi μ)‖ ≤
      (∏ y ∈ C.toLeft, (Real.exp (B0 * Real.exp (-κ'' * d (cy y))) - 1)) *
        ∏ z ∈ C.toRight, Real.exp (-p - h * (zs z).card) := by
  refine (norm_integral_prod_gasW_le (act := coreAct cy cr) hτd hβm hτm
    (fun z => integrable_of_bdd μ (hτm z) (hτb z))
    (fun _ _ y _ Φ _ => norm_expm1_le_exp _ (hB y Φ)) (mem_Cfam.mp hC).2.1).trans ?_
  refine mul_le_mul_of_nonneg_left (Finset.prod_le_prod₀
    (fun z _ => integral_nonneg (fun _ => norm_nonneg _)) (fun z _ => hτ z))
    (Finset.prod_nonneg (fun y _ => ?_))
  simp only [sub_nonneg]
  exact Real.one_le_exp (by positivity)

/-- The scalar GAS bound for the dominating weights `B₀ e^{-κ'' d(Y)}` and `e^{-p-h|Z|}`: the
scalar input of `gasOp_activity_bound`. -/
theorem gasBound_norm_le (hB0 : 0 ≤ B0) (hκ' : 0 ≤ κ') (hκ'' : κ' ≤ κ'') (hc : 0 ≤ c)
    (hc1 : 0 ≤ c1) (hp : 0 ≤ p) (hd : ∀ Y, 0 ≤ d Y) (hz : ∀ z, (zs z).Nonempty)
    (hcr : ∀ z, cr z ⊆ zs z)
    (hzd : ∀ z, d (zs z) ≤ c2 * (zs z).card)
    (hG3 : ∀ C : Finset (Yt ⊕ Zt), ConnSet (gasCs cy zs) C → gasA cy zs cr C →
      d (unionCs (gasCs cy zs) C) ≤ ∑ t ∈ C, d (gasCs cy zs t) + c * ((C.card : ℝ) - 1))
    {K0' K0'' : ℝ} (hK0' : 0 ≤ K0')
    (hent : ∀ b : B, ∑ y ∈ Finset.univ.filter (fun y => b ∈ cy y),
      Real.exp (-(κ'' - κ') * d (cy y)) ≤ K0')
    (hK1 : 1 ≤ K0'')
    (hcount : ∀ (b : B) (v : ℕ),
      ((Finset.univ.filter (fun z => b ∈ zs z ∧ (zs z).card = v)).card : ℝ) ≤ K0'' ^ v)
    (hh : B0 * Real.exp B0 * Real.exp (κ' * c) * K0' + κ' * (c2 + c) + c1 + 3 + Real.log K0'' ≤ h)
    (X : NePoly B) (hG1 : (X.1.card : ℝ) ≤ c1 * (1 + d X.1)) :
    ‖gasK cy zs cr (gasBetaBound cy B0 κ'' d) (gasTauBound zs p h) X‖ ≤
      3 * c1 * Real.exp (-p) * Real.exp (-(κ' - 2) * d X.1) :=
  gas_activity_bound (β := gasBetaBound cy B0 κ'' d) (τ := gasTauBound zs p h)
    hB0 hκ' hκ'' hc hc1 hp hd hz hcr
    (fun y => by
      simp only [gasBetaBound, Complex.norm_real, Real.norm_eq_abs]
      exact le_of_eq (abs_of_nonneg (by positivity)))
    (fun z => by
      simp only [gasTauBound, Complex.norm_real, Real.norm_eq_abs]
      exact le_of_eq (abs_of_pos (Real.exp_pos _)))
    hzd hG3 hK0' hent hK1 hcount hh X hG1


omit [Fintype Yt] [Fintype Zt] in
theorem integrable_prod_gasW (hβm : ∀ y, Measurable (β y)) (hτm : ∀ z, Measurable (τ z))
    (hβb : ∀ y, Bdd (β y)) (hτb : ∀ z, Bdd (τ z)) (C : Finset (Yt ⊕ Zt)) :
    Integrable (fun Φ : ∀ b, Ω b => ∏ t ∈ C, gasW (fun y => β y Φ) (fun z => τ z Φ) t)
      (Measure.pi μ) := by
  obtain ⟨M, hM⟩ := (Bdd.prod C (fun t _ => bdd_gasW hβb hτb t) :
    Bdd (fun Φ : ∀ b, Ω b => ∏ t ∈ C, gasW (fun y => β y Φ) (fun z => τ z Φ) t))
  exact Integrable.of_bound (Finset.measurable_prod _
    (fun t _ => measurable_gasW hβm hτm t)).aestronglyMeasurable M (Filter.Eventually.of_forall hM)

/-- **GAS (activity bound) for functions of the configuration.**  If the couplings are bounded
in sup norm by `B₀ e^{-κ'' d(Y)}` and the heavy weights in integral norm by `e^{-p-h|Z|}` (the
operator norms of (3.10″)), then the expected activities satisfy the bound of `gas_activity_bound`:
`‖K(X)‖ ≤ 3 c₁ e^{-p} e^{-(κ'-2) d(X)}` for `|X| ≤ c₁ (1 + d(X))`. -/
theorem gasOp_activity_bound (hB0 : 0 ≤ B0) (hκ' : 0 ≤ κ') (hκ'' : κ' ≤ κ'') (hc : 0 ≤ c)
    (hc1 : 0 ≤ c1) (hp : 0 ≤ p) (hd : ∀ Y, 0 ≤ d Y) (hz : ∀ z, (zs z).Nonempty)
    (hcr : ∀ z, cr z ⊆ zs z)
    (hτd : ∀ z, DepOn (zs z) (τ z))
    (hβm : ∀ y, Measurable (β y)) (hτm : ∀ z, Measurable (τ z))
    (hτb : ∀ z, Bdd (τ z))
    (hB : ∀ y Φ, ‖β y Φ‖ ≤ B0 * Real.exp (-κ'' * d (cy y)))
    (hτ : ∀ z, ∫ Φ, ‖τ z Φ‖ ∂(Measure.pi μ) ≤ Real.exp (-p - h * (zs z).card))
    (hzd : ∀ z, d (zs z) ≤ c2 * (zs z).card)
    (hG3 : ∀ C : Finset (Yt ⊕ Zt), ConnSet (gasCs cy zs) C → gasA cy zs cr C →
      d (unionCs (gasCs cy zs) C) ≤ ∑ t ∈ C, d (gasCs cy zs t) + c * ((C.card : ℝ) - 1))
    {K0' K0'' : ℝ} (hK0' : 0 ≤ K0')
    (hent : ∀ b : B, ∑ y ∈ Finset.univ.filter (fun y => b ∈ cy y),
      Real.exp (-(κ'' - κ') * d (cy y)) ≤ K0')
    (hK1 : 1 ≤ K0'')
    (hcount : ∀ (b : B) (v : ℕ),
      ((Finset.univ.filter (fun z => b ∈ zs z ∧ (zs z).card = v)).card : ℝ) ≤ K0'' ^ v)
    (hh : B0 * Real.exp B0 * Real.exp (κ' * c) * K0' + κ' * (c2 + c) + c1 + 3 + Real.log K0'' ≤ h)
    (X : NePoly B) (hG1 : (X.1.card : ℝ) ≤ c1 * (1 + d X.1)) :
    ‖gasKOp cy zs cr β τ μ X‖ ≤ 3 * c1 * Real.exp (-p) * Real.exp (-(κ' - 2) * d X.1) :=
  actGasKOp_activity_bound hB0 hκ' hκ'' hc hc1 hp hd hz
    (coreAct_meets (fun _ => Finset.Subset.rfl) hcr) hτd hβm hτm
    (fun z => integrable_of_bdd μ (hτm z) (hτb z)) (fun _ _ y _ Φ _ => hB y Φ) hzd hG3 hK0'
    (fun Γ _ b => sum_filter_act_le (fun _ => (Real.exp_pos _).le) hent Γ b) hK1
    (sum_filter_le_of_count hτ hcount) hh X hG1

/-- **GAS + PE-L for functions of the configuration**: the expectation of the partition function
is `exp(L)` for an absolutely convergent cluster sum, with local terms decaying at the rate
`κg - 2` (the operator-valued version of `gas_pe`). -/
theorem gasOp_pe {κg K0g K0h κ0P K0P cP : ℝ}
    (hB0 : 0 ≤ B0) (hκg : 0 ≤ κg) (hκ'' : κg ≤ κ'') (hc : 0 ≤ c)
    (hc1 : 0 ≤ c1) (hp : 0 ≤ p) (hd : ∀ Y, 0 ≤ d Y) (hz : ∀ z, (zs z).Nonempty)
    (hcr : ∀ z, cr z ⊆ zs z)
    (hβd : ∀ y, DepOn (cy y) (β y)) (hτd : ∀ z, DepOn (zs z) (τ z))
    (hβm : ∀ y, Measurable (β y)) (hτm : ∀ z, Measurable (τ z))
    (hτb : ∀ z, Bdd (τ z))
    (hB : ∀ y Φ, ‖β y Φ‖ ≤ B0 * Real.exp (-κ'' * d (cy y)))
    (hτ : ∀ z, ∫ Φ, ‖τ z Φ‖ ∂(Measure.pi μ) ≤ Real.exp (-p - h * (zs z).card))
    (hzd : ∀ z, d (zs z) ≤ c2 * (zs z).card)
    (hG3 : ∀ C : Finset (Yt ⊕ Zt), ConnSet (gasCs cy zs) C → gasA cy zs cr C →
      d (unionCs (gasCs cy zs) C) ≤ ∑ t ∈ C, d (gasCs cy zs t) + c * ((C.card : ℝ) - 1))
    (hK0g : 0 ≤ K0g)
    (hent : ∀ b : B, ∑ y ∈ Finset.univ.filter (fun y => b ∈ cy y),
      Real.exp (-(κ'' - κg) * d (cy y)) ≤ K0g)
    (hK1 : 1 ≤ K0h)
    (hcount : ∀ (b : B) (v : ℕ),
      ((Finset.univ.filter (fun z => b ∈ zs z ∧ (zs z).card = v)).card : ℝ) ≤ K0h ^ v)
    (hh : B0 * Real.exp B0 * Real.exp (κg * c) * K0g + κg * (c2 + c) + c1 + 3 +
      Real.log K0h ≤ h)
    (hG1 : ∀ X : NePoly B, (X.1.card : ℝ) ≤ c1 * (1 + d X.1))
    (hK0P : 0 ≤ K0P) (hκ' : 0 ≤ κ') (hcP : 0 ≤ cP)
    (hG2P : ∀ b : B, ∑ Y : NePoly B, (if b ∈ Y.1 then Real.exp (-κ0P * d Y.1) else 0) ≤ K0P)
    (hG3P : ∀ (n : ℕ) (X : Fin (n + 1) → NePoly B),
      (clusterGraph (shareBlock (Subtype.val : NePoly B → Finset B)) X).Connected →
        d (unionOf (Subtype.val : NePoly B → Finset B) X) ≤ ∑ i, d (X i).1 + cP * n)
    (hκ : κ' + κ0P + c1 ≤ κg - 2)
    (hα : 3 * c1 * Real.exp (-p) * K0P * Real.exp (c1 + κ' * cP) ≤ 1) :
    gasXiOp cy zs cr β τ μ = Complex.exp (logSeries (shareBlock (Subtype.val : NePoly B → Finset B))
      (gasKOp cy zs cr β τ μ)) ∧
    (∀ b : B, ∑ Y ∈ (Finset.univ : Finset (Finset B)).filter (fun Y => b ∈ Y),
        ‖PY (shareBlock (Subtype.val : NePoly B → Finset B)) Subtype.val
          (gasKOp cy zs cr β τ μ) Y‖ * Real.exp (κ' * d Y) ≤
        3 * c1 * Real.exp (-p) * K0P * Real.exp (c1 + κ' * cP) * Real.exp (-(κ' * cP))) ∧
    ‖logSeries (shareBlock (Subtype.val : NePoly B → Finset B)) (gasKOp cy zs cr β τ μ)‖ ≤
      Fintype.card B * (3 * c1 * Real.exp (-p) * K0P * Real.exp (c1 + κ' * cP)) := by
  exact actGasOp_pe hB0 hκg hκ'' hc hc1 hp hd hz
    (coreAct_local (fun _ => Finset.Subset.rfl) hcr) (coreAct_meets (fun _ => Finset.Subset.rfl) hcr)
    hβd hτd hβm hτm (fun z => integrable_of_bdd μ (hτm z) (hτb z)) (fun _ _ y _ Φ _ => hB y Φ)
    hzd hG3 hK0g (fun Γ _ b => sum_filter_act_le (fun _ => (Real.exp_pos _).le) hent Γ b) hK1
    (sum_filter_le_of_count hτ hcount) hh hG1 hK0P hκ' hcP hG2P hG3P hκ hα

end Bound

end Operator

end Balaban.Polymer
