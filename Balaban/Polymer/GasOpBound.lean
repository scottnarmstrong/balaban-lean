/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Polymer.GasOpEq
public import Balaban.Polymer.Size

/-!
# The activity bound of GAS with a general activation rule, for weights that are functions of
the configuration

The operator norm of a heavy weight is its integral norm `E |τ Z|` and that of a coupling weight
`e^{β Y} - 1` is its sup on the set where the heavy weights activating it do not vanish
(`notes/phase1/LF-RECONSTRUCTION.md` (3.10″)).

* `norm_integral_prod_gasW_le`: the expectation of the product of the weights of an admissible
  family is at most `∏ s(Y) ∏ E |τ Z|` (heavy objects act on disjoint sets of variables).
* `sum_norm_integral_cfam_le_of_counts`: with the sup bounds `B₀ e^{-κ'' d(Y)}` of the couplings
  and the weighted counts `∑_{Z ∋ b, |Z| = v} E|τ Z| ≤ K₀''^v e^{-p - h v}` of the heavy weights,
  `∑_{C ∈ Cfam X} |E ∏_C w| ≤ 3 c₁ e^{-p} e^{-(κ' - 2) d(X)}` for `|X| ≤ c₁ (1 + d(X))` (the
  bound of `gas_activity_bound`; the scalar core is `sum_cfam_actGas_le_of_counts`).
* `actGasKOp_activity_bound`: the activities of `actGasXiOp_eq` obey that bound.
* `actGasOp_pe`: with `pe_size`, the expectation of the partition function is `exp L` for an
  absolutely convergent cluster sum `L`, with local terms decaying at the rate `κg - 2`.
* `sum_norm_integral_cfam_le_of_counts_sized`, `actGasKOp_activity_bound_sized`,
  `actGasOp_pe_sized`: the cores with a size `σ`, attachment and anchor sets, a count prefactor `M₀`
  and an entropy margin `c'` (`sum_cfam_actGas_le_of_counts_sized`), with `pe_size_gen` for the
  expansion; the statements above are their instances.
-/

@[expose] public section

noncomputable section

open scoped Classical

open Finset MeasureTheory

namespace Balaban.Polymer

section Bound

variable {B Yt Zt : Type*} [Fintype B] [Fintype Yt] [Fintype Zt]
  {Ω : B → Type*} [∀ b, MeasurableSpace (Ω b)]
  {act : Yt → Finset Zt → Prop} {cy : Yt → Finset B} {zs : Zt → Finset B}
  {β : Yt → (∀ b, Ω b) → ℂ} {τ : Zt → (∀ b, Ω b) → ℂ} {μ : ∀ b, Measure (Ω b)}
  [∀ b, IsProbabilityMeasure (μ b)]

omit [Fintype Yt] [Fintype Zt] in
/-- The expectation of the product of the weights of an admissible family is bounded by the
product of the coupling majorants and of the integral norms of the heavy weights. -/
theorem norm_integral_prod_gasW_le {s : Yt → ℝ}
    (hτd : ∀ z, DepOn (zs z) (τ z)) (hβm : ∀ y, Measurable (β y)) (hτm : ∀ z, Measurable (τ z))
    (hτi : ∀ z, Integrable (τ z) (Measure.pi μ))
    (hB : ∀ Γ : Finset Zt, (∀ z ∈ Γ, ∀ z' ∈ Γ, z ≠ z' → Disjoint (zs z) (zs z')) →
      ∀ y, act y Γ → ∀ Φ, (∀ z ∈ Γ, τ z Φ ≠ 0) → ‖Complex.exp (β y Φ) - 1‖ ≤ s y)
    {C : Finset (Yt ⊕ Zt)} (hC : actGasA act zs C) :
    ‖∫ Φ, ∏ t ∈ C, gasW (fun y => β y Φ) (fun z => τ z Φ) t ∂(Measure.pi μ)‖ ≤
      (∏ y ∈ C.toLeft, s y) * ∏ z ∈ C.toRight, ∫ Φ, ‖τ z Φ‖ ∂(Measure.pi μ) := by
  have hT := integrable_prod_depOn μ C.toRight zs τ hC.1 (fun z _ => hτd z) hτm
    (fun z _ => hτi z)
  have hTn : Integrable (fun Φ => ∏ z ∈ C.toRight, ‖τ z Φ‖) (Measure.pi μ) := by
    simpa only [norm_prod] using hT.norm
  calc ‖∫ Φ, ∏ t ∈ C, gasW (fun y => β y Φ) (fun z => τ z Φ) t ∂(Measure.pi μ)‖
      ≤ ∫ Φ, ‖∏ t ∈ C, gasW (fun y => β y Φ) (fun z => τ z Φ) t‖ ∂(Measure.pi μ) :=
        norm_integral_le_integral_norm _
    _ ≤ ∫ Φ, (∏ y ∈ C.toLeft, s y) * ∏ z ∈ C.toRight, ‖τ z Φ‖ ∂(Measure.pi μ) :=
        integral_mono (integrable_prod_gasW_of_actGasA hτd hβm hτm hτi hB hC).norm
          (hTn.const_mul _)
          (fun Φ => norm_prod_gasW_le Φ (fun h y hy => hB _ hC.1 y (hC.2 y hy) Φ h))
    _ = (∏ y ∈ C.toLeft, s y) * ∫ Φ, ∏ z ∈ C.toRight, ‖τ z Φ‖ ∂(Measure.pi μ) :=
        integral_const_mul _ _
    _ = (∏ y ∈ C.toLeft, s y) * ∏ z ∈ C.toRight, ∫ Φ, ‖τ z Φ‖ ∂(Measure.pi μ) := by
        rw [integral_prod_norm_depOn μ C.toRight zs τ hC.1 (fun z _ => hτd z) hτm]

/-- **The activity bound for functions of the configuration, for heavy objects with a size, an
attachment set and an anchor set**: with the sup bounds `B₀ e^{-κ'' d(Y)}` of the couplings and the
counts `∑_{Z : b ∈ anc Z, σ Z = v} E|τ Z| ≤ M₀ K₀''^v e^{-p - h v}`,
`∑_{C ∈ Cfam X} |E ∏_C w| ≤ 3 c₁ η e^{-(κ' - 2) d(X)}`, `η = M₀ e^{-p} e^{-(c'+2)}`, for
`|X| ≤ c₁ (1 + d(X))` (the scalar core is `sum_cfam_actGas_le_of_counts_sized`). -/
theorem sum_norm_integral_cfam_le_of_counts_sized {d : Finset B → ℝ}
    {B0 κ' κ'' c c1 c' c2 p h K0' K0'' M0 : ℝ}
    (hB0 : 0 ≤ B0) (hκ' : 0 ≤ κ') (hκ'' : κ' ≤ κ'') (hc : 0 ≤ c) (hc1 : 0 ≤ c1) (hc' : 0 ≤ c')
    (hM0 : 0 ≤ M0) (hd : ∀ Y, 0 ≤ d Y)
    (σ : Zt → ℕ) (hσ : ∀ z, 1 ≤ σ z) (att anc : Zt → Finset B)
    (hanc : ∀ z, (anc z).Nonempty) (hancs : ∀ z, anc z ⊆ zs z)
    (hatt : ∀ z, (att z).card ≤ σ z)
    (hmeet : ∀ y Γ, act y Γ → ∃ z ∈ Γ, ¬ Disjoint (cy y) (att z))
    (hτd : ∀ z, DepOn (zs z) (τ z)) (hβm : ∀ y, Measurable (β y)) (hτm : ∀ z, Measurable (τ z))
    (hτi : ∀ z, Integrable (τ z) (Measure.pi μ))
    (hB : ∀ Γ : Finset Zt, (∀ z ∈ Γ, ∀ z' ∈ Γ, z ≠ z' → Disjoint (zs z) (zs z')) →
      ∀ y, act y Γ → ∀ Φ, (∀ z ∈ Γ, τ z Φ ≠ 0) → ‖β y Φ‖ ≤ B0 * Real.exp (-κ'' * d (cy y)))
    (hzd : ∀ z, d (zs z) ≤ c2 * σ z)
    (hG3 : ∀ C : Finset (Yt ⊕ Zt), ConnSet (gasCs cy zs) C → actGasA act zs C →
      d (unionCs (gasCs cy zs) C) ≤ ∑ t ∈ C, d (gasCs cy zs t) + c * ((C.card : ℝ) - 1))
    (hK0' : 0 ≤ K0')
    (hent : ∀ Γ : Finset Zt, (∀ z ∈ Γ, ∀ z' ∈ Γ, z ≠ z' → Disjoint (zs z) (zs z')) →
      ∀ b : B, ∑ y ∈ Finset.univ.filter (fun y => act y Γ ∧ b ∈ cy y),
        Real.exp (-(κ'' - κ') * d (cy y)) ≤ K0')
    (hK1 : 1 ≤ K0'')
    (hcount : ∀ (b : B) (v : ℕ),
      ∑ z ∈ Finset.univ.filter (fun z => b ∈ anc z ∧ σ z = v),
        ∫ Φ, ‖τ z Φ‖ ∂(Measure.pi μ) ≤ M0 * K0'' ^ v * Real.exp (-p - h * v))
    (hh : B0 * Real.exp B0 * Real.exp (κ' * c) * K0' + κ' * (c2 + c) + c' + 3 +
      Real.log K0'' ≤ h)
    (hη : c1 * (M0 * Real.exp (-p) * Real.exp (-(c' + 2))) ≤ 1 / 7)
    (X : Finset B) (hG1 : (X.card : ℝ) ≤ c1 * (1 + d X)) :
    ∑ C ∈ Cfam (gasCs cy zs) (actGasA act zs) X,
        ‖∫ Φ, ∏ t ∈ C, gasW (fun y => β y Φ) (fun z => τ z Φ) t ∂(Measure.pi μ)‖ ≤
      3 * (c1 * (M0 * Real.exp (-p) * Real.exp (-(c' + 2)))) * Real.exp (-(κ' - 2) * d X) := by
  refine le_trans (Finset.sum_le_sum (fun C hC => norm_integral_prod_gasW_le
    (s := fun y => B0 * Real.exp B0 * Real.exp (-κ'' * d (cy y))) hτd hβm hτm hτi
    (fun Γ hΓ y hy Φ hΦ => norm_expm1_le (β := fun y => β y Φ) hB0 (hκ'.trans hκ'') hd y
      (hB Γ hΓ y hy Φ hΦ)) (mem_Cfam.mp hC).2.1)) ?_
  exact sum_cfam_actGas_le_of_counts_sized hB0 hκ' hc hc1 hc' hM0 hd σ hσ att anc hanc hancs hatt
    hmeet _ (fun z => integral_nonneg (fun _ => norm_nonneg _)) hzd hG3 hK0' hent hK1 hcount hh
    hη X hG1

/-- `3 c₁ (e^{-p} e^{-(c₁+2)}) ≤ 3 c₁ e^{-p}` for `c₁ ≥ 0`. -/
theorem three_mul_eta_le {c1 p : ℝ} (hc1 : 0 ≤ c1) :
    3 * (c1 * (1 * Real.exp (-p) * Real.exp (-(c1 + 2)))) ≤ 3 * c1 * Real.exp (-p) := by
  have hle : Real.exp (-(c1 + 2)) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have h0 : 0 ≤ Real.exp (-p) := (Real.exp_pos _).le
  nlinarith [mul_le_mul_of_nonneg_left hle (mul_nonneg hc1 h0)]

/-- **The activity bound for functions of the configuration.**  If the couplings are bounded by
`B₀ e^{-κ'' d(Y)}` where the heavy weights activating them do not vanish, the integral norms of the
heavy weights through a block with `v` blocks sum to at most `K₀''^v e^{-p - h v}` (weighted counts)
and the couplings active for every compatible family have `∑_{Y ∋ b} e^{-(κ'' - κ') d(Y)} ≤ K₀'`,
then `∑_{C ∈ Cfam X} |E ∏_C w| ≤ 3 c₁ e^{-p} e^{-(κ' - 2) d(X)}` for `|X| ≤ c₁ (1 + d(X))`,
provided `h ≥ B₀ e^{B₀} e^{κ' c} K₀' + κ' (c₂ + c) + c₁ + 3 + ln K₀''` (the instance of
`sum_norm_integral_cfam_le_of_counts_sized` with the size `|Z|`). -/
theorem sum_norm_integral_cfam_le_of_counts {d : Finset B → ℝ}
    {B0 κ' κ'' c c1 c2 p h K0' K0'' : ℝ}
    (hB0 : 0 ≤ B0) (hκ' : 0 ≤ κ') (hκ'' : κ' ≤ κ'') (hc : 0 ≤ c) (hc1 : 0 ≤ c1) (hp : 0 ≤ p)
    (hd : ∀ Y, 0 ≤ d Y) (hz : ∀ z, (zs z).Nonempty)
    (hmeet : ∀ y Γ, act y Γ → ∃ z ∈ Γ, ¬ Disjoint (cy y) (zs z))
    (hτd : ∀ z, DepOn (zs z) (τ z)) (hβm : ∀ y, Measurable (β y)) (hτm : ∀ z, Measurable (τ z))
    (hτi : ∀ z, Integrable (τ z) (Measure.pi μ))
    (hB : ∀ Γ : Finset Zt, (∀ z ∈ Γ, ∀ z' ∈ Γ, z ≠ z' → Disjoint (zs z) (zs z')) →
      ∀ y, act y Γ → ∀ Φ, (∀ z ∈ Γ, τ z Φ ≠ 0) → ‖β y Φ‖ ≤ B0 * Real.exp (-κ'' * d (cy y)))
    (hzd : ∀ z, d (zs z) ≤ c2 * (zs z).card)
    (hG3 : ∀ C : Finset (Yt ⊕ Zt), ConnSet (gasCs cy zs) C → actGasA act zs C →
      d (unionCs (gasCs cy zs) C) ≤ ∑ t ∈ C, d (gasCs cy zs t) + c * ((C.card : ℝ) - 1))
    (hK0' : 0 ≤ K0')
    (hent : ∀ Γ : Finset Zt, (∀ z ∈ Γ, ∀ z' ∈ Γ, z ≠ z' → Disjoint (zs z) (zs z')) →
      ∀ b : B, ∑ y ∈ Finset.univ.filter (fun y => act y Γ ∧ b ∈ cy y),
        Real.exp (-(κ'' - κ') * d (cy y)) ≤ K0')
    (hK1 : 1 ≤ K0'')
    (hcount : ∀ (b : B) (v : ℕ),
      ∑ z ∈ Finset.univ.filter (fun z => b ∈ zs z ∧ (zs z).card = v),
        ∫ Φ, ‖τ z Φ‖ ∂(Measure.pi μ) ≤ K0'' ^ v * Real.exp (-p - h * v))
    (hh : B0 * Real.exp B0 * Real.exp (κ' * c) * K0' + κ' * (c2 + c) + c1 + 3 +
      Real.log K0'' ≤ h)
    (X : Finset B) (hG1 : (X.card : ℝ) ≤ c1 * (1 + d X)) :
    ∑ C ∈ Cfam (gasCs cy zs) (actGasA act zs) X,
        ‖∫ Φ, ∏ t ∈ C, gasW (fun y => β y Φ) (fun z => τ z Φ) t ∂(Measure.pi μ)‖ ≤
      3 * c1 * Real.exp (-p) * Real.exp (-(κ' - 2) * d X) :=
  (sum_norm_integral_cfam_le_of_counts_sized (M0 := 1) (c' := c1) hB0 hκ' hκ'' hc hc1 hc1
    zero_le_one hd (fun z => (zs z).card) (fun z => (hz z).card_pos) zs zs hz
    (fun _ => subset_rfl) (fun _ => le_rfl) hmeet hτd hβm hτm hτi hB hzd hG3 hK0' hent hK1
    (fun b v => by simpa using hcount b v) hh (by simpa using mul_exp_neg_le_seventh hp hc1) X
    hG1).trans (mul_le_mul_of_nonneg_right (three_mul_eta_le hc1) (Real.exp_pos _).le)

/-- The activity is at most the sum over its families of the norms of their expectations. -/
theorem norm_actGasKOp_le_sum {s : Yt → ℝ}
    (hτd : ∀ z, DepOn (zs z) (τ z)) (hβm : ∀ y, Measurable (β y)) (hτm : ∀ z, Measurable (τ z))
    (hτi : ∀ z, Integrable (τ z) (Measure.pi μ))
    (hB : ∀ Γ : Finset Zt, (∀ z ∈ Γ, ∀ z' ∈ Γ, z ≠ z' → Disjoint (zs z) (zs z')) →
      ∀ y, act y Γ → ∀ Φ, (∀ z ∈ Γ, τ z Φ ≠ 0) → ‖Complex.exp (β y Φ) - 1‖ ≤ s y)
    (X : NePoly B) :
    ‖actGasKOp act cy zs β τ μ X‖ ≤ ∑ C ∈ Cfam (gasCs cy zs) (actGasA act zs) X.1,
      ‖∫ Φ, ∏ t ∈ C, gasW (fun y => β y Φ) (fun z => τ z Φ) t ∂(Measure.pi μ)‖ := by
  unfold actGasKOp actGasActOp actGasK polyAct
  rw [integral_finsetSum _ (fun C hC =>
    integrable_prod_gasW_of_actGasA hτd hβm hτm hτi hB (mem_Cfam.mp hC).2.1)]
  exact norm_sum_le _ _

/-- **GAS with a general activation rule (activity bound) for functions of the configuration, for
heavy objects with a size, an attachment set and an anchor set**: under the hypotheses of
`sum_norm_integral_cfam_le_of_counts_sized`, `‖K(X)‖ ≤ 3 c₁ η e^{-(κ' - 2) d(X)}`,
`η = M₀ e^{-p} e^{-(c'+2)}`, for `|X| ≤ c₁ (1 + d(X))`. -/
theorem actGasKOp_activity_bound_sized {d : Finset B → ℝ}
    {B0 κ' κ'' c c1 c' c2 p h K0' K0'' M0 : ℝ}
    (hB0 : 0 ≤ B0) (hκ' : 0 ≤ κ') (hκ'' : κ' ≤ κ'') (hc : 0 ≤ c) (hc1 : 0 ≤ c1) (hc' : 0 ≤ c')
    (hM0 : 0 ≤ M0) (hd : ∀ Y, 0 ≤ d Y)
    (σ : Zt → ℕ) (hσ : ∀ z, 1 ≤ σ z) (att anc : Zt → Finset B)
    (hanc : ∀ z, (anc z).Nonempty) (hancs : ∀ z, anc z ⊆ zs z)
    (hatt : ∀ z, (att z).card ≤ σ z)
    (hmeet : ∀ y Γ, act y Γ → ∃ z ∈ Γ, ¬ Disjoint (cy y) (att z))
    (hτd : ∀ z, DepOn (zs z) (τ z)) (hβm : ∀ y, Measurable (β y)) (hτm : ∀ z, Measurable (τ z))
    (hτi : ∀ z, Integrable (τ z) (Measure.pi μ))
    (hB : ∀ Γ : Finset Zt, (∀ z ∈ Γ, ∀ z' ∈ Γ, z ≠ z' → Disjoint (zs z) (zs z')) →
      ∀ y, act y Γ → ∀ Φ, (∀ z ∈ Γ, τ z Φ ≠ 0) → ‖β y Φ‖ ≤ B0 * Real.exp (-κ'' * d (cy y)))
    (hzd : ∀ z, d (zs z) ≤ c2 * σ z)
    (hG3 : ∀ C : Finset (Yt ⊕ Zt), ConnSet (gasCs cy zs) C → actGasA act zs C →
      d (unionCs (gasCs cy zs) C) ≤ ∑ t ∈ C, d (gasCs cy zs t) + c * ((C.card : ℝ) - 1))
    (hK0' : 0 ≤ K0')
    (hent : ∀ Γ : Finset Zt, (∀ z ∈ Γ, ∀ z' ∈ Γ, z ≠ z' → Disjoint (zs z) (zs z')) →
      ∀ b : B, ∑ y ∈ Finset.univ.filter (fun y => act y Γ ∧ b ∈ cy y),
        Real.exp (-(κ'' - κ') * d (cy y)) ≤ K0')
    (hK1 : 1 ≤ K0'')
    (hcount : ∀ (b : B) (v : ℕ),
      ∑ z ∈ Finset.univ.filter (fun z => b ∈ anc z ∧ σ z = v),
        ∫ Φ, ‖τ z Φ‖ ∂(Measure.pi μ) ≤ M0 * K0'' ^ v * Real.exp (-p - h * v))
    (hh : B0 * Real.exp B0 * Real.exp (κ' * c) * K0' + κ' * (c2 + c) + c' + 3 +
      Real.log K0'' ≤ h)
    (hη : c1 * (M0 * Real.exp (-p) * Real.exp (-(c' + 2))) ≤ 1 / 7)
    (X : NePoly B) (hG1 : (X.1.card : ℝ) ≤ c1 * (1 + d X.1)) :
    ‖actGasKOp act cy zs β τ μ X‖ ≤
      3 * (c1 * (M0 * Real.exp (-p) * Real.exp (-(c' + 2)))) * Real.exp (-(κ' - 2) * d X.1) :=
  (norm_actGasKOp_le_sum (s := fun y => B0 * Real.exp B0 * Real.exp (-κ'' * d (cy y)))
      hτd hβm hτm hτi (fun Γ hΓ y hy Φ hΦ => norm_expm1_le (β := fun y => β y Φ) hB0
        (hκ'.trans hκ'') hd y (hB Γ hΓ y hy Φ hΦ)) X).trans
    (sum_norm_integral_cfam_le_of_counts_sized hB0 hκ' hκ'' hc hc1 hc' hM0 hd σ hσ att anc hanc
      hancs hatt hmeet hτd hβm hτm hτi hB hzd hG3 hK0' hent hK1 hcount hh hη X.1 hG1)

/-- **GAS with a general activation rule (activity bound) for functions of the configuration.**
Under the hypotheses of `sum_norm_integral_cfam_le_of_counts`, the activities of `actGasXiOp_eq`
satisfy `‖K(X)‖ ≤ 3 c₁ e^{-p} e^{-(κ' - 2) d(X)}` for `|X| ≤ c₁ (1 + d(X))`. -/
theorem actGasKOp_activity_bound {d : Finset B → ℝ}
    {B0 κ' κ'' c c1 c2 p h K0' K0'' : ℝ}
    (hB0 : 0 ≤ B0) (hκ' : 0 ≤ κ') (hκ'' : κ' ≤ κ'') (hc : 0 ≤ c) (hc1 : 0 ≤ c1) (hp : 0 ≤ p)
    (hd : ∀ Y, 0 ≤ d Y) (hz : ∀ z, (zs z).Nonempty)
    (hmeet : ∀ y Γ, act y Γ → ∃ z ∈ Γ, ¬ Disjoint (cy y) (zs z))
    (hτd : ∀ z, DepOn (zs z) (τ z)) (hβm : ∀ y, Measurable (β y)) (hτm : ∀ z, Measurable (τ z))
    (hτi : ∀ z, Integrable (τ z) (Measure.pi μ))
    (hB : ∀ Γ : Finset Zt, (∀ z ∈ Γ, ∀ z' ∈ Γ, z ≠ z' → Disjoint (zs z) (zs z')) →
      ∀ y, act y Γ → ∀ Φ, (∀ z ∈ Γ, τ z Φ ≠ 0) → ‖β y Φ‖ ≤ B0 * Real.exp (-κ'' * d (cy y)))
    (hzd : ∀ z, d (zs z) ≤ c2 * (zs z).card)
    (hG3 : ∀ C : Finset (Yt ⊕ Zt), ConnSet (gasCs cy zs) C → actGasA act zs C →
      d (unionCs (gasCs cy zs) C) ≤ ∑ t ∈ C, d (gasCs cy zs t) + c * ((C.card : ℝ) - 1))
    (hK0' : 0 ≤ K0')
    (hent : ∀ Γ : Finset Zt, (∀ z ∈ Γ, ∀ z' ∈ Γ, z ≠ z' → Disjoint (zs z) (zs z')) →
      ∀ b : B, ∑ y ∈ Finset.univ.filter (fun y => act y Γ ∧ b ∈ cy y),
        Real.exp (-(κ'' - κ') * d (cy y)) ≤ K0')
    (hK1 : 1 ≤ K0'')
    (hcount : ∀ (b : B) (v : ℕ),
      ∑ z ∈ Finset.univ.filter (fun z => b ∈ zs z ∧ (zs z).card = v),
        ∫ Φ, ‖τ z Φ‖ ∂(Measure.pi μ) ≤ K0'' ^ v * Real.exp (-p - h * v))
    (hh : B0 * Real.exp B0 * Real.exp (κ' * c) * K0' + κ' * (c2 + c) + c1 + 3 +
      Real.log K0'' ≤ h)
    (X : NePoly B) (hG1 : (X.1.card : ℝ) ≤ c1 * (1 + d X.1)) :
    ‖actGasKOp act cy zs β τ μ X‖ ≤ 3 * c1 * Real.exp (-p) * Real.exp (-(κ' - 2) * d X.1) :=
  (actGasKOp_activity_bound_sized (M0 := 1) (c' := c1) hB0 hκ' hκ'' hc hc1 hc1 zero_le_one hd
    (fun z => (zs z).card) (fun z => (hz z).card_pos) zs zs hz (fun _ => subset_rfl)
    (fun _ => le_rfl) hmeet hτd hβm hτm hτi hB hzd hG3 hK0' hent hK1
    (fun b v => by simpa using hcount b v) hh (by simpa using mul_exp_neg_le_seventh hp hc1) X
    hG1).trans (mul_le_mul_of_nonneg_right (three_mul_eta_le hc1) (Real.exp_pos _).le)

/-- **GAS with a general activation rule + PE-L for functions of the configuration, for heavy
objects with a size, an attachment set and an anchor set** (the core).  The activities obey
`‖K(X)‖ ≤ ε e^{-(κg - 2) d(X)}`, `ε = 3 c₁ η`, `η = M₀ e^{-p} e^{-(c'+2)}`
(`actGasKOp_activity_bound_sized`), and `pe_size_gen` applies with the Kotecký–Preiss weight
dominated by the size, `α |X| ≤ a₀ (1 + d(X))`, `α = ε K₀ᴾ e^{a₀ + κ' cᴾ}`: the expectation of the
partition function is `exp(L)` for an absolutely convergent cluster sum, with local terms decaying
at the rate `κ'`.  The sites per unit of size enter through `α` only. -/
theorem actGasOp_pe_sized {d : Finset B → ℝ} {B0 κ'' c c1 c' c2 p h M0 : ℝ}
    {κg K0g K0h κ' κ0P K0P cP a₀ : ℝ}
    (hB0 : 0 ≤ B0) (hκg : 0 ≤ κg) (hκ'' : κg ≤ κ'') (hc : 0 ≤ c) (hc1 : 0 ≤ c1) (hc' : 0 ≤ c')
    (hM0 : 0 ≤ M0) (hd : ∀ Y, 0 ≤ d Y) (hz : ∀ z, (zs z).Nonempty)
    (σ : Zt → ℕ) (hσ : ∀ z, 1 ≤ σ z) (att anc : Zt → Finset B)
    (hanc : ∀ z, (anc z).Nonempty) (hancs : ∀ z, anc z ⊆ zs z)
    (hattzs : ∀ z, att z ⊆ zs z) (hatt : ∀ z, (att z).card ≤ σ z)
    (hloc : ∀ y Γ, act y Γ ↔ act y (Γ.filter (fun z => ¬ Disjoint (cy y) (zs z))))
    (hmeet : ∀ y Γ, act y Γ → ∃ z ∈ Γ, ¬ Disjoint (cy y) (att z))
    (hβd : ∀ y, DepOn (cy y) (β y)) (hτd : ∀ z, DepOn (zs z) (τ z))
    (hβm : ∀ y, Measurable (β y)) (hτm : ∀ z, Measurable (τ z))
    (hτi : ∀ z, Integrable (τ z) (Measure.pi μ))
    (hB : ∀ Γ : Finset Zt, (∀ z ∈ Γ, ∀ z' ∈ Γ, z ≠ z' → Disjoint (zs z) (zs z')) →
      ∀ y, act y Γ → ∀ Φ, (∀ z ∈ Γ, τ z Φ ≠ 0) → ‖β y Φ‖ ≤ B0 * Real.exp (-κ'' * d (cy y)))
    (hzd : ∀ z, d (zs z) ≤ c2 * σ z)
    (hG3 : ∀ C : Finset (Yt ⊕ Zt), ConnSet (gasCs cy zs) C → actGasA act zs C →
      d (unionCs (gasCs cy zs) C) ≤ ∑ t ∈ C, d (gasCs cy zs t) + c * ((C.card : ℝ) - 1))
    (hK0g : 0 ≤ K0g)
    (hent : ∀ Γ : Finset Zt, (∀ z ∈ Γ, ∀ z' ∈ Γ, z ≠ z' → Disjoint (zs z) (zs z')) →
      ∀ b : B, ∑ y ∈ Finset.univ.filter (fun y => act y Γ ∧ b ∈ cy y),
        Real.exp (-(κ'' - κg) * d (cy y)) ≤ K0g)
    (hK1 : 1 ≤ K0h)
    (hcount : ∀ (b : B) (v : ℕ),
      ∑ z ∈ Finset.univ.filter (fun z => b ∈ anc z ∧ σ z = v),
        ∫ Φ, ‖τ z Φ‖ ∂(Measure.pi μ) ≤ M0 * K0h ^ v * Real.exp (-p - h * v))
    (hh : B0 * Real.exp B0 * Real.exp (κg * c) * K0g + κg * (c2 + c) + c' + 3 +
      Real.log K0h ≤ h)
    (hη : c1 * (M0 * Real.exp (-p) * Real.exp (-(c' + 2))) ≤ 1 / 7)
    (hG1 : ∀ X : NePoly B, (X.1.card : ℝ) ≤ c1 * (1 + d X.1))
    (hK0P : 0 ≤ K0P) (hκ' : 0 ≤ κ') (hcP : 0 ≤ cP)
    (hG1P : ∀ X : NePoly B, 3 * (c1 * (M0 * Real.exp (-p) * Real.exp (-(c' + 2)))) * K0P *
      Real.exp (a₀ + κ' * cP) * X.1.card ≤ a₀ * (1 + d X.1))
    (hG2P : ∀ b : B, ∑ Y : NePoly B, (if b ∈ Y.1 then Real.exp (-κ0P * d Y.1) else 0) ≤ K0P)
    (hG3P : ∀ (n : ℕ) (X : Fin (n + 1) → NePoly B),
      (clusterGraph (shareBlock (Subtype.val : NePoly B → Finset B)) X).Connected →
        d (unionOf (Subtype.val : NePoly B → Finset B) X) ≤ ∑ i, d (X i).1 + cP * n)
    (hκ : κ' + κ0P + a₀ ≤ κg - 2) :
    actGasXiOp act zs β τ μ =
      Complex.exp (logSeries (shareBlock (Subtype.val : NePoly B → Finset B))
        (actGasKOp act cy zs β τ μ)) ∧
    (∀ b : B, ∑ Y ∈ (Finset.univ : Finset (Finset B)).filter (fun Y => b ∈ Y),
        ‖PY (shareBlock (Subtype.val : NePoly B → Finset B)) Subtype.val
          (actGasKOp act cy zs β τ μ) Y‖ * Real.exp (κ' * d Y) ≤
        3 * (c1 * (M0 * Real.exp (-p) * Real.exp (-(c' + 2)))) * K0P *
          Real.exp (a₀ + κ' * cP) * Real.exp (-(κ' * cP))) ∧
    ‖logSeries (shareBlock (Subtype.val : NePoly B → Finset B)) (actGasKOp act cy zs β τ μ)‖ ≤
      Fintype.card B * (3 * (c1 * (M0 * Real.exp (-p) * Real.exp (-(c' + 2)))) * K0P *
        Real.exp (a₀ + κ' * cP)) := by
  set ε : ℝ := 3 * (c1 * (M0 * Real.exp (-p) * Real.exp (-(c' + 2)))) with hεdef
  have hmeetz : ∀ y Γ, act y Γ → ∃ z ∈ Γ, ¬ Disjoint (cy y) (zs z) := fun y Γ h => by
    obtain ⟨z, hz, hnd⟩ := hmeet y Γ h
    exact ⟨z, hz, fun hd => hnd (Finset.disjoint_of_subset_right (hattzs z) hd)⟩
  have hK : ∀ X : NePoly B, ‖actGasKOp act cy zs β τ μ X‖ ≤ ε * Real.exp (-(κg - 2) * d X.1) :=
    fun X => actGasKOp_activity_bound_sized hB0 hκg hκ'' hc hc1 hc' hM0 hd σ hσ att anc hanc
      hancs hatt hmeet hτd hβm hτm hτi hB hzd hG3 hK0g hent hK1 hcount hh hη X (hG1 X)
  have hε : 0 ≤ ε := by rw [hεdef]; positivity
  have hpe := pe_size_gen (Subtype.val : NePoly B → Finset B) d (ε := ε)
    (κ := κg - 2) (κ' := κ') (κ0 := κ0P) (K0 := K0P) (c := cP) (a₀ := a₀)
    hε hK0P hκ' hcP hd (fun Y => Y.2) hG1P hG2P hG3P hκ Finset.univ
    (fun Y => by obtain ⟨b, hb⟩ := Y.2; exact ⟨b, Finset.mem_univ _, hb⟩)
    (actGasKOp act cy zs β τ μ) hK
  obtain ⟨h1, _, h3, h4, _⟩ := hpe
  refine ⟨(actGasXiOp_eq (s := fun y => B0 * Real.exp B0 * Real.exp (-κ'' * d (cy y)))
    hz hloc hmeetz hβd hτd hβm hτm hτi (fun Γ hΓ y hy Φ hΦ => norm_expm1_le (β := fun y => β y Φ)
      hB0 (hκg.trans hκ'') hd y (hB Γ hΓ y hy Φ hΦ))).trans h1, ?_, ?_⟩
  · intro b
    simpa [mul_assoc] using h3 b
  · simpa [mul_assoc] using h4

/-- **GAS with a general activation rule + PE-L for functions of the configuration**: the
expectation of the partition function is `exp(L)` for an absolutely convergent cluster sum, with
local terms decaying at the rate `κg - 2` (`gasOp_pe` for the rule `coreAct`; the instance of
`actGasOp_pe_sized` with the size `|Z|`, `a₀ = c₁`). -/
theorem actGasOp_pe {d : Finset B → ℝ} {B0 κ'' c c1 c2 p h : ℝ}
    {κg K0g K0h κ' κ0P K0P cP : ℝ}
    (hB0 : 0 ≤ B0) (hκg : 0 ≤ κg) (hκ'' : κg ≤ κ'') (hc : 0 ≤ c) (hc1 : 0 ≤ c1) (hp : 0 ≤ p)
    (hd : ∀ Y, 0 ≤ d Y) (hz : ∀ z, (zs z).Nonempty)
    (hloc : ∀ y Γ, act y Γ ↔ act y (Γ.filter (fun z => ¬ Disjoint (cy y) (zs z))))
    (hmeet : ∀ y Γ, act y Γ → ∃ z ∈ Γ, ¬ Disjoint (cy y) (zs z))
    (hβd : ∀ y, DepOn (cy y) (β y)) (hτd : ∀ z, DepOn (zs z) (τ z))
    (hβm : ∀ y, Measurable (β y)) (hτm : ∀ z, Measurable (τ z))
    (hτi : ∀ z, Integrable (τ z) (Measure.pi μ))
    (hB : ∀ Γ : Finset Zt, (∀ z ∈ Γ, ∀ z' ∈ Γ, z ≠ z' → Disjoint (zs z) (zs z')) →
      ∀ y, act y Γ → ∀ Φ, (∀ z ∈ Γ, τ z Φ ≠ 0) → ‖β y Φ‖ ≤ B0 * Real.exp (-κ'' * d (cy y)))
    (hzd : ∀ z, d (zs z) ≤ c2 * (zs z).card)
    (hG3 : ∀ C : Finset (Yt ⊕ Zt), ConnSet (gasCs cy zs) C → actGasA act zs C →
      d (unionCs (gasCs cy zs) C) ≤ ∑ t ∈ C, d (gasCs cy zs t) + c * ((C.card : ℝ) - 1))
    (hK0g : 0 ≤ K0g)
    (hent : ∀ Γ : Finset Zt, (∀ z ∈ Γ, ∀ z' ∈ Γ, z ≠ z' → Disjoint (zs z) (zs z')) →
      ∀ b : B, ∑ y ∈ Finset.univ.filter (fun y => act y Γ ∧ b ∈ cy y),
        Real.exp (-(κ'' - κg) * d (cy y)) ≤ K0g)
    (hK1 : 1 ≤ K0h)
    (hcount : ∀ (b : B) (v : ℕ),
      ∑ z ∈ Finset.univ.filter (fun z => b ∈ zs z ∧ (zs z).card = v),
        ∫ Φ, ‖τ z Φ‖ ∂(Measure.pi μ) ≤ K0h ^ v * Real.exp (-p - h * v))
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
    actGasXiOp act zs β τ μ =
      Complex.exp (logSeries (shareBlock (Subtype.val : NePoly B → Finset B))
        (actGasKOp act cy zs β τ μ)) ∧
    (∀ b : B, ∑ Y ∈ (Finset.univ : Finset (Finset B)).filter (fun Y => b ∈ Y),
        ‖PY (shareBlock (Subtype.val : NePoly B → Finset B)) Subtype.val
          (actGasKOp act cy zs β τ μ) Y‖ * Real.exp (κ' * d Y) ≤
        3 * c1 * Real.exp (-p) * K0P * Real.exp (c1 + κ' * cP) * Real.exp (-(κ' * cP))) ∧
    ‖logSeries (shareBlock (Subtype.val : NePoly B → Finset B)) (actGasKOp act cy zs β τ μ)‖ ≤
      Fintype.card B * (3 * c1 * Real.exp (-p) * K0P * Real.exp (c1 + κ' * cP)) := by
  have hle := three_mul_eta_le (p := p) hc1
  have hA : 3 * (c1 * (1 * Real.exp (-p) * Real.exp (-(c1 + 2)))) * K0P *
      Real.exp (c1 + κ' * cP) ≤ 3 * c1 * Real.exp (-p) * K0P * Real.exp (c1 + κ' * cP) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hle hK0P) (Real.exp_pos _).le
  obtain ⟨h1, h2, h3⟩ := actGasOp_pe_sized (M0 := 1) (c' := c1) (a₀ := c1) hB0 hκg hκ'' hc hc1
    hc1 zero_le_one hd hz (fun z => (zs z).card) (fun z => (hz z).card_pos) zs zs hz
    (fun _ => subset_rfl) (fun _ => subset_rfl) (fun _ => le_rfl) hloc hmeet hβd hτd hβm hτm hτi
    hB hzd hG3 hK0g hent hK1 (fun b v => by simpa using hcount b v) hh
    (by simpa using mul_exp_neg_le_seventh hp hc1) hG1 hK0P hκ' hcP
    (fun X => (mul_le_of_le_one_left (Nat.cast_nonneg _) (hA.trans hα)).trans (hG1 X))
    hG2P hG3P hκ
  refine ⟨h1, fun b => (h2 b).trans ?_, h3.trans ?_⟩
  · exact mul_le_mul_of_nonneg_right hA (Real.exp_pos _).le
  · exact mul_le_mul_of_nonneg_left hA (Nat.cast_nonneg _)

end Bound

end Balaban.Polymer
