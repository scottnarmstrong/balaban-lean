module

public import Balaban.Polymer.Expansion

/-!
# The abstract polymer-expansion theorem (finite case)

Setting: a finite type `P` of polymers with a symmetric reflexive incompatibility relation
`inc`, activities `K : P → ℂ`.  `Xi inc K` is the sum over pairwise compatible families of the
products of activities, `clTerm inc K n` the cluster term of order `n+1` with the Ursell
function `φ^T` (signed count of connected spanning subgraphs of the incompatibility graph of the
cluster), and `logSeries inc K = ∑ₙ clTerm inc K n`.

Kotecký–Preiss hypothesis `KPCond inc κ a`: `κ ≥ 0` dominates `‖K‖`, and for every polymer `Y`
`∑_{Y' incompatible with Y} κ Y' e^{a Y'} ≤ a Y`.

Main results:
* `pe_clusterBound`: for every set `R` of polymers,
  `∑_{n} (n+1)!⁻¹ ∑_{X ∈ P^{n+1}, ∃ i, R (X i)} |φ^T(X)| ∏ κ(X i) ≤ ∑_{Y ∈ R} κ Y e^{a Y}`;
* `pe_summable`: absolute convergence of the cluster sum;
* `pe_xi_eq_exp`: `Xi inc K = exp (logSeries inc K)`;
* `pe_logSeries_bound`: with test objects, `‖logSeries‖ ≤ ∑ₜ a(t)` and the two-sided bound on
  `‖Xi‖`.
-/

@[expose] public section

noncomputable section

open scoped Classical

open Finset

namespace Balaban.Polymer

variable {P : Type*} [Fintype P] (inc : P → P → Prop) {κ a : P → ℝ}

/-- Absolute convergence of the cluster sum, with the sum of the absolute values bounded. -/
theorem pe_clusterBound (h : KPCond inc κ a) (R : P → Prop) :
    Summable (sp inc κ R) ∧
      ∑' n, sp inc κ R n ≤ ∑ Y, (if R Y then κ Y * Real.exp (a Y) else 0) :=
  ⟨summable_sp inc h R, (summable_sp inc h R).tsum_le_of_sum_range_le
    (fun M => sp_sum_le inc κ h.nonneg a h.bound R M)⟩

theorem pe_summable (h : KPCond inc κ a) (K : P → ℂ) (hK : ∀ x, ‖K x‖ ≤ κ x) :
    Summable (fun n => ‖clTerm inc K n‖) :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (norm_clTerm_le inc κ K hK)
    (summable_sp inc h (fun _ => True))

/-- `Ξ = exp L`. -/
theorem pe_xi_eq_exp (h : KPCond inc κ a) (hrefl : ∀ x, inc x x) (K : P → ℂ)
    (hK : ∀ x, ‖K x‖ ≤ κ x) : Xi inc K = Complex.exp (logSeries inc K) :=
  xi_eq_exp_aux inc h hrefl _ K hK rfl

section Tests

variable {τ : Type*} [Fintype τ] (rel : τ → P → Prop) (hcover : ∀ Y, ∃ t, rel t Y)

include hcover in
theorem sp_true_le (hκ : ∀ x, 0 ≤ κ x) (n : ℕ) :
    sp inc κ (fun _ => True) n ≤ ∑ t, sp inc κ (rel t) n := by
  unfold sp
  rw [← Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  rw [Finset.sum_comm]
  refine Finset.sum_le_sum (fun X _ => ?_)
  have hF : 0 ≤ aaw inc X * ∏ i, κ (X i) :=
    mul_nonneg (aaw_nonneg inc X) (Finset.prod_nonneg (fun i _ => hκ _))
  have hex : (∃ i : Fin (n + 1), True) := ⟨0, trivial⟩
  simp only [hex, ite_true, one_mul]
  have h1 : (1 : ℝ) ≤ ∑ t, (if ∃ i, rel t (X i) then (1 : ℝ) else 0) := by
    obtain ⟨t, ht⟩ := hcover (X 0)
    calc (1 : ℝ) = (if ∃ i, rel t (X i) then (1 : ℝ) else 0) := by simp [show (∃ i, rel t (X i)) from ⟨0, ht⟩]
      _ ≤ _ := Finset.single_le_sum (f := fun t => (if ∃ i, rel t (X i) then (1 : ℝ) else 0))
          (fun _ _ => by split_ifs <;> norm_num) (Finset.mem_univ t)
  calc aaw inc X * ∏ i, κ (X i) = 1 * (aaw inc X * ∏ i, κ (X i)) := by ring
    _ ≤ (∑ t, (if ∃ i, rel t (X i) then (1 : ℝ) else 0)) * (aaw inc X * ∏ i, κ (X i)) :=
        mul_le_mul_of_nonneg_right h1 hF
    _ = _ := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl (fun t _ => ?_)
        ring

include hcover in
/-- The cluster sum is bounded by the sum of the test weights. -/
theorem pe_logSeries_bound (h : KPCond inc κ a) (K : P → ℂ) (hK : ∀ x, ‖K x‖ ≤ κ x)
    (w : τ → ℝ)
    (hw : ∀ t, ∑ Y, (if rel t Y then κ Y * Real.exp (a Y) else 0) ≤ w t) :
    ‖logSeries inc K‖ ≤ ∑ t, w t := by
  have hs := pe_summable inc h K hK
  have h1 : ‖logSeries inc K‖ ≤ ∑' n, ‖clTerm inc K n‖ := norm_tsum_le_tsum_norm hs
  have h2 : ∑' n, ‖clTerm inc K n‖ ≤ ∑' n, sp inc κ (fun _ => True) n :=
    hs.tsum_le_tsum (norm_clTerm_le inc κ K hK) (summable_sp inc h _)
  have h3 : ∑' n, sp inc κ (fun _ => True) n ≤ ∑' n, ∑ t, sp inc κ (rel t) n :=
    (summable_sp inc h _).tsum_le_tsum (sp_true_le inc rel hcover h.nonneg)
      (summable_sum (fun t _ => summable_sp inc h (rel t)))
  have h4 : ∑' n, ∑ t, sp inc κ (rel t) n = ∑ t, ∑' n, sp inc κ (rel t) n :=
    Summable.tsum_finsetSum (fun t _ => summable_sp inc h (rel t))
  have h5 : ∑ t, ∑' n, sp inc κ (rel t) n ≤ ∑ t, w t :=
    Finset.sum_le_sum (fun t _ => ((pe_clusterBound inc h (rel t)).2).trans (hw t))
  linarith

include hcover in
theorem pe_xi_norm_bounds (h : KPCond inc κ a) (hrefl : ∀ x, inc x x) (K : P → ℂ)
    (hK : ∀ x, ‖K x‖ ≤ κ x) (w : τ → ℝ)
    (hw : ∀ t, ∑ Y, (if rel t Y then κ Y * Real.exp (a Y) else 0) ≤ w t) :
    Real.exp (-∑ t, w t) ≤ ‖Xi inc K‖ ∧ ‖Xi inc K‖ ≤ Real.exp (∑ t, w t) := by
  have hL := pe_logSeries_bound inc rel hcover h K hK w hw
  rw [pe_xi_eq_exp inc h hrefl K hK, Complex.norm_exp]
  have hre := Complex.abs_re_le_norm (logSeries inc K)
  constructor
  · exact Real.exp_le_exp.mpr (by linarith [(abs_le.mp hre).1])
  · exact Real.exp_le_exp.mpr (by linarith [(abs_le.mp hre).2])

end Tests

end Balaban.Polymer
