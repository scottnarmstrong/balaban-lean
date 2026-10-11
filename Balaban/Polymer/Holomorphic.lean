module

public import Balaban.Polymer.Local
public import Balaban.Analysis.AnalyticLimit

/-!
# Holomorphy of the cluster sum in several parameters

PE (d).  Let `E` be a complex normed space (finite-dimensional in all applications), `U ⊆ E` open,
and let the activities `K Y : E → ℂ` be analytic on `U` with the uniform bound `‖K Y u‖ ≤ κ Y`.
Then `logSeries` and every local term `PY Y` are analytic on `U`
(`pe_analyticOnNhd`, `pe_PY_analyticOnNhd`); the proof is Weierstrass' theorem
`Balaban.Analysis.analyticOnNhd_of_tendstoUniformlyOn` applied to the partial sums.  The Cauchy
estimates for derivatives follow (`pe_norm_fderiv_logSeries_le`, `pe_norm_fderiv_PY_le`).
-/

@[expose] public section

noncomputable section

open scoped Classical

open Finset Filter

namespace Balaban.Polymer

section Series

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- A series of analytic functions with a summable uniform bound is analytic. -/
theorem analyticOnNhd_tsum_of_summable {f : ℕ → E → ℂ} {b : ℕ → ℝ} {U : Set E}
    (hU : IsOpen U) (hf : ∀ n, AnalyticOnNhd ℂ (f n) U) (hb : Summable b)
    (hfb : ∀ n, ∀ u ∈ U, ‖f n u‖ ≤ b n) : AnalyticOnNhd ℂ (fun u => ∑' n, f n u) U := by
  have hu : TendstoUniformlyOn (fun (t : Finset ℕ) u => ∑ n ∈ t, f n u)
      (fun u => ∑' n, f n u) atTop U := tendstoUniformlyOn_tsum hb hfb
  have hu' : TendstoUniformlyOn (fun (N : ℕ) u => ∑ n ∈ Finset.range N, f n u)
      (fun u => ∑' n, f n u) atTop U := fun V hV => tendsto_finset_range.eventually (hu V hV)
  refine Balaban.Analysis.analyticOnNhd_of_tendstoUniformlyOn (M := ∑' n, b n) hU
    (fun N => ?_) (fun N u hu => ?_) hu'
  · exact Finset.analyticOnNhd_fun_sum _ (fun n _ => hf n)
  · refine (norm_sum_le _ _).trans ?_
    exact (Finset.sum_le_sum (fun n _ => hfb n u hu)).trans
      (hb.sum_le_tsum _ (fun n _ => (norm_nonneg _).trans (hfb n u hu)))

end Series

variable {P : Type*} [Fintype P] (inc : P → P → Prop) {κ a : P → ℝ}
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem analyticOnNhd_clTerm {U : Set E} (K : P → E → ℂ) (hK : ∀ Y, AnalyticOnNhd ℂ (K Y) U)
    (n : ℕ) : AnalyticOnNhd ℂ (fun u => clTerm inc (fun Y => K Y u) n) U := by
  unfold clTerm
  refine AnalyticOnNhd.mul (analyticOnNhd_const (𝕜 := ℂ)) ?_
  refine Finset.analyticOnNhd_fun_sum _ (fun X _ => ?_)
  exact AnalyticOnNhd.mul (analyticOnNhd_const (𝕜 := ℂ))
    (Finset.analyticOnNhd_fun_prod _ (fun i _ => hK _))

/-- Holomorphy of the cluster sum in several complex parameters. -/
theorem pe_analyticOnNhd (h : KPCond inc κ a) {U : Set E} (hU : IsOpen U) (K : P → E → ℂ)
    (hK : ∀ Y, AnalyticOnNhd ℂ (K Y) U) (hb : ∀ Y u, u ∈ U → ‖K Y u‖ ≤ κ Y) :
    AnalyticOnNhd ℂ (fun u => logSeries inc (fun Y => K Y u)) U :=
  analyticOnNhd_tsum_of_summable hU (analyticOnNhd_clTerm inc K hK)
    (summable_sp inc h (fun _ => True))
    (fun n u hu => norm_clTerm_le inc κ _ (fun Y => hb Y u hu) n)

variable {B : Type*} (supp : P → Finset B)

theorem analyticOnNhd_Pterm {U : Set E} (K : P → E → ℂ) (hK : ∀ Y, AnalyticOnNhd ℂ (K Y) U)
    (Y : Finset B) (n : ℕ) :
    AnalyticOnNhd ℂ (fun u => Pterm inc supp (fun Z => K Z u) Y n) U := by
  unfold Pterm
  refine AnalyticOnNhd.mul (analyticOnNhd_const (𝕜 := ℂ)) ?_
  refine Finset.analyticOnNhd_fun_sum _ (fun X _ => ?_)
  exact AnalyticOnNhd.mul (analyticOnNhd_const (𝕜 := ℂ))
    (Finset.analyticOnNhd_fun_prod _ (fun i _ => hK _))

/-- Holomorphy of each local term `P(Y)` in several complex parameters. -/
theorem pe_PY_analyticOnNhd (h : KPCond inc κ a) {U : Set E} (hU : IsOpen U) (K : P → E → ℂ)
    (hK : ∀ Y, AnalyticOnNhd ℂ (K Y) U) (hb : ∀ Y u, u ∈ U → ‖K Y u‖ ≤ κ Y) (Y : Finset B) :
    AnalyticOnNhd ℂ (fun u => PY inc supp (fun Z => K Z u) Y) U :=
  analyticOnNhd_tsum_of_summable hU (analyticOnNhd_Pterm inc supp K hK Y)
    (summable_sp inc h (fun _ => True))
    (fun n u hu => norm_Pterm_le inc supp _ (fun Z => hb Z u hu) Y n)

/-- Uniform bound on the local terms. -/
theorem norm_PY_le (h : KPCond inc κ a) (K : P → ℂ) (hK : ∀ x, ‖K x‖ ≤ κ x) (Y : Finset B) :
    ‖PY inc supp K Y‖ ≤ ∑' n, sp inc κ (fun _ => True) n :=
  (norm_tsum_le_tsum_norm (Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
      (norm_Pterm_le inc supp K hK Y) (summable_sp inc h (fun _ => True)))).trans
    ((Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
      (norm_Pterm_le inc supp K hK Y) (summable_sp inc h (fun _ => True))).tsum_le_tsum
      (norm_Pterm_le inc supp K hK Y) (summable_sp inc h (fun _ => True)))

/-- Uniform bound on the cluster sum. -/
theorem norm_logSeries_le_tsum (h : KPCond inc κ a) (K : P → ℂ) (hK : ∀ x, ‖K x‖ ≤ κ x) :
    ‖logSeries inc K‖ ≤ ∑' n, sp inc κ (fun _ => True) n :=
  (norm_tsum_le_tsum_norm (pe_summable inc h K hK)).trans
    ((pe_summable inc h K hK).tsum_le_tsum (norm_clTerm_le inc κ K hK)
      (summable_sp inc h (fun _ => True)))

section Cauchy

variable {u₀ : E} {R : ℝ}

/-- Cauchy estimate for the derivative of the cluster sum on a ball in the parameter space. -/
theorem pe_norm_fderiv_logSeries_le (h : KPCond inc κ a) (hR : 0 < R) (K : P → E → ℂ)
    (hK : ∀ Y, AnalyticOnNhd ℂ (K Y) (Metric.ball u₀ R))
    (hb : ∀ Y u, u ∈ Metric.ball u₀ R → ‖K Y u‖ ≤ κ Y) :
    ‖fderiv ℂ (fun u => logSeries inc (fun Y => K Y u)) u₀‖ ≤
      (∑' n, sp inc κ (fun _ => True) n) / R := by
  have := Balaban.Analysis.norm_fderiv_le_of_ball
    (pe_analyticOnNhd inc h Metric.isOpen_ball K hK hb).differentiableOn
    (fun u hu => norm_logSeries_le_tsum inc h _ (fun Y => hb Y u hu)) (Metric.mem_ball_self hR)
  simpa using this

/-- Cauchy estimate for the derivative of a local term. -/
theorem pe_norm_fderiv_PY_le (h : KPCond inc κ a) (hR : 0 < R) (K : P → E → ℂ)
    (hK : ∀ Y, AnalyticOnNhd ℂ (K Y) (Metric.ball u₀ R))
    (hb : ∀ Y u, u ∈ Metric.ball u₀ R → ‖K Y u‖ ≤ κ Y) (Y : Finset B) :
    ‖fderiv ℂ (fun u => PY inc supp (fun Z => K Z u) Y) u₀‖ ≤
      (∑' n, sp inc κ (fun _ => True) n) / R := by
  have := Balaban.Analysis.norm_fderiv_le_of_ball
    (pe_PY_analyticOnNhd inc supp h Metric.isOpen_ball K hK hb Y).differentiableOn
    (fun u hu => norm_PY_le inc supp h _ (fun Z => hb Z u hu) Y) (Metric.mem_ball_self hR)
  simpa using this

end Cauchy

end Balaban.Polymer
