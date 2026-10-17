module

public import Balaban.LargeField.Base.BaseFirstLocalCode
public import Balaban.LargeField.Counter.LF2
public import Balaban.LargeField.Counter.CaseNew
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Volume and budget of a first large-field component

The spine containment includes the hull closure. At the first step all old parts are empty,
so the spine length is paid for by the number of new cubes in the component.
-/

@[expose] public section

namespace Balaban.LargeField

open Balaban

namespace RegionHistory

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K : ℕ}
  (H : RegionHistory S n R k0 K)

/-- Lemma V and the first-step spine rule bound the whole hull component by its new seeds. -/
theorem baseFirst_component_volume (ok : S.Ok) (hK0 : 0 < K) (Z' : H.Comp 1) :
    (Z'.1.card : ℝ) ≤ ((Z'.1 ∩ H.newCubes 1).card : ℝ) *
      (S.CV * (S.rho 1 : ℝ) ^ (S.d - 1) * (S.D 1 + S.rho 1)) := by
  have hs := (H.spineOK_spine hK0 Z').2.1
  simp only [H.base_parts_empty Z', Finset.sum_empty, Finset.card_empty, zero_add] at hs
  have hv := lemmaV (H.spine 1 Z') ok.one_le_d (ok.two_le_rho 1) Z'.1
    (H.spine_contains 1 (by omega) Z')
  have hD := S.D_nonneg 1
  have hρ : (0 : ℝ) ≤ S.rho 1 := (by norm_num : (0 : ℝ) ≤ 2).trans (ok.two_le_rho 1)
  have hCV : 0 ≤ S.CV := (by norm_num : (0 : ℝ) ≤ 1).trans S.CV_ge
  have hC : 0 ≤ S.CV * (S.rho 1 : ℝ) ^ (S.d - 1) := by positivity
  have hn : 1 ≤ ((Z'.1 ∩ H.newCubes 1).card : ℝ) := by
    exact_mod_cast H.base_newCube hK0 Z'
  have hcv : S.CV = 2 * 14 ^ S.d := rfl
  rw [← hcv] at hv
  nlinarith [mul_nonneg hC hD, mul_nonneg hC hρ]

/-- The high-power level-zero gain pays the first component volume and the scale-one clock. -/
theorem baseFirst_budget_ge_tau {P : BudgetConsts} (B : BudgetSetup S P) (G : S.Good)
    (hK0 : 0 < K) (κ logC : ∀ k, H.Comp k → ℝ) (Z' : H.Comp 1) :
    S.tau 1 ≤ H.Gpre P κ logC 1 Z' := by
  let m : ℝ := ((Z'.1 ∩ H.newCubes 1).card : ℝ)
  have hm : 1 ≤ m := by
    change (1 : ℝ) ≤ ((Z'.1 ∩ H.newCubes 1).card : ℝ)
    exact_mod_cast H.base_newCube hK0 Z'
  have hvol := H.baseFirst_component_volume G.ok hK0 Z'
  have hcost : S.cv * S.lam 1 * (Z'.1.card : ℝ) ≤ m * (S.v 1 * S.D 1 + S.w 1) := by
    have hc : 0 ≤ S.cv * S.lam 1 := by
      have := G.ok.one_le_cv
      have := G.ok.lam_pos 1
      positivity
    have hh := mul_le_mul_of_nonneg_left hvol hc
    have heq : m * (S.v 1 * S.D 1 + S.w 1) =
        S.cv * S.lam 1 * (m * (S.CV * (S.rho 1 : ℝ) ^ (S.d - 1) *
          (S.D 1 + S.rho 1))) := by
      dsimp [m, Setting.w, Setting.v]
      ring
    rw [heq]
    exact hh
  have hE : S.v 1 * S.D 1 ≤ S.E 1 := by
    have hs := G.ok.v_add_two_sigma_D_le 1
    have hσ := G.ok.sigma_nonneg 1
    have hD := S.D_nonneg 1
    nlinarith
  have hΦ : S.tau 1 + S.w 1 ≤ S.Phi (S.lam 1) := by
    have hr := G.ok.restart_bounds (μ := 1) (s' := 1) (Λ' := 0)
      (by omega) (by norm_num)
    have hmax : max (S.lam 1) (0 : ℝ) = S.lam 1 := max_eq_left (G.ok.lam_pos 1).le
    rw [hmax] at hr
    have ht := G.ok.tau_mono (show 1 ≤ 1 + S.nq 1 by omega)
    have hw := G.ok.W_mono_right 1 (show 1 ≤ 1 + S.nq 1 by omega)
    have hW : S.W 1 1 = S.w 1 := by simp [Setting.W]
    rw [hW] at hw
    linarith [hr.2.2]
  have hg := G.E_Phi_le_g 0
  have hbudget := (H.base_budget B G.ok hK0 κ logC Z').2
  have hτ := G.ok.tau_nonneg 1
  have hgain : S.tau 1 + S.v 1 * S.D 1 + S.w 1 + 1 ≤ S.g 0 := by linarith
  have hfactor : S.tau 1 ≤ m * (S.tau 1 + 1) := by nlinarith
  dsimp [m] at hcost hfactor ⊢
  nlinarith [mul_nonneg (sub_nonneg.mpr hgain) (sub_nonneg.mpr hm)]

/-- The first component retains two copies of the running `p₂(β₁)` threshold. -/
theorem baseFirst_budget_ge_two_p2Run {P : BudgetConsts} (B : BudgetSetup S P)
    (G : S.Good) (hβ1 : 1 ≤ P.beta 1) (hK0 : 0 < K)
    (κ logC : ∀ k, H.Comp k → ℝ) (Z' : H.Comp 1) :
    2 * p2Run S.A2 S.p2 P.beta 1 ≤ H.Gpre P κ logC 1 Z' := by
  have hlog : 0 ≤ Real.log (P.beta 1) := Real.log_nonneg hβ1
  have hle : Real.log (P.beta 1) ≤ S.lam 1 := by
    rw [B.lam_eq]
    exact B.run.logBeta_le 1
  have hp : p2Run S.A2 S.p2 P.beta 1 ≤ S.A2 * S.lam 1 ^ S.p2 := by
    unfold p2Run
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hlog hle _) G.ok.A2_pos.le
  have hτ := H.baseFirst_budget_ge_tau B G hK0 κ logC Z'
  unfold Setting.tau at hτ
  linarith

/-- Hence either reserve multiplicity used at the first step is available. -/
theorem baseFirst_budget_ge_p2Run {P : BudgetConsts} (B : BudgetSetup S P)
    (G : S.Good) (hβ1 : 1 ≤ P.beta 1) (hK0 : 0 < K)
    (κ logC : ∀ k, H.Comp k → ℝ) (Z' : H.Comp 1)
    (ell : ℕ) (hell : ell ≤ 2) :
    (ell : ℝ) * p2Run S.A2 S.p2 P.beta 1 ≤ H.Gpre P κ logC 1 Z' := by
  have hp : 0 ≤ p2Run S.A2 S.p2 P.beta 1 := by
    unfold p2Run
    have := G.ok.A2_pos
    have := Real.log_nonneg hβ1
    positivity
  have he : (ell : ℝ) ≤ 2 := by exact_mod_cast hell
  exact (mul_le_mul_of_nonneg_right he hp).trans
    (H.baseFirst_budget_ge_two_p2Run B G hβ1 hK0 κ logC Z')

end RegionHistory

end Balaban.LargeField
