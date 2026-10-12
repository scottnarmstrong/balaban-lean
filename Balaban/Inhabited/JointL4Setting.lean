/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.History.InhabitedJoint
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The parameters of the `L = 4` joint witness

`d = 3`, `L = M = 4`, `R_base = 36 = 4L + 20`, `θ_± = log 4 = (d-2) log L`, `c_v = 320 = M^d (H₀+c₁+3)`
with `H₀ = 2`, `c₁ = c₂ = 0`, `λ_j = log (5β/4) + 1 + j log 4`, the flow `β_k = β 4^k`, `ν_k = 16^k/20`
(`γ = δ = 1`).  Here `L = 4` is the least value with `3 ≤ L` (`BgHyp`) and `4 ≤ L`
(`IsAdmDelta`); `M = L` is the least `M` with `L ≤ M`; the radii are those of
`Balaban.Inhabited.radiusHyp_nonempty` / `stepRadii_nonempty` (`4L + 20`).
-/

@[expose] public section

namespace Balaban.Inhabited
namespace JointL4

open Balaban Balaban.LargeField Balaban.LargeField.JointWitness

theorem log_four_pos : 0 < Real.log 4 := Real.log_pos (by norm_num)

theorem log_four_lt_two : Real.log 4 < 2 := by
  have h : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  have := Real.log_two_lt_d9; linarith

theorem log_four_gt : 1 < Real.log 4 := by
  have h : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  have := Real.log_two_gt_d9; linarith

/-- The typing of the `L = 4` witness. -/
noncomputable def typing0 : Typing where
  d := 3
  L := 4
  M := 4
  Rb := 36
  θp := Real.log 4
  θm := Real.log 4
  α := 1
  p0 := 5
  p2 := 9
  pR := 16
  A2 := 1
  A3 := 1
  A3' := 1
  CR := 0
  Cν := 0
  cv := 320
  cH := 3 * Real.log 4
  sS := 4
  sP := 5
  c0 := 10

noncomputable def typing : Typing := { typing0 with Cν := typing0.Cr }

theorem typing_ok : typing.Ok where
  three_le_d := le_refl _
  two_le_L := by show 2 ≤ 4; norm_num
  one_le_M := by show 1 ≤ 4; norm_num
  two_le_Rb := by show (2 : ℝ) ≤ 36; norm_num
  θm_pos := log_four_pos
  θm_le_θp := le_refl _
  α_pos := by show (0 : ℝ) < 1; norm_num
  A2_pos := by show (0 : ℝ) < 1; norm_num
  A3_pos := by show (0 : ℝ) < 1; norm_num
  A3'_pos := by show (0 : ℝ) < 1; norm_num
  CR_nonneg := le_refl _
  Cν_pos := by
    show 0 < typing0.Cr
    have hl : 0 < typing0.logL := Real.log_pos (by show (1 : ℝ) < ((4 : ℕ) : ℝ); norm_num)
    have h1 : 0 ≤ typing0.cStar := by
      unfold Typing.cStar
      have : (0 : ℝ) ≤ typing0.θp / (typing0.α * typing0.logL) :=
        div_nonneg log_four_pos.le (mul_nonneg (by show (0 : ℝ) ≤ 1; norm_num) hl.le)
      linarith
    have h2 : 0 ≤ typing0.cPrime := by
      unfold Typing.cPrime
      exact mul_nonneg h1 (by have := log_four_pos; show (0 : ℝ) ≤ 1 + 3 * Real.log 4; linarith)
    unfold Typing.Cr
    have : (0 : ℝ) ≤ 2 * typing0.A2 * typing0.cPrime ^ typing0.p2 :=
      mul_nonneg (by show (0 : ℝ) ≤ 2 * 1; norm_num) (pow_nonneg h2 _)
    linarith
  one_le_cv := by show (1 : ℝ) ≤ 320; norm_num
  cH_nonneg := by have := log_four_pos; show (0 : ℝ) ≤ 3 * Real.log 4; linarith
  p2_ge := by decide
  pR_gt := by decide
  p0_gt := by decide
  c0_sS := by show ((4 : ℕ) : ℝ) + 1 ≤ ((10 : ℕ) : ℝ) * (1 - 1 / ((4 : ℕ) : ℝ)); norm_num
  c0_sP := by decide
  Cr_le := le_refl _

/-- The setting `λ_j = log (5β/4) + 1 + j log 4`. -/
noncomputable def setting (β : ℝ) : Setting where
  toTyping := typing
  lam := fun j => Real.log (β * (5 / 4)) + 1 + (j : ℝ) * Real.log 4

theorem setting_lam (β : ℝ) (j : ℕ) :
    (setting β).lam j = Real.log (β * (5 / 4)) + 1 + (j : ℝ) * Real.log 4 := rfl

theorem log_ge_four (β : ℝ) (hβ : 20 < β) : Real.log 4 ≤ Real.log (β * (5 / 4)) :=
  Real.log_le_log (by norm_num) (by linarith)

theorem setting_ok (β : ℝ) (hβ : 20 < β) : (setting β).Ok where
  toOk := typing_ok
  lam_step := fun j => by
    show Real.log 4 ≤ (setting β).lam (j + 1) - (setting β).lam j ∧
      (setting β).lam (j + 1) - (setting β).lam j ≤ Real.log 4
    rw [setting_lam, setting_lam]
    push_cast; constructor <;> linarith
  one_le_lam0 := by
    have := log_ge_four β hβ; have := log_four_pos
    show (1 : ℝ) ≤ Real.log (β * (5 / 4)) + 1 + ((0 : ℕ) : ℝ) * Real.log 4
    simp; linarith
  θp_le_lam0 := by
    have := log_ge_four β hβ; have := log_four_pos
    show Real.log 4 ≤ Real.log (β * (5 / 4)) + 1 + ((0 : ℕ) : ℝ) * Real.log 4
    simp; linarith

/-- The threshold `x₀` of `exists_lamStar` for the typing. -/
noncomputable def lamStar : ℝ := (exists_lamStar typing typing_ok).choose

theorem lamStar_spec : LamStarConditions typing lamStar :=
  (exists_lamStar typing typing_ok).choose_spec

theorem setting_good (β : ℝ) (hβ : 20 < β) (hx : lamStar ≤ Real.log (β * (5 / 4)) + 1) :
    (setting β).Good where
  ok := setting_ok β hβ
  lc := LamStarConditions.mono lamStar_spec (by
    show lamStar ≤ Real.log (β * (5 / 4)) + 1 + ((0 : ℕ) : ℝ) * Real.log 4
    simp; exact hx)

/-! ### The analytic constants -/

def anaK : AnalyticConsts where
  d := 3
  L := 4
  N := 2
  p0 := 5
  A0 := 0
  H0 := 2
  c2 := 0
  c1BG := 1
  c11 := 1
  C3 := 1
  C4 := 1
  deltaSS := 1
  deltaS := 1

noncomputable def anaThreshold : ℝ := max (3 / (1 - (2 : ℝ) ^ (-(1 / (2 * (5 : ℝ)))))) 4

theorem anaK_at {x : ℝ} (hx : anaThreshold ≤ x) : AnalyticLamAt anaK x := by
  have h1 : 3 / (1 - (2 : ℝ) ^ (-(1 / (2 * (5 : ℝ))))) ≤ x := (le_max_left _ _).trans hx
  have h2 : (4 : ℝ) ≤ x := (le_max_right _ _).trans hx
  have hl := log_four_lt_two
  have hl0 := log_four_pos
  have hd : deltaBar anaK.A0 anaK.p0 x = 0 := by simp [deltaBar, anaK]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [anaK] using h1
  · simp only [anaK, thetaOf]
    norm_num
    nlinarith
  · simp only [anaK]; linarith
  · rw [hd]; simp [anaK]
  · rw [hd]; simp [anaK]
  · rw [hd]; simp [anaK]

/-! ### The flow -/

/-- The flow data: `ν = 1/20 < 7/128 = (7/8) L⁻²` so that `k_f ≥ 1`, and `β ν > 1`. -/
noncomputable def flow (β : ℝ) (hβ : 20 < β) : FlowSeq where
  d := 3
  L := 4
  β := β
  ν := 1 / 20
  a := 5 / 4
  γ := fun _ => 1
  δ := fun _ => 1
  hd := le_rfl
  hL := by norm_num
  hβ := by linarith
  hν0 := by norm_num
  hν1 := by norm_num
  ha1 := by norm_num
  ha2 := by norm_num
  hγ := fun _ => by norm_num
  hδ := fun _ => by norm_num
  hγ0 := rfl
  hδ0 := rfl

theorem flow_matches (β : ℝ) (hβ : 20 < β) : (flow β hβ).Matches (setting β) where
  d_eq := rfl
  L_eq := rfl
  lam_eq := fun j => by
    rw [setting_lam]
    simp [FlowSeq.lamHat, flow, FlowSeq.e]
  cH_eq := by
    show 3 * Real.log 4 = ((3 : ℕ) + 3 : ℝ) * (((3 : ℕ) - 2 : ℕ) : ℝ) / 2 * Real.log ((4 : ℕ) : ℝ)
    norm_num

theorem flow_beta_nu_zero (β : ℝ) (hβ : 20 < β) :
    (flow β hβ).beta 0 * (flow β hβ).nu 0 = β / 20 := by
  simp [FlowSeq.beta, FlowSeq.nu, flow]; ring

theorem flow_not_le (β : ℝ) (hβ : 20 < β) (k : ℕ) :
    ¬ (flow β hβ).beta k * (flow β hβ).nu k ≤ 1 := by
  intro h
  have h1 := (flow β hβ).betanu_mono (Nat.zero_le k)
  rw [flow_beta_nu_zero] at h1
  linarith

/-- For `β > 20` the regime index is `k₀ = 0`. -/
theorem flow_k0 (β : ℝ) (hβ : 20 < β) : (flow β hβ).k0 = 0 := by
  rcases (flow β hβ).k0_cases with h | h
  · exact absurd h.1 (flow_not_le β hβ _)
  · exact h.2

theorem flow_one_le_kf (β : ℝ) (hβ : 20 < β) : 1 ≤ (flow β hβ).kf := by
  by_contra h
  have h0 : (flow β hβ).kf = 0 := by omega
  have hk := (flow β hβ).kf_spec
  rw [h0] at hk
  have : (flow β hβ).nu 0 = 1 / 20 := by simp [FlowSeq.nu, flow]
  rw [this] at hk
  have h2 : ((flow β hβ).L : ℝ) = 4 := by simp [flow]
  rw [h2] at hk
  norm_num at hk

theorem flow_hgen (β : ℝ) (hβ : 20 < β) :
    (flow β hβ).beta (flow β hβ).k0 * (flow β hβ).nu (flow β hβ).k0 ≤ 1 →
      2 * ((flow β hβ).L : ℝ) ^ 2 ≤ (flow β hβ).beta (flow β hβ).k0 :=
  fun h => absurd h (flow_not_le β hβ _)

theorem flow_hΛ12 (β : ℝ) (hβ : 20 < β) (h12 : 12 ≤ Real.log (β * (5 / 4)) + 1) :
    (((flow β hβ).d : ℝ) + 3) / 2 ≤
      (setting β).lam (flow β hβ).k0 * (1 - 1 / (2 * Real.log (flow β hβ).L)) := by
  have hlam : 12 ≤ (setting β).lam (flow β hβ).k0 := by
    rw [setting_lam]
    have := log_four_pos
    have : (0 : ℝ) ≤ ((flow β hβ).k0 : ℝ) * Real.log 4 := by positivity
    linarith
  have hd : (((flow β hβ).d : ℝ) + 3) / 2 = 3 := by simp [flow]
  have hL : Real.log ((flow β hβ).L : ℝ) = Real.log 4 := by simp [flow]
  rw [hd, hL]
  have h6 := log_four_gt
  have hc : 1 / 4 ≤ 1 - 1 / (2 * Real.log 4) := by
    have : 1 / (2 * Real.log 4) ≤ 3 / 4 := by
      rw [div_le_iff₀ (by positivity)]; nlinarith
    linarith
  nlinarith

/-! ### The budget -/

noncomputable def budgetConsts (β : ℝ) : BudgetConsts where
  c1 := 0
  c2 := 0
  H0 := 2
  beta := fun k => β * 4 ^ k

noncomputable def budgetSetup (β : ℝ) (hβ : 20 < β)
    (ha : anaThreshold ≤ Real.log (β * (5 / 4)) + 1) :
    BudgetSetup (setting β) (budgetConsts β) where
  β := β
  ν := 1 / 20
  a := 5 / 4
  ε := 0
  nuRun := fun k => 1 / 20 * 16 ^ k
  K := anaK
  run :=
    { hd := by show 2 ≤ 3; norm_num
      hL := by show 2 ≤ 4; norm_num
      hβ := by linarith
      hν := by norm_num
      ha1 := by norm_num
      ha2 := by norm_num
      hε0 := le_rfl
      hε := by norm_num
      beta_eq := fun k => ⟨1, one_pos, by simp, by
        show β * 4 ^ k = β * ((4 : ℕ) : ℝ) ^ (k * (3 - 2)) * 1
        simp⟩
      nu_eq := fun k => ⟨1, one_pos, by simp, by
        show 1 / 20 * 16 ^ k = 1 / 20 * ((4 : ℕ) : ℝ) ^ (2 * k) * 1
        rw [pow_mul]; norm_num⟩ }
  lam_eq := fun j => by
    rw [setting_lam]
    simp [lamHat, thetaOf, setting, typing, typing0]
  Kd := rfl
  KL := rfl
  Kp0 := rfl
  KH0 := rfl
  Kc2 := rfl
  lam_cond := fun j => anaK_at (by
    rw [setting_lam]
    have := log_four_pos
    have : (0 : ℝ) ≤ (j : ℝ) * Real.log 4 := by positivity
    linarith)
  H0_nonneg := by show (0 : ℝ) ≤ 2; norm_num
  c1_nonneg := le_rfl
  L_le_M := by show 4 ≤ 4; exact le_rfl
  cv_ge := by
    show ((4 : ℕ) : ℝ) ^ 3 * (2 + 0 + 3) ≤ 320
    norm_num

instance (β : ℝ) : NeZero (setting β).L := ⟨by show (4 : ℕ) ≠ 0; norm_num⟩

theorem setting_s4 (β : ℝ) : 4 ≤ (setting β).sS := le_refl _
theorem setting_s5 (β : ℝ) : 5 ≤ (setting β).sP := le_refl _
theorem setting_Rb (β : ℝ) : (4 * (setting β).L + 20 : ℝ) ≤ (setting β).Rb := by
  show (4 * ((4 : ℕ) : ℝ) + 20) ≤ 36; norm_num

theorem exists_beta : ∃ β : ℝ, 20 < β ∧ lamStar ≤ Real.log (β * (5 / 4)) + 1 ∧
    anaThreshold ≤ Real.log (β * (5 / 4)) + 1 ∧ 12 ≤ Real.log (β * (5 / 4)) + 1 := by
  set Λ : ℝ := max (max lamStar anaThreshold) 30 with hΛ
  have h1 : lamStar ≤ Λ := (le_max_left _ _).trans (le_max_left _ _)
  have h2 : anaThreshold ≤ Λ := (le_max_right _ _).trans (le_max_left _ _)
  have h3 : 30 ≤ Λ := le_max_right _ _
  have hl : Real.log (Real.exp Λ * (5 / 4)) = Λ + Real.log (5 / 4) := by
    rw [Real.log_mul (Real.exp_pos _).ne' (by norm_num), Real.log_exp]
  have hp : 0 < Real.log (5 / 4 : ℝ) := Real.log_pos (by norm_num)
  have he : Λ + 1 ≤ Real.exp Λ := Real.add_one_le_exp Λ
  refine ⟨Real.exp Λ, by linarith, ?_, ?_, ?_⟩ <;> rw [hl] <;> linarith

/-- The chosen `β`. -/
noncomputable def jointBeta : ℝ := exists_beta.choose

theorem jointBeta_spec :
    20 < jointBeta ∧ lamStar ≤ Real.log (jointBeta * (5 / 4)) + 1 ∧
    anaThreshold ≤ Real.log (jointBeta * (5 / 4)) + 1 ∧ 12 ≤ Real.log (jointBeta * (5 / 4)) + 1 :=
  exists_beta.choose_spec

theorem jointBeta_gt : 20 < jointBeta := jointBeta_spec.1

end JointL4
end Balaban.Inhabited
