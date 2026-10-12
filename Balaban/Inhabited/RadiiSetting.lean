/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.History.InhabitedJoint
public import Balaban.LargeField.Operators.Setup
public import Balaban.LargeField.Budget.LemmaB
public import Balaban.Background.ExistenceSetup
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The setting of the genuine-radii witness

`d = L = 3`, `M = 14 M₁` with `M₁` such that `5 L M₁ ≥ R₀(3, 3)` (so `BgHyp` holds at the
separation `minSep L M₁`, and `Geo` holds with `c = 14`), `R_base = 32`, `θ_± = log 3`,
`c_v = 5 M^3 = M^d (H₀ + c₁ + 3)`, `λ_j = log (5β/4) + 1 + j log 3`.  This is the setting of
`Def7WitLF.lean` with `M` and `c_v` changed (that file has `M₁ = 1`, where `BgHyp` at the
separation `5 L M₁` is impossible).  The radii are `R_j = R_base λ_j²`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.Inhabited.RadiiSet

open Balaban Balaban.LargeField Balaban.LargeField.JointWitness

/-- The unit `M₁` of the generating sets: `5 L M₁ ≥ R₀(3, 3)` (so that `BgHyp` holds at the
separation `5 L M₁`). -/
noncomputable def M1 : ℕ := ⌈Balaban.Background.bgR0 3 3 / 15⌉₊ + 1

theorem M1_pos : 0 < M1 := Nat.succ_pos _

theorem bgR0_le_minSep : Balaban.Background.bgR0 3 3 ≤ ((5 * 3 * M1 : ℕ) : ℝ) := by
  have h := Nat.le_ceil (Balaban.Background.bgR0 3 3 / 15)
  have h2 : (⌈Balaban.Background.bgR0 3 3 / 15⌉₊ : ℝ) ≤ (M1 : ℝ) := by
    unfold M1; push_cast; linarith
  push_cast
  have := (div_le_iff₀ (by norm_num : (0 : ℝ) < 15)).mp (h.trans h2)
  linarith

/-- The typing of the witness. -/
noncomputable def typing0 : Typing where
  d := 3
  L := 3
  M := 14 * M1
  Rb := 32
  θp := Real.log 3
  θm := Real.log 3
  α := 1
  p0 := 5
  p2 := 9
  pR := 16
  A2 := 1
  A3 := 1
  A3' := 1
  CR := 0
  Cν := 0
  cv := 5 * ((14 * M1 : ℕ) : ℝ) ^ 3
  cH := 3 * Real.log 3
  sS := 4
  sP := 5
  c0 := 10

noncomputable def typing : Typing := { typing0 with Cν := typing0.Cr }

theorem log_three_pos : 0 < Real.log 3 := Real.log_pos (by norm_num)

theorem log_three_lt_two : Real.log 3 < 2 := by
  have := Real.log_lt_sub_one_of_pos (show (0 : ℝ) < 3 by norm_num) (by norm_num)
  linarith

theorem typing_ok : typing.Ok where
  three_le_d := le_refl _
  two_le_L := by show 2 ≤ 3; norm_num
  one_le_M := by show 1 ≤ 14 * M1; have := M1_pos; omega
  two_le_Rb := by show (2 : ℝ) ≤ 32; norm_num
  θm_pos := log_three_pos
  θm_le_θp := le_refl _
  α_pos := by show (0 : ℝ) < 1; norm_num
  A2_pos := by show (0 : ℝ) < 1; norm_num
  A3_pos := by show (0 : ℝ) < 1; norm_num
  A3'_pos := by show (0 : ℝ) < 1; norm_num
  CR_nonneg := le_refl _
  Cν_pos := by
    show 0 < typing0.Cr
    have hl : 0 < typing0.logL := Real.log_pos (by show (1 : ℝ) < ((3 : ℕ) : ℝ); norm_num)
    have h1 : 0 ≤ typing0.cStar := by
      unfold Typing.cStar
      have : (0 : ℝ) ≤ typing0.θp / (typing0.α * typing0.logL) :=
        div_nonneg log_three_pos.le (mul_nonneg (by show (0 : ℝ) ≤ 1; norm_num) hl.le)
      linarith
    have h2 : 0 ≤ typing0.cPrime := by
      unfold Typing.cPrime
      exact mul_nonneg h1 (by have := log_three_pos; show (0 : ℝ) ≤ 1 + 3 * Real.log 3; linarith)
    unfold Typing.Cr
    have : (0 : ℝ) ≤ 2 * typing0.A2 * typing0.cPrime ^ typing0.p2 :=
      mul_nonneg (by show (0 : ℝ) ≤ 2 * 1; norm_num) (pow_nonneg h2 _)
    linarith
  one_le_cv := by
    show (1 : ℝ) ≤ 5 * ((14 * M1 : ℕ) : ℝ) ^ 3
    have : (1 : ℝ) ≤ ((14 * M1 : ℕ) : ℝ) := by
      exact_mod_cast (by have := M1_pos; omega : 1 ≤ 14 * M1)
    have := one_le_pow₀ (n := 3) this
    linarith
  cH_nonneg := by have := log_three_pos; show (0 : ℝ) ≤ 3 * Real.log 3; linarith
  p2_ge := by decide
  pR_gt := by decide
  p0_gt := by decide
  c0_sS := by show ((4 : ℕ) : ℝ) + 1 ≤ ((10 : ℕ) : ℝ) * (1 - 1 / ((3 : ℕ) : ℝ)); norm_num
  c0_sP := by decide
  Cr_le := le_refl _

/-- The setting `λ_j = log (5β/4) + 1 + j log 3`. -/
noncomputable def setting (β : ℝ) : Setting where
  toTyping := typing
  lam := fun j => Real.log (β * (5 / 4)) + 1 + (j : ℝ) * Real.log 3

theorem setting_lam (β : ℝ) (j : ℕ) :
    (setting β).lam j = Real.log (β * (5 / 4)) + 1 + (j : ℝ) * Real.log 3 := rfl

theorem log_ge_of (β : ℝ) (hβ : 10 < β) : Real.log 3 < Real.log (β * (5 / 4)) :=
  Real.log_lt_log (by norm_num) (by linarith)

theorem setting_ok (β : ℝ) (hβ : 10 < β) : (setting β).Ok where
  toOk := typing_ok
  lam_step := fun j => by
    show Real.log 3 ≤ (setting β).lam (j + 1) - (setting β).lam j ∧
      (setting β).lam (j + 1) - (setting β).lam j ≤ Real.log 3
    rw [setting_lam, setting_lam]
    push_cast; constructor <;> linarith
  one_le_lam0 := by
    have := log_ge_of β hβ
    have := log_three_pos
    show (1 : ℝ) ≤ Real.log (β * (5 / 4)) + 1 + ((0 : ℕ) : ℝ) * Real.log 3
    simp; linarith
  θp_le_lam0 := by
    have := log_ge_of β hβ
    show Real.log 3 ≤ Real.log (β * (5 / 4)) + 1 + ((0 : ℕ) : ℝ) * Real.log 3
    simp; linarith

/-- The threshold `x₀` of `exists_lamStar` for the typing. -/
noncomputable def lamStar : ℝ := (exists_lamStar typing typing_ok).choose

theorem lamStar_spec : LamStarConditions typing lamStar :=
  (exists_lamStar typing typing_ok).choose_spec

theorem setting_good (β : ℝ) (hβ : 10 < β) (hx : lamStar ≤ Real.log (β * (5 / 4)) + 1) :
    (setting β).Good where
  ok := setting_ok β hβ
  lc := LamStarConditions.mono lamStar_spec (by
    show lamStar ≤ Real.log (β * (5 / 4)) + 1 + ((0 : ℕ) : ℝ) * Real.log 3
    simp; exact hx)

/-! ### The analytic constants and the budget -/

def anaK : AnalyticConsts where
  d := 3
  L := 3
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

theorem anaK_at {x : ℝ} (hx : anaThreshold ≤ x) : AnalyticLamAt anaK x := by
  have h1 : 3 / (1 - (2 : ℝ) ^ (-(1 / (2 * (5 : ℝ))))) ≤ x := (le_max_left _ _).trans hx
  have h2 : (4 : ℝ) ≤ x := (le_max_right _ _).trans hx
  have hl := log_three_lt_two
  have hl0 := log_three_pos
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

/-- The budget constants. -/
noncomputable def budgetConsts (β : ℝ) : BudgetConsts where
  c1 := 0
  c2 := 0
  H0 := 2
  beta := fun k => β * 3 ^ k

theorem setting_lam_eq (β : ℝ) (j : ℕ) : (setting β).lam j = lamHat 3 3 β (5 / 4) j := by
  rw [setting_lam]
  simp [lamHat, thetaOf]

noncomputable def budgetSetup (β ν : ℝ) (hβ : 10 < β) (hν : 0 < ν)
    (ha : anaThreshold ≤ Real.log (β * (5 / 4)) + 1) :
    BudgetSetup (setting β) (budgetConsts β) where
  β := β
  ν := ν
  a := 5 / 4
  ε := 0
  nuRun := fun k => ν * 9 ^ k
  K := anaK
  run :=
    { hd := by show 2 ≤ 3; norm_num
      hL := by show 2 ≤ 3; norm_num
      hβ := by linarith
      hν := hν
      ha1 := by norm_num
      ha2 := by norm_num
      hε0 := le_rfl
      hε := by norm_num
      beta_eq := fun k => ⟨1, one_pos, by simp, by
        show β * 3 ^ k = β * ((3 : ℕ) : ℝ) ^ (k * (3 - 2)) * 1
        simp⟩
      nu_eq := fun k => ⟨1, one_pos, by simp, by
        show ν * 9 ^ k = ν * ((3 : ℕ) : ℝ) ^ (2 * k) * 1
        rw [pow_mul]; norm_num⟩ }
  lam_eq := fun j => setting_lam_eq β j
  Kd := rfl
  KL := rfl
  Kp0 := rfl
  KH0 := rfl
  Kc2 := rfl
  lam_cond := fun j => anaK_at (by
    rw [setting_lam]
    have := log_three_pos
    have : (0 : ℝ) ≤ (j : ℝ) * Real.log 3 := by positivity
    linarith)
  H0_nonneg := by show (0 : ℝ) ≤ 2; norm_num
  c1_nonneg := le_rfl
  L_le_M := by show 3 ≤ 14 * M1; have := M1_pos; omega
  cv_ge := by
    show ((14 * M1 : ℕ) : ℝ) ^ 3 * (2 + 0 + 3) ≤ 5 * ((14 * M1 : ℕ) : ℝ) ^ 3
    linarith

/-! ### A large enough `β`, the geometric typing, the radii -/

instance (β : ℝ) : NeZero (setting β).L := ⟨by show (3 : ℕ) ≠ 0; norm_num⟩

/-- A large enough `β`. -/
theorem exists_beta : ∃ β : ℝ, 10 < β ∧ lamStar ≤ Real.log (β * (5 / 4)) + 1 ∧
    anaThreshold ≤ Real.log (β * (5 / 4)) + 1 := by
  set Λ : ℝ := max (max lamStar anaThreshold) 12 with hΛ
  have h1 : lamStar ≤ Λ := (le_max_left _ _).trans (le_max_left _ _)
  have h2 : anaThreshold ≤ Λ := (le_max_right _ _).trans (le_max_left _ _)
  have h3 : 12 ≤ Λ := le_max_right _ _
  have hl : Real.log (Real.exp Λ * (5 / 4)) = Λ + Real.log (5 / 4) := by
    rw [Real.log_mul (Real.exp_pos _).ne' (by norm_num), Real.log_exp]
  have hp : 0 < Real.log (5 / 4 : ℝ) := Real.log_pos (by norm_num)
  have he : Λ + 1 ≤ Real.exp Λ := Real.add_one_le_exp Λ
  refine ⟨Real.exp Λ, by linarith, ?_, ?_⟩ <;> rw [hl] <;> linarith

/-- The chosen `β`. -/
noncomputable def wβ : ℝ := exists_beta.choose

theorem wβ_spec : 10 < wβ ∧ lamStar ≤ Real.log (wβ * (5 / 4)) + 1 ∧
    anaThreshold ≤ Real.log (wβ * (5 / 4)) + 1 :=
  exists_beta.choose_spec

theorem wβ_gt : 10 < wβ := wβ_spec.1

theorem wβ_pos : 0 < wβ := by linarith [wβ_gt]

/-- The setting of the witness. -/
noncomputable abbrev wS : Setting := setting wβ

theorem wS_good : wS.Good := setting_good wβ wβ_gt wβ_spec.2.1

theorem wS_ok : wS.Ok := wS_good.ok

/-- The radii `R_j = R_base λ_j²`. -/
noncomputable def wR : ℕ → ℝ := fun j => wS.Rb * wS.lam j ^ 2

theorem wS_lam_one_le (j : ℕ) : 1 ≤ wS.lam j := wS_ok.one_le_lam j

/-- The geometric typing `M = 14 M₁ = c M₁`, `c = 14`. -/
noncomputable def wGeo (n : ℕ → ℕ) : Geo wS n wR wS.M where
  M1 := M1
  c := 14
  neM1 := ⟨by have := M1_pos; omega⟩
  nec := ⟨by norm_num⟩
  hM := by show 14 * M1 = 14 * M1; rfl
  hc := by norm_num
  hRlow := fun j => by
    show wS.Rb ≤ wS.Rb * wS.lam j ^ 2
    have h1 := wS_lam_one_le j
    have h2 : (0 : ℝ) ≤ wS.Rb := by show (0 : ℝ) ≤ 32; norm_num
    have h3 : (1 : ℝ) ≤ wS.lam j ^ 2 := one_le_pow₀ h1
    nlinarith
  hRmono := fun j => by
    apply Nat.floor_le_floor
    show wS.Rb * wS.lam (j - 1) ^ 2 ≤ wS.Rb * wS.lam j ^ 2
    have h1 := wS_ok.lam_mono (show j - 1 ≤ j by omega)
    have h2 := wS_lam_one_le (j - 1)
    have h3 : (0 : ℝ) ≤ wS.Rb := by show (0 : ℝ) ≤ 32; norm_num
    have h4 : wS.lam (j - 1) ^ 2 ≤ wS.lam j ^ 2 := by
      have : (0 : ℝ) ≤ wS.lam (j - 1) := by linarith
      gcongr
    exact mul_le_mul_of_nonneg_left h4 h3

/-- The radius hypotheses (RH) for `R_j = R_base λ_j²`. -/
theorem wRH : RadiusHyp wS.L wS.Rb wS.lam wR where
  mono := fun _ _ h => wS_ok.lam_mono h
  one_le := wS_ok.one_le_lam
  nonneg := fun j => mul_nonneg (by show (0 : ℝ) ≤ 32; norm_num) (sq_nonneg (wS.lam j))
  le := fun _ => le_rfl
  base := by show (4 * ((3 : ℕ) : ℝ) + 20) ≤ 32; norm_num

theorem wR_eq (j : ℕ) : wR j = wS.Rb * wS.lam j ^ 2 := rfl

end Balaban.Inhabited.RadiiSet
