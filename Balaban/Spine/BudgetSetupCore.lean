/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Spine.RootFInputs
public import Balaban.Spine.TransferAnalysis
public import Balaban.LargeField.Budget.LemmaB

/-!
# The setting and the budget setup of LF-2 from the prefix

For `β` large the a priori setting `𝒮[d, T, β, a]` is `Good` (`exists_good_lamHat`), and for every
budget constants `P` tied to those of the prefix and every running sequence of masses with (I.2) up
to a scale `K'` against `P.beta`, Lemma B has its hypotheses (`BudgetSetupTo`).  This is the common
core of the budget clauses of the steps (`lfBudgetInput_of_pin`) and of the kept half of `R`
(`Spine/KeptHalf.lean`).
-/

@[expose] public section

namespace Balaban.RootFSpine

open Balaban Balaban.LargeField Balaban.LargeField.Def7 Balaban.Multiscale Balaban.Background
  Balaban.SmallField

section Core

variable {d : ℕ} {δ : ℝ} {T : ℝ → ℝ → Typing} {P6 : ℝ → ℝ → Def6.Consts}
  {C7 : ℝ → ℝ → Consts7} {PB : ℝ → ℝ → BudgetConsts} {cs₀ : ℝ → ℝ → OpConsts}
  {M1 c : ℝ → ℝ → ℕ} {ϱ : ℝ → ℝ → ℝ}

/-- **`Good` and the budget setup from the prefix.** -/
theorem budget_good_setup (hA1 : PrefixInput d δ T P6 C7 PB cs₀ M1 c ϱ) {κ : ℝ} (hκ : 0 < κ)
    {c₉ : ℝ} (hc₉ : 0 < c₉) :
    ∃ b : ℝ, ∀ β : ℝ, b ≤ β →
      (𝒮[d, T κ c₉, β, (cs₀ κ c₉).aKer]).Good ∧
      ∀ (P : BudgetConsts) (ν : ℝ) (nuRun : ℕ → ℝ) (K' : ℕ), P.H0 = (PB κ c₉).H0 →
        P.c1 = (PB κ c₉).c1 → P.c2 = (PB κ c₉).c2 →
        RunningHypTo d (T κ c₉).L β ν (cs₀ κ c₉).aKer (1 / 20) P.beta nuRun K' →
        Nonempty (BudgetSetupTo 𝒮[d, T κ c₉, β, (cs₀ κ c₉).aKer] P K') := by
  obtain ⟨hL3, ha1, -, -, -, -, -, -, -, -, -, -, -, -, -, ⟨hTok, hθ, -, hH0, hc1, hLM, hcv⟩, -,
    hq, -⟩ := hA1 κ hκ c₉ hc₉
  obtain ⟨x₀, hx₀⟩ := exists_good_lamHat ({ T κ c₉ with d := d } : Typing) hTok hθ
  have hd3 : 3 ≤ d := hTok.three_le_d
  have hL2 : 2 ≤ (T κ c₉).L := by omega
  set Xa : ℝ := max (3 / (1 - (2 : ℝ) ^ (-(1 / (2 * ((T κ c₉).p0 : ℝ))))))
    (max ((PB κ c₉).c2 + 2)
      (3 + 2 * (thetaOf d (T κ c₉).L + 1 + 1 / (PB κ c₉).H0))) with hXa
  refine ⟨Real.exp (max x₀ Xa), fun β hβe => ?_⟩
  have hβ0 : 0 < β := lt_of_lt_of_le (Real.exp_pos _) hβe
  have hlog : max x₀ Xa ≤ Real.log β := (Real.le_log_iff_exp_le hβ0).2 hβe
  have hlogβa : Real.log β ≤ Real.log (β * (cs₀ κ c₉).aKer) :=
    Real.log_le_log hβ0 (by nlinarith)
  have hG := hx₀ β (cs₀ κ c₉).aKer (by linarith [le_max_left x₀ Xa])
  have hθ0 : 0 ≤ thetaOf d (T κ c₉).L := by
    unfold thetaOf
    exact mul_nonneg (Nat.cast_nonneg _)
      (Real.log_nonneg (by have : (2 : ℝ) ≤ (T κ c₉).L := by exact_mod_cast hL2
                           linarith))
  have hK : ∀ j, AnalyticLamAt (analyticK d (T κ c₉).L (T κ c₉).p0 (PB κ c₉).H0 (PB κ c₉).c2)
      (lamHat d (T κ c₉).L β (cs₀ κ c₉).aKer j) := by
    intro j
    apply analyticK_at (by omega) hL2 hH0
    have : 0 ≤ (j : ℝ) * thetaOf d (T κ c₉).L := mul_nonneg (Nat.cast_nonneg _) hθ0
    unfold lamHat
    linarith [le_max_right x₀ Xa]
  refine ⟨hG, fun P ν nuRun K' hH hc1' hc2' hrun => ⟨?_⟩⟩
  exact
    { β := β
      ν := ν
      a := (cs₀ κ c₉).aKer
      ε := 1 / 20
      nuRun := nuRun
      K := analyticK d (T κ c₉).L (T κ c₉).p0 (PB κ c₉).H0 (PB κ c₉).c2
      lam_eq := fun _ => rfl
      Kd := rfl
      KL := rfl
      Kp0 := rfl
      KH0 := hH.symm
      Kc2 := hc2'.symm
      lam_cond := hK
      H0_nonneg := by rw [hH]; exact hH0.le
      c1_nonneg := by rw [hc1']; exact hc1
      L_le_M := hLM
      cv_ge := by
        show ((T κ c₉).M : ℝ) ^ d * (P.H0 + P.c1 + 3) ≤ (T κ c₉).cv
        rw [hH, hc1']
        exact hcv
      run := hrun }

end Core

end Balaban.RootFSpine
