/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Spine.RootFInputs
public import Balaban.Spine.TransferAnalysis

/-!
# The analytic and window facts of the prefix for the budget (LF-2)

`prefixBudgetFacts`: for the constants of `PrefixInput` and `β ≥ β₀(κ, c₉)` there are, at every
horizon `k̂_f` of a mass `ν > 0`, the facts that Lemma B and the counter history need on the setting
`λ_j = λ̂_j`: `S.Good`, (Λ15)–(Λ17′) at every `λ̂_j` for `analyticK`, the sign and size conditions of
the budget constants, `k₀ ≤ k̂_f` and the window (H-λ). They are used by the transfer at `k₀`
(`Spine/Transfer.lean`) and by the frozen steps (`Spine/FrozenSFBudget.lean`).
-/

@[expose] public section

namespace Balaban.RootFSpine

open Balaban Balaban.LargeField Balaban.LargeField.Def7 Balaban.Multiscale Balaban.SmallField

/-- The facts of the prefix that the budget needs, at a horizon `k̂_f`. -/
structure PrefixBudgetFacts (d : ℕ) (Ty : Typing) (PB : BudgetConsts) (a β ν : ℝ) (kf : ℕ) :
    Prop where
  three_le_d : 3 ≤ d
  two_le_L : 2 ≤ Ty.L
  good : (Setting.mk { Ty with d := d } (lamHat d Ty.L β a)).Good
  lam : ∀ j, AnalyticLamAt (analyticK d Ty.L Ty.p0 PB.H0 PB.c2) (lamHat d Ty.L β a j)
  H0_pos : 0 < PB.H0
  c1_nonneg : 0 ≤ PB.c1
  L_le_M : Ty.L ≤ Ty.M
  cv_ge : (Ty.M : ℝ) ^ d * (PB.H0 + PB.c1 + 3) ≤ Ty.cv
  k0_le : kZero d Ty.L β ν ≤ kf
  H1 : (kf : ℝ) - kZero d Ty.L β ν < lamHat d Ty.L β a (kZero d Ty.L β ν)
  H2 : lamHat d Ty.L β a kf ≤ d / 2 * lamHat d Ty.L β a (kZero d Ty.L β ν) + Ty.cH
  one_le_beta : 1 ≤ β
  four_le_beta : 4 ≤ β

/-- **The budget facts from the prefix** (the construction of `transferInput_of_prefix`): `hP` is
`PrefixInput`. -/
theorem prefixBudgetFacts (d : ℕ) (δ : ℝ) (Ty : ℝ → ℝ → Typing)
    (P6 : ℝ → ℝ → Def6.Consts) (C7 : ℝ → ℝ → Consts7) (PB : ℝ → ℝ → BudgetConsts)
    (cs₀ : ℝ → ℝ → OpConsts) (M1 c : ℝ → ℝ → ℕ) (ϱ : ℝ → ℝ → ℝ)
    (hP : PrefixInput d δ Ty P6 C7 PB cs₀ M1 c ϱ) (κ : ℝ) (hκ : 0 < κ) (c₉ : ℝ) (hc₉ : 0 < c₉) :
    ∃ β₀ : ℝ, ∀ β : ℝ, β₀ ≤ β → ∀ ν : ℝ, 0 < ν → ∀ kf : ℕ, IsHorizon (Ty κ c₉).L ν kf →
      PrefixBudgetFacts d (Ty κ c₉) (PB κ c₉) (cs₀ κ c₉).aKer β ν kf := by
  obtain ⟨hL3, ha1, ha2, -, -, -, -, -, -, -, -, -, -, -, -, ⟨hTok, hθ, hcH, hH0, hc1, hLM, hcv⟩, -⟩ :=
    hP κ hκ c₉ hc₉
  obtain ⟨x₀, hx₀⟩ := exists_good_lamHat ({ Ty κ c₉ with d := d } : Typing) hTok hθ
  have hd3 : 3 ≤ d := hTok.three_le_d
  have hL2 : 2 ≤ (Ty κ c₉).L := by omega
  set Xa : ℝ := max (3 / (1 - (2 : ℝ) ^ (-(1 / (2 * ((Ty κ c₉).p0 : ℝ))))))
    (max ((PB κ c₉).c2 + 2)
      (3 + 2 * (thetaOf d (Ty κ c₉).L + 1 + 1 / (PB κ c₉).H0))) with hXa
  refine ⟨Real.exp (max x₀ (max Xa (2 * (d : ℝ)))), ?_⟩
  intro β hβ ν hν kf hkf
  have hβ0 : 0 < β := lt_of_lt_of_le (Real.exp_pos _) hβ
  have hlog : max x₀ (max Xa (2 * (d : ℝ))) ≤ Real.log β :=
    (Real.le_log_iff_exp_le hβ0).2 hβ
  have hx₀β : x₀ ≤ Real.log β := (le_max_left _ _).trans hlog
  have hXaβ : Xa ≤ Real.log β := ((le_max_left _ _).trans (le_max_right _ _)).trans hlog
  have h2dβ : 2 * (d : ℝ) ≤ Real.log β := ((le_max_right _ _).trans (le_max_right _ _)).trans hlog
  have hdR : (3 : ℝ) ≤ d := by exact_mod_cast hd3
  have hβ1 : 1 ≤ β := by
    by_contra hcon
    push Not at hcon
    have := Real.log_nonpos hβ0.le hcon.le
    linarith
  have hlogβa : Real.log β ≤ Real.log (β * (cs₀ κ c₉).aKer) :=
    Real.log_le_log hβ0 (by nlinarith)
  have hθ0 : 0 ≤ thetaOf d (Ty κ c₉).L := by
    unfold thetaOf
    exact mul_nonneg (Nat.cast_nonneg _)
      (Real.log_nonneg (by have : (2 : ℝ) ≤ (Ty κ c₉).L := by exact_mod_cast hL2
                           linarith))
  have hG := hx₀ β (cs₀ κ c₉).aKer (by linarith)
  have hK : ∀ j, AnalyticLamAt (analyticK d (Ty κ c₉).L (Ty κ c₉).p0 (PB κ c₉).H0 (PB κ c₉).c2)
      (lamHat d (Ty κ c₉).L β (cs₀ κ c₉).aKer j) := by
    intro j
    apply analyticK_at (by omega) hL2 hH0
    have : 0 ≤ (j : ℝ) * thetaOf d (Ty κ c₉).L := mul_nonneg (Nat.cast_nonneg _) hθ0
    unfold lamHat
    linarith
  have hhor := hkf.2
  obtain ⟨hH1, hH2⟩ := hLam_window hd3 hL2 (a := (cs₀ κ c₉).aKer) (cH := (Ty κ c₉).cH) ha1 hβ0
    h2dβ hν hcH hhor
  have hk0 : kZero d (Ty κ c₉).L β ν ≤ kf :=
    kZero_le_horizon hd3 hL2 hβ1 hν hkf.1
  have hβ4 : 4 ≤ β := by
    have h6 : (6 : ℝ) ≤ Real.log β := by linarith
    have := Real.add_one_le_exp (Real.log β)
    rw [Real.exp_log hβ0] at this
    linarith
  exact ⟨hd3, hL2, hG, hK, hH0, hc1, hLM, hcv, hk0, hH1, hH2, hβ1, hβ4⟩

end Balaban.RootFSpine
