/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Spine.RootFInputs
public import Balaban.Spine.TransferAnalysis
public import Balaban.Spine.BudgetSetupOfRun
public import Balaban.LargeField.Def7v2Basic

/-!
# The transfer at `k₀` (LFR Lemma IV.2.1) from the class at the switching scale

`flatClassAt_of_repClassAt`: a member of the class `ℛ_{k₀}` (`RepClassAt`) is a member of
`ℛ♭_{k₀}` (`FlatClassAt`), with the same data. The clause `IsRep2` is re-read by
`IsRep2.toFlat_of_all_horizons`; the budget setup of Lemma B needs (I.2) only up to `k₀`
(`BudgetSetupTo`), which the class provides (`RunningHypTo`); `LFCoherent`, `β_0 = β`, `ν_0 = ν`
and the running mass are carried through unchanged.
-/

@[expose] public section

namespace Balaban.RootFSpine

open MeasureTheory Balaban Balaban.LargeField Balaban.LargeField.Def7 Balaban.LargeField.Def7v2
  Balaban.SmallField Balaban.SmallField.Def6v2

/-- **The transfer for one class member**, given the conditions of LF-2 on the setting
`λ_j = λ̂_j`: `S.Good`, (Λ15)–(Λ17′) at every `λ̂_j` for the constants `analyticK`, the constants
of the budget, and (H-λ) for `k̂ = kf`. -/
theorem flatClassAt_of_repClassAt (d N : ℕ) (T : Typing) (P6 : Def6.Consts) (C7 : Consts7)
    (PB : BudgetConsts) (cs₀ : OpConsts) (M1 c : ℕ) (rH ϱ β ν : ℝ)
    (h : EuclideanSpace ℝ (Fin N)) (kf : ℕ) [NeZero T.M] [NeZero T.L]
    (ρ : 𝒟[d, N, T, β, cs₀.aKer, kf + 1, kZero d T.L β ν]) (νk : ℝ)
    (G : (Setting.mk { T with d := d } (lamHat d T.L β cs₀.aKer)).Good)
    (hK : ∀ j, AnalyticLamAt (analyticK d T.L T.p0 PB.H0 PB.c2) (lamHat d T.L β cs₀.aKer j))
    (hH0 : 0 ≤ PB.H0) (hc1 : 0 ≤ PB.c1) (hLM : T.L ≤ T.M)
    (hcv : (T.M : ℝ) ^ d * (PB.H0 + PB.c1 + 3) ≤ T.cv)
    (hk0 : kZero d T.L β ν ≤ kf)
    (hH1 : (kf : ℝ) - kZero d T.L β ν < lamHat d T.L β cs₀.aKer (kZero d T.L β ν))
    (hH2 : lamHat d T.L β cs₀.aKer kf ≤
      d / 2 * lamHat d T.L β cs₀.aKer (kZero d T.L β ν) + T.cH)
    (hν9 : νk ≤ 9 / 10)
    (hrep : RepClassAt d N T P6 C7 PB cs₀ M1 c rH ϱ β ν h kf (kZero d T.L β ν) ρ νk) :
    FlatClassAt d N T P6 C7 PB cs₀ M1 c rH ϱ β ν h kf (kZero d T.L β ν) ρ νk := by
  obtain ⟨hM6, hkK, R, geo, cs, P, F, St, vc, hgeo, hKer, hCpsi, hCb, haw, hP1, hP2, hP3, hIs,
    hβ0, hν0, hνk, hrun, hcoh, -⟩ := hrep
  have hbeta : ∀ j ≤ kZero d T.L β ν, P.beta j = F.sf.β j := fun j hj => hIs.coh.beta_P j hj
  let B : BudgetSetupTo (Setting.mk { T with d := d } (lamHat d T.L β cs₀.aKer)) P
      (kZero d T.L β ν) :=
    budgetSetupToOfRun T PB P β ν cs₀.aKer (kZero d T.L β ν) F.sf.β F.sf.ν hP1 hP2 hP3 hbeta hrun hK hH0 hc1 hLM hcv
  exact ⟨hM6, hkK, R, geo, cs, P, F, St, vc, hgeo, hKer, hCpsi, hCb, haw, hP1, hP2, hP3,
    hIs.toFlat_of_all_horizons rfl G B hk0 hH1 hH2, hβ0, hν0, hνk, hrun, hcoh, hν9⟩

/-- **The running mass at the first frozen scale is small**: if `1 ≤ k₀`, `β ≥ 4` and
`ν_{k₀} = ν L^{2k₀} δ` with `|log δ| ≤ 1/20` ((I.2)), then `ν_{k₀} ≤ 9/10`. From
`β ν L^{k₀ d} ≤ 1` (the definition of `k₀`): `ν L^{2k₀} ≤ β⁻¹`, and `δ ≤ e^{1/20} < 3`. -/
theorem nu_kZero_le {d L : ℕ} (hd : 3 ≤ d) (hL : 2 ≤ L) {β ν δ : ℝ} (hβ : 4 ≤ β) (hν : 0 < ν)
    (hk : 1 ≤ kZero d L β ν) (hδ0 : 0 < δ) (hδ : |Real.log δ| ≤ 1 / 20) :
    ν * (L : ℝ) ^ (2 * kZero d L β ν) * δ ≤ 9 / 10 := by
  have hg : KZeroGenuine β ν := by
    by_contra hng
    have := kZero_of_not_genuine (d := d) hL hng
    omega
  have hβν : 0 < β * ν := mul_pos (by linarith) hν
  have hspec := kZero_spec (d := d) (L := L) (by omega) hL hβν hg
  have hLR : (1 : ℝ) ≤ L := by exact_mod_cast (by omega : 1 ≤ L)
  have hpow : (L : ℝ) ^ (2 * kZero d L β ν) ≤ (L : ℝ) ^ (kZero d L β ν * d) :=
    pow_le_pow_right₀ hLR (by nlinarith)
  have h1 : β * (ν * (L : ℝ) ^ (2 * kZero d L β ν)) ≤ 1 := by
    have : 0 ≤ β * ν := hβν.le
    calc β * (ν * (L : ℝ) ^ (2 * kZero d L β ν)) = β * ν * (L : ℝ) ^ (2 * kZero d L β ν) := by ring
      _ ≤ β * ν * (L : ℝ) ^ (kZero d L β ν * d) := mul_le_mul_of_nonneg_left hpow this
      _ ≤ 1 := hspec
  have hδ3 : δ ≤ 3 := by
    have h1 : Real.log δ ≤ 1 / 20 := (abs_le.1 hδ).2
    calc δ = Real.exp (Real.log δ) := (Real.exp_log hδ0).symm
      _ ≤ Real.exp (1 / 20) := Real.exp_le_exp.2 h1
      _ ≤ Real.exp 1 := Real.exp_le_exp.2 (by norm_num)
      _ ≤ 3 := (Real.exp_one_lt_d9.le.trans (by norm_num))
  have hx : 0 ≤ ν * (L : ℝ) ^ (2 * kZero d L β ν) := by positivity
  nlinarith

/-- **A4 (the transfer at `k₀`, LFR Lemma IV.2.1).** `hP` is `PrefixInput` (it gives `1 < a`, the
kernel constant, `L ≥ 3` and the typing clauses `TypingClauses`). -/
theorem transferInput_of_prefix (d N : ℕ) (δ : ℝ) (Ty : ℝ → ℝ → Typing)
    (P6 : ℝ → ℝ → Def6.Consts) (C7 : ℝ → ℝ → Consts7) (PB : ℝ → ℝ → BudgetConsts)
    (cs₀ : ℝ → ℝ → OpConsts) (M1 c : ℝ → ℝ → ℕ) (rH ϱ : ℝ → ℝ → ℝ)
    (hP : PrefixInput d δ Ty P6 C7 PB cs₀ M1 c ϱ) :
    TransferInput d N Ty P6 C7 PB cs₀ M1 c rH ϱ := by
  intro κ hκ c₉ hc₉
  obtain ⟨hL3, ha1, ha2, -, -, -, -, -, -, -, -, -, -, -, -, ⟨hTok, hθ, hcH, hH0, hc1, hLM, hcv⟩, -⟩ :=
    hP κ hκ c₉ hc₉
  obtain ⟨x₀, hx₀⟩ := exists_good_lamHat ({ Ty κ c₉ with d := d } : Typing) hTok hθ
  have hd3 : 3 ≤ d := hTok.three_le_d
  have hL2 : 2 ≤ (Ty κ c₉).L := by omega
  set Xa : ℝ := max (3 / (1 - (2 : ℝ) ^ (-(1 / (2 * ((Ty κ c₉).p0 : ℝ))))))
    (max ((PB κ c₉).c2 + 2)
      (3 + 2 * (thetaOf d (Ty κ c₉).L + 1 + 1 / (PB κ c₉).H0))) with hXa
  refine ⟨Real.exp (max x₀ (max Xa (2 * (d : ℝ)))), ?_⟩
  intro β hβ ν hν _ h _ kf hkf _ _ hk1 ρ νk hrep
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
  have hν9 : νk ≤ 9 / 10 := by
    obtain ⟨_, _, _, _, _, _, F, _, _, _, _, _, _, _, _, _, _, _, _, _, hνk, hrun, -⟩ := hrep
    obtain ⟨-, -, -, -, -, -, -, -, -, hnu⟩ := hrun
    obtain ⟨δ', hδ0, hδlog, hνeq⟩ := hnu (kZero d (Ty κ c₉).L β ν) le_rfl
    rw [← hνk, hνeq]
    exact nu_kZero_le hd3 hL2 hβ4 hν hk1 hδ0 hδlog
  exact flatClassAt_of_repClassAt d N (Ty κ c₉) (P6 κ c₉) (C7 κ c₉) (PB κ c₉) (cs₀ κ c₉)
    (M1 κ c₉) (c κ c₉) (rH κ c₉) (ϱ κ c₉) β ν h kf ρ νk hG hK hH0.le hc1 hLM hcv hk0 hH1 hH2 hν9
    hrep

end Balaban.RootFSpine
