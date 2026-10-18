/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Spine.RootFInputs
public import Balaban.Spine.TransferAnalysis
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
    (hrep : RepClassAt d N T P6 C7 PB cs₀ M1 c rH ϱ β ν h kf (kZero d T.L β ν) ρ νk) :
    FlatClassAt d N T P6 C7 PB cs₀ M1 c rH ϱ β ν h kf (kZero d T.L β ν) ρ νk := by
  obtain ⟨hM6, hkK, R, geo, cs, P, F, St, vc, hgeo, hKer, hCpsi, hCb, haw, hP1, hP2, hP3, hIs,
    hβ0, hν0, hνk, hrun, hcoh⟩ := hrep
  have hbeta : ∀ j ≤ kZero d T.L β ν, P.beta j = F.sf.β j := fun j hj => hIs.coh.beta_P j hj
  let B : BudgetSetupTo (Setting.mk { T with d := d } (lamHat d T.L β cs₀.aKer)) P
      (kZero d T.L β ν) :=
    { β := β
      ν := ν
      a := cs₀.aKer
      ε := 1 / 20
      nuRun := F.sf.ν
      K := analyticK d T.L T.p0 PB.H0 PB.c2
      lam_eq := fun _ => rfl
      Kd := rfl
      KL := rfl
      Kp0 := rfl
      KH0 := hP3.symm
      Kc2 := hP2.symm
      lam_cond := hK
      H0_nonneg := hP3 ▸ hH0
      c1_nonneg := hP1 ▸ hc1
      L_le_M := hLM
      cv_ge := by rw [hP3, hP1]; exact hcv
      run :=
        { hd := hrun.hd
          hL := hrun.hL
          hβ := hrun.hβ
          hν := hrun.hν
          ha1 := hrun.ha1
          ha2 := hrun.ha2
          hε0 := hrun.hε0
          hε := hrun.hε
          beta_eq := fun j hj => by rw [hbeta j hj]; exact hrun.beta_eq j hj
          nu_eq := hrun.nu_eq } }
  exact ⟨hM6, hkK, R, geo, cs, P, F, St, vc, hgeo, hKer, hCpsi, hCb, haw, hP1, hP2, hP3,
    hIs.toFlat_of_all_horizons rfl G B hk0 hH1 hH2, hβ0, hν0, hνk, hrun, hcoh⟩

/-- **The typing conditions of LF-2 that the transfer reads**, for every `κ, c₉ > 0`: the typing
`T = Ty κ c₉` with dimension `d` is `Typing.Ok`; `θ₋ ≤ (d-2) log L ≤ θ₊` ((H-λ), first part);
`c_H ≥ d(d-2) log L / 2` ((H-λ), the window of LFR Lemma IV.3.3 (c)); and for Lemma B: `H₀ > 0`,
`c₁ ≥ 0`, `L ≤ M`, `c_v ≥ M^d (H₀ + c₁ + 3)`. These are constant conditions on `Ty κ c₉` and
`PB κ c₉`; `PrefixInput` states none of them. -/
def TransferTyping (d : ℕ) (Ty : ℝ → ℝ → Typing) (PB : ℝ → ℝ → BudgetConsts) : Prop :=
  ∀ κ : ℝ, 0 < κ → ∀ c₉ : ℝ, 0 < c₉ →
    ({ Ty κ c₉ with d := d } : Typing).Ok ∧
    ((Ty κ c₉).θm ≤ thetaOf d (Ty κ c₉).L ∧ thetaOf d (Ty κ c₉).L ≤ (Ty κ c₉).θp) ∧
    (d : ℝ) * ((d : ℝ) - 2) / 2 * Real.log (Ty κ c₉).L ≤ (Ty κ c₉).cH ∧
    0 < (PB κ c₉).H0 ∧ 0 ≤ (PB κ c₉).c1 ∧ (Ty κ c₉).L ≤ (Ty κ c₉).M ∧
    ((Ty κ c₉).M : ℝ) ^ d * ((PB κ c₉).H0 + (PB κ c₉).c1 + 3) ≤ (Ty κ c₉).cv

/-- **A4 (the transfer at `k₀`, LFR Lemma IV.2.1).** `hP` is `PrefixInput` (it gives `1 < a`, the
kernel constant, and `L ≥ 3`); `hTy` is `TransferTyping`. -/
theorem transferInput_of_prefix (d N : ℕ) (δ : ℝ) (Ty : ℝ → ℝ → Typing)
    (P6 : ℝ → ℝ → Def6.Consts) (C7 : ℝ → ℝ → Consts7) (PB : ℝ → ℝ → BudgetConsts)
    (cs₀ : ℝ → ℝ → OpConsts) (M1 c : ℝ → ℝ → ℕ) (rH ϱ : ℝ → ℝ → ℝ)
    (hP : PrefixInput d δ Ty P6 C7 cs₀ M1 c) (hTy : TransferTyping d Ty PB) :
    TransferInput d N Ty P6 C7 PB cs₀ M1 c rH ϱ := by
  intro κ hκ c₉ hc₉
  obtain ⟨hTok, hθ, hcH, hH0, hc1, hLM, hcv⟩ := hTy κ hκ c₉ hc₉
  obtain ⟨hL3, ha1, ha2, -⟩ := hP κ hκ c₉ hc₉
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
  exact flatClassAt_of_repClassAt d N (Ty κ c₉) (P6 κ c₉) (C7 κ c₉) (PB κ c₉) (cs₀ κ c₉)
    (M1 κ c₉) (c κ c₉) (rH κ c₉) (ϱ κ c₉) β ν h kf ρ νk hG hK hH0.le hc1 hLM hcv hk0 hH1 hH2 hrep

end Balaban.RootFSpine
