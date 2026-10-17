/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.RRemovedMargin
public import Balaban.LargeField.R.RRemovedCapEnergy
public import Balaban.LargeField.R.RRemovedFracArith
public import Balaban.LargeField.R.RRemovedFracE
public import Balaban.LargeField.R.RRemovedFracMassArith
import Mathlib

/-!
# The complete-action quotient of the removed outcome

`notes/phase1/LF4R-PLAN.md`, leaf 6.  `removedFactor_le_restricted` with the bounds of Lemma III.8.2
(`denominatorRestricted_bounds_of_margin_of_weighted`), the margin of the history
(`hmargin_removed`, `hZr_removed`) at `R = (2/γ_w) log β_k`, and a bounded positive running mass:
`quotient ≤ exp (F_z + (C_Ẽ' + C_m) D₀^d + C_♮ λ_k^{2d+1} + 4 + C_k)`,
`F_z = (N/2) log β_k |Z₀|` and `C_m` is the explicit positive-mass oscillation cost.

Needed beyond the history: `log β_k ≤ λ_k`, `λ_{k-1}` large (`removed_margin_arith`).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open Balaban Balaban.Multiscale Balaban.Background Balaban.Fluctuation Balaban.Localization ActionConv
  RegionHistory

/-- The local running mass is the coefficient of the complete action at scale `k`. -/
theorem betaK_mul_nu_scaled_eq {d L k : ℕ} (hd : 2 ≤ d) (β0 ν : ℝ) :
    betaK d L k β0 * (ν * (L : ℝ) ^ (2 * k)) = β0 * ν * ((L : ℝ) ^ k) ^ d := by
  have hsum : k * (d - 2) + 2 * k = k * d := by
    calc k * (d - 2) + 2 * k = k * ((d - 2) + 2) := by ring
      _ = k * d := by rw [Nat.sub_add_cancel hd]
  unfold betaK
  rw [← pow_mul]
  calc β0 * (L : ℝ) ^ (k * (d - 2)) * (ν * (L : ℝ) ^ (2 * k))
      = β0 * ν * ((L : ℝ) ^ (k * (d - 2)) * (L : ℝ) ^ (2 * k)) := by ring
    _ = β0 * ν * (L : ℝ) ^ (k * (d - 2) + 2 * k) := by rw [pow_add]
    _ = β0 * ν * (L : ℝ) ^ (k * d) := by rw [hsum]

section Quotient

variable {S : Setting} (ok : S.Ok) {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K : ℕ}
  [NeZero S.L] [NeZero S.M] {k' : ℕ} {N₁ m₁ N : ℕ} [NeZero N₁] [NeZero N] {ϱ ϱ₀ : ℝ}
  {G₀ : GeneratingSet S.d S.L (N₁ * S.L ^ m₁) (k' + 1) ϱ₀}
  {G : GeneratingSet S.d S.L (N₁ * S.L ^ m₁) (k' + 1) ϱ}

include ok in
/-- **The complete-action quotient (2.58′) of the removed outcome from the history**:
the quotient of `removedFactor_le_restricted` is bounded with one additional cost
`C_m D₀^d`, where `C_m = E (N/2) (4 B_* + B_*²) S_γ`, `B_* = Kw cF d L`,
and `S_γ = exp (γ (2d+1)) countConst d L γ`.
Typing data from the history: `hbx` (the box `Z₀`), `hZrsites` (the action region `Z_r`), `hq`.
Source bounds: `hnat` (`|C^♮_0| ≤ C_♮ λ^{2d+1}`), `hCEt` (`C_Ẽ'` collects `C_Ẽ` and the margin constant),
`hlogβ` (`log β_k ≤ λ_k`, from `log_b_le_lamHat`), `hxl` (`λ_{k-1}` large, `removed_margin_arith`),
`hβν` (`β_k ν L^{2k} ≤ E`, with `β_k ν L^{2k} = β₀ ν L^{kd}`); the margin is uncapped
(`hmargin_removed_uncapped`). -/
theorem removed_quotient_le_of_history_of_mass_bound {a₁ : ℝ} (hprec : Precedes G₀ G)
    (ψ0 : BlockV S.d S.L (N₁ * S.L ^ m₁) (k' + 1) → EuclideanSpace ℝ (Fin N)) (h : Fin N → ℝ) (Du : BgData G₀ N)
    {φu : G₀.Ω 1 × Fin N → ℂ} (D : Region G₀) (Zr Zk1 : Region G)
    (Zb : Finset (Torus S.d ((N₁ * S.L ^ m₁) * S.L ^ ((k' + 1) - (k' + 1))))) {β0 ν : ℝ} (ϖ : ℕ → ℝ)
    (aN : Torus S.d ((N₁ * S.L ^ m₁) * S.L ^ ((k' + 1) - (k' + 1))) → ℝ) (ψk : Torus S.d ((N₁ * S.L ^ m₁) * S.L ^ ((k' + 1) - (k' + 1))) → Fin N → ℂ)
    (hβ0 : 0 < β0) (hν : 0 ≤ ν) (ha₁ : 0 < a₁) (hL : 2 ≤ S.L) (ha : ∀ j, 0 ≤ compWeight S.L a₁ j)
    (haN : ∀ z ∈ Zb, 0 < aN z)
    (hZb : ∀ z ∈ Zb, ∀ x ∈ fib S.d S.L (N₁ * S.L ^ m₁) (k' + 1) (k' + 1) z, 1 ≤ G₀.layerIndex x ∧ G₀.layerIndex x < (k' + 1))
    (hDat : (windowData G₀ G hprec (compWeight S.L a₁) ψ0 h).IsReal) (hDu : Du.IsReal)
    (hφu : ∀ p, (φu p).im = 0)
    (hφ : ∀ p, (hprec.restrictφ (phiZero G (compWeight S.L a₁) ψ0 h) p).im = 0)
    (hid : gaussNat G₀ ϖ Du.Ψ (betaK S.d S.L (k' + 1) β0) aN ψk Zb +
          (β0 : ℂ) * actionRegionC D (compWeight S.L a₁) ν Du φu -
          ((Real.log (constNat N (betaK S.d S.L (k' + 1) β0) aN Zb) : ℝ) : ℂ) =
        (β0 : ℂ) * actionRegionC Zr (compWeight S.L a₁) ν (psiZeroData G ψ0 h)
            (phiZero G (compWeight S.L a₁) ψ0 h) -
          (β0 : ℂ) * actionRegion0 Zk1 ν (psiZeroData G ψ0 h) (phiZero G (compWeight S.L a₁) ψ0 h) +
          ((betaK S.d S.L (k' + 1) β0 : ℝ) * ∑ z ∈ Zb, (1 / 2 : ℂ) * (aN z : ℂ) *
              dotC (kAvg (dataInc (windowData G₀ G hprec (compWeight S.L a₁) ψ0 h) Du) z)
                (kAvg (dataInc (windowData G₀ G hprec (compWeight S.L a₁) ψ0 h) Du) z) +
            (β0 : ℂ) * (deltaActionC D (compWeight S.L a₁) ν
                (windowData G₀ G hprec (compWeight S.L a₁) ψ0 h) Du
                (hprec.restrictφ (phiZero G (compWeight S.L a₁) ψ0 h)) φu
                (hprec.restrictα (alphaZero G (compWeight S.L a₁) ψ0 h)) +
              nuTerm D ν (windowData G₀ G hprec (compWeight S.L a₁) ψ0 h)
                (hprec.restrictφ (phiZero G (compWeight S.L a₁) ψ0 h)) φu)) +
          (β0 : ℂ) * stTerm D (windowData G₀ G hprec (compWeight S.L a₁) ψ0 h) Du
            (hprec.restrictφ (phiZero G (compWeight S.L a₁) ψ0 h)) φu -
          ((Real.log (constNat N (betaK S.d S.L (k' + 1) β0) (compWeightZ G₀ a₁) Zb) : ℝ) : ℂ) +
          Cnat a₁ hprec ψ0 h Du Zb β0 ϖ aN ψk)
    (hA0 : ‖(β0 : ℂ) * actionRegion0 Zk1 ν (psiZeroData G ψ0 h)
      (phiZero G (compWeight S.L a₁) ψ0 h)‖ < 1 / 4)
    (hb : ‖(1 / 2 : ℂ) * (β0 : ℂ) * D.sitePair (hprec.restrictα (alphaZero G (compWeight S.L a₁) ψ0 h))
        (svec G₀ (φu - hprec.restrictφ (phiZero G (compWeight S.L a₁) ψ0 h)))
        (svec G₀ (φu - hprec.restrictφ (phiZero G (compWeight S.L a₁) ψ0 h)))‖ < 1 / 4)
    (hst : ‖(β0 : ℂ) * stTerm D (windowData G₀ G hprec (compWeight S.L a₁) ψ0 h) Du
        (hprec.restrictφ (phiZero G (compWeight S.L a₁) ψ0 h)) φu‖ < 1 / 4)
    (hnu : ‖(β0 : ℂ) * nuTerm D ν (windowData G₀ G hprec (compWeight S.L a₁) ψ0 h)
        (hprec.restrictφ (phiZero G (compWeight S.L a₁) ψ0 h)) φu‖ < 1 / 4)
    {D0 : ℕ} (hd : 2 ≤ S.d) (hk : 1 ≤ (k' + 1)) (b0 : Torus S.d ((N₁ * S.L ^ m₁) * S.L ^ ((k' + 1) - (k' + 1)))) (w : Fin S.d → ℕ)
    (hw1 : ∀ i, 1 ≤ w i) (hwD : ∀ i, w i ≤ D0) (hm : D0 + 2 ≤ (N₁ * S.L ^ m₁) * S.L ^ ((k' + 1) - (k' + 1)))
    {X : Set (Torus S.d ((N₁ * S.L ^ m₁) * S.L ^ ((k' + 1) - (k' + 1))))} (hXreg : box b0 w ∪ shellOut (box b0 w) ⊆ X)
    (hΩ : OverTop G (box b0 w ∪ shellOut (box b0 w)))
    (hdata : ∀ x ∈ dataSites G, jBlock S.d S.L (N₁ * S.L ^ m₁) (k' + 1) (k' + 1) x ∈ X) (Hbg : BgHyp S.d S.L (k' + 1) ϱ (compWeight S.L a₁) 0)
    {δ : ℝ} (hδ : 0 < δ)
    (hδc : δ ≤ psiZeroC11 N G (compWeight S.L a₁) hd hk b0 w hw1 hwD hm hXreg hΩ hdata Hbg)
    {ψout : BlockField S.d S.L (N₁ * S.L ^ m₁) (k' + 1) N} (hψout : TubeOn G (X \ box b0 w) δ ψout) {p0 : ℝ}
    (hp0 : 1 ≤ cSix S.d D0 (psiZeroK N G (compWeight S.L a₁) hd hk b0 w hw1 hwD hm hXreg hΩ hdata Hbg) * p0)
    (hrad : psiZeroK N G (compWeight S.L a₁) hd hk b0 w hw1 hwD hm hXreg hΩ hdata Hbg * δ +
      5 * zeroRadius (cSix S.d D0 (psiZeroK N G (compWeight S.L a₁) hd hk b0 w hw1 hwD hm hXreg hΩ hdata Hbg))
        (betaK S.d S.L (k' + 1) β0) p0 ≤ etaDen S.d S.L N D0)
    (hψ0 : ∀ z i, ψ0 ⟨(k' + 1), z⟩ i =
      psiZero N G (compWeight S.L a₁) hd hk b0 w hw1 hwD hm hXreg hΩ hdata Hbg hδ hδc hψout z i)
    (Ckk : ℝ)
    (Hh : RegionHistory S n R k0 K) (hkK : k' + 1 ≤ K) (Zc : Hh.Comp (k' + 1))
    (hq : N₁ * S.L ^ m₁ = S.M * n (k' + 1))
    (hbx : ∀ x : Torus S.d (N₁ * S.L ^ m₁ * S.L ^ (k' + 1)),
      jBlock S.d S.L (N₁ * S.L ^ m₁) (k' + 1) (k' + 1) x ∈ box b0 w ↔
        blockMap (S.L ^ (k' + 1)) (S.M * n (k' + 1))
          (torusCast (congrArg (· * S.L ^ (k' + 1)) hq) x) ∈ Hh.Zzero (k' + 1) Zc)
    (hZrsites : ∀ x : Torus S.d (N₁ * S.L ^ m₁ * S.L ^ (k' + 1)),
      x ∈ Zr.sites ↔ cubeMap n S.L S.M (k' + 1) (k' + 1)
        (torusCast (congrArg (· * S.L ^ (k' + 1)) hq) x) ∈ (Zc.1 : Set (Torus S.d (n (k' + 1)))))
    {Kw δw : ℝ} (hWP : WeightedProp51S S.d S.L N Kw δw) (hKw : 0 ≤ Kw)
    (hOp : Dec2.OpSetting G (compWeight S.L a₁) 0)
    (hsep2 : 2 * S.d * Real.log S.L ≤ gammaW S.d / 4 * (ϱ - 1))
    {E : ℝ} (hβν : betaK S.d S.L (k' + 1) β0 *
      (ν * (S.L : ℝ) ^ (2 * (k' + 1))) ≤ E)
    (hh1 : ∀ i, |h i| ≤ 1)
    (hsmall : bgK1 S.d S.L N * (psiZeroK N G (compWeight S.L a₁) hd hk b0 w hw1 hwD hm hXreg hΩ hdata Hbg * δ) ≤
      min (deltaStar S.d S.L N) δw)
    (hρs : zeroRadius (cSix S.d D0 (psiZeroK N G (compWeight S.L a₁) hd hk b0 w hw1 hwD hm hXreg hΩ hdata Hbg))
      (betaK S.d S.L (k' + 1) β0) p0 ≤ min (deltaStar S.d S.L N) δw)
    (hRfl : ⌊R k'⌋₊ = ⌊S.Rb * S.lam k' ^ 2⌋₊)
    (hlogβ : Real.log (betaK S.d S.L (k' + 1) β0) ≤ S.lam (k' + 1))
    (hxl : ((S.L : ℝ) * (2 / gammaW S.d) * (1 + S.θp) + S.M) / (S.M * S.Rb) ≤ S.lam k')
    {CEt Cnat : ℝ}
    (hCEt : cTildeE N S.d D0 + (S.d + 1) * N * (2 * (Kw * cF S.d S.L * Real.exp (2 * S.d * gammaW S.d)) +
        (Kw * cF S.d S.L * Real.exp (2 * S.d * gammaW S.d)) ^ 2) *
        (Real.exp (gammaW S.d / 2 * (2 * S.d + 1)) * countConst S.d S.L (gammaW S.d / 2)) ≤ CEt)
    (hnat : ‖Cnat0 a₁ hprec ψ0 h Du Zb β0 ϖ aN ψk‖ ≤ Cnat * S.lam (k' + 1) ^ (2 * S.d + 1)) :
    Real.exp (-(gaussNat G₀ ϖ Du.Ψ (betaK S.d S.L (k' + 1) β0) aN ψk Zb).re -
          (((β0 : ℂ) * actionRegionC D (compWeight S.L a₁) ν Du φu).re - Ckk)) *
        constNat N (betaK S.d S.L (k' + 1) β0) aN Zb / constNat N (betaK S.d S.L (k' + 1) β0) (compWeightZ G₀ a₁) Zb /
        (∫ u, rhoZeroRestricted G (compWeight S.L a₁) hd hk b0 w hw1 hwD hm hXreg hΩ hdata Hbg hδ hδc hψout
          Zr ν h β0 p0 u) ≤
      Real.exp ((N : ℝ) / 2 * Real.log (betaK S.d S.L (k' + 1) β0) *
        ((boxFinset (L := S.L) (N₀ := N₁ * S.L ^ m₁) (k := k' + 1) b0 w).card : ℝ) + (CEt + E * ((N : ℝ) / 2 * (4 * (Kw * cF S.d S.L) + (Kw * cF S.d S.L) ^ 2)) *
          (Real.exp (gammaW S.d * (2 * S.d + 1)) * countConst S.d S.L (gammaW S.d))) *
        (D0 : ℝ) ^ S.d + Cnat * S.lam (k' + 1) ^ (2 * S.d + 1) + 4 + Ckk) := by
  have hq1 := removedFactor_le_restricted hprec ψ0 h Du D Zr Zk1 Zb ϖ aN ψk hβ0 hν ha₁ hL ha haN hZb hDat
    hDu hφu hφ hid hA0 hb hst hnu hd hk b0 w hw1 hwD hm hXreg hΩ hdata Hbg hδ hδc hψout hp0 hrad hψ0 Ckk
  have hd0 : 0 < S.d := by omega
  have hγ : 0 < gammaW S.d := gammaW_pos' hd0
  have hβk : 0 < betaK S.d S.L (k' + 1) β0 := by
    unfold betaK
    have : (0 : ℝ) < S.L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne S.L)
    positivity
  have hR1 := removed_margin_arith ok hRfl hγ hlogβ hxl
  have hZr := hZr_removed Hh hkK Zc hq G Zr b0 w hbx hZrsites
  have hmargin := hmargin_removed_uncapped Hh hkK Zc hq G Zr b0 w hbx hZrsites hR1
  have hb2 := (denominatorRestricted_bounds_of_margin_of_weighted G (compWeight S.L a₁) hd hk b0 w hw1 hwD hm
    hXreg hΩ hdata Hbg hWP hKw hOp hsep2 hδ hδc hψout Zr hν h hh1 ha hβ0 hp0 hrad hsmall hρs hZr hmargin).2
  have hD1 : 1 ≤ D0 := (hw1 ⟨0, hd0⟩).trans (hwD _)
  have hK : 0 < psiZeroK N G (compWeight S.L a₁) hd hk b0 w hw1 hwD hm hXreg hΩ hdata Hbg :=
    psiZeroK_pos N G (compWeight S.L a₁) hd hk b0 w hw1 hwD hm hXreg hΩ hdata Hbg
  have hC6 := cSix_pos hd0 hD1 hK.le
  have hρ0 := zeroRadius_pos hC6 hβk hp0
  have hρ1 : zeroRadius (cSix S.d D0 (psiZeroK N G (compWeight S.L a₁) hd hk b0 w hw1 hwD hm hXreg hΩ hdata Hbg))
      (betaK S.d S.L (k' + 1) β0) p0 ≤ 1 :=
    hρs.trans ((min_le_left _ _).trans deltaStar_le_one)
  have hκ1 := hsmall.trans ((min_le_left _ _).trans deltaStar_le_one)
  have hκ0 : 0 ≤ bgK1 S.d S.L N * (psiZeroK N G (compWeight S.L a₁) hd hk b0 w hw1 hwD hm hXreg hΩ hdata Hbg * δ) :=
    mul_nonneg (bgK1_pos S.d S.L N).le (mul_nonneg hK.le hδ.le)
  have hE := removed_E_arith (d := S.d) (N := N) (βk := betaK S.d S.L (k' + 1) β0) (γ := gammaW S.d)
    (R := 2 / gammaW S.d * Real.log (betaK S.d S.L (k' + 1) β0))
    (e2 := Real.exp (2 * S.d * gammaW S.d))
    (cst := Real.exp (gammaW S.d / 2 * (2 * S.d + 1)) * countConst S.d S.L (gammaW S.d / 2)) hβk hγ rfl hκ0 hκ1 hρ0.le hρ1 hKw
    (cF_pos S.d S.L).le (Real.exp_pos _).le
    (mul_nonneg (Real.exp_pos _).le ((by unfold countConst; exact tsum_nonneg fun m => by positivity)))
    (Nat.cast_nonneg _) (card_boxFinset_le b0 w hwD)
  have hmass0 : 0 ≤ β0 * ν * ((S.L : ℝ) ^ (k' + 1)) ^ S.d := by positivity
  have hβν' : β0 * ν * ((S.L : ℝ) ^ (k' + 1)) ^ S.d ≤ E := by
    rw [← betaK_mul_nu_scaled_eq hd]
    exact hβν
  have hmassBound := removed_mass_arith (N := N) (mass := β0 * ν * ((S.L : ℝ) ^ (k' + 1)) ^ S.d)
    (E := E)
    (ρ := zeroRadius (cSix S.d D0 (psiZeroK N G (compWeight S.L a₁) hd hk b0 w hw1 hwD hm
      hXreg hΩ hdata Hbg)) (betaK S.d S.L (k' + 1) β0) p0)
    (Kw := Kw) (cF := cF S.d S.L)
    (cst := Real.exp (gammaW S.d * (2 * S.d + 1)) * countConst S.d S.L (gammaW S.d))
    (card := ((boxFinset (L := S.L) (N₀ := N₁ * S.L ^ m₁) (k := k' + 1) b0 w).card : ℝ))
    (Dd := (D0 : ℝ) ^ S.d) hmass0 hβν' hρ0.le hρ1 hKw (cF_pos S.d S.L).le
    (mul_nonneg (Real.exp_pos _).le ((by unfold countConst; exact tsum_nonneg fun m => by positivity)))
    (Nat.cast_nonneg _) (card_boxFinset_le b0 w hwD)
  refine hq1.trans (Real.exp_le_exp.2 ?_)
  have := neg_abs_le (tildeE0Restricted G (compWeight S.L a₁) hd hk b0 w hw1 hwD hm hXreg hΩ hdata Hbg hδ hδc hψout
    Zr ν h β0 p0)
  have hDd : 0 ≤ (D0 : ℝ) ^ S.d := by positivity
  have hCEtD := mul_le_mul_of_nonneg_right hCEt hDd
  have hOld := (add_le_add_left hE (cTildeE N S.d D0 * (D0 : ℝ) ^ S.d)).trans (by
    convert hCEtD using 1; ring)
  nlinarith only [hb2, hOld, hmassBound, hnat, this]

end Quotient

end Balaban.LargeField
