/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.MarkedRootAssembly
public import Balaban.Inhabited.MarkRealDiscSlice
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The marked root assembly at every scale of the shared tower (`d = L = 3`, `N = 2`)

`StepSetting.markedRootAssembly_zero` applies, with all its hypotheses discharged, at the step
`T.step k hk N₁ ν β p₁ = hatStepK k T.m₁ hk ν β p₁ T.δ` of every scale of a shared tower
`T : StepTower κmin` for which the per-scale record `StepScaleData` holds (it is inhabited at every
admissible scale beyond one threshold of `β`, `StepTower.scale`):

* the cover data are the block covers of `StepScaleData.covers` (`m₀ = 1`, `j = k`), with
  `hatConn_lvTop` and `rowInHat_lv`;
* the rates and the numerical inequalities are fields of `StepTower`;
* the radii are those of `MarkRealDiscSlice`: `R₁ = R_σ = 17/16`, `t₁ = 1/16`, `t₀ = 1/32` and the
  radial radius `r = lvR/4` (the formula is fixed before the scale; its value depends on `β_k` and
  `p₁`); the radial margin is `StepScaleData.marked_radius_lt`;
* `MARK-REAL` is supplied on the whole constant-`h₀` slice by `markRealAt_of_chart` (with `R = 2`,
  `p⁺ = lvCpsi`).

`markedRootAssembly_zero_fromTower` returns one family `Ev` of block terms and one matrix function
`M` of the raw data, for all marked blocks `z` and all hat fields `‖ψ̂‖ ≤ p₁`;
`markedRootAssembly_zero_fromTower_nonempty` records that its hypotheses hold at `k = 1`, `N₁ = 6`.

Zero class only.  The marks are functions of `(e, u)` at a fixed hat field; continuity and
measurability in the configuration, the clamped extension, the common label system and the
`E1MarksC` inhabitant are NOT constructed here.  Nothing depends on a choice of generating sets
for the class terms.
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation
  Balaban.Localization Balaban.Localization.LevelPair Balaban.Localization.I5Inhabited
  Balaban.Polymer Balaban.SmallField.Def6 Balaban.Inhabited.LevelStep Matrix Metric

open Classical in
/-- **The root assembly of the marked terms of the zero class at a scale of the shared tower.**
Let `T` be a tower, `S = T.step k hk N₁ ν β p₁` the step of a scale with `StepScaleData`,
`5 < N₁`, `0 ≤ ν`, `ν 3^{2(k+1)} ≤ 1`, `β > 0`, `p₁ > 0`.  There are one family `Ev` of block terms
and one matrix function `M` of the raw data, with entries analytic on the chart
`Ξ^c(𝔹_{k+1}; 1, T.t)`, such that `β_k^{-1/2} M(rawOf D) ψ̂` is the shift `shiftUC ψ̂` of the step
with the datum `D` for every datum of the chart with `D.h = h₀`, and such that for every marked
block `z` and every hat field `‖ψ̂‖ ≤ p₁`, with the tangent `Q(Θ) = β_k^{-1/2} M(Θ) ψ̂`:

* `MARK-REAL` holds at every datum of the constant-`h₀` slice (`MarkRealAt` with ball radius `T.t`
  and disc radius `2`);
* the clauses of `MarkedRootFamily` hold on `physV × {|u| < 17/16}` (the rooted sums are analytic
  in `(e, u)`, bounded and anchored at every point, and equal to the rooted sums of the step with
  the datum on the slice);
* the clauses of `MarkedRootAssembly` hold for the marks `G_{z,Y'}(e, u) = -β · markedOut z Y'`:
  analyticity in `(e, u)`, the bound `F₀ e^{-(2κ_dec-1) d(Y')}` with
  `F₀ = |β| · 3‖E*‖/(r³ t₀) · c₁ M^d · nFibre · e^{(2κ_dec-1) cBr}`, `r = lvR/4`, `t₀ = 1/32`, the
  root and domain clause, and on the slice the finite sum equal to the integrand of `E1MarksC`.

The radii `17/16`, `1/16`, `1/32` and the constants of `T` are chosen before the scale. -/
theorem markedRootAssembly_zero_fromTower {κmin : ℝ} (T : StepTower κmin) {k : ℕ} {hk : 1 ≤ k}
    {N₁ : ℕ} [NeZero N₁] {ν β p₁ : ℝ} (D : StepScaleData T k hk N₁ ν β p₁) (hN : 5 < N₁)
    (hν0 : 0 ≤ ν) (hν : ν * 3 ^ (2 * (k + 1)) ≤ 1) (hβ : 0 < β) (hp : 0 < p₁)
    {S : StepSetting 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)} (hS : S = T.step k hk N₁ ν β p₁) :
    ∃ (Ev : Torus 3 (N₁ * 3 ^ T.m₁ * 3 ^ (k + 1 - (k + 1))) → Set (CTorus 3 3 N₁ T.m₁ (k + 1)) →
        RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2 × (CTorus 3 3 N₁ T.m₁ (k + 1) → Fin 2 → ℂ) → ℂ)
      (M : RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2 → Matrix (S.U × Fin 2) (S.U × Fin 2) ℂ),
      (∀ p q, AnalyticOnNhd ℂ (fun Θ => M Θ p q)
        (XiCRaw S.G' (compWeight 3 1) ν (k + 1) 1 T.t)) ∧
      (∀ (D' : BgData S.G' 2) (hD' : ∀ y i, D'.h y i = (S.h₀ i : ℂ)),
        XiCData S.G' (compWeight 3 1) ν (k + 1) 1 T.t D' → ∀ x : S.E,
        (((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) • (M (rawOf D') *ᵥ yhat x) =
          (S.withDatum D' hD').shiftUC x) ∧
      ∀ (z : Torus 3 (N₁ * 3 ^ T.m₁ * 3 ^ (k + 1 - (k + 1)))) (x : S.E), ‖x‖ ≤ p₁ →
        (∀ (D' : BgData S.G' 2) (hD' : ∀ y i, D'.h y i = (S.h₀ i : ℂ)),
          XiCData S.G' (compWeight 3 1) ν (k + 1) 1 T.t D' →
          (S.withDatum D' hD').MarkRealAt T.t 2 x) ∧
        S.MarkedRootFamily z 1
          (fun b => polyDom S.G' (LocalCover.nbhdF 1 (LocalCover.blockSite k b)) 1 k
            (LocalCover.fam 1 (LocalCover.blockSite k b))) Ev 1 ν T.t (17 / 16)
          (fun Θ => (((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) • (M Θ *ᵥ yhat x))
          (3 * ‖energyBdScaled 3 3 2 (compWeight 3 1) k
              (cK2' 3 3 2 (famConst 3 3 T.BG₂ T.κ) * T.t) T.t (rho4 3 3 2 T.BG T.κ)‖ /
              ((lvR T.κ T.t (β * 3 ^ k) p₁ / 4) ^ 3 * (1 / 32)) *
            (c1 3 3 * (((3 : ℕ) : ℝ) ^ (1 + T.m₁)) ^ 3) *
            ((nFibre 3 3 : ℝ) * Real.exp ((2 * T.κdec - 1) * cBr 3 3))) (2 * T.κdec - 1) ∧
        S.MarkedRootAssembly z 1
          (fun b => polyDom S.G' (LocalCover.nbhdF 1 (LocalCover.blockSite k b)) 1 k
            (LocalCover.fam 1 (LocalCover.blockSite k b))) Ev T.t (17 / 16)
          (fun Θ => (((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) • (M Θ *ᵥ yhat x))
          (|β| * (3 * ‖energyBdScaled 3 3 2 (compWeight 3 1) k
              (cK2' 3 3 2 (famConst 3 3 T.BG₂ T.κ) * T.t) T.t (rho4 3 3 2 T.BG T.κ)‖ /
              ((lvR T.κ T.t (β * 3 ^ k) p₁ / 4) ^ 3 * (1 / 32)) *
            (c1 3 3 * (((3 : ℕ) : ℝ) ^ (1 + T.m₁)) ^ 3) *
            ((nFibre 3 3 : ℝ) * Real.exp ((2 * T.κdec - 1) * cBr 3 3)))) (2 * T.κdec - 1) := by
  classical
  subst hS
  obtain ⟨hV, -⟩ := D.covers
  have hr0 := D.r_pos
  have hlt : p₁ < lvCpsi T.κ T.t (β * 3 ^ k) := by
    have h := mul_le_mul_of_nonneg_right
      (show (1 : ℝ) ≤ 2 * 2 + lvR T.κ T.t (β * 3 ^ k) p₁ by linarith) hp.le
    linarith [D.ray_margin]
  have hδ₁ : Real.sqrt ((2 : ℕ) : ℝ) * ((T.step k hk N₁ ν β p₁).betaU ^ (-(1 / 2 : ℝ)) *
      (covSupConstC 3 3 2 (compWeight 3 (1 : ℝ) k) T.κ * lvCpsi T.κ T.t (β * 3 ^ k))) < T.t := by
    rw [← (T.step k hk N₁ ν β p₁).norm_betaU_rpow hβ.le]
    exact D.fl_radius
  obtain ⟨Ev, M, -, -, -, -, hMan, hfib, hall⟩ :=
    (T.step k hk N₁ ν β p₁).markedRootAssembly_zero
      (jV := fun _ => k) (XV := fun z => LocalCover.cube 1 k (LocalCover.blockSite k z))
      (𝒦XV := fun z => LocalCover.fam 1 (LocalCover.blockSite k z))
      (X₁V := fun z => LocalCover.nbhdF 1 (LocalCover.blockSite k z)) (m₀ := 1) (R := 2)
      (pp := lvCpsi T.κ T.t (β * 3 ^ k)) (R₁ := 17 / 16) (Rσ := 17 / 16)
      (r := lvR T.κ T.t (β * 3 ^ k) p₁ / 4) (t₁ := 1 / 16) (t₀ := 1 / 32) (δc := T.δc)
      D.core (fun z => (hV z).1) (fun z => (hV z).2.1) hatConn_lvTop
      (rowInHat_lv hk T.m₁_four hN hν0 hν) (fun z => (hV z).2.2.1) (fun z => (hV z).2.2.2.1)
      T.κ0_nonneg T.κdec_lower (by exact_mod_cast T.κ_lower) T.κ_one T.κ_log
      (fun z => (hV z).2.2.2.2.1) (fun z => (hV z).2.2.2.2.2.1) (by norm_num)
      T.large_block T.dom_margin T.coer_margin T.δc_small one_pos T.c7_cap le_rfl T.t_cap
      T.bg0_cap T.cK2_cap T.cK2'_cap T.bg1_cap hβ hδ₁ hlt hp.le (D.marked_radius_lt hp)
      (by norm_num) (by linarith) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨Ev, M, hMan, hfib, fun z x hx => ?_⟩
  obtain ⟨-, hMR, hfam, hasm⟩ := hall z x hx
  exact ⟨hMR, hfam, hasm⟩

/-- **Non-vacuity of `markedRootAssembly_zero_fromTower`**: for every tower, at `k = 1`, `N₁ = 6`,
`ν = 0`, `p₁ = 1`, `β = βray` the record `StepScaleData` is inhabited (`StepTower.scale_instance`),
the remaining hypotheses are numerical, and `MARK-REAL` holds at the datum of the step for the
hat field `ψ̂ = 0`. -/
theorem markedRootAssembly_zero_fromTower_nonempty {κmin : ℝ} (T : StepTower κmin) :
    ∃ βray : ℝ, 2 ≤ βray ∧ Nonempty (StepScaleData T 1 le_rfl 6 0 βray 1) ∧
      (T.step 1 le_rfl 6 0 βray 1).MarkRealAt T.t 2 0 := by
  obtain ⟨βray, h2, ⟨hS⟩⟩ := T.scale_instance
  obtain ⟨Ev, M, -, -, hall⟩ := markedRootAssembly_zero_fromTower T hS (by norm_num) le_rfl
    (by norm_num) (by linarith) one_pos rfl
  obtain ⟨hMR, -, -⟩ := hall 0 0 (by simp)
  exact ⟨βray, h2, ⟨hS⟩,
    hMR (T.step 1 le_rfl 6 0 βray 1).D' (T.step 1 le_rfl 6 0 βray 1).hh₀ hS.xi⟩

end Balaban.Inhabited
