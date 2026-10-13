/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.DecMarkTotal
public import Balaban.Inhabited.MarkedRootAssemblyFromTower
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The decoupled marks and the physical mark at every scale of the shared tower

`StepSetting.sum_markedOutDec_physical` at the step `(T.step k hk N₁ ν β p₁).withDatum D' hDh` of
a scale of a shared tower `T : StepTower κmin` with `StepScaleData`, every hypothesis discharged
as in `markedRootAssembly_zero_fromTower` (block covers of `StepScaleData.covers`, `m₀ = 1`,
`j = k`; radii `R₁ = 17/16`, `t₁ = 1/16`, `t₀ = 1/32`, `r = lvR/4`, `R = 2`; `MARK-REAL` by
`markRealAt_of_chart`; the marked disc by `markReal_disc_slice`).  Zero class.
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation
  Balaban.Localization Balaban.Localization.LevelPair Balaban.Localization.I5Inhabited
  Balaban.Polymer Balaban.SmallField.Def6 Balaban.Inhabited.LevelStep Matrix Metric Set

open Classical in
/-- **The decoupled marks sum to the physical mark plus the quadratic-form term, at every scale of
the tower.**  See `StepSetting.sum_markedOutDec_physical`; the datum `D'` is any datum of the
chart with `h = h₀`, the hat field satisfies `‖x‖ ≤ p₁`, `s ∈ [0,1]`, `z` any root. -/
theorem sum_markedOutDec_physical_fromTower {κmin : ℝ} (T : StepTower κmin) {k : ℕ} {hk : 1 ≤ k}
    {N₁ : ℕ} [NeZero N₁] {ν β p₁ : ℝ} (D : StepScaleData T k hk N₁ ν β p₁) (hN : 5 < N₁)
    (hν0 : 0 ≤ ν) (hν : ν * 3 ^ (2 * (k + 1)) ≤ 1) (hβ : 0 < β) (hp : 0 < p₁)
    (D' : BgData (T.step k hk N₁ ν β p₁).G' 2)
    (hDh : ∀ y i, D'.h y i = ((T.step k hk N₁ ν β p₁).h₀ i : ℂ))
    (hD : XiCData (T.step k hk N₁ ν β p₁).G' (compWeight 3 1) ν (k + 1) 1 T.t D')
    {S : StepSetting 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)}
    (hS : S = (T.step k hk N₁ ν β p₁).withDatum D' hDh)
    (x : S.E) (hx : ‖x‖ ≤ p₁) (z : Torus 3 (N₁ * 3 ^ T.m₁ * 3 ^ (k + 1 - (k + 1)))) {s : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) :
    ∃ (F₁ : Torus 3 (N₁ * 3 ^ T.m₁ * 3 ^ (k + 1 - (k + 1))) →
        DecParams S.G' × RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2 →
          (S.G'.Ω 1 × Fin 2 → ℂ) × (S.G'.Ω 1 → ℂ))
      (Sol : Torus 3 (N₁ * 3 ^ T.m₁ * 3 ^ (k + 1 - (k + 1))) →
        Dec2.DecParams (coverOf S.G') × Edat (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) 2 →
          ((stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)).Ω 1 × Fin 2 → ℂ) ×
            ((stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)).Ω 1 → ℂ)),
      deriv (fun t : ℂ => ∑ b : Torus 3 (N₁ * 3 ^ T.m₁ * 3 ^ (k + 1 - (k + 1))),
        markedFunDec S.hG' ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) S.a₁ S.ν T.BG₂ T.κ (S.blockU z)
          (s : ℂ) t (blockEnergyFun S.G' (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) (compWeight 3 S.a₁)
            S.ν k b) S.D' (yhat x)) 0 =
        ∑ Y' ∈ bridgeFamily 1 (fun _ => Set.univ)
            (fun b => polyDom S.G' (LocalCover.nbhdF 1 (LocalCover.blockSite k b)) 1 k
              (LocalCover.fam 1 (LocalCover.blockSite k b))) z,
          markedOutDec 1 (fun _ => Set.univ)
            (fun b => polyDom S.G' (LocalCover.nbhdF 1 (LocalCover.blockSite k b)) 1 k
              (LocalCover.fam 1 (LocalCover.blockSite k b))) z
            (evDecFam (fun b => LocalCover.nbhdF 1 (LocalCover.blockSite k b)) (fun _ => k)
              (fun b => LocalCover.fam 1 (LocalCover.blockSite k b)) 1 S.a₁ S.ν S.hG'
              ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) F₁ Sol (S.blockU z) (s : ℂ)
              (rawOf S.D', yhat x)) Y' ∧
      (fderiv ℂ (S.Phi1C (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁))) ((s : ℂ) • S.shiftUC x))
          (S.maskUC z (S.shiftUC x)) =
        -(S.β : ℂ) * ∑ Y' ∈ bridgeFamily 1 (fun _ => Set.univ)
            (fun b => polyDom S.G' (LocalCover.nbhdF 1 (LocalCover.blockSite k b)) 1 k
              (LocalCover.fam 1 (LocalCover.blockSite k b))) z,
          markedOutDec 1 (fun _ => Set.univ)
            (fun b => polyDom S.G' (LocalCover.nbhdF 1 (LocalCover.blockSite k b)) 1 k
              (LocalCover.fam 1 (LocalCover.blockSite k b))) z
            (evDecFam (fun b => LocalCover.nbhdF 1 (LocalCover.blockSite k b)) (fun _ => k)
              (fun b => LocalCover.fam 1 (LocalCover.blockSite k b)) 1 S.a₁ S.ν S.hG'
              ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) F₁ Sol (S.blockU z) (s : ℂ)
              (rawOf S.D', yhat x)) Y' +
        ((S.β : ℂ) / 2) * deriv (fun t : ℂ =>
          deltaForm (S.hG.precedes S.hG' (le_refl (k + 1))) (compWeight 3 S.a₁) S.ν
            (bgMultC S.G' (compWeight 3 S.a₁) S.ν (bgC0 3 3 2) S.D')
            (bgFieldC S.G' (compWeight 3 S.a₁) S.ν (bgC0 3 3 2) S.D')
            (liftC S.hG' (S.markedTangentC z (s : ℂ) t x))) 0 := by
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
  have hmem := compWeight_three_mem hk
  have hCs : 0 ≤ covSupConstC 3 3 2 (compWeight 3 (1 : ℝ) k) T.κ :=
    covSupConstC_nonneg (by norm_num) (by norm_num) (by linarith [hmem.1]) T.κ
  have hmr : 0 ≤ markedRad 3 3 2 k 1 T.κ p₁
      ((((T.step k hk N₁ ν β p₁).betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) := by
    unfold markedRad
    exact mul_nonneg (Real.sqrt_nonneg _) (mul_nonneg (norm_nonneg _) (mul_nonneg hCs hp.le))
  have hs1 : ‖(s : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs.1]; exact hs.2
  have hrad : (‖(s : ℂ)‖ + 1 / 32) * markedRad 3 3 2 k 1 T.κ p₁
      ((((T.step k hk N₁ ν β p₁).betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) < T.t := by
    refine lt_of_le_of_lt (mul_le_mul_of_nonneg_right ?_ hmr) (D.marked_radius_lt hp)
    nlinarith [hr0]
  have hu : ‖(s : ℂ)‖ < 17 / 16 := lt_of_le_of_lt hs1 (by norm_num)
  have hdisc := markReal_disc_slice T D hp D' hDh hD hx z hu
  have hMR := ((T.step k hk N₁ ν β p₁).withDatum D' hDh).markRealAt_of_chart D.core T.large_block
    T.dom_margin T.coer_margin T.δc_small one_pos T.c7_cap (R := 2) (by norm_num) T.bg1_cap hβ
    D.cψ_pos hδ₁ hlt hD hx
  exact ((T.step k hk N₁ ν β p₁).withDatum D' hDh).sum_markedOutDec_physical z
    (jV := fun _ => k) (XV := fun b => LocalCover.cube 1 k (LocalCover.blockSite k b))
    (𝒦XV := fun b => LocalCover.fam 1 (LocalCover.blockSite k b))
    (X₁V := fun b => LocalCover.nbhdF 1 (LocalCover.blockSite k b)) (m₀ := 1)
    D.core hk T.large_block T.dom_margin T.coer_margin T.δc_small
    (fun b => (hV b).1) (fun b => (hV b).2.1) hatConn_lvTop
    (rowInHat_lv hk T.m₁_four hN hν0 hν) (fun b => (hV b).2.2.1) (fun b => (hV b).2.2.2.1)
    T.κ0_nonneg T.κdec_lower (by exact_mod_cast T.κ_lower) T.κ_one T.κ_log
    (fun b => (hV b).2.2.2.2.1) (fun b => (hV b).2.2.2.2.2.1) (by norm_num) one_pos T.c7_cap
    (R := 2) le_rfl T.t_cap T.bg0_cap T.cK2_cap T.cK2'_cap hD hβ hp.le (by norm_num)
    (by linarith) (by norm_num) (by norm_num) x hx hs hrad hdisc hMR

end Balaban.Inhabited
