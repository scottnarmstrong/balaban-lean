/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.DetCauchyChart
public import Balaban.Inhabited.StepActivityDirectWitness
public import Balaban.Inhabited.XiCDomains
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The hypotheses of `DetCauchyChart` have an instance with `e^κ > 2`

At `d = L = 3`, `N = 2` the tower `directWitness_core_amp` supplies, at one choice of
`(m₁, c, BG, κ, t, δc)`, the physical-chart hypotheses `FlCore`, the cap
`cstarX e^{N0 κ} ≤ L^{m₁}`, the margins of `decDom_of_isDecBg`, and `δc² smallConstX ≤ 1/4`
together.  With a datum of the chart `Ξ^c` and the unit lattice this gives
`detCauchyChart_hypotheses_nonempty`: the conclusions of `rootTraceBg_cut_expansion` (and the
analyticity of `analyticOnNhd_rootTraceBg`) hold at an instance whose geometric factor
`2 / e^κ` is `< 1`.
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation
  Balaban.Localization Balaban.Localization.LevelPair Balaban.Localization.I5Inhabited
  Balaban.Analysis

/-- **Non-vacuity of `DetCauchyChart`**: there are `m₁`, constants, a datum `D` of the chart
`Ξ^c` on the generating set `Gp m₁ (rhoSep m₁)` and a `FlCore` with `e^κ > 2` for which all the
hypotheses of `rootTraceBg_cut_expansion` hold (including `cstarX e^{N0 κ} ≤ L^{m₁}`, the two
margins of `decDom_of_isDecBg` and `δc² smallConstX ≤ 1/4`), and the conclusion holds for the
block `B = ` all of the unit lattice. -/
theorem detCauchyChart_hypotheses_nonempty :
    ∃ (m₁ : ℕ) (c BG κ t c₂ BG₂ δc : ℝ),
      Nonempty (FlCore 2 (Gp m₁ (rhoSep m₁)) (Hm m₁ (rhoSep m₁)) 1 nuW c BG κ t (levelKc 3 3)
        (Cchi 3 3) c₂ BG₂ t) ∧ 2 < Real.exp κ ∧ 0 ≤ δc ∧
      cstarX 3 3 * Real.exp (N0 3 3 * κ) ≤ ((3 : ℕ) : ℝ) ^ m₁ ∧
      decDomMargin 3 3 2 BG κ (xiC1 3 * t) < δc ∧
      K4 3 3 2 BG κ * (xiC1 3 * t) < coerciveConst 3 / 2 ∧
      δc ^ 2 * smallConstX 3 3 κ ≤ 1 / 4 ∧
      ∃ D : BgData (Gp m₁ (rhoSep m₁)) 2, XiCData (Gp m₁ (rhoSep m₁)) (compWeight 3 1) nuW
          (1 + 1) 1 t D ∧
        rootTraceBg (Gp m₁ (rhoSep m₁)) (compWeight 3 1) 1 nuW (rho4 3 3 2 BG κ)
            (unitQ (Gp m₁ (rhoSep m₁))) (unitP (Gp m₁ (rhoSep m₁))) Finset.univ D
            (fun _ => 1) =
          ∑ J ∈ (Finset.univ : Finset (cubeIdx (Gp m₁ (rhoSep m₁)))).powerset,
            mixDiff J (rootTraceBg (Gp m₁ (rhoSep m₁)) (compWeight 3 1) 1 nuW
              (rho4 3 3 2 BG κ) (unitQ (Gp m₁ (rhoSep m₁))) (unitP (Gp m₁ (rhoSep m₁)))
              Finset.univ D) ∧
        ∀ J : Finset (cubeIdx (Gp m₁ (rhoSep m₁))),
          ‖mixDiff J (rootTraceBg (Gp m₁ (rhoSep m₁)) (compWeight 3 1) 1 nuW
              (rho4 3 3 2 BG κ) (unitQ (Gp m₁ (rhoSep m₁))) (unitP (Gp m₁ (rhoSep m₁)))
              Finset.univ D)‖ ≤
            (1 / 2 : ℝ) * 2 * (Finset.univ : Finset (unitPts (Gp m₁ (rhoSep m₁)))).card *
              covBLog 3 3 (compWeight 3 1 1) (1 / (3 : ℝ) ^ 2) κ * (2 / Real.exp κ) ^ J.card := by
  obtain ⟨m₁, c, BG, κ, t, c₂, BG₂, κdec, κ0, δc, h4, ht0, ⟨hC⟩, hκ0, hκdec, hκ, h1, hlog, hc7,
    hMX, hdm, hα, hsmX, -⟩ := directWitness_core_amp 2 1
  have hκ6 : 6 ≤ κ := by linarith
  have h2 : 2 < Real.exp κ := by linarith [Real.add_one_le_exp κ]
  have hd0 : 0 < (3 : ℕ) := by norm_num
  have hδc : 0 ≤ δc := by
    have : 0 ≤ decDomMargin 3 3 2 BG κ (xiC1 3 * t) := by
      have : 0 < K4 3 3 2 BG κ := K4_pos hC.hS.fam.2.1 hd0
      have := one_le_xiC1 3
      unfold decDomMargin; positivity
    linarith
  obtain ⟨D, hD⟩ := exists_xiCData (N := 2) (bgHypNu m₁) (Gp m₁ (rhoSep m₁)) (by norm_num)
    (by unfold nuW; norm_num) ht0
  refine ⟨m₁, c, BG, κ, t, c₂, BG₂, δc, ⟨hC⟩, h2, hδc, hMX, hdm, hα, hsmX, D, hD, ?_⟩
  have := rootTraceBg_cut_expansion (Q := unitQ (Gp m₁ (rhoSep m₁)))
    (P := unitP (Gp m₁ (rhoSep m₁))) hC (le_refl 1) hδc hMX hsmX hdm hα
    (isUnitLatticeB_unit (G := Gp m₁ (rhoSep m₁))).toIsUnitLattice Finset.univ hD
  simpa using this

end Balaban.Inhabited
