/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.DetCauchyBgActivity
public import Balaban.Inhabited.StepActivityDirectWitness
public import Balaban.Inhabited.XiCDomains
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Non-vacuity of `DetCauchyBgSupport` and `DetCauchyBgActivity`

At `d = L = 3`, `N = 2`, `k = 1` the tower `directWitness_core_amp` supplies, at one choice of
`(m₁, c, BG, κ, t, δc)`, the chart hypotheses `FlCore`, the cap `cstarX e^{N0 κ} ≤ L^{m₁}`, the
margins of `decDom_of_isDecBg` and `δc² smallConstX ≤ 1/4` together, with `κ ≥ 12348`.  The rate
condition `e^κ > 2 (detDeg 3 3 + 1)²` of the activity theorems needs `κ > 39.1`
(`detDeg 3 3 + 1 = 214991878`), so it holds at this instance (`detDeg_three_rate`): the chart
hypotheses and the rate condition have a common landed instance.  With `HatConn` of the
whole-lattice generating set (`LevelPair.hatConn`), a datum of the chart and a unit block, all the
hypotheses of the support, activity, decay and locality theorems hold simultaneously
(`detCauchyBgActivity_nonempty`).
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation
  Balaban.Localization Balaban.Localization.LevelPair Balaban.Localization.I5Inhabited
  Balaban.Analysis Balaban.SmallField.Def6

/-- `detDeg 3 3 + 1 = 214991878`. -/
theorem detDeg_three_succ : detDeg 3 3 + 1 = 214991878 := by
  norm_num [detDeg, N0]

/-- **The rate condition at `d = L = 3`**: `(detDeg 3 3 + 1)² · 2 / e^κ < 1` for `κ ≥ 57`
(`2 (detDeg 3 3 + 1)² < 2^57 ≤ e^57`). -/
theorem detDeg_three_rate {κ : ℝ} (hκ : 57 ≤ κ) :
    ((detDeg 3 3 + 1 : ℕ) : ℝ) ^ 2 * (2 / Real.exp κ) < 1 := by
  have h2 : (2 : ℝ) ≤ Real.exp 1 := by
    have := Real.add_one_le_exp (1 : ℝ); linarith
  have hexp : (2 : ℝ) ^ 57 ≤ Real.exp κ := by
    calc (2 : ℝ) ^ 57 ≤ (Real.exp 1) ^ 57 := pow_le_pow_left₀ (by norm_num) h2 57
      _ = Real.exp 57 := by rw [← Real.exp_nat_mul]; norm_num
      _ ≤ Real.exp κ := Real.exp_le_exp.2 hκ
  rw [detDeg_three_succ, mul_div_assoc', div_lt_one (Real.exp_pos κ)]
  calc ((214991878 : ℕ) : ℝ) ^ 2 * 2 < (2 : ℝ) ^ 57 := by norm_num
    _ ≤ Real.exp κ := hexp

/-- **Non-vacuity of the support, activity, decay and locality theorems with cut-dependent
backgrounds.**  There are `m₁`, constants, a `FlCore` on the whole-lattice generating sets
`(Gp m₁ ϱ, Hm m₁ ϱ)`, a datum `D` of the chart `Ξ^c` and a unit block `y` at which the chart
hypotheses (`FlCore`, `HatConn`, the cap, the margins, `δc² smallConstX ≤ 1/4`) and the rate
condition `(detDeg 3 3 + 1)² · 2 / e^κ < 1` hold together, and the conclusions hold: root-chain
support of the mixed differences, resummation to the rooted trace at the uncut background,
support of the activities on polymers containing the root cube, exponential decay, and locality
of the activities in the datum. -/
theorem detCauchyBgActivity_nonempty :
    ∃ (m₁ : ℕ) (c BG κ t c₂ BG₂ δc : ℝ),
      Nonempty (FlCore 2 (Gp m₁ (rhoSep m₁)) (Hm m₁ (rhoSep m₁)) 1 nuW c BG κ t (levelKc 3 3)
        (Cchi 3 3) c₂ BG₂ t) ∧ HatConn (Gp m₁ (rhoSep m₁)) ∧ 0 ≤ δc ∧
      cstarX 3 3 * Real.exp (N0 3 3 * κ) ≤ ((3 : ℕ) : ℝ) ^ m₁ ∧
      δc ^ 2 * smallConstX 3 3 κ ≤ 1 / 4 ∧
      decDomMargin 3 3 2 BG κ (xiC1 3 * t) < δc ∧
      K4 3 3 2 BG κ * (xiC1 3 * t) < coerciveConst 3 / 2 ∧
      ((detDeg 3 3 + 1 : ℕ) : ℝ) ^ 2 * (2 / Real.exp κ) < 1 ∧
      ∃ (D : BgData (Gp m₁ (rhoSep m₁)) 2) (y : unitPts (Gp m₁ (rhoSep m₁))),
        XiCData (Gp m₁ (rhoSep m₁)) (compWeight 3 1) nuW (1 + 1) 1 t D ∧
        (∀ J : Finset (cubeIdx (Gp m₁ (rhoSep m₁))),
          mixDiff J (rootTraceBg (Gp m₁ (rhoSep m₁)) (compWeight 3 1) 1 nuW (rho4 3 3 2 BG κ)
            (unitQ (Gp m₁ (rhoSep m₁))) (unitP (Gp m₁ (rhoSep m₁))) {y} D) ≠ 0 →
          ∀ p ∈ J, ∃ q, RootChain (Gp m₁ (rhoSep m₁)) J y q ∧
            p ∈ QsetP (Gp m₁ (rhoSep m₁)) q) ∧
        rootTrace (Gp m₁ (rhoSep m₁)) (compWeight 3 1) 1 nuW (unitQ (Gp m₁ (rhoSep m₁)))
            (unitP (Gp m₁ (rhoSep m₁))) {y} (fun _ => 1)
            (svec (Gp m₁ (rhoSep m₁))
              (bgFieldC (Gp m₁ (rhoSep m₁)) (compWeight 3 1) nuW (bgC0 3 3 2) D))
            (bgMultC (Gp m₁ (rhoSep m₁)) (compWeight 3 1) nuW (bgC0 3 3 2) D) =
          ∑ Y, detActivityBg 0 (compWeight 3 1) 1 nuW (rho4 3 3 2 BG κ) D y Y ∧
        (∀ Y, detActivityBg 0 (compWeight 3 1) 1 nuW (rho4 3 3 2 BG κ) D y Y ≠ 0 →
          rootCube (m₀ := 0) (rootIdxOf y) ∈ Y ∧ IsPolyDom 0 (1 + 1) (sitesOf Y)) ∧
        (∀ Y, ‖detActivityBg 0 (compWeight 3 1) 1 nuW (rho4 3 3 2 BG κ) D y Y‖ ≤
          (1 / 2 : ℝ) * (2 : ℕ) * covBLog 3 3 (compWeight 3 1 1) (1 / ((3 : ℕ) : ℝ) ^ 2) κ /
            (1 - ((detDeg 3 3 + 1 : ℕ) : ℝ) ^ 2 * (2 / Real.exp κ)) *
          Real.exp (-((κ - Real.log 2 - 2 * Real.log ((detDeg 3 3 + 1 : ℕ) : ℝ)) /
            (2 * (3 : ℕ) * (3 : ℕ))) * dExt Y)) ∧
        ∀ D₂ : BgData (Gp m₁ (rhoSep m₁)) 2,
          XiCData (Gp m₁ (rhoSep m₁)) (compWeight 3 1) nuW (1 + 1) 1 t D₂ →
          ∀ Y : Finset (CubeB (d := 3) (L := 3) (N₁ := 9) (m₁ := m₁) (K := 1 + 1) 0 (1 + 1)
            Set.univ),
          (∀ x : (Gp m₁ (rhoSep m₁)).Ω 1, (x : CTorus 3 3 9 m₁ (1 + 1)) ∈ sitesOf Y →
            ∀ z ∈ resDep (Gp m₁ (rhoSep m₁)) (x : CTorus 3 3 9 m₁ (1 + 1)),
              D.Ψ z = D₂.Ψ z ∧ (z ∈ (Gp m₁ (rhoSep m₁)).Ω 1 → D.h z = D₂.h z)) →
          detActivityBg 0 (compWeight 3 1) 1 nuW (rho4 3 3 2 BG κ) D y Y =
            detActivityBg 0 (compWeight 3 1) 1 nuW (rho4 3 3 2 BG κ) D₂ y Y := by
  classical
  obtain ⟨m₁, c, BG, κ, t, c₂, BG₂, κdec, κ0, δc, h4, ht0, ⟨hC⟩, hκ0, hκdec, hκ, h1, hlog, hc7,
    hMX, hdm, hα, hsmX, -⟩ := directWitness_core_amp 2 1
  have hκ57 : (57 : ℝ) ≤ κ := by
    have e : 4 * ((3 : ℕ) : ℝ) * (((2 * 3 + 1) ^ 3 : ℕ) : ℝ) = 4116 := by norm_num
    rw [e] at hκ
    linarith
  have hz := detDeg_three_rate hκ57
  have hd0 : 0 < (3 : ℕ) := by norm_num
  have hδc : 0 ≤ δc := by
    have : 0 ≤ decDomMargin 3 3 2 BG κ (xiC1 3 * t) := by
      have : 0 < K4 3 3 2 BG κ := K4_pos hC.hS.fam.2.1 hd0
      have := one_le_xiC1 3
      unfold decDomMargin; positivity
    linarith
  obtain ⟨D, hD⟩ := exists_xiCData (N := 2) (bgHypNu m₁) (Gp m₁ (rhoSep m₁)) (by norm_num)
    (by unfold nuW; norm_num) ht0
  have hconn : HatConn (Gp m₁ (rhoSep m₁)) := LevelPair.hatConn
  have hl0 : (0 : CTorus 3 3 9 m₁ (1 + 1)) ∈ (Gp m₁ (rhoSep m₁)).layer (1 + 1) := by
    rw [Gp_layer_two]; exact Finset.mem_univ _
  set y : unitPts (Gp m₁ (rhoSep m₁)) :=
    ⟨unitBlock (0 : CTorus 3 3 9 m₁ (1 + 1)), (mem_unitPts (Gp m₁ (rhoSep m₁))).2 ⟨0, hl0, rfl⟩⟩
    with hy
  have hN : (3 : ℕ) ^ 0 ∣ 9 := by norm_num
  refine ⟨m₁, c, BG, κ, t, c₂, BG₂, δc, ⟨hC⟩, hconn, hδc, hMX, hsmX, hdm, hα, hz, D, y, hD,
    ?_, ?_, ?_, ?_, ?_⟩
  · exact (rootTraceBg_single_cutSupport_and_bound hC (le_refl 1) hδc hMX hsmX hdm hα hconn hD
      y).1
  · exact sum_detActivityBg_eq_rootTrace (m₀ := 0) hC hD y
  · intro Y hY
    exact detActivityBg_ne_zero_imp (m₀ := 0) hC (le_refl 1) hδc hMX hsmX hdm hα hconn hD hN hY
  · intro Y
    exact norm_detActivityBg_le (m₀ := 0) hC (le_refl 1) hδc hMX hsmX hdm hα hconn hD hN y hz Y
  · intro D₂ hD₂ Y hdata
    exact detActivityBg_eq_of_agree (m₀ := 0) hC (le_refl 1) hδc hMX hsmX hdm hα hconn hD hD₂ hN
      y Y hdata

end Balaban.Inhabited
