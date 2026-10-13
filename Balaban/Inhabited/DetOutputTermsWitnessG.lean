/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.DetStepInstance
public import Balaban.Inhabited.LevelRayTower
public import Balaban.Inhabited.LevelLemmasGeneral
public import Balaban.Inhabited.StepTowerG
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The localized determinant family at every scale, general `d`, `L`, `N`

`detExpansionLocC_scale_of_towerG`: from the output of the numerical tower (the hypotheses are the
fields of `StepTowerG`), at the step `hatStepKG` of every scale `k ≥ 1`, every torus
`L ∣ N₁`, `5 < N₁` and every mass `0 ≤ ν`, `ν · L^{2(k+1)} ≤ 1`: the datum of the step is a datum
of the chart and for every `z` the record `DetExpansionLocC` has an element with the rate
`(κ - log 2 - 2 log (detDeg d L + 1)) / (2 d L)` and the constant
`L^d · ½ N covBLogMax d L κ / (1 - (detDeg d L + 1)² · 2 / e^κ)`, neither of which involves `k`,
`N₁`, `ν`, `β`, `p₁`, `δ` or `z`.  The fixed `d = L = 3`, `N = 2` theorem
`detExpansionLocC_scale_of_tower` is its corollary.

Also here (moved from `StepTower`): the transport `flCore_three_transport` of the fixed core to the
general level pair.
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation
  Balaban.Localization Balaban.Localization.LevelPair Balaban.Localization.I5Inhabited
  Balaban.Analysis Balaban.SmallField.Def6 Balaban.Polymer Balaban.Inhabited.LevelStep

/-- The general reference mass at `L = 3` is the landed mass `nuW = 1/81`. -/
theorem νref_three : νref 3 = nuW := by
  unfold νref nuW; norm_num

/-- The core of the fixed tower, transported to the general level pair and mass. -/
theorem flCore_three_transport {m₁ : ℕ} {c BG κ t c₂ BG₂ : ℝ}
    (h : Nonempty (FlCore 2 (Gp m₁ (rhoSep m₁)) (Hm m₁ (rhoSep m₁)) 1 nuW c BG κ t
      (levelKc 3 3) (Cchi 3 3) c₂ BG₂ t)) :
    Nonempty (FlCore 2 (GpG 3 3 9 m₁ 1) (HmG 3 3 9 m₁ 1) 1 (νref 3) c BG κ t
      (levelKc 3 3) (Cchi 3 3) c₂ BG₂ t) := by
  rw [νref_three]
  have e := rhoSepG_three (m₁ := m₁)
  have key : ∀ ϱ : ℝ, ϱ = rhoSep m₁ →
      Nonempty (FlCore 2 (Gp m₁ ϱ) (Hm m₁ ϱ) 1 nuW c BG κ t
        (levelKc 3 3) (Cchi 3 3) c₂ BG₂ t) := by
    intro ϱ hϱ; subst hϱ; exact h
  exact key _ e

/-- **The core of the reference pair, transferred to the level pair of the scale `k` and the
mass `ν`.**  This is the transfer step used by every determinant theorem at the general tower. -/
theorem flCore_stepG {d L N : ℕ} [NeZero L] (hd : 3 ≤ d) (hL : 3 ≤ L) {m₁ : ℕ}
    {c BG κ t c₂ BG₂ : ℝ} (h4 : 4 ≤ m₁)
    (hC₀ : FlCore N (GpG d L 9 m₁ 1) (HmG d L 9 m₁ 1) 1 (νref L) c BG κ t (levelKc d L)
      (Cchi d L) c₂ BG₂ t)
    {k : ℕ} (hk : 1 ≤ k) {N₁ : ℕ} [NeZero N₁] (hN₁ : 5 < N₁) {ν : ℝ}
    (hν0 : 0 ≤ ν) (hν : ν * (L : ℝ) ^ (2 * (k + 1)) ≤ 1) :
    FlCore N (GpG d L N₁ m₁ k) (HmG d L N₁ m₁ k) 1 ν c BG κ t
      (levelKc d L) (Cchi d L) c₂ BG₂ t :=
  flCore_level_transfer hC₀ (dgSetting_lvG (k := k) (N₁ := N₁) hd hL h4 hN₁ hν0 hν)
    (opSetting_lvG (k := k) (N₁ := N₁) hd hL h4 hN₁ hν0 hν)
    (isLevel_lvLowG hk) isLevel_lvTopG (bgHyp_lvG (k := k) hd hL (bgR0_le_rhoSepG m₁ hd hL) hν0 hν)

/-- The margin `δc` of the covariance chart is nonnegative. -/
theorem δc_nonneg_of_flCore {d L N : ℕ} [NeZero L] (hd : 3 ≤ d) {m₁ k N₁ : ℕ} [NeZero N₁]
    {c BG κ t c₂ BG₂ δc ν : ℝ} (ht0 : 0 < t)
    (hC : FlCore N (GpG d L N₁ m₁ k) (HmG d L N₁ m₁ k) 1 ν c BG κ t
      (levelKc d L) (Cchi d L) c₂ BG₂ t)
    (hdm : decDomMargin d L N BG κ (xiC1 d * t) < δc) : 0 ≤ δc := by
  have hd0 : 0 < d := by omega
  have : 0 ≤ decDomMargin d L N BG κ (xiC1 d * t) := by
    have : 0 < K4 d L N BG κ := K4_pos hC.hS.fam.2.1 hd0
    have := one_le_xiC1 d
    unfold decDomMargin; positivity
  linarith

open Classical in
/-- **The localized determinant family at every scale and on every torus, general `d`, `L`, `N`,
from the output of the numerical tower.**  Let `(m₁, c, BG, κ, t, c₂, BG₂, δc)` satisfy the
conclusions of the numerical tower used here (`4 ≤ m₁`, `0 < t`, `FlCore` at the reference pair
`(GpG d L 9 m₁ 1, HmG d L 9 m₁ 1)` with mass `L⁻⁴`, the cap and the margins of the covariance
chart) and the rate condition `e^κ > 2 (detDeg d L + 1)²`.  Then at the step
`hatStepKG hN k m₁ (rhoSepG d L m₁) hk ν β p₁ δ` of every scale `k ≥ 1`, every torus parameter
`N₁` with `L ∣ N₁`, `5 < N₁` and every mass `0 ≤ ν` with `ν · L^{2(k+1)} ≤ 1`: the datum of the
step is a datum of the chart `Ξ^c(𝔹_{k+1}; 1, t)`, and for every `z` the record
`DetExpansionLocC` (`m₀ = 1`) has an element whose terms are the sums over `y ∈ B(z)` of the
activities, with the rate `(κ - log 2 - 2 log (detDeg d L + 1)) / (2 d L)` and the constant
`L^d · ½ N covBLogMax d L κ / (1 - (detDeg d L + 1)² · 2 / e^κ)`. -/
theorem detExpansionLocC_scale_of_towerG {d L N : ℕ} [NeZero L] (hd : 3 ≤ d) (hL : 3 ≤ L)
    (hN : 2 ≤ N) {m₁ : ℕ} {c BG κ t c₂ BG₂ δc : ℝ} (h4 : 4 ≤ m₁) (ht0 : 0 < t)
    (hC₀ : FlCore N (GpG d L 9 m₁ 1) (HmG d L 9 m₁ 1) 1 (νref L) c BG κ t (levelKc d L)
      (Cchi d L) c₂ BG₂ t)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    (hdm : decDomMargin d L N BG κ (xiC1 d * t) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * t) < coerciveConst d / 2)
    (hsmX : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    (hz : ((detDeg d L + 1 : ℕ) : ℝ) ^ 2 * (2 / Real.exp κ) < 1)
    (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁] (hLN : L ∣ N₁) (hN₁ : 5 < N₁) {ν : ℝ}
    (hν0 : 0 ≤ ν) (hν : ν * (L : ℝ) ^ (2 * (k + 1)) ≤ 1) (β p₁ δ : ℝ) :
    XiCData (hatStepKG (N₁ := N₁) (d := d) (L := L) hN k m₁ (rhoSepG d L m₁) hk ν β p₁ δ).G'
        (compWeight L 1) ν (k + 1) 1 t
        (hatStepKG (N₁ := N₁) (d := d) (L := L) hN k m₁ (rhoSepG d L m₁) hk ν β p₁ δ).D' ∧
      ∀ z, ∃ E : DetExpansionLocC
          (hatStepKG (N₁ := N₁) (d := d) (L := L) hN k m₁ (rhoSepG d L m₁) hk ν β p₁ δ) 1 z t
          ((κ - Real.log 2 - 2 * Real.log ((detDeg d L + 1 : ℕ) : ℝ)) / (2 * d * L))
          ((L : ℝ) ^ d * ((1 / 2 : ℝ) * N * covBLogMax d L κ /
            (1 - ((detDeg d L + 1 : ℕ) : ℝ) ^ 2 * (2 / Real.exp κ)))),
        ∀ D T, E.term D T =
          ∑ y ∈ (hatStepKG (N₁ := N₁) (d := d) (L := L) hN k m₁ (rhoSepG d L m₁) hk ν β
            p₁ δ).blockU z,
          detActivityBg 1 (compWeight L 1) 1 ν (rho4 d L N BG κ) D y T := by
  set S := hatStepKG (N₁ := N₁) (d := d) (L := L) hN k m₁ (rhoSepG d L m₁) hk ν β p₁ δ with hS
  have hN0 : 0 < N := Nat.lt_of_lt_of_le two_pos hN
  have hHB := bgHyp_lvG (k := k) hd hL (bgR0_le_rhoSepG m₁ hd hL) hν0 hν
  have hC := flCore_stepG (N := N) hd hL h4 hC₀ hk hN₁ hν0 hν
  have hD : XiCData S.G' (compWeight L 1) ν (k + 1) 1 t S.D' := by
    refine ⟨fun _ => unitVec hN0, unitVec hN0, 0, 0,
      exists_xiC hHB (GpG d L N₁ m₁ k) hN0 (massLe_lvG hν) ht0, ?_, ?_⟩
    · intro x hx i
      have := unitBg_Ψ_of_mem (GpG d L N₁ m₁ k) hN0 (unitVec hN0) hx i
      show (unitBg (GpG d L N₁ m₁ k) hN0 (unitVec hN0)).Ψ x i = _
      rw [this]; simp
    · intro x hx i
      have := unitBg_h_of_mem (GpG d L N₁ m₁ k) hN0 (unitVec hN0) hx i
      show (unitBg (GpG d L N₁ m₁ k) hN0 (unitVec hN0)).h x i = _
      rw [this]; simp
  have hδc := δc_nonneg_of_flCore hd ht0 hC hdm
  have hN3 : L ^ 1 ∣ N₁ := by simpa using hLN
  exact ⟨hD, fun z => exists_detExpansionLocC_of_chart_uniform (m₀ := 1) S hC hδc hMX hdm hα
    hsmX (hatConn_lvTopG hL) hN3 hz z⟩

end Balaban.Inhabited
