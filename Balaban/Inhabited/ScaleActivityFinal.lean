/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.LevelRayTower
public import Balaban.Inhabited.ScaleActivityFinalG
public import Balaban.Fluctuation.LevelLocalCover
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

/-!
# The zero-class activity bound at every scale and on every torus

`stepActivityBound_zeroClass_direct_physical_rate` is the label-activity bound of the zero class at
the witness step (`k = 1`, `N₁ = 9`, `ν = 1/81`) for all large `β`.  This file proves the same
bound for the step `hatStepK k m₁ hk ν β p₁ δ` (`d = L = 3`, `N = 2`, constant unit block datum)

* at every scale `k ≥ 1`,
* on every torus `CTorus 3 3 N₁ m₁ (k + 1)` with `3 ∣ N₁` and `5 < N₁`,
* for every mass `0 < ν` with `ν · 3^{2(k+1)} ≤ 1` (for the physical mass `ν = ν_k 3^{-2k}` this is
  `ν_k ≤ L^{-2}`, `massLe_iff`),
* for every `β ≥ β₀`,

with `m₁`, `t = δ₁ = ε`, `δ`, `β₀`, `C` and the rates fixed before, and independent of, `k`, `N₁`,
`ν`.  The rates are those of `stepActivityBound_zeroClass_direct_physical_rate`: `κ₀ = a_Ent + 1`,
`κ_dec = 100 (κ₀ + c₁ + 10)`, `κ' = (3/2) κ_dec + κ₀ + 1`.  Write `β_k = β · 3^k`.

* `stepActivityBound_zeroClass_direct_physical_scale_cutoff`: for every cutoff
  `0 < p₁ ≤ A₁ (log β_k)^p`, a step activity bound with `κ_H = 2 κ_dec - 1` and prefactor
  `ε_H ≤ C (log β_k)^{3p}/√β_k`.
* `stepActivityBound_zeroClass_direct_physical_scale`: the case `p₁ = A₁ (log β_k)^p`, the cutoff of
  the papers at the scale.
* `stepActivityBound_zeroClass_direct_physical_scale_running`: the same for the physical mass
  `ν = ν_k 3^{-2k}` of a running mass `0 < ν_k ≤ L^{-2}`.
* `stepActivityBound_zeroClass_direct_physical_rate_of_scale`: at `k = 1`, `N₁ = 9`, `ν = 1/81`
  the step is the landed `hatStep` (`hatStepK_one_nine`, by `rfl`), and the cutoff
  `A₁ (log β)^p ≤ A₁ (log 3β)^p` of the landed theorem is admissible; the general theorem gives the
  statement of `stepActivityBound_zeroClass_direct_physical_rate` word for word (with
  `(log 3β)^{3p}/√(3β) ≤ 2^{3p} (log β)^{3p}/√β` for `β ≥ 3`).

How the hypotheses of `stepActivityBound_zeroClass_direct_scaled_uniform` are met:
the cover hypotheses of the potential and source parts by `LocalCover.levelLocalCover` at the cover
scale `m₀ = 1` (`X₁` is the `5 × 5 × 5` cells of `π_{k+1}` around the cell of the block);
`FlCore` by `flCore_level_transfer` from the numerical tower `tower_core_rates`; `HatConn`,
`RowInHat`, `BgHyp`, the levels by `LevelStepSetting`; the cutoff, radii and `RayData` by
`scale_C_items`; the amplitude by `scale_amp_exists`, with the scale-free bound
`energyConstScaled ≤ L^d C_E` (weights `a_k ≤ 2`); the smallness by `amplitude_le` at `β_k ≥ β`.

Dependence on the scale, the torus and the mass.  No constant of the conclusion depends on `k`,
`N₁` or `ν`.  Inside the proof one constant does: the bound `Bh = 1 + 2/ν` of the datum field
(`hBh_of_xi`).  It multiplies the coefficient `‖c_ν‖ = 0` of the zero class, so it does not enter
the amplitude; but the hypothesis `hBh` of the engine (a bound on the datum field over the data
domain) has to be supplied, and the landed bound `hBh_of_xi` needs `ν > 0`: every condition on the
datum field in the data domains (`InPsiTilde`, `XiBounds`, `XiCBounds`) carries a factor `ν`.  This
is why the mass premise here is `0 < ν` and not `0 ≤ ν`; the cutoff, radius and `RayData`
hypotheses (`scale_C_items`) and the cover hypotheses hold for `0 ≤ ν`.

The theorem `stepActivityBound_zeroClass_direct_physical_scale_cutoff` is the case `d = L = 3`,
`N = 2` of `stepActivityBound_zeroClass_direct_physical_scale_cutoff_general`
(`ScaleActivityFinalG`), which carries the proof; the other theorems of this file follow from it.

What is proved: zero class, at the step `hatStepK` (`d = L = 3`, `N = 2`, constant unit block
datum, as in the landed witness), every scale with `0 < ν`, `ν · 3^{2(k+1)} ≤ 1`, every torus with
`3 ∣ N₁`, `5 < N₁`, constants independent of the scale, the torus and the mass.  What is not
proved: scales with `ν · 3^{2(k+1)} > 1` (massive backgrounds), the mass `ν = 0`, block data other
than the constant unit datum, general classes (nonempty old-energy and observable families), and
the output terms of the step.
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation
  Balaban.Localization Balaban.Localization.LevelPair Balaban.Localization.I5Inhabited
  Balaban.Polymer Balaban.SmallField.Def6 Balaban.Inhabited.LevelStep Filter Topology

open Classical in
/-- **The zero-class activity bound at every scale and on every torus, for every cutoff up to the
cutoff of the papers.**  With `κ₀ = a_Ent + 1`, `κ_dec = 100 (κ₀ + c₁ + 10)`,
`κ' = (3/2) κ_dec + κ₀ + 1`: there are `m₁, t, δ, β₀, C` (`β₀ ≥ 2`, `C > 0`) such that for every
scale `k ≥ 1`, every torus parameter `N₁` with `3 ∣ N₁`, `5 < N₁`, every mass `0 < ν` with
`ν · 3^{2(k+1)} ≤ 1`, every `β ≥ β₀` and every cutoff `0 < p₁ ≤ A₁ (log β_k)^p`, `β_k = β · 3^k`,
the zero class at `hatStepK k m₁ hk ν β p₁ δ` has a step activity bound with `κ_H = 2 κ_dec - 1`
and prefactor at most `C (log β_k)^{3p}/√β_k`; the rate relation
`κ' + 3κ₀ + c₁ + 3/2 ≤ 2 κ_dec - 1` holds, and the output rate `κ_out = (3/2) κ_dec` satisfies
`κ_dec ≤ κ_out ≤ min κ' κ' - κ₀ - 1`.  The constants do not depend on `k`, `N₁`, `ν`. -/
theorem stepActivityBound_zeroClass_direct_physical_scale_cutoff {A₁ : ℝ} (hA : 0 < A₁) (p : ℕ)
    {κ0 κdec κ' : ℝ} (hκ0def : κ0 = aEnt 3 3 + 1) (hκdecdef : κdec = 100 * (κ0 + c1 3 3 + 10))
    (hκ'def : κ' = 3 / 2 * κdec + κ0 + 1) :
    ∃ (m₁ : ℕ) (t δ β₀ C : ℝ), 2 ≤ β₀ ∧ 0 < C ∧ 0 < t ∧ 0 < δ ∧
      ∀ (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁], 3 ∣ N₁ → 5 < N₁ →
      ∀ ν : ℝ, 0 < ν → ν * 3 ^ (2 * (k + 1)) ≤ 1 → ∀ β : ℝ, β₀ ≤ β →
      ∀ p₁ : ℝ, 0 < p₁ → p₁ ≤ pLog A₁ p (β * 3 ^ k) →
        ∃ B : StepActivityBound (hatStepK (N₁ := N₁) k m₁ hk ν β p₁ δ)
            (zeroClass 3 3 N₁ m₁ k 2 (rhoSep m₁)) 0,
          B.κH = 2 * κdec - 1 ∧
          B.εH ≤ C * (Real.log (β * 3 ^ k)) ^ (3 * p) / Real.sqrt (β * 3 ^ k) ∧
          κ' + 3 * κ0 + c1 3 3 + 3 / 2 ≤ 2 * κdec - 1 ∧
          ∃ κout : ℝ, κout = 3 / 2 * κdec ∧ κdec ≤ κout ∧ κout ≤ min κ' κ' - κ0 - 1 := by
  obtain ⟨m₁, t, δ, β₀, C, hβ₀, hC, ht, hδ, h⟩ :=
    stepActivityBound_zeroClass_direct_physical_scale_cutoff_general (d := 3) (L := 3) (N := 2)
      (by norm_num) (by norm_num) le_rfl hA p hκ0def hκdecdef hκ'def
  refine ⟨m₁, t, δ, β₀, C, hβ₀, hC, ht, hδ, ?_⟩
  intro k hk N₁ _ h3N hN ν hνpos hν β hβ p₁ hp0 hp₁
  have e : (((3 : ℕ) : ℝ)) ^ (k * (3 - 2)) = 3 ^ k := by norm_num
  have key : ∀ ϱ : ℝ, ϱ = rhoSep m₁ →
      ∀ B : StepActivityBound (hatStepKG (d := 3) (L := 3) (N := 2) (N₁ := N₁) le_rfl k m₁ ϱ hk
          ν β p₁ δ) (zeroClass 3 3 N₁ m₁ k 2 ϱ) 0,
        ∃ B' : StepActivityBound (hatStepK (N₁ := N₁) k m₁ hk ν β p₁ δ)
            (zeroClass 3 3 N₁ m₁ k 2 (rhoSep m₁)) 0, B'.κH = B.κH ∧ B'.εH = B.εH := by
    intro ϱ hϱ
    subst hϱ
    exact fun B => ⟨B, rfl, rfl⟩
  obtain ⟨B, hB1, hB2, hB3, hB4⟩ := h k hk N₁ h3N hN ν hνpos (by simpa using hν) β hβ p₁ hp0
    (by rw [e]; exact hp₁)
  obtain ⟨B', h1', h2'⟩ := key _ (rhoSepG_three m₁) B
  refine ⟨B', h1'.trans hB1, ?_, hB3, hB4⟩
  rw [h2']
  have := hB2
  rw [e] at this
  exact this

/-- **The zero-class activity bound at every scale and on every torus, with the cutoff of the
papers.**  With `κ₀ = a_Ent + 1`, `κ_dec = 100 (κ₀ + c₁ + 10)`, `κ' = (3/2) κ_dec + κ₀ + 1`: there
are `m₁, t, δ, β₀, C` (`β₀ ≥ 2`, `C > 0`) such that for every scale `k ≥ 1`, every torus parameter
`N₁` with `3 ∣ N₁`, `5 < N₁`, every mass `0 < ν` with `ν · 3^{2(k+1)} ≤ 1` and every `β ≥ β₀`, at
the step `hatStepK k m₁ hk ν β p₁ δ` with the cutoff `p₁ = A₁ (log β_k)^p`, `β_k = β · 3^k`, the
zero class has a step activity bound with `κ_H = 2 κ_dec - 1` and prefactor at most
`C (log β_k)^{3p}/√β_k`; the rate relation `κ' + 3κ₀ + c₁ + 3/2 ≤ 2 κ_dec - 1` holds, and the
output rate `κ_out = (3/2) κ_dec` satisfies `κ_dec ≤ κ_out ≤ min κ' κ' - κ₀ - 1`.  The constants
`m₁, t, δ, β₀, C` and the rates do not depend on `k`, `N₁`, `ν`.  The only hypotheses are the size
conditions on `N₁`, the mass premise and `β ≥ β₀`. -/
theorem stepActivityBound_zeroClass_direct_physical_scale {A₁ : ℝ} (hA : 0 < A₁) (p : ℕ)
    {κ0 κdec κ' : ℝ} (hκ0def : κ0 = aEnt 3 3 + 1) (hκdecdef : κdec = 100 * (κ0 + c1 3 3 + 10))
    (hκ'def : κ' = 3 / 2 * κdec + κ0 + 1) :
    ∃ (m₁ : ℕ) (t δ β₀ C : ℝ), 2 ≤ β₀ ∧ 0 < C ∧ 0 < t ∧ 0 < δ ∧
      ∀ (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁], 3 ∣ N₁ → 5 < N₁ →
      ∀ ν : ℝ, 0 < ν → ν * 3 ^ (2 * (k + 1)) ≤ 1 → ∀ β : ℝ, β₀ ≤ β →
        ∃ B : StepActivityBound (hatStepK (N₁ := N₁) k m₁ hk ν β (pLog A₁ p (β * 3 ^ k)) δ)
            (zeroClass 3 3 N₁ m₁ k 2 (rhoSep m₁)) 0,
          B.κH = 2 * κdec - 1 ∧
          B.εH ≤ C * (Real.log (β * 3 ^ k)) ^ (3 * p) / Real.sqrt (β * 3 ^ k) ∧
          κ' + 3 * κ0 + c1 3 3 + 3 / 2 ≤ 2 * κdec - 1 ∧
          ∃ κout : ℝ, κout = 3 / 2 * κdec ∧ κdec ≤ κout ∧ κout ≤ min κ' κ' - κ0 - 1 := by
  obtain ⟨m₁, t, δ, β₀, C, hβ₀, hC, ht, hδ, h⟩ :=
    stepActivityBound_zeroClass_direct_physical_scale_cutoff hA p hκ0def hκdecdef hκ'def
  refine ⟨m₁, t, δ, β₀, C, hβ₀, hC, ht, hδ, ?_⟩
  intro k hk N₁ _ h3 hN ν hν0 hν β hβ
  have h3k : (1 : ℝ) ≤ 3 ^ k := one_le_pow₀ (by norm_num)
  have hβ2 : 2 ≤ β := hβ₀.trans hβ
  have hb : 1 < β * 3 ^ k :=
    lt_of_lt_of_le (by linarith) (le_mul_of_one_le_right (by linarith) h3k)
  exact h k hk N₁ h3 hN ν hν0 hν β hβ _ (pLog_pos hA p hb) le_rfl

/-- **The same in terms of the running mass.**  For the physical mass `ν = ν_k 3^{-2k}` of a running
mass `0 < ν_k ≤ L^{-2} = 1/9`, the mass premise of `stepActivityBound_zeroClass_direct_physical_scale`
holds (`massLe_iff`): the bound holds at every scale `k ≥ 1` with `ν_k ≤ L^{-2}`. -/
theorem stepActivityBound_zeroClass_direct_physical_scale_running {A₁ : ℝ} (hA : 0 < A₁) (p : ℕ)
    {κ0 κdec κ' : ℝ} (hκ0def : κ0 = aEnt 3 3 + 1) (hκdecdef : κdec = 100 * (κ0 + c1 3 3 + 10))
    (hκ'def : κ' = 3 / 2 * κdec + κ0 + 1) :
    ∃ (m₁ : ℕ) (t δ β₀ C : ℝ), 2 ≤ β₀ ∧ 0 < C ∧ 0 < t ∧ 0 < δ ∧
      ∀ (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁], 3 ∣ N₁ → 5 < N₁ →
      ∀ νk : ℝ, 0 < νk → νk ≤ (((3 : ℕ) : ℝ) ^ 2)⁻¹ → ∀ β : ℝ, β₀ ≤ β →
        ∃ B : StepActivityBound (hatStepK (N₁ := N₁) k m₁ hk
              (Balaban.SmallField.Def6v2.sfBgMassAt 3 k νk) β (pLog A₁ p (β * 3 ^ k)) δ)
            (zeroClass 3 3 N₁ m₁ k 2 (rhoSep m₁)) 0,
          B.κH = 2 * κdec - 1 ∧
          B.εH ≤ C * (Real.log (β * 3 ^ k)) ^ (3 * p) / Real.sqrt (β * 3 ^ k) ∧
          κ' + 3 * κ0 + c1 3 3 + 3 / 2 ≤ 2 * κdec - 1 ∧
          ∃ κout : ℝ, κout = 3 / 2 * κdec ∧ κdec ≤ κout ∧ κout ≤ min κ' κ' - κ0 - 1 := by
  obtain ⟨m₁, t, δ, β₀, C, hβ₀, hC, ht, hδ, h⟩ :=
    stepActivityBound_zeroClass_direct_physical_scale hA p hκ0def hκdecdef hκ'def
  refine ⟨m₁, t, δ, β₀, C, hβ₀, hC, ht, hδ, ?_⟩
  intro k hk N₁ _ h3 hN νk hνk0 hνk β hβ
  have hm := (massLe_iff (L := 3) k νk).2 hνk
  have hmass : Balaban.SmallField.Def6v2.sfBgMassAt 3 k νk * 3 ^ (2 * (k + 1)) ≤ 1 := by
    rw [← pow_mul, mul_comm (k + 1) 2] at hm
    simpa using hm
  exact h k hk N₁ h3 hN _ (Balaban.SmallField.Def6v2.physMass_pos (L := 3) k hνk0) hmass β hβ

/-- **Consistency with the landed witness theorem.**  At `k = 1`, `N₁ = 9`, `ν = 1/81` the step
`hatStepK` is the landed `hatStep` (`hatStepK_one_nine`), the cutoff `A₁ (log β)^p` of the landed
theorem is at most `A₁ (log β_1)^p`, `β_1 = 3β`, and `(log 3β)^{3p}/√(3β) ≤ 2^{3p} (log β)^{3p}/√β`
for `β ≥ 3`.  Hence the general theorem implies the statement of
`stepActivityBound_zeroClass_direct_physical_rate`. -/
theorem stepActivityBound_zeroClass_direct_physical_rate_of_scale {A₁ : ℝ} (hA : 0 < A₁) (p : ℕ)
    {κ0 κdec κ' : ℝ} (hκ0def : κ0 = aEnt 3 3 + 1) (hκdecdef : κdec = 100 * (κ0 + c1 3 3 + 10))
    (hκ'def : κ' = 3 / 2 * κdec + κ0 + 1) :
    ∃ (m₁ : ℕ) (t δ β₀ C : ℝ), 2 ≤ β₀ ∧ 0 < C ∧ 0 < t ∧ 0 < δ ∧
      ∀ β : ℝ, β₀ ≤ β →
        ∃ B : StepActivityBound (hatStep m₁ β (pLog A₁ p β) δ)
            (zeroClass 3 3 9 m₁ 1 2 (rhoSep m₁)) 0,
          B.κH = 2 * κdec - 1 ∧ B.εH ≤ C * (Real.log β) ^ (3 * p) / Real.sqrt β ∧
          κ' + 3 * κ0 + c1 3 3 + 3 / 2 ≤ 2 * κdec - 1 ∧
          ∃ κout : ℝ, κout = 3 / 2 * κdec ∧ κdec ≤ κout ∧ κout ≤ min κ' κ' - κ0 - 1 := by
  obtain ⟨m₁, t, δ, β₀, C, hβ₀, hC, ht, hδ, h⟩ :=
    stepActivityBound_zeroClass_direct_physical_scale_cutoff hA p hκ0def hκdecdef hκ'def
  refine ⟨m₁, t, δ, max β₀ 3, 2 ^ (3 * p) * C, le_trans hβ₀ (le_max_left _ _), by positivity,
    ht, hδ, ?_⟩
  intro β hβ
  have hβ3 : 3 ≤ β := (le_max_right _ _).trans hβ
  have hβ0 : 0 < β := by linarith
  have hlog0 : 0 ≤ Real.log β := Real.log_nonneg (by linarith)
  have hlogle : Real.log β ≤ Real.log (β * 3 ^ 1) := Real.log_le_log hβ0 (by linarith)
  have hp₁ : pLog A₁ p β ≤ pLog A₁ p (β * 3 ^ 1) := by
    unfold pLog
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hlog0 hlogle p) hA.le
  obtain ⟨B, hB1, hB2, hB3, hB4⟩ := h 1 le_rfl 9 (by norm_num) (by norm_num) nuW nuW_pos
    (by unfold nuW; norm_num) β ((le_max_left _ _).trans hβ) (pLog A₁ p β)
    (pLog_pos hA p (by linarith)) hp₁
  refine ⟨B, hB1, hB2.trans ?_, hB3, hB4⟩
  have hlog3 : Real.log (β * 3 ^ 1) ≤ 2 * Real.log β := by
    rw [pow_one, Real.log_mul hβ0.ne' (by norm_num)]
    have : Real.log 3 ≤ Real.log β := Real.log_le_log (by norm_num) hβ3
    linarith
  have hsqrt : Real.sqrt β ≤ Real.sqrt (β * 3 ^ 1) := Real.sqrt_le_sqrt (by linarith)
  have hsβ : 0 < Real.sqrt β := Real.sqrt_pos.2 hβ0
  have h1 : (Real.log (β * 3 ^ 1)) ^ (3 * p) ≤ 2 ^ (3 * p) * (Real.log β) ^ (3 * p) := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (hlog0.trans hlogle) hlog3 _
  have hnum0 : 0 ≤ C * (Real.log (β * 3 ^ 1)) ^ (3 * p) :=
    mul_nonneg hC.le (pow_nonneg (hlog0.trans hlogle) _)
  calc C * (Real.log (β * 3 ^ 1)) ^ (3 * p) / Real.sqrt (β * 3 ^ 1)
      ≤ C * (Real.log (β * 3 ^ 1)) ^ (3 * p) / Real.sqrt β :=
        div_le_div_of_nonneg_left hnum0 hsβ hsqrt
    _ ≤ C * (2 ^ (3 * p) * (Real.log β) ^ (3 * p)) / Real.sqrt β :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left h1 hC.le) hsβ.le
    _ = 2 ^ (3 * p) * C * (Real.log β) ^ (3 * p) / Real.sqrt β := by ring

end Balaban.Inhabited
