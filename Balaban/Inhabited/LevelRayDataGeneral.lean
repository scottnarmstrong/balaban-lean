/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.LevelRayTowerGeneral
public import Balaban.Inhabited.LevelPairGeneral
public import Balaban.Fluctuation.StepRegWitnessGeneral
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

/-!
# `RayData` of the step at every scale, for general `d`, `L`, `N`

`hatStepKG_domain`: the unit datum of `hatStepKG` lies in the real data domain for every radius.
`rayData_hatStepKG_pp`: the `RayData` record of `hatStepKG` (general `d ≥ 3`, `L ≥ 3`, `N ≥ 2`)
from `β L^{k(d-2)} = T²`, `3 B₅ K₂ p⁺ ≤ T δ` and `B₅ p⁺ ≤ T · fluctRadius`; the separation of the
step is `rhoSepG d L m₁`.  `scale_C_items_general`: the four numeric items of
`scale_C_items_numeric` together with `RayData (2 p₁)`, with `β₀` independent of the scale.
At `(3, 3, 2)` these are the statements of `LevelRayTower`.
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation
  Balaban.Localization Balaban.Localization.LevelPair Balaban.Localization.I5Inhabited
  Balaban.Polymer Balaban.SmallField.Def6

namespace LevelStep

section Ray

variable {d L N : ℕ} [NeZero L] {N₁ : ℕ} [NeZero N₁]

/-- The unit datum of the general step lies in the real data domain, for every radius `δ' > 0`. -/
theorem hatStepKG_domain (hN : 2 ≤ N) (k m₁ : ℕ) (ϱ : ℝ) (hk : 1 ≤ k) (ν β p₁ δ : ℝ) {δ' : ℝ}
    (hδ'0 : 0 < δ') :
    InDomainR (hatStepKG (d := d) (L := L) (N₁ := N₁) hN k m₁ ϱ hk ν β p₁ δ).G'
      (hatStepKG (d := d) (L := L) (N₁ := N₁) hN k m₁ ϱ hk ν β p₁ δ).ν δ'
      (hatStepKG (d := d) (L := L) (N₁ := N₁) hN k m₁ ϱ hk ν β p₁ δ).D' := by
  have hN0 : 0 < N := Nat.lt_of_lt_of_le two_pos hN
  refine ⟨fun _ => unitVec hN0, unitVec hN0,
    (exists_inPsiTildeC (G := lvTopG d L N₁ m₁ k ϱ) hN0 ν hδ'0 hδ'0).toInPsiTilde, ?_, ?_⟩
  · intro x hx i
    exact unitBg_Ψ_of_mem (lvTopG d L N₁ m₁ k ϱ) hN0 (unitVec hN0) hx i
  · intro x hx i
    exact unitBg_h_of_mem (lvTopG d L N₁ m₁ k ϱ) hN0 (unitVec hN0) hx i

/-- **`RayData` for the general step at scale `k`**, with the weight-uniform constants `B5Max`,
`K2Max`: for `β L^{k(d-2)} = T²`, `3 B₅ K₂ p⁺ ≤ T δ` and `B₅ p⁺ ≤ T · fluctRadius`.  The
separation of the step is `rhoSepG d L m₁`. -/
theorem rayData_hatStepKG_pp (hd : 3 ≤ d) (hL : 3 ≤ L) (hN : 2 ≤ N) (k m₁ : ℕ) (hk : 1 ≤ k)
    (p₁ pp : ℝ) (hm : 4 ≤ m₁) (hN₁ : 5 < N₁)
    (hbig : cstarX d L ≤ (L : ℝ) ^ m₁) {ν : ℝ} (hν0 : 0 ≤ ν)
    (hν : ν * (L : ℝ) ^ (2 * (k + 1)) ≤ 1)
    {δ δ' T β : ℝ} (hpp : 0 < pp) (hδ : 0 < δ) (hsm : δ ^ 2 * smallConstX d L 0 ≤ 1 / 4)
    (hδ'0 : 0 < δ')
    (hδ'a : δ' ≤ thm73C3 d L N / 2) (hδ'b : bgK1 d L N * δ' ≤ δ / 4)
    (hδ'c : bgK1 d L N * δ' ≤ coerciveConst d / 4) (hT : 0 < T)
    (hβ : β * (L : ℝ) ^ (k * (d - 2)) = T ^ 2)
    (hT1 : 3 * B5Max d L N * K2Max d L N * pp ≤ T * δ)
    (hT2 : B5Max d L N * pp ≤ T * fluctRadius d L N) :
    Nonempty ((hatStepKG (d := d) (L := L) (N₁ := N₁) hN k m₁ (rhoSepG d L m₁) hk ν β p₁ δ).RayData
      pp) := by
  have hN0 : 0 < N := Nat.lt_of_lt_of_le two_pos hN
  set S := hatStepKG (d := d) (L := L) (N₁ := N₁) hN k m₁ (rhoSepG d L m₁) hk ν β p₁ δ with hS
  have hbetaU : S.betaU = T ^ 2 := by
    rw [hS, hatStepKG_betaU hN (by omega), hβ]
  have hβ0 : 0 < β := by
    have hL0 : (0 : ℝ) < L := by exact_mod_cast (by omega : 0 < L)
    have h3 : (0 : ℝ) < (L : ℝ) ^ (k * (d - 2)) := by positivity
    have : 0 < β * (L : ℝ) ^ (k * (d - 2)) := by rw [hβ]; positivity
    exact pos_of_mul_pos_left this h3.le
  have hHg : BgHyp d L (k + 1) (rhoSepG d L m₁) (compWeight L 1) ν :=
    bgHyp_lvG hd hL (bgR0_le_rhoSepG m₁ hd hL) hν0 hν
  have hcons := theta_consts (d := d) (L := L) (N := N) (by omega) hδ'0 hδ'a
  have hDR : InDomainR S.G' S.ν δ' S.D' :=
    hatStepKG_domain hN k m₁ (rhoSepG d L m₁) hk ν β p₁ δ hδ'0
  have hDU : InUnionDomainR S.G' (bgC1 d L N) S.ν S.D' := ⟨δ', hδ'0, hcons.2.2.1, hDR⟩
  have hbg : bgField S.G' S.a S.ν S.D' = unitPhi S.G' hN0 := bgField_unit_lvG hN0 hL hHg hDU
  have hbd := (theorem71 hHg hDU).2.2.2.2 δ' hδ'0 hcons.2.2.1 hDR
  have hα : ∀ x : S.G'.Ω 1, S.G'.spacing (x : CTorus d L N₁ m₁ (k + 1)) ^ 2 *
      ‖bgMult S.G' S.a S.ν S.D' x‖ ≤ bgK1 d L N * δ' := hbd.alpha
  have hsp : ∀ x : CTorus d L N₁ m₁ (k + 1), 0 < S.G'.spacing x := fun x => spacing_pos _
  have hB : 0 < B5Max d L N := lt_of_lt_of_le one_pos (le_max_left _ _)
  have hK : 0 < K2Max d L N :=
    lt_of_lt_of_le one_pos ((le_max_left _ _).trans (le_max_left _ _))
  refine ⟨{ ha₁ := one_pos, H := hHg, δ' := δ', hδ'0 := hδ'0, hδ' := hδ'a, hD'R := hDR,
            hδ0 := hδ, hfam := ?_, hsm := hsm, hχu := ?_, hnorm := ?_, hβ := hβ0,
            hpp := hpp, B₅ := B5Max d L N, K₂ := K2Max d L N,
            hB5 := B5_le_B5Max (by omega) hL (compWeight_one_mem hL hk),
            hK2 := K2_le_K2Max, hp40 := ?_, hrad := ?_ }⟩
  · intro x hx
    refine ⟨⟨dgSetting_lvG hd hL hm hN₁ hν0 hν, hk, by show (1 / 2 : ℝ) ≤ 1; norm_num,
      by show (1 : ℝ) ≤ 2; norm_num⟩, ?_, hx, le_rfl, ?_, ?_⟩
    · intro y
      have hs2 : 0 < S.G'.spacing (y : CTorus d L N₁ m₁ (k + 1)) ^ 2 := by
        have := hsp y; positivity
      have h1 := hα y
      have h2 : coerciveConst d ≥ 0 := (coerciveConst_pos (by omega)).le
      rw [le_div_iff₀ (by positivity)]
      nlinarith
    · simpa using hbig
    · intro P; simp
  · rw [chiU_eq_one_iff]
    refine chiUBounds_unitBg_nu (isLevel_lvTopG (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k)
      (ϱ := rhoSepG d L m₁)) hN0 hδ hbg fun y => ?_
    exact lt_of_le_of_lt (hα y) (by linarith)
  · have hh : ∑ i, S.h₀ i ^ 2 = 1 := sum_sq_unitVec hN0
    rw [hh, sub_self, abs_zero, mul_zero]
    have hd' : S.δ = δ := rfl
    rw [hd']
    positivity
  · have hd' : S.δ = δ := rfl
    rw [hbetaU, hd']
    have e : (T ^ 2) ^ (1 / 2 : ℝ) = T := by
      rw [← Real.sqrt_eq_rpow, Real.sqrt_sq hT.le]
    rw [e, div_le_iff₀ (by positivity)]
    rw [inv_mul_eq_div, le_div_iff₀ (by positivity)]
    nlinarith
  · rw [hbetaU]
    have e : (T ^ 2) ^ (-(1 / 2) : ℝ) = T⁻¹ := by
      rw [Real.rpow_neg (by positivity), ← Real.sqrt_eq_rpow, Real.sqrt_sq hT.le]
    rw [e]
    have : B5Max d L N * T⁻¹ * pp = B5Max d L N * pp / T := by field_simp
    rw [this, div_le_iff₀ hT]
    linarith

/-- **The cutoff, radius and `RayData` hypotheses at every scale, general `d`, `L`, `N`.**  There
is `β₀ ≥ 2`, depending on `d, L, N, A₁, p, t, κ, δ` only, such that for every scale `k ≥ 1`, torus
parameter `N₁ > 5`, admissible mass, `β ≥ β₀` and `0 < p₁ ≤ pLog A₁ p b`, `b = β L^{k(d-2)}` (the
block coupling `hatStepKG_betaU`): the four numeric items of `scale_C_items_numeric`,
`p₁ < 2 p₁` and `RayData (2 p₁)` for `hatStepKG` at the separation `rhoSepG d L m₁`. -/
theorem scale_C_items_general {d L N : ℕ} [NeZero L] (hd : 3 ≤ d) (hL : 3 ≤ L) (hN : 2 ≤ N)
    {A₁ : ℝ} (hA : 0 < A₁) (p : ℕ) (m₁ : ℕ) (hm : 4 ≤ m₁) (hbig : cstarX d L ≤ (L : ℝ) ^ m₁)
    {δ δ' t : ℝ} (κ : ℝ) (ht : 0 < t) (hδ : 0 < δ) (hsm : δ ^ 2 * smallConstX d L 0 ≤ 1 / 4)
    (hδ'0 : 0 < δ') (hδ'a : δ' ≤ thm73C3 d L N / 2) (hδ'b : bgK1 d L N * δ' ≤ δ / 4)
    (hδ'c : bgK1 d L N * δ' ≤ coerciveConst d / 4) :
    ∃ β₀ : ℝ, 2 ≤ β₀ ∧ ∀ (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁], 5 < N₁ →
      ∀ ν : ℝ, 0 ≤ ν → ν * (L : ℝ) ^ (2 * (k + 1)) ≤ 1 → ∀ β : ℝ, β₀ ≤ β →
      ∀ p₁ : ℝ, 0 < p₁ → p₁ ≤ pLog A₁ p (β * (L : ℝ) ^ (k * (d - 2))) →
      (0 < lvCpsiG d L N κ t (β * (L : ℝ) ^ (k * (d - 2))) ∧
      0 < lvRG d L N κ t (β * (L : ℝ) ^ (k * (d - 2))) p₁ ∧
      Real.sqrt (N : ℝ) *
        (‖(((β * (L : ℝ) ^ (k * (d - 2))) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)‖ *
          (covSupConstC d L N (compWeight L (1 : ℝ) k) κ *
            lvCpsiG d L N κ t (β * (L : ℝ) ^ (k * (d - 2))))) < t ∧
      ((2 : ℝ) * 2 + lvRG d L N κ t (β * (L : ℝ) ^ (k * (d - 2))) p₁) * p₁ <
        lvCpsiG d L N κ t (β * (L : ℝ) ^ (k * (d - 2)))) ∧
      p₁ < 2 * p₁ ∧
      Nonempty ((hatStepKG (d := d) (L := L) (N₁ := N₁) hN k m₁ (rhoSepG d L m₁) hk ν β p₁
        δ).RayData (2 * p₁)) := by
  have hB : 0 < B5Max d L N := lt_of_lt_of_le one_pos (le_max_left _ _)
  have hK : 0 < K2Max d L N :=
    lt_of_lt_of_le one_pos ((le_max_left _ _).trans (le_max_left _ _))
  have hfR := fluctRadius_pos_general (d := d) (L := L) (N := N) (by omega)
  obtain ⟨β₁, hβ₁, hnum⟩ := scale_C_items_numeric (d := d) (L := L) (N := N) (by omega) hL
    (by omega) hA p κ ht
  set c₀ : ℝ := min (δ / (6 * B5Max d L N * K2Max d L N))
    (fluctRadius d L N / (2 * B5Max d L N)) with hc₀
  have hc₀0 : 0 < c₀ := lt_min (by positivity) (by positivity)
  have hc₀1 : c₀ ≤ δ / (6 * B5Max d L N * K2Max d L N) := min_le_left _ _
  have hc₀2 : c₀ ≤ fluctRadius d L N / (2 * B5Max d L N) := min_le_right _ _
  refine ⟨max β₁ (pLogThreshold A₁ p c₀), hβ₁.trans (le_max_left _ _), ?_⟩
  intro k hk N₁ _ hN₁ ν hν0 hν β hβ p₁ hp0 hp₁
  have hβ1 : β₁ ≤ β := (le_max_left _ _).trans hβ
  have hβ2 : 2 ≤ β := hβ₁.trans hβ1
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast (by omega : 1 ≤ L)
  have h3k : (1 : ℝ) ≤ (L : ℝ) ^ (k * (d - 2)) := one_le_pow₀ hL1
  set b : ℝ := β * (L : ℝ) ^ (k * (d - 2)) with hb
  have hbβ : β ≤ b := by rw [hb]; nlinarith
  have hb1 : (1 : ℝ) < b := by linarith
  have hb0 : 0 < b := by linarith
  have hle : p₁ ≤ c₀ * Real.sqrt b :=
    hp₁.trans (pLog_le_mul_sqrt hA.le p hc₀0 hb1.le (((le_max_right _ _).trans hβ).trans hbβ))
  set T : ℝ := Real.sqrt b with hT
  have hT0 : 0 < T := Real.sqrt_pos.2 hb0
  refine ⟨hnum k hk β hβ1 p₁ hp0 hp₁, by linarith, ?_⟩
  have hT1 : 3 * B5Max d L N * K2Max d L N * (2 * p₁) ≤ T * δ := by
    have a1 : c₀ * (6 * B5Max d L N * K2Max d L N) ≤ δ :=
      (le_div_iff₀ (by positivity)).1 hc₀1
    have a2 : 3 * B5Max d L N * K2Max d L N * (2 * p₁) ≤
        3 * B5Max d L N * K2Max d L N * (2 * (c₀ * T)) := by gcongr
    have a4 : (c₀ * (6 * B5Max d L N * K2Max d L N)) * T ≤ δ * T :=
      mul_le_mul_of_nonneg_right a1 hT0.le
    calc _ ≤ 3 * B5Max d L N * K2Max d L N * (2 * (c₀ * T)) := a2
      _ = (c₀ * (6 * B5Max d L N * K2Max d L N)) * T := by ring
      _ ≤ δ * T := a4
      _ = T * δ := mul_comm _ _
  have hT2 : B5Max d L N * (2 * p₁) ≤ T * fluctRadius d L N := by
    have a1 : c₀ * (2 * B5Max d L N) ≤ fluctRadius d L N :=
      (le_div_iff₀ (by positivity)).1 hc₀2
    have a2 : B5Max d L N * (2 * p₁) ≤ B5Max d L N * (2 * (c₀ * T)) := by gcongr
    have a4 : (c₀ * (2 * B5Max d L N)) * T ≤ fluctRadius d L N * T :=
      mul_le_mul_of_nonneg_right a1 hT0.le
    calc _ ≤ B5Max d L N * (2 * (c₀ * T)) := a2
      _ = (c₀ * (2 * B5Max d L N)) * T := by ring
      _ ≤ fluctRadius d L N * T := a4
      _ = T * fluctRadius d L N := mul_comm _ _
  have hTsq : β * (L : ℝ) ^ (k * (d - 2)) = T ^ 2 := by
    rw [hT, Real.sq_sqrt hb0.le]
  exact rayData_hatStepKG_pp hd hL hN k m₁ hk p₁ (2 * p₁) hm hN₁ hbig hν0 hν
    (by positivity) hδ hsm hδ'0 hδ'a hδ'b hδ'c hT0 hTsq hT1 hT2

end Ray

end LevelStep

end Balaban.Inhabited
