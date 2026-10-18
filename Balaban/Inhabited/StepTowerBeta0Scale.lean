/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.StepTowerBeta0Core
public import Balaban.Inhabited.LevelRayDataGeneral
public import Balaban.Inhabited.StepScaleDataG
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

/-!
# The numerical items of the scale record, uniformly in the step radius

`scale_C_items_numeric_agree`, `scale_C_items_general_agree`: the statements of
`scale_C_items_numeric`, `scale_C_items_general` with the radius `t` a variable after the
threshold: one `β₀` serves every `t ≥ c L^{-α(k+1)}` (`2 α < d - 2`).  The cutoff condition is
`p₁ ≤ c' t √b` (`exists_beta0_pLog_le_t_sqrt`).
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation
  Balaban.Localization Balaban.Localization.LevelPair Balaban.Localization.I5Inhabited
  Balaban.Polymer Balaban.SmallField.Def6

namespace LevelStep

/-- **The numeric items at every scale, uniformly in the step radius.** -/
theorem scale_C_items_numeric_agree {d L N : ℕ} (hd : 3 ≤ d) (hL : 3 ≤ L) (hN : 1 ≤ N) {A₁ : ℝ}
    (hA : 0 < A₁) (p : ℕ) {c α : ℝ} (hc : 0 < c) (hα : 2 * α < ((d - 2 : ℕ) : ℝ)) (κ : ℝ) :
    ∃ β₀ : ℝ, 3 ≤ β₀ ∧ ∀ (t : ℝ) (k : ℕ), 1 ≤ k → ∀ β : ℝ, β₀ ≤ β →
      c * (L : ℝ) ^ (-(α * ((k : ℝ) + 1))) ≤ t →
      ∀ p₁ : ℝ, 0 < p₁ → p₁ ≤ pLog A₁ p (β * (L : ℝ) ^ (k * (d - 2))) →
      0 < lvCpsiG d L N κ t (β * (L : ℝ) ^ (k * (d - 2))) ∧
      0 < lvRG d L N κ t (β * (L : ℝ) ^ (k * (d - 2))) p₁ ∧
      Real.sqrt (N : ℝ) *
        (‖(((β * (L : ℝ) ^ (k * (d - 2))) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)‖ *
          (covSupConstC d L N (compWeight L (1 : ℝ) k) κ *
            lvCpsiG d L N κ t (β * (L : ℝ) ^ (k * (d - 2))))) < t ∧
      ((2 : ℝ) * 2 + lvRG d L N κ t (β * (L : ℝ) ^ (k * (d - 2))) p₁) * p₁ <
        lvCpsiG d L N κ t (β * (L : ℝ) ^ (k * (d - 2))) := by
  have hd0 : 0 < d := by omega
  have hs : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hN)
  have hCm := covSupMaxC_nonneg_general (N := N) hd0 hL κ
  set κ₀ : ℝ := 1 / (2 * Real.sqrt (N : ℝ) * (covSupMaxC d L N κ + 1)) with hκ₀
  have hκ₀0 : 0 < κ₀ := by rw [hκ₀]; positivity
  obtain ⟨β₂, hβ₂, H⟩ := exists_beta0_pLog_le_t_sqrt hd hL hA.le p hc (c' := κ₀ / 16) (by positivity)
    hα
  refine ⟨β₂, hβ₂, ?_⟩
  intro t k hk β hβ hct p₁ hp0 hp₁
  have ht : 0 < t := lt_of_lt_of_le (by positivity) hct
  have hβ2 : 2 ≤ β := by linarith
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast (by omega : 1 ≤ L)
  have h3k : (1 : ℝ) ≤ (L : ℝ) ^ (k * (d - 2)) := one_le_pow₀ hL1
  set b : ℝ := β * (L : ℝ) ^ (k * (d - 2)) with hb
  have hbβ : β ≤ b := by rw [hb]; nlinarith
  have hb1 : (1 : ℝ) < b := by linarith
  have hb0 : 0 < b := by linarith
  set κ₁ : ℝ := lvKappaG d L N κ t with hκ₁
  have hκ₁t : κ₁ = κ₀ * t := by rw [hκ₁, hκ₀]; unfold lvKappaG; field_simp
  have hκ₁0 : 0 < κ₁ := by rw [hκ₁t]; positivity
  have hle : p₁ ≤ κ₁ / 16 * Real.sqrt b := by
    have := H k β t p₁ hβ hct hp0 hp₁
    rw [hκ₁t]
    calc p₁ ≤ κ₀ / 16 * t * Real.sqrt b := this
      _ = κ₀ * t / 16 * Real.sqrt b := by ring
  set T : ℝ := Real.sqrt b with hT
  have hT0 : 0 < T := Real.sqrt_pos.2 hb0
  have hcψ : lvCpsiG d L N κ t b = κ₁ * T := lvCpsiG_eq d L N κ t b
  have hcψ0 : 0 < lvCpsiG d L N κ t b := by rw [hcψ]; positivity
  have h8 : 8 * p₁ < lvCpsiG d L N κ t b := by
    rw [hcψ]
    have h4 : 0 < κ₁ * T := by positivity
    nlinarith
  have hr0 : 0 < lvRG d L N κ t b p₁ := by
    unfold lvRG
    have : 4 < lvCpsiG d L N κ t b / (2 * p₁) := by
      rw [lt_div_iff₀ (by positivity)]; linarith
    linarith
  refine ⟨hcψ0, hr0, ?_, ?_⟩
  · rw [Complex.norm_real, Real.norm_of_nonneg (by positivity), hcψ]
    have e : b ^ (-(1 / 2 : ℝ)) = T⁻¹ := by
      rw [Real.rpow_neg hb0.le, ← Real.sqrt_eq_rpow]
    rw [e]
    have hmem := compWeight_one_mem hL hk
    have hC0 : 0 ≤ covSupConstC d L N (compWeight L (1 : ℝ) k) κ :=
      covSupConstC_nonneg hd0 hL (by linarith [hmem.1]) κ
    have hCle : covSupConstC d L N (compWeight L (1 : ℝ) k) κ ≤ covSupMaxC d L N κ :=
      covSupConstC_le_covSupMaxC hd0 hL κ hmem
    have e2 : Real.sqrt (N : ℝ) * (T⁻¹ *
        (covSupConstC d L N (compWeight L (1 : ℝ) k) κ * (κ₁ * T))) =
        covSupConstC d L N (compWeight L (1 : ℝ) k) κ * t / (2 * (covSupMaxC d L N κ + 1)) := by
      rw [hκ₁t, hκ₀]; field_simp
    rw [e2, div_lt_iff₀ (by positivity)]
    nlinarith
  · unfold lvRG
    have : (2 * 2 + (lvCpsiG d L N κ t b / (2 * p₁) - 4)) * p₁ = lvCpsiG d L N κ t b / 2 := by
      field_simp; ring
    rw [this]
    linarith

/-- **The cutoff, radius and `RayData` hypotheses at every scale, uniformly in the step radius.**
The threshold `β₀` depends on `d, L, N, A₁, p, c, α` and on reference values `κ₀`, `δ₀` of `κ`
and `δ` only; it serves every `t ≥ c L^{-α(k+1)}` and all `m₁, δ, δ', κ` with `κ = κ₀`,
`δ = δ₀`. -/
theorem scale_C_items_general_agree {d L N : ℕ} [NeZero L] (hd : 3 ≤ d) (hL : 3 ≤ L) (hN : 2 ≤ N)
    {A₁ : ℝ} (hA : 0 < A₁) (p : ℕ) {c α : ℝ} (hc : 0 < c) (hα : 2 * α < ((d - 2 : ℕ) : ℝ))
    (κ₀ δ₀ : ℝ) :
    ∃ β₀ : ℝ, 3 ≤ β₀ ∧ ∀ (t : ℝ) (m₁ : ℕ) (δ δ' κ : ℝ), 4 ≤ m₁ → cstarX d L ≤ (L : ℝ) ^ m₁ →
      κ = κ₀ → δ = δ₀ → 0 < δ → δ ^ 2 * smallConstX d L 0 ≤ 1 / 4 → 0 < δ' →
      δ' ≤ thm73C3 d L N / 2 → bgK1 d L N * δ' ≤ δ / 4 → bgK1 d L N * δ' ≤ coerciveConst d / 4 →
      ∀ (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁], 5 < N₁ →
      ∀ ν : ℝ, 0 ≤ ν → ν * (L : ℝ) ^ (2 * (k + 1)) ≤ 1 → ∀ β : ℝ, β₀ ≤ β →
      c * (L : ℝ) ^ (-(α * ((k : ℝ) + 1))) ≤ t →
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
  obtain ⟨β₁, hβ₁, hnum⟩ := scale_C_items_numeric_agree (d := d) (L := L) (N := N) hd hL
    (by omega) hA p hc hα κ₀
  by_cases hδ₀ : 0 < δ₀
  swap
  · refine ⟨max β₁ 3, (le_max_right _ _), ?_⟩
    intro t m₁ δ δ' κ hm hbig hκ hδ hδpos
    exact absurd (hδ ▸ hδpos) hδ₀
  set c₀ : ℝ := min (δ₀ / (6 * B5Max d L N * K2Max d L N))
    (fluctRadius d L N / (2 * B5Max d L N)) with hc₀
  have hc₀0 : 0 < c₀ := lt_min (by positivity) (by positivity)
  have hc₀1 : c₀ ≤ δ₀ / (6 * B5Max d L N * K2Max d L N) := min_le_left _ _
  have hc₀2 : c₀ ≤ fluctRadius d L N / (2 * B5Max d L N) := min_le_right _ _
  refine ⟨max β₁ (pLogThreshold A₁ p c₀), hβ₁.trans (le_max_left _ _), ?_⟩
  intro t m₁ δ δ' κ hm hbig hκ hδ hδ0 hsm hδ'0 hδ'a hδ'b hδ'c k hk N₁ _ hN₁ ν hν0 hν β hβ hct p₁ hp0
    hp₁
  subst hκ hδ
  have hβ1 : β₁ ≤ β := (le_max_left _ _).trans hβ
  have hβ2 : 2 ≤ β := by linarith [hβ₁.trans hβ1]
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
  refine ⟨hnum t k hk β hβ1 hct p₁ hp0 hp₁, by linarith, ?_⟩
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
    (by positivity) hδ0 hsm hδ'0 hδ'a hδ'b hδ'c hT0 hTsq hT1 hT2

end LevelStep

namespace StepTowerG

open Balaban.Inhabited.LevelStep

variable {d L N : ℕ} [NeZero L] {κmin : ℝ}

/-- **The general tower at every scale, uniformly in the step radius.**  One threshold
`βray ≥ 3` for all towers with the `κ`, `δ` of the reference tower `T₀`, every
`t ≥ c L^{-α(k+1)}` and `2 α < d - 2`. -/
theorem scale_agree (T₀ : StepTowerG d L N κmin) {A₁ : ℝ} (hA : 0 < A₁) (p : ℕ) {c α : ℝ}
    (hc : 0 < c) (hα : 2 * α < ((d - 2 : ℕ) : ℝ)) :
    ∃ βray : ℝ, 3 ≤ βray ∧ ∀ T : StepTowerG d L N κmin, T.κ = T₀.κ → T.δ = T₀.δ →
      ∀ (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁], L ^ T.m₀ ∣ N₁ →
      5 < N₁ → ∀ ν : ℝ, 0 ≤ ν → ν * (L : ℝ) ^ (2 * (k + 1)) ≤ 1 → ∀ β : ℝ, βray ≤ β →
      c * (L : ℝ) ^ (-(α * ((k : ℝ) + 1))) ≤ T.t →
      ∀ p₁ : ℝ, 0 < p₁ → p₁ ≤ pLog A₁ p (β * (L : ℝ) ^ (k * (d - 2))) →
      Nonempty (StepScaleDataG T k hk N₁ ν β p₁) := by
  classical
  obtain ⟨β₀, hβ₀, hitems⟩ := LevelStep.scale_C_items_general_agree T₀.hd T₀.hL T₀.hN hA p hc hα
    T₀.κ T₀.δ
  refine ⟨β₀, hβ₀, ?_⟩
  intro T hκ hδ k hk N₁ _ hdvd hN ν hν0 hν β hβ hct p₁ hp0 hp₁
  obtain ⟨⟨hcψ0, hr0, hδ₁, hc⟩, hlt, hR⟩ := hitems T.t T.m₁ T.δ T.δ' T.κ T.m₁_four T.block_base hκ
    hδ T.δ_pos T.δ_small T.δ'_pos T.δ'_cap T.δ'_step T.δ'_coer k hk N₁ hN ν hν0 hν β hβ hct p₁ hp0
    hp₁
  have hN0 : 0 < N := Nat.lt_of_lt_of_le two_pos T.hN
  have hSD := dgSetting_lvG (N₁ := N₁) (k := k) T.hd T.hL T.m₁_four hN hν0 hν
  have hHB := bgHyp_lvG (k := k) T.hd T.hL
    (bgR0_le_rhoSepG T.m₁ T.hd T.hL) hν0 hν
  have hC : FlCore N (lvTopG d L N₁ T.m₁ k (rhoSepG d L T.m₁))
      (lvLowG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) 1 ν T.c T.BG T.κ T.t
      (levelKc d L) (Cchi d L) T.c₂ T.BG₂ T.t :=
    flCore_level_transfer (Classical.choice T.core) hSD
      (opSetting_lvG T.hd T.hL T.m₁_four hN hν0 hν)
      (isLevel_lvLowG hk) isLevel_lvTopG hHB
  have hD : XiCData (T.step k hk N₁ ν β p₁).G' (compWeight L 1) ν (k + 1) 1 T.t
      (T.step k hk N₁ ν β p₁).D' := by
    refine ⟨fun _ => unitVec hN0, unitVec hN0, 0, 0,
      exists_xiC hHB (lvTopG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) hN0 (massLe_lvG hν) T.t_pos,
      ?_, ?_⟩
    · intro x hx i
      have := unitBg_Ψ_of_mem (lvTopG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) hN0 (unitVec hN0) hx i
      show (unitBg (lvTopG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) hN0 (unitVec hN0)).Ψ x i = _
      rw [this]; simp
    · intro x hx i
      have := unitBg_h_of_mem (lvTopG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) hN0 (unitVec hN0) hx i
      show (unitBg (lvTopG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) hN0 (unitVec hN0)).h x i = _
      rw [this]; simp
  have hcov := levelCoversG_of_dvd (N := N) (lvLowG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) hSD
    (isLevel_lvTopG (N₁ := N₁) (m₁ := T.m₁) (k := k) (ϱ := rhoSepG d L T.m₁))
    T.m₀_pos hdvd
  have hbU := hatStepKG_betaU (d := d) (L := L) (N₁ := N₁) T.hN (by have := T.hd; omega)
    k T.m₁ (rhoSepG d L T.m₁) hk ν β p₁ T.δ
  refine ⟨⟨hC, hD, hR, hcψ0, hr0, ?_, hc, hlt, hcov⟩⟩
  rw [show (T.step k hk N₁ ν β p₁).betaU = β * (L : ℝ) ^ (k * (d - 2)) from hbU]
  exact hδ₁

end StepTowerG

end Balaban.Inhabited
