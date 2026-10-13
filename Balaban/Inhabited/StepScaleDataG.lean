/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.LevelCoversG
public import Balaban.Inhabited.StepTowerG
public import Balaban.Inhabited.LevelRayDataGeneral
public import Balaban.Inhabited.LevelStepSettingGeneral

/-!
# The general tower at each scale

For `T : StepTowerG d L N κmin`, `StepTowerG.step` is the step `hatStepKG` of the tower and
`StepScaleDataG T k hk N₁ ν β p₁` is the literal generalization of `StepScaleData`: the
transferred `FlCore` on the top and lower levels, the `XiCData` of the step, the ray data, the
radius inequalities, and the block and source-site covers at the tower's cover index `T.m₀`.
`StepTowerG.scale` chooses one threshold `βray ≥ 2` and then inhabits the record at every
admissible scale.
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation
  Balaban.Localization Balaban.Localization.LevelPair Balaban.Localization.I5Inhabited
  Balaban.Polymer Balaban.SmallField.Def6 LevelStep

namespace StepTowerG

variable {d L N : ℕ} [NeZero L] {κmin : ℝ}

/-- The step `hatStepKG … T.δ` of the tower `T` at level `k`, torus parameter `N₁`. -/
noncomputable abbrev step (T : StepTowerG d L N κmin) (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ)
    [NeZero N₁] (ν β p₁ : ℝ) : StepSetting d L N₁ T.m₁ k N (rhoSepG d L T.m₁) :=
  hatStepKG (N₁ := N₁) T.hN k T.m₁ (rhoSepG d L T.m₁) hk ν β p₁ T.δ

end StepTowerG

/-- **The per-scale package of the general tower `T`.**  All fields are stated on the step
`T.step k hk N₁ ν β p₁`. -/
structure StepScaleDataG {d L N : ℕ} [NeZero L] {κmin : ℝ} (T : StepTowerG d L N κmin)
    (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁] (ν β p₁ : ℝ) : Prop where
  core : FlCore N (lvTopG d L N₁ T.m₁ k (rhoSepG d L T.m₁))
    (lvLowG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) 1 ν T.c T.BG T.κ T.t
    (levelKc d L) (Cchi d L) T.c₂ T.BG₂ T.t
  xi : XiCData (T.step k hk N₁ ν β p₁).G' (compWeight L 1) ν (k + 1) 1 T.t
    (T.step k hk N₁ ν β p₁).D'
  ray : Nonempty ((T.step k hk N₁ ν β p₁).RayData (2 * p₁))
  cψ_pos : 0 < lvCpsiG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2)))
  r_pos : 0 < lvRG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2))) p₁
  fl_radius : Real.sqrt (N : ℝ) *
    (‖(((T.step k hk N₁ ν β p₁).betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)‖ *
      (covSupConstC d L N (compWeight L (1 : ℝ) k) T.κ *
        lvCpsiG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2))))) < T.t
  ray_margin : ((2 : ℝ) * 2 + lvRG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2))) p₁) * p₁ <
    lvCpsiG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2)))
  p_lt : p₁ < 2 * p₁
  covers : LevelCoversG d L N N₁ T.m₁ k (rhoSepG d L T.m₁) (rhoSepG d L T.m₁)
    (lvTopG d L N₁ T.m₁ k (rhoSepG d L T.m₁))
    (lvLowG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) T.m₀

namespace StepTowerG

variable {d L N : ℕ} [NeZero L] {κmin : ℝ}

/-- **The general tower at every scale.**  One threshold `βray ≥ 2`, chosen before the scale
index, after which `StepScaleDataG` is inhabited at every admissible scale.  The hypothesis
`5 < N₁` feeds the level pair and the ray data; `L ^ T.m₀ ∣ N₁` feeds the covers. -/
theorem scale (T : StepTowerG d L N κmin) {A₁ : ℝ} (hA : 0 < A₁) (p : ℕ) :
    ∃ βray : ℝ, 2 ≤ βray ∧ ∀ (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁], L ^ T.m₀ ∣ N₁ →
      5 < N₁ → ∀ ν : ℝ, 0 ≤ ν → ν * (L : ℝ) ^ (2 * (k + 1)) ≤ 1 → ∀ β : ℝ, βray ≤ β →
      ∀ p₁ : ℝ, 0 < p₁ → p₁ ≤ pLog A₁ p (β * (L : ℝ) ^ (k * (d - 2))) →
      Nonempty (StepScaleDataG T k hk N₁ ν β p₁) := by
  classical
  obtain ⟨β₀, hβ₀, hitems⟩ := scale_C_items_general T.hd T.hL T.hN hA p T.m₁ T.m₁_four
    T.block_base T.κ T.t_pos T.δ_pos T.δ_small T.δ'_pos T.δ'_cap T.δ'_step T.δ'_coer
  refine ⟨β₀, hβ₀, ?_⟩
  intro k hk N₁ _ hdvd hN ν hν0 hν β hβ p₁ hp0 hp₁
  obtain ⟨⟨hcψ0, hr0, hδ₁, hc⟩, hlt, hR⟩ := hitems k hk N₁ hN ν hν0 hν β hβ p₁ hp0 hp₁
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
