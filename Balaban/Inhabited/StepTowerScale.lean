/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.StepTower
public import Balaban.Inhabited.LevelRayTower
public import Balaban.Fluctuation.LevelLocalCover
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The shared tower at each scale (`d = L = 3`, `N = 2`)

For a fixed `T : StepTower κmin`, `StepScaleData T k hk N₁ ν β p₁` bundles once the objects that
every landed scale theorem re-derives from its own tower call, for the step
`hatStepK k T.m₁ hk ν β p₁ T.δ`: the transferred `FlCore` on `lvTop/lvLow`, the `XiCData` of the
step, the ray data, the radius inequalities of `scale_C_items`, and the block and source-site
covers of `levelLocalCover`.  The fields are stated directly on the term `hatStepK …`
(`StepTower.step`).

* `StepTower.scale`: one threshold `βray ≥ 2`, chosen before the scale index, after which
  `StepScaleData` is inhabited at every admissible scale.
* `StepTower.scale_instance`: the record at `k = 1`, `N₁ = 6`.
* `detExpansionLocC_scale_fromTower`: the localized determinant family at every scale, as a thin
  wrapper of `detExpansionLocC_scale_of_tower`.

The four remaining endpoints (source activity, chart/determinant, `sourceFamilyRelative`,
`expSourceChart`) are not in this file.
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation
  Balaban.Localization Balaban.Localization.LevelPair Balaban.Localization.I5Inhabited
  Balaban.Polymer Balaban.SmallField.Def6 Balaban.Inhabited.LevelStep Filter Topology

/-- The covers of `levelLocalCover` for `d = L = 3`, `N = 2`: for every block `z` the cover
setup, the neighbourhood equality, the connected structure, zero tree length, the read sites and
the block margin; for every source site the same with `x = s.1`. -/
def LevelCovers (N₁ m₁ k : ℕ) [NeZero N₁] (ϱ ϱm : ℝ)
    (Gp : GeneratingSet 3 3 (N₁ * 3 ^ m₁) (k + 1) ϱ)
    (Hm : GeneratingSet 3 3 (N₁ * 3 ^ m₁) (k + 1) ϱm) (m₀ : ℕ) : Prop :=
  (∀ z : Torus 3 (N₁ * 3 ^ m₁ * 3 ^ (k + 1 - (k + 1))),
      CovSetup Gp m₀ k (LocalCover.cube m₀ k (LocalCover.blockSite k z))
        (LocalCover.fam m₀ (LocalCover.blockSite k z)) ∧
      (↑(LocalCover.nbhdF m₀ (LocalCover.blockSite k z)) : Set (CTorus 3 3 N₁ m₁ (k + 1))) =
        X1 Gp m₀ k (LocalCover.fam m₀ (LocalCover.blockSite k z)) ∧
      (∃ (W₀ : Finset (CTorus 3 3 N₁ m₁ (k + 1)))
        (E₀ : Finset (CTorus 3 3 N₁ m₁ (k + 1) × CTorus 3 3 N₁ m₁ (k + 1))),
        ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ LocalCover.cube m₀ k (LocalCover.blockSite k z)) ∧
          MeetsOne m₀ k (LocalCover.fam m₀ (LocalCover.blockSite k z)) W₀ ∧
          bondCost (scaleW 3 m₀ m₁ k) E₀ =
            treeLenCovOne m₀ k (LocalCover.cube m₀ k (LocalCover.blockSite k z))) ∧
      treeLenCovOne m₀ k (LocalCover.cube m₀ k (LocalCover.blockSite k z)) = 0 ∧
      readSites Hm k z ⊆ ↑(LocalCover.nbhdF m₀ (LocalCover.blockSite k z)) ∧
      BlockMargin Gp (LocalCover.nbhdF m₀ (LocalCover.blockSite k z))
        (↑(blockSites 3 3 N₁ m₁ (k + 1) k z) : Set (CTorus 3 3 N₁ m₁ (k + 1))) ∧
      (↑(blockSites 3 3 N₁ m₁ (k + 1) k z) : Set (CTorus 3 3 N₁ m₁ (k + 1))) ⊆
        ↑(LocalCover.nbhdF m₀ (LocalCover.blockSite k z))) ∧
    (∀ s : CTorus 3 3 N₁ m₁ (k + 1) × Fin 2,
      CovSetup Gp m₀ k (LocalCover.cube m₀ k s.1) (LocalCover.fam m₀ s.1) ∧
      (↑(LocalCover.nbhdF m₀ s.1) : Set (CTorus 3 3 N₁ m₁ (k + 1))) =
        X1 Gp m₀ k (LocalCover.fam m₀ s.1) ∧
      (∃ (W₀ : Finset (CTorus 3 3 N₁ m₁ (k + 1)))
        (E₀ : Finset (CTorus 3 3 N₁ m₁ (k + 1) × CTorus 3 3 N₁ m₁ (k + 1))),
        ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ LocalCover.cube m₀ k s.1) ∧
          MeetsOne m₀ k (LocalCover.fam m₀ s.1) W₀ ∧
          bondCost (scaleW 3 m₀ m₁ k) E₀ =
            treeLenCovOne m₀ k (LocalCover.cube m₀ k s.1)) ∧
      treeLenCovOne m₀ k (LocalCover.cube m₀ k s.1) = 0 ∧
      s.1 ∈ LocalCover.nbhdF m₀ s.1)

namespace StepTower

variable {κmin : ℝ}

/-- The step `hatStepK k T.m₁ hk ν β p₁ T.δ` of the tower `T`. -/
noncomputable abbrev step (T : StepTower κmin) (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁]
    (ν β p₁ : ℝ) : StepSetting 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁) :=
  hatStepK (N₁ := N₁) k T.m₁ hk ν β p₁ T.δ

end StepTower

/-- **The per-scale package of the tower `T`.**  All fields are stated on the step
`T.step k hk N₁ ν β p₁ = hatStepK k T.m₁ hk ν β p₁ T.δ`. -/
structure StepScaleData {κmin : ℝ} (T : StepTower κmin) (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ)
    [NeZero N₁] (ν β p₁ : ℝ) : Prop where
  core : FlCore 2 (lvTop N₁ T.m₁ k (rhoSep T.m₁)) (lvLow N₁ T.m₁ k (rhoSep T.m₁)) 1 ν T.c T.BG
    T.κ T.t (levelKc 3 3) (Cchi 3 3) T.c₂ T.BG₂ T.t
  xi : XiCData (T.step k hk N₁ ν β p₁).G' (compWeight 3 1) ν (k + 1) 1 T.t
    (T.step k hk N₁ ν β p₁).D'
  ray : Nonempty ((T.step k hk N₁ ν β p₁).RayData (2 * p₁))
  cψ_pos : 0 < lvCpsi T.κ T.t (β * 3 ^ k)
  r_pos : 0 < lvR T.κ T.t (β * 3 ^ k) p₁
  fl_radius : Real.sqrt ((2 : ℕ) : ℝ) *
    (‖(((T.step k hk N₁ ν β p₁).betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)‖ *
      (covSupConstC 3 3 2 (compWeight 3 (1 : ℝ) k) T.κ * lvCpsi T.κ T.t (β * 3 ^ k))) < T.t
  ray_margin : ((2 : ℝ) * 2 + lvR T.κ T.t (β * 3 ^ k) p₁) * p₁ < lvCpsi T.κ T.t (β * 3 ^ k)
  p_lt : p₁ < 2 * p₁
  covers : LevelCovers N₁ T.m₁ k (rhoSep T.m₁) (rhoSep T.m₁) (lvTop N₁ T.m₁ k (rhoSep T.m₁))
    (lvLow N₁ T.m₁ k (rhoSep T.m₁)) 1

namespace StepTower

variable {κmin : ℝ}

/-- **The tower at every scale.**  One threshold `βray ≥ 2`, chosen before the scale index, after
which `StepScaleData` is inhabited at every admissible scale. -/
theorem scale (T : StepTower κmin) {A₁ : ℝ} (hA : 0 < A₁) (p : ℕ) :
    ∃ βray : ℝ, 2 ≤ βray ∧ ∀ (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁], 3 ∣ N₁ → 5 < N₁ →
      ∀ ν : ℝ, 0 ≤ ν → ν * 3 ^ (2 * (k + 1)) ≤ 1 → ∀ β : ℝ, βray ≤ β →
      ∀ p₁ : ℝ, 0 < p₁ → p₁ ≤ pLog A₁ p (β * 3 ^ k) →
      Nonempty (StepScaleData T k hk N₁ ν β p₁) := by
  classical
  obtain ⟨β₀, hβ₀, hitems⟩ := scale_C_items hA p T.m₁ T.m₁_four T.block_base T.κ T.t_pos
    T.δ_pos T.δ_small T.δ'_pos T.δ'_cap T.δ'_step T.δ'_coer
  refine ⟨β₀, hβ₀, ?_⟩
  intro k hk N₁ _ h3N hN ν hν0 hν β hβ p₁ hp0 hp₁
  obtain ⟨hcψ0, hr0, hδ₁, hc, hlt, hR⟩ := hitems k hk N₁ hN ν hν0 hν β hβ p₁ hp0 hp₁
  have hSD := dgSetting_lv (N₁ := N₁) (k := k) T.m₁_four hN hν0 hν
  have hHB := bgHyp_lv (k := k) T.m₁ hν0 hν
  have hC : FlCore 2 (lvTop N₁ T.m₁ k (rhoSep T.m₁)) (lvLow N₁ T.m₁ k (rhoSep T.m₁)) 1 ν T.c
      T.BG T.κ T.t (levelKc 3 3) (Cchi 3 3) T.c₂ T.BG₂ T.t :=
    flCore_level_transfer (Classical.choice T.core) hSD (opSetting_lv T.m₁_four hN hν0 hν)
      (isLevel_lvLow hk) isLevel_lvTop hHB
  have hD : XiCData (T.step k hk N₁ ν β p₁).G' (compWeight 3 1) ν (k + 1) 1 T.t
      (T.step k hk N₁ ν β p₁).D' := by
    refine ⟨fun _ => unitVec hN2, unitVec hN2, 0, 0,
      exists_xiC hHB (lvTop N₁ T.m₁ k (rhoSep T.m₁)) hN2 (massLe_lv hν) T.t_pos, ?_, ?_⟩
    · intro x hx i
      have := unitBg_Ψ_of_mem (lvTop N₁ T.m₁ k (rhoSep T.m₁)) hN2 (unitVec hN2) hx i
      show (unitBg (lvTop N₁ T.m₁ k (rhoSep T.m₁)) hN2 (unitVec hN2)).Ψ x i = _
      rw [this]; simp
    · intro x hx i
      have := unitBg_h_of_mem (lvTop N₁ T.m₁ k (rhoSep T.m₁)) hN2 (unitVec hN2) hx i
      show (unitBg (lvTop N₁ T.m₁ k (rhoSep T.m₁)) hN2 (unitVec hN2)).h x i = _
      rw [this]; simp
  have hN3 : 3 ^ 1 ∣ N₁ := by simpa using h3N
  obtain ⟨hV, hF⟩ := LocalCover.levelLocalCover (N := 2) (lvLow N₁ T.m₁ k (rhoSep T.m₁)) hSD
    (isLevel_lvTop (N₁ := N₁) (m₁ := T.m₁) (k := k) (ϱ := rhoSep T.m₁)) (m₀ := 1) le_rfl hN3
  exact ⟨⟨hC, hD, hR, hcψ0, hr0, hδ₁, hc, hlt, ⟨hV, hF⟩⟩⟩

/-- Normalization of the determinant rate denominator. -/
theorem det_rate_den : (2 * ((3 : ℕ) : ℝ) * ((3 : ℕ) : ℝ)) = 18 := by norm_num

/-- Normalization of the determinant constant. -/
theorem det_const_eq (c w : ℝ) :
    ((3 : ℕ) : ℝ) ^ 3 * ((1 / 2 : ℝ) * (2 : ℕ) * c / w) = 27 * c / w := by
  push_cast; ring

/-- **Non-vacuity at one scale.**  For every tower, with `k = 1`, `N₁ = 6`, `ν = 0`, `A₁ = 1`,
`p = 0` (so the cutoff is `p₁ = 1`), the record is inhabited at `β = βray`. -/
theorem scale_instance (T : StepTower κmin) :
    ∃ βray : ℝ, 2 ≤ βray ∧ Nonempty (StepScaleData T 1 le_rfl 6 0 βray 1) := by
  obtain ⟨βray, h2, h⟩ := T.scale (A₁ := 1) one_pos 0
  refine ⟨βray, h2, ?_⟩
  have hb : (1 : ℝ) < βray * 3 ^ 1 := by norm_num; linarith
  exact h 1 le_rfl 6 (by norm_num) (by norm_num) 0 le_rfl (by norm_num) βray le_rfl 1
    one_pos (by simp [pLog])

end StepTower

open Classical in
/-- **The localized determinant family at every scale of the tower `T`.**  No threshold on `β`. -/
theorem detExpansionLocC_scale_fromTower {κmin : ℝ} (T : StepTower κmin)
    (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁] (h3N : 3 ∣ N₁) (hN : 5 < N₁) {ν : ℝ}
    (hν0 : 0 ≤ ν) (hν : ν * 3 ^ (2 * (k + 1)) ≤ 1) (β p₁ : ℝ) :
    (∀ z, ∃ E : DetExpansionLocC (T.step k hk N₁ ν β p₁) 1 z T.t
        ((T.κ - Real.log 2 - 2 * Real.log ((detDeg 3 3 + 1 : ℕ) : ℝ)) / 18)
        (27 * covBLogMax 3 3 T.κ /
          (1 - ((detDeg 3 3 + 1 : ℕ) : ℝ) ^ 2 * (2 / Real.exp T.κ))),
      ∀ D T', E.term D T' = ∑ y ∈ (T.step k hk N₁ ν β p₁).blockU z,
        detActivityBg 1 (compWeight 3 1) 1 ν (rho4 3 3 2 T.BG T.κ) D y T') ∧
    T.κ' ≤ (T.κ - Real.log 2 - 2 * Real.log ((detDeg 3 3 + 1 : ℕ) : ℝ)) / 18 := by
  refine ⟨?_, T.det_rate⟩
  have h := (detExpansionLocC_scale_of_tower T.m₁_four T.t_pos (Classical.choice T.core)
    T.large_block T.dom_margin T.coer_margin T.δc_small T.det_z k hk N₁ h3N hN hν0 hν β p₁
    T.δ).2
  intro z
  have hz := h z
  rw [StepTower.det_rate_den, StepTower.det_const_eq] at hz
  exact hz

end Balaban.Inhabited
