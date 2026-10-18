/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.StepTowerScaleT
public import Balaban.Inhabited.StepTowerDecoupleRoom
public import Balaban.Fluctuation.Prop33CloseWitness
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Towers with a large block at the collar `r₀ = 327` (`StepTowerCollarTower`)

At the collar `r₀ = 4 d L³ + L = 327` the closeness bound of the composed backgrounds carries the
factor `exp(-γ_w L^{m₁})` (FLUCTUATION §1.4, §1.5 row 6), so its ratio to the step radius is small
once the block `L^{m₁}` is large against the other constants of the tower (`exists_pow_close_le`).
The block index `m₁` of a tower is chosen together with its decoupling rate; here it is enlarged
afterwards.

* `exists_stepTower_grow`: every tower `T` has a tower `T'` with `T'.m₁ ≥ T.m₁`, `3^{T'.m₁} ≥ M`, a
  smaller step radius and the other constants of `T`, for which an eventual predicate on the step
  radius holds.  The core `FlCore` at the new block index comes from `flCore_level_eventually`
  (the block-size conditions are monotone in `m₁`), the other conditions on the step radius from
  `exists_stepTower_shrink`.
* `exists_stepTower_collar`: for every cover index `m₀`, floor `κlo` and `θ > 0` there is a tower
  with the label rate of `exists_stepTower_labelRate`, the numerics `ChainNum`, `FlNum` at the
  collar `327` and `K₂ · 2 · composedCloseBound(…, C_{Ξ1}, 327) ≤ θ`.
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation
  Balaban.Localization Balaban.Localization.LevelPair Balaban.Localization.I5Inhabited Filter
  Topology

/-- **A tower with a larger block.**  For every tower `T`, bound `M` and predicate `Pr` on
`(m₁, BG, BG₂, κ, t)` that holds eventually as `t → 0+`, there is a tower `T'` with
`M ≤ 3^{T'.m₁}`, `T.m₁ ≤ T'.m₁`, `T'.t ≤ T.t`, the other constants of `T`, and
`Pr T'.m₁ T'.BG T'.BG₂ T'.κ T'.t`. -/
theorem exists_stepTower_grow {κmin : ℝ} (T : StepTower κmin) (M : ℝ)
    (Pr : ℕ → ℝ → ℝ → ℝ → ℝ → Prop)
    (hP : ∀ m₁ BG BG₂ κ, ∀ᶠ t in 𝓝[>] (0 : ℝ), Pr m₁ BG BG₂ κ t) :
    ∃ T' : StepTower κmin, M ≤ (3 : ℝ) ^ T'.m₁ ∧ T.m₁ ≤ T'.m₁ ∧ T'.t ≤ T.t ∧ T'.c = T.c ∧
      T'.BG = T.BG ∧ T'.κ = T.κ ∧ T'.c₂ = T.c₂ ∧ T'.BG₂ = T.BG₂ ∧ T'.δc = T.δc ∧
      T'.δ = T.δ ∧ T'.δ' = T.δ' ∧ Pr T'.m₁ T'.BG T'.BG₂ T'.κ T'.t := by
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt M (by norm_num : (1 : ℝ) < 3)
  set m : ℕ := max T.m₁ n with hm
  have hTm : T.m₁ ≤ m := le_max_left _ _
  have h4 : 4 ≤ m := T.m₁_four.trans hTm
  have hMm : M ≤ (3 : ℝ) ^ m := hn.le.trans (pow_le_pow_right₀ (by norm_num) (le_max_right _ _))
  have hpow : ((3 : ℕ) : ℝ) ^ T.m₁ ≤ ((3 : ℕ) : ℝ) ^ m := pow_le_pow_right₀ (by norm_num) hTm
  obtain ⟨hC⟩ := T.core
  have hev := flCore_level_eventually (N := 2) (dgSettingNu h4) (opSettingNu h4) isLevel_Hm
    isLevel_Gp (bgHypNu m) hC.hS hC.hκ (hC.hM.trans hpow) hC.hS2 (hC.hM2.trans hpow)
  have hpos : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < t := self_mem_nhdsWithin
  have hle : ∀ᶠ t in 𝓝[>] (0 : ℝ), t ≤ T.t :=
    eventually_nhdsWithin_of_eventually_nhds ((eventually_lt_nhds T.t_pos).mono fun _ h => h.le)
  obtain ⟨t', ⟨hC'⟩, hPt, ht0, htT⟩ :=
    (hev.and ((hP m T.BG T.BG₂ T.κ).and (hpos.and hle))).exists
  obtain ⟨Ts, hTst, hTsm, hTsc, hTsB, hTsκ, hTsc₂, hTsB₂, hTsδc, hTsδ, hTsδ'⟩ :=
    exists_stepTower_shrink T ht0 htT
  have hcore : Nonempty (FlCore 2 (Gp m (rhoSep m)) (Hm m (rhoSep m)) 1 nuW Ts.c Ts.BG Ts.κ Ts.t
      (levelKc 3 3) (Cchi 3 3) Ts.c₂ Ts.BG₂ Ts.t) := by
    rw [hTsc, hTsB, hTsκ, hTst, hTsc₂, hTsB₂]
    exact ⟨hC'⟩
  have hpow' : ((3 : ℕ) : ℝ) ^ Ts.m₁ ≤ ((3 : ℕ) : ℝ) ^ m := by rw [hTsm]; exact hpow
  refine ⟨{ Ts with
    m₁ := m
    m₁_four := h4
    core := hcore
    large_block := Ts.large_block.trans hpow'
    block_base := by
      have := Ts.block_base
      push_cast at hpow'
      linarith }, hMm, hTm, ?_, hTsc, hTsB, hTsκ, hTsc₂, hTsB₂, hTsδc, hTsδ, hTsδ', ?_⟩
  · show Ts.t ≤ T.t
    rw [hTst]; exact htT
  · show Pr m Ts.BG Ts.BG₂ Ts.κ Ts.t
    rw [hTsB, hTsB₂, hTsκ, hTst]
    exact hPt

/-- **Towers at the collar `327` with a large block.**  For every cover index `m₀`, floor `κlo`
and `θ > 0` there are `κmin ≥ κlo`, a tower `T : StepTower κmin` and constants `δ₃`, `δ_fl`,
`κ_dec` with `ChainNum`, `FlNum` at the collar `327` and the step radius `T.t`, the two label-rate
inequalities at `m₀`, and the closeness ratio `K₂ · 2 · composedCloseBound(…, C_{Ξ1}, 327) ≤ θ`. -/
theorem exists_stepTower_collar (m₀ : ℕ) (κlo : ℝ) {θ : ℝ} (hθ : 0 < θ) :
    ∃ (κmin : ℝ) (_ : κlo ≤ κmin) (T : StepTower κmin) (δ₃ δfl κdec : ℝ),
      ChainNum 3 3 2 T.m₁ T.BG T.κ 327 T.t δ₃ ∧ FlNum 3 3 2 T.BG T.BG₂ T.κ T.t δ₃ T.t δfl ∧
      4 * 3 * (((2 * 3 + 1) ^ 3 : ℕ) : ℝ) * κdec ≤ T.κ ∧
      (2 * T.κdec - 1) * (((3 : ℕ) : ℝ) ^ (m₀ - 1) + 2 * ((3 : ℕ) : ℝ) *
        ((3 : ℕ) : ℝ) ^ m₀ * ((((3 ^ (m₀ - 1)) ^ 3 : ℕ)) : ℝ) * c1 3 3) + 1 ≤ 2 * κdec ∧
      xiK2 3 3 2 * (2 * composedCloseBound 3 3 2 T.m₁ T.BG T.κ (xiC1 3) 327) ≤ θ := by
  obtain ⟨κmin, hlo, hk⟩ := exists_stepTower_labelRate m₀ κlo
  obtain ⟨T₁⟩ := exists_stepTower κmin
  obtain ⟨hC₁⟩ := T₁.core
  obtain ⟨M, hM⟩ := exists_pow_close_le (BG := T₁.BG) (κ := T₁.κ) hC₁.hS.fam.2.1 hθ
  obtain ⟨T, hMT, -, -, -, hB, hκ, -, -, -, -, -, hPr⟩ := exists_stepTower_grow T₁ M
    (fun m₁ BG BG₂ κ t => 0 ≤ BG → 0 ≤ BG₂ → ∃ δ₃ δfl : ℝ,
      ChainNum 3 3 2 m₁ BG κ 327 t δ₃ ∧ FlNum 3 3 2 BG BG₂ κ t δ₃ t δfl)
    (fun m₁ BG BG₂ κ => by
      by_cases h : 0 ≤ BG ∧ 0 ≤ BG₂
      · exact (BgSettingData.joint_num_eventually 3 3 2 m₁ (by norm_num) h.1 h.2 κ 327).mono
          fun t ht _ _ => ht
      · exact Eventually.of_forall fun t h1 h2 => absurd ⟨h1, h2⟩ h)
  obtain ⟨hC⟩ := T.core
  obtain ⟨δ₃, δfl, h1, h2⟩ := hPr hC.hS.fam.2.1 hC.hS2.fam.2.1
  obtain ⟨κdec, h3, h4⟩ := hk T
  refine ⟨κmin, hlo, T, δ₃, δfl, κdec, h1, h2, h3, h4, ?_⟩
  rw [hB, hκ]
  exact hM T.m₁ hMT

end Balaban.Inhabited
