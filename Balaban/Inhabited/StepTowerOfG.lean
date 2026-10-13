/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.StepTower
public import Balaban.Inhabited.StepTowerRen
public import Balaban.Inhabited.StepTowerG
public import Balaban.Inhabited.StepTowerRenG
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The fixed towers from the general towers

A general tower at `d = L = 3`, `N = 2` with `κ₀ = a_Ent + 2` and cover index `m₀ = 1` gives a
fixed tower; the same for the towers with the renormalization margins.  The fixed producer
`exists_stepTowerRen` is the corollary of the general producer `exists_stepTowerRenG` through
these maps.
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation
  Balaban.Localization Balaban.Localization.LevelPair Balaban.Localization.I5Inhabited
  Balaban.Polymer Balaban.SmallField.Def6 Balaban.Analysis Balaban.Inhabited.LevelStep
  LocalCover Filter Topology

/-- The fixed tower of a general tower at `3, 3, 2` with `κ₀ = a_Ent + 2` and `m₀ = 1`; all
scalar fields are those of the general tower. -/
noncomputable def StepTowerG.ofThree {κmin : ℝ} (T : StepTowerG 3 3 2 κmin)
    (h0 : T.κ0 = aEnt 3 3 + 2) (hm : T.m₀ = 1) : StepTower κmin :=
  have hcore : Nonempty (FlCore 2 (Gp T.m₁ (rhoSep T.m₁)) (Hm T.m₁ (rhoSep T.m₁))
      1 nuW T.c T.BG T.κ T.t (levelKc 3 3) (Cchi 3 3) T.c₂ T.BG₂ T.t) := by
    have h := T.core
    rw [νref_three] at h
    have e := rhoSepG_three (m₁ := T.m₁)
    have key : ∀ ϱ : ℝ, ϱ = rhoSepG 3 3 T.m₁ →
        Nonempty (FlCore 2 (Gp T.m₁ ϱ) (Hm T.m₁ ϱ) 1 nuW T.c T.BG T.κ T.t
          (levelKc 3 3) (Cchi 3 3) T.c₂ T.BG₂ T.t) := by
      intro ϱ hϱ; subst hϱ; exact h
    exact key _ e.symm
  have hlog := T.κ_log
  have hdr := T.det_rate
  { κ0 := T.κ0, κdec := T.κdec, κ' := T.κ', κ0_eq := h0, κdec_eq := T.κdec_eq
    κ'_eq := T.κ'_eq, m₁ := T.m₁, c := T.c, BG := T.BG, κ := T.κ, t := T.t, c₂ := T.c₂
    BG₂ := T.BG₂, δc := T.δc, δ := T.δ, δ' := T.δ'
    m₁_four := T.m₁_four, t_pos := T.t_pos, core := hcore, κ0_nonneg := T.κ0_nonneg
    κdec_lower := T.κdec_lower, κ_lower := T.κ_lower, κ_one := T.κ_one
    κ_log := by rw [hm] at hlog; simpa using hlog, c7_cap := T.c7_cap, large_block := T.large_block
    dom_margin := T.dom_margin, coer_margin := T.coer_margin, δc_small := T.δc_small
    t_cap := T.t_cap, bg0_cap := T.bg0_cap, cK2_cap := T.cK2_cap, cK2'_cap := T.cK2'_cap
    bg1_cap := T.bg1_cap, κ0_ent := T.κ0_ent, rate_rel := T.rate_rel
    fam_nonneg := T.fam_nonneg, κmin_le := T.κmin_le, δ_pos := T.δ_pos
    δ_small := T.δ_small, δ'_pos := T.δ'_pos, δ'_cap := T.δ'_cap, δ'_step := T.δ'_step
    δ'_coer := T.δ'_coer, block_base := T.block_base, xi_small := T.xi_small
    rho_nonneg := T.rho_nonneg, det_z := T.det_z, det_rate := by
      have e : (2 * ((3 : ℕ) : ℝ) * ((3 : ℕ) : ℝ)) = 18 := by norm_num
      rw [e] at hdr; exact hdr }

/-- A general tower at `3, 3, 2` with `κ₀ = a_Ent + 2` and `m₀ = 1` gives a fixed tower. -/
theorem StepTowerG.nonempty_fixed_of_three {κmin : ℝ} (T : StepTowerG 3 3 2 κmin)
    (h0 : T.κ0 = aEnt 3 3 + 2) (hm : T.m₀ = 1) : Nonempty (StepTower κmin) :=
  ⟨T.ofThree h0 hm⟩

/-- **The tower record is inhabited** for every lower bound `κmin`. -/
theorem exists_stepTower (κmin : ℝ) : Nonempty (StepTower κmin) := by
  obtain ⟨T, hm, -, h0⟩ := exists_stepTowerRenG 3 3 2 le_rfl le_rfl le_rfl 1 le_rfl 0 0 κmin
  have := aEnt_nonneg 3 3
  exact StepTowerG.nonempty_fixed_of_three T.toStepTowerG (h0 (by simp; linarith)) hm

/-- **The general tower record is inhabited** at `d = L = 3`, `N = 2` for every `κmin`. -/
theorem exists_stepTowerG_three (κmin : ℝ) : Nonempty (StepTowerG 3 3 2 κmin) :=
  (exists_stepTower κmin).map StepTower.toG

/-- A general tower with margins at `3, 3, 2` with `κ₀ = a_Ent + 2` and `m₀ = 1` gives a fixed
tower with margins. -/
theorem StepTowerRenG.nonempty_fixed_of_three {κmin : ℝ} (T : StepTowerRenG 3 3 2 κmin)
    (h0 : T.κ0 = aEnt 3 3 + 2) (hm : T.m₀ = 1) : Nonempty (StepTowerRen κmin) := by
  exact ⟨StepTowerRen.mk (T.toStepTowerG.ofThree h0 hm) T.ren_margin T.r₀ T.r₀_pos T.r₀_le T.D₀_le_one T.D₀_le_star
    T.D₁_le_star⟩

/-- **The record with margins is inhabited** for every lower bound `κmin`. -/
theorem exists_stepTowerRen (κmin : ℝ) : Nonempty (StepTowerRen κmin) := by
  obtain ⟨T, hm, -, h0⟩ := exists_stepTowerRenG 3 3 2 le_rfl le_rfl le_rfl 1 le_rfl 0 0 κmin
  have := aEnt_nonneg 3 3
  exact StepTowerRenG.nonempty_fixed_of_three T (h0 (by simp; linarith)) hm

end Balaban.Inhabited
