/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.StepTower
public import Balaban.Inhabited.StepTowerG

/-!
# The bridge from the fixed tower to the general tower

`StepTower.toG` maps the fixed `d = L = 3`, `N = 2` tower to `StepTowerG 3 3 2`.  The scalar
fields are preserved; the core is transported along `rhoSepG 3 3 m₁ = rhoSep m₁` and
`νref 3 = nuW`.
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation
  Balaban.Localization Balaban.Localization.LevelPair Balaban.Localization.I5Inhabited
  Balaban.Polymer Balaban.SmallField.Def6 LevelStep

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

/-- **The bridge**: the fixed `3, 3, 2` tower is a general tower. -/
noncomputable def StepTower.toG {κmin : ℝ} (T : StepTower κmin) : StepTowerG 3 3 2 κmin where
  hd := le_rfl
  hL := le_rfl
  hN := le_rfl
  κ0 := T.κ0
  κdec := T.κdec
  κ' := T.κ'
  κ0_ge := T.κ0_two
  κdec_eq := T.κdec_eq
  κ'_eq := T.κ'_eq
  m₁ := T.m₁
  m₀ := 1
  m₀_pos := le_rfl
  c := T.c
  BG := T.BG
  κ := T.κ
  t := T.t
  c₂ := T.c₂
  BG₂ := T.BG₂
  δc := T.δc
  δ := T.δ
  δ' := T.δ'
  m₁_four := T.m₁_four
  t_pos := T.t_pos
  core := flCore_three_transport T.core
  κ0_nonneg := T.κ0_nonneg
  κdec_lower := T.κdec_lower
  κ_lower := T.κ_lower
  κ_one := T.κ_one
  κ_log := by simpa using T.κ_log
  c7_cap := T.c7_cap
  large_block := T.large_block
  dom_margin := T.dom_margin
  coer_margin := T.coer_margin
  δc_small := T.δc_small
  t_cap := T.t_cap
  bg0_cap := T.bg0_cap
  cK2_cap := T.cK2_cap
  cK2'_cap := T.cK2'_cap
  bg1_cap := T.bg1_cap
  κ0_ent := T.κ0_ent
  rate_rel := T.rate_rel
  fam_nonneg := T.fam_nonneg
  κmin_le := T.κmin_le
  δ_pos := T.δ_pos
  δ_small := T.δ_small
  δ'_pos := T.δ'_pos
  δ'_cap := T.δ'_cap
  δ'_step := T.δ'_step
  δ'_coer := T.δ'_coer
  block_base := T.block_base
  xi_small := T.xi_small
  rho_nonneg := T.rho_nonneg
  det_z := T.det_z
  det_rate := by
    have e : (2 * ((3 : ℕ) : ℝ) * ((3 : ℕ) : ℝ)) = 18 := by norm_num
    rw [e]; exact T.det_rate

namespace StepTower

variable {κmin : ℝ} (T : StepTower κmin)

@[simp] theorem toG_κ0 : T.toG.κ0 = T.κ0 := rfl
@[simp] theorem toG_κdec : T.toG.κdec = T.κdec := rfl
@[simp] theorem toG_κ' : T.toG.κ' = T.κ' := rfl
@[simp] theorem toG_κ : T.toG.κ = T.κ := rfl
@[simp] theorem toG_m₁ : T.toG.m₁ = T.m₁ := rfl
@[simp] theorem toG_m₀ : T.toG.m₀ = 1 := rfl
@[simp] theorem toG_t : T.toG.t = T.t := rfl
@[simp] theorem toG_c : T.toG.c = T.c := rfl
@[simp] theorem toG_BG : T.toG.BG = T.BG := rfl
@[simp] theorem toG_c₂ : T.toG.c₂ = T.c₂ := rfl
@[simp] theorem toG_BG₂ : T.toG.BG₂ = T.BG₂ := rfl
@[simp] theorem toG_δc : T.toG.δc = T.δc := rfl
@[simp] theorem toG_δ : T.toG.δ = T.δ := rfl
@[simp] theorem toG_δ' : T.toG.δ' = T.δ' := rfl

end StepTower

/-- **The general tower record is inhabited** at `d = L = 3`, `N = 2` for every `κmin`. -/
theorem exists_stepTowerG_three (κmin : ℝ) : Nonempty (StepTowerG 3 3 2 κmin) :=
  (exists_stepTower κmin).map StepTower.toG

end Balaban.Inhabited
