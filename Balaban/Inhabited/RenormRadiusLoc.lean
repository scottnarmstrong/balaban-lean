/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.RenormRadiusDec
public import Balaban.Inhabited.RenormExpInputTower
public import Balaban.Fluctuation.RenormSharedClass

/-!
# The three localization principles at the tower for a class radius `e ≤ t`

For `0 < e ≤ t`, at the step `lvTop` of every scale `k ≥ 1` of the tower, every torus with
`3 ∣ N₁`, `5 < N₁`, every mass `0 ≤ ν` with `ν · 3^{2(k+1)} ≤ 1`:

* `renLocC1_scale_of_tower_of_le_at`: `locC1` on the class `XiCOneReal … ν e`, for the density
  `renC1On … ν e` (lifted datum `renZeta e ξ · Ψ`), with the class `bgClass … (c_K' e)`;
* `renLocDphi_scale_of_tower_at`, `renLocC2_scale_of_tower_at`: `locDφ` and `locC2` for a solution
  map of `IsRenSol … ν e e r_F (8 e)`, `r_F ≥ r₀`, with the class widths at `B = 8 e`;
* `renLoc_fields_scale_of_tower_at`: ONE solution map `F` of `IsRenSol … ν e e r₀ (8 e)` and the
  three principles for it, in the exact shape of the landed `renLoc_fields_scale_of_tower` with
  `t` replaced by `e`.

The polydisc radius `r₀`, the rates (`κa, κb ≤ 2 κdec`, the cut radius `exp κ` inside the proofs),
the cover (`m₀ = 1`) and the constants `renCK`, `K₁`, `K₂` are those of the tower.  No occurrence
of `t` is left in these statements.  After each theorem, an `example` checks that the landed
statement is the case `e = t`.
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation
  Balaban.Localization Balaban.Localization.LevelPair Balaban.Localization.I5Inhabited
  Balaban.Polymer Balaban.SmallField.Def6 Balaban.Analysis Balaban.Inhabited.LevelStep LocalCover

/-- **The `FlCore` of the record `StepTower` at a scale, at radii `e, e' ≤ t`.**  (For the record
`StepTowerRen` this is `StepTowerRen.flCore_scale_mono`.) -/
theorem StepTower.flCore_scale_of_le {κmin : ℝ} (T : StepTower κmin) (k : ℕ) (hk : 1 ≤ k)
    (N₁ : ℕ) [NeZero N₁] (hN : 5 < N₁) {ν : ℝ} (hν0 : 0 ≤ ν)
    (hν : ν * 3 ^ (2 * (k + 1)) ≤ 1) {e e' : ℝ} (he : 0 < e) (het : e ≤ T.t) (he' : 0 < e')
    (he't : e' ≤ T.t) :
    FlCore 2 (lvTop N₁ T.m₁ k (rhoSep T.m₁)) (lvLow N₁ T.m₁ k (rhoSep T.m₁)) 1 ν T.c
      T.BG T.κ e (levelKc 3 3) (Cchi 3 3) T.c₂ T.BG₂ e' := by
  obtain ⟨hC₀⟩ := T.core
  have hSD := dgSetting_lv (N₁ := N₁) (k := k) T.m₁_four hN hν0 hν
  have hHB := bgHyp_lv (k := k) T.m₁ hν0 hν
  exact (flCore_level_transfer hC₀ hSD (opSetting_lv T.m₁_four hN hν0 hν) (isLevel_lvLow hk)
    isLevel_lvTop hHB).mono he het he' he't

/-- **`locC1` at every scale of the tower, at the class radius `e ≤ t`**, at any class constant
`cK' ≥ 2 + 2 K₄ ξ₁`. -/
theorem renLocC1_scale_of_tower_of_le_at {κmin : ℝ} (T : StepTower κmin) (k : ℕ) (hk : 1 ≤ k)
    (N₁ : ℕ) [NeZero N₁] (h3N : 3 ∣ N₁) (hN : 5 < N₁) {ν : ℝ} (hν0 : 0 ≤ ν)
    (hν : ν * 3 ^ (2 * (k + 1)) ≤ 1) {e : ℝ} (he : 0 < e) (het : e ≤ T.t)
    {κa r₀ : ℝ} (hκa : κa ≤ 2 * T.κdec)
    (hr₀0 : 0 < r₀) (hr₀1 : r₀ ≤ 1 / 16) (z : Torus 3 (N₁ * 3 ^ T.m₁ * 3 ^ (k + 1 - (k + 1))))
    {cK' : ℝ} (hcK : 2 + 2 * K4 3 3 2 T.BG T.κ * xiC1 3 ≤ cK') :
    HasLocPrinciple (N := 2) (lvTop N₁ T.m₁ k (rhoSep T.m₁))
      (XiCOneReal (lvTop N₁ T.m₁ k (rhoSep T.m₁)) (compWeight 3 1) ν e) r₀
      (renYs (renCube (lvTop N₁ T.m₁ k (rhoSep T.m₁))
          (X1 (lvTop N₁ T.m₁ k (rhoSep T.m₁)) 1 k (fam 1 (blockSite k z))))
        (lvTop N₁ T.m₁ k (rhoSep T.m₁)) 1
        (X1 (lvTop N₁ T.m₁ k (rhoSep T.m₁)) 1 k (fam 1 (blockSite k z))))
      (renDY (lvTop N₁ T.m₁ k (rhoSep T.m₁)) 1) κa 1
      (fun D _ => bgClass (lvTop N₁ T.m₁ k (rhoSep T.m₁)) ν (cK' * e) D)
      (fun D φ ξ => renC1On (lvTop N₁ T.m₁ k (rhoSep T.m₁)) (compWeight 3 1) ν e
        (blockSites 3 3 N₁ T.m₁ (k + 1) k z) D.Ψ D.h φ ξ)
      (fun D _ => bgFieldC (lvTop N₁ T.m₁ k (rhoSep T.m₁)) (compWeight 3 1) ν (bgC0 3 3 2) D) := by
  have hN3 : 3 ^ 1 ∣ N₁ := by simpa using h3N
  exact renLocC1_zero_of_le (T.flCore_scale_of_le k hk N₁ hN hν0 hν he het he het) hatConn_lvTop
    isLevel_lvTop le_rfl hN3 (by norm_num) (by norm_num) T.κ0_nonneg T.κdec_lower T.κ_lower
    T.κ_one T.κ_log hκa hr₀0 hr₀1 z hcK

/-- The landed `renLocC1_scale_of_tower_of_le` is the case `e = t`. -/
example {κmin : ℝ} (T : StepTower κmin) (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁]
    (h3N : 3 ∣ N₁) (hN : 5 < N₁) {ν : ℝ} (hν0 : 0 ≤ ν) (hν : ν * 3 ^ (2 * (k + 1)) ≤ 1)
    {κa r₀ : ℝ} (hκa : κa ≤ 2 * T.κdec) (hr₀0 : 0 < r₀) (hr₀1 : r₀ ≤ 1 / 16)
    (z : Torus 3 (N₁ * 3 ^ T.m₁ * 3 ^ (k + 1 - (k + 1)))) {cK' : ℝ}
    (hcK : 2 + 2 * K4 3 3 2 T.BG T.κ * xiC1 3 ≤ cK') :
    type_of% (renLocC1_scale_of_tower_of_le T k hk N₁ h3N hN hν0 hν hκa hr₀0 hr₀1 z hcK) :=
  renLocC1_scale_of_tower_of_le_at T k hk N₁ h3N hN hν0 hν T.t_pos le_rfl hκa hr₀0 hr₀1 z hcK

/-- **`locDφ` at a site root of every scale of the tower, at the class radius `e ≤ t`.** -/
theorem renLocDphi_scale_of_tower_at {κmin : ℝ} (R : StepTowerRenEnd κmin) (k : ℕ) (hk : 1 ≤ k)
    (N₁ : ℕ) [NeZero N₁] (h3N : 3 ∣ N₁) (hN : 5 < N₁) {ν : ℝ} (hν0 : 0 ≤ ν)
    (hν : ν * 3 ^ (2 * (k + 1)) ≤ 1) {e : ℝ} (he : 0 < e) (het : e ≤ R.t)
    {κb rF : ℝ} (hκb : κb ≤ 2 * R.κdec)
    {F : RawData 3 3 (N₁ * 3 ^ R.m₁) (k + 1) 2 × (Fin 3 → ℂ) →
      ((lvTop N₁ R.m₁ k (rhoSep R.m₁)).Ω 1 × Fin 2 → ℂ) ×
        ((lvTop N₁ R.m₁ k (rhoSep R.m₁)).Ω 1 → ℂ)}
    (hF : IsRenSol (N := 2) (lvTop N₁ R.m₁ k (rhoSep R.m₁)) (compWeight 3 1) ν e e rF
      (8 * e) F) (hrF : R.r₀ ≤ rF)
    (p : (lvTop N₁ R.m₁ k (rhoSep R.m₁)).Ω 1 × Fin 2) :
    HasLocPrinciple (N := 2) (lvTop N₁ R.m₁ k (rhoSep R.m₁))
      (XiCOneReal (lvTop N₁ R.m₁ k (rhoSep R.m₁)) (compWeight 3 1) ν e) R.r₀
      (renYs (renCube (lvTop N₁ R.m₁ k (rhoSep R.m₁))
          (X1 (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 1 k (fam 1 (p.1 : CTorus 3 3 N₁ R.m₁ (k + 1)))))
        (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 1
        (X1 (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 1 k (fam 1 (p.1 : CTorus 3 3 N₁ R.m₁ (k + 1)))))
      (renDY (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 1) κb 1
      (fun _ ξ => {v | SupBounds (lvTop N₁ R.m₁ k (rhoSep R.m₁)) v
        (renCK 3 3 2 R.BG R.κ * (cK2 3 3 2 * (8 * e * ‖ξ‖)))})
      (fun _ v _ => v p) (fun D ξ => (F ((D.Ψ, D.h), ξ)).1) := by
  have hC := R.flCore_scale_mono k hk N₁ hN hν0 hν he het he het
  have hN3 : 3 ^ 1 ∣ N₁ := by simpa using h3N
  obtain ⟨hcK, hCB⟩ := R.toStepTowerRen.renCK_facts_at he.le
  obtain ⟨-, h1, h2, h3⟩ := R.toStepTowerRen.ren_margins_of_le het
  exact renLocDphi_zero_at hC hatConn_lvTop isLevel_lvTop le_rfl hN3 (by norm_num) (by norm_num)
    R.κ0_nonneg R.κdec_lower R.κ_lower R.κ_one R.κ_log hκb R.r₀_pos R.r₀_le hF hrF h1 h2 h3
    (R.end_margin_of_le het) (by positivity) hcK hCB p

/-- The landed `renLocDphi_scale_of_tower` is the case `e = t`. -/
example {κmin : ℝ} (R : StepTowerRenEnd κmin) (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁]
    (h3N : 3 ∣ N₁) (hN : 5 < N₁) {ν : ℝ} (hν0 : 0 ≤ ν) (hν : ν * 3 ^ (2 * (k + 1)) ≤ 1)
    {κb rF : ℝ} (hκb : κb ≤ 2 * R.κdec)
    {F : RawData 3 3 (N₁ * 3 ^ R.m₁) (k + 1) 2 × (Fin 3 → ℂ) →
      ((lvTop N₁ R.m₁ k (rhoSep R.m₁)).Ω 1 × Fin 2 → ℂ) ×
        ((lvTop N₁ R.m₁ k (rhoSep R.m₁)).Ω 1 → ℂ)}
    (hF : IsRenSol (N := 2) (lvTop N₁ R.m₁ k (rhoSep R.m₁)) (compWeight 3 1) ν R.t R.t rF
      (8 * R.t) F) (hrF : R.r₀ ≤ rF)
    (p : (lvTop N₁ R.m₁ k (rhoSep R.m₁)).Ω 1 × Fin 2) :
    type_of% (renLocDphi_scale_of_tower R k hk N₁ h3N hN hν0 hν hκb hF hrF p) :=
  renLocDphi_scale_of_tower_at R k hk N₁ h3N hN hν0 hν R.t_pos le_rfl hκb hF hrF p

/-- **`locC2` at a block root of every scale of the tower, at the class radius `e ≤ t`.** -/
theorem renLocC2_scale_of_tower_at {κmin : ℝ} (R : StepTowerRenEnd κmin) (k : ℕ) (hk : 1 ≤ k)
    (N₁ : ℕ) [NeZero N₁] (h3N : 3 ∣ N₁) (hN : 5 < N₁) {ν : ℝ} (hν0 : 0 ≤ ν)
    (hν : ν * 3 ^ (2 * (k + 1)) ≤ 1) {e : ℝ} (he : 0 < e) (het : e ≤ R.t)
    {κa rF : ℝ} (hκa : κa ≤ 2 * R.κdec)
    {F : RawData 3 3 (N₁ * 3 ^ R.m₁) (k + 1) 2 × (Fin 3 → ℂ) →
      ((lvTop N₁ R.m₁ k (rhoSep R.m₁)).Ω 1 × Fin 2 → ℂ) ×
        ((lvTop N₁ R.m₁ k (rhoSep R.m₁)).Ω 1 → ℂ)}
    (hF : IsRenSol (N := 2) (lvTop N₁ R.m₁ k (rhoSep R.m₁)) (compWeight 3 1) ν e e rF
      (8 * e) F) (hrF : R.r₀ ≤ rF)
    (z : Torus 3 (N₁ * 3 ^ R.m₁ * 3 ^ (k + 1 - (k + 1)))) :
    HasLocPrinciple (N := 2) (lvTop N₁ R.m₁ k (rhoSep R.m₁))
      (XiCOneReal (lvTop N₁ R.m₁ k (rhoSep R.m₁)) (compWeight 3 1) ν e) R.r₀
      (renYs (renCube (lvTop N₁ R.m₁ k (rhoSep R.m₁))
          (X1 (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 1 k (fam 1 (blockSite k z))))
        (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 1
        (X1 (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 1 k (fam 1 (blockSite k z))))
      (renDY (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 1) κa 1
      (fun _ ξ => pertClass (lvTop N₁ R.m₁ k (rhoSep R.m₁))
        (renCK 3 3 2 R.BG R.κ * (cK2 3 3 2 * (8 * e * ‖ξ‖)))
        (bgK1 3 3 2 * (xiC1 3 * e) + renCK 3 3 2 R.BG R.κ * cK2 3 3 2 * (8 * e) * R.r₀ + 2)
        (renMassU ν ξ))
      (fun _ v ξ => renC2On (lvTop N₁ R.m₁ k (rhoSep R.m₁)) (compWeight 3 1)
        (blockSites 3 3 N₁ R.m₁ (k + 1) k z) ξ (renMassU ν ξ) v.2 v.1)
      (fun D ξ => ((F ((D.Ψ, D.h), ξ)).1,
        bgMultC (lvTop N₁ R.m₁ k (rhoSep R.m₁)) (compWeight 3 1) ν (bgC0 3 3 2) D +
          (F ((D.Ψ, D.h), ξ)).2)) := by
  have hC := R.flCore_scale_mono k hk N₁ hN hν0 hν he het he het
  have hN3 : 3 ^ 1 ∣ N₁ := by simpa using h3N
  obtain ⟨hcK, hCB⟩ := R.toStepTowerRen.renCK_facts_at he.le
  obtain ⟨-, h1, h2, h3⟩ := R.toStepTowerRen.ren_margins_of_le het
  exact renLocC2_zero_at hC hatConn_lvTop isLevel_lvTop le_rfl hN3 (by norm_num) (by norm_num)
    R.κ0_nonneg R.κdec_lower R.κ_lower R.κ_one R.κ_log hκa R.r₀_pos R.r₀_le hF hrF h1 h2 h3
    (R.end_margin_of_le het) (by positivity) hcK hCB z

/-- The landed `renLocC2_scale_of_tower` is the case `e = t`. -/
example {κmin : ℝ} (R : StepTowerRenEnd κmin) (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁]
    (h3N : 3 ∣ N₁) (hN : 5 < N₁) {ν : ℝ} (hν0 : 0 ≤ ν) (hν : ν * 3 ^ (2 * (k + 1)) ≤ 1)
    {κa rF : ℝ} (hκa : κa ≤ 2 * R.κdec)
    {F : RawData 3 3 (N₁ * 3 ^ R.m₁) (k + 1) 2 × (Fin 3 → ℂ) →
      ((lvTop N₁ R.m₁ k (rhoSep R.m₁)).Ω 1 × Fin 2 → ℂ) ×
        ((lvTop N₁ R.m₁ k (rhoSep R.m₁)).Ω 1 → ℂ)}
    (hF : IsRenSol (N := 2) (lvTop N₁ R.m₁ k (rhoSep R.m₁)) (compWeight 3 1) ν R.t R.t rF
      (8 * R.t) F) (hrF : R.r₀ ≤ rF)
    (z : Torus 3 (N₁ * 3 ^ R.m₁ * 3 ^ (k + 1 - (k + 1)))) :
    type_of% (renLocC2_scale_of_tower R k hk N₁ h3N hN hν0 hν hκa hF hrF z) :=
  renLocC2_scale_of_tower_at R k hk N₁ h3N hN hν0 hν R.t_pos le_rfl hκa hF hrF z

/-- **The three localization fields and the solution at every scale of the tower, at the class
radius `e ≤ t`**: one solution map `F` of `IsRenSol … ν e e r₀ (8 e)` and the three principles for
it, in the exact types of the fields `locC1`, `locC2`, `locDφ` of
`RenormExpInput … ν e r₀ renCK (8 e) F …`. -/
theorem renLoc_fields_scale_of_tower_at {κmin : ℝ} (R : StepTowerRenSol κmin) (k : ℕ)
    (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁] (h3N : 3 ∣ N₁) (hN : 5 < N₁) {ν : ℝ} (hν0 : 0 ≤ ν)
    (hν : ν * 3 ^ (2 * (k + 1)) ≤ 1) {e : ℝ} (he : 0 < e) (het : e ≤ R.t)
    {κa κb : ℝ} (hκa : κa ≤ 2 * R.κdec) (hκb : κb ≤ 2 * R.κdec) :
    ∃ F : RawData 3 3 (N₁ * 3 ^ R.m₁) (k + 1) 2 × (Fin 3 → ℂ) →
        ((lvTop N₁ R.m₁ k (rhoSep R.m₁)).Ω 1 × Fin 2 → ℂ) ×
          ((lvTop N₁ R.m₁ k (rhoSep R.m₁)).Ω 1 → ℂ),
      IsRenSol (N := 2) (lvTop N₁ R.m₁ k (rhoSep R.m₁)) (compWeight 3 1) ν e e R.r₀
        (8 * e) F ∧
      (∀ z : Torus 3 (N₁ * 3 ^ R.m₁ * 3 ^ (k + 1 - (k + 1))),
        HasLocPrinciple (N := 2) (lvTop N₁ R.m₁ k (rhoSep R.m₁))
          (XiCOneReal (lvTop N₁ R.m₁ k (rhoSep R.m₁)) (compWeight 3 1) ν e) R.r₀
          (renYs (renCube (lvTop N₁ R.m₁ k (rhoSep R.m₁))
              (X1 (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 1 k (fam 1 (blockSite k z))))
            (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 1
            (X1 (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 1 k (fam 1 (blockSite k z))))
          (renDY (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 1) κa 1
          (fun D _ => bgClass (lvTop N₁ R.m₁ k (rhoSep R.m₁)) ν
            (renCK 3 3 2 R.BG R.κ * e) D)
          (fun D φ ξ => renC1On (lvTop N₁ R.m₁ k (rhoSep R.m₁)) (compWeight 3 1) ν e
            (blockSites 3 3 N₁ R.m₁ (k + 1) k z) D.Ψ D.h φ ξ)
          (fun D _ => bgFieldC (lvTop N₁ R.m₁ k (rhoSep R.m₁)) (compWeight 3 1) ν
            (bgC0 3 3 2) D)) ∧
      (∀ z : Torus 3 (N₁ * 3 ^ R.m₁ * 3 ^ (k + 1 - (k + 1))),
        HasLocPrinciple (N := 2) (lvTop N₁ R.m₁ k (rhoSep R.m₁))
          (XiCOneReal (lvTop N₁ R.m₁ k (rhoSep R.m₁)) (compWeight 3 1) ν e) R.r₀
          (renYs (renCube (lvTop N₁ R.m₁ k (rhoSep R.m₁))
              (X1 (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 1 k (fam 1 (blockSite k z))))
            (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 1
            (X1 (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 1 k (fam 1 (blockSite k z))))
          (renDY (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 1) κa 1
          (fun _ ξ => pertClass (lvTop N₁ R.m₁ k (rhoSep R.m₁))
            (renCK 3 3 2 R.BG R.κ * (cK2 3 3 2 * (8 * e * ‖ξ‖)))
            (bgK1 3 3 2 * (xiC1 3 * e) + renCK 3 3 2 R.BG R.κ * cK2 3 3 2 * (8 * e) * R.r₀
              + 2) (renMassU ν ξ))
          (fun _ v ξ => renC2On (lvTop N₁ R.m₁ k (rhoSep R.m₁)) (compWeight 3 1)
            (blockSites 3 3 N₁ R.m₁ (k + 1) k z) ξ (renMassU ν ξ) v.2 v.1)
          (fun D ξ => ((F ((D.Ψ, D.h), ξ)).1,
            bgMultC (lvTop N₁ R.m₁ k (rhoSep R.m₁)) (compWeight 3 1) ν (bgC0 3 3 2) D +
              (F ((D.Ψ, D.h), ξ)).2))) ∧
      (∀ p : (lvTop N₁ R.m₁ k (rhoSep R.m₁)).Ω 1 × Fin 2,
        HasLocPrinciple (N := 2) (lvTop N₁ R.m₁ k (rhoSep R.m₁))
          (XiCOneReal (lvTop N₁ R.m₁ k (rhoSep R.m₁)) (compWeight 3 1) ν e) R.r₀
          (renYs (renCube (lvTop N₁ R.m₁ k (rhoSep R.m₁))
              (X1 (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 1 k
                (fam 1 (p.1 : CTorus 3 3 N₁ R.m₁ (k + 1)))))
            (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 1
            (X1 (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 1 k
              (fam 1 (p.1 : CTorus 3 3 N₁ R.m₁ (k + 1)))))
          (renDY (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 1) κb 1
          (fun _ ξ => {v | SupBounds (lvTop N₁ R.m₁ k (rhoSep R.m₁)) v
            (renCK 3 3 2 R.BG R.κ * (cK2 3 3 2 * (8 * e * ‖ξ‖)))})
          (fun _ v _ => v p) (fun D ξ => (F ((D.Ψ, D.h), ξ)).1)) := by
  obtain ⟨F, hF⟩ := exists_isRenSol_scale_of_tower_at R k hk N₁ hN hν0 hν he het
  refine ⟨F, hF, fun z => ?_, fun z => ?_, fun p => ?_⟩
  · exact renLocC1_scale_of_tower_of_le_at R.toStepTower k hk N₁ h3N hN hν0 hν he het hκa
      R.r₀_pos R.r₀_le z (renCK_ge (d := 3) (L := 3) (N := 2) (BG := R.BG) (κ := R.κ))
  · exact renLocC2_scale_of_tower_at R.toStepTowerRenEnd k hk N₁ h3N hN hν0 hν he het hκa hF
      le_rfl z
  · exact renLocDphi_scale_of_tower_at R.toStepTowerRenEnd k hk N₁ h3N hN hν0 hν he het hκb hF
      le_rfl p

/-- The landed `renLoc_fields_scale_of_tower` is the case `e = t`. -/
example {κmin : ℝ} (R : StepTowerRenSol κmin) (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁]
    (h3N : 3 ∣ N₁) (hN : 5 < N₁) {ν : ℝ} (hν0 : 0 ≤ ν) (hν : ν * 3 ^ (2 * (k + 1)) ≤ 1)
    {κa κb : ℝ} (hκa : κa ≤ 2 * R.κdec) (hκb : κb ≤ 2 * R.κdec) :
    type_of% (renLoc_fields_scale_of_tower R k hk N₁ h3N hN hν0 hν hκa hκb) :=
  renLoc_fields_scale_of_tower_at R k hk N₁ h3N hN hν0 hν R.t_pos le_rfl hκa hκb

end Balaban.Inhabited
