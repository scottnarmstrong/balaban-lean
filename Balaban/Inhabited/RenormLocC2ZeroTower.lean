/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.StepTowerRenEnd
public import Balaban.Fluctuation.RenormLocC2Zero

/-!
# `locC2` and `locDφ` at every scale of the shared tower

For `R : StepTowerRenEnd κmin`, at the step `lvTop` of every scale `k ≥ 1`, every torus with
`3 ∣ N₁`, `5 < N₁`, every mass `0 ≤ ν` with `ν · 3^{2(k+1)} ≤ 1`, every solution map `F` of
`IsRenSol` with radius `r_F ≥ r₀`: the principle `locC2` at a block root and the principle `locDφ`
at a site root of the record `RenormExpInput`, at the shared constants `c_K = renCK`, `B = 8 t`,
`ε = t`, `r₀`, `K_loc = 1`, and the same cover (`m₀ = 1`).
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation
  Balaban.Localization Balaban.Localization.LevelPair Balaban.Localization.I5Inhabited
  Balaban.Polymer Balaban.SmallField.Def6 Balaban.Analysis Balaban.Inhabited.LevelStep LocalCover

/-- The two constant inequalities at the shared class constant: `1 ≤ renCK` and (CB) with
`B = 8 t`. -/
theorem StepTowerRen.renCK_facts {κmin : ℝ} (R : StepTowerRen κmin) :
    1 ≤ renCK 3 3 2 R.BG R.κ ∧
    cK2' 3 3 2 (famConst 3 3 R.BG R.κ) *
      ((3 / 2 + 32 / 15 * (3 + (K4 3 3 2 R.BG R.κ + bgK1 3 3 2) * xiC1 3)) * R.t) ≤
      renCK 3 3 2 R.BG R.κ * cK2 3 3 2 * (8 * R.t) := by
  obtain ⟨hC₀⟩ := R.core
  have hK4 := K4_pos (L := 3) (N := 2) (κ := R.κ) hC₀.hS.fam.2.1 (by norm_num : 0 < 3)
  have hX : 0 ≤ xiC1 3 := by unfold xiC1; positivity
  refine ⟨?_, ?_⟩
  · have := renCK_ge (d := 3) (L := 3) (N := 2) (BG := R.BG) (κ := R.κ)
    have := mul_nonneg hK4.le hX
    linarith
  · have h := renCK_mul_ge (d := 3) (L := 3) (N := 2) (BG := R.BG) (κ := R.κ)
    have := mul_le_mul_of_nonneg_right h R.t_pos.le
    nlinarith

/-- **`locDφ` at a site root of every scale of the tower.** -/
theorem renLocDphi_scale_of_tower {κmin : ℝ} (R : StepTowerRenEnd κmin) (k : ℕ) (hk : 1 ≤ k)
    (N₁ : ℕ) [NeZero N₁] (h3N : 3 ∣ N₁) (hN : 5 < N₁) {ν : ℝ} (hν0 : 0 ≤ ν)
    (hν : ν * 3 ^ (2 * (k + 1)) ≤ 1) {κb rF : ℝ} (hκb : κb ≤ 2 * R.κdec)
    {F : RawData 3 3 (N₁ * 3 ^ R.m₁) (k + 1) 2 × (Fin 3 → ℂ) →
      ((lvTop N₁ R.m₁ k (rhoSep R.m₁)).Ω 1 × Fin 2 → ℂ) ×
        ((lvTop N₁ R.m₁ k (rhoSep R.m₁)).Ω 1 → ℂ)}
    (hF : IsRenSol (N := 2) (lvTop N₁ R.m₁ k (rhoSep R.m₁)) (compWeight 3 1) ν R.t R.t rF
      (8 * R.t) F) (hrF : R.r₀ ≤ rF)
    (p : (lvTop N₁ R.m₁ k (rhoSep R.m₁)).Ω 1 × Fin 2) :
    HasLocPrinciple (N := 2) (lvTop N₁ R.m₁ k (rhoSep R.m₁))
      (XiCOneReal (lvTop N₁ R.m₁ k (rhoSep R.m₁)) (compWeight 3 1) ν R.t) R.r₀
      (renYs (renCube (lvTop N₁ R.m₁ k (rhoSep R.m₁))
          (X1 (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 1 k (fam 1 (p.1 : CTorus 3 3 N₁ R.m₁ (k + 1)))))
        (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 1
        (X1 (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 1 k (fam 1 (p.1 : CTorus 3 3 N₁ R.m₁ (k + 1)))))
      (renDY (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 1) κb 1
      (fun _ ξ => {v | SupBounds (lvTop N₁ R.m₁ k (rhoSep R.m₁)) v
        (renCK 3 3 2 R.BG R.κ * (cK2 3 3 2 * (8 * R.t * ‖ξ‖)))})
      (fun _ v _ => v p) (fun D ξ => (F ((D.Ψ, D.h), ξ)).1) := by
  have hC := R.flCore_scale k hk N₁ hN hν0 hν
  have hN3 : 3 ^ 1 ∣ N₁ := by simpa using h3N
  obtain ⟨hcK, hCB⟩ := R.toStepTowerRen.renCK_facts
  exact renLocDphi_zero_at hC hatConn_lvTop isLevel_lvTop le_rfl hN3 (by norm_num) (by norm_num)
    R.κ0_nonneg R.κdec_lower R.κ_lower R.κ_one R.κ_log hκb R.r₀_pos R.r₀_le hF hrF R.D₀_le_one
    R.D₀_le_star R.D₁_le_star R.end_margin (by have := R.t_pos; positivity) hcK hCB p

/-- **`locC2` at a block root of every scale of the tower.** -/
theorem renLocC2_scale_of_tower {κmin : ℝ} (R : StepTowerRenEnd κmin) (k : ℕ) (hk : 1 ≤ k)
    (N₁ : ℕ) [NeZero N₁] (h3N : 3 ∣ N₁) (hN : 5 < N₁) {ν : ℝ} (hν0 : 0 ≤ ν)
    (hν : ν * 3 ^ (2 * (k + 1)) ≤ 1) {κa rF : ℝ} (hκa : κa ≤ 2 * R.κdec)
    {F : RawData 3 3 (N₁ * 3 ^ R.m₁) (k + 1) 2 × (Fin 3 → ℂ) →
      ((lvTop N₁ R.m₁ k (rhoSep R.m₁)).Ω 1 × Fin 2 → ℂ) ×
        ((lvTop N₁ R.m₁ k (rhoSep R.m₁)).Ω 1 → ℂ)}
    (hF : IsRenSol (N := 2) (lvTop N₁ R.m₁ k (rhoSep R.m₁)) (compWeight 3 1) ν R.t R.t rF
      (8 * R.t) F) (hrF : R.r₀ ≤ rF)
    (z : Torus 3 (N₁ * 3 ^ R.m₁ * 3 ^ (k + 1 - (k + 1)))) :
    HasLocPrinciple (N := 2) (lvTop N₁ R.m₁ k (rhoSep R.m₁))
      (XiCOneReal (lvTop N₁ R.m₁ k (rhoSep R.m₁)) (compWeight 3 1) ν R.t) R.r₀
      (renYs (renCube (lvTop N₁ R.m₁ k (rhoSep R.m₁))
          (X1 (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 1 k (fam 1 (blockSite k z))))
        (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 1
        (X1 (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 1 k (fam 1 (blockSite k z))))
      (renDY (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 1) κa 1
      (fun _ ξ => pertClass (lvTop N₁ R.m₁ k (rhoSep R.m₁))
        (renCK 3 3 2 R.BG R.κ * (cK2 3 3 2 * (8 * R.t * ‖ξ‖)))
        (bgK1 3 3 2 * (xiC1 3 * R.t) + renCK 3 3 2 R.BG R.κ * cK2 3 3 2 * (8 * R.t) * R.r₀ + 2)
        (renMassU ν ξ))
      (fun _ v ξ => renC2On (lvTop N₁ R.m₁ k (rhoSep R.m₁)) (compWeight 3 1)
        (blockSites 3 3 N₁ R.m₁ (k + 1) k z) ξ (renMassU ν ξ) v.2 v.1)
      (fun D ξ => ((F ((D.Ψ, D.h), ξ)).1,
        bgMultC (lvTop N₁ R.m₁ k (rhoSep R.m₁)) (compWeight 3 1) ν (bgC0 3 3 2) D +
          (F ((D.Ψ, D.h), ξ)).2)) := by
  have hC := R.flCore_scale k hk N₁ hN hν0 hν
  have hN3 : 3 ^ 1 ∣ N₁ := by simpa using h3N
  obtain ⟨hcK, hCB⟩ := R.toStepTowerRen.renCK_facts
  exact renLocC2_zero_at hC hatConn_lvTop isLevel_lvTop le_rfl hN3 (by norm_num) (by norm_num)
    R.κ0_nonneg R.κdec_lower R.κ_lower R.κ_one R.κ_log hκa R.r₀_pos R.r₀_le hF hrF R.D₀_le_one
    R.D₀_le_star R.D₁_le_star R.end_margin (by have := R.t_pos; positivity) hcK hCB z

end Balaban.Inhabited
