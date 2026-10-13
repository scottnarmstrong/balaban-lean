/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.StepTowerRenSol
public import Balaban.Inhabited.RenormLocC2ZeroTower
public import Balaban.Fluctuation.RenormSharedClass
public import Balaban.Fluctuation.RenormInputZero

/-!
# The renormalization input record at every scale of the shared tower

For `R : StepTowerRenSol κmin`, at the step `lvTop` of every scale `k ≥ 1`, every torus with
`3 ∣ N₁`, `5 < N₁`, every mass `0 ≤ ν` with `ν · 3^{2(k+1)} ≤ 1`:

* `renLoc_fields_scale_of_tower`: the renormalized solution `F` (`IsRenSol` at `r_F = r₀`) and the
  three localization fields `locC1`, `locC2`, `locDφ` of `RenormExpInput`, in the exact field
  types, at one set of parameters (`a = compWeight 3 1`, `ε = t`, `r₀`, `c_K = renCK`, `B = 8 t`,
  `K_loc = 1`, `κa, κb ≤ 2 κdec`);
* `renormExpInput_scale_of_tower_of_exp`: the full record with zero old terms, conditional on the
  two new-term expansions `expE0`, `expM0`.  **The functions `E0θ`, `M0θ` are binders here, not the
  physical functions.**  With `E0θ = M0θ = 0` the record is inhabited, but that is not the physical
  input: the physical theorem needs the definitions of the new terms (RENFIELDS, "Why this is a
  contract");
* `thm31g_C1_scale_of_tower`, `thm31g_C2_scale_of_tower`: the localized expansions of `C₁` and `C₂`
  (Theorem 3.1 (g)) at every scale, unconditional: they use only `locC1`, `locC2`, and their
  conclusions do not mention `E0θ`, `M0θ`;
* `renormExpInput_stepTowerRenSol_instance`: the instance at `k = 1`, `N₁ = 18`.
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation
  Balaban.Localization Balaban.Localization.LevelPair Balaban.Localization.I5Inhabited
  Balaban.Polymer Balaban.SmallField.Def6 Balaban.Analysis Balaban.Inhabited.LevelStep LocalCover

/-- **The three localization fields and the solution at every scale of the tower**, at one set of
parameters, in the exact types of the fields `locC1`, `locC2`, `locDφ` of `RenormExpInput`. -/
theorem renLoc_fields_scale_of_tower {κmin : ℝ} (R : StepTowerRenSol κmin) (k : ℕ) (hk : 1 ≤ k)
    (N₁ : ℕ) [NeZero N₁] (h3N : 3 ∣ N₁) (hN : 5 < N₁) {ν : ℝ} (hν0 : 0 ≤ ν)
    (hν : ν * 3 ^ (2 * (k + 1)) ≤ 1) {κa κb : ℝ} (hκa : κa ≤ 2 * R.κdec)
    (hκb : κb ≤ 2 * R.κdec) :
    ∃ F : RawData 3 3 (N₁ * 3 ^ R.m₁) (k + 1) 2 × (Fin 3 → ℂ) →
        ((lvTop N₁ R.m₁ k (rhoSep R.m₁)).Ω 1 × Fin 2 → ℂ) ×
          ((lvTop N₁ R.m₁ k (rhoSep R.m₁)).Ω 1 → ℂ),
      IsRenSol (N := 2) (lvTop N₁ R.m₁ k (rhoSep R.m₁)) (compWeight 3 1) ν R.t R.t R.r₀
        (8 * R.t) F ∧
      (∀ z : Torus 3 (N₁ * 3 ^ R.m₁ * 3 ^ (k + 1 - (k + 1))),
        HasLocPrinciple (N := 2) (lvTop N₁ R.m₁ k (rhoSep R.m₁))
          (XiCOneReal (lvTop N₁ R.m₁ k (rhoSep R.m₁)) (compWeight 3 1) ν R.t) R.r₀
          (renYs (renCube (lvTop N₁ R.m₁ k (rhoSep R.m₁))
              (X1 (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 1 k (fam 1 (blockSite k z))))
            (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 1
            (X1 (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 1 k (fam 1 (blockSite k z))))
          (renDY (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 1) κa 1
          (fun D _ => bgClass (lvTop N₁ R.m₁ k (rhoSep R.m₁)) ν
            (renCK 3 3 2 R.BG R.κ * R.t) D)
          (fun D φ ξ => renC1On (lvTop N₁ R.m₁ k (rhoSep R.m₁)) (compWeight 3 1) ν R.t
            (blockSites 3 3 N₁ R.m₁ (k + 1) k z) D.Ψ D.h φ ξ)
          (fun D _ => bgFieldC (lvTop N₁ R.m₁ k (rhoSep R.m₁)) (compWeight 3 1) ν
            (bgC0 3 3 2) D)) ∧
      (∀ z : Torus 3 (N₁ * 3 ^ R.m₁ * 3 ^ (k + 1 - (k + 1))),
        HasLocPrinciple (N := 2) (lvTop N₁ R.m₁ k (rhoSep R.m₁))
          (XiCOneReal (lvTop N₁ R.m₁ k (rhoSep R.m₁)) (compWeight 3 1) ν R.t) R.r₀
          (renYs (renCube (lvTop N₁ R.m₁ k (rhoSep R.m₁))
              (X1 (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 1 k (fam 1 (blockSite k z))))
            (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 1
            (X1 (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 1 k (fam 1 (blockSite k z))))
          (renDY (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 1) κa 1
          (fun _ ξ => pertClass (lvTop N₁ R.m₁ k (rhoSep R.m₁))
            (renCK 3 3 2 R.BG R.κ * (cK2 3 3 2 * (8 * R.t * ‖ξ‖)))
            (bgK1 3 3 2 * (xiC1 3 * R.t) + renCK 3 3 2 R.BG R.κ * cK2 3 3 2 * (8 * R.t) * R.r₀
              + 2) (renMassU ν ξ))
          (fun _ v ξ => renC2On (lvTop N₁ R.m₁ k (rhoSep R.m₁)) (compWeight 3 1)
            (blockSites 3 3 N₁ R.m₁ (k + 1) k z) ξ (renMassU ν ξ) v.2 v.1)
          (fun D ξ => ((F ((D.Ψ, D.h), ξ)).1,
            bgMultC (lvTop N₁ R.m₁ k (rhoSep R.m₁)) (compWeight 3 1) ν (bgC0 3 3 2) D +
              (F ((D.Ψ, D.h), ξ)).2))) ∧
      (∀ p : (lvTop N₁ R.m₁ k (rhoSep R.m₁)).Ω 1 × Fin 2,
        HasLocPrinciple (N := 2) (lvTop N₁ R.m₁ k (rhoSep R.m₁))
          (XiCOneReal (lvTop N₁ R.m₁ k (rhoSep R.m₁)) (compWeight 3 1) ν R.t) R.r₀
          (renYs (renCube (lvTop N₁ R.m₁ k (rhoSep R.m₁))
              (X1 (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 1 k
                (fam 1 (p.1 : CTorus 3 3 N₁ R.m₁ (k + 1)))))
            (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 1
            (X1 (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 1 k
              (fam 1 (p.1 : CTorus 3 3 N₁ R.m₁ (k + 1)))))
          (renDY (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 1) κb 1
          (fun _ ξ => {v | SupBounds (lvTop N₁ R.m₁ k (rhoSep R.m₁)) v
            (renCK 3 3 2 R.BG R.κ * (cK2 3 3 2 * (8 * R.t * ‖ξ‖)))})
          (fun _ v _ => v p) (fun D ξ => (F ((D.Ψ, D.h), ξ)).1)) := by
  obtain ⟨F, hF⟩ := exists_isRenSol_scale_of_tower R k hk N₁ hN hν0 hν
  refine ⟨F, hF, fun z => ?_, fun z => ?_, fun p => ?_⟩
  · exact renLocC1_scale_of_tower_of_le R.toStepTower k hk N₁ h3N hN hν0 hν hκa R.r₀_pos
      R.r₀_le z (renCK_ge (d := 3) (L := 3) (N := 2) (BG := R.BG) (κ := R.κ))
  · exact renLocC2_scale_of_tower R.toStepTowerRenEnd k hk N₁ h3N hN hν0 hν hκa hF le_rfl z
  · exact renLocDphi_scale_of_tower R.toStepTowerRenEnd k hk N₁ h3N hN hν0 hν hκb hF le_rfl p

/-- **The renormalization input record at every scale of the tower, with zero old terms,
conditional on the two new-term expansions.**  The functions `E0θ`, `M0θ` are binders: they are
NOT the physical functions.  With `E0θ = M0θ = 0` (and `BE0 = BM0 = 0`) the record is inhabited,
but that is not the physical input; the physical theorem needs the definitions of the new terms
(RENFIELDS, "Why this is a contract"). -/
theorem renormExpInput_scale_of_tower_of_exp {κmin : ℝ} (R : StepTowerRenSol κmin) (k : ℕ)
    (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁] (h3N : 3 ∣ N₁) (hN : 5 < N₁) {ν : ℝ} (hν0 : 0 ≤ ν)
    (hν : ν * 3 ^ (2 * (k + 1)) ≤ 1) {κa κb : ℝ} (hκa : κa ≤ 2 * R.κdec)
    (hκb : κb ≤ 2 * R.κdec) (BE0 BM0 : ℝ)
    (E0θ : Torus 3 (N₁ * 3 ^ R.m₁ * 3 ^ (k + 1 - (k + 1))) →
      BgData (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 2 → (Fin 3 → ℂ) → ℂ)
    (M0θ : (lvTop N₁ R.m₁ k (rhoSep R.m₁)).Ω 1 × Fin 2 →
      BgData (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 2 → (Fin 3 → ℂ) → ℂ) :
    ∃ F : RawData 3 3 (N₁ * 3 ^ R.m₁) (k + 1) 2 × (Fin 3 → ℂ) →
        ((lvTop N₁ R.m₁ k (rhoSep R.m₁)).Ω 1 × Fin 2 → ℂ) ×
          ((lvTop N₁ R.m₁ k (rhoSep R.m₁)).Ω 1 → ℂ),
      IsRenSol (N := 2) (lvTop N₁ R.m₁ k (rhoSep R.m₁)) (compWeight 3 1) ν R.t R.t R.r₀
        (8 * R.t) F ∧
      ((∀ z : Torus 3 (N₁ * 3 ^ R.m₁ * 3 ^ (k + 1 - (k + 1))), ∃ term,
        IsLocExp (N := 2) (lvTop N₁ R.m₁ k (rhoSep R.m₁))
          (XiCOneReal (lvTop N₁ R.m₁ k (rhoSep R.m₁)) (compWeight 3 1) ν R.t) R.r₀
          (renYs (renCube (lvTop N₁ R.m₁ k (rhoSep R.m₁))
              (X1 (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 1 k (fam 1 (blockSite k z))))
            (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 1
            (X1 (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 1 k (fam 1 (blockSite k z))))
          (renDY (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 1) κa BE0 (E0θ z) term) →
        (∀ p : (lvTop N₁ R.m₁ k (rhoSep R.m₁)).Ω 1 × Fin 2, ∃ term,
        IsLocExp (N := 2) (lvTop N₁ R.m₁ k (rhoSep R.m₁))
          (XiCOneReal (lvTop N₁ R.m₁ k (rhoSep R.m₁)) (compWeight 3 1) ν R.t) R.r₀
          (renYs (renCube (lvTop N₁ R.m₁ k (rhoSep R.m₁))
              (X1 (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 1 k
                (fam 1 (p.1 : CTorus 3 3 N₁ R.m₁ (k + 1)))))
            (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 1
            (X1 (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 1 k
              (fam 1 (p.1 : CTorus 3 3 N₁ R.m₁ (k + 1)))))
          (renDY (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 1) κb BM0 (M0θ p) term) →
        RenormExpInput (N := 2) (lvTop N₁ R.m₁ k (rhoSep R.m₁)) (compWeight 3 1) ν R.t R.r₀
          (renCK 3 3 2 R.BG R.κ) (8 * R.t) F
          (fun z : Torus 3 (N₁ * 3 ^ R.m₁ * 3 ^ (k + 1 - (k + 1))) =>
            blockSites 3 3 N₁ R.m₁ (k + 1) k z)
          (fun z => renYs (renCube (lvTop N₁ R.m₁ k (rhoSep R.m₁))
              (X1 (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 1 k (fam 1 (blockSite k z))))
            (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 1
            (X1 (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 1 k (fam 1 (blockSite k z))))
          (fun p => renYs (renCube (lvTop N₁ R.m₁ k (rhoSep R.m₁))
              (X1 (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 1 k
                (fam 1 (p.1 : CTorus 3 3 N₁ R.m₁ (k + 1)))))
            (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 1
            (X1 (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 1 k
              (fam 1 (p.1 : CTorus 3 3 N₁ R.m₁ (k + 1)))))
          (renDY (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 1) κa κb 1 BE0 0 BM0 0 E0θ
          (fun _ _ _ => 0) M0θ (fun _ _ _ => 0)) := by
  obtain ⟨F, hF, h1, h2, h3⟩ := renLoc_fields_scale_of_tower R k hk N₁ h3N hN hν0 hν hκa hκb
  exact ⟨F, hF, fun hE hM => renormExpInput_zero_of_fields h1 h2 hE h3 hM⟩

/-- **Theorem 3.1 (g), `C₁(z)`, at every scale of the tower, unconditional**: the localized
expansion with the bound `(d + 6)(c_K ε)² W(B_z) ε_R`, `K_loc = 1`.  Only `locC1` is used; the
new-term functions are taken to be `0` and do not occur in the conclusion. -/
theorem thm31g_C1_scale_of_tower {κmin : ℝ} (R : StepTowerRenSol κmin) (k : ℕ) (hk : 1 ≤ k)
    (N₁ : ℕ) [NeZero N₁] (h3N : 3 ∣ N₁) (hN : 5 < N₁) {ν : ℝ} (hν0 : 0 ≤ ν)
    (hν : ν * 3 ^ (2 * (k + 1)) ≤ 1) {κa : ℝ} (hκa : κa ≤ 2 * R.κdec) {εR : ℝ}
    (hεR : εR ≤ R.r₀) (z : Torus 3 (N₁ * 3 ^ R.m₁ * 3 ^ (k + 1 - (k + 1)))) :
    ∃ term, IsLocExp (N := 2) (lvTop N₁ R.m₁ k (rhoSep R.m₁))
      (XiCOneReal (lvTop N₁ R.m₁ k (rhoSep R.m₁)) (compWeight 3 1) ν R.t) εR
      (renYs (renCube (lvTop N₁ R.m₁ k (rhoSep R.m₁))
          (X1 (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 1 k (fam 1 (blockSite k z))))
        (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 1
        (X1 (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 1 k (fam 1 (blockSite k z))))
      (renDY (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 1) κa
      (1 * ((3 + 6) * (renCK 3 3 2 R.BG R.κ * R.t) ^ 2 *
        blockWeight (lvTop N₁ R.m₁ k (rhoSep R.m₁)) (blockSites 3 3 N₁ R.m₁ (k + 1) k z)) *
        εR ^ 1)
      (fun D ξ => renC1On (lvTop N₁ R.m₁ k (rhoSep R.m₁)) (compWeight 3 1) ν R.t
        (blockSites 3 3 N₁ R.m₁ (k + 1) k z) D.Ψ D.h
        (bgFieldC (lvTop N₁ R.m₁ k (rhoSep R.m₁)) (compWeight 3 1) ν (bgC0 3 3 2) D) ξ) term := by
  have hC := R.flCore_scale k hk N₁ hN hν0 hν
  obtain ⟨F, hF, h1, h2, h3⟩ := renLoc_fields_scale_of_tower R k hk N₁ h3N hN hν0 hν hκa hκa
  exact thm31g_C1_zero_of_fields (E0θ := fun _ _ _ => 0) (M0θ := fun _ _ _ => 0) (BE0 := 0)
    (BM0 := 0)
    (renormExpInput_zero_of_fields h1 h2 (fun _ => ⟨_, isLocExp_zero_cover _ _⟩) h3
      (fun _ => ⟨_, isLocExp_zero_cover _ _⟩))
    (bgHyp_lv (k := k) R.m₁ hν0 hν) R.t_pos hC.small1
    (hC.c7le.trans (c7_le_bgC1 3 3 2 R.BG R.κ)) (R.r₀_le) zero_le_one
    (by have := renCK_ge (d := 3) (L := 3) (N := 2) (BG := R.BG) (κ := R.κ)
        have := mul_nonneg (K4_pos (d := 3) (L := 3) (N := 2) (κ := R.κ) (BG := R.BG)
          (by simpa using R.core.some.hS.fam.2.1) (by norm_num)).le
          (by unfold xiC1; positivity : (0:ℝ) ≤ xiC1 3)
        linarith) hεR z

/-- **Theorem 3.1 (g), `C₂(z)`, at every scale of the tower, unconditional**: bound
`(17/32) N (3 + A)(c_K K₂ B)² W(B_z) ε_R²`, `K_loc = 1`, `N = 2`, `B = 8 t`,
`A = K₁ ξ₁ t + c_K K₂ B r₀ + 2`.  Only `locC2` is used. -/
theorem thm31g_C2_scale_of_tower {κmin : ℝ} (R : StepTowerRenSol κmin) (k : ℕ) (hk : 1 ≤ k)
    (N₁ : ℕ) [NeZero N₁] (h3N : 3 ∣ N₁) (hN : 5 < N₁) {ν : ℝ} (hν0 : 0 ≤ ν)
    (hν : ν * 3 ^ (2 * (k + 1)) ≤ 1) {κa : ℝ} (hκa : κa ≤ 2 * R.κdec) {εR : ℝ}
    (hεR0 : 0 ≤ εR) (hεR : εR ≤ R.r₀) (z : Torus 3 (N₁ * 3 ^ R.m₁ * 3 ^ (k + 1 - (k + 1)))) :
    ∃ F : RawData 3 3 (N₁ * 3 ^ R.m₁) (k + 1) 2 × (Fin 3 → ℂ) →
        ((lvTop N₁ R.m₁ k (rhoSep R.m₁)).Ω 1 × Fin 2 → ℂ) ×
          ((lvTop N₁ R.m₁ k (rhoSep R.m₁)).Ω 1 → ℂ),
      IsRenSol (N := 2) (lvTop N₁ R.m₁ k (rhoSep R.m₁)) (compWeight 3 1) ν R.t R.t R.r₀
        (8 * R.t) F ∧
      ∃ term, IsLocExp (N := 2) (lvTop N₁ R.m₁ k (rhoSep R.m₁))
      (XiCOneReal (lvTop N₁ R.m₁ k (rhoSep R.m₁)) (compWeight 3 1) ν R.t) εR
      (renYs (renCube (lvTop N₁ R.m₁ k (rhoSep R.m₁))
          (X1 (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 1 k (fam 1 (blockSite k z))))
        (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 1
        (X1 (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 1 k (fam 1 (blockSite k z))))
      (renDY (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 1) κa
      (1 * (17 / 32 * ((2 : ℕ) * ((3 + (bgK1 3 3 2 * (xiC1 3 * R.t) +
        renCK 3 3 2 R.BG R.κ * cK2 3 3 2 * (8 * R.t) * R.r₀ + 2)) *
        (renCK 3 3 2 R.BG R.κ * cK2 3 3 2 * (8 * R.t)) ^ 2)) *
        blockWeight (lvTop N₁ R.m₁ k (rhoSep R.m₁)) (blockSites 3 3 N₁ R.m₁ (k + 1) k z)) *
        εR ^ 2)
      (fun D ξ => renC2On (lvTop N₁ R.m₁ k (rhoSep R.m₁)) (compWeight 3 1)
        (blockSites 3 3 N₁ R.m₁ (k + 1) k z) ξ (renMassU ν ξ)
        (bgMultC (lvTop N₁ R.m₁ k (rhoSep R.m₁)) (compWeight 3 1) ν (bgC0 3 3 2) D +
          (F ((D.Ψ, D.h), ξ)).2) (F ((D.Ψ, D.h), ξ)).1) term := by
  have hC := R.flCore_scale k hk N₁ hN hν0 hν
  obtain ⟨F, hF, h1, h2, h3⟩ := renLoc_fields_scale_of_tower R k hk N₁ h3N hN hν0 hν hκa hκa
  refine ⟨F, hF, ?_⟩
  exact thm31g_C2_zero_of_fields (E0θ := fun _ _ _ => 0) (M0θ := fun _ _ _ => 0) (BE0 := 0)
    (BM0 := 0)
    (renormExpInput_zero_of_fields h1 h2 (fun _ => ⟨_, isLocExp_zero_cover _ _⟩) h3
      (fun _ => ⟨_, isLocExp_zero_cover _ _⟩))
    (bgHyp_lv (k := k) R.m₁ hν0 hν) R.t_pos R.r₀_le zero_le_one
    (by have := R.t_pos; positivity) (R.toStepTowerRen.renCK_facts.1) hεR0 hεR z

/-- The tower record is inhabited, so the theorems above are not vacuous: they apply at `k = 1`,
`N₁ = 18`, `ν = 0` for every `κmin`. -/
theorem renormExpInput_stepTowerRenSol_instance (κmin : ℝ) :
    ∃ R : StepTowerRenSol κmin, ∃ F : RawData 3 3 (18 * 3 ^ R.m₁) (1 + 1) 2 × (Fin 3 → ℂ) →
        ((lvTop 18 R.m₁ 1 (rhoSep R.m₁)).Ω 1 × Fin 2 → ℂ) ×
          ((lvTop 18 R.m₁ 1 (rhoSep R.m₁)).Ω 1 → ℂ),
      IsRenSol (N := 2) (lvTop 18 R.m₁ 1 (rhoSep R.m₁)) (compWeight 3 1) 0 R.t R.t R.r₀
        (8 * R.t) F ∧
      ∀ z : Torus 3 (18 * 3 ^ R.m₁ * 3 ^ (1 + 1 - (1 + 1))), ∃ term,
        IsLocExp (N := 2) (lvTop 18 R.m₁ 1 (rhoSep R.m₁))
          (XiCOneReal (lvTop 18 R.m₁ 1 (rhoSep R.m₁)) (compWeight 3 1) 0 R.t) R.r₀
          (renYs (renCube (lvTop 18 R.m₁ 1 (rhoSep R.m₁))
              (X1 (lvTop 18 R.m₁ 1 (rhoSep R.m₁)) 1 1 (fam 1 (blockSite 1 z))))
            (lvTop 18 R.m₁ 1 (rhoSep R.m₁)) 1
            (X1 (lvTop 18 R.m₁ 1 (rhoSep R.m₁)) 1 1 (fam 1 (blockSite 1 z))))
          (renDY (lvTop 18 R.m₁ 1 (rhoSep R.m₁)) 1) 0
          (1 * ((3 + 6) * (renCK 3 3 2 R.BG R.κ * R.t) ^ 2 *
            blockWeight (lvTop 18 R.m₁ 1 (rhoSep R.m₁)) (blockSites 3 3 18 R.m₁ (1 + 1) 1 z)) *
            R.r₀ ^ 1)
          (fun D ξ => renC1On (lvTop 18 R.m₁ 1 (rhoSep R.m₁)) (compWeight 3 1) 0 R.t
            (blockSites 3 3 18 R.m₁ (1 + 1) 1 z) D.Ψ D.h
            (bgFieldC (lvTop 18 R.m₁ 1 (rhoSep R.m₁)) (compWeight 3 1) 0 (bgC0 3 3 2) D) ξ)
          term := by
  obtain ⟨R⟩ := exists_stepTowerRenSol κmin
  obtain ⟨F, hF⟩ := exists_isRenSol_scale_of_tower R 1 le_rfl 18 (by norm_num) (ν := 0)
    le_rfl (by norm_num)
  exact ⟨R, F, hF, fun z => thm31g_C1_scale_of_tower R 1 le_rfl 18 (by norm_num) (by norm_num)
    le_rfl (by norm_num) (κa := 0) (by have := R.κdec_lower; have := R.κ0_nonneg; linarith) le_rfl z⟩

end Balaban.Inhabited
