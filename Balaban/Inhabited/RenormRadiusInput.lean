/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.StepTowerGProducers
public import Balaban.Inhabited.RenormRadiusLoc
public import Balaban.Fluctuation.RenormInputZero

/-!
# The renormalization input record at the tower for a class radius `e ≤ t`

For `R : StepTowerRenSol κmin` and `0 < e ≤ t`, at the step `lvTop` of every scale `k ≥ 1`, every
torus with `3 ∣ N₁`, `5 < N₁`, every mass `0 ≤ ν` with `ν · 3^{2(k+1)} ≤ 1`:

* `renormExpInput_scale_of_tower_of_exp_at`: the record
  `RenormExpInput … ν e r₀ renCK (8 e) F …` with zero old terms, for the solution map `F` of
  `IsRenSol … ν e e r₀ (8 e)`, conditional on the two new-term expansions `expE0`, `expM0` on the
  class `XiCOneReal … ν e`.  **The functions `E0θ`, `M0θ` are binders here, not the physical
  functions**, exactly as in the landed `renormExpInput_scale_of_tower_of_exp`;
* `thm31g_C1_scale_of_tower_at`, `thm31g_C2_scale_of_tower_at`: the localized expansions of `C₁`
  and `C₂` (Theorem 3.1 (g)) on the class of radius `e`, unconditional.

The polydisc radius `r₀`, the rates, the cover and the constants `renCK`, `K₁`, `K₂` are those of
the tower.  No occurrence of `t` is left in these statements.  The general versions (`…G…_at`, for `StepTowerG`, `StepTowerRenEndG`, `StepTowerRenSolG` at any `d, L, N`) carry the proofs; the `3, 3, 2` theorems are their corollaries.  Each `_at` theorem is followed by the landed
theorem of the same name without `_at`, proved as its corollary at `e = t`; the file ends with
`renormExpInput_stepTowerRenSol_instance`, moved from the former `RenormExpInputTower`.
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation
  Balaban.Localization Balaban.Localization.LevelPair Balaban.Localization.I5Inhabited
  Balaban.Polymer Balaban.SmallField.Def6 Balaban.Analysis Balaban.Inhabited.LevelStep LocalCover

section General

/-- **The renormalization input record at every scale of the general tower, at the class radius `e ≤ t`,
with zero old terms, conditional on the two new-term expansions.**  The functions `E0θ`, `M0θ` are
binders: they are NOT the physical functions.  With `E0θ = M0θ = 0` (and `BE0 = BM0 = 0`) the
record is inhabited, but that is not the physical input; the physical theorem needs the definitions
of the new terms. -/
theorem renormExpInput_scale_of_towerG_of_exp_at {d L N : ℕ} [NeZero L] {κmin : ℝ}
    (R : StepTowerRenSolG d L N κmin) (k : ℕ)
    (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁] (hN₀ : L ^ R.m₀ ∣ N₁) (hN : 5 < N₁) {ν : ℝ} (hν0 : 0 ≤ ν)
    (hν : ν * (L : ℝ) ^ (2 * (k + 1)) ≤ 1) {e : ℝ} (he : 0 < e) (het : e ≤ R.t)
    {κa κb : ℝ} (hκa : κa ≤ 2 * R.κdec)
    (hκb : κb ≤ 2 * R.κdec) (BE0 BM0 : ℝ)
    (E0θ : Torus d (N₁ * L ^ R.m₁ * L ^ (k + 1 - (k + 1))) →
      BgData (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)) N → (Fin 3 → ℂ) → ℂ)
    (M0θ : (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)).Ω 1 × Fin N →
      BgData (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)) N → (Fin 3 → ℂ) → ℂ) :
    ∃ F : RawData d L (N₁ * L ^ R.m₁) (k + 1) N × (Fin 3 → ℂ) →
        ((lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)).Ω 1 × Fin N → ℂ) ×
          ((lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)).Ω 1 → ℂ),
      IsRenSol (N := N) (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)) (compWeight L 1) ν e e R.r₀
        (8 * e) F ∧
      ((∀ z : Torus d (N₁ * L ^ R.m₁ * L ^ (k + 1 - (k + 1))), ∃ term,
        IsLocExp (N := N) (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁))
          (XiCOneReal (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)) (compWeight L 1) ν e) R.r₀
          (renYs (renCube (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁))
              (X1 (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)) R.m₀ k (fam R.m₀ (blockSite k z))))
            (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)) R.m₀
            (X1 (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)) R.m₀ k (fam R.m₀ (blockSite k z))))
          (renDY (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)) R.m₀) κa BE0 (E0θ z) term) →
        (∀ p : (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)).Ω 1 × Fin N, ∃ term,
        IsLocExp (N := N) (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁))
          (XiCOneReal (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)) (compWeight L 1) ν e) R.r₀
          (renYs (renCube (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁))
              (X1 (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)) R.m₀ k
                (fam R.m₀ (p.1 : CTorus d L N₁ R.m₁ (k + 1)))))
            (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)) R.m₀
            (X1 (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)) R.m₀ k
              (fam R.m₀ (p.1 : CTorus d L N₁ R.m₁ (k + 1)))))
          (renDY (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)) R.m₀) κb BM0 (M0θ p) term) →
        RenormExpInput (N := N) (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)) (compWeight L 1) ν e R.r₀
          (renCK d L N R.BG R.κ) (8 * e) F
          (fun z : Torus d (N₁ * L ^ R.m₁ * L ^ (k + 1 - (k + 1))) =>
            blockSites d L N₁ R.m₁ (k + 1) k z)
          (fun z => renYs (renCube (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁))
              (X1 (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)) R.m₀ k (fam R.m₀ (blockSite k z))))
            (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)) R.m₀
            (X1 (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)) R.m₀ k (fam R.m₀ (blockSite k z))))
          (fun p => renYs (renCube (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁))
              (X1 (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)) R.m₀ k
                (fam R.m₀ (p.1 : CTorus d L N₁ R.m₁ (k + 1)))))
            (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)) R.m₀
            (X1 (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)) R.m₀ k
              (fam R.m₀ (p.1 : CTorus d L N₁ R.m₁ (k + 1)))))
          (renDY (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)) R.m₀) κa κb 1 BE0 0 BM0 0 E0θ
          (fun _ _ _ => 0) M0θ (fun _ _ _ => 0)) := by
  obtain ⟨F, hF, h1, h2, h3⟩ :=
    renLoc_fields_scale_of_towerG_at R k hk N₁ hN₀ hN hν0 hν he het hκa hκb
  exact ⟨F, hF, fun hE hM => renormExpInput_zero_of_fields h1 h2 hE h3 hM⟩

/-- **Theorem 3.1 (g), `C₁(z)`, at every scale of the general tower, at the class radius `e ≤ t`,
unconditional**: the localized expansion with the bound `(d + 6)(c_K e)² W(B_z) ε_R`,
`K_loc = 1`.  Only `locC1` is used; the new-term functions are taken to be `0` and do not occur in
the conclusion. -/
theorem thm31g_C1_scale_of_towerG_at {d L N : ℕ} [NeZero L] {κmin : ℝ}
    (R : StepTowerRenSolG d L N κmin) (k : ℕ) (hk : 1 ≤ k)
    (N₁ : ℕ) [NeZero N₁] (hN₀ : L ^ R.m₀ ∣ N₁) (hN : 5 < N₁) {ν : ℝ} (hν0 : 0 ≤ ν)
    (hν : ν * (L : ℝ) ^ (2 * (k + 1)) ≤ 1) {e : ℝ} (he : 0 < e) (het : e ≤ R.t)
    {κa : ℝ} (hκa : κa ≤ 2 * R.κdec) {εR : ℝ}
    (hεR : εR ≤ R.r₀) (z : Torus d (N₁ * L ^ R.m₁ * L ^ (k + 1 - (k + 1)))) :
    ∃ term, IsLocExp (N := N) (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁))
      (XiCOneReal (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)) (compWeight L 1) ν e) εR
      (renYs (renCube (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁))
          (X1 (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)) R.m₀ k (fam R.m₀ (blockSite k z))))
        (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)) R.m₀
        (X1 (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)) R.m₀ k (fam R.m₀ (blockSite k z))))
      (renDY (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)) R.m₀) κa
      (1 * ((d + 6) * (renCK d L N R.BG R.κ * e) ^ 2 *
        blockWeight (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)) (blockSites d L N₁ R.m₁ (k + 1) k z)) *
        εR ^ 1)
      (fun D ξ => renC1On (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)) (compWeight L 1) ν e
        (blockSites d L N₁ R.m₁ (k + 1) k z) D.Ψ D.h
        (bgFieldC (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)) (compWeight L 1) ν (bgC0 d L N) D) ξ) term := by
  have hC := R.toStepTowerG.flCore_scale_mono k hk N₁ hN hν0 hν he het he het
  obtain ⟨F, hF, h1, h2, h3⟩ :=
    renLoc_fields_scale_of_towerG_at R k hk N₁ hN₀ hN hν0 hν he het hκa hκa
  exact thm31g_C1_zero_of_fields (E0θ := fun _ _ _ => 0) (M0θ := fun _ _ _ => 0) (BE0 := 0)
    (BM0 := 0)
    (renormExpInput_zero_of_fields h1 h2 (fun _ => ⟨_, isLocExp_zero_cover _ _⟩) h3
      (fun _ => ⟨_, isLocExp_zero_cover _ _⟩))
    (bgHyp_lvG (k := k) R.hd R.hL (bgR0_le_rhoSepG R.m₁ R.hd R.hL) hν0 hν) he hC.small1
    (hC.c7le.trans (c7_le_bgC1 d L N R.BG R.κ)) (R.r₀_le) zero_le_one
    R.toStepTowerRenG.renCK_facts.1 hεR z

/-- **Theorem 3.1 (g), `C₂(z)`, at every scale of the general tower, at the class radius `e ≤ t`,
unconditional**: bound `(17/32) N (3 + A)(c_K K₂ B)² W(B_z) ε_R²`, `K_loc = 1`, `N = 2`,
`B = 8 e`, `A = K₁ ξ₁ e + c_K K₂ B r₀ + 2`, for the solution map `F` of
`IsRenSol … ν e e r₀ (8 e)`.  Only `locC2` is used. -/
theorem thm31g_C2_scale_of_towerG_at {d L N : ℕ} [NeZero L] {κmin : ℝ}
    (R : StepTowerRenSolG d L N κmin) (k : ℕ) (hk : 1 ≤ k)
    (N₁ : ℕ) [NeZero N₁] (hN₀ : L ^ R.m₀ ∣ N₁) (hN : 5 < N₁) {ν : ℝ} (hν0 : 0 ≤ ν)
    (hν : ν * (L : ℝ) ^ (2 * (k + 1)) ≤ 1) {e : ℝ} (he : 0 < e) (het : e ≤ R.t)
    {κa : ℝ} (hκa : κa ≤ 2 * R.κdec) {εR : ℝ}
    (hεR0 : 0 ≤ εR) (hεR : εR ≤ R.r₀) (z : Torus d (N₁ * L ^ R.m₁ * L ^ (k + 1 - (k + 1)))) :
    ∃ F : RawData d L (N₁ * L ^ R.m₁) (k + 1) N × (Fin 3 → ℂ) →
        ((lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)).Ω 1 × Fin N → ℂ) ×
          ((lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)).Ω 1 → ℂ),
      IsRenSol (N := N) (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)) (compWeight L 1) ν e e R.r₀
        (8 * e) F ∧
      ∃ term, IsLocExp (N := N) (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁))
      (XiCOneReal (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)) (compWeight L 1) ν e) εR
      (renYs (renCube (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁))
          (X1 (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)) R.m₀ k (fam R.m₀ (blockSite k z))))
        (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)) R.m₀
        (X1 (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)) R.m₀ k (fam R.m₀ (blockSite k z))))
      (renDY (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)) R.m₀) κa
      (1 * (17 / 32 * (N * ((3 + (bgK1 d L N * (xiC1 d * e) +
        renCK d L N R.BG R.κ * cK2 d L N * (8 * e) * R.r₀ + 2)) *
        (renCK d L N R.BG R.κ * cK2 d L N * (8 * e)) ^ 2)) *
        blockWeight (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)) (blockSites d L N₁ R.m₁ (k + 1) k z)) *
        εR ^ 2)
      (fun D ξ => renC2On (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)) (compWeight L 1)
        (blockSites d L N₁ R.m₁ (k + 1) k z) ξ (renMassU ν ξ)
        (bgMultC (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)) (compWeight L 1) ν (bgC0 d L N) D +
          (F ((D.Ψ, D.h), ξ)).2) (F ((D.Ψ, D.h), ξ)).1) term := by
  obtain ⟨F, hF, h1, h2, h3⟩ :=
    renLoc_fields_scale_of_towerG_at R k hk N₁ hN₀ hN hν0 hν he het hκa hκa
  refine ⟨F, hF, ?_⟩
  exact thm31g_C2_zero_of_fields (E0θ := fun _ _ _ => 0) (M0θ := fun _ _ _ => 0) (BE0 := 0)
    (BM0 := 0)
    (renormExpInput_zero_of_fields h1 h2 (fun _ => ⟨_, isLocExp_zero_cover _ _⟩) h3
      (fun _ => ⟨_, isLocExp_zero_cover _ _⟩))
    (bgHyp_lvG (k := k) R.hd R.hL (bgR0_le_rhoSepG R.m₁ R.hd R.hL) hν0 hν) he R.r₀_le zero_le_one
    (by positivity) (R.toStepTowerRenG.renCK_facts.1) hεR0 hεR z

end General

/-- **The renormalization input record at every scale of the tower, at the class radius `e ≤ t`,
with zero old terms, conditional on the two new-term expansions.**  The functions `E0θ`, `M0θ` are
binders: they are NOT the physical functions.  With `E0θ = M0θ = 0` (and `BE0 = BM0 = 0`) the
record is inhabited, but that is not the physical input; the physical theorem needs the definitions
of the new terms. -/
theorem renormExpInput_scale_of_tower_of_exp_at {κmin : ℝ} (R : StepTowerRenSol κmin) (k : ℕ)
    (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁] (h3N : 3 ∣ N₁) (hN : 5 < N₁) {ν : ℝ} (hν0 : 0 ≤ ν)
    (hν : ν * 3 ^ (2 * (k + 1)) ≤ 1) {e : ℝ} (he : 0 < e) (het : e ≤ R.t)
    {κa κb : ℝ} (hκa : κa ≤ 2 * R.κdec)
    (hκb : κb ≤ 2 * R.κdec) (BE0 BM0 : ℝ)
    (E0θ : Torus 3 (N₁ * 3 ^ R.m₁ * 3 ^ (k + 1 - (k + 1))) →
      BgData (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 2 → (Fin 3 → ℂ) → ℂ)
    (M0θ : (lvTop N₁ R.m₁ k (rhoSep R.m₁)).Ω 1 × Fin 2 →
      BgData (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 2 → (Fin 3 → ℂ) → ℂ) :
    ∃ F : RawData 3 3 (N₁ * 3 ^ R.m₁) (k + 1) 2 × (Fin 3 → ℂ) →
        ((lvTop N₁ R.m₁ k (rhoSep R.m₁)).Ω 1 × Fin 2 → ℂ) ×
          ((lvTop N₁ R.m₁ k (rhoSep R.m₁)).Ω 1 → ℂ),
      IsRenSol (N := 2) (lvTop N₁ R.m₁ k (rhoSep R.m₁)) (compWeight 3 1) ν e e R.r₀
        (8 * e) F ∧
      ((∀ z : Torus 3 (N₁ * 3 ^ R.m₁ * 3 ^ (k + 1 - (k + 1))), ∃ term,
        IsLocExp (N := 2) (lvTop N₁ R.m₁ k (rhoSep R.m₁))
          (XiCOneReal (lvTop N₁ R.m₁ k (rhoSep R.m₁)) (compWeight 3 1) ν e) R.r₀
          (renYs (renCube (lvTop N₁ R.m₁ k (rhoSep R.m₁))
              (X1 (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 1 k (fam 1 (blockSite k z))))
            (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 1
            (X1 (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 1 k (fam 1 (blockSite k z))))
          (renDY (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 1) κa BE0 (E0θ z) term) →
        (∀ p : (lvTop N₁ R.m₁ k (rhoSep R.m₁)).Ω 1 × Fin 2, ∃ term,
        IsLocExp (N := 2) (lvTop N₁ R.m₁ k (rhoSep R.m₁))
          (XiCOneReal (lvTop N₁ R.m₁ k (rhoSep R.m₁)) (compWeight 3 1) ν e) R.r₀
          (renYs (renCube (lvTop N₁ R.m₁ k (rhoSep R.m₁))
              (X1 (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 1 k
                (fam 1 (p.1 : CTorus 3 3 N₁ R.m₁ (k + 1)))))
            (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 1
            (X1 (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 1 k
              (fam 1 (p.1 : CTorus 3 3 N₁ R.m₁ (k + 1)))))
          (renDY (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 1) κb BM0 (M0θ p) term) →
        RenormExpInput (N := 2) (lvTop N₁ R.m₁ k (rhoSep R.m₁)) (compWeight 3 1) ν e R.r₀
          (renCK 3 3 2 R.BG R.κ) (8 * e) F
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
  have h := renormExpInput_scale_of_towerG_of_exp_at R.toG k hk N₁ (by simpa using h3N) hN hν0
    (by simpa using hν) he het hκa hκb BE0 BM0
  rw [rhoSepG_three] at h
  exact h E0θ M0θ


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
          (fun _ _ _ => 0) M0θ (fun _ _ _ => 0)) :=
  renormExpInput_scale_of_tower_of_exp_at R k hk N₁ h3N hN hν0 hν R.t_pos le_rfl hκa hκb BE0 BM0
    E0θ M0θ

/-- **Theorem 3.1 (g), `C₁(z)`, at every scale of the tower, at the class radius `e ≤ t`,
unconditional**: the localized expansion with the bound `(d + 6)(c_K e)² W(B_z) ε_R`,
`K_loc = 1`.  Only `locC1` is used; the new-term functions are taken to be `0` and do not occur in
the conclusion. -/
theorem thm31g_C1_scale_of_tower_at {κmin : ℝ} (R : StepTowerRenSol κmin) (k : ℕ) (hk : 1 ≤ k)
    (N₁ : ℕ) [NeZero N₁] (h3N : 3 ∣ N₁) (hN : 5 < N₁) {ν : ℝ} (hν0 : 0 ≤ ν)
    (hν : ν * 3 ^ (2 * (k + 1)) ≤ 1) {e : ℝ} (he : 0 < e) (het : e ≤ R.t)
    {κa : ℝ} (hκa : κa ≤ 2 * R.κdec) {εR : ℝ}
    (hεR : εR ≤ R.r₀) (z : Torus 3 (N₁ * 3 ^ R.m₁ * 3 ^ (k + 1 - (k + 1)))) :
    ∃ term, IsLocExp (N := 2) (lvTop N₁ R.m₁ k (rhoSep R.m₁))
      (XiCOneReal (lvTop N₁ R.m₁ k (rhoSep R.m₁)) (compWeight 3 1) ν e) εR
      (renYs (renCube (lvTop N₁ R.m₁ k (rhoSep R.m₁))
          (X1 (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 1 k (fam 1 (blockSite k z))))
        (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 1
        (X1 (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 1 k (fam 1 (blockSite k z))))
      (renDY (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 1) κa
      (1 * ((3 + 6) * (renCK 3 3 2 R.BG R.κ * e) ^ 2 *
        blockWeight (lvTop N₁ R.m₁ k (rhoSep R.m₁)) (blockSites 3 3 N₁ R.m₁ (k + 1) k z)) *
        εR ^ 1)
      (fun D ξ => renC1On (lvTop N₁ R.m₁ k (rhoSep R.m₁)) (compWeight 3 1) ν e
        (blockSites 3 3 N₁ R.m₁ (k + 1) k z) D.Ψ D.h
        (bgFieldC (lvTop N₁ R.m₁ k (rhoSep R.m₁)) (compWeight 3 1) ν (bgC0 3 3 2) D) ξ) term := by
  have h := thm31g_C1_scale_of_towerG_at R.toG k hk N₁ (by simpa using h3N) hN hν0
    (by simpa using hν) he het hκa hεR z
  rw [rhoSepG_three] at h
  exact_mod_cast h


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
        (bgFieldC (lvTop N₁ R.m₁ k (rhoSep R.m₁)) (compWeight 3 1) ν (bgC0 3 3 2) D) ξ) term :=
  thm31g_C1_scale_of_tower_at R k hk N₁ h3N hN hν0 hν R.t_pos le_rfl hκa hεR z

/-- **Theorem 3.1 (g), `C₂(z)`, at every scale of the tower, at the class radius `e ≤ t`,
unconditional**: bound `(17/32) N (3 + A)(c_K K₂ B)² W(B_z) ε_R²`, `K_loc = 1`, `N = 2`,
`B = 8 e`, `A = K₁ ξ₁ e + c_K K₂ B r₀ + 2`, for the solution map `F` of
`IsRenSol … ν e e r₀ (8 e)`.  Only `locC2` is used. -/
theorem thm31g_C2_scale_of_tower_at {κmin : ℝ} (R : StepTowerRenSol κmin) (k : ℕ) (hk : 1 ≤ k)
    (N₁ : ℕ) [NeZero N₁] (h3N : 3 ∣ N₁) (hN : 5 < N₁) {ν : ℝ} (hν0 : 0 ≤ ν)
    (hν : ν * 3 ^ (2 * (k + 1)) ≤ 1) {e : ℝ} (he : 0 < e) (het : e ≤ R.t)
    {κa : ℝ} (hκa : κa ≤ 2 * R.κdec) {εR : ℝ}
    (hεR0 : 0 ≤ εR) (hεR : εR ≤ R.r₀) (z : Torus 3 (N₁ * 3 ^ R.m₁ * 3 ^ (k + 1 - (k + 1)))) :
    ∃ F : RawData 3 3 (N₁ * 3 ^ R.m₁) (k + 1) 2 × (Fin 3 → ℂ) →
        ((lvTop N₁ R.m₁ k (rhoSep R.m₁)).Ω 1 × Fin 2 → ℂ) ×
          ((lvTop N₁ R.m₁ k (rhoSep R.m₁)).Ω 1 → ℂ),
      IsRenSol (N := 2) (lvTop N₁ R.m₁ k (rhoSep R.m₁)) (compWeight 3 1) ν e e R.r₀
        (8 * e) F ∧
      ∃ term, IsLocExp (N := 2) (lvTop N₁ R.m₁ k (rhoSep R.m₁))
      (XiCOneReal (lvTop N₁ R.m₁ k (rhoSep R.m₁)) (compWeight 3 1) ν e) εR
      (renYs (renCube (lvTop N₁ R.m₁ k (rhoSep R.m₁))
          (X1 (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 1 k (fam 1 (blockSite k z))))
        (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 1
        (X1 (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 1 k (fam 1 (blockSite k z))))
      (renDY (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 1) κa
      (1 * (17 / 32 * ((2 : ℕ) * ((3 + (bgK1 3 3 2 * (xiC1 3 * e) +
        renCK 3 3 2 R.BG R.κ * cK2 3 3 2 * (8 * e) * R.r₀ + 2)) *
        (renCK 3 3 2 R.BG R.κ * cK2 3 3 2 * (8 * e)) ^ 2)) *
        blockWeight (lvTop N₁ R.m₁ k (rhoSep R.m₁)) (blockSites 3 3 N₁ R.m₁ (k + 1) k z)) *
        εR ^ 2)
      (fun D ξ => renC2On (lvTop N₁ R.m₁ k (rhoSep R.m₁)) (compWeight 3 1)
        (blockSites 3 3 N₁ R.m₁ (k + 1) k z) ξ (renMassU ν ξ)
        (bgMultC (lvTop N₁ R.m₁ k (rhoSep R.m₁)) (compWeight 3 1) ν (bgC0 3 3 2) D +
          (F ((D.Ψ, D.h), ξ)).2) (F ((D.Ψ, D.h), ξ)).1) term := by
  have h := thm31g_C2_scale_of_towerG_at R.toG k hk N₁ (by simpa using h3N) hN hν0
    (by simpa using hν) he het hκa hεR0 hεR z
  rw [rhoSepG_three] at h
  exact_mod_cast h


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
          (F ((D.Ψ, D.h), ξ)).2) (F ((D.Ψ, D.h), ξ)).1) term :=
  thm31g_C2_scale_of_tower_at R k hk N₁ h3N hN hν0 hν R.t_pos le_rfl hκa hεR0 hεR z

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
