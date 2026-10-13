/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.RenormRadiusLoc
public import Balaban.Fluctuation.LocExpUnion

/-!
# The three localization principles of the renormalization record on a larger index family

The classes of the three localization principles `locC1`, `locC2`, `locDφ` at the tower are
nonempty at every datum of the class domain `XiCOneReal` and every `ξ` of the polydisc:

* the class `bgClass ν (c_K e)` contains the background field `bgFieldC` (it lies in
  `bgClass ν (2 e)`, and `2 ≤ c_K`);
* the class `pertClass` contains the pair `(δφ, bgMultC + δα)` of the solution map;
* the class `{v | SupBounds v (c_K K₂ B ‖ξ‖)}` contains the first component of the solution map.

With this, the three principles of `renLoc_fields_scale_of_tower_at` extend to every larger family
of index sets (`HasLocPrinciple.extend`), in particular to the union of the family `renYs` with the
site domains.
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation
  Balaban.Localization Balaban.Localization.LevelPair Balaban.Localization.I5Inhabited
  Balaban.Polymer Balaban.SmallField.Def6 Balaban.Analysis Balaban.Inhabited.LevelStep LocalCover

/-- **The class of `locC1` is nonempty** at every datum of `XiCOneReal` at the class radius
`e ≤ t`: it contains the background field. -/
theorem renLocC1_class_nonempty {κmin : ℝ} (R : StepTowerRenSol κmin) (k : ℕ) (hk : 1 ≤ k)
    (N₁ : ℕ) [NeZero N₁] (hN : 5 < N₁) {ν : ℝ} (hν0 : 0 ≤ ν)
    (hν : ν * 3 ^ (2 * (k + 1)) ≤ 1) {e : ℝ} (he : 0 < e) (het : e ≤ R.t)
    (D : BgData (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 2)
    (hD : XiCOneReal (lvTop N₁ R.m₁ k (rhoSep R.m₁)) (compWeight 3 1) ν e D) :
    (bgClass (lvTop N₁ R.m₁ k (rhoSep R.m₁)) ν (renCK 3 3 2 R.BG R.κ * e) D).Nonempty := by
  have hC := R.toStepTower.flCore_scale_of_le k hk N₁ hN hν0 hν he het he het
  have hc1 : xiC1 3 * e ≤ bgC1 3 3 2 := hC.c7le.trans (c7_le_bgC1 3 3 2 _ _)
  have hK4 := (K4_pos (d := 3) (L := 3) (N := 2) (κ := R.κ) hC.hS.fam.2.1 (by norm_num)).le
  have hC1pos : 0 < xiC1 3 := by unfold xiC1; positivity
  have hck : 2 ≤ renCK 3 3 2 R.BG R.κ := by
    have := renCK_ge (d := 3) (L := 3) (N := 2) (BG := R.BG) (κ := R.κ)
    nlinarith [mul_nonneg hK4 hC1pos.le]
  exact ⟨_, bgClass_mono (by positivity) (mul_le_mul_of_nonneg_right hck he.le) D
    (XiCOneReal.mem_bgClass hC.HBp he hC.small1 hc1 hD)⟩

/-- **The class of `locC2` is nonempty** at every datum of `XiCOneReal` and every `ξ` with
`‖ξ‖ < r₀`: it contains `(δφ, bgMultC + δα)` of the solution map `F`. -/
theorem renLocC2_class_nonempty {κmin : ℝ} (R : StepTowerRenSol κmin) (k : ℕ) (hk : 1 ≤ k)
    (N₁ : ℕ) [NeZero N₁] (hN : 5 < N₁) {ν : ℝ} (hν0 : 0 ≤ ν)
    (hν : ν * 3 ^ (2 * (k + 1)) ≤ 1) {e : ℝ} (he : 0 < e) (het : e ≤ R.t)
    {F : RawData 3 3 (N₁ * 3 ^ R.m₁) (k + 1) 2 × (Fin 3 → ℂ) →
      ((lvTop N₁ R.m₁ k (rhoSep R.m₁)).Ω 1 × Fin 2 → ℂ) ×
        ((lvTop N₁ R.m₁ k (rhoSep R.m₁)).Ω 1 → ℂ)}
    (hF : IsRenSol (N := 2) (lvTop N₁ R.m₁ k (rhoSep R.m₁)) (compWeight 3 1) ν e e R.r₀
      (8 * e) F)
    (D : BgData (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 2)
    (hD : XiCOneReal (lvTop N₁ R.m₁ k (rhoSep R.m₁)) (compWeight 3 1) ν e D)
    (ξ : Fin 3 → ℂ) (hξ : ‖ξ‖ < R.r₀) :
    ((fun (_ : BgData (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 2) (ξ : Fin 3 → ℂ) =>
      pertClass (N := 2) (lvTop N₁ R.m₁ k (rhoSep R.m₁))
        (renCK 3 3 2 R.BG R.κ * (cK2 3 3 2 * (8 * e * ‖ξ‖)))
        (bgK1 3 3 2 * (xiC1 3 * e) + renCK 3 3 2 R.BG R.κ * cK2 3 3 2 * (8 * e) * R.r₀ + 2)
        (renMassU ν ξ)) D ξ).Nonempty := by
  have hC := R.toStepTower.flCore_scale_of_le k hk N₁ hN hν0 hν he het he het
  have hc1 : xiC1 3 * e ≤ bgC1 3 3 2 := hC.c7le.trans (c7_le_bgC1 3 3 2 _ _)
  obtain ⟨hcK, -⟩ := R.toStepTowerRen.renCK_facts_at he.le
  have h := renSol_mem_pertClass hC.HBp he hC.small1 hc1 hF (by positivity) hcK le_rfl
    R.r₀_le hD.xiCOne hξ
  exact ⟨_, h⟩

/-- **The class of `locDφ` is nonempty**: it contains `δφ` of the solution map `F`. -/
theorem renLocDphi_class_nonempty {κmin : ℝ} (R : StepTowerRenSol κmin) (k : ℕ)
    (N₁ : ℕ) [NeZero N₁] {ν : ℝ} {e : ℝ} (he : 0 < e)
    {F : RawData 3 3 (N₁ * 3 ^ R.m₁) (k + 1) 2 × (Fin 3 → ℂ) →
      ((lvTop N₁ R.m₁ k (rhoSep R.m₁)).Ω 1 × Fin 2 → ℂ) ×
        ((lvTop N₁ R.m₁ k (rhoSep R.m₁)).Ω 1 → ℂ)}
    (hF : IsRenSol (N := 2) (lvTop N₁ R.m₁ k (rhoSep R.m₁)) (compWeight 3 1) ν e e R.r₀
      (8 * e) F)
    (D : BgData (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 2)
    (hD : XiCOneReal (lvTop N₁ R.m₁ k (rhoSep R.m₁)) (compWeight 3 1) ν e D)
    (ξ : Fin 3 → ℂ) (hξ : ‖ξ‖ < R.r₀) :
    {v : (lvTop N₁ R.m₁ k (rhoSep R.m₁)).Ω 1 × Fin 2 → ℂ |
      SupBounds (lvTop N₁ R.m₁ k (rhoSep R.m₁)) v
        (renCK 3 3 2 R.BG R.κ * (cK2 3 3 2 * (8 * e * ‖ξ‖)))}.Nonempty := by
  obtain ⟨hcK, -⟩ := R.toStepTowerRen.renCK_facts_at he.le
  have hK2 := cK2_pos 3 3 2
  have h0 : 0 ≤ cK2 3 3 2 * (8 * e * ‖ξ‖) := by positivity
  exact ⟨_, (hF.sup D hD.xiCOne ξ hξ).mono (by nlinarith)⟩

/-- **The three localization principles on a larger family of index sets.**  The conclusion of
`renLoc_fields_scale_of_tower_at` with `renYs …` replaced by `renYs … ∪ S`, for any finite family
`S` of finsets of sites (for instance the site domains), with the same solution map `F`, domain,
radius, size, rates and `K_loc = 1`. -/
theorem renLoc_fields_union_scale_of_tower_at {κmin : ℝ} (R : StepTowerRenSol κmin) (k : ℕ)
    (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁] (h3N : 3 ∣ N₁) (hN : 5 < N₁) {ν : ℝ} (hν0 : 0 ≤ ν)
    (hν : ν * 3 ^ (2 * (k + 1)) ≤ 1) {e : ℝ} (he : 0 < e) (het : e ≤ R.t)
    {κa κb : ℝ} (hκa : κa ≤ 2 * R.κdec) (hκb : κb ≤ 2 * R.κdec)
    (S : Finset (Finset (Torus 3 (N₁ * 3 ^ R.m₁ * 3 ^ (k + 1))))) :
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
            (X1 (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 1 k (fam 1 (blockSite k z))) ∪ S)
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
            (X1 (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 1 k (fam 1 (blockSite k z))) ∪ S)
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
              (fam 1 (p.1 : CTorus 3 3 N₁ R.m₁ (k + 1)))) ∪ S)
          (renDY (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 1) κb 1
          (fun _ ξ => {v | SupBounds (lvTop N₁ R.m₁ k (rhoSep R.m₁)) v
            (renCK 3 3 2 R.BG R.κ * (cK2 3 3 2 * (8 * e * ‖ξ‖)))})
          (fun _ v _ => v p) (fun D ξ => (F ((D.Ψ, D.h), ξ)).1)) := by
  obtain ⟨F, hF, h1, h2, h3⟩ :=
    renLoc_fields_scale_of_tower_at R k hk N₁ h3N hN hν0 hν he het hκa hκb
  refine ⟨F, hF, fun z => ?_, fun z => ?_, fun p => ?_⟩
  · exact (h1 z).extend Finset.subset_union_left zero_le_one fun D hD _ _ =>
      renLocC1_class_nonempty R k hk N₁ hN hν0 hν he het D hD
  · exact (h2 z).extend Finset.subset_union_left zero_le_one fun D hD ξ hξ =>
      renLocC2_class_nonempty R k hk N₁ hN hν0 hν he het hF D hD ξ hξ
  · exact (h3 p).extend Finset.subset_union_left zero_le_one fun D hD ξ hξ =>
      renLocDphi_class_nonempty R k N₁ he hF D hD ξ hξ

end Balaban.Inhabited
