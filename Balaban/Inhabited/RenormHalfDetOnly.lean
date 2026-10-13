/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.RenormRadiusInput
public import Balaban.Inhabited.RenormRadiusDec
public import Balaban.Inhabited.RenormE0FibreDetRadius
public import Balaban.Inhabited.RenFibreDatum
public import Balaban.Fluctuation.RenormExpInputOn

/-!
# The determinant-only renormalization record at class radius `t / 2` on the fibre

For `R : StepTowerTheta κmin` with `renDetFibreMin ≤ κmin` and `e = R.t / 2`, on the fibre
`Dom D := XiCOneReal G a ν e D ∧ (the field of D is the step's constant h₀)`:

* `renormDetOnlyZeroM_onFibre_half`: one solution map `F` of `IsRenSol … e e r₀ (8 e)`, its cut map
  with the endpoint identity, the record `RenormExpInputOn` whose energy function is the
  determinant summand `renE0θ_det e E` and whose observable and old terms are zero, the localized
  expansion of the determinant summand, its value at `ξ = 0`, a datum of the fibre, and the
  inclusion of the renormalized datum in the step chart of radius `t`;
* `renormDetOnlyZeroM_onFibre_half_C12`: Theorem 3.1 (g) `C₁`, `C₂` on the fibre for the same `F`.

**This is a determinant-only record with zero observable and zero old terms.  It is NOT the
physical record of Theorem 3.1 (g), (h): the marked energy and the observable are absent.**
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation
  Balaban.Localization Balaban.Localization.LevelPair Balaban.Localization.I5Inhabited
  Balaban.Polymer Balaban.SmallField.Def6 Balaban.Analysis Balaban.Inhabited.LevelStep LocalCover

/-- **Determinant-only record with zero observable and zero old terms, at class radius `t / 2`, on
the fibre.**  This is NOT the physical record of Theorem 3.1 (g), (h): the energy function of the
record is only the determinant summand `renE0θ_det`, the observable function and both old-term
differences are zero, and the marked energy and the observable are absent.  What is proved: one
solution map `F` with `IsRenSol`, a cut map `Fcut` whose value at `s = 1` is this `F`, the record
`RenormExpInputOn` on the fibre domain, the localized expansion of the determinant summand, its
value at `ξ = 0` at the step datum, that the step datum lies in the fibre, and that the
renormalized datum lies in the step chart of radius `t`. -/
theorem renormDetOnlyZeroM_onFibre_half {κmin : ℝ} (R : StepTowerTheta κmin)
    (hR : renDetFibreMin ≤ κmin) (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁] (h3N : 3 ∣ N₁)
    (hN : 5 < N₁) {ν : ℝ} (hν0 : 0 ≤ ν) (hν : ν * 3 ^ (2 * (k + 1)) ≤ 1) (β p₁ : ℝ)
    (Xcut : Set (CTorus 3 3 N₁ R.m₁ (k + 1))) :
    ∃ E : ∀ z : Torus 3 (N₁ * 3 ^ R.m₁ * 3 ^ (k + 1 - (k + 1))),
        DetExpansionLocC (R.toStepTower.step k hk N₁ ν β p₁) 1 z (2 * R.t)
          (towerDetRate R.κ) (towerDetConst R.κ),
    ∃ F : RawData 3 3 (N₁ * 3 ^ R.m₁) (k + 1) 2 × (Fin 3 → ℂ) →
        ((lvTop N₁ R.m₁ k (rhoSep R.m₁)).Ω 1 × Fin 2 → ℂ) ×
          ((lvTop N₁ R.m₁ k (rhoSep R.m₁)).Ω 1 → ℂ),
    ∃ Fcut : RawData 3 3 (N₁ * 3 ^ R.m₁) (k + 1) 2 × (Fin 3 → ℂ) →
        (RenLabel (lvTop N₁ R.m₁ k (rhoSep R.m₁)) Xcut → ℂ) →
        ((lvTop N₁ R.m₁ k (rhoSep R.m₁)).Ω 1 × Fin 2 → ℂ) ×
          ((lvTop N₁ R.m₁ k (rhoSep R.m₁)).Ω 1 → ℂ),
      IsRenSol (N := 2) (lvTop N₁ R.m₁ k (rhoSep R.m₁)) (compWeight 3 1) ν (R.t / 2) (R.t / 2)
        R.r₀ (8 * (R.t / 2)) F ∧
      AnalyticOnNhd ℂ (fun p : (RawData 3 3 (N₁ * 3 ^ R.m₁) (k + 1) 2 × (Fin 3 → ℂ)) ×
          (RenLabel (lvTop N₁ R.m₁ k (rhoSep R.m₁)) Xcut → ℂ) => Fcut p.1 p.2)
        (expDom (lvTop N₁ R.m₁ k (rhoSep R.m₁))
          (XiCOneReal (lvTop N₁ R.m₁ k (rhoSep R.m₁)) (compWeight 3 1) ν (R.t / 2)) R.r₀ ×ˢ
          polydisc (0 : RenLabel (lvTop N₁ R.m₁ k (rhoSep R.m₁)) Xcut → ℂ)
            (fun _ => Real.exp R.κ)) ∧
      (∀ D : BgData (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 2,
        XiCOneReal (lvTop N₁ R.m₁ k (rhoSep R.m₁)) (compWeight 3 1) ν (R.t / 2) D →
        ∀ ξ : Fin 3 → ℂ, ‖ξ‖ < R.r₀ → Fcut (rawOf D, ξ) 1 = F ((D.Ψ, D.h), ξ)) ∧
      RenormExpInputOn (N := 2) (lvTop N₁ R.m₁ k (rhoSep R.m₁)) (compWeight 3 1) ν (R.t / 2)
        R.r₀ (renCK 3 3 2 R.BG R.κ) (8 * (R.t / 2)) F
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
        (renDY (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 1) (3 / 2 * R.κdec) (3 / 2 * R.κdec) 1
        (hullConst 3 3 (towerDetRate R.κ) (towerDetConst R.κ) *
            Real.exp (c1 3 3 * Real.log 2) * Real.exp (hullRate 3 3 (towerDetRate R.κ)))
        0 0 0 (renE0θ_det (R.t / 2) E) (fun _ _ _ => 0) (fun _ _ _ => 0) (fun _ _ _ => 0)
        (fun D => XiCOneReal (R.toStepTower.step k hk N₁ ν β p₁).G'
            (R.toStepTower.step k hk N₁ ν β p₁).a (R.toStepTower.step k hk N₁ ν β p₁).ν
            (R.t / 2) D ∧
          ∀ x i, D.h x i = (((R.toStepTower.step k hk N₁ ν β p₁).h₀ i : ℝ) : ℂ)) ∧
      (∀ z : Torus 3 (N₁ * 3 ^ R.m₁ * 3 ^ (k + 1 - (k + 1))), ∃ term,
        IsLocExp (N := 2) (lvTop N₁ R.m₁ k (rhoSep R.m₁))
          (fun D => XiCOneReal (R.toStepTower.step k hk N₁ ν β p₁).G'
              (R.toStepTower.step k hk N₁ ν β p₁).a (R.toStepTower.step k hk N₁ ν β p₁).ν
              (R.t / 2) D ∧
            ∀ x i, D.h x i = (((R.toStepTower.step k hk N₁ ν β p₁).h₀ i : ℝ) : ℂ)) R.r₀
          (renYs (renCube (lvTop N₁ R.m₁ k (rhoSep R.m₁))
              (X1 (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 1 k (fam 1 (blockSite k z))))
            (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 1
            (X1 (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 1 k (fam 1 (blockSite k z))))
          (renDY (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 1) (3 / 2 * R.κdec)
          (hullConst 3 3 (towerDetRate R.κ) (towerDetConst R.κ) *
            Real.exp (c1 3 3 * Real.log 2) * Real.exp (hullRate 3 3 (towerDetRate R.κ)))
          (renE0θ_det (R.t / 2) E z) term) ∧
      (∀ z, renE0θ_det (R.t / 2) E z (R.toStepTower.step k hk N₁ ν β p₁).D' 0 =
        -(1 / 2 : ℂ) * ∑ y ∈ (R.toStepTower.step k hk N₁ ν β p₁).blockU z, ∑ i : Fin 2,
          (R.toStepTower.step k hk N₁ ν β p₁).logAC (y, i) (y, i)) ∧
      (XiCOneReal (R.toStepTower.step k hk N₁ ν β p₁).G'
          (R.toStepTower.step k hk N₁ ν β p₁).a (R.toStepTower.step k hk N₁ ν β p₁).ν
          (R.t / 2) (R.toStepTower.step k hk N₁ ν β p₁).D' ∧
        ∀ x i, (R.toStepTower.step k hk N₁ ν β p₁).D'.h x i =
          (((R.toStepTower.step k hk N₁ ν β p₁).h₀ i : ℝ) : ℂ)) ∧
      (∀ D : BgData (R.toStepTower.step k hk N₁ ν β p₁).G' 2,
        (XiCOneReal (R.toStepTower.step k hk N₁ ν β p₁).G'
            (R.toStepTower.step k hk N₁ ν β p₁).a (R.toStepTower.step k hk N₁ ν β p₁).ν
            (R.t / 2) D ∧
          ∀ x i, D.h x i = (((R.toStepTower.step k hk N₁ ν β p₁).h₀ i : ℝ) : ℂ)) →
        ∀ ξ : Fin 3 → ℂ, ‖ξ‖ < R.r₀ →
          XiCData (R.toStepTower.step k hk N₁ ν β p₁).G'
            (R.toStepTower.step k hk N₁ ν β p₁).a (R.toStepTower.step k hk N₁ ν β p₁).ν
            (k + 1) 1 R.t (renThetaDatum (R.toStepTower.step k hk N₁ ν β p₁) (R.t / 2) D ξ)) := by
  have ht := R.t_pos
  have he : 0 < R.t / 2 := by positivity
  have het : R.t / 2 ≤ R.t := by linarith
  have hκ : 0 ≤ R.κdec := by have := R.κdec_lower; have := R.κ0_nonneg; linarith
  have hκa : 3 / 2 * R.κdec ≤ 2 * R.κdec := by linarith
  obtain ⟨F, hF, h1, h2, h3⟩ :=
    renLoc_fields_scale_of_tower_at R.toStepTowerRenSol k hk N₁ h3N hN hν0 hν he het hκa hκa
  obtain ⟨Fcut, hFa, hFe⟩ := renDec_one_unique_sharp_scale_of_tower_at R.toStepTowerRenEnd k hk
    N₁ hN hν0 hν he het Xcut hF le_rfl
  obtain ⟨E, hE0, hE⟩ := expE0_det_scale_of_tower_at R hR he het k hk N₁ h3N hN hν0 hν β p₁
  have hsub : ∀ D : BgData (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 2,
      (XiCOneReal (R.toStepTower.step k hk N₁ ν β p₁).G'
          (R.toStepTower.step k hk N₁ ν β p₁).a (R.toStepTower.step k hk N₁ ν β p₁).ν
          (R.t / 2) D ∧
        ∀ x i, D.h x i = (((R.toStepTower.step k hk N₁ ν β p₁).h₀ i : ℝ) : ℂ)) →
      XiCOneReal (lvTop N₁ R.m₁ k (rhoSep R.m₁)) (compWeight 3 1) ν (R.t / 2) D :=
    fun D hD => hD.1
  have hE' := fun z => (hE z).imp fun _ h => h.mono_dom hsub
  have hD' := exists_xiCOneReal_fibre_step R.toStepTower k hk N₁ ν β p₁ hν0 hν he
  refine ⟨E, F, Fcut, hF, hFa, hFe, ?_, hE', hE0, hD', ?_⟩
  · exact renormExpInputOn_zero_of_fields hsub h1 h2 hE' h3 (fun _ => ⟨_, isLocExp_zero_cover _ _⟩)
  · intro D hD ξ hξ
    exact R.renDatum_half_mem_xiCData k hk N₁ hν0 hν β p₁ D hD.1 ξ hξ

/-- **`C₁` and `C₂` of Theorem 3.1 (g) on the fibre, for the solution map of the determinant-only
record at class radius `t / 2`.**  As for `renormDetOnlyZeroM_onFibre_half`, the record used is
determinant-only with zero observable and zero old terms; it is NOT the physical record.  The
solution map `F` is the one of the endpoint identity and of the record, and the `C₂` expansion is
that of this `F`.  Constants: `C₁`: `9 (c_K e)² W(B_z) ε_R`; `C₂`: `(17/32) · 2 · (3 + A)
(c_K c_{K2} B)² W(B_z) ε_R²`, with `e = t / 2`, `B = 8 e`. -/
theorem renormDetOnlyZeroM_onFibre_half_C12 {κmin : ℝ} (R : StepTowerTheta κmin)
    (hR : renDetFibreMin ≤ κmin) (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁] (h3N : 3 ∣ N₁)
    (hN : 5 < N₁) {ν : ℝ} (hν0 : 0 ≤ ν) (hν : ν * 3 ^ (2 * (k + 1)) ≤ 1) (β p₁ : ℝ)
    (Xcut : Set (CTorus 3 3 N₁ R.m₁ (k + 1))) :
    ∃ F : RawData 3 3 (N₁ * 3 ^ R.m₁) (k + 1) 2 × (Fin 3 → ℂ) →
        ((lvTop N₁ R.m₁ k (rhoSep R.m₁)).Ω 1 × Fin 2 → ℂ) ×
          ((lvTop N₁ R.m₁ k (rhoSep R.m₁)).Ω 1 → ℂ),
    ∃ Fcut : RawData 3 3 (N₁ * 3 ^ R.m₁) (k + 1) 2 × (Fin 3 → ℂ) →
        (RenLabel (lvTop N₁ R.m₁ k (rhoSep R.m₁)) Xcut → ℂ) →
        ((lvTop N₁ R.m₁ k (rhoSep R.m₁)).Ω 1 × Fin 2 → ℂ) ×
          ((lvTop N₁ R.m₁ k (rhoSep R.m₁)).Ω 1 → ℂ),
      IsRenSol (N := 2) (lvTop N₁ R.m₁ k (rhoSep R.m₁)) (compWeight 3 1) ν (R.t / 2) (R.t / 2)
        R.r₀ (8 * (R.t / 2)) F ∧
      (∀ D : BgData (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 2,
        XiCOneReal (lvTop N₁ R.m₁ k (rhoSep R.m₁)) (compWeight 3 1) ν (R.t / 2) D →
        ∀ ξ : Fin 3 → ℂ, ‖ξ‖ < R.r₀ → Fcut (rawOf D, ξ) 1 = F ((D.Ψ, D.h), ξ)) ∧
      ∀ (z : Torus 3 (N₁ * 3 ^ R.m₁ * 3 ^ (k + 1 - (k + 1)))) (εR : ℝ), 0 ≤ εR → εR ≤ R.r₀ →
        (∃ term, IsLocExp (N := 2) (lvTop N₁ R.m₁ k (rhoSep R.m₁))
          (fun D => XiCOneReal (R.toStepTower.step k hk N₁ ν β p₁).G'
              (R.toStepTower.step k hk N₁ ν β p₁).a (R.toStepTower.step k hk N₁ ν β p₁).ν
              (R.t / 2) D ∧
            ∀ x i, D.h x i = (((R.toStepTower.step k hk N₁ ν β p₁).h₀ i : ℝ) : ℂ)) εR
          (renYs (renCube (lvTop N₁ R.m₁ k (rhoSep R.m₁))
              (X1 (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 1 k (fam 1 (blockSite k z))))
            (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 1
            (X1 (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 1 k (fam 1 (blockSite k z))))
          (renDY (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 1) (3 / 2 * R.κdec)
          (1 * ((3 + 6) * (renCK 3 3 2 R.BG R.κ * (R.t / 2)) ^ 2 *
            blockWeight (lvTop N₁ R.m₁ k (rhoSep R.m₁))
              (blockSites 3 3 N₁ R.m₁ (k + 1) k z)) * εR ^ 1)
          (fun D ξ => renC1On (lvTop N₁ R.m₁ k (rhoSep R.m₁)) (compWeight 3 1) ν (R.t / 2)
            (blockSites 3 3 N₁ R.m₁ (k + 1) k z) D.Ψ D.h
            (bgFieldC (lvTop N₁ R.m₁ k (rhoSep R.m₁)) (compWeight 3 1) ν (bgC0 3 3 2) D) ξ)
          term) ∧
        (∃ term, IsLocExp (N := 2) (lvTop N₁ R.m₁ k (rhoSep R.m₁))
          (fun D => XiCOneReal (R.toStepTower.step k hk N₁ ν β p₁).G'
              (R.toStepTower.step k hk N₁ ν β p₁).a (R.toStepTower.step k hk N₁ ν β p₁).ν
              (R.t / 2) D ∧
            ∀ x i, D.h x i = (((R.toStepTower.step k hk N₁ ν β p₁).h₀ i : ℝ) : ℂ)) εR
          (renYs (renCube (lvTop N₁ R.m₁ k (rhoSep R.m₁))
              (X1 (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 1 k (fam 1 (blockSite k z))))
            (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 1
            (X1 (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 1 k (fam 1 (blockSite k z))))
          (renDY (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 1) (3 / 2 * R.κdec)
          (1 * (17 / 32 * ((2 : ℕ) * ((3 + (bgK1 3 3 2 * (xiC1 3 * (R.t / 2)) +
            renCK 3 3 2 R.BG R.κ * cK2 3 3 2 * (8 * (R.t / 2)) * R.r₀ + 2)) *
            (renCK 3 3 2 R.BG R.κ * cK2 3 3 2 * (8 * (R.t / 2))) ^ 2)) *
            blockWeight (lvTop N₁ R.m₁ k (rhoSep R.m₁))
              (blockSites 3 3 N₁ R.m₁ (k + 1) k z)) * εR ^ 2)
          (fun D ξ => renC2On (lvTop N₁ R.m₁ k (rhoSep R.m₁)) (compWeight 3 1)
            (blockSites 3 3 N₁ R.m₁ (k + 1) k z) ξ (renMassU ν ξ)
            (bgMultC (lvTop N₁ R.m₁ k (rhoSep R.m₁)) (compWeight 3 1) ν (bgC0 3 3 2) D +
              (F ((D.Ψ, D.h), ξ)).2) (F ((D.Ψ, D.h), ξ)).1) term) := by
  obtain ⟨E, F, Fcut, hF, hFa, hFe, I, -⟩ :=
    renormDetOnlyZeroM_onFibre_half R hR k hk N₁ h3N hN hν0 hν β p₁ Xcut
  have ht := R.t_pos
  have he : 0 < R.t / 2 := by positivity
  have het : R.t / 2 ≤ R.t := by linarith
  have hC := R.flCore_scale_mono k hk N₁ hN hν0 hν he het he het
  have hHB := bgHyp_lv (k := k) R.m₁ hν0 hν
  refine ⟨F, Fcut, hF, hFe, fun z εR hεR0 hεR => ⟨?_, ?_⟩⟩
  · exact thm31g_C1_on hHB he hC.small1 (hC.c7le.trans (c7_le_bgC1 3 3 2 R.BG R.κ)) R.r₀_le I
      zero_le_one R.toStepTowerRen.renCK_facts.1 hεR z
  · exact thm31g_C2_on hHB he R.r₀_le I zero_le_one (by positivity)
      R.toStepTowerRen.renCK_facts.1 hεR0 hεR z

end Balaban.Inhabited
