/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.RenormE1SiteRecord
public import Balaban.Inhabited.RenormM0SiteRecord
public import Balaban.Inhabited.RenJoinClassWitness
public import Balaban.Fluctuation.RenormExpInputOn
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The physical renormalization record of the zero class on the fibre at class radius `t / 2`

For a tower with renormalization data `R`, a mark family `cE z` (one for every root `z`) and an
observable family `cM y i` (one for every site and component), each with analyticity, exact
locality on `sitesOf T`, the bound, the support and the value identity at every chart datum with
constant field, the physical marked energy `E₀` and the rescaled observable `β_U^{-1/2} M₀` at the
renormalized datum are localized expansions over `renYs ∪ site sets`, and together with the three
localization principles on the same index families (same solution map) they form a
`RenormExpInputOn` record with zero old terms.  The four consumers of Theorem 3.1 (g), (h) then
apply.

Nothing is assumed about the tower's own families; exact locality is a hypothesis on them.
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation
  Balaban.Localization Balaban.Localization.LevelPair Balaban.Localization.I5Inhabited
  Balaban.Polymer Balaban.SmallField.Def6 Balaban.Analysis Balaban.Inhabited.LevelStep LocalCover

open Classical in
/-- Choose the renormalized solution and cut map once, then form the physical record for any
source whose observable value identity is supplied. -/
private theorem renormPhysicalZero_onFibre_half_core_of_source_value {κmin : ℝ} (R : StepTowerTheta κmin)
    (hR : renDetFibreMin ≤ κmin) (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁] (h3N : 3 ∣ N₁)
    (hN : 5 < N₁) {ν : ℝ} (hν0 : 0 ≤ ν) (hν : ν * 3 ^ (2 * (k + 1)) ≤ 1) (β p₁ : ℝ)
    (hβ : 0 < β) (Xcut : Set (CTorus 3 3 N₁ R.m₁ (k + 1)))
    (q : ℝ) (hq : q ≤ 1)
    {κ B κM BM : ℝ} (hB : 0 ≤ B) (hBM : 0 ≤ BM)
    (cE : Torus 3 (N₁ * 3 ^ R.m₁ * 3 ^ (k + 1 - (k + 1))) →
      physParam 2 (R.toStepTower.step k hk N₁ ν β p₁) → Finset (CubeB (d := 3) (L := 3) (N₁ := N₁) (m₁ := R.m₁) (K := k + 1) 1 (k + 1) Set.univ) → ℂ)
    (cM : CTorus 3 3 N₁ R.m₁ (k + 1) → Fin 2 →
      physParam 2 (R.toStepTower.step k hk N₁ ν β p₁) → Finset (CubeB (d := 3) (L := 3) (N₁ := N₁) (m₁ := R.m₁) (K := k + 1) 1 (k + 1) Set.univ) → ℂ)
    (hanE : ∀ (z : Torus 3 (N₁ * 3 ^ R.m₁ * 3 ^ (k + 1 - (k + 1)))), ∀ T, AnalyticOnNhd ℂ (fun θ => cE z θ T) (physV (R.toStepTower.step k hk N₁ ν β p₁) (R.toStepTower.step k hk N₁ ν β p₁).a₁ (R.toStepTower.step k hk N₁ ν β p₁).ν R.t))
    (hlocE : ∀ (z : Torus 3 (N₁ * 3 ^ R.m₁ * 3 ^ (k + 1 - (k + 1)))), ∀ T, ∀ θ ∈ (physV (R.toStepTower.step k hk N₁ ν β p₁) (R.toStepTower.step k hk N₁ ν β p₁).a₁ (R.toStepTower.step k hk N₁ ν β p₁).ν R.t),
      ∀ θ' ∈ (physV (R.toStepTower.step k hk N₁ ν β p₁) (R.toStepTower.step k hk N₁ ν β p₁).a₁ (R.toStepTower.step k hk N₁ ν β p₁).ν R.t),
      physRestrict (sitesOf T) (physIncl 2 (R.toStepTower.step k hk N₁ ν β p₁) θ) =
        physRestrict (sitesOf T) (physIncl 2 (R.toStepTower.step k hk N₁ ν β p₁) θ') →
        cE z θ T = cE z θ' T)
    (hbdE : ∀ (z : Torus 3 (N₁ * 3 ^ R.m₁ * 3 ^ (k + 1 - (k + 1)))), ∀ θ ∈ (physV (R.toStepTower.step k hk N₁ ν β p₁) (R.toStepTower.step k hk N₁ ν β p₁).a₁ (R.toStepTower.step k hk N₁ ν β p₁).ν R.t),
      ∀ T, IsPolyDom 1 (k + 1) (sitesOf T) → ‖cE z θ T‖ ≤ B * Real.exp (-κ * dExt T))
    (hsuppE : ∀ (z : Torus 3 (N₁ * 3 ^ R.m₁ * 3 ^ (k + 1 - (k + 1)))), ∀ θ ∈ (physV (R.toStepTower.step k hk N₁ ν β p₁) (R.toStepTower.step k hk N₁ ν β p₁).a₁ (R.toStepTower.step k hk N₁ ν β p₁).ν R.t),
      ∀ T, cE z θ T ≠ 0 → IsPolyDom 1 (k + 1) (sitesOf T))
    (hvalE : ∀ (z : Torus 3 (N₁ * 3 ^ R.m₁ * 3 ^ (k + 1 - (k + 1)))), ∀ (D' : BgData (R.toStepTower.step k hk N₁ ν β p₁).G' 2)
        (hDh : ∀ y i, D'.h y i = ((R.toStepTower.step k hk N₁ ν β p₁).h₀ i : ℂ)),
      XiCData (R.toStepTower.step k hk N₁ ν β p₁).G' (R.toStepTower.step k hk N₁ ν β p₁).a
        (R.toStepTower.step k hk N₁ ν β p₁).ν (k + 1) 1 R.t D' →
      ((R.toStepTower.step k hk N₁ ν β p₁).withDatum D' hDh).E1locC
          (zeroClass 3 3 N₁ R.m₁ k 2 (rhoSep R.m₁)) z =
        ∑ C, cE z (⟨rawOf D', rawOf_mem_rawSub _⟩, (0 : CTorus 3 3 N₁ R.m₁ (k + 1) → Fin 2 → ℂ)) C)
    (hanM : ∀ (y : CTorus 3 3 N₁ R.m₁ (k + 1)) (i : Fin 2), ∀ T, AnalyticOnNhd ℂ (fun θ => cM y i θ T) (physV (R.toStepTower.step k hk N₁ ν β p₁) (R.toStepTower.step k hk N₁ ν β p₁).a₁ (R.toStepTower.step k hk N₁ ν β p₁).ν R.t))
    (hlocM : ∀ (y : CTorus 3 3 N₁ R.m₁ (k + 1)) (i : Fin 2), ∀ T, ∀ θ ∈ (physV (R.toStepTower.step k hk N₁ ν β p₁) (R.toStepTower.step k hk N₁ ν β p₁).a₁ (R.toStepTower.step k hk N₁ ν β p₁).ν R.t),
      ∀ θ' ∈ (physV (R.toStepTower.step k hk N₁ ν β p₁) (R.toStepTower.step k hk N₁ ν β p₁).a₁ (R.toStepTower.step k hk N₁ ν β p₁).ν R.t),
      physRestrict (sitesOf T) (physIncl 2 (R.toStepTower.step k hk N₁ ν β p₁) θ) =
        physRestrict (sitesOf T) (physIncl 2 (R.toStepTower.step k hk N₁ ν β p₁) θ') →
        cM y i θ T = cM y i θ' T)
    (hbdM : ∀ (y : CTorus 3 3 N₁ R.m₁ (k + 1)) (i : Fin 2), ∀ θ ∈ (physV (R.toStepTower.step k hk N₁ ν β p₁) (R.toStepTower.step k hk N₁ ν β p₁).a₁ (R.toStepTower.step k hk N₁ ν β p₁).ν R.t),
      ∀ T, IsPolyDom 1 (k + 1) (sitesOf T) → ‖cM y i θ T‖ ≤ BM * Real.exp (-κM * dExt T))
    (hsuppM : ∀ (y : CTorus 3 3 N₁ R.m₁ (k + 1)) (i : Fin 2), ∀ θ ∈ (physV (R.toStepTower.step k hk N₁ ν β p₁) (R.toStepTower.step k hk N₁ ν β p₁).a₁ (R.toStepTower.step k hk N₁ ν β p₁).ν R.t),
      ∀ T, cM y i θ T ≠ 0 → IsPolyDom 1 (k + 1) (sitesOf T))
    : ∃ F : RawData 3 3 (N₁ * 3 ^ R.m₁) (k + 1) 2 × (Fin 3 → ℂ) →
        (((lvTop N₁ R.m₁ k (rhoSep R.m₁))).Ω 1 × Fin 2 → ℂ) ×
          (((lvTop N₁ R.m₁ k (rhoSep R.m₁))).Ω 1 → ℂ),
    ∃ Fcut : RawData 3 3 (N₁ * 3 ^ R.m₁) (k + 1) 2 × (Fin 3 → ℂ) →
        (RenLabel (lvTop N₁ R.m₁ k (rhoSep R.m₁)) Xcut → ℂ) →
        (((lvTop N₁ R.m₁ k (rhoSep R.m₁))).Ω 1 × Fin 2 → ℂ) ×
          (((lvTop N₁ R.m₁ k (rhoSep R.m₁))).Ω 1 → ℂ),
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
      ∀ (g : Fld 3 3 N₁ R.m₁ (k + 1) 2), (∑ x, ∑ j, ‖g x j‖) < q →
        (∀ (y : CTorus 3 3 N₁ R.m₁ (k + 1)) (i : Fin 2), ∀ (D' : BgData (R.toStepTower.step k hk N₁ ν β p₁).G' 2)
        (hDh : ∀ y i, D'.h y i = ((R.toStepTower.step k hk N₁ ν β p₁).h₀ i : ℂ)),
      XiCData (R.toStepTower.step k hk N₁ ν β p₁).G' (R.toStepTower.step k hk N₁ ν β p₁).a
        (R.toStepTower.step k hk N₁ ν β p₁).ν (k + 1) 1 R.t D' →
      ((R.toStepTower.step k hk N₁ ν β p₁).withDatum D' hDh).M0C
          (zeroClass 3 3 N₁ R.m₁ k 2 (rhoSep R.m₁)) g y i =
        ((((R.toStepTower.step k hk N₁ ν β p₁).betaU ^ (1 / 2 : ℝ) : ℝ) : ℂ)) *
          ∑ C, cM y i (⟨rawOf D', rawOf_mem_rawSub _⟩, g) C) →
      RenormExpInputOn (N := 2) (lvTop N₁ R.m₁ k (rhoSep R.m₁)) (compWeight 3 1) ν (R.t / 2)
        R.r₀ (renCK 3 3 2 R.BG R.κ) (8 * (R.t / 2)) F
        (fun z : Torus 3 (N₁ * 3 ^ R.m₁ * 3 ^ (k + 1 - (k + 1))) =>
          blockSites 3 3 N₁ R.m₁ (k + 1) k z)
        (fun z => renYs (renCube (lvTop N₁ R.m₁ k (rhoSep R.m₁))
          (X1 (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 1 k (fam 1 (blockSite k z)))) (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 1
          (X1 (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 1 k (fam 1 (blockSite k z))) ∪ (Finset.univ.image fun T : Finset (CubeB (d := 3) (L := 3) (N₁ := N₁) (m₁ := R.m₁) (K := k + 1) 1 (k + 1) Set.univ) =>
        (Finset.univ.filter fun x : CTorus 3 3 N₁ R.m₁ (k + 1) => x ∈ sitesOf T)))
        (fun p => renYs (renCube (lvTop N₁ R.m₁ k (rhoSep R.m₁))
          (X1 (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 1 k (fam 1 (p.1 : CTorus 3 3 N₁ R.m₁ (k + 1))))) (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 1
          (X1 (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 1 k (fam 1 (p.1 : CTorus 3 3 N₁ R.m₁ (k + 1)))) ∪ (Finset.univ.image fun T : Finset (CubeB (d := 3) (L := 3) (N₁ := N₁) (m₁ := R.m₁) (K := k + 1) 1 (k + 1) Set.univ) =>
        (Finset.univ.filter fun x : CTorus 3 3 N₁ R.m₁ (k + 1) => x ∈ sitesOf T)))
        (renDY (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 1) (min (3 / 2 * R.κdec) (min κ κM)) (min (3 / 2 * R.κdec) (min κ κM)) 1
        (hullConst 3 3 (towerDetRate R.κ) (towerDetConst R.κ) *
            Real.exp (c1 3 3 * Real.log 2) * Real.exp (hullRate 3 3 (towerDetRate R.κ)) + B)
        0 BM 0 (fun (z : Torus 3 (N₁ * 3 ^ R.m₁ * 3 ^ (k + 1 - (k + 1)))) (D : BgData (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 2) (ξ : Fin 3 → ℂ) =>
          if hD : ∀ x i, D.h x i = ((((R.toStepTower.step k hk N₁ ν β p₁).h₀ i : ℝ)) : ℂ)
          then ((R.toStepTower.step k hk N₁ ν β p₁).withDatum
            (renThetaDatum (R.toStepTower.step k hk N₁ ν β p₁) (R.t / 2) D ξ) hD).E0locC
              (zeroClass 3 3 N₁ R.m₁ k 2 (rhoSep R.m₁)) z else 0) (fun _ _ _ => 0) (fun (p : ((lvTop N₁ R.m₁ k (rhoSep R.m₁))).Ω 1 × Fin 2) (D : BgData (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 2) (ξ : Fin 3 → ℂ) =>
          if hD : ∀ x i, D.h x i = ((((R.toStepTower.step k hk N₁ ν β p₁).h₀ i : ℝ)) : ℂ)
          then (((((R.toStepTower.step k hk N₁ ν β p₁).betaU ^ (1 / 2 : ℝ) : ℝ) : ℂ)))⁻¹ *
            ((R.toStepTower.step k hk N₁ ν β p₁).withDatum
              (renThetaDatum (R.toStepTower.step k hk N₁ ν β p₁) (R.t / 2) D ξ) hD).M0C
                (zeroClass 3 3 N₁ R.m₁ k 2 (rhoSep R.m₁)) g (p.1 : CTorus 3 3 N₁ R.m₁ (k + 1)) p.2
          else 0) (fun _ _ _ => 0)
        (fun D => XiCOneReal (R.toStepTower.step k hk N₁ ν β p₁).G'
            (R.toStepTower.step k hk N₁ ν β p₁).a (R.toStepTower.step k hk N₁ ν β p₁).ν
            (R.t / 2) D ∧
          ∀ x i, D.h x i = ((((R.toStepTower.step k hk N₁ ν β p₁).h₀ i : ℝ)) : ℂ)) := by
  have ht := R.t_pos
  have he : 0 < R.t / 2 := by positivity
  have het : R.t / 2 ≤ R.t := by linarith
  have hκ : 0 ≤ R.κdec := by have := R.κdec_lower; have := R.κ0_nonneg; linarith
  have hκa : min (3 / 2 * R.κdec) (min κ κM) ≤ 2 * R.κdec :=
    (min_le_left _ _).trans (by linarith)
  obtain ⟨F, hF, h1, h2, h3⟩ := renLoc_fields_union_scale_of_tower_at R.toStepTowerRenSol k hk N₁
    h3N hN hν0 hν he het hκa hκa
    (Finset.univ.image fun T : Finset (CubeB (d := 3) (L := 3) (N₁ := N₁) (m₁ := R.m₁)
      (K := k + 1) 1 (k + 1) Set.univ) =>
        (Finset.univ.filter fun x : CTorus 3 3 N₁ R.m₁ (k + 1) => x ∈ sitesOf T))
  obtain ⟨Fcut, hFa, hFe⟩ := renDec_one_unique_sharp_scale_of_tower_at R.toStepTowerRenEnd k hk
    N₁ hN hν0 hν he het Xcut hF le_rfl
  have hsub : ∀ D : BgData (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 2,
      (XiCOneReal (R.toStepTower.step k hk N₁ ν β p₁).G'
          (R.toStepTower.step k hk N₁ ν β p₁).a (R.toStepTower.step k hk N₁ ν β p₁).ν
          (R.t / 2) D ∧
        ∀ x i, D.h x i = (((R.toStepTower.step k hk N₁ ν β p₁).h₀ i : ℝ) : ℂ)) →
      XiCOneReal (lvTop N₁ R.m₁ k (rhoSep R.m₁)) (compWeight 3 1) ν (R.t / 2) D :=
    fun D hD => hD.1
  have hH0 : 0 ≤ hullConst 3 3 (towerDetRate R.κ) (towerDetConst R.κ) *
      Real.exp (c1 3 3 * Real.log 2) * Real.exp (hullRate 3 3 (towerDetRate R.κ)) := by
    have hconst := towerDetConst_nonneg R.toStepTower
    have : 0 ≤ hullConst 3 3 (towerDetRate R.κ) (towerDetConst R.κ) := by
      unfold hullConst; exact mul_nonneg hconst (Real.exp_pos _).le
    positivity
  refine ⟨F, Fcut, hF, hFa, hFe, ?_⟩
  intro g hg hvalM
  refine renormExpInputOn_zero_of_fields hsub h1 h2 (fun z => ?_) h3 (fun p => ?_)
  · obtain ⟨term, h⟩ := renE0_siteRecord_of_family R hR k hk N₁ h3N hN hν0 hν β p₁ hB z (cE z)
      (hanE z) (hlocE z) (hbdE z) (hsuppE z) (hvalE z)
    exact ⟨term, h.mono_rate (κ' := min (3 / 2 * R.κdec) (min κ κM))
      (min_le_min le_rfl (min_le_left _ _)) (by positivity) (fun Y _ => renDY_nonneg Y)⟩
  · obtain ⟨term, h⟩ := renM0_siteRecord_union_of_family R k hk N₁ h3N hν0 hν β p₁ hβ hBM
      (p.1 : CTorus 3 3 N₁ R.m₁ (k + 1)) p.2 g q hq hg (cM _ p.2) (hanM _ p.2) (hlocM _ p.2)
      (hbdM _ p.2) (hsuppM _ p.2) (hvalM _ p.2)
    exact ⟨term, h.mono_rate (κ' := min (3 / 2 * R.κdec) (min κ κM))
      ((min_le_right _ _).trans (min_le_right _ _)) hBM (fun Y _ => renDY_nonneg Y)⟩
open Classical in
/-- One solution and cut map give the physical zero-class record for every admissible source. -/
theorem renormPhysicalZero_onFibre_half_uniform {κmin : ℝ} (R : StepTowerTheta κmin)
    (hR : renDetFibreMin ≤ κmin) (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁] (h3N : 3 ∣ N₁)
    (hN : 5 < N₁) {ν : ℝ} (hν0 : 0 ≤ ν) (hν : ν * 3 ^ (2 * (k + 1)) ≤ 1) (β p₁ : ℝ)
    (hβ : 0 < β) (Xcut : Set (CTorus 3 3 N₁ R.m₁ (k + 1)))
    (q : ℝ) (hq : q ≤ 1)
    {κ B κM BM : ℝ} (hB : 0 ≤ B) (hBM : 0 ≤ BM)
    (cE : Torus 3 (N₁ * 3 ^ R.m₁ * 3 ^ (k + 1 - (k + 1))) →
      physParam 2 (R.toStepTower.step k hk N₁ ν β p₁) → Finset (CubeB (d := 3) (L := 3) (N₁ := N₁) (m₁ := R.m₁) (K := k + 1) 1 (k + 1) Set.univ) → ℂ)
    (cM : CTorus 3 3 N₁ R.m₁ (k + 1) → Fin 2 →
      physParam 2 (R.toStepTower.step k hk N₁ ν β p₁) → Finset (CubeB (d := 3) (L := 3) (N₁ := N₁) (m₁ := R.m₁) (K := k + 1) 1 (k + 1) Set.univ) → ℂ)
    (hanE : ∀ (z : Torus 3 (N₁ * 3 ^ R.m₁ * 3 ^ (k + 1 - (k + 1)))), ∀ T, AnalyticOnNhd ℂ (fun θ => cE z θ T) (physV (R.toStepTower.step k hk N₁ ν β p₁) (R.toStepTower.step k hk N₁ ν β p₁).a₁ (R.toStepTower.step k hk N₁ ν β p₁).ν R.t))
    (hlocE : ∀ (z : Torus 3 (N₁ * 3 ^ R.m₁ * 3 ^ (k + 1 - (k + 1)))), ∀ T, ∀ θ ∈ (physV (R.toStepTower.step k hk N₁ ν β p₁) (R.toStepTower.step k hk N₁ ν β p₁).a₁ (R.toStepTower.step k hk N₁ ν β p₁).ν R.t),
      ∀ θ' ∈ (physV (R.toStepTower.step k hk N₁ ν β p₁) (R.toStepTower.step k hk N₁ ν β p₁).a₁ (R.toStepTower.step k hk N₁ ν β p₁).ν R.t),
      physRestrict (sitesOf T) (physIncl 2 (R.toStepTower.step k hk N₁ ν β p₁) θ) =
        physRestrict (sitesOf T) (physIncl 2 (R.toStepTower.step k hk N₁ ν β p₁) θ') →
        cE z θ T = cE z θ' T)
    (hbdE : ∀ (z : Torus 3 (N₁ * 3 ^ R.m₁ * 3 ^ (k + 1 - (k + 1)))), ∀ θ ∈ (physV (R.toStepTower.step k hk N₁ ν β p₁) (R.toStepTower.step k hk N₁ ν β p₁).a₁ (R.toStepTower.step k hk N₁ ν β p₁).ν R.t),
      ∀ T, IsPolyDom 1 (k + 1) (sitesOf T) → ‖cE z θ T‖ ≤ B * Real.exp (-κ * dExt T))
    (hsuppE : ∀ (z : Torus 3 (N₁ * 3 ^ R.m₁ * 3 ^ (k + 1 - (k + 1)))), ∀ θ ∈ (physV (R.toStepTower.step k hk N₁ ν β p₁) (R.toStepTower.step k hk N₁ ν β p₁).a₁ (R.toStepTower.step k hk N₁ ν β p₁).ν R.t),
      ∀ T, cE z θ T ≠ 0 → IsPolyDom 1 (k + 1) (sitesOf T))
    (hvalE : ∀ (z : Torus 3 (N₁ * 3 ^ R.m₁ * 3 ^ (k + 1 - (k + 1)))), ∀ (D' : BgData (R.toStepTower.step k hk N₁ ν β p₁).G' 2)
        (hDh : ∀ y i, D'.h y i = ((R.toStepTower.step k hk N₁ ν β p₁).h₀ i : ℂ)),
      XiCData (R.toStepTower.step k hk N₁ ν β p₁).G' (R.toStepTower.step k hk N₁ ν β p₁).a
        (R.toStepTower.step k hk N₁ ν β p₁).ν (k + 1) 1 R.t D' →
      ((R.toStepTower.step k hk N₁ ν β p₁).withDatum D' hDh).E1locC
          (zeroClass 3 3 N₁ R.m₁ k 2 (rhoSep R.m₁)) z =
        ∑ C, cE z (⟨rawOf D', rawOf_mem_rawSub _⟩, (0 : CTorus 3 3 N₁ R.m₁ (k + 1) → Fin 2 → ℂ)) C)
    (hanM : ∀ (y : CTorus 3 3 N₁ R.m₁ (k + 1)) (i : Fin 2), ∀ T, AnalyticOnNhd ℂ (fun θ => cM y i θ T) (physV (R.toStepTower.step k hk N₁ ν β p₁) (R.toStepTower.step k hk N₁ ν β p₁).a₁ (R.toStepTower.step k hk N₁ ν β p₁).ν R.t))
    (hlocM : ∀ (y : CTorus 3 3 N₁ R.m₁ (k + 1)) (i : Fin 2), ∀ T, ∀ θ ∈ (physV (R.toStepTower.step k hk N₁ ν β p₁) (R.toStepTower.step k hk N₁ ν β p₁).a₁ (R.toStepTower.step k hk N₁ ν β p₁).ν R.t),
      ∀ θ' ∈ (physV (R.toStepTower.step k hk N₁ ν β p₁) (R.toStepTower.step k hk N₁ ν β p₁).a₁ (R.toStepTower.step k hk N₁ ν β p₁).ν R.t),
      physRestrict (sitesOf T) (physIncl 2 (R.toStepTower.step k hk N₁ ν β p₁) θ) =
        physRestrict (sitesOf T) (physIncl 2 (R.toStepTower.step k hk N₁ ν β p₁) θ') →
        cM y i θ T = cM y i θ' T)
    (hbdM : ∀ (y : CTorus 3 3 N₁ R.m₁ (k + 1)) (i : Fin 2), ∀ θ ∈ (physV (R.toStepTower.step k hk N₁ ν β p₁) (R.toStepTower.step k hk N₁ ν β p₁).a₁ (R.toStepTower.step k hk N₁ ν β p₁).ν R.t),
      ∀ T, IsPolyDom 1 (k + 1) (sitesOf T) → ‖cM y i θ T‖ ≤ BM * Real.exp (-κM * dExt T))
    (hsuppM : ∀ (y : CTorus 3 3 N₁ R.m₁ (k + 1)) (i : Fin 2), ∀ θ ∈ (physV (R.toStepTower.step k hk N₁ ν β p₁) (R.toStepTower.step k hk N₁ ν β p₁).a₁ (R.toStepTower.step k hk N₁ ν β p₁).ν R.t),
      ∀ T, cM y i θ T ≠ 0 → IsPolyDom 1 (k + 1) (sitesOf T))
    (hvalM : ∀ (g : Fld 3 3 N₁ R.m₁ (k + 1) 2), (∑ x, ∑ j, ‖g x j‖) < q →
      ∀ (y : CTorus 3 3 N₁ R.m₁ (k + 1)) (i : Fin 2), ∀ (D' : BgData (R.toStepTower.step k hk N₁ ν β p₁).G' 2)
        (hDh : ∀ y i, D'.h y i = ((R.toStepTower.step k hk N₁ ν β p₁).h₀ i : ℂ)),
      XiCData (R.toStepTower.step k hk N₁ ν β p₁).G' (R.toStepTower.step k hk N₁ ν β p₁).a
        (R.toStepTower.step k hk N₁ ν β p₁).ν (k + 1) 1 R.t D' →
      ((R.toStepTower.step k hk N₁ ν β p₁).withDatum D' hDh).M0C
          (zeroClass 3 3 N₁ R.m₁ k 2 (rhoSep R.m₁)) g y i =
        ((((R.toStepTower.step k hk N₁ ν β p₁).betaU ^ (1 / 2 : ℝ) : ℝ) : ℂ)) *
          ∑ C, cM y i (⟨rawOf D', rawOf_mem_rawSub _⟩, g) C) :
    ∃ F : RawData 3 3 (N₁ * 3 ^ R.m₁) (k + 1) 2 × (Fin 3 → ℂ) →
        (((lvTop N₁ R.m₁ k (rhoSep R.m₁))).Ω 1 × Fin 2 → ℂ) ×
          (((lvTop N₁ R.m₁ k (rhoSep R.m₁))).Ω 1 → ℂ),
    ∃ Fcut : RawData 3 3 (N₁ * 3 ^ R.m₁) (k + 1) 2 × (Fin 3 → ℂ) →
        (RenLabel (lvTop N₁ R.m₁ k (rhoSep R.m₁)) Xcut → ℂ) →
        (((lvTop N₁ R.m₁ k (rhoSep R.m₁))).Ω 1 × Fin 2 → ℂ) ×
          (((lvTop N₁ R.m₁ k (rhoSep R.m₁))).Ω 1 → ℂ),
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
      ∀ (g : Fld 3 3 N₁ R.m₁ (k + 1) 2), (∑ x, ∑ j, ‖g x j‖) < q →
      RenormExpInputOn (N := 2) (lvTop N₁ R.m₁ k (rhoSep R.m₁)) (compWeight 3 1) ν (R.t / 2)
        R.r₀ (renCK 3 3 2 R.BG R.κ) (8 * (R.t / 2)) F
        (fun z : Torus 3 (N₁ * 3 ^ R.m₁ * 3 ^ (k + 1 - (k + 1))) =>
          blockSites 3 3 N₁ R.m₁ (k + 1) k z)
        (fun z => renYs (renCube (lvTop N₁ R.m₁ k (rhoSep R.m₁))
          (X1 (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 1 k (fam 1 (blockSite k z)))) (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 1
          (X1 (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 1 k (fam 1 (blockSite k z))) ∪ (Finset.univ.image fun T : Finset (CubeB (d := 3) (L := 3) (N₁ := N₁) (m₁ := R.m₁) (K := k + 1) 1 (k + 1) Set.univ) =>
        (Finset.univ.filter fun x : CTorus 3 3 N₁ R.m₁ (k + 1) => x ∈ sitesOf T)))
        (fun p => renYs (renCube (lvTop N₁ R.m₁ k (rhoSep R.m₁))
          (X1 (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 1 k (fam 1 (p.1 : CTorus 3 3 N₁ R.m₁ (k + 1))))) (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 1
          (X1 (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 1 k (fam 1 (p.1 : CTorus 3 3 N₁ R.m₁ (k + 1)))) ∪ (Finset.univ.image fun T : Finset (CubeB (d := 3) (L := 3) (N₁ := N₁) (m₁ := R.m₁) (K := k + 1) 1 (k + 1) Set.univ) =>
        (Finset.univ.filter fun x : CTorus 3 3 N₁ R.m₁ (k + 1) => x ∈ sitesOf T)))
        (renDY (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 1) (min (3 / 2 * R.κdec) (min κ κM)) (min (3 / 2 * R.κdec) (min κ κM)) 1
        (hullConst 3 3 (towerDetRate R.κ) (towerDetConst R.κ) *
            Real.exp (c1 3 3 * Real.log 2) * Real.exp (hullRate 3 3 (towerDetRate R.κ)) + B)
        0 BM 0 (fun (z : Torus 3 (N₁ * 3 ^ R.m₁ * 3 ^ (k + 1 - (k + 1)))) (D : BgData (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 2) (ξ : Fin 3 → ℂ) =>
          if hD : ∀ x i, D.h x i = ((((R.toStepTower.step k hk N₁ ν β p₁).h₀ i : ℝ)) : ℂ)
          then ((R.toStepTower.step k hk N₁ ν β p₁).withDatum
            (renThetaDatum (R.toStepTower.step k hk N₁ ν β p₁) (R.t / 2) D ξ) hD).E0locC
              (zeroClass 3 3 N₁ R.m₁ k 2 (rhoSep R.m₁)) z else 0) (fun _ _ _ => 0) (fun (p : ((lvTop N₁ R.m₁ k (rhoSep R.m₁))).Ω 1 × Fin 2) (D : BgData (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 2) (ξ : Fin 3 → ℂ) =>
          if hD : ∀ x i, D.h x i = ((((R.toStepTower.step k hk N₁ ν β p₁).h₀ i : ℝ)) : ℂ)
          then (((((R.toStepTower.step k hk N₁ ν β p₁).betaU ^ (1 / 2 : ℝ) : ℝ) : ℂ)))⁻¹ *
            ((R.toStepTower.step k hk N₁ ν β p₁).withDatum
              (renThetaDatum (R.toStepTower.step k hk N₁ ν β p₁) (R.t / 2) D ξ) hD).M0C
                (zeroClass 3 3 N₁ R.m₁ k 2 (rhoSep R.m₁)) g (p.1 : CTorus 3 3 N₁ R.m₁ (k + 1)) p.2
          else 0) (fun _ _ _ => 0)
        (fun D => XiCOneReal (R.toStepTower.step k hk N₁ ν β p₁).G'
            (R.toStepTower.step k hk N₁ ν β p₁).a (R.toStepTower.step k hk N₁ ν β p₁).ν
            (R.t / 2) D ∧
          ∀ x i, D.h x i = ((((R.toStepTower.step k hk N₁ ν β p₁).h₀ i : ℝ)) : ℂ)) := by
  obtain ⟨F, Fcut, hF, hFa, hFe, hI⟩ :=
    renormPhysicalZero_onFibre_half_core_of_source_value R hR k hk N₁ h3N hN hν0 hν β p₁ hβ Xcut q hq hB hBM cE cM hanE hlocE hbdE hsuppE hvalE hanM hlocM hbdM hsuppM
  exact ⟨F, Fcut, hF, hFa, hFe, fun g hg => hI g hg (hvalM g hg)⟩
open Classical in
/-- **The physical renormalization record of the zero class on the fibre, at class radius
`t / 2`, generic in the mark family `cE` and the observable family `cM`.**  One solution map `F`
(`IsRenSol`, with its cut map and the endpoint identity) and the record `RenormExpInputOn` with
zero old terms, whose energy function is the physical `E₀^{(k+1)}(z)` of the step at the
renormalized datum and whose observable function is `β_U^{-1/2} M₀^{(k+1)}(g; y, i)` at the
renormalized datum, for the fixed source `g`.  The index families are `renYs ∪ site sets`
for both fields; the common rate is `min (3/2 κ_dec) (min κ κM)`; the energy budget is the
determinant budget plus `B`, the observable budget is `BM`; the old budgets are `0`.  The
hypotheses on `cE`, `cM` (the value clause of `cE` is the marked energy `E1locC` at the zero class; `E0locC` is the determinant summand plus it; analyticity, exact locality on `sitesOf T`, bound, support, value at
every chart datum of constant field) are the ones of `renE0_siteRecord_of_family` and
`renM0_siteRecord_union_of_family`. -/
theorem renormPhysicalZero_onFibre_half_of_families {κmin : ℝ} (R : StepTowerTheta κmin)
    (hR : renDetFibreMin ≤ κmin) (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁] (h3N : 3 ∣ N₁)
    (hN : 5 < N₁) {ν : ℝ} (hν0 : 0 ≤ ν) (hν : ν * 3 ^ (2 * (k + 1)) ≤ 1) (β p₁ : ℝ)
    (hβ : 0 < β) (Xcut : Set (CTorus 3 3 N₁ R.m₁ (k + 1)))
    (g : Fld 3 3 N₁ R.m₁ (k + 1) 2) (q : ℝ) (hq : q ≤ 1) (hg : ∑ x, ∑ j, ‖g x j‖ < q)
    {κ B κM BM : ℝ} (hB : 0 ≤ B) (hBM : 0 ≤ BM)
    (cE : Torus 3 (N₁ * 3 ^ R.m₁ * 3 ^ (k + 1 - (k + 1))) →
      physParam 2 (R.toStepTower.step k hk N₁ ν β p₁) → Finset (CubeB (d := 3) (L := 3) (N₁ := N₁) (m₁ := R.m₁) (K := k + 1) 1 (k + 1) Set.univ) → ℂ)
    (cM : CTorus 3 3 N₁ R.m₁ (k + 1) → Fin 2 →
      physParam 2 (R.toStepTower.step k hk N₁ ν β p₁) → Finset (CubeB (d := 3) (L := 3) (N₁ := N₁) (m₁ := R.m₁) (K := k + 1) 1 (k + 1) Set.univ) → ℂ)
    (hanE : ∀ (z : Torus 3 (N₁ * 3 ^ R.m₁ * 3 ^ (k + 1 - (k + 1)))), ∀ T, AnalyticOnNhd ℂ (fun θ => cE z θ T) (physV (R.toStepTower.step k hk N₁ ν β p₁) (R.toStepTower.step k hk N₁ ν β p₁).a₁ (R.toStepTower.step k hk N₁ ν β p₁).ν R.t))
    (hlocE : ∀ (z : Torus 3 (N₁ * 3 ^ R.m₁ * 3 ^ (k + 1 - (k + 1)))), ∀ T, ∀ θ ∈ (physV (R.toStepTower.step k hk N₁ ν β p₁) (R.toStepTower.step k hk N₁ ν β p₁).a₁ (R.toStepTower.step k hk N₁ ν β p₁).ν R.t),
      ∀ θ' ∈ (physV (R.toStepTower.step k hk N₁ ν β p₁) (R.toStepTower.step k hk N₁ ν β p₁).a₁ (R.toStepTower.step k hk N₁ ν β p₁).ν R.t),
      physRestrict (sitesOf T) (physIncl 2 (R.toStepTower.step k hk N₁ ν β p₁) θ) =
        physRestrict (sitesOf T) (physIncl 2 (R.toStepTower.step k hk N₁ ν β p₁) θ') →
        cE z θ T = cE z θ' T)
    (hbdE : ∀ (z : Torus 3 (N₁ * 3 ^ R.m₁ * 3 ^ (k + 1 - (k + 1)))), ∀ θ ∈ (physV (R.toStepTower.step k hk N₁ ν β p₁) (R.toStepTower.step k hk N₁ ν β p₁).a₁ (R.toStepTower.step k hk N₁ ν β p₁).ν R.t),
      ∀ T, IsPolyDom 1 (k + 1) (sitesOf T) → ‖cE z θ T‖ ≤ B * Real.exp (-κ * dExt T))
    (hsuppE : ∀ (z : Torus 3 (N₁ * 3 ^ R.m₁ * 3 ^ (k + 1 - (k + 1)))), ∀ θ ∈ (physV (R.toStepTower.step k hk N₁ ν β p₁) (R.toStepTower.step k hk N₁ ν β p₁).a₁ (R.toStepTower.step k hk N₁ ν β p₁).ν R.t),
      ∀ T, cE z θ T ≠ 0 → IsPolyDom 1 (k + 1) (sitesOf T))
    (hvalE : ∀ (z : Torus 3 (N₁ * 3 ^ R.m₁ * 3 ^ (k + 1 - (k + 1)))), ∀ (D' : BgData (R.toStepTower.step k hk N₁ ν β p₁).G' 2)
        (hDh : ∀ y i, D'.h y i = ((R.toStepTower.step k hk N₁ ν β p₁).h₀ i : ℂ)),
      XiCData (R.toStepTower.step k hk N₁ ν β p₁).G' (R.toStepTower.step k hk N₁ ν β p₁).a
        (R.toStepTower.step k hk N₁ ν β p₁).ν (k + 1) 1 R.t D' →
      ((R.toStepTower.step k hk N₁ ν β p₁).withDatum D' hDh).E1locC
          (zeroClass 3 3 N₁ R.m₁ k 2 (rhoSep R.m₁)) z =
        ∑ C, cE z (⟨rawOf D', rawOf_mem_rawSub _⟩, (0 : CTorus 3 3 N₁ R.m₁ (k + 1) → Fin 2 → ℂ)) C)
    (hanM : ∀ (y : CTorus 3 3 N₁ R.m₁ (k + 1)) (i : Fin 2), ∀ T, AnalyticOnNhd ℂ (fun θ => cM y i θ T) (physV (R.toStepTower.step k hk N₁ ν β p₁) (R.toStepTower.step k hk N₁ ν β p₁).a₁ (R.toStepTower.step k hk N₁ ν β p₁).ν R.t))
    (hlocM : ∀ (y : CTorus 3 3 N₁ R.m₁ (k + 1)) (i : Fin 2), ∀ T, ∀ θ ∈ (physV (R.toStepTower.step k hk N₁ ν β p₁) (R.toStepTower.step k hk N₁ ν β p₁).a₁ (R.toStepTower.step k hk N₁ ν β p₁).ν R.t),
      ∀ θ' ∈ (physV (R.toStepTower.step k hk N₁ ν β p₁) (R.toStepTower.step k hk N₁ ν β p₁).a₁ (R.toStepTower.step k hk N₁ ν β p₁).ν R.t),
      physRestrict (sitesOf T) (physIncl 2 (R.toStepTower.step k hk N₁ ν β p₁) θ) =
        physRestrict (sitesOf T) (physIncl 2 (R.toStepTower.step k hk N₁ ν β p₁) θ') →
        cM y i θ T = cM y i θ' T)
    (hbdM : ∀ (y : CTorus 3 3 N₁ R.m₁ (k + 1)) (i : Fin 2), ∀ θ ∈ (physV (R.toStepTower.step k hk N₁ ν β p₁) (R.toStepTower.step k hk N₁ ν β p₁).a₁ (R.toStepTower.step k hk N₁ ν β p₁).ν R.t),
      ∀ T, IsPolyDom 1 (k + 1) (sitesOf T) → ‖cM y i θ T‖ ≤ BM * Real.exp (-κM * dExt T))
    (hsuppM : ∀ (y : CTorus 3 3 N₁ R.m₁ (k + 1)) (i : Fin 2), ∀ θ ∈ (physV (R.toStepTower.step k hk N₁ ν β p₁) (R.toStepTower.step k hk N₁ ν β p₁).a₁ (R.toStepTower.step k hk N₁ ν β p₁).ν R.t),
      ∀ T, cM y i θ T ≠ 0 → IsPolyDom 1 (k + 1) (sitesOf T))
    (hvalM : ∀ (y : CTorus 3 3 N₁ R.m₁ (k + 1)) (i : Fin 2), ∀ (D' : BgData (R.toStepTower.step k hk N₁ ν β p₁).G' 2)
        (hDh : ∀ y i, D'.h y i = ((R.toStepTower.step k hk N₁ ν β p₁).h₀ i : ℂ)),
      XiCData (R.toStepTower.step k hk N₁ ν β p₁).G' (R.toStepTower.step k hk N₁ ν β p₁).a
        (R.toStepTower.step k hk N₁ ν β p₁).ν (k + 1) 1 R.t D' →
      ((R.toStepTower.step k hk N₁ ν β p₁).withDatum D' hDh).M0C
          (zeroClass 3 3 N₁ R.m₁ k 2 (rhoSep R.m₁)) g y i =
        ((((R.toStepTower.step k hk N₁ ν β p₁).betaU ^ (1 / 2 : ℝ) : ℝ) : ℂ)) *
          ∑ C, cM y i (⟨rawOf D', rawOf_mem_rawSub _⟩, g) C) :
    ∃ F : RawData 3 3 (N₁ * 3 ^ R.m₁) (k + 1) 2 × (Fin 3 → ℂ) →
        (((lvTop N₁ R.m₁ k (rhoSep R.m₁))).Ω 1 × Fin 2 → ℂ) ×
          (((lvTop N₁ R.m₁ k (rhoSep R.m₁))).Ω 1 → ℂ),
    ∃ Fcut : RawData 3 3 (N₁ * 3 ^ R.m₁) (k + 1) 2 × (Fin 3 → ℂ) →
        (RenLabel (lvTop N₁ R.m₁ k (rhoSep R.m₁)) Xcut → ℂ) →
        (((lvTop N₁ R.m₁ k (rhoSep R.m₁))).Ω 1 × Fin 2 → ℂ) ×
          (((lvTop N₁ R.m₁ k (rhoSep R.m₁))).Ω 1 → ℂ),
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
          (X1 (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 1 k (fam 1 (blockSite k z)))) (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 1
          (X1 (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 1 k (fam 1 (blockSite k z))) ∪ (Finset.univ.image fun T : Finset (CubeB (d := 3) (L := 3) (N₁ := N₁) (m₁ := R.m₁) (K := k + 1) 1 (k + 1) Set.univ) =>
        (Finset.univ.filter fun x : CTorus 3 3 N₁ R.m₁ (k + 1) => x ∈ sitesOf T)))
        (fun p => renYs (renCube (lvTop N₁ R.m₁ k (rhoSep R.m₁))
          (X1 (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 1 k (fam 1 (p.1 : CTorus 3 3 N₁ R.m₁ (k + 1))))) (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 1
          (X1 (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 1 k (fam 1 (p.1 : CTorus 3 3 N₁ R.m₁ (k + 1)))) ∪ (Finset.univ.image fun T : Finset (CubeB (d := 3) (L := 3) (N₁ := N₁) (m₁ := R.m₁) (K := k + 1) 1 (k + 1) Set.univ) =>
        (Finset.univ.filter fun x : CTorus 3 3 N₁ R.m₁ (k + 1) => x ∈ sitesOf T)))
        (renDY (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 1) (min (3 / 2 * R.κdec) (min κ κM)) (min (3 / 2 * R.κdec) (min κ κM)) 1
        (hullConst 3 3 (towerDetRate R.κ) (towerDetConst R.κ) *
            Real.exp (c1 3 3 * Real.log 2) * Real.exp (hullRate 3 3 (towerDetRate R.κ)) + B)
        0 BM 0 (fun (z : Torus 3 (N₁ * 3 ^ R.m₁ * 3 ^ (k + 1 - (k + 1)))) (D : BgData (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 2) (ξ : Fin 3 → ℂ) =>
          if hD : ∀ x i, D.h x i = ((((R.toStepTower.step k hk N₁ ν β p₁).h₀ i : ℝ)) : ℂ)
          then ((R.toStepTower.step k hk N₁ ν β p₁).withDatum
            (renThetaDatum (R.toStepTower.step k hk N₁ ν β p₁) (R.t / 2) D ξ) hD).E0locC
              (zeroClass 3 3 N₁ R.m₁ k 2 (rhoSep R.m₁)) z else 0) (fun _ _ _ => 0) (fun (p : ((lvTop N₁ R.m₁ k (rhoSep R.m₁))).Ω 1 × Fin 2) (D : BgData (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 2) (ξ : Fin 3 → ℂ) =>
          if hD : ∀ x i, D.h x i = ((((R.toStepTower.step k hk N₁ ν β p₁).h₀ i : ℝ)) : ℂ)
          then (((((R.toStepTower.step k hk N₁ ν β p₁).betaU ^ (1 / 2 : ℝ) : ℝ) : ℂ)))⁻¹ *
            ((R.toStepTower.step k hk N₁ ν β p₁).withDatum
              (renThetaDatum (R.toStepTower.step k hk N₁ ν β p₁) (R.t / 2) D ξ) hD).M0C
                (zeroClass 3 3 N₁ R.m₁ k 2 (rhoSep R.m₁)) g (p.1 : CTorus 3 3 N₁ R.m₁ (k + 1)) p.2
          else 0) (fun _ _ _ => 0)
        (fun D => XiCOneReal (R.toStepTower.step k hk N₁ ν β p₁).G'
            (R.toStepTower.step k hk N₁ ν β p₁).a (R.toStepTower.step k hk N₁ ν β p₁).ν
            (R.t / 2) D ∧
          ∀ x i, D.h x i = ((((R.toStepTower.step k hk N₁ ν β p₁).h₀ i : ℝ)) : ℂ)) := by
  obtain ⟨F, Fcut, hF, hFa, hFe, hI⟩ :=
    renormPhysicalZero_onFibre_half_core_of_source_value R hR k hk N₁ h3N hN hν0 hν β p₁ hβ Xcut q hq hB hBM cE cM hanE hlocE hbdE hsuppE hvalE hanM hlocM hbdM hsuppM
  exact ⟨F, Fcut, hF, hFa, hFe, hI g hg hvalM⟩
open Classical in
/-- The four physical zero-class estimates use one solution map for every admissible source. -/
theorem renormPhysicalZero_onFibre_half_consequences_uniform {κmin : ℝ} (R : StepTowerTheta κmin)
    (hR : renDetFibreMin ≤ κmin) (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁] (h3N : 3 ∣ N₁)
    (hN : 5 < N₁) {ν : ℝ} (hν0 : 0 ≤ ν) (hν : ν * 3 ^ (2 * (k + 1)) ≤ 1) (β p₁ : ℝ)
    (hβ : 0 < β) (Xcut : Set (CTorus 3 3 N₁ R.m₁ (k + 1)))
    (q : ℝ) (hq : q ≤ 1)
    {κ B κM BM : ℝ} (hB : 0 ≤ B) (hBM : 0 ≤ BM)
    (cE : Torus 3 (N₁ * 3 ^ R.m₁ * 3 ^ (k + 1 - (k + 1))) →
      physParam 2 (R.toStepTower.step k hk N₁ ν β p₁) → Finset (CubeB (d := 3) (L := 3) (N₁ := N₁) (m₁ := R.m₁) (K := k + 1) 1 (k + 1) Set.univ) → ℂ)
    (cM : CTorus 3 3 N₁ R.m₁ (k + 1) → Fin 2 →
      physParam 2 (R.toStepTower.step k hk N₁ ν β p₁) → Finset (CubeB (d := 3) (L := 3) (N₁ := N₁) (m₁ := R.m₁) (K := k + 1) 1 (k + 1) Set.univ) → ℂ)
    (hanE : ∀ (z : Torus 3 (N₁ * 3 ^ R.m₁ * 3 ^ (k + 1 - (k + 1)))), ∀ T, AnalyticOnNhd ℂ (fun θ => cE z θ T) (physV (R.toStepTower.step k hk N₁ ν β p₁) (R.toStepTower.step k hk N₁ ν β p₁).a₁ (R.toStepTower.step k hk N₁ ν β p₁).ν R.t))
    (hlocE : ∀ (z : Torus 3 (N₁ * 3 ^ R.m₁ * 3 ^ (k + 1 - (k + 1)))), ∀ T, ∀ θ ∈ (physV (R.toStepTower.step k hk N₁ ν β p₁) (R.toStepTower.step k hk N₁ ν β p₁).a₁ (R.toStepTower.step k hk N₁ ν β p₁).ν R.t),
      ∀ θ' ∈ (physV (R.toStepTower.step k hk N₁ ν β p₁) (R.toStepTower.step k hk N₁ ν β p₁).a₁ (R.toStepTower.step k hk N₁ ν β p₁).ν R.t),
      physRestrict (sitesOf T) (physIncl 2 (R.toStepTower.step k hk N₁ ν β p₁) θ) =
        physRestrict (sitesOf T) (physIncl 2 (R.toStepTower.step k hk N₁ ν β p₁) θ') →
        cE z θ T = cE z θ' T)
    (hbdE : ∀ (z : Torus 3 (N₁ * 3 ^ R.m₁ * 3 ^ (k + 1 - (k + 1)))), ∀ θ ∈ (physV (R.toStepTower.step k hk N₁ ν β p₁) (R.toStepTower.step k hk N₁ ν β p₁).a₁ (R.toStepTower.step k hk N₁ ν β p₁).ν R.t),
      ∀ T, IsPolyDom 1 (k + 1) (sitesOf T) → ‖cE z θ T‖ ≤ B * Real.exp (-κ * dExt T))
    (hsuppE : ∀ (z : Torus 3 (N₁ * 3 ^ R.m₁ * 3 ^ (k + 1 - (k + 1)))), ∀ θ ∈ (physV (R.toStepTower.step k hk N₁ ν β p₁) (R.toStepTower.step k hk N₁ ν β p₁).a₁ (R.toStepTower.step k hk N₁ ν β p₁).ν R.t),
      ∀ T, cE z θ T ≠ 0 → IsPolyDom 1 (k + 1) (sitesOf T))
    (hvalE : ∀ (z : Torus 3 (N₁ * 3 ^ R.m₁ * 3 ^ (k + 1 - (k + 1)))), ∀ (D' : BgData (R.toStepTower.step k hk N₁ ν β p₁).G' 2)
        (hDh : ∀ y i, D'.h y i = ((R.toStepTower.step k hk N₁ ν β p₁).h₀ i : ℂ)),
      XiCData (R.toStepTower.step k hk N₁ ν β p₁).G' (R.toStepTower.step k hk N₁ ν β p₁).a
        (R.toStepTower.step k hk N₁ ν β p₁).ν (k + 1) 1 R.t D' →
      ((R.toStepTower.step k hk N₁ ν β p₁).withDatum D' hDh).E1locC
          (zeroClass 3 3 N₁ R.m₁ k 2 (rhoSep R.m₁)) z =
        ∑ C, cE z (⟨rawOf D', rawOf_mem_rawSub _⟩, (0 : CTorus 3 3 N₁ R.m₁ (k + 1) → Fin 2 → ℂ)) C)
    (hanM : ∀ (y : CTorus 3 3 N₁ R.m₁ (k + 1)) (i : Fin 2), ∀ T, AnalyticOnNhd ℂ (fun θ => cM y i θ T) (physV (R.toStepTower.step k hk N₁ ν β p₁) (R.toStepTower.step k hk N₁ ν β p₁).a₁ (R.toStepTower.step k hk N₁ ν β p₁).ν R.t))
    (hlocM : ∀ (y : CTorus 3 3 N₁ R.m₁ (k + 1)) (i : Fin 2), ∀ T, ∀ θ ∈ (physV (R.toStepTower.step k hk N₁ ν β p₁) (R.toStepTower.step k hk N₁ ν β p₁).a₁ (R.toStepTower.step k hk N₁ ν β p₁).ν R.t),
      ∀ θ' ∈ (physV (R.toStepTower.step k hk N₁ ν β p₁) (R.toStepTower.step k hk N₁ ν β p₁).a₁ (R.toStepTower.step k hk N₁ ν β p₁).ν R.t),
      physRestrict (sitesOf T) (physIncl 2 (R.toStepTower.step k hk N₁ ν β p₁) θ) =
        physRestrict (sitesOf T) (physIncl 2 (R.toStepTower.step k hk N₁ ν β p₁) θ') →
        cM y i θ T = cM y i θ' T)
    (hbdM : ∀ (y : CTorus 3 3 N₁ R.m₁ (k + 1)) (i : Fin 2), ∀ θ ∈ (physV (R.toStepTower.step k hk N₁ ν β p₁) (R.toStepTower.step k hk N₁ ν β p₁).a₁ (R.toStepTower.step k hk N₁ ν β p₁).ν R.t),
      ∀ T, IsPolyDom 1 (k + 1) (sitesOf T) → ‖cM y i θ T‖ ≤ BM * Real.exp (-κM * dExt T))
    (hsuppM : ∀ (y : CTorus 3 3 N₁ R.m₁ (k + 1)) (i : Fin 2), ∀ θ ∈ (physV (R.toStepTower.step k hk N₁ ν β p₁) (R.toStepTower.step k hk N₁ ν β p₁).a₁ (R.toStepTower.step k hk N₁ ν β p₁).ν R.t),
      ∀ T, cM y i θ T ≠ 0 → IsPolyDom 1 (k + 1) (sitesOf T))
    (hvalM : ∀ (g : Fld 3 3 N₁ R.m₁ (k + 1) 2), (∑ x, ∑ j, ‖g x j‖) < q →
      ∀ (y : CTorus 3 3 N₁ R.m₁ (k + 1)) (i : Fin 2), ∀ (D' : BgData (R.toStepTower.step k hk N₁ ν β p₁).G' 2)
        (hDh : ∀ y i, D'.h y i = ((R.toStepTower.step k hk N₁ ν β p₁).h₀ i : ℂ)),
      XiCData (R.toStepTower.step k hk N₁ ν β p₁).G' (R.toStepTower.step k hk N₁ ν β p₁).a
        (R.toStepTower.step k hk N₁ ν β p₁).ν (k + 1) 1 R.t D' →
      ((R.toStepTower.step k hk N₁ ν β p₁).withDatum D' hDh).M0C
          (zeroClass 3 3 N₁ R.m₁ k 2 (rhoSep R.m₁)) g y i =
        ((((R.toStepTower.step k hk N₁ ν β p₁).betaU ^ (1 / 2 : ℝ) : ℝ) : ℂ)) *
          ∑ C, cM y i (⟨rawOf D', rawOf_mem_rawSub _⟩, g) C) :
    ∃ F : RawData 3 3 (N₁ * 3 ^ R.m₁) (k + 1) 2 × (Fin 3 → ℂ) →
        (((lvTop N₁ R.m₁ k (rhoSep R.m₁))).Ω 1 × Fin 2 → ℂ) ×
          (((lvTop N₁ R.m₁ k (rhoSep R.m₁))).Ω 1 → ℂ),
      IsRenSol (N := 2) (lvTop N₁ R.m₁ k (rhoSep R.m₁)) (compWeight 3 1) ν (R.t / 2) (R.t / 2)
        R.r₀ (8 * (R.t / 2)) F ∧
      ∀ (g : Fld 3 3 N₁ R.m₁ (k + 1) 2), (∑ x, ∑ j, ‖g x j‖) < q →
      (∀ (z : Torus 3 (N₁ * 3 ^ R.m₁ * 3 ^ (k + 1 - (k + 1)))) (εR : ℝ), 0 ≤ εR → εR ≤ R.r₀ →
        (∃ term, IsLocExp (N := 2) (lvTop N₁ R.m₁ k (rhoSep R.m₁))
          (fun D => XiCOneReal (R.toStepTower.step k hk N₁ ν β p₁).G'
            (R.toStepTower.step k hk N₁ ν β p₁).a (R.toStepTower.step k hk N₁ ν β p₁).ν
            (R.t / 2) D ∧
          ∀ x i, D.h x i = ((((R.toStepTower.step k hk N₁ ν β p₁).h₀ i : ℝ)) : ℂ)) εR
          (renYs (renCube (lvTop N₁ R.m₁ k (rhoSep R.m₁))
          (X1 (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 1 k (fam 1 (blockSite k z)))) (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 1
          (X1 (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 1 k (fam 1 (blockSite k z))) ∪ (Finset.univ.image fun T : Finset (CubeB (d := 3) (L := 3) (N₁ := N₁) (m₁ := R.m₁) (K := k + 1) 1 (k + 1) Set.univ) =>
        (Finset.univ.filter fun x : CTorus 3 3 N₁ R.m₁ (k + 1) => x ∈ sitesOf T)))
          (renDY (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 1) (min (3 / 2 * R.κdec) (min κ κM))
          (1 * ((3 + 6) * (renCK 3 3 2 R.BG R.κ * (R.t / 2)) ^ 2 *
            blockWeight (lvTop N₁ R.m₁ k (rhoSep R.m₁))
              (blockSites 3 3 N₁ R.m₁ (k + 1) k z)) * εR ^ 1)
          (fun D ξ => renC1On (lvTop N₁ R.m₁ k (rhoSep R.m₁)) (compWeight 3 1) ν (R.t / 2)
            (blockSites 3 3 N₁ R.m₁ (k + 1) k z) D.Ψ D.h
            (bgFieldC (lvTop N₁ R.m₁ k (rhoSep R.m₁)) (compWeight 3 1) ν (bgC0 3 3 2) D) ξ) term) ∧
        (∃ term, IsLocExp (N := 2) (lvTop N₁ R.m₁ k (rhoSep R.m₁))
          (fun D => XiCOneReal (R.toStepTower.step k hk N₁ ν β p₁).G'
            (R.toStepTower.step k hk N₁ ν β p₁).a (R.toStepTower.step k hk N₁ ν β p₁).ν
            (R.t / 2) D ∧
          ∀ x i, D.h x i = ((((R.toStepTower.step k hk N₁ ν β p₁).h₀ i : ℝ)) : ℂ)) εR
          (renYs (renCube (lvTop N₁ R.m₁ k (rhoSep R.m₁))
          (X1 (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 1 k (fam 1 (blockSite k z)))) (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 1
          (X1 (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 1 k (fam 1 (blockSite k z))) ∪ (Finset.univ.image fun T : Finset (CubeB (d := 3) (L := 3) (N₁ := N₁) (m₁ := R.m₁) (K := k + 1) 1 (k + 1) Set.univ) =>
        (Finset.univ.filter fun x : CTorus 3 3 N₁ R.m₁ (k + 1) => x ∈ sitesOf T)))
          (renDY (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 1) (min (3 / 2 * R.κdec) (min κ κM))
          (1 * (17 / 32 * ((2 : ℕ) * ((3 + (bgK1 3 3 2 * (xiC1 3 * (R.t / 2)) +
            renCK 3 3 2 R.BG R.κ * cK2 3 3 2 * (8 * (R.t / 2)) * R.r₀ + 2)) *
            (renCK 3 3 2 R.BG R.κ * cK2 3 3 2 * (8 * (R.t / 2))) ^ 2)) *
            blockWeight (lvTop N₁ R.m₁ k (rhoSep R.m₁))
              (blockSites 3 3 N₁ R.m₁ (k + 1) k z)) * εR ^ 2)
          (fun D ξ => renC2On (lvTop N₁ R.m₁ k (rhoSep R.m₁)) (compWeight 3 1)
            (blockSites 3 3 N₁ R.m₁ (k + 1) k z) ξ (renMassU ν ξ)
            (bgMultC (lvTop N₁ R.m₁ k (rhoSep R.m₁)) (compWeight 3 1) ν (bgC0 3 3 2) D +
              (F ((D.Ψ, D.h), ξ)).2) (F ((D.Ψ, D.h), ξ)).1) term) ∧
        (∃ term, IsLocExp (N := 2) (lvTop N₁ R.m₁ k (rhoSep R.m₁))
          (fun D => XiCOneReal (R.toStepTower.step k hk N₁ ν β p₁).G'
            (R.toStepTower.step k hk N₁ ν β p₁).a (R.toStepTower.step k hk N₁ ν β p₁).ν
            (R.t / 2) D ∧
          ∀ x i, D.h x i = ((((R.toStepTower.step k hk N₁ ν β p₁).h₀ i : ℝ)) : ℂ)) εR
          (renYs (renCube (lvTop N₁ R.m₁ k (rhoSep R.m₁))
          (X1 (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 1 k (fam 1 (blockSite k z)))) (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 1
          (X1 (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 1 k (fam 1 (blockSite k z))) ∪ (Finset.univ.image fun T : Finset (CubeB (d := 3) (L := 3) (N₁ := N₁) (m₁ := R.m₁) (K := k + 1) 1 (k + 1) Set.univ) =>
        (Finset.univ.filter fun x : CTorus 3 3 N₁ R.m₁ (k + 1) => x ∈ sitesOf T)))
          (renDY (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 1) (min (3 / 2 * R.κdec) (min κ κM))
          ((hullConst 3 3 (towerDetRate R.κ) (towerDetConst R.κ) *
            Real.exp (c1 3 3 * Real.log 2) * Real.exp (hullRate 3 3 (towerDetRate R.κ)) + B))
          (fun D ξ => if hD : ∀ x i, D.h x i = ((((R.toStepTower.step k hk N₁ ν β p₁).h₀ i : ℝ)) : ℂ)
          then ((R.toStepTower.step k hk N₁ ν β p₁).withDatum
            (renThetaDatum (R.toStepTower.step k hk N₁ ν β p₁) (R.t / 2) D ξ) hD).E0locC
              (zeroClass 3 3 N₁ R.m₁ k 2 (rhoSep R.m₁)) z else 0) term)) ∧
      ∀ (p : ((lvTop N₁ R.m₁ k (rhoSep R.m₁))).Ω 1 × Fin 2) (εR : ℝ), εR ≤ R.r₀ →
        (∃ term, IsLocExp (N := 2) (lvTop N₁ R.m₁ k (rhoSep R.m₁))
          (fun D => XiCOneReal (R.toStepTower.step k hk N₁ ν β p₁).G'
            (R.toStepTower.step k hk N₁ ν β p₁).a (R.toStepTower.step k hk N₁ ν β p₁).ν
            (R.t / 2) D ∧
          ∀ x i, D.h x i = ((((R.toStepTower.step k hk N₁ ν β p₁).h₀ i : ℝ)) : ℂ)) εR
          (renYs (renCube (lvTop N₁ R.m₁ k (rhoSep R.m₁))
          (X1 (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 1 k (fam 1 (p.1 : CTorus 3 3 N₁ R.m₁ (k + 1))))) (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 1
          (X1 (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 1 k (fam 1 (p.1 : CTorus 3 3 N₁ R.m₁ (k + 1)))) ∪ (Finset.univ.image fun T : Finset (CubeB (d := 3) (L := 3) (N₁ := N₁) (m₁ := R.m₁) (K := k + 1) 1 (k + 1) Set.univ) =>
        (Finset.univ.filter fun x : CTorus 3 3 N₁ R.m₁ (k + 1) => x ∈ sitesOf T)))
          (renDY (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 1) (min (3 / 2 * R.κdec) (min κ κM))
          (BM + 1 * (renCK 3 3 2 R.BG R.κ * cK2 3 3 2 * (8 * (R.t / 2))) * εR ^ 1)
          (fun D ξ => (if hD : ∀ x i, D.h x i = ((((R.toStepTower.step k hk N₁ ν β p₁).h₀ i : ℝ)) : ℂ)
          then (((((R.toStepTower.step k hk N₁ ν β p₁).betaU ^ (1 / 2 : ℝ) : ℝ) : ℂ)))⁻¹ *
            ((R.toStepTower.step k hk N₁ ν β p₁).withDatum
              (renThetaDatum (R.toStepTower.step k hk N₁ ν β p₁) (R.t / 2) D ξ) hD).M0C
                (zeroClass 3 3 N₁ R.m₁ k 2 (rhoSep R.m₁)) g (p.1 : CTorus 3 3 N₁ R.m₁ (k + 1)) p.2
          else 0) + (F ((D.Ψ, D.h), ξ)).1 p) term) := by
  obtain ⟨F, Fcut, hF, -, -, hI⟩ := renormPhysicalZero_onFibre_half_uniform R hR k hk N₁ h3N hN
    hν0 hν β p₁ hβ Xcut q hq hB hBM cE cM hanE hlocE hbdE hsuppE hvalE hanM hlocM hbdM
    hsuppM hvalM
  have ht := R.t_pos
  have he : 0 < R.t / 2 := by positivity
  have het : R.t / 2 ≤ R.t := by linarith
  have hC := R.flCore_scale_mono k hk N₁ hN hν0 hν he het he het
  have hHB := bgHyp_lv (k := k) R.m₁ hν0 hν
  have hcK := R.toStepTowerRen.renCK_facts.1
  have hr : 0 < R.r₀ := R.r₀_pos
  refine ⟨F, hF, ?_⟩
  intro g hg
  have I := hI g hg
  refine ⟨fun z εR hεR0 hεR => ⟨?_, ?_, ?_⟩, fun p εR hεR => ?_⟩
  · exact thm31g_C1_on hHB he hC.small1 (hC.c7le.trans (c7_le_bgC1 3 3 2 R.BG R.κ)) R.r₀_le I
      zero_le_one hcK hεR z
  · exact thm31g_C2_on hHB he R.r₀_le I zero_le_one (by positivity) hcK hεR0 hεR z
  · exact thm31g_Eu_zero_of_fields_on I hr hεR z
  · exact thm31h_zero_of_fields_on I zero_le_one (by positivity) hcK hr hεR p

open Classical in

/-- **The four consequences of the physical record (Theorem 3.1 (g), (h) at the zero class, on
the fibre at class radius `t / 2`).**  For the solution map `F` of
`renormPhysicalZero_onFibre_half_of_families`, every root `z`, every `p = (y, i)` and
`0 ≤ εR ≤ r₀` (`εR ≤ r₀` for the observable): `C₁` with budget `9 (c_K e)² W(B_z) εR`,
`C₂` with budget `(17/32) · 2 · (3 + A) (c_K K₂ B)² W(B_z) εR²`, `E_u` (the physical `E₀`) with
budget `B_det + B`, and the observable plus the first component of `F` at `p` with budget
`BM + c_K K₂ B εR`; `e = t / 2`, `B = 8 e`, `c_K = renCK`, all over `renYs ∪ site sets` with the
rate `min (3/2 κ_dec) (min κ κM)`. -/
theorem renormPhysicalZero_onFibre_half_consequences {κmin : ℝ} (R : StepTowerTheta κmin)
    (hR : renDetFibreMin ≤ κmin) (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁] (h3N : 3 ∣ N₁)
    (hN : 5 < N₁) {ν : ℝ} (hν0 : 0 ≤ ν) (hν : ν * 3 ^ (2 * (k + 1)) ≤ 1) (β p₁ : ℝ)
    (hβ : 0 < β) (Xcut : Set (CTorus 3 3 N₁ R.m₁ (k + 1)))
    (g : Fld 3 3 N₁ R.m₁ (k + 1) 2) (q : ℝ) (hq : q ≤ 1) (hg : ∑ x, ∑ j, ‖g x j‖ < q)
    {κ B κM BM : ℝ} (hB : 0 ≤ B) (hBM : 0 ≤ BM)
    (cE : Torus 3 (N₁ * 3 ^ R.m₁ * 3 ^ (k + 1 - (k + 1))) →
      physParam 2 (R.toStepTower.step k hk N₁ ν β p₁) → Finset (CubeB (d := 3) (L := 3) (N₁ := N₁) (m₁ := R.m₁) (K := k + 1) 1 (k + 1) Set.univ) → ℂ)
    (cM : CTorus 3 3 N₁ R.m₁ (k + 1) → Fin 2 →
      physParam 2 (R.toStepTower.step k hk N₁ ν β p₁) → Finset (CubeB (d := 3) (L := 3) (N₁ := N₁) (m₁ := R.m₁) (K := k + 1) 1 (k + 1) Set.univ) → ℂ)
    (hanE : ∀ (z : Torus 3 (N₁ * 3 ^ R.m₁ * 3 ^ (k + 1 - (k + 1)))), ∀ T, AnalyticOnNhd ℂ (fun θ => cE z θ T) (physV (R.toStepTower.step k hk N₁ ν β p₁) (R.toStepTower.step k hk N₁ ν β p₁).a₁ (R.toStepTower.step k hk N₁ ν β p₁).ν R.t))
    (hlocE : ∀ (z : Torus 3 (N₁ * 3 ^ R.m₁ * 3 ^ (k + 1 - (k + 1)))), ∀ T, ∀ θ ∈ (physV (R.toStepTower.step k hk N₁ ν β p₁) (R.toStepTower.step k hk N₁ ν β p₁).a₁ (R.toStepTower.step k hk N₁ ν β p₁).ν R.t),
      ∀ θ' ∈ (physV (R.toStepTower.step k hk N₁ ν β p₁) (R.toStepTower.step k hk N₁ ν β p₁).a₁ (R.toStepTower.step k hk N₁ ν β p₁).ν R.t),
      physRestrict (sitesOf T) (physIncl 2 (R.toStepTower.step k hk N₁ ν β p₁) θ) =
        physRestrict (sitesOf T) (physIncl 2 (R.toStepTower.step k hk N₁ ν β p₁) θ') →
        cE z θ T = cE z θ' T)
    (hbdE : ∀ (z : Torus 3 (N₁ * 3 ^ R.m₁ * 3 ^ (k + 1 - (k + 1)))), ∀ θ ∈ (physV (R.toStepTower.step k hk N₁ ν β p₁) (R.toStepTower.step k hk N₁ ν β p₁).a₁ (R.toStepTower.step k hk N₁ ν β p₁).ν R.t),
      ∀ T, IsPolyDom 1 (k + 1) (sitesOf T) → ‖cE z θ T‖ ≤ B * Real.exp (-κ * dExt T))
    (hsuppE : ∀ (z : Torus 3 (N₁ * 3 ^ R.m₁ * 3 ^ (k + 1 - (k + 1)))), ∀ θ ∈ (physV (R.toStepTower.step k hk N₁ ν β p₁) (R.toStepTower.step k hk N₁ ν β p₁).a₁ (R.toStepTower.step k hk N₁ ν β p₁).ν R.t),
      ∀ T, cE z θ T ≠ 0 → IsPolyDom 1 (k + 1) (sitesOf T))
    (hvalE : ∀ (z : Torus 3 (N₁ * 3 ^ R.m₁ * 3 ^ (k + 1 - (k + 1)))), ∀ (D' : BgData (R.toStepTower.step k hk N₁ ν β p₁).G' 2)
        (hDh : ∀ y i, D'.h y i = ((R.toStepTower.step k hk N₁ ν β p₁).h₀ i : ℂ)),
      XiCData (R.toStepTower.step k hk N₁ ν β p₁).G' (R.toStepTower.step k hk N₁ ν β p₁).a
        (R.toStepTower.step k hk N₁ ν β p₁).ν (k + 1) 1 R.t D' →
      ((R.toStepTower.step k hk N₁ ν β p₁).withDatum D' hDh).E1locC
          (zeroClass 3 3 N₁ R.m₁ k 2 (rhoSep R.m₁)) z =
        ∑ C, cE z (⟨rawOf D', rawOf_mem_rawSub _⟩, (0 : CTorus 3 3 N₁ R.m₁ (k + 1) → Fin 2 → ℂ)) C)
    (hanM : ∀ (y : CTorus 3 3 N₁ R.m₁ (k + 1)) (i : Fin 2), ∀ T, AnalyticOnNhd ℂ (fun θ => cM y i θ T) (physV (R.toStepTower.step k hk N₁ ν β p₁) (R.toStepTower.step k hk N₁ ν β p₁).a₁ (R.toStepTower.step k hk N₁ ν β p₁).ν R.t))
    (hlocM : ∀ (y : CTorus 3 3 N₁ R.m₁ (k + 1)) (i : Fin 2), ∀ T, ∀ θ ∈ (physV (R.toStepTower.step k hk N₁ ν β p₁) (R.toStepTower.step k hk N₁ ν β p₁).a₁ (R.toStepTower.step k hk N₁ ν β p₁).ν R.t),
      ∀ θ' ∈ (physV (R.toStepTower.step k hk N₁ ν β p₁) (R.toStepTower.step k hk N₁ ν β p₁).a₁ (R.toStepTower.step k hk N₁ ν β p₁).ν R.t),
      physRestrict (sitesOf T) (physIncl 2 (R.toStepTower.step k hk N₁ ν β p₁) θ) =
        physRestrict (sitesOf T) (physIncl 2 (R.toStepTower.step k hk N₁ ν β p₁) θ') →
        cM y i θ T = cM y i θ' T)
    (hbdM : ∀ (y : CTorus 3 3 N₁ R.m₁ (k + 1)) (i : Fin 2), ∀ θ ∈ (physV (R.toStepTower.step k hk N₁ ν β p₁) (R.toStepTower.step k hk N₁ ν β p₁).a₁ (R.toStepTower.step k hk N₁ ν β p₁).ν R.t),
      ∀ T, IsPolyDom 1 (k + 1) (sitesOf T) → ‖cM y i θ T‖ ≤ BM * Real.exp (-κM * dExt T))
    (hsuppM : ∀ (y : CTorus 3 3 N₁ R.m₁ (k + 1)) (i : Fin 2), ∀ θ ∈ (physV (R.toStepTower.step k hk N₁ ν β p₁) (R.toStepTower.step k hk N₁ ν β p₁).a₁ (R.toStepTower.step k hk N₁ ν β p₁).ν R.t),
      ∀ T, cM y i θ T ≠ 0 → IsPolyDom 1 (k + 1) (sitesOf T))
    (hvalM : ∀ (y : CTorus 3 3 N₁ R.m₁ (k + 1)) (i : Fin 2), ∀ (D' : BgData (R.toStepTower.step k hk N₁ ν β p₁).G' 2)
        (hDh : ∀ y i, D'.h y i = ((R.toStepTower.step k hk N₁ ν β p₁).h₀ i : ℂ)),
      XiCData (R.toStepTower.step k hk N₁ ν β p₁).G' (R.toStepTower.step k hk N₁ ν β p₁).a
        (R.toStepTower.step k hk N₁ ν β p₁).ν (k + 1) 1 R.t D' →
      ((R.toStepTower.step k hk N₁ ν β p₁).withDatum D' hDh).M0C
          (zeroClass 3 3 N₁ R.m₁ k 2 (rhoSep R.m₁)) g y i =
        ((((R.toStepTower.step k hk N₁ ν β p₁).betaU ^ (1 / 2 : ℝ) : ℝ) : ℂ)) *
          ∑ C, cM y i (⟨rawOf D', rawOf_mem_rawSub _⟩, g) C) :
    ∃ F : RawData 3 3 (N₁ * 3 ^ R.m₁) (k + 1) 2 × (Fin 3 → ℂ) →
        (((lvTop N₁ R.m₁ k (rhoSep R.m₁))).Ω 1 × Fin 2 → ℂ) ×
          (((lvTop N₁ R.m₁ k (rhoSep R.m₁))).Ω 1 → ℂ),
      IsRenSol (N := 2) (lvTop N₁ R.m₁ k (rhoSep R.m₁)) (compWeight 3 1) ν (R.t / 2) (R.t / 2)
        R.r₀ (8 * (R.t / 2)) F ∧
      (∀ (z : Torus 3 (N₁ * 3 ^ R.m₁ * 3 ^ (k + 1 - (k + 1)))) (εR : ℝ), 0 ≤ εR → εR ≤ R.r₀ →
        (∃ term, IsLocExp (N := 2) (lvTop N₁ R.m₁ k (rhoSep R.m₁))
          (fun D => XiCOneReal (R.toStepTower.step k hk N₁ ν β p₁).G'
            (R.toStepTower.step k hk N₁ ν β p₁).a (R.toStepTower.step k hk N₁ ν β p₁).ν
            (R.t / 2) D ∧
          ∀ x i, D.h x i = ((((R.toStepTower.step k hk N₁ ν β p₁).h₀ i : ℝ)) : ℂ)) εR
          (renYs (renCube (lvTop N₁ R.m₁ k (rhoSep R.m₁))
          (X1 (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 1 k (fam 1 (blockSite k z)))) (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 1
          (X1 (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 1 k (fam 1 (blockSite k z))) ∪ (Finset.univ.image fun T : Finset (CubeB (d := 3) (L := 3) (N₁ := N₁) (m₁ := R.m₁) (K := k + 1) 1 (k + 1) Set.univ) =>
        (Finset.univ.filter fun x : CTorus 3 3 N₁ R.m₁ (k + 1) => x ∈ sitesOf T)))
          (renDY (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 1) (min (3 / 2 * R.κdec) (min κ κM))
          (1 * ((3 + 6) * (renCK 3 3 2 R.BG R.κ * (R.t / 2)) ^ 2 *
            blockWeight (lvTop N₁ R.m₁ k (rhoSep R.m₁))
              (blockSites 3 3 N₁ R.m₁ (k + 1) k z)) * εR ^ 1)
          (fun D ξ => renC1On (lvTop N₁ R.m₁ k (rhoSep R.m₁)) (compWeight 3 1) ν (R.t / 2)
            (blockSites 3 3 N₁ R.m₁ (k + 1) k z) D.Ψ D.h
            (bgFieldC (lvTop N₁ R.m₁ k (rhoSep R.m₁)) (compWeight 3 1) ν (bgC0 3 3 2) D) ξ) term) ∧
        (∃ term, IsLocExp (N := 2) (lvTop N₁ R.m₁ k (rhoSep R.m₁))
          (fun D => XiCOneReal (R.toStepTower.step k hk N₁ ν β p₁).G'
            (R.toStepTower.step k hk N₁ ν β p₁).a (R.toStepTower.step k hk N₁ ν β p₁).ν
            (R.t / 2) D ∧
          ∀ x i, D.h x i = ((((R.toStepTower.step k hk N₁ ν β p₁).h₀ i : ℝ)) : ℂ)) εR
          (renYs (renCube (lvTop N₁ R.m₁ k (rhoSep R.m₁))
          (X1 (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 1 k (fam 1 (blockSite k z)))) (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 1
          (X1 (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 1 k (fam 1 (blockSite k z))) ∪ (Finset.univ.image fun T : Finset (CubeB (d := 3) (L := 3) (N₁ := N₁) (m₁ := R.m₁) (K := k + 1) 1 (k + 1) Set.univ) =>
        (Finset.univ.filter fun x : CTorus 3 3 N₁ R.m₁ (k + 1) => x ∈ sitesOf T)))
          (renDY (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 1) (min (3 / 2 * R.κdec) (min κ κM))
          (1 * (17 / 32 * ((2 : ℕ) * ((3 + (bgK1 3 3 2 * (xiC1 3 * (R.t / 2)) +
            renCK 3 3 2 R.BG R.κ * cK2 3 3 2 * (8 * (R.t / 2)) * R.r₀ + 2)) *
            (renCK 3 3 2 R.BG R.κ * cK2 3 3 2 * (8 * (R.t / 2))) ^ 2)) *
            blockWeight (lvTop N₁ R.m₁ k (rhoSep R.m₁))
              (blockSites 3 3 N₁ R.m₁ (k + 1) k z)) * εR ^ 2)
          (fun D ξ => renC2On (lvTop N₁ R.m₁ k (rhoSep R.m₁)) (compWeight 3 1)
            (blockSites 3 3 N₁ R.m₁ (k + 1) k z) ξ (renMassU ν ξ)
            (bgMultC (lvTop N₁ R.m₁ k (rhoSep R.m₁)) (compWeight 3 1) ν (bgC0 3 3 2) D +
              (F ((D.Ψ, D.h), ξ)).2) (F ((D.Ψ, D.h), ξ)).1) term) ∧
        (∃ term, IsLocExp (N := 2) (lvTop N₁ R.m₁ k (rhoSep R.m₁))
          (fun D => XiCOneReal (R.toStepTower.step k hk N₁ ν β p₁).G'
            (R.toStepTower.step k hk N₁ ν β p₁).a (R.toStepTower.step k hk N₁ ν β p₁).ν
            (R.t / 2) D ∧
          ∀ x i, D.h x i = ((((R.toStepTower.step k hk N₁ ν β p₁).h₀ i : ℝ)) : ℂ)) εR
          (renYs (renCube (lvTop N₁ R.m₁ k (rhoSep R.m₁))
          (X1 (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 1 k (fam 1 (blockSite k z)))) (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 1
          (X1 (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 1 k (fam 1 (blockSite k z))) ∪ (Finset.univ.image fun T : Finset (CubeB (d := 3) (L := 3) (N₁ := N₁) (m₁ := R.m₁) (K := k + 1) 1 (k + 1) Set.univ) =>
        (Finset.univ.filter fun x : CTorus 3 3 N₁ R.m₁ (k + 1) => x ∈ sitesOf T)))
          (renDY (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 1) (min (3 / 2 * R.κdec) (min κ κM))
          ((hullConst 3 3 (towerDetRate R.κ) (towerDetConst R.κ) *
            Real.exp (c1 3 3 * Real.log 2) * Real.exp (hullRate 3 3 (towerDetRate R.κ)) + B))
          (fun D ξ => if hD : ∀ x i, D.h x i = ((((R.toStepTower.step k hk N₁ ν β p₁).h₀ i : ℝ)) : ℂ)
          then ((R.toStepTower.step k hk N₁ ν β p₁).withDatum
            (renThetaDatum (R.toStepTower.step k hk N₁ ν β p₁) (R.t / 2) D ξ) hD).E0locC
              (zeroClass 3 3 N₁ R.m₁ k 2 (rhoSep R.m₁)) z else 0) term)) ∧
      ∀ (p : ((lvTop N₁ R.m₁ k (rhoSep R.m₁))).Ω 1 × Fin 2) (εR : ℝ), εR ≤ R.r₀ →
        (∃ term, IsLocExp (N := 2) (lvTop N₁ R.m₁ k (rhoSep R.m₁))
          (fun D => XiCOneReal (R.toStepTower.step k hk N₁ ν β p₁).G'
            (R.toStepTower.step k hk N₁ ν β p₁).a (R.toStepTower.step k hk N₁ ν β p₁).ν
            (R.t / 2) D ∧
          ∀ x i, D.h x i = ((((R.toStepTower.step k hk N₁ ν β p₁).h₀ i : ℝ)) : ℂ)) εR
          (renYs (renCube (lvTop N₁ R.m₁ k (rhoSep R.m₁))
          (X1 (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 1 k (fam 1 (p.1 : CTorus 3 3 N₁ R.m₁ (k + 1))))) (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 1
          (X1 (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 1 k (fam 1 (p.1 : CTorus 3 3 N₁ R.m₁ (k + 1)))) ∪ (Finset.univ.image fun T : Finset (CubeB (d := 3) (L := 3) (N₁ := N₁) (m₁ := R.m₁) (K := k + 1) 1 (k + 1) Set.univ) =>
        (Finset.univ.filter fun x : CTorus 3 3 N₁ R.m₁ (k + 1) => x ∈ sitesOf T)))
          (renDY (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 1) (min (3 / 2 * R.κdec) (min κ κM))
          (BM + 1 * (renCK 3 3 2 R.BG R.κ * cK2 3 3 2 * (8 * (R.t / 2))) * εR ^ 1)
          (fun D ξ => (if hD : ∀ x i, D.h x i = ((((R.toStepTower.step k hk N₁ ν β p₁).h₀ i : ℝ)) : ℂ)
          then (((((R.toStepTower.step k hk N₁ ν β p₁).betaU ^ (1 / 2 : ℝ) : ℝ) : ℂ)))⁻¹ *
            ((R.toStepTower.step k hk N₁ ν β p₁).withDatum
              (renThetaDatum (R.toStepTower.step k hk N₁ ν β p₁) (R.t / 2) D ξ) hD).M0C
                (zeroClass 3 3 N₁ R.m₁ k 2 (rhoSep R.m₁)) g (p.1 : CTorus 3 3 N₁ R.m₁ (k + 1)) p.2
          else 0) + (F ((D.Ψ, D.h), ξ)).1 p) term) := by
  obtain ⟨F, Fcut, hF, -, -, I⟩ := renormPhysicalZero_onFibre_half_of_families R hR k hk N₁ h3N hN
    hν0 hν β p₁ hβ Xcut g q hq hg hB hBM cE cM hanE hlocE hbdE hsuppE hvalE hanM hlocM hbdM
    hsuppM hvalM
  have ht := R.t_pos
  have he : 0 < R.t / 2 := by positivity
  have het : R.t / 2 ≤ R.t := by linarith
  have hC := R.flCore_scale_mono k hk N₁ hN hν0 hν he het he het
  have hHB := bgHyp_lv (k := k) R.m₁ hν0 hν
  have hcK := R.toStepTowerRen.renCK_facts.1
  have hr : 0 < R.r₀ := R.r₀_pos
  refine ⟨F, hF, fun z εR hεR0 hεR => ⟨?_, ?_, ?_⟩, fun p εR hεR => ?_⟩
  · exact thm31g_C1_on hHB he hC.small1 (hC.c7le.trans (c7_le_bgC1 3 3 2 R.BG R.κ)) R.r₀_le I
      zero_le_one hcK hεR z
  · exact thm31g_C2_on hHB he R.r₀_le I zero_le_one (by positivity) hcK hεR0 hεR z
  · exact thm31g_Eu_zero_of_fields_on I hr hεR z
  · exact thm31h_zero_of_fields_on I zero_le_one (by positivity) hcK hr hεR p

end Balaban.Inhabited
