/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.SmallField.Def6v2Renorm
public import Balaban.SmallField.Def6v2Inhabited

/-!
# I-6 for Def-6 v2: comparison with the landed class, and a witness below the switch

**Comparison.**  In the complete regime of the landed class (`β_k ν_k > 1`: its running-test mass
is the physical mass, `physMass_eq_bgMass_of_lt`) a member of `Def6.IsSFFamily` is a member of the
second version on the wide domain (`Def6.IsSFFamily.toXi`), and the objects of the second version
at the complete mass are the landed ones:

* `liftDomInfM_complete`, `avgFamilyAM_complete`, `avgDomM_complete`;
* `premisesTermAnisoInf_of_v2`, `renormalization_aniso_of_v2`: the statements of the second
  version, applied to the image of `toXi`, are the landed statements
  `Def6.IsSFFamily.premisesTermAnisoInf`, `Def6.IsSFFamily.renormalization_aniso` in that regime.

Below the switch of the landed class (`β_k ν_k ≤ 1`) there is no comparison: the landed class has
backgrounds of mass `0` and the second version backgrounds of mass `ν_k L^{-2k} > 0`
(`bgMass_ne_sfBgMass_of_le`).

**Witness.**  `renorm_v2_hypotheses_witness`: the hypotheses of the statements of `Def6v2Renorm`
(a member of `IsSFFamily2` on `completeXiDom`, `MomNum`) are jointly satisfiable at a scale below
the switch of the landed class (`k = 1`, `β_1 ν_1 = 7/24 ≤ 1`, any a priori `k₀`), where the landed
running-test mass is `0` and the solver mass of the second version is positive.
-/

@[expose] public section

namespace Balaban.SmallField.Def6v2

open Balaban Balaban.SmallField Balaban.Multiscale Balaban.Background Balaban.Localization
  Balaban.Fluctuation Balaban.SmallField.Def6 Metric Set Filter

variable {d L m₁ k N : ℕ} [NeZero L] {ϱ : ℝ}

section Compare

variable {P : Consts} {β ν a : ℕ → ℝ} {Ek : ℕ → ℝ}
  {Tm : ∀ (N₁ : ℕ) [NeZero N₁], Terms d L N₁ m₁ k N ϱ}
  {ρd : ∀ (N₁ : ℕ) [NeZero N₁], (CTorus d L N₁ m₁ k → Fin N → ℝ) → (Fin N → ℝ) →
    (CTorus d L N₁ m₁ k → Fin N → ℝ) → ℝ}
  {j : ℕ}

/-- **Below the switch of the landed class the two versions have different backgrounds**: for
`β_k ν_k ≤ 1` and `ν_k > 0` the landed running-test mass is `0` and the solver mass of the second
version is `ν_k L^{-2k} > 0`. -/
theorem bgMass_ne_sfBgMass_of_le (k₀ : ℕ) (hβν : β k * ν k ≤ 1) (hν : 0 < ν k) :
    Def6.bgMass L k (β k) (ν k) = 0 ∧ 0 < (⟨k₀, ν⟩ : Regime L).sfBgMass k :=
  ⟨by simp [Def6.bgMass, hβν], Regime.sfBgMass_pos (⟨k₀, ν⟩ : Regime L) hν⟩

variable (hμ : physMass L k (ν k) = Def6.bgMass L k (β k) (ν k)) (k₀ : ℕ)
include hμ

/-- In the complete regime of the landed class the data domain of the lifted family of the second
version is the landed one. -/
theorem liftDomInfM_complete (i₀ : Fin N) :
    liftDomInfM P a ((⟨k₀, ν⟩ : Regime L).sfBgMass k) Tm j ((⟨k₀, ν⟩ : Regime L).ν k) i₀ =
      liftDomInf P β ν a Tm j i₀ := by
  show liftDomInfM P a (physMass L k (ν k)) Tm j (ν k) i₀ = _
  rw [hμ, liftDomInf_eq]

/-- In the complete regime of the landed class the averaged family of the second version is the
landed averaged family. -/
theorem avgFamilyAM_complete (i₀ : Fin N) (νj r : ℝ) :
    avgFamilyAM P a ((⟨k₀, ν⟩ : Regime L).sfBgMass k) Tm j i₀ νj r =
      avgFamilyA P β ν a Tm j i₀ νj r := by
  show avgFamilyAM P a (physMass L k (ν k)) Tm j i₀ νj r = _
  rw [hμ, avgFamilyA_eq]

/-- In the complete regime of the landed class the data domain of the averaged family of the
second version is the landed one. -/
theorem avgDomM_complete (i₀ : Fin N) (νj : ℝ) :
    avgDomM P a ((⟨k₀, ν⟩ : Regime L).sfBgMass k) Tm j i₀ νj = avgDom P β ν a Tm j i₀ νj := by
  show avgDomM P a (physMass L k (ν k)) Tm j i₀ νj = _
  rw [hμ, avgDom_eq]

/-- **Comparison for the premises of the anisotropic I-6**: for a member of the landed class in
its complete regime, the statement `IsSFFamily2.premisesTermAnisoInf` of the second version at the
member `toXi` is the landed statement `Def6.IsSFFamily.premisesTermAnisoInf`. -/
theorem premisesTermAnisoInf_of_v2 (hF : IsSFFamily P β ν a Tm ρd Ek)
    (hS : ∀ (N₁ : ℕ) [NeZero N₁], ∀ j, 1 ≤ j → ∀ hjk : j ≤ k, ∀ X, IsPolyDom P.m₀ j X →
      GsSpec.GsSpecStrong j hjk X ((Tm N₁).gs j X)) (hd : 3 ≤ d) (hL : 3 ≤ L)
    (hϱ : bgR0 d L ≤ ϱ) (hj1 : 1 ≤ j) (hjk : j ≤ k)
    (hsmall : P.eps d L j ≤ (2 * bgK1 d L N + 2) * min (bgC0 d L N) (bgC1 d L N))
    (hκ : aEnt d L + 3 ≤ P.κ) {i₀ i₁ : Fin N} (hne : i₁ ≠ i₀) :
    PremisesTermAniso (liftInfA (L := L) (m₁ := m₁) (k := k) P Tm j i₀ (nuIdeal L k (ν k) j)
      (anisoRadius d L N P j)) i₀ i₁ (nuIdeal L k (ν k) j) (anisoRadius d L N P j) P.E₀ P.κ
      (diamA d L P.m₀ m₁)
      ((c1 d L * ((L : ℝ) ^ (P.m₀ + m₁)) ^ d) ^ 2 * (Nat.factorial 8 * Real.exp 1) *
        K0 d L (P.κ - 2)) (liftDomInf P β ν a Tm j i₀) := by
  have h := (hF.toXi 0 hS hμ).premisesTermAnisoInf hd hL hϱ hj1 hjk hsmall hκ hne
  rw [liftDomInfM_complete hμ 0] at h
  exact h

end Compare

/-- **Comparison for the renormalization theorem**: restricted to the members of the landed class
in its complete regime (`β_k ν_k > 1`; the image of `Def6.IsSFFamily.toXi`), the statement
`IsSFFamily2.renormalization_aniso` of the second version is the landed statement
`Def6.IsSFFamily.renormalization_aniso`, for the landed averaged family `avgFamilyA` and data
domain `avgDom`. -/
theorem renormalization_aniso_of_v2 (d L N m₁ : ℕ) [NeZero L] (P : Consts)
    (hP : P.Admissible d L) (Λ Ksig : ℝ) (hΛ : 1 ≤ Λ) (hKsig : 0 ≤ Ksig) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (k : ℕ) (ϱ : ℝ) (β ν a Ek : ℕ → ℝ)
      (Tm : ∀ (N₁ : ℕ) [NeZero N₁], Terms d L N₁ m₁ k N ϱ)
      (ρd : ∀ (N₁ : ℕ) [NeZero N₁], (CTorus d L N₁ m₁ k → Fin N → ℝ) → (Fin N → ℝ) →
        (CTorus d L N₁ m₁ k → Fin N → ℝ) → ℝ),
      IsSFFamily P β ν a Tm ρd Ek →
      (∀ (N₁ : ℕ) [NeZero N₁], ∀ j, 1 ≤ j → ∀ hjk : j ≤ k, ∀ X, IsPolyDom P.m₀ j X →
        GsSpec.GsSpecStrong j hjk X ((Tm N₁).gs j X)) → 1 < β k * ν k → ∀ (j : ℕ), MomNum d L N k j ϱ P →
      ∀ (i₀ i₁ : Fin N), i₁ ≠ i₀ →
      ∀ (ψ : Site d → Spin N) (b : Spin N) (σ ε K₂ : ℝ),
      DataHypAniso (avgDom P β ν a Tm j i₀ (nuIdeal L k (ν k) j)) (nuIdeal L k (ν k) j) σ ε K₂
        ψ b →
      0 < ε → ε ≤ Λ * anisoRadius d L N P j → 0 < σ → σ ≤ 1 → σ ^ 2 * ε ≤ 1 / 4 →
      nuIdeal L k (ν k) j ≤ σ ^ 2 → K₂ ≤ Ksig * σ ^ (2 - P.α₁) * ε →
      (energy (avgFamilyA P β ν a Tm j i₀ (nuIdeal L k (ν k) j) (anisoRadius d L N P j)) ψ b -
          Aterm (avgFamilyA P β ν a Tm j i₀ (nuIdeal L k (ν k) j) (anisoRadius d L N P j)) i₀
            (nuIdeal L k (ν k) j) ψ =
        ∑' X : (avgFamilyA P β ν a Tm j i₀ (nuIdeal L k (ν k) j)
            (anisoRadius d L N P j)).polys,
          Itw (avgFamilyA P β ν a Tm j i₀ (nuIdeal L k (ν k) j) (anisoRadius d L N P j)) i₀ i₁
            (nuIdeal L k (ν k) j) X.1 ψ b) ∧
      Summable (fun X : (avgFamilyA P β ν a Tm j i₀ (nuIdeal L k (ν k) j)
          (anisoRadius d L N P j)).polys =>
        ‖Itw (avgFamilyA P β ν a Tm j i₀ (nuIdeal L k (ν k) j) (anisoRadius d L N P j)) i₀ i₁
          (nuIdeal L k (ν k) j) X.1 ψ b‖) ∧
      ∑' X : (avgFamilyA P β ν a Tm j i₀ (nuIdeal L k (ν k) j)
            (anisoRadius d L N P j)).polys,
          ‖Itw (avgFamilyA P β ν a Tm j i₀ (nuIdeal L k (ν k) j) (anisoRadius d L N P j)) i₀ i₁
            (nuIdeal L k (ν k) j) X.1 ψ b‖ ≤
        C * P.E₀ * (σ ^ (3 - P.α₁) * (ε / P.eps d L j) ^ 2) ∧
      ∀ (ℓ : ℕ) [NeZero ℓ] (ψT : Torus d ℓ → Spin N),
        ∑ y : Torus d ℓ, (1 / 2 : ℂ) * ∑' z : Site d,
          aCoef (avgFamilyA P β ν a Tm j i₀ (nuIdeal L k (ν k) j) (anisoRadius d L N P j)) i₀
            (nuIdeal L k (ν k) j) z *
          (dot (ψT (y + liftSite ℓ z)) (ψT (y + liftSite ℓ z)) - dot (ψT y) (ψT y)) = 0 := by
  obtain ⟨C, hC0, hC⟩ := IsSFFamily2.renormalization_aniso d L N m₁ P hP Λ Ksig hΛ hKsig
  refine ⟨C, hC0, ?_⟩
  intro k ϱ β ν a Ek Tm ρd hF hS hβν
  have hμ : physMass L k (ν k) = Def6.bgMass L k (β k) (ν k) := physMass_eq_bgMass_of_lt hβν
  have h := hC k ϱ ⟨0, ν⟩ β a Ek Tm _ (hF.toXi 0 hS hμ)
  simp only [avgFamilyAM_complete hμ 0, avgDomM_complete hμ 0] at h
  exact h

/-! ### A witness below the switch -/

/-- **The hypotheses of the statements of the second version are jointly satisfiable below the
switch of the landed class** (`d = L = 3`, `N = 2`, `k = j = 1`, any `m₁`, any a priori `k₀`,
`ϱ ≥ R₀(3, 3)`): a member of `IsSFFamily2` on the wide domain at the complete mass and the
numerical conditions `MomNum`, at a scale with `β_1 ν_1 = 7/24 ≤ 1`, where the running-test mass of
the landed class is `0` and the solver mass of the second version is positive. -/
theorem renorm_v2_hypotheses_witness (m₁ k₀ : ℕ) (ϱ : ℝ) (hϱ : bgR0 3 3 ≤ ϱ) :
    IsSFFamily2 (d := 3) (L := 3) (m₁ := m₁) (k := 1) (N := 2) (ϱ := ϱ)
        (witnessConsts (witnessα₀ 1)) ⟨k₀, witnessν 1⟩ witnessβ witnessa
        (completeXiDom (witnessConsts (witnessα₀ 1)) ⟨k₀, witnessν 1⟩ witnessa)
        (fun N₁ _ => pinTerms 3 3 N₁ m₁ 1 2 ϱ (witnessConsts (witnessα₀ 1)).κ (fun _ => 0))
        (fun N₁ _ => rho2 (witnessConsts (witnessα₀ 1)) ⟨k₀, witnessν 1⟩ witnessβ witnessa
          (pinTerms 3 3 N₁ m₁ 1 2 ϱ (witnessConsts (witnessα₀ 1)).κ (fun _ => 0)) 0)
        (fun _ => 0) ∧
      MomNum 3 3 2 1 1 ϱ (witnessConsts (witnessα₀ 1)) ∧
      witnessβ 1 * witnessν 1 1 ≤ 1 ∧
      Def6.bgMass 3 1 (witnessβ 1) (witnessν 1 1) = 0 ∧
      0 < (⟨k₀, witnessν 1⟩ : Regime 3).sfBgMass 1 := by
  have hβν : witnessβ 1 * witnessν 1 1 ≤ 1 := by
    simp only [witnessβ, witnessν]; norm_num
  have hν : (0 : ℝ) < witnessν 1 1 := by
    simp only [witnessν]; norm_num
  refine ⟨isSFFamily2_xi_witness m₁ 1 k₀ ϱ hϱ (witnessα₀_pos 1),
    momNum_witness 1 1 ϱ hϱ le_rfl le_rfl, hβν, ?_, ?_⟩
  · simp [Def6.bgMass, hβν]
  · exact Regime.sfBgMass_pos (⟨k₀, witnessν 1⟩ : Regime 3) hν

end Balaban.SmallField.Def6v2
