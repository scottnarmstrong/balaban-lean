/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.SmallField.Def6v2BridgeMass
public import Balaban.SmallField.RenormClassTheorem

/-!
# The irrelevance estimate I-6 and the renormalization theorem for Def-6 v2

Scheme A (W2-RESOLVE §4): the second version `IsSFFamily2` of the small-field class on its main
instance `completeXiDom` -- the wide domain `Ξ^c_j(𝔹; 1, ε_j)` in the source `b_j = ν_j h` with
**complete backgrounds at every level** (solver mass `Rg.sfBgMass k = ν_k L^{-2k} > 0`, also for
`k ≤ k₀`, where the landed class used the mass `0`).  The landed statements for `Def6.IsSFFamily`
(`RenormAnisoBridgeInf`, `Def6BridgeInfMoment`, `RenormClassFamily`, `RenormClassTheorem`) are
proved for it, through the reduction `IsSFFamily2.toLanded`:

* `IsSFFamily2.anisoRadiusOK`, `IsSFFamily2.premisesTermAnisoInf`: the premises of the anisotropic
  termwise I-6 for the lifted family `liftInfA` of `T∞`, radius `r_j = anisoRadius ≍ ε_j`;
* `IsSFFamily2.premisesCoreInf`, `IsSFFamily2.sumCondsInf`, `IsSFFamily2.bridgeInf`: the core
  premises and the renormalization conditions (H.5)(1)-(4) for the lifted family `liftInf`;
* `IsSFFamily2.termwise_irrelevant_aniso_class`, `..._eps`: the termwise I-6;
* `IsSFFamily2.premisesTermAnisoAvg`, `sumCondsAvgA`, `premisesTermAvgA`, `energy_sub_Aterm_avgA`,
  `Aterm_torus_sum_avgA`: the Reynolds-averaged family `avgFamilyAM` at the complete mass;
* `IsSFFamily2.termwise_irrelevant_avg_aniso`, `..._scaled`, `IsSFFamily2.renormalization_aniso`,
  `IsSFFamily2.renormalization_aniso_scaled`: the renormalization theorem (Theorem 2.1 /
  Lemma 3.2).

**The constants and the mass.**  In every statement the constant `C` is chosen before the scale
`k`, the regime `Rg` (the a priori `k₀` and the masses `ν_j`) and the coefficients, so it is uniform
in the mass `μ_k = ν_k L^{-2k} ↓ 0`; the radius `anisoRadius = ε_j / ((2 K₁ + 2) 4 N (1 + N rotB N))`,
the counting constant and `diamA` do not involve the mass.  The data domains are sets of `(ψ, b)`
with `b = ν_j h` the source; the mass enters the hypotheses only through `ν_j ≤ σ²` and the
reference point `(e, ν_j e)`.  No constant of the bridge degenerates as `μ_k ↓ 0`.
-/

@[expose] public section

namespace Balaban.SmallField.Def6v2

open Balaban Balaban.SmallField Balaban.Multiscale Balaban.Background Balaban.Localization
  Balaban.Fluctuation Balaban.SmallField.Def6 Metric Set Filter

variable {d L m₁ k N : ℕ} [NeZero L] {ϱ : ℝ}

theorem _root_.Balaban.SmallField.Def6.MomNum.noChi {j : ℕ} {P : Consts}
    (h : MomNum d L N k j ϱ P) : MomNum d L N k j ϱ P.noChi :=
  ⟨h.hd, h.hL, h.hϱ, h.hκ, h.hj1, h.hjk, h.hsmall⟩

section Class

variable {P : Consts} {Rg : Regime L} {β a : ℕ → ℝ} {Ek : ℕ → ℝ}
  {Tm : ∀ (N₁ : ℕ) [NeZero N₁], Terms d L N₁ m₁ k N ϱ}
  {ρd : ∀ (N₁ : ℕ) [NeZero N₁], (CTorus d L N₁ m₁ k → Fin N → ℝ) → (Fin N → ℝ) →
    (CTorus d L N₁ m₁ k → Fin N → ℝ) → ℝ}
  {j : ℕ}

/-! ### The lifted family of `T∞` -/

section Lift

variable (hF : IsSFFamily2 P Rg β a (completeXiDom P Rg a) Tm ρd Ek) (hd : 3 ≤ d) (hL : 3 ≤ L)
  (hϱ : bgR0 d L ≤ ϱ) (hj1 : 1 ≤ j) (hjk : j ≤ k)
  (hsmall : P.eps d L j ≤ (2 * bgK1 d L N + 2) * min (bgC0 d L N) (bgC1 d L N))
include hF hd hL hϱ hj1 hjk hsmall

omit hd hL hϱ hj1 hjk in
/-- The anisotropic radius condition holds for the second version at `r_j = anisoRadius`. -/
theorem IsSFFamily2.anisoRadiusOK (i₀ : Fin N) :
    AnisoRadiusOK d L N P j (anisoRadius d L N P j) :=
  anisoRadius_spec (eps_pos hF.admissible.α₀_pos j) i₀ hsmall

/-- **`IsSFFamily2.premisesTermAnisoInf`**: a member of the second version on the wide domain at
the complete mass supplies the premises of the anisotropic termwise I-6 at each scale
`1 ≤ j ≤ k` -- also below the switch -- for the lifted family `liftInfA` of `T∞`, on `TubeAniso`
with the radius `r_j = anisoRadius ≍ ε_j`, with the constants of the landed
`Def6.IsSFFamily.premisesTermAnisoInf` and the data domain `liftDomInfM` at the complete mass. -/
theorem IsSFFamily2.premisesTermAnisoInf (hκ : aEnt d L + 3 ≤ P.κ) {i₀ i₁ : Fin N}
    (hne : i₁ ≠ i₀) :
    PremisesTermAniso (liftInfA (L := L) (m₁ := m₁) (k := k) P Tm j i₀ (nuIdeal L k (Rg.ν k) j)
      (anisoRadius d L N P j)) i₀ i₁ (nuIdeal L k (Rg.ν k) j) (anisoRadius d L N P j) P.E₀ P.κ
      (diamA d L P.m₀ m₁)
      ((c1 d L * ((L : ℝ) ^ (P.m₀ + m₁)) ^ d) ^ 2 * (Nat.factorial 8 * Real.exp 1) *
        K0 d L (P.κ - 2)) (liftDomInfM P a (Rg.sfBgMass k) Tm j (Rg.ν k) i₀) := by
  obtain ⟨β', ν', hν, hμ, hF'⟩ := hF.toLanded
  rw [← hμ, ← hν]
  exact hF'.premisesTermAnisoInf hd hL hϱ hj1 hjk hsmall hκ hne

/-- **`IsSFFamily2.premisesCoreInf`**: the core premises of the termwise I-6 (every field except
the point-group invariance) for the lifted family `liftInf` of `T∞`, at the isotropic radius
`liftRadius ≍ ε_j²`, for the second version at the complete mass. -/
theorem IsSFFamily2.premisesCoreInf (hκ : aEnt d L + 3 ≤ P.κ) {i₀ i₁ : Fin N} (hne : i₁ ≠ i₀) :
    PremisesCore (liftInf (L := L) (m₁ := m₁) (k := k) P Tm j i₀ (nuIdeal L k (Rg.ν k) j)
      (liftRadius d L N P j)) i₀ i₁ (nuIdeal L k (Rg.ν k) j) (liftRadius d L N P j) P.E₀ P.κ
      (diamA d L P.m₀ m₁)
      ((c1 d L * ((L : ℝ) ^ (P.m₀ + m₁)) ^ d) ^ 2 * (Nat.factorial 8 * Real.exp 1) *
        K0 d L (P.κ - 2)) (liftDomInfM P a (Rg.sfBgMass k) Tm j (Rg.ν k) i₀) := by
  obtain ⟨β', ν', hν, hμ, hF'⟩ := hF.toLanded
  rw [← hμ, ← hν]
  exact hF'.premisesCoreInf hd hL hϱ hκ hj1 hjk hsmall hne

end Lift

section Mom

variable (hF : IsSFFamily2 P Rg β a (completeXiDom P Rg a) Tm ρd Ek)
  (hn : MomNum d L N k j ϱ P) {i₀ i₁ : Fin N} (hne : i₁ ≠ i₀)
include hF hn hne

/-- **`SumConds` for the second version**: a member of the second version on the wide domain at
the complete mass satisfies the renormalization conditions (H.5)(1)-(4) of I-6 on the lifted
family `liftInf` of `T∞` (the conditions are those of `RenormCond`, the same clause in both
versions of the class). -/
theorem IsSFFamily2.sumCondsInf :
    SumConds (liftInf (L := L) (m₁ := m₁) (k := k) P Tm j i₀ (nuIdeal L k (Rg.ν k) j)
      (liftRadius d L N P j)) i₀ i₁ (nuIdeal L k (Rg.ν k) j) := by
  obtain ⟨β', ν', hν, -, hF'⟩ := hF.toLanded
  rw [← hν]
  exact hF'.sumCondsInf hn.noChi hne

/-- **The bridge from the infinite-volume family, second version**: a term family that represents
the class term of `T∞` has the core premises of the termwise I-6 and satisfies `SumConds`. -/
theorem IsSFFamily2.bridgeInf {T : TermFamily d N}
    (hT : RepresentsInf (L := L) (m₁ := m₁) (k := k) T P Tm j i₀ (nuIdeal L k (Rg.ν k) j)
      (liftRadius d L N P j)) :
    PremisesCore T i₀ i₁ (nuIdeal L k (Rg.ν k) j) (liftRadius d L N P j) P.E₀ P.κ
      (diamA d L P.m₀ m₁)
      ((c1 d L * ((L : ℝ) ^ (P.m₀ + m₁)) ^ d) ^ 2 * (Nat.factorial 8 * Real.exp 1) *
        K0 d L (P.κ - 2)) (liftDomInfM P a (Rg.sfBgMass k) Tm j (Rg.ν k) i₀) ∧
    SumConds T i₀ i₁ (nuIdeal L k (Rg.ν k) j) := by
  subst hT
  exact ⟨hF.premisesCoreInf hn.hd hn.hL hn.hϱ hn.hj1 hn.hjk hn.hsmall hn.hκ hne,
    hF.sumCondsInf hn hne⟩

/-! ### The Reynolds-averaged family at the complete mass -/

/-- **`PremisesTermAniso` for the averaged family, second version**: the premises of the
anisotropic termwise I-6 for the Reynolds average over paving offsets of the terms of `T∞` at the
complete mass, on `TubeAniso` of radius `r = anisoRadius`. -/
theorem IsSFFamily2.premisesTermAnisoAvg :
    PremisesTermAniso
      (avgFamilyAM P a (Rg.sfBgMass k) Tm j i₀ (nuIdeal L k (Rg.ν k) j) (anisoRadius d L N P j))
      i₀ i₁ (nuIdeal L k (Rg.ν k) j) (anisoRadius d L N P j) P.E₀ P.κ (diamA d L P.m₀ m₁)
      (((L : ℝ) ^ (P.m₀ + m₁)) ^ d * ((c1 d L * ((L : ℝ) ^ (P.m₀ + m₁)) ^ d) ^ 2 *
        (Nat.factorial 8 * Real.exp 1) * K0 d L (P.κ - 2)))
      (avgDomM P a (Rg.sfBgMass k) Tm j i₀ (nuIdeal L k (Rg.ν k) j)) := by
  obtain ⟨β', ν', hν, hμ, hF'⟩ := hF.toLanded
  rw [← hμ, ← hν]
  exact hF'.premisesTermAnisoAvg hn.noChi hne

/-- **`SumConds` for the averaged family on the anisotropic tube, second version.** -/
theorem IsSFFamily2.sumCondsAvgA :
    SumConds (avgFamilyAM P a (Rg.sfBgMass k) Tm j i₀ (nuIdeal L k (Rg.ν k) j)
      (anisoRadius d L N P j)) i₀ i₁ (nuIdeal L k (Rg.ν k) j) := by
  obtain ⟨β', ν', hν, hμ, hF'⟩ := hF.toLanded
  rw [← hμ, ← hν]
  exact hF'.sumCondsAvgA hn.noChi hne

/-- **The isotropic premises for the averaged family on the anisotropic tube, second version**: at
the radius `r_j²` of the isotropic ball contained in the polydisc, with the point-group
invariance. -/
theorem IsSFFamily2.premisesTermAvgA :
    PremisesTerm (avgFamilyAM P a (Rg.sfBgMass k) Tm j i₀ (nuIdeal L k (Rg.ν k) j)
      (anisoRadius d L N P j)) i₀ i₁
      (nuIdeal L k (Rg.ν k) j) (anisoRadius d L N P j ^ 2) P.E₀ P.κ (diamA d L P.m₀ m₁)
      (((L : ℝ) ^ (P.m₀ + m₁)) ^ d * ((c1 d L * ((L : ℝ) ^ (P.m₀ + m₁)) ^ d) ^ 2 *
        (Nat.factorial 8 * Real.exp 1) * K0 d L (P.κ - 2)))
      (avgDomM P a (Rg.sfBgMass k) Tm j i₀ (nuIdeal L k (Rg.ν k) j)) := by
  obtain ⟨β', ν', hν, hμ, hF'⟩ := hF.toLanded
  rw [← hμ, ← hν]
  exact hF'.premisesTermAvgA hn.noChi hne

/-- **The termwise decomposition for the averaged family, second version** (Lemma 3.2):
`𝓔(y;ψ,b) - A_y(ψ) = Σ_X I(y,X;ψ,b)`. -/
theorem IsSFFamily2.energy_sub_Aterm_avgA {ψ : Site d → Spin N} {b : Spin N} {σ ε K₂ : ℝ}
    (dat : DataHyp (avgDomM P a (Rg.sfBgMass k) Tm j i₀ (nuIdeal L k (Rg.ν k) j))
      (nuIdeal L k (Rg.ν k) j) σ ε K₂ ψ b) :
    energy (avgFamilyAM P a (Rg.sfBgMass k) Tm j i₀ (nuIdeal L k (Rg.ν k) j)
          (anisoRadius d L N P j)) ψ b -
        Aterm (avgFamilyAM P a (Rg.sfBgMass k) Tm j i₀ (nuIdeal L k (Rg.ν k) j)
          (anisoRadius d L N P j)) i₀ (nuIdeal L k (Rg.ν k) j) ψ =
      ∑' X : (avgFamilyAM P a (Rg.sfBgMass k) Tm j i₀ (nuIdeal L k (Rg.ν k) j)
          (anisoRadius d L N P j)).polys,
        Itw (avgFamilyAM P a (Rg.sfBgMass k) Tm j i₀ (nuIdeal L k (Rg.ν k) j)
          (anisoRadius d L N P j)) i₀ i₁ (nuIdeal L k (Rg.ν k) j) X.1 ψ b := by
  obtain ⟨hr0, hr1, -⟩ := hF.anisoRadiusOK hn.hsmall i₀
  exact energy_sub_Aterm_eq_tsum_Itw (hF.premisesTermAvgA hn hne) (hF.sumCondsAvgA hn hne)
    (pow_pos hr0 2) hF.admissible.E₀_nonneg (diamA_nonneg d L P.m₀ m₁) dat

/-- **`Σ_y A_y = 0` on every torus** for the averaged family of the second version. -/
theorem IsSFFamily2.Aterm_torus_sum_avgA (ℓ : ℕ) [NeZero ℓ] (ψT : Torus d ℓ → Spin N) :
    ∑ y : Torus d ℓ, (1 / 2 : ℂ) * ∑' z : Site d,
      aCoef (avgFamilyAM P a (Rg.sfBgMass k) Tm j i₀ (nuIdeal L k (Rg.ν k) j)
        (anisoRadius d L N P j)) i₀ (nuIdeal L k (Rg.ν k) j) z *
      (dot (ψT (y + liftSite ℓ z)) (ψT (y + liftSite ℓ z)) - dot (ψT y) (ψT y)) = 0 := by
  obtain ⟨hr0, hr1, -⟩ := hF.anisoRadiusOK hn.hsmall i₀
  exact Aterm_torus_sum_tw (hF.premisesTermAvgA hn hne) (hF.sumCondsAvgA hn hne)
    (pow_pos hr0 2) hF.admissible.E₀_nonneg ℓ ψT

end Mom

end Class

/-! ### The termwise I-6 for the second version -/

/-- **Lemma 3.2 (iii) for the second version of the class on the anisotropic domain** (P1
Lemma 3.8 / Proposition 3.10 termwise, I6-ANISO (2.7)), with complete backgrounds at every level:
for a member of `IsSFFamily2` on the wide domain at the complete mass, at every scale
`1 ≤ j ≤ k` with `ε_j ≤ (2 K₁ + 2) min (c₀, c₁)`, every polymer `X` of `T∞` containing the origin
and every configuration with the properties `DataHypAniso` on the data domain,
`‖I(y,X)‖ ≤ C E₀ e^{-(κ-1) d_j(X)} σ^{3-α₁} (ε/r_j)²`, `r_j = anisoRadius ≍ ε_j`.  The constant `C`
depends on `d, N, L, m₁` and the class constants only: not on `k, j`, the regime (the a priori `k₀`
and the masses `ν_j`, in particular not on the size of the mass `μ_k = ν_k L^{-2k} > 0`), the
polymer or the data. -/
theorem IsSFFamily2.termwise_irrelevant_aniso_class (d L N m₁ : ℕ) [NeZero L] (P : Consts)
    (hP : P.Admissible d L) (Λ Ksig : ℝ) (hΛ : 1 ≤ Λ) (hKsig : 0 ≤ Ksig) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (k : ℕ) (ϱ : ℝ) (Rg : Regime L) (β a Ek : ℕ → ℝ)
      (Tm : ∀ (N₁ : ℕ) [NeZero N₁], Terms d L N₁ m₁ k N ϱ)
      (ρd : ∀ (N₁ : ℕ) [NeZero N₁], (CTorus d L N₁ m₁ k → Fin N → ℝ) → (Fin N → ℝ) →
        (CTorus d L N₁ m₁ k → Fin N → ℝ) → ℝ),
      IsSFFamily2 P Rg β a (completeXiDom P Rg a) Tm ρd Ek → 3 ≤ d → 3 ≤ L → bgR0 d L ≤ ϱ →
      aEnt d L + 3 ≤ P.κ →
      ∀ (j : ℕ), 1 ≤ j → j ≤ k →
      P.eps d L j ≤ (2 * bgK1 d L N + 2) * min (bgC0 d L N) (bgC1 d L N) →
      ∀ (i₀ i₁ : Fin N), i₁ ≠ i₀ →
      ∀ (ψ : Site d → Spin N) (b : Spin N) (σ ε K₂ : ℝ),
      DataHypAniso (liftDomInfM P a (Rg.sfBgMass k) Tm j (Rg.ν k) i₀) (nuIdeal L k (Rg.ν k) j)
        σ ε K₂ ψ b →
      ∀ (X : Finset (Site d)), (0 : Site d) ∈ X →
      InfPoly (L := L) (m₁ := m₁) (k := k) P.m₀ j X →
      0 < ε → ε ≤ Λ * anisoRadius d L N P j → 0 < σ → σ ≤ 1 → σ ^ 2 * ε ≤ 1 / 4 →
      nuIdeal L k (Rg.ν k) j ≤ σ ^ 2 → K₂ ≤ Ksig * σ ^ (2 - P.α₁) * ε →
      ‖Itw (liftInfA (L := L) (m₁ := m₁) (k := k) P Tm j i₀ (nuIdeal L k (Rg.ν k) j)
          (anisoRadius d L N P j)) i₀ i₁ (nuIdeal L k (Rg.ν k) j) X ψ b‖ ≤
        C * P.E₀ * Real.exp (-(P.κ - 1) * dInf L m₁ k P.m₀ j X) *
          (σ ^ (3 - P.α₁) * (ε / anisoRadius d L N P j) ^ 2) := by
  obtain ⟨C, hC0, hC⟩ :=
    IsSFFamily.termwise_irrelevant_aniso_class d L N m₁ P.noChi hP.noChi Λ Ksig hΛ hKsig
  refine ⟨C, hC0, ?_⟩
  intro k ϱ Rg β a Ek Tm ρd hF
  obtain ⟨β', ν', hν, hμ, hF'⟩ := hF.toLanded
  rw [← hμ, ← hν]
  exact hC k ϱ β' ν' a Ek Tm _ hF'

/-- **The termwise I-6 for the second version in the source form**: with the class radius `ε_j`,
`‖I(y,X)‖ ≤ C E₀ σ^{3-α₁} (ε/ε_j)² e^{-(κ-1) d_j(X)}` (I6-ANISO (2.7); `ε = ε_k`). -/
theorem IsSFFamily2.termwise_irrelevant_aniso_class_eps (d L N m₁ : ℕ) [NeZero L] (P : Consts)
    (hP : P.Admissible d L) (Λ Ksig : ℝ) (hΛ : 1 ≤ Λ) (hKsig : 0 ≤ Ksig) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (k : ℕ) (ϱ : ℝ) (Rg : Regime L) (β a Ek : ℕ → ℝ)
      (Tm : ∀ (N₁ : ℕ) [NeZero N₁], Terms d L N₁ m₁ k N ϱ)
      (ρd : ∀ (N₁ : ℕ) [NeZero N₁], (CTorus d L N₁ m₁ k → Fin N → ℝ) → (Fin N → ℝ) →
        (CTorus d L N₁ m₁ k → Fin N → ℝ) → ℝ),
      IsSFFamily2 P Rg β a (completeXiDom P Rg a) Tm ρd Ek → 3 ≤ d → 3 ≤ L → bgR0 d L ≤ ϱ →
      aEnt d L + 3 ≤ P.κ →
      ∀ (j : ℕ), 1 ≤ j → j ≤ k →
      P.eps d L j ≤ (2 * bgK1 d L N + 2) * min (bgC0 d L N) (bgC1 d L N) →
      ∀ (i₀ i₁ : Fin N), i₁ ≠ i₀ →
      ∀ (ψ : Site d → Spin N) (b : Spin N) (σ ε K₂ : ℝ),
      DataHypAniso (liftDomInfM P a (Rg.sfBgMass k) Tm j (Rg.ν k) i₀) (nuIdeal L k (Rg.ν k) j)
        σ ε K₂ ψ b →
      ∀ (X : Finset (Site d)), (0 : Site d) ∈ X →
      InfPoly (L := L) (m₁ := m₁) (k := k) P.m₀ j X →
      0 < ε → ε ≤ Λ * anisoRadius d L N P j → 0 < σ → σ ≤ 1 → σ ^ 2 * ε ≤ 1 / 4 →
      nuIdeal L k (Rg.ν k) j ≤ σ ^ 2 → K₂ ≤ Ksig * σ ^ (2 - P.α₁) * ε →
      ‖Itw (liftInfA (L := L) (m₁ := m₁) (k := k) P Tm j i₀ (nuIdeal L k (Rg.ν k) j)
          (anisoRadius d L N P j)) i₀ i₁ (nuIdeal L k (Rg.ν k) j) X ψ b‖ ≤
        C * P.E₀ * Real.exp (-(P.κ - 1) * dInf L m₁ k P.m₀ j X) *
          (σ ^ (3 - P.α₁) * (ε / P.eps d L j) ^ 2) := by
  obtain ⟨C, hC0, hC⟩ :=
    IsSFFamily.termwise_irrelevant_aniso_class_eps d L N m₁ P.noChi hP.noChi Λ Ksig hΛ hKsig
  refine ⟨C, hC0, ?_⟩
  intro k ϱ Rg β a Ek Tm ρd hF
  obtain ⟨β', ν', hν, hμ, hF'⟩ := hF.toLanded
  rw [← hμ, ← hν]
  exact hC k ϱ β' ν' a Ek Tm _ hF'

/-- **The termwise I-6 for the averaged family of the second version on the anisotropic domain**,
in the source form: `‖I(y,X)‖ ≤ C E₀ σ^{3-α₁} (ε/ε_j)² e^{-(κ-1) d_j(X)}`, with `C` independent
of `k, j`, the regime, the polymer and the data. -/
theorem IsSFFamily2.termwise_irrelevant_avg_aniso (d L N m₁ : ℕ) [NeZero L] (P : Consts)
    (hP : P.Admissible d L) (Λ Ksig : ℝ) (hΛ : 1 ≤ Λ) (hKsig : 0 ≤ Ksig) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (k : ℕ) (ϱ : ℝ) (Rg : Regime L) (β a Ek : ℕ → ℝ)
      (Tm : ∀ (N₁ : ℕ) [NeZero N₁], Terms d L N₁ m₁ k N ϱ)
      (ρd : ∀ (N₁ : ℕ) [NeZero N₁], (CTorus d L N₁ m₁ k → Fin N → ℝ) → (Fin N → ℝ) →
        (CTorus d L N₁ m₁ k → Fin N → ℝ) → ℝ),
      IsSFFamily2 P Rg β a (completeXiDom P Rg a) Tm ρd Ek → ∀ (j : ℕ), MomNum d L N k j ϱ P →
      ∀ (i₀ i₁ : Fin N), i₁ ≠ i₀ →
      ∀ (ψ : Site d → Spin N) (b : Spin N) (σ ε K₂ : ℝ),
      DataHypAniso (avgDomM P a (Rg.sfBgMass k) Tm j i₀ (nuIdeal L k (Rg.ν k) j))
        (nuIdeal L k (Rg.ν k) j) σ ε K₂ ψ b →
      ∀ (X : Finset (Site d)),
      X ∈ (avgFamilyAM P a (Rg.sfBgMass k) Tm j i₀ (nuIdeal L k (Rg.ν k) j)
        (anisoRadius d L N P j)).polys →
      0 < ε → ε ≤ Λ * anisoRadius d L N P j → 0 < σ → σ ≤ 1 → σ ^ 2 * ε ≤ 1 / 4 →
      nuIdeal L k (Rg.ν k) j ≤ σ ^ 2 → K₂ ≤ Ksig * σ ^ (2 - P.α₁) * ε →
      ‖Itw (avgFamilyAM P a (Rg.sfBgMass k) Tm j i₀ (nuIdeal L k (Rg.ν k) j)
          (anisoRadius d L N P j)) i₀ i₁ (nuIdeal L k (Rg.ν k) j) X ψ b‖ ≤
        C * P.E₀ * Real.exp (-(P.κ - 1) * avgDist L m₁ k P j X) *
          (σ ^ (3 - P.α₁) * (ε / P.eps d L j) ^ 2) := by
  obtain ⟨C, hC0, hC⟩ :=
    IsSFFamily.termwise_irrelevant_avg_aniso d L N m₁ P.noChi hP.noChi Λ Ksig hΛ hKsig
  refine ⟨C, hC0, ?_⟩
  intro k ϱ Rg β a Ek Tm ρd hF j hn
  obtain ⟨β', ν', hν, hμ, hF'⟩ := hF.toLanded
  rw [← hμ, ← hν]
  exact hC k ϱ β' ν' a Ek Tm _ hF' j hn.noChi

/-- **The scaled termwise I-6 for the averaged family of the second version, all scales**: with
`σ = C₀ s`, `ε/ε_j ≤ K_R s^{(d-2)/2 - γ}` and `α₃ = 1 - 2γ - α₁`, for every `0 < s ≤ 1`:
`‖I(y,X)‖ ≤ C_I E₀ s^{d+α₃} e^{-(κ-1) d_j(X)}`. -/
theorem IsSFFamily2.termwise_irrelevant_avg_aniso_scaled (d L N m₁ : ℕ) [NeZero L] (P : Consts)
    (hP : P.Admissible d L) (Λ Ksig γ C₀ KR : ℝ) (hΛ : 1 ≤ Λ) (hKsig : 0 ≤ Ksig) (hC₀ : 0 < C₀)
    (hα₃ : 0 ≤ (d : ℝ) + (1 - 2 * γ - P.α₁)) :
    ∃ CI : ℝ, 0 ≤ CI ∧ ∀ (k : ℕ) (ϱ : ℝ) (Rg : Regime L) (β a Ek : ℕ → ℝ)
      (Tm : ∀ (N₁ : ℕ) [NeZero N₁], Terms d L N₁ m₁ k N ϱ)
      (ρd : ∀ (N₁ : ℕ) [NeZero N₁], (CTorus d L N₁ m₁ k → Fin N → ℝ) → (Fin N → ℝ) →
        (CTorus d L N₁ m₁ k → Fin N → ℝ) → ℝ),
      IsSFFamily2 P Rg β a (completeXiDom P Rg a) Tm ρd Ek → ∀ (j : ℕ), MomNum d L N k j ϱ P →
      ∀ (i₀ i₁ : Fin N), i₁ ≠ i₀ →
      ∀ (ψ : Site d → Spin N) (b : Spin N) (s σ ε K₂ : ℝ),
      DataHypAniso (avgDomM P a (Rg.sfBgMass k) Tm j i₀ (nuIdeal L k (Rg.ν k) j))
        (nuIdeal L k (Rg.ν k) j) σ ε K₂ ψ b →
      ∀ (X : Finset (Site d)),
      X ∈ (avgFamilyAM P a (Rg.sfBgMass k) Tm j i₀ (nuIdeal L k (Rg.ν k) j)
        (anisoRadius d L N P j)).polys →
      0 < s → s ≤ 1 → σ = C₀ * s → ε / P.eps d L j ≤ KR * s ^ (((d : ℝ) - 2) / 2 - γ) →
      0 < ε → ε ≤ Λ * anisoRadius d L N P j → σ ^ 2 * ε ≤ 1 / 4 →
      nuIdeal L k (Rg.ν k) j ≤ σ ^ 2 → K₂ ≤ Ksig * σ ^ (2 - P.α₁) * ε →
      ‖Itw (avgFamilyAM P a (Rg.sfBgMass k) Tm j i₀ (nuIdeal L k (Rg.ν k) j)
          (anisoRadius d L N P j)) i₀ i₁ (nuIdeal L k (Rg.ν k) j) X ψ b‖ ≤
        CI * P.E₀ * s ^ ((d : ℝ) + (1 - 2 * γ - P.α₁)) *
          Real.exp (-(P.κ - 1) * avgDist L m₁ k P j X) := by
  obtain ⟨CI, hCI0, hCI⟩ := IsSFFamily.termwise_irrelevant_avg_aniso_scaled d L N m₁ P.noChi
    hP.noChi Λ Ksig γ C₀ KR hΛ hKsig hC₀ hα₃
  refine ⟨CI, hCI0, ?_⟩
  intro k ϱ Rg β a Ek Tm ρd hF j hn
  obtain ⟨β', ν', hν, hμ, hF'⟩ := hF.toLanded
  rw [← hμ, ← hν]
  exact hCI k ϱ β' ν' a Ek Tm _ hF' j hn.noChi

/-! ### The renormalization theorem for the second version -/

/-- **The renormalization theorem I-6 for the second version of the class on the anisotropic
domain** (SMALLFIELD.md Theorem 2.1, FLUCTUATION.md Lemma 3.2), with complete backgrounds at every
level (Scheme A): for a member of `IsSFFamily2` on the wide domain `Ξ^c_j` at the complete mass
`μ_k = ν_k L^{-2k} > 0`, the Reynolds average `T = avgFamilyAM` over paving offsets of the terms of
`T∞` on the anisotropic tube of radius `r_j = anisoRadius ≍ ε_j`, and data `(ψ, b)` of the
anisotropic data domain (`DataHypAniso`):

* `ℰ(y;ψ,b) - A_y(ψ) = Σ_X I(y,X;ψ,b)`;
* `Σ_X ‖I(y,X;ψ,b)‖ ≤ C E₀ σ^{3-α₁} (ε/ε_j)²` (`ε = ε_k`), the series being summable;
* `Σ_y A_y = 0` on every torus `ℤ^d / ℓℤ^d`.

The constant `C` is independent of `k, j`, the regime `Rg` (the a priori index `k₀` and the masses
`ν_j`), the coefficients, the torus sequence and the data: it is uniform as the mass `μ_k ↓ 0`. -/
theorem IsSFFamily2.renormalization_aniso (d L N m₁ : ℕ) [NeZero L] (P : Consts)
    (hP : P.Admissible d L) (Λ Ksig : ℝ) (hΛ : 1 ≤ Λ) (hKsig : 0 ≤ Ksig) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (k : ℕ) (ϱ : ℝ) (Rg : Regime L) (β a Ek : ℕ → ℝ)
      (Tm : ∀ (N₁ : ℕ) [NeZero N₁], Terms d L N₁ m₁ k N ϱ)
      (ρd : ∀ (N₁ : ℕ) [NeZero N₁], (CTorus d L N₁ m₁ k → Fin N → ℝ) → (Fin N → ℝ) →
        (CTorus d L N₁ m₁ k → Fin N → ℝ) → ℝ),
      IsSFFamily2 P Rg β a (completeXiDom P Rg a) Tm ρd Ek → ∀ (j : ℕ), MomNum d L N k j ϱ P →
      ∀ (i₀ i₁ : Fin N), i₁ ≠ i₀ →
      ∀ (ψ : Site d → Spin N) (b : Spin N) (σ ε K₂ : ℝ),
      DataHypAniso (avgDomM P a (Rg.sfBgMass k) Tm j i₀ (nuIdeal L k (Rg.ν k) j))
        (nuIdeal L k (Rg.ν k) j) σ ε K₂ ψ b →
      0 < ε → ε ≤ Λ * anisoRadius d L N P j → 0 < σ → σ ≤ 1 → σ ^ 2 * ε ≤ 1 / 4 →
      nuIdeal L k (Rg.ν k) j ≤ σ ^ 2 → K₂ ≤ Ksig * σ ^ (2 - P.α₁) * ε →
      (energy (avgFamilyAM P a (Rg.sfBgMass k) Tm j i₀ (nuIdeal L k (Rg.ν k) j)
            (anisoRadius d L N P j)) ψ b -
          Aterm (avgFamilyAM P a (Rg.sfBgMass k) Tm j i₀ (nuIdeal L k (Rg.ν k) j)
            (anisoRadius d L N P j)) i₀ (nuIdeal L k (Rg.ν k) j) ψ =
        ∑' X : (avgFamilyAM P a (Rg.sfBgMass k) Tm j i₀ (nuIdeal L k (Rg.ν k) j)
            (anisoRadius d L N P j)).polys,
          Itw (avgFamilyAM P a (Rg.sfBgMass k) Tm j i₀ (nuIdeal L k (Rg.ν k) j)
            (anisoRadius d L N P j)) i₀ i₁ (nuIdeal L k (Rg.ν k) j) X.1 ψ b) ∧
      Summable (fun X : (avgFamilyAM P a (Rg.sfBgMass k) Tm j i₀ (nuIdeal L k (Rg.ν k) j)
          (anisoRadius d L N P j)).polys =>
        ‖Itw (avgFamilyAM P a (Rg.sfBgMass k) Tm j i₀ (nuIdeal L k (Rg.ν k) j)
          (anisoRadius d L N P j)) i₀ i₁ (nuIdeal L k (Rg.ν k) j) X.1 ψ b‖) ∧
      ∑' X : (avgFamilyAM P a (Rg.sfBgMass k) Tm j i₀ (nuIdeal L k (Rg.ν k) j)
            (anisoRadius d L N P j)).polys,
          ‖Itw (avgFamilyAM P a (Rg.sfBgMass k) Tm j i₀ (nuIdeal L k (Rg.ν k) j)
            (anisoRadius d L N P j)) i₀ i₁ (nuIdeal L k (Rg.ν k) j) X.1 ψ b‖ ≤
        C * P.E₀ * (σ ^ (3 - P.α₁) * (ε / P.eps d L j) ^ 2) ∧
      ∀ (ℓ : ℕ) [NeZero ℓ] (ψT : Torus d ℓ → Spin N),
        ∑ y : Torus d ℓ, (1 / 2 : ℂ) * ∑' z : Site d,
          aCoef (avgFamilyAM P a (Rg.sfBgMass k) Tm j i₀ (nuIdeal L k (Rg.ν k) j)
            (anisoRadius d L N P j)) i₀ (nuIdeal L k (Rg.ν k) j) z *
          (dot (ψT (y + liftSite ℓ z)) (ψT (y + liftSite ℓ z)) - dot (ψT y) (ψT y)) = 0 := by
  obtain ⟨C, hC0, hC⟩ :=
    IsSFFamily.renormalization_aniso d L N m₁ P.noChi hP.noChi Λ Ksig hΛ hKsig
  refine ⟨C, hC0, ?_⟩
  intro k ϱ Rg β a Ek Tm ρd hF j hn
  obtain ⟨β', ν', hν, hμ, hF'⟩ := hF.toLanded
  rw [← hμ, ← hν]
  exact hC k ϱ β' ν' a Ek Tm _ hF' j hn.noChi

/-- **The renormalization theorem I-6 for the second version on the anisotropic domain, scaled
form (3.1), all scales**: with `σ = C₀ s`, `ε/ε_j ≤ K_R s^{(d-2)/2 - γ}`, `α₃ = 1 - 2γ - α₁`, for
every `0 < s ≤ 1`: `ℰ(y;ψ,b) - A_y = Σ_X I(y,X)` and `Σ_X ‖I(y,X)‖ ≤ C_I E₀ s^{d+α₃}`; and
`Σ_y A_y = 0` on every torus.  The constant `C_I` is independent of `k, j`, the regime and the
data (uniform as the mass `μ_k ↓ 0`). -/
theorem IsSFFamily2.renormalization_aniso_scaled (d L N m₁ : ℕ) [NeZero L] (P : Consts)
    (hP : P.Admissible d L) (Λ Ksig γ C₀ KR : ℝ) (hΛ : 1 ≤ Λ) (hKsig : 0 ≤ Ksig) (hC₀ : 0 < C₀)
    (hα₃ : 0 ≤ (d : ℝ) + (1 - 2 * γ - P.α₁)) :
    ∃ CI : ℝ, 0 ≤ CI ∧ ∀ (k : ℕ) (ϱ : ℝ) (Rg : Regime L) (β a Ek : ℕ → ℝ)
      (Tm : ∀ (N₁ : ℕ) [NeZero N₁], Terms d L N₁ m₁ k N ϱ)
      (ρd : ∀ (N₁ : ℕ) [NeZero N₁], (CTorus d L N₁ m₁ k → Fin N → ℝ) → (Fin N → ℝ) →
        (CTorus d L N₁ m₁ k → Fin N → ℝ) → ℝ),
      IsSFFamily2 P Rg β a (completeXiDom P Rg a) Tm ρd Ek → ∀ (j : ℕ), MomNum d L N k j ϱ P →
      ∀ (i₀ i₁ : Fin N), i₁ ≠ i₀ →
      ∀ (ψ : Site d → Spin N) (b : Spin N) (s σ ε K₂ : ℝ),
      DataHypAniso (avgDomM P a (Rg.sfBgMass k) Tm j i₀ (nuIdeal L k (Rg.ν k) j))
        (nuIdeal L k (Rg.ν k) j) σ ε K₂ ψ b →
      0 < s → s ≤ 1 → σ = C₀ * s → ε / P.eps d L j ≤ KR * s ^ (((d : ℝ) - 2) / 2 - γ) →
      0 < ε → ε ≤ Λ * anisoRadius d L N P j → σ ^ 2 * ε ≤ 1 / 4 →
      nuIdeal L k (Rg.ν k) j ≤ σ ^ 2 → K₂ ≤ Ksig * σ ^ (2 - P.α₁) * ε →
      (energy (avgFamilyAM P a (Rg.sfBgMass k) Tm j i₀ (nuIdeal L k (Rg.ν k) j)
            (anisoRadius d L N P j)) ψ b -
          Aterm (avgFamilyAM P a (Rg.sfBgMass k) Tm j i₀ (nuIdeal L k (Rg.ν k) j)
            (anisoRadius d L N P j)) i₀ (nuIdeal L k (Rg.ν k) j) ψ =
        ∑' X : (avgFamilyAM P a (Rg.sfBgMass k) Tm j i₀ (nuIdeal L k (Rg.ν k) j)
            (anisoRadius d L N P j)).polys,
          Itw (avgFamilyAM P a (Rg.sfBgMass k) Tm j i₀ (nuIdeal L k (Rg.ν k) j)
            (anisoRadius d L N P j)) i₀ i₁ (nuIdeal L k (Rg.ν k) j) X.1 ψ b) ∧
      Summable (fun X : (avgFamilyAM P a (Rg.sfBgMass k) Tm j i₀ (nuIdeal L k (Rg.ν k) j)
          (anisoRadius d L N P j)).polys =>
        ‖Itw (avgFamilyAM P a (Rg.sfBgMass k) Tm j i₀ (nuIdeal L k (Rg.ν k) j)
          (anisoRadius d L N P j)) i₀ i₁ (nuIdeal L k (Rg.ν k) j) X.1 ψ b‖) ∧
      ∑' X : (avgFamilyAM P a (Rg.sfBgMass k) Tm j i₀ (nuIdeal L k (Rg.ν k) j)
            (anisoRadius d L N P j)).polys,
          ‖Itw (avgFamilyAM P a (Rg.sfBgMass k) Tm j i₀ (nuIdeal L k (Rg.ν k) j)
            (anisoRadius d L N P j)) i₀ i₁ (nuIdeal L k (Rg.ν k) j) X.1 ψ b‖ ≤
        CI * P.E₀ * s ^ ((d : ℝ) + (1 - 2 * γ - P.α₁)) ∧
      ∀ (ℓ : ℕ) [NeZero ℓ] (ψT : Torus d ℓ → Spin N),
        ∑ y : Torus d ℓ, (1 / 2 : ℂ) * ∑' z : Site d,
          aCoef (avgFamilyAM P a (Rg.sfBgMass k) Tm j i₀ (nuIdeal L k (Rg.ν k) j)
            (anisoRadius d L N P j)) i₀ (nuIdeal L k (Rg.ν k) j) z *
          (dot (ψT (y + liftSite ℓ z)) (ψT (y + liftSite ℓ z)) - dot (ψT y) (ψT y)) = 0 := by
  obtain ⟨CI, hCI0, hCI⟩ := IsSFFamily.renormalization_aniso_scaled d L N m₁ P.noChi hP.noChi
    Λ Ksig γ C₀ KR hΛ hKsig hC₀ hα₃
  refine ⟨CI, hCI0, ?_⟩
  intro k ϱ Rg β a Ek Tm ρd hF j hn
  obtain ⟨β', ν', hν, hμ, hF'⟩ := hF.toLanded
  rw [← hμ, ← hν]
  exact hCI k ϱ β' ν' a Ek Tm _ hF' j hn.noChi

end Balaban.SmallField.Def6v2
