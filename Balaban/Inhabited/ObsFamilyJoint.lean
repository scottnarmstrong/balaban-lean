/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.ObsCoeffFamily
public import Balaban.Inhabited.ObsCoeffFibreValue
public import Balaban.Inhabited.Thm31bFromTower
public import Balaban.Inhabited.ObsCoeffLocal
public import Balaban.Inhabited.ObsCoeffExactSites

/-!
# The coefficient family of the observable: analyticity, bound, support and value together

One family `obsCoeffParam` (one activity, one amplitude, one `Ev`) carries all four properties:
analyticity on `physVq`, the bound, the support in the polymer domains containing the root cube of
the observable site, and the value `M0C` of the observable at every chart datum of the fibre and
every source in the ball.

For each site `(y, i)`, after the labels and the activity are fixed for all sites, one `Ev` is chosen; that site's `obsCoeffParam` has the analyticity, bound, support, locality and fibre-value clauses. No `Ev` common to all sites is asserted.
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation
  Balaban.Localization Balaban.Localization.LevelPair Balaban.Localization.I5Inhabited
  Balaban.Polymer Balaban.SmallField.Def6 Balaban.Inhabited.LevelStep MeasureTheory Metric

open Classical in
/-- **The observable coefficient family at the tower: all properties for one choice of
witnesses.**  The labels, `ε_H`, the activity `A`, the amplitude and `Ev` are chosen once; for them:
the sharp-hat family `Ev` is analytic, local in the raw datum and bounded; at every datum of the
chart `ObsMarkHalf` and `ObsRayIdentity` hold; both `ParamMarkFamily` records exist; for every
finite set `T'` of cubes the first-order terms, the kernel sum, the remainder coefficient and
`obsCoeffParam … θ T'` are analytic on `physVq S S.a₁ S.ν T.t q`, `obsCoeffParam` is bounded by
`(B₁ + B₂) e^{-λ dExt T'}` there and vanishes unless `T'` contains the root cube of the observable
site and its sites form a polymer domain; the coefficient is local: `θ, θ'` of `physVq` whose raw
data agree on `thickSet S.G' (sitesOf T')` and whose sources agree on `sitesOf T'` give the same
`obsCoeffParam … T'`; equality of `physRestrict (sitesOf T') (physIncl 2 S ·)` also gives the same
coefficient (exact locality on the sites themselves); and at every chart datum `D` of the fibre and every source `g` with
`‖g‖₁ < q`, `M0C … g y i = √β_U ∑_{T'} obsCoeffParam … (rawOf D, g) T'`.
For each site `(y, i)`, after the labels and the activity are fixed for all sites, one `Ev` is chosen; that site's `obsCoeffParam` has the analyticity, bound, support, locality and fibre-value clauses. No `Ev` common to all sites is asserted. -/
theorem obsFamily_full_fromTower {κmin : ℝ} (T : StepTower κmin) {A₁ : ℝ} (hA : 0 < A₁) (p : ℕ)
    {CR s : ℝ} (hCR : 0 < CR) (hs0 : 0 < s) (hs : s < 1 / 2) :
    ∃ (β₀ CE CF : ℝ), 3 ≤ β₀ ∧ 0 < CE ∧ 0 < CF ∧
      ∀ (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁] (h3N : 3 ∣ N₁), 5 < N₁ →
      ∀ ν : ℝ, 0 < ν → ν * 3 ^ (2 * (k + 1)) ≤ 1 → ∀ β : ℝ, β₀ ≤ β →
      ∀ p₁ : ℝ, 0 < p₁ → p₁ ≤ pLog A₁ p (β * 3 ^ k) → ∀ q : ℝ, 0 < q → q ≤ 1 →
      ∀ (Dsc : StepScaleData T k hk N₁ ν β p₁)
        (S : StepSetting 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)),
        S = T.step k hk N₁ ν β p₁ → ∀ hp : 0 < S.p₁,
      ∃ (Lb : Type) (_ : Fintype Lb)
        (Lab : CubeLabels (d := 3) (L := 3) (N₁ := N₁) (m₁ := T.m₁) (K := k + 1) 1 (k + 1)
          Set.univ Lb) (εH : ℝ) (hεH : 0 < εH)
        (A : physParam 2 S → ℂ → LabelAct Lab (S.blockSplit 1 hp).Ωb εH (2 * T.κdec - 1) T.κ0
          (K0 3 3 T.κ0 + 1)),
        2 * εH ≤ CE * (Real.log (β * 3 ^ k)) ^ (3 * p) / Real.sqrt (β * 3 ^ k) +
          q * CF * (Real.log (β * 3 ^ k)) ^ p / Real.sqrt (β * 3 ^ k) ∧
        ∀ (y : CTorus 3 3 N₁ T.m₁ (k + 1)) (i : Fin 2)
          (hdj : ∀ Y ∈ obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y),
            IsDj 1 (k + 1) Y),
        ∃ hR : 0 ≤ obsRg CR s (p : ℝ) (β * 3 ^ k),
          1 < obsRg CR s (p : ℝ) (β * 3 ^ k) ∧
          obsRg CR s (p : ℝ) (β * 3 ^ k) * max (εH + εH) εH ≤
            stepTheta 3 3 ((K0 3 3 T.κ0 + 1) + (K0 3 3 T.κ0 + 1) + K0 3 3 T.κ0 + K0 3 3 T.κ0)
              (2 * T.κdec - 1) T.κ0 T.κ' ∧
          ∃ Ev : Set (CTorus 3 3 N₁ T.m₁ (k + 1)) →
        RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2 × (unitPts S.G' × Fin 2 → ℂ) → ℂ,
      (∀ Y, AnalyticOnNhd ℂ (Ev Y) (XiCRaw S.G' (compWeight 3 1) ν (k + 1) 1 T.t ×ˢ
          {ψh : unitPts S.G' × Fin 2 → ℂ | ∀ p, ‖ψh p‖ ≤ lvCpsi T.κ T.t (β * 3 ^ k)})) ∧
      (∀ Y, ∀ u ∈ XiCRaw S.G' (compWeight 3 1) ν (k + 1) 1 T.t ×ˢ
          {ψh : unitPts S.G' × Fin 2 → ℂ | ∀ p, ‖ψh p‖ ≤ lvCpsi T.κ T.t (β * 3 ^ k)},
        ∀ u' ∈ XiCRaw S.G' (compWeight 3 1) ν (k + 1) 1 T.t ×ˢ
          {ψh : unitPts S.G' × Fin 2 → ℂ | ∀ p, ‖ψh p‖ ≤ lvCpsi T.κ T.t (β * 3 ^ k)},
        AgHatDir S.hG' Y u u' → Ev Y u = Ev Y u') ∧
      (∀ Y, ∀ u ∈ XiCRaw S.G' (compWeight 3 1) ν (k + 1) 1 T.t ×ˢ
          {ψh : unitPts S.G' × Fin 2 → ℂ | ∀ p, ‖ψh p‖ ≤ lvCpsi T.κ T.t (β * 3 ^ k)},
        ‖Ev Y u‖ ≤ (cK2' 3 3 2 (famConst 3 3 T.BG₂ T.κ) * T.t) *
          Real.exp (-(2 * T.κdec) * treeLenCovOne 1 (k + 1) Y)) ∧
      (∀ D : BgData S.G' 2, XiCData S.G' (compWeight 3 1) ν (k + 1) 1 T.t D →
        ObsMarkHalf S 1 hp Ev D (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y))
          (obsLab (Lab.sum Lab) hdj) (lvCpsi T.κ T.t (β * 3 ^ k))
          (cK2' 3 3 2 (famConst 3 3 T.BG₂ T.κ) * T.t) (2 * T.κdec - 1) T.κ0
          (cK2' 3 3 2 (famConst 3 3 T.BG₂ T.κ) * T.t / (lvCpsi T.κ T.t (β * 3 ^ k)))
          (2 * T.κdec) (rootCube (m₀ := 1) (blockIndex y)) ∧
        ObsRayIdentity S 1 hp
          (fun ψh => svec (lvLow N₁ T.m₁ k (rhoSep T.m₁))
            (flFieldOne S.G' (lvLow N₁ T.m₁ k (rhoSep T.m₁)) T.BG₂ T.κ 1 ν D
              (hatLift S.G' 1 ν S.hG' ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) D ψh)) y i) Ev D
          (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y))) ∧
      ((∀ m : ObsMarkIdx S, Nonempty (ParamMarkFamily (S.blockSplit 1 hp).μ
        (obsLab (Lab.sum Lab) hdj)
        (fun θ t => tiltActObs A (show 3 ^ 1 ∣ N₁ by simpa using h3N) T.κ0_ent hεH.le hdj (le_refl _)
          (obsRg CR s (p : ℝ) (β * 3 ^ k)) hR (ball (0 : ℂ) (3 / 2)) θ t 1)
        (fun _ : Unit => obsY1 1 S (Lb ⊕ Lb) (obsDomains S (LocalCover.nbhdF 1 y) 1 k
          (LocalCover.fam 1 y)) m)
        (fun _ _ _ => blockMarkC S 1 hp m.1 m.2) (2 * T.κdec - 1)
        (fun _ => S.p₁ * Real.exp ((2 * T.κdec - 1) * (obsLab (Lab.sum Lab) hdj).dl
          (obsY1 1 S (Lb ⊕ Lb) (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y)) m)))
        (physVq S S.a₁ S.ν T.t q) (ball (0 : ℂ) (3 / 2)) (physCarrier S 1 hp))) ∧
      Nonempty (ParamMarkFamily (S.blockSplit 1 hp).μ (obsLab (Lab.sum Lab) hdj)
        (fun θ t => tiltActObs A (show 3 ^ 1 ∣ N₁ by simpa using h3N) T.κ0_ent hεH.le hdj (le_refl _)
          (obsRg CR s (p : ℝ) (β * 3 ^ k)) hR (ball (0 : ℂ) (3 / 2)) θ t 1)
        (obsRemLab (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y))
          (fun Y => Sum.inl (Sum.inr Y))
          (obsY0 1 (Lb ⊕ Lb) (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y))
            (rootCube (m₀ := 1) (blockIndex y))))
        (obsGrFam S 1 hp Ev (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y))
          (XiCRaw S.G' (compWeight 3 1) ν (k + 1) 1 T.t)) (2 * T.κdec - 1)
        (fun _ => 8 * (cK2' 3 3 2 (famConst 3 3 T.BG₂ T.κ) * T.t) *
          (S.p₁ / lvCpsi T.κ T.t (β * 3 ^ k)) ^ 2)
        (physVq S S.a₁ S.ν T.t q) (ball (0 : ℂ) (3 / 2)) (physCarrier S 1 hp))) ∧
      (∀ T' : Finset (CubeB (d := 3) (L := 3) (N₁ := N₁) (m₁ := T.m₁) (K := k + 1) 1 (k + 1)
        Set.univ),
      ((∀ (m : ObsMarkIdx S) (S' : Finset (CubeB (d := 3) (L := 3) (N₁ := N₁) (m₁ := T.m₁)
        (K := k + 1) 1 (k + 1) Set.univ)),
      AnalyticOnNhd ℂ (fun θ => markIntTerm (S.blockSplit 1 hp).μ ((fun θ t σ => tiltActObs A (show 3 ^ 1 ∣ N₁ by simpa using h3N) T.κ0_ent hεH.le hdj (le_refl _)
        (obsRg CR s (p : ℝ) (β * 3 ^ k)) hR (ball (0 : ℂ) (3 / 2)) θ t σ) θ)
        (obsY1 1 S (Lb ⊕ Lb) (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y)) m) (blockMarkC S 1 hp m.1 m.2) S')
        (physVq S S.a₁ S.ν T.t q)) ∧
    AnalyticOnNhd ℂ (fun θ => kernelMarkSum
      (fun m T'' => obsHker (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y)) (fun Y => hatCoeff (Ev Y)
        (θ.1 : RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2) (obsUnitVec S m)) 1 T'')
      (fun m S' => markIntTerm (S.blockSplit 1 hp).μ ((fun θ t σ => tiltActObs A (show 3 ^ 1 ∣ N₁ by simpa using h3N) T.κ0_ent hεH.le hdj (le_refl _)
        (obsRg CR s (p : ℝ) (β * 3 ^ k)) hR (ball (0 : ℂ) (3 / 2)) θ t σ) θ) (obsY1 1 S (Lb ⊕ Lb) (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y)) m)
        (blockMarkC S 1 hp m.1 m.2) S') T') (physVq S S.a₁ S.ν T.t q) ∧
    AnalyticOnNhd ℂ (fun θ => gsumCoeff (S.blockSplit 1 hp).μ (obsLab (Lab.sum Lab) hdj)
      (fun t => (fun θ t σ => tiltActObs A (show 3 ^ 1 ∣ N₁ by simpa using h3N) T.κ0_ent hεH.le hdj (le_refl _)
        (obsRg CR s (p : ℝ) (β * 3 ^ k)) hR (ball (0 : ℂ) (3 / 2)) θ t σ) θ t 1)
      (obsRemLab (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y)) (fun Y => Sum.inl (Sum.inr Y))
        (obsY0 1 (Lb ⊕ Lb) (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y)) (rootCube (m₀ := 1) (blockIndex y))))
      (obsGrFam S 1 hp Ev (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y)) (XiCRaw S.G' (compWeight 3 1) ν (k + 1) 1 T.t) θ) T')
      (physVq S S.a₁ S.ν T.t q) ∧
    AnalyticOnNhd ℂ (fun θ => obsCoeffParam (S.blockSplit 1 hp).μ (fun θ t σ => tiltActObs A (show 3 ^ 1 ∣ N₁ by simpa using h3N) T.κ0_ent hεH.le hdj (le_refl _)
        (obsRg CR s (p : ℝ) (β * 3 ^ k)) hR (ball (0 : ℂ) (3 / 2)) θ t σ)
      (fun m => obsY1 1 S (Lb ⊕ Lb) (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y)) m) (fun m => blockMarkC S 1 hp m.1 m.2)
      (fun θ m T'' => obsHker (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y)) (fun Y => hatCoeff (Ev Y)
        (θ.1 : RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2) (obsUnitVec S m)) 1 T'')
      (obsRemLab (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y)) (fun Y => Sum.inl (Sum.inr Y))
        (obsY0 1 (Lb ⊕ Lb) (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y)) (rootCube (m₀ := 1) (blockIndex y))))
      (fun θ => obsGrFam S 1 hp Ev (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y)) (XiCRaw S.G' (compWeight 3 1) ν (k + 1) 1 T.t) θ) θ T')
      (physVq S S.a₁ S.ν T.t q) ∧
      (∀ θ ∈ (physVq S S.a₁ S.ν T.t q),
        ‖obsCoeffParam (S.blockSplit 1 hp).μ
      (fun θ t σ => tiltActObs A (show 3 ^ 1 ∣ N₁ by simpa using h3N) T.κ0_ent hεH.le hdj (le_refl _)
        (obsRg CR s (p : ℝ) (β * 3 ^ k)) hR (ball (0 : ℂ) (3 / 2)) θ t σ)
      (fun m => obsY1 1 S (Lb ⊕ Lb) (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y)) m) (fun m => blockMarkC S 1 hp m.1 m.2)
      (fun θ m T'' => obsHker (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y))
        (fun Y => hatCoeff (Ev Y) (θ.1 : RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2)
          (obsUnitVec S m)) 1 T'')
      (obsRemLab (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y))
        (fun Y => Sum.inl (Sum.inr Y))
        (obsY0 1 (Lb ⊕ Lb) (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y))
          (rootCube (m₀ := 1) (blockIndex y))))
      (fun θ => obsGrFam S 1 hp Ev (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y)) (XiCRaw S.G' (compWeight 3 1) ν (k + 1) 1 T.t) θ) θ T'‖ ≤
      ((cK2' 3 3 2 (famConst 3 3 T.BG₂ T.κ) * T.t / lvCpsi T.κ T.t (β * 3 ^ k)) *
          (CPE 3 3 ((K0 3 3 T.κ0 + 1) + (K0 3 3 T.κ0 + 1) + K0 3 3 T.κ0 + K0 3 3 T.κ0)
            (2 * T.κdec - 1) T.κ0 T.κ' * S.p₁ / (obsRg CR s (p : ℝ) (β * 3 ^ k))) *
          (((2 * 3 ^ (3 * (1 + T.m₁ + 1)) : ℕ) : ℝ) * c1 3 3) *
          ((K0 3 3 T.κ0 + 1) + (K0 3 3 T.κ0 + 1) + K0 3 3 T.κ0 + K0 3 3 T.κ0) ^ 2 *
          Real.exp ((min (2 * T.κdec) T.κ' - T.κ0) * cG 3 3) +
        CPE 3 3 ((K0 3 3 T.κ0 + 1) + (K0 3 3 T.κ0 + 1) + K0 3 3 T.κ0 + K0 3 3 T.κ0)
            (2 * T.κdec - 1) T.κ0 T.κ' *
          (∑ r, 8 * (cK2' 3 3 2 (famConst 3 3 T.BG₂ T.κ) * T.t) *
            (S.p₁ / lvCpsi T.κ T.t (β * 3 ^ k)) ^ 2 * Real.exp (-T.κ0 *
            (obsLab (Lab.sum Lab) hdj).dl (obsRemLab (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y)) (fun Y => Sum.inl (Sum.inr Y))
              (obsY0 1 (Lb ⊕ Lb) (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y)) (rootCube (m₀ := 1) (blockIndex y))) r)))) *
        Real.exp (-(min (min (2 * T.κdec) T.κ' - T.κ0 - 1) T.κ') * dExt T')) ∧
      (∀ θ ∈ (physVq S S.a₁ S.ν T.t q),
        obsCoeffParam (S.blockSplit 1 hp).μ
      (fun θ t σ => tiltActObs A (show 3 ^ 1 ∣ N₁ by simpa using h3N) T.κ0_ent hεH.le hdj (le_refl _)
        (obsRg CR s (p : ℝ) (β * 3 ^ k)) hR (ball (0 : ℂ) (3 / 2)) θ t σ)
      (fun m => obsY1 1 S (Lb ⊕ Lb) (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y)) m) (fun m => blockMarkC S 1 hp m.1 m.2)
      (fun θ m T'' => obsHker (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y))
        (fun Y => hatCoeff (Ev Y) (θ.1 : RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2)
          (obsUnitVec S m)) 1 T'')
      (obsRemLab (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y))
        (fun Y => Sum.inl (Sum.inr Y))
        (obsY0 1 (Lb ⊕ Lb) (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y))
          (rootCube (m₀ := 1) (blockIndex y))))
      (fun θ => obsGrFam S 1 hp Ev (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y)) (XiCRaw S.G' (compWeight 3 1) ν (k + 1) 1 T.t) θ) θ T' ≠ 0 →
        rootCube (m₀ := 1) (blockIndex y) ∈ T' ∧ IsPolyDom 1 (k + 1) (sitesOf T')) ∧
      (∀ θ ∈ (physVq S S.a₁ S.ν T.t q), ∀ θ' ∈ (physVq S S.a₁ S.ν T.t q),
        agreeOn (thickSet S.G' (sitesOf T')) (θ.1 : RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2)
          (θ'.1 : RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2) → (∀ x ∈ sitesOf T', θ.2 x = θ'.2 x) →
        obsCoeffParam (S.blockSplit 1 hp).μ
      (fun θ t σ => tiltActObs A (show 3 ^ 1 ∣ N₁ by simpa using h3N) T.κ0_ent hεH.le hdj (le_refl _)
        (obsRg CR s (p : ℝ) (β * 3 ^ k)) hR (ball (0 : ℂ) (3 / 2)) θ t σ)
      (fun m => obsY1 1 S (Lb ⊕ Lb) (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y)) m) (fun m => blockMarkC S 1 hp m.1 m.2)
      (fun θ m T'' => obsHker (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y))
        (fun Y => hatCoeff (Ev Y) (θ.1 : RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2)
          (obsUnitVec S m)) 1 T'')
      (obsRemLab (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y))
        (fun Y => Sum.inl (Sum.inr Y))
        (obsY0 1 (Lb ⊕ Lb) (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y))
          (rootCube (m₀ := 1) (blockIndex y))))
      (fun θ => obsGrFam S 1 hp Ev (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y)) (XiCRaw S.G' (compWeight 3 1) ν (k + 1) 1 T.t) θ) θ T' =
        obsCoeffParam (S.blockSplit 1 hp).μ
      (fun θ t σ => tiltActObs A (show 3 ^ 1 ∣ N₁ by simpa using h3N) T.κ0_ent hεH.le hdj (le_refl _)
        (obsRg CR s (p : ℝ) (β * 3 ^ k)) hR (ball (0 : ℂ) (3 / 2)) θ t σ)
      (fun m => obsY1 1 S (Lb ⊕ Lb) (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y)) m) (fun m => blockMarkC S 1 hp m.1 m.2)
      (fun θ m T'' => obsHker (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y))
        (fun Y => hatCoeff (Ev Y) (θ.1 : RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2)
          (obsUnitVec S m)) 1 T'')
      (obsRemLab (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y))
        (fun Y => Sum.inl (Sum.inr Y))
        (obsY0 1 (Lb ⊕ Lb) (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y))
          (rootCube (m₀ := 1) (blockIndex y))))
      (fun θ => obsGrFam S 1 hp Ev (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y)) (XiCRaw S.G' (compWeight 3 1) ν (k + 1) 1 T.t) θ) θ' T') ∧
      (∀ θ ∈ (physVq S S.a₁ S.ν T.t q), ∀ θ' ∈ (physVq S S.a₁ S.ν T.t q),
        physRestrict (N := 2) (sitesOf T') (physIncl 2 S θ) =
          physRestrict (sitesOf T') (physIncl 2 S θ') →
        obsCoeffParam (S.blockSplit 1 hp).μ
      (fun θ t σ => tiltActObs A (show 3 ^ 1 ∣ N₁ by simpa using h3N) T.κ0_ent hεH.le hdj (le_refl _)
        (obsRg CR s (p : ℝ) (β * 3 ^ k)) hR (ball (0 : ℂ) (3 / 2)) θ t σ)
      (fun m => obsY1 1 S (Lb ⊕ Lb) (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y)) m) (fun m => blockMarkC S 1 hp m.1 m.2)
      (fun θ m T'' => obsHker (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y))
        (fun Y => hatCoeff (Ev Y) (θ.1 : RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2)
          (obsUnitVec S m)) 1 T'')
      (obsRemLab (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y))
        (fun Y => Sum.inl (Sum.inr Y))
        (obsY0 1 (Lb ⊕ Lb) (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y))
          (rootCube (m₀ := 1) (blockIndex y))))
      (fun θ => obsGrFam S 1 hp Ev (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y)) (XiCRaw S.G' (compWeight 3 1) ν (k + 1) 1 T.t) θ) θ T' =
        obsCoeffParam (S.blockSplit 1 hp).μ
      (fun θ t σ => tiltActObs A (show 3 ^ 1 ∣ N₁ by simpa using h3N) T.κ0_ent hεH.le hdj (le_refl _)
        (obsRg CR s (p : ℝ) (β * 3 ^ k)) hR (ball (0 : ℂ) (3 / 2)) θ t σ)
      (fun m => obsY1 1 S (Lb ⊕ Lb) (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y)) m) (fun m => blockMarkC S 1 hp m.1 m.2)
      (fun θ m T'' => obsHker (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y))
        (fun Y => hatCoeff (Ev Y) (θ.1 : RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2)
          (obsUnitVec S m)) 1 T'')
      (obsRemLab (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y))
        (fun Y => Sum.inl (Sum.inr Y))
        (obsY0 1 (Lb ⊕ Lb) (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y))
          (rootCube (m₀ := 1) (blockIndex y))))
      (fun θ => obsGrFam S 1 hp Ev (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y)) (XiCRaw S.G' (compWeight 3 1) ν (k + 1) 1 T.t) θ) θ' T'))) ∧
      ∀ (D : BgData S.G' 2) (hDh : ∀ y i, D.h y i = (S.h₀ i : ℂ)),
        XiCData S.G' S.a S.ν (k + 1) 1 T.t D →
        ∀ g : Fld 3 3 N₁ T.m₁ (k + 1) 2, ∑ x', ∑ i', ‖g x' i'‖ < q →
          (S.withDatum D hDh).M0C (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) g y i =
            ((S.betaU ^ (1 / 2 : ℝ) : ℝ) : ℂ) * ∑ T', obsCoeffParam (S.blockSplit 1 hp).μ
      (fun θ t σ => tiltActObs A (show 3 ^ 1 ∣ N₁ by simpa using h3N) T.κ0_ent hεH.le hdj (le_refl _)
        (obsRg CR s (p : ℝ) (β * 3 ^ k)) hR (ball (0 : ℂ) (3 / 2)) θ t σ)
      (fun m => obsY1 1 S (Lb ⊕ Lb) (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y)) m) (fun m => blockMarkC S 1 hp m.1 m.2)
      (fun θ m T'' => obsHker (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y))
        (fun Y => hatCoeff (Ev Y) (θ.1 : RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2)
          (obsUnitVec S m)) 1 T'')
      (obsRemLab (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y))
        (fun Y => Sum.inl (Sum.inr Y))
        (obsY0 1 (Lb ⊕ Lb) (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y))
          (rootCube (m₀ := 1) (blockIndex y))))
      (fun θ => obsGrFam S 1 hp Ev (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y)) (XiCRaw S.G' (compWeight 3 1) ν (k + 1) 1 T.t) θ)
      ((⟨rawOf D, rawOf_mem_rawSub _⟩ : rawSub 2 S.G'), g) T'
    := by
  classical
  have hK0 := T.marks_K0_pos
  have hc1 : 0 < c1 3 3 := by linarith [one_le_c1 3 3]
  have hKo : 0 < (K0 3 3 T.κ0 + 1) + (K0 3 3 T.κ0 + 1) + K0 3 3 T.κ0 + K0 3 3 T.κ0 := by linarith
  have hΘ : 0 < stepTheta 3 3 ((K0 3 3 T.κ0 + 1) + (K0 3 3 T.κ0 + 1) + K0 3 3 T.κ0 + K0 3 3 T.κ0)
      (2 * T.κdec - 1) T.κ0 T.κ' :=
    div_pos one_pos (mul_pos (mul_pos (mul_pos (by norm_num) (pow_pos hKo 3)) hc1)
      (Real.exp_pos _))
  obtain ⟨β₀, CE, CF, h3, hCE, hCF, hmain⟩ := obsTiltLabels_local_fromTower T hA p hCR hs0 hs hΘ
  refine ⟨β₀, CE, CF, h3, hCE, hCF, fun k hk N₁ _ h3N hN ν hνpos hν β hβ p₁ hp0 hp₁ q hq0 hq1
    Dsc S hS hp => ?_⟩
  obtain ⟨Lb, instLb, Lab, εH, hεH, A, hAloc, hAlocExact, hεb, hae, hrest⟩ := hmain k hk N₁ h3N hN ν hνpos hν β hβ p₁
    hp0 hp₁ q hq0 hq1 Dsc S hS hp (Kc := K0 3 3 T.κ0 + 1) (by linarith)
  refine ⟨Lb, instLb, Lab, εH, hεH, A, hεb, fun y i hdj => ?_⟩
  obtain ⟨-, -, A3, A4, A5⟩ := hrest hdj (le_refl _)
  obtain ⟨h1, hεΘ, hR, -⟩ := A5 0 (by simpa using hq0)
  refine ⟨hR, h1, hεΘ, ?_⟩
  have hhol := (A4 _ hR h1).1
  have hcont := (A4 _ hR h1).2
  have hσ := fun e he => (A3 _ hR h1 e he).2.1
  have hzero := fun e he => (A3 _ hR h1 e he).2.2
  subst hS
  let S := T.step k hk N₁ ν β p₁
  obtain ⟨Ev, ha, hdRaw, hb, hD⟩ := obsEv_fromTower_rawY T k hk N₁ ν β p₁ hN hνpos hν
    Dsc hp y i (Lab.sum Lab)
  have hd : ∀ Y, ∀ u ∈ XiCRaw S.G' (compWeight 3 1) ν (k + 1) 1 T.t ×ˢ
        {ψh : unitPts S.G' × Fin 2 → ℂ | ∀ p, ‖ψh p‖ ≤ lvCpsi T.κ T.t (β * 3 ^ k)},
      ∀ u' ∈ XiCRaw S.G' (compWeight 3 1) ν (k + 1) 1 T.t ×ˢ
        {ψh : unitPts S.G' × Fin 2 → ℂ | ∀ p, ‖ψh p‖ ≤ lvCpsi T.κ T.t (β * 3 ^ k)},
      AgHatDir S.hG' Y u u' → Ev Y u = Ev Y u' := by
    intro Y u hu u' hu' h
    exact hdRaw Y u hu u' hu' (agreeOn_mono (fun x hx => Or.inl hx) h.1) h.2
  have fam := obsFamilies_of_Ev T k hk N₁ ν β p₁ Dsc _ rfl hp y h3N Lab hεH A
    hdj (le_refl _) _ hR hνpos hν hhol hcont Ev ha hb
  have hT' := fun T' => obsCoeffParam_analytic_of_Ev T k hk N₁ ν β p₁ Dsc _ rfl hp y
    h3N Lab hεH A hdj (le_refl _) _ hR hνpos hν h1 (le_refl _) hhol hcont hεΘ
    Ev ha hd hb T'
  refine ⟨Ev, ha, hd, hb, hD, fam, ⟨fun T' => ⟨(hT' T').1, (hT' T').2.1, (hT' T').2.2.1,
    (hT' T').2.2.2, fun θ hθ => ?_, fun θ hθ => ?_, fun θ hθ θ' hθ' hr hg => ?_,
    fun θ hθ θ' hθ' hπ => ?_⟩, ?_⟩⟩
  · exact obsCoeffParam_bound_of_Ev T k hk N₁ ν β p₁ Dsc S rfl hp y h3N Lab hεH A hdj (le_refl _) _
      hR h1 (le_refl _) hσ hzero hεΘ Ev ha hd hb (fun D hD' => (hD D hD').1) θ hθ T'
  · exact obsCoeffParam_support_of_Ev T k hk N₁ ν β p₁ Dsc S rfl hp y h3N Lab hεH A hdj (le_refl _) _
      hR h1 (le_refl _) hεΘ Ev ha hd hb (fun D hD' => (hD D hD').1) θ hθ T'
  · exact obsCoeffParam_local_of_Ev T k hk N₁ ν β p₁ Dsc S rfl hp y h3N Lab hεH A hdj (le_refl _) _
      hR hAloc Ev hd hθ hθ' T' hr hg
  · exact obsCoeffParam_local_of_Ev_physRestrict T k hk N₁ ν β p₁ Dsc S rfl hp y h3N Lab
      hεH A hdj (le_refl _) _ hR Ev hAlocExact hdRaw hθ hθ' T' hπ
  intro D hDh hDx g hg
  have hN3 : 3 ^ 1 ∣ N₁ := by simpa using h3N
  have hDx' : XiCData (T.step k hk N₁ ν β p₁).G' (compWeight 3 1) ν (k + 1) 1 T.t D := hDx
  obtain ⟨hhalf, hid⟩ := hD D hDx'
  have hmemθ : ((⟨rawOf D, rawOf_mem_rawSub _⟩ : rawSub 2 (T.step k hk N₁ ν β p₁).G'), g) ∈
      physVq (T.step k hk N₁ ν β p₁) (T.step k hk N₁ ν β p₁).a₁ (T.step k hk N₁ ν β p₁).ν T.t q :=
    ⟨⟨⟨D, hDx, rfl⟩, lt_of_lt_of_le hg hq1⟩, hg⟩
  let S := T.step k hk N₁ ν β p₁
  obtain ⟨hholt, hholσ, hzero⟩ := A3 (obsRg CR s (p : ℝ) (β * 3 ^ k)) hR h1 _ hmemθ
  have hν0 := hνpos.le
  obtain ⟨R0⟩ := Dsc.ray
  have hr0 := Dsc.r_pos
  have hcψ0 := Dsc.cψ_pos
  have hC := Dsc.core
  have hHB := bgHyp_lv (k := k) T.m₁ hν0 hν
  have hmem := compWeight_three_mem hk
  have hCs : 0 ≤ covSupConstC 3 3 2 (compWeight 3 (1 : ℝ) k) T.κ :=
    covSupConstC_nonneg (by norm_num) (by norm_num) (by linarith [hmem.1]) T.κ
  have hbU : 0 ≤ S.betaU := R0.betaU_pos.le
  have hβ3 : 3 ≤ β := le_trans h3 hβ
  have hpc : 2 * p₁ < lvCpsi T.κ T.t (β * 3 ^ k) := by
    have : 0 < lvR T.κ T.t (β * 3 ^ k) p₁ * p₁ := mul_pos hr0 hp
    linarith [Dsc.ray_margin]
  have hδp : Real.sqrt ((2 : ℕ) : ℝ) *
      (S.betaU ^ (-(1 / 2 : ℝ)) *
        (covSupConstC 3 3 2 (compWeight 3 (1 : ℝ) k) T.κ * (2 * p₁))) < T.t := by
    refine lt_of_le_of_lt ?_ Dsc.fl_radius
    rw [S.norm_betaU_rpow (show 0 ≤ β by linarith)]
    have hb := Real.rpow_nonneg hbU (-(1 / 2 : ℝ))
    have hs := Real.sqrt_nonneg ((2 : ℕ) : ℝ)
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hpc.le hCs) hb) hs
  obtain ⟨Jr⟩ := S.nonempty_jointRep (pp := 2 * p₁) hC T.large_block T.dom_margin T.coer_margin
    T.δc_small one_pos T.c7_cap (R := 2) (by norm_num) T.bg1_cap (by
      show 0 ≤ β
      linarith) (by linarith) hδp
  have hCh : 0 ≤ cK2' 3 3 2 (famConst 3 3 T.BG₂ T.κ) * T.t / lvCpsi T.κ T.t (β * 3 ^ k) :=
    div_nonneg (cK2'_famConst_mul_t_pos T k hk N₁ ν β p₁ Dsc).le hcψ0.le
  have hκ0h : T.κ0 ≤ 2 * T.κdec := by
    have := T.marks_κ0_le_κH; linarith
  have hεpos : 0 < obsRg CR s (p : ℝ) (β * 3 ^ k) * max (εH + εH) εH :=
    mul_pos (by linarith) (lt_of_lt_of_le (by linarith) (le_max_left _ _))
  obtain ⟨I, hI⟩ := obsRecord_of_halves S 1 hp (Lab.sum Lab) _ hdj hN3 Ev D _ _ hCh T.κ0_ent
    hκ0h hhalf hid
    (fun r x => (S.withDatum D hDh).WoneC (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) 1 x +
      (S.withDatum D hDh).WtwoC (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) g r x)
    (ball (0 : ℂ) (3 / 2)) h1 isOpen_ball (fun r hr => seg_mem_ball_three_halves r hr)
    subset_rfl
    (fun t σ => tiltActObs A hN3 T.κ0_ent hεH.le hdj
      (Kobs := (K0 3 3 T.κ0 + 1) + (K0 3 3 T.κ0 + 1) + K0 3 3 T.κ0 + K0 3 3 T.κ0) le_rfl
      (obsRg CR s (p : ℝ) (β * 3 ^ k)) hR (ball (0 : ℂ) (3 / 2))
      ((⟨rawOf D, rawOf_mem_rawSub _⟩ : rawSub 2 S.G'), g) t σ)
    hholt (fun r hr => hholσ _ (seg_mem_ball_three_halves r hr)) (fun r _ => hzero _)
    (fun r hr => by
      filter_upwards [hae] with x hx
      exact (hx D hDh hDx' g hg r hr hdj (Kobs := (K0 3 3 T.κ0 + 1) + (K0 3 3 T.κ0 + 1) +
        K0 3 3 T.κ0 + K0 3 3 T.κ0) le_rfl).2 _ hR h1)
    (by linarith) hεpos T.marks_hκ' T.marks_κ0_le_κ' T.marks_hκ hεΘ
  let hI' := ObsMarks.toConsumer (Jr.withDatum D hDh) hC one_pos hHB T.c7_cap (R := 2) le_rfl
    T.bg1_cap T.t_cap T.bg0_cap T.cK2_cap T.cK2'_cap T.large_block T.dom_margin T.coer_margin
    T.δc_small hcψ0.le Dsc.fl_radius hp Dsc.p_lt hpc hDx g y i (S.blockSplit 1 hp) I
  have hval := (thm31b_coeff hI' (κb := min hI'.κh hI'.κ' - hI'.κ0 - 1) le_rfl).1
  have hM : (S.withDatum D hDh).M0C (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) g y i =
      ((S.betaU ^ (1 / 2 : ℝ) : ℝ) : ℂ) * ∑ T', obsCoeff hI' T' := by
    rw [← hval]; rfl
  rw [hM]
  congr 1
  refine Finset.sum_congr rfl fun T' _ => ?_
  have := (obsCoeffParam_fibre S 1 hp Ev _ (XiCRaw S.G' (compWeight 3 1) ν (k + 1) 1 T.t) _ _ _ D
    (θ := ((⟨rawOf D, rawOf_mem_rawSub _⟩ : rawSub 2 S.G'), g)) rfl ⟨D, hDx', rfl⟩ T').trans
    (hI T').symm
  exact this.symm


open Classical in
/-- **The observable coefficient family with its four properties for one choice of witnesses.**
In the order of `obsCoeffFamily_fromTower` (labels, `ε_H` and the activity before the site, then the
amplitude and `Ev`): for every finite set `T'` of cubes the family `obsCoeffParam … θ T'` is analytic
on `physVq S S.a₁ S.ν T.t q`, bounded there by `(B₁ + B₂) e^{-λ dExt T'}` and vanishes unless `T'`
contains the root cube of the observable site and its sites form a polymer domain; and for the same
family, at every chart datum of the fibre and every source `g` with `‖g‖₁ < q`, the value
`M0C … g y i` equals `√β_U ∑_{T'} obsCoeffParam … (rawOf D, g) T'`. -/
theorem obsFamily_joint_fromTower {κmin : ℝ} (T : StepTower κmin) {A₁ : ℝ} (hA : 0 < A₁) (p : ℕ)
    {CR s : ℝ} (hCR : 0 < CR) (hs0 : 0 < s) (hs : s < 1 / 2) :
    ∃ (β₀ CE CF : ℝ), 3 ≤ β₀ ∧ 0 < CE ∧ 0 < CF ∧
      ∀ (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁] (h3N : 3 ∣ N₁), 5 < N₁ →
      ∀ ν : ℝ, 0 < ν → ν * 3 ^ (2 * (k + 1)) ≤ 1 → ∀ β : ℝ, β₀ ≤ β →
      ∀ p₁ : ℝ, 0 < p₁ → p₁ ≤ pLog A₁ p (β * 3 ^ k) → ∀ q : ℝ, 0 < q → q ≤ 1 →
      ∀ (Dsc : StepScaleData T k hk N₁ ν β p₁)
        (S : StepSetting 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)),
        S = T.step k hk N₁ ν β p₁ → ∀ hp : 0 < S.p₁,
      ∃ (Lb : Type) (_ : Fintype Lb)
        (Lab : CubeLabels (d := 3) (L := 3) (N₁ := N₁) (m₁ := T.m₁) (K := k + 1) 1 (k + 1)
          Set.univ Lb) (εH : ℝ) (hεH : 0 < εH)
        (A : physParam 2 S → ℂ → LabelAct Lab (S.blockSplit 1 hp).Ωb εH (2 * T.κdec - 1) T.κ0
          (K0 3 3 T.κ0 + 1)),
        2 * εH ≤ CE * (Real.log (β * 3 ^ k)) ^ (3 * p) / Real.sqrt (β * 3 ^ k) +
          q * CF * (Real.log (β * 3 ^ k)) ^ p / Real.sqrt (β * 3 ^ k) ∧
        ∀ (y : CTorus 3 3 N₁ T.m₁ (k + 1)) (i : Fin 2)
          (hdj : ∀ Y ∈ obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y),
            IsDj 1 (k + 1) Y),
        ∃ hR : 0 ≤ obsRg CR s (p : ℝ) (β * 3 ^ k),
          1 < obsRg CR s (p : ℝ) (β * 3 ^ k) ∧
          obsRg CR s (p : ℝ) (β * 3 ^ k) * max (εH + εH) εH ≤
            stepTheta 3 3 ((K0 3 3 T.κ0 + 1) + (K0 3 3 T.κ0 + 1) + K0 3 3 T.κ0 + K0 3 3 T.κ0)
              (2 * T.κdec - 1) T.κ0 T.κ' ∧
          ∃ Ev : Set (CTorus 3 3 N₁ T.m₁ (k + 1)) →
        RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2 × (unitPts S.G' × Fin 2 → ℂ) → ℂ,
      (∀ Y, AnalyticOnNhd ℂ (Ev Y) (XiCRaw S.G' (compWeight 3 1) ν (k + 1) 1 T.t ×ˢ
          {ψh : unitPts S.G' × Fin 2 → ℂ | ∀ p, ‖ψh p‖ ≤ lvCpsi T.κ T.t (β * 3 ^ k)})) ∧
      (∀ Y, ∀ u ∈ XiCRaw S.G' (compWeight 3 1) ν (k + 1) 1 T.t ×ˢ
          {ψh : unitPts S.G' × Fin 2 → ℂ | ∀ p, ‖ψh p‖ ≤ lvCpsi T.κ T.t (β * 3 ^ k)},
        ∀ u' ∈ XiCRaw S.G' (compWeight 3 1) ν (k + 1) 1 T.t ×ˢ
          {ψh : unitPts S.G' × Fin 2 → ℂ | ∀ p, ‖ψh p‖ ≤ lvCpsi T.κ T.t (β * 3 ^ k)},
        AgHatDir S.hG' Y u u' → Ev Y u = Ev Y u') ∧
      (∀ Y, ∀ u ∈ XiCRaw S.G' (compWeight 3 1) ν (k + 1) 1 T.t ×ˢ
          {ψh : unitPts S.G' × Fin 2 → ℂ | ∀ p, ‖ψh p‖ ≤ lvCpsi T.κ T.t (β * 3 ^ k)},
        ‖Ev Y u‖ ≤ (cK2' 3 3 2 (famConst 3 3 T.BG₂ T.κ) * T.t) *
          Real.exp (-(2 * T.κdec) * treeLenCovOne 1 (k + 1) Y)) ∧
      (∀ T' : Finset (CubeB (d := 3) (L := 3) (N₁ := N₁) (m₁ := T.m₁) (K := k + 1) 1 (k + 1)
        Set.univ),
    AnalyticOnNhd ℂ (fun θ => obsCoeffParam (S.blockSplit 1 hp).μ (fun θ t σ => tiltActObs A (show 3 ^ 1 ∣ N₁ by simpa using h3N) T.κ0_ent hεH.le hdj (le_refl _)
        (obsRg CR s (p : ℝ) (β * 3 ^ k)) hR (ball (0 : ℂ) (3 / 2)) θ t σ)
      (fun m => obsY1 1 S (Lb ⊕ Lb) (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y)) m) (fun m => blockMarkC S 1 hp m.1 m.2)
      (fun θ m T'' => obsHker (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y)) (fun Y => hatCoeff (Ev Y)
        (θ.1 : RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2) (obsUnitVec S m)) 1 T'')
      (obsRemLab (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y)) (fun Y => Sum.inl (Sum.inr Y))
        (obsY0 1 (Lb ⊕ Lb) (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y)) (rootCube (m₀ := 1) (blockIndex y))))
      (fun θ => obsGrFam S 1 hp Ev (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y)) (XiCRaw S.G' (compWeight 3 1) ν (k + 1) 1 T.t) θ) θ T')
      (physVq S S.a₁ S.ν T.t q) ∧
      (∀ θ ∈ (physVq S S.a₁ S.ν T.t q),
        ‖obsCoeffParam (S.blockSplit 1 hp).μ
      (fun θ t σ => tiltActObs A (show 3 ^ 1 ∣ N₁ by simpa using h3N) T.κ0_ent hεH.le hdj (le_refl _)
        (obsRg CR s (p : ℝ) (β * 3 ^ k)) hR (ball (0 : ℂ) (3 / 2)) θ t σ)
      (fun m => obsY1 1 S (Lb ⊕ Lb) (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y)) m) (fun m => blockMarkC S 1 hp m.1 m.2)
      (fun θ m T'' => obsHker (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y))
        (fun Y => hatCoeff (Ev Y) (θ.1 : RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2)
          (obsUnitVec S m)) 1 T'')
      (obsRemLab (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y))
        (fun Y => Sum.inl (Sum.inr Y))
        (obsY0 1 (Lb ⊕ Lb) (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y))
          (rootCube (m₀ := 1) (blockIndex y))))
      (fun θ => obsGrFam S 1 hp Ev (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y)) (XiCRaw S.G' (compWeight 3 1) ν (k + 1) 1 T.t) θ) θ T'‖ ≤
      ((cK2' 3 3 2 (famConst 3 3 T.BG₂ T.κ) * T.t / lvCpsi T.κ T.t (β * 3 ^ k)) *
          (CPE 3 3 ((K0 3 3 T.κ0 + 1) + (K0 3 3 T.κ0 + 1) + K0 3 3 T.κ0 + K0 3 3 T.κ0)
            (2 * T.κdec - 1) T.κ0 T.κ' * S.p₁ / (obsRg CR s (p : ℝ) (β * 3 ^ k))) *
          (((2 * 3 ^ (3 * (1 + T.m₁ + 1)) : ℕ) : ℝ) * c1 3 3) *
          ((K0 3 3 T.κ0 + 1) + (K0 3 3 T.κ0 + 1) + K0 3 3 T.κ0 + K0 3 3 T.κ0) ^ 2 *
          Real.exp ((min (2 * T.κdec) T.κ' - T.κ0) * cG 3 3) +
        CPE 3 3 ((K0 3 3 T.κ0 + 1) + (K0 3 3 T.κ0 + 1) + K0 3 3 T.κ0 + K0 3 3 T.κ0)
            (2 * T.κdec - 1) T.κ0 T.κ' *
          (∑ r, 8 * (cK2' 3 3 2 (famConst 3 3 T.BG₂ T.κ) * T.t) *
            (S.p₁ / lvCpsi T.κ T.t (β * 3 ^ k)) ^ 2 * Real.exp (-T.κ0 *
            (obsLab (Lab.sum Lab) hdj).dl (obsRemLab (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y)) (fun Y => Sum.inl (Sum.inr Y))
              (obsY0 1 (Lb ⊕ Lb) (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y)) (rootCube (m₀ := 1) (blockIndex y))) r)))) *
        Real.exp (-(min (min (2 * T.κdec) T.κ' - T.κ0 - 1) T.κ') * dExt T')) ∧
      (∀ θ ∈ (physVq S S.a₁ S.ν T.t q),
        obsCoeffParam (S.blockSplit 1 hp).μ
      (fun θ t σ => tiltActObs A (show 3 ^ 1 ∣ N₁ by simpa using h3N) T.κ0_ent hεH.le hdj (le_refl _)
        (obsRg CR s (p : ℝ) (β * 3 ^ k)) hR (ball (0 : ℂ) (3 / 2)) θ t σ)
      (fun m => obsY1 1 S (Lb ⊕ Lb) (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y)) m) (fun m => blockMarkC S 1 hp m.1 m.2)
      (fun θ m T'' => obsHker (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y))
        (fun Y => hatCoeff (Ev Y) (θ.1 : RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2)
          (obsUnitVec S m)) 1 T'')
      (obsRemLab (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y))
        (fun Y => Sum.inl (Sum.inr Y))
        (obsY0 1 (Lb ⊕ Lb) (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y))
          (rootCube (m₀ := 1) (blockIndex y))))
      (fun θ => obsGrFam S 1 hp Ev (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y)) (XiCRaw S.G' (compWeight 3 1) ν (k + 1) 1 T.t) θ) θ T' ≠ 0 →
        rootCube (m₀ := 1) (blockIndex y) ∈ T' ∧ IsPolyDom 1 (k + 1) (sitesOf T'))) ∧
      ∀ (D : BgData S.G' 2) (hDh : ∀ y i, D.h y i = (S.h₀ i : ℂ)),
        XiCData S.G' S.a S.ν (k + 1) 1 T.t D →
        ∀ g : Fld 3 3 N₁ T.m₁ (k + 1) 2, ∑ x', ∑ i', ‖g x' i'‖ < q →
          (S.withDatum D hDh).M0C (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) g y i =
            ((S.betaU ^ (1 / 2 : ℝ) : ℝ) : ℂ) * ∑ T', obsCoeffParam (S.blockSplit 1 hp).μ
      (fun θ t σ => tiltActObs A (show 3 ^ 1 ∣ N₁ by simpa using h3N) T.κ0_ent hεH.le hdj (le_refl _)
        (obsRg CR s (p : ℝ) (β * 3 ^ k)) hR (ball (0 : ℂ) (3 / 2)) θ t σ)
      (fun m => obsY1 1 S (Lb ⊕ Lb) (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y)) m) (fun m => blockMarkC S 1 hp m.1 m.2)
      (fun θ m T'' => obsHker (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y))
        (fun Y => hatCoeff (Ev Y) (θ.1 : RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2)
          (obsUnitVec S m)) 1 T'')
      (obsRemLab (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y))
        (fun Y => Sum.inl (Sum.inr Y))
        (obsY0 1 (Lb ⊕ Lb) (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y))
          (rootCube (m₀ := 1) (blockIndex y))))
      (fun θ => obsGrFam S 1 hp Ev (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y)) (XiCRaw S.G' (compWeight 3 1) ν (k + 1) 1 T.t) θ)
      ((⟨rawOf D, rawOf_mem_rawSub _⟩ : rawSub 2 S.G'), g) T'
    := by
  classical
  obtain ⟨β₀, CE, CF, h3, hCE, hCF, hmain⟩ := obsFamily_full_fromTower T hA p hCR hs0 hs
  refine ⟨β₀, CE, CF, h3, hCE, hCF, fun k hk N₁ _ h3N hN ν hνpos hν β hβ p₁ hp0 hp₁ q hq0 hq1
    Dsc S hS hp => ?_⟩
  obtain ⟨Lb, instLb, Lab, εH, hεH, A, hεb, hrest⟩ := hmain k hk N₁ h3N hN ν hνpos hν β hβ p₁
    hp0 hp₁ q hq0 hq1 Dsc S hS hp
  refine ⟨Lb, instLb, Lab, εH, hεH, A, hεb, fun y i hdj => ?_⟩
  obtain ⟨hR, h1, hεΘ, Ev, ha, hd, hb, -, -, hT', hv⟩ := hrest y i hdj
  refine ⟨hR, h1, hεΘ, Ev, ha, hd, hb, ⟨fun T' => ⟨(hT' T').2.2.2.1, (hT' T').2.2.2.2.1,
    (hT' T').2.2.2.2.2.1⟩, hv⟩⟩

/-- The rate of the bound of `obsCoeffParam` is `(3/2) κ_dec` at the tower:
`min (min (2 κ_dec, κ') - κ₀ - 1) κ' = (3/2) κ_dec`, from `κ' = (3/2) κ_dec + κ₀ + 1` and
`κ_dec ≥ 3 κ₀ + 3`. -/
theorem obsFamilyRate_eq_tower {κmin : ℝ} (T : StepTower κmin) :
    min (min (2 * T.κdec) T.κ' - T.κ0 - 1) T.κ' = 3 / 2 * T.κdec := T.toG.obsFamilyRate_eq

open Classical in
/-- **The observable coefficient family at the base datum.**  The conclusions (i)-(iii) of
`obsFamily_joint_fromTower` for the family `obsCoeffParam`, and for the same family the value at the
base datum `S.D'` of the step: for every source `g` with `‖g‖₁ < q`,
`S.M0C … g y i = √β_U ∑_{T'} obsCoeffParam … (rawOf S.D', g) T'`.  The rate of the bound is
`λ = min (min (2 κ_dec, κ') - κ₀ - 1) κ'`, which equals `(3/2) κ_dec` (`obsFamilyRate_eq_tower`). -/
theorem obsFamily_atBaseDatum_fromTower {κmin : ℝ} (T : StepTower κmin) {A₁ : ℝ} (hA : 0 < A₁) (p : ℕ)
    {CR s : ℝ} (hCR : 0 < CR) (hs0 : 0 < s) (hs : s < 1 / 2) :
    ∃ (β₀ CE CF : ℝ), 3 ≤ β₀ ∧ 0 < CE ∧ 0 < CF ∧
      ∀ (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁] (h3N : 3 ∣ N₁), 5 < N₁ →
      ∀ ν : ℝ, 0 < ν → ν * 3 ^ (2 * (k + 1)) ≤ 1 → ∀ β : ℝ, β₀ ≤ β →
      ∀ p₁ : ℝ, 0 < p₁ → p₁ ≤ pLog A₁ p (β * 3 ^ k) → ∀ q : ℝ, 0 < q → q ≤ 1 →
      ∀ (Dsc : StepScaleData T k hk N₁ ν β p₁)
        (S : StepSetting 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)),
        S = T.step k hk N₁ ν β p₁ → ∀ hp : 0 < S.p₁,
      ∃ (Lb : Type) (_ : Fintype Lb)
        (Lab : CubeLabels (d := 3) (L := 3) (N₁ := N₁) (m₁ := T.m₁) (K := k + 1) 1 (k + 1)
          Set.univ Lb) (εH : ℝ) (hεH : 0 < εH)
        (A : physParam 2 S → ℂ → LabelAct Lab (S.blockSplit 1 hp).Ωb εH (2 * T.κdec - 1) T.κ0
          (K0 3 3 T.κ0 + 1)),
        2 * εH ≤ CE * (Real.log (β * 3 ^ k)) ^ (3 * p) / Real.sqrt (β * 3 ^ k) +
          q * CF * (Real.log (β * 3 ^ k)) ^ p / Real.sqrt (β * 3 ^ k) ∧
        ∀ (y : CTorus 3 3 N₁ T.m₁ (k + 1)) (i : Fin 2)
          (hdj : ∀ Y ∈ obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y),
            IsDj 1 (k + 1) Y),
        ∃ hR : 0 ≤ obsRg CR s (p : ℝ) (β * 3 ^ k),
          1 < obsRg CR s (p : ℝ) (β * 3 ^ k) ∧
          obsRg CR s (p : ℝ) (β * 3 ^ k) * max (εH + εH) εH ≤
            stepTheta 3 3 ((K0 3 3 T.κ0 + 1) + (K0 3 3 T.κ0 + 1) + K0 3 3 T.κ0 + K0 3 3 T.κ0)
              (2 * T.κdec - 1) T.κ0 T.κ' ∧
          ∃ Ev : Set (CTorus 3 3 N₁ T.m₁ (k + 1)) →
        RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2 × (unitPts S.G' × Fin 2 → ℂ) → ℂ,
      (∀ Y, AnalyticOnNhd ℂ (Ev Y) (XiCRaw S.G' (compWeight 3 1) ν (k + 1) 1 T.t ×ˢ
          {ψh : unitPts S.G' × Fin 2 → ℂ | ∀ p, ‖ψh p‖ ≤ lvCpsi T.κ T.t (β * 3 ^ k)})) ∧
      (∀ Y, ∀ u ∈ XiCRaw S.G' (compWeight 3 1) ν (k + 1) 1 T.t ×ˢ
          {ψh : unitPts S.G' × Fin 2 → ℂ | ∀ p, ‖ψh p‖ ≤ lvCpsi T.κ T.t (β * 3 ^ k)},
        ∀ u' ∈ XiCRaw S.G' (compWeight 3 1) ν (k + 1) 1 T.t ×ˢ
          {ψh : unitPts S.G' × Fin 2 → ℂ | ∀ p, ‖ψh p‖ ≤ lvCpsi T.κ T.t (β * 3 ^ k)},
        AgHatDir S.hG' Y u u' → Ev Y u = Ev Y u') ∧
      (∀ Y, ∀ u ∈ XiCRaw S.G' (compWeight 3 1) ν (k + 1) 1 T.t ×ˢ
          {ψh : unitPts S.G' × Fin 2 → ℂ | ∀ p, ‖ψh p‖ ≤ lvCpsi T.κ T.t (β * 3 ^ k)},
        ‖Ev Y u‖ ≤ (cK2' 3 3 2 (famConst 3 3 T.BG₂ T.κ) * T.t) *
          Real.exp (-(2 * T.κdec) * treeLenCovOne 1 (k + 1) Y)) ∧
      (∀ T' : Finset (CubeB (d := 3) (L := 3) (N₁ := N₁) (m₁ := T.m₁) (K := k + 1) 1 (k + 1)
        Set.univ),
    AnalyticOnNhd ℂ (fun θ => obsCoeffParam (S.blockSplit 1 hp).μ (fun θ t σ => tiltActObs A (show 3 ^ 1 ∣ N₁ by simpa using h3N) T.κ0_ent hεH.le hdj (le_refl _)
        (obsRg CR s (p : ℝ) (β * 3 ^ k)) hR (ball (0 : ℂ) (3 / 2)) θ t σ)
      (fun m => obsY1 1 S (Lb ⊕ Lb) (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y)) m) (fun m => blockMarkC S 1 hp m.1 m.2)
      (fun θ m T'' => obsHker (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y)) (fun Y => hatCoeff (Ev Y)
        (θ.1 : RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2) (obsUnitVec S m)) 1 T'')
      (obsRemLab (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y)) (fun Y => Sum.inl (Sum.inr Y))
        (obsY0 1 (Lb ⊕ Lb) (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y)) (rootCube (m₀ := 1) (blockIndex y))))
      (fun θ => obsGrFam S 1 hp Ev (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y)) (XiCRaw S.G' (compWeight 3 1) ν (k + 1) 1 T.t) θ) θ T')
      (physVq S S.a₁ S.ν T.t q) ∧
      (∀ θ ∈ (physVq S S.a₁ S.ν T.t q),
        ‖obsCoeffParam (S.blockSplit 1 hp).μ
      (fun θ t σ => tiltActObs A (show 3 ^ 1 ∣ N₁ by simpa using h3N) T.κ0_ent hεH.le hdj (le_refl _)
        (obsRg CR s (p : ℝ) (β * 3 ^ k)) hR (ball (0 : ℂ) (3 / 2)) θ t σ)
      (fun m => obsY1 1 S (Lb ⊕ Lb) (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y)) m) (fun m => blockMarkC S 1 hp m.1 m.2)
      (fun θ m T'' => obsHker (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y))
        (fun Y => hatCoeff (Ev Y) (θ.1 : RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2)
          (obsUnitVec S m)) 1 T'')
      (obsRemLab (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y))
        (fun Y => Sum.inl (Sum.inr Y))
        (obsY0 1 (Lb ⊕ Lb) (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y))
          (rootCube (m₀ := 1) (blockIndex y))))
      (fun θ => obsGrFam S 1 hp Ev (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y)) (XiCRaw S.G' (compWeight 3 1) ν (k + 1) 1 T.t) θ) θ T'‖ ≤
      ((cK2' 3 3 2 (famConst 3 3 T.BG₂ T.κ) * T.t / lvCpsi T.κ T.t (β * 3 ^ k)) *
          (CPE 3 3 ((K0 3 3 T.κ0 + 1) + (K0 3 3 T.κ0 + 1) + K0 3 3 T.κ0 + K0 3 3 T.κ0)
            (2 * T.κdec - 1) T.κ0 T.κ' * S.p₁ / (obsRg CR s (p : ℝ) (β * 3 ^ k))) *
          (((2 * 3 ^ (3 * (1 + T.m₁ + 1)) : ℕ) : ℝ) * c1 3 3) *
          ((K0 3 3 T.κ0 + 1) + (K0 3 3 T.κ0 + 1) + K0 3 3 T.κ0 + K0 3 3 T.κ0) ^ 2 *
          Real.exp ((min (2 * T.κdec) T.κ' - T.κ0) * cG 3 3) +
        CPE 3 3 ((K0 3 3 T.κ0 + 1) + (K0 3 3 T.κ0 + 1) + K0 3 3 T.κ0 + K0 3 3 T.κ0)
            (2 * T.κdec - 1) T.κ0 T.κ' *
          (∑ r, 8 * (cK2' 3 3 2 (famConst 3 3 T.BG₂ T.κ) * T.t) *
            (S.p₁ / lvCpsi T.κ T.t (β * 3 ^ k)) ^ 2 * Real.exp (-T.κ0 *
            (obsLab (Lab.sum Lab) hdj).dl (obsRemLab (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y)) (fun Y => Sum.inl (Sum.inr Y))
              (obsY0 1 (Lb ⊕ Lb) (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y)) (rootCube (m₀ := 1) (blockIndex y))) r)))) *
        Real.exp (-(min (min (2 * T.κdec) T.κ' - T.κ0 - 1) T.κ') * dExt T')) ∧
      (∀ θ ∈ (physVq S S.a₁ S.ν T.t q),
        obsCoeffParam (S.blockSplit 1 hp).μ
      (fun θ t σ => tiltActObs A (show 3 ^ 1 ∣ N₁ by simpa using h3N) T.κ0_ent hεH.le hdj (le_refl _)
        (obsRg CR s (p : ℝ) (β * 3 ^ k)) hR (ball (0 : ℂ) (3 / 2)) θ t σ)
      (fun m => obsY1 1 S (Lb ⊕ Lb) (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y)) m) (fun m => blockMarkC S 1 hp m.1 m.2)
      (fun θ m T'' => obsHker (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y))
        (fun Y => hatCoeff (Ev Y) (θ.1 : RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2)
          (obsUnitVec S m)) 1 T'')
      (obsRemLab (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y))
        (fun Y => Sum.inl (Sum.inr Y))
        (obsY0 1 (Lb ⊕ Lb) (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y))
          (rootCube (m₀ := 1) (blockIndex y))))
      (fun θ => obsGrFam S 1 hp Ev (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y)) (XiCRaw S.G' (compWeight 3 1) ν (k + 1) 1 T.t) θ) θ T' ≠ 0 →
        rootCube (m₀ := 1) (blockIndex y) ∈ T' ∧ IsPolyDom 1 (k + 1) (sitesOf T'))) ∧
      ∀ g : Fld 3 3 N₁ T.m₁ (k + 1) 2, ∑ x', ∑ i', ‖g x' i'‖ < q →
          S.M0C (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) g y i =
            ((S.betaU ^ (1 / 2 : ℝ) : ℝ) : ℂ) * ∑ T', obsCoeffParam (S.blockSplit 1 hp).μ
      (fun θ t σ => tiltActObs A (show 3 ^ 1 ∣ N₁ by simpa using h3N) T.κ0_ent hεH.le hdj (le_refl _)
        (obsRg CR s (p : ℝ) (β * 3 ^ k)) hR (ball (0 : ℂ) (3 / 2)) θ t σ)
      (fun m => obsY1 1 S (Lb ⊕ Lb) (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y)) m) (fun m => blockMarkC S 1 hp m.1 m.2)
      (fun θ m T'' => obsHker (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y))
        (fun Y => hatCoeff (Ev Y) (θ.1 : RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2)
          (obsUnitVec S m)) 1 T'')
      (obsRemLab (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y))
        (fun Y => Sum.inl (Sum.inr Y))
        (obsY0 1 (Lb ⊕ Lb) (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y))
          (rootCube (m₀ := 1) (blockIndex y))))
      (fun θ => obsGrFam S 1 hp Ev (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y)) (XiCRaw S.G' (compWeight 3 1) ν (k + 1) 1 T.t) θ)
      ((⟨rawOf S.D', rawOf_mem_rawSub _⟩ : rawSub 2 S.G'), g) T'
    := by
  classical
  obtain ⟨β₀, CE, CF, h3, hCE, hCF, hmain⟩ := obsFamily_joint_fromTower T hA p hCR hs0 hs
  refine ⟨β₀, CE, CF, h3, hCE, hCF, fun k hk N₁ _ h3N hN ν hνpos hν β hβ p₁ hp0 hp₁ q hq0 hq1
    Dsc S hS hp => ?_⟩
  obtain ⟨Lb, instLb, Lab, εH, hεH, A, hεb, hrest⟩ := hmain k hk N₁ h3N hN ν hνpos hν β hβ p₁
    hp0 hp₁ q hq0 hq1 Dsc S hS hp
  refine ⟨Lb, instLb, Lab, εH, hεH, A, hεb, fun y i hdj => ?_⟩
  obtain ⟨hR, h1, hεΘ, Ev, ha, hd, hb, hT', hv⟩ := hrest y i hdj
  refine ⟨hR, h1, hεΘ, Ev, ha, hd, hb, hT', fun g hg => ?_⟩
  subst hS
  exact hv _ (T.step k hk N₁ ν β p₁).hh₀ Dsc.xi g hg

/-- **The coefficient family of the observable at the tower, with no carried hypotheses.**
Thresholds `β₀, C_E, C_F` are those of `obsTiltLabels_fromTower` for `Θ = stepTheta 3 3 K_obs (2 κ_dec - 1) κ₀ κ'`
with `K_c = K₀ + 1`, `K_obs = K_c + K_c + K₀ + K₀`; `R_g = obsRg CR s p (β 3^k)`.  The labels
`Lab`, the activity `A` and `ε_H` are those of `obsTiltLabels_fromTower` and the family `Ev`
is the sharp-hat family of `obsEv_fromTower` built on the label system `Lab.sum Lab`.  For every
finite set `T'` of cubes: the first-order terms, the kernel sum, the remainder coefficient and
`obsCoeffParam` are analytic on `physVq … q`; for `θ` there, `obsCoeffParam … θ T'` is bounded by
`(B₁ + B₂) e^{-λ dExt T'}` (`λ = min (min (2 κ_dec, κ') - κ₀ - 1) κ'`) and vanishes unless the root cube
of the observable site lies in `T'` and the sites of `T'` form a polymer domain. -/
theorem obsCoeffFamily_fromTower {κmin : ℝ} (T : StepTower κmin) {A₁ : ℝ} (hA : 0 < A₁) (p : ℕ)
    {CR s : ℝ} (hCR : 0 < CR) (hs0 : 0 < s) (hs : s < 1 / 2) :
    ∃ (β₀ CE CF : ℝ), 3 ≤ β₀ ∧ 0 < CE ∧ 0 < CF ∧
      ∀ (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁] (h3N : 3 ∣ N₁), 5 < N₁ →
      ∀ ν : ℝ, 0 < ν → ν * 3 ^ (2 * (k + 1)) ≤ 1 → ∀ β : ℝ, β₀ ≤ β →
      ∀ p₁ : ℝ, 0 < p₁ → p₁ ≤ pLog A₁ p (β * 3 ^ k) → ∀ q : ℝ, 0 < q → q ≤ 1 →
      ∀ (Dsc : StepScaleData T k hk N₁ ν β p₁)
        (S : StepSetting 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)),
        S = T.step k hk N₁ ν β p₁ → ∀ hp : 0 < S.p₁,
      ∃ (Lb : Type) (_ : Fintype Lb)
        (Lab : CubeLabels (d := 3) (L := 3) (N₁ := N₁) (m₁ := T.m₁) (K := k + 1) 1 (k + 1)
          Set.univ Lb) (εH : ℝ) (hεH : 0 < εH)
        (A : physParam 2 S → ℂ → LabelAct Lab (S.blockSplit 1 hp).Ωb εH (2 * T.κdec - 1) T.κ0
          (K0 3 3 T.κ0 + 1)),
        2 * εH ≤ CE * (Real.log (β * 3 ^ k)) ^ (3 * p) / Real.sqrt (β * 3 ^ k) +
          q * CF * (Real.log (β * 3 ^ k)) ^ p / Real.sqrt (β * 3 ^ k) ∧
        ∀ (y : CTorus 3 3 N₁ T.m₁ (k + 1)) (i : Fin 2)
          (hdj : ∀ Y ∈ obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y),
            IsDj 1 (k + 1) Y),
        ∃ hR : 0 ≤ obsRg CR s (p : ℝ) (β * 3 ^ k),
          1 < obsRg CR s (p : ℝ) (β * 3 ^ k) ∧
          obsRg CR s (p : ℝ) (β * 3 ^ k) * max (εH + εH) εH ≤
            stepTheta 3 3 ((K0 3 3 T.κ0 + 1) + (K0 3 3 T.κ0 + 1) + K0 3 3 T.κ0 + K0 3 3 T.κ0)
              (2 * T.κdec - 1) T.κ0 T.κ' ∧
          ∃ Ev : Set (CTorus 3 3 N₁ T.m₁ (k + 1)) →
        RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2 × (unitPts S.G' × Fin 2 → ℂ) → ℂ,
      (∀ Y, AnalyticOnNhd ℂ (Ev Y) (XiCRaw S.G' (compWeight 3 1) ν (k + 1) 1 T.t ×ˢ
          {ψh : unitPts S.G' × Fin 2 → ℂ | ∀ p, ‖ψh p‖ ≤ lvCpsi T.κ T.t (β * 3 ^ k)})) ∧
      (∀ Y, ∀ u ∈ XiCRaw S.G' (compWeight 3 1) ν (k + 1) 1 T.t ×ˢ
          {ψh : unitPts S.G' × Fin 2 → ℂ | ∀ p, ‖ψh p‖ ≤ lvCpsi T.κ T.t (β * 3 ^ k)},
        ∀ u' ∈ XiCRaw S.G' (compWeight 3 1) ν (k + 1) 1 T.t ×ˢ
          {ψh : unitPts S.G' × Fin 2 → ℂ | ∀ p, ‖ψh p‖ ≤ lvCpsi T.κ T.t (β * 3 ^ k)},
        AgHatDir S.hG' Y u u' → Ev Y u = Ev Y u') ∧
      (∀ Y, ∀ u ∈ XiCRaw S.G' (compWeight 3 1) ν (k + 1) 1 T.t ×ˢ
          {ψh : unitPts S.G' × Fin 2 → ℂ | ∀ p, ‖ψh p‖ ≤ lvCpsi T.κ T.t (β * 3 ^ k)},
        ‖Ev Y u‖ ≤ (cK2' 3 3 2 (famConst 3 3 T.BG₂ T.κ) * T.t) *
          Real.exp (-(2 * T.κdec) * treeLenCovOne 1 (k + 1) Y)) ∧
      (∀ D : BgData S.G' 2, XiCData S.G' (compWeight 3 1) ν (k + 1) 1 T.t D →
        ObsMarkHalf S 1 hp Ev D (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y))
          (obsLab (Lab.sum Lab) hdj) (lvCpsi T.κ T.t (β * 3 ^ k))
          (cK2' 3 3 2 (famConst 3 3 T.BG₂ T.κ) * T.t) (2 * T.κdec - 1) T.κ0
          (cK2' 3 3 2 (famConst 3 3 T.BG₂ T.κ) * T.t / (lvCpsi T.κ T.t (β * 3 ^ k)))
          (2 * T.κdec) (rootCube (m₀ := 1) (blockIndex y)) ∧
        ObsRayIdentity S 1 hp
          (fun ψh => svec (lvLow N₁ T.m₁ k (rhoSep T.m₁))
            (flFieldOne S.G' (lvLow N₁ T.m₁ k (rhoSep T.m₁)) T.BG₂ T.κ 1 ν D
              (hatLift S.G' 1 ν S.hG' ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) D ψh)) y i) Ev D
          (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y))) ∧
      ((∀ m : ObsMarkIdx S, Nonempty (ParamMarkFamily (S.blockSplit 1 hp).μ
        (obsLab (Lab.sum Lab) hdj)
        (fun θ t => tiltActObs A (show 3 ^ 1 ∣ N₁ by simpa using h3N) T.κ0_ent hεH.le hdj (le_refl _)
          (obsRg CR s (p : ℝ) (β * 3 ^ k)) hR (ball (0 : ℂ) (3 / 2)) θ t 1)
        (fun _ : Unit => obsY1 1 S (Lb ⊕ Lb) (obsDomains S (LocalCover.nbhdF 1 y) 1 k
          (LocalCover.fam 1 y)) m)
        (fun _ _ _ => blockMarkC S 1 hp m.1 m.2) (2 * T.κdec - 1)
        (fun _ => S.p₁ * Real.exp ((2 * T.κdec - 1) * (obsLab (Lab.sum Lab) hdj).dl
          (obsY1 1 S (Lb ⊕ Lb) (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y)) m)))
        (physVq S S.a₁ S.ν T.t q) (ball (0 : ℂ) (3 / 2)) (physCarrier S 1 hp))) ∧
      Nonempty (ParamMarkFamily (S.blockSplit 1 hp).μ (obsLab (Lab.sum Lab) hdj)
        (fun θ t => tiltActObs A (show 3 ^ 1 ∣ N₁ by simpa using h3N) T.κ0_ent hεH.le hdj (le_refl _)
          (obsRg CR s (p : ℝ) (β * 3 ^ k)) hR (ball (0 : ℂ) (3 / 2)) θ t 1)
        (obsRemLab (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y))
          (fun Y => Sum.inl (Sum.inr Y))
          (obsY0 1 (Lb ⊕ Lb) (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y))
            (rootCube (m₀ := 1) (blockIndex y))))
        (obsGrFam S 1 hp Ev (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y))
          (XiCRaw S.G' (compWeight 3 1) ν (k + 1) 1 T.t)) (2 * T.κdec - 1)
        (fun _ => 8 * (cK2' 3 3 2 (famConst 3 3 T.BG₂ T.κ) * T.t) *
          (S.p₁ / lvCpsi T.κ T.t (β * 3 ^ k)) ^ 2)
        (physVq S S.a₁ S.ν T.t q) (ball (0 : ℂ) (3 / 2)) (physCarrier S 1 hp))) ∧
      ∀ T' : Finset (CubeB (d := 3) (L := 3) (N₁ := N₁) (m₁ := T.m₁) (K := k + 1) 1 (k + 1)
        Set.univ),
      ((∀ (m : ObsMarkIdx S) (S' : Finset (CubeB (d := 3) (L := 3) (N₁ := N₁) (m₁ := T.m₁)
        (K := k + 1) 1 (k + 1) Set.univ)),
      AnalyticOnNhd ℂ (fun θ => markIntTerm (S.blockSplit 1 hp).μ ((fun θ t σ => tiltActObs A (show 3 ^ 1 ∣ N₁ by simpa using h3N) T.κ0_ent hεH.le hdj (le_refl _)
        (obsRg CR s (p : ℝ) (β * 3 ^ k)) hR (ball (0 : ℂ) (3 / 2)) θ t σ) θ)
        (obsY1 1 S (Lb ⊕ Lb) (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y)) m) (blockMarkC S 1 hp m.1 m.2) S')
        (physVq S S.a₁ S.ν T.t q)) ∧
    AnalyticOnNhd ℂ (fun θ => kernelMarkSum
      (fun m T'' => obsHker (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y)) (fun Y => hatCoeff (Ev Y)
        (θ.1 : RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2) (obsUnitVec S m)) 1 T'')
      (fun m S' => markIntTerm (S.blockSplit 1 hp).μ ((fun θ t σ => tiltActObs A (show 3 ^ 1 ∣ N₁ by simpa using h3N) T.κ0_ent hεH.le hdj (le_refl _)
        (obsRg CR s (p : ℝ) (β * 3 ^ k)) hR (ball (0 : ℂ) (3 / 2)) θ t σ) θ) (obsY1 1 S (Lb ⊕ Lb) (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y)) m)
        (blockMarkC S 1 hp m.1 m.2) S') T') (physVq S S.a₁ S.ν T.t q) ∧
    AnalyticOnNhd ℂ (fun θ => gsumCoeff (S.blockSplit 1 hp).μ (obsLab (Lab.sum Lab) hdj)
      (fun t => (fun θ t σ => tiltActObs A (show 3 ^ 1 ∣ N₁ by simpa using h3N) T.κ0_ent hεH.le hdj (le_refl _)
        (obsRg CR s (p : ℝ) (β * 3 ^ k)) hR (ball (0 : ℂ) (3 / 2)) θ t σ) θ t 1)
      (obsRemLab (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y)) (fun Y => Sum.inl (Sum.inr Y))
        (obsY0 1 (Lb ⊕ Lb) (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y)) (rootCube (m₀ := 1) (blockIndex y))))
      (obsGrFam S 1 hp Ev (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y)) (XiCRaw S.G' (compWeight 3 1) ν (k + 1) 1 T.t) θ) T')
      (physVq S S.a₁ S.ν T.t q) ∧
    AnalyticOnNhd ℂ (fun θ => obsCoeffParam (S.blockSplit 1 hp).μ (fun θ t σ => tiltActObs A (show 3 ^ 1 ∣ N₁ by simpa using h3N) T.κ0_ent hεH.le hdj (le_refl _)
        (obsRg CR s (p : ℝ) (β * 3 ^ k)) hR (ball (0 : ℂ) (3 / 2)) θ t σ)
      (fun m => obsY1 1 S (Lb ⊕ Lb) (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y)) m) (fun m => blockMarkC S 1 hp m.1 m.2)
      (fun θ m T'' => obsHker (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y)) (fun Y => hatCoeff (Ev Y)
        (θ.1 : RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2) (obsUnitVec S m)) 1 T'')
      (obsRemLab (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y)) (fun Y => Sum.inl (Sum.inr Y))
        (obsY0 1 (Lb ⊕ Lb) (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y)) (rootCube (m₀ := 1) (blockIndex y))))
      (fun θ => obsGrFam S 1 hp Ev (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y)) (XiCRaw S.G' (compWeight 3 1) ν (k + 1) 1 T.t) θ) θ T')
      (physVq S S.a₁ S.ν T.t q) ∧
      (∀ θ ∈ (physVq S S.a₁ S.ν T.t q),
        ‖obsCoeffParam (S.blockSplit 1 hp).μ
      (fun θ t σ => tiltActObs A (show 3 ^ 1 ∣ N₁ by simpa using h3N) T.κ0_ent hεH.le hdj (le_refl _)
        (obsRg CR s (p : ℝ) (β * 3 ^ k)) hR (ball (0 : ℂ) (3 / 2)) θ t σ)
      (fun m => obsY1 1 S (Lb ⊕ Lb) (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y)) m) (fun m => blockMarkC S 1 hp m.1 m.2)
      (fun θ m T'' => obsHker (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y))
        (fun Y => hatCoeff (Ev Y) (θ.1 : RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2)
          (obsUnitVec S m)) 1 T'')
      (obsRemLab (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y))
        (fun Y => Sum.inl (Sum.inr Y))
        (obsY0 1 (Lb ⊕ Lb) (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y))
          (rootCube (m₀ := 1) (blockIndex y))))
      (fun θ => obsGrFam S 1 hp Ev (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y)) (XiCRaw S.G' (compWeight 3 1) ν (k + 1) 1 T.t) θ) θ T'‖ ≤
      ((cK2' 3 3 2 (famConst 3 3 T.BG₂ T.κ) * T.t / lvCpsi T.κ T.t (β * 3 ^ k)) *
          (CPE 3 3 ((K0 3 3 T.κ0 + 1) + (K0 3 3 T.κ0 + 1) + K0 3 3 T.κ0 + K0 3 3 T.κ0)
            (2 * T.κdec - 1) T.κ0 T.κ' * S.p₁ / (obsRg CR s (p : ℝ) (β * 3 ^ k))) *
          (((2 * 3 ^ (3 * (1 + T.m₁ + 1)) : ℕ) : ℝ) * c1 3 3) *
          ((K0 3 3 T.κ0 + 1) + (K0 3 3 T.κ0 + 1) + K0 3 3 T.κ0 + K0 3 3 T.κ0) ^ 2 *
          Real.exp ((min (2 * T.κdec) T.κ' - T.κ0) * cG 3 3) +
        CPE 3 3 ((K0 3 3 T.κ0 + 1) + (K0 3 3 T.κ0 + 1) + K0 3 3 T.κ0 + K0 3 3 T.κ0)
            (2 * T.κdec - 1) T.κ0 T.κ' *
          (∑ r, 8 * (cK2' 3 3 2 (famConst 3 3 T.BG₂ T.κ) * T.t) *
            (S.p₁ / lvCpsi T.κ T.t (β * 3 ^ k)) ^ 2 * Real.exp (-T.κ0 *
            (obsLab (Lab.sum Lab) hdj).dl (obsRemLab (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y)) (fun Y => Sum.inl (Sum.inr Y))
              (obsY0 1 (Lb ⊕ Lb) (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y)) (rootCube (m₀ := 1) (blockIndex y))) r)))) *
        Real.exp (-(min (min (2 * T.κdec) T.κ' - T.κ0 - 1) T.κ') * dExt T')) ∧
      (∀ θ ∈ (physVq S S.a₁ S.ν T.t q),
        obsCoeffParam (S.blockSplit 1 hp).μ
      (fun θ t σ => tiltActObs A (show 3 ^ 1 ∣ N₁ by simpa using h3N) T.κ0_ent hεH.le hdj (le_refl _)
        (obsRg CR s (p : ℝ) (β * 3 ^ k)) hR (ball (0 : ℂ) (3 / 2)) θ t σ)
      (fun m => obsY1 1 S (Lb ⊕ Lb) (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y)) m) (fun m => blockMarkC S 1 hp m.1 m.2)
      (fun θ m T'' => obsHker (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y))
        (fun Y => hatCoeff (Ev Y) (θ.1 : RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2)
          (obsUnitVec S m)) 1 T'')
      (obsRemLab (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y))
        (fun Y => Sum.inl (Sum.inr Y))
        (obsY0 1 (Lb ⊕ Lb) (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y))
          (rootCube (m₀ := 1) (blockIndex y))))
      (fun θ => obsGrFam S 1 hp Ev (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y)) (XiCRaw S.G' (compWeight 3 1) ν (k + 1) 1 T.t) θ) θ T' ≠ 0 →
        rootCube (m₀ := 1) (blockIndex y) ∈ T' ∧ IsPolyDom 1 (k + 1) (sitesOf T')))
    := by
  obtain ⟨β₀, CE, CF, h3, hCE, hCF, hmain⟩ := obsFamily_full_fromTower T hA p hCR hs0 hs
  refine ⟨β₀, CE, CF, h3, hCE, hCF, fun k hk N₁ _ h3N hN ν hνpos hν β hβ p₁ hp0 hp₁ q hq0 hq1
    Dsc S hS hp => ?_⟩
  obtain ⟨Lb, instLb, Lab, εH, hεH, A, hεb, hrest⟩ := hmain k hk N₁ h3N hN ν hνpos hν β hβ p₁
    hp0 hp₁ q hq0 hq1 Dsc S hS hp
  refine ⟨Lb, instLb, Lab, εH, hεH, A, hεb, fun y i hdj => ?_⟩
  obtain ⟨hR, h1, hεΘ, Ev, ha, hd, hb, hD, fam, hT', -⟩ := hrest y i hdj
  exact ⟨hR, h1, hεΘ, Ev, ha, hd, hb, hD, fam, fun T' => by
    obtain ⟨a1, a2, a3, a4, a5, a6, -⟩ := hT' T'
    exact ⟨a1, a2, a3, a4, a5, a6⟩⟩

open Classical in
/-- **The value of the observable coefficient at every chart datum and source, from one `Ev` and
one activity.**

At a scale of the tower, for the site `(y, i)`: the activity `A` (of `obsTiltLabels_fromTower`),
the amplitude `Rg = obsRg …` and the family `Ev` (of `obsEv_fromTower`, on the labels
`Lab.sum Lab`) are chosen once.  Then

* `obsCoeffParam` built from `tiltActObs A … Rg …`, `blockMarkC`, the kernel
  `obsHker 𝒴 (hatCoeff (Ev ·) θ.1 (obsUnitVec S ·)) 1` and `obsGrFam` is analytic in `θ` on
  `physVq S S.a₁ S.ν T.t q` for every finite set of cubes `T'` (`obsCoeffParam_analytic_of_Ev`);
* for every chart datum `D` of the fibre `h = h₀`, every source `g` with `‖g‖₁ < q`, the value
  `(S.withDatum D hDh).M0C … g y i` equals `√β_U · ∑_{T'} obsCoeffParam … θ T'` at
  `θ = (rawOf D, g)`.

The proof builds the record `ObsMarks` of `obsMarks_of_tilt` for the same `Ev` and the activity at
`θ` (`obsRecord_of_halves`), applies `thm31b_coeff` to its consumer form (`ObsMarks.toConsumer`),
and identifies `obsCoeff` of the record with `obsCoeffParam` termwise (`obsCoeffParam_fibre`). -/
theorem obsCoeff_fibreValue_fromTower {κmin : ℝ} (T : StepTower κmin) {A₁ : ℝ}
    (hA : 0 < A₁) (p : ℕ) {CR s : ℝ} (hCR : 0 < CR) (hs0 : 0 < s) (hs : s < 1 / 2) :
    ∃ β₀ : ℝ, 3 ≤ β₀ ∧
      ∀ (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁] (h3N : 3 ∣ N₁), 5 < N₁ →
      ∀ ν : ℝ, 0 < ν → ν * 3 ^ (2 * (k + 1)) ≤ 1 → ∀ β : ℝ, β₀ ≤ β →
      ∀ p₁ : ℝ, 0 < p₁ → p₁ ≤ pLog A₁ p (β * 3 ^ k) → ∀ q : ℝ, 0 < q → q ≤ 1 →
      ∀ (Dsc : StepScaleData T k hk N₁ ν β p₁),
      let S := T.step k hk N₁ ν β p₁;
      ∀ hp : 0 < S.p₁, ∀ (y : CTorus 3 3 N₁ T.m₁ (k + 1)) (i : Fin 2),
      ∃ (Lb : Type) (_ : Fintype Lb)
        (Lab : CubeLabels (d := 3) (L := 3) (N₁ := N₁) (m₁ := T.m₁) (K := k + 1) 1 (k + 1)
          Set.univ Lb) (εH : ℝ) (hεH : 0 < εH)
        (A : physParam 2 S → ℂ → LabelAct Lab (S.blockSplit 1 hp).Ωb εH (2 * T.κdec - 1) T.κ0
          (K0 3 3 T.κ0 + 1))
        (hR : 0 ≤ obsRg CR s (p : ℝ) (β * 3 ^ k)),
        1 < obsRg CR s (p : ℝ) (β * 3 ^ k) ∧
        obsRg CR s (p : ℝ) (β * 3 ^ k) * max (εH + εH) εH ≤
          stepTheta 3 3 ((K0 3 3 T.κ0 + 1) + (K0 3 3 T.κ0 + 1) + K0 3 3 T.κ0 + K0 3 3 T.κ0) (2 * T.κdec - 1) T.κ0 T.κ' ∧
        ∃ Ev : Set (CTorus 3 3 N₁ T.m₁ (k + 1)) →
            RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2 × (unitPts S.G' × Fin 2 → ℂ) → ℂ,
          (∀ Y, AnalyticOnNhd ℂ (Ev Y) (XiCRaw S.G' (compWeight 3 1) ν (k + 1) 1 T.t ×ˢ {ψh : unitPts S.G' × Fin 2 → ℂ | ∀ p, ‖ψh p‖ ≤ lvCpsi T.κ T.t (β * 3 ^ k)})) ∧
          (∀ Y, ∀ u ∈ XiCRaw S.G' (compWeight 3 1) ν (k + 1) 1 T.t ×ˢ {ψh : unitPts S.G' × Fin 2 → ℂ | ∀ p, ‖ψh p‖ ≤ lvCpsi T.κ T.t (β * 3 ^ k)}, ∀ u' ∈ XiCRaw S.G' (compWeight 3 1) ν (k + 1) 1 T.t ×ˢ {ψh : unitPts S.G' × Fin 2 → ℂ | ∀ p, ‖ψh p‖ ≤ lvCpsi T.κ T.t (β * 3 ^ k)},
            AgHatDir S.hG' Y u u' → Ev Y u = Ev Y u') ∧
          (∀ Y, ∀ u ∈ XiCRaw S.G' (compWeight 3 1) ν (k + 1) 1 T.t ×ˢ {ψh : unitPts S.G' × Fin 2 → ℂ | ∀ p, ‖ψh p‖ ≤ lvCpsi T.κ T.t (β * 3 ^ k)},
            ‖Ev Y u‖ ≤ (cK2' 3 3 2 (famConst 3 3 T.BG₂ T.κ) * T.t) *
              Real.exp (-(2 * T.κdec) * treeLenCovOne 1 (k + 1) Y)) ∧
          (∀ T' : Finset (CubeB (d := 3) (L := 3) (N₁ := N₁) (m₁ := T.m₁) (K := k + 1) 1 (k + 1) Set.univ),
            AnalyticOnNhd ℂ (fun θ : physParam 2 S => obsCoeffParam (S.blockSplit 1 hp).μ
              (fun (θ : physParam 2 S) (t σ : ℂ) => tiltActObs A (show 3 ^ 1 ∣ N₁ by simpa using h3N) T.κ0_ent hεH.le (obsDomains_isDj (X₁f := LocalCover.nbhdF 1 y) S le_rfl (Dsc.covers.2 (y, i)).1 (Dsc.covers.2 (y, i)).2.2.1) (Kobs := (K0 3 3 T.κ0 + 1) + (K0 3 3 T.κ0 + 1) + K0 3 3 T.κ0 + K0 3 3 T.κ0) le_rfl (obsRg CR s (p : ℝ) (β * 3 ^ k)) hR (ball (0 : ℂ) (3 / 2)) θ t σ)
              (fun m => obsY1 1 S (Lb ⊕ Lb) (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y)) m)
              (fun m => blockMarkC S 1 hp m.1 m.2)
              (fun θ m T'' => obsHker (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y)) (fun Y' => hatCoeff (Ev Y')
                (θ.1 : RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2) (obsUnitVec S m)) 1 T'')
              (obsRemLab (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y)) (fun Y' => Sum.inl (Sum.inr Y'))
                (obsY0 1 (Lb ⊕ Lb) (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y)) (rootCube (m₀ := 1) (blockIndex y))))
              (fun θ => obsGrFam S 1 hp Ev (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y)) (XiCRaw S.G' (compWeight 3 1) ν (k + 1) 1 T.t) θ) θ T')
              (physVq S S.a₁ S.ν T.t q)) ∧
          ∀ (D : BgData S.G' 2) (hDh : ∀ y i, D.h y i = (S.h₀ i : ℂ)),
            XiCData S.G' S.a S.ν (k + 1) 1 T.t D →
            ∀ g : Fld 3 3 N₁ T.m₁ (k + 1) 2, ∑ x', ∑ i', ‖g x' i'‖ < q →
              (S.withDatum D hDh).M0C (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) g y i =
                ((S.betaU ^ (1 / 2 : ℝ) : ℝ) : ℂ) * ∑ T', obsCoeffParam (S.blockSplit 1 hp).μ
                  (fun (θ : physParam 2 S) (t σ : ℂ) => tiltActObs A (show 3 ^ 1 ∣ N₁ by simpa using h3N) T.κ0_ent hεH.le (obsDomains_isDj (X₁f := LocalCover.nbhdF 1 y) S le_rfl (Dsc.covers.2 (y, i)).1 (Dsc.covers.2 (y, i)).2.2.1) (Kobs := (K0 3 3 T.κ0 + 1) + (K0 3 3 T.κ0 + 1) + K0 3 3 T.κ0 + K0 3 3 T.κ0) le_rfl (obsRg CR s (p : ℝ) (β * 3 ^ k)) hR (ball (0 : ℂ) (3 / 2)) θ t σ)
                  (fun m => obsY1 1 S (Lb ⊕ Lb) (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y)) m)
                  (fun m => blockMarkC S 1 hp m.1 m.2)
                  (fun θ m T'' => obsHker (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y)) (fun Y' => hatCoeff (Ev Y')
                    (θ.1 : RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2) (obsUnitVec S m)) 1 T'')
                  (obsRemLab (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y)) (fun Y' => Sum.inl (Sum.inr Y'))
                    (obsY0 1 (Lb ⊕ Lb) (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y)) (rootCube (m₀ := 1) (blockIndex y))))
                  (fun θ => obsGrFam S 1 hp Ev (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y)) (XiCRaw S.G' (compWeight 3 1) ν (k + 1) 1 T.t) θ)
                  ((⟨rawOf D, rawOf_mem_rawSub _⟩ : rawSub 2 S.G'), g) T' := by
  obtain ⟨β₀, CE, CF, h3, -, -, hmain⟩ := obsFamily_full_fromTower T hA p hCR hs0 hs
  refine ⟨β₀, h3, ?_⟩
  intro k hk N₁ _ h3N hN ν hνpos hν β hβ p₁ hp0 hp₁ q hq0 hq1 Dsc S hp y i
  obtain ⟨Lb, instLb, Lab, εH, hεH, A, -, hrest⟩ := hmain k hk N₁ h3N hN ν hνpos hν β hβ p₁
    hp0 hp₁ q hq0 hq1 Dsc S rfl hp
  have hdj := obsDomains_isDj (X₁f := LocalCover.nbhdF 1 y) S le_rfl (Dsc.covers.2 (y, i)).1
    (Dsc.covers.2 (y, i)).2.2.1
  obtain ⟨hR, h1, hεΘ, Ev, ha, hd, hb, -, -, hT', hv⟩ := hrest y i hdj
  exact ⟨Lb, instLb, Lab, εH, hεH, A, hR, h1, hεΘ, Ev, ha, hd, hb,
    fun T' => (hT' T').2.2.2.1, hv⟩

end Balaban.Inhabited
