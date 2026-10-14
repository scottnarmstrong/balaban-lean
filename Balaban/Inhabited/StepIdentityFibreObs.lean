/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.ObsFamilyJoint
public import Balaban.Inhabited.ObsFamilyPrefactor
public import Balaban.Inhabited.StepIdentityFibre
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The observable half of the step identity on the fibre `h ≡ h₀`

`obsFamily_full_fromTower` gives, at a scale of the shared tower, one label system and one
activity, and for every observable site `(y, i)` one amplitude and one family `Ev`, whose
coefficients `obsCoeffParam … θ T'` are analytic, bounded, supported on rooted polymer sets and
local (equal at two parameters whose raw data agree on the thickening of `sitesOf T'` and whose
sources agree on `sitesOf T'`, and also when their physical restrictions agree on `sitesOf T'`),
and whose sum at `θ = (rawOf D, g)` is `β_U^{-1/2} ℳ₀(y; g)_i` of
the step with the datum `D`.

`obsFamily_pair_fibre_fromTower` collects the coefficients of all sites in one function
`mObs y i θ T'` (equal to `obsCoeffParam …` for the amplitude and the `Ev` of the site), chosen
before the datum and the source, and adds the pairing with the source: for every datum `D` of the
chart with constant field `h₀` and every source `g` with `∑ |g| < q`,
`β_U^{-1/2} ∑_{y,i} g(y,i) ℳ₀(y; g)_i = ∑_{y,i} g(y,i) ∑_{T'} mObs y i (rawOf D, g) T'`.
The factors `β_U^{-1/2}` and `β_U^{1/2}` cancel since `β_U = β 3^k > 0`.

The statements are first proved for a general tower (`obsFamily_pair_fibre_prefactor_fromTowerG`,
`obsFamily_pair_fibre_fromTowerG`); the fixed-tower statements are corollaries.
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation
  Balaban.Localization Balaban.Localization.LevelPair Balaban.Localization.I5Inhabited
  Balaban.Polymer Balaban.SmallField.Def6 Balaban.Inhabited.LevelStep MeasureTheory Metric

open Classical in
/-- At source radius `ρ` (`q ≤ ρ`, `max 1 ρ ≤ β`); the landed theorem is its `ρ = 1` corollary.  **The observable coefficient family of all sites on the fibre, with the prefactor bound.**
Beyond the threshold of `obsFamily_full_fromTowerG`, at every scale datum and for `0 < q ≤ 1` there
are a label system, an amplitude `ε_H`, an activity `A` and a function `mObs y i θ T'` of the
observable site `(y, i)`, the parameter `θ = (raw datum, source)` and the finite set `T'` of
level-one blocks, chosen before the datum and the source, such that:
* for every site `(y, i)` there are an amplitude `obsRg` and a family `Ev` (analytic, local,
  bounded) with `mObs y i θ T' = obsCoeffParam … θ T'` for the tilted activity of `A` and this
  `Ev`; `θ ↦ mObs y i θ T'` is analytic on `physVq … q`, bounded there by
  `(B₁ + B₂) e^{-λ dExt T'}`, `λ = min (min (2 κ_dec) κ' - κ₀ - 1) κ'`, non-zero only if `T'`
  contains the root cube of `y` and its sites form a polymer, and local:
  `mObs y i θ T' = mObs y i θ' T'` for `θ, θ'` of `physVq … q` whose raw data agree on
  `thickSet (sitesOf T')` and whose sources agree on `sitesOf T'`; equality of their
  `physRestrict (sitesOf T')` images also implies equality of the coefficients;
* for every datum `D` of the chart `Ξ^c(𝔹_{k+1}; 1, T.t)` with constant field `h₀` and every source
  `g` with `∑ |g| < q`: `ℳ₀(y; g)_i = β_U^{1/2} ∑_{T'} mObs y i (rawOf D, g) T'` for every site, and
  `β_U^{-1/2} ∑_{y,i} g(y,i) ℳ₀(y; g)_i = ∑_{y,i} g(y,i) ∑_{T'} mObs y i (rawOf D, g) T'`,
  the objects `ℳ₀` being those of the step with the datum `D` and the class with zero old terms;
* with a constant `C ≥ 0` chosen with the thresholds (before the scale): for the same `mObs`,
  `‖mObs y i θ T'‖ ≤ C · obsPrefactor p s (β 3^k) · e^{-(3/2) κ_dec dExt T'}` on `physVq … q`. -/
theorem obsFamily_pair_fibre_prefactor_fromTowerG_rho {d L N : ℕ} [NeZero L] {κmin : ℝ} (T : StepTowerG d L N κmin) {A₁ : ℝ} (hA : 0 < A₁)
    (p : ℕ) {CR s : ℝ} (hCR : 0 < CR) (hs0 : 0 < s) (hs : s < 1 / 2) (ρ : ℝ) :
    ∃ (β₀ CE CF C : ℝ), 3 ≤ β₀ ∧ 0 < CE ∧ 0 < CF ∧ 0 ≤ C ∧
      ∀ (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁] (h3N : L ^ T.m₀ ∣ N₁), 5 < N₁ →
      ∀ ν : ℝ, 0 < ν → ν * (L : ℝ) ^ (2 * (k + 1)) ≤ 1 → ∀ β : ℝ, β₀ ≤ β →
      ∀ p₁ : ℝ, 0 < p₁ → p₁ ≤ pLog A₁ p (β * (L : ℝ) ^ (k * (d - 2))) → ∀ q : ℝ, 0 < q → q ≤ ρ →
      StepScaleDataG T k hk N₁ ν β p₁ →
      ∀ (S : StepSetting d L N₁ T.m₁ k N (rhoSepG d L T.m₁)),
        S = T.step k hk N₁ ν β p₁ → ∀ hp : 0 < S.p₁,
      ∃ (Lb : Type) (_ : Fintype Lb)
        (Lab : CubeLabels (d := d) (L := L) (N₁ := N₁) (m₁ := T.m₁) (K := k + 1) T.m₀ (k + 1)
          Set.univ Lb) (εH : ℝ) (hεH : 0 < εH)
        (A : physParam N S → ℂ → LabelAct Lab (S.blockSplit T.m₀ hp).Ωb εH (2 * T.κdec - 1) T.κ0
          (K0 d L T.κ0 + 1))
        (mObs : CTorus d L N₁ T.m₁ (k + 1) → Fin N → physParam N S →
          Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := T.m₁) (K := k + 1) T.m₀ (k + 1)
            Set.univ) → ℂ),
        2 * εH ≤ CE * (Real.log (β * (L : ℝ) ^ (k * (d - 2)))) ^ (3 * p) / Real.sqrt (β * (L : ℝ) ^ (k * (d - 2))) +
          q * CF * (Real.log (β * (L : ℝ) ^ (k * (d - 2)))) ^ p / Real.sqrt (β * (L : ℝ) ^ (k * (d - 2))) ∧
        (∀ (y : CTorus d L N₁ T.m₁ (k + 1)) (i : Fin N)
          (hdj : ∀ Y ∈ obsDomains S (LocalCover.nbhdF T.m₀ y) T.m₀ k (LocalCover.fam T.m₀ y),
            IsDj T.m₀ (k + 1) Y),
          ∃ hR : 0 ≤ obsRg CR s (p : ℝ) (β * (L : ℝ) ^ (k * (d - 2))),
            1 < obsRg CR s (p : ℝ) (β * (L : ℝ) ^ (k * (d - 2))) ∧
            obsRg CR s (p : ℝ) (β * (L : ℝ) ^ (k * (d - 2))) * max (εH + εH) εH ≤
              stepTheta d L ((K0 d L T.κ0 + 1) + (K0 d L T.κ0 + 1) + K0 d L T.κ0 + K0 d L T.κ0)
                (2 * T.κdec - 1) T.κ0 T.κ' ∧
            ∃ Ev : Set (CTorus d L N₁ T.m₁ (k + 1)) →
                RawData d L (N₁ * L ^ T.m₁) (k + 1) N × (unitPts S.G' × Fin N → ℂ) → ℂ,
              (∀ Y, AnalyticOnNhd ℂ (Ev Y) (XiCRaw S.G' (compWeight L 1) ν (k + 1) 1 T.t ×ˢ
                {ψh : unitPts S.G' × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ lvCpsiG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2)))})) ∧
              (∀ Y, ∀ u ∈ XiCRaw S.G' (compWeight L 1) ν (k + 1) 1 T.t ×ˢ
                  {ψh : unitPts S.G' × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ lvCpsiG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2)))},
                ∀ u' ∈ XiCRaw S.G' (compWeight L 1) ν (k + 1) 1 T.t ×ˢ
                  {ψh : unitPts S.G' × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ lvCpsiG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2)))},
                AgHatDir S.hG' Y u u' → Ev Y u = Ev Y u') ∧
              (∀ Y, ∀ u ∈ XiCRaw S.G' (compWeight L 1) ν (k + 1) 1 T.t ×ˢ
                  {ψh : unitPts S.G' × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ lvCpsiG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2)))},
                ‖Ev Y u‖ ≤ (cK2' d L N (famConst d L T.BG₂ T.κ) * T.t) *
                  Real.exp (-(2 * T.κdec) * treeLenCovOne T.m₀ (k + 1) Y)) ∧
              (∀ θ T', mObs y i θ T' = obsCoeffParam (S.blockSplit T.m₀ hp).μ
                (fun θ t σ => tiltActObs A (show L ^ T.m₀ ∣ N₁ from h3N) T.κ0_ent hεH.le
                  hdj (le_refl _) (obsRg CR s (p : ℝ) (β * (L : ℝ) ^ (k * (d - 2)))) hR (ball (0 : ℂ) (3 / 2))
                  θ t σ)
                (fun m => obsY1 T.m₀ S (Lb ⊕ Lb)
                  (obsDomains S (LocalCover.nbhdF T.m₀ y) T.m₀ k (LocalCover.fam T.m₀ y)) m)
                (fun m => blockMarkC S T.m₀ hp m.1 m.2)
                (fun θ m T'' => obsHker
                  (obsDomains S (LocalCover.nbhdF T.m₀ y) T.m₀ k (LocalCover.fam T.m₀ y))
                  (fun Y => hatCoeff (Ev Y) (θ.1 : RawData d L (N₁ * L ^ T.m₁) (k + 1) N)
                    (obsUnitVec S m)) T.m₀ T'')
                (obsRemLab (obsDomains S (LocalCover.nbhdF T.m₀ y) T.m₀ k (LocalCover.fam T.m₀ y))
                  (fun Y => Sum.inl (Sum.inr Y))
                  (obsY0 T.m₀ (Lb ⊕ Lb)
                    (obsDomains S (LocalCover.nbhdF T.m₀ y) T.m₀ k (LocalCover.fam T.m₀ y))
                    (rootCube (m₀ := T.m₀) (blockIndex y))))
                (fun θ => obsGrFam S T.m₀ hp Ev
                  (obsDomains S (LocalCover.nbhdF T.m₀ y) T.m₀ k (LocalCover.fam T.m₀ y))
                  (XiCRaw S.G' (compWeight L 1) ν (k + 1) 1 T.t) θ) θ T') ∧
              ∀ T' : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := T.m₁) (K := k + 1) T.m₀
                  (k + 1) Set.univ),
                AnalyticOnNhd ℂ (fun θ => mObs y i θ T') (physVqRho S S.a₁ S.ν T.t ρ q) ∧
                (∀ θ ∈ physVqRho S S.a₁ S.ν T.t ρ q, ‖mObs y i θ T'‖ ≤
                  ((cK2' d L N (famConst d L T.BG₂ T.κ) * T.t / lvCpsiG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2)))) *
                      (CPE d L ((K0 d L T.κ0 + 1) + (K0 d L T.κ0 + 1) + K0 d L T.κ0 +
                          K0 d L T.κ0) (2 * T.κdec - 1) T.κ0 T.κ' * S.p₁ /
                        (obsRg CR s (p : ℝ) (β * (L : ℝ) ^ (k * (d - 2))))) *
                      (((N * L ^ (d * (T.m₀ + T.m₁ + 1)) : ℕ) : ℝ) * c1 d L) *
                      ((K0 d L T.κ0 + 1) + (K0 d L T.κ0 + 1) + K0 d L T.κ0 + K0 d L T.κ0) ^ 2 *
                      Real.exp ((min (2 * T.κdec) T.κ' - T.κ0) * cG d L) +
                    CPE d L ((K0 d L T.κ0 + 1) + (K0 d L T.κ0 + 1) + K0 d L T.κ0 + K0 d L T.κ0)
                        (2 * T.κdec - 1) T.κ0 T.κ' *
                      (∑ r, 8 * (cK2' d L N (famConst d L T.BG₂ T.κ) * T.t) *
                        (S.p₁ / lvCpsiG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2)))) ^ 2 * Real.exp (-T.κ0 *
                        (obsLab (Lab.sum Lab) hdj).dl
                          (obsRemLab
                            (obsDomains S (LocalCover.nbhdF T.m₀ y) T.m₀ k (LocalCover.fam T.m₀ y))
                            (fun Y => Sum.inl (Sum.inr Y))
                            (obsY0 T.m₀ (Lb ⊕ Lb)
                              (obsDomains S (LocalCover.nbhdF T.m₀ y) T.m₀ k (LocalCover.fam T.m₀ y))
                              (rootCube (m₀ := T.m₀) (blockIndex y))) r)))) *
                  Real.exp (-(min (min (2 * T.κdec) T.κ' - T.κ0 - 1) T.κ') * dExt T')) ∧
                (∀ θ ∈ physVqRho S S.a₁ S.ν T.t ρ q, mObs y i θ T' ≠ 0 →
                  rootCube (m₀ := T.m₀) (blockIndex y) ∈ T' ∧ IsPolyDom T.m₀ (k + 1) (sitesOf T')) ∧
                (∀ θ ∈ physVqRho S S.a₁ S.ν T.t ρ q, ∀ θ' ∈ physVqRho S S.a₁ S.ν T.t ρ q,
                  agreeOn (thickSet S.G' (sitesOf T'))
                    (θ.1 : RawData d L (N₁ * L ^ T.m₁) (k + 1) N)
                    (θ'.1 : RawData d L (N₁ * L ^ T.m₁) (k + 1) N) →
                  (∀ x ∈ sitesOf T', θ.2 x = θ'.2 x) → mObs y i θ T' = mObs y i θ' T') ∧
                (∀ θ ∈ physVqRho S S.a₁ S.ν T.t ρ q, ∀ θ' ∈ physVqRho S S.a₁ S.ν T.t ρ q,
                  physRestrict (N := N) (sitesOf T') (physIncl N S θ) =
                    physRestrict (sitesOf T') (physIncl N S θ') →
                  mObs y i θ T' = mObs y i θ' T') ∧
                (∀ θ ∈ physVqRho S S.a₁ S.ν T.t ρ q, ‖mObs y i θ T'‖ ≤
                  C * obsPrefactor p s (β * (L : ℝ) ^ (k * (d - 2))) * Real.exp (-(3 / 2 * T.κdec) * dExt T'))) ∧
        ∀ (D : BgData S.G' N) (hDh : ∀ y i, D.h y i = (S.h₀ i : ℂ)),
          XiCData S.G' S.a S.ν (k + 1) 1 T.t D →
          ∀ g : Fld d L N₁ T.m₁ (k + 1) N, ∑ x', ∑ i', ‖g x' i'‖ < q →
            (∀ (y : CTorus d L N₁ T.m₁ (k + 1)) (i : Fin N),
              (S.withDatum D hDh).M0C (zeroClass d L N₁ T.m₁ k N (rhoSepG d L T.m₁)) g y i =
                ((S.betaU ^ (1 / 2 : ℝ) : ℝ) : ℂ) *
                  ∑ T', mObs y i ((⟨rawOf D, rawOf_mem_rawSub _⟩ : rawSub N S.G'), g) T') ∧
            ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
                ∑ y : CTorus d L N₁ T.m₁ (k + 1), ∑ i : Fin N,
                  g y i * (S.withDatum D hDh).M0C (zeroClass d L N₁ T.m₁ k N (rhoSepG d L T.m₁))
                    g y i =
              ∑ y : CTorus d L N₁ T.m₁ (k + 1), ∑ i : Fin N,
                g y i * ∑ T', mObs y i ((⟨rawOf D, rawOf_mem_rawSub _⟩ : rawSub N S.G'), g) T' := by
  classical
  obtain ⟨β₀, CE, CF, h3, hCE, hCF, H⟩ := obsFamily_full_fromTowerG_rho T hA p hCR hs0 hs ρ
  obtain ⟨C, hC0, hC⟩ := obs_B1_add_B2_le_prefactorG T hA p hCR (s := s)
  refine ⟨β₀, CE, CF, C, h3, hCE, hCF, hC0, ?_⟩
  intro k hk N₁ _ h3N hN ν hνpos hν β hβ p₁ hp0 hp₁ q hq0 hq1 Dsc S hS hp
  obtain ⟨Lb, hLb, Lab, εH, hεH, A, hamp, hsite⟩ :=
    H k hk N₁ h3N hN ν hνpos hν β hβ p₁ hp0 hp₁ q hq0 hq1 Dsc S hS hp
  -- the site domains are polymer domains (from the covers of the scale datum)
  have hdj₀ : ∀ (y : CTorus d L N₁ T.m₁ (k + 1)) (_ : Fin N),
      ∀ Y ∈ obsDomains S (LocalCover.nbhdF T.m₀ y) T.m₀ k (LocalCover.fam T.m₀ y), IsDj T.m₀ (k + 1) Y := by
    subst hS
    exact fun y i => obsDomains_isDj (X₁f := LocalCover.nbhdF T.m₀ y) _ T.hd
      (Dsc.covers.2 (y, i)).1 (Dsc.covers.2 (y, i)).2.2.1
  have hbU0 : 0 < S.betaU := by
    rw [hS, show (T.step k hk N₁ ν β p₁).betaU = β * (L : ℝ) ^ (k * (d - 2)) from
      hatStepKG_betaU T.hN (by have := T.hd; omega) k T.m₁ (rhoSepG d L T.m₁) hk ν β p₁ T.δ]
    have : 0 < β := by linarith
    have hLpos : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
    positivity
  choose hR hR1 hRθ Ev ha hd hb hDD hfam hcl hval using fun y i => hsite y i (hdj₀ y i)
  refine ⟨Lb, hLb, Lab, εH, hεH, A, fun y i θ T' => obsCoeffParam (S.blockSplit T.m₀ hp).μ
    (fun θ t σ => tiltActObs A (show L ^ T.m₀ ∣ N₁ from h3N) T.κ0_ent hεH.le
      (hdj₀ y i) (le_refl _) (obsRg CR s (p : ℝ) (β * (L : ℝ) ^ (k * (d - 2)))) (hR y i) (ball (0 : ℂ) (3 / 2))
      θ t σ)
    (fun m => obsY1 T.m₀ S (Lb ⊕ Lb)
      (obsDomains S (LocalCover.nbhdF T.m₀ y) T.m₀ k (LocalCover.fam T.m₀ y)) m)
    (fun m => blockMarkC S T.m₀ hp m.1 m.2)
    (fun θ m T'' => obsHker
      (obsDomains S (LocalCover.nbhdF T.m₀ y) T.m₀ k (LocalCover.fam T.m₀ y))
      (fun Y => hatCoeff (Ev y i Y) (θ.1 : RawData d L (N₁ * L ^ T.m₁) (k + 1) N)
        (obsUnitVec S m)) T.m₀ T'')
    (obsRemLab (obsDomains S (LocalCover.nbhdF T.m₀ y) T.m₀ k (LocalCover.fam T.m₀ y))
      (fun Y => Sum.inl (Sum.inr Y))
      (obsY0 T.m₀ (Lb ⊕ Lb)
        (obsDomains S (LocalCover.nbhdF T.m₀ y) T.m₀ k (LocalCover.fam T.m₀ y))
        (rootCube (m₀ := T.m₀) (blockIndex y))))
    (fun θ => obsGrFam S T.m₀ hp (Ev y i)
      (obsDomains S (LocalCover.nbhdF T.m₀ y) T.m₀ k (LocalCover.fam T.m₀ y))
      (XiCRaw S.G' (compWeight L 1) ν (k + 1) 1 T.t) θ) θ T', hamp, ?_, ?_⟩
  · intro y i hdj
    refine ⟨hR y i, hR1 y i, hRθ y i, Ev y i, ha y i, hd y i, hb y i, fun _ _ => rfl,
      fun T' => ⟨(hcl y i T').2.2.2.1, (hcl y i T').2.2.2.2.1, (hcl y i T').2.2.2.2.2.1,
        (hcl y i T').2.2.2.2.2.2.1, (hcl y i T').2.2.2.2.2.2.2, fun θ hθ => ?_⟩⟩
    have hb0 := (hcl y i T').2.2.2.2.1 θ hθ
    have hβ3 : 3 ≤ β := le_trans h3 hβ
    have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast (by have := T.hL; omega : 1 ≤ L)
    have h3k : (1 : ℝ) ≤ (L : ℝ) ^ (k * (d - 2)) := one_le_pow₀ hL1
    have hb1 : 1 < β * (L : ℝ) ^ (k * (d - 2)) := by nlinarith
    subst hS
    obtain ⟨hhalf, -⟩ := hDD y i _ Dsc.xi
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hsum, -⟩ := hhalf
    have hB := hC (β * (L : ℝ) ^ (k * (d - 2))) hb1 _ hp0.le hp₁ _ _ hsum
    rw [T.obsFamilyRate_eq] at hb0
    exact hb0.trans (mul_le_mul_of_nonneg_right hB (Real.exp_nonneg _))
  · intro D hDh hX g hg
    have hM := fun y i => (hval y i).1 D hDh hX g hg
    exact ⟨hM, rpow_neg_half_mul_sum_pair hbU0 g _ _ hM⟩


open Classical in
/-- **The observable coefficient family of all sites on the fibre, with the prefactor bound.**
Beyond the threshold of `obsFamily_full_fromTowerG`, at every scale datum and for `0 < q ≤ 1` there
are a label system, an amplitude `ε_H`, an activity `A` and a function `mObs y i θ T'` of the
observable site `(y, i)`, the parameter `θ = (raw datum, source)` and the finite set `T'` of
level-one blocks, chosen before the datum and the source, such that:
* for every site `(y, i)` there are an amplitude `obsRg` and a family `Ev` (analytic, local,
  bounded) with `mObs y i θ T' = obsCoeffParam … θ T'` for the tilted activity of `A` and this
  `Ev`; `θ ↦ mObs y i θ T'` is analytic on `physVq … q`, bounded there by
  `(B₁ + B₂) e^{-λ dExt T'}`, `λ = min (min (2 κ_dec) κ' - κ₀ - 1) κ'`, non-zero only if `T'`
  contains the root cube of `y` and its sites form a polymer, and local:
  `mObs y i θ T' = mObs y i θ' T'` for `θ, θ'` of `physVq … q` whose raw data agree on
  `thickSet (sitesOf T')` and whose sources agree on `sitesOf T'`; equality of their
  `physRestrict (sitesOf T')` images also implies equality of the coefficients;
* for every datum `D` of the chart `Ξ^c(𝔹_{k+1}; 1, T.t)` with constant field `h₀` and every source
  `g` with `∑ |g| < q`: `ℳ₀(y; g)_i = β_U^{1/2} ∑_{T'} mObs y i (rawOf D, g) T'` for every site, and
  `β_U^{-1/2} ∑_{y,i} g(y,i) ℳ₀(y; g)_i = ∑_{y,i} g(y,i) ∑_{T'} mObs y i (rawOf D, g) T'`,
  the objects `ℳ₀` being those of the step with the datum `D` and the class with zero old terms;
* with a constant `C ≥ 0` chosen with the thresholds (before the scale): for the same `mObs`,
  `‖mObs y i θ T'‖ ≤ C · obsPrefactor p s (β 3^k) · e^{-(3/2) κ_dec dExt T'}` on `physVq … q`. -/
theorem obsFamily_pair_fibre_prefactor_fromTowerG {d L N : ℕ} [NeZero L] {κmin : ℝ} (T : StepTowerG d L N κmin) {A₁ : ℝ} (hA : 0 < A₁)
    (p : ℕ) {CR s : ℝ} (hCR : 0 < CR) (hs0 : 0 < s) (hs : s < 1 / 2) :
    ∃ (β₀ CE CF C : ℝ), 3 ≤ β₀ ∧ 0 < CE ∧ 0 < CF ∧ 0 ≤ C ∧
      ∀ (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁] (h3N : L ^ T.m₀ ∣ N₁), 5 < N₁ →
      ∀ ν : ℝ, 0 < ν → ν * (L : ℝ) ^ (2 * (k + 1)) ≤ 1 → ∀ β : ℝ, β₀ ≤ β →
      ∀ p₁ : ℝ, 0 < p₁ → p₁ ≤ pLog A₁ p (β * (L : ℝ) ^ (k * (d - 2))) → ∀ q : ℝ, 0 < q → q ≤ 1 →
      StepScaleDataG T k hk N₁ ν β p₁ →
      ∀ (S : StepSetting d L N₁ T.m₁ k N (rhoSepG d L T.m₁)),
        S = T.step k hk N₁ ν β p₁ → ∀ hp : 0 < S.p₁,
      ∃ (Lb : Type) (_ : Fintype Lb)
        (Lab : CubeLabels (d := d) (L := L) (N₁ := N₁) (m₁ := T.m₁) (K := k + 1) T.m₀ (k + 1)
          Set.univ Lb) (εH : ℝ) (hεH : 0 < εH)
        (A : physParam N S → ℂ → LabelAct Lab (S.blockSplit T.m₀ hp).Ωb εH (2 * T.κdec - 1) T.κ0
          (K0 d L T.κ0 + 1))
        (mObs : CTorus d L N₁ T.m₁ (k + 1) → Fin N → physParam N S →
          Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := T.m₁) (K := k + 1) T.m₀ (k + 1)
            Set.univ) → ℂ),
        2 * εH ≤ CE * (Real.log (β * (L : ℝ) ^ (k * (d - 2)))) ^ (3 * p) / Real.sqrt (β * (L : ℝ) ^ (k * (d - 2))) +
          q * CF * (Real.log (β * (L : ℝ) ^ (k * (d - 2)))) ^ p / Real.sqrt (β * (L : ℝ) ^ (k * (d - 2))) ∧
        (∀ (y : CTorus d L N₁ T.m₁ (k + 1)) (i : Fin N)
          (hdj : ∀ Y ∈ obsDomains S (LocalCover.nbhdF T.m₀ y) T.m₀ k (LocalCover.fam T.m₀ y),
            IsDj T.m₀ (k + 1) Y),
          ∃ hR : 0 ≤ obsRg CR s (p : ℝ) (β * (L : ℝ) ^ (k * (d - 2))),
            1 < obsRg CR s (p : ℝ) (β * (L : ℝ) ^ (k * (d - 2))) ∧
            obsRg CR s (p : ℝ) (β * (L : ℝ) ^ (k * (d - 2))) * max (εH + εH) εH ≤
              stepTheta d L ((K0 d L T.κ0 + 1) + (K0 d L T.κ0 + 1) + K0 d L T.κ0 + K0 d L T.κ0)
                (2 * T.κdec - 1) T.κ0 T.κ' ∧
            ∃ Ev : Set (CTorus d L N₁ T.m₁ (k + 1)) →
                RawData d L (N₁ * L ^ T.m₁) (k + 1) N × (unitPts S.G' × Fin N → ℂ) → ℂ,
              (∀ Y, AnalyticOnNhd ℂ (Ev Y) (XiCRaw S.G' (compWeight L 1) ν (k + 1) 1 T.t ×ˢ
                {ψh : unitPts S.G' × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ lvCpsiG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2)))})) ∧
              (∀ Y, ∀ u ∈ XiCRaw S.G' (compWeight L 1) ν (k + 1) 1 T.t ×ˢ
                  {ψh : unitPts S.G' × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ lvCpsiG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2)))},
                ∀ u' ∈ XiCRaw S.G' (compWeight L 1) ν (k + 1) 1 T.t ×ˢ
                  {ψh : unitPts S.G' × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ lvCpsiG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2)))},
                AgHatDir S.hG' Y u u' → Ev Y u = Ev Y u') ∧
              (∀ Y, ∀ u ∈ XiCRaw S.G' (compWeight L 1) ν (k + 1) 1 T.t ×ˢ
                  {ψh : unitPts S.G' × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ lvCpsiG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2)))},
                ‖Ev Y u‖ ≤ (cK2' d L N (famConst d L T.BG₂ T.κ) * T.t) *
                  Real.exp (-(2 * T.κdec) * treeLenCovOne T.m₀ (k + 1) Y)) ∧
              (∀ θ T', mObs y i θ T' = obsCoeffParam (S.blockSplit T.m₀ hp).μ
                (fun θ t σ => tiltActObs A (show L ^ T.m₀ ∣ N₁ from h3N) T.κ0_ent hεH.le
                  hdj (le_refl _) (obsRg CR s (p : ℝ) (β * (L : ℝ) ^ (k * (d - 2)))) hR (ball (0 : ℂ) (3 / 2))
                  θ t σ)
                (fun m => obsY1 T.m₀ S (Lb ⊕ Lb)
                  (obsDomains S (LocalCover.nbhdF T.m₀ y) T.m₀ k (LocalCover.fam T.m₀ y)) m)
                (fun m => blockMarkC S T.m₀ hp m.1 m.2)
                (fun θ m T'' => obsHker
                  (obsDomains S (LocalCover.nbhdF T.m₀ y) T.m₀ k (LocalCover.fam T.m₀ y))
                  (fun Y => hatCoeff (Ev Y) (θ.1 : RawData d L (N₁ * L ^ T.m₁) (k + 1) N)
                    (obsUnitVec S m)) T.m₀ T'')
                (obsRemLab (obsDomains S (LocalCover.nbhdF T.m₀ y) T.m₀ k (LocalCover.fam T.m₀ y))
                  (fun Y => Sum.inl (Sum.inr Y))
                  (obsY0 T.m₀ (Lb ⊕ Lb)
                    (obsDomains S (LocalCover.nbhdF T.m₀ y) T.m₀ k (LocalCover.fam T.m₀ y))
                    (rootCube (m₀ := T.m₀) (blockIndex y))))
                (fun θ => obsGrFam S T.m₀ hp Ev
                  (obsDomains S (LocalCover.nbhdF T.m₀ y) T.m₀ k (LocalCover.fam T.m₀ y))
                  (XiCRaw S.G' (compWeight L 1) ν (k + 1) 1 T.t) θ) θ T') ∧
              ∀ T' : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := T.m₁) (K := k + 1) T.m₀
                  (k + 1) Set.univ),
                AnalyticOnNhd ℂ (fun θ => mObs y i θ T') (physVq S S.a₁ S.ν T.t q) ∧
                (∀ θ ∈ physVq S S.a₁ S.ν T.t q, ‖mObs y i θ T'‖ ≤
                  ((cK2' d L N (famConst d L T.BG₂ T.κ) * T.t / lvCpsiG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2)))) *
                      (CPE d L ((K0 d L T.κ0 + 1) + (K0 d L T.κ0 + 1) + K0 d L T.κ0 +
                          K0 d L T.κ0) (2 * T.κdec - 1) T.κ0 T.κ' * S.p₁ /
                        (obsRg CR s (p : ℝ) (β * (L : ℝ) ^ (k * (d - 2))))) *
                      (((N * L ^ (d * (T.m₀ + T.m₁ + 1)) : ℕ) : ℝ) * c1 d L) *
                      ((K0 d L T.κ0 + 1) + (K0 d L T.κ0 + 1) + K0 d L T.κ0 + K0 d L T.κ0) ^ 2 *
                      Real.exp ((min (2 * T.κdec) T.κ' - T.κ0) * cG d L) +
                    CPE d L ((K0 d L T.κ0 + 1) + (K0 d L T.κ0 + 1) + K0 d L T.κ0 + K0 d L T.κ0)
                        (2 * T.κdec - 1) T.κ0 T.κ' *
                      (∑ r, 8 * (cK2' d L N (famConst d L T.BG₂ T.κ) * T.t) *
                        (S.p₁ / lvCpsiG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2)))) ^ 2 * Real.exp (-T.κ0 *
                        (obsLab (Lab.sum Lab) hdj).dl
                          (obsRemLab
                            (obsDomains S (LocalCover.nbhdF T.m₀ y) T.m₀ k (LocalCover.fam T.m₀ y))
                            (fun Y => Sum.inl (Sum.inr Y))
                            (obsY0 T.m₀ (Lb ⊕ Lb)
                              (obsDomains S (LocalCover.nbhdF T.m₀ y) T.m₀ k (LocalCover.fam T.m₀ y))
                              (rootCube (m₀ := T.m₀) (blockIndex y))) r)))) *
                  Real.exp (-(min (min (2 * T.κdec) T.κ' - T.κ0 - 1) T.κ') * dExt T')) ∧
                (∀ θ ∈ physVq S S.a₁ S.ν T.t q, mObs y i θ T' ≠ 0 →
                  rootCube (m₀ := T.m₀) (blockIndex y) ∈ T' ∧ IsPolyDom T.m₀ (k + 1) (sitesOf T')) ∧
                (∀ θ ∈ physVq S S.a₁ S.ν T.t q, ∀ θ' ∈ physVq S S.a₁ S.ν T.t q,
                  agreeOn (thickSet S.G' (sitesOf T'))
                    (θ.1 : RawData d L (N₁ * L ^ T.m₁) (k + 1) N)
                    (θ'.1 : RawData d L (N₁ * L ^ T.m₁) (k + 1) N) →
                  (∀ x ∈ sitesOf T', θ.2 x = θ'.2 x) → mObs y i θ T' = mObs y i θ' T') ∧
                (∀ θ ∈ physVq S S.a₁ S.ν T.t q, ∀ θ' ∈ physVq S S.a₁ S.ν T.t q,
                  physRestrict (N := N) (sitesOf T') (physIncl N S θ) =
                    physRestrict (sitesOf T') (physIncl N S θ') →
                  mObs y i θ T' = mObs y i θ' T') ∧
                (∀ θ ∈ physVq S S.a₁ S.ν T.t q, ‖mObs y i θ T'‖ ≤
                  C * obsPrefactor p s (β * (L : ℝ) ^ (k * (d - 2))) * Real.exp (-(3 / 2 * T.κdec) * dExt T'))) ∧
        ∀ (D : BgData S.G' N) (hDh : ∀ y i, D.h y i = (S.h₀ i : ℂ)),
          XiCData S.G' S.a S.ν (k + 1) 1 T.t D →
          ∀ g : Fld d L N₁ T.m₁ (k + 1) N, ∑ x', ∑ i', ‖g x' i'‖ < q →
            (∀ (y : CTorus d L N₁ T.m₁ (k + 1)) (i : Fin N),
              (S.withDatum D hDh).M0C (zeroClass d L N₁ T.m₁ k N (rhoSepG d L T.m₁)) g y i =
                ((S.betaU ^ (1 / 2 : ℝ) : ℝ) : ℂ) *
                  ∑ T', mObs y i ((⟨rawOf D, rawOf_mem_rawSub _⟩ : rawSub N S.G'), g) T') ∧
            ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
                ∑ y : CTorus d L N₁ T.m₁ (k + 1), ∑ i : Fin N,
                  g y i * (S.withDatum D hDh).M0C (zeroClass d L N₁ T.m₁ k N (rhoSepG d L T.m₁))
                    g y i =
              ∑ y : CTorus d L N₁ T.m₁ (k + 1), ∑ i : Fin N,
                g y i * ∑ T', mObs y i ((⟨rawOf D, rawOf_mem_rawSub _⟩ : rawSub N S.G'), g) T' := by
  exact obsFamily_pair_fibre_prefactor_fromTowerG_rho T hA p hCR hs0 hs 1

open Classical in
/-- At source radius `ρ` (`q ≤ ρ`, `max 1 ρ ≤ β`); the landed theorem is its `ρ = 1` corollary.  **The observable coefficient family of all sites, and the source pairing on the fibre.**
Beyond the threshold of `obsFamily_full_fromTowerG`, at every scale datum and for `0 < q ≤ 1` there
are a label system, an amplitude `ε_H`, an activity `A` and a function `mObs y i θ T'` of the
observable site `(y, i)`, the parameter `θ = (raw datum, source)` and the finite set `T'` of
level-one blocks, chosen before the datum and the source, such that:
* for every site `(y, i)` there are an amplitude `obsRg` and a family `Ev` (analytic, local,
  bounded) with `mObs y i θ T' = obsCoeffParam … θ T'` for the tilted activity of `A` and this
  `Ev`; `θ ↦ mObs y i θ T'` is analytic on `physVq … q`, bounded there by
  `(B₁ + B₂) e^{-λ dExt T'}`, `λ = min (min (2 κ_dec) κ' - κ₀ - 1) κ'`, non-zero only if `T'`
  contains the root cube of `y` and its sites form a polymer, and local:
  `mObs y i θ T' = mObs y i θ' T'` for `θ, θ'` of `physVq … q` whose raw data agree on
  `thickSet (sitesOf T')` and whose sources agree on `sitesOf T'`; equality of their
  `physRestrict (sitesOf T')` images also implies equality of the coefficients;
* for every datum `D` of the chart `Ξ^c(𝔹_{k+1}; 1, T.t)` with constant field `h₀` and every source
  `g` with `∑ |g| < q`: `ℳ₀(y; g)_i = β_U^{1/2} ∑_{T'} mObs y i (rawOf D, g) T'` for every site, and
  `β_U^{-1/2} ∑_{y,i} g(y,i) ℳ₀(y; g)_i = ∑_{y,i} g(y,i) ∑_{T'} mObs y i (rawOf D, g) T'`,
  the objects `ℳ₀` being those of the step with the datum `D` and the class with zero old terms. -/
theorem obsFamily_pair_fibre_fromTowerG_rho {d L N : ℕ} [NeZero L] {κmin : ℝ} (T : StepTowerG d L N κmin) {A₁ : ℝ} (hA : 0 < A₁)
    (p : ℕ) {CR s : ℝ} (hCR : 0 < CR) (hs0 : 0 < s) (hs : s < 1 / 2) (ρ : ℝ) :
    ∃ (β₀ CE CF : ℝ), 3 ≤ β₀ ∧ 0 < CE ∧ 0 < CF ∧
      ∀ (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁] (h3N : L ^ T.m₀ ∣ N₁), 5 < N₁ →
      ∀ ν : ℝ, 0 < ν → ν * (L : ℝ) ^ (2 * (k + 1)) ≤ 1 → ∀ β : ℝ, β₀ ≤ β →
      ∀ p₁ : ℝ, 0 < p₁ → p₁ ≤ pLog A₁ p (β * (L : ℝ) ^ (k * (d - 2))) → ∀ q : ℝ, 0 < q → q ≤ ρ →
      StepScaleDataG T k hk N₁ ν β p₁ →
      ∀ (S : StepSetting d L N₁ T.m₁ k N (rhoSepG d L T.m₁)),
        S = T.step k hk N₁ ν β p₁ → ∀ hp : 0 < S.p₁,
      ∃ (Lb : Type) (_ : Fintype Lb)
        (Lab : CubeLabels (d := d) (L := L) (N₁ := N₁) (m₁ := T.m₁) (K := k + 1) T.m₀ (k + 1)
          Set.univ Lb) (εH : ℝ) (hεH : 0 < εH)
        (A : physParam N S → ℂ → LabelAct Lab (S.blockSplit T.m₀ hp).Ωb εH (2 * T.κdec - 1) T.κ0
          (K0 d L T.κ0 + 1))
        (mObs : CTorus d L N₁ T.m₁ (k + 1) → Fin N → physParam N S →
          Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := T.m₁) (K := k + 1) T.m₀ (k + 1)
            Set.univ) → ℂ),
        2 * εH ≤ CE * (Real.log (β * (L : ℝ) ^ (k * (d - 2)))) ^ (3 * p) / Real.sqrt (β * (L : ℝ) ^ (k * (d - 2))) +
          q * CF * (Real.log (β * (L : ℝ) ^ (k * (d - 2)))) ^ p / Real.sqrt (β * (L : ℝ) ^ (k * (d - 2))) ∧
        (∀ (y : CTorus d L N₁ T.m₁ (k + 1)) (i : Fin N)
          (hdj : ∀ Y ∈ obsDomains S (LocalCover.nbhdF T.m₀ y) T.m₀ k (LocalCover.fam T.m₀ y),
            IsDj T.m₀ (k + 1) Y),
          ∃ hR : 0 ≤ obsRg CR s (p : ℝ) (β * (L : ℝ) ^ (k * (d - 2))),
            1 < obsRg CR s (p : ℝ) (β * (L : ℝ) ^ (k * (d - 2))) ∧
            obsRg CR s (p : ℝ) (β * (L : ℝ) ^ (k * (d - 2))) * max (εH + εH) εH ≤
              stepTheta d L ((K0 d L T.κ0 + 1) + (K0 d L T.κ0 + 1) + K0 d L T.κ0 + K0 d L T.κ0)
                (2 * T.κdec - 1) T.κ0 T.κ' ∧
            ∃ Ev : Set (CTorus d L N₁ T.m₁ (k + 1)) →
                RawData d L (N₁ * L ^ T.m₁) (k + 1) N × (unitPts S.G' × Fin N → ℂ) → ℂ,
              (∀ Y, AnalyticOnNhd ℂ (Ev Y) (XiCRaw S.G' (compWeight L 1) ν (k + 1) 1 T.t ×ˢ
                {ψh : unitPts S.G' × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ lvCpsiG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2)))})) ∧
              (∀ Y, ∀ u ∈ XiCRaw S.G' (compWeight L 1) ν (k + 1) 1 T.t ×ˢ
                  {ψh : unitPts S.G' × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ lvCpsiG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2)))},
                ∀ u' ∈ XiCRaw S.G' (compWeight L 1) ν (k + 1) 1 T.t ×ˢ
                  {ψh : unitPts S.G' × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ lvCpsiG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2)))},
                AgHatDir S.hG' Y u u' → Ev Y u = Ev Y u') ∧
              (∀ Y, ∀ u ∈ XiCRaw S.G' (compWeight L 1) ν (k + 1) 1 T.t ×ˢ
                  {ψh : unitPts S.G' × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ lvCpsiG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2)))},
                ‖Ev Y u‖ ≤ (cK2' d L N (famConst d L T.BG₂ T.κ) * T.t) *
                  Real.exp (-(2 * T.κdec) * treeLenCovOne T.m₀ (k + 1) Y)) ∧
              (∀ θ T', mObs y i θ T' = obsCoeffParam (S.blockSplit T.m₀ hp).μ
                (fun θ t σ => tiltActObs A (show L ^ T.m₀ ∣ N₁ from h3N) T.κ0_ent hεH.le
                  hdj (le_refl _) (obsRg CR s (p : ℝ) (β * (L : ℝ) ^ (k * (d - 2)))) hR (ball (0 : ℂ) (3 / 2))
                  θ t σ)
                (fun m => obsY1 T.m₀ S (Lb ⊕ Lb)
                  (obsDomains S (LocalCover.nbhdF T.m₀ y) T.m₀ k (LocalCover.fam T.m₀ y)) m)
                (fun m => blockMarkC S T.m₀ hp m.1 m.2)
                (fun θ m T'' => obsHker
                  (obsDomains S (LocalCover.nbhdF T.m₀ y) T.m₀ k (LocalCover.fam T.m₀ y))
                  (fun Y => hatCoeff (Ev Y) (θ.1 : RawData d L (N₁ * L ^ T.m₁) (k + 1) N)
                    (obsUnitVec S m)) T.m₀ T'')
                (obsRemLab (obsDomains S (LocalCover.nbhdF T.m₀ y) T.m₀ k (LocalCover.fam T.m₀ y))
                  (fun Y => Sum.inl (Sum.inr Y))
                  (obsY0 T.m₀ (Lb ⊕ Lb)
                    (obsDomains S (LocalCover.nbhdF T.m₀ y) T.m₀ k (LocalCover.fam T.m₀ y))
                    (rootCube (m₀ := T.m₀) (blockIndex y))))
                (fun θ => obsGrFam S T.m₀ hp Ev
                  (obsDomains S (LocalCover.nbhdF T.m₀ y) T.m₀ k (LocalCover.fam T.m₀ y))
                  (XiCRaw S.G' (compWeight L 1) ν (k + 1) 1 T.t) θ) θ T') ∧
              ∀ T' : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := T.m₁) (K := k + 1) T.m₀
                  (k + 1) Set.univ),
                AnalyticOnNhd ℂ (fun θ => mObs y i θ T') (physVqRho S S.a₁ S.ν T.t ρ q) ∧
                (∀ θ ∈ physVqRho S S.a₁ S.ν T.t ρ q, ‖mObs y i θ T'‖ ≤
                  ((cK2' d L N (famConst d L T.BG₂ T.κ) * T.t / lvCpsiG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2)))) *
                      (CPE d L ((K0 d L T.κ0 + 1) + (K0 d L T.κ0 + 1) + K0 d L T.κ0 +
                          K0 d L T.κ0) (2 * T.κdec - 1) T.κ0 T.κ' * S.p₁ /
                        (obsRg CR s (p : ℝ) (β * (L : ℝ) ^ (k * (d - 2))))) *
                      (((N * L ^ (d * (T.m₀ + T.m₁ + 1)) : ℕ) : ℝ) * c1 d L) *
                      ((K0 d L T.κ0 + 1) + (K0 d L T.κ0 + 1) + K0 d L T.κ0 + K0 d L T.κ0) ^ 2 *
                      Real.exp ((min (2 * T.κdec) T.κ' - T.κ0) * cG d L) +
                    CPE d L ((K0 d L T.κ0 + 1) + (K0 d L T.κ0 + 1) + K0 d L T.κ0 + K0 d L T.κ0)
                        (2 * T.κdec - 1) T.κ0 T.κ' *
                      (∑ r, 8 * (cK2' d L N (famConst d L T.BG₂ T.κ) * T.t) *
                        (S.p₁ / lvCpsiG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2)))) ^ 2 * Real.exp (-T.κ0 *
                        (obsLab (Lab.sum Lab) hdj).dl
                          (obsRemLab
                            (obsDomains S (LocalCover.nbhdF T.m₀ y) T.m₀ k (LocalCover.fam T.m₀ y))
                            (fun Y => Sum.inl (Sum.inr Y))
                            (obsY0 T.m₀ (Lb ⊕ Lb)
                              (obsDomains S (LocalCover.nbhdF T.m₀ y) T.m₀ k (LocalCover.fam T.m₀ y))
                              (rootCube (m₀ := T.m₀) (blockIndex y))) r)))) *
                  Real.exp (-(min (min (2 * T.κdec) T.κ' - T.κ0 - 1) T.κ') * dExt T')) ∧
                (∀ θ ∈ physVqRho S S.a₁ S.ν T.t ρ q, mObs y i θ T' ≠ 0 →
                  rootCube (m₀ := T.m₀) (blockIndex y) ∈ T' ∧ IsPolyDom T.m₀ (k + 1) (sitesOf T')) ∧
                (∀ θ ∈ physVqRho S S.a₁ S.ν T.t ρ q, ∀ θ' ∈ physVqRho S S.a₁ S.ν T.t ρ q,
                  agreeOn (thickSet S.G' (sitesOf T'))
                    (θ.1 : RawData d L (N₁ * L ^ T.m₁) (k + 1) N)
                    (θ'.1 : RawData d L (N₁ * L ^ T.m₁) (k + 1) N) →
                  (∀ x ∈ sitesOf T', θ.2 x = θ'.2 x) → mObs y i θ T' = mObs y i θ' T') ∧
                (∀ θ ∈ physVqRho S S.a₁ S.ν T.t ρ q, ∀ θ' ∈ physVqRho S S.a₁ S.ν T.t ρ q,
                  physRestrict (N := N) (sitesOf T') (physIncl N S θ) =
                    physRestrict (sitesOf T') (physIncl N S θ') →
                  mObs y i θ T' = mObs y i θ' T')) ∧
        ∀ (D : BgData S.G' N) (hDh : ∀ y i, D.h y i = (S.h₀ i : ℂ)),
          XiCData S.G' S.a S.ν (k + 1) 1 T.t D →
          ∀ g : Fld d L N₁ T.m₁ (k + 1) N, ∑ x', ∑ i', ‖g x' i'‖ < q →
            (∀ (y : CTorus d L N₁ T.m₁ (k + 1)) (i : Fin N),
              (S.withDatum D hDh).M0C (zeroClass d L N₁ T.m₁ k N (rhoSepG d L T.m₁)) g y i =
                ((S.betaU ^ (1 / 2 : ℝ) : ℝ) : ℂ) *
                  ∑ T', mObs y i ((⟨rawOf D, rawOf_mem_rawSub _⟩ : rawSub N S.G'), g) T') ∧
            ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
                ∑ y : CTorus d L N₁ T.m₁ (k + 1), ∑ i : Fin N,
                  g y i * (S.withDatum D hDh).M0C (zeroClass d L N₁ T.m₁ k N (rhoSepG d L T.m₁))
                    g y i =
              ∑ y : CTorus d L N₁ T.m₁ (k + 1), ∑ i : Fin N,
                g y i * ∑ T', mObs y i ((⟨rawOf D, rawOf_mem_rawSub _⟩ : rawSub N S.G'), g) T' := by
  classical
  obtain ⟨β₀, CE, CF, C, h3, hCE, hCF, -, H⟩ := obsFamily_pair_fibre_prefactor_fromTowerG_rho T hA p hCR hs0 hs ρ
  refine ⟨β₀, CE, CF, h3, hCE, hCF, ?_⟩
  intro k hk N₁ _ h3N hN ν hνpos hν β hβ p₁ hp0 hp₁ q hq0 hq1 Dsc S hS hp
  obtain ⟨Lb, hLb, Lab, εH, hεH, A, mObs, hamp, hsite, hval⟩ :=
    H k hk N₁ h3N hN ν hνpos hν β hβ p₁ hp0 hp₁ q hq0 hq1 Dsc S hS hp
  refine ⟨Lb, hLb, Lab, εH, hεH, A, mObs, hamp, fun y i hdj => ?_, hval⟩
  obtain ⟨hR, h1, hεΘ, Ev, ha, hd, hb, hmk, hfam⟩ := hsite y i hdj
  exact ⟨hR, h1, hεΘ, Ev, ha, hd, hb, hmk, fun T' =>
    ⟨(hfam T').1, (hfam T').2.1, (hfam T').2.2.1, (hfam T').2.2.2.1, (hfam T').2.2.2.2.1⟩⟩

open Classical in
/-- **The observable coefficient family of all sites, and the source pairing on the fibre.**
Beyond the threshold of `obsFamily_full_fromTowerG`, at every scale datum and for `0 < q ≤ 1` there
are a label system, an amplitude `ε_H`, an activity `A` and a function `mObs y i θ T'` of the
observable site `(y, i)`, the parameter `θ = (raw datum, source)` and the finite set `T'` of
level-one blocks, chosen before the datum and the source, such that:
* for every site `(y, i)` there are an amplitude `obsRg` and a family `Ev` (analytic, local,
  bounded) with `mObs y i θ T' = obsCoeffParam … θ T'` for the tilted activity of `A` and this
  `Ev`; `θ ↦ mObs y i θ T'` is analytic on `physVq … q`, bounded there by
  `(B₁ + B₂) e^{-λ dExt T'}`, `λ = min (min (2 κ_dec) κ' - κ₀ - 1) κ'`, non-zero only if `T'`
  contains the root cube of `y` and its sites form a polymer, and local:
  `mObs y i θ T' = mObs y i θ' T'` for `θ, θ'` of `physVq … q` whose raw data agree on
  `thickSet (sitesOf T')` and whose sources agree on `sitesOf T'`; equality of their
  `physRestrict (sitesOf T')` images also implies equality of the coefficients;
* for every datum `D` of the chart `Ξ^c(𝔹_{k+1}; 1, T.t)` with constant field `h₀` and every source
  `g` with `∑ |g| < q`: `ℳ₀(y; g)_i = β_U^{1/2} ∑_{T'} mObs y i (rawOf D, g) T'` for every site, and
  `β_U^{-1/2} ∑_{y,i} g(y,i) ℳ₀(y; g)_i = ∑_{y,i} g(y,i) ∑_{T'} mObs y i (rawOf D, g) T'`,
  the objects `ℳ₀` being those of the step with the datum `D` and the class with zero old terms. -/
theorem obsFamily_pair_fibre_fromTowerG {d L N : ℕ} [NeZero L] {κmin : ℝ} (T : StepTowerG d L N κmin) {A₁ : ℝ} (hA : 0 < A₁)
    (p : ℕ) {CR s : ℝ} (hCR : 0 < CR) (hs0 : 0 < s) (hs : s < 1 / 2) :
    ∃ (β₀ CE CF : ℝ), 3 ≤ β₀ ∧ 0 < CE ∧ 0 < CF ∧
      ∀ (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁] (h3N : L ^ T.m₀ ∣ N₁), 5 < N₁ →
      ∀ ν : ℝ, 0 < ν → ν * (L : ℝ) ^ (2 * (k + 1)) ≤ 1 → ∀ β : ℝ, β₀ ≤ β →
      ∀ p₁ : ℝ, 0 < p₁ → p₁ ≤ pLog A₁ p (β * (L : ℝ) ^ (k * (d - 2))) → ∀ q : ℝ, 0 < q → q ≤ 1 →
      StepScaleDataG T k hk N₁ ν β p₁ →
      ∀ (S : StepSetting d L N₁ T.m₁ k N (rhoSepG d L T.m₁)),
        S = T.step k hk N₁ ν β p₁ → ∀ hp : 0 < S.p₁,
      ∃ (Lb : Type) (_ : Fintype Lb)
        (Lab : CubeLabels (d := d) (L := L) (N₁ := N₁) (m₁ := T.m₁) (K := k + 1) T.m₀ (k + 1)
          Set.univ Lb) (εH : ℝ) (hεH : 0 < εH)
        (A : physParam N S → ℂ → LabelAct Lab (S.blockSplit T.m₀ hp).Ωb εH (2 * T.κdec - 1) T.κ0
          (K0 d L T.κ0 + 1))
        (mObs : CTorus d L N₁ T.m₁ (k + 1) → Fin N → physParam N S →
          Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := T.m₁) (K := k + 1) T.m₀ (k + 1)
            Set.univ) → ℂ),
        2 * εH ≤ CE * (Real.log (β * (L : ℝ) ^ (k * (d - 2)))) ^ (3 * p) / Real.sqrt (β * (L : ℝ) ^ (k * (d - 2))) +
          q * CF * (Real.log (β * (L : ℝ) ^ (k * (d - 2)))) ^ p / Real.sqrt (β * (L : ℝ) ^ (k * (d - 2))) ∧
        (∀ (y : CTorus d L N₁ T.m₁ (k + 1)) (i : Fin N)
          (hdj : ∀ Y ∈ obsDomains S (LocalCover.nbhdF T.m₀ y) T.m₀ k (LocalCover.fam T.m₀ y),
            IsDj T.m₀ (k + 1) Y),
          ∃ hR : 0 ≤ obsRg CR s (p : ℝ) (β * (L : ℝ) ^ (k * (d - 2))),
            1 < obsRg CR s (p : ℝ) (β * (L : ℝ) ^ (k * (d - 2))) ∧
            obsRg CR s (p : ℝ) (β * (L : ℝ) ^ (k * (d - 2))) * max (εH + εH) εH ≤
              stepTheta d L ((K0 d L T.κ0 + 1) + (K0 d L T.κ0 + 1) + K0 d L T.κ0 + K0 d L T.κ0)
                (2 * T.κdec - 1) T.κ0 T.κ' ∧
            ∃ Ev : Set (CTorus d L N₁ T.m₁ (k + 1)) →
                RawData d L (N₁ * L ^ T.m₁) (k + 1) N × (unitPts S.G' × Fin N → ℂ) → ℂ,
              (∀ Y, AnalyticOnNhd ℂ (Ev Y) (XiCRaw S.G' (compWeight L 1) ν (k + 1) 1 T.t ×ˢ
                {ψh : unitPts S.G' × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ lvCpsiG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2)))})) ∧
              (∀ Y, ∀ u ∈ XiCRaw S.G' (compWeight L 1) ν (k + 1) 1 T.t ×ˢ
                  {ψh : unitPts S.G' × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ lvCpsiG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2)))},
                ∀ u' ∈ XiCRaw S.G' (compWeight L 1) ν (k + 1) 1 T.t ×ˢ
                  {ψh : unitPts S.G' × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ lvCpsiG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2)))},
                AgHatDir S.hG' Y u u' → Ev Y u = Ev Y u') ∧
              (∀ Y, ∀ u ∈ XiCRaw S.G' (compWeight L 1) ν (k + 1) 1 T.t ×ˢ
                  {ψh : unitPts S.G' × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ lvCpsiG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2)))},
                ‖Ev Y u‖ ≤ (cK2' d L N (famConst d L T.BG₂ T.κ) * T.t) *
                  Real.exp (-(2 * T.κdec) * treeLenCovOne T.m₀ (k + 1) Y)) ∧
              (∀ θ T', mObs y i θ T' = obsCoeffParam (S.blockSplit T.m₀ hp).μ
                (fun θ t σ => tiltActObs A (show L ^ T.m₀ ∣ N₁ from h3N) T.κ0_ent hεH.le
                  hdj (le_refl _) (obsRg CR s (p : ℝ) (β * (L : ℝ) ^ (k * (d - 2)))) hR (ball (0 : ℂ) (3 / 2))
                  θ t σ)
                (fun m => obsY1 T.m₀ S (Lb ⊕ Lb)
                  (obsDomains S (LocalCover.nbhdF T.m₀ y) T.m₀ k (LocalCover.fam T.m₀ y)) m)
                (fun m => blockMarkC S T.m₀ hp m.1 m.2)
                (fun θ m T'' => obsHker
                  (obsDomains S (LocalCover.nbhdF T.m₀ y) T.m₀ k (LocalCover.fam T.m₀ y))
                  (fun Y => hatCoeff (Ev Y) (θ.1 : RawData d L (N₁ * L ^ T.m₁) (k + 1) N)
                    (obsUnitVec S m)) T.m₀ T'')
                (obsRemLab (obsDomains S (LocalCover.nbhdF T.m₀ y) T.m₀ k (LocalCover.fam T.m₀ y))
                  (fun Y => Sum.inl (Sum.inr Y))
                  (obsY0 T.m₀ (Lb ⊕ Lb)
                    (obsDomains S (LocalCover.nbhdF T.m₀ y) T.m₀ k (LocalCover.fam T.m₀ y))
                    (rootCube (m₀ := T.m₀) (blockIndex y))))
                (fun θ => obsGrFam S T.m₀ hp Ev
                  (obsDomains S (LocalCover.nbhdF T.m₀ y) T.m₀ k (LocalCover.fam T.m₀ y))
                  (XiCRaw S.G' (compWeight L 1) ν (k + 1) 1 T.t) θ) θ T') ∧
              ∀ T' : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := T.m₁) (K := k + 1) T.m₀
                  (k + 1) Set.univ),
                AnalyticOnNhd ℂ (fun θ => mObs y i θ T') (physVq S S.a₁ S.ν T.t q) ∧
                (∀ θ ∈ physVq S S.a₁ S.ν T.t q, ‖mObs y i θ T'‖ ≤
                  ((cK2' d L N (famConst d L T.BG₂ T.κ) * T.t / lvCpsiG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2)))) *
                      (CPE d L ((K0 d L T.κ0 + 1) + (K0 d L T.κ0 + 1) + K0 d L T.κ0 +
                          K0 d L T.κ0) (2 * T.κdec - 1) T.κ0 T.κ' * S.p₁ /
                        (obsRg CR s (p : ℝ) (β * (L : ℝ) ^ (k * (d - 2))))) *
                      (((N * L ^ (d * (T.m₀ + T.m₁ + 1)) : ℕ) : ℝ) * c1 d L) *
                      ((K0 d L T.κ0 + 1) + (K0 d L T.κ0 + 1) + K0 d L T.κ0 + K0 d L T.κ0) ^ 2 *
                      Real.exp ((min (2 * T.κdec) T.κ' - T.κ0) * cG d L) +
                    CPE d L ((K0 d L T.κ0 + 1) + (K0 d L T.κ0 + 1) + K0 d L T.κ0 + K0 d L T.κ0)
                        (2 * T.κdec - 1) T.κ0 T.κ' *
                      (∑ r, 8 * (cK2' d L N (famConst d L T.BG₂ T.κ) * T.t) *
                        (S.p₁ / lvCpsiG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2)))) ^ 2 * Real.exp (-T.κ0 *
                        (obsLab (Lab.sum Lab) hdj).dl
                          (obsRemLab
                            (obsDomains S (LocalCover.nbhdF T.m₀ y) T.m₀ k (LocalCover.fam T.m₀ y))
                            (fun Y => Sum.inl (Sum.inr Y))
                            (obsY0 T.m₀ (Lb ⊕ Lb)
                              (obsDomains S (LocalCover.nbhdF T.m₀ y) T.m₀ k (LocalCover.fam T.m₀ y))
                              (rootCube (m₀ := T.m₀) (blockIndex y))) r)))) *
                  Real.exp (-(min (min (2 * T.κdec) T.κ' - T.κ0 - 1) T.κ') * dExt T')) ∧
                (∀ θ ∈ physVq S S.a₁ S.ν T.t q, mObs y i θ T' ≠ 0 →
                  rootCube (m₀ := T.m₀) (blockIndex y) ∈ T' ∧ IsPolyDom T.m₀ (k + 1) (sitesOf T')) ∧
                (∀ θ ∈ physVq S S.a₁ S.ν T.t q, ∀ θ' ∈ physVq S S.a₁ S.ν T.t q,
                  agreeOn (thickSet S.G' (sitesOf T'))
                    (θ.1 : RawData d L (N₁ * L ^ T.m₁) (k + 1) N)
                    (θ'.1 : RawData d L (N₁ * L ^ T.m₁) (k + 1) N) →
                  (∀ x ∈ sitesOf T', θ.2 x = θ'.2 x) → mObs y i θ T' = mObs y i θ' T') ∧
                (∀ θ ∈ physVq S S.a₁ S.ν T.t q, ∀ θ' ∈ physVq S S.a₁ S.ν T.t q,
                  physRestrict (N := N) (sitesOf T') (physIncl N S θ) =
                    physRestrict (sitesOf T') (physIncl N S θ') →
                  mObs y i θ T' = mObs y i θ' T')) ∧
        ∀ (D : BgData S.G' N) (hDh : ∀ y i, D.h y i = (S.h₀ i : ℂ)),
          XiCData S.G' S.a S.ν (k + 1) 1 T.t D →
          ∀ g : Fld d L N₁ T.m₁ (k + 1) N, ∑ x', ∑ i', ‖g x' i'‖ < q →
            (∀ (y : CTorus d L N₁ T.m₁ (k + 1)) (i : Fin N),
              (S.withDatum D hDh).M0C (zeroClass d L N₁ T.m₁ k N (rhoSepG d L T.m₁)) g y i =
                ((S.betaU ^ (1 / 2 : ℝ) : ℝ) : ℂ) *
                  ∑ T', mObs y i ((⟨rawOf D, rawOf_mem_rawSub _⟩ : rawSub N S.G'), g) T') ∧
            ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
                ∑ y : CTorus d L N₁ T.m₁ (k + 1), ∑ i : Fin N,
                  g y i * (S.withDatum D hDh).M0C (zeroClass d L N₁ T.m₁ k N (rhoSepG d L T.m₁))
                    g y i =
              ∑ y : CTorus d L N₁ T.m₁ (k + 1), ∑ i : Fin N,
                g y i * ∑ T', mObs y i ((⟨rawOf D, rawOf_mem_rawSub _⟩ : rawSub N S.G'), g) T' := by
  exact obsFamily_pair_fibre_fromTowerG_rho T hA p hCR hs0 hs 1

open Classical in
/-- At source radius `ρ` (`q ≤ ρ`, `max 1 ρ ≤ β`); the landed theorem is its `ρ = 1` corollary.  **The observable coefficient family of all sites on the fibre, with the prefactor bound.**
Beyond the threshold of `obsFamily_full_fromTower`, at every scale datum and for `0 < q ≤ 1` there
are a label system, an amplitude `ε_H`, an activity `A` and a function `mObs y i θ T'` of the
observable site `(y, i)`, the parameter `θ = (raw datum, source)` and the finite set `T'` of
level-one blocks, chosen before the datum and the source, such that:
* for every site `(y, i)` there are an amplitude `obsRg` and a family `Ev` (analytic, local,
  bounded) with `mObs y i θ T' = obsCoeffParam … θ T'` for the tilted activity of `A` and this
  `Ev`; `θ ↦ mObs y i θ T'` is analytic on `physVq … q`, bounded there by
  `(B₁ + B₂) e^{-λ dExt T'}`, `λ = min (min (2 κ_dec) κ' - κ₀ - 1) κ'`, non-zero only if `T'`
  contains the root cube of `y` and its sites form a polymer, and local:
  `mObs y i θ T' = mObs y i θ' T'` for `θ, θ'` of `physVq … q` whose raw data agree on
  `thickSet (sitesOf T')` and whose sources agree on `sitesOf T'`; equality of their
  `physRestrict (sitesOf T')` images also implies equality of the coefficients;
* for every datum `D` of the chart `Ξ^c(𝔹_{k+1}; 1, T.t)` with constant field `h₀` and every source
  `g` with `∑ |g| < q`: `ℳ₀(y; g)_i = β_U^{1/2} ∑_{T'} mObs y i (rawOf D, g) T'` for every site, and
  `β_U^{-1/2} ∑_{y,i} g(y,i) ℳ₀(y; g)_i = ∑_{y,i} g(y,i) ∑_{T'} mObs y i (rawOf D, g) T'`,
  the objects `ℳ₀` being those of the step with the datum `D` and the class with zero old terms;
* with a constant `C ≥ 0` chosen with the thresholds (before the scale): for the same `mObs`,
  `‖mObs y i θ T'‖ ≤ C · obsPrefactor p s (β 3^k) · e^{-(3/2) κ_dec dExt T'}` on `physVq … q`. -/
theorem obsFamily_pair_fibre_prefactor_fromTower_rho {κmin : ℝ} (T : StepTower κmin) {A₁ : ℝ} (hA : 0 < A₁)
    (p : ℕ) {CR s : ℝ} (hCR : 0 < CR) (hs0 : 0 < s) (hs : s < 1 / 2) (ρ : ℝ) :
    ∃ (β₀ CE CF C : ℝ), 3 ≤ β₀ ∧ 0 < CE ∧ 0 < CF ∧ 0 ≤ C ∧
      ∀ (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁] (h3N : 3 ∣ N₁), 5 < N₁ →
      ∀ ν : ℝ, 0 < ν → ν * 3 ^ (2 * (k + 1)) ≤ 1 → ∀ β : ℝ, β₀ ≤ β →
      ∀ p₁ : ℝ, 0 < p₁ → p₁ ≤ pLog A₁ p (β * 3 ^ k) → ∀ q : ℝ, 0 < q → q ≤ ρ →
      ∀ (Dsc : StepScaleData T k hk N₁ ν β p₁)
        (S : StepSetting 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)),
        S = T.step k hk N₁ ν β p₁ → ∀ hp : 0 < S.p₁,
      ∃ (Lb : Type) (_ : Fintype Lb)
        (Lab : CubeLabels (d := 3) (L := 3) (N₁ := N₁) (m₁ := T.m₁) (K := k + 1) 1 (k + 1)
          Set.univ Lb) (εH : ℝ) (hεH : 0 < εH)
        (A : physParam 2 S → ℂ → LabelAct Lab (S.blockSplit 1 hp).Ωb εH (2 * T.κdec - 1) T.κ0
          (K0 3 3 T.κ0 + 1))
        (mObs : CTorus 3 3 N₁ T.m₁ (k + 1) → Fin 2 → physParam 2 S →
          Finset (CubeB (d := 3) (L := 3) (N₁ := N₁) (m₁ := T.m₁) (K := k + 1) 1 (k + 1)
            Set.univ) → ℂ),
        2 * εH ≤ CE * (Real.log (β * 3 ^ k)) ^ (3 * p) / Real.sqrt (β * 3 ^ k) +
          q * CF * (Real.log (β * 3 ^ k)) ^ p / Real.sqrt (β * 3 ^ k) ∧
        (∀ (y : CTorus 3 3 N₁ T.m₁ (k + 1)) (i : Fin 2)
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
              (∀ θ T', mObs y i θ T' = obsCoeffParam (S.blockSplit 1 hp).μ
                (fun θ t σ => tiltActObs A (show 3 ^ 1 ∣ N₁ by simpa using h3N) T.κ0_ent hεH.le
                  hdj (le_refl _) (obsRg CR s (p : ℝ) (β * 3 ^ k)) hR (ball (0 : ℂ) (3 / 2))
                  θ t σ)
                (fun m => obsY1 1 S (Lb ⊕ Lb)
                  (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y)) m)
                (fun m => blockMarkC S 1 hp m.1 m.2)
                (fun θ m T'' => obsHker
                  (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y))
                  (fun Y => hatCoeff (Ev Y) (θ.1 : RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2)
                    (obsUnitVec S m)) 1 T'')
                (obsRemLab (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y))
                  (fun Y => Sum.inl (Sum.inr Y))
                  (obsY0 1 (Lb ⊕ Lb)
                    (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y))
                    (rootCube (m₀ := 1) (blockIndex y))))
                (fun θ => obsGrFam S 1 hp Ev
                  (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y))
                  (XiCRaw S.G' (compWeight 3 1) ν (k + 1) 1 T.t) θ) θ T') ∧
              ∀ T' : Finset (CubeB (d := 3) (L := 3) (N₁ := N₁) (m₁ := T.m₁) (K := k + 1) 1
                  (k + 1) Set.univ),
                AnalyticOnNhd ℂ (fun θ => mObs y i θ T') (physVqRho S S.a₁ S.ν T.t ρ q) ∧
                (∀ θ ∈ physVqRho S S.a₁ S.ν T.t ρ q, ‖mObs y i θ T'‖ ≤
                  ((cK2' 3 3 2 (famConst 3 3 T.BG₂ T.κ) * T.t / lvCpsi T.κ T.t (β * 3 ^ k)) *
                      (CPE 3 3 ((K0 3 3 T.κ0 + 1) + (K0 3 3 T.κ0 + 1) + K0 3 3 T.κ0 +
                          K0 3 3 T.κ0) (2 * T.κdec - 1) T.κ0 T.κ' * S.p₁ /
                        (obsRg CR s (p : ℝ) (β * 3 ^ k))) *
                      (((2 * 3 ^ (3 * (1 + T.m₁ + 1)) : ℕ) : ℝ) * c1 3 3) *
                      ((K0 3 3 T.κ0 + 1) + (K0 3 3 T.κ0 + 1) + K0 3 3 T.κ0 + K0 3 3 T.κ0) ^ 2 *
                      Real.exp ((min (2 * T.κdec) T.κ' - T.κ0) * cG 3 3) +
                    CPE 3 3 ((K0 3 3 T.κ0 + 1) + (K0 3 3 T.κ0 + 1) + K0 3 3 T.κ0 + K0 3 3 T.κ0)
                        (2 * T.κdec - 1) T.κ0 T.κ' *
                      (∑ r, 8 * (cK2' 3 3 2 (famConst 3 3 T.BG₂ T.κ) * T.t) *
                        (S.p₁ / lvCpsi T.κ T.t (β * 3 ^ k)) ^ 2 * Real.exp (-T.κ0 *
                        (obsLab (Lab.sum Lab) hdj).dl
                          (obsRemLab
                            (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y))
                            (fun Y => Sum.inl (Sum.inr Y))
                            (obsY0 1 (Lb ⊕ Lb)
                              (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y))
                              (rootCube (m₀ := 1) (blockIndex y))) r)))) *
                  Real.exp (-(min (min (2 * T.κdec) T.κ' - T.κ0 - 1) T.κ') * dExt T')) ∧
                (∀ θ ∈ physVqRho S S.a₁ S.ν T.t ρ q, mObs y i θ T' ≠ 0 →
                  rootCube (m₀ := 1) (blockIndex y) ∈ T' ∧ IsPolyDom 1 (k + 1) (sitesOf T')) ∧
                (∀ θ ∈ physVqRho S S.a₁ S.ν T.t ρ q, ∀ θ' ∈ physVqRho S S.a₁ S.ν T.t ρ q,
                  agreeOn (thickSet S.G' (sitesOf T'))
                    (θ.1 : RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2)
                    (θ'.1 : RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2) →
                  (∀ x ∈ sitesOf T', θ.2 x = θ'.2 x) → mObs y i θ T' = mObs y i θ' T') ∧
                (∀ θ ∈ physVqRho S S.a₁ S.ν T.t ρ q, ∀ θ' ∈ physVqRho S S.a₁ S.ν T.t ρ q,
                  physRestrict (N := 2) (sitesOf T') (physIncl 2 S θ) =
                    physRestrict (sitesOf T') (physIncl 2 S θ') →
                  mObs y i θ T' = mObs y i θ' T') ∧
                (∀ θ ∈ physVqRho S S.a₁ S.ν T.t ρ q, ‖mObs y i θ T'‖ ≤
                  C * obsPrefactor p s (β * 3 ^ k) * Real.exp (-(3 / 2 * T.κdec) * dExt T'))) ∧
        ∀ (D : BgData S.G' 2) (hDh : ∀ y i, D.h y i = (S.h₀ i : ℂ)),
          XiCData S.G' S.a S.ν (k + 1) 1 T.t D →
          ∀ g : Fld 3 3 N₁ T.m₁ (k + 1) 2, ∑ x', ∑ i', ‖g x' i'‖ < q →
            (∀ (y : CTorus 3 3 N₁ T.m₁ (k + 1)) (i : Fin 2),
              (S.withDatum D hDh).M0C (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) g y i =
                ((S.betaU ^ (1 / 2 : ℝ) : ℝ) : ℂ) *
                  ∑ T', mObs y i ((⟨rawOf D, rawOf_mem_rawSub _⟩ : rawSub 2 S.G'), g) T') ∧
            ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
                ∑ y : CTorus 3 3 N₁ T.m₁ (k + 1), ∑ i : Fin 2,
                  g y i * (S.withDatum D hDh).M0C (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁))
                    g y i =
              ∑ y : CTorus 3 3 N₁ T.m₁ (k + 1), ∑ i : Fin 2,
                g y i * ∑ T', mObs y i ((⟨rawOf D, rawOf_mem_rawSub _⟩ : rawSub 2 S.G'), g) T' := by
  obtain ⟨β₀, CE, CF, C, h3, hCE, hCF, hC0, h⟩ :=
    obsFamily_pair_fibre_prefactor_fromTowerG_rho T.toG hA p hCR hs0 hs ρ
  refine ⟨β₀, CE, CF, C, h3, hCE, hCF, hC0, ?_⟩
  intro k hk N₁ _ h3N hN ν hνpos hν β hβ p₁ hp0 hp₁ q hq0 hq1 Dsc
  have e : β * ((3 : ℕ) : ℝ) ^ (k * (3 - 2)) = β * 3 ^ k := by norm_num
  have G := h k hk N₁ (by simpa using h3N) hN ν hνpos (by simpa using hν) β hβ p₁ hp0
    (by rw [e]; exact hp₁) q hq0 hq1 (T.scaleDataG_of_fixed Dsc)
  unfold StepTowerG.step at G
  revert G
  generalize hb : β * ((3 : ℕ) : ℝ) ^ (k * (3 - 2)) = b
  generalize hϱ : rhoSepG 3 3 T.toG.m₁ = ϱ
  have hϱ' : ϱ = rhoSep T.m₁ := hϱ.symm.trans (rhoSepG_three _)
  have hb' : b = β * 3 ^ k := hb.symm.trans e
  subst hϱ' hb'
  intro G
  exact G

open Classical in
/-- **The observable coefficient family of all sites on the fibre, with the prefactor bound.**
Beyond the threshold of `obsFamily_full_fromTower`, at every scale datum and for `0 < q ≤ 1` there
are a label system, an amplitude `ε_H`, an activity `A` and a function `mObs y i θ T'` of the
observable site `(y, i)`, the parameter `θ = (raw datum, source)` and the finite set `T'` of
level-one blocks, chosen before the datum and the source, such that:
* for every site `(y, i)` there are an amplitude `obsRg` and a family `Ev` (analytic, local,
  bounded) with `mObs y i θ T' = obsCoeffParam … θ T'` for the tilted activity of `A` and this
  `Ev`; `θ ↦ mObs y i θ T'` is analytic on `physVq … q`, bounded there by
  `(B₁ + B₂) e^{-λ dExt T'}`, `λ = min (min (2 κ_dec) κ' - κ₀ - 1) κ'`, non-zero only if `T'`
  contains the root cube of `y` and its sites form a polymer, and local:
  `mObs y i θ T' = mObs y i θ' T'` for `θ, θ'` of `physVq … q` whose raw data agree on
  `thickSet (sitesOf T')` and whose sources agree on `sitesOf T'`; equality of their
  `physRestrict (sitesOf T')` images also implies equality of the coefficients;
* for every datum `D` of the chart `Ξ^c(𝔹_{k+1}; 1, T.t)` with constant field `h₀` and every source
  `g` with `∑ |g| < q`: `ℳ₀(y; g)_i = β_U^{1/2} ∑_{T'} mObs y i (rawOf D, g) T'` for every site, and
  `β_U^{-1/2} ∑_{y,i} g(y,i) ℳ₀(y; g)_i = ∑_{y,i} g(y,i) ∑_{T'} mObs y i (rawOf D, g) T'`,
  the objects `ℳ₀` being those of the step with the datum `D` and the class with zero old terms;
* with a constant `C ≥ 0` chosen with the thresholds (before the scale): for the same `mObs`,
  `‖mObs y i θ T'‖ ≤ C · obsPrefactor p s (β 3^k) · e^{-(3/2) κ_dec dExt T'}` on `physVq … q`. -/
theorem obsFamily_pair_fibre_prefactor_fromTower {κmin : ℝ} (T : StepTower κmin) {A₁ : ℝ} (hA : 0 < A₁)
    (p : ℕ) {CR s : ℝ} (hCR : 0 < CR) (hs0 : 0 < s) (hs : s < 1 / 2) :
    ∃ (β₀ CE CF C : ℝ), 3 ≤ β₀ ∧ 0 < CE ∧ 0 < CF ∧ 0 ≤ C ∧
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
          (K0 3 3 T.κ0 + 1))
        (mObs : CTorus 3 3 N₁ T.m₁ (k + 1) → Fin 2 → physParam 2 S →
          Finset (CubeB (d := 3) (L := 3) (N₁ := N₁) (m₁ := T.m₁) (K := k + 1) 1 (k + 1)
            Set.univ) → ℂ),
        2 * εH ≤ CE * (Real.log (β * 3 ^ k)) ^ (3 * p) / Real.sqrt (β * 3 ^ k) +
          q * CF * (Real.log (β * 3 ^ k)) ^ p / Real.sqrt (β * 3 ^ k) ∧
        (∀ (y : CTorus 3 3 N₁ T.m₁ (k + 1)) (i : Fin 2)
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
              (∀ θ T', mObs y i θ T' = obsCoeffParam (S.blockSplit 1 hp).μ
                (fun θ t σ => tiltActObs A (show 3 ^ 1 ∣ N₁ by simpa using h3N) T.κ0_ent hεH.le
                  hdj (le_refl _) (obsRg CR s (p : ℝ) (β * 3 ^ k)) hR (ball (0 : ℂ) (3 / 2))
                  θ t σ)
                (fun m => obsY1 1 S (Lb ⊕ Lb)
                  (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y)) m)
                (fun m => blockMarkC S 1 hp m.1 m.2)
                (fun θ m T'' => obsHker
                  (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y))
                  (fun Y => hatCoeff (Ev Y) (θ.1 : RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2)
                    (obsUnitVec S m)) 1 T'')
                (obsRemLab (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y))
                  (fun Y => Sum.inl (Sum.inr Y))
                  (obsY0 1 (Lb ⊕ Lb)
                    (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y))
                    (rootCube (m₀ := 1) (blockIndex y))))
                (fun θ => obsGrFam S 1 hp Ev
                  (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y))
                  (XiCRaw S.G' (compWeight 3 1) ν (k + 1) 1 T.t) θ) θ T') ∧
              ∀ T' : Finset (CubeB (d := 3) (L := 3) (N₁ := N₁) (m₁ := T.m₁) (K := k + 1) 1
                  (k + 1) Set.univ),
                AnalyticOnNhd ℂ (fun θ => mObs y i θ T') (physVq S S.a₁ S.ν T.t q) ∧
                (∀ θ ∈ physVq S S.a₁ S.ν T.t q, ‖mObs y i θ T'‖ ≤
                  ((cK2' 3 3 2 (famConst 3 3 T.BG₂ T.κ) * T.t / lvCpsi T.κ T.t (β * 3 ^ k)) *
                      (CPE 3 3 ((K0 3 3 T.κ0 + 1) + (K0 3 3 T.κ0 + 1) + K0 3 3 T.κ0 +
                          K0 3 3 T.κ0) (2 * T.κdec - 1) T.κ0 T.κ' * S.p₁ /
                        (obsRg CR s (p : ℝ) (β * 3 ^ k))) *
                      (((2 * 3 ^ (3 * (1 + T.m₁ + 1)) : ℕ) : ℝ) * c1 3 3) *
                      ((K0 3 3 T.κ0 + 1) + (K0 3 3 T.κ0 + 1) + K0 3 3 T.κ0 + K0 3 3 T.κ0) ^ 2 *
                      Real.exp ((min (2 * T.κdec) T.κ' - T.κ0) * cG 3 3) +
                    CPE 3 3 ((K0 3 3 T.κ0 + 1) + (K0 3 3 T.κ0 + 1) + K0 3 3 T.κ0 + K0 3 3 T.κ0)
                        (2 * T.κdec - 1) T.κ0 T.κ' *
                      (∑ r, 8 * (cK2' 3 3 2 (famConst 3 3 T.BG₂ T.κ) * T.t) *
                        (S.p₁ / lvCpsi T.κ T.t (β * 3 ^ k)) ^ 2 * Real.exp (-T.κ0 *
                        (obsLab (Lab.sum Lab) hdj).dl
                          (obsRemLab
                            (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y))
                            (fun Y => Sum.inl (Sum.inr Y))
                            (obsY0 1 (Lb ⊕ Lb)
                              (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y))
                              (rootCube (m₀ := 1) (blockIndex y))) r)))) *
                  Real.exp (-(min (min (2 * T.κdec) T.κ' - T.κ0 - 1) T.κ') * dExt T')) ∧
                (∀ θ ∈ physVq S S.a₁ S.ν T.t q, mObs y i θ T' ≠ 0 →
                  rootCube (m₀ := 1) (blockIndex y) ∈ T' ∧ IsPolyDom 1 (k + 1) (sitesOf T')) ∧
                (∀ θ ∈ physVq S S.a₁ S.ν T.t q, ∀ θ' ∈ physVq S S.a₁ S.ν T.t q,
                  agreeOn (thickSet S.G' (sitesOf T'))
                    (θ.1 : RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2)
                    (θ'.1 : RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2) →
                  (∀ x ∈ sitesOf T', θ.2 x = θ'.2 x) → mObs y i θ T' = mObs y i θ' T') ∧
                (∀ θ ∈ physVq S S.a₁ S.ν T.t q, ∀ θ' ∈ physVq S S.a₁ S.ν T.t q,
                  physRestrict (N := 2) (sitesOf T') (physIncl 2 S θ) =
                    physRestrict (sitesOf T') (physIncl 2 S θ') →
                  mObs y i θ T' = mObs y i θ' T') ∧
                (∀ θ ∈ physVq S S.a₁ S.ν T.t q, ‖mObs y i θ T'‖ ≤
                  C * obsPrefactor p s (β * 3 ^ k) * Real.exp (-(3 / 2 * T.κdec) * dExt T'))) ∧
        ∀ (D : BgData S.G' 2) (hDh : ∀ y i, D.h y i = (S.h₀ i : ℂ)),
          XiCData S.G' S.a S.ν (k + 1) 1 T.t D →
          ∀ g : Fld 3 3 N₁ T.m₁ (k + 1) 2, ∑ x', ∑ i', ‖g x' i'‖ < q →
            (∀ (y : CTorus 3 3 N₁ T.m₁ (k + 1)) (i : Fin 2),
              (S.withDatum D hDh).M0C (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) g y i =
                ((S.betaU ^ (1 / 2 : ℝ) : ℝ) : ℂ) *
                  ∑ T', mObs y i ((⟨rawOf D, rawOf_mem_rawSub _⟩ : rawSub 2 S.G'), g) T') ∧
            ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
                ∑ y : CTorus 3 3 N₁ T.m₁ (k + 1), ∑ i : Fin 2,
                  g y i * (S.withDatum D hDh).M0C (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁))
                    g y i =
              ∑ y : CTorus 3 3 N₁ T.m₁ (k + 1), ∑ i : Fin 2,
                g y i * ∑ T', mObs y i ((⟨rawOf D, rawOf_mem_rawSub _⟩ : rawSub 2 S.G'), g) T' := by
  exact obsFamily_pair_fibre_prefactor_fromTower_rho T hA p hCR hs0 hs 1

open Classical in
/-- At source radius `ρ` (`q ≤ ρ`, `max 1 ρ ≤ β`); the landed theorem is its `ρ = 1` corollary.  **The observable coefficient family of all sites, and the source pairing on the fibre.**
Beyond the threshold of `obsFamily_full_fromTower`, at every scale datum and for `0 < q ≤ 1` there
are a label system, an amplitude `ε_H`, an activity `A` and a function `mObs y i θ T'` of the
observable site `(y, i)`, the parameter `θ = (raw datum, source)` and the finite set `T'` of
level-one blocks, chosen before the datum and the source, such that:
* for every site `(y, i)` there are an amplitude `obsRg` and a family `Ev` (analytic, local,
  bounded) with `mObs y i θ T' = obsCoeffParam … θ T'` for the tilted activity of `A` and this
  `Ev`; `θ ↦ mObs y i θ T'` is analytic on `physVq … q`, bounded there by
  `(B₁ + B₂) e^{-λ dExt T'}`, `λ = min (min (2 κ_dec) κ' - κ₀ - 1) κ'`, non-zero only if `T'`
  contains the root cube of `y` and its sites form a polymer, and local:
  `mObs y i θ T' = mObs y i θ' T'` for `θ, θ'` of `physVq … q` whose raw data agree on
  `thickSet (sitesOf T')` and whose sources agree on `sitesOf T'`; equality of their
  `physRestrict (sitesOf T')` images also implies equality of the coefficients;
* for every datum `D` of the chart `Ξ^c(𝔹_{k+1}; 1, T.t)` with constant field `h₀` and every source
  `g` with `∑ |g| < q`: `ℳ₀(y; g)_i = β_U^{1/2} ∑_{T'} mObs y i (rawOf D, g) T'` for every site, and
  `β_U^{-1/2} ∑_{y,i} g(y,i) ℳ₀(y; g)_i = ∑_{y,i} g(y,i) ∑_{T'} mObs y i (rawOf D, g) T'`,
  the objects `ℳ₀` being those of the step with the datum `D` and the class with zero old terms. -/
theorem obsFamily_pair_fibre_fromTower_rho {κmin : ℝ} (T : StepTower κmin) {A₁ : ℝ} (hA : 0 < A₁)
    (p : ℕ) {CR s : ℝ} (hCR : 0 < CR) (hs0 : 0 < s) (hs : s < 1 / 2) (ρ : ℝ) :
    ∃ (β₀ CE CF : ℝ), 3 ≤ β₀ ∧ 0 < CE ∧ 0 < CF ∧
      ∀ (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁] (h3N : 3 ∣ N₁), 5 < N₁ →
      ∀ ν : ℝ, 0 < ν → ν * 3 ^ (2 * (k + 1)) ≤ 1 → ∀ β : ℝ, β₀ ≤ β →
      ∀ p₁ : ℝ, 0 < p₁ → p₁ ≤ pLog A₁ p (β * 3 ^ k) → ∀ q : ℝ, 0 < q → q ≤ ρ →
      ∀ (Dsc : StepScaleData T k hk N₁ ν β p₁)
        (S : StepSetting 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)),
        S = T.step k hk N₁ ν β p₁ → ∀ hp : 0 < S.p₁,
      ∃ (Lb : Type) (_ : Fintype Lb)
        (Lab : CubeLabels (d := 3) (L := 3) (N₁ := N₁) (m₁ := T.m₁) (K := k + 1) 1 (k + 1)
          Set.univ Lb) (εH : ℝ) (hεH : 0 < εH)
        (A : physParam 2 S → ℂ → LabelAct Lab (S.blockSplit 1 hp).Ωb εH (2 * T.κdec - 1) T.κ0
          (K0 3 3 T.κ0 + 1))
        (mObs : CTorus 3 3 N₁ T.m₁ (k + 1) → Fin 2 → physParam 2 S →
          Finset (CubeB (d := 3) (L := 3) (N₁ := N₁) (m₁ := T.m₁) (K := k + 1) 1 (k + 1)
            Set.univ) → ℂ),
        2 * εH ≤ CE * (Real.log (β * 3 ^ k)) ^ (3 * p) / Real.sqrt (β * 3 ^ k) +
          q * CF * (Real.log (β * 3 ^ k)) ^ p / Real.sqrt (β * 3 ^ k) ∧
        (∀ (y : CTorus 3 3 N₁ T.m₁ (k + 1)) (i : Fin 2)
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
              (∀ θ T', mObs y i θ T' = obsCoeffParam (S.blockSplit 1 hp).μ
                (fun θ t σ => tiltActObs A (show 3 ^ 1 ∣ N₁ by simpa using h3N) T.κ0_ent hεH.le
                  hdj (le_refl _) (obsRg CR s (p : ℝ) (β * 3 ^ k)) hR (ball (0 : ℂ) (3 / 2))
                  θ t σ)
                (fun m => obsY1 1 S (Lb ⊕ Lb)
                  (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y)) m)
                (fun m => blockMarkC S 1 hp m.1 m.2)
                (fun θ m T'' => obsHker
                  (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y))
                  (fun Y => hatCoeff (Ev Y) (θ.1 : RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2)
                    (obsUnitVec S m)) 1 T'')
                (obsRemLab (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y))
                  (fun Y => Sum.inl (Sum.inr Y))
                  (obsY0 1 (Lb ⊕ Lb)
                    (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y))
                    (rootCube (m₀ := 1) (blockIndex y))))
                (fun θ => obsGrFam S 1 hp Ev
                  (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y))
                  (XiCRaw S.G' (compWeight 3 1) ν (k + 1) 1 T.t) θ) θ T') ∧
              ∀ T' : Finset (CubeB (d := 3) (L := 3) (N₁ := N₁) (m₁ := T.m₁) (K := k + 1) 1
                  (k + 1) Set.univ),
                AnalyticOnNhd ℂ (fun θ => mObs y i θ T') (physVqRho S S.a₁ S.ν T.t ρ q) ∧
                (∀ θ ∈ physVqRho S S.a₁ S.ν T.t ρ q, ‖mObs y i θ T'‖ ≤
                  ((cK2' 3 3 2 (famConst 3 3 T.BG₂ T.κ) * T.t / lvCpsi T.κ T.t (β * 3 ^ k)) *
                      (CPE 3 3 ((K0 3 3 T.κ0 + 1) + (K0 3 3 T.κ0 + 1) + K0 3 3 T.κ0 +
                          K0 3 3 T.κ0) (2 * T.κdec - 1) T.κ0 T.κ' * S.p₁ /
                        (obsRg CR s (p : ℝ) (β * 3 ^ k))) *
                      (((2 * 3 ^ (3 * (1 + T.m₁ + 1)) : ℕ) : ℝ) * c1 3 3) *
                      ((K0 3 3 T.κ0 + 1) + (K0 3 3 T.κ0 + 1) + K0 3 3 T.κ0 + K0 3 3 T.κ0) ^ 2 *
                      Real.exp ((min (2 * T.κdec) T.κ' - T.κ0) * cG 3 3) +
                    CPE 3 3 ((K0 3 3 T.κ0 + 1) + (K0 3 3 T.κ0 + 1) + K0 3 3 T.κ0 + K0 3 3 T.κ0)
                        (2 * T.κdec - 1) T.κ0 T.κ' *
                      (∑ r, 8 * (cK2' 3 3 2 (famConst 3 3 T.BG₂ T.κ) * T.t) *
                        (S.p₁ / lvCpsi T.κ T.t (β * 3 ^ k)) ^ 2 * Real.exp (-T.κ0 *
                        (obsLab (Lab.sum Lab) hdj).dl
                          (obsRemLab
                            (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y))
                            (fun Y => Sum.inl (Sum.inr Y))
                            (obsY0 1 (Lb ⊕ Lb)
                              (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y))
                              (rootCube (m₀ := 1) (blockIndex y))) r)))) *
                  Real.exp (-(min (min (2 * T.κdec) T.κ' - T.κ0 - 1) T.κ') * dExt T')) ∧
                (∀ θ ∈ physVqRho S S.a₁ S.ν T.t ρ q, mObs y i θ T' ≠ 0 →
                  rootCube (m₀ := 1) (blockIndex y) ∈ T' ∧ IsPolyDom 1 (k + 1) (sitesOf T')) ∧
                (∀ θ ∈ physVqRho S S.a₁ S.ν T.t ρ q, ∀ θ' ∈ physVqRho S S.a₁ S.ν T.t ρ q,
                  agreeOn (thickSet S.G' (sitesOf T'))
                    (θ.1 : RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2)
                    (θ'.1 : RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2) →
                  (∀ x ∈ sitesOf T', θ.2 x = θ'.2 x) → mObs y i θ T' = mObs y i θ' T') ∧
                (∀ θ ∈ physVqRho S S.a₁ S.ν T.t ρ q, ∀ θ' ∈ physVqRho S S.a₁ S.ν T.t ρ q,
                  physRestrict (N := 2) (sitesOf T') (physIncl 2 S θ) =
                    physRestrict (sitesOf T') (physIncl 2 S θ') →
                  mObs y i θ T' = mObs y i θ' T')) ∧
        ∀ (D : BgData S.G' 2) (hDh : ∀ y i, D.h y i = (S.h₀ i : ℂ)),
          XiCData S.G' S.a S.ν (k + 1) 1 T.t D →
          ∀ g : Fld 3 3 N₁ T.m₁ (k + 1) 2, ∑ x', ∑ i', ‖g x' i'‖ < q →
            (∀ (y : CTorus 3 3 N₁ T.m₁ (k + 1)) (i : Fin 2),
              (S.withDatum D hDh).M0C (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) g y i =
                ((S.betaU ^ (1 / 2 : ℝ) : ℝ) : ℂ) *
                  ∑ T', mObs y i ((⟨rawOf D, rawOf_mem_rawSub _⟩ : rawSub 2 S.G'), g) T') ∧
            ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
                ∑ y : CTorus 3 3 N₁ T.m₁ (k + 1), ∑ i : Fin 2,
                  g y i * (S.withDatum D hDh).M0C (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁))
                    g y i =
              ∑ y : CTorus 3 3 N₁ T.m₁ (k + 1), ∑ i : Fin 2,
                g y i * ∑ T', mObs y i ((⟨rawOf D, rawOf_mem_rawSub _⟩ : rawSub 2 S.G'), g) T' := by
  obtain ⟨β₀, CE, CF, h3, hCE, hCF, h⟩ :=
    obsFamily_pair_fibre_fromTowerG_rho T.toG hA p hCR hs0 hs ρ
  refine ⟨β₀, CE, CF, h3, hCE, hCF, ?_⟩
  intro k hk N₁ _ h3N hN ν hνpos hν β hβ p₁ hp0 hp₁ q hq0 hq1 Dsc
  have e : β * ((3 : ℕ) : ℝ) ^ (k * (3 - 2)) = β * 3 ^ k := by norm_num
  have G := h k hk N₁ (by simpa using h3N) hN ν hνpos (by simpa using hν) β hβ p₁ hp0
    (by rw [e]; exact hp₁) q hq0 hq1 (T.scaleDataG_of_fixed Dsc)
  unfold StepTowerG.step at G
  revert G
  generalize hb : β * ((3 : ℕ) : ℝ) ^ (k * (3 - 2)) = b
  generalize hϱ : rhoSepG 3 3 T.toG.m₁ = ϱ
  have hϱ' : ϱ = rhoSep T.m₁ := hϱ.symm.trans (rhoSepG_three _)
  have hb' : b = β * 3 ^ k := hb.symm.trans e
  subst hϱ' hb'
  intro G
  exact G

open Classical in
/-- **The observable coefficient family of all sites, and the source pairing on the fibre.**
Beyond the threshold of `obsFamily_full_fromTower`, at every scale datum and for `0 < q ≤ 1` there
are a label system, an amplitude `ε_H`, an activity `A` and a function `mObs y i θ T'` of the
observable site `(y, i)`, the parameter `θ = (raw datum, source)` and the finite set `T'` of
level-one blocks, chosen before the datum and the source, such that:
* for every site `(y, i)` there are an amplitude `obsRg` and a family `Ev` (analytic, local,
  bounded) with `mObs y i θ T' = obsCoeffParam … θ T'` for the tilted activity of `A` and this
  `Ev`; `θ ↦ mObs y i θ T'` is analytic on `physVq … q`, bounded there by
  `(B₁ + B₂) e^{-λ dExt T'}`, `λ = min (min (2 κ_dec) κ' - κ₀ - 1) κ'`, non-zero only if `T'`
  contains the root cube of `y` and its sites form a polymer, and local:
  `mObs y i θ T' = mObs y i θ' T'` for `θ, θ'` of `physVq … q` whose raw data agree on
  `thickSet (sitesOf T')` and whose sources agree on `sitesOf T'`; equality of their
  `physRestrict (sitesOf T')` images also implies equality of the coefficients;
* for every datum `D` of the chart `Ξ^c(𝔹_{k+1}; 1, T.t)` with constant field `h₀` and every source
  `g` with `∑ |g| < q`: `ℳ₀(y; g)_i = β_U^{1/2} ∑_{T'} mObs y i (rawOf D, g) T'` for every site, and
  `β_U^{-1/2} ∑_{y,i} g(y,i) ℳ₀(y; g)_i = ∑_{y,i} g(y,i) ∑_{T'} mObs y i (rawOf D, g) T'`,
  the objects `ℳ₀` being those of the step with the datum `D` and the class with zero old terms. -/
theorem obsFamily_pair_fibre_fromTower {κmin : ℝ} (T : StepTower κmin) {A₁ : ℝ} (hA : 0 < A₁)
    (p : ℕ) {CR s : ℝ} (hCR : 0 < CR) (hs0 : 0 < s) (hs : s < 1 / 2) :
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
          (K0 3 3 T.κ0 + 1))
        (mObs : CTorus 3 3 N₁ T.m₁ (k + 1) → Fin 2 → physParam 2 S →
          Finset (CubeB (d := 3) (L := 3) (N₁ := N₁) (m₁ := T.m₁) (K := k + 1) 1 (k + 1)
            Set.univ) → ℂ),
        2 * εH ≤ CE * (Real.log (β * 3 ^ k)) ^ (3 * p) / Real.sqrt (β * 3 ^ k) +
          q * CF * (Real.log (β * 3 ^ k)) ^ p / Real.sqrt (β * 3 ^ k) ∧
        (∀ (y : CTorus 3 3 N₁ T.m₁ (k + 1)) (i : Fin 2)
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
              (∀ θ T', mObs y i θ T' = obsCoeffParam (S.blockSplit 1 hp).μ
                (fun θ t σ => tiltActObs A (show 3 ^ 1 ∣ N₁ by simpa using h3N) T.κ0_ent hεH.le
                  hdj (le_refl _) (obsRg CR s (p : ℝ) (β * 3 ^ k)) hR (ball (0 : ℂ) (3 / 2))
                  θ t σ)
                (fun m => obsY1 1 S (Lb ⊕ Lb)
                  (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y)) m)
                (fun m => blockMarkC S 1 hp m.1 m.2)
                (fun θ m T'' => obsHker
                  (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y))
                  (fun Y => hatCoeff (Ev Y) (θ.1 : RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2)
                    (obsUnitVec S m)) 1 T'')
                (obsRemLab (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y))
                  (fun Y => Sum.inl (Sum.inr Y))
                  (obsY0 1 (Lb ⊕ Lb)
                    (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y))
                    (rootCube (m₀ := 1) (blockIndex y))))
                (fun θ => obsGrFam S 1 hp Ev
                  (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y))
                  (XiCRaw S.G' (compWeight 3 1) ν (k + 1) 1 T.t) θ) θ T') ∧
              ∀ T' : Finset (CubeB (d := 3) (L := 3) (N₁ := N₁) (m₁ := T.m₁) (K := k + 1) 1
                  (k + 1) Set.univ),
                AnalyticOnNhd ℂ (fun θ => mObs y i θ T') (physVq S S.a₁ S.ν T.t q) ∧
                (∀ θ ∈ physVq S S.a₁ S.ν T.t q, ‖mObs y i θ T'‖ ≤
                  ((cK2' 3 3 2 (famConst 3 3 T.BG₂ T.κ) * T.t / lvCpsi T.κ T.t (β * 3 ^ k)) *
                      (CPE 3 3 ((K0 3 3 T.κ0 + 1) + (K0 3 3 T.κ0 + 1) + K0 3 3 T.κ0 +
                          K0 3 3 T.κ0) (2 * T.κdec - 1) T.κ0 T.κ' * S.p₁ /
                        (obsRg CR s (p : ℝ) (β * 3 ^ k))) *
                      (((2 * 3 ^ (3 * (1 + T.m₁ + 1)) : ℕ) : ℝ) * c1 3 3) *
                      ((K0 3 3 T.κ0 + 1) + (K0 3 3 T.κ0 + 1) + K0 3 3 T.κ0 + K0 3 3 T.κ0) ^ 2 *
                      Real.exp ((min (2 * T.κdec) T.κ' - T.κ0) * cG 3 3) +
                    CPE 3 3 ((K0 3 3 T.κ0 + 1) + (K0 3 3 T.κ0 + 1) + K0 3 3 T.κ0 + K0 3 3 T.κ0)
                        (2 * T.κdec - 1) T.κ0 T.κ' *
                      (∑ r, 8 * (cK2' 3 3 2 (famConst 3 3 T.BG₂ T.κ) * T.t) *
                        (S.p₁ / lvCpsi T.κ T.t (β * 3 ^ k)) ^ 2 * Real.exp (-T.κ0 *
                        (obsLab (Lab.sum Lab) hdj).dl
                          (obsRemLab
                            (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y))
                            (fun Y => Sum.inl (Sum.inr Y))
                            (obsY0 1 (Lb ⊕ Lb)
                              (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y))
                              (rootCube (m₀ := 1) (blockIndex y))) r)))) *
                  Real.exp (-(min (min (2 * T.κdec) T.κ' - T.κ0 - 1) T.κ') * dExt T')) ∧
                (∀ θ ∈ physVq S S.a₁ S.ν T.t q, mObs y i θ T' ≠ 0 →
                  rootCube (m₀ := 1) (blockIndex y) ∈ T' ∧ IsPolyDom 1 (k + 1) (sitesOf T')) ∧
                (∀ θ ∈ physVq S S.a₁ S.ν T.t q, ∀ θ' ∈ physVq S S.a₁ S.ν T.t q,
                  agreeOn (thickSet S.G' (sitesOf T'))
                    (θ.1 : RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2)
                    (θ'.1 : RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2) →
                  (∀ x ∈ sitesOf T', θ.2 x = θ'.2 x) → mObs y i θ T' = mObs y i θ' T') ∧
                (∀ θ ∈ physVq S S.a₁ S.ν T.t q, ∀ θ' ∈ physVq S S.a₁ S.ν T.t q,
                  physRestrict (N := 2) (sitesOf T') (physIncl 2 S θ) =
                    physRestrict (sitesOf T') (physIncl 2 S θ') →
                  mObs y i θ T' = mObs y i θ' T')) ∧
        ∀ (D : BgData S.G' 2) (hDh : ∀ y i, D.h y i = (S.h₀ i : ℂ)),
          XiCData S.G' S.a S.ν (k + 1) 1 T.t D →
          ∀ g : Fld 3 3 N₁ T.m₁ (k + 1) 2, ∑ x', ∑ i', ‖g x' i'‖ < q →
            (∀ (y : CTorus 3 3 N₁ T.m₁ (k + 1)) (i : Fin 2),
              (S.withDatum D hDh).M0C (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) g y i =
                ((S.betaU ^ (1 / 2 : ℝ) : ℝ) : ℂ) *
                  ∑ T', mObs y i ((⟨rawOf D, rawOf_mem_rawSub _⟩ : rawSub 2 S.G'), g) T') ∧
            ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
                ∑ y : CTorus 3 3 N₁ T.m₁ (k + 1), ∑ i : Fin 2,
                  g y i * (S.withDatum D hDh).M0C (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁))
                    g y i =
              ∑ y : CTorus 3 3 N₁ T.m₁ (k + 1), ∑ i : Fin 2,
                g y i * ∑ T', mObs y i ((⟨rawOf D, rawOf_mem_rawSub _⟩ : rawSub 2 S.G'), g) T' := by
  exact obsFamily_pair_fibre_fromTower_rho T hA p hCR hs0 hs 1

end Balaban.Inhabited
