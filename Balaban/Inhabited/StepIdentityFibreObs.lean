/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.ObsFamilyJoint
public import Balaban.Inhabited.StepIdentityFibre
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The observable half of the step identity on the fibre `h ≡ h₀`

`obsFamily_full_fromTower` gives, at a scale of the shared tower, one label system and one
activity, and for every observable site `(y, i)` one amplitude and one family `Ev`, whose
coefficients `obsCoeffParam … θ T'` are analytic, bounded, supported on rooted polymer sets and
local (equal at two parameters whose raw data agree on the thickening of `sitesOf T'` and whose
sources agree on `sitesOf T'`), and whose sum at `θ = (rawOf D, g)` is `β_U^{-1/2} ℳ₀(y; g)_i` of
the step with the datum `D`.

`obsFamily_pair_fibre_fromTower` collects the coefficients of all sites in one function
`mObs y i θ T'` (equal to `obsCoeffParam …` for the amplitude and the `Ev` of the site), chosen
before the datum and the source, and adds the pairing with the source: for every datum `D` of the
chart with constant field `h₀` and every source `g` with `∑ |g| < q`,
`β_U^{-1/2} ∑_{y,i} g(y,i) ℳ₀(y; g)_i = ∑_{y,i} g(y,i) ∑_{T'} mObs y i (rawOf D, g) T'`.
The factors `β_U^{-1/2}` and `β_U^{1/2}` cancel since `β_U = β 3^k > 0`.
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation
  Balaban.Localization Balaban.Localization.LevelPair Balaban.Localization.I5Inhabited
  Balaban.Polymer Balaban.SmallField.Def6 Balaban.Inhabited.LevelStep MeasureTheory Metric

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
  `thickSet (sitesOf T')` and whose sources agree on `sitesOf T'`;
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
  classical
  obtain ⟨β₀, CE, CF, h3, hCE, hCF, H⟩ := obsFamily_full_fromTower T hA p hCR hs0 hs
  refine ⟨β₀, CE, CF, h3, hCE, hCF, ?_⟩
  intro k hk N₁ _ h3N hN ν hνpos hν β hβ p₁ hp0 hp₁ q hq0 hq1 Dsc S hS hp
  obtain ⟨Lb, hLb, Lab, εH, hεH, A, hamp, hsite⟩ :=
    H k hk N₁ h3N hN ν hνpos hν β hβ p₁ hp0 hp₁ q hq0 hq1 Dsc S hS hp
  -- the site domains are polymer domains (from the covers of the scale datum)
  have hdj₀ : ∀ (y : CTorus 3 3 N₁ T.m₁ (k + 1)) (_ : Fin 2),
      ∀ Y ∈ obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y), IsDj 1 (k + 1) Y := by
    subst hS
    exact fun y i => obsDomains_isDj (X₁f := LocalCover.nbhdF 1 y) _ le_rfl
      (Dsc.covers.2 (y, i)).1 (Dsc.covers.2 (y, i)).2.2.1
  have hbU0 : 0 < S.betaU := by
    rw [hS, show (T.step k hk N₁ ν β p₁).betaU = β * 3 ^ k from
      hatStepK_betaU k T.m₁ hk ν β p₁ T.δ]
    have : 0 < β := by linarith
    positivity
  choose hR hR1 hRθ Ev ha hd hb hDD hfam hcl hval using fun y i => hsite y i (hdj₀ y i)
  refine ⟨Lb, hLb, Lab, εH, hεH, A, fun y i θ T' => obsCoeffParam (S.blockSplit 1 hp).μ
    (fun θ t σ => tiltActObs A (show 3 ^ 1 ∣ N₁ by simpa using h3N) T.κ0_ent hεH.le
      (hdj₀ y i) (le_refl _) (obsRg CR s (p : ℝ) (β * 3 ^ k)) (hR y i) (ball (0 : ℂ) (3 / 2))
      θ t σ)
    (fun m => obsY1 1 S (Lb ⊕ Lb)
      (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y)) m)
    (fun m => blockMarkC S 1 hp m.1 m.2)
    (fun θ m T'' => obsHker
      (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y))
      (fun Y => hatCoeff (Ev y i Y) (θ.1 : RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2)
        (obsUnitVec S m)) 1 T'')
    (obsRemLab (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y))
      (fun Y => Sum.inl (Sum.inr Y))
      (obsY0 1 (Lb ⊕ Lb)
        (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y))
        (rootCube (m₀ := 1) (blockIndex y))))
    (fun θ => obsGrFam S 1 hp (Ev y i)
      (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y))
      (XiCRaw S.G' (compWeight 3 1) ν (k + 1) 1 T.t) θ) θ T', hamp, ?_, ?_⟩
  · intro y i hdj
    exact ⟨hR y i, hR1 y i, hRθ y i, Ev y i, ha y i, hd y i, hb y i, fun _ _ => rfl,
      fun T' => ⟨(hcl y i T').2.2.2.1, (hcl y i T').2.2.2.2.1, (hcl y i T').2.2.2.2.2.1,
        (hcl y i T').2.2.2.2.2.2.1, (hcl y i T').2.2.2.2.2.2.2⟩⟩
  · intro D hDh hX g hg
    have hM := fun y i => hval y i D hDh hX g hg
    exact ⟨hM, rpow_neg_half_mul_sum_pair hbU0 g _ _ hM⟩

end Balaban.Inhabited
