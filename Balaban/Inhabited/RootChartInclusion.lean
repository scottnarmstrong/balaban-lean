/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.RootTermZeroClass

/-!
# Chart inclusion at source radius one for the observable families of Root-F

The source ball of Root-F at a fixed datum `D` of the fibre `h ≡ h₀` is
`{g | ∑ ‖g‖ < ρ}` (`ρ = 1` in Root-F).  *Chart inclusion* is the statement that for every datum `D`
of the chart `Ξ^c(𝔹_{k+1}; 1, t)` and every source `g` of this ball, the point `(rawOf D, g)` of
the parameter space lies in `physVqRho S S.a₁ S.ν t ρ ρ`, the domain on which the observable
families of `obsFamily_pair_fibre_prefactor_fromTowerG_rho` are analytic and satisfy their
support, locality and decay clauses (`ρ = 1`: `physVq … 1 = physV`).

* `rawOf_source_mem_physVqRho`: the inclusion, for every datum and every source of the ball.
* `analyticOn_sourceBall_of_chart`: a function analytic on `physVqRho … ρ ρ` is analytic in the
  source on the ball, at every datum of the chart.
* `obsCubeFamily_sourceBall_fromTowerG_rho`: the single family `mObs` (one function of all
  `(y, i, θ, T')`, chosen before the datum `D`) satisfies, for every `(y, i)` simultaneously and
  every datum `D` of the fibre, the support, source-locality, analyticity, bound and value clauses
  on the source ball that `rootTermFamily_of_cubeFamily_rho` consumes.
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation
  Balaban.Localization Balaban.Localization.LevelPair Balaban.Localization.I5Inhabited
  Balaban.Polymer Balaban.SmallField.Def6 Balaban.Inhabited.LevelStep MeasureTheory Metric

/-- **Chart inclusion.**  For a datum `D` of the chart and a source `g` with `∑ ‖g‖ < ρ`, the point
`(rawOf D, g)` lies in `physVqRho S S.a₁ S.ν t ρ ρ`. -/
theorem rawOf_source_mem_physVqRho {d L N N₁ m₁ k : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
    (S : StepSetting d L N₁ m₁ k N ϱ) (ρ t : ℝ) (D : BgData S.G' N)
    (hX : XiCData S.G' S.a S.ν (k + 1) 1 t D)
    (g : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) (hg : ∑ y, ∑ i, ‖g y i‖ < ρ) :
    ((⟨rawOf D, rawOf_mem_rawSub D⟩ : rawSub N S.G'), g) ∈ physVqRho S S.a₁ S.ν t ρ ρ := by
  rw [physVqRho_self]
  exact ⟨⟨D, hX, rfl⟩, hg⟩

/-- A function analytic on `physVqRho … ρ ρ` is analytic in the source on the ball
`∑ ‖g‖ < ρ` at every datum of the chart. -/
theorem analyticOn_sourceBall_of_chart {d L N N₁ m₁ k : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
    (S : StepSetting d L N₁ m₁ k N ϱ) (ρ t : ℝ) (D : BgData S.G' N)
    (hX : XiCData S.G' S.a S.ν (k + 1) 1 t D) (F : physParam N S → ℂ)
    (hF : AnalyticOnNhd ℂ F (physVqRho S S.a₁ S.ν t ρ ρ)) :
    AnalyticOnNhd ℂ
      (fun g => F ((⟨rawOf D, rawOf_mem_rawSub D⟩ : rawSub N S.G'), g))
      {g : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ | ∑ y, ∑ i, ‖g y i‖ < ρ} :=
  hF.comp (analyticOnNhd_const.prod analyticOnNhd_id)
    (fun g hg => rawOf_source_mem_physVqRho S ρ t D hX g hg)

open Classical in
/-- **The observable families on the source ball, for all sites at once.**  For the general tower
`T` and `ρ > 0` there are thresholds and a bound constant `C ≥ 0`, and at every scale a single family
`mObs y i θ T'` (indexed by all sites `(y, i)`, chosen before the datum) such that for every datum
`D` of the fibre `h ≡ h₀` in the chart, every site `(y, i)` and every finite set `T'` of cubes, the
function `g ↦ mObs y i (rawOf D, g) T'` of the source: is analytic on `{∑ ‖g‖ < ρ}`; vanishes
unless `T'` contains the root cube of `y` and `sitesOf T'` is a polymer domain; takes equal values
at sources of the ball that agree on `sitesOf T'`; is bounded by
`C · obsPrefactor · e^{-(3/2) κ_dec dExt T'}` on `{∑ ‖g‖ ≤ ρ / 2}`; and gives the observable
`ℳ₀(y; g)_i = √β_U ∑_{T'} mObs y i (rawOf D, g) T'` at every source of the ball. -/
theorem obsCubeFamily_sourceBall_fromTowerG_rho {d L N : ℕ} [NeZero L] {κmin : ℝ}
    (T : StepTowerG d L N κmin) {A₁ : ℝ} (hA : 0 < A₁) (p : ℕ)
    {CR s : ℝ} (hCR : 0 < CR) (hs0 : 0 < s) (hs : s < 1 / 2) (ρ : ℝ) (hρ : 0 < ρ) :
    ∃ (β₀ CE CF C : ℝ), 3 ≤ β₀ ∧ 0 < CE ∧ 0 < CF ∧ 0 ≤ C ∧
      ∀ (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁] (_h3N : L ^ T.m₀ ∣ N₁), 5 < N₁ →
      ∀ ν : ℝ, 0 < ν → ν * (L : ℝ) ^ (2 * (k + 1)) ≤ 1 → ∀ β : ℝ, β₀ ≤ β →
      ∀ p₁ : ℝ, 0 < p₁ → p₁ ≤ pLog A₁ p (β * (L : ℝ) ^ (k * (d - 2))) →
      ∀ (_ : StepScaleDataG T k hk N₁ ν β p₁)
        (S : StepSetting d L N₁ T.m₁ k N (rhoSepG d L T.m₁)),
        S = T.step k hk N₁ ν β p₁ → ∀ _hp : 0 < S.p₁,
      ∃ (mObs : CTorus d L N₁ T.m₁ (k + 1) → Fin N → physParam N S →
          Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := T.m₁) (K := k + 1) T.m₀ (k + 1)
            Set.univ) → ℂ),
        ∀ (D : BgData S.G' N) (hDh : ∀ y i, D.h y i = (S.h₀ i : ℂ)),
          XiCData S.G' S.a S.ν (k + 1) 1 T.t D →
          ∀ (y : CTorus d L N₁ T.m₁ (k + 1)) (i : Fin N)
            (T' : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := T.m₁) (K := k + 1) T.m₀
              (k + 1) Set.univ)),
            AnalyticOnNhd ℂ
              (fun g => mObs y i ((⟨rawOf D, rawOf_mem_rawSub D⟩ : rawSub N S.G'), g) T')
              {g : CTorus d L N₁ T.m₁ (k + 1) → Fin N → ℂ | ∑ y, ∑ i, ‖g y i‖ < ρ} ∧
            (∀ g : CTorus d L N₁ T.m₁ (k + 1) → Fin N → ℂ, ∑ y, ∑ i, ‖g y i‖ < ρ →
              mObs y i ((⟨rawOf D, rawOf_mem_rawSub D⟩ : rawSub N S.G'), g) T' ≠ 0 →
                rootCube (m₀ := T.m₀) (blockIndex y) ∈ T' ∧
                  IsPolyDom T.m₀ (k + 1) (sitesOf T')) ∧
            (∀ g g' : CTorus d L N₁ T.m₁ (k + 1) → Fin N → ℂ, ∑ y, ∑ i, ‖g y i‖ < ρ →
              ∑ y, ∑ i, ‖g' y i‖ < ρ → (∀ x ∈ sitesOf T', g x = g' x) →
              mObs y i ((⟨rawOf D, rawOf_mem_rawSub D⟩ : rawSub N S.G'), g) T' =
                mObs y i ((⟨rawOf D, rawOf_mem_rawSub D⟩ : rawSub N S.G'), g') T') ∧
            (∀ g : CTorus d L N₁ T.m₁ (k + 1) → Fin N → ℂ, ∑ y, ∑ i, ‖g y i‖ ≤ ρ / 2 →
              ‖mObs y i ((⟨rawOf D, rawOf_mem_rawSub D⟩ : rawSub N S.G'), g) T'‖ ≤
                C * obsPrefactor p s (β * (L : ℝ) ^ (k * (d - 2))) *
                  Real.exp (-(3 / 2 * T.κdec) * dExt T')) ∧
            (∀ g : CTorus d L N₁ T.m₁ (k + 1) → Fin N → ℂ, ∑ y, ∑ i, ‖g y i‖ < ρ →
              (S.withDatum D hDh).M0C (zeroClass d L N₁ T.m₁ k N (rhoSepG d L T.m₁)) g y i =
                ((S.betaU ^ (1 / 2 : ℝ) : ℝ) : ℂ) *
                  ∑ T'', mObs y i ((⟨rawOf D, rawOf_mem_rawSub D⟩ : rawSub N S.G'), g) T'') := by
  classical
  obtain ⟨β₀, CE, CF, C, h3, hCE, hCF, hC0, H⟩ :=
    obsFamily_pair_fibre_prefactor_fromTowerG_rho T hA p hCR hs0 hs ρ
  refine ⟨β₀, CE, CF, C, h3, hCE, hCF, hC0, ?_⟩
  intro k hk N₁ _ h3N hN ν hνpos hν β hβ p₁ hp0 hp₁ Dsc S hS hp
  obtain ⟨Lb, hLb, Lab, εH, hεH, A, mObs, -, hsite, hval⟩ :=
    H k hk N₁ h3N hN ν hνpos hν β hβ p₁ hp0 hp₁ ρ hρ le_rfl Dsc S hS hp
  have hcl : ∀ y i, ∀ T' : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := T.m₁)
      (K := k + 1) T.m₀ (k + 1) Set.univ),
      AnalyticOnNhd ℂ (fun θ => mObs y i θ T') (physVqRho S S.a₁ S.ν T.t ρ ρ) ∧
      (∀ θ ∈ physVqRho S S.a₁ S.ν T.t ρ ρ, mObs y i θ T' ≠ 0 →
        rootCube (m₀ := T.m₀) (blockIndex y) ∈ T' ∧ IsPolyDom T.m₀ (k + 1) (sitesOf T')) ∧
      (∀ θ ∈ physVqRho S S.a₁ S.ν T.t ρ ρ, ∀ θ' ∈ physVqRho S S.a₁ S.ν T.t ρ ρ,
        agreeOn (thickSet S.G' (sitesOf T'))
          (θ.1 : RawData d L (N₁ * L ^ T.m₁) (k + 1) N)
          (θ'.1 : RawData d L (N₁ * L ^ T.m₁) (k + 1) N) →
        (∀ x ∈ sitesOf T', θ.2 x = θ'.2 x) → mObs y i θ T' = mObs y i θ' T') ∧
      (∀ θ ∈ physVqRho S S.a₁ S.ν T.t ρ ρ, ‖mObs y i θ T'‖ ≤
        C * obsPrefactor p s (β * (L : ℝ) ^ (k * (d - 2))) *
          Real.exp (-(3 / 2 * T.κdec) * dExt T')) := by
    intro y i T'
    obtain ⟨-, -, -, -, -, -, -, -, hfam⟩ := hsite y i (by
      subst hS
      exact obsDomains_isDj (X₁f := LocalCover.nbhdF T.m₀ y) _ T.hd
        (Dsc.covers.2 (y, i)).1 (Dsc.covers.2 (y, i)).2.2.1)
    exact ⟨(hfam T').1, (hfam T').2.2.1, (hfam T').2.2.2.1, (hfam T').2.2.2.2.2⟩
  refine ⟨mObs, fun D hDh hX y i T' => ⟨?_, ?_, ?_, ?_, ?_⟩⟩
  · exact analyticOn_sourceBall_of_chart S ρ T.t D hX _ (hcl y i T').1
  · exact fun g hg h0 => (hcl y i T').2.1 _ (rawOf_source_mem_physVqRho S ρ T.t D hX g hg) h0
  · exact fun g g' hg hg' hag => (hcl y i T').2.2.1 _
      (rawOf_source_mem_physVqRho S ρ T.t D hX g hg) _
      (rawOf_source_mem_physVqRho S ρ T.t D hX g' hg') (fun _ _ => ⟨rfl, rfl⟩) hag
  · exact fun g hg => (hcl y i T').2.2.2 _
      (rawOf_source_mem_physVqRho S ρ T.t D hX g (by linarith))
  · exact fun g hg => ((hval D hDh hX g hg).1 y i)
