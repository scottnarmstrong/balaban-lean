/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.StepIdentityFibreObs
public import Balaban.Inhabited.ObsFamilyPrefactor
public import Balaban.Inhabited.ObsPrefactorScale
public import Balaban.Fluctuation.RootTermFamily
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The zero-class observable coefficients as a family with the root's clauses

For a fixed chart datum `D` of the fibre `h ≡ h₀`, the coefficients `mObs y i (rawOf D, g) T'` of
`obsFamily_pair_fibre_fromTower` (with `q = 1`) are regrouped by `rootTermFamily_of_cubeFamily`
into a family `U x X g` indexed by site, polymer and source, with the root's support, locality,
analyticity and decay clauses, and with the paired sum
`∑ x, ∑ X, ∑ i, g x i * U x X g i = β_U^{-1/2} ∑ y, ∑ i, g y i * ℳ₀(y; g)_i`.
The family `mObs` and its bound constant are chosen before the datum and the decay rate.
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
/-- At source radius `ρ` (`q ≤ ρ`, `max 1 ρ ≤ β`); the landed theorem is its `ρ = 1` corollary.  **The regrouping of the observable coefficients at cube index one.**  The rooted regrouping
`rootTermFamily_of_cubeFamily` and `pairing_of_regroup` applied to a family `mObs` of coefficients
indexed by sets of cubes of index `m`, `m = 1`, with the support, locality, analyticity and decay
clauses on `physVq`, and the pairing identity on the fibre.  It returns the same family with the
cube index `1` (the equation `m = 1` is used by `subst`). -/
theorem rootTermFamily_obs_core_rho {d L N N₁ m₁ k : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
    (S : StepSetting d L N₁ m₁ k N ϱ) (ρ : ℝ) (hρ : 0 < ρ) (t lam B : ℝ) (hLN : L ∣ N₁) (hB : 0 ≤ B)
    {m : ℕ} (hm : m = 1)
    (mObs : CTorus d L N₁ m₁ (k + 1) → Fin N → physParam N S →
      Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) m (k + 1)
        Set.univ) → ℂ)
    (hcl : ∀ y i, ∀ T' : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
      (K := k + 1) m (k + 1) Set.univ),
      AnalyticOnNhd ℂ (fun θ => mObs y i θ T') (physVqRho S S.a₁ S.ν t ρ ρ) ∧
      (∀ θ ∈ physVqRho S S.a₁ S.ν t ρ ρ, mObs y i θ T' ≠ 0 →
        rootCube (m₀ := m) (blockIndex y) ∈ T' ∧ IsPolyDom m (k + 1) (sitesOf T')) ∧
      (∀ θ ∈ physVqRho S S.a₁ S.ν t ρ ρ, ∀ θ' ∈ physVqRho S S.a₁ S.ν t ρ ρ,
        agreeOn (thickSet S.G' (sitesOf T'))
          (θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N)
          (θ'.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) →
        (∀ x ∈ sitesOf T', θ.2 x = θ'.2 x) → mObs y i θ T' = mObs y i θ' T') ∧
      (∀ θ ∈ physVqRho S S.a₁ S.ν t ρ ρ, ‖mObs y i θ T'‖ ≤ B * Real.exp (-lam * dExt T')))
    (hval : ∀ (D : BgData S.G' N) (hDh : ∀ y i, D.h y i = (S.h₀ i : ℂ)),
      XiCData S.G' S.a S.ν (k + 1) 1 t D →
      ∀ g : Fld d L N₁ m₁ (k + 1) N, ∑ x', ∑ i', ‖g x' i'‖ < ρ →
        ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
            ∑ y : CTorus d L N₁ m₁ (k + 1), ∑ i : Fin N,
              g y i * (S.withDatum D hDh).M0C (zeroClass d L N₁ m₁ k N ϱ) g y i =
          ∑ y : CTorus d L N₁ m₁ (k + 1), ∑ i : Fin N,
            g y i * ∑ T', mObs y i ((⟨rawOf D, rawOf_mem_rawSub D⟩ : rawSub N S.G'), g) T') :
    ∃ (mObs' : CTorus d L N₁ m₁ (k + 1) → Fin N → physParam N S →
        Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) 1 (k + 1)
          Set.univ) → ℂ),
      ∀ (D : BgData S.G' N) (hDh : ∀ y i, D.h y i = (S.h₀ i : ℂ)),
        XiCData S.G' S.a S.ν (k + 1) 1 t D →
        ∀ κroot : ℝ, 0 < κroot → c1 d L * κroot ≤ lam →
        ∃ U : CTorus d L N₁ m₁ (k + 1) → Finset (CTorus d L N₁ m₁ (k + 1)) →
            (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) → (Fin N → ℂ),
          (∀ x X, ¬ (x ∈ X ∧ IsPolymer d ((N₁ * L ^ m₁) * L ^ (k + 1))
              (L ^ (m₁ + 1) * L ^ (k + 1)) X) → U x X = 0) ∧
          (∀ x X g g', (∀ y ∈ X, g y = g' y) → U x X g = U x X g') ∧
          (∀ x X, AnalyticOnNhd ℂ (U x X)
            {g : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ | ∑ y, ∑ i, ‖g y i‖ < ρ}) ∧
          (∀ x X g, ∑ y, ∑ i, ‖g y i‖ ≤ ρ / 2 →
            ‖U x X g‖ ≤ B * Real.exp lam *
              Real.exp (-κroot * (X.card : ℝ) /
                ((L ^ (m₁ + 1) * L ^ (k + 1) : ℕ) : ℝ) ^ d)) ∧
          (∀ g : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ, ∑ y, ∑ i, ‖g y i‖ < ρ →
            ∀ x i, ∑ X : Finset (CTorus d L N₁ m₁ (k + 1)), U x X g i =
              ∑ T', mObs' x i ((⟨rawOf D, rawOf_mem_rawSub D⟩ : rawSub N S.G'), g) T') ∧
          ∀ g : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ, ∑ y, ∑ i, ‖g y i‖ < ρ →
            ∑ x, ∑ X : Finset (CTorus d L N₁ m₁ (k + 1)), ∑ i, g x i * U x X g i =
              ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
                ∑ y : CTorus d L N₁ m₁ (k + 1), ∑ i : Fin N,
                  g y i * (S.withDatum D hDh).M0C (zeroClass d L N₁ m₁ k N ϱ) g y i := by
  subst hm
  refine ⟨mObs, ?_⟩
  intro D hDh hX κroot hκ hc
  have hmem : ∀ g : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ, ∑ y, ∑ i, ‖g y i‖ < ρ →
      ((⟨rawOf D, rawOf_mem_rawSub D⟩ : rawSub N S.G'), g) ∈ physVqRho S S.a₁ S.ν t ρ ρ := by
    intro g hg
    exact rawOf_source_mem_physVqRho S ρ t D hX g hg
  obtain ⟨U, h1, h2, h3', h4, h5⟩ := rootTermFamily_of_cubeFamily_rho (d := d) (L := L) (N₁ := N₁)
    (m₁ := m₁) (K := k + 1) (N := N) ρ hρ hLN
    (fun y i g T' => mObs y i ((⟨rawOf D, rawOf_mem_rawSub D⟩ : rawSub N S.G'), g) T')
    (κ := κroot) (lam := lam) (B := B) hκ hc hB
    (fun x i g hg T' h0 => (hcl x i T').2.1 _ (hmem g hg) h0)
    (fun x i T' g hg g' hg' hag =>
      (hcl x i T').2.2.1 _ (hmem g hg) _ (hmem g' hg') (fun _ _ => ⟨rfl, rfl⟩) hag)
    (fun x i T' => (hcl x i T').1.comp
      (analyticOnNhd_const.prod analyticOnNhd_id) (fun g hg => hmem g hg))
    (fun x i T' g hg => (hcl x i T').2.2.2 _ (hmem g (by linarith)))
  refine ⟨U, h1, h2, h3', h4, fun g hg x i => h5 g hg x i, fun g hg => ?_⟩
  rw [pairing_of_regroup (fun y i g T' => mObs y i
    ((⟨rawOf D, rawOf_mem_rawSub D⟩ : rawSub N S.G'), g) T') U g (fun x i => h5 g hg x i)]
  exact (hval D hDh hX g hg).symm

open Classical in
/-- **The regrouping of the observable coefficients at cube index one.**  The rooted regrouping
`rootTermFamily_of_cubeFamily` and `pairing_of_regroup` applied to a family `mObs` of coefficients
indexed by sets of cubes of index `m`, `m = 1`, with the support, locality, analyticity and decay
clauses on `physVq`, and the pairing identity on the fibre.  It returns the same family with the
cube index `1` (the equation `m = 1` is used by `subst`). -/
theorem rootTermFamily_obs_core {d L N N₁ m₁ k : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
    (S : StepSetting d L N₁ m₁ k N ϱ) (t lam B : ℝ) (hLN : L ∣ N₁) (hB : 0 ≤ B)
    {m : ℕ} (hm : m = 1)
    (mObs : CTorus d L N₁ m₁ (k + 1) → Fin N → physParam N S →
      Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) m (k + 1)
        Set.univ) → ℂ)
    (hcl : ∀ y i, ∀ T' : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
      (K := k + 1) m (k + 1) Set.univ),
      AnalyticOnNhd ℂ (fun θ => mObs y i θ T') (physVq S S.a₁ S.ν t 1) ∧
      (∀ θ ∈ physVq S S.a₁ S.ν t 1, mObs y i θ T' ≠ 0 →
        rootCube (m₀ := m) (blockIndex y) ∈ T' ∧ IsPolyDom m (k + 1) (sitesOf T')) ∧
      (∀ θ ∈ physVq S S.a₁ S.ν t 1, ∀ θ' ∈ physVq S S.a₁ S.ν t 1,
        agreeOn (thickSet S.G' (sitesOf T'))
          (θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N)
          (θ'.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) →
        (∀ x ∈ sitesOf T', θ.2 x = θ'.2 x) → mObs y i θ T' = mObs y i θ' T') ∧
      (∀ θ ∈ physVq S S.a₁ S.ν t 1, ‖mObs y i θ T'‖ ≤ B * Real.exp (-lam * dExt T')))
    (hval : ∀ (D : BgData S.G' N) (hDh : ∀ y i, D.h y i = (S.h₀ i : ℂ)),
      XiCData S.G' S.a S.ν (k + 1) 1 t D →
      ∀ g : Fld d L N₁ m₁ (k + 1) N, ∑ x', ∑ i', ‖g x' i'‖ < 1 →
        ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
            ∑ y : CTorus d L N₁ m₁ (k + 1), ∑ i : Fin N,
              g y i * (S.withDatum D hDh).M0C (zeroClass d L N₁ m₁ k N ϱ) g y i =
          ∑ y : CTorus d L N₁ m₁ (k + 1), ∑ i : Fin N,
            g y i * ∑ T', mObs y i ((⟨rawOf D, rawOf_mem_rawSub D⟩ : rawSub N S.G'), g) T') :
    ∃ (mObs' : CTorus d L N₁ m₁ (k + 1) → Fin N → physParam N S →
        Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) 1 (k + 1)
          Set.univ) → ℂ),
      ∀ (D : BgData S.G' N) (hDh : ∀ y i, D.h y i = (S.h₀ i : ℂ)),
        XiCData S.G' S.a S.ν (k + 1) 1 t D →
        ∀ κroot : ℝ, 0 < κroot → c1 d L * κroot ≤ lam →
        ∃ U : CTorus d L N₁ m₁ (k + 1) → Finset (CTorus d L N₁ m₁ (k + 1)) →
            (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) → (Fin N → ℂ),
          (∀ x X, ¬ (x ∈ X ∧ IsPolymer d ((N₁ * L ^ m₁) * L ^ (k + 1))
              (L ^ (m₁ + 1) * L ^ (k + 1)) X) → U x X = 0) ∧
          (∀ x X g g', (∀ y ∈ X, g y = g' y) → U x X g = U x X g') ∧
          (∀ x X, AnalyticOnNhd ℂ (U x X)
            {g : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ | ∑ y, ∑ i, ‖g y i‖ < 1}) ∧
          (∀ x X g, ∑ y, ∑ i, ‖g y i‖ ≤ 1 / 2 →
            ‖U x X g‖ ≤ B * Real.exp lam *
              Real.exp (-κroot * (X.card : ℝ) /
                ((L ^ (m₁ + 1) * L ^ (k + 1) : ℕ) : ℝ) ^ d)) ∧
          (∀ g : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ, ∑ y, ∑ i, ‖g y i‖ < 1 →
            ∀ x i, ∑ X : Finset (CTorus d L N₁ m₁ (k + 1)), U x X g i =
              ∑ T', mObs' x i ((⟨rawOf D, rawOf_mem_rawSub D⟩ : rawSub N S.G'), g) T') ∧
          ∀ g : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ, ∑ y, ∑ i, ‖g y i‖ < 1 →
            ∑ x, ∑ X : Finset (CTorus d L N₁ m₁ (k + 1)), ∑ i, g x i * U x X g i =
              ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
                ∑ y : CTorus d L N₁ m₁ (k + 1), ∑ i : Fin N,
                  g y i * (S.withDatum D hDh).M0C (zeroClass d L N₁ m₁ k N ϱ) g y i := by
  exact rootTermFamily_obs_core_rho S 1 one_pos t lam B hLN hB hm mObs hcl hval

open Classical in
/-- **The observable family on the chart, shared form.**  For the general tower and `ρ > 0`, at
every scale there is one family `mObs` (for all sites `(y, i)`) with the analyticity, support,
locality and prefactor-bound clauses on `physVqRho … ρ ρ`, and the value and pairing identities of
the step at every fibre datum of the chart.  Both `obsCubeFamily_sourceBall_fromTowerG_rho` and
`rootTermFamily_obs_prefactor_fromTowerG_rho` are applications. -/
theorem obsFamilyTheta_fromTowerG_rho {d L N : ℕ} [NeZero L] {κmin : ℝ}
    (T : StepTowerG d L N κmin) {A₁ : ℝ} (hA : 0 < A₁)
    (p : ℕ) {CR s : ℝ} (hCR : 0 < CR) (hs0 : 0 < s) (hs : s < 1 / 2) (ρ : ℝ) (hρ : 0 < ρ) :
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
        (∀ y i, ∀ T' : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := T.m₁)
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
          Real.exp (-(3 / 2 * T.κdec) * dExt T')) ) ∧
        (∀ (D : BgData S.G' N) (hDh : ∀ y i, D.h y i = (S.h₀ i : ℂ)),
          XiCData S.G' S.a S.ν (k + 1) 1 T.t D →
          ∀ g : CTorus d L N₁ T.m₁ (k + 1) → Fin N → ℂ, ∑ y, ∑ i, ‖g y i‖ < ρ →
            (∀ (y : CTorus d L N₁ T.m₁ (k + 1)) (i : Fin N),
              (S.withDatum D hDh).M0C (zeroClass d L N₁ T.m₁ k N (rhoSepG d L T.m₁)) g y i =
                ((S.betaU ^ (1 / 2 : ℝ) : ℝ) : ℂ) *
                  ∑ T', mObs y i ((⟨rawOf D, rawOf_mem_rawSub _⟩ : rawSub N S.G'), g) T') ∧
            ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
                ∑ y : CTorus d L N₁ T.m₁ (k + 1), ∑ i : Fin N,
                  g y i * (S.withDatum D hDh).M0C (zeroClass d L N₁ T.m₁ k N (rhoSepG d L T.m₁))
                    g y i =
              ∑ y : CTorus d L N₁ T.m₁ (k + 1), ∑ i : Fin N,
                g y i * ∑ T', mObs y i ((⟨rawOf D, rawOf_mem_rawSub _⟩ : rawSub N S.G'), g) T') := by
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
  exact ⟨mObs, hcl, fun D hDh hX g hg => hval D hDh hX g hg⟩

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
    obsFamilyTheta_fromTowerG_rho T hA p hCR hs0 hs ρ hρ
  refine ⟨β₀, CE, CF, C, h3, hCE, hCF, hC0, ?_⟩
  intro k hk N₁ _ h3N hN ν hνpos hν β hβ p₁ hp0 hp₁ Dsc S hS hp
  obtain ⟨mObs, hcl, hval⟩ := H k hk N₁ h3N hN ν hνpos hν β hβ p₁ hp0 hp₁ Dsc S hS hp
  refine ⟨mObs, fun D hDh hX y i T' => ⟨?_, ?_, ?_, ?_, ?_⟩⟩
  · exact analyticOn_sourceBall_of_chart S ρ T.t D hX _ (hcl y i T').1
  · exact fun g hg h0 => (hcl y i T').2.1 _ (rawOf_source_mem_physVqRho S ρ T.t D hX g hg) h0
  · exact fun g g' hg hg' hag => (hcl y i T').2.2.1 _
      (rawOf_source_mem_physVqRho S ρ T.t D hX g hg) _
      (rawOf_source_mem_physVqRho S ρ T.t D hX g' hg') (fun _ _ => ⟨rfl, rfl⟩) hag
  · exact fun g hg => (hcl y i T').2.2.2 _
      (rawOf_source_mem_physVqRho S ρ T.t D hX g (by linarith))
  · exact fun g hg => ((hval D hDh hX g hg).1 y i)
open Classical in
/-- At source radius `ρ` (`q ≤ ρ`, `max 1 ρ ≤ β`); the landed theorem is its `ρ = 1` corollary.  **The zero-class observable coefficients with the root's clauses, and the prefactor bound.**
As `rootTermFamily_obs_fromTower`, with a constant `C ≥ 0` chosen with the thresholds (before the
scale) and the bound `C · obsPrefactor p s (β 3^k) · e^{(3/2) κ_dec} · e^{-κroot |X| / (M 3^{k+1})^3}`
in place of the bare constant.  The fixed `rootTermFamily_obs_prefactor_fromTower` is its corollary at `T.toG`.  The cube index is
`T.m₀ = 1` (`hm₀`), because the regrouping `rootTermFamily_of_cubeFamily` is at index one. -/
theorem rootTermFamily_obs_prefactor_fromTowerG_rho {d L N : ℕ} [NeZero L] {κmin : ℝ}
    (T : StepTowerG d L N κmin) (hm₀ : T.m₀ = 1) {A₁ : ℝ} (hA : 0 < A₁)
    (p : ℕ) {CR s : ℝ} (hCR : 0 < CR) (hs0 : 0 < s) (hs : s < 1 / 2) (ρ : ℝ) (hρ : 0 < ρ) :
    ∃ (β₀ CE CF C : ℝ), 3 ≤ β₀ ∧ 0 < CE ∧ 0 < CF ∧ 0 ≤ C ∧
      ∀ (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁] (_h3N : L ^ T.m₀ ∣ N₁), 5 < N₁ →
      ∀ ν : ℝ, 0 < ν → ν * (L : ℝ) ^ (2 * (k + 1)) ≤ 1 → ∀ β : ℝ, β₀ ≤ β →
      ∀ p₁ : ℝ, 0 < p₁ → p₁ ≤ pLog A₁ p (β * (L : ℝ) ^ (k * (d - 2))) →
      ∀ (_ : StepScaleDataG T k hk N₁ ν β p₁)
        (S : StepSetting d L N₁ T.m₁ k N (rhoSepG d L T.m₁)),
        S = T.step k hk N₁ ν β p₁ → ∀ _hp : 0 < S.p₁,
      ∃ (mObs : CTorus d L N₁ T.m₁ (k + 1) → Fin N → physParam N S →
          Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := T.m₁) (K := k + 1) 1 (k + 1)
            Set.univ) → ℂ),
        ∀ (D : BgData S.G' N) (hDh : ∀ y i, D.h y i = (S.h₀ i : ℂ)),
          XiCData S.G' S.a S.ν (k + 1) 1 T.t D →
          ∀ κroot : ℝ, 0 < κroot → c1 d L * κroot ≤ 3 / 2 * T.κdec →
          ∃ U : CTorus d L N₁ T.m₁ (k + 1) → Finset (CTorus d L N₁ T.m₁ (k + 1)) →
              (CTorus d L N₁ T.m₁ (k + 1) → Fin N → ℂ) → (Fin N → ℂ),
            (∀ x X, ¬ (x ∈ X ∧ IsPolymer d ((N₁ * L ^ T.m₁) * L ^ (k + 1))
                (L ^ (T.m₁ + 1) * L ^ (k + 1)) X) → U x X = 0) ∧
            (∀ x X g g', (∀ y ∈ X, g y = g' y) → U x X g = U x X g') ∧
            (∀ x X, AnalyticOnNhd ℂ (U x X)
              {g : CTorus d L N₁ T.m₁ (k + 1) → Fin N → ℂ | ∑ y, ∑ i, ‖g y i‖ < ρ}) ∧
            (∀ x X g, ∑ y, ∑ i, ‖g y i‖ ≤ ρ / 2 →
              ‖U x X g‖ ≤ C * obsPrefactor p s (β * (L : ℝ) ^ (k * (d - 2))) * Real.exp (3 / 2 * T.κdec) *
                Real.exp (-κroot * (X.card : ℝ) /
                  ((L ^ (T.m₁ + 1) * L ^ (k + 1) : ℕ) : ℝ) ^ d)) ∧
            (∀ g : CTorus d L N₁ T.m₁ (k + 1) → Fin N → ℂ, ∑ y, ∑ i, ‖g y i‖ < ρ →
              ∀ x i, ∑ X : Finset (CTorus d L N₁ T.m₁ (k + 1)), U x X g i =
                ∑ T', mObs x i ((⟨rawOf D, rawOf_mem_rawSub D⟩ : rawSub N S.G'), g) T') ∧
            ∀ g : CTorus d L N₁ T.m₁ (k + 1) → Fin N → ℂ, ∑ y, ∑ i, ‖g y i‖ < ρ →
              ∑ x, ∑ X : Finset (CTorus d L N₁ T.m₁ (k + 1)), ∑ i, g x i * U x X g i =
                ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
                  ∑ y : CTorus d L N₁ T.m₁ (k + 1), ∑ i : Fin N,
                    g y i * (S.withDatum D hDh).M0C
                      (zeroClass d L N₁ T.m₁ k N (rhoSepG d L T.m₁)) g y i := by
  classical
  obtain ⟨β₀, CE, CF, C, h3, hCE, hCF, hC0, H⟩ :=
    obsFamilyTheta_fromTowerG_rho T hA p hCR hs0 hs ρ hρ
  refine ⟨β₀, CE, CF, C, h3, hCE, hCF, hC0, ?_⟩
  intro k hk N₁ _ h3N hN ν hνpos hν β hβ p₁ hp0 hp₁ Dsc S hS hp
  obtain ⟨mObs, hcl, hval⟩ := H k hk N₁ h3N hN ν hνpos hν β hβ p₁ hp0 hp₁ Dsc S hS hp
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast (by have := T.hL; omega : 1 ≤ L)
  have hβ1 : 1 ≤ β * (L : ℝ) ^ (k * (d - 2)) := by
    have h3k : (1 : ℝ) ≤ (L : ℝ) ^ (k * (d - 2)) := one_le_pow₀ hL1
    nlinarith [h3]
  have hLN : L ∣ N₁ := by rw [hm₀] at h3N; simpa using h3N
  have hBnn : 0 ≤ C * obsPrefactor p s (β * (L : ℝ) ^ (k * (d - 2))) :=
    mul_nonneg hC0 (obsPrefactor_nonneg p s hβ1)
  exact rootTermFamily_obs_core_rho S ρ hρ T.t (3 / 2 * T.κdec)
    (C * obsPrefactor p s (β * (L : ℝ) ^ (k * (d - 2)))) hLN hBnn hm₀ mObs hcl
    (fun D hDh hX g hg => (hval D hDh hX g hg).2)


open Classical in
/-- **The zero-class observable coefficients with the root's clauses, and the prefactor bound.**
As `rootTermFamily_obs_fromTower`, with a constant `C ≥ 0` chosen with the thresholds (before the
scale) and the bound `C · obsPrefactor p s (β 3^k) · e^{(3/2) κ_dec} · e^{-κroot |X| / (M 3^{k+1})^3}`
in place of the bare constant.  The fixed `rootTermFamily_obs_prefactor_fromTower` is its corollary at `T.toG`.  The cube index is
`T.m₀ = 1` (`hm₀`), because the regrouping `rootTermFamily_of_cubeFamily` is at index one. -/
theorem rootTermFamily_obs_prefactor_fromTowerG {d L N : ℕ} [NeZero L] {κmin : ℝ}
    (T : StepTowerG d L N κmin) (hm₀ : T.m₀ = 1) {A₁ : ℝ} (hA : 0 < A₁)
    (p : ℕ) {CR s : ℝ} (hCR : 0 < CR) (hs0 : 0 < s) (hs : s < 1 / 2) :
    ∃ (β₀ CE CF C : ℝ), 3 ≤ β₀ ∧ 0 < CE ∧ 0 < CF ∧ 0 ≤ C ∧
      ∀ (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁] (_h3N : L ^ T.m₀ ∣ N₁), 5 < N₁ →
      ∀ ν : ℝ, 0 < ν → ν * (L : ℝ) ^ (2 * (k + 1)) ≤ 1 → ∀ β : ℝ, β₀ ≤ β →
      ∀ p₁ : ℝ, 0 < p₁ → p₁ ≤ pLog A₁ p (β * (L : ℝ) ^ (k * (d - 2))) →
      ∀ (_ : StepScaleDataG T k hk N₁ ν β p₁)
        (S : StepSetting d L N₁ T.m₁ k N (rhoSepG d L T.m₁)),
        S = T.step k hk N₁ ν β p₁ → ∀ _hp : 0 < S.p₁,
      ∃ (mObs : CTorus d L N₁ T.m₁ (k + 1) → Fin N → physParam N S →
          Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := T.m₁) (K := k + 1) 1 (k + 1)
            Set.univ) → ℂ),
        ∀ (D : BgData S.G' N) (hDh : ∀ y i, D.h y i = (S.h₀ i : ℂ)),
          XiCData S.G' S.a S.ν (k + 1) 1 T.t D →
          ∀ κroot : ℝ, 0 < κroot → c1 d L * κroot ≤ 3 / 2 * T.κdec →
          ∃ U : CTorus d L N₁ T.m₁ (k + 1) → Finset (CTorus d L N₁ T.m₁ (k + 1)) →
              (CTorus d L N₁ T.m₁ (k + 1) → Fin N → ℂ) → (Fin N → ℂ),
            (∀ x X, ¬ (x ∈ X ∧ IsPolymer d ((N₁ * L ^ T.m₁) * L ^ (k + 1))
                (L ^ (T.m₁ + 1) * L ^ (k + 1)) X) → U x X = 0) ∧
            (∀ x X g g', (∀ y ∈ X, g y = g' y) → U x X g = U x X g') ∧
            (∀ x X, AnalyticOnNhd ℂ (U x X)
              {g : CTorus d L N₁ T.m₁ (k + 1) → Fin N → ℂ | ∑ y, ∑ i, ‖g y i‖ < 1}) ∧
            (∀ x X g, ∑ y, ∑ i, ‖g y i‖ ≤ 1 / 2 →
              ‖U x X g‖ ≤ C * obsPrefactor p s (β * (L : ℝ) ^ (k * (d - 2))) * Real.exp (3 / 2 * T.κdec) *
                Real.exp (-κroot * (X.card : ℝ) /
                  ((L ^ (T.m₁ + 1) * L ^ (k + 1) : ℕ) : ℝ) ^ d)) ∧
            (∀ g : CTorus d L N₁ T.m₁ (k + 1) → Fin N → ℂ, ∑ y, ∑ i, ‖g y i‖ < 1 →
              ∀ x i, ∑ X : Finset (CTorus d L N₁ T.m₁ (k + 1)), U x X g i =
                ∑ T', mObs x i ((⟨rawOf D, rawOf_mem_rawSub D⟩ : rawSub N S.G'), g) T') ∧
            ∀ g : CTorus d L N₁ T.m₁ (k + 1) → Fin N → ℂ, ∑ y, ∑ i, ‖g y i‖ < 1 →
              ∑ x, ∑ X : Finset (CTorus d L N₁ T.m₁ (k + 1)), ∑ i, g x i * U x X g i =
                ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
                  ∑ y : CTorus d L N₁ T.m₁ (k + 1), ∑ i : Fin N,
                    g y i * (S.withDatum D hDh).M0C
                      (zeroClass d L N₁ T.m₁ k N (rhoSepG d L T.m₁)) g y i := by
  exact rootTermFamily_obs_prefactor_fromTowerG_rho T hm₀ hA p hCR hs0 hs 1 one_pos

open Classical in
/-- At source radius `ρ` (`q ≤ ρ`, `max 1 ρ ≤ β`); the landed theorem is its `ρ = 1` corollary.  **The zero-class observable coefficients with the root's clauses, and the prefactor bound.**
As `rootTermFamily_obs_fromTower`, with a constant `C ≥ 0` chosen with the thresholds (before the
scale) and the bound `C · obsPrefactor p s (β 3^k) · e^{(3/2) κ_dec} · e^{-κroot |X| / (M 3^{k+1})^3}`
in place of the bare constant. -/
theorem rootTermFamily_obs_prefactor_fromTower_rho {κmin : ℝ} (T : StepTower κmin) {A₁ : ℝ} (hA : 0 < A₁)
    (p : ℕ) {CR s : ℝ} (hCR : 0 < CR) (hs0 : 0 < s) (hs : s < 1 / 2) (ρ : ℝ) (hρ : 0 < ρ) :
    ∃ (β₀ CE CF C : ℝ), 3 ≤ β₀ ∧ 0 < CE ∧ 0 < CF ∧ 0 ≤ C ∧
      ∀ (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁] (_h3N : 3 ∣ N₁), 5 < N₁ →
      ∀ ν : ℝ, 0 < ν → ν * 3 ^ (2 * (k + 1)) ≤ 1 → ∀ β : ℝ, β₀ ≤ β →
      ∀ p₁ : ℝ, 0 < p₁ → p₁ ≤ pLog A₁ p (β * 3 ^ k) →
      ∀ (_ : StepScaleData T k hk N₁ ν β p₁)
        (S : StepSetting 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)),
        S = T.step k hk N₁ ν β p₁ → ∀ _hp : 0 < S.p₁,
      ∃ (mObs : CTorus 3 3 N₁ T.m₁ (k + 1) → Fin 2 → physParam 2 S →
          Finset (CubeB (d := 3) (L := 3) (N₁ := N₁) (m₁ := T.m₁) (K := k + 1) 1 (k + 1)
            Set.univ) → ℂ),
        ∀ (D : BgData S.G' 2) (hDh : ∀ y i, D.h y i = (S.h₀ i : ℂ)),
          XiCData S.G' S.a S.ν (k + 1) 1 T.t D →
          ∀ κroot : ℝ, 0 < κroot → c1 3 3 * κroot ≤ 3 / 2 * T.κdec →
          ∃ U : CTorus 3 3 N₁ T.m₁ (k + 1) → Finset (CTorus 3 3 N₁ T.m₁ (k + 1)) →
              (CTorus 3 3 N₁ T.m₁ (k + 1) → Fin 2 → ℂ) → (Fin 2 → ℂ),
            (∀ x X, ¬ (x ∈ X ∧ IsPolymer 3 ((N₁ * 3 ^ T.m₁) * 3 ^ (k + 1))
                (3 ^ (T.m₁ + 1) * 3 ^ (k + 1)) X) → U x X = 0) ∧
            (∀ x X g g', (∀ y ∈ X, g y = g' y) → U x X g = U x X g') ∧
            (∀ x X, AnalyticOnNhd ℂ (U x X)
              {g : CTorus 3 3 N₁ T.m₁ (k + 1) → Fin 2 → ℂ | ∑ y, ∑ i, ‖g y i‖ < ρ}) ∧
            (∀ x X g, ∑ y, ∑ i, ‖g y i‖ ≤ ρ / 2 →
              ‖U x X g‖ ≤ C * obsPrefactor p s (β * 3 ^ k) * Real.exp (3 / 2 * T.κdec) *
                Real.exp (-κroot * (X.card : ℝ) /
                  ((3 ^ (T.m₁ + 1) * 3 ^ (k + 1) : ℕ) : ℝ) ^ 3)) ∧
            (∀ g : CTorus 3 3 N₁ T.m₁ (k + 1) → Fin 2 → ℂ, ∑ y, ∑ i, ‖g y i‖ < ρ →
              ∀ x i, ∑ X : Finset (CTorus 3 3 N₁ T.m₁ (k + 1)), U x X g i =
                ∑ T', mObs x i ((⟨rawOf D, rawOf_mem_rawSub D⟩ : rawSub 2 S.G'), g) T') ∧
            ∀ g : CTorus 3 3 N₁ T.m₁ (k + 1) → Fin 2 → ℂ, ∑ y, ∑ i, ‖g y i‖ < ρ →
              ∑ x, ∑ X : Finset (CTorus 3 3 N₁ T.m₁ (k + 1)), ∑ i, g x i * U x X g i =
                ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
                  ∑ y : CTorus 3 3 N₁ T.m₁ (k + 1), ∑ i : Fin 2,
                    g y i * (S.withDatum D hDh).M0C
                      (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) g y i := by
  obtain ⟨β₀, CE, CF, C, h3, hCE, hCF, hC0, H⟩ :=
    rootTermFamily_obs_prefactor_fromTowerG_rho T.toG rfl hA p hCR hs0 hs ρ hρ
  refine ⟨β₀, CE, CF, C, h3, hCE, hCF, hC0, ?_⟩
  intro k hk N₁ _ h3N hN ν hνpos hν β hβ p₁ hp0 hp₁ Dsc S hS hp
  have e : (((3 : ℕ) : ℝ)) ^ (k * (3 - 2)) = 3 ^ k := by norm_num
  subst hS
  have hp' : 0 < (T.toG.step k hk N₁ ν β p₁).p₁ := hp
  have G := H k hk N₁ (by simpa using h3N) hN ν hνpos (by simpa using hν) β hβ p₁ hp0
    (by rw [e]; exact hp₁) (StepTower.scaleDataG_of_fixed T Dsc) (T.toG.step k hk N₁ ν β p₁)
    rfl hp'
  unfold StepTowerG.step at G
  revert G
  generalize hb : β * ((3 : ℕ) : ℝ) ^ (k * (3 - 2)) = b
  generalize hϱ : rhoSepG 3 3 T.toG.m₁ = ϱ
  have hϱ' : ϱ = rhoSep T.m₁ := hϱ.symm.trans (rhoSepG_three _)
  have hb' : b = β * 3 ^ k := hb.symm.trans (by rw [e])
  subst hϱ' hb'
  intro G
  exact G

open Classical in
/-- **The zero-class observable coefficients with the root's clauses, and the prefactor bound.**
As `rootTermFamily_obs_fromTower`, with a constant `C ≥ 0` chosen with the thresholds (before the
scale) and the bound `C · obsPrefactor p s (β 3^k) · e^{(3/2) κ_dec} · e^{-κroot |X| / (M 3^{k+1})^3}`
in place of the bare constant. -/
theorem rootTermFamily_obs_prefactor_fromTower {κmin : ℝ} (T : StepTower κmin) {A₁ : ℝ} (hA : 0 < A₁)
    (p : ℕ) {CR s : ℝ} (hCR : 0 < CR) (hs0 : 0 < s) (hs : s < 1 / 2) :
    ∃ (β₀ CE CF C : ℝ), 3 ≤ β₀ ∧ 0 < CE ∧ 0 < CF ∧ 0 ≤ C ∧
      ∀ (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁] (_h3N : 3 ∣ N₁), 5 < N₁ →
      ∀ ν : ℝ, 0 < ν → ν * 3 ^ (2 * (k + 1)) ≤ 1 → ∀ β : ℝ, β₀ ≤ β →
      ∀ p₁ : ℝ, 0 < p₁ → p₁ ≤ pLog A₁ p (β * 3 ^ k) →
      ∀ (_ : StepScaleData T k hk N₁ ν β p₁)
        (S : StepSetting 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)),
        S = T.step k hk N₁ ν β p₁ → ∀ _hp : 0 < S.p₁,
      ∃ (mObs : CTorus 3 3 N₁ T.m₁ (k + 1) → Fin 2 → physParam 2 S →
          Finset (CubeB (d := 3) (L := 3) (N₁ := N₁) (m₁ := T.m₁) (K := k + 1) 1 (k + 1)
            Set.univ) → ℂ),
        ∀ (D : BgData S.G' 2) (hDh : ∀ y i, D.h y i = (S.h₀ i : ℂ)),
          XiCData S.G' S.a S.ν (k + 1) 1 T.t D →
          ∀ κroot : ℝ, 0 < κroot → c1 3 3 * κroot ≤ 3 / 2 * T.κdec →
          ∃ U : CTorus 3 3 N₁ T.m₁ (k + 1) → Finset (CTorus 3 3 N₁ T.m₁ (k + 1)) →
              (CTorus 3 3 N₁ T.m₁ (k + 1) → Fin 2 → ℂ) → (Fin 2 → ℂ),
            (∀ x X, ¬ (x ∈ X ∧ IsPolymer 3 ((N₁ * 3 ^ T.m₁) * 3 ^ (k + 1))
                (3 ^ (T.m₁ + 1) * 3 ^ (k + 1)) X) → U x X = 0) ∧
            (∀ x X g g', (∀ y ∈ X, g y = g' y) → U x X g = U x X g') ∧
            (∀ x X, AnalyticOnNhd ℂ (U x X)
              {g : CTorus 3 3 N₁ T.m₁ (k + 1) → Fin 2 → ℂ | ∑ y, ∑ i, ‖g y i‖ < 1}) ∧
            (∀ x X g, ∑ y, ∑ i, ‖g y i‖ ≤ 1 / 2 →
              ‖U x X g‖ ≤ C * obsPrefactor p s (β * 3 ^ k) * Real.exp (3 / 2 * T.κdec) *
                Real.exp (-κroot * (X.card : ℝ) /
                  ((3 ^ (T.m₁ + 1) * 3 ^ (k + 1) : ℕ) : ℝ) ^ 3)) ∧
            (∀ g : CTorus 3 3 N₁ T.m₁ (k + 1) → Fin 2 → ℂ, ∑ y, ∑ i, ‖g y i‖ < 1 →
              ∀ x i, ∑ X : Finset (CTorus 3 3 N₁ T.m₁ (k + 1)), U x X g i =
                ∑ T', mObs x i ((⟨rawOf D, rawOf_mem_rawSub D⟩ : rawSub 2 S.G'), g) T') ∧
            ∀ g : CTorus 3 3 N₁ T.m₁ (k + 1) → Fin 2 → ℂ, ∑ y, ∑ i, ‖g y i‖ < 1 →
              ∑ x, ∑ X : Finset (CTorus 3 3 N₁ T.m₁ (k + 1)), ∑ i, g x i * U x X g i =
                ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
                  ∑ y : CTorus 3 3 N₁ T.m₁ (k + 1), ∑ i : Fin 2,
                    g y i * (S.withDatum D hDh).M0C
                      (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) g y i := by
  exact rootTermFamily_obs_prefactor_fromTower_rho T hA p hCR hs0 hs 1 one_pos

open Classical in
/-- At source radius `ρ` (`q ≤ ρ`, `max 1 ρ ≤ β`); the landed theorem is its `ρ = 1` corollary.  **The zero-class observable coefficients with the root's clauses.**  At the scale data of
`obsFamily_pair_fibre_fromTower` with `q = 1` there are a bound constant `B ≥ 0` and a family
`mObs y i θ T'` (chosen before the datum), such that for every chart datum `D` of the fibre
and every `κroot > 0` with `c1 3 3 * κroot ≤ (3/2) κ_dec` there is `U x X g` that vanishes unless
`x ∈ X` and `X` is a polymer, is local in `g` on `X`, is analytic in `g` on the unit `ℓ¹` ball,
is bounded by `B e^{(3/2) κ_dec} e^{-κroot |X| / (M 3^{k+1})^3}` on the half ball, and pairs with
the source to `β_U^{-1/2} ∑ g ℳ₀`.  The fixed `rootTermFamily_obs_fromTower` is its corollary. -/
theorem rootTermFamily_obs_fromTowerG_rho {d L N : ℕ} [NeZero L] {κmin : ℝ}
    (T : StepTowerG d L N κmin) (hm₀ : T.m₀ = 1) {A₁ : ℝ} (hA : 0 < A₁)
    (p : ℕ) {CR s : ℝ} (hCR : 0 < CR) (hs0 : 0 < s) (hs : s < 1 / 2) (ρ : ℝ) (hρ : 0 < ρ) :
    ∃ (β₀ CE CF : ℝ), 3 ≤ β₀ ∧ 0 < CE ∧ 0 < CF ∧
      ∀ (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁] (_h3N : L ^ T.m₀ ∣ N₁), 5 < N₁ →
      ∀ ν : ℝ, 0 < ν → ν * (L : ℝ) ^ (2 * (k + 1)) ≤ 1 → ∀ β : ℝ, β₀ ≤ β →
      ∀ p₁ : ℝ, 0 < p₁ → p₁ ≤ pLog A₁ p (β * (L : ℝ) ^ (k * (d - 2))) →
      ∀ (_ : StepScaleDataG T k hk N₁ ν β p₁)
        (S : StepSetting d L N₁ T.m₁ k N (rhoSepG d L T.m₁)),
        S = T.step k hk N₁ ν β p₁ → ∀ _hp : 0 < S.p₁,
      ∃ (B : ℝ) (mObs : CTorus d L N₁ T.m₁ (k + 1) → Fin N → physParam N S →
          Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := T.m₁) (K := k + 1) 1 (k + 1)
            Set.univ) → ℂ), 0 ≤ B ∧
        ∀ (D : BgData S.G' N) (hDh : ∀ y i, D.h y i = (S.h₀ i : ℂ)),
          XiCData S.G' S.a S.ν (k + 1) 1 T.t D →
          ∀ κroot : ℝ, 0 < κroot → c1 d L * κroot ≤ 3 / 2 * T.κdec →
          ∃ U : CTorus d L N₁ T.m₁ (k + 1) → Finset (CTorus d L N₁ T.m₁ (k + 1)) →
              (CTorus d L N₁ T.m₁ (k + 1) → Fin N → ℂ) → (Fin N → ℂ),
            (∀ x X, ¬ (x ∈ X ∧ IsPolymer d ((N₁ * L ^ T.m₁) * L ^ (k + 1))
                (L ^ (T.m₁ + 1) * L ^ (k + 1)) X) → U x X = 0) ∧
            (∀ x X g g', (∀ y ∈ X, g y = g' y) → U x X g = U x X g') ∧
            (∀ x X, AnalyticOnNhd ℂ (U x X)
              {g : CTorus d L N₁ T.m₁ (k + 1) → Fin N → ℂ | ∑ y, ∑ i, ‖g y i‖ < ρ}) ∧
            (∀ x X g, ∑ y, ∑ i, ‖g y i‖ ≤ ρ / 2 →
              ‖U x X g‖ ≤ B * Real.exp (3 / 2 * T.κdec) *
                Real.exp (-κroot * (X.card : ℝ) /
                  ((L ^ (T.m₁ + 1) * L ^ (k + 1) : ℕ) : ℝ) ^ d)) ∧
            (∀ g : CTorus d L N₁ T.m₁ (k + 1) → Fin N → ℂ, ∑ y, ∑ i, ‖g y i‖ < ρ →
              ∀ x i, ∑ X : Finset (CTorus d L N₁ T.m₁ (k + 1)), U x X g i =
                ∑ T', mObs x i ((⟨rawOf D, rawOf_mem_rawSub D⟩ : rawSub N S.G'), g) T') ∧
            ∀ g : CTorus d L N₁ T.m₁ (k + 1) → Fin N → ℂ, ∑ y, ∑ i, ‖g y i‖ < ρ →
              ∑ x, ∑ X : Finset (CTorus d L N₁ T.m₁ (k + 1)), ∑ i, g x i * U x X g i =
                ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
                  ∑ y : CTorus d L N₁ T.m₁ (k + 1), ∑ i : Fin N,
                    g y i * (S.withDatum D hDh).M0C
                      (zeroClass d L N₁ T.m₁ k N (rhoSepG d L T.m₁)) g y i := by
  classical
  obtain ⟨β₀, CE, CF, C, h3, hCE, hCF, hC0, H⟩ :=
    rootTermFamily_obs_prefactor_fromTowerG_rho T hm₀ hA p hCR hs0 hs ρ hρ
  refine ⟨β₀, CE, CF, h3, hCE, hCF, ?_⟩
  intro k hk N₁ _ h3N hN ν hνpos hν β hβ p₁ hp0 hp₁ Dsc S hS hp
  obtain ⟨mObs, H2⟩ := H k hk N₁ h3N hN ν hνpos hν β hβ p₁ hp0 hp₁ Dsc S hS hp
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast (by have := T.hL; omega : 1 ≤ L)
  have hβ1 : 1 ≤ β * (L : ℝ) ^ (k * (d - 2)) := by
    have h3k : (1 : ℝ) ≤ (L : ℝ) ^ (k * (d - 2)) := one_le_pow₀ hL1
    nlinarith [h3]
  exact ⟨C * obsPrefactor p s (β * (L : ℝ) ^ (k * (d - 2))), mObs,
    mul_nonneg hC0 (obsPrefactor_nonneg p s hβ1), H2⟩

open Classical in
/-- **The zero-class observable coefficients with the root's clauses.**  At the scale data of
`obsFamily_pair_fibre_fromTower` with `q = 1` there are a bound constant `B ≥ 0` and a family
`mObs y i θ T'` (chosen before the datum), such that for every chart datum `D` of the fibre
and every `κroot > 0` with `c1 3 3 * κroot ≤ (3/2) κ_dec` there is `U x X g` that vanishes unless
`x ∈ X` and `X` is a polymer, is local in `g` on `X`, is analytic in `g` on the unit `ℓ¹` ball,
is bounded by `B e^{(3/2) κ_dec} e^{-κroot |X| / (M 3^{k+1})^3}` on the half ball, and pairs with
the source to `β_U^{-1/2} ∑ g ℳ₀`.  The fixed `rootTermFamily_obs_fromTower` is its corollary. -/
theorem rootTermFamily_obs_fromTowerG {d L N : ℕ} [NeZero L] {κmin : ℝ}
    (T : StepTowerG d L N κmin) (hm₀ : T.m₀ = 1) {A₁ : ℝ} (hA : 0 < A₁)
    (p : ℕ) {CR s : ℝ} (hCR : 0 < CR) (hs0 : 0 < s) (hs : s < 1 / 2) :
    ∃ (β₀ CE CF : ℝ), 3 ≤ β₀ ∧ 0 < CE ∧ 0 < CF ∧
      ∀ (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁] (_h3N : L ^ T.m₀ ∣ N₁), 5 < N₁ →
      ∀ ν : ℝ, 0 < ν → ν * (L : ℝ) ^ (2 * (k + 1)) ≤ 1 → ∀ β : ℝ, β₀ ≤ β →
      ∀ p₁ : ℝ, 0 < p₁ → p₁ ≤ pLog A₁ p (β * (L : ℝ) ^ (k * (d - 2))) →
      ∀ (_ : StepScaleDataG T k hk N₁ ν β p₁)
        (S : StepSetting d L N₁ T.m₁ k N (rhoSepG d L T.m₁)),
        S = T.step k hk N₁ ν β p₁ → ∀ _hp : 0 < S.p₁,
      ∃ (B : ℝ) (mObs : CTorus d L N₁ T.m₁ (k + 1) → Fin N → physParam N S →
          Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := T.m₁) (K := k + 1) 1 (k + 1)
            Set.univ) → ℂ), 0 ≤ B ∧
        ∀ (D : BgData S.G' N) (hDh : ∀ y i, D.h y i = (S.h₀ i : ℂ)),
          XiCData S.G' S.a S.ν (k + 1) 1 T.t D →
          ∀ κroot : ℝ, 0 < κroot → c1 d L * κroot ≤ 3 / 2 * T.κdec →
          ∃ U : CTorus d L N₁ T.m₁ (k + 1) → Finset (CTorus d L N₁ T.m₁ (k + 1)) →
              (CTorus d L N₁ T.m₁ (k + 1) → Fin N → ℂ) → (Fin N → ℂ),
            (∀ x X, ¬ (x ∈ X ∧ IsPolymer d ((N₁ * L ^ T.m₁) * L ^ (k + 1))
                (L ^ (T.m₁ + 1) * L ^ (k + 1)) X) → U x X = 0) ∧
            (∀ x X g g', (∀ y ∈ X, g y = g' y) → U x X g = U x X g') ∧
            (∀ x X, AnalyticOnNhd ℂ (U x X)
              {g : CTorus d L N₁ T.m₁ (k + 1) → Fin N → ℂ | ∑ y, ∑ i, ‖g y i‖ < 1}) ∧
            (∀ x X g, ∑ y, ∑ i, ‖g y i‖ ≤ 1 / 2 →
              ‖U x X g‖ ≤ B * Real.exp (3 / 2 * T.κdec) *
                Real.exp (-κroot * (X.card : ℝ) /
                  ((L ^ (T.m₁ + 1) * L ^ (k + 1) : ℕ) : ℝ) ^ d)) ∧
            (∀ g : CTorus d L N₁ T.m₁ (k + 1) → Fin N → ℂ, ∑ y, ∑ i, ‖g y i‖ < 1 →
              ∀ x i, ∑ X : Finset (CTorus d L N₁ T.m₁ (k + 1)), U x X g i =
                ∑ T', mObs x i ((⟨rawOf D, rawOf_mem_rawSub D⟩ : rawSub N S.G'), g) T') ∧
            ∀ g : CTorus d L N₁ T.m₁ (k + 1) → Fin N → ℂ, ∑ y, ∑ i, ‖g y i‖ < 1 →
              ∑ x, ∑ X : Finset (CTorus d L N₁ T.m₁ (k + 1)), ∑ i, g x i * U x X g i =
                ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
                  ∑ y : CTorus d L N₁ T.m₁ (k + 1), ∑ i : Fin N,
                    g y i * (S.withDatum D hDh).M0C
                      (zeroClass d L N₁ T.m₁ k N (rhoSepG d L T.m₁)) g y i := by
  exact rootTermFamily_obs_fromTowerG_rho T hm₀ hA p hCR hs0 hs 1 one_pos

open Classical in
/-- At source radius `ρ` (`q ≤ ρ`, `max 1 ρ ≤ β`); the landed theorem is its `ρ = 1` corollary.  **The zero-class observable coefficients with the root's clauses.**  At the scale data of
`obsFamily_pair_fibre_fromTower` with `q = 1` there are a bound constant `B ≥ 0` and a family
`mObs y i θ T'` (chosen before the datum), such that for every chart datum `D` of the fibre
and every `κroot > 0` with `c1 3 3 * κroot ≤ (3/2) κ_dec` there is `U x X g` that vanishes unless
`x ∈ X` and `X` is a polymer, is local in `g` on `X`, is analytic in `g` on the unit `ℓ¹` ball,
is bounded by `B e^{(3/2) κ_dec} e^{-κroot |X| / (M 3^{k+1})^3}` on the half ball, and pairs with
the source to `β_U^{-1/2} ∑ g ℳ₀`. -/
theorem rootTermFamily_obs_fromTower_rho {κmin : ℝ} (T : StepTower κmin) {A₁ : ℝ} (hA : 0 < A₁)
    (p : ℕ) {CR s : ℝ} (hCR : 0 < CR) (hs0 : 0 < s) (hs : s < 1 / 2) (ρ : ℝ) (hρ : 0 < ρ) :
    ∃ (β₀ CE CF : ℝ), 3 ≤ β₀ ∧ 0 < CE ∧ 0 < CF ∧
      ∀ (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁] (_h3N : 3 ∣ N₁), 5 < N₁ →
      ∀ ν : ℝ, 0 < ν → ν * 3 ^ (2 * (k + 1)) ≤ 1 → ∀ β : ℝ, β₀ ≤ β →
      ∀ p₁ : ℝ, 0 < p₁ → p₁ ≤ pLog A₁ p (β * 3 ^ k) →
      ∀ (_ : StepScaleData T k hk N₁ ν β p₁)
        (S : StepSetting 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)),
        S = T.step k hk N₁ ν β p₁ → ∀ _hp : 0 < S.p₁,
      ∃ (B : ℝ) (mObs : CTorus 3 3 N₁ T.m₁ (k + 1) → Fin 2 → physParam 2 S →
          Finset (CubeB (d := 3) (L := 3) (N₁ := N₁) (m₁ := T.m₁) (K := k + 1) 1 (k + 1)
            Set.univ) → ℂ), 0 ≤ B ∧
        ∀ (D : BgData S.G' 2) (hDh : ∀ y i, D.h y i = (S.h₀ i : ℂ)),
          XiCData S.G' S.a S.ν (k + 1) 1 T.t D →
          ∀ κroot : ℝ, 0 < κroot → c1 3 3 * κroot ≤ 3 / 2 * T.κdec →
          ∃ U : CTorus 3 3 N₁ T.m₁ (k + 1) → Finset (CTorus 3 3 N₁ T.m₁ (k + 1)) →
              (CTorus 3 3 N₁ T.m₁ (k + 1) → Fin 2 → ℂ) → (Fin 2 → ℂ),
            (∀ x X, ¬ (x ∈ X ∧ IsPolymer 3 ((N₁ * 3 ^ T.m₁) * 3 ^ (k + 1))
                (3 ^ (T.m₁ + 1) * 3 ^ (k + 1)) X) → U x X = 0) ∧
            (∀ x X g g', (∀ y ∈ X, g y = g' y) → U x X g = U x X g') ∧
            (∀ x X, AnalyticOnNhd ℂ (U x X)
              {g : CTorus 3 3 N₁ T.m₁ (k + 1) → Fin 2 → ℂ | ∑ y, ∑ i, ‖g y i‖ < ρ}) ∧
            (∀ x X g, ∑ y, ∑ i, ‖g y i‖ ≤ ρ / 2 →
              ‖U x X g‖ ≤ B * Real.exp (3 / 2 * T.κdec) *
                Real.exp (-κroot * (X.card : ℝ) /
                  ((3 ^ (T.m₁ + 1) * 3 ^ (k + 1) : ℕ) : ℝ) ^ 3)) ∧
            (∀ g : CTorus 3 3 N₁ T.m₁ (k + 1) → Fin 2 → ℂ, ∑ y, ∑ i, ‖g y i‖ < ρ →
              ∀ x i, ∑ X : Finset (CTorus 3 3 N₁ T.m₁ (k + 1)), U x X g i =
                ∑ T', mObs x i ((⟨rawOf D, rawOf_mem_rawSub D⟩ : rawSub 2 S.G'), g) T') ∧
            ∀ g : CTorus 3 3 N₁ T.m₁ (k + 1) → Fin 2 → ℂ, ∑ y, ∑ i, ‖g y i‖ < ρ →
              ∑ x, ∑ X : Finset (CTorus 3 3 N₁ T.m₁ (k + 1)), ∑ i, g x i * U x X g i =
                ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
                  ∑ y : CTorus 3 3 N₁ T.m₁ (k + 1), ∑ i : Fin 2,
                    g y i * (S.withDatum D hDh).M0C
                      (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) g y i := by
  obtain ⟨β₀, CE, CF, h3, hCE, hCF, H⟩ := rootTermFamily_obs_fromTowerG_rho T.toG rfl hA p hCR hs0 hs ρ hρ
  refine ⟨β₀, CE, CF, h3, hCE, hCF, ?_⟩
  intro k hk N₁ _ h3N hN ν hνpos hν β hβ p₁ hp0 hp₁ Dsc S hS hp
  have e : (((3 : ℕ) : ℝ)) ^ (k * (3 - 2)) = 3 ^ k := by norm_num
  subst hS
  have hp' : 0 < (T.toG.step k hk N₁ ν β p₁).p₁ := hp
  have G := H k hk N₁ (by simpa using h3N) hN ν hνpos (by simpa using hν) β hβ p₁ hp0
    (by rw [e]; exact hp₁) (StepTower.scaleDataG_of_fixed T Dsc) (T.toG.step k hk N₁ ν β p₁)
    rfl hp'
  unfold StepTowerG.step at G
  revert G
  generalize hb : β * ((3 : ℕ) : ℝ) ^ (k * (3 - 2)) = b
  generalize hϱ : rhoSepG 3 3 T.toG.m₁ = ϱ
  have hϱ' : ϱ = rhoSep T.m₁ := hϱ.symm.trans (rhoSepG_three _)
  have hb' : b = β * 3 ^ k := hb.symm.trans (by rw [e])
  subst hϱ' hb'
  intro G
  exact G

open Classical in
/-- **The zero-class observable coefficients with the root's clauses.**  At the scale data of
`obsFamily_pair_fibre_fromTower` with `q = 1` there are a bound constant `B ≥ 0` and a family
`mObs y i θ T'` (chosen before the datum), such that for every chart datum `D` of the fibre
and every `κroot > 0` with `c1 3 3 * κroot ≤ (3/2) κ_dec` there is `U x X g` that vanishes unless
`x ∈ X` and `X` is a polymer, is local in `g` on `X`, is analytic in `g` on the unit `ℓ¹` ball,
is bounded by `B e^{(3/2) κ_dec} e^{-κroot |X| / (M 3^{k+1})^3}` on the half ball, and pairs with
the source to `β_U^{-1/2} ∑ g ℳ₀`. -/
theorem rootTermFamily_obs_fromTower {κmin : ℝ} (T : StepTower κmin) {A₁ : ℝ} (hA : 0 < A₁)
    (p : ℕ) {CR s : ℝ} (hCR : 0 < CR) (hs0 : 0 < s) (hs : s < 1 / 2) :
    ∃ (β₀ CE CF : ℝ), 3 ≤ β₀ ∧ 0 < CE ∧ 0 < CF ∧
      ∀ (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁] (_h3N : 3 ∣ N₁), 5 < N₁ →
      ∀ ν : ℝ, 0 < ν → ν * 3 ^ (2 * (k + 1)) ≤ 1 → ∀ β : ℝ, β₀ ≤ β →
      ∀ p₁ : ℝ, 0 < p₁ → p₁ ≤ pLog A₁ p (β * 3 ^ k) →
      ∀ (_ : StepScaleData T k hk N₁ ν β p₁)
        (S : StepSetting 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)),
        S = T.step k hk N₁ ν β p₁ → ∀ _hp : 0 < S.p₁,
      ∃ (B : ℝ) (mObs : CTorus 3 3 N₁ T.m₁ (k + 1) → Fin 2 → physParam 2 S →
          Finset (CubeB (d := 3) (L := 3) (N₁ := N₁) (m₁ := T.m₁) (K := k + 1) 1 (k + 1)
            Set.univ) → ℂ), 0 ≤ B ∧
        ∀ (D : BgData S.G' 2) (hDh : ∀ y i, D.h y i = (S.h₀ i : ℂ)),
          XiCData S.G' S.a S.ν (k + 1) 1 T.t D →
          ∀ κroot : ℝ, 0 < κroot → c1 3 3 * κroot ≤ 3 / 2 * T.κdec →
          ∃ U : CTorus 3 3 N₁ T.m₁ (k + 1) → Finset (CTorus 3 3 N₁ T.m₁ (k + 1)) →
              (CTorus 3 3 N₁ T.m₁ (k + 1) → Fin 2 → ℂ) → (Fin 2 → ℂ),
            (∀ x X, ¬ (x ∈ X ∧ IsPolymer 3 ((N₁ * 3 ^ T.m₁) * 3 ^ (k + 1))
                (3 ^ (T.m₁ + 1) * 3 ^ (k + 1)) X) → U x X = 0) ∧
            (∀ x X g g', (∀ y ∈ X, g y = g' y) → U x X g = U x X g') ∧
            (∀ x X, AnalyticOnNhd ℂ (U x X)
              {g : CTorus 3 3 N₁ T.m₁ (k + 1) → Fin 2 → ℂ | ∑ y, ∑ i, ‖g y i‖ < 1}) ∧
            (∀ x X g, ∑ y, ∑ i, ‖g y i‖ ≤ 1 / 2 →
              ‖U x X g‖ ≤ B * Real.exp (3 / 2 * T.κdec) *
                Real.exp (-κroot * (X.card : ℝ) /
                  ((3 ^ (T.m₁ + 1) * 3 ^ (k + 1) : ℕ) : ℝ) ^ 3)) ∧
            (∀ g : CTorus 3 3 N₁ T.m₁ (k + 1) → Fin 2 → ℂ, ∑ y, ∑ i, ‖g y i‖ < 1 →
              ∀ x i, ∑ X : Finset (CTorus 3 3 N₁ T.m₁ (k + 1)), U x X g i =
                ∑ T', mObs x i ((⟨rawOf D, rawOf_mem_rawSub D⟩ : rawSub 2 S.G'), g) T') ∧
            ∀ g : CTorus 3 3 N₁ T.m₁ (k + 1) → Fin 2 → ℂ, ∑ y, ∑ i, ‖g y i‖ < 1 →
              ∑ x, ∑ X : Finset (CTorus 3 3 N₁ T.m₁ (k + 1)), ∑ i, g x i * U x X g i =
                ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
                  ∑ y : CTorus 3 3 N₁ T.m₁ (k + 1), ∑ i : Fin 2,
                    g y i * (S.withDatum D hDh).M0C
                      (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) g y i := by
  exact rootTermFamily_obs_fromTower_rho T hA p hCR hs0 hs 1 one_pos

open Classical in
/-- At source radius `ρ` (`q ≤ ρ`, `max 1 ρ ≤ β`); the landed theorem is its `ρ = 1` corollary.  **The zero-class observable terms with the root's per-term bound at their birth scale.**
For every `c₉ > 0` and `0 < δ' < min s (1/2)` there is a threshold, chosen before the scale, such
that for `β` beyond it the family `U` of `rootTermFamily_obs_prefactor_fromTower` satisfies, on the
half ball, `‖U x X g‖ ≤ c₉ 3^{-(k+1)(1/2+δ')} e^{-κroot |X| / (M 3^{k+1})^3}`
(the root's exponent `(d-2)/2 + δ` with `d = 3`).  The fixed `rootTermFamily_obs_birthScale_fromTower` is its corollary.  The exponent is `(d-2)/2 + δ'` and `δ' < min (s (d-2)) ((d-2)/2)`. -/
theorem rootTermFamily_obs_birthScale_fromTowerG_rho {d L N : ℕ} [NeZero L] {κmin : ℝ}
    (T : StepTowerG d L N κmin) (hm₀ : T.m₀ = 1) {A₁ : ℝ} (hA : 0 < A₁)
    (p : ℕ) {CR s : ℝ} (hCR : 0 < CR) (hs0 : 0 < s) (hs : s < 1 / 2) (ρ : ℝ) (hρ : 0 < ρ) :
    ∀ c₉ : ℝ, 0 < c₉ → ∀ δ' : ℝ, 0 < δ' → δ' < min (s * ((d : ℝ) - 2)) (((d : ℝ) - 2) / 2) →
    ∃ (β₀ CE CF : ℝ), 3 ≤ β₀ ∧ 0 < CE ∧ 0 < CF ∧
      ∀ (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁] (_h3N : L ^ T.m₀ ∣ N₁), 5 < N₁ →
      ∀ ν : ℝ, 0 < ν → ν * (L : ℝ) ^ (2 * (k + 1)) ≤ 1 → ∀ β : ℝ, β₀ ≤ β →
      ∀ p₁ : ℝ, 0 < p₁ → p₁ ≤ pLog A₁ p (β * (L : ℝ) ^ (k * (d - 2))) →
      ∀ (_ : StepScaleDataG T k hk N₁ ν β p₁)
        (S : StepSetting d L N₁ T.m₁ k N (rhoSepG d L T.m₁)),
        S = T.step k hk N₁ ν β p₁ → ∀ _hp : 0 < S.p₁,
      ∃ (mObs : CTorus d L N₁ T.m₁ (k + 1) → Fin N → physParam N S →
          Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := T.m₁) (K := k + 1) 1 (k + 1)
            Set.univ) → ℂ),
        ∀ (D : BgData S.G' N) (hDh : ∀ y i, D.h y i = (S.h₀ i : ℂ)),
          XiCData S.G' S.a S.ν (k + 1) 1 T.t D →
          ∀ κroot : ℝ, 0 < κroot → c1 d L * κroot ≤ 3 / 2 * T.κdec →
          ∃ U : CTorus d L N₁ T.m₁ (k + 1) → Finset (CTorus d L N₁ T.m₁ (k + 1)) →
              (CTorus d L N₁ T.m₁ (k + 1) → Fin N → ℂ) → (Fin N → ℂ),
            (∀ x X, ¬ (x ∈ X ∧ IsPolymer d ((N₁ * L ^ T.m₁) * L ^ (k + 1))
                (L ^ (T.m₁ + 1) * L ^ (k + 1)) X) → U x X = 0) ∧
            (∀ x X g g', (∀ y ∈ X, g y = g' y) → U x X g = U x X g') ∧
            (∀ x X, AnalyticOnNhd ℂ (U x X)
              {g : CTorus d L N₁ T.m₁ (k + 1) → Fin N → ℂ | ∑ y, ∑ i, ‖g y i‖ < ρ}) ∧
            (∀ x X g, ∑ y, ∑ i, ‖g y i‖ ≤ ρ / 2 →
              ‖U x X g‖ ≤ c₉ * (L : ℝ) ^ (-(((k + 1 : ℕ) : ℝ) * (((d : ℝ) - 2) / 2 + δ'))) *
                Real.exp (-κroot * (X.card : ℝ) /
                  ((L ^ (T.m₁ + 1) * L ^ (k + 1) : ℕ) : ℝ) ^ d)) ∧
            (∀ g : CTorus d L N₁ T.m₁ (k + 1) → Fin N → ℂ, ∑ y, ∑ i, ‖g y i‖ < ρ →
              ∀ x i, ∑ X : Finset (CTorus d L N₁ T.m₁ (k + 1)), U x X g i =
                ∑ T', mObs x i ((⟨rawOf D, rawOf_mem_rawSub D⟩ : rawSub N S.G'), g) T') ∧
            ∀ g : CTorus d L N₁ T.m₁ (k + 1) → Fin N → ℂ, ∑ y, ∑ i, ‖g y i‖ < ρ →
              ∑ x, ∑ X : Finset (CTorus d L N₁ T.m₁ (k + 1)), ∑ i, g x i * U x X g i =
                ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
                  ∑ y : CTorus d L N₁ T.m₁ (k + 1), ∑ i : Fin N,
                    g y i * (S.withDatum D hDh).M0C
                      (zeroClass d L N₁ T.m₁ k N (rhoSepG d L T.m₁)) g y i := by
  classical
  intro c₉ hc₉ δ' hδ0 hδ
  have hδs : δ' < s * ((d : ℝ) - 2) := lt_of_lt_of_le hδ (min_le_left _ _)
  have hδd : δ' < ((d : ℝ) - 2) / 2 := lt_of_lt_of_le hδ (min_le_right _ _)
  obtain ⟨β₀, CE, CF, C, h3, hCE, hCF, hC0, H⟩ :=
    rootTermFamily_obs_prefactor_fromTowerG_rho T hm₀ hA p hCR hs0 hs ρ hρ
  obtain ⟨C', hC'0, hC'⟩ := obsPrefactor_le_birth_scale p T.hd hδs hδd
  have hd2 : (0 : ℝ) < (d : ℝ) - 2 := by
    have : (3 : ℝ) ≤ d := by exact_mod_cast T.hd
    linarith
  have hL2 : 2 ≤ L := by have := T.hL; omega
  have hL0 : (0 : ℝ) < L := by
    have : (2 : ℝ) ≤ L := by exact_mod_cast hL2
    linarith
  obtain ⟨β₁, hβ₁, hβ₁c⟩ := birth_const_le_of_large
    (C := C * C' * Real.exp (3 / 2 * T.κdec)) (c := c₉)
    (e := ((d : ℝ) - 2) / 2 + δ') (q := (((d : ℝ) - 2) / 2 + δ') / ((d : ℝ) - 2)) (L : ℝ) hL0 hc₉
    (by positivity)
  refine ⟨max β₀ β₁, CE, CF, h3.trans (le_max_left _ _), hCE, hCF, ?_⟩
  intro k hk N₁ _ h3N hN ν hνpos hν β hβ p₁ hp0 hp₁ Dsc S hS hp
  have hββ₀ : β₀ ≤ β := (le_max_left _ _).trans hβ
  have hββ₁ : β₁ ≤ β := (le_max_right _ _).trans hβ
  have hβ1 : 1 ≤ β := hβ₁.trans hββ₁
  obtain ⟨mObs, H2⟩ := H k hk N₁ h3N hN ν hνpos hν β hββ₀ p₁ hp0 hp₁ Dsc S hS hp
  refine ⟨mObs, fun D hDh hX κroot hκ hc => ?_⟩
  obtain ⟨U, h1, h2, h3', h4, h5, h6⟩ := H2 D hDh hX κroot hκ hc
  refine ⟨U, h1, h2, h3', fun x X g hg => (h4 x X g hg).trans ?_, h5, h6⟩
  have hpref := (hC' L k β hL2 hβ1).2
  have hbirth := hβ₁c β hββ₁
  have hE : 0 ≤ Real.exp (-κroot * (X.card : ℝ) /
      ((L ^ (T.m₁ + 1) * L ^ (k + 1) : ℕ) : ℝ) ^ d) := (Real.exp_pos _).le
  have hP : 0 ≤ (L : ℝ) ^ (-(((k + 1 : ℕ) : ℝ) * (((d : ℝ) - 2) / 2 + δ'))) := by positivity
  have hexp : 0 < Real.exp (3 / 2 * T.κdec) := Real.exp_pos _
  refine mul_le_mul_of_nonneg_right ?_ hE
  calc C * obsPrefactor p s (β * (L : ℝ) ^ (k * (d - 2))) * Real.exp (3 / 2 * T.κdec)
      ≤ C * ((C' * (L : ℝ) ^ (((d : ℝ) - 2) / 2 + δ') *
            β ^ (-((((d : ℝ) - 2) / 2 + δ') / ((d : ℝ) - 2)))) *
          (L : ℝ) ^ (-(((k + 1 : ℕ) : ℝ) * (((d : ℝ) - 2) / 2 + δ')))) *
          Real.exp (3 / 2 * T.κdec) := by
        gcongr
    _ = (C * C' * Real.exp (3 / 2 * T.κdec)) * (L : ℝ) ^ (((d : ℝ) - 2) / 2 + δ') *
          β ^ (-((((d : ℝ) - 2) / 2 + δ') / ((d : ℝ) - 2))) *
          (L : ℝ) ^ (-(((k + 1 : ℕ) : ℝ) * (((d : ℝ) - 2) / 2 + δ'))) := by ring
    _ ≤ c₉ * (L : ℝ) ^ (-(((k + 1 : ℕ) : ℝ) * (((d : ℝ) - 2) / 2 + δ'))) := by
        refine mul_le_mul_of_nonneg_right ?_ hP
        have hβ0 : 0 < β := by linarith
        exact le_trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
          (le_abs_self _) (by positivity)) (by positivity)) hbirth

open Classical in
/-- **The zero-class observable terms with the root's per-term bound at their birth scale.**
For every `c₉ > 0` and `0 < δ' < min s (1/2)` there is a threshold, chosen before the scale, such
that for `β` beyond it the family `U` of `rootTermFamily_obs_prefactor_fromTower` satisfies, on the
half ball, `‖U x X g‖ ≤ c₉ 3^{-(k+1)(1/2+δ')} e^{-κroot |X| / (M 3^{k+1})^3}`
(the root's exponent `(d-2)/2 + δ` with `d = 3`).  The fixed `rootTermFamily_obs_birthScale_fromTower` is its corollary.  The exponent is `(d-2)/2 + δ'` and `δ' < min (s (d-2)) ((d-2)/2)`. -/
theorem rootTermFamily_obs_birthScale_fromTowerG {d L N : ℕ} [NeZero L] {κmin : ℝ}
    (T : StepTowerG d L N κmin) (hm₀ : T.m₀ = 1) {A₁ : ℝ} (hA : 0 < A₁)
    (p : ℕ) {CR s : ℝ} (hCR : 0 < CR) (hs0 : 0 < s) (hs : s < 1 / 2) :
    ∀ c₉ : ℝ, 0 < c₉ → ∀ δ' : ℝ, 0 < δ' → δ' < min (s * ((d : ℝ) - 2)) (((d : ℝ) - 2) / 2) →
    ∃ (β₀ CE CF : ℝ), 3 ≤ β₀ ∧ 0 < CE ∧ 0 < CF ∧
      ∀ (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁] (_h3N : L ^ T.m₀ ∣ N₁), 5 < N₁ →
      ∀ ν : ℝ, 0 < ν → ν * (L : ℝ) ^ (2 * (k + 1)) ≤ 1 → ∀ β : ℝ, β₀ ≤ β →
      ∀ p₁ : ℝ, 0 < p₁ → p₁ ≤ pLog A₁ p (β * (L : ℝ) ^ (k * (d - 2))) →
      ∀ (_ : StepScaleDataG T k hk N₁ ν β p₁)
        (S : StepSetting d L N₁ T.m₁ k N (rhoSepG d L T.m₁)),
        S = T.step k hk N₁ ν β p₁ → ∀ _hp : 0 < S.p₁,
      ∃ (mObs : CTorus d L N₁ T.m₁ (k + 1) → Fin N → physParam N S →
          Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := T.m₁) (K := k + 1) 1 (k + 1)
            Set.univ) → ℂ),
        ∀ (D : BgData S.G' N) (hDh : ∀ y i, D.h y i = (S.h₀ i : ℂ)),
          XiCData S.G' S.a S.ν (k + 1) 1 T.t D →
          ∀ κroot : ℝ, 0 < κroot → c1 d L * κroot ≤ 3 / 2 * T.κdec →
          ∃ U : CTorus d L N₁ T.m₁ (k + 1) → Finset (CTorus d L N₁ T.m₁ (k + 1)) →
              (CTorus d L N₁ T.m₁ (k + 1) → Fin N → ℂ) → (Fin N → ℂ),
            (∀ x X, ¬ (x ∈ X ∧ IsPolymer d ((N₁ * L ^ T.m₁) * L ^ (k + 1))
                (L ^ (T.m₁ + 1) * L ^ (k + 1)) X) → U x X = 0) ∧
            (∀ x X g g', (∀ y ∈ X, g y = g' y) → U x X g = U x X g') ∧
            (∀ x X, AnalyticOnNhd ℂ (U x X)
              {g : CTorus d L N₁ T.m₁ (k + 1) → Fin N → ℂ | ∑ y, ∑ i, ‖g y i‖ < 1}) ∧
            (∀ x X g, ∑ y, ∑ i, ‖g y i‖ ≤ 1 / 2 →
              ‖U x X g‖ ≤ c₉ * (L : ℝ) ^ (-(((k + 1 : ℕ) : ℝ) * (((d : ℝ) - 2) / 2 + δ'))) *
                Real.exp (-κroot * (X.card : ℝ) /
                  ((L ^ (T.m₁ + 1) * L ^ (k + 1) : ℕ) : ℝ) ^ d)) ∧
            (∀ g : CTorus d L N₁ T.m₁ (k + 1) → Fin N → ℂ, ∑ y, ∑ i, ‖g y i‖ < 1 →
              ∀ x i, ∑ X : Finset (CTorus d L N₁ T.m₁ (k + 1)), U x X g i =
                ∑ T', mObs x i ((⟨rawOf D, rawOf_mem_rawSub D⟩ : rawSub N S.G'), g) T') ∧
            ∀ g : CTorus d L N₁ T.m₁ (k + 1) → Fin N → ℂ, ∑ y, ∑ i, ‖g y i‖ < 1 →
              ∑ x, ∑ X : Finset (CTorus d L N₁ T.m₁ (k + 1)), ∑ i, g x i * U x X g i =
                ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
                  ∑ y : CTorus d L N₁ T.m₁ (k + 1), ∑ i : Fin N,
                    g y i * (S.withDatum D hDh).M0C
                      (zeroClass d L N₁ T.m₁ k N (rhoSepG d L T.m₁)) g y i := by
  exact rootTermFamily_obs_birthScale_fromTowerG_rho T hm₀ hA p hCR hs0 hs 1 one_pos

open Classical in
/-- At source radius `ρ` (`q ≤ ρ`, `max 1 ρ ≤ β`); the landed theorem is its `ρ = 1` corollary.  **The zero-class observable terms with the root's per-term bound at their birth scale.**
For every `c₉ > 0` and `0 < δ' < min s (1/2)` there is a threshold, chosen before the scale, such
that for `β` beyond it the family `U` of `rootTermFamily_obs_prefactor_fromTower` satisfies, on the
half ball, `‖U x X g‖ ≤ c₉ 3^{-(k+1)(1/2+δ')} e^{-κroot |X| / (M 3^{k+1})^3}`
(the root's exponent `(d-2)/2 + δ` with `d = 3`). -/
theorem rootTermFamily_obs_birthScale_fromTower_rho {κmin : ℝ} (T : StepTower κmin) {A₁ : ℝ} (hA : 0 < A₁)
    (p : ℕ) {CR s : ℝ} (hCR : 0 < CR) (hs0 : 0 < s) (hs : s < 1 / 2) (ρ : ℝ) (hρ : 0 < ρ) :
    ∀ c₉ : ℝ, 0 < c₉ → ∀ δ' : ℝ, 0 < δ' → δ' < min s (1 / 2) →
    ∃ (β₀ CE CF : ℝ), 3 ≤ β₀ ∧ 0 < CE ∧ 0 < CF ∧
      ∀ (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁] (_h3N : 3 ∣ N₁), 5 < N₁ →
      ∀ ν : ℝ, 0 < ν → ν * 3 ^ (2 * (k + 1)) ≤ 1 → ∀ β : ℝ, β₀ ≤ β →
      ∀ p₁ : ℝ, 0 < p₁ → p₁ ≤ pLog A₁ p (β * 3 ^ k) →
      ∀ (_ : StepScaleData T k hk N₁ ν β p₁)
        (S : StepSetting 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)),
        S = T.step k hk N₁ ν β p₁ → ∀ _hp : 0 < S.p₁,
      ∃ (mObs : CTorus 3 3 N₁ T.m₁ (k + 1) → Fin 2 → physParam 2 S →
          Finset (CubeB (d := 3) (L := 3) (N₁ := N₁) (m₁ := T.m₁) (K := k + 1) 1 (k + 1)
            Set.univ) → ℂ),
        ∀ (D : BgData S.G' 2) (hDh : ∀ y i, D.h y i = (S.h₀ i : ℂ)),
          XiCData S.G' S.a S.ν (k + 1) 1 T.t D →
          ∀ κroot : ℝ, 0 < κroot → c1 3 3 * κroot ≤ 3 / 2 * T.κdec →
          ∃ U : CTorus 3 3 N₁ T.m₁ (k + 1) → Finset (CTorus 3 3 N₁ T.m₁ (k + 1)) →
              (CTorus 3 3 N₁ T.m₁ (k + 1) → Fin 2 → ℂ) → (Fin 2 → ℂ),
            (∀ x X, ¬ (x ∈ X ∧ IsPolymer 3 ((N₁ * 3 ^ T.m₁) * 3 ^ (k + 1))
                (3 ^ (T.m₁ + 1) * 3 ^ (k + 1)) X) → U x X = 0) ∧
            (∀ x X g g', (∀ y ∈ X, g y = g' y) → U x X g = U x X g') ∧
            (∀ x X, AnalyticOnNhd ℂ (U x X)
              {g : CTorus 3 3 N₁ T.m₁ (k + 1) → Fin 2 → ℂ | ∑ y, ∑ i, ‖g y i‖ < ρ}) ∧
            (∀ x X g, ∑ y, ∑ i, ‖g y i‖ ≤ ρ / 2 →
              ‖U x X g‖ ≤ c₉ * (3 : ℝ) ^ (-(((k + 1 : ℕ) : ℝ) * (1 / 2 + δ'))) *
                Real.exp (-κroot * (X.card : ℝ) /
                  ((3 ^ (T.m₁ + 1) * 3 ^ (k + 1) : ℕ) : ℝ) ^ 3)) ∧
            (∀ g : CTorus 3 3 N₁ T.m₁ (k + 1) → Fin 2 → ℂ, ∑ y, ∑ i, ‖g y i‖ < ρ →
              ∀ x i, ∑ X : Finset (CTorus 3 3 N₁ T.m₁ (k + 1)), U x X g i =
                ∑ T', mObs x i ((⟨rawOf D, rawOf_mem_rawSub D⟩ : rawSub 2 S.G'), g) T') ∧
            ∀ g : CTorus 3 3 N₁ T.m₁ (k + 1) → Fin 2 → ℂ, ∑ y, ∑ i, ‖g y i‖ < ρ →
              ∑ x, ∑ X : Finset (CTorus 3 3 N₁ T.m₁ (k + 1)), ∑ i, g x i * U x X g i =
                ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
                  ∑ y : CTorus 3 3 N₁ T.m₁ (k + 1), ∑ i : Fin 2,
                    g y i * (S.withDatum D hDh).M0C
                      (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) g y i := by
  intro c₉ hc₉ δ' hδ0 hδ
  have hδ3 : δ' < min (s * (((3 : ℕ) : ℝ) - 2)) ((((3 : ℕ) : ℝ) - 2) / 2) := by
    norm_num; exact lt_min_iff.1 hδ
  obtain ⟨β₀, CE, CF, h3, hCE, hCF, H⟩ :=
    rootTermFamily_obs_birthScale_fromTowerG_rho T.toG rfl hA p hCR hs0 hs ρ hρ c₉ hc₉ δ' hδ0 hδ3
  refine ⟨β₀, CE, CF, h3, hCE, hCF, ?_⟩
  intro k hk N₁ _ h3N hN ν hνpos hν β hβ p₁ hp0 hp₁ Dsc S hS hp
  have e : (((3 : ℕ) : ℝ)) ^ (k * (3 - 2)) = 3 ^ k := by norm_num
  subst hS
  have hp' : 0 < (T.toG.step k hk N₁ ν β p₁).p₁ := hp
  have G := H k hk N₁ (by simpa using h3N) hN ν hνpos (by simpa using hν) β hβ p₁ hp0
    (by rw [e]; exact hp₁) (StepTower.scaleDataG_of_fixed T Dsc) (T.toG.step k hk N₁ ν β p₁)
    rfl hp'
  unfold StepTowerG.step at G
  revert G
  generalize hb : β * ((3 : ℕ) : ℝ) ^ (k * (3 - 2)) = b
  generalize hϱ : rhoSepG 3 3 T.toG.m₁ = ϱ
  have hϱ' : ϱ = rhoSep T.m₁ := hϱ.symm.trans (rhoSepG_three _)
  have hb' : b = β * 3 ^ k := hb.symm.trans (by rw [e])
  subst hϱ' hb'
  intro G
  simp only [Nat.cast_ofNat] at G
  rw [show ((3 : ℝ) - 2) / 2 + δ' = 1 / 2 + δ' by norm_num] at G
  exact G

open Classical in
/-- **The zero-class observable terms with the root's per-term bound at their birth scale.**
For every `c₉ > 0` and `0 < δ' < min s (1/2)` there is a threshold, chosen before the scale, such
that for `β` beyond it the family `U` of `rootTermFamily_obs_prefactor_fromTower` satisfies, on the
half ball, `‖U x X g‖ ≤ c₉ 3^{-(k+1)(1/2+δ')} e^{-κroot |X| / (M 3^{k+1})^3}`
(the root's exponent `(d-2)/2 + δ` with `d = 3`). -/
theorem rootTermFamily_obs_birthScale_fromTower {κmin : ℝ} (T : StepTower κmin) {A₁ : ℝ} (hA : 0 < A₁)
    (p : ℕ) {CR s : ℝ} (hCR : 0 < CR) (hs0 : 0 < s) (hs : s < 1 / 2) :
    ∀ c₉ : ℝ, 0 < c₉ → ∀ δ' : ℝ, 0 < δ' → δ' < min s (1 / 2) →
    ∃ (β₀ CE CF : ℝ), 3 ≤ β₀ ∧ 0 < CE ∧ 0 < CF ∧
      ∀ (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁] (_h3N : 3 ∣ N₁), 5 < N₁ →
      ∀ ν : ℝ, 0 < ν → ν * 3 ^ (2 * (k + 1)) ≤ 1 → ∀ β : ℝ, β₀ ≤ β →
      ∀ p₁ : ℝ, 0 < p₁ → p₁ ≤ pLog A₁ p (β * 3 ^ k) →
      ∀ (_ : StepScaleData T k hk N₁ ν β p₁)
        (S : StepSetting 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)),
        S = T.step k hk N₁ ν β p₁ → ∀ _hp : 0 < S.p₁,
      ∃ (mObs : CTorus 3 3 N₁ T.m₁ (k + 1) → Fin 2 → physParam 2 S →
          Finset (CubeB (d := 3) (L := 3) (N₁ := N₁) (m₁ := T.m₁) (K := k + 1) 1 (k + 1)
            Set.univ) → ℂ),
        ∀ (D : BgData S.G' 2) (hDh : ∀ y i, D.h y i = (S.h₀ i : ℂ)),
          XiCData S.G' S.a S.ν (k + 1) 1 T.t D →
          ∀ κroot : ℝ, 0 < κroot → c1 3 3 * κroot ≤ 3 / 2 * T.κdec →
          ∃ U : CTorus 3 3 N₁ T.m₁ (k + 1) → Finset (CTorus 3 3 N₁ T.m₁ (k + 1)) →
              (CTorus 3 3 N₁ T.m₁ (k + 1) → Fin 2 → ℂ) → (Fin 2 → ℂ),
            (∀ x X, ¬ (x ∈ X ∧ IsPolymer 3 ((N₁ * 3 ^ T.m₁) * 3 ^ (k + 1))
                (3 ^ (T.m₁ + 1) * 3 ^ (k + 1)) X) → U x X = 0) ∧
            (∀ x X g g', (∀ y ∈ X, g y = g' y) → U x X g = U x X g') ∧
            (∀ x X, AnalyticOnNhd ℂ (U x X)
              {g : CTorus 3 3 N₁ T.m₁ (k + 1) → Fin 2 → ℂ | ∑ y, ∑ i, ‖g y i‖ < 1}) ∧
            (∀ x X g, ∑ y, ∑ i, ‖g y i‖ ≤ 1 / 2 →
              ‖U x X g‖ ≤ c₉ * (3 : ℝ) ^ (-(((k + 1 : ℕ) : ℝ) * (1 / 2 + δ'))) *
                Real.exp (-κroot * (X.card : ℝ) /
                  ((3 ^ (T.m₁ + 1) * 3 ^ (k + 1) : ℕ) : ℝ) ^ 3)) ∧
            (∀ g : CTorus 3 3 N₁ T.m₁ (k + 1) → Fin 2 → ℂ, ∑ y, ∑ i, ‖g y i‖ < 1 →
              ∀ x i, ∑ X : Finset (CTorus 3 3 N₁ T.m₁ (k + 1)), U x X g i =
                ∑ T', mObs x i ((⟨rawOf D, rawOf_mem_rawSub D⟩ : rawSub 2 S.G'), g) T') ∧
            ∀ g : CTorus 3 3 N₁ T.m₁ (k + 1) → Fin 2 → ℂ, ∑ y, ∑ i, ‖g y i‖ < 1 →
              ∑ x, ∑ X : Finset (CTorus 3 3 N₁ T.m₁ (k + 1)), ∑ i, g x i * U x X g i =
                ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
                  ∑ y : CTorus 3 3 N₁ T.m₁ (k + 1), ∑ i : Fin 2,
                    g y i * (S.withDatum D hDh).M0C
                      (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) g y i := by
  exact rootTermFamily_obs_birthScale_fromTower_rho T hA p hCR hs0 hs 1 one_pos

end Balaban.Inhabited
