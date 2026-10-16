/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Base.BaseConstrainedCov
public import Balaban.Fluctuation.FlCoreCover
public import Balaban.Fluctuation.LocalPairDecBg

/-!
# The decoupled background at the first step: analyticity and localization

The cover forms of Theorem I-4b (`Dec2.i4b_analytic`, `coverBg_exists`, `Dec2.decBg_value_cross`)
are stated for a generating set at any level `K`, and none of their hypotheses reads `1 ≤ k`.
At the first step (`K = 1`) they apply to

* the whole-torus generating set of `baseDGSetting_exists`, with its self cover
  (`Dec2.coverBase_self`), and
* the literal local generating set `localB 1 _ Y` at the separation `5 L M₁`, with the cover
  base `localB_coverData`.

This file records these two instances: existence, uniqueness and bounds of the decoupled
background `(φ, α)` of a datum of the chart `Ξ^c_1`, analyticity of `(s, Θ) ↦ (φ, α)` on the
H7 domain `|s_P| < e^κ`, and the exact agreement of the multipliers on `T` and the fields on `Y`
for two local generating sets (the localization).
-/

@[expose] public section

namespace Balaban.LargeField.Base

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Localization

section Whole

variable {d L N₁ m₁ N : ℕ} [NeZero L] [NeZero N₁]

/-- **Analyticity of the decoupled background on the whole torus at the first step.**  For the
whole-torus generating set `G` of `baseDGSetting_exists` (weights `compWeight L 1`, `ϱ = rhoSepG`),
there is one function of the parameters `s` and the raw data, analytic on the H7 domain
`|s_P| < e^κ`, data in the union domain, which returns every decoupled background field. -/
theorem baseBackground_analytic_whole (hd : 3 ≤ d) (hL : 3 ≤ L) (hM : 4 * L ^ 2 ≤ L ^ m₁)
    (hN₁ : 5 < N₁) {ν : ℝ} (hν0 : 0 ≤ ν) (hν : ν * (L : ℝ) ^ 2 ≤ 1) {c BG : ℝ}
    (hS : Dec2.DecSpecs d L (Dec2.selfKc d L) (Cchi d L) c BG) {κ : ℝ} (hκ : 0 ≤ κ)
    (hMκ : c * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) :
    ∃ G : GeneratingSet d L (N₁ * L ^ m₁) 1 (Inhabited.LevelStep.rhoSepG d L m₁),
      G.Ω 1 = Finset.univ ∧
      ∃ F : Dec2.DecParams (coverOf G) × RawData d L (N₁ * L ^ m₁) 1 N →
          (G.Ω 1 × Fin N → ℂ) × (G.Ω 1 → ℂ),
        AnalyticOnNhd ℂ F {q | (∀ P, ‖q.1 P‖ < Real.exp κ) ∧ ∃ D : BgData G N,
          InUnionDomainC G (bgC0 d L N) (c7 d L N BG κ) ν D ∧ q.2 = (D.Ψ, D.h)} ∧
        ∀ (s : Dec2.DecParams (coverOf G)) (D : BgData G N), (∀ P, ‖s P‖ < Real.exp κ) →
          InUnionDomainC G (bgC0 d L N) (c7 d L N BG κ) ν D →
          ∀ (φ : G.Ω 1 × Fin N → ℂ) (α : G.Ω 1 → ℂ),
            Dec2.IsDecBg (coverOf G) G (compWeight L 1) ν (rho4 d L N BG κ) s D φ α →
              F (s, (D.Ψ, D.h)) = (φ, α) := by
  obtain ⟨G, hG, S⟩ := baseDGSetting_exists (m₁ := m₁) hd hL hM hN₁ hν0 hν
  refine ⟨G, hG, ?_⟩
  have HB : BgHyp d L 1 (Inhabited.LevelStep.rhoSepG d L m₁) (compWeight L 1) ν :=
    Inhabited.LevelStep.bgHyp_lvG (k := 0) hd hL
      (Inhabited.LevelStep.bgR0_le_rhoSepG m₁ hd hL) hν0 (by simpa using hν)
  exact Dec2.i4b_analytic hS (Dec2.coverBase_self S) HB hκ hMκ

end Whole

section Local

variable {d L N₁ m₁ N : ℕ} [NeZero L] [NeZero N₁]

/-- **Analyticity of the decoupled background for the local generating set at the first step.**
For `𝔹 = localB 1 _ Y` (level `K = 1`, separation `5 L M₁`), the decoupled background field of
`(coverOf 𝔹, 𝔹)` is given on the H7 domain by one analytic function of `(s, Θ)`. -/
theorem baseBackground_analytic_localB (Y : Set (Balaban.Localization.CTorus d L N₁ m₁ 1)) (hN₁ : 5 < N₁)
    (hMM : 4 * L ^ 2 ≤ L ^ m₁)
    (hag : 2 * d * Real.log L ≤ agmonRate d / 16 * (minSep L (L ^ m₁) - 1)) {a : ℕ → ℝ} {ν : ℝ}
    {c BG : ℝ} (hS : Dec2.DecSpecs d L (Dec2.mixedKc d L) (Cchi d L) c BG)
    (HBp : BgHyp d L 1 (minSep L (L ^ m₁)) a ν) {κ : ℝ} (hκ : 0 ≤ κ)
    (hM : c * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) :
    ∃ F : Dec2.DecParams (coverOf (GsSpec.localB 1 le_rfl Y (le_refl (minSep L (L ^ m₁))))) ×
        RawData d L (N₁ * L ^ m₁) 1 N →
        ((GsSpec.localB 1 le_rfl Y (le_refl (minSep L (L ^ m₁)))).Ω 1 × Fin N → ℂ) ×
          ((GsSpec.localB 1 le_rfl Y (le_refl (minSep L (L ^ m₁)))).Ω 1 → ℂ),
      AnalyticOnNhd ℂ F {q | (∀ P, ‖q.1 P‖ < Real.exp κ) ∧
        ∃ D : BgData (GsSpec.localB 1 le_rfl Y (le_refl (minSep L (L ^ m₁)))) N,
          InUnionDomainC (GsSpec.localB 1 le_rfl Y (le_refl (minSep L (L ^ m₁)))) (bgC0 d L N)
            (c7 d L N BG κ) ν D ∧ q.2 = (D.Ψ, D.h)} ∧
      ∀ (s : Dec2.DecParams (coverOf (GsSpec.localB 1 le_rfl Y (le_refl (minSep L (L ^ m₁))))))
        (D : BgData (GsSpec.localB 1 le_rfl Y (le_refl (minSep L (L ^ m₁)))) N),
        (∀ P, ‖s P‖ < Real.exp κ) →
        InUnionDomainC (GsSpec.localB 1 le_rfl Y (le_refl (minSep L (L ^ m₁)))) (bgC0 d L N)
          (c7 d L N BG κ) ν D →
        ∀ (φ : (GsSpec.localB 1 le_rfl Y (le_refl (minSep L (L ^ m₁)))).Ω 1 × Fin N → ℂ)
          (α : (GsSpec.localB 1 le_rfl Y (le_refl (minSep L (L ^ m₁)))).Ω 1 → ℂ),
          Dec2.IsDecBg (coverOf (GsSpec.localB 1 le_rfl Y (le_refl (minSep L (L ^ m₁)))))
            (GsSpec.localB 1 le_rfl Y (le_refl (minSep L (L ^ m₁)))) a ν (rho4 d L N BG κ) s D φ α →
              F (s, (D.Ψ, D.h)) = (φ, α) :=
  Dec2.i4b_analytic hS (localB_coverData le_rfl Y hN₁ hMM hag HBp).1 HBp hκ hM

open Classical in
/-- **Existence, uniqueness and bounds of the decoupled background for the local generating set
at the first step** (`coverBg_exists` at `K = 1`, `𝔹 = localB 1 _ Y`). -/
theorem baseBackground_exists_localB (Y : Set (Balaban.Localization.CTorus d L N₁ m₁ 1))
    (hN₁ : 5 < N₁) (hMM : 4 * L ^ 2 ≤ L ^ m₁)
    (hag : 2 * d * Real.log L ≤ agmonRate d / 16 * (minSep L (L ^ m₁) - 1)) {a₁ ν : ℝ}
    {c BG : ℝ} (hS : Dec2.DecSpecs d L (Dec2.mixedKc d L) (Cchi d L) c BG)
    (HBp : BgHyp d L 1 (minSep L (L ^ m₁)) (compWeight L a₁) ν) {κ eps : ℝ} (hκ : 0 ≤ κ)
    (hM : c * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) (heps : 0 < eps)
    (hsmall : (4 * d + 6) * ((2 * d + 1) * eps) ≤ 1) (hc7 : xiC1 d * eps ≤ c7 d L N BG κ)
    {s : Dec2.DecParams (coverOf (GsSpec.localB 1 le_rfl Y (le_refl (minSep L (L ^ m₁)))))}
    (hs : ∀ P, ‖s P‖ < Real.exp κ)
    {D : BgData (GsSpec.localB 1 le_rfl Y (le_refl (minSep L (L ^ m₁)))) N}
    (hD : XiCData (GsSpec.localB 1 le_rfl Y (le_refl (minSep L (L ^ m₁)))) (compWeight L a₁) ν 1
      1 eps D) :
    ∃ (φ : (GsSpec.localB 1 le_rfl Y (le_refl (minSep L (L ^ m₁)))).Ω 1 × Fin N → ℂ)
      (α : (GsSpec.localB 1 le_rfl Y (le_refl (minSep L (L ^ m₁)))).Ω 1 → ℂ),
      IsDecBg
        (GsSpec.localB 1 le_rfl Y (le_refl (minSep L (L ^ m₁)))) (compWeight L a₁) ν
        (rho4 d L N BG κ) s D φ α ∧
      (∀ φ' α', IsDecBg
        (GsSpec.localB 1 le_rfl Y (le_refl (minSep L (L ^ m₁)))) (compWeight L a₁) ν
        (rho4 d L N BG κ) s D φ' α' → φ' = φ ∧ α' = α) ∧
      BgBounds (GsSpec.localB 1 le_rfl Y (le_refl (minSep L (L ^ m₁)))) D φ α
        (K4 d L N BG κ * (xiC1 d * eps)) :=
  coverBg_exists hS (localB_coverData le_rfl Y hN₁ hMM hag HBp).1 HBp hκ hM heps hsmall hc7 hs hD

/-- **Localization of the decoupled background at the first step.**  Let `H`, `H'` be two local
generating sets `localB 1 _ Y`, `localB 1 _ Y'` at the separation `5 L M₁`, and `F₁`, `F₁'` maps
with the defining property of the decoupled background of the two pairs on the H7 domain.  Under
the hypotheses of `Dec2.decBg_value_cross` (dichotomy, row, inner-cube and layer conditions on
`T ⊆ Y`, raw data agreeing on `approxDep`), the multipliers agree on `T` and the fields agree
on `Y`. -/
theorem baseBackground_value_cross_localB {Y₀ Y₀' : Set (Balaban.Localization.CTorus d L N₁ m₁ 1)}
    {H H' : GeneratingSet d L (N₁ * L ^ m₁) 1 (minSep L (L ^ m₁))}
    (hH : H = GsSpec.localB 1 le_rfl Y₀ (le_refl (minSep L (L ^ m₁))))
    (hH' : H' = GsSpec.localB 1 le_rfl Y₀' (le_refl (minSep L (L ^ m₁))))
    (hN₁ : 5 < N₁) (hMM : 4 * L ^ 2 ≤ L ^ m₁)
    (hag : 2 * d * Real.log L ≤ agmonRate d / 16 * (minSep L (L ^ m₁) - 1)) {a : ℕ → ℝ} {ν : ℝ}
    {c BG : ℝ} (hS : Dec2.DecSpecs d L (Dec2.mixedKc d L) (Cchi d L) c BG)
    (HBp : BgHyp d L 1 (minSep L (L ^ m₁)) a ν) {κ : ℝ} (hκ : 0 ≤ κ)
    (hM : c * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    {F₁ : Dec2.DecParams (coverOf H) × RawData d L (N₁ * L ^ m₁) 1 N →
      (H.Ω 1 × Fin N → ℂ) × (H.Ω 1 → ℂ)}
    {F₁' : Dec2.DecParams (coverOf H') × RawData d L (N₁ * L ^ m₁) 1 N →
      (H'.Ω 1 × Fin N → ℂ) × (H'.Ω 1 → ℂ)}
    (hF₁ : ∀ (s : Dec2.DecParams (coverOf H)) (D : BgData H N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC H (bgC0 d L N) (c7 d L N BG κ) ν D → ∀ (φ : H.Ω 1 × Fin N → ℂ)
        (α : H.Ω 1 → ℂ), Dec2.IsDecBg (coverOf H) H a ν (rho4 d L N BG κ) s D φ α →
          F₁ (s, rawOf D) = (φ, α))
    (hF₁' : ∀ (s : Dec2.DecParams (coverOf H')) (D : BgData H' N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC H' (bgC0 d L N) (c7 d L N BG κ) ν D → ∀ (φ : H'.Ω 1 × Fin N → ℂ)
        (α : H'.Ω 1 → ℂ), Dec2.IsDecBg (coverOf H') H' a ν (rho4 d L N BG κ) s D φ α →
          F₁' (s, rawOf D) = (φ, α))
    {s : Dec2.DecParams (coverOf H)} {s' : Dec2.DecParams (coverOf H')}
    (hs : ∀ P, ‖s P‖ < Real.exp κ) (hs' : ∀ P, ‖s' P‖ < Real.exp κ)
    {D : BgData H N} {D' : BgData H' N}
    (hDd : InUnionDomainC H (bgC0 d L N) (c7 d L N BG κ) ν D)
    (hDd' : InUnionDomainC H' (bgC0 d L N) (c7 d L N BG κ) ν D')
    {Y T : Finset (Balaban.Localization.CTorus d L N₁ m₁ 1)} (hTY : T ⊆ Y)
    (hYlay : ∀ y ∈ Y, ∀ n, 1 ≤ n → n ≤ 1 → (y ∈ H.layer n ↔ y ∈ H'.layer n))
    (hdich : ∀ q ∈ (coverOf H).cubeIdx, (coverOf H).sProd (Dec2.extS (coverOf H) s) q ≠ 0 →
      SubI H (intBox q) T ∨ DisjI H (intBox q) T)
    (hdich' : ∀ q ∈ (coverOf H').cubeIdx, (coverOf H').sProd (Dec2.extS (coverOf H') s') q ≠ 0 →
      SubI H' (intBox q) T ∨ DisjI H' (intBox q) T)
    (hrow : ∀ q ∈ (coverOf H).cubeIdx, (coverOf H).sProd (Dec2.extS (coverOf H) s) q ≠ 0 →
      ∀ x ∈ Y, x ∈ intBox q → x ∈ T)
    (hrow' : ∀ q ∈ (coverOf H').cubeIdx, (coverOf H').sProd (Dec2.extS (coverOf H') s') q ≠ 0 →
      ∀ x ∈ Y, x ∈ intBox q → x ∈ T)
    (hin : ∀ q ∈ Dec2.innerCentres (coverOf H) H T,
      (coverOf H).sProd (Dec2.extS (coverOf H) s) q ≠ 0 →
      q ∈ Dec2.innerCentres (coverOf H') H' T ∧
      (coverOf H').sProd (Dec2.extS (coverOf H') s') q =
        (coverOf H).sProd (Dec2.extS (coverOf H) s) q ∧
      (∀ x ∈ intBox q, ∀ y : Balaban.Localization.CTorus d L N₁ m₁ 1,
        (y = x ∨ ∃ μ : Fin d, y = x + Pi.single μ 1 ∨ y = x - Pi.single μ 1) →
          ∀ n, 1 ≤ n → n ≤ 1 → (y ∈ H.layer n ↔ y ∈ H'.layer n)) ∧
      (∀ x ∈ intBox q, (coverOf H).chi q x = (coverOf H').chi q x))
    (hin' : ∀ q ∈ Dec2.innerCentres (coverOf H') H' T,
      (coverOf H').sProd (Dec2.extS (coverOf H') s') q ≠ 0 →
      q ∈ Dec2.innerCentres (coverOf H) H T ∧
        (coverOf H).sProd (Dec2.extS (coverOf H) s) q ≠ 0)
    (hres : ∀ x ∈ T, x ∈ H.Ω 1 → ∀ y ∈ resSites H x, y ∈ H.Ω 1 ∧ y ∈ Y)
    (hact : ∀ y ∈ Y, y ∈ H.Ω 1 → ∀ q : ℕ × Balaban.Localization.CTorus d L N₁ m₁ 1, 1 ≤ q.1 →
      q.1 ≤ 1 → bump q.1 q.2 y ≠ 0 → ∀ n, 1 ≤ n → n ≤ 1 →
        (q.2 ∈ H.layer n ↔ q.2 ∈ H'.layer n))
    (hdat : ∀ y ∈ Y, y ∈ H.Ω 1 → ∀ z ∈ approxDep H y, D.Ψ z = D'.Ψ z ∧ D.h z = D'.h z) :
    (∀ (x : Balaban.Localization.CTorus d L N₁ m₁ 1) (hx : x ∈ H.Ω 1) (hx' : x ∈ H'.Ω 1),
      x ∈ T → (F₁' (s', rawOf D')).2 ⟨x, hx'⟩ = (F₁ (s, rawOf D)).2 ⟨x, hx⟩) ∧
    (∀ (y : Balaban.Localization.CTorus d L N₁ m₁ 1) (hy : y ∈ H.Ω 1) (hy' : y ∈ H'.Ω 1),
      y ∈ Y → ∀ i : Fin N,
        (F₁' (s', rawOf D')).1 (⟨y, hy'⟩, i) = (F₁ (s, rawOf D)).1 (⟨y, hy⟩, i)) := by
  have S : Dec2.CoverBase (coverOf H) H a ν (Dec2.mixedKc d L) (Cchi d L) := by
    subst hH; exact (localB_coverData le_rfl Y₀ hN₁ hMM hag HBp).1
  have S' : Dec2.CoverBase (coverOf H') H' a ν (Dec2.mixedKc d L) (Cchi d L) := by
    subst hH'; exact (localB_coverData le_rfl Y₀' hN₁ hMM hag HBp).1
  exact Dec2.decBg_value_cross hS S S' HBp HBp hκ hM hF₁ hF₁' hs hs' hDd hDd' hTY hYlay hdich
    hdich' hrow hrow' hin hin' hres hact hdat

end Local

end Balaban.LargeField.Base
