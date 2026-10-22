/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Base.BaseLocalSpec
public import Balaban.LargeField.Base.BaseLabelCross
public import Balaban.LargeField.Base.BaseChartLabelAct

/-!
# The coefficients of the chart exponent on a generating set, at the pairs with a deep label

For a generating set `G` of the first step (not necessarily with `Ω₁` the whole torus), a pair `(x, Cs)`
whose label `Y` lies in a set `R` with `8 L^{1+m₁}`-neighbourhood in `Ω₁`: the coefficient `coef_{Cs}` of
`s ↦ V_x(F(s,e); ψ)` vanishes unless `Cs` is rooted at the ball of radius `ρ + L` about `x`, and is bounded by
`2 B_V e^{-(κ-1)|Cs|}` (`chartPair_spec_deep`, from `bgFunctional_pair_spec` and the depth of the seed hull
`hdeep_of_cells`).
-/

@[expose] public section

namespace Balaban.LargeField.Base

open Balaban Balaban.Multiscale Balaban.Localization Balaban.Background Balaban.Fluctuation
  Balaban.LargeField Balaban.SmallField Balaban.SmallField.Def6 Balaban.Green Balaban.Analysis
  Balaban.Polymer Matrix

section Spec

variable {d L N₁ m₁ N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}

open Classical in
/-- **The spec of a pair with a deep label.** -/
theorem chartPair_spec_deep {Kc Cx c BG : ℝ} (hS : Dec2.DecSpecs d L Kc Cx c BG)
    (G : GeneratingSet d L (N₁ * L ^ m₁) 1 ϱ) (a : ℕ → ℝ) (ν β : ℝ) (hβ : 0 < β)
    (Sb : Dec2.CoverBase (coverOf G) G a ν Kc Cx) (HB : BgHyp d L 1 ϱ a ν) {κ : ℝ}
    (hκ : 1 ≤ κ) (hM : c * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    {F : Dec2.DecParams (coverOf G) × RawData d L (N₁ * L ^ m₁) 1 N →
      (G.Ω 1 × Fin N → ℂ) × (G.Ω 1 → ℂ)}
    (hF : ∀ (s : Dec2.DecParams (coverOf G)) (D : BgData G N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC G (bgC0 d L N) (c7 d L N BG κ) ν D → ∀ (φ : G.Ω 1 × Fin N → ℂ)
        (α : G.Ω 1 → ℂ), Dec2.IsDecBg (coverOf G) G a ν (rho4 d L N BG κ) s D φ α →
          F (s, (D.Ψ, D.h)) = (φ, α))
    {Dd : BgData G N} (hDu : InUnionDomainC G (bgC0 d L N) (c7 d L N BG κ) ν Dd)
    (hFan : AnalyticOnNhd ℂ F {q | (∀ P, ‖q.1 P‖ < Real.exp κ) ∧
      ∃ D : BgData G N, InUnionDomainC G (bgC0 d L N) (c7 d L N BG κ) ν D ∧ q.2 = (D.Ψ, D.h)})
    {Dr : ℕ} (hDD : L ^ 1 + 2 * L ^ 1 ≤ Dr)
    (g ψ : G.Ω 1 × Fin N → ℂ) (x : G.Ω 1) (ρ : ℕ)
    (W : ((G.Ω 1 × Fin N → ℂ) × (G.Ω 1 → ℂ)) → Matrix (G.Ω 1 × Fin N) (G.Ω 1 × Fin N) ℂ)
    (hWloc : ∀ (u u' : (G.Ω 1 × Fin N → ℂ) × (G.Ω 1 → ℂ)) (p : G.Ω 1 × Fin N),
      (∀ y' : G.Ω 1, supDist (p.1 : Balaban.Localization.CTorus d L N₁ m₁ 1) y' ≤ ρ →
        (∀ i, u.1 (y', i) = u'.1 (y', i)) ∧ u.2 y' = u'.2 y') → ∀ r, W u p r = W u' p r)
    {U : Set ((G.Ω 1 × Fin N → ℂ) × (G.Ω 1 → ℂ))}
    (hWan : ∀ p r, AnalyticOnNhd ℂ (fun u => W u p r) U) {Ee BW p₁ Aα Gg : ℝ} (hE : 0 ≤ Ee)
    (hBW : 0 ≤ BW) (hp : 0 ≤ p₁)
    (hU : ∀ u ∈ U, (∀ y i, ‖u.1 (y, i)‖ ≤ Ee) ∧ (∀ p, ∑ r, ‖W u p r‖ ≤ BW) ∧ ‖u.2 x‖ ≤ Aα)
    (hψ : ∀ r, ‖ψ r‖ ≤ p₁) (hg : ∑ i, ‖g (x, i)‖ ≤ Gg)
    (hsmall : (N : ℝ) * ((1 + N * Ee ^ 2) * BW * p₁) ^ 2 / β ≤ 1 / 4)
    (hmem : ∀ s : Dec2.DecParams (coverOf G), (∀ P, ‖s P‖ < Real.exp κ) →
      F (s, (Dd.Ψ, Dd.h)) ∈ U)
    (Cs : Finset ↥(coverOf G).cubeIdx)
    (hdeep : ∀ s ∈ supportedOn Cs, ∀ y ∈ seedHull (coverOf G) Dr (Dec2.extS _ s)
        (seedBall (x : Balaban.Localization.CTorus d L N₁ m₁ 1) (ρ + L)),
      ∀ z : Balaban.Localization.CTorus d L N₁ m₁ (0 + 1), supDist y z ≤ 2 * L ^ (0 + 1) → z ∈ G.Ω 1) :
    (¬ IsRootedFamily (cellPatch (coverOf G) Dr)
        (seedBall (x : Balaban.Localization.CTorus d L N₁ m₁ 1) (ρ + L) : Set _) Cs →
      coef (fun s => chartFe G a ν β g ψ W x (F (s, (Dd.Ψ, Dd.h)))) Cs = 0) ∧
    ‖coef (fun s => chartFe G a ν β g ψ W x (F (s, (Dd.Ψ, Dd.h)))) Cs‖ ≤
      2 * chartBound d L N (a 1) ν β Aα Ee BW p₁ Gg * Real.exp (-(κ - 1) * Cs.card) := by
  obtain ⟨hFeU, hFeB⟩ := chartFunctional_bound G a ν β hβ g ψ x W hWan hE hBW hp hU hψ hg hsmall
  exact bgFunctional_pair_spec G a ν hS Sb HB hκ hM hF hDu hFan hDD
    (chartSite_readsSeed G a ν β g ψ x ρ W hWloc) hFeU hFeB hmem Cs hdeep

end Spec

end Balaban.LargeField.Base
