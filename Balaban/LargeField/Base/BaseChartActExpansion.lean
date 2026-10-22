/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Base.BaseChartActReads
public import Balaban.LargeField.Base.BaseChartActBound
public import Balaban.LargeField.Base.BaseHessianRows
public import Balaban.LargeField.Base.BaseBgFunctional

/-!
# The chart activity as a bounded analytic functional of the decoupled background

For a whitening family `W(φ, α)` with entries analytic in `(φ, α)` on a set `U`, the functional
`Fe (φ, α) = V_x (φ, α, W(φ, α) ψ')` is analytic on `U` and bounded by the explicit expression of
`norm_chartSite_whitened_le` as soon as, on `U`, the background components are `≤ E_e`, the rows of
`W` have `ℓ¹` norm `≤ B_W`, `|α_x| ≤ A_α`, and the smallness condition `N m² / β ≤ 1/4` holds
(`chartFunctional_analytic_bdd`).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField.Base

open Balaban Balaban.Multiscale Balaban.Localization Matrix

section Expansion

variable {d L N₁ m₁ N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}

theorem mem_slitPlane_of_norm_le {t : ℂ} (h : ‖t‖ ≤ 1 / 4) : 1 - t ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]
  left
  have h1 : |t.re| ≤ ‖t‖ := Complex.abs_re_le_norm t
  have h2 := le_abs_self t.re
  simp only [Complex.sub_re, Complex.one_re]
  linarith

/-- **The factor `t_y` of the chart is `≤ 1/4`** for a background `e` with entries `≤ E_e`, a whitening
matrix with `ℓ¹` rows `≤ B_W` and a field `≤ p₁`, under the smallness condition. -/
theorem chartT_whitened_le {ι : Type*} [Fintype ι] [DecidableEq ι] {β : ℝ} (hβ : 0 < β) {e : ι → Fin N → ℂ}
    {M : Matrix (ι × Fin N) (ι × Fin N) ℂ} {ψ : ι × Fin N → ℂ} {Ee BW p₁ : ℝ} (hE : 0 ≤ Ee)
    (he : ∀ y i, ‖e y i‖ ≤ Ee) (hW : ∀ p, ∑ r, ‖M p r‖ ≤ BW) (hψ : ∀ r, ‖ψ r‖ ≤ p₁)
    (hsmall : (N : ℝ) * ((1 + N * Ee ^ 2) * BW * p₁) ^ 2 / β ≤ 1 / 4) (y : ι) :
    ‖chartT β (chartTangent e (M *ᵥ ψ)) y‖ ≤ 1 / 4 := by
  have hv : ∀ i, ‖chartTangent e (M *ᵥ ψ) (y, i)‖ ≤ (1 + N * Ee ^ 2) * BW * p₁ := by
    intro i
    have hw : ∀ y i, ‖(M *ᵥ ψ) (y, i)‖ ≤ BW * p₁ := fun y i => norm_mulVec_le hW hψ (y, i)
    have := norm_chartTangent_le (e := e) hE he hw y i
    simpa [mul_assoc] using this
  exact (norm_chartT_le hβ y hv).trans hsmall

/-- **The chart functional is analytic and bounded on `U`.** -/
theorem chartFunctional_analytic_bdd (G : GeneratingSet d L (N₁ * L ^ m₁) 1 ϱ) (a : ℕ → ℝ)
    (ν β : ℝ) (hβ : 0 < β) (g ψ : G.Ω 1 × Fin N → ℂ) (x : G.Ω 1)
    (W : ((G.Ω 1 × Fin N → ℂ) × (G.Ω 1 → ℂ)) → Matrix (G.Ω 1 × Fin N) (G.Ω 1 × Fin N) ℂ)
    {U : Set ((G.Ω 1 × Fin N → ℂ) × (G.Ω 1 → ℂ))}
    (hWan : ∀ p r, AnalyticOnNhd ℂ (fun u => W u p r) U) {Ee BW p₁ Aα Gg : ℝ} (hE : 0 ≤ Ee)
    (hBW : 0 ≤ BW) (hp : 0 ≤ p₁)
    (hU : ∀ u ∈ U, (∀ y i, ‖u.1 (y, i)‖ ≤ Ee) ∧ (∀ p, ∑ r, ‖W u p r‖ ≤ BW) ∧ ‖u.2 x‖ ≤ Aα)
    (hψ : ∀ r, ‖ψ r‖ ≤ p₁) (hg : ∑ i, ‖g (x, i)‖ ≤ Gg)
    (hsmall : (N : ℝ) * ((1 + N * Ee ^ 2) * BW * p₁) ^ 2 / β ≤ 1 / 4) :
    AnalyticOnNhd ℂ (fun u => chartSite β (fun y i => u.1 (y, i))
        (baseHamiltonian G a ν u.2 (fun _ => 1)) g (W u *ᵥ ψ) x) U ∧
      ∀ u ∈ U, ‖chartSite β (fun y i => u.1 (y, i)) (baseHamiltonian G a ν u.2 (fun _ => 1)) g
          (W u *ᵥ ψ) x‖ ≤
        (4 * d + |ν| + |a 1| / (L : ℝ) ^ 2 + Aα) * (N * (((1 + N * Ee ^ 2) * BW * p₁) *
          (Real.sqrt β * (3 / 2 * ((N : ℝ) * ((1 + N * Ee ^ 2) * BW * p₁) ^ 2 / β)) * Ee))) +
        1 / 2 * ((4 * d + |ν| + |a 1| / (L : ℝ) ^ 2 + Aα) * (N *
          ((Real.sqrt β * (3 / 2 * ((N : ℝ) * ((1 + N * Ee ^ 2) * BW * p₁) ^ 2 / β)) * Ee) *
          (Real.sqrt β * (3 / 2 * ((N : ℝ) * ((1 + N * Ee ^ 2) * BW * p₁) ^ 2 / β)) * Ee)))) +
        1 / 2 * (3 / 2 * ((N : ℝ) * ((1 + N * Ee ^ 2) * BW * p₁) ^ 2 / β)) +
        (Real.sqrt β)⁻¹ * (Gg * (((1 + N * Ee ^ 2) * BW * p₁) + Real.sqrt β *
          (3 / 2 * ((N : ℝ) * ((1 + N * Ee ^ 2) * BW * p₁) ^ 2 / β)) * Ee)) := by
  classical
  have hτ2 : (N : ℝ) * ((1 + N * Ee ^ 2) * BW * p₁) ^ 2 / β ≤ 1 / 2 := by linarith
  have hT : ∀ u ∈ U, ∀ y, ‖chartT β (chartTangent (fun y i => u.1 (y, i)) (W u *ᵥ ψ)) y‖ ≤ 1 / 4 :=
    fun u hu y => chartT_whitened_le hβ hE (fun y i => (hU u hu).1 y i) (hU u hu).2.1 hψ hsmall y
  refine ⟨fun u hu => ?_, fun u hu => ?_⟩
  · -- analyticity
    have hcoord : ∀ y i, AnalyticAt ℂ (fun q : (G.Ω 1 × Fin N → ℂ) × (G.Ω 1 → ℂ) => q.1 (y, i)) u := by
      intro y i
      fun_prop
    have hH : ∀ y z, AnalyticAt ℂ (fun q : (G.Ω 1 × Fin N → ℂ) × (G.Ω 1 → ℂ) =>
        baseHamiltonian G a ν q.2 (fun _ => 1) y z) u := by
      intro y z
      have hq : (fun q : (G.Ω 1 × Fin N → ℂ) × (G.Ω 1 → ℂ) =>
          baseHamiltonian G a ν q.2 (fun _ => 1) y z) =
          fun q => baseHamiltonian G a ν 0 (fun _ => 1) y z + (if y = z then q.2 y else 0) :=
        funext fun q => baseHamiltonian_apply_diag G a ν _ _ y z
      rw [hq]
      refine analyticAt_const.add ?_
      by_cases h : y = z
      · have : (fun q : (G.Ω 1 × Fin N → ℂ) × (G.Ω 1 → ℂ) => if y = z then q.2 y else (0 : ℂ)) =
            fun q => q.2 y := funext fun q => by simp [h]
        rw [this]
        fun_prop
      · have : (fun q : (G.Ω 1 × Fin N → ℂ) × (G.Ω 1 → ℂ) => if y = z then q.2 y else (0 : ℂ)) =
            fun _ => 0 := funext fun q => by simp [h]
        rw [this]
        exact analyticAt_const
    exact analyticAt_chartSiteW (E := (G.Ω 1 × Fin N → ℂ) × (G.Ω 1 → ℂ)) (q₀ := u) (β := β)
      (e := fun q i j => q.1 (i, j))
      (H := fun q => baseHamiltonian G a ν q.2 (fun _ => 1)) (g := fun _ => g) (ψ := fun _ => ψ)
      (W := W) hcoord hH (fun _ _ => analyticAt_const) (fun p r => hWan p r u hu)
      (fun _ => analyticAt_const) (fun y => mem_slitPlane_of_norm_le (hT u hu y)) x
  · obtain ⟨he, hW, hα⟩ := hU u hu
    have hHrow : ∑ y, ‖baseHamiltonian G a ν u.2 (fun _ => 1) x y‖ ≤
        4 * d + |ν| + |a 1| / (L : ℝ) ^ 2 + Aα :=
      (baseHamiltonian_rowSum_le G a ν u.2 x).trans (by linarith)
    exact norm_chartSite_whitened_le hβ hE hBW hp he hW hψ hτ2 x hHrow hg

open Classical Balaban.Fluctuation Balaban.Background Balaban.SmallField Balaban.Analysis Balaban.Green in
/-- **Lemma AE for the chart activity `V_x` through the decoupled background (item 4).**  For a
finite-range whitening family `W` (rows read `(φ, α)` within `ρ`), analytic on a set `U` that contains
the decoupled backgrounds of the polydisc and on which the bounds of `chartFunctional_analytic_bdd`
hold, `V_x(1) = V_x(0) + ∑_{C ≠ ∅ rooted at the ball of radius ρ + L about x} coef_C`, the coefficients
of the non-rooted families vanish and `‖coef_C‖ ≤ 2 B_V e^{-(κ-1)|C|}`. -/
theorem chartActivity_expansion {Kc Cx c BG : ℝ} (hS : Dec2.DecSpecs d L Kc Cx c BG)
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
    (hΩ : ∀ z, z ∈ G.Ω 1) {Dr : ℕ} (hDD : L ^ 1 + 2 * L ^ 1 ≤ Dr)
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
      F (s, (Dd.Ψ, Dd.h)) ∈ U) :
    let Fe : ((G.Ω 1 × Fin N → ℂ) × (G.Ω 1 → ℂ)) → ℂ := fun u => chartSite β
      (fun y i => u.1 (y, i)) (baseHamiltonian G a ν u.2 (fun _ => 1)) g (W u *ᵥ ψ) x
    ∃ Bv : ℝ, Fe (F (fun _ => 1, (Dd.Ψ, Dd.h))) = Fe (F (0, (Dd.Ψ, Dd.h))) +
        ∑ C ∈ Finset.univ.filter (fun C : Finset ↥(coverOf G).cubeIdx =>
          C.Nonempty ∧ IsRootedFamily (cellPatch (coverOf G) Dr)
            (seedBall (x : Balaban.Localization.CTorus d L N₁ m₁ 1) (ρ + L) : Set _) C),
          coef (fun s => Fe (F (s, (Dd.Ψ, Dd.h)))) C ∧
      (∀ C : Finset ↥(coverOf G).cubeIdx, ¬ IsRootedFamily (cellPatch (coverOf G) Dr)
        (seedBall (x : Balaban.Localization.CTorus d L N₁ m₁ 1) (ρ + L) : Set _) C →
        coef (fun s => Fe (F (s, (Dd.Ψ, Dd.h)))) C = 0) ∧
      (∀ C : Finset ↥(coverOf G).cubeIdx, C.Nonempty →
        ‖coef (fun s => Fe (F (s, (Dd.Ψ, Dd.h)))) C‖ ≤ 2 * Bv * Real.exp (-(κ - 1) * C.card)) := by
  classical
  intro Fe
  obtain ⟨hFeU, hFeB⟩ := chartFunctional_analytic_bdd G a ν β hβ g ψ x W hWan hE hBW hp hU hψ hg hsmall
  refine ⟨_, bgFunctional_expansion G a ν hS Sb HB hκ hM hF hDu hFan hΩ hDD
    (chartSite_readsSeed G a ν β g ψ x ρ W hWloc) hFeU hFeB hmem⟩

end Expansion

end Balaban.LargeField.Base
