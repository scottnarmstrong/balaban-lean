/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Base.BaseChartActExpansion
import Mathlib.Tactic.Linarith

/-!
# The coefficients of the chart exponent

For the chart exponent `V_x(u; ψ)` (`chartFe`) of a whitening family `W` and a field `ψ`:
the explicit bound `chartBound` of `chartFunctional_analytic_bdd`; the coefficients of `s ↦ V_x(F(s,e); ψ)`
vanish off the rooted families, are bounded by `2 B_V e^{-(κ-1)|C|}` and sum to `V_x(F(1,e); ψ)`
(`chartCoef_spec`); they are analytic in the data `e` of the union domain and the field `ψ`
(`chartCoef_analyticOnNhd`, from the joint analyticity `chartFe_analyticAt_joint`); and `V_x` reads the
field only within `ρ + L` of `x` (`chartFe_psi_congr`).
-/

@[expose] public section

namespace Balaban.LargeField.Base

open Balaban Balaban.Multiscale Balaban.Localization Balaban.Background Balaban.Fluctuation
  Balaban.LargeField Balaban.SmallField Balaban.Green Balaban.Analysis Matrix

section Terms

variable {d L N₁ m₁ N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}

/-- The explicit bound of `chartFunctional_analytic_bdd` for the chart exponent `V_x` on the set where
the background is `≤ E_e`, the rows of the whitening have `ℓ¹` norm `≤ B_W`, the field is `≤ p₁`, the
multiplier is `≤ A_α` and the source row is `≤ G_g`. -/
noncomputable def chartBound (d L N : ℕ) (a1 ν β Aα Ee BW p₁ Gg : ℝ) : ℝ :=
  (4 * d + |ν| + |a1| / (L : ℝ) ^ 2 + Aα) * (N * (((1 + N * Ee ^ 2) * BW * p₁) *
          (Real.sqrt β * (3 / 2 * ((N : ℝ) * ((1 + N * Ee ^ 2) * BW * p₁) ^ 2 / β)) * Ee))) +
        1 / 2 * ((4 * d + |ν| + |a1| / (L : ℝ) ^ 2 + Aα) * (N *
          ((Real.sqrt β * (3 / 2 * ((N : ℝ) * ((1 + N * Ee ^ 2) * BW * p₁) ^ 2 / β)) * Ee) *
          (Real.sqrt β * (3 / 2 * ((N : ℝ) * ((1 + N * Ee ^ 2) * BW * p₁) ^ 2 / β)) * Ee)))) +
        1 / 2 * (3 / 2 * ((N : ℝ) * ((1 + N * Ee ^ 2) * BW * p₁) ^ 2 / β)) +
        (Real.sqrt β)⁻¹ * (Gg * (((1 + N * Ee ^ 2) * BW * p₁) + Real.sqrt β *
          (3 / 2 * ((N : ℝ) * ((1 + N * Ee ^ 2) * BW * p₁) ^ 2 / β)) * Ee))

/-- The chart exponent `V_x` as a function of the background, for the field `ψ'` and the whitening
`W`. -/
noncomputable def chartFe (G : GeneratingSet d L (N₁ * L ^ m₁) 1 ϱ) (a : ℕ → ℝ) (ν β : ℝ)
    (g ψ : G.Ω 1 × Fin N → ℂ)
    (W : ((G.Ω 1 × Fin N → ℂ) × (G.Ω 1 → ℂ)) → Matrix (G.Ω 1 × Fin N) (G.Ω 1 × Fin N) ℂ)
    (x : G.Ω 1) (u : (G.Ω 1 × Fin N → ℂ) × (G.Ω 1 → ℂ)) : ℂ :=
  chartSite β (fun y i => u.1 (y, i)) (baseHamiltonian G a ν u.2 (fun _ => 1)) g (W u *ᵥ ψ) x

theorem chartFunctional_bound (G : GeneratingSet d L (N₁ * L ^ m₁) 1 ϱ) (a : ℕ → ℝ)
    (ν β : ℝ) (hβ : 0 < β) (g ψ : G.Ω 1 × Fin N → ℂ) (x : G.Ω 1)
    (W : ((G.Ω 1 × Fin N → ℂ) × (G.Ω 1 → ℂ)) → Matrix (G.Ω 1 × Fin N) (G.Ω 1 × Fin N) ℂ)
    {U : Set ((G.Ω 1 × Fin N → ℂ) × (G.Ω 1 → ℂ))}
    (hWan : ∀ p r, AnalyticOnNhd ℂ (fun u => W u p r) U) {Ee BW p₁ Aα Gg : ℝ} (hE : 0 ≤ Ee)
    (hBW : 0 ≤ BW) (hp : 0 ≤ p₁)
    (hU : ∀ u ∈ U, (∀ y i, ‖u.1 (y, i)‖ ≤ Ee) ∧ (∀ p, ∑ r, ‖W u p r‖ ≤ BW) ∧ ‖u.2 x‖ ≤ Aα)
    (hψ : ∀ r, ‖ψ r‖ ≤ p₁) (hg : ∑ i, ‖g (x, i)‖ ≤ Gg)
    (hsmall : (N : ℝ) * ((1 + N * Ee ^ 2) * BW * p₁) ^ 2 / β ≤ 1 / 4) :
    AnalyticOnNhd ℂ (chartFe G a ν β g ψ W x) U ∧
      ∀ u ∈ U, ‖chartFe G a ν β g ψ W x u‖ ≤ chartBound d L N (a 1) ν β Aα Ee BW p₁ Gg :=
  chartFunctional_analytic_bdd G a ν β hβ g ψ x W hWan hE hBW hp hU hψ hg hsmall


open Classical in
/-- **The coefficients of the chart exponent.**  Under the hypotheses of `chartActivity_expansion`:
the coefficients of the families not rooted at the ball of radius `ρ + L` about `x` vanish, all
coefficients are bounded by `2 B_V e^{-(κ-1)|C|}` with the explicit `B_V = chartBound …`, and
`V_x(1) = ∑_{C rooted} coef_C` (the empty family has the coefficient `V_x(0)`). -/
theorem chartCoef_spec {Kc Cx c BG : ℝ} (hS : Dec2.DecSpecs d L Kc Cx c BG)
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
    (∀ Cs : Finset ↥(coverOf G).cubeIdx, ¬ IsRootedFamily (cellPatch (coverOf G) Dr)
        (seedBall (x : Balaban.Localization.CTorus d L N₁ m₁ 1) (ρ + L) : Set _) Cs →
        coef (fun s => chartFe G a ν β g ψ W x (F (s, (Dd.Ψ, Dd.h)))) Cs = 0) ∧
    (∀ Cs : Finset ↥(coverOf G).cubeIdx,
        ‖coef (fun s => chartFe G a ν β g ψ W x (F (s, (Dd.Ψ, Dd.h)))) Cs‖ ≤
          2 * chartBound d L N (a 1) ν β Aα Ee BW p₁ Gg * Real.exp (-(κ - 1) * Cs.card)) ∧
    chartFe G a ν β g ψ W x (F (fun _ => 1, (Dd.Ψ, Dd.h))) =
      ∑ Cs ∈ Finset.univ.filter (fun Cs : Finset ↥(coverOf G).cubeIdx => IsRootedFamily
          (cellPatch (coverOf G) Dr)
          (seedBall (x : Balaban.Localization.CTorus d L N₁ m₁ 1) (ρ + L) : Set _) Cs),
        coef (fun s => chartFe G a ν β g ψ W x (F (s, (Dd.Ψ, Dd.h)))) Cs := by
  classical
  obtain ⟨hFeU, hFeB⟩ := chartFunctional_bound G a ν β hβ g ψ x W hWan hE hBW hp hU hψ hg hsmall
  obtain ⟨h1, h2, h3⟩ := bgFunctional_expansion G a ν hS Sb HB hκ hM hF hDu hFan hΩ hDD
    (seed := seedBall (x : Balaban.Localization.CTorus d L N₁ m₁ 1) (ρ + L))
    (Fe := chartFe G a ν β g ψ W x) (chartSite_readsSeed G a ν β g ψ x ρ W hWloc) hFeU hFeB hmem
  have hzero : (0 : Dec2.DecParams (coverOf G)) ∈
      {s : Dec2.DecParams (coverOf G) | ∀ P, ‖s P‖ < Real.exp κ} := fun P => by
    simpa using Real.exp_pos κ
  have h0 := hFeB _ (hmem 0 hzero)
  refine ⟨h2, fun Cs => ?_, ?_⟩
  · by_cases hne : Cs.Nonempty
    · exact h3 Cs hne
    · rw [Finset.not_nonempty_iff_eq_empty] at hne
      subst hne
      rw [coef_empty]
      simp only [Finset.card_empty, Nat.cast_zero, mul_zero, Real.exp_zero, mul_one]
      linarith [norm_nonneg (chartFe G a ν β g ψ W x (F (0, (Dd.Ψ, Dd.h))))]
  · rw [h1]
    have hmemE : (∅ : Finset ↥(coverOf G).cubeIdx) ∈ Finset.univ.filter (fun Cs : Finset ↥(coverOf G).cubeIdx =>
        IsRootedFamily (cellPatch (coverOf G) Dr)
          (seedBall (x : Balaban.Localization.CTorus d L N₁ m₁ 1) (ρ + L) : Set _) Cs) :=
      Finset.mem_filter.2 ⟨Finset.mem_univ _, fun i hi => absurd hi (Finset.notMem_empty i)⟩
    rw [← Finset.add_sum_erase _ _ hmemE, coef_empty]
    congr 1
    refine Finset.sum_congr ?_ fun _ _ => rfl
    ext Cs
    simp only [Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and, ne_eq,
      Finset.nonempty_iff_ne_empty]

/-- **The chart exponent is jointly analytic in the background and the field.**  At every background
`u` of `U` (where the whitening `W` is analytic and the bounds hold) and every field `ψ` with
`‖ψ‖ ≤ p₁`, the function `(u, ψ) ↦ V_x(u; ψ)` is analytic. -/
theorem chartFe_analyticAt_joint (G : GeneratingSet d L (N₁ * L ^ m₁) 1 ϱ) (a : ℕ → ℝ)
    (ν β : ℝ) (hβ : 0 < β) (g : G.Ω 1 × Fin N → ℂ) (x : G.Ω 1)
    (W : ((G.Ω 1 × Fin N → ℂ) × (G.Ω 1 → ℂ)) → Matrix (G.Ω 1 × Fin N) (G.Ω 1 × Fin N) ℂ)
    {U : Set ((G.Ω 1 × Fin N → ℂ) × (G.Ω 1 → ℂ))}
    (hWan : ∀ p r, AnalyticOnNhd ℂ (fun u => W u p r) U) {Ee BW p₁ : ℝ} (hE : 0 ≤ Ee)
    (hU : ∀ u ∈ U, (∀ y i, ‖u.1 (y, i)‖ ≤ Ee) ∧ (∀ p, ∑ r, ‖W u p r‖ ≤ BW))
    (hsmall : (N : ℝ) * ((1 + N * Ee ^ 2) * BW * p₁) ^ 2 / β ≤ 1 / 4)
    {u₀ : (G.Ω 1 × Fin N → ℂ) × (G.Ω 1 → ℂ)} (hu₀ : u₀ ∈ U) {ψ₀ : G.Ω 1 × Fin N → ℂ}
    (hψ₀ : ∀ r, ‖ψ₀ r‖ ≤ p₁) :
    AnalyticAt ℂ (fun q : ((G.Ω 1 × Fin N → ℂ) × (G.Ω 1 → ℂ)) × (G.Ω 1 × Fin N → ℂ) =>
      chartFe G a ν β g q.2 W x q.1) (u₀, ψ₀) := by
  classical
  have hcoord : ∀ y i, AnalyticAt ℂ (fun q : ((G.Ω 1 × Fin N → ℂ) × (G.Ω 1 → ℂ)) × (G.Ω 1 × Fin N → ℂ) =>
      q.1.1 (y, i)) (u₀, ψ₀) := by
    intro y i
    fun_prop
  have hH : ∀ y z, AnalyticAt ℂ (fun q : ((G.Ω 1 × Fin N → ℂ) × (G.Ω 1 → ℂ)) × (G.Ω 1 × Fin N → ℂ) =>
      baseHamiltonian G a ν q.1.2 (fun _ => 1) y z) (u₀, ψ₀) := by
    intro y z
    have hq : (fun q : ((G.Ω 1 × Fin N → ℂ) × (G.Ω 1 → ℂ)) × (G.Ω 1 × Fin N → ℂ) =>
        baseHamiltonian G a ν q.1.2 (fun _ => 1) y z) =
        fun q => baseHamiltonian G a ν 0 (fun _ => 1) y z + (if y = z then q.1.2 y else 0) :=
      funext fun q => baseHamiltonian_apply_diag G a ν _ _ y z
    rw [hq]
    refine analyticAt_const.add ?_
    by_cases h : y = z
    · have : (fun q : ((G.Ω 1 × Fin N → ℂ) × (G.Ω 1 → ℂ)) × (G.Ω 1 × Fin N → ℂ) =>
          if y = z then q.1.2 y else (0 : ℂ)) = fun q => q.1.2 y := funext fun q => by simp [h]
      rw [this]
      fun_prop
    · have : (fun q : ((G.Ω 1 × Fin N → ℂ) × (G.Ω 1 → ℂ)) × (G.Ω 1 × Fin N → ℂ) =>
          if y = z then q.1.2 y else (0 : ℂ)) = fun _ => 0 := funext fun q => by simp [h]
      rw [this]
      exact analyticAt_const
  have hWa : ∀ p r, AnalyticAt ℂ (fun q : ((G.Ω 1 × Fin N → ℂ) × (G.Ω 1 → ℂ)) × (G.Ω 1 × Fin N → ℂ) =>
      W q.1 p r) (u₀, ψ₀) := fun p r => by
    have h1 : AnalyticAt ℂ (fun u => W u p r) (u₀, ψ₀).1 := hWan p r u₀ hu₀
    have h2 : AnalyticAt ℂ (fun q : ((G.Ω 1 × Fin N → ℂ) × (G.Ω 1 → ℂ)) × (G.Ω 1 × Fin N → ℂ) => q.1)
        (u₀, ψ₀) := analyticAt_fst
    exact h1.comp h2
  have hψa : ∀ r, AnalyticAt ℂ (fun q : ((G.Ω 1 × Fin N → ℂ) × (G.Ω 1 → ℂ)) × (G.Ω 1 × Fin N → ℂ) =>
      q.2 r) (u₀, ψ₀) := fun r => by fun_prop
  exact analyticAt_chartSiteW (E := ((G.Ω 1 × Fin N → ℂ) × (G.Ω 1 → ℂ)) × (G.Ω 1 × Fin N → ℂ))
    (q₀ := (u₀, ψ₀)) (β := β) (e := fun q i j => q.1.1 (i, j))
    (H := fun q => baseHamiltonian G a ν q.1.2 (fun _ => 1)) (g := fun _ => g)
    (ψ := fun q => q.2) (W := fun q => W q.1) hcoord hH (fun _ _ => analyticAt_const) hWa hψa
    (fun y => mem_slitPlane_of_norm_le (chartT_whitened_le hβ hE
      (fun y i => (hU u₀ hu₀).1 y i) (hU u₀ hu₀).2 hψ₀ hsmall y)) x

/-- The raw data of the union domain: the data `(Ψ, h)` of the fields `D` with
`InUnionDomainC G (bgC0 d L N) (c7 d L N BG κ) ν D`. -/
def dataSet (G : GeneratingSet d L (N₁ * L ^ m₁) 1 ϱ) (N : ℕ) (BG κ ν : ℝ) :
    Set (RawData d L (N₁ * L ^ m₁) 1 N) :=
  {r | ∃ D : BgData G N, InUnionDomainC G (bgC0 d L N) (c7 d L N BG κ) ν D ∧ r = (D.Ψ, D.h)}

open Classical in
/-- **The coefficients of the chart exponent are analytic in the data and the field.**  For the
background map `F` analytic on the polydisc times the data of the union domain, and a set `U` of
backgrounds on which the whitening is analytic and the bounds hold, every coefficient `coef_C` of
`s ↦ V_x(F(s, e); ψ)` is analytic in `(e, ψ)` at every `e` of the union domain and every field with
`‖ψ‖ ≤ p₁`. -/
theorem chartCoef_analyticOnNhd {BG : ℝ} (G : GeneratingSet d L (N₁ * L ^ m₁) 1 ϱ)
    (a : ℕ → ℝ) (ν β : ℝ) (hβ : 0 < β) {κ : ℝ} (hκ : 0 < κ)
    {F : Dec2.DecParams (coverOf G) × RawData d L (N₁ * L ^ m₁) 1 N →
      (G.Ω 1 × Fin N → ℂ) × (G.Ω 1 → ℂ)}
    (hFan : AnalyticOnNhd ℂ F {q | (∀ P, ‖q.1 P‖ < Real.exp κ) ∧
      ∃ D : BgData G N, InUnionDomainC G (bgC0 d L N) (c7 d L N BG κ) ν D ∧ q.2 = (D.Ψ, D.h)})
    (g : G.Ω 1 × Fin N → ℂ) (x : G.Ω 1)
    (W : ((G.Ω 1 × Fin N → ℂ) × (G.Ω 1 → ℂ)) → Matrix (G.Ω 1 × Fin N) (G.Ω 1 × Fin N) ℂ)
    {U : Set ((G.Ω 1 × Fin N → ℂ) × (G.Ω 1 → ℂ))}
    (hWan : ∀ p r, AnalyticOnNhd ℂ (fun u => W u p r) U) {Ee BW p₁ : ℝ} (hE : 0 ≤ Ee)
    (hU : ∀ u ∈ U, (∀ y i, ‖u.1 (y, i)‖ ≤ Ee) ∧ (∀ p, ∑ r, ‖W u p r‖ ≤ BW))
    (hsmall : (N : ℝ) * ((1 + N * Ee ^ 2) * BW * p₁) ^ 2 / β ≤ 1 / 4)
    (hmemAll : ∀ D : BgData G N, InUnionDomainC G (bgC0 d L N) (c7 d L N BG κ) ν D →
      ∀ s : Dec2.DecParams (coverOf G), (∀ P, ‖s P‖ < Real.exp κ) → F (s, (D.Ψ, D.h)) ∈ U)
    (Cs : Finset ↥(coverOf G).cubeIdx) :
    AnalyticOnNhd ℂ (fun e : RawData d L (N₁ * L ^ m₁) 1 N × (G.Ω 1 × Fin N → ℂ) =>
        coef (fun s => chartFe G a ν β g e.2 W x (F (s, e.1))) Cs)
      (dataSet G N BG κ ν ×ˢ {ψ : G.Ω 1 × Fin N → ℂ | ∀ r, ‖ψ r‖ ≤ p₁}) := by
  have hR : 1 < Real.exp κ := Real.one_lt_exp_iff.2 hκ
  refine analyticOnNhd_coef_of_analyticOnNhd (R := Real.exp κ) hR
    (Φ := fun p : (RawData d L (N₁ * L ^ m₁) 1 N × (G.Ω 1 × Fin N → ℂ)) × (Dec2.DecParams (coverOf G)) =>
      chartFe G a ν β g p.1.2 W x (F (p.2, p.1.1))) ?_ Cs
  rintro ⟨⟨e, ψ⟩, s⟩ ⟨⟨he, hψ⟩, hs⟩
  obtain ⟨D, hD, rfl⟩ := he
  have hsb : ∀ P, ‖s P‖ < Real.exp κ := fun P => by simpa using hs P
  have hF1 : AnalyticAt ℂ F (s, (D.Ψ, D.h)) := hFan _ ⟨hsb, D, hD, rfl⟩
  have hq1 : AnalyticAt ℂ (fun p : (RawData d L (N₁ * L ^ m₁) 1 N × (G.Ω 1 × Fin N → ℂ)) ×
      (Dec2.DecParams (coverOf G)) => (p.2, p.1.1)) ((((D.Ψ, D.h)), ψ), s) :=
    AnalyticAt.prod analyticAt_snd (analyticAt_fst.comp analyticAt_fst)
  have hq2 : AnalyticAt ℂ (fun p : (RawData d L (N₁ * L ^ m₁) 1 N × (G.Ω 1 × Fin N → ℂ)) ×
      (Dec2.DecParams (coverOf G)) => F (p.2, p.1.1)) ((((D.Ψ, D.h)), ψ), s) :=
    hF1.comp_of_eq hq1 rfl
  have hq3 : AnalyticAt ℂ (fun p : (RawData d L (N₁ * L ^ m₁) 1 N × (G.Ω 1 × Fin N → ℂ)) ×
      (Dec2.DecParams (coverOf G)) => p.1.2) ((((D.Ψ, D.h)), ψ), s) :=
    analyticAt_snd.comp analyticAt_fst
  have hq : AnalyticAt ℂ (fun p : (RawData d L (N₁ * L ^ m₁) 1 N × (G.Ω 1 × Fin N → ℂ)) ×
      (Dec2.DecParams (coverOf G)) => (F (p.2, p.1.1), p.1.2)) ((((D.Ψ, D.h)), ψ), s) :=
    AnalyticAt.prod hq2 hq3
  have hj := chartFe_analyticAt_joint G a ν β hβ g x W hWan hE hU hsmall (hmemAll D hD s hsb) hψ
  have h := hj.comp_of_eq hq rfl
  exact h.congr (Filter.Eventually.of_forall fun p => rfl)

open Classical in
/-- **The chart exponent reads the field only near the site.**  If the rows of the whitening are
supported within `ρ` of the row, `V_x(u; ψ)` depends on `ψ` only at the sites within `ρ + L` of `x`. -/
theorem chartFe_psi_congr (G : GeneratingSet d L (N₁ * L ^ m₁) 1 ϱ) (a : ℕ → ℝ) (ν β : ℝ)
    (g ψ ψ' : G.Ω 1 × Fin N → ℂ) (x : G.Ω 1) (ρ : ℕ)
    (W : ((G.Ω 1 × Fin N → ℂ) × (G.Ω 1 → ℂ)) → Matrix (G.Ω 1 × Fin N) (G.Ω 1 × Fin N) ℂ)
    (hWr : ∀ u p r, W u p r ≠ 0 →
      supDist (p.1 : Balaban.Localization.CTorus d L N₁ m₁ 1) (r.1 : Balaban.Localization.CTorus d L N₁ m₁ 1) ≤ ρ)
    (hψ : ∀ r : G.Ω 1 × Fin N,
      supDist (x : Balaban.Localization.CTorus d L N₁ m₁ 1) (r.1 : Balaban.Localization.CTorus d L N₁ m₁ 1) ≤ ρ + L →
        ψ r = ψ' r) (u : (G.Ω 1 × Fin N → ℂ) × (G.Ω 1 → ℂ)) :
    chartFe G a ν β g ψ W x u = chartFe G a ν β g ψ' W x u := by
  set NB : Finset (G.Ω 1) := Finset.univ.filter fun y =>
    supDist (x : Balaban.Localization.CTorus d L N₁ m₁ 1) y ≤ L with hNB
  have hmemNB : ∀ y, y ∈ NB ↔ supDist (x : Balaban.Localization.CTorus d L N₁ m₁ 1) y ≤ L := by
    intro y; simp [hNB]
  refine chartSite_congr x NB ((hmemNB x).2 (by rw [supDist_self]; exact Nat.zero_le _)) ?_
    (fun _ => rfl) (fun _ => rfl) (fun _ _ => rfl) ?_
  · intro y hy
    exact (hmemNB y).2 (baseHamiltonian_ne_zero_dist G a ν u.2 hy)
  · intro y hy i
    simp only [Matrix.mulVec, dotProduct]
    refine Finset.sum_congr rfl fun r _ => ?_
    by_cases h0 : W u (y, i) r = 0
    · rw [h0]; simp
    · rw [hψ r ?_]
      have h1 := (hmemNB y).1 hy
      have h2 := hWr u (y, i) r h0
      have h3 := supDist_triangle (x : Balaban.Localization.CTorus d L N₁ m₁ 1) y r.1
      simp only [] at h2
      omega

end Terms

end Balaban.LargeField.Base
