/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Base.BaseChartSource
import Mathlib.Tactic.Linarith

/-!
# Joint analyticity of the chart coefficients in the datum and the source

`chartCoef_analyticOnNhd_eg`: `(e, g) ↦ coef_C (s ↦ V_x(F(s, e); ψ, g))` is analytic on the data of the union
domain times all sources (the exponent is affine in `g`, `chartFe_affine_g`, with pieces analytic in
`(s, e)`).
-/

@[expose] public section

namespace Balaban.LargeField.Base

open Balaban Balaban.Multiscale Balaban.Localization Balaban.Background Balaban.Fluctuation
  Balaban.LargeField Balaban.SmallField Balaban.Green Balaban.Analysis Matrix

section EG

variable {d L N₁ m₁ N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}

open Classical in
/-- **The coefficients of the chart exponent are jointly analytic in the datum and the source.** -/
theorem chartCoef_analyticOnNhd_eg {BG : ℝ} (G : GeneratingSet d L (N₁ * L ^ m₁) 1 ϱ) (a : ℕ → ℝ)
    (ν β : ℝ) (hβ : 0 < β) {κ : ℝ} (hκ : 0 < κ)
    {F : Dec2.DecParams (coverOf G) × RawData d L (N₁ * L ^ m₁) 1 N →
      (G.Ω 1 × Fin N → ℂ) × (G.Ω 1 → ℂ)}
    (hFan : AnalyticOnNhd ℂ F {q | (∀ P, ‖q.1 P‖ < Real.exp κ) ∧
      ∃ D : BgData G N, InUnionDomainC G (bgC0 d L N) (c7 d L N BG κ) ν D ∧ q.2 = (D.Ψ, D.h)})
    (ψ : G.Ω 1 × Fin N → ℂ) (x : G.Ω 1)
    (W : ((G.Ω 1 × Fin N → ℂ) × (G.Ω 1 → ℂ)) → Matrix (G.Ω 1 × Fin N) (G.Ω 1 × Fin N) ℂ)
    {U : Set ((G.Ω 1 × Fin N → ℂ) × (G.Ω 1 → ℂ))}
    (hWan : ∀ p r, AnalyticOnNhd ℂ (fun u => W u p r) U) {Ee BW p₁ Aα : ℝ} (hE : 0 ≤ Ee)
    (hBW : 0 ≤ BW) (hp : 0 ≤ p₁)
    (hU : ∀ u ∈ U, (∀ y i, ‖u.1 (y, i)‖ ≤ Ee) ∧ (∀ p, ∑ r, ‖W u p r‖ ≤ BW) ∧ ‖u.2 x‖ ≤ Aα)
    (hψ : ∀ r, ‖ψ r‖ ≤ p₁)
    (hsmall : (N : ℝ) * ((1 + N * Ee ^ 2) * BW * p₁) ^ 2 / β ≤ 1 / 4)
    (hmemAll : ∀ D : BgData G N, InUnionDomainC G (bgC0 d L N) (c7 d L N BG κ) ν D →
      ∀ s : Dec2.DecParams (coverOf G), (∀ P, ‖s P‖ < Real.exp κ) → F (s, (D.Ψ, D.h)) ∈ U)
    (Cs : Finset ↥(coverOf G).cubeIdx) :
    AnalyticOnNhd ℂ (fun p : RawData d L (N₁ * L ^ m₁) 1 N × (G.Ω 1 × Fin N → ℂ) =>
      coef (fun s => chartFe G a ν β p.2 ψ W x (F (s, p.1))) Cs) (dataSet G N BG κ ν ×ˢ Set.univ) := by
  have hR : 1 < Real.exp κ := Real.one_lt_exp_iff.2 hκ
  have hδ : ∀ i : Fin N, ∑ i', ‖(Pi.single (x, i) (1 : ℂ) : G.Ω 1 × Fin N → ℂ) (x, i')‖ ≤ 1 := by
    intro i
    rw [Finset.sum_eq_single i]
    · simp
    · intro b _ hb
      have : (x, b) ≠ (x, i) := fun h => hb (Prod.mk.inj h).2
      simp [this]
    · simp
  have h0 : ∑ i', ‖(0 : G.Ω 1 × Fin N → ℂ) (x, i')‖ ≤ 1 := by simp
  refine analyticOnNhd_coef_of_analyticOnNhd (R := Real.exp κ) hR
    (Φ := fun q : (RawData d L (N₁ * L ^ m₁) 1 N × (G.Ω 1 × Fin N → ℂ)) × Dec2.DecParams (coverOf G) =>
      chartFe G a ν β q.1.2 ψ W x (F (q.2, q.1.1))) ?_ Cs
  rintro ⟨⟨e, g⟩, s⟩ ⟨⟨he, -⟩, hs⟩
  obtain ⟨D, hD, rfl⟩ := he
  have hsb : ∀ P, ‖s P‖ < Real.exp κ := fun P => by simpa using hs P
  have hF1 : AnalyticAt ℂ F (s, (D.Ψ, D.h)) := hFan _ ⟨hsb, D, hD, rfl⟩
  have hq1 : AnalyticAt ℂ (fun q : (RawData d L (N₁ * L ^ m₁) 1 N × (G.Ω 1 × Fin N → ℂ)) ×
      Dec2.DecParams (coverOf G) => (q.2, q.1.1)) ((((D.Ψ, D.h)), g), s) :=
    AnalyticAt.prod analyticAt_snd (analyticAt_fst.comp analyticAt_fst)
  have hq2 : AnalyticAt ℂ (fun q : (RawData d L (N₁ * L ^ m₁) 1 N × (G.Ω 1 × Fin N → ℂ)) ×
      Dec2.DecParams (coverOf G) => F (q.2, q.1.1)) ((((D.Ψ, D.h)), g), s) :=
    hF1.comp_of_eq hq1 rfl
  -- the pieces for a unit source or the source `0`
  have hpiece : ∀ src : G.Ω 1 × Fin N → ℂ, ∑ i, ‖src (x, i)‖ ≤ 1 →
      AnalyticAt ℂ (fun q : (RawData d L (N₁ * L ^ m₁) 1 N × (G.Ω 1 × Fin N → ℂ)) ×
        Dec2.DecParams (coverOf G) => chartFe G a ν β src ψ W x (F (q.2, q.1.1)))
        ((((D.Ψ, D.h)), g), s) := by
    intro src hsrc
    have hFe := (chartFunctional_bound G a ν β hβ src ψ x W hWan hE hBW hp hU hψ hsrc hsmall).1
      (F (s, (D.Ψ, D.h))) (hmemAll D hD s hsb)
    have h1 := hFe.comp_of_eq hq2 rfl
    exact h1.congr (Filter.Eventually.of_forall fun q => rfl)
  have hf0 := hpiece 0 h0
  have hexp : AnalyticAt ℂ (fun q : (RawData d L (N₁ * L ^ m₁) 1 N × (G.Ω 1 × Fin N → ℂ)) ×
      Dec2.DecParams (coverOf G) =>
      chartFe G a ν β 0 ψ W x (F (q.2, q.1.1)) +
        ∑ i, q.1.2 (x, i) * (chartFe G a ν β (Pi.single (x, i) 1) ψ W x (F (q.2, q.1.1)) -
          chartFe G a ν β 0 ψ W x (F (q.2, q.1.1)))) ((((D.Ψ, D.h)), g), s) := by
    refine hf0.add (Finset.analyticAt_fun_sum _ fun i _ => ?_)
    have hc : AnalyticAt ℂ (fun q : (RawData d L (N₁ * L ^ m₁) 1 N × (G.Ω 1 × Fin N → ℂ)) ×
        Dec2.DecParams (coverOf G) => q.1.2 (x, i)) ((((D.Ψ, D.h)), g), s) := by fun_prop
    exact hc.mul ((hpiece _ (hδ i)).sub hf0)
  exact hexp.congr (Filter.Eventually.of_forall fun q => (chartFe_affine_g G a ν β q.1.2 ψ W x _).symm)

end EG

end Balaban.LargeField.Base
