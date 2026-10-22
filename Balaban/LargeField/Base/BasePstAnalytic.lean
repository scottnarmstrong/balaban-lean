/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Base.BaseUnionNumerics
public import Balaban.Fluctuation.Thm31CoeffAnalytic

/-!
# The coefficients of the cluster expansion of a family of `LabelAct` are analytic in the parameter

`labelAct_Pst_analyticOnNhd`: for a family `A` of `LabelAct` with the constants of `marked_cubes_explicit`
(amplitude `ε* ≤ ε_max`, rate `κ_H` large, `κ₀ = a_ent + 1`, `K_c = K₀ + 1`), analytic in a parameter `u ∈ V`
(finite-dimensional) for each configuration `Φ` of a compact set `Q` carrying the product measure and
continuous on `Q`, the coefficient `u ↦ Pst μ Lab (A u).H Y` is analytic on `V`
(`Pst_Gst_analyticOnNhd` with the mark `G = 1`).
-/

@[expose] public section

namespace Balaban.LargeField.Base

open Balaban Balaban.Multiscale Balaban.Localization Balaban.Fluctuation Balaban.SmallField.Def6
  Balaban.Polymer MeasureTheory

section PstAnalytic

variable {d L N₁ m₁ : ℕ} [NeZero N₁] [NeZero L] {m₀ : ℕ}

/-- **The cluster-expansion coefficient of an analytic family of activities is analytic.** -/
theorem labelAct_Pst_analyticOnNhd {Lb : Type*} [Fintype Lb]
    {Ωb : CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := 1) m₀ 1 Set.univ → Type*}
    [∀ b, MeasurableSpace (Ωb b)] [∀ b, TopologicalSpace (Ωb b)] [∀ b, OpensMeasurableSpace (Ωb b)]
    [∀ b, SecondCountableTopology (Ωb b)]
    (μ : ∀ b, Measure (Ωb b)) [∀ b, IsProbabilityMeasure (μ b)] (hN : L ^ m₀ ∣ N₁)
    {Lab : CubeLabels m₀ 1 Set.univ Lb} {εs κH κ' : ℝ}
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    {V : Set E} (hV : IsOpen V) {Q : Set (∀ b, Ωb b)} (hQ : IsCompact Q) (hQm : MeasurableSet Q)
    (hμQ : ∀ᵐ Φ ∂(Measure.pi μ), Φ ∈ Q)
    (A : E → LabelAct Lab Ωb εs κH (aEnt d L + 1) (K0 d L (aEnt d L + 1) + 1)) (y0 : Lb)
    (hAhol : ∀ y Φ, AnalyticOnNhd ℂ (fun u => (A u).H y Φ) V)
    (hAcont : ∀ y, ∀ u ∈ V, ContinuousOn ((A u).H y) Q)
    (hκ'0 : 0 ≤ κ') (hεpos : 0 < εs)
    (hrate : κ' + 3 * (aEnt d L + 1) + c1 d L + 3 / 2 ≤ κH)
    (hεs : εs ≤ epsMax d L (K0 d L (aEnt d L + 1) + 1) κH (aEnt d L + 1) κ')
    (Y : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := 1) m₀ 1 Set.univ)) :
    AnalyticOnNhd ℂ (fun u => Pst μ Lab (A u).H Y) V := by
  have hK0pos : 0 < K0 d L (aEnt d L + 1) := by
    unfold K0
    have : Real.exp (-1) < 1 := by rw [Real.exp_lt_one_iff]; norm_num
    exact div_pos (Real.exp_pos _) (by linarith [aEnt_nonneg d L])
  have := Pst_Gst_analyticOnNhd (μ := μ) (hN := hN) (hj := le_refl 1) (hΩ := isPiUnion_univ_K)
    (Lab := Lab) (εH := εs) (κH := κH) (κG := κH) (κ0 := aEnt d L + 1) (κ' := κ')
    (Kc := K0 d L (aEnt d L + 1) + 1) (F0 := Real.exp (κH * Lab.dl y0)) (hV := hV) (hQ := hQ)
    (hQm := hQm) (hμQ := hμQ) (A := A) (y0 := y0) (G := fun _ _ => 1) (hGm := fun _ => measurable_const)
    (hG := fun u Φ => by
      simp only [norm_one]
      rw [← Real.exp_add]; simp)
    (hAhol := fun y Φ _ => hAhol y Φ) (hGhol := fun Φ _ => analyticOnNhd_const)
    (hAcont := hAcont) (hGcont := fun u _ => continuousOn_const) (hκ0 := le_refl _)
    (hKc := le_refl _) (hεpos := hεpos) (hF0 := Real.exp_pos _) (hκ' := hκ'0) (hκG := le_refl _)
    (hκ := hrate) (hε := hεs) (Y := Y)
  exact this.1

end PstAnalytic

end Balaban.LargeField.Base
