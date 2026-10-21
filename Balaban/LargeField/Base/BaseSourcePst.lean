/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Base.BaseSourceIncrement
public import Balaban.Fluctuation.Thm31CoeffAnalytic
import Mathlib.Tactic.Linarith

/-!
# The source increment of the cluster-expansion coefficients

`Pst_src_increment`: for a family `g ↦ A g` of `LabelAct` indexed by sources `g : CTorus → (J → ℂ)` in
the `ℓ¹` ball of radius `Gs > 1`, analytic in `g`, with common constants satisfying the hypotheses of
`marked_cubes_explicit`, and with `(A g).H y` depending on `g` only on the sites of the label of `y` (for `g` in the ball):
`Pst(g) = Pst(0) + ∑_{x,i} g_{x,i} ℳ_{x,i}(g)` on the unit `ℓ¹` ball (`sub_eq_sum_srcM`), with
`|ℳ_{x,i}(g)| ≤ ε_H Kc C_PE e^{-κ' d(Y)} / (Gs - 1)` (Cauchy, `norm_srcM_le`) and `ℳ_{x,i} = 0` for the
sites `x` outside `Ŷ(Y)` (`Pst_ext_congr`).
-/

@[expose] public section

namespace Balaban.LargeField.Base

open Balaban Balaban.Localization Balaban.Polymer Balaban.Fluctuation MeasureTheory

section SrcPst

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {m₀ j : ℕ} {Ω : Set (CTorus d L N₁ m₁ K)}
  {Lb : Type*} [Fintype Lb] {J : Type*} [Fintype J] [DecidableEq J]

open Classical in
/-- **The source increment of the cluster-expansion coefficients.**  Let `g ↦ A g` be a family of
`LabelAct`, `g` a source `CTorus → (J → ℂ)` in the `ℓ¹` ball of radius `Gs > 1`, with the
activities analytic in `g` (on a compact set `Q` carrying the product measure), continuous on `Q`,
bounded with common constants satisfying the hypotheses of `marked_cubes_explicit`, and
`(A g).H y` depending on `g` only on the sites of the label of `y`.  Then for every `Y ≠ ∅`,
`P(g) = Pst μ Lab (A g).H Y` satisfies on `‖g‖₁ < 1`:
`P g = P 0 + ∑_{x,i} g_{x,i} ℳ_{x,i}(g)`, `|ℳ_{x,i}(g)| ≤ ε_H Kc C_PE e^{-κ' d(Y)} / (Gs - 1)`, and
`ℳ_{x,i} = 0` for the sites `x ∉ Ŷ(Y)`. -/
theorem Pst_src_increment {Ωb : (CubeB (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ j Ω) → Type*} [∀ b, MeasurableSpace (Ωb b)]
    (μ : ∀ b, Measure (Ωb b)) [∀ b, IsProbabilityMeasure (μ b)]
    (hN : L ^ m₀ ∣ N₁) (hj : j ≤ K) (hΩ : IsPiUnion m₀ j Ω)
    {Lab : CubeLabels m₀ j Ω Lb} {εH κH κ0 κ' Kc : ℝ}
    [∀ b, TopologicalSpace (Ωb b)] [∀ b, OpensMeasurableSpace (Ωb b)]
    [∀ b, SecondCountableTopology (Ωb b)]
    {Q : Set (∀ b, Ωb b)} (hQ : IsCompact Q) (hQm : MeasurableSet Q)
    (hμQ : ∀ᵐ Φ ∂(Measure.pi μ), Φ ∈ Q) {Gs : ℝ} (hGs : 1 < Gs)
    (A : (CTorus d L N₁ m₁ K → J → ℂ) → LabelAct Lab Ωb εH κH κ0 Kc) (y0 : Lb)
    (hAhol : ∀ y, ∀ Φ ∈ Q, AnalyticOnNhd ℂ (fun g => (A g).H y Φ) {g | l1src g < Gs})
    (hAcont : ∀ y, ∀ g, l1src g < Gs → ContinuousOn ((A g).H y) Q)
    (hdep : ∀ y (g g' : CTorus d L N₁ m₁ K → J → ℂ), l1src g < Gs → l1src g' < Gs →
      (∀ z ∈ Lab.ysite y, g z = g' z) → (A g).H y = (A g').H y)
    (hκ0 : aEnt d L + 1 ≤ κ0) (hKc : K0 d L κ0 + 1 ≤ Kc) (hεpos : 0 < εH)
    (hκ' : 0 ≤ κ') (hκ : κ' + 3 * κ0 + c1 d L + 3 / 2 ≤ κH)
    (hε : εH ≤ 1 / (8 * Kc ^ 3 * c1 d L *
      Real.exp ((κH - 2 * κ0) * cG d L + c1 d L + κ' * cG d L)))
    (Y : Finset (CubeB (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ j Ω)) (hY : Y.Nonempty) {g : CTorus d L N₁ m₁ K → J → ℂ} (hg : l1src g < 1) :
    Pst μ Lab (A g).H Y = Pst μ Lab (A 0).H Y +
        ∑ x, ∑ i, g x i * srcM (fun h => Pst μ Lab (A h).H Y) g x i ∧
      (∀ x i, ‖srcM (fun h => Pst μ Lab (A h).H Y) g x i‖ ≤
        εH * Kc * CPE d L Kc κH κ0 κ' * Real.exp (-κ' * dExt Y) / (Gs - 1)) ∧
      (∀ x, x ∉ Yhat Ω (sitesOf Y) → ∀ i, srcM (fun h => Pst μ Lab (A h).H Y) g x i = 0) := by
  have hV : IsOpen {g : CTorus d L N₁ m₁ K → J → ℂ | l1src g < Gs} := by
    refine isOpen_lt ?_ continuous_const
    unfold l1src
    fun_prop
  have hGm : ∀ _ : CTorus d L N₁ m₁ K → J → ℂ, Measurable (fun _ : (∀ b, Ωb b) => (1 : ℂ)) :=
    fun _ => measurable_const
  have hP := (Pst_Gst_analyticOnNhd (μ := μ) hN hj hΩ (Lab := Lab) (εH := εH) (κH := κH)
    (κG := κH) (κ0 := κ0) (κ' := κ') (Kc := Kc) (F0 := Real.exp (κH * Lab.dl y0)) hV hQ hQm hμQ A y0
    (fun _ _ => 1) hGm (fun u Φ => by simp only [norm_one]; rw [← Real.exp_add]; simp)
    hAhol (fun Φ _ => analyticOnNhd_const) (fun y g hg => hAcont y g hg) (fun u _ => continuousOn_const)
    hκ0 hKc hεpos (Real.exp_pos _) hκ' le_rfl hκ hε Y).1
  have hB : ∀ h : CTorus d L N₁ m₁ K → J → ℂ, l1src h < Gs →
      ‖Pst μ Lab (A h).H Y‖ ≤ εH * Kc * CPE d L Kc κH κ0 κ' * Real.exp (-κ' * dExt Y) := by
    intro h _
    have := (marked_cubes_explicit (F0 := Real.exp (κH * Lab.dl y0)) (κG := κH) (κ' := κ') μ hN hj hΩ
      (A h) y0 (fun _ => 1) measurable_const (fun Φ Φ' _ => rfl)
      (fun Φ => by simp only [norm_one]; rw [← Real.exp_add]; simp) hκ0 hKc hεpos (Real.exp_pos _) hκ'
      le_rfl hκ hε).2.1.2 Y hY
    exact this
  have hg' : l1src g < Gs := by linarith
  refine ⟨sub_eq_sum_srcM hP hg', fun x i => norm_srcM_le hGs hP hB hg x i, fun x hx i => ?_⟩
  refine srcM_eq_zero hP x (fun h hh c hc => ?_) hg' i
  exact Pst_congr μ μ (A (Function.update h x c)) (A h).H Y (fun _ _ => rfl) (fun y hy =>
    hdep y _ _ hc hh (fun z hz => by
      have hzx : z ≠ x := fun h' => hx (h' ▸ ysite_subset_Yhat hN hj hΩ Lab y hy hz)
      simp [Function.update_of_ne hzx]))

end SrcPst

end Balaban.LargeField.Base
