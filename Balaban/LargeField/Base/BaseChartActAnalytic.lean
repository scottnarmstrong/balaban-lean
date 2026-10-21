/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Base.BaseChartAct

/-!
# (AE1), analyticity of the decoupled chart activity in the parameters and the data

`baseChartV_analyticAt`: for a background map `F` analytic on a set `Dom` of parameters and data
whose decoupled data lie in the domain `DecDom` of `baseCovX_sqrt`, the site exponent
`(s, θ, ψ', g) ↦ baseChartV x s (θ, ψ', g)` is analytic at every point where
`1 - v_y·v_y/β` is in the slit plane for all `y` (the square root and the logarithm of the chart
are then analytic).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField.Base

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization MeasureTheory Set Matrix

section Analytic

variable {d L N₁ m₁ N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
  (G : GeneratingSet d L (N₁ * L ^ m₁) 1 ϱ) (a : ℕ → ℝ) (ν : ℝ)

theorem baseHamiltonian_apply_diag (α : G.Ω 1 → ℂ) (s : FineBond d L (N₁ * L ^ m₁) → ℂ)
    (x y : G.Ω 1) :
    baseHamiltonian G a ν α s x y =
      baseHamiltonian G a ν 0 s x y + (if x = y then α x else 0) := by
  unfold baseHamiltonian cutOperator
  simp only [Matrix.add_apply, Matrix.diagonal_apply, Pi.zero_apply]
  by_cases h : x = y <;> simp [h, add_assoc, add_comm]

variable {G}

/-- The parameter space of the activity: decoupling parameters, raw data, fluctuation, source. -/
abbrev ChartArg (G : GeneratingSet d L (N₁ * L ^ m₁) 1 ϱ) (N : ℕ) : Type _ :=
  Dec2.DecParams (coverOf G) × (RawData d L (N₁ * L ^ m₁) 1 N × (G.Ω 1 × Fin N → ℂ) ×
    (G.Ω 1 × Fin N → ℂ))

theorem analyticAt_bgDataOf
    {F : Dec2.DecParams (coverOf G) × RawData d L (N₁ * L ^ m₁) 1 N →
      (G.Ω 1 × Fin N → ℂ) × (G.Ω 1 → ℂ)}
    {w : ChartArg G N} (hF : AnalyticAt ℂ F (w.1, w.2.1)) :
    AnalyticAt ℂ (fun q : ChartArg G N => bgDataOf G F q.1 q.2.1) w := by
  have hq : AnalyticAt ℂ (fun q : ChartArg G N => (q.1, q.2.1)) w := by fun_prop
  have hFq : AnalyticAt ℂ (fun q : ChartArg G N => F (q.1, q.2.1)) w :=
    AnalyticAt.comp (g := F) (f := fun q : ChartArg G N => (q.1, q.2.1)) hF hq
  unfold bgDataOf
  refine AnalyticAt.prod (by fun_prop) (AnalyticAt.prod ?_ ?_)
  · rw [analyticAt_pi_iff]
    intro z
    rw [analyticAt_pi_iff]
    intro i
    by_cases h : z ∈ G.Ω 1
    · simp only [extField, h, dite_true]
      exact (analyticAt_pi_iff.1 (by fun_prop : AnalyticAt ℂ (fun q : ChartArg G N => (F (q.1, q.2.1)).1) w) (⟨z, h⟩, i))
    · simp only [extField, h, dite_false]
      exact analyticAt_const
  · exact (by fun_prop : AnalyticAt ℂ (fun q : ChartArg G N => (F (q.1, q.2.1)).2) w)

theorem baseChartV_eq_chartSite
    (F : Dec2.DecParams (coverOf G) × RawData d L (N₁ * L ^ m₁) 1 N →
      (G.Ω 1 × Fin N → ℂ) × (G.Ω 1 → ℂ)) (aT β : ℝ) (x : G.Ω 1) (q : ChartArg G N) :
    baseChartV G a aT ν F β x q.1 q.2 =
      chartSite β (fun y i => (F (q.1, q.2.1)).1 (y, i))
        (baseHamiltonian G a ν (F (q.1, q.2.1)).2 (fun _ => 1)) q.2.2.2
        (baseSqrtCov G a aT ν (bgDataOf G F q.1 q.2.1) *ᵥ q.2.2.1) x := by
  unfold baseChartV baseChartVAt
  have : restrictField G (bgDataOf G F q.1 q.2.1).2.1 = fun y i => (F (q.1, q.2.1)).1 (y, i) := by
    funext y i; exact restrictField_extField G _ y i
  rw [this]
  rfl

variable {Cx : ℝ}

theorem analyticOn_baseSqrtCov (aT : ℝ) (S : Dec2.XCover (coverOf G) G a aT ν Cx) (hCx : 0 ≤ Cx)
    {κ δ : ℝ} (hκ : 0 ≤ κ)
    (hM : Dec2.cstarX d L Cx * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) (hδ : 0 ≤ δ)
    (hsm : δ ^ 2 * smallConstX d L κ ≤ 1 / 4) (y z : G.Ω 1 × Fin N) :
    AnalyticOnNhd ℂ (fun e : DecData G N => baseSqrtCov G a aT ν e y z) (DecDom G N κ δ) := by
  obtain ⟨B, -, H⟩ := baseCovX_sqrt d L κ
  exact (H S hCx hκ hM hδ hsm y z).2.2.1

/-- **(AE1), analyticity.** -/
theorem baseChartV_analyticAt (aT : ℝ) (S : Dec2.XCover (coverOf G) G a aT ν Cx) (hCx : 0 ≤ Cx)
    {κ δ : ℝ} (hκ : 0 ≤ κ)
    (hM : Dec2.cstarX d L Cx * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) (hδ : 0 ≤ δ)
    (hsm : δ ^ 2 * smallConstX d L κ ≤ 1 / 4)
    {F : Dec2.DecParams (coverOf G) × RawData d L (N₁ * L ^ m₁) 1 N →
      (G.Ω 1 × Fin N → ℂ) × (G.Ω 1 → ℂ)} (β : ℝ)
    {w : ChartArg G N} (hF : AnalyticAt ℂ F (w.1, w.2.1))
    (hdom : bgDataOf G F w.1 w.2.1 ∈ DecDom G N κ δ)
    (hslit : ∀ y, 1 - chartT β (chartTangent (fun y i => (F (w.1, w.2.1)).1 (y, i))
      (baseSqrtCov G a aT ν (bgDataOf G F w.1 w.2.1) *ᵥ w.2.2.1)) y ∈ Complex.slitPlane)
    (x : G.Ω 1) :
    AnalyticAt ℂ (fun q : ChartArg G N => baseChartV G a aT ν F β x q.1 q.2) w := by
  have hbg : AnalyticAt ℂ (fun q : ChartArg G N => bgDataOf G F q.1 q.2.1) w :=
    analyticAt_bgDataOf hF
  have hFq : AnalyticAt ℂ (fun q : ChartArg G N => F (q.1, q.2.1)) w :=
    AnalyticAt.comp (g := F) (f := fun q : ChartArg G N => (q.1, q.2.1)) hF (by fun_prop)
  have hF1 : AnalyticAt ℂ (fun q : ChartArg G N => (F (q.1, q.2.1)).1) w :=
    AnalyticAt.comp (g := Prod.fst) (f := fun q : ChartArg G N => F (q.1, q.2.1)) analyticAt_fst hFq
  have hF2 : AnalyticAt ℂ (fun q : ChartArg G N => (F (q.1, q.2.1)).2) w :=
    AnalyticAt.comp (g := Prod.snd) (f := fun q : ChartArg G N => F (q.1, q.2.1)) analyticAt_snd hFq
  have hpsi : AnalyticAt ℂ (fun q : ChartArg G N => q.2.2.1) w :=
    AnalyticAt.comp (g := Prod.fst) (f := fun q : ChartArg G N => q.2.2) analyticAt_fst
      (AnalyticAt.comp (g := Prod.snd) (f := fun q : ChartArg G N => q.2) analyticAt_snd
        (AnalyticAt.comp (g := Prod.snd) (f := fun q : ChartArg G N => q) analyticAt_snd analyticAt_id))
  have hsrc : AnalyticAt ℂ (fun q : ChartArg G N => q.2.2.2) w :=
    AnalyticAt.comp (g := Prod.snd) (f := fun q : ChartArg G N => q.2.2) analyticAt_snd
      (AnalyticAt.comp (g := Prod.snd) (f := fun q : ChartArg G N => q.2) analyticAt_snd
        (AnalyticAt.comp (g := Prod.snd) (f := fun q : ChartArg G N => q) analyticAt_snd analyticAt_id))
  have hSq : ∀ y z, AnalyticAt ℂ
      (fun q : ChartArg G N => baseSqrtCov G a aT ν (bgDataOf G F q.1 q.2.1) y z) w := by
    intro y z
    have := analyticOn_baseSqrtCov a ν aT S hCx hκ hM hδ hsm y z _ hdom
    exact AnalyticAt.comp (g := fun e : DecData G N => baseSqrtCov G a aT ν e y z)
      (f := fun q : ChartArg G N => bgDataOf G F q.1 q.2.1) this hbg
  have hHe : ∀ y z, AnalyticAt ℂ
      (fun q : ChartArg G N => baseHamiltonian G a ν (F (q.1, q.2.1)).2 (fun _ => 1) y z) w := by
    intro y z
    have hq : (fun q : ChartArg G N => baseHamiltonian G a ν (F (q.1, q.2.1)).2 (fun _ => 1) y z) =
        fun q => baseHamiltonian G a ν 0 (fun _ => 1) y z + (if y = z then (F (q.1, q.2.1)).2 y else 0) :=
      funext fun q => baseHamiltonian_apply_diag G a ν _ _ y z
    rw [hq]
    refine analyticAt_const.add ?_
    by_cases h : y = z
    · have : (fun q : ChartArg G N => if y = z then (F (q.1, q.2.1)).2 y else (0 : ℂ)) =
          fun q => (F (q.1, q.2.1)).2 y := funext fun q => by simp [h]
      rw [this]
      exact analyticAt_pi_iff.1 hF2 y
    · have : (fun q : ChartArg G N => if y = z then (F (q.1, q.2.1)).2 y else (0 : ℂ)) =
          fun _ => 0 := funext fun q => by simp [h]
      rw [this]
      exact analyticAt_const
  have hEe : ∀ y i, AnalyticAt ℂ (fun q : ChartArg G N => (F (q.1, q.2.1)).1 (y, i)) w :=
    fun y i => analyticAt_pi_iff.1 hF1 (y, i)
  have hGe : ∀ y i, AnalyticAt ℂ (fun q : ChartArg G N => q.2.2.2 (y, i)) w :=
    fun y i => analyticAt_pi_iff.1 hsrc (y, i)
  have hPe : ∀ r, AnalyticAt ℂ (fun q : ChartArg G N => q.2.2.1 r) w :=
    fun r => analyticAt_pi_iff.1 hpsi r
  have hfun : (fun q : ChartArg G N => baseChartV G a aT ν F β x q.1 q.2) =
      fun q => chartSite β (fun y i => (F (q.1, q.2.1)).1 (y, i))
        (baseHamiltonian G a ν (F (q.1, q.2.1)).2 (fun _ => 1)) q.2.2.2
        (baseSqrtCov G a aT ν (bgDataOf G F q.1 q.2.1) *ᵥ q.2.2.1) x := by
    funext q; exact baseChartV_eq_chartSite a ν F aT β x q
  rw [hfun]
  have key := @analyticAt_chartSiteW (G.Ω 1) _ _ N (ChartArg G N) _ _ w β
    (fun q => fun i j => (F (q.1, q.2.1)).1 (i, j))
    (fun q => baseHamiltonian G a ν (F (q.1, q.2.1)).2 (fun _ => 1))
    (fun q => q.2.2.2) (fun q => q.2.2.1)
    (fun q => baseSqrtCov G a aT ν (bgDataOf G F q.1 q.2.1)) hEe hHe hGe hSq hPe hslit x
  exact key

end Analytic

end Balaban.LargeField.Base
