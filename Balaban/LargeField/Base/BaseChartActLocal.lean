/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Base.BaseChartActAlg

/-!
# The site exponent reads a finite neighbourhood of the site

`chartSite_congr`: `V_x` depends on the background `e`, the whitened fluctuation `w` and the Hessian
`H` only through the sites `y` of a set `NB ∋ x` that contains the support of the row `H x ·`, and on the
source `g` only at `x`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField.Base

open Balaban Balaban.Multiscale Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {N : ℕ}

theorem chartTangent_congr {e e' : ι → Fin N → ℂ} {w w' : ι × Fin N → ℂ} {y : ι}
    (he : e y = e' y) (hw : ∀ i, w (y, i) = w' (y, i)) (i : Fin N) :
    chartTangent e w (y, i) = chartTangent e' w' (y, i) := by
  rw [chartTangent_apply, chartTangent_apply]
  have h1 : ∀ j, e y j = e' y j := fun j => congrFun he j
  simp only [h1, hw]

theorem chartSite_congr {β : ℝ} {e e' : ι → Fin N → ℂ} {H H' : Matrix ι ι ℂ}
    {g g' w w' : ι × Fin N → ℂ} (x : ι) (NB : Finset ι) (hx : x ∈ NB)
    (hH : ∀ y, H x y ≠ 0 → y ∈ NB) (hHH : ∀ y, H x y = H' x y)
    (hg : ∀ i, g (x, i) = g' (x, i)) (he : ∀ y ∈ NB, e y = e' y)
    (hw : ∀ y ∈ NB, ∀ i, w (y, i) = w' (y, i)) :
    chartSite β e H g w x = chartSite β e' H' g' w' x := by
  have hv : ∀ y ∈ NB, ∀ i, chartTangent e w (y, i) = chartTangent e' w' (y, i) :=
    fun y hy i => chartTangent_congr (he y hy) (hw y hy) i
  have hT : ∀ y ∈ NB, chartT β (chartTangent e w) y = chartT β (chartTangent e' w') y := by
    intro y hy
    unfold chartT
    simp only [hv y hy]
  have hz : ∀ y ∈ NB, ∀ i, chartZ β e (chartTangent e w) (y, i) =
      chartZ β e' (chartTangent e' w') (y, i) := by
    intro y hy i
    unfold chartZ
    simp only [hT y hy, he y hy]
  unfold chartSite
  simp only []
  have h1 : ∀ y, H x y * (∑ i, chartTangent e w (x, i) * chartZ β e (chartTangent e w) (y, i)) =
      H' x y * (∑ i, chartTangent e' w' (x, i) * chartZ β e' (chartTangent e' w') (y, i)) := by
    intro y
    by_cases h0 : H x y = 0
    · rw [h0, ← hHH y, h0]; simp
    · rw [← hHH y]
      simp only [hv x hx, hz y (hH y h0)]
  have h2 : ∀ y, H x y * (∑ i, chartZ β e (chartTangent e w) (x, i) *
      chartZ β e (chartTangent e w) (y, i)) =
      H' x y * (∑ i, chartZ β e' (chartTangent e' w') (x, i) *
        chartZ β e' (chartTangent e' w') (y, i)) := by
    intro y
    by_cases h0 : H x y = 0
    · rw [h0, ← hHH y, h0]; simp
    · rw [← hHH y]
      simp only [hz x hx, hz y (hH y h0)]
  rw [Finset.sum_congr rfl fun y _ => h1 y, Finset.sum_congr rfl fun y _ => h2 y]
  simp only [hT x hx, hv x hx, hz x hx, hg]

end Balaban.LargeField.Base
