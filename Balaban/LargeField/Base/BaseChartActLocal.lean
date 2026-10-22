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

theorem chartTangent_cross {ι' : Type*} [Fintype ι'] [DecidableEq ι'] {e : ι → Fin N → ℂ}
    {e' : ι' → Fin N → ℂ} {w : ι × Fin N → ℂ} {w' : ι' × Fin N → ℂ} {y : ι} {y' : ι'}
    (he : e' y' = e y) (hw : ∀ i, w' (y', i) = w (y, i)) (i : Fin N) :
    chartTangent e' w' (y', i) = chartTangent e w (y, i) := by
  rw [chartTangent_apply, chartTangent_apply]
  have h1 : ∀ j, e' y' j = e y j := fun j => congrFun he j
  simp only [h1, hw]

/-- **The site exponent reads a finite neighbourhood of the site, across two index sets.**  Let
`j : ι → ι'` be injective on a set `NB ∋ x` that contains the support of the row `H x ·` and such that
the support of the row `H' (j x) ·` lies in the image of `NB`.  If the data `e`, `w`, `H`, `g` at the sites of
`NB` correspond under `j`, then `V_{j x}` for the primed data equals `V_x`. -/
theorem chartSite_cross {ι' : Type*} [Fintype ι'] [DecidableEq ι'] {β : ℝ} {e : ι → Fin N → ℂ}
    {e' : ι' → Fin N → ℂ} {H : Matrix ι ι ℂ} {H' : Matrix ι' ι' ℂ} {g w : ι × Fin N → ℂ}
    {g' w' : ι' × Fin N → ℂ} (j : ι → ι') (x : ι) (NB : Finset ι) (hx : x ∈ NB)
    (hj : Set.InjOn j (NB : Set ι)) (hH : ∀ y, H x y ≠ 0 → y ∈ NB)
    (hH' : ∀ y', H' (j x) y' ≠ 0 → y' ∈ NB.image j) (hHH : ∀ y ∈ NB, H' (j x) (j y) = H x y)
    (hg : ∀ i, g' (j x, i) = g (x, i)) (he : ∀ y ∈ NB, e' (j y) = e y)
    (hw : ∀ y ∈ NB, ∀ i, w' (j y, i) = w (y, i)) :
    chartSite β e' H' g' w' (j x) = chartSite β e H g w x := by
  classical
  have hv : ∀ y ∈ NB, ∀ i, chartTangent e' w' (j y, i) = chartTangent e w (y, i) :=
    fun y hy i => chartTangent_cross (he y hy) (hw y hy) i
  have hT : ∀ y ∈ NB, chartT β (chartTangent e' w') (j y) = chartT β (chartTangent e w) y := by
    intro y hy
    unfold chartT
    simp only [hv y hy]
  have hz : ∀ y ∈ NB, ∀ i, chartZ β e' (chartTangent e' w') (j y, i) =
      chartZ β e (chartTangent e w) (y, i) := by
    intro y hy i
    unfold chartZ
    simp only [hT y hy, he y hy]
  -- the sums over the index sets reduce to `NB` and its image
  have hsum' : ∀ f : ι' → ℂ, ∑ y', H' (j x) y' * f y' = ∑ y ∈ NB, H' (j x) (j y) * f (j y) := by
    intro f
    rw [← Finset.sum_image (f := fun y' => H' (j x) y' * f y') (g := j)
      (fun a ha b hb hab => hj ha hb hab)]
    refine (Finset.sum_subset (Finset.subset_univ (NB.image j)) (fun y' _ hy' => ?_)).symm
    have h0 : H' (j x) y' = 0 := by
      by_contra h
      exact hy' (hH' y' h)
    simp [h0]
  have hsum : ∀ f : ι → ℂ, ∑ y, H x y * f y = ∑ y ∈ NB, H x y * f y := by
    intro f
    refine (Finset.sum_subset (Finset.subset_univ NB) (fun y _ hy => ?_)).symm
    have h0 : H x y = 0 := by
      by_contra h
      exact hy (hH y h)
    simp [h0]
  have h1 : ∑ y', H' (j x) y' * (∑ i, chartTangent e' w' (j x, i) *
      chartZ β e' (chartTangent e' w') (y', i)) =
      ∑ y, H x y * (∑ i, chartTangent e w (x, i) * chartZ β e (chartTangent e w) (y, i)) := by
    rw [hsum', hsum]
    refine Finset.sum_congr rfl fun y hy => ?_
    rw [hHH y hy]
    simp only [hv x hx, hz y hy]
  have h2 : ∑ y', H' (j x) y' * (∑ i, chartZ β e' (chartTangent e' w') (j x, i) *
      chartZ β e' (chartTangent e' w') (y', i)) =
      ∑ y, H x y * (∑ i, chartZ β e (chartTangent e w) (x, i) *
        chartZ β e (chartTangent e w) (y, i)) := by
    rw [hsum', hsum]
    refine Finset.sum_congr rfl fun y hy => ?_
    rw [hHH y hy]
    simp only [hz x hx, hz y hy]
  unfold chartSite
  simp only []
  rw [h1, h2]
  simp only [hT x hx, hv x hx, hz x hx, hg]

theorem chartSite_congr {β : ℝ} {e e' : ι → Fin N → ℂ} {H H' : Matrix ι ι ℂ}
    {g g' w w' : ι × Fin N → ℂ} (x : ι) (NB : Finset ι) (hx : x ∈ NB)
    (hH : ∀ y, H x y ≠ 0 → y ∈ NB) (hHH : ∀ y, H x y = H' x y)
    (hg : ∀ i, g (x, i) = g' (x, i)) (he : ∀ y ∈ NB, e y = e' y)
    (hw : ∀ y ∈ NB, ∀ i, w (y, i) = w' (y, i)) :
    chartSite β e H g w x = chartSite β e' H' g' w' x :=
  (chartSite_cross (e := e) (e' := e') (H := H) (H' := H') (g := g) (g' := g') (w := w) (w' := w')
    id x NB hx (Set.injOn_id _) hH (fun y' h0 => by
      rw [Finset.image_id]; exact hH y' (by rw [hHH y']; exact h0))
    (fun y _ => (hHH y).symm) (fun i => (hg i).symm) (fun y hy => (he y hy).symm)
    (fun y hy i => (hw y hy i).symm)).symm

end Balaban.LargeField.Base
