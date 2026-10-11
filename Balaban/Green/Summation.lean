/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Topology.MetricSpace.HausdorffDistance

/-!
# The summation lemma for kernels with exponential tails (Lemma 4.10)

Let `ι` be a finite pseudometric space and `d : ι → ℝ` a nonnegative function with
`d x ≤ dist x z + d z` (for instance `d = setDist X'`, the distance to a set; for `X' = ∅` this is
`0` by the convention of `Metric.infDist`).  Lemma 4.10 of `notes/phase1/GREEN.md`:

* `Balaban.Green.sum_tail_le`: for `m ≤ μ`, `m ≤ δ`, `m > 0`,
  `∑_z ∑_w e^{-μ|x₁-z|} e^{-δ(d z + d w)} e^{-δ|z-w|} e^{-μ|w-x₂|}
     ≤ κ₁ κ_δ e^{-(m/2)(d x₁ + d x₂)}`;
* `Balaban.Green.sum_tail_sub_le`: the variant for `z` ranging over a set `Z` at distance
  `≥ D₁` from `x₁` and `≥ D₂` from `x₂` (no tail factors), giving `κ₁² e^{-(m/2)(D₁+D₂)}`.

Here `κ₁` bounds the ball sums `∑_y e^{-(m/2) dist x y}` and `κ_δ` the sums
`∑_w e^{-δ dist z w}`.
-/

@[expose] public section

open Finset

namespace Balaban.Green

/-- The distance to a set (`Metric.infDist`, which equals `⨅ x' ∈ X', dist x x'` for `X'`
nonempty and `0` for `X' = ∅`). -/
noncomputable abbrev setDist {ι : Type*} [PseudoMetricSpace ι] (X : Set ι) (x : ι) : ℝ :=
  Metric.infDist x X

section Aux

lemma setDist_nonneg {ι : Type*} [PseudoMetricSpace ι] (X : Set ι) (x : ι) : 0 ≤ setDist X x :=
  Metric.infDist_nonneg

lemma setDist_le_dist {ι : Type*} [PseudoMetricSpace ι] {X : Set ι} {x y : ι} (hy : y ∈ X) :
    setDist X x ≤ dist x y :=
  Metric.infDist_le_dist_of_mem hy

lemma setDist_le_dist_add {ι : Type*} [PseudoMetricSpace ι] (X : Set ι) (x z : ι) :
    setDist X x ≤ dist x z + setDist X z := by
  have := Metric.infDist_le_infDist_add_dist (x := x) (y := z) (s := X)
  linarith

lemma setDist_eq_zero_of_mem {ι : Type*} [PseudoMetricSpace ι] {X : Set ι} {x : ι} (hx : x ∈ X) :
    setDist X x = 0 := by
  have := setDist_le_dist (X := X) (x := x) hx
  simp only [dist_self] at this
  exact le_antisymm this (setDist_nonneg _ _)

/-- Splitting a two-rate exponential: if `D ≤ a + e` then
`e^{-μ a} e^{-δ e} ≤ e^{-(m/2) D} e^{-(m/2)(a+e)}`. -/
lemma exp_tail_aux {μ δ m a e D : ℝ} (hm : 0 < m) (hμ : m ≤ μ) (hδ : m ≤ δ) (ha : 0 ≤ a)
    (he : 0 ≤ e) (hD : D ≤ a + e) :
    Real.exp (-μ * a) * Real.exp (-δ * e) ≤
      Real.exp (-(m / 2) * D) * Real.exp (-(m / 2) * (a + e)) := by
  rw [← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp.2
  nlinarith [mul_le_mul_of_nonneg_right hμ ha, mul_le_mul_of_nonneg_right hδ he,
    mul_le_mul_of_nonneg_left hD hm.le]

end Aux

variable {ι : Type*} [Fintype ι] [PseudoMetricSpace ι]

/-- **Lemma 4.10 (summation with exponential tails).** -/
theorem sum_tail_le {μ δ m κ₁ κδ : ℝ} (hm : 0 < m) (hμ : m ≤ μ) (hδ : m ≤ δ)
    (hκδ : 0 ≤ κδ)
    (hK₁ : ∀ x : ι, ∑ y, Real.exp (-(m / 2) * dist x y) ≤ κ₁)
    (hKδ : ∀ z : ι, ∑ w, Real.exp (-δ * dist z w) ≤ κδ)
    {d : ι → ℝ} (hd0 : ∀ z, 0 ≤ d z) (hd1 : ∀ x z, d x ≤ dist x z + d z) (x₁ x₂ : ι) :
    ∑ z, ∑ w, Real.exp (-μ * dist x₁ z) * (Real.exp (-δ * (d z + d w)) *
        Real.exp (-δ * dist z w)) * Real.exp (-μ * dist w x₂)
      ≤ κ₁ * κδ * Real.exp (-(m / 2) * (d x₁ + d x₂)) := by
  have hpt : ∀ z w, Real.exp (-μ * dist x₁ z) * (Real.exp (-δ * (d z + d w)) *
        Real.exp (-δ * dist z w)) * Real.exp (-μ * dist w x₂)
      ≤ Real.exp (-(m / 2) * (d x₁ + d x₂)) *
        (Real.exp (-(m / 2) * dist x₁ z) * Real.exp (-δ * dist z w)) := by
    intro z w
    have h1 := exp_tail_aux (μ := μ) (δ := δ) hm hμ hδ (dist_nonneg (x := x₁) (y := z))
      (hd0 z) (hd1 x₁ z)
    have h2 := exp_tail_aux (μ := μ) (δ := δ) hm hμ hδ (dist_nonneg (x := w) (y := x₂))
      (hd0 w) (show d x₂ ≤ dist w x₂ + d w by
        have := hd1 x₂ w; rwa [dist_comm] at this)
    have h3 : Real.exp (-(m / 2) * (dist w x₂ + d w)) ≤ 1 :=
      Real.exp_le_one_iff.2 (by nlinarith [dist_nonneg (x := w) (y := x₂), hd0 w])
    have h4 : Real.exp (-(m / 2) * (dist x₁ z + d z)) ≤ Real.exp (-(m / 2) * dist x₁ z) :=
      Real.exp_le_exp.2 (by nlinarith [hd0 z])
    have h2' : Real.exp (-μ * dist w x₂) * Real.exp (-δ * d w) ≤ Real.exp (-(m / 2) * d x₂) :=
      h2.trans (by
        calc _ ≤ Real.exp (-(m / 2) * d x₂) * 1 := mul_le_mul_of_nonneg_left h3 (Real.exp_pos _).le
          _ = _ := mul_one _)
    have h1' : Real.exp (-μ * dist x₁ z) * Real.exp (-δ * d z) ≤
        Real.exp (-(m / 2) * d x₁) * Real.exp (-(m / 2) * dist x₁ z) :=
      h1.trans (mul_le_mul_of_nonneg_left h4 (Real.exp_pos _).le)
    have e1 : Real.exp (-δ * (d z + d w)) = Real.exp (-δ * d z) * Real.exp (-δ * d w) := by
      rw [← Real.exp_add]; ring_nf
    have e2 : Real.exp (-(m / 2) * (d x₁ + d x₂)) =
        Real.exp (-(m / 2) * d x₁) * Real.exp (-(m / 2) * d x₂) := by
      rw [← Real.exp_add]; ring_nf
    rw [e1, e2]
    have p1 := (Real.exp_pos (-δ * dist z w)).le
    calc _ = (Real.exp (-μ * dist x₁ z) * Real.exp (-δ * d z)) *
          (Real.exp (-μ * dist w x₂) * Real.exp (-δ * d w)) * Real.exp (-δ * dist z w) := by ring
      _ ≤ (Real.exp (-(m / 2) * d x₁) * Real.exp (-(m / 2) * dist x₁ z)) *
          Real.exp (-(m / 2) * d x₂) * Real.exp (-δ * dist z w) := by
        gcongr
      _ = _ := by ring
  calc _ ≤ ∑ z, ∑ w, Real.exp (-(m / 2) * (d x₁ + d x₂)) *
        (Real.exp (-(m / 2) * dist x₁ z) * Real.exp (-δ * dist z w)) :=
        Finset.sum_le_sum fun z _ => Finset.sum_le_sum fun w _ => hpt z w
    _ = Real.exp (-(m / 2) * (d x₁ + d x₂)) *
        ∑ z, Real.exp (-(m / 2) * dist x₁ z) * ∑ w, Real.exp (-δ * dist z w) := by
        simp only [Finset.mul_sum]
    _ ≤ Real.exp (-(m / 2) * (d x₁ + d x₂)) * ∑ z, Real.exp (-(m / 2) * dist x₁ z) * κδ := by
        gcongr with z _
        exact hKδ z
    _ ≤ Real.exp (-(m / 2) * (d x₁ + d x₂)) * (κ₁ * κδ) := by
        rw [← Finset.sum_mul]
        gcongr
        exact hK₁ x₁
    _ = _ := by ring

/-- **Lemma 4.10, variant** (the two lines added for G-4(b)): for `z` ranging over a set `Z`
with `D₁ ≤ dist x₁ z`, `D₂ ≤ dist x₂ z` and `w` over a set `W`, no tail weights on `z`, `w`. -/
theorem sum_tail_sub_le {μ δ m κ₁ : ℝ} (hm : 0 < m) (hμ : m ≤ μ) (hδ : m ≤ δ) (hκ₁ : 0 ≤ κ₁)
    (hK₁ : ∀ x : ι, ∑ y, Real.exp (-(m / 2) * dist x y) ≤ κ₁)
    (Z W : Finset ι) {D₁ D₂ : ℝ} {x₁ x₂ : ι}
    (hZ₁ : ∀ z ∈ Z, D₁ ≤ dist x₁ z) (hZ₂ : ∀ z ∈ Z, D₂ ≤ dist x₂ z) :
    ∑ z ∈ Z, ∑ w ∈ W, Real.exp (-μ * dist x₁ z) * Real.exp (-δ * dist z w) *
        Real.exp (-μ * dist w x₂)
      ≤ κ₁ * κ₁ * Real.exp (-(m / 2) * (D₁ + D₂)) := by
  have hpt : ∀ z ∈ Z, ∀ w ∈ W, Real.exp (-μ * dist x₁ z) * Real.exp (-δ * dist z w) *
        Real.exp (-μ * dist w x₂)
      ≤ Real.exp (-(m / 2) * (D₁ + D₂)) *
        (Real.exp (-(m / 2) * dist x₁ z) * Real.exp (-(m / 2) * dist z w)) := by
    intro z hz w _
    have hz1 := hZ₁ z hz
    have hz2 := hZ₂ z hz
    have h1 : Real.exp (-μ * dist x₁ z) ≤
        Real.exp (-(m / 2) * D₁) * Real.exp (-(m / 2) * dist x₁ z) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.2
      nlinarith [mul_le_mul_of_nonneg_right hμ (dist_nonneg (x := x₁) (y := z)),
        mul_le_mul_of_nonneg_left hz1 hm.le]
    have h2 := exp_tail_aux (μ := μ) (δ := δ) hm hμ hδ (dist_nonneg (x := w) (y := x₂))
      (dist_nonneg (x := z) (y := w))
      (show D₂ ≤ dist w x₂ + dist z w by
        have := dist_triangle x₂ w z
        rw [dist_comm x₂ w, dist_comm x₂ z] at *
        rw [dist_comm w z] at this
        linarith)
    have h3 : Real.exp (-(m / 2) * (dist w x₂ + dist z w)) ≤ Real.exp (-(m / 2) * dist z w) :=
      Real.exp_le_exp.2 (by nlinarith [dist_nonneg (x := w) (y := x₂)])
    have h2' : Real.exp (-μ * dist w x₂) * Real.exp (-δ * dist z w) ≤
        Real.exp (-(m / 2) * D₂) * Real.exp (-(m / 2) * dist z w) :=
      h2.trans (mul_le_mul_of_nonneg_left h3 (Real.exp_pos _).le)
    have e2 : Real.exp (-(m / 2) * (D₁ + D₂)) =
        Real.exp (-(m / 2) * D₁) * Real.exp (-(m / 2) * D₂) := by
      rw [← Real.exp_add]; ring_nf
    rw [e2]
    calc _ = Real.exp (-μ * dist x₁ z) *
          (Real.exp (-μ * dist w x₂) * Real.exp (-δ * dist z w)) := by ring
      _ ≤ (Real.exp (-(m / 2) * D₁) * Real.exp (-(m / 2) * dist x₁ z)) *
          (Real.exp (-(m / 2) * D₂) * Real.exp (-(m / 2) * dist z w)) := by gcongr
      _ = _ := by ring
  have hW : ∀ z, ∑ w ∈ W, Real.exp (-(m / 2) * dist z w) ≤ κ₁ := fun z =>
    (Finset.sum_le_univ_sum_of_nonneg fun _ => (Real.exp_pos _).le).trans (hK₁ z)
  calc _ ≤ ∑ z ∈ Z, ∑ w ∈ W, Real.exp (-(m / 2) * (D₁ + D₂)) *
        (Real.exp (-(m / 2) * dist x₁ z) * Real.exp (-(m / 2) * dist z w)) :=
        Finset.sum_le_sum fun z hz => Finset.sum_le_sum fun w hw => hpt z hz w hw
    _ = Real.exp (-(m / 2) * (D₁ + D₂)) *
        ∑ z ∈ Z, Real.exp (-(m / 2) * dist x₁ z) * ∑ w ∈ W, Real.exp (-(m / 2) * dist z w) := by
        simp only [Finset.mul_sum]
    _ ≤ Real.exp (-(m / 2) * (D₁ + D₂)) * ∑ z ∈ Z, Real.exp (-(m / 2) * dist x₁ z) * κ₁ := by
        gcongr with z _
        exact hW z
    _ ≤ Real.exp (-(m / 2) * (D₁ + D₂)) * (κ₁ * κ₁) := by
        rw [← Finset.sum_mul]
        gcongr
        exact (Finset.sum_le_univ_sum_of_nonneg fun _ => (Real.exp_pos _).le).trans (hK₁ x₁)
    _ = _ := by ring

end Balaban.Green
