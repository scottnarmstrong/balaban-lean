/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Multiscale.ConstraintGrad
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The constraint field `φ₀` and its hypotheses (GREEN.md G-2(v))

* `Balaban.Multiscale.vn`: the Euclidean norm on `ℂ^N`;
* `Balaban.Multiscale.IsConstraintField G δ φ`: the hypotheses of G-2(v) on a field
  `φ₀ : Torus → ℂ^N` (defined on the torus, so that its differences at points of `Ω₁` make sense):
  `|φ₀| ≤ 3/2`, `|φ₀ · φ₀ - 1| ≤ δ`, `ℓ(x) |∂ φ₀| ≤ δ` along every bond at a point `x ∈ Ω₁`, and
  `ℓ(x)² |Δ φ₀(x)| ≤ δ` for `x ∈ Ω₁` (P3 (3.2), P2 (3.21): `|∂φ₀|₁ < δ₀`, `|Δφ₀|₂ < δ₀`);
* `Balaban.Multiscale.IsConstraintField.osc_block`: the oscillation of `φ₀` on a block of its layer
  is at most `2 d δ` (path argument through the multiscale metric).
-/

@[expose] public section

namespace Balaban.Multiscale

open Matrix Finset

section Vec

variable {N : ℕ}

/-- The Euclidean norm of a vector in `ℂ^N`. -/
noncomputable def vn (v : Fin N → ℂ) : ℝ := ‖(WithLp.toLp 2 v : EuclideanSpace ℂ (Fin N))‖

theorem vn_nonneg (v : Fin N → ℂ) : 0 ≤ vn v := norm_nonneg _

theorem vn_sq (v : Fin N → ℂ) : vn v ^ 2 = ∑ i, ‖v i‖ ^ 2 := by
  unfold vn
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]

theorem vn_add (v w : Fin N → ℂ) : vn (v + w) ≤ vn v + vn w :=
  norm_add_le (WithLp.toLp 2 v : EuclideanSpace ℂ (Fin N)) (WithLp.toLp 2 w)

theorem vn_sub_comm (v w : Fin N → ℂ) : vn (v - w) = vn (w - v) := by
  unfold vn
  exact norm_sub_rev (WithLp.toLp 2 v : EuclideanSpace ℂ (Fin N)) (WithLp.toLp 2 w)

theorem vn_triangle (u v w : Fin N → ℂ) : vn (u - w) ≤ vn (u - v) + vn (v - w) := by
  have h := vn_add (u - v) (v - w)
  have e : u - v + (v - w) = u - w := by abel
  rwa [e] at h

theorem norm_le_vn (v : Fin N → ℂ) (i : Fin N) : ‖v i‖ ≤ vn v := by
  have h : ‖v i‖ ^ 2 ≤ vn v ^ 2 := by
    rw [vn_sq]
    exact Finset.single_le_sum (f := fun i => ‖v i‖ ^ 2) (fun _ _ => sq_nonneg _)
      (Finset.mem_univ i)
  exact le_of_sq_le_sq h (vn_nonneg v) |>.trans_eq rfl

theorem vn_eq_sqrt (v : Fin N → ℂ) : vn v = Real.sqrt (∑ i, ‖v i‖ ^ 2) := by
  rw [← vn_sq, Real.sqrt_sq (vn_nonneg v)]

/-- Cauchy–Schwarz for the bilinear dot product. -/
theorem norm_dot_le (a b : Fin N → ℂ) : ‖∑ i, a i * b i‖ ≤ vn a * vn b := by
  calc ‖∑ i, a i * b i‖ ≤ ∑ i, ‖a i * b i‖ := norm_sum_le _ _
    _ = ∑ i, ‖a i‖ * ‖b i‖ := Finset.sum_congr rfl fun i _ => norm_mul _ _
    _ ≤ Real.sqrt (∑ i, ‖a i‖ ^ 2) * Real.sqrt (∑ i, ‖b i‖ ^ 2) :=
        Real.sum_mul_le_sqrt_mul_sqrt _ _ _
    _ = vn a * vn b := by rw [vn_eq_sqrt a, vn_eq_sqrt b]

theorem vn_zero : vn (0 : Fin N → ℂ) = 0 := by
  unfold vn
  simp

end Vec

section Field

variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}

/-- The hypotheses of G-2(v) on the constraint field `φ₀ : Torus → ℂ^N` (smallness `δ`):
`|φ₀| ≤ 3/2`, `|φ₀ · φ₀ - 1| ≤ δ`, `ℓ |∂ φ₀| ≤ δ` on bonds at points of `Ω₁` and
`ℓ² |Δ φ₀| ≤ δ` at points of `Ω₁` (Euclidean norms in `ℂ^N`, bilinear square `φ₀ · φ₀`). -/
structure IsConstraintField (G : GeneratingSet d L N₀ k ϱ) (δ : ℝ)
    (φ : Torus d (N₀ * L ^ k) → Fin N → ℂ) : Prop where
  grad : ∀ x ∈ G.Ω 1, ∀ μ : Fin d,
    vn (φ (x + Pi.single μ 1) - φ x) ≤ δ / G.spacing x ∧
      vn (φ (x - Pi.single μ 1) - φ x) ≤ δ / G.spacing x
  lap : ∀ x ∈ G.Ω 1,
    vn (fun i => ∑ μ : Fin d, (φ (x + Pi.single μ 1) i + φ (x - Pi.single μ 1) i - 2 * φ x i)) ≤
      δ / G.spacing x ^ 2
  bound : ∀ x ∈ G.Ω 1, vn (φ x) ≤ 3 / 2
  sq : ∀ x ∈ G.Ω 1, ‖∑ i, φ x i * φ x i - 1‖ ≤ δ

namespace IsConstraintField

variable {G : GeneratingSet d L N₀ k ϱ} {δ : ℝ} {φ : Torus d (N₀ * L ^ k) → Fin N → ℂ}

theorem delta_nonneg (hφ : IsConstraintField G δ φ) (hΩ : (G.Ω 1).Nonempty) : 0 ≤ δ := by
  obtain ⟨x, hx⟩ := hΩ
  exact (norm_nonneg _).trans (hφ.sq x hx)

theorem adj_bound (hφ : IsConstraintField G δ φ) {x x' : Torus d (N₀ * L ^ k)}
    (hx : x ∈ G.Ω 1) (hx' : x' ∈ G.Ω 1) (hadj : Adj x x') :
    vn (φ x' - φ x) ≤ δ * G.bondCost x x' := by
  have h1 : vn (φ x' - φ x) ≤ δ / G.spacing x ∧ vn (φ x' - φ x) ≤ δ / G.spacing x' := by
    obtain ⟨μ, h | h⟩ := hadj
    · refine ⟨?_, ?_⟩
      · rw [h]; exact (hφ.grad x hx μ).1
      · have := (hφ.grad x' hx' μ).2
        rw [vn_sub_comm]
        have e : x' - Pi.single μ 1 = x := by rw [h]; simp
        rwa [e] at this
    · refine ⟨?_, ?_⟩
      · have := (hφ.grad x hx μ).2
        have e : x - Pi.single μ 1 = x' := by rw [h]; simp
        rwa [e] at this
      · have := (hφ.grad x' hx' μ).1
        rw [vn_sub_comm]
        have e : x' + Pi.single μ 1 = x := by rw [h]
        rwa [e] at this
  unfold GeneratingSet.bondCost
  rw [mul_one_div]
  rcases le_total (G.spacing x') (G.spacing x) with h | h
  · rw [max_eq_left h]; exact h1.1
  · rw [max_eq_right h]; exact h1.2

theorem pathCost_bound (hφ : IsConstraintField G δ φ) {x y : Torus d (N₀ * L ^ k)} {c : ℝ}
    (h : G.PathCost x y c) : vn (φ y - φ x) ≤ δ * c := by
  induction h with
  | refl x hx => simp [vn_zero]
  | step x y z c hx hadj hp ih =>
      have h1 := hφ.adj_bound hx hp.left_mem hadj
      have h2 := vn_triangle (φ z) (φ y) (φ x)
      rw [mul_add]
      linarith

/-- **Oscillation on a block** (the source's `osc_B φ₀ ≤ d δ₀`; constant `2 d` from the corner
paths): two points of a `j`-block of layer `j` have `|φ₀(x') - φ₀(x)| ≤ 2 d δ`. -/
theorem osc_block (hφ : IsConstraintField G δ φ) (hδ : 0 ≤ δ) {j : ℕ} (hj : 1 ≤ j) (hjk : j ≤ k)
    {x x' : Torus d (N₀ * L ^ k)} (hx : x ∈ G.layer j)
    (h : jBlock d L N₀ k j x' = jBlock d L N₀ k j x) : vn (φ x' - φ x) ≤ 2 * d * δ := by
  have hpd := G.pathDist_block_le hj hjk hx h
  by_contra hcon
  push Not at hcon
  set gap := vn (φ x' - φ x) - 2 * d * δ with hgap
  have hgap0 : 0 < gap := by linarith
  set η := gap / (δ + 1) with hη
  have hη0 : 0 < η := by positivity
  have hlt : G.pathDist x x' < ENNReal.ofReal (2 * d + η) := by
    refine lt_of_le_of_lt hpd ?_
    rw [ENNReal.ofReal_lt_ofReal_iff (by positivity)]
    linarith
  unfold GeneratingSet.pathDist at hlt
  rw [iInf_lt_iff] at hlt
  obtain ⟨c, hc⟩ := hlt
  rw [iInf_lt_iff] at hc
  obtain ⟨hpc, hc⟩ := hc
  have hc' : c < 2 * d + η := by
    have hc0 := hpc.nonneg
    rwa [ENNReal.ofReal_lt_ofReal_iff (by positivity)] at hc
  have hb := hφ.pathCost_bound hpc
  have : δ * c ≤ δ * (2 * d + η) := mul_le_mul_of_nonneg_left hc'.le hδ
  have hδη : δ * η < gap := by
    rw [hη, mul_div_assoc']
    rw [div_lt_iff₀ (by positivity)]
    nlinarith
  nlinarith

end IsConstraintField

end Field

end Balaban.Multiscale
