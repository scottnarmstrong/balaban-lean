/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Background.Theorem52
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Algebra for the minimizer identity (5.3): block sums, lattice summation by parts

* `blk_sum_comm`: for a function `g` constant on blocks, `∑_x w_x g(x) (Q u)(x) = ∑_x w_x g(x) u(x)`
  (the block averaging `Q` is self-adjoint and idempotent);
* `bond_sum_by_parts`: `∑_x ∑_μ (v(x+e) - v(x))(w(x+e) - w(x)) = ∑_x w(x) ∑_μ (2v(x) - v(x+e) - v(x-e))`
  on the torus.
-/

@[expose] public section

namespace Balaban.Background

open Balaban.Multiscale Matrix Finset

variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}

section Block

variable (G : GeneratingSet d L N₀ k ϱ)

/-- `y ∈ B_n(x)` for `x ∈ Ω₁` iff `y ∈ Ω₁`, `ℓ(y) = ℓ(x)` and `x ∈ B_n(y)`. -/
theorem mem_blk_iff {x y : Torus d (N₀ * L ^ k)} (hx : x ∈ G.Ω 1) :
    y ∈ G.blk (G.layerIndex x) x ↔
      y ∈ G.Ω 1 ∧ G.layerIndex y = G.layerIndex x ∧ x ∈ G.blk (G.layerIndex y) y := by
  obtain ⟨hn1, hnk, hxl⟩ := G.layerIndex_spec hx
  constructor
  · intro hy
    have hyl := mem_layer_of_mem_blk G hn1 hnk hxl hy
    have hly : G.layerIndex y = G.layerIndex x := G.layerIndex_eq hn1 hnk hyl
    refine ⟨G.layer_subset hn1 hnk hyl, hly, ?_⟩
    rw [hly, GeneratingSet.mem_blk]
    exact (GeneratingSet.mem_blk.1 hy).symm
  · rintro ⟨-, hly, hxy⟩
    rw [hly] at hxy
    rw [GeneratingSet.mem_blk]
    exact (GeneratingSet.mem_blk.1 hxy).symm

/-- **Block sums**: for `g` constant on blocks, `∑_x w_x g(x) (Q u)(x) = ∑_x w_x g(x) u(x)`
(`w_x = a_n L^{-2n}`, `Q u (x) = L^{-nd} ∑_{y ∈ B_n(x)} u(y)`). -/
theorem blk_sum_comm (a : ℕ → ℝ) (g u : Torus d (N₀ * L ^ k) → ℂ)
    (hg : ∀ x ∈ G.Ω 1, ∀ y ∈ G.blk (G.layerIndex x) x, g y = g x) :
    ∑ x : G.Ω 1, ((a (G.layerIndex x.1) / ((L : ℝ) ^ G.layerIndex x.1) ^ 2 : ℝ) : ℂ) * g x.1 *
      ((((((L : ℝ) ^ G.layerIndex x.1) ^ d)⁻¹ : ℝ) : ℂ) *
        ∑ y ∈ G.blk (G.layerIndex x.1) x.1, u y) =
    ∑ x : G.Ω 1, ((a (G.layerIndex x.1) / ((L : ℝ) ^ G.layerIndex x.1) ^ 2 : ℝ) : ℂ) * g x.1 *
      u x.1 := by
  classical
  rw [Finset.sum_coe_sort (G.Ω 1) (fun x => ((a (G.layerIndex x) / ((L : ℝ) ^ G.layerIndex x) ^ 2 : ℝ) : ℂ) *
      g x * ((((((L : ℝ) ^ G.layerIndex x) ^ d)⁻¹ : ℝ) : ℂ) * ∑ y ∈ G.blk (G.layerIndex x) x, u y)),
    Finset.sum_coe_sort (G.Ω 1) (fun x => ((a (G.layerIndex x) / ((L : ℝ) ^ G.layerIndex x) ^ 2 : ℝ) : ℂ) *
      g x * u x)]
  have e1 : ∀ x ∈ G.Ω 1, ((a (G.layerIndex x) / ((L : ℝ) ^ G.layerIndex x) ^ 2 : ℝ) : ℂ) *
      g x * ((((((L : ℝ) ^ G.layerIndex x) ^ d)⁻¹ : ℝ) : ℂ) * ∑ y ∈ G.blk (G.layerIndex x) x, u y) =
      ∑ y ∈ G.blk (G.layerIndex x) x, (((a (G.layerIndex x) / ((L : ℝ) ^ G.layerIndex x) ^ 2 : ℝ) : ℂ) *
      g x * (((((L : ℝ) ^ G.layerIndex x) ^ d)⁻¹ : ℝ) : ℂ)) * u y := by
    intro x _
    rw [Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun y _ => by ring
  rw [Finset.sum_congr rfl e1]
  rw [Finset.sum_comm' (s' := fun y => G.blk (G.layerIndex y) y) (t' := G.Ω 1)
    (fun x y => by
      constructor
      · rintro ⟨hx, hy⟩
        have := (mem_blk_iff G hx).1 hy
        exact ⟨this.2.2, this.1⟩
      · rintro ⟨hxy, hy⟩
        have := (mem_blk_iff G hy).1 hxy
        exact ⟨this.1, this.2.2⟩)]
  refine Finset.sum_congr rfl fun y hy => ?_
  have hy1 := G.layerIndex_spec hy
  have e2 : ∀ x ∈ G.blk (G.layerIndex y) y,
      ((a (G.layerIndex x) / ((L : ℝ) ^ G.layerIndex x) ^ 2 : ℝ) : ℂ) * g x *
        (((((L : ℝ) ^ G.layerIndex x) ^ d)⁻¹ : ℝ) : ℂ) * u y =
      ((a (G.layerIndex y) / ((L : ℝ) ^ G.layerIndex y) ^ 2 : ℝ) : ℂ) * g y *
        (((((L : ℝ) ^ G.layerIndex y) ^ d)⁻¹ : ℝ) : ℂ) * u y := by
    intro x hx
    have h := (mem_blk_iff G hy).1 hx
    rw [h.2.1, hg y hy x hx]
  rw [Finset.sum_congr rfl e2, Finset.sum_const, nsmul_eq_mul]
  have hcard := card_blk_cast G (G.layerIndex y) hy1.2.1 y
  have hc : ((G.blk (G.layerIndex y) y).card : ℂ) =
      ((((L : ℝ) ^ G.layerIndex y) ^ d : ℝ) : ℂ) := by exact_mod_cast hcard
  rw [hc]
  have hne : ((((L : ℝ) ^ G.layerIndex y) ^ d : ℝ) : ℂ) ≠ 0 := by
    have : (0 : ℝ) < ((L : ℝ) ^ G.layerIndex y) ^ d := by
      have : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
      positivity
    exact_mod_cast this.ne'
  have hinv : (((((L : ℝ) ^ G.layerIndex y) ^ d)⁻¹ : ℝ) : ℂ) =
      ((((L : ℝ) ^ G.layerIndex y) ^ d : ℝ) : ℂ)⁻¹ := by push_cast; rfl
  rw [hinv]
  field_simp

end Block

section Bonds

variable {ℓ : ℕ} [NeZero ℓ]

theorem sum_shiftC (e : Torus d ℓ) (f : Torus d ℓ → ℂ) : ∑ x, f (x + e) = ∑ x, f x :=
  Equiv.sum_comp (Equiv.addRight e) f

/-- **Summation by parts on the torus** (complex-valued, bilinear):
`∑_x ∑_μ (v(x+e_μ) - v(x))(w(x+e_μ) - w(x)) = ∑_x w(x) ∑_μ (2 v(x) - v(x+e_μ) - v(x-e_μ))`. -/
theorem bond_sum_by_parts (v w : Torus d ℓ → ℂ) :
    ∑ x, ∑ μ : Fin d, (v (x + Pi.single μ 1) - v x) * (w (x + Pi.single μ 1) - w x) =
      ∑ x, w x * ∑ μ : Fin d, (2 * v x - v (x + Pi.single μ 1) - v (x - Pi.single μ 1)) := by
  have hR : ∑ x, w x * ∑ μ : Fin d, (2 * v x - v (x + Pi.single μ 1) - v (x - Pi.single μ 1)) =
      ∑ μ : Fin d, ∑ x, w x * (2 * v x - v (x + Pi.single μ 1) - v (x - Pi.single μ 1)) := by
    simp only [Finset.mul_sum]; exact Finset.sum_comm
  rw [Finset.sum_comm, hR]
  refine Finset.sum_congr rfl fun μ _ => ?_
  have h1 := sum_shiftC (Pi.single μ 1 : Torus d ℓ) (fun x => v x * w x)
  have h2 := sum_shiftC (Pi.single μ 1 : Torus d ℓ) (fun x => v (x - Pi.single μ 1) * w x)
  simp only [add_sub_cancel_right] at h2
  have e : ∀ x : Torus d ℓ, (v (x + Pi.single μ 1) - v x) * (w (x + Pi.single μ 1) - w x) =
      v (x + Pi.single μ 1) * w (x + Pi.single μ 1) + v x * w x -
        w x * v (x + Pi.single μ 1) - v x * w (x + Pi.single μ 1) := fun x => by ring
  simp only [e]
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_add_distrib, h1]
  have e3 : ∀ x : Torus d ℓ, w x * (2 * v x - v (x + Pi.single μ 1) - v (x - Pi.single μ 1)) =
      2 * (v x * w x) - w x * v (x + Pi.single μ 1) - v (x - Pi.single μ 1) * w x :=
    fun x => by ring
  simp only [e3]
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  have h3 : ∑ x : Torus d ℓ, v x * w (x + Pi.single μ 1) = ∑ x, v (x - Pi.single μ 1) * w x := h2
  rw [h3]
  ring

end Bonds

end Balaban.Background
