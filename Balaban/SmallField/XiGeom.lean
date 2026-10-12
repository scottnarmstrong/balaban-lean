/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.SmallField.Xi
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Block geometry for the spaces `Ξ` (oscillation, interface estimate)

Generic estimates for a vector field `f` with gradient bounds `|∂f| ≤ A / ℓ` (`IsSmoothField`),
used both for the real extension `φ̄` and for the difference `φ̄^c - φ̄^r` of the complex one:

* `Balaban.SmallField.mean_sub_le`: the block mean is within `2 d A` of the values in the block;
* `Balaban.SmallField.interface_gen`: the interface estimate (R1)/(C1) for a block-constant field
  `ψ` that is within `r` of the block means of `f` and equals `f` on the collar.
-/

@[expose] public section

namespace Balaban.SmallField

open Balaban.Background Balaban.Multiscale Matrix Finset

variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}

variable {G : GeneratingSet d L N₀ k ϱ}

omit [NeZero N₀] [NeZero L] in
/-- `vn u ≤ vn (u - v) + vn v`. -/
theorem vn_le_sub_add (u v : Fin N → ℂ) : vn u ≤ vn (fun i => u i - v i) + vn v := by
  have h := vn_add (fun i => u i - v i) v
  have e : ((fun i => u i - v i) + v) = u := by funext i; simp
  rw [e] at h
  exact h

omit [NeZero N₀] [NeZero L] in
/-- `vn (u - w) ≤ vn u + vn w`. -/
theorem vn_sub_le_add (u w : Fin N → ℂ) : vn (u - w) ≤ vn u + vn w := by
  have h := vn_triangle u 0 w
  rwa [sub_zero, vn_sub_comm 0 w, sub_zero] at h

omit [NeZero N₀] [NeZero L] in
/-- The triangle inequality for functions written with `fun`. -/
theorem vn_tri (u v w : Fin N → ℂ) :
    vn (fun i => u i - w i) ≤ vn (fun i => u i - v i) + vn (fun i => v i - w i) :=
  vn_triangle u v w

/-- The bond bound `A * bondCost` of a smooth field on `Ω₁`. -/
theorem smooth_bond {f : Torus d (N₀ * L ^ k) → Fin N → ℂ} {A : ℝ} (hs : IsSmoothField G A f) :
    ∀ x x' : Torus d (N₀ * L ^ k), x ∈ G.Ω 1 → x' ∈ G.Ω 1 → Adj x x' →
      vn (f x' - f x) ≤ A * G.bondCost x x' := fun _ _ hx hx' hadj => hs.adj_bound hx hx' hadj

/-- Two points of the same block of a site `x ∈ Ω₁` differ by at most `2 d A`. -/
theorem block_osc {f : Torus d (N₀ * L ^ k) → Fin N → ℂ} {A : ℝ} (hA : 0 ≤ A)
    (hs : IsSmoothField G A f) {x y y' : Torus d (N₀ * L ^ k)} (hx : x ∈ G.Ω 1)
    (hy : y ∈ G.blk (G.layerIndex x) x) (hy' : y' ∈ G.blk (G.layerIndex x) x) :
    vn (f y - f y') ≤ 2 * d * A := by
  obtain ⟨hn1, hnk, -⟩ := G.layerIndex_spec hx
  have hy'l := blk_mem_layer hx hy'
  refine vn_block_osc f hA (smooth_bond hs) hn1 hnk hy'l ?_
  rw [GeneratingSet.mem_blk.1 hy, GeneratingSet.mem_blk.1 hy']

/-- The block mean is within `2 d A` of the values of `f` in the block. -/
theorem mean_sub_le {f : Torus d (N₀ * L ^ k) → Fin N → ℂ} {A : ℝ} (hA : 0 ≤ A)
    (hs : IsSmoothField G A f) {x y : Torus d (N₀ * L ^ k)} (hx : x ∈ G.Ω 1)
    (hy : y ∈ G.blk (G.layerIndex x) x) :
    vn (fun i => blockMean G (G.layerIndex x) (fun y => f y i) x - f y i) ≤ 2 * d * A := by
  obtain ⟨-, hnk, -⟩ := G.layerIndex_spec hx
  exact vn_blockMean_sub_le (G := G) hnk f x (f y) (fun y' hy' => block_osc hA hs hx hy' hy)

/-- `ψ x` is within `r + 2 d A` of `f y` for `y` in the block of `x`. -/
theorem psi_sub_le {f ψ : Torus d (N₀ * L ^ k) → Fin N → ℂ} {A r : ℝ} (hA : 0 ≤ A)
    (hs : IsSmoothField G A f) {x y : Torus d (N₀ * L ^ k)} (hx : x ∈ G.Ω 1)
    (hmean : vn (fun i => ψ x i - blockMean G (G.layerIndex x) (fun y => f y i) x) ≤ r)
    (hy : y ∈ G.blk (G.layerIndex x) x) :
    vn (fun i => ψ x i - f y i) ≤ r + 2 * d * A := by
  have h := mean_sub_le hA hs hx hy
  have t := vn_triangle (fun i => ψ x i) (fun i => blockMean G (G.layerIndex x) (fun y => f y i) x)
    (fun i => f y i)
  have e1 : (fun i => ψ x i - blockMean G (G.layerIndex x) (fun y => f y i) x) =
      (fun i => ψ x i) - fun i => blockMean G (G.layerIndex x) (fun y => f y i) x := rfl
  have e2 : (fun i => blockMean G (G.layerIndex x) (fun y => f y i) x - f y i) =
      (fun i => blockMean G (G.layerIndex x) (fun y => f y i) x) - fun i => f y i := rfl
  have e3 : (fun i => ψ x i - f y i) = (fun i => ψ x i) - fun i => f y i := rfl
  rw [e1] at hmean
  rw [e2] at h
  rw [e3]
  linarith

/-- **The interface estimate** (R1)/(C1) (cf. `CompHyp.interface`): `ψ` within `r` of the block
means of the smooth field `f`, equal to `f` on the collar, with the data bound `A` across the bonds
of the collar. -/
theorem interface_gen {f ψ : Torus d (N₀ * L ^ k) → Fin N → ℂ} {A r : ℝ} (hA : 0 ≤ A)
    (hr0 : 0 ≤ r) (hs : IsSmoothField G A f)
    (hmean : ∀ x ∈ G.Ω 1, vn (fun i => ψ x i - blockMean G (G.layerIndex x) (fun y => f y i) x) ≤ r)
    (hcol : ∀ x ∈ collar G, ψ x = f x)
    (hcb : ∀ z ∈ collar G, ∀ z' ∈ collar G, Adj z z' → vn (ψ z - ψ z') ≤ A)
    {x x' : Torus d (N₀ * L ^ k)} (hxx' : IsInterfacePair G x x') :
    vn (ψ x - ψ x') ≤ 2 * (r + 2 * d * A) + A := by
  obtain ⟨hx, hx', -, z, hz, z', hz', hadj⟩ := hxx'
  have hr : 0 ≤ r + 2 * d * A := by positivity
  have key : ∀ {w w' : Torus d (N₀ * L ^ k)}, w ∈ dataSites G → w' ∈ blockSet G w →
      vn (fun i => ψ w i - f w' i) ≤ r + 2 * d * A := by
    intro w w' hw hw'
    rcases (mem_dataSites G).1 hw with hw1 | hw1
    · rw [blockSet_of_mem G hw1] at hw'
      exact psi_sub_le hA hs hw1 (hmean w hw1) hw'
    · have hn : w ∉ G.Ω 1 := ((mem_collar G).1 hw1).1
      rw [blockSet_of_not_mem G hn, Finset.mem_singleton] at hw'
      subst hw'
      have : (fun i => ψ w' i - f w' i) = 0 := by funext i; simp [hcol w' hw1]
      rw [this, vn_zero]; exact hr
  have h1 := key hx hz
  have h2 := key hx' hz'
  have hzd := blockSet_subset_dataSites hx hz
  have hzd' := blockSet_subset_dataSites hx' hz'
  have h3 : vn (fun i => f z i - f z' i) ≤ A := by
    rcases (mem_dataSites G).1 hzd with hz1 | hz1
    · have := hs.adj_grad hz1 hadj
      have e : (fun i => f z i - f z' i) = f z - f z' := rfl
      rw [e, vn_sub_comm]
      exact this.trans (div_le_self hA (G.spacing_ge_one z))
    · rcases (mem_dataSites G).1 hzd' with hz2 | hz2
      · have := hs.adj_grad hz2 hadj.symm
        have e : (fun i => f z i - f z' i) = f z - f z' := rfl
        rw [e]
        exact this.trans (div_le_self hA (G.spacing_ge_one z'))
      · have := hcb z hz1 z' hz2 hadj
        rw [hcol z hz1, hcol z' hz2] at this
        exact this
  have t1 := vn_triangle (fun i => ψ x i) (fun i => f z i) (fun i => ψ x' i)
  have t2 := vn_triangle (fun i => f z i) (fun i => f z' i) (fun i => ψ x' i)
  have e1 : vn (fun i => f z' i - ψ x' i) = vn (fun i => ψ x' i - f z' i) := by
    have := vn_sub_comm (fun i => f z' i) (fun i => ψ x' i)
    exact this
  have e3 : vn (fun i => f z i - ψ x' i) ≤ vn (fun i => f z i - f z' i) + vn (fun i => f z' i - ψ x' i) := by
    have := t2
    exact this
  have e4 : vn (fun i => ψ x i - f z i) ≤ r + 2 * d * A := h1
  have e5 : vn ((fun i => ψ x i) - fun i => f z i) = vn (fun i => ψ x i - f z i) := rfl
  have e6 : vn (ψ x - ψ x') = vn ((fun i => ψ x i) - fun i => ψ x' i) := rfl
  have e7 : vn ((fun i => f z i) - fun i => ψ x' i) = vn (fun i => f z i - ψ x' i) := rfl
  have e8 : vn ((fun i => f z i) - fun i => f z' i) = vn (fun i => f z i - f z' i) := rfl
  have e9 : vn ((fun i => f z' i) - fun i => ψ x' i) = vn (fun i => f z' i - ψ x' i) := rfl
  rw [e6]
  rw [e5, e7] at t1
  rw [e7, e8, e9] at t2
  linarith

end Balaban.SmallField
