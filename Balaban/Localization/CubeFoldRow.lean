/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.CubeFoldGeometry
public import Balaban.Green.Lattice.LocAlgebra

/-!
# The local Neumann row of the cut Laplacian (VMOD-9, (2.4))

`cutLaplacian_mulVec_complex_row`: the row of the (complex) cut Laplacian `-Δ_cut + ν`.

`cubeFold_local_neumann_row`: for the local fold `P(z) = foldMap (p₀ + z)` of a cube, the integer
lattice Laplacian of `w(z) = v(P(z))` at `z` is the cut-Laplacian row (without mass) of `v` at `P(z)`
for the cut `cubeCut G Λ`, provided that every neighbour of `P(z)` outside the cube is a site of
`Ω₁(G)` (a local collar: no global collar and no reflected generating set is needed).
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Reflection Balaban.LatticeGreen Finset Matrix

variable {d L N₀ k : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}

/-- The row of the cut Laplacian `-Δ_cut + ν` on complex fields: the retained bonds at `x`. -/
theorem cutLaplacian_mulVec_complex_row {ℓ : ℕ} [NeZero ℓ] (hℓ : 2 ≤ ℓ) (ν : ℝ)
    (cut : Finset (Torus d ℓ × Fin d)) (ψ : Torus d ℓ → ℂ) (x : Torus d ℓ) :
    ((cutLaplacian ν cut).map (algebraMap ℝ ℂ) *ᵥ ψ) x = ν * ψ x +
      ∑ μ : Fin d, ((if (x, μ) ∈ cut then 0 else ψ x - ψ (x + Pi.single μ 1)) +
        (if (x - Pi.single μ 1, μ) ∈ cut then 0 else ψ x - ψ (x - Pi.single μ 1))) := by
  classical
  have key : ∀ φ : Torus d ℓ → ℝ, (cutLaplacian ν cut *ᵥ φ) x = ν * φ x +
      ∑ μ : Fin d, ((if (x, μ) ∈ cut then 0 else φ x - φ (x + Pi.single μ 1)) +
        (if (x - Pi.single μ 1, μ) ∈ cut then 0 else φ x - φ (x - Pi.single μ 1))) := by
    intro φ
    rw [cutLaplacian_mulVec_row hℓ, latticeLaplacian_mulVec, add_comm _ (ν * φ x), add_assoc,
      add_comm _ (∑ μ : Fin d, _), ← Finset.sum_add_distrib]
    congr 1
    refine Finset.sum_congr rfl fun μ _ => ?_
    split_ifs <;> ring
  apply Complex.ext
  · rw [re_mulVec_map, key]
    simp only [Complex.add_re, Complex.re_sum, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero]
    congr 1
    refine Finset.sum_congr rfl fun μ _ => ?_
    split_ifs <;> simp
  · rw [im_mulVec_map, key]
    simp only [Complex.add_im, Complex.im_sum, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, add_zero]
    congr 1
    refine Finset.sum_congr rfl fun μ _ => ?_
    split_ifs <;> simp

/-- A bond leaving the cube upwards is cut, if its far end is a site of `Ω₁`. -/
theorem mem_cubeCut_up_iff (G : GeneratingSet d L N₀ k ϱ) {Λ : Finset (Torus d (N₀ * L ^ k))}
    {x : Torus d (N₀ * L ^ k)} (hx : x ∈ Λ) (μ : Fin d)
    (hc : x + Pi.single μ 1 ∉ Λ → x + Pi.single μ 1 ∈ G.Ω 1) :
    (x, μ) ∈ cubeCut G Λ ↔ x + Pi.single μ 1 ∉ Λ := by
  rw [mem_cubeCut]
  tauto

/-- A bond entering the cube from below is cut, if its near end is a site of `Ω₁`. -/
theorem mem_cubeCut_dn_iff (G : GeneratingSet d L N₀ k ϱ) {Λ : Finset (Torus d (N₀ * L ^ k))}
    {x : Torus d (N₀ * L ^ k)} (hx : x ∈ Λ) (μ : Fin d)
    (hc : x - Pi.single μ 1 ∉ Λ → x - Pi.single μ 1 ∈ G.Ω 1) :
    (x - Pi.single μ 1, μ) ∈ cubeCut G Λ ↔ x - Pi.single μ 1 ∉ Λ := by
  rw [mem_cubeCut, sub_add_cancel]
  tauto

/-- **The local Neumann row** (VMOD-9 (2.4)). -/
theorem cubeFold_local_neumann_row (G : GeneratingSet d L N₀ k ϱ) (S : ℕ) [NeZero S]
    (c : Fin d → ℕ) (hSℓ : S < N₀ * L ^ k) (p0 : Torus d (2 * S)) (z : Fin d → ℤ)
    (hcollar : ∀ μ : Fin d,
      (cubeFoldPt N₀ L k S c p0 z + Pi.single μ 1 ∉ cubeSet (N₀ * L ^ k) S c →
        cubeFoldPt N₀ L k S c p0 z + Pi.single μ 1 ∈ G.Ω 1) ∧
      (cubeFoldPt N₀ L k S c p0 z - Pi.single μ 1 ∉ cubeSet (N₀ * L ^ k) S c →
        cubeFoldPt N₀ L k S c p0 z - Pi.single μ 1 ∈ G.Ω 1))
    (v : Torus d (N₀ * L ^ k) → ℂ) :
    negLap (fun w => v (cubeFoldPt N₀ L k S c p0 w)) z =
      ∑ μ : Fin d, ((if (cubeFoldPt N₀ L k S c p0 z, μ) ∈ cubeCut G (cubeSet (N₀ * L ^ k) S c)
          then 0 else v (cubeFoldPt N₀ L k S c p0 z) -
            v (cubeFoldPt N₀ L k S c p0 z + Pi.single μ 1)) +
        (if (cubeFoldPt N₀ L k S c p0 z - Pi.single μ 1, μ) ∈
            cubeCut G (cubeSet (N₀ * L ^ k) S c)
          then 0 else v (cubeFoldPt N₀ L k S c p0 z) -
            v (cubeFoldPt N₀ L k S c p0 z - Pi.single μ 1))) := by
  classical
  have hS : 0 < S := Nat.pos_of_ne_zero (NeZero.ne S)
  set x := cubeFoldPt N₀ L k S c p0 z with hxdef
  have hx : x ∈ cubeSet (N₀ * L ^ k) S c := cubeFoldPt_mem S c p0 z
  unfold negLap
  refine Finset.sum_congr rfl fun μ _ => ?_
  have e1 : cubeFoldPt N₀ L k S c p0 (z + Pi.single μ 1) =
      foldMap (N₀ * L ^ k) S (2 * S) c (dblPt S p0 z + Pi.single μ 1) := by
    unfold cubeFoldPt; rw [dblPt_add_single]
  have e2 : cubeFoldPt N₀ L k S c p0 (z - Pi.single μ 1) =
      foldMap (N₀ * L ^ k) S (2 * S) c (dblPt S p0 z - Pi.single μ 1) := by
    unfold cubeFoldPt; rw [dblPt_sub_single]
  have hs : v (cubeFoldPt N₀ L k S c p0 (z + Pi.single μ 1)) +
      v (cubeFoldPt N₀ L k S c p0 (z - Pi.single μ 1)) =
      v (stepUpT (cubeSet (N₀ * L ^ k) S c) x μ) + v (stepDnT (cubeSet (N₀ * L ^ k) S c) x μ) := by
    rw [e1, e2]
    rcases foldMap_nbr (ℓ := N₀ * L ^ k) (c := c) (m := 2 * S) rfl hS hSℓ (dblPt S p0 z) μ with
      ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2]; rfl
    · rw [h1, h2, add_comm]; rfl
  have hc1 := mem_cubeCut_up_iff G hx μ (hcollar μ).1
  have hc2 := mem_cubeCut_dn_iff G hx μ (hcollar μ).2
  have hup : stepUpT (cubeSet (N₀ * L ^ k) S c) x μ =
      if x + Pi.single μ 1 ∈ cubeSet (N₀ * L ^ k) S c then x + Pi.single μ 1 else x := rfl
  have hdn : stepDnT (cubeSet (N₀ * L ^ k) S c) x μ =
      if x - Pi.single μ 1 ∈ cubeSet (N₀ * L ^ k) S c then x - Pi.single μ 1 else x := rfl
  have : 2 * v x - v (cubeFoldPt N₀ L k S c p0 (z + Pi.single μ 1)) -
        v (cubeFoldPt N₀ L k S c p0 (z - Pi.single μ 1)) =
      2 * v x - (v (stepUpT (cubeSet (N₀ * L ^ k) S c) x μ) +
        v (stepDnT (cubeSet (N₀ * L ^ k) S c) x μ)) := by rw [← hs]; ring
  rw [this, hup, hdn]
  by_cases h1 : x + Pi.single μ 1 ∈ cubeSet (N₀ * L ^ k) S c <;>
    by_cases h2 : x - Pi.single μ 1 ∈ cubeSet (N₀ * L ^ k) S c <;>
    simp [h1, h2, hc1, hc2] <;> ring

end Balaban.Localization
