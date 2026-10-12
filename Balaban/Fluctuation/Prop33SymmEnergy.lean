/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.InteractionVBlock
public import Balaban.Fluctuation.InteractionSymmSolReal
public import Balaban.Fluctuation.InteractionSymmSolRot

/-!
# `O(N)` invariance and reality of the block energy (FLUCTUATION.md Proposition 3.3, symmetry)

The block energy `energyBlock` of the chord form is invariant under `(δφ, ψ') ↦ (R δφ, R ψ')` for
real orthogonal `R` (the multiplier `α` is a scalar) and commutes with complex conjugation of
`(α, δφ)` when `ψ'` is real.
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation Finset
  Matrix

local notation "cj" => starRingEnd ℂ

section Energy

variable {d L N₁ m₁ K N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱm : ℝ}
variable {Gp : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {Hm : GeneratingSet d L (N₁ * L ^ m₁) K ϱm}

theorem svec_rot (R : Matrix (Fin N) (Fin N) ℂ) (δφ : Hm.Ω 1 × Fin N → ℂ)
    (y : CTorus d L N₁ m₁ K) : svec Hm (rotFld R δφ) y = R *ᵥ svec Hm δφ y := by
  classical
  funext i
  by_cases hy : y ∈ Hm.Ω 1
  · simp only [svec, zeroExt, hy, dite_true, rotFld, Matrix.mulVec, dotProduct]
  · simp [svec, zeroExt, hy, Matrix.mulVec, dotProduct]

theorem dot_rot {R : Matrix (Fin N) (Fin N) ℂ} (hR : Rᵀ * R = 1) (u v : Fin N → ℂ) :
    ∑ i, (R *ᵥ u) i * (R *ᵥ v) i = ∑ i, u i * v i := by
  have h : (R *ᵥ u) ⬝ᵥ (R *ᵥ v) = u ⬝ᵥ v := by
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, Matrix.mulVec_mulVec, hR,
      Matrix.one_mulVec]
  simpa [dotProduct] using h

theorem sub_dot_rot {R : Matrix (Fin N) (Fin N) ℂ} (hR : Rᵀ * R = 1) (u v : Fin N → ℂ) :
    ∑ i, ((R *ᵥ u) i - (R *ᵥ v) i) * ((R *ᵥ u) i - (R *ᵥ v) i) =
      ∑ i, (u i - v i) * (u i - v i) := by
  have := dot_rot hR (u - v) (u - v)
  simpa [Matrix.mulVec_sub] using this

theorem blockMean_rot (R : Matrix (Fin N) (Fin N) ℂ) (n : ℕ) (v : CTorus d L N₁ m₁ K → Fin N → ℂ)
    (x : CTorus d L N₁ m₁ K) (i : Fin N) :
    blockMean Hm n (fun y => (R *ᵥ v y) i) x = (R *ᵥ fun j => blockMean Hm n (fun y => v y j) x) i := by
  unfold blockMean
  have h1 : ∑ y ∈ Hm.blk n x, (R *ᵥ v y) i = ∑ j, R i j * ∑ y ∈ Hm.blk n x, v y j := by
    simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
    exact Finset.sum_comm
  rw [h1, Finset.mul_sum]
  simp only [Matrix.mulVec, dotProduct]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

/-- **`O(N)` invariance of the energy density.** -/
theorem energyDensity_rot {R : Matrix (Fin N) (Fin N) ℂ} (hR : Rᵀ * R = 1) (a : ℕ → ℝ) (ν : ℝ)
    (n : ℕ) (α : Gp.Ω 1 → ℂ) (δφ : Hm.Ω 1 × Fin N → ℂ)
    (ψ' : CTorus d L N₁ m₁ K → Fin N → ℂ) (x : CTorus d L N₁ m₁ K) :
    energyDensity Gp Hm a ν n α (rotFld R δφ) (DecEquiv.rotSite R ψ') x =
      energyDensity Gp Hm a ν n α δφ ψ' x := by
  classical
  unfold energyDensity
  have hs : ∀ y, svec Hm (rotFld R δφ) y = R *ᵥ svec Hm δφ y := svec_rot R δφ
  have hbm : ∀ i, blockMean Hm n (fun y => svec Hm (rotFld R δφ) y i) x =
      (R *ᵥ fun j => blockMean Hm n (fun y => svec Hm δφ y j) x) i := by
    intro i
    simp only [hs]
    exact blockMean_rot R n (fun y => svec Hm δφ y) x i
  have hψ : ∀ i, DecEquiv.rotSite R ψ' x i = (R *ᵥ ψ' x) i := fun i => rfl
  simp only [hbm, hψ]
  simp only [hs, sub_dot_rot hR, dot_rot hR]

/-- **`O(N)` invariance of the block energy.** -/
theorem energyBlock_rot {R : Matrix (Fin N) (Fin N) ℂ} (hR : Rᵀ * R = 1) (a : ℕ → ℝ) (ν : ℝ)
    (n : ℕ) (α : Gp.Ω 1 → ℂ) (δφ : Hm.Ω 1 × Fin N → ℂ)
    (ψ' : CTorus d L N₁ m₁ K → Fin N → ℂ) (z : Torus d (N₁ * L ^ m₁ * L ^ (K - (n + 1)))) :
    energyBlock Gp Hm a ν n α (rotFld R δφ) (DecEquiv.rotSite R ψ') z =
      energyBlock Gp Hm a ν n α δφ ψ' z :=
  Finset.sum_congr rfl fun x _ => energyDensity_rot hR a ν n α δφ ψ' x

theorem svec_conj (δφ : Hm.Ω 1 × Fin N → ℂ) (y : CTorus d L N₁ m₁ K) (i : Fin N) :
    svec Hm (fun p => cj (δφ p)) y i = cj (svec Hm δφ y i) := by
  classical
  by_cases hy : y ∈ Hm.Ω 1
  · simp [svec, zeroExt, hy]
  · simp [svec, zeroExt, hy]

theorem zeroExt_conj (α : Gp.Ω 1 → ℂ) (x : CTorus d L N₁ m₁ K) :
    zeroExt (Gp.Ω 1) (fun y => cj (α y)) x = cj (zeroExt (Gp.Ω 1) α x) := by
  classical
  by_cases hx : x ∈ Gp.Ω 1
  · simp [zeroExt, hx]
  · simp [zeroExt, hx]

theorem blockMean_conj (n : ℕ) (v : CTorus d L N₁ m₁ K → ℂ) (x : CTorus d L N₁ m₁ K) :
    blockMean Hm n (fun y => cj (v y)) x = cj (blockMean Hm n v x) := by
  unfold blockMean
  simp [map_sum]

/-- **Reality of the energy density**: conjugating `(α, δφ)` conjugates the density for real `ψ'`. -/
theorem energyDensity_conj (a : ℕ → ℝ) (ν : ℝ) (n : ℕ) (α : Gp.Ω 1 → ℂ)
    (δφ : Hm.Ω 1 × Fin N → ℂ) (ψ' : CTorus d L N₁ m₁ K → Fin N → ℂ)
    (hψ : ∀ x i, (ψ' x i).im = 0) (x : CTorus d L N₁ m₁ K) :
    cj (energyDensity Gp Hm a ν n α δφ ψ' x) =
      energyDensity Gp Hm a ν n (fun y => cj (α y)) (fun p => cj (δφ p)) ψ' x := by
  classical
  have hψ' : ∀ i, cj (ψ' x i) = ψ' x i := fun i => Complex.conj_eq_iff_im.2 (hψ x i)
  unfold energyDensity
  simp only [svec_conj, zeroExt_conj, blockMean_conj, map_add, map_mul, map_sum, map_sub,
    map_div₀, map_one, map_ofNat, Complex.conj_ofReal, hψ', apply_ite cj, map_zero]

theorem energyBlock_conj (a : ℕ → ℝ) (ν : ℝ) (n : ℕ) (α : Gp.Ω 1 → ℂ)
    (δφ : Hm.Ω 1 × Fin N → ℂ) (ψ' : CTorus d L N₁ m₁ K → Fin N → ℂ)
    (hψ : ∀ x i, (ψ' x i).im = 0) (z : Torus d (N₁ * L ^ m₁ * L ^ (K - (n + 1)))) :
    cj (energyBlock Gp Hm a ν n α δφ ψ' z) =
      energyBlock Gp Hm a ν n (fun y => cj (α y)) (fun p => cj (δφ p)) ψ' z := by
  unfold energyBlock
  rw [map_sum]
  exact Finset.sum_congr rfl fun x _ => energyDensity_conj a ν n α δφ ψ' hψ x

end Energy

end Balaban.Localization
