/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Flow.CellMoments
public import Balaban.Fluctuation.CriticalPoint
public import Balaban.Multiscale.AgmonDecay

/-!
# The Dirichlet operator of a whole-lattice level on functions of one coordinate

On the torus `Torus d ℓ = (ZMod ℓ)^d`, a function `U ∘ π_μ` of the single coordinate `x_μ` is
mapped by the Dirichlet operator of a whole-lattice level `n` (`IsLevel G n`, `α = 0`) to the
function of `x_μ` obtained by applying the one-dimensional operator
`H₁ U = -Δ₁ U + w P₁ U + ν U`, `P₁` the average over the `L^n` consecutive sites of the block and
`w = a_n L^{-2n}` (`dirichlet_lift1`).
-/

@[expose] public section

namespace Balaban.Flow

open Finset Balaban Balaban.Multiscale Balaban.Background Balaban.Fluctuation Matrix

section Coord

theorem sum_piFinset_coord {ι α : Type*} [Fintype ι] [DecidableEq ι] (S : ι → Finset α) (μ : ι)
    (U : α → ℂ) :
    ∑ y ∈ Fintype.piFinset S, U (y μ) =
      (∏ i ∈ (Finset.univ : Finset ι).erase μ, ((S i).card : ℂ)) * ∑ s ∈ S μ, U s := by
  classical
  have h := Finset.prod_univ_sum S (fun i (a : α) => if i = μ then U a else (1 : ℂ))
  have e1 : ∀ p : ι → α, (∏ i, (if i = μ then U (p i) else (1 : ℂ))) = U (p μ) := fun p => by
    simp [Finset.prod_ite_eq']
  simp only [e1] at h
  rw [← h, ← Finset.mul_prod_erase _ _ (Finset.mem_univ μ)]
  simp only [↓reduceIte]
  rw [mul_comm]
  congr 1
  refine Finset.prod_congr rfl fun i hi => ?_
  have : i ≠ μ := (Finset.mem_erase.1 hi).1
  simp [this]

end Coord

variable {d : ℕ}

/-- The function `y ↦ U (y μ)` of the single coordinate `μ`. -/
def lift1 {ℓ : ℕ} (μ : Fin d) (U : ZMod ℓ → ℂ) : Torus d ℓ → ℂ := fun y => U (y μ)

theorem negLap_lift1 {ℓ : ℕ} (μ : Fin d) (U : ZMod ℓ → ℂ) (y : Torus d ℓ) :
    negLap (lift1 μ U) y = 2 * U (y μ) - U (y μ + 1) - U (y μ - 1) := by
  unfold negLap lift1
  rw [Finset.sum_eq_single μ]
  · simp
  · intro ν _ hne
    simp [hne]; ring
  · intro h; exact absurd (Finset.mem_univ μ) h

/-- The one-dimensional block: the sites `s'` of `ZMod ℓ` with `blockCoord N m s' = c`. -/
def fibre1 {ℓ : ℕ} [NeZero ℓ] (N m : ℕ) (c : ZMod m) : Finset (ZMod ℓ) :=
  Finset.univ.filter fun s' => blockCoord N m s' = c

theorem sum_blockFibre_lift1 {ℓ N m : ℕ} [NeZero ℓ] [NeZero m] (hℓ : ℓ = N * m) (μ : Fin d)
    (U : ZMod ℓ → ℂ) (c : Torus d m) :
    ∑ y ∈ (blockFibre N m c : Finset (Torus d ℓ)), U (y μ) =
      (N : ℂ) ^ (d - 1) * ∑ s ∈ fibre1 (ℓ := ℓ) N m (c μ), U s := by
  have h : (blockFibre N m c : Finset (Torus d ℓ)) =
      Fintype.piFinset fun i => fibre1 (ℓ := ℓ) N m (c i) := by
    ext x
    simp [mem_blockFibre, blockMap, funext_iff, Fintype.mem_piFinset, fibre1]
  rw [h, sum_piFinset_coord]
  have hc : ∀ i, ((fibre1 (ℓ := ℓ) N m (c i)).card : ℂ) = (N : ℂ) := fun i => by
    have : (fibre1 (ℓ := ℓ) N m (c i)).card = N := card_blockCoord_fibre hℓ (c i)
    exact_mod_cast this
  simp only [hc, Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ μ),
    Finset.card_univ, Fintype.card_fin]

/-- The one-dimensional operator `-Δ₁ U + w P₁ U + ν U` on `ZMod ℓ`, `P₁` the average over the
`N` consecutive sites of the block. -/
noncomputable def hamil1 {ℓ : ℕ} [NeZero ℓ] (N m : ℕ) (w ν : ℝ) (U : ZMod ℓ → ℂ) (s : ZMod ℓ) : ℂ :=
  2 * U s - U (s + 1) - U (s - 1) + (w : ℂ) * ((1 / (N : ℂ)) *
    ∑ s' ∈ fibre1 (ℓ := ℓ) N m (blockCoord N m s), U s') + (ν : ℂ) * U s

variable {L N₀ K : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}

theorem dirichlet_lift1 {G : GeneratingSet d L N₀ K ϱ} {n : ℕ} (hG : IsLevel G n) (a : ℕ → ℝ)
    (ν : ℝ) (μ : Fin d) (U : ZMod (N₀ * L ^ K) → ℂ) (x : G.Ω 1) :
    (dirichletOperator G a ν 0 *ᵥ (fun y : G.Ω 1 => lift1 μ U (y : Torus d (N₀ * L ^ K)))) x =
      hamil1 (L ^ n) (N₀ * L ^ (K - n)) (a n / ((L : ℝ) ^ n) ^ 2) ν U
        ((x : Torus d (N₀ * L ^ K)) μ) := by
  have hz : zeroExt (G.Ω 1) (fun y : G.Ω 1 => lift1 μ U (y : Torus d (N₀ * L ^ K))) = lift1 μ U := by
    funext y
    simp [zeroExt, (hG y).1]
  have hn : G.layerIndex (x : Torus d (N₀ * L ^ K)) = n := (hG x).2
  have hn1 := (IsLevel.bounds hG).1
  have hnK := (IsLevel.bounds hG).2
  have hℓ : N₀ * L ^ K = L ^ n * (N₀ * L ^ (K - n)) := by
    rw [← mul_assoc, mul_comm (L ^ n), mul_assoc, ← pow_add, Nat.add_sub_cancel' hnK]
  have : NeZero (N₀ * L ^ (K - n)) :=
    ⟨Nat.mul_ne_zero (NeZero.ne N₀) (pow_ne_zero _ (NeZero.ne L))⟩
  rw [dirichlet_apply, hz]
  simp only [Pi.zero_apply, zero_mul, add_zero]
  have hb : G.blk n (x : Torus d (N₀ * L ^ K)) =
      blockFibre (L ^ n) (N₀ * L ^ (K - n)) (blockMap (L ^ n) (N₀ * L ^ (K - n)) (x : Torus d (N₀ * L ^ K))) := by
    ext y
    simp [GeneratingSet.mem_blk, jBlock, mem_blockFibre]
  unfold blockTerm
  rw [hn, hb, negLap_lift1]
  unfold lift1
  rw [sum_blockFibre_lift1 hℓ]
  unfold hamil1
  have hd : 1 ≤ d := Nat.one_le_iff_ne_zero.2 (fun h => by subst h; exact μ.elim0)
  have hL : ((L : ℝ) ^ n) ≠ 0 := by
    have : (L : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne L
    positivity
  simp only [blockMap, blockCoord]
  push_cast
  have e : ((L : ℂ) ^ n) ^ d = ((L : ℂ) ^ n) ^ (d - 1) * (L : ℂ) ^ n := by
    rw [← pow_succ, Nat.sub_add_cancel hd]
  have hL' : (L : ℂ) ^ n ≠ 0 := by exact_mod_cast hL
  rw [e]
  field_simp

end Balaban.Flow
