/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Background.Def5
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Theorem 5.2 (5): the single-scale generating set (P2 Cor 1.1)

`GeneratingSet.single`: `Ω_j = 𝕋` for `1 ≤ j ≤ k` (and `Ω_j = ∅` otherwise); the separation
condition is vacuous.  Its only layer is `k` (`layerIndex_single`), so `ℓ ≡ L^k` and the collar is
empty (`collar_single`).  Theorems 5.2, 7.1, 7.2 apply to it verbatim.
-/

@[expose] public section

namespace Balaban.Background

open Balaban.Multiscale

variable {d L N₀ k : ℕ} [NeZero N₀] [NeZero L] (ϱ : ℝ)

open Classical in
/-- The domains of the single-scale generating set: `Ω_j = 𝕋` for `j ≤ k`, `∅` for `j > k`. -/
noncomputable def singleΩ (d L N₀ k : ℕ) [NeZero N₀] [NeZero L] (j : ℕ) :
    Finset (Torus d (N₀ * L ^ k)) :=
  if j ≤ k then Finset.univ else ∅

/-- **The single-scale generating set** `Ω_1 = … = Ω_k = 𝕋`. -/
noncomputable def GeneratingSet.single : GeneratingSet d L N₀ k ϱ where
  Ω := singleΩ d L N₀ k
  top := by simp [singleΩ]
  subset := fun j _ hjk => by
    unfold singleΩ
    split_ifs <;> simp
  blockUnion := fun j _ hjk x x' _ => by
    simp [singleΩ, hjk]
  separation := fun j _ hjk x hx => by
    exfalso
    apply hx
    simp [singleΩ, hjk.le]

variable {ϱ}

theorem single_Ω_one (hk : 1 ≤ k) :
    (GeneratingSet.single (d := d) (L := L) (N₀ := N₀) (k := k) ϱ).Ω 1 = Finset.univ := by
  classical
  simp [GeneratingSet.single, singleΩ, hk]

theorem layerIndex_single (hk : 1 ≤ k) (x : Torus d (N₀ * L ^ k)) :
    (GeneratingSet.single (d := d) (L := L) (N₀ := N₀) (k := k) ϱ).layerIndex x = k := by
  classical
  apply GeneratingSet.layerIndex_eq _ hk le_rfl
  rw [GeneratingSet.mem_layer]
  simp [GeneratingSet.single, singleΩ]

theorem spacing_single (hk : 1 ≤ k) (x : Torus d (N₀ * L ^ k)) :
    (GeneratingSet.single (d := d) (L := L) (N₀ := N₀) (k := k) ϱ).spacing x = (L : ℝ) ^ k := by
  unfold GeneratingSet.spacing
  rw [layerIndex_single hk]

theorem collar_single (hk : 1 ≤ k) :
    collar (GeneratingSet.single (d := d) (L := L) (N₀ := N₀) (k := k) ϱ) = ∅ := by
  classical
  ext x
  rw [mem_collar, single_Ω_one hk]
  simp

end Balaban.Background
