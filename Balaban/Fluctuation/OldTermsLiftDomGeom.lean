/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.OldTermsLiftGeom
public import Balaban.SmallField.Xi

/-!
# Sites, layers and blocks of a transported generating set

For the transported generating set `liftOldGS G` the layer index, the blocks, the collar, the data
sites and the interface pairs of the background problem agree with those of `G` under the
relabeling `oldTorusEquiv`.  This is the geometric input for comparing the wide complex charts at
the old and the new scale.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Localization Balaban.Multiscale Balaban.Background

variable {d L N₁ m₁ k : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}

section Sites

variable (G : GeneratingSet d L ((L * N₁) * L ^ m₁) k ϱ)

theorem liftOldGS_mem_Ω_le {j : ℕ} (hj : j ≤ k + 1) (x : CTorus d L (L * N₁) m₁ k) :
    oldTorusEquiv x ∈ (liftOldGS G).Ω j ↔ x ∈ G.Ω j := by
  rcases Nat.lt_or_ge j (k + 1) with h | h
  · exact liftOldGS_mem_Ω G (by omega) x
  · obtain rfl : j = k + 1 := by omega
    simp [liftOldGS_Ω_top, G.top]

theorem liftOldGS_layerIndex_all (x : CTorus d L (L * N₁) m₁ k) :
    (liftOldGS G).layerIndex (oldTorusEquiv x) = G.layerIndex x := by
  by_cases hx : x ∈ G.Ω 1
  · exact liftOldGS_layerIndex G x hx
  · rw [layerIndex_of_not_mem G hx, layerIndex_of_not_mem (liftOldGS G)]
    rwa [liftOldGS_mem_Ω_le G (by omega)]

theorem liftOldGS_spacing (x : CTorus d L (L * N₁) m₁ k) :
    (liftOldGS G).spacing (oldTorusEquiv x) = G.spacing x := by
  simp only [GeneratingSet.spacing, liftOldGS_layerIndex_all]

omit [NeZero L] [NeZero N₁] in
theorem oldTorusEquiv_add (x y : CTorus d L (L * N₁) m₁ k) :
    oldTorusEquiv (x + y) = oldTorusEquiv x + oldTorusEquiv y := by
  simp only [oldTorusEquiv_apply, castT_add]

omit [NeZero L] [NeZero N₁] in
theorem oldTorusEquiv_sub (x y : CTorus d L (L * N₁) m₁ k) :
    oldTorusEquiv (x - y) = oldTorusEquiv x - oldTorusEquiv y := by
  simp only [oldTorusEquiv_apply, castT_sub]

omit [NeZero L] [NeZero N₁] in
theorem oldTorusEquiv_single (μ : Fin d) :
    oldTorusEquiv (Pi.single μ 1 : CTorus d L (L * N₁) m₁ k) = Pi.single μ 1 := by
  rw [oldTorusEquiv_apply, castT_single]

omit [NeZero L] [NeZero N₁] in
theorem oldTorusEquiv_adj_iff (x y : CTorus d L (L * N₁) m₁ k) :
    Adj (oldTorusEquiv x) (oldTorusEquiv y) ↔ Adj x y := by
  constructor
  · rintro ⟨μ, h | h⟩
    · refine ⟨μ, Or.inl (oldTorusEquiv.injective ?_)⟩
      rw [oldTorusEquiv_add, oldTorusEquiv_single]; exact h
    · refine ⟨μ, Or.inr (oldTorusEquiv.injective ?_)⟩
      rw [oldTorusEquiv_add, oldTorusEquiv_single]; exact h
  · rintro ⟨μ, h | h⟩
    · refine ⟨μ, Or.inl ?_⟩
      rw [h, oldTorusEquiv_add, oldTorusEquiv_single]
    · refine ⟨μ, Or.inr ?_⟩
      rw [h, oldTorusEquiv_add, oldTorusEquiv_single]

theorem liftOldGS_mem_collar (x : CTorus d L (L * N₁) m₁ k) :
    oldTorusEquiv x ∈ collar (liftOldGS G) ↔ x ∈ collar G := by
  rw [mem_collar, mem_collar, liftOldGS_mem_Ω_le G (by omega)]
  refine and_congr Iff.rfl ?_
  constructor
  · rintro ⟨y', hy', hadj⟩
    obtain ⟨y, rfl⟩ := oldTorusEquiv.surjective y'
    exact ⟨y, (liftOldGS_mem_Ω_le G (by omega) y).1 hy', (oldTorusEquiv_adj_iff y x).1 hadj⟩
  · rintro ⟨y, hy, hadj⟩
    exact ⟨oldTorusEquiv y, (liftOldGS_mem_Ω_le G (by omega) y).2 hy,
      (oldTorusEquiv_adj_iff y x).2 hadj⟩

theorem liftOldGS_mem_dataSites (x : CTorus d L (L * N₁) m₁ k) :
    oldTorusEquiv x ∈ dataSites (liftOldGS G) ↔ x ∈ dataSites G := by
  rw [mem_dataSites, mem_dataSites, liftOldGS_mem_Ω_le G (by omega), liftOldGS_mem_collar]

theorem liftOldGS_mem_blk {j : ℕ} (hj : j ≤ k) (x y : CTorus d L (L * N₁) m₁ k) :
    oldTorusEquiv y ∈ (liftOldGS G).blk j (oldTorusEquiv x) ↔ y ∈ G.blk j x := by
  rw [GeneratingSet.mem_blk, GeneratingSet.mem_blk]
  exact oldTorusEquiv_jBlock_iff hj y x

theorem liftOldGS_sum_blk {M : Type*} [AddCommMonoid M] {j : ℕ} (hj : j ≤ k)
    (x : CTorus d L (L * N₁) m₁ k) (f : CTorus d L N₁ m₁ (k + 1) → M) :
    ∑ y ∈ (liftOldGS G).blk j (oldTorusEquiv x), f y = ∑ y ∈ G.blk j x, f (oldTorusEquiv y) := by
  refine Finset.sum_equiv oldTorusEquiv.symm (fun y => ?_) (fun y _ => ?_)
  · obtain ⟨y, rfl⟩ := oldTorusEquiv.surjective y
    rw [Equiv.symm_apply_apply, liftOldGS_mem_blk G hj]
  · simp

theorem liftOldGS_mem_blockSet (x y : CTorus d L (L * N₁) m₁ k) :
    oldTorusEquiv y ∈ blockSet (liftOldGS G) (oldTorusEquiv x) ↔ y ∈ blockSet G x := by
  classical
  unfold blockSet
  by_cases hx : x ∈ G.Ω 1
  · have hx' : oldTorusEquiv x ∈ (liftOldGS G).Ω 1 := (liftOldGS_mem_Ω_le G (by omega) x).2 hx
    simp only [hx, hx', ↓reduceIte, liftOldGS_layerIndex_all]
    exact liftOldGS_mem_blk G (G.layerIndex_spec hx).2.1 x y
  · have hx' : oldTorusEquiv x ∉ (liftOldGS G).Ω 1 := by
      rwa [liftOldGS_mem_Ω_le G (by omega)]
    simp only [hx, hx', ↓reduceIte]
    simp

theorem liftOldGS_blocksAdjacent_iff (x x' : CTorus d L (L * N₁) m₁ k) :
    BlocksAdjacent (liftOldGS G) (oldTorusEquiv x) (oldTorusEquiv x') ↔ BlocksAdjacent G x x' := by
  constructor
  · rintro ⟨y, hy, y', hy', hadj⟩
    obtain ⟨z, rfl⟩ := oldTorusEquiv.surjective y
    obtain ⟨z', rfl⟩ := oldTorusEquiv.surjective y'
    exact ⟨z, (liftOldGS_mem_blockSet G x z).1 hy, z', (liftOldGS_mem_blockSet G x' z').1 hy',
      (oldTorusEquiv_adj_iff z z').1 hadj⟩
  · rintro ⟨y, hy, y', hy', hadj⟩
    exact ⟨oldTorusEquiv y, (liftOldGS_mem_blockSet G x y).2 hy, oldTorusEquiv y',
      (liftOldGS_mem_blockSet G x' y').2 hy', (oldTorusEquiv_adj_iff y y').2 hadj⟩

theorem liftOldGS_isInterfacePair_iff (x x' : CTorus d L (L * N₁) m₁ k) :
    IsInterfacePair (liftOldGS G) (oldTorusEquiv x) (oldTorusEquiv x') ↔ IsInterfacePair G x x' := by
  unfold IsInterfacePair
  rw [liftOldGS_mem_dataSites, liftOldGS_mem_dataSites, liftOldGS_layerIndex_all,
    liftOldGS_layerIndex_all, liftOldGS_blocksAdjacent_iff]

theorem liftOldGS_isLayerConstant {β : Type*} {Ψ : CTorus d L N₁ m₁ (k + 1) → β}
    (h : IsLayerConstant (liftOldGS G) Ψ) :
    IsLayerConstant G (fun x => Ψ (oldTorusEquiv x)) := by
  intro n hn1 hnk x hx x' hx'
  have hx1 : oldTorusEquiv x ∈ (liftOldGS G).layer n := (liftOldGS_mem_layer G hnk x).2 hx
  exact h n hn1 (by omega) _ hx1 _ ((liftOldGS_mem_blk G hnk x x').2 hx')

end Sites

end Balaban.Fluctuation
