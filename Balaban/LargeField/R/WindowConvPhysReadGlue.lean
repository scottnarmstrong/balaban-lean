/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.ChainGraph

/-!
# One block field from the data of disjoint block-closed regions

P7 p. 501 (2.14): the physical datum of the window is the trace of one multiscale field `ψ`.  If
the sites of the pieces form disjoint block-closed regions and on each the datum is real and
constant on the blocks of the layer of the site, then there is one block field `ψ` that reads the
datum of the piece on every one of its sites.  The pieces are pairwise disjoint, so no two of them
constrain the same block.
-/

@[expose] public section

namespace Balaban.LargeField

open Balaban Balaban.Multiscale

theorem blockV_eq_aux {d L N₀ k : ℕ} [NeZero N₀] [NeZero L] (a a' : ℕ)
    (x x' : Torus d (N₀ * L ^ k))
    (h : (⟨a, jBlock d L N₀ k a x⟩ : BlockV d L N₀ k) = ⟨a', jBlock d L N₀ k a' x'⟩) :
    a = a' ∧ jBlock d L N₀ k a x = jBlock d L N₀ k a x' := by
  have ha : a = a' := congrArg Sigma.fst h
  subst ha
  exact ⟨rfl, eq_of_heq (Sigma.mk.inj_iff.1 h).2⟩

/-- **One block field for disjoint regions** (P7 (2.14)). -/
theorem exists_glued_blockField {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ι : Type*}
    (ℓ : Torus d (N₀ * L ^ k) → ℕ) (X : ι → Set (Torus d (N₀ * L ^ k)))
    (F : ι → Torus d (N₀ * L ^ k) → Fin N → ℂ)
    (hdisj : ∀ i i', i ≠ i' → ∀ x, x ∈ X i → x ∈ X i' → False)
    (hcl : ∀ i x, x ∈ X i → ∀ x', jBlock d L N₀ k (ℓ x) x' = jBlock d L N₀ k (ℓ x) x → x' ∈ X i)
    (hconst : ∀ i x, x ∈ X i → ∀ x', jBlock d L N₀ k (ℓ x) x' = jBlock d L N₀ k (ℓ x) x →
      F i x' = F i x)
    (hreal : ∀ i x, x ∈ X i → ∃ r : Fin N → ℝ, F i x = fun q => (r q : ℂ)) :
    ∃ ψ : BlockV d L N₀ k → EuclideanSpace ℝ (Fin N), ∀ i x, x ∈ X i →
      F i x = fun q => ((ψ (blockOf d L N₀ k (ℓ x) x) q : ℝ) : ℂ) := by
  classical
  have key : ∀ i x i' x', x ∈ X i → x' ∈ X i' →
      blockOf d L N₀ k (ℓ x) x = blockOf d L N₀ k (ℓ x') x' → F i x = F i' x' := by
    intro i x i' x' hx hx' hb
    obtain ⟨-, hj⟩ := blockV_eq_aux (ℓ x) (ℓ x') x x' hb
    have hx'i : x' ∈ X i := hcl i x hx x' hj.symm
    have hii : i = i' := by
      by_contra hne
      exact hdisj i i' hne x' hx'i hx'
    subst hii
    exact (hconst i x hx x' hj.symm).symm
  let P : BlockV d L N₀ k → Prop := fun b => ∃ i x, x ∈ X i ∧ blockOf d L N₀ k (ℓ x) x = b
  refine ⟨fun b => if h : P b then
      WithLp.toLp 2 (Classical.choose (hreal _ _ (Classical.choose_spec (Classical.choose_spec h)).1))
    else 0, fun i x hx => ?_⟩
  have hP : P (blockOf d L N₀ k (ℓ x) x) := ⟨i, x, hx, rfl⟩
  simp only [hP, dite_true]
  obtain ⟨hxi, hb⟩ := Classical.choose_spec (Classical.choose_spec hP)
  rw [key i x _ _ hx hxi hb.symm]
  exact Classical.choose_spec (hreal _ _ hxi)

end Balaban.LargeField
