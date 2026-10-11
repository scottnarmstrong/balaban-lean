module

public import Balaban.Frozen.Model.Torus
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic.Linarith

/-!
# Blocks on the torus

Block hierarchy on the frozen torus `Balaban.Torus d ℓ = Fin d → ZMod ℓ` (P1 §1, pp. 103–110).

Conventions. The sites of `ZMod ℓ` are represented by their residues `a.val ∈ [0, ℓ)`. The block
of side `N` containing a site `a` is the set of sites with the same `a.val / N`; the block map
sends `a` to the class of `a.val / N` in `ZMod m` where `m` is the number of blocks per side.
Instead of dividing `ℓ` by `N` in types, the coarse side `m` is a parameter, and the compatibility
`ℓ = N * m` is a hypothesis of the theorems (so that no type casts occur). Powers `N = L ^ j` are
obtained by specialization.

Main results:
* `Balaban.blockMap` : the block map `Torus d ℓ → Torus d m`;
* `Balaban.card_blockFibre` : every fibre has `N ^ d` sites;
* `Balaban.blockMap_comp` : `blockMap (N * M) = blockMap M ∘ blockMap N` (compatibility of scales),
  and the power form `blockMap_pow_add`.
-/

@[expose] public section

namespace Balaban

/-- The block of side `N` containing the site `a` of `ZMod ℓ`, as a site of `ZMod m`. -/
def blockCoord {ℓ : ℕ} (N m : ℕ) (a : ZMod ℓ) : ZMod m := ((a.val / N : ℕ) : ZMod m)

/-- The block map `Torus d ℓ → Torus d m` for blocks of side `N` (coordinatewise). -/
def blockMap {d ℓ : ℕ} (N m : ℕ) (x : Torus d ℓ) : Torus d m := fun i => blockCoord N m (x i)

theorem blockMap_apply {d ℓ : ℕ} (N m : ℕ) (x : Torus d ℓ) (i : Fin d) :
    blockMap N m x i = blockCoord N m (x i) := rfl

section Coord

variable {ℓ N m : ℕ} [NeZero ℓ]

theorem blockCoord_val (hℓ : ℓ = N * m) (a : ZMod ℓ) :
    (blockCoord N m a).val = a.val / N := by
  have hN : 0 < N := by
    rcases Nat.eq_zero_or_pos N with h | h
    · exact absurd (by simpa [h] using hℓ) (NeZero.ne ℓ)
    · exact h
  unfold blockCoord
  apply ZMod.val_natCast_of_lt
  rw [Nat.div_lt_iff_lt_mul hN]
  have := lt_of_lt_of_eq (ZMod.val_lt a) hℓ
  linarith [mul_comm N m]

theorem blockCoord_comp {m₁ m₂ M : ℕ} [NeZero m₁] (hℓ : ℓ = N * m₁)
    (_hm : m₁ = M * m₂) (a : ZMod ℓ) :
    blockCoord M m₂ (blockCoord N m₁ a) = blockCoord (N * M) m₂ a := by
  have h : ((a.val / N : ℕ) : ZMod m₁).val = a.val / N := blockCoord_val hℓ a
  unfold blockCoord
  rw [h, Nat.div_div_eq_div_mul]

/-- The fibre of the coordinate block map over `b`. -/
theorem card_blockCoord_fibre [NeZero m] (hℓ : ℓ = N * m) (b : ZMod m) :
    (Finset.univ.filter fun a : ZMod ℓ => blockCoord N m a = b).card = N := by
  have hN : 0 < N := by
    rcases Nat.eq_zero_or_pos N with h | h
    · exact absurd (by simpa [h] using hℓ) (NeZero.ne ℓ)
    · exact h
  have himg : (Finset.univ.filter fun a : ZMod ℓ => blockCoord N m a = b).image ZMod.val =
      Finset.Ico (b.val * N) (b.val * N + N) := by
    ext v
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Ico]
    constructor
    · rintro ⟨a, ha, rfl⟩
      have hv : b.val = a.val / N := by rw [← ha, blockCoord_val hℓ]
      rw [hv]
      exact ⟨Nat.div_mul_le_self _ _, by linarith [Nat.lt_div_mul_add (a := a.val) hN]⟩
    · rintro ⟨h1, h2⟩
      have hvl : v < ℓ := by
        have := ZMod.val_lt b
        rw [hℓ]
        nlinarith
      refine ⟨(v : ZMod ℓ), ?_, ZMod.val_natCast_of_lt hvl⟩
      apply ZMod.val_injective
      rw [blockCoord_val hℓ, ZMod.val_natCast_of_lt hvl]
      exact (Nat.div_eq_of_lt_le h1 (by rw [add_mul, one_mul]; exact h2))
  rw [← Finset.card_image_of_injective _ (ZMod.val_injective ℓ), himg]
  simp

end Coord

section Torus

variable {d ℓ N m : ℕ} [NeZero ℓ]

/-- The fibre of the block map over the block `y`. -/
def blockFibre (N m : ℕ) (y : Torus d m) : Finset (Torus d ℓ) :=
  Finset.univ.filter fun x => blockMap N m x = y

theorem mem_blockFibre {y : Torus d m} {x : Torus d ℓ} :
    x ∈ blockFibre N m y ↔ blockMap N m x = y := by
  simp [blockFibre]

/-- Every block contains exactly `N ^ d` sites. -/
theorem card_blockFibre [NeZero m] (hℓ : ℓ = N * m) (y : Torus d m) :
    (blockFibre N m y : Finset (Torus d ℓ)).card = N ^ d := by
  have : (blockFibre N m y : Finset (Torus d ℓ)) =
      Fintype.piFinset fun i => Finset.univ.filter fun a : ZMod ℓ => blockCoord N m a = y i := by
    ext x
    simp [mem_blockFibre, blockMap, funext_iff, Fintype.mem_piFinset]
  rw [this, Fintype.card_piFinset]
  simp [card_blockCoord_fibre hℓ]

/-- Compatibility of scales: `block_{N M} = block_M ∘ block_N`. -/
theorem blockMap_comp {m₁ m₂ M : ℕ} [NeZero m₁] [NeZero m₂] (hℓ : ℓ = N * m₁)
    (hm : m₁ = M * m₂) (x : Torus d ℓ) :
    blockMap M m₂ (blockMap N m₁ x) = blockMap (N * M) m₂ x := by
  funext i
  exact blockCoord_comp hℓ hm (x i)

/-- Compatibility of scales for powers of `L`. -/
theorem blockMap_pow_add {m₁ m₂ L j k : ℕ} [NeZero m₁] [NeZero m₂] (hℓ : ℓ = L ^ j * m₁)
    (hm : m₁ = L ^ k * m₂) (x : Torus d ℓ) :
    blockMap (L ^ k) m₂ (blockMap (L ^ j) m₁ x) = blockMap (L ^ (j + k)) m₂ x := by
  rw [blockMap_comp hℓ hm, pow_add]

end Torus

end Balaban
