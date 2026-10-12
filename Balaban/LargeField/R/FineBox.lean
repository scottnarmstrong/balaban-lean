module

public import Balaban.LargeField.Geometry.Continuous
public import Balaban.LargeField.Geometry.Small
public import Balaban.Lattice.Blocks
import Mathlib.Tactic.Linarith

/-!
# Preimages of boxes under the block maps are boxes

For the block map `blockMap N m : Torus d (N * m) → Torus d m`, the preimage of a cyclic interval
of `s ≤ m` blocks starting at the block `a` is the cyclic interval of `N s` sites starting at
`N a.val` (`blockCoord_mem_cycInt_iff`).  Hence the preimage of a box is a box
(`blockMap_mem_box_iff`); for `s = 1` the fibre of a block is a box of side `N`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open Balaban

section OneDim

variable {ℓ N m : ℕ}

theorem blockCoord_natCast_lt (hℓ : ℓ = N * m) [NeZero ℓ] {c r : ℕ} (hc : c < m) (hr : r < N) :
    blockCoord (ℓ := ℓ) N m ((N * c + r : ℕ) : ZMod ℓ) = (c : ZMod m) := by
  have hN : 0 < N := by omega
  have hlt : N * c + r < ℓ := by
    rw [hℓ]
    nlinarith
  unfold blockCoord
  rw [ZMod.val_natCast_of_lt hlt]
  congr 1
  rw [Nat.add_comm, Nat.add_mul_div_left _ _ hN, Nat.div_eq_of_lt hr, zero_add]

/-- The preimage of a cyclic interval of blocks is a cyclic interval of sites. -/
theorem blockCoord_mem_cycInt_iff [NeZero ℓ] [NeZero m] (hℓ : ℓ = N * m) (a : ZMod m) {s : ℕ}
    (u : ZMod ℓ) :
    blockCoord N m u ∈ cycInt a s ↔ u ∈ cycInt (((N * a.val : ℕ)) : ZMod ℓ) (N * s) := by
  have hN : 0 < N := by
    rcases Nat.eq_zero_or_pos N with h | h
    · exact absurd (by simpa [h] using hℓ) (NeZero.ne ℓ)
    · exact h
  have hmpos : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
  have hav : a.val < m := ZMod.val_lt a
  constructor
  · rintro ⟨j, hj, hjeq⟩
    -- `u.val = N c + r`
    set c := u.val / N with hc
    set r := u.val % N with hr
    have hrN : r < N := Nat.mod_lt _ hN
    have hu : u.val = N * c + r := (Nat.div_add_mod u.val N).symm
    have hcm : c < m := by
      have := ZMod.val_lt u
      rw [hu, hℓ] at this
      by_contra hcm
      push Not at hcm
      nlinarith
    have hcast : (c : ZMod m) = a + (j : ZMod m) := by
      have := hjeq
      unfold blockCoord at this
      exact this
    -- c ≡ a.val + j mod m
    have hmod : (c : ZMod m) = ((a.val + j : ℕ) : ZMod m) := by
      rw [hcast]; push_cast; rw [ZMod.natCast_zmod_val]
    obtain ⟨q, hq⟩ : ∃ q, a.val + j = c + m * q := by
      have := (ZMod.natCast_eq_natCast_iff' c (a.val + j) m).1 hmod
      refine ⟨(a.val + j) / m, ?_⟩
      have h1 := Nat.div_add_mod (a.val + j) m
      rw [Nat.mod_eq_of_lt hcm] at this
      omega
    refine ⟨N * j + r, ?_, ?_⟩
    · nlinarith
    · have hu' : u = ((N * c + r : ℕ) : ZMod ℓ) := by
        rw [← hu, ZMod.natCast_zmod_val]
      rw [hu']
      have : N * (a.val + j) + r = (N * c + r) + ℓ * q := by
        rw [hq, hℓ]; ring
      have h2 : (((N * (a.val + j) + r : ℕ)) : ZMod ℓ) = ((N * c + r : ℕ) : ZMod ℓ) := by
        rw [this]; push_cast; simp
      rw [← h2]; push_cast; ring
  · rintro ⟨j', hj', hu⟩
    -- `j' = N q + r`
    set q := j' / N with hq
    set r := j' % N with hr
    have hrN : r < N := Nat.mod_lt _ hN
    have hj'e : j' = N * q + r := (Nat.div_add_mod j' N).symm
    have hqs : q < s := by
      rw [hq]
      exact (Nat.div_lt_iff_lt_mul hN).2 (by linarith [mul_comm N s])
    refine ⟨q, hqs, ?_⟩
    -- decompose `a.val + q = m t + c`
    set c := (a.val + q) % m with hc
    have hcm : c < m := Nat.mod_lt _ hmpos
    obtain ⟨t, ht⟩ : ∃ t, a.val + q = c + m * t := ⟨(a.val + q) / m, by
      have := Nat.div_add_mod (a.val + q) m; omega⟩
    have hu' : u = ((N * c + r : ℕ) : ZMod ℓ) := by
      rw [hu]
      have : N * a.val + j' = (N * c + r) + ℓ * t := by
        rw [hj'e, hℓ]
        have : N * a.val + (N * q + r) = N * (a.val + q) + r := by ring
        rw [this, ht]; ring
      have h2 : (((N * a.val + j' : ℕ)) : ZMod ℓ) = ((N * c + r : ℕ) : ZMod ℓ) := by
        rw [this]; push_cast; simp
      rw [← h2]; push_cast; ring
    rw [hu']
    rw [blockCoord_natCast_lt hℓ hcm hrN]
    have : (c : ZMod m) = ((a.val + q : ℕ) : ZMod m) := by
      rw [ht]; push_cast; simp
    rw [this]; push_cast; rw [ZMod.natCast_zmod_val]

end OneDim

section Torus

variable {d ℓ N m : ℕ} [NeZero ℓ] [NeZero m]

/-- The preimage of a box of blocks is a box of sites. -/
theorem blockMap_mem_box_iff (hℓ : ℓ = N * m) (a : Torus d m) {s : Fin d → ℕ}
    (u : Torus d ℓ) :
    blockMap N m u ∈ box a s ↔
      u ∈ box (fun i => (((N * (a i).val : ℕ)) : ZMod ℓ)) (fun i => N * s i) := by
  unfold box
  simp only [Set.mem_ofPred_eq]
  refine forall_congr' fun i => ?_
  exact blockCoord_mem_cycInt_iff hℓ (a i) (u i)

end Torus

end Balaban.LargeField
