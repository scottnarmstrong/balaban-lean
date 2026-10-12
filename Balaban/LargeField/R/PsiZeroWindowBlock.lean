/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Lattice.Blocks
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The blocks meeting a cyclic interval of cells are exactly an interval of blocks

If `F = N m = u m₁`, the cells of size `u` indexed by `{a, …, a + s - 1} ⊂ ℤ/m₁`, then the blocks of size `N`
meeting these cells are exactly `{b₀, …, b₀ + J}` with `b₀ = ⌊a u / N⌋` and `J = ⌊(a u + s u - 1) / N⌋ - b₀`.
(`blockCoord_box_image` of `ZeroDomainBox` gives only the inclusion into a larger interval.)
-/

@[expose] public section

namespace Balaban

/-- The block of the natural number `x` (as a site of `ℤ/F`). -/
theorem blockCoord_natCast {F N m : ℕ} [NeZero F] (hN : F = N * m) (x : ℕ) :
    blockCoord N m ((x : ℕ) : ZMod F) = ((x / N : ℕ) : ZMod m) := by
  unfold blockCoord
  rw [ZMod.val_natCast, hN, Nat.mod_mul_right_div_self, ZMod.natCast_mod]

/-- Every block of `{b₀, …, b₀ + J}` is hit by a site of the cells `a, …, a + s - 1`. -/
theorem exists_site_of_block {F N m u m₁ : ℕ} [NeZero F] [NeZero m] [NeZero m₁] (hN : F = N * m)
    (hu : F = u * m₁) (a : ZMod m₁) (s : ℕ) (hs : 0 < s) (j' : ℕ)
    (hj' : j' ≤ (a.val * u + s * u - 1) / N - a.val * u / N) :
    ∃ p : ZMod F, (∃ j < s, blockCoord u m₁ p = a + (j : ZMod m₁)) ∧
      blockCoord N m p = ((a.val * u / N : ℕ) : ZMod m) + (j' : ZMod m) := by
  have hNpos : 0 < N := by
    rcases Nat.eq_zero_or_pos N with h | h
    · exact absurd (by simpa [h] using hN) (NeZero.ne F)
    · exact h
  have hupos : 0 < u := by
    rcases Nat.eq_zero_or_pos u with h | h
    · exact absurd (by simpa [h] using hu) (NeZero.ne F)
    · exact h
  set β := a.val * u with hβ
  set t := (β / N + j') * N - β with ht
  have hsu : 0 < s * u := Nat.mul_pos hs hupos
  have hb0e : β / N ≤ (β + s * u - 1) / N := Nat.div_le_div_right (by omega)
  have hle : β / N + j' ≤ (β + s * u - 1) / N := by omega
  have h1 : (β / N + j') * N ≤ β + s * u - 1 := by
    have := Nat.div_mul_le_self (β + s * u - 1) N
    exact le_trans (Nat.mul_le_mul_right N hle) this
  have htlt : t < s * u := by omega
  have hdiv : (β + t) / N = β / N + j' := by
    rcases Nat.eq_zero_or_pos j' with h0 | hpos
    · subst h0
      have : t = 0 := by
        rw [ht, add_zero]
        exact Nat.sub_eq_zero_of_le (Nat.div_mul_le_self β N)
      simp [this]
    · have hβle : β ≤ (β / N + j') * N := by
        have := Nat.lt_div_mul_add (a := β) hNpos
        nlinarith
      have : β + t = (β / N + j') * N := by omega
      rw [this, Nat.mul_div_cancel _ hNpos]
  refine ⟨((β + t : ℕ) : ZMod F), ⟨t / u, ?_, ?_⟩, ?_⟩
  · exact (Nat.div_lt_iff_lt_mul hupos).2 htlt
  · rw [blockCoord_natCast hu, hβ, Nat.mul_comm a.val u, Nat.mul_add_div hupos]
    push_cast
    rw [ZMod.natCast_zmod_val]
  · rw [blockCoord_natCast hN, hdiv]
    push_cast
    rfl

/-- A site of the cells `a, …, a + s - 1` lies in a block of `{b₀, …, b₀ + J}`. -/
theorem blockCoord_interval {F N m u m₁ : ℕ} [NeZero F] [NeZero m] [NeZero m₁] (hN : F = N * m)
    (hu : F = u * m₁) (a : ZMod m₁) (s j : ℕ) (hj : j < s) (p : ZMod F)
    (hp : blockCoord u m₁ p = a + (j : ZMod m₁)) :
    ∃ j' : ℕ, j' ≤ (a.val * u + s * u - 1) / N - a.val * u / N ∧
      blockCoord N m p = ((a.val * u / N : ℕ) : ZMod m) + (j' : ZMod m) := by
  have hNpos : 0 < N := by
    rcases Nat.eq_zero_or_pos N with h | h
    · exact absurd (by simpa [h] using hN) (NeZero.ne F)
    · exact h
  have hupos : 0 < u := by
    rcases Nat.eq_zero_or_pos u with h | h
    · exact absurd (by simpa [h] using hu) (NeZero.ne F)
    · exact h
  have hm₁pos : 0 < m₁ := Nat.pos_of_ne_zero (NeZero.ne _)
  have hpv : p.val < u * m₁ := lt_of_lt_of_eq (ZMod.val_lt p) hu
  have hav : a.val < m₁ := ZMod.val_lt a
  have hcell : p.val / u < m₁ := by
    rw [Nat.div_lt_iff_lt_mul hupos]; linarith [mul_comm u m₁]
  have hcv : (blockCoord u m₁ p).val = p.val / u := blockCoord_val hu p
  have h1 : p.val / u = (a.val + j) % m₁ := by
    rw [← hcv, hp, ZMod.val_add, ZMod.val_natCast]
    simp [Nat.add_mod]
  set V := p.val with hV
  set β := a.val * u with hβ
  set c := V / u with hc
  set r := V % u with hr
  set t := (a.val + j) / m₁ with ht
  have hVu : u * c + r = V := Nat.div_add_mod V u
  have hr_lt : r < u := Nat.mod_lt _ hupos
  have htc : m₁ * t + c = a.val + j := by rw [h1]; exact Nat.div_add_mod (a.val + j) m₁
  have hβq : β + (j * u + r) = V + (u * m₁) * t := by
    have : u * (m₁ * t + c) = u * (a.val + j) := by rw [htc]
    nlinarith [hVu, this]
  set q := j * u + r with hq
  have hq_le : q + 1 ≤ s * u := by
    have : j * u + u ≤ s * u := by nlinarith [Nat.mul_le_mul_right u (show j + 1 ≤ s by omega)]
    omega
  have hbc : blockCoord N m p = (((β + q) / N : ℕ) : ZMod m) := by
    unfold blockCoord
    have : (β + q) / N = V / N + m * t := by
      have hNu : u * m₁ = N * m := hu.symm.trans hN
      rw [hβq, hNu, (by ring : N * m * t = N * (m * t)), Nat.add_mul_div_left _ _ hNpos]
    rw [this]; push_cast
    simp
    rfl
  have hle : β / N ≤ (β + q) / N := Nat.div_le_div_right (by omega)
  refine ⟨(β + q) / N - β / N, ?_, ?_⟩
  · have : (β + q) / N ≤ (β + s * u - 1) / N := Nat.div_le_div_right (by omega)
    omega
  · rw [hbc, ← Nat.cast_add, Nat.add_sub_cancel' hle]

/-- The length of the block interval. -/
theorem blockInterval_le {N s u β : ℕ} (hN : 0 < N) :
    (β + s * u - 1) / N - β / N ≤ (s * u + N - 2) / N := by
  have hβN : β = N * (β / N) + β % N := (Nat.div_add_mod β N).symm
  have hlt : β % N < N := Nat.mod_lt _ hN
  by_cases hsu : s * u = 0
  · have : (β + s * u - 1) / N ≤ β / N := Nat.div_le_div_right (by omega)
    exact le_trans (by omega) (Nat.zero_le _)
  · have hpos : 1 ≤ s * u := Nat.one_le_iff_ne_zero.2 hsu
    have h2 : (β + s * u - 1) / N ≤ β / N + (s * u - 1 + N - 1) / N := by
      have : β + s * u - 1 = N * (β / N) + (β % N + (s * u - 1)) := by omega
      rw [this, Nat.mul_add_div hN]
      have : (β % N + (s * u - 1)) / N ≤ (s * u - 1 + N - 1) / N := Nat.div_le_div_right (by omega)
      omega
    have h3 : (s * u - 1 + N - 1) / N = (s * u + N - 2) / N := by congr 1; omega
    rw [h3] at h2
    exact Nat.sub_le_of_le_add (by linarith)

end Balaban
