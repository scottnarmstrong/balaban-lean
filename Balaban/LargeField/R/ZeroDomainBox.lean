module

public import Balaban.Lattice.Blocks
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The blocks meeting a cyclic interval of cubes

If `p ∈ ℤ/F` lies in the `c`-th cell of size `u` (`F = u m₁`) with `c ∈ {a, …, a + s - 1}` (cyclic in `ℤ/m₁`),
then its block of size `N` (`F = N m`) is `b₀ + j` with `b₀` the block of the first site of the cell `a`
and `0 ≤ j ≤ (s u + N - 2)/N`.
-/

@[expose] public section

namespace Balaban

theorem blockCoord_box_image {F N m u m₁ : ℕ} [NeZero F] [NeZero m] [NeZero m₁] (hN : F = N * m)
    (hu : F = u * m₁) (a : ZMod m₁) (s j : ℕ) (hj : j < s) (p : ZMod F)
    (hp : blockCoord u m₁ p = a + (j : ZMod m₁)) :
    ∃ j' : ℕ, j' ≤ (s * u + N - 2) / N ∧
      blockCoord N m p = blockCoord N m (((a.val * u : ℕ) : ZMod F)) + (j' : ZMod m) := by
  have hNpos : 0 < N := by
    rcases Nat.eq_zero_or_pos N with h | h
    · exact absurd (by simpa [h] using hN) (NeZero.ne F)
    · exact h
  have hupos : 0 < u := by
    rcases Nat.eq_zero_or_pos u with h | h
    · exact absurd (by simpa [h] using hu) (NeZero.ne F)
    · exact h
  have hm₁pos : 0 < m₁ := Nat.pos_of_ne_zero (NeZero.ne _)
  have hmpos : 0 < m := Nat.pos_of_ne_zero (NeZero.ne _)
  have hpv : p.val < u * m₁ := lt_of_lt_of_eq (ZMod.val_lt p) hu
  have hav : a.val < m₁ := ZMod.val_lt a
  -- the cell index of `p`
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
  -- block coordinate of `p`
  have hbc : blockCoord N m p = (((β + q) / N : ℕ) : ZMod m) := by
    unfold blockCoord
    have : (β + q) / N = V / N + m * t := by
      have hNu : u * m₁ = N * m := hu.symm.trans hN
      rw [hβq, hNu, (by ring : N * m * t = N * (m * t)), Nat.add_mul_div_left _ _ hNpos]
    rw [this]; push_cast
    simp
    rfl
  have hβF : β < F := by rw [hu]; calc a.val * u < m₁ * u := Nat.mul_lt_mul_of_pos_right hav hupos
      _ = u * m₁ := mul_comm _ _
  have hb0 : blockCoord N m (((β : ℕ) : ZMod F)) = ((β / N : ℕ) : ZMod m) := by
    unfold blockCoord
    rw [ZMod.val_natCast_of_lt hβF]
  refine ⟨(β + q) / N - β / N, ?_, ?_⟩
  · -- the bound
    have h2 : (β + q) / N ≤ β / N + (q + N - 1) / N := by
      have hβN : β = N * (β / N) + β % N := (Nat.div_add_mod β N).symm
      have hlt : β % N < N := Nat.mod_lt _ hNpos
      have : β + q = N * (β / N) + (β % N + q) := by omega
      rw [this, Nat.mul_add_div hNpos]
      have : (β % N + q) / N ≤ (q + N - 1) / N := Nat.div_le_div_right (by omega)
      omega
    have h3 : (q + N - 1) / N ≤ (s * u + N - 2) / N := Nat.div_le_div_right (by omega)
    exact Nat.sub_le_of_le_add (by linarith)
  · rw [hbc, hb0]
    have hle : β / N ≤ (β + q) / N := Nat.div_le_div_right (by omega)
    rw [← Nat.cast_add, Nat.add_sub_cancel' hle]

end Balaban
