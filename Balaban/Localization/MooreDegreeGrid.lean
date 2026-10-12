/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Int.Interval
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Grid bases near an interval (VMOD-24 Lemma 3.1, one-coordinate count)

On the cyclic group `ZMod n`, let `q ∣ n`.  The grid bases of side `q` are the residues `b` with
`q ∣ b.val`.  If `[b, b + q)` contains a point within distance one of the interval `[a, a + p)`
then `b - a` lies among the `p + q + 1` residues `-q, ..., p`, and the grid bases among them
number at most `p / q + 2` (`card_gridBases_le`).  The bound does not need `p ∣ n`, and the
wrap-around of the circle cannot add candidates.
-/

@[expose] public section

namespace Balaban.Localization

/-- `b` is a grid base of side `q` which is **Moore-near** the interval `[a, a + p)`: some point
`b + j`, `j < q`, of the interval `[b, b + q)` is within distance `1` of some point `a + i`,
`i < p`. -/
def NearGridBase {n : ℕ} (p q : ℕ) (a b : ZMod n) : Prop :=
  q ∣ b.val ∧ ∃ j i : ℕ, j < q ∧ i < p ∧ ∃ s : ℤ, |s| ≤ 1 ∧ a + (i : ZMod n) = b + (j : ZMod n) + s

open Classical in
/-- **One-coordinate count.**  For `q ∣ n`, `0 < q`, at most `p / q + 2` grid bases of side `q`
are Moore-near a given interval of length `p`. -/
theorem card_gridBases_le {n : ℕ} [NeZero n] (p q : ℕ) (hq : 0 < q) (hqn : q ∣ n) (a : ZMod n) :
    ((Finset.univ : Finset (ZMod n)).filter (NearGridBase p q a)).card ≤ p / q + 2 := by
  set r : ℤ := (-(a.val : ℤ)) % q with hr
  have hqz : (0 : ℤ) < q := by exact_mod_cast hq
  have hr0 : 0 ≤ r := Int.emod_nonneg _ hqz.ne'
  have hrq : r < q := Int.emod_lt_of_pos _ hqz
  have hsub : (Finset.univ : Finset (ZMod n)).filter (NearGridBase p q a) ⊆
      (Finset.Icc (-1 : ℤ) ((p / q : ℕ) : ℤ)).image
        (fun m : ℤ => a + ((q * m + r : ℤ) : ZMod n)) := by
    intro b hb
    obtain ⟨⟨c, hc⟩, j, i, hj, hi, s, hs, hbs⟩ := (Finset.mem_filter.1 hb).2
    rw [Finset.mem_image]
    -- the integer offset `t` with `b = a + t`
    set t : ℤ := (i : ℤ) - j - s with ht
    have hbt : b = a + (t : ZMod n) := by
      have : b = a + (i : ZMod n) - (j : ZMod n) - (s : ZMod n) := by
        rw [hbs]; ring
      rw [this, ht]; push_cast; ring
    have hs' := abs_le.1 hs
    have hij : (i : ℤ) < p := by exact_mod_cast hi
    have hjq : (j : ℤ) < q := by exact_mod_cast hj
    have ht1 : -(q : ℤ) ≤ t := by rw [ht]; omega
    have ht2 : t ≤ p := by rw [ht]; omega
    -- congruence `b.val ≡ a.val + t (mod n)`, hence mod `q`
    have hcong : ((b.val : ℤ) : ZMod n) = ((a.val + t : ℤ) : ZMod n) := by
      push_cast
      rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
      exact hbt
    obtain ⟨e, he⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).1 hcong
    have hqnz : (q : ℤ) ∣ n := by exact_mod_cast hqn
    obtain ⟨f, hf⟩ := hqnz
    -- `t + a.val = q * (c + f * e)`
    have h1 : (a.val : ℤ) + t = (q : ℤ) * (c + f * e) := by
      have hb' : (b.val : ℤ) = (q : ℤ) * c := by exact_mod_cast hc
      rw [hf] at he
      linarith
    have hdec := Int.emod_add_mul_ediv (-(a.val : ℤ)) q
    set e' : ℤ := (-(a.val : ℤ)) / q with he'
    have hm : t = q * (c + f * e + e') + r := by
      have : (-(a.val : ℤ)) = r + q * e' := by
        rw [hr]; exact hdec.symm
      nlinarith
    refine ⟨c + f * e + e', Finset.mem_Icc.2 ⟨?_, ?_⟩, ?_⟩
    · by_contra hlt
      have hlt' : c + f * e + e' ≤ -2 := by omega
      nlinarith
    · have hle : (q : ℤ) * (c + f * e + e') ≤ p := by linarith
      have := Int.le_ediv_of_mul_le hqz (by linarith : (c + f * e + e') * q ≤ p)
      rw [show ((p / q : ℕ) : ℤ) = (p : ℤ) / q by exact_mod_cast Int.natCast_ediv p q]
      exact this
    · rw [hbt, ← hm]
  refine (Finset.card_le_card hsub).trans (Finset.card_image_le.trans ?_)
  rw [Int.card_Icc]
  generalize p / q = u
  omega

end Balaban.Localization
