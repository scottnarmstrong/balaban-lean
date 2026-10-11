/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Background.BlockGeometry
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

/-!
# The cardinal quadratic B-spline and its periodization (LEMMA53-astra.md, §3, §6 item 5)

`bsp` is the cardinal quadratic B-spline `β`, written as a combination of truncated squares so
that the support, nonnegativity, lower bound at the centre and the first and second difference
bounds are proved without case analysis on the pairs of arguments.  `perN r α = ∑_p β(α + p r)` is
its periodization (finitely many nonzero terms), used for the bumps of blocks on the torus.

Constants: the second difference of `β` is bounded by `4 s²` (the note has `2 s²`; the constant
is immaterial), and `|β(t + s) - β(t)| ≤ 30 |s|` for `|s| ≤ 1/2`.
-/

@[expose] public section

namespace Balaban.Background


noncomputable def tp (x : ℝ) : ℝ := (max x 0) ^ 2

noncomputable def bsp (t : ℝ) : ℝ :=
  (tp (t + 3 / 2) - 3 * tp (t + 1 / 2) + 3 * tp (t - 1 / 2) - tp (t - 3 / 2)) / 2

theorem tp_of_nonneg {x : ℝ} (h : 0 ≤ x) : tp x = x ^ 2 := by simp [tp, max_eq_left h]
theorem tp_of_nonpos {x : ℝ} (h : x ≤ 0) : tp x = 0 := by simp [tp, max_eq_right h]

theorem bsp_far_left {t : ℝ} (h : t ≤ -3 / 2) : bsp t = 0 := by
  unfold bsp
  rw [tp_of_nonpos (by linarith), tp_of_nonpos (by linarith), tp_of_nonpos (by linarith), tp_of_nonpos (by linarith)]
  ring

theorem bsp_far_right {t : ℝ} (h : 3 / 2 ≤ t) : bsp t = 0 := by
  unfold bsp
  rw [tp_of_nonneg (by linarith), tp_of_nonneg (by linarith), tp_of_nonneg (by linarith), tp_of_nonneg (by linarith)]
  ring

theorem bsp_left {t : ℝ} (h1 : -3 / 2 ≤ t) (h2 : t ≤ -1 / 2) : bsp t = (t + 3 / 2) ^ 2 / 2 := by
  unfold bsp
  rw [tp_of_nonneg (by linarith), tp_of_nonpos (by linarith), tp_of_nonpos (by linarith), tp_of_nonpos (by linarith)]
  ring

theorem bsp_mid {t : ℝ} (h1 : -1 / 2 ≤ t) (h2 : t ≤ 1 / 2) : bsp t = 3 / 4 - t ^ 2 := by
  unfold bsp
  rw [tp_of_nonneg (by linarith), tp_of_nonneg (by linarith), tp_of_nonpos (by linarith), tp_of_nonpos (by linarith)]
  ring

theorem bsp_right {t : ℝ} (h1 : 1 / 2 ≤ t) (h2 : t ≤ 3 / 2) : bsp t = (3 / 2 - t) ^ 2 / 2 := by
  unfold bsp
  rw [tp_of_nonneg (by linarith), tp_of_nonneg (by linarith), tp_of_nonneg (by linarith), tp_of_nonpos (by linarith)]
  ring

theorem bsp_nonneg (t : ℝ) : 0 ≤ bsp t := by
  rcases le_total t (-3/2) with h | h
  · rw [bsp_far_left h]
  rcases le_total t (-1/2) with h' | h'
  · rw [bsp_left h h']; positivity
  rcases le_total t (1/2) with h'' | h''
  · rw [bsp_mid h' h'']; nlinarith
  rcases le_total t (3/2) with h3 | h3
  · rw [bsp_right h'' h3]; positivity
  · rw [bsp_far_right h3]

theorem bsp_le (t : ℝ) : bsp t ≤ 3 / 4 := by
  rcases le_total t (-3/2) with h | h
  · rw [bsp_far_left h]; norm_num
  rcases le_total t (-1/2) with h' | h'
  · rw [bsp_left h h']; nlinarith
  rcases le_total t (1/2) with h'' | h''
  · rw [bsp_mid h' h'']; nlinarith
  rcases le_total t (3/2) with h3 | h3
  · rw [bsp_right h'' h3]; nlinarith
  · rw [bsp_far_right h3]; norm_num

theorem bsp_eq_zero {t : ℝ} (h : 3 / 2 ≤ |t|) : bsp t = 0 := by
  rcases le_abs'.1 h with h | h
  · exact bsp_far_left (by linarith)
  · exact bsp_far_right h

theorem abs_lt_of_bsp_ne_zero {t : ℝ} (h : bsp t ≠ 0) : |t| < 3 / 2 := by
  by_contra h'
  exact h (bsp_eq_zero (not_lt.1 h'))

theorem bsp_ge_half {t : ℝ} (h : |t| ≤ 1 / 2) : 1 / 2 ≤ bsp t := by
  rw [abs_le] at h
  rw [bsp_mid (by linarith [h.1]) (by linarith [h.2])]; nlinarith [h.1, h.2]

theorem tp_second {x s : ℝ} : 0 ≤ tp (x + s) + tp (x - s) - 2 * tp x ∧
    tp (x + s) + tp (x - s) - 2 * tp x ≤ 2 * s ^ 2 := by
  unfold tp
  rcases le_total 0 s with hs | hs
  · rcases le_total 0 (x - s) with h1 | h1
    · have h2 : 0 ≤ x + s := by linarith
      have h3 : 0 ≤ x := by linarith
      rw [max_eq_left h2, max_eq_left h1, max_eq_left h3]; constructor <;> nlinarith
    rcases le_total 0 x with h3 | h3
    · have h2 : 0 ≤ x + s := by linarith
      rw [max_eq_left h2, max_eq_right h1, max_eq_left h3]; constructor <;> nlinarith
    rcases le_total 0 (x + s) with h2 | h2
    · rw [max_eq_left h2, max_eq_right h1, max_eq_right h3]; constructor <;> nlinarith
    · rw [max_eq_right h2, max_eq_right h1, max_eq_right h3]; constructor <;> nlinarith
  · rcases le_total 0 (x + s) with h1 | h1
    · have h2 : 0 ≤ x - s := by linarith
      have h3 : 0 ≤ x := by linarith
      rw [max_eq_left h2, max_eq_left h1, max_eq_left h3]; constructor <;> nlinarith
    rcases le_total 0 x with h3 | h3
    · have h2 : 0 ≤ x - s := by linarith
      rw [max_eq_left h2, max_eq_right h1, max_eq_left h3]; constructor <;> nlinarith
    rcases le_total 0 (x - s) with h2 | h2
    · rw [max_eq_left h2, max_eq_right h1, max_eq_right h3]; constructor <;> nlinarith
    · rw [max_eq_right h2, max_eq_right h1, max_eq_right h3]; constructor <;> nlinarith

theorem bsp_second (t s : ℝ) : |bsp (t + s) + bsp (t - s) - 2 * bsp t| ≤ 4 * s ^ 2 := by
  have h1 := tp_second (x := t + 3 / 2) (s := s)
  have h2 := tp_second (x := t + 1 / 2) (s := s)
  have h3 := tp_second (x := t - 1 / 2) (s := s)
  have h4 := tp_second (x := t - 3 / 2) (s := s)
  have e : bsp (t + s) + bsp (t - s) - 2 * bsp t =
      ((tp (t + 3 / 2 + s) + tp (t + 3 / 2 - s) - 2 * tp (t + 3 / 2))
        - 3 * (tp (t + 1 / 2 + s) + tp (t + 1 / 2 - s) - 2 * tp (t + 1 / 2))
        + 3 * (tp (t - 1 / 2 + s) + tp (t - 1 / 2 - s) - 2 * tp (t - 1 / 2))
        - (tp (t - 3 / 2 + s) + tp (t - 3 / 2 - s) - 2 * tp (t - 3 / 2))) / 2 := by
    unfold bsp
    have a1 : t + s + 3 / 2 = t + 3 / 2 + s := by ring
    have a2 : t - s + 3 / 2 = t + 3 / 2 - s := by ring
    have a3 : t + s + 1 / 2 = t + 1 / 2 + s := by ring
    have a4 : t - s + 1 / 2 = t + 1 / 2 - s := by ring
    have a5 : t + s - 1 / 2 = t - 1 / 2 + s := by ring
    have a6 : t - s - 1 / 2 = t - 1 / 2 - s := by ring
    have a7 : t + s - 3 / 2 = t - 3 / 2 + s := by ring
    have a8 : t - s - 3 / 2 = t - 3 / 2 - s := by ring
    rw [a1, a2, a3, a4, a5, a6, a7, a8]; ring
  rw [e, abs_le]
  constructor <;> nlinarith [h1.1, h1.2, h2.1, h2.2, h3.1, h3.2, h4.1, h4.2]

theorem tp_diff {x s : ℝ} : |tp (x + s) - tp x| ≤ |s| * (2 * |x| + |s|) := by
  unfold tp
  have h1 : |max (x + s) 0 - max x 0| ≤ |s| := by
    have := abs_max_sub_max_le_abs (x + s) x 0
    simpa using this
  have h2 : |max (x + s) 0 + max x 0| ≤ 2 * |x| + |s| := by
    have a : |max (x + s) 0| ≤ |x| + |s| := by
      rw [abs_of_nonneg (le_max_right _ _)]
      refine max_le ?_ (by positivity)
      calc x + s ≤ |x + s| := le_abs_self _
        _ ≤ |x| + |s| := abs_add_le _ _
    have b : |max x 0| ≤ |x| := by
      rw [abs_of_nonneg (le_max_right _ _)]
      exact max_le (le_abs_self _) (abs_nonneg _)
    calc _ ≤ |max (x + s) 0| + |max x 0| := abs_add_le _ _
      _ ≤ _ := by linarith
  have : (max (x + s) 0) ^ 2 - (max x 0) ^ 2 =
      (max (x + s) 0 - max x 0) * (max (x + s) 0 + max x 0) := by ring
  rw [this, abs_mul]
  exact mul_le_mul h1 h2 (abs_nonneg _) (abs_nonneg _)

theorem bsp_diff (t s : ℝ) (hs : |s| ≤ 1 / 2) : |bsp (t + s) - bsp t| ≤ 30 * |s| := by
  by_cases ht : |t| ≤ 2
  · have key : ∀ x : ℝ, |x| ≤ 7 / 2 → |tp (x + s) - tp x| ≤ 15 / 2 * |s| := by
      intro x hx
      refine tp_diff.trans ?_
      have := abs_nonneg s
      nlinarith
    have e : bsp (t + s) - bsp t = ((tp (t + 3 / 2 + s) - tp (t + 3 / 2))
        - 3 * (tp (t + 1 / 2 + s) - tp (t + 1 / 2)) + 3 * (tp (t - 1 / 2 + s) - tp (t - 1 / 2))
        - (tp (t - 3 / 2 + s) - tp (t - 3 / 2))) / 2 := by
      unfold bsp
      have a1 : t + s + 3 / 2 = t + 3 / 2 + s := by ring
      have a3 : t + s + 1 / 2 = t + 1 / 2 + s := by ring
      have a5 : t + s - 1 / 2 = t - 1 / 2 + s := by ring
      have a7 : t + s - 3 / 2 = t - 3 / 2 + s := by ring
      rw [a1, a3, a5, a7]; ring
    have b := abs_le.1 ht
    have k1 := abs_le.1 (key (t + 3 / 2) (by rw [abs_le]; constructor <;> linarith))
    have k2 := abs_le.1 (key (t + 1 / 2) (by rw [abs_le]; constructor <;> linarith))
    have k3 := abs_le.1 (key (t - 1 / 2) (by rw [abs_le]; constructor <;> linarith))
    have k4 := abs_le.1 (key (t - 3 / 2) (by rw [abs_le]; constructor <;> linarith))
    rw [e, abs_le]
    have := abs_nonneg s
    constructor <;> nlinarith [k1.1, k1.2, k2.1, k2.2, k3.1, k3.2, k4.1, k4.2]
  · have h1 : bsp t = 0 := bsp_eq_zero (by linarith)
    have h2 : bsp (t + s) = 0 := by
      refine bsp_eq_zero ?_
      have := abs_sub_abs_le_abs_sub t (-s)
      rw [sub_neg_eq_add] at this
      have := abs_neg s
      linarith [abs_nonneg s, abs_sub_abs_le_abs_sub t (-s), neg_neg s]
    rw [h1, h2]; simp

/-- A finite window containing all `p` with `|α + p r| ≤ 2`. -/
noncomputable def Tset (r α : ℝ) : Finset ℤ := Finset.Icc ⌈(-2 - α) / r⌉ ⌊(2 - α) / r⌋

theorem mem_Tset {r α : ℝ} (hr : 0 < r) {p : ℤ} (h : |α + p * r| ≤ 2) : p ∈ Tset r α := by
  rw [abs_le] at h
  unfold Tset
  rw [Finset.mem_Icc, Int.ceil_le, Int.le_floor]
  constructor
  · rw [div_le_iff₀ hr]; linarith
  · rw [le_div_iff₀ hr]; linarith

theorem card_Tset_le {r : ℝ} (hr : 1 ≤ r) (α : ℝ) : (Tset r α).card ≤ 5 := by
  unfold Tset
  rw [Int.card_Icc]
  have hr0 : 0 < r := by linarith
  have h1 : ((-2 - α) / r) ≤ ⌈(-2 - α) / r⌉ := Int.le_ceil _
  have h2 : (⌊(2 - α) / r⌋ : ℝ) ≤ (2 - α) / r := Int.floor_le _
  have h3 : (2 - α) / r - (-2 - α) / r = 4 / r := by field_simp; ring
  have h4 : 4 / r ≤ 4 := by rw [div_le_iff₀ hr0]; nlinarith
  have h5 : ((⌊(2 - α) / r⌋ + 1 - ⌈(-2 - α) / r⌉ : ℤ) : ℝ) ≤ 5 := by push_cast; linarith
  have h6 : (⌊(2 - α) / r⌋ + 1 - ⌈(-2 - α) / r⌉ : ℤ) ≤ 5 := by exact_mod_cast h5
  omega

/-- The periodized spline in normalized variables: `∑_p β(α + p r)`. -/
noncomputable def perN (r α : ℝ) : ℝ := ∑ᶠ p : ℤ, bsp (α + p * r)

theorem perN_eq_sum {r α α' : ℝ} (hr : 0 < r) (h : |α' - α| ≤ 1 / 2) :
    perN r α' = ∑ p ∈ Tset r α, bsp (α' + p * r) := by
  unfold perN
  refine finsum_eq_sum_of_support_subset _ fun p hp => ?_
  have hp' : bsp (α' + p * r) ≠ 0 := hp
  have := abs_lt_of_bsp_ne_zero hp'
  refine mem_Tset hr ?_
  have h2 : α + p * r = (α' + p * r) - (α' - α) := by ring
  rw [h2]
  calc |(α' + p * r) - (α' - α)| ≤ |α' + p * r| + |α' - α| := abs_sub _ _
    _ ≤ 2 := by linarith

theorem perN_nonneg {r : ℝ} (hr : 0 < r) (α : ℝ) : 0 ≤ perN r α := by
  rw [perN_eq_sum hr (α := α) (by simp)]
  exact Finset.sum_nonneg fun p _ => bsp_nonneg _

theorem perN_le {r : ℝ} (hr : 1 ≤ r) (α : ℝ) : perN r α ≤ 4 := by
  have hr0 : 0 < r := by linarith
  rw [perN_eq_sum hr0 (α := α) (by simp)]
  calc ∑ p ∈ Tset r α, bsp (α + p * r) ≤ ∑ _p ∈ Tset r α, (3 / 4 : ℝ) :=
        Finset.sum_le_sum fun p _ => bsp_le _
    _ = (Tset r α).card * (3 / 4) := by simp
    _ ≤ 5 * (3 / 4) := by
        have := card_Tset_le hr α
        have : ((Tset r α).card : ℝ) ≤ 5 := by exact_mod_cast this
        nlinarith
    _ ≤ 4 := by norm_num

theorem bsp_le_perN {r : ℝ} (hr : 0 < r) {α : ℝ} (h : |α| ≤ 2) : bsp α ≤ perN r α := by
  have hα : α ∈ Set.Icc (-2 : ℝ) 2 := abs_le.1 h
  rw [perN_eq_sum hr (α := α) (by simp)]
  have h0 : (0 : ℤ) ∈ Tset r α := mem_Tset hr (by simpa using h)
  have := Finset.single_le_sum (f := fun p : ℤ => bsp (α + p * r)) (fun p _ => bsp_nonneg _) h0
  simpa using this

theorem exists_of_perN_ne_zero {r α : ℝ} (h : perN r α ≠ 0) : ∃ p : ℤ, |α + p * r| < 3 / 2 := by
  by_contra hcon
  have hcon' : ∀ p : ℤ, 3 / 2 ≤ |α + p * r| := fun p => not_lt.1 fun h => hcon ⟨p, h⟩
  apply h
  unfold perN
  exact finsum_eq_zero_of_forall_eq_zero fun p => bsp_eq_zero (hcon' p)

theorem perN_diff1 {r : ℝ} (hr : 1 ≤ r) (α s : ℝ) (hs : |s| ≤ 1 / 2) :
    |perN r (α + s) - perN r α| ≤ 150 * |s| := by
  have hr0 : 0 < r := by linarith
  have h1 : |α + s - α| ≤ 1 / 2 := by simpa using hs
  rw [perN_eq_sum hr0 h1, perN_eq_sum hr0 (α := α) (by simp), ← Finset.sum_sub_distrib]
  calc |∑ p ∈ Tset r α, (bsp (α + s + p * r) - bsp (α + p * r))|
      ≤ ∑ p ∈ Tset r α, |bsp (α + s + p * r) - bsp (α + p * r)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _p ∈ Tset r α, 30 * |s| := Finset.sum_le_sum fun p _ => by
        have := bsp_diff (α + p * r) s hs
        rwa [show α + p * r + s = α + s + p * r by ring] at this
    _ = (Tset r α).card * (30 * |s|) := by simp
    _ ≤ 5 * (30 * |s|) := by
        have : ((Tset r α).card : ℝ) ≤ 5 := by exact_mod_cast card_Tset_le hr α
        nlinarith [abs_nonneg s]
    _ = 150 * |s| := by ring

theorem perN_diff2 {r : ℝ} (hr : 1 ≤ r) (α s : ℝ) (hs : |s| ≤ 1 / 2) :
    |perN r (α + s) + perN r (α - s) - 2 * perN r α| ≤ 20 * s ^ 2 := by
  have hr0 : 0 < r := by linarith
  have h1 : |α + s - α| ≤ 1 / 2 := by simpa using hs
  have h2 : |α - s - α| ≤ 1 / 2 := by simpa [abs_neg] using hs
  rw [perN_eq_sum hr0 h1, perN_eq_sum hr0 h2, perN_eq_sum hr0 (α := α) (by simp),
    Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  calc |∑ p ∈ Tset r α, (bsp (α + s + p * r) + bsp (α - s + p * r) - 2 * bsp (α + p * r))|
      ≤ ∑ p ∈ Tset r α, |bsp (α + s + p * r) + bsp (α - s + p * r) - 2 * bsp (α + p * r)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _p ∈ Tset r α, 4 * s ^ 2 := Finset.sum_le_sum fun p _ => by
        have := bsp_second (α + p * r) s
        rwa [show α + p * r + s = α + s + p * r by ring,
          show α + p * r - s = α - s + p * r by ring] at this
    _ = (Tset r α).card * (4 * s ^ 2) := by simp
    _ ≤ 5 * (4 * s ^ 2) := by
        have : ((Tset r α).card : ℝ) ≤ 5 := by exact_mod_cast card_Tset_le hr α
        nlinarith [sq_nonneg s]
    _ = 20 * s ^ 2 := by ring

end Balaban.Background
