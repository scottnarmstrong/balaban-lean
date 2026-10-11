module

public import Balaban.LargeField.Geometry.Distance
public import Balaban.Lattice.Blocks
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Coarsening (Part I, Definition I.2.3 and Lemma I.2.4)

The coarsening `x ↦ x^↑` of `𝕋_k` to `𝕋_{k+1}` is `Balaban.blockMap L (n (k+1))`, where
`n_k = L * n_{k+1}`. Lemma I.2.4: `d(x^↑, y^↑) ≤ ⌈d(x, y)/L⌉` (`supDist_blockMap_le`, with
`⌈t/L⌉ = (t + L - 1)/L`) and `d(x, y) ≤ L d(x^↑, y^↑) + L - 1` (`supDist_le_blockMap`).
-/

@[expose] public section

namespace Balaban.LargeField

open Balaban

section Coord

variable {d L n m : ℕ} [NeZero n] [NeZero m]

omit [NeZero m] in
private theorem pos_of_eq (hn : n = L * m) : 0 < L := by
  rcases Nat.eq_zero_or_pos L with h | h
  · exact absurd (by simpa [h] using hn) (NeZero.ne n)
  · exact h

omit [NeZero m] in
/-- The block of any integer lift `z` of `a`: `blockCoord L m a = ⌊z / L⌋` modulo `m`. -/
theorem blockCoord_intCast (hn : n = L * m) (a : ZMod n) (z : ℤ) (hz : (z : ZMod n) = a) :
    blockCoord L m a = ((z / L : ℤ) : ZMod m) := by
  have hL := pos_of_eq hn
  have hdvd : (n : ℤ) ∣ z - a.val := by
    rw [← ZMod.intCast_eq_intCast_iff_dvd_sub]
    simpa using hz.symm
  obtain ⟨q, hq⟩ := hdvd
  have hz' : z = a.val + (L : ℤ) * (m * q) := by
    have : (n : ℤ) = L * m := by exact_mod_cast hn
    rw [this] at hq; linarith
  have hdiv : z / L = (a.val / L : ℕ) + m * q := by
    rw [hz', Int.add_mul_ediv_left _ _ (by exact_mod_cast hL.ne')]
    simp
  rw [hdiv]
  unfold blockCoord
  rw [Int.cast_add, Int.cast_natCast, Int.cast_mul, Int.cast_natCast, ZMod.natCast_self,
    zero_mul, add_zero]

variable (hn : n = L * m)
include hn

/-- Coarsening does not increase a cyclic displacement by more than a factor `L`:
`|A - B|_m ≤ ⌈|a - b|_n / L⌉`. -/
theorem cycNorm_blockCoord_le (a b : ZMod n) {t : ℕ} (h : cycNorm n (a - b) ≤ t) :
    cycNorm m (blockCoord L m a - blockCoord L m b) ≤ (t + L - 1) / L := by
  have hL := pos_of_eq hn
  obtain ⟨u, hu, hub⟩ := (cycNorm_le_iff _ _).mp h
  have ha : ((a.val : ℤ) : ZMod n) = a := by simp
  have hb : (((a.val : ℤ) - u : ℤ) : ZMod n) = b := by
    push_cast; rw [hub] ; simp
  rw [blockCoord_intCast hn a _ ha, blockCoord_intCast hn b _ hb, ← Int.cast_sub,
    cycNorm_le_iff]
  set c : ℕ := (t + L - 1) / L with hc
  have hLc : (t : ℤ) ≤ L * c := by
    have h1 : t + L - 1 < L * (c + 1) := by
      rw [hc]
      have := Nat.lt_mul_div_succ (t + L - 1) hL
      simpa [mul_comm] using this
    have h1' : t + L - 1 < L * c + L := by rw [mul_add, mul_one] at h1; exact h1
    have : t ≤ L * c := by
      generalize L * c = P at h1' ⊢
      omega
    exact_mod_cast this
  have hu' := abs_le.mp hu
  have hLz : (0 : ℤ) < L := by exact_mod_cast hL
  refine ⟨(a.val : ℤ) / L - ((a.val : ℤ) - u) / L, ?_, rfl⟩
  rw [abs_le]
  have e1 : ((a.val : ℤ) + L * c) / L = (a.val : ℤ) / L + c := by
    rw [Int.add_mul_ediv_left _ _ hLz.ne']
  have e2 : ((a.val : ℤ) - L * c) / L = (a.val : ℤ) / L - c := by
    rw [sub_eq_add_neg, ← mul_neg, Int.add_mul_ediv_left _ _ hLz.ne']; ring
  have i1 : ((a.val : ℤ) - u) / L ≤ ((a.val : ℤ) + L * c) / L :=
    Int.ediv_le_ediv hLz (by nlinarith)
  have i2 : ((a.val : ℤ) - L * c) / L ≤ ((a.val : ℤ) - u) / L :=
    Int.ediv_le_ediv hLz (by nlinarith)
  constructor <;> linarith

/-- Lower bound: `|a - b|_n ≤ L |A - B|_m + L - 1`. -/
theorem cycNorm_le_blockCoord (a b : ZMod n) :
    cycNorm n (a - b) ≤ L * cycNorm m (blockCoord L m a - blockCoord L m b) + (L - 1) := by
  have hL := pos_of_eq hn
  obtain ⟨w, hw, hwe⟩ := (cycNorm_le_iff (n := m) _ _).mp
    (le_refl (cycNorm m (blockCoord L m a - blockCoord L m b)))
  have hLz : (0 : ℤ) < L := by exact_mod_cast hL
  have hA : blockCoord L m a = ((a.val / L : ℕ) : ZMod m) := rfl
  have hB : blockCoord L m b = ((b.val / L : ℕ) : ZMod m) := rfl
  rw [hA, hB] at hwe
  have hdvd : (m : ℤ) ∣ w - (((a.val / L : ℕ) : ℤ) - ((b.val / L : ℕ) : ℤ)) := by
    rw [← ZMod.intCast_eq_intCast_iff_dvd_sub, Int.cast_sub, Int.cast_natCast,
      Int.cast_natCast, hwe]
  obtain ⟨q, hq⟩ := hdvd
  have hnz : (n : ℤ) = L * m := by exact_mod_cast hn
  have ha1 := Nat.div_add_mod a.val L
  have hb1 := Nat.div_add_mod b.val L
  have ra := Nat.mod_lt a.val hL
  have rb := Nat.mod_lt b.val hL
  set s := cycNorm m (blockCoord L m a - blockCoord L m b) with hs
  rw [cycNorm_le_iff]
  have hw := abs_le.mp hw
  refine ⟨L * w + ((a.val % L : ℕ) - (b.val % L : ℕ)), ?_, ?_⟩
  · rw [abs_le]
    have hLs : (L : ℤ) * s ≥ L * w := mul_le_mul_of_nonneg_left hw.2 hLz.le
    have hLs' : (L : ℤ) * w ≥ -(L * s) := by nlinarith [hw.1]
    have h1 : ((L - 1 : ℕ) : ℤ) = L - 1 := by omega
    have ra' : ((a.val % L : ℕ) : ℤ) ≤ L - 1 := by omega
    have rb' : ((b.val % L : ℕ) : ℤ) ≤ L - 1 := by omega
    have ra0 : (0 : ℤ) ≤ ((a.val % L : ℕ) : ℤ) := by positivity
    have rb0 : (0 : ℤ) ≤ ((b.val % L : ℕ) : ℤ) := by positivity
    rw [Nat.cast_add, Nat.cast_mul, h1]
    constructor <;> linarith
  · have hsub : ((a - b : ZMod n)) = (a.val : ZMod n) - (b.val : ZMod n) := by simp
    rw [hsub]
    have key : (L : ℤ) * w + (((a.val % L : ℕ) : ℤ) - ((b.val % L : ℕ) : ℤ)) =
        ((a.val : ℤ) - b.val) + n * q := by
      have e1 : ((a.val : ℕ) : ℤ) = L * ((a.val / L : ℕ) : ℤ) + ((a.val % L : ℕ) : ℤ) := by
        exact_mod_cast ha1.symm
      have e2 : ((b.val : ℕ) : ℤ) = L * ((b.val / L : ℕ) : ℤ) + ((b.val % L : ℕ) : ℤ) := by
        exact_mod_cast hb1.symm
      rw [hnz]
      have : w = (((a.val / L : ℕ) : ℤ) - ((b.val / L : ℕ) : ℤ)) + m * q := by linarith
      rw [this]; rw [e1, e2]; ring
    have : (((L : ℤ) * w + (((a.val % L : ℕ) : ℤ) - ((b.val % L : ℕ) : ℤ)) : ℤ) : ZMod n) =
        (a.val : ZMod n) - (b.val : ZMod n) := by
      rw [key]; push_cast; simp
    exact this

/-- **Lemma I.2.4 (a)**: `d(x^↑, y^↑) ≤ ⌈d(x, y)/L⌉`, with `⌈t/L⌉ = (t + L - 1)/L`. -/
theorem supDist_blockMap_le (x y : Torus d n) :
    supDist (blockMap L m x) (blockMap L m y) ≤ (supDist x y + L - 1) / L :=
  supDist_le_iff.mpr fun i => cycNorm_blockCoord_le hn _ _ (cycNorm_le_supDist x y i)

/-- **Lemma I.2.4 (b)**: `d(x, y) ≤ L d(x^↑, y^↑) + L - 1`. -/
theorem supDist_le_blockMap (x y : Torus d n) :
    supDist x y ≤ L * supDist (blockMap L m x) (blockMap L m y) + (L - 1) :=
  supDist_le_iff.mpr fun i =>
    (cycNorm_le_blockCoord hn (x i) (y i)).trans
      (Nat.add_le_add_right
        (Nat.mul_le_mul_left L (cycNorm_le_supDist (blockMap L m x) (blockMap L m y) i)) _)

/-- **Lemma I.2.4 (b)**, in particular: points in the same coarse block are within `L - 1`. -/
theorem supDist_le_of_blockMap_eq {x y : Torus d n} (h : blockMap L m x = blockMap L m y) :
    supDist x y ≤ L - 1 := by
  have := supDist_le_blockMap hn x y
  rwa [h, supDist_self, mul_zero, zero_add] at this

/-- **Lemma I.2.4 (a)**, for sets: `(X^{∼k})^↑ ⊆ (X^↑)^{∼⌈k/L⌉}`. -/
theorem blockMap_nbhd_subset (k : ℕ) (X : Set (Torus d n)) :
    blockMap L m '' nbhd k X ⊆ nbhd ((k + L - 1) / L) (blockMap L m '' X) := by
  rintro _ ⟨y, hy, rfl⟩
  obtain ⟨x, hx, hxy⟩ := mem_nbhd.mp hy
  refine mem_nbhd.mpr ⟨blockMap L m x, ⟨x, hx, rfl⟩, ?_⟩
  refine (supDist_blockMap_le hn y x).trans ?_
  exact Nat.div_le_div_right (by omega)

end Coord

end Balaban.LargeField
