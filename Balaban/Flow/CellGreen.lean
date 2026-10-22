/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Flow.LatticeSums
public import Mathlib.Analysis.Fourier.ZMod

/-!
# The Green function of the periodic cell Laplacian

The block structure of the first-step operators reduces, after a Bloch decomposition, to the Laplacian of
the cycle `ℤ/M` (`M = L^m` the side of a block): `-Δ` with eigenvalues `λ_n = 2 − 2 cos (2π n/M)`.  This
file proves, with the orthogonality of the characters of `ZMod M` (`ZMod.stdAddChar`), the
resolvent identities of the cell with the zero mode removed:

* `cellGreen M ν j r = (1/M) ∑_{n ≠ 0} cos(2π n r/M) / (λ_n + ν)^j`;
* `(−Δ + ν) cellGreen (j+1) = cellGreen j`, `cellGreen 0 = δ_0 − 1/M` (`cellGreen_eq`);
* the first differences `cellGreen j 1 − cellGreen j 0 = −(1/(2M)) ∑ λ_n/(λ_n+ν)^j`.

These give the sums `c_i(v)` of P4 (5.13) in the form needed for the second moments of the first step.
-/

@[expose] public section

namespace Balaban.Flow

open Finset

variable {M : ℕ} [NeZero M]

/-- The angle `2π n/M` of the character of residue `n` (represented by `valMinAbs n`). -/
noncomputable def cellFreq (M : ℕ) (n : ZMod M) : ℝ := 2 * Real.pi * (ZMod.valMinAbs n : ℝ) / M

/-- The eigenvalue `λ_n = 2 − 2 cos (2π n/M)` of `−Δ` on the cycle `ℤ/M`. -/
noncomputable def cellEig (M : ℕ) (n : ZMod M) : ℝ := 2 - 2 * Real.cos (cellFreq M n)

omit [NeZero M] in
theorem latticeSymbol_eq_cellEig (n : ZMod M) : latticeSymbol M n = (M : ℝ) ^ 2 * cellEig M n := by
  unfold latticeSymbol cellEig cellFreq; ring

theorem cellEig_ge (n : ZMod M) : 16 * (ZMod.valMinAbs n : ℝ) ^ 2 / (M : ℝ) ^ 2 ≤ cellEig M n := by
  have hM : (0 : ℝ) < (M : ℝ) ^ 2 := by
    have : (0 : ℝ) < M := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne M)
    positivity
  have := latticeSymbol_ge n
  rw [latticeSymbol_eq_cellEig] at this
  rw [div_le_iff₀ hM]; linarith

theorem cellEig_pos {n : ZMod M} (hn : n ≠ 0) : 0 < cellEig M n := by
  have h0 : ZMod.valMinAbs n ≠ 0 := fun h => hn ((ZMod.valMinAbs_eq_zero n).1 h)
  have h1 := cellEig_ge n
  have hM : (0 : ℝ) < (M : ℝ) ^ 2 := by
    have : (0 : ℝ) < M := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne M)
    positivity
  have : (0 : ℝ) < (ZMod.valMinAbs n : ℝ) ^ 2 := by positivity
  have : 0 < 16 * (ZMod.valMinAbs n : ℝ) ^ 2 / (M : ℝ) ^ 2 := by positivity
  linarith

/-- **Orthogonality of the cosines**: `∑_n cos(2π n r/M) = M` if `M ∣ r`, else `0`. -/
theorem sum_cos_residues (r : ℤ) :
    ∑ n : ZMod M, Real.cos (cellFreq M n * r) = if (r : ZMod M) = 0 then (M : ℝ) else 0 := by
  classical
  have hc : ∀ n : ZMod M, Real.cos (cellFreq M n * r) =
      (ZMod.stdAddChar (((r : ZMod M)) * n)).re := by
    intro n
    have h1 : ((r : ZMod M)) * n = (((ZMod.valMinAbs n * r : ℤ)) : ZMod M) := by
      push_cast; ring
    rw [h1, ZMod.stdAddChar_coe]
    have : (2 * Real.pi * Complex.I * ((ZMod.valMinAbs n * r : ℤ) : ℂ) / (M : ℂ)) =
        ((cellFreq M n * r : ℝ) : ℂ) * Complex.I := by
      unfold cellFreq; push_cast; ring
    rw [this, Complex.exp_ofReal_mul_I_re]
  simp only [hc]
  have hs : ∑ n : ZMod M, ZMod.stdAddChar (((r : ZMod M)) * n) =
      if (r : ZMod M) = 0 then (M : ℂ) else 0 := by
    split_ifs with h
    · simp [h]
    · exact AddChar.sum_eq_zero_of_ne_one (ZMod.isPrimitive_stdAddChar M h)
  rw [← Complex.re_sum, hs]
  split_ifs <;> simp

/-- **The Green function of the cell with the zero mode removed**:
`(1/M) ∑_{n ≠ 0} cos(2π n r/M)/(λ_n + ν)^j`, for the integer position `r`. -/
noncomputable def cellGreen (M : ℕ) [NeZero M] (ν : ℝ) (j : ℕ) (r : ℤ) : ℝ :=
  (1 / (M : ℝ)) * ∑ n ∈ (Finset.univ : Finset (ZMod M)).erase 0,
    Real.cos (cellFreq M n * r) / (cellEig M n + ν) ^ j

theorem cellGreen_zero (ν : ℝ) (r : ℤ) :
    cellGreen M ν 0 r = (if (r : ZMod M) = 0 then 1 else 0) - 1 / (M : ℝ) := by
  have hM : (M : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne M
  have h := sum_cos_residues (M := M) r
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : ZMod M))] at h
  have h0 : Real.cos (cellFreq M 0 * r) = 1 := by simp [cellFreq]
  rw [h0] at h
  unfold cellGreen
  simp only [pow_zero, div_one]
  have : ∑ n ∈ (Finset.univ : Finset (ZMod M)).erase 0, Real.cos (cellFreq M n * r) =
      (if (r : ZMod M) = 0 then (M : ℝ) else 0) - 1 := by linarith
  rw [this]
  split_ifs
  · field_simp
  · simp

theorem cos_shift_add (θ : ℝ) (r : ℤ) :
    Real.cos (θ * ((r + 1 : ℤ) : ℝ)) + Real.cos (θ * ((r - 1 : ℤ) : ℝ)) =
      2 * Real.cos θ * Real.cos (θ * r) := by
  push_cast
  have e1 : θ * ((r : ℝ) + 1) = θ * r + θ := by ring
  have e2 : θ * ((r : ℝ) - 1) = θ * r - θ := by ring
  rw [e1, e2, Real.cos_add, Real.cos_sub]; ring

/-- `(−Δ + ν) G_{j+1} = G_j` on the cycle, for the Green functions without the zero mode. -/
theorem cellGreen_eq {ν : ℝ} (hν : 0 ≤ ν) (j : ℕ) (r : ℤ) :
    (2 + ν) * cellGreen M ν (j + 1) r - cellGreen M ν (j + 1) (r + 1) -
      cellGreen M ν (j + 1) (r - 1) = cellGreen M ν j r := by
  unfold cellGreen
  have key : ∀ n ∈ (Finset.univ : Finset (ZMod M)).erase 0,
      (2 + ν) * (Real.cos (cellFreq M n * r) / (cellEig M n + ν) ^ (j + 1)) -
        Real.cos (cellFreq M n * ((r + 1 : ℤ) : ℝ)) / (cellEig M n + ν) ^ (j + 1) -
        Real.cos (cellFreq M n * ((r - 1 : ℤ) : ℝ)) / (cellEig M n + ν) ^ (j + 1) =
        Real.cos (cellFreq M n * r) / (cellEig M n + ν) ^ j := by
    intro n hn
    have hpos : 0 < cellEig M n + ν := by
      have := cellEig_pos (Finset.mem_erase.1 hn).1; linarith
    have hs := cos_shift_add (cellFreq M n) r
    have hlam : cellEig M n = 2 - 2 * Real.cos (cellFreq M n) := rfl
    have h : (2 + ν) * Real.cos (cellFreq M n * r) - Real.cos (cellFreq M n * ((r + 1 : ℤ) : ℝ)) -
        Real.cos (cellFreq M n * ((r - 1 : ℤ) : ℝ)) =
        Real.cos (cellFreq M n * r) * (cellEig M n + ν) := by
      rw [hlam]
      linear_combination (-1 : ℝ) * hs
    have e : (2 + ν) * (Real.cos (cellFreq M n * r) / (cellEig M n + ν) ^ (j + 1)) -
        Real.cos (cellFreq M n * ((r + 1 : ℤ) : ℝ)) / (cellEig M n + ν) ^ (j + 1) -
        Real.cos (cellFreq M n * ((r - 1 : ℤ) : ℝ)) / (cellEig M n + ν) ^ (j + 1) =
        ((2 + ν) * Real.cos (cellFreq M n * r) - Real.cos (cellFreq M n * ((r + 1 : ℤ) : ℝ)) -
          Real.cos (cellFreq M n * ((r - 1 : ℤ) : ℝ))) / (cellEig M n + ν) ^ (j + 1) := by ring
    rw [e, h, pow_succ]
    field_simp
  have hsum : (2 + ν) * (1 / (M : ℝ) * ∑ n ∈ (Finset.univ : Finset (ZMod M)).erase 0,
        Real.cos (cellFreq M n * r) / (cellEig M n + ν) ^ (j + 1)) -
      1 / (M : ℝ) * ∑ n ∈ (Finset.univ : Finset (ZMod M)).erase 0,
        Real.cos (cellFreq M n * ((r + 1 : ℤ) : ℝ)) / (cellEig M n + ν) ^ (j + 1) -
      1 / (M : ℝ) * ∑ n ∈ (Finset.univ : Finset (ZMod M)).erase 0,
        Real.cos (cellFreq M n * ((r - 1 : ℤ) : ℝ)) / (cellEig M n + ν) ^ (j + 1) =
      1 / (M : ℝ) * ∑ n ∈ (Finset.univ : Finset (ZMod M)).erase 0,
        ((2 + ν) * (Real.cos (cellFreq M n * r) / (cellEig M n + ν) ^ (j + 1)) -
          Real.cos (cellFreq M n * ((r + 1 : ℤ) : ℝ)) / (cellEig M n + ν) ^ (j + 1) -
          Real.cos (cellFreq M n * ((r - 1 : ℤ) : ℝ)) / (cellEig M n + ν) ^ (j + 1)) := by
    simp only [Finset.sum_sub_distrib, ← Finset.mul_sum]; ring
  rw [hsum, Finset.sum_congr rfl key]

theorem cos_cellFreq_congr (n : ZMod M) {k k' : ℤ} (h : (k : ZMod M) = k') :
    Real.cos (cellFreq M n * k) = Real.cos (cellFreq M n * k') := by
  obtain ⟨t, ht⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub k k' M).1 h
  have hM : (M : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne M
  have : cellFreq M n * (k' : ℝ) = cellFreq M n * k + (ZMod.valMinAbs n * t : ℤ) * (2 * Real.pi) := by
    have h2 : (k' : ℝ) = k + M * t := by exact_mod_cast (by linarith : k' = k + M * t)
    rw [h2]; unfold cellFreq; push_cast; field_simp
  rw [this, Real.cos_add_int_mul_two_pi]

theorem cellGreen_congr (ν : ℝ) (j : ℕ) {r r' : ℤ} (h : (r : ZMod M) = r') :
    cellGreen M ν j r = cellGreen M ν j r' := by
  unfold cellGreen
  congr 1
  exact Finset.sum_congr rfl fun n _ => by rw [cos_cellFreq_congr n h]

theorem cellGreen_neg (ν : ℝ) (j : ℕ) (r : ℤ) : cellGreen M ν j (-r) = cellGreen M ν j r := by
  unfold cellGreen
  congr 1
  exact Finset.sum_congr rfl fun n _ => by push_cast; rw [mul_neg, Real.cos_neg]

theorem cellGreen_add_card (ν : ℝ) (j : ℕ) (r : ℤ) :
    cellGreen M ν j (r + M) = cellGreen M ν j r :=
  cellGreen_congr ν j (by push_cast; simp)

/-- The first difference of the Green function. -/
theorem cellGreen_diff (ν : ℝ) (j : ℕ) :
    cellGreen M ν j 1 - cellGreen M ν j 0 =
      -(1 / (2 * (M : ℝ))) * ∑ n ∈ (Finset.univ : Finset (ZMod M)).erase 0,
        cellEig M n / (cellEig M n + ν) ^ j := by
  unfold cellGreen
  rw [← mul_sub, ← Finset.sum_sub_distrib, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  have : Real.cos (cellFreq M n * ((1 : ℤ) : ℝ)) = 1 - cellEig M n / 2 := by
    unfold cellEig; push_cast; ring_nf
  have h0 : Real.cos (cellFreq M n * ((0 : ℤ) : ℝ)) = 1 := by simp
  rw [this, h0]
  have hM : (M : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne M
  field_simp
  ring

/-- The cycle Laplacian `(−Δ f)(r) = 2 f(r) − f(r+1) − f(r−1)` on `ZMod M`. -/
def cellNegLap (f : ZMod M → ℝ) (r : ZMod M) : ℝ := 2 * f r - f (r + 1) - f (r - 1)

theorem cell_sum_shift (F : ZMod M → ℝ) (a : ZMod M) : ∑ r, F (r + a) = ∑ r, F r :=
  Fintype.sum_equiv (Equiv.addRight a) _ _ (fun _ => rfl)

/-- Summation by parts on the cycle. -/
theorem sum_mul_cellNegLap (f g : ZMod M → ℝ) :
    ∑ r, f r * cellNegLap g r = ∑ r, g r * cellNegLap f r := by
  have h1 : ∑ r, f r * g (r + 1) = ∑ r, g r * f (r - 1) := by
    have := cell_sum_shift (fun r => g r * f (r - 1)) 1
    simp only [add_sub_cancel_right] at this
    rw [← this]; exact Finset.sum_congr rfl fun r _ => by ring
  have h2 : ∑ r, f r * g (r - 1) = ∑ r, g r * f (r + 1) := by
    have := cell_sum_shift (fun r => g r * f (r + 1)) (-1)
    simp only [sub_eq_add_neg] at *
    simp only [neg_add_cancel_right] at this
    rw [← this]; exact Finset.sum_congr rfl fun r _ => by ring
  have e : ∀ u v : ZMod M → ℝ, ∑ r, u r * cellNegLap v r =
      2 * ∑ r, u r * v r - ∑ r, u r * v (r + 1) - ∑ r, u r * v (r - 1) := by
    intro u v
    unfold cellNegLap
    have : ∀ r, u r * (2 * v r - v (r + 1) - v (r - 1)) =
        2 * (u r * v r) - u r * v (r + 1) - u r * v (r - 1) := fun r => by ring
    simp only [this, Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [e, e, h1, h2]
  have : ∑ r, f r * g r = ∑ r, g r * f r := Finset.sum_congr rfl fun r _ => mul_comm _ _
  rw [this]; ring

/-- The cosine mode `r ↦ cos(2π n r/M)` on `ZMod M`. -/
noncomputable def cellMode (M : ℕ) [NeZero M] (n r : ZMod M) : ℝ :=
  Real.cos (cellFreq M n * (ZMod.valMinAbs r : ℝ))

theorem cellMode_symm (n r : ZMod M) : cellMode M n r = cellMode M r n := by
  unfold cellMode cellFreq; congr 1; ring

theorem cellMode_zero_left (r : ZMod M) : cellMode M 0 r = 1 := by simp [cellMode, cellFreq]

theorem cellMode_zero_right (n : ZMod M) : cellMode M n 0 = 1 := by simp [cellMode]

/-- `∑_r cos(2π n r/M) = 0` for `n ≠ 0`. -/
theorem sum_cellMode_right {n : ZMod M} (hn : n ≠ 0) : ∑ r, cellMode M n r = 0 := by
  simp only [cellMode_symm n]
  have := sum_cos_residues (M := M) (ZMod.valMinAbs n)
  simp only [ZMod.coe_valMinAbs, hn, ↓reduceIte] at this
  simpa [cellMode] using this

/-- `∑_n cos(2π n r/M) = M [r = 0]`. -/
theorem sum_cellMode_left (r : ZMod M) :
    ∑ n, cellMode M n r = if r = 0 then (M : ℝ) else 0 := by
  have := sum_cos_residues (M := M) (ZMod.valMinAbs r)
  simp only [ZMod.coe_valMinAbs] at this
  simpa [cellMode] using this

theorem cellNegLap_cellMode (n r : ZMod M) :
    cellNegLap (cellMode M n) r = cellEig M n * cellMode M n r := by
  unfold cellNegLap cellMode
  have h1 : Real.cos (cellFreq M n * (ZMod.valMinAbs (r + 1) : ℝ)) =
      Real.cos (cellFreq M n * (((ZMod.valMinAbs r + 1 : ℤ)) : ℝ)) :=
    cos_cellFreq_congr n (by push_cast; simp)
  have h2 : Real.cos (cellFreq M n * (ZMod.valMinAbs (r - 1) : ℝ)) =
      Real.cos (cellFreq M n * (((ZMod.valMinAbs r - 1 : ℤ)) : ℝ)) :=
    cos_cellFreq_congr n (by push_cast; simp)
  rw [h1, h2]
  have := cos_shift_add (cellFreq M n) (ZMod.valMinAbs r)
  unfold cellEig
  linear_combination (-1 : ℝ) * this

/-- The parabola `r(M − r)/2` on the representatives `0 ≤ r < M`. -/
noncomputable def cellParab (M : ℕ) [NeZero M] (r : ZMod M) : ℝ :=
  (r.val : ℝ) * ((M : ℝ) - r.val) / 2

theorem val_add_one (r : ZMod M) :
    (r + 1).val = if r.val + 1 < M then r.val + 1 else 0 := by
  have hM : 0 < M := Nat.pos_of_ne_zero (NeZero.ne M)
  have hv := ZMod.val_lt r
  have : r + 1 = ((r.val + 1 : ℕ) : ZMod M) := by simp
  rw [this, ZMod.val_natCast]
  split_ifs with h
  · exact Nat.mod_eq_of_lt h
  · have : r.val + 1 = M := by omega
    rw [this]; simp

theorem val_sub_one (r : ZMod M) :
    (r - 1).val = if r.val = 0 then M - 1 else r.val - 1 := by
  have hM : 0 < M := Nat.pos_of_ne_zero (NeZero.ne M)
  have hv := ZMod.val_lt r
  by_cases h0 : r.val = 0
  · have hr : r = 0 := (ZMod.val_eq_zero r).1 h0
    subst hr
    simp only [ZMod.val_zero, ↓reduceIte]
    have : (0 - 1 : ZMod M) = ((M - 1 : ℕ) : ZMod M) := by
      rw [Nat.cast_sub (by omega)]; simp
    rw [this, ZMod.val_natCast]
    exact Nat.mod_eq_of_lt (by omega)
  · simp only [h0, ↓reduceIte]
    have : r - 1 = ((r.val - 1 : ℕ) : ZMod M) := by
      rw [Nat.cast_sub (by omega)]; simp
    rw [this, ZMod.val_natCast]
    exact Nat.mod_eq_of_lt (by omega)

theorem cellNegLap_cellParab (r : ZMod M) :
    cellNegLap (cellParab M) r = 1 - (if r = 0 then (M : ℝ) else 0) := by
  have hM : 0 < M := Nat.pos_of_ne_zero (NeZero.ne M)
  have hv := ZMod.val_lt r
  unfold cellNegLap cellParab
  rw [val_add_one, val_sub_one]
  by_cases h0 : r.val = 0
  · have hr : r = 0 := (ZMod.val_eq_zero r).1 h0
    simp only [hr, ZMod.val_zero, ↓reduceIte]
    by_cases h1 : 0 + 1 < M
    · simp only [h1, ↓reduceIte]
      have : (M - 1 : ℕ) = M - 1 := rfl
      simp only [Nat.cast_sub (by omega : 1 ≤ M), Nat.cast_zero, Nat.cast_one, zero_add]
      ring
    · have hM1 : M = 1 := by omega
      subst hM1
      simp
  · have hr0 : r ≠ 0 := fun h => h0 (by simp [h])
    simp only [h0, hr0, ↓reduceIte]
    by_cases h1 : r.val + 1 < M
    · simp only [h1, ↓reduceIte]
      simp only [Nat.cast_sub (by omega : 1 ≤ r.val), Nat.cast_add, Nat.cast_one]
      ring
    · simp only [h1, ↓reduceIte]
      have : r.val + 1 = M := by omega
      simp only [Nat.cast_sub (by omega : 1 ≤ r.val), Nat.cast_zero]
      have h2 : (r.val : ℝ) = M - 1 := by
        have : (r.val : ℝ) + 1 = M := by exact_mod_cast this
        linarith
      rw [h2]; ring

theorem sum_range_sq_real (n : ℕ) :
    ∑ i ∈ Finset.range n, (i : ℝ) ^ 2 = ((n : ℝ) - 1) * n * (2 * n - 1) / 6 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]; push_cast; ring

theorem sum_range_id_real (n : ℕ) : ∑ i ∈ Finset.range n, (i : ℝ) = (n : ℝ) * (n - 1) / 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]; push_cast; ring

theorem sum_zmod_val (f : ℕ → ℝ) : ∑ r : ZMod M, f r.val = ∑ v ∈ Finset.range M, f v := by
  refine Finset.sum_bij (fun r _ => r.val) (fun r _ => Finset.mem_range.2 (ZMod.val_lt r))
    (fun a _ b _ h => ZMod.val_injective M h) (fun v hv => ?_) (fun r _ => rfl)
  exact ⟨(v : ZMod M), Finset.mem_univ _, by simp [ZMod.val_natCast, Nat.mod_eq_of_lt (Finset.mem_range.1 hv)]⟩

theorem sum_cellParab : ∑ r, cellParab M r = (M : ℝ) * ((M : ℝ) ^ 2 - 1) / 12 := by
  unfold cellParab
  rw [sum_zmod_val (fun v => (v : ℝ) * ((M : ℝ) - v) / 2)]
  have : ∑ v ∈ Finset.range M, (v : ℝ) * ((M : ℝ) - v) / 2 =
      ((M : ℝ) * ∑ v ∈ Finset.range M, (v : ℝ) - ∑ v ∈ Finset.range M, (v : ℝ) ^ 2) / 2 := by
    rw [← Finset.sum_div, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact congrArg (· / 2) (Finset.sum_congr rfl fun v _ => by ring)
  rw [this, sum_range_id_real, sum_range_sq_real]
  ring

/-- **The sum of the inverse eigenvalues**: `∑_{n ≠ 0} 1/(2 − 2 cos (2π n/M)) = (M² − 1)/12`. -/
theorem sum_inv_cellEig : ∑ n ∈ (Finset.univ : Finset (ZMod M)).erase 0, 1 / cellEig M n =
    ((M : ℝ) ^ 2 - 1) / 12 := by
  classical
  have hM : (M : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne M
  -- `∑_n ∑_r p(r) cos(n r) = M p(0) = 0`
  have h1 : ∑ n : ZMod M, ∑ r, cellParab M r * cellMode M n r = 0 := by
    rw [Finset.sum_comm]
    simp only [← Finset.mul_sum, sum_cellMode_left]
    simp [cellParab]
  -- the nonzero modes: `∑_r p(r) cos(n r) = −M/λ_n`
  have h2 : ∀ n ∈ (Finset.univ : Finset (ZMod M)).erase 0,
      ∑ r, cellParab M r * cellMode M n r = -(M : ℝ) / cellEig M n := by
    intro n hn
    have hn0 := (Finset.mem_erase.1 hn).1
    have hpos := cellEig_pos hn0
    have key := sum_mul_cellNegLap (cellMode M n) (cellParab M)
    simp only [cellNegLap_cellMode, cellNegLap_cellParab] at key
    have hL : ∑ r, cellMode M n r * (1 - if r = 0 then (M : ℝ) else 0) = -(M : ℝ) := by
      simp only [mul_sub, mul_one, Finset.sum_sub_distrib, sum_cellMode_right hn0]
      simp [cellMode_zero_right]
    rw [hL] at key
    rw [eq_div_iff hpos.ne']
    calc (∑ r, cellParab M r * cellMode M n r) * cellEig M n
        = ∑ r, cellParab M r * (cellEig M n * cellMode M n r) := by
          rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun r _ => by ring
      _ = -(M : ℝ) := key.symm
  have h3 : ∑ r, cellParab M r * cellMode M 0 r = (M : ℝ) * ((M : ℝ) ^ 2 - 1) / 12 := by
    simp only [cellMode_zero_left, mul_one, sum_cellParab]
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : ZMod M)), h3,
    Finset.sum_congr rfl h2] at h1
  have h4 : ∑ n ∈ (Finset.univ : Finset (ZMod M)).erase 0, -(M : ℝ) / cellEig M n =
      -(M : ℝ) * ∑ n ∈ (Finset.univ : Finset (ZMod M)).erase 0, 1 / cellEig M n := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun n _ => by ring
  rw [h4] at h1
  set T := ∑ n ∈ (Finset.univ : Finset (ZMod M)).erase 0, 1 / cellEig M n with hT
  have h5 : (M : ℝ) * (T - ((M : ℝ) ^ 2 - 1) / 12) = 0 := by linarith
  have h6 := (mul_eq_zero.1 h5).resolve_left hM
  linarith

/-- `∑_{n≠0} 1/x_n = τ/12` with `x_n = 2M²(1 − cos(2πn/M))` and `τ = 1 − M⁻²` (P4 (5.13)). -/
theorem sum_inv_latticeSymbol :
    ∑ n ∈ (Finset.univ : Finset (ZMod M)).erase 0, 1 / latticeSymbol M n = latticeTau M / 12 := by
  have hM : (M : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne M
  have : ∀ n : ZMod M, 1 / latticeSymbol M n = (1 / (M : ℝ) ^ 2) * (1 / cellEig M n) := fun n => by
    rw [latticeSymbol_eq_cellEig]; field_simp
  simp only [this, ← Finset.mul_sum, sum_inv_cellEig]
  unfold latticeTau
  field_simp

/-- The partial fractions `v c₁(v) = τ/12 − ∑ 1/(x_n + v)`. -/
theorem latticeSum_one_mul {v : ℝ} (hv : 0 < v) :
    v * latticeSum M v 1 = latticeTau M / 12 -
      ∑ n ∈ (Finset.univ : Finset (ZMod M)).erase 0, 1 / (latticeSymbol M n + v) := by
  rw [← sum_inv_latticeSymbol, ← Finset.sum_sub_distrib]
  unfold latticeSum
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun n hn => ?_
  have h0 : ZMod.valMinAbs n ≠ 0 := fun h => (Finset.mem_erase.1 hn).1 ((ZMod.valMinAbs_eq_zero n).1 h)
  have hx := latticeSymbol_ge n
  have hn0 : (0 : ℝ) < (ZMod.valMinAbs n : ℝ) ^ 2 := by positivity
  have h1 : latticeSymbol M n ≠ 0 := by linarith
  have h2 : latticeSymbol M n + v ≠ 0 := by linarith
  field_simp
  ring

/-- The partial fractions `v c₂(v) = c₁(v) − ∑ 1/(x_n + v)²`. -/
theorem latticeSum_two_mul {v : ℝ} (hv : 0 < v) :
    v * latticeSum M v 2 = latticeSum M v 1 -
      ∑ n ∈ (Finset.univ : Finset (ZMod M)).erase 0, 1 / (latticeSymbol M n + v) ^ 2 := by
  unfold latticeSum
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun n hn => ?_
  have h0 : ZMod.valMinAbs n ≠ 0 := fun h => (Finset.mem_erase.1 hn).1 ((ZMod.valMinAbs_eq_zero n).1 h)
  have hx := latticeSymbol_ge n
  have hn0 : (0 : ℝ) < (ZMod.valMinAbs n : ℝ) ^ 2 := by positivity
  have h1 : latticeSymbol M n ≠ 0 := by linarith
  have h2 : latticeSymbol M n + v ≠ 0 := by linarith
  field_simp
  ring

end Balaban.Flow
