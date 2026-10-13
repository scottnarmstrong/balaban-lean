/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.ScaleUniform
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The stopping index `k_f` of the ordinary block-spin steps

The papers (P4 section 6, P5 section 1, P7 section 4, P9 section 4.1) perform ordinary block-spin steps
`k → k+1` only while the running unit-lattice mass satisfies `ν_k ≤ (7/8) L⁻²`, and let `k_f` be
the first index with `ν_{k_f} > (7/8) L⁻²`.  For a running sequence `n` satisfying `RunningHyp`
this file defines `kStop` (the first index with `(7/8) L⁻² < n k`), proves that it exists, and proves:

* the characterization of `kStop` (`kStop_spec`, `kStop_min`, `kStop_eq_iff`), and its agreement
  with the older `sInf` definition `kF`;
* every ordinary step `k < kStop` has the mass premise of the step engine, with a strict margin
  (`massLe_of_lt_kStop`);
* the bounds at the stopping index: `n kStop ≤ (7/8) e^{2ε} < 1` when `kStop > 0`, and
  `n 0 ≤ ν e^ε` when `kStop = 0`;
* `kZero < kStop` for `β ≥ (8/7) L² e^{3ε}`, and a bound on the number of intermediate steps;
* the scale clause of the root `logPartition_multiscale` and the bounds of `C1Star` for
  `kStop` and `kStop + 1` (restated as plain inequalities; the frozen root is not imported);
* an explicit running sequence on which `kStop` and `kZero` are computed.

This file proves nothing about the last integral itself: the final cutoff, the massive covariance,
the final fluctuation integral, the large-field gas and the branch `k_f = 0` are open
(`notes/phase1/MASSIVE.md`, section 3).
-/

@[expose] public section

namespace Balaban.LargeField

open Balaban.Fluctuation Balaban.SmallField.Def6v2

namespace StopIndex

variable {d L : ℕ} {β ν a ε : ℝ} {b n : ℕ → ℝ}

/-! ### Numerics -/

theorem exp_le_inv_one_sub {x : ℝ} (h1 : x < 1) : Real.exp x ≤ 1 / (1 - x) := by
  have h := Real.add_one_le_exp (-x)
  rw [Real.exp_neg] at h
  have hx := Real.exp_pos x
  rw [le_div_iff₀ (by linarith)]
  calc Real.exp x * (1 - x) ≤ Real.exp x * (Real.exp x)⁻¹ :=
        mul_le_mul_of_nonneg_left (by linarith) hx.le
    _ = 1 := mul_inv_cancel₀ hx.ne'

theorem exp_eps_le {ε : ℝ} (h : ε ≤ 1 / 20) : Real.exp ε ≤ 20 / 19 :=
  (exp_le_inv_one_sub (by linarith)).trans ((div_le_iff₀ (by linarith)).2 (by linarith))

theorem exp_two_eps_le {ε : ℝ} (h : ε ≤ 1 / 20) : Real.exp (2 * ε) ≤ 10 / 9 :=
  (exp_le_inv_one_sub (by linarith)).trans ((div_le_iff₀ (by linarith)).2 (by linarith))

theorem exp_neg_eps_ge {ε : ℝ} (h : ε ≤ 1 / 20) : 19 / 20 ≤ Real.exp (-ε) := by
  have := Real.add_one_le_exp (-ε)
  linarith

theorem exp_mul_exp_neg (ε : ℝ) : Real.exp ε * Real.exp (-ε) = 1 := by
  rw [← Real.exp_add]; simp

theorem exp_two_eps_lt {ε : ℝ} (h : ε ≤ 1 / 20) : Real.exp (2 * ε) < 8 / 7 :=
  lt_of_le_of_lt (exp_two_eps_le h) (by norm_num)

/-! ### The running mass and the factor `δ_k` -/

theorem delta_bounds {δ : ℝ} (hδ : 0 < δ) (hl : |Real.log δ| ≤ ε) :
    Real.exp (-ε) ≤ δ ∧ δ ≤ Real.exp ε := by
  have h1 := abs_le.1 hl
  constructor
  · calc Real.exp (-ε) ≤ Real.exp (Real.log δ) := Real.exp_le_exp.2 h1.1
      _ = δ := Real.exp_log hδ
  · calc δ = Real.exp (Real.log δ) := (Real.exp_log hδ).symm
      _ ≤ _ := Real.exp_le_exp.2 h1.2

/-- Two-sided relation: `ν L^{2k} e^{-ε} ≤ n_k ≤ ν L^{2k} e^{ε}`. -/
theorem nu_two_sided (h : RunningHyp d L β ν a ε b n) (k : ℕ) :
    ν * (L : ℝ) ^ (2 * k) * Real.exp (-ε) ≤ n k ∧ n k ≤ ν * (L : ℝ) ^ (2 * k) * Real.exp ε := by
  obtain ⟨δ, hδ, hl, hn⟩ := h.nu_eq k
  obtain ⟨h1, h2⟩ := delta_bounds hδ hl
  have hc : 0 ≤ ν * (L : ℝ) ^ (2 * k) := by have := h.hν; positivity
  rw [hn]
  exact ⟨mul_le_mul_of_nonneg_left h1 hc, mul_le_mul_of_nonneg_left h2 hc⟩

theorem nL_pos (h : RunningHyp d L β ν a ε b n) : (0 : ℝ) < L := by
  exact_mod_cast (by have := h.hL; omega : 0 < L)

theorem n_pos (h : RunningHyp d L β ν a ε b n) (k : ℕ) : 0 < n k := by
  have := (nu_two_sided h k).1
  have hL := nL_pos h
  have hν := h.hν
  have : 0 < ν * (L : ℝ) ^ (2 * k) * Real.exp (-ε) := by positivity
  linarith

/-- One step of the running mass: `n_{k+1} ≤ L² e^{2ε} n_k`. -/
theorem n_succ_le (h : RunningHyp d L β ν a ε b n) (k : ℕ) :
    n (k + 1) ≤ (L : ℝ) ^ 2 * Real.exp (2 * ε) * n k := by
  have h1 := (nu_two_sided h (k + 1)).2
  have h2 := (nu_two_sided h k).1
  have he : Real.exp ε = Real.exp (2 * ε) * Real.exp (-ε) := by
    rw [← Real.exp_add]; congr 1; ring
  calc n (k + 1) ≤ ν * (L : ℝ) ^ (2 * (k + 1)) * Real.exp ε := h1
    _ = (L : ℝ) ^ 2 * Real.exp (2 * ε) * (ν * (L : ℝ) ^ (2 * k) * Real.exp (-ε)) := by
        rw [he, show 2 * (k + 1) = 2 * k + 2 by ring, pow_add]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left h2 (by positivity)

/-- Lower ratio: `n_{j+m} ≥ e^{-2ε} L^{2m} n_j`. -/
theorem n_add_ge (h : RunningHyp d L β ν a ε b n) (j m : ℕ) :
    Real.exp (-ε) * Real.exp (-ε) * (L : ℝ) ^ (2 * m) * n j ≤ n (j + m) := by
  have h1 := (nu_two_sided h (j + m)).1
  have h2 := (nu_two_sided h j).2
  have hq := Real.exp_pos (-ε)
  have hLm : (0 : ℝ) < (L : ℝ) ^ (2 * m) := pow_pos (nL_pos h) _
  have e1 := exp_mul_exp_neg ε
  have h3 : n j * Real.exp (-ε) ≤ ν * (L : ℝ) ^ (2 * j) := by
    calc n j * Real.exp (-ε) ≤ ν * (L : ℝ) ^ (2 * j) * Real.exp ε * Real.exp (-ε) :=
          mul_le_mul_of_nonneg_right h2 hq.le
      _ = ν * (L : ℝ) ^ (2 * j) := by linear_combination (ν * (L : ℝ) ^ (2 * j)) * e1
  calc Real.exp (-ε) * Real.exp (-ε) * (L : ℝ) ^ (2 * m) * n j
      = Real.exp (-ε) * (L : ℝ) ^ (2 * m) * (n j * Real.exp (-ε)) := by ring
    _ ≤ Real.exp (-ε) * (L : ℝ) ^ (2 * m) * (ν * (L : ℝ) ^ (2 * j)) :=
        mul_le_mul_of_nonneg_left h3 (by positivity)
    _ = ν * (L : ℝ) ^ (2 * (j + m)) * Real.exp (-ε) := by
        rw [show 2 * (j + m) = 2 * j + 2 * m by ring, pow_add]; ring
    _ ≤ _ := h1

/-! ### T1: existence and definition -/

/-- The running mass eventually exceeds `(7/8) L⁻²`. -/
theorem exists_gt (h : RunningHyp d L β ν a ε b n) :
    ∃ k, 7 / 8 * ((L : ℝ) ^ 2)⁻¹ < n k := by
  have hL := nL_pos h
  have hν := h.hν
  have hq := Real.exp_pos (-ε)
  have hL1 : (1 : ℝ) < (L : ℝ) ^ 2 := by
    have : (2 : ℝ) ≤ L := by exact_mod_cast h.hL
    nlinarith
  obtain ⟨m, hm⟩ := pow_unbounded_of_one_lt (1 / (ν * Real.exp (-ε))) hL1
  refine ⟨m, ?_⟩
  have hpos : 0 < ν * Real.exp (-ε) := by positivity
  rw [div_lt_iff₀ hpos] at hm
  have h1 := (nu_two_sided h m).1
  have h2 : ν * (L : ℝ) ^ (2 * m) * Real.exp (-ε) = ((L : ℝ) ^ 2) ^ m * (ν * Real.exp (-ε)) := by
    rw [pow_mul]; ring
  have h3 : ((L : ℝ) ^ 2)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hL1.le
  have : 0 < ((L : ℝ) ^ 2)⁻¹ := by positivity
  linarith

open scoped Classical in
/-- **The stopping index `k_f`.**  The first index `k` with `(7/8) L⁻² < n k`, where `n` is the
running unit-lattice mass of `RunningHyp`; it exists by `exists_gt`. -/
noncomputable def kStop (h : RunningHyp d L β ν a ε b n) : ℕ := Nat.find (exists_gt h)

theorem kStop_spec (h : RunningHyp d L β ν a ε b n) :
    7 / 8 * ((L : ℝ) ^ 2)⁻¹ < n (kStop h) := by
  classical
  unfold kStop
  exact Nat.find_spec (exists_gt h)

theorem kStop_min (h : RunningHyp d L β ν a ε b n) {k : ℕ} (hk : k < kStop h) :
    n k ≤ 7 / 8 * ((L : ℝ) ^ 2)⁻¹ := by
  classical
  unfold kStop at hk
  exact not_lt.1 (Nat.find_min (exists_gt h) hk)

theorem kStop_le (h : RunningHyp d L β ν a ε b n) {k : ℕ} (hk : 7 / 8 * ((L : ℝ) ^ 2)⁻¹ < n k) :
    kStop h ≤ k := by
  classical
  unfold kStop
  exact Nat.find_min' (exists_gt h) hk

/-- Uniqueness: `kStop` is the unique index that is above the threshold and preceded only by
indices at or below it. -/
theorem kStop_eq_iff (h : RunningHyp d L β ν a ε b n) {k : ℕ} :
    kStop h = k ↔ 7 / 8 * ((L : ℝ) ^ 2)⁻¹ < n k ∧ ∀ j < k, n j ≤ 7 / 8 * ((L : ℝ) ^ 2)⁻¹ := by
  constructor
  · rintro rfl
    exact ⟨kStop_spec h, fun j hj => kStop_min h hj⟩
  · rintro ⟨h1, h2⟩
    refine le_antisymm (kStop_le h h1) ?_
    by_contra hlt
    exact absurd (kStop_spec h) (not_lt.2 (h2 _ (not_le.1 hlt)))

/-- `kStop` is the landed `sInf` index `kF`. -/
theorem kStop_eq_kF (h : RunningHyp d L β ν a ε b n) : kStop h = kF L n := by
  have hne : {k : ℕ | 7 / 8 * ((L : ℝ) ^ 2)⁻¹ < n k}.Nonempty := exists_gt h
  refine le_antisymm (kStop_le h (Nat.sInf_mem hne)) (Nat.sInf_le (kStop_spec h))

/-! ### T2: every ordinary step has the mass premise -/

theorem nu_le_of_lt_kStop (h : RunningHyp d L β ν a ε b n) {k : ℕ} (hk : k < kStop h) :
    n k ≤ 7 / 8 * ((L : ℝ) ^ 2)⁻¹ ∧ 7 / 8 * ((L : ℝ) ^ 2)⁻¹ < ((L : ℝ) ^ 2)⁻¹ := by
  have hL := nL_pos h
  have : 0 < ((L : ℝ) ^ 2)⁻¹ := by positivity
  exact ⟨kStop_min h hk, by linarith⟩

/-- **Every ordinary step has the mass premise.**  For `k < kStop`, the mass premise of the step
engine, `ν (L^{k+1})² ≤ 1` for the physical mass of `n k`, holds. -/
theorem massLe_of_lt_kStop [NeZero L] (h : RunningHyp d L β ν a ε b n) {k : ℕ}
    (hk : k < kStop h) : sfBgMassAt L k (n k) * ((L : ℝ) ^ (k + 1)) ^ 2 ≤ 1 := by
  have := nu_le_of_lt_kStop h hk
  exact (massLe_iff k (n k)).2 (by linarith [this.1, this.2])

/-! ### T3: the mass at the stopping index -/

/-- For `kStop > 0`: `n kStop ≤ (7/8) e^{2ε}`. -/
theorem n_kStop_le (h : RunningHyp d L β ν a ε b n) (hpos : 0 < kStop h) :
    n (kStop h) ≤ 7 / 8 * Real.exp (2 * ε) := by
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hpos.ne'
  have hm := kStop_min h (show k < kStop h by omega)
  have hL := nL_pos h
  have hcancel : (L : ℝ) ^ 2 * ((L : ℝ) ^ 2)⁻¹ = 1 := mul_inv_cancel₀ (by positivity)
  rw [hk]
  calc n (k + 1) ≤ (L : ℝ) ^ 2 * Real.exp (2 * ε) * n k := n_succ_le h k
    _ ≤ (L : ℝ) ^ 2 * Real.exp (2 * ε) * (7 / 8 * ((L : ℝ) ^ 2)⁻¹) :=
        mul_le_mul_of_nonneg_left hm (by positivity)
    _ = 7 / 8 * Real.exp (2 * ε) * ((L : ℝ) ^ 2 * ((L : ℝ) ^ 2)⁻¹) := by ring
    _ = _ := by rw [hcancel]; ring

/-- For `kStop > 0`, under the smallness `e^{2ε} < 8/7`, `n kStop < 1`. -/
theorem n_kStop_lt_one_of_exp (h : RunningHyp d L β ν a ε b n) (hpos : 0 < kStop h)
    (hε : Real.exp (2 * ε) < 8 / 7) : n (kStop h) < 1 := by
  have := n_kStop_le h hpos
  linarith

/-- For `kStop > 0`, `n kStop < 1`; the smallness `e^{2ε} < 8/7` follows from `ε ≤ 1/20`. -/
theorem n_kStop_lt_one (h : RunningHyp d L β ν a ε b n) (hpos : 0 < kStop h) :
    n (kStop h) < 1 :=
  n_kStop_lt_one_of_exp h hpos (exp_two_eps_lt h.hε)

/-- The branch `kStop = 0`: `n 0 ≤ ν e^ε`. -/
theorem n_zero_le (h : RunningHyp d L β ν a ε b n) : n 0 ≤ ν * Real.exp ε := by
  simpa using (nu_two_sided h 0).2

/-- The branch `kStop = 0`: `n 0 < 1` provided `ν e^ε < 1`.  (From `ν ≤ 1` alone only
`n 0 ≤ e^ε ≤ 20/19` follows.) -/
theorem n_zero_lt_one (h : RunningHyp d L β ν a ε b n) (hν : ν * Real.exp ε < 1) : n 0 < 1 :=
  lt_of_le_of_lt (n_zero_le h) hν

/-! ### T4: relation to `k₀` -/

theorem n_le_exp_div_of_le_kZero (h : RunningHyp d L β ν a ε b n) (hg : KZeroGenuine β ν)
    {k : ℕ} (hk : k ≤ kZero d L β ν) : n k ≤ Real.exp (3 * ε) / β := by
  have hL := nL_pos h
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast (by have := h.hL; omega : 1 ≤ L)
  have hβ := h.hβ
  obtain ⟨γ, hγ, hlγ, hb⟩ := h.beta_eq k
  have hn0 := n_pos h k
  have hγe := (delta_bounds hγ hlγ).1
  have hbk : β * Real.exp (-ε) ≤ b k := by
    rw [hb]
    have h1 : (1 : ℝ) ≤ (L : ℝ) ^ (k * (d - 2)) := one_le_pow₀ hL1
    calc β * Real.exp (-ε) = β * 1 * Real.exp (-ε) := by ring
      _ ≤ β * (L : ℝ) ^ (k * (d - 2)) * γ :=
        mul_le_mul (mul_le_mul_of_nonneg_left h1 hβ.le) hγe (Real.exp_pos _).le (by positivity)
  have h2 : β * Real.exp (-ε) * n k ≤ Real.exp (2 * ε) :=
    (mul_le_mul_of_nonneg_right hbk hn0.le).trans (h.beta_mul_nu_le hg hk)
  have e1 := exp_mul_exp_neg ε
  have e2 : Real.exp ε * Real.exp (2 * ε) = Real.exp (3 * ε) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [le_div_iff₀ hβ]
  calc n k * β = Real.exp ε * (β * Real.exp (-ε) * n k) := by
        linear_combination (-(n k * β)) * e1
    _ ≤ Real.exp ε * Real.exp (2 * ε) := mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le
    _ = _ := e2

/-- For `β ≥ (8/7) L² e^{3ε}` every `k ≤ k₀` has `n k ≤ (7/8) L⁻²`. -/
theorem n_le_of_le_kZero (h : RunningHyp d L β ν a ε b n) (hg : KZeroGenuine β ν)
    (hβ : 8 / 7 * (L : ℝ) ^ 2 * Real.exp (3 * ε) ≤ β) {k : ℕ} (hk : k ≤ kZero d L β ν) :
    n k ≤ 7 / 8 * ((L : ℝ) ^ 2)⁻¹ := by
  have hL := nL_pos h
  have hβ0 := h.hβ
  refine (n_le_exp_div_of_le_kZero h hg hk).trans ?_
  rw [div_le_iff₀ hβ0]
  calc Real.exp (3 * ε) = 7 / 8 * ((L : ℝ) ^ 2)⁻¹ * (8 / 7 * (L : ℝ) ^ 2 * Real.exp (3 * ε)) := by
        field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left hβ (by positivity)

/-- **`k₀ < k_f`** for `β ≥ (8/7) L² e^{3ε}`. -/
theorem kZero_lt_kStop (h : RunningHyp d L β ν a ε b n) (hg : KZeroGenuine β ν)
    (hβ : 8 / 7 * (L : ℝ) ^ 2 * Real.exp (3 * ε) ≤ β) : kZero d L β ν < kStop h := by
  by_contra hle
  have := n_le_of_le_kZero h hg hβ (not_lt.1 hle)
  exact absurd (kStop_spec h) (not_lt.2 this)

/-- **Number of intermediate steps.**  If `m` satisfies `(7/8) e^{4ε} β_{k₀+1} ≤ L^{2m+2}` then
`k_f ≤ k₀ + 1 + m`; hence `k_f - k₀ - 1` is at most about `(log β_{k₀+1}) / (2 log L)`. -/
theorem kStop_le_kZero_add (h : RunningHyp d L β ν a ε b n) (m : ℕ)
    (hm : 7 / 8 * Real.exp (4 * ε) * b (kZero d L β ν + 1) ≤ (L : ℝ) ^ (2 * m + 2)) :
    kStop h ≤ kZero d L β ν + 1 + m := by
  apply kStop_le
  by_contra hnot
  rw [not_lt] at hnot
  set j := kZero d L β ν + 1 with hj
  have hL := nL_pos h
  have hbj := h.betaRun_pos j
  have hlow := h.lt_beta_mul_nu (j := j) (by omega)
  have hnj := n_pos h j
  have hq := Real.exp_pos (-ε)
  have h1 := n_add_ge h j m
  have hLm : (0 : ℝ) < (L : ℝ) ^ (2 * m) := pow_pos hL _
  have hq4 : Real.exp (4 * ε) * (Real.exp (-ε) * Real.exp (-ε) * Real.exp (-ε) * Real.exp (-ε)) = 1 := by
    rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    simp; ring_nf
  have hq2 : Real.exp (-(2 * ε)) = Real.exp (-ε) * Real.exp (-ε) := by
    rw [← Real.exp_add]; congr 1; ring
  have hL2 : (L : ℝ) ^ (2 * m + 2) = (L : ℝ) ^ (2 * m) * (L : ℝ) ^ 2 := pow_add _ _ _
  have hcancel : (L : ℝ) ^ 2 * ((L : ℝ) ^ 2)⁻¹ = 1 := mul_inv_cancel₀ (by positivity)
  -- b j * n (j+m) ≥ q^2 L^{2m} (b j n j) > q^4 L^{2m}
  have h4 : Real.exp (-ε) * Real.exp (-ε) * (L : ℝ) ^ (2 * m) *
      (Real.exp (-ε) * Real.exp (-ε)) < b j * n (j + m) := by
    have := mul_le_mul_of_nonneg_left h1 hbj.le
    have h5 : Real.exp (-ε) * Real.exp (-ε) * (L : ℝ) ^ (2 * m) * (Real.exp (-ε) * Real.exp (-ε))
        < Real.exp (-ε) * Real.exp (-ε) * (L : ℝ) ^ (2 * m) * (b j * n j) :=
      mul_lt_mul_of_pos_left (by rw [← hq2]; exact hlow) (by positivity)
    nlinarith
  have h6 : b j * n (j + m) ≤ b j * (7 / 8 * ((L : ℝ) ^ 2)⁻¹) :=
    mul_le_mul_of_nonneg_left hnot hbj.le
  have h7 : 7 / 8 * b j ≤ Real.exp (-ε) * Real.exp (-ε) * Real.exp (-ε) * Real.exp (-ε) *
      ((L : ℝ) ^ (2 * m) * (L : ℝ) ^ 2) := by
    rw [← hL2]
    calc 7 / 8 * b j = Real.exp (-ε) * Real.exp (-ε) * Real.exp (-ε) * Real.exp (-ε) *
          (Real.exp (4 * ε) * (7 / 8 * b j)) := by linear_combination (-(7 / 8 * b j)) * hq4
      _ ≤ _ := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          linarith
  have h8 : b j * (7 / 8 * ((L : ℝ) ^ 2)⁻¹) ≤ Real.exp (-ε) * Real.exp (-ε) * (L : ℝ) ^ (2 * m) *
      (Real.exp (-ε) * Real.exp (-ε)) := by
    calc b j * (7 / 8 * ((L : ℝ) ^ 2)⁻¹) = (7 / 8 * b j) * ((L : ℝ) ^ 2)⁻¹ := by ring
      _ ≤ (Real.exp (-ε) * Real.exp (-ε) * Real.exp (-ε) * Real.exp (-ε) *
          ((L : ℝ) ^ (2 * m) * (L : ℝ) ^ 2)) * ((L : ℝ) ^ 2)⁻¹ :=
          mul_le_mul_of_nonneg_right h7 (by positivity)
      _ = Real.exp (-ε) * Real.exp (-ε) * (L : ℝ) ^ (2 * m) * (Real.exp (-ε) * Real.exp (-ε)) *
          ((L : ℝ) ^ 2 * ((L : ℝ) ^ 2)⁻¹) := by ring
      _ = _ := by rw [hcancel]; ring
  linarith

/-! ### T5: the scale clause of Root-F and the bounds of `C1Star` -/

theorem sq_bounds (h : RunningHyp d L β ν a ε b n) (hν1 : ν ≤ 1) :
    ν * (L : ℝ) ^ (2 * kStop h) ≤ (L : ℝ) ^ 2 ∧ 1 / 4 ≤ ν * (L : ℝ) ^ (2 * kStop h + 2) := by
  have hL := nL_pos h
  have hν := h.hν
  have hL2 : (2 : ℝ) ≤ L := by exact_mod_cast h.hL
  have hε := h.hε
  have hq := Real.exp_pos (-ε)
  have e1 := exp_mul_exp_neg ε
  have hlo := (nu_two_sided h (kStop h)).1
  have hup := (nu_two_sided h (kStop h)).2
  have hsp := kStop_spec h
  have hcancel : (L : ℝ) ^ 2 * ((L : ℝ) ^ 2)⁻¹ = 1 := mul_inv_cancel₀ (by positivity)
  have hLsq : (4 : ℝ) ≤ (L : ℝ) ^ 2 := by nlinarith
  constructor
  · rcases Nat.eq_zero_or_pos (kStop h) with h0 | hpos
    · rw [h0]; simp; linarith
    · have hn := n_kStop_lt_one h hpos
      have heq : ν * (L : ℝ) ^ (2 * kStop h) =
          ν * (L : ℝ) ^ (2 * kStop h) * Real.exp (-ε) * Real.exp ε := by
        linear_combination (-(ν * (L : ℝ) ^ (2 * kStop h))) * e1
      have hee := exp_eps_le hε
      have hpos' : 0 ≤ ν * (L : ℝ) ^ (2 * kStop h) * Real.exp (-ε) := by positivity
      rw [heq]
      calc ν * (L : ℝ) ^ (2 * kStop h) * Real.exp (-ε) * Real.exp ε ≤ 1 * (20 / 19) :=
            mul_le_mul (by linarith) hee (Real.exp_pos _).le (by norm_num)
        _ ≤ _ := by linarith
  · have h1 : 7 / 8 * ((L : ℝ) ^ 2)⁻¹ < ν * (L : ℝ) ^ (2 * kStop h) * Real.exp ε :=
      lt_of_lt_of_le hsp hup
    have h2 := mul_lt_mul_of_pos_right h1 (mul_pos (pow_pos hL 2) hq)
    have h3 : 7 / 8 * ((L : ℝ) ^ 2)⁻¹ * ((L : ℝ) ^ 2 * Real.exp (-ε)) = 7 / 8 * Real.exp (-ε) := by
      linear_combination (7 / 8 * Real.exp (-ε)) * hcancel
    have h4 : ν * (L : ℝ) ^ (2 * kStop h) * Real.exp ε * ((L : ℝ) ^ 2 * Real.exp (-ε)) =
        ν * (L : ℝ) ^ (2 * kStop h + 2) := by
      rw [pow_add]; linear_combination (ν * (L : ℝ) ^ (2 * kStop h) * (L : ℝ) ^ 2) * e1
    have := exp_neg_eps_ge hε
    linarith

/-- **Scale clause of Root-F** (restated; the frozen root is not imported): for `ν ≤ 1`, the index
`kStop` satisfies `L^{k_f} √ν ≤ L` and `1/2 ≤ L^{k_f+1} √ν`. -/
theorem kStop_rootF_scale (h : RunningHyp d L β ν a ε b n) (hν1 : ν ≤ 1) :
    (L : ℝ) ^ kStop h * Real.sqrt ν ≤ L ∧ 1 / 2 ≤ (L : ℝ) ^ (kStop h + 1) * Real.sqrt ν := by
  obtain ⟨hA, hB⟩ := sq_bounds h hν1
  have hL := nL_pos h
  have hν := h.hν
  have hs : 0 ≤ Real.sqrt ν := Real.sqrt_nonneg _
  have hsq : Real.sqrt ν ^ 2 = ν := Real.sq_sqrt hν.le
  constructor
  · rw [← pow_le_pow_iff_left₀ (by positivity) hL.le (two_ne_zero)]
    calc ((L : ℝ) ^ kStop h * Real.sqrt ν) ^ 2 = ν * (L : ℝ) ^ (2 * kStop h) := by
          rw [mul_pow, hsq, pow_mul']; ring
      _ ≤ _ := hA
  · rw [← pow_le_pow_iff_left₀ (by norm_num) (by positivity) (two_ne_zero)]
    calc ((1 : ℝ) / 2) ^ 2 = 1 / 4 := by norm_num
      _ ≤ ν * (L : ℝ) ^ (2 * kStop h + 2) := hB
      _ = ((L : ℝ) ^ (kStop h + 1) * Real.sqrt ν) ^ 2 := by
          rw [mul_pow, hsq, ← pow_mul, show (kStop h + 1) * 2 = 2 * kStop h + 2 by ring]; ring

/-- The bounds of `C1Star` for `J = kStop + 1`: `1/2 ≤ L^J √ν ≤ L²`. -/
theorem kStop_succ_C1Star (h : RunningHyp d L β ν a ε b n) (hν1 : ν ≤ 1) :
    1 / 2 ≤ (L : ℝ) ^ (kStop h + 1) * Real.sqrt ν ∧
      (L : ℝ) ^ (kStop h + 1) * Real.sqrt ν ≤ (L : ℝ) ^ 2 := by
  obtain ⟨h1, h2⟩ := kStop_rootF_scale h hν1
  have hL := nL_pos h
  refine ⟨h2, ?_⟩
  calc (L : ℝ) ^ (kStop h + 1) * Real.sqrt ν = L * ((L : ℝ) ^ kStop h * Real.sqrt ν) := by ring
    _ ≤ L * L := mul_le_mul_of_nonneg_left h1 hL.le
    _ = _ := by ring

/-! ### T6: an explicit running sequence -/

theorem witness_gt_iff (hL : 2 ≤ L) (d k : ℕ) :
    7 / 8 * ((L : ℝ) ^ 2)⁻¹ < 1 / ((L : ℝ) ^ 2 * (L : ℝ) ^ d) * (L : ℝ) ^ (2 * k) * 1 ↔
      d ≤ 2 * k := by
  have hL0 : (0 : ℝ) < L := by exact_mod_cast (by omega : 0 < L)
  have hL2 : (2 : ℝ) ≤ L := by exact_mod_cast hL
  have hd : (0 : ℝ) < (L : ℝ) ^ d := by positivity
  have hpos : (0 : ℝ) < (L : ℝ) ^ 2 * (L : ℝ) ^ d := by positivity
  rw [show 1 / ((L : ℝ) ^ 2 * (L : ℝ) ^ d) * (L : ℝ) ^ (2 * k) * 1 =
    (L : ℝ) ^ (2 * k) / ((L : ℝ) ^ 2 * (L : ℝ) ^ d) by ring, lt_div_iff₀ hpos]
  have e : 7 / 8 * ((L : ℝ) ^ 2)⁻¹ * ((L : ℝ) ^ 2 * (L : ℝ) ^ d) = 7 / 8 * (L : ℝ) ^ d := by
    field_simp
  rw [e]
  constructor
  · intro hlt
    by_contra hc
    have h1 : (L : ℝ) ^ (2 * k + 1) ≤ (L : ℝ) ^ d :=
      pow_le_pow_right₀ (by linarith) (by omega)
    rw [pow_succ] at h1
    have : (0 : ℝ) < (L : ℝ) ^ (2 * k) := by positivity
    nlinarith
  · intro hd2
    have h1 : (L : ℝ) ^ d ≤ (L : ℝ) ^ (2 * k) := pow_le_pow_right₀ (by linarith) hd2
    linarith

/-- **The witness.**  For `d ≥ 2`, `L ≥ 2`, `ε = 0`, `β = L²`, `ν = 1/(β L^d)`, `n k = ν L^{2k}`:
`k₀ = 1`, `k_f = ⌊(d+1)/2⌋` (the least `k` with `d ≤ 2k`), so `k₀ < k_f` iff `d ≥ 3`; the step
`k = 0 < k_f` has the mass premise; and `n k_f < 1`. -/
theorem witness_kStop (hd : 2 ≤ d) (hL : 2 ≤ L) [NeZero L] :
    ∃ (β ν : ℝ) (b n : ℕ → ℝ) (h : RunningHyp d L β ν (5 / 4) 0 b n), KZeroGenuine β ν ∧
      kZero d L β ν = 1 ∧ kStop h = (d + 1) / 2 ∧ 0 < kStop h ∧
      (3 ≤ d → kZero d L β ν < kStop h) ∧
      sfBgMassAt L 0 (n 0) * ((L : ℝ) ^ (0 + 1)) ^ 2 ≤ 1 ∧
      n (kStop h) = ν * (L : ℝ) ^ (2 * ((d + 1) / 2)) ∧ n (kStop h) < 1 := by
  have hL0 : (0 : ℝ) < L := by exact_mod_cast (by omega : 0 < L)
  have hL1 : (1 : ℝ) < L := by exact_mod_cast (by omega : 1 < L)
  set β : ℝ := (L : ℝ) ^ 2 with hβdef
  have hβ : 0 < β := by positivity
  set ν : ℝ := 1 / (β * (L : ℝ) ^ d) with hνdef
  have hν : 0 < ν := by positivity
  have h : RunningHyp d L β ν (5 / 4) 0 (fun k => β * (L : ℝ) ^ (k * (d - 2)) * 1)
      (fun k => ν * (L : ℝ) ^ (2 * k) * 1) :=
    { hd := hd, hL := hL, hβ := hβ, hν := hν, ha1 := by norm_num, ha2 := by norm_num
      hε0 := le_rfl, hε := by norm_num
      beta_eq := fun k => ⟨1, one_pos, by simp, rfl⟩
      nu_eq := fun k => ⟨1, one_pos, by simp, rfl⟩ }
  have hβν : β * ν = 1 / (L : ℝ) ^ d := by rw [hνdef]; field_simp
  have hg : KZeroGenuine β ν := by
    unfold KZeroGenuine
    rw [hβν, div_le_one (by positivity)]
    exact one_le_pow₀ hL1.le
  have hk1 : 1 ≤ kZero d L β ν := by
    unfold kZero
    refine le_csSup (kZero_bddAbove (by omega) hL (mul_pos hβ hν)) ?_
    show β * ν * (L : ℝ) ^ (1 * d) ≤ 1
    rw [hβν, one_mul]
    have : (0 : ℝ) < (L : ℝ) ^ d := by positivity
    rw [one_div, inv_mul_cancel₀ this.ne']
  have hk2 : kZero d L β ν ≤ 1 := by
    have hs := kZero_spec (d := d) (L := L) (by omega) hL (mul_pos hβ hν) hg
    rw [hβν] at hs
    have hdp : (0 : ℝ) < (L : ℝ) ^ d := by positivity
    rw [one_div, inv_mul_le_iff₀ hdp, mul_one] at hs
    have h5 : kZero d L β ν * d ≤ d := (pow_le_pow_iff_right₀ hL1).1 hs
    by_contra hc
    nlinarith [Nat.mul_le_mul_right d (show 2 ≤ kZero d L β ν by omega)]
  have hkz : kZero d L β ν = 1 := le_antisymm hk2 hk1
  have hks : kStop h = (d + 1) / 2 := by
    rw [kStop_eq_iff]
    refine ⟨(witness_gt_iff hL d _).2 (by omega), fun j hj => ?_⟩
    have := mt (witness_gt_iff hL d j).1 (by omega)
    exact not_lt.1 this
  have hpos : 0 < kStop h := by rw [hks]; omega
  refine ⟨β, ν, _, _, h, hg, hkz, hks, hpos, fun h3 => by rw [hkz, hks]; omega, ?_, ?_,
    n_kStop_lt_one h hpos⟩
  · exact massLe_of_lt_kStop h hpos
  · show ν * (L : ℝ) ^ (2 * kStop h) * 1 = _
    rw [hks, mul_one]

end StopIndex

end Balaban.LargeField
