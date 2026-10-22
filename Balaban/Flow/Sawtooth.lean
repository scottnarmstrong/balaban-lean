/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Flow.TorusLift
public import Balaban.Green.BallSums

/-!
# The sawtooth periodization of a cell polynomial on the circle of `N m` sites

On `ZMod ℓ`, `ℓ = N m`, `m` blocks of `N` sites, a cell polynomial `polyZ F₂ F₁ F₀` of the integer
`slift s = N * (signed block index of s) + (position of s in its block)` (the signed block index is
`ZMod.valMinAbs` of the block coordinate) is a function `saw F s` on the circle.  Away from the two
seam sites (where the signed lift jumps by `ℓ`), `hamil1` acts on it as `HZ` acts on `polyZ`
(`hamil1_saw`), so `saw F` solves the cell-polynomial equation up to a defect supported at the seam.
-/

@[expose] public section

namespace Balaban.Flow

open Finset Balaban

variable {ℓ N m : ℕ} [NeZero ℓ] [NeZero N] [NeZero m]

/-- The signed block index of `s`. -/
def sb (N m : ℕ) (s : ZMod ℓ) : ℤ := ZMod.valMinAbs (blockCoord N m s)

/-- The position of `s` in its block. -/
def sc (N : ℕ) (s : ZMod ℓ) : ℕ := s.val % N

/-- The signed lift of `s` to `ℤ`. -/
def slift (N m : ℕ) (s : ZMod ℓ) : ℤ := (N : ℤ) * sb N m s + (sc N s : ℤ)

/-- The sawtooth function of the cell polynomial `(F₂, F₁, F₀)`. -/
noncomputable def saw (N m : ℕ) (F₂ F₁ F₀ : ZMod N → ℂ) (s : ZMod ℓ) : ℂ :=
  polyZ F₂ F₁ F₀ (slift N m s)

omit [NeZero ℓ] [NeZero m] in
theorem slift_ediv (s : ZMod ℓ) : slift N m s / N = sb N m s := by
  have hN : (0 : ℤ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have : (sc N s : ℤ) < N := by
    unfold sc; exact_mod_cast Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne N))
  unfold slift
  rw [Int.mul_add_ediv_left _ _ hN.ne', Int.ediv_eq_zero_of_lt (by positivity) this, add_zero]

/-- The `j`-th site of the block with coordinate `c`. -/
def blockSite (N : ℕ) (c : ZMod m) (j : ℕ) : ZMod ℓ := ((c.val * N + j : ℕ) : ZMod ℓ)

omit [NeZero ℓ] [NeZero N] in
theorem blockSite_val (hℓ : ℓ = N * m) (c : ZMod m) {j : ℕ} (hj : j < N) :
    (blockSite (ℓ := ℓ) N c j).val = c.val * N + j := by
  unfold blockSite
  apply ZMod.val_natCast_of_lt
  have h1 : c.val + 1 ≤ m := ZMod.val_lt c
  rw [hℓ]
  nlinarith

omit [NeZero ℓ] in
theorem blockCoord_blockSite (hℓ : ℓ = N * m) (c : ZMod m) {j : ℕ} (hj : j < N) :
    blockCoord N m (blockSite (ℓ := ℓ) N c j) = c := by
  unfold blockCoord
  rw [blockSite_val hℓ c hj]
  have hN : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have : (c.val * N + j) / N = c.val := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hN, Nat.div_eq_of_lt hj, zero_add]
  rw [this]; simp

theorem sum_fibre1 (hℓ : ℓ = N * m) (c : ZMod m) (g : ZMod ℓ → ℂ) :
    ∑ s ∈ fibre1 (ℓ := ℓ) N m c, g s = ∑ j : Fin N, g (blockSite (ℓ := ℓ) N c j) := by
  have hN : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have himg : fibre1 (ℓ := ℓ) N m c =
      Finset.univ.image (fun j : Fin N => blockSite (ℓ := ℓ) N c j) := by
    ext s
    simp only [fibre1, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro hs
      have hv : s.val / N = c.val := by rw [← blockCoord_val hℓ, hs]
      refine ⟨⟨s.val % N, Nat.mod_lt _ hN⟩, ?_⟩
      apply ZMod.val_injective
      rw [blockSite_val hℓ c (Nat.mod_lt _ hN)]
      have := Nat.div_add_mod s.val N
      rw [hv] at this
      rw [Nat.mul_comm]; exact this
    · rintro ⟨j, rfl⟩
      exact blockCoord_blockSite hℓ c j.2
  rw [himg, Finset.sum_image]
  intro j _ j' _ h
  have h1 := congrArg ZMod.val h
  rw [blockSite_val hℓ c j.2, blockSite_val hℓ c j'.2] at h1
  exact Fin.ext (by omega)

omit [NeZero ℓ] in
theorem slift_blockSite (hℓ : ℓ = N * m) (c : ZMod m) {j : ℕ} (hj : j < N) :
    slift N m (blockSite (ℓ := ℓ) N c j) = (N : ℤ) * ZMod.valMinAbs c + j := by
  unfold slift sb sc
  rw [blockCoord_blockSite hℓ c hj, blockSite_val hℓ c hj]
  have hN : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have : (c.val * N + j) % N = j := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hj]
  rw [this]

theorem blockavg_saw (hℓ : ℓ = N * m) (F₂ F₁ F₀ : ZMod N → ℂ) (s : ZMod ℓ) :
    (1 / (N : ℂ)) * ∑ s' ∈ fibre1 (ℓ := ℓ) N m (blockCoord N m s), saw N m F₂ F₁ F₀ s' =
      blockAvgZ N (polyZ F₂ F₁ F₀) (slift N m s) := by
  unfold blockAvgZ
  rw [sum_fibre1 hℓ, slift_ediv]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  unfold saw
  rw [slift_blockSite hℓ _ j.2]
  rfl

theorem val_succ (s : ZMod ℓ) : (s + 1).val = (s.val + 1) % ℓ := by
  have : s + 1 = ((s.val + 1 : ℕ) : ZMod ℓ) := by push_cast; simp
  rw [this, ZMod.val_natCast]

omit [NeZero N] [NeZero m] in
theorem blockCoord_succ (hℓ : ℓ = N * m) (s : ZMod ℓ) :
    blockCoord N m (s + 1) = (((s.val + 1) / N : ℕ) : ZMod m) := by
  unfold blockCoord
  have h1 : (s.val + 1) % ℓ / N = (s.val + 1) / N % m := by
    have := Nat.mod_mul_right_div_self (s.val + 1) N m
    rw [← hℓ] at this; exact this
  rw [val_succ, h1, ZMod.natCast_mod]

omit [NeZero N] [NeZero m] in
theorem sc_succ (hℓ : ℓ = N * m) (s : ZMod ℓ) : sc N (s + 1) = (s.val + 1) % N := by
  unfold sc
  have hdv : N ∣ ℓ := ⟨m, hℓ⟩
  rw [val_succ]
  exact Nat.mod_mod_of_dvd _ hdv

omit [NeZero N] [NeZero m] in
theorem sb_succ (hℓ : ℓ = N * m) (s : ZMod ℓ) :
    sb N m (s + 1) = ZMod.valMinAbs (((s.val + 1) / N : ℕ) : ZMod m) := by
  unfold sb; rw [blockCoord_succ hℓ]

omit [NeZero ℓ] [NeZero N] [NeZero m] in
theorem sb_def (s : ZMod ℓ) : sb N m s = ZMod.valMinAbs (((s.val / N : ℕ)) : ZMod m) := rfl

omit [NeZero m] in
theorem slift_succ_of_lt (hℓ : ℓ = N * m) (s : ZMod ℓ) (h : sc N s + 1 < N) :
    slift N m (s + 1) = slift N m s + 1 := by
  have hN : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have h : s.val % N + 1 < N := h
  have hdiv : (s.val + 1) / N = s.val / N := by
    have h1 := Nat.div_add_mod s.val N
    have h2 : s.val + 1 = N * (s.val / N) + (s.val % N + 1) := by omega
    rw [h2, Nat.mul_add_div hN, Nat.div_eq_of_lt h]; simp
  have hmod : (s.val + 1) % N = sc N s + 1 := by
    have h1 := Nat.div_add_mod s.val N
    have h2 : s.val + 1 = N * (s.val / N) + (s.val % N + 1) := by omega
    rw [h2, Nat.mul_add_mod, Nat.mod_eq_of_lt h]; rfl
  unfold slift
  rw [sb_succ hℓ, sc_succ hℓ, hdiv, hmod, ← sb_def]
  push_cast; ring

omit [NeZero m] in
theorem blockCoord_succ_last (hℓ : ℓ = N * m) (s : ZMod ℓ) (h : sc N s + 1 = N) :
    blockCoord N m (s + 1) = blockCoord N m s + 1 := by
  have hN : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have h2 : s.val + 1 = N * (s.val / N + 1) := by
    have h1 := Nat.div_add_mod s.val N
    unfold sc at h; nlinarith
  have hdiv : (s.val + 1) / N = s.val / N + 1 := by rw [h2, Nat.mul_div_cancel_left _ hN]
  rw [blockCoord_succ hℓ, hdiv]
  simp [blockCoord]

omit [NeZero m] in
theorem slift_succ_of_last (hℓ : ℓ = N * m) (s : ZMod ℓ) (h : sc N s + 1 = N) :
    slift N m (s + 1) = (N : ℤ) * ZMod.valMinAbs (blockCoord N m s + 1) := by
  have hN : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have hdiv : (s.val + 1) / N = s.val / N + 1 := by
    have h1 := Nat.div_add_mod s.val N
    have h2 : s.val + 1 = N * (s.val / N + 1) := by unfold sc at h; nlinarith
    rw [h2, Nat.mul_div_cancel_left _ hN]
  have hmod : (s.val + 1) % N = 0 := by
    have h2 : s.val + 1 = N * (s.val / N + 1) := by
      have h1 := Nat.div_add_mod s.val N
      unfold sc at h; nlinarith
    rw [h2]; exact Nat.mul_mod_right _ _
  unfold slift
  rw [sb_succ hℓ, sc_succ hℓ, hdiv, hmod]
  push_cast
  simp [blockCoord]

theorem valMinAbs_succ_cases (x : ZMod m) (h : ZMod.valMinAbs (x + 1) ≠ ZMod.valMinAbs x + 1) :
    (m : ℤ) - 2 ≤ 2 * ZMod.valMinAbs x ∧ 2 * ZMod.valMinAbs x ≤ m ∧
      ZMod.valMinAbs (x + 1) = ZMod.valMinAbs x + 1 - m := by
  have hm : (0 : ℤ) < m := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne m)
  have h1 := ZMod.valMinAbs_mem_Ioc x
  have h2 := ZMod.valMinAbs_mem_Ioc (x + 1)
  simp only [Set.mem_Ioc] at h1 h2
  have hc : ((ZMod.valMinAbs (x + 1) : ℤ) : ZMod m) = (((ZMod.valMinAbs x + 1 : ℤ)) : ZMod m) := by
    simp [ZMod.coe_valMinAbs]
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at hc
  obtain ⟨k, hk⟩ := hc
  have hk0 : k ≠ 0 := by
    rintro rfl
    apply h; linarith
  have hk1 : k < 2 := by
    by_contra hk'; push Not at hk'
    nlinarith
  have hk2 : -1 < k := by
    by_contra hk'; push Not at hk'
    nlinarith
  have hk3 : k = 1 := by omega
  subst hk3
  refine ⟨by nlinarith, by nlinarith, by nlinarith⟩

omit [NeZero N] [NeZero m] in
theorem sc_succ_lt (hℓ : ℓ = N * m) (s : ZMod ℓ) (h : sc N s + 1 < N) : sc N (s + 1) = sc N s + 1 := by
  rw [sc_succ hℓ]
  have : (s.val + 1) % N = (s.val % N + 1) % N := Nat.add_mod _ _ _ |>.trans (by simp)
  rw [this]
  exact Nat.mod_eq_of_lt h

omit [NeZero N] [NeZero m] in
theorem sc_succ_last (hℓ : ℓ = N * m) (s : ZMod ℓ) (h : sc N s + 1 = N) : sc N (s + 1) = 0 := by
  rw [sc_succ hℓ]
  have : (s.val + 1) % N = (s.val % N + 1) % N := Nat.add_mod _ _ _ |>.trans (by simp)
  rw [this]
  have h' : s.val % N + 1 = N := h
  rw [h']; exact Nat.mod_self N

omit [NeZero ℓ] in
theorem sc_lt (s : ZMod ℓ) : sc N s < N := Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne N))

theorem seam_succ (hℓ : ℓ = N * m) (s : ZMod ℓ) (h : slift N m (s + 1) ≠ slift N m s + 1) :
    (m : ℤ) - 2 ≤ 2 * sb N m s ∧ 2 * sb N m s ≤ m := by
  by_cases hl : sc N s + 1 < N
  · exact absurd (slift_succ_of_lt hℓ s hl) h
  · have hlast : sc N s + 1 = N := by have := sc_lt (N := N) s; omega
    have h1 := slift_succ_of_last hℓ s hlast
    have h2 : slift N m s + 1 = (N : ℤ) * (sb N m s + 1) := by
      unfold slift; have : (sc N s : ℤ) + 1 = N := by exact_mod_cast hlast
      linear_combination this
    rw [h1, h2] at h
    have hN : (N : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne N
    have hne : ZMod.valMinAbs (blockCoord N m s + 1) ≠ sb N m s + 1 := fun e => h (by rw [e])
    obtain ⟨a, b, -⟩ := valMinAbs_succ_cases (blockCoord N m s) hne
    exact ⟨a, b⟩

theorem seam_pred (hℓ : ℓ = N * m) (s : ZMod ℓ) (h : slift N m (s - 1) ≠ slift N m s - 1) :
    (m : ℤ) - 2 ≤ -(2 * sb N m s) ∧ -(2 * sb N m s) ≤ m := by
  have hs : s - 1 + 1 = s := sub_add_cancel s 1
  set s' := s - 1 with hs'
  have hh : slift N m (s' + 1) ≠ slift N m s' + 1 := by
    rw [hs]; intro e; apply h; rw [e]; ring
  by_cases hl : sc N s' + 1 < N
  · exact absurd (slift_succ_of_lt hℓ s' hl) hh
  · have hlast : sc N s' + 1 = N := by have := sc_lt (N := N) s'; omega
    have h1 := slift_succ_of_last hℓ s' hlast
    have h2 : slift N m s' + 1 = (N : ℤ) * (sb N m s' + 1) := by
      unfold slift; have : (sc N s' : ℤ) + 1 = N := by exact_mod_cast hlast
      linear_combination this
    rw [h1, h2] at hh
    have hN : (N : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne N
    have hne : ZMod.valMinAbs (blockCoord N m s' + 1) ≠ sb N m s' + 1 := fun e => hh (by rw [e])
    obtain ⟨a, b, c⟩ := valMinAbs_succ_cases (blockCoord N m s') hne
    have hsc : sc N s = 0 := by rw [← hs]; exact sc_succ_last hℓ s' hlast
    have hsb : sb N m s = ZMod.valMinAbs (blockCoord N m s' + 1) := by
      have : blockCoord N m s = blockCoord N m s' + 1 := by
        rw [← hs]; exact blockCoord_succ_last hℓ s' hlast
      unfold sb; rw [this]
    have hsb' : sb N m s' = ZMod.valMinAbs (blockCoord N m s') := rfl
    rw [hsb, c, ← hsb']
    constructor <;> linarith

/-- The error of the periodization: the part of `hamil1` missed by `HZ` on the lift. -/
noncomputable def sawErr (N m : ℕ) (F₂ F₁ F₀ : ZMod N → ℂ) (s : ZMod ℓ) : ℂ :=
  -(saw N m F₂ F₁ F₀ (s + 1) - polyZ F₂ F₁ F₀ (slift N m s + 1))
    - (saw N m F₂ F₁ F₀ (s - 1) - polyZ F₂ F₁ F₀ (slift N m s - 1))

theorem hamil1_saw (hℓ : ℓ = N * m) (w ν : ℝ) (F₂ F₁ F₀ : ZMod N → ℂ) (s : ZMod ℓ) :
    hamil1 N m w ν (saw N m F₂ F₁ F₀) s =
      HZ N w ν (polyZ F₂ F₁ F₀) (slift N m s) + sawErr N m F₂ F₁ F₀ s := by
  unfold hamil1 HZ sawErr
  rw [blockavg_saw hℓ]
  have : saw N m F₂ F₁ F₀ s = polyZ F₂ F₁ F₀ (slift N m s) := rfl
  rw [this]
  ring

omit [NeZero ℓ] [NeZero N] [NeZero m] in
theorem sawErr_eq_zero (F₂ F₁ F₀ : ZMod N → ℂ) (s : ZMod ℓ)
    (h1 : slift N m (s + 1) = slift N m s + 1) (h2 : slift N m (s - 1) = slift N m s - 1) :
    sawErr N m F₂ F₁ F₀ s = 0 := by
  unfold sawErr saw
  rw [h1, h2]; ring

theorem sawErr_ne_zero (hℓ : ℓ = N * m) (F₂ F₁ F₀ : ZMod N → ℂ) (s : ZMod ℓ)
    (h : sawErr N m F₂ F₁ F₀ s ≠ 0) : (m : ℤ) - 2 ≤ |2 * sb N m s| := by
  by_cases h1 : slift N m (s + 1) = slift N m s + 1
  · by_cases h2 : slift N m (s - 1) = slift N m s - 1
    · exact absurd (sawErr_eq_zero F₂ F₁ F₀ s h1 h2) h
    · exact ((seam_pred hℓ s h2).1).trans (neg_le_abs _)
  · exact ((seam_succ hℓ s h1).1).trans (le_abs_self _)

/-- The sum of the sup norms of the three cell coefficients. -/
noncomputable def cellNorm (F₂ F₁ F₀ : ZMod N → ℂ) : ℝ := ∑ r, (‖F₂ r‖ + ‖F₁ r‖ + ‖F₀ r‖)

theorem norm_polyZ_le (F₂ F₁ F₀ : ZMod N → ℂ) (k : ℤ) :
    ‖polyZ F₂ F₁ F₀ k‖ ≤ cellNorm F₂ F₁ F₀ * (|((k / N : ℤ) : ℝ)| + 1) ^ 2 := by
  unfold polyZ cellNorm
  set r : ZMod N := (k : ZMod N)
  set x : ℝ := |(((k / N : ℤ)) : ℝ)|
  have hx : ‖((k / N : ℤ) : ℂ)‖ = x := by simp [x]
  have hr : ‖F₂ r‖ + ‖F₁ r‖ + ‖F₀ r‖ ≤ ∑ r, (‖F₂ r‖ + ‖F₁ r‖ + ‖F₀ r‖) :=
    Finset.single_le_sum (f := fun r => ‖F₂ r‖ + ‖F₁ r‖ + ‖F₀ r‖)
      (fun r _ => by positivity) (Finset.mem_univ r)
  have hx0 : 0 ≤ x := abs_nonneg _
  calc ‖F₂ r * ((k / N : ℤ) : ℂ) ^ 2 + F₁ r * ((k / N : ℤ) : ℂ) + F₀ r‖
      ≤ ‖F₂ r‖ * x ^ 2 + ‖F₁ r‖ * x + ‖F₀ r‖ := by
        refine (norm_add₃_le).trans ?_
        simp only [norm_mul, norm_pow, hx]; exact le_rfl
    _ ≤ (‖F₂ r‖ + ‖F₁ r‖ + ‖F₀ r‖) * (x + 1) ^ 2 := by
        have := norm_nonneg (F₂ r); have := norm_nonneg (F₁ r); have := norm_nonneg (F₀ r)
        nlinarith [mul_nonneg (norm_nonneg (F₁ r)) hx0, mul_nonneg (norm_nonneg (F₀ r)) hx0,
          mul_nonneg (norm_nonneg (F₀ r)) (mul_nonneg hx0 hx0)]
    _ ≤ _ := mul_le_mul_of_nonneg_right hr (sq_nonneg _)

omit [NeZero ℓ] [NeZero N] in
theorem abs_sb_le (x : ZMod ℓ) : |((sb N m x : ℤ) : ℝ)| ≤ (m : ℝ) / 2 := by
  have h := ZMod.valMinAbs_mem_Ioc (blockCoord N m x)
  simp only [Set.mem_Ioc] at h
  have h1 : (-(m : ℝ)) < 2 * (sb N m x : ℝ) := by
    have : (-(m : ℤ)) < 2 * sb N m x := by unfold sb; linarith [h.1]
    exact_mod_cast this
  have h2 : 2 * (sb N m x : ℝ) ≤ m := by
    have : 2 * sb N m x ≤ (m : ℤ) := by unfold sb; linarith [h.2]
    exact_mod_cast this
  rw [abs_le]; constructor <;> linarith

theorem abs_ediv_succ_le (k : ℤ) :
    |(((k + 1) / N : ℤ) : ℝ)| ≤ |((k / N : ℤ) : ℝ)| + 1 := by
  have h := int_ediv_succ (M := N) k
  have h' : ((k + 1) / N : ℤ) = k / N ∨ ((k + 1) / N : ℤ) = k / N + 1 := by
    rw [h]; split_ifs <;> simp
  rcases h' with h' | h' <;> rw [h'] <;> push_cast
  · linarith [abs_nonneg ((k / N : ℤ) : ℝ)]
  · exact (abs_add_le _ _).trans (by simp)

theorem abs_ediv_pred_le (k : ℤ) :
    |(((k - 1) / N : ℤ) : ℝ)| ≤ |((k / N : ℤ) : ℝ)| + 1 := by
  have h := int_ediv_pred (M := N) k
  have h' : ((k - 1) / N : ℤ) = k / N ∨ ((k - 1) / N : ℤ) = k / N - 1 := by
    rw [h]; split_ifs <;> simp
  rcases h' with h' | h' <;> rw [h'] <;> push_cast
  · linarith [abs_nonneg ((k / N : ℤ) : ℝ)]
  · exact (abs_sub _ _).trans (by simp)

omit [NeZero ℓ] in
theorem norm_sawErr_le (F₂ F₁ F₀ : ZMod N → ℂ) (s : ZMod ℓ) :
    ‖sawErr N m F₂ F₁ F₀ s‖ ≤ 4 * cellNorm F₂ F₁ F₀ * ((m : ℝ) / 2 + 2) ^ 2 := by
  have hC : 0 ≤ cellNorm F₂ F₁ F₀ := Finset.sum_nonneg fun r _ => by positivity
  have key : ∀ k : ℤ, |((k / N : ℤ) : ℝ)| ≤ (m : ℝ) / 2 + 1 →
      ‖polyZ F₂ F₁ F₀ k‖ ≤ cellNorm F₂ F₁ F₀ * ((m : ℝ) / 2 + 2) ^ 2 := fun k hk =>
    (norm_polyZ_le F₂ F₁ F₀ k).trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by positivity) (by linarith) 2) hC)
  have hsaw : ∀ y : ZMod ℓ, ‖saw N m F₂ F₁ F₀ y‖ ≤ cellNorm F₂ F₁ F₀ * ((m : ℝ) / 2 + 2) ^ 2 :=
    fun y => key _ (by rw [slift_ediv]; linarith [abs_sb_le (N := N) (m := m) y])
  have h0 : |((slift N m s / N : ℤ) : ℝ)| ≤ (m : ℝ) / 2 := by
    rw [slift_ediv]; exact abs_sb_le s
  have hp := key (slift N m s + 1) (by linarith [abs_ediv_succ_le (N := N) (slift N m s)])
  have hq := key (slift N m s - 1) (by linarith [abs_ediv_pred_le (N := N) (slift N m s)])
  unfold sawErr
  calc ‖-(saw N m F₂ F₁ F₀ (s + 1) - polyZ F₂ F₁ F₀ (slift N m s + 1))
        - (saw N m F₂ F₁ F₀ (s - 1) - polyZ F₂ F₁ F₀ (slift N m s - 1))‖
      ≤ ‖saw N m F₂ F₁ F₀ (s + 1)‖ + ‖polyZ F₂ F₁ F₀ (slift N m s + 1)‖
        + (‖saw N m F₂ F₁ F₀ (s - 1)‖ + ‖polyZ F₂ F₁ F₀ (slift N m s - 1)‖) := by
        refine (norm_sub_le _ _).trans ?_
        rw [norm_neg]
        gcongr <;> exact norm_sub_le _ _
    _ ≤ _ := by
        have := hsaw (s + 1); have := hsaw (s - 1); linarith

omit [NeZero N] [NeZero m] in
theorem slift_cast (hℓ : ℓ = N * m) (s : ZMod ℓ) : ((slift N m s : ℤ) : ZMod ℓ) = s := by
  have hq : ((sb N m s : ℤ) : ZMod m) = ((s.val / N : ℕ) : ZMod m) := by
    unfold sb blockCoord; exact ZMod.coe_valMinAbs _
  have h2 : (m : ℤ) ∣ (sb N m s - ((s.val / N : ℕ) : ℤ)) := by
    rw [← ZMod.intCast_eq_intCast_iff_dvd_sub, hq]; exact Int.cast_natCast (R := ZMod m) (s.val / N)
  obtain ⟨c, hc⟩ := h2
  have hd : (N : ℤ) * ((s.val / N : ℕ) : ℤ) + ((s.val % N : ℕ) : ℤ) = (s.val : ℤ) := by
    exact_mod_cast Nat.div_add_mod s.val N
  have hmain : slift N m s = (s.val : ℤ) + ((N * m : ℕ) : ℤ) * c := by
    unfold slift sc
    simp only [Nat.cast_mul]
    have : (sb N m s : ℤ) = ((s.val / N : ℕ) : ℤ) + m * c := by linarith
    rw [this]
    linear_combination hd
  rw [hmain]
  have h3 : ((N * m : ℕ) : ZMod ℓ) = 0 := by rw [← hℓ]; exact ZMod.natCast_self ℓ
  push_cast at h3 ⊢
  rw [h3]; simp

theorem cycRep_two_abs_le (a : ZMod ℓ) : |2 * Green.cycRep a| ≤ ℓ := by
  unfold Green.cycRep
  split_ifs with h
  · rw [abs_le]; constructor <;> omega
  · have := ZMod.val_lt a
    rw [abs_le]; constructor <;> omega

omit [NeZero N] in
theorem dist_seam (hℓ : ℓ = N * m) (s a : ZMod ℓ) (ha : a.val < N)
    (hs : (m : ℤ) - 2 ≤ |2 * sb N m s|) :
    (N : ℤ) * ((m : ℤ) - 4) ≤ 2 * |Green.cycRep (s - a)| := by
  have hκ := cycRep_two_abs_le (s - a)
  set κ := Green.cycRep (s - a) with hκdef
  have hcast : ((κ : ℤ) : ZMod ℓ) = (((slift N m s - (a.val : ℤ) : ℤ)) : ZMod ℓ) := by
    rw [hκdef, Green.cast_cycRep]
    push_cast
    rw [slift_cast hℓ, ZMod.natCast_zmod_val]
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at hcast
  obtain ⟨t, ht⟩ := hcast
  have hN : (0 : ℤ) ≤ N := Nat.cast_nonneg N
  have hsc : (sc N s : ℤ) < N := by
    unfold sc; exact_mod_cast Nat.mod_lt _ (by omega : 0 < N)
  have hsc0 : (0 : ℤ) ≤ sc N s := Nat.cast_nonneg _
  have hav : (a.val : ℤ) < N := by exact_mod_cast ha
  have hav0 : (0 : ℤ) ≤ a.val := Nat.cast_nonneg _
  have hsb2 : |2 * sb N m s| ≤ m := by
    have h := ZMod.valMinAbs_mem_Ioc (blockCoord N m s)
    simp only [Set.mem_Ioc] at h
    unfold sb
    rw [abs_le]; constructor <;> linarith [h.1, h.2]
  have hP1 : (N : ℤ) * ((m : ℤ) - 2) ≤ |2 * ((N : ℤ) * sb N m s)| := by
    have : |2 * ((N : ℤ) * sb N m s)| = (N : ℤ) * |2 * sb N m s| := by
      rw [show 2 * ((N : ℤ) * sb N m s) = (N : ℤ) * (2 * sb N m s) by ring, abs_mul,
        abs_of_nonneg hN]
    rw [this]; exact mul_le_mul_of_nonneg_left hs hN
  have hP2 : |2 * ((N : ℤ) * sb N m s)| ≤ (N : ℤ) * m := by
    have : |2 * ((N : ℤ) * sb N m s)| = (N : ℤ) * |2 * sb N m s| := by
      rw [show 2 * ((N : ℤ) * sb N m s) = (N : ℤ) * (2 * sb N m s) by ring, abs_mul,
        abs_of_nonneg hN]
    rw [this]; exact mul_le_mul_of_nonneg_left hsb2 hN
  have hℓz : (ℓ : ℤ) = (N : ℤ) * m := by rw [hℓ]; push_cast; ring
  have hD : slift N m s - (a.val : ℤ) = (N : ℤ) * sb N m s + ((sc N s : ℤ) - a.val) := by
    unfold slift; ring
  have hdiff : |2 * ((sc N s : ℤ) - a.val)| ≤ 2 * ((N : ℤ) - 1) := by
    rw [abs_le]; constructor <;> linarith
  rw [hD] at ht
  have hκ2 : 2 * |κ| = |2 * κ| := by rw [abs_mul]; simp
  rw [hκ2]
  by_cases h0 : t = 0
  · subst h0
    have hκeq : 2 * κ = 2 * ((N : ℤ) * sb N m s) + 2 * ((sc N s : ℤ) - a.val) := by linarith
    have := abs_sub_abs_le_abs_sub (2 * ((N : ℤ) * sb N m s)) (-(2 * ((sc N s : ℤ) - a.val)))
    rw [abs_neg, sub_neg_eq_add, ← hκeq] at this
    nlinarith
  · have ht1 : (ℓ : ℤ) ≤ |(ℓ : ℤ) * t| := by
      rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg ℓ)]
      exact le_mul_of_one_le_right (Nat.cast_nonneg ℓ) (Int.one_le_abs h0)
    set X : ℤ := 2 * ((N : ℤ) * sb N m s) + 2 * ((sc N s : ℤ) - a.val) with hX
    have hκeq : 2 * ((ℓ : ℤ) * t) - X = -(2 * κ) := by rw [hX]; linarith
    have h1 := abs_sub_abs_le_abs_sub (2 * ((ℓ : ℤ) * t)) X
    rw [hκeq, abs_neg] at h1
    have h2 : |2 * ((ℓ : ℤ) * t)| = 2 * |(ℓ : ℤ) * t| := by
      rw [abs_mul]; simp
    have h3 := abs_add_le (2 * ((N : ℤ) * sb N m s)) (2 * ((sc N s : ℤ) - a.val))
    rw [← hX] at h3
    nlinarith

end Balaban.Flow
