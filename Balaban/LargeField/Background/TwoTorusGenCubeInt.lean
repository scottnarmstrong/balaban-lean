/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Background.TwoTorusCubeLift
public import Balaban.LargeField.Background.StepGenSets

/-!
# The neighbourhood of a cube on integer lifts

For a cube `a = zcast n u` of side `P`, the sites of its neighbourhood `a^{∼r}` have integer
representatives `z` with `bidx P z + s = u` for some `|s| ≤ r` (when no wrap around the torus
occurs: `two_abs_nbhd_close`), and the sites of the neighbourhood of a cube whose lift is in a box
with margin are in the box (`nbhd_cube_near`).
-/

@[expose] public section

namespace Balaban.RootFSpine

open Balaban Balaban.LargeField

section Int

theorem ediv_diff_bound {P a b B : ℤ} (hP : 0 < P) (h : |a - b| ≤ B) :
    P * (|a / P - b / P| - 1) < B := by
  have h1 := Int.emod_add_mul_ediv a P
  have h2 := Int.emod_add_mul_ediv b P
  have h3 := Int.emod_nonneg a hP.ne'
  have h4 := Int.emod_lt_of_pos a hP
  have h5 := Int.emod_nonneg b hP.ne'
  have h6 := Int.emod_lt_of_pos b hP
  have e1 : P * (a / P - b / P) < (a - b) + P := by
    have : P * (a / P - b / P) = P * (a / P) - P * (b / P) := mul_sub _ _ _
    linarith
  have e2 : (a - b) - P < P * (a / P - b / P) := by
    have : P * (a / P - b / P) = P * (a / P) - P * (b / P) := mul_sub _ _ _
    linarith
  rcases abs_cases (a / P - b / P) with ⟨h7, h8⟩ | ⟨h7, h8⟩
  · rw [h7]
    have : a - b ≤ |a - b| := le_abs_self _
    nlinarith
  · rw [h7]
    have : -(a - b) ≤ |a - b| := neg_le_abs _
    nlinarith

/-- Floor quotients of integers within `ℓ/2 + ρ` of each other (with `ℓ = P n`) differ by less
than `n - r`, so that adding a shift of size `≤ r` stays below `n`. -/
theorem ediv_close_lt_r {P n a b ρ r : ℤ} (hP : 0 < P) (hρ : ρ ≤ P)
    (hn : 2 * r + 8 ≤ n) (h : 2 * |a - b| ≤ P * n + 2 * ρ) : |a / P - b / P| + r < n := by
  have := ediv_diff_bound (P := P) (a := a) (b := b) (B := (P * n + 2 * ρ + 1) / 2) hP (by omega)
  by_contra hc
  have h1 : n ≤ |a / P - b / P| + r := by omega
  have h2 : P * (n - r - 1) ≤ P * (|a / P - b / P| - 1) := by
    apply mul_le_mul_of_nonneg_left (by omega) hP.le
  have h4 : 2 * ((P * n + 2 * ρ + 1) / 2) ≤ P * n + 2 * ρ + 1 := Int.mul_ediv_self_le (by norm_num)
  nlinarith

end Int

section Agree

variable {d : ℕ}

theorem mem_cubePre_nbhd_zcast {M1 N₁ L q : ℕ} [NeZero M1] [NeZero N₁] [NeZero L] {P n r : ℕ}
    (hP : 0 < P) (hℓ : M1 * N₁ * L ^ q = P * n) (a : Torus d n) (w : Fin d → ℤ) :
    zcast (M1 * N₁ * L ^ q) w ∈ cubePre M1 N₁ L q P n (nbhd r {a}) ↔
      ∃ s : Fin d → ℤ, (∀ μ, |s μ| ≤ r) ∧ zcast n (bidx P w + s) = a := by
  have : NeZero n := ⟨fun h0 => by
    have := NeZero.ne (M1 * N₁ * L ^ q)
    rw [hℓ, h0] at this; simp at this⟩
  rw [mem_cubePre, blockMap_zcast hℓ hP]
  exact (mem_nbhd_zcast (bidx P w)).trans (by simp [Set.mem_singleton_iff])

/-- Without wrap around the torus, a shift of the cube index is an equality of integers. -/
theorem exists_shift_iff {n r : ℕ} {z u : Fin d → ℤ}
    (h : ∀ μ, |z μ - u μ| + r < n) :
    (∃ s : Fin d → ℤ, (∀ μ, |s μ| ≤ r) ∧ zcast n (z + s) = zcast n u) ↔
      ∃ s : Fin d → ℤ, (∀ μ, |s μ| ≤ r) ∧ z + s = u := by
  refine exists_congr fun s => and_congr_right fun hs => ?_
  refine zcast_eq_iff_of_abs_lt fun μ => ?_
  have h1 := h μ
  have h2 := hs μ
  have h3 : |(z + s) μ - u μ| ≤ |z μ - u μ| + |s μ| := by
    have := abs_add_le (z μ - u μ) (s μ)
    simpa [Pi.add_apply, add_sub_right_comm] using this
  have : (r : ℤ) ≥ |s μ| := h2
  omega

end Agree

section Near

variable {d : ℕ}

/-- The one-dimensional core of `nbhd_cube_near`. -/
theorem int_near {P n r R ℓ v w c s t : ℤ} (hP : 0 < P) (hn : 0 < n) (hℓ : ℓ = P * n)
    (hs : |s| ≤ r) (hbid : v / P + s - w / P = n * t) (hlv : 2 * |v - c| ≤ ℓ)
    (hw : 4 * (|w - c| + R) < ℓ) (hR : (r + 2) * P ≤ R) : |v - w| ≤ (r + 1) * P := by
  have h1 := Int.emod_add_mul_ediv v P
  have h2 := Int.emod_add_mul_ediv w P
  have h3 := Int.emod_nonneg v hP.ne'
  have h4 := Int.emod_lt_of_pos v hP
  have h5 := Int.emod_nonneg w hP.ne'
  have h6 := Int.emod_lt_of_pos w hP
  have hdiff : v - w = P * (n * t) - P * s + (v % P - w % P) := by
    have : v / P = n * t - s + w / P := by linarith
    rw [this] at h1
    nlinarith
  have hsP : P * |s| ≤ P * r := mul_le_mul_of_nonneg_left hs hP.le
  have hsP' : |P * s| = P * |s| := by rw [abs_mul, abs_of_pos hP]
  have hθ : |v % P - w % P| ≤ P := by
    rw [abs_le]; constructor <;> linarith
  have ht0 : t = 0 := by
    by_contra hne
    have htabs : 1 ≤ |t| := Int.one_le_abs hne
    have hT : |P * (n * t)| = P * n * |t| := by
      rw [abs_mul, abs_mul, abs_of_pos hP, abs_of_pos hn]; ring
    have hbig : P * n ≤ P * n * |t| := le_mul_of_one_le_right (mul_pos hP hn).le htabs
    have a1 : |P * (n * t)| ≤ |v - w| + |P * s| + |v % P - w % P| := by
      have e : P * (n * t) = (v - w) + P * s - (v % P - w % P) := by rw [hdiff]; ring
      rw [e]
      calc |(v - w) + P * s - (v % P - w % P)|
          ≤ |(v - w) + P * s| + |v % P - w % P| := abs_sub _ _
        _ ≤ |v - w| + |P * s| + |v % P - w % P| := by
          have := abs_add_le (v - w) (P * s); linarith
    have hc1 : |v - w| ≤ |v - c| + |w - c| := by
      have := abs_sub_le v c w
      rw [abs_sub_comm c w] at this
      exact this
    have hc5 : (0 : ℤ) ≤ |w - c| := abs_nonneg _
    have hR0 : (0 : ℤ) ≤ R := by
      have : 0 ≤ (r + 2) * P := mul_nonneg (by have := abs_nonneg s; linarith) hP.le
      linarith
    rw [hT] at a1
    nlinarith
  rw [ht0, mul_zero] at hdiff
  have hdiff' : v - w = -(P * s) + (v % P - w % P) := by rw [hdiff]; ring
  rw [abs_le] at hθ ⊢
  have hs1 := abs_le.1 hs
  have e1 : -(P * r) ≤ P * s := by nlinarith
  have e2 : P * s ≤ P * r := by nlinarith
  constructor <;> nlinarith

/-- The sites of the `r`-neighbourhood of a cube `zcast n (bidx P w₀)` (side `P`, `ℓ = P n`) have
representatives near the box point `w₀`: within `(r + 1) P`. -/
theorem nbhd_cube_near {ℓ ℓ' n P r R : ℕ} [NeZero ℓ] [NeZero n] {c w₀ : Fin d → ℤ} (hP : 0 < P)
    (hℓ : ℓ = P * n) (hw₀ : InBoxK R ℓ ℓ' c w₀) (hR : (r + 2) * P ≤ R) (x : Torus d ℓ)
    (hx : blockMap P n x ∈ nbhd r {zcast n (bidx P w₀)}) :
    ∀ μ, |liftNear c x μ - w₀ μ| ≤ ((r + 1) * P : ℕ) := by
  have hxe : x = zcast ℓ (liftNear c x) := (zcast_liftNear x).symm
  rw [hxe, blockMap_zcast hℓ hP] at hx
  obtain ⟨s, hs, hmem⟩ := (mem_nbhd_zcast (bidx P (liftNear c x))).1 hx
  have hd := (zcast_eq_iff n _ _).1 (Set.mem_singleton_iff.1 hmem)
  intro μ
  obtain ⟨t, ht⟩ := hd μ
  have hbid : liftNear c x μ / (P : ℤ) + s μ - w₀ μ / (P : ℤ) = n * t := by
    simp only [bidx, Pi.add_apply] at ht
    exact ht
  have hPi : (0 : ℤ) < P := by exact_mod_cast hP
  have hnn : (0 : ℤ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  have hℓi : (ℓ : ℤ) = P * n := by rw [hℓ]; push_cast; ring
  have hwb := hw₀ μ
  have := int_near (r := (r : ℤ)) (R := (R : ℤ)) hPi hnn hℓi (hs μ) hbid
    (liftNear_abs_le c x μ) (by simpa using hwb.1) (by exact_mod_cast hR)
  push_cast
  exact this

end Near

end Balaban.RootFSpine
