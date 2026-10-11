/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Background.Bump
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

/-!
# Mixed second differences of the periodic bumps

For `μ ≠ ν` the bump factorizes over coordinates, so the mixed second difference
`b(x + e_μ + e_ν) - b(x + e_μ) - b(x + e_ν) + b(x)` is a product of two one-coordinate first
differences times the remaining factors; for `μ = ν` it is a centred second difference of one
coordinate factor at `x + e_μ`.  Both are at most `22500 · 4^d / (L^m)²` (`bump_sq_diff`).
-/

@[expose] public section

namespace Balaban.Background

open Balaban.Multiscale Finset

variable {d L N₀ k : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}

/-- The integer lift of the corner `x + i e_μ + j e_ν`. -/
def cornerLift (x : Torus d (N₀ * L ^ k)) (μ ν : Fin d) (i j : ℤ) : Fin d → ℤ := fun ρ =>
  ((x ρ).val : ℤ) + (if ρ = μ then i else 0) + (if ρ = ν then j else 0)

theorem bump_eq_prod_lift (m : ℕ) (y0 x : Torus d (N₀ * L ^ k)) (t : Fin d → ℤ)
    (ht : ∀ ρ, ((t ρ : ℤ) : ZMod (N₀ * L ^ k)) = x ρ) :
    bump m y0 x = ∏ ρ, perFac m y0 ρ (t ρ : ℝ) := by
  unfold bump
  exact prod_congr rfl fun ρ _ => (perFac_lift m y0 x ρ (t ρ) (ht ρ)).symm

theorem cast_cornerLift (x : Torus d (N₀ * L ^ k)) (μ ν : Fin d) (i j : ℤ) (ρ : Fin d) :
    ((cornerLift x μ ν i j ρ : ℤ) : ZMod (N₀ * L ^ k)) =
      x ρ + (if ρ = μ then (i : ZMod (N₀ * L ^ k)) else 0) +
        (if ρ = ν then (j : ZMod (N₀ * L ^ k)) else 0) := by
  unfold cornerLift
  by_cases h1 : ρ = μ <;> by_cases h2 : ρ = ν <;> simp [h1, h2]

theorem prod_corner_eq {μ ν : Fin d} (hμν : μ ≠ ν) (F : Fin d → ℝ) :
    ∏ ρ, F ρ = F μ * F ν * ∏ ρ ∈ (univ.erase μ).erase ν, F ρ := by
  have h1 : ν ∈ univ.erase μ := mem_erase.2 ⟨hμν.symm, mem_univ _⟩
  rw [← mul_prod_erase univ F (mem_univ μ), ← mul_prod_erase (univ.erase μ) F h1, mul_assoc]

theorem rest2_nonneg {m : ℕ} (hm : m ≤ k) (y0 x : Torus d (N₀ * L ^ k)) (μ ν : Fin d) :
    0 ≤ ∏ ρ ∈ (univ.erase μ).erase ν, perFac m y0 ρ ((x ρ).val : ℝ) :=
  prod_nonneg fun ρ _ => perFac_nonneg hm y0 ρ _

theorem rest2_le {m : ℕ} (hm : m ≤ k) (y0 x : Torus d (N₀ * L ^ k)) (μ ν : Fin d) :
    ∏ ρ ∈ (univ.erase μ).erase ν, perFac m y0 ρ ((x ρ).val : ℝ) ≤ 4 ^ d := by
  calc _ ≤ ∏ _ρ ∈ (univ.erase μ).erase ν, (4 : ℝ) :=
        Finset.prod_le_prod₀ (fun ρ _ => perFac_nonneg hm y0 ρ _) fun ρ _ => perFac_le hm y0 ρ _
    _ = 4 ^ ((univ.erase μ).erase ν).card := by simp
    _ ≤ 4 ^ d := pow_le_pow_right₀ (by norm_num) (by
        calc ((univ.erase μ).erase ν).card ≤ (univ.erase μ).card := card_erase_le
          _ ≤ d := by rw [card_erase_of_mem (mem_univ μ)]; simp)

/-- The mixed second difference of the bump for `μ ≠ ν` factorizes. -/
theorem bump_sq_ne (m : ℕ) (y0 x : Torus d (N₀ * L ^ k)) {μ ν : Fin d} (hμν : μ ≠ ν) :
    bump m y0 (x + Pi.single μ 1 + Pi.single ν 1) - bump m y0 (x + Pi.single μ 1) -
        bump m y0 (x + Pi.single ν 1) + bump m y0 x =
      (perFac m y0 μ (((x μ).val : ℝ) + 1) - perFac m y0 μ ((x μ).val : ℝ)) *
        (perFac m y0 ν (((x ν).val : ℝ) + 1) - perFac m y0 ν ((x ν).val : ℝ)) *
        ∏ ρ ∈ (univ.erase μ).erase ν, perFac m y0 ρ ((x ρ).val : ℝ) := by
  have hl : ∀ (i j : ℤ) (z : Torus d (N₀ * L ^ k)),
      (∀ ρ, z ρ = x ρ + (if ρ = μ then (i : ZMod (N₀ * L ^ k)) else 0) +
        (if ρ = ν then (j : ZMod (N₀ * L ^ k)) else 0)) →
      bump m y0 z = perFac m y0 μ (((x μ).val : ℝ) + i) * perFac m y0 ν (((x ν).val : ℝ) + j) *
        ∏ ρ ∈ (univ.erase μ).erase ν, perFac m y0 ρ ((x ρ).val : ℝ) := by
    intro i j z hz
    rw [bump_eq_prod_lift m y0 z (cornerLift x μ ν i j)
      (fun ρ => by rw [cast_cornerLift, hz ρ]),
      prod_corner_eq hμν]
    congr 1
    · congr 1
      · simp [cornerLift, hμν]
      · simp [cornerLift, hμν.symm]
    · refine prod_congr rfl fun ρ hρ => ?_
      have h1 : ρ ≠ ν := (mem_erase.1 hρ).1
      have h2 : ρ ≠ μ := (mem_erase.1 (mem_erase.1 hρ).2).1
      simp [cornerLift, h1, h2]
  have c11 := hl 1 1 (x + Pi.single μ 1 + Pi.single ν 1) (fun ρ => by
    by_cases h1 : ρ = μ <;> by_cases h2 : ρ = ν <;> simp [h1, h2, Pi.single_apply])
  have c10 := hl 1 0 (x + Pi.single μ 1) (fun ρ => by
    by_cases h1 : ρ = μ <;> by_cases h2 : ρ = ν <;> simp [h1, h2, Pi.single_apply])
  have c01 := hl 0 1 (x + Pi.single ν 1) (fun ρ => by
    by_cases h1 : ρ = μ <;> by_cases h2 : ρ = ν <;> simp [h1, h2, Pi.single_apply])
  have c00 := hl 0 0 x (fun ρ => by simp)
  rw [c11, c10, c01, c00]
  push_cast
  simp only [add_zero]
  ring

/-- The mixed second difference of the bump for `μ = ν` is a centred second difference. -/
theorem bump_sq_eq (m : ℕ) (y0 x : Torus d (N₀ * L ^ k)) (μ : Fin d) :
    bump m y0 (x + Pi.single μ 1 + Pi.single μ 1) - bump m y0 (x + Pi.single μ 1) -
        bump m y0 (x + Pi.single μ 1) + bump m y0 x =
      (perFac m y0 μ (((x μ).val : ℝ) + 2) - 2 * perFac m y0 μ (((x μ).val : ℝ) + 1) +
        perFac m y0 μ ((x μ).val : ℝ)) *
        ∏ ρ ∈ univ.erase μ, perFac m y0 ρ ((x ρ).val : ℝ) := by
  have hl : ∀ (i : ℤ) (z : Torus d (N₀ * L ^ k)),
      (∀ ρ, z ρ = x ρ + (if ρ = μ then (i : ZMod (N₀ * L ^ k)) else 0)) →
      bump m y0 z = perFac m y0 μ (((x μ).val : ℝ) + i) *
        ∏ ρ ∈ univ.erase μ, perFac m y0 ρ ((x ρ).val : ℝ) := by
    intro i z hz
    rw [bump_eq_prod_lift m y0 z (cornerLift x μ μ i 0)
      (fun ρ => by rw [cast_cornerLift, hz ρ]; simp),
      ← mul_prod_erase univ _ (mem_univ μ)]
    congr 1
    · simp [cornerLift]
    · refine prod_congr rfl fun ρ hρ => ?_
      have h1 : ρ ≠ μ := (mem_erase.1 hρ).1
      simp [cornerLift, h1]
  have c2 := hl 2 (x + Pi.single μ 1 + Pi.single μ 1) (fun ρ => by
    by_cases h1 : ρ = μ
    · subst h1; simp; ring
    · simp [h1])
  have c1 := hl 1 (x + Pi.single μ 1) (fun ρ => by
    by_cases h1 : ρ = μ <;> simp [h1])
  have c0 := hl 0 x (fun ρ => by simp)
  rw [c2, c1, c0]
  push_cast
  simp only [add_zero]
  ring

/-- **Mixed second differences of a bump.**  For all `μ, ν` (equal or not),
`|b(x + e_μ + e_ν) - b(x + e_μ) - b(x + e_ν) + b(x)| ≤ 22500 · 4^d / (L^m)²`. -/
theorem bump_sq_diff {m : ℕ} (hm : m ≤ k) (hlam : 2 ≤ L ^ m) (y0 x : Torus d (N₀ * L ^ k))
    (μ ν : Fin d) :
    |bump m y0 (x + Pi.single μ 1 + Pi.single ν 1) - bump m y0 (x + Pi.single μ 1) -
        bump m y0 (x + Pi.single ν 1) + bump m y0 x| ≤
      22500 * 4 ^ d / ((L : ℝ) ^ m) ^ 2 := by
  have hlam' : (2 : ℝ) ≤ (L : ℝ) ^ m := by exact_mod_cast hlam
  have hlam0 : (0 : ℝ) < (L : ℝ) ^ m := by linarith
  by_cases hμν : μ = ν
  · subst hμν
    rw [bump_sq_eq]
    obtain ⟨-, -, h3⟩ := perFac_diff hm hlam y0 μ (((x μ).val : ℝ) + 1)
    have e : perFac m y0 μ (((x μ).val : ℝ) + 1 + 1) + perFac m y0 μ (((x μ).val : ℝ) + 1 - 1) -
        2 * perFac m y0 μ (((x μ).val : ℝ) + 1) =
        perFac m y0 μ (((x μ).val : ℝ) + 2) - 2 * perFac m y0 μ (((x μ).val : ℝ) + 1) +
          perFac m y0 μ ((x μ).val : ℝ) := by
      have a1 : ((x μ).val : ℝ) + 1 + 1 = ((x μ).val : ℝ) + 2 := by ring
      have a2 : ((x μ).val : ℝ) + 1 - 1 = ((x μ).val : ℝ) := by ring
      rw [a1, a2]; ring
    rw [e] at h3
    have hR0 := rest_nonneg hm y0 x μ
    have hR1 := rest_le hm y0 x μ
    rw [abs_mul, abs_of_nonneg hR0]
    have hsq : (1 : ℝ) ≤ ((L : ℝ) ^ m) ^ 2 := by nlinarith
    calc _ ≤ 20 / ((L : ℝ) ^ m) ^ 2 * 4 ^ d := mul_le_mul h3 hR1 hR0 (by positivity)
      _ ≤ 22500 * 4 ^ d / ((L : ℝ) ^ m) ^ 2 := by
        rw [div_mul_eq_mul_div]
        refine div_le_div_of_nonneg_right ?_ (by positivity)
        have : (0 : ℝ) ≤ 4 ^ d := by positivity
        nlinarith
  · rw [bump_sq_ne m y0 x hμν]
    obtain ⟨h1, -, -⟩ := perFac_diff hm hlam y0 μ ((x μ).val : ℝ)
    obtain ⟨h2, -, -⟩ := perFac_diff hm hlam y0 ν ((x ν).val : ℝ)
    have hR0 := rest2_nonneg hm y0 x μ ν
    have hR1 := rest2_le hm y0 x μ ν
    rw [abs_mul, abs_mul, abs_of_nonneg hR0]
    have hp : |perFac m y0 μ (((x μ).val : ℝ) + 1) - perFac m y0 μ ((x μ).val : ℝ)| *
        |perFac m y0 ν (((x ν).val : ℝ) + 1) - perFac m y0 ν ((x ν).val : ℝ)| ≤
        150 / (L : ℝ) ^ m * (150 / (L : ℝ) ^ m) :=
      mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
    calc _ ≤ 150 / (L : ℝ) ^ m * (150 / (L : ℝ) ^ m) * 4 ^ d :=
          mul_le_mul hp hR1 hR0 (by positivity)
      _ = 22500 * 4 ^ d / ((L : ℝ) ^ m) ^ 2 := by field_simp; norm_num

end Balaban.Background
