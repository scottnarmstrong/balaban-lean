/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.Cover
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Torus parameters of the root

Natural-number arithmetic connecting the tori `ℓ` with `L ^ (m₀ + m₁) * L ^ J ∣ ℓ` of the root to
the step tori `CTorus d L N₁ m₁ K`, `N₁ = q * L ^ m₀ * L ^ (J - K)`, at every scale `K ≤ J`:
the torus identity, the quotient `q`, and the divisibility and size facts the step theorems use.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Localization

theorem rootTorus_eq (L m₀ m₁ J K q : ℕ) (hK : K ≤ J) :
    q * (L ^ (m₀ + m₁) * L ^ J) = (q * L ^ m₀ * L ^ (J - K) * L ^ m₁) * L ^ K := by
  obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le hK
  rw [Nat.add_sub_cancel_left]
  ring

theorem rootTorus_type_eq (d L m₀ m₁ J K q : ℕ) (hK : K ≤ J) :
    Torus d (q * (L ^ (m₀ + m₁) * L ^ J)) = CTorus d L (q * L ^ m₀ * L ^ (J - K)) m₁ K :=
  congrArg (Torus d) (rootTorus_eq L m₀ m₁ J K q hK)

theorem admissible_iff (L m₀ m₁ J ℓ : ℕ) :
    L ^ (m₀ + m₁) * L ^ J ∣ ℓ ↔ ∃ q, ℓ = q * (L ^ (m₀ + m₁) * L ^ J) := by
  constructor
  · rintro ⟨q, rfl⟩
    exact ⟨q, mul_comm _ _⟩
  · rintro ⟨q, rfl⟩
    exact ⟨q, mul_comm _ _⟩

theorem one_le_of_admissible (L m₀ m₁ J ℓ q : ℕ) (hℓ : ℓ ≠ 0)
    (hq : ℓ = q * (L ^ (m₀ + m₁) * L ^ J)) : 1 ≤ q := by
  rcases Nat.eq_zero_or_pos q with h | h
  · subst h; simp at hq; exact absurd hq hℓ
  · exact h

theorem pow_dvd_rootN₁ (L m₀ q J K : ℕ) : L ^ m₀ ∣ q * L ^ m₀ * L ^ (J - K) :=
  ⟨q * L ^ (J - K), by ring⟩

theorem rootN₁_ne_zero (L m₀ q J K : ℕ) (hL : 0 < L) (hq : 1 ≤ q) :
    NeZero (q * L ^ m₀ * L ^ (J - K)) :=
  ⟨by positivity⟩

theorem five_lt_rootN₁_of_five_lt_pow (L m₀ q J K : ℕ) (hq : 1 ≤ q) (h : 5 < L ^ m₀) :
    5 < q * L ^ m₀ * L ^ (J - K) := by
  have hL : 0 < L := by
    rcases Nat.eq_zero_or_pos L with h0 | h0
    · subst h0
      rcases Nat.eq_zero_or_pos m₀ with h1 | h1
      · subst h1; simp at h
      · simp [zero_pow h1.ne'] at h
    · exact h0
  have h1 : 1 ≤ L ^ (J - K) := Nat.one_le_pow _ _ hL
  calc 5 < L ^ m₀ := h
    _ = 1 * L ^ m₀ * 1 := by ring
    _ ≤ q * L ^ m₀ * L ^ (J - K) := Nat.mul_le_mul (Nat.mul_le_mul hq le_rfl) h1

theorem five_lt_rootN₁_of_lt (L m₀ q J K : ℕ) (hq : 1 ≤ q) (hK : K < J)
    (h : 5 < L ^ (m₀ + 1)) : 5 < q * L ^ m₀ * L ^ (J - K) := by
  have hL : 1 ≤ L := by
    rcases Nat.eq_zero_or_pos L with h0 | h0
    · subst h0; simp at h
    · exact h0
  have h1 : L ≤ L ^ (J - K) := by
    simpa using Nat.pow_le_pow_right hL (show 1 ≤ J - K by omega)
  calc 5 < L ^ (m₀ + 1) := h
    _ = 1 * L ^ m₀ * L := by ring
    _ ≤ q * L ^ m₀ * L ^ (J - K) := Nat.mul_le_mul (Nat.mul_le_mul hq le_rfl) h1

/-- At `L = 3`, `m₀ = 1`: `3 ∣ N₁`. -/
theorem three_dvd_rootN₁ (q J K : ℕ) : 3 ∣ q * 3 ^ 1 * 3 ^ (J - K) := by
  simpa using pow_dvd_rootN₁ 3 1 q J K

/-- At `L = 3`, `m₀ = 1`, `5 < N₁` exactly when not (`q = 1` and `K = J`), for `K ≤ J`, `1 ≤ q`. -/
theorem five_lt_rootN₁_three_one_iff (q J K : ℕ) (hq : 1 ≤ q) (hK : K ≤ J) :
    5 < q * 3 ^ 1 * 3 ^ (J - K) ↔ ¬ (q = 1 ∧ K = J) := by
  constructor
  · rintro h ⟨rfl, rfl⟩
    simp at h
  · intro h
    rcases Nat.lt_or_ge K J with hKJ | hKJ
    · exact five_lt_rootN₁_of_lt 3 1 q J K hq hKJ (by norm_num)
    · have hKJ' : K = J := le_antisymm hK hKJ
      subst hKJ'
      have : 2 ≤ q := by
        rcases Nat.lt_or_ge 1 q with h2 | h2
        · exact h2
        · exact absurd ⟨by omega, rfl⟩ h
      simp; omega

end Balaban.Fluctuation
