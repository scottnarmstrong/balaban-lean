/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.SmallField.Def6

/-!
# Def-6: the tori of the stabilizing sequence

`eventually_nonWind`: a finite set `X' ⊆ ℤ^d` of `j`-blocks does not wind around the tori
`torusSeq` from some torus on.
-/


@[expose] public section

namespace Balaban.SmallField.Def6

open Balaban Filter

variable {d L m₁ k : ℕ} [NeZero L]

omit [NeZero L] in
theorem torusSeq_dvd (m₀ n : ℕ) : L ^ m₀ ∣ torusSeq L m₀ n := Dvd.intro _ rfl

theorem succ_le_torusSeq (m₀ n : ℕ) : n + 1 ≤ torusSeq L m₀ n := by
  unfold torusSeq
  have : 1 ≤ L ^ m₀ := Nat.one_le_pow _ _ (Nat.pos_of_ne_zero (NeZero.ne L))
  nlinarith

theorem torusSeq_le_side (m₀ n j : ℕ) :
    torusSeq L m₀ n ≤ torusSeq L m₀ n * L ^ m₁ * L ^ (k - j) := by
  have h1 : 1 ≤ L ^ m₁ := Nat.one_le_pow _ _ (Nat.pos_of_ne_zero (NeZero.ne L))
  have h2 : 1 ≤ L ^ (k - j) := Nat.one_le_pow _ _ (Nat.pos_of_ne_zero (NeZero.ne L))
  calc torusSeq L m₀ n = torusSeq L m₀ n * 1 * 1 := by ring
    _ ≤ _ := by gcongr

/-- **Eventual non-winding**: a finite set `X' ⊆ ℤ^d` of `j`-blocks does not wind around the tori
of the sequence `torusSeq`, from some torus on. -/
theorem eventually_nonWind (m₀ j : ℕ) (X' : Finset (Fin d → ℤ)) :
    ∀ᶠ n in atTop, NonWind L (torusSeq L m₀ n) m₁ k j X' := by
  unfold NonWind
  rw [Filter.eventually_all_finset]
  intro z _
  rw [Filter.eventually_all]
  intro μ
  filter_upwards [Filter.eventually_ge_atTop ((z μ).natAbs * 2)] with n hn
  have hnz : NeZero (torusSeq L m₀ n * L ^ m₁ * L ^ (k - j)) :=
    ⟨Nat.mul_ne_zero (Nat.mul_ne_zero (torusSeq_ne_zero m₀ n) (pow_ne_zero _ (NeZero.ne L)))
      (pow_ne_zero _ (NeZero.ne L))⟩
  have hR := (succ_le_torusSeq (L := L) m₀ n).trans (torusSeq_le_side (L := L) (m₁ := m₁) (k := k) m₀ n j)
  rw [ZMod.valMinAbs_spec]
  refine ⟨rfl, ?_, ?_⟩
  · have : ((z μ).natAbs : ℤ) * 2 ≤ n := by exact_mod_cast hn
    have h2 := Int.natAbs_eq (z μ)
    have h3 : (n : ℤ) + 1 ≤ ((torusSeq L m₀ n * L ^ m₁ * L ^ (k - j) : ℕ) : ℤ) := by exact_mod_cast hR
    rcases Int.natAbs_eq (z μ) with h | h <;> omega
  · have : ((z μ).natAbs : ℤ) * 2 ≤ n := by exact_mod_cast hn
    have h3 : (n : ℤ) + 1 ≤ ((torusSeq L m₀ n * L ^ m₁ * L ^ (k - j) : ℕ) : ℤ) := by exact_mod_cast hR
    rcases Int.natAbs_eq (z μ) with h | h <;> omega

/-- **`InfPoly` reduces to the polymer condition**: a finite set of blocks is a polymer of `T∞`
iff its lift is eventually a polymer of `𝒟_j` on the tori of the sequence. -/
theorem infPoly_iff (m₀ j : ℕ) (X' : Finset (Fin d → ℤ)) :
    InfPoly (L := L) (m₁ := m₁) (k := k) m₀ j X' ↔
      ∀ᶠ n in atTop, haveI : NeZero (torusSeq L m₀ n) := ⟨torusSeq_ne_zero m₀ n⟩
        IsPolyDom (L := L) (N₁ := torusSeq L m₀ n) (m₁ := m₁) (k := k) m₀ j
          (Ypoly (L := L) (N₁ := torusSeq L m₀ n) (m₁ := m₁) (k := k) j X') := by
  constructor
  · intro h
    filter_upwards [h] with n hn using hn.2
  · intro h
    filter_upwards [h, eventually_nonWind (L := L) (m₁ := m₁) (k := k) m₀ j X'] with n h1 h2
    exact ⟨h2, h1⟩

end Balaban.SmallField.Def6
