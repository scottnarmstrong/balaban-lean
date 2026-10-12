/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.P6PairHalo
public import Balaban.Localization.P6PairCover
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Sup-separation of `F♯` (VMOD-11 §1.1-§1.2)

The minimal generating sets of P3 are separated in the sup metric of the cube indices; `F♯` adds the
halo `A` at sup-distance `> 5 L M₁ ℓ_k` from `Wᶜ` (`p6_halo_far_sup`).  Hence `F♯` satisfies
`SupSep` (`p6_fsharp_supSep`), which is what the cover estimates of `P6PairCover.lean` need.
-/

@[expose] public section

namespace Balaban.LargeField

open Balaban Balaban.Multiscale Balaban.Localization

set_option linter.unusedSectionVars false

variable {d M1 N₁ L q : ℕ} [NeZero L] [NeZero M1] [NeZero N₁]

/-- The step of the recursion separates in the sup metric: a site outside `nearStep n A` is at
sup-distance `> 5 L M₁ L^n` from every site of `A`. -/
theorem supDist_gt_of_not_mem_nearStep {n : ℕ} (hn : n ≤ q)
    {A : Finset (Torus d (M1 * N₁ * L ^ q))} {x y : Torus d (M1 * N₁ * L ^ q)}
    (hx : x ∉ nearStep M1 N₁ L q n A) (hy : y ∈ A) :
    (5 * L * M1 : ℝ) * (L : ℝ) ^ n < supDist x y := by
  have h1 : 5 * L + 1 ≤ supDist (fineCubeIdx M1 N₁ L q n x) (fineCubeIdx M1 N₁ L q n y) := by
    by_contra hlt
    exact hx (mem_nearStep.2 ⟨y, hy, by omega⟩)
  have hN : 0 < L ^ n * M1 := Nat.pos_of_ne_zero (by
    have := NeZero.ne L; have := NeZero.ne M1; positivity)
  have h2 := supDist_blockMap_le (d := d) (fine_eq_cube hn) x y
  unfold fineCubeIdx at h1
  have h3 : 5 * L + 1 ≤ (supDist x y + L ^ n * M1 - 1) / (L ^ n * M1) := h1.trans h2
  rw [Nat.le_div_iff_mul_le hN] at h3
  have h4 : (5 * L + 1) * (L ^ n * M1) ≤ supDist x y + L ^ n * M1 - 1 := h3
  have h5 : 5 * L * (L ^ n * M1) < supDist x y := by
    have : (5 * L + 1) * (L ^ n * M1) = 5 * L * (L ^ n * M1) + L ^ n * M1 := by ring
    omega
  have h6 : ((5 * L * (L ^ n * M1) : ℕ) : ℝ) < (supDist x y : ℝ) := by exact_mod_cast h5
  push_cast at h6
  nlinarith [h6]

variable {n1 c k n0 : ℕ} [NeZero c] [NeZero n0] [NeZero n1]

/-- **`F♯` is sup-separated** (the hypothesis of the cover estimates of `P6PairCover.lean`):
`4 L^(j+1+m₁) < supDist x y` for `x ∉ Ω_j(F♯)`, `y ∈ Ω_{j+1}(F♯)`, `1 ≤ j ≤ k`, where `M₁ = L^m₁`. -/
theorem p6_fsharp_supSep (hn : n0 = L * n1) {ρ' : ℕ} (hρ : 3 * L ≤ ρ') (hc : 5 ≤ c)
    (Z : Set (Torus d n0)) {m₁ : ℕ} (hM1 : M1 = L ^ m₁) :
    SupSep (p6Fsharp (M1 := M1) (c := c) (L := L) (k := k) hn hρ hc Z) m₁ := by
  intro j hj1 hjK x hx y hy
  by_cases hjk : j + 1 ≤ k
  · rw [p6Fsharp_Ω_of_le hn hρ hc Z (by omega), p6Hold_Ω] at hx
    rw [p6Fsharp_Ω_of_le hn hρ hc Z hjk, p6Hold_Ω] at hy
    rw [minLayer_of_lt _ (by omega : j < k)] at hx
    have h := supDist_gt_of_not_mem_nearStep (q := k + 1) (by omega : j ≤ k + 1) hx hy
    have e : (5 * L * M1 : ℝ) * (L : ℝ) ^ j = 5 * (L : ℝ) ^ (j + 1 + m₁) := by
      rw [hM1]; push_cast; ring
    have hpos : (0 : ℝ) < (L : ℝ) ^ (j + 1 + m₁) := by
      have : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
      positivity
    rw [e] at h
    linarith
  · have hjk' : j = k := by omega
    subst hjk'
    rw [p6Fsharp_Ω_of_le hn hρ hc Z le_rfl, p6Hold_Ω_k hn] at hx
    rw [p6Fsharp_Ω_top] at hy
    have h := p6_halo_far_sup (M1 := M1) (c := c) hn (by omega) Z hx hy
    -- `P₀ (ρ' + 3 - 2L) + 1 ≤ s + P₀`, `P₀ = L^j c M₁`
    set s := supDist x y with hs
    set a := L ^ j * M1 with ha
    have hP0 : L ^ j * (c * M1) = c * a := by rw [ha]; ring
    rw [hP0] at h
    have h1 : c * a * (L + 3) ≤ c * a * (ρ' + 3 - 2 * L) :=
      Nat.mul_le_mul_left _ (by omega)
    have h2 : 5 * a * (L + 2) ≤ c * a * (L + 2) := by
      have : 5 * a ≤ c * a := Nat.mul_le_mul_right _ hc
      exact Nat.mul_le_mul_right _ this
    have h3 : c * a * (L + 3) = c * a * (L + 2) + c * a := by ring
    have h4 : 4 * a * L < s := by
      have : 4 * a * L < 5 * a * (L + 2) + 1 := by
        have hapos : 0 < a := Nat.pos_of_ne_zero (by
          rw [ha]; have := NeZero.ne L; have := NeZero.ne M1; positivity)
        nlinarith
      omega
    have h5 : ((4 * a * L : ℕ) : ℝ) < (s : ℝ) := by exact_mod_cast h4
    have e : (L : ℝ) ^ (j + 1 + m₁) = (a : ℝ) * L := by
      rw [ha, hM1]; push_cast; ring
    rw [e]
    push_cast at h5
    linarith

end Balaban.LargeField
