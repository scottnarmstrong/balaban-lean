/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.HatSetGeom
public import Balaban.Fluctuation.LocalPairCast
public import Balaban.Fluctuation.LocalPairDepth
public import Balaban.Inhabited.LevelPairGeneral

/-!
# The local sets `𝔹_{k+1}(Ŷ)` of the new level (route R-LOC, L5; ruling R13)

The family of the new level is recomputed on the cast local set of the label polymer
`Y⁺(T′)`; under ruling R13 the generating set of a polymer `Y` of the new level is the local set
`𝔹_{k+1}(Ŷ)` of its thickening `Ŷ = hatSet m₀ (k + 1) Y` (`HatSpec`), read on the torus of the cube
exponent `s = hatScale L m₁ ϱ`.

* `exists_minSep_rhoSepG`, `two_le_hatScale_rhoSepG`: at the separation `ϱ = rhoSepG d L m₁` of the
  step the cube exponent exists and is at least `2` (so `m₁ + 2 ≤ m₁ + s`, the room of the read
  margin of L5);
* `hatLocal_margin`: when `s < m₀`, every site within `2 L^{k+1+m₁+s}` of a site of `Y` lies in the
  top layer of the cast local set `castG hc (𝔹_{k+1}(Ŷ))` (the hypothesis `hmarg` of
  `NewLevelSystem.localFamily_castLocal_of`).
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Fluctuation Balaban.Multiscale Balaban.Background Balaban.Localization
  Balaban.SmallField Balaban.SmallField.GsSpec Balaban.LargeField Balaban.Localization.LevelPair
  Balaban.Inhabited.LevelStep

section Scale

variable {d L : ℕ}

/-- **The separation of the step is reached by the cube sizes**: `rhoSepG d L m₁ ≤ 5 L L^{m₁+s}`
for some `s`. -/
theorem exists_minSep_rhoSepG (hL : 3 ≤ L) (m₁ : ℕ) :
    ∃ s : ℕ, rhoSepG d L m₁ ≤ LargeField.minSep L (L ^ (m₁ + s)) := by
  refine ⟨⌈rhoSepG d L m₁⌉₊, ?_⟩
  unfold LargeField.minSep
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast (by omega : 1 ≤ L)
  have h1 : rhoSepG d L m₁ ≤ (⌈rhoSepG d L m₁⌉₊ : ℝ) := Nat.le_ceil _
  have h2 : ((⌈rhoSepG d L m₁⌉₊ : ℕ) : ℝ) ≤ ((L ^ (m₁ + ⌈rhoSepG d L m₁⌉₊) : ℕ) : ℝ) := by
    exact_mod_cast (Nat.lt_pow_self (by omega : 1 < L)).le.trans
      (Nat.pow_le_pow_right (by omega) (Nat.le_add_left _ _))
  have h3 : ((L ^ (m₁ + ⌈rhoSepG d L m₁⌉₊) : ℕ) : ℝ) ≤
      5 * (L : ℝ) * ((L ^ (m₁ + ⌈rhoSepG d L m₁⌉₊) : ℕ) : ℝ) := by
    have : (0 : ℝ) ≤ ((L ^ (m₁ + ⌈rhoSepG d L m₁⌉₊) : ℕ) : ℝ) := by positivity
    nlinarith
  linarith

/-- **The cube exponent of the separation of the step is at least `2`**: the cubes of side
`L^{m₁+s}`, `s ≤ 1`, are too small for `rhoSepG d L m₁ > 4 d L³ L^{m₁}`. -/
theorem two_le_hatScale_rhoSepG (hd : 3 ≤ d) (hL : 3 ≤ L) (m₁ : ℕ) :
    2 ≤ hatScale L m₁ (rhoSepG d L m₁) := by
  classical
  obtain ⟨s₀, hs₀⟩ := exists_minSep_rhoSepG (d := d) hL m₁
  have h : ∃ s : ℕ, rhoSepG d L m₁ ≤ LargeField.minSep L (L ^ (m₁ + s)) := ⟨s₀, hs₀⟩
  unfold hatScale
  rw [dite_eq_left_of_eq_true (eq_true h)]
  refine (Nat.le_find_iff h 2).2 fun s hs hle => ?_
  unfold LargeField.minSep at hle
  have hL3 : (3 : ℝ) ≤ L := by exact_mod_cast hL
  have hd3 : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hLm : (0 : ℝ) < (L : ℝ) ^ m₁ := by positivity
  have hpow : ((L ^ (m₁ + s) : ℕ) : ℝ) ≤ (L : ℝ) * (L : ℝ) ^ m₁ := by
    have : L ^ (m₁ + s) ≤ L ^ (m₁ + 1) := Nat.pow_le_pow_right (by omega) (by omega)
    calc ((L ^ (m₁ + s) : ℕ) : ℝ) ≤ ((L ^ (m₁ + 1) : ℕ) : ℝ) := by exact_mod_cast this
      _ = (L : ℝ) * (L : ℝ) ^ m₁ := by push_cast; ring
  have hρ : 4 * (d : ℝ) * (L : ℝ) ^ 3 * (L : ℝ) ^ m₁ < rhoSepG d L m₁ := by
    have := rhoSepG_tail_nonneg hd hL
    have := (rhoSepG_terms_nonneg (m₁ := m₁) hd hL).1
    have := bgR0_nonneg_G (d := d) (L := L)
    unfold rhoSepG; linarith
  have h5 : 5 * (L : ℝ) * ((L ^ (m₁ + s) : ℕ) : ℝ) ≤ 5 * (L : ℝ) * ((L : ℝ) * (L : ℝ) ^ m₁) :=
    mul_le_mul_of_nonneg_left hpow (by positivity)
  have h6 : 5 * (L : ℝ) * ((L : ℝ) * (L : ℝ) ^ m₁) < 4 * (d : ℝ) * (L : ℝ) ^ 3 * (L : ℝ) ^ m₁ := by
    have hL2 : (0 : ℝ) < (L : ℝ) ^ 2 := by positivity
    have h7 : (5 : ℝ) < 4 * d * L := by nlinarith
    have h8 : 5 * (L : ℝ) ^ 2 < 4 * (d : ℝ) * (L : ℝ) ^ 3 := by
      have := mul_lt_mul_of_pos_left h7 hL2
      calc 5 * (L : ℝ) ^ 2 = (L : ℝ) ^ 2 * 5 := by ring
        _ < (L : ℝ) ^ 2 * (4 * d * L) := this
        _ = 4 * (d : ℝ) * (L : ℝ) ^ 3 := by ring
    calc 5 * (L : ℝ) * ((L : ℝ) * (L : ℝ) ^ m₁) = (5 * (L : ℝ) ^ 2) * (L : ℝ) ^ m₁ := by ring
      _ < (4 * (d : ℝ) * (L : ℝ) ^ 3) * (L : ℝ) ^ m₁ := mul_lt_mul_of_pos_right h8 hLm
  linarith

end Scale

section Margin

variable {d L N₁ m₁ k : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}

/-- **The read margin of the local set of the thickening**: for `s < m₀` and `L ≥ 3`, every site
within sup-distance `2 L^{k+1+m₁+s}` of a site of `Y` lies in the top layer of
`castG hc (𝔹_{k+1}(Ŷ))`, `Ŷ = hatSet m₀ (k + 1) Y` read on the torus `(N₁', m₁ + s)`: the cell of
side `L^{k+1+m₁+s}` of such a site lies within `3 L^{k+1+m₁+s} ≤ L^{k+1+m₀+m₁}` of `Y`. -/
theorem hatLocal_margin {m₀ s : ℕ} (hs : s < m₀) (hL : 3 ≤ L) {N₁' : ℕ} [NeZero N₁']
    (hc : N₁' * L ^ (m₁ + s) = N₁ * L ^ m₁) (hsep : ϱ ≤ LargeField.minSep L (L ^ (m₁ + s)))
    {Y R : Set (CTorus d L N₁ m₁ (k + 1))} (hRY : R ⊆ Y) :
    ∀ x ∈ R, ∀ y : CTorus d L N₁ m₁ (k + 1), supDist x y ≤ 2 * L ^ (k + 1 + (m₁ + s)) →
      y ∈ (castG hc (localB (k + 1) (le_refl (k + 1))
        {x' : CTorus d L N₁' (m₁ + s) (k + 1) |
          (torusCast x' : CTorus d L N₁ m₁ (k + 1)) ∈ hatSet m₀ (k + 1) Y} hsep)).Ω (k + 1) := by
  intro x hx y hy
  have hceq : N₁ * L ^ m₁ * L ^ (k + 1) = N₁' * L ^ (m₁ + s) * L ^ (k + 1) := by rw [hc]
  rw [castG_localB_top_sameCell hc le_rfl _ hsep]
  intro w hw
  show (torusCast (torusCast w : CTorus d L N₁' (m₁ + s) (k + 1)) : CTorus d L N₁ m₁ (k + 1)) ∈
    hatSet m₀ (k + 1) Y
  rw [torusCast_torusCast hceq]
  refine mem_hatSet_of_supDist_le (by omega) (hRY hx) ?_
  have hpos : 0 < L ^ (k + 1 + (m₁ + s)) := pow_pos (by omega) _
  have h1 := supDist_le_of_sameCell hpos hw
  have h2 := supDist_triangle w y x
  rw [supDist_comm y x] at h2
  have h3 : 3 * L ^ (k + 1 + (m₁ + s)) ≤ cellSide L m₀ m₁ (k + 1) := by
    unfold cellSide
    calc 3 * L ^ (k + 1 + (m₁ + s)) ≤ L * L ^ (k + 1 + (m₁ + s)) := Nat.mul_le_mul_right _ hL
      _ = L ^ (k + 1 + (m₁ + s) + 1) := by ring
      _ ≤ L ^ (k + 1 + m₀ + m₁) := Nat.pow_le_pow_right (by omega) (by omega)
  omega

end Margin

end Balaban.Inhabited
