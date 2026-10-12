/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.SupportMargin
public import Balaban.Localization.DecoupledBackgroundLocal
public import Balaban.Background.Weights
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# No margin for `X₁` itself: the geometry of the counterexample (`TRUE-LOCAL.md` §1, §2)

This file proves **geometry only**; no statement about the physical terms.

* `not_psiThick_subset_X1`: `psiThick X₁ ⊄ X₁` as soon as `X₁` is nonempty and not the whole torus
  (`SupportMargin.not_psiThick_subset`).
* `exists_outside_approxDep`: in the full-level case, if `S` is a nonempty proper union of
  complete level-`K` unit blocks (for example `S = X₁`), there are a site `x ∈ S` (next to the
  outer face) and the base `q ∉ S` of an adjacent unit block with `q ∈ approxDep x` and a positive
  weight `weight (K, q) x > 0`: the approximate background field at `x` reads data outside `S`.
  The spline positivity used is `bsp_pos` (`bsp t > 0` for `|t| < 3/2`; at the face coordinate
  `t = ±(ℓ + 1)/(2ℓ)`, value `(3/2 - |t|)² / 2`).

The analytic part (the derivative of `approxField` in the data at `q`) is not attempted.
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background Balaban.Fluctuation Finset

/-- The spline `bsp` is positive on `(-3/2, 3/2)`. -/
theorem bsp_pos {t : ℝ} (h : |t| < 3 / 2) : 0 < bsp t := by
  rcases abs_lt.1 h with ⟨h1, h2⟩
  by_cases hm : |t| ≤ 1 / 2
  · exact lt_of_lt_of_le (by norm_num) (bsp_ge_half hm)
  · rcases le_or_gt 0 t with ht | ht
    · rw [bsp_right (by rw [abs_of_nonneg ht] at hm; linarith) h2.le]
      have : 0 < 3 / 2 - t := by linarith
      positivity
    · rw [bsp_left (by linarith) (by rw [abs_of_neg ht] at hm; linarith)]
      have : 0 < t + 3 / 2 := by linarith
      positivity

section Bump

variable {d L N₀ k : ℕ} [NeZero N₀] [NeZero L]

/-- If `y` lies in the block of the base `y0` and `x = y ± e_μ`, then the bump of that block is
positive at `x`: in coordinate `μ` the displacement from the block centre is at most
`(ℓ + 1)/2`, so the spline argument has modulus at most `(ℓ + 1)/(2ℓ) ≤ 1`. -/
theorem bump_pos_of_adj_block {m : ℕ} (hm : m ≤ k) {y0 y x : Torus d (N₀ * L ^ k)}
    (hb : IsBase m y0) (h : jBlock d L N₀ k m y = jBlock d L N₀ k m y0) {μ : Fin d}
    (hx : x = y + Pi.single μ 1 ∨ x = y - Pi.single μ 1) : 0 < bump m y0 x := by
  have hlam : 0 < L ^ m := pow_pos (Nat.pos_of_ne_zero (NeZero.ne L)) m
  have hlamR : (1 : ℝ) ≤ (L : ℝ) ^ m := by exact_mod_cast hlam
  have hy := bump_ge_of_jBlock_eq hm hb h
  have hyp : 0 < bump m y0 y := lt_of_lt_of_le (by positivity) hy
  have hq := val_div_eq_of_jBlock_eq hm h μ
  have h1 : (y0 μ).val = L ^ m * ((y μ).val / L ^ m) := by
    rw [hq]; exact (Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero (hb μ))).symm
  have h2 := Nat.div_mul_le_self (y μ).val (L ^ m)
  have h3 := Nat.lt_div_mul_add (a := (y μ).val) hlam
  have n1 : (y0 μ).val ≤ (y μ).val := by
    have e := mul_comm (L ^ m) ((y μ).val / L ^ m); rw [h1]; linarith
  have n2 : (y μ).val + 1 ≤ (y0 μ).val + L ^ m := by
    have e := mul_comm (L ^ m) ((y μ).val / L ^ m); rw [h1]; linarith
  have r1 : ((y0 μ).val : ℝ) ≤ ((y μ).val : ℝ) := by exact_mod_cast n1
  have r2 : ((y μ).val : ℝ) + 1 ≤ ((y0 μ).val : ℝ) + (L : ℝ) ^ m := by exact_mod_cast n2
  -- the factor in coordinate `μ` at a shifted position is positive
  have key : ∀ s : ℝ, |s| ≤ 1 → 0 < perFac m y0 μ (((y μ).val : ℝ) + s) := by
    intro s hs
    have hs' := abs_le.1 hs
    unfold perFac
    have hr := one_le_sideRatio (N₀ := N₀) (L := L) hm
    have hα : |((((y μ).val : ℝ) + s) - bumpCentre m y0 μ) / (L : ℝ) ^ m| ≤ 1 := by
      rw [abs_div, abs_of_pos (by linarith : (0 : ℝ) < (L : ℝ) ^ m), div_le_one (by linarith)]
      unfold bumpCentre
      rw [abs_le]; constructor <;> nlinarith
    exact lt_of_lt_of_le (bsp_pos (by linarith)) (bsp_le_perN (by linarith) (by linarith))
  have hrest : 0 < ∏ ν ∈ univ.erase μ, perFac m y0 ν ((y ν).val : ℝ) := by
    have e := bump_eq_mul m y0 y μ
    have hf := perFac_nonneg hm y0 μ ((y μ).val : ℝ)
    have hr := rest_nonneg hm y0 y μ
    rcases hr.lt_or_eq with hr | hr
    · exact hr
    · rw [← hr, mul_zero] at e; linarith
  rcases hx with rfl | rfl
  · rw [bump_add_one]
    have := key 1 (by simp)
    exact mul_pos this hrest
  · rw [bump_sub_one]
    have := key (-1) (by simp)
    rw [← sub_eq_add_neg] at this
    exact mul_pos this hrest

end Bump

section Example

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
variable {G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {m₀ : ℕ}

/-- **The approximate background reads outside `S`** (first step of the counterexample).
Full-level case, `S` a nonempty proper union of complete level-`K` unit blocks.  There are a
site `x ∈ S` and a site `q ∉ S` such that `(K, q)` is a block of `G`, its weight at `x` is
positive, and `q ∈ approxDep G x`. -/
theorem exists_outside_approxDep (hlev : IsLevel G K) {S : Set (CTorus d L N₁ m₁ K)}
    (hS : IsCellUnion (L ^ K) S) (hne : S.Nonempty) (hproper : S ≠ Set.univ) :
    ∃ x ∈ S, ∃ q ∉ S, (K, q) ∈ blockIdx G ∧ 0 < weight G (K, q) x ∧ q ∈ approxDep G x := by
  obtain ⟨x, hx, y, hy, μ, hxy⟩ := exists_adj_out hne hproper
  obtain ⟨hK1, hKK⟩ := hlev.bounds
  have hlayer : ∀ z, z ∈ G.layer K := fun z => by
    have := (G.layerIndex_spec (hlev z).1).2.2
    rw [(hlev z).2] at this
    exact this
  set q : CTorus d L N₁ m₁ K := ownBase K y with hqdef
  have hqblk : jBlock d L (N₁ * L ^ m₁) K K q = jBlock d L (N₁ * L ^ m₁) K K y :=
    ownBase_jBlock y
  have hqS : q ∉ S := fun hq => hy ((hS.unitBlock_iff hqblk).1 hq)
  have hblk : (K, q) ∈ blockIdx G := own_mem_blockIdx G hK1 hKK (hlayer y)
  have hxadj : x = y + Pi.single μ 1 ∨ x = y - Pi.single μ 1 := by
    rcases hxy with h | h
    · right; rw [h]; simp
    · left; exact h
  have hbump : 0 < bump K q x :=
    bump_pos_of_adj_block hKK (ownBase_isBase y) hqblk.symm hxadj
  refine ⟨x, hx, q, hqS, hblk, ?_, ?_⟩
  · unfold weight
    exact div_pos hbump (denom_pos G hK1 hKK (hlayer x))
  · unfold approxDep
    simp only [Finset.mem_insert, Finset.mem_image]
    exact Or.inr ⟨(K, q), (mem_active G).2 ⟨hblk, hbump.ne'⟩, rfl⟩

/-- For `X₁ = X1 G m₀ j 𝒦X` (nonempty, not the whole torus), full level: the approximate
background field at a site of `X₁` reads the block base `q ∉ X₁`, with positive weight. -/
theorem exists_outside_approxDep_X1 {j : ℕ} {𝒦X : Set (CTorus d L N₁ m₁ K)} (hN : L ^ m₀ ∣ N₁)
    (hlev : IsLevel G K) (hne : (X1 G m₀ j 𝒦X).Nonempty) (hproper : X1 G m₀ j 𝒦X ≠ Set.univ) :
    ∃ x ∈ X1 G m₀ j 𝒦X, ∃ q ∉ X1 G m₀ j 𝒦X, (K, q) ∈ blockIdx G ∧ 0 < weight G (K, q) x ∧
      q ∈ approxDep G x :=
  exists_outside_approxDep hlev
    ((X1_isCellUnion (G := G) (j := j) (𝒦X := 𝒦X) hN).mono_dvd (pow_dvd_pow L (by omega))) hne hproper

/-- No margin for `X₁` itself: `psiThick X₁ ⊄ X₁` when `X₁` is nonempty and not the torus. -/
theorem not_psiThick_subset_X1 {j : ℕ} {𝒦X : Set (CTorus d L N₁ m₁ K)}
    (hne : (X1 G m₀ j 𝒦X).Nonempty) (hproper : X1 G m₀ j 𝒦X ≠ Set.univ) :
    ¬ psiThick (X1 G m₀ j 𝒦X) ⊆ X1 G m₀ j 𝒦X :=
  not_psiThick_subset hne hproper

end Example

end Balaban.Localization
