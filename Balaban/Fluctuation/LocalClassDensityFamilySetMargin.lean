/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.LocalClassDensityFamilySetShift
public import Balaban.Fluctuation.ClassOldLocalGk
public import Balaban.SmallField.LocalGeneratorSource
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The margin of the local ambient set `𝔹_k(Z)` against `X₁` (`LocalClassDensityFamilySetMargin`)

For a label `τ = (j, y, X)` with covering setup `(X, 𝒦_X)` of index `m₀` on the step torus of level
`k + 1`, and a set `Z` of sites within sup-distance `ℓ₀` of `X` (`Z = X` or `X` with the cubes of
`st₊(y)`), the local generating set `𝔹_k(Z) = localB k Z` has its data sites within sup-distance
`11 L^{m₁} L^k + 1` of `Z` (`localB_dataSites_range`).  So the ball of radius `r₀ L^{m₁} L^{k+1}`
about a data site lies in `X₁ = X1 Gp m₀ j 𝒦_X` as soon as
`ℓ₀ + 11 L^{m₁} L^k + 1 + r₀ L^{m₁} L^{k+1} ≤ (L - 2) a_{k+1}` (`shift_mem_X1`).

* `hmar_localB`: the margin `hmar` of `bgSetting_localGk` for `Gk = localB k Z`;
* `hmar_localB_of_index`: the same under a condition on the index `m₀` alone;
* `index_condition_three`: at `L = d = 3`, `r₀ ≥ 4 d L³` the condition holds for `m₀ ≥ 6` (`Z = X`).
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Localization Balaban.Multiscale Balaban.Background Balaban.SmallField
  Balaban.SmallField.GsSpec Balaban.LargeField Finset

section Margin

variable {d L N₁ m₁ k m₀ : ℕ} [NeZero L] [NeZero N₁] {ϱ ϱ₁ : ℝ}

/-- A site `y` with `ℓ¹` torus distance `< R` from `x` has `cycNorm (y μ - x μ) < R`. -/
theorem cycNorm_lt_of_torusDist_lt {n : ℕ} [NeZero n] {x y : Torus d n} {R : ℝ}
    (h : Green.torusDist d n x y < R) (μ : Fin d) : (cycNorm n (y μ - x μ) : ℝ) < R := by
  have h1 : ((Green.cycRep (x μ - y μ)).natAbs : ℝ) ≤ Green.torusDist d n x y := by
    unfold Green.torusDist
    exact Finset.single_le_sum (f := fun i => ((Green.cycRep (x i - y i)).natAbs : ℝ))
      (fun i _ => by positivity) (Finset.mem_univ μ)
  have h2 : cycNorm n (x μ - y μ) ≤ (Green.cycRep (x μ - y μ)).natAbs := by
    rw [cycNorm_le_iff]
    refine ⟨Green.cycRep (x μ - y μ), ?_, Green.cast_cycRep _⟩
    simp
  have h3 : (cycNorm n (x μ - y μ) : ℝ) ≤ ((Green.cycRep (x μ - y μ)).natAbs : ℝ) := by
    exact_mod_cast h2
  rw [cycNorm_sub_comm] at h3
  linarith

/-- **The chain of distances.**  Let `(X, 𝒦_X)` be a covering setup of index `m₀` and `j ≤ k` for the
level generating set `Gp` of level `k + 1`.  If `x` is within sup-distance `D` of `z`, `z` within `ℓ₀`
of `w ∈ X`, `y` within the torus distance `R` of `x`, and `ℓ₀ + D + R ≤ (L - 2) a_{k+1}`, then
`y ∈ X₁`. -/
theorem mem_X1_of_chain {Gp : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ} (hG' : IsLevel Gp (k + 1))
    (hL : 2 ≤ L) {j : ℕ} {X 𝒦X : Set (CTorus d L N₁ m₁ (k + 1))}
    (hcov : CovSetup Gp m₀ j X 𝒦X) {x z w y : CTorus d L N₁ m₁ (k + 1)} {ℓ₀ D : ℕ} {R : ℝ}
    (hxz : supDist x z ≤ D) (hzw : supDist z w ≤ ℓ₀) (hw : w ∈ X)
    (hy : Green.torusDist d ((N₁ * L ^ m₁) * L ^ (k + 1)) x y < R)
    (hr : (ℓ₀ : ℝ) + D + R ≤ (((L - 2) * cellSide L m₀ m₁ (k + 1) : ℕ) : ℝ)) :
    y ∈ X1 Gp m₀ j 𝒦X := by
  obtain ⟨q, hq, hwq⟩ := hcov.chosen.2 w hw
  have hxz' := supDist_le_iff.1 hxz
  have hzw' := supDist_le_iff.1 hzw
  have hbd : ∀ μ, cycNorm ((N₁ * L ^ m₁) * L ^ (k + 1)) (y μ - w μ) ≤
      (L - 2) * cellSide L m₀ m₁ (k + 1) := by
    intro μ
    have h1 := cycNorm_lt_of_torusDist_lt hy μ
    have h2 : cycNorm _ (y μ - w μ) ≤ cycNorm _ (y μ - x μ) + cycNorm _ (x μ - z μ) +
        cycNorm _ (z μ - w μ) := by
      exact (cycNorm_sub_le (y μ) (z μ) (w μ)).trans
        (Nat.add_le_add_right (cycNorm_sub_le (y μ) (x μ) (z μ)) _)
    have h3 : (cycNorm _ (y μ - w μ) : ℝ) ≤ cycNorm _ (y μ - x μ) + cycNorm _ (x μ - z μ) +
        cycNorm _ (z μ - w μ) := by exact_mod_cast h2
    have h4 : (cycNorm _ (x μ - z μ) : ℝ) ≤ D := by exact_mod_cast hxz' μ
    have h5 : (cycNorm _ (z μ - w μ) : ℝ) ≤ ℓ₀ := by exact_mod_cast hzw' μ
    have : (cycNorm _ (y μ - w μ) : ℝ) ≤ (((L - 2) * cellSide L m₀ m₁ (k + 1) : ℕ) : ℝ) := by
      linarith
    exact_mod_cast this
  have hv : ∀ μ, ∃ t : ℤ, |t| ≤ (((L - 2) * cellSide L m₀ m₁ (k + 1) : ℕ) : ℤ) ∧
      (t : ZMod ((N₁ * L ^ m₁) * L ^ (k + 1))) = y μ - w μ := fun μ =>
    (cycNorm_le_iff _ _).1 (hbd μ)
  choose v hv1 hv2 using hv
  have hyw : y = w + (intTorus v : CTorus d L N₁ m₁ (k + 1)) := by
    funext μ
    simp only [Pi.add_apply, intTorus_apply, hv2]
    ring
  rw [hyw]
  exact shift_mem_X1 hG' hcov.hN hL (by have := hcov.hjK; omega) hq hwq v hv1

/-- **The margin `hmar` for `Gk = 𝔹_k(Z)`** (P3 (4.8): `X₀^{~r₀} ⊂ X₁`).  Let `(X, 𝒦_X)` be a covering
setup of index `m₀` and `j ≤ k` for the level generating set `Gp` of level `k + 1`, `Z` a set of sites
within sup-distance `ℓ₀` of `X`, and
`ℓ₀ + 11 L^{m₁} L^k + 1 + r₀ L^{m₁} L^{k+1} ≤ (L - 2) a_{k+1}`.  Then every site within the
distance `r₀ L^{m₁} L^{k+1}` of a data site of `𝔹_k(Z)` lies in `X₁`. -/
theorem hmar_localB {Gp : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ} (hG' : IsLevel Gp (k + 1))
    (hL : 2 ≤ L) {j : ℕ} {X 𝒦X : Set (CTorus d L N₁ m₁ (k + 1))}
    (hcov : CovSetup Gp m₀ j X 𝒦X) {Z : Set (CTorus d L N₁ m₁ (k + 1))} {ℓ₀ : ℕ}
    (hZ : ∀ z ∈ Z, ∃ w ∈ X, supDist z w ≤ ℓ₀) {r₀ : ℝ}
    (hr : (ℓ₀ : ℝ) + 11 * (L : ℝ) ^ m₁ * (L : ℝ) ^ k + 1 + r₀ * (L : ℝ) ^ m₁ * (L : ℝ) ^ (k + 1) ≤
      (((L - 2) * cellSide L m₀ m₁ (k + 1) : ℕ) : ℝ))
    (hsep : ϱ₁ ≤ minSep L (L ^ m₁)) :
    ∀ x ∈ dataSites (localB k (Nat.le_succ k) Z hsep), ∀ y : CTorus d L N₁ m₁ (k + 1),
      Green.torusDist d ((N₁ * L ^ m₁) * L ^ (k + 1)) x y <
        r₀ * (L : ℝ) ^ m₁ * (L : ℝ) ^ (k + 1) → y ∈ X1 Gp m₀ j 𝒦X := by
  intro x hx y hy
  obtain ⟨z, hz, hxz⟩ := localB_dataSites_range (j := k) hL hx
  obtain ⟨w, hwX, hzw⟩ := hZ z hz
  refine mem_X1_of_chain hG' hL hcov hxz hzw hwX hy ?_
  push_cast at hr ⊢
  linarith

omit [NeZero L] in
/-- **The margin condition in terms of the index `m₀`.**  If `ℓ₀ ≤ c L^{m₁+k}` and
`c + 12 + r₀ L ≤ (L - 2) L^{m₀+1}`, the numerical hypothesis of `hmar_localB` holds. -/
theorem margin_arith_of_index (hL : 2 ≤ L) {ℓ₀ c : ℕ} {r₀ : ℝ}
    (hℓ : ℓ₀ ≤ L ^ (m₁ + k) * c)
    (hm : (c : ℝ) + 12 + r₀ * L ≤ (((L - 2 : ℕ)) : ℝ) * (L : ℝ) ^ (m₀ + 1)) :
    (ℓ₀ : ℝ) + 11 * (L : ℝ) ^ m₁ * (L : ℝ) ^ k + 1 + r₀ * (L : ℝ) ^ m₁ * (L : ℝ) ^ (k + 1) ≤
      (((L - 2) * cellSide L m₀ m₁ (k + 1) : ℕ) : ℝ) := by
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast (by omega : 1 ≤ L)
  have hP : (1 : ℝ) ≤ (L : ℝ) ^ k := one_le_pow₀ hL1
  have hQ : (0 : ℝ) < (L : ℝ) ^ m₁ := by positivity
  have hℓ' : (ℓ₀ : ℝ) ≤ (L : ℝ) ^ (m₁ + k) * c := by exact_mod_cast hℓ
  have hpk : (L : ℝ) ^ (m₁ + k) = (L : ℝ) ^ m₁ * (L : ℝ) ^ k := pow_add _ _ _
  have hcs : (((L - 2) * cellSide L m₀ m₁ (k + 1) : ℕ) : ℝ) =
      (((L - 2 : ℕ)) : ℝ) * ((L : ℝ) ^ (m₁ + k) * (L : ℝ) ^ (m₀ + 1)) := by
    unfold cellSide
    push_cast
    rw [← pow_add]
    congr 2
    ring
  have hpos : (0 : ℝ) < (L : ℝ) ^ (m₁ + k) := by positivity
  have h1 : (L : ℝ) ^ (m₁ + k) * ((c : ℝ) + 12 + r₀ * L) ≤
      (L : ℝ) ^ (m₁ + k) * ((((L - 2 : ℕ)) : ℝ) * (L : ℝ) ^ (m₀ + 1)) :=
    mul_le_mul_of_nonneg_left hm hpos.le
  have h2 : (1 : ℝ) ≤ (L : ℝ) ^ (m₁ + k) := one_le_pow₀ hL1
  have h3 : (L : ℝ) ^ (k + 1) = (L : ℝ) ^ k * L := pow_succ _ _
  rw [hcs]
  have e1 : r₀ * (L : ℝ) ^ m₁ * (L : ℝ) ^ (k + 1) = (L : ℝ) ^ (m₁ + k) * (r₀ * L) := by
    rw [hpk, h3]; ring
  have e2 : 11 * (L : ℝ) ^ m₁ * (L : ℝ) ^ k = 11 * (L : ℝ) ^ (m₁ + k) := by rw [hpk]; ring
  rw [e1, e2]
  nlinarith

/-- **`hmar_localB` under a condition on the index alone** (`Z` within `c L^{m₁+k}` of `X`). -/
theorem hmar_localB_of_index {Gp : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
    (hG' : IsLevel Gp (k + 1)) (hL : 2 ≤ L) {j : ℕ} {X 𝒦X : Set (CTorus d L N₁ m₁ (k + 1))}
    (hcov : CovSetup Gp m₀ j X 𝒦X) {Z : Set (CTorus d L N₁ m₁ (k + 1))} {ℓ₀ c : ℕ}
    (hZ : ∀ z ∈ Z, ∃ w ∈ X, supDist z w ≤ ℓ₀) (hℓ : ℓ₀ ≤ L ^ (m₁ + k) * c) {r₀ : ℝ}
    (hm : (c : ℝ) + 12 + r₀ * L ≤ (((L - 2 : ℕ)) : ℝ) * (L : ℝ) ^ (m₀ + 1))
    (hsep : ϱ₁ ≤ minSep L (L ^ m₁)) :
    ∀ x ∈ dataSites (localB k (Nat.le_succ k) Z hsep), ∀ y : CTorus d L N₁ m₁ (k + 1),
      Green.torusDist d ((N₁ * L ^ m₁) * L ^ (k + 1)) x y <
        r₀ * (L : ℝ) ^ m₁ * (L : ℝ) ^ (k + 1) → y ∈ X1 Gp m₀ j 𝒦X :=
  hmar_localB hG' hL hcov hZ (margin_arith_of_index hL hℓ hm) hsep

/-- **At `L = 3` the index condition holds for `m₀ ≥ 6`** when `r₀ ≤ 324 = 4 d L³` (`d = 3`) and
`Z = X` (`c = 0`).  For `r₀ ≥ 4 d L³` and `m₀ = 5` it fails (`12 + 972 > 2 · 3^6 / 2`). -/
theorem index_condition_three {m₀ : ℕ} (hm : 6 ≤ m₀) {r₀ : ℝ} (hr : r₀ ≤ 324) :
    ((0 : ℕ) : ℝ) + 12 + r₀ * ((3 : ℕ) : ℝ) ≤ (((3 - 2 : ℕ)) : ℝ) * ((3 : ℕ) : ℝ) ^ (m₀ + 1) := by
  have h : ((3 : ℕ) : ℝ) ^ 7 ≤ ((3 : ℕ) : ℝ) ^ (m₀ + 1) :=
    pow_le_pow_right₀ (by norm_num) (by omega)
  norm_num at h ⊢
  linarith

end Margin

end Balaban.Fluctuation
