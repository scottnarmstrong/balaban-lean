/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Correlations.Agreement

/-!
# Tails of the polymer sums (CORRELATIONS.md, Lemma 4.2)

Conditional on the clauses of Root-F; consumed by the Root-C provider.  Polymers through a point
`x` that leave the box `boxT d R ℓ` have at least `K + 1` blocks if `R = s_J K + X₀ + 1`
(Lemma 1.2), and the contribution of the polymers with at least `K + 1` blocks is at most
`2 c₉ L^{-jθ} (1/2)^{K+1}` for the terms `T` (`norm_tail_sum_le`) and `8 c₉ L^{-jθ} (1/2)^{K+1}`
for the two-point summands (`norm_tail_dsum_le`).
-/

@[expose] public section

open scoped Classical

namespace Balaban.Correlations

open Balaban Finset

variable {d N L M kf : ℕ} {β ν : ℝ} {h : EuclideanSpace ℝ (Fin N)} {κ c₉ δ : ℝ}
  {T : RootFFamily d N} {ℓ : ℕ} [NeZero ℓ]

theorem norm_tail_sum_le (hcl : RootFTorusClauses d N L M β ν h kf κ c₉ δ T ℓ)
    (hdiv : M * L ^ (kf + 1) ∣ ℓ) (hd : 1 ≤ d) (hc₉ : 0 ≤ c₉) (hκ : kappaStar d ≤ κ) {j : ℕ}
    (hj : j ∈ Finset.Icc 1 (kf + 1)) (x : Torus d ℓ) (i : Fin N) (K : ℕ)
    (F : Finset (Finset (Torus d ℓ)))
    (hF : ∀ X ∈ F, IsPolymer d ℓ (M * L ^ j) X → x ∈ X →
      K + 1 ≤ blockNumber d (M * L ^ j) X) :
    ‖∑ X ∈ F, T ℓ j x X 0 i‖ ≤
      2 * (c₉ * (L : ℝ) ^ (-((j : ℝ) * (((d : ℝ) - 2) / 2 + δ)))) * (1 / 2) ^ (K + 1) := by
  obtain ⟨m, hm, hmz⟩ := scale_dvd (ℓ := ℓ) hdiv hj
  set P' := (polymersAt d ℓ (M * L ^ j) x).filter (fun X => K + 1 ≤ blockNumber d (M * L ^ j) X)
    with hP'
  set r : ℝ := Real.exp (-κ) with hr
  set c : ℝ := c₉ * (L : ℝ) ^ (-((j : ℝ) * (((d : ℝ) - 2) / 2 + δ))) with hc
  have hc0 : 0 ≤ c := mul_nonneg hc₉ (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  calc ‖∑ X ∈ F, T ℓ j x X 0 i‖ ≤ ∑ X ∈ F, ‖T ℓ j x X 0 i‖ := norm_sum_le _ _
    _ = ∑ X ∈ F.filter (fun X => X ∈ P'), ‖T ℓ j x X 0 i‖ := by
        symm
        refine Finset.sum_filter_of_ne fun X hX hne => ?_
        by_contra hXP
        apply hne
        have : ¬ (j ∈ Finset.Icc 1 (kf + 1) ∧ x ∈ X ∧ IsPolymer d ℓ (M * L ^ j) X) := by
          rintro ⟨-, hxX, hp⟩
          exact hXP (by
            rw [hP', mem_filter, mem_polymersAt]
            exact ⟨⟨hp, hxX⟩, hF X hX hp hxX⟩)
        rw [term_zero_eq_zero_of_not hcl this i, norm_zero]
    _ ≤ ∑ X ∈ F.filter (fun X => X ∈ P'), c * r ^ blockNumber d (M * L ^ j) X := by
        refine sum_le_sum fun X hX => ?_
        rw [mem_filter, hP', mem_filter, mem_polymersAt] at hX
        refine (norm_term_zero_le hcl hj x X i).trans (le_of_eq ?_)
        have := exp_card_div_eq hm hX.2.1.1 κ
        push_cast at this
        rw [this, hc, hr, ← exp_neg_mul_pow]
    _ ≤ ∑ X ∈ P', c * r ^ blockNumber d (M * L ^ j) X := by
        refine sum_le_sum_of_subset_of_nonneg ?_ fun X _ _ => mul_nonneg hc0 (pow_nonneg
          (Real.exp_nonneg _) _)
        intro X hX
        exact (mem_filter.1 hX).2
    _ = c * ∑ X ∈ P', r ^ blockNumber d (M * L ^ j) X := by rw [mul_sum]
    _ ≤ c * (2 * (1 / 2) ^ (K + 1)) := by
        refine mul_le_mul_of_nonneg_left ?_ hc0
        exact sum_polymersAt_pow_tail_le hm hd x (K + 1) (Real.exp_nonneg _)
          (by simpa using ratio_le_half hd hκ (t := 1) (by norm_num))
    _ = _ := by ring

theorem norm_tail_dsum_le (hcl : RootFTorusClauses d N L M β ν h kf κ c₉ δ T ℓ)
    (hdiv : M * L ^ (kf + 1) ∣ ℓ) (hd : 1 ≤ d) (hc₉ : 0 ≤ c₉) (hκ : kappaStar d ≤ κ) {j : ℕ}
    (hj : j ∈ Finset.Icc 1 (kf + 1)) (x y : Torus d ℓ) (i k : Fin N) (K : ℕ)
    (F : Finset (Finset (Torus d ℓ)))
    (hF : ∀ X ∈ F, IsPolymer d ℓ (M * L ^ j) X → x ∈ X → y ∈ X →
      K + 1 ≤ blockNumber d (M * L ^ j) X) :
    ‖∑ X ∈ F, dsum T ℓ j x y i k X‖ ≤
      8 * (c₉ * (L : ℝ) ^ (-((j : ℝ) * (((d : ℝ) - 2) / 2 + δ)))) * (1 / 2) ^ (K + 1) := by
  obtain ⟨m, hm, hmz⟩ := scale_dvd (ℓ := ℓ) hdiv hj
  set P' := (polymersAt d ℓ (M * L ^ j) x).filter (fun X => K + 1 ≤ blockNumber d (M * L ^ j) X)
    with hP'
  set r : ℝ := Real.exp (-κ) with hr
  set c : ℝ := c₉ * (L : ℝ) ^ (-((j : ℝ) * (((d : ℝ) - 2) / 2 + δ))) with hc
  have hc0 : 0 ≤ c := mul_nonneg hc₉ (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  calc ‖∑ X ∈ F, dsum T ℓ j x y i k X‖ ≤ ∑ X ∈ F, ‖dsum T ℓ j x y i k X‖ := norm_sum_le _ _
    _ = ∑ X ∈ F.filter (fun X => X ∈ P'), ‖dsum T ℓ j x y i k X‖ := by
        symm
        refine Finset.sum_filter_of_ne fun X hX hne => ?_
        by_contra hXP
        apply hne
        have : ¬ (IsPolymer d ℓ (M * L ^ j) X ∧ x ∈ X ∧ y ∈ X) := by
          rintro ⟨hp, hxX, hyX⟩
          exact hXP (by
            rw [hP', mem_filter, mem_polymersAt]
            exact ⟨⟨hp, hxX⟩, hF X hX hp hxX hyX⟩)
        rw [dsum_eq_zero hcl this i k, norm_zero]
    _ ≤ ∑ X ∈ F.filter (fun X => X ∈ P'), 4 * (c * r ^ blockNumber d (M * L ^ j) X) := by
        refine sum_le_sum fun X hX => ?_
        rw [mem_filter, hP', mem_filter, mem_polymersAt] at hX
        refine (norm_dsum_le hcl hj x y i k X).trans (le_of_eq ?_)
        have := exp_card_div_eq hm hX.2.1.1 κ
        push_cast at this
        rw [this, hc, hr, ← exp_neg_mul_pow]
    _ ≤ ∑ X ∈ P', 4 * (c * r ^ blockNumber d (M * L ^ j) X) := by
        refine sum_le_sum_of_subset_of_nonneg ?_ fun X _ _ => mul_nonneg (by norm_num)
          (mul_nonneg hc0 (pow_nonneg (Real.exp_nonneg _) _))
        intro X hX
        exact (mem_filter.1 hX).2
    _ = 4 * c * ∑ X ∈ P', r ^ blockNumber d (M * L ^ j) X := by
        rw [mul_sum]
        refine sum_congr rfl fun X _ => by ring
    _ ≤ 4 * c * (2 * (1 / 2) ^ (K + 1)) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact sum_polymersAt_pow_tail_le hm hd x (K + 1) (Real.exp_nonneg _)
          (by simpa using ratio_le_half hd hκ (t := 1) (by norm_num))
    _ = _ := by ring

/-- Polymers through `x` that leave the box have many blocks. -/
theorem blockNumber_ge_of_not_subset (hL : 1 ≤ L) {j : ℕ} (hj : j ∈ Finset.Icc 1 (kf + 1))
    (hdiv : M * L ^ (kf + 1) ∣ ℓ) {R K X0 : ℕ}
    (hRK : R = M * L ^ (kf + 1) * K + X0 + 1) {x : Fin d → ℤ} (hx : ∀ μ, (x μ).natAbs ≤ X0)
    {X : Finset (Torus d ℓ)} (hp : IsPolymer d ℓ (M * L ^ j) X) (hxX : embedZ ℓ x ∈ X)
    (hnot : ¬ X ⊆ boxT d R ℓ) : K + 1 ≤ blockNumber d (M * L ^ j) X := by
  obtain ⟨m, hm, hmz⟩ := scale_dvd (ℓ := ℓ) hdiv hj
  obtain ⟨u, huX, hu⟩ := Finset.not_subset.1 hnot
  obtain ⟨μ, hμ⟩ := exists_far hu
  have hdist := torusDist_add_one_le hm hp hxX huX
  have h1 : torusNorm (embedZ ℓ x μ - u μ) ≤ torusDist (embedZ ℓ x) u :=
    Finset.le_sup (f := fun μ => torusNorm (embedZ ℓ x μ - u μ)) (Finset.mem_univ μ)
  have h2 : torusNorm (u μ) ≤ torusNorm (u μ - embedZ ℓ x μ) + torusNorm (embedZ ℓ x μ) := by
    have := torusNorm_add_le (u μ - embedZ ℓ x μ) (embedZ ℓ x μ)
    rwa [sub_add_cancel] at this
  have h3 : torusNorm (u μ - embedZ ℓ x μ) = torusNorm (embedZ ℓ x μ - u μ) := by
    rw [← neg_sub, torusNorm_neg]
  have h4 : torusNorm (embedZ ℓ x μ) ≤ X0 :=
    (torusNorm_intCast_le (x μ)).trans (hx μ)
  have h5 : R ≤ torusNorm (u μ) := by
    unfold torusNorm
    have := hμ
    rw [Int.abs_eq_natAbs] at this
    exact_mod_cast this
  have hsJ : M * L ^ j ≤ M * L ^ (kf + 1) :=
    Nat.mul_le_mul_left M (Nat.pow_le_pow_right hL (Finset.mem_Icc.1 hj).2)
  by_contra hlt
  have hn : blockNumber d (M * L ^ j) X ≤ K := by omega
  have h6 : blockNumber d (M * L ^ j) X * (M * L ^ j) ≤ K * (M * L ^ (kf + 1)) :=
    Nat.mul_le_mul hn hsJ
  have h7 : K * (M * L ^ (kf + 1)) = M * L ^ (kf + 1) * K := mul_comm _ _
  rw [hRK] at h5
  linarith

end Balaban.Correlations
