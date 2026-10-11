/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Correlations.Identity
public import Balaban.Correlations.PolymerDiameter
public import Balaban.Correlations.Series
public import Balaban.Analysis.Cauchy

/-!
# One- and two-point bounds from the clauses of Root-F (CORRELATIONS.md, Proposition 1.5)

Conditional on the clauses of Root-F; consumed by the Root-C provider.  Let
`RootFTorusClauses d N L M β ν h kf κ c₉ δ T ℓ` hold on an admissible torus
(`M L^(kf+1) ∣ ℓ`), with `κ ≥ κ* = 2 log (8 d²)`, `θ = (d-2)/2 + δ`.  Then, uniformly in `ℓ`,
`β`, `ν`, `h`:

* `abs_onePoint_sub_le`: `|⟨φ_i(x)⟩ - h_i| ≤ 3 c₉`;
* `abs_twoPointTruncated_le`: `|G_{ik}(x, y)| ≤ C c₉ (1 + d_ℓ(x,y))^{-θ} exp(-c' √ν d_ℓ(x,y))`,
  with `c' = κ / (4 M L²)` and `C` depending only on `d, L, M, δ, κ` (through `L, M`, hence on
  `c₉`).
-/

@[expose] public section

namespace Balaban.Correlations

open Balaban Finset

/-- The threshold `κ* = 2 log (8 d²)` for the polymer decay rate. -/
noncomputable def kappaStar (d : ℕ) : ℝ := 2 * Real.log (8 * (d : ℝ) ^ 2)

theorem exp_neg_half_kappaStar_mul {d : ℕ} (hd : 1 ≤ d) :
    ((2 * d : ℕ) : ℝ) ^ 2 * Real.exp (-(kappaStar d / 2)) = 1 / 2 := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  unfold kappaStar
  rw [show -(2 * Real.log (8 * (d : ℝ) ^ 2) / 2) = -Real.log (8 * (d : ℝ) ^ 2) by ring,
    Real.exp_neg, Real.exp_log (by positivity)]
  push_cast
  field_simp
  ring

theorem kappaStar_pos {d : ℕ} (hd : 1 ≤ d) : 0 < kappaStar d := by
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  unfold kappaStar
  have : (1 : ℝ) < 8 * (d : ℝ) ^ 2 := by nlinarith
  have := Real.log_pos this
  linarith

/-- For `κ ≥ κ*` and `0 ≤ t ≤ 1/2` ... the geometric ratio `(2 d)² e^{-κ t}` is at most `1/2`
when `t ≥ 1/2`. -/
theorem ratio_le_half {d : ℕ} (hd : 1 ≤ d) {κ t : ℝ} (hκ : kappaStar d ≤ κ) (ht : 1 / 2 ≤ t) :
    ((2 * d : ℕ) : ℝ) ^ 2 * Real.exp (-(κ * t)) ≤ 1 / 2 := by
  have h1 : Real.exp (-(κ * t)) ≤ Real.exp (-(kappaStar d / 2)) := by
    apply Real.exp_le_exp.2
    have := kappaStar_pos hd
    nlinarith
  calc _ ≤ ((2 * d : ℕ) : ℝ) ^ 2 * Real.exp (-(kappaStar d / 2)) := by gcongr
    _ = 1 / 2 := exp_neg_half_kappaStar_mul hd

variable {d ℓ s m : ℕ} [NeZero ℓ]

theorem one_le_blockNumber (hℓ : ℓ = s * m) [NeZero m] {X : Finset (Torus d ℓ)}
    (hX : IsPolymer d ℓ s X) : 1 ≤ blockNumber d s X := by
  rw [polymer_blockNumber_eq hℓ hX]
  exact Nat.one_le_iff_ne_zero.2 (polymer_image_connected hℓ hX).1

/-- The weighted sum over the polymers through `x`, `∑_X r^{n(X)} ≤ 1` if `(2 d)² r ≤ 1/2`. -/
theorem sum_polymersAt_pow_le_one (hℓ : ℓ = s * m) [NeZero m] (hd : 1 ≤ d) (x : Torus d ℓ)
    {r : ℝ} (hr0 : 0 ≤ r) (hr : ((2 * d : ℕ) : ℝ) ^ 2 * r ≤ 1 / 2) :
    ∑ X ∈ polymersAt d ℓ s x, r ^ blockNumber d s X ≤ 1 := by
  have h := sum_polymersAt_pow_le hℓ hd x 1 hr0 hr
  have heq : (polymersAt d ℓ s x).filter (fun X => 1 ≤ blockNumber d s X) = polymersAt d ℓ s x :=
    Finset.filter_true_of_mem fun X hX => one_le_blockNumber hℓ (mem_polymersAt.1 hX).1
  rw [heq] at h
  linarith

/-- The tail `∑_{X ∋ x, n(X) ≥ n₀} r^{n(X)} ≤ 2 (1/2)^{n₀}`, restated. -/
theorem sum_polymersAt_pow_tail_le (hℓ : ℓ = s * m) [NeZero m] (hd : 1 ≤ d) (x : Torus d ℓ)
    (n0 : ℕ) {r : ℝ} (hr0 : 0 ≤ r) (hr : ((2 * d : ℕ) : ℝ) ^ 2 * r ≤ 1 / 2) :
    ∑ X ∈ (polymersAt d ℓ s x).filter (fun X => n0 ≤ blockNumber d s X),
        r ^ blockNumber d s X ≤ 2 * (1 / 2) ^ n0 :=
  sum_polymersAt_pow_le hℓ hd x n0 hr0 hr

/-- For a polymer, `exp (-κ |X| / s^d) = exp (-κ n(X))`. -/
theorem exp_card_div_eq (hℓ : ℓ = s * m) [NeZero m] {X : Finset (Torus d ℓ)}
    (hX : IsPolymer d ℓ s X) (κ : ℝ) :
    Real.exp (-κ * (X.card : ℝ) / (s : ℝ) ^ d) = Real.exp (-κ * (blockNumber d s X : ℝ)) := by
  have hs : (0 : ℝ) < s := by exact_mod_cast pos_of_eq_mul hℓ
  congr 1
  rw [polymer_card_eq_blockNumber hℓ hX]
  push_cast
  field_simp

theorem exp_neg_mul_pow (κ : ℝ) (n : ℕ) : Real.exp (-κ * (n : ℝ)) = Real.exp (-κ) ^ n := by
  rw [← Real.exp_nat_mul]
  ring_nf

theorem sum_rpow_le_three {L : ℕ} (hL : 2 ≤ L) {θ : ℝ} (hθ : 1 / 2 ≤ θ) (J : ℕ) :
    ∑ j ∈ Finset.Icc 1 J, (L : ℝ) ^ (-((j : ℝ) * θ)) ≤ 3 := by
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast (by omega : 1 ≤ L)
  have hL2 : (2 : ℝ) ≤ L := by exact_mod_cast hL
  set q : ℝ := (L : ℝ) ^ (-θ) with hq
  have hq0 : 0 ≤ q := Real.rpow_nonneg (by linarith) _
  have hterm : ∀ j : ℕ, (L : ℝ) ^ (-((j : ℝ) * θ)) = q ^ j := by
    intro j
    rw [hq, ← Real.rpow_mul_natCast (by linarith)]
    congr 1
    ring
  have hq2 : q ^ 2 ≤ 1 / 2 := by
    rw [← hterm 2]
    have : (L : ℝ) ^ (-(((2 : ℕ) : ℝ) * θ)) ≤ (L : ℝ) ^ (-1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hL1 (by push_cast; linarith)
    rw [Real.rpow_neg_one] at this
    refine this.trans ?_
    rw [inv_eq_one_div]
    exact one_div_le_one_div_of_le (by norm_num) hL2
  have hq34 : q ≤ 3 / 4 := by
    by_contra hcon
    have hc := not_le.1 hcon
    nlinarith
  simp_rw [hterm]
  have hIcc : Finset.Icc 1 J = Finset.Ico 1 (J + 1) := by ext; simp
  rw [hIcc]
  refine (geom_sum_Ico_le_of_lt_one hq0 (by linarith)).trans ?_
  rw [pow_one, div_le_iff₀ (by linarith)]
  linarith

section OnePoint

variable {N : ℕ} {L M : ℕ} {β ν : ℝ} {h : EuclideanSpace ℝ (Fin N)} {kf : ℕ} {κ c₉ δ : ℝ}
  {T : RootFFamily d N}

theorem scale_dvd (hdiv : M * L ^ (kf + 1) ∣ ℓ) {j : ℕ} (hj : j ∈ Finset.Icc 1 (kf + 1)) :
    ∃ m : ℕ, ℓ = M * L ^ j * m ∧ NeZero m := by
  obtain ⟨m, hm⟩ := (Nat.mul_dvd_mul_left M (pow_dvd_pow L (Finset.mem_Icc.1 hj).2)).trans hdiv
  refine ⟨m, hm, ⟨?_⟩⟩
  rintro rfl
  simp at hm
  exact NeZero.ne ℓ hm

theorem norm_term_zero_le (hcl : RootFTorusClauses d N L M β ν h kf κ c₉ δ T ℓ) {j : ℕ}
    (hj : j ∈ Finset.Icc 1 (kf + 1)) (x : Torus d ℓ) (X : Finset (Torus d ℓ)) (i : Fin N) :
    ‖T ℓ j x X 0 i‖ ≤ c₉ * (L : ℝ) ^ (-((j : ℝ) * (((d : ℝ) - 2) / 2 + δ)))
      * Real.exp (-κ * (X.card : ℝ) / ((M : ℝ) * (L : ℝ) ^ j) ^ d) :=
  (norm_le_pi_norm (T ℓ j x X 0) i).trans (hcl.2.2.2.1 j hj x X 0 (by simp))

theorem term_zero_eq_zero_of_not (hcl : RootFTorusClauses d N L M β ν h kf κ c₉ δ T ℓ) {j : ℕ}
    {x : Torus d ℓ} {X : Finset (Torus d ℓ)}
    (hX : ¬ (j ∈ Finset.Icc 1 (kf + 1) ∧ x ∈ X ∧ IsPolymer d ℓ (M * L ^ j) X)) (i : Fin N) :
    T ℓ j x X 0 i = 0 := by
  rw [hcl.1 j x X hX]
  rfl

/-- The sum over all `X` reduces to the polymers through `x`. -/
theorem sum_term_eq_sum_polymersAt {j : ℕ} (x : Torus d ℓ) (f : Finset (Torus d ℓ) → ℂ)
    (hf : ∀ X, ¬ (j ∈ Finset.Icc 1 (kf + 1) ∧ x ∈ X ∧ IsPolymer d ℓ (M * L ^ j) X) → f X = 0) :
    ∑ X : Finset (Torus d ℓ), f X = ∑ X ∈ polymersAt d ℓ (M * L ^ j) x, f X := by
  symm
  refine Finset.sum_subset (Finset.subset_univ _) fun X _ hX => hf X fun h' => hX ?_
  rw [mem_polymersAt]
  exact ⟨h'.2.2, h'.2.1⟩

theorem sum_exp_card_le (hdiv : M * L ^ (kf + 1) ∣ ℓ) (hd : 1 ≤ d) {κ : ℝ}
    (hκ : kappaStar d ≤ κ) {j : ℕ} (hj : j ∈ Finset.Icc 1 (kf + 1)) (x : Torus d ℓ) {t : ℝ}
    (ht : 1 / 2 ≤ t) :
    ∑ X ∈ polymersAt d ℓ (M * L ^ j) x,
      Real.exp (-(κ * t) * (blockNumber d (M * L ^ j) X : ℝ)) ≤ 1 := by
  obtain ⟨m, hm, hmz⟩ := scale_dvd (ℓ := ℓ) hdiv hj
  have := sum_polymersAt_pow_le_one hm hd x (r := Real.exp (-(κ * t))) (Real.exp_nonneg _)
    (ratio_le_half hd hκ ht)
  simpa only [← exp_neg_mul_pow] using this

/-- Each term sum is bounded: `|∑_X T_j(x, X; 0)_i| ≤ c₉ L^{-jθ}`. -/
theorem norm_sum_term_zero_le (hcl : RootFTorusClauses d N L M β ν h kf κ c₉ δ T ℓ)
    (hdiv : M * L ^ (kf + 1) ∣ ℓ) (hd : 1 ≤ d) (hc₉ : 0 ≤ c₉) (hκ : kappaStar d ≤ κ) {j : ℕ}
    (hj : j ∈ Finset.Icc 1 (kf + 1)) (x : Torus d ℓ) (i : Fin N) :
    ‖∑ X : Finset (Torus d ℓ), T ℓ j x X 0 i‖ ≤
      c₉ * (L : ℝ) ^ (-((j : ℝ) * (((d : ℝ) - 2) / 2 + δ))) := by
  obtain ⟨m, hm, hmz⟩ := scale_dvd (ℓ := ℓ) hdiv hj
  rw [sum_term_eq_sum_polymersAt x (fun X => T ℓ j x X 0 i)
    (fun X hX => term_zero_eq_zero_of_not hcl hX i)]
  refine (norm_sum_le _ _).trans ?_
  have hb : ∀ X ∈ polymersAt d ℓ (M * L ^ j) x, ‖T ℓ j x X 0 i‖ ≤
      c₉ * (L : ℝ) ^ (-((j : ℝ) * (((d : ℝ) - 2) / 2 + δ))) *
        Real.exp (-(κ * 1) * (blockNumber d (M * L ^ j) X : ℝ)) := by
    intro X hX
    refine (norm_term_zero_le hcl hj x X i).trans (le_of_eq ?_)
    rw [mem_polymersAt] at hX
    congr 1
    have := exp_card_div_eq hm hX.1 κ
    push_cast at this
    rw [this, mul_one]
  refine (sum_le_sum hb).trans ?_
  rw [← mul_sum]
  calc _ ≤ c₉ * (L : ℝ) ^ (-((j : ℝ) * (((d : ℝ) - 2) / 2 + δ))) * 1 := by
        exact mul_le_mul_of_nonneg_left (sum_exp_card_le hdiv hd hκ hj x (by norm_num))
          (mul_nonneg hc₉ (Real.rpow_nonneg (Nat.cast_nonneg _) _))
    _ = _ := mul_one _

/-- Proposition 1.5 (a): `|⟨φ_i(x)⟩ - h_i| ≤ 3 c₉`, uniformly in the torus. -/
theorem abs_onePoint_sub_le [NeZero N] (hcl : RootFTorusClauses d N L M β ν h kf κ c₉ δ T ℓ)
    (hdiv : M * L ^ (kf + 1) ∣ ℓ) (hd : 3 ≤ d) (hδ : 0 < δ) (hL : 2 ≤ L) (hc₉ : 0 ≤ c₉)
    (hκ : kappaStar d ≤ κ) (x : Torus d ℓ) (i : Fin N) :
    |onePoint d N ℓ β ν h x i - h i| ≤ 3 * c₉ := by
  have hθ : 1 / 2 ≤ ((d : ℝ) - 2) / 2 + δ := by
    have : (3 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have h1 : ((onePoint d N ℓ β ν h x i - h i : ℝ) : ℂ) =
      ∑ j ∈ Finset.Icc 1 (kf + 1), ∑ X : Finset (Torus d ℓ), T ℓ j x X 0 i := by
    push_cast
    rw [onePoint_eq_of_clauses hcl x i]
    ring
  rw [← Real.norm_eq_abs, ← Complex.norm_real, h1]
  refine (norm_sum_le _ _).trans ?_
  calc _ ≤ ∑ j ∈ Finset.Icc 1 (kf + 1),
        c₉ * (L : ℝ) ^ (-((j : ℝ) * (((d : ℝ) - 2) / 2 + δ))) :=
        sum_le_sum fun j hj => norm_sum_term_zero_le hcl hdiv (by omega) hc₉ hκ hj x i
    _ = c₉ * ∑ j ∈ Finset.Icc 1 (kf + 1), (L : ℝ) ^ (-((j : ℝ) * (((d : ℝ) - 2) / 2 + δ))) := by
        rw [mul_sum]
    _ ≤ c₉ * 3 := mul_le_mul_of_nonneg_left (sum_rpow_le_three hL hθ _) hc₉
    _ = 3 * c₉ := mul_comm _ _

end OnePoint

end Balaban.Correlations
