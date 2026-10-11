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

section TwoPoint

theorem sum_norm_smul_sourceDelta (y : Torus d ℓ) (k : Fin N) (l : ℂ) :
    ∑ x', ∑ i', ‖(l • sourceDelta y k) x' i'‖ = ‖l‖ := by
  rw [Finset.sum_eq_single y (fun x _ hx => by simp [sourceDelta, hx]) (by simp)]
  rw [Finset.sum_eq_single k (fun i _ hi => by simp [sourceDelta, hi]) (by simp)]
  simp [sourceDelta]

theorem norm_fderiv_termComp_le (hcl : RootFTorusClauses d N L M β ν h kf κ c₉ δ T ℓ) {j : ℕ}
    (hj : j ∈ Finset.Icc 1 (kf + 1)) (x : Torus d ℓ) (X : Finset (Torus d ℓ)) (i : Fin N)
    (y : Torus d ℓ) (k : Fin N) :
    ‖fderiv ℂ (termComp T ℓ j x X i) 0 (sourceDelta y k)‖ ≤
      2 * (c₉ * (L : ℝ) ^ (-((j : ℝ) * (((d : ℝ) - 2) / 2 + δ)))
        * Real.exp (-κ * (X.card : ℝ) / ((M : ℝ) * (L : ℝ) ^ j) ^ d)) := by
  have key := Balaban.Analysis.norm_fderiv_line_le (f := termComp T ℓ j x X i) (w := 0)
    (v := sourceDelta y k) (ρ := 1 / 2)
    (M := c₉ * (L : ℝ) ^ (-((j : ℝ) * (((d : ℝ) - 2) / 2 + δ)))
        * Real.exp (-κ * (X.card : ℝ) / ((M : ℝ) * (L : ℝ) ^ j) ^ d)) (by norm_num)
    (fun l hl => by
      refine (termComp_analytic hcl j x X i _ ?_).differentiableAt
      show ∑ x', ∑ i', ‖(0 + l • sourceDelta y k) x' i'‖ < 1
      simp only [zero_add]
      rw [sum_norm_smul_sourceDelta]
      linarith)
    (fun l hl => by
      refine (norm_le_pi_norm (T ℓ j x X (0 + l • sourceDelta y k)) i).trans
        (hcl.2.2.2.1 j hj x X _ ?_)
      simp only [zero_add]
      rw [sum_norm_smul_sourceDelta]
      exact hl.le)
  simpa [div_eq_mul_inv, mul_comm] using key

theorem fderiv_termComp_eq_zero_of_not_mem (hcl : RootFTorusClauses d N L M β ν h kf κ c₉ δ T ℓ)
    {j : ℕ} {x : Torus d ℓ} {X : Finset (Torus d ℓ)} {y : Torus d ℓ} (hy : y ∉ X) (i k : Fin N) :
    fderiv ℂ (termComp T ℓ j x X i) 0 (sourceDelta y k) = 0 := by
  set f := termComp T ℓ j x X i with hf
  have hdiff : DifferentiableAt ℂ f 0 :=
    (termComp_analytic hcl j x X i 0 zero_mem_sourceBall).differentiableAt
  have h1 : HasDerivAt (fun t : ℂ => t • sourceDelta y k) (sourceDelta y k) 0 := by
    simpa using (hasDerivAt_id (0 : ℂ)).smul_const (sourceDelta y k)
  have h2 : HasFDerivAt f (fderiv ℂ f 0) ((fun t : ℂ => t • sourceDelta y k) 0) := by
    simpa using hdiff.hasFDerivAt
  have h3 := h2.comp_hasDerivAt (0 : ℂ) h1
  have hconst : (f ∘ fun t : ℂ => t • sourceDelta y k) = fun _ => f 0 := by
    funext t
    have hloc := hcl.2.1 j x X (t • sourceDelta y k) 0 fun z hz => by
      have hzy : z ≠ y := fun h => hy (h ▸ hz)
      simp [sourceDelta, Pi.single_eq_of_ne hzy]
    simp only [Function.comp, hf, termComp]
    rw [hloc]
  rw [hconst] at h3
  exact h3.unique (hasDerivAt_const _ _)

theorem fderiv_termComp_eq_zero_of_not_polymer
    (hcl : RootFTorusClauses d N L M β ν h kf κ c₉ δ T ℓ) {j : ℕ} {x : Torus d ℓ}
    {X : Finset (Torus d ℓ)}
    (hX : ¬ (j ∈ Finset.Icc 1 (kf + 1) ∧ x ∈ X ∧ IsPolymer d ℓ (M * L ^ j) X)) (i : Fin N)
    (v : Torus d ℓ → Fin N → ℂ) : fderiv ℂ (termComp T ℓ j x X i) 0 v = 0 := by
  have : termComp T ℓ j x X i = fun _ => 0 := by
    funext g
    simp [termComp, hcl.1 j x X hX]
  rw [this]
  simp

/-- The contribution of scale `j` to the two-point function is exponentially small in the
distance. -/
theorem norm_sum_fderiv_le (hcl : RootFTorusClauses d N L M β ν h kf κ c₉ δ T ℓ)
    (hdiv : M * L ^ (kf + 1) ∣ ℓ) (hd : 1 ≤ d) (hc₉ : 0 ≤ c₉) (hκ : kappaStar d ≤ κ) {j : ℕ}
    (hj : j ∈ Finset.Icc 1 (kf + 1)) (x y : Torus d ℓ) (i k : Fin N) :
    ‖∑ X : Finset (Torus d ℓ), (fderiv ℂ (termComp T ℓ j x X i) 0 (sourceDelta y k)
        + fderiv ℂ (termComp T ℓ j y X k) 0 (sourceDelta x i))‖ ≤
      4 * c₉ * (L : ℝ) ^ (-((j : ℝ) * (((d : ℝ) - 2) / 2 + δ))) *
        Real.exp (-κ * ((torusDist x y : ℝ) + 1) / (2 * ((M : ℝ) * (L : ℝ) ^ j))) := by
  obtain ⟨m, hm, hmz⟩ := scale_dvd (ℓ := ℓ) hdiv hj
  have hs : (0 : ℝ) < (M : ℝ) * (L : ℝ) ^ j := by
    have : 0 < M * L ^ j := Nat.pos_of_ne_zero (fun h0 => by
      have := NeZero.ne ℓ
      rw [hm, h0] at this; simp at this)
    exact_mod_cast this
  set Q := (polymersAt d ℓ (M * L ^ j) x).filter (fun X => y ∈ X) with hQ
  have hzero : ∀ X ∈ (Finset.univ : Finset (Finset (Torus d ℓ))), X ∉ Q →
      (fderiv ℂ (termComp T ℓ j x X i) 0 (sourceDelta y k)
        + fderiv ℂ (termComp T ℓ j y X k) 0 (sourceDelta x i)) = 0 := by
    intro X _ hXQ
    rw [hQ, mem_filter, mem_polymersAt] at hXQ
    by_cases hp : IsPolymer d ℓ (M * L ^ j) X
    · by_cases hxX : x ∈ X
      · have hyX : y ∉ X := fun hyX => hXQ ⟨⟨hp, hxX⟩, hyX⟩
        rw [fderiv_termComp_eq_zero_of_not_mem hcl hyX,
          fderiv_termComp_eq_zero_of_not_polymer hcl (j := j) (x := y) (X := X)
            (fun h' => hyX h'.2.1)]
        simp
      · rw [fderiv_termComp_eq_zero_of_not_polymer hcl (j := j) (x := x) (X := X)
          (fun h' => hxX h'.2.1), fderiv_termComp_eq_zero_of_not_mem hcl hxX]
        simp
    · rw [fderiv_termComp_eq_zero_of_not_polymer hcl (j := j) (x := x) (X := X)
          (fun h' => hp h'.2.2),
        fderiv_termComp_eq_zero_of_not_polymer hcl (j := j) (x := y) (X := X)
          (fun h' => hp h'.2.2)]
      simp
  rw [← Finset.sum_subset (Finset.subset_univ Q) hzero]
  set r : ℝ := (torusDist x y : ℝ) + 1 with hr
  have hterm : ∀ X ∈ Q,
      ‖fderiv ℂ (termComp T ℓ j x X i) 0 (sourceDelta y k)
        + fderiv ℂ (termComp T ℓ j y X k) 0 (sourceDelta x i)‖ ≤
      4 * c₉ * (L : ℝ) ^ (-((j : ℝ) * (((d : ℝ) - 2) / 2 + δ))) *
        Real.exp (-κ * r / (2 * ((M : ℝ) * (L : ℝ) ^ j))) *
        Real.exp (-(κ * (1 / 2)) * (blockNumber d (M * L ^ j) X : ℝ)) := by
    intro X hX
    rw [hQ, mem_filter, mem_polymersAt] at hX
    obtain ⟨⟨hp, hxX⟩, hyX⟩ := hX
    refine (norm_add_le _ _).trans ?_
    have b1 := norm_fderiv_termComp_le hcl hj x X i y k
    have b2 := norm_fderiv_termComp_le hcl hj y X k x i
    have hexp := exp_card_div_eq hm hp κ
    push_cast at hexp
    rw [hexp] at b1 b2
    have hdist := torusDist_add_one_le hm hp hxX hyX
    have hdistR : r ≤ (blockNumber d (M * L ^ j) X : ℝ) * ((M : ℝ) * (L : ℝ) ^ j) := by
      have : ((torusDist x y + 1 : ℕ) : ℝ) ≤ ((blockNumber d (M * L ^ j) X * (M * L ^ j) : ℕ) : ℝ) :=
        by exact_mod_cast hdist
      push_cast at this
      rw [hr]
      exact this
    have hn : -κ * r / (2 * ((M : ℝ) * (L : ℝ) ^ j)) ≥
        -(κ * (1 / 2)) * (blockNumber d (M * L ^ j) X : ℝ) := by
      have hκ0 : 0 ≤ κ := le_trans (kappaStar_pos hd).le hκ
      rw [ge_iff_le, le_div_iff₀ (by positivity)]
      nlinarith
    have hnn : -κ * (blockNumber d (M * L ^ j) X : ℝ) =
        -(κ * (1 / 2)) * (blockNumber d (M * L ^ j) X : ℝ) +
          -(κ * (1 / 2)) * (blockNumber d (M * L ^ j) X : ℝ) := by ring
    have hE : Real.exp (-κ * (blockNumber d (M * L ^ j) X : ℝ)) ≤
        Real.exp (-κ * r / (2 * ((M : ℝ) * (L : ℝ) ^ j))) *
          Real.exp (-(κ * (1 / 2)) * (blockNumber d (M * L ^ j) X : ℝ)) := by
      rw [hnn, Real.exp_add]
      exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 hn) (Real.exp_nonneg _)
    have hc : 0 ≤ c₉ * (L : ℝ) ^ (-((j : ℝ) * (((d : ℝ) - 2) / 2 + δ))) :=
      mul_nonneg hc₉ (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    calc _ ≤ 2 * (c₉ * (L : ℝ) ^ (-((j : ℝ) * (((d : ℝ) - 2) / 2 + δ))) *
            Real.exp (-κ * (blockNumber d (M * L ^ j) X : ℝ))) +
          2 * (c₉ * (L : ℝ) ^ (-((j : ℝ) * (((d : ℝ) - 2) / 2 + δ))) *
            Real.exp (-κ * (blockNumber d (M * L ^ j) X : ℝ))) := add_le_add b1 b2
      _ = 4 * (c₉ * (L : ℝ) ^ (-((j : ℝ) * (((d : ℝ) - 2) / 2 + δ))) *
            Real.exp (-κ * (blockNumber d (M * L ^ j) X : ℝ))) := by ring
      _ ≤ 4 * (c₉ * (L : ℝ) ^ (-((j : ℝ) * (((d : ℝ) - 2) / 2 + δ))) *
            (Real.exp (-κ * r / (2 * ((M : ℝ) * (L : ℝ) ^ j))) *
              Real.exp (-(κ * (1 / 2)) * (blockNumber d (M * L ^ j) X : ℝ)))) := by
          gcongr
      _ = _ := by ring
  refine (norm_sum_le _ _).trans ((sum_le_sum hterm).trans ?_)
  rw [← mul_sum]
  calc _ ≤ 4 * c₉ * (L : ℝ) ^ (-((j : ℝ) * (((d : ℝ) - 2) / 2 + δ))) *
        Real.exp (-κ * r / (2 * ((M : ℝ) * (L : ℝ) ^ j))) * 1 := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        refine (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun _ _ _ => Real.exp_nonneg _)).trans ?_
        exact sum_exp_card_le hdiv hd hκ hj x le_rfl
    _ = _ := mul_one _

/-- Proposition 1.5 (b): decay of the truncated two-point function, uniformly in the torus, `β`,
`ν ∈ (0, 1]` and `h`.  The constant `C` depends only on `d, L, M, δ, κ`; the decay rate is
`c' = κ / (4 M L²)`. -/
theorem exists_abs_twoPointTruncated_le (d L M : ℕ) (δ κ : ℝ) (hd : 3 ≤ d) (hδ : 0 < δ)
    (hL : 2 ≤ L) (hM : 1 ≤ M) (hκ : kappaStar d ≤ κ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (N : ℕ) [NeZero N] (β ν : ℝ) (h : EuclideanSpace ℝ (Fin N)) (kf : ℕ)
      (c₉ : ℝ) (T : RootFFamily d N) (ℓ : ℕ) [NeZero ℓ],
      RootFTorusClauses d N L M β ν h kf κ c₉ δ T ℓ → M * L ^ (kf + 1) ∣ ℓ → 0 ≤ c₉ →
      0 < ν → (L : ℝ) ^ kf * Real.sqrt ν ≤ L →
      ∀ (x y : Torus d ℓ) (i k : Fin N),
        |twoPointTruncated d N ℓ β ν h x y i k| ≤
          C * c₉ * (1 + (torusDist x y : ℝ)) ^ (-(((d : ℝ) - 2) / 2 + δ)) *
            Real.exp (-(κ / (4 * (M : ℝ) * (L : ℝ) ^ 2) * Real.sqrt ν * (torusDist x y : ℝ))) := by
  have hd1 : 1 ≤ d := by omega
  have hθ : 0 < ((d : ℝ) - 2) / 2 + δ := by
    have : (3 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have hL1 : (1 : ℝ) < L := by exact_mod_cast (by omega : 1 < L)
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hκ0 : 0 < κ := lt_of_lt_of_le (kappaStar_pos hd1) hκ
  have ha : 0 < κ / (4 * (M : ℝ)) := by positivity
  obtain ⟨C0, hC0, hsum⟩ := sum_pow_exp_le hθ ha hL1
  refine ⟨4 * C0, by positivity, ?_⟩
  intro N _ β ν h kf c₉ T ℓ _ hcl hdiv hc₉ hν hkf x y i k
  set θ := ((d : ℝ) - 2) / 2 + δ with hθdef
  set r : ℝ := (torusDist x y : ℝ) + 1 with hr
  set a : ℝ := κ / (4 * (M : ℝ)) with ha_def
  set dist : ℝ := (torusDist x y : ℝ) with hdist
  have hr0 : 0 ≤ r := by positivity
  have hsq : 0 < Real.sqrt ν := Real.sqrt_pos.2 hν
  have hLpos : (0 : ℝ) < L := by linarith
  -- the sum over `j`
  have hG : (twoPointTruncated d N ℓ β ν h x y i k : ℂ) =
      ∑ j ∈ Finset.Icc 1 (kf + 1), ∑ X : Finset (Torus d ℓ),
        (fderiv ℂ (termComp T ℓ j x X i) 0 (sourceDelta y k)
          + fderiv ℂ (termComp T ℓ j y X k) 0 (sourceDelta x i)) :=
    twoPointTruncated_eq_of_clauses hcl x y i k
  rw [← Real.norm_eq_abs, ← Complex.norm_real, hG]
  refine (norm_sum_le _ _).trans ?_
  have hj : ∀ j ∈ Finset.Icc 1 (kf + 1),
      ‖∑ X : Finset (Torus d ℓ), (fderiv ℂ (termComp T ℓ j x X i) 0 (sourceDelta y k)
        + fderiv ℂ (termComp T ℓ j y X k) 0 (sourceDelta x i))‖ ≤
      4 * c₉ * Real.exp (-(a * r * Real.sqrt ν / (L : ℝ) ^ 2)) *
        ((L : ℝ) ^ (-((j : ℝ) * θ)) * Real.exp (-(a * r / (L : ℝ) ^ j))) := by
    intro j hjm
    refine (norm_sum_fderiv_le hcl hdiv hd1 hc₉ hκ hjm x y i k).trans ?_
    have hLj : (0 : ℝ) < (L : ℝ) ^ j := by positivity
    have hLjle : (L : ℝ) ^ j * Real.sqrt ν ≤ (L : ℝ) ^ 2 := by
      have h1 : (L : ℝ) ^ j ≤ (L : ℝ) ^ (kf + 1) :=
        pow_le_pow_right₀ hL1.le (Finset.mem_Icc.1 hjm).2
      calc (L : ℝ) ^ j * Real.sqrt ν ≤ (L : ℝ) ^ (kf + 1) * Real.sqrt ν :=
            mul_le_mul_of_nonneg_right h1 hsq.le
        _ = (L : ℝ) * ((L : ℝ) ^ kf * Real.sqrt ν) := by ring
        _ ≤ (L : ℝ) * L := mul_le_mul_of_nonneg_left hkf hLpos.le
        _ = _ := by ring
    have hsplit : -κ * r / (2 * ((M : ℝ) * (L : ℝ) ^ j)) =
        -(a * r / (L : ℝ) ^ j) + -(a * r / (L : ℝ) ^ j) := by
      rw [ha_def]; field_simp; ring
    have hsec : -(a * r / (L : ℝ) ^ j) ≤ -(a * r * Real.sqrt ν / (L : ℝ) ^ 2) := by
      rw [neg_le_neg_iff, div_le_div_iff₀ (by positivity) hLj]
      have : 0 ≤ a * r := by positivity
      nlinarith
    rw [hsplit, Real.exp_add]
    have hexp2 : Real.exp (-(a * r / (L : ℝ) ^ j)) ≤
        Real.exp (-(a * r * Real.sqrt ν / (L : ℝ) ^ 2)) := Real.exp_le_exp.2 hsec
    have hLr : 0 ≤ (L : ℝ) ^ (-((j : ℝ) * θ)) := Real.rpow_nonneg hLpos.le _
    calc 4 * c₉ * (L : ℝ) ^ (-((j : ℝ) * θ)) *
          (Real.exp (-(a * r / (L : ℝ) ^ j)) * Real.exp (-(a * r / (L : ℝ) ^ j)))
        ≤ 4 * c₉ * (L : ℝ) ^ (-((j : ℝ) * θ)) *
          (Real.exp (-(a * r / (L : ℝ) ^ j)) *
            Real.exp (-(a * r * Real.sqrt ν / (L : ℝ) ^ 2))) := by gcongr
      _ = _ := by ring
  refine (sum_le_sum hj).trans ?_
  rw [← mul_sum]
  have hsum2 : ∑ j ∈ Finset.Icc 1 (kf + 1), (L : ℝ) ^ (-((j : ℝ) * θ)) *
      Real.exp (-(a * r / (L : ℝ) ^ j)) ≤ C0 * (1 + r) ^ (-θ) := by
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg (t := Finset.range (kf + 2)) ?_
      (fun _ _ _ => by positivity)) (hsum (kf + 2) r hr0)
    intro j hjm
    have := Finset.mem_Icc.1 hjm
    exact Finset.mem_range.2 (by omega)
  have h1r : (1 + (torusDist x y : ℝ)) ^ (-θ) ≥ (1 + r) ^ (-θ) := by
    apply Real.rpow_le_rpow_of_nonpos (by positivity) (by rw [hr]; linarith) (by linarith)
  have hexp3 : Real.exp (-(a * r * Real.sqrt ν / (L : ℝ) ^ 2)) ≤
      Real.exp (-(κ / (4 * (M : ℝ) * (L : ℝ) ^ 2) * Real.sqrt ν * dist)) := by
    apply Real.exp_le_exp.2
    rw [neg_le_neg_iff]
    have : κ / (4 * (M : ℝ) * (L : ℝ) ^ 2) * Real.sqrt ν * dist =
        a * dist * Real.sqrt ν / (L : ℝ) ^ 2 := by
      rw [ha_def]; field_simp
    rw [this]
    apply div_le_div_of_nonneg_right _ (by positivity)
    have : 0 ≤ a * Real.sqrt ν := by positivity
    rw [hr]
    nlinarith
  calc 4 * c₉ * Real.exp (-(a * r * Real.sqrt ν / (L : ℝ) ^ 2)) *
        ∑ j ∈ Finset.Icc 1 (kf + 1), (L : ℝ) ^ (-((j : ℝ) * θ)) *
          Real.exp (-(a * r / (L : ℝ) ^ j))
      ≤ 4 * c₉ * Real.exp (-(κ / (4 * (M : ℝ) * (L : ℝ) ^ 2) * Real.sqrt ν * dist)) *
          (C0 * (1 + r) ^ (-θ)) := by
        gcongr
    _ ≤ 4 * c₉ * Real.exp (-(κ / (4 * (M : ℝ) * (L : ℝ) ^ 2) * Real.sqrt ν * dist)) *
          (C0 * (1 + (torusDist x y : ℝ)) ^ (-θ)) := by
        gcongr
    _ = _ := by ring

end TwoPoint

end OnePoint

end Balaban.Correlations
