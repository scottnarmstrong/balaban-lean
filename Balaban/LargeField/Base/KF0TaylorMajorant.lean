/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Base.KF0Gaussian
public import Balaban.Green.KF0WalkOrdinary
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Algebra.Order.Antidiag.Pi
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

/-!
# `KF0TaylorMajorant`: absolute Taylor majorants (F.12) of the site and bond functions

Part F of `notes/phase1/LF-BASE-KF0.md`.  On the all-plus sheet, in the hemisphere chart, the
logarithm of the integrand is a sum of the site functions
`F_x = -½ log(1 - u·u) - (βν/2) (t(u) - 1)² + g·(u + (t(u) - 1) h)` and the bond functions
`F_xy = -(β/2) (t(u) - t(u'))²`, with `t(u) = √(1 - u·u)` and `u = β^{-1/2} v` the landed
tangent variable `v` divided by `√β`.  This file proves, in the coefficient-family form consumed by
`Balaban/Green/KF0WalkOrdinary.lean` (`kf0SeriesBound_summable`, `kf0SeriesTerm_hasSum`):

* (T1) one-variable series with explicit signs: `√(1-x) - 1 = ∑ sqrtCoeff n xⁿ` with
  `sqrtCoeff n ≤ 0` (the Mathlib binomial series for exponent `1/2`, plus a sign argument proved
  here), `-log(1-x) = ∑ logCoeff n xⁿ`, and the squares; absolute majorants
  `1 - √(1-x) ≤ x`, `-log(1-x) ≤ 2x`, `(1 - √(1-x))² ≤ x²`;
* (T2) the composition with a quadratic form `∑_{i∈S} z_i²` as a multivariate coefficient family
  `quadCoeff S a : (Fin D → ℕ) → ℝ` with weighted sum `= ∑ |aₙ| (|S| ρ²)ⁿ` (multinomial expansion),
  the Cauchy square `sqCoeff` of a family, and the linear family `linCoeff`;
* (T3) the site and bond coefficient families `siteCoeff`, `bondCoeff`: `HasSum` to the function on
  the polydisc `|z_i| ≤ ρ`, `D ρ² ≤ 1/4`, and the majorants of (F.12) with explicit constants;
  the exact identification with the landed chart exponent (`chartJac_mul_exp_chartInteractionExponent`);
* (T4) the arithmetic of (F.13): the three terms tend to `0`;
* (T5) a numerical instance for `N = 2`.

Not proved here: the localization Theorem F.1 itself (walk substitution, halos, grouping) is in
other files; the heavy (minus-sheet and large-field) sector and the one-scale theorem are NOT
proved here.  Everything in this file is unconditional.
-/

@[expose] public section

namespace Balaban.LargeField.KF0Taylor

open Polynomial Finset



theorem descP_half_succ (n : ℕ) :
    (descPochhammer ℤ (n+1)).smeval (1/2 : ℝ) = (descPochhammer ℤ n).smeval (1/2 : ℝ) * (1/2 - n) := by
  rw [descPochhammer_succ_right]
  simp [Polynomial.smeval_mul, Polynomial.smeval_sub, Polynomial.smeval_natCast]

theorem sign_descP_half (n : ℕ) :
    (-1 : ℝ) ^ (n+1) * (descPochhammer ℤ (n+1)).smeval (1/2 : ℝ) ≤ 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [descP_half_succ (n+1)]
    have : (-1 : ℝ) ^ (n+1+1) * ((descPochhammer ℤ (n+1)).smeval (1/2 : ℝ) * (1/2 - ((n+1 : ℕ) : ℝ)))
        = ((-1 : ℝ) ^ (n+1) * (descPochhammer ℤ (n+1)).smeval (1/2 : ℝ)) * ((n : ℝ) + 1/2) := by
      push_cast; ring
    rw [this]
    exact mul_nonpos_of_nonpos_of_nonneg ih (by positivity)

/-- Coefficients of `√(1-x) - 1 = ∑ sCoeff n xⁿ`. -/
noncomputable def sqrtCoeff (n : ℕ) : ℝ :=
  (-1) ^ n * Ring.choose (1/2 : ℝ) n - if n = 0 then 1 else 0

theorem sqrtCoeff_nonpos (n : ℕ) : sqrtCoeff n ≤ 0 := by
  cases n with
  | zero => simp [sqrtCoeff]
  | succ n =>
    unfold sqrtCoeff
    rw [Ring.choose_eq_smul]
    simp only [Nat.succ_ne_zero, ite_false, sub_zero]
    have h := sign_descP_half n
    rw [smul_eq_mul, show (-1 : ℝ) ^ (n+1) * (((n+1).factorial : ℝ)⁻¹ *
        (descPochhammer ℤ (n + 1)).smeval (1 / 2)) = ((n+1).factorial : ℝ)⁻¹ *
        ((-1 : ℝ) ^ (n+1) * (descPochhammer ℤ (n + 1)).smeval (1 / 2)) by ring]
    have hp : 0 ≤ ((n+1).factorial : ℝ)⁻¹ := by positivity
    exact mul_nonpos_of_nonneg_of_nonpos hp h

theorem hasSum_sqrtCoeff {x : ℝ} (hx : |x| < 1) :
    HasSum (fun n => sqrtCoeff n * x ^ n) (Real.sqrt (1 - x) - 1) := by
  have h := Complex.one_add_cpow_hasFPowerSeriesOnBall_zero (a := (1/2 : ℂ))
  have hy : (-(x : ℂ)) ∈ Metric.eball (0 : ℂ) 1 := by
    simpa [Metric.mem_eball, edist_dist] using hx
  have h2 := h.hasSum (y := -(x:ℂ)) hy
  simp only [binomialSeries_apply, zero_add] at h2
  have h3 : HasSum (fun n : ℕ => (((-1 : ℝ) ^ n * Ring.choose (1/2 : ℝ) n * x ^ n : ℝ) : ℂ))
      ((Real.sqrt (1 - x) : ℝ) : ℂ) := by
    have hv : ((Real.sqrt (1 - x) : ℝ) : ℂ) = (1 + -(x:ℂ)) ^ (1 / 2 : ℂ) := by
      have hx1 : 0 ≤ 1 - x := by have := (abs_lt.1 hx).2; linarith
      have := Complex.ofReal_cpow hx1 (1/2)
      rw [Real.sqrt_eq_rpow, this]
      push_cast
      ring_nf
    rw [hv]
    convert h2 using 1
    funext n
    rw [List.ofFn_const, List.prod_replicate, smul_eq_mul]
    push_cast
    rw [neg_pow]
    ring
  have h4 := Complex.hasSum_ofReal.1 h3
  have h5 := h4.sub (hasSum_ite_eq 0 (1 : ℝ))
  convert h5 using 1
  funext n
  by_cases hn : n = 0
  · subst hn; simp [sqrtCoeff]
  · simp [sqrtCoeff, hn]


/-- Coefficients of `-log(1-x) = ∑ logCoeff n xⁿ`. -/
noncomputable def logCoeff (n : ℕ) : ℝ := if n = 0 then 0 else 1 / (n : ℝ)

theorem logCoeff_nonneg (n : ℕ) : 0 ≤ logCoeff n := by
  unfold logCoeff; split_ifs <;> positivity

theorem hasSum_logCoeff {x : ℝ} (hx : |x| < 1) :
    HasSum (fun n => logCoeff n * x ^ n) (-Real.log (1 - x)) := by
  have h := Real.hasSum_pow_div_log_of_abs_lt_one hx
  refine (hasSum_nat_add_iff' 1).1 ?_
  simp only [Finset.range_one, Finset.sum_singleton, logCoeff, ite_true, zero_mul, sub_zero]
  convert h using 1
  funext n
  simp only [Nat.add_one_ne_zero, ite_false]
  push_cast
  ring

theorem hasSum_abs_sqrtCoeff {x : ℝ} (hx0 : 0 ≤ x) (hx : x < 1) :
    HasSum (fun n => ‖sqrtCoeff n‖ * x ^ n) (1 - Real.sqrt (1 - x)) := by
  have h := (hasSum_sqrtCoeff (x := x) (by rw [abs_of_nonneg hx0]; exact hx)).neg
  convert h using 1
  · funext n
    rw [Real.norm_eq_abs, abs_of_nonpos (sqrtCoeff_nonpos n)]; ring
  · ring

theorem one_sub_sqrt_le_self {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1) : 1 - Real.sqrt (1 - x) ≤ x := by
  have : 1 - x ≤ Real.sqrt (1 - x) := by
    have h0 : 0 ≤ 1 - x := by linarith
    calc 1 - x = (1 - x) * 1 := by ring
      _ ≤ Real.sqrt (1 - x) := by
        have h1 : Real.sqrt (1 - x) ≤ 1 := Real.sqrt_le_one.2 (by linarith)
        nlinarith [Real.sq_sqrt h0, Real.sqrt_nonneg (1 - x)]
  linarith

theorem hasSum_abs_logCoeff {x : ℝ} (hx0 : 0 ≤ x) (hx : x < 1) :
    HasSum (fun n => ‖logCoeff n‖ * x ^ n) (-Real.log (1 - x)) := by
  convert hasSum_logCoeff (x := x) (by rw [abs_of_nonneg hx0]; exact hx) using 2 with n
  rw [Real.norm_eq_abs, abs_of_nonneg (logCoeff_nonneg n)]

theorem neg_log_one_sub_le {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1 / 2) : -Real.log (1 - x) ≤ 2 * x := by
  have h1 : 0 < 1 - x := by linarith
  have h2 := Real.log_le_sub_one_of_pos (inv_pos.2 h1)
  rw [Real.log_inv] at h2
  have h3 : (1 - x)⁻¹ - 1 = x / (1 - x) := by field_simp; ring
  rw [h3] at h2
  have h4 : x / (1 - x) ≤ 2 * x := by
    rw [div_le_iff₀ h1]; nlinarith
  linarith


/-- Coefficients of `(√(1-x) - 1)²`: the Cauchy square of `sqrtCoeff`. -/
noncomputable def sqrtSqCoeff (n : ℕ) : ℝ :=
  ∑ kl ∈ Finset.HasAntidiagonal.antidiagonal n, sqrtCoeff kl.1 * sqrtCoeff kl.2

theorem sqrtSqCoeff_nonneg (n : ℕ) : 0 ≤ sqrtSqCoeff n :=
  Finset.sum_nonneg fun _ _ => mul_nonneg_of_nonpos_of_nonpos (sqrtCoeff_nonpos _)
    (sqrtCoeff_nonpos _)

theorem hasSum_sqrtSqCoeff {x : ℝ} (hx0 : 0 ≤ x) (hx : x < 1) :
    HasSum (fun n => sqrtSqCoeff n * x ^ n) ((Real.sqrt (1 - x) - 1) ^ 2) := by
  have hs := hasSum_sqrtCoeff (x := x) (by rw [abs_of_nonneg hx0]; exact hx)
  have hn : Summable fun n => ‖sqrtCoeff n * x ^ n‖ := by
    have := (hasSum_abs_sqrtCoeff hx0 hx).summable
    simpa [norm_mul, norm_pow, Real.norm_eq_abs, abs_of_nonneg hx0] using this
  have hprod := tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hn hn
  have hsum := summable_norm_sum_mul_antidiagonal_of_summable_norm hn hn
  have e : ∀ n, ∑ kl ∈ Finset.HasAntidiagonal.antidiagonal n, (sqrtCoeff kl.1 * x ^ kl.1) * (sqrtCoeff kl.2 * x ^ kl.2)
      = sqrtSqCoeff n * x ^ n := by
    intro n
    unfold sqrtSqCoeff
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun kl hkl => ?_
    have := Finset.HasAntidiagonal.mem_antidiagonal.1 hkl
    rw [← this, pow_add]; ring
  simp_rw [e] at hprod hsum
  rw [hs.tsum_eq] at hprod
  rw [sq, hprod]
  exact hsum.of_norm.hasSum

theorem hasSum_abs_sqrtSqCoeff {x : ℝ} (hx0 : 0 ≤ x) (hx : x < 1) :
    HasSum (fun n => ‖sqrtSqCoeff n‖ * x ^ n) ((1 - Real.sqrt (1 - x)) ^ 2) := by
  have := hasSum_sqrtSqCoeff hx0 hx
  convert this using 1
  · funext n; rw [Real.norm_eq_abs, abs_of_nonneg (sqrtSqCoeff_nonneg n)]
  · ring

theorem one_sub_sqrt_sq_le {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1) : (1 - Real.sqrt (1 - x)) ^ 2 ≤ x ^ 2 :=
  pow_le_pow_left₀ (by linarith [Real.sqrt_le_one.2 (show 1 - x ≤ 1 by linarith)])
    (one_sub_sqrt_le_self hx0 hx) 2



section Push

variable {D : ℕ} {ι : Type*}

/-- Total degree `|α| = ∑ α_i` of a multi-index. -/
def mdeg (α : Fin D → ℕ) : ℕ := ∑ i, α i

/-- Push-forward of a family `g` along `φ`: the coefficient of `z^γ` is the sum of `g x` over the
fibre `φ x = γ`. -/
noncomputable def pushCoeff (φ : ι → Fin D → ℕ) (g : ι → ℝ) (γ : Fin D → ℕ) : ℝ :=
  ∑' y : {x // φ x = γ}, g y

theorem abs_prod_pow_le {z : Fin D → ℝ} {ρ : ℝ} (hz : ∀ i, |z i| ≤ ρ) (α : Fin D → ℕ) :
    |∏ i, z i ^ α i| ≤ ρ ^ mdeg α := by
  rw [Finset.abs_prod, mdeg, ← Finset.prod_pow_eq_pow_sum]
  simp_rw [abs_pow]
  gcongr with i
  exact hz i

/-- Regrouping a summable family along `φ`. -/
theorem push_hasSum (φ : ι → Fin D → ℕ) (g : ι → ℝ) (z : Fin D → ℝ)
    (hz : Summable fun x => |g x * ∏ i, z i ^ φ x i|)
    (hfib : ∀ γ, Summable fun y : {x // φ x = γ} => g y) :
    HasSum (fun γ => pushCoeff φ g γ * ∏ i, z i ^ γ i) (∑' x, g x * ∏ i, z i ^ φ x i) := by
  have hs : Summable fun x => g x * ∏ i, z i ^ φ x i := hz.of_abs
  have h1 := (Equiv.sigmaFiberEquiv φ).hasSum_iff.2 hs.hasSum
  refine h1.sigma (fun γ => ?_)
  have : ∀ y : {x // φ x = γ}, g ((Equiv.sigmaFiberEquiv φ) ⟨γ, y⟩) *
      ∏ i, z i ^ φ ((Equiv.sigmaFiberEquiv φ) ⟨γ, y⟩) i = g y * ∏ i, z i ^ γ i := by
    intro y
    simp only [Equiv.sigmaFiberEquiv_apply]
    rw [y.2]
  simp_rw [Function.comp_apply, this]
  exact (hfib γ).hasSum.mul_right _


theorem prod_const_pow (ρ : ℝ) (α : Fin D → ℕ) : ∏ _i : Fin D, ρ ^ α _i = ρ ^ mdeg α := by
  rw [mdeg, Finset.prod_pow_eq_pow_sum]

theorem push_fiber_summable (φ : ι → Fin D → ℕ) (g : ι → ℝ) {ρ : ℝ} (hρ : 0 < ρ)
    (hg : Summable fun x => |g x| * ρ ^ mdeg (φ x)) (γ : Fin D → ℕ) :
    Summable fun y : {x // φ x = γ} => |g y| := by
  have h := hg.subtype {x | φ x = γ}
  have h2 : Summable fun y : {x // φ x = γ} => |g y| * ρ ^ mdeg γ := by
    refine h.congr fun y => ?_
    simp only [Function.comp_apply]
    rw [y.2]
  have := h2.mul_right ((ρ ^ mdeg γ)⁻¹)
  refine this.congr fun y => ?_
  field_simp

theorem push_majorant (φ : ι → Fin D → ℕ) (g : ι → ℝ) {ρ : ℝ} (hρ : 0 < ρ)
    (hg : Summable fun x => |g x| * ρ ^ mdeg (φ x)) :
    Summable (fun γ => |pushCoeff φ g γ| * ρ ^ mdeg γ) ∧
      ∑' γ, |pushCoeff φ g γ| * ρ ^ mdeg γ ≤ ∑' x, |g x| * ρ ^ mdeg (φ x) := by
  have hf := push_fiber_summable φ g hρ hg
  have e : ∀ x, |(|g x|) * ∏ i, ρ ^ φ x i| = |g x| * ρ ^ mdeg (φ x) := by
    intro x
    rw [prod_const_pow, abs_mul, abs_abs, abs_of_pos (pow_pos hρ _)]
  have h1 := push_hasSum φ (fun x => |g x|) (fun _ => ρ) (by simpa only [e] using hg)
    (fun γ => by simpa using (hf γ))
  have hle : ∀ γ, |pushCoeff φ g γ| * ρ ^ mdeg γ ≤ pushCoeff φ (fun x => |g x|) γ * ∏ _i : Fin D, ρ ^ γ _i := by
    intro γ
    rw [prod_const_pow]
    refine mul_le_mul_of_nonneg_right ?_ (pow_nonneg hρ.le _)
    have := norm_tsum_le_tsum_norm (f := fun y : {x // φ x = γ} => g y)
      (by simpa using hf γ)
    simpa [pushCoeff] using this
  have hsum := h1.summable
  have hnn : ∀ γ, 0 ≤ |pushCoeff φ g γ| * ρ ^ mdeg γ := fun γ => by positivity
  refine ⟨hsum.of_nonneg_of_le hnn hle, ?_⟩
  calc ∑' γ, |pushCoeff φ g γ| * ρ ^ mdeg γ
      ≤ ∑' γ, pushCoeff φ (fun x => |g x|) γ * ∏ _i : Fin D, ρ ^ γ _i :=
        Summable.tsum_le_tsum hle (hsum.of_nonneg_of_le hnn hle) hsum
    _ = ∑' x, |g x| * ρ ^ mdeg (φ x) := by
        rw [h1.tsum_eq]
        refine tsum_congr fun x => ?_
        rw [prod_const_pow]

end Push

section Quad

variable {D : ℕ}

/-- Index set of the multinomial expansion of `(∑_{i ∈ S} z_i²)ⁿ`. -/
abbrev QIdx (S : Finset (Fin D)) : Type := Σ n : ℕ, ↥(Finset.piAntidiag S n)

/-- The exponent `α = 2k` of the monomial `∏ (z_i²)^{k_i}`. -/
def quadPhi (S : Finset (Fin D)) : QIdx S → Fin D → ℕ := fun x i => 2 * x.2.1 i

/-- The weight `a_n · multinomial(k)` of the monomial `∏ (z_i²)^{k_i}` in `a_n (∑ z_i²)ⁿ`. -/
noncomputable def quadG (S : Finset (Fin D)) (a : ℕ → ℝ) : QIdx S → ℝ :=
  fun x => a x.1 * (Nat.multinomial S x.2.1 : ℝ)

/-- The coefficient family of `z ↦ ∑ₙ aₙ (∑_{i∈S} z_i²)ⁿ`. -/
noncomputable def quadCoeff (S : Finset (Fin D)) (a : ℕ → ℝ) : (Fin D → ℕ) → ℝ :=
  pushCoeff (quadPhi S) (quadG S a)

theorem mdeg_quadPhi (S : Finset (Fin D)) (x : QIdx S) : mdeg (quadPhi S x) = 2 * x.1 := by
  obtain ⟨n, k, hk⟩ := x
  have hk' := Finset.mem_piAntidiag.1 hk
  simp only [mdeg, quadPhi]
  rw [← Finset.mul_sum]
  congr 1
  rw [← hk'.1]
  symm
  refine Finset.sum_subset (Finset.subset_univ _) fun i _ hi => ?_
  by_contra h
  exact hi (hk'.2 i h)

theorem prod_quadPhi (S : Finset (Fin D)) (z : Fin D → ℝ) (x : QIdx S) :
    ∏ i, z i ^ quadPhi S x i = ∏ i ∈ S, (z i ^ 2) ^ x.2.1 i := by
  obtain ⟨n, k, hk⟩ := x
  have hk' := Finset.mem_piAntidiag.1 hk
  simp only [quadPhi]
  rw [← Finset.prod_subset (Finset.subset_univ S)]
  · refine Finset.prod_congr rfl fun i _ => ?_
    rw [pow_mul]
  · intro i _ hi
    have : k i = 0 := by by_contra h; exact hi (hk'.2 i h)
    simp [this]

theorem sum_piAntidiag_coe (S : Finset (Fin D)) (n : ℕ) (f : (Fin D → ℕ) → ℝ) :
    ∑' k : ↥(Finset.piAntidiag S n), f k = ∑ k ∈ Finset.piAntidiag S n, f k := by
  rw [tsum_fintype]
  exact Finset.sum_coe_sort _ _

theorem sum_multinomial_mul_prod (S : Finset (Fin D)) (n : ℕ) (w : Fin D → ℝ) :
    ∑ k ∈ Finset.piAntidiag S n, (Nat.multinomial S k : ℝ) * ∏ i ∈ S, w i ^ k i =
      (∑ i ∈ S, w i) ^ n :=
  (Finset.sum_pow_eq_sum_piAntidiag S w n).symm

theorem quad_abs_summable (S : Finset (Fin D)) (a : ℕ → ℝ) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hM : Summable fun n => |a n| * ((S.card : ℝ) * ρ ^ 2) ^ n) :
    Summable (fun x : QIdx S => |quadG S a x| * ρ ^ mdeg (quadPhi S x)) ∧
      ∑' x : QIdx S, |quadG S a x| * ρ ^ mdeg (quadPhi S x) =
        ∑' n, |a n| * ((S.card : ℝ) * ρ ^ 2) ^ n := by
  have hfib : ∀ n : ℕ, ∑' k : ↥(Finset.piAntidiag S n),
      |quadG S a ⟨n, k⟩| * ρ ^ mdeg (quadPhi S ⟨n, k⟩) =
      |a n| * ((S.card : ℝ) * ρ ^ 2) ^ n := by
    intro n
    have e : ∀ k : ↥(Finset.piAntidiag S n),
        |quadG S a ⟨n, k⟩| * ρ ^ mdeg (quadPhi S ⟨n, k⟩) =
        |a n| * ρ ^ (2 * n) * (Nat.multinomial S k.1 : ℝ) := by
      intro k
      rw [mdeg_quadPhi]
      simp only [quadG, abs_mul, Nat.abs_cast]
      ring
    simp_rw [e]
    rw [sum_piAntidiag_coe S n (fun k => |a n| * ρ ^ (2 * n) * (Nat.multinomial S k : ℝ)),
      ← Finset.mul_sum]
    have h1 := sum_multinomial_mul_prod S n (fun _ => (1 : ℝ))
    simp only [one_pow, Finset.prod_const_one, mul_one, Finset.sum_const, nsmul_eq_mul] at h1
    rw [h1, mul_pow, ← pow_mul]
    ring
  have hnn : ∀ x : QIdx S, 0 ≤ |quadG S a x| * ρ ^ mdeg (quadPhi S x) := fun x => by positivity
  have hsum : Summable (fun x : QIdx S => |quadG S a x| * ρ ^ mdeg (quadPhi S x)) := by
    rw [summable_sigma_of_nonneg hnn]
    refine ⟨fun n => Summable.of_finite, ?_⟩
    simp_rw [hfib]
    exact hM
  refine ⟨hsum, ?_⟩
  rw [hsum.tsum_sigma' (fun n => Summable.of_finite)]
  exact tsum_congr hfib

theorem quadCoeff_majorant (S : Finset (Fin D)) (a : ℕ → ℝ) {ρ : ℝ} (hρ : 0 < ρ)
    (hM : Summable fun n => |a n| * ((S.card : ℝ) * ρ ^ 2) ^ n) :
    Summable (fun γ => |quadCoeff S a γ| * ρ ^ mdeg γ) ∧
      ∑' γ, |quadCoeff S a γ| * ρ ^ mdeg γ ≤ ∑' n, |a n| * ((S.card : ℝ) * ρ ^ 2) ^ n := by
  obtain ⟨h1, h2⟩ := quad_abs_summable S a hρ.le hM
  obtain ⟨h3, h4⟩ := push_majorant (quadPhi S) (quadG S a) hρ h1
  exact ⟨h3, h4.trans h2.le⟩

theorem quadCoeff_hasSum (S : Finset (Fin D)) (a : ℕ → ℝ) {ρ : ℝ} (hρ : 0 < ρ)
    (hM : Summable fun n => |a n| * ((S.card : ℝ) * ρ ^ 2) ^ n)
    (z : Fin D → ℝ) (hz : ∀ i, |z i| ≤ ρ) {F : ℝ}
    (hF : HasSum (fun n => a n * (∑ i ∈ S, z i ^ 2) ^ n) F) :
    HasSum (fun γ => quadCoeff S a γ * ∏ i, z i ^ γ i) F := by
  obtain ⟨h1, -⟩ := quad_abs_summable S a hρ.le hM
  have hz' : Summable fun x : QIdx S => |quadG S a x * ∏ i, z i ^ quadPhi S x i| := by
    refine h1.of_nonneg_of_le (fun x => abs_nonneg _) fun x => ?_
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (abs_prod_pow_le hz _) (abs_nonneg _)
  have hfib := fun γ => (push_fiber_summable (quadPhi S) (quadG S a) hρ h1 γ).of_abs
  have h2 := push_hasSum (quadPhi S) (quadG S a) z hz' hfib
  have hs : Summable fun x : QIdx S => quadG S a x * ∏ i, z i ^ quadPhi S x i := hz'.of_abs
  have hF2 : HasSum (fun x : QIdx S => quadG S a x * ∏ i, z i ^ quadPhi S x i) F := by
    refine HasSum.sigma_of_hasSum hF (fun n => ?_) hs
    have : ∀ k : ↥(Finset.piAntidiag S n), quadG S a ⟨n, k⟩ * ∏ i, z i ^ quadPhi S ⟨n, k⟩ i =
        a n * ((Nat.multinomial S k.1 : ℝ) * ∏ i ∈ S, (z i ^ 2) ^ k.1 i) := by
      intro k
      rw [prod_quadPhi]
      simp only [quadG]
      ring
    simp_rw [this]
    convert hasSum_fintype (fun k : ↥(Finset.piAntidiag S n) =>
      a n * ((Nat.multinomial S k.1 : ℝ) * ∏ i ∈ S, (z i ^ 2) ^ k.1 i)) using 1
    rw [Finset.sum_coe_sort (Finset.piAntidiag S n) (fun k => a n * ((Nat.multinomial S k : ℝ) *
      ∏ i ∈ S, (z i ^ 2) ^ k i)), ← Finset.mul_sum, sum_multinomial_mul_prod S n (fun i => z i ^ 2)]
  rw [← hF2.tsum_eq]
  exact h2

end Quad

section Combine

variable {D : ℕ}

/-- `c` has absolutely convergent weighted sum at radius `ρ`, bounded by `M`. -/
def Maj (c : (Fin D → ℕ) → ℝ) (ρ M : ℝ) : Prop :=
  Summable (fun α => |c α| * ρ ^ mdeg α) ∧ ∑' α, |c α| * ρ ^ mdeg α ≤ M

theorem Maj.mono {c : (Fin D → ℕ) → ℝ} {ρ M M' : ℝ} (h : Maj c ρ M) (hM : M ≤ M') :
    Maj c ρ M' := ⟨h.1, h.2.trans hM⟩

theorem Maj.add {c₁ c₂ : (Fin D → ℕ) → ℝ} {ρ M₁ M₂ : ℝ} (hρ : 0 ≤ ρ) (h₁ : Maj c₁ ρ M₁)
    (h₂ : Maj c₂ ρ M₂) : Maj (fun α => c₁ α + c₂ α) ρ (M₁ + M₂) := by
  have hs := h₁.1.add h₂.1
  have hle : ∀ α, |c₁ α + c₂ α| * ρ ^ mdeg α ≤ |c₁ α| * ρ ^ mdeg α + |c₂ α| * ρ ^ mdeg α := by
    intro α
    rw [← add_mul]
    exact mul_le_mul_of_nonneg_right (abs_add_le _ _) (pow_nonneg hρ _)
  have hnn : ∀ α, 0 ≤ |c₁ α + c₂ α| * ρ ^ mdeg α := fun α => by positivity
  refine ⟨hs.of_nonneg_of_le hnn hle, ?_⟩
  calc ∑' α, |c₁ α + c₂ α| * ρ ^ mdeg α
      ≤ ∑' α, (|c₁ α| * ρ ^ mdeg α + |c₂ α| * ρ ^ mdeg α) :=
        Summable.tsum_le_tsum hle (hs.of_nonneg_of_le hnn hle) hs
    _ ≤ M₁ + M₂ := by
        rw [Summable.tsum_add h₁.1 h₂.1]
        exact add_le_add h₁.2 h₂.2

theorem Maj.smul {c : (Fin D → ℕ) → ℝ} {ρ M : ℝ} (r : ℝ) (h : Maj c ρ M) :
    Maj (fun α => r * c α) ρ (|r| * M) := by
  have e : ∀ α, |r * c α| * ρ ^ mdeg α = |r| * (|c α| * ρ ^ mdeg α) := fun α => by
    rw [abs_mul]; ring
  unfold Maj
  simp_rw [e]
  exact ⟨h.1.mul_left _, by rw [tsum_mul_left]; exact mul_le_mul_of_nonneg_left h.2 (abs_nonneg _)⟩

theorem Maj.neg {c : (Fin D → ℕ) → ℝ} {ρ M : ℝ} (h : Maj c ρ M) :
    Maj (fun α => -c α) ρ M := by
  have := h.smul (-1)
  simpa using this

theorem Maj.sub {c₁ c₂ : (Fin D → ℕ) → ℝ} {ρ M₁ M₂ : ℝ} (hρ : 0 ≤ ρ) (h₁ : Maj c₁ ρ M₁)
    (h₂ : Maj c₂ ρ M₂) : Maj (fun α => c₁ α - c₂ α) ρ (M₁ + M₂) := by
  simpa [sub_eq_add_neg] using h₁.add hρ h₂.neg

/-- The Cauchy square of a multivariate coefficient family. -/
noncomputable def sqCoeff (e : (Fin D → ℕ) → ℝ) : (Fin D → ℕ) → ℝ :=
  pushCoeff (fun p : (Fin D → ℕ) × (Fin D → ℕ) => p.1 + p.2) (fun p => e p.1 * e p.2)

theorem mdeg_add (α β : Fin D → ℕ) : mdeg (α + β) = mdeg α + mdeg β := by
  simp [mdeg, Finset.sum_add_distrib]

theorem sqCoeff_maj {e : (Fin D → ℕ) → ℝ} {ρ M : ℝ} (hρ : 0 < ρ) (h : Maj e ρ M) :
    Maj (sqCoeff e) ρ (M ^ 2) := by
  have hn : ∀ α, 0 ≤ |e α| * ρ ^ mdeg α := fun α => by positivity
  have hprod : Summable fun p : (Fin D → ℕ) × (Fin D → ℕ) =>
      |e p.1 * e p.2| * ρ ^ mdeg (p.1 + p.2) := by
    have := Summable.mul_of_nonneg h.1 h.1 hn hn
    refine this.congr fun p => ?_
    rw [mdeg_add, abs_mul, pow_add]; ring
  obtain ⟨h1, h2⟩ := push_majorant (fun p : (Fin D → ℕ) × (Fin D → ℕ) => p.1 + p.2)
    (fun p => e p.1 * e p.2) hρ hprod
  refine ⟨h1, h2.trans ?_⟩
  have : ∑' p : (Fin D → ℕ) × (Fin D → ℕ), |e p.1 * e p.2| * ρ ^ mdeg (p.1 + p.2) =
      (∑' α, |e α| * ρ ^ mdeg α) * ∑' α, |e α| * ρ ^ mdeg α := by
    have hN : Summable fun α => ‖|e α| * ρ ^ mdeg α‖ := by
      simpa only [Real.norm_eq_abs] using h.1.abs
    rw [tsum_mul_tsum_of_summable_norm hN hN]
    refine tsum_congr fun p => ?_
    rw [mdeg_add, abs_mul, pow_add]; ring
  rw [this, sq]
  have h0 : 0 ≤ ∑' α, |e α| * ρ ^ mdeg α := tsum_nonneg hn
  exact mul_le_mul h.2 h.2 h0 (h0.trans h.2)

theorem sqCoeff_hasSum {e : (Fin D → ℕ) → ℝ} {ρ : ℝ} (hρ : 0 < ρ)
    (hM : Summable fun α => |e α| * ρ ^ mdeg α) (z : Fin D → ℝ) (hz : ∀ i, |z i| ≤ ρ) {E : ℝ}
    (hE : HasSum (fun α => e α * ∏ i, z i ^ α i) E) :
    HasSum (fun γ => sqCoeff e γ * ∏ i, z i ^ γ i) (E ^ 2) := by
  have hn : ∀ α, 0 ≤ |e α| * ρ ^ mdeg α := fun α => by positivity
  have hprod : Summable fun p : (Fin D → ℕ) × (Fin D → ℕ) =>
      |e p.1 * e p.2| * ρ ^ mdeg (p.1 + p.2) := by
    have := Summable.mul_of_nonneg hM hM hn hn
    refine this.congr fun p => ?_
    rw [mdeg_add, abs_mul, pow_add]; ring
  have hN : Summable fun α => ‖e α * ∏ i, z i ^ α i‖ := by
    refine hM.of_nonneg_of_le (fun α => norm_nonneg _) fun α => ?_
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_left (abs_prod_pow_le hz _) (abs_nonneg _)
  have hz' : Summable fun p : (Fin D → ℕ) × (Fin D → ℕ) =>
      |(e p.1 * e p.2) * ∏ i, z i ^ (p.1 + p.2) i| := by
    have := Summable.mul_of_nonneg hN hN (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
    refine this.congr fun p => ?_
    simp only [Real.norm_eq_abs, ← abs_mul, Pi.add_apply, pow_add, Finset.prod_mul_distrib]
    congr 1; ring
  have hfib := fun γ => (push_fiber_summable
    (fun p : (Fin D → ℕ) × (Fin D → ℕ) => p.1 + p.2) (fun p => e p.1 * e p.2) hρ hprod γ).of_abs
  have h2 := push_hasSum (fun p : (Fin D → ℕ) × (Fin D → ℕ) => p.1 + p.2)
    (fun p => e p.1 * e p.2) z hz' hfib
  have h3 : ∑' p : (Fin D → ℕ) × (Fin D → ℕ), (e p.1 * e p.2) * ∏ i, z i ^ (p.1 + p.2) i = E ^ 2 := by
    have := tsum_mul_tsum_of_summable_norm hN hN
    rw [hE.tsum_eq] at this
    rw [sq, this]
    refine tsum_congr fun p => ?_
    simp only [Pi.add_apply, pow_add, Finset.prod_mul_distrib]
    ring
  rw [h3] at h2
  exact h2

/-- The coefficient family of the linear form `z ↦ ∑ᵢ bᵢ zᵢ`. -/
noncomputable def linCoeff (b : Fin D → ℝ) : (Fin D → ℕ) → ℝ :=
  pushCoeff (fun i : Fin D => (Pi.single i 1 : Fin D → ℕ)) b

theorem linCoeff_maj (b : Fin D → ℝ) {ρ : ℝ} (hρ : 0 < ρ) :
    Maj (linCoeff b) ρ (ρ * ∑ i, |b i|) := by
  have h : Summable fun i : Fin D => |b i| * ρ ^ mdeg (Pi.single i 1 : Fin D → ℕ) := Summable.of_finite
  obtain ⟨h1, h2⟩ := push_majorant (fun i : Fin D => (Pi.single i 1 : Fin D → ℕ)) b hρ h
  refine ⟨h1, h2.trans_eq ?_⟩
  rw [tsum_fintype, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have : mdeg (Pi.single i 1 : Fin D → ℕ) = 1 := by simp [mdeg]
  rw [this]; ring

theorem linCoeff_hasSum (b : Fin D → ℝ) {ρ : ℝ} (hρ : 0 < ρ) (z : Fin D → ℝ) :
    HasSum (fun γ => linCoeff b γ * ∏ i, z i ^ γ i) (∑ i, b i * z i) := by
  have h : Summable fun i : Fin D => |b i * ∏ j, z j ^ (Pi.single i 1 : Fin D → ℕ) j| :=
    Summable.of_finite
  have h1 : Summable fun i : Fin D => |b i| * ρ ^ mdeg (Pi.single i 1 : Fin D → ℕ) := Summable.of_finite
  have hfib := fun γ => (push_fiber_summable (fun i : Fin D => (Pi.single i 1 : Fin D → ℕ)) b hρ h1 γ).of_abs
  have h2 := push_hasSum (fun i : Fin D => (Pi.single i 1 : Fin D → ℕ)) b z h hfib
  rw [tsum_fintype] at h2
  have e : ∀ i : Fin D, ∏ j, z j ^ (Pi.single i 1 : Fin D → ℕ) j = z i := by
    intro i
    rw [Finset.prod_eq_single i]
    · simp
    · intro j _ hj; simp [Pi.single_eq_of_ne hj]
    · simp
  simp_rw [e] at h2
  exact h2

end Combine




section Functions

variable {D : ℕ}

/-- `L(q) = -log(1 - q)`; `½ L(u·u) = -½ log(1 - u·u)` is the Jacobian term of the site function. -/
noncomputable def kf0LogFn (q : ℝ) : ℝ := -Real.log (1 - q)

/-- `S(q) = √(1 - q) - 1`; `S(u·u) = t(u) - 1` is the normal coordinate in units of `β^{-1/2}`. -/
noncomputable def kf0SqrtFn (q : ℝ) : ℝ := Real.sqrt (1 - q) - 1

theorem quad_sum_bounds (S : Finset (Fin D)) (z : Fin D → ℝ) {ρ : ℝ} (hz : ∀ i, |z i| ≤ ρ) :
    0 ≤ ∑ i ∈ S, z i ^ 2 ∧ ∑ i ∈ S, z i ^ 2 ≤ (S.card : ℝ) * ρ ^ 2 := by
  refine ⟨Finset.sum_nonneg fun i _ => sq_nonneg _, ?_⟩
  calc ∑ i ∈ S, z i ^ 2 ≤ ∑ _i ∈ S, ρ ^ 2 :=
        Finset.sum_le_sum fun i _ => by rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hz i) 2
    _ = (S.card : ℝ) * ρ ^ 2 := by simp

theorem summable_abs_sqrtCoeff {x : ℝ} (hx0 : 0 ≤ x) (hx : x < 1) :
    Summable fun n => |sqrtCoeff n| * x ^ n := by
  simpa only [Real.norm_eq_abs] using (hasSum_abs_sqrtCoeff hx0 hx).summable

theorem summable_abs_logCoeff {x : ℝ} (hx0 : 0 ≤ x) (hx : x < 1) :
    Summable fun n => |logCoeff n| * x ^ n := by
  simpa only [Real.norm_eq_abs] using (hasSum_abs_logCoeff hx0 hx).summable

/-- (T1+T2) The coefficient family of `z ↦ √(1 - ∑_{i∈S} z_i²) - 1`: majorant `≤ x = |S| ρ²`. -/
theorem quadSqrt_maj (S : Finset (Fin D)) {ρ : ℝ} (hρ : 0 < ρ)
    (hx : (S.card : ℝ) * ρ ^ 2 ≤ 1 / 4) :
    Maj (quadCoeff S sqrtCoeff) ρ ((S.card : ℝ) * ρ ^ 2) := by
  have hx0 : 0 ≤ (S.card : ℝ) * ρ ^ 2 := by positivity
  obtain ⟨h1, h2⟩ := quadCoeff_majorant S sqrtCoeff hρ
    (summable_abs_sqrtCoeff hx0 (by linarith))
  refine ⟨h1, h2.trans ?_⟩
  have := (hasSum_abs_sqrtCoeff hx0 (by linarith)).tsum_eq
  simp only [Real.norm_eq_abs] at this
  rw [this]
  exact one_sub_sqrt_le_self hx0 (by linarith)

theorem quadSqrt_hasSum (S : Finset (Fin D)) {ρ : ℝ} (hρ : 0 < ρ)
    (hx : (S.card : ℝ) * ρ ^ 2 ≤ 1 / 4) (z : Fin D → ℝ) (hz : ∀ i, |z i| ≤ ρ) :
    HasSum (fun γ => quadCoeff S sqrtCoeff γ * ∏ i, z i ^ γ i) (kf0SqrtFn (∑ i ∈ S, z i ^ 2)) := by
  have hx0 : 0 ≤ (S.card : ℝ) * ρ ^ 2 := by positivity
  obtain ⟨hq0, hq1⟩ := quad_sum_bounds S z hz
  exact quadCoeff_hasSum S sqrtCoeff hρ (summable_abs_sqrtCoeff hx0 (by linarith)) z hz
    (hasSum_sqrtCoeff (by rw [abs_of_nonneg hq0]; linarith))

/-- (T1+T2) The coefficient family of `z ↦ -log(1 - ∑_{i∈S} z_i²)`: majorant `≤ 2x`. -/
theorem quadLog_maj (S : Finset (Fin D)) {ρ : ℝ} (hρ : 0 < ρ)
    (hx : (S.card : ℝ) * ρ ^ 2 ≤ 1 / 4) :
    Maj (quadCoeff S logCoeff) ρ (2 * ((S.card : ℝ) * ρ ^ 2)) := by
  have hx0 : 0 ≤ (S.card : ℝ) * ρ ^ 2 := by positivity
  obtain ⟨h1, h2⟩ := quadCoeff_majorant S logCoeff hρ
    (summable_abs_logCoeff hx0 (by linarith))
  refine ⟨h1, h2.trans ?_⟩
  have := (hasSum_abs_logCoeff hx0 (by linarith)).tsum_eq
  simp only [Real.norm_eq_abs] at this
  rw [this]
  exact neg_log_one_sub_le hx0 (by linarith)

theorem quadLog_hasSum (S : Finset (Fin D)) {ρ : ℝ} (hρ : 0 < ρ)
    (hx : (S.card : ℝ) * ρ ^ 2 ≤ 1 / 4) (z : Fin D → ℝ) (hz : ∀ i, |z i| ≤ ρ) :
    HasSum (fun γ => quadCoeff S logCoeff γ * ∏ i, z i ^ γ i) (kf0LogFn (∑ i ∈ S, z i ^ 2)) := by
  have hx0 : 0 ≤ (S.card : ℝ) * ρ ^ 2 := by positivity
  obtain ⟨hq0, hq1⟩ := quad_sum_bounds S z hz
  exact quadCoeff_hasSum S logCoeff hρ (summable_abs_logCoeff hx0 (by linarith)) z hz
    (hasSum_logCoeff (by rw [abs_of_nonneg hq0]; linarith))

/-- The coefficient family of `(√(1 - ∑_{i∈S} z_i²) - 1)²`. -/
theorem quadSqrtSq_maj (S : Finset (Fin D)) {ρ : ℝ} (hρ : 0 < ρ)
    (hx : (S.card : ℝ) * ρ ^ 2 ≤ 1 / 4) :
    Maj (sqCoeff (quadCoeff S sqrtCoeff)) ρ (((S.card : ℝ) * ρ ^ 2) ^ 2) :=
  sqCoeff_maj hρ (quadSqrt_maj S hρ hx)

theorem quadSqrtSq_hasSum (S : Finset (Fin D)) {ρ : ℝ} (hρ : 0 < ρ)
    (hx : (S.card : ℝ) * ρ ^ 2 ≤ 1 / 4) (z : Fin D → ℝ) (hz : ∀ i, |z i| ≤ ρ) :
    HasSum (fun γ => sqCoeff (quadCoeff S sqrtCoeff) γ * ∏ i, z i ^ γ i)
      (kf0SqrtFn (∑ i ∈ S, z i ^ 2) ^ 2) :=
  sqCoeff_hasSum hρ (quadSqrt_maj S hρ hx).1 z hz (quadSqrt_hasSum S hρ hx z hz)

/-! ### The site function -/

/-- The part of the site function that depends on `q = u·u` only:
`½ L(q) - (βν/2) S(q)² + a S(q)`, `a = g_x · h`. -/
noncomputable def siteProfile (β ν a q : ℝ) : ℝ :=
  (1 / 2) * kf0LogFn q - (β * ν / 2) * kf0SqrtFn q ^ 2 + a * kf0SqrtFn q

/-- The bond function as a function of the two squared tangent norms. -/
noncomputable def bondProfile (β q q' : ℝ) : ℝ := -(β / 2) * (kf0SqrtFn q - kf0SqrtFn q') ^ 2

/-- The site function of the all-plus sector in the variable `u = β^{-1/2} v` (units of the
landed `v`-chart divided by `√β`), `q = u·u`:
`F_x = ½ L(q) - (βν/2) S(q)² + a S(q) + ∑ b_i z_i`, with `a = g_x·h` and `b_i` the tangential
components of `g_x`. -/
noncomputable def siteFn (β ν a : ℝ) (b : Fin D → ℝ) (z : Fin D → ℝ) : ℝ :=
  siteProfile β ν a (∑ i, z i ^ 2) + ∑ i, b i * z i

/-- Coefficient family of `siteFn`. -/
noncomputable def siteCoeff (β ν a : ℝ) (b : Fin D → ℝ) : (Fin D → ℕ) → ℝ := fun α =>
  (1 / 2) * quadCoeff Finset.univ logCoeff α
    + (-(β * ν / 2)) * sqCoeff (quadCoeff Finset.univ sqrtCoeff) α
    + a * quadCoeff Finset.univ sqrtCoeff α + linCoeff b α

theorem siteCoeff_hasSum (β ν a : ℝ) (b : Fin D → ℝ) {ρ : ℝ} (hρ : 0 < ρ)
    (hx : (D : ℝ) * ρ ^ 2 ≤ 1 / 4) (z : Fin D → ℝ) (hz : ∀ i, |z i| ≤ ρ) :
    HasSum (fun γ => siteCoeff β ν a b γ * ∏ i, z i ^ γ i) (siteFn β ν a b z) := by
  have hx' : ((Finset.univ : Finset (Fin D)).card : ℝ) * ρ ^ 2 ≤ 1 / 4 := by simpa using hx
  have h1 := (quadLog_hasSum Finset.univ hρ hx' z hz).mul_left (1 / 2)
  have h2 := (quadSqrtSq_hasSum Finset.univ hρ hx' z hz).mul_left (-(β * ν / 2))
  have h3 := (quadSqrt_hasSum Finset.univ hρ hx' z hz).mul_left a
  have h4 := linCoeff_hasSum b hρ z
  have := ((h1.add h2).add h3).add h4
  convert this using 1
  · funext γ; simp only [siteCoeff]; ring
  · simp only [siteFn, siteProfile]; ring

theorem siteCoeff_maj {β ν : ℝ} (hβ : 0 ≤ β) (hν : 0 ≤ ν) (a : ℝ) (b : Fin D → ℝ) {ρ : ℝ}
    (hρ : 0 < ρ) (hx : (D : ℝ) * ρ ^ 2 ≤ 1 / 4) :
    Maj (siteCoeff β ν a b) ρ
      (ρ * (∑ i, |b i|) + (D : ℝ) * ρ ^ 2 * (1 + |a|) + (ν / 2) * (D : ℝ) ^ 2 * β * ρ ^ 4) := by
  have hx' : ((Finset.univ : Finset (Fin D)).card : ℝ) * ρ ^ 2 ≤ 1 / 4 := by simpa using hx
  have m1 := (quadLog_maj Finset.univ hρ hx').smul (1 / 2)
  have m2 := (quadSqrtSq_maj Finset.univ hρ hx').smul (-(β * ν / 2))
  have m3 := (quadSqrt_maj Finset.univ hρ hx').smul a
  have m4 := linCoeff_maj b hρ
  have := (((m1.add hρ.le m2).add hρ.le m3).add hρ.le m4)
  refine Maj.mono this ?_
  simp only [Finset.card_univ, Fintype.card_fin, abs_neg, abs_div, abs_mul, abs_of_nonneg hβ,
    abs_of_nonneg hν]
  norm_num
  nlinarith [sq_nonneg ρ]


/-- The `D ≥ 1`, `ρ ≤ 1`, `ν ≤ 1` form of the site majorant (F.12):
`M ≤ D² (G ρ + ρ² + β ρ⁴)` with `G = ∑ |b_i| + |a|`. -/
theorem siteCoeff_maj_C {β ν : ℝ} (hβ : 0 ≤ β) (hν : 0 ≤ ν) (hν1 : ν ≤ 1) (hD : 1 ≤ D) (a : ℝ)
    (b : Fin D → ℝ) {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hx : (D : ℝ) * ρ ^ 2 ≤ 1 / 4) :
    Maj (siteCoeff β ν a b) ρ
      ((D : ℝ) ^ 2 * (((∑ i, |b i|) + |a|) * ρ + ρ ^ 2 + β * ρ ^ 4)) := by
  refine (siteCoeff_maj hβ hν a b hρ hx).mono ?_
  have hD1 : (1 : ℝ) ≤ D := by exact_mod_cast hD
  have hB : 0 ≤ ∑ i, |b i| := Finset.sum_nonneg fun i _ => abs_nonneg _
  have hρ2 : ρ ^ 2 ≤ ρ := by nlinarith
  have hD2 : (D : ℝ) ≤ (D : ℝ) ^ 2 := by nlinarith
  have h4 : 0 ≤ β * ρ ^ 4 := by positivity
  have hD3 : (1 : ℝ) ≤ (D : ℝ) ^ 2 := by nlinarith
  have e1 : ρ * (∑ i, |b i|) ≤ (D : ℝ) ^ 2 * ((∑ i, |b i|) * ρ) := by
    nlinarith [mul_nonneg (sub_nonneg.2 hD3) (mul_nonneg hB hρ.le)]
  have t1 : (D : ℝ) * ρ ^ 2 ≤ (D : ℝ) ^ 2 * ρ ^ 2 := mul_le_mul_of_nonneg_right hD2 (sq_nonneg ρ)
  have t2 : (D : ℝ) * ρ ^ 2 * |a| ≤ (D : ℝ) ^ 2 * ρ * |a| :=
    mul_le_mul_of_nonneg_right (mul_le_mul hD2 hρ2 (sq_nonneg ρ) (sq_nonneg _)) (abs_nonneg _)
  have e2 : (D : ℝ) * ρ ^ 2 * (1 + |a|) ≤ (D : ℝ) ^ 2 * (ρ ^ 2 + |a| * ρ) := by
    nlinarith [t1, t2]
  have e3 : (ν / 2) * (D : ℝ) ^ 2 * β * ρ ^ 4 ≤ (D : ℝ) ^ 2 * (β * ρ ^ 4) := by
    have : ν / 2 ≤ 1 := by linarith
    nlinarith [mul_nonneg (sq_nonneg (D : ℝ)) h4]
  nlinarith [e1, e2, e3]

/-! ### The bond function -/

/-- The bond function `F_xy = -(β/2)(S(q₁) - S(q₂))²` of two sites with squared tangent norms
`q_k = ∑_{i∈S_k} z_i²`, as a function of the `|S₁| + |S₂|` coordinates. -/
noncomputable def bondFn (β : ℝ) (S₁ S₂ : Finset (Fin D)) (z : Fin D → ℝ) : ℝ :=
  bondProfile β (∑ i ∈ S₁, z i ^ 2) (∑ i ∈ S₂, z i ^ 2)

/-- Coefficient family of `bondFn`. -/
noncomputable def bondCoeff (β : ℝ) (S₁ S₂ : Finset (Fin D)) : (Fin D → ℕ) → ℝ := fun α =>
  (-(β / 2)) * sqCoeff (fun γ => quadCoeff S₁ sqrtCoeff γ - quadCoeff S₂ sqrtCoeff γ) α

theorem bondCoeff_hasSum (β : ℝ) (S₁ S₂ : Finset (Fin D)) {ρ : ℝ} (hρ : 0 < ρ)
    (hx₁ : (S₁.card : ℝ) * ρ ^ 2 ≤ 1 / 4) (hx₂ : (S₂.card : ℝ) * ρ ^ 2 ≤ 1 / 4)
    (z : Fin D → ℝ) (hz : ∀ i, |z i| ≤ ρ) :
    HasSum (fun γ => bondCoeff β S₁ S₂ γ * ∏ i, z i ^ γ i) (bondFn β S₁ S₂ z) := by
  have hm := (quadSqrt_maj S₁ hρ hx₁).sub hρ.le (quadSqrt_maj S₂ hρ hx₂)
  have he : HasSum (fun α => (quadCoeff S₁ sqrtCoeff α - quadCoeff S₂ sqrtCoeff α) *
      ∏ i, z i ^ α i) (kf0SqrtFn (∑ i ∈ S₁, z i ^ 2) - kf0SqrtFn (∑ i ∈ S₂, z i ^ 2)) := by
    simpa only [sub_mul] using
      (quadSqrt_hasSum S₁ hρ hx₁ z hz).sub (quadSqrt_hasSum S₂ hρ hx₂ z hz)
  have h := sqCoeff_hasSum hρ hm.1 z hz he
  have := h.mul_left (-(β / 2))
  convert this using 1
  · funext γ; simp only [bondCoeff]; ring
  · simp only [bondFn, bondProfile]

theorem bondCoeff_maj {β : ℝ} (hβ : 0 ≤ β) (S₁ S₂ : Finset (Fin D)) {ρ : ℝ} (hρ : 0 < ρ)
    (hx₁ : (S₁.card : ℝ) * ρ ^ 2 ≤ 1 / 4) (hx₂ : (S₂.card : ℝ) * ρ ^ 2 ≤ 1 / 4) :
    Maj (bondCoeff β S₁ S₂) ρ ((β / 2) * ((S₁.card : ℝ) + S₂.card) ^ 2 * ρ ^ 4) := by
  have hm := (quadSqrt_maj S₁ hρ hx₁).sub hρ.le (quadSqrt_maj S₂ hρ hx₂)
  have h := (sqCoeff_maj hρ hm).smul (-(β / 2))
  refine h.mono (le_of_eq ?_)
  rw [abs_neg, abs_div, abs_of_nonneg hβ]
  norm_num
  ring

/-- First block of `m` coordinates in `Fin (m + m)`. -/
def bondFst (m : ℕ) : Finset (Fin (m + m)) := Finset.univ.image (Fin.castAdd m)

/-- Second block of `m` coordinates in `Fin (m + m)`. -/
def bondSnd (m : ℕ) : Finset (Fin (m + m)) := Finset.univ.image (Fin.natAdd m)

theorem card_bondFst (m : ℕ) : (bondFst m).card = m := by
  rw [bondFst, Finset.card_image_of_injective _ (Fin.castAdd_injective m m)]; simp

theorem card_bondSnd (m : ℕ) : (bondSnd m).card = m := by
  rw [bondSnd, Finset.card_image_of_injective _ (Fin.natAdd_injective m m)]; simp

/-- The bond majorant (F.12) for two sites with `m = N - 1` tangent coordinates each:
`M ≤ 2 m² β ρ⁴`. -/
theorem bondCoeff_maj_pair {β : ℝ} (hβ : 0 ≤ β) (m : ℕ) {ρ : ℝ} (hρ : 0 < ρ)
    (hx : (m : ℝ) * ρ ^ 2 ≤ 1 / 4) :
    Maj (bondCoeff β (bondFst m) (bondSnd m)) ρ (2 * (m : ℝ) ^ 2 * β * ρ ^ 4) := by
  have := bondCoeff_maj hβ (bondFst m) (bondSnd m) hρ (by rwa [card_bondFst])
    (by rwa [card_bondSnd])
  rw [card_bondFst, card_bondSnd] at this
  refine this.mono (le_of_eq ?_)
  ring

theorem bondCoeff_hasSum_pair (β : ℝ) (m : ℕ) {ρ : ℝ} (hρ : 0 < ρ)
    (hx : (m : ℝ) * ρ ^ 2 ≤ 1 / 4) (z : Fin (m + m) → ℝ) (hz : ∀ i, |z i| ≤ ρ) :
    HasSum (fun γ => bondCoeff β (bondFst m) (bondSnd m) γ * ∏ i, z i ^ γ i)
      (bondFn β (bondFst m) (bondSnd m) z) :=
  bondCoeff_hasSum β _ _ hρ (by rwa [card_bondFst]) (by rwa [card_bondSnd]) z hz


/-! ### Smallness (F.13) -/

section Smallness

open Filter Topology

/-- The radius `ρ_β = θ · p_β · A / √β` with `p_β = b log(β a)`. -/
noncomputable def rhoBeta (θ b A a β : ℝ) : ℝ := θ * (b * Real.log (β * a)) * A / Real.sqrt β

/-- `log(β a) / β^{1/4} → 0`. -/
theorem tendsto_log_div_rpow_quarter {a : ℝ} (ha : 0 < a) :
    Tendsto (fun β : ℝ => Real.log (β * a) / β ^ (1 / 4 : ℝ)) atTop (𝓝 0) := by
  have h1 : Tendsto (fun β : ℝ => Real.log β / β ^ (1 / 4 : ℝ)) atTop (𝓝 0) :=
    (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 4)).tendsto_div_nhds_zero
  have h2 : Tendsto (fun β : ℝ => Real.log a / β ^ (1 / 4 : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_rpow_atTop (by norm_num))
  have := h1.add h2
  rw [add_zero] at this
  refine this.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with β hβ
  rw [Real.log_mul hβ.ne' ha.ne', add_div]

/-- `log(β a)/√β → 0`. -/
theorem tendsto_log_div_sqrt {a : ℝ} (ha : 0 < a) :
    Tendsto (fun β : ℝ => Real.log (β * a) / Real.sqrt β) atTop (𝓝 0) := by
  have h := (tendsto_log_div_rpow_quarter ha).mul
    (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 4))
  rw [zero_mul] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with β hβ
  have hs : Real.sqrt β = (β ^ (1 / 4 : ℝ)) ^ 2 := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hβ.le]; norm_num
  rw [hs, Real.rpow_neg hβ.le]
  have : 0 < β ^ (1 / 4 : ℝ) := Real.rpow_pos_of_pos hβ _
  field_simp

/-- `log⁴(β a)/β → 0`. -/
theorem tendsto_log_pow_four_div {a : ℝ} (ha : 0 < a) :
    Tendsto (fun β : ℝ => Real.log (β * a) ^ 4 / β) atTop (𝓝 0) := by
  have h := (tendsto_log_div_rpow_quarter ha).pow 4
  rw [zero_pow (by norm_num)] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with β hβ
  have hs : (β ^ (1 / 4 : ℝ)) ^ 4 = β := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hβ.le]; norm_num
  rw [div_pow, hs]

/-- (T4) The three terms of (F.13) tend to `0`: for every `ε > 0` there is `β₁` such that for
`β ≥ β₁` and every choice of the (finite) constants, the bound is below `ε`. -/
theorem smallness_tendsto {a : ℝ} (ha : 0 < a) (K₁ K₂ K₄ : ℝ) :
    Tendsto (fun β : ℝ => K₁ * (Real.log (β * a) / Real.sqrt β)
      + K₂ * (Real.log (β * a) ^ 2 / β) + K₄ * (Real.log (β * a) ^ 4 / β)) atTop (𝓝 0) := by
  have h1 := tendsto_log_div_sqrt ha
  have h2 : Tendsto (fun β : ℝ => Real.log (β * a) ^ 2 / β) atTop (𝓝 0) := by
    have := h1.pow 2
    rw [zero_pow (by norm_num)] at this
    refine this.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with β hβ
    rw [div_pow, Real.sq_sqrt hβ.le]
  have h4 := tendsto_log_pow_four_div ha
  have := ((h1.const_mul K₁).add (h2.const_mul K₂)).add (h4.const_mul K₄)
  simpa using this

theorem smallness_eps {a : ℝ} (ha : 0 < a) (K₁ K₂ K₄ : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ β₁ : ℝ, ∀ β ≥ β₁, |K₁ * (Real.log (β * a) / Real.sqrt β)
      + K₂ * (Real.log (β * a) ^ 2 / β) + K₄ * (Real.log (β * a) ^ 4 / β)| < ε := by
  have h := (smallness_tendsto ha K₁ K₂ K₄)
  rw [Metric.tendsto_nhds] at h
  obtain ⟨β₁, hβ₁⟩ := eventually_atTop.1 (h ε hε)
  exact ⟨β₁, fun β hβ => by simpa [Real.dist_eq] using hβ₁ β hβ⟩

/-- The site majorant `G ρ + ρ² + β ρ⁴` at `ρ = ρ_β` is the combination
`K₁ L₁ + K₂ L₂ + K₄ L₄` of the three terms of (F.13), with `c = θ b A`,
`K₁ = G c`, `K₂ = c²`, `K₄ = c⁴`. -/
theorem site_bound_rhoBeta (θ b A a G β : ℝ) (hβ : 0 < β) :
    G * rhoBeta θ b A a β + rhoBeta θ b A a β ^ 2 + β * rhoBeta θ b A a β ^ 4 =
      (G * (θ * b * A)) * (Real.log (β * a) / Real.sqrt β)
      + (θ * b * A) ^ 2 * (Real.log (β * a) ^ 2 / β)
      + (θ * b * A) ^ 4 * (Real.log (β * a) ^ 4 / β) := by
  obtain ⟨s, hs, rfl⟩ : ∃ s : ℝ, 0 < s ∧ β = s ^ 2 :=
    ⟨Real.sqrt β, Real.sqrt_pos.2 hβ, (Real.sq_sqrt hβ.le).symm⟩
  simp only [rhoBeta, Real.sqrt_sq hs.le]
  field_simp


/-- The bond majorant `β ρ⁴` at `ρ = ρ_β`. -/
theorem bond_bound_rhoBeta (θ b A a β : ℝ) (hβ : 0 < β) :
    β * rhoBeta θ b A a β ^ 4 = (θ * b * A) ^ 4 * (Real.log (β * a) ^ 4 / β) := by
  obtain ⟨s, hs, rfl⟩ : ∃ s : ℝ, 0 < s ∧ β = s ^ 2 :=
    ⟨Real.sqrt β, Real.sqrt_pos.2 hβ, (Real.sq_sqrt hβ.le).symm⟩
  simp only [rhoBeta, Real.sqrt_sq hs.le]
  field_simp

/-- For `θ b A > 0` the radius `ρ_β` is positive, at most `1` and satisfies `D ρ_β² ≤ 1/4`
for all large `β`: the hypotheses of the majorant theorems hold eventually. -/
theorem rhoBeta_eventually_small {θ b A a : ℝ} (hc : 0 < θ * b * A) (ha : 0 < a) (D : ℕ) :
    ∀ᶠ β : ℝ in atTop, 0 < rhoBeta θ b A a β ∧ rhoBeta θ b A a β ≤ 1 ∧
      (D : ℝ) * rhoBeta θ b A a β ^ 2 ≤ 1 / 4 := by
  have h := (tendsto_log_div_sqrt ha).const_mul (θ * b * A)
  rw [mul_zero] at h
  have hr : ∀ β, rhoBeta θ b A a β = θ * b * A * (Real.log (β * a) / Real.sqrt β) := by
    intro β; unfold rhoBeta; ring
  have h2 : Tendsto (fun β : ℝ => rhoBeta θ b A a β) atTop (𝓝 0) := by
    simpa only [hr] using h
  have h3 : Tendsto (fun β : ℝ => (D : ℝ) * rhoBeta θ b A a β ^ 2) atTop (𝓝 0) := by
    simpa using (h2.pow 2).const_mul (D : ℝ)
  have e1 := (tendsto_order.1 h2).2 1 one_pos
  have e2 := (tendsto_order.1 h3).2 (1 / 4) (by norm_num)
  have e3 : ∀ᶠ β : ℝ in atTop, 1 < β * a := by
    have : Tendsto (fun β : ℝ => β * a) atTop atTop := tendsto_id.atTop_mul_const ha
    exact this.eventually_gt_atTop 1
  filter_upwards [e1, e2, e3, eventually_gt_atTop 0] with β h1 h2' h3' h4'
  refine ⟨?_, h1.le, h2'.le⟩
  rw [hr]
  exact mul_pos hc (div_pos (Real.log_pos h3') (Real.sqrt_pos.2 h4'))

end Smallness

/-! ### An instance (N = 2) -/

/-- Non-vacuity (T5): `N = 2`, `D = 1`, `ρ = 1/4`, `β = 100`, `ν = 1`, source data `a = 1`,
`b = 1/2`.  The coefficient family is summable at `ρ` with weighted sum at most
`1 · (3/2 · 1/4 + 1/16 + 100/256)` and it sums to the site function at `z = 1/8`. -/
theorem siteCoeff_instance :
    Maj (siteCoeff (100 : ℝ) 1 1 (fun _ : Fin 1 => (1 / 2 : ℝ))) (1 / 4)
      (1 ^ 2 * ((((∑ _i : Fin 1, |(1 / 2 : ℝ)|) + |(1 : ℝ)|) * (1 / 4)) + (1 / 4) ^ 2
        + 100 * (1 / 4) ^ 4)) ∧
    HasSum (fun γ => siteCoeff (100 : ℝ) 1 1 (fun _ : Fin 1 => (1 / 2 : ℝ)) γ *
        ∏ i, (fun _ : Fin 1 => (1 / 8 : ℝ)) i ^ γ i)
      (siteFn (100 : ℝ) 1 1 (fun _ : Fin 1 => (1 / 2 : ℝ)) (fun _ => (1 / 8 : ℝ))) := by
  constructor
  · have := siteCoeff_maj_C (D := 1) (β := 100) (ν := 1) (by norm_num) (by norm_num) le_rfl
      le_rfl 1 (fun _ : Fin 1 => (1 / 2 : ℝ)) (ρ := 1 / 4) (by norm_num) (by norm_num)
      (by norm_num)
    simpa using this
  · exact siteCoeff_hasSum 100 1 1 _ (ρ := 1 / 4) (by norm_num) (by norm_num) _ (fun i => by
      norm_num [abs_of_pos])


end Functions


/-! ### The landed chart exponent -/

section Bridge

open SphereChart

variable {d N ℓ : ℕ} [NeZero ℓ] {h : EuclideanSpace ℝ (Fin N)}

omit [NeZero ℓ] in
theorem wN_eq_sqrt_mul (β : ℝ) (v : Torus d ℓ → perp h) (x : Torus d ℓ) :
    wN β v x = Real.sqrt β * kf0SqrtFn (‖v x‖ ^ 2 / β) := rfl

theorem chartJac_eq_exp {β : ℝ} (v : Torus d ℓ → perp h) (hv : ∀ x, ‖v x‖ ^ 2 < β) :
    chartJac β (fun x => ((v x : perp h) : EuclideanSpace ℝ (Fin N))) =
      Real.exp (∑ x, (1 / 2) * kf0LogFn (‖v x‖ ^ 2 / β)) := by
  have hβ : 0 < β := lt_of_le_of_lt (sq_nonneg _) (hv (Classical.arbitrary _))
  have hlt : ∀ x, ‖((v x : perp h) : EuclideanSpace ℝ (Fin N))‖ < Real.sqrt β := fun x =>
    (Real.lt_sqrt (norm_nonneg _)).2 (hv x)
  rw [Real.exp_sum, chartJac_of_lt hlt]
  refine Finset.prod_congr rfl fun x _ => ?_
  have hn : ‖((v x : perp h) : EuclideanSpace ℝ (Fin N))‖ = ‖v x‖ := rfl
  rw [hn]
  have hq : 0 < 1 - ‖v x‖ ^ 2 / β := by
    have : ‖v x‖ ^ 2 / β < 1 := (div_lt_one hβ).2 (hv x)
    linarith
  rw [kf0LogFn, Real.sqrt_eq_rpow, Real.rpow_def_of_pos hq, ← Real.exp_neg]
  congr 1
  ring

/-- **The landed chart integrand in the variables of the site and bond functions.**  For
`‖v x‖² < β` at every site, the Jacobian times the exponential of the interaction exponent is the
exponential of `⟨g,h⟩ + β^{-1/2}⟨g,v⟩` plus the sum of the site profiles `siteProfile β ν (g_x·h) q_x`
(the Jacobian term `½ L(q_x)`, the mass term, the normal source) and of the bond profiles over
the forward bonds, where `q_x = ‖v x‖²/β = u_x·u_x`. -/
theorem chartJac_mul_exp_chartInteractionExponent {β : ℝ} (ν : ℝ) (g : Torus d ℓ → Fin N → ℝ)
    (v : Torus d ℓ → perp h) (hv : ∀ x, ‖v x‖ ^ 2 < β) :
    chartJac β (fun x => ((v x : perp h) : EuclideanSpace ℝ (Fin N))) *
        Real.exp (chartInteractionExponent β ν h g v) =
      Real.exp (sourceConst g h + (Real.sqrt β)⁻¹ * sourceTangent g v
        + ∑ x, siteProfile β ν (∑ i, g x i * h i) (‖v x‖ ^ 2 / β)
        + ∑ x, ∑ μ : Fin d,
            bondProfile β (‖v (x + Pi.single μ 1)‖ ^ 2 / β) (‖v x‖ ^ 2 / β)) := by
  have hβ : 0 < β := lt_of_le_of_lt (sq_nonneg _) (hv (Classical.arbitrary _))
  have hs : Real.sqrt β ^ 2 = β := Real.sq_sqrt hβ.le
  have hs0 : Real.sqrt β ≠ 0 := (Real.sqrt_pos.2 hβ).ne'
  rw [chartJac_eq_exp v hv, ← Real.exp_add]
  congr 1
  have eR : chartRemainder β ν v =
      ∑ x, ∑ μ : Fin d, (β / 2) * (kf0SqrtFn (‖v (x + Pi.single μ 1)‖ ^ 2 / β)
        - kf0SqrtFn (‖v x‖ ^ 2 / β)) ^ 2
      + ∑ x, (β * ν / 2) * kf0SqrtFn (‖v x‖ ^ 2 / β) ^ 2 := by
    unfold chartRemainder
    simp only [wN_eq_sqrt_mul]
    rw [Finset.mul_sum, Finset.mul_sum]
    congr 1
    · refine Finset.sum_congr rfl fun x _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun μ _ => ?_
      rw [← mul_sub, mul_pow, hs]; ring
    · refine Finset.sum_congr rfl fun x _ => ?_
      rw [mul_pow, hs]; ring
  have eN : (Real.sqrt β)⁻¹ * sourceNormal g h β v =
      ∑ x, (∑ i, g x i * h i) * kf0SqrtFn (‖v x‖ ^ 2 / β) := by
    unfold sourceNormal
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    simp only [wN_eq_sqrt_mul]
    field_simp
  have eS : ∑ x, siteProfile β ν (∑ i, g x i * h i) (‖v x‖ ^ 2 / β) =
      ∑ x, (1 / 2) * kf0LogFn (‖v x‖ ^ 2 / β) - ∑ x, (β * ν / 2) * kf0SqrtFn (‖v x‖ ^ 2 / β) ^ 2
        + ∑ x, (∑ i, g x i * h i) * kf0SqrtFn (‖v x‖ ^ 2 / β) := by
    simp only [siteProfile, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  have eB : ∑ x, ∑ μ : Fin d, bondProfile β (‖v (x + Pi.single μ 1)‖ ^ 2 / β) (‖v x‖ ^ 2 / β) =
      -∑ x, ∑ μ : Fin d, (β / 2) * (kf0SqrtFn (‖v (x + Pi.single μ 1)‖ ^ 2 / β)
        - kf0SqrtFn (‖v x‖ ^ 2 / β)) ^ 2 := by
    simp only [bondProfile, neg_mul, Finset.sum_neg_distrib]
  unfold chartInteractionExponent
  rw [eR, eN, eS, eB]
  ring

end Bridge

/-! ### Consumption by the walk estimate core -/

section Consumer

open Balaban.Green

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] {D : ℕ}

/-- The site series feeds `kf0SeriesTerm_hasSum`: with the radius
`ρ = θ (p A_γ / √β)` (positive, `D ρ² ≤ 1/4`), the expanded walk series of the site function is
absolutely summable and sums to `∑_α c_α ∏_j (ℓ_j u_{x_j})^{α_j}`; if moreover the coordinates
`ℓ_j u_{x_j}` lie in the polydisc of radius `ρ`, this sum is the site function. -/
theorem siteCoeff_kf0SeriesTerm_hasSum {d m : ℕ} [NeZero m] {ν g : ℝ} (hg : 0 < g) (hgν : g ≤ ν)
    {γ : ℝ} (hγ : 0 ≤ γ) (hq : 2 * d / (2 * d + g) * Real.exp γ < 1) (β : ℝ) {p : ℝ}
    (hp0 : 0 ≤ p) {θ : ℝ} (hθ : 1 ≤ θ) (x : Fin D → Torus d m) (ℓ : Fin D → W →L[ℝ] ℝ)
    (hℓ : ∀ j, ‖ℓ j‖ ≤ 1) (βs νs a : ℝ) (hβs : 0 ≤ βs) (hνs : 0 ≤ νs) (b : Fin D → ℝ)
    (hρ : 0 < θ * (p * kf0WalkA d g γ / Real.sqrt β))
    (hx : (D : ℝ) * (θ * (p * kf0WalkA d g γ / Real.sqrt β)) ^ 2 ≤ 1 / 4)
    (ψ : Torus d m → W) (hψ : ∀ y, ‖ψ y‖ ≤ p) :
    Summable (fun t => ‖kf0SeriesTerm d m ν β x ℓ (siteCoeff βs νs a b) ψ t‖) ∧
      HasSum (kf0SeriesTerm d m ν β x ℓ (siteCoeff βs νs a b) ψ)
        (∑' α : Fin D → ℕ, siteCoeff βs νs a b α * ∏ j, (ℓ j ((Real.sqrt β)⁻¹ •
          matAct (kf0C d m ν) ψ (x j))) ^ (α j)) := by
  refine kf0SeriesTerm_hasSum hg hgν hγ hq β hp0 hθ x ℓ hℓ (siteCoeff βs νs a b) ?_ ψ hψ
  have := (siteCoeff_maj hβs hνs a b hρ hx).1
  simpa only [Real.norm_eq_abs, mdeg] using this

end Consumer

end Balaban.LargeField.KF0Taylor
