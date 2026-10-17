/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Regime.A0PrimeRadiusWeight
public import Balaban.LargeField.Regime.A0PrimeReserve
public import Balaban.SmallField.Def6v2Regime
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.GCongr

/-!
# Transport of the source tube and one failed directional test

The source is measured in the common physical field `h`.  At scale `j`, the squared field
radius is `c² / (β_j μ_j)`.  Its inclusion in the earlier tube follows from monotonicity of
`β_j μ_j`; no analytic activity estimate is assumed.
-/

@[expose] public section

namespace Balaban.LargeField

/-- The small running-error allowance is strictly below one scale of mass times coupling. -/
theorem running_exp_four_error_lt_scale {d L : ℕ} {β ν a ε : ℝ} {b n : ℕ → ℝ}
    (h : RunningHyp d L β ν a ε b n) :
    Real.exp (4 * ε) < (L : ℝ) ^ d := by
  have he0 : 0 ≤ 4 * ε := mul_nonneg (by norm_num) h.hε0
  have he2 : 4 * ε < 2 := by linarith [h.hε]
  have hfrac : (2 + 4 * ε) / (2 - 4 * ε) < 2 := by
    apply (div_lt_iff₀ (by linarith : 0 < 2 - 4 * ε)).mpr
    linarith [h.hε]
  have hL : (1 : ℝ) ≤ L := by exact_mod_cast (by have := h.hL; omega : 1 ≤ L)
  have hLd : (2 : ℝ) ≤ (L : ℝ) ^ d := by
    have h2 : (2 : ℝ) ≤ L := by exact_mod_cast h.hL
    calc
      (2 : ℝ) ≤ L := h2
      _ = (L : ℝ) ^ 1 := by ring
      _ ≤ (L : ℝ) ^ d := pow_le_pow_right₀ hL (by have := h.hd; omega)
  exact (Real.exp_le_two_add_div_two_sub he0 he2).trans_lt (hfrac.trans_le hLd)

/-- The product `β_k ν_k` increases strictly at every running step.  This is the
scale fact behind the shrinking radius in the physical field `h`. -/
theorem running_beta_mass_lt_succ {d L : ℕ} {β ν a ε : ℝ} {b n : ℕ → ℝ}
    (h : RunningHyp d L β ν a ε b n) (k : ℕ) :
    b k * n k < b (k + 1) * n (k + 1) := by
  obtain ⟨γ, δ, hγ, hδ, hlγ, hlδ, he⟩ := h.beta_mul_nu_eq k
  obtain ⟨γ', δ', hγ', hδ', hlγ', hlδ', he'⟩ := h.beta_mul_nu_eq (k + 1)
  have htop : γ * δ ≤ Real.exp (2 * ε) :=
    RunningHyp.gamma_mul_delta_le hγ hδ hlγ hlδ
  have hbot : Real.exp (-(2 * ε)) ≤ γ' * δ' := by
    rw [show -(2 * ε) = -ε + -ε by ring, Real.exp_add]
    exact mul_le_mul
      (Balaban.SmallField.Def6v2.exp_neg_le_of_abs_log hγ' hlγ')
      (Balaban.SmallField.Def6v2.exp_neg_le_of_abs_log hδ' hlδ')
      (Real.exp_pos _).le hγ'.le
  have hgap : Real.exp (2 * ε) < (L : ℝ) ^ d * Real.exp (-(2 * ε)) := by
    have hh := mul_lt_mul_of_pos_right (running_exp_four_error_lt_scale h)
      (Real.exp_pos (-(2 * ε)))
    rw [← Real.exp_add] at hh
    simpa only [show 4 * ε + -(2 * ε) = 2 * ε by ring] using hh
  have hcomp : γ * δ < (L : ℝ) ^ d * (γ' * δ') := by
    calc γ * δ ≤ Real.exp (2 * ε) := htop
      _ < (L : ℝ) ^ d * Real.exp (-(2 * ε)) := hgap
      _ ≤ (L : ℝ) ^ d * (γ' * δ') :=
        mul_le_mul_of_nonneg_left hbot (by positivity)
  have hprefix : 0 < β * ν * (L : ℝ) ^ (k * d) := by
    have hL0 : (0 : ℝ) < L := by exact_mod_cast (by have := h.hL; omega : 0 < L)
    exact mul_pos (mul_pos h.hβ h.hν) (pow_pos hL0 _)
  have hscaled := mul_lt_mul_of_pos_left hcomp hprefix
  rw [he, he']
  have hpow : (L : ℝ) ^ ((k + 1) * d) = (L : ℝ) ^ (k * d) * (L : ℝ) ^ d := by
    rw [show (k + 1) * d = k * d + d by ring, pow_add]
  rw [hpow]
  nlinarith [hscaled]

/-- A later physical field tube is contained in every earlier tube once `β_j μ_j` increases.
The corresponding radius in `b_j = μ_j h` is `c √(μ_j / β_j)`. -/
theorem source_radius_transport {N : ℕ} (h h₀ : Fin N → ℂ)
    {βj βk μj μk c : ℝ} (hβj : 0 < βj) (hβk : 0 < βk)
    (hμj : 0 < μj) (hμk : 0 < μk)
    (hprod : βj * μj ≤ βk * μk)
    (hlater : (∑ i, ‖h i - h₀ i‖ ^ 2) ≤ c ^ 2 / (βk * μk)) :
    (∑ i, ‖h i - h₀ i‖ ^ 2) ≤ c ^ 2 / (βj * μj) := by
  apply hlater.trans
  apply (div_le_div_iff₀ (mul_pos hβk hμk) (mul_pos hβj hμj)).mpr
  nlinarith [mul_nonneg (sq_nonneg c) (sub_nonneg.mpr hprod)]

/-- The physical field tube at step `k + 1` lies in the tube at step `k` under the
landed running-coefficient hypotheses. -/
theorem running_source_radius_transport_succ {d L N : ℕ} {β ν a ε : ℝ}
    {b n : ℕ → ℝ} (hRun : RunningHyp d L β ν a ε b n)
    (k : ℕ) (h h₀ : Fin N → ℂ) (c : ℝ)
    (hlater : (∑ i, ‖h i - h₀ i‖ ^ 2) ≤ c ^ 2 / (b (k + 1) * n (k + 1))) :
    (∑ i, ‖h i - h₀ i‖ ^ 2) ≤ c ^ 2 / (b k * n k) := by
  have hnu : ∀ j, 0 < n j := by
    intro j
    obtain ⟨δ, hδ, -, he⟩ := hRun.nu_eq j
    rw [he]
    have hL : (0 : ℝ) < L := by exact_mod_cast (by have := hRun.hL; omega : 0 < L)
    exact mul_pos (mul_pos hRun.hν (pow_pos hL _)) hδ
  exact source_radius_transport h h₀ (hRun.betaRun_pos k) (hRun.betaRun_pos (k + 1))
    (hnu k) (hnu (k + 1)) (running_beta_mass_lt_succ hRun k).le hlater

/-- The real-part budget of a single failed directional coordinate.  The condition
`δ² ≤ μ x²` is the failed real test, and `u²+v² ≤ c² μ/β` is the transverse source tube.
The result retains one eighth of `δ²` before the imaginary source cost. -/
theorem failed_direction_scalar_re {μ β δ c x u v : ℝ}
    (hμ : 0 < μ) (hβ : 0 < β)
    (hfail : δ ^ 2 ≤ μ * x ^ 2)
    (hsource : u ^ 2 + v ^ 2 ≤ c ^ 2 * μ / β)
    (hc : 4 * c ^ 2 ≤ β * δ ^ 2) :
    δ ^ 2 / 8 - c ^ 2 / (2 * β) ≤
      μ / 2 * ((x - u / μ) ^ 2 - (v / μ) ^ 2) := by
  have hu : u ^ 2 ≤ c ^ 2 * μ / β := by nlinarith [sq_nonneg v]
  have hv : v ^ 2 ≤ c ^ 2 * μ / β := by nlinarith [sq_nonneg u]
  have huβ : β * u ^ 2 ≤ c ^ 2 * μ := by
    apply (le_div_iff₀ hβ).mp at hu
    nlinarith [hu]
  have hcoef : 4 * c ^ 2 * μ ≤ β * δ ^ 2 * μ :=
    mul_le_mul_of_nonneg_right hc hμ.le
  have hureal : 4 * u ^ 2 ≤ μ * δ ^ 2 := by
    have h1 : β * (4 * u ^ 2) ≤ β * (μ * δ ^ 2) := by nlinarith [huβ]
    exact (mul_le_mul_iff_of_pos_left hβ).mp h1
  have hx : δ ^ 2 / μ ≤ x ^ 2 := by
    apply (div_le_iff₀ hμ).mpr
    nlinarith [hfail]
  have hy : (u / μ) ^ 2 ≤ δ ^ 2 / (4 * μ) := by
    rw [div_pow]
    apply (div_le_div_iff₀ (show 0 < μ ^ 2 by positivity)
      (show 0 < 4 * μ by positivity)).mpr
    nlinarith [mul_le_mul_of_nonneg_right hureal hμ.le]
  have hreverse : x ^ 2 / 2 - (u / μ) ^ 2 ≤ (x - u / μ) ^ 2 := by
    nlinarith [sq_nonneg (x - 2 * (u / μ))]
  have hreal : δ ^ 2 / (4 * μ) ≤ (x - u / μ) ^ 2 := by
    have he : δ ^ 2 / (4 * μ) = (δ ^ 2 / μ) / 4 := by ring
    rw [he] at hy ⊢
    linarith
  have hcost : μ / 2 * (v / μ) ^ 2 ≤ c ^ 2 / (2 * β) := by
    have he : μ / 2 * (v / μ) ^ 2 = v ^ 2 / (2 * μ) := by field_simp
    rw [he]
    apply (div_le_div_iff₀ (show 0 < 2 * μ by positivity)
      (show 0 < 2 * β by positivity)).mpr
    have hvβ : β * v ^ 2 ≤ c ^ 2 * μ := by
      simpa [mul_comm] using (le_div_iff₀ hβ).mp hv
    nlinarith [hvβ]
  have hreal2 := mul_le_mul_of_nonneg_left hreal (show 0 ≤ μ / 2 by positivity)
  have he : μ / 2 * (δ ^ 2 / (4 * μ)) = δ ^ 2 / 8 := by
    field_simp
    ring
  rw [he] at hreal2
  nlinarith [hreal2]

/-- The complex one-coordinate mass weight on a failed real direction test.  The exponent
keeps `β δ² / 8` of the Peierls reserve and pays `c² / 2` for the imaginary source. -/
theorem failed_direction_scalar_weight {μ β δ c x : ℝ} {q : ℂ}
    (hμ : 0 < μ) (hβ : 0 < β)
    (hfail : δ ^ 2 ≤ μ * x ^ 2)
    (hq : ‖q‖ ^ 2 ≤ c ^ 2 * μ / β)
    (hc : 4 * c ^ 2 ≤ β * δ ^ 2) :
    ‖Complex.exp (-((β : ℂ) * (((μ / 2 : ℝ) : ℂ) * (((x : ℂ) - q / μ) ^ 2))))‖ ≤
      Real.exp (-(β * δ ^ 2 / 8) + c ^ 2 / 2) := by
  have hqre : q.re ^ 2 + q.im ^ 2 ≤ c ^ 2 * μ / β := by
    rw [Complex.sq_norm, Complex.normSq_apply] at hq
    nlinarith [hq]
  have hmass : ((((μ / 2 : ℝ) : ℂ) * (((x : ℂ) - q / μ) ^ 2))).re =
      μ / 2 * ((x - q.re / μ) ^ 2 - (q.im / μ) ^ 2) := by
    have hre : ((x : ℂ) - q / μ).re = x - q.re / μ := by
      simp [Complex.sub_re, Complex.div_ofReal_re]
    have him : ((x : ℂ) - q / μ).im = -(q.im / μ) := by
      simp [Complex.sub_im, Complex.div_ofReal_im]
    rw [Complex.re_ofReal_mul, sq, Complex.mul_re, hre, him]
    ring
  rw [Complex.norm_exp]
  apply Real.exp_le_exp.mpr
  have h1 := failed_direction_scalar_re hμ hβ hfail hqre hc
  simp only [Complex.neg_re, Complex.re_ofReal_mul, hmass]
  have hm := mul_le_mul_of_nonneg_left h1 hβ.le
  have he : β * (c ^ 2 / (2 * β)) = c ^ 2 / 2 := by field_simp
  rw [mul_sub, he] at hm
  nlinarith [hm]

/-- The same failed-test reserve for an `N`-component real direction defect.  The real
source increment and the imaginary increment are both charged to the single Euclidean
source tube; no factor of `N` occurs. -/
theorem failed_direction_vector_re {N : ℕ} (u : Fin N → ℝ) (q : Fin N → ℂ)
    {μ β δ c : ℝ} (hμ : 0 < μ) (hβ : 0 < β)
    (hfail : δ ^ 2 ≤ μ * ∑ i, u i ^ 2)
    (hq : (∑ i, ‖q i‖ ^ 2) ≤ c ^ 2 * μ / β)
    (hc : 4 * c ^ 2 ≤ β * δ ^ 2) :
    δ ^ 2 / 8 - c ^ 2 / (2 * β) ≤
      μ / 2 * ∑ i, ((u i - (q i).re / μ) ^ 2 - ((q i).im / μ) ^ 2) := by
  have hqsum : (∑ i, (q i).re ^ 2) + (∑ i, (q i).im ^ 2) ≤
      c ^ 2 * μ / β := by
    have he : ∀ i, (q i).re ^ 2 + (q i).im ^ 2 = ‖q i‖ ^ 2 := by
      intro i
      rw [Complex.sq_norm, Complex.normSq_apply]
      ring
    have hs : (∑ i, ((q i).re ^ 2 + (q i).im ^ 2)) ≤ c ^ 2 * μ / β := by
      simpa only [he] using hq
    simpa only [Finset.sum_add_distrib] using hs
  have hU : (∑ i, (q i).re ^ 2) ≤ c ^ 2 * μ / β := by
    have hv0 : 0 ≤ ∑ i, (q i).im ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
    linarith
  have hV : (∑ i, (q i).im ^ 2) ≤ c ^ 2 * μ / β := by
    have hu0 : 0 ≤ ∑ i, (q i).re ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
    linarith
  have hUβ : β * (∑ i, (q i).re ^ 2) ≤ c ^ 2 * μ := by
    have hh := (le_div_iff₀ hβ).mp hU
    nlinarith [hh]
  have hcoef : 4 * c ^ 2 * μ ≤ β * δ ^ 2 * μ :=
    mul_le_mul_of_nonneg_right hc hμ.le
  have hUreal : 4 * (∑ i, (q i).re ^ 2) ≤ μ * δ ^ 2 := by
    apply (mul_le_mul_iff_of_pos_left hβ).mp
    nlinarith [hUβ]
  have hfail' : δ ^ 2 / μ ≤ ∑ i, u i ^ 2 := by
    apply (div_le_iff₀ hμ).mpr
    nlinarith [hfail]
  have hUy : (∑ i, ((q i).re / μ) ^ 2) ≤ δ ^ 2 / (4 * μ) := by
    have he : (∑ i, ((q i).re / μ) ^ 2) =
        (∑ i, (q i).re ^ 2) / μ ^ 2 := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [he]
    apply (div_le_div_iff₀ (show 0 < μ ^ 2 by positivity)
      (show 0 < 4 * μ by positivity)).mpr
    nlinarith [mul_le_mul_of_nonneg_right hUreal hμ.le]
  have hreverse : (∑ i, u i ^ 2) / 2 - (∑ i, ((q i).re / μ) ^ 2) ≤
      ∑ i, (u i - (q i).re / μ) ^ 2 := by
    have hp : ∀ i, u i ^ 2 / 2 - ((q i).re / μ) ^ 2 ≤
        (u i - (q i).re / μ) ^ 2 := by
      intro i
      nlinarith [sq_nonneg (u i - 2 * ((q i).re / μ))]
    have hs := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hp i)
    simpa only [Finset.sum_sub_distrib, Finset.sum_div] using hs
  have hreal : δ ^ 2 / (4 * μ) ≤ ∑ i, (u i - (q i).re / μ) ^ 2 := by
    have he : δ ^ 2 / (4 * μ) = (δ ^ 2 / μ) / 4 := by ring
    rw [he] at hUy ⊢
    linarith
  have hcost : μ / 2 * (∑ i, ((q i).im / μ) ^ 2) ≤ c ^ 2 / (2 * β) := by
    have he : μ / 2 * (∑ i, ((q i).im / μ) ^ 2) =
        (∑ i, (q i).im ^ 2) / (2 * μ) := by
      have hsum : (∑ i, ((q i).im / μ) ^ 2) =
          (∑ i, (q i).im ^ 2) / μ ^ 2 := by
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro i _
        ring
      rw [hsum]
      field_simp
    rw [he]
    apply (div_le_div_iff₀ (show 0 < 2 * μ by positivity)
      (show 0 < 2 * β by positivity)).mpr
    have hvβ : β * (∑ i, (q i).im ^ 2) ≤ c ^ 2 * μ := by
      simpa [mul_comm] using (le_div_iff₀ hβ).mp hV
    nlinarith [hvβ]
  have hsumDiff : (∑ i, ((u i - (q i).re / μ) ^ 2 - ((q i).im / μ) ^ 2)) =
      (∑ i, (u i - (q i).re / μ) ^ 2) -
        (∑ i, ((q i).im / μ) ^ 2) := by
    rw [Finset.sum_sub_distrib]
  rw [hsumDiff]
  have hreal2 := mul_le_mul_of_nonneg_left hreal (show 0 ≤ μ / 2 by positivity)
  have he : μ / 2 * (δ ^ 2 / (4 * μ)) = δ ^ 2 / 8 := by
    field_simp
    ring
  rw [he] at hreal2
  nlinarith [hreal2, hcost]

/-- The full vector mass weight for one failed directional test, with one Euclidean
source charge and no dimension factor in the exponent. -/
theorem failed_direction_vector_weight {N : ℕ} (u : Fin N → ℝ) (q : Fin N → ℂ)
    {μ β δ c : ℝ} (hμ : 0 < μ) (hβ : 0 < β)
    (hfail : δ ^ 2 ≤ μ * ∑ i, u i ^ 2)
    (hq : (∑ i, ‖q i‖ ^ 2) ≤ c ^ 2 * μ / β)
    (hc : 4 * c ^ 2 ≤ β * δ ^ 2) :
    ‖Complex.exp (-((β : ℂ) * (((μ / 2 : ℝ) : ℂ) *
      ∑ i, (((u i : ℝ) : ℂ) - q i / μ) ^ 2)))‖ ≤
      Real.exp (-(β * δ ^ 2 / 8) + c ^ 2 / 2) := by
  have hmass : ((((μ / 2 : ℝ) : ℂ) *
      ∑ i, (((u i : ℝ) : ℂ) - q i / μ) ^ 2)).re =
      μ / 2 * ∑ i, ((u i - (q i).re / μ) ^ 2 - ((q i).im / μ) ^ 2) := by
    rw [Complex.re_ofReal_mul, Complex.re_sum, Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    have hre : ((((u i : ℝ) : ℂ) - q i / μ)).re = u i - (q i).re / μ := by
      simp [Complex.sub_re, Complex.div_ofReal_re]
    have him : ((((u i : ℝ) : ℂ) - q i / μ)).im = -((q i).im / μ) := by
      simp [Complex.sub_im, Complex.div_ofReal_im]
    rw [sq, Complex.mul_re, hre, him]
    ring
  rw [Complex.norm_exp]
  apply Real.exp_le_exp.mpr
  have h1 := failed_direction_vector_re u q hμ hβ hfail hq hc
  simp only [Complex.neg_re, Complex.re_ofReal_mul, hmass]
  have hm := mul_le_mul_of_nonneg_left h1 hβ.le
  have he : β * (c ^ 2 / (2 * β)) = c ^ 2 / 2 := by field_simp
  rw [mul_sub, he] at hm
  nlinarith [hm]

/-- The number of cubes read by the extended direction stencil is bounded by its
polynomial collar majorant. -/
theorem extended_collar_count_le (d : ℕ) {Rb lamPrev : ℝ}
    (hRb : 0 < Rb) (h1 : 1 ≤ lamPrev) :
    (2 * (2 * (⌊Rb * lamPrev ^ 2⌋₊ : ℝ) + 3) + 1) ^ d ≤
      (4 * Rb + 7) ^ d * lamPrev ^ (2 * d) := by
  have hl2 : 1 ≤ lamPrev ^ 2 := one_le_pow₀ h1
  have hfl : (⌊Rb * lamPrev ^ 2⌋₊ : ℝ) ≤ Rb * lamPrev ^ 2 :=
    Nat.floor_le (by positivity)
  have hbase : 2 * (2 * (⌊Rb * lamPrev ^ 2⌋₊ : ℝ) + 3) + 1 ≤
      (4 * Rb + 7) * lamPrev ^ 2 := by nlinarith
  calc
    (2 * (2 * (⌊Rb * lamPrev ^ 2⌋₊ : ℝ) + 3) + 1) ^ d ≤
        ((4 * Rb + 7) * lamPrev ^ 2) ^ d :=
      pow_le_pow_left₀ (by positivity) hbase d
    _ = (4 * Rb + 7) ^ d * lamPrev ^ (2 * d) := by rw [mul_pow, ← pow_mul]

/-- A counted collar, **including the failed site**, leaves half of the one-test gain.
The input `hcharge` is the explicit large-`β` threshold of Part II (17).  `Csite` and
`Cold` remain named physical input constants: their values require the actual kernels. -/
theorem failed_test_collar_reserve (d p0 : ℕ) (hp : d ≤ p0)
    {a A0 lam Csite Cold c Cj J : ℝ}
    (ha : 0 < a) (hlam : 0 ≤ lam) (hCsite : 0 ≤ Csite) (hCold : 0 ≤ Cold)
    (hsize : J ≤ Cj * lam ^ (2 * d))
    (hcharge : 16 * a * Cj * (c ^ 2 * Csite / 2 + Cold) ≤
      A0 ^ 2 * lam ^ (2 * (p0 - d))) :
    -(A0 ^ 2 * lam ^ (2 * p0) / (8 * a)) +
        (c ^ 2 * Csite / 2 + Cold) * J ≤
      -(A0 ^ 2 * lam ^ (2 * p0) / (16 * a)) := by
  have hC : 0 ≤ c ^ 2 * Csite / 2 + Cold := by positivity
  have hpow : 2 * (p0 - d) + 2 * d = 2 * p0 := by omega
  have hpay : 16 * a * (c ^ 2 * Csite / 2 + Cold) * J ≤ A0 ^ 2 * lam ^ (2 * p0) := by
    calc
      _ ≤ 16 * a * (c ^ 2 * Csite / 2 + Cold) * (Cj * lam ^ (2 * d)) := by
        gcongr
      _ = (16 * a * Cj * (c ^ 2 * Csite / 2 + Cold)) * lam ^ (2 * d) := by ring
      _ ≤ (A0 ^ 2 * lam ^ (2 * (p0 - d))) * lam ^ (2 * d) :=
        mul_le_mul_of_nonneg_right hcharge (pow_nonneg hlam _)
      _ = A0 ^ 2 * lam ^ (2 * p0) := by
        rw [mul_assoc, ← pow_add, hpow]
  have hpay' : (c ^ 2 * Csite / 2 + Cold) * J ≤
      A0 ^ 2 * lam ^ (2 * p0) / (16 * a) := by
    apply (le_div_iff₀ (by positivity : 0 < 16 * a)).mpr
    nlinarith [hpay]
  have he : A0 ^ 2 * lam ^ (2 * p0) / (8 * a) =
      2 * (A0 ^ 2 * lam ^ (2 * p0) / (16 * a)) := by
    field_simp
    ring
  rw [he]
  linarith

/-- The reserve theorem for the actual floor-defined collar.  The source cost is counted
over **all** charged mass sites, including the failed site. -/
theorem failed_test_extended_collar_reserve (d p0 : ℕ) (hp : d ≤ p0)
    {Rb a A0 lamPrev lam Csite Cold c : ℝ}
    (hRb : 0 < Rb) (ha : 0 < a) (h1 : 1 ≤ lamPrev)
    (hmono : lamPrev ≤ lam) (hCsite : 0 ≤ Csite) (hCold : 0 ≤ Cold)
    (hcharge : 16 * a * (4 * Rb + 7) ^ d * (c ^ 2 * Csite / 2 + Cold) ≤
      A0 ^ 2 * lamPrev ^ (2 * (p0 - d))) :
    -(A0 ^ 2 * lam ^ (2 * p0) / (8 * a)) +
        (c ^ 2 * Csite / 2 + Cold) *
          (2 * (2 * (⌊Rb * lamPrev ^ 2⌋₊ : ℝ) + 3) + 1) ^ d ≤
      -(A0 ^ 2 * lam ^ (2 * p0) / (16 * a)) := by
  have hCj : 0 ≤ (4 * Rb + 7) ^ d := by positivity
  have hsize := extended_collar_count_le d hRb h1
  have hsize' : (2 * (2 * (⌊Rb * lamPrev ^ 2⌋₊ : ℝ) + 3) + 1) ^ d ≤
      (4 * Rb + 7) ^ d * lam ^ (2 * d) := by
    calc
      _ ≤ (4 * Rb + 7) ^ d * lamPrev ^ (2 * d) := hsize
      _ ≤ (4 * Rb + 7) ^ d * lam ^ (2 * d) := by gcongr
  have hcharge' : 16 * a * (4 * Rb + 7) ^ d * (c ^ 2 * Csite / 2 + Cold) ≤
      A0 ^ 2 * lam ^ (2 * (p0 - d)) := by
    apply hcharge.trans
    gcongr
  exact failed_test_collar_reserve d p0 hp ha (by linarith) hCsite hCold hsize' hcharge'

end Balaban.LargeField
