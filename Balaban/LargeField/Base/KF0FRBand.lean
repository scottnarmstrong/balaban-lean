/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Base.KF0FRTerms
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# `KF0FRBand`: pointwise bounds on the terms (route FR, (O2)–(O4), (H1)–(H3))

`notes/phase1/KF0-FR.md` (O), (H). With `t = √(1 - |u|²)`, `w(u) = (1-|u|²)^{-1/2}`:

* `one_sub_tN_le` (O3): `0 ≤ 1 - t ≤ |u|²`; `tN_lt_of_lt` : `t < 7/8` when `|u|² > 1/4`;
* `chartWeight_le_two`, `abs_chartWeight_sub_one_le` (O2): for `|u|² ≤ 1/4`, `w ≤ 2` and
  `|w - 1| ≤ |u|²`;
* `norm_sheetPt_sub_le_two`, `norm_sheetPt_true_sub_le` (O4): `|Φ_σ(u) - h| ≤ 2`, and
  `|Φ_+(u) - h| ≤ 2|u|`;
* `band_split` (H1): `w b(σ) e^{-(βν/2)(s t - 1)²} ≤ 2 Λ(σ) + w Λ'(σ)` with `Λ(+) = 1`,
  `Λ'(+) = e^{-βν/128}`, `Λ(-) = Λ'(-) = ε^{-1} e^{-βν/2}`;
* `sum_sum_abs_mul_le` (H3), `sum_sum_mul_le` (H2): row sums of symmetric kernels over a set of
  rows;
* `norm_frField_le`: `|u_x| ≤ β^{-1/2} ∑_y C_R(x,y) |ψ_y|`.
-/

@[expose] public section

open MeasureTheory Set Matrix Balaban.Green

namespace Balaban.LargeField.KF0FR

open SphereChart

noncomputable section

variable {N : ℕ} (h : EuclideanSpace ℝ (Fin N))

local notation "E" => EuclideanSpace ℝ (Fin N)
local notation "Sph" => Metric.sphere (0 : EuclideanSpace ℝ (Fin N)) 1

/-! ### The normal coordinate and the chart weight -/

theorem tN_nonneg (ξ : perp h) : 0 ≤ tN h ξ := Real.sqrt_nonneg _

/-- **(O3)** `1 - t ≤ |u|²` for `|u| ≤ 1`. -/
theorem one_sub_tN_le {ξ : perp h} (hξ : ‖ξ‖ ≤ 1) : 1 - tN h ξ ≤ ‖ξ‖ ^ 2 := by
  have h0 : 0 ≤ 1 - ‖ξ‖ ^ 2 := by nlinarith [norm_nonneg ξ]
  have h1 : 1 - ‖ξ‖ ^ 2 ≤ tN h ξ := by
    unfold tN
    rw [Real.le_sqrt h0 h0]
    nlinarith
  linarith

theorem tN_le_one (ξ : perp h) : tN h ξ ≤ 1 := by
  unfold tN
  rw [Real.sqrt_le_one]
  nlinarith [sq_nonneg ‖ξ‖]

/-- The normal coordinate is below `7/8` off the inner band `|u|² ≤ 1/4`. -/
theorem tN_lt_of_lt {ξ : perp h} (hξ : 1 / 4 < ‖ξ‖ ^ 2) : tN h ξ < 7 / 8 := by
  unfold tN
  rw [Real.sqrt_lt' (by norm_num)]
  linarith

theorem norm_lt_one_of_sq_le {ξ : perp h} (hξ : ‖ξ‖ ^ 2 ≤ 1 / 4) : ‖ξ‖ < 1 := by
  nlinarith [norm_nonneg ξ]

/-- **(O2)** `w ≤ 2` on the inner band. -/
theorem chartWeight_le_two {ξ : perp h} (hξ : ‖ξ‖ ^ 2 ≤ 1 / 4) : chartWeight h ξ ≤ 2 := by
  unfold chartWeight
  rw [ite_eq_left (norm_lt_one_of_sq_le h hξ)]
  have h1 : 1 / 2 ≤ Real.sqrt (1 - ‖ξ‖ ^ 2) := by
    rw [Real.le_sqrt (by norm_num) (by linarith)]
    linarith
  rw [div_le_iff₀ (by linarith)]
  linarith

/-- **(O2)** `|w - 1| ≤ |u|²` on the inner band. -/
theorem abs_chartWeight_sub_one_le {ξ : perp h} (hξ : ‖ξ‖ ^ 2 ≤ 1 / 4) :
    |chartWeight h ξ - 1| ≤ ‖ξ‖ ^ 2 := by
  unfold chartWeight
  rw [ite_eq_left (norm_lt_one_of_sq_le h hξ)]
  set r := ‖ξ‖ ^ 2 with hr
  have hr0 : 0 ≤ r := sq_nonneg _
  set t := Real.sqrt (1 - r) with ht
  have ht0 : 0 < t := Real.sqrt_pos.2 (by linarith)
  have ht2 : t ^ 2 = 1 - r := Real.sq_sqrt (by linarith)
  have ht1 : t ≤ 1 := by nlinarith
  have hge : 1 ≤ 1 / t := by rw [le_div_iff₀ ht0]; linarith
  have hle : 1 / t ≤ 1 + r := by
    rw [div_le_iff₀ ht0]
    have h5 : 0 ≤ r * (1 - r - r ^ 2) := mul_nonneg hr0 (by nlinarith)
    have hx : 1 ≤ ((1 + r) * t) ^ 2 := by
      rw [mul_pow, ht2]; nlinarith
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 1 + r) ht0.le]
  rw [abs_of_nonneg (by linarith)]
  linarith

/-- **(O4)** The sheet points are unit vectors: `|Φ - h| ≤ 2`. -/
theorem norm_sheetPt_sub_le_two (hh : ‖h‖ = 1) (b : Bool) (ξ : perp h) :
    ‖((sheetPt h hh b ξ : Sph) : E) - h‖ ≤ 2 := by
  have h1 : ‖((sheetPt h hh b ξ : Sph) : E)‖ = 1 := by simp
  calc _ ≤ ‖((sheetPt h hh b ξ : Sph) : E)‖ + ‖h‖ := norm_sub_le _ _
    _ = 2 := by rw [h1, hh]; norm_num

/-- **(O4)** On the upper sheet `|Φ_+(u) - h| ≤ 2|u|`. -/
theorem norm_sheetPt_true_sub_le (hh : ‖h‖ = 1) {ξ : perp h} (hξ : ‖ξ‖ < 1) :
    ‖((sheetPt h hh true ξ : Sph) : E) - h‖ ≤ 2 * ‖ξ‖ := by
  rw [coe_sheetPt h hh true hξ]
  have e : (ξ : E) + (sgn true * tN h ξ) • h - h = (ξ : E) + (tN h ξ - 1) • h := by
    simp only [sgn, ite_true, one_mul, sub_smul, one_smul]; abel
  rw [e]
  have hsq := norm_sq_add_smul h hh ξ (tN h ξ - 1)
  have h1 := one_sub_tN_le h hξ.le
  have h2 : 0 ≤ 1 - tN h ξ := by linarith [tN_le_one h ξ]
  have h3 : (tN h ξ - 1) ^ 2 ≤ ‖ξ‖ ^ 2 := by
    have : ‖ξ‖ ^ 2 ≤ ‖ξ‖ := by nlinarith [norm_nonneg ξ]
    nlinarith
  have h4 : ‖(ξ : E) + (tN h ξ - 1) • h‖ ^ 2 ≤ (2 * ‖ξ‖) ^ 2 := by
    rw [hsq]; nlinarith [sq_nonneg ‖ξ‖]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 h4

/-! ### The band split -/

/-- The inner-band weight of a sheet: `Λ(+) = 1`, `Λ(-) = ε^{-1} e^{-βν/2}`. -/
def bandL (ε β ν : ℝ) (b : Bool) : ℝ := if b then 1 else ε⁻¹ * Real.exp (-(β * ν / 2))

/-- The outer-band weight of a sheet: `Λ'(+) = e^{-βν/128}`, `Λ'(-) = ε^{-1} e^{-βν/2}`. -/
def bandL' (ε β ν : ℝ) (b : Bool) : ℝ :=
  if b then Real.exp (-(β * ν / 128)) else ε⁻¹ * Real.exp (-(β * ν / 2))

theorem bandL_nonneg {ε : ℝ} (hε : 0 ≤ ε) (β ν : ℝ) (b : Bool) : 0 ≤ bandL ε β ν b := by
  unfold bandL; split_ifs <;> positivity

theorem bandL'_nonneg {ε : ℝ} (hε : 0 ≤ ε) (β ν : ℝ) (b : Bool) : 0 ≤ bandL' ε β ν b := by
  unfold bandL'; split_ifs <;> positivity

/-- The lower sheet costs `e^{-βν/2}` against its compensating weight. -/
theorem bW_mul_exp_false_le {ε β ν : ℝ} (hε : 0 ≤ ε) (hβν : 0 ≤ β * ν) (ξ : perp h) :
    bW ε false * Real.exp (-(β * ν / 2) * (sgn false * tN h ξ - 1) ^ 2) ≤
      ε⁻¹ * Real.exp (-(β * ν / 2)) := by
  unfold bW
  simp only [Bool.false_eq_true, ite_false, sgn]
  have ht := tN_nonneg h ξ
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (inv_nonneg.2 hε)
  have : 1 ≤ (-1 * tN h ξ - 1) ^ 2 := by nlinarith
  nlinarith

/-- **(H1) The band split** of the chart weight times the normal mass and the sheet weight. -/
theorem band_split {ε β ν : ℝ} (hε : 0 < ε) (hβν : 0 ≤ β * ν) (σ : Bool) (ξ : perp h) :
    chartWeight h ξ * bW ε σ * Real.exp (-(β * ν / 2) * (sgn σ * tN h ξ - 1) ^ 2) ≤
      2 * bandL ε β ν σ + chartWeight h ξ * bandL' ε β ν σ := by
  have hw0 := chartWeight_nonneg h ξ
  have hL := bandL_nonneg hε.le β ν σ
  have hL' := bandL'_nonneg hε.le β ν σ
  -- the sheet factor is at most `Λ(σ)`, and at most `Λ'(σ)` off the inner band
  have hfac : bW ε σ * Real.exp (-(β * ν / 2) * (sgn σ * tN h ξ - 1) ^ 2) ≤ bandL ε β ν σ := by
    cases σ
    · simpa [bandL] using bW_mul_exp_false_le h hε.le hβν ξ
    · simp only [bW, ite_true, one_mul, bandL]
      exact Real.exp_le_one_iff.2 (by nlinarith [sq_nonneg (sgn true * tN h ξ - 1)])
  by_cases hband : ‖ξ‖ ^ 2 ≤ 1 / 4
  · have hw := chartWeight_le_two h hband
    have hfac0 : 0 ≤ bW ε σ * Real.exp (-(β * ν / 2) * (sgn σ * tN h ξ - 1) ^ 2) := by
      unfold bW; split_ifs <;> positivity
    calc _ = chartWeight h ξ * (bW ε σ * Real.exp (-(β * ν / 2) * (sgn σ * tN h ξ - 1) ^ 2)) := by
          ring
      _ ≤ 2 * bandL ε β ν σ := mul_le_mul hw hfac hfac0 (by norm_num)
      _ ≤ _ := le_add_of_nonneg_right (mul_nonneg hw0 hL')
  · push Not at hband
    have hfac' : bW ε σ * Real.exp (-(β * ν / 2) * (sgn σ * tN h ξ - 1) ^ 2) ≤
        bandL' ε β ν σ := by
      cases σ
      · simpa [bandL'] using bW_mul_exp_false_le h hε.le hβν ξ
      · simp only [bW, ite_true, one_mul, bandL', sgn]
        refine Real.exp_le_exp.2 ?_
        have ht := tN_lt_of_lt h hband
        have : 1 / 64 ≤ (1 * tN h ξ - 1) ^ 2 := by nlinarith [tN_nonneg h ξ]
        nlinarith
    calc _ = chartWeight h ξ * (bW ε σ * Real.exp (-(β * ν / 2) * (sgn σ * tN h ξ - 1) ^ 2)) := by
          ring
      _ ≤ chartWeight h ξ * bandL' ε β ν σ := mul_le_mul_of_nonneg_left hfac' hw0
      _ ≤ _ := le_add_of_nonneg_left (by positivity)

/-! ### Row sums over a set of rows -/

/-- **(H3)** For a symmetric kernel with absolute row sums at most `θ`, and a set `D` of rows whose
supports lie in `W ⊇ D`: `∑_{x∈D} ∑_y |Q(x,y)| |r_x| |r_y| ≤ θ ∑_{y∈W} r_y²`. -/
theorem sum_sum_abs_mul_le {ι : Type*} [Fintype ι] (Q : ι → ι → ℝ) (hQ : ∀ x y, Q x y = Q y x)
    {θ : ℝ} (hrow : ∀ x, ∑ y, |Q x y| ≤ θ) (r : ι → ℝ) {D W : Finset ι} (hDW : D ⊆ W)
    (hsupp : ∀ x ∈ D, ∀ y, Q x y ≠ 0 → y ∈ W) :
    ∑ x ∈ D, ∑ y, |Q x y| * |r x| * |r y| ≤ θ * ∑ y ∈ W, r y ^ 2 := by
  rcases W.eq_empty_or_nonempty with hW | ⟨y0, _⟩
  · have hD : D = ∅ := Finset.subset_empty.1 (hW ▸ hDW)
    simp [hD, hW]
  have hθ : 0 ≤ θ := (Finset.sum_nonneg fun _ _ => abs_nonneg _).trans (hrow y0)
  have hpt : ∀ x y, |Q x y| * |r x| * |r y| ≤ |Q x y| * (r x ^ 2 / 2) + |Q x y| * (r y ^ 2 / 2) := by
    intro x y
    have : |r x| * |r y| ≤ r x ^ 2 / 2 + r y ^ 2 / 2 := by
      nlinarith [sq_nonneg (|r x| - |r y|), sq_abs (r x), sq_abs (r y)]
    nlinarith [abs_nonneg (Q x y)]
  have h1 : ∑ x ∈ D, ∑ y, |Q x y| * (r x ^ 2 / 2) ≤ θ / 2 * ∑ y ∈ W, r y ^ 2 := by
    calc _ = ∑ x ∈ D, (∑ y, |Q x y|) * (r x ^ 2 / 2) := by
          simp_rw [Finset.sum_mul]
      _ ≤ ∑ x ∈ D, θ * (r x ^ 2 / 2) :=
          Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_right (hrow x) (by positivity)
      _ ≤ ∑ x ∈ W, θ * (r x ^ 2 / 2) :=
          Finset.sum_le_sum_of_subset_of_nonneg hDW fun _ _ _ => by positivity
      _ = θ / 2 * ∑ y ∈ W, r y ^ 2 := by rw [Finset.mul_sum]; ring_nf
  have h2 : ∑ x ∈ D, ∑ y, |Q x y| * (r y ^ 2 / 2) ≤ θ / 2 * ∑ y ∈ W, r y ^ 2 := by
    have hz : ∀ x ∈ D, ∑ y, |Q x y| * (r y ^ 2 / 2) = ∑ y ∈ W, |Q x y| * (r y ^ 2 / 2) := by
      intro x hx
      refine (Finset.sum_subset (Finset.subset_univ W) fun y _ hy => ?_).symm
      have : Q x y = 0 := by
        by_contra hne; exact hy (hsupp x hx y hne)
      simp [this]
    rw [Finset.sum_congr rfl hz, Finset.sum_comm]
    calc ∑ y ∈ W, ∑ x ∈ D, |Q x y| * (r y ^ 2 / 2)
        = ∑ y ∈ W, (∑ x ∈ D, |Q y x|) * (r y ^ 2 / 2) := by
          refine Finset.sum_congr rfl fun y _ => ?_
          rw [Finset.sum_mul]
          exact Finset.sum_congr rfl fun x _ => by rw [hQ x y]
      _ ≤ ∑ y ∈ W, θ * (r y ^ 2 / 2) := by
          refine Finset.sum_le_sum fun y _ => mul_le_mul_of_nonneg_right ?_ (by positivity)
          exact (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ D)
            fun _ _ _ => abs_nonneg _).trans (hrow y)
      _ = θ / 2 * ∑ y ∈ W, r y ^ 2 := by rw [Finset.mul_sum]; ring_nf
  calc _ ≤ ∑ x ∈ D, ∑ y, (|Q x y| * (r x ^ 2 / 2) + |Q x y| * (r y ^ 2 / 2)) :=
        Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ => hpt x y
    _ = ∑ x ∈ D, ∑ y, |Q x y| * (r x ^ 2 / 2) + ∑ x ∈ D, ∑ y, |Q x y| * (r y ^ 2 / 2) := by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun x _ => Finset.sum_add_distrib
    _ ≤ θ / 2 * ∑ y ∈ W, r y ^ 2 + θ / 2 * ∑ y ∈ W, r y ^ 2 := add_le_add h1 h2
    _ = θ * ∑ y ∈ W, r y ^ 2 := by ring

/-- **(H2)** For a symmetric nonnegative kernel with row sums at most `c`, and a set `D` of rows
whose supports lie in `W`: `∑_{x∈D} ∑_y C(x,y) r_y ≤ c ∑_{y∈W} r_y` for `r ≥ 0`. -/
theorem sum_sum_mul_le {ι : Type*} [Fintype ι] (C : ι → ι → ℝ) (hC0 : ∀ x y, 0 ≤ C x y)
    (hCs : ∀ x y, C x y = C y x) {c : ℝ} (hrow : ∀ x, ∑ y, C x y ≤ c) (r : ι → ℝ)
    (hr : ∀ y, 0 ≤ r y) {D W : Finset ι} (hsupp : ∀ x ∈ D, ∀ y, C x y ≠ 0 → y ∈ W) :
    ∑ x ∈ D, ∑ y, C x y * r y ≤ c * ∑ y ∈ W, r y := by
  have hz : ∀ x ∈ D, ∑ y, C x y * r y = ∑ y ∈ W, C x y * r y := by
    intro x hx
    refine (Finset.sum_subset (Finset.subset_univ W) fun y _ hy => ?_).symm
    have : C x y = 0 := by
      by_contra hne; exact hy (hsupp x hx y hne)
    simp [this]
  rw [Finset.sum_congr rfl hz, Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_le_sum fun y _ => ?_
  rw [← Finset.sum_mul]
  refine mul_le_mul_of_nonneg_right ?_ (hr y)
  calc ∑ x ∈ D, C x y = ∑ x ∈ D, C y x := Finset.sum_congr rfl fun x _ => hCs x y
    _ ≤ ∑ x, C y x := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ D)
        fun x _ _ => hC0 y x
    _ ≤ c := hrow y

/-! ### The whitened field -/

variable {d ℓ : ℕ} [NeZero ℓ]

/-- `|u_x| ≤ β^{-1/2} ∑_y C_R(x,y) |ψ_y|`. -/
theorem norm_frField_le {β ν : ℝ} (hν : 0 < ν) (R : ℕ) (ψ : Torus d ℓ → perp h)
    (x : Torus d ℓ) :
    ‖frField d ℓ β ν R ψ x‖ ≤ (Real.sqrt β)⁻¹ * ∑ y, kf0CR d ℓ ν R x y * ‖ψ y‖ := by
  unfold frField matAct
  refine (norm_sum_le _ _).trans ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun y _ => ?_
  rw [norm_smul, Matrix.smul_apply, smul_eq_mul, Real.norm_eq_abs, abs_mul,
    abs_of_nonneg (inv_nonneg.2 (Real.sqrt_nonneg β)), abs_of_nonneg (kf0CR_nonneg hν R x y)]
  ring_nf
  rfl

/-- **(O1)** If `|ψ_y| ≤ p` wherever `C_R(x,y) ≠ 0`, then `|u_x| ≤ β^{-1/2} ν^{-1/2} p`. -/
theorem norm_frField_le_of_small {β ν p : ℝ} (hν : 0 < ν) (hp : 0 ≤ p) (R : ℕ)
    (ψ : Torus d ℓ → perp h) (x : Torus d ℓ)
    (hψ : ∀ y, kf0CR d ℓ ν R x y ≠ 0 → ‖ψ y‖ ≤ p) :
    ‖frField d ℓ β ν R ψ x‖ ≤ (Real.sqrt β)⁻¹ * ((Real.sqrt ν)⁻¹ * p) := by
  refine (norm_frField_le h hν R ψ x).trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
  calc ∑ y, kf0CR d ℓ ν R x y * ‖ψ y‖ ≤ ∑ y, kf0CR d ℓ ν R x y * p := by
        refine Finset.sum_le_sum fun y _ => ?_
        by_cases hy : kf0CR d ℓ ν R x y = 0
        · rw [hy, zero_mul, zero_mul]
        · exact mul_le_mul_of_nonneg_left (hψ y hy) (kf0CR_nonneg hν R x y)
    _ = (∑ y, kf0CR d ℓ ν R x y) * p := by rw [Finset.sum_mul]
    _ ≤ (Real.sqrt ν)⁻¹ * p := by
        refine mul_le_mul_of_nonneg_right ?_ hp
        have := kf0CR_rowAbs_le (d := d) (m := ℓ) hν R x
        simpa [abs_of_nonneg (kf0CR_nonneg hν R x _)] using this

end

end Balaban.LargeField.KF0FR
