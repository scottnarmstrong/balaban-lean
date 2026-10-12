/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Def7v2Corr
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The elementary estimates of the grouped regional bound (Q13 round 22, sections 2 and 3)

These are the arithmetic parts of the grouped regional bound only.  The inputs they are applied
to (the halo distance `regionalHaloDistance`, the coefficient tails, the polymer counts and the
data bounds of the small-field class) are **not** proved here; every statement below is an
unconditional inequality under explicit numeric hypotheses.

* (E), (F), (T): the exponential against a power, `exp (-t) ≤ (p/e)^p t^(-p)`, and its two uses,
  the far term (6) and the omitted-polymer tail (8).
* (V): the source term (5).  `unit_sub_le` / `source_sub_le` / `inner_unit_sub` are the three
  steps, `source_term_le` the bound `|b · (u_x - u_y)| ≤ 8 (D² + D) σ³ ε²` for real vectors, and
  `dotC_source_term_le` the complex version for the bilinear `dot` and `unitDirC` in the `ℓ²` norm.
* (S): the scale powers (7).  (G): the geometric sum.  (C): the charge per new cube.
* The exponent relations of the note are verified symbolically, and each lemma is instantiated at
  `d = 3`, `γ = 1/8`, `α = 3/8`, `α₁ = 1/4`, `α₃ = 1/2`.
-/

@[expose] public section

namespace Balaban.LargeField.RegionalArith

open Real

/-! ### (E), (F), (T): the exponential against a power -/

/-- (E): `exp (-t) ≤ (p/e)^p t^(-p)` for `p, t > 0`. -/
theorem exp_neg_le_rpow {p t : ℝ} (hp : 0 < p) (ht : 0 < t) :
    exp (-t) ≤ (p / exp 1) ^ p * t ^ (-p) := by
  have h1 : t / p ≤ exp (t / p - 1) := by
    have := Real.add_one_le_exp (t / p - 1); linarith
  have h2 : exp 1 * (t / p) ≤ exp (t / p) := by
    have : exp (t / p) = exp 1 * exp (t / p - 1) := by rw [← Real.exp_add]; ring_nf
    rw [this]
    exact mul_le_mul_of_nonneg_left h1 (Real.exp_pos 1).le
  have h3 : (exp 1 * (t / p)) ^ p ≤ exp t := by
    calc (exp 1 * (t / p)) ^ p ≤ exp (t / p) ^ p :=
          Real.rpow_le_rpow (by positivity) h2 hp.le
      _ = exp t := by rw [← Real.exp_mul]; congr 1; field_simp
  have h4 : 0 < (exp 1 * (t / p)) ^ p := by positivity
  have h5 : exp (-t) ≤ ((exp 1 * (t / p)) ^ p)⁻¹ := by
    rw [Real.exp_neg]; exact inv_anti₀ h4 h3
  refine h5.trans (le_of_eq ?_)
  rw [Real.rpow_neg ht.le, Real.mul_rpow (by positivity) (by positivity),
    Real.div_rpow ht.le hp.le, Real.div_rpow hp.le (Real.exp_pos 1).le]
  have : (exp 1) ^ p ≠ 0 := by positivity
  have : p ^ p ≠ 0 := by positivity
  have : t ^ p ≠ 0 := by positivity
  field_simp

/-- (E) with a scale: `exp (-(κ/s)) ≤ (p/(e κ₀))^p s^p` for `κ ≥ κ₀ > 0`, `s > 0`, `p > 0`. -/
theorem exp_neg_div_le {p s κ κ₀ : ℝ} (hp : 0 < p) (hs : 0 < s) (hκ₀ : 0 < κ₀) (hκ : κ₀ ≤ κ) :
    exp (-(κ / s)) ≤ (p / (exp 1 * κ₀)) ^ p * s ^ p := by
  have hκp : 0 < κ := hκ₀.trans_le hκ
  have h := exp_neg_le_rpow hp (div_pos hκp hs)
  refine h.trans ?_
  have h6 : (κ / s) ^ (-p) = (s / κ) ^ p := by
    rw [Real.rpow_neg (by positivity), ← Real.inv_rpow (by positivity), inv_div]
  have h7 : (s / κ) ^ p ≤ (s / κ₀) ^ p :=
    Real.rpow_le_rpow (by positivity) (div_le_div_of_nonneg_left hs.le hκ₀ hκ) hp.le
  have h8 : (p / exp 1) ^ p * (s / κ₀) ^ p = (p / (exp 1 * κ₀)) ^ p * s ^ p := by
    rw [← Real.mul_rpow (by positivity) (by positivity),
      ← Real.mul_rpow (by positivity) hs.le]
    congr 1; field_simp
  rw [h6, ← h8]
  exact mul_le_mul_of_nonneg_left h7 (by positivity)

/-- (F): the far term (6).  With `p = d + α₃ - 2 - α > 0`,
`s^(2+α) exp (-ρ c_h Rq / s) ≤ (p / (e ρ c_h R_*))^p s^(d+α₃)`. -/
theorem far_term_le {s ρ c Rq Rs d α α₃ : ℝ} (hs : 0 < s) (hρ : 0 < ρ) (hc : 0 < c) (hRs : 0 < Rs)
    (hRq : Rs ≤ Rq) (hp : 0 < d + α₃ - 2 - α) :
    s ^ (2 + α) * exp (-(ρ * c * Rq / s)) ≤
      ((d + α₃ - 2 - α) / (exp 1 * (ρ * c * Rs))) ^ (d + α₃ - 2 - α) * s ^ (d + α₃) := by
  have h := exp_neg_div_le hp hs (by positivity : 0 < ρ * c * Rs)
    (by nlinarith [mul_pos hρ hc] : ρ * c * Rs ≤ ρ * c * Rq)
  calc s ^ (2 + α) * exp (-(ρ * c * Rq / s))
      ≤ s ^ (2 + α) * (((d + α₃ - 2 - α) / (exp 1 * (ρ * c * Rs))) ^ (d + α₃ - 2 - α) *
          s ^ (d + α₃ - 2 - α)) := mul_le_mul_of_nonneg_left h (by positivity)
    _ = _ := by
      rw [mul_left_comm, ← Real.rpow_add hs, show 2 + α + (d + α₃ - 2 - α) = d + α₃ by ring]

/-- (F), consequence: a quantity bounded by `K s^(2+α) exp (-ρ c_h Rq/s)` is bounded by
`C₁ s^(d+α₃)` with `C₁ = K (p/(e ρ c_h R_*))^p`. -/
theorem far_term_bound {s ρ c Rq Rs d α α₃ K Q : ℝ} (hs : 0 < s) (hρ : 0 < ρ) (hc : 0 < c)
    (hRs : 0 < Rs) (hRq : Rs ≤ Rq) (hp : 0 < d + α₃ - 2 - α) (hK : 0 ≤ K)
    (hQ : Q ≤ K * (s ^ (2 + α) * exp (-(ρ * c * Rq / s)))) :
    Q ≤ K * ((d + α₃ - 2 - α) / (exp 1 * (ρ * c * Rs))) ^ (d + α₃ - 2 - α) * s ^ (d + α₃) := by
  have := far_term_le hs hρ hc hRs hRq hp
  calc Q ≤ _ := hQ
    _ ≤ K * (((d + α₃ - 2 - α) / (exp 1 * (ρ * c * Rs))) ^ (d + α₃ - 2 - α) * s ^ (d + α₃)) :=
        mul_le_mul_of_nonneg_left this hK
    _ = _ := by ring

/-- (T): the tail (8).  With `p_T = d + α₃ > 0`,
`exp (-ρ c_h Rq / s) ≤ (p_T/(e ρ c_h R_*))^{p_T} s^(d+α₃)`. -/
theorem tail_term_le {s ρ c Rq Rs d α₃ : ℝ} (hs : 0 < s) (hρ : 0 < ρ) (hc : 0 < c) (hRs : 0 < Rs)
    (hRq : Rs ≤ Rq) (hp : 0 < d + α₃) :
    exp (-(ρ * c * Rq / s)) ≤ ((d + α₃) / (exp 1 * (ρ * c * Rs))) ^ (d + α₃) * s ^ (d + α₃) :=
  exp_neg_div_le hp hs (by positivity : 0 < ρ * c * Rs)
    (by nlinarith [mul_pos hρ hc] : ρ * c * Rs ≤ ρ * c * Rq)

/-! ### Exponent relations -/

section Relations
variable {d γ α α₁ α₃ : ℝ}

/-- `3 + 2α = d + 1 - 2γ` when `α = (d - 2)/2 - γ`. -/
theorem three_add_two_mul (hα : α = (d - 2) / 2 - γ) : 3 + 2 * α = d + 1 - 2 * γ := by
  subst hα; ring

/-- `3 + 2α = d + α₃ + α₁` when `α = (d-2)/2 - γ`, `α₃ = 1 - 2γ - α₁`. -/
theorem three_add_two_mul_eq (hα : α = (d - 2) / 2 - γ) (hα₃ : α₃ = 1 - 2 * γ - α₁) :
    3 + 2 * α = d + α₃ + α₁ := by
  subst hα hα₃; ring

/-- `p = d + α₃ - 2 - α = d/2 - γ - α₁`. -/
theorem exponent_p_eq (hα : α = (d - 2) / 2 - γ) (hα₃ : α₃ = 1 - 2 * γ - α₁) :
    d + α₃ - 2 - α = d / 2 - γ - α₁ := by
  subst hα hα₃; ring

end Relations

/-! ### (S): the scale powers (7) -/

/-- (7), first half: `8 M₂ E₀ r⁻² σ³ ε² ≤ 8 M₂ E₀ C₀³ K_r² K_R² s^(3+2α)`, for `σ = C₀ s`,
`ε = ε_q`, `ε_q/ε_j ≤ K_R s^α`, `r = ε_j/K_r`. -/
theorem v2_scale_le {M₂ E₀ C₀ K_r K_R s α εj εq r : ℝ} (hM : 0 ≤ M₂) (hE : 0 ≤ E₀) (hC : 0 ≤ C₀)
    (hKr : 0 < K_r) (hs : 0 < s) (hεj : 0 < εj) (hεq : 0 ≤ εq) (hr : r = εj / K_r)
    (hR : εq / εj ≤ K_R * s ^ α) :
    8 * M₂ * E₀ * (1 / r ^ 2) * (C₀ * s) ^ 3 * εq ^ 2 ≤
      8 * M₂ * E₀ * C₀ ^ 3 * K_r ^ 2 * K_R ^ 2 * s ^ (3 + 2 * α) := by
  have hq : 0 ≤ εq / εj := div_nonneg hεq hεj.le
  have h2 : (εq / εj) ^ 2 ≤ (K_R * s ^ α) ^ 2 := pow_le_pow_left₀ hq hR 2
  have hsα : s ^ (3 + 2 * α) = s ^ 3 * (s ^ α) ^ 2 := by
    rw [Real.rpow_add hs, show (2 * α) = α * 2 by ring, Real.rpow_mul hs.le]
    norm_cast
  have e1 : 8 * M₂ * E₀ * (1 / r ^ 2) * (C₀ * s) ^ 3 * εq ^ 2 =
      8 * M₂ * E₀ * C₀ ^ 3 * K_r ^ 2 * s ^ 3 * (εq / εj) ^ 2 := by
    subst hr; field_simp
  rw [e1, hsα]
  have : 0 ≤ 8 * M₂ * E₀ * C₀ ^ 3 * K_r ^ 2 * s ^ 3 := by positivity
  calc _ ≤ 8 * M₂ * E₀ * C₀ ^ 3 * K_r ^ 2 * s ^ 3 * (K_R * s ^ α) ^ 2 :=
        mul_le_mul_of_nonneg_left h2 this
    _ = _ := by ring

/-- (7), second half: if `3 + 2α = d + α₃ + α₁`, `α₁ ≥ 0`, `0 < s ≤ 1`, the bound is
`C₂ E₀ s^(d+α₃)`, `C₂ = 8 M₂ C₀³ K_r² K_R²`. -/
theorem v2_scale_le_rate {M₂ E₀ C₀ K_r K_R s α εj εq r d α₁ α₃ : ℝ} (hM : 0 ≤ M₂) (hE : 0 ≤ E₀)
    (hC : 0 ≤ C₀) (hKr : 0 < K_r) (hs : 0 < s) (hs1 : s ≤ 1) (hεj : 0 < εj) (hεq : 0 ≤ εq)
    (hr : r = εj / K_r) (hR : εq / εj ≤ K_R * s ^ α) (hrel : 3 + 2 * α = d + α₃ + α₁)
    (hα₁ : 0 ≤ α₁) :
    8 * M₂ * E₀ * (1 / r ^ 2) * (C₀ * s) ^ 3 * εq ^ 2 ≤
      (8 * M₂ * C₀ ^ 3 * K_r ^ 2 * K_R ^ 2) * E₀ * s ^ (d + α₃) := by
  have h := v2_scale_le hM hE hC hKr hs hεj hεq hr hR
  have hpow : s ^ (3 + 2 * α) ≤ s ^ (d + α₃) := by
    rw [hrel]; exact Real.rpow_le_rpow_of_exponent_ge hs hs1 (by linarith)
  refine h.trans ?_
  have : 0 ≤ 8 * M₂ * E₀ * C₀ ^ 3 * K_r ^ 2 * K_R ^ 2 := by positivity
  calc _ ≤ 8 * M₂ * E₀ * C₀ ^ 3 * K_r ^ 2 * K_R ^ 2 * s ^ (d + α₃) :=
        mul_le_mul_of_nonneg_left hpow this
    _ = _ := by ring

/-! ### (G): the geometric sum -/

/-- `L^(-(m α₃)) = (L^(-α₃))^m`. -/
theorem rpow_neg_nat_mul {L α₃ : ℝ} (hL : 0 < L) (m : ℕ) :
    L ^ (-((m : ℝ) * α₃)) = (L ^ (-α₃)) ^ m := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hL.le]; congr 1; ring

theorem rpow_neg_lt_one {L α₃ : ℝ} (hL : 1 < L) (hα₃ : 0 < α₃) : L ^ (-α₃) < 1 :=
  Real.rpow_lt_one_of_one_lt_of_neg hL (by linarith)

/-- (G): `∑_{m ≥ n₁} L^(-m α₃) = L^(-n₁ α₃)/(1 - L^(-α₃))` as a `HasSum`. -/
theorem hasSum_geometric_tail {L α₃ : ℝ} (hL : 1 < L) (hα₃ : 0 < α₃) (n₁ : ℕ) :
    HasSum (fun k : ℕ => L ^ (-(((n₁ + k : ℕ) : ℝ) * α₃)))
      (L ^ (-((n₁ : ℝ) * α₃)) / (1 - L ^ (-α₃))) := by
  have hL0 : 0 < L := by linarith
  have hq0 : 0 ≤ L ^ (-α₃) := by positivity
  have hq1 := rpow_neg_lt_one hL hα₃
  have h := (hasSum_geometric_of_lt_one hq0 hq1).mul_left (L ^ (-((n₁ : ℝ) * α₃)))
  convert h using 1
  · funext k
    rw [rpow_neg_nat_mul hL0, rpow_neg_nat_mul hL0, pow_add, mul_comm]
  · rw [div_eq_mul_inv]

/-- (G), finite partial sums: for every `n`,
`∑_{k<n} L^(-(n₁+k) α₃) ≤ L^(-n₁ α₃)/(1 - L^(-α₃))`. -/
theorem sum_geometric_tail_le {L α₃ : ℝ} (hL : 1 < L) (hα₃ : 0 < α₃) (n₁ n : ℕ) :
    ∑ k ∈ Finset.range n, L ^ (-(((n₁ + k : ℕ) : ℝ) * α₃)) ≤
      L ^ (-((n₁ : ℝ) * α₃)) / (1 - L ^ (-α₃)) :=
  sum_le_hasSum (Finset.range n) (fun _ _ => by positivity) (hasSum_geometric_tail hL hα₃ n₁)

/-! ### (C): the charge per new cube -/

/-- (C), one scale: with per-site bounds `C₁ E₀ s^(d+α₃)`, `C₂ E₀ s^(d+α₃)`,
`2 C_T E₀ s^(d+α₃)` and at most `Γ_E s^(-d)` sites, the charge is
`≤ Γ_E (C₁ + C₂ + 2 C_T) E₀ s^α₃`. -/
theorem charge_le {ι : Type*} {s d α₃ Γ C₁ C₂ C_T E₀ : ℝ} (hs : 0 < s)
    (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) (hCT : 0 ≤ C_T) (hE : 0 ≤ E₀) (S : Finset ι)
    (a₁ a₂ a₃ : ι → ℝ) (h₁ : ∀ y ∈ S, a₁ y ≤ C₁ * E₀ * s ^ (d + α₃))
    (h₂ : ∀ y ∈ S, a₂ y ≤ C₂ * E₀ * s ^ (d + α₃))
    (h₃ : ∀ y ∈ S, a₃ y ≤ 2 * C_T * E₀ * s ^ (d + α₃))
    (hcard : (S.card : ℝ) ≤ Γ * s ^ (-d)) :
    ∑ y ∈ S, (a₁ y + a₂ y + a₃ y) ≤ Γ * (C₁ + C₂ + 2 * C_T) * E₀ * s ^ α₃ := by
  have h : ∑ y ∈ S, (a₁ y + a₂ y + a₃ y) ≤ ∑ _y ∈ S, (C₁ + C₂ + 2 * C_T) * E₀ * s ^ (d + α₃) :=
    Finset.sum_le_sum fun y hy => by
      have := h₁ y hy; have := h₂ y hy; have := h₃ y hy; nlinarith
  rw [Finset.sum_const, nsmul_eq_mul] at h
  refine h.trans ?_
  have hK : 0 ≤ (C₁ + C₂ + 2 * C_T) * E₀ * s ^ (d + α₃) := by positivity
  calc _ ≤ Γ * s ^ (-d) * ((C₁ + C₂ + 2 * C_T) * E₀ * s ^ (d + α₃)) :=
        mul_le_mul_of_nonneg_right hcard hK
    _ = Γ * (C₁ + C₂ + 2 * C_T) * E₀ * (s ^ (-d) * s ^ (d + α₃)) := by ring
    _ = _ := by
      rw [← Real.rpow_add hs]; congr 2; ring

/-- (C), summed over the scale gaps `m ≥ n₁`: if the charge at gap `m` is at most
`Γ K E₀ L^(-m α₃)` (that is `s = L^(-m)` in `charge_le`), every finite partial sum over
`m ∈ [n₁, n₁ + n)` is `≤ Γ K E₀ L^(-n₁ α₃)/(1 - L^(-α₃))`. -/
theorem charge_sum_le {L α₃ Γ K E₀ : ℝ} (hL : 1 < L) (hα₃ : 0 < α₃) (hΓ : 0 ≤ Γ) (hK : 0 ≤ K)
    (hE : 0 ≤ E₀) (n₁ n : ℕ) (c : ℕ → ℝ)
    (hc : ∀ m, c m ≤ Γ * K * E₀ * L ^ (-((m : ℝ) * α₃))) :
    ∑ k ∈ Finset.range n, c (n₁ + k) ≤
      Γ * K * E₀ * (L ^ (-((n₁ : ℝ) * α₃)) / (1 - L ^ (-α₃))) := by
  calc ∑ k ∈ Finset.range n, c (n₁ + k)
      ≤ ∑ k ∈ Finset.range n, Γ * K * E₀ * L ^ (-(((n₁ + k : ℕ) : ℝ) * α₃)) :=
        Finset.sum_le_sum fun k _ => hc _
    _ = Γ * K * E₀ * ∑ k ∈ Finset.range n, L ^ (-(((n₁ + k : ℕ) : ℝ) * α₃)) := by
        rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left (sum_geometric_tail_le hL hα₃ n₁ n) (by positivity)

/-- With `s = L^(-m)`: `s^α₃ = L^(-(m α₃))`. -/
theorem rpow_scale_eq {L α₃ : ℝ} (hL : 0 < L) (m : ℕ) :
    (L ^ (-(m : ℝ))) ^ α₃ = L ^ (-((m : ℝ) * α₃)) := by
  rw [← Real.rpow_mul hL.le]; congr 1; ring

/-! ### Non-vacuity of the exponent data and of (F), (T) -/

/-- The sample exponents `d = 3`, `γ = 1/8`, `α = 3/8`, `α₁ = 1/4`, `α₃ = 1/2` satisfy
`α = (d-2)/2 - γ`, `α₃ = 1 - 2γ - α₁`, `p = 9/8 > 0` and `3 + 2α = d + α₃ + α₁`. -/
theorem sample_exponents :
    (3 / 8 : ℝ) = (3 - 2) / 2 - 1 / 8 ∧ (1 / 2 : ℝ) = 1 - 2 * (1 / 8) - 1 / 4 ∧
    (3 : ℝ) + 1 / 2 - 2 - 3 / 8 = 9 / 8 ∧ (0 : ℝ) < 9 / 8 ∧ (0 : ℝ) < 3 + 1 / 2 ∧
    3 + 2 * (3 / 8 : ℝ) = 3 + 1 / 2 + 1 / 4 := by
  norm_num

/-- (F) at the sample exponents, `s = 1/2`, `ρ = c_h = R_* = 1`, `Rq = 2`. -/
theorem far_term_sample :
    (1 / 2 : ℝ) ^ (2 + 3 / 8 : ℝ) * exp (-(1 * 1 * 2 / (1 / 2))) ≤
      ((3 + 1 / 2 - 2 - 3 / 8) / (exp 1 * (1 * 1 * 1))) ^ (3 + 1 / 2 - 2 - 3 / 8 : ℝ) *
        (1 / 2 : ℝ) ^ (3 + 1 / 2 : ℝ) :=
  far_term_le (by norm_num) one_pos one_pos one_pos (by norm_num) (by norm_num)

/-- (T) at the same sample. -/
theorem tail_term_sample :
    exp (-(1 * 1 * 2 / (1 / 2 : ℝ))) ≤
      ((3 + 1 / 2) / (exp 1 * (1 * 1 * 1))) ^ (3 + 1 / 2 : ℝ) * (1 / 2 : ℝ) ^ (3 + 1 / 2 : ℝ) :=
  tail_term_le (by norm_num) one_pos one_pos one_pos (by norm_num) (by norm_num)

/-! ### (V): the source term (5), real vectors -/

section Real

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The unit direction `ψ / |ψ|`. -/
noncomputable def unitDir (ψ : E) : E := ‖ψ‖⁻¹ • ψ

/-- Step 1: `ψ ↦ ψ/|ψ|` is Lipschitz with constant `2/min |ψ| ≤ 4` on `|ψ| ≥ 1/2`. -/
theorem unit_sub_le {x y : E} (hx : 1 / 2 ≤ ‖x‖) (hy : 1 / 2 ≤ ‖y‖) :
    ‖unitDir x - unitDir y‖ ≤ 4 * ‖x - y‖ := by
  have hxp : 0 < ‖x‖ := by linarith
  have hyp : 0 < ‖y‖ := by linarith
  have e : unitDir x - unitDir y = ‖x‖⁻¹ • (x - y) + (‖x‖⁻¹ - ‖y‖⁻¹) • y := by
    unfold unitDir; module
  have h1 : ‖x‖⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ hxp (by norm_num)]; linarith
  have h2 : |(‖x‖⁻¹ - ‖y‖⁻¹)| * ‖y‖ ≤ ‖x - y‖ * 2 := by
    have : (‖x‖⁻¹ - ‖y‖⁻¹) * ‖y‖ = (‖y‖ - ‖x‖) / ‖x‖ := by field_simp
    rw [← abs_of_pos hyp, ← abs_mul, abs_of_pos hyp, this, abs_div, abs_of_pos hxp,
      div_eq_mul_inv]
    have : |‖y‖ - ‖x‖| ≤ ‖x - y‖ := by rw [norm_sub_rev]; exact abs_norm_sub_norm_le _ _
    calc _ ≤ ‖x - y‖ * ‖x‖⁻¹ := mul_le_mul_of_nonneg_right this (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
  rw [e]
  refine (norm_add_le _ _).trans ?_
  rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hxp)]
  have : ‖x‖⁻¹ * ‖x - y‖ ≤ 2 * ‖x - y‖ := mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
  nlinarith

/-- Step 2: `|b - ν u_y| ≤ 2 η` when `|b - ν ψ_y| ≤ η`, `| |ψ_y|² - 1 | ≤ η`, `0 ≤ ν ≤ 1`,
`|ψ_y| ≥ 1/2`.  (With `η = σ² ε` this is `|b - ν u_y| ≤ 2 σ² ε`.) -/
theorem source_sub_le {b y : E} {ν η : ℝ} (hy : 1 / 2 ≤ ‖y‖) (hν0 : 0 ≤ ν) (hν1 : ν ≤ 1)
    (hb : ‖b - ν • y‖ ≤ η) (hn : |‖y‖ ^ 2 - 1| ≤ η) : ‖b - ν • unitDir y‖ ≤ 2 * η := by
  have hyp : 0 < ‖y‖ := by linarith
  have e : b - ν • unitDir y = (b - ν • y) + ν • ((1 - ‖y‖⁻¹) • y) := by
    unfold unitDir; module
  have h1 : ‖(1 - ‖y‖⁻¹) • y‖ = |‖y‖ - 1| := by
    rw [norm_smul, Real.norm_eq_abs]
    have : (1 - ‖y‖⁻¹) * ‖y‖ = ‖y‖ - 1 := by field_simp
    rw [← abs_of_pos hyp, ← abs_mul, abs_of_pos hyp, this]
  have h2 : |‖y‖ - 1| ≤ |‖y‖ ^ 2 - 1| := by
    have : ‖y‖ ^ 2 - 1 = (‖y‖ - 1) * (‖y‖ + 1) := by ring
    rw [this, abs_mul, abs_of_pos (by linarith : 0 < ‖y‖ + 1)]
    nlinarith [abs_nonneg (‖y‖ - 1)]
  rw [e]
  refine (norm_add_le _ _).trans ?_
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hν0, h1]
  have : ν * |‖y‖ - 1| ≤ η := by
    calc _ ≤ 1 * |‖y‖ - 1| := mul_le_mul_of_nonneg_right hν1 (abs_nonneg _)
      _ ≤ η := by linarith
  linarith

/-- Step 3: for unit vectors, `u_y · (u_x - u_y) = -½ |u_x - u_y|²`. -/
theorem inner_unit_sub {u v : E} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    inner ℝ u (v - u) = -(1 / 2) * ‖v - u‖ ^ 2 := by
  rw [norm_sub_sq_real, hu, hv, inner_sub_right, real_inner_self_eq_norm_sq, hu,
    real_inner_comm]
  ring

theorem norm_unitDir {ψ : E} (h : ψ ≠ 0) : ‖unitDir ψ‖ = 1 := by
  unfold unitDir
  rw [norm_smul, norm_inv, norm_norm]
  exact inv_mul_cancel₀ (norm_ne_zero_iff.2 h)

/-- (V), real case, (5): with `|ψ_x|, |ψ_y| ≥ 1/2`, `|ψ_x - ψ_y| ≤ Dσε`, `|b - νψ_y| ≤ σ²ε`,
`| |ψ_y|² - 1 | ≤ σ²ε`, `0 ≤ ν ≤ σ² ≤ 1`, `0 ≤ σ`, `0 ≤ ε`:
`|⟨b, u_x - u_y⟩| ≤ 8 (D² + D) σ³ ε²`.  (The constant `8` is exactly what the steps give; `ε ≤ 1`
is not needed.) -/
theorem source_term_le {ψx ψy b : E} {ν σ ε D : ℝ} (hx : 1 / 2 ≤ ‖ψx‖) (hy : 1 / 2 ≤ ‖ψy‖)
    (hD : ‖ψx - ψy‖ ≤ D * σ * ε) (hb : ‖b - ν • ψy‖ ≤ σ ^ 2 * ε)
    (hn : |‖ψy‖ ^ 2 - 1| ≤ σ ^ 2 * ε) (hν0 : 0 ≤ ν) (hνσ : ν ≤ σ ^ 2) (hσ0 : 0 ≤ σ)
    (hσ1 : σ ≤ 1) (hε0 : 0 ≤ ε) :
    |inner ℝ b (unitDir ψx - unitDir ψy)| ≤ 8 * (D ^ 2 + D) * σ ^ 3 * ε ^ 2 := by
  have hσ2 : σ ^ 2 ≤ 1 := by nlinarith
  have hν1 : ν ≤ 1 := hνσ.trans hσ2
  have hw : ‖unitDir ψx - unitDir ψy‖ ≤ 4 * (D * σ * ε) :=
    (unit_sub_le hx hy).trans (by linarith)
  have hc : ‖b - ν • unitDir ψy‖ ≤ 2 * (σ ^ 2 * ε) := source_sub_le hy hν0 hν1 hb hn
  set w := unitDir ψx - unitDir ψy with hwdef
  have hxu : ‖unitDir ψx‖ = 1 := norm_unitDir (norm_pos_iff.1 (by linarith))
  have hyu : ‖unitDir ψy‖ = 1 := norm_unitDir (norm_pos_iff.1 (by linarith))
  have hid : inner ℝ (unitDir ψy) w = -(1 / 2) * ‖w‖ ^ 2 := inner_unit_sub hyu hxu
  have e : inner ℝ b w = inner ℝ (b - ν • unitDir ψy) w + ν * inner ℝ (unitDir ψy) w := by
    rw [inner_sub_left, real_inner_smul_left]; ring
  rw [e, hid]
  have t1 : |inner ℝ (b - ν • unitDir ψy) w| ≤ 2 * (σ ^ 2 * ε) * (4 * (D * σ * ε)) :=
    (abs_real_inner_le_norm _ _).trans
      (mul_le_mul hc hw (norm_nonneg _) (by positivity))
  have hw0 := norm_nonneg w
  have t2 : ν * (1 / 2) * ‖w‖ ^ 2 ≤ σ ^ 2 * (1 / 2) * (4 * (D * σ * ε)) ^ 2 := by
    have : ‖w‖ ^ 2 ≤ (4 * (D * σ * ε)) ^ 2 := pow_le_pow_left₀ hw0 hw 2
    calc ν * (1 / 2) * ‖w‖ ^ 2 ≤ σ ^ 2 * (1 / 2) * ‖w‖ ^ 2 := by gcongr
      _ ≤ _ := by gcongr
  have t3 : σ ^ 2 * (1 / 2) * (4 * (D * σ * ε)) ^ 2 ≤ 8 * D ^ 2 * σ ^ 3 * ε ^ 2 := by
    have : σ ^ 4 ≤ σ ^ 3 := pow_le_pow_of_le_one hσ0 hσ1 (by norm_num)
    have h8 : 0 ≤ 8 * D ^ 2 * ε ^ 2 := by positivity
    nlinarith [mul_le_mul_of_nonneg_left this h8]
  have e2 : ν * (-(1 / 2) * ‖w‖ ^ 2) = -(ν * (1 / 2) * ‖w‖ ^ 2) := by ring
  rw [e2]
  refine (abs_add_le _ _).trans ?_
  rw [abs_neg, abs_of_nonneg (by positivity : 0 ≤ ν * (1 / 2) * ‖w‖ ^ 2)]
  nlinarith

end Real

/-- (V), real case, in `Fin N → ℝ` with the Euclidean norm. -/
theorem source_term_le_euclidean {N : ℕ} {ψx ψy b : EuclideanSpace ℝ (Fin N)} {ν σ ε D : ℝ}
    (hx : 1 / 2 ≤ ‖ψx‖) (hy : 1 / 2 ≤ ‖ψy‖) (hD : ‖ψx - ψy‖ ≤ D * σ * ε)
    (hb : ‖b - ν • ψy‖ ≤ σ ^ 2 * ε) (hn : |‖ψy‖ ^ 2 - 1| ≤ σ ^ 2 * ε) (hν0 : 0 ≤ ν)
    (hνσ : ν ≤ σ ^ 2) (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1) (hε0 : 0 ≤ ε) :
    |inner ℝ b (unitDir ψx - unitDir ψy)| ≤ 8 * (D ^ 2 + D) * σ ^ 3 * ε ^ 2 :=
  source_term_le hx hy hD hb hn hν0 hνσ hσ0 hσ1 hε0

/-- Non-vacuity of (V): `ψ_x = ψ_y = b = 1`, `ν = 0`, `D = 0`, `σ = ε = 1` in `ℝ`. -/
theorem source_term_sample :
    |inner ℝ (1 : ℝ) (unitDir (1 : ℝ) - unitDir (1 : ℝ))| ≤ 8 * (0 ^ 2 + 0) * 1 ^ 3 * 1 ^ 2 := by
  refine source_term_le (ν := 0) (σ := 1) (ε := 1) (D := 0) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) le_rfl (by norm_num) zero_le_one le_rfl
    zero_le_one

/-! ### (V): the source term (5), complex vectors with the bilinear `dot` -/

section Complex

open Balaban.SmallField Balaban.LargeField.Def7v2

variable {N : ℕ}

/-- The `ℓ²` norm on `Fin N → ℂ`: `(∑ i, ‖v i‖²)^{1/2}`. -/
noncomputable def nrm2 (v : Fin N → ℂ) : ℝ := ‖(WithLp.toLp 2 v : EuclideanSpace ℂ (Fin N))‖

theorem nrm2_nonneg (v : Fin N → ℂ) : 0 ≤ nrm2 v := norm_nonneg _

theorem nrm2_add (v w : Fin N → ℂ) : nrm2 (v + w) ≤ nrm2 v + nrm2 w := by
  unfold nrm2
  have := norm_add_le (WithLp.toLp 2 v : EuclideanSpace ℂ (Fin N)) (WithLp.toLp 2 w)
  rwa [← WithLp.toLp_add] at this

theorem nrm2_smul (c : ℂ) (v : Fin N → ℂ) : nrm2 (c • v) = ‖c‖ * nrm2 v := by
  unfold nrm2
  rw [WithLp.toLp_smul, norm_smul]

theorem nrm2_eq (v : Fin N → ℂ) : nrm2 v = Real.sqrt (∑ i, ‖v i‖ ^ 2) := by
  unfold nrm2
  rw [EuclideanSpace.norm_eq]

/-- Cauchy--Schwarz for the bilinear pairing: `‖v · w‖ ≤ |v|₂ |w|₂`. -/
theorem norm_dot_le (v w : Fin N → ℂ) : ‖dot v w‖ ≤ nrm2 v * nrm2 w := by
  rw [nrm2_eq, nrm2_eq]
  calc ‖dot v w‖ ≤ ∑ i, ‖v i * w i‖ := norm_sum_le _ _
    _ = ∑ i, ‖v i‖ * ‖w i‖ := by simp
    _ ≤ _ := Real.sum_mul_le_sqrt_mul_sqrt _ _ _

/-- The principal root of `a` with `‖a - 1‖ ≤ 1/2` has real part `≥ 7/10`. -/
theorem sqrtC_re_ge {a : ℂ} (h : ‖a - 1‖ ≤ 1 / 2) : 7 / 10 ≤ (sqrtC a).re := by
  have h1 : |(a - 1).re| ≤ 1 / 2 := (Complex.abs_re_le_norm _).trans h
  have h2 : 1 / 2 ≤ a.re := by
    have := (abs_le.1 h1).1; simp at this; linarith
  have h3 := congrArg Complex.re (sqrtC_mul_self a)
  rw [Complex.mul_re] at h3
  have h4 := sqrtC_re_nonneg a
  nlinarith [sq_nonneg (sqrtC a).im]

theorem sqrtC_norm_ge {a : ℂ} (h : ‖a - 1‖ ≤ 1 / 2) : 7 / 10 ≤ ‖sqrtC a‖ :=
  (sqrtC_re_ge h).trans (Complex.re_le_norm _)

/-- `‖√a - 1‖ ≤ ‖a - 1‖` on the disc. -/
theorem sqrtC_sub_one_le {a : ℂ} (h : ‖a - 1‖ ≤ 1 / 2) : ‖sqrtC a - 1‖ ≤ ‖a - 1‖ := by
  have e : (sqrtC a - 1) * (sqrtC a + 1) = a - 1 := by
    linear_combination sqrtC_mul_self a
  have h1 : 1 ≤ ‖sqrtC a + 1‖ :=
    le_trans (by have := sqrtC_re_ge h; simp; linarith) (Complex.re_le_norm _)
  calc ‖sqrtC a - 1‖ ≤ ‖sqrtC a - 1‖ * ‖sqrtC a + 1‖ := le_mul_of_one_le_right (norm_nonneg _) h1
    _ = ‖a - 1‖ := by rw [← norm_mul, e]

/-- `(7/5) ‖√a - √a'‖ ≤ ‖a - a'‖` on the disc. -/
theorem sqrtC_sub_le {a a' : ℂ} (h : ‖a - 1‖ ≤ 1 / 2) (h' : ‖a' - 1‖ ≤ 1 / 2) :
    7 / 5 * ‖sqrtC a - sqrtC a'‖ ≤ ‖a - a'‖ := by
  have e : (sqrtC a - sqrtC a') * (sqrtC a + sqrtC a') = a - a' := by
    linear_combination sqrtC_mul_self a - sqrtC_mul_self a'
  have h1 : 7 / 5 ≤ ‖sqrtC a + sqrtC a'‖ :=
    le_trans (by have := sqrtC_re_ge h; have := sqrtC_re_ge h'; simp; linarith)
      (Complex.re_le_norm _)
  calc 7 / 5 * ‖sqrtC a - sqrtC a'‖ ≤ ‖sqrtC a + sqrtC a'‖ * ‖sqrtC a - sqrtC a'‖ :=
        mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
    _ = ‖a - a'‖ := by rw [mul_comm, ← norm_mul, e]

theorem dot_ne_zero_of_near {a : ℂ} (h : ‖a - 1‖ ≤ 1 / 2) : a ≠ 0 := by
  intro h0; subst h0; norm_num at h

theorem dot_sub_dot (x y : Fin N → ℂ) : dot x x - dot y y = dot (x - y) (x + y) := by
  rw [dot_add_right, dot_sub_left, dot_sub_left, dot_comm y x]; ring

/-- Step 1, complex: `|u_x - u_y|₂ ≤ (2 + 3B²) |ψ_x - ψ_y|₂` when `|ψ·ψ - 1| ≤ 1/2` and
`|ψ|₂ ≤ B` at both points. -/
theorem unitDirC_sub_le {ψx ψy : Fin N → ℂ} {B : ℝ} (hax : ‖dot ψx ψx - 1‖ ≤ 1 / 2)
    (hay : ‖dot ψy ψy - 1‖ ≤ 1 / 2) (hBx : nrm2 ψx ≤ B) (hBy : nrm2 ψy ≤ B) :
    nrm2 (unitDirC ψx - unitDirC ψy) ≤ (2 + 3 * B ^ 2) * nrm2 (ψx - ψy) := by
  set sx := sqrtC (dot ψx ψx) with hsx
  set sy := sqrtC (dot ψy ψy) with hsy
  have hnx : 7 / 10 ≤ ‖sx‖ := sqrtC_norm_ge hax
  have hny : 7 / 10 ≤ ‖sy‖ := sqrtC_norm_ge hay
  have hB0 : 0 ≤ B := (nrm2_nonneg _).trans hBx
  have hΔ := nrm2_nonneg (ψx - ψy)
  have hsxz : sx ≠ 0 := norm_pos_iff.1 (by linarith)
  have hsyz : sy ≠ 0 := norm_pos_iff.1 (by linarith)
  have e : unitDirC ψx - unitDirC ψy = sx⁻¹ • (ψx - ψy) + (sx⁻¹ - sy⁻¹) • ψy := by
    unfold unitDirC; rw [← hsx, ← hsy]; module
  -- the difference of the roots
  have hA : ‖dot ψx ψx - dot ψy ψy‖ ≤ nrm2 (ψx - ψy) * (2 * B) := by
    rw [dot_sub_dot]
    refine (norm_dot_le _ _).trans (mul_le_mul_of_nonneg_left ?_ hΔ)
    have := nrm2_add ψx ψy; linarith
  have hS : 7 / 5 * ‖sx - sy‖ ≤ nrm2 (ψx - ψy) * (2 * B) :=
    (sqrtC_sub_le hax hay).trans hA
  have hI : ‖sx⁻¹ - sy⁻¹‖ ≤ 100 / 49 * ‖sx - sy‖ := by
    rw [inv_sub_inv hsxz hsyz, norm_div, norm_mul, div_le_iff₀ (by positivity), norm_sub_rev]
    have : 49 / 100 ≤ ‖sx‖ * ‖sy‖ := by nlinarith
    nlinarith [norm_nonneg (sy - sx), norm_nonneg (sx - sy), norm_sub_rev sx sy]
  have hi : ‖sx⁻¹‖ ≤ 10 / 7 := by
    rw [norm_inv]; exact inv_le_of_inv_le₀ (by norm_num) (by linarith)
  rw [e]
  refine (nrm2_add _ _).trans ?_
  rw [nrm2_smul, nrm2_smul]
  have t1 : ‖sx⁻¹‖ * nrm2 (ψx - ψy) ≤ 10 / 7 * nrm2 (ψx - ψy) :=
    mul_le_mul_of_nonneg_right hi hΔ
  have t2 : ‖sx⁻¹ - sy⁻¹‖ * nrm2 ψy ≤ 3 * B ^ 2 * nrm2 (ψx - ψy) := by
    have h1 : ‖sx⁻¹ - sy⁻¹‖ ≤ 100 / 49 * (5 / 7 * (nrm2 (ψx - ψy) * (2 * B))) := by
      refine hI.trans ?_
      have : ‖sx - sy‖ ≤ 5 / 7 * (nrm2 (ψx - ψy) * (2 * B)) := by linarith
      linarith
    calc ‖sx⁻¹ - sy⁻¹‖ * nrm2 ψy ≤ (100 / 49 * (5 / 7 * (nrm2 (ψx - ψy) * (2 * B)))) * B :=
          mul_le_mul h1 hBy (nrm2_nonneg _) (by positivity)
      _ ≤ _ := by nlinarith [mul_nonneg hΔ (sq_nonneg B)]
  nlinarith

/-- Step 2, complex: `|b - ν u_y|₂ ≤ (1 + 2B) η` when `|b - νψ_y|₂ ≤ η`, `|ψ_y·ψ_y - 1| ≤ η`,
`η ≤ 1/2`, `|ψ_y|₂ ≤ B`, `0 ≤ ν ≤ 1`. -/
theorem source_sub_le_C {b ψy : Fin N → ℂ} {B ν η : ℝ} (hη : η ≤ 1 / 2)
    (hn : ‖dot ψy ψy - 1‖ ≤ η) (hB : nrm2 ψy ≤ B) (hν0 : 0 ≤ ν) (hν1 : ν ≤ 1)
    (hb : nrm2 (b - (ν : ℂ) • ψy) ≤ η) :
    nrm2 (b - (ν : ℂ) • unitDirC ψy) ≤ (1 + 2 * B) * η := by
  have hay : ‖dot ψy ψy - 1‖ ≤ 1 / 2 := hn.trans hη
  set s := sqrtC (dot ψy ψy) with hs
  have hns : 7 / 10 ≤ ‖s‖ := sqrtC_norm_ge hay
  have hsz : s ≠ 0 := norm_pos_iff.1 (by linarith)
  have hη0 : 0 ≤ η := (norm_nonneg _).trans hn
  have e : b - (ν : ℂ) • unitDirC ψy =
      (b - (ν : ℂ) • ψy) + ((ν : ℂ) * (1 - s⁻¹)) • ψy := by
    unfold unitDirC; rw [← hs]; module
  have h1 : ‖1 - s⁻¹‖ ≤ 2 * η := by
    have : 1 - s⁻¹ = (s - 1) / s := by field_simp
    rw [this, norm_div, div_le_iff₀ (by linarith)]
    have := sqrtC_sub_one_le hay
    nlinarith
  have hB0 : 0 ≤ B := (nrm2_nonneg _).trans hB
  rw [e]
  refine (nrm2_add _ _).trans ?_
  rw [nrm2_smul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hν0]
  have : ν * ‖1 - s⁻¹‖ * nrm2 ψy ≤ 1 * (2 * η) * B := by
    have : ν * ‖1 - s⁻¹‖ ≤ 1 * (2 * η) :=
      mul_le_mul hν1 h1 (norm_nonneg _) zero_le_one
    exact mul_le_mul this hB (nrm2_nonneg _) (by positivity)
  nlinarith

/-- Step 3, complex: for the bilinear `dot`, `u_y · (u_x - u_y) = -½ (u_x - u_y) · (u_x - u_y)`
whenever `u_x · u_x = u_y · u_y = 1`. -/
theorem dot_unit_sub {u v : Fin N → ℂ} (hu : dot u u = 1) (hv : dot v v = 1) :
    dot u (v - u) = -(1 / 2) * dot (v - u) (v - u) := by
  simp only [dot_sub_left, dot_sub_right, hu, hv, dot_comm u v]; ring

/-- The constant of `dotC_source_term_le`. -/
noncomputable def sourceConstC (B : ℝ) : ℝ :=
  (1 + 2 * B) * (2 + 3 * B ^ 2) + (2 + 3 * B ^ 2) ^ 2 / 2

/-- (V), complex case.  Norm: `ℓ²` on `Fin N → ℂ`.  Hypotheses: `|ψ_x·ψ_x - 1| ≤ 1/2` (principal
branch, `|√| ≥ 7/10`), `|ψ_x|₂, |ψ_y|₂ ≤ B`, `|ψ_x - ψ_y|₂ ≤ Dσε`, `|b - νψ_y|₂ ≤ σ²ε`,
`|ψ_y·ψ_y - 1| ≤ σ²ε ≤ 1/2`, `0 ≤ ν ≤ σ² ≤ 1`, `0 ≤ σ ≤ 1`, `ε, D ≥ 0`.  Then
`‖b · (u_x - u_y)‖ ≤ C_B (D² + D) σ³ ε²`, with `C_B = (1+2B)(2+3B²) + (2+3B²)²/2`.
The dependence on `B` is genuine: for complex vectors `|ψ·ψ - 1|` small does not bound `|ψ|₂`. -/
theorem dotC_source_term_le {ψx ψy b : Fin N → ℂ} {B ν σ ε D : ℝ}
    (hax : ‖dot ψx ψx - 1‖ ≤ 1 / 2) (hBx : nrm2 ψx ≤ B) (hBy : nrm2 ψy ≤ B)
    (hD : nrm2 (ψx - ψy) ≤ D * σ * ε) (hb : nrm2 (b - (ν : ℂ) • ψy) ≤ σ ^ 2 * ε)
    (hn : ‖dot ψy ψy - 1‖ ≤ σ ^ 2 * ε) (hη : σ ^ 2 * ε ≤ 1 / 2) (hν0 : 0 ≤ ν)
    (hνσ : ν ≤ σ ^ 2) (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1) (hε0 : 0 ≤ ε) (hD0 : 0 ≤ D) :
    ‖dot b (unitDirC ψx - unitDirC ψy)‖ ≤ sourceConstC B * (D ^ 2 + D) * σ ^ 3 * ε ^ 2 := by
  have hσ2 : σ ^ 2 ≤ 1 := by nlinarith
  have hν1 : ν ≤ 1 := hνσ.trans hσ2
  have hay : ‖dot ψy ψy - 1‖ ≤ 1 / 2 := hn.trans hη
  have hB0 : 0 ≤ B := (nrm2_nonneg _).trans hBx
  have hxu : dot (unitDirC ψx) (unitDirC ψx) = 1 :=
    unitDirC_dot (dot_ne_zero_of_near hax)
  have hyu : dot (unitDirC ψy) (unitDirC ψy) = 1 :=
    unitDirC_dot (dot_ne_zero_of_near hay)
  have hw : nrm2 (unitDirC ψx - unitDirC ψy) ≤ (2 + 3 * B ^ 2) * (D * σ * ε) :=
    (unitDirC_sub_le hax hay hBx hBy).trans (mul_le_mul_of_nonneg_left hD (by positivity))
  have hc : nrm2 (b - (ν : ℂ) • unitDirC ψy) ≤ (1 + 2 * B) * (σ ^ 2 * ε) :=
    source_sub_le_C hη hn hBy hν0 hν1 hb
  set w := unitDirC ψx - unitDirC ψy with hwdef
  have hid : dot (unitDirC ψy) w = -(1 / 2) * dot w w := dot_unit_sub hyu hxu
  have e : dot b w = dot (b - (ν : ℂ) • unitDirC ψy) w + (ν : ℂ) * dot (unitDirC ψy) w := by
    rw [dot_sub_left, dot_smul_left]; ring
  rw [e, hid]
  have hw0 := nrm2_nonneg w
  set K := 2 + 3 * B ^ 2 with hK
  have hK0 : 0 ≤ K := by positivity
  have t1 : ‖dot (b - (ν : ℂ) • unitDirC ψy) w‖ ≤ (1 + 2 * B) * (σ ^ 2 * ε) * (K * (D * σ * ε)) :=
    (norm_dot_le _ _).trans (mul_le_mul hc hw hw0 (by positivity))
  have t2 : ‖(ν : ℂ) * (-(1 / 2) * dot w w)‖ ≤ ν * (1 / 2) * nrm2 w ^ 2 := by
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hν0]
    have : ‖dot w w‖ ≤ nrm2 w ^ 2 := by rw [sq]; exact norm_dot_le _ _
    have h12 : ‖(-(1 / 2 : ℂ))‖ = 1 / 2 := by simp
    rw [h12]
    calc ν * (1 / 2 * ‖dot w w‖) ≤ ν * (1 / 2 * nrm2 w ^ 2) := by gcongr
      _ = _ := by ring
  have t3 : ν * (1 / 2) * nrm2 w ^ 2 ≤ σ ^ 2 * (1 / 2) * (K * (D * σ * ε)) ^ 2 := by
    have : nrm2 w ^ 2 ≤ (K * (D * σ * ε)) ^ 2 := pow_le_pow_left₀ hw0 hw 2
    calc ν * (1 / 2) * nrm2 w ^ 2 ≤ σ ^ 2 * (1 / 2) * nrm2 w ^ 2 := by gcongr
      _ ≤ _ := by gcongr
  have s4 : σ ^ 4 ≤ σ ^ 3 := pow_le_pow_of_le_one hσ0 hσ1 (by norm_num)
  have t4 : σ ^ 2 * (1 / 2) * (K * (D * σ * ε)) ^ 2 ≤ K ^ 2 / 2 * D ^ 2 * σ ^ 3 * ε ^ 2 := by
    have h8 : 0 ≤ K ^ 2 / 2 * D ^ 2 * ε ^ 2 := by positivity
    nlinarith [mul_le_mul_of_nonneg_left s4 h8]
  have hfin : (1 + 2 * B) * (σ ^ 2 * ε) * (K * (D * σ * ε)) + K ^ 2 / 2 * D ^ 2 * σ ^ 3 * ε ^ 2
      ≤ sourceConstC B * (D ^ 2 + D) * σ ^ 3 * ε ^ 2 := by
    unfold sourceConstC
    rw [← hK]
    have hp : 0 ≤ σ ^ 3 * ε ^ 2 := by positivity
    have h1 : 0 ≤ (1 + 2 * B) * K := by positivity
    have h2 : 0 ≤ K ^ 2 / 2 := by positivity
    have : (1 + 2 * B) * (σ ^ 2 * ε) * (K * (D * σ * ε)) =
        (1 + 2 * B) * K * D * (σ ^ 3 * ε ^ 2) := by ring
    rw [this]
    have h3 : K ^ 2 / 2 * D ^ 2 * σ ^ 3 * ε ^ 2 = K ^ 2 / 2 * D ^ 2 * (σ ^ 3 * ε ^ 2) := by ring
    rw [h3]
    have h4 : ((1 + 2 * B) * K + K ^ 2 / 2) * (D ^ 2 + D) * σ ^ 3 * ε ^ 2 =
        ((1 + 2 * B) * K + K ^ 2 / 2) * (D ^ 2 + D) * (σ ^ 3 * ε ^ 2) := by ring
    rw [h4]
    have hDD : 0 ≤ D ^ 2 := sq_nonneg D
    nlinarith [mul_nonneg (mul_nonneg h1 hD0) hp, mul_nonneg (mul_nonneg h2 hDD) hp,
      mul_nonneg (mul_nonneg h1 hDD) hp, mul_nonneg (mul_nonneg h2 hD0) hp]
  refine (norm_add_le _ _).trans ?_
  have : ‖dot (b - (ν : ℂ) • unitDirC ψy) w‖ + ‖(ν : ℂ) * (-(1 / 2) * dot w w)‖ ≤
      (1 + 2 * B) * (σ ^ 2 * ε) * (K * (D * σ * ε)) + K ^ 2 / 2 * D ^ 2 * σ ^ 3 * ε ^ 2 := by
    linarith
  linarith

/-- Non-vacuity of the complex case: `ψ_x = ψ_y = e₀`, `b = 0`, `ν = 0`, `D = 0`, `σ = ε = 1/2`,
`B = 1` (`N = 1`). -/
theorem dotC_source_term_sample :
    ‖dot (0 : Fin 1 → ℂ) (unitDirC (Pi.single 0 1 : Fin 1 → ℂ) - unitDirC (Pi.single 0 1))‖ ≤
      sourceConstC 1 * (0 ^ 2 + 0) * (1 / 2 : ℝ) ^ 3 * (1 / 2 : ℝ) ^ 2 := by
  have h1 : nrm2 (Pi.single 0 1 : Fin 1 → ℂ) ≤ 1 := by
    rw [nrm2_eq]; simp
  have h0 : dot (Pi.single 0 1 : Fin 1 → ℂ) (Pi.single 0 1) = 1 := by
    simp [dot_single_left]
  refine dotC_source_term_le (ψx := Pi.single 0 1) (ψy := Pi.single 0 1) (ν := 0) (B := 1)
    (σ := 1 / 2) (ε := 1 / 2) (D := 0) (by rw [h0]; norm_num) h1 h1 (by simp [nrm2_eq])
    (by simp [nrm2_eq]) (by rw [h0]; norm_num) (by norm_num) le_rfl (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) le_rfl

end Complex

end Balaban.LargeField.RegionalArith
