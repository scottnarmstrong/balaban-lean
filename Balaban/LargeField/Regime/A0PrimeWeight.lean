module

public import Balaban.LargeField.LF1.Setup
public import Balaban.LargeField.R.PositiveMassFacts
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The weight on the common support (route R-YM, leaf `weight_common_support`)

Under the hybrid convention A0' the sharp supports are massless; the mass `m` and the source
`b = m h` enter only the weight `exp (-β (A^{m,b} - A^0))`, compared on one field and one support.

* `actionG_sub_massless`: the landed action at mass `μ` minus the massless action is
  `μ/2 ∑_{x ∈ X} ‖φ x - h‖²`.
* `weight_real_bounds`: for unit `φ` on `X`, unit `h`, `β μ ≤ E`:
  `exp (-2 E |X|) ≤ exp (-β (A^{μ,h} - A^0)) ≤ 1`.
* the mass term `μ/2 ∑_{x ∈ C} ∑_i (φ x i - h i)²` continued to a complex source (bilinear square), real on real
  sources (`massTermC_ofReal`; no definition, the expression is written out), entire (`differentiable_massTermC`), and
  `norm_exp_neg_massTermC_le`: for real `φ`, `‖exp (-β M)‖ ≤ exp (β μ |C| ‖Im h‖² / 2)`.
* the one-block value `R - c = c (1 + (q/c)²)^(1/2) - c`, `R = √(c² + q²)`, `c = a + m`, as an analytic
  function of the complex transverse source `q` on `|q| < c`
  (`analyticOn_blockGap`), equal to `q²/(R + c)` (`blockGap_mul_add`) and with
  `‖exp (-β (R - c))‖ ≤ exp (β |q|² / c)` (`norm_exp_neg_blockGap_le`).  The constant
  `1/(2c)` is false for imaginary `q` (`blockGap_re_lt_of_imag`): the constant is `1/c`.
-/

@[expose] public section

namespace Balaban.LargeField

open Balaban Balaban.Multiscale Balaban.Background

section Real

variable {d L N₀ q : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}

theorem actionG_sub_massless {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (G : GeneratingSet d L N₀ q ϱ) (a : ℕ → ℝ) (μ : ℝ) (h : E) (X : Finset (Site d L N₀ q))
    (ψ : (m : ℕ) → Blk d L N₀ q m → E) (φ : Site d L N₀ q → E) :
    actionG G a μ h X ψ φ - actionG G a 0 h X ψ φ = μ / 2 * ∑ x ∈ X, ‖φ x - h‖ ^ 2 := by
  unfold actionG; ring

/-- (5.1) for the landed action: on a common field and support. -/
theorem weight_real_bounds {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (G : GeneratingSet d L N₀ q ϱ) (a : ℕ → ℝ) {μ β Eb : ℝ} (h : E) (X : Finset (Site d L N₀ q))
    (ψ : (m : ℕ) → Blk d L N₀ q m → E) (φ : Site d L N₀ q → E)
    (hφ : ∀ x ∈ X, ‖φ x‖ = 1) (hh : ‖h‖ = 1) (hβ : 0 ≤ β) (hμ : 0 ≤ μ) (hE : β * μ ≤ Eb) :
    Real.exp (-(2 * Eb * X.card)) ≤
        Real.exp (-(β * (actionG G a μ h X ψ φ - actionG G a 0 h X ψ φ))) ∧
      Real.exp (-(β * (actionG G a μ h X ψ φ - actionG G a 0 h X ψ φ))) ≤ 1 := by
  rw [actionG_sub_massless]
  have := real_mass_cost_exp X φ h hφ hh hβ hμ hE
  have e : β * (μ / 2 * ∑ x ∈ X, ‖φ x - h‖ ^ 2) = 1 / 2 * β * μ * ∑ x ∈ X, ‖φ x - h‖ ^ 2 := by
    ring
  rw [e]; exact this

end Real

section Complex

variable {ι : Type*} {N : ℕ}

theorem massTermC_ofReal (μ : ℝ) (C : Finset ι) (φ : ι → EuclideanSpace ℝ (Fin N))
    (h : EuclideanSpace ℝ (Fin N)) :
    ((((μ) / 2 : ℝ) : ℂ) * ∑ x ∈ C, ∑ i, (((((fun x i => φ x i)) x i : ℝ) : ℂ) - ((fun i => ((h i : ℝ) : ℂ))) i) ^ 2) =
      ((μ / 2 * ∑ x ∈ C, ‖φ x - h‖ ^ 2 : ℝ) : ℂ) := by
  push_cast
  congr 1
  refine Finset.sum_congr rfl fun x _ => ?_
  have h1 : ‖φ x - h‖ ^ 2 = ∑ i, (φ x i - h i) ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    exact Finset.sum_congr rfl fun i _ => by simp [Real.norm_eq_abs, sq_abs]
  rw [← Complex.ofReal_pow, h1]
  push_cast
  rfl

theorem differentiable_massTermC (μ : ℝ) (C : Finset ι) (φ : ι → Fin N → ℝ) :
    Differentiable ℂ (fun h : Fin N → ℂ => ((((μ) / 2 : ℝ) : ℂ) * ∑ x ∈ C, ∑ i, ((((φ) x i : ℝ) : ℂ) - (h) i) ^ 2)) := by
  fun_prop

theorem re_massTermC_ge (μ : ℝ) (hμ : 0 ≤ μ) (C : Finset ι) (φ : ι → Fin N → ℝ)
    (h : Fin N → ℂ) :
    -(μ / 2 * C.card * ∑ i, (h i).im ^ 2) ≤ (((((μ) / 2 : ℝ) : ℂ) * ∑ x ∈ C, ∑ i, ((((φ) x i : ℝ) : ℂ) - (h) i) ^ 2)).re := by
  rw [Complex.re_ofReal_mul]
  have key : ∀ x ∈ C, -(∑ i, (h i).im ^ 2) ≤ (∑ i, (((φ x i : ℝ) : ℂ) - h i) ^ 2).re := by
    intro x _
    rw [Complex.re_sum]
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_le_sum fun i _ => ?_
    simp only [sq, Complex.mul_re, Complex.sub_re, Complex.ofReal_re, Complex.sub_im,
      Complex.ofReal_im]
    nlinarith [sq_nonneg (φ x i - (h i).re)]
  rw [Complex.re_sum]
  have : -(C.card * ∑ i, (h i).im ^ 2) ≤ ∑ x ∈ C, (∑ i, (((φ x i : ℝ) : ℂ) - h i) ^ 2).re := by
    have := Finset.sum_le_sum key
    simpa [Finset.sum_const, nsmul_eq_mul] using this
  have hμ2 : 0 ≤ μ / 2 := by positivity
  nlinarith

/-- Modulus of the weight at a complex source: `‖exp (-β M)‖ ≤ exp (β μ |C| ‖Im h‖² / 2)`. -/
theorem norm_exp_neg_massTermC_le (μ β : ℝ) (hμ : 0 ≤ μ) (hβ : 0 ≤ β) (C : Finset ι)
    (φ : ι → Fin N → ℝ) (h : Fin N → ℂ) :
    ‖Complex.exp (-((β : ℂ) * ((((μ) / 2 : ℝ) : ℂ) * ∑ x ∈ C, ∑ i, ((((φ) x i : ℝ) : ℂ) - (h) i) ^ 2)))‖ ≤
      Real.exp (β * μ / 2 * C.card * ∑ i, (h i).im ^ 2) := by
  rw [Complex.norm_exp]
  apply Real.exp_le_exp.2
  have := re_massTermC_ge μ hμ C φ h
  simp only [Complex.neg_re, Complex.re_ofReal_mul] at this ⊢
  have h2 := mul_le_mul_of_nonneg_left this hβ
  linarith

end Complex

section Block

theorem analyticOn_blockGap {c : ℝ} (hc : 0 < c) :
    AnalyticOn ℂ (fun q : ℂ => (c : ℂ) * (1 + (q / c) ^ 2) ^ (1 / 2 : ℂ) - c) (Metric.ball 0 c) := by
  have hcne : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  have h1 : AnalyticOn ℂ (fun q : ℂ => 1 + (q / c) ^ 2) (Metric.ball 0 c) := by
    intro q _
    have : AnalyticAt ℂ (fun q : ℂ => 1 + (q / c) ^ 2) q := by fun_prop
    exact this.analyticWithinAt
  have h2 : AnalyticOn ℂ (fun q : ℂ => (1 + (q / c) ^ 2) ^ (1 / 2 : ℂ)) (Metric.ball 0 c) := by
    refine h1.cpow analyticOn_const fun q hq => ?_
    have hqn : ‖q‖ < c := by simpa using hq
    apply Complex.mem_slitPlane_of_norm_lt_one
    rw [norm_pow, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc]
    exact pow_lt_one₀ (by positivity) ((div_lt_one hc).2 hqn) (by norm_num)
  intro q hq
  exact ((analyticOn_const.mul h2) q hq).sub (analyticOn_const q hq)

/-- The square root `w = (1 + z)^(1/2)` for `‖z‖ < 1`: `w² = 1 + z`, `0 ≤ Re w`. -/
theorem sqrt_one_add_facts {z : ℂ} (hz : ‖z‖ < 1) :
    ((1 + z) ^ (1 / 2 : ℂ)) ^ 2 = 1 + z ∧ 0 ≤ ((1 + z) ^ (1 / 2 : ℂ)).re := by
  refine ⟨?_, ?_⟩
  · have := Complex.cpow_ofNat_inv_pow (1 + z) 2
    simp [one_div]
  · have hs := Complex.mem_slitPlane_of_norm_lt_one hz
    have hne : (1 + z) ≠ 0 := Complex.slitPlane_ne_zero hs
    rw [Complex.cpow_def_of_ne_zero hne, Complex.exp_re]
    refine mul_nonneg (Real.exp_pos _).le ?_
    have harg := Complex.neg_pi_lt_arg (1 + z)
    have harg2 := Complex.arg_le_pi (1 + z)
    have : (Complex.log (1 + z) * (1 / 2 : ℂ)).im = Complex.arg (1 + z) / 2 := by
      simp [Complex.log_im]; ring
    rw [this]
    apply Real.cos_nonneg_of_mem_Icc
    constructor <;> linarith [Real.pi_pos]

theorem norm_sqrt_sub_one_le {z : ℂ} (hz : ‖z‖ < 1) :
    ‖(1 + z) ^ (1 / 2 : ℂ) - 1‖ ≤ ‖z‖ := by
  obtain ⟨h2, h0⟩ := sqrt_one_add_facts hz
  set w := (1 + z) ^ (1 / 2 : ℂ)
  have hw : (w - 1) * (w + 1) = z := by linear_combination h2
  have hge : 1 ≤ ‖w + 1‖ := by
    have : (w + 1).re ≤ ‖w + 1‖ := Complex.re_le_norm _
    simp at this; linarith
  calc ‖w - 1‖ ≤ ‖w - 1‖ * ‖w + 1‖ := le_mul_of_one_le_right (norm_nonneg _) hge
    _ = ‖z‖ := by rw [← norm_mul, hw]

theorem blockGap_re_ge {c : ℝ} (hc : 0 < c) {q : ℂ} (hq : ‖q‖ < c) :
    -(‖q‖ ^ 2 / c) ≤ (((c : ℂ) * (1 + (q / c) ^ 2) ^ (1 / 2 : ℂ) - c)).re := by
  have hz : ‖(q / c) ^ 2‖ < 1 := by
    rw [norm_pow, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc]
    exact pow_lt_one₀ (by positivity) ((div_lt_one hc).2 hq) (by norm_num)
  have h := norm_sqrt_sub_one_le hz
  have hre : -‖(1 + (q / c) ^ 2) ^ (1 / 2 : ℂ) - 1‖ ≤
      ((1 + (q / c) ^ 2) ^ (1 / 2 : ℂ) - 1).re := by
    have := Complex.abs_re_le_norm ((1 + (q / c) ^ 2) ^ (1 / 2 : ℂ) - 1)
    linarith [neg_abs_le ((1 + (q / c) ^ 2) ^ (1 / 2 : ℂ) - 1).re]
  have hn : ‖(q / c) ^ 2‖ = ‖q‖ ^ 2 / c ^ 2 := by
    rw [norm_pow, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc]; ring
  have e : ((c : ℂ) * (1 + (q / c) ^ 2) ^ (1 / 2 : ℂ) - c) =
      (c : ℂ) * ((1 + (q / c) ^ 2) ^ (1 / 2 : ℂ) - 1) := by ring
  rw [e, Complex.re_ofReal_mul]
  have : -(‖q‖ ^ 2 / c ^ 2) ≤ ((1 + (q / c) ^ 2) ^ (1 / 2 : ℂ) - 1).re := by
    rw [hn] at h; linarith
  have h3 := mul_le_mul_of_nonneg_left this hc.le
  have e2 : c * -(‖q‖ ^ 2 / c ^ 2) = -(‖q‖ ^ 2 / c) := by field_simp
  linarith

/-- Modulus of the block weight on the polydisc `|q| < c`: `‖exp (-β (R - c))‖ ≤ exp (β |q|²/c)`. -/
theorem norm_exp_neg_blockGap_le {c : ℝ} (hc : 0 < c) {β : ℝ} (hβ : 0 ≤ β) {q : ℂ}
    (hq : ‖q‖ < c) :
    ‖Complex.exp (-((β : ℂ) * ((c : ℂ) * (1 + (q / c) ^ 2) ^ (1 / 2 : ℂ) - c)))‖ ≤ Real.exp (β * ‖q‖ ^ 2 / c) := by
  rw [Complex.norm_exp]
  apply Real.exp_le_exp.2
  have := blockGap_re_ge hc hq
  simp only [Complex.neg_re, Complex.re_ofReal_mul]
  have := mul_le_mul_of_nonneg_left this hβ
  have e : β * (‖q‖ ^ 2 / c) = β * ‖q‖ ^ 2 / c := by ring
  linarith

/-- The block gap is `q² / (R + c)`. -/
theorem blockGap_mul_add {c : ℝ} (hc : 0 < c) {q : ℂ} (hq : ‖q‖ < c) :
    ((c : ℂ) * (1 + (q / c) ^ 2) ^ (1 / 2 : ℂ) - c) * ((c : ℂ) * (1 + (q / c) ^ 2) ^ (1 / 2 : ℂ) + c) = q ^ 2 := by
  have hcne : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  have hz : ‖(q / c) ^ 2‖ < 1 := by
    rw [norm_pow, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc]
    exact pow_lt_one₀ (by positivity) ((div_lt_one hc).2 hq) (by norm_num)
  obtain ⟨h2, _⟩ := sqrt_one_add_facts hz
  set w := (1 + (q / c) ^ 2) ^ (1 / 2 : ℂ)
  have : (c : ℂ) ^ 2 * (w ^ 2 - 1) = q ^ 2 := by
    rw [h2]; field_simp; ring
  linear_combination this

/-- The constant `1/(2c)` in the modulus bound is false: for imaginary `q = i t`, `0 < t < c`,
`-Re (R - c) > t² / (2c)`. -/
theorem blockGap_re_lt_of_imag {c t : ℝ} (hc : 0 < c) (ht : 0 < t) (htc : t < c) :
    (((c : ℂ) * (1 + (((t : ℂ) * Complex.I) / c) ^ 2) ^ (1 / 2 : ℂ) - c)).re < -(t ^ 2 / (2 * c)) := by
  have hr : 0 < 1 - (t / c) ^ 2 := by
    have : t / c < 1 := (div_lt_one hc).2 htc
    have : 0 < t / c := by positivity
    nlinarith
  have e1 : (1 + (((t : ℂ) * Complex.I) / c) ^ 2) = ((1 - (t / c) ^ 2 : ℝ) : ℂ) := by
    push_cast
    have : ((t : ℂ) * Complex.I / c) ^ 2 = -((t : ℂ) / c) ^ 2 := by
      rw [div_pow, mul_pow, Complex.I_sq]; ring
    rw [this]; ring
  have e2 : ((1 - (t / c) ^ 2 : ℝ) : ℂ) ^ (1 / 2 : ℂ) = ((Real.sqrt (1 - (t / c) ^ 2) : ℝ) : ℂ) := by
    rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; rfl, ← Complex.ofReal_cpow hr.le,
      ← Real.sqrt_eq_rpow]
  rw [e1, e2]
  simp only [Complex.sub_re, Complex.re_ofReal_mul, Complex.ofReal_re]
  set r := (t / c) ^ 2 with hrdef
  set s := Real.sqrt (1 - r) with hs
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hs2 : s ^ 2 = 1 - r := Real.sq_sqrt hr.le
  have hrpos : 0 < r := by positivity
  have hs1 : s < 1 := by nlinarith
  have hrt : r = t ^ 2 / c ^ 2 := by rw [hrdef, div_pow]
  have key : c * s - c < -(t ^ 2 / (2 * c)) := by
    have : t ^ 2 / (2 * c) = c * r / 2 := by rw [hrt]; field_simp
    rw [this]
    nlinarith [mul_pos hc (sq_pos_of_pos (show 0 < 1 - s by linarith))]
  exact key

end Block

end Balaban.LargeField
