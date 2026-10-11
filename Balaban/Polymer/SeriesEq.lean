module

public import Mathlib

/-!
# The exponential identity for a convolution recursion

If `a`, `z : ℕ → ℂ` have summable norms, `a 0 = 0`, `z 0 = 1` and
`(n+1) z_{n+1} = - ∑_{m ≤ n} (m+1) a_{m+1} z_{n-m}`, then `∑ z_n = exp (- ∑ a_n)`.
Proof: the power series `Z(x) exp(A(x))` has derivative zero on `(-1, 1)`.
-/

@[expose] public section

noncomputable section

open Finset Set

namespace Balaban.Polymer

theorem summable_mul_geom {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    Summable (fun n : ℕ => (n : ℝ) * r ^ (n - 1)) := by
  have h := summable_pow_mul_geometric_of_norm_lt_one 1 (r := r) (by rwa [Real.norm_of_nonneg hr0.le])
  have h2 := h.div_const r
  refine h2.congr (fun n => ?_)
  rcases n with _ | n
  · simp
  · simp only [pow_one, Nat.add_sub_cancel]
    field_simp
    ring

theorem summable_deriv_terms (c : ℕ → ℂ) (hc : Summable (fun n => ‖c n‖)) {x : ℝ}
    (hx : |x| < 1) : Summable (fun n : ℕ => ‖(n : ℂ) * c n * (x : ℂ) ^ (n - 1)‖) := by
  set B := ∑' n, ‖c n‖
  have hB : ∀ n, ‖c n‖ ≤ B := fun n => hc.le_tsum n (fun _ _ => norm_nonneg _)
  have hr0 : 0 < (|x| + 1) / 2 := by positivity
  have hr1 : (|x| + 1) / 2 < 1 := by linarith
  have hxr : |x| ≤ (|x| + 1) / 2 := by linarith
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ?_)
    ((summable_mul_geom hr0 hr1).mul_left B)
  rw [norm_mul, norm_mul, norm_pow, Complex.norm_natCast, Complex.norm_real, Real.norm_eq_abs]
  calc (n : ℝ) * ‖c n‖ * |x| ^ (n - 1) ≤ (n : ℝ) * B * ((|x| + 1) / 2) ^ (n - 1) := by
        gcongr
        exact hB n
    _ = B * ((n : ℝ) * ((|x| + 1) / 2) ^ (n - 1)) := by ring

theorem hasDerivAt_powSeries (c : ℕ → ℂ) (hc : Summable (fun n => ‖c n‖)) {x : ℝ}
    (hx : |x| < 1) :
    HasDerivAt (fun y : ℝ => ∑' n, c n * (y : ℂ) ^ n)
      (∑' n : ℕ, (n : ℂ) * c n * (x : ℂ) ^ (n - 1)) x := by
  set B := ∑' n, ‖c n‖
  have hB : ∀ n, ‖c n‖ ≤ B := fun n => hc.le_tsum n (fun _ _ => norm_nonneg _)
  set r : ℝ := (|x| + 1) / 2 with hr
  have hr0 : 0 < r := by positivity
  have hr1 : r < 1 := by rw [hr]; linarith
  have hxr : |x| < r := by rw [hr]; linarith
  have key := hasDerivAt_tsum_of_isPreconnected
    (g := fun (n : ℕ) (y : ℝ) => c n * (y : ℂ) ^ n)
    (g' := fun (n : ℕ) (y : ℝ) => (n : ℂ) * c n * (y : ℂ) ^ (n - 1))
    (u := fun n : ℕ => B * ((n : ℝ) * r ^ (n - 1)))
    ((summable_mul_geom hr0 hr1).mul_left B) (isOpen_Ioo (a := -r) (b := r)) isPreconnected_Ioo
    (t := Ioo (-r) r) ?_ ?_ (y₀ := 0) (by simp [hr0]) ?_ (y := x) (by rw [Set.mem_Ioo]; constructor <;> linarith [abs_lt.mp hxr])
  · exact key
  · intro n y _
    have := ((hasDerivAt_pow n (y : ℂ)).comp_ofReal).const_mul (c n)
    convert this using 1
    ring
  · intro n y hy
    rw [Set.mem_Ioo] at hy
    have hyr : |y| ≤ r := abs_le.mpr ⟨by linarith, by linarith⟩
    rw [norm_mul, norm_mul, norm_pow, Complex.norm_natCast, Complex.norm_real, Real.norm_eq_abs]
    calc (n : ℝ) * ‖c n‖ * |y| ^ (n - 1) ≤ (n : ℝ) * B * r ^ (n - 1) := by
          gcongr
          exact hB n
      _ = B * ((n : ℝ) * r ^ (n - 1)) := by ring
  · refine hc.of_norm_bounded (fun n => ?_)
    rw [norm_mul, norm_pow]
    simp only [Complex.ofReal_zero, norm_zero]
    exact mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ (le_refl _) zero_le_one)

theorem continuousOn_powSeries (c : ℕ → ℂ) (hc : Summable (fun n => ‖c n‖)) :
    ContinuousOn (fun y : ℝ => ∑' n, c n * (y : ℂ) ^ n) (Set.Icc 0 1) := by
  refine continuousOn_tsum (u := fun n => ‖c n‖) (fun n => ?_) hc (fun n y hy => ?_)
  · fun_prop
  · rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
    refine mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ (abs_nonneg _) ?_)
    rw [abs_le]; constructor <;> linarith [hy.1, hy.2]

theorem tsum_deriv_shift (c : ℕ → ℂ) (hc : Summable (fun n => ‖c n‖)) {x : ℝ} (hx : |x| < 1) :
    ∑' n : ℕ, (n : ℂ) * c n * (x : ℂ) ^ (n - 1) =
      ∑' n : ℕ, ((n : ℂ) + 1) * c (n + 1) * (x : ℂ) ^ n := by
  have hs := (summable_deriv_terms c hc hx).of_norm
  rw [hs.tsum_eq_zero_add]
  simp

theorem exp_eq (a z : ℕ → ℂ) (ha0 : a 0 = 0) (hz0 : z 0 = 1)
    (hrec : ∀ n : ℕ, ((n : ℂ) + 1) * z (n + 1) =
      -∑ m ∈ range (n + 1), ((m : ℂ) + 1) * a (m + 1) * z (n - m))
    (ha : Summable (fun n => ‖a n‖)) (hz : Summable (fun n => ‖z n‖)) :
    ∑' n, z n = Complex.exp (-∑' n, a n) := by
  set Zf : ℝ → ℂ := fun y => ∑' n, z n * (y : ℂ) ^ n with hZf
  set Af : ℝ → ℂ := fun y => ∑' n, a n * (y : ℂ) ^ n with hAf
  have hder : ∀ x : ℝ, |x| < 1 → HasDerivAt (fun y => Zf y * Complex.exp (Af y)) 0 x := by
    intro x hx
    have hZ := hasDerivAt_powSeries z hz hx
    have hA := hasDerivAt_powSeries a ha hx
    have hP := hZ.mul (hA.cexp)
    convert hP using 1
    -- Z' = - A' * Z
    have hfs : Summable (fun m : ℕ => ‖((m : ℂ) + 1) * a (m + 1) * (x : ℂ) ^ m‖) := by
      have := (summable_nat_add_iff 1).mpr (summable_deriv_terms a ha hx)
      refine this.congr (fun m => ?_)
      simp
    have hgs : Summable (fun k : ℕ => ‖z k * (x : ℂ) ^ k‖) := by
      refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun k => ?_) hz
      rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ (abs_nonneg _) hx.le)
    have hcauchy := tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm hfs hgs
    have h1 : ∑' n : ℕ, (n : ℂ) * z n * (x : ℂ) ^ (n - 1) =
        -((∑' n : ℕ, (n : ℂ) * a n * (x : ℂ) ^ (n - 1)) * Zf x) := by
      rw [tsum_deriv_shift z hz hx, tsum_deriv_shift a ha hx, hZf]
      simp only
      rw [hcauchy, ← tsum_neg]
      refine tsum_congr (fun n => ?_)
      have e : ∑ k ∈ range (n + 1), ((k : ℂ) + 1) * a (k + 1) * (x : ℂ) ^ k * (z (n - k) * (x : ℂ) ^ (n - k))
          = (∑ k ∈ range (n + 1), ((k : ℂ) + 1) * a (k + 1) * z (n - k)) * (x : ℂ) ^ n := by
        rw [Finset.sum_mul]
        refine sum_congr rfl (fun k hk => ?_)
        have hkn : k ≤ n := by have := mem_range.mp hk; omega
        have : (x : ℂ) ^ n = (x : ℂ) ^ k * (x : ℂ) ^ (n - k) := by
          rw [← pow_add]; congr 1; omega
        rw [this]; ring
      rw [e]
      linear_combination (x : ℂ) ^ n * hrec n
    rw [h1]
    ring
  have hF1 : ∀ x : ℝ, 0 ≤ x → x < 1 → Zf x * Complex.exp (Af x) = 1 := by
    intro x hx0 hx1
    set r : ℝ := (x + 1) / 2 with hr
    have hxr : x < r := by rw [hr]; linarith
    have hr1 : r < 1 := by rw [hr]; linarith
    have hr0 : 0 < r := by rw [hr]; linarith
    have hmem : ∀ y ∈ Set.Ioo (-r) r, |y| < 1 := fun y hy => by
      rw [abs_lt]; constructor <;> linarith [(Set.mem_Ioo.mp hy).1, (Set.mem_Ioo.mp hy).2]
    have hconst := IsOpen.is_const_of_deriv_eq_zero (f := fun y => Zf y * Complex.exp (Af y))
      isOpen_Ioo isPreconnected_Ioo
      (fun y hy => (hder y (hmem y hy)).differentiableAt.differentiableWithinAt)
      (fun y hy => (hder y (hmem y hy)).deriv)
      (Set.mem_Ioo.mpr ⟨by linarith, hxr⟩) (Set.mem_Ioo.mpr ⟨by linarith, hr0⟩)
    rw [hconst]
    have hZ0 : Zf 0 = 1 := by
      rw [hZf]; simp only
      rw [tsum_eq_single 0 (fun n hn => by simp [hn])]
      simp [hz0]
    have hA0 : Af 0 = 0 := by
      rw [hAf]; simp only
      rw [tsum_eq_single 0 (fun n hn => by simp [hn])]
      simp [ha0]
    rw [hZ0, hA0]; simp
  have hcontZ : ContinuousOn Zf (Set.Icc 0 1) := continuousOn_powSeries z hz
  have hcontA : ContinuousOn Af (Set.Icc 0 1) := continuousOn_powSeries a ha
  have hEq : Set.EqOn Zf (fun y => Complex.exp (-Af y)) (Set.Icc 0 1) := by
    refine Set.EqOn.of_subset_closure (s := Set.Ico 0 1) (fun y hy => ?_) hcontZ
      (Complex.continuous_exp.comp_continuousOn hcontA.neg) Set.Ico_subset_Icc_self ?_
    · have := hF1 y hy.1 hy.2
      rw [Complex.exp_neg]
      exact (mul_eq_one_iff_eq_inv₀ (Complex.exp_ne_zero _)).mp this
    · rw [closure_Ico (by norm_num)]
  have h1 := hEq (Set.mem_Icc.mpr ⟨zero_le_one, le_rfl⟩)
  simp only [hZf, hAf, Complex.ofReal_one, one_pow, mul_one] at h1
  exact h1

end Balaban.Polymer
