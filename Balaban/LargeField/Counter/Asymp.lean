module

public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.GCongr

/-!
# Eventual inequalities between polynomials, logarithms and exponentials

`PolyB f m`: `f x ≤ K x^m` on `[1, ∞)`; `LogB f`: `f x ≤ a + b log x` on `[1, ∞)`.
The master lemmas show that products "polynomial × logarithm" are eventually below a higher
power, polynomials are eventually below `c e^{a x}`, and logarithms below `c x`.
They are used to prove `exists_lamStar` (Part I, §I.5.3).
-/

@[expose] public section

open Filter Asymptotics

namespace Balaban.LargeField.Asymp

/-- `f ≤ K x^m` on `[1, ∞)`. -/
def PolyB (f : ℝ → ℝ) (m : ℕ) : Prop := ∃ K : ℝ, 0 ≤ K ∧ ∀ x : ℝ, 1 ≤ x → f x ≤ K * x ^ m

/-- `f ≤ a + b log x` on `[1, ∞)`. -/
def LogB (f : ℝ → ℝ) : Prop := ∃ a b : ℝ, 0 ≤ b ∧ ∀ x : ℝ, 1 ≤ x → f x ≤ a + b * Real.log x

theorem PolyB.mono {f : ℝ → ℝ} {m m' : ℕ} (h : PolyB f m) (hm : m ≤ m') : PolyB f m' := by
  obtain ⟨K, hK, hf⟩ := h
  refine ⟨K, hK, fun x hx => (hf x hx).trans ?_⟩
  exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hx hm) hK

theorem PolyB.add {f g : ℝ → ℝ} {m : ℕ} (hf : PolyB f m) (hg : PolyB g m) :
    PolyB (fun x => f x + g x) m := by
  obtain ⟨K, hK, hf⟩ := hf
  obtain ⟨K', hK', hg⟩ := hg
  refine ⟨K + K', by positivity, fun x hx => ?_⟩
  have := hf x hx; have := hg x hx
  nlinarith

theorem PolyB.const_mul {f : ℝ → ℝ} {m : ℕ} (hf : PolyB f m) {c : ℝ} (hc : 0 ≤ c) :
    PolyB (fun x => c * f x) m := by
  obtain ⟨K, hK, hf⟩ := hf
  refine ⟨c * K, by positivity, fun x hx => ?_⟩
  have := hf x hx
  nlinarith

theorem polyB_pow (m : ℕ) : PolyB (fun x => x ^ m) m := ⟨1, by norm_num, fun x _ => by simp⟩

theorem polyB_const {c : ℝ} (hc : 0 ≤ c) (m : ℕ) : PolyB (fun _ => c) m :=
  ⟨c, hc, fun x hx => by
    have : (1 : ℝ) ≤ x ^ m := one_le_pow₀ hx
    nlinarith⟩

theorem LogB.add {f g : ℝ → ℝ} (hf : LogB f) (hg : LogB g) : LogB (fun x => f x + g x) := by
  obtain ⟨a, b, hb, hf⟩ := hf
  obtain ⟨a', b', hb', hg⟩ := hg
  refine ⟨a + a', b + b', by positivity, fun x hx => ?_⟩
  have := hf x hx; have := hg x hx
  nlinarith

theorem LogB.const_mul {f : ℝ → ℝ} (hf : LogB f) {c : ℝ} (hc : 0 ≤ c) :
    LogB (fun x => c * f x) := by
  obtain ⟨a, b, hb, hf⟩ := hf
  refine ⟨c * a, c * b, by positivity, fun x hx => ?_⟩
  have := hf x hx
  nlinarith

theorem logB_const (c : ℝ) : LogB (fun _ => c) := ⟨c, 0, le_rfl, fun x _ => by simp⟩

theorem LogB.add_const {f : ℝ → ℝ} (hf : LogB f) (c : ℝ) : LogB (fun x => f x + c) := by
  have := hf.add (logB_const c); exact this

/-- `log_L` of a polynomially bounded quantity `≥ 1` is logarithmically bounded. -/
theorem logB_logb {L : ℝ} (hL : 1 < L) {y : ℝ → ℝ} {m : ℕ} (hy : PolyB y m)
    (hy1 : ∀ x : ℝ, 1 ≤ x → 1 ≤ y x) : LogB (fun x => Real.logb L (y x)) := by
  obtain ⟨K, hK, hy⟩ := hy
  have hK1 : 0 < K := by
    have := hy 1 le_rfl
    have := hy1 1 le_rfl
    simp at *; linarith
  have hlogL : 0 < Real.log L := Real.log_pos hL
  refine ⟨Real.log K / Real.log L, m / Real.log L, by positivity, fun x hx => ?_⟩
  have hx0 : 0 < x := by linarith
  have h1 : y x ≤ K * x ^ m := hy x hx
  have h2 : 0 < y x := lt_of_lt_of_le one_pos (hy1 x hx)
  have h3 : Real.logb L (y x) ≤ Real.logb L (K * x ^ m) :=
    Real.logb_le_logb_of_le hL h2 h1
  have h4 : Real.logb L (K * x ^ m) = (Real.log K + m * Real.log x) / Real.log L := by
    rw [Real.logb, Real.log_mul hK1.ne' (by positivity), Real.log_pow]
  rw [h4] at h3
  calc Real.logb L (y x) ≤ _ := h3
    _ = _ := by ring

/-- Logarithms are eventually below `c x`. -/
theorem ev_logB_le {g : ℝ → ℝ} (hg : LogB g) {c : ℝ} (hc : 0 < c) :
    ∀ᶠ x in atTop, g x ≤ c * x := by
  obtain ⟨a, b, hb, hg⟩ := hg
  have hε : (0 : ℝ) < c / (2 * (b + 1)) := by positivity
  have h1 := Real.isLittleO_log_id_atTop.def hε
  have h2 : ∀ᶠ x : ℝ in atTop, 2 * |a| / c ≤ x := eventually_ge_atTop _
  have h3 : ∀ᶠ x : ℝ in atTop, 1 ≤ x := eventually_ge_atTop _
  filter_upwards [h1, h2, h3] with x hx1 hx2 hx3
  have hx0 : 0 < x := by linarith
  have hl : Real.log x ≤ c / (2 * (b + 1)) * x := by
    have := hx1
    simp only [id, Real.norm_eq_abs] at this
    rw [abs_of_pos hx0] at this
    exact (le_abs_self _).trans this
  have hlog0 : 0 ≤ Real.log x := Real.log_nonneg hx3
  have e1 : |a| ≤ c / 2 * x := by
    have := mul_le_mul_of_nonneg_left hx2 (show 0 ≤ c by linarith)
    have e : c * (2 * |a| / c) = 2 * |a| := by field_simp
    nlinarith
  have e2 : b * Real.log x ≤ c / 2 * x := by
    have : b * Real.log x ≤ b * (c / (2 * (b + 1)) * x) := mul_le_mul_of_nonneg_left hl hb
    have e : b * (c / (2 * (b + 1)) * x) ≤ c / 2 * x := by
      have : b / (b + 1) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
      calc b * (c / (2 * (b + 1)) * x) = (b / (b + 1)) * (c / 2 * x) := by field_simp
        _ ≤ 1 * (c / 2 * x) := by gcongr
        _ = c / 2 * x := one_mul _
    linarith
  calc g x ≤ a + b * Real.log x := hg x hx3
    _ ≤ |a| + c / 2 * x := by linarith [le_abs_self a]
    _ ≤ c * x := by linarith

/-- A polynomial of degree `m` is eventually below `c x^p` for `m < p`. -/
theorem ev_polyB_le {f : ℝ → ℝ} {m p : ℕ} (hf : PolyB f m) (hmp : m < p) {c : ℝ} (hc : 0 < c) :
    ∀ᶠ x in atTop, f x ≤ c * x ^ p := by
  obtain ⟨K, hK, hf⟩ := hf
  filter_upwards [eventually_ge_atTop (max 1 (K / c))] with x hx
  have hx1 : 1 ≤ x := (le_max_left _ _).trans hx
  have hx2 : K / c ≤ x := (le_max_right _ _).trans hx
  have hxp : x ^ p = x ^ m * x ^ (p - m) := by rw [← pow_add]; congr 1; omega
  have h1 : x ≤ x ^ (p - m) := by
    calc x = x ^ 1 := (pow_one x).symm
      _ ≤ x ^ (p - m) := pow_le_pow_right₀ hx1 (by omega)
  have h2 : K ≤ c * x := by rwa [div_le_iff₀ hc, mul_comm] at hx2
  calc f x ≤ K * x ^ m := hf x hx1
    _ ≤ (c * x ^ (p - m)) * x ^ m := by
      have : K ≤ c * x ^ (p - m) := h2.trans (by gcongr)
      exact mul_le_mul_of_nonneg_right this (by positivity)
    _ = c * x ^ p := by rw [hxp]; ring

/-- `f · g ≤ c x^p` eventually, for `f` polynomial of degree `m < p` and `g` logarithmic. -/
theorem ev_polyB_mul_logB_le {f g : ℝ → ℝ} {m p : ℕ} (hf : PolyB f m) (hg : LogB g)
    (hg0 : ∀ x : ℝ, 1 ≤ x → 0 ≤ g x) (hf0 : ∀ x : ℝ, 1 ≤ x → 0 ≤ f x) (hmp : m < p) {c : ℝ}
    (hc : 0 < c) : ∀ᶠ x in atTop, f x * g x ≤ c * x ^ p := by
  obtain ⟨K, hK, hfK⟩ := hf
  have hc' : 0 < c / (K + 1) := by positivity
  have h1 := ev_logB_le hg hc'
  filter_upwards [h1, eventually_ge_atTop (1 : ℝ)] with x hx hx1
  have hf1 := hfK x hx1
  have hx0 : 0 < x := by linarith
  have hg1 := hg0 x hx1
  have hf2 := hf0 x hx1
  calc f x * g x ≤ (K * x ^ m) * (c / (K + 1) * x) := by
        apply mul_le_mul hf1 hx hg1 (by positivity)
    _ = (K / (K + 1)) * c * x ^ (m + 1) := by field_simp; ring
    _ ≤ 1 * c * x ^ (m + 1) := by
        have : K / (K + 1) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
        gcongr
    _ ≤ c * x ^ p := by
        rw [one_mul]
        exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hx1 (by omega)) hc.le

/-- A polynomial is eventually below `c e^{a x}`. -/
theorem ev_polyB_le_exp {f : ℝ → ℝ} {m : ℕ} (hf : PolyB f m) {a : ℝ} (ha : 0 < a) {c : ℝ}
    (hc : 0 < c) : ∀ᶠ x in atTop, f x ≤ c * Real.exp (a * x) := by
  obtain ⟨K, hK, hf⟩ := hf
  have hε : 0 < c * a ^ m / (K + 1) := by positivity
  have h1 := (Real.isLittleO_pow_exp_atTop (n := m)).comp_tendsto
    (Filter.tendsto_id.const_mul_atTop ha)
  have h2 := h1.def hε
  filter_upwards [h2, eventually_ge_atTop (1 : ℝ)] with x hx hx1
  simp only [Function.comp_apply, id, Real.norm_eq_abs] at hx
  have hxa : 0 < a * x := by positivity
  rw [abs_of_pos (pow_pos hxa m), abs_of_pos (Real.exp_pos _)] at hx
  have e : (a * x) ^ m = a ^ m * x ^ m := mul_pow _ _ _
  rw [e] at hx
  have ham : 0 < a ^ m := by positivity
  have hxm : 0 < x ^ m := by positivity
  have h3 : x ^ m ≤ c / (K + 1) * Real.exp (a * x) := by
    have : a ^ m * x ^ m ≤ c * a ^ m / (K + 1) * Real.exp (a * x) := hx
    have h4 : a ^ m * x ^ m ≤ a ^ m * (c / (K + 1) * Real.exp (a * x)) := by
      calc a ^ m * x ^ m ≤ c * a ^ m / (K + 1) * Real.exp (a * x) := this
        _ = a ^ m * (c / (K + 1) * Real.exp (a * x)) := by ring
    exact le_of_mul_le_mul_left h4 ham
  calc f x ≤ K * x ^ m := hf x hx1
    _ ≤ K * (c / (K + 1) * Real.exp (a * x)) := mul_le_mul_of_nonneg_left h3 hK
    _ = (K / (K + 1)) * (c * Real.exp (a * x)) := by ring
    _ ≤ 1 * (c * Real.exp (a * x)) := by
        have : K / (K + 1) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
        gcongr
    _ = c * Real.exp (a * x) := one_mul _

end Balaban.LargeField.Asymp
