module

public import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Gaussian trees (Part III, Lemma III.1.6: the Gaussian chain on the block tree)

`gaussDens p` is the isotropic Gaussian probability density of precision `p` on a finite-dimensional
real inner product space `V` (the field space `ℝ^N` of the model).  A `GaussTree` is a rooted tree on
the nodes `0, …, n` (parent `par i < i`) whose node `i` carries the probability density
`s_i^d g_{p_i}(s_i ψ_i - μ_i - ∑_{c child of i} α_c ψ_c)` in its variable `ψ_i`.  `GaussTree.integral_Psi`
integrates out every node except the root, for arbitrary positive scales `s_i` and precisions `p_i`:
the result is the Gaussian density of the root with mean `∑ A_i μ_i` and variance `∑ A_i² / p_i`, where
`A_i` is the product of `α_c / s_c` along the path from the root to `i`.

The proof removes the last node (the integral over its variable is `integral_node`, a two-step Gaussian
convolution) and uses the induction hypothesis for the tree with the parent's precision and constant
changed (`GaussTree.elim`).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open MeasureTheory Real

section Gauss

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

/-- The isotropic Gaussian probability density of precision `p` on `V`:
`(p / 2π)^{dim V / 2} exp (-(p/2) ‖u‖²)`. -/
noncomputable def gaussDens (p : ℝ) (u : V) : ℝ :=
  (p / (2 * π)) ^ ((Module.finrank ℝ V : ℝ) / 2) * Real.exp (-(p / 2) * ‖u‖ ^ 2)

theorem gaussDens_pos {p : ℝ} (hp : 0 < p) (u : V) : 0 < gaussDens p u := by
  unfold gaussDens; positivity

theorem integral_exp_sq_shift {S : ℝ} (hS : 0 < S) (c : V) :
    ∫ z : V, Real.exp (-(S / 2) * ‖z - c‖ ^ 2) = (2 * π / S) ^ ((Module.finrank ℝ V : ℝ) / 2) := by
  rw [integral_sub_right_eq_self (fun z : V => Real.exp (-(S / 2) * ‖z‖ ^ 2)) c,
    GaussianFourier.integral_rexp_neg_mul_sq_norm (by positivity : 0 < S / 2)]
  congr 1; field_simp

theorem integral_gaussDens {p : ℝ} (hp : 0 < p) : ∫ u : V, gaussDens p u = 1 := by
  unfold gaussDens
  rw [integral_const_mul, GaussianFourier.integral_rexp_neg_mul_sq_norm (by positivity : 0 < p / 2)]
  have : π / (p / 2) = 2 * π / p := by field_simp
  rw [this, ← Real.mul_rpow (by positivity) (by positivity)]
  have : p / (2 * π) * (2 * π / p) = 1 := by field_simp
  rw [this, Real.one_rpow]

/-- Convolution of two Gaussians: integrating the middle variable of a two-step Gaussian chain
with an affine link `y - α w` (precision `P⁻¹ = r⁻¹ + α² p⁻¹`). -/
theorem integral_gaussDens_conv {p r : ℝ} (hp : 0 < p) (hr : 0 < r) (α : ℝ) (μ y : V) :
    ∫ w : V, gaussDens p (w - μ) * gaussDens r (y - α • w) =
      gaussDens (p * r / (p + α ^ 2 * r)) (y - α • μ) := by
  have hS : 0 < p + α ^ 2 * r := by positivity
  set S := p + α ^ 2 * r with hSdef
  set P := p * r / S with hPdef
  have hP : 0 < P := by positivity
  set c := r * α / S with hcdef
  set y' := y - α • μ with hy'
  have key : ∀ w : V, gaussDens p (w - μ) * gaussDens r (y - α • w) =
      ((p / (2 * π)) ^ ((Module.finrank ℝ V : ℝ) / 2) * (r / (2 * π)) ^ ((Module.finrank ℝ V : ℝ) / 2) *
        Real.exp (-(P / 2) * ‖y'‖ ^ 2)) *
        Real.exp (-(S / 2) * ‖w - (μ + c • y')‖ ^ 2) := by
    intro w
    unfold gaussDens
    have e1 : y - α • w = y' - α • (w - μ) := by
      rw [hy', smul_sub]; abel
    have e2 : w - (μ + c • y') = (w - μ) - c • y' := by abel
    rw [e1, e2]
    set z := w - μ
    have n1 : ‖y' - α • z‖ ^ 2 = ‖y'‖ ^ 2 - 2 * α * inner ℝ y' z + α ^ 2 * ‖z‖ ^ 2 := by
      rw [norm_sub_sq_real, norm_smul, inner_smul_right, mul_pow, Real.norm_eq_abs, sq_abs]; ring
    have n2 : ‖z - c • y'‖ ^ 2 = ‖z‖ ^ 2 - 2 * c * inner ℝ y' z + c ^ 2 * ‖y'‖ ^ 2 := by
      rw [norm_sub_sq_real, norm_smul, inner_smul_right, real_inner_comm, mul_pow, Real.norm_eq_abs, sq_abs]
      ring
    rw [n1, n2]
    have : -(p / 2) * ‖z‖ ^ 2 + -(r / 2) * (‖y'‖ ^ 2 - 2 * α * inner ℝ y' z + α ^ 2 * ‖z‖ ^ 2) =
        -(P / 2) * ‖y'‖ ^ 2 + -(S / 2) * (‖z‖ ^ 2 - 2 * c * inner ℝ y' z + c ^ 2 * ‖y'‖ ^ 2) := by
      rw [hPdef, hcdef]; field_simp; rw [hSdef]; ring
    calc _ = (p / (2 * π)) ^ ((Module.finrank ℝ V : ℝ) / 2) * (r / (2 * π)) ^ ((Module.finrank ℝ V : ℝ) / 2) *
          Real.exp (-(p / 2) * ‖z‖ ^ 2 + -(r / 2) * (‖y'‖ ^ 2 - 2 * α * inner ℝ y' z + α ^ 2 * ‖z‖ ^ 2)) := by
            rw [Real.exp_add]; ring
      _ = _ := by rw [this, Real.exp_add]; ring
  simp_rw [key]
  rw [integral_const_mul, integral_exp_sq_shift hS]
  unfold gaussDens
  have : p / (2 * π) * (r / (2 * π)) * (2 * π / S) = P / (2 * π) := by
    rw [hPdef]; field_simp
  rw [← this, Real.mul_rpow (by positivity) (by positivity),
    Real.mul_rpow (by positivity) (by positivity)]
  ring

/-- Eliminating one node of a Gaussian tree: the node variable `v` carries the probability density
`s^d g_p(s v - μ)` and enters the parent factor `g_r(a - α v)` linearly. -/
theorem integral_node {p r s α : ℝ} (hp : 0 < p) (hr : 0 < r) (hs : 0 < s) (μ a : V) :
    ∫ v : V, (s ^ Module.finrank ℝ V * gaussDens p (s • v - μ)) * gaussDens r (a - α • v) =
      gaussDens (p * r / (p + (α / s) ^ 2 * r)) (a - (α / s) • μ) := by
  have h1 : ∀ v : V, (s ^ Module.finrank ℝ V * gaussDens p (s • v - μ)) * gaussDens r (a - α • v) =
      (fun w : V => s ^ Module.finrank ℝ V *
        (gaussDens p (w - μ) * gaussDens r (a - (α / s) • w))) (s • v) := by
    intro v
    have : a - α • v = a - (α / s) • (s • v) := by
      rw [smul_smul, div_mul_cancel₀ _ hs.ne']
    simp only [this]; ring
  simp_rw [h1]
  rw [MeasureTheory.Measure.integral_comp_smul volume (fun w : V => s ^ Module.finrank ℝ V *
        (gaussDens p (w - μ) * gaussDens r (a - (α / s) • w))) s, integral_const_mul,
    integral_gaussDens_conv hp hr]
  simp only [smul_eq_mul]
  rw [abs_of_pos (by positivity)]
  field_simp

theorem integrable_node {p r s α : ℝ} (hp : 0 < p) (hr : 0 < r) (hs : 0 < s) (μ a : V) :
    MeasureTheory.Integrable fun v : V =>
      (s ^ Module.finrank ℝ V * gaussDens p (s • v - μ)) * gaussDens r (a - α • v) := by
  refine MeasureTheory.Integrable.of_integral_ne_zero ?_
  rw [integral_node hp hr hs]
  refine (gaussDens_pos ?_ _).ne'
  have : 0 < p + (α / s) ^ 2 * r := by positivity
  positivity

/-- Rescaling: `s^d g_p(s w) = g_{p s²}(w)`. -/
theorem gaussDens_scale {p s : ℝ} (hp : 0 < p) (hs : 0 < s) (w : V) :
    s ^ Module.finrank ℝ V * gaussDens p (s • w) = gaussDens (p * s ^ 2) w := by
  unfold gaussDens
  rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  have h1 : (p * s ^ 2 / (2 * π)) ^ ((Module.finrank ℝ V : ℝ) / 2) =
      (s ^ 2) ^ ((Module.finrank ℝ V : ℝ) / 2) * (p / (2 * π)) ^ ((Module.finrank ℝ V : ℝ) / 2) := by
    rw [← Real.mul_rpow (by positivity) (by positivity)]; congr 1; ring
  have h2 : (s ^ 2) ^ ((Module.finrank ℝ V : ℝ) / 2) = s ^ Module.finrank ℝ V := by
    rw [← Real.rpow_natCast s 2, ← Real.rpow_mul hs.le]
    rw [show (2 : ℕ) * ((Module.finrank ℝ V : ℝ) / 2) = (Module.finrank ℝ V : ℝ) by push_cast; ring,
      Real.rpow_natCast]
  rw [h1, h2]
  have : -(p / 2) * (s ^ 2 * ‖w‖ ^ 2) = -(p * s ^ 2 / 2) * ‖w‖ ^ 2 := by ring
  rw [this]; ring

end Gauss

/-! ### Gaussian trees -/

section Tree

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

/-- The data of a Gaussian tree on the nodes `0, 1, …, n` (node `0` the root; node `i > 0` has parent
`par i < i`): node `i` carries the factor `s_i^d g_{p_i}(s_i ψ_i - μ_i - ∑_{c : par c = i} α_c ψ_c)`,
a probability density in `ψ_i`. -/
structure GaussTree (V : Type*) where
  /-- parent -/
  par : ℕ → ℕ
  /-- scale `s_i` of the node variable -/
  s : ℕ → ℝ
  /-- precision `p_i` -/
  p : ℕ → ℝ
  /-- constant `μ_i` (the contribution of the fixed children) -/
  μ : ℕ → V
  /-- the coefficient of `ψ_i` in the factor of its parent -/
  α : ℕ → ℝ

namespace GaussTree

variable (T : GaussTree V)

/-- The argument of the Gaussian factor of node `i` (children among the nodes `0, …, n`). -/
def arg (n : ℕ) (ψ : ℕ → V) (i : ℕ) : V :=
  T.s i • ψ i - T.μ i - ∑ c ∈ Finset.range (n + 1), if c ≠ 0 ∧ T.par c = i then T.α c • ψ c else 0

/-- The factor of node `i`. -/
noncomputable def factor (n : ℕ) (ψ : ℕ → V) (i : ℕ) : ℝ :=
  T.s i ^ Module.finrank ℝ V * gaussDens (T.p i) (T.arg n ψ i)

/-- The product of all the node factors. -/
noncomputable def Psi (n : ℕ) (ψ : ℕ → V) : ℝ := ∏ i ∈ Finset.range (n + 1), T.factor n ψ i

/-- The product of the coefficients along the path from the root to `i`. -/
noncomputable def pathCoef (par : ℕ → ℕ) (b : ℕ → ℝ) : ℕ → ℝ
  | i => if i = 0 then 1 else if par i < i then b i * pathCoef par b (par i) else 0
  decreasing_by assumption

theorem pathCoef_zero (par : ℕ → ℕ) (b : ℕ → ℝ) : pathCoef par b 0 = 1 := by
  rw [pathCoef]; simp

theorem pathCoef_pos_index (par : ℕ → ℕ) (b : ℕ → ℝ) {i : ℕ} (hi : i ≠ 0) (hp : par i < i) :
    pathCoef par b i = b i * pathCoef par b (par i) := by
  rw [pathCoef]; simp [hi, hp]

/-- `A_i = ∏ (α_c / s_c)` over the path. -/
noncomputable def A : ℕ → ℝ := pathCoef T.par fun i => T.α i / T.s i

/-- The total variance of the root: `∑ A_i² / p_i`. -/
noncomputable def var (n : ℕ) : ℝ := ∑ i ∈ Finset.range (n + 1), T.A i ^ 2 / T.p i

/-- The total mean of the root: `∑ A_i μ_i`. -/
noncomputable def mean (n : ℕ) : V := ∑ i ∈ Finset.range (n + 1), T.A i • T.μ i

end GaussTree

/-- Root value `u`, then the integrated variables `x`, as a function on `ℕ`. -/
def extVec (u : V) {n : ℕ} (x : Fin n → V) : ℕ → V := fun i =>
  if i = 0 then u else if h : i - 1 < n then x ⟨i - 1, h⟩ else 0

theorem extVec_snoc (u : V) {n : ℕ} (x : Fin n → V) (v : V) :
    extVec u (Fin.snoc x v : Fin (n + 1) → V) = Function.update (extVec u x) (n + 1) v := by
  funext i
  by_cases h0 : i = 0
  · subst h0; simp [extVec]
  by_cases h1 : i = n + 1
  · subst h1; simp [extVec]; exact Fin.snoc_last _ _
  · rw [Function.update_of_ne h1]
    simp only [extVec, h0, ite_false]
    by_cases h2 : i - 1 < n
    · have h3 : i - 1 < n + 1 := by omega
      simp only [h2, h3, dite_true]
      have : (⟨i - 1, h3⟩ : Fin (n + 1)) = Fin.castSucc ⟨i - 1, h2⟩ := rfl
      rw [this, Fin.snoc_castSucc]
    · have h3 : ¬ i - 1 < n + 1 := by omega
      simp [h2, h3]

namespace GaussTree

variable (T : GaussTree V)

/-- Eliminating the node `m` into its parent `q = par m`: the parent precision and constant change. -/
noncomputable def elim (m : ℕ) : GaussTree V :=
  { T with
    p := Function.update T.p (T.par m)
      (T.p m * T.p (T.par m) / (T.p m + (T.α m / T.s m) ^ 2 * T.p (T.par m)))
    μ := Function.update T.μ (T.par m) (T.μ (T.par m) + (T.α m / T.s m) • T.μ m) }

theorem arg_succ_update (n : ℕ) (ψ' : ℕ → V) (v : V) {i : ℕ} (hi : i < n + 1) :
    T.arg (n + 1) (Function.update ψ' (n + 1) v) i =
      T.arg n ψ' i - (if T.par (n + 1) = i then T.α (n + 1) • v else 0) := by
  have hne : i ≠ n + 1 := by omega
  unfold arg
  rw [Finset.sum_range_succ, Function.update_of_ne hne]
  have : ∑ c ∈ Finset.range (n + 1),
      (if c ≠ 0 ∧ T.par c = i then T.α c • Function.update ψ' (n + 1) v c else 0) =
      ∑ c ∈ Finset.range (n + 1), (if c ≠ 0 ∧ T.par c = i then T.α c • ψ' c else 0) := by
    refine Finset.sum_congr rfl fun c hc => ?_
    have : c ≠ n + 1 := by have := Finset.mem_range.mp hc; omega
    rw [Function.update_of_ne this]
  rw [this]
  by_cases h : T.par (n + 1) = i
  · simp [h]; abel
  · simp [h]

theorem arg_last_update (n : ℕ) (hpar : ∀ c ≤ n + 1, c ≠ 0 → T.par c < c) (ψ' : ℕ → V) (v : V) :
    T.arg (n + 1) (Function.update ψ' (n + 1) v) (n + 1) = T.s (n + 1) • v - T.μ (n + 1) := by
  unfold arg
  rw [Function.update_self]
  have : ∑ c ∈ Finset.range (n + 1 + 1),
      (if c ≠ 0 ∧ T.par c = n + 1 then T.α c • Function.update ψ' (n + 1) v c else 0) = 0 := by
    refine Finset.sum_eq_zero fun c hc => ?_
    have hc' := Finset.mem_range.mp hc
    have hc0 : ¬ (c ≠ 0 ∧ T.par c = n + 1) := by
      rintro ⟨h0, h1⟩
      have := hpar c (by omega) h0
      omega
    simp [hc0]
  rw [this, sub_zero]

theorem arg_elim (m : ℕ) (n : ℕ) (ψ : ℕ → V) (i : ℕ) :
    (T.elim m).arg n ψ i =
      T.arg n ψ i - (if i = T.par m then (T.α m / T.s m) • T.μ m else 0) := by
  unfold arg elim
  by_cases h : i = T.par m
  · subst h; simp only [Function.update_self, ite_true]; abel
  · simp [h]

theorem factor_elim_ne (m n : ℕ) (ψ : ℕ → V) {i : ℕ} (h : i ≠ T.par m) :
    (T.elim m).factor n ψ i = T.factor n ψ i := by
  unfold factor
  rw [arg_elim]
  simp [h, elim]

theorem factor_elim_eq (m n : ℕ) (ψ : ℕ → V) :
    (T.elim m).factor n ψ (T.par m) =
      T.s (T.par m) ^ Module.finrank ℝ V * gaussDens
        (T.p m * T.p (T.par m) / (T.p m + (T.α m / T.s m) ^ 2 * T.p (T.par m)))
        (T.arg n ψ (T.par m) - (T.α m / T.s m) • T.μ m) := by
  unfold factor
  rw [arg_elim]
  simp [elim]

theorem Psi_succ_update (n : ℕ) (hpar : ∀ c ≤ n + 1, c ≠ 0 → T.par c < c) (ψ' : ℕ → V) (v : V) :
    T.Psi (n + 1) (Function.update ψ' (n + 1) v) =
      (T.s (n + 1) ^ Module.finrank ℝ V * gaussDens (T.p (n + 1)) (T.s (n + 1) • v - T.μ (n + 1))) *
        (∏ i ∈ (Finset.range (n + 1)).erase (T.par (n + 1)), T.factor n ψ' i) *
        (T.s (T.par (n + 1)) ^ Module.finrank ℝ V *
          gaussDens (T.p (T.par (n + 1))) (T.arg n ψ' (T.par (n + 1)) - T.α (n + 1) • v)) := by
  have hq : T.par (n + 1) < n + 1 := hpar (n + 1) le_rfl (by omega)
  have hqmem : T.par (n + 1) ∈ Finset.range (n + 1) := Finset.mem_range.mpr hq
  unfold Psi
  rw [Finset.prod_range_succ, ← Finset.mul_prod_erase _ _ hqmem]
  have hlast : T.factor (n + 1) (Function.update ψ' (n + 1) v) (n + 1) =
      T.s (n + 1) ^ Module.finrank ℝ V * gaussDens (T.p (n + 1)) (T.s (n + 1) • v - T.μ (n + 1)) := by
    unfold factor; rw [arg_last_update T n hpar]
  have hq' : T.factor (n + 1) (Function.update ψ' (n + 1) v) (T.par (n + 1)) =
      T.s (T.par (n + 1)) ^ Module.finrank ℝ V *
        gaussDens (T.p (T.par (n + 1))) (T.arg n ψ' (T.par (n + 1)) - T.α (n + 1) • v) := by
    unfold factor; rw [arg_succ_update T n ψ' v hq]; simp
  have hrest : ∏ i ∈ (Finset.range (n + 1)).erase (T.par (n + 1)),
      T.factor (n + 1) (Function.update ψ' (n + 1) v) i =
      ∏ i ∈ (Finset.range (n + 1)).erase (T.par (n + 1)), T.factor n ψ' i := by
    refine Finset.prod_congr rfl fun i hi => ?_
    have hi' := Finset.mem_erase.mp hi
    have hi2 := Finset.mem_range.mp hi'.2
    unfold factor
    rw [arg_succ_update T n ψ' v hi2]
    simp [hi'.1.symm]
  rw [hlast, hq', hrest]; ring

theorem Psi_elim (n : ℕ) (hq : T.par (n + 1) < n + 1) (ψ' : ℕ → V) :
    (T.elim (n + 1)).Psi n ψ' =
      (∏ i ∈ (Finset.range (n + 1)).erase (T.par (n + 1)), T.factor n ψ' i) *
        (T.s (T.par (n + 1)) ^ Module.finrank ℝ V * gaussDens
          (T.p (n + 1) * T.p (T.par (n + 1)) /
            (T.p (n + 1) + (T.α (n + 1) / T.s (n + 1)) ^ 2 * T.p (T.par (n + 1))))
          (T.arg n ψ' (T.par (n + 1)) - (T.α (n + 1) / T.s (n + 1)) • T.μ (n + 1))) := by
  have hqmem : T.par (n + 1) ∈ Finset.range (n + 1) := Finset.mem_range.mpr hq
  unfold Psi
  rw [← Finset.mul_prod_erase _ _ hqmem, factor_elim_eq, mul_comm]
  congr 1
  exact Finset.prod_congr rfl fun i hi => factor_elim_ne T _ _ _ (Finset.mem_erase.mp hi).1

theorem integral_Psi_step (n : ℕ) (hpar : ∀ c ≤ n + 1, c ≠ 0 → T.par c < c)
    (hs : ∀ i ≤ n + 1, 0 < T.s i) (hp : ∀ i ≤ n + 1, 0 < T.p i) (ψ' : ℕ → V) :
    MeasureTheory.Integrable (fun v : V => T.Psi (n + 1) (Function.update ψ' (n + 1) v)) ∧
      ∫ v : V, T.Psi (n + 1) (Function.update ψ' (n + 1) v) = (T.elim (n + 1)).Psi n ψ' := by
  have hq : T.par (n + 1) < n + 1 := hpar (n + 1) le_rfl (by omega)
  have hm : 0 < T.p (n + 1) := hp _ le_rfl
  have hqp : 0 < T.p (T.par (n + 1)) := hp _ (by omega)
  have hsm : 0 < T.s (n + 1) := hs _ le_rfl
  have hsq : 0 < T.s (T.par (n + 1)) := hs _ (by omega)
  set R := ∏ i ∈ (Finset.range (n + 1)).erase (T.par (n + 1)), T.factor n ψ' i with hR
  set a := T.arg n ψ' (T.par (n + 1)) with ha
  have hform : ∀ v : V, T.Psi (n + 1) (Function.update ψ' (n + 1) v) =
      (R * T.s (T.par (n + 1)) ^ Module.finrank ℝ V) *
        ((T.s (n + 1) ^ Module.finrank ℝ V * gaussDens (T.p (n + 1)) (T.s (n + 1) • v - T.μ (n + 1))) *
          gaussDens (T.p (T.par (n + 1))) (a - T.α (n + 1) • v)) := by
    intro v; rw [Psi_succ_update T n hpar]; ring
  simp_rw [hform]
  refine ⟨(integrable_node hm hqp hsm _ _).const_mul _, ?_⟩
  rw [MeasureTheory.integral_const_mul, integral_node hm hqp hsm, Psi_elim T n hq]
  ring

theorem A_succ (n : ℕ) (hpar : ∀ c ≤ n + 1, c ≠ 0 → T.par c < c) :
    T.A (n + 1) = T.α (n + 1) / T.s (n + 1) * T.A (T.par (n + 1)) :=
  pathCoef_pos_index _ _ (by omega) (hpar _ le_rfl (by omega))

theorem A_elim (m : ℕ) : (T.elim m).A = T.A := rfl

theorem var_elim (n : ℕ) (hpar : ∀ c ≤ n + 1, c ≠ 0 → T.par c < c)
    (_hs : ∀ i ≤ n + 1, 0 < T.s i) (hp : ∀ i ≤ n + 1, 0 < T.p i) :
    (T.elim (n + 1)).var n = T.var (n + 1) := by
  have hq : T.par (n + 1) < n + 1 := hpar (n + 1) le_rfl (by omega)
  have hqmem : T.par (n + 1) ∈ Finset.range (n + 1) := Finset.mem_range.mpr hq
  have hm : 0 < T.p (n + 1) := hp _ le_rfl
  have hqp : 0 < T.p (T.par (n + 1)) := hp _ (by omega)
  unfold var
  rw [Finset.sum_range_succ _ (n + 1), A_succ T n hpar, A_elim]
  have : ∀ i ∈ Finset.range (n + 1), T.A i ^ 2 / (T.elim (n + 1)).p i =
      T.A i ^ 2 / T.p i + (if i = T.par (n + 1) then
        (T.α (n + 1) / T.s (n + 1) * T.A (T.par (n + 1))) ^ 2 / T.p (n + 1) else 0) := by
    intro i hi
    by_cases h : i = T.par (n + 1)
    · subst h
      simp only [elim, Function.update_self, ↓reduceIte]
      field_simp
    · simp [elim, h]
  rw [Finset.sum_congr rfl this, Finset.sum_add_distrib, Finset.sum_ite_eq' _ _]
  simp only [hqmem, ite_true]

theorem mean_elim (n : ℕ) (hpar : ∀ c ≤ n + 1, c ≠ 0 → T.par c < c) :
    (T.elim (n + 1)).mean n = T.mean (n + 1) := by
  have hq : T.par (n + 1) < n + 1 := hpar (n + 1) le_rfl (by omega)
  have hqmem : T.par (n + 1) ∈ Finset.range (n + 1) := Finset.mem_range.mpr hq
  unfold mean
  rw [Finset.sum_range_succ _ (n + 1), A_succ T n hpar, A_elim]
  have : ∀ i ∈ Finset.range (n + 1), T.A i • (T.elim (n + 1)).μ i =
      T.A i • T.μ i + (if i = T.par (n + 1) then
        (T.α (n + 1) / T.s (n + 1) * T.A (T.par (n + 1))) • T.μ (n + 1) else 0) := by
    intro i hi
    by_cases h : i = T.par (n + 1)
    · subst h
      simp only [elim, Function.update_self, smul_add, smul_smul, ↓reduceIte]
      rw [mul_comm]
    · simp [elim, h]
  rw [Finset.sum_congr rfl this, Finset.sum_add_distrib]
  simp [Finset.sum_ite_eq', hqmem]

theorem Psi_nonneg (n : ℕ) (hs : ∀ i ≤ n, 0 < T.s i) (hp : ∀ i ≤ n, 0 < T.p i) (ψ : ℕ → V) :
    0 ≤ T.Psi n ψ := by
  unfold Psi factor
  refine Finset.prod_nonneg fun i hi => ?_
  have hi' := Finset.mem_range.mp hi
  have h1 := hs i (by omega)
  have := gaussDens_pos (V := V) (hp i (by omega)) (T.arg n ψ i)
  positivity

theorem continuous_gaussDens (p : ℝ) : Continuous (gaussDens (V := V) p) := by
  unfold gaussDens; fun_prop

theorem continuous_Psi (n : ℕ) : Continuous (T.Psi n) := by
  unfold Psi factor arg
  refine continuous_finsetProd _ fun i _ => ?_
  refine continuous_const.mul ((continuous_gaussDens _).comp ?_)
  refine (((continuous_const.smul (continuous_apply i)).sub continuous_const).sub ?_)
  refine continuous_finsetSum _ fun c _ => ?_
  split_ifs
  · exact continuous_const.smul (continuous_apply c)
  · exact continuous_const

theorem continuous_extVec (u : V) (n : ℕ) : Continuous (fun x : Fin n → V => extVec u x) := by
  refine continuous_pi fun i => ?_
  unfold extVec
  by_cases h0 : i = 0
  · simp [h0]; exact continuous_const
  · simp only [h0, ite_false]
    by_cases h : i - 1 < n
    · simp only [h, dite_true]; exact continuous_apply _
    · simp only [h, dite_false]; exact continuous_const

theorem main_aux (n : ℕ) : ∀ (T : GaussTree V) (u : V), (∀ i ≤ n, 0 < T.s i) → (∀ i ≤ n, 0 < T.p i) →
    (∀ c ≤ n, c ≠ 0 → T.par c < c) →
    MeasureTheory.Integrable (fun x : Fin n → V => T.Psi n (extVec u x)) ∧
      ∫ x : Fin n → V, T.Psi n (extVec u x) =
        T.s 0 ^ Module.finrank ℝ V * gaussDens (T.var n)⁻¹ (T.s 0 • u - T.mean n) := by
  induction n with
  | zero =>
    intro T u hs hp hpar
    have h0 : ∀ x : Fin 0 → V, T.Psi 0 (extVec u x) =
        T.s 0 ^ Module.finrank ℝ V * gaussDens (T.var 0)⁻¹ (T.s 0 • u - T.mean 0) := by
      intro x
      have hA : T.A 0 = 1 := pathCoef_zero _ _
      simp [Psi, factor, arg, var, mean, hA, extVec]
    simp_rw [h0]
    refine ⟨MeasureTheory.integrable_const _, ?_⟩
    simp [MeasureTheory.Measure.real, MeasureTheory.volume_pi]
  | succ n ih =>
    intro T u hs hp hpar
    have hT' : (∀ i ≤ n, 0 < (T.elim (n + 1)).s i) ∧ (∀ i ≤ n, 0 < (T.elim (n + 1)).p i) ∧
        (∀ c ≤ n, c ≠ 0 → (T.elim (n + 1)).par c < c) := by
      refine ⟨fun i hi => hs i (by omega), fun i hi => ?_, fun c hc hc0 => hpar c (by omega) hc0⟩
      have hm : 0 < T.p (n + 1) := hp _ le_rfl
      have hqp : 0 < T.p (T.par (n + 1)) := hp _ (by have := hpar (n + 1) le_rfl (by omega); omega)
      by_cases h : i = T.par (n + 1)
      · subst h
        simp only [elim, Function.update_self]
        positivity
      · simp only [elim, Function.update_of_ne h]
        exact hp i (by omega)
    obtain ⟨hI, hJ⟩ := ih (T.elim (n + 1)) u hT'.1 hT'.2.1 hT'.2.2
    have he := (MeasureTheory.volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => V)
      (Fin.last n)).symm
    set e := (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => V) (Fin.last n)).symm with he_def
    have hGe : ∀ (v : V) (x' : Fin n → V),
        T.Psi (n + 1) (extVec u (e (v, x'))) =
          T.Psi (n + 1) (Function.update (extVec u x') (n + 1) v) := by
      intro v x'
      have : e (v, x') = Fin.snoc x' v := by
        simp [he_def, MeasurableEquiv.piFinSuccAbove]; rfl
      rw [this, extVec_snoc]
    have hGc : Continuous (fun x : Fin (n + 1) → V => T.Psi (n + 1) (extVec u x)) :=
      (T.continuous_Psi _).comp (continuous_extVec u _)
    have hstep := fun x' : Fin n → V => integral_Psi_step T n hpar (fun i hi => hs i hi)
      (fun i hi => hp i hi) (extVec u x')
    have hFint : MeasureTheory.Integrable
        (fun z : V × (Fin n → V) => T.Psi (n + 1) (extVec u (e z))) := by
      rw [MeasureTheory.Measure.volume_eq_prod]
      refine (MeasureTheory.integrable_prod_iff' ?_).mpr ⟨?_, ?_⟩
      · exact (hGc.measurable.comp e.measurable).aestronglyMeasurable
      · exact Filter.Eventually.of_forall fun x' => by
          have := (hstep x').1; simpa only [hGe] using this
      · have : (fun x' : Fin n → V => ∫ v : V, ‖T.Psi (n + 1) (extVec u (e (v, x')))‖) =
            fun x' => (T.elim (n + 1)).Psi n (extVec u x') := by
          funext x'
          simp_rw [hGe]
          rw [← (hstep x').2]
          refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
          simp only [Real.norm_eq_abs]
          exact abs_of_nonneg (T.Psi_nonneg _ hs hp _)
        rw [this]; exact hI
    refine ⟨(he.integrable_comp_emb e.measurableEmbedding).mp hFint, ?_⟩
    rw [← he.integral_comp' (fun x : Fin (n + 1) → V => T.Psi (n + 1) (extVec u x))]
    rw [MeasureTheory.Measure.volume_eq_prod, MeasureTheory.integral_prod_symm _ hFint]
    simp_rw [hGe]
    simp_rw [(fun x' => (hstep x').2)]
    rw [hJ, var_elim T n hpar (fun i hi => hs i hi) (fun i hi => hp i hi), mean_elim T n hpar]
    rfl

theorem var_pos (n : ℕ) (hp : ∀ i ≤ n, 0 < T.p i) : 0 < T.var n := by
  unfold var
  have h0 : T.A 0 = 1 := pathCoef_zero _ _
  rw [Finset.sum_range_succ']
  have := hp 0 (Nat.zero_le _)
  have h1 : 0 ≤ ∑ i ∈ Finset.range n, T.A (i + 1) ^ 2 / T.p (i + 1) :=
    Finset.sum_nonneg fun i hi => div_nonneg (sq_nonneg _) (hp _ (by have := Finset.mem_range.mp hi; omega)).le
  rw [h0]
  have : 0 < (1 : ℝ) ^ 2 / T.p 0 := by positivity
  linarith

/-- The integrand `Ψ` of a Gaussian tree, with the root value `u`, is integrable in the other
node variables. -/
theorem integrable_Psi (n : ℕ) (u : V) (hs : ∀ i ≤ n, 0 < T.s i) (hp : ∀ i ≤ n, 0 < T.p i)
    (hpar : ∀ c ≤ n, c ≠ 0 → T.par c < c) :
    MeasureTheory.Integrable fun x : Fin n → V => T.Psi n (extVec u x) :=
  (main_aux n T u hs hp hpar).1

/-- **Integration of a Gaussian tree** (arbitrary positive scales `s_i` and precisions `p_i`): integrating
all node variables but the root gives the Gaussian density of the root. -/
theorem integral_Psi (n : ℕ) (u : V) (hs : ∀ i ≤ n, 0 < T.s i) (hp : ∀ i ≤ n, 0 < T.p i)
    (hpar : ∀ c ≤ n, c ≠ 0 → T.par c < c) :
    ∫ x : Fin n → V, T.Psi n (extVec u x) =
      T.s 0 ^ Module.finrank ℝ V * gaussDens (T.var n)⁻¹ (T.s 0 • u - T.mean n) :=
  (main_aux n T u hs hp hpar).2

end GaussTree

end Tree
end Balaban.LargeField
