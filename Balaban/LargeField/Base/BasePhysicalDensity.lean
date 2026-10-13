module

public import Balaban.Frozen.Model.PartitionFunction
public import Balaban.Lattice.Blocks
public import Balaban.LargeField.Operators.Quiet
public import Balaban.LargeField.Operators.ShellVolume
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FunProp

/-!
# The first renormalization step: the frozen partition function as an integral of the level-one density

For the fine torus `Λ₀ = Torus d (L n)` and the coarse torus `Λ₁ = Torus d n`, the block average
of a spin configuration is `(Qφ)(y) = L^{-d} ∑_{x ∈ block y} φ_x`, the block-averaging kernel is
`∏_y t(ϑ_y, (Qφ)(y))` with the Gaussian `t = gaussT` of constant `β a L^d / L^2`, and the
level-one density is
`ρ₁(ψ; g) = z₁^D ∫ K(z₁ ψ, φ) exp(-β H(φ) + ⟨g, φ⟩) dσ(φ)`, `D = N |Λ₁|`.

* `baseQ`, `baseKernel`, `baseRho1`: the three definitions;
* `basePhysicalDensity`: `Z(g) = ∫ ρ₁(ψ; g) dψ` (the frozen `partitionFunction` on the left);
* `basePhysicalDensity_one`: the case `z₁ = 1`;
* `baseRho1_integrable`: `ρ₁(·; g)` is integrable.

The proof is Gaussian normalization of each block factor, Fubini, and the change of variables
`ϑ = z₁ ψ`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open MeasureTheory Balaban

/-- The block average `(Qφ)(y) = L^{-d} ∑_{x ∈ block y} φ_x`. -/
noncomputable def baseQ (d N L n : ℕ) [NeZero L] [NeZero n]
    (φ : Torus d (L * n) → Metric.sphere (0 : EuclideanSpace ℝ (Fin N)) 1) (y : Torus d n) :
    EuclideanSpace ℝ (Fin N) :=
  ((L : ℝ) ^ d)⁻¹ • ∑ x ∈ blockFibre (ℓ := L * n) L n y, (φ x : EuclideanSpace ℝ (Fin N))

/-- The block-averaging kernel `∏_y t(θ_y, (Qφ)(y))` with `t = gaussT` of constant
`β a L^d / L^2`. -/
noncomputable def baseKernel (d N L n : ℕ) [NeZero L] [NeZero n] (β a : ℝ)
    (θ : Torus d n → EuclideanSpace ℝ (Fin N))
    (φ : Torus d (L * n) → Metric.sphere (0 : EuclideanSpace ℝ (Fin N)) 1) : ℝ :=
  ∏ y : Torus d n, gaussT N (β * a * (L : ℝ) ^ d / (L : ℝ) ^ 2) (θ y) (baseQ d N L n φ y)

/-- The level-one density
`ρ₁(ψ; g) = z₁^D ∫ K(z₁ ψ, φ) exp(-β H(φ) + ∑ g φ) dσ(φ)`, `D = N |Λ₁|`. -/
noncomputable def baseRho1 (d N L n : ℕ) [NeZero L] [NeZero n] (β a z₁ ν : ℝ)
    (h : EuclideanSpace ℝ (Fin N)) (ψ : Torus d n → EuclideanSpace ℝ (Fin N))
    (g : Torus d (L * n) → Fin N → ℂ) : ℂ :=
  ((z₁ ^ (N * Fintype.card (Torus d n)) : ℝ) : ℂ) *
    ∫ φ, ((baseKernel d N L n β a (z₁ • ψ) φ : ℝ) : ℂ) *
      Complex.exp (-((β * energy d N (L * n) ν h φ : ℝ) : ℂ)
        + ∑ x : Torus d (L * n), ∑ i : Fin N,
          g x i * (((φ x : EuclideanSpace ℝ (Fin N)) i : ℝ) : ℂ)) ∂aprioriMeasure d N (L * n)

section Lemmas

variable {d N L n : ℕ} [NeZero L] [NeZero n] [NeZero N]

private lemma continuous_gaussT (c : ℝ) :
    Continuous fun p : EuclideanSpace ℝ (Fin N) × EuclideanSpace ℝ (Fin N) => gaussT N c p.1 p.2 := by
  unfold gaussT
  fun_prop

private lemma gaussT_sub (c : ℝ) (u w : EuclideanSpace ℝ (Fin N)) :
    gaussT N c u w = gaussT N c (u - w) 0 := by
  unfold gaussT; simp

private lemma integrable_gaussT {c : ℝ} (hc : 0 < c) (w : EuclideanSpace ℝ (Fin N)) :
    Integrable (fun u : EuclideanSpace ℝ (Fin N) => gaussT N c u w) := by
  have h0 : Integrable (fun u : EuclideanSpace ℝ (Fin N) => gaussT N c u 0) := by
    refine ⟨(continuous_gaussT c).comp (continuous_id.prodMk continuous_const) |>.aestronglyMeasurable, ?_⟩
    unfold HasFiniteIntegral
    have : ∀ u : EuclideanSpace ℝ (Fin N), ‖gaussT N c u 0‖ₑ = ENNReal.ofReal (gaussT N c u 0) := by
      intro u; rw [Real.enorm_eq_ofReal (gaussT_nonneg N c hc.le u 0)]
    simp_rw [this]
    rw [lintegral_gaussT N hc]; exact ENNReal.one_lt_top
  have := h0.comp_sub_right w
  simpa [gaussT_sub c] using this

private lemma integral_gaussT {c : ℝ} (hc : 0 < c) (w : EuclideanSpace ℝ (Fin N)) :
    ∫ u : EuclideanSpace ℝ (Fin N), gaussT N c u w = 1 := by
  have h1 : ∫ u : EuclideanSpace ℝ (Fin N), gaussT N c u 0 = 1 := by
    rw [integral_eq_lintegral_of_nonneg_ae
      (Filter.Eventually.of_forall fun u => gaussT_nonneg N c hc.le u 0)
      ((continuous_gaussT c).comp (continuous_id.prodMk continuous_const)).aestronglyMeasurable,
      lintegral_gaussT N hc]
    simp
  simp_rw [gaussT_sub c _ w]
  rw [integral_sub_right_eq_self (fun u => gaussT N c u 0) w]
  exact h1


/-- The spin configurations. -/
abbrev CfgT (d N L n : ℕ) : Type :=
  Torus d (L * n) → Metric.sphere (0 : EuclideanSpace ℝ (Fin N)) 1

lemma baseKernel_pos {β a : ℝ} (hβ : 0 < β) (ha : 0 < a) :
    0 < β * a * (L : ℝ) ^ d / (L : ℝ) ^ 2 := by
  have : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  positivity

private lemma measurable_baseQ (y : Torus d n) :
    Measurable fun φ : CfgT d N L n => baseQ d N L n φ y := by
  unfold baseQ
  have hs : Measurable fun φ : CfgT d N L n =>
      ∑ x ∈ blockFibre (ℓ := L * n) L n y, (φ x : EuclideanSpace ℝ (Fin N)) :=
    Finset.measurable_sum _ fun x _ => measurable_subtype_coe.comp (measurable_pi_apply x)
  exact Measurable.const_smul hs ((L : ℝ) ^ d)⁻¹

lemma measurable_baseKernel (β a z : ℝ) :
    Measurable fun p : (Torus d n → EuclideanSpace ℝ (Fin N)) × CfgT d N L n =>
      baseKernel d N L n β a (z • p.1) p.2 := by
  have hy : ∀ y : Torus d n, Measurable fun p : (Torus d n → EuclideanSpace ℝ (Fin N)) × CfgT d N L n =>
      gaussT N (β * a * (L : ℝ) ^ d / (L : ℝ) ^ 2) (z • p.1 y) (baseQ d N L n p.2 y) := by
    intro y
    have h1 : Measurable fun p : (Torus d n → EuclideanSpace ℝ (Fin N)) × CfgT d N L n =>
        p.1 y := (measurable_pi_apply y).comp measurable_fst
    have h2 : Measurable fun p : (Torus d n → EuclideanSpace ℝ (Fin N)) × CfgT d N L n =>
        z • p.1 y := h1.const_smul z
    have h3 : Measurable fun p : (Torus d n → EuclideanSpace ℝ (Fin N)) × CfgT d N L n =>
        baseQ d N L n p.2 y := (measurable_baseQ y).comp measurable_snd
    unfold gaussT
    exact measurable_const.mul (Real.measurable_exp.comp (measurable_const.mul
      ((measurable_norm.comp (h2.sub h3)).pow_const 2)))
  unfold baseKernel
  exact Finset.measurable_prod _ fun y _ => hy y

lemma baseKernel_nonneg {β a : ℝ} (hβ : 0 < β) (ha : 0 < a)
    (θ : Torus d n → EuclideanSpace ℝ (Fin N)) (φ : CfgT d N L n) :
    0 ≤ baseKernel d N L n β a θ φ :=
  Finset.prod_nonneg fun _ _ => gaussT_nonneg N _ (baseKernel_pos hβ ha).le _ _

private lemma baseKernel_integrable {β a : ℝ} (hβ : 0 < β) (ha : 0 < a) (φ : CfgT d N L n) :
    Integrable (fun θ : Torus d n → EuclideanSpace ℝ (Fin N) => baseKernel d N L n β a θ φ)
      (Measure.pi fun _ => volume) := by
  unfold baseKernel
  exact Integrable.fintype_prod (f := fun y u => gaussT N _ u (baseQ d N L n φ y))
    fun y => integrable_gaussT (baseKernel_pos hβ ha) _

private lemma baseKernel_integral {β a : ℝ} (hβ : 0 < β) (ha : 0 < a) (φ : CfgT d N L n) :
    ∫ θ : Torus d n → EuclideanSpace ℝ (Fin N), baseKernel d N L n β a θ φ
      ∂(Measure.pi fun _ => volume) = 1 := by
  unfold baseKernel
  rw [integral_fintype_prod_eq_prod (f := fun y u => gaussT N _ u (baseQ d N L n φ y))]
  exact Finset.prod_eq_one fun y _ => integral_gaussT (baseKernel_pos hβ ha) _

private lemma finrank_coarse :
    Module.finrank ℝ (Torus d n → EuclideanSpace ℝ (Fin N)) = N * Fintype.card (Torus d n) := by
  simp [Module.finrank_pi_fintype, mul_comm]

private lemma baseKernel_smul_integrable {β a z : ℝ} (hβ : 0 < β) (ha : 0 < a) (hz : 0 < z)
    (φ : CfgT d N L n) :
    Integrable (fun ψ : Torus d n → EuclideanSpace ℝ (Fin N) => baseKernel d N L n β a (z • ψ) φ)
      (Measure.pi fun _ => volume) :=
  (baseKernel_integrable hβ ha φ).comp_smul hz.ne'

private lemma baseKernel_smul_integral {β a z : ℝ} (hβ : 0 < β) (ha : 0 < a) (hz : 0 < z)
    (φ : CfgT d N L n) :
    z ^ (N * Fintype.card (Torus d n)) *
      ∫ ψ : Torus d n → EuclideanSpace ℝ (Fin N), baseKernel d N L n β a (z • ψ) φ
        ∂(Measure.pi fun _ => volume) = 1 := by
  rw [Measure.integral_comp_smul (μ := (Measure.pi fun _ : Torus d n =>
    (volume : Measure (EuclideanSpace ℝ (Fin N))))) (fun θ => baseKernel d N L n β a θ φ) z,
    baseKernel_integral hβ ha φ, finrank_coarse]
  have : 0 < z ^ (N * Fintype.card (Torus d n)) := by positivity
  rw [abs_of_pos (by positivity)]
  rw [smul_eq_mul, mul_one]
  exact mul_inv_cancel₀ this.ne'

/-- Fubini for the product of the kernel and a bounded measurable function of the spins. -/
private lemma fubini_core {β a z : ℝ} (hβ : 0 < β) (ha : 0 < a) (hz : 0 < z)
    (F : CfgT d N L n → ℂ) (hF : Measurable F) (C : ℝ) (hC : ∀ φ, ‖F φ‖ ≤ C) :
    Integrable (fun p : (Torus d n → EuclideanSpace ℝ (Fin N)) × CfgT d N L n =>
      ((z ^ (N * Fintype.card (Torus d n)) : ℝ) : ℂ) *
        ((baseKernel d N L n β a (z • p.1) p.2 : ℝ) : ℂ) * F p.2)
      ((Measure.pi fun _ => volume).prod (aprioriMeasure d N (L * n))) := by
  have hmeas : Measurable fun p : (Torus d n → EuclideanSpace ℝ (Fin N)) × CfgT d N L n =>
      ((z ^ (N * Fintype.card (Torus d n)) : ℝ) : ℂ) *
        ((baseKernel d N L n β a (z • p.1) p.2 : ℝ) : ℂ) * F p.2 :=
    (measurable_const.mul (Complex.measurable_ofReal.comp (measurable_baseKernel β a z))).mul
      (hF.comp measurable_snd)
  rw [integrable_prod_iff' hmeas.aestronglyMeasurable]
  have hnorm : ∀ φ : CfgT d N L n,
      ∫ ψ : Torus d n → EuclideanSpace ℝ (Fin N), ‖((z ^ (N * Fintype.card (Torus d n)) : ℝ) : ℂ) *
        ((baseKernel d N L n β a (z • ψ) φ : ℝ) : ℂ) * F φ‖ ∂(Measure.pi fun _ => volume)
        = ‖F φ‖ := by
    intro φ
    have hpt : ∀ ψ : Torus d n → EuclideanSpace ℝ (Fin N),
        ‖((z ^ (N * Fintype.card (Torus d n)) : ℝ) : ℂ) *
          ((baseKernel d N L n β a (z • ψ) φ : ℝ) : ℂ) * F φ‖ =
        (z ^ (N * Fintype.card (Torus d n)) * baseKernel d N L n β a (z • ψ) φ) * ‖F φ‖ := by
      intro ψ
      rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg (by positivity),
        Real.norm_of_nonneg (baseKernel_nonneg hβ ha _ _)]
    simp_rw [hpt]
    rw [integral_mul_const, integral_const_mul, baseKernel_smul_integral hβ ha hz, one_mul]
  refine ⟨Filter.Eventually.of_forall fun φ => ?_, ?_⟩
  · exact (((baseKernel_smul_integrable hβ ha hz φ).ofReal.const_mul _).mul_const (F φ))
  · simp_rw [hnorm]
    exact Integrable.of_bound (hF.norm.aestronglyMeasurable) C
      (Filter.Eventually.of_forall fun φ => by simpa using hC φ)

end Lemmas

section Main

variable {d N L n : ℕ} [NeZero L] [NeZero n] [NeZero N]

lemma spin_integrand_bound (β ν : ℝ) (h : EuclideanSpace ℝ (Fin N))
    (g : Torus d (L * n) → Fin N → ℂ) :
    Measurable (fun φ : CfgT d N L n => Complex.exp (-((β * energy d N (L * n) ν h φ : ℝ) : ℂ)
        + ∑ x : Torus d (L * n), ∑ i : Fin N,
          g x i * (((φ x : EuclideanSpace ℝ (Fin N)) i : ℝ) : ℂ))) ∧
    ∃ C : ℝ, ∀ φ : CfgT d N L n, ‖Complex.exp (-((β * energy d N (L * n) ν h φ : ℝ) : ℂ)
        + ∑ x : Torus d (L * n), ∑ i : Fin N,
          g x i * (((φ x : EuclideanSpace ℝ (Fin N)) i : ℝ) : ℂ))‖ ≤ C := by
  have hcont : Continuous (fun φ : CfgT d N L n => Complex.exp (-((β * energy d N (L * n) ν h φ : ℝ) : ℂ)
        + ∑ x : Torus d (L * n), ∑ i : Fin N,
          g x i * (((φ x : EuclideanSpace ℝ (Fin N)) i : ℝ) : ℂ))) := by
    unfold energy
    fun_prop
  refine ⟨hcont.measurable, ?_⟩
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hcont.continuousOn
  exact ⟨C, fun φ => hC φ (Set.mem_univ φ)⟩

/-- The level-one density is integrable. -/
theorem baseRho1_integrable {β a z₁ ν : ℝ} (hβ : 0 < β) (ha : 0 < a) (hz : 0 < z₁)
    (h : EuclideanSpace ℝ (Fin N)) (g : Torus d (L * n) → Fin N → ℂ) :
    Integrable (fun ψ : Torus d n → EuclideanSpace ℝ (Fin N) => baseRho1 d N L n β a z₁ ν h ψ g)
      (Measure.pi fun _ => volume) := by
  obtain ⟨hm, C, hC⟩ := spin_integrand_bound (L := L) (n := n) β ν h g
  have hf := fubini_core (z := z₁) hβ ha hz _ hm C hC
  have := hf.integral_prod_left
  refine this.congr (Filter.Eventually.of_forall fun ψ => ?_)
  simp only [baseRho1]
  rw [← integral_const_mul]
  simp_rw [mul_assoc]

/-- **The first renormalization step, exact starting identity.** The frozen partition function with
source equals the integral over the coarse variables of the level-one density. -/
theorem basePhysicalDensity {β a z₁ ν : ℝ} (hβ : 0 < β) (ha : 0 < a) (hz : 0 < z₁)
    (h : EuclideanSpace ℝ (Fin N)) (g : Torus d (L * n) → Fin N → ℂ) :
    partitionFunction d N (L * n) β ν h g =
      ∫ ψ : Torus d n → EuclideanSpace ℝ (Fin N), baseRho1 d N L n β a z₁ ν h ψ g
        ∂(Measure.pi fun _ => volume) := by
  obtain ⟨hm, C, hC⟩ := spin_integrand_bound (L := L) (n := n) β ν h g
  have hf := fubini_core (z := z₁) hβ ha hz _ hm C hC
  have hrho : ∀ ψ : Torus d n → EuclideanSpace ℝ (Fin N), baseRho1 d N L n β a z₁ ν h ψ g =
      ∫ φ, ((z₁ ^ (N * Fintype.card (Torus d n)) : ℝ) : ℂ) *
        ((baseKernel d N L n β a (z₁ • ψ) φ : ℝ) : ℂ) *
        Complex.exp (-((β * energy d N (L * n) ν h φ : ℝ) : ℂ)
          + ∑ x : Torus d (L * n), ∑ i : Fin N,
            g x i * (((φ x : EuclideanSpace ℝ (Fin N)) i : ℝ) : ℂ)) ∂aprioriMeasure d N (L * n) := by
    intro ψ
    simp only [baseRho1]
    rw [← integral_const_mul]
    simp_rw [mul_assoc]
  simp_rw [hrho]
  rw [integral_integral_swap hf]
  unfold partitionFunction
  refine integral_congr_ae (Filter.Eventually.of_forall fun φ => ?_)
  simp only
  rw [integral_mul_const]
  have := baseKernel_smul_integral (z := z₁) hβ ha hz φ
  have hc : ∫ ψ : Torus d n → EuclideanSpace ℝ (Fin N),
      ((z₁ ^ (N * Fintype.card (Torus d n)) : ℝ) : ℂ) *
        ((baseKernel d N L n β a (z₁ • ψ) φ : ℝ) : ℂ) ∂(Measure.pi fun _ => volume) = 1 := by
    rw [integral_const_mul, integral_complex_ofReal, ← Complex.ofReal_mul, this]
    simp
  rw [hc, one_mul]

/-- The case `z₁ = 1`: `Z(g) = ∫ ρ̄₁(ϑ; g) dϑ`. -/
theorem basePhysicalDensity_one {β a ν : ℝ} (hβ : 0 < β) (ha : 0 < a)
    (h : EuclideanSpace ℝ (Fin N)) (g : Torus d (L * n) → Fin N → ℂ) :
    partitionFunction d N (L * n) β ν h g =
      ∫ ψ : Torus d n → EuclideanSpace ℝ (Fin N), baseRho1 d N L n β a 1 ν h ψ g
        ∂(Measure.pi fun _ => volume) :=
  basePhysicalDensity hβ ha one_pos h g

end Main

end Balaban.LargeField
