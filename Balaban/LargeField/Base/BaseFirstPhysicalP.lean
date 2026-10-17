module

public import Balaban.LargeField.Base.BaseFirstPartition
public import Balaban.LargeField.Base.BaseSectorSupport
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FunProp

/-!
# Exact physical first `P` partition

The first decomposition is applied to the literal test-free spin integrand in `baseRho1`.
All sphere spins, including those in failed cubes, remain present in each selected integral.
-/

@[expose] public section

namespace Balaban.LargeField

open Balaban MeasureTheory

/-- At fixed coarse field, every selected first `P` weight is Borel and lies in `[0,1]`. -/
theorem baseFirstPhysicalP_weight_measurable_unit
    {d N L n : ℕ} [NeZero L] [NeZero n]
    (regimeB : Prop) (ν δ₀ : ℝ) (h : EuclideanSpace ℝ (Fin N))
    (θ : Torus d n → EuclideanSpace ℝ (Fin N))
    (P : Finset (Torus d n)) :
    Measurable (fun φ : CfgT d N L n =>
      (∏ c ∈ P, (1 - chiPrimeZero (baseSectorN L n) L 1 1 regimeB ν δ₀
        (fun i => h i) c (baseSectorSpin φ, baseSectorTheta θ))) *
      ∏ c ∈ (Finset.univ : Finset (Torus d n)) \ P,
        chiPrimeZero (baseSectorN L n) L 1 1 regimeB ν δ₀
          (fun i => h i) c (baseSectorSpin φ, baseSectorTheta θ)) ∧
    (∀ φ : CfgT d N L n, 0 ≤
      (∏ c ∈ P, (1 - chiPrimeZero (baseSectorN L n) L 1 1 regimeB ν δ₀
        (fun i => h i) c (baseSectorSpin φ, baseSectorTheta θ))) *
      ∏ c ∈ (Finset.univ : Finset (Torus d n)) \ P,
        chiPrimeZero (baseSectorN L n) L 1 1 regimeB ν δ₀
          (fun i => h i) c (baseSectorSpin φ, baseSectorTheta θ)) ∧
    (∀ φ : CfgT d N L n,
      (∏ c ∈ P, (1 - chiPrimeZero (baseSectorN L n) L 1 1 regimeB ν δ₀
        (fun i => h i) c (baseSectorSpin φ, baseSectorTheta θ))) *
      ∏ c ∈ (Finset.univ : Finset (Torus d n)) \ P,
        chiPrimeZero (baseSectorN L n) L 1 1 regimeB ν δ₀
          (fun i => h i) c (baseSectorSpin φ, baseSectorTheta θ) ≤ 1) := by
  classical
  have hχ (c : Torus d n) (φ : CfgT d N L n) :
      0 ≤ chiPrimeZero (baseSectorN L n) L 1 1 regimeB ν δ₀
        (fun i => h i) c (baseSectorSpin φ, baseSectorTheta θ) ∧
      chiPrimeZero (baseSectorN L n) L 1 1 regimeB ν δ₀
        (fun i => h i) c (baseSectorSpin φ, baseSectorTheta θ) ≤ 1 := by
    rcases chiPrimeZero_eq_zero_or_one (baseSectorN L n) L 1 1 regimeB ν δ₀
      (fun i => h i) c (baseSectorSpin φ, baseSectorTheta θ) with hz | ho
    · exact ⟨hz ▸ le_refl (0 : ℝ), by rw [hz]; norm_num⟩
    · exact ⟨by rw [ho]; norm_num, ho ▸ le_refl (1 : ℝ)⟩
  have hleft (φ : CfgT d N L n) :
      0 ≤ ∏ c ∈ P, (1 - chiPrimeZero (baseSectorN L n) L 1 1 regimeB ν δ₀
        (fun i => h i) c (baseSectorSpin φ, baseSectorTheta θ)) ∧
      (∏ c ∈ P, (1 - chiPrimeZero (baseSectorN L n) L 1 1 regimeB ν δ₀
        (fun i => h i) c (baseSectorSpin φ, baseSectorTheta θ))) ≤ 1 := by
    constructor
    · exact Finset.prod_nonneg fun c _ => sub_nonneg.mpr (hχ c φ).2
    · exact Finset.prod_le_one₀ (fun c _ => sub_nonneg.mpr (hχ c φ).2)
        (fun c _ => sub_le_self 1 (hχ c φ).1)
  have hright (φ : CfgT d N L n) :
      0 ≤ ∏ c ∈ (Finset.univ : Finset (Torus d n)) \ P,
        chiPrimeZero (baseSectorN L n) L 1 1 regimeB ν δ₀
          (fun i => h i) c (baseSectorSpin φ, baseSectorTheta θ) ∧
      (∏ c ∈ (Finset.univ : Finset (Torus d n)) \ P,
        chiPrimeZero (baseSectorN L n) L 1 1 regimeB ν δ₀
          (fun i => h i) c (baseSectorSpin φ, baseSectorTheta θ)) ≤ 1 := by
    constructor
    · exact Finset.prod_nonneg fun c _ => (hχ c φ).1
    · exact Finset.prod_le_one₀ (fun c _ => (hχ c φ).1) (fun c _ => (hχ c φ).2)
  refine ⟨?_, fun φ => mul_nonneg (hleft φ).1 (hright φ).1, fun φ => ?_⟩
  · exact (Finset.measurable_prod _ fun c _ =>
      measurable_const.sub (measurable_baseSectorCube regimeB ν δ₀ h θ c)).mul
      (Finset.measurable_prod _ fun c _ => measurable_baseSectorCube regimeB ν δ₀ h θ c)
  · calc
      _ ≤ 1 * (∏ c ∈ (Finset.univ : Finset (Torus d n)) \ P,
          chiPrimeZero (baseSectorN L n) L 1 1 regimeB ν δ₀
            (fun i => h i) c (baseSectorSpin φ, baseSectorTheta θ)) :=
            mul_le_mul_of_nonneg_right (hleft φ).2 (hright φ).1
      _ ≤ 1 := by simpa using (hright φ).2

/-- The first physical density is an exact sum of selected `P` spin integrals. Each term
still integrates all bare spins; this identity performs no component localization and no
later `Q,R,S` decomposition. -/
theorem baseRho1_eq_sum_firstP
    {d N L n : ℕ} [NeZero L] [NeZero n] [NeZero N]
    (β a z ν : ℝ)
    (regimeB : Prop) (δ₀ : ℝ) (h : EuclideanSpace ℝ (Fin N))
    (g : Torus d (L * n) → Fin N → ℂ)
    (ψ : Torus d n → EuclideanSpace ℝ (Fin N)) :
    let θ := z • ψ
    let W : Finset (Torus d n) → CfgT d N L n → ℝ := fun P φ =>
      (∏ c ∈ P, (1 - chiPrimeZero (baseSectorN L n) L 1 1 regimeB ν δ₀
        (fun i => h i) c (baseSectorSpin φ, baseSectorTheta θ))) *
      ∏ c ∈ (Finset.univ : Finset (Torus d n)) \ P,
        chiPrimeZero (baseSectorN L n) L 1 1 regimeB ν δ₀
          (fun i => h i) c (baseSectorSpin φ, baseSectorTheta θ)
    let F : CfgT d N L n → ℂ := fun φ =>
      ((baseKernel d N L n β a θ φ : ℝ) : ℂ) *
        Complex.exp (-((β * energy d N (L * n) ν h φ : ℝ) : ℂ) +
          ∑ x : Torus d (L * n), ∑ i : Fin N,
            g x i * (((φ x : EuclideanSpace ℝ (Fin N)) i : ℝ) : ℂ))
    baseRho1 d N L n β a z ν h ψ g =
      ((z ^ (N * Fintype.card (Torus d n)) : ℝ) : ℂ) *
        ∑ P ∈ (Finset.univ : Finset (Torus d n)).powerset,
          ∫ φ, ((W P φ : ℝ) : ℂ) * F φ ∂aprioriMeasure d N (L * n) := by
  classical
  dsimp only
  let θ := z • ψ
  let W : Finset (Torus d n) → CfgT d N L n → ℝ := fun P φ =>
    (∏ c ∈ P, (1 - chiPrimeZero (baseSectorN L n) L 1 1 regimeB ν δ₀
      (fun i => h i) c (baseSectorSpin φ, baseSectorTheta θ))) *
    ∏ c ∈ (Finset.univ : Finset (Torus d n)) \ P,
      chiPrimeZero (baseSectorN L n) L 1 1 regimeB ν δ₀
        (fun i => h i) c (baseSectorSpin φ, baseSectorTheta θ)
  let F : CfgT d N L n → ℂ := fun φ =>
    ((baseKernel d N L n β a θ φ : ℝ) : ℂ) *
      Complex.exp (-((β * energy d N (L * n) ν h φ : ℝ) : ℂ) +
        ∑ x : Torus d (L * n), ∑ i : Fin N,
          g x i * (((φ x : EuclideanSpace ℝ (Fin N)) i : ℝ) : ℂ))
  have hFcont : Continuous F := by
    dsimp [F, baseKernel, baseQ, gaussT, energy]
    fun_prop
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hFcont.continuousOn
  have hm : Measurable F := hFcont.measurable
  have hInt (P : Finset (Torus d n)) :
      Integrable (fun φ : CfgT d N L n => ((W P φ : ℝ) : ℂ) * F φ)
        (aprioriMeasure d N (L * n)) := by
    obtain ⟨hw, hw0, hw1⟩ := baseFirstPhysicalP_weight_measurable_unit
      (d := d) (N := N) (L := L) (n := n) regimeB ν δ₀ h θ P
    refine Integrable.of_bound
      ((Complex.measurable_ofReal.comp hw).mul hm).aestronglyMeasurable C
      (Filter.Eventually.of_forall fun φ => ?_)
    have hp : |W P φ| ≤ 1 := by
      rw [abs_of_nonneg (hw0 φ)]
      exact hw1 φ
    calc
      ‖((W P φ : ℝ) : ℂ) * F φ‖ = |W P φ| * ‖F φ‖ := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      _ ≤ 1 * ‖F φ‖ := mul_le_mul_of_nonneg_right hp (norm_nonneg _)
      _ ≤ C := by simpa using hC φ (Set.mem_univ φ)
  have hpoint (φ : CfgT d N L n) :
      F φ = ∑ P ∈ (Finset.univ : Finset (Torus d n)).powerset,
        ((W P φ : ℝ) : ℂ) * F φ := by
    let p : BaseCfg d N (baseSectorN L n) L 1 1 :=
      (baseSectorSpin φ, baseSectorTheta θ)
    have hp := baseFirst_partition_pointwise (nn := baseSectorN L n)
      (L := L) (M := 1) (K := 1) regimeB ν δ₀ (fun i => h i) p (fun _ => F φ)
    convert hp using 1
    simp only [W, p, baseSectorN]
    rfl
  have hintegral : (∫ φ, F φ ∂aprioriMeasure d N (L * n)) =
      ∑ P ∈ (Finset.univ : Finset (Torus d n)).powerset,
        ∫ φ, ((W P φ : ℝ) : ℂ) * F φ ∂aprioriMeasure d N (L * n) := by
    conv_lhs =>
      arg 2
      ext φ
      rw [hpoint φ]
    exact integral_finsetSum _ (fun P _ => hInt P)
  change ((z ^ (N * Fintype.card (Torus d n)) : ℝ) : ℂ) *
      (∫ φ, F φ ∂aprioriMeasure d N (L * n)) = _
  rw [hintegral]

end Balaban.LargeField
