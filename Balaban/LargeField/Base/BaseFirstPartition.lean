module

public import Balaban.LargeField.Base.BaseRecord
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Exact first partition of a test-free density

The first cube test is inserted by a partition of unity. The identity applies to an
arbitrary bare integrand and leaves the spins on failed cubes in that integrand.
-/

@[expose] public section

namespace Balaban.LargeField

open Balaban MeasureTheory

/-- The first binary partition multiplies an arbitrary bare integrand without changing it.
Its summands retain the complete input configuration, including spins on failed cubes. -/
theorem baseFirst_partition_pointwise
    {d N L M K : ℕ} {nn : ℕ → ℕ}
    [∀ k, NeZero (nn k)] [NeZero M] [NeZero L]
    (regimeB : Prop) (ν δ₀ : ℝ) (h : Fin N → ℝ)
    (p : BaseCfg d N nn L M K) (F : BaseCfg d N nn L M K → ℂ) :
    F p =
      ∑ P ∈ (Finset.univ : Finset (Torus d (nn 1))).powerset,
        (((∏ c ∈ P, (1 - chiPrimeZero nn L M K regimeB ν δ₀ h c p)) *
          ∏ c ∈ (Finset.univ : Finset (Torus d (nn 1))) \ P,
            chiPrimeZero nn L M K regimeB ν δ₀ h c p : ℝ) : ℂ) * F p := by
  classical
  rw [← Finset.sum_mul, ← Complex.ofReal_sum]
  rw [chiPrimeZero_decomposition]
  simp

/-- Exact first transform identity for any integrable bare density and integrable selected
pieces. The integrability condition makes the finite Bochner sum legitimate. -/
theorem baseFirst_partition_integral
    {d N L M K : ℕ} {nn : ℕ → ℕ}
    [∀ k, NeZero (nn k)] [NeZero M] [NeZero L]
    [MeasurableSpace (BaseCfg d N nn L M K)]
    (μ : Measure (BaseCfg d N nn L M K))
    (regimeB : Prop) (ν δ₀ : ℝ) (h : Fin N → ℝ)
    (F : BaseCfg d N nn L M K → ℂ)
    (hInt : ∀ P ∈ (Finset.univ : Finset (Torus d (nn 1))).powerset,
      Integrable (fun p =>
        (((∏ c ∈ P, (1 - chiPrimeZero nn L M K regimeB ν δ₀ h c p)) *
          ∏ c ∈ (Finset.univ : Finset (Torus d (nn 1))) \ P,
            chiPrimeZero nn L M K regimeB ν δ₀ h c p : ℝ) : ℂ) * F p) μ) :
    ∫ p, F p ∂μ =
      ∑ P ∈ (Finset.univ : Finset (Torus d (nn 1))).powerset,
        ∫ p,
          (((∏ c ∈ P, (1 - chiPrimeZero nn L M K regimeB ν δ₀ h c p)) *
            ∏ c ∈ (Finset.univ : Finset (Torus d (nn 1))) \ P,
              chiPrimeZero nn L M K regimeB ν δ₀ h c p : ℝ) : ℂ) * F p ∂μ := by
  classical
  conv_lhs =>
    arg 2
    ext p
    rw [baseFirst_partition_pointwise regimeB ν δ₀ h p F]
  rw [integral_finsetSum _ hInt]

end Balaban.LargeField
