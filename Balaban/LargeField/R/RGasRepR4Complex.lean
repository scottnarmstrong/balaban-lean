/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.Rop

/-!
# The complex R operation

P7 (1.6), printed p. 496, and Definition III.8.3 of
`notes/phase1/LF-RECONSTRUCTION.md` define `R` by integrating the selected output
variables and dividing by the corresponding integrals of the real reference
densities.  `RopC` uses exactly the same measure-preserving decomposition and
reference densities as `Rop`, with a complex density in the numerator.  The
Bochner integral is defined on the whole function carrier; analytic applications
separately prove its absolute integrability.
-/

@[expose] public section

open MeasureTheory

namespace Balaban.LargeField

variable {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω}

/-- The complex form of P7 (1.6), using the reference densities of `RDecomp`.
The denominator is real and the numerator is the complex integral over the
variables of the components sent to `R`. -/
noncomputable def RopC (D : RDecomp ν) (ρ : Ω → ℂ) : Ω → ℂ :=
  fun ψ =>
    ((∏ c, D.r c ((D.e ψ).1 c) (D.e ψ).2 : ℝ) : ℂ) *
      ((∫ x, ρ (D.e.symm (x, (D.e ψ).2)) ∂(Measure.pi D.μ)) /
        ((∏ c, ∫ w, D.r c w (D.e ψ).2 ∂(D.μ c) : ℝ) : ℂ))

/-- The formula of P7 (1.6) for a complex term, unfolded at an output field. -/
theorem RopC_apply (D : RDecomp ν) (ρ : Ω → ℂ) (ψ : Ω) :
    RopC D ρ ψ =
      ((∏ c, D.r c ((D.e ψ).1 c) (D.e ψ).2 : ℝ) : ℂ) *
        ((∫ x, ρ (D.e.symm (x, (D.e ψ).2)) ∂(Measure.pi D.μ)) /
          ((∏ c, ∫ w, D.r c w (D.e ψ).2 ∂(D.μ c) : ℝ) : ℂ)) := rfl

/-- The complex R operation respects pointwise equality of densities. -/
theorem RopC_congr (D : RDecomp ν) {ρ ρ' : Ω → ℂ} (h : ∀ ψ, ρ ψ = ρ' ψ) :
    RopC D ρ = RopC D ρ' := by
  funext ψ
  simp only [RopC_apply, h]

/-- The zero density contributes zero to the complex R operation. -/
theorem RopC_zero (D : RDecomp ν) : RopC D (fun _ => 0) = fun _ => 0 := by
  funext ψ
  simp only [RopC_apply, integral_zero, zero_div, mul_zero]

end Balaban.LargeField
