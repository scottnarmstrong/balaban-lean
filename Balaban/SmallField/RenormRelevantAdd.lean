/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Complex.Basic

/-!
# The relevant parts of a density: additivity and shift invariance

For a density `D : (Fin N → ℂ) → (Fin N → ℂ) → ℂ` of the pair (constant field `ψ`, constant `h`),
the three local functionals of the renormalization conditions, in the shape of the right sides of
`hval`, `hpsi`, `hh` of `Def6.renormCondAlong_of_system`: the value at the reference point
`(e_{i₀}, e_{i₀})`, the derivative along `ψ = (1+t) e_{i₀}`, and the derivative in `h` at `e_{i₀}`.
They are additive for differentiable densities and unchanged by subtracting the constant value of
the density at the reference point; the shifted density vanishes there.  The moment functional is a
limit of sums and is additive by `Filter.Tendsto.add`.
-/

@[expose] public section

namespace Balaban.SmallField

variable {N : ℕ}

/-- The reference direction `e_{i₀}`. -/
abbrev relE (i₀ : Fin N) : Fin N → ℂ := Pi.single i₀ 1

/-- The value of a density at the reference point `(e_{i₀}, e_{i₀})`. -/
def relVal (D : (Fin N → ℂ) → (Fin N → ℂ) → ℂ) (i₀ : Fin N) : ℂ := D (relE i₀) (relE i₀)

/-- The derivative of a density along `ψ = (1+t) e_{i₀}` at `t = 0`. -/
noncomputable def relDpsi (D : (Fin N → ℂ) → (Fin N → ℂ) → ℂ) (i₀ : Fin N) : ℂ :=
  deriv (fun t : ℂ => D ((1 + t) • relE i₀) (relE i₀)) 0

/-- The derivative of a density in `h` at `e_{i₀}`, in the direction `e_{i₀}`. -/
noncomputable def relDh (D : (Fin N → ℂ) → (Fin N → ℂ) → ℂ) (i₀ : Fin N) : ℂ :=
  fderiv ℂ (fun h : Fin N → ℂ => D (relE i₀) h) (relE i₀) (relE i₀)

/-- The density shifted by its constant value at the reference point. -/
def relShift (D : (Fin N → ℂ) → (Fin N → ℂ) → ℂ) (i₀ : Fin N) :
    (Fin N → ℂ) → (Fin N → ℂ) → ℂ := fun ψ h => D ψ h - relVal D i₀

theorem relVal_add (D₁ D₂ : (Fin N → ℂ) → (Fin N → ℂ) → ℂ) (i₀ : Fin N) :
    relVal (fun ψ h => D₁ ψ h + D₂ ψ h) i₀ = relVal D₁ i₀ + relVal D₂ i₀ := rfl

theorem relVal_relShift (D : (Fin N → ℂ) → (Fin N → ℂ) → ℂ) (i₀ : Fin N) :
    relVal (relShift D i₀) i₀ = 0 := by
  simp [relVal, relShift]

theorem relDpsi_add (D₁ D₂ : (Fin N → ℂ) → (Fin N → ℂ) → ℂ) (i₀ : Fin N)
    (h₁ : DifferentiableAt ℂ (fun t : ℂ => D₁ ((1 + t) • relE i₀) (relE i₀)) 0)
    (h₂ : DifferentiableAt ℂ (fun t : ℂ => D₂ ((1 + t) • relE i₀) (relE i₀)) 0) :
    relDpsi (fun ψ h => D₁ ψ h + D₂ ψ h) i₀ = relDpsi D₁ i₀ + relDpsi D₂ i₀ :=
  deriv_add h₁ h₂

theorem relDpsi_relShift (D : (Fin N → ℂ) → (Fin N → ℂ) → ℂ) (i₀ : Fin N) :
    relDpsi (relShift D i₀) i₀ = relDpsi D i₀ := by
  simp only [relDpsi, relShift]
  rw [deriv_sub_const]

theorem relDh_add (D₁ D₂ : (Fin N → ℂ) → (Fin N → ℂ) → ℂ) (i₀ : Fin N)
    (h₁ : DifferentiableAt ℂ (fun h : Fin N → ℂ => D₁ (relE i₀) h) (relE i₀))
    (h₂ : DifferentiableAt ℂ (fun h : Fin N → ℂ => D₂ (relE i₀) h) (relE i₀)) :
    relDh (fun ψ h => D₁ ψ h + D₂ ψ h) i₀ = relDh D₁ i₀ + relDh D₂ i₀ := by
  have := fderiv_fun_add h₁ h₂
  simp only [relDh]
  rw [this]; rfl

theorem relDh_relShift (D : (Fin N → ℂ) → (Fin N → ℂ) → ℂ) (i₀ : Fin N) :
    relDh (relShift D i₀) i₀ = relDh D i₀ := by
  simp only [relDh, relShift]
  rw [fderiv_sub_const]

/-- The moment functional is additive: the limit of a sum of sequences. -/
theorem relMom_add {a b : ℕ → ℂ} {x y : ℂ} (ha : Filter.Tendsto a Filter.atTop (nhds x))
    (hb : Filter.Tendsto b Filter.atTop (nhds y)) :
    Filter.Tendsto (fun n => a n + b n) Filter.atTop (nhds (x + y)) := ha.add hb

end Balaban.SmallField
