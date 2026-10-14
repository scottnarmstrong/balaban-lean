/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Green.FinalLogDetLocal
public import Balaban.Correlations.KF0Cauchy
public import Balaban.Model.PartitionFunction
public import Balaban.Model.Derivatives
public import Mathlib.Analysis.SpecialFunctions.Complex.Log

/-!
# `RootFLog`: the principal logarithm of an exponential, and the multiscale exponent of Root-F

Root-F node A8.  A function with values in the slit plane that is an exponential `exp (S g)` on a
preconnected set containing `0`, with `S 0 = log (f 0)`, has the principal logarithm `S`
(`log_eq_of_exp_eq_of_slitPlane`).  The instance for the multiscale exponent
`⟨g, h⟩ + ∑_j ∑_x ∑_X ∑_i g_i(x) T_j(x, X; g)_i` with `T_j` analytic on the source ball is
`log_partition_eq_multiscale_of_exp`: for the assembly it only remains to prove the exponential
identity.
-/

@[expose] public section

namespace Balaban.Correlations

open Balaban Set

/-- Model-free principal logarithm: on a preconnected set `U` containing `0`, if `f` and `S` are
continuous on `U`, `f` takes values in the slit plane, `exp (S g) = f g` on `U` and
`S 0 = log (f 0)`, then `log (f g) = S g` on `U`. -/
theorem log_eq_of_exp_eq_of_slitPlane {X : Type*} [TopologicalSpace X] {U : Set X}
    (hU : IsPreconnected U) {x₀ : X} (hx₀ : x₀ ∈ U) {f S : X → ℂ}
    (hf : ContinuousOn f U) (hS : ContinuousOn S U)
    (hslit : ∀ g ∈ U, f g ∈ Complex.slitPlane)
    (hexp : ∀ g ∈ U, Complex.exp (S g) = f g) (h0 : S x₀ = Complex.log (f x₀)) :
    ∀ g ∈ U, Complex.log (f g) = S g := by
  have hlog : ContinuousOn (fun g => Complex.log (f g)) U :=
    ContinuousOn.clog hf hslit
  exact Balaban.Green.eq_of_exp_eq_of_continuousOn hU hx₀ hlog hS h0.symm fun g hg => by
    rw [Complex.exp_log (Complex.slitPlane_ne_zero (hslit g hg)), hexp g hg]

section Multiscale

variable {d N ℓ : ℕ} [NeZero ℓ] [NeZero N]

/-- Root-F, principal logarithm for the multiscale exponent: if the terms `T j x X` are analytic on
the source ball `∑ ∑ ‖g y i‖ < 1` and `Z(g)/Z(0) = exp Φ(g)` there, with
`Φ(g) = ⟨g, h⟩ + ∑_{j=1}^{kf+1} ∑_x ∑_X ∑_i g x i * T j x X g i`, then
`log (Z(g)/Z(0)) = Φ(g)` there. -/
theorem log_partition_eq_multiscale_of_exp {β ν : ℝ} {h : EuclideanSpace ℝ (Fin N)} {kf : ℕ}
    {T : ℕ → Torus d ℓ → Finset (Torus d ℓ) → (Torus d ℓ → Fin N → ℂ) → (Fin N → ℂ)}
    (hana : ∀ j x X, AnalyticOnNhd ℂ (T j x X) {g | ∑ y, ∑ i, ‖g y i‖ < 1})
    (hexp : ∀ g : Torus d ℓ → Fin N → ℂ, ∑ y, ∑ i, ‖g y i‖ < 1 →
      partitionFunction d N ℓ β ν h g / partitionFunction d N ℓ β ν h 0 =
        Complex.exp (∑ x, ∑ i, g x i * (h i : ℂ)
          + ∑ j ∈ Finset.Icc 1 (kf + 1), ∑ x, ∑ X : Finset (Torus d ℓ), ∑ i,
              g x i * T j x X g i))
    {g : Torus d ℓ → Fin N → ℂ} (hg : ∑ y, ∑ i, ‖g y i‖ < 1) :
    Complex.log (partitionFunction d N ℓ β ν h g / partitionFunction d N ℓ β ν h 0) =
      ∑ x, ∑ i, g x i * (h i : ℂ)
        + ∑ j ∈ Finset.Icc 1 (kf + 1), ∑ x, ∑ X : Finset (Torus d ℓ), ∑ i,
            g x i * T j x X g i := by
  set Φ : (Torus d ℓ → Fin N → ℂ) → ℂ := fun g => ∑ x, ∑ i, g x i * (h i : ℂ)
    + ∑ j ∈ Finset.Icc 1 (kf + 1), ∑ x, ∑ X : Finset (Torus d ℓ), ∑ i, g x i * T j x X g i
    with hΦ
  have hb : ball1 (Torus d ℓ) (Fin N) = sourceBall d N ℓ := rfl
  have hΦc : ContinuousOn Φ (sourceBall d N ℓ) := by
    refine ContinuousOn.add (Continuous.continuousOn (by fun_prop)) ?_
    refine continuousOn_finsetSum _ fun j _ => continuousOn_finsetSum _ fun x _ =>
      continuousOn_finsetSum _ fun X _ => continuousOn_finsetSum _ fun i _ => ?_
    exact (Continuous.continuousOn (by fun_prop)).mul
      ((continuousOn_pi.1 (hana j x X).continuousOn) i)
  have hfc : ContinuousOn (fun g => partitionFunction d N ℓ β ν h g /
      partitionFunction d N ℓ β ν h 0) (sourceBall d N ℓ) :=
    (hΦc.cexp).congr fun g hg => hexp g hg
  have hZ0 := partitionFunction_zero_ne_zero (d := d) (N := N) (ℓ := ℓ) β ν h
  have h0 : Φ 0 = Complex.log (partitionFunction d N ℓ β ν h 0 /
      partitionFunction d N ℓ β ν h 0) := by
    simp [hΦ, div_self hZ0]
  exact log_eq_of_exp_eq_of_slitPlane (convex_ball1 (α := Torus d ℓ) (β := Fin N)).isPreconnected
    (zero_mem_ball1 (α := Torus d ℓ) (β := Fin N)) hfc hΦc
    (fun g hg => partitionFunction_div_mem_slitPlane β ν h hg)
    (fun g hg => (hexp g hg).symm) h0 g hg

end Multiscale

end Balaban.Correlations
