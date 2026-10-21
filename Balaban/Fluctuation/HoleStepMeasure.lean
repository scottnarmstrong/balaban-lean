/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.HoleStep
public import Balaban.Fluctuation.Thm31cde
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The measure of the fluctuation integral on a region (P5 (2.47)–(2.48), (3.1)–(3.2))

After the substitution (2.39) the integral (2.16) over the old field `ψ_k` on the blocks of
`Ω_{k+1}` splits (P5 (2.42)–(2.48)): the variables `ψ̂` on the blocks of `Ω_{k+1} ∖ Ω''_{k+1}` are
integrated by the large-field operator `T'^{(k)}` (they are fixed here), and the variables `ψ̂` on the
blocks of `Ω''_{k+1}` are integrated in the *fluctuation integral*
```
(2π)^{-N|Ω''|/2} ∫ dψ̂_{Ω''} e^{-½‖ψ̂‖²} χ^{(k)}(Ω''_{k+1}) e^{-β_k V^{(k)}_eff + δℰ_k + δℱ_k + ℛ^{(k)} + ℬ''^{(k)}}
```
(2.48), the measure of (3.2) with `ℬ''^{(k)}` multiplied by a parameter `u`.  By (2.38) the exponent
is, up to a constant (a function of the fixed variables only), the logarithm `Φ` of the integrand of
(2.16) at the composed field `ψ_k(ψ̂)` of (2.39) plus `½ ‖ψ̂‖²` (the Gaussian weight is in the measure
`ν_{p₁}`).  This file defines, for the step on a region (`HoleStep`), with the logarithm `Φ` and the
old boundary terms `ℬ` given as functions of the field on the unit points of `Ω_{k+1}`:

* `fill`: the field `ψ̂` on the unit points of `Ω_{k+1}` with the integration variables on the unit
  points `inner` (those of `Ω''_{k+1}`) and the fixed values `ψout` on the others;
* `nuIn`: the measure `ν_{p₁}` of (2.5) on the integration variables (a probability measure for
  `p₁ > 0`, `isProbabilityMeasure_nuIn`);
* `expW`: the exponent `W(u, ψ̂) = Φ(ψ_k(ψ̂)) + ½ ∑_{inner} |ψ̂|² + u ℬ(ψ_k(ψ̂))` of the measure of (3.2);
* `avgOld`: the expectation `⟨ℬ''^{(k)}⟩''_u` (`avgFun`), and `oldTotal`: the interpolation
  average `∫₀¹ ⟨ℬ''^{(k)}⟩''_u du` (`interpAvg`), the contribution `ℬ''^{(k+1)}` of P5 (3.2) of the old
  boundary terms to the logarithm of the fluctuation integral (FLUCTUATION Theorem 3.1 (c)).

Characterization: `partFun_one_eq_mul_exp_oldTotal`: with the family `W(u)` of class `C¹` and
nonvanishing partition functions (`IsC1Family`, `Z(u) ≠ 0` on `[0, 1]`), the fluctuation integral
with the old boundary terms is the one without them times `exp (oldTotal)` (P5 (3.1)–(3.2): `ℬ''^{(k+1)}`
is the difference of the logarithms).
-/

@[expose] public section

namespace Balaban.Fluctuation

open MeasureTheory Balaban.Localization

namespace HoleStep

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ ϱ' : ℝ}
  (S : HoleStep d L N₁ m₁ k N ϱ ϱ')

open Classical in
/-- **The fluctuation variables on the unit points of `Ω_{k+1}`**: the integration variables `ψin`
on the unit points `inner` (the blocks of `Ω''_{k+1}`), the fixed values `ψout` on the other unit
points (the variables `ψ'_k` of `Ω_{k+1} ∖ Ω''_{k+1}`, integrated by `T'^{(k)}`). -/
noncomputable def fill (inner : Finset S.U) (ψin : inner → Rn N) (ψout : S.U → Fin N → ℂ) :
    S.U → Fin N → ℂ :=
  fun b i => if h : b ∈ inner then ((ψin ⟨b, h⟩ i : ℝ) : ℂ) else ψout b i

/-- **The measure `ν_{p₁}` of (2.5) on the integration variables of `Ω''_{k+1}`.** -/
noncomputable def nuIn (inner : Finset S.U) : Measure (inner → Rn N) :=
  fluctMeasure inner N S.p₁

theorem isProbabilityMeasure_nuIn (inner : Finset S.U) (hp : 0 < S.p₁) :
    IsProbabilityMeasure (S.nuIn inner) :=
  isProbabilityMeasure_fluctMeasure inner N hp

/-- **The exponent of the measure of P5 (3.2)** at the parameter `u`: for the logarithm `Φ` of the
integrand of (2.16) and the old boundary terms `ℬ`, both as functions of the field on the unit
points of `Ω_{k+1}`, evaluated at the composed field `ψ_k(ψ̂)` of (2.39) (cover `C`, radius `ρ`,
localization map `sloc`): `W(u, ψ̂) = Φ(ψ_k(ψ̂)) + ½ ∑_{inner} |ψ̂|² + u ℬ(ψ_k(ψ̂))`. -/
noncomputable def expW (C : DecCover d L N₁ m₁ (k + 1)) (ρ : ℝ) (sloc : S.U → Dec2.DecParams C)
    (inner : Finset S.U) (ψout : S.U → Fin N → ℂ) (Φ B : (S.U → Fin N → ℂ) → ℂ) (u : ℝ)
    (ψin : inner → Rn N) : ℂ :=
  Φ (S.composed C ρ sloc (S.fill inner ψin ψout)) + (1 / 2 : ℂ) * ((∑ b, ‖ψin b‖ ^ 2 : ℝ) : ℂ) +
    (u : ℂ) * B (S.composed C ρ sloc (S.fill inner ψin ψout))

/-- The old boundary terms at the composed field, as a function of the integration variables. -/
noncomputable def oldAt (C : DecCover d L N₁ m₁ (k + 1)) (ρ : ℝ) (sloc : S.U → Dec2.DecParams C)
    (inner : Finset S.U) (ψout : S.U → Fin N → ℂ) (B : (S.U → Fin N → ℂ) → ℂ)
    (ψin : inner → Rn N) : ℂ :=
  B (S.composed C ρ sloc (S.fill inner ψin ψout))

/-- **The expectation `⟨ℬ''^{(k)}⟩''_u`** in the measure of P5 (3.2) at the parameter `u`. -/
noncomputable def avgOld (C : DecCover d L N₁ m₁ (k + 1)) (ρ : ℝ) (sloc : S.U → Dec2.DecParams C)
    (inner : Finset S.U) (ψout : S.U → Fin N → ℂ) (Φ B : (S.U → Fin N → ℂ) → ℂ) (u : ℝ) : ℂ :=
  avgFun (S.nuIn inner) (S.expW C ρ sloc inner ψout Φ B) (S.oldAt C ρ sloc inner ψout B) u

/-- **The contribution of the old boundary terms to the logarithm of the fluctuation integral**
(P5 (3.1)–(3.2); FLUCTUATION Theorem 3.1 (c)): `ℬ''^{(k+1)} = ∫₀¹ ⟨ℬ''^{(k)}⟩''_u du`. -/
noncomputable def oldTotal (C : DecCover d L N₁ m₁ (k + 1)) (ρ : ℝ)
    (sloc : S.U → Dec2.DecParams C) (inner : Finset S.U) (ψout : S.U → Fin N → ℂ)
    (Φ B : (S.U → Fin N → ℂ) → ℂ) : ℂ :=
  interpAvg (S.nuIn inner) (S.expW C ρ sloc inner ψout Φ B)
    (fun _ => S.oldAt C ρ sloc inner ψout B)

theorem oldTotal_eq (C : DecCover d L N₁ m₁ (k + 1)) (ρ : ℝ)
    (sloc : S.U → Dec2.DecParams C) (inner : Finset S.U) (ψout : S.U → Fin N → ℂ)
    (Φ B : (S.U → Fin N → ℂ) → ℂ) :
    S.oldTotal C ρ sloc inner ψout Φ B =
      ∫ u in (0 : ℝ)..1, S.avgOld C ρ sloc inner ψout Φ B u := rfl

/-- The exponent is affine in the parameter `u`, with slope the old boundary terms. -/
theorem hasDerivAt_expW (C : DecCover d L N₁ m₁ (k + 1)) (ρ : ℝ)
    (sloc : S.U → Dec2.DecParams C) (inner : Finset S.U) (ψout : S.U → Fin N → ℂ)
    (Φ B : (S.U → Fin N → ℂ) → ℂ) (ψin : inner → Rn N) (u : ℝ) :
    HasDerivAt (fun r => S.expW C ρ sloc inner ψout Φ B r ψin)
      (S.oldAt C ρ sloc inner ψout B ψin) u := by
  unfold expW oldAt
  have h := ((hasDerivAt_id (u : ℝ)).ofReal_comp).mul_const
    (B (S.composed C ρ sloc (S.fill inner ψin ψout)))
  have h' := h.const_add (Φ (S.composed C ρ sloc (S.fill inner ψin ψout)) +
    (1 / 2 : ℂ) * ((∑ b, ‖ψin b‖ ^ 2 : ℝ) : ℂ))
  simpa using h'

/-- **`ℬ''^{(k+1)}` is the difference of the logarithms of the fluctuation integrals** (P5 (3.1)–(3.2),
the interpolation identity of FLUCTUATION Proposition 2.6): if the family of exponents is of class
`C¹` with derivative the old boundary terms, and the partition functions do not vanish on `[0,1]`,
the fluctuation integral with the old boundary terms is the one without them times
`exp (ℬ''^{(k+1)})`. -/
theorem partFun_one_eq_mul_exp_oldTotal (C : DecCover d L N₁ m₁ (k + 1)) (ρ : ℝ)
    (sloc : S.U → Dec2.DecParams C) (inner : Finset S.U) (ψout : S.U → Fin N → ℂ)
    (Φ B : (S.U → Fin N → ℂ) → ℂ) (hp : 0 < S.p₁) {U : Set ℝ}
    (hC1 : IsC1Family U (S.expW C ρ sloc inner ψout Φ B)
      (fun _ => S.oldAt C ρ sloc inner ψout B))
    (hZ : ∀ u ∈ Set.Icc (0 : ℝ) 1, partFun (S.nuIn inner) (S.expW C ρ sloc inner ψout Φ B) u ≠ 0) :
    partFun (S.nuIn inner) (S.expW C ρ sloc inner ψout Φ B) 1 =
      partFun (S.nuIn inner) (S.expW C ρ sloc inner ψout Φ B) 0 *
        Complex.exp (S.oldTotal C ρ sloc inner ψout Φ B) := by
  have := S.isProbabilityMeasure_nuIn inner hp
  exact hC1.partFun_one_eq hZ

end HoleStep

end Balaban.Fluctuation
