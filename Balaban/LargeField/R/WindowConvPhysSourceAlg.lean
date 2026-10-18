/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.CoeffResponseAction
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The cost of one conversion step from six read budgets (P7CONV (36)–(40))

At one datum, the action after the conversion step `n - 1 → n` differs from the action before it
by (i) the change of the background at the coefficients of the step (a cross term and a square
for each of the block, bond and mass reads) and (ii) the change of the couplings at one
background.  Since `β_{n-1} a_{n-1} = β_n a_n`, (ii) has no block part.

* `actionRegionC_ratio_sub_eq`: the exact form of (ii);
* `actionRegionC_ratio_sub_le`: its bound by the bond and mass budgets;
* `convCost_le_of_budgets`: the total bound by the six budgets.
-/

@[expose] public section

namespace Balaban.LargeField.ActionConv

open Balaban.Multiscale Balaban.Background Finset

variable {d L N₀ K N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ} {G : GeneratingSet d L N₀ K ϱ}

/-- The layer weights `β a(ℓ)` agree, so do the weights `β lc(x)` of the block pairing. -/
theorem levelCoeff_mul_eq {a₀ a₁ : ℕ → ℝ} {β₀ β₁ : ℝ} (h : ∀ ℓ, β₁ * a₁ ℓ = β₀ * a₀ ℓ)
    (x : Torus d (N₀ * L ^ K)) :
    (β₁ : ℂ) * levelCoeff G a₁ x = (β₀ : ℂ) * levelCoeff G a₀ x := by
  unfold levelCoeff
  rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, mul_div_assoc', mul_div_assoc', h]

/-- **The change of the couplings at one background** (the remainder of P7CONV (36)): with
`β₁ a₁ = β₀ a₀` the block terms cancel. -/
theorem actionRegionC_ratio_sub_eq (X : Region G) {a₀ a₁ : ℕ → ℝ} {ν₀ ν₁ β₀ β₁ : ℝ}
    (hcoef : ∀ ℓ, β₁ * a₁ ℓ = β₀ * a₀ ℓ) (Dat : BgData G N) (φ : G.Ω 1 × Fin N → ℂ) :
    (β₁ : ℂ) * actionRegionC X a₁ ν₁ Dat φ - (β₀ : ℂ) * actionRegionC X a₀ ν₀ Dat φ =
      ((β₁ - β₀ : ℝ) : ℂ) / 2 * X.bondPair (barField G Dat.Ψ φ) (barField G Dat.Ψ φ) +
      ((β₁ * ν₁ - β₀ * ν₀ : ℝ) : ℂ) / 2 *
        X.massPair (fun x i => svec G φ x i - Dat.h x i) (fun x i => svec G φ x i - Dat.h x i) := by
  have hB : (β₁ : ℂ) * X.blockPair a₁ (fun x i => Dat.Ψ x i - blockAvg G φ x i)
      (fun x i => Dat.Ψ x i - blockAvg G φ x i) =
      (β₀ : ℂ) * X.blockPair a₀ (fun x i => Dat.Ψ x i - blockAvg G φ x i)
      (fun x i => Dat.Ψ x i - blockAvg G φ x i) := by
    unfold Region.blockPair
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← mul_assoc, ← mul_assoc, levelCoeff_mul_eq hcoef]
  unfold actionRegionC
  push_cast
  linear_combination (1 / 2 : ℂ) * hB

/-- The norm of a weighted bilinear sum with the bond weights. -/
theorem norm_bondPair_self_le (X : Region G) (f : Torus d (N₀ * L ^ K) → Fin N → ℂ) :
    ‖X.bondPair f f‖ ≤ ∑ z : Torus d (N₀ * L ^ K) × Fin d, X.starWeight z.1 z.2 *
      ∑ i, ‖f (z.1 + Pi.single z.2 1) i - f z.1 i‖ ^ 2 := by
  have hw : ∀ z : Torus d (N₀ * L ^ K) × Fin d,
      ‖(X.starWeight z.1 z.2 : ℂ)‖ = X.starWeight z.1 z.2 := fun z => by
    rw [Complex.norm_real, Real.norm_of_nonneg (starWeight_nonneg X z.1 z.2)]
  have n3 := weighted_bilinear_self_le (Finset.univ : Finset (Torus d (N₀ * L ^ K) × Fin d))
    (fun z => (X.starWeight z.1 z.2 : ℂ))
    (fun z i => f (z.1 + Pi.single z.2 1) i - f z.1 i)
  simp only [hw] at n3
  rwa [bondPair_eq_sum]

/-- The norm of the mass pairing. -/
theorem norm_massPair_self_le (X : Region G) (p : Torus d (N₀ * L ^ K) → Fin N → ℂ) :
    ‖X.massPair p p‖ ≤ ∑ x ∈ X.sites, ∑ i, ‖p x i‖ ^ 2 := by
  have h := weighted_bilinear_self_le X.sites (fun _ => (1 : ℂ)) p
  simp only [norm_one, one_mul] at h
  unfold Region.massPair
  simpa using h

/-- **The coupling change under the bond and mass budgets.**  If
`|β₁ - β₀| ≤ 2ρ β₁`, `|β₁ ν₁ - β₀ ν₀| ≤ 2ρ β₁ |ν₁|`, `β₁ E_G ≤ G_G A`, `β₁ E_M ≤ G_M A`, the
change is at most `ρ A (G_G + G_M)`. -/
theorem actionRegionC_ratio_sub_le (X : Region G) {a₀ a₁ : ℕ → ℝ} {ν₀ ν₁ β₀ β₁ ρ A GG GM : ℝ}
    (hcoef : ∀ ℓ, β₁ * a₁ ℓ = β₀ * a₀ ℓ) (hβ₁ : 0 ≤ β₁) (hρ : 0 ≤ ρ)
    (hb : |β₁ - β₀| ≤ 2 * ρ * β₁) (hc : |β₁ * ν₁ - β₀ * ν₀| ≤ 2 * ρ * (β₁ * |ν₁|))
    (Dat : BgData G N) (φ : G.Ω 1 × Fin N → ℂ)
    (hG : β₁ * ∑ z : Torus d (N₀ * L ^ K) × Fin d, X.starWeight z.1 z.2 * ∑ i,
      ‖barField G Dat.Ψ φ (z.1 + Pi.single z.2 1) i - barField G Dat.Ψ φ z.1 i‖ ^ 2 ≤ GG * A)
    (hM : β₁ * ∑ x ∈ X.sites, |ν₁| * ∑ i, ‖svec G φ x i - Dat.h x i‖ ^ 2 ≤ GM * A) :
    ‖(β₁ : ℂ) * actionRegionC X a₁ ν₁ Dat φ - (β₀ : ℂ) * actionRegionC X a₀ ν₀ Dat φ‖ ≤
      ρ * (A * (GG + GM)) := by
  rw [actionRegionC_ratio_sub_eq X hcoef]
  have h1 := norm_bondPair_self_le X (barField G Dat.Ψ φ)
  have h2 := norm_massPair_self_le X (fun x i => svec G φ x i - Dat.h x i)
  set EG := ∑ z : Torus d (N₀ * L ^ K) × Fin d, X.starWeight z.1 z.2 * ∑ i,
      ‖barField G Dat.Ψ φ (z.1 + Pi.single z.2 1) i - barField G Dat.Ψ φ z.1 i‖ ^ 2 with hEG
  set EM := ∑ x ∈ X.sites, ∑ i, ‖svec G φ x i - Dat.h x i‖ ^ 2 with hEM
  have hEG0 : 0 ≤ EG := Finset.sum_nonneg fun z _ => mul_nonneg (starWeight_nonneg X z.1 z.2)
    (Finset.sum_nonneg fun i _ => by positivity)
  have hEM0 : 0 ≤ EM := Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun i _ => by positivity
  have hMe : β₁ * (|ν₁| * EM) ≤ GM * A := by
    have : ∑ x ∈ X.sites, |ν₁| * ∑ i, ‖svec G φ x i - Dat.h x i‖ ^ 2 = |ν₁| * EM := by
      rw [hEM, Finset.mul_sum]
    rwa [this] at hM
  refine (norm_add_le _ _).trans ?_
  simp only [norm_mul, norm_div, Complex.norm_real, Complex.norm_ofNat, Real.norm_eq_abs]
  have t1 : |β₁ - β₀| / 2 * ‖X.bondPair (barField G Dat.Ψ φ) (barField G Dat.Ψ φ)‖ ≤ ρ * (GG * A) := by
    calc _ ≤ (2 * ρ * β₁) / 2 * EG := by
          gcongr
      _ = ρ * (β₁ * EG) := by ring
      _ ≤ ρ * (GG * A) := mul_le_mul_of_nonneg_left hG hρ
  have t2 : |β₁ * ν₁ - β₀ * ν₀| / 2 *
      ‖X.massPair (fun x i => svec G φ x i - Dat.h x i)
        (fun x i => svec G φ x i - Dat.h x i)‖ ≤ ρ * (GM * A) := by
    calc _ ≤ (2 * ρ * (β₁ * |ν₁|)) / 2 * EM := by
          gcongr
      _ = ρ * (β₁ * (|ν₁| * EM)) := by ring
      _ ≤ ρ * (GM * A) := mul_le_mul_of_nonneg_left hMe hρ
  nlinarith [t1, t2]

/-- **The cost of one conversion step under the six read budgets** (P7CONV (38)–(40)): the action
`β₁ A(a₁, ν₁; φ + w)` after the step against `β₀ A(a₀, ν₀; φ)` before it, with `β₁ a₁ = β₀ a₀`,
`|β₁ - β₀| ≤ 2ρ β₁`, `|β₁ ν₁ - β₀ ν₀| ≤ 2ρ β₁ |ν₁|`, the unprimed energies of `φ` at most
`G_Z A` and the energies of `w` at most `G'_Z A σ²` (all weighted by `β₁`, `a₁`, `ν₁`). -/
theorem actionRegionC_step_le (X : Region G) {a₀ a₁ : ℕ → ℝ} {ν₀ ν₁ β₀ β₁ ρ A σ : ℝ}
    {GB GB' GG GG' GM GM' : ℝ}
    (hcoef : ∀ ℓ, β₁ * a₁ ℓ = β₀ * a₀ ℓ) (hβ₁ : 0 ≤ β₁) (hρ : 0 ≤ ρ) (hA : 0 ≤ A) (hσ : 0 ≤ σ)
    (hGB : 0 ≤ GB) (hGG : 0 ≤ GG) (hGM : 0 ≤ GM)
    (hb : |β₁ - β₀| ≤ 2 * ρ * β₁) (hc : |β₁ * ν₁ - β₀ * ν₀| ≤ 2 * ρ * (β₁ * |ν₁|))
    (Dat : BgData G N) (φ w : G.Ω 1 × Fin N → ℂ)
    (hB : β₁ * ∑ x ∈ X.sites, ‖levelCoeff G a₁ x‖ * ∑ i, ‖Dat.Ψ x i - blockAvg G φ x i‖ ^ 2 ≤
      GB * A)
    (hB' : β₁ * ∑ x ∈ X.sites, ‖levelCoeff G a₁ x‖ * ∑ i, ‖blockAvg G w x i‖ ^ 2 ≤
      GB' * (A * σ ^ 2))
    (hG : β₁ * ∑ z : Torus d (N₀ * L ^ K) × Fin d, X.starWeight z.1 z.2 * ∑ i,
      ‖barField G Dat.Ψ φ (z.1 + Pi.single z.2 1) i - barField G Dat.Ψ φ z.1 i‖ ^ 2 ≤ GG * A)
    (hG' : β₁ * ∑ z : Torus d (N₀ * L ^ K) × Fin d, X.starWeight z.1 z.2 * ∑ i,
      ‖svec G w (z.1 + Pi.single z.2 1) i - svec G w z.1 i‖ ^ 2 ≤ GG' * (A * σ ^ 2))
    (hM : β₁ * ∑ x ∈ X.sites, |ν₁| * ∑ i, ‖svec G φ x i - Dat.h x i‖ ^ 2 ≤ GM * A)
    (hM' : β₁ * ∑ x ∈ X.sites, |ν₁| * ∑ i, ‖svec G w x i‖ ^ 2 ≤ GM' * (A * σ ^ 2)) :
    ‖(β₁ : ℂ) * actionRegionC X a₁ ν₁ Dat (φ + w) - (β₀ : ℂ) * actionRegionC X a₀ ν₀ Dat φ‖ ≤
      A * (σ * (Real.sqrt (GB * GB') + Real.sqrt (GG * GG') + Real.sqrt (GM * GM')) +
        σ ^ 2 / 2 * (GB' + GG' + GM')) + ρ * (A * (GG + GM)) := by
  have h1 := actionRegionC_add_sub_le X a₁ ν₁ Dat φ w hβ₁ hA hσ hGB hGG hGM hB hB' hG hG' hM hM'
  have h2 := actionRegionC_ratio_sub_le X (ν₀ := ν₀) hcoef hβ₁ hρ hb hc Dat φ hG hM
  have e : (β₁ : ℂ) * actionRegionC X a₁ ν₁ Dat (φ + w) - (β₀ : ℂ) * actionRegionC X a₀ ν₀ Dat φ =
      (β₁ : ℂ) * (actionRegionC X a₁ ν₁ Dat (φ + w) - actionRegionC X a₁ ν₁ Dat φ) +
      ((β₁ : ℂ) * actionRegionC X a₁ ν₁ Dat φ - (β₀ : ℂ) * actionRegionC X a₀ ν₀ Dat φ) := by ring
  rw [e]
  exact (norm_add_le _ _).trans (add_le_add h1 h2)

end Balaban.LargeField.ActionConv
