/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.CancelRemaining
public import Balaban.Background.MinimizerExpansion
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The action read of a perturbed background at fixed coefficients (P7CONV §3.4, (36)–(37), (52)–(53))

At fixed coefficients, mass and datum, the restricted action `A_X` of `φ + w` differs from that
of `φ` by one cross term and one half-square for each of the block, bond and mass reads.
Cauchy–Schwarz and the read-energy budgets give the bound
`β̂ |A_X(φ + w) - A_X(φ)| ≤ A [σ ∑ √(G G') + σ²/2 ∑ G']`.

* `weighted_bilinear_le`: the weighted bilinear Cauchy–Schwarz inequality;
* `actionRegionC_add_sub_eq`: the exact expansion of the difference;
* `actionRegionC_add_sub_le`: the budget bound.
-/

@[expose] public section

namespace Balaban.LargeField.ActionConv

open Balaban.Multiscale Balaban.Background Finset

section Cauchy

variable {N : ℕ}

/-- **Weighted bilinear Cauchy–Schwarz**: `|∑ c_x p_x · q_x| ≤ (∑ |c_x| |p_x|²)^{1/2}
(∑ |c_x| |q_x|²)^{1/2}` for the complex bilinear coordinate sum. -/
theorem weighted_bilinear_le {ι : Type*} (s : Finset ι) (c : ι → ℂ) (p q : ι → Fin N → ℂ) :
    ‖∑ x ∈ s, c x * ∑ i, p x i * q x i‖ ≤
      Real.sqrt (∑ x ∈ s, ‖c x‖ * ∑ i, ‖p x i‖ ^ 2) *
        Real.sqrt (∑ x ∈ s, ‖c x‖ * ∑ i, ‖q x i‖ ^ 2) := by
  have h1 : ‖∑ x ∈ s, c x * ∑ i, p x i * q x i‖ ≤
      ∑ x ∈ s, ∑ i, Real.sqrt (‖c x‖ * ‖p x i‖ ^ 2) * Real.sqrt (‖c x‖ * ‖q x i‖ ^ 2) := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun x _ => ?_)
    rw [norm_mul]
    refine (mul_le_mul_of_nonneg_left (norm_sum_le _ _) (norm_nonneg _)).trans ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [← Real.sqrt_mul (by positivity)]
    have e : (‖c x‖ * ‖p x i‖ ^ 2) * (‖c x‖ * ‖q x i‖ ^ 2) =
        (‖c x‖ * ‖p x i‖ * ‖q x i‖) ^ 2 := by ring
    rw [e, Real.sqrt_sq (by positivity), norm_mul]
    ring_nf
    exact le_rfl
  have h2 : ∑ x ∈ s, ∑ i, Real.sqrt (‖c x‖ * ‖p x i‖ ^ 2) * Real.sqrt (‖c x‖ * ‖q x i‖ ^ 2) =
      ∑ z ∈ s ×ˢ (Finset.univ : Finset (Fin N)),
        Real.sqrt (‖c z.1‖ * ‖p z.1 z.2‖ ^ 2) * Real.sqrt (‖c z.1‖ * ‖q z.1 z.2‖ ^ 2) := by
    rw [Finset.sum_product]
  have h3 := Real.sum_sqrt_mul_sqrt_le (s ×ˢ (Finset.univ : Finset (Fin N)))
    (f := fun z => ‖c z.1‖ * ‖p z.1 z.2‖ ^ 2) (g := fun z => ‖c z.1‖ * ‖q z.1 z.2‖ ^ 2)
    (fun z => by positivity) (fun z => by positivity)
  have e1 : ∑ z ∈ s ×ˢ (Finset.univ : Finset (Fin N)), ‖c z.1‖ * ‖p z.1 z.2‖ ^ 2 =
      ∑ x ∈ s, ‖c x‖ * ∑ i, ‖p x i‖ ^ 2 := by
    rw [Finset.sum_product]; simp only [Finset.mul_sum]
  have e2 : ∑ z ∈ s ×ˢ (Finset.univ : Finset (Fin N)), ‖c z.1‖ * ‖q z.1 z.2‖ ^ 2 =
      ∑ x ∈ s, ‖c x‖ * ∑ i, ‖q x i‖ ^ 2 := by
    rw [Finset.sum_product]; simp only [Finset.mul_sum]
  rw [e1, e2] at h3
  exact h1.trans (h2.le.trans h3)

/-- The self-pairing version: `|∑ c_x p_x · p_x| ≤ ∑ |c_x| |p_x|²`. -/
theorem weighted_bilinear_self_le {ι : Type*} (s : Finset ι) (c : ι → ℂ) (p : ι → Fin N → ℂ) :
    ‖∑ x ∈ s, c x * ∑ i, p x i * p x i‖ ≤ ∑ x ∈ s, ‖c x‖ * ∑ i, ‖p x i‖ ^ 2 := by
  have h := weighted_bilinear_le s c p p
  rwa [← Real.sqrt_mul (Finset.sum_nonneg fun x _ => by positivity),
    Real.sqrt_mul_self (Finset.sum_nonneg fun x _ => by positivity)] at h

/-- Expansion of a weighted bilinear square. -/
theorem weighted_sub_sq {ι : Type*} (s : Finset ι) (c : ι → ℂ) (p q : ι → Fin N → ℂ) :
    ∑ x ∈ s, c x * ∑ i, (p x i + q x i) * (p x i + q x i) =
      ∑ x ∈ s, c x * ∑ i, p x i * p x i +
        2 * ∑ x ∈ s, c x * ∑ i, p x i * q x i + ∑ x ∈ s, c x * ∑ i, q x i * q x i := by
  have h : ∀ x ∈ s, c x * ∑ i, (p x i + q x i) * (p x i + q x i) =
      (c x * ∑ i, p x i * p x i + 2 * (c x * ∑ i, p x i * q x i)) +
        c x * ∑ i, q x i * q x i := by
    intro x _
    have : ∑ i, (p x i + q x i) * (p x i + q x i) =
        ∑ i, p x i * p x i + 2 * ∑ i, p x i * q x i + ∑ i, q x i * q x i := by
      simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [this]; ring
  rw [Finset.sum_congr rfl h, Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]

/-- The scalar step of (52)–(53): `β̂ √E √E' ≤ A σ √(G G')` from `β̂ E ≤ G A`, `β̂ E' ≤ G' A σ²`. -/
theorem budget_sqrt_le {β E E' G G' A σ : ℝ} (hβ : 0 ≤ β)
    (hG : 0 ≤ G) (hA : 0 ≤ A) (hσ : 0 ≤ σ) (h1 : β * E ≤ G * A)
    (h2 : β * E' ≤ G' * (A * σ ^ 2)) :
    β * (Real.sqrt E * Real.sqrt E') ≤ A * σ * Real.sqrt (G * G') := by
  have e : β * (Real.sqrt E * Real.sqrt E') = Real.sqrt (β * E) * Real.sqrt (β * E') := by
    rw [Real.sqrt_mul hβ, Real.sqrt_mul hβ]
    have : Real.sqrt β * Real.sqrt β = β := Real.mul_self_sqrt hβ
    calc _ = (Real.sqrt β * Real.sqrt β) * (Real.sqrt E * Real.sqrt E') := by rw [this]
      _ = _ := by ring
  rw [e]
  calc Real.sqrt (β * E) * Real.sqrt (β * E') ≤
      Real.sqrt (G * A) * Real.sqrt (G' * (A * σ ^ 2)) :=
        mul_le_mul (Real.sqrt_le_sqrt h1) (Real.sqrt_le_sqrt h2) (Real.sqrt_nonneg _)
          (Real.sqrt_nonneg _)
    _ = A * σ * Real.sqrt (G * G') := by
        rw [← Real.sqrt_mul (by positivity)]
        have : G * A * (G' * (A * σ ^ 2)) = (A * σ) ^ 2 * (G * G') := by ring
        rw [this, Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]

end Cauchy

section Action

variable {d L N₀ K N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ} {G : GeneratingSet d L N₀ K ϱ}

/-- The bond pairing as a sum over oriented bonds. -/
theorem bondPair_eq_sum (X : Region G) (f g : Torus d (N₀ * L ^ K) → Fin N → ℂ) :
    X.bondPair f g = ∑ z : Torus d (N₀ * L ^ K) × Fin d, (X.starWeight z.1 z.2 : ℂ) *
      ∑ i, (f (z.1 + Pi.single z.2 1) i - f z.1 i) * (g (z.1 + Pi.single z.2 1) i - g z.1 i) := by
  unfold Region.bondPair
  rw [Fintype.sum_prod_type]

/-- The mass pairing with its coefficient `ν/2`. -/
theorem massPair_eq_sum (X : Region G) (ν : ℝ) (p q : Torus d (N₀ * L ^ K) → Fin N → ℂ) :
    (ν : ℂ) / 2 * X.massPair p q = (1 / 2) * ∑ x ∈ X.sites, (ν : ℂ) * ∑ i, p x i * q x i := by
  unfold Region.massPair
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  ring

/-- **The exact expansion of the action difference at fixed coefficients** (P7CONV (36) with
`b = e = 0`): one cross term and one half-square for each of the block, bond and mass reads.
Here `r = Ψ - Q φ`, `t = Q w`, `g = φ̄`, `v = w̃`, `s = φ - h`. -/
theorem actionRegionC_add_sub_eq (X : Region G) (a : ℕ → ℝ) (ν : ℝ) (Dat : BgData G N)
    (φ w : G.Ω 1 × Fin N → ℂ) :
    actionRegionC X a ν Dat (φ + w) - actionRegionC X a ν Dat φ =
      (∑ x ∈ X.sites, levelCoeff G a x * ∑ i, (Dat.Ψ x i - blockAvg G φ x i) *
          (-blockAvg G w x i) +
        (1 / 2) * ∑ x ∈ X.sites, levelCoeff G a x * ∑ i, blockAvg G w x i * blockAvg G w x i) +
      (∑ z : Torus d (N₀ * L ^ K) × Fin d, (X.starWeight z.1 z.2 : ℂ) * ∑ i,
          (barField G Dat.Ψ φ (z.1 + Pi.single z.2 1) i - barField G Dat.Ψ φ z.1 i) *
          (svec G w (z.1 + Pi.single z.2 1) i - svec G w z.1 i) +
        (1 / 2) * ∑ z : Torus d (N₀ * L ^ K) × Fin d, (X.starWeight z.1 z.2 : ℂ) * ∑ i,
          (svec G w (z.1 + Pi.single z.2 1) i - svec G w z.1 i) *
          (svec G w (z.1 + Pi.single z.2 1) i - svec G w z.1 i)) +
      (∑ x ∈ X.sites, (ν : ℂ) * ∑ i, (svec G φ x i - Dat.h x i) * svec G w x i +
        (1 / 2) * ∑ x ∈ X.sites, (ν : ℂ) * ∑ i, svec G w x i * svec G w x i) := by
  have eB : (fun x i => Dat.Ψ x i - blockAvg G (φ + w) x i) =
      fun x i => (Dat.Ψ x i - blockAvg G φ x i) + (-blockAvg G w x i) := by
    funext x i; rw [blockAvg_add]; ring
  have eG : barField G Dat.Ψ (φ + w) = fun x i => barField G Dat.Ψ φ x i + svec G w x i := by
    funext x i; exact barField_add Dat.Ψ φ w x i
  have eM : (fun x i => svec G (φ + w) x i - Dat.h x i) =
      fun x i => (svec G φ x i - Dat.h x i) + svec G w x i := by
    funext x i; rw [svec_add]; ring
  have hB := weighted_sub_sq X.sites (levelCoeff G a)
    (fun x i => Dat.Ψ x i - blockAvg G φ x i) (fun x i => -blockAvg G w x i)
  have hM := weighted_sub_sq X.sites (fun _ => (ν : ℂ))
    (fun x i => svec G φ x i - Dat.h x i) (fun x i => svec G w x i)
  have hG := weighted_sub_sq (Finset.univ : Finset (Torus d (N₀ * L ^ K) × Fin d))
    (fun z => (X.starWeight z.1 z.2 : ℂ))
    (fun z i => barField G Dat.Ψ φ (z.1 + Pi.single z.2 1) i - barField G Dat.Ψ φ z.1 i)
    (fun z i => svec G w (z.1 + Pi.single z.2 1) i - svec G w z.1 i)
  have hbond : X.bondPair (barField G Dat.Ψ (φ + w)) (barField G Dat.Ψ (φ + w)) =
      ∑ z : Torus d (N₀ * L ^ K) × Fin d, (X.starWeight z.1 z.2 : ℂ) * ∑ i,
        ((barField G Dat.Ψ φ (z.1 + Pi.single z.2 1) i - barField G Dat.Ψ φ z.1 i) +
          (svec G w (z.1 + Pi.single z.2 1) i - svec G w z.1 i)) *
        ((barField G Dat.Ψ φ (z.1 + Pi.single z.2 1) i - barField G Dat.Ψ φ z.1 i) +
          (svec G w (z.1 + Pi.single z.2 1) i - svec G w z.1 i)) := by
    rw [bondPair_eq_sum, eG]
    refine Finset.sum_congr rfl fun z _ => ?_
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  unfold actionRegionC
  rw [eB, eM, hbond, bondPair_eq_sum X (barField G Dat.Ψ φ) (barField G Dat.Ψ φ),
    massPair_eq_sum, massPair_eq_sum]
  unfold Region.blockPair
  beta_reduce
  rw [hB, hM, hG]
  ring_nf

/-- Triangle inequality for the six terms of the expansion. -/
theorem norm_six_le (b₁ b₂ b₃ b₄ b₅ b₆ : ℂ) :
    ‖(b₁ + 1 / 2 * b₂) + (b₃ + 1 / 2 * b₄) + (b₅ + 1 / 2 * b₆)‖ ≤
      ‖b₁‖ + ‖b₂‖ / 2 + (‖b₃‖ + ‖b₄‖ / 2) + (‖b₅‖ + ‖b₆‖ / 2) := by
  have h : ∀ x y : ℂ, ‖x + 1 / 2 * y‖ ≤ ‖x‖ + ‖y‖ / 2 := fun x y => by
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul]
    simp only [one_div, norm_inv, Complex.norm_ofNat]
    linarith
  calc _ ≤ ‖(b₁ + 1 / 2 * b₂) + (b₃ + 1 / 2 * b₄)‖ + ‖b₅ + 1 / 2 * b₆‖ := norm_add_le _ _
    _ ≤ (‖b₁ + 1 / 2 * b₂‖ + ‖b₃ + 1 / 2 * b₄‖) + ‖b₅ + 1 / 2 * b₆‖ := by
        gcongr; exact norm_add_le _ _
    _ ≤ _ := by
        have := h b₁ b₂; have := h b₃ b₄; have := h b₅ b₆; linarith

/-- **The fixed-coefficient action difference under the read budgets** (P7CONV (52)–(53)):
if `β̂ E_Z ≤ G_Z A` for the three unprimed read energies of `φ` and `β̂ E'_Z ≤ G'_Z A σ²` for the
three read energies of the perturbation `w`, then
`β̂ |A_X(φ + w) - A_X(φ)| ≤ A [σ ∑_Z √(G_Z G'_Z) + σ²/2 ∑_Z G'_Z]`. -/
theorem actionRegionC_add_sub_le (X : Region G) (a : ℕ → ℝ) (ν : ℝ) (Dat : BgData G N)
    (φ w : G.Ω 1 × Fin N → ℂ) {β A σ GB GB' GG GG' GM GM' : ℝ}
    (hβ : 0 ≤ β) (hA : 0 ≤ A) (hσ : 0 ≤ σ) (hGB : 0 ≤ GB) (hGG : 0 ≤ GG) (hGM : 0 ≤ GM)
    (hB : β * ∑ x ∈ X.sites, ‖levelCoeff G a x‖ * ∑ i, ‖Dat.Ψ x i - blockAvg G φ x i‖ ^ 2 ≤
      GB * A)
    (hB' : β * ∑ x ∈ X.sites, ‖levelCoeff G a x‖ * ∑ i, ‖blockAvg G w x i‖ ^ 2 ≤
      GB' * (A * σ ^ 2))
    (hG : β * ∑ z : Torus d (N₀ * L ^ K) × Fin d, X.starWeight z.1 z.2 * ∑ i,
      ‖barField G Dat.Ψ φ (z.1 + Pi.single z.2 1) i - barField G Dat.Ψ φ z.1 i‖ ^ 2 ≤ GG * A)
    (hG' : β * ∑ z : Torus d (N₀ * L ^ K) × Fin d, X.starWeight z.1 z.2 * ∑ i,
      ‖svec G w (z.1 + Pi.single z.2 1) i - svec G w z.1 i‖ ^ 2 ≤ GG' * (A * σ ^ 2))
    (hM : β * ∑ x ∈ X.sites, |ν| * ∑ i, ‖svec G φ x i - Dat.h x i‖ ^ 2 ≤ GM * A)
    (hM' : β * ∑ x ∈ X.sites, |ν| * ∑ i, ‖svec G w x i‖ ^ 2 ≤ GM' * (A * σ ^ 2)) :
    ‖(β : ℂ) * (actionRegionC X a ν Dat (φ + w) - actionRegionC X a ν Dat φ)‖ ≤
      A * (σ * (Real.sqrt (GB * GB') + Real.sqrt (GG * GG') + Real.sqrt (GM * GM')) +
        σ ^ 2 / 2 * (GB' + GG' + GM')) := by
  have hw : ∀ z : Torus d (N₀ * L ^ K) × Fin d,
      ‖(X.starWeight z.1 z.2 : ℂ)‖ = X.starWeight z.1 z.2 := fun z => by
    rw [Complex.norm_real, Real.norm_of_nonneg (starWeight_nonneg X z.1 z.2)]
  have n1 := weighted_bilinear_le X.sites (levelCoeff G a)
    (fun x i => Dat.Ψ x i - blockAvg G φ x i) (fun x i => -blockAvg G w x i)
  have n2 := weighted_bilinear_self_le X.sites (levelCoeff G a) (fun x i => blockAvg G w x i)
  have n3 := weighted_bilinear_le (Finset.univ : Finset (Torus d (N₀ * L ^ K) × Fin d))
    (fun z => (X.starWeight z.1 z.2 : ℂ))
    (fun z i => barField G Dat.Ψ φ (z.1 + Pi.single z.2 1) i - barField G Dat.Ψ φ z.1 i)
    (fun z i => svec G w (z.1 + Pi.single z.2 1) i - svec G w z.1 i)
  have n4 := weighted_bilinear_self_le (Finset.univ : Finset (Torus d (N₀ * L ^ K) × Fin d))
    (fun z => (X.starWeight z.1 z.2 : ℂ))
    (fun z i => svec G w (z.1 + Pi.single z.2 1) i - svec G w z.1 i)
  have n5 := weighted_bilinear_le X.sites (fun _ => (ν : ℂ))
    (fun x i => svec G φ x i - Dat.h x i) (fun x i => svec G w x i)
  have n6 := weighted_bilinear_self_le X.sites (fun _ => (ν : ℂ)) (fun x i => svec G w x i)
  simp only [norm_neg, hw, Complex.norm_real, Real.norm_eq_abs] at n1 n2 n3 n4 n5 n6
  have k1 := budget_sqrt_le hβ hGB hA hσ hB hB'
  have k3 := budget_sqrt_le hβ hGG hA hσ hG hG'
  have k5 := budget_sqrt_le hβ hGM hA hσ hM hM'
  rw [actionRegionC_add_sub_eq, norm_mul, Complex.norm_real, Real.norm_of_nonneg hβ]
  refine (mul_le_mul_of_nonneg_left (norm_six_le _ _ _ _ _ _) hβ).trans ?_
  have m1 := mul_le_mul_of_nonneg_left n1 hβ
  have m2 := mul_le_mul_of_nonneg_left n2 hβ
  have m3 := mul_le_mul_of_nonneg_left n3 hβ
  have m4 := mul_le_mul_of_nonneg_left n4 hβ
  have m5 := mul_le_mul_of_nonneg_left n5 hβ
  have m6 := mul_le_mul_of_nonneg_left n6 hβ
  nlinarith [m1, m2, m3, m4, m5, m6, k1, k3, k5, hB', hG', hM']

end Action

end Balaban.LargeField.ActionConv
