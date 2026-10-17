/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, GPT-6-Sol (astra)
-/
module

public import Balaban.LargeField.Base.KF0SectorSum
import Mathlib.Tactic.Linarith

/-!
# The raw bare-sector Peierls charge at the linked-gas threshold

At cutoff radius `r = 1/2`, the landed bad-spin energy bound gives `βν/8` per bad block.
For a nonempty bad set this pays a gas charge `p + H |B|` when `8(p+H) ≤ βν`.
The theorem is pointwise in the retained bad spins and at zero source. It does not identify
this factor with the normalized heavy component activity `τ` of the linked gas.
-/

@[expose] public section

namespace Balaban.LargeField

open SphereChart

/-- The bad-spin factor at zero source pays the numerical heavy charge before the
Gaussian determinant and the good-region integral are incorporated. The underlying
Peierls inequality is `KF0SectorSum.kf0BadFactor_le` (T5). -/
theorem kf0BadFactor_le_gas_charge {d N ℓ : ℕ} [NeZero ℓ]
    (s m : ℕ) [NeZero m] {β ν p H : ℝ} (hβ : 0 ≤ β) (hν : 0 ≤ ν)
    (hp : 0 ≤ p) (hbudget : 8 * (p + H) ≤ β * ν)
    (h : EuclideanSpace ℝ (Fin N)) (B : Finset (Torus d m))
    (hB : B.Nonempty)
    (q : ↥(siteUnion (ℓ := ℓ) s m B) → SpinSphere N) :
    kf0BadFactor (siteUnion (ℓ := ℓ) s m B) s m (1 / 2) β ν h
      (fun _ _ => 0) B q ≤ Real.exp (-p - H * B.card) := by
  have hraw := kf0BadFactor_le (h := h) s m (1 / 2) (by norm_num)
    hβ hν (fun _ _ => 0) B q
  have hsource : sourceIn (siteUnion (ℓ := ℓ) s m B) (fun _ _ => 0) q = 0 := by
    simp [sourceIn]
  rw [hsource, Real.exp_zero, mul_one] at hraw
  have hcard : (1 : ℝ) ≤ (B.card : ℝ) := by
    exact_mod_cast Finset.one_le_card.mpr hB
  have hcard0 : (0 : ℝ) ≤ B.card := by positivity
  have hcharge : p + H ≤ β * ν / 8 := by linarith
  have hscale := mul_le_mul_of_nonneg_right hcharge hcard0
  have hpblock := mul_le_mul_of_nonneg_left hcard hp
  calc
    _ ≤ Real.exp (-(β * ν * (1 / 2 : ℝ) ^ 2 * B.card / 2)) := hraw
    _ ≤ Real.exp (-p - H * B.card) := by
      apply Real.exp_le_exp.mpr
      nlinarith

end Balaban.LargeField
