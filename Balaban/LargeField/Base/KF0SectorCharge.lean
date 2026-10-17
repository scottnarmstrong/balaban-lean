/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, GPT-6-Sol (astra)
-/
module

public import Balaban.LargeField.Base.KF0BadCharge
import Balaban.Polymer.Bridge

/-!
# The bare bad-sector charge including its Gaussian determinant

Combines the raw Peierls factor in `KF0SectorSum` with its normalization ratio.
Each bad block has `s^d` sites, so the determinant upper bound costs
`((N-1)s^d/2) log[β(2d+ν)/(2π)]` per bad block. This is the normalization
term in `KF0B.md`, Round 6. The good-region integral in
`kf0SectorLint_le_peierls` remains and is not bounded here. In particular,
this is not yet a normalized component activity of the linked gas.
-/

@[expose] public section

open scoped Classical
open MeasureTheory

namespace Balaban.LargeField

/-- A union of `s`-blocks has exactly `s^d` sites per block. -/
theorem kf0_siteUnion_card {d s m : ℕ} [NeZero s] [NeZero m]
    (B : Finset (Torus d m)) :
    (siteUnion (ℓ := s * m) s m B).card = s ^ d * B.card := by
  change (Balaban.Polymer.siteSet d s m B).card = _
  exact Balaban.Polymer.card_siteSet d s m B

/-- The Gaussian normalization ratio and the pointwise bad-sector energy pay
`exp(-p-H|B|)` if `βν/8` exceeds the heavy charge plus the determinant cost
`((N-1)s^d/2) log[β(2d+ν)/(2π)]`. The bound holds for nonempty `B`. -/
theorem kf0SectorNorm_peierls_charge {d s m N : ℕ} [NeZero s] [NeZero m]
    {β ν p H : ℝ} (hβ : 0 < β) (hν : 0 < ν) (hp : 0 ≤ p)
    (hbudget : 8 * (p + H + (((N - 1) * s ^ d : ℕ) : ℝ) / 2 *
        Real.log (β * (2 * d + ν) / (2 * Real.pi))) ≤ β * ν)
    (B : Finset (Torus d m)) (hB : B.Nonempty) :
    kwNormRatio d (s * m) N β ν (siteUnion (ℓ := s * m) s m B) *
        Real.exp (-(β * ν / 8) * B.card) ≤
      Real.exp (-p - H * B.card) := by
  let D := siteUnion (ℓ := s * m) s m B
  let a : ℝ := β * (2 * d + ν) / (2 * Real.pi)
  let W : ℝ := (((N - 1) * s ^ d : ℕ) : ℝ) / 2 * Real.log a
  have ha : 0 < a := by
    dsimp [a]
    positivity
  have hD : ((N - 1) * D.card : ℕ) = ((N - 1) * s ^ d) * B.card := by
    dsimp [D]
    rw [kf0_siteUnion_card]
    ring
  have hpow : a ^ ((((N - 1) * D.card : ℕ) : ℝ) / 2) =
      Real.exp (W * B.card) := by
    rw [hD, Real.rpow_def_of_pos ha]
    congr 1
    dsimp [W]
    push_cast
    ring
  have hnorm : kwNormRatio d (s * m) N β ν D ≤ Real.exp (W * B.card) := by
    exact (kwNormRatio_le (d := d) (ℓ := s * m) N hβ hν D).trans_eq hpow
  have hcard : (1 : ℝ) ≤ B.card := by
    exact_mod_cast Finset.one_le_card.mpr hB
  have hcard0 : (0 : ℝ) ≤ B.card := by positivity
  have hmul : (p + H + W) * (B.card : ℝ) ≤ (β * ν / 8) * B.card := by
    apply mul_le_mul_of_nonneg_right _ hcard0
    dsimp [W, a]
    linarith
  have hpblock : p ≤ p * (B.card : ℝ) := by
    nlinarith
  have hexp : W * B.card + (-(β * ν / 8) * B.card) ≤
      -p - H * B.card := by
    nlinarith
  calc
    kwNormRatio d (s * m) N β ν D * Real.exp (-(β * ν / 8) * B.card)
      ≤ Real.exp (W * B.card) * Real.exp (-(β * ν / 8) * B.card) :=
        mul_le_mul_of_nonneg_right hnorm (Real.exp_nonneg _)
    _ = Real.exp (W * B.card + (-(β * ν / 8) * B.card)) := by
        rw [Real.exp_add]
    _ ≤ Real.exp (-p - H * B.card) := Real.exp_le_exp.mpr hexp

/-- The fixed bad-sector integral obeys the same determinant-inclusive heavy charge,
with the retained good-region integral displayed explicitly. This is the
`kf0SectorLint_le_peierls` estimate at radius `1/2`; it does not bound that
integral or construct the connected heavy activity. -/
theorem kf0SectorLint_le_charged_goodIntegral {d s m N : ℕ} [NeZero s] [NeZero m]
    {β ν p H : ℝ} (hβ : 0 < β) (hν : 0 < ν) (hp : 0 ≤ p)
    (hbudget : 8 * (p + H + (((N - 1) * s ^ d : ℕ) : ℝ) / 2 *
        Real.log (β * (2 * d + ν) / (2 * Real.pi))) ≤ β * ν)
    (h : EuclideanSpace ℝ (Fin N)) (hh : ‖h‖ = 1)
    (g : Torus d (s * m) → Fin N → ℝ)
    (B : Finset (Torus d m)) (hB : B.Nonempty) :
    kf0SectorLint s m (1 / 2) β ν h g B ≤
      ENNReal.ofReal (fullNorm d (s * m) N β ν) *
        ENNReal.ofReal (Real.exp (-p - H * B.card)) *
        ∫⁻ q, ENNReal.ofReal (Real.exp (sourceIn (siteUnion (ℓ := s * m) s m B) g q)) *
          kf0GoodInnerDropped (siteUnion (ℓ := s * m) s m B) hh β ν g q
          ∂sigmaIn (siteUnion (ℓ := s * m) s m B) := by
  let D := siteUnion (ℓ := s * m) s m B
  have hnorm0 : 0 ≤ kwNormRatio d (s * m) N β ν D := by
    unfold kwNormRatio
    exact (div_pos (kwSectorNorm_pos N hβ hν D) (fullNorm_pos N hβ hν)).le
  have hmul : ENNReal.ofReal (kwNormRatio d (s * m) N β ν D) *
      ENNReal.ofReal (Real.exp (-(β * ν / 8) * B.card)) ≤
      ENNReal.ofReal (Real.exp (-p - H * B.card)) := by
    rw [← ENNReal.ofReal_mul hnorm0]
    exact ENNReal.ofReal_le_ofReal (kf0SectorNorm_peierls_charge hβ hν hp hbudget B hB)
  have hraw := kf0SectorLint_le_peierls s m (1 / 2) (by norm_num) (by norm_num)
    hβ hν hh g B
  have hraw' : kf0SectorLint s m (1 / 2) β ν h g B ≤
      ENNReal.ofReal (fullNorm d (s * m) N β ν) *
        ENNReal.ofReal (kwNormRatio d (s * m) N β ν D) *
        ENNReal.ofReal (Real.exp (-(β * ν / 8) * B.card)) *
        (∫⁻ q, ENNReal.ofReal (Real.exp (sourceIn D g q)) *
          kf0GoodInnerDropped D hh β ν g q ∂sigmaIn D) := by
    simpa only [D, show -(β * ν * (1 / 2 : ℝ) ^ 2 * B.card / 2) =
        -(β * ν / 8) * B.card by ring] using hraw
  exact hraw'.trans (show
      ENNReal.ofReal (fullNorm d (s * m) N β ν) *
        ENNReal.ofReal (kwNormRatio d (s * m) N β ν D) *
        ENNReal.ofReal (Real.exp (-(β * ν / 8) * B.card)) *
        (∫⁻ q, ENNReal.ofReal (Real.exp (sourceIn D g q)) *
          kf0GoodInnerDropped D hh β ν g q ∂sigmaIn D) ≤ _ from by
    calc
      _ = ENNReal.ofReal (fullNorm d (s * m) N β ν) *
          (ENNReal.ofReal (kwNormRatio d (s * m) N β ν D) *
           ENNReal.ofReal (Real.exp (-(β * ν / 8) * B.card))) *
          (∫⁻ q, ENNReal.ofReal (Real.exp (sourceIn D g q)) *
            kf0GoodInnerDropped D hh β ν g q ∂sigmaIn D) := by ring
      _ ≤ ENNReal.ofReal (fullNorm d (s * m) N β ν) *
          ENNReal.ofReal (Real.exp (-p - H * B.card)) *
          (∫⁻ q, ENNReal.ofReal (Real.exp (sourceIn D g q)) *
            kf0GoodInnerDropped D hh β ν g q ∂sigmaIn D) := by
        exact mul_le_mul' (mul_le_mul' le_rfl hmul) le_rfl)


end Balaban.LargeField
