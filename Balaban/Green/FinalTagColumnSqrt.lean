/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Green.FinalTagColumn
public import Balaban.Green.FinalTaggedSqrt

/-!
# The final Stieltjes family has a column bound at the full row decay rate

Integrating the same-rate resolvent column bound removes the rate loss and the
extra ball constant from `taggedCfin_column_bound`. All mass-window, macro-scale
and parameter hypotheses are unchanged. This is a bound for the proposed reference
family, not a construction of the physical last integral.
-/

@[expose] public section

open Finset Matrix MeasureTheory Set

namespace Balaban.Green

variable {d L N₀ k M : ℕ} [NeZero N₀] [NeZero L] {v a : ℝ}

local notation "Gf" => taggedGfin Finset.univ (macBoxF d N₀ M)
  (fun z u => ((macChi d N₀ M z u : ℝ) : ℂ)) (macTags d N₀ M) (finalOp d L N₀ k v a)

variable (hd : 0 < d) (hk : 1 ≤ k) (hv0 : 0 ≤ v) (hv1 : v ≤ 1) (ha1 : 1 / 2 ≤ a) (ha2 : a ≤ 2)
  (hmass : 7 / 8 * ((L : ℝ) ^ 2)⁻¹ < v) (hM : 0 < M) {κ : ℝ} (hκ : 0 ≤ κ)
  (hMB : 4 * (pdB d L * Real.exp (pdH d * κ)) ≤ M) (hMκ : 8 * κ * 7 ^ d ≤ pdEps d L * M)
include hd hk hv0 hv1 ha1 ha2 hmass hM hκ hMB hMκ

/-- The Stieltjes family obeys the column estimate at every `0 ≤ r ≤ pdEps d L / 8`,
with the same bound as `taggedCfin_row_bound`. -/
theorem taggedCfin_column_bound_same_rate {s : MacIdx d N₀ M → ℂ} (hs : ∀ p, ‖s p‖ ≤ Real.exp κ)
    {r : ℝ} (hr0 : 0 ≤ r) (hr : r ≤ pdEps d L / 8) (y : L1Torus d N₀) :
    ∑ x, Real.exp (r * dist x y) * ‖taggedCfin d L N₀ k M v a s x y‖ ≤
      4 / 3 * (2 * Real.exp (pdH d * κ) * ballConst d (pdEps d L / 2)) /
        Real.sqrt (finalGap d L) := by
  have hL : 0 < L := Nat.pos_of_ne_zero (NeZero.ne L)
  have hg := finalGap_pos (d := d) hL
  set c0 : ℝ := 4 / 3 * (2 * Real.exp (pdH d * κ) * ballConst d (pdEps d L / 2)) with hc0
  have hint : ∀ x, Integrable (fun t : ℝ => Real.exp (r * dist x y) *
      ‖((t ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * Gf t s x y‖) (volume.restrict (Ioi (0 : ℝ))) :=
    fun x => (taggedCfin_integrable hd hk hv0 hv1 ha1 ha2 hmass hM hκ hMB hMκ hs x y).norm.const_mul _
  have hentry : ∀ x, ‖taggedCfin d L N₀ k M v a s x y‖ ≤
      (1 / Real.pi) * ∫ t in Ioi (0 : ℝ), ‖((t ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * Gf t s x y‖ := by
    intro x
    have : taggedCfin d L N₀ k M v a s x y = ((1 / Real.pi : ℝ) : ℂ) *
        ∫ t in Ioi (0 : ℝ), ((t ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * Gf t s x y := rfl
    rw [this, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) (by positivity)
  have hsum : ∑ x, Real.exp (r * dist x y) * ‖taggedCfin d L N₀ k M v a s x y‖ ≤
      (1 / Real.pi) * ∫ t in Ioi (0 : ℝ), ∑ x, Real.exp (r * dist x y) *
        ‖((t ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * Gf t s x y‖ := by
    rw [integral_finsetSum _ fun x _ => hint x, Finset.mul_sum]
    refine Finset.sum_le_sum fun x _ => ?_
    rw [integral_const_mul]
    calc _ ≤ Real.exp (r * dist x y) * ((1 / Real.pi) * ∫ t in Ioi (0 : ℝ),
          ‖((t ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * Gf t s x y‖) :=
          mul_le_mul_of_nonneg_left (hentry x) (Real.exp_pos _).le
      _ = _ := by ring
  have hI : ∫ t in Ioi (0 : ℝ), ∑ x, Real.exp (r * dist x y) *
        ‖((t ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * Gf t s x y‖ ≤ c0 * (Real.pi / Real.sqrt (finalGap d L)) := by
    rw [← Localization.integral_rpow_inv_add hg, ← integral_const_mul]
    refine integral_mono_of_nonneg ?_ ((Localization.integrableOn_rpow_inv_add hg).const_mul c0) ?_
    · exact Filter.Eventually.of_forall fun t => Finset.sum_nonneg fun x _ =>
        mul_nonneg (Real.exp_pos _).le (norm_nonneg _)
    · refine (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun t ht => ?_)
      have ht0 : 0 < t := mem_Ioi.1 ht
      have h3 : 0 < t ^ (-(1 / 2 : ℝ)) := Real.rpow_pos_of_pos ht0 _
      have hrow := taggedGfin_column_bound_same_rate hd hk hv0 hv1 ha1 ha2 hmass ht0.le hM hκ hMB hMκ hr0 hr hs y
      have : ∑ x, Real.exp (r * dist x y) * ‖((t ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * Gf t s x y‖ =
          t ^ (-(1 / 2 : ℝ)) * ∑ x, Real.exp (r * dist x y) * ‖Gf t s x y‖ := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg h3.le]; ring
      beta_reduce
      rw [this]
      calc _ ≤ t ^ (-(1 / 2 : ℝ)) * (4 / 3 * taggedA0 d L κ t) :=
            mul_le_mul_of_nonneg_left hrow h3.le
        _ = _ := by unfold taggedA0; rw [hc0, div_eq_mul_inv]; ring
  have hpi : 0 < Real.pi := Real.pi_pos
  calc _ ≤ _ := hsum
    _ ≤ (1 / Real.pi) * (c0 * (Real.pi / Real.sqrt (finalGap d L))) :=
        mul_le_mul_of_nonneg_left hI (by positivity)
    _ = _ := by field_simp

end Balaban.Green
