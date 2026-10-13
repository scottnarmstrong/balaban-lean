/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Green.FinalMassGreen
public import Balaban.Localization.DecoupledCovPrincipal
public import Balaban.Flow.StopIndex
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The inverse square root of the final reference operator (FINAL §3, package 4)

For `U = finalOp d L N₀ k v a` (see `Green/FinalMassGreen.lean`) the landed matrix
`Localization.sqrtMat U = π⁻¹ ∫₀^∞ t^{-1/2} (t + U)⁻¹ dt` is the principal inverse square root
`U^{-1/2}`: `sqrtMat U * sqrtMat U = U⁻¹` (`finalMass_sqrt_mul_self`).  Integrating the resolvent
bound `|(U + t)⁻¹_{xy}| ≤ 2/(g_* + t) exp(-r_* dist x y)` and using
`π⁻¹ ∫₀^∞ t^{-1/2} (g_* + t)⁻¹ dt = g_*^{-1/2}` gives
`|(U^{-1/2})_{xy}| ≤ 2 g_*^{-1/2} exp(-r_* dist x y)` (`finalMass_sqrt_decay`), uniformly in the
torus size, in `k` and in `v, a`.

As in `Green/FinalMassGreen.lean`: this is the real covariance of the reference operator.  The
identification with the Hessian of the physical final density (`FINAL-HESSIAN-BRIDGE`), the
complex chart, the cut-parameter family needed for exact locality, and the branch `k_f = 0` are NOT
proved here.  The last theorem restates the bounds at the stopping index of a running sequence.
-/

@[expose] public section

open Matrix MeasureTheory Set

namespace Balaban.Green

variable {d L N₀ k : ℕ} [NeZero N₀] [NeZero L]

private instance : Nonempty (L1Torus d N₀) := ⟨(0 : Torus d N₀)⟩

/-- `U` has resolvent entries for all `x ≥ 0` (the hypothesis `ResOK` of the landed square-root
calculus). -/
theorem finalMass_resOK (hd : 0 < d) (hk : 1 ≤ k) {v a : ℝ} (hv0 : 0 ≤ v)
    (hv1 : v ≤ 1) (ha1 : 1 / 2 ≤ a) (ha2 : a ≤ 2) (hmass : 7 / 8 * ((L : ℝ) ^ 2)⁻¹ < v) :
    Localization.ResOK (finalOp d L N₀ k v a) := by
  intro x hx
  have := (finalMass_resolvent_decay (L := L) (N₀ := N₀) (k := k) hd hk hv0 hv1 ha1 ha2 hmass
    hx).1
  rwa [add_comm] at this

/-- `sqrtMat U` is the principal inverse square root: `sqrtMat U * sqrtMat U = U⁻¹`. -/
theorem finalMass_sqrt_mul_self (hd : 0 < d) (hk : 1 ≤ k) {v a : ℝ} (hv0 : 0 ≤ v)
    (hv1 : v ≤ 1) (ha1 : 1 / 2 ≤ a) (ha2 : a ≤ 2) (hmass : 7 / 8 * ((L : ℝ) ^ 2)⁻¹ < v) :
    Localization.sqrtMat (finalOp d L N₀ k v a) * Localization.sqrtMat (finalOp d L N₀ k v a) =
      (finalOp d L N₀ k v a)⁻¹ :=
  Localization.sqrtMat_mul_self (finalMass_resOK hd hk hv0 hv1 ha1 ha2 hmass)

/-- **Inverse square root decay** (T5): `|(U^{-1/2})_{xy}| ≤ 2 g_*^{-1/2} exp(-r_* dist x y)`,
where `U^{-1/2} = sqrtMat U` is the Stieltjes integral `π⁻¹ ∫₀^∞ t^{-1/2} (t + U)⁻¹ dt`. -/
theorem finalMass_sqrt_decay (hd : 0 < d) (hk : 1 ≤ k) {v a : ℝ} (hv0 : 0 ≤ v)
    (hv1 : v ≤ 1) (ha1 : 1 / 2 ≤ a) (ha2 : a ≤ 2) (hmass : 7 / 8 * ((L : ℝ) ^ 2)⁻¹ < v)
    (x y : L1Torus d N₀) :
    ‖Localization.sqrtMat (finalOp d L N₀ k v a) x y‖ ≤
      2 / Real.sqrt (finalGap d L) * Real.exp (-finalRate d L * dist x y) := by
  have hL : 0 < L := Nat.pos_of_ne_zero (NeZero.ne L)
  have hg := finalGap_pos (d := d) hL
  have hA := finalMass_resOK (L := L) (N₀ := N₀) (k := k) hd hk hv0 hv1 ha1 ha2 hmass
  set B0 : ℝ := 2 * Real.exp (-finalRate d L * dist x y) with hB0
  have hB0nn : 0 ≤ B0 := by rw [hB0]; positivity
  unfold Localization.sqrtMat
  simp only [Matrix.smul_apply, smul_eq_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  unfold Localization.intMat
  have hint : Integrable (fun s : ℝ => B0 * (s ^ (-(1 / 2 : ℝ)) * (finalGap d L + s)⁻¹))
      (volume.restrict (Ioi (0 : ℝ))) :=
    (Localization.integrableOn_rpow_inv_add hg).const_mul B0
  have hbound := norm_integral_le_of_norm_le
    (f := fun s : ℝ => (((s ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) •
      ((s : ℂ) • (1 : Matrix (L1Torus d N₀) (L1Torus d N₀) ℂ) + finalOp d L N₀ k v a)⁻¹) x y)
    hint
    ((ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun s hs => by
      have hs0 : 0 < s := mem_Ioi.mp hs
      have h3 : 0 < s ^ (-(1 / 2 : ℝ)) := Real.rpow_pos_of_pos hs0 _
      simp only [Matrix.smul_apply, smul_eq_mul, norm_mul, Complex.norm_real,
        Real.norm_of_nonneg h3.le]
      have := (finalMass_resolvent_decay (L := L) (N₀ := N₀) (k := k) hd hk hv0 hv1 ha1 ha2
        hmass hs0.le).2 x y
      rw [add_comm] at this
      calc s ^ (-(1 / 2 : ℝ)) * ‖((s : ℂ) • (1 : Matrix (L1Torus d N₀) (L1Torus d N₀) ℂ) +
              finalOp d L N₀ k v a)⁻¹ x y‖
          ≤ s ^ (-(1 / 2 : ℝ)) * (B0 * (finalGap d L + s)⁻¹) := by
            refine mul_le_mul_of_nonneg_left (this.trans (le_of_eq ?_)) h3.le
            rw [hB0]; ring
        _ = _ := by ring))
  rw [integral_const_mul, Localization.integral_rpow_inv_add hg] at hbound
  have hpi : 0 < Real.pi := Real.pi_pos
  have hsq : 0 < Real.sqrt (finalGap d L) := Real.sqrt_pos.2 hg
  rw [abs_of_pos (by positivity)]
  calc 1 / Real.pi * ‖∫ s in Ioi (0 : ℝ), (((s ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) •
        ((s : ℂ) • (1 : Matrix (L1Torus d N₀) (L1Torus d N₀) ℂ) + finalOp d L N₀ k v a)⁻¹) x y‖
      ≤ 1 / Real.pi * (B0 * (Real.pi / Real.sqrt (finalGap d L))) := by gcongr
    _ = _ := by rw [hB0]; field_simp

/-- **Instance** (T6): `d = 3`, `L = 3`, `k = 1`, `a = 1`, any `v ∈ (7/72, 1]`, on the torus with
one point per direction (`N₀ = 1`): all hypotheses of the above hold. -/
theorem finalMass_instance {v : ℝ} (hv : 7 / 72 < v) (hv1 : v ≤ 1) :
    (0 : ℝ) ≤ v ∧ 7 / 8 * (((3 : ℕ) : ℝ) ^ 2)⁻¹ < v ∧ 0 < finalGap 3 3 ∧ 0 < finalRate 3 3 ∧
      IsCoercive (finalOp 3 3 1 1 v 1) (finalGap 3 3) ∧
      (∀ x y : L1Torus 3 1, ‖Localization.sqrtMat (finalOp 3 3 1 1 v 1) x y‖ ≤
        2 / Real.sqrt (finalGap 3 3) * Real.exp (-finalRate 3 3 * dist x y)) := by
  have hm : 7 / 8 * (((3 : ℕ) : ℝ) ^ 2)⁻¹ < v := by norm_num; linarith
  have hv0 : (0 : ℝ) ≤ v := by linarith
  refine ⟨hv0, hm, finalGap_pos (by norm_num), finalRate_pos (by norm_num),
    finalMass_isCoercive (by norm_num) hv0 hv1 (by norm_num) hm, fun x y => ?_⟩
  exact finalMass_sqrt_decay (by norm_num) le_rfl hv0 hv1 (by norm_num) (by norm_num) hm x y

/-- **At the stopping index** (T6): for a running sequence with `RunningHyp` and `0 < kStop h`,
the mass `v = n (kStop h)` is in the window, so the resolvent bound (F.4), the inverse bound and
the inverse square root bound hold at `k = kStop h` with constants depending only on `d, L`. -/
theorem finalMass_at_stop {β ν a ε : ℝ} {b n : ℕ → ℝ}
    (h : LargeField.RunningHyp d L β ν a ε b n) (hpos : 0 < LargeField.StopIndex.kStop h)
    (N₀ : ℕ) [NeZero N₀] :
    (∀ {t : ℝ}, 0 ≤ t →
      IsUnit (finalOp d L N₀ (LargeField.StopIndex.kStop h) (n (LargeField.StopIndex.kStop h)) a +
        (t : ℂ) • (1 : Matrix (L1Torus d N₀) (L1Torus d N₀) ℂ)) ∧
      ∀ x y : L1Torus d N₀,
        ‖(finalOp d L N₀ (LargeField.StopIndex.kStop h) (n (LargeField.StopIndex.kStop h)) a +
            (t : ℂ) • (1 : Matrix (L1Torus d N₀) (L1Torus d N₀) ℂ))⁻¹ x y‖ ≤
          2 / (finalGap d L + t) * Real.exp (-finalRate d L * dist x y)) ∧
    (∀ x y : L1Torus d N₀,
      ‖Localization.sqrtMat (finalOp d L N₀ (LargeField.StopIndex.kStop h)
          (n (LargeField.StopIndex.kStop h)) a) x y‖ ≤
        2 / Real.sqrt (finalGap d L) * Real.exp (-finalRate d L * dist x y)) := by
  have hd : 0 < d := by have := h.hd; omega
  have hmass := LargeField.StopIndex.kStop_spec h
  have hv1 := (LargeField.StopIndex.n_kStop_lt_one h hpos).le
  have hv0 : 0 ≤ n (LargeField.StopIndex.kStop h) := by
    have : (0 : ℝ) < 7 / 8 * ((L : ℝ) ^ 2)⁻¹ := by
      have : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
      positivity
    linarith
  have ha1 : 1 / 2 ≤ a := by linarith [h.ha1]
  have ha2 : a ≤ 2 := by linarith [h.ha2]
  exact ⟨fun ht => ⟨(finalMass_resolvent_decay hd hpos hv0 hv1 ha1 ha2 hmass ht).1,
      (finalMass_resolvent_decay hd hpos hv0 hv1 ha1 ha2 hmass ht).2⟩,
    finalMass_sqrt_decay hd hpos hv0 hv1 ha1 ha2 hmass⟩

end Balaban.Green
