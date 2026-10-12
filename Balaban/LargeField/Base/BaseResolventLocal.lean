/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Base.BaseResolventRange
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Exact block-component locality of the base resolvent (BASE-KERNEL-3 Theorem 1.1)

If the nonzero-parameter bonds do not join a union `U` of complete first blocks to its complement,
then `A_e(s)` is a direct sum over `U` and `Uᶜ`; consequently the entries of the resolvent, the inverse
square root and the logarithm inside `U × U` depend only on the data (`s`, `α`, `e`) in `U`.
-/

@[expose] public section

namespace Balaban.LargeField.Base

open Matrix Finset

section Abstract

variable {κ : Type*} [Fintype κ] [DecidableEq κ] (P : κ → Prop)

/-- `M` is a direct sum over `P` and its complement. -/
def BlockDiag (M : Matrix κ κ ℂ) : Prop := ∀ p q, (P p ↔ ¬ P q) → M p q = 0

variable {P}

open Classical in
theorem mulVec_eq_of_agree {M M' : Matrix κ κ ℂ} (hagree : ∀ p q, P p → P q → M p q = M' p q)
    {w : κ → ℂ} (hw : ∀ q, ¬ P q → w q = 0) {p : κ} (hp : P p) :
    (M *ᵥ w) p = (M' *ᵥ w) p := by
  simp only [Matrix.mulVec, dotProduct]
  refine Finset.sum_congr rfl fun q _ => ?_
  by_cases hq : P q
  · rw [hagree p q hp hq]
  · rw [hw q hq]; simp

theorem mulVec_supp_P {M : Matrix κ κ ℂ} (hM : BlockDiag P M) {w : κ → ℂ}
    (hw : ∀ q, ¬ P q → w q = 0) {p : κ} (hp : ¬ P p) : (M *ᵥ w) p = 0 := by
  simp only [Matrix.mulVec, dotProduct]
  refine Finset.sum_eq_zero fun q _ => ?_
  by_cases hq : P q
  · rw [hM p q (by simp [hp, hq]), zero_mul]
  · rw [hw q hq, mul_zero]

theorem mulVec_supp_N {M : Matrix κ κ ℂ} (hM : BlockDiag P M) {w : κ → ℂ}
    (hw : ∀ q, P q → w q = 0) {p : κ} (hp : P p) : (M *ᵥ w) p = 0 := by
  simp only [Matrix.mulVec, dotProduct]
  refine Finset.sum_eq_zero fun q _ => ?_
  by_cases hq : P q
  · rw [hw q hq, mul_zero]
  · rw [hM p q (by simp [hp, hq]), zero_mul]

open Classical in
/-- The solution of `M v = f` with `f` supported on `P` is supported on `P`. -/
theorem inv_mulVec_supp {M : Matrix κ κ ℂ} (hM : BlockDiag P M) (hU : IsUnit M) {f : κ → ℂ}
    (hf : ∀ q, ¬ P q → f q = 0) (q : κ) (hq : ¬ P q) : (M⁻¹ *ᵥ f) q = 0 := by
  set v := M⁻¹ *ᵥ f with hv
  have hdet := (Matrix.isUnit_iff_isUnit_det _).1 hU
  have hMv : M *ᵥ v = f := by
    rw [hv, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec]
  set vN : κ → ℂ := fun p => if P p then 0 else v p with hvN
  set vP : κ → ℂ := fun p => if P p then v p else 0 with hvP
  have hsplit : v = vP + vN := by
    funext p; by_cases hp : P p <;> simp [hvP, hvN, hp]
  have hzero : M *ᵥ vN = 0 := by
    funext p
    by_cases hp : P p
    · exact mulVec_supp_N hM (fun q hq => by simp [hvN, hq]) hp
    · have h1 : (M *ᵥ v) p = (M *ᵥ vP) p + (M *ᵥ vN) p := by
        rw [hsplit, Matrix.mulVec_add]; rfl
      have h2 : (M *ᵥ vP) p = 0 := mulVec_supp_P hM (fun q hq => by simp [hvP, hq]) hp
      rw [hMv, hf p hp, h2] at h1
      simpa using h1.symm
  have hvN0 : vN = 0 := by
    have hinj := (Matrix.mulVec_injective_iff_isUnit (A := M)).2 hU
    exact hinj (by rw [hzero, Matrix.mulVec_zero])
  have := congrFun hvN0 q
  simpa [hvN, hq] using this

open Classical in
/-- **Inverses see only the `P`-block of the data.** -/
theorem inv_entry_congr {M M' : Matrix κ κ ℂ} (hM : BlockDiag P M) (hM' : BlockDiag P M')
    (hU : IsUnit M) (hU' : IsUnit M') (hagree : ∀ p q, P p → P q → M p q = M' p q)
    {p q : κ} (hp : P p) (hq : P q) : M⁻¹ p q = M'⁻¹ p q := by
  set f : κ → ℂ := Pi.single q 1 with hf
  have hf0 : ∀ r, ¬ P r → f r = 0 := fun r hr => by
    have : r ≠ q := fun h => hr (h ▸ hq)
    simp [hf, Pi.single_apply, this]
  have e1 : M⁻¹ p q = (M⁻¹ *ᵥ f) p := by
    rw [hf, Matrix.mulVec_single_one]; rfl
  have e2 : M'⁻¹ p q = (M'⁻¹ *ᵥ f) p := by
    rw [hf, Matrix.mulVec_single_one]; rfl
  rw [e1, e2]
  set v := M⁻¹ *ᵥ f with hv
  set v' := M'⁻¹ *ᵥ f with hv'
  have hv0 : ∀ r, ¬ P r → v r = 0 := inv_mulVec_supp hM hU hf0
  have hv'0 : ∀ r, ¬ P r → v' r = 0 := inv_mulVec_supp hM' hU' hf0
  have hMv : M *ᵥ v = f := by
    rw [hv, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hU),
      Matrix.one_mulVec]
  have hMv' : M' *ᵥ v' = f := by
    rw [hv', Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _
      ((Matrix.isUnit_iff_isUnit_det _).1 hU'), Matrix.one_mulVec]
  have hdiff : M *ᵥ (v - v') = 0 := by
    funext r
    by_cases hr : P r
    · rw [Matrix.mulVec_sub, Pi.sub_apply, hMv, mulVec_eq_of_agree hagree hv'0 hr, hMv']
      simp
    · have a1 : (M *ᵥ v) r = 0 := mulVec_supp_P hM hv0 hr
      have a2 : (M *ᵥ v') r = 0 := mulVec_supp_P hM hv'0 hr
      rw [Matrix.mulVec_sub]; simp [a1, a2]
  have hinj := (Matrix.mulVec_injective_iff_isUnit (A := M)).2 hU
  have : v - v' = 0 := hinj (by rw [hdiff, Matrix.mulVec_zero])
  have := congrFun this p
  simpa [sub_eq_zero] using this

theorem blockDiag_add_smul_one {M : Matrix κ κ ℂ} (hM : BlockDiag P M) (y : ℂ) :
    BlockDiag P (y • (1 : Matrix κ κ ℂ) + M) := by
  intro p q hpq
  have hne : p ≠ q := by
    rintro rfl
    by_cases h : P p
    · exact (hpq.1 h) h
    · exact h (hpq.2 h)
  simp [Matrix.add_apply, Matrix.one_apply, hne, hM p q hpq]

theorem resolvent_entry_congr {M M' : Matrix κ κ ℂ} (hM : BlockDiag P M) (hM' : BlockDiag P M')
    (hagree : ∀ p q, P p → P q → M p q = M' p q) {y : ℂ}
    (hU : IsUnit (y • (1 : Matrix κ κ ℂ) + M)) (hU' : IsUnit (y • (1 : Matrix κ κ ℂ) + M'))
    {p q : κ} (hp : P p) (hq : P q) :
    (y • (1 : Matrix κ κ ℂ) + M)⁻¹ p q = (y • (1 : Matrix κ κ ℂ) + M')⁻¹ p q := by
  refine inv_entry_congr (blockDiag_add_smul_one hM y) (blockDiag_add_smul_one hM' y) hU hU' ?_ hp hq
  intro a b ha hb
  simp [Matrix.add_apply, hagree a b ha hb]

open MeasureTheory Set Balaban.Localization in
theorem sqrtMat_entry_congr [Nonempty κ] {M M' : Matrix κ κ ℂ} (hM : BlockDiag P M)
    (hM' : BlockDiag P M') (hagree : ∀ p q, P p → P q → M p q = M' p q) (hR : ResOK M)
    (hR' : ResOK M') {p q : κ} (hp : P p) (hq : P q) : sqrtMat M p q = sqrtMat M' p q := by
  simp only [sqrtMat, intMat, Matrix.smul_apply]
  congr 1
  refine integral_congr_ae ?_
  refine (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun y hy => ?_)
  have hy0 : 0 ≤ y := le_of_lt hy
  simp only [Matrix.smul_apply]
  rw [resolvent_entry_congr hM hM' hagree (hR y hy0) (hR' y hy0) hp hq]

open MeasureTheory Set Balaban.Localization in
theorem logMat_entry_congr [Nonempty κ] {M M' : Matrix κ κ ℂ} (hM : BlockDiag P M)
    (hM' : BlockDiag P M') (hagree : ∀ p q, P p → P q → M p q = M' p q) (hR : ResOK M)
    (hR' : ResOK M') {p q : κ} (hp : P p) (hq : P q) : logMat M p q = logMat M' p q := by
  simp only [logMat, intMat, Matrix.neg_apply]
  congr 1
  refine integral_congr_ae ?_
  refine (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun y hy => ?_)
  have hy0 : 0 ≤ y := le_of_lt hy
  simp only [Matrix.sub_apply]
  rw [resolvent_entry_congr hM hM' hagree (hR y hy0) (hR' y hy0) hp hq]

end Abstract

end Balaban.LargeField.Base
