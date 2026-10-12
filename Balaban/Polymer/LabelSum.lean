/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Polymer.MarkedCubes
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Sums of cube labels and of label activities

Two families of labels at the same scale `m₀`, level `j` and region `Ω` are combined into the labels
on the sum type `Lb₀ ⊕ Lb₁` (`CubeLabels.sum`).  Label activities on the two families, with the same
decay rates `κH`, `κ0`, combine into one activity on the sum
(`LabelAct.sum`, constants `max ε₀ ε₁`, `K₀ + K₁`), whose total over the labels is the sum of the
two totals.  Also: the negative of an activity, and the monotonicity of `LabelAct` in its
parameters (`εH` up, `κH` down, `κ0` up, `Kc` up).
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Localization Balaban.Polymer MeasureTheory

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {m₀ j : ℕ} {Ω : Set (CTorus d L N₁ m₁ K)}

section Sum

variable {Lb₀ Lb₁ : Type*}

/-- The labels on the sum type: `ysite`, `dl` by cases; `isDj`, `meets`, `size` by cases. -/
def CubeLabels.sum (Lab₀ : CubeLabels m₀ j Ω Lb₀) (Lab₁ : CubeLabels m₀ j Ω Lb₁) :
    CubeLabels m₀ j Ω (Lb₀ ⊕ Lb₁) where
  ysite := Sum.elim Lab₀.ysite Lab₁.ysite
  dl := Sum.elim Lab₀.dl Lab₁.dl
  isDj := fun y => by cases y with
    | inl y => exact Lab₀.isDj y
    | inr y => exact Lab₁.isDj y
  meets := fun y => by cases y with
    | inl y => exact Lab₀.meets y
    | inr y => exact Lab₁.meets y
  size := fun y => by cases y with
    | inl y => exact Lab₀.size y
    | inr y => exact Lab₁.size y

omit [NeZero N₁] [NeZero L] in
@[simp] theorem CubeLabels.sum_ysite_inl (Lab₀ : CubeLabels m₀ j Ω Lb₀)
    (Lab₁ : CubeLabels m₀ j Ω Lb₁) (y : Lb₀) :
    (Lab₀.sum Lab₁).ysite (Sum.inl y) = Lab₀.ysite y := rfl

omit [NeZero N₁] [NeZero L] in
@[simp] theorem CubeLabels.sum_ysite_inr (Lab₀ : CubeLabels m₀ j Ω Lb₀)
    (Lab₁ : CubeLabels m₀ j Ω Lb₁) (y : Lb₁) :
    (Lab₀.sum Lab₁).ysite (Sum.inr y) = Lab₁.ysite y := rfl

omit [NeZero N₁] [NeZero L] in
@[simp] theorem CubeLabels.sum_dl_inl (Lab₀ : CubeLabels m₀ j Ω Lb₀)
    (Lab₁ : CubeLabels m₀ j Ω Lb₁) (y : Lb₀) :
    (Lab₀.sum Lab₁).dl (Sum.inl y) = Lab₀.dl y := rfl

omit [NeZero N₁] [NeZero L] in
@[simp] theorem CubeLabels.sum_dl_inr (Lab₀ : CubeLabels m₀ j Ω Lb₀)
    (Lab₁ : CubeLabels m₀ j Ω Lb₁) (y : Lb₁) :
    (Lab₀.sum Lab₁).dl (Sum.inr y) = Lab₁.dl y := rfl

variable [Fintype Lb₀] [Fintype Lb₁]
  {Lab₀ : CubeLabels m₀ j Ω Lb₀} {Lab₁ : CubeLabels m₀ j Ω Lb₁}
  {Ωb : CubeB (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ j Ω → Type*}
  [∀ b, MeasurableSpace (Ωb b)] {ε₀ ε₁ κH κ0 K₀ K₁ : ℝ}

/-- **The sum of two label activities** with the same rates: constants `max ε₀ ε₁`, `K₀ + K₁`. -/
noncomputable def LabelAct.sum (A₀ : LabelAct Lab₀ Ωb ε₀ κH κ0 K₀)
    (A₁ : LabelAct Lab₁ Ωb ε₁ κH κ0 K₁) :
    LabelAct (Lab₀.sum Lab₁) Ωb (max ε₀ ε₁) κH κ0 (K₀ + K₁) where
  H := Sum.elim A₀.H A₁.H
  meas := fun y => by cases y with
    | inl y => exact A₀.meas y
    | inr y => exact A₁.meas y
  dep := fun y => by cases y with
    | inl y => exact A₀.dep y
    | inr y => exact A₁.dep y
  bound := fun y Φ => by
    cases y with
    | inl y =>
      exact (A₀.bound y Φ).trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
        (Real.exp_nonneg _))
    | inr y =>
      exact (A₁.bound y Φ).trans (mul_le_mul_of_nonneg_right (le_max_right _ _)
        (Real.exp_nonneg _))
  entropy := fun b => by
    rw [Fintype.sum_sum_type]
    exact add_le_add (A₀.entropy b) (A₁.entropy b)

@[simp] theorem LabelAct.sum_H_inl (A₀ : LabelAct Lab₀ Ωb ε₀ κH κ0 K₀)
    (A₁ : LabelAct Lab₁ Ωb ε₁ κH κ0 K₁) (y : Lb₀) :
    (A₀.sum A₁).H (Sum.inl y) = A₀.H y := rfl

@[simp] theorem LabelAct.sum_H_inr (A₀ : LabelAct Lab₀ Ωb ε₀ κH κ0 K₀)
    (A₁ : LabelAct Lab₁ Ωb ε₁ κH κ0 K₁) (y : Lb₁) :
    (A₀.sum A₁).H (Sum.inr y) = A₁.H y := rfl

/-- The total of the sum is the sum of the totals. -/
theorem LabelAct.sum_total (A₀ : LabelAct Lab₀ Ωb ε₀ κH κ0 K₀)
    (A₁ : LabelAct Lab₁ Ωb ε₁ κH κ0 K₁) (Φ : ∀ b, Ωb b) :
    ∑ y, (A₀.sum A₁).H y Φ = ∑ y, A₀.H y Φ + ∑ y, A₁.H y Φ :=
  Fintype.sum_sum_type _

end Sum

section Neg

variable {Lb : Type*} [Fintype Lb] {Lab : CubeLabels m₀ j Ω Lb}
  {Ωb : CubeB (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ j Ω → Type*}
  [∀ b, MeasurableSpace (Ωb b)] {εH κH κ0 Kc : ℝ}

/-- The negative of a label activity, with the same constants. -/
noncomputable def LabelAct.neg (A : LabelAct Lab Ωb εH κH κ0 Kc) :
    LabelAct Lab Ωb εH κH κ0 Kc where
  H y Φ := -A.H y Φ
  meas y := (A.meas y).neg
  dep y Φ Φ' h := by simp only [A.dep y Φ Φ' h]
  bound y Φ := by rw [norm_neg]; exact A.bound y Φ
  entropy := A.entropy

@[simp] theorem LabelAct.neg_H (A : LabelAct Lab Ωb εH κH κ0 Kc) (y : Lb) (Φ : ∀ b, Ωb b) :
    A.neg.H y Φ = -A.H y Φ := rfl

/-- **Monotonicity.**  The activity bound weakens when `εH` increases or `κH` decreases (the sizes
`𝗱` are nonnegative by `CubeLabels.dl_nonneg`); the entropy bound weakens when `κ0` increases (as
`𝗱 ≥ 0`) or `Kc` increases (`0 ≤ εH` is needed to compare the
bounds). -/
noncomputable def LabelAct.mono (A : LabelAct Lab Ωb εH κH κ0 Kc) {ε' κH' κ0' Kc' : ℝ}
    (h0 : 0 ≤ εH) (hε : εH ≤ ε') (hκH : κH' ≤ κH) (hκ0 : κ0 ≤ κ0') (hK : Kc ≤ Kc') :
    LabelAct Lab Ωb ε' κH' κ0' Kc' where
  H := A.H
  meas := A.meas
  dep := A.dep
  bound y Φ := by
    refine (A.bound y Φ).trans ?_
    have hd := Lab.dl_nonneg y
    have hpos : 0 ≤ Real.exp (-κH * Lab.dl y) := Real.exp_nonneg _
    calc εH * Real.exp (-κH * Lab.dl y) ≤ ε' * Real.exp (-κH * Lab.dl y) :=
          mul_le_mul_of_nonneg_right hε hpos
      _ ≤ ε' * Real.exp (-κH' * Lab.dl y) := by
          have h0 : 0 ≤ ε' := h0.trans hε
          exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (by nlinarith)) h0
  entropy b := by
    refine le_trans (Finset.sum_le_sum fun y _ => ?_) ((A.entropy b).trans hK)
    split_ifs
    · exact Real.exp_le_exp.2 (by nlinarith [Lab.dl_nonneg y])
    · exact le_rfl

end Neg

end Balaban.Fluctuation
