/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.LocalClassDensityFamilyAct
public import Balaban.Fluctuation.Prop33Level

/-!
# Decay bookkeeping of the families (M1), (M2) for a class of index `1`

The label expansions of an inherited label are made on the cover of the index `C.m₀` of the class:
their bounds decay in `d^cov_{C.m₀}(Y) = treeLenCov S.G' C.m₀ Y`, while the labels of (M1) and (M2)
are domains of the block index `1` with sizes `d^cov_1`.  For a class of index `C.m₀ = 1` the two
sizes agree on the step (`treeLenCov_eq_treeLenCovOne`), and the size of a bridge exceeds that of
its domain by at most `c_Br` (`treeLenCovOne_bridge_le`):

* `classActivity_hnumH_of_index_one`: the bound condition `hnumH` of `classActivityFamily_labelAct`
  (and of `e0CoeffFamily_class_fromTower_of_families`) follows from the resummation over the labels
  of each domain, `∑_{τ : Y ∈ polyDom τ} 2 E₀ e^{-κ₀ d(X_τ)} ≤ ε_C`, when `κ_H ≤ 2κ_dec`;
* `classMarks_bound_of_index_one`: the marks of `classMarksFamily_fields` satisfy the bound of (M2)
  with `F1 q = |β| β⁻¹ E₀ e^{2κ_dec c_Br} e^{-κ₀ d(X_τ)} / b` and the size of the bridge label
  `𝗱(bridge 1 z Y)`, for `κ_G ≤ 2κ_dec`: `F1` no longer absorbs `e^{κ_G 𝗱(y1)}`.

For a class of index `C.m₀ > 1` the comparison is not available: a single cell of index `C.m₀` has
size `0` at the index `C.m₀` (`treeLenCovOne_box`) and positive size at the index `1`.
-/

@[expose] public section

namespace Balaban.Fluctuation

open MeasureTheory Balaban Balaban.Localization Balaban.Multiscale
  Balaban.Background Balaban.SmallField Balaban.Polymer Finset

section Decay

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}
variable (S : StepSetting d L N₁ m₁ k N ϱ)

open Classical in
/-- **The bound condition of the activity family for a class of index `1`.**  If `C.m₀ = 1`,
`κ_H ≤ 2κ_dec`, `E₀ ≥ 0` and on every domain `Y` of `𝒴C` the label sum
`∑_{τ : Y ∈ polyDom τ} 2 E₀ e^{-κ₀ d(X_τ)}` is at most `ε_C`, then
`∑_{τ : Y ∈ polyDom τ} 2 E₀ e^{-κ₀ d(X_τ) - 2κ_dec d^cov_{C.m₀}(Y)} ≤ ε_C e^{-κ_H d^cov_1(Y)}`
(the hypothesis `hnumH` of `classActivityFamily_labelAct`). -/
theorem classActivity_hnumH_of_index_one {ι : Type*} [Fintype ι]
    (C : StepClass d L N₁ m₁ k N ϱ) (hC1 : C.m₀ = 1)
    (jL : ι → ℕ) (XL : ι → Set (CTorus d L N₁ m₁ (k + 1)))
    (X₁f : ι → Finset (CTorus d L N₁ m₁ (k + 1))) (𝒦X : ι → Set (CTorus d L N₁ m₁ (k + 1)))
    (𝒴C : Finset (Set (CTorus d L N₁ m₁ (k + 1))))
    {E₀ κ₀ κdec κH εC : ℝ} (hE₀ : 0 ≤ E₀) (hκH : κH ≤ 2 * κdec)
    (hres : ∀ Y ∈ 𝒴C, (∑ τ, if Y ∈ polyDom S.G' (X₁f τ) C.m₀ (jL τ) (𝒦X τ) then
        2 * E₀ * Real.exp (-κ₀ * treeLenCovOne C.m₀ (jL τ) (XL τ)) else 0) ≤ εC) :
    ∀ Y ∈ 𝒴C, (∑ τ, if Y ∈ polyDom S.G' (X₁f τ) C.m₀ (jL τ) (𝒦X τ) then
        2 * E₀ * Real.exp (-κ₀ * treeLenCovOne C.m₀ (jL τ) (XL τ) -
          2 * κdec * treeLenCov S.G' C.m₀ Y)
      else 0) ≤ εC * Real.exp (-κH * treeLenCovOne 1 (k + 1) Y) := by
  intro Y hY
  have hd : treeLenCov S.G' C.m₀ Y = treeLenCovOne 1 (k + 1) Y := by
    rw [hC1]; exact treeLenCov_eq_treeLenCovOne S.hG' 1 Y
  have hd0 := treeLenCovOne_nonneg (m₁ := m₁) (N₁ := N₁) (L := L) (d := d) (K := k + 1) 1 (k + 1) Y
  have hexp : Real.exp (-(2 * κdec) * treeLenCovOne 1 (k + 1) Y) ≤
      Real.exp (-κH * treeLenCovOne 1 (k + 1) Y) :=
    Real.exp_le_exp.2 (by nlinarith)
  calc (∑ τ, if Y ∈ polyDom S.G' (X₁f τ) C.m₀ (jL τ) (𝒦X τ) then
          2 * E₀ * Real.exp (-κ₀ * treeLenCovOne C.m₀ (jL τ) (XL τ) -
            2 * κdec * treeLenCov S.G' C.m₀ Y)
        else 0)
      ≤ ∑ τ, (if Y ∈ polyDom S.G' (X₁f τ) C.m₀ (jL τ) (𝒦X τ) then
          2 * E₀ * Real.exp (-κ₀ * treeLenCovOne C.m₀ (jL τ) (XL τ)) else 0) *
          Real.exp (-κH * treeLenCovOne 1 (k + 1) Y) := by
        refine Finset.sum_le_sum fun τ _ => ?_
        split_ifs
        · rw [hd, sub_eq_add_neg, Real.exp_add]
          have h0 : 0 ≤ 2 * E₀ * Real.exp (-κ₀ * treeLenCovOne C.m₀ (jL τ) (XL τ)) := by positivity
          have h2 : Real.exp (-(2 * κdec * treeLenCovOne 1 (k + 1) Y)) ≤
              Real.exp (-κH * treeLenCovOne 1 (k + 1) Y) := by
            rw [show -(2 * κdec * treeLenCovOne 1 (k + 1) Y) =
              -(2 * κdec) * treeLenCovOne 1 (k + 1) Y by ring]
            exact hexp
          have h3 := mul_le_mul_of_nonneg_left h2 h0
          calc 2 * E₀ * (Real.exp (-κ₀ * treeLenCovOne C.m₀ (jL τ) (XL τ)) *
                Real.exp (-(2 * κdec * treeLenCovOne 1 (k + 1) Y)))
              = 2 * E₀ * Real.exp (-κ₀ * treeLenCovOne C.m₀ (jL τ) (XL τ)) *
                Real.exp (-(2 * κdec * treeLenCovOne 1 (k + 1) Y)) := by ring
            _ ≤ _ := h3
        · rw [zero_mul]
    _ = (∑ τ, if Y ∈ polyDom S.G' (X₁f τ) C.m₀ (jL τ) (𝒦X τ) then
          2 * E₀ * Real.exp (-κ₀ * treeLenCovOne C.m₀ (jL τ) (XL τ)) else 0) *
          Real.exp (-κH * treeLenCovOne 1 (k + 1) Y) := by rw [Finset.sum_mul]
    _ ≤ εC * Real.exp (-κH * treeLenCovOne 1 (k + 1) Y) :=
        mul_le_mul_of_nonneg_right (hres Y hY) (Real.exp_pos _).le

open Classical in
/-- **The bound of the inherited marks for a class of index `1`, in the form of (M2).**  If
`C.m₀ = 1`, `κ_dec ≥ 0`, `κ_G ≤ 2κ_dec`, the domains of the labels are domains of `𝒟_{k+1}` for
the index `1`, and the marks `G₁` of the rooted pairs satisfy the bound of
`classMarksFamily_fields`, then
`‖G₁ θ q u Φ‖ ≤ F1 q · e^{-κ_G d^cov_1(bridge 1 z Y)}` with
`F1 q = |β| β⁻¹ E₀ e^{2κ_dec c_Br} e^{-κ₀ d(X_τ)} / b`, which does not grow with the size of the
label (`treeLenCovOne_bridge_le`). -/
theorem classMarks_bound_of_index_one {ι : Type*} [Fintype ι]
    (C : StepClass d L N₁ m₁ k N ϱ) (hC1 : C.m₀ = 1) (hN1 : L ^ 1 ∣ N₁)
    (jL : ι → ℕ) (XL : ι → Set (CTorus d L N₁ m₁ (k + 1)))
    (X₁f : ι → Finset (CTorus d L N₁ m₁ (k + 1))) (𝒦X : ι → Set (CTorus d L N₁ m₁ (k + 1)))
    (hYdj : ∀ τ, ∀ Y ∈ polyDom S.G' (X₁f τ) C.m₀ (jL τ) (𝒦X τ), IsDj 1 (k + 1) Y)
    (z : RootIdx d L N₁ m₁ (k + 1)) (hp : 0 < S.p₁)
    {E₀ β κ₀ κdec κG bb : ℝ} (hβ : 0 < β) (hE₀ : 0 ≤ E₀) (hbb : 0 < bb) (hκdec : 0 ≤ κdec)
    (hκG : κG ≤ 2 * κdec)
    (G₁ : physParam N S →
      {q // q ∈ markedIdx (fun _ => (Set.univ : Set (CTorus d L N₁ m₁ (k + 1))))
        (fun τ => polyDom S.G' (X₁f τ) C.m₀ (jL τ) (𝒦X τ)) z} →
      ℂ → (∀ b, (S.blockSplit 1 hp).Ωb b) → ℂ)
    (hbd : ∀ θ q u Φ, ‖G₁ θ q u Φ‖ ≤ ‖(β : ℂ)‖ * ((β⁻¹ * E₀) *
      Real.exp (-κ₀ * treeLenCovOne C.m₀ (jL q.1.1) (XL q.1.1) -
        2 * κdec * treeLenCov S.G' C.m₀ q.1.2) / bb)) :
    ∀ θ q u Φ, ‖G₁ θ q u Φ‖ ≤
      (‖(β : ℂ)‖ * (β⁻¹ * E₀) * Real.exp (2 * κdec * cBr d L) *
        Real.exp (-κ₀ * treeLenCovOne C.m₀ (jL q.1.1) (XL q.1.1)) / bb) *
        Real.exp (-κG * treeLenCovOne 1 (k + 1) (bridge 1 z q.1.2)) := by
  intro θ q u Φ
  have hq : (q.1.1, q.1.2) ∈ markedIdx (fun _ => (Set.univ : Set (CTorus d L N₁ m₁ (k + 1))))
      (fun τ => polyDom S.G' (X₁f τ) C.m₀ (jL τ) (𝒦X τ)) z := q.2
  have hYdj' := hYdj q.1.1 q.1.2 (mem_markedIdx.1 hq).1
  have hkey : ∀ Y : Set (CTorus d L N₁ m₁ (k + 1)),
      treeLenCov S.G' C.m₀ Y = treeLenCovOne 1 (k + 1) Y := fun Y => by
    rw [hC1]; exact treeLenCov_eq_treeLenCovOne S.hG' 1 Y
  have hd := hkey q.1.2
  have hbr := treeLenCovOne_bridge_le hN1 z hYdj'
  have hb0 := treeLenCovOne_nonneg (m₁ := m₁) (N₁ := N₁) (L := L) (d := d) (K := k + 1) 1 (k + 1)
    (bridge 1 z q.1.2)
  have hexp : Real.exp (-κ₀ * treeLenCovOne C.m₀ (jL q.1.1) (XL q.1.1) -
      2 * κdec * treeLenCov S.G' C.m₀ q.1.2) ≤
      Real.exp (2 * κdec * cBr d L) *
        Real.exp (-κ₀ * treeLenCovOne C.m₀ (jL q.1.1) (XL q.1.1)) *
        Real.exp (-κG * treeLenCovOne 1 (k + 1) (bridge 1 z q.1.2)) := by
    rw [← Real.exp_add, ← Real.exp_add, hd]
    refine Real.exp_le_exp.2 ?_
    nlinarith
  have hc : 0 ≤ ‖(β : ℂ)‖ * (β⁻¹ * E₀) := mul_nonneg (norm_nonneg _)
    (mul_nonneg (inv_nonneg.2 hβ.le) hE₀)
  calc ‖G₁ θ q u Φ‖ ≤ ‖(β : ℂ)‖ * ((β⁻¹ * E₀) *
        Real.exp (-κ₀ * treeLenCovOne C.m₀ (jL q.1.1) (XL q.1.1) -
          2 * κdec * treeLenCov S.G' C.m₀ q.1.2) / bb) := hbd θ q u Φ
    _ = ‖(β : ℂ)‖ * (β⁻¹ * E₀) * Real.exp (-κ₀ * treeLenCovOne C.m₀ (jL q.1.1) (XL q.1.1) -
          2 * κdec * treeLenCov S.G' C.m₀ q.1.2) / bb := by ring
    _ ≤ ‖(β : ℂ)‖ * (β⁻¹ * E₀) * (Real.exp (2 * κdec * cBr d L) *
          Real.exp (-κ₀ * treeLenCovOne C.m₀ (jL q.1.1) (XL q.1.1)) *
          Real.exp (-κG * treeLenCovOne 1 (k + 1) (bridge 1 z q.1.2))) / bb :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hexp hc) hbb.le
    _ = _ := by ring

end Decay

end Balaban.Fluctuation
