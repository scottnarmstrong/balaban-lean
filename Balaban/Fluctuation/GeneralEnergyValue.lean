/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.StepComplexThm31
public import Balaban.Fluctuation.Thm31CoeffA
public import Balaban.Fluctuation.GeneralEnergyMarks

/-!
# The value of the local energy term of a class member as a sum of coefficients

For a class member `C` the local energy term is `ℰ₁^{(k+1)}(z) = ∫₀¹ ⟨DΦ₁^C(sψ')[M_z ψ']⟩_{s} ds`
with the weight `exp(WoneC C)`, which carries the old energy.  The inherited energy therefore
enters through the activity (the exponent `WoneC C` is a sum of block-local terms `A' s`), and
through the marks (the derivative of `Φ₁^C` is the derivative for the zero class plus the label
terms of the old energy).

* `e1locC_eq_sum_gsumCoeff_of_input`: the shared core.  For any record `I : E1MarksC S C BS z` of
  any class, `ℰ₁(z) = ∑_T gsumCoeff μ Lab A y0 G T` with the bound of `interpCoeff_spec`.  The
  zero-class value theorem `e1Param_fibre_value_of_fields_fromTowerG` is this statement for
  `C = zeroClass`.
* `e1MarksC_class_of_zero_add_old`: the record of a class member from a zero-class record, an
  activity `A'` for the exponent `WoneC C`, and old-energy marks `G₁`; the family of marks is the
  zero marks followed by the old marks.
* `e1locC_class_value_of_zero_add_old`: the value `ℰ₁^C(z) = ∑_T c^C(T)` with
  `c^C = gsumCoeff μ Lab A' (zero anchors ⊕ old anchors) (zero marks ⊕ old marks)`.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Localization Balaban.Polymer Balaban.Multiscale Balaban.Background
  Balaban.SmallField.Def6 MeasureTheory

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}
  {S : StepSetting d L N₁ m₁ k N ϱ} {C : StepClass d L N₁ m₁ k N ϱ} {m₀ : ℕ}
  {BS : BlockSplit S m₀} {z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1)))}

open Classical in
/-- **The value of the local energy term as a sum of coefficients (shared core).**  For every
class member `C` and every record `I : E1MarksC S C BS z`, `ℰ₁^{(k+1)}(z) = ∑_T c(T)` with
`c = gsumCoeff μ I.Lab I.A I.y0 I.G`, and `‖c T‖ ≤ C_PE (∑ F₀ e^{-κ₀ d}) e^{-κ' d_Ext(T)}`. -/
theorem e1locC_eq_sum_gsumCoeff_of_input (I : E1MarksC S C BS z) :
    S.E1locC C z = ∑ T, gsumCoeff BS.μ I.Lab I.A I.y0 I.G T ∧
      ∀ T, ‖gsumCoeff BS.μ I.Lab I.A I.y0 I.G T‖ ≤ CPE d L I.Kc I.κH I.κ0 I.κ' *
          (∑ i, I.F0 i * Real.exp (-I.κ0 * I.Lab.dl (I.y0 i))) * Real.exp (-I.κ' * dExt T) :=
  interpCoeff_spec I

open Classical in
/-- **The record of a class member from a zero-class record, a new activity and old-energy
marks.**  Let `I₀` be a record for the zero class (labels, anchors `y0`, marks `G`).  Let `A'` be a
label activity on the same labels and constants with `WoneC C = ∑_y (A' s).H y` (the activity of
the exponent of `C`; it carries the old energy), and let `G₁` be marks anchored at `y1`, bounded
as the zero marks, block-local, holomorphic on the disc of `I₀`, whose sum added to the zero marks
is the integrand `DΦ₁^C(sψ')[M_z ψ']`.  Then the record `E1MarksC S C BS z` with activity `A'` and
the marks `I₀.G` followed by `G₁` exists, and its coefficients are `gsumCoeff` of this family. -/
theorem e1MarksC_class_of_zero_add_old
    (I₀ : E1MarksC S (zeroClass d L N₁ m₁ k N ϱ) BS z)
    {ι₁ : Type} [Fintype ι₁] (y1 : ι₁ → I₀.Lb) (F1 : ι₁ → ℝ) (hF1 : ∀ j, 0 < F1 j)
    (G₁ : ι₁ → ℂ → (∀ b, BS.Ωb b) → ℂ) (meas₁ : ∀ j u, Measurable (G₁ j u))
    (dep₁ : ∀ j u, DepOn (blocksOf m₀ (k + 1) Set.univ (I₀.Lab.ysite (y1 j))) (G₁ j u))
    (bound₁ : ∀ j u Φ, ‖G₁ j u Φ‖ ≤ F1 j * Real.exp (-I₀.κG * I₀.Lab.dl (y1 j)))
    (holG₁ : ∀ j Φ, DifferentiableOn ℂ (fun u => G₁ j u Φ) I₀.𝒰)
    (A' : ℂ → LabelAct I₀.Lab BS.Ωb I₀.εH I₀.κH I₀.κ0 I₀.Kc)
    (holA' : ∀ y Φ, DifferentiableOn ℂ (fun u => (A' u).H y Φ) I₀.𝒰)
    (hW' : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ᵐ x ∂S.nuFl,
      S.WoneC C s x = ∑ y, (A' (s : ℂ)).H y (BS.restr x))
    (hF' : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ᵐ x ∂S.nuFl,
      (fderiv ℂ (S.Phi1C C) ((s : ℂ) • S.shiftUC x)) (S.maskUC z (S.shiftUC x)) =
        ∑ i, I₀.G i (s : ℂ) (BS.restr x) + ∑ j, G₁ j (s : ℂ) (BS.restr x)) :
    ∃ I : E1MarksC S C BS z, I.𝒰 = I₀.𝒰 ∧ I.κG = I₀.κG ∧ I.κ' = I₀.κ' ∧ I.κH = I₀.κH ∧
      I.κ0 = I₀.κ0 ∧ I.Kc = I₀.Kc ∧ I.εH = I₀.εH ∧
      (∀ T, gsumCoeff BS.μ I.Lab I.A I.y0 I.G T = gsumCoeff BS.μ I₀.Lab A'
        (Sum.elim I₀.y0 y1) (Sum.elim I₀.G G₁) T) ∧
      CPE d L I.Kc I.κH I.κ0 I.κ' * (∑ i, I.F0 i * Real.exp (-I.κ0 * I.Lab.dl (I.y0 i))) =
        CPE d L I₀.Kc I₀.κH I₀.κ0 I₀.κ' *
          ((∑ i, I₀.F0 i * Real.exp (-I₀.κ0 * I₀.Lab.dl (I₀.y0 i))) +
            ∑ j, F1 j * Real.exp (-I₀.κ0 * I₀.Lab.dl (y1 j))) := by
  refine ⟨{
      Lb := I₀.Lb
      εH := I₀.εH
      κH := I₀.κH
      κ0 := I₀.κ0
      κ' := I₀.κ'
      Kc := I₀.Kc
      Lab := I₀.Lab
      ι := I₀.ι ⊕ ι₁
      nonempty := ⟨Sum.inl I₀.nonempty.some⟩
      κG := I₀.κG
      F0 := Sum.elim I₀.F0 F1
      hN := I₀.hN
      𝒰 := I₀.𝒰
      isOpen := I₀.isOpen
      seg := I₀.seg
      A := A'
      y0 := Sum.elim I₀.y0 y1
      G := Sum.elim I₀.G G₁
      meas := fun i u => by cases i with
        | inl i => exact I₀.meas i u
        | inr j => exact meas₁ j u
      dep := fun i u => by cases i with
        | inl i => exact I₀.dep i u
        | inr j => exact dep₁ j u
      bound := fun i u Φ => by cases i with
        | inl i => exact I₀.bound i u Φ
        | inr j => exact bound₁ j u Φ
      holA := holA'
      holG := fun i Φ => by cases i with
        | inl i => exact I₀.holG i Φ
        | inr j => exact holG₁ j Φ
      hκ0 := I₀.hκ0
      hKc := I₀.hKc
      hεpos := I₀.hεpos
      hF0 := fun i => by cases i with
        | inl i => exact I₀.hF0 i
        | inr j => exact hF1 j
      hκ' := I₀.hκ'
      hκG := I₀.hκG
      hκ := I₀.hκ
      hε := I₀.hε
      hW := hW'
      hF := fun s hs => by
        filter_upwards [hF' s hs] with x hx
        rw [hx, Fintype.sum_sum_type]
        rfl }, rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun T => rfl, ?_⟩
  rw [Fintype.sum_sum_type]
  rfl

open Classical in
/-- **The value of the local energy term of a class member as a sum of coefficients.**  Under the
hypotheses of `e1MarksC_class_of_zero_add_old`,
`ℰ₁^C(z) = ∑_T c^C(T)` with `c^C = gsumCoeff μ Lab A' (zero anchors ⊕ old anchors)
(zero marks ⊕ old marks)`, `A'` the activity of the exponent `WoneC C` (which contains the
inherited energy), and
`‖c^C T‖ ≤ C_PE (∑_i F₀ e^{-κ₀ d(y0 i)} + ∑_j F₁ e^{-κ₀ d(y1 j)}) e^{-κ' d_Ext(T)}`. -/
theorem e1locC_class_value_of_zero_add_old
    (I₀ : E1MarksC S (zeroClass d L N₁ m₁ k N ϱ) BS z)
    {ι₁ : Type} [Fintype ι₁] (y1 : ι₁ → I₀.Lb) (F1 : ι₁ → ℝ) (hF1 : ∀ j, 0 < F1 j)
    (G₁ : ι₁ → ℂ → (∀ b, BS.Ωb b) → ℂ) (meas₁ : ∀ j u, Measurable (G₁ j u))
    (dep₁ : ∀ j u, DepOn (blocksOf m₀ (k + 1) Set.univ (I₀.Lab.ysite (y1 j))) (G₁ j u))
    (bound₁ : ∀ j u Φ, ‖G₁ j u Φ‖ ≤ F1 j * Real.exp (-I₀.κG * I₀.Lab.dl (y1 j)))
    (holG₁ : ∀ j Φ, DifferentiableOn ℂ (fun u => G₁ j u Φ) I₀.𝒰)
    (A' : ℂ → LabelAct I₀.Lab BS.Ωb I₀.εH I₀.κH I₀.κ0 I₀.Kc)
    (holA' : ∀ y Φ, DifferentiableOn ℂ (fun u => (A' u).H y Φ) I₀.𝒰)
    (hW' : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ᵐ x ∂S.nuFl,
      S.WoneC C s x = ∑ y, (A' (s : ℂ)).H y (BS.restr x))
    (hF' : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ᵐ x ∂S.nuFl,
      (fderiv ℂ (S.Phi1C C) ((s : ℂ) • S.shiftUC x)) (S.maskUC z (S.shiftUC x)) =
        ∑ i, I₀.G i (s : ℂ) (BS.restr x) + ∑ j, G₁ j (s : ℂ) (BS.restr x)) :
    S.E1locC C z = ∑ T, gsumCoeff BS.μ I₀.Lab A' (Sum.elim I₀.y0 y1) (Sum.elim I₀.G G₁) T ∧
      ∀ T, ‖gsumCoeff BS.μ I₀.Lab A' (Sum.elim I₀.y0 y1) (Sum.elim I₀.G G₁) T‖ ≤
        CPE d L I₀.Kc I₀.κH I₀.κ0 I₀.κ' *
          ((∑ i, I₀.F0 i * Real.exp (-I₀.κ0 * I₀.Lab.dl (I₀.y0 i))) +
            ∑ j, F1 j * Real.exp (-I₀.κ0 * I₀.Lab.dl (y1 j))) * Real.exp (-I₀.κ' * dExt T) := by
  obtain ⟨I, -, -, hk', -, -, -, -, hc, hb⟩ := e1MarksC_class_of_zero_add_old I₀ y1 F1 hF1 G₁ meas₁
    dep₁ bound₁ holG₁ A' holA' hW' hF'
  obtain ⟨h1, h2⟩ := e1locC_eq_sum_gsumCoeff_of_input I
  refine ⟨by rw [h1]; exact Finset.sum_congr rfl fun T _ => hc T, fun T => ?_⟩
  rw [← hc T, ← hb, ← hk']
  exact h2 T

end Balaban.Fluctuation
