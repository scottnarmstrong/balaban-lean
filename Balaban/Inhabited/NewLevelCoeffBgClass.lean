/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.NewLevelCoeffBg
public import Balaban.Fluctuation.MarkedCommonLabels

/-!
# The coefficient of the new level of a class as a formula on a background set (`NewLevelCoeffBgClass`)

The activity family of a class with inherited labels is `commonAct (A₀.sum (commonAct A_C …))` on
the common labels `commonLabels (Lab₀.sum (commonLabels Lab_C …)) …` (`classActivityFamily_sum_fields`,
`classE1_M1_of_family`): the zero-class activities `A₀` on the labels `Lab₀`, the activities `A_C`
of the inherited energy on the labels `Lab_C`, both extended by zero to the root-union labels.  On a
background generating set `Gb` the coefficient of the new level is the formula `newLevelCoeffBg` of
the activity functions recomputed on `Gb`, combined in the same way (`classActFun`).

* `classActFun`: the activity function of the class on the common labels, from the activity
  functions `H₀` on `Lab₀` and `H₁` on `Lab_C` (zero on the root-union labels);
* `commonAct_sum_H`: the activities of the bundled family of the class are `classActFun` of the
  activities of its two parts;
* `newLevelCoeffBg_class_eq_of_agree`: **the replacement identity of the coefficient of a class,
  reduced to its parts** (P3 p. 79): the coefficient of the step (determinant part plus `gsumCoeff`
  of the class family) equals the formula `newLevelCoeffBg` on `Gb` with `classActFun H₀ H₁` when the
  determinant parts agree, the zero-class activities and the inherited activities agree on the labels
  inside `T`, and the marks agree on the anchors inside `T` (`newLevelCoeffBg_eq_of_agree`).
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Localization Balaban.Polymer Balaban.Multiscale MeasureTheory

section Comb

variable {d L N₁ m₁ k : ℕ} [NeZero L] [NeZero N₁]
  {Ωb : CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) 1 (k + 1) Set.univ → Type*}
  {E : Type*} {Lb₀ Lb₁ R₁ R₂ : Type*}

/-- **The activity function of a class on its common labels**: `H₀` on the zero-class labels, `H₁`
on the labels of the inherited energy, `0` on the root-union labels of both. -/
def classActFun (H₀ : E → ℂ → Lb₀ → (∀ b, Ωb b) → ℂ) (H₁ : E → ℂ → Lb₁ → (∀ b, Ωb b) → ℂ) :
    E → ℂ → (Lb₀ ⊕ (Lb₁ ⊕ R₁)) ⊕ R₂ → (∀ b, Ωb b) → ℂ :=
  fun θ u => Sum.elim (Sum.elim (H₀ θ u) (Sum.elim (H₁ θ u) fun _ _ => 0)) fun _ _ => 0

end Comb

section Bundled

variable {d L N₁ m₁ k : ℕ} [NeZero L] [NeZero N₁]
  {Ωb : CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) 1 (k + 1) Set.univ → Type*}
  [∀ b, MeasurableSpace (Ωb b)] {E : Type*}
  {Lb₀ Lb₁ β₁ β₂ : Type*} [Fintype Lb₀] [Fintype Lb₁] [Fintype β₁] [Fintype β₂]
  {Lab₀ : CubeLabels (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) 1 (k + 1) Set.univ Lb₀}
  {Lab₁ : CubeLabels (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) 1 (k + 1) Set.univ Lb₁}
  {ε₀ ε₁ κH κ0 K₀ K₁ : ℝ}

/-- **The activities of the bundled family of a class** are `classActFun` of the activities of
its two parts. -/
theorem commonAct_sum_H (A₀ : E → ℂ → LabelAct Lab₀ Ωb ε₀ κH κ0 K₀)
    (A₁ : E → ℂ → LabelAct Lab₁ Ωb ε₁ κH κ0 K₁) (hN : L ^ 1 ∣ N₁) (hL : 2 ≤ L)
    (reads₁ : β₁ → Set (CTorus d L N₁ m₁ (k + 1)))
    (dom₁ : β₁ → Finset (Set (CTorus d L N₁ m₁ (k + 1))))
    (hdom₁ : ∀ b, ∀ Y ∈ dom₁ b, IsDj 1 (k + 1) Y)
    (reads : β₂ → Set (CTorus d L N₁ m₁ (k + 1)))
    (dom : β₂ → Finset (Set (CTorus d L N₁ m₁ (k + 1))))
    (hdom : ∀ b, ∀ Y ∈ dom b, IsDj 1 (k + 1) Y) (hε₁ : 0 ≤ ε₁) (hε : 0 ≤ max ε₀ ε₁)
    (hκ0 : aEnt d L + 2 ≤ κ0) (θ : E) (u : ℂ) :
    (commonAct (fun θ u => (A₀ θ u).sum (commonAct A₁ hN hL reads₁ dom₁ hdom₁ hε₁ hκ0 θ u))
        hN hL reads dom hdom hε hκ0 θ u).H =
      classActFun (R₁ := RootUnionLb 1 reads₁ dom₁) (R₂ := RootUnionLb 1 reads dom)
        (fun θ u => (A₀ θ u).H) (fun θ u => (A₁ θ u).H) θ u := by
  funext y
  rcases y with (y | y | y) | y <;> rfl

open Classical in
/-- **The replacement identity of the coefficient of a class, reduced to its parts** (P3 p. 79):
the coefficient of the step on `Gp` (the determinant part plus the interpolation coefficient of the
class family `commonAct (A₀.sum (commonAct A₁ …))` at the parameter `e`) equals the formula
`newLevelCoeffBg` on `Gb` at the parameter `θ` with the activity function `classActFun H₀ H₁`, when
the determinant parts agree at `T`, the zero-class activities (`A₀` against `H₀`) and the inherited
activities (`A₁` against `H₁`) agree for `s ∈ [0, 1]` on the labels whose blocks lie in `T`, and the
marks agree on the anchors whose blocks lie in `T`. -/
theorem newLevelCoeffBg_class_eq_of_agree {N : ℕ} {ϱp ϱb : ℝ}
    (Gp : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱp)
    (Gb : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱb)
    (μ : ∀ b, Measure (Ωb b)) [∀ b, IsProbabilityMeasure (μ b)]
    (a : ℕ → ℝ) (aT ν ρ : ℝ) (Zp : Finset (unitPts Gp)) (Zb : Finset (unitPts Gb))
    (A₀ : E → ℂ → LabelAct Lab₀ Ωb ε₀ κH κ0 K₀)
    (A₁ : E → ℂ → LabelAct Lab₁ Ωb ε₁ κH κ0 K₁) (hN : L ^ 1 ∣ N₁) (hL : 2 ≤ L)
    (reads₁ : β₁ → Set (CTorus d L N₁ m₁ (k + 1)))
    (dom₁ : β₁ → Finset (Set (CTorus d L N₁ m₁ (k + 1))))
    (hdom₁ : ∀ b, ∀ Y ∈ dom₁ b, IsDj 1 (k + 1) Y)
    (reads : β₂ → Set (CTorus d L N₁ m₁ (k + 1)))
    (dom : β₂ → Finset (Set (CTorus d L N₁ m₁ (k + 1))))
    (hdom : ∀ b, ∀ Y ∈ dom b, IsDj 1 (k + 1) Y) (hε₁ : 0 ≤ ε₁) (hε : 0 ≤ max ε₀ ε₁)
    (hκ0 : aEnt d L + 2 ≤ κ0) (e : E) {ι : Type*} [Fintype ι]
    (y0 : ι → (Lb₀ ⊕ (Lb₁ ⊕ RootUnionLb 1 reads₁ dom₁)) ⊕ RootUnionLb 1 reads dom)
    (G : ι → ℂ → (∀ b, Ωb b) → ℂ) (θp : physParamBg N Gp)
    (H₀ : physParamBg N Gb → ℂ → Lb₀ → (∀ b, Ωb b) → ℂ)
    (H₁ : physParamBg N Gb → ℂ → Lb₁ → (∀ b, Ωb b) → ℂ)
    (G' : physParamBg N Gb → ι → ℂ → (∀ b, Ωb b) → ℂ) (θ : physParamBg N Gb)
    (T : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) 1 (k + 1) Set.univ))
    (hdet : newLevelDetBg Gp a aT ν ρ Zp θp T = newLevelDetBg Gb a aT ν ρ Zb θ T)
    (hGdep : ∀ i s, DepOn (blocksOf 1 (k + 1) Set.univ
      ((commonLabels (Lab₀.sum (commonLabels Lab₁ hN hL reads₁ dom₁ hdom₁)) hN hL reads dom
        hdom).ysite (y0 i))) (G i s))
    (hA₀ : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ y,
      blocksOf 1 (k + 1) Set.univ (Lab₀.ysite y) ⊆ T → (A₀ e (s : ℂ)).H y = H₀ θ (s : ℂ) y)
    (hA₁ : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ y,
      blocksOf 1 (k + 1) Set.univ (Lab₁.ysite y) ⊆ T → (A₁ e (s : ℂ)).H y = H₁ θ (s : ℂ) y)
    (hG : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ i,
      blocksOf 1 (k + 1) Set.univ
        ((commonLabels (Lab₀.sum (commonLabels Lab₁ hN hL reads₁ dom₁ hdom₁)) hN hL reads dom
          hdom).ysite (y0 i)) ⊆ T → G i (s : ℂ) = G' θ i (s : ℂ)) :
    newLevelDetBg Gp a aT ν ρ Zp θp T +
        gsumCoeff μ (commonLabels (Lab₀.sum (commonLabels Lab₁ hN hL reads₁ dom₁ hdom₁)) hN hL
          reads dom hdom)
          (commonAct (fun θ u => (A₀ θ u).sum (commonAct A₁ hN hL reads₁ dom₁ hdom₁ hε₁ hκ0 θ u))
            hN hL reads dom hdom hε hκ0 e) y0 G T =
      newLevelCoeffBg Gb μ a aT ν ρ Zb
        (commonLabels (Lab₀.sum (commonLabels Lab₁ hN hL reads₁ dom₁ hdom₁)) hN hL reads dom hdom)
        (classActFun H₀ H₁) y0 G' θ T := by
  refine newLevelCoeffBg_eq_of_agree Gb μ Gp a aT ν ρ Zp Zb _ _ y0 G θp _ G' θ T hdet hGdep
    (fun s hs y hy => ?_) hG
  rw [commonAct_sum_H A₀ A₁ hN hL reads₁ dom₁ hdom₁ reads dom hdom hε₁ hε hκ0 e (s : ℂ)]
  rcases y with (y | y | y) | y
  · exact hA₀ s hs y hy
  · exact hA₁ s hs y hy
  · rfl
  · rfl

end Bundled

end Balaban.Fluctuation
