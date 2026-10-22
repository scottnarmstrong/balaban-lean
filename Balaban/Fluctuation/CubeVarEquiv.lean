/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.HoleStepMarks

/-!
# Transport of the cube variables along a bijection of the unit points and of the cubes

For two assignments `cb₁ : inner₁ → Cb₁`, `cb₂ : inner₂ → Cb₂` of cubes to unit points and a
bijection `ι : inner₁ ≃ inner₂` of the unit points that carries `cb₁` to `cb₂` along a bijection
`e : Cb₁ ≃ Cb₂` of the cubes, the variables of the cubes are identified
(`cubeVarEquiv`): it preserves the product of the measures of the unit points
(`measurePreserving_cubeVarEquiv`) and carries the value at a unit point to the value at its image
(`ungroup_cubeVarEquiv`).
-/

@[expose] public section

open MeasureTheory

namespace Balaban.Fluctuation

open Balaban Balaban.Localization

variable {U₁ U₂ Cb₁ Cb₂ : Type*} {inner₁ : Finset U₁} {inner₂ : Finset U₂}
  (e : Cb₁ ≃ Cb₂) (cb₁ : inner₁ → Cb₁) (cb₂ : inner₂ → Cb₂) (ι : inner₁ ≃ inner₂)
  (hι : ∀ u, cb₂ (ι u) = e (cb₁ u)) (N : ℕ)

/-- The fibre of a cube is carried to the fibre of its image. -/
def cubeFibre (b : Cb₁) : {u : inner₁ // cb₁ u = b} ≃ {u : inner₂ // cb₂ u = e b} where
  toFun u := ⟨ι u.1, by rw [hι, u.2]⟩
  invFun u := ⟨ι.symm u.1, by
    apply e.injective
    rw [← hι, Equiv.apply_symm_apply, u.2]⟩
  left_inv u := Subtype.ext (by simp)
  right_inv u := Subtype.ext (by simp)

/-- **The identification of the cube variables** of two systems related by `e` and `ι`. -/
def cubeVarEquiv :
    (∀ b, {u : inner₁ // cb₁ u = b} → Rn N) ≃ᵐ (∀ b, {u : inner₂ // cb₂ u = b} → Rn N) :=
  (MeasurableEquiv.piCongrRight fun b =>
    MeasurableEquiv.piCongrLeft (fun _ => Rn N) (cubeFibre e cb₁ cb₂ ι hι b)).trans
    (MeasurableEquiv.piCongrLeft (fun b' => {u : inner₂ // cb₂ u = b'} → Rn N) e)

/-- The identification of the cube variables preserves the product of the measures of the unit
points. -/
theorem measurePreserving_cubeVarEquiv (ν : Measure (Rn N)) [SigmaFinite ν] [Fintype Cb₁] [Fintype Cb₂]
    [DecidableEq Cb₁] [DecidableEq Cb₂] :
    MeasurePreserving (cubeVarEquiv e cb₁ cb₂ ι hι N)
      (Measure.pi fun b => Measure.pi fun _ : {u : inner₁ // cb₁ u = b} => ν)
      (Measure.pi fun b => Measure.pi fun _ : {u : inner₂ // cb₂ u = b} => ν) := by
  have h1 : MeasurePreserving (MeasurableEquiv.piCongrRight fun b =>
      MeasurableEquiv.piCongrLeft (fun _ => Rn N) (cubeFibre e cb₁ cb₂ ι hι b))
      (Measure.pi fun b => Measure.pi fun _ : {u : inner₁ // cb₁ u = b} => ν)
      (Measure.pi fun b => Measure.pi fun _ : {u : inner₂ // cb₂ u = e b} => ν) :=
    measurePreserving_pi _ _ fun b =>
      measurePreserving_piCongrLeft (fun _ => ν) (cubeFibre e cb₁ cb₂ ι hι b)
  have h2 := measurePreserving_piCongrLeft
    (α := fun b' => {u : inner₂ // cb₂ u = b'} → Rn N)
    (fun b' => Measure.pi fun _ : {u : inner₂ // cb₂ u = b'} => ν) e
  exact h2.comp h1

/-- The value at a unit point is carried to the value at its image. -/
theorem ungroup_cubeVarEquiv (Φ : ∀ b, {u : inner₁ // cb₁ u = b} → Rn N) (u : inner₁) :
    ungroup cb₂ (cubeVarEquiv e cb₁ cb₂ ι hι N Φ) (ι u) = ungroup cb₁ Φ u := by
  have claim : ∀ (b : Cb₁) (x : {u : inner₁ // cb₁ u = b}),
      cubeVarEquiv e cb₁ cb₂ ι hι N Φ (e b) (cubeFibre e cb₁ cb₂ ι hι b x) = Φ b x := by
    intro b x
    simp only [cubeVarEquiv, MeasurableEquiv.trans_apply, MeasurableEquiv.coe_piCongrLeft,
      Equiv.piCongrLeft_apply_apply]
    simp [MeasurableEquiv.piCongrRight, MeasurableEquiv.coe_piCongrLeft,
      Equiv.piCongrLeft_apply_apply]
  have gen : ∀ (b : Cb₁) (hb : cb₁ u = b) (b' : Cb₂) (hb' : cb₂ (ι u) = b') (h : e b = b'),
      cubeVarEquiv e cb₁ cb₂ ι hι N Φ b' ⟨ι u, hb'⟩ = Φ b ⟨u, hb⟩ := by
    intro b hb b' hb' h
    subst hb h
    exact claim _ ⟨u, rfl⟩
  exact gen _ rfl _ rfl (hι u).symm

end Balaban.Fluctuation
