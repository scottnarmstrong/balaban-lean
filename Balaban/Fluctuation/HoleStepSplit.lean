/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.HoleStepMeasure
public import Balaban.Fluctuation.Thm31cdeOn
public import Mathlib.Probability.ProductMeasure

/-!
# The fluctuation measure of the step on a region as a product over cubes (P5 (2.48), (3.2))

The measure `ν_{p₁}` of the fluctuation integral of the step on a region (`HoleStep.nuIn`) is a
product over the unit points of `Ω''_{k+1}`.  Grouping the unit points by the `π'_{k+1}`-cubes of a
region `Ω` makes it the product over the cubes of the products over their unit points, the block
structure (`ProdSplitOn`) on which the cluster expansion of Theorem 3.4 runs.

* `regroup`, `measurable_regroup`, `map_regroup_pi`: for a finite index set grouped by a map `c`, the
  product of a probability measure is carried by the regrouping to the product over the groups of
  the products over their members (`infinitePi_map_piCongrLeft`, `infinitePi_map_piCurry`);
* `HoleStep.prodSplit`: the block structure of `nuIn inner` on the cubes of `Ω`, for an assignment
  `cb` of a cube of `Ω` to every unit point of `inner` (`0 < p₁`);
* `HoleStep.oldTotal_eq_sum_of_marks`: **Theorem 3.1 (c) for the step on a region**: with the
  localized exponent and marks of the measure of P5 (3.2) on this block structure
  (`InterpMarksOn`), `ℬ''^{(k+1)} = ∑_S interpTermOn S` over the sets `S` of cubes of `Ω`, with the
  bound of Theorem 3.4.
-/

@[expose] public section

namespace Balaban.Fluctuation

open MeasureTheory Balaban.Localization

section Regroup

variable {ι β X : Type*} [Fintype ι] [Fintype β] [MeasurableSpace X]

/-- The regrouping of a family indexed by `ι` along `c : ι → β`: the family of its restrictions
to the fibres. -/
def regroup (c : ι → β) (x : ι → X) : ∀ b, {i // c i = b} → X := fun _ u => x u

omit [Fintype ι] [Fintype β] in
theorem measurable_regroup (c : ι → β) : Measurable (regroup (X := X) c) := by
  unfold regroup
  fun_prop

/-- **The product measure regrouped by fibres** is the product over the fibres of the products
over their members. -/
theorem map_regroup_pi [DecidableEq β] (c : ι → β) (μ : Measure X) [IsProbabilityMeasure μ] :
    (Measure.pi fun _ : ι => μ).map (regroup c) =
      Measure.pi fun b => Measure.pi fun _ : {i // c i = b} => μ := by
  set e : (Σ b, {i // c i = b}) ≃ ι := Equiv.sigmaFiberEquiv c
  have hcomp : regroup (X := X) c =
      (MeasurableEquiv.piCurry fun (b : β) (_ : {i // c i = b}) => X) ∘
        (MeasurableEquiv.piCongrLeft (fun _ : ι => X) e).symm := by
    funext x b u
    rfl
  have h1 : (Measure.infinitePi fun _ : ι => μ).map (MeasurableEquiv.piCongrLeft (fun _ => X) e).symm =
      Measure.infinitePi fun _ : (Σ b, {i // c i = b}) => μ := by
    rw [← Measure.infinitePi_map_piCongrLeft (X := fun _ : ι => X) (fun _ => μ) e, Measure.map_map
      (MeasurableEquiv.piCongrLeft (fun _ => X) e).symm.measurable
      (MeasurableEquiv.piCongrLeft (fun _ => X) e).measurable]
    simp
  have h2 := Measure.infinitePi_map_piCurry (X := fun (b : β) (_ : {i // c i = b}) => X)
    (fun _ _ => μ)
  rw [← Measure.infinitePi_eq_pi, hcomp, ← Measure.map_map (MeasurableEquiv.piCurry _).measurable
    (MeasurableEquiv.piCongrLeft (fun _ : ι => X) e).symm.measurable, h1, h2,
    Measure.infinitePi_eq_pi]
  congr 1
  funext b
  exact Measure.infinitePi_eq_pi _

end Regroup

namespace HoleStep

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ ϱ' : ℝ}
  (S : HoleStep d L N₁ m₁ k N ϱ ϱ')

/-- **The block structure of the fluctuation measure on the cubes of a region** `Ω` (side
`cellSide L m₀ m₁ (k + 1)`): for an assignment `cb` of a cube of `Ω` to every unit point of `inner`,
the variables of a cube are the variables of its unit points, with the product measure. -/
noncomputable def prodSplit (inner : Finset S.U) {m₀ : ℕ}
    (Ω : Set (CTorus d L N₁ m₁ (k + 1)))
    (cb : inner → CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) m₀ (k + 1) Ω)
    (hp : 0 < S.p₁) : ProdSplitOn (S.nuIn inner) d L N₁ m₁ (k + 1) m₀ Ω :=
  have := isProbabilityMeasure_fluctMeasure1 N hp
  { Ωb := fun b => {u : inner // cb u = b} → Rn N
    μ := fun b => Measure.pi fun _ : {u : inner // cb u = b} => fluctMeasure1 N S.p₁
    restr := regroup cb
    meas := measurable_regroup cb
    map_eq := map_regroup_pi cb (fluctMeasure1 N S.p₁) }

/-- **Theorem 3.1 (c) for the step on a region** (P5 (3.2), Proposition 3.1; P6 (4.32)–(4.34),
FLUCTUATION Theorem 3.1 (c)): if the exponent of the measure of P5 (3.2) and the old boundary terms
are localized on the cubes of the `π'`-union `Ω` (`InterpMarksOn` on the block structure `BS`), then
`ℬ''^{(k+1)} = ∫₀¹ ⟨ℬ''^{(k)}⟩''_u du = ∑_S interpTermOn S` over the sets `S` of cubes of `Ω`, with
`|interpTermOn S| ≤ C_PE (∑_i F₀ᵢ e^{-κ₀ 𝗱(Y₀ᵢ)}) e^{-κ' d_Ω(S)}`. -/
theorem oldTotal_eq_sum_of_marks (C : DecCover d L N₁ m₁ (k + 1)) (ρ : ℝ)
    (sloc : S.U → Dec2.DecParams C) (inner : Finset S.U) (ψout : S.U → Fin N → ℂ)
    (Φ B : (S.U → Fin N → ℂ) → ℂ) {m₀ : ℕ} {Ω : Set (CTorus d L N₁ m₁ (k + 1))}
    (hΩ : IsPiUnion m₀ (k + 1) Ω) {BS : ProdSplitOn (S.nuIn inner) d L N₁ m₁ (k + 1) m₀ Ω}
    (I : InterpMarksOn (S.nuIn inner) BS (S.expW C ρ sloc inner ψout Φ B)
      (fun _ => S.oldAt C ρ sloc inner ψout B)) :
    S.oldTotal C ρ sloc inner ψout Φ B = ∑ T, interpTermOn I T ∧
      ∀ T, ‖interpTermOn I T‖ ≤ CPE d L I.Kc I.κH I.κ0 I.κ' *
          (∑ i, I.F0 i * Real.exp (-I.κ0 * I.Lab.dl (I.y0 i))) * Real.exp (-I.κ' * dExt T) :=
  interpAvg_eq_sum_interpTermOn hΩ I

end HoleStep

end Balaban.Fluctuation
