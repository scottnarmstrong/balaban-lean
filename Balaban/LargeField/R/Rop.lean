/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.Outcome
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# The operation `R` on a term of a representation (Definition III.8.3, P7 (1.3)-(1.6))

* `ROutcome`: the labels `σ(Z) ∈ {ϰ₁, …, ϰ₄, →R}` of the ripe components of `Z^pre_k(𝔸)`; `ROutcome.weight` is the
  weight of the corresponding piece of the decomposition of unity, `ROutcome.ofOutcome` the map from the six outcomes of
  Definition III.5.2 (`ϰ₅` and "removed" are the two parts of "→R", `weight_ofOutcome`).
* `RDecomp ν`: the data of a term `ρ(𝔸, σ)` for the operation `R`: the set `𝒵_σ = σ⁻¹(→R)` of components (the type `ι`),
  the variables `ψ_k↾Z₀` of the component `Z` (the space `W Z` with its measure; the variable space of
  `𝒵_{σ,0} = ⋃ Z₀` is the product `Π_Z W Z` with the product measure, the `Z₀` being pairwise disjoint), the remaining
  variables `ψ_k↾𝒵^c_{σ,0}` (`Y`), a measure preserving identification `e` of the whole field space with the product, and
  the reference densities `ρ_{k,0}(Z)` as functions of `(ψ_k↾Z₀, ψ_k↾𝒵^c_{σ,0})`: that `ρ_{k,0}(Z)` does not read the
  variables of the other components of `𝒵_σ` is built into this type.
* `Rop D ρ`: `R[ρ] = ∏_Z ρ_{k,0}(Z) · (∫ dψ_k↾𝒵_{σ,0} ρ) / ∏_Z ∫ dψ_k↾Z₀ ρ_{k,0}(Z)` (P7 (1.6)), defined for every
  function `ρ` on the field space; `RopSum` is `ρ' = Σ_{(𝔸,σ)} R[ρ(𝔸, σ)]`.
-/

@[expose] public section

open MeasureTheory

namespace Balaban.LargeField

/-- The labels of a ripe component under `R`: the kept outcomes `ϰ₁, …, ϰ₄` (`kept i = ϰ_{i+1}`) and "to `R`". -/
inductive ROutcome
  | kept (i : Fin 4)
  | toR
  deriving DecidableEq

namespace ROutcome

instance : Fintype ROutcome :=
  Fintype.ofEquiv (Option (Fin 4))
    { toFun := fun o => o.elim toR kept
      invFun := fun o => match o with
        | kept i => some i
        | toR => none
      left_inv := fun o => by cases o <;> rfl
      right_inv := fun o => by cases o <;> rfl }

/-- The weight of the label, for the values `t = χ̃_k`, `s = χ_S`, `z = χ^0`, `w = χ''`:
`ϰ₁: 1-t`, `ϰ₂: t(1-s)`, `ϰ₃: t s (1-z)`, `ϰ₄: t s z (1-w)`, `→R: t s z w`. -/
def weight (t s z w : ℝ) : ROutcome → ℝ
  | kept 0 => 1 - t
  | kept 1 => t * (1 - s)
  | kept 2 => t * s * (1 - z)
  | kept 3 => t * s * z * (1 - w)
  | toR => t * s * z * w

theorem weight_sum (t s z w : ℝ) : ∑ o : ROutcome, weight t s z w o = 1 := by
  have h : ∑ o : ROutcome, weight t s z w o = ∑ o : Option (Fin 4), weight t s z w (o.elim toR kept) := by
    refine (Fintype.sum_equiv
      { toFun := fun o => match o with
          | kept i => some i
          | toR => none
        invFun := fun o => o.elim toR kept
        left_inv := fun o => by cases o <;> rfl
        right_inv := fun o => by cases o <;> rfl } _ _ fun o => ?_)
    cases o <;> rfl
  rw [h, Fintype.sum_option]
  simp only [Option.elim_none, Option.elim_some, Fin.sum_univ_four]
  simp only [weight]
  ring

/-- Definition III.5.2 refined by `R`: the outcomes `ϰ₁, …, ϰ₄` of the first kind are kept; `ϰ₅` and "removed" are the
two parts of the term "to `R`". -/
def ofOutcome : Outcome → ROutcome
  | Outcome.kept 0 => kept 0
  | Outcome.kept 1 => kept 1
  | Outcome.kept 2 => kept 2
  | Outcome.kept 3 => kept 3
  | Outcome.kept 4 => toR
  | Outcome.rem => toR

/-- The weight of "to `R`" is the sum of the weights of `ϰ₅` and "removed" (`t s z w (1-u) + t s z w u`), and the other
labels are unchanged. -/
theorem weight_ofOutcome (t s z w u : ℝ) (r : ROutcome) :
    (Outcome.weight t s z w u (Outcome.kept 0) * (if ofOutcome (Outcome.kept 0) = r then 1 else 0) +
      Outcome.weight t s z w u (Outcome.kept 1) * (if ofOutcome (Outcome.kept 1) = r then 1 else 0) +
      Outcome.weight t s z w u (Outcome.kept 2) * (if ofOutcome (Outcome.kept 2) = r then 1 else 0) +
      Outcome.weight t s z w u (Outcome.kept 3) * (if ofOutcome (Outcome.kept 3) = r then 1 else 0) +
      Outcome.weight t s z w u (Outcome.kept 4) * (if ofOutcome (Outcome.kept 4) = r then 1 else 0) +
      Outcome.weight t s z w u Outcome.rem * (if ofOutcome Outcome.rem = r then 1 else 0)) =
      weight t s z w r := by
  rcases r with ⟨i⟩ | _
  · fin_cases i <;> simp [ofOutcome, weight, Outcome.weight]
  · simp [ofOutcome, weight, Outcome.weight]
    ring

end ROutcome

/-- **The data of a term `ρ(𝔸, σ)` for the operation `R`** (Definition III.8.3). -/
structure RDecomp {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω) where
  /-- The set `𝒵_σ = σ⁻¹(→R)` of ripe components sent to `R`. -/
  ι : Type
  [fintype : Fintype ι]
  /-- The variables `ψ_k↾Z₀` of the component `Z`. -/
  W : ι → Type
  [mW : ∀ c, MeasurableSpace (W c)]
  /-- Their (Lebesgue) measures. -/
  μ : ∀ c, Measure (W c)
  [sfW : ∀ c, SigmaFinite (μ c)]
  /-- The remaining variables `ψ_k↾𝒵^c_{σ,0}`. -/
  Y : Type
  [mY : MeasurableSpace Y]
  νY : Measure Y
  [sfY : SigmaFinite νY]
  /-- The identification `ψ_k ↔ (ψ_k↾𝒵_{σ,0}, ψ_k↾𝒵^c_{σ,0})`. -/
  e : Ω ≃ᵐ ((∀ c, W c) × Y)
  mp : MeasurePreserving e ν ((Measure.pi μ).prod νY)
  /-- The reference densities `ρ_{k,0}(Z)` as functions of `(ψ_k↾Z₀, ψ_k↾𝒵^c_{σ,0})`. -/
  r : ∀ c, W c → Y → ℝ

attribute [instance] RDecomp.fintype RDecomp.mW RDecomp.sfW RDecomp.mY RDecomp.sfY

variable {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω}

/-- **`R[ρ]`** on the product space (P7 (1.6)). -/
noncomputable def RopProd {ι : Type} [Fintype ι] {W : ι → Type} [∀ c, MeasurableSpace (W c)]
    (μ : ∀ c, Measure (W c)) {Y : Type} (r : ∀ c, W c → Y → ℝ) (ρ : ((∀ c, W c) × Y) → ℝ) :
    ((∀ c, W c) × Y) → ℝ :=
  fun p => (∏ c, r c (p.1 c) p.2) * ((∫ x, ρ (x, p.2) ∂(Measure.pi μ)) / ∏ c, ∫ w, r c w p.2 ∂(μ c))

/-- **The operation `R` on a term `ρ(𝔸, σ)`** (Definition III.8.3, P7 (1.6)):
`R[ρ] = ∏_{Z ∈ 𝒵_σ} ρ_{k,0}(Z) · (∫ dψ_k↾𝒵_{σ,0} ρ) / ∏_{Z ∈ 𝒵_σ} ∫ dψ_k↾Z₀ ρ_{k,0}(Z)`. -/
noncomputable def Rop (D : RDecomp ν) (ρ : Ω → ℝ) : Ω → ℝ :=
  fun ψ => RopProd D.μ D.r (fun p => ρ (D.e.symm p)) (D.e ψ)

/-- **`ρ' = Σ_{(𝔸,σ)} R[ρ(𝔸,σ)]`** (P7 (1.6)): the sum over the finitely many terms. -/
noncomputable def RopSum {T : Type*} [Fintype T] (D : T → RDecomp ν) (ρ : T → Ω → ℝ) : Ω → ℝ :=
  fun ψ => ∑ t, Rop (D t) (ρ t) ψ

section Witness

/-- **Inhabitedness of `RDecomp`**: the decomposition with no component sent to `R` (`𝒵_σ = ∅`). -/
noncomputable def RDecomp.empty {Ω : Type} [MeasurableSpace Ω] (ν : Measure Ω) [SigmaFinite ν] : RDecomp ν where
  ι := PEmpty
  W := fun _ => PUnit
  μ := fun _ => 0
  Y := Ω
  νY := ν
  e :=
    { toFun := fun ψ => (fun c => isEmptyElim c, ψ)
      invFun := fun p => p.2
      left_inv := fun _ => rfl
      right_inv := fun p => by
        refine Prod.ext (funext fun c => isEmptyElim c) rfl
      measurable_toFun := measurable_prodMk_left
      measurable_invFun := measurable_snd }
  mp := by
    refine ⟨?_, ?_⟩
    · exact measurable_prodMk_left
    · rw [Measure.pi_of_empty, Measure.dirac_prod]
      rfl
  r := fun _ _ _ => 0

theorem RDecomp.nonempty {Ω : Type} [MeasurableSpace Ω] (ν : Measure Ω) [SigmaFinite ν] :
    Nonempty (RDecomp ν) :=
  ⟨RDecomp.empty ν⟩

end Witness

end Balaban.LargeField
