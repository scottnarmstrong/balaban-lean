/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Polymer.TwoTorusObsAssembly
public import Balaban.Polymer.TwoTorusGapCloseSym

/-!
# Translation covariance of the observable coefficient: block measures and hat variables

For a lattice symmetry `σ` of the step torus acting on the unit points by `unitAct`, block
variables `Φ`, `Φ'` correspond when `Φ'` at the translated unit point of the translated block equals
`Φ` at the unit point.  The integral of the block measures is invariant, the hat variables and the
first-order marks correspond.
-/

@[expose] public section

noncomputable section

open scoped Classical

namespace Balaban.Polymer.TwoTorusStep

open Balaban Balaban.Localization Balaban.Fluctuation Balaban.SmallField Balaban.SmallField.Def6
  Balaban.Background Balaban.Analysis Balaban.Polymer Balaban.Multiscale MeasureTheory
  Balaban.Localization.DetUnitIncidence

section Sym

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
  (S : StepSetting d L N₁ m₁ k N ϱ) (m₀ : ℕ) (hp : 0 < S.p₁)
  {σ : Equiv.Perm (CTorus d L N₁ m₁ (k + 1))} (SS : LatSymm S.G' S.G' σ) (hU : UnitBlockPres σ)

/-- **Integral of the block measures under a lattice symmetry.**  If `F' Φ' = F Φ` whenever the block
variables correspond under `unitAct`, the integrals agree. -/
theorem integral_blockSplit_sym
    {F F' : (∀ c, (S.blockSplit m₀ hp).Ωb c) → ℂ}
    (hFF : ∀ Φ Φ', (∀ u : S.U, Φ' (S.cellOf m₀ (unitAct S.G' SS hU u)) ⟨unitAct S.G' SS hU u, rfl⟩ =
        Φ (S.cellOf m₀ u) ⟨u, rfl⟩) → F' Φ' = F Φ) :
    ∫ Φ', F' Φ' ∂(Measure.pi (S.blockSplit m₀ hp).μ) =
      ∫ Φ, F Φ ∂(Measure.pi (S.blockSplit m₀ hp).μ) := by
  classical
  have : IsProbabilityMeasure (fluctMeasure1 N S.p₁) := isProbabilityMeasure_fluctMeasure1 N hp
  rw [integral_blockSplit_eq S m₀ hp F', integral_blockSplit_eq S m₀ hp F]
  have key : ∀ x' : S.U → Rn N,
      F' (fun _ u => x' u.1) = F (fun _ u => x' (unitAct S.G' SS hU u.1)) := fun x' =>
    hFF _ _ (fun u => rfl)
  simp_rw [key]
  exact integral_pi_comp_of_injOn (fluctMeasure1 N S.p₁) (unitAct S.G' SS hU) Finset.univ
    (fun a _ b _ h => (unitAct S.G' SS hU).injective h)
    (f := fun x : S.U → Rn N => F (fun _ u => x u.1)) (fun x y h => by
      rw [show x = y from funext fun w => h w (Finset.mem_univ _)])

/-- The hat variables correspond under `unitAct`. -/
theorem hatOf_sym (ρ : ℝ) {Φ Φ' : ∀ c, (S.blockSplit m₀ hp).Ωb c}
    (hΦ : ∀ u : S.U, Φ' (S.cellOf m₀ (unitAct S.G' SS hU u)) ⟨unitAct S.G' SS hU u, rfl⟩ =
        Φ (S.cellOf m₀ u) ⟨u, rfl⟩) (u : S.U) (a : Fin N) :
    S.hatOf m₀ ρ hp Φ' (unitAct S.G' SS hU u, a) = S.hatOf m₀ ρ hp Φ (u, a) := by
  simp only [StepSetting.hatOf]
  rw [hΦ u]

/-- The first-order marks correspond under `unitAct`. -/
theorem blockMarkC_sym {Φ Φ' : ∀ c, (S.blockSplit m₀ hp).Ωb c}
    (hΦ : ∀ u : S.U, Φ' (S.cellOf m₀ (unitAct S.G' SS hU u)) ⟨unitAct S.G' SS hU u, rfl⟩ =
        Φ (S.cellOf m₀ u) ⟨u, rfl⟩) (u : S.U) (a : Fin N) :
    blockMarkC S m₀ hp (unitAct S.G' SS hU u) a Φ' = blockMarkC S m₀ hp u a Φ :=
  hatOf_sym S m₀ hp SS hU _ hΦ u a

end Sym

end Balaban.Polymer.TwoTorusStep
