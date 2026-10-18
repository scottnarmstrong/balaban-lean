/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.StepTowerNewLevelSymGeom
public import Balaban.Fluctuation.LocalClassDensityHAnalytic
public import Balaban.Fluctuation.LocalClassLatCore

/-!
# The old datum of a shifted spin and the critical spin under a lattice symmetry (`StepTowerNewLevelSymData`)

For a block datum `D` of the step and a lattice symmetry `σ` of the level sets `𝔹'_k` and `𝔹_k`
(preserving the unit blocks, with the induced permutation `u` of the unit points):

* `dataUCH_sym`: `dataUCH (σ D) (ψ ∘ u⁻¹) = σ (dataUCH D ψ)`;
* `psi0H_sym`: the critical spin of `σ D` is `ψ^{(k)}(D) ∘ u⁻¹`.
-/

@[expose] public section

namespace Balaban.Inhabited.StepSym

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization Balaban.Fluctuation
  Balaban.SmallField Balaban.SmallField.Def6 Balaban.Localization.DecEquiv
  Balaban.Localization.DetUnitIncidence Matrix

section Step

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
variable {S : StepSetting d L N₁ m₁ k N ϱ} {σ : Equiv.Perm (CTorus d L N₁ m₁ (k + 1))}
variable (Sy : LatSymm S.G' S.G' σ) (Sk : LatSymm (stepG d L N₁ m₁ k ϱ) (stepG d L N₁ m₁ k ϱ) σ)
  (hU : UnitBlockPres σ)

include Sk Sy hU in
/-- **The old datum of a shifted spin is transported**: the datum `dataUCH` of the block datum
`σ D` at the shift `ψ ∘ u⁻¹` is the `σ`-transport of the datum `dataUCH` of `D` at `ψ`. -/
theorem dataUCH_sym (D : BgData S.G' N) (ψ : S.EC) :
    (S.withDatumH (Sy.sym D)).dataUCH (fun r => ψ ((unitAct S.G' Sy hU).symm r.1, r.2)) =
      Sk.sym ((S.withDatumH D).dataUCH ψ) := by
  refine BgData.ext' ?_ ?_
  · funext x i
    rw [StepSettingH.dataUCH_Ψ]
    show ψ ((unitAct S.G' Sy hU).symm (unitPt S.hG' x), i) =
      ((S.withDatumH D).dataUCH ψ).Ψ (σ.symm x) i
    rw [StepSettingH.dataUCH_Ψ, unitAct_symm_unitPt S.hG' Sy hU]
  · funext x i
    rw [StepSettingH.dataUCH_h]
    show D.h (σ.symm x) i = ((S.withDatumH D).dataUCH ψ).h (σ.symm x) i
    rw [StepSettingH.dataUCH_h]
    rfl

include Sk Sy hU in
/-- **The critical spin is transported**: `ψ^{(k)}(σ θ) = ψ^{(k)}(θ) ∘ u⁻¹` on the unit points. -/
theorem psi0H_sym (D : BgData S.G' N) :
    (S.withDatumH (Sy.sym D)).psi0H =
      fun r => (S.withDatumH D).psi0H ((unitAct S.G' Sy hU).symm r.1, r.2) := by
  funext r
  have hc := composeData_sym_pair Sk Sy (S.hG.precedes S.hG' (le_refl (k + 1)))
    (S.hG.precedes S.hG' (le_refl (k + 1))) S.a
    (bgFieldC S.G' S.a S.ν (bgC0 d L N) D) D
  have hb := (Sy.bgFieldC_sym S.a S.ν (bgC0 d L N) D).1
  show (composeData (S.hG.precedes S.hG' (le_refl (k + 1))) S.a
      (bgFieldC S.G' S.a S.ν (bgC0 d L N) (Sy.sym D)) (Sy.sym D)).Ψ (unitRep r.1) r.2 =
    (composeData (S.hG.precedes S.hG' (le_refl (k + 1))) S.a
      (bgFieldC S.G' S.a S.ν (bgC0 d L N) D) D).Ψ
        (unitRep ((unitAct S.G' Sy hU).symm r.1)) r.2
  rw [hb, hc]
  show (composeData (S.hG.precedes S.hG' (le_refl (k + 1))) S.a
      (bgFieldC S.G' S.a S.ν (bgC0 d L N) D) D).Ψ (σ.symm (unitRep r.1)) r.2 = _
  rw [← S.critical_Ψ_unitRep _ (σ.symm (unitRep r.1)) r.2,
    ← S.critical_Ψ_unitRep _ (unitRep ((unitAct S.G' Sy hU).symm r.1)) r.2]
  congr 2
  rw [← unitAct_symm_unitPt S.hG' Sy hU]
  have h1 : unitPt S.hG' (unitRep r.1) = r.1 := Subtype.ext (unitBlock_unitRep r.1)
  have h2 : unitPt S.hG' (unitRep ((unitAct S.G' Sy hU).symm r.1)) =
      (unitAct S.G' Sy hU).symm r.1 := Subtype.ext (unitBlock_unitRep _)
  rw [h1, h2]

end Step
end Balaban.Inhabited.StepSym
