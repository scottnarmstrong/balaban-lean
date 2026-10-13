/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.StepComplexProp26

/-!
# The step setting with a free block datum (off the constant-field fibre)

`StepSetting` stores a constant field `h₀` and a block datum `θ` with `θ.h = h₀`.  The wrapper
`StepSettingH S` carries a block datum whose field is arbitrary.  The old-level datum `dataUCH`
has the complex old spin `liftC ψ` and the field inherited from the incoming datum; on the fibre
it is the landed `dataUC`.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Background Balaban.Multiscale Balaban.Localization

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}

/-- A step setting with a free block datum `D'` (its field need not be constant). -/
structure StepSettingH (S : StepSetting d L N₁ m₁ k N ϱ) where
  /-- The block datum, with an arbitrary field. -/
  D' : BgData S.G' N

namespace StepSetting

variable (S : StepSetting d L N₁ m₁ k N ϱ)

/-- The free-datum wrapper with block datum `D`. -/
def withDatumH (D : BgData S.G' N) : StepSettingH S := ⟨D⟩

theorem withDatumH_fibre_datum (D : BgData S.G' N)
    (hD : ∀ x i, D.h x i = (S.h₀ i : ℂ)) :
    (S.withDatumH D).D' = (S.withDatum D hD).D' := rfl

end StepSetting

namespace StepSettingH

variable {S : StepSetting d L N₁ m₁ k N ϱ}

/-- The datum `(ψ, h)` of the complex old spin `ψ` at the level `k`, with spin `liftC ψ` and the
field inherited from the incoming datum (restricted by `composeData` to `Ω₁`). -/
noncomputable def dataUCH (H : StepSettingH S) (ψ : S.EC) :
    BgData (stepG d L N₁ m₁ k ϱ) N := by
  let B := composeData (S.hG.precedes S.hG' (le_refl (k + 1))) S.a
    (bgFieldC S.G' S.a S.ν (bgC0 d L N) H.D') H.D'
  exact BgData.clip (stepG d L N₁ m₁ k ϱ) (liftC S.hG' ψ) B.h
    (isLayerConstant_liftC S.hG S.hG' ψ) B.h_layerConst

/-- The raw data of `dataUCH`: the lifted spin and the field of the incoming datum. -/
def rawUCH (H : StepSettingH S) (ψ : S.EC) : RawData d L (N₁ * L ^ m₁) (k + 1) N :=
  (liftC S.hG' ψ, H.D'.h)

theorem dataUCH_h (H : StepSettingH S) (ψ : S.EC) (x : CTorus d L N₁ m₁ (k + 1)) (i : Fin N) :
    (H.dataUCH ψ).h x i = H.D'.h x i := by
  have hx : x ∈ (stepG d L N₁ m₁ k ϱ).Ω 1 := (S.hG x).1
  simp [dataUCH, BgData.clip, composeData, hx]

theorem dataUCH_Ψ (H : StepSettingH S) (ψ : S.EC) (x : CTorus d L N₁ m₁ (k + 1)) (i : Fin N) :
    (H.dataUCH ψ).Ψ x i = ψ (unitPt S.hG' x, i) := by
  have hx : x ∈ dataSites (stepG d L N₁ m₁ k ϱ) := (mem_dataSites _).2 (Or.inl (S.hG x).1)
  simp [dataUCH, BgData.clip, hx, liftC_apply]

theorem rawOf_dataUCH (H : StepSettingH S) (ψ : S.EC) :
    rawOf (H.dataUCH ψ) = H.rawUCH ψ := by
  refine Prod.ext ?_ ?_
  · funext z i
    show (H.dataUCH ψ).Ψ z i = liftC S.hG' ψ z i
    rw [H.dataUCH_Ψ, liftC_apply]
  · funext z i
    exact H.dataUCH_h ψ z i

theorem rawUCH_fibre (D : BgData S.G' N) (hD : ∀ x i, D.h x i = (S.h₀ i : ℂ)) (ψ : S.EC) :
    (S.withDatumH D).rawUCH ψ = (S.withDatum D hD).rawUC ψ := by
  refine Prod.ext rfl ?_
  funext z i
  exact hD z i

theorem dataUCH_fibre (D : BgData S.G' N) (hD : ∀ x i, D.h x i = (S.h₀ i : ℂ)) (ψ : S.EC) :
    (S.withDatumH D).dataUCH ψ = (S.withDatum D hD).dataUC ψ := by
  refine BgData.eq_of_raw ?_
  rw [rawOf_dataUCH, rawUCH_fibre D hD ψ]
  exact (StepSetting.dataUC_raw (S.withDatum D hD) ψ).symm

end StepSettingH

end Balaban.Fluctuation
