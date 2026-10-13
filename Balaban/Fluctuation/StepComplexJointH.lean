/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.StepSettingH

/-!
# Joint representatives at a free block datum

The raw joint representatives are compared with the old-level datum carrying the incoming
external field. These comparisons do not require the field to be constant.
-/

@[expose] public section

namespace Balaban.Fluctuation.StepSetting.JointRep

open Balaban Balaban.Background Balaban.Multiscale Balaban.Localization Balaban.SmallField.Def6 Matrix

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ eps pp : ℝ}
  {S : StepSetting d L N₁ m₁ k N ϱ} (Jr : S.JointRep eps pp)
  (H : StepSettingH S) (C : StepClass d L N₁ m₁ k N ϱ)
  (hX : XiCData S.G' S.a S.ν (k + 1) 1 eps H.D')

include hX in
/-- The raw old spin represented by `gJ` has the incoming field at every chart datum. -/
theorem gJ_dataUCH (ψh : S.EC) :
    Jr.gJ (rawOf H.D', ψh) = rawOf (H.dataUCH
      ((fun q =>
        (composeData (S.hG.precedes S.hG' (le_refl (k + 1))) S.a
          (bgFieldC S.G' S.a S.ν (bgC0 d L N) H.D') H.D').Ψ
            (unitRep (G' := S.G') q.1) q.2) +
        S.hatField (hatCovSqrt S.G' S.a₁ S.ν H.D') ψh)) := by
  rw [Jr.gJ_datum H.D' hX ψh, H.rawOf_dataUCH_psiHat]

include Jr hX in
/-- A bounded old spin represented by `gJ` lies in the old-level domain. -/
theorem dataUCH_hat_dom {ψh : S.EC} (hψh : ∀ p, ‖ψh p‖ ≤ pp) :
    InUnionDomainC (stepG d L N₁ m₁ k ϱ) (bgC0 d L N) (bgC1 d L N) S.ν
      (H.dataUCH
        ((fun q =>
          (composeData (S.hG.precedes S.hG' (le_refl (k + 1))) S.a
            (bgFieldC S.G' S.a S.ν (bgC0 d L N) H.D') H.D').Ψ
              (unitRep (G' := S.G') q.1) q.2) +
          S.hatField (hatCovSqrt S.G' S.a₁ S.ν H.D') ψh)) := by
  exact Jr.datum_hat_dom H.D' hX _ (Jr.gJ_dataUCH H hX ψh) hψh

include hX in
/-- The old small solution represented by `FJ` is evaluated at the free-field old datum. -/
theorem FJ_dataUCH {ψh : S.EC} (hψh : ∀ p, ‖ψh p‖ ≤ pp) :
    Jr.FJ (rawOf H.D', ψh) =
      (bgFieldC (stepG d L N₁ m₁ k ϱ) S.a S.ν (bgC0 d L N)
        (H.dataUCH
          ((fun q =>
            (composeData (S.hG.precedes S.hG' (le_refl (k + 1))) S.a
              (bgFieldC S.G' S.a S.ν (bgC0 d L N) H.D') H.D').Ψ
                (unitRep (G' := S.G') q.1) q.2) +
            S.hatField (hatCovSqrt S.G' S.a₁ S.ν H.D') ψh)),
       bgMultC (stepG d L N₁ m₁ k ϱ) S.a S.ν (bgC0 d L N)
        (H.dataUCH
          ((fun q =>
            (composeData (S.hG.precedes S.hG' (le_refl (k + 1))) S.a
              (bgFieldC S.G' S.a S.ν (bgC0 d L N) H.D') H.D').Ψ
                (unitRep (G' := S.G') q.1) q.2) +
            S.hatField (hatCovSqrt S.G' S.a₁ S.ν H.D') ψh))) := by
  exact Jr.FJ_datum H.D' hX _ (Jr.gJ_dataUCH H hX ψh) hψh

include hX in
/-- The composed pair represented by `PJ` is that of the free-field old datum. -/
theorem PJ_dataUCH {ψh : S.EC} (hψh : ∀ p, ‖ψh p‖ ≤ pp) (j : ℕ) :
    let D₀ := H.dataUCH
      ((fun q =>
        (composeData (S.hG.precedes S.hG' (le_refl (k + 1))) S.a
          (bgFieldC S.G' S.a S.ν (bgC0 d L N) H.D') H.D').Ψ
            (unitRep (G' := S.G') q.1) q.2) +
        S.hatField (hatCovSqrt S.G' S.a₁ S.ν H.D') ψh)
    Jr.PJ j (rawOf H.D', ψh) =
      composedPairAtC S.a S.ν (Nat.le_succ k) j D₀ := by
  exact Jr.PJ_datum H.D' hX _ (Jr.gJ_dataUCH H hX ψh) hψh j

include hX in
/-- The composed energy represented by `EJ` is evaluated at the free-field old datum. -/
theorem EJ_dataUCH {ψh : S.EC} (hψh : ∀ p, ‖ψh p‖ ≤ pp) :
    let D₀ := H.dataUCH
      ((fun q =>
        (composeData (S.hG.precedes S.hG' (le_refl (k + 1))) S.a
          (bgFieldC S.G' S.a S.ν (bgC0 d L N) H.D') H.D').Ψ
            (unitRep (G' := S.G') q.1) q.2) +
        S.hatField (hatCovSqrt S.G' S.a₁ S.ν H.D') ψh)
    Jr.EJ C (rawOf H.D', ψh) =
      EcompAtC C.m₀ C.Tm S.a S.ν (Nat.le_succ k) D₀ := by
  exact Jr.EJ_datum C H.D' hX _ (Jr.gJ_dataUCH H hX ψh) hψh

include hX in
/-- The composed source term represented by `FcJ` is evaluated at the free-field datum. -/
theorem FcJ_dataUCH {ψh : S.EC} (hψh : ∀ p, ‖ψh p‖ ≤ pp)
    (g : Fld d L N₁ m₁ (k + 1) N) :
    let D₀ := H.dataUCH
      ((fun q =>
        (composeData (S.hG.precedes S.hG' (le_refl (k + 1))) S.a
          (bgFieldC S.G' S.a S.ν (bgC0 d L N) H.D') H.D').Ψ
            (unitRep (G' := S.G') q.1) q.2) +
        S.hatField (hatCovSqrt S.G' S.a₁ S.ν H.D') ψh)
    Jr.FcJ C g (rawOf H.D', ψh) =
      FcompAtC C.m₀ C.Tm S.a S.ν (Nat.le_succ k) D₀ g := by
  exact Jr.FcJ_datum C H.D' hX _ (Jr.gJ_dataUCH H hX ψh) hψh g

include hX in
/-- The composed observable represented by `McJ` is evaluated at the free-field datum. -/
theorem McJ_dataUCH {ψh : S.EC} (hψh : ∀ p, ‖ψh p‖ ≤ pp)
    (g : Fld d L N₁ m₁ (k + 1) N) (y : CTorus d L N₁ m₁ (k + 1)) (i : Fin N) :
    let D₀ := H.dataUCH
      ((fun q =>
        (composeData (S.hG.precedes S.hG' (le_refl (k + 1))) S.a
          (bgFieldC S.G' S.a S.ν (bgC0 d L N) H.D') H.D').Ψ
            (unitRep (G' := S.G') q.1) q.2) +
        S.hatField (hatCovSqrt S.G' S.a₁ S.ν H.D') ψh)
    Jr.McJ C g y i (rawOf H.D', ψh) =
      McompAtC C.m₀ C.Tm S.a S.ν (Nat.le_succ k) D₀ g y i := by
  exact Jr.McJ_datum C H.D' hX _ (Jr.gJ_dataUCH H hX ψh) hψh g y i

include hX in
/-- The joint interaction is the old-level interaction at the free-field datum. -/
theorem VJ_dataUCH {ψh : S.EC} (hψh : ∀ p, ‖ψh p‖ ≤ pp) :
    let D₀ := H.dataUCH
      ((fun q =>
        (composeData (S.hG.precedes S.hG' (le_refl (k + 1))) S.a
          (bgFieldC S.G' S.a S.ν (bgC0 d L N) H.D') H.D').Ψ
            (unitRep (G' := S.G') q.1) q.2) +
        S.hatField (hatCovSqrt S.G' S.a₁ S.ν H.D') ψh)
    Jr.VJ (rawOf H.D', ψh) =
      interactionV (S.hG.precedes S.hG' (le_refl (k + 1))) S.a S.ν
        (bgMultC S.G' S.a S.ν (bgC0 d L N) H.D')
        (bgFieldC S.G' S.a S.ν (bgC0 d L N) H.D')
        (compTangent S.hG S.hG' (le_refl (k + 1)) S.a
          (bgFieldC S.G' S.a S.ν (bgC0 d L N) H.D') H.D' D₀)
        (bgFieldC (stepG d L N₁ m₁ k ϱ) S.a S.ν (bgC0 d L N) D₀ -
          (S.hG.precedes S.hG' (le_refl (k + 1))).restrictφ
            (bgFieldC S.G' S.a S.ν (bgC0 d L N) H.D')) := by
  exact Jr.VJ_datum H.D' hX _ (Jr.gJ_dataUCH H hX ψh) hψh

include hX in
/-- The joint kernel uses the incoming spin and the free-field old spin. -/
theorem tKJ_dataUCH (ψh : S.EC) :
    let D₀ := H.dataUCH
      ((fun q =>
        (composeData (S.hG.precedes S.hG' (le_refl (k + 1))) S.a
          (bgFieldC S.G' S.a S.ν (bgC0 d L N) H.D') H.D').Ψ
            (unitRep (G' := S.G') q.1) q.2) +
        S.hatField (hatCovSqrt S.G' S.a₁ S.ν H.D') ψh)
    Jr.tKJ (rawOf H.D', ψh) =
      (((S.cKernel / (2 * Real.pi)) ^ ((N : ℝ) * S.nBlocks / 2) : ℝ) : ℂ) *
        Complex.exp (-((S.β : ℂ) * couplingC S.G' S.a₁ (k + 1) H.D'.Ψ D₀.Ψ)) := by
  exact Jr.tKJ_datum H.D' _ (Jr.gJ_dataUCH H hX ψh)

include hX in
/-- The joint density is the action and composites of the free-field old datum. -/
theorem rhoJ_dataUCH {ψh : S.EC} (hψh : ∀ p, ‖ψh p‖ ≤ pp)
    (g : Fld d L N₁ m₁ (k + 1) N) :
    let D₀ := H.dataUCH
      ((fun q =>
        (composeData (S.hG.precedes S.hG' (le_refl (k + 1))) S.a
          (bgFieldC S.G' S.a S.ν (bgC0 d L N) H.D') H.D').Ψ
            (unitRep (G' := S.G') q.1) q.2) +
        S.hatField (hatCovSqrt S.G' S.a₁ S.ν H.D') ψh)
    Jr.rhoJ C g (rawOf H.D', ψh) =
      Complex.exp (-(S.β : ℂ) * actionC (stepG d L N₁ m₁ k ϱ) S.a S.ν D₀
          (bgFieldC (stepG d L N₁ m₁ k ϱ) S.a S.ν (bgC0 d L N) D₀) +
        EcompAtC C.m₀ C.Tm S.a S.ν (Nat.le_succ k) D₀ -
        (C.Ek : ℂ) * (S.nU : ℂ) +
        FcompAtC C.m₀ C.Tm S.a S.ν (Nat.le_succ k) D₀ g) := by
  exact Jr.rhoJ_datum C H.D' hX _ (Jr.gJ_dataUCH H hX ψh) hψh g

include hX in
/-- The second interpolation exponent is the change of the free-field source term. -/
theorem W2_dataUCH {ψh : S.EC} (hψh : ∀ p, ‖ψh p‖ ≤ pp)
    (g : Fld d L N₁ m₁ (k + 1) N) :
    let D₀ := H.dataUCH
      ((fun q =>
        (composeData (S.hG.precedes S.hG' (le_refl (k + 1))) S.a
          (bgFieldC S.G' S.a S.ν (bgC0 d L N) H.D') H.D').Ψ
            (unitRep (G' := S.G') q.1) q.2) +
        S.hatField (hatCovSqrt S.G' S.a₁ S.ν H.D') ψh)
    let Dcrit := H.dataUCH
      ((fun q =>
        (composeData (S.hG.precedes S.hG' (le_refl (k + 1))) S.a
          (bgFieldC S.G' S.a S.ν (bgC0 d L N) H.D') H.D').Ψ
            (unitRep (G' := S.G') q.1) q.2) +
        S.hatField (hatCovSqrt S.G' S.a₁ S.ν H.D') 0)
    Jr.W2 C g (rawOf H.D', ψh) =
      FcompAtC C.m₀ C.Tm S.a S.ν (Nat.le_succ k) D₀ g -
      FcompAtC C.m₀ C.Tm S.a S.ν (Nat.le_succ k) Dcrit g := by
  exact Jr.W2_datum C H.D' hX _ (Jr.gJ_dataUCH H hX ψh) hψh g _
    (Jr.gJ_dataUCH H hX 0)

include hX in
/-- The first interpolation exponent is the interaction and change of composed energy. -/
theorem W1_dataUCH {ψh : S.EC} (hψh : ∀ p, ‖ψh p‖ ≤ pp) :
    let D₀ := H.dataUCH
      ((fun q =>
        (composeData (S.hG.precedes S.hG' (le_refl (k + 1))) S.a
          (bgFieldC S.G' S.a S.ν (bgC0 d L N) H.D') H.D').Ψ
            (unitRep (G' := S.G') q.1) q.2) +
        S.hatField (hatCovSqrt S.G' S.a₁ S.ν H.D') ψh)
    let Dcrit := H.dataUCH
      ((fun q =>
        (composeData (S.hG.precedes S.hG' (le_refl (k + 1))) S.a
          (bgFieldC S.G' S.a S.ν (bgC0 d L N) H.D') H.D').Ψ
            (unitRep (G' := S.G') q.1) q.2) +
        S.hatField (hatCovSqrt S.G' S.a₁ S.ν H.D') 0)
    Jr.W1 C (rawOf H.D', ψh) =
      -(S.β : ℂ) * interactionV (S.hG.precedes S.hG' (le_refl (k + 1))) S.a S.ν
        (bgMultC S.G' S.a S.ν (bgC0 d L N) H.D')
        (bgFieldC S.G' S.a S.ν (bgC0 d L N) H.D')
        (compTangent S.hG S.hG' (le_refl (k + 1)) S.a
          (bgFieldC S.G' S.a S.ν (bgC0 d L N) H.D') H.D' D₀)
        (bgFieldC (stepG d L N₁ m₁ k ϱ) S.a S.ν (bgC0 d L N) D₀ -
          (S.hG.precedes S.hG' (le_refl (k + 1))).restrictφ
            (bgFieldC S.G' S.a S.ν (bgC0 d L N) H.D')) +
      (EcompAtC C.m₀ C.Tm S.a S.ν (Nat.le_succ k) D₀ -
        EcompAtC C.m₀ C.Tm S.a S.ν (Nat.le_succ k) Dcrit) := by
  exact Jr.W1_datum C H.D' hX _ (Jr.gJ_dataUCH H hX ψh) hψh _
    (Jr.gJ_dataUCH H hX 0)

end Balaban.Fluctuation.StepSetting.JointRep
