/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.ClassOldEndpointE
public import Balaban.Fluctuation.ClassOldTermInputM
import Mathlib.Tactic.Linarith

/-!
# The endpoint identity of an inherited observable label of a class member

The observable counterpart of `ClassOldEndpointE`.  For a label `(j, y, i, X)` of a class member
whose term generator `𝔹_j(X)` has the strong specification, and a fixed source `g`, the
functional `flComp` of `ℳ^{(j)}_i(y, X; ·, g)` with generator `𝔹_j(X)` over the step set,
evaluated at the physical point, is the term `ℳ^{(j)}_i(y, X; ·, g)` at the composed pair of the
step.  Same proof as for the energy, with `localM` (at the same source on both sides) in place of
`localE`; `composeData_agree_on_X` is shared.

* `classOldEndpointM_complex`: the identity at the complex datum;
* `classOldEndpointM_real`: the same on the real chart of `RayData`, the per-label identity `hid`
  of `oldObsHatMatch_of_label_identity`.
-/

@[expose] public section

namespace Balaban.Fluctuation

open MeasureTheory Balaban Balaban.Localization Balaban.Multiscale
  Balaban.Background Balaban.SmallField Balaban.SmallField.Def6 Balaban.SmallField.Def6v2
  Balaban.SmallField.GsSpec Balaban.Analysis Finset

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}

/-- The complex-datum identity, local-to-whole: the functional of the decoupled expansion for a
label with term generator `Gj` is the term at the whole-level composed pair of the complex step. -/
theorem classOldEndpointM_complex (S : StepSetting d L N₁ m₁ k N ϱ)
    {P : Consts} {Dom : FieldDom d L N₁ m₁ (k + 1) N ϱ} {Tm : Terms d L N₁ m₁ (k + 1) N ϱ}
    (hcl : SFTermClauses P Dom Tm) {j : ℕ} (hj1 : 1 ≤ j) (hjk : j ≤ k) {y : CTorus d L N₁ m₁ (k + 1)} (i : Fin N) (g : Fld d L N₁ m₁ (k + 1) N)
    {X : Set (CTorus d L N₁ m₁ (k + 1))} {Gj : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
    (hS : GsSpecStrong j (hjk.trans (Nat.le_succ k)) X Gj)
    {c BG κ eps Kc Cx c₂ BG₂ δ₁ r₀ δ₃ δfl : ℝ}
    {X₀ X₁f : Finset (CTorus d L N₁ m₁ (k + 1))} {j₁ : ℕ}
    (hB : BgSetting N S.G' (stepG d L N₁ m₁ k ϱ) Gj S.a₁ S.ν c BG κ r₀ eps δ₃ X₀ X₁f j₁)
    (hF : FlSetting N S.G' (stepG d L N₁ m₁ k ϱ) (stepG d L N₁ m₁ k ϱ) S.a₁ S.ν κ BG eps δ₃ Kc Cx
      c₂ BG₂ δ₁ δfl X₁f)
    (hD : XiCData S.G' S.a S.ν (k + 1) 1 eps S.D') (z : S.E) :
    hatFun S.G' S.a₁ S.ν eps S.hG' ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)
        (flComp hB hF (fun raw => Tm.M j y X raw.1 raw.2 g i))
        (rawOf S.D', S.hatC z) =
      Tm.M j y X
        (composedPairAtC S.a S.ν (Nat.le_succ k) j (S.dataUC (S.psiAtC 1 z))).1
        (composedPairAtC S.a S.ν (Nat.le_succ k) j (S.dataUC (S.psiAtC 1 z))).2 g i := by
  have ha : S.a k ≠ 0 :=
    (compWeight_pos (by have := hB.HBp.hL; omega) hB.ha₁ S.hk1).ne'
  have hzl : IsLayerConstant (stepG d L N₁ m₁ k ϱ)
      (hatLift S.G' S.a₁ S.ν S.hG' ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) S.D' (yhat z)) :=
    isLayerConstant_hatLift S.hG S.hG' _ S.D' _
  show hatFun S.G' S.a₁ S.ν eps S.hG' ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)
    (flComp hB hF (fun raw => Tm.M j y X raw.1 raw.2 g i)) (rawOf S.D', yhat z) = _
  rw [hatFun_rawOf S.hG' _ _ hD, flComp_rawOf hB hF _ hD hzl,
    S.flDatumOne_stepG ha BG₂ κ hB.hP hF.hPm z hzl]
  unfold composedPairAtC
  simp only [hjk, ↓reduceDIte]
  refine congrFun ?_ i
  refine hcl.localM j y X _ _ _ _ g g fun x hx => ?_
  have h := composeData_agree_on_X (N := N) (a := S.a) hj1 hjk hS
    (bgFieldC (stepG d L N₁ m₁ k ϱ) S.a S.ν (bgC0 d L N) (S.dataUC (S.psiAtC 1 z)))
    (S.dataUC (S.psiAtC 1 z)) hx
  exact ⟨h.1, h.2, rfl⟩

/-- **The per-label endpoint identity on the real ray** (`hid` of
`oldEnergyHatMatch_of_label_identity`, for a label of a class member with the strong
specification of its term generator): for `‖z‖ < pp`,
`hatFun (flComp Eτ) (rawOf D', hatC z) = Eτ (composedPairAt … (dataU (psiAt 1 z)))`,
`Mτ = ℳ^{(j)}_i(y, X; ·, g)`. -/
theorem classOldEndpointM_real (S : StepSetting d L N₁ m₁ k N ϱ)
    {P : Consts} {Dom : FieldDom d L N₁ m₁ (k + 1) N ϱ} {Tm : Terms d L N₁ m₁ (k + 1) N ϱ}
    (hcl : SFTermClauses P Dom Tm) {pp : ℝ} (R0 : S.RayData pp)
    {j : ℕ} (hj1 : 1 ≤ j) (hjk : j ≤ k) {y : CTorus d L N₁ m₁ (k + 1)} (i : Fin N) (g : Fld d L N₁ m₁ (k + 1) N)
    {X : Set (CTorus d L N₁ m₁ (k + 1))} {Gj : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
    (hS : GsSpecStrong j (hjk.trans (Nat.le_succ k)) X Gj)
    {c BG κ eps Kc Cx c₂ BG₂ δ₁ r₀ δ₃ δfl : ℝ}
    {X₀ X₁f : Finset (CTorus d L N₁ m₁ (k + 1))} {j₁ : ℕ}
    (hB : BgSetting N S.G' (stepG d L N₁ m₁ k ϱ) Gj S.a₁ S.ν c BG κ r₀ eps δ₃ X₀ X₁f j₁)
    (hF : FlSetting N S.G' (stepG d L N₁ m₁ k ϱ) (stepG d L N₁ m₁ k ϱ) S.a₁ S.ν κ BG eps δ₃ Kc Cx
      c₂ BG₂ δ₁ δfl X₁f)
    (hD : XiCData S.G' S.a S.ν (k + 1) 1 eps S.D') {z : S.E} (hz : ‖z‖ < pp) :
    hatFun S.G' S.a₁ S.ν eps S.hG' ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)
        (flComp hB hF (fun raw => Tm.M j y X raw.1 raw.2 g i))
        (rawOf S.D', S.hatC z) =
      Tm.M j y X
        (composedPairAt S.a S.ν (Nat.le_succ k) j (S.dataU (S.psiAt 1 z))).1
        (composedPairAt S.a S.ν (Nat.le_succ k) j (S.dataU (S.psiAt 1 z))).2 g i := by
  have hχ := (chiU_eq_one_iff _ _ _ _).1 R0.hχu
  have hdom : InUnionDomainR (stepG d L N₁ m₁ k ϱ) (bgC1 d L N) S.ν (S.dataU (S.psiAt 1 z)) :=
    R0.dom (q := (1, z)) (by simpa using hz)
  rw [classOldEndpointM_complex S hcl hj1 hjk i g hS hB hF hD z,
    S.psiAtC_eq R0.ha₁ R0.H R0.hδ'0 R0.hδ' R0.hD'R R0.hδ0 hχ R0.hfam R0.hsm, S.dataUC_yhat,
    composedPairAtC_eq_of_bg (theorem72_real R0.H hdom).1 j]

end Balaban.Fluctuation
