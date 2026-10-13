/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.ClassOldDecInputE
public import Balaban.Fluctuation.StepActivityHatLevel
import Mathlib.Tactic.Linarith

/-!
# The endpoint identity of an inherited energy label of a class member

For a label `(j, y, X)` of a class member whose term generator `𝔹_j(X)` has the strong
specification (`GsSpecStrong`), the functional `flComp` of the decoupled expansion, with the term
generator `𝔹_j(X)` over the whole step set `𝔹_k`, evaluated at the physical point, is the term
`β⁻¹ ℰ^{(j)}(y, X; ·)` at the composed pair of the step.  The composed field of `𝔹_j(X)` over
`𝔹_k` agrees on `X` with that of the whole level `levelGS j` (same layer, same block, same
background), and the term reads its field arguments on `X` only (clause `localE`).

* `classOldEndpoint_complex`: the identity at the complex datum;
* `classOldEndpoint_real`: the same on the real chart of `RayData`, the per-label identity `hid`
  of `oldEnergyHatMatch_of_label_identity`.
-/

@[expose] public section

namespace Balaban.Fluctuation

open MeasureTheory Balaban Balaban.Localization Balaban.Multiscale
  Balaban.Background Balaban.SmallField Balaban.SmallField.Def6 Balaban.SmallField.Def6v2
  Balaban.SmallField.GsSpec Balaban.Analysis Finset

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}

/-- **The composed pair of the term generator agrees on `X` with the whole-level composed pair.**
For `GsSpecStrong` of `Gj` for `X`, the field and the source of `composeData` of `Gj` over the
step set, built from any field `φ` on the step set and any datum, are on `X` those of
`composeData` of `levelGS j` over the step set. -/
theorem composeData_agree_on_X {j : ℕ} (hj1 : 1 ≤ j) (hjk : j ≤ k) {a : ℕ → ℝ}
    {X : Set (CTorus d L N₁ m₁ (k + 1))} {Gj : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
    (hS : GsSpecStrong j (hjk.trans (Nat.le_succ k)) X Gj)
    (φ : (stepG d L N₁ m₁ k ϱ).Ω 1 × Fin N → ℂ)
    (D : BgData (stepG d L N₁ m₁ k ϱ) N) {z : CTorus d L N₁ m₁ (k + 1)} (hz : z ∈ X) :
    (composeData (precedes_levelGS hS hjk (Nat.le_succ k)) a φ D).Ψ z =
        (composeData (levelGS_precedes_at hjk (Nat.le_succ k)) a φ D).Ψ z ∧
      (composeData (precedes_levelGS hS hjk (Nat.le_succ k)) a φ D).h z =
        (composeData (levelGS_precedes_at hjk (Nat.le_succ k)) a φ D).h z := by
  have hzG : z ∈ Gj.Ω 1 := hS.subset hz
  have hzL : z ∈ (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ) j
      (hjk.trans (Nat.le_succ k))).Ω 1 := by simp [levelGS, hj1]
  refine ⟨funext fun i => ?_, funext fun i => ?_⟩
  · show composeField Gj _ a φ D.Ψ z i = composeField _ _ a φ D.Ψ z i
    rw [composeField_of_mem _ _ _ hzG, composeField_of_mem _ _ _ hzL, hS.layerEq z hz]
    rfl
  · show (if z ∈ Gj.Ω 1 then D.h z i else 0) = (if z ∈ _ then D.h z i else 0)
    simp [hzG, hzL]

/-- The complex-datum identity, local-to-whole: the functional of the decoupled expansion for a
label with term generator `Gj` is the term at the whole-level composed pair of the complex step. -/
theorem classOldEndpoint_complex (S : StepSetting d L N₁ m₁ k N ϱ)
    {P : Consts} {Dom : FieldDom d L N₁ m₁ (k + 1) N ϱ} {Tm : Terms d L N₁ m₁ (k + 1) N ϱ}
    (hcl : SFTermClauses P Dom Tm) {j : ℕ} (hj1 : 1 ≤ j) (hjk : j ≤ k) {y : CTorus d L N₁ m₁ (k + 1)}
    {X : Set (CTorus d L N₁ m₁ (k + 1))} {Gj : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
    (hS : GsSpecStrong j (hjk.trans (Nat.le_succ k)) X Gj)
    {c BG κ eps Kc Cx c₂ BG₂ δ₁ r₀ δ₃ δfl : ℝ}
    {X₀ X₁f : Finset (CTorus d L N₁ m₁ (k + 1))} {j₁ : ℕ}
    (hB : BgSetting N S.G' (stepG d L N₁ m₁ k ϱ) Gj S.a₁ S.ν c BG κ r₀ eps δ₃ X₀ X₁f j₁)
    (hF : FlSetting N S.G' (stepG d L N₁ m₁ k ϱ) (stepG d L N₁ m₁ k ϱ) S.a₁ S.ν κ BG eps δ₃ Kc Cx
      c₂ BG₂ δ₁ δfl X₁f)
    (hD : XiCData S.G' S.a S.ν (k + 1) 1 eps S.D') (z : S.E) :
    hatFun S.G' S.a₁ S.ν eps S.hG' ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)
        (flComp hB hF (fun raw => (S.β : ℂ)⁻¹ * Tm.E j y X raw.1 raw.2))
        (rawOf S.D', S.hatC z) =
      (S.β : ℂ)⁻¹ * Tm.E j y X
        (composedPairAtC S.a S.ν (Nat.le_succ k) j (S.dataUC (S.psiAtC 1 z))).1
        (composedPairAtC S.a S.ν (Nat.le_succ k) j (S.dataUC (S.psiAtC 1 z))).2 := by
  have ha : S.a k ≠ 0 :=
    (compWeight_pos (by have := hB.HBp.hL; omega) hB.ha₁ S.hk1).ne'
  have hzl : IsLayerConstant (stepG d L N₁ m₁ k ϱ)
      (hatLift S.G' S.a₁ S.ν S.hG' ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) S.D' (yhat z)) :=
    isLayerConstant_hatLift S.hG S.hG' _ S.D' _
  show hatFun S.G' S.a₁ S.ν eps S.hG' ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)
    (flComp hB hF (fun raw => (S.β : ℂ)⁻¹ * Tm.E j y X raw.1 raw.2)) (rawOf S.D', yhat z) = _
  rw [hatFun_rawOf S.hG' _ _ hD, flComp_rawOf hB hF _ hD hzl,
    S.flDatumOne_stepG ha BG₂ κ hB.hP hF.hPm z hzl]
  unfold composedPairAtC
  simp only [hjk, ↓reduceDIte]
  congr 1
  refine hcl.localE j y X _ _ _ _ fun x hx => ?_
  have h := composeData_agree_on_X (N := N) (a := S.a) hj1 hjk hS
    (bgFieldC (stepG d L N₁ m₁ k ϱ) S.a S.ν (bgC0 d L N) (S.dataUC (S.psiAtC 1 z)))
    (S.dataUC (S.psiAtC 1 z)) hx
  exact h

/-- **The per-label endpoint identity on the real ray** (`hid` of
`oldEnergyHatMatch_of_label_identity`, for a label of a class member with the strong
specification of its term generator): for `‖z‖ < pp`,
`hatFun (flComp Eτ) (rawOf D', hatC z) = Eτ (composedPairAt … (dataU (psiAt 1 z)))`,
`Eτ = β⁻¹ ℰ^{(j)}(y, X; ·)`. -/
theorem classOldEndpoint_real (S : StepSetting d L N₁ m₁ k N ϱ)
    {P : Consts} {Dom : FieldDom d L N₁ m₁ (k + 1) N ϱ} {Tm : Terms d L N₁ m₁ (k + 1) N ϱ}
    (hcl : SFTermClauses P Dom Tm) {pp : ℝ} (R0 : S.RayData pp)
    {j : ℕ} (hj1 : 1 ≤ j) (hjk : j ≤ k) {y : CTorus d L N₁ m₁ (k + 1)}
    {X : Set (CTorus d L N₁ m₁ (k + 1))} {Gj : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
    (hS : GsSpecStrong j (hjk.trans (Nat.le_succ k)) X Gj)
    {c BG κ eps Kc Cx c₂ BG₂ δ₁ r₀ δ₃ δfl : ℝ}
    {X₀ X₁f : Finset (CTorus d L N₁ m₁ (k + 1))} {j₁ : ℕ}
    (hB : BgSetting N S.G' (stepG d L N₁ m₁ k ϱ) Gj S.a₁ S.ν c BG κ r₀ eps δ₃ X₀ X₁f j₁)
    (hF : FlSetting N S.G' (stepG d L N₁ m₁ k ϱ) (stepG d L N₁ m₁ k ϱ) S.a₁ S.ν κ BG eps δ₃ Kc Cx
      c₂ BG₂ δ₁ δfl X₁f)
    (hD : XiCData S.G' S.a S.ν (k + 1) 1 eps S.D') {z : S.E} (hz : ‖z‖ < pp) :
    hatFun S.G' S.a₁ S.ν eps S.hG' ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)
        (flComp hB hF (fun raw => (S.β : ℂ)⁻¹ * Tm.E j y X raw.1 raw.2))
        (rawOf S.D', S.hatC z) =
      (S.β : ℂ)⁻¹ * Tm.E j y X
        (composedPairAt S.a S.ν (Nat.le_succ k) j (S.dataU (S.psiAt 1 z))).1
        (composedPairAt S.a S.ν (Nat.le_succ k) j (S.dataU (S.psiAt 1 z))).2 := by
  have hχ := (chiU_eq_one_iff _ _ _ _).1 R0.hχu
  have hdom : InUnionDomainR (stepG d L N₁ m₁ k ϱ) (bgC1 d L N) S.ν (S.dataU (S.psiAt 1 z)) :=
    R0.dom (q := (1, z)) (by simpa using hz)
  rw [classOldEndpoint_complex S hcl hj1 hjk hS hB hF hD z,
    S.psiAtC_eq R0.ha₁ R0.H R0.hδ'0 R0.hδ' R0.hD'R R0.hδ0 hχ R0.hfam R0.hsm, S.dataUC_yhat,
    composedPairAtC_eq_of_bg (theorem72_real R0.H hdom).1 j]

end Balaban.Fluctuation
