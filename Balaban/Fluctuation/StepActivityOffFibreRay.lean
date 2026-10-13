/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.StepSettingH
public import Balaban.Background.Def5Response
import Balaban.Fluctuation.StepTaylorComplex
import Balaban.Fluctuation.StepComplexOffFibreJoint

/-!
# Affine rays at a free block datum

The old datum obtained from a free block field varies affinely with the old spin. This is the
datum identity needed to apply the background response theorem along the fluctuation ray.
-/

@[expose] public section

namespace Balaban.Fluctuation.StepSettingH

open Balaban Balaban.Background Balaban.Multiscale Balaban.Localization

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}
  {S : StepSetting d L N₁ m₁ k N ϱ}

/-- At any incoming field, the old datum follows the affine line of a spin perturbation with
zero field component. -/
theorem dataUCH_add_smul (H : StepSettingH S) (ψ v : S.EC) (z : ℂ) :
    H.dataUCH (ψ + z • v) = (H.dataUCH ψ).lineAt
      (BgData.clip (stepG d L N₁ m₁ k ϱ) (liftC S.hG' v) (fun _ _ => 0)
        (isLayerConstant_liftC S.hG S.hG' v)
        (by intro n _hn1 _hnk x _hx x' _hx'; rfl)) z := by
  refine BgData.eq_of_raw (Prod.ext ?_ ?_)
  · funext x i
    dsimp only [rawOf]
    rw [H.dataUCH_Ψ]
    simp [BgData.lineAt, BgData.clip, liftC_apply,
      (mem_dataSites _).2 (Or.inl (S.hG x).1)]
    exact (H.dataUCH_Ψ ψ x i).symm
  · funext x i
    dsimp only [rawOf]
    rw [H.dataUCH_h]
    simp [BgData.lineAt, BgData.clip, (S.hG x).1]
    exact (H.dataUCH_h ψ x i).symm

/-- The critical old datum lies in the background response domain for every incoming field in
the chart. -/
theorem baseDomainC_of_chart (H : StepSettingH S) (ha₁ : 0 < S.a₁)
    (HB : BgHyp d L (k + 1) ϱ S.a S.ν)
    (hD2 : InUnionDomainC S.G' (bgC0 d L N) (thm73C2 d L N) S.ν H.D') :
    InUnionDomainC (stepG d L N₁ m₁ k ϱ) (bgC0 d L N) (bgC2 d L N) S.ν
      (H.dataUCH (fun q =>
        (composeData (S.hG.precedes S.hG' (le_refl (k + 1))) S.a
          (bgFieldC S.G' S.a S.ν (bgC0 d L N) H.D') H.D').Ψ
            (unitRep (G' := S.G') q.1) q.2)) := by
  rw [H.dataUCH_psi0C]
  exact theorem73_complex_small ha₁ HB HB (S.hG.precedes S.hG' (le_refl (k + 1))) hD2

/-- At the critical old spin, the lower background equals the restriction of the incoming
background for an arbitrary chart field. -/
theorem lower_bg_psi0C (H : StepSettingH S) (ha₁ : 0 < S.a₁)
    (HB : BgHyp d L (k + 1) ϱ S.a S.ν)
    (hD1 : InUnionDomainC S.G' (bgC0 d L N) (thm73C1 d L N) S.ν H.D') :
    let B := composeData (S.hG.precedes S.hG' (le_refl (k + 1))) S.a
      (bgFieldC S.G' S.a S.ν (bgC0 d L N) H.D') H.D'
    bgFieldC (stepG d L N₁ m₁ k ϱ) S.a S.ν (bgC0 d L N) B =
        (S.hG.precedes S.hG' (le_refl (k + 1))).restrictφ
          (bgFieldC S.G' S.a S.ν (bgC0 d L N) H.D') ∧
      bgMultC (stepG d L N₁ m₁ k ϱ) S.a S.ν (bgC0 d L N) B =
        (S.hG.precedes S.hG' (le_refl (k + 1))).restrictα
          (bgMultC S.G' S.a S.ν (bgC0 d L N) H.D') := by
  obtain ⟨-, -, hfield, hmult, -⟩ :=
    criticalPoint_complex ha₁ S.hG S.hG' (le_refl (k + 1)) HB HB H.D' hD1
  exact ⟨hfield, hmult⟩

/-- A spin perturbation with zero field component has the expected source in the background
response equation. -/
theorem source_zeroField_ray (v : S.EC) :
    source (stepG d L N₁ m₁ k ϱ) S.a S.ν
      (BgData.clip (stepG d L N₁ m₁ k ϱ) (liftC S.hG' v) (fun _ _ => 0)
        (isLayerConstant_liftC S.hG S.hG' v)
        (by intro n _hn1 _hnk x _hx x' _hx'; rfl)) =
      qStar (stepG d L N₁ m₁ k ϱ) S.a (liftC S.hG' v) := by
  funext p
  unfold source
  rw [S.boundaryTerm_stepG]
  have hh : (BgData.clip (stepG d L N₁ m₁ k ϱ) (liftC S.hG' v) (fun _ _ => 0)
      (isLayerConstant_liftC S.hG S.hG' v)
      (by intro n _hn1 _hnk x _hx x' _hx'; rfl)).h = fun _ _ => 0 := by
    funext y i
    simp [BgData.clip, (S.hG y).1]
  rw [hh]
  have hΨ : (BgData.clip (stepG d L N₁ m₁ k ϱ) (liftC S.hG' v) (fun _ _ => 0)
      (isLayerConstant_liftC S.hG S.hG' v)
      (by intro n _hn1 _hnk x _hx x' _hx'; rfl)).Ψ = liftC S.hG' v := by
    funext y i
    simp [BgData.clip, (mem_dataSites _).2 (Or.inl (S.hG y).1)]
  rw [hΨ]
  simp

/-- Linear response of the lower background along a spin ray at a free block field. -/
theorem hasDerivAt_bgC_ray (H : StepSettingH S) (ha₁ : 0 < S.a₁)
    (HB : BgHyp d L (k + 1) ϱ S.a S.ν)
    (hD2 : InUnionDomainC S.G' (bgC0 d L N) (thm73C2 d L N) S.ν H.D')
    (v : S.EC) :
    let B := composeData (S.hG.precedes S.hG' (le_refl (k + 1))) S.a
      (bgFieldC S.G' S.a S.ν (bgC0 d L N) H.D') H.D'
    let ψ₀ : S.EC := fun q => B.Ψ (unitRep (G' := S.G') q.1) q.2
    HasDerivAt (fun z : ℂ =>
      bgFieldC (stepG d L N₁ m₁ k ϱ) S.a S.ν (bgC0 d L N)
        (H.dataUCH (ψ₀ + z • v)) -
        (S.hG.precedes S.hG' (le_refl (k + 1))).restrictφ
          (bgFieldC S.G' S.a S.ν (bgC0 d L N) H.D'))
      (phiOne (S.hG.precedes S.hG' (le_refl (k + 1))) S.a S.ν
        (bgMultC S.G' S.a S.ν (bgC0 d L N) H.D')
        (bgFieldC S.G' S.a S.ν (bgC0 d L N) H.D')
        (qStar (stepG d L N₁ m₁ k ϱ) S.a (liftC S.hG' v))) 0 := by
  dsimp only
  let B := composeData (S.hG.precedes S.hG' (le_refl (k + 1))) S.a
    (bgFieldC S.G' S.a S.ν (bgC0 d L N) H.D') H.D'
  let ψ₀ : S.EC := fun q => B.Ψ (unitRep (G' := S.G') q.1) q.2
  let R : BgData (stepG d L N₁ m₁ k ϱ) N :=
    BgData.clip (stepG d L N₁ m₁ k ϱ) (liftC S.hG' v) (fun _ _ => 0)
      (isLayerConstant_liftC S.hG S.hG' v)
      (by intro n _hn1 _hnk x _hx x' _hx'; rfl)
  have hbase : InUnionDomainC (stepG d L N₁ m₁ k ϱ) (bgC0 d L N) (bgC2 d L N) S.ν
      (H.dataUCH ψ₀) := H.baseDomainC_of_chart ha₁ HB hD2
  obtain ⟨φd, αd, h1, -, -, h4, -⟩ := theorem72_linearResponse HB hbase R
  have h3 : HasDerivAt (fun z : ℂ =>
      bgFieldC (stepG d L N₁ m₁ k ϱ) S.a S.ν (bgC0 d L N)
        (H.dataUCH (ψ₀ + z • v))) φd 0 := by
    have e : (fun z : ℂ =>
        bgFieldC (stepG d L N₁ m₁ k ϱ) S.a S.ν (bgC0 d L N)
          (H.dataUCH (ψ₀ + z • v))) =
        fun z : ℂ => bgFieldC (stepG d L N₁ m₁ k ϱ) S.a S.ν (bgC0 d L N)
          ((H.dataUCH ψ₀).lineAt R z) := by
      funext z
      rw [H.dataUCH_add_smul]
    rw [e]
    exact h1
  obtain ⟨hF, hM⟩ := H.lower_bg_psi0C ha₁ HB
    (hD2.mono (thm73C2_le_thm73C1 d L N))
  change _ = _ at hF hM
  rw [← H.dataUCH_psi0C] at hF hM
  convert h3.sub_const _ using 1
  rw [h4, source_zeroField_ray]
  unfold phiOne opHk fieldBase bgOp bgVec
  rw [hM]
  congr 3
  funext x i
  exact (congrFun hF _).symm

end Balaban.Fluctuation.StepSettingH

namespace Balaban.Fluctuation.StepSetting.JointRep

open Balaban Balaban.Background Balaban.Multiscale Balaban.Localization

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ eps pp : ℝ}
  {S : StepSetting d L N₁ m₁ k N ϱ}

/-- The first interpolation exponent vanishes at the critical spin for every chart field. -/
theorem W1_zero_freeDatum (Jr : S.JointRep eps pp) (H : StepSettingH S)
    (C : StepClass d L N₁ m₁ k N ϱ)
    {c BG κ Kc Cx c₂ BG₂ δ₁ : ℝ}
    (hC : FlCore N S.G' (stepG d L N₁ m₁ k ϱ) S.a₁ S.ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
    (ha₁ : 0 < S.a₁) (hc7 : c7 d L N BG κ ≤ thm73C3 d L N)
    (hX : XiCData S.G' S.a S.ν (k + 1) 1 eps H.D') :
    Jr.W1 C (rawOf H.D', 0) = 0 := by
  unfold W1
  rw [Jr.VJ_zero H hC ha₁ hc7 hX]
  ring

end Balaban.Fluctuation.StepSetting.JointRep
