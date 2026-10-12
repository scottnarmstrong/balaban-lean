/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.StepComplexSource
public import Balaban.Fluctuation.StepComplexProp26Agree
public import Balaban.Fluctuation.StepRegClass
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The localized energies of the complex step on real data are the landed ones (FLUCTUATION §2.5)

For a real block datum satisfying the premises of the landed step with the margin `p₁ < p⁺` (the
bundle `RayData p⁺`: the hypothesis block (R) of `StepIdentity`), and a class whose exponent
`Φ₁ = Phi1C` is complex-differentiable near the segments (`ClassRegularLocC`):

* `yhatL`, `maskUC_yhat`: the complexification of real fields as a real-linear map, and its
  compatibility with the restriction to a block;
* `RayData.Phi1_eventuallyEq`: near every real shift of the segments, the landed `Φ₁ = Phi1` is the
  restriction of `Phi1C` to real shifts;
* `RayData.fderiv_Phi1C_yhat`: hence the complex derivative of `Phi1C` in a real direction is the
  real derivative of `Phi1`;
* `E1locC_eq`, `E0locC_eq`: `ℰ₁^{(k+1)}(z)` and `ℰ₀^{(k+1)}(z)` of the complex step are the landed
  `E1loc`, `E0loc` (P4 (2.56)-(2.60)).

These statements hold on the real chart only: they are stated with `RayData`.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.SmallField.Def6 Balaban.Background Balaban.Multiscale Balaban.Localization
  Balaban.SmallField Finset MeasureTheory Set

namespace StepSetting

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}
  (S : StepSetting d L N₁ m₁ k N ϱ) (C : StepClass d L N₁ m₁ k N ϱ)

/-- The complexification `ψ ↦ (ψ(b)_i : ℂ)` of the real fields of the unit lattice, as a continuous
real-linear map into the complex fields. -/
noncomputable def yhatL : S.E →L[ℝ] S.EC :=
  LinearMap.toContinuousLinearMap
    { toFun := fun y => yhat y
      map_add' := S.yhat_add
      map_smul' := fun c y => by
        funext q
        simp [yhat] }

theorem yhatL_apply (y : S.E) : S.yhatL y = yhat y := rfl

/-- The restriction to a block commutes with the complexification. -/
theorem maskUC_yhat (z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1)))) (v : S.E) :
    S.maskUC z (yhat v) = yhat (S.maskU z v) := by
  classical
  funext q
  by_cases h : q.1 ∈ S.blockU z
  · simp [maskUC, maskU, yhat, h]
  · simp [maskUC, maskU, yhat, h]

variable {S} {pp : ℝ}

/-- **Real data: near every real shift of the segments, `Φ₁` of the landed step is the restriction
of `Φ₁` of the complex step to real shifts** (`Phi1 = Phi1C ∘ yhat`): the interaction parts agree at
every real field (`VkC_yhat`), and the class parts agree where the real old spin is in `𝒟_ℝ`
(`EcompAtC_eq`), an open condition on the shift. -/
theorem RayData.Phi1_eventuallyEq (R : S.RayData pp) (hlt : S.p₁ < pp) {x : S.E}
    (hx : ‖x‖ ≤ S.p₁) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    S.Phi1 C =ᶠ[nhds (s • S.shiftU x)] fun y => S.Phi1C C (yhat y) := by
  have hopen : IsOpen {y : S.E | ‖S.unshiftU y‖ < pp} :=
    isOpen_lt (continuous_norm.comp contDiff_unshiftU.continuous) continuous_const
  have hy₀ : s • S.shiftU x ∈ {y : S.E | ‖S.unshiftU y‖ < pp} := by
    have := R.unshift_ray hlt hx hs
    simpa using this
  have hdom0 := S.dataU_psi0_domain R.ha₁ R.H R.hδ'0 R.hδ' R.hD'R
  filter_upwards [hopen.mem_nhds hy₀] with y hy
  have hdom : InUnionDomainR (stepG d L N₁ m₁ k ϱ) (bgC1 d L N) S.ν (S.dataU (S.psi0 + y)) := by
    rw [R.psi0_add_eq y]
    exact R.dom (q := ((1 : ℝ), S.unshiftU y)) (by simpa using hy)
  unfold Phi1C Phi1 dEC dE
  rw [S.psi0C_eq R.ha₁ R.H R.hδ'0 R.hδ' R.hD'R, ← S.yhat_add, S.VkC_yhat, S.dataUC_yhat,
    S.dataUC_yhat, EcompAtC_eq R.H _ _ hdom, EcompAtC_eq R.H _ _ hdom0]

/-- **Real data: the complex derivative of `Φ₁ = Phi1C` in a real direction is the real derivative
of the landed `Φ₁ = Phi1`**, at the shifts of the segments, as soon as `Phi1C` is
complex-differentiable there. -/
theorem RayData.fderiv_Phi1C_yhat (R : S.RayData pp) (hlt : S.p₁ < pp) {x : S.E}
    (hx : ‖x‖ ≤ S.p₁) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1)
    (hd : DifferentiableAt ℂ (S.Phi1C C) ((s : ℂ) • S.shiftUC x)) (v : S.E) :
    fderiv ℂ (S.Phi1C C) ((s : ℂ) • S.shiftUC x) (yhat v) =
      fderiv ℝ (S.Phi1 C) (s • S.shiftU x) v := by
  have hχ := (chiU_eq_one_iff _ _ _ _).1 R.hχu
  have hsh : S.shiftUC x = yhat (S.shiftU x) :=
    S.shiftUC_eq R.H R.hδ'0 R.hδ' R.hD'R R.hδ0 hχ R.hfam R.hsm x
  have hpt : (s : ℂ) • S.shiftUC x = S.yhatL (s • S.shiftU x) := by
    rw [hsh, S.yhatL_apply, yhat_smul]
  rw [hpt] at hd ⊢
  have hdC := hd.hasFDerivAt.restrictScalars ℝ
  have hcomp := hdC.comp (s • S.shiftU x) (S.yhatL.hasFDerivAt)
  have hreal : HasFDerivAt (S.Phi1 C)
      (((fderiv ℂ (S.Phi1C C) (S.yhatL (s • S.shiftU x))).restrictScalars ℝ).comp S.yhatL)
      (s • S.shiftU x) :=
    hcomp.congr_of_eventuallyEq (R.Phi1_eventuallyEq C hlt hx hs)
  rw [hreal.fderiv]
  rfl

/-! ### The localized energies -/

/-- **Real data: `ℰ₁^{(k+1)}(z)` of the complex step is the landed `E1loc`** (P4 (2.56)-(2.60)),
for a real block datum with the premises of the landed step (`RayData`, `p₁ < p⁺`) and a class
with `ClassRegularLocC`. -/
theorem E1locC_eq (R : S.RayData pp) (hp₁ : 0 < S.p₁) (hlt : S.p₁ < pp)
    (hc : S.ClassRegularLocC C) (z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1)))) :
    S.E1locC C z = S.E1loc C z := by
  have hχ := (chiU_eq_one_iff _ _ _ _).1 R.hχu
  obtain ⟨h40, hr⟩ := S.margin_small R.hδ0 R.hβ hlt R.hB5 R.hp40 R.hrad
  obtain ⟨O, hO, hcd, hmem⟩ := hc.phi1
  unfold E1locC E1loc
  refine intervalIntegral.integral_congr fun s hs => ?_
  rw [Set.uIcc_of_le zero_le_one] at hs
  refine avgFun_congr_ae ?_ ?_
  · exact (S.ae_ball hp₁).mono fun x hx =>
      S.WoneC_eq C R.ha₁ R.H R.hδ'0 R.hδ' R.hD'R R.hδ0 R.hfam R.hsm R.hχu R.hnorm R.hβ hp₁ R.hB5
        R.hK2 h40 hr hs x hx
  · filter_upwards [S.ae_ball hp₁] with x hx
    have hxn : ‖x‖ ≤ S.p₁ := ((chiFl_eq_one_iff hp₁ x).1 hx).le
    have hd : DifferentiableAt ℂ (S.Phi1C C) ((s : ℂ) • S.shiftUC x) :=
      (hcd.differentiableOn (by norm_num)).differentiableAt (hO.mem_nhds (hmem x hxn s hs))
    have hsh : S.shiftUC x = yhat (S.shiftU x) :=
      S.shiftUC_eq R.H R.hδ'0 R.hδ' R.hD'R R.hδ0 hχ R.hfam R.hsm x
    have hm : S.maskUC z (S.shiftUC x) = yhat (S.maskU z (S.shiftU x)) := by
      rw [hsh, S.maskUC_yhat]
    rw [hm]
    exact R.fderiv_Phi1C_yhat C hlt hxn hs hd _

/-- **Real data: `ℰ₀^{(k+1)}(z)` of the complex step is the landed `E0loc`** (P4 (2.56)), under the
same premises. -/
theorem E0locC_eq (R : S.RayData pp) (hp₁ : 0 < S.p₁) (hlt : S.p₁ < pp)
    (hc : S.ClassRegularLocC C) (z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1)))) :
    S.E0locC C z = S.E0loc C z := by
  unfold E0locC E0loc
  rw [S.logAC_eq R.H R.hδ'0 R.hδ' R.hD'R, E1locC_eq C R hp₁ hlt hc z]

end StepSetting

end Balaban.Fluctuation
