/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.StepTaylorComplex
public import Balaban.Fluctuation.StepActivityWitness
public import Balaban.Fluctuation.StepRegClass
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The complex-analytic extension of the potential and of the background field in the old spin

`exists_analytic_ext`: one function `P` of the complex old spin `w` (the displacement from
`ψ^{(k)}`), analytic at every `w` whose datum `dataUC (ψ^{(k)} + w)` lies in the union domain, with
`P w = V^{(k)}(ψ^{(k)} + w)` (`VkC`) on the domain; and likewise for the background field.  This is
the multi-directional form of `exists_analyticAt_VkC_rayC`.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban.SmallField.Def6 Balaban.Background Balaban.Multiscale Balaban.Localization
  Balaban.SmallField Finset MeasureTheory Set Matrix Filter Topology

namespace StepSetting

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}
  (S : StepSetting d L N₁ m₁ k N ϱ)

/-- The datum of the old spin `ψ^{(k)} + w` lies in the union domain of the lower level. -/
def InDom (w : S.EC) : Prop :=
  InUnionDomainC (stepG d L N₁ m₁ k ϱ) (bgC0 d L N) (bgC1 d L N) S.ν (S.dataUC (S.psi0C + w))

theorem exists_analytic_ext (ha₁ : 0 < S.a₁) (H : BgHyp d L (k + 1) ϱ S.a S.ν)
    (hD2 : InUnionDomainC S.G' (bgC0 d L N) (thm73C2 d L N) S.ν S.D') :
    ∃ (P : S.EC → ℂ) (B : S.EC → (stepG d L N₁ m₁ k ϱ).Ω 1 × Fin N → ℂ),
      (∀ w₀, S.InDom w₀ → AnalyticAt ℂ P w₀ ∧ ∀ r, AnalyticAt ℂ (fun w => B w r) w₀) ∧
      ∀ w, S.InDom w → S.VkC (S.psi0C + w) = P w ∧
        bgFieldC (stepG d L N₁ m₁ k ϱ) S.a S.ν (bgC0 d L N) (S.dataUC (S.psi0C + w)) = B w := by
  obtain ⟨F, hF, hFe⟩ := theorem72_analytic (G := stepG d L N₁ m₁ k ϱ) (a := S.a) (ν := S.ν) H
  let raw : S.EC → RawData d L (N₁ * L ^ m₁) (k + 1) N := fun w =>
    ((S.dataUC (S.psi0C + w)).Ψ, (S.dataUC (S.psi0C + w)).h)
  have hrawan : ∀ w₀, AnalyticAt ℂ raw w₀ := by
    intro w₀
    refine AnalyticAt.prod ?_ ?_
    · refine analyticAt_pi_iff.2 fun y => analyticAt_pi_iff.2 fun i => ?_
      simp only [dataUC_Ψ]
      have h1 : AnalyticAt ℂ (fun w : S.EC => w (unitPt S.hG' y, i)) w₀ :=
        (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : S.U × Fin N => ℂ)
          (unitPt S.hG' y, i)).analyticAt w₀
      exact analyticAt_const.add h1
    · refine analyticAt_pi_iff.2 fun y => analyticAt_pi_iff.2 fun i => ?_
      simp only [dataUC_h]
      exact analyticAt_const
  obtain ⟨δs, Φ, St, hΦ⟩ := base_standing ha₁ S.hG S.hG' (le_refl (k + 1)) H H S.D' hD2
  have hΦ' : restrictField (stepG d L N₁ m₁ k ϱ) Φ =
      fieldBase (S.hG.precedes S.hG' (le_refl (k + 1)))
        (bgFieldC S.G' S.a S.ν (bgC0 d L N) S.D') :=
    funext fun x => funext fun i => hΦ x i
  refine ⟨fun w => interactionV (S.hG.precedes S.hG' (le_refl (k + 1))) S.a S.ν
    (bgMultC S.G' S.a S.ν (bgC0 d L N) S.D') (bgFieldC S.G' S.a S.ν (bgC0 d L N) S.D')
    (liftC S.hG' w)
    ((F (raw w)).1 - (S.hG.precedes S.hG' (le_refl (k + 1))).restrictφ
      (bgFieldC S.G' S.a S.ν (bgC0 d L N) S.D')), fun w => (F (raw w)).1, ?_, ?_⟩
  · intro w₀ hw₀
    have hFat : AnalyticAt ℂ F (raw w₀) := hF _ ⟨_, hw₀, rfl⟩
    have hFraw : AnalyticAt ℂ (fun w => F (raw w)) w₀ := hFat.comp (hrawan w₀)
    refine ⟨?_, fun r => ?_⟩
    · refine analyticAt_interactionV (S.hG.precedes S.hG' (le_refl (k + 1))) S.a S.ν
        (αF := fun _ => bgMultC S.G' S.a S.ν (bgC0 d L N) S.D')
        (φF := fun _ => bgFieldC S.G' S.a S.ν (bgC0 d L N) S.D')
        (ψF := fun w => liftC S.hG' w)
        (φ'F := fun w => (F (raw w)).1 - (S.hG.precedes S.hG' (le_refl (k + 1))).restrictφ
          (bgFieldC S.G' S.a S.ν (bgC0 d L N) S.D'))
        (fun y => analyticAt_const) (fun r => analyticAt_const) (fun y i => ?_) (fun r => ?_)
        ?_ ?_
      · have h1 : AnalyticAt ℂ (fun w : S.EC => w (unitPt S.hG' y, i)) w₀ :=
          (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : S.U × Fin N => ℂ)
            (unitPt S.hG' y, i)).analyticAt w₀
        exact h1
      · exact (analyticAt_pi_iff.1 (analyticAt_fst.comp hFraw) r).sub analyticAt_const
      · exact dirichletOperator_isUnit (stepG d L N₁ m₁ k ϱ) St.pos St.mass St.weights _ St.alpha
      · show IsUnit (constraintForm (opHk (S.hG.precedes S.hG' (le_refl (k + 1))) S.a S.ν
          (bgMultC S.G' S.a S.ν (bgC0 d L N) S.D'))⁻¹
          (fieldBase (S.hG.precedes S.hG' (le_refl (k + 1)))
            (bgFieldC S.G' S.a S.ν (bgC0 d L N) S.D')))
        rw [← hΦ']
        exact constraintForm_isUnit St
    · exact analyticAt_pi_iff.1 (analyticAt_fst.comp hFraw) r
  · intro w hw
    have hFw := hFe _ hw
    refine ⟨?_, ?_⟩
    · unfold VkC
      have : compTangent S.hG S.hG' (le_refl (k + 1)) S.a
          (bgFieldC S.G' S.a S.ν (bgC0 d L N) S.D') S.D' (S.dataUC (S.psi0C + w)) =
          liftC S.hG' w := by
        rw [S.compTangent_dataUC]; congr 1; abel
      rw [this]
      show _ = interactionV _ _ _ _ _ _ ((F (raw w)).1 - _)
      rw [show F (raw w) = _ from hFw]
    · exact (congrArg Prod.fst hFw).symm

/-- `yhat` as a continuous `ℝ`-linear map. -/
noncomputable def yhatL : S.E →L[ℝ] S.EC :=
  LinearMap.toContinuousLinearMap
    { toFun := fun x => yhat x
      map_add' := S.yhat_add
      map_smul' := fun c y => by simpa [Complex.real_smul] using S.yhat_smul c y }

theorem yhatL_apply (x : S.E) : S.yhatL x = yhat x := rfl

variable {S} {pp : ℝ}

/-- For `‖ψ̂'‖ < p⁺` after unshifting, the complexification of the real displacement `y` has its
datum in the union domain. -/
theorem RayData.inDom_yhat (R : S.RayData pp) {y : S.E} (hy : ‖S.unshiftU y‖ < pp) :
    S.InDom (yhat y) := by
  unfold InDom
  have h1 : S.psi0C + yhat y = yhat (S.psiAt 1 (S.unshiftU y)) := by
    rw [← R.psi0_add_eq, S.psi0C_eq R.ha₁ R.H R.hδ'0 R.hδ' R.hD'R, S.yhat_add]
  rw [h1, S.dataUC_yhat]
  exact S.inUnionDomainC_of_R' R.H (R.dom (q := (1, S.unshiftU y)) (by simpa using hy))

theorem Phi1_zeroClass {S : StepSetting d L N₁ m₁ k N ϱ} (y : S.E) :
    S.Phi1 (zeroClass d L N₁ m₁ k N ϱ) y = -(S.β : ℂ) * S.Vk (S.psi0 + y) := by
  unfold Phi1 dE
  show -(S.β : ℂ) * _ + (EcompAt 0 (zeroTerms d L N₁ m₁ (k + 1) N ϱ) S.a S.ν (Nat.le_succ k) _ -
    EcompAt 0 (zeroTerms d L N₁ m₁ (k + 1) N ϱ) S.a S.ν (Nat.le_succ k) _) = _
  rw [EcompAt_zero, EcompAt_zero]; simp

theorem RayData.fderiv_Phi1_zeroClass {S : StepSetting d L N₁ m₁ k N ϱ} {pp : ℝ}
    (R : S.RayData pp) {P : S.EC → ℂ}
    (hP : ∀ w, S.InDom w → S.VkC (S.psi0C + w) = P w)
    (hPa : ∀ w, S.InDom w → AnalyticAt ℂ P w) {y₀ : S.E} (hy₀ : ‖S.unshiftU y₀‖ < pp) (m : S.E) :
    (fderiv ℝ (S.Phi1 (zeroClass d L N₁ m₁ k N ϱ)) y₀) m =
      -(S.β : ℂ) * (fderiv ℂ P (yhat y₀)) (yhat m) := by
  have hopen : IsOpen {y : S.E | ‖S.unshiftU y‖ < pp} :=
    isOpen_lt (contDiff_unshiftU.continuous.norm) continuous_const
  have hev : S.Phi1 (zeroClass d L N₁ m₁ k N ϱ) =ᶠ[nhds y₀]
      fun y => -(S.β : ℂ) * P (S.yhatL y) := by
    filter_upwards [hopen.mem_nhds hy₀] with y hy
    rw [Phi1_zeroClass, S.yhatL_apply, ← hP _ (R.inDom_yhat hy)]
    have e : S.Vk (S.psi0 + y) = S.VkC (S.psi0C + yhat y) := by
      rw [← S.VkC_yhat, S.yhat_add, S.psi0C_eq R.ha₁ R.H R.hδ'0 R.hδ' R.hD'R]
    rw [e]
  rw [hev.fderiv_eq]
  have h1 : HasFDerivAt P (fderiv ℂ P (yhat y₀)) (S.yhatL y₀) :=
    ((hPa _ (R.inDom_yhat hy₀)).differentiableAt.hasFDerivAt)
  have h2 : HasFDerivAt (fun y => P (S.yhatL y))
      ((fderiv ℂ P (yhat y₀)).restrictScalars ℝ ∘L S.yhatL) y₀ :=
    (h1.restrictScalars ℝ).comp y₀ S.yhatL.hasFDerivAt
  have h3 := h2.const_mul (-(S.β : ℂ))
  rw [h3.fderiv]
  rfl

end StepSetting

end Balaban.Fluctuation
