/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.RenormThetaDatum
public import Balaban.Fluctuation.RenormExpCauchy
public import Balaban.Fluctuation.RenormDomainParams
public import Balaban.Fluctuation.DetOutputTerms
public import Balaban.Localization.I5FluctChain
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The renormalized datum lies in the step chart at a slightly larger radius

For `D` in the class `XiCOneReal` at radius `εren` and `‖ξ‖ < r₀`, the renormalized datum
`renThetaDatum S εren D ξ = ((1 + ζ) Ψ, h)` is the datum `D` perturbed by the layer-constant
function `δΨ = ζ Ψ`, which has size at most `(3/2) εren r₀` on the data sites.  The perturbation
theorem `xiCData_perturb` therefore places it in the chart `XiCData` at radius
`εren + xiK2 · (3/2) εren r₀`.

## Main results

* `renTheta_delta_layerConst`, `renTheta_delta_bound`: the perturbation is layer-constant and small.
* `renTheta_eq_perturbData`: the perturbed datum is the renormalized datum.
* `ThetaChartMargin`: the numerical hypotheses of `xiCData_perturb` at the class radius.
* `renE0_theta_domain`: the chart inclusion.
* `exists_renDetGrouped_ambient`: an analytic function on all raw data times parameters, analytic
  on the expansion domain, equal there to the regrouped determinant terms at the renormalized
  datum.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Localization

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}
variable {S : StepSetting d L N₁ m₁ k N ϱ}

/-- The perturbation `δΨ = ζ Ψ` of the renormalized datum is layer-constant. -/
theorem renTheta_delta_layerConst (ε : ℝ) (D : BgData S.G' N) (ξ : Fin 3 → ℂ) :
    IsLayerConstant S.G' (fun x i => renZeta ε ξ * D.Ψ x i) := by
  intro n hn hk x hx x' hx'
  funext i
  show renZeta ε ξ * D.Ψ x' i = renZeta ε ξ * D.Ψ x i
  rw [D.Ψ_layerConst n hn hk x hx x' hx']

/-- The perturbation `δΨ = ζ Ψ` has size at most `(3/2) εren r₀` on the data sites. -/
theorem renTheta_delta_bound {εren r₀ : ℝ}
    (H : BgHyp d L (k + 1) ϱ S.a S.ν) (hε : 0 < εren)
    (hsm : (4 * d + 6) * ((2 * d + 1) * εren) ≤ 1) (hc1 : xiC1 d * εren ≤ bgC1 d L N)
    {D : BgData S.G' N} (hD : XiCOneReal S.G' S.a S.ν εren D) {ξ : Fin 3 → ℂ}
    (hξ : ‖ξ‖ < r₀) :
    ∀ x ∈ dataSites S.G', vn (fun i => renZeta εren ξ * D.Ψ x i) ≤ (3 / 2) * εren * r₀ := by
  intro x hx
  have h32 := (XiCOneReal.factors H hε hsm hc1 hD).2.2.2 x hx
  rw [vn_smul_complex]
  have hr0 : 0 ≤ r₀ := (norm_nonneg ξ).trans hξ.le
  have hz := norm_renZeta_le hε.le ξ
  have hv := vn_nonneg (D.Ψ x)
  calc ‖renZeta εren ξ‖ * vn (D.Ψ x) ≤ (εren * r₀) * (3 / 2) :=
        mul_le_mul (hz.trans (mul_le_mul_of_nonneg_left hξ.le hε.le)) h32 hv
          (by positivity)
    _ = (3 / 2) * εren * r₀ := by ring

/-- **The bridge.**  The datum perturbed by `δΨ = ζ Ψ` is the renormalized datum. -/
theorem renTheta_eq_perturbData (ε : ℝ) (D : BgData S.G' N) (ξ : Fin 3 → ℂ) :
    perturbData S.G' D (fun x i => renZeta ε ξ * D.Ψ x i) (renTheta_delta_layerConst ε D ξ) =
      renThetaDatum S ε D ξ := by
  apply BgData.eq_of_raw
  refine Prod.ext ?_ rfl
  funext x i
  show D.Ψ x i + (if x ∈ dataSites S.G' then renZeta ε ξ * D.Ψ x i else 0) =
    (1 + renZeta ε ξ) * D.Ψ x i
  by_cases hx : x ∈ dataSites S.G'
  · simp only [hx, ite_true]; ring
  · have h0 := congrFun (D.Ψ_zero x hx) i
    simp only [hx, ite_false]
    rw [show D.Ψ x i = 0 from h0]; ring

/-- **The numerical margin of the chart inclusion**: precisely the numerical premises of
`xiCData_perturb` with `δ₃ = (3/2) εren r₀`, together with the new radius. -/
structure ThetaChartMargin (d L N : ℕ) [NeZero L] (εren εstep r₀ : ℝ) : Prop where
  ε_pos : 0 < εren
  r_pos : 0 < r₀
  δ_nonneg : 0 ≤ (3 / 2 : ℝ) * εren * r₀
  δ_one : (3 / 2 : ℝ) * εren * r₀ ≤ 1
  small : (4 * d + 6) * ((2 * d + 1) * εren) ≤ 1
  data : xiC1 d * εren + 5 * ((3 / 2 : ℝ) * εren * r₀) ≤ bgC1 d L N
  star : (3 / 2 : ℝ) * εren * r₀ ≤ deltaStar d L N
  K₁ : bgK1 d L N * (xiC1 d * εren) ≤ deltaStar d L N
  c₀ : bgK1 d L N * (xiC1 d * εren) + cK2 d L N * ((3 / 2 : ℝ) * εren * r₀) < bgC0 d L N
  radius : εstep = εren + xiK2 d L N * ((3 / 2 : ℝ) * εren * r₀)

/-- **The renormalized datum lies in the step chart.**  For `D` in `XiCOneReal` at radius `εren`
and `‖ξ‖ < r₀`, the datum `renThetaDatum S εren D ξ` lies in `XiCData` at radius `εstep`. -/
theorem renE0_theta_domain (S : StepSetting d L N₁ m₁ k N ϱ)
    (H : BgHyp d L (k + 1) ϱ S.a S.ν) (εren εstep r₀ : ℝ)
    (hM : ThetaChartMargin d L N εren εstep r₀)
    (D : BgData S.G' N) (hD : XiCOneReal S.G' S.a S.ν εren D)
    (ξ : Fin 3 → ℂ) (hξ : ‖ξ‖ < r₀) :
    XiCData S.G' S.a S.ν (k + 1) 1 εstep (renThetaDatum S εren D ξ) := by
  have hc1 : xiC1 d * εren ≤ bgC1 d L N := by linarith [hM.data, hM.δ_nonneg]
  have h := xiCData_perturb H hM.δ_nonneg hM.δ_one hM.small hM.data hM.star hM.K₁ hM.c₀
    (renTheta_delta_layerConst εren D ξ)
    (renTheta_delta_bound H hM.ε_pos hM.small hc1 hD hξ)
    (xiCData_of_xiCOneReal hD)
  rw [renTheta_eq_perturbData, ← hM.radius] at h
  exact h

/-- **The ambient analytic extension of the regrouped determinant terms.**  For a record `E` at the
chart radius `εstep`, a hull `X`, there is a function on all raw data times parameters which is
analytic (in the ambient sense) at every point of the expansion domain of `XiCOneReal` at radius
`r₀`, and equals there the regrouped determinant terms at the renormalized datum. -/
theorem exists_renDetGrouped_ambient {m₀ : ℕ} {z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1)))}
    {εstep κ'' cdet : ℝ}
    (E : DetExpansionLocC S m₀ z εstep κ'' cdet)
    (H : BgHyp d L (k + 1) ϱ S.a S.ν) (εren r₀ : ℝ)
    (hM : ThetaChartMargin d L N εren εstep r₀)
    (hm : m₀ = 1)
    (X : Set (CTorus d L N₁ m₁ (k + 1))) :
    ∃ F : RawData d L (N₁ * L ^ m₁) (k + 1) N × (Fin 3 → ℂ) → ℂ,
      AnalyticOnNhd ℂ F (expDom S.G' (XiCOneReal S.G' S.a S.ν εren) r₀) ∧
      ∀ (D : BgData S.G' N) (ξ : Fin 3 → ℂ), XiCOneReal S.G' S.a S.ν εren D → ‖ξ‖ < r₀ →
        F ((D.Ψ, D.h), ξ) = E.detGrouped (renThetaDatum S εren D ξ) X := by
  subst hm
  choose A hAan hAeq using E.analyticAt_raw
  refine ⟨fun q => ∑ T ∈ detCollarFibre 1 X,
    A T ((fun x i => (1 + renZeta εren q.2) * q.1.1 x i), q.1.2), ?_, ?_⟩
  · rintro ⟨p, ξ'⟩ ⟨D, hD, hp, hξ⟩
    simp only at hp hξ
    subst hp
    have hθ := renE0_theta_domain S H εren εstep r₀ hM D hD ξ' hξ
    refine Finset.analyticAt_fun_sum _ fun T _ => ?_
    have hTh := analyticOnNhd_renThetaRaw εren Set.univ ((D.Ψ, D.h), ξ') trivial
    have hA : AnalyticAt ℂ (A T) ((fun x i => (1 + renZeta εren ξ') * D.Ψ x i), D.h) :=
      hAan T _ hθ
    exact AnalyticAt.comp_of_eq hA hTh rfl
  · intro D ξ hD hξ
    have hθ := renE0_theta_domain S H εren εstep r₀ hM D hD ξ hξ
    unfold DetExpansionLocC.detGrouped detCollarGrouped
    refine Finset.sum_congr rfl fun T _ => ?_
    exact hAeq T _ hθ
end Balaban.Fluctuation
