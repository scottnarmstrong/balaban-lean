/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.StepTowerNewLevelSymPhi
public import Balaban.Fluctuation.LocalClassDensityHRep
public import Balaban.Fluctuation.HatLabelsTerms

/-!
# The local energy of the new level under a lattice symmetry (`StepTowerNewLevelSymE`)

`ℰ₀^{(k+1)}(z) = -½ ∑_{y ∈ B(z)} tr 𝕃(y,y) + ℰ₁^{(k+1)}(z)` at the block datum `θ` (P4 (2.56),
`E0locH`) is unchanged when the datum and the block are transported by a lattice symmetry `σ`
(`E0locH_sym`).  The proof:

* the rooted trace is `decLog_sym` (the logarithm is relabelled by the permutation `u` of the unit
  points, and `B(σ z)` is the image of `B(z)`);
* the interpolation integral `E1locH` is transported by `u`: the hat variable, the square root, the
  mask `1_{B(z)}` (`hatField_sym`, `maskUC_sym`), the measure `ν_{p₁}` (a product measure, invariant
  under `x ↦ x ∘ u⁻¹`, `nuFl_measurePreserving`) and the derivative of `Φ₁` through the linear
  homeomorphism `w ↦ w ∘ u⁻¹` (`fderiv_apply_of_eventuallyEq_equiv`, unconditional);
* the only input on `Φ₁` is that the transported `Φ₁` agrees with `Φ₁` near the points of the path
  `s ψ'(x)`, `‖x‖ < p₁` (`hPhi`; `Phi1H_sym` gives the equality wherever the old composed pairs
  lie in the domain of the level sets).
-/

@[expose] public section

namespace Balaban.Inhabited.StepSym

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization Balaban.Fluctuation
  Balaban.SmallField Balaban.SmallField.Def6 Balaban.SmallField.Def6v2
  Balaban.Localization.DecEquiv Balaban.Localization.DetUnitIncidence Matrix Filter Topology
  MeasureTheory

section Chain

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- **The derivative through an invertible linear substitution, unconditionally**: if
`f = Φ ∘ T` near `u` for a linear homeomorphism `T`, then `Df(u)[v] = DΦ(T u)[T v]` (both sides
vanish if `Φ` is not differentiable at `T u`). -/
theorem fderiv_apply_of_eventuallyEq_equiv {f Φ : E → ℂ} (T : E ≃L[ℂ] E) {u : E}
    (hev : f =ᶠ[𝓝 u] fun w => Φ (T w)) (v : E) :
    fderiv ℂ f u v = fderiv ℂ Φ (T u) (T v) := by
  by_cases hΦ : DifferentiableAt ℂ Φ (T u)
  · exact fderiv_apply_of_eventuallyEq_clm (T : E →L[ℂ] E) hev hΦ v
  · have hf : ¬ DifferentiableAt ℂ f u := fun hf =>
      hΦ (differentiableAt_of_eventuallyEq_clm (T : E →L[ℂ] E) (T.symm : E →L[ℂ] E)
        (fun y => T.apply_symm_apply y) (fun w => T.symm_apply_apply w) hev hf)
    rw [fderiv_zero_of_not_differentiableAt hf, fderiv_zero_of_not_differentiableAt hΦ]
    simp

/-- Change of variables for a measure-preserving equivalence. -/
theorem integral_transport {α : Type*} [MeasurableSpace α] {ν : Measure α} {e : α ≃ᵐ α}
    (hμ : MeasurePreserving e ν ν) (g g₀ : α → ℂ) (h : ∀ᵐ x ∂ν, g (e x) = g₀ x) :
    ∫ x', g x' ∂ν = ∫ x, g₀ x ∂ν :=
  (hμ.integral_comp' g).symm.trans (integral_congr_ae h)

end Chain

section Step

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
variable {S : StepSetting d L N₁ m₁ k N ϱ} {σ : Equiv.Perm (CTorus d L N₁ m₁ (k + 1))}
variable (Sy : LatSymm S.G' S.G' σ) (hU : UnitBlockPres σ)

include Sy hU in
theorem maskUC_sym {z z' : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1)))}
    (hz : S.blockU z' = (S.blockU z).map (unitAct S.G' Sy hU).toEmbedding) (v : S.EC) :
    S.maskUC z' (fun r => v ((unitAct S.G' Sy hU).symm r.1, r.2)) =
      fun r => (S.maskUC z v) ((unitAct S.G' Sy hU).symm r.1, r.2) := by
  classical
  funext r
  unfold StepSetting.maskUC
  have : r.1 ∈ S.blockU z' ↔ (unitAct S.G' Sy hU).symm r.1 ∈ S.blockU z := by
    rw [hz, Finset.mem_map_equiv]
  by_cases h : r.1 ∈ S.blockU z'
  · have h' := this.1 h
    simp only [h, h', ↓reduceIte]
  · have h' : ¬ (unitAct S.G' Sy hU).symm r.1 ∈ S.blockU z := fun h'' => h (this.2 h'')
    simp only [h, h', ↓reduceIte]

include Sy hU in
theorem hatField_sym (M : Matrix (S.U × Fin N) (S.U × Fin N) ℂ) (v : S.EC) :
    S.hatField (rm ((unitAct S.G' Sy hU).prodCongr (Equiv.refl (Fin N))) M)
        (fun r => v ((unitAct S.G' Sy hU).symm r.1, r.2)) =
      fun r => S.hatField M v ((unitAct S.G' Sy hU).symm r.1, r.2) := by
  unfold StepSetting.hatField
  have h2 := mulVec_rm_fun ((unitAct S.G' Sy hU).prodCongr (Equiv.refl (Fin N))) M v
  funext r
  show _ * (rm ((unitAct S.G' Sy hU).prodCongr (Equiv.refl (Fin N))) M *ᵥ
    (fun q => v (((unitAct S.G' Sy hU).prodCongr (Equiv.refl (Fin N))).symm q))) r = _
  rw [h2]
  rfl

theorem nuFl_measurePreserving (hp₁ : 0 < S.p₁) (e : S.U ≃ S.U) :
    MeasurePreserving (MeasurableEquiv.arrowCongr' e (MeasurableEquiv.refl (Rn N)))
      S.nuFl S.nuFl := by
  have := isProbabilityMeasure_fluctMeasure1 N hp₁
  unfold StepSetting.nuFl fluctMeasure
  exact measurePreserving_arrowCongr' (fun _ : S.U => fluctMeasure1 N S.p₁)
    (fun _ : S.U => fluctMeasure1 N S.p₁) e (MeasurableEquiv.refl (Rn N))
    (fun _ => MeasurePreserving.id _)

variable (C : StepClass d L N₁ m₁ k N ϱ)
variable {c BG κ eps Kc Cx c₂ BG₂ δ₁ δc : ℝ}
variable (hC : FlCore N S.G' (stepG d L N₁ m₁ k ϱ) S.a₁ S.ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
  (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
  (hdm : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
  (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
  (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)

include hC hMX hdm hα hsm Sy hU in
/-- **`ℰ₁^{(k+1)}(z)` is covariant under a lattice symmetry** (the interpolation integral of
`E1locH`): at the transported datum and the transported block, the integral is unchanged, once `Φ₁`
at the transported datum agrees with the transported `Φ₁` near the points of the path. -/
theorem E1locH_sym (hp₁ : 0 < S.p₁) {D : BgData S.G' N}
    (hD : XiCData S.G' S.a S.ν (k + 1) 1 eps D)
    {z z' : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1)))}
    (hz : S.blockU z' = (S.blockU z).map (unitAct S.G' Sy hU).toEmbedding)
    (hPhi : ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ x : S.E, ‖x‖ < S.p₁ →
      (S.withDatumH D).Phi1H C =ᶠ[𝓝 ((s : ℂ) • S.hatField (hatCovSqrt S.G' S.a₁ S.ν D) (yhat x))]
        fun w => (S.withDatumH (Sy.sym D)).Phi1H C
          (fun r => w ((unitAct S.G' Sy hU).symm r.1, r.2))) :
    (S.withDatumH (Sy.sym D)).E1locH C z' = (S.withDatumH D).E1locH C z := by
  classical
  have hD' : ∀ D : BgData S.G' N, (S.withDatumH D).D' = D := fun _ => rfl
  have hM := hatCovSqrt_sym hC hMX hdm hα hsm Sy hU hD
  set u := unitAct S.G' Sy hU with hu
  have hμ := nuFl_measurePreserving (S := S) hp₁ u
  let T : S.EC ≃L[ℂ] S.EC :=
    (LinearEquiv.funCongrLeft ℂ ℂ (u.prodCongr (Equiv.refl (Fin N))).symm).toContinuousLinearEquiv
  have hT : ∀ w : S.EC, T w = fun r => w (u.symm r.1, r.2) := fun w => rfl
  unfold StepSettingH.E1locH
  simp only [hD']
  refine intervalIntegral.integral_congr fun s hs => ?_
  rw [Set.uIcc_of_le zero_le_one] at hs
  unfold avgFun partFun
  -- the integrand at the transported variable
  have key : ∀ᵐ x ∂S.nuFl,
      ((fderiv ℂ ((S.withDatumH (Sy.sym D)).Phi1H C)
        ((s : ℂ) • S.hatField (hatCovSqrt S.G' S.a₁ S.ν (Sy.sym D))
          (yhat (MeasurableEquiv.arrowCongr' u (MeasurableEquiv.refl (Rn N)) x)))) 
        (S.maskUC z' (S.hatField (hatCovSqrt S.G' S.a₁ S.ν (Sy.sym D))
          (yhat (MeasurableEquiv.arrowCongr' u (MeasurableEquiv.refl (Rn N)) x))))) =
      ((fderiv ℂ ((S.withDatumH D).Phi1H C)
        ((s : ℂ) • S.hatField (hatCovSqrt S.G' S.a₁ S.ν D) (yhat x)))
        (S.maskUC z (S.hatField (hatCovSqrt S.G' S.a₁ S.ν D) (yhat x)))) ∧
      (S.withDatumH (Sy.sym D)).Phi1H C
        ((s : ℂ) • S.hatField (hatCovSqrt S.G' S.a₁ S.ν (Sy.sym D))
          (yhat (MeasurableEquiv.arrowCongr' u (MeasurableEquiv.refl (Rn N)) x))) =
      (S.withDatumH D).Phi1H C ((s : ℂ) • S.hatField (hatCovSqrt S.G' S.a₁ S.ν D) (yhat x)) := by
    filter_upwards [S.ae_ball hp₁] with x hx
    have hxn : ‖x‖ < S.p₁ := (chiFl_eq_one_iff hp₁ x).1 hx
    have hy : yhat (MeasurableEquiv.arrowCongr' u (MeasurableEquiv.refl (Rn N)) x) =
        fun r => yhat x (u.symm r.1, r.2) := rfl
    have hh : S.hatField (hatCovSqrt S.G' S.a₁ S.ν (Sy.sym D))
        (yhat (MeasurableEquiv.arrowCongr' u (MeasurableEquiv.refl (Rn N)) x)) =
        fun r => S.hatField (hatCovSqrt S.G' S.a₁ S.ν D) (yhat x) (u.symm r.1, r.2) := by
      rw [hy, hM]; exact hatField_sym Sy hU _ _
    have hev := hPhi s hs x hxn
    have hw : (s : ℂ) • S.hatField (hatCovSqrt S.G' S.a₁ S.ν (Sy.sym D))
        (yhat (MeasurableEquiv.arrowCongr' u (MeasurableEquiv.refl (Rn N)) x)) =
        T ((s : ℂ) • S.hatField (hatCovSqrt S.G' S.a₁ S.ν D) (yhat x)) := by
      rw [hh, hT]; rfl
    rw [hw]
    refine ⟨?_, (hev.eq_of_nhds).symm⟩
    have hm := maskUC_sym Sy hU hz (S.hatField (hatCovSqrt S.G' S.a₁ S.ν D) (yhat x))
    rw [hh, hm, ← hT]
    exact (fderiv_apply_of_eventuallyEq_equiv T hev _).symm
  refine congrArg₂ (· / ·) ?_ ?_
  · refine integral_transport hμ _ _ ?_
    filter_upwards [key] with x hx
    simp only [hx.1, hx.2]
  · refine integral_transport hμ _ _ ?_
    filter_upwards [key] with x hx
    simp only [hx.2]

include hC hMX hdm hα hsm Sy hU in
/-- **`ℰ₀^{(k+1)}(z)` is covariant under a lattice symmetry**: the rooted trace of `𝕃` and the
interpolation integral `ℰ₁` are both unchanged. -/
theorem E0locH_sym (hp₁ : 0 < S.p₁) {D : BgData S.G' N}
    (hD : XiCData S.G' S.a S.ν (k + 1) 1 eps D)
    {z z' : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1)))}
    (hz : S.blockU z' = (S.blockU z).map (unitAct S.G' Sy hU).toEmbedding)
    (hPhi : ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ x : S.E, ‖x‖ < S.p₁ →
      (S.withDatumH D).Phi1H C =ᶠ[𝓝 ((s : ℂ) • S.hatField (hatCovSqrt S.G' S.a₁ S.ν D) (yhat x))]
        fun w => (S.withDatumH (Sy.sym D)).Phi1H C
          (fun r => w ((unitAct S.G' Sy hU).symm r.1, r.2))) :
    (S.withDatumH (Sy.sym D)).E0locH C z' = (S.withDatumH D).E0locH C z := by
  have hD' : ∀ D : BgData S.G' N, (S.withDatumH D).D' = D := fun _ => rfl
  have hsum : ∑ y ∈ S.blockU z', ∑ i : Fin N,
      decLog S.G' S.a S.a₁ S.ν (bgMultC S.G' S.a S.ν (bgC0 d L N) (Sy.sym D)) (fun _ => 1)
        (svec S.G' (bgFieldC S.G' S.a S.ν (bgC0 d L N) (Sy.sym D))) (unitQ S.G') (unitP S.G')
        (y, i) (y, i) =
      ∑ y ∈ S.blockU z, ∑ i : Fin N,
      decLog S.G' S.a S.a₁ S.ν (bgMultC S.G' S.a S.ν (bgC0 d L N) D) (fun _ => 1)
        (svec S.G' (bgFieldC S.G' S.a S.ν (bgC0 d L N) D)) (unitQ S.G') (unitP S.G')
        (y, i) (y, i) := by
    rw [hz, Finset.sum_map]
    refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun i _ => ?_
    rw [decLog_sym hC hMX hdm hα hsm Sy hU hD]
    exact rm_apply ((unitAct S.G' Sy hU).prodCongr (Equiv.refl (Fin N))) _ (y, i) (y, i)
  unfold StepSettingH.E0locH
  simp only [hD']
  rw [E1locH_sym Sy hU C hC hMX hdm hα hsm hp₁ hD hz hPhi, hsum]

end Step

end Balaban.Inhabited.StepSym
