/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.LocalClassDensityHDef

/-!
# Ambient representatives of the new local densities in the raw datum (blocker 6, item (2))

For a bundle `Jr : S.JointRep eps pp` of analytic representatives of the backgrounds of the complex
step (`StepComplexJoint`), this file defines the new local densities as functions of the raw block
datum `Θ = (Ψ, h̃)` (spin and field, both complex, the field not necessarily constant), by the
formulas of P4 (2.53), (2.56)-(2.60) with the joint functions of `Jr`:

* `E1locJ z Θ`: `∫₀¹ ds ∫ dμ_{s,0} ∂_ψ̂ W₁(Θ, s ψ̂)[C^{-1/2} 1_{B(z)} C^{1/2} ψ̂]`, the localized
  first energy coefficient in the hat variable (the masked shift `1_{B(z)} ψ'` written in hat
  coordinates with the inverse of the square-root representative `Jr.Mx Θ`);
* `rootTraceJ z Θ`: `-½ Σ_{y ∈ B(z)} tr 𝕃(y,y)` at the background `Jr.F₀ Θ` (`rootTrace` at `s = 1`);
* `E0locJ z Θ = rootTraceJ z Θ + E1locJ z Θ`;
* `M0J g y i Θ = β_k^{1/2} · avgJ (W₁, W₂, ℳ_k(y)_i)(Θ)`.

**Characterization.**  At the raw datum of every datum `D` of the chart `Ξ^c(𝔹_{k+1}; 1, ε)` (any
field, `StepSettingH`) the representatives are the densities of `LocalClassDensityHDef`:
`rootTraceJ_datum`, `E1locJ_datum`, `E0locJ_datum`, `M0J_datum`; on the fibre `D.h ≡ h₀` they are
the landed `E0locC`, `M0C` (`E0locJ_withDatum`, `M0J_withDatum'`).  The value identity
`E1locJ_datum` needs the analyticity of the class densities `ℰ^{(j)}` at the composed pairs of the
path (`hE`, the hypothesis of `JointRep.analyticAt_W1`), which gives the differentiability of
`Φ₁` along the path.

The proof of `E1locJ_datum` transports the derivative through the substitution
`ψ' = β_k^{-1/2} C^{(k)1/2} ψ̂`, an invertible linear map on the chart
(`differentiableAt_of_eventuallyEq_clm`, `fderiv_apply_of_eventuallyEq_clm`).
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Background Balaban.Multiscale Balaban.Localization Balaban.SmallField
  Balaban.SmallField.Def6 Matrix Filter Topology

/-! ### Derivatives through an invertible linear substitution -/

section Chain

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F]
  [NormedSpace ℂ F]

/-- If `f = Φ ∘ T` near `u` for a continuous linear map `T`, and `Φ` is differentiable at `T u`,
then `Df(u)[v] = DΦ(T u)[T v]`. -/
theorem fderiv_apply_of_eventuallyEq_clm {f : E → ℂ} {Φ : F → ℂ} (T : E →L[ℂ] F) {u : E}
    (hev : f =ᶠ[𝓝 u] fun w => Φ (T w)) (hΦ : DifferentiableAt ℂ Φ (T u)) (v : E) :
    fderiv ℂ f u v = fderiv ℂ Φ (T u) (T v) := by
  have h : HasFDerivAt (fun w => Φ (T w)) ((fderiv ℂ Φ (T u)).comp T) u :=
    hΦ.hasFDerivAt.comp u T.hasFDerivAt
  rw [(h.congr_of_eventuallyEq hev).fderiv]
  rfl

/-- If `f = Φ ∘ T` near `u` for an invertible continuous linear map `T` and `f` is differentiable
at `u`, then `Φ` is differentiable at `T u`. -/
theorem differentiableAt_of_eventuallyEq_clm {f : E → ℂ} {Φ : F → ℂ} (T : E →L[ℂ] F)
    (Ti : F →L[ℂ] E) (hTTi : ∀ y, T (Ti y) = y) (hTiT : ∀ w, Ti (T w) = w) {u : E}
    (hev : f =ᶠ[𝓝 u] fun w => Φ (T w)) (hf : DifferentiableAt ℂ f u) :
    DifferentiableAt ℂ Φ (T u) := by
  have hc : Tendsto Ti (𝓝 (T u)) (𝓝 u) := by
    have := Ti.continuous.tendsto (T u)
    rwa [hTiT] at this
  have h2 : (fun y => f (Ti y)) =ᶠ[𝓝 (T u)] Φ := by
    filter_upwards [hc.eventually hev] with y hy
    rw [hy, hTTi]
  have h3 : DifferentiableAt ℂ (fun y => f (Ti y)) (T u) := by
    have hf' : DifferentiableAt ℂ f (Ti (T u)) := by rw [hTiT]; exact hf
    exact hf'.comp (T u) Ti.differentiableAt
  exact h3.congr_of_eventuallyEq h2.symm

end Chain

namespace StepSetting

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ} (S : StepSetting d L N₁ m₁ k N ϱ)

/-- The substitution `ψ' = β_k^{-1/2} M ψ̂` is linear in `ψ̂`. -/
theorem hatField_smul' (M : Matrix (S.U × Fin N) (S.U × Fin N) ℂ) (c : ℂ) (v : S.EC) :
    S.hatField M (c • v) = c • S.hatField M v := by
  unfold hatField
  rw [Matrix.mulVec_smul, smul_comm]

theorem hatField_zero' (M : Matrix (S.U × Fin N) (S.U × Fin N) ℂ) :
    S.hatField M 0 = 0 := by
  unfold hatField
  rw [Matrix.mulVec_zero, smul_zero]

/-- **The substitution as an invertible continuous linear map**: for a square-root matrix with
non-zero determinant and `β > 0`, `ψ̂ ↦ β_k^{-1/2} M ψ̂` has the inverse `ψ' ↦ β_k^{1/2} M⁻¹ ψ'`. -/
theorem exists_hatField_clm (hβ : 0 < S.β) (M : Matrix (S.U × Fin N) (S.U × Fin N) ℂ)
    (hM : IsUnit M.det) :
    ∃ T Ti : S.EC →L[ℂ] S.EC, (∀ w, T w = S.hatField M w) ∧ (∀ y, T (Ti y) = y) ∧
      ∀ w, Ti (T w) = w := by
  set c : ℂ := ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) with hc
  have hβU : 0 < S.betaU := S.betaU_pos' (Nat.pos_of_ne_zero (NeZero.ne L)) hβ
  have hc0 : c ≠ 0 := Complex.ofReal_ne_zero.2 (Real.rpow_pos_of_pos hβU _).ne'
  refine ⟨c • LinearMap.toContinuousLinearMap (Matrix.mulVecLin M),
    c⁻¹ • LinearMap.toContinuousLinearMap (Matrix.mulVecLin M⁻¹), fun w => rfl, fun y => ?_,
    fun w => ?_⟩
  · show c • (M *ᵥ (c⁻¹ • (M⁻¹ *ᵥ y))) = y
    rw [Matrix.mulVec_smul, smul_smul, mul_inv_cancel₀ hc0, one_smul, Matrix.mulVec_mulVec,
      Matrix.mul_nonsing_inv _ hM, Matrix.one_mulVec]
  · show c⁻¹ • (M⁻¹ *ᵥ (c • (M *ᵥ w))) = w
    rw [Matrix.mulVec_smul, smul_smul, inv_mul_cancel₀ hc0, one_smul, Matrix.mulVec_mulVec,
      Matrix.nonsing_inv_mul _ hM, Matrix.one_mulVec]

end StepSetting

namespace StepSetting.JointRep

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ eps pp : ℝ}
  {S : StepSetting d L N₁ m₁ k N ϱ} (Jr : S.JointRep eps pp) (C : StepClass d L N₁ m₁ k N ϱ)

/-! ### The representatives -/

/-- **`ℰ₁^{(k+1)}(z)` as a function of the raw block datum** `Θ` (P4 (2.56)-(2.60)): the
interpolation integral of the derivative of the joint exponent `W₁(Θ, ·)` along the ray `s ψ̂` in
the hat direction `C^{-1/2} 1_{B(z)} C^{1/2} ψ̂` (`C^{1/2} = Jr.Mx Θ`). -/
noncomputable def E1locJ (z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))))
    (Θ : RawData d L (N₁ * L ^ m₁) (k + 1) N) : ℂ :=
  ∫ s in (0 : ℝ)..1, avgFun S.nuFl
    (fun s x => Jr.W1 C (Θ, (s : ℂ) • yhat x))
    (fun x => (fderiv ℂ (fun u : S.EC => Jr.W1 C (Θ, u)) ((s : ℂ) • yhat x))
      ((Jr.Mx Θ)⁻¹ *ᵥ S.maskUC z (Jr.Mx Θ *ᵥ yhat x))) s

/-- **`-½ Σ_{y ∈ B(z)} tr 𝕃(y,y)` as a function of the raw block datum** `Θ`: the rooted trace at
`s = 1` of the decoupled logarithm at the background `Jr.F₀ Θ` (P4 (2.56), (2.58)). -/
noncomputable def rootTraceJ (z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))))
    (Θ : RawData d L (N₁ * L ^ m₁) (k + 1) N) : ℂ :=
  rootTrace S.G' S.a S.a₁ S.ν (unitQ S.G') (unitP S.G') (S.blockU z) (fun _ => 1)
    (svec S.G' (Jr.F₀ Θ).1) (Jr.F₀ Θ).2

/-- **`ℰ₀^{(k+1)}(z)` as a function of the raw block datum** `Θ` (P4 (2.56)). -/
noncomputable def E0locJ (z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))))
    (Θ : RawData d L (N₁ * L ^ m₁) (k + 1) N) : ℂ :=
  Jr.rootTraceJ z Θ + Jr.E1locJ C z Θ

/-- **`ℳ₀^{(k+1)}(y; g)_i` as a function of the raw block datum** `Θ` (P4 (2.53)):
`β_k^{1/2}` times the interpolation average of `ℳ_k(y)_i` with the exponents `W₁`, `W₂`. -/
noncomputable def M0J (g : Fld d L N₁ m₁ (k + 1) N) (y : CTorus d L N₁ m₁ (k + 1)) (i : Fin N)
    (Θ : RawData d L (N₁ * L ^ m₁) (k + 1) N) : ℂ :=
  ((S.betaU ^ (1 / 2 : ℝ) : ℝ) : ℂ) * S.avgJ (Jr.W1 C) (Jr.W2 C g) (Jr.McJ C g y i) Θ

/-! ### Values at a datum of the chart (any field) -/

section Datum

variable (H : StepSettingH S) (hX : XiCData S.G' S.a S.ν (k + 1) 1 eps H.D')

include hX in
/-- **The rooted-trace representative at a datum of the chart** is `-½ Σ_{y ∈ B(z)} tr 𝕃(y,y)` at
the complex background of the datum (the determinant part of `E0locH`). -/
theorem rootTraceJ_datum (z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1)))) :
    Jr.rootTraceJ z (rawOf H.D') =
      -(1 / 2 : ℂ) * ∑ y ∈ S.blockU z, ∑ i,
        decLog S.G' S.a S.a₁ S.ν (bgMultC S.G' S.a S.ν (bgC0 d L N) H.D') (fun _ => 1)
          (svec S.G' (bgFieldC S.G' S.a S.ν (bgC0 d L N) H.D')) (unitQ S.G') (unitP S.G')
          (y, i) (y, i) := by
  unfold rootTraceJ rootTrace
  rw [Jr.F₀_eq H.D' hX, Balaban.Localization.extS_one]

include hX in
/-- On a bounded hat variable, the joint exponent `W₁` at a datum of the chart (any field) is
`Φ₁` of the block datum at the substituted shift. -/
theorem W1_eq_Phi1H {u : S.EC} (hu : ∀ p, ‖u p‖ ≤ pp) :
    Jr.W1 C (rawOf H.D', u) = H.Phi1H C (S.hatField (hatCovSqrt S.G' S.a₁ S.ν H.D') u) := by
  have h := Jr.W1_dataUCH H C hX hu
  dsimp only at h
  rw [h, S.hatField_zero', add_zero]
  rfl

include hX in
/-- On a bounded hat variable, the joint exponent `W₂` at a datum of the chart (any field) is the
change of `ℱ_k` between the old data with the field of the block datum. -/
theorem W2_eq_dataUCH {u : S.EC} (hu : ∀ p, ‖u p‖ ≤ pp) (g : Fld d L N₁ m₁ (k + 1) N) :
    Jr.W2 C g (rawOf H.D', u) =
      FcompAtC C.m₀ C.Tm S.a S.ν (Nat.le_succ k)
          (H.dataUCH (H.psi0H + S.hatField (hatCovSqrt S.G' S.a₁ S.ν H.D') u)) g -
        FcompAtC C.m₀ C.Tm S.a S.ν (Nat.le_succ k) (H.dataUCH H.psi0H) g := by
  have h := Jr.W2_dataUCH H C hX hu g
  dsimp only at h
  rw [h, S.hatField_zero', add_zero]
  rfl

variable {c BG κ Kc Cx c₂ BG₂ δ₁ δc : ℝ}

include hX in
/-- **`E1locJ` at a datum of the chart (any field) is `ℰ₁^{(k+1)}(z)` of the block datum**
(`E1locH`), where the class densities `ℰ^{(j)}` are analytic at the composed pairs of the path. -/
theorem E1locJ_datum
    (hC : FlCore N S.G' (stepG d L N₁ m₁ k ϱ) S.a₁ S.ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    (hdm : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    (hβ : 0 < S.β) (hp₁ : 0 < S.p₁) (hle : S.p₁ ≤ pp)
    (hE : ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ x : S.E, ‖x‖ ≤ S.p₁ → ∀ j ∈ Finset.Icc 1 k,
      AnalyticAt ℂ
        (fun p : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N => Edens C.m₀ C.Tm j p.1 p.2)
        (Jr.PJ j (rawOf H.D', (s : ℂ) • yhat x)))
    (z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1)))) :
    Jr.E1locJ C z (rawOf H.D') = H.E1locH C z := by
  set M := hatCovSqrt S.G' S.a₁ S.ν H.D' with hMdef
  have hMx : Jr.Mx (rawOf H.D') = M := Jr.Mx_eq H.D' hX
  have hdet : IsUnit M.det := by
    rw [hMdef, H.det_hatCovSqrt_of_chart hC hMX hdm hα hsm hX]
    exact (Complex.exp_ne_zero _).isUnit
  obtain ⟨T, Ti, hT, hTTi, hTiT⟩ := S.exists_hatField_clm hβ M hdet
  have hΘ : rawOf H.D' ∈ XiCRaw S.G' S.a S.ν (k + 1) 1 eps := ⟨H.D', hX, rfl⟩
  have hW : ∀ u : S.EC, ‖u‖ < pp →
      Jr.W1 C (rawOf H.D', u) = H.Phi1H C (S.hatField M u) := fun u hu =>
    Jr.W1_eq_Phi1H C H hX fun p => (norm_le_pi_norm u p).trans hu.le
  have hE0 : ∀ j ∈ Finset.Icc 1 k, AnalyticAt ℂ
      (fun p : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N => Edens C.m₀ C.Tm j p.1 p.2)
      (Jr.PJ j (rawOf H.D', 0)) := by
    intro j hj
    have h := hE 0 ⟨le_rfl, zero_le_one⟩ 0 (by rw [norm_zero]; exact hp₁.le) j hj
    rwa [Complex.ofReal_zero, zero_smul] at h
  unfold E1locJ StepSettingH.E1locH
  refine intervalIntegral.integral_congr fun s hs => ?_
  rw [Set.uIcc_of_le zero_le_one] at hs
  have hs1 : |s| ≤ 1 := by rw [abs_of_nonneg hs.1]; exact hs.2
  refine avgFun_congr_ae ?_ ?_
  · filter_upwards [S.ae_ball hp₁] with x hx
    have hxn : ‖x‖ < S.p₁ := (chiFl_eq_one_iff hp₁ x).1 hx
    have hu : ‖(s : ℂ) • yhat x‖ < pp :=
      calc ‖(s : ℂ) • yhat x‖ ≤ |s| * ‖x‖ := norm_smul_yhat_le (S := S) s x
        _ ≤ 1 * ‖x‖ := mul_le_mul_of_nonneg_right hs1 (norm_nonneg _)
        _ < pp := by rw [one_mul]; exact hxn.trans_le hle
    show Jr.W1 C (rawOf H.D', (s : ℂ) • yhat x) =
      H.Phi1H C ((s : ℂ) • S.hatField M (yhat x))
    rw [hW _ hu, S.hatField_smul']
  · filter_upwards [S.ae_ball hp₁] with x hx
    have hxn : ‖x‖ < S.p₁ := (chiFl_eq_one_iff hp₁ x).1 hx
    have hu : ‖(s : ℂ) • yhat x‖ < pp :=
      calc ‖(s : ℂ) • yhat x‖ ≤ |s| * ‖x‖ := norm_smul_yhat_le (S := S) s x
        _ ≤ 1 * ‖x‖ := mul_le_mul_of_nonneg_right hs1 (norm_nonneg _)
        _ < pp := by rw [one_mul]; exact hxn.trans_le hle
    have hev : (fun w : S.EC => Jr.W1 C (rawOf H.D', w)) =ᶠ[𝓝 ((s : ℂ) • yhat x)]
        fun w => H.Phi1H C (T w) := by
      filter_upwards [isOpen_lt continuous_norm continuous_const |>.mem_nhds hu] with w hw
      rw [hW w hw, hT]
    have hf : DifferentiableAt ℂ (fun w : S.EC => Jr.W1 C (rawOf H.D', w))
        ((s : ℂ) • yhat x) := by
      have han := Jr.analyticAt_W1 C hΘ
        (smul_yhat_le (S := S) (S.abs_mul_le_of_mem hle hs hxn.le)) (hE s hs x hxn.le) hE0
      exact han.differentiableAt.comp ((s : ℂ) • yhat x)
        (DifferentiableAt.prodMk (differentiableAt_const _) differentiableAt_id)
    have hΦ := differentiableAt_of_eventuallyEq_clm T Ti hTTi hTiT hev hf
    rw [fderiv_apply_of_eventuallyEq_clm T hev hΦ, hT, hT, hMx, S.hatField_smul']
    have hmask := Jr.hatField_inv_mask_of_chart H hC hMX hdm hα hsm hX z x
    rw [hMx] at hmask
    rw [hmask]

include hX in
/-- **`E0locJ` at a datum of the chart (any field) is `ℰ₀^{(k+1)}(z)` of the block datum**
(`E0locH`). -/
theorem E0locJ_datum
    (hC : FlCore N S.G' (stepG d L N₁ m₁ k ϱ) S.a₁ S.ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    (hdm : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    (hβ : 0 < S.β) (hp₁ : 0 < S.p₁) (hle : S.p₁ ≤ pp)
    (hE : ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ x : S.E, ‖x‖ ≤ S.p₁ → ∀ j ∈ Finset.Icc 1 k,
      AnalyticAt ℂ
        (fun p : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N => Edens C.m₀ C.Tm j p.1 p.2)
        (Jr.PJ j (rawOf H.D', (s : ℂ) • yhat x)))
    (z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1)))) :
    Jr.E0locJ C z (rawOf H.D') = H.E0locH C z := by
  unfold E0locJ StepSettingH.E0locH
  rw [Jr.rootTraceJ_datum H hX z,
    Jr.E1locJ_datum C H hX hC hMX hdm hα hsm hβ hp₁ hle hE z]

include hX in
/-- **`M0J` at a datum of the chart (any field) is `ℳ₀^{(k+1)}(y; g)_i` of the block datum**
(`M0H`). -/
theorem M0J_datum (hp₁ : 0 < S.p₁) (hle : S.p₁ ≤ pp) (g : Fld d L N₁ m₁ (k + 1) N)
    (y : CTorus d L N₁ m₁ (k + 1)) (i : Fin N) :
    Jr.M0J C g y i (rawOf H.D') = H.M0H C g y i := by
  unfold M0J
  rw [Jr.M0J_dataUCH C hp₁ hle H hX g y i]
  unfold StepSettingH.M0H
  refine congrArg (fun w : ℂ => ((S.betaU ^ (1 / 2 : ℝ) : ℝ) : ℂ) * w) ?_
  refine intervalIntegral.integral_congr fun t ht => ?_
  rw [Set.uIcc_of_le zero_le_one] at ht
  refine avgFun₂_congr_ae ?_ ?_ (Filter.Eventually.of_forall fun x => ?_)
  · filter_upwards [S.ae_ball hp₁] with x hx
    have hxn : ‖x‖ < S.p₁ := (chiFl_eq_one_iff hp₁ x).1 hx
    have hu : ∀ p, ‖yhat x p‖ ≤ pp := fun p =>
      (norm_le_pi_norm (yhat x) p).trans (by
        have := norm_smul_yhat_le (S := S) 1 x
        simp only [Complex.ofReal_one, one_smul, abs_one, one_mul] at this
        exact this.trans (hxn.le.trans hle))
    show Jr.W1 C (rawOf H.D', yhat x) = H.Phi1H C (((1 : ℝ) : ℂ) •
      S.hatField (hatCovSqrt S.G' S.a₁ S.ν H.D') (yhat x))
    rw [Jr.W1_eq_Phi1H C H hX hu, Complex.ofReal_one, one_smul]
  · filter_upwards [S.ae_ball hp₁] with x hx
    have hxn : ‖x‖ < S.p₁ := (chiFl_eq_one_iff hp₁ x).1 hx
    show Jr.W2 C g (rawOf H.D', (t : ℂ) • yhat x) = _
    rw [Jr.W2_eq_dataUCH C H hX (smul_yhat_le (S := S) (S.abs_mul_le_of_mem hle ht hxn.le)) g,
      S.hatField_smul']
  · refine congrArg (fun F : ℝ → ℂ => deriv F t) (funext fun r => ?_)
    show McompAtC C.m₀ C.Tm S.a S.ν (Nat.le_succ k)
        (H.dataUCH (H.psi0H + S.hatField (hatCovSqrt S.G' S.a₁ S.ν H.D') ((r : ℂ) • yhat x)))
        g y i = _
    rw [S.hatField_smul']

end Datum

/-! ### On the fibre: the landed densities -/

section Fibre

variable {c BG κ Kc Cx c₂ BG₂ δ₁ δc : ℝ}
  (D : BgData S.G' N) (hD : ∀ y i, D.h y i = (S.h₀ i : ℂ))
  (hX : XiCData S.G' S.a S.ν (k + 1) 1 eps D)

include hX in
/-- **On the fibre `E0locJ` is the landed `E0locC`** of the step with the datum `D`. -/
theorem E0locJ_withDatum
    (hC : FlCore N S.G' (stepG d L N₁ m₁ k ϱ) S.a₁ S.ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    (hdm : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    (hβ : 0 < S.β) (hp₁ : 0 < S.p₁) (hle : S.p₁ ≤ pp)
    (hE : ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ x : S.E, ‖x‖ ≤ S.p₁ → ∀ j ∈ Finset.Icc 1 k,
      AnalyticAt ℂ
        (fun p : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N => Edens C.m₀ C.Tm j p.1 p.2)
        (Jr.PJ j (rawOf D, (s : ℂ) • yhat x)))
    (z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1)))) :
    Jr.E0locJ C z (rawOf D) = (S.withDatum D hD).E0locC C z := by
  rw [← StepSettingH.E0locH_fibre C D hD z]
  exact Jr.E0locJ_datum C (S.withDatumH D) hX hC hMX hdm hα hsm hβ hp₁ hle hE z

include hX in
/-- **On the fibre `M0J` is the landed `M0C`** of the step with the datum `D`. -/
theorem M0J_withDatum' (hp₁ : 0 < S.p₁) (hle : S.p₁ ≤ pp) (g : Fld d L N₁ m₁ (k + 1) N)
    (y : CTorus d L N₁ m₁ (k + 1)) (i : Fin N) :
    Jr.M0J C g y i (rawOf D) = (S.withDatum D hD).M0C C g y i :=
  Jr.M0J_withDatum C hp₁ hle D hD hX g y i

end Fibre

end StepSetting.JointRep

end Balaban.Fluctuation
