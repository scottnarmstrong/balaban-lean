/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.StepComplexProp26
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The output side of the complex step on real data is the landed one (FLUCTUATION.md §2.6)

For a real block datum satisfying the premises of the landed step (the hypothesis block of
`StepIdentity`, as in `StepComplexAgree`), the holomorphic objects of `StepComplexOut` are the
landed objects of `StepObjects`:

* `covAC_eq`, `logAC_eq`, `halfLogDetCC_eq`: `𝒜`, `𝕃` and `½ log det C^{(k)}` (the analytic branch
  `-½ ∑ tr 𝕃(y,y)` is the real logarithm, `halfLogDetC_eq_trace`);
* `AnewC_eq`, `tKernelC_yhat`, `AoldC_yhat`, `rhoExpC_yhat`: the actions, the kernel and the density
  on real fields;
* `det_covSqrtC_real`: `det C^{(k)1/2} = |det K|`;
* `TstepC_eq`: the fluctuation integral (the change of variables (2.7) and Lemma 2.5);
* `E1C_eq`, `E0C_eq`, `F0C_eq`, `M0C_eq`: the new terms;
* `EcompAtC_psiKdC_eq`, `FcompAtC_psiKdC_eq`: the class composites at the critical point;
* `prop26C_class_of_real`: the identity of Proposition 2.6 for the holomorphic objects at a real
  datum, from the landed `prop26_complex_class` and the agreements (the consistency of `prop26C_class`
  with the landed theorem on the real chart).
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.SmallField.Def6 Balaban.Background Balaban.Multiscale Balaban.Localization
  Balaban.SmallField Finset Matrix MeasureTheory

section AeCongr

variable {X : Type*} [MeasurableSpace X] {ν : Measure X}

theorem avgFun_congr_ae {W W' : ℝ → X → ℂ} {f f' : X → ℂ} {s : ℝ}
    (h1 : ∀ᵐ x ∂ν, W s x = W' s x) (hf : ∀ᵐ x ∂ν, f x = f' x) :
    avgFun ν W f s = avgFun ν W' f' s := by
  unfold avgFun partFun
  congr 1
  · refine integral_congr_ae ?_
    filter_upwards [h1, hf] with x hx1 hx2
    rw [hx1, hx2]
  · refine integral_congr_ae ?_
    filter_upwards [h1] with x hx1
    rw [hx1]

end AeCongr

namespace StepSetting

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}
  (S : StepSetting d L N₁ m₁ k N ϱ) (C : StepClass d L N₁ m₁ k N ϱ)

/-! ### The covariance objects and the actions -/

section Bg

variable (ha₁ : 0 < S.a₁) (H : BgHyp d L (k + 1) ϱ S.a S.ν) {δ' : ℝ} (hδ'0 : 0 < δ')
  (hδ' : δ' ≤ thm73C3 d L N / 2) (hD'R : InDomainR S.G' S.ν δ' S.D')

include H hδ'0 hδ' hD'R in
/-- **Real data: `𝒜` of the complex step is the landed `covA`.** -/
theorem covAC_eq : S.covAC = S.covA := by
  obtain ⟨hf, hm⟩ := S.bgC_eq H hδ'0 hδ' hD'R
  unfold covAC covA
  rw [hf, hm]

include H hδ'0 hδ' hD'R in
/-- **Real data: `𝕃` of the complex step is the landed `logA`.** -/
theorem logAC_eq : S.logAC = S.logA := by
  obtain ⟨hf, hm⟩ := S.bgC_eq H hδ'0 hδ' hD'R
  unfold logAC logA
  rw [hf, hm]

include H hδ'0 hδ' hD'R in
/-- **Real data: `A^η_{k+1}` of the complex step is the landed `Anew`.** -/
theorem AnewC_eq : S.AnewC = (S.Anew : ℂ) := by
  obtain ⟨hf, -⟩ := S.bgC_eq H hδ'0 hδ' hD'R
  have hunit := S.bgField_unit H hδ'0 hδ' hD'R
  unfold AnewC Anew
  rw [hf]
  exact (action_cast S.D' (isReal_of_inDomainR hD'R) (fun z i => (hunit z).1 i)).symm

include hD'R in
/-- **Real `θ`: the kernel `∏ t_k` of the complex step at a real old spin is the landed
`tKernel`.** -/
theorem tKernelC_yhat (ψ : S.E) : S.tKernelC (yhat ψ) = (S.tKernel ψ : ℂ) := by
  have hD'real := isReal_of_inDomainR hD'R
  have h := couplingC_ofReal S.G' S.a₁ (k + 1) S.D'.Ψ (S.dataU ψ).Ψ
    (fun z i => (hD'real z i).1) (fun z i => by rw [S.dataU_Ψ]; exact Complex.ofReal_im _)
  unfold tKernelC tKernel
  rw [S.dataUC_yhat, h]
  push_cast
  rfl

include H in
/-- **`A_k(ψ, φ_k(ψ))` of the complex step at a real old spin of the real domain `𝒟_ℝ` is the
landed `Aold`.** -/
theorem AoldC_yhat (ψ : S.E)
    (hdom : InUnionDomainR (stepG d L N₁ m₁ k ϱ) (bgC1 d L N) S.ν (S.dataU ψ)) :
    S.AoldC (yhat ψ) = (S.Aold ψ : ℂ) := by
  have hunit := (theorem71 H hdom).2.1
  have hreal := isReal_of_inDomainR hdom.choose_spec.2.2
  unfold AoldC Aold
  rw [S.dataUC_yhat, (theorem72_real H hdom).1]
  exact (action_cast (S.dataU ψ) hreal (fun x i => (hunit x).1 i)).symm

include H in
/-- **The exponential of `ρ_k` of the complex step at a real old spin of `𝒟_ℝ` is the exponential
of the landed `rhoStep`.** -/
theorem rhoExpC_yhat (g : Fld d L N₁ m₁ (k + 1) N) (ψ : S.E)
    (hdom : InUnionDomainR (stepG d L N₁ m₁ k ϱ) (bgC1 d L N) S.ν (S.dataU ψ)) :
    S.rhoExpC C g (yhat ψ) = Complex.exp (-(S.β : ℂ) * (S.Aold ψ : ℂ) +
      EcompAt C.m₀ C.Tm S.a S.ν (Nat.le_succ k) (S.dataU ψ) - (C.Ek : ℂ) * (S.nU : ℂ) +
      FcompAt C.m₀ C.Tm S.a S.ν (Nat.le_succ k) (S.dataU ψ) g) := by
  unfold rhoExpC
  rw [S.AoldC_yhat H ψ hdom, S.dataUC_yhat, EcompAtC_eq H _ _ hdom, FcompAtC_eq H _ _ hdom]

include ha₁ H hδ'0 hδ' hD'R in
/-- **Real data: `ℰ_k(ψ^{(k)}(θ))` of the complex step is the landed one.** -/
theorem EcompAtC_psiKdC_eq :
    EcompAtC C.m₀ C.Tm S.a S.ν (Nat.le_succ k) S.psiKdC =
      EcompAt C.m₀ C.Tm S.a S.ν (Nat.le_succ k) S.psiKd := by
  obtain ⟨hDU', -⟩ := S.D'_domains H hδ'0 hδ' hD'R
  have hdom := (criticalPoint_real ha₁ S.hG S.hG' (le_refl (k + 1)) H H S.D' hDU').2.1
  rw [S.psiKdC_eq H hδ'0 hδ' hD'R]
  exact EcompAtC_eq H _ _ hdom

include ha₁ H hδ'0 hδ' hD'R in
/-- **Real data: `ℱ_k(ψ^{(k)}(θ), g)` of the complex step is the landed one.** -/
theorem FcompAtC_psiKdC_eq (g : Fld d L N₁ m₁ (k + 1) N) :
    FcompAtC C.m₀ C.Tm S.a S.ν (Nat.le_succ k) S.psiKdC g =
      FcompAt C.m₀ C.Tm S.a S.ν (Nat.le_succ k) S.psiKd g := by
  obtain ⟨hDU', -⟩ := S.D'_domains H hδ'0 hδ' hD'R
  have hdom := (criticalPoint_real ha₁ S.hG S.hG' (le_refl (k + 1)) H H S.D' hDU').2.1
  rw [S.psiKdC_eq H hδ'0 hδ' hD'R]
  exact FcompAtC_eq H _ _ hdom g

end Bg

/-! ### `½ log det C^{(k)}` and the Jacobian -/

section Det

variable (H : BgHyp d L (k + 1) ϱ S.a S.ν) {δ' : ℝ} (hδ'0 : 0 < δ')
  (hδ' : δ' ≤ thm73C3 d L N / 2) (hD'R : InDomainR S.G' S.ν δ' S.D')
  (hδ0 : 0 < S.δ)
  (hχ : ChiUBounds S.G' S.ν S.δ S.D' (bgField S.G' S.a S.ν S.D') (bgMult S.G' S.a S.ν S.D'))
  (hfam : ∀ x, 0 ≤ x → XData S.G' S.a S.a₁ S.ν x (bgMult S.G' S.a S.ν S.D') 0 (fun _ => 1))
  (hsm : S.δ ^ 2 * smallConstX d L 0 ≤ 1 / 4)

include H hδ'0 hδ' hD'R hδ0 hχ hfam in
/-- **Real data: the pointwise premises of Theorem I-4c at the complex background** (which is the
real background). -/
theorem covData_of_real :
    (∀ x, 0 ≤ x → XData S.G' S.a S.a₁ S.ν x
        (bgMultC S.G' S.a S.ν (bgC0 d L N) S.D') 0 (fun _ => 1)) ∧
      IsConstraintField S.G' S.δ (svec S.G' (bgFieldC S.G' S.a S.ν (bgC0 d L N) S.D')) := by
  obtain ⟨hf, hm⟩ := S.bgC_eq H hδ'0 hδ' hD'R
  rw [hf, hm]
  exact ⟨hfam, S.constraintField_bg H hδ'0 hδ' hD'R hδ0 hχ⟩

include H hδ'0 hδ' hD'R hδ0 hχ hfam hsm in
/-- **Real data: the analytic `½ log det C^{(k)}` is the real one**, `halfLogDetCC = halfLogDetC`
(Lemma 2.4 (c): `-½ ∑_y tr 𝕃(y,y)` is real and equals `½ log det C^{(k)}`). -/
theorem halfLogDetCC_eq : S.halfLogDetCC = (S.halfLogDetC : ℂ) := by
  have h2 := S.halfLogDetC_eq_trace H hδ'0 hδ' hD'R hδ0 hχ hfam hsm
  have h3 := S.trace_logA_im H hδ'0 hδ' hD'R hδ0 hχ hfam hsm
  unfold halfLogDetCC
  rw [S.logAC_eq H hδ'0 hδ' hD'R, h2]
  generalize (∑ y : S.U, ∑ i : Fin N, S.logA (y, i) (y, i)) = T at h3 ⊢
  have h4 : T = ((T.re : ℝ) : ℂ) := Complex.ext (by simp) (by rw [Complex.ofReal_im]; exact h3)
  conv_lhs => rw [h4]
  push_cast
  ring

include H hδ'0 hδ' hD'R hδ0 hχ hfam hsm in
/-- **Real data: `det C^{(k)1/2} = |det K|`**, the Jacobian of the substitution (2.7). -/
theorem det_covSqrtC_real : S.covSqrtC.det = ((|LinearMap.det S.K| : ℝ) : ℂ) := by
  obtain ⟨h1, h2⟩ := S.covData_of_real H hδ'0 hδ' hD'R hδ0 hχ hfam
  rw [S.det_covSqrtC h1 h2 hδ0.le hsm, S.halfLogDetCC_eq H hδ'0 hδ' hD'R hδ0 hχ hfam hsm,
    ← Complex.ofReal_exp, ← S.abs_det_K H hδ'0 hδ' hD'R hδ0 hχ hfam hsm]

end Det

/-! ### The fluctuation integral and the new terms -/

section Out

variable (ha₁ : 0 < S.a₁) (H : BgHyp d L (k + 1) ϱ S.a S.ν)
  {δ' : ℝ} (hδ'0 : 0 < δ') (hδ' : δ' ≤ thm73C3 d L N / 2) (hD'R : InDomainR S.G' S.ν δ' S.D')
  (hδ0 : 0 < S.δ)
  (hfam : ∀ x, 0 ≤ x → XData S.G' S.a S.a₁ S.ν x (bgMult S.G' S.a S.ν S.D') 0 (fun _ => 1))
  (hsm : S.δ ^ 2 * smallConstX d L 0 ≤ 1 / 4)
  (hχu : chiU S.G' S.a S.ν S.δ S.D' = 1)
  (hnorm : S.ν * ((L : ℝ) ^ k) ^ 2 * |∑ i, S.h₀ i ^ 2 - 1| < (1 * S.δ) ^ 2)
  (hβ : 0 < S.β) (hp₁ : 0 < S.p₁)
  {B₅ K₂ : ℝ} (hB5 : max 1 (Real.sqrt N * covSupConst d L N (S.a k)) ≤ B₅)
  (hK2 : max (max 1 (cK2 d L N)) (Real.sqrt N * cK2 d L N) ≤ K₂)
  (hp40 : S.p₁ / (S.betaU ^ (1 / 2 : ℝ) * S.δ) ≤ (3 * B₅ * K₂)⁻¹)
  (hrad : B₅ * S.betaU ^ (-(1 / 2 : ℝ)) * S.p₁ ≤ fluctRadius d L N)

include S C ha₁ H hδ'0 hδ' hD'R hδ0 hfam hsm hχu hnorm hβ hp₁ hB5 hK2 hp40 hrad in
/-- **Real data: the fluctuation integral of the complex step is the landed `Tstep`**
(`T^{(k)} χ^{(k)} ρ_k`, Definition 2.1): the change of variables (2.7) in the integral over the real
old spin, and Lemma 2.5 (`χ^{(k)} χ_k = χ_fl` on the path). -/
theorem TstepC_eq (g : Fld d L N₁ m₁ (k + 1) N) : S.TstepC C g = S.Tstep C g := by
  classical
  have hL : 0 < L := Nat.pos_of_ne_zero (NeZero.ne L)
  have hβU := S.betaU_pos' hL hβ
  have hχ := (chiU_eq_one_iff _ _ _ _).1 hχu
  have hdetK := S.det_K_ne H hδ'0 hδ' hD'R hδ0 hχ hfam hsm
  -- the change of variables in the landed integral
  have e1 : S.Tstep C g =
      ((S.betaU ^ (-((N * Fintype.card S.U : ℕ) : ℝ) / 2) * |LinearMap.det S.K| : ℝ) : ℂ) *
        ∫ x : S.E, (S.tKernel (S.psiAt 1 x) : ℂ) * (S.chiK (S.psiAt 1 x) : ℂ) *
          S.rhoStep C g (S.psiAt 1 x) := by
    unfold Tstep
    rw [← integral_add_left_eq_self (μ := (volume : Measure S.E))
      (fun ψ => (S.tKernel ψ : ℂ) * (S.chiK ψ : ℂ) * S.rhoStep C g ψ) S.psi0,
      integral_eq_smul_integral_comp_smul_linearMap_pi S.U N S.K hdetK hβU
        (fun y => (S.tKernel (S.psi0 + y) : ℂ) * (S.chiK (S.psi0 + y) : ℂ) *
          S.rhoStep C g (S.psi0 + y))]
    simp only [S.psi0_add_smul, Complex.real_smul]
  -- the integrands
  have hpt : ∀ x : S.E, (S.tKernel (S.psiAt 1 x) : ℂ) * (S.chiK (S.psiAt 1 x) : ℂ) *
        S.rhoStep C g (S.psiAt 1 x) =
      ((chiFl S.U N S.p₁ x : ℝ) : ℂ) *
        (S.tKernelC (S.psiAtC 1 x) * S.rhoExpC C g (S.psiAtC 1 x)) := by
    intro x
    have hK := S.chiK_psiAt H hδ'0 hδ' hD'R hδ0 hfam hsm hχu hβ x
    by_cases hx : chiFl S.U N S.p₁ x = 1
    · have hxi := S.chiXi_eq_one ha₁ H hδ'0 hδ' hD'R hδ0 hfam hsm hχu hnorm hβ hp₁ hB5 hK2 hp40
        hrad x hx
      have hc22 : chi22 S.G' S.δ S.D' (liftU S.hG' (S.psiAt 1 x)) = 1 := by
        have h := S.chi_absorb ha₁ H hδ'0 hδ' hD'R hδ0 hfam hsm hχu hnorm hβ hp₁ hB5 hK2 hp40
          hrad x
        rw [hx, mul_one, hxi, one_mul] at h
        exact h
      rw [hc22, hx, mul_one] at hK
      have hdom := S.dataU_inDomainR ha₁ H hδ'0 hδ' hD'R hδ0 hfam hsm hχu hnorm hβ hp₁ hB5 hK2
        hp40 hrad x hx
      rw [S.psiAtC_eq ha₁ H hδ'0 hδ' hD'R hδ0 hχ hfam hsm, S.tKernelC_yhat hD'R,
        S.rhoExpC_yhat C H g _ hdom, hK, hx]
      unfold rhoStep
      rw [hxi]
      push_cast
      ring
    · have h0 : chiFl S.U N S.p₁ x = 0 := (chiFl_eq_zero_or_one S.p₁ x).resolve_right hx
      rw [h0, mul_zero] at hK
      rw [hK, h0]
      simp
  have hdet := S.det_covSqrtC_real H hδ'0 hδ' hD'R hδ0 hχ hfam hsm
  unfold TstepC
  rw [e1, hdet]
  simp only [hpt]
  push_cast
  ring

include S C ha₁ H hδ'0 hδ' hD'R hδ0 hfam hsm hχu hnorm hβ hp₁ hB5 hK2 hp40 hrad in
/-- **Real data: `ℰ₁^{(k+1)}` of the complex step is the landed `E1`.** -/
theorem E1C_eq : S.E1C C = S.E1 C := by
  unfold E1C E1
  refine intervalIntegral.integral_congr_uIoo fun s hs => ?_
  rw [Set.uIoo_of_le zero_le_one] at hs
  have hsI : s ∈ Set.Icc (0 : ℝ) 1 := ⟨hs.1.le, hs.2.le⟩
  refine avgFun_congr_ae ?_ ?_
  · exact (S.ae_ball hp₁).mono fun x hx =>
      S.WoneC_eq C ha₁ H hδ'0 hδ' hD'R hδ0 hfam hsm hχu hnorm hβ hp₁ hB5 hK2 hp40 hrad hsI x hx
  · filter_upwards [S.ae_ball hp₁] with x hx
    refine Filter.EventuallyEq.deriv_eq ?_
    filter_upwards [Ioo_mem_nhds hs.1 hs.2] with r hr
    exact S.WoneC_eq C ha₁ H hδ'0 hδ' hD'R hδ0 hfam hsm hχu hnorm hβ hp₁ hB5 hK2 hp40 hrad
      ⟨hr.1.le, hr.2.le⟩ x hx

include S C ha₁ H hδ'0 hδ' hD'R hδ0 hfam hsm hχu hnorm hβ hp₁ hB5 hK2 hp40 hrad in
/-- **Real data: `ℰ₀^{(k+1)}` of the complex step is the landed `E0`.** -/
theorem E0C_eq : S.E0C C = S.E0 C := by
  have hχ := (chiU_eq_one_iff _ _ _ _).1 hχu
  unfold E0C E0
  rw [S.halfLogDetCC_eq H hδ'0 hδ' hD'R hδ0 hχ hfam hsm,
    S.E1C_eq C ha₁ H hδ'0 hδ' hD'R hδ0 hfam hsm hχu hnorm hβ hp₁ hB5 hK2 hp40 hrad]

include S C ha₁ H hδ'0 hδ' hD'R hδ0 hfam hsm hχu hnorm hβ hp₁ hB5 hK2 hp40 hrad in
/-- **Real data: `ℱ₀^{(k+1)}(g)` of the complex step is the landed `F0`.** -/
theorem F0C_eq (g : Fld d L N₁ m₁ (k + 1) N) : S.F0C C g = S.F0 C g := by
  have h1I : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := Set.right_mem_Icc.2 zero_le_one
  unfold F0C F0
  refine intervalIntegral.integral_congr_uIoo fun t ht => ?_
  rw [Set.uIoo_of_le zero_le_one] at ht
  have htI : t ∈ Set.Icc (0 : ℝ) 1 := ⟨ht.1.le, ht.2.le⟩
  refine avgFun₂_congr_ae ?_ ?_ ?_
  · exact (S.ae_ball hp₁).mono fun x hx =>
      S.WoneC_eq C ha₁ H hδ'0 hδ' hD'R hδ0 hfam hsm hχu hnorm hβ hp₁ hB5 hK2 hp40 hrad h1I x hx
  · exact (S.ae_ball hp₁).mono fun x hx =>
      S.WtwoC_eq C ha₁ H hδ'0 hδ' hD'R hδ0 hfam hsm hχu hnorm hβ hp₁ hB5 hK2 hp40 hrad g htI x hx
  · filter_upwards [S.ae_ball hp₁] with x hx
    refine Filter.EventuallyEq.deriv_eq ?_
    filter_upwards [Ioo_mem_nhds ht.1 ht.2] with r hr
    exact S.WtwoC_eq C ha₁ H hδ'0 hδ' hD'R hδ0 hfam hsm hχu hnorm hβ hp₁ hB5 hK2 hp40 hrad g
      ⟨hr.1.le, hr.2.le⟩ x hx

include S C ha₁ H hδ'0 hδ' hD'R hδ0 hfam hsm hχu hnorm hβ hp₁ hB5 hK2 hp40 hrad in
/-- **Real data: `ℳ₀^{(k+1)}(y; g)` of the complex step is the landed `M0`.** -/
theorem M0C_eq (g : Fld d L N₁ m₁ (k + 1) N) (y : CTorus d L N₁ m₁ (k + 1)) (i : Fin N) :
    S.M0C C g y i = S.M0 C g y i := by
  have hχ := (chiU_eq_one_iff _ _ _ _).1 hχu
  have h1I : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := Set.right_mem_Icc.2 zero_le_one
  have hM : ∀ r ∈ Set.Icc (0 : ℝ) 1, ∀ x : S.E, chiFl S.U N S.p₁ x = 1 →
      McompAtC C.m₀ C.Tm S.a S.ν (Nat.le_succ k) (S.dataUC (S.psiAtC r x)) g y i =
        McompAt C.m₀ C.Tm S.a S.ν (Nat.le_succ k) (S.dataU (S.psiAt r x)) g y i := by
    intro r hr x hx
    have hdom := S.dataU_inDomainR_path ha₁ H hδ'0 hδ' hD'R hδ0 hfam hsm hχu hnorm hβ hp₁ hB5 hK2
      hp40 hrad hr x hx
    rw [S.psiAtC_eq ha₁ H hδ'0 hδ' hD'R hδ0 hχ hfam hsm, S.dataUC_yhat, McompAtC_eq H _ _ hdom]
  unfold M0C M0
  refine congrArg (fun z : ℂ => ((S.betaU ^ (1 / 2 : ℝ) : ℝ) : ℂ) * z) ?_
  refine intervalIntegral.integral_congr_uIoo fun t ht => ?_
  rw [Set.uIoo_of_le zero_le_one] at ht
  have htI : t ∈ Set.Icc (0 : ℝ) 1 := ⟨ht.1.le, ht.2.le⟩
  refine avgFun₂_congr_ae ?_ ?_ ?_
  · exact (S.ae_ball hp₁).mono fun x hx =>
      S.WoneC_eq C ha₁ H hδ'0 hδ' hD'R hδ0 hfam hsm hχu hnorm hβ hp₁ hB5 hK2 hp40 hrad h1I x hx
  · exact (S.ae_ball hp₁).mono fun x hx =>
      S.WtwoC_eq C ha₁ H hδ'0 hδ' hD'R hδ0 hfam hsm hχu hnorm hβ hp₁ hB5 hK2 hp40 hrad g htI x hx
  · filter_upwards [S.ae_ball hp₁] with x hx
    refine Filter.EventuallyEq.deriv_eq ?_
    filter_upwards [Ioo_mem_nhds ht.1 ht.2] with r hr
    exact hM r ⟨hr.1.le, hr.2.le⟩ x hx

end Out

/-! ### Proposition 2.6 for the holomorphic objects at a real datum -/

section Public

variable (ha₁ : 0 < S.a₁) (H : BgHyp d L (k + 1) ϱ S.a S.ν)
  {δ' : ℝ} (hδ'0 : 0 < δ') (hδ' : δ' ≤ thm73C3 d L N / 2) (hD'R : InDomainR S.G' S.ν δ' S.D')
  (hδ0 : 0 < S.δ)
  (hfam : ∀ x, 0 ≤ x → XData S.G' S.a S.a₁ S.ν x (bgMult S.G' S.a S.ν S.D') 0 (fun _ => 1))
  (hsm : S.δ ^ 2 * smallConstX d L 0 ≤ 1 / 4)
  (hχu : chiU S.G' S.a S.ν S.δ S.D' = 1)
  (hnorm : S.ν * ((L : ℝ) ^ k) ^ 2 * |∑ i, S.h₀ i ^ 2 - 1| < (1 * S.δ) ^ 2)
  (hβ : 0 < S.β) (hp₁ : 0 < S.p₁) {pp : ℝ} (hlt : S.p₁ < pp)
  {B₅ K₂ : ℝ} (hB5 : max 1 (Real.sqrt N * covSupConst d L N (S.a k)) ≤ B₅)
  (hK2 : max (max 1 (cK2 d L N)) (Real.sqrt N * cK2 d L N) ≤ K₂)
  (hp40 : pp / (S.betaU ^ (1 / 2 : ℝ) * S.δ) ≤ (3 * B₅ * K₂)⁻¹)
  (hrad : B₅ * S.betaU ^ (-(1 / 2 : ℝ)) * pp ≤ fluctRadius d L N)

include S C ha₁ H hδ'0 hδ' hD'R hδ0 hfam hsm hχu hnorm hβ hp₁ hlt hB5 hK2 hp40 hrad in
/-- **Proposition 2.6 for the holomorphic objects, at a real block datum** (the premises of the
landed step): the identity of `prop26C_class` follows from the landed `prop26_complex_class` and the
agreement of the two families of objects on real data.  On the real chart the theorem for the
complex step and the landed theorem are the same statement. -/
theorem prop26C_class_of_real (g : Fld d L N₁ m₁ (k + 1) N) (hc : S.ClassRegular C g)
    (hnv : S.StepNonvanishing C g) :
    S.TstepC C g = Complex.exp (-(S.β : ℂ) * S.AnewC +
      EcompAtC C.m₀ C.Tm S.a S.ν (Nat.le_succ k) S.psiKdC - (S.Eppp C : ℂ) * (S.nU : ℂ) +
      FcompAtC C.m₀ C.Tm S.a S.ν (Nat.le_succ k) S.psiKdC g + S.E0C C + S.F0C C g) := by
  obtain ⟨h40, hr⟩ := S.margin_small hδ0 hβ hlt hB5 hp40 hrad
  rw [S.TstepC_eq C ha₁ H hδ'0 hδ' hD'R hδ0 hfam hsm hχu hnorm hβ hp₁ hB5 hK2 h40 hr g,
    S.AnewC_eq H hδ'0 hδ' hD'R, S.EcompAtC_psiKdC_eq C ha₁ H hδ'0 hδ' hD'R,
    S.FcompAtC_psiKdC_eq C ha₁ H hδ'0 hδ' hD'R g,
    S.E0C_eq C ha₁ H hδ'0 hδ' hD'R hδ0 hfam hsm hχu hnorm hβ hp₁ hB5 hK2 h40 hr,
    S.F0C_eq C ha₁ H hδ'0 hδ' hD'R hδ0 hfam hsm hχu hnorm hβ hp₁ hB5 hK2 h40 hr g]
  exact S.prop26_complex_class C ha₁ H hδ'0 hδ' hD'R hδ0 hfam hsm hχu hnorm hβ hp₁ hlt hB5 hK2
    hp40 hrad g hc hnv

end Public

end StepSetting

end Balaban.Fluctuation
