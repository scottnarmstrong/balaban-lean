/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.StepComplexSource
public import Balaban.Fluctuation.StepComplexProp26Agree
public import Balaban.Fluctuation.StepRegClass
public import Balaban.Fluctuation.StepRegWitness
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
  `E1loc`, `E0loc` (P4 (2.56)-(2.60));
* `exists_complex_tube_inUnionDomainC`, `analyticAt_VkC_shift_of_eventually`,
  `RayData.classRegularLocC_zeroClass`: a complex neighbourhood of a real old spin of `𝒟_ℝ` lies in
  the complex domain `𝒟`, so that for the class with zero old terms `ClassRegularLocC` holds on the
  real chart (under `RayData` alone);
* `E1locC_zeroClass_eq`, `E0locC_zeroClass_eq`: hence for the zero class the agreement holds with no
  hypothesis on the class; `exists_real_E0locC_eq`: at the landed real witness of `RayData`.

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

/-! ### The class with zero old terms on the real chart -/

variable (S) in
/-- **A complex neighbourhood of a real old spin of `𝒟_ℝ` lies in the complex domain `𝒟`**: if the
datum of the real old spin `ψ₀` is in `𝒟_ℝ(𝔹_k)` (`InUnionDomainR`, parameter `δ`), then for every
complex field `η` of the unit lattice with small coordinates the datum of `ψ₀ + η` is in
`𝒟(𝔹_k) = InUnionDomainC` (with `ε = δ`: the conditions (C1)-(C3) of `Ψ̃^c(δ, δ)` on the complex
perturbation are strict inequalities). -/
theorem exists_complex_tube_inUnionDomainC (H : BgHyp d L (k + 1) ϱ S.a S.ν) {ψ₀ : S.E}
    (hD : InUnionDomainR (stepG d L N₁ m₁ k ϱ) (bgC1 d L N) S.ν (S.dataU ψ₀)) :
    ∃ r : ℝ, 0 < r ∧ ∀ η : S.EC, (∀ q, ‖η q‖ < r) →
      InUnionDomainC (stepG d L N₁ m₁ k ϱ) (bgC0 d L N) (bgC1 d L N) S.ν
        (S.dataUC (yhat ψ₀ + η)) := by
  have hd0 : 0 < d := by have := H.hd; omega
  obtain ⟨δ, hδ0, hδc, Ψ, h, hP, hΨ, hh⟩ := hD
  set B : ℝ := 1 + δ with hB
  have hB0 : 0 < B := by positivity
  set K : ℝ := 2 * (N * (2 * B + 1)) + 1 with hK
  have hK0 : 0 < K := by positivity
  set r : ℝ := min 1 (δ / (2 * K)) with hr
  have hr0 : 0 < r := lt_min one_pos (by positivity)
  have hr1 : r ≤ 1 := min_le_left _ _
  have hKr : K * r ≤ δ / 2 := by
    calc K * r ≤ K * (δ / (2 * K)) := mul_le_mul_of_nonneg_left (min_le_right _ _) hK0.le
      _ = δ / 2 := by field_simp
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have h2N : (N : ℝ) * r + N * r ≤ K * r := by
    have : (N : ℝ) + N ≤ K := by rw [hK]; nlinarith
    nlinarith
  have hNB : (N : ℝ) * ((2 * B + 1) * r) ≤ K * r := by
    have : (N : ℝ) * (2 * B + 1) ≤ K := by rw [hK]; nlinarith
    nlinarith
  refine ⟨r, hr0, fun η hη => ⟨δ, δ, hδ0, le_rfl, hδc.trans (bgC1_le_bgC0 d L N hd0), hδc, ?_,
    ?_⟩⟩
  · have := H.massLe
    nlinarith [sq_nonneg δ]
  have hvn : ∀ x : CTorus d L N₁ m₁ (k + 1), vn (liftC S.hG' η x) ≤ N * r := fun x =>
    vn_le_card_mul hr0.le fun i => (hη _).le
  have hΨb : ∀ x ∈ dataSites (stepG d L N₁ m₁ k ϱ), ∀ i, |Ψ x i| ≤ B := by
    intro x hx i
    have h2 := hP.r2 x hx
    have h3 : Ψ x i ^ 2 ≤ ∑ j, Ψ x j ^ 2 :=
      Finset.single_le_sum (f := fun j => Ψ x j ^ 2) (fun j _ => sq_nonneg _) (Finset.mem_univ i)
    have h4 : ∑ j, Ψ x j ^ 2 < 1 + δ := by
      have := (abs_lt.1 h2).2
      linarith
    have h5 : |Ψ x i| ^ 2 ≤ B ^ 2 := by
      rw [sq_abs]
      nlinarith
    exact (sq_le_sq₀ (abs_nonneg _) hB0.le).1 h5
  refine ⟨Ψ, h, liftC S.hG' η, 0, ⟨hP, hδ0, isLayerConstant_liftC S.hG S.hG' η,
    fun _ _ _ _ _ _ _ => rfl, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · intro x x' _
    calc vn (liftC S.hG' η x - liftC S.hG' η x')
        ≤ vn (liftC S.hG' η x) + vn (liftC S.hG' η x') := vn_sub_le_add _ _
      _ ≤ N * r + N * r := add_le_add (hvn x) (hvn x')
      _ < δ := by linarith
  · intro x _
    have := hvn x
    nlinarith
  · intro x hx
    have e : ∑ i, ((Ψ x i : ℂ) + liftC S.hG' η x i) * ((Ψ x i : ℂ) + liftC S.hG' η x i) -
        ∑ i, (Ψ x i : ℂ) * (Ψ x i : ℂ) =
        ∑ i, (2 * (Ψ x i : ℂ) * liftC S.hG' η x i +
          liftC S.hG' η x i * liftC S.hG' η x i) := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      ring
    rw [e]
    have hterm : ∀ i : Fin N, ‖2 * (Ψ x i : ℂ) * liftC S.hG' η x i +
        liftC S.hG' η x i * liftC S.hG' η x i‖ ≤ (2 * B + 1) * r := by
      intro i
      have he : ‖liftC S.hG' η x i‖ ≤ r := (hη _).le
      have he0 : 0 ≤ ‖liftC S.hG' η x i‖ := norm_nonneg _
      have hΨi : ‖(Ψ x i : ℂ)‖ ≤ B := by
        rw [Complex.norm_real]
        exact hΨb x hx i
      have hΨ0 : 0 ≤ ‖(Ψ x i : ℂ)‖ := norm_nonneg _
      have h1 : ‖2 * (Ψ x i : ℂ) * liftC S.hG' η x i‖ ≤ 2 * B * r := by
        rw [norm_mul, norm_mul, Complex.norm_ofNat]
        have := mul_le_mul hΨi he he0 hB0.le
        nlinarith
      have h2 : ‖liftC S.hG' η x i * liftC S.hG' η x i‖ ≤ r * r := by
        rw [norm_mul]
        exact mul_le_mul he he he0 hr0.le
      calc _ ≤ ‖2 * (Ψ x i : ℂ) * liftC S.hG' η x i‖ +
            ‖liftC S.hG' η x i * liftC S.hG' η x i‖ := norm_add_le _ _
        _ ≤ 2 * B * r + r * r := add_le_add h1 h2
        _ ≤ (2 * B + 1) * r := by nlinarith
    calc ‖∑ i, (2 * (Ψ x i : ℂ) * liftC S.hG' η x i +
          liftC S.hG' η x i * liftC S.hG' η x i)‖
        ≤ ∑ _i : Fin N, (2 * B + 1) * r :=
          (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => hterm i)
      _ = N * ((2 * B + 1) * r) := by simp
      _ < δ := by linarith
  · intro x _
    simp only [vn, Pi.zero_apply]
    have : 0 < δ ^ 2 / δ := by positivity
    simpa using this
  · intro x _
    simp [hδ0]
  · intro x hx i
    have h1 := hΨ x hx i
    rw [S.dataU_Ψ] at h1
    rw [S.dataUC_Ψ, ← h1]
    rfl
  · intro x hx i
    have h1 := hh x hx i
    rw [S.dataU_h] at h1
    rw [S.dataUC_h, h1]
    simp

variable (S) in
/-- **The interaction `V^{(k)}(ψ')` of the complex step is analytic in the complex shift at every
shift near which the old spin stays in the domain `𝒟(𝔹_k)`** (FLUCTUATION Lemma 2.3 (d); the form
of `analyticAt_VkC_shift` with the domain inclusion as the premise). -/
theorem analyticAt_VkC_shift_of_eventually (H : BgHyp d L (k + 1) ϱ S.a S.ν)
    (hH : IsUnit (opHk (S.hG.precedes S.hG' (le_refl (k + 1))) S.a S.ν
      (bgMultC S.G' S.a S.ν (bgC0 d L N) S.D')))
    (hM : IsUnit (constraintForm
      (opHk (S.hG.precedes S.hG' (le_refl (k + 1))) S.a S.ν
        (bgMultC S.G' S.a S.ν (bgC0 d L N) S.D'))⁻¹
      (fieldBase (S.hG.precedes S.hG' (le_refl (k + 1)))
        (bgFieldC S.G' S.a S.ν (bgC0 d L N) S.D')))) {y₀ : S.EC}
    (hdom : ∀ᶠ y in nhds y₀, InUnionDomainC (stepG d L N₁ m₁ k ϱ) (bgC0 d L N) (bgC1 d L N) S.ν
      (S.dataUC (S.psi0C + y))) :
    AnalyticAt ℂ (fun y : S.EC => S.VkC (S.psi0C + y)) y₀ := by
  obtain ⟨F, hF, hFe⟩ := theorem72_analytic (G := stepG d L N₁ m₁ k ϱ) (a := S.a) (ν := S.ν)
    (N := N) H
  have hFat : AnalyticAt ℂ (fun y : S.EC => F (S.rawUC (S.psi0C + y))) y₀ := by
    have h1 : AnalyticAt ℂ F (S.rawUC (S.psi0C + y₀)) :=
      hF _ ⟨S.dataUC (S.psi0C + y₀), hdom.self_of_nhds, (S.dataUC_raw _).symm⟩
    exact AnalyticAt.comp (f := fun y : S.EC => S.rawUC (S.psi0C + y)) h1
      (S.analyticAt_rawUC_shift y₀)
  have hmodel := analyticAt_interactionV (q₀ := y₀) (S.hG.precedes S.hG' (le_refl (k + 1))) S.a S.ν
    (αF := fun _ : S.EC => bgMultC S.G' S.a S.ν (bgC0 d L N) S.D')
    (φF := fun _ : S.EC => bgFieldC S.G' S.a S.ν (bgC0 d L N) S.D')
    (ψF := fun y : S.EC => liftC S.hG' y)
    (φ'F := fun y : S.EC => (F (S.rawUC (S.psi0C + y))).1 -
      (S.hG.precedes S.hG' (le_refl (k + 1))).restrictφ
        (bgFieldC S.G' S.a S.ν (bgC0 d L N) S.D'))
    (fun _ => analyticAt_const) (fun _ => analyticAt_const)
    (fun z i => by
      simp only [liftC_apply]
      exact (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : S.U × Fin N => ℂ)
        (unitPt S.hG' z, i)).analyticAt y₀)
    (fun r => (analyticAt_pi_iff.1 (analyticAt_fst.comp hFat) r).sub analyticAt_const) hH hM
  refine hmodel.congr ?_
  filter_upwards [hdom] with y hy
  have hFq := hFe (S.dataUC (S.psi0C + y)) hy
  rw [S.dataUC_raw] at hFq
  unfold VkC
  rw [S.compTangent_dataUC, add_sub_cancel_left, hFq]

/-- **Real data: `ClassRegularLocC` holds for the class with zero old terms** (rule 10 on the real
chart), for a real block datum with the premises of the landed step (`RayData`, `p₁ < p⁺`):
`Φ₁ = -β_k V^{(k)}` is analytic at the real shifts of the segments, because a complex neighbourhood
of a real old spin of `𝒟_ℝ` lies in `𝒟` (`exists_complex_tube_inUnionDomainC`). -/
theorem RayData.classRegularLocC_zeroClass (R : S.RayData pp) (hlt : S.p₁ < pp) :
    S.ClassRegularLocC (zeroClass d L N₁ m₁ k N ϱ) := by
  have hχ := (chiU_eq_one_iff _ _ _ _).1 R.hχu
  have hD'2 := (S.D'_domains R.H R.hδ'0 R.hδ' R.hD'R).2
  obtain ⟨δs, Φ, St, hΦ⟩ := base_standing R.ha₁ S.hG S.hG' (le_refl (k + 1)) R.H R.H S.D' hD'2
  have hΦ' : restrictField (stepG d L N₁ m₁ k ϱ) Φ =
      fieldBase (S.hG.precedes S.hG' (le_refl (k + 1)))
        (bgFieldC S.G' S.a S.ν (bgC0 d L N) S.D') := funext fun x => funext fun i => hΦ x i
  have hH : IsUnit (opHk (S.hG.precedes S.hG' (le_refl (k + 1))) S.a S.ν
      (bgMultC S.G' S.a S.ν (bgC0 d L N) S.D')) :=
    dirichletOperator_isUnit (stepG d L N₁ m₁ k ϱ) St.pos St.mass St.weights _ St.alpha
  have hM : IsUnit (constraintForm
      (opHk (S.hG.precedes S.hG' (le_refl (k + 1))) S.a S.ν
        (bgMultC S.G' S.a S.ν (bgC0 d L N) S.D'))⁻¹
      (fieldBase (S.hG.precedes S.hG' (le_refl (k + 1)))
        (bgFieldC S.G' S.a S.ν (bgC0 d L N) S.D'))) := by
    rw [← hΦ']
    exact constraintForm_isUnit St
  have hΦ1 : S.Phi1C (zeroClass d L N₁ m₁ k N ϱ) =
      fun y => -(S.β : ℂ) * S.VkC (S.psi0C + y) := by
    funext y
    unfold Phi1C
    rw [dEC_zeroClass, add_zero]
  refine ⟨{y | AnalyticAt ℂ (S.Phi1C (zeroClass d L N₁ m₁ k N ϱ)) y}, isOpen_analyticAt ℂ _,
    AnalyticOnNhd.contDiffOn_of_completeSpace (fun y hy => hy), fun x hx s hs => ?_⟩
  -- the real shift of the segment, and a complex neighbourhood of it
  have hsh : S.shiftUC x = yhat (S.shiftU x) :=
    S.shiftUC_eq R.H R.hδ'0 R.hδ' R.hD'R R.hδ0 hχ R.hfam R.hsm x
  have hpt : (s : ℂ) • S.shiftUC x = yhat (s • S.shiftU x) := by
    rw [hsh, yhat_smul]
  have hdomR : InUnionDomainR (stepG d L N₁ m₁ k ϱ) (bgC1 d L N) S.ν
      (S.dataU (S.psi0 + s • S.shiftU x)) := by
    rw [R.psi0_add_eq (s • S.shiftU x)]
    exact R.dom (q := ((1 : ℝ), S.unshiftU (s • S.shiftU x))) (R.unshift_ray hlt hx hs)
  obtain ⟨r, hr, htube⟩ := S.exists_complex_tube_inUnionDomainC R.H hdomR
  have hopen : IsOpen {y : S.EC | ∀ q, ‖(y - yhat (s • S.shiftU x)) q‖ < r} := by
    have : {y : S.EC | ∀ q, ‖(y - yhat (s • S.shiftU x)) q‖ < r} =
        ⋂ q, {y : S.EC | ‖(y - yhat (s • S.shiftU x)) q‖ < r} := by
      ext y; simp
    rw [this]
    exact isOpen_iInter_of_finite fun q => isOpen_lt
      (continuous_norm.comp ((continuous_apply q).comp (continuous_id.sub continuous_const)))
      continuous_const
  have hmem0 : yhat (s • S.shiftU x) ∈ {y : S.EC | ∀ q, ‖(y - yhat (s • S.shiftU x)) q‖ < r} := by
    intro q
    simpa using hr
  have hdom : ∀ᶠ y in nhds (yhat (s • S.shiftU x)),
      InUnionDomainC (stepG d L N₁ m₁ k ϱ) (bgC0 d L N) (bgC1 d L N) S.ν
        (S.dataUC (S.psi0C + y)) := by
    filter_upwards [hopen.mem_nhds hmem0] with y hy
    have e : S.psi0C + y = yhat (S.psi0 + s • S.shiftU x) + (y - yhat (s • S.shiftU x)) := by
      rw [S.psi0C_eq R.ha₁ R.H R.hδ'0 R.hδ' R.hD'R, S.yhat_add]
      abel
    rw [e]
    exact htube _ hy
  show AnalyticAt ℂ (S.Phi1C (zeroClass d L N₁ m₁ k N ϱ)) ((s : ℂ) • S.shiftUC x)
  rw [hpt, hΦ1]
  exact analyticAt_const.mul (S.analyticAt_VkC_shift_of_eventually R.H hH hM hdom)

/-- **Real data, zero class: `ℰ₁^{(k+1)}(z)` of the complex step is the landed `E1loc`**, for a real
block datum with the premises of the landed step (`RayData`, `p₁ < p⁺`), with no hypothesis on the
class. -/
theorem E1locC_zeroClass_eq (R : S.RayData pp) (hp₁ : 0 < S.p₁) (hlt : S.p₁ < pp)
    (z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1)))) :
    S.E1locC (zeroClass d L N₁ m₁ k N ϱ) z = S.E1loc (zeroClass d L N₁ m₁ k N ϱ) z :=
  E1locC_eq _ R hp₁ hlt (R.classRegularLocC_zeroClass hlt) z

/-- **Real data, zero class: `ℰ₀^{(k+1)}(z)` of the complex step is the landed `E0loc`**, for a real
block datum with the premises of the landed step (`RayData`, `p₁ < p⁺`). -/
theorem E0locC_zeroClass_eq (R : S.RayData pp) (hp₁ : 0 < S.p₁) (hlt : S.p₁ < pp)
    (z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1)))) :
    S.E0locC (zeroClass d L N₁ m₁ k N ϱ) z = S.E0loc (zeroClass d L N₁ m₁ k N ϱ) z :=
  E0locC_eq _ R hp₁ hlt (R.classRegularLocC_zeroClass hlt) z

open Balaban.Localization.I5Inhabited in
/-- **`ClassRegularLocC` and the agreement of the localized energies are not vacuous on the real
chart**: at the landed real witness of `RayData` (`nonempty_rayData`: `d = L = 3`, `N = 2`,
`β > 0`, `θ ≡ e₀`), `ClassRegularLocC` holds for the zero class and `E0locC = E0loc`. -/
theorem exists_real_E0locC_eq :
    ∃ (m₁ : ℕ) (S : StepSetting 3 3 6 m₁ 1 2 (rhoSep m₁)), 0 < S.β ∧ 0 < S.p₁ ∧
      Nonempty (S.RayData 2) ∧ S.ClassRegularLocC (zeroClass 3 3 6 m₁ 1 2 (rhoSep m₁)) ∧
      ∀ z, S.E0locC (zeroClass 3 3 6 m₁ 1 2 (rhoSep m₁)) z =
        S.E0loc (zeroClass 3 3 6 m₁ 1 2 (rhoSep m₁)) z := by
  obtain ⟨m₁, S, hβ, hp₁, hlt, ⟨R⟩⟩ := nonempty_rayData
  exact ⟨m₁, S, hβ, hp₁, ⟨R⟩, R.classRegularLocC_zeroClass hlt,
    fun z => E0locC_zeroClass_eq R hp₁ hlt z⟩

end StepSetting

end Balaban.Fluctuation
