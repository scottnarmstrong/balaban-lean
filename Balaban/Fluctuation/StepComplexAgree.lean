/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.StepComplex
public import Balaban.Fluctuation.StepIdentity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The complex step restricted to real data is the landed step (FLUCTUATION.md §2.6; RAY-CHART §2)

For a real block datum in the domain of the landed step (`InDomainR S.G' S.ν δ' S.D'`,
`δ' ≤ C₃/2`, as in `StepIdentity`), the objects of `StepComplex` are the landed ones:

* `bgC_eq`, `covSqrtC_eq`, `psiKdC_eq`: the backgrounds, the square root and the critical point
  (Theorem 7.2, agreement with the real field: `theorem72_real`);
* `psi0C_eq`: `psi0C` is the complexification of `psi0` (the critical point is real);
* `shiftUC_eq`: `shiftUC x` is the complexification of `shiftU x` (the square root has real
  entries, `covSqrt_isReal`); `psiAtC_eq`;
* `WoneC_eq`, `WtwoC_eq` on the ray (`s ∈ [0,1]`, `χ_fl(ψ̂) = 1`, where the old spin stays in the
  real domain `𝒟_ℝ`), `ZstC_eq`: `Z_{s,t}` for `s, t ∈ [0,1]`.

For complex data in `𝒟(𝔹'_k)`: `VkC_psi0C` (`V^{(k)}(0) = 0`, by (2.2) for complex data) and
`WoneC_zero`.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban.SmallField.Def6 Balaban.Background Balaban.Multiscale Balaban.Localization
  Balaban.SmallField Finset Matrix

namespace StepSetting

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}
  (S : StepSetting d L N₁ m₁ k N ϱ) (C : StepClass d L N₁ m₁ k N ϱ)

/-! ### The complexification of real fields of the unit lattice -/

theorem yhat_add (x y : S.E) : yhat (x + y) = yhat x + yhat y := by
  funext q
  simp [yhat]

/-- For a square root with real entries, the hat field of the complexification of a real
fluctuation variable is the complexification of the landed `shiftU`. -/
theorem hatField_covSqrt_yhat (hreal : IsRealMat S.covSqrt) (x : S.E) :
    S.hatField S.covSqrt (yhat x) = yhat (S.shiftU x) := by
  funext q
  obtain ⟨b, i⟩ := q
  simp only [StepSetting.hatField, Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct,
    StepSetting.shiftU, StepSetting.K, matMap_apply, PiLp.smul_apply, yhat]
  push_cast
  congr 1
  refine Finset.sum_congr rfl fun r _ => ?_
  have := hreal (b, i) r
  rw [Matrix.map_apply]
  rw [Complex.conj_eq_iff_re] at this
  rw [this]

/-- **The substitution (2.7) on the real chart, from its two inputs**: if the complex square root
is the landed one and has real entries, then `shiftUC x` is the complexification of `shiftU x`. -/
theorem shiftUC_eq_of_isRealMat (hC : S.covSqrtC = S.covSqrt) (hreal : IsRealMat S.covSqrt)
    (x : S.E) : S.shiftUC x = yhat (S.shiftU x) := by
  rw [S.shiftUC_eq_hatField, hC, S.hatField_covSqrt_yhat hreal]

/-! ### Real data: the backgrounds, the square root, the critical point -/

section Bg

variable (ha₁ : 0 < S.a₁) (H : BgHyp d L (k + 1) ϱ S.a S.ν) {δ' : ℝ} (hδ'0 : 0 < δ')
  (hδ' : δ' ≤ thm73C3 d L N / 2) (hD'R : InDomainR S.G' S.ν δ' S.D')

include H hδ'0 hδ' hD'R in
/-- **Real data: the complex small solution of `θ` is the real background** (Theorem 7.2). -/
theorem bgC_eq :
    bgFieldC S.G' S.a S.ν (bgC0 d L N) S.D' = bgField S.G' S.a S.ν S.D' ∧
      bgMultC S.G' S.a S.ν (bgC0 d L N) S.D' = bgMult S.G' S.a S.ν S.D' := by
  have hd0 : 0 < d := by have := H.hd; omega
  obtain ⟨-, -, hδ'c1, -⟩ := theta_consts hd0 hδ'0 hδ'
  exact theorem72_real H ⟨δ', hδ'0, hδ'c1, hD'R⟩

include H hδ'0 hδ' hD'R in
/-- **Real data: `C^{(k)1/2}` of the complex step is the landed `covSqrt`** (RAY-CHART (3.1)). -/
theorem covSqrtC_eq : S.covSqrtC = S.covSqrt := by
  obtain ⟨hf, hm⟩ := S.bgC_eq H hδ'0 hδ' hD'R
  unfold covSqrtC covSqrt
  rw [hf, hm]

include H hδ'0 hδ' hD'R in
/-- **Real data: the critical point of the complex step is the landed `psiKd`.** -/
theorem psiKdC_eq : S.psiKdC = S.psiKd := by
  unfold psiKdC psiKd psiK
  rw [(S.bgC_eq H hδ'0 hδ' hD'R).1]

include ha₁ H hδ'0 hδ' hD'R in
/-- **Real data: `psi0C` is the complexification of `psi0`** (the critical point is real,
`criticalPoint_real`). -/
theorem psi0C_eq : S.psi0C = yhat S.psi0 := by
  obtain ⟨hDU', -⟩ := S.D'_domains H hδ'0 hδ' hD'R
  have hpsiReal := (criticalPoint_real ha₁ S.hG S.hG' (le_refl (k + 1)) H H S.D' hDU').1
  funext q
  have him : (S.psiKd.Ψ (unitRep (G' := S.G') q.1) q.2).im = 0 := (hpsiReal _ _).1
  show S.psiKdC.Ψ (unitRep (G' := S.G') q.1) q.2 =
    (((S.psiKd.Ψ (unitRep (G' := S.G') q.1) q.2).re : ℝ) : ℂ)
  rw [S.psiKdC_eq H hδ'0 hδ' hD'R]
  exact Complex.ext (by simp) (by simpa using him)

end Bg

section Shift

variable (ha₁ : 0 < S.a₁) (H : BgHyp d L (k + 1) ϱ S.a S.ν) {δ' : ℝ} (hδ'0 : 0 < δ')
  (hδ' : δ' ≤ thm73C3 d L N / 2) (hD'R : InDomainR S.G' S.ν δ' S.D')
  (hδ0 : 0 < S.δ)
  (hχ : ChiUBounds S.G' S.ν S.δ S.D' (bgField S.G' S.a S.ν S.D') (bgMult S.G' S.a S.ν S.D'))
  (hfam : ∀ x, 0 ≤ x → XData S.G' S.a S.a₁ S.ν x (bgMult S.G' S.a S.ν S.D') 0 (fun _ => 1))
  (hsm : S.δ ^ 2 * smallConstX d L 0 ≤ 1 / 4)

include H hδ'0 hδ' hD'R hδ0 hχ hfam hsm in
/-- **Real data: the entries of `C^{(k)1/2}` of the complex step are real.** -/
theorem covSqrtC_isReal : IsRealMat S.covSqrtC := by
  rw [S.covSqrtC_eq H hδ'0 hδ' hD'R]
  exact S.covSqrt_isReal H hδ'0 hδ' hD'R hδ0 hχ hfam hsm

include H hδ'0 hδ' hD'R hδ0 hχ hfam hsm in
/-- **Real data: the substitution (2.7) of the complex step is the landed one**,
`shiftUC x = ↑(shiftU x)` coordinatewise (RAY-CHART (3.2) on the unit lattice). -/
theorem shiftUC_eq (x : S.E) : S.shiftUC x = yhat (S.shiftU x) :=
  S.shiftUC_eq_of_isRealMat (S.covSqrtC_eq H hδ'0 hδ' hD'R)
    (S.covSqrt_isReal H hδ'0 hδ' hD'R hδ0 hχ hfam hsm) x

include ha₁ H hδ'0 hδ' hD'R hδ0 hχ hfam hsm in
/-- **Real data: the path of the interpolation of the complex step is the landed one.** -/
theorem psiAtC_eq (s : ℝ) (x : S.E) : S.psiAtC s x = yhat (S.psiAt s x) := by
  unfold psiAtC psiAt
  rw [S.psi0C_eq ha₁ H hδ'0 hδ' hD'R, S.shiftUC_eq H hδ'0 hδ' hD'R hδ0 hχ hfam hsm, S.yhat_add,
    yhat_smul]

end Shift

/-! ### Real data: the exponents and the partition functions -/

section Exponents

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
/-- **Real data: `W₁` of the complex step is the landed `Wone` on the ray** (`s ∈ [0,1]`,
`χ_fl(ψ̂) = 1`): there the old spin `ψ^{(k)} + s ψ'` is real and in `𝒟_ℝ`, where the composite
`ℰ_k` with the complex backgrounds is the landed one. -/
theorem WoneC_eq {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) (x : S.E) (hx : chiFl S.U N S.p₁ x = 1) :
    S.WoneC C s x = S.Wone C s x := by
  have hχ := (chiU_eq_one_iff _ _ _ _).1 hχu
  have hdom := S.dataU_inDomainR_path ha₁ H hδ'0 hδ' hD'R hδ0 hfam hsm hχu hnorm hβ hp₁ hB5 hK2 hp40
    hrad hs x hx
  have hdom0 := S.dataU_psi0_domain ha₁ H hδ'0 hδ' hD'R
  unfold WoneC Wone dEC dE
  rw [S.psiAtC_eq ha₁ H hδ'0 hδ' hD'R hδ0 hχ hfam hsm, S.VkC_yhat, S.dataUC_yhat,
    S.psi0C_eq ha₁ H hδ'0 hδ' hD'R, S.dataUC_yhat, EcompAtC_eq H _ _ hdom, EcompAtC_eq H _ _ hdom0]

include S C ha₁ H hδ'0 hδ' hD'R hδ0 hfam hsm hχu hnorm hβ hp₁ hB5 hK2 hp40 hrad in
/-- **Real data: `W₂` of the complex step is the landed `Wtwo` on the ray** (`t ∈ [0,1]`,
`χ_fl(ψ̂) = 1`), for every (complex) source `g`. -/
theorem WtwoC_eq (g : Fld d L N₁ m₁ (k + 1) N) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) (x : S.E)
    (hx : chiFl S.U N S.p₁ x = 1) : S.WtwoC C g t x = S.Wtwo C g t x := by
  have hχ := (chiU_eq_one_iff _ _ _ _).1 hχu
  have hdom := S.dataU_inDomainR_path ha₁ H hδ'0 hδ' hD'R hδ0 hfam hsm hχu hnorm hβ hp₁ hB5 hK2 hp40
    hrad ht x hx
  have hdom0 := S.dataU_psi0_domain ha₁ H hδ'0 hδ' hD'R
  unfold WtwoC Wtwo dFC dF
  rw [S.psiAtC_eq ha₁ H hδ'0 hδ' hD'R hδ0 hχ hfam hsm, S.dataUC_yhat,
    S.psi0C_eq ha₁ H hδ'0 hδ' hD'R, S.dataUC_yhat, FcompAtC_eq H _ _ hdom, FcompAtC_eq H _ _ hdom0]

include S C ha₁ H hδ'0 hδ' hD'R hδ0 hfam hsm hχu hnorm hβ hp₁ hB5 hK2 hp40 hrad in
/-- **Real data: the exponent of the complex step is the landed one `ν_{p₁}`-almost everywhere**,
at every point of the square `[0,1]²` of the interpolation. -/
theorem ae_WoneC_add_WtwoC_eq (g : Fld d L N₁ m₁ (k + 1) N) {s t : ℝ}
    (hs : s ∈ Set.Icc (0 : ℝ) 1) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ∀ᵐ x ∂S.nuFl, S.WoneC C s x + S.WtwoC C g t x = S.Wone C s x + S.Wtwo C g t x := by
  filter_upwards [S.ae_ball hp₁] with x hx
  rw [S.WoneC_eq C ha₁ H hδ'0 hδ' hD'R hδ0 hfam hsm hχu hnorm hβ hp₁ hB5 hK2 hp40 hrad hs x hx,
    S.WtwoC_eq C ha₁ H hδ'0 hδ' hD'R hδ0 hfam hsm hχu hnorm hβ hp₁ hB5 hK2 hp40 hrad g ht x hx]

include S C ha₁ H hδ'0 hδ' hD'R hδ0 hfam hsm hχu hnorm hβ hp₁ hB5 hK2 hp40 hrad in
/-- **Real data: the partition functions of the complex step are the landed `Z_{s,t}`**,
`s, t ∈ [0,1]`. -/
theorem ZstC_eq (g : Fld d L N₁ m₁ (k + 1) N) {s t : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1)
    (ht : t ∈ Set.Icc (0 : ℝ) 1) : S.ZstC C g s t = S.Zst C g s t := by
  unfold ZstC Zst
  exact partFun₂_congr_ae
    ((S.ae_ball hp₁).mono fun x hx =>
      S.WoneC_eq C ha₁ H hδ'0 hδ' hD'R hδ0 hfam hsm hχu hnorm hβ hp₁ hB5 hK2 hp40 hrad hs x hx)
    ((S.ae_ball hp₁).mono fun x hx =>
      S.WtwoC_eq C ha₁ H hδ'0 hδ' hD'R hδ0 hfam hsm hχu hnorm hβ hp₁ hB5 hK2 hp40 hrad g ht x hx)

end Exponents

/-! ### Complex data: the exponents vanish at `s = 0` -/

/-- The interaction vanishes at the composed critical datum for any incoming field. -/
theorem interactionV_critical_core (D : BgData S.G' N)
    (ha₁ : 0 < S.a₁) (H : BgHyp d L (k + 1) ϱ S.a S.ν)
    (hD : InUnionDomainC S.G' (bgC0 d L N) (thm73C1 d L N) S.ν D) :
    let B := composeData (S.hG.precedes S.hG' (le_refl (k + 1))) S.a
      (bgFieldC S.G' S.a S.ν (bgC0 d L N) D) D
    interactionV (S.hG.precedes S.hG' (le_refl (k + 1))) S.a S.ν
      (bgMultC S.G' S.a S.ν (bgC0 d L N) D)
      (bgFieldC S.G' S.a S.ν (bgC0 d L N) D)
      (compTangent S.hG S.hG' (le_refl (k + 1)) S.a
        (bgFieldC S.G' S.a S.ν (bgC0 d L N) D) D B)
      (bgFieldC (stepG d L N₁ m₁ k ϱ) S.a S.ν (bgC0 d L N) B -
        (S.hG.precedes S.hG' (le_refl (k + 1))).restrictφ
          (bgFieldC S.G' S.a S.ν (bgC0 d L N) D)) = 0 := by
  dsimp only
  obtain ⟨-, -, hfield, -⟩ :=
    criticalPoint_complex ha₁ S.hG S.hG' (le_refl (k + 1)) H H D hD
  have htan : compTangent S.hG S.hG' (le_refl (k + 1)) S.a
      (bgFieldC S.G' S.a S.ν (bgC0 d L N) D) D
      (composeData (S.hG.precedes S.hG' (le_refl (k + 1))) S.a
        (bgFieldC S.G' S.a S.ν (bgC0 d L N) D) D) = 0 := by
    funext z i
    unfold compTangent
    exact sub_self _
  rw [htan, hfield, sub_self]
  exact interactionV_zero' _ _ _ _ _

section Zero

variable (ha₁ : 0 < S.a₁) (H : BgHyp d L (k + 1) ϱ S.a S.ν)
  (hD' : InUnionDomainC S.G' (bgC0 d L N) (thm73C1 d L N) S.ν S.D')

include ha₁ H hD' in
/-- **`V^{(k)}(0) = 0` at a complex datum** of `𝒟(𝔹'_k)`: by (2.2) for complex data
(FLUCTUATION Lemma 2.2 (c); `criticalPoint_complex`), the small solution of the critical point is
the restriction of `φ_{k+1}(θ)`.  The complex form of `Vk_psi0`, with no realness hypothesis. -/
theorem VkC_psi0C : S.VkC S.psi0C = 0 := by
  unfold VkC
  rw [S.dataUC_psi0C]
  exact S.interactionV_critical_core S.D' ha₁ H hD'

include ha₁ H hD' in
/-- **`W₁(0, ψ̂) = 0` at a complex datum** of `𝒟(𝔹'_k)`. -/
theorem WoneC_zero (x : S.E) : S.WoneC C 0 x = 0 := by
  unfold WoneC dEC
  rw [S.psiAtC_zero, S.VkC_psi0C ha₁ H hD']
  simp

end Zero

end StepSetting

end Balaban.Fluctuation
