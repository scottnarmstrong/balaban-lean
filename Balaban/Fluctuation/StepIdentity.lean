/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.StepIdentityQuad
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Proposition 2.6 for the actual step objects (FLUCTUATION.md §2.6, whole lattice, `λ = ∞`)

Basic facts on the step objects of `StepObjects`: the datum of a real old spin on the unit lattice,
the background `ψ^{(k)}(θ)` and the substitution (2.7).
-/

@[expose] public section

namespace Balaban.Fluctuation

open scoped ComplexOrder
open Balaban.SmallField.Def6 Balaban.Background Balaban.Multiscale Balaban.Localization
  Balaban.SmallField Finset Matrix

section CovAlg

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The inverse square root of a positive definite matrix with real entries is symmetric. -/
theorem invSqrt_transpose (A : Matrix ι ι ℂ) (hA : A.PosDef)
    (hK : IsRealMat (invSqrtMat hA)) : (invSqrtMat hA)ᵀ = invSqrtMat hA := by
  set K := invSqrtMat hA with hKdef
  have hKh : Kᴴ = K := (invSqrtMat_posDef hA).isHermitian
  ext p q
  have h1 := congrFun (congrFun hKh p) q
  simp only [Matrix.conjTranspose_apply] at h1
  have h2 : star (K q p) = K q p := hK q p
  rw [h2] at h1
  simpa using h1

/-- For a positive definite `A` whose inverse square root `K` has real entries,
`Kᵀ A K = 1`. -/
theorem invSqrt_transpose_mul (A : Matrix ι ι ℂ) (hA : A.PosDef)
    (hK : IsRealMat (invSqrtMat hA)) : (invSqrtMat hA)ᵀ * A * invSqrtMat hA = 1 := by
  set K := invSqrtMat hA with hKdef
  have hKK : K * K = A⁻¹ := invSqrtMat_mul_self hA
  have hKt : Kᵀ = K := invSqrt_transpose A hA hK
  have hAu : IsUnit A := hA.isUnit
  have hAA : A * A⁻¹ = 1 := Matrix.mul_nonsing_inv A ((Matrix.isUnit_iff_isUnit_det A).1 hAu)
  have hAA' : A⁻¹ * A = 1 := Matrix.nonsing_inv_mul A ((Matrix.isUnit_iff_isUnit_det A).1 hAu)
  have hc : K * A⁻¹ = A⁻¹ * K := by
    rw [← hKK]
    simp only [Matrix.mul_assoc]
  have hAK : A * K = K * A := by
    calc A * K = A * (K * (A⁻¹ * A)) := by rw [hAA', Matrix.mul_one]
      _ = A * (K * A⁻¹) * A := by simp only [Matrix.mul_assoc]
      _ = A * (A⁻¹ * K) * A := by rw [hc]
      _ = (A * A⁻¹) * K * A := by simp only [Matrix.mul_assoc]
      _ = K * A := by rw [hAA, Matrix.one_mul]
  rw [hKt]
  calc K * A * K = (A * K) * K := by rw [hAK]
    _ = A * (K * K) := by rw [Matrix.mul_assoc]
    _ = 1 := by rw [hKK, hAA]

end CovAlg

namespace StepSetting

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}
  (S : StepSetting d L N₁ m₁ k N ϱ) (C : StepClass d L N₁ m₁ k N ϱ)

include S in
theorem dataSites_stepG (x : CTorus d L N₁ m₁ (k + 1)) :
    x ∈ dataSites (stepG d L N₁ m₁ k ϱ) :=
  (mem_dataSites _).2 (Or.inl (S.hG x).1)

theorem dataU_Ψ (ψ : S.E) (x : CTorus d L N₁ m₁ (k + 1)) (i : Fin N) :
    (S.dataU ψ).Ψ x i = ((liftU S.hG' ψ x i : ℝ) : ℂ) :=
  (realData_realizes (G := stepG d L N₁ m₁ k ϱ) (h₀ := S.h₀)
    (isLayerConstant_liftU S.hG S.hG' ψ)).1 x (S.dataSites_stepG x) i

theorem dataU_h (ψ : S.E) (x : CTorus d L N₁ m₁ (k + 1)) (i : Fin N) :
    (S.dataU ψ).h x i = (S.h₀ i : ℂ) :=
  (realData_realizes (G := stepG d L N₁ m₁ k ϱ) (h₀ := S.h₀)
    (isLayerConstant_liftU S.hG S.hG' ψ)).2 x (S.hG x).1 i

theorem isLayerConstant_re_psiKd : IsLayerConstant (stepG d L N₁ m₁ k ϱ)
    (fun x i => ((S.psiKd.Ψ x i).re)) := by
  intro n hn1 hnk x hx x' hx'
  funext i
  have := congrFun (S.psiKd.Ψ_layerConst n hn1 hnk x hx x' hx') i
  simp only [this]

theorem liftU_psi0 (x : CTorus d L N₁ m₁ (k + 1)) (i : Fin N) :
    liftU S.hG' S.psi0 x i = (S.psiKd.Ψ x i).re := by
  have := liftU_unitRestrict (G' := S.G') S.hG S.hG' (fun x i => (S.psiKd.Ψ x i).re)
    S.isLayerConstant_re_psiKd
  exact congrFun (congrFun this x) i

theorem liftU_add (ψ ψ' : S.E) (x : CTorus d L N₁ m₁ (k + 1)) (i : Fin N) :
    liftU S.hG' (ψ + ψ') x i = liftU S.hG' ψ x i + liftU S.hG' ψ' x i := rfl

theorem liftU_smul (c : ℝ) (ψ : S.E) (x : CTorus d L N₁ m₁ (k + 1)) (i : Fin N) :
    liftU S.hG' (c • ψ) x i = c * liftU S.hG' ψ x i := rfl

theorem liftU_psiAt (s : ℝ) (y : S.E) (x : CTorus d L N₁ m₁ (k + 1)) (i : Fin N) :
    liftU S.hG' (S.psiAt s y) x i =
      (S.psiKd.Ψ x i).re + s * (S.betaU ^ (-(1 / 2 : ℝ)) * liftU S.hG' (S.K y) x i) := by
  unfold psiAt shiftU
  rw [liftU_add, liftU_psi0, liftU_smul, liftU_smul]

theorem psiAt_smul (s t : ℝ) (y : S.E) : S.psiAt s (t • y) = S.psiAt (s * t) y := by
  unfold psiAt shiftU
  rw [map_smul, smul_smul, smul_smul]
  have : s * S.betaU ^ (-(1 / 2 : ℝ)) * t = s * t * S.betaU ^ (-(1 / 2 : ℝ)) := by ring
  rw [this, ← smul_smul]

theorem K_apply (y : S.E) (t : S.U) (i : Fin N) :
    S.K y t i = ∑ q : S.U × Fin N, (S.covSqrt (t, i) q).re * y q.1 q.2 := by
  unfold K
  rw [matMap_apply]
  rfl

/-- **The fluctuation field of Lemma 2.5 is the path point at `s = 1`**:
`ψ = ψ^{(k)} + β^{-1/2} C^{(k)1/2} ψ̂`. -/
theorem fluctPsi_eq (ψh : S.E) (x : CTorus d L N₁ m₁ (k + 1)) (i : Fin N) :
    fluctPsi S.hG S.hG' S.a S.a₁ S.ν S.D' S.betaU ψh x i =
      liftU S.hG' (S.psiAt 1 ψh) x i := by
  rw [liftU_psiAt, one_mul]
  simp only [liftU, K_apply]
  unfold fluctPsi fluctShift
  rw [Complex.add_re, Complex.re_ofReal_mul]
  simp only [Matrix.mulVec, dotProduct, Complex.re_sum, Complex.re_mul_ofReal]
  rfl

section Standing

variable {δ' : ℝ} (H' : BgHyp d L (k + 1) ϱ S.a S.ν) (hδ'0 : 0 < δ')
  (hδ' : δ' ≤ thm73C3 d L N / 2) (hD'R : InDomainR S.G' S.ν δ' S.D')
  (hδ0 : 0 < S.δ)
  (hχ : ChiUBounds S.G' S.ν S.δ S.D' (bgField S.G' S.a S.ν S.D') (bgMult S.G' S.a S.ν S.D'))
  (hfam : ∀ x, 0 ≤ x → XData S.G' S.a S.a₁ S.ν x (bgMult S.G' S.a S.ν S.D') 0 (fun _ => 1))
  (hsm : S.δ ^ 2 * smallConstX d L 0 ≤ 1 / 4)

include H' hδ'0 hδ' hD'R in
theorem bgField_unit : IsRealUnitField S.G' (bgField S.G' S.a S.ν S.D') := by
  have hd0 : 0 < d := by have := H'.hd; omega
  obtain ⟨-, -, hδ'c1, -⟩ := theta_consts hd0 hδ'0 hδ'
  have hDU' : InUnionDomainR S.G' (bgC1 d L N) S.ν S.D' := ⟨δ', hδ'0, hδ'c1, hD'R⟩
  exact (theorem71 H' hDU').2.1

include H' hδ'0 hδ' hD'R hδ0 hχ in
theorem constraintField_bg :
    IsConstraintField S.G' S.δ (svec S.G' (bgField S.G' S.a S.ν S.D')) :=
  isConstraintField_of_chiU S.hG' hχ hδ0.le (S.bgField_unit H' hδ'0 hδ' hD'R)

include H' hδ'0 hδ' hD'R in
theorem bgMult_real_S (w : S.G'.Ω 1) :
    starRingEnd ℂ (bgMult S.G' S.a S.ν S.D' w) = bgMult S.G' S.a S.ν S.D' w := by
  have hd0 : 0 < d := by have := H'.hd; omega
  obtain ⟨-, -, hδ'c1, -⟩ := theta_consts hd0 hδ'0 hδ'
  exact bgMult_isReal H' hδ'0 hδ'c1 hD'R w

include H' hδ'0 hδ' hD'R in
theorem svec_bg_real (y : CTorus d L N₁ m₁ (k + 1)) (i : Fin N) :
    starRingEnd ℂ (svec S.G' (bgField S.G' S.a S.ν S.D') y i) =
      svec S.G' (bgField S.G' S.a S.ν S.D') y i := by
  have hunit := S.bgField_unit H' hδ'0 hδ' hD'R
  by_cases hy : y ∈ S.G'.Ω 1
  · rw [svec_of_mem S.G' _ ⟨y, hy⟩ i]
    exact Complex.conj_eq_iff_im.2 ((hunit ⟨y, hy⟩).1 i)
  · rw [svec_of_not_mem S.G' _ hy]; simp

include H' hδ'0 hδ' hD'R hfam in
theorem covA_isReal : IsRealMat S.covA :=
  isRealMat_covOp hfam (S.bgMult_real_S H' hδ'0 hδ' hD'R) (S.svec_bg_real H' hδ'0 hδ' hD'R)
    isRealMat_unitQ isRealMat_unitP

include H' hδ'0 hδ' hD'R hδ0 hχ hfam hsm in
theorem covA_posDef : S.covA.PosDef :=
  (lemma24_a hfam (S.constraintField_bg H' hδ'0 hδ' hD'R hδ0 hχ) hδ0.le hsm
    (S.bgMult_real_S H' hδ'0 hδ' hD'R) (S.svec_bg_real H' hδ'0 hδ' hD'R)).1

include H' hδ'0 hδ' hD'R hδ0 hχ hfam hsm in
theorem covSqrt_isReal : IsRealMat S.covSqrt :=
  decCovSqrt_isRealMat hfam (S.constraintField_bg H' hδ'0 hδ' hD'R hδ0 hχ) hδ0.le hsm
    (S.bgMult_real_S H' hδ'0 hδ' hD'R) (S.svec_bg_real H' hδ'0 hδ' hD'R)

include H' hδ'0 hδ' hD'R hδ0 hχ hfam hsm in
theorem covSqrt_eq : S.covSqrt = invSqrtMat (S.covA_posDef H' hδ'0 hδ' hD'R hδ0 hχ hfam hsm) :=
  lemma24_c_real hfam (S.constraintField_bg H' hδ'0 hδ' hD'R hδ0 hχ) hδ0.le hsm
    (S.bgMult_real_S H' hδ'0 hδ' hD'R) (S.svec_bg_real H' hδ'0 hδ' hD'R)

include H' hδ'0 hδ' hD'R hδ0 hχ hfam hsm in
/-- `C^{1/2} 𝒜 C^{1/2} = 1` (with `C^{1/2}` symmetric). -/
theorem covSqrt_T_mul : S.covSqrtᵀ * S.covA * S.covSqrt = 1 := by
  have hP := S.covA_posDef H' hδ'0 hδ' hD'R hδ0 hχ hfam hsm
  have h := invSqrt_transpose_mul S.covA hP (by
    rw [← S.covSqrt_eq H' hδ'0 hδ' hD'R hδ0 hχ hfam hsm]
    exact S.covSqrt_isReal H' hδ'0 hδ' hD'R hδ0 hχ hfam hsm)
  rwa [← S.covSqrt_eq H' hδ'0 hδ' hD'R hδ0 hχ hfam hsm] at h

end Standing

section Gauss

variable {δ' : ℝ} (H' : BgHyp d L (k + 1) ϱ S.a S.ν) (hδ'0 : 0 < δ')
  (hδ' : δ' ≤ thm73C3 d L N / 2) (hD'R : InDomainR S.G' S.ν δ' S.D')
  (hδ0 : 0 < S.δ)
  (hχ : ChiUBounds S.G' S.ν S.δ S.D' (bgField S.G' S.a S.ν S.D') (bgMult S.G' S.a S.ν S.D'))
  (hfam : ∀ x, 0 ≤ x → XData S.G' S.a S.a₁ S.ν x (bgMult S.G' S.a S.ν S.D') 0 (fun _ => 1))
  (hsm : S.δ ^ 2 * smallConstX d L 0 ≤ 1 / 4)

theorem yhat_smul (c : ℝ) (y : S.E) : yhat (c • y) = (c : ℂ) • yhat y := by
  funext q
  simp [yhat]

theorem yhat_dot (x : S.E) : yhat x ⬝ᵥ yhat x = ((∑ b : S.U, ‖x b‖ ^ 2 : ℝ) : ℂ) := by
  simp only [dotProduct, yhat, Fintype.sum_prod_type]
  push_cast
  refine Finset.sum_congr rfl fun b _ => ?_
  have h : ‖x b‖ ^ 2 = ∑ i, (x b i) * (x b i) := by
    rw [EuclideanSpace.norm_sq_eq]; simp [sq]
  rw [← Complex.ofReal_pow, h]
  push_cast
  rfl

include H' hδ'0 hδ' hD'R hδ0 hχ hfam hsm in
theorem covSqrt_eq_map : S.covSqrt = (S.covSqrt.map Complex.re).map (algebraMap ℝ ℂ) := by
  have hr := S.covSqrt_isReal H' hδ'0 hδ' hD'R hδ0 hχ hfam hsm
  ext p q
  simp only [Matrix.map_apply, Complex.coe_algebraMap]
  exact (Complex.conj_eq_iff_re.1 (hr p q)).symm

include H' hδ'0 hδ' hD'R hδ0 hχ hfam hsm in
theorem yhat_K (x : S.E) : yhat (S.K x) = S.covSqrt *ᵥ yhat x := by
  funext p
  simp only [Matrix.mulVec, dotProduct, yhat, K_apply, Complex.ofReal_sum]
  conv_rhs => rw [S.covSqrt_eq_map H' hδ'0 hδ' hD'R hδ0 hχ hfam hsm]
  refine Finset.sum_congr rfl fun q _ => ?_
  simp

include H' hδ'0 hδ' hD'R hδ0 hχ hfam hsm in
/-- **`β ⟨ψ', 𝒜 ψ'⟩ = |ψ̂|²` for `ψ' = β^{-1/2} C^{1/2} ψ̂`** (the Gaussian part of (2.6)). -/
theorem quad_K (c : ℝ) (x : S.E) :
    yhat (c • S.K x) ⬝ᵥ (S.covA *ᵥ yhat (c • S.K x)) =
      ((c ^ 2 * ∑ b : S.U, ‖x b‖ ^ 2 : ℝ) : ℂ) := by
  rw [yhat_smul, yhat_K S H' hδ'0 hδ' hD'R hδ0 hχ hfam hsm, Matrix.mulVec_smul, smul_dotProduct,
    dotProduct_smul]
  have hT := S.covSqrt_T_mul H' hδ'0 hδ' hD'R hδ0 hχ hfam hsm
  have key : (S.covSqrt *ᵥ yhat x) ⬝ᵥ (S.covA *ᵥ (S.covSqrt *ᵥ yhat x)) = yhat x ⬝ᵥ yhat x := by
    calc (S.covSqrt *ᵥ yhat x) ⬝ᵥ (S.covA *ᵥ (S.covSqrt *ᵥ yhat x))
        = (S.covSqrtᵀ *ᵥ (S.covA *ᵥ (S.covSqrt *ᵥ yhat x))) ⬝ᵥ yhat x := by
          rw [dotProduct_comm, Matrix.dotProduct_mulVec, Matrix.mulVec_transpose]
      _ = ((S.covSqrtᵀ * S.covA * S.covSqrt) *ᵥ yhat x) ⬝ᵥ yhat x := by
          simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]
      _ = yhat x ⬝ᵥ yhat x := by rw [hT, Matrix.one_mulVec]
  rw [key, yhat_dot]
  simp only [smul_eq_mul]
  push_cast
  ring

end Gauss

section Det

variable {δ' : ℝ} (H' : BgHyp d L (k + 1) ϱ S.a S.ν) (hδ'0 : 0 < δ')
  (hδ' : δ' ≤ thm73C3 d L N / 2) (hD'R : InDomainR S.G' S.ν δ' S.D')
  (hδ0 : 0 < S.δ)
  (hχ : ChiUBounds S.G' S.ν S.δ S.D' (bgField S.G' S.a S.ν S.D') (bgMult S.G' S.a S.ν S.D'))
  (hfam : ∀ x, 0 ≤ x → XData S.G' S.a S.a₁ S.ν x (bgMult S.G' S.a S.ν S.D') 0 (fun _ => 1))
  (hsm : S.δ ^ 2 * smallConstX d L 0 ≤ 1 / 4)

include H' hδ'0 hδ' hD'R hfam in
theorem covA_eq_map : S.covA = (S.covA.map Complex.re).map (algebraMap ℝ ℂ) := by
  have hr := S.covA_isReal H' hδ'0 hδ' hD'R hfam
  ext p q
  simp only [Matrix.map_apply, Complex.coe_algebraMap]
  exact (Complex.conj_eq_iff_re.1 (hr p q)).symm

include H' hδ'0 hδ' hD'R hδ0 hχ hfam hsm in
/-- **`C^{1/2} 𝒜 C^{1/2} = 1` in real entries.** -/
theorem covSqrt_re_T_mul :
    (S.covSqrt.map Complex.re)ᵀ * S.covA.map Complex.re * S.covSqrt.map Complex.re = 1 := by
  have hT := S.covSqrt_T_mul H' hδ'0 hδ' hD'R hδ0 hχ hfam hsm
  have hK := S.covSqrt_eq_map H' hδ'0 hδ' hD'R hδ0 hχ hfam hsm
  have hA := S.covA_eq_map H' hδ'0 hδ' hD'R hfam
  set Kr := S.covSqrt.map Complex.re with hKr
  set Ar := S.covA.map Complex.re with hAr
  rw [hK, hA, ← Matrix.transpose_map, ← Matrix.map_mul, ← Matrix.map_mul] at hT
  have h1 : (1 : Matrix (S.U × Fin N) (S.U × Fin N) ℂ) =
      (1 : Matrix (S.U × Fin N) (S.U × Fin N) ℝ).map (algebraMap ℝ ℂ) := by
    simp
  rw [h1] at hT
  exact Matrix.map_injective (algebraMap ℝ ℂ).injective hT

include H' hδ'0 hδ' hD'R hδ0 hχ hfam hsm in
theorem det_covSqrt_re_ne : (S.covSqrt.map Complex.re).det ≠ 0 := by
  have h := congrArg Matrix.det (S.covSqrt_re_T_mul H' hδ'0 hδ' hD'R hδ0 hχ hfam hsm)
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at h
  intro h0
  rw [h0] at h
  simp at h

include H' hδ'0 hδ' hD'R hδ0 hχ hfam hsm in
theorem det_K_ne : LinearMap.det S.K ≠ 0 := by
  unfold K
  rw [det_matMap]
  exact S.det_covSqrt_re_ne H' hδ'0 hδ' hD'R hδ0 hχ hfam hsm

include H' hδ'0 hδ' hD'R hδ0 hχ hfam hsm in
theorem Kinv_K (x : S.E) : S.Kinv (S.K x) = x := by
  unfold Kinv K
  rw [matMap_mul, Matrix.nonsing_inv_mul _
    (isUnit_iff_ne_zero.2 (S.det_covSqrt_re_ne H' hδ'0 hδ' hD'R hδ0 hχ hfam hsm)), matMap_one]

include H' hδ'0 hδ' hD'R hδ0 hχ hfam hsm in
/-- **`|det C^{(k)1/2}| = exp (½ log det C^{(k)})`** (Lemma 2.4 (c)). -/
theorem abs_det_K : |LinearMap.det S.K| = Real.exp S.halfLogDetC := by
  have h1 := congrArg Matrix.det (S.covSqrt_re_T_mul H' hδ'0 hδ' hD'R hδ0 hχ hfam hsm)
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at h1
  have hKne := S.det_covSqrt_re_ne H' hδ'0 hδ' hD'R hδ0 hχ hfam hsm
  have hA := S.covA_eq_map H' hδ'0 hδ' hD'R hfam
  set Kr := S.covSqrt.map Complex.re with hKr
  set Ar := S.covA.map Complex.re with hAr
  have hAne : Ar.det ≠ 0 := by
    intro h0; rw [h0] at h1; simp at h1
  have hdA : S.covA.det = ((Ar.det : ℝ) : ℂ) := by
    rw [hA]
    exact (RingHom.map_det (algebraMap ℝ ℂ) Ar).symm
  have hinv : (S.covA)⁻¹.det.re = (Kr.det) ^ 2 := by
    rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv', hdA, ← Complex.ofReal_inv, Complex.ofReal_re]
    field_simp
    nlinarith [h1]
  have hpos : 0 < (Kr.det) ^ 2 := by positivity
  unfold halfLogDetC
  rw [hinv, Real.log_pow, show LinearMap.det S.K = Kr.det from det_matMap _]
  have e : (1 / 2 : ℝ) * (((2 : ℕ) : ℝ) * Real.log Kr.det) = Real.log |Kr.det| := by
    rw [Real.log_abs]; push_cast; ring
  rw [e, Real.exp_log (abs_pos.2 hKne)]

end Det

section Main

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

theorem betaU_pos' (hL : 0 < L) (hβ : 0 < S.β) : 0 < S.betaU := by
  unfold betaU
  have hL' : (0 : ℝ) < L := by exact_mod_cast hL
  have : (0 : ℝ) < (L : ℝ) ^ k := by positivity
  positivity

include S ha₁ H hδ'0 hδ' hD'R hδ0 hfam hsm hχu hnorm hβ hp₁ hB5 hK2 hp40 hrad in
/-- **Lemma 2.5 on the path point `s = 1`**: `χ_k(ψ) χ_{(2.2)}(θ, ψ) χ_fl(ψ̂) = χ_fl(ψ̂)` for
`ψ = ψ^{(k)} + β^{-1/2} C^{(k)1/2} ψ̂`. -/
theorem chi_absorb (x : S.E) :
    chiXi (stepG d L N₁ m₁ k ϱ) S.a S.ν S.δ (liftU S.hG' (S.psiAt 1 x)) S.h₀ *
        chi22 S.G' S.δ S.D' (liftU S.hG' (S.psiAt 1 x)) * chiFl S.U N S.p₁ x =
      chiFl S.U N S.p₁ x := by
  have hL : 0 < L := Nat.pos_of_ne_zero (NeZero.ne L)
  have hβU := betaU_pos' S hL hβ
  have := lemma25_field (G := stepG d L N₁ m₁ k ϱ) (G' := S.G') ha₁ S.hG S.hG' H H hδ'0 hδ' hD'R
    S.hh₀ hδ0 hfam hsm hχu hnorm hβU hp₁ hB5 hK2 hp40 hrad x
  have e : fluctPsi S.hG S.hG' (compWeight L S.a₁) S.a₁ S.ν S.D' S.betaU x =
      liftU S.hG' (S.psiAt 1 x) := funext fun y => funext fun i => S.fluctPsi_eq x y i
  rw [e] at this
  exact this

end Main

theorem bgData_ext' {G : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ} {D E : BgData G N}
    (hΨ : D.Ψ = E.Ψ) (hh : D.h = E.h) : D = E := by
  cases D; cases E
  simp only at hΨ hh
  subst hΨ; subst hh; rfl

section Main2

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

include S ha₁ H hδ'0 hδ' hD'R hδ0 hfam hsm hχu hnorm hβ hp₁ hB5 hK2 hp40 hrad in
/-- On the support of `χ_fl`, `χ_k(ψ) = 1`. -/
theorem chiXi_eq_one (x : S.E) (hx : chiFl S.U N S.p₁ x = 1) :
    chiXi (stepG d L N₁ m₁ k ϱ) S.a S.ν S.δ (liftU S.hG' (S.psiAt 1 x)) S.h₀ = 1 := by
  have h := S.chi_absorb ha₁ H hδ'0 hδ' hD'R hδ0 hfam hsm hχu hnorm hβ hp₁ hB5 hK2 hp40 hrad x
  rw [hx, mul_one] at h
  have h1 : chiXi (stepG d L N₁ m₁ k ϱ) S.a S.ν S.δ (liftU S.hG' (S.psiAt 1 x)) S.h₀ = 0 ∨
      chiXi (stepG d L N₁ m₁ k ϱ) S.a S.ν S.δ (liftU S.hG' (S.psiAt 1 x)) S.h₀ = 1 := by
    unfold chiXi; split_ifs <;> simp
  have h2 : chi22 S.G' S.δ S.D' (liftU S.hG' (S.psiAt 1 x)) = 0 ∨
      chi22 S.G' S.δ S.D' (liftU S.hG' (S.psiAt 1 x)) = 1 := by
    unfold chi22; split_ifs <;> simp
  rcases h1 with h1 | h1
  · rw [h1] at h; simp at h
  · exact h1

include S ha₁ H hδ'0 hδ' hD'R hδ0 hfam hsm hχu hnorm hβ hp₁ hB5 hK2 hp40 hrad in
/-- On the support of `χ_fl`, the datum of `ψ = ψ^{(k)} + ψ'` lies in the real domain. -/
theorem dataU_inDomainR (x : S.E) (hx : chiFl S.U N S.p₁ x = 1) :
    InUnionDomainR (stepG d L N₁ m₁ k ϱ) (bgC1 d L N) S.ν (S.dataU (S.psiAt 1 x)) := by
  have h := S.chiXi_eq_one ha₁ H hδ'0 hδ' hD'R hδ0 hfam hsm hχu hnorm hβ hp₁ hB5 hK2 hp40 hrad x hx
  unfold chiXi at h
  by_cases hX : Xi (stepG d L N₁ m₁ k ϱ) S.a S.ν k 1 S.δ (liftU S.hG' (S.psiAt 1 x)) S.h₀
  · obtain ⟨-, -, D, hreal, hdom, -⟩ := hX
    have hD : D = S.dataU (S.psiAt 1 x) := by
      refine bgData_ext' ?_ ?_
      · funext y i
        rw [hreal.1 y (S.dataSites_stepG y) i, S.dataU_Ψ]
      · funext y i
        rw [hreal.2 y (S.hG y).1 i, S.dataU_h]
    rwa [hD] at hdom
  · simp [hX] at h

end Main2

theorem inUnionDomainC_of_R' {a : ℕ → ℝ} {G : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
    {D : BgData G N} (H : BgHyp d L (k + 1) ϱ a S.ν)
    (hD : InUnionDomainR G (bgC1 d L N) S.ν D) :
    InUnionDomainC G (bgC0 d L N) (bgC1 d L N) S.ν D := by
  have hd0 : 0 < d := by have := H.hd; omega
  obtain ⟨δ, hδ0, hδc, Ψ, h, hP, hΨ, hh⟩ := hD
  refine ⟨δ, δ, hδ0, le_rfl, hδc.trans (bgC1_le_bgC0 d L N hd0), hδc, ?_, ?_⟩
  · have := H.massLe
    nlinarith [sq_nonneg δ]
  · refine ⟨Ψ, h, 0, 0, ⟨hP, hδ0, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
    · intro n hn1 hnk x hx x' hx'; rfl
    · intro n hn1 hnk x hx x' hx'; rfl
    · intro x x' hx; simp [vn, hδ0]
    · intro x hx; simp [vn, hδ0]
    · intro x hx; simp [hδ0]
    · intro x hx
      simp only [vn, Pi.zero_apply]
      have : 0 < δ ^ 2 / δ := by positivity
      simpa using this
    · intro x hx; simp [hδ0]
    · intro x hx i
      simp [hΨ x hx i]
    · intro x hx i
      simp [hh x hx i]

section Main3

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

include S H hδ'0 hδ' hD'R in
/-- The datum `θ` is in the domain of the expansion. -/
theorem D'_domains :
    InUnionDomainR S.G' (thm73C1 d L N) S.ν S.D' ∧
      InUnionDomainC S.G' (bgC0 d L N) (thm73C2 d L N) S.ν S.D' := by
  have hd0 : 0 < d := by have := H.hd; omega
  obtain ⟨hδ'1, hδ'3, hδ'c1, -⟩ := theta_consts hd0 hδ'0 hδ'
  refine ⟨⟨δ', hδ'0, hδ'1, hD'R⟩, ?_⟩
  have hDC' : InUnionDomainC S.G' (bgC0 d L N) (thm73C3 d L N) S.ν S.D' := by
    obtain ⟨Ψ', h', hP', hΨ', hh'⟩ := hD'R
    refine ⟨δ', δ', hδ'0, le_rfl, hδ'c1.trans (bgC1_le_bgC0 d L N hd0), hδ'3, ?_, ?_⟩
    · have := mul_le_mul_of_nonneg_right H.massLe (sq_nonneg δ')
      nlinarith [sq_nonneg δ']
    · exact ⟨Ψ', h', fun _ _ => 0, fun _ _ => 0,
        (DataWit.ofReal (ν := S.ν) hδ'0 hδ'0 hP' S.D' hΨ' hh').P, by simpa using hΨ', by simpa using hh'⟩
  exact InUnionDomainC.mono (thm73C3_le_thm73C2 d L N) hDC'

include S ha₁ H hδ'0 hδ' hD'R hδ0 hfam hsm hχu hnorm hβ hp₁ hB5 hK2 hp40 hrad in
/-- **The exact expansion (Lemma 2.3 (b)) on the path point `s = 1`**:
`J_k(θ, ψ) = A^η_{k+1}(θ, φ_{k+1}) + ‖ψ̂‖²/(2β) + V^{(k)}(ψ')` in the units of the Background
action (`β ⟨ψ', 𝒜 ψ'⟩ L^{k(d-2)} = ‖ψ̂‖²`). -/
theorem Jbg_expansion (x : S.E) (hx : chiFl S.U N S.p₁ x = 1) :
    ((Jbg (stepG d L N₁ m₁ k ϱ) S.G' S.a S.a₁ S.ν k S.D'.Ψ (S.dataU (S.psiAt 1 x)) : ℝ) : ℂ) =
      (S.Anew : ℂ) + ((1 / (2 * S.β) * ∑ b : S.U, ‖x b‖ ^ 2 : ℝ) : ℂ) + S.Vk (S.psiAt 1 x) := by
  have hL : 0 < L := Nat.pos_of_ne_zero (NeZero.ne L)
  have hd0 : 0 < d := by have := H.hd; omega
  have hβU := betaU_pos' S hL hβ
  obtain ⟨hDU', hDC'⟩ := S.D'_domains H hδ'0 hδ' hD'R
  obtain ⟨-, -, hδ'c1, -⟩ := theta_consts hd0 hδ'0 hδ'
  have hDU1 : InUnionDomainR S.G' (bgC1 d L N) S.ν S.D' := ⟨δ', hδ'0, hδ'c1, hD'R⟩
  have hDR := S.dataU_inDomainR ha₁ H hδ'0 hδ' hD'R hδ0 hfam hsm hχu hnorm hβ hp₁ hB5 hK2 hp40 hrad
    x hx
  have hDC := S.inUnionDomainC_of_R' H hDR
  have hh : ∀ z i, (S.dataU (S.psiAt 1 x)).h z i = S.D'.h z i := fun z i => by
    rw [S.dataU_h, S.hh₀]
  have hexp := expansion_quadratic ha₁ S.hG S.hG' (le_refl (k + 1)) H H S.D' hDC'
    (S.dataU (S.psiAt 1 x)) hh hDC
  have hD'real : S.D'.IsReal := isReal_of_inDomainR hD'R
  have hJ := Jbg_eq_bilinear (G' := S.G') (n := k) H (S.dataU (S.psiAt 1 x)) hDR S.D'.Ψ
    (fun z i => (hD'real z i).1)
  obtain ⟨hf, hm⟩ := theorem72_real H hDU1
  have hχ := (chiU_eq_one_iff _ _ _ _).1 hχu
  have hunit := S.bgField_unit H hδ'0 hδ' hD'R
  have hA' : actionC S.G' S.a S.ν S.D' (bgFieldC S.G' S.a S.ν (bgC0 d L N) S.D') = (S.Anew : ℂ) := by
    rw [hf]
    exact (action_cast S.D' hD'real (fun z i => (hunit z).1 i)).symm
  -- the tangent
  have hpsiReal := (criticalPoint_real ha₁ S.hG S.hG' (le_refl (k + 1)) H H S.D' hDU').1
  have htan : compTangent S.hG S.hG' (le_refl (k + 1)) S.a
      (bgFieldC S.G' S.a S.ν (bgC0 d L N) S.D') S.D' (S.dataU (S.psiAt 1 x)) =
      fun z i => ((liftU S.hG' (S.shiftU x) z i : ℝ) : ℂ) := by
    funext z i
    unfold compTangent
    rw [hf]
    have hpr : S.psiKd.Ψ z i = (((S.psiKd.Ψ z i).re : ℝ) : ℂ) :=
      Complex.ext (by simp) (by simpa using (show (S.psiKd.Ψ z i).im = 0 from (hpsiReal z i).1))
    show (S.dataU (S.psiAt 1 x)).Ψ z i - S.psiKd.Ψ z i = _
    rw [S.dataU_Ψ, hpr, liftU_psiAt]
    unfold shiftU
    rw [liftU_smul]
    push_cast
    ring
  have hq := quad_identity S.hG S.hG' S.a S.a₁ S.ν (bgMultC S.G' S.a S.ν (bgC0 d L N) S.D')
    (bgFieldC S.G' S.a S.ν (bgC0 d L N) S.D') (S.shiftU x)
  have hcov : covOp S.G' S.a S.a₁ S.ν (bgMultC S.G' S.a S.ν (bgC0 d L N) S.D')
      (svec S.G' (bgFieldC S.G' S.a S.ν (bgC0 d L N) S.D')) (unitQ S.G') (unitP S.G') = S.covA := by
    rw [hf, hm]; rfl
  rw [hcov] at hq
  have hK := S.quad_K H hδ'0 hδ' hD'R hδ0 hχ hfam hsm (S.betaU ^ (-(1 / 2 : ℝ))) x
  have hsh : yhat (S.shiftU x) = yhat ((S.betaU ^ (-(1 / 2 : ℝ))) • S.K x) := rfl
  rw [hsh, hK, ← htan] at hq
  have hc2 : (S.betaU ^ (-(1 / 2 : ℝ))) ^ 2 = S.betaU⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hβU.le]
    norm_num
    exact Real.rpow_neg_one S.betaU
  have hL' : (0 : ℝ) < L := by exact_mod_cast hL
  have hLk : (0 : ℝ) < (L : ℝ) ^ k := by positivity
  have hbeta : S.betaU = S.β * (((L : ℝ) ^ k) ^ d / ((L : ℝ) ^ k) ^ 2) := by
    unfold betaU; ring
  have key : (((1 / 2) * (((L : ℝ) ^ k) ^ d / ((L : ℝ) ^ k) ^ 2) : ℝ)) *
      ((S.betaU ^ (-(1 / 2 : ℝ))) ^ 2 * ∑ b : S.U, ‖x b‖ ^ 2) =
      1 / (2 * S.β) * ∑ b : S.U, ‖x b‖ ^ 2 := by
    rw [hc2, hbeta]
    have : 0 < ((L : ℝ) ^ k) ^ d := by positivity
    field_simp
  have hqq : couplingC S.G' S.a₁ (k + 1) (fun _ _ => 0)
        (compTangent S.hG S.hG' (le_refl (k + 1)) S.a (bgFieldC S.G' S.a S.ν (bgC0 d L N) S.D')
          S.D' (S.dataU (S.psiAt 1 x))) +
      (1 / 2 : ℂ) * deltaForm (S.hG.precedes S.hG' (le_refl (k + 1))) S.a S.ν
        (bgMultC S.G' S.a S.ν (bgC0 d L N) S.D') (bgFieldC S.G' S.a S.ν (bgC0 d L N) S.D')
        (compTangent S.hG S.hG' (le_refl (k + 1)) S.a (bgFieldC S.G' S.a S.ν (bgC0 d L N) S.D')
          S.D' (S.dataU (S.psiAt 1 x))) =
      ((1 / (2 * S.β) * ∑ b : S.U, ‖x b‖ ^ 2 : ℝ) : ℂ) := by
    rw [hq, ← key]
    push_cast
    ring
  rw [hJ.trans hexp, hA']
  unfold Vk
  linear_combination hqq

end Main3

end StepSetting

end Balaban.Fluctuation
