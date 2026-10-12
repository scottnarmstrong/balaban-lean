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

/-- The exponent bookkeeping of the integrand (2.6): pure algebra. -/
theorem step_exponent_algebra (K0 cp Ao An β sg Ek nU : ℝ) (Eψ E0 Fψ F0 V : ℂ) (hβ : β ≠ 0)
    (hJ : (cp : ℂ) + (Ao : ℂ) = (An : ℂ) + ((1 / (2 * β) * sg : ℝ) : ℂ) + V) :
    ((K0 * Real.exp (-(β * cp)) : ℝ) : ℂ) * ((1 : ℝ) : ℂ) *
        (((1 : ℝ) : ℂ) * Complex.exp (-(β : ℂ) * (Ao : ℂ) + Eψ - (Ek : ℂ) * (nU : ℂ) + Fψ)) =
      (K0 : ℂ) * Complex.exp (-(β : ℂ) * (An : ℂ) + E0 - (Ek : ℂ) * (nU : ℂ) + F0) *
          ((1 * Real.exp ((-sg) / 2) : ℝ) : ℂ) *
        Complex.exp (-(β : ℂ) * V + (Eψ - E0) + (Fψ - F0)) := by
  have hβc : (β : ℂ) ≠ 0 := by exact_mod_cast hβ
  have hJ2 : (β : ℂ) * ((cp : ℂ) + (Ao : ℂ)) = (β : ℂ) * An + (sg : ℂ) / 2 + (β : ℂ) * V := by
    rw [hJ]; push_cast; field_simp
  simp only [Complex.ofReal_mul, Complex.ofReal_exp, Complex.ofReal_one, one_mul, mul_one]
  have hexp : Complex.exp (((-(β * cp) : ℝ) : ℂ)) * Complex.exp (-(β : ℂ) * (Ao : ℂ) + Eψ - (Ek : ℂ) * (nU : ℂ) + Fψ) =
      Complex.exp (-(β : ℂ) * (An : ℂ) + E0 - (Ek : ℂ) * (nU : ℂ) + F0) *
        Complex.exp ((((-sg) / 2 : ℝ) : ℂ)) *
        Complex.exp (-(β : ℂ) * V + (Eψ - E0) + (Fψ - F0)) := by
    rw [← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]
    congr 1
    push_cast
    linear_combination (-1 : ℂ) * hJ2
  calc (K0 : ℂ) * Complex.exp (((-(β * cp) : ℝ) : ℂ)) *
        Complex.exp (-(β : ℂ) * (Ao : ℂ) + Eψ - (Ek : ℂ) * (nU : ℂ) + Fψ)
      = (K0 : ℂ) * (Complex.exp (((-(β * cp) : ℝ) : ℂ)) *
        Complex.exp (-(β : ℂ) * (Ao : ℂ) + Eψ - (Ek : ℂ) * (nU : ℂ) + Fψ)) := by ring
    _ = _ := by rw [hexp]; ring

section AeCongr

open MeasureTheory

variable {X : Type*} [MeasurableSpace X] {ν : Measure X}

theorem partFun₂_congr_ae {W₁ W₁' W₂ W₂' : ℝ → X → ℂ} {s t : ℝ}
    (h1 : ∀ᵐ x ∂ν, W₁ s x = W₁' s x) (h2 : ∀ᵐ x ∂ν, W₂ t x = W₂' t x) :
    partFun₂ ν W₁ W₂ s t = partFun₂ ν W₁' W₂' s t := by
  unfold partFun₂
  refine integral_congr_ae ?_
  filter_upwards [h1, h2] with x hx1 hx2
  rw [hx1, hx2]

theorem avgFun₂_congr_ae {W₁ W₁' W₂ W₂' : ℝ → X → ℂ} {f f' : X → ℂ} {s t : ℝ}
    (h1 : ∀ᵐ x ∂ν, W₁ s x = W₁' s x) (h2 : ∀ᵐ x ∂ν, W₂ t x = W₂' t x)
    (hf : ∀ᵐ x ∂ν, f x = f' x) :
    avgFun₂ ν W₁ W₂ f s t = avgFun₂ ν W₁' W₂' f' s t := by
  unfold avgFun₂
  rw [partFun₂_congr_ae h1 h2]
  congr 1
  refine integral_congr_ae ?_
  filter_upwards [h1, h2, hf] with x hx1 hx2 hx3
  rw [hx1, hx2, hx3]

theorem avgFun_eq_avgFun₂ {W₁ W₂ : ℝ → X → ℂ} (h0 : ∀ x, W₂ 0 x = 0) (f : X → ℂ) (s : ℝ) :
    avgFun ν W₁ f s = avgFun₂ ν W₁ W₂ f s 0 := by
  unfold avgFun avgFun₂ partFun partFun₂
  simp [h0]

end AeCongr

section RealPos

open MeasureTheory

variable {X : Type*} [MeasurableSpace X] {ν : Measure X} [IsProbabilityMeasure ν]

/-- A partition function with real, bounded, measurable exponents is a positive real. -/
theorem partFun₂_real_pos {W₁ W₂ : ℝ → X → ℂ} {s t : ℝ} (hm1 : Measurable (W₁ s))
    (hm2 : Measurable (W₂ t)) (hr1 : ∀ x, (W₁ s x).im = 0) (hr2 : ∀ x, (W₂ t x).im = 0)
    {M₁ M₂ : ℝ} (hb1 : ∀ x, ‖W₁ s x‖ ≤ M₁) (hb2 : ∀ x, ‖W₂ t x‖ ≤ M₂) :
    (partFun₂ ν W₁ W₂ s t).im = 0 ∧ 0 < (partFun₂ ν W₁ W₂ s t).re := by
  set r1 : X → ℝ := fun x => (W₁ s x).re with hr1d
  set r2 : X → ℝ := fun x => (W₂ t x).re with hr2d
  have e1 : ∀ x, W₁ s x = (r1 x : ℂ) := fun x => Complex.ext (by simp [hr1d]) (by simp [hr1 x])
  have e2 : ∀ x, W₂ t x = (r2 x : ℂ) := fun x => Complex.ext (by simp [hr2d]) (by simp [hr2 x])
  have hZ : partFun₂ ν W₁ W₂ s t = ((∫ x, Real.exp (r1 x + r2 x) ∂ν : ℝ) : ℂ) := by
    unfold partFun₂
    rw [← integral_complex_ofReal]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    show Complex.exp (W₁ s x + W₂ t x) = ((Real.exp (r1 x + r2 x) : ℝ) : ℂ)
    rw [e1 x, e2 x, ← Complex.ofReal_add, Complex.ofReal_exp]
  refine ⟨by rw [hZ]; exact Complex.ofReal_im _, ?_⟩
  rw [hZ, Complex.ofReal_re]
  have hm1' : Measurable r1 := Complex.measurable_re.comp hm1
  have hm2' : Measurable r2 := Complex.measurable_re.comp hm2
  refine integral_exp_pos (Integrable.of_bound (C := Real.exp (M₁ + M₂)) ?_ ?_)
  · exact (Real.measurable_exp.comp (hm1'.add hm2')).aestronglyMeasurable
  · refine ae_of_all _ fun x => ?_
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    refine Real.exp_le_exp.2 ?_
    have h1 : r1 x ≤ M₁ := (Complex.re_le_norm _).trans (hb1 x)
    have h2 : r2 x ≤ M₂ := (Complex.re_le_norm _).trans (hb2 x)
    linarith

end RealPos

section ZeroTangent

variable {d L N₀ K N : ℕ} [NeZero N₀] [NeZero L] {ϱ ϱ' : ℝ}
  {G : GeneratingSet d L N₀ K ϱ} {G' : GeneratingSet d L N₀ K ϱ'}

theorem qStar_zero' (a : ℕ → ℝ) :
    qStar G a (0 : Torus d (N₀ * L ^ K) → Fin N → ℂ) = 0 := by
  funext p; simp [qStar]

theorem phiOne_zero' (h : Precedes G G') (a : ℕ → ℝ) (ν : ℝ) (α₁ : G'.Ω 1 → ℂ)
    (φ₁ : G'.Ω 1 × Fin N → ℂ) : phiOne h a ν α₁ φ₁ 0 = 0 := by
  simp [phiOne]

theorem alphaOne_zero' (h : Precedes G G') (a : ℕ → ℝ) (ν : ℝ) (α₁ : G'.Ω 1 → ℂ)
    (φ₁ : G'.Ω 1 × Fin N → ℂ) : alphaOne h a ν α₁ φ₁ 0 = 0 := by
  simp [alphaOne]

/-- The interaction vanishes at the critical point. -/
theorem interactionV_zero' (h : Precedes G G') (a : ℕ → ℝ) (ν : ℝ) (α₁ : G'.Ω 1 → ℂ)
    (φ₁ : G'.Ω 1 × Fin N → ℂ) :
    interactionV h a ν α₁ φ₁ (0 : Torus d (N₀ * L ^ K) → Fin N → ℂ) 0 = 0 := by
  simp [interactionV, qStar_zero', phiOne_zero', alphaOne_zero', pair]

end ZeroTangent

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

section Main4

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

include S ha₁ H hδ'0 hδ' hD'R in
theorem dataU_psi0 : S.dataU S.psi0 = S.psiKd := by
  obtain ⟨hDU', -⟩ := S.D'_domains H hδ'0 hδ' hD'R
  have hpsiReal := (criticalPoint_real ha₁ S.hG S.hG' (le_refl (k + 1)) H H S.D' hDU').1
  refine bgData_ext' ?_ ?_
  · funext z i
    have hpr : S.psiKd.Ψ z i = (((S.psiKd.Ψ z i).re : ℝ) : ℂ) :=
      Complex.ext (by simp) (by simpa using (show (S.psiKd.Ψ z i).im = 0 from (hpsiReal z i).1))
    rw [S.dataU_Ψ, S.liftU_psi0, ← hpr]
  · funext z i
    rw [S.dataU_h]
    show (S.h₀ i : ℂ) = (if z ∈ (stepG d L N₁ m₁ k ϱ).Ω 1 then S.D'.h z i else 0 : ℂ)
    simp [(S.hG z).1, S.hh₀]

include S ha₁ H hδ'0 hδ' hD'R in
theorem Vk_psi0 : S.Vk S.psi0 = 0 := by
  have hd0 : 0 < d := by have := H.hd; omega
  obtain ⟨hDU', -⟩ := S.D'_domains H hδ'0 hδ' hD'R
  obtain ⟨hr, hdom, -, -, -, -, hfield, -⟩ :=
    criticalPoint_real ha₁ S.hG S.hG' (le_refl (k + 1)) H H S.D' hDU'
  obtain ⟨-, -, hδ'c1, -⟩ := theta_consts hd0 hδ'0 hδ'
  have hDU1 : InUnionDomainR S.G' (bgC1 d L N) S.ν S.D' := ⟨δ', hδ'0, hδ'c1, hD'R⟩
  obtain ⟨hf, hm⟩ := theorem72_real H hDU1
  have hdp := S.dataU_psi0 ha₁ H hδ'0 hδ' hD'R
  have hdom' : InUnionDomainR (stepG d L N₁ m₁ k ϱ) (bgC1 d L N) S.ν S.psiKd := hdom
  have hfield' : bgField (stepG d L N₁ m₁ k ϱ) S.a S.ν S.psiKd =
      (S.hG.precedes S.hG' (le_refl (k + 1))).restrictφ (bgField S.G' S.a S.ν S.D') := hfield
  unfold Vk
  rw [hdp]
  have h1 : compTangent S.hG S.hG' (le_refl (k + 1)) S.a
      (bgFieldC S.G' S.a S.ν (bgC0 d L N) S.D') S.D' S.psiKd = 0 := by
    funext z i
    unfold compTangent
    rw [hf]
    exact sub_self _
  have h2 : bgFieldC (stepG d L N₁ m₁ k ϱ) S.a S.ν (bgC0 d L N) S.psiKd -
      (S.hG.precedes S.hG' (le_refl (k + 1))).restrictφ (bgFieldC S.G' S.a S.ν (bgC0 d L N) S.D')
      = 0 := by
    rw [(theorem72_real H hdom').1, hf, hfield']
    exact sub_self _
  rw [h1, h2]
  exact interactionV_zero' _ _ _ _ _

end Main4

/-- The truncation of `W₁` to the support of `χ_fl` (where `ν_{p₁}` lives). -/
noncomputable def WoneT (s : ℝ) (x : S.E) : ℂ :=
  open Classical in if chiFl S.U N S.p₁ x = 1 then S.Wone C s x else 0

/-- The truncation of `W₂` to the support of `χ_fl`. -/
noncomputable def WtwoT (g : Fld d L N₁ m₁ (k + 1) N) (t : ℝ) (x : S.E) : ℂ :=
  open Classical in if chiFl S.U N S.p₁ x = 1 then S.Wtwo C g t x else 0

/-- The constant prefactor of (2.6)-(2.7): the normalisation of `t_k` and the background values of
the exponent. -/
noncomputable def Pconst (g : Fld d L N₁ m₁ (k + 1) N) : ℂ :=
  (((S.cKernel / (2 * Real.pi)) ^ ((N : ℝ) * S.nBlocks / 2) : ℝ) : ℂ) *
    Complex.exp (-(S.β : ℂ) * (S.Anew : ℂ) +
      EcompAt C.m₀ C.Tm S.a S.ν (Nat.le_succ k) S.psiKd - (C.Ek : ℂ) * (S.nU : ℂ) +
      FcompAt C.m₀ C.Tm S.a S.ν (Nat.le_succ k) S.psiKd g)

theorem psiAt_one_sub (x : S.E) : S.psiAt 1 x - S.psi0 = S.shiftU x := by
  unfold psiAt; rw [one_smul]; abel

section Main5

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

include S H hδ'0 hδ' hD'R hδ0 hfam hsm hχu hβ in
/-- `χ^{(k)}` at the path point `s = 1` is `χ_{(2.2)} χ_fl(ψ̂)`. -/
theorem chiK_psiAt (x : S.E) :
    S.chiK (S.psiAt 1 x) = chi22 S.G' S.δ S.D' (liftU S.hG' (S.psiAt 1 x)) * chiFl S.U N S.p₁ x := by
  have hL : 0 < L := Nat.pos_of_ne_zero (NeZero.ne L)
  have hβU := betaU_pos' S hL hβ
  have hχ := (chiU_eq_one_iff _ _ _ _).1 hχu
  unfold chiK
  rw [S.psiAt_one_sub]
  unfold shiftU
  rw [map_smul, S.Kinv_K H hδ'0 hδ' hD'R hδ0 hχ hfam hsm, smul_smul, ← Real.rpow_add hβU]
  norm_num

include S ha₁ H hδ'0 hδ' hD'R hδ0 hfam hsm hχu hnorm hβ hp₁ hB5 hK2 hp40 hrad in
/-- **The integrand of the fluctuation integral after the substitution (2.7)**:
`t_k χ^{(k)} ρ_k (ψ^{(k)} + ψ') = P χ_fl(ψ̂) e^{-‖ψ̂‖²/2} e^{W₁(1, ψ̂) + W₂(1, ψ̂)}`. -/
theorem integrand_eq (g : Fld d L N₁ m₁ (k + 1) N) (x : S.E) :
    (S.tKernel (S.psiAt 1 x) : ℂ) * (S.chiK (S.psiAt 1 x) : ℂ) * S.rhoStep C g (S.psiAt 1 x) =
      S.Pconst C g * ((chiFl S.U N S.p₁ x * gaussWeight S.U N x : ℝ) : ℂ) *
        Complex.exp (S.WoneT C 1 x + S.WtwoT C g 1 x) := by
  classical
  have hL : 0 < L := Nat.pos_of_ne_zero (NeZero.ne L)
  by_cases hx : chiFl S.U N S.p₁ x = 1
  · have hxi := S.chiXi_eq_one ha₁ H hδ'0 hδ' hD'R hδ0 hfam hsm hχu hnorm hβ hp₁ hB5 hK2 hp40 hrad
      x hx
    have hc22 : chi22 S.G' S.δ S.D' (liftU S.hG' (S.psiAt 1 x)) = 1 := by
      have h := S.chi_absorb ha₁ H hδ'0 hδ' hD'R hδ0 hfam hsm hχu hnorm hβ hp₁ hB5 hK2 hp40 hrad x
      rw [hx, mul_one, hxi, one_mul] at h
      exact h
    have hK := S.chiK_psiAt H hδ'0 hδ' hD'R hδ0 hfam hsm hχu hβ x
    rw [hc22, hx, mul_one] at hK
    have hJ := S.Jbg_expansion ha₁ H hδ'0 hδ' hD'R hδ0 hfam hsm hχu hnorm hβ hp₁ hB5 hK2 hp40 hrad
      x hx
    have hdp := S.dataU_psi0 ha₁ H hδ'0 hδ' hD'R
    simp only [Jbg] at hJ
    rw [Complex.ofReal_add] at hJ
    simp only [rhoStep, tKernel, Pconst, WoneT, WtwoT, hK, hxi, hx, ↓reduceIte, Wone, Wtwo, dE, dF,
      Aold, hdp, gaussWeight]
    exact step_exponent_algebra _ _ _ _ S.β _ C.Ek S.nU _ _ _ _ _ hβ.ne' hJ
  · have h0 : chiFl S.U N S.p₁ x = 0 := by
      rcases chiFl_eq_zero_or_one S.p₁ x with h | h
      · exact h
      · exact absurd h hx
    have hK := S.chiK_psiAt H hδ'0 hδ' hD'R hδ0 hfam hsm hχu hβ x
    rw [h0, mul_zero] at hK
    rw [hK, h0]
    simp

end Main5

section Constants

include S C in
/-- **The vacuum constants** (P4 (2.58)-(2.63), Definition 2.1): the product of the normalisation of
the kernel `t_k`, the Jacobian of (2.7) and the normalisation of `ν_{p₁}` is
`exp (-(E'''_k - E_k) |T^{(k)}_1|)`. -/
theorem const_identity (hL : 0 < L) (ha₁ : 0 < S.a₁) (hβ : 0 < S.β) (hp₁ : 0 < S.p₁) :
    (S.cKernel / (2 * Real.pi)) ^ ((N : ℝ) * S.nBlocks / 2) *
        (S.betaU ^ (-((N * Fintype.card S.U : ℕ) : ℝ) / 2) *
          fluctNorm N S.p₁ ^ Fintype.card S.U) =
      Real.exp (-((S.Eppp C - C.Ek) * S.nU)) := by
  have hL' : (0 : ℝ) < L := by exact_mod_cast hL
  have hcK : 0 < S.cKernel := by
    unfold cKernel
    have : 0 < ((L : ℝ) ^ (k + 1)) ^ d / ((L : ℝ) ^ (k + 1)) ^ 2 := by positivity
    positivity
  have hA : 0 < S.cKernel / (2 * Real.pi) := by positivity
  have hB := betaU_pos' S hL hβ
  have hZ := fluctNorm_pos N hp₁
  have he : fluctE N S.p₁ = -((N : ℝ) / 2) * Real.log (2 * Real.pi) + Real.log (fluctNorm N S.p₁) := by
    unfold fluctE
    rw [Real.log_mul (by positivity) hZ.ne', Real.log_rpow (by positivity)]
    ring
  have hZe : fluctNorm N S.p₁ ^ Fintype.card S.U =
      Real.exp ((Fintype.card S.U : ℝ) * Real.log (fluctNorm N S.p₁)) := by
    rw [Real.exp_nat_mul, Real.exp_log hZ]
  rw [Real.rpow_def_of_pos hA, Real.rpow_def_of_pos hB, hZe, ← Real.exp_add, ← Real.exp_add]
  congr 1
  unfold Eppp Epp Ep nBlocks nU
  rw [he]
  push_cast
  field_simp
  ring

end Constants

/-- **Regularity of the interpolation along the ray** (the analyticity (H.2), (H.7) of the class
terms on `Ξ^c`, and of the Background field on `𝒟`, along the path `s ↦ ψ^{(k)} + s ψ'`): the
exponents of `μ_{s,t}`, truncated to the support `{χ_fl = 1}` of `ν_{p₁}`, are `C¹` families on an
open neighbourhood of `[0,1]`, bounded together with their derivatives. -/
structure StepRegular (g : Fld d L N₁ m₁ (k + 1) N) : Prop where
  c1 : ∃ (U : Set ℝ) (W₁' W₂' : ℝ → S.E → ℂ),
    IsC1Family U (S.WoneT C) W₁' ∧ IsC1Family U (S.WtwoT C g) W₂'

/-- **Nonvanishing of the partition functions** (the cluster expansion, Theorem 3.4 (a), (e)) along
the two segments of the interpolation: `Z_{s,0} ≠ 0` and `Z_{1,t} ≠ 0`, `s, t ∈ [0,1]`. Automatic
for real data, where `Z_{s,t} > 0`. -/
structure StepNonvanishing (g : Fld d L N₁ m₁ (k + 1) N) : Prop where
  seg1 : ∀ s ∈ Set.Icc (0 : ℝ) 1, S.Zst C g s 0 ≠ 0
  seg2 : ∀ t ∈ Set.Icc (0 : ℝ) 1, S.Zst C g 1 t ≠ 0

theorem psi0_add_smul (x : S.E) : S.psi0 + (S.betaU ^ (-(1 / 2 : ℝ))) • S.K x = S.psiAt 1 x := by
  unfold psiAt shiftU; rw [one_smul]

theorem psiAt_zero (x : S.E) : S.psiAt 0 x = S.psi0 := by
  unfold psiAt; rw [zero_smul, add_zero]

theorem WoneT_of_chi (s : ℝ) (x : S.E) (hx : chiFl S.U N S.p₁ x = 1) :
    S.WoneT C s x = S.Wone C s x := by
  simp [WoneT, hx]

theorem WtwoT_of_chi (g : Fld d L N₁ m₁ (k + 1) N) (s : ℝ) (x : S.E)
    (hx : chiFl S.U N S.p₁ x = 1) : S.WtwoT C g s x = S.Wtwo C g s x := by
  simp [WtwoT, hx]

theorem ae_ball (hp₁ : 0 < S.p₁) : ∀ᵐ x ∂S.nuFl, chiFl S.U N S.p₁ x = 1 :=
  ae_chiFl_fluctMeasure S.U N hp₁

theorem Wtwo_zero (g : Fld d L N₁ m₁ (k + 1) N) (x : S.E) : S.Wtwo C g 0 x = 0 := by
  unfold Wtwo dF
  rw [S.psiAt_zero]
  exact sub_self _

theorem WoneT_zero (x : S.E) (hV : S.Vk S.psi0 = 0) : S.WoneT C 0 x = 0 := by
  unfold WoneT Wone dE
  rw [S.psiAt_zero, hV]
  simp

theorem WtwoT_zero (g : Fld d L N₁ m₁ (k + 1) N) (x : S.E) : S.WtwoT C g 0 x = 0 := by
  unfold WtwoT
  rw [S.Wtwo_zero]
  simp

section Final

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
/-- **Proposition 2.6, (2.6)-(2.9), whole lattice, `λ = ∞`, complete convention** (FLUCTUATION
§2.6).  On `{χ_{k+1,u} = 1}`,
`(T^{(k)} χ^{(k)} ρ_k)(θ) = exp [-β_k A^η_{k+1}(θ, φ_{k+1}) + ℰ_k(ψ^{(k)}(θ)) - E'''_k |T^{(k)}_1|
+ ℱ_k(ψ^{(k)}(θ), g) + ℰ₀^{(k+1)} + ℱ₀^{(k+1)}(g)]`.  Premises: those of Lemma 2.5 (the source
premises on the data and constants), the regularity of the exponents along the ray and the
nonvanishing `Z_{s,0}, Z_{1,t} ≠ 0`. -/
theorem prop26_complex (g : Fld d L N₁ m₁ (k + 1) N) (hreg : StepRegular S C g)
    (hnv : StepNonvanishing S C g) :
    S.Tstep C g = Complex.exp (-(S.β : ℂ) * (S.Anew : ℂ) +
      EcompAt C.m₀ C.Tm S.a S.ν (Nat.le_succ k) S.psiKd - (S.Eppp C : ℂ) * (S.nU : ℂ) +
      FcompAt C.m₀ C.Tm S.a S.ν (Nat.le_succ k) S.psiKd g + S.E0 C + S.F0 C g) := by
  classical
  have hL : 0 < L := Nat.pos_of_ne_zero (NeZero.ne L)
  have hβU := betaU_pos' S hL hβ
  have hχ := (chiU_eq_one_iff _ _ _ _).1 hχu
  obtain ⟨U, W₁', W₂', h₁, h₂⟩ := hreg.c1
  have hdet := S.det_K_ne H hδ'0 hδ' hD'R hδ0 hχ hfam hsm
  have hV0 := S.Vk_psi0 ha₁ H hδ'0 hδ' hD'R
  have key := fluct_integral_eq_complex S.K hdet hβU hp₁ S.psi0 (S.Pconst C g)
    (fun ψ => (S.tKernel ψ : ℂ) * (S.chiK ψ : ℂ) * S.rhoStep C g ψ)
    (W₁ := S.WoneT C) (W₂ := S.WtwoT C g) (U := U)
    (fun x => by
      rw [S.psi0_add_smul]
      exact S.integrand_eq C ha₁ H hδ'0 hδ' hD'R hδ0 hfam hsm hχu hnorm hβ hp₁ hB5 hK2 hp40 hrad
        g x)
    h₁ h₂ (fun x => S.WoneT_zero C x hV0) (fun x => S.WtwoT_zero C g x)
    (fun s hs => by
      have h := hnv.seg1 s hs
      unfold Zst at h
      rw [← partFun₂_congr_ae (ν := S.nuFl) (W₁ := S.WoneT C) (W₁' := S.Wone C)
        (W₂ := S.WtwoT C g) (W₂' := S.Wtwo C g)
        ((S.ae_ball hp₁).mono fun x hx => S.WoneT_of_chi C s x hx)
        ((S.ae_ball hp₁).mono fun x hx => S.WtwoT_of_chi C g 0 x hx)] at h
      exact h)
    (fun t ht => by
      have h := hnv.seg2 t ht
      unfold Zst at h
      rw [← partFun₂_congr_ae (ν := S.nuFl) (W₁ := S.WoneT C) (W₁' := S.Wone C)
        (W₂ := S.WtwoT C g) (W₂' := S.Wtwo C g)
        ((S.ae_ball hp₁).mono fun x hx => S.WoneT_of_chi C 1 x hx)
        ((S.ae_ball hp₁).mono fun x hx => S.WtwoT_of_chi C g t x hx)] at h
      exact h)
  have hI1 : (∫ s in (0 : ℝ)..1, avgFun₂ (fluctMeasure S.U N S.p₁) (S.WoneT C) (S.WtwoT C g)
      (W₁' s) s 0) = S.E1 C := by
    unfold E1
    refine intervalIntegral.integral_congr (fun s hs => ?_)
    have hsU : s ∈ U := h₁.Icc_subset (by rwa [Set.uIcc_of_le zero_le_one] at hs)
    show avgFun₂ S.nuFl (S.WoneT C) (S.WtwoT C g) (W₁' s) s 0 = _
    rw [avgFun_eq_avgFun₂ (W₂ := S.Wtwo C g) (fun x => S.Wtwo_zero C g x)]
    refine avgFun₂_congr_ae ?_ ?_ ?_
    · exact (S.ae_ball hp₁).mono fun x hx => S.WoneT_of_chi C s x hx
    · exact (S.ae_ball hp₁).mono fun x hx => S.WtwoT_of_chi C g 0 x hx
    · filter_upwards [S.ae_ball hp₁] with x hx
      have hd := h₁.hasDerivAt x s hsU
      have hfun : (fun r => S.WoneT C r x) = fun r => S.Wone C r x :=
        funext fun r => S.WoneT_of_chi C r x hx
      rw [hfun] at hd
      exact hd.deriv.symm
  have hI2 : (∫ t in (0 : ℝ)..1, avgFun₂ (fluctMeasure S.U N S.p₁) (S.WoneT C) (S.WtwoT C g)
      (W₂' t) 1 t) = S.F0 C g := by
    unfold F0
    refine intervalIntegral.integral_congr (fun t ht => ?_)
    have htU : t ∈ U := h₂.Icc_subset (by rwa [Set.uIcc_of_le zero_le_one] at ht)
    show avgFun₂ S.nuFl (S.WoneT C) (S.WtwoT C g) (W₂' t) 1 t = _
    refine avgFun₂_congr_ae ?_ ?_ ?_
    · exact (S.ae_ball hp₁).mono fun x hx => S.WoneT_of_chi C 1 x hx
    · exact (S.ae_ball hp₁).mono fun x hx => S.WtwoT_of_chi C g t x hx
    · filter_upwards [S.ae_ball hp₁] with x hx
      have hd := h₂.hasDerivAt x t htU
      have hfun : (fun r => S.WtwoT C g r x) = fun r => S.Wtwo C g r x :=
        funext fun r => S.WtwoT_of_chi C g r x hx
      rw [hfun] at hd
      exact hd.deriv.symm
  have hconst := S.const_identity C hL ha₁ hβ hp₁
  have hdetabs := S.abs_det_K H hδ'0 hδ' hD'R hδ0 hχ hfam hsm
  show (∫ ψ, (S.tKernel ψ : ℂ) * (S.chiK ψ : ℂ) * S.rhoStep C g ψ) = _
  rw [key, hI1, hI2]
  unfold Pconst E0
  rw [hdetabs]
  set K0 : ℝ := (S.cKernel / (2 * Real.pi)) ^ ((N : ℝ) * S.nBlocks / 2) with hK0
  set bp : ℝ := S.betaU ^ (-((N * Fintype.card S.U : ℕ) : ℝ) / 2) with hbp
  set Zc : ℝ := fluctNorm N S.p₁ ^ Fintype.card S.U with hZc
  set Y : ℂ := -(S.β : ℂ) * (S.Anew : ℂ) +
      EcompAt C.m₀ C.Tm S.a S.ν (Nat.le_succ k) S.psiKd - (C.Ek : ℂ) * (S.nU : ℂ) +
      FcompAt C.m₀ C.Tm S.a S.ν (Nat.le_succ k) S.psiKd g with hY
  have hX : -(S.β : ℂ) * (S.Anew : ℂ) +
      EcompAt C.m₀ C.Tm S.a S.ν (Nat.le_succ k) S.psiKd - (S.Eppp C : ℂ) * (S.nU : ℂ) +
      FcompAt C.m₀ C.Tm S.a S.ν (Nat.le_succ k) S.psiKd g +
      ((S.halfLogDetC : ℂ) + S.E1 C) + S.F0 C g =
      Y + ((-((S.Eppp C - C.Ek) * S.nU) : ℝ) : ℂ) + (S.halfLogDetC : ℂ) + (S.E1 C + S.F0 C g) := by
    rw [hY]; push_cast; ring
  have hE : Complex.exp (-(S.β : ℂ) * (S.Anew : ℂ) +
      EcompAt C.m₀ C.Tm S.a S.ν (Nat.le_succ k) S.psiKd - (S.Eppp C : ℂ) * (S.nU : ℂ) +
      FcompAt C.m₀ C.Tm S.a S.ν (Nat.le_succ k) S.psiKd g +
      ((S.halfLogDetC : ℂ) + S.E1 C) + S.F0 C g) =
      Complex.exp Y * ((Real.exp (-((S.Eppp C - C.Ek) * S.nU)) : ℝ) : ℂ) *
        ((Real.exp S.halfLogDetC : ℝ) : ℂ) * Complex.exp (S.E1 C + S.F0 C g) := by
    rw [hX, Complex.exp_add, Complex.exp_add, Complex.exp_add, Complex.ofReal_exp,
      Complex.ofReal_exp]
  rw [hE]
  have hc' : (K0 : ℂ) * ((bp * Zc : ℝ) : ℂ) = ((Real.exp (-((S.Eppp C - C.Ek) * S.nU)) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, hconst]
  have hsplit : ((bp * Real.exp S.halfLogDetC * Zc : ℝ) : ℂ) =
      ((bp * Zc : ℝ) : ℂ) * ((Real.exp S.halfLogDetC : ℝ) : ℂ) := by push_cast; ring
  rw [hsplit]
  linear_combination (Complex.exp Y * ((Real.exp S.halfLogDetC : ℝ) : ℂ) *
    Complex.exp (S.E1 C + S.F0 C g)) * hc'

end Final

/-- **Reality of the class terms on real data** (the terms `ℰ_k`, `ℱ_k` are real for real
arguments in the domain `𝒟_ℝ`, (H.2), (H.7)). -/
structure RealClassTerms (g : Fld d L N₁ m₁ (k + 1) N) : Prop where
  E_real : ∀ ψ : S.E, InUnionDomainR (stepG d L N₁ m₁ k ϱ) (bgC1 d L N) S.ν (S.dataU ψ) →
    (EcompAt C.m₀ C.Tm S.a S.ν (Nat.le_succ k) (S.dataU ψ)).im = 0
  F_real : ∀ ψ : S.E, InUnionDomainR (stepG d L N₁ m₁ k ϱ) (bgC1 d L N) S.ν (S.dataU ψ) →
    (FcompAt C.m₀ C.Tm S.a S.ν (Nat.le_succ k) (S.dataU ψ) g).im = 0

theorem chiFl_smul (hp₁ : 0 < S.p₁) {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) {x : S.E}
    (hx : chiFl S.U N S.p₁ x = 1) : chiFl S.U N S.p₁ (s • x) = 1 := by
  rw [chiFl_eq_one_iff hp₁] at hx ⊢
  rw [norm_smul, Real.norm_of_nonneg hs.1]
  calc s * ‖x‖ ≤ 1 * ‖x‖ := by gcongr; exact hs.2
    _ < S.p₁ := by simpa using hx

section Real1

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
theorem dataU_inDomainR_path {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) (x : S.E)
    (hx : chiFl S.U N S.p₁ x = 1) :
    InUnionDomainR (stepG d L N₁ m₁ k ϱ) (bgC1 d L N) S.ν (S.dataU (S.psiAt s x)) := by
  have h := S.dataU_inDomainR ha₁ H hδ'0 hδ' hD'R hδ0 hfam hsm hχu hnorm hβ hp₁ hB5 hK2 hp40 hrad
    (s • x) (S.chiFl_smul hp₁ hs hx)
  rwa [S.psiAt_smul, one_mul] at h

include S ha₁ H hδ'0 hδ' hD'R hδ0 hfam hsm hχu hnorm hβ hp₁ hB5 hK2 hp40 hrad in
/-- The interaction `V^{(k)}` is real on the ray. -/
theorem Vk_im {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) (x : S.E) (hx : chiFl S.U N S.p₁ x = 1) :
    (S.Vk (S.psiAt s x)).im = 0 := by
  have h := S.Jbg_expansion ha₁ H hδ'0 hδ' hD'R hδ0 hfam hsm hχu hnorm hβ hp₁ hB5 hK2 hp40 hrad
    (s • x) (S.chiFl_smul hp₁ hs hx)
  rw [S.psiAt_smul, one_mul] at h
  have key : S.Vk (S.psiAt s x) =
      (((Jbg (stepG d L N₁ m₁ k ϱ) S.G' S.a S.a₁ S.ν k S.D'.Ψ (S.dataU (S.psiAt s x)) - S.Anew -
        1 / (2 * S.β) * ∑ b : S.U, ‖(s • x) b‖ ^ 2 : ℝ)) : ℂ) := by
    simp only [Complex.ofReal_sub]
    linear_combination -h
  rw [key]
  exact Complex.ofReal_im _

end Real1

section Real2

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
  (g : Fld d L N₁ m₁ (k + 1) N) (hrc : S.RealClassTerms C g)

include S ha₁ H hδ'0 hδ' hD'R in
theorem dataU_psi0_domain :
    InUnionDomainR (stepG d L N₁ m₁ k ϱ) (bgC1 d L N) S.ν (S.dataU S.psi0) := by
  obtain ⟨hDU', -⟩ := S.D'_domains H hδ'0 hδ' hD'R
  have hdom := (criticalPoint_real ha₁ S.hG S.hG' (le_refl (k + 1)) H H S.D' hDU').2.1
  rw [S.dataU_psi0 ha₁ H hδ'0 hδ' hD'R]
  exact hdom

include S C ha₁ H hδ'0 hδ' hD'R hδ0 hfam hsm hχu hnorm hβ hp₁ hB5 hK2 hp40 hrad g hrc in
theorem Wone_im {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) (x : S.E) (hx : chiFl S.U N S.p₁ x = 1) :
    (S.Wone C s x).im = 0 := by
  have hV := S.Vk_im ha₁ H hδ'0 hδ' hD'R hδ0 hfam hsm hχu hnorm hβ hp₁ hB5 hK2 hp40 hrad hs x hx
  have hdom := S.dataU_inDomainR_path ha₁ H hδ'0 hδ' hD'R hδ0 hfam hsm hχu hnorm hβ hp₁ hB5 hK2 hp40
    hrad hs x hx
  have hdom0 := S.dataU_psi0_domain ha₁ H hδ'0 hδ' hD'R
  unfold Wone dE
  rw [Complex.add_im, Complex.sub_im, hrc.E_real _ hdom, hrc.E_real _ hdom0]
  simp [hV]

include S C ha₁ H hδ'0 hδ' hD'R hδ0 hfam hsm hχu hnorm hβ hp₁ hB5 hK2 hp40 hrad g hrc in
theorem Wtwo_im {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) (x : S.E) (hx : chiFl S.U N S.p₁ x = 1) :
    (S.Wtwo C g t x).im = 0 := by
  have hdom := S.dataU_inDomainR_path ha₁ H hδ'0 hδ' hD'R hδ0 hfam hsm hχu hnorm hβ hp₁ hB5 hK2 hp40
    hrad ht x hx
  have hdom0 := S.dataU_psi0_domain ha₁ H hδ'0 hδ' hD'R
  unfold Wtwo dF
  rw [Complex.sub_im, hrc.F_real _ hdom, hrc.F_real _ hdom0]
  simp

include S C ha₁ H hδ'0 hδ' hD'R hδ0 hfam hsm hχu hnorm hβ hp₁ hB5 hK2 hp40 hrad g hrc in
/-- **Real data: `Z_{s,t}` is a positive real** (`s, t ∈ [0,1]`; this includes the nonvanishing
of §2.6). -/
theorem Zst_real_pos (hreg : StepRegular S C g) {s t : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1)
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    (S.Zst C g s t).im = 0 ∧ 0 < (S.Zst C g s t).re := by
  obtain ⟨U, W₁', W₂', h₁, h₂⟩ := hreg.c1
  have : MeasureTheory.IsProbabilityMeasure S.nuFl := isProbabilityMeasure_fluctMeasure S.U N hp₁
  have hsU : s ∈ U := h₁.Icc_subset hs
  have htU : t ∈ U := h₂.Icc_subset ht
  have hZ : S.Zst C g s t = partFun₂ S.nuFl (S.WoneT C) (S.WtwoT C g) s t := by
    unfold Zst
    exact partFun₂_congr_ae ((S.ae_ball hp₁).mono fun x hx => (S.WoneT_of_chi C s x hx).symm)
      ((S.ae_ball hp₁).mono fun x hx => (S.WtwoT_of_chi C g t x hx).symm)
  rw [hZ]
  obtain ⟨M₁, hM₁⟩ := h₁.bound
  obtain ⟨M₂, hM₂⟩ := h₂.bound
  refine partFun₂_real_pos (h₁.measurable s hsU) (h₂.measurable t htU) (fun x => ?_) (fun x => ?_)
    (fun x => (hM₁ x s hsU).1) (fun x => (hM₂ x t htU).1)
  · unfold WoneT
    by_cases hx : chiFl S.U N S.p₁ x = 1
    · simp only [hx, ↓reduceIte]
      exact S.Wone_im C ha₁ H hδ'0 hδ' hD'R hδ0 hfam hsm hχu hnorm hβ hp₁ hB5 hK2 hp40 hrad g hrc
        hs x hx
    · simp [hx]
  · unfold WtwoT
    by_cases hx : chiFl S.U N S.p₁ x = 1
    · simp only [hx, ↓reduceIte]
      exact S.Wtwo_im C ha₁ H hδ'0 hδ' hD'R hδ0 hfam hsm hχu hnorm hβ hp₁ hB5 hK2 hp40 hrad g hrc
        ht x hx
    · simp [hx]

include S C ha₁ H hδ'0 hδ' hD'R hδ0 hfam hsm hχu hnorm hβ hp₁ hB5 hK2 hp40 hrad g hrc in
/-- **Proposition 2.6 for real data**: the nonvanishing is automatic (`Z_{s,t} > 0`). -/
theorem prop26_real (hreg : StepRegular S C g) :
    S.Tstep C g = Complex.exp (-(S.β : ℂ) * (S.Anew : ℂ) +
      EcompAt C.m₀ C.Tm S.a S.ν (Nat.le_succ k) S.psiKd - (S.Eppp C : ℂ) * (S.nU : ℂ) +
      FcompAt C.m₀ C.Tm S.a S.ν (Nat.le_succ k) S.psiKd g + S.E0 C + S.F0 C g) := by
  refine S.prop26_complex C ha₁ H hδ'0 hδ' hD'R hδ0 hfam hsm hχu hnorm hβ hp₁ hB5 hK2 hp40 hrad g
    hreg ⟨fun s hs => ?_, fun t ht => ?_⟩
  · have h := S.Zst_real_pos C ha₁ H hδ'0 hδ' hD'R hδ0 hfam hsm hχu hnorm hβ hp₁ hB5 hK2 hp40 hrad g
      hrc hreg hs (Set.left_mem_Icc.2 zero_le_one)
    intro h0
    rw [h0] at h
    simp at h
  · have h := S.Zst_real_pos C ha₁ H hδ'0 hδ' hD'R hδ0 hfam hsm hχu hnorm hβ hp₁ hB5 hK2 hp40 hrad g
      hrc hreg (Set.right_mem_Icc.2 zero_le_one) ht
    intro h0
    rw [h0] at h
    simp at h

end Real2

end StepSetting

end Balaban.Fluctuation
