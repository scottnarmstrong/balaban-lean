/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.Lemma25Real
public import Balaban.Localization.Dec2Covariance
public import Balaban.Localization.Decoupled2X
public import Balaban.Localization.DecEquivReal
public import Balaban.Fluctuation.HoleStepOldCoef
import Mathlib.Tactic.Linarith

/-!
# Reality of the decoupled covariance square root at every decoupling vector

`Dec2.decCovSqrt C H a aT ν α s φ Q P` has real entries whenever the data `α`, `φ`, `Q`, `P` and the
decoupling vector `s` are real (`decCovSqrt_isRealMat`).  This generalizes `Lemma25Real` from
`s = 1` (`decCovSqrt_isRealMat`) to an arbitrary real decoupling vector, in particular to every
interpolation parameter `s ∈ [0,1]`.  The proof is entrywise reality of the pieces (`Gsx`, `decM`,
`decN`, `decPi`, `decCov`) at each `x`, then of the integral (`integral_conj`).
-/

@[expose] public section

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization Balaban.Fluctuation Finset
  Matrix

namespace Balaban.Localization.Dec2

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
  (C : DecCover d L N₁ m₁ (k + 1)) (H : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ)
  (a : ℕ → ℝ) (aT x ν : ℝ) {α : H.Ω 1 → ℂ} {s : ℕ × CTorus d L N₁ m₁ (k + 1) → ℂ}
  {φ : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ}

theorem isRealMat_chiD (q : ℕ × CTorus d L N₁ m₁ (k + 1)) : IsRealMat (chiD C H q) := fun p r => by
  by_cases h : p = r <;> simp [chiD, h]

theorem isRealMat_cD (q : ℕ × CTorus d L N₁ m₁ (k + 1)) : IsRealMat (cD H q) := fun p r => by
  by_cases h : p = r <;> simp [cD, h]

theorem isRealMat_cutX (cut : Finset (Torus d (N₁ * L ^ m₁ * L ^ (k + 1)) × Fin d))
    (hα : ∀ w, starRingEnd ℂ (α w) = α w) : IsRealMat (cutXOperator H a aT x ν cut α) := by
  unfold cutXOperator
  refine IsRealMat.add (fun p q => ?_) (fun p q => ?_)
  · simp [Green.restrictOp, Matrix.submatrix_apply, Matrix.map_apply]
  · by_cases h : p = q <;> simp [h, hα]

theorem isRealMat_cubeGx (hα : ∀ w, starRingEnd ℂ (α w) = α w)
    (q : ℕ × CTorus d L N₁ m₁ (k + 1)) : IsRealMat (cubeGx H a aT x ν α q) :=
  (isRealMat_cutX H a aT x ν _ hα).inv.mul (isRealMat_cD H q)

theorem isRealMat_xDirichlet' (hα : ∀ w, starRingEnd ℂ (α w) = α w) :
    IsRealMat (xDirichletOperator H a aT x ν α) := isRealMat_xDirichlet x hα

theorem conj_sProd (hs : ∀ P, starRingEnd ℂ (s P) = s P) (q : ℕ × CTorus d L N₁ m₁ (k + 1)) :
    starRingEnd ℂ (C.sProd s q) = C.sProd s q := by
  unfold DecCover.sProd
  rw [map_prod]
  exact Finset.prod_congr rfl fun P _ => hs P

theorem isRealMat_sum_smul {ι : Type*} [Fintype ι] (T : Finset (ℕ × CTorus d L N₁ m₁ (k + 1)))
    (c : ℕ × CTorus d L N₁ m₁ (k + 1) → ℂ) (M : ℕ × CTorus d L N₁ m₁ (k + 1) → Matrix ι ι ℂ)
    (hc : ∀ q, starRingEnd ℂ (c q) = c q) (hM : ∀ q, IsRealMat (M q)) :
    IsRealMat (∑ q ∈ T, c q • M q) := by
  intro p r
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, map_sum, map_mul, hc, hM _ p r]

theorem isRealMat_Gsx (hα : ∀ w, starRingEnd ℂ (α w) = α w)
    (hs : ∀ P, starRingEnd ℂ (s P) = s P) : IsRealMat (Gsx C H a aT x ν α s) := by
  have hK : IsRealMat (Kcalx C H a aT x ν α s) :=
    isRealMat_sum_smul _ _ _ (conj_sProd C hs) fun q => by
      unfold Kzx
      exact (((isRealMat_chiD C H q).mul (isRealMat_xDirichlet' H a aT x ν
        (α := 0) (fun w => by simp))).sub
        ((isRealMat_xDirichlet' H a aT x ν (α := 0) (fun w => by simp)).mul
          (isRealMat_chiD C H q))).mul (isRealMat_cubeGx H a aT x ν hα q)
  have hG : IsRealMat (Gstarx C H a aT x ν α s) :=
    isRealMat_sum_smul _ _ _ (conj_sProd C hs) fun q =>
      (isRealMat_chiD C H q).mul (isRealMat_cubeGx H a aT x ν hα q)
  exact hG.mul (isRealMat_one.sub hK).inv

theorem isRealMat_commK {ι : Type*} [Fintype ι] [DecidableEq ι] {Hm : Matrix ι ι ℂ}
    (hH : IsRealMat Hm) {ψ : ι → Fin N → ℂ} (hψ : ∀ y i, starRingEnd ℂ (ψ y i) = ψ y i) :
    IsRealMat (commK Hm ψ) := by
  unfold commK
  exact ((isRealMat_fieldMul hψ).transpose.mul (isRealMat_liftOp N hH)).sub
    (hH.mul (isRealMat_fieldMul hψ).transpose)

theorem isRealMat_restrictField (hφ : ∀ y i, starRingEnd ℂ (φ y i) = φ y i) :
    ∀ y i, starRingEnd ℂ (restrictField H φ y i) = restrictField H φ y i := fun y i => hφ _ _

theorem isRealMat_decM (hα : ∀ w, starRingEnd ℂ (α w) = α w)
    (hs : ∀ P, starRingEnd ℂ (s P) = s P) (hφ : ∀ y i, starRingEnd ℂ (φ y i) = φ y i) :
    IsRealMat (decM C H a aT x ν α s φ) := by
  have hF := isRealMat_fieldMul (isRealMat_restrictField H hφ)
  unfold decM constraintM
  exact (hF.transpose.mul hF).sub
    (((isRealMat_commK (isRealMat_xDirichlet' H a aT x ν hα) (isRealMat_restrictField H hφ)).mul
      (isRealMat_liftOp N (isRealMat_Gsx C H a aT x ν hα hs))).mul hF)

theorem isRealMat_decN (hα : ∀ w, starRingEnd ℂ (α w) = α w)
    (hs : ∀ P, starRingEnd ℂ (s P) = s P) (hφ : ∀ y i, starRingEnd ℂ (φ y i) = φ y i) :
    IsRealMat (decN C H a aT x ν α s φ) := by
  have hF := isRealMat_fieldMul (isRealMat_restrictField H hφ)
  unfold decN constraintN
  exact hF.transpose.sub
    ((isRealMat_commK (isRealMat_xDirichlet' H a aT x ν hα) (isRealMat_restrictField H hφ)).mul
      (isRealMat_liftOp N (isRealMat_Gsx C H a aT x ν hα hs)))

theorem isRealMat_decPi (hα : ∀ w, starRingEnd ℂ (α w) = α w)
    (hs : ∀ P, starRingEnd ℂ (s P) = s P) (hφ : ∀ y i, starRingEnd ℂ (φ y i) = φ y i) :
    IsRealMat (decPi C H a aT x ν α s φ) := by
  unfold decPi
  exact (((isRealMat_liftOp N (isRealMat_Gsx C H a aT x ν hα hs)).mul
    (isRealMat_fieldMul (isRealMat_restrictField H hφ))).mul
      (isRealMat_decM (N := N) C H a aT x ν hα hs hφ).inv).mul
    (isRealMat_decN (N := N) C H a aT x ν hα hs hφ)

theorem isRealMat_smul_conj {ι : Type*} {c : ℂ} (hc : starRingEnd ℂ c = c) {A : Matrix ι ι ℂ}
    (hA : IsRealMat A) : IsRealMat (c • A) := fun p q => by
  simp [hc, hA p q]

theorem isRealMat_covA {ι : Type*} [Fintype ι] [DecidableEq ι] (c b : ℝ) {P : Matrix ι ι ℂ}
    (hP : IsRealMat P) : IsRealMat (covA c b x P) := by
  unfold covA
  refine IsRealMat.add (isRealMat_smul_conj ?_ (isRealMat_one.sub hP))
    (isRealMat_smul_conj ?_ hP)
  · simp
  · simp

variable {κι : Type*} [Fintype κι] [DecidableEq κι]

theorem isRealMat_decCov (hα : ∀ w, starRingEnd ℂ (α w) = α w)
    (hs : ∀ P, starRingEnd ℂ (s P) = s P) (hφ : ∀ y i, starRingEnd ℂ (φ y i) = φ y i)
    {Q : Matrix κι (H.Ω 1) ℂ} {P : Matrix κι κι ℂ} (hQ : IsRealMat Q) (hP : IsRealMat P) :
    IsRealMat (decCov C H a aT x ν α s φ Q P) := by
  have hA := isRealMat_covA x (a k) (aT / (L : ℝ) ^ 2) (isRealMat_liftOp N hP)
  unfold decCov
  refine hA.add (isRealMat_smul_conj (by simp) ?_)
  exact (((hA.mul (isRealMat_liftRect N hQ)).mul
    ((isRealMat_liftOp N (isRealMat_Gsx C H a aT x ν hα hs)).sub
      (isRealMat_decPi (N := N) C H a aT x ν hα hs hφ))).mul
    (isRealMat_liftRect N hQ).transpose).mul hA

/-- **Reality of the decoupled covariance square root at every real decoupling vector.** -/
theorem decCovSqrt_isRealMat (hα : ∀ w, starRingEnd ℂ (α w) = α w)
    (hs : ∀ P, starRingEnd ℂ (s P) = s P) (hφ : ∀ y i, starRingEnd ℂ (φ y i) = φ y i)
    {Q : Matrix κι (H.Ω 1) ℂ} {P : Matrix κι κι ℂ} (hQ : IsRealMat Q) (hP : IsRealMat P) :
    IsRealMat (decCovSqrt C H a aT ν α s φ Q P) := by
  intro p q
  have e : decCovSqrt C H a aT ν α s φ Q P p q = ((1 / Real.pi : ℝ) : ℂ) *
      ∫ x in Set.Ioi (0 : ℝ), ((x ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
        decCov C H a aT x ν α s φ Q P p q := rfl
  rw [e, map_mul, Complex.conj_ofReal, ← integral_conj]
  congr 1
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only
  rw [map_mul, Complex.conj_ofReal,
    isRealMat_decCov (N := N) C H a aT x ν hα hs hφ hQ hP p q]

end Balaban.Localization.Dec2

namespace Balaban.Fluctuation

open Balaban.Localization.DecEquiv

section ComposedReal

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ ϱ' : ℝ}
  (S : HoleStep d L N₁ m₁ k N ϱ ϱ')

theorem svec_conj {G : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ'} (φ : G.Ω 1 × Fin N → ℂ)
    (h : ∀ p, starRingEnd ℂ (φ p) = φ p) (y : CTorus d L N₁ m₁ (k + 1)) (i : Fin N) :
    starRingEnd ℂ (svec G φ y i) = svec G φ y i := by
  by_cases hy : y ∈ G.Ω 1
  · rw [svec_of_mem' φ hy]; exact h _
  · simp [svec, zeroExt, hy]

theorem extS_conj (C : DecCover d L N₁ m₁ (k + 1)) {s : Dec2.DecParams C}
    (hs : ∀ P, starRingEnd ℂ (s P) = s P) (P : ℕ × CTorus d L N₁ m₁ (k + 1)) :
    starRingEnd ℂ (Dec2.extS C s P) = Dec2.extS C s P := by
  unfold Dec2.extS
  split_ifs with h
  · exact hs _
  · simp

theorem HoleStep.covSqrtAt_isRealMat (hD : S.D'.IsReal) (C : DecCover d L N₁ m₁ (k + 1)) (ρ : ℝ)
    {s : Dec2.DecParams C} (hs : ∀ P, starRingEnd ℂ (s P) = s P) :
    IsRealMat (S.covSqrtAt C ρ s) := by
  obtain ⟨hf, hm⟩ := decBg2_real (C := C) (H := S.G') (a := S.a) (ν := S.ν) (ρ := ρ) hs hD
  exact Dec2.decCovSqrt_isRealMat C S.G' S.a S.a₁ S.ν hm (extS_conj C hs)
    (fun y i => svec_conj _ hf y i) isRealMat_unitQ isRealMat_unitP

theorem HoleStep.psiKdAt_isReal (hD : S.D'.IsReal) (C : DecCover d L N₁ m₁ (k + 1)) (ρ : ℝ)
    {s : Dec2.DecParams C} (hs : ∀ P, starRingEnd ℂ (s P) = s P) :
    (S.psiKdAt C ρ s).IsReal := by
  obtain ⟨hf, -⟩ := decBg2_real (C := C) (H := S.G') (a := S.a) (ν := S.ν) (ρ := ρ) hs hD
  exact composeData_isReal S.hpre S.a _ S.D' (fun z i => Complex.conj_eq_iff_im.1 (hf _)) hD

/-- **The composed field is real** at real localization vectors and real fluctuation variables. -/
theorem HoleStep.composed_conj (hD : S.D'.IsReal) (C : DecCover d L N₁ m₁ (k + 1)) (ρ : ℝ)
    {sloc : S.U → Dec2.DecParams C} (hs : ∀ b P, starRingEnd ℂ (sloc b P) = sloc b P)
    {ψhat : S.U → Fin N → ℂ} (hψ : ∀ q i, starRingEnd ℂ (ψhat q i) = ψhat q i) (b : S.U)
    (i : Fin N) :
    starRingEnd ℂ (S.composed C ρ sloc ψhat b i) = S.composed C ρ sloc ψhat b i := by
  unfold HoleStep.composed HoleStep.psiLoc HoleStep.shiftLoc
  rw [map_add, map_mul, Complex.conj_ofReal]
  congr 1
  · exact Complex.conj_eq_iff_im.2 ((S.psiKdAt_isReal hD C ρ (hs b)) _ i).1
  · congr 1
    simp only [map_sum, map_mul]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [S.covSqrtAt_isRealMat hD C ρ (hs b) _ _, hψ]

end ComposedReal

end Balaban.Fluctuation
