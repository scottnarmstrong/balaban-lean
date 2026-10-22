/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Analysis.SourceRay

/-!
# Linearity and rotation covariance of the source ray

* `srcMDir_add`, `srcMDir_smul`, `srcMDir_sum`: the ray integral `srcMDir F g v` is linear in the direction
  (the integrands are continuous on `[0, 1]`, `intervalIntegrable_fderiv_ray`).
* `srcMDir_comp_of_mem`: `srcMDir (F ∘ T) g v = srcMDir F (T g) (T v)` for a continuous linear `T`, when
  only `T g` lies in the `ℓ¹` ball (the ray `t T g` stays in it by convexity); `srcMDir_comp` is its
  corollary with the premise "`T` maps the ball into the ball".
* `srcM_rot`: for `Rᵀ R = 1`, `F' (R g) = F g` where `g` and `R g` lie in the ball, `F'` analytic on
  the ball of radius `G`: `ℳ_x(F', R g) = R ℳ_x(F, g)` whenever `g` and `R g` lie in the ball
  (the shape of `SFTermClauses.rotM`); the ball need not be invariant under `R`.
-/

@[expose] public section

namespace Balaban.Analysis

open Metric Set MeasureTheory intervalIntegral

section Linear

variable {ι J : Type*} [Fintype ι] [Fintype J] [DecidableEq ι] [DecidableEq J]

omit [DecidableEq ι] [DecidableEq J] in
/-- **Covariance of the ray integral, premises on the two points only.**  For a continuous linear `T`
with `g` and `T g` in the `ℓ¹` ball (by convexity so are the rays `t g` and `t T g`),
`srcMDir (F ∘ T) g v = srcMDir F (T g) (T v)`. -/
theorem srcMDir_comp_of_mem {F : (ι → J → ℂ) → ℂ} {G : ℝ}
    (hF : AnalyticOnNhd ℂ F {g | l1src g < G}) (T : (ι → J → ℂ) →L[ℂ] (ι → J → ℂ))
    {g : ι → J → ℂ} (hTg : l1src (T g) < G) (v : ι → J → ℂ) :
    srcMDir (fun h => F (T h)) g v = srcMDir F (T g) (T v) := by
  unfold srcMDir
  refine intervalIntegral.integral_congr fun t ht => ?_
  rw [Set.uIcc_of_le zero_le_one] at ht
  have hh : l1src ((t : ℂ) • T g) < G := l1_smul_lt hTg ht.1 ht.2
  have hTt : T ((t : ℂ) • g) = (t : ℂ) • T g := map_smul T _ _
  have hdiff : DifferentiableAt ℂ F (T ((t : ℂ) • g)) := by
    rw [hTt]; exact (hF _ hh).differentiableAt
  have hchain : fderiv ℂ (fun h => F (T h)) ((t : ℂ) • g) =
      (fderiv ℂ F (T ((t : ℂ) • g))).comp T :=
    (hdiff.hasFDerivAt.comp ((t : ℂ) • g) T.hasFDerivAt).fderiv
  rw [hchain, ContinuousLinearMap.comp_apply, hTt]

omit [DecidableEq ι] [DecidableEq J] in
/-- **Covariance of the ray integral under a linear map of the sources**: for a continuous linear `T`
that maps the ball into the ball, `srcMDir (F ∘ T) g v = srcMDir F (T g) (T v)`. -/
theorem srcMDir_comp {F : (ι → J → ℂ) → ℂ} {G : ℝ}
    (hF : AnalyticOnNhd ℂ F {g | l1src g < G}) (T : (ι → J → ℂ) →L[ℂ] (ι → J → ℂ))
    (hT : ∀ g, l1src g < G → l1src (T g) < G) {g : ι → J → ℂ} (hg : l1src g < G)
    (v : ι → J → ℂ) :
    srcMDir (fun h => F (T h)) g v = srcMDir F (T g) (T v) :=
  srcMDir_comp_of_mem hF T (hT g hg) v

omit [DecidableEq ι] [DecidableEq J] in
theorem intervalIntegrable_fderiv_ray {F : (ι → J → ℂ) → ℂ} {G : ℝ}
    (hF : AnalyticOnNhd ℂ F {g | l1src g < G}) {g : ι → J → ℂ} (hg : l1src g < G)
    (v : ι → J → ℂ) :
    IntervalIntegrable (fun t : ℝ => fderiv ℂ F ((t : ℂ) • g) v) volume 0 1 := by
  have hA : AnalyticOnNhd ℂ (fderiv ℂ F) {g | l1src g < G} := hF.fderiv
  have hc1 : ContinuousOn (fun t : ℝ => fderiv ℂ F ((t : ℂ) • g)) (Icc (0 : ℝ) 1) := by
    refine hA.continuousOn.comp (g := fderiv ℂ F) ?_ (fun t ht => l1_smul_lt hg ht.1 ht.2)
    exact (Complex.continuous_ofReal.smul continuous_const).continuousOn
  exact (hc1.clm_apply continuousOn_const).intervalIntegrable_of_Icc zero_le_one

omit [DecidableEq ι] [DecidableEq J] in
theorem srcMDir_add {F : (ι → J → ℂ) → ℂ} {G : ℝ}
    (hF : AnalyticOnNhd ℂ F {g | l1src g < G}) {g : ι → J → ℂ} (hg : l1src g < G)
    (v w : ι → J → ℂ) : srcMDir F g (v + w) = srcMDir F g v + srcMDir F g w := by
  unfold srcMDir
  simp only [map_add]
  exact intervalIntegral.integral_add (intervalIntegrable_fderiv_ray hF hg v)
    (intervalIntegrable_fderiv_ray hF hg w)

omit [DecidableEq ι] [DecidableEq J] in
omit [Fintype ι] [Fintype J] in
theorem srcMDir_smul {F : (ι → J → ℂ) → ℂ} (c : ℂ) (g v : ι → J → ℂ) :
    srcMDir F g (c • v) = c * srcMDir F g v := by
  unfold srcMDir
  simp only [map_smul, smul_eq_mul]
  exact intervalIntegral.integral_const_mul c _

omit [DecidableEq ι] [DecidableEq J] in
theorem srcMDir_sum {F : (ι → J → ℂ) → ℂ} {G : ℝ}
    (hF : AnalyticOnNhd ℂ F {g | l1src g < G}) {g : ι → J → ℂ} (hg : l1src g < G)
    {κ : Type*} (s : Finset κ) (c : κ → ℂ) (v : κ → ι → J → ℂ) :
    srcMDir F g (∑ k ∈ s, c k • v k) = ∑ k ∈ s, c k * srcMDir F g (v k) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    unfold srcMDir
    simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, srcMDir_add hF hg, srcMDir_smul, ih]

end Linear

section Rot

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {N : ℕ}

/-- The action of a matrix `R` on the sources: row by row, `(R g)_x = R g_x` (`rotField R`). -/
noncomputable def rotSrc (R : Matrix (Fin N) (Fin N) ℂ) : (ι → Fin N → ℂ) →L[ℂ] (ι → Fin N → ℂ) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun g y => R.mulVec (g y)
      map_add' := fun g h => by funext y; simp [Matrix.mulVec_add]
      map_smul' := fun c g => by funext y; simp [Matrix.mulVec_smul] }

omit [DecidableEq ι] in
theorem rotSrc_apply (R : Matrix (Fin N) (Fin N) ℂ) (g : ι → Fin N → ℂ) (y : ι) :
    rotSrc R g y = R.mulVec (g y) := rfl

theorem rotSrc_unitSrc (R : Matrix (Fin N) (Fin N) ℂ) (x : ι) (j : Fin N) :
    rotSrc R (unitSrc x j) = ∑ i, R i j • unitSrc x i := by
  funext y k
  rw [rotSrc_apply]
  simp only [Finset.sum_apply, Pi.smul_apply, unitSrc, smul_eq_mul]
  by_cases hy : y = x
  · subst hy
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  · simp [hy, Matrix.mulVec, dotProduct]

/-- **Covariance of the source coefficient under a rotation of the sources.**  Let `R` satisfy
`Rᵀ R = 1` and let `F' (R g) = F g` wherever `g` and `R g` lie in the `ℓ¹` ball of radius `G`
(`F'` analytic there).  If `g` and `R g` lie in the ball, then `ℳ_x(F', R g) = R ℳ_x(F, g)`:
`srcMVec F' (R g) x = R *ᵥ srcMVec F g x`.  (No invariance of the ball under `R` is needed.) -/
theorem srcM_rot {F F' : (ι → Fin N → ℂ) → ℂ} {G : ℝ}
    (hF' : AnalyticOnNhd ℂ F' {g | l1src g < G})
    (R : Matrix (Fin N) (Fin N) ℂ) (hR : R.transpose * R = 1)
    (hFF : ∀ h, l1src h < G → l1src (rotSrc R h) < G → F' (rotSrc R h) = F h)
    {g : ι → Fin N → ℂ} (hg : l1src g < G) (hRg : l1src (rotSrc R g) < G) (x : ι) :
    srcMVec F' (rotSrc R g) x = R.mulVec (srcMVec F g x) := by
  -- the ray derivatives of `F` and `F' ∘ R` agree
  have hopen : IsOpen {h : ι → Fin N → ℂ | l1src h < G ∧ l1src (rotSrc R h) < G} :=
    (isOpen_lt continuous_l1src continuous_const).inter
      (isOpen_lt (continuous_l1src.comp (rotSrc R).continuous) continuous_const)
  have hcongr : ∀ v, srcMDir F g v = srcMDir (fun h => F' (rotSrc R h)) g v := by
    intro v
    unfold srcMDir
    refine intervalIntegral.integral_congr fun t ht => ?_
    rw [Set.uIcc_of_le zero_le_one] at ht
    have h1 : l1src ((t : ℂ) • g) < G := l1_smul_lt hg ht.1 ht.2
    have h2 : l1src (rotSrc R ((t : ℂ) • g)) < G := by
      rw [map_smul]; exact l1_smul_lt hRg ht.1 ht.2
    have hev : F =ᶠ[nhds ((t : ℂ) • g)] fun h => F' (rotSrc R h) := by
      filter_upwards [hopen.mem_nhds ⟨h1, h2⟩] with h hh using (hFF h hh.1 hh.2).symm
    rw [hev.fderiv_eq]
  -- the components
  have hcomp : ∀ j, srcM F g x j = ∑ i, R i j * srcM F' (rotSrc R g) x i := by
    intro j
    rw [srcM_eq_srcMDir, hcongr, srcMDir_comp_of_mem hF' (rotSrc R) hRg, rotSrc_unitSrc,
      srcMDir_sum hF' hRg]
    rfl
  have hvec : srcMVec F g x = R.transpose.mulVec (srcMVec F' (rotSrc R g) x) := by
    funext j
    simp only [srcMVec, hcomp j, Matrix.mulVec, dotProduct, Matrix.transpose_apply]
  rw [hvec, Matrix.mulVec_mulVec, mul_eq_one_comm.1 hR, Matrix.one_mulVec]

end Rot

end Balaban.Analysis
