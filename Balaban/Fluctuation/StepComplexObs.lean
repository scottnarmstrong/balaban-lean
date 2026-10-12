/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.StepComplexLocal
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The observable relation `ℱ₀ = ⟨g, β^{-1/2} ℳ₀⟩` for the complex step (FLUCTUATION.md (2.9); P4 (2.53))

The complex form of `StepObs`, for the holomorphic objects of `StepComplexOut`:

* `mcompCT`: the component `(y, i)` of `ℳ_k(ψ^{(k)}(θ) + t ψ'; g)` with the complex backgrounds
  (`McompAtC` on the path `psiAtC`), truncated to the support of `ν_{p₁}`;
* `ClassRegularObsC`: `ClassRegularLocC` extended by the `C¹` regularity in `t` of these components,
  bounded with their derivatives (the analytic terms `ℳ^{(j)}` of the class, (H.7), and the complex
  small solution `φ_k(ψ)`);
* `F0C_eq_pair`: `ℱ₀^{(k+1)}(g) = β_k^{-1/2} ∑_y ∑_i g(y,i) ℳ₀^{(k+1)}(y; g)_i` for `F0C`, `M0C`,
  under `ClassRegularObsC` and `StepNonvanishingC`, at every (complex) block datum.

`ClassRegularObsC` is inhabited for the class with zero old terms and every source on the complex
chart (`classRegularObsC_zeroClass`, in `StepComplexSource`).
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban.SmallField.Def6 Balaban.Background Balaban.Multiscale Balaban.Localization
  Balaban.SmallField Finset MeasureTheory Set

namespace StepSetting

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}
  (S : StepSetting d L N₁ m₁ k N ϱ) (C : StepClass d L N₁ m₁ k N ϱ)

/-- The component `(y, i)` of `ℳ_k(ψ^{(k)}(θ) + t ψ'; g)` of the complex step (`McompAtC` on the
path `psiAtC`), truncated to the support of `ν_{p₁}`; `mcompT` for the complex step. -/
noncomputable def mcompCT (g : Fld d L N₁ m₁ (k + 1) N) (y : CTorus d L N₁ m₁ (k + 1)) (i : Fin N)
    (r : ℝ) (x : S.E) : ℂ :=
  open Classical in if chiFl S.U N S.p₁ x = 1 then
    McompAtC C.m₀ C.Tm S.a S.ν (Nat.le_succ k) (S.dataUC (S.psiAtC r x)) g y i else 0

/-- **Regularity of the observable vector of the complex step along the interpolation**
(`ClassRegularObs` for the complex step): `ClassRegularLocC`, and every component of
`ℳ_k(y; ψ^{(k)}(θ) + t ψ', g)` with the complex backgrounds, truncated to the support of `ν_{p₁}`, is
a `C¹` family on an open neighbourhood of `[0,1]`, bounded with its derivative (the analyticity
(H.7) of the terms `ℳ^{(j)}` of the class and of the complex small solution `φ_k(ψ)` along the
path).  This is the hypothesis of `F0C_eq_pair`. -/
structure ClassRegularObsC (g : Fld d L N₁ m₁ (k + 1) N) : Prop extends S.ClassRegularLocC C where
  mcomp : ∀ (y : CTorus d L N₁ m₁ (k + 1)) (i : Fin N), ∃ (U : Set ℝ) (M' : ℝ → S.E → ℂ),
    IsC1Family U (S.mcompCT C g y i) M'

/-- **`ℱ₀^{(k+1)}(g) = ⟨g, β_k^{-1/2} ℳ₀^{(k+1)}(g)⟩₁` for the complex step** (FLUCTUATION (2.9),
P4 (2.53); the complex form of `F0_eq_pair`), for the holomorphic `F0C`, `M0C`, at every (complex)
block datum.  Premises: `ClassRegularObsC` and the nonvanishing of `Z_{1,t}`
(`StepNonvanishingC`). -/
theorem F0C_eq_pair (hp₁ : 0 < S.p₁) (hβ : 0 < S.β) (g : Fld d L N₁ m₁ (k + 1) N)
    (hc : S.ClassRegularObsC C g) (hnv : S.StepNonvanishingC C g) :
    S.F0C C g = ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
      ∑ y : CTorus d L N₁ m₁ (k + 1), ∑ i : Fin N, g y i * S.M0C C g y i := by
  classical
  obtain ⟨O, hO, hcd, hmem⟩ := hc.phi1
  have hprob : IsProbabilityMeasure S.nuFl := isProbabilityMeasure_fluctMeasure S.U N hp₁
  set B : Set S.E := Metric.closedBall (0 : S.E) S.p₁ with hBdef
  have hBc : IsCompact B := isCompact_closedBall _ _
  have hBm : MeasurableSet B := measurableSet_closedBall
  have hB : ∀ᵐ x ∂S.nuFl, x ∈ B := S.ae_mem_closedBall hp₁
  have hball : ∀ᵐ x ∂S.nuFl, chiFl S.U N S.p₁ x = 1 := S.ae_ball hp₁
  choose U M' hMC using hc.mcomp
  choose Mb hMb using fun y i => (hMC y i).bound
  set m : CTorus d L N₁ m₁ (k + 1) → Fin N → ℝ → S.E → ℂ := fun y i r x =>
    McompAtC C.m₀ C.Tm S.a S.ν (Nat.le_succ k) (S.dataUC (S.psiAtC r x)) g y i with hm
  set c : ℂ := FcompAtC C.m₀ C.Tm S.a S.ν (Nat.le_succ k) (S.dataUC S.psi0C) g with hcdef
  have hWt : ∀ r x, S.WtwoC C g r x = ∑ y, ∑ i, g y i * m y i r x - c := fun r x =>
    S.WtwoC_eq_sum C g r x
  have hmT : ∀ y i r x, chiFl S.U N S.p₁ x = 1 → S.mcompCT C g y i r x = m y i r x := by
    intro y i r x hx
    simp [mcompCT, hx, hm]
  have hIcc : ∀ y i, Icc (0 : ℝ) 1 ⊆ U y i := fun y i => (hMC y i).Icc_subset
  have hder : ∀ y i x, chiFl S.U N S.p₁ x = 1 → ∀ t ∈ Icc (0 : ℝ) 1,
      HasDerivAt (fun r => m y i r x) (M' y i t x) t := by
    intro y i x hx t ht
    have := (hMC y i).hasDerivAt x t (hIcc y i ht)
    have hfun : (fun r => S.mcompCT C g y i r x) = fun r => m y i r x := funext fun r =>
      hmT y i r x hx
    rwa [hfun] at this
  have hderW : ∀ x, chiFl S.U N S.p₁ x = 1 → ∀ t ∈ Icc (0 : ℝ) 1,
      HasDerivAt (fun r => S.WtwoC C g r x) (∑ y, ∑ i, g y i * M' y i t x) t := by
    intro x hx t ht
    have : (fun r => S.WtwoC C g r x) = fun r => (∑ y, ∑ i, g y i * m y i r x) - c :=
      funext fun r => hWt r x
    rw [this]
    have hs : HasDerivAt (fun r => ∑ y, ∑ i, g y i * m y i r x)
        (∑ y, ∑ i, g y i * M' y i t x) t :=
      HasDerivAt.fun_sum fun y _ => HasDerivAt.fun_sum fun i _ =>
        (hder y i x hx t ht).const_mul _
    exact hs.sub_const c
  -- bounds
  set M₂ : ℝ := (∑ y, ∑ i, ‖g y i‖ * Mb y i) + ‖c‖ with hM₂
  have hW2b : ∀ x, chiFl S.U N S.p₁ x = 1 → ∀ t ∈ Icc (0 : ℝ) 1, ‖S.WtwoC C g t x‖ ≤ M₂ := by
    intro x hx t ht
    rw [hWt]
    refine (norm_sub_le _ _).trans (add_le_add ?_ le_rfl)
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun y _ => ?_)
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [norm_mul]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    rw [← hmT y i t x hx]
    exact ((hMb y i) x t (hIcc y i ht)).1
  have hWc : ContinuousOn (fun q : ℝ × S.E => S.WoneC C q.1 q.2) (Icc (0 : ℝ) 1 ×ˢ B) :=
    S.continuousOn_Phi1C_ray hcd hmem
  have hW1c : ContinuousOn (fun x => S.WoneC C 1 x) B :=
    hWc.comp (f := fun x => ((1 : ℝ), x)) (by fun_prop)
      (fun x hx => ⟨⟨zero_le_one, le_rfl⟩, hx⟩)
  obtain ⟨M₁, hM₁⟩ := hBc.exists_bound_of_continuousOn hW1c
  have hν : S.nuFl.restrict B = S.nuFl := Measure.restrict_eq_self_of_ae_mem hB
  have hW1m : AEStronglyMeasurable (fun x => S.WoneC C 1 x) S.nuFl := by
    have h := hW1c.aestronglyMeasurable hBm (μ := S.nuFl)
    rwa [hν] at h
  -- the exponential weight
  have hexpm : ∀ t ∈ Icc (0 : ℝ) 1,
      AEStronglyMeasurable (fun x => Complex.exp (S.WoneC C 1 x + S.WtwoC C g t x)) S.nuFl := by
    intro t ht
    have hmeas : Measurable fun x => ∑ y, ∑ i, g y i * S.mcompCT C g y i t x - c := by
      refine Measurable.sub ?_ measurable_const
      refine Finset.measurable_sum _ fun y _ => Finset.measurable_sum _ fun i _ => ?_
      exact measurable_const.mul ((hMC y i).measurable t (hIcc y i ht))
    have hae : (fun x => ∑ y, ∑ i, g y i * S.mcompCT C g y i t x - c) =ᵐ[S.nuFl]
        fun x => S.WtwoC C g t x := by
      filter_upwards [hball] with x hx
      rw [hWt]
      simp only [hmT _ _ _ _ hx]
    have hW2m : AEStronglyMeasurable (fun x => S.WtwoC C g t x) S.nuFl :=
      hmeas.aestronglyMeasurable.congr hae
    exact Complex.continuous_exp.comp_aestronglyMeasurable (hW1m.add hW2m)
  have hexpb : ∀ t ∈ Icc (0 : ℝ) 1, ∀ᵐ x ∂S.nuFl,
      ‖Complex.exp (S.WoneC C 1 x + S.WtwoC C g t x)‖ ≤ Real.exp (M₁ + M₂) := by
    intro t ht
    filter_upwards [hB, hball] with x hx hx1
    rw [Complex.norm_exp]
    refine Real.exp_le_exp.2 ?_
    refine (Complex.re_le_norm _).trans ((norm_add_le _ _).trans (add_le_add ?_ ?_))
    · exact hM₁ x hx
    · exact hW2b x hx1 t ht
  have hexpc : ∀ᵐ x ∂S.nuFl, ContinuousOn (fun t => Complex.exp (S.WoneC C 1 x + S.WtwoC C g t x))
      (Icc (0 : ℝ) 1) := by
    filter_upwards [hball] with x hx
    refine Complex.continuous_exp.comp_continuousOn (continuousOn_const.add ?_)
    exact fun t ht => (hderW x hx t ht).continuousAt.continuousWithinAt
  -- continuity of weighted integrals
  have key : ∀ (f : ℝ → S.E → ℂ) (Mf : ℝ),
      (∀ t ∈ Icc (0 : ℝ) 1, AEStronglyMeasurable (f t) S.nuFl) →
      (∀ t ∈ Icc (0 : ℝ) 1, ∀ᵐ x ∂S.nuFl, ‖f t x‖ ≤ Mf) →
      (∀ᵐ x ∂S.nuFl, ContinuousOn (fun t => f t x) (Icc (0 : ℝ) 1)) →
      ContinuousOn (fun t => ∫ x, f t x * Complex.exp (S.WoneC C 1 x + S.WtwoC C g t x) ∂S.nuFl)
        (Icc (0 : ℝ) 1) := by
    intro f Mf hfm hfb hfc
    refine continuousOn_integral_param' (M := Mf * Real.exp (M₁ + M₂)) (fun t ht => ?_)
      (fun t ht => ?_) ?_
    · exact (hfm t ht).mul (hexpm t ht)
    · filter_upwards [hfb t ht, hexpb t ht] with x h1 h2
      rw [norm_mul]
      exact mul_le_mul h1 h2 (norm_nonneg _) ((norm_nonneg _).trans h1)
    · filter_upwards [hfc, hexpc] with x h1 h2
      exact h1.mul h2
  have hZc : ContinuousOn (fun t => S.ZstC C g 1 t) (Icc (0 : ℝ) 1) := by
    have := key (fun _ _ => 1) 1 (fun _ _ => aestronglyMeasurable_const)
      (fun _ _ => Filter.Eventually.of_forall fun _ => by simp)
      (Filter.Eventually.of_forall fun _ => continuousOn_const)
    simpa [ZstC, partFun₂] using this
  have hZ : ∀ t ∈ Icc (0 : ℝ) 1, S.ZstC C g 1 t ≠ 0 := hnv.seg2
  have hNc : ∀ y i, ContinuousOn (fun t =>
      ∫ x, M' y i t x * Complex.exp (S.WoneC C 1 x + S.WtwoC C g t x) ∂S.nuFl) (Icc (0 : ℝ) 1) := by
    intro y i
    refine key (M' y i) (Mb y i) (fun t ht => ?_) (fun t ht => ?_) ?_
    · exact ((hMC y i).measurable' t (hIcc y i ht)).aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun x => ((hMb y i) x t (hIcc y i ht)).2
    · filter_upwards [hball] with x hx
      exact (hMC y i).continuousOn x
  -- the averages
  have havg : ∀ y i, ContinuousOn (fun t =>
      avgFun₂ S.nuFl (S.WoneC C) (S.WtwoC C g) (M' y i t) 1 t) (Icc (0 : ℝ) 1) := fun y i =>
    (hNc y i).div hZc hZ
  have hint : ∀ y i, ∀ t ∈ Icc (0 : ℝ) 1,
      Integrable (fun x => M' y i t x * Complex.exp (S.WoneC C 1 x + S.WtwoC C g t x)) S.nuFl := by
    intro y i t ht
    refine Integrable.of_bound (C := Mb y i * Real.exp (M₁ + M₂)) ?_ ?_
    · exact (((hMC y i).measurable' t (hIcc y i ht)).aestronglyMeasurable).mul (hexpm t ht)
    · filter_upwards [hexpb t ht] with x h2
      rw [norm_mul]
      exact mul_le_mul (((hMb y i) x t (hIcc y i ht)).2) h2 (norm_nonneg _)
        ((norm_nonneg _).trans (((hMb y i) x t (hIcc y i ht)).2))
  have hpt : ∀ t ∈ Icc (0 : ℝ) 1,
      avgFun₂ S.nuFl (S.WoneC C) (S.WtwoC C g) (fun x => deriv (fun r => S.WtwoC C g r x) t) 1 t =
        ∑ y, ∑ i, g y i * avgFun₂ S.nuFl (S.WoneC C) (S.WtwoC C g) (M' y i t) 1 t := by
    intro t ht
    unfold avgFun₂
    simp only [← mul_div_assoc, ← Finset.sum_div]
    congr 1
    have e1 : ∀ y, Integrable (fun x => ∑ i, g y i *
        (M' y i t x * Complex.exp (S.WoneC C 1 x + S.WtwoC C g t x))) S.nuFl := fun y =>
      integrable_finsetSum _ fun i _ => (hint y i t ht).const_mul _
    rw [show (∑ y, ∑ i, g y i * ∫ x, M' y i t x * Complex.exp (S.WoneC C 1 x + S.WtwoC C g t x)
          ∂S.nuFl) = ∑ y, ∑ i, ∫ x, g y i *
          (M' y i t x * Complex.exp (S.WoneC C 1 x + S.WtwoC C g t x)) ∂S.nuFl from
        Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun i _ =>
          (integral_const_mul _ _).symm]
    rw [show (∑ y, ∑ i, ∫ x, g y i *
          (M' y i t x * Complex.exp (S.WoneC C 1 x + S.WtwoC C g t x)) ∂S.nuFl) =
        ∑ y, ∫ x, ∑ i, g y i *
          (M' y i t x * Complex.exp (S.WoneC C 1 x + S.WtwoC C g t x)) ∂S.nuFl from
        Finset.sum_congr rfl fun y _ =>
          (integral_finsetSum _ fun i _ => (hint y i t ht).const_mul _).symm]
    rw [← integral_finsetSum _ (fun y _ => e1 y)]
    refine integral_congr_ae ?_
    filter_upwards [hball] with x hx
    rw [(hderW x hx t ht).deriv, Finset.sum_mul]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  -- the derivative of `ℳ` is the family `M'`
  have hdm : ∀ y i, ∀ t ∈ Icc (0 : ℝ) 1,
      avgFun₂ S.nuFl (S.WoneC C) (S.WtwoC C g)
        (fun x => deriv (fun r => McompAtC C.m₀ C.Tm S.a S.ν (Nat.le_succ k)
          (S.dataUC (S.psiAtC r x)) g y i) t) 1 t =
        avgFun₂ S.nuFl (S.WoneC C) (S.WtwoC C g) (M' y i t) 1 t := by
    intro y i t ht
    unfold avgFun₂
    congr 1
    refine integral_congr_ae ?_
    filter_upwards [hball] with x hx
    rw [(hder y i x hx t ht).deriv]
  -- assemble
  have hβU : 0 < S.betaU := S.betaU_pos' (Nat.pos_of_ne_zero (NeZero.ne L)) hβ
  have hr : S.betaU ^ (-(1 / 2 : ℝ)) * S.betaU ^ (1 / 2 : ℝ) = 1 := by
    rw [← Real.rpow_add hβU]; norm_num
  unfold F0C
  rw [intervalIntegral.integral_congr (g := fun t => ∑ y, ∑ i, g y i *
      avgFun₂ S.nuFl (S.WoneC C) (S.WtwoC C g) (M' y i t) 1 t) (fun t ht => by
    rw [Set.uIcc_of_le zero_le_one] at ht; exact hpt t ht)]
  have hii : ∀ y i, IntervalIntegrable (fun t =>
      avgFun₂ S.nuFl (S.WoneC C) (S.WtwoC C g) (M' y i t) 1 t) MeasureTheory.volume 0 1 :=
    fun y i => (havg y i).intervalIntegrable_of_Icc zero_le_one
  have hsumII : ∀ y : CTorus d L N₁ m₁ (k + 1), IntervalIntegrable (fun t => ∑ i : Fin N, g y i *
      avgFun₂ S.nuFl (S.WoneC C) (S.WtwoC C g) (M' y i t) 1 t) MeasureTheory.volume 0 1 := by
    intro y
    have := IntervalIntegrable.sum (Finset.univ : Finset (Fin N))
      (f := fun i t => g y i * avgFun₂ S.nuFl (S.WoneC C) (S.WtwoC C g) (M' y i t) 1 t)
      (μ := MeasureTheory.volume) (a := 0) (b := 1) (fun i _ => (hii y i).const_mul _)
    convert this using 1
    ext t
    simp [Finset.sum_apply]
  rw [intervalIntegral.integral_finsetSum fun y _ => hsumII y]
  simp only [intervalIntegral.integral_finsetSum fun i _ => (hii _ i).const_mul _,
    intervalIntegral.integral_const_mul]
  unfold M0C
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hI : (∫ t in (0 : ℝ)..1, avgFun₂ S.nuFl (S.WoneC C) (S.WtwoC C g)
        (fun x => deriv (fun r => McompAtC C.m₀ C.Tm S.a S.ν (Nat.le_succ k)
          (S.dataUC (S.psiAtC r x)) g y i) t) 1 t) =
      ∫ t in (0 : ℝ)..1, avgFun₂ S.nuFl (S.WoneC C) (S.WtwoC C g) (M' y i t) 1 t :=
    intervalIntegral.integral_congr fun t ht => by
      rw [Set.uIcc_of_le zero_le_one] at ht; exact hdm y i t ht
  rw [hI]
  have h1 : ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * ((S.betaU ^ (1 / 2 : ℝ) : ℝ) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, hr, Complex.ofReal_one]
  linear_combination (-(g y i) * ∫ t in (0 : ℝ)..1, avgFun₂ S.nuFl (S.WoneC C) (S.WtwoC C g)
    (M' y i t) 1 t) * h1

end StepSetting

end Balaban.Fluctuation
