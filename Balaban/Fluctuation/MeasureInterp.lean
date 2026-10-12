/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The interpolation identities (FLUCTUATION.md §2.6, Proposition 2.6, abstract form)

For a probability measure `ν` and bounded measurable exponents `W(s, ·)` that are `C¹` in the
parameter `s` (derivative `W'`, bounded and continuous in `s` on `[0,1]`), put
`Z(s) = ∫ exp (W s ω) dν` and `⟨f⟩_s = Z(s)⁻¹ ∫ f exp (W s ω) dν`.

* `Z_one_eq_Z_zero_mul_cexp_integral_avg`: if `Z ≠ 0` on `[0,1]` then
  `Z(1) = Z(0) exp (∫₀¹ ⟨W'⟩_s ds)`: the integral is a continuous lift of the logarithm along the
  path (the analytic branch of the logarithm, wherever the path of `Z` lies in a region where
  a branch exists, is then `log Z(0) + ∫₀¹ ⟨W'⟩_s ds` up to `2πi ℤ`; see
  `log_Z_one_sub_log_Z_zero` for the slit-plane case).
* `real_log_Z_one_sub_log_Z_zero`: the real case, `log Z(1) - log Z(0) = ∫₀¹ ⟨W'⟩_s ds`.
* `log_Zst_one_one_sub_log_Zst_zero_zero`, `real_log_Zst_one_one_sub_log_Zst_zero_zero`: the
  two-parameter identity `log Z_{1,1} - log Z_{0,0} = ∫₀¹ ⟨∂_s W₁⟩_{s,0} ds + ∫₀¹ ⟨∂_t W₂⟩_{1,t} dt`
  of Proposition 2.6.
-/

@[expose] public section

namespace Balaban.Fluctuation

open MeasureTheory Set Filter Topology intervalIntegral
open scoped Real

variable {Ω : Type*} [MeasurableSpace Ω]

/-- A bounded measurable family of exponents `W(s, ·)` on the open set `U ⊇ [0,1]`, `C¹` in `s`
with derivative `W'` (bounded, continuous in `s` on `[0,1]`). -/
structure IsC1Family (U : Set ℝ) (W W' : ℝ → Ω → ℂ) : Prop where
  isOpen : IsOpen U
  Icc_subset : Icc (0 : ℝ) 1 ⊆ U
  measurable : ∀ s ∈ U, Measurable (W s)
  measurable' : ∀ s ∈ U, Measurable (W' s)
  hasDerivAt : ∀ ω, ∀ s ∈ U, HasDerivAt (fun r => W r ω) (W' s ω) s
  continuousOn : ∀ ω, ContinuousOn (fun s => W' s ω) (Icc 0 1)
  bound : ∃ M : ℝ, ∀ ω, ∀ s ∈ U, ‖W s ω‖ ≤ M ∧ ‖W' s ω‖ ≤ M

/-- The partition function `Z(s) = ∫ exp (W s ω) dν`. -/
noncomputable def partFun (ν : Measure Ω) (W : ℝ → Ω → ℂ) (s : ℝ) : ℂ :=
  ∫ ω, Complex.exp (W s ω) ∂ν

/-- The expectation `⟨f⟩_s = Z(s)⁻¹ ∫ f exp (W s) dν` in the interpolating measure. -/
noncomputable def avgFun (ν : Measure Ω) (W : ℝ → Ω → ℂ) (f : Ω → ℂ) (s : ℝ) : ℂ :=
  (∫ ω, f ω * Complex.exp (W s ω) ∂ν) / partFun ν W s

section Core

variable {ν : Measure Ω} [IsProbabilityMeasure ν] {U : Set ℝ} {W W' : ℝ → Ω → ℂ}

private theorem norm_cexp_le {z : ℂ} {M : ℝ} (h : ‖z‖ ≤ M) : ‖Complex.exp z‖ ≤ Real.exp M := by
  rw [Complex.norm_exp]
  exact Real.exp_le_exp.2 ((Complex.re_le_norm z).trans h)

theorem IsC1Family.hasDerivAt_partFun (h : IsC1Family U W W') {s : ℝ} (hs : s ∈ U) :
    HasDerivAt (partFun ν W) (∫ ω, W' s ω * Complex.exp (W s ω) ∂ν) s := by
  obtain ⟨M, hM⟩ := h.bound
  have hU : U ∈ 𝓝 s := h.isOpen.mem_nhds hs
  have hmeas : ∀ x ∈ U, AEStronglyMeasurable (fun ω => Complex.exp (W x ω)) ν := fun x hx =>
    (Complex.measurable_exp.comp (h.measurable x hx)).aestronglyMeasurable
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := ν)
    (F := fun x ω => Complex.exp (W x ω)) (x₀ := s) (s := U)
    (F' := fun x ω => W' x ω * Complex.exp (W x ω)) (bound := fun _ => Real.exp M * M) hU
    (Filter.eventually_of_mem hU hmeas)
    (Integrable.of_bound (hmeas s hs) (Real.exp M) (ae_of_all _ fun ω =>
      norm_cexp_le (hM ω s hs).1))
    (((h.measurable' s hs).mul
      (Complex.measurable_exp.comp (h.measurable s hs))).aestronglyMeasurable)
    (ae_of_all _ fun ω x hx => by
      rw [norm_mul]
      rw [mul_comm]
      exact mul_le_mul (norm_cexp_le (hM ω x hx).1) (hM ω x hx).2 (norm_nonneg _)
        (Real.exp_pos M).le)
    (integrable_const _)
    (ae_of_all _ fun ω x hx => ((Complex.hasDerivAt_exp (W x ω)).scomp x (h.hasDerivAt ω x hx)))
  exact key.2

theorem IsC1Family.continuousAt_partFun (h : IsC1Family U W W') {s : ℝ} (hs : s ∈ U) :
    ContinuousAt (partFun ν W) s :=
  (h.hasDerivAt_partFun hs).continuousAt

theorem IsC1Family.continuousOn_partFun' (h : IsC1Family U W W') :
    ContinuousOn (fun s => ∫ ω, W' s ω * Complex.exp (W s ω) ∂ν) (Icc 0 1) := by
  obtain ⟨M, hM⟩ := h.bound
  refine continuousOn_of_dominated (bound := fun _ => M * Real.exp M) ?_ ?_ (integrable_const _) ?_
  · intro x hx
    exact (((h.measurable' x (h.Icc_subset hx)).mul
      (Complex.measurable_exp.comp (h.measurable x (h.Icc_subset hx)))).aestronglyMeasurable)
  · intro x hx
    refine ae_of_all _ fun ω => ?_
    rw [norm_mul]
    exact mul_le_mul (hM ω x (h.Icc_subset hx)).2 (norm_cexp_le (hM ω x (h.Icc_subset hx)).1)
      (norm_nonneg _) ((norm_nonneg _).trans (hM ω x (h.Icc_subset hx)).2)
  · refine ae_of_all _ fun ω => ?_
    refine (h.continuousOn ω).mul ?_
    intro x hx
    exact ((h.hasDerivAt ω x (h.Icc_subset hx)).continuousAt.cexp).continuousWithinAt

/-- **Interpolation identity, exponential form.**  If `Z(s) ≠ 0` for `s ∈ [0,1]`, then
`Z(1) = Z(0) exp (∫₀¹ ⟨W'⟩_s ds)`. -/
theorem IsC1Family.partFun_one_eq (h : IsC1Family U W W')
    (hZ : ∀ s ∈ Icc (0 : ℝ) 1, partFun ν W s ≠ 0) :
    partFun ν W 1 = partFun ν W 0 *
      Complex.exp (∫ s in (0 : ℝ)..1, avgFun ν W (W' s) s) := by
  set g : ℝ → ℂ := fun s => avgFun ν W (W' s) s with hg
  have hZcont : ContinuousOn (partFun ν W) (Icc 0 1) := fun s hs =>
    (h.continuousAt_partFun (h.Icc_subset hs)).continuousWithinAt
  have hgcont : ContinuousOn g (Icc 0 1) :=
    h.continuousOn_partFun'.div hZcont hZ
  set gt : ℝ → ℂ := fun s => g (Set.projIcc (0 : ℝ) 1 zero_le_one s) with hgt
  have hgtc : Continuous gt :=
    hgcont.comp_continuous (continuous_subtype_val.comp continuous_projIcc) (fun s => (Set.projIcc (0 : ℝ) 1 zero_le_one s).2)
  set Λ : ℝ → ℂ := fun u => ∫ x in (0 : ℝ)..u, gt x with hΛ
  have hΛd : ∀ s, HasDerivAt Λ (gt s) s := fun s => (hgtc.integral_hasStrictDerivAt 0 s).hasDerivAt
  set F : ℝ → ℂ := fun s => partFun ν W s * Complex.exp (-Λ s) with hF
  have hFd : ∀ s ∈ Icc (0 : ℝ) 1, HasDerivAt F 0 s := by
    intro s hs
    have h1 := h.hasDerivAt_partFun (ν := ν) (h.Icc_subset hs)
    have h2 := (Complex.hasDerivAt_exp (-Λ s)).scomp s (hΛd s).neg
    have h3 : HasDerivAt F _ s := h1.mul h2
    refine h3.congr_deriv ?_
    have hgs : gt s = g s := by
      simp only [hgt]
      rw [Set.projIcc_of_mem _ hs]
    have : gt s = (∫ ω, W' s ω * Complex.exp (W s ω) ∂ν) / partFun ν W s := by
      rw [hgs]; rfl
    have hz := hZ s hs
    rw [this]
    simp only [smul_eq_mul]
    field_simp
    ring
  have hconst := constant_of_derivWithin_zero
    (f := F) (a := 0) (b := 1)
    (fun s hs => (hFd s hs).differentiableAt.differentiableWithinAt)
    (fun s hs => by
      rw [(hFd s (Ico_subset_Icc_self hs)).hasDerivWithinAt.derivWithin
        (uniqueDiffOn_Icc zero_lt_one s (Ico_subset_Icc_self hs))])
    1 (right_mem_Icc.2 zero_le_one)
  have hΛ0 : Λ 0 = 0 := by simp [hΛ]
  have hF0 : F 0 = partFun ν W 0 := by simp [hF, hΛ0]
  have hΛ1 : Λ 1 = ∫ s in (0 : ℝ)..1, g s := by
    simp only [hΛ]
    refine intervalIntegral.integral_congr fun x hx => ?_
    rw [uIcc_of_le zero_le_one] at hx
    simp only [hgt]
    rw [Set.projIcc_of_mem _ hx]
  rw [hF0] at hconst
  simp only [hF] at hconst
  have : partFun ν W 1 = partFun ν W 0 * Complex.exp (Λ 1) := by
    rw [← hconst, mul_assoc, ← Complex.exp_add]
    simp
  rw [this, hΛ1]


/-- Complex logarithm along the path, when `Z` stays in the slit plane (so that `Complex.log` is
the analytic branch): `log Z(1) - log Z(0) = ∫₀¹ ⟨W'⟩_s ds`. -/
theorem IsC1Family.log_partFun_one_sub (h : IsC1Family U W W')
    (hZ : ∀ s ∈ Icc (0 : ℝ) 1, partFun ν W s ∈ Complex.slitPlane) :
    Complex.log (partFun ν W 1) - Complex.log (partFun ν W 0) =
      ∫ s in (0 : ℝ)..1, avgFun ν W (W' s) s := by
  have hZcont : ContinuousOn (partFun ν W) (Icc 0 1) := fun s hs =>
    (h.continuousAt_partFun (h.Icc_subset hs)).continuousWithinAt
  have hne : ∀ s ∈ Icc (0 : ℝ) 1, partFun ν W s ≠ 0 := fun s hs =>
    Complex.slitPlane_ne_zero (hZ s hs)
  have hgcont : ContinuousOn (fun s => avgFun ν W (W' s) s) (Icc 0 1) :=
    h.continuousOn_partFun'.div hZcont hne
  have := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun s => Complex.log (partFun ν W s)) (f' := fun s => avgFun ν W (W' s) s)
    (a := 0) (b := 1)
    (fun s hs => by
      rw [uIcc_of_le zero_le_one] at hs
      exact HasDerivAt.clog_real (h.hasDerivAt_partFun (ν := ν) (h.Icc_subset hs)) (hZ s hs))
    (hgcont.intervalIntegrable_of_Icc zero_le_one)
  exact this.symm

end Core

section TwoParameter

variable {ν : Measure Ω} [IsProbabilityMeasure ν] {U : Set ℝ} {W₁ W₁' W₂ W₂' : ℝ → Ω → ℂ}

/-- `Z_{s,t} = ∫ exp (W₁(s,·) + W₂(t,·)) dν`. -/
noncomputable def partFun₂ (ν : Measure Ω) (W₁ W₂ : ℝ → Ω → ℂ) (s t : ℝ) : ℂ :=
  ∫ ω, Complex.exp (W₁ s ω + W₂ t ω) ∂ν

/-- `⟨f⟩_{s,t} = Z_{s,t}⁻¹ ∫ f exp (W₁(s,·) + W₂(t,·)) dν`. -/
noncomputable def avgFun₂ (ν : Measure Ω) (W₁ W₂ : ℝ → Ω → ℂ) (f : Ω → ℂ) (s t : ℝ) : ℂ :=
  (∫ ω, f ω * Complex.exp (W₁ s ω + W₂ t ω) ∂ν) / partFun₂ ν W₁ W₂ s t

theorem IsC1Family.add_const (h : IsC1Family U W₁ W₁') (c : Ω → ℂ) (hc : Measurable c)
    (M : ℝ) (hM : ∀ ω, ‖c ω‖ ≤ M) :
    IsC1Family U (fun s ω => W₁ s ω + c ω) W₁' where
  isOpen := h.isOpen
  Icc_subset := h.Icc_subset
  measurable s hs := (h.measurable s hs).add hc
  measurable' := h.measurable'
  hasDerivAt ω s hs := (h.hasDerivAt ω s hs).add_const (c ω)
  continuousOn := h.continuousOn
  bound := by
    obtain ⟨M₁, hM₁⟩ := h.bound
    refine ⟨max (M₁ + M) M₁, fun ω s hs => ⟨?_, ?_⟩⟩
    · exact ((norm_add_le _ _).trans (add_le_add (hM₁ ω s hs).1 (hM ω))).trans (le_max_left _ _)
    · exact (hM₁ ω s hs).2.trans (le_max_right _ _)

theorem IsC1Family.const_add (h : IsC1Family U W₁ W₁') (c : Ω → ℂ) (hc : Measurable c)
    (M : ℝ) (hM : ∀ ω, ‖c ω‖ ≤ M) :
    IsC1Family U (fun s ω => c ω + W₁ s ω) W₁' := by
  have := h.add_const c hc M hM
  simpa only [add_comm] using this

/-- **Proposition 2.6 (interpolation identity), exponential form.**
`Z_{1,1} = Z_{0,0} exp (∫₀¹ ⟨∂_s W₁⟩_{s,0} ds + ∫₀¹ ⟨∂_t W₂⟩_{1,t} dt)` when `Z_{s,0} ≠ 0` and
`Z_{1,t} ≠ 0` on `[0,1]`. -/
theorem partFun₂_one_one_eq (h₁ : IsC1Family U W₁ W₁') (h₂ : IsC1Family U W₂ W₂')
    (hZ₁ : ∀ s ∈ Icc (0 : ℝ) 1, partFun₂ ν W₁ W₂ s 0 ≠ 0)
    (hZ₂ : ∀ t ∈ Icc (0 : ℝ) 1, partFun₂ ν W₁ W₂ 1 t ≠ 0) :
    partFun₂ ν W₁ W₂ 1 1 = partFun₂ ν W₁ W₂ 0 0 *
      Complex.exp ((∫ s in (0 : ℝ)..1, avgFun₂ ν W₁ W₂ (W₁' s) s 0) +
        ∫ t in (0 : ℝ)..1, avgFun₂ ν W₁ W₂ (W₂' t) 1 t) := by
  have h0 : (0 : ℝ) ∈ U := h₂.Icc_subset ⟨le_rfl, zero_le_one⟩
  have h1 : (1 : ℝ) ∈ U := h₁.Icc_subset ⟨zero_le_one, le_rfl⟩
  obtain ⟨M₂, hM₂⟩ := h₂.bound
  obtain ⟨M₁, hM₁⟩ := h₁.bound
  have hA := h₁.add_const (W₂ 0) (h₂.measurable 0 h0) M₂ (fun ω => (hM₂ ω 0 h0).1)
  have hB := h₂.const_add (W₁ 1) (h₁.measurable 1 h1) M₁ (fun ω => (hM₁ ω 1 h1).1)
  have eA := hA.partFun_one_eq (ν := ν) hZ₁
  have eB := hB.partFun_one_eq (ν := ν) hZ₂
  simp only [partFun, avgFun, partFun₂, avgFun₂] at eA eB ⊢
  rw [eB, eA, Complex.exp_add]
  ring

/-- **Proposition 2.6, analytic-branch form.**  If the paths `s ↦ Z_{s,0}` and `t ↦ Z_{1,t}` stay in
the slit plane, then `log Z_{1,1} - log Z_{0,0}` (principal branch) is the sum of the two
integrals. -/
theorem log_partFun₂_one_one_sub (h₁ : IsC1Family U W₁ W₁') (h₂ : IsC1Family U W₂ W₂')
    (hZ₁ : ∀ s ∈ Icc (0 : ℝ) 1, partFun₂ ν W₁ W₂ s 0 ∈ Complex.slitPlane)
    (hZ₂ : ∀ t ∈ Icc (0 : ℝ) 1, partFun₂ ν W₁ W₂ 1 t ∈ Complex.slitPlane) :
    Complex.log (partFun₂ ν W₁ W₂ 1 1) - Complex.log (partFun₂ ν W₁ W₂ 0 0) =
      (∫ s in (0 : ℝ)..1, avgFun₂ ν W₁ W₂ (W₁' s) s 0) +
        ∫ t in (0 : ℝ)..1, avgFun₂ ν W₁ W₂ (W₂' t) 1 t := by
  have h0 : (0 : ℝ) ∈ U := h₂.Icc_subset ⟨le_rfl, zero_le_one⟩
  have h1 : (1 : ℝ) ∈ U := h₁.Icc_subset ⟨zero_le_one, le_rfl⟩
  obtain ⟨M₂, hM₂⟩ := h₂.bound
  obtain ⟨M₁, hM₁⟩ := h₁.bound
  have hA := h₁.add_const (W₂ 0) (h₂.measurable 0 h0) M₂ (fun ω => (hM₂ ω 0 h0).1)
  have hB := h₂.const_add (W₁ 1) (h₁.measurable 1 h1) M₁ (fun ω => (hM₁ ω 1 h1).1)
  have eA := hA.log_partFun_one_sub (ν := ν) hZ₁
  have eB := hB.log_partFun_one_sub (ν := ν) hZ₂
  simp only [partFun, avgFun, partFun₂, avgFun₂] at eA eB ⊢
  rw [← eA, ← eB]
  ring

end TwoParameter

section Real

variable {ν : Measure Ω} [IsProbabilityMeasure ν] {U : Set ℝ} {W₁ W₁' W₂ W₂' : ℝ → Ω → ℝ}

/-- Real-valued version of `IsC1Family`. -/
structure IsC1FamilyR (U : Set ℝ) (W W' : ℝ → Ω → ℝ) : Prop where
  isOpen : IsOpen U
  Icc_subset : Icc (0 : ℝ) 1 ⊆ U
  measurable : ∀ s ∈ U, Measurable (W s)
  measurable' : ∀ s ∈ U, Measurable (W' s)
  hasDerivAt : ∀ ω, ∀ s ∈ U, HasDerivAt (fun r => W r ω) (W' s ω) s
  continuousOn : ∀ ω, ContinuousOn (fun s => W' s ω) (Icc 0 1)
  bound : ∃ M : ℝ, ∀ ω, ∀ s ∈ U, |W s ω| ≤ M ∧ |W' s ω| ≤ M

theorem IsC1FamilyR.toComplex (h : IsC1FamilyR U W₁ W₁') :
    IsC1Family U (fun s ω => (W₁ s ω : ℂ)) (fun s ω => (W₁' s ω : ℂ)) where
  isOpen := h.isOpen
  Icc_subset := h.Icc_subset
  measurable s hs := Complex.measurable_ofReal.comp (h.measurable s hs)
  measurable' s hs := Complex.measurable_ofReal.comp (h.measurable' s hs)
  hasDerivAt ω s hs := (h.hasDerivAt ω s hs).ofReal_comp
  continuousOn ω := Complex.continuous_ofReal.comp_continuousOn (h.continuousOn ω)
  bound := by
    obtain ⟨M, hM⟩ := h.bound
    exact ⟨M, fun ω s hs => by simpa using hM ω s hs⟩

/-- Real partition function `Z_{s,t} = ∫ exp (W₁(s,·) + W₂(t,·)) dν`. -/
noncomputable def partFunR₂ (ν : Measure Ω) (W₁ W₂ : ℝ → Ω → ℝ) (s t : ℝ) : ℝ :=
  ∫ ω, Real.exp (W₁ s ω + W₂ t ω) ∂ν

/-- Real expectation `⟨f⟩_{s,t}`. -/
noncomputable def avgFunR₂ (ν : Measure Ω) (W₁ W₂ : ℝ → Ω → ℝ) (f : Ω → ℝ) (s t : ℝ) : ℝ :=
  (∫ ω, f ω * Real.exp (W₁ s ω + W₂ t ω) ∂ν) / partFunR₂ ν W₁ W₂ s t

theorem partFunR₂_pos (h₁ : IsC1FamilyR U W₁ W₁') (h₂ : IsC1FamilyR U W₂ W₂') {s t : ℝ}
    (hs : s ∈ U) (ht : t ∈ U) : 0 < partFunR₂ ν W₁ W₂ s t := by
  obtain ⟨M₁, hM₁⟩ := h₁.bound
  obtain ⟨M₂, hM₂⟩ := h₂.bound
  refine integral_exp_pos (Integrable.of_bound (C := Real.exp (M₁ + M₂)) ?_ ?_)
  · exact (Real.measurable_exp.comp ((h₁.measurable s hs).add (h₂.measurable t ht))).aestronglyMeasurable
  · refine ae_of_all _ fun ω => ?_
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    refine Real.exp_le_exp.2 ?_
    have := (hM₁ ω s hs).1
    have := (hM₂ ω t ht).1
    have := le_abs_self (W₁ s ω)
    have := le_abs_self (W₂ t ω)
    linarith

omit [IsProbabilityMeasure ν] in
theorem partFun₂_ofReal (W₁ W₂ : ℝ → Ω → ℝ) (s t : ℝ) :
    partFun₂ ν (fun s ω => (W₁ s ω : ℂ)) (fun s ω => (W₂ s ω : ℂ)) s t =
      (partFunR₂ ν W₁ W₂ s t : ℂ) := by
  simp only [partFun₂, partFunR₂]
  refine Eq.trans (integral_congr_ae (g := fun ω => ((Real.exp (W₁ s ω + W₂ t ω) : ℝ) : ℂ))
    (ae_of_all _ fun ω => by simp [Complex.ofReal_exp])) ?_
  exact integral_complex_ofReal

omit [IsProbabilityMeasure ν] in
theorem avgFun₂_ofReal (W₁ W₂ : ℝ → Ω → ℝ) (f : Ω → ℝ) (s t : ℝ) :
    avgFun₂ ν (fun s ω => (W₁ s ω : ℂ)) (fun s ω => (W₂ s ω : ℂ)) (fun ω => (f ω : ℂ)) s t =
      (avgFunR₂ ν W₁ W₂ f s t : ℂ) := by
  simp only [avgFun₂, avgFunR₂]
  rw [partFun₂_ofReal, Complex.ofReal_div]
  congr 1
  refine Eq.trans (integral_congr_ae
    (g := fun ω => ((f ω * Real.exp (W₁ s ω + W₂ t ω) : ℝ) : ℂ))
    (ae_of_all _ fun ω => by simp [Complex.ofReal_exp])) ?_
  exact integral_complex_ofReal

/-- **Proposition 2.6 (interpolation identity), real case.**
`log Z_{1,1} - log Z_{0,0} = ∫₀¹ ⟨∂_s W₁⟩_{s,0} ds + ∫₀¹ ⟨∂_t W₂⟩_{1,t} dt`. -/
theorem log_partFunR₂_one_one_sub (h₁ : IsC1FamilyR U W₁ W₁') (h₂ : IsC1FamilyR U W₂ W₂') :
    Real.log (partFunR₂ ν W₁ W₂ 1 1) - Real.log (partFunR₂ ν W₁ W₂ 0 0) =
      (∫ s in (0 : ℝ)..1, avgFunR₂ ν W₁ W₂ (W₁' s) s 0) +
        ∫ t in (0 : ℝ)..1, avgFunR₂ ν W₁ W₂ (W₂' t) 1 t := by
  have h0 : (0 : ℝ) ∈ U := h₂.Icc_subset ⟨le_rfl, zero_le_one⟩
  have h1 : (1 : ℝ) ∈ U := h₁.Icc_subset ⟨zero_le_one, le_rfl⟩
  have hpos : ∀ {s t : ℝ}, s ∈ U → t ∈ U → 0 < partFunR₂ ν W₁ W₂ s t :=
    fun hs ht => partFunR₂_pos h₁ h₂ hs ht
  have e := partFun₂_one_one_eq (ν := ν) h₁.toComplex h₂.toComplex
    (fun s hs => by
      rw [partFun₂_ofReal]
      exact_mod_cast (hpos (h₁.Icc_subset hs) h0).ne')
    (fun t ht => by
      rw [partFun₂_ofReal]
      exact_mod_cast (hpos h1 (h₂.Icc_subset ht)).ne')
  simp only [partFun₂_ofReal, avgFun₂_ofReal] at e
  rw [intervalIntegral.integral_ofReal, intervalIntegral.integral_ofReal, ← Complex.ofReal_add,
    ← Complex.ofReal_exp, ← Complex.ofReal_mul] at e
  have e' := Complex.ofReal_injective e
  have hz0 := hpos h0 h0
  rw [e', Real.log_mul hz0.ne' (Real.exp_pos _).ne', Real.log_exp]
  ring

end Real

end Balaban.Fluctuation
