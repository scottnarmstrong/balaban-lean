/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.Thm31CoeffAnalytic
public import Balaban.Fluctuation.Thm31bFirst
public import Balaban.Fluctuation.Thm31bResum
public import Balaban.Fluctuation.Thm31CoeffB
import Mathlib.Tactic.Linarith

/-!
# Parameter analyticity of the first-order term `markIntTerm` and of the kernel sum

For activities `A θ t σ` and a first-order mark `G θ` depending on a parameter `θ` of a
finite-dimensional complex space, the `t`-integrated local term
`E(S) = ∫₀¹ G*(Y₀,S)(t, σ = 1) dt` (`markIntTerm`) is analytic in `θ` on an open set `V`
(`markIntTerm_analyticOnNhd`), bounded uniformly in `θ` with the constant of the fixed-parameter
bound (`norm_markIntTerm_le`), and local in the parameter (`markIntTerm_param_congr_of_local`).
The resummed kernel sum `kernelMarkSum` of analytic kernels and analytic first-order terms is
analytic in `θ` (`kernelMarkSum_analyticOnNhd`), with the uniform bound of `kernel_mark_resum`
(`norm_kernelMarkSum_le`).

The regularity hypothesis is `ParamMarkFamily` for the activities `fun θ t => A θ t 1`, the single
label `y0` and the marks `fun θ _ _ => G θ` (which do not depend on `t`).
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Localization Balaban.Polymer MeasureTheory

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {m₀ j : ℕ} {Ω : Set (CTorus d L N₁ m₁ K)}

local notation "𝔅" => CubeB (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ j Ω

section MarkInt

variable {Lb : Type*} [Fintype Lb] {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

open Classical in
/-- **Analyticity of `markIntTerm` in the parameter `θ ∈ V`.** -/
theorem markIntTerm_analyticOnNhd {Ωb : 𝔅 → Type*} [∀ b, MeasurableSpace (Ωb b)]
    [∀ b, TopologicalSpace (Ωb b)] [∀ b, OpensMeasurableSpace (Ωb b)]
    [∀ b, SecondCountableTopology (Ωb b)] [FiniteDimensional ℂ E]
    (μ : ∀ b, Measure (Ωb b)) [∀ b, IsProbabilityMeasure (μ b)]
    (hN : L ^ m₀ ∣ N₁) (hj : j ≤ K) (hΩ : IsPiUnion m₀ j Ω)
    {Lab : CubeLabels m₀ j Ω Lb} {εH κH κG κ0 κ' Kc F0 : ℝ}
    {A : E → ℂ → ℂ → LabelAct Lab Ωb εH κH κ0 Kc} {y0 : Lb}
    {G : E → (∀ b, Ωb b) → ℂ} {V : Set E} {𝒰 : Set ℂ} {Q : Set (∀ b, Ωb b)}
    (hfam : ParamMarkFamily μ Lab (fun θ t => A θ t 1) (fun _ : Unit => y0)
      (fun θ _ _ => G θ) κG (fun _ => F0) V 𝒰 Q)
    (hκ0 : aEnt d L + 1 ≤ κ0) (hKc : K0 d L κ0 + 1 ≤ Kc) (hεpos : 0 < εH)
    (hF0 : 0 < F0) (hκ' : 0 ≤ κ') (hκG : κH ≤ κG)
    (hκ : κ' + 3 * κ0 + c1 d L + 3 / 2 ≤ κH)
    (hε : εH ≤ 1 / (8 * Kc ^ 3 * c1 d L *
      Real.exp ((κH - 2 * κ0) * cG d L + c1 d L + κ' * cG d L)))
    (S : Finset 𝔅) :
    AnalyticOnNhd ℂ (fun θ => markIntTerm μ (A θ) y0 (G θ) S) V := by
  intro θ0 hθ0
  have hG : AnalyticOnNhd ℂ (fun p : E × ℂ =>
      Gst μ Lab (A p.1 p.2 1).H (blocksOf m₀ j Ω (Lab.ysite y0)) (G p.1) S) (V ×ˢ 𝒰) :=
    (Pst_Gst_analyticOnNhd (E := E × ℂ) μ hN hj hΩ (V := V ×ˢ 𝒰)
      (hfam.isOpenV.prod hfam.isOpenU) hfam.compact hfam.measQ hfam.carried
      (fun p => A p.1 p.2 1) y0 (fun p => G p.1) (fun p => hfam.meas p.1 () p.2)
      (fun p Φ => hfam.bound p.1 () p.2 Φ) (fun y Φ hΦ => hfam.holA y Φ hΦ)
      (fun Φ hΦ => hfam.holG () Φ hΦ) (fun y p hp => hfam.contA y p.1 hp.1 p.2 hp.2)
      (fun p hp => hfam.contG () p.1 hp.1 p.2 hp.2) hκ0 hKc hεpos hF0 hκ' hκG hκ hε S).2
  have hfin : IsFiniteMeasure (volume.restrict (Set.Ioc (0 : ℝ) 1)) :=
    ⟨by rw [Measure.restrict_apply_univ, Real.volume_Ioc]; exact ENNReal.ofReal_lt_top⟩
  have h := Balaban.Analysis.analyticAt_integral_comp (P := E) (V := ℂ) (X := ℝ)
    (μ := volume.restrict (Set.Ioc (0 : ℝ) 1)) (K := Set.Icc (0 : ℝ) 1)
    isCompact_Icc measurableSet_Icc
    (ae_restrict_of_forall_mem measurableSet_Ioc (fun x hx => Set.Ioc_subset_Icc_self hx))
    (ι := fun s : ℝ => (s : ℂ)) Complex.continuous_ofReal.continuousOn
    (G := fun p : E × ℂ =>
      Gst μ Lab (A p.1 p.2 1).H (blocksOf m₀ j Ω (Lab.ysite y0)) (G p.1) S) (Θ₀ := θ0)
    (fun s hs => hG _ ⟨hθ0, hfam.seg s hs⟩)
  unfold markIntTerm
  simp only [intervalIntegral.integral_of_le (zero_le_one' ℝ)]
  exact h

/-- **Analyticity of `markIntTerm` for a parameter-independent first-order mark** (the case of
`blockMark`): the mark `G1` is fixed and only the activities depend on `θ`. -/
theorem markIntTerm_analyticOnNhd_const {Ωb : 𝔅 → Type*} [∀ b, MeasurableSpace (Ωb b)]
    [∀ b, TopologicalSpace (Ωb b)] [∀ b, OpensMeasurableSpace (Ωb b)]
    [∀ b, SecondCountableTopology (Ωb b)] [FiniteDimensional ℂ E]
    (μ : ∀ b, Measure (Ωb b)) [∀ b, IsProbabilityMeasure (μ b)]
    (hN : L ^ m₀ ∣ N₁) (hj : j ≤ K) (hΩ : IsPiUnion m₀ j Ω)
    {Lab : CubeLabels m₀ j Ω Lb} {εH κH κG κ0 κ' Kc F0 : ℝ}
    {A : E → ℂ → ℂ → LabelAct Lab Ωb εH κH κ0 Kc} {y0 : Lb}
    {G1 : (∀ b, Ωb b) → ℂ} {V : Set E} {𝒰 : Set ℂ} {Q : Set (∀ b, Ωb b)}
    (hfam : ParamMarkFamily μ Lab (fun θ t => A θ t 1) (fun _ : Unit => y0)
      (fun _ _ _ => G1) κG (fun _ => F0) V 𝒰 Q)
    (hκ0 : aEnt d L + 1 ≤ κ0) (hKc : K0 d L κ0 + 1 ≤ Kc) (hεpos : 0 < εH)
    (hF0 : 0 < F0) (hκ' : 0 ≤ κ') (hκG : κH ≤ κG)
    (hκ : κ' + 3 * κ0 + c1 d L + 3 / 2 ≤ κH)
    (hε : εH ≤ 1 / (8 * Kc ^ 3 * c1 d L *
      Real.exp ((κH - 2 * κ0) * cG d L + c1 d L + κ' * cG d L)))
    (S : Finset 𝔅) :
    AnalyticOnNhd ℂ (fun θ => markIntTerm μ (A θ) y0 G1 S) V :=
  markIntTerm_analyticOnNhd (G := fun _ => G1) μ hN hj hΩ hfam hκ0 hKc hεpos hF0 hκ' hκG hκ hε S

omit [NormedAddCommGroup E] [NormedSpace ℂ E] in
open Classical in
/-- **Uniform bound for `markIntTerm`**: for every `θ ∈ V` the bound of `markInt_bound` holds with
the same constant. -/
theorem norm_markIntTerm_le {Ωb : 𝔅 → Type*} [∀ b, MeasurableSpace (Ωb b)]
    (μ : ∀ b, Measure (Ωb b)) [∀ b, IsProbabilityMeasure (μ b)]
    (hN : L ^ m₀ ∣ N₁) (hj : j ≤ K) (hΩ : IsPiUnion m₀ j Ω)
    {Lab : CubeLabels m₀ j Ω Lb} {εH κH κG κ0 κ' Kc F0 R : ℝ}
    (A : E → ℂ → ℂ → LabelAct Lab Ωb εH κH κ0 Kc) (y0 : Lb)
    (G : E → (∀ b, Ωb b) → ℂ) (V : Set E)
    (hGm : ∀ θ, Measurable (G θ))
    (hGdep : ∀ θ, DepOn (blocksOf m₀ j Ω (Lab.ysite y0)) (G θ))
    (hG : ∀ θ Φ, ‖G θ Φ‖ ≤ F0 * Real.exp (-κG * Lab.dl y0))
    (hκ0 : aEnt d L + 1 ≤ κ0) (hKc : K0 d L κ0 + 1 ≤ Kc) (hεpos : 0 < εH)
    (hF0 : 0 < F0) (hκ' : 0 ≤ κ') (hκG : κH ≤ κG)
    (hκ : κ' + 3 * κ0 + c1 d L + 3 / 2 ≤ κH)
    (hε : εH ≤ 1 / (8 * Kc ^ 3 * c1 d L *
      Real.exp ((κH - 2 * κ0) * cG d L + c1 d L + κ' * cG d L)))
    (hR : 1 < R)
    (holσ : ∀ θ ∈ V, ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ y Φ,
      DifferentiableOn ℂ (fun σ => (A θ (s : ℂ) σ).H y Φ) (Metric.ball (0 : ℂ) R))
    (hzero : ∀ θ ∈ V, ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ y Φ, (A θ (s : ℂ) 0).H y Φ = 0)
    (hmean : ∀ θ ∈ V, ∫ Φ, G θ Φ ∂(Measure.pi μ) = 0) (S : Finset 𝔅) :
    ∀ θ ∈ V, ‖markIntTerm μ (A θ) y0 (G θ) S‖ ≤
      CPE d L Kc κH κ0 κ' * F0 * Real.exp (-κ0 * Lab.dl y0) * Real.exp (-κ' * dExt S) / R :=
  fun θ hθ => markInt_bound μ hN hj hΩ (A θ) y0 (G θ) (hGm θ) (hGdep θ) (hG θ) hκ0 hKc hεpos
    hF0 hκ' hκG hκ hε hR (holσ θ hθ) (hzero θ hθ) (hmean θ hθ) S

omit [NormedAddCommGroup E] [NormedSpace ℂ E] in
/-- **Locality of `markIntTerm` in a parameter.**  If at two parameters the activities (at
`σ = 1`, `s ∈ [0,1]`) agree on every label whose cubes lie in `S`, and the marks agree whenever the
cubes of the mark lie in `S`, the first-order terms at `S` agree. -/
theorem markIntTerm_param_congr_of_local {Ωb : 𝔅 → Type*} [∀ b, MeasurableSpace (Ωb b)]
    (μ : ∀ b, Measure (Ωb b)) [∀ b, IsProbabilityMeasure (μ b)]
    {Lab : CubeLabels m₀ j Ω Lb} {εH κH κ0 Kc : ℝ}
    (A : E → ℂ → ℂ → LabelAct Lab Ωb εH κH κ0 Kc) (y0 : Lb)
    (G : E → (∀ b, Ωb b) → ℂ)
    (hGdep : ∀ θ, DepOn (blocksOf m₀ j Ω (Lab.ysite y0)) (G θ)) (S : Finset 𝔅) {θ θ' : E}
    (hA : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ y, blocksOf m₀ j Ω (Lab.ysite y) ⊆ S →
      (A θ (s : ℂ) 1).H y = (A θ' (s : ℂ) 1).H y)
    (hG : blocksOf m₀ j Ω (Lab.ysite y0) ⊆ S → G θ = G θ') :
    markIntTerm μ (A θ) y0 (G θ) S = markIntTerm μ (A θ') y0 (G θ') S :=
  markIntTerm_congr μ (A θ) (A θ') y0 S (hGdep θ) hA hG

open Classical in
/-- **Analytic, local and bounded: `markIntTerm` for a parameter family.**  Analytic on `V`;
equal at parameters of `V` with equal `π` when the activities and marks read at `S` depend on `θ`
only through `π θ`; bounded by the constant of `markInt_bound`. -/
theorem markIntTerm_analytic_local_bound {P : Type*} [FiniteDimensional ℂ E]
    {Ωb : 𝔅 → Type*} [∀ b, MeasurableSpace (Ωb b)]
    [∀ b, TopologicalSpace (Ωb b)] [∀ b, OpensMeasurableSpace (Ωb b)]
    [∀ b, SecondCountableTopology (Ωb b)]
    (μ : ∀ b, Measure (Ωb b)) [∀ b, IsProbabilityMeasure (μ b)]
    (hN : L ^ m₀ ∣ N₁) (hj : j ≤ K) (hΩ : IsPiUnion m₀ j Ω)
    {Lab : CubeLabels m₀ j Ω Lb} {εH κH κG κ0 κ' Kc F0 R : ℝ}
    {A : E → ℂ → ℂ → LabelAct Lab Ωb εH κH κ0 Kc} {y0 : Lb}
    {G : E → (∀ b, Ωb b) → ℂ} {V : Set E} {𝒰 : Set ℂ} {Q : Set (∀ b, Ωb b)}
    (hfam : ParamMarkFamily μ Lab (fun θ t => A θ t 1) (fun _ : Unit => y0)
      (fun θ _ _ => G θ) κG (fun _ => F0) V 𝒰 Q)
    (hGdep : ∀ θ, DepOn (blocksOf m₀ j Ω (Lab.ysite y0)) (G θ))
    (hκ0 : aEnt d L + 1 ≤ κ0) (hKc : K0 d L κ0 + 1 ≤ Kc) (hεpos : 0 < εH)
    (hF0 : 0 < F0) (hκ' : 0 ≤ κ') (hκG : κH ≤ κG)
    (hκ : κ' + 3 * κ0 + c1 d L + 3 / 2 ≤ κH)
    (hε : εH ≤ 1 / (8 * Kc ^ 3 * c1 d L *
      Real.exp ((κH - 2 * κ0) * cG d L + c1 d L + κ' * cG d L)))
    (hR : 1 < R)
    (holσ : ∀ θ ∈ V, ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ y Φ,
      DifferentiableOn ℂ (fun σ => (A θ (s : ℂ) σ).H y Φ) (Metric.ball (0 : ℂ) R))
    (hzero : ∀ θ ∈ V, ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ y Φ, (A θ (s : ℂ) 0).H y Φ = 0)
    (hmean : ∀ θ ∈ V, ∫ Φ, G θ Φ ∂(Measure.pi μ) = 0) (S : Finset 𝔅) (π : E → P)
    (hA : ∀ θ ∈ V, ∀ θ' ∈ V, π θ = π θ' → ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 →
      ∀ y, blocksOf m₀ j Ω (Lab.ysite y) ⊆ S → (A θ (s : ℂ) 1).H y = (A θ' (s : ℂ) 1).H y)
    (hG : ∀ θ ∈ V, ∀ θ' ∈ V, π θ = π θ' → blocksOf m₀ j Ω (Lab.ysite y0) ⊆ S → G θ = G θ') :
    AnalyticOnNhd ℂ (fun θ => markIntTerm μ (A θ) y0 (G θ) S) V ∧
      (∀ θ ∈ V, ∀ θ' ∈ V, π θ = π θ' →
        markIntTerm μ (A θ) y0 (G θ) S = markIntTerm μ (A θ') y0 (G θ') S) ∧
      ∀ θ ∈ V, ‖markIntTerm μ (A θ) y0 (G θ) S‖ ≤
        CPE d L Kc κH κ0 κ' * F0 * Real.exp (-κ0 * Lab.dl y0) * Real.exp (-κ' * dExt S) / R :=
  ⟨markIntTerm_analyticOnNhd μ hN hj hΩ hfam hκ0 hKc hεpos hF0 hκ' hκG hκ hε S,
    fun θ hθ θ' hθ' h => markIntTerm_param_congr_of_local μ A y0 G hGdep S
      (hA θ hθ θ' hθ' h) (hG θ hθ θ' hθ' h),
    norm_markIntTerm_le μ hN hj hΩ A y0 G V (fun θ => hfam.meas θ () 0) hGdep
      (fun θ Φ => hfam.bound θ () 0 Φ) hκ0 hKc hεpos hF0 hκ' hκG hκ hε hR holσ hzero hmean S⟩

end MarkInt

section Kernel

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {ι : Type*} [Fintype ι]

open Classical in
/-- **Analyticity of the resummed kernel sum in a parameter**: finite sums and products of
analytic functions. -/
theorem kernelMarkSum_analyticOnNhd {V : Set E} (h Ek : E → ι → Finset 𝔅 → ℂ)
    (hh : ∀ i T, AnalyticOnNhd ℂ (fun e => h e i T) V)
    (hE : ∀ i S, AnalyticOnNhd ℂ (fun e => Ek e i S) V) (W : Finset 𝔅) :
    AnalyticOnNhd ℂ (fun e => kernelMarkSum (h e) (Ek e) W) V := by
  unfold kernelMarkSum
  refine Finset.analyticOnNhd_fun_sum _ fun i _ => ?_
  refine Finset.analyticOnNhd_fun_sum _ fun T _ => ?_
  refine Finset.analyticOnNhd_fun_sum _ fun S _ => ?_
  by_cases hTS : T ∪ S = W
  · simp only [hTS, ite_true]
    exact (hh i T).mul (hE i S)
  · simp only [hTS, ite_false]
    exact analyticOnNhd_const

omit [NormedAddCommGroup E] [NormedSpace ℂ E] in
open Classical in
/-- **Uniform bound for the resummed kernel sum**: if the kernel and the terms satisfy the
hypotheses of `kernel_mark_resum` for every `e ∈ V`, with the same constants, the bound of
`kernel_mark_resum` holds on `V`. -/
theorem norm_kernelMarkSum_le (hN : L ^ m₀ ∣ N₁) (hj : j ≤ K) {V : Set E}
    (b : ι → 𝔅) {nmax : ℝ} (hnmax : 0 ≤ nmax)
    (hcount : ∀ c : 𝔅, ((Finset.univ.filter fun i => b i = c).card : ℝ) ≤ nmax)
    (h Ek : E → ι → Finset 𝔅 → ℂ) {Ch Cg κh κg κ0 Kc : ℝ} (hCh : 0 ≤ Ch) (hCg : 0 ≤ Cg)
    (hh : ∀ e ∈ V, ∀ i T, ‖h e i T‖ ≤ Ch * Real.exp (-κh * dExt T))
    (hhs : ∀ e ∈ V, ∀ i T, b i ∉ T → h e i T = 0)
    (hE : ∀ e ∈ V, ∀ i S, ‖Ek e i S‖ ≤ Cg * Real.exp (-κg * dExt S))
    (hEs : ∀ e ∈ V, ∀ i S, b i ∉ S → Ek e i S = 0)
    (hκ0 : aEnt d L + 1 ≤ κ0) (hKc : K0 d L κ0 + 1 ≤ Kc) (hκh : κ0 ≤ κh) (hκg : κ0 ≤ κg)
    (W : Finset 𝔅) :
    ∀ e ∈ V, ‖kernelMarkSum (h e) (Ek e) W‖ ≤
      Ch * Cg * (nmax * c1 d L) * Kc ^ 2 * Real.exp ((min κh κg - κ0) * cG d L) *
        Real.exp (-(min κh κg - κ0 - 1) * dExt W) :=
  fun e he => kernel_mark_resum hN hj b hnmax hcount (h e) (Ek e) hCh hCg (hh e he) (hhs e he)
    (hE e he) (hEs e he) hκ0 hKc hκh hκg W

end Kernel

end Balaban.Fluctuation
