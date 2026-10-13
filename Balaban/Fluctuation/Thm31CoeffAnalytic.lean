/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Polymer.MarkedCubesHolo
public import Balaban.Polymer.MarkedHoloParam
public import Balaban.Fluctuation.Thm31CoeffA
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Analyticity in a finite-dimensional parameter of `P(S)`, `G*(Y₀, S)` and `gsumCoeff`

Several-parameter form of `Pst_Gst_differentiableOn`, and the analyticity of the canonical
coefficient `gsumCoeff` in a parameter `θ` of a finite-dimensional complex space when the label
activities `A θ u` and the marks `G θ i u` are analytic in `(θ, u)`.

`ParamMarkFamily` is the ANALYTIC part of a parameter-dependent `InterpMarks`: it records the
regularity of the family (analytic in `(θ, u)` on `V × 𝒰` for each configuration of a compact set
`Q` carrying the product measure, continuous in the configuration, measurable, and the mark bound
uniform in `θ`).  It does not contain the numerical constants of Theorem 3.4 (they are explicit
hypotheses of the theorems), nor the dependence (`DepOn`) fields, nor `W`/`f`/`hW`/`hF`.  The
compact carrier `Q` is an extra hypothesis: it does not hold for Gaussian reference measures, but
it does hold for the actual step measure, which has the sharp cutoff `‖ψ̂(u)‖ < p₁`
(`physCarrier` in `ParamCarrierLocal`).  Producing a parameter family from the physical
step (the actual activities and marks, and the determinant term) is not done here.

Finite-dimensionality of `E` is used only through `analyticAt_integral_of_continuousOn` (the
integrals over the configuration `Φ` and over `s ∈ [0,1]`).  Joint continuity in
(parameter, configuration) is not assumed: it follows from analyticity in the parameter, the
uniform bound and continuity in the configuration (`continuousOn_prod_of_analytic_bdd`).  The
analyticity is assumed jointly in `(θ, u)`; the numerical constants are explicit hypotheses.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Localization Balaban.Polymer MeasureTheory

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {m₀ j : ℕ} {Ω : Set (CTorus d L N₁ m₁ K)}

local notation "𝔅" => CubeB (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ j Ω

section Holo

variable {Lb : Type*} [Fintype Lb]

open Classical in
/-- **Analyticity of `P(S)` and `G*(Y₀, S)` in a finite-dimensional parameter `u ∈ V`**
(several-parameter form of `Pst_Gst_differentiableOn`).  The label activities `(A u).H` and the
mark `G u` are analytic in `u ∈ V` for each configuration `Φ` of a compact set `Q` carrying the
product measure, and continuous on `Q` for each `u`; the hypotheses of `marked_cubes` hold for
every `u` with the same constants. -/
theorem Pst_Gst_analyticOnNhd {Ωb : 𝔅 → Type*} [∀ b, MeasurableSpace (Ωb b)]
    (μ : ∀ b, Measure (Ωb b)) [∀ b, IsProbabilityMeasure (μ b)]
    (hN : L ^ m₀ ∣ N₁) (hj : j ≤ K) (hΩ : IsPiUnion m₀ j Ω)
    {Lab : CubeLabels m₀ j Ω Lb} {εH κH κG κ0 κ' Kc F0 : ℝ}
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    [∀ b, TopologicalSpace (Ωb b)] [∀ b, OpensMeasurableSpace (Ωb b)]
    [∀ b, SecondCountableTopology (Ωb b)]
    {V : Set E} (hV : IsOpen V) {Q : Set (∀ b, Ωb b)} (hQ : IsCompact Q) (hQm : MeasurableSet Q)
    (hμQ : ∀ᵐ Φ ∂(Measure.pi μ), Φ ∈ Q)
    (A : E → LabelAct Lab Ωb εH κH κ0 Kc) (y0 : Lb) (G : E → (∀ b, Ωb b) → ℂ)
    (hGm : ∀ u, Measurable (G u))
    (hG : ∀ u Φ, ‖G u Φ‖ ≤ F0 * Real.exp (-κG * Lab.dl y0))
    (hAhol : ∀ y, ∀ Φ ∈ Q, AnalyticOnNhd ℂ (fun u => (A u).H y Φ) V)
    (hGhol : ∀ Φ ∈ Q, AnalyticOnNhd ℂ (fun u => G u Φ) V)
    (hAcont : ∀ y, ∀ u ∈ V, ContinuousOn ((A u).H y) Q)
    (hGcont : ∀ u ∈ V, ContinuousOn (G u) Q)
    (hκ0 : aEnt d L + 1 ≤ κ0) (hKc : K0 d L κ0 + 1 ≤ Kc) (hεpos : 0 < εH) (hF0 : 0 < F0)
    (hκ' : 0 ≤ κ') (hκG : κH ≤ κG)
    (hκ : κ' + 3 * κ0 + c1 d L + 3 / 2 ≤ κH)
    (hε : εH ≤ 1 / (8 * Kc ^ 3 * c1 d L *
      Real.exp ((κH - 2 * κ0) * cG d L + c1 d L + κ' * cG d L)))
    (Y : Finset 𝔅) :
    AnalyticOnNhd ℂ (fun u => Pst μ Lab (A u).H Y) V ∧
      AnalyticOnNhd ℂ (fun u => Gst μ Lab (A u).H (blocksOf m₀ j Ω (Lab.ysite y0)) (G u) Y) V := by
  set S0 := blocksOf m₀ j Ω (Lab.ysite y0) with hS0
  set r0 := εH * Kc * Real.exp (κ0 * Lab.dl y0) / F0 with hr0
  have hKgeo : 0 < K0 d L κ0 := by
    unfold K0
    have : Real.exp (-1) < 1 := by rw [Real.exp_lt_one_iff]; norm_num
    exact div_pos (Real.exp_pos _) (by linarith [aEnt_nonneg d L])
  have hKc1 : 1 ≤ Kc := by linarith
  have hKc0 : 0 ≤ Kc := by linarith
  have hc1 := one_le_c1 d L
  have hcG : 0 ≤ cG d L := by unfold cG; positivity
  have haent := aEnt_nonneg d L
  have hκ0nn : 0 ≤ κ0 := by linarith
  have hκHge : κ0 ≤ κH := by linarith
  have hκ1nn : 0 ≤ κH - 2 * κ0 := by linarith
  have hκGnn : 0 ≤ κG := by linarith
  have hr0pos : 0 < r0 := by positivity
  obtain ⟨hα1, hq, hH0log⟩ := numerics_PE hεpos hKc1 hc1 hcG hκ' hκ1nn hε
  have hexp_le : ∀ (κ x : ℝ), 0 ≤ κ → 0 ≤ x → Real.exp (-κ * x) ≤ 1 := fun κ x hκ hx =>
    Real.exp_le_one_iff.2 (by nlinarith)
  have hGC : ∀ u Φ, ‖G u Φ‖ ≤ F0 := fun u Φ => (hG u Φ).trans (by
    have := hexp_le κG (Lab.dl y0) hκGnn (Lab.dl_nonneg y0)
    nlinarith)
  have hG2c := fun b : 𝔅 => (sum_exp_dExt_le hN hj b hκ0).trans hKc
  have hG3T : ∀ C : Finset (NePoly 𝔅), ConnSet (Subtype.val : NePoly 𝔅 → Finset 𝔅) C →
      dExt (unionCs (Subtype.val : NePoly 𝔅 → Finset 𝔅) C) ≤
        ∑ t ∈ C, dExt t.1 + cG d L * ((C.card : ℝ) - 1) := fun C hC => dExt_unionCs_le C hC
  have hG1 : ∀ Y : NePoly 𝔅, (Y.1.card : ℝ) ≤ c1 d L * (1 + dExt Y.1) :=
    fun Y => card_le_dExt hN hj Y.1
  have hκ1 : κ' + κ0 + c1 d L ≤ (κH - 2 * κ0) - 3 / 2 := by linarith
  have hH0 : 0 ≤ 2 * εH * Kc := by positivity
  have hKP := marked_kp (B := 𝔅) (d := dExt) (c1 := c1 d L) (κ' := κ') (κ0P := κ0) (K0P := Kc)
    (cP := cG d L) (κ1 := κH - 2 * κ0)
    (ε := 2 * (2 * (2 * εH * Kc) * Kc * Real.exp ((κH - 2 * κ0) * cG d L)) * c1 d L)
    (by positivity) (fun Y => dExt_nonneg Y) hG1 (fun b => by convert hG2c b) hκ1 hα1
  -- the per-`u` data
  have hdat : ∀ u, (∀ Z : NePoly 𝔅, AnalyticOnNhd ℂ
        (marksK μ Subtype.val (presum Lab (A u).H) (gMark S0 (G u)) Z)
        (Balaban.Analysis.polydisc (0 : Unit → ℂ) (fun _ => r0))) ∧
      (∀ (Z : NePoly 𝔅), ∀ l ∈ Balaban.Analysis.polydisc (0 : Unit → ℂ) (fun _ => r0),
        ‖marksK μ Subtype.val (presum Lab (A u).H) (gMark S0 (G u)) Z l‖ ≤
          sizeW (Subtype.val : NePoly 𝔅 → Finset 𝔅) dExt
            (2 * (2 * (2 * εH * Kc) * Kc * Real.exp ((κH - 2 * κ0) * cG d L)) * c1 d L)
            (κH - 2 * κ0 - 3 / 2) κ' (cG d L) Z) := by
    intro u
    have hab : ∀ t, Bdd ((presum Lab (A u).H) t) := fun t => ⟨εH * Kc, fun Φ =>
      ((A u).presum_bound hN hj hΩ hεpos.le hκHge t Φ).trans (by
        have := hexp_le (κH - κ0) (dExt t.1) (by linarith) (dExt_nonneg t.1)
        have h0 : 0 ≤ εH * Kc := by positivity
        nlinarith)⟩
    have hHb : ∀ l ∈ Balaban.Analysis.polydisc (0 : Unit → ℂ) (fun _ : Unit => r0),
        ∀ (t : NePoly 𝔅) (Φ : ∀ b, Ωb b),
        ‖Hlam (presum Lab (A u).H) (gMark S0 (G u)) l t Φ‖ ≤
          (2 * εH * Kc) * Real.exp (-(κ0 + (κH - 2 * κ0)) * dExt t.1) :=
      fun l hl t Φ => hHlam_bound hN hj hΩ (A u) y0 (G u) (hG u) hεpos hF0 (by linarith) hκHge hκG l
        (by simpa using hl ()) t Φ
    have hmb := marked_bounds μ (Subtype.val : NePoly 𝔅 → Finset 𝔅) (fun t => t.2)
      (fun t => (A u).presum_meas t) hab (fun _ t => gMark_measurable S0 (hGm u) t)
      (fun _ t => gMark_bdd S0 hF0.le (hGC u) t) hH0 hH0log hκ0nn hκ1nn hcG
      (fun Y => dExt_nonneg Y) hHb (fun b => by rw [Finset.sum_filter]; convert hG2c b) hG3T
      (by linarith) hq hG1 hKc0 hκ' hcG
    exact ⟨hmb.1, hmb.2.2⟩
  -- analyticity in `u` of the activities, for fixed marks
  have hKu : ∀ (Z : NePoly 𝔅), ∀ l ∈ Balaban.Analysis.polydisc (0 : Unit → ℂ) (fun _ : Unit => r0),
      AnalyticOnNhd ℂ (fun u => marksK μ Subtype.val (presum Lab (A u).H)
        (gMark S0 (G u)) Z l) V := by
    intro Z l hl
    have hHb : ∀ u (t : NePoly 𝔅) (Φ : ∀ b, Ωb b),
        ‖Hlam (presum Lab (A u).H) (gMark S0 (G u)) l t Φ‖ ≤ 2 * εH * Kc := fun u t Φ => by
      refine (hHlam_bound hN hj hΩ (A u) y0 (G u) (hG u) hεpos hF0 (by linarith) hκHge hκG l
        (by simpa using hl ()) t Φ).trans ?_
      have := hexp_le (κ0 + (κH - 2 * κ0)) (dExt t.1) (by linarith) (dExt_nonneg t.1)
      nlinarith [mul_nonneg hKc0 hεpos.le]
    have hanal : ∀ t : NePoly 𝔅, ∀ Φ ∈ Q,
        AnalyticOnNhd ℂ (fun u => Hlam (presum Lab (A u).H) (gMark S0 (G u)) l t Φ) V := by
      intro t Φ hΦ
      have h1 : AnalyticOnNhd ℂ (fun u => presum Lab (A u).H t Φ) V := by
        unfold presum
        exact Finset.analyticOnNhd_fun_sum _ (fun y _ => hAhol y Φ hΦ)
      have h2 : AnalyticOnNhd ℂ (fun u => gMark S0 (G u) () t Φ) V := by
        by_cases ht : t.1 = S0
        · simp only [gMark, ht, ite_true]; exact hGhol Φ hΦ
        · simp only [gMark, ht, ite_false]; exact analyticOnNhd_const
      unfold Hlam
      exact h1.add (Finset.analyticOnNhd_fun_sum _ (fun j _ => analyticOnNhd_const.mul h2))
    have hcontΦ : ∀ t : NePoly 𝔅, ∀ u ∈ V,
        ContinuousOn (Hlam (presum Lab (A u).H) (gMark S0 (G u)) l t) Q := by
      intro t u hu
      have h1 : ContinuousOn (presum Lab (A u).H t) Q := by
        unfold presum
        exact continuousOn_finsetSum _ (fun y _ => hAcont y u hu)
      have h2 : ContinuousOn (gMark S0 (G u) () t) Q := by
        by_cases ht : t.1 = S0
        · have : gMark S0 (G u) () t = G u := by funext Φ; simp [gMark, ht]
          rw [this]; exact hGcont u hu
        · have : gMark S0 (G u) () t = fun _ => 0 := by funext Φ; simp [gMark, ht]
          rw [this]; exact continuousOn_const
      unfold Hlam
      exact h1.add (continuousOn_finsetSum _ (fun j _ => continuousOn_const.mul h2))
    exact analyticOnNhd_mayerK_param (sup := (Subtype.val : NePoly 𝔅 → Finset 𝔅)) μ hV hQ hQm
      hμQ (H := fun u => Hlam (presum Lab (A u).H) (gMark S0 (G u)) l) hanal
      (fun t => continuousOn_prod_of_analytic_bdd hV (fun Φ hΦ => hanal t Φ hΦ)
        (fun u hu => hcontΦ t u hu) (fun u _ Φ _ => hHb u t Φ)) Z
  have hmain := holo_of_KP_param (shareBlock (Subtype.val : NePoly 𝔅 → Finset 𝔅)) Subtype.val hKP
    (fun _ => hr0pos) hV
    (fun u Z l => marksK μ Subtype.val (presum Lab (A u).H) (gMark S0 (G u)) Z l)
    (fun u _ Z => (hdat u).1 Z) hKu (fun u _ Z l hl => (hdat u).2 Z l hl) Y
  refine ⟨?_, hmain.2 ()⟩
  have heq : (fun u => Pst μ Lab (A u).H Y) = fun u => PY (shareBlock
      (Subtype.val : NePoly 𝔅 → Finset 𝔅)) Subtype.val
      (fun Z => marksK μ Subtype.val (presum Lab (A u).H) (gMark S0 (G u)) Z 0) Y := by
    funext u
    exact (Ff_zero_eq_Pst μ Lab (A u).H S0 (G u) Y).symm
  rw [heq]
  exact hmain.1

end Holo

section Family

variable {Lb : Type*} [Fintype Lb] {ι : Type*} [Fintype ι]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- **Analytic regularity of a parameter family of labels activities and marks.**  For `θ ∈ V ⊆ E`
(open) and `u ∈ 𝒰 ⊆ ℂ` (open, containing `[0,1]`): the activities `(A θ u).H y Φ` and the marks
`G θ i u Φ` are analytic in `(θ, u) ∈ V × 𝒰` for every configuration `Φ` of the compact set `Q`
(which carries the product measure), continuous in `Φ ∈ Q`, the marks are measurable and bounded by
`F0 i e^{-κG 𝗱(y0 i)}` uniformly in `(θ, u)`.  The constants `εH κH κ0 Kc` in the type of `A` are
the same for all `θ, u`. -/
structure ParamMarkFamily {Ωb : 𝔅 → Type*} [∀ b, MeasurableSpace (Ωb b)]
    [∀ b, TopologicalSpace (Ωb b)] (μ : ∀ b, Measure (Ωb b)) [∀ b, IsProbabilityMeasure (μ b)]
    (Lab : CubeLabels m₀ j Ω Lb) {εH κH κ0 Kc : ℝ}
    (A : E → ℂ → LabelAct Lab Ωb εH κH κ0 Kc) (y0 : ι → Lb)
    (G : E → ι → ℂ → (∀ b, Ωb b) → ℂ) (κG : ℝ) (F0 : ι → ℝ)
    (V : Set E) (𝒰 : Set ℂ) (Q : Set (∀ b, Ωb b)) : Prop where
  isOpenV : IsOpen V
  isOpenU : IsOpen 𝒰
  seg : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → (s : ℂ) ∈ 𝒰
  compact : IsCompact Q
  measQ : MeasurableSet Q
  carried : ∀ᵐ Φ ∂(Measure.pi μ), Φ ∈ Q
  meas : ∀ θ i u, Measurable (G θ i u)
  bound : ∀ θ i u Φ, ‖G θ i u Φ‖ ≤ F0 i * Real.exp (-κG * Lab.dl (y0 i))
  holA : ∀ y, ∀ Φ ∈ Q, AnalyticOnNhd ℂ (fun p : E × ℂ => (A p.1 p.2).H y Φ) (V ×ˢ 𝒰)
  holG : ∀ i, ∀ Φ ∈ Q, AnalyticOnNhd ℂ (fun p : E × ℂ => G p.1 i p.2 Φ) (V ×ˢ 𝒰)
  contA : ∀ y, ∀ θ ∈ V, ∀ u ∈ 𝒰, ContinuousOn ((A θ u).H y) Q
  contG : ∀ i, ∀ θ ∈ V, ∀ u ∈ 𝒰, ContinuousOn (G θ i u) Q

open Classical in
/-- **Analyticity of `Gsum` in `(θ, u)`.** -/
theorem Gsum_analyticOnNhd {Ωb : 𝔅 → Type*} [∀ b, MeasurableSpace (Ωb b)]
    [∀ b, TopologicalSpace (Ωb b)] [∀ b, OpensMeasurableSpace (Ωb b)]
    [∀ b, SecondCountableTopology (Ωb b)] [FiniteDimensional ℂ E]
    (μ : ∀ b, Measure (Ωb b)) [∀ b, IsProbabilityMeasure (μ b)]
    (hN : L ^ m₀ ∣ N₁) (hj : j ≤ K) (hΩ : IsPiUnion m₀ j Ω)
    {Lab : CubeLabels m₀ j Ω Lb} {εH κH κG κ0 κ' Kc : ℝ} {F0 : ι → ℝ}
    {A : E → ℂ → LabelAct Lab Ωb εH κH κ0 Kc} {y0 : ι → Lb}
    {G : E → ι → ℂ → (∀ b, Ωb b) → ℂ} {V : Set E} {𝒰 : Set ℂ} {Q : Set (∀ b, Ωb b)}
    (hfam : ParamMarkFamily μ Lab A y0 G κG F0 V 𝒰 Q)
    (hκ0 : aEnt d L + 1 ≤ κ0) (hKc : K0 d L κ0 + 1 ≤ Kc) (hεpos : 0 < εH)
    (hF0 : ∀ i, 0 < F0 i) (hκ' : 0 ≤ κ') (hκG : κH ≤ κG)
    (hκ : κ' + 3 * κ0 + c1 d L + 3 / 2 ≤ κH)
    (hε : εH ≤ 1 / (8 * Kc ^ 3 * c1 d L *
      Real.exp ((κH - 2 * κ0) * cG d L + c1 d L + κ' * cG d L)))
    (T : Finset 𝔅) :
    AnalyticOnNhd ℂ (fun p : E × ℂ =>
      Gsum μ Lab (A p.1 p.2).H y0 (fun i => G p.1 i p.2) T) (V ×ˢ 𝒰) := by
  unfold Gsum
  refine Finset.analyticOnNhd_fun_sum _ (fun i _ => ?_)
  exact (Pst_Gst_analyticOnNhd (E := E × ℂ) μ hN hj hΩ (V := V ×ˢ 𝒰)
    (hfam.isOpenV.prod hfam.isOpenU) hfam.compact hfam.measQ hfam.carried
    (fun p => A p.1 p.2) (y0 i) (fun p => G p.1 i p.2) (fun p => hfam.meas _ _ _)
    (fun p Φ => hfam.bound _ _ _ _) (fun y Φ hΦ => hfam.holA y Φ hΦ)
    (fun Φ hΦ => hfam.holG i Φ hΦ) (fun y p hp => hfam.contA y p.1 hp.1 p.2 hp.2)
    (fun p hp => hfam.contG i p.1 hp.1 p.2 hp.2) hκ0 hKc hεpos (hF0 i) hκ' hκG hκ hε T).2

open Classical in
/-- **Analyticity of the canonical coefficient `gsumCoeff` in the parameter `θ ∈ V`.** -/
theorem gsumCoeff_analyticOnNhd {Ωb : 𝔅 → Type*} [∀ b, MeasurableSpace (Ωb b)]
    [∀ b, TopologicalSpace (Ωb b)] [∀ b, OpensMeasurableSpace (Ωb b)]
    [∀ b, SecondCountableTopology (Ωb b)] [FiniteDimensional ℂ E]
    (μ : ∀ b, Measure (Ωb b)) [∀ b, IsProbabilityMeasure (μ b)]
    (hN : L ^ m₀ ∣ N₁) (hj : j ≤ K) (hΩ : IsPiUnion m₀ j Ω)
    {Lab : CubeLabels m₀ j Ω Lb} {εH κH κG κ0 κ' Kc : ℝ} {F0 : ι → ℝ}
    {A : E → ℂ → LabelAct Lab Ωb εH κH κ0 Kc} {y0 : ι → Lb}
    {G : E → ι → ℂ → (∀ b, Ωb b) → ℂ} {V : Set E} {𝒰 : Set ℂ} {Q : Set (∀ b, Ωb b)}
    (hfam : ParamMarkFamily μ Lab A y0 G κG F0 V 𝒰 Q)
    (hκ0 : aEnt d L + 1 ≤ κ0) (hKc : K0 d L κ0 + 1 ≤ Kc) (hεpos : 0 < εH)
    (hF0 : ∀ i, 0 < F0 i) (hκ' : 0 ≤ κ') (hκG : κH ≤ κG)
    (hκ : κ' + 3 * κ0 + c1 d L + 3 / 2 ≤ κH)
    (hε : εH ≤ 1 / (8 * Kc ^ 3 * c1 d L *
      Real.exp ((κH - 2 * κ0) * cG d L + c1 d L + κ' * cG d L)))
    (T : Finset 𝔅) :
    AnalyticOnNhd ℂ (fun θ => gsumCoeff μ Lab (A θ) y0 (G θ) T) V := by
  intro θ0 hθ0
  have hG := Gsum_analyticOnNhd μ hN hj hΩ hfam hκ0 hKc hεpos hF0 hκ' hκG hκ hε T
  have hfin : IsFiniteMeasure (volume.restrict (Set.Ioc (0 : ℝ) 1)) :=
    ⟨by rw [Measure.restrict_apply_univ, Real.volume_Ioc]; exact ENNReal.ofReal_lt_top⟩
  have h := Balaban.Analysis.analyticAt_integral_comp (P := E) (V := ℂ) (X := ℝ)
    (μ := volume.restrict (Set.Ioc (0 : ℝ) 1)) (K := Set.Icc (0 : ℝ) 1)
    isCompact_Icc measurableSet_Icc
    (ae_restrict_of_forall_mem measurableSet_Ioc (fun x hx => Set.Ioc_subset_Icc_self hx))
    (ι := fun s : ℝ => (s : ℂ)) Complex.continuous_ofReal.continuousOn
    (G := fun p : E × ℂ => Gsum μ Lab (A p.1 p.2).H y0 (fun i => G p.1 i p.2) T) (Θ₀ := θ0)
    (fun s hs => hG _ ⟨hθ0, hfam.seg s hs⟩)
  unfold gsumCoeff
  simp only [intervalIntegral.integral_of_le (zero_le_one' ℝ)]
  exact h

omit [NormedAddCommGroup E] [NormedSpace ℂ E] in
/-- The bound of `interpCoeff_spec` is uniform in the parameter: it depends only on the constants
`Kc κH κ0 κ'`, `F0` and `𝗱(y0 i)`, which are the same for all `θ`.  The conclusion is given by
`avg_marks_expansion` at each `(θ, s)`; the integral over `s ∈ [0,1]` keeps the bound. -/
theorem norm_gsumCoeff_le {Ωb : 𝔅 → Type*} [∀ b, MeasurableSpace (Ωb b)]
    (μ : ∀ b, Measure (Ωb b)) [∀ b, IsProbabilityMeasure (μ b)]
    (hN : L ^ m₀ ∣ N₁) (hj : j ≤ K) (hΩ : IsPiUnion m₀ j Ω)
    {Lab : CubeLabels m₀ j Ω Lb} {εH κH κG κ0 κ' Kc : ℝ} {F0 : ι → ℝ}
    (A : E → ℂ → LabelAct Lab Ωb εH κH κ0 Kc) (y0 : ι → Lb)
    (G : E → ι → ℂ → (∀ b, Ωb b) → ℂ) (V : Set E)
    (hGm : ∀ θ i u, Measurable (G θ i u))
    (hGdep : ∀ θ i u, DepOn (blocksOf m₀ j Ω (Lab.ysite (y0 i))) (G θ i u))
    (hG : ∀ θ i u Φ, ‖G θ i u Φ‖ ≤ F0 i * Real.exp (-κG * Lab.dl (y0 i)))
    (hκ0 : aEnt d L + 1 ≤ κ0) (hKc : K0 d L κ0 + 1 ≤ Kc) (hεpos : 0 < εH)
    (hι : Nonempty ι) (hF0 : ∀ i, 0 < F0 i) (hκ' : 0 ≤ κ') (hκG : κH ≤ κG)
    (hκ : κ' + 3 * κ0 + c1 d L + 3 / 2 ≤ κH)
    (hε : εH ≤ 1 / (8 * Kc ^ 3 * c1 d L *
      Real.exp ((κH - 2 * κ0) * cG d L + c1 d L + κ' * cG d L))) (T : Finset 𝔅) :
    ∀ θ ∈ V, ‖gsumCoeff μ Lab (A θ) y0 (G θ) T‖ ≤ CPE d L Kc κH κ0 κ' *
      (∑ i, F0 i * Real.exp (-κ0 * Lab.dl (y0 i))) * Real.exp (-κ' * dExt T) := by
  intro θ _
  unfold gsumCoeff
  have hb : ∀ s ∈ Set.uIoc (0 : ℝ) 1, ‖Gsum μ Lab (A θ (s : ℂ)).H y0
      (fun i => G θ i (s : ℂ)) T‖ ≤ CPE d L Kc κH κ0 κ' *
      (∑ i, F0 i * Real.exp (-κ0 * Lab.dl (y0 i))) * Real.exp (-κ' * dExt T) := fun s _ =>
    (avg_marks_expansion μ hN hj hΩ (A θ (s : ℂ)) y0 (fun i => G θ i (s : ℂ))
      (fun i => hGm θ i _) (fun i => hGdep θ i _) (fun i Φ => hG θ i _ Φ) hκ0 hKc hεpos hι hF0
      hκ' hκG hκ hε).2.2 T
  have := intervalIntegral.norm_integral_le_of_norm_le_const hb
  simpa using this

section Inhabited

omit [Fintype ι] in
/-- **`ParamMarkFamily` is inhabited (constant family).**  Activities and marks independent of
`(θ, u)`, on configuration spaces that are finite and discrete (so that every configuration set is
compact and every function continuous), for any label activity `A₀` and any measurable marks with
the mark bound. -/
theorem nonempty_paramMarkFamily_const
    {Ωb : 𝔅 → Type*} [∀ b, MeasurableSpace (Ωb b)] [∀ b, TopologicalSpace (Ωb b)]
    [∀ b, Finite (Ωb b)] [∀ b, DiscreteTopology (Ωb b)]
    (μ : ∀ b, Measure (Ωb b)) [∀ b, IsProbabilityMeasure (μ b)] {Lab : CubeLabels m₀ j Ω Lb}
    {εH κH κ0 Kc : ℝ}
    (A₀ : LabelAct Lab Ωb εH κH κ0 Kc) (y0 : ι → Lb)
    (G₀ : ι → (∀ b, Ωb b) → ℂ) (κG : ℝ) (F0 : ι → ℝ) (hG₀m : ∀ i, Measurable (G₀ i))
    (hG₀ : ∀ i Φ, ‖G₀ i Φ‖ ≤ F0 i * Real.exp (-κG * Lab.dl (y0 i)))
    (V : Set E) (hV : IsOpen V) :
    Nonempty (ParamMarkFamily μ Lab (fun _ _ => A₀) y0 (fun _ i _ => G₀ i) κG F0 V Set.univ
      Set.univ) :=
  ⟨{ isOpenV := hV
     isOpenU := isOpen_univ
     seg := fun _ _ => Set.mem_univ _
     compact := isCompact_univ
     measQ := MeasurableSet.univ
     carried := Filter.Eventually.of_forall (fun _ => Set.mem_univ _)
     meas := fun _ i _ => hG₀m i
     bound := fun _ i _ Φ => hG₀ i Φ
     holA := fun _ _ _ => analyticOnNhd_const
     holG := fun _ _ _ => analyticOnNhd_const
     contA := fun _ _ _ _ _ => continuous_of_discreteTopology.continuousOn
     contG := fun _ _ _ _ _ => continuous_of_discreteTopology.continuousOn }⟩

/-- The label activity `A₀` multiplied by a complex factor `c` with `‖c‖ ≤ 2`; its size constant
is `2 ε_H`. -/
noncomputable def LabelAct.scale
    {Ωb : 𝔅 → Type*} [∀ b, MeasurableSpace (Ωb b)] {Lab : CubeLabels m₀ j Ω Lb}
    {εH κH κ0 Kc : ℝ} (A₀ : LabelAct Lab Ωb εH κH κ0 Kc) (c : ℂ) (hc : ‖c‖ ≤ 2) :
    LabelAct Lab Ωb (2 * εH) κH κ0 Kc where
  H := fun y Φ => c * A₀.H y Φ
  meas := fun y => (A₀.meas y).const_mul c
  dep := fun y Φ Φ' h => by simp only [A₀.dep y Φ Φ' h]
  bound := fun y Φ => by
    rw [norm_mul]
    calc ‖c‖ * ‖A₀.H y Φ‖ ≤ 2 * (εH * Real.exp (-κH * Lab.dl y)) :=
        mul_le_mul hc (A₀.bound y Φ) (norm_nonneg _) (by norm_num)
      _ = _ := by ring
  entropy := A₀.entropy

omit [Fintype ι] in
/-- **`ParamMarkFamily` is inhabited by a genuinely `θ`-dependent family**: for `θ ∈ ℂ`,
`‖θ‖ < 2⁻¹`, the activities `(1 + θ) A₀` and the constant marks. -/
theorem nonempty_paramMarkFamily_scaled
    {Ωb : 𝔅 → Type*} [∀ b, MeasurableSpace (Ωb b)] [∀ b, TopologicalSpace (Ωb b)]
    [∀ b, Finite (Ωb b)] [∀ b, DiscreteTopology (Ωb b)]
    (μ : ∀ b, Measure (Ωb b)) [∀ b, IsProbabilityMeasure (μ b)] {Lab : CubeLabels m₀ j Ω Lb}
    {εH κH κ0 Kc : ℝ}
    (A₀ : LabelAct Lab Ωb εH κH κ0 Kc) (y0 : ι → Lb)
    (G₀ : ι → (∀ b, Ωb b) → ℂ) (κG : ℝ) (F0 : ι → ℝ) (hG₀m : ∀ i, Measurable (G₀ i))
    (hG₀ : ∀ i Φ, ‖G₀ i Φ‖ ≤ F0 i * Real.exp (-κG * Lab.dl (y0 i))) :
    ∃ A : ℂ → ℂ → LabelAct Lab Ωb (2 * εH) κH κ0 Kc,
      (∀ θ u y Φ, ‖θ‖ < 2⁻¹ → (A θ u).H y Φ = (1 + θ) * A₀.H y Φ) ∧
      Nonempty (ParamMarkFamily μ Lab A y0 (fun _ i _ => G₀ i) κG F0 (Metric.ball 0 (2⁻¹))
        Set.univ Set.univ) := by
  have hcb : ∀ θ : ℂ, ‖(if ‖θ‖ < 2⁻¹ then 1 + θ else 1 : ℂ)‖ ≤ 2 := fun θ => by
    by_cases h : ‖θ‖ < 2⁻¹
    · simp only [h, ite_true]
      calc ‖(1 + θ : ℂ)‖ ≤ ‖(1 : ℂ)‖ + ‖θ‖ := norm_add_le _ _
        _ ≤ 2 := by simp; linarith
    · simp [h]
  refine ⟨fun θ _ => A₀.scale _ (hcb θ), fun θ u y Φ h => ?_, ⟨?_⟩⟩
  · simp [LabelAct.scale, h]
  · refine
      { isOpenV := Metric.isOpen_ball
        isOpenU := isOpen_univ
        seg := fun _ _ => Set.mem_univ _
        compact := isCompact_univ
        measQ := MeasurableSet.univ
        carried := Filter.Eventually.of_forall (fun _ => Set.mem_univ _)
        meas := fun _ i _ => hG₀m i
        bound := fun _ i _ Φ => hG₀ i Φ
        holA := fun y Φ _ => ?_
        holG := fun _ _ _ => analyticOnNhd_const
        contA := fun _ _ _ _ _ => continuous_of_discreteTopology.continuousOn
        contG := fun _ _ _ _ _ => continuous_of_discreteTopology.continuousOn }
    have h1 : AnalyticOnNhd ℂ (fun p : ℂ × ℂ => (1 + p.1) * A₀.H y Φ)
        (Metric.ball (0 : ℂ) (2⁻¹) ×ˢ (Set.univ : Set ℂ)) :=
      (analyticOnNhd_const.add analyticOnNhd_fst).mul analyticOnNhd_const
    refine h1.congr (Metric.isOpen_ball.prod isOpen_univ) (fun p hp => ?_)
    have : ‖p.1‖ < 2⁻¹ := by simpa using hp.1
    simp [LabelAct.scale, this]

end Inhabited

end Family

end Balaban.Fluctuation


