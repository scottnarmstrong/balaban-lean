/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Polymer.LabelRootUnion
public import Balaban.Fluctuation.Thm31CoeffAnalytic
public import Balaban.Fluctuation.ParamActivityPhysical
public import Balaban.Inhabited.StepOutputConsts
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# One label system and one activity family for the marks of all roots

The records `ParamMarkFamily` and `InterpMarks` (hence `E1MarksC`) fix one label system and one
activity family before the root `z` is chosen.  Starting from an activity family `A` on labels
`Lab`, the common labels are `Lab` summed with the root-union labels of the bridge families
(`commonLabels`), the activity family is extended by zero (`commonAct`) with entropy constant
`K_c + rootUnionK`, and the mark of the root `z` and bridge domain `Y′` is anchored at
`commonAnchor z Y′ = Sum.inr (rootUnionIncl …)`.

* `commonAct_total`, `commonAct_hW_interp`: the activity sum and the identity `hW` are unchanged.
* `commonAct_holA_analytic`, `commonAct_holA_differentiableOn`, `commonAct_contA`: the analyticity,
  differentiability and continuity fields of the two records transfer (the new activities are `0`).
* `commonAnchor_ysite`, `commonAnchor_dl`, `commonAnchor_marks_fields`: the site set and size of the
  anchor of `(z, Y′)` are `Y′` and `d^cov_K(Y′)`, and `dep`, `bound` of the marks of one root
  transfer.
* `paramMarkFamily_common`: the `ParamMarkFamily` on the common system from the activity and mark
  fields.
* `commonK_ge`, `commonKc_ge`, `commonStepTheta_le`, `exists_beta0_commonLabels`: the numerical
  conditions at `K_c′ = K_c + rootUnionK` and `κ₀ ≥ a_ent + 2`.
* `markedCommonLabels_nonempty`: non-vacuity for the zero activities of a physical step.

The marks themselves and `E1MarksC` are NOT constructed here.  Everything is independent of the
datum, the chart and the choice of generators.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Localization Balaban.Polymer Balaban.Multiscale MeasureTheory
open scoped Classical

section Common

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {m₀ : ℕ} {β : Type*} [Fintype β]
  {Lb : Type*} [Fintype Lb] {Lab : CubeLabels (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := K)
    m₀ K Set.univ Lb}
  {Ωb : CubeB (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ K Set.univ → Type*}
  [∀ b, MeasurableSpace (Ωb b)] {εH κH κ0 Kc : ℝ}
  {E : Type*}

/-- The common labels: the labels `Lab` and the labels `(z, Y′)` of all roots. -/
noncomputable abbrev commonLabels (Lab : CubeLabels (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := K)
      m₀ K Set.univ Lb)
    (hN : L ^ m₀ ∣ N₁) (hL : 2 ≤ L)
    (reads : β → Set (CTorus d L N₁ m₁ K)) (dom : β → Finset (Set (CTorus d L N₁ m₁ K)))
    (hdom : ∀ b, ∀ Y ∈ dom b, IsDj m₀ K Y) :
    CubeLabels (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ K Set.univ
      (Lb ⊕ RootUnionLb m₀ reads dom) :=
  Lab.sum (rootUnionLabels hN hL reads dom hdom)

/-- The activity family extended by zero to the labels of all roots; entropy constant
`K_c + rootUnionK`. -/
noncomputable abbrev commonAct (A : E → ℂ → LabelAct Lab Ωb εH κH κ0 Kc)
    (hN : L ^ m₀ ∣ N₁) (hL : 2 ≤ L)
    (reads : β → Set (CTorus d L N₁ m₁ K)) (dom : β → Finset (Set (CTorus d L N₁ m₁ K)))
    (hdom : ∀ b, ∀ Y ∈ dom b, IsDj m₀ K Y) (hεH : 0 ≤ εH) (hκ0 : aEnt d L + 2 ≤ κ0) :
    E → ℂ → LabelAct (commonLabels Lab hN hL reads dom hdom) Ωb εH κH κ0
      (Kc + rootUnionK d L m₀ m₁ κ0) :=
  fun θ u => (A θ u).extendRootUnion hN hL reads dom hdom hεH hκ0

/-- The anchor label of the mark of the root `z` at the bridge domain `Y′`. -/
abbrev commonAnchor (Lb : Type*) (reads : β → Set (CTorus d L N₁ m₁ K))
    (dom : β → Finset (Set (CTorus d L N₁ m₁ K))) (z : RootIdx d L N₁ m₁ K)
    (Y' : {Y' // Y' ∈ bridgeFamily m₀ reads dom z}) : Lb ⊕ RootUnionLb m₀ reads dom :=
  Sum.inr (rootUnionIncl reads dom z Y')

variable (A : E → ℂ → LabelAct Lab Ωb εH κH κ0 Kc)
  (hN : L ^ m₀ ∣ N₁) (hL : 2 ≤ L)
  (reads : β → Set (CTorus d L N₁ m₁ K)) (dom : β → Finset (Set (CTorus d L N₁ m₁ K)))
  (hdom : ∀ b, ∀ Y ∈ dom b, IsDj m₀ K Y) (hεH : 0 ≤ εH) (hκ0 : aEnt d L + 2 ≤ κ0)

@[simp] theorem commonAct_H_inl (θ : E) (u : ℂ) (y : Lb) :
    (commonAct A hN hL reads dom hdom hεH hκ0 θ u).H (Sum.inl y) = (A θ u).H y := rfl

@[simp] theorem commonAct_H_inr (θ : E) (u : ℂ) (y : RootUnionLb m₀ reads dom)
    (Φ : ∀ b, Ωb b) :
    (commonAct A hN hL reads dom hdom hεH hκ0 θ u).H (Sum.inr y) Φ = 0 := rfl

/-- The activity sum is unchanged. -/
theorem commonAct_total (θ : E) (u : ℂ) (Φ : ∀ b, Ωb b) :
    ∑ y, (commonAct A hN hL reads dom hdom hεH hκ0 θ u).H y Φ = ∑ y, (A θ u).H y Φ :=
  LabelAct.extendRootUnion_total _ hN hL reads dom hdom hεH hκ0 Φ

/-- **The exact shape of `InterpMarks.hW`** (and of the `hW` of the parameter family at `θ`)
transfers to the common system. -/
theorem commonAct_hW_interp {X : Type*} [MeasurableSpace X] {ν : Measure X} (θ : E)
    {W : ℝ → X → ℂ} {restr : X → ∀ b, Ωb b}
    (hW : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ᵐ x ∂ν,
      W s x = ∑ y, (A θ (s : ℂ)).H y (restr x)) :
    ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ᵐ x ∂ν,
      W s x = ∑ y, (commonAct A hN hL reads dom hdom hεH hκ0 θ (s : ℂ)).H y (restr x) :=
  LabelAct.extendRootUnion_hW_interp (A θ) hN hL reads dom hdom hεH hκ0 hW

/-- The analyticity field `holA` of `ParamMarkFamily` transfers. -/
theorem commonAct_holA_analytic [NormedAddCommGroup E] [NormedSpace ℂ E] {V : Set E} {𝒰 : Set ℂ}
    {Q : Set (∀ b, Ωb b)}
    (h : ∀ y, ∀ Φ ∈ Q, AnalyticOnNhd ℂ (fun p : E × ℂ => (A p.1 p.2).H y Φ) (V ×ˢ 𝒰)) :
    ∀ y, ∀ Φ ∈ Q, AnalyticOnNhd ℂ
      (fun p : E × ℂ => (commonAct A hN hL reads dom hdom hεH hκ0 p.1 p.2).H y Φ) (V ×ˢ 𝒰) := by
  intro y Φ hΦ
  cases y with
  | inl y => exact h y Φ hΦ
  | inr y => exact analyticOnNhd_const

/-- The differentiability field `holA` of `InterpMarks` transfers. -/
theorem commonAct_holA_differentiableOn (θ : E) {𝒰 : Set ℂ}
    (h : ∀ y Φ, DifferentiableOn ℂ (fun u => (A θ u).H y Φ) 𝒰) :
    ∀ y Φ, DifferentiableOn ℂ
      (fun u => (commonAct A hN hL reads dom hdom hεH hκ0 θ u).H y Φ) 𝒰 := by
  intro y Φ
  cases y with
  | inl y => exact h y Φ
  | inr y => exact differentiableOn_const _

/-- The continuity field `contA` of `ParamMarkFamily` transfers. -/
theorem commonAct_contA [TopologicalSpace (∀ b, Ωb b)] {V : Set E} {𝒰 : Set ℂ}
    {Q : Set (∀ b, Ωb b)}
    (h : ∀ y, ∀ θ ∈ V, ∀ u ∈ 𝒰, ContinuousOn ((A θ u).H y) Q) :
    ∀ y, ∀ θ ∈ V, ∀ u ∈ 𝒰,
      ContinuousOn ((commonAct A hN hL reads dom hdom hεH hκ0 θ u).H y) Q := by
  intro y θ hθ u hu
  cases y with
  | inl y => exact h y θ hθ u hu
  | inr y => exact continuousOn_const

omit [Fintype Lb] in
/-- The site set of the anchor of `(z, Y′)` is `Y′`. -/
theorem commonAnchor_ysite (z : RootIdx d L N₁ m₁ K)
    (Y' : {Y' // Y' ∈ bridgeFamily m₀ reads dom z}) :
    (commonLabels Lab hN hL reads dom hdom).ysite (commonAnchor Lb reads dom z Y') = Y'.1 := rfl

omit [Fintype Lb] in
/-- The site set and size of the anchor are those of the bridge label of the root `z`. -/
theorem commonAnchor_bridge (z : RootIdx d L N₁ m₁ K)
    (Y' : {Y' // Y' ∈ bridgeFamily m₀ reads dom z}) :
    (commonLabels Lab hN hL reads dom hdom).ysite (commonAnchor Lb reads dom z Y') =
        (bridgeLabels hN hL reads dom hdom z).ysite Y' ∧
      (commonLabels Lab hN hL reads dom hdom).dl (commonAnchor Lb reads dom z Y') =
        (bridgeLabels hN hL reads dom hdom z).dl Y' := ⟨rfl, rfl⟩

omit [Fintype Lb] in
/-- The size of the anchor of `(z, Y′)` is `d^cov_K(Y′)`. -/
theorem commonAnchor_dl (z : RootIdx d L N₁ m₁ K)
    (Y' : {Y' // Y' ∈ bridgeFamily m₀ reads dom z}) :
    (commonLabels Lab hN hL reads dom hdom).dl (commonAnchor Lb reads dom z Y') =
      treeLenCovOne m₀ K Y'.1 := rfl

omit [Fintype Lb] [∀ b, MeasurableSpace (Ωb b)] in
/-- **Root clause**: `dep` and `bound` of the marks of the root `z` transfer to the anchors. -/
theorem commonAnchor_marks_fields (z : RootIdx d L N₁ m₁ K)
    {ι : Type*} (y0 : ι → {Y' // Y' ∈ bridgeFamily m₀ reads dom z}) (F0 : ι → ℝ) (κG : ℝ)
    (G : ι → ℂ → (∀ b, Ωb b) → ℂ)
    (hdep : ∀ i u, DepOn (Ω := Ωb) (blocksOf m₀ K Set.univ
      ((bridgeLabels hN hL reads dom hdom z).ysite (y0 i))) (G i u))
    (hbound : ∀ i u Φ, ‖G i u Φ‖ ≤
      F0 i * Real.exp (-κG * (bridgeLabels hN hL reads dom hdom z).dl (y0 i))) :
    (∀ i u, DepOn (Ω := Ωb) (blocksOf m₀ K Set.univ
      ((commonLabels Lab hN hL reads dom hdom).ysite (commonAnchor Lb reads dom z (y0 i))))
      (G i u)) ∧
    (∀ i u Φ, ‖G i u Φ‖ ≤ F0 i * Real.exp (-κG *
      (commonLabels Lab hN hL reads dom hdom).dl (commonAnchor Lb reads dom z (y0 i)))) :=
  rootUnion_marks_fields (Lab := Lab) hN hL reads dom hdom z y0 F0 κG G hdep hbound

/-- **The `ParamMarkFamily` on the common system.**  The activity fields are those of the
original family; the mark fields are given at the new anchors `y0'`. -/
theorem paramMarkFamily_common [NormedAddCommGroup E] [NormedSpace ℂ E]
    [∀ b, TopologicalSpace (Ωb b)] (μ : ∀ b, Measure (Ωb b)) [∀ b, IsProbabilityMeasure (μ b)]
    {ι : Type*} (y0' : ι → Lb ⊕ RootUnionLb m₀ reads dom)
    (G : E → ι → ℂ → (∀ b, Ωb b) → ℂ) (κG : ℝ) (F0 : ι → ℝ)
    (V : Set E) (𝒰 : Set ℂ) (Q : Set (∀ b, Ωb b))
    (hV : IsOpen V) (h𝒰 : IsOpen 𝒰)
    (hseg : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → (s : ℂ) ∈ 𝒰)
    (hQ : IsCompact Q) (hQm : MeasurableSet Q) (hcar : ∀ᵐ Φ ∂(Measure.pi μ), Φ ∈ Q)
    (hmeas : ∀ θ i u, Measurable (G θ i u))
    (hbound : ∀ θ i u Φ, ‖G θ i u Φ‖ ≤
      F0 i * Real.exp (-κG * (commonLabels Lab hN hL reads dom hdom).dl (y0' i)))
    (hholA : ∀ y, ∀ Φ ∈ Q, AnalyticOnNhd ℂ (fun p : E × ℂ => (A p.1 p.2).H y Φ) (V ×ˢ 𝒰))
    (hholG : ∀ i, ∀ Φ ∈ Q, AnalyticOnNhd ℂ (fun p : E × ℂ => G p.1 i p.2 Φ) (V ×ˢ 𝒰))
    (hcontA : ∀ y, ∀ θ ∈ V, ∀ u ∈ 𝒰, ContinuousOn ((A θ u).H y) Q)
    (hcontG : ∀ i, ∀ θ ∈ V, ∀ u ∈ 𝒰, ContinuousOn (G θ i u) Q) :
    ParamMarkFamily μ (commonLabels Lab hN hL reads dom hdom)
      (commonAct A hN hL reads dom hdom hεH hκ0) y0' G κG F0 V 𝒰 Q where
  isOpenV := hV
  isOpenU := h𝒰
  seg := hseg
  compact := hQ
  measQ := hQm
  carried := hcar
  meas := hmeas
  bound := hbound
  holA := commonAct_holA_analytic A hN hL reads dom hdom hεH hκ0 hholA
  holG := hholG
  contA := commonAct_contA A hN hL reads dom hdom hεH hκ0 hcontA
  contG := hcontG

end Common

section Numerics

variable {d L N₁ m₁ : ℕ} [NeZero L]

/-- `rootUnionK ≥ 0`. -/
theorem rootUnionK_nonneg (m₀ : ℕ) (κ0 : ℝ) : 0 ≤ rootUnionK d L m₀ m₁ κ0 := by
  have hc : 0 < c1 d L := lt_of_lt_of_le one_pos (one_le_c1 d L)
  have hK := K0_pos d L (κ0 - 1)
  unfold rootUnionK
  positivity

/-- `K_c ≤ K_c′`. -/
theorem commonK_ge (m₀ : ℕ) (κ0 Kc : ℝ) : Kc ≤ Kc + rootUnionK d L m₀ m₁ κ0 :=
  le_add_of_nonneg_right (rootUnionK_nonneg m₀ κ0)

/-- The conditions `hκ0` and `hKc` of the two records hold at the common system: `κ₀ ≥ a_ent + 2`
gives `κ₀ ≥ a_ent + 1`, and `K₀ + 1 ≤ K_c` gives `K₀ + 1 ≤ K_c′`. -/
theorem commonKc_ge (m₀ : ℕ) {κ0 Kc : ℝ} (hκ0 : aEnt d L + 2 ≤ κ0)
    (hKc : K0 d L κ0 + 1 ≤ Kc) :
    aEnt d L + 1 ≤ κ0 ∧ K0 d L κ0 + 1 ≤ Kc + rootUnionK d L m₀ m₁ κ0 :=
  ⟨by linarith, hKc.trans (commonK_ge m₀ κ0 Kc)⟩

omit [NeZero L] in
/-- The strengthened smallness `hε` of the two records at `K_c′` is the inequality
`ε_H ≤ stepTheta d L K_c′ κ_H κ₀ κ′`. -/
theorem hε_common_iff (εH Kc' κH κ0 κ' : ℝ) :
    εH ≤ 1 / (8 * Kc' ^ 3 * c1 d L *
      Real.exp ((κH - 2 * κ0) * cG d L + c1 d L + κ' * cG d L)) ↔
      εH ≤ stepTheta d L Kc' κH κ0 κ' := Iff.rfl

/-- `stepTheta` is decreasing in the entropy constant: the smallness at `K_c′` implies the
smallness at `K_c ≤ K_c′` (for `0 < K_c`). -/
theorem commonStepTheta_le {Kc Kc' : ℝ} (hKc : 0 < Kc) (h : Kc ≤ Kc') (κH κ0 κ' : ℝ) :
    stepTheta d L Kc' κH κ0 κ' ≤ stepTheta d L Kc κH κ0 κ' := by
  have hc : 0 < c1 d L := lt_of_lt_of_le one_pos (one_le_c1 d L)
  unfold stepTheta
  have h3 : Kc ^ 3 ≤ Kc' ^ 3 := pow_le_pow_left₀ hKc.le h 3
  apply one_div_le_one_div_of_le
  · positivity
  · have := Real.exp_pos ((κH - 2 * κ0) * cG d L + c1 d L + κ' * cG d L)
    have h8 : 8 * Kc ^ 3 ≤ 8 * Kc' ^ 3 := by linarith
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h8 hc.le) this.le

/-- **The scale threshold at the enlarged constant.**  For every `K_c′ > 0` and the fixed
constants `κ_H, κ₀, κ′, C_U, C_R, s, p` there is `β₀` such that for `b = β 3^k`, `β ≥ β₀`, every
`0 ≤ ε_H ≤ C_U (log b)^{3p}/√b` satisfies the strengthened `hε`
`ε_H ≤ stepTheta d L K_c′ κ_H κ₀ κ′` (and `R_g ε_H ≤ stepTheta …`, `R_g > 1`).
`exists_beta0_stepOutput` gives this only for `K_tot = 2(2K₀+1)`, which does not contain
`rootUnionK` (it depends on `L^{d(m₀+m₁)}`); this statement is for arbitrary `K_c′`. -/
theorem exists_beta0_commonLabels {Kc' κH κ0 κ' CU CR s p : ℝ} (hKc' : 0 < Kc')
    (hCU : 0 ≤ CU) (hCR : 0 < CR) (hs0 : 0 < s) (hs : s < 1 / 2) :
    ∃ β₀ : ℝ, 1 < β₀ ∧ ∀ (β : ℝ) (k : ℕ), β₀ ≤ β → ∀ ε : ℝ, 0 ≤ ε →
      ε ≤ CU * Real.log (β * 3 ^ k) ^ (3 * p) / Real.sqrt (β * 3 ^ k) →
      1 < obsRg CR s p (β * 3 ^ k) ∧
        obsRg CR s p (β * 3 ^ k) * ε ≤ stepTheta d L Kc' κH κ0 κ' ∧
        ε ≤ stepTheta d L Kc' κH κ0 κ' := by
  have hc : 0 < c1 d L := lt_of_lt_of_le one_pos (one_le_c1 d L)
  have hθ : 0 < stepTheta d L Kc' κH κ0 κ' := by unfold stepTheta; positivity
  obtain ⟨b₁, hb₁, h1⟩ := exists_one_lt_obsRg (p := p) hCR hs0
  obtain ⟨b₂, hb₂, h2⟩ := exists_obsRg_mul_le (p := p) hCR hs hCU hθ
  refine ⟨max b₁ b₂, lt_of_lt_of_le hb₁ (le_max_left _ _), fun β k hβ ε hε0 hε => ?_⟩
  have hβ1 : 1 < β := lt_of_lt_of_le hb₁ (le_trans (le_max_left _ _) hβ)
  have h3k : (1 : ℝ) ≤ 3 ^ k := one_le_pow₀ (by norm_num)
  have hb : β ≤ β * 3 ^ k := by nlinarith
  have hb1 : 1 ≤ β * 3 ^ k := by linarith
  have hR := h1 _ (le_trans (le_trans (le_max_left _ _) hβ) hb)
  have hε' : ε ≤ CU * obsW p (β * 3 ^ k) ^ 3 / Real.sqrt (β * 3 ^ k) := by
    rwa [obsW_cube p _ hb1]
  have hR2 := h2 _ ε (le_trans (le_trans (le_max_right _ _) hβ) hb) hε'
  refine ⟨hR, hR2, ?_⟩
  nlinarith

end Numerics

section Inhabited

open Metric

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}

/-- **Non-vacuity.**  For a step `S` (with `L^{m₀} ∣ N₁`, `2 ≤ L`, `0 < p₁`) and the zero
activities of the whole-torus label, with the single block domain the box of the root cube of
the root `0` (reading every site) and `κ₀ = a_ent + 2`: there is a root `z` and a bridge domain
`Y′` of `z` such that the `ParamMarkFamily` on the common labels, over the parameter space `ℂ`,
with the extended activities, the single zero mark anchored at `(z, Y′)`, `V = ℂ`, `𝒰 = B(0, 2)`
and the physical carrier, exists. -/
theorem markedCommonLabels_nonempty (S : StepSetting d L N₁ m₁ k N ϱ) (m₀ : ℕ)
    (hN : L ^ m₀ ∣ N₁) (hL : 2 ≤ L) (hp : 0 < S.p₁) (a : ℝ) :
    ∃ (I : DirectTerms S m₀ hp (F' := Unit) (fun _ => ()) 1 2 0 a (0 : ℂ) Set.univ Set.univ
        (fun _ _ _ _ => (0 : ℂ)) (fun _ _ _ => True) (fun _ _ _ => True))
      (hF : DirectTermsFamily S m₀ I Set.univ)
      (reads : Unit → Set (CTorus d L N₁ m₁ (k + 1)))
      (dom : Unit → Finset (Set (CTorus d L N₁ m₁ (k + 1))))
      (hdom : ∀ b, ∀ Y ∈ dom b, IsDj m₀ (k + 1) Y)
      (z : RootIdx d L N₁ m₁ (k + 1))
      (Y' : {Y' // Y' ∈ bridgeFamily m₀ reads dom z})
      (hκ : aEnt d L + 2 ≤ aEnt d L + 2),
      Nonempty (ParamMarkFamily (S.blockSplit m₀ hp).μ
        (commonLabels (thickLabels I.𝒴 I.dom) hN hL reads dom hdom)
        (commonAct (labelActFamily S m₀ I hF hN one_pos (by norm_num) le_rfl
          (κ0 := aEnt d L + 2) (by linarith) (le_refl (K0 d L (aEnt d L + 2))))
          hN hL reads dom hdom (by norm_num) hκ)
        (fun _ : Unit => commonAnchor _ reads dom z Y') (fun _ _ _ _ => (0 : ℂ)) 0
        (fun _ : Unit => 1) Set.univ (ball (0 : ℂ) 2) (physCarrier S m₀ hp)) := by
  obtain ⟨I, hF, -⟩ := nonempty_directTermsFamily S m₀ hp 1 2 0 a le_rfl
  have hfam := paramMarkFamily_zero_marks S m₀ hF hN one_pos (by norm_num) le_rfl
    (κ0 := aEnt d L + 2) (by linarith) (le_refl (K0 d L (aEnt d L + 2))) (by norm_num)
    (fun e : Empty => e.elim) 0 (fun e : Empty => e.elim) (fun e : Empty => e.elim)
  set z0 : RootIdx d L N₁ m₁ (k + 1) := 0 with hz0
  set Y0 : Set (CTorus d L N₁ m₁ (k + 1)) :=
    box (rootCube (m₀ := m₀) z0).1 (L * cellSide L m₀ m₁ (k + 1)) with hY0
  have hdom : ∀ b, ∀ Y ∈ (fun _ : Unit => ({Y0} : Finset _)) b, IsDj m₀ (k + 1) Y := by
    intro b Y hY
    rw [Finset.mem_singleton] at hY
    subst hY
    exact isDj_box (rootCube (m₀ := m₀) z0).2.1
  have hmem : rootSite z0 ∈ Y0 :=
    box_mono _ (Nat.le_mul_of_pos_left _ (by omega))
      (rootSite_mem_box_rootCube (m₀ := m₀) z0)
  have hfb : rootSite z0 ∈ fineBlock z0 := blockIndex_rootSite z0
  have hbr : bridge m₀ z0 Y0 ∈ bridgeFamily m₀ (fun _ : Unit => Set.univ)
      (fun _ => {Y0}) z0 := by
    rw [mem_bridgeFamily]
    exact ⟨(), Y0, Finset.mem_singleton_self _, ⟨rootSite z0, Set.mem_univ _, hfb⟩,
      ⟨rootSite z0, Or.inl hmem, hfb⟩, rfl⟩
  refine ⟨I, hF, fun _ => Set.univ, fun _ => {Y0}, hdom, z0, ⟨bridge m₀ z0 Y0, hbr⟩, le_rfl,
    ⟨paramMarkFamily_common _ hN hL _ _ hdom (by norm_num) le_rfl _
      (fun _ : Unit => commonAnchor _ (fun _ : Unit => Set.univ) (fun _ => {Y0}) z0
        ⟨bridge m₀ z0 Y0, hbr⟩)
      (fun _ _ _ _ => (0 : ℂ)) 0 (fun _ : Unit => 1) Set.univ (ball (0 : ℂ) 2) _
      hfam.isOpenV hfam.isOpenU hfam.seg hfam.compact hfam.measQ hfam.carried
      (fun _ _ _ => measurable_const)
      (fun _ _ _ _ => by simp only [norm_zero]; exact mul_nonneg zero_le_one (Real.exp_pos _).le)
      hfam.holA (fun _ _ _ => analyticOnNhd_const) hfam.contA
      (fun _ _ _ _ _ => continuousOn_const)⟩⟩

end Inhabited

end Balaban.Fluctuation
