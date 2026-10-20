/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.LabelActRestr

/-!
# Parameter families of activities and marks truncated to a class of labels

The activities and marks of the new level recomputed on a background generating set `Gb` (route
R-LOC, L4-3) have their fields (measurability, bound, analyticity, continuity) only for the labels
whose neighbourhood lies in the top layer of `Gb` (`LabelMargin Gb`).  Truncated to such a class `P`
of labels (zero off `P`), bundled at the configuration restricted to the blocks of the label
(`labelActRestr`), and with the marks evaluated at the configuration restricted to the blocks of
their anchor label, they form one `ParamMarkFamily`.  The coefficient of a polymer `T` reads the
activities and marks of the labels inside `T` only, and the labels inside the polymer of the local
generating set have the margin, so the truncation does not change the coefficient there.

* `truncAct`, `truncMark`: the truncated activities and the truncated restricted marks;
* `truncMark_dep`: the truncated restricted marks depend only on the blocks of their anchor label;
* `paramMarkFamily_trunc`: the bundled truncated activities and the truncated restricted marks form a
  `ParamMarkFamily`, from the fields of the activities and the marks of the labels of `P`.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Localization Balaban.Polymer MeasureTheory

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {m₀ j : ℕ} {Ω : Set (CTorus d L N₁ m₁ K)}

local notation "𝔅" => CubeB (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ j Ω

section Trunc

variable {Lb : Type*} {ι : Type*} {E : Type*}

open Classical in
/-- **The activities truncated to a class `P` of labels**: `H θ u y` on the labels whose site set
is in `P`, `0` on the others. -/
noncomputable def truncAct (Lab : CubeLabels m₀ j Ω Lb) (P : Set (CTorus d L N₁ m₁ K) → Prop)
    {Ωb : 𝔅 → Type*} (H : E → ℂ → Lb → (∀ b : 𝔅, Ωb b) → ℂ) (θ : E) (u : ℂ) (y : Lb)
    (Φ : ∀ b : 𝔅, Ωb b) : ℂ :=
  if P (Lab.ysite y) then H θ u y Φ else 0

open Classical in
/-- **The marks truncated to a class `P` of labels and restricted to the blocks of their anchor**:
`G θ i u` at the configuration restricted to the blocks of the anchor label `y0 i` (`Φ₀` off them)
when the anchor label is in `P`, `0` otherwise. -/
noncomputable def truncMark (Lab : CubeLabels m₀ j Ω Lb) (P : Set (CTorus d L N₁ m₁ K) → Prop)
    (y0 : ι → Lb) {Ωb : 𝔅 → Type*} (Φ₀ : ∀ b : 𝔅, Ωb b)
    (G : E → ι → ℂ → (∀ b : 𝔅, Ωb b) → ℂ) (θ : E) (i : ι) (u : ℂ) (Φ : ∀ b : 𝔅, Ωb b) : ℂ :=
  if P (Lab.ysite (y0 i)) then
    G θ i u (restrConf (blocksOf m₀ j Ω (Lab.ysite (y0 i))) Φ₀ Φ) else 0

omit [NeZero N₁] [NeZero L] in
/-- The truncated activity of a label of `P`. -/
theorem truncAct_of_pos (Lab : CubeLabels m₀ j Ω Lb) {P : Set (CTorus d L N₁ m₁ K) → Prop}
    {Ωb : 𝔅 → Type*} (H : E → ℂ → Lb → (∀ b : 𝔅, Ωb b) → ℂ) (θ : E) (u : ℂ) {y : Lb}
    (hP : P (Lab.ysite y)) : truncAct Lab P H θ u y = H θ u y := by
  funext Φ
  simp only [truncAct, hP, ↓reduceIte]

omit [NeZero N₁] [NeZero L] in
/-- The truncated activity of a label off `P` vanishes. -/
theorem truncAct_of_neg (Lab : CubeLabels m₀ j Ω Lb) {P : Set (CTorus d L N₁ m₁ K) → Prop}
    {Ωb : 𝔅 → Type*} (H : E → ℂ → Lb → (∀ b : 𝔅, Ωb b) → ℂ) (θ : E) (u : ℂ) {y : Lb}
    (hP : ¬ P (Lab.ysite y)) : truncAct Lab P H θ u y = fun _ => 0 := by
  funext Φ
  simp only [truncAct, hP, ↓reduceIte]

/-- The truncated mark of an anchor of `P` is the mark at the restricted configuration. -/
theorem truncMark_of_pos (Lab : CubeLabels m₀ j Ω Lb) {P : Set (CTorus d L N₁ m₁ K) → Prop}
    (y0 : ι → Lb) {Ωb : 𝔅 → Type*} (Φ₀ : ∀ b : 𝔅, Ωb b)
    (G : E → ι → ℂ → (∀ b : 𝔅, Ωb b) → ℂ) (θ : E) {i : ι} (u : ℂ)
    (hP : P (Lab.ysite (y0 i))) : truncMark Lab P y0 Φ₀ G θ i u =
      fun Φ => G θ i u (restrConf (blocksOf m₀ j Ω (Lab.ysite (y0 i))) Φ₀ Φ) := by
  funext Φ
  simp only [truncMark, hP, ↓reduceIte]

/-- The truncated mark of an anchor off `P` vanishes. -/
theorem truncMark_of_neg (Lab : CubeLabels m₀ j Ω Lb) {P : Set (CTorus d L N₁ m₁ K) → Prop}
    (y0 : ι → Lb) {Ωb : 𝔅 → Type*} (Φ₀ : ∀ b : 𝔅, Ωb b)
    (G : E → ι → ℂ → (∀ b : 𝔅, Ωb b) → ℂ) (θ : E) {i : ι} (u : ℂ)
    (hP : ¬ P (Lab.ysite (y0 i))) : truncMark Lab P y0 Φ₀ G θ i u = fun _ => 0 := by
  funext Φ
  simp only [truncMark, hP, ↓reduceIte]

/-- The truncated restricted marks depend only on the blocks of their anchor label. -/
theorem truncMark_dep (Lab : CubeLabels m₀ j Ω Lb) (P : Set (CTorus d L N₁ m₁ K) → Prop)
    (y0 : ι → Lb) {Ωb : 𝔅 → Type*} (Φ₀ : ∀ b : 𝔅, Ωb b)
    (G : E → ι → ℂ → (∀ b : 𝔅, Ωb b) → ℂ) (θ : E) (i : ι) (u : ℂ) :
    DepOn (blocksOf m₀ j Ω (Lab.ysite (y0 i))) (truncMark Lab P y0 Φ₀ G θ i u) := by
  classical
  intro Φ Φ' h
  by_cases hP : P (Lab.ysite (y0 i))
  · rw [truncMark_of_pos Lab y0 Φ₀ G θ u hP]
    exact congrArg (G θ i u) (restrConf_eq_of_agree Φ₀ h)
  · rw [truncMark_of_neg Lab y0 Φ₀ G θ u hP]

variable [NormedAddCommGroup E] [NormedSpace ℂ E]

open Classical in
/-- **`ParamMarkFamily` of the truncated bundled activities and the truncated restricted marks.**
For a class `P` of label sets, activities `H` that are measurable, bounded by
`ε_H e^{-κ_H 𝗱(y)}`, analytic in the parameters on `V × 𝒰` at every configuration and continuous in
the configuration on `V × 𝒰` for the labels of `P`, with the entropy of the labels, and marks `G`
that are measurable, bounded by `F₀ᵢ e^{-κ_G 𝗱(y0 i)}`, analytic on `V × 𝒰` at every configuration
and continuous in the configuration for the anchor labels of `P`: the truncated activities bundled at
the restricted configuration (`labelActRestr`) and the truncated restricted marks form a
`ParamMarkFamily` over `V`, `𝒰` and any compact measurable carrier `Q`. -/
theorem paramMarkFamily_trunc [Fintype Lb] {Ωb : 𝔅 → Type*} [∀ b, MeasurableSpace (Ωb b)]
    [∀ b, TopologicalSpace (Ωb b)] (μ : ∀ b, Measure (Ωb b)) [∀ b, IsProbabilityMeasure (μ b)]
    (Lab : CubeLabels m₀ j Ω Lb) (P : Set (CTorus d L N₁ m₁ K) → Prop) {εH κH κ0 Kc : ℝ}
    (Φ₀ : ∀ b : 𝔅, Ωb b) (H : E → ℂ → Lb → (∀ b : 𝔅, Ωb b) → ℂ)
    (hmeasP : ∀ θ u y, P (Lab.ysite y) → Measurable (H θ u y))
    (hbdP : ∀ θ u y Φ, P (Lab.ysite y) → ‖H θ u y Φ‖ ≤ εH * Real.exp (-κH * Lab.dl y))
    (hεH : 0 ≤ εH)
    (hent : ∀ b : 𝔅, ∑ y : Lb, (if box b.1 (cellSide L m₀ m₁ j) ⊆ Lab.ysite y then
      Real.exp (-κ0 * Lab.dl y) else 0) ≤ Kc)
    (y0 : ι → Lb) (G : E → ι → ℂ → (∀ b : 𝔅, Ωb b) → ℂ) (κG : ℝ) (F0 : ι → ℝ)
    (hF0 : ∀ i, 0 ≤ F0 i) {V : Set E} {𝒰 : Set ℂ} {Q : Set (∀ b : 𝔅, Ωb b)}
    (hV : IsOpen V) (hU : IsOpen 𝒰) (hseg : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → (s : ℂ) ∈ 𝒰)
    (hQ : IsCompact Q) (hQm : MeasurableSet Q) (hcar : ∀ᵐ Φ ∂(Measure.pi μ), Φ ∈ Q)
    (hholP : ∀ y, P (Lab.ysite y) → ∀ Φ,
      AnalyticOnNhd ℂ (fun p : E × ℂ => H p.1 p.2 y Φ) (V ×ˢ 𝒰))
    (hcontP : ∀ y, P (Lab.ysite y) → ∀ θ ∈ V, ∀ u ∈ 𝒰, Continuous (H θ u y))
    (hGmeasP : ∀ θ i u, P (Lab.ysite (y0 i)) → Measurable (G θ i u))
    (hGbdP : ∀ θ i u Φ, P (Lab.ysite (y0 i)) →
      ‖G θ i u Φ‖ ≤ F0 i * Real.exp (-κG * Lab.dl (y0 i)))
    (hGholP : ∀ i, P (Lab.ysite (y0 i)) → ∀ Φ,
      AnalyticOnNhd ℂ (fun p : E × ℂ => G p.1 i p.2 Φ) (V ×ˢ 𝒰))
    (hGcontP : ∀ i, P (Lab.ysite (y0 i)) → ∀ θ ∈ V, ∀ u ∈ 𝒰, Continuous (G θ i u)) :
    ∃ A : E → ℂ → LabelAct Lab Ωb εH κH κ0 Kc,
      (∀ θ u y Φ, (A θ u).H y Φ =
        truncAct Lab P H θ u y (restrConf (blocksOf m₀ j Ω (Lab.ysite y)) Φ₀ Φ)) ∧
      Nonempty (ParamMarkFamily μ Lab A y0 (truncMark Lab P y0 Φ₀ G) κG F0 V 𝒰 Q) := by
  have hmeas : ∀ θ u y, Measurable (truncAct Lab P H θ u y) := by
    intro θ u y
    by_cases hP : P (Lab.ysite y)
    · rw [truncAct_of_pos Lab H θ u hP]
      exact hmeasP θ u y hP
    · rw [truncAct_of_neg Lab H θ u hP]
      exact measurable_const
  have hbd : ∀ θ u y Φ, ‖truncAct Lab P H θ u y Φ‖ ≤ εH * Real.exp (-κH * Lab.dl y) := by
    intro θ u y Φ
    by_cases hP : P (Lab.ysite y)
    · simp only [truncAct, hP, ↓reduceIte]
      exact hbdP θ u y Φ hP
    · simp only [truncAct, hP, ↓reduceIte, norm_zero]
      exact mul_nonneg hεH (Real.exp_pos _).le
  refine ⟨fun θ u => labelActRestr Lab Φ₀ (truncAct Lab P H θ u) (hmeas θ u) (hbd θ u) hent,
    fun _ _ _ _ => rfl, ⟨paramMarkFamily_restr μ Lab Φ₀ (truncAct Lab P H) hmeas hbd hent y0
      (truncMark Lab P y0 Φ₀ G) κG F0 hV hU hseg hQ hQm hcar (fun y Φ => ?_)
      (fun y θ hθ u hu => ?_) (fun θ i u => ?_) (fun θ i u Φ => ?_) (fun i Φ _ => ?_)
      (fun i θ hθ u hu => ?_)⟩⟩
  · by_cases hP : P (Lab.ysite y)
    · simp only [truncAct, hP, ↓reduceIte]
      exact hholP y hP Φ
    · simp only [truncAct, hP, ↓reduceIte]
      exact analyticOnNhd_const
  · by_cases hP : P (Lab.ysite y)
    · rw [truncAct_of_pos Lab H θ u hP]
      exact hcontP y hP θ hθ u hu
    · rw [truncAct_of_neg Lab H θ u hP]
      exact continuous_const
  · by_cases hP : P (Lab.ysite (y0 i))
    · rw [truncMark_of_pos Lab y0 Φ₀ G θ u hP]
      exact (hGmeasP θ i u hP).comp (measurable_restrConf _ Φ₀)
    · rw [truncMark_of_neg Lab y0 Φ₀ G θ u hP]
      exact measurable_const
  · by_cases hP : P (Lab.ysite (y0 i))
    · simp only [truncMark, hP, ↓reduceIte]
      exact hGbdP θ i u _ hP
    · simp only [truncMark, hP, ↓reduceIte, norm_zero]
      exact mul_nonneg (hF0 i) (Real.exp_pos _).le
  · by_cases hP : P (Lab.ysite (y0 i))
    · simp only [truncMark, hP, ↓reduceIte]
      exact hGholP i hP _
    · simp only [truncMark, hP, ↓reduceIte]
      exact analyticOnNhd_const
  · by_cases hP : P (Lab.ysite (y0 i))
    · rw [truncMark_of_pos Lab y0 Φ₀ G θ u hP]
      exact ((hGcontP i hP θ hθ u hu).comp (continuous_restrConf _ Φ₀)).continuousOn
    · rw [truncMark_of_neg Lab y0 Φ₀ G θ u hP]
      exact continuousOn_const

end Trunc

end Balaban.Fluctuation
