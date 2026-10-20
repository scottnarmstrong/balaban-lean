/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.Thm31CoeffAnalytic

/-!
# Label activities bundled at the configuration restricted to the blocks of the label

A family of activities `H y Φ` that is measurable and bounded in the configuration `Φ` of the
block variables, but whose dependence on `Φ` only through the blocks of the label `y` is not known,
is bundled into a `LabelAct` by evaluating it at the configuration restricted to the blocks of `y`
(`restrConf`: `Φ` on the blocks of `y`, a fixed reference configuration `Φ₀` off them).  The
bundled activity depends on `Φ` only through the blocks of `y` by construction, and it agrees with
`H y` wherever `H y` itself depends only on those blocks (`labelActRestr_H_of_dep`).  This is the
bundling of the activities of the new level recomputed on a background generating set (route
R-LOC, L4-3): the clauses (A1), (A2), (A4) read the bundle on the analyticity chart, and the
identity with the step's coefficient (A5) passes through the step's own locality.

* `restrConf`, `restrConf_eq_of_agree`, `restrConf_agree`, `measurable_restrConf`,
  `continuous_restrConf`;
* `labelActRestr`: the bundled activity; `labelActRestr_H`, `labelActRestr_H_of_dep`;
* `paramMarkFamily_restr`: the record `ParamMarkFamily` for the bundled activities of a parameter
  family, from the analyticity of `H` in the parameters at every configuration, its continuity in
  the configuration, and the fields of the marks.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Localization Balaban.Polymer MeasureTheory

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {m₀ j : ℕ} {Ω : Set (CTorus d L N₁ m₁ K)}

local notation "𝔅" => CubeB (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ j Ω

section Restr

open Classical in
/-- **The configuration restricted to a set `S` of blocks**: `Φ` on the blocks of `S`, the
reference configuration `Φ₀` off them. -/
noncomputable def restrConf {Ωb : 𝔅 → Type*} (S : Finset 𝔅) (Φ₀ Φ : ∀ b : 𝔅, Ωb b) : ∀ b : 𝔅, Ωb b :=
  fun b : 𝔅 => if b ∈ S then Φ b else Φ₀ b

omit [NeZero N₁] [NeZero L] in
theorem restrConf_eq_of_agree {Ωb : 𝔅 → Type*} {S : Finset 𝔅} (Φ₀ : ∀ b : 𝔅, Ωb b) {Φ Φ' : ∀ b : 𝔅, Ωb b}
    (h : ∀ b ∈ S, Φ b = Φ' b) : restrConf S Φ₀ Φ = restrConf S Φ₀ Φ' := by
  classical
  funext b
  unfold restrConf
  split_ifs with hb
  · exact h b hb
  · rfl

omit [NeZero N₁] [NeZero L] in
/-- The restricted configuration agrees with `Φ` on the blocks of `S`. -/
theorem restrConf_agree {Ωb : 𝔅 → Type*} (S : Finset 𝔅) (Φ₀ Φ : ∀ b : 𝔅, Ωb b) :
    ∀ b ∈ S, restrConf S Φ₀ Φ b = Φ b := by
  classical
  intro b hb
  unfold restrConf
  simp [hb]

omit [NeZero N₁] [NeZero L] in
theorem measurable_restrConf {Ωb : 𝔅 → Type*} [∀ b, MeasurableSpace (Ωb b)] (S : Finset 𝔅) (Φ₀ : ∀ b : 𝔅, Ωb b) :
    Measurable (restrConf S Φ₀) := by
  classical
  refine measurable_pi_iff.2 fun b => ?_
  unfold restrConf
  by_cases hb : b ∈ S
  · simp only [hb, ite_true]
    exact measurable_pi_apply b
  · simp only [hb, ite_false]
    exact measurable_const

omit [NeZero N₁] [NeZero L] in
theorem continuous_restrConf {Ωb : 𝔅 → Type*} [∀ b, TopologicalSpace (Ωb b)] (S : Finset 𝔅) (Φ₀ : ∀ b : 𝔅, Ωb b) :
    Continuous (restrConf S Φ₀) := by
  classical
  refine continuous_pi fun b => ?_
  unfold restrConf
  by_cases hb : b ∈ S
  · simp only [hb, ite_true]
    exact continuous_apply b
  · simp only [hb, ite_false]
    exact continuous_const

end Restr

section Bundle

variable {Lb : Type*} [Fintype Lb]

open Classical in
/-- **The activities bundled at the restricted configuration**: the label `y` has the activity
`H y` at the configuration restricted to the blocks of `y` (`Φ₀` off them); measurable from the
measurability of `H y`, bounded by the bound of `H y` at every configuration, with the entropy of
the labels. -/
noncomputable def labelActRestr {Ωb : 𝔅 → Type*} [∀ b, MeasurableSpace (Ωb b)]
    (Lab : CubeLabels m₀ j Ω Lb) {εH κH κ0 Kc : ℝ}
    (Φ₀ : ∀ b : 𝔅, Ωb b) (H : Lb → (∀ b : 𝔅, Ωb b) → ℂ) (hmeas : ∀ y, Measurable (H y))
    (hbd : ∀ y Φ, ‖H y Φ‖ ≤ εH * Real.exp (-κH * Lab.dl y))
    (hent : ∀ b : 𝔅, ∑ y : Lb, (if box b.1 (cellSide L m₀ m₁ j) ⊆ Lab.ysite y then
      Real.exp (-κ0 * Lab.dl y) else 0) ≤ Kc) :
    LabelAct Lab Ωb εH κH κ0 Kc where
  H y Φ := H y (restrConf (blocksOf m₀ j Ω (Lab.ysite y)) Φ₀ Φ)
  meas y := (hmeas y).comp (measurable_restrConf _ Φ₀)
  dep y _ _ h := congrArg (H y) (restrConf_eq_of_agree Φ₀ h)
  bound y _ := hbd y _
  entropy := hent

open Classical in
theorem labelActRestr_H {Ωb : 𝔅 → Type*} [∀ b, MeasurableSpace (Ωb b)]
    (Lab : CubeLabels m₀ j Ω Lb) {εH κH κ0 Kc : ℝ}
    (Φ₀ : ∀ b : 𝔅, Ωb b) (H : Lb → (∀ b : 𝔅, Ωb b) → ℂ) (hmeas : ∀ y, Measurable (H y))
    (hbd : ∀ y Φ, ‖H y Φ‖ ≤ εH * Real.exp (-κH * Lab.dl y))
    (hent : ∀ b : 𝔅, ∑ y : Lb, (if box b.1 (cellSide L m₀ m₁ j) ⊆ Lab.ysite y then
      Real.exp (-κ0 * Lab.dl y) else 0) ≤ Kc) (y : Lb) (Φ : ∀ b : 𝔅, Ωb b) :
    (labelActRestr Lab Φ₀ H hmeas hbd hent).H y Φ =
      H y (restrConf (blocksOf m₀ j Ω (Lab.ysite y)) Φ₀ Φ) := rfl

open Classical in
/-- **Where the activity of a label depends only on the blocks of the label, the bundle is the
activity**. -/
theorem labelActRestr_H_of_dep {Ωb : 𝔅 → Type*} [∀ b, MeasurableSpace (Ωb b)]
    (Lab : CubeLabels m₀ j Ω Lb) {εH κH κ0 Kc : ℝ}
    (Φ₀ : ∀ b : 𝔅, Ωb b) (H : Lb → (∀ b : 𝔅, Ωb b) → ℂ) (hmeas : ∀ y, Measurable (H y))
    (hbd : ∀ y Φ, ‖H y Φ‖ ≤ εH * Real.exp (-κH * Lab.dl y))
    (hent : ∀ b : 𝔅, ∑ y : Lb, (if box b.1 (cellSide L m₀ m₁ j) ⊆ Lab.ysite y then
      Real.exp (-κ0 * Lab.dl y) else 0) ≤ Kc) {y : Lb}
    (hdep : DepOn (blocksOf m₀ j Ω (Lab.ysite y)) (H y))
    (Φ : ∀ b : 𝔅, Ωb b) : (labelActRestr Lab Φ₀ H hmeas hbd hent).H y Φ = H y Φ :=
  hdep _ _ (restrConf_agree _ Φ₀ Φ)

end Bundle

section Family

variable {Lb : Type*} [Fintype Lb] {ι : Type*} [Fintype ι]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

omit [Fintype ι] in
open Classical in
/-- **`ParamMarkFamily` for activities bundled at the restricted configuration.**  For a parameter
family of activities `H θ u y` measurable and bounded at every parameter, analytic in `(θ, u)` on
`V × 𝒰` at every configuration and continuous in the configuration for `(θ, u) ∈ V × 𝒰`, the
bundles `labelActRestr … (H θ u)` together with marks `G` with the fields of a `ParamMarkFamily`
(measurable, bounded, analytic on `V × 𝒰` and continuous on the carrier `Q`) form a
`ParamMarkFamily` over `V`, `𝒰`, `Q`. -/
theorem paramMarkFamily_restr {Ωb : 𝔅 → Type*} [∀ b, MeasurableSpace (Ωb b)]
    [∀ b, TopologicalSpace (Ωb b)] (μ : ∀ b, Measure (Ωb b)) [∀ b, IsProbabilityMeasure (μ b)]
    (Lab : CubeLabels m₀ j Ω Lb) {εH κH κ0 Kc : ℝ} (Φ₀ : ∀ b : 𝔅, Ωb b)
    (H : E → ℂ → Lb → (∀ b : 𝔅, Ωb b) → ℂ) (hmeas : ∀ θ u y, Measurable (H θ u y))
    (hbd : ∀ θ u y Φ, ‖H θ u y Φ‖ ≤ εH * Real.exp (-κH * Lab.dl y))
    (hent : ∀ b : 𝔅, ∑ y : Lb, (if box b.1 (cellSide L m₀ m₁ j) ⊆ Lab.ysite y then
      Real.exp (-κ0 * Lab.dl y) else 0) ≤ Kc)
    (y0 : ι → Lb) (G : E → ι → ℂ → (∀ b : 𝔅, Ωb b) → ℂ) (κG : ℝ) (F0 : ι → ℝ)
    {V : Set E} {𝒰 : Set ℂ} {Q : Set (∀ b : 𝔅, Ωb b)}
    (hV : IsOpen V) (hU : IsOpen 𝒰) (hseg : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → (s : ℂ) ∈ 𝒰)
    (hQ : IsCompact Q) (hQm : MeasurableSet Q) (hcar : ∀ᵐ Φ ∂(Measure.pi μ), Φ ∈ Q)
    (hholH : ∀ y Φ, AnalyticOnNhd ℂ (fun p : E × ℂ => H p.1 p.2 y Φ) (V ×ˢ 𝒰))
    (hcontH : ∀ y, ∀ θ ∈ V, ∀ u ∈ 𝒰, Continuous (H θ u y))
    (hGmeas : ∀ θ i u, Measurable (G θ i u))
    (hGbd : ∀ θ i u Φ, ‖G θ i u Φ‖ ≤ F0 i * Real.exp (-κG * Lab.dl (y0 i)))
    (hholG : ∀ i, ∀ Φ ∈ Q, AnalyticOnNhd ℂ (fun p : E × ℂ => G p.1 i p.2 Φ) (V ×ˢ 𝒰))
    (hcontG : ∀ i, ∀ θ ∈ V, ∀ u ∈ 𝒰, ContinuousOn (G θ i u) Q) :
    ParamMarkFamily μ Lab
      (fun θ u => labelActRestr Lab Φ₀ (H θ u) (hmeas θ u) (hbd θ u) hent) y0 G κG F0 V 𝒰 Q where
  isOpenV := hV
  isOpenU := hU
  seg := hseg
  compact := hQ
  measQ := hQm
  carried := hcar
  meas := hGmeas
  bound := hGbd
  holA y _ _ := hholH y _
  holG := hholG
  contA y θ hθ u hu :=
    ((hcontH y θ hθ u hu).comp (continuous_restrConf _ Φ₀)).continuousOn
  contG := hcontG

end Family

end Balaban.Fluctuation
