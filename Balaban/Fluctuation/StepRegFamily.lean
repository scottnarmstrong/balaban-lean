/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.StepObs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# `C¹` families from joint `C¹` regularity on the ray region

A function `f(s, ψ̂)` which is `C¹` in the joint variable near every point with `|s| ‖ψ̂‖ < p⁺`
(`p₁ < p⁺`) gives, truncated to the support `{χ_fl = 1}` of `ν_{p₁}`, a `C¹` family on an open
neighbourhood of `[0,1]` in the sense of `IsC1Family`, bounded with its derivative
(`isC1Family_trunc`; the model is `isC1Family_WVT`).  `exists_open_contDiffOn` produces the open
set on which a function is `C¹` from the pointwise statement.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban.SmallField.Def6 Balaban.Background Balaban.Multiscale Balaban.Localization
  Balaban.SmallField Finset MeasureTheory Set

/-- A function which is `C¹` at every point of a set is `C¹` on an open set containing it. -/
theorem exists_open_contDiffOn {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F} {T : Set E}
    (h : ∀ y ∈ T, ContDiffAt ℝ 1 f y) : ∃ O : Set E, IsOpen O ∧ ContDiffOn ℝ 1 f O ∧ T ⊆ O := by
  refine ⟨{y | ContDiffAt ℝ 1 f y}, ?_, fun y (hy : ContDiffAt ℝ 1 f y) => hy.contDiffWithinAt, h⟩
  rw [isOpen_iff_mem_nhds]
  intro y (hy : ContDiffAt ℝ 1 f y)
  have h1 : (1 : WithTop ℕ∞) ≠ ((⊤ : ℕ∞) : WithTop ℕ∞) := by simp
  exact hy.eventually h1

namespace StepSetting

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}
  (S : StepSetting d L N₁ m₁ k N ϱ)

/-- The truncation of `f(s, ψ̂)` to the support of `ν_{p₁}`. -/
noncomputable def truncF (f : ℝ × S.E → ℂ) (s : ℝ) (x : S.E) : ℂ :=
  open Classical in if chiFl S.U N S.p₁ x = 1 then f (s, x) else 0

/-- The `s`-derivative of the truncation. -/
noncomputable def dtruncF (f : ℝ × S.E → ℂ) (s : ℝ) (x : S.E) : ℂ :=
  open Classical in if chiFl S.U N S.p₁ x = 1 then (fderiv ℝ f (s, x)) (1, 0) else 0

/-- **A jointly `C¹` function gives a `C¹` family on a neighbourhood of `[0,1]`**, bounded with its
derivative on the support of `ν_{p₁}` (needs `p₁ < p⁺`). -/
theorem isC1Family_trunc {f : ℝ × S.E → ℂ} {pp : ℝ} (hp₁ : 0 < S.p₁) (hlt : S.p₁ < pp)
    (hCD1 : ∀ q : ℝ × S.E, |q.1| * ‖q.2‖ < pp → ContDiffAt ℝ 1 f q) :
    ∃ U : Set ℝ, IsC1Family U (S.truncF f) (S.dtruncF f) := by
  classical
  set ε : ℝ := (pp / S.p₁ - 1) / 2 with hε
  have hε0 : 0 < ε := by
    have : 1 < pp / S.p₁ := by rw [lt_div_iff₀ hp₁]; linarith
    rw [hε]; linarith
  have hεp : (1 + ε) * S.p₁ < pp := by
    have h1 : (1 + ε) * S.p₁ = (S.p₁ + pp) / 2 := by
      rw [hε]; field_simp; ring
    rw [h1]; linarith
  have hΩ : ∀ s ∈ Set.Icc (-ε) (1 + ε), ∀ x : S.E, ‖x‖ ≤ S.p₁ → |s| * ‖x‖ < pp := by
    intro s hs x hx
    have hs' : |s| ≤ 1 + ε := abs_le.2 ⟨by linarith [hs.1], hs.2⟩
    calc |s| * ‖x‖ ≤ (1 + ε) * S.p₁ := mul_le_mul hs' hx (norm_nonneg _) (by linarith)
      _ < pp := hεp
  have hCD : ∀ s ∈ Set.Icc (-ε) (1 + ε), ∀ x : S.E, ‖x‖ ≤ S.p₁ →
      ContDiffAt ℝ 1 f (s, x) := fun s hs x hx => hCD1 (s, x) (hΩ s hs x hx)
  have hball : ∀ x : S.E, chiFl S.U N S.p₁ x = 1 → ‖x‖ ≤ S.p₁ := fun x hx =>
    ((chiFl_eq_one_iff hp₁ x).1 hx).le
  have hIcc : ∀ s ∈ Set.Ioo (-ε) (1 + ε), s ∈ Set.Icc (-ε) (1 + ε) :=
    fun s hs => ⟨hs.1.le, hs.2.le⟩
  have hcont : ∀ s ∈ Set.Icc (-ε) (1 + ε), ∀ x : S.E, ‖x‖ ≤ S.p₁ →
      ContinuousAt f (s, x) := fun s hs x hx => (hCD s hs x hx).continuousAt
  have hcontd : ∀ s ∈ Set.Icc (-ε) (1 + ε), ∀ x : S.E, ‖x‖ ≤ S.p₁ →
      ContinuousAt (fun q : ℝ × S.E => (fderiv ℝ f q) (1, 0)) (s, x) := by
    intro s hs x hx
    have h1 : ContDiffAt ℝ 0 (fderiv ℝ f) (s, x) :=
      (hCD s hs x hx).fderiv_right (m := 0) (by norm_num)
    have h2 : ContinuousAt (fderiv ℝ f) (s, x) := h1.continuousAt
    exact (ContinuousLinearMap.apply ℝ ℂ ((1 : ℝ), (0 : S.E))).continuous.continuousAt.comp h2
  have hslice : ∀ s ∈ Set.Icc (-ε) (1 + ε), ∀ x : S.E, ‖x‖ ≤ S.p₁ →
      ContinuousAt (fun x : S.E => f (s, x)) x := fun s hs x hx =>
    (hcont s hs x hx).comp (Continuous.prodMk_right s).continuousAt
  have hslice' : ∀ s ∈ Set.Icc (-ε) (1 + ε), ∀ x : S.E, ‖x‖ ≤ S.p₁ →
      ContinuousAt (fun x : S.E => (fderiv ℝ f (s, x)) (1, 0)) x := fun s hs x hx =>
    (hcontd s hs x hx).comp (Continuous.prodMk_right s).continuousAt
  have hmeasB : MeasurableSet {x : S.E | chiFl S.U N S.p₁ x = 1} :=
    (measurable_chiFl S.p₁) (measurableSet_singleton 1)
  refine ⟨Set.Ioo (-ε) (1 + ε), ?_⟩
  refine
    { isOpen := isOpen_Ioo
      Icc_subset := fun s hs => ⟨by linarith [hs.1], by linarith [hs.2]⟩
      measurable := ?_
      measurable' := ?_
      hasDerivAt := ?_
      continuousOn := ?_
      bound := ?_ }
  · intro s hs
    have hs' := hIcc s hs
    have hpw : S.truncF f s = Set.piecewise {x : S.E | chiFl S.U N S.p₁ x = 1}
        (fun x => f (s, x)) 0 := by
      funext x
      by_cases hx : chiFl S.U N S.p₁ x = 1
      · simp [truncF, Set.piecewise, hx]
      · simp [truncF, Set.piecewise, hx]
    rw [hpw]
    refine ContinuousOn.measurable_piecewise (fun x hx => ?_) continuousOn_const hmeasB
    exact (hslice s hs' x (hball x hx)).continuousWithinAt
  · intro s hs
    have hs' := hIcc s hs
    have hpw : S.dtruncF f s = Set.piecewise {x : S.E | chiFl S.U N S.p₁ x = 1}
        (fun x => (fderiv ℝ f (s, x)) (1, 0)) 0 := by
      funext x
      by_cases hx : chiFl S.U N S.p₁ x = 1
      · simp [dtruncF, Set.piecewise, hx]
      · simp [dtruncF, Set.piecewise, hx]
    rw [hpw]
    refine ContinuousOn.measurable_piecewise (fun x hx => ?_) continuousOn_const hmeasB
    exact (hslice' s hs' x (hball x hx)).continuousWithinAt
  · intro x s hs
    have hs' := hIcc s hs
    by_cases hx : chiFl S.U N S.p₁ x = 1
    · have hfun : (fun r => S.truncF f r x) = fun r => f (r, x) := by
        funext r; simp [truncF, hx]
      have hd : DifferentiableAt ℝ f (s, x) := (hCD s hs' x (hball x hx)).differentiableAt
        (by simp)
      have h1 : HasDerivAt (fun r : ℝ => f (r, x)) ((fderiv ℝ f (s, x)) (1, 0)) s := by
        have hp : HasDerivAt (fun r : ℝ => ((r, x) : ℝ × S.E)) ((1 : ℝ), (0 : S.E)) s :=
          (hasDerivAt_id s).prodMk (hasDerivAt_const s x)
        exact hd.hasFDerivAt.comp_hasDerivAt s hp
      rw [hfun]
      simp only [dtruncF, hx, ↓reduceIte]
      exact h1
    · simp only [truncF, dtruncF, hx, ↓reduceIte]
      exact hasDerivAt_const s 0
  · intro x
    by_cases hx : chiFl S.U N S.p₁ x = 1
    · have hfun : (fun s => S.dtruncF f s x) = fun s => (fderiv ℝ f (s, x)) (1, 0) := by
        funext s; simp [dtruncF, hx]
      rw [hfun]
      refine fun s hs => ?_
      have hs' : s ∈ Set.Icc (-ε) (1 + ε) := ⟨by linarith [hs.1], by linarith [hs.2]⟩
      have := (hcontd s hs' x (hball x hx)).comp (f := fun s : ℝ => ((s, x) : ℝ × S.E))
        (continuous_id.prodMk continuous_const).continuousAt
      exact this.continuousWithinAt
    · have : (fun s => S.dtruncF f s x) = fun _ => 0 := by
        funext s; simp [dtruncF, hx]
      rw [this]
      exact continuousOn_const
  · have hKc : IsCompact (Set.Icc (-ε) (1 + ε) ×ˢ Metric.closedBall (0 : S.E) S.p₁) :=
      isCompact_Icc.prod (isCompact_closedBall _ _)
    have hKm : ∀ q ∈ Set.Icc (-ε) (1 + ε) ×ˢ Metric.closedBall (0 : S.E) S.p₁,
        q.1 ∈ Set.Icc (-ε) (1 + ε) ∧ ‖q.2‖ ≤ S.p₁ := fun q hq =>
      ⟨hq.1, by simpa using hq.2⟩
    obtain ⟨M₀, hM₀⟩ := hKc.exists_bound_of_continuousOn
      (f := f) (fun q hq => (hcont q.1 (hKm q hq).1 q.2 (hKm q hq).2).continuousWithinAt)
    obtain ⟨M₁, hM₁⟩ := hKc.exists_bound_of_continuousOn
      (f := fun q : ℝ × S.E => (fderiv ℝ f q) (1, 0))
      (fun q hq => (hcontd q.1 (hKm q hq).1 q.2 (hKm q hq).2).continuousWithinAt)
    refine ⟨max M₀ 0 + max M₁ 0, fun x s hs => ?_⟩
    have hs' := hIcc s hs
    by_cases hx : chiFl S.U N S.p₁ x = 1
    · have hq : (s, x) ∈ Set.Icc (-ε) (1 + ε) ×ˢ Metric.closedBall (0 : S.E) S.p₁ :=
        ⟨hs', by simpa using hball x hx⟩
      refine ⟨?_, ?_⟩
      · simp only [truncF, hx, ↓reduceIte]
        exact (hM₀ _ hq).trans ((le_max_left _ _).trans
          (le_add_of_nonneg_right (le_max_right _ _)))
      · simp only [dtruncF, hx, ↓reduceIte]
        exact (hM₁ _ hq).trans ((le_max_left _ _).trans
          (le_add_of_nonneg_left (le_max_right _ _)))
    · simp only [truncF, dtruncF, hx, ↓reduceIte, norm_zero]
      exact ⟨by positivity, by positivity⟩

end StepSetting

end Balaban.Fluctuation
