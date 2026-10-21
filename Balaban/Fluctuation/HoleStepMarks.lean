/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.HoleStepSplit
public import Balaban.Localization.DecoupledCovAnalyticFull

/-!
# Marks of the fluctuation measure of the step on a region (P5 (3.2), P6 (4.32)–(4.34))

A function `T` of the fluctuation field `ψ̂` on the unit points of `Ω_{k+1}` (the coefficient of an
old boundary term, `RootFSpine.oldCoefLoc`) becomes a mark of the cluster expansion of the measure of
the step (`InterpMarksOn`, `marked_cubes_explicit`): a function of the variables of the cubes of the
block structure `HoleStep.prodSplit` (for any assignment `cb` of cubes, of any torus, to the unit
points), cut off outside the ball `|ψ̂_b| < r` of the unit points `b` it
reads (the measure lives on `|ψ̂_b| < p₁`, so the cutoff is inactive almost everywhere for `p₁ ≤ r`).

* `ungroup`, `ungroup_regroup`, `continuous_ungroup`, `measurable_ungroup`, `ungroup_congr`: the
  variables of the unit
  points from those of the cubes (the inverse of `regroup`);
* `HoleStep.markOf`: the cut-off mark of `T`;
* `HoleStep.markOf_dep`: it depends only on the cubes of the unit points that `T` reads;
* `HoleStep.markOf_bound`: it is bounded by the bound of `T` on the ball;
* `HoleStep.measurable_fill_ungroup`, `HoleStep.measurable_markOf`: the fluctuation field is
  measurable in the variables of the cubes, and the mark is measurable when `T` is continuous on
  the ball;
* `HoleStep.markOf_eq_of_mem`: it is `T` at the fluctuation field when the field lies in the ball.
-/

@[expose] public section

namespace Balaban.Fluctuation

open MeasureTheory Balaban.Localization Balaban.Multiscale

section Ungroup

variable {ι β X : Type*}

/-- **The variables of the members from those of the fibres** (the inverse of `regroup`). -/
def ungroup (c : ι → β) (Φ : ∀ b, {i // c i = b} → X) : ι → X := fun i => Φ (c i) ⟨i, rfl⟩

theorem ungroup_regroup (c : ι → β) (x : ι → X) : ungroup c (regroup c x) = x := rfl

theorem continuous_ungroup [TopologicalSpace X] (c : ι → β) :
    Continuous (ungroup (X := X) c) := by
  unfold ungroup
  fun_prop

theorem measurable_ungroup [MeasurableSpace X] (c : ι → β) :
    Measurable (ungroup (X := X) c) := by
  unfold ungroup
  fun_prop

/-- The variable of a member depends only on the fibre of the member. -/
theorem ungroup_congr (c : ι → β) {Φ Φ' : ∀ b, {i // c i = b} → X} {i : ι}
    (h : Φ (c i) = Φ' (c i)) : ungroup c Φ i = ungroup c Φ' i := by
  unfold ungroup
  rw [h]

end Ungroup

namespace HoleStep

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ ϱ' : ℝ}
  (S : HoleStep d L N₁ m₁ k N ϱ ϱ')

variable {Cb : Type*}

open Classical in
/-- **The cut-off mark of a function of the fluctuation field**: the function `T` at the fluctuation
field `fill inner ψin ψout` of the variables `ψin` of the cubes (`ungroup`), where the field lies in
the ball `|ψ̂_b| < r` at the unit points `b ∈ U₀`, and `0` elsewhere. -/
noncomputable def markOf (inner : Finset S.U)
    (cb : inner → Cb)
    (ψout : S.U → Fin N → ℂ) (U₀ : Finset S.U) (r : ℝ) (T : (S.U → Fin N → ℂ) → ℂ)
    (Φ : ∀ b, {u : inner // cb u = b} → Rn N) : ℂ :=
  if ∀ b ∈ U₀, vn (S.fill inner (ungroup cb Φ) ψout b) < r then
    T (S.fill inner (ungroup cb Φ) ψout) else 0

variable (inner : Finset S.U)
  (cb : inner → Cb)
  (ψout : S.U → Fin N → ℂ) (U₀ : Finset S.U) (r : ℝ) (T : (S.U → Fin N → ℂ) → ℂ)

theorem markOf_eq_of_mem (Φ : ∀ b, {u : inner // cb u = b} → Rn N)
    (h : ∀ b ∈ U₀, vn (S.fill inner (ungroup cb Φ) ψout b) < r) :
    S.markOf inner cb ψout U₀ r T Φ = T (S.fill inner (ungroup cb Φ) ψout) := by
  classical
  unfold markOf
  split_ifs
  rfl

open Classical in
/-- **The mark depends only on the cubes of the unit points read by `T`**: if `T` reads the field only
at the unit points of `U₀`, the mark depends only on the cubes of the integration variables of `U₀`. -/
theorem markOf_dep [DecidableEq Cb]
    (hT : ∀ ψ ψ' : S.U → Fin N → ℂ, (∀ b ∈ U₀, ψ b = ψ' b) → T ψ = T ψ') :
    Polymer.DepOn ((inner.attach.filter fun u : inner => (u : S.U) ∈ U₀).image cb)
      (S.markOf inner cb ψout U₀ r T) := by
  intro Φ Φ' h
  have hfill : ∀ b ∈ U₀, S.fill inner (ungroup cb Φ) ψout b = S.fill inner (ungroup cb Φ') ψout b := by
    intro b hb
    unfold fill
    by_cases hbi : b ∈ inner
    · simp only [hbi, ↓reduceDIte]
      have : ungroup cb Φ ⟨b, hbi⟩ = ungroup cb Φ' ⟨b, hbi⟩ := by
        refine ungroup_congr cb (h _ ?_)
        exact Finset.mem_image.2 ⟨⟨b, hbi⟩, Finset.mem_filter.2 ⟨Finset.mem_attach _ _, hb⟩, rfl⟩
      rw [this]
    · simp only [hbi, ↓reduceDIte]
  unfold markOf
  have hc : (∀ b ∈ U₀, vn (S.fill inner (ungroup cb Φ) ψout b) < r) ↔
      (∀ b ∈ U₀, vn (S.fill inner (ungroup cb Φ') ψout b) < r) :=
    forall₂_congr fun b hb => by rw [hfill b hb]
  split_ifs with h1 h2 h2
  · exact hT _ _ hfill
  · exact absurd (hc.1 h1) h2
  · exact absurd (hc.2 h2) h1
  · rfl

/-- **The mark is bounded by the bound of `T` on the ball.** -/
theorem markOf_bound {B : ℝ} (hB0 : 0 ≤ B)
    (hT : ∀ ψ : S.U → Fin N → ℂ, (∀ b ∈ U₀, vn (ψ b) < r) → ‖T ψ‖ ≤ B)
    (Φ : ∀ b, {u : inner // cb u = b} → Rn N) : ‖S.markOf inner cb ψout U₀ r T Φ‖ ≤ B := by
  classical
  unfold markOf
  split_ifs with h
  · exact hT _ h
  · simpa using hB0

/-- **The fluctuation field is measurable in the variables of the cubes.** -/
theorem measurable_fill_ungroup :
    Measurable fun Φ : ∀ b, {u : inner // cb u = b} → Rn N => S.fill inner (ungroup cb Φ) ψout := by
  classical
  refine measurable_pi_iff.2 fun b => measurable_pi_iff.2 fun i => ?_
  unfold fill
  by_cases hb : b ∈ inner
  · simp only [hb, ↓reduceDIte]
    have h1 : Measurable fun Φ : ∀ b, {u : inner // cb u = b} → Rn N => ungroup cb Φ ⟨b, hb⟩ := by
      unfold ungroup
      fun_prop
    have h2 : Measurable fun v : Rn N => v i :=
      (EuclideanSpace.proj (𝕜 := ℝ) i).continuous.measurable
    exact Complex.measurable_ofReal.comp (h2.comp h1)
  · simp only [hb, ↓reduceDIte]
    exact measurable_const

/-- **The mark is measurable** when `T` is continuous on the ball `|ψ̂_b| < r`, `b ∈ U₀`. -/
theorem measurable_markOf
    (hT : ContinuousOn T {ψ : S.U → Fin N → ℂ | ∀ b ∈ U₀, vn (ψ b) < r}) :
    Measurable (S.markOf inner cb ψout U₀ r T) := by
  classical
  set V := {ψ : S.U → Fin N → ℂ | ∀ b ∈ U₀, vn (ψ b) < r} with hV
  have hVo : IsOpen V := by
    have : V = ⋂ b ∈ U₀, {ψ : S.U → Fin N → ℂ | vn (ψ b) < r} := by
      ext ψ; simp [hV]
    rw [this]
    exact isOpen_biInter_finset fun b _ =>
      isOpen_lt (continuous_vn.comp (continuous_apply b)) continuous_const
  have hg : Measurable (V.piecewise T fun _ => 0) :=
    hT.measurable_piecewise continuousOn_const hVo.measurableSet
  have : S.markOf inner cb ψout U₀ r T =
      (V.piecewise T fun _ => 0) ∘ fun Φ => S.fill inner (ungroup cb Φ) ψout := by
    funext Φ
    simp only [markOf, Function.comp_apply, Set.piecewise, hV, Set.mem_ofPred_eq]
  rw [this]
  exact hg.comp (S.measurable_fill_ungroup inner cb ψout)

end HoleStep

end Balaban.Fluctuation
