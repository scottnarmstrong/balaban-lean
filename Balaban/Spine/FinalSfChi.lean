/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Spine.FinalSfCont
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Measurability of the small-field characteristic function

A6-3 (a), item 1: `χ_k(Y)` (with the extended direction stencil `chiKLong`) is Borel in the block
field: the cube condition `ChiKProp` is Borel by Lemma II.3.3 (`measurableSet_chiKProp`) and the
direction test `DataDirClose` is a finite conjunction of strict inequalities between continuous
functions.
-/

@[expose] public section

open MeasureTheory Balaban Balaban.Multiscale Balaban.Background Balaban.LargeField
  Balaban.LargeField.Def7

namespace Balaban.RootFSpine

section Cube

variable {d M1 N₁ L N : ℕ} [NeZero L] [NeZero M1] [NeZero N₁]

/-- The direction test `DataDirClose` of the lifted configuration is a Borel condition. -/
theorem measurableSet_dataDirClose {q : ℕ} (h : Fin N → ℝ) (ν δ : ℝ)
    (S : Finset (Torus d (M1 * N₁ * L ^ q))) :
    MeasurableSet {ψ : BlockCfg d (M1 * N₁) L q q N | DataDirClose
      (fun x i => (ψ (jBlock d L (M1 * N₁) q q x) i : ℂ)) (fun i => (h i : ℂ)) ν S δ} := by
  classical
  unfold DataDirClose
  by_cases hν : 0 < ν
  · simp only [hν, forall_true_left, Set.ofPred_and]
    refine MeasurableSet.inter ?_ (MeasurableSet.const _)
    have e : {ψ : BlockCfg d (M1 * N₁) L q q N | ∀ x ∈ S, vn (fun i =>
          (ψ (jBlock d L (M1 * N₁) q q x) i : ℂ) - (h i : ℂ)) < δ / Real.sqrt ν} =
        ⋂ x ∈ S, {ψ : BlockCfg d (M1 * N₁) L q q N | vn (fun i =>
          (ψ (jBlock d L (M1 * N₁) q q x) i : ℂ) - (h i : ℂ)) < δ / Real.sqrt ν} := by
      ext ψ; simp
    rw [e]
    refine Finset.measurableSet_biInter S fun x _ => measurableSet_lt ?_ measurable_const
    refine (Background.continuous_vn.comp (continuous_pi fun i => ?_)).measurable
    exact (Complex.continuous_ofReal.comp ((continuous_apply i).comp
      (continuous_apply (jBlock d L (M1 * N₁) q q x)))).sub continuous_const
  · simp [hν]

/-- `{χ^ρ_q(□) = 1}` is Borel (Lemma II.3.3 and the direction test). -/
theorem measurableSet_chiKLongProp {q : ℕ} (a : ℕ → ℝ) (μ δ : ℝ) (h : Fin N → ℝ) (c n ρ : ℕ)
    (H : BgHyp d L q (minSep L M1) a μ) (y0 : Torus d n) :
    MeasurableSet {ψ : BlockCfg d (M1 * N₁) L q q N |
      ChiKLongProp (N₁ := N₁) (L := L) (M1 := M1) (q := q) a μ δ h c n ρ y0 ψ} := by
  unfold ChiKLongProp
  simp only [Set.ofPred_and]
  exact (measurableSet_chiKProp a μ δ h c n H y0).inter (measurableSet_dataDirClose h _ δ _)

theorem measurable_chiKLong {q : ℕ} (a : ℕ → ℝ) (μ δ : ℝ) (h : Fin N → ℝ) (c n ρ : ℕ)
    (H : BgHyp d L q (minSep L M1) a μ) (y0 : Torus d n) :
    Measurable (chiKLong (M1 := M1) (N₁ := N₁) (L := L) (q := q) (N := N) a μ δ h c n ρ y0) :=
  measurable_charFn (measurableSet_chiKLongProp a μ δ h c n ρ H y0)

end Cube

section Ctx

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {M K : ℕ} [NeZero M]
  [NeZero S.L] {N m₁ j : ℕ} {ϱ : ℝ} (C : SFCtx S n R M K N (j + 1) m₁ ϱ)
  (hv : EuclideanSpace ℝ (Fin N))

/-- **`χ_k(Y)` is Borel in the block field.** -/
theorem measurable_chiY
    (HB : BgHyp S.d S.L (j + 1) (minSep S.L C.geo.M1) C.weights (C.cs.mu (j + 1)))
    (Y : Set (Torus S.d (n (j + 1)))) :
    Measurable fun ψk : BlockAt S n M K (j + 1) → EuclideanSpace ℝ (Fin N) =>
      C.chiY Y ψk hv := by
  unfold SFCtx.chiY
  refine (measurable_cubeProd (fun y0 => measurable_chiKLong _ _ _ _ _ _ _ HB y0) _).comp ?_
  exact (continuous_pi fun _ => continuous_pi fun i =>
    (EuclideanSpace.proj i).continuous.comp (continuous_apply _)).measurable

end Ctx

end Balaban.RootFSpine
