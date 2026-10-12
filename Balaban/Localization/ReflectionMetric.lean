/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.ReflectedGeneratingSet
public import Balaban.Multiscale.PathMetric
import Mathlib.Tactic.Linarith

/-!
# Metric folding (NC3, Lemma R2)

The fold `F` of the doubled torus onto the cube does not increase the multiscale path distance:
`d_G(F p, F v) ≤ d_{G*}(p, v)` (`Balaban.Reflection.pathDist_fold_le`), with values in `ℝ≥0∞`, so
that the infinite-distance case is included: a finite reflected path folds to a finite original
path.  A reflected path is folded step by step; a step across a seam is deleted (the two endpoints
have the same image), every other step is a bond of `G` with the same cost, because the reflected
spacing is the spacing of `G` at the folded point (`spacing_reflectedGS`).
-/

@[expose] public section

namespace Balaban.Reflection

open Balaban Balaban.Multiscale Balaban.Localization

variable {d L N₀ k : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}
  {G : GeneratingSet d L N₀ k ϱ} {q s : ℕ} {c : Fin d → ℕ} [NeZero s]

/-- A point obtained from `x` by a step in `Λ` is `x` itself or a neighbour of `x`. -/
theorem eq_or_adj_of_step {Λ : Finset (Torus d (N₀ * L ^ k))} {x y : Torus d (N₀ * L ^ k)}
    {μ : Fin d} (h : y = stepUpT Λ x μ ∨ y = stepDnT Λ x μ) : y = x ∨ Adj x y := by
  classical
  rcases h with h | h
  · unfold stepUpT at h
    by_cases hm : x + Pi.single μ 1 ∈ Λ
    · simp only [hm, ↓reduceIte] at h
      exact Or.inr ⟨μ, Or.inl h⟩
    · simp only [hm, ↓reduceIte] at h
      exact Or.inl h
  · unfold stepDnT at h
    by_cases hm : x - Pi.single μ 1 ∈ Λ
    · simp only [hm, ↓reduceIte] at h
      refine Or.inr ⟨μ, Or.inr ?_⟩
      rw [h]; abel
    · simp only [hm, ↓reduceIte] at h
      exact Or.inl h

/-- One step of a reflected path folds to nothing or to one step. -/
theorem fold_adj (h : FoldSetting G q s c) {x y : Torus d (2 * s * L ^ q)}
    (hxy : Adj x y) :
    foldTo N₀ L k q s c x = foldTo N₀ L k q s c y ∨
      Adj (foldTo N₀ L k q s c x) (foldTo N₀ L k q s c y) := by
  have hs : 0 < s := h.s_pos
  have hS : 0 < s * L ^ q := Nat.mul_pos hs (L_pow_pos L _)
  have hnbr := fun (p : Torus d (2 * s * L ^ q)) (μ : Fin d) =>
    foldMap_nbr (c := c) (ℓ := N₀ * L ^ k) (two_mul_side L q s) hS h.side p μ
  obtain ⟨μ, hμ | hμ⟩ := hxy
  · -- y = x + e_μ
    have := hnbr x μ
    have hy : foldTo N₀ L k q s c y = foldMap (N₀ * L ^ k) (s * L ^ q) (2 * s * L ^ q) c
        (x + Pi.single μ 1) := by rw [hμ]; rfl
    have hmem : foldTo N₀ L k q s c y = stepUpT (cubeSet (N₀ * L ^ k) (s * L ^ q) c)
          (foldTo N₀ L k q s c x) μ ∨
        foldTo N₀ L k q s c y = stepDnT (cubeSet (N₀ * L ^ k) (s * L ^ q) c)
          (foldTo N₀ L k q s c x) μ := by
      rcases this with ⟨h1, -⟩ | ⟨h1, -⟩
      · exact Or.inl (hy.trans h1)
      · exact Or.inr (hy.trans h1)
    rcases eq_or_adj_of_step hmem with he | ha
    · exact Or.inl he.symm
    · exact Or.inr ha
  · -- x = y + e_μ
    have := hnbr y μ
    have hx : foldTo N₀ L k q s c x = foldMap (N₀ * L ^ k) (s * L ^ q) (2 * s * L ^ q) c
        (y + Pi.single μ 1) := by rw [hμ]; rfl
    have hmem : foldTo N₀ L k q s c x = stepUpT (cubeSet (N₀ * L ^ k) (s * L ^ q) c)
          (foldTo N₀ L k q s c y) μ ∨
        foldTo N₀ L k q s c x = stepDnT (cubeSet (N₀ * L ^ k) (s * L ^ q) c)
          (foldTo N₀ L k q s c y) μ := by
      rcases this with ⟨h1, -⟩ | ⟨h1, -⟩
      · exact Or.inl (hx.trans h1)
      · exact Or.inr (hx.trans h1)
    rcases eq_or_adj_of_step hmem with he | ha
    · exact Or.inl he
    · exact Or.inr ha.symm

/-- A reflected path folds to a path of no greater cost. -/
theorem pathCost_fold (h : FoldSetting G q s c) {x y : Torus d (2 * s * L ^ q)} {cost : ℝ}
    (hp : (reflectedGS G h).PathCost x y cost) :
    ∃ cost' : ℝ, cost' ≤ cost ∧
      G.PathCost (foldTo N₀ L k q s c x) (foldTo N₀ L k q s c y) cost' := by
  induction hp with
  | refl x _ => exact ⟨0, le_rfl, GeneratingSet.PathCost.refl _ (foldTo_mem_Ω_one h x)⟩
  | step x y z cst _ hadj _ ih =>
      obtain ⟨c', hc', hpath⟩ := ih
      have hb0 := (reflectedGS G h).bondCost_nonneg x y
      rcases fold_adj h hadj with he | ha
      · rw [he]
        exact ⟨c', by linarith, hpath⟩
      · refine ⟨G.bondCost (foldTo N₀ L k q s c x) (foldTo N₀ L k q s c y) + c', ?_,
          GeneratingSet.PathCost.step _ _ _ _ (foldTo_mem_Ω_one h x) ha hpath⟩
        have : G.bondCost (foldTo N₀ L k q s c x) (foldTo N₀ L k q s c y) =
            (reflectedGS G h).bondCost x y := by
          unfold GeneratingSet.bondCost
          rw [spacing_reflectedGS h, spacing_reflectedGS h]
        rw [this]
        linarith

/-- **Lemma R2 (metric folding).** `d_G(F p, F v) ≤ d_{G*}(p, v)` in `ℝ≥0∞`. -/
theorem pathDist_fold_le (h : FoldSetting G q s c) (x y : Torus d (2 * s * L ^ q)) :
    G.pathDist (foldTo N₀ L k q s c x) (foldTo N₀ L k q s c y) ≤
      (reflectedGS G h).pathDist x y := by
  unfold GeneratingSet.pathDist
  refine le_iInf₂ fun cost hcost => ?_
  obtain ⟨cost', hle, hpath⟩ := pathCost_fold h hcost
  exact (GeneratingSet.pathDist_le hpath).trans (ENNReal.ofReal_le_ofReal hle)

end Balaban.Reflection
