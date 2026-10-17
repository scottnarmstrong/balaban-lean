/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.LocalClassDensityFamilyIdx

/-!
# The per-domain sum of the inherited labels (`LocalClassDensityFamilyIdxSum`)

The conditions `hnumH` (`classActivityFamily_labelAct`) and `hres` (`classActivity_hnumH_of_index`)
ask, on every domain `Y` of the activity family, for a bound on the sum over the inherited labels
`τ = (j, y, X)` of the class whose expansion has `Y` among its domains,
`∑_{τ : Y ∈ polyDom τ} 2 E₀ e^{-κ₀ d(X_τ)}`, by a constant `ε_C`.

* `X1_mem_polyDom`: the localization domain `X₁(τ)` of a label is a domain of its own expansion
  (the empty family of parameter cubes, `Y[∅] = X₁`).
* `classActivity_domainSum_ge`: hence the per-domain sum at `Y` is at least the sum over the labels
  with `X₁(τ) = Y`.

The labels with `X₁(τ) = Y` are many: if `X_τ` is one cube of index `C.m₀` and level `j` inside a
cell `c` of the level `k + 1`, then `d(X_τ) = 0` (`treeLenCovOne_box`) and `X₁(τ)` is the union of
the cover cubes of the level `k + 1` containing `c`, the same for all such labels.  Their number is
at least the number of points of the lattice of spacing `L` in `c`, of order `L^{(k + C.m₀ + m₁)d}`,
so the per-domain sum is at least `2 E₀` times that number.  With the class bound `boundE`
(`‖E(j, y, X)‖ ≤ E₀ e^{-κ d_j(X)}`, one constant `E₀` for all levels `j ≤ k` and all centres `y`),
no `ε_C` independent of `k` bounds it: the per-label bound of the class has no factor of the
volume, and a bound of the activity of a domain uniform in `k` needs the resummed inherited energy
(the sum over the centres and the domains of the old terms before the expansion, D3(b)).
-/

@[expose] public section

namespace Balaban.Fluctuation

open MeasureTheory Balaban Balaban.Localization Balaban.Multiscale
  Balaban.Background Balaban.SmallField Balaban.Polymer Finset

section DomainSum

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}

/-- **The localization domain of a label is a domain of its expansion**: `X₁ = Y[∅]`. -/
theorem X1_mem_polyDom (Gp : GeneratingSet d L (N₁ * L ^ m₁) K ϱ)
    (X₁f : Finset (CTorus d L N₁ m₁ K)) (m₀ j : ℕ) (𝒦X : Set (CTorus d L N₁ m₁ K)) :
    X1 Gp m₀ j 𝒦X ∈ polyDom Gp X₁f m₀ j 𝒦X := by
  classical
  unfold polyDom polymerDomains
  refine Finset.mem_image.2 ⟨∅, ?_, ?_⟩
  · simp [IsConnectedFamily]
  · simp [Ysites]

open Classical in
/-- **The per-domain sum is at least the sum over the labels with `X₁(τ) = Y`.**  For a finite
family of labels with nonnegative weights `w τ`, the sum of `w τ` over the labels whose expansion
has the domain `Y` is at least the sum over the labels whose localization domain is `Y`
(`X1_mem_polyDom`). -/
theorem classActivity_domainSum_ge {ι : Type*} [Fintype ι]
    (Gp : GeneratingSet d L (N₁ * L ^ m₁) K ϱ) (m₀ : ℕ) (jL : ι → ℕ)
    (X₁f : ι → Finset (CTorus d L N₁ m₁ K)) (𝒦X : ι → Set (CTorus d L N₁ m₁ K))
    (w : ι → ℝ) (hw : ∀ τ, 0 ≤ w τ) (Y : Set (CTorus d L N₁ m₁ K)) :
    (∑ τ, if X1 Gp m₀ (jL τ) (𝒦X τ) = Y then w τ else 0) ≤
      ∑ τ, if Y ∈ polyDom Gp (X₁f τ) m₀ (jL τ) (𝒦X τ) then w τ else 0 := by
  refine Finset.sum_le_sum fun τ _ => ?_
  by_cases h : X1 Gp m₀ (jL τ) (𝒦X τ) = Y
  · have hmem : Y ∈ polyDom Gp (X₁f τ) m₀ (jL τ) (𝒦X τ) := h ▸ X1_mem_polyDom Gp _ m₀ _ _
    rw [ite_eq_left h, ite_eq_left hmem]
  · rw [ite_eq_right h]
    split_ifs
    · exact hw τ
    · exact le_rfl

end DomainSum

end Balaban.Fluctuation
