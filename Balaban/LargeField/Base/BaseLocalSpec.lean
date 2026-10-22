/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Base.BaseBgFunctional
public import Balaban.LargeField.Base.BaseCrossAgree

/-!
# The seed hull of a family of cells is deep when the cells are

For parameters supported on a family `Cs` of cells, the seed hull of the active closure is contained
in the `3 L^{k+1+m₁} + 2 L^{k+1}`-neighbourhood of the bases of `Cs` and the `L^{k+1}`-neighbourhood of the seed
(`seedHull_near`); hence if these neighbourhoods are deep in `Ω₁`, the hypothesis `hdeep` of
`bgFunctional_cutTo_invariant_deep` and `bgFunctional_coef_data_congr_deep` holds.
-/

@[expose] public section

namespace Balaban.LargeField.Base

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization Balaban.Fluctuation
  Balaban.LargeField

section Hull

variable {d L N₁ m₁ k : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}

theorem seedHull_near {C : DecCover d L N₁ m₁ (k + 1)} (hC : ∀ q ∈ C.cubeIdx, q.1 ≤ k + 1)
    {Dr : ℕ} {Cs : Finset ↥C.cubeIdx} {s : Dec2.DecParams C} (hsC : s ∈ supportedOn Cs)
    {seed : Finset (Balaban.Localization.CTorus d L N₁ m₁ (k + 1))}
    {y : Balaban.Localization.CTorus d L N₁ m₁ (k + 1)} (hy : y ∈ seedHull C Dr (Dec2.extS _ s) seed) :
    (∃ z ∈ seed, supDist z y ≤ L ^ (k + 1)) ∨
      ∃ i ∈ Cs, supDist (i : ℕ × Balaban.Localization.CTorus d L N₁ m₁ (k + 1)).2 y ≤
        3 * L ^ (k + 1 + m₁) + 2 * L ^ (k + 1) := by
  classical
  rcases Finset.mem_union.1 hy with h | h
  · right
    obtain ⟨z, hz, q, hq, x, hx, hxz⟩ := mem_actHull.1 h
    obtain ⟨hqc, q₀, hq₀, -, hq0q⟩ := mem_actComp.1 hq
    have hact : ActC C (Dec2.extS _ s) q := actC_of_reflTransGen hq₀ hq0q
    have hq0 : Dec2.extS C s q ≠ 0 := fun h0 =>
      hact.2 (Finset.prod_eq_zero (self_mem_Qset_cover C hqc) h0)
    have hqC : (⟨q, hqc⟩ : ↥C.cubeIdx) ∈ Cs := by
      by_contra hn
      apply hq0
      unfold Dec2.extS
      simp only [hqc, ↓reduceDIte]
      exact hsC _ hn
    refine ⟨⟨q, hqc⟩, hqC, ?_⟩
    have h1 := supDist_intBox_le' (L := L) (m₁ := m₁) (k := k) hx
    have h2 := crossPow_le (L := L) (m₁ := m₁) (k := k) (hC q hqc)
    have h3 : supDist z y ≤ L ^ (k + 1) :=
      supDist_le_of_sameCell (pow_pos (Nat.pos_of_ne_zero (NeZero.ne L)) _)
        (sameCell_of_jBlock_eq le_rfl hz)
    have h4 := supDist_triangle q.2 x z
    have h5 := supDist_triangle q.2 z y
    rw [supDist_comm q.2 x] at h4
    show supDist q.2 y ≤ _
    omega
  · left
    obtain ⟨z, hz, hzy⟩ := mem_nbhdSup.1 h
    exact ⟨z, hz, hzy⟩

/-- **The depth hypothesis of the locality theorems from the depth of the cells.**  If the
`3 L^{k+1+m₁} + 4 L^{k+1}`-neighbourhood of the base of each cell of `Cs` and the `3 L^{k+1}`-neighbourhood
of the seed lie in `Ω₁`, the seed hull of every parameter supported on `Cs` has depth `2 L^{k+1}`. -/
theorem hdeep_of_cells (G : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ)
    {Dr : ℕ} (Cs : Finset ↥(coverOf G).cubeIdx)
    (seed : Finset (Balaban.Localization.CTorus d L N₁ m₁ (k + 1)))
    (hCs : ∀ i ∈ Cs, ∀ w : Balaban.Localization.CTorus d L N₁ m₁ (k + 1),
      supDist (i : ℕ × Balaban.Localization.CTorus d L N₁ m₁ (k + 1)).2 w ≤
        3 * L ^ (k + 1 + m₁) + 4 * L ^ (k + 1) → w ∈ G.Ω 1)
    (hseed : ∀ z ∈ seed, ∀ w : Balaban.Localization.CTorus d L N₁ m₁ (k + 1),
      supDist z w ≤ 3 * L ^ (k + 1) → w ∈ G.Ω 1) :
    ∀ s ∈ supportedOn Cs, ∀ y ∈ seedHull (coverOf G) Dr (Dec2.extS _ s) seed,
      ∀ z : Balaban.Localization.CTorus d L N₁ m₁ (k + 1), supDist y z ≤ 2 * L ^ (k + 1) →
        z ∈ G.Ω 1 := by
  intro s hs y hy z hyz
  rcases seedHull_near (fun q hq => ((mem_cubeIdx G).1 hq).1.2) hs hy with ⟨w, hw, hwy⟩ | ⟨i, hi, hiy⟩
  · refine hseed w hw z ?_
    have := supDist_triangle w y z
    omega
  · refine hCs i hi z ?_
    have := supDist_triangle (i : ℕ × Balaban.Localization.CTorus d L N₁ m₁ (k + 1)).2 y z
    omega

end Hull

end Balaban.LargeField.Base
