/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.StepTowerRotChainBirth
public import Balaban.SmallField.PolyDomOpt

/-!
# The label data of the class chain

The class chain takes, for its labels `τ = (j, y, X)` (`1 ≤ j ≤ k`, `y ∈ X` aligned to `L^j`,
`X ∈ 𝒟_j`), the polymers `XL τ = X ∪ □(y)` of the old terms, chosen families `𝒦X τ` of their
`π'_j`-cubes and connected structures of the optimal cost `d_j(XL τ)` meeting them (`hXL`, `h𝒦`,
`hopt`).  These are definitions of the class data, not premises: `XL τ` is the union of two polymers
of `𝒟_j` through `y` (`isPolyDom_union`, `isPolyDom_cubeAt`), and an optimal admissible triple
exists for every polymer (`exists_opt_of_isPolyDom`).

* `labelPoly`, `labelPoly_isPolyDom`, `exists_labelData`.
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Fluctuation Balaban.Multiscale Balaban.Background Balaban.Localization
  Balaban.SmallField Balaban.SmallField.Def6 Balaban.SmallField.Def6v2

variable {d L N₁ m₁ k : ℕ} [NeZero L] [NeZero N₁]

/-- **The polymer of the old term of a label** `τ = (j, y, X)`: `X ∪ □(y)`, `□(y)` the
`π'_j`-cube of side `L · cellSide j` centred at the cell of `y`. -/
def labelPoly (m₀ : ℕ) (τ : ℕ × CTorus d L N₁ m₁ (k + 1) × Set (CTorus d L N₁ m₁ (k + 1))) :
    Set (CTorus d L N₁ m₁ (k + 1)) :=
  τ.2.2 ∪ box (cbase (cellSide L m₀ m₁ τ.1) τ.2.1 - natT fun _ => L / 2 * cellSide L m₀ m₁ τ.1)
    (L * cellSide L m₀ m₁ τ.1)

/-- The polymer of a label is a polymer of `𝒟_j`. -/
theorem labelPoly_isPolyDom {m₀ : ℕ} (hN : L ^ m₀ ∣ N₁)
    {τ : ℕ × CTorus d L N₁ m₁ (k + 1) × Set (CTorus d L N₁ m₁ (k + 1))} (hjk : τ.1 ≤ k)
    (hX : IsPolyDom m₀ τ.1 τ.2.2) (hy : τ.2.1 ∈ τ.2.2) :
    IsPolyDom m₀ τ.1 (labelPoly m₀ τ) :=
  isPolyDom_union hX (isPolyDom_cubeAt hN (hjk.trans (Nat.le_succ k)) τ.2.1) hy (mem_cubeAt τ.2.1)

open Classical in
/-- **The label data of the class chain**: for the labels `𝒯E` of the levels `1 ≤ j ≤ k` there are
chosen families `𝒦X τ` of the polymers `XL τ = labelPoly m₀ τ` of the old terms with connected
structures of the optimal cost meeting them (the premises `hXL`, `h𝒦`, `hopt` of the chain). -/
theorem exists_labelData {m₀ : ℕ} (hN : L ^ m₀ ∣ N₁)
    {𝒯E : Finset (ℕ × CTorus d L N₁ m₁ (k + 1) × Set (CTorus d L N₁ m₁ (k + 1)))}
    (h𝒯 : 𝒯E = ((Finset.Icc 1 k) ×ˢ (Finset.univ : Finset (CTorus d L N₁ m₁ (k + 1) ×
        Set (CTorus d L N₁ m₁ (k + 1))))).filter
      (fun τ => Aligned (L ^ τ.1) τ.2.1 ∧ IsPolyDom m₀ τ.1 τ.2.2 ∧ τ.2.1 ∈ τ.2.2)) :
    ∃ 𝒦X : {τ // τ ∈ 𝒯E} → Set (CTorus d L N₁ m₁ (k + 1)),
      (∀ τ : {τ // τ ∈ 𝒯E}, ChosenOne m₀ τ.1.1 (labelPoly m₀ τ.1) (𝒦X τ)) ∧
      ∀ τ : {τ // τ ∈ 𝒯E}, ∃ (W₀ : Finset (CTorus d L N₁ m₁ (k + 1)))
        (E₀ : Finset (CTorus d L N₁ m₁ (k + 1) × CTorus d L N₁ m₁ (k + 1))),
        ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ labelPoly m₀ τ.1) ∧ MeetsOne m₀ τ.1.1 (𝒦X τ) W₀ ∧
          bondCost (scaleW L m₀ m₁ τ.1.1) E₀ = treeLenCovOne m₀ τ.1.1 (labelPoly m₀ τ.1) := by
  have H : ∀ τ : {τ // τ ∈ 𝒯E}, ∃ 𝒦 : Set (CTorus d L N₁ m₁ (k + 1)),
      ChosenOne m₀ τ.1.1 (labelPoly m₀ τ.1) 𝒦 ∧ ∃ (W₀ : Finset (CTorus d L N₁ m₁ (k + 1)))
        (E₀ : Finset (CTorus d L N₁ m₁ (k + 1) × CTorus d L N₁ m₁ (k + 1))),
        ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ labelPoly m₀ τ.1) ∧ MeetsOne m₀ τ.1.1 𝒦 W₀ ∧
          bondCost (scaleW L m₀ m₁ τ.1.1) E₀ = treeLenCovOne m₀ τ.1.1 (labelPoly m₀ τ.1) := by
    intro τ
    obtain ⟨-, hjk, -, hX, hy⟩ := classLabel_mem h𝒯 τ
    obtain ⟨𝒦, W, E, h1, h2, h3, h4, h5⟩ :=
      exists_opt_of_isPolyDom (labelPoly_isPolyDom hN hjk hX hy)
    exact ⟨𝒦, h1, W, E, h2, h3, h4, h5⟩
  choose 𝒦X h𝒦 hopt using H
  exact ⟨𝒦X, h𝒦, hopt⟩

end Balaban.Inhabited
