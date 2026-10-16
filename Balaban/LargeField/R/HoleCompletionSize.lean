/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.SizeModG1
public import Balaban.Fluctuation.SizeModUnion
import Mathlib.Tactic.Linarith

/-!
# The size of the completion of a label across a hole (blocker 3, leaf 0b)

`notes/phase1/VMOD-44.md` §5, leaf 0b.  Let `Ω` be the active region (fine sites), `X` a label with
admissible data `(𝒦, W, E)` for `(Ω, X)`, and `Y ⊇ X` its completion across a hole.  The modular
covering size of `Y` is controlled by the new active sites of `Y`, the *spill* `(Y ∩ Ω) ∖ X`:

* `dcovModE_completion_le_of_noSpill`: if `Y ∩ Ω ⊆ X` (the completion adds only hole sites), then
  `d^cov(Y mod Ω^c) ≤ d^cov(X mod Ω^c)`: no mark term, no extra tree.
* `dcovModE_completion_le_add`: in general, an admissible `(𝒦, W, E)` for `(Ω, X)` and a second
  family `𝒦'` of aligned `π'_j`-cubes inside `Y` covering the spill, with a connected structure
  `(W', E') ⊆ Y` that meets every cube of `𝒦'` and shares a vertex with `W` (the extra tree,
  through the hole if necessary), give
  `d^cov(Y mod Ω^c) ≤ M⁻¹ℓ_j⁻¹(|E| + |E'|)` in the weighted form
  `ofReal (bondCost E + bondCost E')`.
* `completion_cellCount_le`: the spill is paid: `n_π(Y ∩ Ω) ≤ c₁ (1 + d^cov(Y mod Ω^c))`
  (`G1_cellCount`), so a completion with spill of `s` cells has size `≥ s / c₁ - 1`.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Localization

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {m₀ j : ℕ}

omit [NeZero N₁] [NeZero L] in
/-- A completion that adds no active site does not increase the modular size. -/
theorem modAdmissible_of_noSpill {Ω X Y 𝒦 : Set (CTorus d L N₁ m₁ K)}
    {W : Finset (CTorus d L N₁ m₁ K)} {E : Finset (CTorus d L N₁ m₁ K × CTorus d L N₁ m₁ K)}
    (hXY : X ⊆ Y) (hsp : Y ∩ Ω ⊆ X) (h : ModAdmissible m₀ j Ω X 𝒦 W E) :
    ModAdmissible m₀ j Ω Y 𝒦 W E := by
  obtain ⟨hK, hcov, hc, hW, hm⟩ := h
  refine ⟨fun b hb => ⟨(hK b hb).1, (hK b hb).2.trans hXY⟩, ?_, hc, hW.trans hXY, hm⟩
  rintro z ⟨hzY, hzΩ⟩
  exact hcov ⟨hsp ⟨hzY, hzΩ⟩, hzΩ⟩

omit [NeZero N₁] [NeZero L] in
/-- **Leaf 0b, spill-free case.**  `X ⊆ Y` and `Y ∩ Ω ⊆ X` give
`d^cov(Y mod Ω^c) ≤ d^cov(X mod Ω^c)`. -/
theorem dcovModE_completion_le_of_noSpill {Ω X Y : Set (CTorus d L N₁ m₁ K)}
    (hXY : X ⊆ Y) (hsp : Y ∩ Ω ⊆ X) :
    dcovModE m₀ j Ω Y ≤ dcovModE m₀ j Ω X := by
  unfold dcovModE
  refine le_iInf fun 𝒦 => le_iInf fun W => le_iInf fun E => le_iInf fun h => ?_
  exact dcovModE_le_of_admissible (modAdmissible_of_noSpill hXY hsp h)

omit [NeZero N₁] [NeZero L] in
/-- **Leaf 0b, general case with the extra tree explicit.** -/
theorem dcovModE_completion_le_add {Ω X Y 𝒦 𝒦' : Set (CTorus d L N₁ m₁ K)}
    {W W' : Finset (CTorus d L N₁ m₁ K)}
    {E E' : Finset (CTorus d L N₁ m₁ K × CTorus d L N₁ m₁ K)}
    (hXY : X ⊆ Y) (h : ModAdmissible m₀ j Ω X 𝒦 W E)
    (hK' : ∀ b ∈ 𝒦', Aligned (cellSide L m₀ m₁ j) b ∧
      box b (L * cellSide L m₀ m₁ j) ⊆ Y)
    (hcov' : (Y ∩ Ω) \ X ⊆ ⋃ b ∈ 𝒦', box b (L * cellSide L m₀ m₁ j))
    (hc' : ConnStruct W' E') (hW'Y : (↑W' : Set (CTorus d L N₁ m₁ K)) ⊆ Y)
    (hm' : MeetsOne m₀ j 𝒦' W') (hz : ∃ z, z ∈ W ∧ z ∈ W') :
    dcovModE m₀ j Ω Y ≤ ENNReal.ofReal (bondCost (scaleW L m₀ m₁ j) E +
      bondCost (scaleW L m₀ m₁ j) E') := by
  obtain ⟨hK, hcov, hc, hW, hm⟩ := h
  have hadm : ModAdmissible m₀ j Ω Y (𝒦 ∪ 𝒦') (W ∪ W') (E ∪ E') := by
    refine ⟨?_, ?_, hc.union hc' hz, ?_, ?_⟩
    · rintro b (hb | hb)
      · exact ⟨(hK b hb).1, (hK b hb).2.trans hXY⟩
      · exact hK' b hb
    · rintro z ⟨hzY, hzΩ⟩
      by_cases hzX : z ∈ X
      · obtain ⟨b, hb, hzb⟩ := Set.mem_iUnion₂.1 (hcov ⟨hzX, hzΩ⟩)
        exact Set.mem_iUnion₂.2 ⟨b, Or.inl hb, hzb⟩
      · obtain ⟨b, hb, hzb⟩ := Set.mem_iUnion₂.1 (hcov' ⟨⟨hzY, hzΩ⟩, hzX⟩)
        exact Set.mem_iUnion₂.2 ⟨b, Or.inr hb, hzb⟩
    · intro x hx
      rcases Finset.mem_union.1 hx with hx | hx
      · exact hXY (hW hx)
      · exact hW'Y hx
    · rintro b (hb | hb)
      · obtain ⟨x, hx, hxb⟩ := hm b hb
        exact ⟨x, Finset.mem_union_left _ hx, hxb⟩
      · obtain ⟨x, hx, hxb⟩ := hm' b hb
        exact ⟨x, Finset.mem_union_right _ hx, hxb⟩
  refine (dcovModE_le_of_admissible hadm).trans (ENNReal.ofReal_le_ofReal ?_)
  exact bondCost_union_le (fun x y => by simp only [scaleW]; positivity) E E'

/-- **The spill is paid** (`G1_cellCount`): the number of `π_j`-cubes of `Y ∩ Ω` is at most
`c₁ (1 + d^cov(Y mod Ω^c))`. -/
theorem completion_cellCount_le (hN : L ^ m₀ ∣ N₁) (hj : j ≤ K) {Ω Y : Set (CTorus d L N₁ m₁ K)}
    (hY : DjMod m₀ j Ω Y) :
    (cellCount (cellSide L m₀ m₁ j) (Y ∩ Ω) : ℝ) ≤ c1 d L * (1 + dcovMod m₀ j Ω Y) :=
  G1_cellCount hN hj hY

end Balaban.Fluctuation
