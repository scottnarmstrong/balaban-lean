/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.DecCover

/-!
# The common-cover partition (VMOD-6 §1)

The cover of a generating set `F` partitions unity on every site of `Ω₁(F)`, with
`coverDenom ≥ 4⁻ᵈ`.  So the cover `coverOf F` is a partition of unity on `Ω₁(H)` for every
operator set `H` with `Ω₁(H) ⊆ Ω₁(F)`; no inclusion in the other direction is needed.  The corrected
replacement of the (false) reverse partition of `VMOD-5.md` §2 is the common cover `F♯` of the old
operator `H⁻` and the boundary operator `H^∂`, whose first domain lies in `Ω₁(H⁻) ∪ Ω_{k+1}` with
`Ω_{k+1} ⊆ Ω_K(F♯)` (formula (1.2) and the history inclusion).
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱ' : ℝ}

/-- **Standalone partition (VMOD-6 §1, last paragraph).**  If `Ω₁(H) ⊆ Ω₁(F)`, `F` is cube aligned
and `L ≥ 2`, the cover of `F` is a partition of unity on `Ω₁(H)` with denominator `≥ 4⁻ᵈ`. -/
theorem coverOf_partition_of_subset (hd : 0 < d) (hL : 2 ≤ L)
    {F : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} (hF : CubeAligned F m₁)
    {H : GeneratingSet d L (N₁ * L ^ m₁) K ϱ'} (hH : H.Ω 1 ⊆ F.Ω 1) :
    ∀ x ∈ H.Ω 1, ∑ q ∈ (coverOf F).cubeIdx, (coverOf F).chi q x = 1 ∧
      (1 / 4 : ℝ) ^ d ≤ coverDenom F x := by
  intro x hx
  obtain ⟨n, hn1, hnK, hxn⟩ := F.exists_layer (hH hx)
  exact ⟨sum_chi hF hL hn1 hnK hxn ⟨0, hd⟩,
    coverDenom_ge hF hL hn1 hnK hxn ⟨0, hd⟩ (Or.inl rfl)⟩

/-- **Corrected common-cover partition (VMOD-6 §1, (1.1)).**  `F` is the common generating set
(`F♯`), `Hm` the old operator (`H⁻`) and `Hb` the boundary operator (`H^∂`).  Source premises:
`Ω₁(Hm) = Ω₁(F)` (the lower domains of `F♯` are those of `H⁻`); every site of `Ω₁(Hb)` lies in
`Ω₁(Hm)` or in the history set `Ω` (`= Ω_{k+1}`), by formula (1.2); and the history inclusion
`Ω ⊆ Ω_K(F)` (`Ω_{k+1} ⊂ A`).  Then the cover of `F` is a partition of unity on `Ω₁(Hm)` and on
`Ω₁(Hb)`, with `coverDenom ≥ 4⁻ᵈ`, the same cover for both. -/
theorem commonCover_partition (hd : 0 < d) (hL : 2 ≤ L) (hK : 1 ≤ K)
    {F Hm Hb : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} (hF : CubeAligned F m₁)
    (hmF : Hm.Ω 1 = F.Ω 1)
    (Ω : Finset (CTorus d L N₁ m₁ K))
    (hb : ∀ x ∈ Hb.Ω 1, x ∈ Hm.Ω 1 ∨ x ∈ Ω) (hΩ : Ω ⊆ F.Ω K) :
    (∀ x ∈ Hm.Ω 1, ∑ q ∈ (coverOf F).cubeIdx, (coverOf F).chi q x = 1 ∧
      (1 / 4 : ℝ) ^ d ≤ coverDenom F x) ∧
    (∀ x ∈ Hb.Ω 1, ∑ q ∈ (coverOf F).cubeIdx, (coverOf F).chi q x = 1 ∧
      (1 / 4 : ℝ) ^ d ≤ coverDenom F x) := by
  refine ⟨coverOf_partition_of_subset hd hL hF hmF.le, ?_⟩
  refine coverOf_partition_of_subset hd hL hF ?_
  intro x hx
  rcases hb x hx with h | h
  · exact hmF ▸ h
  · exact F.Ω_antitone le_rfl hK (by omega) (hΩ h)

/-- **Inhabitation of the hypotheses of `commonCover_partition`**: take `Hm = Hb = F` and
`Ω = ∅`, for any cube-aligned `F`. -/
theorem commonCover_hyps_nonempty (F : GeneratingSet d L (N₁ * L ^ m₁) K ϱ) :
    Nonempty (F.Ω 1 = F.Ω 1 ∧ (∀ x ∈ F.Ω 1, x ∈ F.Ω 1 ∨ x ∈ (∅ : Finset (CTorus d L N₁ m₁ K))) ∧
      (∅ : Finset (CTorus d L N₁ m₁ K)) ⊆ F.Ω K) :=
  ⟨⟨rfl, fun _ h => Or.inl h, Finset.empty_subset _⟩⟩

end Balaban.Localization
