/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.SizeModCore
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The all-eligible fine surrogate of the modular size (VMOD-43 §2)

The landed modular size `dcovModE` (`SizeModDefs.lean`) lets the connected structure meet a
*chosen* family of aligned boxes contained in the label `X` and covering `X ∩ Ω`.  The papers'
rule (P5 (1.34)) asks the tree to meet *every* cover cube that meets `X ∩ Ω`, with no
containment in `X`.  Here is its fine nearest-neighbour version.

* `eligibleCover m₀ j Ω X`: the aligned boxes `box b (L · cellSide)` meeting `X ∩ Ω`; no
  containment in `X` is required.
* `ModAdmissibleAll Ω X W E`: a nearest-neighbour connected structure `(W, E)` contained in `X`
  meeting every box of `eligibleCover`.
* `dcovModAllE` (in `[0, ∞]`) is the infimum of the bond cost `M⁻¹ℓ_j⁻¹ |E|` over such structures;
  `dcovModAll` is its real value.
* `dcovModE_le_dcovModAllE`: for a label `X ∈ 𝒟_j` (`IsDj`), `dcovModE ≤ dcovModAllE`.
* `dcovModAllE_ne_top_of_IsDj`: the surrogate is finite on `𝒟_j`.

The landed size is not changed.  The comparison with the papers' continuum size, the
identification of the aligned lift of the open cubes, and the compatibility of the components of
the complement are NOT proved here.  The upper comparison with the landed size is in
`SizeModAllCompare.lean`.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Localization

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] (m₀ j : ℕ)

/-- The eligible cover boxes of `X` at scale `j`: the aligned boxes of side `L · cellSide` that
meet `X ∩ Ω` (no condition that the box lies in `X`). -/
def eligibleCover (Ω X : Set (CTorus d L N₁ m₁ K)) : Set (CTorus d L N₁ m₁ K) :=
  {b | Aligned (cellSide L m₀ m₁ j) b ∧
    (box b (L * cellSide L m₀ m₁ j) ∩ (X ∩ Ω)).Nonempty}

/-- The data of the all-eligible size: a connected structure `Γ = (W, E)` contained in `X`
meeting every eligible box. -/
def ModAdmissibleAll (Ω X : Set (CTorus d L N₁ m₁ K))
    (W : Finset (CTorus d L N₁ m₁ K)) (E : Finset (CTorus d L N₁ m₁ K × CTorus d L N₁ m₁ K)) :
    Prop :=
  ConnStruct W E ∧ (↑W ⊆ X) ∧ MeetsOne m₀ j (eligibleCover m₀ j Ω X) W

/-- **The all-eligible fine size** `D_A(X mod Ω^c)`, in `[0, ∞]` (`+∞` if no admissible structure
exists).  The length of `Γ` is `M⁻¹ℓ_j⁻¹ |E|`, as for `dcovModE`. -/
noncomputable def dcovModAllE (Ω X : Set (CTorus d L N₁ m₁ K)) : ENNReal :=
  ⨅ (W : Finset (CTorus d L N₁ m₁ K))
    (E : Finset (CTorus d L N₁ m₁ K × CTorus d L N₁ m₁ K))
    (_ : ModAdmissibleAll m₀ j Ω X W E), ENNReal.ofReal (bondCost (scaleW L m₀ m₁ j) E)

/-- The real value of `dcovModAllE`. -/
noncomputable def dcovModAll (Ω X : Set (CTorus d L N₁ m₁ K)) : ℝ :=
  (dcovModAllE m₀ j Ω X).toReal

variable {m₀ j}

omit [NeZero N₁] [NeZero L] in
theorem dcovModAllE_le_of_admissible {Ω X : Set (CTorus d L N₁ m₁ K)}
    {W : Finset (CTorus d L N₁ m₁ K)} {E : Finset (CTorus d L N₁ m₁ K × CTorus d L N₁ m₁ K)}
    (h : ModAdmissibleAll m₀ j Ω X W E) :
    dcovModAllE m₀ j Ω X ≤ ENNReal.ofReal (bondCost (scaleW L m₀ m₁ j) E) :=
  iInf_le_of_le W (iInf_le_of_le E (iInf_le_of_le h le_rfl))

omit [NeZero N₁] [NeZero L] in
theorem dcovModAll_nonneg (Ω X : Set (CTorus d L N₁ m₁ K)) : 0 ≤ dcovModAll m₀ j Ω X :=
  ENNReal.toReal_nonneg

omit [NeZero N₁] [NeZero L] in
/-- The eligible family is monotone in the region. -/
theorem eligibleCover_mono {Ω Ω' X : Set (CTorus d L N₁ m₁ K)} (h : Ω ⊆ Ω') :
    eligibleCover m₀ j Ω X ⊆ eligibleCover m₀ j Ω' X := by
  rintro b ⟨hb, z, hz1, hz2, hz3⟩
  exact ⟨hb, z, hz1, hz2, h hz3⟩

omit [NeZero N₁] [NeZero L] in
/-- A larger region has a larger all-eligible size. -/
theorem dcovModAllE_mono_region {Ω Ω' X : Set (CTorus d L N₁ m₁ K)} (h : Ω ⊆ Ω') :
    dcovModAllE m₀ j Ω X ≤ dcovModAllE m₀ j Ω' X := by
  refine le_iInf fun W => le_iInf fun E => le_iInf fun hE => ?_
  exact dcovModAllE_le_of_admissible
    ⟨hE.1, hE.2.1, fun b hb => hE.2.2 b (eligibleCover_mono h hb)⟩

omit [NeZero N₁] [NeZero L] in
/-- A real bound from an admissible structure, when the size is finite. -/
theorem dcovModAll_le_of_admissible {Ω X : Set (CTorus d L N₁ m₁ K)}
    {W : Finset (CTorus d L N₁ m₁ K)} {E : Finset (CTorus d L N₁ m₁ K × CTorus d L N₁ m₁ K)}
    (h : ModAdmissibleAll m₀ j Ω X W E) :
    dcovModAll m₀ j Ω X ≤ bondCost (scaleW L m₀ m₁ j) E := by
  have hle := dcovModAllE_le_of_admissible h
  have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hle
  rwa [ENNReal.toReal_ofReal (bondCost_scaleW_nonneg E)] at this

/-- For `X ∈ 𝒟_j` there is an admissible structure: all of `X`, with all nearest-neighbour
bonds inside `X`. -/
theorem exists_modAdmissibleAll_of_IsDj {Ω X : Set (CTorus d L N₁ m₁ K)} (hX : IsDj m₀ j X) :
    ∃ W E, ModAdmissibleAll m₀ j Ω X W E := by
  classical
  obtain ⟨hne, -, hconn⟩ := hX
  refine ⟨Finset.univ.filter (· ∈ X),
    Finset.univ.filter fun p => p.1 ∈ X ∧ p.2 ∈ X ∧ Nbr p.1 p.2, ⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · obtain ⟨x, hx⟩ := hne
    exact ⟨x, by simp [hx]⟩
  · intro p hp
    simpa using (Finset.mem_filter.1 hp).2
  · intro x hx y hy
    have hx' : x ∈ X := by simpa using hx
    have hy' : y ∈ X := by simpa using hy
    refine Relation.ReflTransGen.mono (fun u v huv => ?_) x y (hconn x hx' y hy')
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact Or.inl huv
  · intro x hx; simpa using hx
  · rintro b ⟨-, z, hzb, hzX, -⟩
    exact ⟨z, by simpa using hzX, hzb⟩

/-- The all-eligible size is finite on `𝒟_j`. -/
theorem dcovModAllE_ne_top_of_IsDj {Ω X : Set (CTorus d L N₁ m₁ K)} (hX : IsDj m₀ j X) :
    dcovModAllE m₀ j Ω X ≠ ⊤ := by
  obtain ⟨W, E, h⟩ := exists_modAdmissibleAll_of_IsDj (Ω := Ω) hX
  exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top (dcovModAllE_le_of_admissible h)

omit [NeZero N₁] [NeZero L] in
/-- **Lower comparison** (VMOD-43 §2): for a label `X ∈ 𝒟_j`, a structure meeting every eligible
box meets the eligible boxes contained in `X`, which form a chosen family of `X ∩ Ω`; hence
`dcovModE ≤ dcovModAllE`.  Only the union property of `IsDj` is used. -/
theorem dcovModE_le_dcovModAllE {Ω X : Set (CTorus d L N₁ m₁ K)} (hX : IsDj m₀ j X) :
    dcovModE m₀ j Ω X ≤ dcovModAllE m₀ j Ω X := by
  refine le_iInf fun W => le_iInf fun E => le_iInf fun hE => ?_
  refine dcovModE_le_of_admissible (𝒦 := {b | b ∈ eligibleCover m₀ j Ω X ∧
      box b (L * cellSide L m₀ m₁ j) ⊆ X}) ⟨fun b hb => ⟨hb.1.1, hb.2⟩, fun z hz => ?_, hE.1,
    hE.2.1, fun b hb => hE.2.2 b hb.1⟩
  obtain ⟨b, hb1, hb2, hb3⟩ := hX.2.1 z hz.1
  exact Set.mem_iUnion₂.2 ⟨b, ⟨⟨hb1, z, hb2, hz⟩, hb3⟩, hb2⟩

/-- Real form of the lower comparison. -/
theorem dcovMod_le_dcovModAll {Ω X : Set (CTorus d L N₁ m₁ K)} (hX : IsDj m₀ j X) :
    dcovMod m₀ j Ω X ≤ dcovModAll m₀ j Ω X :=
  ENNReal.toReal_mono (dcovModAllE_ne_top_of_IsDj hX) (dcovModE_le_dcovModAllE hX)

end Balaban.Fluctuation
