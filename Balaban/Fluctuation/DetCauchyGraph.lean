/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.YregBlocks
public import Balaban.Localization.MooreDegree
public import Balaban.Polymer.RootedAnimals
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Support of the rooted trace expansion: connection to the root block (DET-CAUCHY, package (4))

Fields are fixed throughout: `φ` and `α` do not depend on the cut parameters (no cut-dependent
background).  The hull assignment and the bound on the number of hulls (the class bound) are not
proved here.

## Activation structure at a cut point (T1)

At the cut point `1_{J'}` (parameter cubes of `J'` switched on, the others off) a centre `q` of the
cover is *active* iff its footprint `𝒬(q)` lies in `J'` (`mem_Zs_cutPt_iff`), and `Yreg` is the set
of sites of `Ω₁` lying in the thickened cube of an active centre (`mem_Yreg_cutPt_iff`).

## Support (T2)

* `HatAdj q q'`: the thickened cubes of `q`, `q'` (their sites in `Ω₁`) overlap or contain
  nearest-neighbour sites.
* `HatAttached y q`: the thickened cube of `q` contains a site of `Ω₁` of the unit block `y`.
* `RootChain J y q`: `q` is a centre of the cover with footprint in `J`, joined to a centre
  attached to `y` by a chain of centres with footprints in `J` and consecutive thickened cubes
  `HatAdj`.
* `exists_rootChain_of_mixDiff_ne_zero`: if the `J`-th mixed difference of the rooted trace of a
  set `B` of unit blocks is non-zero then there is a block `y ∈ B` such that every parameter cube
  `p ∈ J` lies in the footprint of a centre `q` with `RootChain J y q`.

**On condition (4) of `mixDiff_rootTrace_unit_eq_zero_of_root_component`.** That condition asks
that no cube `q` with `□_q ⊆ Y'` have the switched parameter in its footprint.  It is not implied by
the absence of a chain: a cube `q` that is *inactive* at the cut point may have `□_q ⊆ Y'` because
other thickened cubes cover it, and have `p ∈ 𝒬(q)`.  What `decLog` uses is only the equality of
the cut factors `s_q = ∏_{P ∈ 𝒬(q)} s_P` at the two cut points, and an inactive `q` has
`s_q = 0` at both (some parameter of its footprint other than `p` is off), so the factors agree.
Here the vanishing is proved with the weaker hypothesis "the cut factors of the cubes inside `Y'`
agree" (`rootTrace_eq_of_comp_unit'`); an *active* cube inside `Y'` with `p` in its footprint
would be joined to the root, which the absence of a chain excludes.

## Counting (T3, T4)

The parameter graph `paramGraph`: two parameter cubes are adjacent if they lie in a common
footprint, or their cubes Moore-touch.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization Balaban.Analysis
  Finset Matrix

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}

section Activation

variable (G : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ)

open Classical in
/-- The footprint `𝒬(q)` of a centre, as a set of parameter cubes (elements of `cubeIdx G`). -/
noncomputable def QsetP (q : ℕ × CTorus d L N₁ m₁ (k + 1)) : Finset (cubeIdx G) :=
  (Qset G q).subtype (· ∈ cubeIdx G)

variable {G}

theorem mem_QsetP {q : ℕ × CTorus d L N₁ m₁ (k + 1)} {P : cubeIdx G} :
    P ∈ QsetP G q ↔ (P : ℕ × CTorus d L N₁ m₁ (k + 1)) ∈ Qset G q := by
  classical
  simp [QsetP]

/-- **T1. The active centres at the cut point `1_{J'}`**: `q` is active iff its footprint lies
in `J'`. -/
theorem mem_Zs_cutPt_iff {J' : Finset (cubeIdx G)} {z : ℕ × CTorus d L N₁ m₁ (k + 1)} :
    z ∈ Zs G (extS G (cutPt J')) ↔ z ∈ cubeIdx G ∧ QsetP G z ⊆ J' := by
  rw [mem_Zs_extS_cutPt_iff]
  refine and_congr_right fun _ => ⟨fun h P hP => ?_, fun h R hR hRz => ?_⟩
  · exact h P.1 P.2 (mem_QsetP.1 hP)
  · exact h ((mem_QsetP (q := z) (P := ⟨R, hR⟩)).2 hRz)

theorem mem_hatI_iff {q : ℕ × CTorus d L N₁ m₁ (k + 1)} {x : CTorus d L N₁ m₁ (k + 1)} :
    x ∈ hatI G q ↔ x ∈ hatBox q ∧ x ∈ G.Ω 1 := by
  classical
  simp [hatI]

theorem mem_Yreg_iff {s : ℕ × CTorus d L N₁ m₁ (k + 1) → ℂ} {x : CTorus d L N₁ m₁ (k + 1)} :
    x ∈ Yreg G s ↔ x ∈ G.Ω 1 ∧ ∃ z ∈ Zs G s, x ∈ hatBox z := by
  classical
  simp only [Yreg, Finset.mem_filter, Finset.mem_biUnion]
  tauto

/-- **T1. `Yreg` at the cut point `1_{J'}`**: the sites of `Ω₁` in the thickened cube of a centre
whose footprint lies in `J'`. -/
theorem mem_Yreg_cutPt_iff {J' : Finset (cubeIdx G)} {x : CTorus d L N₁ m₁ (k + 1)} :
    x ∈ Yreg G (extS G (cutPt J')) ↔
      x ∈ G.Ω 1 ∧ ∃ z ∈ cubeIdx G, QsetP G z ⊆ J' ∧ x ∈ hatBox z := by
  rw [mem_Yreg_iff]
  refine and_congr_right fun _ => ⟨fun ⟨z, hz, hx⟩ => ?_, fun ⟨z, hz, h, hx⟩ => ?_⟩
  · obtain ⟨h1, h2⟩ := mem_Zs_cutPt_iff.1 hz
    exact ⟨z, h1, h2, hx⟩
  · exact ⟨z, mem_Zs_cutPt_iff.2 ⟨hz, h⟩, hx⟩

end Activation

section Chains

variable (G : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ)

/-- The thickened cubes of the centres `q`, `q'` (their sites in `Ω₁`) overlap or contain
nearest-neighbour sites. -/
def HatAdj (q q' : ℕ × CTorus d L N₁ m₁ (k + 1)) : Prop :=
  ∃ x ∈ hatI G q, ∃ x' ∈ hatI G q', x = x' ∨ Adj x x'

/-- The thickened cube of the centre `q` contains a site of `Ω₁` of the unit block `y`. -/
def HatAttached (y : unitPts G) (q : ℕ × CTorus d L N₁ m₁ (k + 1)) : Prop :=
  ∃ x : G.Ω 1, unitBlock (x : CTorus d L N₁ m₁ (k + 1)) = (y : UnitTorus d L N₁ m₁ k) ∧
    (x : CTorus d L N₁ m₁ (k + 1)) ∈ hatBox q

/-- `q` is a centre of the cover whose footprint lies in the set `J` of parameter cubes. -/
def ActIn (J : Finset (cubeIdx G)) (q : ℕ × CTorus d L N₁ m₁ (k + 1)) : Prop :=
  q ∈ cubeIdx G ∧ QsetP G q ⊆ J

/-- Two centres with footprints in `J` whose thickened cubes `HatAdj`. -/
def CentreLink (J : Finset (cubeIdx G)) (q q' : ℕ × CTorus d L N₁ m₁ (k + 1)) : Prop :=
  ActIn G J q ∧ ActIn G J q' ∧ HatAdj G q q'

/-- **Connection to the root block.** `q` has its footprint in `J` and is joined by a chain of
centres `q = q₀, q₁, …, q_n` with footprints in `J` and consecutive `HatAdj` thickened cubes to a
centre `q_n` whose thickened cube meets the unit block `y`. -/
def RootChain (J : Finset (cubeIdx G)) (y : unitPts G) (q : ℕ × CTorus d L N₁ m₁ (k + 1)) :
    Prop :=
  ActIn G J q ∧ ∃ q0, HatAttached G y q0 ∧ ActIn G J q0 ∧
    Relation.ReflTransGen (CentreLink G J) q q0

variable {G}

theorem HatAdj.symm {q q' : ℕ × CTorus d L N₁ m₁ (k + 1)} (h : HatAdj G q q') : HatAdj G q' q := by
  obtain ⟨x, hx, x', hx', h⟩ := h
  exact ⟨x', hx', x, hx, h.imp Eq.symm Adj.symm⟩

theorem CentreLink.symm {J : Finset (cubeIdx G)} {q q' : ℕ × CTorus d L N₁ m₁ (k + 1)}
    (h : CentreLink G J q q') : CentreLink G J q' q :=
  ⟨h.2.1, h.1, h.2.2.symm⟩

theorem RootChain.of_attached {J : Finset (cubeIdx G)} {y : unitPts G}
    {q : ℕ × CTorus d L N₁ m₁ (k + 1)} (hq : ActIn G J q) (ha : HatAttached G y q) :
    RootChain G J y q :=
  ⟨hq, q, ha, hq, Relation.ReflTransGen.refl⟩

theorem RootChain.of_adj {J : Finset (cubeIdx G)} {y : unitPts G}
    {q q' : ℕ × CTorus d L N₁ m₁ (k + 1)} (hq' : ActIn G J q') (hadj : HatAdj G q' q)
    (hq : RootChain G J y q) : RootChain G J y q' := by
  obtain ⟨hqa, q0, ha, h0, hr⟩ := hq
  exact ⟨hq', q0, ha, h0, Relation.ReflTransGen.head ⟨hq', hqa, hadj⟩ hr⟩

end Chains

end Balaban.Fluctuation
