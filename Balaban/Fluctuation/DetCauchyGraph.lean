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

* `paramGraph G`: the graph on the parameter cubes `cubeIdx G` in which two distinct cubes are
  adjacent when they lie in a common footprint `𝒬(q)`, or their cubes Moore-touch.  Its degree is
  at most `detDeg d L = 3 (L + 4)^d + 3 (L + 9)^d · 3 (8 L)^d` (`paramGraph_degree_le`): the Moore
  part by `cubeIdx_moore_degree`, the common-footprint part by `card_Qset_le` (footprints have at
  most `N₀` cubes) and `card_mult_le` (a cube lies in at most `3 (L + 9)^d` footprints).  So the
  graph is not a subgraph of the Moore graph; it is contained in a bounded power of it.
* `rootParam G y`: the parameter cube containing the sites of the unit block `y` (at most one,
  `card_rootParam_le`).
* `rooted_of_rootChain`: if every parameter of `J` has a chain, then `J` is rooted at
  `rootParam G y` in `paramGraph G`; `rooted_of_mixDiff_ne_zero` combines this with the support
  theorem.
* `card_support_le`: at most `Δ^(2n)` cut sets of size `n` have non-zero mixed difference,
  `Δ = max (detDeg d L + 1) |B|`.
* `sum_norm_mixDiff_le`, `norm_rootTrace_one_le`: with the fixed-field bound
  `‖mixDiff J‖ ≤ M (2 / e^κ)^|J|` of `rootTrace_cut_expansion`, if `(detDeg d L + 1)² · 2 / e^κ < 1`
  then `∑_J ‖mixDiff J‖ ≤ M (1 - (detDeg d L + 1)² · 2 / e^κ)^(-|B|)`, independent of the volume.
* `tail_norm_mixDiff_le`: the tail over `|J| ≥ n` is at most `M z^n / (1 - z)`,
  `z = Δ² · 2 / e^κ`.

Not proved here: that the hull assigned to a cut set has a bounded size, the composition of the
expansion with cut-dependent backgrounds, and the prefactor.
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

section Support

variable {G : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ} {a : ℕ → ℝ} {ν : ℝ}

/-- Every interaction cube of a centre of the cover contains a site of `Ω₁` (its base). -/
theorem exists_site_intBox (S : DGSetting G a ν) {q : ℕ × CTorus d L N₁ m₁ (k + 1)}
    (hq : q ∈ cubeIdx G) : ∃ x ∈ intBox q, x ∈ G.Ω 1 := by
  have hP : q.2 ∈ cubeP q := mem_cubeP.2 (SameCell.refl _ _)
  refine ⟨q.2, ?_, cubeP_subset_Ω S hq hP⟩
  rw [cubeP_eq_boxSet hq, mem_boxSet] at hP
  rw [mem_intBox]
  refine hP.mono ?_
  have : (0 : ℝ) ≤ (L : ℝ) ^ (q.1 + m₁) := by positivity
  linarith

/-- **The component of the root, for a parameter cube `p` not joined to the root.** Let `I ⊆ J`
with `p ∉ I`, and suppose no centre whose footprint contains `p` is joined to the block `y` by a
chain in `J` (`hnc`).  If `y` is attached to an active centre at the cut point `1_I`, then the
union `Y'` of the thickened cubes of the active centres that are joined to `y` is a union of
nearest-neighbour components of `Yreg` at both cut points `1_I`, `1_{I ∪ {p}}`, carries the label of
`y`, and the cut factors of the cubes inside `Y'` agree at the two cut points. -/
theorem exists_root_comp (S : DGSetting G a ν) {J I : Finset (cubeIdx G)} {p : cubeIdx G}
    (hpJ : p ∈ J) (hIJ : I ⊆ J) (y : unitPts G)
    (hnc : ∀ q, RootChain G J y q → p ∉ QsetP G q)
    (hatt : ∃ q0 ∈ Zs G (extS G (cutPt I)), HatAttached G y q0) :
    ∃ Y' : Finset (CTorus d L N₁ m₁ (k + 1)),
      IsNnComp (Yreg G (extS G (cutPt I))) Y' ∧
      IsNnComp (Yreg G (extS G (cutPt (insert p I)))) Y' ∧ unitLabel G Y' y ∧
      ∀ q ∈ cubeIdx G, SubI G (intBox q) Y' →
        sProd G (extS G (cutPt I)) q = sProd G (extS G (cutPt (insert p I))) q := by
  classical
  have hZ : ∀ z, z ∈ Zs G (extS G (cutPt I)) → z ∈ Zs G (extS G (cutPt (insert p I))) := by
    intro z hz
    rw [mem_Zs_cutPt_iff] at hz ⊢
    exact ⟨hz.1, hz.2.trans (Finset.subset_insert _ _)⟩
  have hact : ∀ z, z ∈ Zs G (extS G (cutPt (insert p I))) → ActIn G J z := by
    intro z hz
    rw [mem_Zs_cutPt_iff] at hz
    refine ⟨hz.1, hz.2.trans ?_⟩
    intro r hr
    rcases Finset.mem_insert.1 hr with h | h
    · exact h ▸ hpJ
    · exact hIJ h
  have hact0 : ∀ z, z ∈ Zs G (extS G (cutPt I)) → ActIn G J z := fun z hz => hact z (hZ z hz)
  set Y' : Finset (CTorus d L N₁ m₁ (k + 1)) := (Yreg G (extS G (cutPt I))).filter
    (fun x => ∃ w ∈ Zs G (extS G (cutPt I)), RootChain G J y w ∧ x ∈ hatBox w) with hY'
  have hmemY' : ∀ x, x ∈ Y' ↔ x ∈ G.Ω 1 ∧
      ∃ w ∈ Zs G (extS G (cutPt I)), RootChain G J y w ∧ x ∈ hatBox w := by
    intro x
    rw [hY', Finset.mem_filter, mem_Yreg_iff]
    constructor
    · rintro ⟨⟨h1, -⟩, h2⟩; exact ⟨h1, h2⟩
    · rintro ⟨h1, w, hw, hr, hx⟩; exact ⟨⟨h1, w, hw, hx⟩, w, hw, hr, hx⟩
  -- the key propagation step
  have claim : ∀ x ∈ Y', ∀ y' ∈ Yreg G (extS G (cutPt (insert p I))), Adj x y' → y' ∈ Y' := by
    intro x hx y' hy' hadj
    obtain ⟨hxΩ, w, hw, hwr, hxw⟩ := (hmemY' x).1 hx
    obtain ⟨hy'Ω, z, hz, hy'z⟩ := mem_Yreg_iff.1 hy'
    have hwz : HatAdj G w z :=
      ⟨x, mem_hatI_iff.2 ⟨hxw, hxΩ⟩, y', mem_hatI_iff.2 ⟨hy'z, hy'Ω⟩, Or.inr hadj⟩
    have hrz : RootChain G J y z := RootChain.of_adj (hact z hz) hwz.symm hwr
    have hzI : z ∈ Zs G (extS G (cutPt I)) := by
      have hz' := mem_Zs_cutPt_iff.1 hz
      refine mem_Zs_cutPt_iff.2 ⟨hz'.1, fun P hP => ?_⟩
      rcases Finset.mem_insert.1 (hz'.2 hP) with h | h
      · exact absurd (h ▸ hP) (hnc z hrz)
      · exact h
    exact (hmemY' y').2 ⟨hy'Ω, z, hzI, hrz, hy'z⟩
  have hYY : Y' ⊆ Yreg G (extS G (cutPt I)) := Finset.filter_subset _ _
  have hmono : Yreg G (extS G (cutPt I)) ⊆ Yreg G (extS G (cutPt (insert p I))) := by
    intro x hx
    obtain ⟨hxΩ, z, hz, hxz⟩ := mem_Yreg_iff.1 hx
    exact mem_Yreg_iff.2 ⟨hxΩ, z, hZ z hz, hxz⟩
  refine ⟨Y', ⟨hYY, fun x hx y' hy' hadj => claim x hx y' (hmono hy') hadj⟩,
    ⟨hYY.trans hmono, claim⟩, ?_, ?_⟩
  · -- the label of `y`
    obtain ⟨q0, hq0, x₁, hx₁b, hx₁h⟩ := hatt
    have hx₁l : (x₁ : CTorus d L N₁ m₁ (k + 1)) ∈ G.layer (k + 1) :=
      (unitBlock_mem_iff G _).1 (by rw [hx₁b]; exact y.2)
    have hq0c : q0 ∈ cubeIdx G := (mem_Zs_cutPt_iff.1 hq0).1
    intro x hxb
    refine (hmemY' x).2 ⟨x.2, q0, hq0, RootChain.of_attached (hact0 q0 hq0) ⟨x₁, hx₁b, hx₁h⟩, ?_⟩
    have hsame : SameCell (L ^ (k + 1)) (x₁ : CTorus d L N₁ m₁ (k + 1)) x :=
      sameCell_of_jBlock_eq le_rfl (jBlock_eq_of_unitBlock_eq (hx₁b.trans hxb.symm))
    exact hatBox_sameCell_top S hq0c hx₁l hx₁h hsame
  · -- the cut factors
    intro q hq hsub
    by_cases hpq : p ∈ QsetP G q
    · have h1 : sProd G (extS G (cutPt (insert p I))) q = 0 := by
        by_contra h0
        have hqZ : q ∈ Zs G (extS G (cutPt (insert p I))) := by
          unfold Zs; exact Finset.mem_filter.2 ⟨hq, h0⟩
        obtain ⟨x₀, hx₀b, hx₀Ω⟩ := exists_site_intBox S hq
        obtain ⟨-, w, hw, hwr, hx₀w⟩ := (hmemY' x₀).1 (hsub ⟨x₀, hx₀Ω⟩ hx₀b)
        have hqw : HatAdj G q w :=
          ⟨x₀, mem_hatI_iff.2 ⟨box_subset_hatBox q hx₀b, hx₀Ω⟩, x₀,
            mem_hatI_iff.2 ⟨hx₀w, hx₀Ω⟩, Or.inl rfl⟩
        exact hnc q (RootChain.of_adj (hact q hqZ) hqw hwr) hpq
      have h0 : sProd G (extS G (cutPt I)) q = 0 := by
        by_contra h0
        have hqZ : q ∈ Zs G (extS G (cutPt I)) := by
          unfold Zs; exact Finset.mem_filter.2 ⟨hq, h0⟩
        have := (Finset.mem_filter.1 (hZ q hqZ)).2
        exact this h1
      rw [h0, h1]
    · unfold sProd
      refine Finset.prod_congr rfl fun R hR => ?_
      have hRc : R ∈ cubeIdx G := Qset_subset_cubeIdx q hR
      have hne : (⟨R, hRc⟩ : cubeIdx G) ≠ p := fun h => hpq (h ▸ mem_QsetP.2 hR)
      rw [extS_cutPt_of_mem hRc, extS_cutPt_of_mem hRc]
      simp [hne]

end Support

section Algebra

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] in
/-- The `J`-th mixed difference vanishes if `F` does not change when the parameter `p ∈ J` is
switched on at the cut points `1_I` of the subsets `I ⊆ J ∖ {p}`.  (Only the cut points of
subsets of `J` enter, in contrast with `mixDiff_eq_zero_of_update_invariant`.) -/
theorem mixDiff_eq_zero_of_insert_eq {p : ι} {J : Finset ι} (hp : p ∈ J) (F : (ι → ℂ) → ℂ)
    (hF : ∀ I ⊆ J.erase p, F (cutPt (insert p I)) = F (cutPt I)) : mixDiff J F = 0 := by
  classical
  obtain ⟨J', hpJ', rfl⟩ : ∃ J', p ∉ J' ∧ J = insert p J' :=
    ⟨J.erase p, Finset.notMem_erase p J, (Finset.insert_erase hp).symm⟩
  rw [mixDiff_insert hpJ']
  unfold mixDiff cutDiff
  refine Finset.sum_eq_zero fun I hI => ?_
  have hIJ : I ⊆ J' := Finset.mem_powerset.1 hI
  have hpI : p ∉ I := fun h => hpJ' (hIJ h)
  have hu1 : Function.update (cutPt I) p 1 = cutPt (insert p I) := by
    funext q
    by_cases h : q = p
    · subst h; simp [cutPt]
    · simp [cutPt, h]
  have hu0 : Function.update (cutPt I) p 0 = cutPt I := by
    funext q
    by_cases h : q = p
    · subst h; simp [cutPt, hpI]
    · simp [Function.update_of_ne h]
  have := hF I (by rw [Finset.erase_insert hpJ']; exact hIJ)
  simp only [hu1, hu0, this, sub_self, mul_zero]

end Algebra

section Trace

variable {G : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ} {a : ℕ → ℝ} {aT ν κ δ : ℝ}

/-- **Locality of the rooted trace for the unit lattice, product form.**  The same as
`rootTrace_eq_of_comp_unit` for equal fields, but the hypothesis on the parameters is only that the
cut factors `s_q = ∏_{P ∈ 𝒬(q)} s_P` of the cubes `q` with `□_q ⊆ Y'` agree (which is all that
`decLog` uses; the individual parameters of the footprint need not agree). -/
theorem rootTrace_eq_of_comp_unit' {s s' : DecParams G} {α : G.Ω 1 → ℂ}
    {φ : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ}
    (H : CovStanding G a aT ν α κ (extS G s) δ φ (unitQ G) (unitP G))
    (H' : CovStanding G a aT ν α κ (extS G s') δ φ (unitQ G) (unitP G)) (hconn : HatConn G)
    {Y' : Finset (CTorus d L N₁ m₁ (k + 1))} (hY : IsNnComp (Yreg G (extS G s)) Y')
    (hY' : IsNnComp (Yreg G (extS G s')) Y')
    (hs : ∀ q ∈ cubeIdx G, SubI G (intBox q) Y' → sProd G (extS G s) q = sProd G (extS G s') q)
    (B : Finset (unitPts G)) (hB : ∀ y ∈ B, unitLabel G Y' y) :
    rootTrace G a aT ν (unitQ G) (unitP G) B s φ α =
      rootTrace G a aT ν (unitQ G) (unitP G) B s' φ α := by
  have key : ∀ y ∈ B, ∀ i : Fin N, decLog G a aT ν α (extS G s) φ (unitQ G) (unitP G) (y, i) (y, i) =
      decLog G a aT ν α (extS G s') φ (unitQ G) (unitP G) (y, i) (y, i) := fun y hy i =>
    H.decLog_agree H' hconn hY hY' hs (fun _ _ => rfl) (fun _ _ => rfl) (unitLabel G Y')
      (unitQ_label_top (unionOfTopBlocks_of_isNnComp (H.fam 0 le_rfl).st.dg hconn hY))
      (unitP_label_top (unionOfTopBlocks_of_isNnComp (H.fam 0 le_rfl).st.dg hconn hY))
      (y, i) (y, i) (hB y hy) (hB y hy)
  unfold rootTrace
  rw [Finset.sum_congr rfl fun y hy => Finset.sum_congr rfl (fun i _ => key y hy i)]

theorem rootTrace_eq_sum_single (B : Finset (unitPts G)) (s : DecParams G)
    (φ : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) (α : G.Ω 1 → ℂ) :
    rootTrace G a aT ν (unitQ G) (unitP G) B s φ α =
      ∑ y ∈ B, rootTrace G a aT ν (unitQ G) (unitP G) {y} s φ α := by
  unfold rootTrace
  rw [Finset.mul_sum]
  simp

theorem mixDiff_rootTrace_eq_sum (B : Finset (unitPts G)) (J : Finset (cubeIdx G))
    (φ : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) (α : G.Ω 1 → ℂ) :
    mixDiff J (fun s => rootTrace G a aT ν (unitQ G) (unitP G) B s φ α) =
      ∑ y ∈ B, mixDiff J (fun s => rootTrace G a aT ν (unitQ G) (unitP G) {y} s φ α) := by
  have hfun : (fun s => rootTrace G a aT ν (unitQ G) (unitP G) B s φ α) =
      fun s => ∑ y ∈ B, rootTrace G a aT ν (unitQ G) (unitP G) {y} s φ α :=
    funext fun s => rootTrace_eq_sum_single B s φ α
  rw [hfun]
  unfold mixDiff
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]

section Cuts

variable (S : XSetting G a aT ν) {κ : ℝ} (hκ : 0 < κ)
  (hM : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δ : ℝ} (hδ : 0 ≤ δ)
  (hsm : δ ^ 2 * smallConstX d L κ ≤ 1 / 4)
  {φ : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ} (hφ : IsConstraintFieldStrict G δ φ)
  {α : G.Ω 1 → ℂ}
  (hα : ∀ w, ‖α w‖ < coerciveConst d / (2 * (G.spacing (w : CTorus d L N₁ m₁ (k + 1))) ^ 2))

include S hκ hM hδ hsm hφ hα

/-- **Switching on a parameter cube not joined to the root does not change the rooted trace of a
block.**  Let `I ⊆ J`, `p ∈ J ∖ I`, and suppose no centre with `p` in its footprint is joined to
the unit block `y` by a chain in `J` (`hnc`).  Then the rooted trace of `{y}` at the cut points
`1_{I ∪ {p}}` and `1_I` agree. -/
theorem rootTrace_cut_insert_eq (hconn : HatConn G) {J I : Finset (cubeIdx G)} {p : cubeIdx G}
    (hpJ : p ∈ J) (hIJ : I ⊆ J) (y : unitPts G)
    (hnc : ∀ q, RootChain G J y q → p ∉ QsetP G q) :
    rootTrace G a aT ν (unitQ G) (unitP G) {y} (cutPt (insert p I)) φ α =
      rootTrace G a aT ν (unitQ G) (unitP G) {y} (cutPt I) φ α := by
  classical
  have h01 : ∀ I' : Finset (cubeIdx G), ∀ q, cutPt I' q = 0 ∨ cutPt I' q = 1 := by
    intro I' q; unfold cutPt; split_ifs <;> simp
  have hU := (isUnitLatticeB_unit (G := G)).toIsUnitLattice
  have H := covStanding_of_zero_one S hκ hM hδ hsm hU hφ hα (h01 I)
  have H' := covStanding_of_zero_one S hκ hM hδ hsm hU hφ hα (h01 (insert p I))
  by_cases hatt : ∃ q0 ∈ Zs G (extS G (cutPt I)), HatAttached G y q0
  · obtain ⟨Y', hY, hY', hl, hs⟩ := exists_root_comp S.dg hpJ hIJ y hnc hatt
    exact rootTrace_eq_of_comp_unit' H' H hconn hY' hY (fun q hq hsub => (hs q hq hsub).symm) {y}
      (fun y' hy' => by rw [Finset.mem_singleton.1 hy']; exact hl)
  · -- no active centre is attached to `y`, at either cut point: both are the baseline
    have hatt' : ¬ ∃ q0 ∈ Zs G (extS G (cutPt (insert p I))), HatAttached G y q0 := by
      rintro ⟨q0, hq0, ha⟩
      have hq0' := mem_Zs_cutPt_iff.1 hq0
      have hact : ActIn G J q0 := by
        refine ⟨hq0'.1, hq0'.2.trans ?_⟩
        intro r hr
        rcases Finset.mem_insert.1 hr with h | h
        · exact h ▸ hpJ
        · exact hIJ h
      have hnp := hnc q0 (RootChain.of_attached hact ha)
      refine hatt ⟨q0, mem_Zs_cutPt_iff.2 ⟨hq0'.1, fun P hP => ?_⟩, ha⟩
      rcases Finset.mem_insert.1 (hq0'.2 hP) with h | h
      · exact absurd (h ▸ hP) hnp
      · exact h
    have hbase : ∀ I' : Finset (cubeIdx G),
        (¬ ∃ q0 ∈ Zs G (extS G (cutPt I')), HatAttached G y q0) →
        rootTrace G a aT ν (unitQ G) (unitP G) {y} (cutPt I') φ α =
          -(1 / 2 : ℂ) * ∑ y ∈ ({y} : Finset (unitPts G)), ∑ i : Fin N,
            (((Real.log (a k) : ℝ) : ℂ) • (1 - liftOp N (unitP G)) +
              ((Real.log (a k + aT / (L : ℝ) ^ 2) : ℝ) : ℂ) • liftOp N (unitP G)) (y, i) (y, i) := by
      intro I' hna
      have HI := covStanding_of_zero_one S hκ hM hδ hsm hU hφ hα (h01 I')
      have hYr : IsNnComp (Yreg G (extS G (cutPt I'))) (Yreg G (extS G (cutPt I'))) :=
        ⟨subset_rfl, fun _ _ y' hy' _ => hy'⟩
      have hUT := unionOfTopBlocks_of_isNnComp S.dg hconn hYr
      refine rootTrace_eq_baseline_of_not_label HI hconn (unitLabel G (Yreg G (extS G (cutPt I'))))
        (unitQ_label_top hUT) (unitP_label_top hUT) {y} ?_
      intro y' hy' hlab
      rw [Finset.mem_singleton.1 hy'] at hlab
      obtain ⟨x₀, hx₀l, hx₀b⟩ := (mem_unitPts G).1 y.2
      have hx₀Ω : x₀ ∈ G.Ω 1 := G.layer_subset (by omega) le_rfl hx₀l
      obtain ⟨-, z, hz, hxz⟩ := mem_Yreg_iff.1 (hlab ⟨x₀, hx₀Ω⟩ hx₀b)
      exact hna ⟨z, hz, ⟨x₀, hx₀Ω⟩, hx₀b, hxz⟩
    rw [hbase _ hatt', hbase _ hatt]

/-- **Vanishing for a block that is not joined to some `p ∈ J`.** -/
theorem mixDiff_rootTrace_single_eq_zero (hconn : HatConn G) {J : Finset (cubeIdx G)}
    {p : cubeIdx G} (hpJ : p ∈ J) (y : unitPts G)
    (hnc : ∀ q, RootChain G J y q → p ∉ QsetP G q) :
    mixDiff J (fun s => rootTrace G a aT ν (unitQ G) (unitP G) {y} s φ α) = 0 :=
  mixDiff_eq_zero_of_insert_eq hpJ _ fun _ hI =>
    rootTrace_cut_insert_eq S hκ hM hδ hsm hφ hα hconn hpJ
      (hI.trans (Finset.erase_subset _ _)) y hnc

/-- **T2. Support of the mixed differences of the rooted trace.**  If `mixDiff J` of the rooted
trace of the set `B` of unit blocks is non-zero then there is a block `y ∈ B` such that every
parameter cube `p ∈ J` lies in the footprint of a centre `q` which is joined to `y` by a chain of
centres with footprints in `J` and consecutive `HatAdj` thickened cubes, the last attached to `y`
(`RootChain G J y q`). -/
theorem exists_rootChain_of_mixDiff_ne_zero (hconn : HatConn G) (B : Finset (unitPts G))
    {J : Finset (cubeIdx G)}
    (hne : mixDiff J (fun s => rootTrace G a aT ν (unitQ G) (unitP G) B s φ α) ≠ 0) :
    ∃ y ∈ B, ∀ p ∈ J, ∃ q, RootChain G J y q ∧ p ∈ QsetP G q := by
  by_contra h
  push Not at h
  apply hne
  rw [mixDiff_rootTrace_eq_sum]
  refine Finset.sum_eq_zero fun y hy => ?_
  obtain ⟨p, hpJ, hp⟩ := h y hy
  exact mixDiff_rootTrace_single_eq_zero S hκ hM hδ hsm hφ hα hconn hpJ y hp

end Cuts

end Trace

section Graph

variable {G : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}

theorem mem_Pset_iff {P : ℕ × CTorus d L N₁ m₁ (k + 1)} {x : CTorus d L N₁ m₁ (k + 1)} :
    x ∈ Pset m₁ P ↔ x ∈ cubeP P := by
  rw [mem_cubeP]; rfl

/-- **The cubes of the cover cover `Ω₁`.** -/
theorem exists_cube_of_mem_Omega (hG : CubeAligned G m₁) {x : CTorus d L N₁ m₁ (k + 1)}
    (hx : x ∈ G.Ω 1) : ∃ P ∈ cubeIdx G, x ∈ cubeP P := by
  obtain ⟨hn1, hnK, hxl⟩ := G.layerIndex_spec hx
  set n := G.layerIndex x with hn
  set A : ℕ := L ^ (n + m₁) with hA
  have hApos : 0 < A := pow_pos (Nat.pos_of_ne_zero (NeZero.ne L)) _
  have hdvd : A ∣ (N₁ * L ^ m₁) * L ^ (k + 1) := by
    have : A ∣ L ^ m₁ * L ^ (k + 1) := by
      rw [hA, ← pow_add]; exact pow_dvd_pow L (by omega)
    exact this.trans ⟨N₁, by ring⟩
  set y0 : CTorus d L N₁ m₁ (k + 1) := cbase A x with hy0
  have hval : ∀ μ, (y0 μ).val = A * ((x μ).val / A) := by
    intro μ
    simp only [hy0, cbase]
    rw [ZMod.val_natCast_of_lt]
    exact lt_of_le_of_lt (Nat.mul_div_le _ _) (ZMod.val_lt (x μ))
  have hsame : SameCell A x y0 := by
    intro μ
    rw [hval μ, Nat.mul_div_cancel_left _ hApos]
  have hbase : CubeBase m₁ n y0 := fun μ => by
    rw [hval μ]; exact Nat.mul_mod_right _ _
  refine ⟨(n, y0), (mem_cubeIdx G).2 ⟨⟨hn1, hnK⟩, ?_, hbase⟩, mem_cubeP.2 hsame⟩
  exact (hG.mem_layer_iff hn1 hnK hsame).1 hxl

theorem mem_Qset_of_mem_hat_cube {q P : ℕ × CTorus d L N₁ m₁ (k + 1)} (hP : P ∈ cubeIdx G)
    {x : CTorus d L N₁ m₁ (k + 1)} (hxq : x ∈ hatBox q) (hxP : x ∈ cubeP P) :
    P ∈ Qset G q :=
  mem_Qset.2 ⟨hP, x, mem_cubeP.1 hxP, mem_boxSet.1 hxq⟩

omit [NeZero N₁] [NeZero L] in
theorem near_of_eq_or_adj {x x' : CTorus d L N₁ m₁ (k + 1)} (h : x = x' ∨ Adj x x') :
    Near 1 1 x x' := by
  rcases h with rfl | ⟨μ, h | h⟩
  · exact ⟨0, fun _ => by simp, by funext μ; simp⟩
  · refine ⟨Pi.single μ 1, fun ν => ?_, ?_⟩
    · by_cases h' : ν = μ <;> simp [h']
    · rw [h]; congr 1; funext ν
      by_cases h' : ν = μ <;> simp [h']
  · refine ⟨-Pi.single μ 1, fun ν => ?_, ?_⟩
    · by_cases h' : ν = μ <;> simp [h']
    · rw [h]; funext ν
      by_cases h' : ν = μ <;> simp [h']

variable (G)

/-- **The parameter graph.** Vertices: the parameter cubes `cubeIdx G`.  Two distinct parameter
cubes are adjacent when they lie in a common footprint `𝒬(q)` of a centre `q`, or when their cubes
Moore-touch (are within sup-distance `1`). -/
def paramGraph : SimpleGraph (cubeIdx G) where
  Adj P P' := P ≠ P' ∧ ((∃ q ∈ cubeIdx G, P.1 ∈ Qset G q ∧ P'.1 ∈ Qset G q) ∨
    MooreTouch (Pset m₁ P.1) (Pset m₁ P'.1))
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.elim (fun ⟨q, hq, h1, h2⟩ => Or.inl ⟨q, hq, h2, h1⟩)
    (fun h => Or.inr h.symm)⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

open Classical in
/-- The parameter cubes that contain a site of the unit block `y` (at most one, `card_rootParam_le`);
the root of the animal count. -/
noncomputable def rootParam (y : unitPts G) : Finset (cubeIdx G) :=
  Finset.univ.filter fun P => ∃ x : G.Ω 1,
    unitBlock (x : CTorus d L N₁ m₁ (k + 1)) = (y : UnitTorus d L N₁ m₁ k) ∧
      (x : CTorus d L N₁ m₁ (k + 1)) ∈ cubeP P.1

variable {G}

theorem mem_rootParam {y : unitPts G} {P : cubeIdx G} :
    P ∈ rootParam G y ↔ ∃ x : G.Ω 1,
      unitBlock (x : CTorus d L N₁ m₁ (k + 1)) = (y : UnitTorus d L N₁ m₁ k) ∧
        (x : CTorus d L N₁ m₁ (k + 1)) ∈ cubeP P.1 := by
  classical
  simp [rootParam]

theorem walkIn_of_adj {Γ : SimpleGraph (cubeIdx G)} {C : Finset (cubeIdx G)} {v w : cubeIdx G}
    (hv : v ∈ C) (hw : w ∈ C) (h : Γ.Adj v w) : Polymer.WalkIn Γ C v w :=
  ⟨SimpleGraph.Walk.cons h SimpleGraph.Walk.nil, by
    intro x hx
    simp only [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil, List.mem_cons,
      List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl <;> assumption⟩

theorem walkIn_of_eq_or_adj {Γ : SimpleGraph (cubeIdx G)} {C : Finset (cubeIdx G)}
    {v w : cubeIdx G} (hv : v ∈ C) (hw : w ∈ C) (h : v = w ∨ Γ.Adj v w) :
    Polymer.WalkIn Γ C v w := by
  rcases h with rfl | h
  · exact Polymer.WalkIn.refl hv
  · exact walkIn_of_adj hv hw h

/-- **At most one parameter cube contains the sites of a unit block.** -/
theorem card_rootParam_le (hG : CubeAligned G m₁) (y : unitPts G) : (rootParam G y).card ≤ 1 := by
  rw [Finset.card_le_one]
  rintro ⟨⟨n, y0⟩, hP⟩ hPm ⟨⟨n', y0'⟩, hP'⟩ hPm'
  obtain ⟨x, hxb, hxP⟩ := mem_rootParam.1 hPm
  obtain ⟨x', hxb', hxP'⟩ := mem_rootParam.1 hPm'
  have hxl : (x : CTorus d L N₁ m₁ (k + 1)) ∈ G.layer (k + 1) :=
    (unitBlock_mem_iff G _).1 (by rw [hxb]; exact y.2)
  have hxl' : (x' : CTorus d L N₁ m₁ (k + 1)) ∈ G.layer (k + 1) :=
    (unitBlock_mem_iff G _).1 (by rw [hxb']; exact y.2)
  obtain ⟨⟨hn1, hnK⟩, hl, hb⟩ := (mem_cubeIdx G).1 hP
  obtain ⟨⟨hn1', hnK'⟩, hl', hb'⟩ := (mem_cubeIdx G).1 hP'
  have hsc := mem_cubeP.1 hxP
  have hsc' := mem_cubeP.1 hxP'
  have hnn : n = k + 1 := by
    by_contra hne
    exact G.layer_disjoint hn1 hnK (by omega) le_rfl hne
      ((hG.mem_layer_iff hn1 hnK hsc).2 hl) hxl
  have hnn' : n' = k + 1 := by
    by_contra hne
    exact G.layer_disjoint hn1' hnK' (by omega) le_rfl hne
      ((hG.mem_layer_iff hn1' hnK' hsc').2 hl') hxl'
  subst hnn hnn'
  have hxx : SameCell (L ^ (k + 1 + m₁)) (x : CTorus d L N₁ m₁ (k + 1)) x' := by
    intro μ
    have h1 := (unitBlock_eq_iff _ _).1 (hxb.trans hxb'.symm) μ
    have key : ∀ z : ℕ, z / L ^ (k + 1 + m₁) = z / L ^ k / L ^ (1 + m₁) := fun z => by
      rw [Nat.div_div_eq_div_mul, ← pow_add]; congr 2; omega
    rw [key, key, h1]
  have hcell : SameCell (L ^ (k + 1 + m₁)) y0 y0' := (hsc.symm.trans hxx).trans hsc'
  have hApos : 0 < L ^ (k + 1 + m₁) := pow_pos (Nat.pos_of_ne_zero (NeZero.ne L)) _
  have : y0 = y0' := by
    funext μ
    apply ZMod.val_injective
    have e1 := Nat.div_add_mod (y0 μ).val (L ^ (k + 1 + m₁))
    have e2 := Nat.div_add_mod (y0' μ).val (L ^ (k + 1 + m₁))
    rw [hb μ] at e1
    rw [hb' μ] at e2
    rw [hcell μ] at e1
    omega
  subst this
  rfl

end Graph

section Rooted

variable {G : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}

/-- **A set `J` all of whose parameter cubes are joined to a block by chains lies in the rooted
sets of the parameter graph.**  Every parameter cube of `J` is joined inside `J`, by a walk of
`paramGraph G`, to the parameter cube containing the block. -/
theorem rooted_of_rootChain (hG : CubeAligned G m₁) {J : Finset (cubeIdx G)} {y : unitPts G}
    (hJ : ∀ p ∈ J, ∃ q, RootChain G J y q ∧ p ∈ QsetP G q) :
    Polymer.Rooted (paramGraph G) ((rootParam G y : Finset (cubeIdx G)) : Set (cubeIdx G)) J := by
  classical
  -- the walk from a parameter of the footprint of `q` to the root
  have main : ∀ q q0, Relation.ReflTransGen (CentreLink G J) q q0 → HatAttached G y q0 →
      ActIn G J q0 → ∀ P ∈ QsetP G q, ∃ w ∈ rootParam G y, Polymer.WalkIn (paramGraph G) J P w := by
    intro q q0 hr hat hq0
    induction hr using Relation.ReflTransGen.head_induction_on with
    | refl =>
      intro P hP
      obtain ⟨x, hxb, hxh⟩ := hat
      obtain ⟨Px, hPx, hxP⟩ := exists_cube_of_mem_Omega hG x.2
      have hPxQ : Px ∈ Qset G q0 := mem_Qset_of_mem_hat_cube hPx hxh hxP
      have hwQ : (⟨Px, hPx⟩ : cubeIdx G) ∈ QsetP G q0 := mem_QsetP.2 hPxQ
      refine ⟨⟨Px, hPx⟩, mem_rootParam.2 ⟨x, hxb, hxP⟩, walkIn_of_eq_or_adj (hq0.2 hP) (hq0.2 hwQ) ?_⟩
      by_cases h : P = ⟨Px, hPx⟩
      · exact Or.inl h
      · exact Or.inr ⟨h, Or.inl ⟨_, hq0.1, mem_QsetP.1 hP, hPxQ⟩⟩
    | head hstep hrest ih =>
      rename_i q1 q2
      intro P hP
      obtain ⟨hq1, hq2, x, hx, x', hx', hxx'⟩ := hstep
      obtain ⟨hxh, hxΩ⟩ := mem_hatI_iff.1 hx
      obtain ⟨hxh', hxΩ'⟩ := mem_hatI_iff.1 hx'
      obtain ⟨Px, hPx, hxP⟩ := exists_cube_of_mem_Omega hG hxΩ
      obtain ⟨Px', hPx', hxP'⟩ := exists_cube_of_mem_Omega hG hxΩ'
      have h1 : (⟨Px, hPx⟩ : cubeIdx G) ∈ QsetP G q1 :=
        mem_QsetP.2 (mem_Qset_of_mem_hat_cube hPx hxh hxP)
      have h2 : (⟨Px', hPx'⟩ : cubeIdx G) ∈ QsetP G q2 :=
        mem_QsetP.2 (mem_Qset_of_mem_hat_cube hPx' hxh' hxP')
      obtain ⟨w, hw, hwalk⟩ := ih _ h2
      refine ⟨w, hw, ?_⟩
      have hw1 : Polymer.WalkIn (paramGraph G) J P ⟨Px, hPx⟩ := by
        refine walkIn_of_eq_or_adj (hq1.2 hP) (hq1.2 h1) ?_
        by_cases h : P = ⟨Px, hPx⟩
        · exact Or.inl h
        · exact Or.inr ⟨h, Or.inl ⟨_, hq1.1, mem_QsetP.1 hP, mem_QsetP.1 h1⟩⟩
      have hw2 : Polymer.WalkIn (paramGraph G) J ⟨Px, hPx⟩ ⟨Px', hPx'⟩ := by
        refine walkIn_of_eq_or_adj (hq1.2 h1) (hq2.2 h2) ?_
        by_cases h : (⟨Px, hPx⟩ : cubeIdx G) = ⟨Px', hPx'⟩
        · exact Or.inl h
        · exact Or.inr ⟨h, Or.inr ⟨x, mem_Pset_iff.2 hxP, x', mem_Pset_iff.2 hxP',
            near_of_eq_or_adj hxx'⟩⟩
      exact (hw1.trans hw2).trans hwalk
  intro p hp
  obtain ⟨q, ⟨hqa, q0, hat, h0, hr⟩, hpq⟩ := hJ p hp
  exact main q q0 hr hat h0 p hpq

end Rooted

section Degree

/-- **One coordinate of the multiplicity count.** If a site `y` of the cell `[P2, P2 + p₀)` lies in
the periodic interval of half-width `5/2 B + 3 A` around `y0 + (B - 1)/2`, and `B ∣ y0`, then `y0`
is a grid base of side `B` that is Moore-near the interval `[P2 - (3B + 3A), P2 + p₀ + 2B + 3A)`. -/
theorem nearGridBase_of_hat {n B A p₀ u : ℕ} [NeZero n] (hB : 0 < B) (y0 y P2 : ZMod n)
    (hdvd : B ∣ y0.val) (hu : u < p₀) (hy : y = P2 + (u : ZMod n)) (p : ℤ)
    (h : |(y.val : ℝ) + p * n - ((y0.val : ℝ) + ((B : ℝ) - 1) / 2)| < 5 / 2 * (B : ℝ) + 3 * A) :
    NearGridBase (p₀ + 5 * B + 6 * A) B (P2 - ((3 * B + 3 * A : ℕ) : ZMod n)) y0 := by
  set δ : ℤ := (y.val : ℤ) + p * n - y0.val with hδdef
  have hδ : (δ : ℝ) = (y.val : ℝ) + p * n - y0.val := by rw [hδdef]; push_cast; ring
  rw [abs_lt] at h
  obtain ⟨h1, h2⟩ := h
  have hl : -((2 * B + 3 * A : ℕ) : ℤ) ≤ δ := by
    by_contra hc
    push Not at hc
    have : (δ : ℝ) ≤ -((2 * B + 3 * A : ℕ) : ℝ) - 1 := by
      have : δ ≤ -((2 * B + 3 * A : ℕ) : ℤ) - 1 := by omega
      exact_mod_cast this
    push_cast at this
    linarith
  have hu' : δ ≤ ((3 * B + 3 * A : ℕ) : ℤ) - 1 := by
    by_contra hc
    push Not at hc
    have : ((3 * B + 3 * A : ℕ) : ℝ) ≤ (δ : ℝ) := by
      have : ((3 * B + 3 * A : ℕ) : ℤ) ≤ δ := by omega
      exact_mod_cast this
    push_cast at this
    linarith
  set i' : ℤ := (u : ℤ) - δ + ((3 * B + 3 * A : ℕ) : ℤ) with hi'
  have hi0 : 0 ≤ i' := by rw [hi']; omega
  have hip : i'.toNat < p₀ + 5 * B + 6 * A := by
    have : i' < ((p₀ + 5 * B + 6 * A : ℕ) : ℤ) := by rw [hi']; push_cast at hl ⊢; omega
    omega
  have hcast : ((i'.toNat : ℕ) : ZMod n) = ((i' : ℤ) : ZMod n) := by
    rw [← Int.cast_natCast, Int.toNat_of_nonneg hi0]
  have hδz : ((δ : ℤ) : ZMod n) = y - y0 := by
    rw [hδdef]; push_cast
    rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val, ZMod.natCast_self]; ring
  refine ⟨hdvd, 0, i'.toNat, hB, hip, 0, by simp, ?_⟩
  rw [hcast, hi']
  push_cast
  rw [hδz, hy]
  ring

variable {G : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}

open Classical in
/-- **Multiplicity of a parameter cube in the footprints, one layer.** At most `(L + 9) ^ d` centres
`q` of layer `j` have a given parameter cube `P` in their footprint, if `P.1 ≤ j + 1` and
`4 L² ≤ L ^ m₁`. -/
theorem card_mult_layer_le (hM : 4 * L ^ 2 ≤ L ^ m₁) {P : ℕ × CTorus d L N₁ m₁ (k + 1)}
    (hP : P ∈ cubeIdx G) {j : ℕ} (hj : P.1 ≤ j + 1) :
    ((cubeIdx G).filter fun q => q.1 = j ∧ P ∈ Qset G q).card ≤ (L + 9) ^ d := by
  by_cases hjK : j ≤ k + 1
  swap
  · have : ((cubeIdx G).filter fun q => q.1 = j ∧ P ∈ Qset G q) = ∅ := by
      refine Finset.filter_eq_empty_iff.2 fun q hq => ?_
      have := ((mem_cubeIdx G).1 hq).1.2
      omega
    rw [this]; simp
  have hLpos : 0 < L := Nat.pos_of_ne_zero (NeZero.ne L)
  have hBpos : 0 < L ^ (j + m₁) := pow_pos hLpos _
  have hqn : L ^ (j + m₁) ∣ (N₁ * L ^ m₁) * L ^ (k + 1) := by
    have : L ^ (j + m₁) ∣ L ^ m₁ * L ^ (k + 1) := by
      rw [← pow_add]; exact pow_dvd_pow L (by omega)
    exact Dvd.dvd.trans this (by rw [mul_assoc]; exact Dvd.intro_left _ rfl)
  have h4A : 4 * L ^ (j + 2) ≤ L ^ (j + m₁) := by
    have := Nat.mul_le_mul_left (L ^ j) hM
    calc 4 * L ^ (j + 2) = L ^ j * (4 * L ^ 2) := by ring
      _ ≤ L ^ j * L ^ m₁ := this
      _ = L ^ (j + m₁) := (pow_add _ _ _).symm
  have hp0 : L ^ (P.1 + m₁) ≤ L * L ^ (j + m₁) := by
    calc L ^ (P.1 + m₁) ≤ L ^ (j + m₁ + 1) := Nat.pow_le_pow_right hLpos (by omega)
      _ = L * L ^ (j + m₁) := by rw [pow_succ]; ring
  obtain ⟨-, -, hbP⟩ := (mem_cubeIdx G).1 hP
  set Bμ : Fin d → Finset (ZMod ((N₁ * L ^ m₁) * L ^ (k + 1))) := fun μ =>
    (Finset.univ).filter (NearGridBase (L ^ (P.1 + m₁) + 5 * L ^ (j + m₁) + 6 * L ^ (j + 2))
      (L ^ (j + m₁)) (P.2 μ - ((3 * L ^ (j + m₁) + 3 * L ^ (j + 2) : ℕ) :
        ZMod ((N₁ * L ^ m₁) * L ^ (k + 1))))) with hBμ
  have hBc : ∀ μ, (Bμ μ).card ≤ L + 9 := by
    intro μ
    refine (card_gridBases_le _ _ hBpos hqn _).trans ?_
    have : (L ^ (P.1 + m₁) + 5 * L ^ (j + m₁) + 6 * L ^ (j + 2)) / L ^ (j + m₁) ≤ L + 7 := by
      refine Nat.div_le_of_le_mul ?_
      nlinarith
    omega
  calc _ ≤ (Fintype.piFinset Bμ).card := by
        refine Finset.card_le_card_of_injOn Prod.snd ?_ ?_
        · intro q hq
          obtain ⟨hqi, hj', hQ⟩ := Finset.mem_filter.1 (Finset.mem_coe.1 hq)
          refine Finset.mem_coe.2 (Fintype.mem_piFinset.2 fun μ => ?_)
          obtain ⟨-, y, hy, hbox⟩ := mem_Qset.1 hQ
          obtain ⟨-, -, hbq⟩ := (mem_cubeIdx G).1 hqi
          obtain ⟨pz, hpz⟩ := hbox μ
          obtain ⟨u, hu, hyu⟩ := exists_add_of_div_eq (Nat.pos_of_ne_zero
            (pow_ne_zero _ (NeZero.ne (n := L)))) (hy μ) (hbP μ)
          rw [hj'] at hbq hpz
          have hR : hatRad L m₁ j = 5 / 2 * ((L ^ (j + m₁) : ℕ) : ℝ) +
              3 * ((L ^ (j + 2) : ℕ) : ℝ) := by
            unfold hatRad; push_cast; ring
          rw [hR] at hpz
          have hBr : (((L ^ (j + m₁) : ℕ) : ℝ)) = (L : ℝ) ^ (j + m₁) := by push_cast; rfl
          rw [← hBr] at hpz
          exact Finset.mem_filter.2 ⟨Finset.mem_univ _,
            nearGridBase_of_hat hBpos (q.2 μ) (y μ) (P.2 μ) (Nat.dvd_of_mod_eq_zero (hbq μ)) hu
              hyu pz hpz⟩
        · intro q hq q' hq' hsnd
          have h1 := (Finset.mem_filter.1 (Finset.mem_coe.1 hq)).2.1
          have h2 := (Finset.mem_filter.1 (Finset.mem_coe.1 hq')).2.1
          exact Prod.ext (h1.trans h2.symm) hsnd
    _ = ∏ μ, (Bμ μ).card := Fintype.card_piFinset Bμ
    _ ≤ ∏ _μ : Fin d, (L + 9) := Finset.prod_le_prod (fun μ _ => hBc μ)
    _ = (L + 9) ^ d := by simp

open Classical in
/-- **Multiplicity of a parameter cube in the footprints.** At most `3 (L + 9) ^ d` centres `q` of
the cover have a given parameter cube `P` in their footprint `𝒬(q)`. -/
theorem card_mult_le (hG : CubeAligned G m₁) (hϱ : (4 * d * L * (L : ℝ) ^ m₁ : ℝ) ≤ ϱ)
    (hM : 4 * L ^ 2 ≤ L ^ m₁) (hL : 1 ≤ L) {P : ℕ × CTorus d L N₁ m₁ (k + 1)}
    (hP : P ∈ cubeIdx G) :
    ((cubeIdx G).filter fun q => P ∈ Qset G q).card ≤ 3 * (L + 9) ^ d := by
  have hP1 := ((mem_cubeIdx G).1 hP).1.1
  have hsub : ((cubeIdx G).filter fun q => P ∈ Qset G q) ⊆
      (Finset.Icc (P.1 - 1) (P.1 + 1)).biUnion fun j =>
        (cubeIdx G).filter fun q => q.1 = j ∧ P ∈ Qset G q := by
    intro q hq
    obtain ⟨hqi, hQ⟩ := Finset.mem_filter.1 hq
    have hlay := Qset_layer hG hϱ hM hL hqi hQ
    exact Finset.mem_biUnion.2 ⟨q.1, Finset.mem_Icc.2 ⟨by omega, by omega⟩,
      Finset.mem_filter.2 ⟨hqi, rfl, hQ⟩⟩
  refine (Finset.card_le_card hsub).trans (Finset.card_biUnion_le.trans ?_)
  calc ∑ j ∈ Finset.Icc (P.1 - 1) (P.1 + 1),
        ((cubeIdx G).filter fun q => q.1 = j ∧ P ∈ Qset G q).card
      ≤ ∑ _j ∈ Finset.Icc (P.1 - 1) (P.1 + 1), (L + 9) ^ d :=
        Finset.sum_le_sum fun j hj => card_mult_layer_le hM hP (by
          have := (Finset.mem_Icc.1 hj).1
          omega)
    _ = 3 * (L + 9) ^ d := by
        rw [Finset.sum_const, Nat.card_Icc, smul_eq_mul]
        congr 1
        omega

/-- The degree bound `D = 3 (L + 4)^d + 3 (L + 9)^d · N₀`, `N₀ = 3 (8 L)^d`, of the parameter
graph. -/
def detDeg (d L : ℕ) : ℕ := 3 * (L + 4) ^ d + 3 * (L + 9) ^ d * N0 d L

omit [NeZero L] in
theorem d_le_of_cover_sep (hL : 1 ≤ L) (hϱ : (4 * d * L * (L : ℝ) ^ m₁ : ℝ) ≤ ϱ) :
    (d : ℝ) ≤ ϱ * (L : ℝ) ^ 2 := by
  have h1 : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have h2 : (1 : ℝ) ≤ (L : ℝ) ^ m₁ := one_le_pow₀ h1
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have h3 : (d : ℝ) ≤ 4 * d * L * (L : ℝ) ^ m₁ := by
    have : (1 : ℝ) ≤ L * (L : ℝ) ^ m₁ := by nlinarith
    nlinarith
  have h4 : (0 : ℝ) ≤ ϱ := by linarith
  have h5 : (d : ℝ) ≤ ϱ := h3.trans hϱ
  have hL2 : (1 : ℝ) ≤ (L : ℝ) ^ 2 := one_le_pow₀ h1
  nlinarith [mul_le_mul_of_nonneg_left hL2 h4]

open Classical in
/-- **T3. The degree of the parameter graph.** Every parameter cube is adjacent to at most
`detDeg d L = 3 (L + 4)^d + 3 (L + 9)^d · 3 (8 L)^d` others.  The Moore part of the adjacency
contributes at most `3 (L + 4)^d` (`cubeIdx_moore_degree`); the common-footprint part at most
`(number of footprints containing P) · N₀`. -/
theorem paramGraph_degree_le (hG : CubeAligned G m₁) (hϱ : (4 * d * L * (L : ℝ) ^ m₁ : ℝ) ≤ ϱ)
    (hM : 4 * L ^ 2 ≤ L ^ m₁) (hL : 1 ≤ L) (P : cubeIdx G) :
    (paramGraph G).degree P ≤ detDeg d L := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  set S1 : Finset (ℕ × CTorus d L N₁ m₁ (k + 1)) := (cubeIdx G).filter fun Q =>
    Q ≠ P.1 ∧ MooreTouch (Pset m₁ P.1) (Pset m₁ Q) with hS1
  set S2 : Finset (ℕ × CTorus d L N₁ m₁ (k + 1)) :=
    ((cubeIdx G).filter fun q => P.1 ∈ Qset G q).biUnion (Qset G) with hS2
  have hc1 : S1.card ≤ 3 * (L + 4) ^ d :=
    cubeIdx_moore_degree hG (d_le_of_cover_sep hL hϱ) P.2
  have hc2 : S2.card ≤ 3 * (L + 9) ^ d * N0 d L := by
    refine Finset.card_biUnion_le.trans ?_
    calc ∑ q ∈ (cubeIdx G).filter (fun q => P.1 ∈ Qset G q), (Qset G q).card
        ≤ ∑ _q ∈ (cubeIdx G).filter (fun q => P.1 ∈ Qset G q), N0 d L :=
          Finset.sum_le_sum fun q hq => card_Qset_le hG hϱ hM hL (Finset.mem_filter.1 hq).1
      _ = ((cubeIdx G).filter fun q => P.1 ∈ Qset G q).card * N0 d L := by
          rw [Finset.sum_const, smul_eq_mul]
      _ ≤ 3 * (L + 9) ^ d * N0 d L :=
          Nat.mul_le_mul_right _ (card_mult_le hG hϱ hM hL P.2)
  refine le_trans ?_ (Nat.add_le_add hc1 hc2)
  refine (Finset.card_le_card_of_injOn Subtype.val ?_ (fun _ _ _ _ h => Subtype.ext h)).trans
    (Finset.card_union_le _ _)
  intro Q hQ
  have hQ0 := (SimpleGraph.mem_neighborFinset _ _ _).1 (Finset.mem_coe.1 hQ)
  obtain ⟨hne, h | h⟩ : P ≠ Q ∧ _ := hQ0
  · obtain ⟨q, hq, h1, h2⟩ := h
    refine Finset.mem_coe.2 (Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨q, ?_, h2⟩))
    exact Finset.mem_filter.2 ⟨hq, h1⟩
  · exact Finset.mem_coe.2 (Finset.mem_union_left _
      (Finset.mem_filter.2 ⟨Q.2, fun h => hne (Subtype.ext h.symm), h⟩))

end Degree

section Tail

open Classical in
/-- **Tail of the rooted sum.** For sets rooted at a finite set `N` of at most `b_root` vertices of
a graph of degree at most `b`, with `z = Δ² t < 1`, `Δ = max (b + 1) b_root`:
`∑_{|C| ≥ n} t^{|C|} ≤ z^n / (1 - z)`. -/
theorem rooted_tail_sum_le {V : Type*} [Fintype V] [DecidableEq V] {Gr : SimpleGraph V}
    [Gr.LocallyFinite] {b b_root : ℕ} (hb : ∀ v, Gr.degree v ≤ b) (N : Finset V)
    (hN : N.card ≤ b_root) {t : ℝ} (ht : 0 ≤ t)
    (hz : ((max (b + 1) b_root : ℕ) : ℝ) ^ 2 * t < 1) (n : ℕ) :
    ∑ C ∈ (Polymer.rootedSets (G := Gr) (N : Set V)).filter (fun C => n ≤ C.card), t ^ C.card
      ≤ (((max (b + 1) b_root : ℕ) : ℝ) ^ 2 * t) ^ n / (1 - ((max (b + 1) b_root : ℕ) : ℝ) ^ 2 * t) := by
  set Δ : ℕ := max (b + 1) b_root with hΔ
  set z : ℝ := (Δ : ℝ) ^ 2 * t with hzdef
  have hz0 : 0 ≤ z := by positivity
  have hmaps : ∀ C ∈ (Polymer.rootedSets (G := Gr) (N : Set V)).filter (fun C => n ≤ C.card),
      C.card ∈ Finset.range (Fintype.card V + 1) := by
    intro C _; rw [Finset.mem_range]; exact Nat.lt_succ_of_le (Finset.card_le_univ _)
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  set g : ℕ → ℝ := fun m => if n ≤ m then z ^ m else 0 with hg
  have hfib : ∀ m ∈ Finset.range (Fintype.card V + 1),
      ∑ C ∈ ((Polymer.rootedSets (G := Gr) (N : Set V)).filter (fun C => n ≤ C.card)).filter
        (fun C => C.card = m), t ^ C.card ≤ g m := by
    intro m _
    by_cases hm : n ≤ m
    · have hgm : g m = z ^ m := by simp [hg, hm]
      rw [hgm]
      rw [Finset.sum_congr rfl (g := fun _ => t ^ m) (fun C hC => by
        rw [(Finset.mem_filter.1 hC).2]), Finset.sum_const, nsmul_eq_mul]
      have hcard := Polymer.card_rooted_le hb N hN m
      rw [← hΔ] at hcard
      have hsub : (((Polymer.rootedSets (G := Gr) (N : Set V)).filter (fun C => n ≤ C.card)).filter
          (fun C => C.card = m)).card ≤ Δ ^ (2 * m) :=
        (Finset.card_le_card (fun C hC => by
          obtain ⟨h1, h2⟩ := Finset.mem_filter.1 hC
          exact Finset.mem_filter.2 ⟨(Finset.mem_filter.1 h1).1, h2⟩)).trans hcard
      calc _ ≤ ((Δ ^ (2 * m) : ℕ) : ℝ) * t ^ m := by
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            exact_mod_cast hsub
        _ = z ^ m := by rw [hzdef, mul_pow, ← pow_mul]; push_cast; ring
    · have : ((Polymer.rootedSets (G := Gr) (N : Set V)).filter (fun C => n ≤ C.card)).filter
          (fun C => C.card = m) = ∅ := by
        refine Finset.filter_eq_empty_iff.2 fun C hC => ?_
        have := (Finset.mem_filter.1 hC).2
        omega
      rw [this]; simp [hg, hm]
  refine (Finset.sum_le_sum hfib).trans ?_
  have hHas : HasSum g (z ^ n / (1 - z)) := by
    refine (hasSum_nat_add_iff' n).1 ?_
    have h0 : ∑ i ∈ Finset.range n, g i = 0 := by
      refine Finset.sum_eq_zero fun i hi => ?_
      have := not_le.2 (Finset.mem_range.1 hi)
      simp [hg, this]
    rw [h0, sub_zero]
    have := (hasSum_geometric_of_lt_one hz0 hz).mul_left (z ^ n)
    convert this using 1
    · funext i; simp only [hg, le_add_iff_nonneg_left, zero_le, ite_true]; ring
    · rw [div_eq_mul_inv]
  exact sum_le_hasSum _ (fun i _ => by simp only [hg]; split_ifs <;> positivity) hHas

end Tail

section Combine

variable {G : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ} {a : ℕ → ℝ} {aT ν : ℝ}
variable (S : XSetting G a aT ν) {κ : ℝ} (hκ : 0 < κ)
  (hM : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δ : ℝ} (hδ : 0 ≤ δ)
  (hsm : δ ^ 2 * smallConstX d L κ ≤ 1 / 4)
  {φ : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ} (hφ : IsConstraintFieldStrict G δ φ)
  {α : G.Ω 1 → ℂ}
  (hα : ∀ w, ‖α w‖ < coerciveConst d / (2 * (G.spacing (w : CTorus d L N₁ m₁ (k + 1))) ^ 2))

include S hκ hM hδ hsm hφ hα

/-- **A cut set with non-zero mixed difference is rooted in the parameter graph.** If
`mixDiff J` of the rooted trace of `B` is non-zero, every parameter cube of `J` is joined, inside
`J`, by a walk of `paramGraph G` to the parameter cube containing a block of `B`. -/
theorem rooted_of_mixDiff_ne_zero (hconn : HatConn G) (B : Finset (unitPts G))
    {J : Finset (cubeIdx G)}
    (hne : mixDiff J (fun s => rootTrace G a aT ν (unitQ G) (unitP G) B s φ α) ≠ 0) :
    Polymer.Rooted (paramGraph G)
      ((B.biUnion (rootParam G) : Finset (cubeIdx G)) : Set (cubeIdx G)) J := by
  obtain ⟨y, hy, hJ⟩ := exists_rootChain_of_mixDiff_ne_zero S hκ hM hδ hsm hφ hα hconn B hne
  refine Polymer.Rooted.mono ?_ (rooted_of_rootChain S.dg.aligned hJ)
  intro P hP
  exact Finset.mem_coe.2 (Finset.mem_biUnion.2 ⟨y, hy, hP⟩)

open Classical in
/-- **The count of cut sets (T3).** At most `Δ^(2n)` cut sets `J` with `|J| = n` have non-zero
`mixDiff J` of the rooted trace of `B`, `Δ = max (detDeg d L + 1) |B|`. -/
theorem card_support_le (hconn : HatConn G) (B : Finset (unitPts G)) (n : ℕ) :
    (((Finset.univ : Finset (cubeIdx G)).powerset.filter fun J =>
        J.card = n ∧ mixDiff J (fun s => rootTrace G a aT ν (unitQ G) (unitP G) B s φ α) ≠ 0)).card
      ≤ (max (detDeg d L + 1) B.card) ^ (2 * n) := by
  have hdeg := fun P => paramGraph_degree_le (G := G) S.dg.aligned S.dg.cover_sep S.dg.hM
    (by have := S.dg.hL; omega) P
  have hN : (B.biUnion (rootParam G)).card ≤ B.card :=
    Finset.card_biUnion_le_card_mul B (rootParam G) 1 (fun y _ => card_rootParam_le S.dg.aligned y)
      |>.trans (by simp)
  refine le_trans ?_ (Polymer.card_rooted_le hdeg (B.biUnion (rootParam G)) hN n)
  refine Finset.card_le_card fun J hJ => ?_
  obtain ⟨-, hcard, hne⟩ := Finset.mem_filter.1 hJ
  exact Finset.mem_filter.2 ⟨Polymer.mem_rootedSets.2
    (rooted_of_mixDiff_ne_zero S hκ hM hδ hsm hφ hα hconn B hne), hcard⟩

open Classical in
/-- **T4. Volume-independent bound for the whole rooted trace expansion at fixed fields.** With
`M = (1/2) N |B| covBLog` and `Δ = detDeg d L + 1`, if `Δ² · 2 / e^κ < 1` then
`∑_J ‖mixDiff J‖ ≤ M (1 - Δ² · 2 / e^κ)^(-|B|)`; for one root block, `M / (1 - Δ² · 2 / e^κ)`. -/
theorem sum_norm_mixDiff_le (hconn : HatConn G) (B : Finset (unitPts G))
    (hz : ((detDeg d L + 1 : ℕ) : ℝ) ^ 2 * (2 / Real.exp κ) < 1) :
    ∑ J ∈ (Finset.univ : Finset (cubeIdx G)).powerset,
        ‖mixDiff J (fun s => rootTrace G a aT ν (unitQ G) (unitP G) B s φ α)‖ ≤
      (1 / 2 : ℝ) * N * B.card * covBLog d L (a k) (aT / (L : ℝ) ^ 2) κ *
        (1 / (1 - ((detDeg d L + 1 : ℕ) : ℝ) ^ 2 * (2 / Real.exp κ))) ^ B.card := by
  have hU := (isUnitLatticeB_unit (G := G)).toIsUnitLattice
  obtain ⟨-, hbound⟩ := rootTrace_cut_expansion (N := N) S hκ hM hδ hsm hU B hφ hα
  set Mc : ℝ := (1 / 2 : ℝ) * N * B.card * covBLog d L (a k) (aT / (L : ℝ) ^ 2) κ with hMc
  have hM0 : 0 ≤ Mc := by
    have := hbound ∅
    simp only [Finset.card_empty, pow_zero, mul_one] at this
    exact (norm_nonneg _).trans this
  have ht : 0 ≤ 2 / Real.exp κ := by positivity
  have hdeg := fun P => paramGraph_degree_le (G := G) S.dg.aligned S.dg.cover_sep S.dg.hM
    (by have := S.dg.hL; omega) P
  have hmax : max (detDeg d L + 1) 1 = detDeg d L + 1 := max_eq_left (by omega)
  have hfam := Polymer.sum_rooted_le (G := paramGraph G) (b := detDeg d L) (b_root := 1) hdeg
    (rootParam G) (fun y => card_rootParam_le S.dg.aligned y) ht (by rw [hmax]; exact hz) B
  rw [hmax] at hfam
  set R := Polymer.rootedSets (G := paramGraph G) (⋃ y ∈ B, ((rootParam G y : Finset (cubeIdx G)) :
    Set (cubeIdx G))) with hR
  have hRsub : R ⊆ (Finset.univ : Finset (cubeIdx G)).powerset :=
    fun J _ => Finset.mem_powerset.2 (Finset.subset_univ _)
  have hzero : ∀ J ∈ (Finset.univ : Finset (cubeIdx G)).powerset, J ∉ R →
      ‖mixDiff J (fun s => rootTrace G a aT ν (unitQ G) (unitP G) B s φ α)‖ = 0 := by
    intro J _ hJR
    by_contra hne
    apply hJR
    have hne' := norm_ne_zero_iff.1 hne
    refine Polymer.mem_rootedSets.2 (Polymer.Rooted.mono ?_
      (rooted_of_mixDiff_ne_zero S hκ hM hδ hsm hφ hα hconn B hne'))
    intro P hP
    simp only [Finset.coe_biUnion, Set.mem_iUnion] at hP ⊢
    exact hP
  rw [← Finset.sum_subset hRsub hzero]
  calc _ ≤ ∑ J ∈ R, Mc * (2 / Real.exp κ) ^ J.card := Finset.sum_le_sum fun J _ => hbound J
    _ = Mc * ∑ J ∈ R, (2 / Real.exp κ) ^ J.card := by rw [Finset.mul_sum]
    _ ≤ Mc * (1 / (1 - ((detDeg d L + 1 : ℕ) : ℝ) ^ 2 * (2 / Real.exp κ))) ^ B.card :=
        mul_le_mul_of_nonneg_left hfam hM0

open Classical in
/-- **T4. The value of the rooted trace at `s = 1`** (the sum of all mixed differences) obeys the
same bound. -/
theorem norm_rootTrace_one_le (hconn : HatConn G) (B : Finset (unitPts G))
    (hz : ((detDeg d L + 1 : ℕ) : ℝ) ^ 2 * (2 / Real.exp κ) < 1) :
    ‖rootTrace G a aT ν (unitQ G) (unitP G) B (fun _ => 1) φ α‖ ≤
      (1 / 2 : ℝ) * N * B.card * covBLog d L (a k) (aT / (L : ℝ) ^ 2) κ *
        (1 / (1 - ((detDeg d L + 1 : ℕ) : ℝ) ^ 2 * (2 / Real.exp κ))) ^ B.card := by
  have hU := (isUnitLatticeB_unit (G := G)).toIsUnitLattice
  obtain ⟨hsum, -⟩ := rootTrace_cut_expansion (N := N) S hκ hM hδ hsm hU B hφ hα
  rw [hsum]
  exact (norm_sum_le _ _).trans (sum_norm_mixDiff_le S hκ hM hδ hsm hφ hα hconn B hz)

open Classical in
/-- **T4. The tail of the expansion.** With `Δ = max (detDeg d L + 1) |B|` and
`z = Δ² · 2 / e^κ < 1`: `∑_{|J| ≥ n} ‖mixDiff J‖ ≤ M z^n / (1 - z)`. -/
theorem tail_norm_mixDiff_le (hconn : HatConn G) (B : Finset (unitPts G)) (n : ℕ)
    (hz : ((max (detDeg d L + 1) B.card : ℕ) : ℝ) ^ 2 * (2 / Real.exp κ) < 1) :
    ∑ J ∈ (Finset.univ : Finset (cubeIdx G)).powerset.filter (fun J => n ≤ J.card),
        ‖mixDiff J (fun s => rootTrace G a aT ν (unitQ G) (unitP G) B s φ α)‖ ≤
      (1 / 2 : ℝ) * N * B.card * covBLog d L (a k) (aT / (L : ℝ) ^ 2) κ *
        ((((max (detDeg d L + 1) B.card : ℕ) : ℝ) ^ 2 * (2 / Real.exp κ)) ^ n /
          (1 - ((max (detDeg d L + 1) B.card : ℕ) : ℝ) ^ 2 * (2 / Real.exp κ))) := by
  have hU := (isUnitLatticeB_unit (G := G)).toIsUnitLattice
  obtain ⟨-, hbound⟩ := rootTrace_cut_expansion (N := N) S hκ hM hδ hsm hU B hφ hα
  set Mc : ℝ := (1 / 2 : ℝ) * N * B.card * covBLog d L (a k) (aT / (L : ℝ) ^ 2) κ with hMc
  have hM0 : 0 ≤ Mc := by
    have := hbound ∅
    simp only [Finset.card_empty, pow_zero, mul_one] at this
    exact (norm_nonneg _).trans this
  have ht : 0 ≤ 2 / Real.exp κ := by positivity
  have hdeg := fun P => paramGraph_degree_le (G := G) S.dg.aligned S.dg.cover_sep S.dg.hM
    (by have := S.dg.hL; omega) P
  have hN : (B.biUnion (rootParam G)).card ≤ B.card :=
    Finset.card_biUnion_le_card_mul B (rootParam G) 1 (fun y _ => card_rootParam_le S.dg.aligned y)
      |>.trans (by simp)
  have htail := rooted_tail_sum_le hdeg (B.biUnion (rootParam G)) hN ht hz n
  set R := (Polymer.rootedSets (G := paramGraph G)
    ((B.biUnion (rootParam G) : Finset (cubeIdx G)) : Set (cubeIdx G))).filter
      (fun J => n ≤ J.card) with hR
  have hRsub : R ⊆ (Finset.univ : Finset (cubeIdx G)).powerset.filter (fun J => n ≤ J.card) :=
    fun J hJ => Finset.mem_filter.2 ⟨Finset.mem_powerset.2 (Finset.subset_univ _),
      (Finset.mem_filter.1 hJ).2⟩
  have hzero : ∀ J ∈ (Finset.univ : Finset (cubeIdx G)).powerset.filter (fun J => n ≤ J.card),
      J ∉ R → ‖mixDiff J (fun s => rootTrace G a aT ν (unitQ G) (unitP G) B s φ α)‖ = 0 := by
    intro J hJ hJR
    by_contra hne
    apply hJR
    exact Finset.mem_filter.2 ⟨Polymer.mem_rootedSets.2
      (rooted_of_mixDiff_ne_zero S hκ hM hδ hsm hφ hα hconn B (norm_ne_zero_iff.1 hne)),
      (Finset.mem_filter.1 hJ).2⟩
  rw [← Finset.sum_subset hRsub hzero]
  calc _ ≤ ∑ J ∈ R, Mc * (2 / Real.exp κ) ^ J.card := Finset.sum_le_sum fun J _ => hbound J
    _ = Mc * ∑ J ∈ R, (2 / Real.exp κ) ^ J.card := by rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left htail hM0

end Combine

end Balaban.Fluctuation
