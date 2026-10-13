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

end Balaban.Fluctuation
