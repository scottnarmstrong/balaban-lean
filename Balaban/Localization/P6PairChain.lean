/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.P6PairGraph
public import Balaban.Fluctuation.DetCauchyGraph
public import Balaban.Polymer.RootedAnimals
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The chain of eligible live centres in the joint closure of the P6 pair

Finite geometry and combinatorics only.  Nothing is said about coefficients: that the coefficient of
the actual P6 interpolation is supported on patches rooted at the active cells
(`OPEN-P6-ACTIVE-COMPOSITE-LOC`) is open and is the subject of a question to the author.  This file
only extracts the exact chain structure of the joint closure `JointIn`.

The closure `JointIn` of `P6PairGraph.lean` moves only through *eligible live* centres of one of the
two operators.  A centre `(o, z)` (`o = true` for the boundary operator, `false` for the old-wall
operator) is *active* (`PairAct`) when `EligC` holds and the centre is live for that operator.

* `PairCentreLink u v` (`u` newer, `v` older): both centres are active and either some site of the
  extended footprint of `v` (its footprint, or a cell of a marked patch of `𝒬(v)`) equals, or is a
  nearest neighbour inside the incidence sites of the operator of `u` of, a site of the footprint
  of `u`; or `u` and `v` have a common marked patch in their footprints.
* `PairAnchor u`: `u` is active and a site of its footprint equals, or is an incidence-site nearest
  neighbour of, a site of the seed `U`.
* `PairRootChain u`: `u` is joined by `ReflTransGen PairCentreLink` to an anchor.

`jointParams_support`: every reached parameter lies in `𝒬(z) ∩ 𝒞` for a centre of a root chain;
`jointSites_support`: every reached site is in the seed `U` (which contains `X₁`) or in the extended
footprint of a centre of a root chain.  `pairRootChain_iff_jointIn` is the converse.

Parameter-free centres (`PairParamFree`: `𝒬(z) ∩ parCubes X₁ = ∅`) are eligible for every `𝒞`;
mathematically, outside the parameter region the operator is not decoupled, so dependence is carried
by undecoupled rows and no marked patch is charged for it.  A chain centre is parameter-free or has
a non-empty `𝒬(z) ∩ parCubes X₁ ⊆ 𝒞` (`chain_dichotomy`).
-/

@[expose] public section

namespace Balaban.Localization.Dec2

open Balaban Balaban.Multiscale Balaban.Background Finset

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱ' : ℝ}

section Chain

variable (C : DecCover d L N₁ m₁ K) (Hb : GeneratingSet d L (N₁ * L ^ m₁) K ϱ')
  (Hm : GeneratingSet d L (N₁ * L ^ m₁) K ϱ) (a : ℕ → ℝ) (ν : ℝ)
  (X₁ : Finset (CTorus d L N₁ m₁ K)) (𝒞 : Finset (ℕ × CTorus d L N₁ m₁ K))
  (U : Set (CTorus d L N₁ m₁ K))

/-- The footprint of the centre `z` for the operator labelled `o`. -/
def pFoot : Bool → ℕ × CTorus d L N₁ m₁ K → Set (CTorus d L N₁ m₁ K)
  | true, z => footprint Hb a ν z
  | false, z => footprint Hm a ν z

/-- The centre `z` is live for the operator labelled `o`. -/
def PairLive : Bool → ℕ × CTorus d L N₁ m₁ K → Prop
  | true, z => LiveI Hb z
  | false, z => LiveI Hm z

/-- The incidence sites of the operator labelled `o`. -/
def pSites : Bool → Set (CTorus d L N₁ m₁ K)
  | true => incSites C Hb a ν X₁ 𝒞
  | false => incSites C Hm a ν X₁ 𝒞

/-- **Active centre**: eligible and live for its operator. -/
def PairAct (u : Bool × (ℕ × CTorus d L N₁ m₁ K)) : Prop :=
  EligC C X₁ 𝒞 u.2 ∧ PairLive Hb Hm u.1 u.2

/-- Equal sites, or nearest neighbours that are both incidence sites of the operator `o`. -/
def PairAtt (o : Bool) (x y : CTorus d L N₁ m₁ K) : Prop :=
  x = y ∨ (Adj x y ∧ x ∈ pSites C Hb Hm a ν X₁ 𝒞 o ∧ y ∈ pSites C Hb Hm a ν X₁ 𝒞 o)

/-- **Extended footprint** of a centre: its footprint and the cells of the marked patches of
`𝒬(z)`. -/
def pairExt (u : Bool × (ℕ × CTorus d L N₁ m₁ K)) : Set (CTorus d L N₁ m₁ K) :=
  pFoot Hb Hm a ν u.1 u.2 ∪ {x | ∃ P ∈ 𝒞, P ∈ C.Qset u.2 ∧ x ∈ cubeP P}

/-- **The link between consecutive centres of the joint closure** (`u` newer, `v` older): both are
active and either a site of the extended footprint of `v` equals, or is a nearest-neighbour
incidence site of the operator of `u` of, a site of the footprint of `u`; or `u`, `v` have a common
marked patch in their footprints. -/
def PairCentreLink (u v : Bool × (ℕ × CTorus d L N₁ m₁ K)) : Prop :=
  PairAct C Hb Hm X₁ 𝒞 u ∧ PairAct C Hb Hm X₁ 𝒞 v ∧
    ((∃ x ∈ pairExt C Hb Hm a ν 𝒞 v, ∃ y ∈ pFoot Hb Hm a ν u.1 u.2,
        PairAtt C Hb Hm a ν X₁ 𝒞 u.1 x y) ∨
      ∃ P ∈ 𝒞, P ∈ C.Qset u.2 ∧ P ∈ C.Qset v.2)

/-- **Anchor**: an active centre whose footprint contains a seed site or an incidence-site
nearest neighbour of one. -/
def PairAnchor (u : Bool × (ℕ × CTorus d L N₁ m₁ K)) : Prop :=
  PairAct C Hb Hm X₁ 𝒞 u ∧ ∃ s ∈ U, ∃ y ∈ pFoot Hb Hm a ν u.1 u.2,
    PairAtt C Hb Hm a ν X₁ 𝒞 u.1 s y

/-- **Root chain**: joined by a chain of centre links to an anchor. -/
def PairRootChain (u : Bool × (ℕ × CTorus d L N₁ m₁ K)) : Prop :=
  ∃ v, PairAnchor C Hb Hm a ν X₁ 𝒞 U v ∧
    Relation.ReflTransGen (PairCentreLink C Hb Hm a ν X₁ 𝒞) u v

/-- The invariant of the joint closure. -/
def PairChainInv (o : Bool) : IncV d L N₁ m₁ K → Prop
  | Sum.inl x => x ∈ U ∨ ∃ u, PairRootChain C Hb Hm a ν X₁ 𝒞 U u ∧
      x ∈ pairExt C Hb Hm a ν 𝒞 u
  | Sum.inr (Sum.inl z) => PairRootChain C Hb Hm a ν X₁ 𝒞 U (o, z)
  | Sum.inr (Sum.inr P) => P ∈ 𝒞 ∧ ∃ u, PairRootChain C Hb Hm a ν X₁ 𝒞 U u ∧ P ∈ C.Qset u.2

variable {C Hb Hm a ν X₁ 𝒞 U}

theorem PairRootChain.act {u : Bool × (ℕ × CTorus d L N₁ m₁ K)}
    (h : PairRootChain C Hb Hm a ν X₁ 𝒞 U u) : PairAct C Hb Hm X₁ 𝒞 u := by
  obtain ⟨v, hv, hr⟩ := h
  rcases hr.cases_head with rfl | ⟨w, hw, -⟩
  · exact hv.1
  · exact hw.1

theorem PairRootChain.head {u v : Bool × (ℕ × CTorus d L N₁ m₁ K)}
    (h : PairCentreLink C Hb Hm a ν X₁ 𝒞 u v) (hv : PairRootChain C Hb Hm a ν X₁ 𝒞 U v) :
    PairRootChain C Hb Hm a ν X₁ 𝒞 U u := by
  obtain ⟨w, hw, hr⟩ := hv
  exact ⟨w, hw, Relation.ReflTransGen.head h hr⟩

theorem PairRootChain.of_anchor {u : Bool × (ℕ × CTorus d L N₁ m₁ K)}
    (h : PairAnchor C Hb Hm a ν X₁ 𝒞 U u) : PairRootChain C Hb Hm a ν X₁ 𝒞 U u :=
  ⟨u, h, Relation.ReflTransGen.refl⟩

/-- One step of the invariant for one operator. -/
theorem pairChainInv_step {ϱ₀ : ℝ} (H : GeneratingSet d L (N₁ * L ^ m₁) K ϱ₀) (o : Bool)
    (hF : ∀ z, pFoot Hb Hm a ν o z = footprint H a ν z)
    (hL : ∀ z, PairLive Hb Hm o z ↔ LiveI H z)
    (hS : pSites C Hb Hm a ν X₁ 𝒞 o = incSites C H a ν X₁ 𝒞)
    (hX : ∀ x ∈ X₁, x ∈ U) {u v : IncV d L N₁ m₁ K}
    (hadj : (incGraph C H a ν X₁ 𝒞).Adj u v) (hu : PairChainInv C Hb Hm a ν X₁ 𝒞 U o u) :
    PairChainInv C Hb Hm a ν X₁ 𝒞 U o v := by
  have site : ∀ x y, x ∈ incSites C H a ν X₁ 𝒞 → y ∈ incSites C H a ν X₁ 𝒞 → Adj x y →
      PairChainInv C Hb Hm a ν X₁ 𝒞 U o (Sum.inl x) → PairChainInv C Hb Hm a ν X₁ 𝒞 U o (Sum.inl y) := by
    intro x y hx hy hxy hux
    obtain ⟨hyΩ, hy' | ⟨z, hE, hLz, hf⟩⟩ := id hy
    · exact Or.inl (hX y hy')
    · right
      have hact : PairAct C Hb Hm X₁ 𝒞 (o, z) := ⟨hE, (hL z).2 hLz⟩
      have hfz : y ∈ pFoot Hb Hm a ν o z := (hF z).symm ▸ hf
      have hatt : PairAtt C Hb Hm a ν X₁ 𝒞 o x y :=
        Or.inr ⟨hxy, by rw [hS]; exact hx, by rw [hS]; exact ⟨hyΩ, Or.inr ⟨z, hE, hLz, hf⟩⟩⟩
      refine ⟨(o, z), ?_, Or.inl hfz⟩
      rcases hux with hxU | ⟨w, hw, hxw⟩
      · exact PairRootChain.of_anchor ⟨hact, x, hxU, y, hfz, hatt⟩
      · exact PairRootChain.head ⟨hact, hw.act, Or.inl ⟨x, hxw, y, hfz, hatt⟩⟩ hw
  have fwd : ∀ u v : IncV d L N₁ m₁ K, incRel C H a ν X₁ 𝒞 u v →
      PairChainInv C Hb Hm a ν X₁ 𝒞 U o u → PairChainInv C Hb Hm a ν X₁ 𝒞 U o v := by
    intro u v h hu
    rcases u with x | z | Q <;> rcases v with y | z' | P <;> simp only [incRel] at h
    · exact site x y h.1 h.2.1 h.2.2 hu
    · exact Or.inr ⟨(o, z), hu, Or.inl ((hF z).symm ▸ h.2.2)⟩
    · exact ⟨h.2.2.2, (o, z), hu, h.2.2.1⟩
  have bwd : ∀ u v : IncV d L N₁ m₁ K, incRel C H a ν X₁ 𝒞 v u →
      PairChainInv C Hb Hm a ν X₁ 𝒞 U o u → PairChainInv C Hb Hm a ν X₁ 𝒞 U o v := by
    intro u v h hu
    rcases u with x | z | Q <;> rcases v with y | z' | P <;> simp only [incRel] at h
    · exact site x y h.2.1 h.1 h.2.2.symm hu
    · have hact : PairAct C Hb Hm X₁ 𝒞 (o, z') := ⟨h.1, (hL z').2 h.2.1⟩
      have hfz : x ∈ pFoot Hb Hm a ν o z' := (hF z').symm ▸ h.2.2
      rcases hu with hxU | ⟨w, hw, hxw⟩
      · exact PairRootChain.of_anchor ⟨hact, x, hxU, x, hfz, Or.inl rfl⟩
      · exact PairRootChain.head ⟨hact, hw.act, Or.inl ⟨x, hxw, x, hfz, Or.inl rfl⟩⟩ hw
    · obtain ⟨hP𝒞, w, hw, hPw⟩ := hu
      have hact : PairAct C Hb Hm X₁ 𝒞 (o, z') := ⟨h.1, (hL z').2 h.2.1⟩
      exact PairRootChain.head ⟨hact, hw.act, Or.inr ⟨Q, hP𝒞, h.2.2.1, hPw⟩⟩ hw
  obtain ⟨-, h | h⟩ := hadj
  · exact fwd u v h hu
  · exact bwd u v h hu

/-- **The invariant holds along the whole joint closure.**  The seed contains `X₁`. -/
theorem JointIn.chainInv (hX : ∀ x ∈ X₁, x ∈ U) {o : Bool} {v : IncV d L N₁ m₁ K}
    (h : JointIn C Hb Hm a ν X₁ 𝒞 U o v) : PairChainInv C Hb Hm a ν X₁ 𝒞 U o v := by
  induction h with
  | seed o hs => exact Or.inl hs
  | adjB hadj _ ih =>
    exact pairChainInv_step (H := Hb) true (fun _ => rfl) (fun _ => Iff.rfl) rfl hX hadj ih
  | adjM hadj _ ih =>
    exact pairChainInv_step (H := Hm) false (fun _ => rfl) (fun _ => Iff.rfl) rfl hX hadj ih
  | site _ ih => exact ih
  | param _ ih => exact ih
  | cell hP _ hx ih => exact Or.inr (by obtain ⟨-, u, hu, hPu⟩ := ih; exact ⟨u, hu, Or.inr ⟨_, hP, hPu, hx⟩⟩)

/-- **Support of the reached parameters.**  Every reached parameter lies in `𝒬(z) ∩ 𝒞` for a centre
`z` of a root chain. -/
theorem jointParams_support (hX : ∀ x ∈ X₁, x ∈ U) {P : ℕ × CTorus d L N₁ m₁ K}
    (hP : P ∈ jointParams C Hb Hm a ν X₁ 𝒞 U) :
    P ∈ 𝒞 ∧ ∃ u, PairRootChain C Hb Hm a ν X₁ 𝒞 U u ∧ P ∈ C.Qset u.2 :=
  (mem_jointParams.1 hP).chainInv hX

/-- **Support of the reached sites.**  Every reached site lies in the seed or in the extended
footprint of a centre of a root chain. -/
theorem jointSites_support (hX : ∀ x ∈ X₁, x ∈ U) {x : CTorus d L N₁ m₁ K}
    (hx : x ∈ jointSites C Hb Hm a ν X₁ 𝒞 U) :
    x ∈ U ∨ ∃ u, PairRootChain C Hb Hm a ν X₁ 𝒞 U u ∧ x ∈ pairExt C Hb Hm a ν 𝒞 u :=
  (mem_jointSites.1 hx).chainInv hX

variable (C Hb Hm a ν X₁ 𝒞) in
/-- The incidence graph of the operator labelled `o`. -/
def pGraph : Bool → SimpleGraph (IncV d L N₁ m₁ K)
  | true => incGraph C Hb a ν X₁ 𝒞
  | false => incGraph C Hm a ν X₁ 𝒞

theorem JointIn.pstep {o : Bool} {u v : IncV d L N₁ m₁ K}
    (hadj : (pGraph C Hb Hm a ν X₁ 𝒞 o).Adj u v) (hu : JointIn C Hb Hm a ν X₁ 𝒞 U o u) :
    JointIn C Hb Hm a ν X₁ 𝒞 U o v := by
  cases o
  · exact JointIn.adjM hadj hu
  · exact JointIn.adjB hadj hu

theorem pGraph_site_centre {o : Bool} {z : ℕ × CTorus d L N₁ m₁ K} {x : CTorus d L N₁ m₁ K}
    (hz : PairAct C Hb Hm X₁ 𝒞 (o, z)) (hx : x ∈ pFoot Hb Hm a ν o z) :
    (pGraph C Hb Hm a ν X₁ 𝒞 o).Adj (Sum.inl x) (Sum.inr (Sum.inl z)) := by
  cases o
  · exact ⟨by simp, Or.inr ⟨hz.1, hz.2, hx⟩⟩
  · exact ⟨by simp, Or.inr ⟨hz.1, hz.2, hx⟩⟩

theorem pGraph_centre_param {o : Bool} {z P : ℕ × CTorus d L N₁ m₁ K}
    (hz : PairAct C Hb Hm X₁ 𝒞 (o, z)) (hP : P ∈ C.Qset z) (hP𝒞 : P ∈ 𝒞) :
    (pGraph C Hb Hm a ν X₁ 𝒞 o).Adj (Sum.inr (Sum.inl z)) (Sum.inr (Sum.inr P)) := by
  cases o
  · exact ⟨by simp, Or.inl ⟨hz.1, hz.2, hP, hP𝒞⟩⟩
  · exact ⟨by simp, Or.inl ⟨hz.1, hz.2, hP, hP𝒞⟩⟩

theorem pGraph_site_site {o : Bool} {x y : CTorus d L N₁ m₁ K} (hxy : Adj x y) (hne' : x ≠ y)
    (hx : x ∈ pSites C Hb Hm a ν X₁ 𝒞 o) (hy : y ∈ pSites C Hb Hm a ν X₁ 𝒞 o) :
    (pGraph C Hb Hm a ν X₁ 𝒞 o).Adj (Sum.inl x) (Sum.inl y) := by
  have hne : (Sum.inl x : IncV d L N₁ m₁ K) ≠ Sum.inl y := by
    intro h; cases h; exact hne' rfl
  cases o
  · exact ⟨hne, Or.inl ⟨hx, hy, hxy⟩⟩
  · exact ⟨hne, Or.inl ⟨hx, hy, hxy⟩⟩

/-- Reaching a centre from an attached site. -/
theorem jointIn_centre_of_att {o : Bool} {z : ℕ × CTorus d L N₁ m₁ K}
    {x y : CTorus d L N₁ m₁ K} (hz : PairAct C Hb Hm X₁ 𝒞 (o, z))
    (hy : y ∈ pFoot Hb Hm a ν o z) (hatt : PairAtt C Hb Hm a ν X₁ 𝒞 o x y)
    (hx : JointIn C Hb Hm a ν X₁ 𝒞 U o (Sum.inl x)) :
    JointIn C Hb Hm a ν X₁ 𝒞 U o (Sum.inr (Sum.inl z)) := by
  rcases hatt with rfl | ⟨hxy, hxs, hys⟩
  · exact JointIn.pstep (pGraph_site_centre hz hy) hx
  · by_cases hne : x = y
    · subst hne; exact JointIn.pstep (pGraph_site_centre hz hy) hx
    · exact JointIn.pstep (pGraph_site_centre hz hy)
        (JointIn.pstep (pGraph_site_site hxy hne hxs hys) hx)

/-- **Converse.**  Every centre of a root chain is reached by the joint closure. -/
theorem PairRootChain.jointIn {u : Bool × (ℕ × CTorus d L N₁ m₁ K)}
    (h : PairRootChain C Hb Hm a ν X₁ 𝒞 U u) :
    JointIn C Hb Hm a ν X₁ 𝒞 U u.1 (Sum.inr (Sum.inl u.2)) := by
  obtain ⟨v, ⟨hv, s, hs, y, hy, hatt⟩, hr⟩ := h
  have base : JointIn C Hb Hm a ν X₁ 𝒞 U v.1 (Sum.inr (Sum.inl v.2)) :=
    jointIn_centre_of_att hv hy hatt (JointIn.seed _ hs)
  induction hr using Relation.ReflTransGen.head_induction_on with
  | refl => exact base
  | @head u' w hstep _ ih =>
    obtain ⟨hu', hw, hcase⟩ := hstep
    rcases hcase with ⟨x, hx, y', hy', hatt'⟩ | ⟨P, hP𝒞, hPu, hPw⟩
    · have hxr : JointIn C Hb Hm a ν X₁ 𝒞 U w.1 (Sum.inl x) := by
        rcases hx with hx | ⟨P, hP𝒞, hPw, hxP⟩
        · exact JointIn.pstep (pGraph_site_centre hw hx).symm ih
        · exact JointIn.cell hP𝒞 (JointIn.pstep (pGraph_centre_param hw hPw hP𝒞) ih) hxP
      exact jointIn_centre_of_att hu' hy' hatt' (JointIn.site hxr)
    · have hPr := JointIn.param (o' := u'.1) (JointIn.pstep (pGraph_centre_param hw hPw hP𝒞) ih)
      exact JointIn.pstep (pGraph_centre_param hu' hPu hP𝒞).symm hPr

/-- **The exact support statement.**  A centre is reached by the joint closure iff it has a root
chain. -/
theorem jointIn_centre_iff (hX : ∀ x ∈ X₁, x ∈ U) {o : Bool} {z : ℕ × CTorus d L N₁ m₁ K} :
    JointIn C Hb Hm a ν X₁ 𝒞 U o (Sum.inr (Sum.inl z)) ↔
      PairRootChain C Hb Hm a ν X₁ 𝒞 U (o, z) :=
  ⟨fun h => h.chainInv hX, fun h => h.jointIn⟩

/-- A centre is **parameter-free** if no parameter cube lies in its footprint. -/
def PairParamFree (z : ℕ × CTorus d L N₁ m₁ K) : Prop :=
  C.Qset z ∩ C.parCubes X₁ = ∅

/-- **Dichotomy for chain centres.**  A centre of a root chain is parameter-free, or its footprint
meets the parameter cubes and all of them are marked. -/
theorem chain_dichotomy {u : Bool × (ℕ × CTorus d L N₁ m₁ K)}
    (h : PairRootChain C Hb Hm a ν X₁ 𝒞 U u) :
    PairParamFree (C := C) (X₁ := X₁) u.2 ∨
      ((C.Qset u.2 ∩ C.parCubes X₁).Nonempty ∧ C.Qset u.2 ∩ C.parCubes X₁ ⊆ 𝒞) := by
  by_cases hne : (C.Qset u.2 ∩ C.parCubes X₁).Nonempty
  · exact Or.inr ⟨hne, fun P hP => h.act.1.2 P (Finset.mem_inter.1 hP).1 (Finset.mem_inter.1 hP).2⟩
  · exact Or.inl (Finset.not_nonempty_iff_eq_empty.1 hne)

/-- Every eligible centre that is parameter-free is eligible for every marked set. -/
theorem eligC_of_paramFree {z : ℕ × CTorus d L N₁ m₁ K} (hz : z ∈ C.cubeIdx)
    (h : PairParamFree (C := C) (X₁ := X₁) z) (𝒞' : Finset (ℕ × CTorus d L N₁ m₁ K)) :
    EligC C X₁ 𝒞' z :=
  ⟨hz, fun P hP hpar => by
    have : P ∈ C.Qset z ∩ C.parCubes X₁ := Finset.mem_inter.2 ⟨hP, hpar⟩
    rw [h] at this; simp at this⟩

end Chain


/-! ### The patch graph of the chain and rootedness -/

section Patch

open Balaban.Fluctuation Balaban.Polymer Classical

variable {k : ℕ} {ϱG : ℝ} (G : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱG)

theorem eq_or_adj_symm {V : Type*} {Γ : SimpleGraph V} {a b : V} (h : a = b ∨ Γ.Adj a b) :
    b = a ∨ Γ.Adj b a := h.elim (fun h => Or.inl h.symm) (fun h => Or.inr h.symm)

/-- **The patch graph of the chain.**  Two distinct parameter cubes are adjacent when they are
joined by a path of at most three edges of the parameter graph `paramGraph G` (two cubes are
adjacent there when they lie in a common footprint `𝒬(z)` or Moore-touch).  The intermediate cubes
need not be marked: a chain step between two centres passes through an unmarked cube of the cover
(a cube contained in `X₁`) at most twice. -/
def chainPatchGraph : SimpleGraph (cubeIdx G) where
  Adj P P' := P ≠ P' ∧ ∃ Q R, (P = Q ∨ (paramGraph G).Adj P Q) ∧ (Q = R ∨ (paramGraph G).Adj Q R) ∧
    (R = P' ∨ (paramGraph G).Adj R P')
  symm := ⟨fun _ _ h => by
    obtain ⟨hne, Q, R, h1, h2, h3⟩ := h
    exact ⟨hne.symm, R, Q, eq_or_adj_symm h3, eq_or_adj_symm h2, eq_or_adj_symm h1⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

variable {G}

theorem chainPatch_of_path {P Q R P' : cubeIdx G} (h1 : P = Q ∨ (paramGraph G).Adj P Q)
    (h2 : Q = R ∨ (paramGraph G).Adj Q R) (h3 : R = P' ∨ (paramGraph G).Adj R P') :
    P = P' ∨ (chainPatchGraph G).Adj P P' := by
  by_cases h : P = P'
  · exact Or.inl h
  · exact Or.inr ⟨h, Q, R, h1, h2, h3⟩

/-- The closed neighbourhood in the parameter graph. -/
noncomputable def closedNbhd (P : cubeIdx G) : Finset (cubeIdx G) :=
  insert P ((paramGraph G).neighborFinset P)

variable (G) in
/-- The degree constant of the patch graph of the chain: `(detDeg d L + 1)^3`, with
`detDeg d L = 3 (L+4)^d + 3 (L+9)^d · 3 (8L)^d` the degree bound of the parameter graph. -/
def pairChainDeg (d L : ℕ) : ℕ := (detDeg d L + 1) ^ 3

theorem card_closedNbhd_le (hdeg : ∀ P : cubeIdx G, (paramGraph G).degree P ≤ detDeg d L)
    (P : cubeIdx G) : (closedNbhd P).card ≤ detDeg d L + 1 := by
  unfold closedNbhd
  refine (Finset.card_insert_le _ _).trans ?_
  rw [SimpleGraph.card_neighborFinset_eq_degree]
  exact Nat.add_le_add_right (hdeg P) 1

/-- **T3.  The degree of the patch graph of the chain** is at most `(detDeg d L + 1)^3`. -/
theorem chainPatchGraph_degree_le (hG : CubeAligned G m₁)
    (hϱ : (4 * d * L * (L : ℝ) ^ m₁ : ℝ) ≤ ϱG) (hM : 4 * L ^ 2 ≤ L ^ m₁) (hL : 1 ≤ L)
    (P : cubeIdx G) : (chainPatchGraph G).degree P ≤ pairChainDeg d L := by
  have hdeg := fun P => paramGraph_degree_le (G := G) hG hϱ hM hL P
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  have hsub : (chainPatchGraph G).neighborFinset P ⊆
      (closedNbhd P).biUnion fun Q => (closedNbhd Q).biUnion closedNbhd := by
    intro P' hP'
    obtain ⟨-, Q, R, h1, h2, h3⟩ := (SimpleGraph.mem_neighborFinset _ _ _).1 hP'
    refine Finset.mem_biUnion.2 ⟨Q, ?_, Finset.mem_biUnion.2 ⟨R, ?_, ?_⟩⟩
    · rcases h1 with rfl | h1
      · exact Finset.mem_insert_self _ _
      · exact Finset.mem_insert_of_mem ((SimpleGraph.mem_neighborFinset _ _ _).2 h1)
    · rcases h2 with rfl | h2
      · exact Finset.mem_insert_self _ _
      · exact Finset.mem_insert_of_mem ((SimpleGraph.mem_neighborFinset _ _ _).2 h2)
    · rcases h3 with rfl | h3
      · exact Finset.mem_insert_self _ _
      · exact Finset.mem_insert_of_mem ((SimpleGraph.mem_neighborFinset _ _ _).2 h3)
  have hc := card_closedNbhd_le hdeg
  refine (Finset.card_le_card hsub).trans (Finset.card_biUnion_le.trans ?_)
  calc ∑ Q ∈ closedNbhd P, ((closedNbhd Q).biUnion closedNbhd).card
      ≤ ∑ _Q ∈ closedNbhd P, (detDeg d L + 1) * (detDeg d L + 1) := by
        refine Finset.sum_le_sum fun Q _ => Finset.card_biUnion_le.trans ?_
        calc ∑ R ∈ closedNbhd Q, (closedNbhd R).card
            ≤ ∑ _R ∈ closedNbhd Q, (detDeg d L + 1) := Finset.sum_le_sum fun R _ => hc R
          _ = (closedNbhd Q).card * (detDeg d L + 1) := by rw [Finset.sum_const, smul_eq_mul]
          _ ≤ (detDeg d L + 1) * (detDeg d L + 1) := Nat.mul_le_mul_right _ (hc Q)
    _ = (closedNbhd P).card * ((detDeg d L + 1) * (detDeg d L + 1)) := by
        rw [Finset.sum_const, smul_eq_mul]
    _ ≤ (detDeg d L + 1) * ((detDeg d L + 1) * (detDeg d L + 1)) :=
        Nat.mul_le_mul_right _ (hc P)
    _ = pairChainDeg d L := by unfold pairChainDeg; ring


/-! #### Rootedness -/

/-- The seed set in the patch graph: the cubes `P` such that some cube `Q` containing a site `y`
equal or adjacent to a seed site `s` is equal or adjacent to `P` in the parameter graph. -/
noncomputable def pairRootNbhd (s : CTorus d L N₁ m₁ (k + 1)) : Finset (cubeIdx G) :=
  Finset.univ.filter fun P => ∃ Q : cubeIdx G, ∃ y : CTorus d L N₁ m₁ (k + 1),
    (s = y ∨ Adj s y) ∧ y ∈ cubeP Q.1 ∧ (P = Q ∨ (paramGraph G).Adj P Q)

theorem mem_pairRootNbhd {s : CTorus d L N₁ m₁ (k + 1)} {P : cubeIdx G} :
    P ∈ pairRootNbhd (G := G) s ↔ ∃ Q : cubeIdx G, ∃ y : CTorus d L N₁ m₁ (k + 1),
      (s = y ∨ Adj s y) ∧ y ∈ cubeP Q.1 ∧ (P = Q ∨ (paramGraph G).Adj P Q) := by
  simp [pairRootNbhd]

/-- The root neighbourhood of a seed set `U`. -/
def pairRootSet (U : Set (CTorus d L N₁ m₁ (k + 1))) : Set (cubeIdx G) :=
  ⋃ s ∈ U, ((pairRootNbhd (G := G) s : Finset (cubeIdx G)) : Set (cubeIdx G))

theorem mem_Omega_of_mem_footprint {ϱ₀ : ℝ} {H : GeneratingSet d L (N₁ * L ^ m₁) K ϱ₀}
    {a : ℕ → ℝ} {ν : ℝ} {z : ℕ × CTorus d L N₁ m₁ K} {x : CTorus d L N₁ m₁ K}
    (hx : x ∈ footprint H a ν z) : x ∈ H.Ω 1 := by
  obtain ⟨b, -, rfl | ⟨y, -, rfl⟩⟩ := hx
  · exact b.2
  · exact y.2

theorem cube_unique (hG : CubeAligned G m₁) {Q Q' : cubeIdx G} {y : CTorus d L N₁ m₁ (k + 1)}
    (h : y ∈ cubeP Q.1) (h' : y ∈ cubeP Q'.1) : Q = Q' := by
  obtain ⟨⟨n, y0⟩, hQ⟩ := Q
  obtain ⟨⟨n', y0'⟩, hQ'⟩ := Q'
  obtain ⟨⟨hn1, hnK⟩, hl, hb⟩ := (mem_cubeIdx G).1 hQ
  obtain ⟨⟨hn1', hnK'⟩, hl', hb'⟩ := (mem_cubeIdx G).1 hQ'
  have hsc := mem_cubeP.1 h
  have hsc' := mem_cubeP.1 h'
  have hnn : n = n' := by
    by_contra hne
    exact G.layer_disjoint hn1 hnK hn1' hnK' hne ((hG.mem_layer_iff hn1 hnK hsc).2 hl)
      ((hG.mem_layer_iff hn1' hnK' hsc').2 hl')
  subst hnn
  have hcell : SameCell (L ^ (n + m₁)) y0 y0' := hsc.symm.trans hsc'
  have hApos : 0 < L ^ (n + m₁) := pow_pos (Nat.pos_of_ne_zero (NeZero.ne L)) _
  have : y0 = y0' := by
    funext μ
    apply ZMod.val_injective
    have e1 := Nat.div_add_mod (y0 μ).val (L ^ (n + m₁))
    have e2 := Nat.div_add_mod (y0' μ).val (L ^ (n + m₁))
    rw [hb μ] at e1
    rw [hb' μ] at e2
    rw [hcell μ] at e1
    omega
  subst this
  rfl

theorem pg_common {q : ℕ × CTorus d L N₁ m₁ (k + 1)} (hq : q ∈ cubeIdx G) {P P' : cubeIdx G}
    (hP : P.1 ∈ Qset G q) (hP' : P'.1 ∈ Qset G q) : P = P' ∨ (paramGraph G).Adj P P' := by
  by_cases h : P = P'
  · exact Or.inl h
  · exact Or.inr ⟨h, Or.inl ⟨q, hq, hP, hP'⟩⟩

theorem pg_moore {P P' : cubeIdx G} {x y : CTorus d L N₁ m₁ (k + 1)} (hx : x ∈ cubeP P.1)
    (hy : y ∈ cubeP P'.1) (h : x = y ∨ Adj x y) : P = P' ∨ (paramGraph G).Adj P P' := by
  by_cases hne : P = P'
  · exact Or.inl hne
  · exact Or.inr ⟨hne, Or.inr ⟨x, mem_Pset_iff.2 hx, y, mem_Pset_iff.2 hy, near_of_eq_or_adj h⟩⟩

section Rooted

variable {Hb : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ'} {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
  {a : ℕ → ℝ} {ν : ℝ} {X₁ : Finset (CTorus d L N₁ m₁ (k + 1))}
  {𝒞 : Finset (ℕ × CTorus d L N₁ m₁ (k + 1))} {U : Set (CTorus d L N₁ m₁ (k + 1))}

/-- A site of the footprint of a centre lies in a cube of the footprint `𝒬(z)`. -/
theorem pFoot_cube (hG : CubeAligned G m₁) (hΩb : ∀ x ∈ Hb.Ω 1, x ∈ G.Ω 1)
    (hΩm : ∀ x ∈ Hm.Ω 1, x ∈ G.Ω 1)
    (hfb : ∀ z ∈ cubeIdx G, ∀ t ∈ footprint Hb a ν z, t ∈ hatBox z)
    (hfm : ∀ z ∈ cubeIdx G, ∀ t ∈ footprint Hm a ν z, t ∈ hatBox z) {o : Bool}
    {z : ℕ × CTorus d L N₁ m₁ (k + 1)} (hz : z ∈ cubeIdx G)
    {x : CTorus d L N₁ m₁ (k + 1)} (hx : x ∈ pFoot Hb Hm a ν o z) :
    ∃ Q : cubeIdx G, x ∈ cubeP Q.1 ∧ Q.1 ∈ Qset G z := by
  have h : x ∈ G.Ω 1 ∧ x ∈ hatBox z := by
    cases o
    · exact ⟨hΩm _ (mem_Omega_of_mem_footprint hx), hfm z hz x hx⟩
    · exact ⟨hΩb _ (mem_Omega_of_mem_footprint hx), hfb z hz x hx⟩
  obtain ⟨Q, hQ, hxQ⟩ := exists_cube_of_mem_Omega hG h.1
  exact ⟨⟨Q, hQ⟩, hxQ, mem_Qset_of_mem_hat_cube hQ h.2 hxQ⟩

theorem att_near {o : Bool} {x y : CTorus d L N₁ m₁ (k + 1)}
    (h : PairAtt (coverOf G) Hb Hm a ν X₁ 𝒞 o x y) : x = y ∨ Adj x y :=
  h.elim Or.inl fun h => Or.inr h.1

/-- Reached marked patches of the footprint of a centre of a root chain are reached parameters. -/
theorem mem_jointParams_of_chain {u : Bool × (ℕ × CTorus d L N₁ m₁ (k + 1))}
    (hu : PairRootChain (coverOf G) Hb Hm a ν X₁ 𝒞 U u) {P : ℕ × CTorus d L N₁ m₁ (k + 1)}
    (hP : P ∈ (coverOf G).Qset u.2) (hP𝒞 : P ∈ 𝒞) :
    P ∈ jointParams (coverOf G) Hb Hm a ν X₁ 𝒞 U :=
  mem_jointParams.2 (JointIn.param (JointIn.pstep (pGraph_centre_param hu.act hP hP𝒞) hu.jointIn))

/-- **Parameter-free centres have their footprint in `X₁`.**  If no parameter cube lies in `𝒬(z)`,
every site of the footprint of `z` lies in a cube of `𝒬(z)` that is contained in `X₁`. -/
theorem paramFree_foot_subset (hG : CubeAligned G m₁) (hΩb : ∀ x ∈ Hb.Ω 1, x ∈ G.Ω 1)
    (hΩm : ∀ x ∈ Hm.Ω 1, x ∈ G.Ω 1)
    (hfb : ∀ z ∈ cubeIdx G, ∀ t ∈ footprint Hb a ν z, t ∈ hatBox z)
    (hfm : ∀ z ∈ cubeIdx G, ∀ t ∈ footprint Hm a ν z, t ∈ hatBox z) {o : Bool}
    {z : ℕ × CTorus d L N₁ m₁ (k + 1)} (hz : z ∈ cubeIdx G)
    (hpf : PairParamFree (C := coverOf G) (X₁ := X₁) z)
    {x : CTorus d L N₁ m₁ (k + 1)} (hx : x ∈ pFoot Hb Hm a ν o z) : x ∈ X₁ := by
  obtain ⟨Q, hxQ, hQz⟩ := pFoot_cube (a := a) (ν := ν) hG hΩb hΩm hfb hfm hz hx
  by_contra hxX
  have : Q.1 ∈ (coverOf G).Qset z ∩ (coverOf G).parCubes X₁ :=
    Finset.mem_inter.2 ⟨hQz, Finset.mem_filter.2 ⟨Q.2, fun hsub => hxX (hsub (mem_cubeP.2
      (mem_cubeP.1 hxQ)))⟩⟩
  rw [hpf] at this
  simp at this

/-- **T2, rootedness (pair analogue of `rooted_of_rootChain`).**  Every reached marked patch is joined, by a walk of the patch graph of the chain inside the set of
reached patches, to the root neighbourhood of the seed. -/
theorem jointParams_rooted (hG : CubeAligned G m₁)
    (hΩb : ∀ x ∈ Hb.Ω 1, x ∈ G.Ω 1) (hΩm : ∀ x ∈ Hm.Ω 1, x ∈ G.Ω 1)
    (hfb : ∀ z ∈ cubeIdx G, ∀ t ∈ footprint Hb a ν z, t ∈ hatBox z)
    (hfm : ∀ z ∈ cubeIdx G, ∀ t ∈ footprint Hm a ν z, t ∈ hatBox z)
    (hX : ∀ x ∈ X₁, x ∈ U) :
    Rooted (chainPatchGraph G) (pairRootSet (G := G) U)
      ((jointParams (coverOf G) Hb Hm a ν X₁ 𝒞 U).subtype (fun P => P ∈ cubeIdx G)) := by
  set J := (jointParams (coverOf G) Hb Hm a ν X₁ 𝒞 U).subtype (fun P => P ∈ cubeIdx G) with hJ
  have memJ : ∀ {u : Bool × (ℕ × CTorus d L N₁ m₁ (k + 1))},
      PairRootChain (coverOf G) Hb Hm a ν X₁ 𝒞 U u → ∀ P : cubeIdx G, P.1 ∈ Qset G u.2 →
        P.1 ∈ 𝒞 → P ∈ J := fun hu P hP hP𝒞 =>
    Finset.mem_subtype.2 (mem_jointParams_of_chain hu hP hP𝒞)
  have walkJ : ∀ {P P' : cubeIdx G}, P ∈ J → P' ∈ J → (P = P' ∨ (chainPatchGraph G).Adj P P') →
      WalkIn (chainPatchGraph G) J P P' := fun hP hP' h => walkIn_of_eq_or_adj hP hP' h
  have claim : ∀ u v, Relation.ReflTransGen (PairCentreLink (coverOf G) Hb Hm a ν X₁ 𝒞) u v →
      PairAnchor (coverOf G) Hb Hm a ν X₁ 𝒞 U v →
      ∀ P : cubeIdx G, P.1 ∈ Qset G u.2 → P.1 ∈ 𝒞 →
        ∃ w ∈ pairRootSet (G := G) U, WalkIn (chainPatchGraph G) J P w := by
    intro u v hr hv
    induction hr using Relation.ReflTransGen.head_induction_on with
    | refl =>
      intro P hP hP𝒞
      have hvc : PairRootChain (coverOf G) Hb Hm a ν X₁ 𝒞 U v :=
        PairRootChain.of_anchor hv
      obtain ⟨hact, s, hs, y, hy, hatt⟩ := hv
      obtain ⟨Qy, hyQ, hQyz⟩ := pFoot_cube hG hΩb hΩm hfb hfm hact.1.1 hy
      refine ⟨P, Set.mem_iUnion₂.2 ⟨s, hs, Finset.mem_coe.2 (mem_pairRootNbhd.2
        ⟨Qy, y, att_near hatt, hyQ, pg_common hact.1.1 hP hQyz⟩)⟩, ?_⟩
      exact Polymer.WalkIn.refl (memJ hvc P hP hP𝒞)
    | @head u' w hstep hrest ih =>
      intro P hP hP𝒞
      obtain ⟨hu', hw, hcase⟩ := hstep
      have hwc : PairRootChain (coverOf G) Hb Hm a ν X₁ 𝒞 U w := ⟨v, hv, hrest⟩
      have huc : PairRootChain (coverOf G) Hb Hm a ν X₁ 𝒞 U u' := PairRootChain.head
        ⟨hu', hw, hcase⟩ hwc
      have hPJ := memJ huc P hP hP𝒞
      rcases hcase with ⟨x, hx, y, hy, hatt⟩ | ⟨P₀, hP₀𝒞, hP₀u, hP₀w⟩
      · obtain ⟨Qy, hyQ, hQyu⟩ := pFoot_cube hG hΩb hΩm hfb hfm hu'.1.1 hy
        have hnear := att_near hatt
        have hnear' : y = x ∨ Adj y x := hnear.elim (fun h => Or.inl h.symm) (fun h => Or.inr h.symm)
        rcases hx with hx | ⟨P', hP'𝒞, hP'w, hxP'⟩
        · by_cases hne : ((coverOf G).Qset w.2 ∩ (coverOf G).parCubes X₁).Nonempty
          · obtain ⟨Qx, hxQ, hQxw⟩ := pFoot_cube hG hΩb hΩm hfb hfm hw.1.1 hx
            obtain ⟨Pv, hPv⟩ := hne
            have hPv𝒞 : Pv ∈ 𝒞 := hw.1.2 Pv (Finset.mem_inter.1 hPv).1 (Finset.mem_inter.1 hPv).2
            have hPvc : Pv ∈ cubeIdx G := Qset_subset_cubeIdx _ (Finset.mem_inter.1 hPv).1
            obtain ⟨r, hr, wk⟩ := ih ⟨Pv, hPvc⟩ (Finset.mem_inter.1 hPv).1 hPv𝒞
            refine ⟨r, hr, ?_⟩
            have hPvJ := memJ hwc ⟨Pv, hPvc⟩ (Finset.mem_inter.1 hPv).1 hPv𝒞
            have e1 := pg_common (P := P) (P' := Qy) hu'.1.1 hP hQyu
            have e2 := pg_moore (P := Qy) (P' := Qx) hyQ hxQ hnear'
            have e3 := pg_common (P := Qx) (P' := ⟨Pv, hPvc⟩) hw.1.1 hQxw
              (Finset.mem_inter.1 hPv).1
            exact (walkJ hPJ hPvJ (chainPatch_of_path e1 e2 e3)).trans wk
          · have hxX : x ∈ X₁ := paramFree_foot_subset hG hΩb hΩm hfb hfm hw.1.1
              (Finset.not_nonempty_iff_eq_empty.1 hne) hx
            exact ⟨P, Set.mem_iUnion₂.2 ⟨x, hX x hxX, Finset.mem_coe.2 (mem_pairRootNbhd.2
              ⟨Qy, y, hnear, hyQ, pg_common hu'.1.1 hP hQyu⟩)⟩, Polymer.WalkIn.refl hPJ⟩
        · have hP'c : P' ∈ cubeIdx G := Qset_subset_cubeIdx _ hP'w
          obtain ⟨r, hr, wk⟩ := ih ⟨P', hP'c⟩ hP'w hP'𝒞
          refine ⟨r, hr, ?_⟩
          have hP'J := memJ hwc ⟨P', hP'c⟩ hP'w hP'𝒞
          have e1 := pg_common (P := P) (P' := Qy) hu'.1.1 hP hQyu
          have e2 := pg_moore (P := Qy) (P' := ⟨P', hP'c⟩) hyQ hxP' hnear'
          exact (walkJ hPJ hP'J (chainPatch_of_path e1 e2 (Or.inl rfl))).trans wk
      · have hP₀c : P₀ ∈ cubeIdx G := Qset_subset_cubeIdx _ hP₀w
        obtain ⟨r, hr, wk⟩ := ih ⟨P₀, hP₀c⟩ hP₀w hP₀𝒞
        refine ⟨r, hr, ?_⟩
        have hP₀J := memJ hwc ⟨P₀, hP₀c⟩ hP₀w hP₀𝒞
        have e1 := pg_common (P := P) (P' := ⟨P₀, hP₀c⟩) hu'.1.1 hP hP₀u
        exact (walkJ hPJ hP₀J (chainPatch_of_path e1 (Or.inl rfl) (Or.inl rfl))).trans wk
  intro P hP
  obtain ⟨hP𝒞, u, hu, hPu⟩ := jointParams_support hX (Finset.mem_subtype.1 hP)
  obtain ⟨v, hv, hr⟩ := hu
  exact claim u v hr hv P hPu hP𝒞


end Rooted

/-! #### Counting the root neighbourhood and the rooted sum -/

section Sum

/-- The root neighbourhood of one seed site has at most `(2 d + 1) (detDeg d L + 1)` cubes. -/
theorem card_pairRootNbhd_le (hG : CubeAligned G m₁)
    (hϱ : (4 * d * L * (L : ℝ) ^ m₁ : ℝ) ≤ ϱG) (hM : 4 * L ^ 2 ≤ L ^ m₁) (hL : 1 ≤ L)
    (s : CTorus d L N₁ m₁ (k + 1)) :
    (pairRootNbhd (G := G) s).card ≤ (2 * d + 1) * (detDeg d L + 1) := by
  have hdeg := fun P => paramGraph_degree_le (G := G) hG hϱ hM hL P
  set S : Finset (CTorus d L N₁ m₁ (k + 1)) :=
    Finset.univ.filter fun y => s = y ∨ Adj s y with hS
  have hSc : S.card ≤ 2 * d + 1 := by
    let f : Fin d × Bool → CTorus d L N₁ m₁ (k + 1) := fun p =>
      if p.2 then s + Pi.single p.1 1 else s - Pi.single p.1 1
    have hsub : S ⊆ insert s (Finset.univ.image f) := by
      intro y hy
      obtain h | ⟨μ, h | h⟩ := (Finset.mem_filter.1 hy).2
      · exact Finset.mem_insert.2 (Or.inl h.symm)
      · exact Finset.mem_insert_of_mem (Finset.mem_image.2 ⟨(μ, true), Finset.mem_univ _, by
          simp [f, h]⟩)
      · exact Finset.mem_insert_of_mem (Finset.mem_image.2 ⟨(μ, false), Finset.mem_univ _, by
          simp [f, h]⟩)
    refine (Finset.card_le_card hsub).trans ((Finset.card_insert_le _ _).trans ?_)
    have := Finset.card_image_le (s := (Finset.univ : Finset (Fin d × Bool))) (f := f)
    simp only [Finset.card_univ, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool] at this
    omega
  let g : CTorus d L N₁ m₁ (k + 1) → Finset (cubeIdx G) := fun y =>
    if h : ∃ Q : cubeIdx G, y ∈ cubeP Q.1 then closedNbhd h.choose else ∅
  have hsub : pairRootNbhd (G := G) s ⊆ S.biUnion g := by
    intro P hP
    obtain ⟨Q, y, hy, hyQ, hPQ⟩ := mem_pairRootNbhd.1 hP
    refine Finset.mem_biUnion.2 ⟨y, Finset.mem_filter.2 ⟨Finset.mem_univ _, hy⟩, ?_⟩
    have h : ∃ Q : cubeIdx G, y ∈ cubeP Q.1 := ⟨Q, hyQ⟩
    simp only [g, h, ↓reduceDIte]
    have hQ : h.choose = Q := cube_unique hG h.choose_spec hyQ
    rw [hQ]
    rcases hPQ with rfl | hPQ
    · exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem ((SimpleGraph.mem_neighborFinset _ _ _).2 hPQ.symm)
  refine (Finset.card_le_card hsub).trans (Finset.card_biUnion_le.trans ?_)
  calc ∑ y ∈ S, (g y).card ≤ ∑ _y ∈ S, (detDeg d L + 1) := by
        refine Finset.sum_le_sum fun y _ => ?_
        by_cases h : ∃ Q : cubeIdx G, y ∈ cubeP Q.1
        · simp only [g, h, ↓reduceDIte]; exact card_closedNbhd_le hdeg _
        · simp only [g, h, ↓reduceDIte, Finset.card_empty]; omega
    _ = S.card * (detDeg d L + 1) := by rw [Finset.sum_const, smul_eq_mul]
    _ ≤ (2 * d + 1) * (detDeg d L + 1) := Nat.mul_le_mul_right _ hSc

/-- The rooted-sum constant: `max (pairChainDeg d L + 1) ((2 d + 1) (detDeg d L + 1))`. -/
def pairChainD (d L : ℕ) : ℕ := max (pairChainDeg d L + 1) ((2 * d + 1) * (detDeg d L + 1))

/-- **T5.  The rooted sum for the chain patch graph.**  For a finite seed `A` of sites and
`z = pairChainD² t < 1`: `Σ t^|C| ≤ (1 / (1 - z))^|A|` over the sets rooted at the root
neighbourhoods of `A`. -/
theorem chainPatch_rooted_sum_le (hG : CubeAligned G m₁)
    (hϱ : (4 * d * L * (L : ℝ) ^ m₁ : ℝ) ≤ ϱG) (hM : 4 * L ^ 2 ≤ L ^ m₁) (hL : 1 ≤ L)
    (A : Finset (CTorus d L N₁ m₁ (k + 1))) {t : ℝ} (ht : 0 ≤ t)
    (hz : ((pairChainD d L : ℕ) : ℝ) ^ 2 * t < 1) :
    ∑ C ∈ rootedSets (G := chainPatchGraph G)
        (⋃ s ∈ A, (pairRootNbhd (G := G) s : Set (cubeIdx G))), t ^ C.card
      ≤ (1 / (1 - ((pairChainD d L : ℕ) : ℝ) ^ 2 * t)) ^ A.card := by
  have key := sum_rooted_le (G := chainPatchGraph G) (b := pairChainDeg d L)
    (b_root := (2 * d + 1) * (detDeg d L + 1))
    (fun P => chainPatchGraph_degree_le hG hϱ hM hL P)
    (fun s : {s // s ∈ A} => pairRootNbhd (G := G) s.1)
    (fun s => card_pairRootNbhd_le hG hϱ hM hL s.1) ht hz A.attach
  have hU : ((⋃ i ∈ A.attach, ((pairRootNbhd (G := G) i.1 : Finset _) : Set _)) : Set (cubeIdx G))
      = ⋃ s ∈ A, ((pairRootNbhd (G := G) s : Finset _) : Set _) := by
    ext x; simp
  rw [hU, Finset.card_attach] at key
  exact key

/-- **T5, exponential form.**  With `t = exp (-κ₂)`, `z = pairChainD² t < 1`, `h = -log (1 - z)`:
if `|A| ≤ c_A (1 + Δ)` then the rooted sum is at most `exp (h c_A) exp (h c_A Δ)`. -/
theorem chainPatch_rooted_sum_le_exp (hG : CubeAligned G m₁)
    (hϱ : (4 * d * L * (L : ℝ) ^ m₁ : ℝ) ≤ ϱG) (hM : 4 * L ^ 2 ≤ L ^ m₁) (hL : 1 ≤ L)
    (A : Finset (CTorus d L N₁ m₁ (k + 1))) {κ₂ Δ c_A : ℝ}
    (hz : ((pairChainD d L : ℕ) : ℝ) ^ 2 * Real.exp (-κ₂) < 1)
    (hR : (A.card : ℝ) ≤ c_A * (1 + Δ)) :
    ∑ C ∈ rootedSets (G := chainPatchGraph G)
        (⋃ s ∈ A, (pairRootNbhd (G := G) s : Set (cubeIdx G))), Real.exp (-κ₂ * C.card)
      ≤ Real.exp (-Real.log (1 - ((pairChainD d L : ℕ) : ℝ) ^ 2 * Real.exp (-κ₂)) * c_A) *
        Real.exp (-Real.log (1 - ((pairChainD d L : ℕ) : ℝ) ^ 2 * Real.exp (-κ₂)) * c_A * Δ) := by
  set z : ℝ := ((pairChainD d L : ℕ) : ℝ) ^ 2 * Real.exp (-κ₂) with hzdef
  have hz0 : 0 ≤ z := by positivity
  have hpos : 0 < 1 - z := by linarith
  set h : ℝ := -Real.log (1 - z) with hh
  have hh0 : 0 ≤ h := by
    have : Real.log (1 - z) ≤ 0 := Real.log_nonpos (by linarith) (by linarith)
    linarith
  have hsum := chainPatch_rooted_sum_le hG hϱ hM hL A (Real.exp_pos (-κ₂)).le hz
  have hterm : ∀ C : Finset (cubeIdx G), Real.exp (-κ₂ * C.card) = Real.exp (-κ₂) ^ C.card :=
    fun C => by rw [← Real.exp_nat_mul]; ring_nf
  simp only [hterm]
  refine hsum.trans ?_
  have : 1 / (1 - z) = Real.exp h := by
    rw [hh, Real.exp_neg, Real.exp_log hpos, one_div]
  rw [this, ← Real.exp_nat_mul, ← Real.exp_add]
  apply Real.exp_le_exp.2
  nlinarith [mul_le_mul_of_nonneg_left hR hh0]

end Sum

end Patch

end Balaban.Localization.Dec2
