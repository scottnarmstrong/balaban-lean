/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.P6PairGraph

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

end Balaban.Localization.Dec2
