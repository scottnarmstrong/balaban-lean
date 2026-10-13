/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.PairedLocalAgree
public import Balaban.Localization.PairedLocalGraph
public import Balaban.Localization.FootprintHat
public import Balaban.Localization.P6PairOp

/-!
# The joint incidence graph of the P6 pair (VMOD-34 §4 package 3, VMOD-32 §2)

Geometry and combinatorics only.  The old boundary term of P6 is re-expanded with one auxiliary
cover `F♯` and two operators, the old-wall operator `H^- = p6OldC` and the boundary operator
`H^∂ = p6BoundaryC`.  The abstract locality theorem `PairedLocalAgree.paired_locality` needs, for
every set `J` of marked parameter patches, two incidence unions (one per operator) on a **common**
site set `Y_f(J)`, containing the seed, with the cells of the selected patches inside `Y_f(J)`.

* `JointIn` (T1): the least family of vertices of the incidence graphs of both operators, closed
  under the edges of the incidence graph of each operator (with its own live centres), under
  "a site is a site of both operators", "a parameter is a parameter of both operators", and under
  "a charged parameter reached has all sites of its cell `cubeP P` reached".  `jointSites` and
  `jointParams` are its site and parameter projections.
* `isIncUnion_joint_b`, `isIncUnion_joint_m`, `joint_cell` (T2): `IsIncUnion` for each operator on
  the same pair, and the cells of the reached parameters lie in the site set.
* `jointSites_mono_param`, `jointSites_mono_seed`, `jointSites_detach` (T3): monotonicity, and the
  detachment: if no patch of `J₂` is reached over `J = J₁ ∪ J₂` then the site set is that of `J₁`.
* `HatRooted`, `jointParams_hatRooted` (T4): every reached parameter is joined to the seed by a
  chain of the link "two sites are in the thickened box of one cover centre" through marked
  patches.  This is **not** Moore adjacency of the patches (see the discussion at `HatRooted`).
* `paired_graph_hyps`, `p6_paired_graph_hyps` (T5): the graph hypotheses of `paired_locality`
  (`hXY` and the four parts of `hG`) for `Y_f(J) := jointSites`.

**Not proved here** (open, see VMOD-32/34): the selectors `Fb`, `Sol` and their data domains and
smallness hypotheses, the dependency `composeDep` of every read of the output set lying in the seed
(OPEN-P6-AFFINE-DOMAIN), the covariance square root term.  Nothing is said about coefficients;
that the coefficient of the actual P6 interpolation is supported on patches rooted at the active
cells is the subject of a question to the author.
-/

@[expose] public section

namespace Balaban.Localization.Dec2

open Balaban Balaban.Multiscale Balaban.Background Finset

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱ' : ℝ}

section Joint

variable (C : DecCover d L N₁ m₁ K) (Hb : GeneratingSet d L (N₁ * L ^ m₁) K ϱ')
  (Hm : GeneratingSet d L (N₁ * L ^ m₁) K ϱ) (a : ℕ → ℝ) (ν : ℝ)
  (X₁ : Finset (CTorus d L N₁ m₁ K)) (𝒞 : Finset (ℕ × CTorus d L N₁ m₁ K))
  (U : Set (CTorus d L N₁ m₁ K))

/-- **The joint incidence closure** (T1).  `JointIn o v` says the vertex `v` of the incidence graph
of the operator `Hb` (`o = true`) or `Hm` (`o = false`) is reached from the seed `U`: seed sites;
the edges of the incidence graph of each operator, with the live centres of that operator; a site
(a parameter) reached for one operator is reached for the other; a charged parameter reached has all
sites of its cell in the closure. -/
inductive JointIn : Bool → IncV d L N₁ m₁ K → Prop
  | seed (o : Bool) {s : CTorus d L N₁ m₁ K} : s ∈ U → JointIn o (Sum.inl s)
  | adjB {u v : IncV d L N₁ m₁ K} : (incGraph C Hb a ν X₁ 𝒞).Adj u v → JointIn true u →
      JointIn true v
  | adjM {u v : IncV d L N₁ m₁ K} : (incGraph C Hm a ν X₁ 𝒞).Adj u v → JointIn false u →
      JointIn false v
  | site {o o' : Bool} {x : CTorus d L N₁ m₁ K} : JointIn o (Sum.inl x) → JointIn o' (Sum.inl x)
  | param {o o' : Bool} {P : ℕ × CTorus d L N₁ m₁ K} :
      JointIn o (Sum.inr (Sum.inr P)) → JointIn o' (Sum.inr (Sum.inr P))
  | cell {o : Bool} {P : ℕ × CTorus d L N₁ m₁ K} {x : CTorus d L N₁ m₁ K} : P ∈ 𝒞 →
      JointIn o (Sum.inr (Sum.inr P)) → x ∈ cubeP P → JointIn o (Sum.inl x)

open Classical in
/-- The site projection `Y_J` of the joint closure. -/
noncomputable def jointSites : Finset (CTorus d L N₁ m₁ K) :=
  Finset.univ.filter fun x => JointIn C Hb Hm a ν X₁ 𝒞 U true (Sum.inl x)

open Classical in
/-- The parameter projection `D_J` of the joint closure. -/
noncomputable def jointParams : Finset (ℕ × CTorus d L N₁ m₁ K) :=
  𝒞.filter fun P => JointIn C Hb Hm a ν X₁ 𝒞 U true (Sum.inr (Sum.inr P))

variable {C Hb Hm a ν X₁ 𝒞 U}

theorem mem_jointSites {x : CTorus d L N₁ m₁ K} :
    x ∈ jointSites C Hb Hm a ν X₁ 𝒞 U ↔ JointIn C Hb Hm a ν X₁ 𝒞 U true (Sum.inl x) := by
  classical
  simp [jointSites]

/-- A parameter reached lies in `𝒞`. -/
theorem JointIn.param_mem {o : Bool} {v : IncV d L N₁ m₁ K}
    (h : JointIn C Hb Hm a ν X₁ 𝒞 U o v) :
    ∀ P, v = Sum.inr (Sum.inr P) → P ∈ 𝒞 := by
  have key : ∀ {H : Σ ϱ : ℝ, GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {u : IncV d L N₁ m₁ K} {P},
      (incGraph C H.2 a ν X₁ 𝒞).Adj u (Sum.inr (Sum.inr P)) → P ∈ 𝒞 := by
    intro H u P hadj
    obtain ⟨-, h1 | h1⟩ := hadj
    · rcases u with x | z | Q <;> simp [incRel] at h1
      exact h1.2.2.2
    · simp [incRel] at h1
  induction h with
  | seed o hs => intro P hP; simp at hP
  | adjB hadj _ _ => intro P hP; subst hP; exact key (H := ⟨_, Hb⟩) hadj
  | adjM hadj _ _ => intro P hP; subst hP; exact key (H := ⟨_, Hm⟩) hadj
  | site _ _ => intro P hP; simp at hP
  | param _ ih => intro P hP; cases hP; exact ih _ rfl
  | cell _ _ _ => intro P hP; simp at hP

open Classical in
theorem mem_jointParams {P : ℕ × CTorus d L N₁ m₁ K} :
    P ∈ jointParams C Hb Hm a ν X₁ 𝒞 U ↔
      JointIn C Hb Hm a ν X₁ 𝒞 U true (Sum.inr (Sum.inr P)) := by
  classical
  simp only [jointParams, Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨h.param_mem P rfl, h⟩⟩

theorem seed_mem_jointSites {s : CTorus d L N₁ m₁ K} (hs : s ∈ U) :
    s ∈ jointSites C Hb Hm a ν X₁ 𝒞 U :=
  mem_jointSites.2 (JointIn.seed _ hs)

/-- **T2.** The joint closure is an incidence union for the boundary operator. -/
theorem isIncUnion_joint_b :
    IsIncUnion C Hb a ν X₁ 𝒞 (jointSites C Hb Hm a ν X₁ 𝒞 U)
      (jointParams C Hb Hm a ν X₁ 𝒞 U) :=
  ⟨{v | JointIn C Hb Hm a ν X₁ 𝒞 U true v}, fun _ _ h hu => JointIn.adjB h hu,
    fun _ => mem_jointSites, fun _ => mem_jointParams⟩

/-- **T2.** The same pair is an incidence union for the old-wall operator. -/
theorem isIncUnion_joint_m :
    IsIncUnion C Hm a ν X₁ 𝒞 (jointSites C Hb Hm a ν X₁ 𝒞 U)
      (jointParams C Hb Hm a ν X₁ 𝒞 U) :=
  ⟨{v | JointIn C Hb Hm a ν X₁ 𝒞 U false v}, fun _ _ h hu => JointIn.adjM h hu,
    fun _ => ⟨fun h => JointIn.site (mem_jointSites.1 h), fun h => mem_jointSites.2 (JointIn.site h)⟩,
    fun _ => ⟨fun h => JointIn.param (mem_jointParams.1 h),
      fun h => mem_jointParams.2 (JointIn.param h)⟩⟩

open Classical in
/-- **T2, cells.** Every reached parameter has its whole cell in the site set. -/
theorem joint_cell {P : ℕ × CTorus d L N₁ m₁ K}
    (hP : P ∈ jointParams C Hb Hm a ν X₁ 𝒞 U) :
    P ∈ 𝒞 ∧ ∀ x ∈ cubeP P, x ∈ jointSites C Hb Hm a ν X₁ 𝒞 U :=
  ⟨(Finset.mem_filter.1 hP).1, fun _ hx => mem_jointSites.2 (JointIn.cell
    (Finset.mem_filter.1 hP).1 (mem_jointParams.1 hP) hx)⟩

/-- **T2, dichotomy for both operators.** Every eligible live centre of either operator has its
footprint inside the site set or missing it. -/
theorem joint_dichotomy_b {z : ℕ × CTorus d L N₁ m₁ K} (hE : EligC C X₁ 𝒞 z) (hL : LiveI Hb z) :
    ((∀ x ∈ footprint Hb a ν z, x ∈ jointSites C Hb Hm a ν X₁ 𝒞 U) ∧
        ∀ P ∈ C.Qset z, P ∈ 𝒞 → P ∈ jointParams C Hb Hm a ν X₁ 𝒞 U) ∨
      (∀ x ∈ footprint Hb a ν z, x ∉ jointSites C Hb Hm a ν X₁ 𝒞 U) :=
  isIncUnion_joint_b.dichotomy hE hL

theorem joint_dichotomy_m {z : ℕ × CTorus d L N₁ m₁ K} (hE : EligC C X₁ 𝒞 z) (hL : LiveI Hm z) :
    ((∀ x ∈ footprint Hm a ν z, x ∈ jointSites C Hb Hm a ν X₁ 𝒞 U) ∧
        ∀ P ∈ C.Qset z, P ∈ 𝒞 → P ∈ jointParams C Hb Hm a ν X₁ 𝒞 U) ∨
      (∀ x ∈ footprint Hm a ν z, x ∉ jointSites C Hb Hm a ν X₁ 𝒞 U) :=
  isIncUnion_joint_m.dichotomy hE hL

end Joint

end Balaban.Localization.Dec2
