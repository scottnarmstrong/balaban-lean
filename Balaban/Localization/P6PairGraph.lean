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
* `PairHatRooted`, `jointParams_hatRooted` (T4): every reached parameter is joined to the seed by a
  chain of the link "two sites are in the thickened box of one cover centre" through marked
  patches.  This is **not** Moore adjacency of the patches (see the discussion at `PairHatRooted`).
* `paired_graph_hyps`, `p6_paired_graph_hyps` (T5): the graph hypotheses of `paired_locality`
  (`hXY` and the four parts of `hG`) for `Y_f(J) := jointSites`.

**Moore adjacency versus hat links (T4).**  Rootedness in the Moore graph (`mooreGraph`,
`mem_rootedSets_fsharp_iff`) is *not* implied.  A reached patch `P ∈ 𝒬(z)` only has a cell meeting
`□̂_z`, whose radius is about `3 L² ℓ_j`; two marked patches of `𝒬(z)` at opposite ends of `□̂_z`
are joined in the joint graph through the (unmarked) centre `z` without touching, and likewise the
first patch reached from the seed need not Moore-touch it.  The adjacency that is true is the hat
link of `PairHatRooted`: consecutive patches (and the seed) are joined through chains of cover
centres whose thickened boxes overlap or are adjacent.  The degree bound `mooreGraph_degree_le` does
not cover this relation; its degree is bounded by a larger constant of the same type (`|𝒬(z)| ≤ N₀`
and the number of centres with a given thickened box meeting a cell), which is not proved here.
The old-wall operator can combinatorially read from the active region into the hole: the joint
graph allows it, and the dependency set then extends into the hole only through hat-linked chains
of marked patches (`jointParams_hatRooted`).

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

section Mono

variable {C : DecCover d L N₁ m₁ K} {H : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {a : ℕ → ℝ} {ν : ℝ}
  {X₁ : Finset (CTorus d L N₁ m₁ K)} {𝒞 𝒞₁ : Finset (ℕ × CTorus d L N₁ m₁ K)}

theorem eligC_mono (h : 𝒞₁ ⊆ 𝒞) {z : ℕ × CTorus d L N₁ m₁ K} (hz : EligC C X₁ 𝒞₁ z) :
    EligC C X₁ 𝒞 z :=
  ⟨hz.1, fun P hP hpar => h (hz.2 P hP hpar)⟩

theorem incSites_mono (h : 𝒞₁ ⊆ 𝒞) :
    incSites C H a ν X₁ 𝒞₁ ⊆ incSites C H a ν X₁ 𝒞 := by
  rintro x ⟨hΩ, hx | ⟨z, hE, hL, hf⟩⟩
  · exact ⟨hΩ, Or.inl hx⟩
  · exact ⟨hΩ, Or.inr ⟨z, eligC_mono h hE, hL, hf⟩⟩

theorem incGraph_adj_mono (h : 𝒞₁ ⊆ 𝒞) {u v : IncV d L N₁ m₁ K}
    (hadj : (incGraph C H a ν X₁ 𝒞₁).Adj u v) : (incGraph C H a ν X₁ 𝒞).Adj u v := by
  have key : ∀ u v : IncV d L N₁ m₁ K, incRel C H a ν X₁ 𝒞₁ u v → incRel C H a ν X₁ 𝒞 u v := by
    intro u v hr
    rcases u with x | z | Q <;> rcases v with y | z' | P <;> simp only [incRel] at hr ⊢
    · exact ⟨incSites_mono h hr.1, incSites_mono h hr.2.1, hr.2.2⟩
    · exact ⟨eligC_mono h hr.1, hr.2.1, hr.2.2⟩
    · exact ⟨eligC_mono h hr.1, hr.2.1, hr.2.2.1, h hr.2.2.2⟩
  obtain ⟨hne, h1 | h1⟩ := hadj
  · exact ⟨hne, Or.inl (key _ _ h1)⟩
  · exact ⟨hne, Or.inr (key _ _ h1)⟩

variable (Hb : GeneratingSet d L (N₁ * L ^ m₁) K ϱ') (Hm : GeneratingSet d L (N₁ * L ^ m₁) K ϱ)
  {U U' : Set (CTorus d L N₁ m₁ K)}

/-- **T3.** The joint closure is monotone in the seed. -/
theorem JointIn.mono_seed (hU : U ⊆ U') {o : Bool} {v : IncV d L N₁ m₁ K}
    (h : JointIn C Hb Hm a ν X₁ 𝒞 U o v) : JointIn C Hb Hm a ν X₁ 𝒞 U' o v := by
  induction h with
  | seed o hs => exact JointIn.seed o (hU hs)
  | adjB hadj _ ih => exact JointIn.adjB hadj ih
  | adjM hadj _ ih => exact JointIn.adjM hadj ih
  | site _ ih => exact JointIn.site ih
  | param _ ih => exact JointIn.param ih
  | cell hP _ hx ih => exact JointIn.cell hP ih hx

/-- **T3.** The joint closure is monotone in the set of marked patches. -/
theorem JointIn.mono_param (h𝒞 : 𝒞₁ ⊆ 𝒞) {o : Bool} {v : IncV d L N₁ m₁ K}
    (h : JointIn C Hb Hm a ν X₁ 𝒞₁ U o v) : JointIn C Hb Hm a ν X₁ 𝒞 U o v := by
  induction h with
  | seed o hs => exact JointIn.seed o hs
  | adjB hadj _ ih => exact JointIn.adjB (incGraph_adj_mono h𝒞 hadj) ih
  | adjM hadj _ ih => exact JointIn.adjM (incGraph_adj_mono h𝒞 hadj) ih
  | site _ ih => exact JointIn.site ih
  | param _ ih => exact JointIn.param ih
  | cell hP _ hx ih => exact JointIn.cell (h𝒞 hP) ih hx

theorem jointSites_mono_seed (hU : U ⊆ U') :
    jointSites C Hb Hm a ν X₁ 𝒞 U ⊆ jointSites C Hb Hm a ν X₁ 𝒞 U' := fun _ hx =>
  mem_jointSites.2 ((mem_jointSites.1 hx).mono_seed Hb Hm hU)

theorem jointSites_mono_param (h𝒞 : 𝒞₁ ⊆ 𝒞) :
    jointSites C Hb Hm a ν X₁ 𝒞₁ U ⊆ jointSites C Hb Hm a ν X₁ 𝒞 U := fun _ hx =>
  mem_jointSites.2 ((mem_jointSites.1 hx).mono_param Hb Hm h𝒞)

theorem jointParams_mono_seed (hU : U ⊆ U') :
    jointParams C Hb Hm a ν X₁ 𝒞 U ⊆ jointParams C Hb Hm a ν X₁ 𝒞 U' := fun _ hx =>
  mem_jointParams.2 ((mem_jointParams.1 hx).mono_seed Hb Hm hU)

theorem jointParams_mono_param (h𝒞 : 𝒞₁ ⊆ 𝒞) :
    jointParams C Hb Hm a ν X₁ 𝒞₁ U ⊆ jointParams C Hb Hm a ν X₁ 𝒞 U := fun _ hx =>
  mem_jointParams.2 ((mem_jointParams.1 hx).mono_param Hb Hm h𝒞)

/-- Lowering lemma for one operator: an edge of the incidence graph over `𝒞` from a vertex of a
family `R` closed under these edges, in which every reached marked patch lies in `𝒞₁`, is an edge
over `𝒞₁`. -/
theorem incGraph_adj_down (R : IncV d L N₁ m₁ K → Prop)
    (hR : ∀ u v, (incGraph C H a ν X₁ 𝒞).Adj u v → R u → R v)
    (hQ : ∀ Q, R (Sum.inr (Sum.inr Q)) → Q ∈ 𝒞 → Q ∈ 𝒞₁) {u v : IncV d L N₁ m₁ K}
    (hadj : (incGraph C H a ν X₁ 𝒞).Adj u v) (hu : R u) :
    (incGraph C H a ν X₁ 𝒞₁).Adj u v := by
  have hv := hR u v hadj hu
  have key1 : ∀ z, R (Sum.inr (Sum.inl z)) → EligC C X₁ 𝒞 z → LiveI H z → EligC C X₁ 𝒞₁ z :=
    fun z hz hE hL => ⟨hE.1, fun P hP hpar => hQ P
      (hR (Sum.inr (Sum.inl z)) (Sum.inr (Sum.inr P)) ⟨by simp, Or.inl ⟨hE, hL, hP, hE.2 P hP hpar⟩⟩ hz) (hE.2 P hP hpar)⟩
  have key2 : ∀ x, R (Sum.inl x) → x ∈ incSites C H a ν X₁ 𝒞 → x ∈ incSites C H a ν X₁ 𝒞₁ := by
    rintro x hx ⟨hΩ, hx' | ⟨z, hE, hL, hf⟩⟩
    · exact ⟨hΩ, Or.inl hx'⟩
    · have hz := hR (Sum.inl x) (Sum.inr (Sum.inl z)) ⟨by simp, Or.inr ⟨hE, hL, hf⟩⟩ hx
      exact ⟨hΩ, Or.inr ⟨z, key1 z hz hE hL, hL, hf⟩⟩
  have key : ∀ u v : IncV d L N₁ m₁ K, R u → R v → incRel C H a ν X₁ 𝒞 u v →
      incRel C H a ν X₁ 𝒞₁ u v := by
    intro u v hu hv hr
    rcases u with x | z | Q <;> rcases v with y | z' | P <;> simp only [incRel] at hr ⊢
    · exact ⟨key2 x hu hr.1, key2 y hv hr.2.1, hr.2.2⟩
    · exact ⟨key1 z hu hr.1 hr.2.1, hr.2.1, hr.2.2⟩
    · exact ⟨key1 z hu hr.1 hr.2.1, hr.2.1, hr.2.2.1, hQ P hv hr.2.2.2⟩
  obtain ⟨hne, h1 | h1⟩ := hadj
  · exact ⟨hne, Or.inl (key _ _ hu hv h1)⟩
  · exact ⟨hne, Or.inr (key _ _ hv hu h1)⟩

variable {Hb Hm}

/-- **T3, detachment.**  Let `𝒞 = 𝒞₁ ∪ 𝒞₂` and suppose no patch of `𝒞₂` is reached from the seed in
the joint closure over `𝒞`.  Then everything reached over `𝒞` is reached over `𝒞₁`. -/
theorem JointIn.detach {𝒞₂ : Finset (ℕ × CTorus d L N₁ m₁ K)} (h𝒞 : 𝒞 = 𝒞₁ ∪ 𝒞₂)
    (hdet : ∀ P ∈ 𝒞₂, ¬ JointIn C Hb Hm a ν X₁ 𝒞 U true (Sum.inr (Sum.inr P))) {o : Bool}
    {v : IncV d L N₁ m₁ K} (h : JointIn C Hb Hm a ν X₁ 𝒞 U o v) :
    JointIn C Hb Hm a ν X₁ 𝒞₁ U o v := by
  have hQ : ∀ {o' : Bool} {Q}, JointIn C Hb Hm a ν X₁ 𝒞 U o' (Sum.inr (Sum.inr Q)) → Q ∈ 𝒞 →
      Q ∈ 𝒞₁ := by
    intro o' Q hr hQ𝒞
    rw [h𝒞] at hQ𝒞
    rcases Finset.mem_union.1 hQ𝒞 with h1 | h2
    · exact h1
    · exact absurd (JointIn.param hr) (hdet Q h2)
  induction h with
  | seed o hs => exact JointIn.seed o hs
  | adjB hadj hu ih =>
    exact JointIn.adjB (incGraph_adj_down (H := Hb) (JointIn C Hb Hm a ν X₁ 𝒞 U true)
      (fun _ _ h' hu' => JointIn.adjB h' hu') (fun Q hr hq => hQ hr hq) hadj hu) ih
  | adjM hadj hu ih =>
    exact JointIn.adjM (incGraph_adj_down (H := Hm) (JointIn C Hb Hm a ν X₁ 𝒞 U false)
      (fun _ _ h' hu' => JointIn.adjM h' hu') (fun Q hr hq => hQ hr hq) hadj hu) ih
  | site _ ih => exact JointIn.site ih
  | param _ ih => exact JointIn.param ih
  | cell hP hu hx ih => exact JointIn.cell (hQ hu hP) ih hx

/-- **T3, detachment (sites and parameters).**  If `𝒞 = 𝒞₁ ∪ 𝒞₂` and no patch of `𝒞₂` is reached
over `𝒞` (i.e. `D_𝒞 ∩ 𝒞₂ = ∅`), then `Y_𝒞 = Y_𝒞₁` and `D_𝒞 = D_𝒞₁`: the cut parameters of `𝒞₂` are
outside the dependency set. -/
theorem jointSites_detach {𝒞₂ : Finset (ℕ × CTorus d L N₁ m₁ K)} (h𝒞 : 𝒞 = 𝒞₁ ∪ 𝒞₂)
    (hdet : ∀ P ∈ 𝒞₂, P ∉ jointParams C Hb Hm a ν X₁ 𝒞 U) :
    jointSites C Hb Hm a ν X₁ 𝒞 U = jointSites C Hb Hm a ν X₁ 𝒞₁ U ∧
      jointParams C Hb Hm a ν X₁ 𝒞 U = jointParams C Hb Hm a ν X₁ 𝒞₁ U := by
  have hd : ∀ P ∈ 𝒞₂, ¬ JointIn C Hb Hm a ν X₁ 𝒞 U true (Sum.inr (Sum.inr P)) :=
    fun P hP h => hdet P hP (mem_jointParams.2 h)
  have hsub : 𝒞₁ ⊆ 𝒞 := by rw [h𝒞]; exact Finset.subset_union_left
  exact ⟨Finset.Subset.antisymm (fun x hx => mem_jointSites.2
      (JointIn.detach h𝒞 hd (mem_jointSites.1 hx))) (jointSites_mono_param Hb Hm hsub),
    Finset.Subset.antisymm (fun P hP => mem_jointParams.2
      (JointIn.detach h𝒞 hd (mem_jointParams.1 hP))) (jointParams_mono_param Hb Hm hsub)⟩

end Mono

section Hat

variable (C : DecCover d L N₁ m₁ K) (𝒞 : Finset (ℕ × CTorus d L N₁ m₁ K))
  (U : Set (CTorus d L N₁ m₁ K))

/-- The site `x` is **hat-near** the centre `z`: it lies in the thickened box `□̂_z` or is a
nearest neighbour of a site of it. -/
def PairHatNear (z : ℕ × CTorus d L N₁ m₁ K) (x : CTorus d L N₁ m₁ K) : Prop :=
  ∃ y ∈ hatBox z, x = y ∨ Adj x y

/-- **The hat link**: `x` is hat-near a centre `z` of the cover and `y` lies in `□̂_z`. -/
def HatLink (x y : CTorus d L N₁ m₁ K) : Prop :=
  ∃ z ∈ C.cubeIdx, PairHatNear z x ∧ y ∈ hatBox z

/-- **Hat-rootedness of a marked patch** (T4).  `P ∈ 𝒞` is hat-rooted at the seed `U` if a chain of
marked patches `P₀, …, P = Pₙ` exists in which `P₀` has a cover centre `z₀` with `P₀ ∈ 𝒬(z₀)` and
`z₀` hat-near a site hat-linked (by a chain of centres) to the seed, and `P_{i+1} ∈ 𝒬(z)` for a
centre `z` hat-near a site hat-linked to the cell `cubeP P_i`.

This is the adjacency that is true for the multiscale cover: two patches of `𝒬(z)` need not touch
(each only meets `□̂_z`, of radius about `3 L² ℓ_j`), so consecutive patches are linked through a
cover centre, not through Moore adjacency (`MooreTouch`).  See the module documentation. -/
inductive PairHatRooted : ℕ × CTorus d L N₁ m₁ K → Prop
  | root {P z : ℕ × CTorus d L N₁ m₁ K} {s x : CTorus d L N₁ m₁ K} :
      P ∈ 𝒞 → P ∈ C.Qset z → s ∈ U → Relation.ReflTransGen (HatLink C) s x → PairHatNear z x →
      PairHatRooted P
  | step {P P' z : ℕ × CTorus d L N₁ m₁ K} {x₀ x : CTorus d L N₁ m₁ K} :
      PairHatRooted P → P' ∈ 𝒞 → P' ∈ C.Qset z → x₀ ∈ cubeP P →
      Relation.ReflTransGen (HatLink C) x₀ x → PairHatNear z x → PairHatRooted P'

/-- The sites hat-linked to the seed or to the cell of a hat-rooted patch. -/
def PairHatSite (x : CTorus d L N₁ m₁ K) : Prop :=
  (∃ s ∈ U, Relation.ReflTransGen (HatLink C) s x) ∨
    ∃ P, PairHatRooted C 𝒞 U P ∧ ∃ x₀ ∈ cubeP P, Relation.ReflTransGen (HatLink C) x₀ x

variable {C 𝒞 U}

theorem PairHatSite.conn {x y : CTorus d L N₁ m₁ K} (hx : PairHatSite C 𝒞 U x) (h : HatLink C x y) :
    PairHatSite C 𝒞 U y := by
  rcases hx with ⟨s, hs, hr⟩ | ⟨P, hP, x₀, hx₀, hr⟩
  · exact Or.inl ⟨s, hs, hr.tail h⟩
  · exact Or.inr ⟨P, hP, x₀, hx₀, hr.tail h⟩

theorem PairHatSite.of_cell {P : ℕ × CTorus d L N₁ m₁ K} (hP : PairHatRooted C 𝒞 U P)
    {x : CTorus d L N₁ m₁ K} (hx : x ∈ cubeP P) : PairHatSite C 𝒞 U x :=
  Or.inr ⟨P, hP, x, hx, Relation.ReflTransGen.refl⟩

theorem PairHatSite.rooted {x : CTorus d L N₁ m₁ K} (hx : PairHatSite C 𝒞 U x)
    {z P : ℕ × CTorus d L N₁ m₁ K} (hP𝒞 : P ∈ 𝒞) (hQ : P ∈ C.Qset z) (hn : PairHatNear z x) :
    PairHatRooted C 𝒞 U P := by
  rcases hx with ⟨s, hs, hr⟩ | ⟨P₀, hP₀, x₀, hx₀, hr⟩
  · exact PairHatRooted.root hP𝒞 hQ hs hr hn
  · exact PairHatRooted.step hP₀ hP𝒞 hQ hx₀ hr hn

/-- The invariant of the joint closure: sites are hat-linked, centres are hat-near a hat-linked
site, parameters are hat-rooted. -/
def PairHatInv : IncV d L N₁ m₁ K → Prop
  | Sum.inl x => PairHatSite C 𝒞 U x
  | Sum.inr (Sum.inl z) => z ∈ C.cubeIdx ∧ ∃ x, PairHatSite C 𝒞 U x ∧ PairHatNear z x
  | Sum.inr (Sum.inr P) => P ∈ 𝒞 ∧ PairHatRooted C 𝒞 U P

variable {H : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {a : ℕ → ℝ} {ν : ℝ}
  {X₁ : Finset (CTorus d L N₁ m₁ K)}

theorem PairHatNear.of_mem {z : ℕ × CTorus d L N₁ m₁ K} {y : CTorus d L N₁ m₁ K} (h : y ∈ hatBox z) :
    PairHatNear z y := ⟨y, h, Or.inl rfl⟩

theorem PairHatNear.of_adj {z : ℕ × CTorus d L N₁ m₁ K} {x y : CTorus d L N₁ m₁ K}
    (h : y ∈ hatBox z) (hxy : Adj x y) : PairHatNear z x := ⟨y, h, Or.inr hxy⟩

/-- **The invariant is preserved along edges of the incidence graph** (footprints lie in the
thickened boxes). -/
theorem hatInv_step (hfp : ∀ z ∈ C.cubeIdx, ∀ t ∈ footprint H a ν z, t ∈ hatBox z)
    (hX : ∀ x ∈ X₁, x ∈ U) {u v : IncV d L N₁ m₁ K}
    (hadj : (incGraph C H a ν X₁ 𝒞).Adj u v) (hu : PairHatInv (C := C) (𝒞 := 𝒞) (U := U) u) :
    PairHatInv (C := C) (𝒞 := 𝒞) (U := U) v := by
  have site : ∀ x y, x ∈ incSites C H a ν X₁ 𝒞 → y ∈ incSites C H a ν X₁ 𝒞 → Adj x y →
      PairHatSite C 𝒞 U x → PairHatSite C 𝒞 U y := by
    rintro x y - ⟨-, hy | ⟨z, hE, hL, hf⟩⟩ hxy hx
    · exact Or.inl ⟨y, hX y hy, Relation.ReflTransGen.refl⟩
    · exact hx.conn ⟨z, hE.1, PairHatNear.of_adj (hfp z hE.1 y hf) hxy, hfp z hE.1 y hf⟩
  have fwd : ∀ u v : IncV d L N₁ m₁ K, incRel C H a ν X₁ 𝒞 u v →
      PairHatInv (C := C) (𝒞 := 𝒞) (U := U) u → PairHatInv (C := C) (𝒞 := 𝒞) (U := U) v := by
    intro u v h hu
    rcases u with x | z | Q <;> rcases v with y | z' | P <;> simp only [incRel] at h
    · exact site x y h.1 h.2.1 h.2.2 hu
    · obtain ⟨hz, x', hx', hn⟩ := hu
      exact hx'.conn ⟨z, hz, hn, hfp z hz y h.2.2⟩
    · obtain ⟨hz, x', hx', hn⟩ := hu
      exact ⟨h.2.2.2, hx'.rooted h.2.2.2 h.2.2.1 hn⟩
  have bwd : ∀ u v : IncV d L N₁ m₁ K, incRel C H a ν X₁ 𝒞 v u →
      PairHatInv (C := C) (𝒞 := 𝒞) (U := U) u → PairHatInv (C := C) (𝒞 := 𝒞) (U := U) v := by
    intro u v h hu
    rcases u with x | z | Q <;> rcases v with y | z' | P <;> simp only [incRel] at h
    · exact site x y h.2.1 h.1 h.2.2.symm hu
    · exact ⟨h.1.1, x, hu, PairHatNear.of_mem (hfp z' h.1.1 x h.2.2)⟩
    · obtain ⟨-, hr⟩ := hu
      obtain ⟨-, y, hy, hyb⟩ := C.mem_Qset.1 h.2.2.1
      exact ⟨h.1.1, y, PairHatSite.of_cell hr (mem_cubeP.2 hy), PairHatNear.of_mem (mem_boxSet.2 hyb)⟩
  obtain ⟨-, h | h⟩ := hadj
  · exact fwd u v h hu
  · exact bwd u v h hu

variable {ϱ' : ℝ} {Hb : GeneratingSet d L (N₁ * L ^ m₁) K ϱ'}

/-- **T4. The joint closure is hat-linked to the seed.**  If the footprints of both operators lie
in the thickened boxes of their centres and `X₁ ⊆ U`, every vertex reached from the seed `U` in the
joint closure satisfies `PairHatInv`: a reached site is hat-linked to the seed or to the cell of a
hat-rooted patch, a reached parameter is a hat-rooted patch of `𝒞`. -/
theorem JointIn.hatInv (hfb : ∀ z ∈ C.cubeIdx, ∀ t ∈ footprint Hb a ν z, t ∈ hatBox z)
    (hfm : ∀ z ∈ C.cubeIdx, ∀ t ∈ footprint H a ν z, t ∈ hatBox z)
    (hX : ∀ x ∈ X₁, x ∈ U) {o : Bool} {v : IncV d L N₁ m₁ K}
    (h : JointIn C Hb H a ν X₁ 𝒞 U o v) : PairHatInv (C := C) (𝒞 := 𝒞) (U := U) v := by
  induction h with
  | seed o hs => exact Or.inl ⟨_, hs, Relation.ReflTransGen.refl⟩
  | adjB hadj _ ih => exact hatInv_step hfb hX hadj ih
  | adjM hadj _ ih => exact hatInv_step hfm hX hadj ih
  | site _ ih => exact ih
  | param _ ih => exact ih
  | cell _ _ hx ih => exact PairHatSite.of_cell ih.2 hx

/-- **T4. Every reached marked patch is hat-rooted, and every reached site is hat-linked.** -/
theorem jointParams_hatRooted (hfb : ∀ z ∈ C.cubeIdx, ∀ t ∈ footprint Hb a ν z, t ∈ hatBox z)
    (hfm : ∀ z ∈ C.cubeIdx, ∀ t ∈ footprint H a ν z, t ∈ hatBox z)
    (hX : ∀ x ∈ X₁, x ∈ U) :
    (∀ P ∈ jointParams C Hb H a ν X₁ 𝒞 U, P ∈ 𝒞 ∧ PairHatRooted C 𝒞 U P) ∧
      ∀ x ∈ jointSites C Hb H a ν X₁ 𝒞 U, PairHatSite C 𝒞 U x :=
  ⟨fun _ hP => (JointIn.hatInv hfb hfm hX (mem_jointParams.1 hP) :), fun _ hx =>
    JointIn.hatInv hfb hfm hX (mem_jointSites.1 hx)⟩

end Hat

section Paired

variable {C : DecCover d L N₁ m₁ K} {Hb : GeneratingSet d L (N₁ * L ^ m₁) K ϱ'}
  {Hm : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {a : ℕ → ℝ} {ν : ℝ}

/-- **T5. The graph hypotheses of `paired_locality`.**  With the common seed `X₁` and
`Y_f(J) := jointSites … (J.image cc) ↑X₁`, the hypotheses `hXY` and the graph part of `hG`
(both `IsIncUnion` with the selected incidence patches `Ab = Am = jointParams` contained in
`Y_f(J)`) hold, with the exact shapes consumed by `paired_locality`.  The remaining hypotheses of
`paired_locality` (selectors `Fb`, `Sol`, data domains, `hdepb`, `hdepm`) are not treated. -/
theorem paired_graph_hyps {ι : Type*} [DecidableEq ι] (cc : ι → ℕ × CTorus d L N₁ m₁ K)
    (X₁ : Finset (CTorus d L N₁ m₁ K)) :
    (∀ J : Finset ι, ∀ y ∈ X₁, y ∈ jointSites C Hb Hm a ν X₁ (J.image cc) (↑X₁ : Set _)) ∧
    ∀ J : Finset ι, ∃ Ab Am : Finset (ℕ × CTorus d L N₁ m₁ K),
      IsIncUnion C Hb a ν X₁ (J.image cc) (jointSites C Hb Hm a ν X₁ (J.image cc) ↑X₁) Ab ∧
      IsIncUnion C Hm a ν X₁ (J.image cc) (jointSites C Hb Hm a ν X₁ (J.image cc) ↑X₁) Am ∧
      (∀ P ∈ Ab, ∀ x ∈ cubeP P, x ∈ jointSites C Hb Hm a ν X₁ (J.image cc) ↑X₁) ∧
      (∀ P ∈ Am, ∀ x ∈ cubeP P, x ∈ jointSites C Hb Hm a ν X₁ (J.image cc) ↑X₁) :=
  ⟨fun _ _ hy => seed_mem_jointSites (Finset.mem_coe.2 hy), fun _ =>
    ⟨_, _, isIncUnion_joint_b, isIncUnion_joint_m, fun _ hP => (joint_cell hP).2,
      fun _ hP => (joint_cell hP).2⟩⟩

end Paired

end Balaban.Localization.Dec2

namespace Balaban.LargeField

open Balaban Balaban.Multiscale Balaban.Localization Balaban.Localization.Dec2

set_option linter.unusedSectionVars false

section P6

variable {d M1 c n1 L k n0 m₁ : ℕ} [NeZero L] [NeZero M1] [NeZero c] [NeZero n0] [NeZero n1]
  {Rprev Rk : ℝ} {Zp : Set (Torus d n1)} (st : RegionStep d L n0 n1 Rprev Rk)

/-- **T4/T5 for the P6 pair.**  For `C = coverOf F♯`, `H_b = H^∂ = p6BoundaryC`, `H_m = H^- = p6OldC`
(the old operator built from the same `Z = st.Z` and `ρ' = ⌊R_{k-1}⌋`), every parameter patch
reached from a seed `U ⊇ X₁` in the joint closure over the marked set `𝒞` lies in `𝒞` and is
hat-rooted at `U` (`PairHatRooted`), and every reached site is hat-linked to the seed or to the
cell of a hat-rooted patch.  The source premises are those of `p6_coverGeom_old` and
`p6_coverGeom_boundary`; the statement is combinatorial and says nothing about coefficients. -/
theorem p6_joint_hatRooted (hc : 14 ≤ c) (hn : n0 = L * n1) (hL : 2 ≤ L)
    (hρ : 3 * L ≤ ⌊Rprev⌋₊) (hZ : st.Omegaᶜ ⊆ Zp) (hM1 : M1 = L ^ m₁) (hm₁ : 2 ≤ m₁)
    (hM : 4 * L ^ 2 ≤ L ^ m₁) {a : ℕ → ℝ} {ν : ℝ} (hd : 3 ≤ d) (hL3 : 3 ≤ L) (hν : 0 ≤ ν)
    (hνL : ν * ((L : ℝ) ^ (k + 1)) ^ 2 ≤ 1) (ha : IsAdmissibleWeights (k + 1) a)
    (hsep : 2 * d * Real.log L ≤ agmonRate d / 16 * (minSep L M1 - 1))
    (X₁ : Finset (Localization.CTorus d L (c * n1) m₁ (k + 1)))
    (𝒞 : Finset (ℕ × Localization.CTorus d L (c * n1) m₁ (k + 1)))
    (U : Set (Localization.CTorus d L (c * n1) m₁ (k + 1))) (hX : ∀ x ∈ X₁, x ∈ U) :
    (∀ P ∈ jointParams (coverOf (p6FsharpC (k := k) hn hρ (by omega : 5 ≤ c) st.Z hM1))
        (p6BoundaryC (k := k) st hM1 hc hn hL hρ hZ)
        (p6OldC (k := k) (n1 := n1) (c := c) hM1 ⌊Rprev⌋₊ st.Z) a ν X₁ 𝒞 U,
      P ∈ 𝒞 ∧ PairHatRooted (coverOf (p6FsharpC (k := k) hn hρ (by omega : 5 ≤ c) st.Z hM1)) 𝒞 U P) ∧
    (∀ x ∈ jointSites (coverOf (p6FsharpC (k := k) hn hρ (by omega : 5 ≤ c) st.Z hM1))
        (p6BoundaryC (k := k) st hM1 hc hn hL hρ hZ)
        (p6OldC (k := k) (n1 := n1) (c := c) hM1 ⌊Rprev⌋₊ st.Z) a ν X₁ 𝒞 U,
      PairHatSite (coverOf (p6FsharpC (k := k) hn hρ (by omega : 5 ≤ c) st.Z hM1)) 𝒞 U x) :=
  jointParams_hatRooted
    (footprint_hat_of_coverGeom (p6_coverGeom_boundary st hc hn hL hρ hZ hM1 hm₁ hM hd hL3 hν hνL
      ha hsep))
    (footprint_hat_of_coverGeom (p6_coverGeom_old hn hρ (by omega : 5 ≤ c) st.Z hM1 hm₁ hM hd hL3
      hν hνL ha hsep)) hX

end P6

end Balaban.LargeField
