/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.Decoupled2Self

/-!
# The footprint interface of the locality (VMOD-4): cover and operator with different domains

The landed locality (`Decoupled2Geometry.lean`) assumes `cubeP_sub` and `own_cover`, which force the
first domain of the cover to coincide with that of the operator.  This file replaces them by:

* `FootLocalGeom C`: `supp χ_z ⊂ C_z` and nothing else (`chi_core`);
* the footprint `footprint H a ν z = I_H(z) ∪ rows of the potential-free operator` of a centre
  (`footprint_row`: the rows of `H_D(α)` at the operator sites of `□_z` stay in it, for every `α`);
* a centre without operator sites contributes nothing (`cubeG_dead`, `Kz_cubeG_dead`);
* the parameter-incidence graph `incGraph` on sites, centres and parameters, and the predicate
  `IsIncUnion` (`(Y, A)` is a union of components of the graph) with its dichotomy
  (`IsIncUnion.dichotomy`).
-/

@[expose] public section

namespace Balaban.Localization.Dec2

open Balaban Balaban.Multiscale Balaban.Background Balaban.Reflection Finset Matrix

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}

section Interface

variable (C : DecCover d L N₁ m₁ K)

/-- **The geometry of the cover used by the footprint locality**: `supp χ_z ⊂ C_z`. -/
structure FootLocalGeom : Prop where
  chi_core : ∀ q ∈ C.cubeIdx, ∀ x, C.chi q x ≠ 0 →
    InBox m₁ q.1 q.2 (3 / 2 * (L : ℝ) ^ (q.1 + m₁)) x

variable (H : GeneratingSet d L (N₁ * L ^ m₁) K ϱ) (a : ℕ → ℝ) (ν Kc Cx : ℝ)

/-- **The properties of the pair used by the footprint locality**: `CoverBase` and
`FootLocalGeom`. -/
structure FootLocal : Prop extends CoverBase C H a ν Kc Cx, FootLocalGeom C

end Interface

section Compare

variable {C : DecCover d L N₁ m₁ K} {H : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {a : ℕ → ℝ} {ν : ℝ}
  {Kc Cx : ℝ}

/-- The old geometry implies the new one. -/
theorem FootLocalGeom.of_coverLocalGeom (S : CoverLocalGeom C H a ν Cx) : FootLocalGeom C :=
  ⟨S.chi_supp⟩

/-- The old pair properties imply the new ones. -/
theorem FootLocal.of_coverLocal (S : CoverLocal C H a ν Kc Cx) : FootLocal C H a ν Kc Cx :=
  { toCoverBase := S.toCoverBase
    chi_core := S.chi_supp }

/-- `FootLocalGeom` holds for the cover of any generating set `F` (it does not involve the
operator). -/
theorem footLocalGeom_coverOf (F : GeneratingSet d L (N₁ * L ^ m₁) K ϱ) :
    FootLocalGeom (coverOf F) :=
  ⟨fun _ _ _ h => inBox_of_chi_ne_zero h⟩

omit [NeZero N₁] [NeZero L] in
/-- **Inhabitation of `FootLocalGeom`**: the empty cover. -/
theorem footLocalGeom_nonempty :
    Nonempty (FootLocalGeom (⟨∅, fun _ _ => 0⟩ : DecCover d L N₁ m₁ K)) :=
  ⟨⟨fun _ hq => absurd hq (by simp)⟩⟩

/-- **Inhabitation of `FootLocal`** at the pair `(coverOf G, G)` of the landed same-domain
setting. -/
theorem footLocal_nonempty {G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {a : ℕ → ℝ} {ν : ℝ}
    (S : DGSetting G a ν) :
    Nonempty (FootLocal (coverOf G) G a ν (selfKc d L) (Cchi d L)) :=
  ⟨{ toCoverBase := coverBase_self S
     chi_core := (footLocalGeom_coverOf G).chi_core }⟩

end Compare

section Footprint

variable {C : DecCover d L N₁ m₁ K} {H : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {a : ℕ → ℝ} {ν : ℝ}
  {Kc Cx : ℝ} {α : H.Ω 1 → ℂ}

variable (H) in
/-- The centre `z` is **live**: its interaction cube contains a site of `Ω₁(H)`. -/
def LiveI (z : ℕ × CTorus d L N₁ m₁ K) : Prop :=
  ∃ x : H.Ω 1, (x : CTorus d L N₁ m₁ K) ∈ intBox z

variable (H a ν) in
/-- **The operator footprint of a centre**: the operator sites of `□_z` and the columns of the
potential-free operator `H_D(0)` in their rows. -/
def footprint (z : ℕ × CTorus d L N₁ m₁ K) : Set (CTorus d L N₁ m₁ K) :=
  {x | ∃ b : H.Ω 1, (b : CTorus d L N₁ m₁ K) ∈ intBox z ∧
    (x = (b : CTorus d L N₁ m₁ K) ∨
      ∃ y : H.Ω 1, dirichletOperator H a ν 0 b y ≠ 0 ∧ x = (y : CTorus d L N₁ m₁ K))}

theorem mem_footprint_self {z : ℕ × CTorus d L N₁ m₁ K} {b : H.Ω 1}
    (hb : (b : CTorus d L N₁ m₁ K) ∈ intBox z) : (b : CTorus d L N₁ m₁ K) ∈ footprint H a ν z :=
  ⟨b, hb, Or.inl rfl⟩

/-- **(2.2) The rows of the operator at the operator sites of `□_z` stay in the footprint, for every
potential.** -/
theorem footprint_row {z : ℕ × CTorus d L N₁ m₁ K} {b : H.Ω 1}
    (hb : (b : CTorus d L N₁ m₁ K) ∈ intBox z) (α : H.Ω 1 → ℂ) {y : H.Ω 1}
    (h : dirichletOperator H a ν α b y ≠ 0) : (y : CTorus d L N₁ m₁ K) ∈ footprint H a ν z := by
  by_cases hby : b = y
  · subst hby; exact mem_footprint_self hb
  · refine ⟨b, hb, Or.inr ⟨y, ?_, rfl⟩⟩
    rw [dirichletOperator_eq_add a ν α] at h
    simpa [Matrix.add_apply, Matrix.diagonal_apply, hby] using h

/-- A centre without operator sites has a zero cube indicator. -/
theorem cD_dead {z : ℕ × CTorus d L N₁ m₁ K} (hz : ¬ LiveI H z) : cD H z = 0 := by
  classical
  unfold cD
  have : (fun x : H.Ω 1 => if (x : CTorus d L N₁ m₁ K) ∈ intBox z then (1 : ℂ) else 0) =
      fun _ => 0 := by
    funext x
    exact ite_eq_right_iff.2 (fun h => absurd ⟨x, h⟩ hz)
  rw [this]
  exact Matrix.diagonal_zero

/-- **(2.5)** A centre without operator sites has `cubeG = 0`. -/
theorem cubeG_dead {z : ℕ × CTorus d L N₁ m₁ K} (hz : ¬ LiveI H z) (α : H.Ω 1 → ℂ) :
    cubeG H a ν α z = 0 := by
  unfold cubeG
  rw [cD_dead hz, Matrix.mul_zero]

theorem Kz_cubeG_dead {z : ℕ × CTorus d L N₁ m₁ K} (hz : ¬ LiveI H z) (α : H.Ω 1 → ℂ) :
    Kz C H a ν z * cubeG H a ν α z = 0 := by
  rw [cubeG_dead hz, Matrix.mul_zero]

theorem chiD_cubeG_dead {z : ℕ × CTorus d L N₁ m₁ K} (hz : ¬ LiveI H z) (α : H.Ω 1 → ℂ) :
    chiD C H z * cubeG H a ν α z = 0 := by
  rw [cubeG_dead hz, Matrix.mul_zero]

end Footprint

section Graph

variable (C : DecCover d L N₁ m₁ K) (H : GeneratingSet d L (N₁ * L ^ m₁) K ϱ) (a : ℕ → ℝ) (ν : ℝ)
  (X₁ : Finset (CTorus d L N₁ m₁ K)) (𝒞 : Finset (ℕ × CTorus d L N₁ m₁ K))

/-- A centre is **eligible**: it is a centre of the cover and all its parameter cubes lie in `𝒞`
(or are not parameter cubes). -/
def EligC (z : ℕ × CTorus d L N₁ m₁ K) : Prop :=
  z ∈ C.cubeIdx ∧ ∀ P ∈ C.Qset z, P ∈ C.parCubes X₁ → P ∈ 𝒞

/-- The vertices of the incidence graph: sites, centres, parameter cubes. -/
abbrev IncV (d L N₁ m₁ K : ℕ) [NeZero N₁] [NeZero L] : Type :=
  CTorus d L N₁ m₁ K ⊕ (ℕ × CTorus d L N₁ m₁ K) ⊕ (ℕ × CTorus d L N₁ m₁ K)

/-- The site vertices: the sites of `X₁ ∩ Ω₁(H)` and the footprints of eligible live centres. -/
def incSites : Set (CTorus d L N₁ m₁ K) :=
  {x | x ∈ H.Ω 1 ∧ (x ∈ X₁ ∨ ∃ z, EligC C X₁ 𝒞 z ∧ LiveI H z ∧ x ∈ footprint H a ν z)}

/-- The generating relation of the incidence graph: nearest-neighbour sites; an eligible live
centre to every site of its footprint and to every parameter of `𝒬(z) ∩ 𝒞`. -/
def incRel : IncV d L N₁ m₁ K → IncV d L N₁ m₁ K → Prop
  | .inl x, .inl y => x ∈ incSites C H a ν X₁ 𝒞 ∧ y ∈ incSites C H a ν X₁ 𝒞 ∧ Adj x y
  | .inr (.inl z), .inl x => EligC C X₁ 𝒞 z ∧ LiveI H z ∧ x ∈ footprint H a ν z
  | .inr (.inl z), .inr (.inr P) => EligC C X₁ 𝒞 z ∧ LiveI H z ∧ P ∈ C.Qset z ∧ P ∈ 𝒞
  | _, _ => False

/-- **The parameter-incidence graph** `𝔊_H(X₁, 𝒞)` (VMOD-4 §2.3). -/
def incGraph : SimpleGraph (IncV d L N₁ m₁ K) :=
  SimpleGraph.fromRel (incRel C H a ν X₁ 𝒞)

/-- **`(Y, A)` is a union of components of the incidence graph**: the sites in `Y` and the
parameters in `A` are the site and parameter vertices of a set of vertices closed under
adjacency. -/
def IsIncUnion (Y : Finset (CTorus d L N₁ m₁ K)) (A : Finset (ℕ × CTorus d L N₁ m₁ K)) : Prop :=
  ∃ U : Set (IncV d L N₁ m₁ K),
    (∀ u v, (incGraph C H a ν X₁ 𝒞).Adj u v → u ∈ U → v ∈ U) ∧
    (∀ x, x ∈ Y ↔ Sum.inl x ∈ U) ∧ (∀ P, P ∈ A ↔ Sum.inr (Sum.inr P) ∈ U)

variable {C H a ν X₁ 𝒞}

/-- **The dichotomy**: for an eligible live centre, either its whole footprint lies in `Y` and
its charged parameters in `A`, or its footprint misses `Y`. -/
theorem IsIncUnion.dichotomy {Y : Finset (CTorus d L N₁ m₁ K)}
    {A : Finset (ℕ × CTorus d L N₁ m₁ K)} (hY : IsIncUnion C H a ν X₁ 𝒞 Y A)
    {z : ℕ × CTorus d L N₁ m₁ K} (hE : EligC C X₁ 𝒞 z) (hL : LiveI H z) :
    ((∀ x ∈ footprint H a ν z, x ∈ Y) ∧ ∀ P ∈ C.Qset z, P ∈ 𝒞 → P ∈ A) ∨
      (∀ x ∈ footprint H a ν z, x ∉ Y) := by
  obtain ⟨U, hcl, hYU, hAU⟩ := hY
  by_cases hz : (Sum.inr (Sum.inl z) : IncV d L N₁ m₁ K) ∈ U
  · left
    refine ⟨fun x hx => (hYU x).2 (hcl _ _ ?_ hz), fun P hP hPC => (hAU P).2 (hcl _ _ ?_ hz)⟩
    · refine ⟨by simp, Or.inl ⟨hE, hL, hx⟩⟩
    · refine ⟨by simp, Or.inl ⟨hE, hL, hP, hPC⟩⟩
  · right
    intro x hx hxY
    refine hz (hcl _ _ ?_ ((hYU x).1 hxY))
    exact ⟨by simp, Or.inr ⟨hE, hL, hx⟩⟩

/-- `(∅, ∅)` is a union of components. -/
theorem isIncUnion_empty : IsIncUnion C H a ν X₁ 𝒞 ∅ ∅ :=
  ⟨∅, fun _ _ _ h => absurd h (by simp), by simp, by simp⟩

/-- `(univ, 𝒞)` is a union of components (all sites and centres, the parameters of `𝒞`). -/
theorem isIncUnion_univ : IsIncUnion C H a ν X₁ 𝒞 Finset.univ 𝒞 := by
  classical
  refine ⟨{v | match v with
    | .inl _ => True
    | .inr (.inl _) => True
    | .inr (.inr P) => P ∈ 𝒞}, ?_, by simp, by simp⟩
  intro u v hadj _
  obtain ⟨-, h | h⟩ := hadj
  · rcases v with x | z | P
    · trivial
    · trivial
    · rcases u with x | z | P <;> simp [incRel] at h ⊢
      exact h.2.2.2
  · rcases v with x | z | P
    · trivial
    · trivial
    · simp [incRel] at h

end Graph

end Balaban.Localization.Dec2
