module

public import Balaban.LargeField.Geometry.Components
public import Balaban.LargeField.Geometry.Openings
public import Balaban.LargeField.Geometry.Continuous
public import Mathlib.Topology.Connected.Basic
public import Mathlib.Basic.ENNReal.Real
public import Mathlib.Analysis.Real.Sqrt

/-!
# Localization domains modulo `Ω^c` (Part I, Definition I.2.15)

At cube level (the torus `𝕋_k = Torus d n`, `n = n_k`):

* `IsDomain X` (`X ∈ 𝒟_k`): `X` is nonempty and nn-connected. (This is the cube-level form of
  Def-2 `Balaban.IsPolymer` with block side `M L^k`: a polymer is the union of the fibres
  `blockFibre (M L^k)` of such a set of cubes.)
* `DmodOmega Ω X` (`X ∈ 𝒟_k(mod Ω^c)`): `X ∈ 𝒟_k` and every nearest-neighbour component `nnComp` of
  `Ω^c` is contained in `X` or disjoint from `X` (P5 (1.33); ruling CLASS-RULINGS Q-E). The
  `*`-components `starComp` of `LemmaS` are a separate notion and are not used here.
* `treeLengthMod L Ω X` (`d_k(X mod Ω^c)`): the infimum, in cube units, of the lengths of connected
  finite unions of straight segments `Γ ⊂ ⋃_{x ∈ X} □_x` meeting every `L`-block `Bl(c)` with
  `Bl(c) ∩ X ∩ Ω ≠ ∅` (meeting `Bl(c)` means meeting a cube `□_y`, `y ∈ Bl(c)`). The length of
  a segment is Euclidean; the length of a finite union is bounded by the sum of the lengths, and the
  infimum is taken over the finite families of segments (the two infima coincide).
-/

@[expose] public section

namespace Balaban.LargeField

open Balaban

variable {d n : ℕ}

/-- Nearest-neighbour adjacency on the torus. -/
def NNAdj (a b : Torus d n) : Prop := ∃ μ : Fin d, b = a + Pi.single μ 1 ∨ a = b + Pi.single μ 1

/-- `X ∈ 𝒟_k`: nonempty and nn-connected. -/
def IsDomain (X : Finset (Torus d n)) : Prop :=
  X.Nonempty ∧ ∀ x ∈ X, ∀ y ∈ X, Relation.ReflTransGen
    (fun a b => a ∈ X ∧ b ∈ X ∧ NNAdj a b) x y

/-- The `*`-component of `a` in `T`: the points of `T` linked to `a` by chains of consecutive
sup-distance `≤ 1`. -/
def starComp [NeZero n] (T : Set (Torus d n)) (a : Torus d n) : Set (Torus d n) :=
  {b | b ∈ T ∧ Linked 2 T a b}

/-- The nearest-neighbour component of `a` in `T`: the points of `T` reached from `a` by chains of
`NNAdj` steps inside `T`. -/
def nnComp (T : Set (Torus d n)) (a : Torus d n) : Set (Torus d n) :=
  {b | b ∈ T ∧ Relation.ReflTransGen (fun u v => u ∈ T ∧ v ∈ T ∧ NNAdj u v) a b}

/-- `X ∈ 𝒟_k(mod Ω^c)` (P5 (1.33), ruling CLASS-RULINGS Q-E): `X ∈ 𝒟_k` and every
nearest-neighbour component of `Ω^c` is contained in `X` or disjoint from `X`. -/
def DmodOmega (Ω : Set (Torus d n)) (X : Finset (Torus d n)) : Prop :=
  IsDomain X ∧ ∀ a ∈ Ωᶜ, nnComp Ωᶜ a ⊆ (X : Set (Torus d n)) ∨
    Disjoint (nnComp Ωᶜ a) (X : Set (Torus d n))

theorem mem_nnComp_self {T : Set (Torus d n)} {a : Torus d n} (ha : a ∈ T) : a ∈ nnComp T a :=
  ⟨ha, Relation.ReflTransGen.refl⟩

theorem nnComp_subset {T : Set (Torus d n)} (a : Torus d n) : nnComp T a ⊆ T := fun _ h => h.1

theorem nnComp_mono {T U : Set (Torus d n)} (h : T ⊆ U) (a : Torus d n) :
    nnComp T a ⊆ nnComp U a := by
  rintro b ⟨hb, hab⟩
  refine ⟨h hb, ?_⟩
  clear hb
  induction hab with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih => exact ih.tail ⟨h hbc.1, h hbc.2.1, hbc.2.2⟩

theorem nnComp_eq_of_mem {T : Set (Torus d n)} {a b : Torus d n} (hb : b ∈ nnComp T a) :
    nnComp T b = nnComp T a := by
  have hsymm : ∀ {u v}, Relation.ReflTransGen (fun u v => u ∈ T ∧ v ∈ T ∧ NNAdj u v) u v →
      Relation.ReflTransGen (fun u v => u ∈ T ∧ v ∈ T ∧ NNAdj u v) v u := by
    intro u v h
    induction h with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ hbc ih =>
      obtain ⟨hx, hy, μ, h | h⟩ := hbc
      · exact Relation.ReflTransGen.head ⟨hy, hx, μ, Or.inr h⟩ ih
      · exact Relation.ReflTransGen.head ⟨hy, hx, μ, Or.inl h⟩ ih
  ext c
  constructor
  · rintro ⟨hc, h⟩
    exact ⟨hc, (hb.2).trans h⟩
  · rintro ⟨hc, h⟩
    exact ⟨hc, (hsymm hb.2).trans h⟩

/-- The nn components of `Ω^c` are contained in `Ω^c`, so a set `X ∈ 𝒟_k(mod Ω^c)` that meets a
component contains it. -/
theorem DmodOmega.comp_subset {Ω : Set (Torus d n)} {X : Finset (Torus d n)}
    (h : DmodOmega Ω X) {a : Torus d n} (ha : a ∈ Ωᶜ) {x : Torus d n} (hx : x ∈ nnComp Ωᶜ a)
    (hxX : x ∈ X) : nnComp Ωᶜ a ⊆ X := by
  rcases h.2 a ha with h1 | h1
  · exact h1
  · exact absurd hxX (Set.disjoint_left.mp h1 hx)

/-- A straight segment `{p + t v : t ∈ [0,1]}` in the continuous torus. -/
structure Seg (d n : ℕ) where
  /-- start point -/
  start : CTorus d n
  /-- displacement (in cube units) -/
  vec : Fin d → ℝ

namespace Seg

/-- The points of the segment. -/
def carrier (s : Seg d n) : Set (CTorus d n) :=
  {q | ∃ t ∈ Set.Icc (0 : ℝ) 1, ∀ i, q i = s.start i + ((t * s.vec i : ℝ) : AddCircle (n : ℝ))}

/-- The Euclidean length of a segment, in cube units. -/
noncomputable def length (s : Seg d n) : ℝ := Real.sqrt (∑ i, (s.vec i) ^ 2)

end Seg

/-- An admissible curve for `d_k(X mod Ω^c)`: a finite family of segments whose union is connected,
lies in `⋃_{x∈X} □_x` and meets every block `Bl(c)` with `Bl(c) ∩ X ∩ Ω ≠ ∅`. -/
def IsAdmissibleCurve [NeZero n] (L : ℕ) (Ω : Set (Torus d n)) (X : Finset (Torus d n))
    (Γ : Finset (Seg d n)) : Prop :=
  IsConnected (⋃ s ∈ Γ, s.carrier) ∧
  (⋃ s ∈ Γ, s.carrier) ⊆ ⋃ x ∈ X, cube x ∧
  ∀ c : Torus d n, (lblock L c ∩ (X : Set (Torus d n)) ∩ Ω).Nonempty →
    ∃ y ∈ lblock L c, ∃ q ∈ ⋃ s ∈ Γ, s.carrier, q ∈ cube y

/-- `d_k(X mod Ω^c)`: the infimum of the total lengths of admissible curves, in `[0, ∞]`
(`⊤` if there is none). -/
noncomputable def treeLengthMod [NeZero n] (L : ℕ) (Ω : Set (Torus d n))
    (X : Finset (Torus d n)) : ENNReal :=
  ⨅ (Γ : Finset (Seg d n)) (_ : IsAdmissibleCurve L Ω X Γ), ENNReal.ofReal (∑ s ∈ Γ, s.length)

end Balaban.LargeField
