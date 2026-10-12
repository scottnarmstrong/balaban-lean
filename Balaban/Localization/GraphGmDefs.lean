/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.GraphGmWalk
public import Balaban.Fluctuation.SizeModCore
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The witness-carrying source index of P6 boundary localization (GRAPH-GM-2 §5)

The replacements, as NEW definitions, for the landed `incGraph` / `seedClosure` of
`Decoupled2Fp{Geometry,Count}.lean` as the P6 counting graph and output index.  The landed
definitions stay valid for the locality dichotomy.

* `locAdj`, `witnessClosure`, `Effective` (5.1): the physical face-adjacency graph on the source
  cubes `B` and the retained derivative cubes `𝒞`, the cubes reachable from the source base, and
  the effectiveness condition `𝒞 ⊂ witnessClosure`.  Vertices are the cubes themselves; the
  face components of `B` of the note (`SourceComp(B)`) are the classes of cubes of `B` mutually
  reachable inside `B`, and reachability from `B` is the same as reachability from its
  components.  No hole is contracted: adjacency is the physical `(d-1)`-face contact `ZFaceAdj`.
* `rawY1` (5.1) (without the proper lower-dimensional walls of P3 (4.42), which are not counted).
* `holeCl`, `outputY` (2.1): the modular output
  `Y(𝒞) = holeCl_Ω (X ∪ B ∪ ⋃_{P ∈ 𝒞} ⋃ D(P))`, with the hole closure adjoining each entire
  component of `Ω^c` met by the argument.
* `zTorus`, `ZCell.sites`: the lift of integer cells to the torus.
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Fluctuation Finset

section Lift

variable {d L N₁ m₁ K : ℕ}

/-- The torus site with integer coordinates `x`. -/
def zTorus (L N₁ m₁ K : ℕ) (x : Fin d → ℤ) : CTorus d L N₁ m₁ K :=
  fun μ => ((x μ : ℤ) : ZMod ((N₁ * L ^ m₁) * L ^ K))

/-- The sites of an integer cell, as a subset of the torus. -/
def ZCell.sites (L N₁ m₁ K : ℕ) (c : ZCell d) : Set (CTorus d L N₁ m₁ K) :=
  zTorus L N₁ m₁ K '' c.pts

theorem zTorus_add (x y : Fin d → ℤ) :
    zTorus L N₁ m₁ K (x + y) = zTorus L N₁ m₁ K x + zTorus L N₁ m₁ K y := by
  funext μ; simp [zTorus]

theorem zTorus_single (μ : Fin d) :
    zTorus L N₁ m₁ K (Pi.single μ (1 : ℤ)) = Pi.single μ 1 := by
  funext ν
  by_cases h : ν = μ
  · subst h; simp [zTorus]
  · simp [zTorus, h]

theorem zTorus_natT (w : Fin d → ℕ) :
    zTorus L N₁ m₁ K (fun μ => ((w μ : ℕ) : ℤ)) = natT w := by
  funext μ; simp [zTorus]

/-- Integer neighbours are torus neighbours. -/
theorem nbr_zTorus {a b : Fin d → ℤ} (h : ZStep a b) :
    Nbr (zTorus L N₁ m₁ K a) (zTorus L N₁ m₁ K b) := by
  obtain ⟨μ, h | h⟩ := h
  · exact ⟨μ, Or.inl (by rw [h, zTorus_add, zTorus_single])⟩
  · exact ⟨μ, Or.inr (by rw [h, zTorus_add, zTorus_single])⟩

/-- The sites of the cell `base + [0, side)^d` are the torus box at `zTorus base`. -/
theorem ZCell.sites_eq_box (c : ZCell d) :
    c.sites L N₁ m₁ K = box (zTorus L N₁ m₁ K c.base) c.side := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨fun μ => (y μ - c.base μ).toNat, fun μ => ?_, ?_⟩
    · show (y μ - c.base μ).toNat < c.side
      have := hy μ; omega
    · funext μ
      have h1 := (hy μ).1
      have e : y μ = c.base μ + (((y μ - c.base μ).toNat : ℕ) : ℤ) := by omega
      simp only [zTorus, Pi.add_apply, natT_apply]
      rw [← Int.cast_natCast, ← Int.cast_add]
      exact congrArg _ e
  · rintro ⟨w, hw, rfl⟩
    refine ⟨c.base + fun μ => ((w μ : ℕ) : ℤ), fun μ => ?_, ?_⟩
    · have := hw μ
      simp only [Pi.add_apply]
      omega
    · rw [zTorus_add, zTorus_natT]

theorem ZCell.rep_mem_sites (c : ZCell d) (h : 0 < c.side) :
    zTorus L N₁ m₁ K c.rep ∈ c.sites L N₁ m₁ K := ⟨c.rep, c.rep_mem h, rfl⟩

/-- Alignment of the torus image of a base divisible by the side, for a side dividing the
torus side. -/
theorem aligned_zTorus [NeZero N₁] [NeZero L] {a : ℕ} (ha : a ∣ (N₁ * L ^ m₁) * L ^ K)
    {b : Fin d → ℤ} (hb : ∀ μ, (a : ℤ) ∣ b μ) : Aligned a (zTorus L N₁ m₁ K b) := by
  have : NeZero ((N₁ * L ^ m₁) * L ^ K) := ⟨by
    have := NeZero.pos N₁; have := NeZero.pos L; positivity⟩
  intro μ
  have han : (a : ℤ) ∣ (((N₁ * L ^ m₁) * L ^ K : ℕ) : ℤ) := by exact_mod_cast ha
  have hv : (((zTorus L N₁ m₁ K b) μ).val : ℤ) = b μ % (((N₁ * L ^ m₁) * L ^ K : ℕ) : ℤ) :=
    ZMod.val_intCast (b μ)
  have h2 : (a : ℤ) ∣ b μ % (((N₁ * L ^ m₁) * L ^ K : ℕ) : ℤ) := by
    have e : b μ % (((N₁ * L ^ m₁) * L ^ K : ℕ) : ℤ) =
        b μ - (((N₁ * L ^ m₁) * L ^ K : ℕ) : ℤ) * (b μ / (((N₁ * L ^ m₁) * L ^ K : ℕ) : ℤ)) := by
      have := Int.mul_ediv_add_emod (b μ) (((N₁ * L ^ m₁) * L ^ K : ℕ) : ℤ); linarith
    rw [e]
    exact dvd_sub (hb μ) (dvd_mul_of_dvd_left han _)
  have h3 : (a : ℤ) ∣ (((zTorus L N₁ m₁ K b) μ).val : ℤ) := by rw [hv]; exact h2
  have h4 : a ∣ ((zTorus L N₁ m₁ K b) μ).val := by exact_mod_cast h3
  exact Nat.mod_eq_zero_of_dvd h4

/-- A face-adjacent pair of cells has a pair of neighbouring sites across the common face. -/
theorem ZFaceAdj.exists_step {c c' : ZCell d} (h : ZFaceAdj c c') (hs : 0 < c.side)
    (hs' : 0 < c'.side) : ∃ u ∈ c.pts, ∃ v ∈ c'.pts, ZStep u v := by
  classical
  obtain ⟨μ, hn, ht⟩ := h
  rcases hn with hn | hn
  · -- `c'` lies above `c` in direction `μ`
    refine ⟨fun ν => if ν = μ then c.base μ + c.side - 1 else max (c.base ν) (c'.base ν),
      ?_, fun ν => if ν = μ then c.base μ + c.side else max (c.base ν) (c'.base ν), ?_, μ, Or.inl ?_⟩
    · intro ν
      by_cases hν : ν = μ
      · subst hν; simp only [↓reduceIte]; omega
      · have := ht ν hν
        simp only [hν, ↓reduceIte]; omega
    · intro ν
      by_cases hν : ν = μ
      · subst hν; simp only [↓reduceIte]; omega
      · have := ht ν hν
        simp only [hν, ↓reduceIte]; omega
    · funext ν
      by_cases hν : ν = μ
      · subst hν; simp
      · simp [hν]
  · refine ⟨fun ν => if ν = μ then c.base μ else max (c.base ν) (c'.base ν),
      ?_, fun ν => if ν = μ then c.base μ - 1 else max (c.base ν) (c'.base ν), ?_, μ, Or.inr ?_⟩
    · intro ν
      by_cases hν : ν = μ
      · subst hν; simp only [↓reduceIte]; omega
      · have := ht ν hν
        simp only [hν, ↓reduceIte]; omega
    · intro ν
      by_cases hν : ν = μ
      · subst hν; simp only [↓reduceIte]; omega
      · have := ht ν hν
        simp only [hν, ↓reduceIte]; omega
    · funext ν
      by_cases hν : ν = μ
      · subst hν; simp
      · simp [hν]

end Lift

section Index

variable {d L N₁ m₁ K : ℕ}

/-- **The physical localization graph** (5.1): `u` and `v` are vertices (cubes of the source base
`B` or retained derivative cubes `𝒞`) whose cubes share a `(d-1)`-face. -/
def locAdj (B C : Finset (ZCell d)) (u v : ZCell d) : Prop :=
  u ∈ B ∪ C ∧ v ∈ B ∪ C ∧ ZFaceAdj u v

/-- **`witnessClosure(B, 𝒞)`** (5.1): the cubes reachable in `locAdj` from the source base. -/
def witnessClosure (B C : Finset (ZCell d)) : Set (ZCell d) :=
  {v | ∃ b ∈ B, Relation.ReflTransGen (locAdj B C) b v}

/-- **`effective(B, 𝒞)`** (5.1): every retained derivative cube is reached from the source base
through face-adjacent cubes. -/
def Effective (B C : Finset (ZCell d)) : Prop :=
  ∀ P ∈ C, P ∈ witnessClosure B C

open Classical in
/-- **`rawY1(B, 𝒞)`** (5.1), without the proper lower-dimensional walls: the source base and the
retained derivative cubes that lie in the witness closure. -/
def rawY1 (L N₁ m₁ K : ℕ) (B C : Finset (ZCell d)) : Set (CTorus d L N₁ m₁ K) :=
  (⋃ b ∈ B, b.sites L N₁ m₁ K) ∪ ⋃ P ∈ C.filter (· ∈ witnessClosure B C), P.sites L N₁ m₁ K

/-- **Hole closure** `holeCl_Ω(S)`: `S` together with each entire component of `Ω^c` met by `S`. -/
def holeCl (Ω S : Set (CTorus d L N₁ m₁ K)) : Set (CTorus d L N₁ m₁ K) :=
  S ∪ {y | ∃ z ∈ S, z ∈ Ωᶜ ∧ y ∈ OmegaComp Ω z}

/-- **The modular output `Y(𝒞)`** (2.1):
`holeCl_Ω (X ∪ B ∪ ⋃_{P ∈ 𝒞} ⋃ D(P))`, where `D P` are the active aligned `M`-cells generated by
P3's completion of the derivative `P`. -/
def outputY (L N₁ m₁ K : ℕ) (Ω X : Set (CTorus d L N₁ m₁ K)) (B C : Finset (ZCell d))
    (D : ZCell d → Finset (ZCell d)) : Set (CTorus d L N₁ m₁ K) :=
  holeCl Ω (X ∪ (⋃ b ∈ B, b.sites L N₁ m₁ K) ∪
    ⋃ P ∈ C, ⋃ g ∈ D P, g.sites L N₁ m₁ K)

theorem subset_holeCl (Ω S : Set (CTorus d L N₁ m₁ K)) : S ⊆ holeCl Ω S := Set.subset_union_left

/-- Hole closure adds no site of `Ω`. -/
theorem holeCl_inter (Ω S : Set (CTorus d L N₁ m₁ K)) : holeCl Ω S ∩ Ω ⊆ S := by
  rintro y ⟨hy | ⟨z, hz, hzΩ, hy⟩, hyΩ⟩
  · exact hy
  · exact absurd hyΩ hy.1

theorem X_subset_outputY (Ω X : Set (CTorus d L N₁ m₁ K)) (B C : Finset (ZCell d))
    (D : ZCell d → Finset (ZCell d)) : X ⊆ outputY L N₁ m₁ K Ω X B C D :=
  fun _ hx => subset_holeCl _ _ (Or.inl (Or.inl hx))

theorem source_subset_outputY (Ω X : Set (CTorus d L N₁ m₁ K)) (B C : Finset (ZCell d))
    (D : ZCell d → Finset (ZCell d)) {b : ZCell d} (hb : b ∈ B) :
    b.sites L N₁ m₁ K ⊆ outputY L N₁ m₁ K Ω X B C D :=
  fun _ hx => subset_holeCl _ _ (Or.inl (Or.inr (Set.mem_iUnion₂.2 ⟨b, hb, hx⟩)))

theorem cell_subset_outputY (Ω X : Set (CTorus d L N₁ m₁ K)) (B C : Finset (ZCell d))
    (D : ZCell d → Finset (ZCell d)) {P g : ZCell d} (hP : P ∈ C) (hg : g ∈ D P) :
    g.sites L N₁ m₁ K ⊆ outputY L N₁ m₁ K Ω X B C D :=
  fun _ hx => subset_holeCl _ _ (Or.inr (Set.mem_iUnion₂.2 ⟨P, hP,
    Set.mem_iUnion₂.2 ⟨g, hg, hx⟩⟩))

/-- The active part of the output: `Y(𝒞) ∩ Ω ⊆ (X ∪ B ∪ ⋃ D(P)) ∩ Ω`. -/
theorem outputY_inter (Ω X : Set (CTorus d L N₁ m₁ K)) (B C : Finset (ZCell d))
    (D : ZCell d → Finset (ZCell d)) :
    outputY L N₁ m₁ K Ω X B C D ∩ Ω ⊆ X ∪ (⋃ b ∈ B, b.sites L N₁ m₁ K) ∪
      ⋃ P ∈ C, ⋃ g ∈ D P, g.sites L N₁ m₁ K :=
  holeCl_inter _ _

theorem Effective.empty (B : Finset (ZCell d)) : Effective B (∅ : Finset (ZCell d)) :=
  fun _ hP => absurd hP (Finset.notMem_empty _)

end Index

end Balaban.Localization
