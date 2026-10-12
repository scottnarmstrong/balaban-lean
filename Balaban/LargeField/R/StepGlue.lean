module

public import Balaban.LargeField.Region.Locality
public import Balaban.LargeField.R.HullUnion
import Mathlib.Tactic.Linarith

/-!
# Gluing local steps (the step-level core of Lemma III.10.2)

A `PreStep` is the data `(Z, P, Q, R, S)` of a step of the region calculus without the constraints
(R4)-(R6).  Its derived sets `Ω', Ω, Ω'', Z^{(0)}` are the set functions of Definition I.3.1.

For a finite family `st i` of steps, `PreStep.biUnion F` is the union of the data.  Assume that for
every point `x` the members that come within `ϱ = L + 2⌊R_k⌋ + 6` of `x` (their `Z^pre`) are
*witnessed*: they are the restrictions `big.restrict (V i)` of one step `big` to link-closed sets
`V i`.  Then (`glue_step`) the union of the data is again a step, whose `Z^{(0)}` is the union of the
`Z^{(0)}`'s of the members, and, if the `Z^pre` of the members are pairwise `ω`-separated, whose
`Z^pre` is the union of theirs, and whose restriction to the `Z^pre` of a member is that member.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open Balaban

/-- The data `(Z, P, Q, R, S)` of a step of the region calculus (Definition I.3.1), without the
constraints (R4)-(R6). -/
@[ext]
structure PreStep (d L n0 n1 : ℕ) (Rprev Rk : ℝ) where
  Z : Set (Torus d n0)
  P : Set (Torus d n1)
  Q : Set (Torus d n1)
  R : Set (Torus d n1)
  S : Set (Torus d n1)

namespace PreStep

variable {d L n0 n1 : ℕ} {Rprev Rk : ℝ} (p : PreStep d L n0 n1 Rprev Rk)

/-- `U'`. -/
abbrev Uprime : Set (Torus d n1) := Region.Uprime L n1 ⌊Rprev⌋₊ p.Z
/-- `Ω'`. -/
abbrev OmegaPrime : Set (Torus d n1) := Region.OmegaPrime L ⌊Rk⌋₊ p.Uprime
/-- `Ω`. -/
abbrev Omega : Set (Torus d n1) := Region.Omega L p.P p.OmegaPrime
/-- `Ω''`. -/
abbrev OmegaDD : Set (Torus d n1) := Region.OmegaDD L (Region.FDD ⌊Rk⌋₊ p.Q p.R) p.Omega
/-- `F^Z`. -/
abbrev FZ : Set (Torus d n1) := Region.FZ p.OmegaDD p.S
/-- `Z^{(0)}`. -/
abbrev Z0 : Set (Torus d n1) := Region.Z0 L ⌊2 * Rk⌋₊ p.FZ

/-- The data of `p` are contained in those of `q`. -/
def Le (p q : PreStep d L n0 n1 Rprev Rk) : Prop :=
  p.Z ⊆ q.Z ∧ p.P ⊆ q.P ∧ p.Q ⊆ q.Q ∧ p.R ⊆ q.R ∧ p.S ⊆ q.S

variable {p} {q : PreStep d L n0 n1 Rprev Rk}

theorem Le.refl (p : PreStep d L n0 n1 Rprev Rk) : Le p p :=
  ⟨subset_rfl, subset_rfl, subset_rfl, subset_rfl, subset_rfl⟩

theorem Le.trans {p q r : PreStep d L n0 n1 Rprev Rk} (h1 : Le p q) (h2 : Le q r) : Le p r :=
  ⟨h1.1.trans h2.1, h1.2.1.trans h2.2.1, h1.2.2.1.trans h2.2.2.1, h1.2.2.2.1.trans h2.2.2.2.1,
    h1.2.2.2.2.trans h2.2.2.2.2⟩

theorem Le.Uprime (h : Le p q) : p.Uprime ⊆ q.Uprime := Region.Uprime_mono h.1

theorem Le.OmegaPrime (h : Le p q) : q.OmegaPrime ⊆ p.OmegaPrime :=
  Region.OmegaPrime_anti h.Uprime

theorem Le.Omega (h : Le p q) : q.Omega ⊆ p.Omega :=
  Region.Omega_anti_mono h.2.1 h.OmegaPrime

theorem Le.OmegaDD (h : Le p q) : q.OmegaDD ⊆ p.OmegaDD :=
  Region.OmegaDD_anti_mono (Region.FDD_mono h.2.2.1 h.2.2.2.1) h.Omega

theorem Le.Z0 (h : Le p q) : p.Z0 ⊆ q.Z0 :=
  Region.Z0_mono (Region.FZ_anti_mono h.OmegaDD h.2.2.2.2)

/-- The union of the data of a finite family. -/
def biUnion {ι : Type*} (F : Finset ι) (p : ι → PreStep d L n0 n1 Rprev Rk) :
    PreStep d L n0 n1 Rprev Rk where
  Z := ⋃ i ∈ F, (p i).Z
  P := ⋃ i ∈ F, (p i).P
  Q := ⋃ i ∈ F, (p i).Q
  R := ⋃ i ∈ F, (p i).R
  S := ⋃ i ∈ F, (p i).S

theorem le_biUnion {ι : Type*} {F : Finset ι} {p : ι → PreStep d L n0 n1 Rprev Rk} {i : ι}
    (hi : i ∈ F) : Le (p i) (biUnion F p) :=
  ⟨fun _ hx => Set.mem_biUnion hi hx, fun _ hx => Set.mem_biUnion hi hx,
    fun _ hx => Set.mem_biUnion hi hx, fun _ hx => Set.mem_biUnion hi hx,
    fun _ hx => Set.mem_biUnion hi hx⟩

theorem biUnion_le {ι : Type*} {F G : Finset ι} (h : F ⊆ G)
    (p : ι → PreStep d L n0 n1 Rprev Rk) : Le (biUnion F p) (biUnion G p) :=
  ⟨Set.biUnion_subset_biUnion_left h, Set.biUnion_subset_biUnion_left h,
    Set.biUnion_subset_biUnion_left h, Set.biUnion_subset_biUnion_left h,
    Set.biUnion_subset_biUnion_left h⟩

theorem biUnion_congr {ι : Type*} {F : Finset ι} {p p' : ι → PreStep d L n0 n1 Rprev Rk}
    (h : ∀ i ∈ F, p i = p' i) : biUnion F p = biUnion F p' := by
  have e : ∀ {α : Type _} (f g : ι → Set α), (∀ i ∈ F, f i = g i) →
      (⋃ i ∈ F, f i) = ⋃ i ∈ F, g i := fun f g hfg => Set.iUnion₂_congr hfg
  refine PreStep.ext ?_ ?_ ?_ ?_ ?_
  · exact e _ _ fun i hi => by rw [h i hi]
  · exact e _ _ fun i hi => by rw [h i hi]
  · exact e _ _ fun i hi => by rw [h i hi]
  · exact e _ _ fun i hi => by rw [h i hi]
  · exact e _ _ fun i hi => by rw [h i hi]

theorem mem_Uprime_biUnion {ι : Type*} {F : Finset ι} {p : ι → PreStep d L n0 n1 Rprev Rk}
    {u : Torus d n1} :
    u ∈ (biUnion F p).Uprime ↔ ∃ i ∈ F, u ∈ (p i).Uprime := by
  constructor
  · rintro ⟨v, hv, rfl⟩
    obtain ⟨z, hz, hvz⟩ := mem_nbhd.mp hv
    simp only [biUnion, Set.mem_iUnion, exists_prop] at hz
    obtain ⟨i, hi, hzi⟩ := hz
    exact ⟨i, hi, _, mem_nbhd.mpr ⟨z, hzi, hvz⟩, rfl⟩
  · rintro ⟨i, hi, hu⟩
    exact (le_biUnion hi).Uprime hu

end PreStep

namespace RegionStep

variable {d L n0 n1 : ℕ} {Rprev Rk : ℝ} (st : RegionStep d L n0 n1 Rprev Rk)

/-- The data of a step. -/
def toPre : PreStep d L n0 n1 Rprev Rk := ⟨st.Z, st.P, st.Q, st.R, st.S⟩

theorem toPre_Uprime : st.toPre.Uprime = st.Uprime := rfl
theorem toPre_OmegaPrime : st.toPre.OmegaPrime = st.OmegaPrime := rfl
theorem toPre_Omega : st.toPre.Omega = st.Omega := rfl
theorem toPre_OmegaDD : st.toPre.OmegaDD = st.OmegaDD := rfl
theorem toPre_Z0 : st.toPre.Z0 = st.Z0 := rfl

end RegionStep

/-! ### Locality of the set functions for the data `p ≤ q` -/

section Locality

variable {d L n0 n1 : ℕ} [NeZero n1] {Rprev Rk : ℝ}

theorem PreStep.not_mem_OmegaPrime_of_local {p q : PreStep d L n0 n1 Rprev Rk} (hL : 1 ≤ L)
    {x : Torus d n1}
    (hloc : ∀ u ∈ q.Uprime, supDist x u ≤ L + ⌊Rk⌋₊ + 3 → u ∈ p.Uprime)
    (hx : x ∉ q.OmegaPrime) : x ∉ p.OmegaPrime := by
  refine not_mem_opening_local (fun f hf hd => ?_) hx
  obtain ⟨u, hu, hfu⟩ := mem_nbhd.mp hf
  have := supDist_triangle x f u
  exact mem_nbhd.mpr ⟨u, hloc u hu (by omega), hfu⟩

theorem PreStep.not_mem_Omega_of_local {p q : PreStep d L n0 n1 Rprev Rk} (hL : 1 ≤ L)
    {x : Torus d n1}
    (hΘ : ∀ y, supDist x y ≤ L - 1 → y ∉ q.OmegaPrime → y ∉ p.OmegaPrime)
    (hP : ∀ u ∈ q.P, supDist x u ≤ L + 2 → u ∈ p.P)
    (hx : x ∉ q.Omega) : x ∉ p.Omega := by
  refine not_mem_openingIn_local hΘ (fun g hg hd => ?_) hx
  obtain ⟨u, hu, hgu⟩ := mem_nbhd.mp hg
  have := supDist_triangle x g u
  exact mem_nbhd.mpr ⟨u, hP u hu (by omega), hgu⟩

theorem PreStep.not_mem_OmegaDD_of_local {p q : PreStep d L n0 n1 Rprev Rk} (hL : 1 ≤ L)
    {x : Torus d n1}
    (hΘ : ∀ y, supDist x y ≤ L - 1 → y ∉ q.Omega → y ∉ p.Omega)
    (hQ : ∀ u ∈ q.Q, supDist x u ≤ L + ⌊Rk⌋₊ + 1 → u ∈ p.Q)
    (hR : ∀ u ∈ q.R, supDist x u ≤ L + 2 * ⌊Rk⌋₊ + 3 → u ∈ p.R)
    (hx : x ∉ q.OmegaDD) : x ∉ p.OmegaDD := by
  refine not_mem_openingIn_local hΘ (fun g hg hd => ?_) hx
  rcases hg with hg | hg
  · obtain ⟨u, hu, hgu⟩ := mem_nbhd.mp hg
    have := supDist_triangle x g u
    exact Or.inl (mem_nbhd.mpr ⟨u, hQ u hu (by omega), hgu⟩)
  · obtain ⟨u, hu, hgu⟩ := mem_nbhd.mp hg
    have := supDist_triangle x g u
    exact Or.inr (mem_nbhd.mpr ⟨u, hR u hu (by omega), hgu⟩)

theorem PreStep.mem_Z0_of_local {p q : PreStep d L n0 n1 Rprev Rk} (hL : 1 ≤ L)
    {x : Torus d n1}
    (hΩ : ∀ g, supDist x g ≤ L + ⌊2 * Rk⌋₊ + 5 → g ∉ q.OmegaDD → g ∉ p.OmegaDD)
    (hS : ∀ u ∈ q.S, supDist x u ≤ L + ⌊2 * Rk⌋₊ + 3 → u ∈ p.S)
    (hx : x ∈ q.Z0) : x ∈ p.Z0 := by
  refine not_mem_opening_local (fun f hf hd => ?_) hx
  rcases hf with hf | hf
  · obtain ⟨g, hg, hfg⟩ := mem_nbhd.mp hf
    have := supDist_triangle x f g
    exact Or.inl (mem_nbhd.mpr ⟨g, hΩ g (by omega) hg, hfg⟩)
  · obtain ⟨u, hu, hfu⟩ := mem_nbhd.mp hf
    have := supDist_triangle x f u
    exact Or.inr (mem_nbhd.mpr ⟨u, hS u hu (by omega), hfu⟩)

end Locality

end Balaban.LargeField
