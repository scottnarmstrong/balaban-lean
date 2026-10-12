module

public import Balaban.LargeField.Region.Seeds
public import Balaban.LargeField.Region.Hull
public import Balaban.LargeField.History.JoinFamily

/-!
# Indexed seeds of a step (Part I, Definition I.4.7, items 1-2)

The seeds of the step `k → k+1` are indexed by `SeedIdx = (component of Z_k) ⊕ (cube of 𝕋_{k+1})`:
`sset (inl Y) = Y^↑` and `sset (inr q) = {q}`.  For a component `C` of any `X ⊇ Z^{(0)}`,
`seedsIn C` is the finite set of indices whose seed lies in `C`.

* every component of a hull round `X_t` contains a seed (`seedsIn_card_pos`);
* the seeds of a component `C'` of `H_b(X)` are the disjoint union of the seeds of the components
  of `X` in `C'` (`seedsIn_hullRound`).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open Balaban

/-- Index of a seed: an old seed `Z^↑` (index: the component `Z`) or a new seed `{q}`. -/
abbrev SeedIdx (d n0 n1 : ℕ) : Type := Finset (Torus d n0) ⊕ Torus d n1

/-- The seed with a given index. -/
def sset {d n0 n1 : ℕ} (L : ℕ) : SeedIdx d n0 n1 → Set (Torus d n1)
  | .inl Y => blockMap L n1 '' (Y : Set (Torus d n0))
  | .inr q => {q}

/-- The radius weight `s_σ` of an index: `4` (old) or `5` (new). -/
def seedWt {d n0 n1 : ℕ} : SeedIdx d n0 n1 → ℕ
  | .inl _ => 4
  | .inr _ => 5

/-- Numerical facts about a step used by the spine construction. -/
structure StepGeom (L n0 n1 ωk ω r : ℕ) (Rprev Rk : ℝ) : Prop where
  hn : n0 = L * n1
  rad : StepRadii L ω r Rprev Rk
  hlt : (ωk + L - 2) / L < ω
  hLωk : L ≤ ωk
  hω2 : 2 ≤ ω

namespace RegionStep

variable {d L n0 n1 : ℕ} [NeZero n0] [NeZero n1] {Rprev Rk : ℝ}
  (st : RegionStep d L n0 n1 Rprev Rk)

open Classical in
/-- The finite set of seed indices. -/
noncomputable def idx (ωk : ℕ) : Finset (SeedIdx d n0 n1) :=
  (comps ωk (finOf st.Z)).image Sum.inl ∪ (finOf st.newCubes).image Sum.inr

theorem inl_mem_idx {ωk : ℕ} {Y : Finset (Torus d n0)} :
    Sum.inl Y ∈ st.idx ωk ↔ Y ∈ comps ωk (finOf st.Z) := by
  classical
  simp [idx]

theorem inr_mem_idx {ωk : ℕ} {q : Torus d n1} : Sum.inr q ∈ st.idx ωk ↔ q ∈ st.newCubes := by
  classical
  simp [idx]

theorem sset_mem_seeds {ωk : ℕ} {a : SeedIdx d n0 n1} (ha : a ∈ st.idx ωk) :
    sset (n0 := n0) L a ∈ st.seeds ωk := by
  rcases a with Y | q
  · exact Or.inl ⟨Y, (st.inl_mem_idx).mp ha, rfl⟩
  · exact Or.inr ⟨q, (st.inr_mem_idx).mp ha, rfl⟩

theorem sset_nonempty {ωk : ℕ} {a : SeedIdx d n0 n1} (ha : a ∈ st.idx ωk) :
    (sset (n0 := n0) L a).Nonempty := by
  rcases a with Y | q
  · obtain ⟨y, hy⟩ := comp_nonempty ((st.inl_mem_idx).mp ha)
    exact ⟨_, y, hy, rfl⟩
  · exact ⟨q, rfl⟩

theorem sset_subset_Z0 {ωk : ℕ} {a : SeedIdx d n0 n1} (ha : a ∈ st.idx ωk) :
    sset (n0 := n0) L a ⊆ st.Z0 :=
  st.seed_subset_Z0 (st.sset_mem_seeds ha)

theorem sset_disjoint {ωk : ℕ} (hn : n0 = L * n1) (hL : 0 < L) (hωk : L ≤ ωk)
    {a b : SeedIdx d n0 n1} (ha : a ∈ st.idx ωk) (hb : b ∈ st.idx ωk) (hab : a ≠ b) :
    Disjoint (sset (n0 := n0) L a) (sset (n0 := n0) L b) := by
  have hnew : ∀ q ∈ st.newCubes, ∀ τ ∈ st.oldSeeds ωk, q ∉ τ := fun q hq τ hτ hqτ =>
    (Set.disjoint_left.mp st.newCubes_disjoint_Uprime) hq (st.oldSeed_subset_Uprime hτ hqτ)
  rcases a with Y | q <;> rcases b with Y' | q'
  · have hY := (st.inl_mem_idx).mp ha
    have hY' := (st.inl_mem_idx).mp hb
    have hYY : Y ≠ Y' := fun h => hab (by rw [h])
    rw [Set.disjoint_left]
    rintro _ ⟨x, hx, rfl⟩ ⟨y, hy, hxy⟩
    have h1 := comps_sep hY hY' hYY hx hy
    have h2 := supDist_le_of_blockMap_eq hn hxy.symm
    omega
  · rw [sset, sset, Set.disjoint_singleton_right]
    exact hnew q' ((st.inr_mem_idx).mp hb) _ ⟨Y, (st.inl_mem_idx).mp ha, rfl⟩
  · rw [sset, sset, Set.disjoint_singleton_left]
    exact hnew q ((st.inr_mem_idx).mp ha) _ ⟨Y', (st.inl_mem_idx).mp hb, rfl⟩
  · rw [sset, sset, Set.disjoint_singleton]
    intro h; exact hab (by rw [h])

open Classical in
/-- The indices whose seed lies in `C`. -/
noncomputable def seedsIn (ωk : ℕ) (C : Finset (Torus d n1)) : Finset (SeedIdx d n0 n1) :=
  (st.idx ωk).filter fun a => sset (n0 := n0) L a ⊆ (C : Set (Torus d n1))

theorem mem_seedsIn {ωk : ℕ} {C : Finset (Torus d n1)} {a : SeedIdx d n0 n1} :
    a ∈ st.seedsIn ωk C ↔ a ∈ st.idx ωk ∧ sset (n0 := n0) L a ⊆ (C : Set (Torus d n1)) := by
  classical
  simp [seedsIn]

variable {ωk ω r : ℕ}

theorem sset_in_Z0comp (hg : StepGeom L n0 n1 ωk ω r Rprev Rk) {a : SeedIdx d n0 n1}
    (ha : a ∈ st.idx ωk) :
    ∃ C ∈ comps ω (finOf st.Z0), sset (n0 := n0) L a ⊆ (C : Set (Torus d n1)) :=
  st.seed_in_comp hg.hn hg.hlt (st.sset_mem_seeds ha)

theorem attr_seed (hg : StepGeom L n0 n1 ωk ω r Rprev Rk) {x : Torus d n1} (hx : x ∈ st.Z0) :
    ∃ a ∈ st.idx ωk, ∃ y ∈ sset (n0 := n0) L a, supDist x y ≤ seedWt a * r ∧
      Linked ω st.Z0 x y := by
  rcases st.attribution (ωk := ωk) hg.rad hg.hn hx with ⟨Y, hY, y, hy, hd, hl⟩ | ⟨q, hq, hd, hl⟩
  · exact ⟨Sum.inl Y, (st.inl_mem_idx).mpr hY, y, hy, hd, hl⟩
  · exact ⟨Sum.inr q, (st.inr_mem_idx).mpr hq, q, rfl, hd, hl⟩

theorem sset_subset_of_linked (hg : StepGeom L n0 n1 ωk ω r Rprev Rk) {C0 : Finset (Torus d n1)}
    (hC0 : C0 ∈ comps ω (finOf st.Z0)) {x : Torus d n1} (hx : x ∈ C0) {a : SeedIdx d n0 n1}
    (ha : a ∈ st.idx ωk) {y : Torus d n1} (hy : y ∈ sset (n0 := n0) L a)
    (hl : Linked ω st.Z0 x y) : sset (n0 := n0) L a ⊆ (C0 : Set (Torus d n1)) := by
  have hyC0 : y ∈ C0 := mem_comp_of_linked hC0 hx (mem_finOf.mpr (st.sset_subset_Z0 ha hy))
    (by rw [coe_finOf]; exact hl)
  obtain ⟨C1, hC1, hsub⟩ := st.sset_in_Z0comp hg ha
  have : C1 = C0 := comp_eq_of_mem hC1 hC0 (hsub hy) hyC0
  exact this ▸ hsub

theorem sset_in_comp_of (hg : StepGeom L n0 n1 ωk ω r Rprev Rk) {X : Set (Torus d n1)}
    (hX : st.Z0 ⊆ X) {a : SeedIdx d n0 n1} (ha : a ∈ st.idx ωk) :
    ∃ C ∈ comps ω (finOf X), sset (n0 := n0) L a ⊆ (C : Set (Torus d n1)) := by
  obtain ⟨C0, hC0, hsub⟩ := st.sset_in_Z0comp hg ha
  obtain ⟨C, hC, hCC⟩ := comp_mono (finOf_subset_finOf hX) hC0
  exact ⟨C, hC, hsub.trans fun y hy => hCC hy⟩

theorem seedsIn_card_pos (hg : StepGeom L n0 n1 ωk ω r Rprev Rk) {C : Finset (Torus d n1)}
    (hcont : ∃ C0 ∈ comps ω (finOf st.Z0), C0 ⊆ C) : 1 ≤ (st.seedsIn ωk C).card := by
  obtain ⟨C0, hC0, hC0C⟩ := hcont
  obtain ⟨x, hx⟩ := comp_nonempty hC0
  obtain ⟨a, ha, y, hy, -, hl⟩ := st.attr_seed hg (mem_finOf.mp (comp_subset hC0 hx))
  have hsub := st.sset_subset_of_linked hg hC0 hx ha hy hl
  exact Finset.card_pos.mpr ⟨a, st.mem_seedsIn.mpr ⟨ha, hsub.trans fun z hz => hC0C hz⟩⟩

/-- The seeds of a component of a superset are the disjoint union of the seeds of the components
of `X` it contains. -/
theorem seedsIn_biUnion (hg : StepGeom L n0 n1 ωk ω r Rprev Rk) {X Y : Set (Torus d n1)}
    (hX : st.Z0 ⊆ X) (hXY : X ⊆ Y) {C' : Finset (Torus d n1)} (hC' : C' ∈ comps ω (finOf Y)) :
    st.seedsIn ωk C' =
      ((comps ω (finOf X)).filter (fun C => C ⊆ C')).biUnion (st.seedsIn ωk) := by
  classical
  ext a
  simp only [Finset.mem_biUnion, Finset.mem_filter, mem_seedsIn]
  constructor
  · rintro ⟨ha, hsub⟩
    obtain ⟨C, hC, hsubC⟩ := st.sset_in_comp_of hg hX ha
    obtain ⟨y, hy⟩ := st.sset_nonempty ha
    obtain ⟨C'', hC'', hCC''⟩ := comp_mono (finOf_subset_finOf hXY) hC
    have : C'' = C' := comp_eq_of_mem hC'' hC' (hCC'' (hsubC hy)) (hsub hy)
    exact ⟨C, ⟨hC, fun z hz => this ▸ hCC'' hz⟩, ha, hsubC⟩
  · rintro ⟨C, ⟨hC, hCC'⟩, ha, hsub⟩
    exact ⟨ha, hsub.trans fun z hz => hCC' hz⟩

theorem seedsIn_disjoint {X : Set (Torus d n1)}
    {C C' : Finset (Torus d n1)} (hC : C ∈ comps ω (finOf X)) (hC' : C' ∈ comps ω (finOf X))
    (hne : C ≠ C') : Disjoint (st.seedsIn ωk C) (st.seedsIn ωk C') := by
  rw [Finset.disjoint_left]
  intro a ha ha'
  rw [mem_seedsIn] at ha ha'
  obtain ⟨y, hy⟩ := st.sset_nonempty ha.1
  exact hne (comp_eq_of_mem hC hC' (ha.2 hy) (ha'.2 hy))

end RegionStep

/-- Two points of a component are linked inside it. -/
theorem comp_linked_self {d n ω : ℕ} [NeZero n] {X : Set (Torus d n)} {C : Finset (Torus d n)}
    (hC : C ∈ comps ω (finOf X)) {x y : Torus d n} (hx : x ∈ C) (hy : y ∈ C) :
    Linked ω (C : Set (Torus d n)) x y := by
  have h := ((mem_comp_iff hC hx).mp hy).2
  rw [coe_finOf] at h
  have hsub : (C : Set (Torus d n)) ⊆ X := fun z hz => mem_finOf.mp (comp_subset hC hz)
  have := (linked_inter_comp (le_refl X) hC hx h).2
  rwa [Set.inter_eq_right.mpr hsub] at this

end Balaban.LargeField
