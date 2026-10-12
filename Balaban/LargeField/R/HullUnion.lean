module

public import Balaban.LargeField.Region.Hull

/-!
# Components and hull closures of separated unions

If the sets `X i`, `i ∈ F`, are pairwise at index distance `≥ ω`, then a chain in the union with
steps `< ω` never leaves one of them.  Hence the components of the union are the components of
the members, one hull round acts memberwise, and so does the hull closure when the closures of the
members are themselves separated.  These are the combinatorial facts behind Lemma III.10.2.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open Balaban

variable {d n : ℕ} [NeZero n] {ω b : ℕ} {ι : Type*} {F : Finset ι}

/-- The members `X i`, `i ∈ F`, are pairwise at index distance `≥ ω`. -/
def SepFam (ω : ℕ) (F : Finset ι) (X : ι → Set (Torus d n)) : Prop :=
  ∀ i ∈ F, ∀ j ∈ F, i ≠ j → ∀ x ∈ X i, ∀ y ∈ X j, ω ≤ supDist x y

theorem SepFam.mono {X Y : ι → Set (Torus d n)} (h : SepFam ω F Y) (hXY : ∀ i, X i ⊆ Y i) :
    SepFam ω F X :=
  fun i hi j hj hij x hx y hy => h i hi j hj hij x (hXY i hx) y (hXY j hy)

theorem linked_iUnion_sep {X : ι → Set (Torus d n)} (hs : SepFam ω F X) {i : ι} (hi : i ∈ F)
    {x y : Torus d n} (hx : x ∈ X i) (h : Linked ω (⋃ j ∈ F, X j) x y) :
    y ∈ X i ∧ Linked ω (X i) x y := by
  induction h with
  | refl => exact ⟨hx, Linked.refl _⟩
  | tail _ hbc ih =>
    obtain ⟨hb, hl⟩ := ih
    obtain ⟨-, hc, hbc⟩ := hbc
    simp only [Set.mem_iUnion, exists_prop] at hc
    obtain ⟨j, hj, hcj⟩ := hc
    have hji : j = i := by
      by_contra hne
      have := hs i hi j hj (Ne.symm hne) _ hb _ hcj
      omega
    subst hji
    exact ⟨hcj, hl.trans (Linked.single hb hcj hbc)⟩

theorem linkClass_iUnion_sep {X : ι → Set (Torus d n)} (hs : SepFam ω F X) {i : ι} (hi : i ∈ F)
    {x : Torus d n} (hx : x ∈ X i) :
    linkClass ω (finOf (⋃ j ∈ F, X j)) x = linkClass ω (finOf (X i)) x := by
  ext y
  rw [mem_linkClass, mem_linkClass, coe_finOf, coe_finOf, mem_finOf, mem_finOf]
  constructor
  · rintro ⟨-, h⟩
    exact linked_iUnion_sep hs hi hx h
  · rintro ⟨hy, h⟩
    exact ⟨Set.mem_biUnion hi hy, h.mono (Set.subset_biUnion_of_mem hi)⟩

theorem mem_comps_iUnion_sep {X : ι → Set (Torus d n)} (hs : SepFam ω F X)
    {Y : Finset (Torus d n)} :
    Y ∈ comps ω (finOf (⋃ j ∈ F, X j)) ↔ ∃ i ∈ F, Y ∈ comps ω (finOf (X i)) := by
  constructor
  · intro hY
    obtain ⟨x, hx, rfl⟩ := mem_comps_iff.mp hY
    have hx' := mem_finOf.mp hx
    simp only [Set.mem_iUnion, exists_prop] at hx'
    obtain ⟨i, hi, hxi⟩ := hx'
    refine ⟨i, hi, mem_comps_iff.mpr ⟨x, mem_finOf.mpr hxi, ?_⟩⟩
    exact linkClass_iUnion_sep hs hi hxi
  · rintro ⟨i, hi, hY⟩
    obtain ⟨x, hx, rfl⟩ := mem_comps_iff.mp hY
    have hxi := mem_finOf.mp hx
    refine mem_comps_iff.mpr ⟨x, mem_finOf.mpr (Set.mem_biUnion hi hxi), ?_⟩
    exact (linkClass_iUnion_sep hs hi hxi).symm

/-- One hull round acts memberwise on a separated union. -/
theorem hullRound_iUnion_sep {X : ι → Set (Torus d n)} (hs : SepFam ω F X) :
    hullRound ω b (⋃ j ∈ F, X j) = ⋃ j ∈ F, hullRound ω b (X j) := by
  ext y
  constructor
  · rintro (hy | ⟨Y, hY, hsm, hsd, hyY⟩)
    · simp only [Set.mem_iUnion, exists_prop] at hy
      obtain ⟨j, hj, hyj⟩ := hy
      exact Set.mem_biUnion hj (subset_hullRound _ hyj)
    · obtain ⟨i, hi, hYi⟩ := (mem_comps_iUnion_sep hs).mp hY
      exact Set.mem_biUnion hi (Or.inr ⟨Y, hYi, hsm, hsd, hyY⟩)
  · intro hy
    simp only [Set.mem_iUnion, exists_prop] at hy
    obtain ⟨j, hj, hyj⟩ := hy
    rcases hyj with hyj | ⟨Y, hY, hsm, hsd, hyY⟩
    · exact Or.inl (Set.mem_biUnion hj hyj)
    · exact Or.inr ⟨Y, (mem_comps_iUnion_sep hs).mpr ⟨j, hj, hY⟩, hsm, hsd, hyY⟩

/-- The hull closure acts memberwise on a union whose members' closures are separated. -/
theorem hullClosure_iUnion_sep {X : ι → Set (Torus d n)}
    (hs : SepFam ω F (fun i => hullClosure ω b (X i))) :
    hullClosure ω b (⋃ j ∈ F, X j) = ⋃ j ∈ F, hullClosure ω b (X j) := by
  set N := Fintype.card (Torus d n) with hN
  have key : ∀ t ≤ N, (hullRound ω b)^[t] (⋃ j ∈ F, X j) =
      ⋃ j ∈ F, (hullRound ω b)^[t] (X j) := by
    intro t
    induction t with
    | zero => intro _; rfl
    | succ t ih =>
      intro ht
      simp only [Function.iterate_succ_apply']
      rw [ih (by omega)]
      exact hullRound_iUnion_sep (b := b)
        (hs.mono fun i => iter_subset_hullClosure (X i) (by omega))
  exact key N le_rfl

end Balaban.LargeField
