/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.Decoupled2FpGeometry

/-!
# The landed `IsIncUnion` is not anchored; the anchored selector (VMOD-6 §2)

* `isIncUnion_univ_emptySeed`: `(univ, 𝒞)` satisfies `IsIncUnion` for every input, including the empty
  seed `X₁ = ∅` (the vertex set is not anchored to the source).
* `not_universal_gm2`: the logical core of the VMOD-6 counterexample.  A cost `cost` on site sets
  that is positive on the whole torus cannot satisfy the proposed inequality (2.2) with the source
  cost zero and `𝒞 = ∅` for all `IsIncUnion` pairs.  The geometric input of VMOD-6 (positivity of
  `d̃_F^cov(𝕋)` for an aligned full-torus set with two disjoint top cubes, via `bondW_of_layer`) is
  the hypothesis `hpos`; it is not formalized here.
* The **anchored closure** `seedClosure`: the vertices of `incGraph` reachable from the site
  vertices of a seed `S ⊆ X₁ ∩ Ω₁(H)`.  It is the least adjacency-closed set containing the seed
  (`seedClosure_le`), its projections `(seedSites, seedParams)` satisfy `IsIncUnion`, lie in the active
  vertices (`seedSites_subset_incSites`), and contain no vertex not reachable from the seed.
-/

@[expose] public section

namespace Balaban.Localization.Dec2

open Balaban Balaban.Multiscale Balaban.Background Balaban.Reflection Finset Matrix

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
variable {C : DecCover d L N₁ m₁ K} {H : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {a : ℕ → ℝ} {ν : ℝ}

/-- **The landed predicate is not anchored**: for the empty seed `X₁ = ∅` the whole torus with the
parameters `𝒞` is still an `IsIncUnion`. -/
theorem isIncUnion_univ_emptySeed (𝒞 : Finset (ℕ × CTorus d L N₁ m₁ K)) :
    IsIncUnion C H a ν (∅ : Finset (CTorus d L N₁ m₁ K)) 𝒞 Finset.univ 𝒞 :=
  isIncUnion_univ

/-- **Logical core of the counterexample to graph GM2 for `IsIncUnion`.**  If a cost `cost` on site
sets is positive on the whole torus, then the inequality `cost Y ≤ L⁻¹ · 0 + c · |𝒞|` with `𝒞 = ∅`
fails for `Y = univ`, which is an `IsIncUnion` by `isIncUnion_univ`; no constant `c` repairs it. -/
theorem not_universal_gm2 (cost : Finset (CTorus d L N₁ m₁ K) → ℝ)
    (hpos : 0 < cost Finset.univ) (X₁ : Finset (CTorus d L N₁ m₁ K)) :
    ¬ ∃ c : ℝ, ∀ (Y : Finset (CTorus d L N₁ m₁ K)) (A : Finset (ℕ × CTorus d L N₁ m₁ K)),
      IsIncUnion C H a ν X₁ ∅ Y A → cost Y ≤ c * ((∅ : Finset (ℕ × CTorus d L N₁ m₁ K)).card : ℝ) := by
  rintro ⟨c, hc⟩
  have := hc Finset.univ ∅ isIncUnion_univ
  simp at this
  linarith

section Anchored

variable (C H a ν) (X₁ : Finset (CTorus d L N₁ m₁ K)) (𝒞 : Finset (ℕ × CTorus d L N₁ m₁ K))

/-- **The anchored closure**: the vertices reachable in `incGraph` from the site vertices of the
seed `S`. -/
def seedClosure (S : Set (CTorus d L N₁ m₁ K)) : Set (IncV d L N₁ m₁ K) :=
  {v | ∃ s ∈ S, (incGraph C H a ν X₁ 𝒞).Reachable (Sum.inl s) v}

open Classical in
/-- The site projection of the anchored closure. -/
noncomputable def seedSites (S : Set (CTorus d L N₁ m₁ K)) : Finset (CTorus d L N₁ m₁ K) :=
  Finset.univ.filter fun x => (Sum.inl x : IncV d L N₁ m₁ K) ∈ seedClosure C H a ν X₁ 𝒞 S

open Classical in
/-- The parameter projection of the anchored closure. -/
noncomputable def seedParams (S : Set (CTorus d L N₁ m₁ K)) : Finset (ℕ × CTorus d L N₁ m₁ K) :=
  𝒞.filter fun P => (Sum.inr (Sum.inr P) : IncV d L N₁ m₁ K) ∈ seedClosure C H a ν X₁ 𝒞 S

variable {C H a ν X₁ 𝒞} {S : Set (CTorus d L N₁ m₁ K)}

theorem seed_mem_seedClosure {s : CTorus d L N₁ m₁ K} (hs : s ∈ S) :
    (Sum.inl s : IncV d L N₁ m₁ K) ∈ seedClosure C H a ν X₁ 𝒞 S :=
  ⟨s, hs, SimpleGraph.Reachable.refl _⟩

theorem seedClosure_closed {u v : IncV d L N₁ m₁ K}
    (h : (incGraph C H a ν X₁ 𝒞).Adj u v) (hu : u ∈ seedClosure C H a ν X₁ 𝒞 S) :
    v ∈ seedClosure C H a ν X₁ 𝒞 S := by
  obtain ⟨s, hs, hr⟩ := hu
  exact ⟨s, hs, hr.trans h.reachable⟩

/-- **Minimality**: the anchored closure lies in every adjacency-closed set containing the seed. -/
theorem seedClosure_le {U : Set (IncV d L N₁ m₁ K)}
    (hcl : ∀ u v, (incGraph C H a ν X₁ 𝒞).Adj u v → u ∈ U → v ∈ U)
    (hS : ∀ s ∈ S, (Sum.inl s : IncV d L N₁ m₁ K) ∈ U) :
    seedClosure C H a ν X₁ 𝒞 S ⊆ U := by
  have key : ∀ {u v : IncV d L N₁ m₁ K}, (incGraph C H a ν X₁ 𝒞).Walk u v → u ∈ U → v ∈ U := by
    intro u v w
    induction w with
    | nil => exact id
    | cons h _ ih => exact fun hu => ih (hcl _ _ h hu)
  rintro v ⟨s, hs, ⟨w⟩⟩
  exact key w (hS s hs)


/-- A parameter vertex reachable from a site vertex is charged: `P ∈ 𝒞`. -/
theorem mem_of_reachable_param {s : CTorus d L N₁ m₁ K} {P : ℕ × CTorus d L N₁ m₁ K}
    (h : (incGraph C H a ν X₁ 𝒞).Reachable (Sum.inl s) (Sum.inr (Sum.inr P))) : P ∈ 𝒞 := by
  obtain ⟨w⟩ := h.symm
  cases w with
  | cons hadj _ =>
    obtain ⟨-, h1 | h1⟩ := hadj
    · simp [incRel] at h1
    · rename_i u _
      rcases u with x | z | Q
      · simp [incRel] at h1
      · simp [incRel] at h1; exact h1.2.2.2
      · simp [incRel] at h1

/-- **The anchored closure is an `IsIncUnion`.** -/
theorem isIncUnion_seed (S : Set (CTorus d L N₁ m₁ K)) :
    IsIncUnion C H a ν X₁ 𝒞 (seedSites C H a ν X₁ 𝒞 S) (seedParams C H a ν X₁ 𝒞 S) := by
  classical
  refine ⟨seedClosure C H a ν X₁ 𝒞 S, fun u v h hu => seedClosure_closed h hu, ?_, ?_⟩
  · intro x; simp [seedSites]
  · intro P
    simp only [seedParams, Finset.mem_filter]
    constructor
    · exact fun h => h.2
    · intro h
      obtain ⟨s, hs, hr⟩ := h
      exact ⟨mem_of_reachable_param hr, ⟨s, hs, hr⟩⟩

/-- **Anchoring and minimality of the sites**: every site of the closure is reachable from the
seed, and the closure lies in every `IsIncUnion` witness containing the seed. -/
theorem seedSites_subset_of_witness {S : Set (CTorus d L N₁ m₁ K)}
    {U : Set (IncV d L N₁ m₁ K)}
    (hcl : ∀ u v, (incGraph C H a ν X₁ 𝒞).Adj u v → u ∈ U → v ∈ U)
    (hS : ∀ s ∈ S, (Sum.inl s : IncV d L N₁ m₁ K) ∈ U) {x : CTorus d L N₁ m₁ K}
    (hx : x ∈ seedSites C H a ν X₁ 𝒞 S) : (Sum.inl x : IncV d L N₁ m₁ K) ∈ U := by
  classical
  simp only [seedSites, Finset.mem_filter] at hx
  exact seedClosure_le hcl hS hx.2

theorem exists_reachable_of_mem_seedSites {x : CTorus d L N₁ m₁ K}
    (hx : x ∈ seedSites C H a ν X₁ 𝒞 S) :
    ∃ s ∈ S, (incGraph C H a ν X₁ 𝒞).Reachable (Sum.inl s) (Sum.inl x) := by
  classical
  simp only [seedSites, Finset.mem_filter] at hx
  exact hx.2

/-- **The closure of a seed in `X₁ ∩ Ω₁(H)` consists of active sites**: `seedSites ⊆ incSites`. -/
theorem seedSites_subset_incSites (hS : ∀ s ∈ S, s ∈ X₁ ∧ s ∈ H.Ω 1) {x : CTorus d L N₁ m₁ K}
    (hx : x ∈ seedSites C H a ν X₁ 𝒞 S) : x ∈ incSites C H a ν X₁ 𝒞 := by
  obtain ⟨s, hs, ⟨w⟩⟩ := exists_reachable_of_mem_seedSites hx
  have hsin : s ∈ incSites C H a ν X₁ 𝒞 := ⟨(hS s hs).2, Or.inl (hS s hs).1⟩
  cases w.reverse with
  | nil => exact hsin
  | cons hadj _ =>
    obtain ⟨-, h1 | h1⟩ := hadj
    · rename_i u _
      rcases u with y | z | Q
      · exact h1.1
      · simp [incRel] at h1
      · simp [incRel] at h1
    · rename_i u _
      rcases u with y | z | Q
      · exact h1.2.1
      · simp only [incRel] at h1
        obtain ⟨hE, hL, hf⟩ := h1
        obtain ⟨b, -, hb⟩ := id hf
        rcases hb with rfl | ⟨y, -, rfl⟩
        · exact ⟨b.2, Or.inr ⟨z, hE, hL, hf⟩⟩
        · exact ⟨y.2, Or.inr ⟨z, hE, hL, hf⟩⟩
      · simp [incRel] at h1

end Anchored

end Balaban.Localization.Dec2
