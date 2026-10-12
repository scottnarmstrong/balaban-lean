/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.DecEquivRelabel
public import Balaban.Localization.DecEquivLat
public import Balaban.Localization.I5Expansion

/-!
# The expansion terms `𝓔(X, Y)` under a lattice symmetry

A lattice symmetry `σ` of the paved torus maps the parameter cubes `Pset q` of the cover to the
parameter cubes `Pset (τ q)` and the sets `D(P)` to `D(τ P)` (`PolymerSymm`).  Then the components
`Y(𝒞)`, the sets `Y[𝒞]`, the connected families and therefore the terms are transported:
`𝓔(σ X, σ Y)(σ u) = 𝓔(X, Y)(u)` (`evTerm_relabel`), if the function expanded is transported
(on the unit polydisc) by the relabelling of the parameters.
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background Balaban.Analysis Finset

section Graph

variable {Ω : Type*}

theorem componentOf_image (G : SimpleGraph Ω) (e : Ω ≃ Ω) (hadj : ∀ a b, G.Adj (e a) (e b) ↔ G.Adj a b)
    (X₁ V : Set Ω) : componentOf G (e '' X₁) (e '' V) = e '' componentOf G X₁ V := by
  have key : ∀ (y x : Ω), Relation.ReflTransGen (fun a b => G.Adj a b ∧ a ∈ V ∧ b ∈ V) y x →
      Relation.ReflTransGen (fun a b => G.Adj a b ∧ a ∈ e '' V ∧ b ∈ e '' V) (e y) (e x) := by
    intro y x h
    induction h with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ hab ih =>
      exact ih.tail ⟨(hadj _ _).2 hab.1, ⟨_, hab.2.1, rfl⟩, ⟨_, hab.2.2, rfl⟩⟩
  have key' : ∀ (y' : Ω) (x : Ω),
      Relation.ReflTransGen (fun a b => G.Adj a b ∧ a ∈ e '' V ∧ b ∈ e '' V) (e y') x →
      Relation.ReflTransGen (fun a b => G.Adj a b ∧ a ∈ V ∧ b ∈ V) y' (e.symm x) := by
    intro y' x h
    induction h with
    | refl => simpa using Relation.ReflTransGen.refl
    | tail _ hbc ih =>
      obtain ⟨hadjbc, ⟨b', hb', hb⟩, ⟨c', hc', hc⟩⟩ := hbc
      rename_i b c
      subst hb hc
      refine ih.tail ⟨?_, by simpa using hb', by simpa using hc'⟩
      simpa using (hadj (e.symm (e b')) (e.symm (e c'))).1 (by simpa using hadjbc)
  ext x
  constructor
  · rintro ⟨y, ⟨y', hy', rfl⟩, h⟩
    exact ⟨e.symm x, ⟨y', hy', key' y' x h⟩, by simp⟩
  · rintro ⟨x', ⟨y, hy, h⟩, rfl⟩
    exact ⟨e y, ⟨y, hy, rfl⟩, key y x' h⟩

end Graph

section Polymers

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
variable {G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {m₀ : ℕ}

/-- **Compatibility of a symmetry with the polymers**: the symmetry `σ` maps the parameter cube of
the centre `q` to the parameter cube of `τ q`, and the set `D(P)` to the set `D(τ P)`. -/
structure PolymerSymm (G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ) (m₀ : ℕ)
    (σ : Equiv.Perm (CTorus d L N₁ m₁ K)) (τ : Equiv.Perm (ℕ × CTorus d L N₁ m₁ K)) : Prop where
  pset : ∀ q x, σ x ∈ Pset m₁ (τ q) ↔ x ∈ Pset m₁ q
  dsites : ∀ q, Dsites G m₀ (τ q) = σ '' Dsites G m₀ q

theorem polymerSymm_refl (G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ) (m₀ : ℕ) :
    PolymerSymm G m₀ (1 : Equiv.Perm (CTorus d L N₁ m₁ K))
      (1 : Equiv.Perm (ℕ × CTorus d L N₁ m₁ K)) :=
  ⟨fun _ _ => Iff.rfl, fun q => by simp⟩

theorem polymerSymm_nonempty (G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ) (m₀ : ℕ) :
    ∃ (σ : Equiv.Perm (CTorus d L N₁ m₁ K)) (τ : Equiv.Perm (ℕ × CTorus d L N₁ m₁ K)),
      PolymerSymm G m₀ σ τ := ⟨1, 1, polymerSymm_refl G m₀⟩

variable {σ : Equiv.Perm (CTorus d L N₁ m₁ K)} {τ : Equiv.Perm (ℕ × CTorus d L N₁ m₁ K)}

theorem PolymerSymm.image_pset (P : PolymerSymm G m₀ σ τ) (q : ℕ × CTorus d L N₁ m₁ K) :
    σ '' Pset m₁ q = Pset m₁ (τ q) := by
  ext z
  obtain ⟨x, rfl⟩ := σ.surjective z
  rw [Set.image_congr (g := σ) fun _ _ => rfl, Set.mem_image_equiv]
  simp only [Equiv.symm_apply_apply]
  exact (P.pset q x).symm

variable {ι ι' : Type*} [DecidableEq ι] [DecidableEq ι']
  (c : ι → ℕ × CTorus d L N₁ m₁ K) (c' : ι' → ℕ × CTorus d L N₁ m₁ K) (κ : ι ≃ ι')
  (hc : ∀ i, c' (κ i) = τ (c i))

include hc

omit [DecidableEq ι] [DecidableEq ι'] in
theorem patchUnion_relabel (P : PolymerSymm G m₀ σ τ) (X₁ : Set (CTorus d L N₁ m₁ K)) (C : Finset ι) :
    patchUnion (σ '' X₁) (fun i' => Pset m₁ (c' i')) (C.map κ.toEmbedding) =
      σ '' patchUnion X₁ (fun i => Pset m₁ (c i)) C := by
  unfold patchUnion
  rw [Set.image_union]
  congr 1
  ext x
  simp only [Set.mem_iUnion, Finset.mem_map, Equiv.coe_toEmbedding, exists_prop, Set.mem_image]
  constructor
  · rintro ⟨i', ⟨i, hi, rfl⟩, hx⟩
    rw [hc, ← P.image_pset] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact ⟨y, ⟨i, hi, hy⟩, rfl⟩
  · rintro ⟨y, ⟨i, hi, hy⟩, rfl⟩
    exact ⟨κ i, ⟨i, hi, rfl⟩, by rw [hc, ← P.image_pset]; exact ⟨y, hy, rfl⟩⟩

omit [DecidableEq ι] [DecidableEq ι'] in
theorem Ysites_relabel (P : PolymerSymm G m₀ σ τ) (X₁ : Set (CTorus d L N₁ m₁ K)) (C : Finset ι) :
    Ysites G m₀ c' (σ '' X₁) (C.map κ.toEmbedding) = σ '' Ysites G m₀ c X₁ C := by
  unfold Ysites
  rw [Set.image_union]
  congr 1
  ext x
  simp only [Set.mem_iUnion, Finset.mem_map, Equiv.coe_toEmbedding, exists_prop, Set.mem_image]
  constructor
  · rintro ⟨i', ⟨i, hi, rfl⟩, hx⟩
    rw [hc, P.dsites] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact ⟨y, ⟨i, hi, hy⟩, rfl⟩
  · rintro ⟨y, ⟨i, hi, hy⟩, rfl⟩
    exact ⟨κ i, ⟨i, hi, rfl⟩, by rw [hc, P.dsites]; exact ⟨y, hy, rfl⟩⟩


omit [DecidableEq ι] [DecidableEq ι'] in
theorem compY_relabel (P : PolymerSymm G m₀ σ τ)
    (S : LatSymm G G σ) (X₁ : Set (CTorus d L N₁ m₁ K)) (C : Finset ι) :
    compY c' (σ '' X₁) (C.map κ.toEmbedding) = σ '' compY c X₁ C := by
  unfold compY
  rw [patchUnion_relabel c c' κ hc P]
  refine componentOf_image (latGraph d ((N₁ * L ^ m₁) * L ^ K)) σ (fun a b => ?_) _ _
  show (σ a ≠ σ b ∧ Nbr (σ a) (σ b)) ↔ (a ≠ b ∧ Nbr a b)
  rw [σ.injective.ne_iff]
  exact and_congr_right fun _ => S.adj_iff a b

omit [DecidableEq ι] [DecidableEq ι'] in
theorem isConnectedFamily_relabel (P : PolymerSymm G m₀ σ τ)
    (S : LatSymm G G σ) (X₁ : Set (CTorus d L N₁ m₁ K)) (C : Finset ι) :
    IsConnectedFamily (fun i' => Pset m₁ (c' i')) (compY c' (σ '' X₁)) (C.map κ.toEmbedding) ↔
      IsConnectedFamily (fun i => Pset m₁ (c i)) (compY c X₁) C := by
  unfold IsConnectedFamily
  rw [compY_relabel c c' κ hc P S]
  constructor
  · intro h i hi
    have := h (κ i) (Finset.mem_map_of_mem _ hi)
    simp only [hc, ← P.image_pset] at this
    exact (Set.image_subset_image_iff σ.injective).1 this
  · intro h i' hi'
    obtain ⟨i, hi, rfl⟩ := Finset.mem_map.1 hi'
    simp only [Equiv.coe_toEmbedding, hc, ← P.image_pset]
    exact Set.image_mono (h i hi)

end Polymers

section Terms

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
variable {G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {m₀ : ℕ}
variable {σ : Equiv.Perm (CTorus d L N₁ m₁ K)} {τ : Equiv.Perm (ℕ × CTorus d L N₁ m₁ K)}
variable {ι ι' : Type*} [DecidableEq ι] [Fintype ι] [DecidableEq ι'] [Fintype ι']
  (c : ι → ℕ × CTorus d L N₁ m₁ K) (c' : ι' → ℕ × CTorus d L N₁ m₁ K) (κ : ι ≃ ι')
  (hc : ∀ i, c' (κ i) = τ (c i))

include hc

omit [DecidableEq ι] [DecidableEq ι'] in
/-- **The connected families are transported by the relabelling.** -/
theorem connFams_relabel (P : PolymerSymm G m₀ σ τ) (S : LatSymm G G σ)
    (X₁ Y : Set (CTorus d L N₁ m₁ K)) :
    connFams c' G m₀ (σ '' X₁) (σ '' Y) =
      (connFams c G m₀ X₁ Y).map ⟨Finset.map κ.toEmbedding, Finset.map_injective _⟩ := by
  ext C'
  rw [mem_connFams, Finset.mem_map]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨C'.map κ.symm.toEmbedding, ?_, ?_⟩
    · rw [mem_connFams]
      have e : C' = (C'.map κ.symm.toEmbedding).map κ.toEmbedding := by ext j; simp
      rw [e] at h1 h2
      refine ⟨(isConnectedFamily_relabel c c' κ hc P S X₁ _).1 h1, ?_⟩
      rw [Ysites_relabel c c' κ hc P] at h2
      exact σ.injective.image_injective h2
    · ext j; simp
  · rintro ⟨C, hC, rfl⟩
    rw [mem_connFams] at hC
    refine ⟨?_, ?_⟩
    · exact (isConnectedFamily_relabel c c' κ hc P S X₁ C).2 hC.1
    · simp only [Function.Embedding.coeFn_mk]
      rw [Ysites_relabel c c' κ hc P, hC.2]

omit hc in
/-- **Lattice-symmetry covariance of the terms `𝓔(X, Y)`**: if the function expanded is transported by
a relabelling `κ` of the parameters (at the points of the unit polydisc) and the centres by `τ`, then
`𝓔(σ X, σ Y)(u') = 𝓔(X, Y)(u)`. -/
theorem evTerm_relabel {R : ℝ} (hR : 1 < R) (P : PolymerSymm G m₀ σ τ) (S : LatSymm G G σ)
    (hc : ∀ i, c' (κ i) = τ (c i)) (X₁ Y : Set (CTorus d L N₁ m₁ K))
    {U U' : Type*} {F : U → (ι → ℂ) → ℂ} {F' : U' → (ι' → ℂ) → ℂ} {u : U} {u' : U'}
    (hF : AnalyticOnNhd ℂ (F u) (polydisc (0 : ι → ℂ) (fun _ => R)))
    (hF' : AnalyticOnNhd ℂ (F' u') (polydisc (0 : ι' → ℂ) (fun _ => R)))
    (hff : ∀ s ∈ unitCube ι', F' u' s = F u (s ∘ κ)) :
    evTerm c' G m₀ (σ '' X₁) F' (σ '' Y) u' = evTerm c G m₀ X₁ F Y u := by
  unfold evTerm
  rw [connFams_relabel c c' κ hc P S X₁ Y, Finset.sum_map]
  exact Finset.sum_congr rfl fun C _ => coef_relabel hR κ hF hF' hff C

end Terms

end Balaban.Localization
