/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.Decoupled2FpCount

/-!
# The raw anchored site projection is constant (VMOD-7 §3)

If the first domain `Ω₁(H)` lies in the seed set `X₁` and is nonempty and nearest-neighbour
connected, then for every charge set `𝒞` the anchored site projection `seedSites` of a nonempty
seed `S ⊆ Ω₁(H)` is all of `Ω₁(H)` (`seedSites_eq_Ω_one`).  Consequently the literal Peierls count
`∑_{𝒞 : seedSites 𝒞 = Y} e^{-κ₂ |𝒞|} ≤ 1` is false as soon as the charge universe contains a
parameter (`not_peierls_seedSites`).  This records a defect: no counting theorem of that shape
can be true.
-/

@[expose] public section

namespace Balaban.Localization.Dec2

open Balaban Balaban.Multiscale Balaban.Background Balaban.Reflection Finset Matrix

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
variable {C : DecCover d L N₁ m₁ K} {H : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {a : ℕ → ℝ} {ν : ℝ}
variable {X₁ : Finset (CTorus d L N₁ m₁ K)} {𝒞 : Finset (ℕ × CTorus d L N₁ m₁ K)}

/-- Nearest-neighbour connectedness of the first domain `Ω₁(H)` inside itself. -/
def OmegaOneConnected (H : GeneratingSet d L (N₁ * L ^ m₁) K ϱ) : Prop :=
  ∀ x ∈ H.Ω 1, ∀ y ∈ H.Ω 1,
    Relation.ReflTransGen (fun u v : CTorus d L N₁ m₁ K => u ∈ H.Ω 1 ∧ v ∈ H.Ω 1 ∧ Adj u v) x y

/-- If `Ω₁(H) ⊆ X₁`, every site of `Ω₁(H)` is an active site, for every charge set. -/
theorem mem_incSites_of_subset (hX : ∀ x ∈ H.Ω 1, x ∈ X₁) {x : CTorus d L N₁ m₁ K}
    (hx : x ∈ H.Ω 1) : x ∈ incSites C H a ν X₁ 𝒞 :=
  ⟨hx, Or.inl (hX x hx)⟩

/-- **(3.1) The raw anchored projection is the whole first domain, for every charge set.** -/
theorem seedSites_eq_Ω_one (hX : ∀ x ∈ H.Ω 1, x ∈ X₁) (hconn : OmegaOneConnected H)
    {S : Set (CTorus d L N₁ m₁ K)} (hSΩ : ∀ s ∈ S, s ∈ H.Ω 1) (hS : S.Nonempty) :
    seedSites C H a ν X₁ 𝒞 S = H.Ω 1 := by
  classical
  obtain ⟨s₀, hs₀⟩ := hS
  ext x
  constructor
  · intro hx
    exact (seedSites_subset_incSites (fun s hs => ⟨hX s (hSΩ s hs), hSΩ s hs⟩) hx).1
  · intro hx
    have key : ∀ y, Relation.ReflTransGen
        (fun u v : CTorus d L N₁ m₁ K => u ∈ H.Ω 1 ∧ v ∈ H.Ω 1 ∧ Adj u v) s₀ y →
        (incGraph C H a ν X₁ 𝒞).Reachable (Sum.inl s₀) (Sum.inl y) := by
      intro y hy
      induction hy with
      | refl => exact SimpleGraph.Reachable.refl _
      | @tail u v _ h ih =>
        refine ih.trans ?_
        by_cases huv : u = v
        · rw [huv]
        · refine SimpleGraph.Adj.reachable ?_
          refine ⟨fun h' => huv (Sum.inl.inj h'), Or.inl ?_⟩
          exact ⟨mem_incSites_of_subset hX h.1, mem_incSites_of_subset hX h.2.1, h.2.2⟩
    have hr := key x (hconn s₀ (hSΩ s₀ hs₀) x hx)
    simp only [seedSites, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨s₀, hs₀, hr⟩

/-- **(3.2) The literal Peierls count over the raw anchored site projection is false.**  For every
real `κ₂` and every finite charge universe `U` containing a parameter `P`, the sum of the weights
`e^{-κ₂ |𝒞|}` over the sub-families `𝒞 ⊆ U` whose raw projection equals `Y = Ω₁(H)` exceeds `1`
(it contains the two terms `𝒞 = ∅` and `𝒞 = {P}`). -/
theorem not_peierls_seedSites (hX : ∀ x ∈ H.Ω 1, x ∈ X₁) (hconn : OmegaOneConnected H)
    {S : Set (CTorus d L N₁ m₁ K)} (hSΩ : ∀ s ∈ S, s ∈ H.Ω 1) (hS : S.Nonempty)
    (U : Finset (ℕ × CTorus d L N₁ m₁ K)) {P : ℕ × CTorus d L N₁ m₁ K} (hP : P ∈ U) (κ₂ : ℝ) :
    ¬ (∑ 𝒞 ∈ U.powerset.filter (fun 𝒞 => seedSites C H a ν X₁ 𝒞 S = H.Ω 1),
        Real.exp (-κ₂ * (𝒞.card : ℝ)) ≤ 1) := by
  classical
  have hall : U.powerset.filter (fun 𝒞 => seedSites C H a ν X₁ 𝒞 S = H.Ω 1) = U.powerset := by
    apply Finset.filter_true_of_mem
    intro 𝒞 _
    exact seedSites_eq_Ω_one hX hconn hSΩ hS
  rw [hall]
  intro hle
  have hsub : ({∅, {P}} : Finset (Finset (ℕ × CTorus d L N₁ m₁ K))) ⊆ U.powerset := by
    intro 𝒞 h
    simp only [Finset.mem_insert, Finset.mem_singleton] at h
    rcases h with rfl | rfl
    · exact Finset.empty_mem_powerset _
    · exact Finset.mem_powerset.2 (Finset.singleton_subset_iff.2 hP)
  have h1 := Finset.sum_le_sum_of_subset_of_nonneg hsub
    (f := fun 𝒞 : Finset (ℕ × CTorus d L N₁ m₁ K) => Real.exp (-κ₂ * (𝒞.card : ℝ)))
    (fun _ _ _ => (Real.exp_pos _).le)
  have hne : (∅ : Finset (ℕ × CTorus d L N₁ m₁ K)) ≠ {P} := fun h => by
    simpa using congrArg (P ∈ ·) h
  rw [Finset.sum_pair hne] at h1
  simp only [Finset.card_empty, Finset.card_singleton, Nat.cast_zero, mul_zero, Real.exp_zero,
    Nat.cast_one, mul_one] at h1
  have := Real.exp_pos (-κ₂)
  linarith

end Balaban.Localization.Dec2
