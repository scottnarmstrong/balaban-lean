module

public import Balaban.LargeField.R.ConfigAdm
public import Balaban.LargeField.Budget.CanonicalBook
import Mathlib.Tactic.Linarith

/-!
# Removed clusters and the gas identity (Part III, Definition III.10.3, Lemma III.10.4)

Fix a kept configuration `Kc` (the non-removed components of a history, with their localized
histories; `Y_k = ⋃ Z`).  A *removed component* is a member `(Z, 𝔞)` with `Z` ripe (`IsRipeMember`).
A *removed cluster* (`RemCluster`) is a nonempty finite family of removed components pairwise
and from `Y_k` at index distance `≥ ω_k`, connected under "index distance `≤ 4ω_k`".  Its support
is `⋃ Z^{∼2ω_k}` (`clusterSupp`); the *admissibility factor* (`admFactor`) is `1` if the cluster
together with the kept components within `2ω_k` of it is an admissible configuration, else `0`.

`gas_identity`: the removed parts `Rm` for which `Kc ∪ Rm` is an admissible configuration
correspond bijectively (`Rm ↦ clusters Rm`) to the families of pairwise compatible (disjoint
supports) removed clusters with `∏ admFactor = 1`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open Balaban RegionHistory
open scoped Classical

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K : ℕ} {M k : ℕ} [NeZero M]

/-- A member `(Z, 𝔞)` of a configuration: a set and its localized history. -/
abbrev ConfigPair (S : Setting) (n : ℕ → ℕ) (M K k : ℕ) :=
  Finset (Torus S.d (n k)) × LocalHistory S n M K

/-- The member `(Z, 𝔞)` is *ripe*: `Z` is ripe in the localized history `𝔞`
(the bookkeeping is a function of the localized history,
`ripeMember_iff`). -/
def IsRipeMember (R : ℕ → ℝ) (k0 K M k : ℕ) [NeZero M] (m : ConfigPair S n M K k) : Prop :=
  ∃ H' ∈ (historiesWithFinal (R := R) (k0 := k0) (K := K) k m.1 : Set (RegionHistory S n R k0 K)),
    ∃ c : H'.Comp k, c.1 = m.1 ∧ H'.localHistory M K k c = m.2 ∧ S.Ripe k (H'.bk k c)

/-- Ripeness of a member is read off any representative history. -/
theorem ripeMember_iff (hk : k ≤ K) {m : ConfigPair S n M K k} {H' : RegionHistory S n R k0 K}
    (hH' : H' ∈ (historiesWithFinal (R := R) (k0 := k0) (K := K) k m.1 :
      Set (RegionHistory S n R k0 K))) {c : H'.Comp k} (hc : c.1 = m.1)
    (hc2 : H'.localHistory M K k c = m.2) :
    IsRipeMember R k0 K M k m ↔ S.Ripe k (H'.bk k c) := by
  constructor
  · rintro ⟨H'', -, c'', hc1'', hc2'', hr⟩
    obtain ⟨-, -, hb⟩ := spine_bk_eq_of_localHistory_eq (M := M) k hk H'' H' c'' c
      (hc2''.trans hc2.symm)
    rwa [hb] at hr
  · intro hr
    exact ⟨H', hH', c, hc, hc2, hr⟩

/-- Two members are at index distance `≤ 4ω_k` of each other. -/
def Near4 (S : Setting) (n : ℕ → ℕ) (M K k : ℕ) (m m' : ConfigPair S n M K k) : Prop :=
  ∃ x ∈ m.1, ∃ y ∈ m'.1, supDist x y ≤ 4 * S.omega k

theorem Near4.symm {m m' : ConfigPair S n M K k} (h : Near4 S n M K k m m') :
    Near4 S n M K k m' m := by
  obtain ⟨x, hx, y, hy, hxy⟩ := h
  exact ⟨y, hy, x, hx, by rwa [supDist_comm]⟩

/-- **Definition III.10.3 (removed cluster)**: a nonempty finite family of removed components,
connected under "index distance `≤ 4ω_k`", at index distance `≥ ω_k` from each other and from
`Y_k` (the sets of the kept configuration `Kc`). -/
structure RemCluster (Kc : HistConfig S n R k0 K M k) (C : Finset (ConfigPair S n M K k)) : Prop where
  nonempty : C.Nonempty
  ripe : ∀ m ∈ C, IsRipeMember R k0 K M k m
  mem_hist : ∀ m ∈ C, m.2 ∈ localizedHistories (S := S) (n := n) R k0 K M k m.1
  sep : ∀ m ∈ C, ∀ m' ∈ C, m ≠ m' → ∀ x ∈ m.1, ∀ y ∈ m'.1, S.omega k ≤ supDist x y
  sepKept : ∀ m ∈ C, ∀ m' ∈ Kc.members, ∀ x ∈ m.1, ∀ y ∈ m'.1, S.omega k ≤ supDist x y
  connected : ∀ m ∈ C, ∀ m' ∈ C,
    Relation.ReflTransGen (fun a b => a ∈ C ∧ b ∈ C ∧ Near4 S n M K k a b) m m'

/-- The support `S(𝒞) = ⋃_{Z ∈ 𝒞} Z^{∼2ω_k}` of a cluster. -/
def clusterSupp (S : Setting) (n : ℕ → ℕ) (M K k : ℕ) (C : Finset (ConfigPair S n M K k)) :
    Set (Torus S.d (n k)) :=
  ⋃ m ∈ C, nbhd (2 * S.omega k) ((m.1 : Finset (Torus S.d (n k))) : Set (Torus S.d (n k)))

/-- The core `c(𝒞) = ⋃_{Z ∈ 𝒞} Z` of a cluster. -/
def clusterCore (S : Setting) (n : ℕ → ℕ) (M K k : ℕ) (C : Finset (ConfigPair S n M K k)) :
    Set (Torus S.d (n k)) :=
  ⋃ m ∈ C, ((m.1 : Finset (Torus S.d (n k))) : Set (Torus S.d (n k)))

/-- The kept components within `2ω_k` of the cluster: `𝒴(𝒞)`. -/
noncomputable def keptNear (Kc : HistConfig S n R k0 K M k) (C : Finset (ConfigPair S n M K k)) :
    Finset (ConfigPair S n M K k) :=
  Kc.members.filter fun m' => ∃ x ∈ m'.1, ∃ y ∈ clusterCore S n M K k C,
    supDist x y ≤ 2 * S.omega k

/-- A finite family of members is the family of members of an admissible configuration. -/
def IsAdmFamily (R : ℕ → ℝ) (k0 K M k : ℕ) [NeZero M] (G : Finset (ConfigPair S n M K k)) : Prop :=
  ∃ F : HistConfig S n R k0 K M k, F.members = G ∧ IsAdmConfig F

/-- **Definition III.10.3 (admissibility factor)**: `1` if `𝒞 ∪ 𝒴(𝒞)` is an admissible
configuration, `0` otherwise. -/
noncomputable def admFactor (Kc : HistConfig S n R k0 K M k) (C : Finset (ConfigPair S n M K k)) : ℕ :=
  if IsAdmFamily (S := S) (n := n) R k0 K M k (C ∪ keptNear Kc C) then 1 else 0

/-- Removed parts `Rm` with non-removed part `Kc`: removed components, disjoint from `Kc`, such
that `Kc ∪ Rm` is an admissible configuration. -/
def IsRemSet (Kc : HistConfig S n R k0 K M k) (Rm : Finset (ConfigPair S n M K k)) : Prop :=
  (∀ m ∈ Rm, IsRipeMember R k0 K M k m) ∧ Disjoint Rm Kc.members ∧
    IsAdmFamily (S := S) (n := n) R k0 K M k (Kc.members ∪ Rm)

/-- Families of pairwise compatible (disjoint supports) removed clusters with
`∏ admFactor = 1`. -/
def IsClusterFamily (Kc : HistConfig S n R k0 K M k)
    (𝒞 : Finset (Finset (ConfigPair S n M K k))) : Prop :=
  (∀ C ∈ 𝒞, RemCluster Kc C) ∧
    (∀ C ∈ 𝒞, ∀ C' ∈ 𝒞, C ≠ C' →
      Disjoint (clusterSupp S n M K k C) (clusterSupp S n M K k C')) ∧
    ∏ C ∈ 𝒞, admFactor Kc C = 1

/-- The relation "connected through `Rm` under index distance `≤ 4ω_k`". -/
def ClusterRel (S : Setting) (n : ℕ → ℕ) (M K k : ℕ) (Rm : Finset (ConfigPair S n M K k))
    (m m' : ConfigPair S n M K k) : Prop :=
  Relation.ReflTransGen (fun a b => a ∈ Rm ∧ b ∈ Rm ∧ Near4 S n M K k a b) m m'

/-- The class of `m` in `Rm`. -/
noncomputable def clusterOf (S : Setting) (n : ℕ → ℕ) (M K k : ℕ)
    (Rm : Finset (ConfigPair S n M K k)) (m : ConfigPair S n M K k) :
    Finset (ConfigPair S n M K k) :=
  Rm.filter fun m' => ClusterRel S n M K k Rm m m'

/-- The clusters of the removed components `Rm` under "index distance `≤ 4ω_k`". -/
noncomputable def clusters (S : Setting) (n : ℕ → ℕ) (M K k : ℕ)
    (Rm : Finset (ConfigPair S n M K k)) : Finset (Finset (ConfigPair S n M K k)) :=
  Rm.image (clusterOf S n M K k Rm)

end Balaban.LargeField
