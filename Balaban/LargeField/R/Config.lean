module

public import Balaban.LargeField.Budget.RecordForward
public import Balaban.LargeField.History.InhabitedJoint

/-!
# Configurations of localized histories (Part III, Definition III.10.1)

A *configuration* at scale `k` is a finite family `{(Z, 𝔞_Z)}` of sets `Z ⊂ 𝕋_k` with localized
histories `𝔞_Z ∈ 𝔥_k(Z)` (each the localized history of an admissible region history with the single
pre-`R` component `Z`), the `Z` pairwise at index distance `≥ ω_k`.  It is *admissible*
(`IsAdmConfig`) if some admissible global history has exactly these `Z` as the components of its
pre-`R` region at scale `k`, with these localized histories.  Two members are *linked* if their
sets are at index distance `≤ 2 ω_k`; a *clique* is a family of pairwise linked members.

The localized history is `RegionHistory.localHistory` (Definition I.4.4): the records of the
lineage of the component, on the fine torus.  The `R`-records of the lineage components are
empty in a localized history (lineages consist of non-removed components, `Desc.first`).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open Balaban RegionHistory

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K : ℕ}

/-- `𝔥_k(Z)` as a set of localized histories: the localized histories (Definition I.4.4, on the
fine torus with `M` sites per cube) of the elements of `historiesWithFinal k Z`, i.e. of the
admissible region histories whose pre-`R` region at scale `k` is `Z`, with `Z` as only
component. -/
def localizedHistories (R : ℕ → ℝ) (k0 K M k : ℕ) [NeZero M] (Z : Finset (Torus S.d (n k))) :
    Set (LocalHistory S n M K) :=
  {a | ∃ H' ∈ (historiesWithFinal (R := R) (k0 := k0) (K := K) k Z : Set (RegionHistory S n R k0 K)),
    ∃ c : H'.Comp k, c.1 = Z ∧ H'.localHistory M K k c = a}

/-- **Definition III.10.1**: a configuration at scale `k`: a finite family of pairs `(Z, 𝔞_Z)` with
`𝔞_Z` a localized history in `𝔥_k(Z)`, the sets `Z` pairwise at index distance `≥ ω_k`. -/
structure HistConfig (S : Setting) (n : ℕ → ℕ) [∀ k, NeZero (n k)] (R : ℕ → ℝ) (k0 K M k : ℕ)
    [NeZero M] where
  /-- the members `(Z, 𝔞_Z)` -/
  members : Finset (Finset (Torus S.d (n k)) × LocalHistory S n M K)
  /-- `𝔞_Z ∈ 𝔥_k(Z)` -/
  mem_hist : ∀ m ∈ members, m.2 ∈ localizedHistories (S := S) (n := n) R k0 K M k m.1
  /-- the sets are pairwise at index distance `≥ ω_k` -/
  sep : ∀ m ∈ members, ∀ m' ∈ members, m ≠ m' → ∀ x ∈ m.1, ∀ y ∈ m'.1, S.omega k ≤ supDist x y

namespace HistConfig

variable {M k : ℕ} [NeZero M]

/-- A subfamily of a configuration is a configuration. -/
def sub (F : HistConfig S n R k0 K M k) (G : Finset (Finset (Torus S.d (n k)) × LocalHistory S n M K))
    (hG : G ⊆ F.members) : HistConfig S n R k0 K M k where
  members := G
  mem_hist m hm := F.mem_hist m (hG hm)
  sep m hm m' hm' := F.sep m (hG hm) m' (hG hm')

/-- The empty configuration. -/
def empty : HistConfig S n R k0 K M k where
  members := ∅
  mem_hist := by simp
  sep := by simp

/-- Two members are *linked* if their sets are at index distance `≤ 2 ω_k`
(Definition III.10.1). -/
def Linked (S : Setting) (n : ℕ → ℕ) (k : ℕ) (M K : ℕ)
    (m m' : Finset (Torus S.d (n k)) × LocalHistory S n M K) : Prop :=
  ∃ x ∈ m.1, ∃ y ∈ m'.1, supDist x y ≤ 2 * S.omega k

/-- A *clique*: a family of pairwise linked members. -/
def IsClique (S : Setting) (n : ℕ → ℕ) (k M K : ℕ)
    (C : Finset (Finset (Torus S.d (n k)) × LocalHistory S n M K)) : Prop :=
  ∀ m ∈ C, ∀ m' ∈ C, Linked S n k M K m m'

end HistConfig

/-- **Definition III.10.1**: the configuration `F` is *admissible* if there is an admissible global
history whose pre-`R` components at scale `k` are exactly the sets `Z` of the members, with the
members' localized histories (the `R`-records at scales `< k` being part of the localized
history). -/
def IsAdmConfig {M k : ℕ} [NeZero M] (F : HistConfig S n R k0 K M k) : Prop :=
  ∃ H : RegionHistory S n R k0 K, H.Admissible ∧
    (∀ c : H.Comp k, ∃ m ∈ F.members, m.1 = c.1) ∧
    ∀ m ∈ F.members, ∃ c : H.Comp k, c.1 = m.1 ∧ H.localHistory M K k c = m.2

end Balaban.LargeField
