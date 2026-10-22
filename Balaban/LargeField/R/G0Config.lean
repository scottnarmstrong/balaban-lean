/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.G0Gas
public import Balaban.Spine.CorrLoc
public import Balaban.LargeField.R.LocalLemmas
public import Balaban.LargeField.Operators.Setup
public import Balaban.LargeField.Budget.Injective

/-!
# G0: the scale-`k` configuration of a history is a configuration

LFR Definition III.10.1: a configuration is a family of pairs `(Z, 𝔞_Z)` with `𝔞_Z ∈ 𝔥_k(Z)`, the
localized histories of the admissible histories with the single pre-`R` component `Z`, the sets at
index distance `≥ ω_k`.  For a history `H` and a component `Z` of `Z^pre_k(H)`, the lineage
localization `H.locRH k Z` (Lemma I.3.9) is such a history, and its localized history at `Z` is
the localized history of `Z` in `H`:

* `locRH_admissible`: the localization has no removal record, so it is admissible;
* `lin_locRH`: the lineages of `Z` in the localization are those in `H`;
* `localHistory_mem_localizedHistories`: `H.localHistory M K k Z ∈ 𝔥_k(Z)`;
* `configMembers_mem_hist`, `configMembers_sep`, `keptConfig_members`: the members of the scale-`k`
  configuration of a history satisfy the two clauses of `HistConfig`, so `keptConfig` is the
  configuration with these members.
-/

@[expose] public section

noncomputable section

open scoped Classical
open Finset Balaban Balaban.LargeField.Def7

namespace Balaban.LargeField

namespace RegionHistory

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K : ℕ}
  {H : RegionHistory S n R k0 K} {k : ℕ}

/-- The lineage localization has no removal record, so it is admissible. -/
theorem locRH_admissible (Z : H.Comp k) : (H.locRH k Z).Admissible := by
  intro j c hc
  simp [locRH_rem] at hc

/-- The component `Z` of the pre-`R` region of its lineage localization. -/
def locComp (hkK : k ≤ K) (Z : H.Comp k) : (H.locRH k Z).Comp k :=
  ⟨Z.1, by have := H.neZero_L; exact locComp_mem H hkK Z⟩

theorem locComp_val (hkK : k ≤ K) (Z : H.Comp k) : (locComp hkK Z).1 = Z.1 := by
  unfold locComp
  rfl

/-- **The lineages of `Z` in its localization are those in `H`.** -/
theorem lin_locRH (M : ℕ) [NeZero M] (hkK : k ≤ K) (Z : H.Comp k) {j : ℕ} (hj : j ≤ k) :
    (H.locRH k Z).lin j k (locComp hkK Z) = H.lin j k Z := by
  have := H.neZero_L
  ext y
  obtain ⟨x, rfl⟩ := cubeMap_surjective (M := M) H.F.hnn (hj.trans hkK) y
  have h1 := mem_lin_iff_of_rem_between (H := H.locRH k Z) (M := M) hj hkK
    (fun i _ _ => locRH_rem k Z i) (locComp hkK Z) x
  rw [locRH_Zpre Z hj (hj.trans hkK)] at h1
  rw [← Finset.mem_coe, h1, Finset.mem_coe]
  constructor
  · exact fun h => h.1
  · intro h
    refine ⟨h, ?_⟩
    rw [locComp_val]
    obtain ⟨Y, hd, hxY⟩ := mem_lin.mp h
    exact cubeMap_mem_of_desc H.F.hnn hkK hd hxY

/-- **The localized history of a component lies in `𝔥_k(Z)`** (Definition III.10.1): it is the
localized history of the lineage localization, an admissible history with the single pre-`R`
component `Z`. -/
theorem localHistory_mem_localizedHistories (M : ℕ) [NeZero M] (hkK : k ≤ K) (Z : H.Comp k) :
    H.localHistory M K k Z ∈ localizedHistories (S := S) (n := n) R k0 K M k Z.1 := by
  refine ⟨H.locRH k Z, ⟨locRH_admissible Z, locRH_Zp hkK Z, ?_⟩, locComp hkK Z,
    locComp_val hkK Z, localHistory_locRH (M := M) hkK Z⟩
  have := locRH_comps hkK Z
  rwa [locRH_Zp hkK Z] at this

end RegionHistory

namespace G0

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K M : ℕ} [NeZero M]
  {k : ℕ}

omit [NeZero M] in
/-- The members of the scale-`k` configuration of a history are its components with their
localized histories. -/
theorem mem_configMembers [NeZero M] {A : LabHist S n R k0 K} {m : ConfigPair S n M K k} :
    m ∈ configMembers M k A ↔ ∃ c : A.H.Comp k, (c.1, A.H.localHistory M K k c) = m := by
  simp [configMembers]

/-- The members of the scale-`k` configuration have localized histories in `𝔥_k(Z)`. -/
theorem configMembers_mem_hist (hkK : k ≤ K) (A : LabHist S n R k0 K) :
    ∀ m ∈ configMembers M k A, m.2 ∈ localizedHistories (S := S) (n := n) R k0 K M k m.1 := by
  intro m hm
  obtain ⟨c, rfl⟩ := mem_configMembers.mp hm
  exact RegionHistory.localHistory_mem_localizedHistories M hkK c

/-- The sets of the members of the scale-`k` configuration are at index distance `≥ ω_k`. -/
theorem configMembers_sep (A : LabHist S n R k0 K) :
    ∀ m ∈ configMembers M k A, ∀ m' ∈ configMembers M k A, m ≠ m' →
      ∀ x ∈ m.1, ∀ y ∈ m'.1, S.omega k ≤ supDist x y := by
  intro m hm m' hm' hne x hx y hy
  obtain ⟨c, rfl⟩ := mem_configMembers.mp hm
  obtain ⟨c', rfl⟩ := mem_configMembers.mp hm'
  refine comps_sep c.2 c'.2 (fun h => hne ?_) hx hy
  have : c = c' := Subtype.ext h
  rw [this]

/-- **`keptConfig` is the configuration of the history** (its members are `configMembers`). -/
theorem keptConfig_members (hkK : k ≤ K) (A : LabHist S n R k0 K) :
    (keptConfig M k A).members = configMembers M k A := by
  unfold keptConfig
  split_ifs with h
  · rfl
  · exact absurd ⟨configMembers_mem_hist hkK A, configMembers_sep A⟩ h

end G0

end Balaban.LargeField
