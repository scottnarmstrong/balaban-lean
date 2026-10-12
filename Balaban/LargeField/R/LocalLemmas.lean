module

public import Balaban.LargeField.Budget.RecordForward
public import Balaban.LargeField.Operators.DomainGeom

/-!
# Lineages and localized histories: auxiliary facts for the assembly of histories

* `supDist_cubeMap_le`: coarsening does not increase the index distance of the cubes of two sites;
* `locRH_step_eq_of_localHistory_eq`: equal localized histories have equal localization steps;
* `mem_lin_iff_of_rem`: in a history without removals, the lineage of a component `Z` of scale `k`
  at scale `j` is the set of cubes of `Z^pre_j` whose coarsening lies in `Z`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open Balaban

section Distance

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {K M : ℕ} [NeZero M]

theorem div_le_self_of_one_le {D L : ℕ} (hL : 1 ≤ L) : (D + L - 1) / L ≤ D := by
  rcases Nat.eq_zero_or_pos D with rfl | hD
  · simp only [zero_add]
    exact Nat.le_of_eq (Nat.div_eq_of_lt (by omega))
  · apply Nat.div_le_of_le_mul
    obtain ⟨l, rfl⟩ : ∃ l, L = l + 1 := ⟨L - 1, by omega⟩
    obtain ⟨d, rfl⟩ : ∃ d, D = d + 1 := ⟨D - 1, by omega⟩
    have : d + 1 + (l + 1) - 1 = d + l + 1 := by omega
    rw [this]
    nlinarith [Nat.zero_le (l * d)]

/-- Coarsening does not increase the index distance of the cubes containing two fine sites. -/
theorem supDist_cubeMap_le (hnn : ∀ i, i < K → n i = S.L * n (i + 1)) (hL : 1 ≤ S.L) {j k : ℕ}
    (hjk : j ≤ k) (hkK : k ≤ K) (x x' : Torus S.d (M * n K * S.L ^ K)) :
    supDist (cubeMap n S.L M K k x) (cubeMap n S.L M K k x') ≤
      supDist (cubeMap n S.L M K j x) (cubeMap n S.L M K j x') := by
  have := NeZero.of_pos (show 0 < S.L by omega)
  induction k, hjk using Nat.le_induction with
  | base => exact le_rfl
  | succ k hjk ih =>
    have h1 := ih (by omega)
    rw [← cubeMap_succ hnn (by omega) x, ← cubeMap_succ hnn (by omega) x']
    exact (supDist_blockMap_le (hnn k (by omega)) _ _).trans
      ((div_le_self_of_one_le hL).trans h1)

end Distance

namespace RegionHistory

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K : ℕ}

/-- Equal localized histories have equal localization steps. -/
theorem locRH_step_eq_of_localHistory_eq {H1 H2 : RegionHistory S n R k0 K} {M k : ℕ} [NeZero M]
    (hkK : k ≤ K) (Z1 : H1.Comp k) (Z2 : H2.Comp k) (hZ : Z1.1 = Z2.1)
    (h : H1.localHistory M K k Z1 = H2.localHistory M K k Z2) (j : ℕ) :
    (H1.locRH k Z1).step j = (H2.locRH k Z2).step j := by
  refine locRH_step_congr hkK Z1 Z2 hZ (fun j hj => lin_eq_of_localHistory_eq hkK Z1 Z2 h hj)
    ?_ ?_ ?_ ?_ j
  · exact fun j hj => (new_eq_of_localHistory_eq hkK Z1 Z2 h hj).1
  · exact fun j hj => (new_eq_of_localHistory_eq hkK Z1 Z2 h hj).2.1
  · exact fun j hj => (new_eq_of_localHistory_eq hkK Z1 Z2 h hj).2.2.1
  · exact fun j hj => (new_eq_of_localHistory_eq hkK Z1 Z2 h hj).2.2.2

variable {H : RegionHistory S n R k0 K}

/-- Without removals the coarsening of a cube of `Z^pre_j` lies in `Z^pre_k`. -/
theorem cubeMap_mem_Zpre_of_rem (hrem : ∀ j, H.rem j = ∅) {M : ℕ} [NeZero M] {j k : ℕ}
    (hjk : j ≤ k) (hkK : k ≤ K) {x : Torus S.d (M * n K * S.L ^ K)}
    (hx : cubeMap n S.L M K j x ∈ H.F.Zpre j) : cubeMap n S.L M K k x ∈ H.F.Zpre k := by
  have := H.neZero_L
  induction k, hjk using Nat.le_induction with
  | base => exact hx
  | succ k hjk ih =>
    have h1 := ih (by omega)
    have h2 : cubeMap n S.L M K k x ∈ (H.step k).Z := by
      rw [H.Z_eq k, hrem k]
      simpa using h1
    rw [← cubeMap_succ H.F.hnn (by omega) x]
    exact H.blockMap_Z_subset_Zpre k h2

/-- **Lemma I.4.3 (c) without removals**: the lineage of `Z` at scale `j` is the set of cubes of
`Z^pre_j` whose coarsening lies in `Z`. -/
theorem mem_lin_iff_of_rem (hrem : ∀ j, H.rem j = ∅) {M : ℕ} [NeZero M] {j k : ℕ} (hjk : j ≤ k)
    (hkK : k ≤ K) (Z : H.Comp k) (x : Torus S.d (M * n K * S.L ^ K)) :
    cubeMap n S.L M K j x ∈ ((H.lin j k Z : Finset (Torus S.d (n j))) : Set _) ↔
      cubeMap n S.L M K j x ∈ H.F.Zpre j ∧ cubeMap n S.L M K k x ∈ Z.1 := by
  have := H.neZero_L
  induction k, hjk using Nat.le_induction with
  | base =>
    rw [lin_self]
    exact ⟨fun h => ⟨mem_finOf.mp (comp_subset Z.2 (Finset.mem_coe.mp h)), h⟩, fun h => h.2⟩
  | succ k hjk ih =>
    rw [H.lin_succ_decomp k hjk Z]
    simp only [Finset.coe_biUnion, Set.mem_iUnion, Finset.mem_coe, exists_prop]
    constructor
    · rintro ⟨c, hc, hxc⟩
      obtain ⟨hcrem, hs⟩ := (H.mem_parts k c Z).mp hc
      obtain ⟨hz, hxk⟩ := (ih (by omega) c).mp hxc
      refine ⟨hz, ?_⟩
      rw [← cubeMap_succ H.F.hnn (by omega) x]
      exact hs ⟨_, hxk, rfl⟩
    · rintro ⟨hz, hxZ⟩
      have hyk : cubeMap n S.L M K k x ∈ H.F.Zpre k :=
        cubeMap_mem_Zpre_of_rem hrem hjk (by omega) hz
      obtain ⟨Y, hY, hyY⟩ := mem_comp_self (ω := S.omega k) (mem_finOf.mpr hyk)
      have hYrem : Y ∉ H.rem k := by rw [hrem k]; simp
      obtain ⟨Z'', hZ''⟩ := H.exists_succ (by omega) (c := ⟨Y, hY⟩) hYrem
      have hxk : cubeMap n S.L M K (k + 1) x ∈ Z''.1 := by
        rw [← cubeMap_succ H.F.hnn (by omega) x]
        exact hZ'' ⟨_, hyY, rfl⟩
      have hZZ : Z''.1 = Z.1 := comp_eq_of_mem Z''.2 Z.2 hxk hxZ
      refine ⟨⟨Y, hY⟩, (H.mem_parts k ⟨Y, hY⟩ Z).mpr ⟨hYrem, ?_⟩, ?_⟩
      · intro z hz'
        have := hZ'' hz'
        rwa [hZZ] at this
      · exact (ih (by omega) ⟨Y, hY⟩).mpr ⟨hz, hyY⟩

end RegionHistory

end Balaban.LargeField
