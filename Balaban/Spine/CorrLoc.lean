/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Budget.CanonicalBook
public import Balaban.LargeField.Operators.Setup

/-!
# The localization of a component is a region history with the same localized history

For a component `Z` of `Z^pre_k` the lineage localization `H.locRH k Z` is a region history
without removals whose only component of `Z^pre_k` is `Z`.  The lineage of `Z` in it is the lineage
of `Z` in `H` (`lin_loc_eq`), hence the localized history of `Z` in `H.locRH k Z` is that of `Z` in
`H` (`localHistory_locRH`).
-/

@[expose] public section

open Balaban Balaban.LargeField

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

section LocLoc

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K : ℕ} [NeZero S.L]
  {H : RegionHistory S n R k0 K}

namespace RegionHistory

theorem mem_locComps {k : ℕ} (hkK : k ≤ K) (Z : H.Comp k) {b : ℕ} (hb : b ≤ k) {Y : H.Comp b}
    (hY : H.Desc b k Y Z) : Y.1 ∈ comps (S.omega b) ((H.locRH k Z).F.Zp b) := by
  classical
  have hZp : (H.locRH k Z).F.Zp b = H.lin b k Z := by
    show finOf ((H.locRH k Z).F.Zpre b) = _
    rw [locRH_Zpre Z hb (hb.trans hkK), finOf_coe]
  rw [hZp]
  set T : Finset (Finset (Torus S.d (n b))) := (H.ancFin b k Z).image Subtype.val with hT
  have hTc : T ⊆ comps (S.omega b) (H.Zp b) := by
    intro Y' hY'
    obtain ⟨Y'', -, rfl⟩ := Finset.mem_image.1 hY'
    exact Y''.2
  have h1 := comps_biUnion_of_subset hTc
  have h2 : T.biUnion id = H.lin b k Z := by
    ext x
    simp [hT, lin, Finset.mem_biUnion]
  rw [h2] at h1
  rw [h1]
  exact Finset.mem_image.2 ⟨Y, mem_ancFin.2 hY, rfl⟩


theorem desc_loc {k : ℕ} (hkK : k ≤ K) (Z : H.Comp k) {a b : ℕ} {Y : H.Comp a} {W : H.Comp b}
    (hd : H.Desc a b Y W) (hWZ : H.Desc b k W Z) :
    (H.locRH k Z).Desc a b ⟨Y.1, mem_locComps hkK Z (hd.le.trans hWZ.le) (hd.trans hWZ)⟩
      ⟨W.1, mem_locComps hkK Z hWZ.le hWZ⟩ := by
  induction hd with
  | refl Y => exact Desc.refl _
  | step b' Y' Y'' W'' hd' hrem hs ih =>
    have hY' : H.Desc b' k Y'' Z := Desc.trans (Desc.single hrem hs) hWZ
    exact Desc.step b' _ ⟨Y''.1, mem_locComps hkK Z hY'.le hY'⟩ _ (ih hY') (by simp [locRH_rem]) hs

theorem lin_loc_eq {k : ℕ} (hkK : k ≤ K) (Z : H.Comp k) {j : ℕ} (hj : j ≤ k) :
    (H.locRH k Z).lin j k ⟨Z.1, locComp_mem H hkK Z⟩ = H.lin j k Z := by
  ext x
  rw [mem_lin, mem_lin]
  constructor
  · rintro ⟨Y, -, hx⟩
    have hx' := comp_subset Y.2 hx
    have hZp : (H.locRH k Z).F.Zp j = H.lin j k Z := by
      show finOf ((H.locRH k Z).F.Zpre j) = _
      rw [locRH_Zpre Z hj (hj.trans hkK), finOf_coe]
    rw [hZp] at hx'
    exact mem_lin.1 hx'
  · rintro ⟨Y, hd, hx⟩
    exact ⟨⟨Y.1, mem_locComps hkK Z hd.le hd⟩, desc_loc hkK Z hd (Desc.refl Z), hx⟩

/-- **The localized history of the localization is the localized history.** -/
theorem localHistory_locRH {M : ℕ} [NeZero M] {k : ℕ} (hkK : k ≤ K) (Z : H.Comp k) :
    (H.locRH k Z).localHistory M K k ⟨Z.1, locComp_mem H hkK Z⟩ = H.localHistory M K k Z := by
  refine localHistory_congr (M := M) (K := K) _ _ rfl ?_
  have hstep := locRH_step_congr (H1 := H.locRH k Z) (H2 := H) hkK
    ⟨Z.1, locComp_mem H hkK Z⟩ Z rfl (fun j hj => lin_loc_eq hkK Z hj) ?_ ?_ ?_ ?_
  · exact hstep
  all_goals
    intro j hj
    have hjK : j < K := by omega
    obtain ⟨p, q, r, s⟩ := locRH_new Z hj hjK
    rw [lin_loc_eq hkK Z (by omega : j + 1 ≤ k)]
  · rw [p, Set.inter_assoc, Set.inter_self]
  · rw [q, Set.inter_assoc, Set.inter_self]
  · rw [r, Set.inter_assoc, Set.inter_self]
  · rw [s, Set.inter_assoc, Set.inter_self]

end RegionHistory

end LocLoc

end Balaban.LargeField
