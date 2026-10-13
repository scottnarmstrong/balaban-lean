/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.RipeGeoCollar
public import Balaban.LargeField.History.RetainedShell

/-!
# Non-vacuity of the retained-shell lemma

On the lineage localization `H0.locRH T Z0` of the genuine-radii ripe history
(`RipeGeoWitness`, `RipeGeoCollar`), at the core scale `q = k₁(T)` the region `Z_q` is nonempty
(`deepA`) and not everything (`exists_out0`).  Since the torus is connected, some cube `x ∈ Z_q`
is adjacent to a cube `y ∉ Z_q`; `x` lies in a non-removed component of `Z^pre_q`, is at
distance `≤ 1 ≤ 2⌊R_{q-1}⌋ + 3` from `Y = Z_qᶜ`, and the lemma
`retained_shell_subset_OmegaDD` puts it in `Ω''_q`.  The numeric premise
`2⌊R_{q-1}⌋ + 3 < ω_q` holds in every region history (`two_floor_add_three_lt_omega`).
-/

@[expose] public section

namespace Balaban.Inhabited.RipeGeo

open Balaban Balaban.LargeField Balaban.Inhabited Balaban.Multiscale

theorem exists_adj_cross {α : Type*} {r : α → α → Prop} {A : Set α} {a b : α}
    (h : Relation.ReflTransGen r a b) (ha : a ∈ A) (hb : b ∉ A) :
    ∃ x ∈ A, ∃ y ∉ A, r x y := by
  induction h with
  | refl => exact absurd ha hb
  | @tail m c _ hbc ih =>
    by_cases hm : m ∈ A
    · exact ⟨m, hm, c, hb, hbc⟩
    · exact ih hm

theorem conn0 (q : ℕ) (x y : Torus S0.d (n0 q)) : Relation.ReflTransGen Adj x y :=
  adj_connected (N₀ := N1) (L := S0.L) (k := T - q) x y

theorem aux (q : ℕ) (hq : 1 ≤ q) (u w : Torus S0.d (n0 q))
    (hu : u ∈ ((H0.locRH T Z0).step q).Z) (hw : w ∉ ((H0.locRH T Z0).step q).Z) :
    ∃ j, ∃ C : (H0.locRH T Z0).Comp (j + 1), C.1 ∉ (H0.locRH T Z0).rem (j + 1) ∧
      ∃ x ∈ C.1, ∃ y ∈ (((H0.locRH T Z0).step (j + 1)).Z)ᶜ, supDist x y ≤ 1 ∧
        x ∈ ((H0.locRH T Z0).step j).OmegaDD := by
  cases q with
  | zero => omega
  | succ j =>
    obtain ⟨x, hx, y, hy, hxy⟩ := exists_adj_cross (conn0 (j + 1) u w) hu hw
    obtain ⟨C, hC, hxC⟩ := RegionHistory.exists_retained_of_mem_Z (H := H0.locRH T Z0) hx
    have hd : supDist x y ≤ 1 := Adj.supDist_le_one hxy
    exact ⟨j, C, hC, x, hxC, y, hy, hd,
      (H0.locRH T Z0).retained_shell_subset_OmegaDD_of_dist j hC hxC hy (hd.trans (by omega))⟩

/-- **Non-vacuity of `retained_shell_subset_OmegaDD`**: on the localized genuine-radii ripe
history there are a scale `j + 1`, a non-removed component `C` of `Z^pre_{j+1}`, cubes `x ∈ C` and
`y ∉ Z_{j+1}` with `d(x, y) ≤ 1`, and then `x ∈ Ω''_{j+1}`. -/
theorem retained_shell_witness :
    ∃ j, ∃ C : (H0.locRH T Z0).Comp (j + 1), C.1 ∉ (H0.locRH T Z0).rem (j + 1) ∧
      ∃ x ∈ C.1, ∃ y ∈ (((H0.locRH T Z0).step (j + 1)).Z)ᶜ, supDist x y ≤ 1 ∧
        x ∈ ((H0.locRH T Z0).step j).OmegaDD := by
  have hk1 := hW0.k1_pos hkK0
  have hqk := RegionHistory.k1_le hW0
  obtain ⟨u, hu, -⟩ := deepA (S0.k1 T) hk1 hqk
  obtain ⟨w, hw⟩ := exists_out0 (S0.k1 T) hW0.core_k1
  exact aux (S0.k1 T) hk1 u w hu hw

end Balaban.Inhabited.RipeGeo
