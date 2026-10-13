/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.History.Core
public import Balaban.LargeField.History.RegionLineage
public import Balaban.LargeField.Def7SmallField

/-!
# The retained shell and the seed margin of a region history

Geometry of a region history `H` at a scale `k = j + 1 ≥ 1`, with `Y = Z_kᶜ` the small-field
region, `a = ⌊R_{k-1}⌋`, `b = ⌊2 R_{k-1}⌋` (so `2a ≤ b`), and `W₂(Y) = Y^{≈2} = nbhd_{2a+2}(Y)`.

* `retained_shell_subset_OmegaDD`: a cube of a retained (non-removed) component of `Z^pre_k`
  at distance `≤ 2a + 3` from `Y` lies in `Ω''_k`.  The proof uses the separation of distinct
  components by `ω_k > 2a + 3` (`core_sep`) and the radius of `Z^{(0)}_k` (`ball_nbhd_Z0`).
  It does not use `H.Admissible`.
* `nbhd_subset_union_OmegaDD`, `W2_subset_union_OmegaDD`: the resulting inclusion
  `nbhd_{2a+3}(Y) ⊆ Y ∪ Ω''_k ⊆ Y ∪ Ω_k`.
* `seed_margin_PQR`, `seed_margin_S`, `seed_margin_old`: a seed centre of a retained component
  is at distance at least `b - 2a + 5` (new `P, Q, R` cubes; surviving old seeds, taken as the
  image `U'` of the step), respectively `b - 2a + 2` (new `S` cubes), from `W₂(Y)`.
  Stated without truncated subtraction.
* `removed_subset_compl_Z`: a removed component lies in `Y`; hence a bound for seeds of
  removed components is impossible.

`ball_nbhd_Z0` is the statement of `Inhabited/RipeGeoCollar.lean : ball_Z0`, re-proved here
because that file imports the witness files.

Not proved here: the transport of an old scale-`j` seed through the block maps to a scale-`k`
centre (`ScaleLiftDistance` of `notes/phase1/Q13-COVER.md` §1, open), the assignment of history
factors to shell sites, the transfer to composed fields and the strict-margin statements
(Q13-COVER §2-§4).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open Balaban Balaban.LargeField.Def7

/-- Every cube outside `Ω''` has its `(⌊2R_k⌋ + 6)`-neighbourhood inside `Z^{(0)}`
(the content of `Balaban.Inhabited.RipeGeo.ball_Z0`, for any region step). -/
theorem RegionStep.ball_nbhd_Z0 {d L a n1 : ℕ} [NeZero a] [NeZero n1] {Rp Rk : ℝ}
    (st : RegionStep d L a n1 Rp Rk) {v : Torus d n1} (hv : v ∈ st.OmegaDDᶜ) :
    nbhd (⌊2 * Rk⌋₊ + 6) {v} ⊆ st.Z0 := by
  have h1 : nbhd 4 {v} ⊆ st.FZ :=
    (nbhd_mono le_rfl (Set.singleton_subset_iff.2 hv)).trans Set.subset_union_left
  refine Set.Subset.trans ?_ st.nbhd_FZ_subset_Z0
  have := nbhd_mono (m := ⌊2 * Rk⌋₊ + 2) le_rfl h1
  rw [nbhd_nbhd] at this
  intro y hy
  exact this (nbhd_mono (by omega) subset_rfl hy)

/-- A new `S` cube has its `(⌊2R_k⌋ + 3)`-neighbourhood inside `Z^{(0)}`. -/
theorem RegionStep.ball_nbhd_Z0_S {d L a n1 : ℕ} [NeZero a] [NeZero n1] {Rp Rk : ℝ}
    (st : RegionStep d L a n1 Rp Rk) {v : Torus d n1} (hv : v ∈ st.S) :
    nbhd (⌊2 * Rk⌋₊ + 3) {v} ⊆ st.Z0 := by
  have h1 : nbhd 1 {v} ⊆ st.FZ :=
    (nbhd_mono le_rfl (Set.singleton_subset_iff.2 hv)).trans Set.subset_union_right
  refine Set.Subset.trans ?_ st.nbhd_FZ_subset_Z0
  have := nbhd_mono (m := ⌊2 * Rk⌋₊ + 2) le_rfl h1
  rw [nbhd_nbhd] at this
  intro y hy
  exact this (nbhd_mono (by omega) subset_rfl hy)

theorem two_mul_floor_le {R : ℝ} (hR : 0 ≤ R) : 2 * ⌊R⌋₊ ≤ ⌊2 * R⌋₊ := by
  apply Nat.le_floor
  push_cast
  linarith [Nat.floor_le hR]

namespace RegionHistory

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K : ℕ}
  (H : RegionHistory S n R k0 K)

include H in
/-- The component width at scale `j + 1` exceeds `2⌊R_j⌋ + 3` (from `RH.le`). -/
theorem two_floor_add_three_lt_omega (j : ℕ) : 2 * ⌊R j⌋₊ + 3 < S.omega (j + 1) := by
  have h1 : ⌊R j⌋₊ ≤ ⌊S.Rb * S.lam j ^ 2⌋₊ := Nat.floor_le_floor (H.F.RH.le j)
  have h2 := Setting.omega_eq_omegaW S (j + 1)
  have h3 := omegaW_succ S.L S.Rb S.lam j
  have h4 : 2 ≤ S.L := H.F.ok.two_le_L
  omega

/-- A cube of a removed component lies in `Y = Z_kᶜ`. -/
theorem removed_subset_compl_Z {k : ℕ} {c : Finset (Torus S.d (n k))} (hc : c ∈ H.rem k)
    {x : Torus S.d (n k)} (hx : x ∈ c) : x ∈ ((H.step k).Z)ᶜ := by
  have hcc : c ∈ comps (S.omega k) (H.Zp k) := H.rem_sub k hc
  exact fun hz => (H.mem_Z_iff (Y := ⟨c, hcc⟩) hx).1 hz hc

/-- A cube of `Z^pre_k` outside `Z_k` lies in a removed component. -/
theorem exists_removed_of_mem_Zpre {k : ℕ} {y : Torus S.d (n k)} (hy : y ∈ H.F.Zpre k)
    (hyZ : y ∉ (H.step k).Z) : ∃ c ∈ H.rem k, y ∈ c := by
  rw [H.Z_eq k] at hyZ
  simp only [Set.mem_sdiff, Set.mem_iUnion, Finset.mem_coe, exists_prop, not_and, not_not] at hyZ
  exact hyZ hy

/-- A cube of `Z_k` lies in a retained (non-removed) component of `Z^pre_k`. -/
theorem exists_retained_of_mem_Z {k : ℕ} {x : Torus S.d (n k)} (hx : x ∈ (H.step k).Z) :
    ∃ C : H.Comp k, C.1 ∉ H.rem k ∧ x ∈ C.1 := by
  obtain ⟨Y, hY, hxY⟩ := mem_comp_self (ω := S.omega k)
    (mem_finOf.mpr (H.Z_subset_Zpre k hx))
  exact ⟨⟨Y, hY⟩, (H.mem_Z_iff (Y := ⟨Y, hY⟩) hxY).1 hx, hxY⟩

/-- A cube of a retained component and a cube of `Zpre` outside `Z_k` are at distance
`≥ ω_k`: a retained and a removed component are different components. -/
theorem omega_le_supDist_retained_removed {k : ℕ} {C : H.Comp k} (hC : C.1 ∉ H.rem k)
    {x y : Torus S.d (n k)} (hx : x ∈ C.1) (hyZ : y ∈ H.F.Zpre k) (hy : y ∉ (H.step k).Z) :
    S.omega k ≤ supDist x y := by
  obtain ⟨c, hc, hyc⟩ := H.exists_removed_of_mem_Zpre hyZ hy
  refine H.core_sep (Y := C) (Y' := ⟨c, H.rem_sub k hc⟩) ?_ hx hyc
  intro h
  exact hC (by have : C.1 = c := congrArg Subtype.val h; rwa [this])

/-- **Retained shell** (Q13-COVER §1 (1)).  Let `C` be a component of `Z^pre_{j+1}` not removed
at that scale, `x ∈ C`, and `y ∉ Z_{j+1}` with `d(x, y) ≤ 2⌊R_j⌋ + 3`.  Then `x ∈ Ω''_{j+1}`.
Numeric premise used: `2⌊R_j⌋ + 3 < ω_{j+1}` (`two_floor_add_three_lt_omega`, from
`RH.le`).  No admissibility is used. -/
theorem retained_shell_subset_OmegaDD_of_dist (j : ℕ) {C : H.Comp (j + 1)}
    (hC : C.1 ∉ H.rem (j + 1)) {x y : Torus S.d (n (j + 1))} (hx : x ∈ C.1)
    (hy : y ∈ ((H.step (j + 1)).Z)ᶜ) (hd : supDist x y ≤ 2 * ⌊R j⌋₊ + 3) :
    x ∈ (H.step j).OmegaDD := by
  by_contra hxO
  have hball := (H.step j).ball_nbhd_Z0 hxO
  have hb : 2 * ⌊R j⌋₊ ≤ ⌊2 * R j⌋₊ := two_mul_floor_le (H.F.RH.nonneg j)
  have hy0 : y ∈ (H.step j).Z0 := hball (mem_nbhd.mpr ⟨x, rfl, by rw [supDist_comm]; omega⟩)
  have hyP : y ∈ H.F.Zpre (j + 1) := (H.step j).Z0_subset_Zpre _ _ hy0
  have := H.omega_le_supDist_retained_removed hC hx hyP hy
  have := H.two_floor_add_three_lt_omega j
  omega

/-- **Retained shell**, in the form `x ∈ nbhd_{2a+3}(Y)`, `Y = Z_{j+1}ᶜ`, `a = ⌊R_j⌋`. -/
theorem retained_shell_subset_OmegaDD (j : ℕ) {C : H.Comp (j + 1)}
    (hC : C.1 ∉ H.rem (j + 1)) {x : Torus S.d (n (j + 1))} (hx : x ∈ C.1)
    (hxY : x ∈ nbhd (2 * ⌊R j⌋₊ + 3) ((H.step (j + 1)).Z)ᶜ) :
    x ∈ (H.step j).OmegaDD := by
  obtain ⟨y, hy, hd⟩ := mem_nbhd.mp hxY
  exact H.retained_shell_subset_OmegaDD_of_dist j hC hx hy hd

/-- The inclusion `nbhd_{2a+3}(Y) ⊆ Y ∪ Ω''_{j+1}`, `Y = Z_{j+1}ᶜ`. -/
theorem nbhd_subset_union_OmegaDD (j : ℕ) :
    nbhd (2 * ⌊R j⌋₊ + 3) ((H.step (j + 1)).Z)ᶜ ⊆
      ((H.step (j + 1)).Z)ᶜ ∪ (H.step j).OmegaDD := by
  intro x hx
  by_cases hxZ : x ∈ (H.step (j + 1)).Z
  · obtain ⟨C, hC, hxC⟩ := H.exists_retained_of_mem_Z hxZ
    exact Or.inr (H.retained_shell_subset_OmegaDD j hC hxC hx)
  · exact Or.inl hxZ

/-- The same with `Ω_{j+1} ⊇ Ω''_{j+1}`. -/
theorem nbhd_subset_union_Omega (j : ℕ) :
    nbhd (2 * ⌊R j⌋₊ + 3) ((H.step (j + 1)).Z)ᶜ ⊆
      ((H.step (j + 1)).Z)ᶜ ∪ (H.step j).Omega :=
  (H.nbhd_subset_union_OmegaDD j).trans
    (Set.union_subset_union_right _ (H.step j).OmegaDD_subset_Omega)

theorem W2_subset_nbhd (j : ℕ) (Y : Set (Torus S.d (n (j + 1)))) :
    W2 R Y ⊆ nbhd (2 * ⌊R j⌋₊ + 2) Y := by
  intro x hx
  have e : W2 R Y = nbhd (2 * ⌊R j⌋₊ + 2) Y := by
    unfold W2 thick
    rw [nbhd_nbhd]
    congr 1
    simp only [Nat.add_sub_cancel]
    omega
  exact e ▸ hx

theorem thickY_subset_nbhd (j : ℕ) (Y : Set (Torus S.d (n (j + 1)))) :
    thickY R Y ⊆ nbhd (⌊R j⌋₊ + 1) Y := fun _ hx => hx

/-- Every cube of `W₂(Y)` is in `Y` or in `Ω''_{j+1}` (and lies in a retained component in the
second case). -/
theorem W2_subset_union_OmegaDD (j : ℕ) :
    W2 R ((H.step (j + 1)).Z)ᶜ ⊆ ((H.step (j + 1)).Z)ᶜ ∪ (H.step j).OmegaDD :=
  fun _ hx => H.nbhd_subset_union_OmegaDD j
    (nbhd_mono (by omega) subset_rfl (W2_subset_nbhd j _ hx))

theorem thickY_subset_union_OmegaDD (j : ℕ) :
    thickY R ((H.step (j + 1)).Z)ᶜ ⊆ ((H.step (j + 1)).Z)ᶜ ∪ (H.step j).OmegaDD :=
  fun _ hx => H.nbhd_subset_union_OmegaDD j
    (nbhd_mono (by omega) subset_rfl (thickY_subset_nbhd j _ hx))

/-! ### Seed margin -/

theorem floor_two_mul_le_add_one {R : ℝ} (hR : 0 ≤ R) : ⌊2 * R⌋₊ ≤ 2 * ⌊R⌋₊ + 1 := by
  have h : 2 * R < ((2 * ⌊R⌋₊ + 2 : ℕ) : ℝ) := by
    push_cast; linarith [Nat.lt_floor_add_one R]
  have := (Nat.floor_lt (by linarith)).2 h
  omega

/-- A centre `v` of a retained component whose `m`-ball, `m ≤ ⌊2R_j⌋ + 6`, lies in
`Z^{(0)}_{j+1}` is at distance `> m` from every cube of `Y = Z_{j+1}ᶜ`.  (Numeric premise:
`m < ω_{j+1}`, which follows from `m ≤ 2⌊R_j⌋ + 7` and `ω_{j+1} ≥ 2⌊R_j⌋ + 13`.) -/
theorem lt_supDist_of_ball (j : ℕ) {C : H.Comp (j + 1)} (hC : C.1 ∉ H.rem (j + 1))
    {v : Torus S.d (n (j + 1))} (hv : v ∈ C.1) {m : ℕ} (hm : m ≤ ⌊2 * R j⌋₊ + 6)
    (hball : nbhd m {v} ⊆ (H.step j).Z0)
    {y : Torus S.d (n (j + 1))} (hy : y ∈ ((H.step (j + 1)).Z)ᶜ) : m < supDist v y := by
  by_contra hle
  have hy0 : y ∈ (H.step j).Z0 :=
    hball (mem_nbhd.mpr ⟨v, rfl, by rw [supDist_comm]; omega⟩)
  have h1 := H.omega_le_supDist_retained_removed hC hv ((H.step j).Z0_subset_Zpre _ _ hy0) hy
  have h2 := floor_two_mul_le_add_one (H.F.RH.nonneg j)
  have h3 := Setting.omega_eq_omegaW S (j + 1)
  have h4 := omegaW_succ S.L S.Rb S.lam j
  have h5 : ⌊R j⌋₊ ≤ ⌊S.Rb * S.lam j ^ 2⌋₊ := Nat.floor_le_floor (H.F.RH.le j)
  have h6 : 2 ≤ S.L := H.F.ok.two_le_L
  omega

/-- From a ball of radius `m ≤ ⌊2R_j⌋ + 6` around a retained cube: every `w ∈ W₂(Y)` has
`m + 1 ≤ d(v, w) + 2⌊R_j⌋ + 2`. -/
theorem margin_W2_of_ball (j : ℕ) {C : H.Comp (j + 1)} (hC : C.1 ∉ H.rem (j + 1))
    {v : Torus S.d (n (j + 1))} (hv : v ∈ C.1) {m : ℕ} (hm : m ≤ ⌊2 * R j⌋₊ + 6)
    (hball : nbhd m {v} ⊆ (H.step j).Z0) {w : Torus S.d (n (j + 1))}
    (hw : w ∈ W2 R ((H.step (j + 1)).Z)ᶜ) : m + 1 ≤ supDist v w + (2 * ⌊R j⌋₊ + 2) := by
  obtain ⟨y, hy, hwy⟩ := mem_nbhd.mp (W2_subset_nbhd j _ hw)
  have h1 := H.lt_supDist_of_ball j hC hv hm hball hy
  have h2 := supDist_triangle v w y
  omega

/-- **Seed margin, new `P, Q, R` cubes.**  A new `P`, `Q` or `R` cube of the step `j` which lies
in a retained component of `Z^pre_{j+1}` satisfies `⌊2R_j⌋ - 2⌊R_j⌋ + 5 ≤ d(v, w)` for every
`w ∈ W₂(Y)` (written without subtraction). -/
theorem seed_margin_PQR (j : ℕ) {C : H.Comp (j + 1)} (hC : C.1 ∉ H.rem (j + 1))
    {v : Torus S.d (n (j + 1))} (hv : v ∈ C.1)
    (hs : v ∈ (H.step j).P ∪ (H.step j).Q ∪ (H.step j).R) {w : Torus S.d (n (j + 1))}
    (hw : w ∈ W2 R ((H.step (j + 1)).Z)ᶜ) :
    ⌊2 * R j⌋₊ + 5 ≤ supDist v w + 2 * ⌊R j⌋₊ := by
  have hO : v ∈ ((H.step j).OmegaDD)ᶜ := by
    rcases hs with (h | h) | h
    · exact (H.step j).Omega_compl_subset_OmegaDD_compl ((H.step j).P_subset_compl_Omega h)
    · exact (H.step j).Q_subset_compl_OmegaDD h
    · exact (H.step j).R_subset_compl_OmegaDD h
  have := H.margin_W2_of_ball j hC hv le_rfl ((H.step j).ball_nbhd_Z0 hO) hw
  omega

/-- **Seed margin, surviving old seeds** (the image `U'_{j+1}` of the step): the same bound
`⌊2R_j⌋ + 5 ≤ d(v, w) + 2⌊R_j⌋`. -/
theorem seed_margin_old (j : ℕ) {C : H.Comp (j + 1)} (hC : C.1 ∉ H.rem (j + 1))
    {v : Torus S.d (n (j + 1))} (hv : v ∈ C.1) (hs : v ∈ (H.step j).Uprime)
    {w : Torus S.d (n (j + 1))} (hw : w ∈ W2 R ((H.step (j + 1)).Z)ᶜ) :
    ⌊2 * R j⌋₊ + 5 ≤ supDist v w + 2 * ⌊R j⌋₊ := by
  have hO : v ∈ ((H.step j).OmegaDD)ᶜ :=
    (H.step j).Omega_compl_subset_OmegaDD_compl
      ((H.step j).OmegaPrime_compl_subset_Omega_compl ((H.step j).Uprime_subset_compl hs))
  have := H.margin_W2_of_ball j hC hv le_rfl ((H.step j).ball_nbhd_Z0 hO) hw
  omega

/-- **Seed margin, new `S` cubes**: `⌊2R_j⌋ + 2 ≤ d(v, w) + 2⌊R_j⌋`. -/
theorem seed_margin_S (j : ℕ) {C : H.Comp (j + 1)} (hC : C.1 ∉ H.rem (j + 1))
    {v : Torus S.d (n (j + 1))} (hv : v ∈ C.1) (hs : v ∈ (H.step j).S)
    {w : Torus S.d (n (j + 1))} (hw : w ∈ W2 R ((H.step (j + 1)).Z)ᶜ) :
    ⌊2 * R j⌋₊ + 2 ≤ supDist v w + 2 * ⌊R j⌋₊ := by
  have := H.margin_W2_of_ball j hC hv (m := ⌊2 * R j⌋₊ + 3) (by omega)
    ((H.step j).ball_nbhd_Z0_S hs) hw
  omega

end RegionHistory

end Balaban.LargeField
