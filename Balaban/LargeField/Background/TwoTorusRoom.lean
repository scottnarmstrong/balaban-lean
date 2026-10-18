/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Background.TwoTorusZone
public import Balaban.LargeField.Background.TwoTorusSize
public import Balaban.LargeField.Background.TwoTorusVars
public import Balaban.LargeField.Operators.Quiet

/-!
# The cubes of the component, and the room of the box

For a localized history of a component `Zc` of `Z^pre_{k+1}` of a history without removals, the
cubes of `Z_{k+1}` are the cubes of `Zc` (`zcubes_locHist`).
-/

@[expose] public section

namespace Balaban.RootFSpine

open Balaban Balaban.LargeField RegionHistory

section Room

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K M : ℕ} [NeZero M]
  [NeZero S.L]

theorem exists_site_cube (hnn : ∀ i, i < K → n i = S.L * n (i + 1)) {j : ℕ} (hj : j ≤ K)
    (y : Torus S.d (n j)) : ∃ x : Torus S.d (M * n K * S.L ^ K), cubeMap n S.L M K j x = y :=
  exists_site_blockMap (Nat.mul_pos (pow_pos (Nat.pos_of_ne_zero (NeZero.ne _)) _)
    (Nat.pos_of_ne_zero (NeZero.ne _))) (Balaban.LargeField.fine_eq hnn hj) y

omit [NeZero S.L] in
/-- The cubes of a component of `Z^pre_{k+1}` lie in `Z_{k+1}` (histories without removals). -/
theorem mem_step_Z_of_mem_comp (Hl : RegionHistory S n R k0 K) (hrem : ∀ j, Hl.rem j = ∅) {k : ℕ}
    {Zc : Finset (Torus S.d (n (k + 1)))} (hZc : Zc ∈ comps (S.omega (k + 1)) (Hl.F.Zp (k + 1)))
    {y : Torus S.d (n (k + 1))} (hy : y ∈ Zc) : y ∈ (Hl.step (k + 1)).Z := by
  rw [Hl.Z_eq, hrem]
  simp only [Finset.notMem_empty, Set.iUnion_of_empty, Set.iUnion_empty, Set.sdiff_empty]
  exact mem_finOf.1 (comp_subset hZc hy)

/-- The cubes of `Z_{k+1}` of the localized history of a component `Zc` are the cubes of `Zc`
(histories without removals). -/
theorem zcubes_locHist (Hl : RegionHistory S n R k0 K) (hrem : ∀ j, Hl.rem j = ∅) {k : ℕ}
    (hk : k + 1 ≤ K) (Zc : Finset (Torus S.d (n (k + 1))))
    (hZc : Zc ∈ comps (S.omega (k + 1)) (Hl.F.Zp (k + 1))) :
    Zcubes (locHist Hl M K (k + 1) Zc) (k + 1) = (Zc : Set (Torus S.d (n (k + 1)))) := by
  ext y
  constructor
  · intro hy
    obtain ⟨x, hx⟩ := exists_site_cube (M := M) Hl.F.hnn hk y
    have := (hy x hx).2
    simpa [fineSet, hx] using this
  · intro hy x hx
    have hyZ : y ∈ (Hl.step (k + 1)).Z := mem_step_Z_of_mem_comp Hl hrem hZc hy
    refine ⟨?_, ?_⟩
    · show cubeMap n S.L M K (k + 1) x ∈ (Hl.step (k + 1)).Z
      rw [hx]; exact hyZ
    · show cubeMap n S.L M K (k + 1) x ∈ Zc
      rw [hx]; exact hy

omit [NeZero M] [NeZero S.L] in
/-- The record `Z_{k+1}` of the localized history of a component is the fine set of the component. -/
theorem locHist_Z_top (Hl : RegionHistory S n R k0 K) (hrem : ∀ j, Hl.rem j = ∅) {k : ℕ}
    (Zc : Finset (Torus S.d (n (k + 1)))) (hZc : Zc ∈ comps (S.omega (k + 1)) (Hl.F.Zp (k + 1))) :
    (locHist Hl M K (k + 1) Zc).Z (k + 1) = fineSet (S := S) (n := n) M K (k + 1) (Zc : Set _) := by
  ext x
  refine ⟨fun hx => hx.2, fun hx => ⟨?_, hx⟩⟩
  exact mem_step_Z_of_mem_comp Hl hrem hZc (Finset.mem_coe.1 hx)

theorem blockMap_torusCast {d m m' : ℕ} (h : m = m') (P q : ℕ) (x : Torus d m) :
    blockMap P q (torusCast h x) = blockMap P q x := by
  subst h; rfl

theorem site_eq {c M1 L q K : ℕ} {n : ℕ → ℕ} (hM : M = c * M1)
    (hnn : ∀ i, i < K → n i = L * n (i + 1)) (hqK : q ≤ K) :
    M1 * (c * n q) * L ^ q = M * n K * L ^ K := by
  subst hM
  rw [nn_eq_pow' hnn hqK, show L ^ K = L ^ q * L ^ (K - q) by rw [← pow_add]; congr 1; omega]
  ring

/-- **`V` in the box, on the level torus**: if the fine sites of `V` lie in the box, so do the
sites of the level-`(k+1)` torus whose `π_{k+1}`-cube is in the neighbourhood `V` of `Zc`. -/
theorem inBox_levelV {c M1 : ℕ} [NeZero c] [NeZero M1] (Hl : RegionHistory S n R k0 K)
    (hrem : ∀ j, Hl.rem j = ∅) {k : ℕ} (hk : k + 1 ≤ K) (hM : M = c * M1)
    (Zc : Finset (Torus S.d (n (k + 1)))) (hZc : Zc ∈ comps (S.omega (k + 1)) (Hl.F.Zp (k + 1)))
    {ℓ' : ℕ} {cc : Fin S.d → ℤ}
    (hV : ∀ x ∈ Vsites R (locHist Hl M K (k + 1) Zc) (k + 1),
      InBox (M * n K * S.L ^ K) ℓ' cc (liftNear cc x))
    (x : Torus S.d (M1 * (c * n (k + 1)) * S.L ^ (k + 1)))
    (hx : x ∈ fineK1 M1 c (n (k + 1)) S.L k (nbhd 1 (thick ⌊R k⌋₊ (Zc : Set (Torus S.d (n (k + 1))))))) :
    InBox (M1 * (c * n (k + 1)) * S.L ^ (k + 1)) ℓ' cc (liftNear cc x) := by
  have hsite := site_eq (c := c) (M1 := M1) (L := S.L) (q := k + 1) (n := n) hM Hl.F.hnn hk
  have hZ := zcubes_locHist (M := M) Hl hrem hk Zc hZc
  have hmem : torusCast hsite x ∈ Vsites R (locHist Hl M K (k + 1) Zc) (k + 1) := by
    show cubeMap n S.L M K (k + 1) (torusCast hsite x) ∈
      nbhd 1 (thick ⌊R (k + 1 - 1)⌋₊ (Zcubes (locHist Hl M K (k + 1) Zc) (k + 1)))
    rw [hZ]
    show blockMap (S.L ^ (k + 1) * M) (n (k + 1)) (torusCast hsite x) ∈ _
    rw [blockMap_torusCast]
    have := Finset.mem_coe.1 hx
    rw [mem_fineK1] at this
    subst hM
    exact this
  have h1 := hV _ hmem
  rw [liftNear_torusCast] at h1
  exact (inBox_cast hsite rfl).2 h1

/-- **The room of the box**: if the sites of `V` lie in the box, a component has at least `32`
cubes of side `L^{k+1} M` per side of the torus. -/
theorem room_of_V {c M1 : ℕ} [NeZero c] [NeZero M1] (Hl : RegionHistory S n R k0 K)
    (hrem : ∀ j, Hl.rem j = ∅) {k : ℕ} (hk : k + 1 ≤ K) (hM : M = c * M1) (hc : 14 ≤ c)
    (hρ : 3 * S.L ≤ ⌊R k⌋₊) (Zc : Finset (Torus S.d (n (k + 1))))
    (hZc : Zc ∈ comps (S.omega (k + 1)) (Hl.F.Zp (k + 1))) {ℓ' : ℕ} [NeZero ℓ']
    {cc : Fin S.d → ℤ}
    (hV : ∀ x ∈ Vsites R (locHist Hl M K (k + 1) Zc) (k + 1),
      InBox (M * n K * S.L ^ K) ℓ' cc (liftNear cc x)) : 32 ≤ n (k + 1) := by
  have hd : 0 < S.d := by have := Hl.F.ok.three_le_d; omega
  have key := size_of_V (M1 := M1) (c := c) (n1 := n (k + 1)) (L := S.L) (k := k)
    (ω := S.omega (k + 1)) (Zp := Hl.F.Zpre (k + 1)) (Z' := Zc) hd hc ⌊R k⌋₊ hZc (m' := ℓ')
    (cc := cc) (fun x hx => inBox_levelV Hl hrem hk hM Zc hZc hV x (Finset.mem_coe.1 hx))
  by_contra hlt
  have hlt' : n (k + 1) ≤ 31 := by omega
  have hP1 : 0 < S.L ^ (k + 1) * (c * M1) :=
    Nat.mul_pos (pow_pos (Nat.pos_of_ne_zero (NeZero.ne _)) _)
      (Nat.mul_pos (Nat.pos_of_ne_zero (NeZero.ne _)) (Nat.pos_of_ne_zero (NeZero.ne _)))
  have e : M1 * (c * n (k + 1)) * S.L ^ (k + 1) = (S.L ^ (k + 1) * (c * M1)) * n (k + 1) := by ring
  rw [e] at key
  have hL := Hl.F.ok.two_le_L
  have h8 : 8 ≤ ⌊R k⌋₊ + 2 := by omega
  nlinarith

/-- **The margin of the box at the sites of a component**: if `V` lies in the box and the
component has `32` cubes per side, every point `w` of the box whose cube is in `Zc` has the
margin `6 L^{k+1} M`. -/
theorem zone_locHist (Hl : RegionHistory S n R k0 K) (hrem : ∀ j, Hl.rem j = ∅) {k : ℕ}
    (hk : k + 1 ≤ K) (hρ : 3 * S.L ≤ ⌊R k⌋₊) (Zc : Finset (Torus S.d (n (k + 1))))
    (hZc : Zc ∈ comps (S.omega (k + 1)) (Hl.F.Zp (k + 1))) {ℓ' : ℕ} {cc : Fin S.d → ℤ}
    (hV : ∀ x ∈ Vsites R (locHist Hl M K (k + 1) Zc) (k + 1),
      InBox (M * n K * S.L ^ K) ℓ' cc (liftNear cc x)) (h32 : 32 ≤ n (k + 1))
    {w : Fin S.d → ℤ} (hw : InBox (M * n K * S.L ^ K) ℓ' cc w)
    (hcube : cubeMap n S.L M K (k + 1) (zcast (M * n K * S.L ^ K) w) ∈ Zc) :
    InBoxK (6 * (S.L ^ (k + 1) * M)) (M * n K * S.L ^ K) ℓ' cc w := by
  have hL := Hl.F.ok.two_le_L
  have hZ := zcubes_locHist (M := M) Hl hrem hk Zc hZc
  refine zone_inBoxK (P := S.L ^ (k + 1) * M) (n := n (k + 1)) (r := 8)
    (Nat.mul_pos (pow_pos (Nat.pos_of_ne_zero (NeZero.ne _)) _) (Nat.pos_of_ne_zero (NeZero.ne _)))
    (Balaban.LargeField.fine_eq Hl.F.hnn hk) (by omega) hw (Zc : Set (Torus S.d (n (k + 1))))
    (by omega) (Vsites R (locHist Hl M K (k + 1) Zc) (k + 1)) hV ?_ hcube
  intro x hx
  show cubeMap n S.L M K (k + 1) x ∈
    nbhd 1 (thick ⌊R (k + 1 - 1)⌋₊ (Zcubes (locHist Hl M K (k + 1) Zc) (k + 1)))
  rw [hZ]
  unfold thick
  rw [nbhd_nbhd]
  simp only [Nat.add_sub_cancel]
  exact nbhd_mono (by omega) (Set.Subset.refl _) hx

end Room

end Balaban.RootFSpine
