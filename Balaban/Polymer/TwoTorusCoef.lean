/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Polymer.TwoTorusEv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The coefficients of one zero-class step on two tori

For two step tori `CTorus d L N₁ m₁ K` and `CTorus d L N₁' m₁ K` identified on a centred box by
`boxMap` (`bm`), this file supplies the cover data of the second torus for the comparison of the
energy coefficients of `TwoTorusEv` and `TwoTorusDet`.

## D1: the covering data on two tori

* `mem_Q0_levelGS_iff`: for the whole-lattice set `levelGS K` of the top level the cubes `𝒬₀`
  are the aligned `π'_K`-cubes containing a cube of `𝒦_X`.
* `X1_levelGS_image`: `X₁ = ⋃ 𝒬₀` of the image family `bm '' 𝒦_X` on the second torus is the
  image of `X₁` of `𝒦_X`, when `X₁` and the cubes of `𝒦_X` lie in the box of radius `R`;
  margin `2 R + 5 L · cellSide L m₀ m₁ K < N₁ L^m₁ L^K, N₁' L^m₁ L^K`.
* `covSetup_levelGS_image`, `X1_levelGS_image_of_covSetup`: a covering setup `(X, 𝒦_X)` of the
  first torus with `X₁` in the box goes to the covering setup `(bm '' X, bm '' 𝒦_X)` of the second
  torus, with `X₁` the image.
* `X1_localCover_image`, `covSetup_localCover_image`: the local cover of a site `x`
  (`LocalCover.cube`, `LocalCover.fam`, `LocalCover.nbhdF`) and that of `bm x`; with
  `blockSite_boxMap` this is the cover of the block `B_{k+1}(b)` and of its image block.
-/

@[expose] public section

noncomputable section

open scoped Classical

namespace Balaban.Polymer.TwoTorusStep

open Balaban Balaban.Localization Balaban.Fluctuation Balaban.SmallField Balaban.SmallField.Def6
  Balaban.Polymer Balaban.Multiscale

/-! ### D1: the covering data on two tori -/

section Cover

variable {d L N₁ N₁' m₁ K : ℕ} [NeZero N₁] [NeZero N₁'] [NeZero L] {ϱ : ℝ} {m₀ j : ℕ}

set_option hygiene false in
local notation "bm" => boxMap ((N₁ * L ^ m₁) * L ^ K) ((N₁' * L ^ m₁) * L ^ K)
set_option hygiene false in
local notation "bm'" => boxMap ((N₁' * L ^ m₁) * L ^ K) ((N₁ * L ^ m₁) * L ^ K)
set_option hygiene false in
local notation "GA" => levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) (ϱ := ϱ) K le_rfl
set_option hygiene false in
local notation "GB" => levelGS (d := d) (L := L) (N₁ := N₁') (m₁ := m₁) (k := K) (ϱ := ϱ) K le_rfl

omit [NeZero N₁'] in
/-- Every site lies in the top layer of the whole-lattice set `levelGS K`. -/
theorem mem_layer_levelGS_top (x : CTorus d L N₁ m₁ K) :
    x ∈ ((levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) (ϱ := ϱ) K le_rfl).layer K :
      Set (CTorus d L N₁ m₁ K)) := by
  rw [Finset.mem_coe, layer_levelGS le_rfl]
  simp

omit [NeZero N₁'] in
/-- **The cubes `𝒬₀` of the top level**: the aligned `π'_K`-cubes containing a cube of `𝒦_X`. -/
theorem mem_Q0_levelGS_iff {𝒦X : Set (CTorus d L N₁ m₁ K)} (b : CTorus d L N₁ m₁ K) :
    b ∈ Q0 (GA) m₀ j 𝒦X ↔ Aligned (cellSide L m₀ m₁ K) b ∧
      ∃ q ∈ 𝒦X, box q (L * cellSide L m₀ m₁ j) ⊆ box b (L * cellSide L m₀ m₁ K) :=
  ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, fun x _ => mem_layer_levelGS_top x, h.2⟩⟩

omit [NeZero N₁] [NeZero N₁'] in
theorem cellSide_le_of_le (hj : j ≤ K) : cellSide L m₀ m₁ j ≤ cellSide L m₀ m₁ K := by
  unfold cellSide
  exact Nat.pow_le_pow_right (Nat.pos_of_ne_zero (NeZero.ne L)) (by omega)

/-- **D1: `X₁` of the image family.**  Let the cubes of the family `𝒦_X` (of side `L a_j`,
`j ≤ K`) and the set `X₁ = ⋃ 𝒬₀` of the first torus lie in the box of radius `R`.  Then `X₁` of
the image family `bm '' 𝒦_X` on the second torus is `bm '' X₁`.  A cube `b'` of `𝒬₀` of the
second torus contains the image cube `box (bm q)`, hence lies in the box of radius
`R + 2 L a_K`; its preimage `bm' b'` is a cube of `𝒬₀` of the first torus.  Margin:
`2 R + 5 L a_K < N₁ L^m₁ L^K` and `< N₁' L^m₁ L^K` (`a_K = cellSide L m₀ m₁ K`). -/
theorem X1_levelGS_image (hN : L ^ m₀ ∣ N₁) (hN' : L ^ m₀ ∣ N₁') (hj : j ≤ K) {R : ℕ}
    (hn : 2 * R + 5 * (L * cellSide L m₀ m₁ K) < (N₁ * L ^ m₁) * L ^ K)
    (hn' : 2 * R + 5 * (L * cellSide L m₀ m₁ K) < (N₁' * L ^ m₁) * L ^ K)
    {𝒦X : Set (CTorus d L N₁ m₁ K)}
    (h𝒦 : ∀ q ∈ 𝒦X, ∀ x ∈ box q (L * cellSide L m₀ m₁ j),
      InBox d R ((N₁ * L ^ m₁) * L ^ K) x)
    (hX1 : ∀ x ∈ X1 (GA) m₀ j 𝒦X, InBox d R ((N₁ * L ^ m₁) * L ^ K) x) :
    X1 (GB) m₀ j (bm '' 𝒦X) = bm '' X1 (GA) m₀ j 𝒦X := by
  have hcj := cellSide_le_of_le (L := L) (m₀ := m₀) (m₁ := m₁) hj
  have hLj : L * cellSide L m₀ m₁ j ≤ L * cellSide L m₀ m₁ K := Nat.mul_le_mul_left _ hcj
  have hpK : 0 < L * cellSide L m₀ m₁ K :=
    Nat.mul_pos (Nat.pos_of_ne_zero (NeZero.ne L)) (cellSide_pos m₀ m₁ K)
  have hpj : 0 < L * cellSide L m₀ m₁ j :=
    Nat.mul_pos (Nat.pos_of_ne_zero (NeZero.ne L)) (cellSide_pos m₀ m₁ j)
  have hdA := cellSide_dvd (L := L) (m₁ := m₁) (K := K) hN (le_refl K)
  have hdB := cellSide_dvd (L := L) (m₁ := m₁) (K := K) hN' (le_refl K)
  have himq : ∀ q ∈ 𝒦X, bm '' box q (L * cellSide L m₀ m₁ j) =
      box (bm q) (L * cellSide L m₀ m₁ j) := fun q hq =>
    image_box_boxMap (by omega) hpj (h𝒦 q hq)
  ext x'
  constructor
  · intro hx'
    obtain ⟨b', hb', hx'b'⟩ := Set.mem_iUnion₂.1 hx'
    obtain ⟨hb'al, -, q', ⟨q, hq, rfl⟩, hqb'⟩ := hb'
    have hq0 : InBox d R ((N₁ * L ^ m₁) * L ^ K) q := h𝒦 q hq q (mem_box_self q hpj)
    have hq0' : InBox d R ((N₁' * L ^ m₁) * L ^ K) (bm q) := inBox_boxMap (by omega) hq0
    have hbmq : bm q ∈ box b' (L * cellSide L m₀ m₁ K) := hqb' (mem_box_self _ hpj)
    have hb'R : InBox d (R + L * cellSide L m₀ m₁ K) ((N₁' * L ^ m₁) * L ^ K) b' :=
      inBox_of_mem_box_left (by omega) hq0' hbmq
    have hbox' : ∀ z ∈ box b' (L * cellSide L m₀ m₁ K),
        InBox d (R + L * cellSide L m₀ m₁ K + L * cellSide L m₀ m₁ K)
          ((N₁' * L ^ m₁) * L ^ K) z :=
      fun z hz => inBox_of_mem_box_right (by omega) hb'R hz
    have himb' : bm' '' box b' (L * cellSide L m₀ m₁ K) =
        box (bm' b') (L * cellSide L m₀ m₁ K) :=
      image_box_boxMap (by omega) hpK hbox'
    have hbal : Aligned (cellSide L m₀ m₁ K) (bm' b') := aligned_boxMap hdB hdA hb'al
    have hqb : box q (L * cellSide L m₀ m₁ j) ⊆ box (bm' b') (L * cellSide L m₀ m₁ K) := by
      rw [← himb']
      intro z hz
      refine ⟨bm z, hqb' ?_, boxMap_boxMap (by omega) (h𝒦 q hq z hz)⟩
      rw [← himq q hq]
      exact ⟨z, hz, rfl⟩
    have hbQ : bm' b' ∈ Q0 (GA) m₀ j 𝒦X := (mem_Q0_levelGS_iff _).2 ⟨hbal, q, hq, hqb⟩
    have hbX : box (bm' b') (L * cellSide L m₀ m₁ K) ⊆ X1 (GA) m₀ j 𝒦X :=
      fun z hz => Set.mem_iUnion₂.2 ⟨_, hbQ, hz⟩
    have hbb : bm (bm' b') = b' := boxMap_boxMap (by omega) hb'R
    have himb : bm '' box (bm' b') (L * cellSide L m₀ m₁ K) =
        box (bm (bm' b')) (L * cellSide L m₀ m₁ K) :=
      image_box_boxMap (by omega) hpK fun z hz => hX1 z (hbX hz)
    rw [hbb] at himb
    rw [← himb] at hx'b'
    obtain ⟨x, hx, rfl⟩ := hx'b'
    exact ⟨x, hbX hx, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨b, hb, hxb⟩ := Set.mem_iUnion₂.1 hx
    have hbX : box b (L * cellSide L m₀ m₁ K) ⊆ X1 (GA) m₀ j 𝒦X :=
      fun z hz => Set.mem_iUnion₂.2 ⟨b, hb, hz⟩
    obtain ⟨hbal, q, hq, hqb⟩ := (mem_Q0_levelGS_iff _).1 hb
    have himb : bm '' box b (L * cellSide L m₀ m₁ K) = box (bm b) (L * cellSide L m₀ m₁ K) :=
      image_box_boxMap (by omega) hpK fun z hz => hX1 z (hbX hz)
    refine Set.mem_iUnion₂.2 ⟨bm b, (mem_Q0_levelGS_iff _).2
      ⟨aligned_boxMap hdA hdB hbal, bm q, ⟨q, hq, rfl⟩, ?_⟩, ?_⟩
    · rw [← himq q hq, ← himb]
      exact Set.image_mono hqb
    · rw [← himb]
      exact ⟨x, hxb, rfl⟩

omit [NeZero N₁'] in
/-- The cubes of the family of a covering setup lie in `X₁`. -/
theorem box_subset_X1_of_covSetup {X 𝒦X : Set (CTorus d L N₁ m₁ K)}
    (hcov : CovSetup (GA) m₀ j X 𝒦X) {q : CTorus d L N₁ m₁ K} (hq : q ∈ 𝒦X) :
    box q (L * cellSide L m₀ m₁ j) ⊆ X1 (GA) m₀ j 𝒦X := by
  obtain ⟨b, hbal, hqb, -⟩ := hcov.nest q hq
  exact fun z hz => Set.mem_iUnion₂.2 ⟨b, (mem_Q0_levelGS_iff _).2 ⟨hbal, q, hq, hqb⟩, hqb hz⟩

/-- **D1, `X₁` for a covering setup.**  `X1_levelGS_image` with the cubes of `𝒦_X` inside `X₁`
(`box_subset_X1_of_covSetup`). -/
theorem X1_levelGS_image_of_covSetup (hN' : L ^ m₀ ∣ N₁') {R : ℕ}
    (hn : 2 * R + 5 * (L * cellSide L m₀ m₁ K) < (N₁ * L ^ m₁) * L ^ K)
    (hn' : 2 * R + 5 * (L * cellSide L m₀ m₁ K) < (N₁' * L ^ m₁) * L ^ K)
    {X 𝒦X : Set (CTorus d L N₁ m₁ K)} (hcov : CovSetup (GA) m₀ j X 𝒦X)
    (hX1 : ∀ x ∈ X1 (GA) m₀ j 𝒦X, InBox d R ((N₁ * L ^ m₁) * L ^ K) x) :
    X1 (GB) m₀ j (bm '' 𝒦X) = bm '' X1 (GA) m₀ j 𝒦X :=
  X1_levelGS_image hcov.hN hN' (by have := hcov.hjK; omega) hn hn'
    (fun q hq x hx => hX1 x (box_subset_X1_of_covSetup hcov hq hx)) hX1

/-- **D1, the covering setup of the image.**  A covering setup `(X, 𝒦_X)` of the first torus
whose set `X₁` lies in the box of radius `R` gives the covering setup `(bm '' X, bm '' 𝒦_X)` of
the second torus (`L^{m₀} ∣ N₁'`).  Margin as in `X1_levelGS_image`. -/
theorem covSetup_levelGS_image (hN' : L ^ m₀ ∣ N₁') {R : ℕ}
    (hn : 2 * R + 5 * (L * cellSide L m₀ m₁ K) < (N₁ * L ^ m₁) * L ^ K)
    {X 𝒦X : Set (CTorus d L N₁ m₁ K)} (hcov : CovSetup (GA) m₀ j X 𝒦X)
    (hX1 : ∀ x ∈ X1 (GA) m₀ j 𝒦X, InBox d R ((N₁ * L ^ m₁) * L ^ K) x) :
    CovSetup (GB) m₀ j (bm '' X) (bm '' 𝒦X) := by
  have hj : j ≤ K := by have := hcov.hjK; omega
  have hcj := cellSide_le_of_le (L := L) (m₀ := m₀) (m₁ := m₁) hj
  have hLj : L * cellSide L m₀ m₁ j ≤ L * cellSide L m₀ m₁ K := Nat.mul_le_mul_left _ hcj
  have hpK : 0 < L * cellSide L m₀ m₁ K :=
    Nat.mul_pos (Nat.pos_of_ne_zero (NeZero.ne L)) (cellSide_pos m₀ m₁ K)
  have hdA := cellSide_dvd (L := L) (m₁ := m₁) (K := K) hcov.hN (le_refl K)
  have hdB := cellSide_dvd (L := L) (m₁ := m₁) (K := K) hN' (le_refl K)
  refine ⟨layerUnion_levelGS le_rfl m₀, hN', hcov.hjK, ?_, ?_⟩
  · exact chosenOne_image hcov.hN hN' hj (by omega) (fun x hx => hX1 x (hcov.X_sub hx))
      hcov.chosen
  · rintro _ ⟨b, hb, rfl⟩
    obtain ⟨b₀, hb₀al, hbb₀, -⟩ := hcov.nest b hb
    have hb₀X : box b₀ (L * cellSide L m₀ m₁ K) ⊆ X1 (GA) m₀ j 𝒦X :=
      fun z hz => Set.mem_iUnion₂.2 ⟨b₀, (mem_Q0_levelGS_iff _).2 ⟨hb₀al, b, hb, hbb₀⟩, hz⟩
    have himb₀ : bm '' box b₀ (L * cellSide L m₀ m₁ K) = box (bm b₀) (L * cellSide L m₀ m₁ K) :=
      image_box_boxMap (by omega) hpK fun z hz => hX1 z (hb₀X hz)
    have himb : bm '' box b (L * cellSide L m₀ m₁ j) = box (bm b) (L * cellSide L m₀ m₁ j) :=
      image_box_boxMap (by omega)
        (Nat.mul_pos (Nat.pos_of_ne_zero (NeZero.ne L)) (cellSide_pos m₀ m₁ j))
        fun z hz => hX1 z (hb₀X (hbb₀ hz))
    refine ⟨bm b₀, aligned_boxMap hdA hdB hb₀al, ?_, fun z _ => mem_layer_levelGS_top z⟩
    rw [← himb, ← himb₀]
    exact Set.image_mono hbb₀

end Cover

/-! ### D1 for the local cover of a site and of a block -/

section LocalCoverImage

variable {d L N₁ N₁' m₁ K : ℕ} [NeZero N₁] [NeZero N₁'] [NeZero L] {ϱ : ℝ} {m₀ j : ℕ}

set_option hygiene false in
local notation "bm" => boxMap ((N₁ * L ^ m₁) * L ^ K) ((N₁' * L ^ m₁) * L ^ K)
set_option hygiene false in
local notation "GA" => levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) (ϱ := ϱ) K le_rfl
set_option hygiene false in
local notation "GB" => levelGS (d := d) (L := L) (N₁ := N₁') (m₁ := m₁) (k := K) (ϱ := ϱ) K le_rfl

omit [NeZero N₁] [NeZero N₁'] in
/-- The cell of a site lies in its region `X₁`. -/
theorem cell_subset_nbhd (x : CTorus d L N₁ m₁ K) :
    box (LocalCover.corner m₀ x) (cellSide L m₀ m₁ K) ⊆ LocalCover.nbhd m₀ x :=
  cell_subset_cellNbhd (Nat.pos_of_ne_zero (NeZero.ne L)) _ _

/-- **D1 for the local cover of a site.**  If the region `X₁ = nbhd m₀ x` of the site `x` lies in
the box of radius `R`, the image of the finite region `nbhdF m₀ x` is the region of `bm x`, which
is `X₁` of the local cover of `bm x` on the second torus.  Margin
`2 R + (2 L - 1) a_K < N₁ L^m₁ L^K` (`(L - 1) a_K + L a_K`), `j + 1 ≤ K`. -/
theorem X1_localCover_image (hN : L ^ m₀ ∣ N₁) (hN' : L ^ m₀ ∣ N₁') (hj : j + 1 ≤ K) {R : ℕ}
    (hn : 2 * R + ((L - 1) * cellSide L m₀ m₁ K + L * cellSide L m₀ m₁ K) <
      (N₁ * L ^ m₁) * L ^ K)
    (x : CTorus d L N₁ m₁ K)
    (hbox : ∀ y ∈ LocalCover.nbhd m₀ x, InBox d R ((N₁ * L ^ m₁) * L ^ K) y) :
    (↑((LocalCover.nbhdF m₀ x).image bm) : Set (CTorus d L N₁' m₁ K)) =
      X1 (GB) m₀ j (LocalCover.fam m₀ (bm x)) := by
  have hs : 2 * R + L * cellSide L m₀ m₁ K < (N₁ * L ^ m₁) * L ^ K := by omega
  rw [Finset.coe_image, nbhdF_image hN hN' hs hn x hbox fun y hy => hbox y (cell_subset_nbhd x hy)]
  exact LocalCover.coe_nbhdF_eq_X1 (isLevel_levelGS (by omega) le_rfl) hN' hj (bm x)

/-- The image of the finite region of a site is the finite region of the image site. -/
theorem nbhdF_image_finset (hN : L ^ m₀ ∣ N₁) (hN' : L ^ m₀ ∣ N₁') {R : ℕ}
    (hn : 2 * R + ((L - 1) * cellSide L m₀ m₁ K + L * cellSide L m₀ m₁ K) <
      (N₁ * L ^ m₁) * L ^ K)
    (x : CTorus d L N₁ m₁ K)
    (hbox : ∀ y ∈ LocalCover.nbhd m₀ x, InBox d R ((N₁ * L ^ m₁) * L ^ K) y) :
    (LocalCover.nbhdF m₀ x).image bm = LocalCover.nbhdF m₀ (bm x) := by
  have hs : 2 * R + L * cellSide L m₀ m₁ K < (N₁ * L ^ m₁) * L ^ K := by omega
  apply Finset.coe_injective
  rw [Finset.coe_image]
  exact nbhdF_image hN hN' hs hn x hbox fun y hy => hbox y (cell_subset_nbhd x hy)

/-- **D1, the covering data of the local cover on the second torus** (the premises `hcov'`,
`hX₁'` of `FFmarked_twoTorus`, `evDec_twoTorus`, `Ev_twoTorus`): for the local cover of `x`
(`X = cube m₀ j x`, `𝒦_X = fam m₀ x`, `X₁ = nbhdF m₀ x`) and of `bm x`. -/
theorem covSetup_localCover_image (hN : L ^ m₀ ∣ N₁) (hN' : L ^ m₀ ∣ N₁') (hj : j + 1 ≤ K)
    {R : ℕ}
    (hn : 2 * R + ((L - 1) * cellSide L m₀ m₁ K + L * cellSide L m₀ m₁ K) <
      (N₁ * L ^ m₁) * L ^ K)
    (x : CTorus d L N₁ m₁ K)
    (hbox : ∀ y ∈ LocalCover.nbhd m₀ x, InBox d R ((N₁ * L ^ m₁) * L ^ K) y) :
    CovSetup (GA) m₀ j (LocalCover.cube m₀ j x) (LocalCover.fam m₀ x) ∧
      (↑(LocalCover.nbhdF m₀ x) : Set (CTorus d L N₁ m₁ K)) =
        X1 (GA) m₀ j (LocalCover.fam m₀ x) ∧
      CovSetup (GB) m₀ j (LocalCover.cube m₀ j (bm x)) (LocalCover.fam m₀ (bm x)) ∧
      (↑((LocalCover.nbhdF m₀ x).image bm) : Set (CTorus d L N₁' m₁ K)) =
        X1 (GB) m₀ j (LocalCover.fam m₀ (bm x)) :=
  ⟨LocalCover.covSetup (isLevel_levelGS (by omega) le_rfl) hN hj x,
    LocalCover.coe_nbhdF_eq_X1 (isLevel_levelGS (by omega) le_rfl) hN hj x,
    LocalCover.covSetup (isLevel_levelGS (by omega) le_rfl) hN' hj (bm x),
    X1_localCover_image hN hN' hj hn x hbox⟩

end LocalCoverImage

end Balaban.Polymer.TwoTorusStep
