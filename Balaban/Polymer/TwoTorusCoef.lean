/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Polymer.TwoTorusEv
public import Balaban.Fluctuation.DecMarkCorrected
public import Balaban.Inhabited.LevelStepSettingGeneral
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
  Balaban.Background Balaban.Analysis
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

/-! ### D2: the root block, its masks and its hat variables on two tori -/

section RootBlock

variable {d L N₁ N₁' m₁ k N : ℕ} [NeZero N₁] [NeZero N₁'] [NeZero L] {ϱ : ℝ}

set_option hygiene false in
local notation "bm" => boxMap ((N₁ * L ^ m₁) * L ^ (k + 1)) ((N₁' * L ^ m₁) * L ^ (k + 1))
set_option hygiene false in
local notation "bc" => boxMap (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1)))
  (N₁' * L ^ m₁ * L ^ (k + 1 - (k + 1)))
set_option hygiene false in
local notation "GA" => levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ)
  (k + 1) le_rfl
set_option hygiene false in
local notation "GB" => levelGS (d := d) (L := L) (N₁ := N₁') (m₁ := m₁) (k := k + 1) (ϱ := ϱ)
  (k + 1) le_rfl
set_option hygiene false in
local notation "HA" => levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ)
  k (Nat.le_succ k)
set_option hygiene false in
local notation "HB" => levelGS (d := d) (L := L) (N₁ := N₁') (m₁ := m₁) (k := k + 1) (ϱ := ϱ)
  k (Nat.le_succ k)
set_option hygiene false in
local notation "ρ₁" => R + (3 * L ^ (k + 1 + m₁) + 3 * L ^ (k + 1 + 2)) + L ^ (k + 1 + m₁)

omit [NeZero N₁'] in
/-- **D2 (b): the premises of the root block.**  For the block `B_{k+1}(b)` with corner site
`x_b = blockSite k b` and the region `X₁ = nbhdF m₀ x_b` of its local cover (`m₀ ≥ 1`), the sites
read by the block energy lie in `X₁`, and the block has the margin `BlockMargin` against `X₁`
(`LocalCover.readSites_subset_nbhdF`, `LocalCover.blockMargin`).  These are the premises `hZ`,
`hBM` of `evDec_blockEnergy_twoTorus` (the same-torus analogue is `evDec_local_rawY`). -/
theorem rootBlock_premises {a : ℕ → ℝ} {ν : ℝ} (S : DGSetting (GA) a ν) {m₀ : ℕ} (hm₀ : 1 ≤ m₀)
    (b : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1)))) :
    readSites (HA) k (jBlock d L (N₁ * L ^ m₁) (k + 1) (k + 1) (LocalCover.blockSite k b)) ⊆
        ↑(LocalCover.nbhdF m₀ (LocalCover.blockSite k b)) ∧
      BlockMargin (GA) (LocalCover.nbhdF m₀ (LocalCover.blockSite k b))
        (↑(blockSites d L N₁ m₁ (k + 1) k
          (jBlock d L (N₁ * L ^ m₁) (k + 1) (k + 1) (LocalCover.blockSite k b))) :
          Set (CTorus d L N₁ m₁ (k + 1))) := by
  rw [LocalCover.jBlock_blockSite le_rfl b]
  exact ⟨LocalCover.readSites_subset_nbhdF (HA) (by have := S.hL; omega) m₀ le_rfl b,
    LocalCover.blockMargin S (isLevel_levelGS (Nat.le_add_left 1 k) le_rfl) hm₀ _
      (LocalCover.blockSites_subset_cell m₀ le_rfl b)⟩

/-- **D2 (c): the root mask on two tori.**  The unit point of a site `x` of the box lies in the
unit points of the block `B_{k+1}(x₀)` (the mask `blockU` of the root `jBlock x₀`) iff the unit
point of `bm x` lies in those of the block of `bm x₀` (`unitBlock1_unitBlock`,
`jBlock_boxMap_iff`).  Margin: `2 ρ + 3 L^(k+1) + 5 < N₁ L^m₁ L^(k+1), N₁' L^m₁ L^(k+1)`. -/
theorem rootMask_boxMap {ρ : ℕ} (hn : 2 * ρ + 3 * L ^ (k + 1) + 5 < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hn' : 2 * ρ + 3 * L ^ (k + 1) + 5 < (N₁' * L ^ m₁) * L ^ (k + 1))
    (hGA : IsLevel (GA) (k + 1)) (hGB : IsLevel (GB) (k + 1)) {x₀ x : CTorus d L N₁ m₁ (k + 1)}
    (hx₀ : InBox d ρ ((N₁ * L ^ m₁) * L ^ (k + 1)) x₀)
    (hx : InBox d ρ ((N₁ * L ^ m₁) * L ^ (k + 1)) x) :
    unitPt hGB (bm x) ∈ (Finset.univ.filter fun u : unitPts (GB) =>
        unitBlock1 (u : UnitTorus d L N₁' m₁ k) =
          jBlock d L (N₁' * L ^ m₁) (k + 1) (k + 1) (bm x₀)) ↔
      unitPt hGA x ∈ (Finset.univ.filter fun u : unitPts (GA) =>
        unitBlock1 (u : UnitTorus d L N₁ m₁ k) = jBlock d L (N₁ * L ^ m₁) (k + 1) (k + 1) x₀) := by
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  show unitBlock1 (unitBlock (bm x)) = _ ↔ unitBlock1 (unitBlock x) = _
  rw [unitBlock1_unitBlock, unitBlock1_unitBlock]
  exact (jBlock_boxMap_iff le_rfl hn hn' hx hx₀).symm

/-- **D2 (c): the root mask of a coarse root on two tori.**  `rootMask_boxMap` for the root `z`
of the first torus (`|z| ≤ r_c`, `L^(k+1) r_c ≤ ρ`) and its image `bc z`: the masks are
`blockU z` and `blockU (bc z)` (written as the filters that define `StepSetting.blockU`). -/
theorem rootMask_bc {ρ rc : ℕ}
    (hn : 2 * ρ + 3 * L ^ (k + 1) + 5 < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hn' : 2 * ρ + 3 * L ^ (k + 1) + 5 < (N₁' * L ^ m₁) * L ^ (k + 1))
    (hGA : IsLevel (GA) (k + 1)) (hGB : IsLevel (GB) (k + 1))
    (z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))))
    (hz : InBox d rc (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) z) (hrc : L ^ (k + 1) * rc ≤ ρ)
    {x : CTorus d L N₁ m₁ (k + 1)} (hx : InBox d ρ ((N₁ * L ^ m₁) * L ^ (k + 1)) x) :
    unitPt hGB (bm x) ∈ (Finset.univ.filter fun u : unitPts (GB) =>
        unitBlock1 (u : UnitTorus d L N₁' m₁ k) = bc z) ↔
      unitPt hGA x ∈ (Finset.univ.filter fun u : unitPts (GA) =>
        unitBlock1 (u : UnitTorus d L N₁ m₁ k) = z) := by
  have hs : 2 * ρ + 1 < (N₁ * L ^ m₁) * L ^ (k + 1) := by omega
  have hbs : LocalCover.blockSite k (bc z) = bm (LocalCover.blockSite k z) :=
    blockSite_boxMap le_rfl z hz hrc hs
  have hx₀ : InBox d ρ ((N₁ * L ^ m₁) * L ^ (k + 1)) (LocalCover.blockSite k z) := by
    intro μ
    have h1 : |(z μ).valMinAbs| ≤ rc := hz μ
    have e : (LocalCover.blockSite k z μ) =
        ((((L ^ (k + 1) : ℕ) : ℤ) * (z μ).valMinAbs : ℤ) : ZMod ((N₁ * L ^ m₁) * L ^ (k + 1))) := by
      have hzμ : z μ = (((z μ).valMinAbs : ℤ) : ZMod (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1)))) :=
        (ZMod.coe_valMinAbs _).symm
      show ((L ^ (k + 1) * (z μ).val : ℕ) : ZMod ((N₁ * L ^ m₁) * L ^ (k + 1))) = _
      conv_lhs => rw [hzμ]
      exact rootCoord_intCast (side_eq (N₀ := N₁ * L ^ m₁) (L := L) (le_refl (k + 1))) _
    have h2 : |((L ^ (k + 1) : ℕ) : ℤ) * (z μ).valMinAbs| ≤ ρ := by
      rw [abs_mul, Nat.abs_cast]
      have h3 : ((L ^ (k + 1) : ℕ) : ℤ) * |(z μ).valMinAbs| ≤ ((L ^ (k + 1) : ℕ) : ℤ) * rc :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
      have h4 : ((L ^ (k + 1) * rc : ℕ) : ℤ) ≤ ρ := by exact_mod_cast hrc
      push_cast at h3 h4 ⊢
      linarith
    rw [e, valMinAbs_intCast_of_abs_le hs h2]
    exact h2
  have h := rootMask_boxMap hn hn' hGA hGB hx₀ hx
  rw [← hbs, LocalCover.jBlock_blockSite le_rfl, LocalCover.jBlock_blockSite le_rfl] at h
  exact h

/-- **D2/D3: the marked energy coefficient of the root block on two tori.**  The block `B_{k+1}(b)`
of the first torus (`|b| ≤ r_c` in centred coarse coordinates, `L^(k+1) r_c ≤ R`) and its image
block `bc b` of the second torus, with their local covers (`X = cube m₀ k`, `𝒦_X = fam m₀`,
`X₁ = nbhdF m₀` of the corner sites `blockSite k b` and `blockSite k (bc b) = bm (blockSite k b)`):
if the region `X₁` of the block and the domain `Y` lie in the box of radius `R`, the coefficients
`evDec` of the block energy of `bc b` at `bm '' Y` and of `b` at `Y` are equal.  This is
`evDec_blockEnergy_twoTorus` with its premises `hcov`, `hX₁`, `hcov'`, `hX₁'`
(`covSetup_localCover_image`), `hZ` and `hBM` (`rootBlock_premises`) discharged; the hat variables
and the masks are corresponding (`hhat`, `hZm`; for the root masks see `rootMask_boxMap`, for the
hat variables of the block variables `hatOf_boxMap`).  Margins as in `evDec_twoTorus`, with `R`
bounding `X₁ ∪ Y`. -/
theorem evDec_rootBlock_twoTorus
    {a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁ : ℝ}
    (hC : FlCore N (GA) (HA) a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
    (hC' : FlCore N (GB) (HB) a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁) (hk : 1 ≤ k)
    (hGA : IsLevel (GA) (k + 1)) (hGB : IsLevel (GB) (k + 1)) (cc : ℂ) {cψ : ℝ} (hcψ : 0 ≤ cψ)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δc : ℝ}
    (hmar : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hαK : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    {F₁ : DecParams (GA) × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      ((GA).Ω 1 × Fin N → ℂ) × ((GA).Ω 1 → ℂ)}
    {F₁' : DecParams (GB) × RawData d L (N₁' * L ^ m₁) (k + 1) N →
      ((GB).Ω 1 × Fin N → ℂ) × ((GB).Ω 1 → ℂ)}
    (hF₁ : ∀ (s : DecParams (GA)) (D : BgData (GA) N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC (GA) (bgC0 d L N) (c7 d L N BG κ) ν D → ∀ (φ : (GA).Ω 1 × Fin N → ℂ)
        (α : (GA).Ω 1 → ℂ), IsDecBg (GA) (compWeight L a₁) ν (rho4 d L N BG κ) s D φ α →
        F₁ (s, rawOf D) = (φ, α))
    (hF₁' : ∀ (s : DecParams (GB)) (D : BgData (GB) N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC (GB) (bgC0 d L N) (c7 d L N BG κ) ν D → ∀ (φ : (GB).Ω 1 × Fin N → ℂ)
        (α : (GB).Ω 1 → ℂ), IsDecBg (GB) (compWeight L a₁) ν (rho4 d L N BG κ) s D φ α →
        F₁' (s, rawOf D) = (φ, α))
    {Sol : Dec2.DecParams (coverOf (GA)) × Edat (HA) N → ((HA).Ω 1 × Fin N → ℂ) × ((HA).Ω 1 → ℂ)}
    {Sol' : Dec2.DecParams (coverOf (GB)) × Edat (HB) N →
      ((HB).Ω 1 × Fin N → ℂ) × ((HB).Ω 1 → ℂ)}
    (hSol : ∀ p : Dec2.DecParams (coverOf (GA)) × Edat (HA) N, (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM (HA) N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2 →
        (Sol p).1 = dphi (HA) (Dec2.decG (coverOf (GA)) (HA) (compWeight L a₁) ν p.1) p.2.2.1
          p.2.1 (pertSource (HA) (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol p).2 ∧
        Dec2.DecFixed (coverOf (GA)) (HA) (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
          (pertSource (HA) (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol p).2 ∧
        Small (HA) (Sol p).2 (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
        Small (HA) (Sol p).2 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        SupBounds (HA) (Sol p).1 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        (∀ δα' : (HA).Ω 1 → ℂ, Small (HA) δα' (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf (GA)) (HA) (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
            (pertSource (HA) (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol p).2))
    (hSol' : ∀ p : Dec2.DecParams (coverOf (GB)) × Edat (HB) N, (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM (HB) N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2 →
        (Sol' p).1 = dphi (HB) (Dec2.decG (coverOf (GB)) (HB) (compWeight L a₁) ν p.1) p.2.2.1
          p.2.1 (pertSource (HB) (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol' p).2 ∧
        Dec2.DecFixed (coverOf (GB)) (HB) (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
          (pertSource (HB) (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol' p).2 ∧
        Small (HB) (Sol' p).2 (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
        Small (HB) (Sol' p).2 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        SupBounds (HB) (Sol' p).1 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        (∀ δα' : (HB).Ω 1 → ℂ, Small (HB) δα' (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf (GB)) (HB) (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
            (pertSource (HB) (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol' p).2))
    {m₀ : ℕ} (hm₀ : 1 ≤ m₀) (hN : L ^ m₀ ∣ N₁) (hN' : L ^ m₀ ∣ N₁')
    (b : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1)))) {rc R : ℕ}
    (hb : InBox d rc (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) b) (hrc : L ^ (k + 1) * rc ≤ R)
    (hX₁R : ∀ x ∈ LocalCover.nbhd m₀ (LocalCover.blockSite k b),
      InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x)
    {Y : Set (CTorus d L N₁ m₁ (k + 1))}
    (hYR : ∀ y ∈ Y, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) y)
    (hn : 4 * R + 12 * L ^ (k + 1 + m₁) + 7 * L ^ (k + 1) + 5 < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hn' : 4 * R + 12 * L ^ (k + 1 + m₁) + 7 * L ^ (k + 1) + 5 < (N₁' * L ^ m₁) * L ^ (k + 1))
    (hnS : 2 * (ρ₁) + 5 * (L * cellSide L 0 m₁ (k + 1)) < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hnS' : 2 * (ρ₁) + 5 * (L * cellSide L 0 m₁ (k + 1)) < (N₁' * L ^ m₁) * L ^ (k + 1))
    (hnF : 2 * R + 5 * (L * cellSide L m₀ m₁ (k + 1)) < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hnF' : 2 * R + 5 * (L * cellSide L m₀ m₁ (k + 1)) < (N₁' * L ^ m₁) * L ^ (k + 1))
    {D : BgData (GA) N} {D' : BgData (GB) N}
    (hD : XiCData (GA) (compWeight L a₁) ν (k + 1) 1 eps D)
    (hD' : XiCData (GB) (compWeight L a₁) ν (k + 1) 1 eps D')
    (hraw : RawBoxAgree {z | InBox d (R + 3 * L ^ (k + 1)) ((N₁ * L ^ m₁) * L ^ (k + 1)) z}
      (rawOf D) (rawOf D'))
    {ψh : unitPts (GA) × Fin N → ℂ} {ψh' : unitPts (GB) × Fin N → ℂ}
    (hψh : ∀ p, ‖ψh p‖ ≤ cψ) (hψh' : ∀ p, ‖ψh' p‖ ≤ cψ)
    (hhat : ∀ x, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x →
      ∀ i, ψh' (unitPt hGB (bm x), i) = ψh (unitPt hGA x, i))
    {Zm : Finset (unitPts (GA))} {Zm' : Finset (unitPts (GB))}
    (hZm : ∀ x, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x →
      (unitPt hGB (bm x) ∈ Zm' ↔ unitPt hGA x ∈ Zm))
    {um tm : ℂ} (hum : (‖um‖ + ‖tm‖) * markedRad d L N k a₁ κ cψ cc < δ₁) :
    evDec (LocalCover.nbhdF m₀ (LocalCover.blockSite k (bc b))) m₀ k
        (LocalCover.fam m₀ (LocalCover.blockSite k (bc b))) a₁ ν hGB cc F₁' Sol'
        (blockEnergyFun (GB) (HB) (compWeight L a₁) ν k (bc b)) Zm' um tm (bm '' Y)
        (rawOf D', ψh') =
      evDec (LocalCover.nbhdF m₀ (LocalCover.blockSite k b)) m₀ k
        (LocalCover.fam m₀ (LocalCover.blockSite k b)) a₁ ν hGA cc F₁ Sol
        (blockEnergyFun (GA) (HA) (compWeight L a₁) ν k b) Zm um tm Y (rawOf D, ψh) := by
  have hcs : (L - 1) * cellSide L m₀ m₁ (k + 1) ≤ L * cellSide L m₀ m₁ (k + 1) :=
    Nat.mul_le_mul_right _ (Nat.sub_le L 1)
  have hbs : LocalCover.blockSite k (bc b) = bm (LocalCover.blockSite k b) :=
    blockSite_boxMap le_rfl b hb hrc (by omega)
  have hjb' : jBlock d L (N₁' * L ^ m₁) (k + 1) (k + 1) (bm (LocalCover.blockSite k b)) = bc b := by
    rw [← hbs]; exact LocalCover.jBlock_blockSite le_rfl (bc b)
  obtain ⟨hcov, hX₁, hcov', hX₁'⟩ := covSetup_localCover_image (ϱ := ϱ) hN hN' (j := k) le_rfl
    (R := R) (by omega) (LocalCover.blockSite k b) hX₁R
  have hF := nbhdF_image_finset hN hN' (R := R) (by omega) (LocalCover.blockSite k b) hX₁R
  obtain ⟨hZ, hBM⟩ := rootBlock_premises hC.Sp hm₀ b
  have hXR : ∀ x ∈ LocalCover.nbhdF m₀ (LocalCover.blockSite k b),
      InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x := fun x hx =>
    hX₁R x (by rw [← LocalCover.coe_nbhdF]; exact hx)
  have h := evDec_blockEnergy_twoTorus hC hC' hk hGA hGB cc hcψ hMX hmar hαK hsm hF₁ hF₁' hSol
    hSol' hcov hX₁ hcov' hX₁' hZ hBM hXR hYR hn hn' hnS hnS' hnF hnF' hD hD' hraw hψh hψh' hhat
    hZm hum
  rw [LocalCover.jBlock_blockSite le_rfl b, hjb', hF] at h
  rw [hbs]
  exact h


end RootBlock

/-! ### D3: the marks of the energy coefficient on two tori -/

section Marks

open Balaban.Inhabited.LevelStep

variable {d L N₁ N₁' m₁ k N : ℕ} [NeZero N₁] [NeZero N₁'] [NeZero L] {ϱ : ℝ}

set_option hygiene false in
local notation "bm" => boxMap ((N₁ * L ^ m₁) * L ^ (k + 1)) ((N₁' * L ^ m₁) * L ^ (k + 1))
set_option hygiene false in
local notation "bc" => boxMap (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1)))
  (N₁' * L ^ m₁ * L ^ (k + 1 - (k + 1)))
set_option hygiene false in
local notation "GA" => levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ)
  (k + 1) le_rfl
set_option hygiene false in
local notation "GB" => levelGS (d := d) (L := L) (N₁ := N₁') (m₁ := m₁) (k := k + 1) (ϱ := ϱ)
  (k + 1) le_rfl
set_option hygiene false in
local notation "HA" => levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ)
  k (Nat.le_succ k)
set_option hygiene false in
local notation "HB" => levelGS (d := d) (L := L) (N₁ := N₁') (m₁ := m₁) (k := k + 1) (ϱ := ϱ)
  k (Nat.le_succ k)
set_option hygiene false in
local notation "ρ₁" => R + (3 * L ^ (k + 1 + m₁) + 3 * L ^ (k + 1 + 2)) + L ^ (k + 1 + m₁)
set_option hygiene false in
local notation "SA" => hatStepKG (d := d) (L := L) (N := N) (N₁ := N₁) hN2 k m₁ ϱ hk νS β p₁ δ
set_option hygiene false in
local notation "SB" => hatStepKG (d := d) (L := L) (N := N) (N₁ := N₁') hN2 k m₁ ϱ hk νS β p₁ δ

/-- **D2 (c): the hat variables of the block variables on two tori.**  For the steps `hatStepKG`
on `N₁` and `N₁'`, if the block variables `Φ`, `Φ'` agree at the unit points of corresponding
sites of the box (each read in its `π_{k+1}`-cube, `cellOf`), the clamped hat variables `hatOf`
agree there: this is the premise `hhat` of `evDec_twoTorus` for `ψ̂ = hatOf … Φ`. -/
theorem hatOf_boxMap (hGA : IsLevel (GA) (k + 1)) (hGB : IsLevel (GB) (k + 1)) (hN2 : 2 ≤ N)
    (hk : 1 ≤ k) (νS β p₁ δ : ℝ) (m₀ : ℕ) (ρ : ℝ) (hp : 0 < (SA).p₁) (hp' : 0 < (SB).p₁)
    (Φ : ∀ c, ((SA).blockSplit m₀ hp).Ωb c) (Φ' : ∀ c, ((SB).blockSplit m₀ hp').Ωb c) {R : ℕ}
    (hΦ : ∀ x, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x →
      Φ' ((SB).cellOf m₀ (unitPt hGB (bm x))) ⟨unitPt hGB (bm x), rfl⟩ =
        Φ ((SA).cellOf m₀ (unitPt hGA x)) ⟨unitPt hGA x, rfl⟩) :
    ∀ x, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x → ∀ i,
      (SB).hatOf m₀ ρ hp' Φ' (unitPt hGB (bm x), i) = (SA).hatOf m₀ ρ hp Φ (unitPt hGA x, i) := by
  intro x hx i
  simp only [StepSetting.hatOf]
  rw [hΦ x hx]

/-- **D3: the block-level decoupled mark of the root block on two tori.**  The `t`-derivative at `0`
of `evDec` (the mark `decMarkG` of the steps `hatStepKG` on `N₁` and `N₁'`, at the clamped hat
variables `hatOf` of block variables `Φ`, `Φ'` agreeing at corresponding unit points of the box)
is the same for the block `b` at the label `Y` and for `bc b` at `bm '' Y`, for every first mark
`um` with `‖um‖ · markedRad < δ₁` (the radius of the hat variables is the clamp radius `ρ`):
`evDec_rootBlock_twoTorus` holds for every `t` near `0`. -/
theorem decMarkG_rootBlock_twoTorus
    {a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁ : ℝ}
    (hC : FlCore N (GA) (HA) a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
    (hC' : FlCore N (GB) (HB) a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁) (hk : 1 ≤ k)
    (hGA : IsLevel (GA) (k + 1)) (hGB : IsLevel (GB) (k + 1)) (cc : ℂ)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δc : ℝ}
    (hmar : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hαK : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    {F₁ : DecParams (GA) × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      ((GA).Ω 1 × Fin N → ℂ) × ((GA).Ω 1 → ℂ)}
    {F₁' : DecParams (GB) × RawData d L (N₁' * L ^ m₁) (k + 1) N →
      ((GB).Ω 1 × Fin N → ℂ) × ((GB).Ω 1 → ℂ)}
    (hF₁ : ∀ (s : DecParams (GA)) (D : BgData (GA) N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC (GA) (bgC0 d L N) (c7 d L N BG κ) ν D → ∀ (φ : (GA).Ω 1 × Fin N → ℂ)
        (α : (GA).Ω 1 → ℂ), IsDecBg (GA) (compWeight L a₁) ν (rho4 d L N BG κ) s D φ α →
        F₁ (s, rawOf D) = (φ, α))
    (hF₁' : ∀ (s : DecParams (GB)) (D : BgData (GB) N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC (GB) (bgC0 d L N) (c7 d L N BG κ) ν D → ∀ (φ : (GB).Ω 1 × Fin N → ℂ)
        (α : (GB).Ω 1 → ℂ), IsDecBg (GB) (compWeight L a₁) ν (rho4 d L N BG κ) s D φ α →
        F₁' (s, rawOf D) = (φ, α))
    {Sol : Dec2.DecParams (coverOf (GA)) × Edat (HA) N → ((HA).Ω 1 × Fin N → ℂ) × ((HA).Ω 1 → ℂ)}
    {Sol' : Dec2.DecParams (coverOf (GB)) × Edat (HB) N →
      ((HB).Ω 1 × Fin N → ℂ) × ((HB).Ω 1 → ℂ)}
    (hSol : ∀ p : Dec2.DecParams (coverOf (GA)) × Edat (HA) N, (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM (HA) N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2 →
        (Sol p).1 = dphi (HA) (Dec2.decG (coverOf (GA)) (HA) (compWeight L a₁) ν p.1) p.2.2.1
          p.2.1 (pertSource (HA) (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol p).2 ∧
        Dec2.DecFixed (coverOf (GA)) (HA) (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
          (pertSource (HA) (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol p).2 ∧
        Small (HA) (Sol p).2 (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
        Small (HA) (Sol p).2 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        SupBounds (HA) (Sol p).1 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        (∀ δα' : (HA).Ω 1 → ℂ, Small (HA) δα' (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf (GA)) (HA) (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
            (pertSource (HA) (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol p).2))
    (hSol' : ∀ p : Dec2.DecParams (coverOf (GB)) × Edat (HB) N, (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM (HB) N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2 →
        (Sol' p).1 = dphi (HB) (Dec2.decG (coverOf (GB)) (HB) (compWeight L a₁) ν p.1) p.2.2.1
          p.2.1 (pertSource (HB) (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol' p).2 ∧
        Dec2.DecFixed (coverOf (GB)) (HB) (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
          (pertSource (HB) (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol' p).2 ∧
        Small (HB) (Sol' p).2 (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
        Small (HB) (Sol' p).2 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        SupBounds (HB) (Sol' p).1 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        (∀ δα' : (HB).Ω 1 → ℂ, Small (HB) δα' (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf (GB)) (HB) (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
            (pertSource (HB) (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol' p).2))
    {m₀ : ℕ} (hm₀ : 1 ≤ m₀) (hN : L ^ m₀ ∣ N₁) (hN' : L ^ m₀ ∣ N₁')
    (b : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1)))) {rc R : ℕ}
    (hb : InBox d rc (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) b) (hrc : L ^ (k + 1) * rc ≤ R)
    (hX₁R : ∀ x ∈ LocalCover.nbhd m₀ (LocalCover.blockSite k b),
      InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x)
    {Y : Set (CTorus d L N₁ m₁ (k + 1))}
    (hYR : ∀ y ∈ Y, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) y)
    (hn : 4 * R + 12 * L ^ (k + 1 + m₁) + 7 * L ^ (k + 1) + 5 < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hn' : 4 * R + 12 * L ^ (k + 1 + m₁) + 7 * L ^ (k + 1) + 5 < (N₁' * L ^ m₁) * L ^ (k + 1))
    (hnS : 2 * (ρ₁) + 5 * (L * cellSide L 0 m₁ (k + 1)) < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hnS' : 2 * (ρ₁) + 5 * (L * cellSide L 0 m₁ (k + 1)) < (N₁' * L ^ m₁) * L ^ (k + 1))
    (hnF : 2 * R + 5 * (L * cellSide L m₀ m₁ (k + 1)) < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hnF' : 2 * R + 5 * (L * cellSide L m₀ m₁ (k + 1)) < (N₁' * L ^ m₁) * L ^ (k + 1))
    {D : BgData (GA) N} {D' : BgData (GB) N}
    (hD : XiCData (GA) (compWeight L a₁) ν (k + 1) 1 eps D)
    (hD' : XiCData (GB) (compWeight L a₁) ν (k + 1) 1 eps D')
    (hraw : RawBoxAgree {z | InBox d (R + 3 * L ^ (k + 1)) ((N₁ * L ^ m₁) * L ^ (k + 1)) z}
      (rawOf D) (rawOf D'))
    (hN2 : 2 ≤ N) (νS β p₁ δ : ℝ) {ρ : ℝ} (hρ : 0 < ρ)
    (hp : 0 < (SA).p₁) (hp' : 0 < (SB).p₁)
    (Φ : ∀ c, ((SA).blockSplit m₀ hp).Ωb c) (Φ' : ∀ c, ((SB).blockSplit m₀ hp').Ωb c)
    (hΦ : ∀ x, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x →
      Φ' ((SB).cellOf m₀ (unitPt hGB (bm x))) ⟨unitPt hGB (bm x), rfl⟩ =
        Φ ((SA).cellOf m₀ (unitPt hGA x)) ⟨unitPt hGA x, rfl⟩)
    {Zm : Finset (unitPts (GA))} {Zm' : Finset (unitPts (GB))}
    (hZm : ∀ x, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x →
      (unitPt hGB (bm x) ∈ Zm' ↔ unitPt hGA x ∈ Zm))
    {um : ℂ} (hum : ‖um‖ * markedRad d L N k a₁ κ ρ cc < δ₁) :
    decMarkG (SB) (LocalCover.nbhdF m₀ (LocalCover.blockSite k (bc b))) m₀ k
        (LocalCover.fam m₀ (LocalCover.blockSite k (bc b))) a₁ ν cc F₁' Sol'
        (blockEnergyFun (GB) (HB) (compWeight L a₁) ν k (bc b)) Zm' (bm '' Y) ρ hp' (rawOf D') um Φ' =
      decMarkG (SA) (LocalCover.nbhdF m₀ (LocalCover.blockSite k b)) m₀ k
        (LocalCover.fam m₀ (LocalCover.blockSite k b)) a₁ ν cc F₁ Sol
        (blockEnergyFun (GA) (HA) (compWeight L a₁) ν k b) Zm Y ρ hp (rawOf D) um Φ := by
  unfold decMarkG
  refine Filter.EventuallyEq.deriv_eq ?_
  have hopen : IsOpen {t : ℂ | (‖um‖ + ‖t‖) * markedRad d L N k a₁ κ ρ cc < δ₁} :=
    isOpen_lt (by fun_prop) continuous_const
  have h0 : (0 : ℂ) ∈ {t : ℂ | (‖um‖ + ‖t‖) * markedRad d L N k a₁ κ ρ cc < δ₁} := by
    simpa using hum
  filter_upwards [hopen.mem_nhds h0] with t ht
  exact evDec_rootBlock_twoTorus hC hC' hk hGA hGB cc hρ.le hMX hmar hαK hsm hF₁ hF₁' hSol hSol'
    hm₀ hN hN' b hb hrc hX₁R hYR hn hn' hnS hnS' hnF hnF' hD hD' hraw
    (fun p => (SA).hatOf_mem m₀ hρ hp Φ p) (fun p => (SB).hatOf_mem m₀ hρ hp' Φ' p)
    (hatOf_boxMap hGA hGB hN2 hk νS β p₁ δ m₀ ρ hp hp' Φ Φ' hΦ) hZm ht

/-- **D3: the corrected mark of the root block on two tori** (`decMarkCorr`, the first-order Taylor
remainder in the first mark of `decMarkG`, which enters the energy coefficient through
`decMarkCorrTerm` and `markedOutDec`): equal for the block `b` at the label `Y` and for `bc b` at
`bm '' Y`, by `decMarkG_rootBlock_twoTorus` at `um`, at `0` and near `0`. -/
theorem decMarkCorr_rootBlock_twoTorus
    {a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁ : ℝ}
    (hC : FlCore N (GA) (HA) a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
    (hC' : FlCore N (GB) (HB) a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁) (hk : 1 ≤ k)
    (hGA : IsLevel (GA) (k + 1)) (hGB : IsLevel (GB) (k + 1)) (cc : ℂ)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δc : ℝ}
    (hmar : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hαK : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    {F₁ : DecParams (GA) × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      ((GA).Ω 1 × Fin N → ℂ) × ((GA).Ω 1 → ℂ)}
    {F₁' : DecParams (GB) × RawData d L (N₁' * L ^ m₁) (k + 1) N →
      ((GB).Ω 1 × Fin N → ℂ) × ((GB).Ω 1 → ℂ)}
    (hF₁ : ∀ (s : DecParams (GA)) (D : BgData (GA) N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC (GA) (bgC0 d L N) (c7 d L N BG κ) ν D → ∀ (φ : (GA).Ω 1 × Fin N → ℂ)
        (α : (GA).Ω 1 → ℂ), IsDecBg (GA) (compWeight L a₁) ν (rho4 d L N BG κ) s D φ α →
        F₁ (s, rawOf D) = (φ, α))
    (hF₁' : ∀ (s : DecParams (GB)) (D : BgData (GB) N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC (GB) (bgC0 d L N) (c7 d L N BG κ) ν D → ∀ (φ : (GB).Ω 1 × Fin N → ℂ)
        (α : (GB).Ω 1 → ℂ), IsDecBg (GB) (compWeight L a₁) ν (rho4 d L N BG κ) s D φ α →
        F₁' (s, rawOf D) = (φ, α))
    {Sol : Dec2.DecParams (coverOf (GA)) × Edat (HA) N → ((HA).Ω 1 × Fin N → ℂ) × ((HA).Ω 1 → ℂ)}
    {Sol' : Dec2.DecParams (coverOf (GB)) × Edat (HB) N →
      ((HB).Ω 1 × Fin N → ℂ) × ((HB).Ω 1 → ℂ)}
    (hSol : ∀ p : Dec2.DecParams (coverOf (GA)) × Edat (HA) N, (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM (HA) N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2 →
        (Sol p).1 = dphi (HA) (Dec2.decG (coverOf (GA)) (HA) (compWeight L a₁) ν p.1) p.2.2.1
          p.2.1 (pertSource (HA) (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol p).2 ∧
        Dec2.DecFixed (coverOf (GA)) (HA) (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
          (pertSource (HA) (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol p).2 ∧
        Small (HA) (Sol p).2 (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
        Small (HA) (Sol p).2 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        SupBounds (HA) (Sol p).1 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        (∀ δα' : (HA).Ω 1 → ℂ, Small (HA) δα' (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf (GA)) (HA) (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
            (pertSource (HA) (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol p).2))
    (hSol' : ∀ p : Dec2.DecParams (coverOf (GB)) × Edat (HB) N, (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM (HB) N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2 →
        (Sol' p).1 = dphi (HB) (Dec2.decG (coverOf (GB)) (HB) (compWeight L a₁) ν p.1) p.2.2.1
          p.2.1 (pertSource (HB) (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol' p).2 ∧
        Dec2.DecFixed (coverOf (GB)) (HB) (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
          (pertSource (HB) (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol' p).2 ∧
        Small (HB) (Sol' p).2 (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
        Small (HB) (Sol' p).2 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        SupBounds (HB) (Sol' p).1 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        (∀ δα' : (HB).Ω 1 → ℂ, Small (HB) δα' (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf (GB)) (HB) (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
            (pertSource (HB) (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol' p).2))
    {m₀ : ℕ} (hm₀ : 1 ≤ m₀) (hN : L ^ m₀ ∣ N₁) (hN' : L ^ m₀ ∣ N₁')
    (b : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1)))) {rc R : ℕ}
    (hb : InBox d rc (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) b) (hrc : L ^ (k + 1) * rc ≤ R)
    (hX₁R : ∀ x ∈ LocalCover.nbhd m₀ (LocalCover.blockSite k b),
      InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x)
    {Y : Set (CTorus d L N₁ m₁ (k + 1))}
    (hYR : ∀ y ∈ Y, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) y)
    (hn : 4 * R + 12 * L ^ (k + 1 + m₁) + 7 * L ^ (k + 1) + 5 < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hn' : 4 * R + 12 * L ^ (k + 1 + m₁) + 7 * L ^ (k + 1) + 5 < (N₁' * L ^ m₁) * L ^ (k + 1))
    (hnS : 2 * (ρ₁) + 5 * (L * cellSide L 0 m₁ (k + 1)) < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hnS' : 2 * (ρ₁) + 5 * (L * cellSide L 0 m₁ (k + 1)) < (N₁' * L ^ m₁) * L ^ (k + 1))
    (hnF : 2 * R + 5 * (L * cellSide L m₀ m₁ (k + 1)) < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hnF' : 2 * R + 5 * (L * cellSide L m₀ m₁ (k + 1)) < (N₁' * L ^ m₁) * L ^ (k + 1))
    {D : BgData (GA) N} {D' : BgData (GB) N}
    (hD : XiCData (GA) (compWeight L a₁) ν (k + 1) 1 eps D)
    (hD' : XiCData (GB) (compWeight L a₁) ν (k + 1) 1 eps D')
    (hraw : RawBoxAgree {z | InBox d (R + 3 * L ^ (k + 1)) ((N₁ * L ^ m₁) * L ^ (k + 1)) z}
      (rawOf D) (rawOf D'))
    (hN2 : 2 ≤ N) (νS β p₁ δ : ℝ) {ρ : ℝ} (hρ : 0 < ρ)
    (hp : 0 < (SA).p₁) (hp' : 0 < (SB).p₁)
    (Φ : ∀ c, ((SA).blockSplit m₀ hp).Ωb c) (Φ' : ∀ c, ((SB).blockSplit m₀ hp').Ωb c)
    (hΦ : ∀ x, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x →
      Φ' ((SB).cellOf m₀ (unitPt hGB (bm x))) ⟨unitPt hGB (bm x), rfl⟩ =
        Φ ((SA).cellOf m₀ (unitPt hGA x)) ⟨unitPt hGA x, rfl⟩)
    {Zm : Finset (unitPts (GA))} {Zm' : Finset (unitPts (GB))}
    (hZm : ∀ x, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x →
      (unitPt hGB (bm x) ∈ Zm' ↔ unitPt hGA x ∈ Zm))
    {um : ℂ} (hum : ‖um‖ * markedRad d L N k a₁ κ ρ cc < δ₁) :
    decMarkCorr (SB) (LocalCover.nbhdF m₀ (LocalCover.blockSite k (bc b))) m₀ k
        (LocalCover.fam m₀ (LocalCover.blockSite k (bc b))) a₁ ν cc F₁' Sol'
        (blockEnergyFun (GB) (HB) (compWeight L a₁) ν k (bc b)) Zm' (bm '' Y) ρ hp' (rawOf D') um Φ' =
      decMarkCorr (SA) (LocalCover.nbhdF m₀ (LocalCover.blockSite k b)) m₀ k
        (LocalCover.fam m₀ (LocalCover.blockSite k b)) a₁ ν cc F₁ Sol
        (blockEnergyFun (GA) (HA) (compWeight L a₁) ν k b) Zm Y ρ hp (rawOf D) um Φ := by
  have hG : ∀ v : ℂ, ‖v‖ * markedRad d L N k a₁ κ ρ cc < δ₁ →
      decMarkG (SB) (LocalCover.nbhdF m₀ (LocalCover.blockSite k (bc b))) m₀ k
        (LocalCover.fam m₀ (LocalCover.blockSite k (bc b))) a₁ ν cc F₁' Sol'
        (blockEnergyFun (GB) (HB) (compWeight L a₁) ν k (bc b)) Zm' (bm '' Y) ρ hp' (rawOf D') v Φ' =
        decMarkG (SA) (LocalCover.nbhdF m₀ (LocalCover.blockSite k b)) m₀ k
        (LocalCover.fam m₀ (LocalCover.blockSite k b)) a₁ ν cc F₁ Sol
        (blockEnergyFun (GA) (HA) (compWeight L a₁) ν k b) Zm Y ρ hp (rawOf D) v Φ :=
    fun v hv => decMarkG_rootBlock_twoTorus hC hC' hk hGA hGB cc hMX hmar hαK hsm hF₁ hF₁' hSol
      hSol' hm₀ hN hN' b hb hrc hX₁R hYR hn hn' hnS hnS' hnF hnF' hD hD' hraw hN2 νS β p₁ δ hρ hp
      hp' Φ Φ' hΦ hZm hv
  have hδ : ‖(0 : ℂ)‖ * markedRad d L N k a₁ κ ρ cc < δ₁ := by simpa using hC.δ₁_pos
  have hopen : IsOpen {v : ℂ | ‖v‖ * markedRad d L N k a₁ κ ρ cc < δ₁} :=
    isOpen_lt (by fun_prop) continuous_const
  have hd : deriv (fun v : ℂ => decMarkG (SB) (LocalCover.nbhdF m₀ (LocalCover.blockSite k (bc b))) m₀ k
        (LocalCover.fam m₀ (LocalCover.blockSite k (bc b))) a₁ ν cc F₁' Sol'
        (blockEnergyFun (GB) (HB) (compWeight L a₁) ν k (bc b)) Zm' (bm '' Y) ρ hp' (rawOf D') v Φ') 0 =
      deriv (fun v : ℂ => decMarkG (SA) (LocalCover.nbhdF m₀ (LocalCover.blockSite k b)) m₀ k
        (LocalCover.fam m₀ (LocalCover.blockSite k b)) a₁ ν cc F₁ Sol
        (blockEnergyFun (GA) (HA) (compWeight L a₁) ν k b) Zm Y ρ hp (rawOf D) v Φ) 0 :=
    Filter.EventuallyEq.deriv_eq (Filter.mem_of_superset (hopen.mem_nhds hδ) fun v hv => hG v hv)
  unfold decMarkCorr
  rw [hG um hum, hG 0 hδ, hd]


end Marks

/-! ### D3 (e): the sum of the marked energy terms over the domains of the box -/

section EvSum

variable {d L N₁ N₁' m₁ k N : ℕ} [NeZero N₁] [NeZero N₁'] [NeZero L] {ϱ : ℝ}

set_option hygiene false in
local notation "bm" => boxMap ((N₁ * L ^ m₁) * L ^ (k + 1)) ((N₁' * L ^ m₁) * L ^ (k + 1))
set_option hygiene false in
local notation "bm'" => boxMap ((N₁' * L ^ m₁) * L ^ (k + 1)) ((N₁ * L ^ m₁) * L ^ (k + 1))
set_option hygiene false in
local notation "GA" => levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ)
  (k + 1) le_rfl
set_option hygiene false in
local notation "GB" => levelGS (d := d) (L := L) (N₁ := N₁') (m₁ := m₁) (k := k + 1) (ϱ := ϱ)
  (k + 1) le_rfl
set_option hygiene false in
local notation "HA" => levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ)
  k (Nat.le_succ k)
set_option hygiene false in
local notation "HB" => levelGS (d := d) (L := L) (N₁ := N₁') (m₁ := m₁) (k := k + 1) (ϱ := ϱ)
  k (Nat.le_succ k)
set_option hygiene false in
local notation "ρ₁" => R + (3 * L ^ (k + 1 + m₁) + 3 * L ^ (k + 1 + 2)) + L ^ (k + 1 + m₁)

/-- **Sums over the sets of a box on two tori.**  Let `t_A`, `t_B` be finite families of sets of the
boxes of radius `r` of the two tori such that a set `Y` of the box lies in `t_A` iff `boxMap '' Y`
lies in `t_B`, and let `g (boxMap '' Y) = f Y` for `Y ∈ t_A`.  Then `∑_{t_B} g = ∑_{t_A} f`. -/
theorem sum_image_boxMap_of_inBox {d n n' r : ℕ} {β : Type*} [AddCommMonoid β]
    (hm : 2 * r + 1 < n) (hm' : 2 * r + 1 < n') (tA : Finset (Set (Torus d n)))
    (tB : Finset (Set (Torus d n'))) (f : Set (Torus d n) → β) (g : Set (Torus d n') → β)
    (hA : ∀ Y ∈ tA, ∀ y ∈ Y, InBox d r n y) (hB : ∀ Y' ∈ tB, ∀ y ∈ Y', InBox d r n' y)
    (hmem : ∀ Y : Set (Torus d n), (∀ y ∈ Y, InBox d r n y) → (boxMap n n' '' Y ∈ tB ↔ Y ∈ tA))
    (hfg : ∀ Y ∈ tA, g (boxMap n n' '' Y) = f Y) :
    ∑ Y' ∈ tB, g Y' = ∑ Y ∈ tA, f Y := by
  symm
  refine Finset.sum_nbij' (fun Y => boxMap n n' '' Y) (fun Y' => boxMap n' n '' Y')
    (fun Y hY => (hmem Y (hA Y hY)).2 hY) (fun Y' hY' => ?_)
    (fun Y hY => image_image_boxMap hm' (hA Y hY)) (fun Y' hY' => image_image_boxMap hm (hB Y' hY'))
    (fun Y hY => (hfg Y hY).symm)
  have hYb2 : ∀ y ∈ boxMap n' n '' Y', InBox d r n y := by
    rintro _ ⟨y, hy, rfl⟩
    exact inBox_boxMap hm (hB Y' hY' y hy)
  refine (hmem _ hYb2).1 ?_
  rw [image_image_boxMap hm (hB Y' hY')]
  exact hY'

/-- `mem_polymerDomains_boxMap_iff` at the top level, for a set `S'` of the second torus equal to
the image `bm '' X₁` (the parameter type `ParIdx GB S'` is not rewritten). -/
theorem mem_polymerDomains_boxMap_iff_of_eq {m₀ R : ℕ} (hN : L ^ m₀ ∣ N₁) (hN' : L ^ m₀ ∣ N₁')
    (hn : 2 * R + 5 * (L * cellSide L m₀ m₁ (k + 1)) < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hn' : 2 * R + 5 * (L * cellSide L m₀ m₁ (k + 1)) < (N₁' * L ^ m₁) * L ^ (k + 1))
    {X₁ : Set (CTorus d L N₁ m₁ (k + 1))}
    (hX : ∀ x ∈ X₁, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x)
    {S' : Set (CTorus d L N₁' m₁ (k + 1))} (hS' : S' = bm '' X₁)
    {Y : Set (CTorus d L N₁ m₁ (k + 1))} (hY : ∀ y ∈ Y, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) y) :
    bm '' Y ∈ polymerDomains (fun i : ParIdx (GB) S' => i.1.1) (GB) m₀ S' ↔
      Y ∈ polymerDomains (fun i : ParIdx (GA) X₁ => i.1.1) (GA) m₀ X₁ := by
  subst hS'
  exact mem_polymerDomains_boxMap_iff hN hN' le_rfl hn hn' (Nat.le_add_left 1 k) hX hY

/-- **The domains `polyDom` of the box on two tori.**  For covering data `(X, 𝒦_X)`, `(X', 𝒦_X')`
of the two tori with `X₁ = X1 … 𝒦_X` in the box of radius `R` and `X1 … 𝒦_X' = bm '' X₁`, a set
`Y` of the box is a domain of the expansion of the first torus iff `bm '' Y` is one of the
second torus (`mem_polymerDomains_boxMap_iff`). -/
theorem mem_polyDom_boxMap_iff {m₀ j R : ℕ}
    {X 𝒦X : Set (CTorus d L N₁ m₁ (k + 1))} {X' 𝒦X' : Set (CTorus d L N₁' m₁ (k + 1))}
    {X₁f : Finset (CTorus d L N₁ m₁ (k + 1))}
    (hcov : CovSetup (GA) m₀ j X 𝒦X)
    (hX₁ : (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) = X1 (GA) m₀ j 𝒦X)
    (hcov' : CovSetup (GB) m₀ j X' 𝒦X')
    (hX₁' : (↑(X₁f.image bm) : Set (CTorus d L N₁' m₁ (k + 1))) = X1 (GB) m₀ j 𝒦X')
    (hX₁R : ∀ x ∈ X₁f, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x)
    (hn : 2 * R + 5 * (L * cellSide L m₀ m₁ (k + 1)) < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hn' : 2 * R + 5 * (L * cellSide L m₀ m₁ (k + 1)) < (N₁' * L ^ m₁) * L ^ (k + 1))
    (Y : Set (CTorus d L N₁ m₁ (k + 1)))
    (hY : ∀ y ∈ Y, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) y) :
    bm '' Y ∈ polyDom (GB) (X₁f.image bm) m₀ j 𝒦X' ↔ Y ∈ polyDom (GA) X₁f m₀ j 𝒦X := by
  have hXs : ∀ x ∈ (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))),
      InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x := fun x hx => hX₁R x (Finset.mem_coe.1 hx)
  show bm '' Y ∈ polymerDomains (fun i : ParIdx (GB)
      (↑(X₁f.image bm) : Set (CTorus d L N₁' m₁ (k + 1))) => i.1.1) (GB) m₀ (X1 (GB) m₀ j 𝒦X') ↔
    Y ∈ polymerDomains (fun i : ParIdx (GA) (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) => i.1.1)
      (GA) m₀ (X1 (GA) m₀ j 𝒦X)
  rw [← hX₁, ← hX₁']
  exact mem_polymerDomains_boxMap_iff_of_eq hcov.hN hcov'.hN hn hn' hXs Finset.coe_image hY

/-- **D3 (e): the marked energy terms summed over the domains of the box.**  Under the hypotheses of
`evDec_twoTorus` (for every domain), the sum of `evDec … Y` over the polymer domains `Y` of the
expansion (`polyDom`, the domains `Y[𝒞]`) that lie in the box of radius `R` (the family `t_A`,
for instance the filter of `polyDom` by the box condition) equals the same sum on the second torus
(`t_B`).  The domains of the box correspond by `bm` (`mem_polymerDomains_boxMap_iff`);
the domains not in the box (in particular those winding around the torus) are not compared. -/
theorem sum_evDec_box_twoTorus
    {a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁ : ℝ}
    (hC : FlCore N (GA) (HA) a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
    (hC' : FlCore N (GB) (HB) a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁) (hk : 1 ≤ k)
    (hGA : IsLevel (GA) (k + 1)) (hGB : IsLevel (GB) (k + 1)) (cc : ℂ) {cψ : ℝ} (hcψ : 0 ≤ cψ)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δc : ℝ}
    (hmar : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hαK : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    {F₁ : DecParams (GA) × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      ((GA).Ω 1 × Fin N → ℂ) × ((GA).Ω 1 → ℂ)}
    {F₁' : DecParams (GB) × RawData d L (N₁' * L ^ m₁) (k + 1) N →
      ((GB).Ω 1 × Fin N → ℂ) × ((GB).Ω 1 → ℂ)}
    (hF₁ : ∀ (s : DecParams (GA)) (D : BgData (GA) N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC (GA) (bgC0 d L N) (c7 d L N BG κ) ν D → ∀ (φ : (GA).Ω 1 × Fin N → ℂ)
        (α : (GA).Ω 1 → ℂ), IsDecBg (GA) (compWeight L a₁) ν (rho4 d L N BG κ) s D φ α →
        F₁ (s, rawOf D) = (φ, α))
    (hF₁' : ∀ (s : DecParams (GB)) (D : BgData (GB) N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC (GB) (bgC0 d L N) (c7 d L N BG κ) ν D → ∀ (φ : (GB).Ω 1 × Fin N → ℂ)
        (α : (GB).Ω 1 → ℂ), IsDecBg (GB) (compWeight L a₁) ν (rho4 d L N BG κ) s D φ α →
        F₁' (s, rawOf D) = (φ, α))
    {Sol : Dec2.DecParams (coverOf (GA)) × Edat (HA) N → ((HA).Ω 1 × Fin N → ℂ) × ((HA).Ω 1 → ℂ)}
    {Sol' : Dec2.DecParams (coverOf (GB)) × Edat (HB) N →
      ((HB).Ω 1 × Fin N → ℂ) × ((HB).Ω 1 → ℂ)}
    (hSol : ∀ p : Dec2.DecParams (coverOf (GA)) × Edat (HA) N, (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM (HA) N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2 →
        (Sol p).1 = dphi (HA) (Dec2.decG (coverOf (GA)) (HA) (compWeight L a₁) ν p.1) p.2.2.1
          p.2.1 (pertSource (HA) (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol p).2 ∧
        Dec2.DecFixed (coverOf (GA)) (HA) (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
          (pertSource (HA) (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol p).2 ∧
        Small (HA) (Sol p).2 (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
        Small (HA) (Sol p).2 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        SupBounds (HA) (Sol p).1 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        (∀ δα' : (HA).Ω 1 → ℂ, Small (HA) δα' (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf (GA)) (HA) (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
            (pertSource (HA) (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol p).2))
    (hSol' : ∀ p : Dec2.DecParams (coverOf (GB)) × Edat (HB) N, (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM (HB) N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2 →
        (Sol' p).1 = dphi (HB) (Dec2.decG (coverOf (GB)) (HB) (compWeight L a₁) ν p.1) p.2.2.1
          p.2.1 (pertSource (HB) (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol' p).2 ∧
        Dec2.DecFixed (coverOf (GB)) (HB) (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
          (pertSource (HB) (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol' p).2 ∧
        Small (HB) (Sol' p).2 (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
        Small (HB) (Sol' p).2 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        SupBounds (HB) (Sol' p).1 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        (∀ δα' : (HB).Ω 1 → ℂ, Small (HB) δα' (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf (GB)) (HB) (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
            (pertSource (HB) (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol' p).2))
    {m₀ j : ℕ} {X 𝒦X : Set (CTorus d L N₁ m₁ (k + 1))} {X' 𝒦X' : Set (CTorus d L N₁' m₁ (k + 1))}
    {X₁f : Finset (CTorus d L N₁ m₁ (k + 1))}
    (hcov : CovSetup (GA) m₀ j X 𝒦X)
    (hX₁ : (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) = X1 (GA) m₀ j 𝒦X)
    (hcov' : CovSetup (GB) m₀ j X' 𝒦X')
    (hX₁' : (↑(X₁f.image bm) : Set (CTorus d L N₁' m₁ (k + 1))) = X1 (GB) m₀ j 𝒦X')
    {Φ : (((GA).Ω 1 × Fin N → ℂ) × ((GA).Ω 1 → ℂ)) → ((HA).Ω 1 × Fin N → ℂ) →
      RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) → ℂ}
    {Φ' : (((GB).Ω 1 × Fin N → ℂ) × ((GB).Ω 1 → ℂ)) → ((HB).Ω 1 × Fin N → ℂ) →
      RawData d L (N₁' * L ^ m₁) (k + 1) N × (CTorus d L N₁' m₁ (k + 1) → Fin N → ℂ) → ℂ}
    {Rα Rδ Rψ : Set (CTorus d L N₁ m₁ (k + 1))} (hBM : BlockMargin (GA) X₁f Rα)
    (hRδ : Rδ ⊆ ↑X₁f) (hRψ : Rψ ⊆ ↑X₁f)
    (hΦ : ∀ (t : (((GA).Ω 1 × Fin N → ℂ) × ((GA).Ω 1 → ℂ)) × ((HA).Ω 1 × Fin N → ℂ) ×
        (RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ)))
      (t' : (((GB).Ω 1 × Fin N → ℂ) × ((GB).Ω 1 → ℂ)) × ((HB).Ω 1 × Fin N → ℂ) ×
        (RawData d L (N₁' * L ^ m₁) (k + 1) N × (CTorus d L N₁' m₁ (k + 1) → Fin N → ℂ))),
      (∀ (y : (GA).Ω 1) (y' : (GB).Ω 1), (y : CTorus d L N₁ m₁ (k + 1)) ∈ Rα →
        (y' : CTorus d L N₁' m₁ (k + 1)) = bm (y : CTorus d L N₁ m₁ (k + 1)) →
          t'.1.2 y' = t.1.2 y) →
      (∀ (w : (HA).Ω 1) (w' : (HB).Ω 1), (w : CTorus d L N₁ m₁ (k + 1)) ∈ Rδ →
        (w' : CTorus d L N₁' m₁ (k + 1)) = bm (w : CTorus d L N₁ m₁ (k + 1)) →
        ∀ i, t'.2.1 (w', i) = t.2.1 (w, i)) →
      (∀ x ∈ Rψ, t'.2.2.2 (bm x) = t.2.2.2 x) →
      Φ' t'.1 t'.2.1 t'.2.2 = Φ t.1 t.2.1 t.2.2)
    {R : ℕ} (hX₁R : ∀ x ∈ X₁f, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x)
    (hn : 4 * R + 12 * L ^ (k + 1 + m₁) + 7 * L ^ (k + 1) + 5 < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hn' : 4 * R + 12 * L ^ (k + 1 + m₁) + 7 * L ^ (k + 1) + 5 < (N₁' * L ^ m₁) * L ^ (k + 1))
    (hnS : 2 * (ρ₁) + 5 * (L * cellSide L 0 m₁ (k + 1)) < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hnS' : 2 * (ρ₁) + 5 * (L * cellSide L 0 m₁ (k + 1)) < (N₁' * L ^ m₁) * L ^ (k + 1))
    (hnF : 2 * R + 5 * (L * cellSide L m₀ m₁ (k + 1)) < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hnF' : 2 * R + 5 * (L * cellSide L m₀ m₁ (k + 1)) < (N₁' * L ^ m₁) * L ^ (k + 1))
    (hΦan : AnalyticOnNhd ℂ (fun t => Φ t.1 t.2.1 t.2.2)
      (FlReal (GA) (HA) a₁ ν BG κ eps X₁f BG₂ δ₁))
    {D : BgData (GA) N} {D' : BgData (GB) N}
    (hD : XiCData (GA) (compWeight L a₁) ν (k + 1) 1 eps D)
    (hD' : XiCData (GB) (compWeight L a₁) ν (k + 1) 1 eps D')
    (hraw : RawBoxAgree {z | InBox d (R + 3 * L ^ (k + 1)) ((N₁ * L ^ m₁) * L ^ (k + 1)) z}
      (rawOf D) (rawOf D'))
    {ψh : unitPts (GA) × Fin N → ℂ} {ψh' : unitPts (GB) × Fin N → ℂ}
    (hψh : ∀ p, ‖ψh p‖ ≤ cψ) (hψh' : ∀ p, ‖ψh' p‖ ≤ cψ)
    (hhat : ∀ x, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x →
      ∀ i, ψh' (unitPt hGB (bm x), i) = ψh (unitPt hGA x, i))
    {Zm : Finset (unitPts (GA))} {Zm' : Finset (unitPts (GB))}
    (hZm : ∀ x, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x →
      (unitPt hGB (bm x) ∈ Zm' ↔ unitPt hGA x ∈ Zm))
    {um tm : ℂ} (hum : (‖um‖ + ‖tm‖) * markedRad d L N k a₁ κ cψ cc < δ₁)
    (tA : Finset (Set (CTorus d L N₁ m₁ (k + 1))))
    (tB : Finset (Set (CTorus d L N₁' m₁ (k + 1))))
    (htA : ∀ Y, Y ∈ tA ↔
      Y ∈ polyDom (GA) X₁f m₀ j 𝒦X ∧ ∀ y ∈ Y, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) y)
    (htB : ∀ Y', Y' ∈ tB ↔
      Y' ∈ polyDom (GB) (X₁f.image bm) m₀ j 𝒦X' ∧
        ∀ y ∈ Y', InBox d R ((N₁' * L ^ m₁) * L ^ (k + 1)) y) :
    ∑ Y' ∈ tB, evDec (X₁f.image bm) m₀ j 𝒦X' a₁ ν hGB cc F₁' Sol' Φ' Zm' um tm Y' (rawOf D', ψh') =
      ∑ Y ∈ tA, evDec X₁f m₀ j 𝒦X a₁ ν hGA cc F₁ Sol Φ Zm um tm Y (rawOf D, ψh) := by
  have hc1 : 1 ≤ 5 * (L * cellSide L m₀ m₁ (k + 1)) :=
    Nat.succ_le_of_lt (Nat.mul_pos (by norm_num)
      (Nat.mul_pos (Nat.pos_of_ne_zero (NeZero.ne L)) (cellSide_pos m₀ m₁ (k + 1))))
  have hR1 : 2 * R + 1 < (N₁ * L ^ m₁) * L ^ (k + 1) :=
    Nat.lt_of_le_of_lt (Nat.add_le_add_left hc1 _) hnF
  have hR1' : 2 * R + 1 < (N₁' * L ^ m₁) * L ^ (k + 1) :=
    Nat.lt_of_le_of_lt (Nat.add_le_add_left hc1 _) hnF'
  have hmem := mem_polyDom_boxMap_iff hcov hX₁ hcov' hX₁' hX₁R hnF hnF'
  apply sum_image_boxMap_of_inBox hR1 hR1'
  · intro Y hY
    exact ((htA Y).1 hY).2
  · intro Y hY
    exact ((htB Y).1 hY).2
  · intro Y hY
    rw [htA, htB, hmem Y hY]
    refine and_congr_right fun _ => ⟨fun _ => hY, fun _ => ?_⟩
    rintro _ ⟨y, hy, rfl⟩
    exact inBox_boxMap hR1' (hY y hy)
  · intro Y hY
    exact evDec_twoTorus hC hC' hk hGA hGB cc hcψ hMX hmar hαK hsm hF₁ hF₁' hSol hSol' hcov hX₁ hcov'
      hX₁' hBM hRδ hRψ hΦ hX₁R ((htA Y).1 hY).2 hn hn' hnS hnS' hnF hnF' hΦan hD hD' hraw
      hψh hψh' hhat hZm hum

end EvSum

/-! ### D3: the determinant part of the energy coefficient on two tori -/

section Det

variable {d L N₁ N₁' m₁ k N : ℕ} [NeZero N₁] [NeZero N₁'] [NeZero L] {ϱ ϱm ϱm' : ℝ} {m₀ : ℕ}

set_option hygiene false in
local notation "bm" => boxMap ((N₁ * L ^ m₁) * L ^ (k + 1)) ((N₁' * L ^ m₁) * L ^ (k + 1))
set_option hygiene false in
local notation "bU" => boxMap ((N₁ * L ^ m₁) * L ^ (k + 1 - k)) ((N₁' * L ^ m₁) * L ^ (k + 1 - k))
set_option hygiene false in
local notation "GA" => levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ)
  (k + 1) le_rfl
set_option hygiene false in
local notation "GB" => levelGS (d := d) (L := L) (N₁ := N₁') (m₁ := m₁) (k := k + 1) (ϱ := ϱ)
  (k + 1) le_rfl
set_option hygiene false in
local notation "ιu" b:max => Subtype.mk (bU (b : UnitTorus d L N₁ m₁ k))
  (mem_unitPts_levelTop (d := d) (L := L) (N₁ := N₁') (m₁ := m₁) (k := k) (ϱ := ϱ) _)
set_option hygiene false in
local notation "aK" => cellSide L m₀ m₁ (k + 1)

omit [NeZero N₁'] in
/-- The root cube of the coarse site of a fine site `x` is the cell of side `a_K` of `x`. -/
theorem rootCube_blockIndex_val (x : CTorus d L N₁ m₁ (k + 1)) :
    (rootCube (m₀ := m₀) (blockIndex x)).1 = cbase aK x := by
  show cbase aK (rootSite (blockIndex x)) = _
  rw [rootSite_blockIndex, blockBase, cbase_cbase_of_dvd_hull (Nat.pos_of_ne_zero (NeZero.ne _))
    (pow_dvd_cellSide (m₀ := m₀))]

/-- **The root cube of a unit point on two tori.**  If the root cell of the unit point `y` lies in
the box of radius `r`, the root cube of `ιu y` is the `cubeMap`-image of the root cube of `y`.
Margins: `2 r + 3 L^(k+1) + 5 < N₁ L^m₁ L^(k+1)` and `2 r + a_K < N₁ L^m₁ L^(k+1)`. -/
theorem cubeMap_rootCube_unitPt (hN : L ^ m₀ ∣ N₁) (hN' : L ^ m₀ ∣ N₁') {r : ℕ}
    (hn1 : 2 * r + 3 * L ^ (k + 1) + 5 < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hn2 : 2 * r + aK < (N₁ * L ^ m₁) * L ^ (k + 1)) (y : unitPts (GA))
    (hroot : ∀ x ∈ rootSet m₀ (rootIdxOf y), InBox d r ((N₁ * L ^ m₁) * L ^ (k + 1)) x) :
    cubeMap hN hN' le_rfl (rootCube (m₀ := m₀) (rootIdxOf y)) =
      rootCube (m₀ := m₀) (rootIdxOf (ιu y)) := by
  obtain ⟨x0, -, hx0⟩ := (mem_unitPts _).1 y.2
  have hr0 : rootIdxOf y = blockIndex x0 := rootIdxOf_eq hx0
  have hx0R : InBox d r ((N₁ * L ^ m₁) * L ^ (k + 1)) x0 :=
    hroot x0 (by rw [hr0]; exact mem_rootSet_blockIndex x0)
  have hr1 : rootIdxOf (ιu y) = blockIndex (bm x0) :=
    rootIdxOf_eq (unitImage_val (N₁' := N₁') hn1 y hx0 hx0R).symm
  apply Subtype.ext
  rw [cubeMap_val, hr1, hr0, rootCube_blockIndex_val, rootCube_blockIndex_val]
  refine cbase_boxMap (cellSide_dvd (K := k + 1) (m₁ := m₁) hN le_rfl)
    (cellSide_dvd (K := k + 1) (m₁ := m₁) hN' le_rfl) (cellSide_pos m₀ m₁ _) hn2 x0
    fun z hz => hroot z ?_
  rw [hr0, rootSet_blockIndex]
  exact hz

/-- **D3 (e): the determinant activities summed over the polymers of the box.**  For a unit point
`y` whose root cell lies in the box of radius `r`, the sum of the activities `detActivityBg y Y`
over all sets `Y` of level-`(k+1)` cubes with sites in the box equals the same sum on the second
torus for `ιu y`.  The sets correspond by `cubeMap` (`image_image_cubeMap`); a set containing the
root cube is `detActivityBg_twoTorus`; a set without the root cube has activity `0` on the first
torus (`detActivityBg_ne_zero_imp`), and its image has no root cube of `ιu y`
(`cubeMap_rootCube_unitPt`), hence activity `0` on the second torus.  The polymers not inside the
box are not compared.  Margins as in `detActivityBg_twoTorus`. -/
theorem sum_detActivityBg_box_twoTorus (hN : L ^ m₀ ∣ N₁) (hN' : L ^ m₀ ∣ N₁')
    {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}
    {Hm' : GeneratingSet d L (N₁' * L ^ m₁) (k + 1) ϱm'}
    {a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁ : ℝ}
    (hC : FlCore N (GA) Hm a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
    (hC' : FlCore N (GB) Hm' a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁) (hk : 1 ≤ k) {δc : ℝ}
    (hδc : 0 ≤ δc) (hcap : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    (hmar : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hαK : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hconn : HatConn (GA)) (hconn' : HatConn (GB))
    {D : BgData (GA) N} {D' : BgData (GB) N}
    (hD : XiCData (GA) (compWeight L a₁) ν (k + 1) 1 eps D)
    (hD' : XiCData (GB) (compWeight L a₁) ν (k + 1) 1 eps D')
    (y : unitPts (GA))
    {r : ℕ} (hroot : ∀ x ∈ rootSet m₀ (rootIdxOf y), InBox d r ((N₁ * L ^ m₁) * L ^ (k + 1)) x)
    (hn : 4 * r + 12 * L ^ (k + 1 + m₁) + 7 * L ^ (k + 1) + 5 < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hn' : 4 * r + 12 * L ^ (k + 1 + m₁) + 7 * L ^ (k + 1) + 5 < (N₁' * L ^ m₁) * L ^ (k + 1))
    (hnS : 2 * (r + (3 * L ^ (k + 1 + m₁) + 3 * L ^ (k + 1 + 2)) + L ^ (k + 1 + m₁)) +
      5 * (L * cellSide L 0 m₁ (k + 1)) < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hnS' : 2 * (r + (3 * L ^ (k + 1 + m₁) + 3 * L ^ (k + 1 + 2)) + L ^ (k + 1 + m₁)) +
      5 * (L * cellSide L 0 m₁ (k + 1)) < (N₁' * L ^ m₁) * L ^ (k + 1))
    (hnH : 2 * (r + 2 * (L * aK)) + L * aK < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hnH' : 2 * (r + 2 * (L * aK)) + L * aK < (N₁' * L ^ m₁) * L ^ (k + 1))
    (hraw : RawBoxAgree {z | InBox d (r + 3 * L ^ (k + 1)) ((N₁ * L ^ m₁) * L ^ (k + 1)) z}
      (rawOf D) (rawOf D')) :
    ∑ Y' ∈ Finset.univ.filter (fun Y' : Finset (CubeB (d := d) (L := L) (N₁ := N₁') (m₁ := m₁)
        (K := k + 1) m₀ (k + 1) Set.univ) =>
          ∀ x ∈ sitesOf Y', InBox d r ((N₁' * L ^ m₁) * L ^ (k + 1)) x),
        detActivityBg m₀ (compWeight L a₁) a₁ ν (rho4 d L N BG κ) D' (ιu y) Y' =
      ∑ Y ∈ Finset.univ.filter (fun Y : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
        (K := k + 1) m₀ (k + 1) Set.univ) =>
          ∀ x ∈ sitesOf Y, InBox d r ((N₁ * L ^ m₁) * L ^ (k + 1)) x),
        detActivityBg m₀ (compWeight L a₁) a₁ ν (rho4 d L N BG κ) D y Y := by
  have hcs : aK ≤ L * aK := cellSide_le_mul
  have hK1 : 1 ≤ L ^ (k + 1) := Nat.one_le_pow _ _ (Nat.pos_of_ne_zero (NeZero.ne L))
  have hr : 2 * r + L * aK < (N₁ * L ^ m₁) * L ^ (k + 1) := by omega
  have hr' : 2 * r + L * aK < (N₁' * L ^ m₁) * L ^ (k + 1) := by omega
  have hrc : InBox d r ((N₁ * L ^ m₁) * L ^ (k + 1)) (rootCube (m₀ := m₀) (rootIdxOf y)).1 :=
    hroot _ (mem_box_self _ (cellSide_pos m₀ m₁ _))
  symm
  refine Finset.sum_nbij' (fun Y => Y.image (cubeMap hN hN' le_rfl))
    (fun Y' => Y'.image (cubeMap hN' hN le_rfl)) (fun Y hY => ?_) (fun Y' hY' => ?_)
    (fun Y hY => ?_) (fun Y' hY' => ?_) (fun Y hY => ?_)
  · have hY1 := (Finset.mem_filter.1 hY).2
    refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩
    rw [sitesOf_image_cubeMap hN hN' le_rfl hr Y hY1]
    rintro _ ⟨x, hx, rfl⟩
    exact inBox_boxMap (by omega) (hY1 x hx)
  · have hY1 := (Finset.mem_filter.1 hY').2
    refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩
    rw [sitesOf_image_cubeMap hN' hN le_rfl hr' Y' hY1]
    rintro _ ⟨x, hx, rfl⟩
    exact inBox_boxMap (by omega) (hY1 x hx)
  · exact image_image_cubeMap hN hN' le_rfl hr' Y (Finset.mem_filter.1 hY).2
  · exact image_image_cubeMap hN' hN le_rfl hr Y' (Finset.mem_filter.1 hY').2
  · have hY1 := (Finset.mem_filter.1 hY).2
    by_cases hyY : rootCube (m₀ := m₀) (rootIdxOf y) ∈ Y
    · exact (detActivityBg_twoTorus hN hN' hC hC' hk hδc hcap hsm hmar hαK hconn hconn' hD hD' y Y
        hyY hY1 hn hn' hnS hnS' hnH hnH' hraw).symm
    · have h1 : detActivityBg m₀ (compWeight L a₁) a₁ ν (rho4 d L N BG κ) D y Y = 0 := by
        by_contra h
        exact hyY (detActivityBg_ne_zero_imp hC hk hδc hcap hsm hmar hαK hconn hD hN h).1
      have h2 : detActivityBg m₀ (compWeight L a₁) a₁ ν (rho4 d L N BG κ) D' (ιu y)
          (Y.image (cubeMap hN hN' le_rfl)) = 0 := by
        by_contra h
        have hm := (detActivityBg_ne_zero_imp hC' hk hδc hcap hsm hmar hαK hconn' hD' hN' h).1
        rw [← cubeMap_rootCube_unitPt hN hN' (by omega) (by omega) y hroot] at hm
        obtain ⟨c, hc, hce⟩ := Finset.mem_image.1 hm
        apply hyY
        have e := congrArg (cubeMap hN' hN le_rfl) hce
        rw [cubeMap_cubeMap hN hN' le_rfl hr' (sitesOf_subset_box_of_mem hY1 hc),
          cubeMap_cubeMap hN hN' le_rfl hr' hrc] at e
        rw [← e]
        exact hc
      rw [h1, h2]

end Det

end Balaban.Polymer.TwoTorusStep
