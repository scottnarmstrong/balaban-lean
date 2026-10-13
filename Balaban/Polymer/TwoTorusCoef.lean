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

omit [NeZero N₁'] in
/-- The corner site `blockSite k z` of the block `B_{k+1}(z)` of a coarse site `|z| ≤ r_c` lies in
the box of radius `ρ ≥ L^(k+1) r_c`. -/
theorem blockSite_inBox {ρ rc : ℕ} (hs : 2 * ρ + 1 < (N₁ * L ^ m₁) * L ^ (k + 1))
    (z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))))
    (hz : InBox d rc (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) z) (hrc : L ^ (k + 1) * rc ≤ ρ) :
    InBox d ρ ((N₁ * L ^ m₁) * L ^ (k + 1)) (LocalCover.blockSite k z) := by
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
  have hx₀ := blockSite_inBox (N₁ := N₁) hs z hz hrc
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


set_option hygiene false in
local notation "XA" => (↑(LocalCover.nbhdF m₀ xs) : Set (CTorus d L N₁ m₁ (k + 1)))
set_option hygiene false in
local notation "XB" => (↑(LocalCover.nbhdF m₀ (bm xs)) : Set (CTorus d L N₁' m₁ (k + 1)))

/-- **D3, the site terms of the observable on two tori** (`Ev_twoTorus` for the local cover of a
site `xs`, the cover of the observable coefficient: `X = cube m₀ k xs`, `𝒦_X = fam m₀ xs`,
`X₁ = nbhdF m₀ xs`, and those of `bm xs`).  The premises `hcov`, `hX₁`, `hcov'`, `hX₁'` are
discharged by `covSetup_localCover_image`; the block functional `Φ` with its reads (`hBM`, `hRδ`,
`hRψ`, `hΦ`) and its analyticity `hΦan` remain hypotheses (they depend on the functional).  If the
region `X₁` of `xs` and the domain `Y` lie in the box of radius `R`, the terms `Ev` of `bm '' Y` and
of `Y` are equal. -/
theorem Ev_localCover_twoTorus
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
    {m₀ : ℕ} (hN : L ^ m₀ ∣ N₁) (hN' : L ^ m₀ ∣ N₁') (xs : CTorus d L N₁ m₁ (k + 1))
    {Φ : (((GA).Ω 1 × Fin N → ℂ) × ((GA).Ω 1 → ℂ)) → ((HA).Ω 1 × Fin N → ℂ) →
      RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) → ℂ}
    {Φ' : (((GB).Ω 1 × Fin N → ℂ) × ((GB).Ω 1 → ℂ)) → ((HB).Ω 1 × Fin N → ℂ) →
      RawData d L (N₁' * L ^ m₁) (k + 1) N × (CTorus d L N₁' m₁ (k + 1) → Fin N → ℂ) → ℂ}
    {Rα Rδ Rψ : Set (CTorus d L N₁ m₁ (k + 1))} (hBM : BlockMargin (GA) (LocalCover.nbhdF m₀ xs) Rα)
    (hRδ : Rδ ⊆ ↑(LocalCover.nbhdF m₀ xs)) (hRψ : Rψ ⊆ ↑(LocalCover.nbhdF m₀ xs))
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
    {R : ℕ} (hX₁R : ∀ x ∈ LocalCover.nbhd m₀ xs, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x)
    {Y : Set (CTorus d L N₁ m₁ (k + 1))}
    (hYR : ∀ y ∈ Y, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) y)
    (hn : 4 * R + 12 * L ^ (k + 1 + m₁) + 7 * L ^ (k + 1) + 5 < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hn' : 4 * R + 12 * L ^ (k + 1 + m₁) + 7 * L ^ (k + 1) + 5 < (N₁' * L ^ m₁) * L ^ (k + 1))
    (hnS : 2 * (ρ₁) + 5 * (L * cellSide L 0 m₁ (k + 1)) < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hnS' : 2 * (ρ₁) + 5 * (L * cellSide L 0 m₁ (k + 1)) < (N₁' * L ^ m₁) * L ^ (k + 1))
    (hnF : 2 * R + 5 * (L * cellSide L m₀ m₁ (k + 1)) < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hnF' : 2 * R + 5 * (L * cellSide L m₀ m₁ (k + 1)) < (N₁' * L ^ m₁) * L ^ (k + 1))
    (hΦan : AnalyticOnNhd ℂ (fun t => Φ t.1 t.2.1 t.2.2)
      (FlReal (GA) (HA) a₁ ν BG κ eps (LocalCover.nbhdF m₀ xs) BG₂ δ₁))
    {D : BgData (GA) N} {D' : BgData (GB) N}
    (hD : XiCData (GA) (compWeight L a₁) ν (k + 1) 1 eps D)
    (hD' : XiCData (GB) (compWeight L a₁) ν (k + 1) 1 eps D')
    (hraw : RawBoxAgree {z | InBox d (R + 3 * L ^ (k + 1)) ((N₁ * L ^ m₁) * L ^ (k + 1)) z}
      (rawOf D) (rawOf D'))
    {ψh : unitPts (GA) × Fin N → ℂ} {ψh' : unitPts (GB) × Fin N → ℂ}
    (hψh : ∀ p, ‖ψh p‖ ≤ cψ) (hψh' : ∀ p, ‖ψh' p‖ ≤ cψ)
    (hhat : ∀ x, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x →
      ∀ i, ψh' (unitPt hGB (bm x), i) = ψh (unitPt hGA x, i))
    (hrad : markedRad d L N k a₁ κ cψ cc < δ₁) :
    evTerm (fun i : ParIdx (GB) (XB) => i.1.1) (GB)
        m₀ (X1 (GB) m₀ k (LocalCover.fam m₀ (bm xs)))
        (fun u s => Φ'
          (F₁' (extParams (GB) (XB) s, u.1))
          (Sol' (extParams (GB) (XB) s,
            flEdat (GB) (HB) (F₁' (extParams (GB)
              (XB) s, u.1)) u.1.1
              (hatPsiF (GB) a₁ ν hGB cc F₁'
                (extParams (GB) (XB) s) u.1 u.2))).1
          (u.1, hatPsiF (GB) a₁ ν hGB cc F₁'
            (extParams (GB) (XB) s) u.1 u.2))
        (bm '' Y) (rawOf D', ψh') =
      evTerm (fun i : ParIdx (GA) (XA) => i.1.1) (GA) m₀
        (X1 (GA) m₀ k (LocalCover.fam m₀ xs))
        (fun u s => Φ (F₁ (extParams (GA) (XA) s, u.1))
          (Sol (extParams (GA) (XA) s,
            flEdat (GA) (HA) (F₁ (extParams (GA) (XA) s, u.1))
              u.1.1 (hatPsiF (GA) a₁ ν hGA cc F₁
                (extParams (GA) (XA) s) u.1 u.2))).1
          (u.1, hatPsiF (GA) a₁ ν hGA cc F₁
            (extParams (GA) (XA) s) u.1 u.2))
        Y (rawOf D, ψh) := by
  have hcs : (L - 1) * cellSide L m₀ m₁ (k + 1) ≤ L * cellSide L m₀ m₁ (k + 1) :=
    Nat.mul_le_mul_right _ (Nat.sub_le L 1)
  obtain ⟨hcov, hX₁, hcov', hX₁'⟩ := covSetup_localCover_image (ϱ := ϱ) hN hN' (j := k) le_rfl
    (R := R) (by omega) xs hX₁R
  have hF := nbhdF_image_finset hN hN' (R := R) (by omega) xs hX₁R
  have hXR : ∀ x ∈ LocalCover.nbhdF m₀ xs, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x :=
    fun x hx => hX₁R x (by rw [← LocalCover.coe_nbhdF]; exact hx)
  have h := Ev_twoTorus hC hC' hk hGA hGB cc hcψ hMX hmar hαK hsm hF₁ hF₁' hSol hSol' hcov hX₁
    hcov' hX₁' hBM hRδ hRψ hΦ hXR hYR hn hn' hnS hnS' hnF hnF' hΦan hD hD' hraw hψh hψh' hhat hrad
  rw [hF] at h
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
        (blockEnergyFun (GB) (HB) (compWeight L a₁) ν k (bc b))
          Zm' (bm '' Y) ρ hp' (rawOf D') um Φ' =
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
        (blockEnergyFun (GB) (HB) (compWeight L a₁) ν k (bc b))
          Zm' (bm '' Y) ρ hp' (rawOf D') um Φ' =
      decMarkCorr (SA) (LocalCover.nbhdF m₀ (LocalCover.blockSite k b)) m₀ k
        (LocalCover.fam m₀ (LocalCover.blockSite k b)) a₁ ν cc F₁ Sol
        (blockEnergyFun (GA) (HA) (compWeight L a₁) ν k b) Zm Y ρ hp (rawOf D) um Φ := by
  have hG : ∀ v : ℂ, ‖v‖ * markedRad d L N k a₁ κ ρ cc < δ₁ →
      decMarkG (SB) (LocalCover.nbhdF m₀ (LocalCover.blockSite k (bc b))) m₀ k
        (LocalCover.fam m₀ (LocalCover.blockSite k (bc b))) a₁ ν cc F₁' Sol'
        (blockEnergyFun (GB) (HB) (compWeight L a₁) ν k (bc b))
          Zm' (bm '' Y) ρ hp' (rawOf D') v Φ' =
        decMarkG (SA) (LocalCover.nbhdF m₀ (LocalCover.blockSite k b)) m₀ k
        (LocalCover.fam m₀ (LocalCover.blockSite k b)) a₁ ν cc F₁ Sol
        (blockEnergyFun (GA) (HA) (compWeight L a₁) ν k b) Zm Y ρ hp (rawOf D) v Φ :=
    fun v hv => decMarkG_rootBlock_twoTorus hC hC' hk hGA hGB cc hMX hmar hαK hsm hF₁ hF₁' hSol
      hSol' hm₀ hN hN' b hb hrc hX₁R hYR hn hn' hnS hnS' hnF hnF' hD hD' hraw hN2 νS β p₁ δ hρ hp
      hp' Φ Φ' hΦ hZm hv
  have hδ : ‖(0 : ℂ)‖ * markedRad d L N k a₁ κ ρ cc < δ₁ := by simpa using hC.δ₁_pos
  have hopen : IsOpen {v : ℂ | ‖v‖ * markedRad d L N k a₁ κ ρ cc < δ₁} :=
    isOpen_lt (by fun_prop) continuous_const
  have hd : deriv (fun v : ℂ => decMarkG (SB)
      (LocalCover.nbhdF m₀ (LocalCover.blockSite k (bc b))) m₀ k
        (LocalCover.fam m₀ (LocalCover.blockSite k (bc b))) a₁ ν cc F₁' Sol'
        (blockEnergyFun (GB) (HB) (compWeight L a₁) ν k (bc b))
          Zm' (bm '' Y) ρ hp' (rawOf D') v Φ') 0 =
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
    exact evDec_twoTorus hC hC' hk hGA hGB cc hcψ hMX hmar hαK hsm hF₁ hF₁' hSol hSol' hcov hX₁
      hcov' hX₁' hBM hRδ hRψ hΦ hX₁R ((htA Y).1 hY).2 hn hn' hnS hnS' hnF hnF' hΦan hD hD'
      hraw hψh hψh' hhat hZm hum

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
set_option hygiene false in
local notation "bc" => boxMap (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1)))
  (N₁' * L ^ m₁ * L ^ (k + 1 - (k + 1)))

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

/-- **D3: the determinant activity of a unit point on two tori, with or without the root cube.**
For a unit point `y` whose root cell lies in the box of radius `r` and a set `Y` of level-`(k+1)`
cubes with sites in the box, `detActivityBg D' (ιu y) (cubeMap '' Y) = detActivityBg D y Y`: if
`Y` contains the root cube this is `detActivityBg_twoTorus`; otherwise both activities vanish
(`detActivityBg_ne_zero_imp`; the root cube of `ιu y` is `cubeMap` of that of `y`,
`cubeMap_rootCube_unitPt`, and `cubeMap` is injective on the cubes of the box). -/
theorem detActivityBg_image_twoTorus (hN : L ^ m₀ ∣ N₁) (hN' : L ^ m₀ ∣ N₁')
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
    (Y : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) m₀ (k + 1)
      Set.univ)) {r : ℕ}
    (hroot : ∀ x ∈ rootSet m₀ (rootIdxOf y), InBox d r ((N₁ * L ^ m₁) * L ^ (k + 1)) x)
    (hYr : ∀ x ∈ sitesOf Y, InBox d r ((N₁ * L ^ m₁) * L ^ (k + 1)) x)
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
    detActivityBg m₀ (compWeight L a₁) a₁ ν (rho4 d L N BG κ) D' (ιu y)
        (Y.image (cubeMap hN hN' le_rfl)) =
      detActivityBg m₀ (compWeight L a₁) a₁ ν (rho4 d L N BG κ) D y Y := by
  have hcs : aK ≤ L * aK := cellSide_le_mul
  have hK1 : 1 ≤ L ^ (k + 1) := Nat.one_le_pow _ _ (Nat.pos_of_ne_zero (NeZero.ne L))
  have hr' : 2 * r + L * aK < (N₁' * L ^ m₁) * L ^ (k + 1) := by omega
  have hrc : InBox d r ((N₁ * L ^ m₁) * L ^ (k + 1)) (rootCube (m₀ := m₀) (rootIdxOf y)).1 :=
    hroot _ (mem_box_self _ (cellSide_pos m₀ m₁ _))
  by_cases hyY : rootCube (m₀ := m₀) (rootIdxOf y) ∈ Y
  · exact detActivityBg_twoTorus hN hN' hC hC' hk hδc hcap hsm hmar hαK hconn hconn' hD hD' y Y
      hyY hYr hn hn' hnS hnS' hnH hnH' hraw
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
      rw [cubeMap_cubeMap hN hN' le_rfl hr' (sitesOf_subset_box_of_mem hYr hc),
        cubeMap_cubeMap hN hN' le_rfl hr' hrc] at e
      rw [← e]
      exact hc
    rw [h1, h2]

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
  · exact (detActivityBg_image_twoTorus hN hN' hC hC' hk hδc hcap hsm hmar hαK hconn hconn' hD
      hD' y Y hroot (Finset.mem_filter.1 hY).2 hn hn' hnS hnS' hnH hnH' hraw).symm

/-- **D3: the determinant term of the root block on two tori** (the term
`E.term D T = ∑_{y ∈ B(z)} detActivityBg D y T` of the determinant record,
`exists_detExpansionLocC_rot`).  For a coarse root `z` (`|z| ≤ r_c`, `L^(k+1) (r_c + 1) ≤ r`)
whose root cell lies in the box of radius `r`, and a set `T` of level-`(k+1)` cubes with sites in
the box, the sum over the unit points of the block `B_{k+1}(bc z)` of the second torus of the
activities of `cubeMap '' T` equals the sum over the unit points of `B_{k+1}(z)` of the activities
of `T`.  The unit points correspond by `ιu` (`unitImage_val`, `unitImage_inj`; every unit point of
the image block is the image of a unit point of the block). -/
theorem sum_blockU_detActivityBg_twoTorus (hN : L ^ m₀ ∣ N₁) (hN' : L ^ m₀ ∣ N₁')
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
    (z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1)))) {rc r : ℕ}
    (hz : InBox d rc (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) z)
    (hrc : L ^ (k + 1) * rc + L ^ (k + 1) ≤ r)
    (hroot : ∀ x ∈ rootSet m₀ z, InBox d r ((N₁ * L ^ m₁) * L ^ (k + 1)) x)
    (Y : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) m₀ (k + 1)
      Set.univ))
    (hYr : ∀ x ∈ sitesOf Y, InBox d r ((N₁ * L ^ m₁) * L ^ (k + 1)) x)
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
    ∑ y' ∈ (Finset.univ.filter fun u : unitPts (GB) =>
        unitBlock1 (u : UnitTorus d L N₁' m₁ k) = bc z),
        detActivityBg m₀ (compWeight L a₁) a₁ ν (rho4 d L N BG κ) D' y'
          (Y.image (cubeMap hN hN' le_rfl)) =
      ∑ y ∈ (Finset.univ.filter fun u : unitPts (GA) =>
        unitBlock1 (u : UnitTorus d L N₁ m₁ k) = z),
        detActivityBg m₀ (compWeight L a₁) a₁ ν (rho4 d L N BG κ) D y Y := by
  have hK1 : 1 ≤ L ^ (k + 1) := Nat.one_le_pow _ _ (Nat.pos_of_ne_zero (NeZero.ne L))
  have hKm : L ^ (k + 1) ≤ L ^ (k + 1 + m₁) :=
    Nat.pow_le_pow_right (Nat.pos_of_ne_zero (NeZero.ne L)) (Nat.le_add_right _ _)
  have hn1 : 2 * r + 3 * L ^ (k + 1) + 5 < (N₁ * L ^ m₁) * L ^ (k + 1) := by omega
  have hn1' : 2 * r + 3 * L ^ (k + 1) + 5 < (N₁' * L ^ m₁) * L ^ (k + 1) := by omega
  have hpK : 0 < L ^ (k + 1) := pow_pos (Nat.pos_of_ne_zero (NeZero.ne L)) _
  have hdA : L ^ (k + 1) ∣ (N₁ * L ^ m₁) * L ^ (k + 1) := Dvd.intro_left _ rfl
  have hdB : L ^ (k + 1) ∣ (N₁' * L ^ m₁) * L ^ (k + 1) := Dvd.intro_left _ rfl
  -- the corner site of the block and the sites of the block
  set x₀ := LocalCover.blockSite k z with hx₀def
  have hx₀ : InBox d (L ^ (k + 1) * rc) ((N₁ * L ^ m₁) * L ^ (k + 1)) x₀ :=
    blockSite_inBox (N₁ := N₁) (by omega) z hz le_rfl
  have hbs : LocalCover.blockSite k (bc z) = bm x₀ :=
    blockSite_boxMap le_rfl z hz le_rfl (by omega)
  have hcell : ∀ x ∈ box (cbase (L ^ (k + 1)) x₀) (L ^ (k + 1)),
      InBox d r ((N₁ * L ^ m₁) * L ^ (k + 1)) x := fun x hx =>
    inBox_mono hrc (inBox_of_mem_cell (by omega) hx₀ hx)
  have hblk : ∀ x : CTorus d L N₁ m₁ (k + 1),
      jBlock d L (N₁ * L ^ m₁) (k + 1) (k + 1) x = z → InBox d r ((N₁ * L ^ m₁) * L ^ (k + 1)) x :=
    fun x hx => hcell x ((jBlock_eq_iff_mem_box le_rfl x x₀).1
      (hx.trans (LocalCover.jBlock_blockSite le_rfl z).symm))
  have hjB : jBlock d L (N₁' * L ^ m₁) (k + 1) (k + 1) (bm x₀) = bc z := by
    rw [← hbs]; exact LocalCover.jBlock_blockSite le_rfl (bc z)
  -- the unit points of the block
  have hmemA : ∀ y : unitPts (GA), unitBlock1 (y : UnitTorus d L N₁ m₁ k) = z →
      ∃ x : CTorus d L N₁ m₁ (k + 1), unitBlock x = (y : UnitTorus d L N₁ m₁ k) ∧
        jBlock d L (N₁ * L ^ m₁) (k + 1) (k + 1) x = z ∧
        InBox d r ((N₁ * L ^ m₁) * L ^ (k + 1)) x := by
    intro y hy
    obtain ⟨x, -, hx⟩ := (mem_unitPts _).1 y.2
    have hjx : jBlock d L (N₁ * L ^ m₁) (k + 1) (k + 1) x = z := by
      rw [← unitBlock1_unitBlock, hx, hy]
    exact ⟨x, hx, hjx, hblk x hjx⟩
  symm
  refine Finset.sum_nbij (fun y => ιu y) (fun y hy => ?_) (fun y1 hy1 y2 hy2 h => ?_)
    (fun y' hy' => ?_) (fun y hy => ?_)
  · have hy1 := (Finset.mem_filter.1 hy).2
    obtain ⟨x, hx, hjx, hxR⟩ := hmemA y hy1
    refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩
    show unitBlock1 ((ιu y : unitPts (GB)) : UnitTorus d L N₁' m₁ k) = bc z
    rw [unitImage_val (N₁' := N₁') hn1 y hx hxR, unitBlock1_unitBlock, ← hjB]
    have hx₀r : InBox d r ((N₁ * L ^ m₁) * L ^ (k + 1)) x₀ :=
      inBox_mono (by omega) hx₀
    exact (jBlock_boxMap_iff le_rfl hn1 hn1' hxR hx₀r).1
      (hjx.trans (LocalCover.jBlock_blockSite le_rfl z).symm)
  · obtain ⟨x1, hx1, -, hx1R⟩ := hmemA y1 (Finset.mem_filter.1 (Finset.mem_coe.1 hy1)).2
    obtain ⟨x2, hx2, -, hx2R⟩ := hmemA y2 (Finset.mem_filter.1 (Finset.mem_coe.1 hy2)).2
    exact unitImage_inj hn1 hn1' hx1 hx2 hx1R hx2R h
  · have hy1 := (Finset.mem_filter.1 (Finset.mem_coe.1 hy')).2
    obtain ⟨x', -, hx'⟩ := (mem_unitPts _).1 y'.2
    have hjx' : jBlock d L (N₁' * L ^ m₁) (k + 1) (k + 1) x' =
        jBlock d L (N₁' * L ^ m₁) (k + 1) (k + 1) (bm x₀) := by
      rw [hjB, ← unitBlock1_unitBlock, hx']
      exact hy1
    have hx'mem : x' ∈ box (cbase (L ^ (k + 1)) (bm x₀)) (L ^ (k + 1)) :=
      (jBlock_eq_iff_mem_box le_rfl x' (bm x₀)).1 hjx'
    have hcellr : ∀ x ∈ box (cbase (L ^ (k + 1)) x₀) (L ^ (k + 1)),
        InBox d (L ^ (k + 1) * rc + L ^ (k + 1)) ((N₁ * L ^ m₁) * L ^ (k + 1)) x :=
      fun x hx => inBox_of_mem_cell (by omega) hx₀ hx
    rw [← cbase_boxMap hdA hdB hpK (by omega) x₀ hcellr,
      ← image_box_boxMap (by omega) hpK hcellr] at hx'mem
    obtain ⟨x, hx, rfl⟩ := hx'mem
    have hjx : jBlock d L (N₁ * L ^ m₁) (k + 1) (k + 1) x = z :=
      ((jBlock_eq_iff_mem_box le_rfl x x₀).2 hx).trans (LocalCover.jBlock_blockSite le_rfl z)
    have hxR := hcell x hx
    refine ⟨⟨unitBlock x, mem_unitPts_levelTop (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k)
      (ϱ := ϱ) _⟩, Finset.mem_coe.2 (Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩), ?_⟩
    · show unitBlock1 (unitBlock x) = z
      rw [unitBlock1_unitBlock, hjx]
    · apply Subtype.ext
      rw [← hx']
      exact unitImage_val (N₁' := N₁') hn1 _ rfl hxR
  · have hy1 := (Finset.mem_filter.1 hy).2
    have hr : rootIdxOf y = z := (rootIdxOf_eq_unitBlock1 y).trans hy1
    refine (detActivityBg_image_twoTorus hN hN' hC hC' hk hδc hcap hsm hmar hαK hconn hconn' hD hD'
      y Y (fun x hx => hroot x (hr ▸ hx)) hYr hn hn' hnS hnS' hnH hnH' hraw).symm

end Det

/-! ### D3: the labels of the marks on two tori -/

section Labels

variable {d L N₁ N₁' m₁ k : ℕ} [NeZero N₁] [NeZero N₁'] [NeZero L]

set_option hygiene false in
local notation "bm" => boxMap ((N₁ * L ^ m₁) * L ^ (k + 1)) ((N₁' * L ^ m₁) * L ^ (k + 1))
set_option hygiene false in
local notation "bm'" => boxMap ((N₁' * L ^ m₁) * L ^ (k + 1)) ((N₁ * L ^ m₁) * L ^ (k + 1))
set_option hygiene false in
local notation "bc" => boxMap (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1)))
  (N₁' * L ^ m₁ * L ^ (k + 1 - (k + 1)))

omit [NeZero N₁] [NeZero N₁'] [NeZero L] in
/-- A neighbour of a site of the box of radius `r` lies in the box of radius `r + 1`. -/
theorem inBox_of_adj {r : ℕ} (hn : 2 * (r + 1) + 1 < (N₁ * L ^ m₁) * L ^ (k + 1))
    {x y : CTorus d L N₁ m₁ (k + 1)} (hx : InBox d r ((N₁ * L ^ m₁) * L ^ (k + 1)) x)
    (h : Adj x y) : InBox d (r + 1) ((N₁ * L ^ m₁) * L ^ (k + 1)) y := by
  obtain ⟨μ, h | h⟩ := h
  · rw [h]; exact inBox_add_single hn hx μ
  · have : y = x - Pi.single μ 1 := by rw [h]; abel
    rw [this]; exact inBox_sub_single hn hx μ

omit [NeZero N₁] [NeZero N₁'] [NeZero L] in
theorem inBox_of_mem_psiThick {r : ℕ} (hn : 2 * (r + 1) + 1 < (N₁ * L ^ m₁) * L ^ (k + 1))
    {Y : Set (CTorus d L N₁ m₁ (k + 1))} (hY : ∀ y ∈ Y, InBox d r ((N₁ * L ^ m₁) * L ^ (k + 1)) y)
    {y : CTorus d L N₁ m₁ (k + 1)} (h : y ∈ psiThick Y) :
    InBox d (r + 1) ((N₁ * L ^ m₁) * L ^ (k + 1)) y := by
  rcases h with h | ⟨x, hx, hxy⟩
  · exact inBox_mono (Nat.le_succ r) (hY y h)
  · exact inBox_of_adj hn (hY x hx) hxy

omit [NeZero N₁] [NeZero N₁'] [NeZero L] in
/-- **The set `Y` and its neighbours on two tori**: `psiThick (bm '' Y) = bm '' psiThick Y` for `Y`
in the box of radius `r`.  Margin: `2 (r + 1) + 1 < N₁ L^m₁ L^(k+1), N₁' L^m₁ L^(k+1)`. -/
theorem psiThick_image {r : ℕ} (hn : 2 * (r + 1) + 1 < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hn' : 2 * (r + 1) + 1 < (N₁' * L ^ m₁) * L ^ (k + 1))
    {Y : Set (CTorus d L N₁ m₁ (k + 1))}
    (hY : ∀ y ∈ Y, InBox d r ((N₁ * L ^ m₁) * L ^ (k + 1)) y) :
    psiThick (bm '' Y) = bm '' psiThick Y := by
  have hr1 : 2 * r + 1 < (N₁' * L ^ m₁) * L ^ (k + 1) := by omega
  ext y'
  constructor
  · rintro (⟨x, hx, rfl⟩ | ⟨_, ⟨x, hx, rfl⟩, hxy⟩)
    · exact ⟨x, Or.inl hx, rfl⟩
    · have hxR := hY x hx
      have hy'R : InBox d (r + 1) ((N₁' * L ^ m₁) * L ^ (k + 1)) y' :=
        inBox_of_adj hn' (inBox_boxMap hr1 hxR) hxy
      have hyR : InBox d (r + 1) ((N₁ * L ^ m₁) * L ^ (k + 1)) (bm' y') := inBox_boxMap hn hy'R
      have hbb : bm (bm' y') = y' := boxMap_boxMap hn hy'R
      refine ⟨bm' y', Or.inr ⟨x, hx, ?_⟩, hbb⟩
      have h1 : Nbr (bm x) (bm (bm' y')) := by rw [hbb]; exact hxy
      exact (nbr_boxMap_iff (by omega) hn' (inBox_mono (Nat.le_succ r) hxR) hyR).2 h1
  · rintro ⟨y, hy | ⟨x, hx, hxy⟩, rfl⟩
    · exact Or.inl ⟨y, hy, rfl⟩
    · refine Or.inr ⟨bm x, ⟨x, hx, rfl⟩, ?_⟩
      exact (nbr_boxMap_iff (by omega) hn' (inBox_mono (Nat.le_succ r) (hY x hx))
        (inBox_of_adj hn (hY x hx) hxy)).1 hxy

omit [NeZero N₁'] in
/-- The fine block of a coarse site is the box of side `L^(k+1)` at its corner site. -/
theorem fineBlock_eq_box (z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1)))) :
    fineBlock (m₁ := m₁) (K := k + 1) z =
      box (cbase (L ^ (k + 1)) (LocalCover.blockSite k z)) (L ^ (k + 1)) := by
  ext x
  show jBlock d L (N₁ * L ^ m₁) (k + 1) (k + 1) x = z ↔ _
  rw [← jBlock_eq_iff_mem_box le_rfl, LocalCover.jBlock_blockSite le_rfl z]

/-- **The fine block of a coarse site on two tori**: `bm '' fineBlock z = fineBlock (bc z)` for
`|z| ≤ r_c`, `L^(k+1) r_c ≤ ρ`.  Margin: `2 (ρ + L^(k+1)) + L^(k+1) < N₁ L^m₁ L^(k+1)` and
`2 ρ + 1 < N₁' L^m₁ L^(k+1)`. -/
theorem fineBlock_image {ρ rc : ℕ}
    (hn : 2 * (ρ + L ^ (k + 1)) + L ^ (k + 1) < (N₁ * L ^ m₁) * L ^ (k + 1))
    (z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))))
    (hz : InBox d rc (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) z) (hrc : L ^ (k + 1) * rc ≤ ρ) :
    bm '' fineBlock (m₁ := m₁) (K := k + 1) z = fineBlock (m₁ := m₁) (K := k + 1) (bc z) := by
  have hpK : 0 < L ^ (k + 1) := pow_pos (Nat.pos_of_ne_zero (NeZero.ne L)) _
  have hx₀ := blockSite_inBox (N₁ := N₁) (by omega) z hz hrc
  have hcell : ∀ x ∈ box (cbase (L ^ (k + 1)) (LocalCover.blockSite k z)) (L ^ (k + 1)),
      InBox d (ρ + L ^ (k + 1)) ((N₁ * L ^ m₁) * L ^ (k + 1)) x :=
    fun x hx => inBox_of_mem_cell (by omega) hx₀ hx
  rw [fineBlock_eq_box, fineBlock_eq_box, image_box_boxMap hn hpK hcell,
    cbase_boxMap (Dvd.intro_left _ rfl) (Dvd.intro_left _ rfl) hpK (by omega) _ hcell,
    blockSite_boxMap le_rfl z hz hrc (by omega)]

set_option hygiene false in
local notation "aK" => cellSide L m₀ m₁ (k + 1)

omit [NeZero N₁] [NeZero N₁'] [NeZero L] in
/-- A box of the box of radius `ρ` is contained in the image of a set `Y` of the box iff it is the
image of a box contained in `Y`. -/
theorem box_subset_image_iff {ρ a : ℕ} (hn : 2 * ρ + a < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hn' : 2 * ρ + 1 < (N₁' * L ^ m₁) * L ^ (k + 1)) (ha : 0 < a)
    {Y : Set (CTorus d L N₁ m₁ (k + 1))} (hY : ∀ y ∈ Y, InBox d ρ ((N₁ * L ^ m₁) * L ^ (k + 1)) y)
    {c : CTorus d L N₁ m₁ (k + 1)}
    (hc : ∀ x ∈ box c a, InBox d ρ ((N₁ * L ^ m₁) * L ^ (k + 1)) x) :
    box (bm c) a ⊆ bm '' Y ↔ box c a ⊆ Y := by
  rw [← image_box_boxMap hn ha hc]
  constructor
  · intro h x hx
    obtain ⟨y, hy, hyx⟩ := h ⟨x, hx, rfl⟩
    have := boxMap_inj (hm' := hn') (hY y hy) (hc x hx) hyx
    exact this ▸ hy
  · exact Set.image_mono

/-- **The root cube is a cube of `Y` on two tori**: `rootCube (bc z)` is a cube of `bm '' Y` iff
`rootCube z` is a cube of `Y`, when the root cell and `Y` lie in the box of radius `r`
(`|z| ≤ r_c`, `L^(k+1) r_c ≤ r`).  Margins: `2 r + a_K < N₁ L^m₁ L^(k+1)`,
`2 r + 1 < N₁' L^m₁ L^(k+1)`. -/
theorem rootCube_mem_blocksOf_image_iff {m₀ : ℕ} (hN : L ^ m₀ ∣ N₁) (hN' : L ^ m₀ ∣ N₁')
    {r rc : ℕ} (hn : 2 * r + aK < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hn' : 2 * r + 1 < (N₁' * L ^ m₁) * L ^ (k + 1))
    (z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))))
    (hz : InBox d rc (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) z) (hrc : L ^ (k + 1) * rc ≤ r)
    (hroot : ∀ x ∈ rootSet m₀ z, InBox d r ((N₁ * L ^ m₁) * L ^ (k + 1)) x)
    {Y : Set (CTorus d L N₁ m₁ (k + 1))}
    (hY : ∀ y ∈ Y, InBox d r ((N₁ * L ^ m₁) * L ^ (k + 1)) y) :
    rootCube (m₀ := m₀) (bc z) ∈ blocksOf m₀ (k + 1) Set.univ (bm '' Y) ↔
      rootCube (m₀ := m₀) z ∈ blocksOf m₀ (k + 1) Set.univ Y := by
  rw [← cubeMap_rootCube hN hN' z hz hrc hn hroot, mem_blocksOf, mem_blocksOf, cubeMap_val]
  exact box_subset_image_iff hn hn' (cellSide_pos m₀ m₁ _) hY hroot

/-- **The cubes joining `Y` to the root on two tori**: `joinCubes (bc z) (bm '' Y)` is the image of
`joinCubes z Y`, when the root cell and `Y` lie in the box of radius `r`.  The cubes through the
root cube lie in the box of radius `r + 2 L a_K`.  Margins: `2 (r + 2 L a_K) + L a_K` below
`N₁ L^m₁ L^(k+1)` and `N₁' L^m₁ L^(k+1)`. -/
theorem joinCubes_image {m₀ : ℕ} (hN : L ^ m₀ ∣ N₁) (hN' : L ^ m₀ ∣ N₁') {r rc : ℕ}
    (hnH : 2 * (r + 2 * (L * aK)) + L * aK < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hnH' : 2 * (r + 2 * (L * aK)) + L * aK < (N₁' * L ^ m₁) * L ^ (k + 1))
    (z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))))
    (hz : InBox d rc (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) z) (hrc : L ^ (k + 1) * rc ≤ r)
    (hroot : ∀ x ∈ rootSet m₀ z, InBox d r ((N₁ * L ^ m₁) * L ^ (k + 1)) x)
    {Y : Set (CTorus d L N₁ m₁ (k + 1))}
    (hY : ∀ y ∈ Y, InBox d r ((N₁ * L ^ m₁) * L ^ (k + 1)) y) :
    joinCubes m₀ (bc z) (bm '' Y) = (joinCubes m₀ z Y).image bm := by
  have hcs : aK ≤ L * aK := cellSide_le_mul
  have ha0 : 0 < aK := cellSide_pos m₀ m₁ _
  have hLa : 0 < L * aK := Nat.mul_pos (Nat.pos_of_ne_zero (NeZero.ne L)) ha0
  have hdA := cellSide_dvd (L := L) (m₁ := m₁) (K := k + 1) hN (le_refl (k + 1))
  have hdB := cellSide_dvd (L := L) (m₁ := m₁) (K := k + 1) hN' (le_refl (k + 1))
  set rb := (rootCube (m₀ := m₀) z).1 with hrb
  have hrbR : InBox d r ((N₁ * L ^ m₁) * L ^ (k + 1)) rb := hroot _ (mem_box_self _ ha0)
  have hrb' : (rootCube (m₀ := m₀) (bc z)).1 = bm rb := by
    rw [← cubeMap_rootCube hN hN' z hz hrc (by omega) hroot, cubeMap_val]
  -- the cubes through the root cube, on each torus
  have hpA : ∀ p : CTorus d L N₁ m₁ (k + 1), rb ∈ box p (L * aK) →
      ∀ x ∈ box p (L * aK), InBox d (r + L * aK + L * aK) ((N₁ * L ^ m₁) * L ^ (k + 1)) x :=
    fun p hp x hx => inBox_of_mem_box_right (by omega) (inBox_of_mem_box_left (by omega) hrbR hp) hx
  have hpB : ∀ p' : CTorus d L N₁' m₁ (k + 1), bm rb ∈ box p' (L * aK) →
      ∀ x ∈ box p' (L * aK), InBox d (r + L * aK + L * aK) ((N₁' * L ^ m₁) * L ^ (k + 1)) x :=
    fun p' hp' x hx => inBox_of_mem_box_right (by omega)
      (inBox_of_mem_box_left (by omega) (inBox_boxMap (by omega) hrbR) hp') hx
  have hYimg : bm' '' (bm '' Y) = Y := image_image_boxMap (by omega) hY
  ext p'
  simp only [joinCubes, rootCubes, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_image]
  constructor
  · rintro ⟨⟨hal', hroot'⟩, t', htal', ht'⟩
    rw [hrb'] at hroot'
    have hbox' := hpB p' hroot'
    have himg' : bm' '' box p' (L * aK) = box (bm' p') (L * aK) :=
      image_box_boxMap (by omega) hLa hbox'
    have hpp : bm (bm' p') = p' :=
      boxMap_boxMap (by omega) (hbox' p' (mem_box_self _ hLa))
    refine ⟨bm' p', ⟨⟨aligned_boxMap hdB hdA hal', ?_⟩, bm' t', aligned_boxMap hdB hdA htal', ?_⟩,
      hpp⟩
    · rw [← himg']
      exact ⟨bm rb, hroot', boxMap_boxMap (by omega) hrbR⟩
    · have htbox : ∀ x ∈ box t' aK, InBox d (r + L * aK + L * aK) ((N₁' * L ^ m₁) * L ^ (k + 1)) x :=
        fun x hx => hbox' x (ht' hx).2
      rw [← image_box_boxMap (by omega) ha0 htbox, ← himg', ← hYimg]
      intro x hx
      obtain ⟨w, hw, rfl⟩ := hx
      exact ⟨⟨w, (ht' hw).1, rfl⟩, ⟨w, (ht' hw).2, rfl⟩⟩
  · rintro ⟨p, ⟨⟨hal, hrp⟩, t, htal, ht⟩, rfl⟩
    have hbox := hpA p hrp
    have himg : bm '' box p (L * aK) = box (bm p) (L * aK) := image_box_boxMap (by omega) hLa hbox
    refine ⟨⟨aligned_boxMap hdA hdB hal, ?_⟩, bm t, aligned_boxMap hdA hdB htal, ?_⟩
    · rw [hrb', ← himg]
      exact ⟨rb, hrp, rfl⟩
    · have htbox : ∀ x ∈ box t aK, InBox d (r + L * aK + L * aK) ((N₁ * L ^ m₁) * L ^ (k + 1)) x :=
        fun x hx => hbox x (ht hx).2
      rw [← image_box_boxMap (by omega) ha0 htbox, ← himg]
      rintro _ ⟨w, hw, rfl⟩
      exact ⟨⟨w, (ht hw).1, rfl⟩, ⟨w, (ht hw).2, rfl⟩⟩

/-- **The bridge of `Y` to the root on two tori**: `bridge (bc z) (bm '' Y) = bm '' bridge z Y`,
when the root cell and `Y` lie in the box of radius `r` (`|z| ≤ r_c`, `L^(k+1) r_c ≤ r`).
Margins: `2 (r + 2 L a_K) + L a_K` below `N₁ L^m₁ L^(k+1)` and `N₁' L^m₁ L^(k+1)`. -/
theorem bridge_image {m₀ : ℕ} (hN : L ^ m₀ ∣ N₁) (hN' : L ^ m₀ ∣ N₁') {r rc : ℕ}
    (hnH : 2 * (r + 2 * (L * aK)) + L * aK < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hnH' : 2 * (r + 2 * (L * aK)) + L * aK < (N₁' * L ^ m₁) * L ^ (k + 1))
    (z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))))
    (hz : InBox d rc (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) z) (hrc : L ^ (k + 1) * rc ≤ r)
    (hroot : ∀ x ∈ rootSet m₀ z, InBox d r ((N₁ * L ^ m₁) * L ^ (k + 1)) x)
    {Y : Set (CTorus d L N₁ m₁ (k + 1))}
    (hY : ∀ y ∈ Y, InBox d r ((N₁ * L ^ m₁) * L ^ (k + 1)) y) :
    bridge m₀ (bc z) (bm '' Y) = bm '' bridge m₀ z Y := by
  have hcs : aK ≤ L * aK := cellSide_le_mul
  have hLa : 0 < L * aK :=
    Nat.mul_pos (Nat.pos_of_ne_zero (NeZero.ne L)) (cellSide_pos m₀ m₁ _)
  have hiff := rootCube_mem_blocksOf_image_iff hN hN' (by omega) (by omega) z hz hrc hroot hY
  unfold bridge
  by_cases h : rootCube (m₀ := m₀) z ∈ blocksOf m₀ (k + 1) Set.univ Y
  · simp only [hiff.2 h, h, ↓reduceIte]
  · have h' : rootCube (m₀ := m₀) (bc z) ∉ blocksOf m₀ (k + 1) Set.univ (bm '' Y) :=
      fun h' => h (hiff.1 h')
    simp only [h, h', ↓reduceIte]
    rw [joinCubes_image hN hN' hnH hnH' z hz hrc hroot hY, Set.image_union, Set.image_iUnion₂,
      Finset.set_biUnion_finset_image]
    congr 1
    refine Set.iUnion₂_congr fun p hp => ?_
    have hrbR : InBox d r ((N₁ * L ^ m₁) * L ^ (k + 1)) (rootCube (m₀ := m₀) z).1 :=
      hroot _ (mem_box_self _ (cellSide_pos m₀ m₁ _))
    have hrp := (Finset.mem_filter.1 (Finset.mem_filter.1 hp).1).2.2
    exact (image_box_boxMap (by omega) hLa fun x hx =>
      inBox_of_mem_box_right (by omega) (inBox_of_mem_box_left (by omega) hrbR hrp) hx).symm

omit [NeZero N₁'] in
/-- **The coarse site of a block whose corner site lies in the box.**  If the corner site
`blockSite k b` of the block `B_{k+1}(b)` lies in the box of radius `r`, then
`|b| ≤ r / L^(k+1)` in centred coarse coordinates. -/
theorem inBox_coarse_of_blockSite {r : ℕ} (b : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))))
    (h : InBox d r ((N₁ * L ^ m₁) * L ^ (k + 1)) (LocalCover.blockSite k b)) :
    InBox d (r / L ^ (k + 1)) (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) b := by
  have : NeZero (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) :=
    ⟨by have := NeZero.pos N₁; have := NeZero.pos L; positivity⟩
  have hside := side_eq (N₀ := N₁ * L ^ m₁) (L := L) (le_refl (k + 1))
  have hpK : 0 < L ^ (k + 1) := pow_pos (Nat.pos_of_ne_zero (NeZero.ne L)) _
  intro μ
  set v := (b μ).valMinAbs with hv
  have e : (LocalCover.blockSite k b μ) =
      ((((L ^ (k + 1) : ℕ) : ℤ) * v : ℤ) : ZMod ((N₁ * L ^ m₁) * L ^ (k + 1))) := by
    have hzμ : b μ = ((v : ℤ) : ZMod (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1)))) :=
      (ZMod.coe_valMinAbs _).symm
    show ((L ^ (k + 1) * (b μ).val : ℕ) : ZMod ((N₁ * L ^ m₁) * L ^ (k + 1))) = _
    conv_lhs => rw [hzμ]
    exact rootCoord_intCast hside _
  have hIoc := ZMod.valMinAbs_mem_Ioc (b μ)
  rw [← hv] at hIoc
  have hval : (LocalCover.blockSite k b μ).valMinAbs = ((L ^ (k + 1) : ℕ) : ℤ) * v := by
    rw [e, ZMod.valMinAbs_spec]
    refine ⟨rfl, ?_, ?_⟩
    · have h1 := hIoc.1
      have hc : (((N₁ * L ^ m₁) * L ^ (k + 1) : ℕ) : ℤ) =
          ((L ^ (k + 1) : ℕ) : ℤ) * ((N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1)) : ℕ) : ℤ) := by
        rw [hside]; push_cast; ring
      rw [hc]
      have hp : (0 : ℤ) < ((L ^ (k + 1) : ℕ) : ℤ) := by exact_mod_cast hpK
      nlinarith
    · have h1 := hIoc.2
      have hc : (((N₁ * L ^ m₁) * L ^ (k + 1) : ℕ) : ℤ) =
          ((L ^ (k + 1) : ℕ) : ℤ) * ((N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1)) : ℕ) : ℤ) := by
        rw [hside]; push_cast; ring
      rw [hc]
      have hp : (0 : ℤ) < ((L ^ (k + 1) : ℕ) : ℤ) := by exact_mod_cast hpK
      nlinarith
  have h1 := h μ
  rw [hval, abs_mul, Nat.abs_cast] at h1
  have hp : (0 : ℤ) < ((L ^ (k + 1) : ℕ) : ℤ) := by exact_mod_cast hpK
  have h2 : |v| ≤ ((r : ℤ) / ((L ^ (k + 1) : ℕ) : ℤ)) :=
    (Int.le_ediv_iff_mul_le hp).2 (by linarith)
  have h3 : ((r / L ^ (k + 1) : ℕ) : ℤ) = (r : ℤ) / ((L ^ (k + 1) : ℕ) : ℤ) := by
    push_cast; rfl
  rw [h3]
  exact h2

omit [NeZero N₁] [NeZero N₁'] in
/-- The coarse margin: `2 (r / L^(k+1)) + 1 < N₁ L^m₁` from `2 r + L^(k+1) < N₁ L^m₁ L^(k+1)`. -/
theorem coarse_margin {r : ℕ} (hn : 2 * r + L ^ (k + 1) < (N₁ * L ^ m₁) * L ^ (k + 1)) :
    2 * (r / L ^ (k + 1)) + 1 < N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1)) := by
  have hpK : 0 < L ^ (k + 1) := pow_pos (Nat.pos_of_ne_zero (NeZero.ne L)) _
  have h0 : k + 1 - (k + 1) = 0 := Nat.sub_self _
  rw [h0, pow_zero, mul_one]
  have h1 : L ^ (k + 1) * (r / L ^ (k + 1)) ≤ r := Nat.mul_div_le r _
  have h2 : L ^ (k + 1) * (2 * (r / L ^ (k + 1)) + 1) < L ^ (k + 1) * (N₁ * L ^ m₁) := by
    rw [mul_comm (L ^ (k + 1)) (N₁ * L ^ m₁)]
    calc L ^ (k + 1) * (2 * (r / L ^ (k + 1)) + 1)
        = 2 * (L ^ (k + 1) * (r / L ^ (k + 1))) + L ^ (k + 1) := by ring
      _ ≤ 2 * r + L ^ (k + 1) := by omega
      _ < (N₁ * L ^ m₁) * L ^ (k + 1) := hn
  exact Nat.lt_of_mul_lt_mul_left h2

omit [NeZero N₁] [NeZero N₁'] [NeZero L] in
/-- The image map of sets of the box of radius `ρ` is injective. -/
theorem image_boxMap_inj {ρ : ℕ} (hn' : 2 * ρ + 1 < (N₁' * L ^ m₁) * L ^ (k + 1))
    {A B : Set (CTorus d L N₁ m₁ (k + 1))}
    (hA : ∀ x ∈ A, InBox d ρ ((N₁ * L ^ m₁) * L ^ (k + 1)) x)
    (hB : ∀ x ∈ B, InBox d ρ ((N₁ * L ^ m₁) * L ^ (k + 1)) x) (h : bm '' A = bm '' B) : A = B := by
  rw [← image_image_boxMap hn' hA, h, image_image_boxMap hn' hB]

omit [NeZero N₁'] in
/-- `Y` lies in its bridge to the root. -/
theorem subset_bridge (m₀ : ℕ) (z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))))
    (Y : Set (CTorus d L N₁ m₁ (k + 1))) : Y ⊆ bridge m₀ z Y := by
  unfold bridge
  split_ifs
  · exact subset_rfl
  · exact Set.subset_union_left

omit [NeZero N₁'] in
/-- The bridge of a set of the box of radius `r` lies in the box of radius `r + 2 L a_K`, when the
root cell lies in the box of radius `r`. -/
theorem inBox_of_mem_bridge {m₀ r : ℕ}
    (hnH : 2 * (r + 2 * (L * aK)) + 1 < (N₁ * L ^ m₁) * L ^ (k + 1))
    (z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))))
    (hroot : ∀ x ∈ rootSet m₀ z, InBox d r ((N₁ * L ^ m₁) * L ^ (k + 1)) x)
    {Y : Set (CTorus d L N₁ m₁ (k + 1))}
    (hY : ∀ y ∈ Y, InBox d r ((N₁ * L ^ m₁) * L ^ (k + 1)) y) :
    ∀ x ∈ bridge m₀ z Y, InBox d (r + 2 * (L * aK)) ((N₁ * L ^ m₁) * L ^ (k + 1)) x := by
  have hrbR : InBox d r ((N₁ * L ^ m₁) * L ^ (k + 1)) (rootCube (m₀ := m₀) z).1 :=
    hroot _ (mem_box_self _ (cellSide_pos m₀ m₁ _))
  intro x hx
  unfold bridge at hx
  split_ifs at hx
  · exact inBox_mono (by omega) (hY x hx)
  · rcases hx with hx | hx
    · exact inBox_mono (by omega) (hY x hx)
    · obtain ⟨p, hp, hxp⟩ := Set.mem_iUnion₂.1 hx
      have hrp := (Finset.mem_filter.1 (Finset.mem_filter.1 hp).1).2.2
      have := inBox_of_mem_box_right (by omega) (inBox_of_mem_box_left (by omega) hrbR hrp) hxp
      exact inBox_mono (by omega) this

omit [NeZero N₁'] in
/-- The region `X₁` of a block lies in each domain of its expansion. -/
theorem nbhd_subset_of_mem_polyDom {m₀ : ℕ} (hN : L ^ m₀ ∣ N₁) {ϱ : ℝ}
    (x : CTorus d L N₁ m₁ (k + 1)) {Y : Set (CTorus d L N₁ m₁ (k + 1))}
    (hY : Y ∈ polyDom (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ)
      (k + 1) le_rfl) (LocalCover.nbhdF m₀ x) m₀ k (LocalCover.fam m₀ x)) :
    LocalCover.nbhd m₀ x ⊆ Y := by
  obtain ⟨C, -, rfl⟩ := Finset.mem_image.1 hY
  rw [← LocalCover.X1_eq (isLevel_levelGS (Nat.le_add_left 1 k) le_rfl) hN le_rfl x]
  exact subset_Ysites _ _

end Labels

end Balaban.Polymer.TwoTorusStep
