/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Def7SmallField
public import Balaban.Localization.TreeLengthDiam
public import Balaban.SmallField.PsiGeomPath
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The halo distance: a polymer leaving the halo `Y^≈` is large (`regionalHaloDistance`)

Geometry only.  This file proves that a polymer of the inherited scale `j` which contains a
site over a region `Y` of cubes of `𝕋_k` and a site outside the fine set of the thickening
`thickY R Y = Y^≈` (a thickening at the current scale `k`, by `⌊R_{k-1}⌋ + 1` cubes) has covering
size `sizeJ m₀ j X` at least
`(⌊R_{k-1}⌋ + 1) · L^k M / L^(j + m₀ + m₁) − 2 L`.
Here `L^k M` is the number of fine sites per side of a cube of `𝕋_k` and `L^(j+m₀+m₁)` is the
cell side `a_j` of `𝒟_j`; for `j ≤ k` the ratio is `c_h L^(k-j)` with `c_h = M / L^(m₀+m₁)`.

The coefficient bounds and the regional estimate that use this inequality are not proved here.
The distance is the cyclic index distance `supDist` of the torus, so wraparound needs no
separate treatment.
-/

@[expose] public section

namespace Balaban.LargeField.Def7

open Balaban Balaban.Multiscale Balaban.Localization Balaban.SmallField Balaban.LargeField

section Blocks

/-- The residue of a coordinate after a cast along an equality of torus sizes has the same
representative. -/
theorem val_torusCast {d a b : ℕ} (h : a = b) (x : Torus d a) (i : Fin d) :
    (torusCast h x i).val = (x i).val := by
  subst h; rfl

/-- The block coordinate only depends on the representative, hence is unchanged by a cast. -/
theorem blockCoord_torusCast {d a b : ℕ} (N m : ℕ) (h : a = b) (x : Torus d a) (i : Fin d) :
    blockCoord N m (torusCast h x i) = blockCoord N m (x i) := by
  unfold blockCoord; rw [val_torusCast]

/-- Block coordinates of two residues at cyclic distance at most `δ` are at cyclic distance at
most `⌊δ / σ⌋ + 1` (blocks of side `σ`, `T = σ m` sites). -/
theorem cycNorm_blockCoord_sub_le {T σ m : ℕ} [NeZero T] [NeZero m] (hσ : 0 < σ)
    (hT : T = σ * m) (a b : ZMod T) {δ : ℕ} (h : cycNorm T (a - b) ≤ δ) :
    cycNorm m (blockCoord σ m a - blockCoord σ m b) ≤ δ / σ + 1 := by
  obtain ⟨t, ht, hta⟩ := (cycNorm_le_iff (a - b) δ).1 h
  have hdvd : (T : ℤ) ∣ (a.val : ℤ) - (b.val : ℤ) - t := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [hta]
    simp
  obtain ⟨c, hc⟩ := hdvd
  have hA := Nat.div_add_mod a.val σ
  have hB := Nat.div_add_mod b.val σ
  have hD := Nat.div_add_mod δ σ
  have hrA : a.val % σ < σ := Nat.mod_lt _ hσ
  have hrB : b.val % σ < σ := Nat.mod_lt _ hσ
  have hrδ : δ % σ < σ := Nat.mod_lt _ hσ
  have hTz : (T : ℤ) = σ * m := by exact_mod_cast hT
  obtain ⟨qA, hqA⟩ : ∃ q : ℤ, q = ((a.val / σ : ℕ) : ℤ) := ⟨_, rfl⟩
  obtain ⟨qB, hqB⟩ : ∃ q : ℤ, q = ((b.val / σ : ℕ) : ℤ) := ⟨_, rfl⟩
  obtain ⟨D, hDD⟩ : ∃ q : ℤ, q = ((δ / σ : ℕ) : ℤ) := ⟨_, rfl⟩
  have hAz : (σ : ℤ) * qA + ((a.val % σ : ℕ) : ℤ) = a.val := by rw [hqA]; exact_mod_cast hA
  have hBz : (σ : ℤ) * qB + ((b.val % σ : ℕ) : ℤ) = b.val := by rw [hqB]; exact_mod_cast hB
  have hDz : (σ : ℤ) * D + ((δ % σ : ℕ) : ℤ) = δ := by rw [hDD]; exact_mod_cast hD
  set q' : ℤ := qA - qB - m * c with hq'
  have hσz : (0 : ℤ) < σ := by exact_mod_cast hσ
  have key : (σ : ℤ) * q' = ((b.val % σ : ℕ) : ℤ) + t - ((a.val % σ : ℕ) : ℤ) := by
    rw [hq']
    have : (a.val : ℤ) - b.val - t = σ * m * c := by rw [hc, hTz]
    linear_combination hAz - hBz + this
  have hrA0 : (0 : ℤ) ≤ ((a.val % σ : ℕ) : ℤ) := by positivity
  have hrB0 : (0 : ℤ) ≤ ((b.val % σ : ℕ) : ℤ) := by positivity
  have hrδ0 : (0 : ℤ) ≤ ((δ % σ : ℕ) : ℤ) := by positivity
  have hrA1 : ((a.val % σ : ℕ) : ℤ) < σ := by exact_mod_cast hrA
  have hrB1 : ((b.val % σ : ℕ) : ℤ) < σ := by exact_mod_cast hrB
  have hrδ1 : ((δ % σ : ℕ) : ℤ) < σ := by exact_mod_cast hrδ
  have htabs := abs_le.1 ht
  have hδ : (δ : ℤ) < σ * (D + 1) := by nlinarith
  have hup : q' ≤ D + 1 := by
    by_contra hcon
    have : (D + 2 : ℤ) ≤ q' := by omega
    nlinarith
  have hlo : -(D + 1) ≤ q' := by
    by_contra hcon
    have : q' ≤ -(D + 2) := by omega
    nlinarith
  rw [cycNorm_le_iff]
  refine ⟨q', ?_, ?_⟩
  · rw [abs_le, Nat.cast_add, ← hDD, Nat.cast_one]; constructor <;> linarith
  · unfold blockCoord
    rw [hq', hqA, hqB]
    simp only [Int.cast_sub, Int.cast_mul, Int.cast_natCast, ZMod.natCast_self]
    ring

end Blocks

section Halo

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {M K : ℕ} [NeZero M]
  [NeZero S.L] {N k m₁ : ℕ} {ϱ : ℝ} (C : SFCtx S n R M K N k m₁ ϱ)

/-- The cube of `𝕋_k` over a site of the Def-6 torus is read from the representative:
`⌊x_i / (L^k M)⌋`. -/
theorem cubeMap_sfToBg (x : Localization.CTorus S.d S.L C.N₁ m₁ k) (i : Fin S.d) :
    cubeMap n S.L M K k (bgToFine C.geo C.hnn C.hkK (sfToBg C.geo C.hT x)) i =
      blockCoord (S.L ^ k * M) (n k) (x i) := by
  unfold cubeMap blockMap bgToFine sfToBg
  rw [blockCoord_torusCast, blockCoord_torusCast]

/-- **Fine sites per side of a cube of `𝕋_k`**: the side of the cube is `σ_k = L^k M` sites of
the Def-6 torus, and the Def-6 torus has `σ_k n_k` sites per side. -/
theorem side_eq_sigma : C.N₁ * S.L ^ m₁ * S.L ^ k = (S.L ^ k * M) * n k := by
  have hM := C.geo.hM
  rw [C.hT]
  calc _ = (C.geo.c * C.geo.M1) * S.L ^ k * n k := by ring
    _ = _ := by rw [← hM]; ring

/-- **Halo separation** (T2): a site over `Y` and a site not over the thickening
`thick r Y = nbhd (r+1) Y` are at index distance at least `(r + 1) · L^k M`. -/
theorem sset_dist_of_not_mem_thick {Y : Set (Torus S.d (n k))} {r : ℕ}
    {y x : Localization.CTorus S.d S.L C.N₁ m₁ k} (hy : y ∈ C.sset Y)
    (hx : x ∉ C.sset (thick r Y)) :
    (r + 1) * (S.L ^ k * M) ≤ supDist y x := by
  have hσ : 0 < S.L ^ k * M :=
    Nat.mul_pos (pow_pos (Nat.pos_of_ne_zero (NeZero.ne S.L)) _) (Nat.pos_of_ne_zero (NeZero.ne M))
  unfold SFCtx.sset sfSet at hy hx
  simp only [Set.mem_ofPred_eq] at hy hx
  have hF : supDist (cubeMap n S.L M K k (bgToFine C.geo C.hnn C.hkK (sfToBg C.geo C.hT x)))
      (cubeMap n S.L M K k (bgToFine C.geo C.hnn C.hkK (sfToBg C.geo C.hT y))) ≤
        supDist y x / (S.L ^ k * M) + 1 := by
    rw [supDist_le_iff]
    intro i
    rw [cubeMap_sfToBg, cubeMap_sfToBg]
    refine cycNorm_blockCoord_sub_le hσ (side_eq_sigma C) (x i) (y i) ?_
    rw [← cycNorm_neg, neg_sub]
    exact cycNorm_le_supDist y x i
  have hnot : ¬ supDist
      (cubeMap n S.L M K k (bgToFine C.geo C.hnn C.hkK (sfToBg C.geo C.hT x)))
      (cubeMap n S.L M K k (bgToFine C.geo C.hnn C.hkK (sfToBg C.geo C.hT y))) ≤ r + 1 := by
    intro h
    exact hx (mem_nbhd.2 ⟨_, hy, h⟩)
  have h1 : r + 1 ≤ supDist y x / (S.L ^ k * M) := by omega
  exact (Nat.le_div_iff_mul_le hσ).1 h1

/-- **Halo distance for a pair of sites** (T4, in the form of `farCrossing`): if a polymer
`X ∈ 𝒟_j` contains a site `y` over `Y` and a site `x` not over the thickening `Y^≈`, then
`sizeJ m₀ j X ≥ (⌊R_{k-1}⌋ + 1) · L^k M / L^(j+m₀+m₁) - 2 L`. -/
theorem sizeJ_ge_of_halo_pair {Y : Set (Torus S.d (n k))} {j : ℕ} {X : Set (Localization.CTorus S.d S.L C.N₁ m₁ k)}
    (hX : Def6.IsPolyDom C.m₀ j X) {y x : Localization.CTorus S.d S.L C.N₁ m₁ k}
    (hyX : y ∈ X) (hxX : x ∈ X) (hy : y ∈ C.sset Y) (hx : x ∉ C.sset (thickY R Y)) :
    ((⌊R (k - 1)⌋₊ : ℝ) + 1) * (((S.L : ℝ) ^ k * M) / (S.L : ℝ) ^ (j + C.m₀ + m₁)) - 2 * S.L ≤
      Def6.sizeJ C.m₀ j X := by
  have h1 := treeLenCovOne_ge_dist (L := S.L) (N₁ := C.N₁) (m₁ := m₁) (K := k) C.m₀ j
    (exists_cover_struct (m₀ := C.m₀) (j := j) hX) hyX hxX
  have h2 : (⌊R (k - 1)⌋₊ + 1) * (S.L ^ k * M) ≤ supDist y x :=
    sset_dist_of_not_mem_thick C hy hx
  have h3 : (((⌊R (k - 1)⌋₊ : ℝ) + 1) * ((S.L : ℝ) ^ k * M)) ≤ (supDist y x : ℝ) := by
    exact_mod_cast h2
  have hpos : (0 : ℝ) < (S.L : ℝ) ^ (j + C.m₀ + m₁) := by
    have : (0 : ℝ) < S.L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne S.L)
    positivity
  have h4 : ((⌊R (k - 1)⌋₊ : ℝ) + 1) * (((S.L : ℝ) ^ k * M) / (S.L : ℝ) ^ (j + C.m₀ + m₁)) ≤
      (supDist y x : ℝ) / (S.L : ℝ) ^ (j + C.m₀ + m₁) := by
    rw [← mul_div_assoc]
    exact div_le_div_of_nonneg_right h3 hpos.le
  unfold Def6.sizeJ
  linarith

/-- **`regionalHaloDistance`** (T3): a polymer `X ∈ 𝒟_j` containing a site over `Y` and not
contained in the fine set of `Y^≈` has `sizeJ m₀ j X ≥ (⌊R_{k-1}⌋ + 1) · L^k M / L^(j+m₀+m₁) - 2 L`. -/
theorem sizeJ_ge_of_not_subset_thickY {Y : Set (Torus S.d (n k))} {j : ℕ}
    {X : Set (Localization.CTorus S.d S.L C.N₁ m₁ k)} (hX : Def6.IsPolyDom C.m₀ j X)
    {y : Localization.CTorus S.d S.L C.N₁ m₁ k} (hyX : y ∈ X) (hy : y ∈ C.sset Y)
    (hnot : ¬ X ⊆ C.sset (thickY R Y)) :
    ((⌊R (k - 1)⌋₊ : ℝ) + 1) * (((S.L : ℝ) ^ k * M) / (S.L : ℝ) ^ (j + C.m₀ + m₁)) - 2 * S.L ≤
      Def6.sizeJ C.m₀ j X := by
  obtain ⟨x, hxX, hx⟩ := Set.not_subset.1 hnot
  exact sizeJ_ge_of_halo_pair C hX hyX hxX hy hx

/-- The ratio of the cube side to the cell side: `L^k M / L^(j+m₀+m₁) = c_h L^(k-j)` with
`c_h = M / L^(m₀+m₁)`, for `j ≤ k`. -/
theorem sigma_div_cell {j : ℕ} (hj : j ≤ k) :
    ((S.L : ℝ) ^ k * M) / (S.L : ℝ) ^ (j + C.m₀ + m₁) =
      ((M : ℝ) / (S.L : ℝ) ^ (C.m₀ + m₁)) * (S.L : ℝ) ^ (k - j) := by
  have hL : (S.L : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne S.L
  have : (S.L : ℝ) ^ k = (S.L : ℝ) ^ (k - j) * (S.L : ℝ) ^ j := by
    rw [← pow_add]; congr 1; omega
  rw [this, show j + C.m₀ + m₁ = j + (C.m₀ + m₁) by ring, pow_add]
  field_simp

/-- **`regionalHaloDistance`, form of the note** (formula (3)): for `j ≤ k`,
`sizeJ m₀ j X ≥ c_h R_{k-1} L^(k-j) - 2 L` with `c_h = M / L^(m₀+m₁)`. -/
theorem regionalHaloDistance {Y : Set (Torus S.d (n k))} {j : ℕ} (hj : j ≤ k)
    {X : Set (Localization.CTorus S.d S.L C.N₁ m₁ k)} (hX : Def6.IsPolyDom C.m₀ j X)
    {y : Localization.CTorus S.d S.L C.N₁ m₁ k} (hyX : y ∈ X) (hy : y ∈ C.sset Y)
    (hnot : ¬ X ⊆ C.sset (thickY R Y)) :
    ((M : ℝ) / (S.L : ℝ) ^ (C.m₀ + m₁)) * R (k - 1) * (S.L : ℝ) ^ (k - j) - 2 * S.L ≤
      Def6.sizeJ C.m₀ j X := by
  have h := sizeJ_ge_of_not_subset_thickY C hX hyX hy hnot
  rw [sigma_div_cell C hj] at h
  have hc : (0 : ℝ) ≤ ((M : ℝ) / (S.L : ℝ) ^ (C.m₀ + m₁)) * (S.L : ℝ) ^ (k - j) := by
    have : (0 : ℝ) < S.L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne S.L)
    positivity
  have hR : R (k - 1) ≤ (⌊R (k - 1)⌋₊ : ℝ) + 1 := (Nat.lt_floor_add_one _).le
  nlinarith

open Classical in
/-- **The decay form used by the bounds** (T3): for `ρ ≥ 0`, `j ≤ k`, a centre
`y ∈ alignedIn j Y` and a polymer `X ∈ 𝒟_j` through `y` leaving `Y^≈`,
`exp (-ρ sizeJ) ≤ exp (2 L ρ) · exp (-ρ c_h ⌊R_{k-1}⌋ L^(k-j))`, `c_h = M / L^(m₀+m₁)`. -/
theorem exp_sizeJ_le_of_halo {Y : Set (Torus S.d (n k))} {j : ℕ} (hj : j ≤ k)
    {X : Set (Localization.CTorus S.d S.L C.N₁ m₁ k)} (hX : Def6.IsPolyDom C.m₀ j X)
    {y : Localization.CTorus S.d S.L C.N₁ m₁ k} (hy : y ∈ C.alignedIn j Y) (hyX : y ∈ X)
    (hnot : ¬ X ⊆ C.sset (thickY R Y)) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    Real.exp (-ρ * Def6.sizeJ C.m₀ j X) ≤ Real.exp (2 * S.L * ρ) *
      Real.exp (-ρ * (((M : ℝ) / (S.L : ℝ) ^ (C.m₀ + m₁)) * (⌊R (k - 1)⌋₊ : ℝ) *
        (S.L : ℝ) ^ (k - j))) := by
  have hysY : y ∈ C.sset Y := (Finset.mem_filter.1 hy).2.2
  have h := sizeJ_ge_of_not_subset_thickY C hX hyX hysY hnot
  rw [sigma_div_cell C hj] at h
  have hc : (0 : ℝ) ≤ ((M : ℝ) / (S.L : ℝ) ^ (C.m₀ + m₁)) * (S.L : ℝ) ^ (k - j) := by
    have : (0 : ℝ) < S.L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne S.L)
    positivity
  rw [← Real.exp_add]
  apply Real.exp_le_exp.2
  nlinarith

end Halo

end Balaban.LargeField.Def7
