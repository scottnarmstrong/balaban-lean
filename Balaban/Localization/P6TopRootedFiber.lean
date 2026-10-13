/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.P6TopCover
public import Balaban.Polymer.RootedAnimals

/-!
# Sums over patch sets rooted at top cells (VMOD-31 §3 package (v), with §2 (2.2))

For the full-torus top-only cover `F^top` (`topGS`), a set `C` of patches is *rooted at* a set `R`
of top cells when every connected component of `C` in the Moore graph of patches contains a patch
that Moore-touches a cell of `R`.  This file proves the combinatorial fixed-support sum

  `Σ_{C rooted at R} exp (-κ₂ |C|) ≤ (1 - z)^{-|R|}`,   `z = D² exp (-κ₂)`,
  `D = max (3 (L+4)^d + 1) (3^d (L^m₀)^d)`,

and its exponential form `≤ exp (h c_R) exp (h c_R Δ)` when `|R| ≤ c_R (1 + Δ)`, `h = -log (1 - z)`.

* `topRootNbhd`: the patches Moore-touching a top cell (at most `3^d (L^m₀)^d` of them).
* `top_rooted_sum_le`: the rooted sum for the top cover (`sum_rooted_le` with `topGS_degree_le`
  and `topGS_root_patch_count`).
* `mem_rootedSets_top_iff`: a set of patches is rooted at the union of the root neighbourhoods iff
  each of its patches is joined, by a walk inside the set, to a patch touching a cell of `R`
  (that is, every component touches `R`); both directions hold.
* `top_rooted_sum_le_of_rootCount`, `top_rooted_fixed_support_sum_le`: the exponential form.

**Not proved here.**  That the coefficients of the actual P6 interpolation vanish unless every
component of their patch set touches the active cells or the source cover
(`P6_COEF_ROOTED_XB` of `notes/phase1/VMOD-31.md`); the count `|R| ≤ c_R (1 + Δ_X)` (the
source-size bridge, an explicit premise of the exponential form); the H7 mixed transfer.  So no
statement about P6 (4.34) itself follows yet.
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Polymer

variable {d L N₁ m₁ K : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}

open Classical in
/-- The patches of `F^top` that Moore-touch the top cell of `u` (side `a = L^m₀ M₁ L^K`), as
vertices of the Moore graph of patches. -/
noncomputable def topRootNbhd (d L N₁ m₁ K : ℕ) [NeZero L] [NeZero N₁] (ϱ : ℝ) (m₀ : ℕ)
    (u : CTorus d L N₁ m₁ K) : Finset {P // P ∈ cubeIdx (topGS d L N₁ m₁ K ϱ)} :=
  (cubeIdx (topGS d L N₁ m₁ K ϱ)).attach.filter
    fun P => MooreTouch (topCell m₀ (K, u)) (Pset m₁ P.1)

theorem mem_topRootNbhd {m₀ : ℕ} {u : CTorus d L N₁ m₁ K}
    {P : {P // P ∈ cubeIdx (topGS d L N₁ m₁ K ϱ)}} :
    P ∈ topRootNbhd d L N₁ m₁ K ϱ m₀ u ↔ MooreTouch (topCell m₀ (K, u)) (Pset m₁ P.1) := by
  classical
  simp [topRootNbhd]

/-- **T1.** At most `3^d (L^m₀)^d` patches touch a top cell. -/
theorem card_topRootNbhd_le {m₀ : ℕ} (hN : L ^ m₀ ∣ N₁) (u : CTorus d L N₁ m₁ K) :
    (topRootNbhd d L N₁ m₁ K ϱ m₀ u).card ≤ 3 ^ d * (L ^ m₀) ^ d := by
  classical
  refine le_trans ?_ (topGS_root_patch_count (ϱ := ϱ) (m₁ := m₁) (K := K) hN u)
  refine Finset.card_le_card_of_injOn (fun P => P.1) (fun P hP => ?_) (fun P _ Q _ h => ?_)
  · rw [Finset.mem_coe, mem_topRootNbhd] at hP
    exact Finset.mem_coe.2 (Finset.mem_filter.2 ⟨P.2, hP⟩)
  · exact Subtype.ext h

/-- The constant `D = max (3 (L+4)^d + 1) (3^d (L^m₀)^d)`. -/
def topD (d L m₀ : ℕ) : ℕ := max (3 * (L + 4) ^ d + 1) (3 ^ d * (L ^ m₀) ^ d)

open Classical in
/-- **T2.** The rooted sum for the top cover: for a finite set `R` of top cells,
`Σ_{C rooted at the root neighbourhoods of R} t^|C| ≤ (1 / (1 - D² t))^|R|`. -/
theorem top_rooted_sum_le {m₀ : ℕ} (hN : L ^ m₀ ∣ N₁) (hm : 2 ≤ m₁)
    (hϱ : (d : ℝ) ≤ ϱ * (L : ℝ) ^ 2) (R : Finset (CTorus d L N₁ m₁ K)) {t : ℝ} (ht : 0 ≤ t)
    (hz : ((topD d L m₀ : ℕ) : ℝ) ^ 2 * t < 1) :
    ∑ C ∈ rootedSets (G := mooreGraph (topGS d L N₁ m₁ K ϱ))
        (⋃ u ∈ R, (topRootNbhd d L N₁ m₁ K ϱ m₀ u : Set _)), t ^ C.card
      ≤ (1 / (1 - ((topD d L m₀ : ℕ) : ℝ) ^ 2 * t)) ^ R.card :=
  sum_rooted_le (G := mooreGraph (topGS d L N₁ m₁ K ϱ))
    (b := 3 * (L + 4) ^ d) (b_root := 3 ^ d * (L ^ m₀) ^ d)
    (fun P => topGS_degree_le hm hϱ P)
    (fun u => topRootNbhd d L N₁ m₁ K ϱ m₀ u) (fun u => card_topRootNbhd_le hN u) ht hz R

open Classical in
/-- **T3.** A set `C` of patches is rooted at the root neighbourhoods of `R` if and only if every
patch of `C` is joined, by a walk of the Moore graph inside `C`, to a patch of `C` that
Moore-touches the top cell of some `u ∈ R`; that is, every connected component of `C` touches `R`. -/
theorem mem_rootedSets_top_iff {m₀ : ℕ} (R : Finset (CTorus d L N₁ m₁ K))
    (C : Finset {P // P ∈ cubeIdx (topGS d L N₁ m₁ K ϱ)}) :
    C ∈ rootedSets (G := mooreGraph (topGS d L N₁ m₁ K ϱ))
        (⋃ u ∈ R, (topRootNbhd d L N₁ m₁ K ϱ m₀ u : Set _)) ↔
      ∀ v ∈ C, ∃ w, WalkIn (mooreGraph (topGS d L N₁ m₁ K ϱ)) C v w ∧
        ∃ u ∈ R, MooreTouch (topCell m₀ (K, u)) (Pset m₁ w.1) := by
  rw [mem_rootedSets]
  refine forall₂_congr fun v hv => ?_
  constructor
  · rintro ⟨w, hw, h⟩
    simp only [Set.mem_iUnion, Finset.mem_coe, exists_prop] at hw
    obtain ⟨u, hu, hwu⟩ := hw
    exact ⟨w, h, u, hu, mem_topRootNbhd.1 hwu⟩
  · rintro ⟨w, h, u, hu, ht⟩
    refine ⟨w, ?_, h⟩
    simp only [Set.mem_iUnion, Finset.mem_coe, exists_prop]
    exact ⟨u, hu, mem_topRootNbhd.2 ht⟩

open Classical in
/-- **T4 (2.2).** With `t = exp (-κ₂)`, `z = D² t < 1`, `h = -log (1 - z)`: if `|R| ≤ c_R (1 + Δ)`
then the rooted sum is at most `exp (h c_R) exp (h c_R Δ)`. -/
theorem top_rooted_sum_le_of_rootCount {m₀ : ℕ} (hN : L ^ m₀ ∣ N₁) (hm : 2 ≤ m₁)
    (hϱ : (d : ℝ) ≤ ϱ * (L : ℝ) ^ 2) (R : Finset (CTorus d L N₁ m₁ K)) {κ₂ Δ c_R : ℝ}
    (hz : ((topD d L m₀ : ℕ) : ℝ) ^ 2 * Real.exp (-κ₂) < 1)
    (hR : (R.card : ℝ) ≤ c_R * (1 + Δ)) :
    ∑ C ∈ rootedSets (G := mooreGraph (topGS d L N₁ m₁ K ϱ))
        (⋃ u ∈ R, (topRootNbhd d L N₁ m₁ K ϱ m₀ u : Set _)), Real.exp (-κ₂ * C.card)
      ≤ Real.exp (-Real.log (1 - ((topD d L m₀ : ℕ) : ℝ) ^ 2 * Real.exp (-κ₂)) * c_R) *
        Real.exp (-Real.log (1 - ((topD d L m₀ : ℕ) : ℝ) ^ 2 * Real.exp (-κ₂)) * c_R * Δ) := by
  set z : ℝ := ((topD d L m₀ : ℕ) : ℝ) ^ 2 * Real.exp (-κ₂) with hzdef
  have hz0 : 0 ≤ z := by positivity
  have hpos : 0 < 1 - z := by linarith
  set h : ℝ := -Real.log (1 - z) with hh
  have hh0 : 0 ≤ h := by
    have : Real.log (1 - z) ≤ 0 := Real.log_nonpos (by linarith) (by linarith)
    linarith
  have hsum := top_rooted_sum_le (K := K) (ϱ := ϱ) hN hm hϱ R (Real.exp_pos (-κ₂)).le hz
  have hterm : ∀ C : Finset {P // P ∈ cubeIdx (topGS d L N₁ m₁ K ϱ)},
      Real.exp (-κ₂ * C.card) = Real.exp (-κ₂) ^ C.card := fun C => by
    rw [← Real.exp_nat_mul]; ring_nf
  simp only [hterm]
  refine hsum.trans ?_
  have : 1 / (1 - z) = Real.exp h := by
    rw [hh, Real.exp_neg, Real.exp_log hpos, one_div]
  rw [this, ← Real.exp_nat_mul, ← Real.exp_add]
  apply Real.exp_le_exp.2
  nlinarith [mul_le_mul_of_nonneg_left hR hh0]

open Classical in
/-- **T4, fixed support.**  For any map `supp` from patch sets to supports and any support `S`,
the sum over the rooted sets with `supp C = S` obeys the same bound. -/
theorem top_rooted_fixed_support_sum_le {m₀ : ℕ} {S₀ : Type*} [DecidableEq S₀]
    (hN : L ^ m₀ ∣ N₁) (hm : 2 ≤ m₁)
    (hϱ : (d : ℝ) ≤ ϱ * (L : ℝ) ^ 2) (R : Finset (CTorus d L N₁ m₁ K)) {κ₂ Δ c_R : ℝ}
    (hz : ((topD d L m₀ : ℕ) : ℝ) ^ 2 * Real.exp (-κ₂) < 1)
    (hR : (R.card : ℝ) ≤ c_R * (1 + Δ))
    (supp : Finset {P // P ∈ cubeIdx (topGS d L N₁ m₁ K ϱ)} → S₀) (S : S₀) :
    ∑ C ∈ (rootedSets (G := mooreGraph (topGS d L N₁ m₁ K ϱ))
        (⋃ u ∈ R, (topRootNbhd d L N₁ m₁ K ϱ m₀ u : Set _))).filter (fun C => supp C = S),
        Real.exp (-κ₂ * C.card)
      ≤ Real.exp (-Real.log (1 - ((topD d L m₀ : ℕ) : ℝ) ^ 2 * Real.exp (-κ₂)) * c_R) *
        Real.exp (-Real.log (1 - ((topD d L m₀ : ℕ) : ℝ) ^ 2 * Real.exp (-κ₂)) * c_R * Δ) :=
  le_trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    (fun _ _ _ => (Real.exp_pos _).le))
    (top_rooted_sum_le_of_rootCount hN hm hϱ R hz hR)

end Balaban.Localization
