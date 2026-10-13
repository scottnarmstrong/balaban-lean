/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.History.ParentR2Y
public import Balaban.SmallField.FinalCutoff
public import Balaban.SmallField.Def6v2Regime
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The direction of the parent datum at the tested sites (`LateYDirection`)

`notes/phase1/Q13-LATE.md` ("Exact missing estimate"), `notes/phase1/Q13-LATE2.md`
("Lean consequences", packages L1-L2).

At a late scale `k_0 < k < k_f` the background of the step lives on the generating set
`G = genW Y`, `Y = Z_kᶜ`, whose data sites reach `2⌊R_{k-1}⌋ + 3` cubes beyond `Y`.  The real
domain asks, at every data site `s`, for the mass alignment `m L^{2ℓ(s)} |1 - u_s · h| < η²`;
above `k_0` this needs the direction bound

    (RD)    ‖Ψ(s) - h‖ < 2 δ_k / √ν_k

for the datum `Ψ(s) = parentPsi s`.

## What is proved

* `testedSites`: the data sites of `genW Y` covered by the direction test of one small-field cube:
  there is a cube `□ ⊆ Y` such that `s` lies in the top domain of the cube's generating set and in
  the neighbourhood `□~` (the block-closeness test set `T`), and the whole averaging block of `s`
  lies in `□~` (the field-test set `S`).  `outerSites` is the complement among the data sites.
* `parentPsi_direction_of_chiY_ne_zero` (L1): if `χ_Y ≠ 0`, `0 < ν_k ≤ 1` and the cube mass is
  `ν_k L^{-2k}`, then (RD) holds at every tested site (block averaging: closeness of the
  field to `h` on the block, plus block closeness of the datum).
* The r3 clause of the real domain at the tested sites, and the geometry of the partition.

## What is NOT proved

The late-scale parent-domain theorem is NOT proved.  Mass alignment at the outer sites is an open
question to the author (`Q13-LATE2`, verdict V3).  In Lean, the open statement is

    ∀ s ∈ outerSites Cx Y,
      rn (fun i => parentPsi Cx ψk s i - hv i) < 2 * Cx.cs.delta (j + 1) / Real.sqrt ν

(or the clause `InPsiTilde.r3` itself there).  It is neither proved nor assumed anywhere in
this file.
-/

@[expose] public section

namespace Balaban.LargeField

open Balaban Balaban.Multiscale Balaban.Background RegionHistory Balaban.LargeField.Def7
  Balaban.SmallField.Def6v2

section Tested

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {M K : ℕ} [NeZero M]
  [NeZero S.L] {N m₁ j : ℕ} {ϱ : ℝ} (Cx : SFCtx S n R M K N (j + 1) m₁ ϱ)

/-- The generating set of the single cube `y₀` at scale `k = j + 1`. -/
noncomputable abbrev cubeGen (y₀ : Torus S.d (n (j + 1))) :=
  genCube (M1 := Cx.geo.M1) (N₁ := Cx.geo.c * n (j + 1)) (L := S.L) (q := j + 1)
    Cx.geo.c (n (j + 1)) y₀

/-- **The tested data sites.**  A data site `s` of `genW Y` is tested if there is a cube
`y₀ ∈ Y` of the product `χ_Y` such that `s` lies in the first domain of the generating set of the
cube, in the neighbourhood `y₀~` of the cube (the test set of the block-closeness test), and the
whole averaging block of `s` (the block of its layer) lies in `y₀~` (the test set of the field
test). -/
def testedSites (Y : Set (Torus S.d (n (j + 1)))) : Set (BgT Cx.geo (j + 1)) :=
  {s | s ∈ dataSites (Cx.genW Y) ∧ ∃ y₀ ∈ cubeFin Y,
    s ∈ (cubeGen Cx y₀).Ω 1 ∧
    s ∈ cubeNbhd Cx.geo.M1 (Cx.geo.c * n (j + 1)) S.L (j + 1) Cx.geo.c (n (j + 1)) 1 y₀ ∧
    ∀ z ∈ (cubeGen Cx y₀).blk ((cubeGen Cx y₀).layerIndex s) s,
      z ∈ cubeNbhd Cx.geo.M1 (Cx.geo.c * n (j + 1)) S.L (j + 1) Cx.geo.c (n (j + 1)) 1 y₀}

/-- **The outer data sites**: the data sites of `genW Y` that are not tested. -/
def outerSites (Y : Set (Torus S.d (n (j + 1)))) : Set (BgT Cx.geo (j + 1)) :=
  {s | s ∈ dataSites (Cx.genW Y)} \ testedSites Cx Y

theorem testedSites_subset_dataSites (Y : Set (Torus S.d (n (j + 1)))) :
    testedSites Cx Y ⊆ {s | s ∈ dataSites (Cx.genW Y)} := fun _ hs => hs.1

theorem testedSites_union_outerSites (Y : Set (Torus S.d (n (j + 1)))) :
    testedSites Cx Y ∪ outerSites Cx Y = {s | s ∈ dataSites (Cx.genW Y)} := by
  ext s
  simp only [outerSites, Set.mem_union, Set.mem_sdiff, Set.mem_ofPred_eq]
  constructor
  · rintro (h | h)
    · exact h.1
    · exact h.1
  · intro h
    by_cases ht : s ∈ testedSites Cx Y
    · exact Or.inl ht
    · exact Or.inr ⟨h, ht⟩

theorem disjoint_testedSites_outerSites (Y : Set (Torus S.d (n (j + 1)))) :
    Disjoint (testedSites Cx Y) (outerSites Cx Y) :=
  Set.disjoint_left.2 fun _ h1 h2 => h2.2 h1

/-- **L1: the direction of the datum at the tested sites.**  If `χ_Y ≠ 0`, the running mass
satisfies `0 < ν ≤ 1` and the cube mass is `ν L^{-2k}` (`Def7.FieldClauses.mu_eq`, `Coh.nu_cs`
above `k₀`), then at every tested site `‖Ψ(s) - h‖ < 2 δ_k / √ν`. -/
theorem parentPsi_direction_of_chiY_ne_zero (Y : Set (Torus S.d (n (j + 1))))
    (ψk : BlockAt S n M K (j + 1) → EuclideanSpace ℝ (Fin N)) (hv : EuclideanSpace ℝ (Fin N))
    (h : Cx.chiY Y ψk hv ≠ 0) {ν : ℝ} (hν : 0 < ν) (hν1 : ν ≤ 1)
    (hμ : Cx.cs.mu (j + 1) = sfBgMassAt S.L (j + 1) ν)
    {s : BgT Cx.geo (j + 1)} (hs : s ∈ testedSites Cx Y) :
    rn (fun i => parentPsi Cx ψk s i - hv i) < 2 * Cx.cs.delta (j + 1) / Real.sqrt ν := by
  obtain ⟨hsd, y₀, hy₀, hΩ, hT, hb⟩ := hs
  have hK := chiKProp_of_chiY_ne_zero Cx Y ψk hv h hy₀
  have hmass : Cx.cs.mu (j + 1) * ((S.L : ℝ) ^ (j + 1)) ^ 2 = ν := by
    rw [hμ]; exact physMass_mul_sq _ _
  have hF := hK.2.2.2
  rw [hmass] at hF
  have hc : ∀ y ∈ (cubeGen Cx y₀).blk ((cubeGen Cx y₀).layerIndex s) s, ∀ i,
      (cubeData (M1 := Cx.geo.M1) (N₁ := Cx.geo.c * n (j + 1)) (L := S.L) (q := j + 1)
        (fun i => hv i) Cx.geo.c (n (j + 1)) y₀
        (blockCfgOf Cx.geo Cx.hnn le_rfl Cx.hkK ψk)).h y i = ((hv i : ℝ) : ℂ) := by
    intro y hy i
    obtain ⟨h1, h2, h3⟩ := (cubeGen Cx y₀).layerIndex_spec hΩ
    have hy1 : y ∈ (cubeGen Cx y₀).Ω 1 := blk_subset_Ω _ h1 h2 h3 hy
    unfold cubeData
    rw [liftSingle_h _ _ _ hy1]
  have key := FinalCutoff.regIneq_cutoff_le_one hK.2.1 hF hν hν1 hΩ hT hb hc
  have hs₁ : s ∈ dataSites (cubeGen Cx y₀) :=
    (mem_dataSites _).2 (Or.inl hΩ)
  have e := cubeData_Ψ_eq_liftSingle_Ψ Cx Y ψk hv y₀ hs₁ hsd
  have e2 : ∀ i, (cubeData (M1 := Cx.geo.M1) (N₁ := Cx.geo.c * n (j + 1)) (L := S.L)
      (q := j + 1) (fun i => hv i) Cx.geo.c (n (j + 1)) y₀
      (blockCfgOf Cx.geo Cx.hnn le_rfl Cx.hkK ψk)).Ψ s i = ((parentPsi Cx ψk s i : ℝ) : ℂ) :=
    fun i => by rw [e]; exact liftSingle_Ψ_eq_parentPsi Cx Y ψk hv hsd i
  simp_rw [e2] at key
  rwa [show (fun i => ((parentPsi Cx ψk s i : ℝ) : ℂ) - ((hv i : ℝ) : ℂ)) =
    fun i => (((parentPsi Cx ψk s i - hv i : ℝ)) : ℂ) by
      funext i; push_cast; rfl, vn_ofReal] at key

/-- The cube datum at a data site of the cube and of `genW Y` is the parent datum. -/
theorem cubeData_Ψ_eq_parentPsi (Y : Set (Torus S.d (n (j + 1))))
    (ψk : BlockAt S n M K (j + 1) → EuclideanSpace ℝ (Fin N)) (hv : EuclideanSpace ℝ (Fin N))
    (y₀ : Torus S.d (n (j + 1))) {s : BgT Cx.geo (j + 1)}
    (hΩ : s ∈ (cubeGen Cx y₀).Ω 1) (hsd : s ∈ dataSites (Cx.genW Y)) (i : Fin N) :
    (cubeData (M1 := Cx.geo.M1) (N₁ := Cx.geo.c * n (j + 1)) (L := S.L)
      (q := j + 1) (fun i => hv i) Cx.geo.c (n (j + 1)) y₀
      (blockCfgOf Cx.geo Cx.hnn le_rfl Cx.hkK ψk)).Ψ s i = ((parentPsi Cx ψk s i : ℝ) : ℂ) := by
  rw [cubeData_Ψ_eq_liftSingle_Ψ Cx Y ψk hv y₀ ((mem_dataSites _).2 (Or.inl hΩ)) hsd]
  exact liftSingle_Ψ_eq_parentPsi Cx Y ψk hv hsd i

/-- **R2 at the tested sites.**  `|‖Ψ(s)‖ - 1| < (d + 1) δ_k` (the sphere bound of the cube
background and block averaging). -/
theorem parentPsi_norm_of_tested (Y : Set (Torus S.d (n (j + 1))))
    (ψk : BlockAt S n M K (j + 1) → EuclideanSpace ℝ (Fin N)) (hv : EuclideanSpace ℝ (Fin N))
    (h : Cx.chiY Y ψk hv ≠ 0)
    (HB : BgHyp S.d S.L (j + 1) (minSep S.L Cx.geo.M1) Cx.weights (Cx.cs.mu (j + 1)))
    {s : BgT Cx.geo (j + 1)} (hs : s ∈ testedSites Cx Y) :
    |rn (parentPsi Cx ψk s) - 1| < (S.d + 1) * Cx.cs.delta (j + 1) := by
  classical
  obtain ⟨hsd, y₀, hy₀, hΩ, hT, hb⟩ := hs
  have hm : Cx.geo.c * n (j + 1) * S.L ^ (j + 1 - (j + 1)) = Cx.geo.c * n (j + 1) := by simp
  have hK := chiKProp_of_chiY_ne_zero Cx Y ψk hv h hy₀
  have hD := hK.1
  have hunit := (theorem71 HB hD).2.1
  rw [← (theorem72_real HB hD).1] at hunit
  have htop : s ∈ (cubeGen Cx y₀).Ω (j + 1) :=
    (genCube_top_mem hm y₀).2 (nbhd_mono (by omega) subset_rfl (mem_cubePre.1 hT))
  have hlay := layerIndex_top (cubeGen Cx y₀) (Nat.succ_pos j) htop
  have hS : ∀ z, jBlock S.d S.L (Cx.geo.M1 * (Cx.geo.c * n (j + 1))) (j + 1) (j + 1) z =
      jBlock S.d S.L (Cx.geo.M1 * (Cx.geo.c * n (j + 1))) (j + 1) (j + 1) s →
      z ∈ cubeNbhd Cx.geo.M1 (Cx.geo.c * n (j + 1)) S.L (j + 1) Cx.geo.c (n (j + 1)) 1 y₀ ∧
        z ∈ (cubeGen Cx y₀).Ω 1 := by
    intro z hz
    have hzb : z ∈ (cubeGen Cx y₀).blk ((cubeGen Cx y₀).layerIndex s) s := by
      rw [hlay]; exact GeneratingSet.mem_blk.2 hz
    obtain ⟨h1, h2, h3⟩ := (cubeGen Cx y₀).layerIndex_spec hΩ
    exact ⟨hb z hzb, blk_subset_Ω _ h1 h2 h3 hzb⟩
  have key := sphere_bound_of_close (cubeGen Cx y₀) _ _ _ _ (Cx.cs.delta (j + 1)) (Nat.succ_pos j)
    hK.2.2.1 hunit (s := s) (mem_layer_top _ htop) hS (hK.2.1 s hT)
  have e : vn ((cubeData (M1 := Cx.geo.M1) (N₁ := Cx.geo.c * n (j + 1)) (L := S.L)
      (q := j + 1) (fun i => hv i) Cx.geo.c (n (j + 1)) y₀
      (blockCfgOf Cx.geo Cx.hnn le_rfl Cx.hkK ψk)).Ψ s) = rn (parentPsi Cx ψk s) := by
    rw [← vn_ofReal]
    congr 1
    funext i
    exact cubeData_Ψ_eq_parentPsi Cx Y ψk hv y₀ hΩ hsd i
  rwa [e] at key

/-- Algebra of the mass-alignment clause: for `Σ h² = 1`, `r = ‖a‖ ≥ 1/4`,
`|1 - a·h/‖a‖| ≤ 2 ‖a - h‖²`. -/
theorem one_sub_dot_le (a h : Fin N → ℝ) (hh : ∑ i, h i ^ 2 = 1) (hr : 1 / 4 ≤ rn a) :
    |1 - (∑ i, a i * h i) / rn a| ≤ 2 * rn (fun i => a i - h i) ^ 2 := by
  have hr0 : 0 < rn a := by linarith
  have h1 : rn a ^ 2 = ∑ i, a i ^ 2 := rn_sq a
  have h2 : rn (fun i => a i - h i) ^ 2 = ∑ i, (a i - h i) ^ 2 := rn_sq _
  have h3 : ∑ i, (a i - h i) ^ 2 = rn a ^ 2 - 2 * ∑ i, a i * h i + 1 := by
    have : ∀ i, (a i - h i) ^ 2 = a i ^ 2 - 2 * (a i * h i) + h i ^ 2 := fun i => by ring
    simp_rw [this, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, hh, h1]
  have hcs : (∑ i, a i * h i) ^ 2 ≤ (∑ i, a i ^ 2) * ∑ i, h i ^ 2 :=
    Finset.sum_mul_sq_le_sq_mul_sq _ _ _
  rw [hh, mul_one, ← h1] at hcs
  have hsr : ∑ i, a i * h i ≤ rn a := by nlinarith [sq_nonneg (∑ i, a i * h i - rn a)]
  have hρ := sq_nonneg (rn (fun i => a i - h i))
  rw [h2, h3] at hρ
  rw [h2, h3]
  generalize ∑ i, a i * h i = t at *
  generalize rn a = r at *
  have hx : 0 ≤ 1 - t / r := by rw [sub_nonneg, div_le_one hr0]; exact hsr
  rw [abs_of_nonneg hx]
  have : 1 - t / r = (r - t) / r := by field_simp
  rw [this, div_le_iff₀ hr0]
  nlinarith [sq_nonneg (r - 1)]

/-- **T3: the mass-alignment clause `r3` of the real domain at the tested sites.**  With
`m = ν L^{-2k}`, `η = max (3 d L δ_{k-1}) (4 (d + 1) δ_k) < 1`, `0 < ν ≤ 1`, `‖h‖ = 1`,
`χ_Y ≠ 0` and the cube `BgHyp`: at every tested site (whose layer index is at most `k`),
`m L^{2ℓ(s)} |1 - u_s · h| < η²`, `u_s = Ψ(s) / ‖Ψ(s)‖`. -/
theorem parentPsi_r3_of_tested (Y : Set (Torus S.d (n (j + 1))))
    (ψk : BlockAt S n M K (j + 1) → EuclideanSpace ℝ (Fin N)) (hv : EuclideanSpace ℝ (Fin N))
    (h : Cx.chiY Y ψk hv ≠ 0)
    (HB : BgHyp S.d S.L (j + 1) (minSep S.L Cx.geo.M1) Cx.weights (Cx.cs.mu (j + 1)))
    (hunit : ‖hv‖ = 1) {ν : ℝ} (hν : 0 < ν) (hν1 : ν ≤ 1)
    (hμ : Cx.cs.mu (j + 1) = sfBgMassAt S.L (j + 1) ν)
    (hη : max (3 * S.d * S.L * Cx.cs.delta j) (4 * (S.d + 1) * Cx.cs.delta (j + 1)) < 1)
    {s : BgT Cx.geo (j + 1)} (hs : s ∈ testedSites Cx Y) :
    sfBgMassAt S.L (j + 1) ν * ((S.L : ℝ) ^ (Cx.genW Y).layerIndex s) ^ 2 *
        |1 - (∑ i, parentPsi Cx ψk s i * hv i) / rn (parentPsi Cx ψk s)| <
      (max (3 * S.d * S.L * Cx.cs.delta j) (4 * (S.d + 1) * Cx.cs.delta (j + 1))) ^ 2 := by
  have hdir := parentPsi_direction_of_chiY_ne_zero Cx Y ψk hv h hν hν1 hμ hs
  have hnorm := parentPsi_norm_of_tested Cx Y ψk hv h HB hs
  set δ := Cx.cs.delta (j + 1) with hδdef
  set a := parentPsi Cx ψk s with ha
  have hsq : 0 < Real.sqrt ν := Real.sqrt_pos.2 hν
  have hρ0 : 0 ≤ rn (fun i => a i - hv i) := Real.sqrt_nonneg _
  have hδ : 0 < δ := by
    have := hρ0.trans_lt hdir
    have h2 : 0 < 2 * δ := (div_pos_iff_of_pos_right hsq).1 this
    linarith
  have hd0 : (0 : ℝ) ≤ S.d := Nat.cast_nonneg _
  have h4 : 4 * (S.d + 1) * δ < 1 := lt_of_le_of_lt (le_max_right _ _) hη
  have hε : (S.d + 1) * δ < 1 / 4 := by linarith
  have hr : 1 / 4 ≤ rn a := by
    have := (abs_lt.1 hnorm).1
    linarith
  have hx := one_sub_dot_le a (fun i => hv i) (by
    rw [parent_sum_sq_eq_norm_sq, hunit]; norm_num) hr
  have hX0 : 0 ≤ |1 - (∑ i, a i * hv i) / rn a| := abs_nonneg _
  have hm0 : 0 ≤ sfBgMassAt S.L (j + 1) ν := by
    unfold sfBgMassAt physMass; positivity
  have hL1 : (1 : ℝ) ≤ S.L := by
    exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne S.L)
  have hlk : (Cx.genW Y).layerIndex s ≤ j + 1 := layerIndex_le_k _ _
  have hmL : sfBgMassAt S.L (j + 1) ν * ((S.L : ℝ) ^ (Cx.genW Y).layerIndex s) ^ 2 ≤ ν := by
    calc _ ≤ sfBgMassAt S.L (j + 1) ν * ((S.L : ℝ) ^ (j + 1)) ^ 2 := by
          gcongr
      _ = ν := physMass_mul_sq _ _
  have hρν : rn (fun i => a i - hv i) ^ 2 * ν < 4 * δ ^ 2 := by
    have h1 : rn (fun i => a i - hv i) * Real.sqrt ν < 2 * δ := (lt_div_iff₀ hsq).1 hdir
    have h2 := pow_lt_pow_left₀ h1 (by positivity) (two_ne_zero)
    rw [mul_pow, Real.sq_sqrt hν.le] at h2
    nlinarith
  have hηδ : 4 * δ ≤ max (3 * S.d * S.L * Cx.cs.delta j) (4 * (S.d + 1) * δ) :=
    le_trans (by nlinarith) (le_max_right _ _)
  calc sfBgMassAt S.L (j + 1) ν * ((S.L : ℝ) ^ (Cx.genW Y).layerIndex s) ^ 2 *
        |1 - (∑ i, a i * hv i) / rn a|
      ≤ ν * |1 - (∑ i, a i * hv i) / rn a| := mul_le_mul_of_nonneg_right hmL hX0
    _ ≤ ν * (2 * rn (fun i => a i - hv i) ^ 2) := mul_le_mul_of_nonneg_left hx hν.le
    _ < 8 * δ ^ 2 := by nlinarith
    _ ≤ _ := by nlinarith

/-! ### Geometry of the partition -/

/-- **The partition is the distance-one neighbourhood.**  A data site of `genW Y` is tested
exactly when its scale-`k` cube lies within one cube of `Y`: the averaging block of a site over a
cube never leaves that cube, so the block condition is automatic. -/
theorem mem_testedSites_iff (Y : Set (Torus S.d (n (j + 1)))) {s : BgT Cx.geo (j + 1)} :
    s ∈ testedSites Cx Y ↔ s ∈ dataSites (Cx.genW Y) ∧ parentSiteCube Cx s ∈ nbhd 1 Y := by
  classical
  have hm : Cx.geo.c * n (j + 1) * S.L ^ (j + 1 - (j + 1)) = Cx.geo.c * n (j + 1) := by simp
  have hbs : blockMap (S.L ^ (j + 1) * (Cx.geo.c * Cx.geo.M1)) (n (j + 1)) s =
      parentSiteCube Cx s := (cubeMap_bgToFine Cx s).symm
  constructor
  · rintro ⟨hsd, y₀, hy₀, hΩ, hT, -⟩
    refine ⟨hsd, ?_⟩
    have hy : y₀ ∈ Y := by simpa [cubeFin] using hy₀
    rw [← hbs]
    exact nbhd_mono (le_refl 1) (Set.singleton_subset_iff.2 hy) (mem_cubePre.1 hT)
  · rintro ⟨hsd, hq⟩
    obtain ⟨y₀, hy, hd⟩ := mem_nbhd.mp hq
    have hq0 : blockMap (S.L ^ (j + 1) * (Cx.geo.c * Cx.geo.M1)) (n (j + 1)) s ∈ nbhd 1 {y₀} :=
      mem_nbhd.mpr ⟨y₀, rfl, hbs ▸ hd⟩
    have hy₀ : y₀ ∈ cubeFin Y := by simp [cubeFin, hy]
    have htop : s ∈ (cubeGen Cx y₀).Ω (j + 1) :=
      (genCube_top_mem hm y₀).2 (nbhd_mono (by omega) subset_rfl hq0)
    have hlay := layerIndex_top (cubeGen Cx y₀) (Nat.succ_pos j) htop
    refine ⟨hsd, y₀, hy₀, mem_Ω_one_of_top _ (Nat.succ_pos j) htop, mem_cubePre.2 hq0, ?_⟩
    intro z hz
    rw [hlay] at hz
    have hzj := GeneratingSet.mem_blk.1 hz
    have hzc := cube_eq_of_jBlock_eq (M1 := Cx.geo.M1) (N₁ := Cx.geo.c * n (j + 1)) (L := S.L)
      (q := j + 1) (c := Cx.geo.c) (n := n (j + 1)) hm hzj
    exact mem_cubePre.2 (hzc ▸ hq0)

theorem mem_outerSites_iff (Y : Set (Torus S.d (n (j + 1)))) {s : BgT Cx.geo (j + 1)} :
    s ∈ outerSites Cx Y ↔ s ∈ dataSites (Cx.genW Y) ∧ parentSiteCube Cx s ∉ nbhd 1 Y := by
  simp only [outerSites, Set.mem_sdiff, Set.mem_ofPred_eq, mem_testedSites_iff]
  tauto

/-- **(a)** Every data site over a cube of `Y` is tested. -/
theorem tested_of_over_Y (Y : Set (Torus S.d (n (j + 1)))) {s : BgT Cx.geo (j + 1)}
    (hsd : s ∈ dataSites (Cx.genW Y)) (hY : parentSiteCube Cx s ∈ Y) :
    s ∈ testedSites Cx Y :=
  (mem_testedSites_iff Cx Y).2 ⟨hsd, subset_nbhd 1 Y hY⟩

/-- **(b)** A tested site has its cube within one cube of `Y`. -/
theorem testedSites_subset_nbhd_one (Y : Set (Torus S.d (n (j + 1)))) {s : BgT Cx.geo (j + 1)}
    (hs : s ∈ testedSites Cx Y) : parentSiteCube Cx s ∈ nbhd 1 Y :=
  ((mem_testedSites_iff Cx Y).1 hs).2

/-- **(c)** An outer site has its cube strictly outside `Y`, at distance more than one cube and at
most `2⌊R_{k-1}⌋ + 3` cubes from `Y`; and every data site whose cube is at distance more than one
from `Y` is an outer site. -/
theorem outerSites_cube_mem (hL : 2 ≤ S.L) (Y : Set (Torus S.d (n (j + 1))))
    {s : BgT Cx.geo (j + 1)} (hs : s ∈ outerSites Cx Y) :
    parentSiteCube Cx s ∈ nbhd (2 * ⌊R j⌋₊ + 3) Y ∧ parentSiteCube Cx s ∉ nbhd 1 Y ∧
      parentSiteCube Cx s ∉ Y := by
  obtain ⟨hsd, hq⟩ := (mem_outerSites_iff Cx Y).1 hs
  exact ⟨dataSite_cube_mem_nbhd Cx hL Y hsd, hq, fun hy => hq (subset_nbhd 1 Y hy)⟩

theorem mem_outerSites_of_far (Y : Set (Torus S.d (n (j + 1)))) {s : BgT Cx.geo (j + 1)}
    (hsd : s ∈ dataSites (Cx.genW Y)) (hq : parentSiteCube Cx s ∉ nbhd 1 Y) :
    s ∈ outerSites Cx Y :=
  (mem_outerSites_iff Cx Y).2 ⟨hsd, hq⟩

/-- **(d)** For a retained component `C`, a data site over a cube of `C` is tested exactly when
that cube is adjacent (distance at most one) to a cube of `Y`. -/
theorem retained_tested_iff {k0 : ℕ} (H : RegionHistory S n R k0 K) (C : H.Comp (j + 1))
    (_hC : C.1 ∉ H.rem (j + 1)) (Y : Set (Torus S.d (n (j + 1))))
    {s : BgT Cx.geo (j + 1)} (hsd : s ∈ dataSites (Cx.genW Y)) (_hq : parentSiteCube Cx s ∈ C.1) :
    s ∈ testedSites Cx Y ↔ ∃ y ∈ Y, supDist (parentSiteCube Cx s) y ≤ 1 := by
  rw [mem_testedSites_iff, mem_nbhd]
  simp [hsd]

end Tested

end Balaban.LargeField
