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

end Tested

end Balaban.LargeField
