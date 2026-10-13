/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.P6ActiveSeed
public import Balaban.Inhabited.D7FineSizeWitness
public import Balaban.Inhabited.P6TopWitness
public import Balaban.Inhabited.P6PairWitness

/-!
# An instance of the active seed of the old boundary term of P6 with `c = L ^ m₀`

The side premise `hside` of `Localization/P6ActiveSeed.lean` holds exactly when `c = L ^ m₀`
(`hside_iff`), whereas the slab witnesses of the P6 pair (`P6PairWitness`) have `c = 15`, `L = 3`,
`m₀ = 1`, for which `hside` is false.  This file builds a setting with `c = L ^ m₀` in which every
hypothesis of the active-seed theorems and of the geometric theorems of the P6 pair holds.

Parameters: `d = L = 3`, `m₀ = 3`, `c = 3 ^ 3 = 27`, `m₁ = 7`, `M₁ = 3 ^ 7`, `M = 3 ^ 10`, scale
`k = 1` (top layer `k + 1 = 2`), `n_j = 2` for all `j`, `R_{k-1} = 9`, `R_k = 0`.  The values
`m₀ = 3` and `m₁ = 7` are forced: the boundary operator needs `14 ≤ c`, so `c = L ^ m₀` needs
`m₀ ≥ 3` when `L = 3`; the landed numerical premise `2 d log L ≤ agmonRate d / 16 (5 L M₁ - 1)`
needs `m₁ ≥ 7` (see `P6TopWitness`).  The region step is the one of `P6PairWitness.stepZ0` (no old
large-field region, so the new region is the whole torus), the region `Om` is everything and the
label `X` is the set of all cubes.

This is an instance of the geometric count only.  Active-only coefficient support
(`OPEN-P6-ACTIVE-COMPOSITE-LOC`) and the region cast for a physical history are open; the region
step here is a toy one (`Z = ∅`).
-/

@[expose] public section

namespace Balaban.Inhabited

namespace P6ActiveSeedWitness

open Balaban Balaban.LargeField Balaban.Localization Balaban.Multiscale Balaban.Polymer
  Balaban.LargeField.Def7

/-- The dimension `d = 3` (irreducible, so that side lengths are never evaluated to numerals by
unification). -/
@[irreducible] def swd : ℕ := 3

/-- The scale factor `L = 3` (irreducible, as `swd`). -/
@[irreducible] def swL : ℕ := 3

theorem swd_eq : swd = 3 := by unfold swd; rfl

theorem swL_eq : swL = 3 := by unfold swL; rfl

/-- The setting of the Def-7 witnesses, with `d = swd = 3` and `L = swL = 3`. -/
noncomputable abbrev swS : Setting := { Balaban.LargeField.Def7.Wit.wS with d := swd, L := swL }

/-- The exponent `m₀ = 3` of the cell side `L ^ m₀`. -/
abbrev swm₀ : ℕ := 3

/-- The exponent `m₁ = 7` of the cover torus. -/
abbrev swm₁ : ℕ := 7

/-- The scale `k = 1` (the cover has top layer `k + 1 = 2`). -/
abbrev swk : ℕ := 1

/-- The halo parameter `c = L ^ m₀ = 27`. -/
noncomputable abbrev swc : ℕ := swS.L ^ swm₀

/-- `M₁ = L ^ m₁ = 3 ^ 7`. -/
noncomputable abbrev swM1 : ℕ := swS.L ^ swm₁

/-- The number `n₀ = 3 · 2` of cubes per side of the torus of the old region. -/
abbrev swn0 : ℕ := 3 * 2

/-- The numbers of cubes `n_j = 2` (irreducible, so that the side lengths of the tori are never
evaluated to numerals by unification). -/
@[irreducible] def swn : ℕ → ℕ := fun _ => 2

theorem swn_eq (j : ℕ) : swn j = 2 := by unfold swn; rfl

instance : NeZero swS.L := ⟨by show swL ≠ 0; rw [swL_eq]; norm_num⟩

instance (j : ℕ) : NeZero (swn j) := ⟨by rw [swn_eq]; norm_num⟩

instance : NeZero swc := ⟨pow_ne_zero _ (NeZero.ne _)⟩

instance : NeZero swM1 := ⟨pow_ne_zero _ (NeZero.ne _)⟩

instance : NeZero swn0 := ⟨by show (3 * 2 : ℕ) ≠ 0; norm_num⟩

/-- The frame of the fine size: `m₀ = 3`, `m₁ = 7`, `M = L ^ 10`, scale `k + 1 = 2`. -/
noncomputable abbrev swF : FineSizeFrame swS swn (swS.L ^ (swm₀ + swm₁)) (swk + 1) swm₀ swm₁ :=
  fineFrame swS swn (swk + 1) rfl

theorem swN1 : swF.N₁ = swc * swn (swk + 1) := rfl

/-- The side identity `hside` for `c = L ^ m₀`. -/
theorem swHside : (swF.N₁ * swS.L ^ swm₁) * swS.L ^ (swk + 1) =
    (swc * swn (swk + 1)) * swS.L ^ swm₁ * swS.L ^ (swk + 1) := by
  rw [swN1]

/-- The region step: `Z = ∅`, `R_{k-1} = 9 = 3 L`, `R_k = 0`. -/
noncomputable def swSt : RegionStep swS.d swS.L swn0 (swn (swk + 1)) 9 0 := by
  with_unfolding_all exact P6PairWitness.stepZ0 3 2

theorem swSt_omega : swSt.Omega = Set.univ := by
  with_unfolding_all exact P6PairWitness.omega_stepZ0 3 2

theorem swHn : swn0 = swS.L * swn (swk + 1) := by
  show 3 * 2 = swL * swn (swk + 1)
  rw [swn_eq, swL_eq]

theorem swHρ : 3 * swS.L ≤ ⌊(9 : ℝ)⌋₊ := by
  show 3 * swL ≤ ⌊(9 : ℝ)⌋₊
  rw [swL_eq]
  norm_num

theorem swH5 : 5 ≤ swc := by
  show 5 ≤ swL ^ 3
  rw [swL_eq]
  norm_num

theorem swHd : swS.d < 5 * swS.L ^ 3 * swM1 := by
  show swd < 5 * swL ^ 3 * swL ^ 7
  rw [swd_eq, swL_eq]
  norm_num

theorem swHm : 2 ≤ swm₁ := by norm_num

/-- `D = fsharpD 3 3 3 = 531441`. -/
theorem swD : fsharpD swS.d swS.L swm₀ = 531441 := by
  show fsharpD swd swL 3 = 531441
  rw [swd_eq, swL_eq]
  norm_num [fsharpD]

/-- `D² exp (-30) < 1` for `D = 531441`, so `κ₂ = 30` is admissible. -/
theorem swHz : ((fsharpD swS.d swS.L swm₀ : ℕ) : ℝ) ^ 2 * Real.exp (-30) < 1 := by
  rw [swD, Real.exp_neg]
  have h1 : (2.7 : ℝ) < Real.exp 1 := lt_trans (by norm_num) Real.exp_one_gt_d9
  have h2 : (2.7 : ℝ) ^ 30 < Real.exp 1 ^ 30 := pow_lt_pow_left₀ h1 (by norm_num) (by norm_num)
  have h3 : Real.exp 30 = Real.exp 1 ^ 30 := by
    rw [← Real.exp_nat_mul]; norm_num
  rw [← h3] at h2
  have h4 : (0 : ℝ) < Real.exp 30 := Real.exp_pos _
  rw [mul_inv_lt_iff₀ h4]
  push_cast
  nlinarith [h2]

/-- The cover torus of the instance. -/
noncomputable abbrev swCT : Type :=
  Localization.CTorus swS.d swS.L (swc * swn (swk + 1)) swm₁ (swk + 1)

/-- The active seed of the instance: `X` = all cubes, `Om` = everything, `ΩK` = the new region. -/
noncomputable def swSeed : Finset swCT :=
  d7ActiveSeed (k := swk) swF swc swHside (Set.univ : Set (Torus swS.d (swn swk)))
    swSt.Omega (Finset.univ : Finset (Torus swS.d (swn swk)))

theorem swValid : FineValidAt swF swk (Set.univ : Set (Torus swS.d (swn swk)))
    (Finset.univ : Finset (Torus swS.d (swn swk))) :=
  fineValidAt_univ swF swk _

section Generic

variable {S : Setting} {n : ℕ → ℕ} {M m₀ m₁ k : ℕ} [NeZero S.L] [∀ j, NeZero (n j)]

/-- For the label `X` = all cubes, the region `Om` = everything and `ΩK` = everything, the active
seed is non-empty (any frame, any `c`). -/
theorem d7ActiveSeed_univ_nonempty (F : FineSizeFrame S n M (k + 1) m₀ m₁) (c : ℕ) [NeZero c]
    (hside : (F.N₁ * S.L ^ m₁) * S.L ^ (k + 1) = (c * n (k + 1)) * S.L ^ m₁ * S.L ^ (k + 1))
    {ΩK : Set (Torus S.d (n (k + 1)))} (hΩ : ΩK = Set.univ) :
    (d7ActiveSeed F c hside (Set.univ : Set (Torus S.d (n k))) ΩK
      (Finset.univ : Finset (Torus S.d (n k)))).Nonempty := by
  subst hΩ
  let y := d7ToCover F c hside 0
  refine ⟨cbase (cellSide S.L m₀ m₁ (k + 1)) y, mem_d7ActiveSeed.2 ⟨aligned_cbase _, 0, ?_, ?_⟩⟩
  · simp [d7Pull_univ]
  · unfold topCell
    simp only
    rw [cbase_cbase_of_dvd dvd_rfl (cellSide_pos m₀ m₁ _)]
    exact mem_box_cbase (cellSide_pos m₀ m₁ _) y

open Classical in
/-- The cast images of the cells of the active seed lie in `fineK1` (`d7ActiveSeed_active`, for
`M1 = L ^ m₁`, the cast proof quantified). -/
theorem d7ActiveSeed_image_cast_subset {c n0 : ℕ} [NeZero c] [NeZero (S.L ^ m₁)] {Rprev Rk : ℝ}
    (F : FineSizeFrame S n M (k + 1) m₀ m₁)
    (hside : (F.N₁ * S.L ^ m₁) * S.L ^ (k + 1) = (c * n (k + 1)) * S.L ^ m₁ * S.L ^ (k + 1))
    (st : RegionStep S.d S.L n0 (n (k + 1)) Rprev Rk)
    (Om : Set (Torus S.d (n k))) (X : Finset (Torus S.d (n k)))
    (h : (c * n (k + 1)) * S.L ^ m₁ * S.L ^ (k + 1) = S.L ^ m₁ * (c * n (k + 1)) * S.L ^ (k + 1)) :
    (d7ActiveSeed F c hside Om st.Omega X).image (fun u => LargeField.torusCast h u) ⊆
      fineK1 (S.L ^ m₁) c (n (k + 1)) S.L k st.Omega := by
  intro y hy
  obtain ⟨u, hu, rfl⟩ := Finset.mem_image.1 hy
  exact d7ActiveSeed_active F hside rfl st rfl hu

end Generic

/-- **The seed is non-empty.** -/
theorem swSeed_nonempty : swSeed.Nonempty :=
  d7ActiveSeed_univ_nonempty (k := swk) swF swc swHside swSt_omega

/-- `c₁ = [3 (2 L - 1)]^d = 15^3 = 3375`. -/
theorem sw_c1 : Fluctuation.c1 swS.d swS.L = 3375 := by
  show Fluctuation.c1 swd swL = 3375
  rw [swd_eq, swL_eq]
  unfold Fluctuation.c1
  norm_num

/-- The cover `F♯` of the instance. -/
noncomputable def swCover :=
  p6FsharpC (k := swk) (m₁ := swm₁) (n0 := swn0) (M1 := swM1) (c := swc) swHn swHρ swH5
    swSt.Z (rfl : swM1 = swS.L ^ swm₁)

/-- The root neighbourhood of the cell `u` in the instance. -/
noncomputable def swNbhd (u : swCT) : Finset {P // P ∈ cubeIdx swCover} :=
  @fsharpRootNbhd swS.d swM1 swc (swn (swk + 1)) swS.L swk swn0 swm₁ _ _ _ _ _ swHn _ swHρ swH5
    swSt.Z rfl swm₀ u

open Classical in
/-- **The instance of the active-seed theorems.**  For the old boundary term of P6 on the
parameters `d = L = 3`, `m₀ = 3`, `c = 27`, `m₁ = 7`, `k = 1`, `n_j = 2`: the seed is non-empty,
the cast of every cell of it lies in `fineK1` (every cell is active), `|seed| ≤ 3375 (1 + Δ_X)`,
and the rooted sum of `e^{-30 |C|}` over families of patches of `F♯` rooted at the seed is at most
`e^{h c₁} e^{h c₁ Δ_X}`, `h = -log (1 - D² e^{-30})`, `D = 531441`. -/
theorem p6ActiveSeed_instance :
    swSeed.Nonempty ∧
    (∀ h : (swc * swn (swk + 1)) * swS.L ^ swm₁ * swS.L ^ (swk + 1) = swM1 * (swc * swn (swk + 1)) * swS.L ^ (swk + 1),
        swSeed.image (fun u => LargeField.torusCast h u) ⊆
          fineK1 swM1 swc (swn (swk + 1)) swS.L swk swSt.Omega) ∧
    ((swSeed.card : ℝ) ≤ 3375 * (1 + d7SizeAt swF swk (Set.univ : Set (Torus swS.d (swn swk)))
          (Finset.univ : Finset (Torus swS.d (swn swk))))) ∧
    (∑ C ∈ rootedSets (G := mooreGraph swCover)
        (⋃ (u : swCT) (_ : u ∈ swSeed), (swNbhd u : Set _)),
        Real.exp (-30 * C.card)
      ≤ Real.exp (-Real.log (1 - ((fsharpD swS.d swS.L swm₀ : ℕ) : ℝ) ^ 2 * Real.exp (-30)) *
            3375) *
        Real.exp (-Real.log (1 - ((fsharpD swS.d swS.L swm₀ : ℕ) : ℝ) ^ 2 * Real.exp (-30)) *
          3375 * d7SizeAt swF swk (Set.univ : Set (Torus swS.d (swn swk)))
            (Finset.univ : Finset (Torus swS.d (swn swk))))) := by
  have hΩ : swSt.Omega = swSt.Omega := rfl
  refine ⟨swSeed_nonempty, fun h => ?_, ?_, ?_⟩
  · exact d7ActiveSeed_image_cast_subset swF swHside swSt Set.univ Finset.univ h
  · have := d7ActiveSeed_card_le (k := swk) swF swHside swSt.Omega swValid
    rwa [sw_c1] at this
  · have := d7ActiveSeed_rooted_sum_le (k := swk) (M1 := swM1) (n0 := swn0) swF swHside rfl
      swHn swHρ swH5 swHm swHd swSt hΩ swValid swHz
    rwa [sw_c1] at this

end P6ActiveSeedWitness

end Balaban.Inhabited
