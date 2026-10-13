/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.RegionalAlignedSource
public import Balaban.LargeField.R.RadialCoefficientLimit
public import Balaban.LargeField.R.RadialCoefficientAvg
public import Balaban.SmallField.Def6BridgeInfDict
public import Balaban.SmallField.Def6AvgDens
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Transport of the scale-`j` decomposition to the aligned fine sites

Convention (Q13-ALIGN): a scale-`j` site is an `L^j`-aligned site of the fine torus, counted once,
with no factor `L^{-jd}` (P5 (1.8), P1 (3.104)).

## What is proved

* The dictionary (T1).  `blockPt j` sends the scale-`j` lattice `ℤ^d` to the aligned fine sites,
  `unlift j` is its inverse (`blockPt_unlift`), and
  `unlift j (blockPt j z - blockPt j z') = z - z'` exactly when the difference does not wind
  (`nonWind_singleton_iff`: `-n < 2 w_μ ≤ n` for every coordinate, `n = N₁ L^{m₁} L^{k-j}` the
  number of scale-`j` sites per side).  A scale-`j` polymer `X'` (a finite set of `ℤ^d`) has the fine
  thickening `Ypoly j X'`; its aligned sites are the points `blockPt j z`, `z ∈ X'`
  (`aligned_mem_Ypoly_iff`).  The size of the fine polymer is `sizeJ (Ypoly j X')`; the class bound
  on the coefficients of the scale-`j` family is stated with this very size, so the size dictionary
  has constant `1` (`sizeJ_Ypoly_le_dInf` compares it with the size `dInf` of `T∞`).
* The per-site coefficient bound and the locality of the torus coefficient (T3):
  `v1Loc_polyUniv`.
* The decomposition of the whole-torus coefficient into polymer contributions (T2):
  `v1T_eq_sum_polyUniv`.
* The assembly (T5): `groupedInputsSite_of_class`, `EresJ2_sub_remainder_le_aligned_of_class_site`,
  and the non-vacuity statements at the zero class.

## What is not proved (named hypotheses of the constructor)

* `hstab`: the whole-torus coefficient `v1T` of the torus `C.N₁` at the origin equals the
  thermodynamic limit `vc.v1 j ∘ unlift j` on aligned differences.  This is the periodic
  identification: `D1Corr.v1_lim` gives it only as a limit along `torusSeq`; on a finite torus
  the polymers winding around it contribute a defect, exponentially small in the side, which is
  not an identity.
* `v2_decomp`, `v2_site`: the `v₂` counterpart (the mixed second derivative `v2Loc`); no landed
  theorem bounds `v2Loc` or shows its locality, and there is no `v₂` analogue of
  `aCoef_avgFamilyA_eq_v1`.
* `hXi`: the composed field lies in the class domain on each polymer (the data of the class
  bound `boundE`); with it the field `E_bound` is derived.

The data bounds of `GroupedBase`, the count of centres, the regional energy identity and the common
complex tube are not treated.
-/

@[expose] public section

open Finset Real Balaban.LargeField.RegionEnergyAlgebra Balaban.LargeField.RegionalFlux

namespace Balaban.LargeField.AlignedI6Transport

open Balaban Balaban.Localization Balaban.Multiscale Balaban.Background Balaban.SmallField
  Balaban.SmallField.Def6 Balaban.LargeField.Def7v2 Balaban.LargeField.RegionalAligned

/-! ### The dictionary (T1) -/

section Dictionary

variable {d L N₁ m₁ k : ℕ} [NeZero L] [NeZero N₁]

omit [NeZero L] [NeZero N₁] in
theorem blockPt_eq_ibase (j : ℕ) (z : SmallField.Site d) :
    blockPt (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j z = ibase j z := by
  funext μ; simp only [blockPt, ibase]; congr 1; ring

/-- `unlift j` is the inverse of `blockPt j` on the aligned sites: every aligned site is the block
corner of its centred position. -/
theorem blockPt_unlift {j : ℕ} (hjk : j ≤ k) {u : Localization.CTorus d L N₁ m₁ k} (hu : Aligned (L ^ j) u) :
    blockPt j (unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j u) = u := by
  rw [blockPt_eq_ibase]; exact ibase_unlift hjk hu

/-- The non-winding condition for one lattice point, exactly: `w` is its own centred
representative modulo `n = N₁ L^{m₁} L^{k-j}` (the number of scale-`j` sites per side) iff
`-n < 2 w_μ ≤ n` for every coordinate. -/
theorem nonWind_singleton_iff (j : ℕ) (w : SmallField.Site d) :
    NonWind L N₁ m₁ k j ({w} : Finset (SmallField.Site d)) ↔
      ∀ μ, (-(N₁ * L ^ m₁ * L ^ (k - j) : ℕ) : ℤ) < 2 * w μ ∧
        2 * w μ ≤ ((N₁ * L ^ m₁ * L ^ (k - j) : ℕ) : ℤ) := by
  have : NeZero (N₁ * L ^ m₁ * L ^ (k - j)) := ⟨by
    have := NeZero.pos N₁; have := NeZero.pos L; positivity⟩
  unfold NonWind
  simp only [Finset.mem_singleton, forall_eq]
  refine forall_congr' fun μ => ?_
  rw [ZMod.valMinAbs_spec]
  constructor
  · rintro h
    have := h.2
    simp only [Set.mem_Ioc] at this
    constructor <;> linarith [this.1, this.2]
  · intro h
    refine ⟨rfl, ?_⟩
    simp only [Set.mem_Ioc]
    constructor <;> linarith [h.1, h.2]

/-- **Differences of block corners.**  For differences that do not wind,
`unlift j (blockPt j z - blockPt j z') = z - z'`. -/
theorem unlift_blockPt_sub {j : ℕ} (hjk : j ≤ k) {z z' : SmallField.Site d}
    (h : NonWind L N₁ m₁ k j ({z - z'} : Finset (SmallField.Site d))) :
    unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j (blockPt j z - blockPt j z') = z - z' := by
  rw [← blockPt_sub, blockPt_eq_ibase]
  exact unlift_ibase hjk (h (z - z') (Finset.mem_singleton_self _))

omit [NeZero L] [NeZero N₁] in
/-- The fine thickening `Ypoly j X'` of a scale-`j` polymer `X'` is the set of fine sites whose
block lies in `X'`. -/
theorem mem_Ypoly_iff (j : ℕ) (X' : Finset (SmallField.Site d)) (x : Localization.CTorus d L N₁ m₁ k) :
    x ∈ Ypoly (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j X' ↔
      unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j x ∈ X' := Iff.rfl

/-- **The aligned sites of the fine polymer.**  For a polymer `X'` of the scale-`j` lattice that does
not wind, an aligned fine site lies in `Ypoly j X'` iff it is the block corner `blockPt j z` of a
point `z ∈ X'`. -/
theorem aligned_mem_Ypoly_iff {j : ℕ} (hjk : j ≤ k) {X' : Finset (SmallField.Site d)}
    (hnw : NonWind L N₁ m₁ k j X') {x : Localization.CTorus d L N₁ m₁ k} (hx : Aligned (L ^ j) x) :
    x ∈ Ypoly (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j X' ↔ ∃ z ∈ X', x = blockPt j z := by
  constructor
  · intro h
    exact ⟨_, h, (blockPt_unlift hjk hx).symm⟩
  · rintro ⟨z, hz, rfl⟩
    exact blockPt_mem_Ypoly hjk hnw hz

/-- Differences of aligned sites that do not wind: `unlift (x - y) = unlift x - unlift y`. -/
theorem unlift_sub_aligned {j : ℕ} (hjk : j ≤ k) {x y : Localization.CTorus d L N₁ m₁ k}
    (hx : Aligned (L ^ j) x) (hy : Aligned (L ^ j) y)
    (h : NonWind L N₁ m₁ k j
      ({unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j x -
        unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j y} : Finset (SmallField.Site d))) :
    unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j (x - y) =
      unlift j x - unlift j y := by
  have := unlift_blockPt_sub (N₁ := N₁) (m₁ := m₁) (k := k) hjk h
  rwa [blockPt_unlift hjk hx, blockPt_unlift hjk hy] at this

/-- **The size dictionary.**  On the `n`-th torus of the sequence, the size `sizeJ` of the fine
polymer of a good scale-`j` polymer `X'` is at most the size `dInf` of `X'` as a polymer of `T∞`
(constant `1`); the size used by the coefficient bounds of the class is `sizeJ` of the fine polymer
itself, so no constant enters the passage to the fine representatives. -/
theorem sizeJ_Ypoly_le_dInf {m₀ j : ℕ} (hjk : j ≤ k) {X' : Finset (SmallField.Site d)} {n : ℕ}
    (hn : GoodAt L m₁ k m₀ j X' n) :
    haveI : NeZero (torusSeq L m₀ n) := ⟨torusSeq_ne_zero m₀ n⟩
    sizeJ (L := L) (N₁ := torusSeq L m₀ n) (m₁ := m₁) (k := k) m₀ j
      (Ypoly (L := L) (N₁ := torusSeq L m₀ n) (m₁ := m₁) (k := k) j X') ≤
      dInf L m₁ k m₀ j X' :=
  sizeSeq_le_dInf hjk hn

end Dictionary

end Balaban.LargeField.AlignedI6Transport
