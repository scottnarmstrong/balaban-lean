/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.DecLogCutFactor
public import Balaban.Fluctuation.RootDetCutSupport
import Mathlib.Tactic.Linarith

/-!
# The thickened interaction cubes as unions of cells; components of `Yreg` as unions of blocks

Settles the last proviso `UnionOfBlocks` of `DecLogCutFactor.lean` (DET-CUT-FACTOR).

**T1 (shape of one box).** For a centre `q = (j, y₀)` with `y₀` a multiple of `B = L ^ (j + m₁)`
the thickened cube `hatBox q` has half-width `5/2 B + 3 L² L^j` (open, sup distance) around the
centre `y₀ + (B - 1)/2`. On the integers this is the interval `[y₀ - 2B - 3L^(j+2), y₀ + 3B +
3L^(j+2) - 1]` in each coordinate. The half-integer in `5/2` is compensated by the centre
`(B - 1)/2`, so no parity of `L` enters. As `m₁ ≥ 2`, `y₀`, `B` and `3 L^(j+2)` are multiples of
`L^(j+2)`: `hatBox q` is a union of cells of side `L^(j+2)` (`hatBox_sameCell`).

**T2 (which blocks matter).** A site of layer `n` in `hatBox q` has `n ≤ q.1 + 1`
(`layer_le_of_mem_hatBox`). A top-layer site (`n = k + 1`) therefore lies only in boxes with
`q.1 ≥ k`, whose cells have side at least `L^(k+2)`, a multiple of the block side `L^(k+1)`. So
the part of a component of `Yreg` in the top layer is a union of `(k+1)`-blocks
(`hatBox_sameCell_top`, `unionOfTopBlocks_of_isNnComp`). Lower-layer sites of `Ω₁` need not be
unions of `(k+1)`-blocks (blocks of the lower layers are smaller, and `Ω₁` itself is only a union
of `1`-blocks), so the full `UnionOfBlocks G Y'` of `DecLogCutFactor.lean` is not what is true; but
it is not what is used: `unitQ`, `unitP` only see top-layer sites (`IsUnitLattice.layer`). The
property that is proved, and used, is `UnionOfTopBlocks` (the same statement for a top-layer site
`y`); it coincides with `UnionOfBlocks` when `Ω₁ = Ω_{k+1}`.

The decay bound and the count of cut sets are not proved here.
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background Finset Matrix

section Coord

/-- The elementary integer inequality behind the cell description of the thickened cube:
for `w = A m + r` with `0 ≤ r < A`, `|w - (A b - 1)/2| < 5/2 A b + 3 A` iff
`-(2b+3) ≤ m ≤ 3b+2`. -/
theorem abs_lt_hat_iff {A b : ℕ} (hA : 0 < A) (m r : ℤ) (hr0 : 0 ≤ r) (hrA : r < A) :
    |(((A : ℤ) * m + r : ℤ) : ℝ) - (((A : ℝ) * b - 1) / 2)| < 5 / 2 * ((A : ℝ) * b) + 3 * A ↔
      -((2 * b + 3 : ℕ) : ℤ) ≤ m ∧ m ≤ ((3 * b + 2 : ℕ) : ℤ) := by
  have hA' : (0 : ℤ) < A := by exact_mod_cast hA
  rw [abs_lt]
  push_cast
  constructor
  · rintro ⟨h1, h2⟩
    have e1 : (0 : ℝ) < ((2 * (A * m + r) + 4 * A * b + 6 * A + 1 : ℤ) : ℝ) := by
      push_cast; linarith
    have e2 : (0 : ℝ) < ((6 * A * b + 6 * A - 1 - 2 * (A * m + r) : ℤ) : ℝ) := by
      push_cast; linarith
    have e1' : (0 : ℤ) < 2 * (A * m + r) + 4 * A * b + 6 * A + 1 := by exact_mod_cast e1
    have e2' : (0 : ℤ) < 6 * A * b + 6 * A - 1 - 2 * (A * m + r) := by exact_mod_cast e2
    constructor
    · by_contra hc
      push Not at hc
      have : m + (2 * b + 3) ≤ -1 := by linarith
      nlinarith
    · by_contra hc
      push Not at hc
      have : 3 * b + 3 ≤ m := by linarith
      nlinarith
  · rintro ⟨h1, h2⟩
    have f1 : (0 : ℤ) ≤ A * (m + (2 * b + 3)) := by
      apply mul_nonneg hA'.le; linarith
    have f2 : (0 : ℤ) ≤ A * ((3 * b + 2) - m) := by
      apply mul_nonneg hA'.le; linarith
    have g1 : ((0 : ℤ) : ℝ) ≤ ((A * (m + (2 * b + 3)) : ℤ) : ℝ) := by exact_mod_cast f1
    have g2 : ((0 : ℤ) : ℝ) ≤ ((A * ((3 * b + 2) - m) : ℤ) : ℝ) := by exact_mod_cast f2
    have hr0' : (0 : ℝ) ≤ r := by exact_mod_cast hr0
    have hrA' : (r : ℝ) + 1 ≤ A := by exact_mod_cast (by omega : r + 1 ≤ (A : ℤ))
    push_cast at g1 g2
    constructor <;> nlinarith


end Coord

section Box

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
variable {G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ}

omit [NeZero N₁] in
/-- Coordinatewise form of `hatBox`: with cells of side `A = L ^ (j + 2)`, the coordinate of `x` lies
in the thickened interval iff the cell index of `x` is within `[-(2b+3), 3b+2]` of that of the base,
periodically; here `b = L ^ (m₁ - 2)`, so `B = A b`. -/
theorem hat_coord_iff {j : ℕ} (hj : j ≤ K) (hm : 2 ≤ m₁) {y0 x : CTorus d L N₁ m₁ K}
    (hb : CubeBase m₁ j y0) (μ : Fin d) :
    (∃ p : ℤ, |((x μ).val : ℝ) + p * (((N₁ * L ^ m₁) * L ^ K : ℕ) : ℝ) -
      (((y0 μ).val : ℝ) + ((L : ℝ) ^ (j + m₁) - 1) / 2)| < hatRad L m₁ j) ↔
    ∃ p : ℤ, -((2 * L ^ (m₁ - 2) + 3 : ℕ) : ℤ) ≤
        (((x μ).val / L ^ (j + 2) : ℕ) : ℤ) + p * ((((N₁ * L ^ m₁) * L ^ K) / L ^ (j + 2) : ℕ) : ℤ)
          - (((y0 μ).val / L ^ (j + 2) : ℕ) : ℤ) ∧
      (((x μ).val / L ^ (j + 2) : ℕ) : ℤ) + p * ((((N₁ * L ^ m₁) * L ^ K) / L ^ (j + 2) : ℕ) : ℤ)
          - (((y0 μ).val / L ^ (j + 2) : ℕ) : ℤ) ≤ ((3 * L ^ (m₁ - 2) + 2 : ℕ) : ℤ) := by
  have hApos : 0 < L ^ (j + 2) := pow_pos (Nat.pos_of_ne_zero (NeZero.ne L)) _
  obtain ⟨n, hn⟩ : L ^ (j + 2) ∣ (N₁ * L ^ m₁) * L ^ K := by
    have : L ^ (j + 2) ∣ L ^ m₁ * L ^ K := by
      rw [← pow_add]; exact pow_dvd_pow L (by omega)
    exact this.trans ⟨N₁, by ring⟩
  have hnn : ((N₁ * L ^ m₁) * L ^ K) / L ^ (j + 2) = n := by
    rw [hn]; exact Nat.mul_div_cancel_left _ hApos
  rw [hnn]
  set A : ℕ := L ^ (j + 2) with hAdef
  set b : ℕ := L ^ (m₁ - 2) with hbdef
  have hBA : L ^ (j + m₁) = A * b := by
    rw [hAdef, hbdef, ← pow_add]; congr 1; omega
  obtain ⟨c, hc⟩ : A ∣ (y0 μ).val := by
    have h1 : L ^ (j + m₁) ∣ (y0 μ).val := Nat.dvd_of_mod_eq_zero (hb μ)
    rw [hBA] at h1
    exact (Dvd.intro _ rfl).trans h1
  set a : ℕ := (x μ).val / A with ha
  set r : ℕ := (x μ).val % A with hr
  have hx : (x μ).val = A * a + r := (Nat.div_add_mod _ _).symm
  have hcdiv : (y0 μ).val / A = c := by rw [hc]; exact Nat.mul_div_cancel_left _ hApos
  rw [hcdiv]
  have hrA : r < A := Nat.mod_lt _ hApos
  have hrad : hatRad L m₁ j = 5 / 2 * ((A : ℝ) * b) + 3 * A := by
    unfold hatRad
    have h1 : ((L : ℝ) ^ (j + m₁)) = (A : ℝ) * b := by
      have := congrArg (fun t : ℕ => (t : ℝ)) hBA
      simpa using this
    rw [h1]
    have h2 : (A : ℝ) = (L : ℝ) ^ (j + 2) := by rw [hAdef]; push_cast; rfl
    rw [h2]; ring
  refine exists_congr fun p => ?_
  rw [hrad]
  have hB : ((L : ℝ) ^ (j + m₁)) = (A : ℝ) * b := by
    have := congrArg (fun t : ℕ => (t : ℝ)) hBA
    simpa using this
  have e : ((x μ).val : ℝ) + p * (((N₁ * L ^ m₁) * L ^ K : ℕ) : ℝ) -
      (((y0 μ).val : ℝ) + ((L : ℝ) ^ (j + m₁) - 1) / 2) =
      (((A : ℤ) * ((a : ℤ) + p * n - c) + (r : ℤ) : ℤ) : ℝ) - (((A : ℝ) * b - 1) / 2) := by
    have hNr : (((N₁ * L ^ m₁) * L ^ K : ℕ) : ℝ) = (A : ℝ) * n := by
      have := congrArg (fun t : ℕ => (t : ℝ)) hn
      simpa using this
    have hxr : ((x μ).val : ℝ) = (A : ℝ) * a + r := by exact_mod_cast hx
    have hyr : ((y0 μ).val : ℝ) = (A : ℝ) * c := by exact_mod_cast hc
    rw [hNr, hxr, hyr, hB]; push_cast; ring
  rw [e, abs_lt_hat_iff hApos _ _ (by positivity) (by exact_mod_cast hrA)]

/-- **T1. The thickened cube is a union of cells of side `L ^ (j + 2)`** (`m₁ ≥ 2`). -/
theorem hatBox_sameCell {j : ℕ} (hj : j ≤ K) (hm : 2 ≤ m₁) {q : ℕ × CTorus d L N₁ m₁ K}
    (hq : q.1 = j) (hb : CubeBase m₁ j q.2) {x x' : CTorus d L N₁ m₁ K}
    (h : SameCell (L ^ (j + 2)) x x') : x ∈ hatBox q ↔ x' ∈ hatBox q := by
  unfold hatBox
  rw [mem_boxSet, mem_boxSet]
  unfold InBox
  rw [hq]
  refine forall_congr' fun μ => ?_
  rw [hat_coord_iff hj hm hb, hat_coord_iff hj hm hb, h μ]

/-- **T2. Layers in a thickened cube.** A site of layer `n` in `hatBox q` has `n ≤ q.1 + 1`. -/
theorem layer_le_of_mem_hatBox (hϱ : (4 * d * L * (L : ℝ) ^ m₁ : ℝ) ≤ ϱ)
    (hM : 4 * L ^ 2 ≤ L ^ m₁) (hL : 1 ≤ L)
    {q : ℕ × CTorus d L N₁ m₁ K} (hq : q ∈ cubeIdx G) {n : ℕ} (hn1 : 1 ≤ n) (hnK : n ≤ K)
    {x : CTorus d L N₁ m₁ K} (hx : x ∈ G.layer n) (hb : x ∈ hatBox q) : n ≤ q.1 + 1 := by
  obtain ⟨⟨hm1, hmK⟩, hl, hbase⟩ := (mem_cubeIdx G).1 hq
  have hdist := torusDist_le_of_inBox ((mem_boxSet).1 hb)
  have hM' : (4 : ℝ) * (L : ℝ) ^ 2 ≤ (L : ℝ) ^ m₁ := by exact_mod_cast hM
  have hLj : (1 : ℝ) ≤ (L : ℝ) ^ q.1 := one_le_pow₀ (by exact_mod_cast hL)
  have hd1 : (0 : ℝ) ≤ d := by positivity
  have hlam : (L : ℝ) ^ (q.1 + m₁) = (L : ℝ) ^ q.1 * (L : ℝ) ^ m₁ := pow_add _ _ _
  have hl0 : (0 : ℝ) ≤ (L : ℝ) ^ (q.1 + m₁) := by positivity
  have key : hatRad L m₁ q.1 + (L : ℝ) ^ (q.1 + m₁) / 2 ≤ 4 * (L : ℝ) ^ (q.1 + m₁) := by
    unfold hatRad
    have := mul_le_mul_of_nonneg_right hM' (by linarith : (0 : ℝ) ≤ (L : ℝ) ^ q.1)
    rw [hlam] at *
    nlinarith
  have := layer_bounds_cube m₁ G hϱ hm1 hmK hn1 hnK hx hl
    (hdist.trans (by nlinarith [mul_le_mul_of_nonneg_left key hd1])) hL
  exact this.1

/-- **T2/T3a. A top-layer site of a thickened cube carries its whole `(k+1)`-block with it.**
If `x` is a top-layer site (`K = k + 1`) of `hatBox q` and `x'` lies in the same `L^(k+1)`-block
as `x`, then `x'` lies in `hatBox q`. -/
theorem hatBox_sameCell_top {k : ℕ} {a : ℕ → ℝ} {ν : ℝ} {G : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
    (S : DGSetting G a ν) {q : ℕ × CTorus d L N₁ m₁ (k + 1)} (hq : q ∈ cubeIdx G)
    {x x' : CTorus d L N₁ m₁ (k + 1)} (hx : x ∈ G.layer (k + 1)) (hxb : x ∈ hatBox q)
    (hsame : SameCell (L ^ (k + 1)) x x') : x' ∈ hatBox q := by
  obtain ⟨⟨hm1, hmK⟩, hl, hbase⟩ := (mem_cubeIdx G).1 hq
  have hle := layer_le_of_mem_hatBox S.cover_sep S.hM (by have := S.hL; omega) hq
    (by omega) le_rfl hx hxb
  have hcell : SameCell (L ^ (q.1 + 2)) x x' :=
    hsame.mono (pow_dvd_pow L (by omega))
  exact (hatBox_sameCell hmK S.aligned.two_le rfl hbase hcell).1 hxb

end Box

section Components

variable {d L N₁ m₁ k : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
variable {G : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ} {a : ℕ → ℝ} {ν : ℝ}

/-- `Y'` is a union of `L ^ (k+1)`-blocks as seen from the top layer: a site of `Ω₁` in the same
`(k+1)`-block as a top-layer site of `Y'` lies in `Y'`. (A block that contains one top-layer site
lies entirely in the top layer, since `Ω_{k+1}` is a union of `(k+1)`-blocks.) This is the part of
`UnionOfBlocks` that `unitQ`, `unitP` use; the two agree when `Ω₁ = Ω_{k+1}`. -/
abbrev UnionOfTopBlocks (G : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ)
    (Y' : Finset (CTorus d L N₁ m₁ (k + 1))) : Prop :=
  ∀ y y' : G.Ω 1, (y : CTorus d L N₁ m₁ (k + 1)) ∈ G.layer (k + 1) →
    jBlock d L (N₁ * L ^ m₁) (k + 1) (k + 1) (y : CTorus d L N₁ m₁ (k + 1)) =
      jBlock d L (N₁ * L ^ m₁) (k + 1) (k + 1) (y' : CTorus d L N₁ m₁ (k + 1)) →
    (y : CTorus d L N₁ m₁ (k + 1)) ∈ Y' → (y' : CTorus d L N₁ m₁ (k + 1)) ∈ Y'

/-- `UnionOfBlocks` implies `UnionOfTopBlocks`. -/
theorem UnionOfBlocks.top {Y' : Finset (CTorus d L N₁ m₁ (k + 1))} (h : UnionOfBlocks G Y') :
    UnionOfTopBlocks G Y' := fun y y' _ => h y y'

/-- When `Ω₁` is the top layer, the two properties agree. -/
theorem UnionOfTopBlocks.unionOfBlocks {Y' : Finset (CTorus d L N₁ m₁ (k + 1))}
    (hΩ : ∀ y : G.Ω 1, (y : CTorus d L N₁ m₁ (k + 1)) ∈ G.layer (k + 1))
    (h : UnionOfTopBlocks G Y') : UnionOfBlocks G Y' := fun y y' => h y y' (hΩ y)

/-- **T3a. The components of `Yreg` are unions of `(k+1)`-blocks at the top layer.** Every union
`Y'` of nearest-neighbour components of `Yreg G s` satisfies `UnionOfTopBlocks G Y'`, under the
standing geometric hypotheses (`DGSetting`: cube alignment, `4 L² ≤ L^m₁`, cover separation) and
`HatConn`. Reason: a top-layer site lies only in thickened cubes of scale `q.1 ≥ k`
(`layer_le_of_mem_hatBox`), which are unions of cells of side `L^(q.1+2)`, a multiple of the
block side (`hatBox_sameCell_top`); a block is then inside one `hatI q`, which is connected, hence
inside one component. -/
theorem unionOfTopBlocks_of_isNnComp (S : DGSetting G a ν) (hconn : HatConn G)
    {s : ℕ × CTorus d L N₁ m₁ (k + 1) → ℂ} {Y' : Finset (CTorus d L N₁ m₁ (k + 1))}
    (hY : IsNnComp (Yreg G s) Y') : UnionOfTopBlocks G Y' := by
  classical
  intro y y' hyl hbl hyY
  have hyYreg := hY.1 hyY
  unfold Yreg at hyYreg
  rw [Finset.mem_filter, Finset.mem_biUnion] at hyYreg
  obtain ⟨⟨z, hzZ, hyz⟩, -⟩ := hyYreg
  have hz : z ∈ cubeIdx G := (Finset.mem_filter.1 hzZ).1
  have hsame : SameCell (L ^ (k + 1)) (y : CTorus d L N₁ m₁ (k + 1)) y' :=
    sameCell_of_jBlock_eq le_rfl hbl
  have hy'z := hatBox_sameCell_top S hz hyl hyz hsame
  have hyI : (y : CTorus d L N₁ m₁ (k + 1)) ∈ hatI G z := by
    unfold hatI; rw [Finset.mem_filter]; exact ⟨hyz, y.2⟩
  have hy'I : (y' : CTorus d L N₁ m₁ (k + 1)) ∈ hatI G z := by
    unfold hatI; rw [Finset.mem_filter]; exact ⟨hy'z, y'.2⟩
  have hsub : hatI G z ⊆ Yreg G s := by
    intro x hx
    unfold hatI at hx
    rw [Finset.mem_filter] at hx
    unfold Yreg
    rw [Finset.mem_filter, Finset.mem_biUnion]
    exact ⟨⟨z, hzZ, hx.1⟩, hx.2⟩
  rcases connIn_dichotomy (hconn z hz) hsub hY with h | h
  · exact h hy'I
  · exact absurd hyY (Finset.disjoint_left.1 h hyI)

/-- The hypotheses of `unionOfTopBlocks_of_isNnComp` in the form of the full structure
`UnionOfBlocks`, for a generating set whose domain `Ω₁` is the top layer. -/
theorem unionOfBlocks_of_isNnComp (S : DGSetting G a ν) (hconn : HatConn G)
    (hΩ : ∀ y : G.Ω 1, (y : CTorus d L N₁ m₁ (k + 1)) ∈ G.layer (k + 1))
    {s : ℕ × CTorus d L N₁ m₁ (k + 1) → ℂ} {Y' : Finset (CTorus d L N₁ m₁ (k + 1))}
    (hY : IsNnComp (Yreg G s) Y') : UnionOfBlocks G Y' :=
  (unionOfTopBlocks_of_isNnComp S hconn hY).unionOfBlocks hΩ

theorem unitQ_label_top {Y' : Finset (CTorus d L N₁ m₁ (k + 1))} (hY : UnionOfTopBlocks G Y') :
    BD (unitLabel G Y') (fun y : G.Ω 1 => (y : CTorus d L N₁ m₁ (k + 1)) ∈ Y') (unitQ G) := by
  intro b y h
  have hb : unitBlock (y : CTorus d L N₁ m₁ (k + 1)) = (b : UnitTorus d L N₁ m₁ k) := by
    by_contra hne
    exact h (by simp [unitQ, hne])
  have hyl : (y : CTorus d L N₁ m₁ (k + 1)) ∈ G.layer (k + 1) :=
    (unitBlock_mem_iff G _).1 (hb ▸ b.2)
  constructor
  · intro hc; exact hc y hb
  · intro hy y' hy'
    exact hY y y' hyl (jBlock_eq_of_unitBlock_eq (hb.trans hy'.symm)) hy

theorem unitP_label_top {Y' : Finset (CTorus d L N₁ m₁ (k + 1))} (hY : UnionOfTopBlocks G Y') :
    BD (unitLabel G Y') (unitLabel G Y') (unitP G) := by
  have key : ∀ b b' : unitPts G,
      unitBlock1 (b : UnitTorus d L N₁ m₁ k) = unitBlock1 (b' : UnitTorus d L N₁ m₁ k) →
      unitLabel G Y' b → unitLabel G Y' b' := by
    intro b b' hbb hc y' hy'
    obtain ⟨x, hx, hxb⟩ := (mem_unitPts G).1 b.2
    have hxΩ : x ∈ G.Ω 1 := G.layer_subset (by omega) le_rfl hx
    have hxY := hc ⟨x, hxΩ⟩ hxb
    refine hY ⟨x, hxΩ⟩ y' hx ?_ hxY
    show jBlock d L (N₁ * L ^ m₁) (k + 1) (k + 1) x = jBlock d L (N₁ * L ^ m₁) (k + 1) (k + 1) y'
    rw [← unitBlock1_unitBlock, ← unitBlock1_unitBlock, hxb, hy', hbb]
  intro b b' h
  have hbb : unitBlock1 (b : UnitTorus d L N₁ m₁ k) = unitBlock1 (b' : UnitTorus d L N₁ m₁ k) := by
    by_contra hne
    exact h (by simp [unitP, hne])
  exact ⟨key b b' hbb, key b' b hbb.symm⟩

/-- **T3a. `decLog` of the step is block diagonal for the unit lattice**, for every union `Y'` of
nearest-neighbour components of `Yreg s`. Hypotheses: `CovStanding` for `unitQ`, `unitP` (all
`x ≥ 0`), `HatConn`, and `DGSetting` (the geometric standing hypotheses); no union-of-blocks
hypothesis. The labels are `unitLabel G Y'`: the unit block lies in `Y'`. -/
theorem CovStanding.decLog_BD_unit {aT : ℝ} {N : ℕ} {α : G.Ω 1 → ℂ} {κ δ : ℝ}
    {s : ℕ × CTorus d L N₁ m₁ (k + 1) → ℂ} {φ : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ}
    (H : CovStanding G a aT ν α κ s δ φ (unitQ G) (unitP G)) (hconn : HatConn G)
    {Y' : Finset (CTorus d L N₁ m₁ (k + 1))} (hY : IsNnComp (Yreg G s) Y') :
    BD (fun p : unitPts G × Fin N => unitLabel G Y' p.1)
      (fun p : unitPts G × Fin N => unitLabel G Y' p.1) (decLog G a aT ν α s φ (unitQ G) (unitP G)) :=
  H.decLog_BD_of_respects hconn hY
    (fun x hx => hRespects_of_hatConn (H.fam x hx.le).st hconn hY) (unitLabel G Y')
    (unitQ_label_top (unionOfTopBlocks_of_isNnComp (H.fam 0 le_rfl).st.dg hconn hY))
    (unitP_label_top (unionOfTopBlocks_of_isNnComp (H.fam 0 le_rfl).st.dg hconn hY))

end Components

end Balaban.Localization

namespace Balaban.Fluctuation

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization Balaban.Analysis
  Finset Matrix

section UnitTrace

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
variable {G : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ} {a : ℕ → ℝ} {aT ν κ κ' δ δ' : ℝ}

/-- **Locality of the rooted trace for the unit lattice, without `UnionOfBlocks`.** The specialisation
of `rootTrace_eq_of_comp` to `Q = unitQ G`, `P = unitP G`, the labels `unitLabel G Y'`, and a set
`B` of unit points whose blocks lie in `Y'`. -/
theorem rootTrace_eq_of_comp_unit {s s' : DecParams G}
    {α α' : G.Ω 1 → ℂ} {φ φ' : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ}
    (H : CovStanding G a aT ν α κ (extS G s) δ φ (unitQ G) (unitP G))
    (H' : CovStanding G a aT ν α' κ' (extS G s') δ' φ' (unitQ G) (unitP G)) (hconn : HatConn G)
    {Y' : Finset (CTorus d L N₁ m₁ (k + 1))} (hY : IsNnComp (Yreg G (extS G s)) Y')
    (hY' : IsNnComp (Yreg G (extS G s')) Y')
    (hs : ∀ q ∈ cubeIdx G, SubI G (intBox q) Y' → ∀ R ∈ Qset G q, extS G s R = extS G s' R)
    (hA : ∀ y : G.Ω 1, (y : CTorus d L N₁ m₁ (k + 1)) ∈ Y' → α y = α' y)
    (hφ : ∀ y : CTorus d L N₁ m₁ (k + 1), y ∈ Y' → φ y = φ' y)
    (B : Finset (unitPts G)) (hB : ∀ y ∈ B, unitLabel G Y' y) :
    rootTrace G a aT ν (unitQ G) (unitP G) B s φ α =
      rootTrace G a aT ν (unitQ G) (unitP G) B s' φ' α' :=
  rootTrace_eq_of_comp H H' hconn hY hY' hs hA hφ (unitLabel G Y')
    (unitQ_label_top (unionOfTopBlocks_of_isNnComp (H.fam 0 le_rfl).st.dg hconn hY))
    (unitP_label_top (unionOfTopBlocks_of_isNnComp (H.fam 0 le_rfl).st.dg hconn hY)) B hB

section Cuts

variable (S : XSetting G a aT ν) {κ : ℝ} (hκ : 0 < κ)
  (hM : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δ : ℝ} (hδ : 0 ≤ δ)
  (hsm : δ ^ 2 * smallConstX d L κ ≤ 1 / 4)
  {φ : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ} (hφ : IsConstraintFieldStrict G δ φ)
  {α : G.Ω 1 → ℂ}
  (hα : ∀ w, ‖α w‖ < coerciveConst d / (2 * (G.spacing (w : CTorus d L N₁ m₁ (k + 1))) ^ 2))

include S hκ hM hδ hsm hφ hα

/-- **T4. Vanishing of the mixed difference of the rooted trace of the root block: geometric form.**
`B` is a set of unit points (for the determinant, the unit points of one `L`-block of the unit
lattice, `StepObjects.blockU z`). Let `J` contain the parameter cube `p`. Suppose that at every
`{0,1}`-valued cut point `σ` and for `t ∈ {0,1}` there is a set `Y'` which is a union of
nearest-neighbour components of both `Yreg (extS σ)` and `Yreg (extS (σ[p ↦ t]))`, which contains
all the `Ω₁`-sites of the unit blocks of `B`, and such that no cube `q` of the cover with
`□_q ⊆ Y'` has the parameter cube `p` in its footprint `𝒬(q)`. Then `mixDiff J` of the rooted trace
vanishes. (The common component is the component of the root block, which is the same for the two
values of the parameter `p`; the last condition says that the cut factors of the cubes inside it
do not see `p`.) No `UnionOfBlocks` hypothesis. -/
theorem mixDiff_rootTrace_unit_eq_zero_of_root_component (B : Finset (unitPts G))
    (hconn : HatConn G) {J : Finset (cubeIdx G)} {p : cubeIdx G} (hp : p ∈ J)
    (hgeom : ∀ σ : DecParams G, (∀ q, σ q = 0 ∨ σ q = 1) → ∀ t : ℂ, (t = 0 ∨ t = 1) →
      ∃ Y' : Finset (CTorus d L N₁ m₁ (k + 1)),
        IsNnComp (Yreg G (extS G σ)) Y' ∧
        IsNnComp (Yreg G (extS G (Function.update σ p t))) Y' ∧
        (∀ y ∈ B, unitLabel G Y' y) ∧
        ∀ q ∈ cubeIdx G, SubI G (intBox q) Y' → (p : ℕ × CTorus d L N₁ m₁ (k + 1)) ∉ Qset G q) :
    mixDiff J (fun s => rootTrace G a aT ν (unitQ G) (unitP G) B s φ α) = 0 := by
  classical
  refine mixDiff_rootTrace_eq_zero_of_separated S hκ hM hδ hsm
    (isUnitLatticeB_unit (G := G)).toIsUnitLattice hφ hα B hconn hp ?_
  intro σ h01 t ht
  obtain ⟨Y', hY, hY', hB, hpq⟩ := hgeom σ h01 t ht
  refine ⟨Y', unitLabel G Y', hY, hY', ?_, unitQ_label_top
    (unionOfTopBlocks_of_isNnComp S.dg hconn hY), unitP_label_top
    (unionOfTopBlocks_of_isNnComp S.dg hconn hY), hB⟩
  intro q hq hsub R hR
  have hRc : R ∈ cubeIdx G := Qset_subset_cubeIdx q hR
  have hne : (⟨R, hRc⟩ : cubeIdx G) ≠ p := by
    intro h
    exact hpq q hq hsub (by rw [← h]; exact hR)
  unfold extS
  simp [hRc, Function.update_of_ne hne]

end Cuts

end UnitTrace

end Balaban.Fluctuation
