/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.P6PairSep
public import Balaban.Localization.PairedLocalX0
public import Balaban.SmallField.LocalGeneratorSource
public import Balaban.Localization.P6PairOp
public import Balaban.Localization.CubeBlockHolderMixed
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The distance from `X₀` to the parameter cubes at the separation `5 L M₁` (WIDEGEN route A)

`DecoupledFieldX0.scaled_dist_X0` bounds the scaled path distance from `x ∈ X₀` to the set `𝒲` of
interaction cubes depending on a parameter cube by `T = ((r₀ - 4 d L³)/L) M₁`, under the physical
collar `hN` (radius `r₀ M₁ ℓ(x)`) and `hr : r₀ M₁ ≤ ϱ - 1`, through `DGSetting` (`ℓ¹`-separation
`4 d L M₁ ≤ ϱ`).  With the literal generator of P3 (4.4)-(4.6) (`localB`, separation
`ϱ ≤ 5 L M₁`) both fail: `hr` together with `hr₀ : 4 d L³ ≤ r₀` and the cover separation
(`BgSetting.index_ge`, `DGSetting.false_of_le_minSep`).

The proof spends `hr` only on the **target** `T`: it needs `T ≤ ϱ - 1` (to exclude paths jumping
two layers and to keep the truncated physical distance), not `r₀ M₁ ≤ ϱ - 1`; and it spends the
cover separation only on the layer comparisons, which hold under the sup-separation `SupSep`
(`P6PairCover`).  So the collar radius `r₀` is decoupled from the index `ϱ`: P3's two cube sizes
(pp. 44, 57, 69: `X₀^{~r₀} ⊂ X₁` in `M₁`-cubes, `X₁` made of `M`-cubes, `M ≫ M₁`) absorb the
loss `4 d L³` into `M / M₁`, and the decay radius is `r₁ M₁` with `r₁ = (r₀ - 4 d L³)/L`.  For
`r₀ = 4 d L³ + L` this is `r₁ = 1`, P3's `r₁ = r₀ - 4 = 1` at `r₀ = 5`.

* `supSep_castG`, `supSep_minimalGenSet`, `localB_supSep`: the literal local generator
  `𝔹_j(X) = localB j hj X hsep` is sup-separated (the `5 L M₁ ℓ_n` sup-distance of the `nearStep`
  recursion, `P6PairSep.supDist_gt_of_not_mem_nearStep`);
* `cubeAligned_castG`, `localB_cubeAligned`: it is cube aligned (`LocalGen.localGen_cubeAligned`);
* `localB_coverGeom`, `localB_coverBase`: hence its own cover satisfies the hypotheses
  `Dec2.CoverGeom`/`Dec2.CoverBase` of the cover form of Theorems I-4a/I-4b
  (`Dec2.i4b_exists_unique`, `Dec2.i4b_analytic`, `Dec2.i4a_close`), with no `ℓ¹` cover separation
  (`P6PairOp.p6_coverGeom_of_pair`, `CubeBlockHolderMixed.coverBase_mixed`);
* `layer_ge_of_mem_box_sup`, `torusDist_box_cube_le_sup`: the two geometric inputs of
  `scaled_dist_X0` under `SupSep` instead of `DGSetting`;
* `scaled_dist_X0_sup`, `siteSetDist_X0_sup`: **the `X₀` distance with the target bound
  `T ≤ ϱ - 1` only**, for a sup-separated, cube-aligned generating set;
* `target_le_minSep`, `localB_siteSetDist_X0`: at `ϱ = 5 L M₁` and `r₀ = 4 d L³ + L` the target is
  `T = M₁ ≤ ϱ - 1`, so `siteSetDist ≥ M₁` for the literal local generator;
* `i4a_close_X0_sup`: **Theorem I-4a (d) on `X₀`** in the cover form (`Dec2.i4a_close` on the pair
  `(coverOf G, G)`) for a sup-separated, cube-aligned `G`, with the factor `e^{-γ_w T}`; for
  `G = localB …` its `CoverBase` is `localB_coverBase`.
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background Balaban.LargeField Finset

/-! ### The literal local generator is sup-separated and cube aligned -/

section LocalB

/-- `SupSep` is transported along `castG`. -/
theorem supSep_castG {d L K : ℕ} [NeZero L] {N₀' N₀ : ℕ} [NeZero N₀'] [NeZero N₀] {ϱ : ℝ}
    (h : N₀' = N₀) {G : GeneratingSet d L N₀' K ϱ} {m₁ : ℕ} (hG : SupSep G m₁) :
    SupSep (SmallField.GsSpec.castG h G) m₁ := by
  subst h
  exact hG

/-- `CubeAligned` is transported along `castG`. -/
theorem cubeAligned_castG {d L K : ℕ} [NeZero L] {N₀' N₀ : ℕ} [NeZero N₀'] [NeZero N₀] {ϱ : ℝ}
    (h : N₀' = N₀) {G : GeneratingSet d L N₀' K ϱ} {m₁ : ℕ} (hG : CubeAligned G m₁) :
    CubeAligned (SmallField.GsSpec.castG h G) m₁ := by
  subst h
  exact hG

/-- **The minimal generating set of P3 (4.4)-(4.6) is sup-separated**: for `x ∉ Ω_n`,
`y ∈ Ω_{n+1}`, `supDist x y > 5 L M₁ L^n > 4 L^{n+1+m₁}` (`M₁ = L^{m₁}`). -/
theorem supSep_minimalGenSet {d M1 N₁ L q j m₁ : ℕ} [NeZero L] [NeZero M1] [NeZero N₁]
    (hj : j ≤ q) (X : Finset (Torus d (M1 * N₁ * L ^ q))) (hM1 : M1 = L ^ m₁) :
    SupSep (minimalGenSet (M1 := M1) (N₁ := N₁) (L := L) (q := q) hj X) m₁ := by
  intro n hn1 hnq x hx y hy
  rw [minimalGenSet_Ω] at hx hy
  by_cases hnj : n < j
  · rw [minLayer_of_lt X hnj] at hx
    have h := supDist_gt_of_not_mem_nearStep (q := q) (by omega : n ≤ q) hx hy
    have e : (5 * L * M1 : ℝ) * (L : ℝ) ^ n = 5 * (L : ℝ) ^ (n + 1 + m₁) := by
      rw [hM1]; push_cast; ring
    have hpos : (0 : ℝ) < (L : ℝ) ^ (n + 1 + m₁) := by
      have : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
      positivity
    rw [e] at h
    linarith
  · rw [minLayer_of_gt X (by omega : j < n + 1)] at hy
    exact absurd hy (Finset.notMem_empty _)

variable {d L N₁ m₁ k : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}

/-- **The literal local generator `𝔹_j(X) = localB j hj X hsep` is sup-separated** at every index
`ϱ ≤ 5 L M₁` (the sup-separation does not involve `ϱ`). -/
theorem localB_supSep {j : ℕ} (hj : j ≤ k) (X : Set (CTorus d L N₁ m₁ k))
    (hsep : ϱ ≤ minSep L (L ^ m₁)) : SupSep (SmallField.GsSpec.localB j hj X hsep) m₁ :=
  supSep_castG _ (supSep_minimalGenSet (M1 := L ^ m₁) (N₁ := N₁) (L := L) (q := k) hj _ rfl)

/-- **The literal local generator is cube aligned** (`M₁ = L^{m₁}`, `m₁ ≥ 2`). -/
theorem localB_cubeAligned {j : ℕ} (hj : j ≤ k) (X : Set (CTorus d L N₁ m₁ k))
    (hsep : ϱ ≤ minSep L (L ^ m₁)) (hm₁ : 2 ≤ m₁) :
    CubeAligned (SmallField.GsSpec.localB j hj X hsep) m₁ :=
  cubeAligned_castG _ (by
    refine ⟨hm₁, ?_, ?_⟩
    · exact (localGen_cubeAligned (d := d) (M1 := L ^ m₁) (N₁ := N₁) (L := L) (q := k) ∅ hj rfl
        hm₁).dvd
    · exact (localGen_cubeAligned (M1 := L ^ m₁) (N₁ := N₁) (L := L) (q := k) _ hj rfl
        hm₁).union)

/-- **The cover geometry of the literal local generator**: `Dec2.CoverGeom` of the pair
`(coverOf 𝔹, 𝔹)`, `𝔹 = localB j hj X hsep`, from its sup-separation and cube alignment (the
`ℓ¹`-separation `4 d L M₁ ≤ ϱ` of `DGSetting` is not needed). -/
theorem localB_coverGeom {j : ℕ} (hj : j ≤ k) (X : Set (CTorus d L N₁ m₁ k))
    (hsep : ϱ ≤ minSep L (L ^ m₁)) (hm₁ : 2 ≤ m₁) (hM : 4 * L ^ 2 ≤ L ^ m₁) {a : ℕ → ℝ} {ν : ℝ}
    (hd : 3 ≤ d) (hL : 3 ≤ L) (hν : 0 ≤ ν) (hνL : ν * ((L : ℝ) ^ k) ^ 2 ≤ 1)
    (ha : IsAdmissibleWeights k a) (hag : 2 * d * Real.log L ≤ agmonRate d / 16 * (ϱ - 1)) :
    Dec2.CoverGeom (coverOf (SmallField.GsSpec.localB j hj X hsep))
      (SmallField.GsSpec.localB j hj X hsep) a ν (Cchi d L) :=
  p6_coverGeom_of_pair (localB_cubeAligned hj X hsep hm₁) (localB_supSep hj X hsep)
    (SmallField.precedes_refl _) hM hd hL hν hνL ha hag

/-- **The cover base of the literal local generator**: `Dec2.CoverBase` of `(coverOf 𝔹, 𝔹)` with
the cut-operator constant `mixedKc d L` (`N₁ > 5`). -/
theorem localB_coverBase {j : ℕ} (hj : j ≤ k) (X : Set (CTorus d L N₁ m₁ k))
    (hsep : ϱ ≤ minSep L (L ^ m₁)) (hN : 5 < N₁) (hm₁ : 2 ≤ m₁) (hM : 4 * L ^ 2 ≤ L ^ m₁)
    {a : ℕ → ℝ} {ν : ℝ} (hd : 3 ≤ d) (hL : 3 ≤ L) (hν : 0 ≤ ν)
    (hνL : ν * ((L : ℝ) ^ k) ^ 2 ≤ 1) (ha : IsAdmissibleWeights k a)
    (hag : 2 * d * Real.log L ≤ agmonRate d / 16 * (ϱ - 1)) :
    Dec2.CoverBase (coverOf (SmallField.GsSpec.localB j hj X hsep))
      (SmallField.GsSpec.localB j hj X hsep) a ν (Dec2.mixedKc d L) (Cchi d L) :=
  Dec2.coverBase_mixed hN _ (localB_coverGeom hj X hsep hm₁ hM hd hL hν hνL ha hag) hνL
    (fun _ hq => hq)

end LocalB

/-! ### The geometry of `scaled_dist_X0` under the sup-separation -/

section Geometry

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
variable {G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ}

/-- **The layer of a site of `□_z` is at least `j - 1`** (sup-separation form of
`layer_ge_of_mem_box`). -/
theorem layer_ge_of_mem_box_sup (hSS : SupSep G m₁) (hL : 1 ≤ L)
    {z : ℕ × CTorus d L N₁ m₁ K} (hz : z ∈ cubeIdx G) {w : CTorus d L N₁ m₁ K}
    (hw : w ∈ intBox z) (hwΩ : w ∈ G.Ω 1) : z.1 ≤ G.layerIndex w + 1 := by
  obtain ⟨⟨hm1, hmK⟩, hl, -⟩ := (mem_cubeIdx G).1 hz
  obtain ⟨hn1, hnK, hwl⟩ := G.layerIndex_spec hwΩ
  by_cases h2 : z.1 ≤ 1
  · omega
  · have hz2 : 2 ≤ z.1 := by omega
    have hLr : (1 : ℝ) ≤ L := by exact_mod_cast hL
    have hl1 : (0 : ℝ) ≤ (L : ℝ) ^ (z.1 + m₁) := by positivity
    have hdist := supDist_le_of_inBox (by positivity) ((mem_intBox).1 hw)
    have hz2Ω : z.2 ∈ G.Ω z.1 := (G.mem_layer.1 hl).1
    have hd : (supDist z.2 w : ℝ) ≤ 4 * (L : ℝ) ^ (z.1 + m₁) := by
      rw [supDist_comm]; linarith
    have := mem_pred_cube_sup hSS hz2 hmK hz2Ω hd
    by_contra hcon
    push Not at hcon
    have hsub : w ∈ G.Ω (G.layerIndex w + 1) :=
      G.Ω_antitone (by omega) (by omega) (by omega) this
    exact (G.mem_layer.1 hwl).2 hsub

/-- **Distance from a site of `□_z` to a site of a cube `P ∈ 𝒬(z)`** (sup-separation form of
`torusDist_box_cube_le`): `≤ 4 d L M₁ ℓ_{j}`, `j = z.1`. -/
theorem torusDist_box_cube_le_sup (hG : CubeAligned G m₁) (hSS : SupSep G m₁) (hL : 3 ≤ L)
    (hM : 4 * L ^ 2 ≤ L ^ m₁) {z P : ℕ × CTorus d L N₁ m₁ K}
    (hz : z ∈ cubeIdx G) (hP : P ∈ Qset G z) {w : CTorus d L N₁ m₁ K} (hw : w ∈ intBox z)
    {y' : CTorus d L N₁ m₁ K} (hy' : y' ∈ cubeP P) :
    Green.torusDist d ((N₁ * L ^ m₁) * L ^ K) w y' ≤ 4 * d * L * (L : ℝ) ^ (z.1 + m₁) := by
  obtain ⟨-, y, hy, hbox⟩ := mem_Qset.1 hP
  have hlay := Qset_layer_sup hG hSS hM (by omega) hz hP
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast (by omega : 1 ≤ L)
  have hd0 : (0 : ℝ) ≤ d := by positivity
  have hyhat : y ∈ hatBox z := by unfold hatBox; exact mem_boxSet.2 hbox
  have d1 := torusDist_hatBox_le_cover (K := K) (N₁ := N₁) hL hM (box_subset_hatBox z hw)
  have d2 := torusDist_hatBox_le_cover (K := K) (N₁ := N₁) hL hM hyhat
  have hyy : SameCell (L ^ (P.1 + m₁)) y' y := (mem_cubeP.1 hy').trans hy.symm
  have d3 := torusDist_sameCell_le (L := L) (N₁ := N₁) (m₁ := m₁) (K := K)
    (pow_pos (Nat.pos_of_ne_zero (NeZero.ne L)) _) hyy
  have hBP : (L : ℝ) ^ (P.1 + m₁) ≤ L * (L : ℝ) ^ (z.1 + m₁) := by
    rw [← pow_succ']
    exact pow_le_pow_right₀ hL1 (by omega)
  have t1 := Green.torusDist_triangle_gen (d := d) (m := (N₁ * L ^ m₁) * L ^ K) w z.2 y'
  have t2 := Green.torusDist_triangle_gen (d := d) (m := (N₁ * L ^ m₁) * L ^ K) z.2 y y'
  have c1 : Green.torusDist d ((N₁ * L ^ m₁) * L ^ K) z.2 y =
      Green.torusDist d ((N₁ * L ^ m₁) * L ^ K) y z.2 := Green.torusDist_comm_gen _ _
  have c2 : Green.torusDist d ((N₁ * L ^ m₁) * L ^ K) y y' =
      Green.torusDist d ((N₁ * L ^ m₁) * L ^ K) y' y := Green.torusDist_comm_gen _ _
  have e3 : Green.torusDist d ((N₁ * L ^ m₁) * L ^ K) y' y ≤ d * (L : ℝ) ^ (P.1 + m₁) := by
    have : ((L ^ (P.1 + m₁) : ℕ) : ℝ) = (L : ℝ) ^ (P.1 + m₁) := by push_cast; rfl
    rw [← this]; exact d3
  have hB0 : (0 : ℝ) ≤ (L : ℝ) ^ (z.1 + m₁) := by positivity
  have hL3 : (3 : ℝ) ≤ L := by exact_mod_cast hL
  nlinarith [mul_le_mul_of_nonneg_left hBP hd0, mul_nonneg hd0 hB0,
    mul_nonneg (mul_nonneg hd0 hB0) (by linarith : (0 : ℝ) ≤ 4 * (L : ℝ) - 11)]

end Geometry

/-! ### The `X₀` distance with the target bound only -/

section Main

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
variable {G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ}

/-- **The scaled distance from `X₀` to `𝒲` with the target bound only.**  For a sup-separated,
cube-aligned generating set (`L ≥ 3`, `M₁ ≥ 4 L²`, `ϱ ≥ 1`): if the physical `r₀ M₁ ℓ(x)`-collar
of every site `x ∈ X₀ ∩ Ω₁` lies in `X₁` and the target `T = ((r₀ - 4 d L³)/L) M₁` satisfies
`T ≤ ϱ - 1`, then `d(x, w) ≥ T` for every `w ∈ 𝒲`.  The landed `scaled_dist_X0` asks
`r₀ M₁ ≤ ϱ - 1` (the whole collar below the index) and `DGSetting` (`4 d L M₁ ≤ ϱ`). -/
theorem scaled_dist_X0_sup (hG : CubeAligned G m₁) (hSS : SupSep G m₁) (hL : 3 ≤ L)
    (hM : 4 * L ^ 2 ≤ L ^ m₁) (hρ : 1 ≤ ϱ) {r₀ : ℝ} {X₀ X₁ : Finset (CTorus d L N₁ m₁ K)}
    (hN : ∀ x ∈ X₀, x ∈ G.Ω 1 → ∀ y : CTorus d L N₁ m₁ K,
      Green.torusDist d ((N₁ * L ^ m₁) * L ^ K) x y < r₀ * (L : ℝ) ^ m₁ * G.spacing x → y ∈ X₁)
    (hT : (r₀ - 4 * d * (L : ℝ) ^ 3) * (L : ℝ) ^ m₁ / L ≤ ϱ - 1)
    {x : CTorus d L N₁ m₁ K} (hx : x ∈ X₀) (hxΩ : x ∈ G.Ω 1)
    {w : CTorus d L N₁ m₁ K} (hw : w ∈ Wpar G X₁) :
    ENNReal.ofReal ((r₀ - 4 * d * (L : ℝ) ^ 3) * (L : ℝ) ^ m₁ / L) ≤ G.pathDist x w := by
  classical
  by_cases hwΩ : w ∉ G.Ω 1
  · have : G.pathDist x w = ⊤ := by
      refine eq_top_iff.2 (le_iInf₂ fun c hc => ?_)
      exact absurd hc.right_mem hwΩ
    rw [this]; exact le_top
  push Not at hwΩ
  by_contra hcon
  push Not at hcon
  obtain ⟨hn1, hnK, hxl⟩ := G.layerIndex_spec hxΩ
  set n := G.layerIndex x with hn
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast (by omega : 1 ≤ L)
  have hd0 : (0 : ℝ) ≤ d := by positivity
  have hℓ1 : (1 : ℝ) ≤ (L : ℝ) ^ n := one_le_pow₀ hL1
  have hsp : G.spacing x = (L : ℝ) ^ n := rfl
  obtain ⟨z, hz, ⟨P, hPQ, hPpar⟩, hwz⟩ := mem_Wpar.1 hw
  have hPsub : ¬ cubeP P ⊆ X₁ := (Finset.mem_filter.1 hPpar).2
  obtain ⟨y', hy'P, hy'X⟩ := Finset.not_subset.1 hPsub
  obtain ⟨hm1, hmK, hwl⟩ := G.layerIndex_spec hwΩ
  set nw := G.layerIndex w with hnw
  set T : ℝ := (r₀ - 4 * d * (L : ℝ) ^ 3) * (L : ℝ) ^ m₁ / L with hTdef
  have hLpos : (0 : ℝ) < L := by linarith
  have hTpos : 0 < T := by
    by_contra h
    push Not at h
    rw [ENNReal.ofReal_of_nonpos h] at hcon
    exact absurd hcon (not_lt.2 bot_le)
  -- no jump of two layers
  have hnw1 : nw ≤ n + 1 := by
    by_contra hh
    push Not at hh
    have h1 := G.pathDist_separation_le hρ hn1 hmK hxl (G.mem_layer.1 hwl).1
    have h2 : ϱ - 1 ≤ (ϱ - 1) * (((nw - n - 1 : ℕ)) : ℝ) := by
      have : (1 : ℝ) ≤ ((nw - n - 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ nw - n - 1)
      nlinarith
    have h3 : ENNReal.ofReal (ϱ - 1) ≤ G.pathDist x w := h1.trans' (ENNReal.ofReal_le_ofReal h2)
    exact absurd (hcon.trans_le (ENNReal.ofReal_le_ofReal hT)) (not_lt.2 h3)
  have hzn : z.1 ≤ n + 2 := by
    have := layer_ge_of_mem_box_sup hSS (by omega) hz hwz hwΩ
    omega
  -- the physical distances
  have hB := torusDist_box_cube_le_sup hG hSS hL hM hz hPQ hwz hy'P
  have hz1 : (L : ℝ) ^ (z.1 + m₁) ≤ (L : ℝ) ^ n * (L : ℝ) ^ 2 * (L : ℝ) ^ m₁ := by
    rw [← pow_add, ← pow_add]
    exact pow_le_pow_right₀ hL1 (by omega)
  have hxy : r₀ * (L : ℝ) ^ m₁ * G.spacing x ≤
      Green.torusDist d ((N₁ * L ^ m₁) * L ^ K) x y' := by
    by_contra h
    push Not at h
    exact hy'X (hN x hx hxΩ y' h)
  have tri := Green.torusDist_triangle_gen (d := d) (m := (N₁ * L ^ m₁) * L ^ K) x w y'
  set tw := Green.torusDist d ((N₁ * L ^ m₁) * L ^ K) x w with htw
  have hℓ0 : 0 < (L : ℝ) ^ n := by linarith
  have hQ : (r₀ - 4 * d * (L : ℝ) ^ 3) * (L : ℝ) ^ m₁ * (L : ℝ) ^ n ≤ tw := by
    have h1 : 4 * d * L * (L : ℝ) ^ (z.1 + m₁) ≤
        4 * d * L * ((L : ℝ) ^ n * (L : ℝ) ^ 2 * (L : ℝ) ^ m₁) :=
      mul_le_mul_of_nonneg_left hz1 (by positivity)
    rw [hsp] at hxy
    nlinarith
  have hsucc : (L : ℝ) ^ (n + 1) = (L : ℝ) ^ n * L := pow_succ _ _
  have hTL : T * (L : ℝ) ^ (n + 1) = (r₀ - 4 * d * (L : ℝ) ^ 3) * (L : ℝ) ^ m₁ * (L : ℝ) ^ n := by
    rw [hTdef, hsucc]
    field_simp
  -- the truncation only needs the target below the index
  have hR : T * (L : ℝ) ^ (n + 1) ≤ ϱ * (L : ℝ) ^ (n + 1) - 1 := by
    have hc1 : (1 : ℝ) ≤ (L : ℝ) ^ (n + 1) := one_le_pow₀ hL1
    have := mul_le_mul_of_nonneg_right hT (by linarith : (0 : ℝ) ≤ (L : ℝ) ^ (n + 1))
    nlinarith
  have hA := pathDist_ge_torusDist G hρ hn1 hxl w
  have hmin : T * (L : ℝ) ^ (n + 1) ≤ min tw (ϱ * (L : ℝ) ^ (n + 1) - 1) :=
    le_min (by rw [hTL]; exact hQ) hR
  have hdiv : T ≤ min tw (ϱ * (L : ℝ) ^ (n + 1) - 1) / (L : ℝ) ^ (n + 1) := by
    rw [le_div_iff₀ (by positivity)]
    exact hmin
  exact absurd hcon (not_lt.2 ((ENNReal.ofReal_le_ofReal hdiv).trans hA))

/-- The scaled distance from `x ∈ X₀` to `𝒲` with the target bound only. -/
theorem siteSetDist_X0_sup (hG : CubeAligned G m₁) (hSS : SupSep G m₁) (hL : 3 ≤ L)
    (hM : 4 * L ^ 2 ≤ L ^ m₁) (hρ : 1 ≤ ϱ) {r₀ : ℝ} {X₀ X₁ : Finset (CTorus d L N₁ m₁ K)}
    (hN : ∀ x ∈ X₀, x ∈ G.Ω 1 → ∀ y : CTorus d L N₁ m₁ K,
      Green.torusDist d ((N₁ * L ^ m₁) * L ^ K) x y < r₀ * (L : ℝ) ^ m₁ * G.spacing x → y ∈ X₁)
    (hT : (r₀ - 4 * d * (L : ℝ) ^ 3) * (L : ℝ) ^ m₁ / L ≤ ϱ - 1)
    {x : CTorus d L N₁ m₁ K} (hx : x ∈ X₀) (hxΩ : x ∈ G.Ω 1) :
    ENNReal.ofReal ((r₀ - 4 * d * (L : ℝ) ^ 3) * (L : ℝ) ^ m₁ / L) ≤
      siteSetDist G (Wpar G X₁) x := by
  unfold siteSetDist
  exact le_iInf₂ fun w hw => scaled_dist_X0_sup hG hSS hL hM hρ hN hT hx hxΩ hw

omit [NeZero N₁] [NeZero L] in
/-- **The target at the literal separation**: for the collar `r₀ = 4 d L³ + L` the target is
`T = M₁` (P3's `r₁ = 1`), and `M₁ ≤ 5 L M₁ - 1`. -/
theorem target_le_minSep (hL : 1 ≤ L) :
    ((4 * d * (L : ℝ) ^ 3 + L) - 4 * d * (L : ℝ) ^ 3) * (L : ℝ) ^ m₁ / L = (L : ℝ) ^ m₁ ∧
      (L : ℝ) ^ m₁ ≤ minSep L (L ^ m₁) - 1 := by
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hM1 : (1 : ℝ) ≤ (L : ℝ) ^ m₁ := one_le_pow₀ hL1
  refine ⟨by field_simp; ring, ?_⟩
  unfold minSep
  push_cast
  nlinarith

/-- **The `X₀` distance for the literal local generator** (P3 pp. 44, 57, 69): for
`𝔹 = localB j hj X hsep` at the index `ϱ = 5 L M₁`, `L ≥ 3`, `M₁ = L^{m₁} ≥ 4 L²`, and the collar
`r₀ = 4 d L³ + L` (the `(4 d L³ + L) M₁ ℓ(x)`-neighbourhood of each `x ∈ X₀ ∩ Ω₁` lies in `X₁`),
the scaled distance from `x` to `𝒲` is at least `M₁`. -/
theorem localB_siteSetDist_X0 {j : ℕ} (hj : j ≤ K) (Y : Set (CTorus d L N₁ m₁ K))
    (hL : 3 ≤ L) (hM : 4 * L ^ 2 ≤ L ^ m₁) {X₀ X₁ : Finset (CTorus d L N₁ m₁ K)}
    (hN : ∀ x ∈ X₀, x ∈ (SmallField.GsSpec.localB j hj Y (le_refl (minSep L (L ^ m₁)))).Ω 1 →
      ∀ y : CTorus d L N₁ m₁ K, Green.torusDist d ((N₁ * L ^ m₁) * L ^ K) x y <
        (4 * d * (L : ℝ) ^ 3 + L) * (L : ℝ) ^ m₁ *
          (SmallField.GsSpec.localB j hj Y (le_refl (minSep L (L ^ m₁)))).spacing x → y ∈ X₁)
    {x : CTorus d L N₁ m₁ K} (hx : x ∈ X₀)
    (hxΩ : x ∈ (SmallField.GsSpec.localB j hj Y (le_refl (minSep L (L ^ m₁)))).Ω 1) :
    ENNReal.ofReal ((L : ℝ) ^ m₁) ≤
      siteSetDist (SmallField.GsSpec.localB j hj Y (le_refl (minSep L (L ^ m₁))))
        (Wpar (SmallField.GsSpec.localB j hj Y (le_refl (minSep L (L ^ m₁)))) X₁) x := by
  have hm₁ : 2 ≤ m₁ := by
    by_contra h
    push Not at h
    have hL2 : L ^ m₁ ≤ L ^ 1 := Nat.pow_le_pow_right (by omega) (by omega)
    nlinarith
  obtain ⟨hT1, hT2⟩ := target_le_minSep (d := d) (m₁ := m₁) (by omega : 1 ≤ L)
  have hρ : (1 : ℝ) ≤ minSep L (L ^ m₁) := by
    have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast (by omega : 1 ≤ L)
    have : (1 : ℝ) ≤ (L : ℝ) ^ m₁ := one_le_pow₀ hL1
    linarith
  have h := siteSetDist_X0_sup (localB_cubeAligned hj Y le_rfl hm₁) (localB_supSep hj Y le_rfl)
    hL hM hρ hN (by rw [hT1]; exact hT2) hx hxΩ
  rwa [hT1] at h

/-- A centre of `W_C(X₁)` for the cover `C = coverOf G` is a centre of `𝒲 = Wpar G X₁`. -/
theorem mem_Wpar_of_mem_Wcover {X₁ : Finset (CTorus d L N₁ m₁ K)} {w : CTorus d L N₁ m₁ K}
    (hw : w ∈ Wcover (coverOf G) X₁) : w ∈ Wpar G X₁ := by
  obtain ⟨z, hz, ⟨P, hP, hPs⟩, hwz⟩ := mem_Wcover.1 hw
  exact mem_Wpar.2 ⟨z, hz, ⟨P, hP, Finset.mem_filter.2 ⟨((coverOf G).mem_Qset.1 hP).1, hPs⟩⟩, hwz⟩

/-- `d(x, 𝒲) ≤ d(x, W_C(X₁))` for `C = coverOf G`. -/
theorem siteSetDist_Wpar_le_Wcover (X₁ : Finset (CTorus d L N₁ m₁ K)) (x : CTorus d L N₁ m₁ K) :
    siteSetDist G (Wpar G X₁) x ≤ siteSetDist G (Wcover (coverOf G) X₁) x := by
  unfold siteSetDist
  exact le_iInf₂ fun w hw => iInf₂_le w (mem_Wpar_of_mem_Wcover hw)

/-- **Theorem I-4a (d) on `X₀` for a sup-separated generating set** (cover form `Dec2.i4a_close`
on the pair `(coverOf G, G)`).  Under the hypotheses of `Dec2.i4a_close`, with the parameters equal
to `1` off the parameter cubes, the physical `r₀ M₁ ℓ(x)`-collar of `X₀ ∩ Ω₁` in `X₁` and the target
`T = ((r₀ - 4 d L³)/L) M₁ ≤ ϱ - 1`, the solutions at `s` and at `s ≡ 1` differ on `X₀ ∩ Ω₁` by at
most `closeConst · e^{-γ_w T}` (twice that for the fields).  No `ℓ¹` cover separation and no
`r₀ M₁ ≤ ϱ - 1` is assumed. -/
theorem i4a_close_X0_sup {Kc Cx c BG : ℝ} {a : ℕ → ℝ} {ν : ℝ} {N : ℕ}
    (hF : Dec2.FamSpec d L Kc Cx c BG) (hD : Dec2.Dg2Spec d L Kc Cx c BG)
    (hCl : Dec2.CloseSpec d L Kc Cx c BG) (h1 : Dec2.OneSpec d L Kc Cx c)
    (S : Dec2.CoverBase (coverOf G) G a ν Kc Cx) (hG : CubeAligned G m₁) (hSS : SupSep G m₁)
    (hMM : 4 * L ^ 2 ≤ L ^ m₁) (hρ : 1 ≤ ϱ) {κ : ℝ} (hκ : 0 ≤ κ)
    (hM : c * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {s : Dec2.DecParams (coverOf G)}
    (hs : ∀ P, ‖s P‖ ≤ Real.exp κ) {X₀ X₁ : Finset (CTorus d L N₁ m₁ K)} {r₀ : ℝ}
    (hs1 : ∀ (P : ℕ × CTorus d L N₁ m₁ K) (hP : P ∈ (coverOf G).cubeIdx),
      P ∉ (coverOf G).parCubes X₁ → s ⟨P, hP⟩ = 1)
    (hN : ∀ x ∈ X₀, x ∈ G.Ω 1 → ∀ y : CTorus d L N₁ m₁ K,
      Green.torusDist d ((N₁ * L ^ m₁) * L ^ K) x y < r₀ * (L : ℝ) ^ m₁ * G.spacing x → y ∈ X₁)
    (hT : (r₀ - 4 * d * (L : ℝ) ^ 3) * (L : ℝ) ^ m₁ / L ≤ ϱ - 1)
    (hr₀ : 4 * d * (L : ℝ) ^ 3 ≤ r₀)
    {ιU : Bool} {α₀ : G.Ω 1 → ℂ} {φ₀ δΨ : CTorus d L N₁ m₁ K → Fin N → ℂ}
    {f₁ : G.Ω 1 × Fin N → ℂ} {δ₀ δ₁ : ℝ} (Hh : DecHyp G a ν ιU α₀ φ₀ δΨ f₁ δ₀ δ₁)
    (hδ₀ : δ₀ ≤ deltaClose d L N BG κ) (hδ₁ : δ₁ ≤ deltaClose d L N BG κ)
    {δα δα' : G.Ω 1 → ℂ}
    (hfix : Dec2.DecFixed (coverOf G) G a ν s ιU α₀ φ₀ (pertSource G a δΨ f₁) δα)
    (hsm : Small G δα (c6' d L N (famConst d L BG κ) (gamma1 d / 8)))
    (hfix' : Dec2.DecFixed (coverOf G) G a ν (fun _ => 1) ιU α₀ φ₀ (pertSource G a δΨ f₁) δα')
    (hsm' : Small G δα' (c6' d L N (famConst d L BG κ) (gamma1 d / 8))) :
    (∀ x : G.Ω 1, (x : CTorus d L N₁ m₁ K) ∈ X₀ →
      G.spacing (x : CTorus d L N₁ m₁ K) ^ 2 * ‖δα x - δα' x‖ ≤ closeConst d L N BG κ δ₁ *
        Real.exp (-(gammaW d * ((r₀ - 4 * d * (L : ℝ) ^ 3) * (L : ℝ) ^ m₁ / L)))) ∧
    (∀ y ∈ X₀, y ∈ G.Ω 1 → ∀ i : Fin N,
      ‖svec G (dphi G (Dec2.decG (coverOf G) G a ν s) α₀ φ₀ (pertSource G a δΨ f₁) δα -
        dphi G (Dec2.decG (coverOf G) G a ν (fun _ => 1)) α₀ φ₀ (pertSource G a δΨ f₁) δα') y i‖ ≤
        2 * closeConst d L N BG κ δ₁ *
          Real.exp (-(gammaW d * ((r₀ - 4 * d * (L : ℝ) ^ 3) * (L : ℝ) ^ m₁ / L)))) ∧
    (∀ x ∈ X₀, x ∈ G.Ω 1 → ∀ (μ : Fin d) (i : Fin N), G.spacing x *
      ‖svec G (dphi G (Dec2.decG (coverOf G) G a ν s) α₀ φ₀ (pertSource G a δΨ f₁) δα -
        dphi G (Dec2.decG (coverOf G) G a ν (fun _ => 1)) α₀ φ₀ (pertSource G a δΨ f₁) δα')
          (x + Pi.single μ 1) i -
        svec G (dphi G (Dec2.decG (coverOf G) G a ν s) α₀ φ₀ (pertSource G a δΨ f₁) δα -
        dphi G (Dec2.decG (coverOf G) G a ν (fun _ => 1)) α₀ φ₀ (pertSource G a δΨ f₁) δα') x i‖ ≤
        2 * closeConst d L N BG κ δ₁ *
          Real.exp (-(gammaW d * ((r₀ - 4 * d * (L : ℝ) ^ 3) * (L : ℝ) ^ m₁ / L)))) ∧
    (∀ x ∈ X₀, x ∈ G.Ω 1 → ∀ i : Fin N, G.spacing x ^ 2 * ‖∑ μ : Fin d,
      (2 * svec G (dphi G (Dec2.decG (coverOf G) G a ν s) α₀ φ₀ (pertSource G a δΨ f₁) δα -
        dphi G (Dec2.decG (coverOf G) G a ν (fun _ => 1)) α₀ φ₀ (pertSource G a δΨ f₁) δα') x i -
      svec G (dphi G (Dec2.decG (coverOf G) G a ν s) α₀ φ₀ (pertSource G a δΨ f₁) δα -
        dphi G (Dec2.decG (coverOf G) G a ν (fun _ => 1)) α₀ φ₀ (pertSource G a δΨ f₁) δα')
          (x + Pi.single μ 1) i -
      svec G (dphi G (Dec2.decG (coverOf G) G a ν s) α₀ φ₀ (pertSource G a δΨ f₁) δα -
        dphi G (Dec2.decG (coverOf G) G a ν (fun _ => 1)) α₀ φ₀ (pertSource G a δΨ f₁) δα')
          (x - Pi.single μ 1) i)‖ ≤
        2 * closeConst d L N BG κ δ₁ *
          Real.exp (-(gammaW d * ((r₀ - 4 * d * (L : ℝ) ^ 3) * (L : ℝ) ^ m₁ / L)))) := by
  have hd0 : 0 < d := by have := S.hd; omega
  have hL : 3 ≤ L := S.hL
  have hBG : 0 ≤ BG := hF.2.1
  have hcc := closeConst_nonneg (d := d) (L := L) (κ := κ) (N := N) hBG Hh.δ₁_nn hd0
  have hγ0 : 0 ≤ gammaW d := gammaW_nonneg hd0
  have hL1 : (0 : ℝ) < L := by exact_mod_cast (by omega : 0 < L)
  have hT0 : 0 ≤ (r₀ - 4 * d * (L : ℝ) ^ 3) * (L : ℝ) ^ m₁ / L := by
    have : 0 ≤ r₀ - 4 * d * (L : ℝ) ^ 3 := by linarith
    positivity
  have hclose := Dec2.i4a_close hF hD hCl h1 S hκ hM hs (W := Wcover (coverOf G) X₁)
    (hW_of_par_cover hs1) Hh hδ₀ hδ₁ hfix hsm hfix' hsm'
  have hdec : ∀ x ∈ X₀, x ∈ G.Ω 1 → decay (gammaW d) (siteSetDist G (Wcover (coverOf G) X₁) x) ≤
      Real.exp (-(gammaW d * ((r₀ - 4 * d * (L : ℝ) ^ 3) * (L : ℝ) ^ m₁ / L))) := by
    intro x hx hxΩ
    have h := decay_anti_dist hγ0 ((siteSetDist_X0_sup hG hSS hL hMM hρ hN hT hx hxΩ).trans
      (siteSetDist_Wpar_le_Wcover X₁ x))
    rw [decay_of_ne_top ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hT0] at h
    exact h
  obtain ⟨c1, c2, c3, c4⟩ := hclose
  refine ⟨fun x hx => ?_, fun y hy hyΩ i => ?_, fun x hx hxΩ μ i => ?_, fun x hx hxΩ i => ?_⟩
  · exact (c1 x).trans (mul_le_mul_of_nonneg_left (hdec x hx x.2) hcc)
  · exact (c2 y i).trans (mul_le_mul_of_nonneg_left (hdec y hy hyΩ) (by positivity))
  · exact (c3 x hxΩ μ i).trans (mul_le_mul_of_nonneg_left (hdec x hx hxΩ) (by positivity))
  · exact (c4 x hxΩ i).trans (mul_le_mul_of_nonneg_left (hdec x hx hxΩ) (by positivity))

end Main

end Balaban.Localization
