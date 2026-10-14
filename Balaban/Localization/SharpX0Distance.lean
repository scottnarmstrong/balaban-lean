/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.P6PairSep
public import Balaban.Localization.PairedLocalX0
public import Balaban.SmallField.LocalGeneratorSource
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
* `layer_ge_of_mem_box_sup`, `torusDist_box_cube_le_sup`: the two geometric inputs of
  `scaled_dist_X0` under `SupSep` instead of `DGSetting`;
* `scaled_dist_X0_sup`, `siteSetDist_X0_sup`: **the `X₀` distance with the target bound
  `T ≤ ϱ - 1` only**, for a sup-separated, cube-aligned generating set;
* `target_le_minSep`, `localB_siteSetDist_X0`: at `ϱ = 5 L M₁` and `r₀ = 4 d L³ + L` the target is
  `T = M₁ ≤ ϱ - 1`, so `siteSetDist ≥ M₁` for the literal local generator.
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

end Main

end Balaban.Localization
