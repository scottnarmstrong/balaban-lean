/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.SmallField.Xi
public import Balaban.LargeField.Characteristic.Reg
public import Balaban.LargeField.Background.CubeUnitBg
public import Balaban.Background.MinimizerAlg
public import Balaban.Flow.StopIndex
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The final cutoff: averaging the direction test (`FinalCutoffAlgebra`)

At the stopping index the block spin `ψ_k` is confined near the constant unit vector `h`
(P4 (6.2)).  This file proves the elementary averaging argument behind it.

* `blockAvg_sub_const_lt`, `blockAvg_sub_const_le`: if `|φ(z) - c| < r` (resp. `≤ r`) at every site
  `z` of the block of `x`, then `|(Qφ)(x) - c| < r` (resp. `≤ r`); the block average has
  nonnegative weights summing to one.  For `x ∈ Ω₁` the block `G.blk (G.layerIndex x) x` lies
  inside `Ω₁` automatically (`blk_subset_Ω`), and all its sites have the layer, hence the spacing, of `x`
  (`mem_blk_iff`), so no extra "full block" hypothesis is needed for the landed `blockAvg`.
* `xiBounds_cutoff`: from `XiBounds.close` and `XiBounds.mass`,
  `|Ψ(x) - h₀| < σ²ε + σε / (√ν ℓ(x))`.
* `xiBounds_cutoff_top`, `xiBounds_cutoff_top_le_five`, `xiBounds_cutoff_top_le_one`: the
  corollaries for `σ = 1`, a site of the top layer, dimensionless mass `ν_k = ν L^{2k}`:
  `(1 + √(8/7) L) ε < (5 L + 3) ε` if `ν_k > (7/8) L⁻²`, and `2 ε / √ν_k` if `ν_k ≤ 1`.
* `regIneq_cutoff`, `regIneq_cutoff_five`, `regIneq_cutoff_le_one`: the same from the cube tests
  `BlockClose` and `FieldClose` of `RegIneq` (used by `chiK`); the geometric premise is that the
  block of `x` lies inside the field-test set `S`, and that the external field `D.h` is the constant
  `c` on that block.
* `p4_cutoff_xi`, `p4_cutoff_reg`: P4 (6.2) at the stopping index `kStop`, for a mass
  `ν_k = n (kStop h)` (`n_kStop_lt_one`, `kStop_spec`).
* `regIneq_cutoff_const`: an instance (constant field) in which all hypotheses of
  `regIneq_cutoff` hold; the conclusion is the trivial `0 < bound`.  A non-constant instance, and an
  instance of `XiBounds` itself, are not provided here.

`FINAL-CUTOFF-BRIDGE` (that the tests hold for the physical final density, covering of every
integrated block by tested regions, `k_f > k₀`), the final Hessian bridge and the last expansion are
NOT proved here.
-/

@[expose] public section

namespace Balaban.FinalCutoff

open Balaban Balaban.Multiscale Balaban.Background Balaban.LargeField Balaban.SmallField

section Avg

variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ} {G : GeneratingSet d L N₀ k ϱ}

private theorem blockAvg_vec (φ : G.Ω 1 × Fin N → ℂ) (c : Fin N → ℂ) {x : Torus d (N₀ * L ^ k)}
    (hx : x ∈ G.Ω 1) :
    (WithLp.toLp 2 (fun i => blockAvg G φ x i - c i) : EuclideanSpace ℂ (Fin N)) =
      ((((((L : ℝ) ^ G.layerIndex x) ^ d)⁻¹ : ℝ) : ℂ)) •
        ∑ y ∈ (G.blk (G.layerIndex x) x).attach, (WithLp.toLp 2 (fun i =>
          φ (⟨y, blk_subset_Ω G (G.layerIndex_spec hx).1 (G.layerIndex_spec hx).2.1
            (G.layerIndex_spec hx).2.2 y.2⟩, i) - c i) : EuclideanSpace ℂ (Fin N)) := by
  classical
  obtain ⟨hn1, hnk, hxl⟩ := G.layerIndex_spec hx
  have hsub := blk_subset_Ω G hn1 hnk hxl
  have hcard : ((G.blk (G.layerIndex x) x).card : ℝ) = ((L : ℝ) ^ G.layerIndex x) ^ d := by
    rw [card_blk G _ hnk x]; push_cast; ring
  have hpos : (0 : ℝ) < ((L : ℝ) ^ G.layerIndex x) ^ d := by
    have : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
    positivity
  ext i
  simp only [PiLp.smul_apply, WithLp.ofLp_sum, Finset.sum_apply, smul_eq_mul]
  have e1 : ∑ y ∈ (G.blk (G.layerIndex x) x).attach,
      (φ (⟨y, hsub y.2⟩, i) - c i) =
      ∑ y ∈ G.blk (G.layerIndex x) x, svec G φ y i -
        ((G.blk (G.layerIndex x) x).card : ℂ) * c i := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_attach, nsmul_eq_mul]
    congr 1
    rw [← Finset.sum_attach (G.blk (G.layerIndex x) x) (fun y => svec G φ y i)]
    exact Finset.sum_congr rfl fun y _ => (svec_of_mem G φ ⟨y, hsub y.2⟩ i).symm
  rw [e1]
  unfold blockAvg
  have hcq : ((((((L : ℝ) ^ G.layerIndex x) ^ d)⁻¹ : ℝ)) : ℂ) *
      ((((L : ℝ) ^ G.layerIndex x) ^ d : ℝ) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, inv_mul_cancel₀ hpos.ne', Complex.ofReal_one]
  have hcc : ((G.blk (G.layerIndex x) x).card : ℂ) = ((((L : ℝ) ^ G.layerIndex x) ^ d : ℝ) : ℂ) := by
    exact_mod_cast hcard
  rw [hcc]
  linear_combination (c i) * hcq

/-- **Averaging (strict).**  If `|φ(z) - c| < r` at every site `z` of the block of `x ∈ Ω₁`, then
`|(Qφ)(x) - c| < r`.  The block average is a mean over the (nonempty) block. -/
theorem blockAvg_sub_const_lt (φ : G.Ω 1 × Fin N → ℂ) (c : Fin N → ℂ) {x : Torus d (N₀ * L ^ k)}
    (hx : x ∈ G.Ω 1) {r : ℝ}
    (hr : ∀ (y : Torus d (N₀ * L ^ k)) (hy : y ∈ G.Ω 1), y ∈ G.blk (G.layerIndex x) x →
      vn (fun i => φ (⟨y, hy⟩, i) - c i) < r) :
    vn (fun i => blockAvg G φ x i - c i) < r := by
  classical
  obtain ⟨hn1, hnk, hxl⟩ := G.layerIndex_spec hx
  have hsub := blk_subset_Ω G hn1 hnk hxl
  have hcard : ((G.blk (G.layerIndex x) x).card : ℝ) = ((L : ℝ) ^ G.layerIndex x) ^ d := by
    rw [card_blk G _ hnk x]; push_cast; ring
  have hpos : (0 : ℝ) < ((L : ℝ) ^ G.layerIndex x) ^ d := by
    have : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
    positivity
  have hne : (G.blk (G.layerIndex x) x).attach.Nonempty := by
    rw [Finset.attach_nonempty_iff, ← Finset.card_pos]
    have : (0 : ℝ) < (G.blk (G.layerIndex x) x).card := by rw [hcard]; exact hpos
    exact_mod_cast this
  have h1 := blockAvg_vec φ c hx
  calc vn (fun i => blockAvg G φ x i - c i)
      = ‖(WithLp.toLp 2 (fun i => blockAvg G φ x i - c i) : EuclideanSpace ℂ (Fin N))‖ := rfl
    _ = (((L : ℝ) ^ G.layerIndex x) ^ d)⁻¹ *
        ‖∑ y ∈ (G.blk (G.layerIndex x) x).attach, (WithLp.toLp 2 (fun i =>
          φ (⟨y, hsub y.2⟩, i) - c i) : EuclideanSpace ℂ (Fin N))‖ := by
        rw [h1, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    _ < (((L : ℝ) ^ G.layerIndex x) ^ d)⁻¹ * ∑ y ∈ (G.blk (G.layerIndex x) x).attach, r := by
        refine mul_lt_mul_of_pos_left (lt_of_le_of_lt (norm_sum_le _ _)
          (Finset.sum_lt_sum_of_nonempty hne fun y _ => hr y _ y.2)) (by positivity)
    _ = r := by
        rw [Finset.sum_const, Finset.card_attach, nsmul_eq_mul, hcard]
        field_simp

/-- **Averaging (non-strict).**  Same with `≤ r`. -/
theorem blockAvg_sub_const_le (φ : G.Ω 1 × Fin N → ℂ) (c : Fin N → ℂ) {x : Torus d (N₀ * L ^ k)}
    (hx : x ∈ G.Ω 1) {r : ℝ}
    (hr : ∀ (y : Torus d (N₀ * L ^ k)) (hy : y ∈ G.Ω 1), y ∈ G.blk (G.layerIndex x) x →
      vn (fun i => φ (⟨y, hy⟩, i) - c i) ≤ r) :
    vn (fun i => blockAvg G φ x i - c i) ≤ r := by
  classical
  obtain ⟨hn1, hnk, hxl⟩ := G.layerIndex_spec hx
  have hsub := blk_subset_Ω G hn1 hnk hxl
  have hcard : ((G.blk (G.layerIndex x) x).card : ℝ) = ((L : ℝ) ^ G.layerIndex x) ^ d := by
    rw [card_blk G _ hnk x]; push_cast; ring
  have hpos : (0 : ℝ) < ((L : ℝ) ^ G.layerIndex x) ^ d := by
    have : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
    positivity
  have h1 := blockAvg_vec φ c hx
  calc vn (fun i => blockAvg G φ x i - c i)
      = ‖(WithLp.toLp 2 (fun i => blockAvg G φ x i - c i) : EuclideanSpace ℂ (Fin N))‖ := rfl
    _ = (((L : ℝ) ^ G.layerIndex x) ^ d)⁻¹ *
        ‖∑ y ∈ (G.blk (G.layerIndex x) x).attach, (WithLp.toLp 2 (fun i =>
          φ (⟨y, hsub y.2⟩, i) - c i) : EuclideanSpace ℂ (Fin N))‖ := by
        rw [h1, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    _ ≤ (((L : ℝ) ^ G.layerIndex x) ^ d)⁻¹ * ∑ y ∈ (G.blk (G.layerIndex x) x).attach, r := by
        refine mul_le_mul_of_nonneg_left (le_trans (norm_sum_le _ _)
          (Finset.sum_le_sum fun y _ => hr y _ y.2)) (by positivity)
    _ = r := by
        rw [Finset.sum_const, Finset.card_attach, nsmul_eq_mul, hcard]
        field_simp

/-- Triangle step: `|Ψ(x) - c| ≤ |Ψ(x) - Qφ(x)| + |Qφ(x) - c|`, in the strict form used below. -/
theorem vn_lt_of_close_avg (Ψx A c : Fin N → ℂ) {a b : ℝ} (h1 : vn (fun i => Ψx i - A i) < a)
    (h2 : vn (fun i => A i - c i) < b) : vn (fun i => Ψx i - c i) < a + b := by
  have := vn_triangle Ψx A c
  have e : (fun i => Ψx i - c i) = Ψx - c := rfl
  have e1 : (fun i => Ψx i - A i) = Ψx - A := rfl
  have e2 : (fun i => A i - c i) = A - c := rfl
  rw [e1] at h1; rw [e2] at h2; rw [e]
  linarith

end Avg

section Numeric

/-- `1 / √ν < √(8/7) L` when `ν > (7/8) L⁻²`. -/
theorem inv_sqrt_lt {L ν : ℝ} (hL : 0 < L) (hν : 7 / 8 * (L ^ 2)⁻¹ < ν) :
    1 / Real.sqrt ν < Real.sqrt (8 / 7) * L := by
  have hν0 : 0 < ν := lt_trans (by positivity) hν
  have hs : 0 < Real.sqrt ν := Real.sqrt_pos.2 hν0
  rw [div_lt_iff₀ hs]
  have hsq : 1 < (Real.sqrt (8 / 7) * L) ^ 2 * ν := by
    rw [mul_pow, Real.sq_sqrt (by norm_num)]
    have : 7 / 8 < L ^ 2 * ν := by
      have := mul_lt_mul_of_pos_left hν (show 0 < L ^ 2 by positivity)
      rwa [← mul_assoc, mul_comm (L ^ 2), mul_assoc, mul_inv_cancel₀ (by positivity), mul_one] at this
    nlinarith
  have hpos : 0 < Real.sqrt (8 / 7) * L * Real.sqrt ν := by positivity
  have : 1 < (Real.sqrt (8 / 7) * L * Real.sqrt ν) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hν0.le]; exact hsq
  nlinarith

/-- **P4 (6.2) numerics:** `ε + ε/√ν < (1 + √(8/7) L) ε < (5L+3) ε` for `ε > 0`,
`ν > (7/8) L⁻²`, `L ≥ 1`. -/
theorem cutoff_const_lt {L ν ε : ℝ} (hL : 1 ≤ L) (hε : 0 < ε) (hν : 7 / 8 * (L ^ 2)⁻¹ < ν) :
    ε + ε / Real.sqrt ν < (1 + Real.sqrt (8 / 7) * L) * ε ∧
      (1 + Real.sqrt (8 / 7) * L) * ε < (5 * L + 3) * ε := by
  have hL0 : 0 < L := by linarith
  have h1 := inv_sqrt_lt hL0 hν
  have h4 : Real.sqrt (8 / 7) ≤ 4 := by
    rw [Real.sqrt_le_left (by norm_num)]; norm_num
  constructor
  · have : ε / Real.sqrt ν < Real.sqrt (8 / 7) * L * ε := by
      rw [div_eq_mul_one_div, mul_comm]; exact mul_lt_mul_of_pos_right h1 hε
    nlinarith
  · have : Real.sqrt (8 / 7) * L ≤ 4 * L := by nlinarith
    nlinarith

/-- For `0 < ν ≤ 1`: `ε + ε/√ν ≤ 2 ε / √ν`. -/
theorem cutoff_const_le_one {ν ε : ℝ} (hε : 0 ≤ ε) (hν : 0 < ν) (hν1 : ν ≤ 1) :
    ε + ε / Real.sqrt ν ≤ 2 * ε / Real.sqrt ν := by
  have hs : 0 < Real.sqrt ν := Real.sqrt_pos.2 hν
  have hs1 : Real.sqrt ν ≤ 1 := Real.sqrt_le_one.2 hν1
  rw [le_div_iff₀ hs]
  have : ε / Real.sqrt ν * Real.sqrt ν = ε := div_mul_cancel₀ _ hs.ne'
  rw [add_mul, this]
  nlinarith

end Numeric

section Xi

variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ} {G : GeneratingSet d L N₀ k ϱ}

/-- **Cutoff from `XiBounds`.**  For `x ∈ Ω₁`, `ν > 0`: the closeness test at `x` and the direction
test at the sites of the block of `x` (all of spacing `ℓ(x)`) give
`|Ψ(x) - h₀| < σ² ε + σ ε / (√ν ℓ(x))`. -/
theorem xiBounds_cutoff {ν : ℝ} {n : ℕ} {σ ε : ℝ} {D : BgData G N} {h₀ : Fin N → ℝ}
    {φ : G.Ω 1 × Fin N → ℂ} {α : G.Ω 1 → ℂ} (hb : XiBounds G ν n σ ε D h₀ φ α) (hν : 0 < ν)
    {x : Torus d (N₀ * L ^ k)} (hx : x ∈ G.Ω 1) :
    vn (fun i => D.Ψ x i - (h₀ i : ℂ)) <
      σ ^ 2 * ε + σ * ε / (Real.sqrt ν * G.spacing x) := by
  have hLpos : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hsp : 0 < G.spacing x := by unfold GeneratingSet.spacing; positivity
  have hs : 0 < Real.sqrt ν * G.spacing x := mul_pos (Real.sqrt_pos.2 hν) hsp
  have havg := blockAvg_sub_const_lt (G := G) φ (fun i => (h₀ i : ℂ)) hx
    (r := σ * ε / (Real.sqrt ν * G.spacing x)) (by
      intro y hy hyb
      have hlay := ((mem_blk_iff (G := G) hx).1 hyb).2.1
      have hmass := hb.mass ⟨y, hy⟩
      have hspy : G.spacing y = G.spacing x := by unfold GeneratingSet.spacing; rw [hlay]
      simp only [hspy] at hmass
      rw [lt_div_iff₀ hs]
      linarith [mul_comm (vn fun i => φ (⟨y, hy⟩, i) - (h₀ i : ℂ)) (Real.sqrt ν * G.spacing x),
        show Real.sqrt ν * G.spacing x * (vn fun i => φ (⟨y, hy⟩, i) - (h₀ i : ℂ)) =
          Real.sqrt ν * G.spacing x * (vn fun i => φ (⟨y, hy⟩, i) - (h₀ i : ℂ)) from rfl])
  exact vn_lt_of_close_avg _ _ _ (hb.close x hx) havg

/-- **P4 (6.2), `XiBounds` form.**  For `σ = 1`, a site `x` of the top layer `k`, and the
dimensionless mass `ν_k = ν L^{2k}` with `(7/8) L⁻² < ν_k`:
`|Ψ(x) - h₀| < (1 + √(8/7) L) ε < (5 L + 3) ε`. -/
theorem xiBounds_cutoff_top {ν : ℝ} {n : ℕ} {ε : ℝ} {D : BgData G N} {h₀ : Fin N → ℝ}
    {φ : G.Ω 1 × Fin N → ℂ} {α : G.Ω 1 → ℂ} (hb : XiBounds G ν n 1 ε D h₀ φ α)
    (hk : 1 ≤ k) {x : Torus d (N₀ * L ^ k)} (hx : x ∈ G.layer k)
    (hν : 7 / 8 * ((L : ℝ) ^ 2)⁻¹ < ν * ((L : ℝ) ^ k) ^ 2) (hL : 1 ≤ L) :
    vn (fun i => D.Ψ x i - (h₀ i : ℂ)) < (1 + Real.sqrt (8 / 7) * L) * ε ∧
      vn (fun i => D.Ψ x i - (h₀ i : ℂ)) < (5 * L + 3) * ε := by
  have hLr : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hLk : (0 : ℝ) < (L : ℝ) ^ k := by positivity
  have hν0 : 0 < ν := by
    have h0 : 0 < ν * ((L : ℝ) ^ k) ^ 2 := lt_trans (by positivity) hν
    by_contra hneg
    nlinarith [sq_nonneg ((L : ℝ) ^ k)]
  have hxΩ : x ∈ G.Ω 1 := G.layer_subset hk le_rfl hx
  have h := xiBounds_cutoff hb hν0 hxΩ
  have hsp : G.spacing x = (L : ℝ) ^ k := G.spacing_eq hk le_rfl hx
  have hε : 0 < ε := by
    have := hb.close x hxΩ
    have := vn_nonneg (fun i => D.Ψ x i - blockAvg G φ x i)
    nlinarith
  have hsq : Real.sqrt ν * (L : ℝ) ^ k = Real.sqrt (ν * ((L : ℝ) ^ k) ^ 2) := by
    rw [Real.sqrt_mul hν0.le, Real.sqrt_sq hLk.le]
  rw [hsp, hsq] at h
  have hn := cutoff_const_lt hLr hε hν
  simp only [one_pow, one_mul] at h
  exact ⟨by linarith [hn.1], by linarith [hn.1, hn.2]⟩

/-- **The `ν_k ≤ 1` form** (late scales): `|Ψ(x) - h₀| < 2 ε / √ν_k`. -/
theorem xiBounds_cutoff_top_le_one {ν : ℝ} {n : ℕ} {ε : ℝ} {D : BgData G N} {h₀ : Fin N → ℝ}
    {φ : G.Ω 1 × Fin N → ℂ} {α : G.Ω 1 → ℂ} (hb : XiBounds G ν n 1 ε D h₀ φ α)
    (hk : 1 ≤ k) {x : Torus d (N₀ * L ^ k)} (hx : x ∈ G.layer k)
    (hν : 0 < ν) (hν1 : ν * ((L : ℝ) ^ k) ^ 2 ≤ 1) :
    vn (fun i => D.Ψ x i - (h₀ i : ℂ)) < 2 * ε / Real.sqrt (ν * ((L : ℝ) ^ k) ^ 2) := by
  have hLpos : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hLk : (0 : ℝ) < (L : ℝ) ^ k := by positivity
  have hxΩ : x ∈ G.Ω 1 := G.layer_subset hk le_rfl hx
  have h := xiBounds_cutoff hb hν hxΩ
  have hsp : G.spacing x = (L : ℝ) ^ k := G.spacing_eq hk le_rfl hx
  have hε : 0 ≤ ε := by
    have := hb.close x hxΩ
    have := vn_nonneg (fun i => D.Ψ x i - blockAvg G φ x i)
    nlinarith
  have hsq : Real.sqrt ν * (L : ℝ) ^ k = Real.sqrt (ν * ((L : ℝ) ^ k) ^ 2) := by
    rw [Real.sqrt_mul hν.le, Real.sqrt_sq hLk.le]
  rw [hsp, hsq] at h
  simp only [one_pow, one_mul] at h
  exact lt_of_lt_of_le h (cutoff_const_le_one hε (by positivity) hν1)

end Xi

section Reg

variable {d L N₀ q N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ} {G : GeneratingSet d L N₀ q ϱ}

/-- **Cutoff from the cube tests.**  Let `BlockClose` hold on `T` with tolerance `δc`, `FieldClose`
hold on `S` with tolerance `δf` and mass `ν > 0`, `x ∈ T ∩ Ω₁`, the block of `x` lie in `S`
(the "field-average" hypothesis), and the external field `D.h` equal the constant `c` on that block.
Then `|Ψ(x) - c| < δc + δf / √ν`. -/
theorem regIneq_cutoff {D : BgData G N} {φ : G.Ω 1 × Fin N → ℂ} {T S : Finset (Torus d (N₀ * L ^ q))}
    {δc δf ν : ℝ} (hT : BlockClose G D φ T δc) (hS : FieldClose G D φ ν S δf) (hν : 0 < ν)
    {x : Torus d (N₀ * L ^ q)} (hx : x ∈ G.Ω 1) (hxT : x ∈ T)
    (hblock : ∀ y ∈ G.blk (G.layerIndex x) x, y ∈ S) {c : Fin N → ℂ}
    (hc : ∀ y ∈ G.blk (G.layerIndex x) x, ∀ i, D.h y i = c i) :
    vn (fun i => D.Ψ x i - c i) < δc + δf / Real.sqrt ν := by
  have havg := blockAvg_sub_const_lt (G := G) φ c hx (r := δf / Real.sqrt ν) (by
    intro y hy hyb
    have := (hS hν ⟨y, hy⟩ (hblock y hyb)).1
    have e : (fun i => φ (⟨y, hy⟩, i) - c i) = fun i => φ (⟨y, hy⟩, i) - D.h y i := by
      funext i; rw [hc y hyb i]
    rw [e]; exact this)
  exact vn_lt_of_close_avg _ _ _ (hT x hxT) havg

/-- **P4 (6.2), cube-test form.**  With equal tolerances `δ` and `(7/8) L⁻² < ν`, `L ≥ 1`:
`|Ψ(x) - c| < (1 + √(8/7) L) δ < (5L+3) δ`. -/
theorem regIneq_cutoff_five {D : BgData G N} {φ : G.Ω 1 × Fin N → ℂ}
    {T S : Finset (Torus d (N₀ * L ^ q))} {δ ν : ℝ} (hT : BlockClose G D φ T δ)
    (hS : FieldClose G D φ ν S δ) (hL : 1 ≤ L) (hν : 7 / 8 * ((L : ℝ) ^ 2)⁻¹ < ν)
    {x : Torus d (N₀ * L ^ q)} (hx : x ∈ G.Ω 1) (hxT : x ∈ T)
    (hblock : ∀ y ∈ G.blk (G.layerIndex x) x, y ∈ S) {c : Fin N → ℂ}
    (hc : ∀ y ∈ G.blk (G.layerIndex x) x, ∀ i, D.h y i = c i) :
    vn (fun i => D.Ψ x i - c i) < (1 + Real.sqrt (8 / 7) * L) * δ ∧
      vn (fun i => D.Ψ x i - c i) < (5 * L + 3) * δ := by
  have hLr : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hν0 : 0 < ν := lt_trans (by positivity) hν
  have h := regIneq_cutoff hT hS hν0 hx hxT hblock hc
  have hδ : 0 < δ := lt_of_le_of_lt (vn_nonneg _) (hT x hxT)
  have hn := cutoff_const_lt hLr hδ hν
  exact ⟨by linarith [hn.1], by linarith [hn.1, hn.2]⟩

/-- **The `ν ≤ 1` form** of `regIneq_cutoff`: `|Ψ(x) - c| < 2 δ / √ν`. -/
theorem regIneq_cutoff_le_one {D : BgData G N} {φ : G.Ω 1 × Fin N → ℂ}
    {T S : Finset (Torus d (N₀ * L ^ q))} {δ ν : ℝ} (hT : BlockClose G D φ T δ)
    (hS : FieldClose G D φ ν S δ) (hν : 0 < ν) (hν1 : ν ≤ 1)
    {x : Torus d (N₀ * L ^ q)} (hx : x ∈ G.Ω 1) (hxT : x ∈ T)
    (hblock : ∀ y ∈ G.blk (G.layerIndex x) x, y ∈ S) {c : Fin N → ℂ}
    (hc : ∀ y ∈ G.blk (G.layerIndex x) x, ∀ i, D.h y i = c i) :
    vn (fun i => D.Ψ x i - c i) < 2 * δ / Real.sqrt ν := by
  have h := regIneq_cutoff hT hS hν hx hxT hblock hc
  have hδ : 0 ≤ δ := (vn_nonneg _).trans (hT x hxT).le
  exact lt_of_lt_of_le h (cutoff_const_le_one hδ hν hν1)

/-- Constant-field instance: for `φ ≡ e`, `Ψ ≡ e`, `h ≡ e` on all of `Ω₁` (tested set `Ω₁`, field
set `Ω₁`, tolerance `1`, any mass `ν > 0`), all hypotheses of `regIneq_cutoff` hold and the
conclusion is the (trivial) `|Ψ(x) - e| = 0 < 1 + 1/√ν`.  A non-constant instance is not provided. -/
theorem regIneq_cutoff_const (e : Fin N → ℝ) (he : ∑ i, e i ^ 2 = 1) {ν : ℝ} (hν : 0 < ν) {x : Torus d (N₀ * L ^ q)}
    (hx : x ∈ G.Ω 1) :
    ∃ (T S : Finset (Torus d (N₀ * L ^ q))),
      BlockClose G (constUnitBg G e) (constUnitPhi G e) T 1 ∧
      FieldClose G (constUnitBg G e) (constUnitPhi G e) ν S 1 ∧ x ∈ T ∧
      (∀ y ∈ G.blk (G.layerIndex x) x, y ∈ S) ∧
      (∀ y ∈ G.blk (G.layerIndex x) x, ∀ i, (constUnitBg G e).h y i = (e i : ℂ)) ∧
      vn (fun i => (constUnitBg G e).Ψ x i - (e i : ℂ)) < 1 + 1 / Real.sqrt ν := by
  classical
  obtain ⟨hn1, hnk, hxl⟩ := G.layerIndex_spec hx
  have hsub := blk_subset_Ω G hn1 hnk hxl
  have hzero : vn (fun i => (constUnitBg G e).Ψ x i - (e i : ℂ)) = 0 := by
    have : (fun i => (constUnitBg G e).Ψ x i - (e i : ℂ)) = 0 := by
      funext i; rw [constUnitBg_Ψ ((mem_dataSites G).2 (Or.inl hx))]; simp
    rw [this, vn_zero]
  refine ⟨Finset.univ.filter (· ∈ G.Ω 1), Finset.univ.filter (· ∈ G.Ω 1), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro y hy
    have hyΩ : y ∈ G.Ω 1 := (Finset.mem_filter.1 hy).2
    unfold blockDev
    have : (fun i => (constUnitBg G e).Ψ y i - blockAvg G (constUnitPhi G e) y i) = 0 := by
      funext i
      rw [blockAvg_constUnitPhi e hyΩ, constUnitBg_Ψ ((mem_dataSites G).2 (Or.inl hyΩ)), sub_self]
      rfl
    rw [this, vn_zero]; exact one_pos
  · intro _ y _
    have hz : (fun i => constUnitPhi G e (y, i) - (constUnitBg G e).h y i) = 0 := by
      funext i; rw [constUnitBg_h y.2]; simp [constUnitPhi]
    refine ⟨by rw [hz, vn_zero]; positivity, ?_⟩
    have h1 : ∀ i, (constUnitBg G e).h y i = (e i : ℂ) := fun i => constUnitBg_h y.2 i
    have he' : ∑ i, (e i : ℂ) * (e i : ℂ) = 1 := by
      have : ∑ i, e i * e i = 1 := by simpa [sq] using he
      exact_mod_cast this
    have : ∑ i, (constUnitBg G e).h y i * (constUnitBg G e).h y i - 1 = 0 := by
      rw [Finset.sum_congr rfl fun i _ => by rw [h1 i], he', sub_self]
    rw [this, norm_zero]; positivity
  · simp [hx]
  · intro y hy; simp [hsub hy]
  · intro y hy i; exact constUnitBg_h (hsub hy) i
  · rw [hzero]; positivity

end Reg

section Stop

open Balaban.LargeField.StopIndex Balaban.Fluctuation Balaban.SmallField.Def6v2

variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ} {G : GeneratingSet d L N₀ k ϱ}
  {β ν₀ a ε₀ : ℝ} {b n : ℕ → ℝ}

/-- **P4 (6.2) at the stopping index, `XiBounds` form.**  Under `RunningHyp` with `0 < kStop`, let
`ν_k = n (kStop)` be the dimensionless mass of the final step, i.e. `ν L^{2k} = n (kStop)` for the
fine-lattice mass `ν` of `XiBounds` on a generating set of top level `k`.  If `XiBounds` holds
(`σ = 1`, tolerance `ε`) and `x` is a top-layer site, then `|ψ_k(x) - h₀| < (5L+3) ε` (and
`ν_k < 1`).  That the tests hold for the physical final density is `FINAL-CUTOFF-BRIDGE`. -/
theorem p4_cutoff_xi (h : RunningHyp d L β ν₀ a ε₀ b n) (hpos : 0 < kStop h) {ν : ℝ} {m : ℕ}
    {ε : ℝ} {D : BgData G N} {h₀ : Fin N → ℝ} {φ : G.Ω 1 × Fin N → ℂ} {α : G.Ω 1 → ℂ}
    (hb : XiBounds G ν m 1 ε D h₀ φ α) (hk : 1 ≤ k) (hL : 1 ≤ L)
    (hνk : ν * ((L : ℝ) ^ k) ^ 2 = n (kStop h)) {x : Torus d (N₀ * L ^ k)} (hx : x ∈ G.layer k) :
    n (kStop h) < 1 ∧ vn (fun i => D.Ψ x i - (h₀ i : ℂ)) < (5 * L + 3) * ε := by
  refine ⟨n_kStop_lt_one h hpos, ?_⟩
  exact (xiBounds_cutoff_top hb hk hx (by rw [hνk]; exact kStop_spec h) hL).2

/-- **P4 (6.2) at the stopping index, cube-test form** (`ν = n (kStop)`). -/
theorem p4_cutoff_reg (h : RunningHyp d L β ν₀ a ε₀ b n) (hpos : 0 < kStop h) {D : BgData G N}
    {φ : G.Ω 1 × Fin N → ℂ} {T S : Finset (Torus d (N₀ * L ^ k))} {δ : ℝ}
    (hT : BlockClose G D φ T δ) (hS : FieldClose G D φ (n (kStop h)) S δ) (hL : 1 ≤ L)
    {x : Torus d (N₀ * L ^ k)} (hx : x ∈ G.Ω 1) (hxT : x ∈ T)
    (hblock : ∀ y ∈ G.blk (G.layerIndex x) x, y ∈ S) {c : Fin N → ℂ}
    (hc : ∀ y ∈ G.blk (G.layerIndex x) x, ∀ i, D.h y i = c i) :
    n (kStop h) < 1 ∧ vn (fun i => D.Ψ x i - c i) < (5 * L + 3) * δ :=
  ⟨n_kStop_lt_one h hpos, (regIneq_cutoff_five hT hS hL (kStop_spec h) hx hxT hblock hc).2⟩

end Stop

end Balaban.FinalCutoff
