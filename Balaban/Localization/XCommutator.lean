/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Multiscale.ConstraintSandwich
public import Balaban.Multiscale.XVariantAgmon
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

/-!
# The commutator of the x-variant operator with a smooth field, weighted `L²` bound (DG7, I-4c)

For the x-variant operator `H_{k,x}(α)` of GREEN.md (1.7) (`xDirichletOperator`) and a smooth field
`φ` (`IsSmoothField`) the commutator `K_x(φ) s = φ · H_{k,x} s - H_{k,x} (φ · s)` is, at `y ∈ Ω₁`,
the sum of the Laplacian part `lapTerm` (as for `H_D`) and a block part.  The block part is bounded
in the weighted norms of the Agmon estimate, **uniformly in `x ≥ 0`** (the coefficients of the blocks
`s₁ = a_k x/(a_k + x)`, `s₂ - s₁` are non-negative with sum `≤ a_k ≤ 2`):

* `commK_restrict_diag`: the commutator of `restrictOp F + diag α` is `F` applied to the
  commutator argument (the diagonal cancels), for every real matrix `F`;
* `commK_xOperator_split`: `K_x(φ) s (y) = lapTerm + (x-variant averaging form) (commArg)`;
* `layerBlock_comm_norm_le`: the block part of one layer-block term;
* `commKx_pointwise`: the weighted pointwise bound at `y ∈ layer j`;
* `agmonSource_commKx_le`: **`‖ℓ w K_x(φ) s‖² ≤ C δ² (‖w ∂ s‖²_Λ + ‖ℓ⁻¹ w s‖²)`** where the
  gradient is charged only on a set `Λ ⊇ {y : K_x(φ) s (y) ≠ 0}`.  The constant depends on `d, L`.
-/

@[expose] public section

namespace Balaban.Multiscale

open Matrix Finset Balaban

variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}

section Formula

theorem commK_restrict_diag {K : ℕ} (G : GeneratingSet d L N₀ K ϱ)
    (F : Matrix (Torus d (N₀ * L ^ K)) (Torus d (N₀ * L ^ K)) ℝ) (α : G.Ω 1 → ℂ)
    (φ : Torus d (N₀ * L ^ K) → Fin N → ℂ) (s : G.Ω 1 × Fin N → ℂ) (x : G.Ω 1) :
    (commK (Green.restrictOp (F.map (algebraMap ℝ ℂ)) (G.Ω 1) + Matrix.diagonal α)
        (restrictField G φ) *ᵥ s) x =
      (F.map (algebraMap ℝ ℂ) *ᵥ commArg G φ s x) x := by
  rw [commK_mulVec]
  have hy : ∀ y : G.Ω 1, ∑ i, (restrictField G φ x i - restrictField G φ y i) * s (y, i) =
      commArg G φ s x y := by
    intro y
    simp only [commArg, restrictField]
    exact Finset.sum_congr rfl fun i _ => by rw [svec_of_mem]
  have h1 : ∀ y : G.Ω 1, ∑ i, (Green.restrictOp (F.map (algebraMap ℝ ℂ)) (G.Ω 1) +
      Matrix.diagonal α) x y * (restrictField G φ x i - restrictField G φ y i) * s (y, i) =
      (Green.restrictOp (F.map (algebraMap ℝ ℂ)) (G.Ω 1) + Matrix.diagonal α) x y *
        commArg G φ s x y := by
    intro y
    rw [← hy y, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  simp only [h1]
  simp only [Matrix.add_apply, add_mul, Finset.sum_add_distrib, Green.restrictOp,
    Matrix.submatrix_apply, Matrix.diagonal_apply, ite_mul, zero_mul]
  rw [Finset.sum_ite_eq]
  simp only [Finset.mem_univ, ↓reduceIte]
  have hxx : commArg G φ s x x = 0 := commArg_self G φ s x
  rw [hxx, mul_zero, add_zero]
  simp only [Matrix.mulVec, dotProduct]
  exact (Green.sum_eq_sum_subtype (G.Ω 1) (fun y => F.map (algebraMap ℝ ℂ) x y *
    commArg G φ s x y) (fun i hi => by rw [commArg_of_not_mem G φ s x hi, mul_zero])).symm

variable {k : ℕ} (G : GeneratingSet d L N₀ (k + 1) ϱ)

theorem commK_xOperator_split (a : ℕ → ℝ) (aT x ν : ℝ) (α : G.Ω 1 → ℂ)
    (φ : Torus d (N₀ * L ^ (k + 1)) → Fin N → ℂ) (s : G.Ω 1 × Fin N → ℂ) (y : G.Ω 1) :
    (commK (xDirichletOperator G a aT x ν α) (restrictField G φ) *ᵥ s) y =
      lapTerm G φ s y +
        ((xAvgMatrix G a (xS1 (a k) x) (xS2 (a k) (aT / (L : ℝ) ^ 2) x)).map
          (algebraMap ℝ ℂ) *ᵥ commArg G φ s y) y := by
  unfold xDirichletOperator
  rw [commK_restrict_diag, ← lap_part_eq G ν φ s y]
  unfold xFullMatrix
  have : ((latticeLaplacian d (N₀ * L ^ (k + 1)) ν +
      xAvgMatrix G a (xS1 (a k) x) (xS2 (a k) (aT / (L : ℝ) ^ 2) x)).map (algebraMap ℝ ℂ)) =
      (latticeLaplacian d (N₀ * L ^ (k + 1)) ν).map (algebraMap ℝ ℂ) +
        (xAvgMatrix G a (xS1 (a k) x) (xS2 (a k) (aT / (L : ℝ) ^ 2) x)).map
          (algebraMap ℝ ℂ) := by
    ext y z; simp
  rw [this, Matrix.add_mulVec, Pi.add_apply]

end Formula

/-! ### Block averages and the rows of the x-variant averaging form -/

section Rows

/-- The block average `(L^m)^{-d} ∑_{y' ∈ Δ_m(y)} V(y')`. -/
noncomputable def blkAvg {K : ℕ} (G : GeneratingSet d L N₀ K ϱ) (m : ℕ)
    (V : Torus d (N₀ * L ^ K) → ℝ) (y : Torus d (N₀ * L ^ K)) : ℝ :=
  (((L : ℝ) ^ m) ^ d)⁻¹ * ∑ y' ∈ G.blk m y, V y'

theorem blkAvg_nonneg {K : ℕ} (G : GeneratingSet d L N₀ K ϱ) (m : ℕ)
    {V : Torus d (N₀ * L ^ K) → ℝ} (hV : ∀ y, 0 ≤ V y) (y : Torus d (N₀ * L ^ K)) :
    0 ≤ blkAvg G m V y := by
  unfold blkAvg
  have : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  exact mul_nonneg (by positivity) (Finset.sum_nonneg fun y' _ => hV y')

/-- **The block average is a mean-square contraction on a layer** (levels `m` inside the layer). -/
theorem layer_blkAvg_sq_le {K : ℕ} (G : GeneratingSet d L N₀ K ϱ) {j m : ℕ} (hm : m ≤ K)
    (hsat : ∀ y y' : Torus d (N₀ * L ^ K), y ∈ G.layer j → y' ∈ G.blk m y → y' ∈ G.layer j)
    (V : Torus d (N₀ * L ^ K) → ℝ) :
    ∑ y ∈ G.layer j, (blkAvg G m V y) ^ 2 ≤ ∑ y ∈ G.layer j, V y ^ 2 := by
  have hL : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  set c : ℝ := (((L : ℝ) ^ m) ^ d)⁻¹ with hc
  have hc0 : 0 < c := by positivity
  have hcard : ((L : ℝ) ^ m) ^ d * c = 1 := by rw [hc]; field_simp
  have h1 : ∀ x ∈ G.layer j, (blkAvg G m V x) ^ 2 ≤ c * ∑ y ∈ G.blk m x, V y ^ 2 := by
    intro x _
    have h := sq_sum_le_card_mul_sum_sq (s := G.blk m x) (f := V)
    rw [card_blk_cast G m hm] at h
    unfold blkAvg
    rw [← hc]
    calc (c * ∑ y ∈ G.blk m x, V y) ^ 2 = c ^ 2 * (∑ y ∈ G.blk m x, V y) ^ 2 := by ring
      _ ≤ c ^ 2 * (((L : ℝ) ^ m) ^ d * ∑ y ∈ G.blk m x, V y ^ 2) :=
          mul_le_mul_of_nonneg_left h (by positivity)
      _ = c * ((((L : ℝ) ^ m) ^ d * c) * ∑ y ∈ G.blk m x, V y ^ 2) := by ring
      _ = c * ∑ y ∈ G.blk m x, V y ^ 2 := by rw [hcard, one_mul]
  refine (Finset.sum_le_sum h1).trans ?_
  rw [← Finset.mul_sum]
  have h2 : ∑ x ∈ G.layer j, ∑ y ∈ G.blk m x, V y ^ 2 =
      ∑ y ∈ G.layer j, ((L : ℝ) ^ m) ^ d * V y ^ 2 := by
    have e : ∀ x ∈ G.layer j, ∑ y ∈ G.blk m x, V y ^ 2 =
        ∑ y : Torus d (N₀ * L ^ K),
          if jBlock d L N₀ K m y = jBlock d L N₀ K m x then V y ^ 2 else 0 := by
      intro x _
      rw [GeneratingSet.blk, Finset.sum_filter]
    rw [Finset.sum_congr rfl e, Finset.sum_comm]
    have e2 : ∀ y : Torus d (N₀ * L ^ K),
        ∑ x ∈ G.layer j, (if jBlock d L N₀ K m y = jBlock d L N₀ K m x then V y ^ 2 else 0) =
          if y ∈ G.layer j then ((L : ℝ) ^ m) ^ d * V y ^ 2 else 0 := by
      intro y
      by_cases hy : y ∈ G.layer j
      · simp only [hy, ↓reduceIte]
        rw [← Finset.sum_filter]
        have : (G.layer j).filter (fun x => jBlock d L N₀ K m y = jBlock d L N₀ K m x) =
            G.blk m y := by
          ext x
          simp only [Finset.mem_filter, GeneratingSet.mem_blk]
          constructor
          · exact fun h => h.2.symm
          · intro h
            exact ⟨hsat y x hy (GeneratingSet.mem_blk.2 h), h.symm⟩
        rw [this, Finset.sum_const, nsmul_eq_mul, card_blk_cast G m hm]
      · simp only [hy, ↓reduceIte]
        refine Finset.sum_eq_zero fun x hx => ?_
        have : jBlock d L N₀ K m y ≠ jBlock d L N₀ K m x := fun h =>
          hy (hsat x y hx (GeneratingSet.mem_blk.2 h))
        simp [this]
    rw [Finset.sum_congr rfl fun y _ => e2 y, ← Finset.sum_filter]
    congr 1
    ext y; simp
  rw [h2]
  have : c * ∑ y ∈ G.layer j, ((L : ℝ) ^ m) ^ d * V y ^ 2 = ∑ y ∈ G.layer j, V y ^ 2 := by
    rw [← Finset.mul_sum, ← mul_assoc, mul_comm c, hcard, one_mul]
  exact this.le

variable {k : ℕ} (G : GeneratingSet d L N₀ (k + 1) ϱ)

theorem layerBlockMatrix_of_not_mem {K : ℕ} (G : GeneratingSet d L N₀ K ϱ) {j m : ℕ}
    {y : Torus d (N₀ * L ^ K)} (hy : y ∉ G.layer j) (y' : Torus d (N₀ * L ^ K)) :
    layerBlockMatrix G j m y y' = 0 := by
  simp [layerBlockMatrix, hy]

theorem xAvg_apply_low (a : ℕ → ℝ) (s₁ s₂ : ℝ) {j : ℕ} (hj1 : 1 ≤ j) (hjk : j ≤ k)
    {y : Torus d (N₀ * L ^ (k + 1))} (hy : y ∈ G.layer j) (y' : Torus d (N₀ * L ^ (k + 1))) :
    xAvgMatrix G a s₁ s₂ y y' = a j / ((L : ℝ) ^ j) ^ 2 * layerBlockMatrix G j j y y' := by
  unfold xAvgMatrix
  have htop : y ∉ G.layer (k + 1) :=
    G.layer_disjoint hj1 (by omega) (by omega) le_rfl (by omega) hy
  rw [Matrix.add_apply, Matrix.add_apply, Matrix.sum_apply, Matrix.smul_apply, Matrix.smul_apply,
    layerBlockMatrix_of_not_mem G htop, layerBlockMatrix_of_not_mem G htop, Finset.sum_eq_single j]
  · simp
  · intro j' hj' hne
    have hx' : y ∉ G.layer j' := G.layer_disjoint hj1 (by omega) (Finset.mem_Icc.1 hj').1
      (by have := (Finset.mem_Icc.1 hj').2; omega) (Ne.symm hne) hy
    rw [Matrix.smul_apply, layerBlockMatrix_of_not_mem G hx']
    simp
  · intro h
    exact absurd (Finset.mem_Icc.2 ⟨hj1, hjk⟩) h

theorem xAvg_apply_top (a : ℕ → ℝ) (s₁ s₂ : ℝ) {y : Torus d (N₀ * L ^ (k + 1))}
    (hy : y ∈ G.layer (k + 1)) (y' : Torus d (N₀ * L ^ (k + 1))) :
    xAvgMatrix G a s₁ s₂ y y' =
      s₁ / ((L : ℝ) ^ k) ^ 2 * layerBlockMatrix G (k + 1) k y y' +
        (s₂ - s₁) / ((L : ℝ) ^ k) ^ 2 * layerBlockMatrix G (k + 1) (k + 1) y y' := by
  unfold xAvgMatrix
  rw [Matrix.add_apply, Matrix.add_apply, Matrix.sum_apply, Matrix.smul_apply, Matrix.smul_apply]
  have h0 : ∑ j ∈ Finset.Icc 1 k, ((a j / ((L : ℝ) ^ j) ^ 2) •
      layerBlockMatrix G j j) y y' = 0 := by
    refine Finset.sum_eq_zero fun j hj => ?_
    have hx' : y ∉ G.layer j := G.layer_disjoint (by omega) le_rfl
      (by have := (Finset.mem_Icc.1 hj).1; omega) (by have := (Finset.mem_Icc.1 hj).2; omega)
      (by have := (Finset.mem_Icc.1 hj).2; omega) hy
    rw [Matrix.smul_apply, layerBlockMatrix_of_not_mem G hx']
    simp
  rw [h0, zero_add]
  simp

theorem mulVec_comb {K : ℕ} (M A B : Matrix (Torus d (N₀ * L ^ K)) (Torus d (N₀ * L ^ K)) ℝ)
    (c₁ c₂ : ℝ) (y : Torus d (N₀ * L ^ K))
    (h : ∀ y', M y y' = c₁ * A y y' + c₂ * B y y') (v : Torus d (N₀ * L ^ K) → ℂ) :
    (M.map (algebraMap ℝ ℂ) *ᵥ v) y =
      (c₁ : ℂ) * (A.map (algebraMap ℝ ℂ) *ᵥ v) y + (c₂ : ℂ) * (B.map (algebraMap ℝ ℂ) *ᵥ v) y := by
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, h, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun y' _ => ?_
  simp only [map_add, map_mul, Complex.coe_algebraMap]
  ring

end Rows


section Pointwise

/-- The block part of one layer-block term at `y ∈ layer j`: the commutator argument is bounded by
the oscillation of `φ` on the `j`-block, so the term is at most `2 d δ` times the `m`-block average
of `|s̃|` (`m`-blocks inside the `j`-block of `y`). -/
theorem layerBlock_comm_norm_le {K : ℕ} (G : GeneratingSet d L N₀ K ϱ) {δ : ℝ}
    {φ : Torus d (N₀ * L ^ K) → Fin N → ℂ} (hφ : IsSmoothField G δ φ) (hδ : 0 ≤ δ)
    (s : G.Ω 1 × Fin N → ℂ) {j m : ℕ} (hj1 : 1 ≤ j) (hjK : j ≤ K)
    (hnest : ∀ y y' : Torus d (N₀ * L ^ K), y' ∈ G.blk m y → y' ∈ G.blk j y)
    {y : Torus d (N₀ * L ^ K)} (hy : y ∈ G.layer j) :
    ‖((layerBlockMatrix G j m).map (algebraMap ℝ ℂ) *ᵥ commArg G φ s y) y‖ ≤
      2 * d * δ * blkAvg G m (fun y' => vn (svec G s y')) y := by
  have hL : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply]
  have hterm : ∀ y' : Torus d (N₀ * L ^ K),
      ‖(algebraMap ℝ ℂ) (layerBlockMatrix G j m y y') * commArg G φ s y y'‖ ≤
        if y' ∈ G.blk m y then (((L : ℝ) ^ m) ^ d)⁻¹ * (2 * d * δ * vn (svec G s y')) else 0 := by
    intro y'
    by_cases hy' : y' ∈ G.blk m y
    · simp only [hy', ↓reduceIte]
      have hjb := GeneratingSet.mem_blk.1 (hnest y y' hy')
      have hy'l : y' ∈ G.layer j := (G.mem_layer_iff hj1 hjK hjb.symm).1 hy
      have hmb := GeneratingSet.mem_blk.1 hy'
      have hLB : layerBlockMatrix G j m y y' = (((L : ℝ) ^ m) ^ d)⁻¹ := by
        unfold layerBlockMatrix blockProjMatrix
        have : blockMap (L ^ m) (N₀ * L ^ (K - m)) y = blockMap (L ^ m) (N₀ * L ^ (K - m)) y' :=
          hmb.symm
        simp [hy, hy'l, this]
      rw [hLB, norm_mul, norm_algebraMap', Real.norm_of_nonneg (by positivity)]
      have := commArg_norm_le G hφ hδ s hj1 hjK hy (hnest y y' hy')
      gcongr
    · simp only [hy', ↓reduceIte]
      have : layerBlockMatrix G j m y y' = 0 := by
        unfold layerBlockMatrix blockProjMatrix
        have hne : blockMap (L ^ m) (N₀ * L ^ (K - m)) y ≠
            blockMap (L ^ m) (N₀ * L ^ (K - m)) y' := fun h => hy' (GeneratingSet.mem_blk.2 h.symm)
        simp [hne]
      rw [this]; simp
  calc ‖∑ y', (algebraMap ℝ ℂ) (layerBlockMatrix G j m y y') * commArg G φ s y y'‖
      ≤ ∑ y', ‖(algebraMap ℝ ℂ) (layerBlockMatrix G j m y y') * commArg G φ s y y'‖ :=
        norm_sum_le _ _
    _ ≤ ∑ y', (if y' ∈ G.blk m y then (((L : ℝ) ^ m) ^ d)⁻¹ * (2 * d * δ * vn (svec G s y'))
          else 0) := Finset.sum_le_sum fun y' _ => hterm y'
    _ = 2 * d * δ * blkAvg G m (fun y' => vn (svec G s y')) y := by
        rw [← Finset.sum_filter]
        have : (Finset.univ.filter fun y' => y' ∈ G.blk m y) = G.blk m y := by ext; simp
        rw [this]
        unfold blkAvg
        rw [Finset.mul_sum, Finset.mul_sum]
        exact Finset.sum_congr rfl fun y' _ => by ring

/-- The weight is comparable on a block: `w(y) avg(V) ≤ e^{2εd} avg(w V)`. -/
theorem w_blkAvg_le {K : ℕ} (G : GeneratingSet d L N₀ K ϱ) {r : Torus d (N₀ * L ^ K) → ℝ}
    (hr : IsAgmonWeight G r) {ε : ℝ} (hε0 : 0 ≤ ε) {j m : ℕ} (hj1 : 1 ≤ j) (hjK : j ≤ K)
    (hnest : ∀ y y' : Torus d (N₀ * L ^ K), y' ∈ G.blk m y → y' ∈ G.blk j y)
    {y : Torus d (N₀ * L ^ K)} (hy : y ∈ G.layer j) (V : Torus d (N₀ * L ^ K) → ℝ)
    (hV : ∀ z, 0 ≤ V z) :
    Real.exp (ε * r y) * blkAvg G m V y ≤
      Real.exp (ε * (2 * d)) * blkAvg G m (fun z => Real.exp (ε * r z) * V z) y := by
  have hL : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  unfold blkAvg
  have hc : 0 ≤ (((L : ℝ) ^ m) ^ d)⁻¹ := by positivity
  calc Real.exp (ε * r y) * ((((L : ℝ) ^ m) ^ d)⁻¹ * ∑ y' ∈ G.blk m y, V y')
      = (((L : ℝ) ^ m) ^ d)⁻¹ * ∑ y' ∈ G.blk m y, Real.exp (ε * r y) * V y' := by
        rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
        exact Finset.sum_congr rfl fun z _ => by ring
    _ ≤ (((L : ℝ) ^ m) ^ d)⁻¹ * ∑ y' ∈ G.blk m y,
          Real.exp (ε * (2 * d)) * (Real.exp (ε * r y') * V y') := by
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun z hz => ?_) hc
        have hb := hr.block j hj1 hjK y z hy (GeneratingSet.mem_blk.1 (hnest y z hz))
        have : r y ≤ r z + 2 * d := by linarith [(abs_le.1 hb).2, (abs_le.1 hb).1]
        have hexp : Real.exp (ε * r y) ≤ Real.exp (ε * (2 * d)) * Real.exp (ε * r z) := by
          rw [← Real.exp_add]
          exact Real.exp_le_exp.2 (by nlinarith)
        calc Real.exp (ε * r y) * V z ≤ (Real.exp (ε * (2 * d)) * Real.exp (ε * r z)) * V z :=
              mul_le_mul_of_nonneg_right hexp (hV z)
          _ = _ := by ring
    _ = Real.exp (ε * (2 * d)) * ((((L : ℝ) ^ m) ^ d)⁻¹ *
          ∑ y' ∈ G.blk m y, Real.exp (ε * r y') * V y') := by
        rw [← Finset.mul_sum]; ring

end Pointwise


section Weighted

variable {k : ℕ} (G : GeneratingSet d L N₀ (k + 1) ϱ)

/-- The weighted bound for the Laplacian part. -/
theorem lap_weighted {δ : ℝ} {φ : Torus d (N₀ * L ^ (k + 1)) → Fin N → ℂ}
    (hφ : IsSmoothField G δ φ) (s : G.Ω 1 × Fin N → ℂ) {j : ℕ} (hj1 : 1 ≤ j)
    (hjK : j ≤ k + 1) {r : Torus d (N₀ * L ^ (k + 1)) → ℝ} {ε : ℝ} (y : G.Ω 1)
    (hy : (y : Torus d (N₀ * L ^ (k + 1))) ∈ G.layer j) :
    (L : ℝ) ^ j * Real.exp (ε * r y) * ‖lapTerm G φ s y‖ ≤
      δ * Real.exp (ε * r y) * ∑ μ : Fin d,
          (vn (svec G s ((y : Torus d (N₀ * L ^ (k + 1))) + Pi.single μ 1) - svec G s y) +
            vn (svec G s ((y : Torus d (N₀ * L ^ (k + 1))) - Pi.single μ 1) - svec G s y)) +
        δ * ((L : ℝ) ^ j)⁻¹ * (Real.exp (ε * r y) * vn (svec G s y)) := by
  have hL : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hLj : (0 : ℝ) < (L : ℝ) ^ j := by positivity
  have hsp : G.spacing y = (L : ℝ) ^ j := G.spacing_eq hj1 hjK hy
  have h1 := lapTerm_norm_le G hφ s y.2
  rw [hsp] at h1
  have hW0 : 0 < Real.exp (ε * r y) := Real.exp_pos _
  calc (L : ℝ) ^ j * Real.exp (ε * r y) * ‖lapTerm G φ s y‖
      ≤ (L : ℝ) ^ j * Real.exp (ε * r y) *
        (δ / (L : ℝ) ^ j * ∑ μ : Fin d,
          (vn (svec G s ((y : Torus d (N₀ * L ^ (k + 1))) + Pi.single μ 1) - svec G s y) +
            vn (svec G s ((y : Torus d (N₀ * L ^ (k + 1))) - Pi.single μ 1) - svec G s y)) +
          δ / ((L : ℝ) ^ j) ^ 2 * vn (svec G s y)) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = _ := by field_simp

/-- **Block part, layers `j ≤ k`**: the row of the x-variant form is the row of `a_j L^{-2j} P_j`. -/
theorem blockPart_low {a : ℕ → ℝ} (ha : IsAdmissibleWeights k a) (s₁ s₂ : ℝ)
    {δ : ℝ} {φ : Torus d (N₀ * L ^ (k + 1)) → Fin N → ℂ} (hφ : IsSmoothField G δ φ)
    (hδ : 0 ≤ δ) (s : G.Ω 1 × Fin N → ℂ) {r : Torus d (N₀ * L ^ (k + 1)) → ℝ}
    (hr : IsAgmonWeight G r) {ε : ℝ} (hε0 : 0 ≤ ε) {j : ℕ} (hj1 : 1 ≤ j) (hjk : j ≤ k)
    (y : G.Ω 1) (hy : (y : Torus d (N₀ * L ^ (k + 1))) ∈ G.layer j) :
    (L : ℝ) ^ j * Real.exp (ε * r y) *
        ‖((xAvgMatrix G a s₁ s₂).map (algebraMap ℝ ℂ) *ᵥ commArg G φ s y) y‖ ≤
      4 * d * (L : ℝ) ^ 2 * δ * Real.exp (ε * (2 * d)) * ((L : ℝ) ^ j)⁻¹ *
        (blkAvg G j (fun z => Real.exp (ε * r z) * vn (svec G s z)) y +
          blkAvg G j (fun z => Real.exp (ε * r z) * vn (svec G s z)) y) := by
  have hL : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne L)
  have hLj : (0 : ℝ) < (L : ℝ) ^ j := by positivity
  have hrow := mulVec_comb ((xAvgMatrix G a s₁ s₂)) (layerBlockMatrix G j j)
    (layerBlockMatrix G j j) (a j / ((L : ℝ) ^ j) ^ 2) 0 y
    (fun y' => by rw [xAvg_apply_low G a s₁ s₂ hj1 hjk hy y']; ring)
    (commArg G φ s y)
  rw [hrow]
  simp only [Complex.ofReal_zero, zero_mul, add_zero, norm_mul, Complex.norm_real]
  have haj := ha j hj1 hjk
  have hc0 : 0 ≤ a j / ((L : ℝ) ^ j) ^ 2 := div_nonneg (by linarith [haj.1]) (by positivity)
  rw [Real.norm_of_nonneg hc0]
  have hb := layerBlock_comm_norm_le G hφ hδ s hj1 (by omega : j ≤ k + 1)
    (m := j) (fun y y' h => h) hy
  have hW := w_blkAvg_le G hr hε0 hj1 (by omega : j ≤ k + 1) (m := j) (fun y y' h => h) hy
    (fun z => vn (svec G s z)) (fun z => vn_nonneg _)
  set A := blkAvg G j (fun z => Real.exp (ε * r z) * vn (svec G s z)) y with hA
  set Av := blkAvg G j (fun z => vn (svec G s z)) y with hAv
  have hA0 : 0 ≤ A := blkAvg_nonneg G j (fun z => mul_nonneg (Real.exp_pos _).le (vn_nonneg _)) y
  have hE0 : 0 < Real.exp (ε * (2 * d)) := Real.exp_pos _
  have hw0 : 0 < Real.exp (ε * r y) := Real.exp_pos _
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hL2 : (1 : ℝ) ≤ (L : ℝ) ^ 2 := by nlinarith
  have hAv0 : 0 ≤ Av := blkAvg_nonneg G j (fun z => vn_nonneg _) y
  calc (L : ℝ) ^ j * Real.exp (ε * r y) * (a j / ((L : ℝ) ^ j) ^ 2 *
        ‖((layerBlockMatrix G j j).map (algebraMap ℝ ℂ) *ᵥ commArg G φ s y) y‖)
      ≤ (L : ℝ) ^ j * Real.exp (ε * r y) * (a j / ((L : ℝ) ^ j) ^ 2 * (2 * d * δ * Av)) := by
        gcongr
    _ = (2 * a j * d * δ * ((L : ℝ) ^ j)⁻¹) * (Real.exp (ε * r y) * Av) := by
        field_simp
    _ ≤ (2 * a j * d * δ * ((L : ℝ) ^ j)⁻¹) * (Real.exp (ε * (2 * d)) * A) := by
        refine mul_le_mul_of_nonneg_left hW ?_
        have : 0 ≤ a j := by linarith [haj.1]
        positivity
    _ ≤ _ := by
        have hi : 0 ≤ ((L : ℝ) ^ j)⁻¹ := by positivity
        have h2 : a j ≤ 2 := haj.2
        have hq : 0 ≤ (d : ℝ) * δ * ((L : ℝ) ^ j)⁻¹ * (Real.exp (ε * (2 * d)) * A) := by positivity
        have e : 4 * d * (L : ℝ) ^ 2 * δ * Real.exp (ε * (2 * d)) * ((L : ℝ) ^ j)⁻¹ * (A + A) =
            8 * (L : ℝ) ^ 2 * ((d : ℝ) * δ * ((L : ℝ) ^ j)⁻¹ * (Real.exp (ε * (2 * d)) * A)) := by
          ring
        rw [e]
        have e2 : 2 * a j * d * δ * ((L : ℝ) ^ j)⁻¹ * (Real.exp (ε * (2 * d)) * A) =
            2 * a j * ((d : ℝ) * δ * ((L : ℝ) ^ j)⁻¹ * (Real.exp (ε * (2 * d)) * A)) := by ring
        rw [e2]
        have haj0 : 0 ≤ a j := by linarith [haj.1]
        nlinarith [mul_nonneg hq (by linarith : (0 : ℝ) ≤ 8 * (L : ℝ) ^ 2 - 2 * a j)]


omit [NeZero L] in
theorem top_coef {u t : ℝ} (hL : 0 < (L : ℝ)) (hu : 0 < u) (ht : t ≤ 2) :
    (L : ℝ) * u * (t / u ^ 2) ≤ 2 * (L : ℝ) ^ 2 * ((L : ℝ) * u)⁻¹ := by
  have e1 : (L : ℝ) * u * (t / u ^ 2) = (L : ℝ) * t / u := by field_simp
  have e2 : 2 * (L : ℝ) ^ 2 * ((L : ℝ) * u)⁻¹ = 2 * (L : ℝ) / u := by field_simp
  rw [e1, e2]
  exact div_le_div_of_nonneg_right (by nlinarith) hu.le

/-- **Block part, top layer `k + 1`**: the two block terms `s₁ L^{-2k} P_k + (s₂ - s₁) L^{-2k} P_{k+1}`
with `0 ≤ s₁`, `0 ≤ s₂ - s₁`, `s₂ ≤ 2`. -/
theorem blockPart_top {s₁ s₂ : ℝ} (hs₁ : 0 ≤ s₁) (hs : 0 ≤ s₂ - s₁) (hs₂ : s₂ ≤ 2) (a : ℕ → ℝ)
    {δ : ℝ} {φ : Torus d (N₀ * L ^ (k + 1)) → Fin N → ℂ} (hφ : IsSmoothField G δ φ)
    (hδ : 0 ≤ δ) (s : G.Ω 1 × Fin N → ℂ) {r : Torus d (N₀ * L ^ (k + 1)) → ℝ}
    (hr : IsAgmonWeight G r) {ε : ℝ} (hε0 : 0 ≤ ε)
    (y : G.Ω 1) (hy : (y : Torus d (N₀ * L ^ (k + 1))) ∈ G.layer (k + 1)) :
    (L : ℝ) ^ (k + 1) * Real.exp (ε * r y) *
        ‖((xAvgMatrix G a s₁ s₂).map (algebraMap ℝ ℂ) *ᵥ commArg G φ s y) y‖ ≤
      4 * d * (L : ℝ) ^ 2 * δ * Real.exp (ε * (2 * d)) * ((L : ℝ) ^ (k + 1))⁻¹ *
        (blkAvg G k (fun z => Real.exp (ε * r z) * vn (svec G s z)) y +
          blkAvg G (k + 1) (fun z => Real.exp (ε * r z) * vn (svec G s z)) y) := by
  have hL : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hu : (0 : ℝ) < (L : ℝ) ^ k := by positivity
  have hrow := mulVec_comb ((xAvgMatrix G a s₁ s₂)) (layerBlockMatrix G (k + 1) k)
    (layerBlockMatrix G (k + 1) (k + 1)) (s₁ / ((L : ℝ) ^ k) ^ 2) ((s₂ - s₁) / ((L : ℝ) ^ k) ^ 2) y
    (fun y' => xAvg_apply_top G a s₁ s₂ hy y') (commArg G φ s y)
  rw [hrow]
  have hnest1 : ∀ y y' : Torus d (N₀ * L ^ (k + 1)), y' ∈ G.blk k y → y' ∈ G.blk (k + 1) y := by
    intro y y' h
    rw [GeneratingSet.mem_blk] at h ⊢
    exact GeneratingSet.jBlock_succ_eq (by omega) h
  have hb1 := layerBlock_comm_norm_le G hφ hδ s (by omega : 1 ≤ k + 1) le_rfl (m := k) hnest1 hy
  have hb2 := layerBlock_comm_norm_le G hφ hδ s (by omega : 1 ≤ k + 1) le_rfl (m := k + 1)
    (fun y y' h => h) hy
  have hW1 := w_blkAvg_le G hr hε0 (by omega : 1 ≤ k + 1) le_rfl (m := k) hnest1 hy
    (fun z => vn (svec G s z)) (fun z => vn_nonneg _)
  have hW2 := w_blkAvg_le G hr hε0 (by omega : 1 ≤ k + 1) le_rfl (m := k + 1)
    (fun y y' h => h) hy (fun z => vn (svec G s z)) (fun z => vn_nonneg _)
  set A₁ := blkAvg G k (fun z => Real.exp (ε * r z) * vn (svec G s z)) y with hA₁
  set A₂ := blkAvg G (k + 1) (fun z => Real.exp (ε * r z) * vn (svec G s z)) y with hA₂
  have hA₁0 : 0 ≤ A₁ := blkAvg_nonneg G k (fun z => mul_nonneg (Real.exp_pos _).le (vn_nonneg _)) y
  have hA₂0 : 0 ≤ A₂ :=
    blkAvg_nonneg G (k + 1) (fun z => mul_nonneg (Real.exp_pos _).le (vn_nonneg _)) y
  have hAv1 : 0 ≤ blkAvg G k (fun z => vn (svec G s z)) y := blkAvg_nonneg G k (fun z => vn_nonneg _) y
  have hAv2 : 0 ≤ blkAvg G (k + 1) (fun z => vn (svec G s z)) y :=
    blkAvg_nonneg G (k + 1) (fun z => vn_nonneg _) y
  have hE0 : 0 < Real.exp (ε * (2 * d)) := Real.exp_pos _
  have hw0 : 0 < Real.exp (ε * r y) := Real.exp_pos _
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hc1 : 0 ≤ s₁ / ((L : ℝ) ^ k) ^ 2 := by positivity
  have hc2 : 0 ≤ (s₂ - s₁) / ((L : ℝ) ^ k) ^ 2 := by positivity
  have hn := norm_add_le ((s₁ / ((L : ℝ) ^ k) ^ 2 : ℝ) * ((layerBlockMatrix G (k + 1) k).map
      (algebraMap ℝ ℂ) *ᵥ commArg G φ s y) y)
    (((s₂ - s₁) / ((L : ℝ) ^ k) ^ 2 : ℝ) * ((layerBlockMatrix G (k + 1) (k + 1)).map
      (algebraMap ℝ ℂ) *ᵥ commArg G φ s y) y)
  simp only [norm_mul, Complex.norm_real, Real.norm_of_nonneg hc1, Real.norm_of_nonneg hc2] at hn
  have hco1 := top_coef (L := L) (u := (L : ℝ) ^ k) hL hu (by linarith : s₁ ≤ 2)
  have hco2 := top_coef (L := L) (u := (L : ℝ) ^ k) hL hu (by linarith : s₂ - s₁ ≤ 2)
  have hℓ : (L : ℝ) ^ (k + 1) = (L : ℝ) * (L : ℝ) ^ k := by ring
  rw [hℓ]
  calc (L : ℝ) * (L : ℝ) ^ k * Real.exp (ε * r y) * ‖_ + _‖
      ≤ (L : ℝ) * (L : ℝ) ^ k * Real.exp (ε * r y) *
        (s₁ / ((L : ℝ) ^ k) ^ 2 * ‖((layerBlockMatrix G (k + 1) k).map
          (algebraMap ℝ ℂ) *ᵥ commArg G φ s y) y‖ +
        (s₂ - s₁) / ((L : ℝ) ^ k) ^ 2 * ‖((layerBlockMatrix G (k + 1) (k + 1)).map
          (algebraMap ℝ ℂ) *ᵥ commArg G φ s y) y‖) :=
        mul_le_mul_of_nonneg_left hn (by positivity)
    _ ≤ (L : ℝ) * (L : ℝ) ^ k * Real.exp (ε * r y) *
        (s₁ / ((L : ℝ) ^ k) ^ 2 * (2 * d * δ * blkAvg G k (fun z => vn (svec G s z)) y) +
        (s₂ - s₁) / ((L : ℝ) ^ k) ^ 2 *
          (2 * d * δ * blkAvg G (k + 1) (fun z => vn (svec G s z)) y)) := by
        gcongr
    _ = ((L : ℝ) * (L : ℝ) ^ k * (s₁ / ((L : ℝ) ^ k) ^ 2)) *
          (2 * d * δ * (Real.exp (ε * r y) * blkAvg G k (fun z => vn (svec G s z)) y)) +
        ((L : ℝ) * (L : ℝ) ^ k * ((s₂ - s₁) / ((L : ℝ) ^ k) ^ 2)) *
          (2 * d * δ * (Real.exp (ε * r y) * blkAvg G (k + 1) (fun z => vn (svec G s z)) y)) := by
        ring
    _ ≤ (2 * (L : ℝ) ^ 2 * ((L : ℝ) * (L : ℝ) ^ k)⁻¹) *
          (2 * d * δ * (Real.exp (ε * (2 * d)) * A₁)) +
        (2 * (L : ℝ) ^ 2 * ((L : ℝ) * (L : ℝ) ^ k)⁻¹) *
          (2 * d * δ * (Real.exp (ε * (2 * d)) * A₂)) := by
        have hP : 0 ≤ (2 : ℝ) * d * δ := by positivity
        have i1 := mul_le_mul hco1 (mul_le_mul_of_nonneg_left hW1 hP)
          (mul_nonneg hP (mul_nonneg hw0.le hAv1)) (by positivity)
        have i2 := mul_le_mul hco2 (mul_le_mul_of_nonneg_left hW2 hP)
          (mul_nonneg hP (mul_nonneg hw0.le hAv2)) (by positivity)
        linarith
    _ = _ := by ring


/-- Core of `commKx_pointwise` with `1 ≤ k` replaced by the lower bound `1/2 ≤ a_k` (the only use of `k ≥ 1`); the weights `a_j`, `1 ≤ j ≤ k`, stay in `[1/2, 2]`. -/
theorem commKx_pointwise_of_ak {a : ℕ → ℝ} (ha : IsAdmissibleWeights k a)
    (hak : 1 / 2 ≤ a k ∧ a k ≤ 2) {aT x ν : ℝ}
    (haT1 : 1 / 2 ≤ aT) (hx : 0 ≤ x) (α : G.Ω 1 → ℂ) {δ : ℝ}
    {φ : Torus d (N₀ * L ^ (k + 1)) → Fin N → ℂ} (hφ : IsSmoothField G δ φ) (hδ : 0 ≤ δ)
    {r : Torus d (N₀ * L ^ (k + 1)) → ℝ} (hr : IsAgmonWeight G r) {ε : ℝ} (hε0 : 0 ≤ ε)
    (s : G.Ω 1 × Fin N → ℂ) {j : ℕ} (hj1 : 1 ≤ j) (hjK : j ≤ k + 1) :
    ∃ m₁ m₂ : ℕ, m₁ ≤ k + 1 ∧ m₂ ≤ k + 1 ∧
      (∀ y y' : Torus d (N₀ * L ^ (k + 1)), y' ∈ G.blk m₁ y → y' ∈ G.blk j y) ∧
      (∀ y y' : Torus d (N₀ * L ^ (k + 1)), y' ∈ G.blk m₂ y → y' ∈ G.blk j y) ∧
      ∀ y : G.Ω 1, (y : Torus d (N₀ * L ^ (k + 1))) ∈ G.layer j →
        (L : ℝ) ^ j * Real.exp (ε * r y) *
            ‖(commK (xDirichletOperator G a aT x ν α) (restrictField G φ) *ᵥ s) y‖ ≤
          δ * Real.exp (ε * r y) * ∑ μ : Fin d,
              (vn (svec G s ((y : Torus d (N₀ * L ^ (k + 1))) + Pi.single μ 1) - svec G s y) +
                vn (svec G s ((y : Torus d (N₀ * L ^ (k + 1))) - Pi.single μ 1) - svec G s y)) +
            δ * ((L : ℝ) ^ j)⁻¹ * (Real.exp (ε * r y) * vn (svec G s y)) +
            4 * d * (L : ℝ) ^ 2 * δ * Real.exp (ε * (2 * d)) * ((L : ℝ) ^ j)⁻¹ *
              (blkAvg G m₁ (fun z => Real.exp (ε * r z) * vn (svec G s z)) y +
                blkAvg G m₂ (fun z => Real.exp (ε * r z) * vn (svec G s z)) y) := by
  have hL : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hLj : (0 : ℝ) < (L : ℝ) ^ j := by positivity
  rcases Nat.lt_or_ge k j with hjk | hjk
  · have hjeq : j = k + 1 := by omega
    subst hjeq
    have hak0 : 0 < a k := by linarith [hak.1]
    have hb0 : 0 ≤ aT / (L : ℝ) ^ 2 := by positivity
    have hnest1 : ∀ y y' : Torus d (N₀ * L ^ (k + 1)), y' ∈ G.blk k y → y' ∈ G.blk (k + 1) y := by
      intro y y' h
      rw [GeneratingSet.mem_blk] at h ⊢
      exact GeneratingSet.jBlock_succ_eq (by omega) h
    refine ⟨k, k + 1, by omega, le_rfl, hnest1, fun y y' h => h, fun y hy => ?_⟩
    rw [commK_xOperator_split]
    have hl := lap_weighted G hφ s hj1 hjK y hy (r := r) (ε := ε)
    have hb := blockPart_top G (xS1_nonneg hak0 hx) (xS12_sub_nonneg hak0 hb0 hx)
      ((xS2_le hak0 hb0 hx).trans hak.2) a hφ hδ s hr hε0 y hy
    have hw0 : 0 < Real.exp (ε * r y) := Real.exp_pos _
    calc (L : ℝ) ^ (k + 1) * Real.exp (ε * r y) * ‖_ + _‖
        ≤ (L : ℝ) ^ (k + 1) * Real.exp (ε * r y) * (‖lapTerm G φ s y‖ + ‖_‖) :=
          mul_le_mul_of_nonneg_left (norm_add_le _ _) (by positivity)
      _ ≤ _ := by rw [mul_add]; linarith
  · refine ⟨j, j, by omega, by omega, fun y y' h => h, fun y y' h => h, fun y hy => ?_⟩
    rw [commK_xOperator_split]
    have hl := lap_weighted G hφ s hj1 hjK y hy (r := r) (ε := ε)
    have hb := blockPart_low G ha (xS1 (a k) x) (xS2 (a k) (aT / (L : ℝ) ^ 2) x) hφ hδ s hr hε0
      hj1 hjk y hy
    have hw0 : 0 < Real.exp (ε * r y) := Real.exp_pos _
    calc (L : ℝ) ^ j * Real.exp (ε * r y) * ‖_ + _‖
        ≤ (L : ℝ) ^ j * Real.exp (ε * r y) * (‖lapTerm G φ s y‖ + ‖_‖) :=
          mul_le_mul_of_nonneg_left (norm_add_le _ _) (by positivity)
      _ ≤ _ := by rw [mul_add]; linarith

/-- **The weighted pointwise bound for the commutator of the x-variant** (uniform in `x ≥ 0`) at a
point `y` of layer `j`: Laplacian part plus the block part with `m₁`-, `m₂`-block averages of
`w |s̃|` (`m`-blocks inside the `j`-block). -/
theorem commKx_pointwise (hk : 1 ≤ k) {a : ℕ → ℝ} (ha : IsAdmissibleWeights k a) {aT x ν : ℝ}
    (haT1 : 1 / 2 ≤ aT) (hx : 0 ≤ x) (α : G.Ω 1 → ℂ) {δ : ℝ}
    {φ : Torus d (N₀ * L ^ (k + 1)) → Fin N → ℂ} (hφ : IsSmoothField G δ φ) (hδ : 0 ≤ δ)
    {r : Torus d (N₀ * L ^ (k + 1)) → ℝ} (hr : IsAgmonWeight G r) {ε : ℝ} (hε0 : 0 ≤ ε)
    (s : G.Ω 1 × Fin N → ℂ) {j : ℕ} (hj1 : 1 ≤ j) (hjK : j ≤ k + 1) :
    ∃ m₁ m₂ : ℕ, m₁ ≤ k + 1 ∧ m₂ ≤ k + 1 ∧
      (∀ y y' : Torus d (N₀ * L ^ (k + 1)), y' ∈ G.blk m₁ y → y' ∈ G.blk j y) ∧
      (∀ y y' : Torus d (N₀ * L ^ (k + 1)), y' ∈ G.blk m₂ y → y' ∈ G.blk j y) ∧
      ∀ y : G.Ω 1, (y : Torus d (N₀ * L ^ (k + 1))) ∈ G.layer j →
        (L : ℝ) ^ j * Real.exp (ε * r y) *
            ‖(commK (xDirichletOperator G a aT x ν α) (restrictField G φ) *ᵥ s) y‖ ≤
          δ * Real.exp (ε * r y) * ∑ μ : Fin d,
              (vn (svec G s ((y : Torus d (N₀ * L ^ (k + 1))) + Pi.single μ 1) - svec G s y) +
                vn (svec G s ((y : Torus d (N₀ * L ^ (k + 1))) - Pi.single μ 1) - svec G s y)) +
            δ * ((L : ℝ) ^ j)⁻¹ * (Real.exp (ε * r y) * vn (svec G s y)) +
            4 * d * (L : ℝ) ^ 2 * δ * Real.exp (ε * (2 * d)) * ((L : ℝ) ^ j)⁻¹ *
              (blkAvg G m₁ (fun z => Real.exp (ε * r z) * vn (svec G s z)) y +
                blkAvg G m₂ (fun z => Real.exp (ε * r z) * vn (svec G s z)) y) :=
  commKx_pointwise_of_ak G ha (ha k hk le_rfl) haT1 hx α hφ hδ hr hε0 s hj1 hjK

end Weighted

/-! ### The `L²` bound -/

section Sum

/-- The weighted gradient `‖w ∂ s‖²` (two-sided, vector valued) charged on the points of `Λ`. -/
noncomputable def vecGradOn {K : ℕ} (G : GeneratingSet d L N₀ K ϱ) (ε : ℝ)
    (r : Torus d (N₀ * L ^ K) → ℝ) (Λ : Finset (Torus d (N₀ * L ^ K)))
    (s : G.Ω 1 × Fin N → ℂ) : ℝ :=
  ∑ x ∈ G.Ω 1, if x ∈ Λ then Real.exp (ε * r x) ^ 2 * ∑ μ : Fin d,
    (vn (svec G s (x + Pi.single μ 1) - svec G s x) ^ 2 +
      vn (svec G s (x - Pi.single μ 1) - svec G s x) ^ 2) else 0

theorem vecGradOn_nonneg {K : ℕ} (G : GeneratingSet d L N₀ K ϱ) (ε : ℝ)
    (r : Torus d (N₀ * L ^ K) → ℝ) (Λ : Finset (Torus d (N₀ * L ^ K))) (s : G.Ω 1 × Fin N → ℂ) :
    0 ≤ vecGradOn G ε r Λ s :=
  Finset.sum_nonneg fun x _ => by
    split_ifs
    · exact mul_nonneg (sq_nonneg _) (Finset.sum_nonneg fun μ _ => by positivity)
    · exact le_rfl

/-- The constant of the `L²` commutator bound (depends on `d` and `L` only). -/
noncomputable def commXConst (d L : ℕ) : ℝ :=
  3 * (2 * d + 1 + 128 * (d : ℝ) ^ 2 * (L : ℝ) ^ 4)

theorem commXConst_nonneg (d L : ℕ) : 0 ≤ commXConst d L := by
  unfold commXConst; positivity

/-- The squared form of the pointwise bound (real numbers). -/
theorem sq_assemble {δ w ℓ v Cb A₁ A₂ P : ℝ} (p q : Fin d → ℝ) (hδ : 0 ≤ δ) (hw : 0 ≤ w)
    (hℓ : 0 < ℓ) (hv : 0 ≤ v) (hCb : 0 ≤ Cb) (hA₁ : 0 ≤ A₁) (hA₂ : 0 ≤ A₂) (hp : ∀ μ, 0 ≤ p μ)
    (hq : ∀ μ, 0 ≤ q μ) (hP0 : 0 ≤ P)
    (hP : P ≤ δ * w * ∑ μ, (p μ + q μ) + δ * ℓ⁻¹ * (w * v) + Cb * δ * ℓ⁻¹ * (A₁ + A₂)) :
    P ^ 2 ≤ 3 * (2 * d * δ ^ 2 * (w ^ 2 * ∑ μ, (p μ ^ 2 + q μ ^ 2)) +
      δ ^ 2 * (ℓ ^ 2)⁻¹ * (w * v) ^ 2 + 2 * Cb ^ 2 * δ ^ 2 * (ℓ ^ 2)⁻¹ * (A₁ ^ 2 + A₂ ^ 2)) := by
  set t1 := δ * w * ∑ μ, (p μ + q μ) with ht1
  set t2 := δ * ℓ⁻¹ * (w * v) with ht2
  set t3 := Cb * δ * ℓ⁻¹ * (A₁ + A₂) with ht3
  have ht10 : 0 ≤ t1 := by
    rw [ht1]; exact mul_nonneg (mul_nonneg hδ hw) (Finset.sum_nonneg fun μ _ => add_nonneg (hp μ) (hq μ))
  have ht20 : 0 ≤ t2 := by rw [ht2]; positivity
  have ht30 : 0 ≤ t3 := by rw [ht3]; positivity
  have h1' := pow_le_pow_left₀ hP0 hP 2
  refine h1'.trans ((three_sq_le t1 t2 t3).trans ?_)
  have e1 : t1 ^ 2 ≤ 2 * d * δ ^ 2 * (w ^ 2 * ∑ μ, (p μ ^ 2 + q μ ^ 2)) := by
    have := sq_sum_pair_le d p q
    calc t1 ^ 2 = (δ * w) ^ 2 * (∑ μ, (p μ + q μ)) ^ 2 := by rw [ht1]; ring
      _ ≤ (δ * w) ^ 2 * (2 * d * ∑ μ, (p μ ^ 2 + q μ ^ 2)) :=
          mul_le_mul_of_nonneg_left this (sq_nonneg _)
      _ = _ := by ring
  have e2 : t2 ^ 2 = δ ^ 2 * (ℓ ^ 2)⁻¹ * (w * v) ^ 2 := by
    rw [ht2]; simp only [mul_pow, inv_pow]
  have e3 : t3 ^ 2 ≤ 2 * Cb ^ 2 * δ ^ 2 * (ℓ ^ 2)⁻¹ * (A₁ ^ 2 + A₂ ^ 2) := by
    rw [ht3]
    calc (Cb * δ * ℓ⁻¹ * (A₁ + A₂)) ^ 2 = Cb ^ 2 * δ ^ 2 * (ℓ ^ 2)⁻¹ * (A₁ + A₂) ^ 2 := by
          simp only [mul_pow, inv_pow]
      _ ≤ Cb ^ 2 * δ ^ 2 * (ℓ ^ 2)⁻¹ * (2 * (A₁ ^ 2 + A₂ ^ 2)) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          nlinarith [sq_nonneg (A₁ - A₂)]
      _ = _ := by ring
  linarith

/-- The sum over a layer of the pointwise bounds. -/
theorem layer_sum_assemble {ι : Type*} (S : Finset ι) {δ ℓ Cb d' : ℝ} (hℓ : 0 < ℓ)
    (F Gp W B₁ B₂ : ι → ℝ)
    (hpt : ∀ y ∈ S, F y ≤ 3 * (2 * d' * δ ^ 2 * Gp y + δ ^ 2 * (ℓ ^ 2)⁻¹ * W y ^ 2 +
      2 * Cb ^ 2 * δ ^ 2 * (ℓ ^ 2)⁻¹ * (B₁ y ^ 2 + B₂ y ^ 2)))
    (hc₁ : ∑ y ∈ S, B₁ y ^ 2 ≤ ∑ y ∈ S, W y ^ 2) (hc₂ : ∑ y ∈ S, B₂ y ^ 2 ≤ ∑ y ∈ S, W y ^ 2) :
    ∑ y ∈ S, F y ≤ 3 * (2 * d' * δ ^ 2 * ∑ y ∈ S, Gp y +
      (1 + 4 * Cb ^ 2) * δ ^ 2 * ((ℓ ^ 2)⁻¹ * ∑ y ∈ S, W y ^ 2)) := by
  calc ∑ y ∈ S, F y ≤ ∑ y ∈ S, 3 * (2 * d' * δ ^ 2 * Gp y + δ ^ 2 * (ℓ ^ 2)⁻¹ * W y ^ 2 +
        2 * Cb ^ 2 * δ ^ 2 * (ℓ ^ 2)⁻¹ * (B₁ y ^ 2 + B₂ y ^ 2)) := Finset.sum_le_sum hpt
    _ = 3 * (2 * d' * δ ^ 2 * ∑ y ∈ S, Gp y + δ ^ 2 * (ℓ ^ 2)⁻¹ * ∑ y ∈ S, W y ^ 2 +
        2 * Cb ^ 2 * δ ^ 2 * (ℓ ^ 2)⁻¹ * (∑ y ∈ S, B₁ y ^ 2 + ∑ y ∈ S, B₂ y ^ 2)) := by
        simp only [← Finset.mul_sum, Finset.sum_add_distrib]
    _ ≤ _ := by
        have hi : 0 ≤ (ℓ ^ 2)⁻¹ := by positivity
        have hm : 2 * Cb ^ 2 * δ ^ 2 * (ℓ ^ 2)⁻¹ * (∑ y ∈ S, B₁ y ^ 2 + ∑ y ∈ S, B₂ y ^ 2) ≤
            2 * Cb ^ 2 * δ ^ 2 * (ℓ ^ 2)⁻¹ * (2 * ∑ y ∈ S, W y ^ 2) :=
          mul_le_mul_of_nonneg_left (by linarith) (by positivity)
        nlinarith [hm]

variable {k : ℕ} (G : GeneratingSet d L N₀ (k + 1) ϱ)

/-- Core of `agmonSource_commKx_le` with `1 ≤ k` replaced by the lower bound `1/2 ≤ a_k` (the only use of `k ≥ 1`); the weights `a_j`, `1 ≤ j ≤ k`, stay in `[1/2, 2]`. -/
theorem agmonSource_commKx_le_of_ak (hd : 0 < d) {a : ℕ → ℝ} (ha : IsAdmissibleWeights k a)
    (hak : 1 / 2 ≤ a k ∧ a k ≤ 2)
    {aT x ν : ℝ} (haT1 : 1 / 2 ≤ aT) (hx : 0 ≤ x) (α : G.Ω 1 → ℂ) {δ : ℝ}
    {φ : Torus d (N₀ * L ^ (k + 1)) → Fin N → ℂ} (hφ : IsSmoothField G δ φ) (hδ : 0 ≤ δ)
    {r : Torus d (N₀ * L ^ (k + 1)) → ℝ} (hr : IsAgmonWeight G r) {ε : ℝ} (hε0 : 0 ≤ ε)
    (hε1 : ε ≤ agmonRate d) (s : G.Ω 1 × Fin N → ℂ)
    (Λ : Finset (Torus d (N₀ * L ^ (k + 1))))
    (hΛ : ∀ y : G.Ω 1, (y : Torus d (N₀ * L ^ (k + 1))) ∉ Λ →
      (commK (xDirichletOperator G a aT x ν α) (restrictField G φ) *ᵥ s) y = 0) :
    agmonSource G ε r (commK (xDirichletOperator G a aT x ν α) (restrictField G φ) *ᵥ s) ≤
      commXConst d L * δ ^ 2 * (vecGradOn G ε r Λ s + vecM G ε r s) := by
  have hL : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hdd : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hE := exp_two_d_sq_le hd hε0 hε1
  set Kf := commK (xDirichletOperator G a aT x ν α) (restrictField G φ) *ᵥ s with hKf
  set F : Torus d (N₀ * L ^ (k + 1)) → ℝ := fun y => G.spacing y ^ 2 *
    ‖((Real.exp (ε * r y) : ℝ) : ℂ) * zeroExt (G.Ω 1) Kf y‖ ^ 2 with hF
  have hF0 : ∀ y ∈ (Finset.univ : Finset (Torus d (N₀ * L ^ (k + 1)))), y ∉ G.Ω 1 → F y = 0 := by
    intro y _ hy
    simp [hF, zeroExt_not_mem _ _ hy]
  have h1 : agmonSource G ε r Kf = ∑ j ∈ Finset.Icc 1 (k + 1), ∑ y ∈ G.layer j, F y := by
    rw [← sum_Ω_layers G F]
    unfold agmonSource
    exact (Finset.sum_subset (Finset.subset_univ _) hF0).symm
  set W : Torus d (N₀ * L ^ (k + 1)) → ℝ := fun z => Real.exp (ε * r z) * vn (svec G s z)
    with hW
  set Cb : ℝ := 4 * d * (L : ℝ) ^ 2 * Real.exp (ε * (2 * d)) with hCb
  set Gp : Torus d (N₀ * L ^ (k + 1)) → ℝ := fun y =>
    if y ∈ Λ then Real.exp (ε * r y) ^ 2 * ∑ μ : Fin d,
      (vn (svec G s (y + Pi.single μ 1) - svec G s y) ^ 2 +
        vn (svec G s (y - Pi.single μ 1) - svec G s y) ^ 2) else 0 with hGp
  have hGp0 : ∀ y, 0 ≤ Gp y := fun y => by
    simp only [hGp]
    split_ifs
    · exact mul_nonneg (sq_nonneg _) (Finset.sum_nonneg fun μ _ => by positivity)
    · exact le_rfl
  have hCb2 : Cb ^ 2 ≤ 32 * (d : ℝ) ^ 2 * (L : ℝ) ^ 4 := by
    have : Cb ^ 2 = 16 * (d : ℝ) ^ 2 * (L : ℝ) ^ 4 * Real.exp (ε * (2 * d)) ^ 2 := by
      rw [hCb]; ring
    rw [this]
    nlinarith [mul_le_mul_of_nonneg_left hE (by positivity : (0 : ℝ) ≤ 16 * (d : ℝ) ^ 2 * (L : ℝ) ^ 4)]
  have hCb0 : 0 ≤ Cb := by rw [hCb]; positivity
  -- per layer
  have h2 : ∀ j ∈ Finset.Icc 1 (k + 1), ∑ y ∈ G.layer j, F y ≤
      3 * (2 * d * δ ^ 2 * ∑ y ∈ G.layer j, Gp y +
        (1 + 4 * Cb ^ 2) * δ ^ 2 * ((((L : ℝ) ^ j) ^ 2)⁻¹ * ∑ y ∈ G.layer j, W y ^ 2)) := by
    intro j hj
    have hj1 := (Finset.mem_Icc.1 hj).1
    have hjK := (Finset.mem_Icc.1 hj).2
    obtain ⟨m₁, m₂, hm₁, hm₂, hn₁, hn₂, hpt⟩ :=
      commKx_pointwise_of_ak G ha hak haT1 hx (ν := ν) α hφ hδ hr hε0 s hj1 hjK
    have hsat₁ : ∀ y y' : Torus d (N₀ * L ^ (k + 1)), y ∈ G.layer j → y' ∈ G.blk m₁ y →
        y' ∈ G.layer j := fun y y' hy hy' =>
      (G.mem_layer_iff hj1 hjK (GeneratingSet.mem_blk.1 (hn₁ y y' hy')).symm).1 hy
    have hsat₂ : ∀ y y' : Torus d (N₀ * L ^ (k + 1)), y ∈ G.layer j → y' ∈ G.blk m₂ y →
        y' ∈ G.layer j := fun y y' hy hy' =>
      (G.mem_layer_iff hj1 hjK (GeneratingSet.mem_blk.1 (hn₂ y y' hy')).symm).1 hy
    have hc₁ := layer_blkAvg_sq_le G hm₁ hsat₁ W
    have hc₂ := layer_blkAvg_sq_le G hm₂ hsat₂ W
    have hLj : (0 : ℝ) < (L : ℝ) ^ j := by positivity
    refine layer_sum_assemble (G.layer j) hLj F Gp W (blkAvg G m₁ W)
      (blkAvg G m₂ W) (fun y hy => ?_) hc₁ hc₂
    have hyΩ : y ∈ G.Ω 1 := G.layer_subset hj1 hjK hy
    set y' : G.Ω 1 := ⟨y, hyΩ⟩ with hy'
    have hsp : G.spacing y = (L : ℝ) ^ j := G.spacing_eq hj1 hjK hy
    have e : F y = ((L : ℝ) ^ j * Real.exp (ε * r y) * ‖Kf y'‖) ^ 2 := by
      have : zeroExt (G.Ω 1) Kf y = Kf y' := zeroExt_mem (G.Ω 1) _ y'
      simp only [hF, this, norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le,
        hsp]
      ring
    have hA₁ : 0 ≤ blkAvg G m₁ W y :=
      blkAvg_nonneg G m₁ (fun z => mul_nonneg (Real.exp_pos _).le (vn_nonneg _)) y
    have hA₂ : 0 ≤ blkAvg G m₂ W y :=
      blkAvg_nonneg G m₂ (fun z => mul_nonneg (Real.exp_pos _).le (vn_nonneg _)) y
    by_cases hyΛ : y ∈ Λ
    · rw [e]
      have h := hpt y' hy
      have hGpy : Gp y = Real.exp (ε * r y) ^ 2 * ∑ μ : Fin d,
          (vn (svec G s (y + Pi.single μ 1) - svec G s y) ^ 2 +
            vn (svec G s (y - Pi.single μ 1) - svec G s y) ^ 2) := by
        simp only [hGp, hyΛ, ↓reduceIte]
      rw [hGpy]
      have := sq_assemble (d := d) (δ := δ) (w := Real.exp (ε * r y)) (ℓ := (L : ℝ) ^ j)
        (v := vn (svec G s y)) (Cb := Cb) (A₁ := blkAvg G m₁ W y) (A₂ := blkAvg G m₂ W y)
        (P := (L : ℝ) ^ j * Real.exp (ε * r y) * ‖Kf y'‖)
        (fun μ => vn (svec G s (y + Pi.single μ 1) - svec G s y))
        (fun μ => vn (svec G s (y - Pi.single μ 1) - svec G s y)) hδ (Real.exp_pos _).le hLj
        (vn_nonneg _) hCb0 hA₁ hA₂ (fun μ => vn_nonneg _) (fun μ => vn_nonneg _)
        (by positivity) (by
          have e3 : Cb * δ * ((L : ℝ) ^ j)⁻¹ * (blkAvg G m₁ W y + blkAvg G m₂ W y) =
              4 * d * (L : ℝ) ^ 2 * δ * Real.exp (ε * (2 * d)) * ((L : ℝ) ^ j)⁻¹ *
                (blkAvg G m₁ W y + blkAvg G m₂ W y) := by rw [hCb]; ring
          rw [e3]; exact h)
      exact this
    · rw [hΛ y' hyΛ] at e
      simp only [norm_zero, mul_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
        zero_pow] at e
      rw [e]
      have := hGp0 y
      positivity
  rw [h1]
  refine (Finset.sum_le_sum h2).trans ?_
  have hGv : vecGradOn G ε r Λ s = ∑ j ∈ Finset.Icc 1 (k + 1), ∑ y ∈ G.layer j, Gp y := by
    rw [← sum_Ω_layers G Gp]; rfl
  have hMv : vecM G ε r s = ∑ j ∈ Finset.Icc 1 (k + 1), (((L : ℝ) ^ j) ^ 2)⁻¹ *
      ∑ y ∈ G.layer j, W y ^ 2 := wsq_eq_layers G W
  rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← hGv]
  have hM0 := vecM_nonneg G ε r s
  have hG0 := vecGradOn_nonneg G ε r Λ s
  rw [← hMv]
  have hδ2 : 0 ≤ δ ^ 2 := sq_nonneg δ
  unfold commXConst
  have hC1 : 1 + 4 * Cb ^ 2 ≤ 1 + 128 * (d : ℝ) ^ 2 * (L : ℝ) ^ 4 := by nlinarith
  have hdd2 : (0 : ℝ) ≤ 128 * (d : ℝ) ^ 2 * (L : ℝ) ^ 4 := by positivity
  nlinarith [mul_nonneg hδ2 hG0, mul_nonneg hδ2 hM0,
    mul_le_mul_of_nonneg_right hC1 (mul_nonneg hδ2 hM0),
    mul_nonneg (mul_nonneg hδ2 hG0) hdd2, mul_nonneg (mul_nonneg hδ2 hM0) hdd2]

/-- **The `L²` bound for the commutator of the x-variant with a smooth field** (uniform in
`x ≥ 0`): `‖ℓ w K_x(φ) s‖² ≤ C δ² (‖w ∂ s‖²_Λ + ‖ℓ⁻¹ w s‖²)` when `K_x(φ) s` vanishes off `Λ`. -/
theorem agmonSource_commKx_le (hd : 0 < d) (hk : 1 ≤ k) {a : ℕ → ℝ} (ha : IsAdmissibleWeights k a)
    {aT x ν : ℝ} (haT1 : 1 / 2 ≤ aT) (hx : 0 ≤ x) (α : G.Ω 1 → ℂ) {δ : ℝ}
    {φ : Torus d (N₀ * L ^ (k + 1)) → Fin N → ℂ} (hφ : IsSmoothField G δ φ) (hδ : 0 ≤ δ)
    {r : Torus d (N₀ * L ^ (k + 1)) → ℝ} (hr : IsAgmonWeight G r) {ε : ℝ} (hε0 : 0 ≤ ε)
    (hε1 : ε ≤ agmonRate d) (s : G.Ω 1 × Fin N → ℂ)
    (Λ : Finset (Torus d (N₀ * L ^ (k + 1))))
    (hΛ : ∀ y : G.Ω 1, (y : Torus d (N₀ * L ^ (k + 1))) ∉ Λ →
      (commK (xDirichletOperator G a aT x ν α) (restrictField G φ) *ᵥ s) y = 0) :
    agmonSource G ε r (commK (xDirichletOperator G a aT x ν α) (restrictField G φ) *ᵥ s) ≤
      commXConst d L * δ ^ 2 * (vecGradOn G ε r Λ s + vecM G ε r s) :=
  agmonSource_commKx_le_of_ak G hd ha (ha k hk le_rfl) haT1 hx α hφ hδ hr hε0 hε1 s Λ hΛ

end Sum

end Balaban.Multiscale
