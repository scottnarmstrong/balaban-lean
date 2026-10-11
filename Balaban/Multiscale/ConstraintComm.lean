/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Multiscale.ConstraintField
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The commutator `K(φ₀)` of `H_D(α)` with the multiplication by `φ₀`: explicit form

GREEN.md §4.5a: `K(φ₀) s = φ₀ H s - H (φ₀ s) = 2 ∇φ₀·∇s + (Δφ₀) s - [Q* a Q, φ₀] s`.  The matrix
`Balaban.Multiscale.commK H φ` is *defined* as the commutator; here its entries are computed for
`H = H_D(α)`: the diagonal terms (mass, `α`) cancel and, for `x ∈ Ω₁`,

`(K(φ₀) s)(x) = Lap part + block part` with
* `Lap part = ∑_μ ∑_i [(φ₀ᵢ(x+e_μ) - φ₀ᵢ(x))(s̃ᵢ(x+e_μ) - sᵢ(x)) + (backward)] + ∑_i sᵢ(x) (Δφ₀ᵢ)(x)`
  (`Balaban.Multiscale.lapPart`),
* `block part = (a_j ℓ_j⁻²) ⨍_{B_j(x)} ∑_i (φ₀ᵢ(x) - φ₀ᵢ(y)) s̃ᵢ(y) dy` (`Balaban.Multiscale.blockPart`).
-/

@[expose] public section

namespace Balaban.Multiscale

open Matrix Finset

variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}

section Formula

variable (G : GeneratingSet d L N₀ k ϱ)

/-- The restriction of a torus field to `Ω₁`. -/
def restrictField (φ : Torus d (N₀ * L ^ k) → Fin N → ℂ) : G.Ω 1 → Fin N → ℂ := fun x => φ x

/-- The vector `s̃(y) ∈ ℂ^N` of zero extensions of the components of `s : Ω₁ × Fin N → ℂ`. -/
noncomputable def svec (s : G.Ω 1 × Fin N → ℂ) (y : Torus d (N₀ * L ^ k)) : Fin N → ℂ :=
  fun i => zeroExt (G.Ω 1) (fun z => s (z, i)) y

/-- The argument `T_x(y) = ∑ᵢ (φ₀ᵢ(x) - φ₀ᵢ(y)) s̃ᵢ(y)` of the commutator at `x`. -/
noncomputable def commArg (φ : Torus d (N₀ * L ^ k) → Fin N → ℂ) (s : G.Ω 1 × Fin N → ℂ)
    (x : Torus d (N₀ * L ^ k)) (y : Torus d (N₀ * L ^ k)) : ℂ :=
  ∑ i, (φ x i - φ y i) * svec G s y i

theorem svec_of_mem (s : G.Ω 1 × Fin N → ℂ) (y : G.Ω 1) (i : Fin N) :
    svec G s y i = s (y, i) := by
  simp [svec, zeroExt_mem]

theorem svec_of_not_mem (s : G.Ω 1 × Fin N → ℂ) {y : Torus d (N₀ * L ^ k)} (hy : y ∉ G.Ω 1)
    (i : Fin N) : svec G s y i = 0 := by
  simp [svec, zeroExt_not_mem _ _ hy]

theorem commArg_self (φ : Torus d (N₀ * L ^ k) → Fin N → ℂ) (s : G.Ω 1 × Fin N → ℂ)
    (x : Torus d (N₀ * L ^ k)) : commArg G φ s x x = 0 := by
  simp [commArg]

theorem commArg_of_not_mem (φ : Torus d (N₀ * L ^ k) → Fin N → ℂ) (s : G.Ω 1 × Fin N → ℂ)
    (x : Torus d (N₀ * L ^ k)) {y : Torus d (N₀ * L ^ k)} (hy : y ∉ G.Ω 1) :
    commArg G φ s x y = 0 := by
  simp [commArg, svec_of_not_mem G s hy]

/-- The commutator for the Dirichlet operator is the full torus operator applied to the commutator
argument (the diagonal terms cancel). -/
theorem commK_dirichlet (a : ℕ → ℝ) (ν : ℝ) (α : G.Ω 1 → ℂ)
    (φ : Torus d (N₀ * L ^ k) → Fin N → ℂ) (s : G.Ω 1 × Fin N → ℂ) (x : G.Ω 1) :
    (commK (dirichletOperator G a ν α) (restrictField G φ) *ᵥ s) x =
      ((fullMatrix G a ν).map (algebraMap ℝ ℂ) *ᵥ commArg G φ s x) x := by
  rw [commK_mulVec]
  have hy : ∀ y : G.Ω 1, ∑ i, (restrictField G φ x i - restrictField G φ y i) * s (y, i) =
      commArg G φ s x y := by
    intro y
    simp only [commArg, restrictField]
    exact Finset.sum_congr rfl fun i _ => by rw [svec_of_mem]
  have h1 : ∀ y : G.Ω 1, ∑ i, dirichletOperator G a ν α x y *
      (restrictField G φ x i - restrictField G φ y i) * s (y, i) =
      dirichletOperator G a ν α x y * commArg G φ s x y := by
    intro y
    rw [← hy y, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  simp only [h1]
  unfold dirichletOperator
  simp only [Matrix.add_apply, add_mul, Finset.sum_add_distrib, Green.restrictOp,
    Matrix.submatrix_apply, Matrix.diagonal_apply, ite_mul, zero_mul]
  rw [Finset.sum_ite_eq]
  simp only [Finset.mem_univ, ↓reduceIte]
  have hxx : commArg G φ s x x = 0 := commArg_self G φ s x
  rw [hxx, mul_zero, add_zero]
  simp only [Matrix.mulVec, dotProduct]
  exact (Green.sum_eq_sum_subtype (G.Ω 1) (fun y => (fullMatrix G a ν).map (algebraMap ℝ ℂ) x y *
    commArg G φ s x y) (fun i hi => by rw [commArg_of_not_mem G φ s x hi, mul_zero])).symm

end Formula

/-! ### The Laplacian part -/

section Lap

omit [NeZero N₀] [NeZero L] in
theorem lap_mulVec_complex {ℓ : ℕ} [NeZero ℓ] (ν : ℝ) (ψ : Torus d ℓ → ℂ) (x : Torus d ℓ) :
    ((latticeLaplacian d ℓ ν).map (algebraMap ℝ ℂ) *ᵥ ψ) x =
      ∑ μ : Fin d, (2 * ψ x - ψ (x + Pi.single μ 1) - ψ (x - Pi.single μ 1)) + ν * ψ x := by
  apply Complex.ext
  · rw [re_mulVec_map, latticeLaplacian_mulVec]
    simp [Complex.re_sum]
  · rw [im_mulVec_map, latticeLaplacian_mulVec]
    simp [Complex.im_sum]

variable (G : GeneratingSet d L N₀ k ϱ)

/-- The Laplacian part of `(K(φ₀) s)(x)` (for `x ∈ Ω₁`). -/
noncomputable def lapTerm (φ : Torus d (N₀ * L ^ k) → Fin N → ℂ) (s : G.Ω 1 × Fin N → ℂ)
    (x : Torus d (N₀ * L ^ k)) : ℂ :=
  ∑ μ : Fin d, ∑ i, ((φ (x + Pi.single μ 1) i - φ x i) *
        (svec G s (x + Pi.single μ 1) i - svec G s x i) +
      (φ (x - Pi.single μ 1) i - φ x i) * (svec G s (x - Pi.single μ 1) i - svec G s x i) +
      svec G s x i * (φ (x + Pi.single μ 1) i + φ (x - Pi.single μ 1) i - 2 * φ x i))

theorem lap_part_eq (ν : ℝ) (φ : Torus d (N₀ * L ^ k) → Fin N → ℂ) (s : G.Ω 1 × Fin N → ℂ)
    (x : Torus d (N₀ * L ^ k)) :
    ((latticeLaplacian d (N₀ * L ^ k) ν).map (algebraMap ℝ ℂ) *ᵥ commArg G φ s x) x =
      lapTerm G φ s x := by
  rw [lap_mulVec_complex, commArg_self, mul_zero, mul_zero, add_zero]
  unfold lapTerm
  refine Finset.sum_congr rfl fun μ _ => ?_
  simp only [commArg]
  have hc : ∀ i : Fin N, ((φ (x + Pi.single μ 1) i - φ x i) *
        (svec G s (x + Pi.single μ 1) i - svec G s x i) +
      (φ (x - Pi.single μ 1) i - φ x i) * (svec G s (x - Pi.single μ 1) i - svec G s x i) +
      svec G s x i * (φ (x + Pi.single μ 1) i + φ (x - Pi.single μ 1) i - 2 * φ x i)) =
      -((φ x i - φ (x + Pi.single μ 1) i) * svec G s (x + Pi.single μ 1) i) -
        (φ x i - φ (x - Pi.single μ 1) i) * svec G s (x - Pi.single μ 1) i :=
    fun i => by ring
  rw [Finset.sum_congr rfl fun i _ => hc i, Finset.sum_sub_distrib, Finset.sum_neg_distrib]
  ring

theorem lapTerm_norm_le {δ : ℝ} {φ : Torus d (N₀ * L ^ k) → Fin N → ℂ}
    (hφ : IsSmoothField G δ φ) (s : G.Ω 1 × Fin N → ℂ)
    {x : Torus d (N₀ * L ^ k)} (hx : x ∈ G.Ω 1) :
    ‖lapTerm G φ s x‖ ≤ δ / G.spacing x *
      ∑ μ : Fin d, (vn (svec G s (x + Pi.single μ 1) - svec G s x) +
        vn (svec G s (x - Pi.single μ 1) - svec G s x)) +
      δ / G.spacing x ^ 2 * vn (svec G s x) := by
  set A : Fin d → Fin N → ℂ := fun μ i => (φ (x + Pi.single μ 1) i - φ x i) *
    (svec G s (x + Pi.single μ 1) i - svec G s x i) with hA
  set B : Fin d → Fin N → ℂ := fun μ i => (φ (x - Pi.single μ 1) i - φ x i) *
    (svec G s (x - Pi.single μ 1) i - svec G s x i) with hB
  have hsplit : lapTerm G φ s x = ∑ μ, ∑ i, A μ i + ∑ μ, ∑ i, B μ i +
      ∑ i, svec G s x i * ∑ μ : Fin d, (φ (x + Pi.single μ 1) i + φ (x - Pi.single μ 1) i -
        2 * φ x i) := by
    unfold lapTerm
    simp only [Finset.sum_add_distrib, hA, hB]
    congr 1
    simp only [Finset.mul_sum]
    exact Finset.sum_comm
  have hℓ : 0 < G.spacing x := spacing_pos G
  have h1 : ‖∑ μ, ∑ i, A μ i‖ ≤ δ / G.spacing x * ∑ μ : Fin d,
      vn (svec G s (x + Pi.single μ 1) - svec G s x) := by
    refine (norm_sum_le _ _).trans ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun μ _ => ?_
    refine (norm_dot_le (φ (x + Pi.single μ 1) - φ x)
      (svec G s (x + Pi.single μ 1) - svec G s x)).trans ?_
    exact mul_le_mul_of_nonneg_right (hφ.grad x hx μ).1 (vn_nonneg _)
  have h2 : ‖∑ μ, ∑ i, B μ i‖ ≤ δ / G.spacing x * ∑ μ : Fin d,
      vn (svec G s (x - Pi.single μ 1) - svec G s x) := by
    refine (norm_sum_le _ _).trans ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun μ _ => ?_
    refine (norm_dot_le (φ (x - Pi.single μ 1) - φ x)
      (svec G s (x - Pi.single μ 1) - svec G s x)).trans ?_
    exact mul_le_mul_of_nonneg_right (hφ.grad x hx μ).2 (vn_nonneg _)
  have h3 : ‖∑ i, svec G s x i * ∑ μ : Fin d, (φ (x + Pi.single μ 1) i +
      φ (x - Pi.single μ 1) i - 2 * φ x i)‖ ≤ δ / G.spacing x ^ 2 * vn (svec G s x) := by
    refine (norm_dot_le (svec G s x) (fun i => ∑ μ : Fin d, (φ (x + Pi.single μ 1) i +
      φ (x - Pi.single μ 1) i - 2 * φ x i))).trans ?_
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_right (hφ.lap x hx) (vn_nonneg _)
  rw [hsplit]
  refine (norm_add₃_le).trans ?_
  have e : δ / G.spacing x * ∑ μ : Fin d, (vn (svec G s (x + Pi.single μ 1) - svec G s x) +
        vn (svec G s (x - Pi.single μ 1) - svec G s x)) =
      δ / G.spacing x * ∑ μ : Fin d, vn (svec G s (x + Pi.single μ 1) - svec G s x) +
      δ / G.spacing x * ∑ μ : Fin d, vn (svec G s (x - Pi.single μ 1) - svec G s x) := by
    rw [Finset.sum_add_distrib, mul_add]
  rw [e]
  linarith

end Lap

/-! ### The block part -/

section Block

variable (G : GeneratingSet d L N₀ k ϱ)

theorem avgMatrix_apply_of_layer (a : ℕ → ℝ) {j : ℕ} (hj1 : 1 ≤ j) (hjk : j ≤ k)
    {x : Torus d (N₀ * L ^ k)} (hx : x ∈ G.layer j) (y : Torus d (N₀ * L ^ k)) :
    avgMatrix G a x y = a j / ((L : ℝ) ^ j) ^ 2 * layerProjMatrix G j x y := by
  unfold avgMatrix
  rw [Matrix.sum_apply, Finset.sum_eq_single j]
  · simp
  · intro j' hj' hne
    have hx' : x ∉ G.layer j' := G.layer_disjoint hj1 hjk (Finset.mem_Icc.1 hj').1
      (Finset.mem_Icc.1 hj').2 (Ne.symm hne) hx
    simp [layerProjMatrix, hx']
  · intro h
    exact absurd (Finset.mem_Icc.2 ⟨hj1, hjk⟩) h

theorem layerProjMatrix_apply_of_layer {j : ℕ} (hj1 : 1 ≤ j) (hjk : j ≤ k)
    {x : Torus d (N₀ * L ^ k)} (hx : x ∈ G.layer j) (y : Torus d (N₀ * L ^ k)) :
    layerProjMatrix G j x y =
      if y ∈ G.blk j x then (((L : ℝ) ^ j) ^ d)⁻¹ else 0 := by
  unfold layerProjMatrix blockProjMatrix
  by_cases hb : jBlock d L N₀ k j y = jBlock d L N₀ k j x
  · have hy : y ∈ G.layer j := (G.mem_layer_iff hj1 hjk hb).2 hx
    have hb' : blockMap (L ^ j) (N₀ * L ^ (k - j)) x = blockMap (L ^ j) (N₀ * L ^ (k - j)) y :=
      hb.symm
    simp [hx, hy, hb', G.mem_blk.2 hb]
  · have hb' : ¬ blockMap (L ^ j) (N₀ * L ^ (k - j)) x = blockMap (L ^ j) (N₀ * L ^ (k - j)) y :=
      fun h => hb h.symm
    have hnb : y ∉ G.blk j x := fun h => hb (G.mem_blk.1 h)
    simp [hb', hnb]

/-- Norm of one entry of the commutator argument on a block of the layer of `x`. -/
theorem commArg_norm_le {δ : ℝ} {φ : Torus d (N₀ * L ^ k) → Fin N → ℂ}
    (hφ : IsSmoothField G δ φ) (hδ : 0 ≤ δ) (s : G.Ω 1 × Fin N → ℂ) {j : ℕ} (hj1 : 1 ≤ j)
    (hjk : j ≤ k) {x : Torus d (N₀ * L ^ k)} (hx : x ∈ G.layer j) {y : Torus d (N₀ * L ^ k)}
    (hy : y ∈ G.blk j x) : ‖commArg G φ s x y‖ ≤ 2 * d * δ * vn (svec G s y) := by
  have h := hφ.osc_block hδ hj1 hjk hx (G.mem_blk.1 hy)
  rw [vn_sub_comm] at h
  unfold commArg
  refine (norm_dot_le (φ x - φ y) (svec G s y)).trans ?_
  exact mul_le_mul_of_nonneg_right h (vn_nonneg _)

theorem blockPart_norm_le {a : ℕ → ℝ} (ha : IsAdmissibleWeights k a) {δ : ℝ}
    {φ : Torus d (N₀ * L ^ k) → Fin N → ℂ} (hφ : IsSmoothField G δ φ) (hδ : 0 ≤ δ)
    (s : G.Ω 1 × Fin N → ℂ) {j : ℕ} (hj1 : 1 ≤ j) (hjk : j ≤ k) {x : Torus d (N₀ * L ^ k)}
    (hx : x ∈ G.layer j) :
    ‖((avgMatrix G a).map (algebraMap ℝ ℂ) *ᵥ commArg G φ s x) x‖ ≤
      a j / ((L : ℝ) ^ j) ^ 2 * (2 * d * δ) * (((L : ℝ) ^ j) ^ d)⁻¹ *
        ∑ y ∈ G.blk j x, vn (svec G s y) := by
  have haj : 0 ≤ a j := by linarith [(ha j hj1 hjk).1]
  have hL : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply]
  have hterm : ∀ y : Torus d (N₀ * L ^ k),
      ‖(algebraMap ℝ ℂ) (avgMatrix G a x y) * commArg G φ s x y‖ ≤
        if y ∈ G.blk j x then a j / ((L : ℝ) ^ j) ^ 2 * (2 * d * δ) * (((L : ℝ) ^ j) ^ d)⁻¹ *
          vn (svec G s y) else 0 := by
    intro y
    rw [avgMatrix_apply_of_layer G a hj1 hjk hx, layerProjMatrix_apply_of_layer G hj1 hjk hx]
    by_cases hy : y ∈ G.blk j x
    · simp only [hy, ↓reduceIte]
      rw [norm_mul, norm_algebraMap']
      have hn : ‖a j / ((L : ℝ) ^ j) ^ 2 * (((L : ℝ) ^ j) ^ d)⁻¹‖ =
          a j / ((L : ℝ) ^ j) ^ 2 * (((L : ℝ) ^ j) ^ d)⁻¹ := by
        rw [Real.norm_of_nonneg]; positivity
      rw [hn]
      have := commArg_norm_le G hφ hδ s hj1 hjk hx hy
      calc a j / ((L : ℝ) ^ j) ^ 2 * (((L : ℝ) ^ j) ^ d)⁻¹ * ‖commArg G φ s x y‖
          ≤ a j / ((L : ℝ) ^ j) ^ 2 * (((L : ℝ) ^ j) ^ d)⁻¹ * (2 * d * δ * vn (svec G s y)) := by
            gcongr
        _ = _ := by ring
    · simp [hy]
  calc _ ≤ ∑ y, ‖(algebraMap ℝ ℂ) (avgMatrix G a x y) * commArg G φ s x y‖ := norm_sum_le _ _
    _ ≤ ∑ y, (if y ∈ G.blk j x then a j / ((L : ℝ) ^ j) ^ 2 * (2 * d * δ) *
          (((L : ℝ) ^ j) ^ d)⁻¹ * vn (svec G s y) else 0) := Finset.sum_le_sum fun y _ => hterm y
    _ = _ := by
        rw [← Finset.sum_filter, Finset.mul_sum]
        refine Finset.sum_congr ?_ fun y _ => rfl
        ext y; simp

end Block

/-! ### Mean-square contraction of the block average -/

section BlockAverage

variable (G : GeneratingSet d L N₀ k ϱ)

theorem blk_eq_fibre (j : ℕ) (x : Torus d (N₀ * L ^ k)) :
    G.blk j x = blockFibre (L ^ j) (N₀ * L ^ (k - j)) (jBlock d L N₀ k j x) := by
  ext y
  exact Iff.rfl

theorem card_blk_cast (j : ℕ) (hjk : j ≤ k) (x : Torus d (N₀ * L ^ k)) :
    ((G.blk j x).card : ℝ) = ((L : ℝ) ^ j) ^ d := by
  rw [blk_eq_fibre, card_blockFibre (side_eq hjk)]
  push_cast
  rfl

/-- The block average is a mean-square contraction on a layer. -/
theorem layer_block_sq_sum {j : ℕ} (hj1 : 1 ≤ j) (hjk : j ≤ k)
    (V : Torus d (N₀ * L ^ k) → ℝ) :
    ∑ x ∈ G.layer j, ((((L : ℝ) ^ j) ^ d)⁻¹ * ∑ y ∈ G.blk j x, V y) ^ 2 ≤
      ∑ y ∈ G.layer j, V y ^ 2 := by
  have hL : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  set c : ℝ := (((L : ℝ) ^ j) ^ d)⁻¹ with hc
  have hc0 : 0 < c := by positivity
  have hcard : ((L : ℝ) ^ j) ^ d * c = 1 := by rw [hc]; field_simp
  have h1 : ∀ x ∈ G.layer j, (c * ∑ y ∈ G.blk j x, V y) ^ 2 ≤ c * ∑ y ∈ G.blk j x, V y ^ 2 := by
    intro x _
    have h := sq_sum_le_card_mul_sum_sq (s := G.blk j x) (f := V)
    rw [card_blk_cast G j hjk] at h
    calc (c * ∑ y ∈ G.blk j x, V y) ^ 2 = c ^ 2 * (∑ y ∈ G.blk j x, V y) ^ 2 := by ring
      _ ≤ c ^ 2 * (((L : ℝ) ^ j) ^ d * ∑ y ∈ G.blk j x, V y ^ 2) :=
          mul_le_mul_of_nonneg_left h (by positivity)
      _ = c * ((((L : ℝ) ^ j) ^ d * c) * ∑ y ∈ G.blk j x, V y ^ 2) := by ring
      _ = c * ∑ y ∈ G.blk j x, V y ^ 2 := by rw [hcard, one_mul]
  refine (Finset.sum_le_sum h1).trans ?_
  rw [← Finset.mul_sum]
  have h2 : ∑ x ∈ G.layer j, ∑ y ∈ G.blk j x, V y ^ 2 =
      ∑ y ∈ G.layer j, ((L : ℝ) ^ j) ^ d * V y ^ 2 := by
    have e : ∀ x ∈ G.layer j, ∑ y ∈ G.blk j x, V y ^ 2 =
        ∑ y : Torus d (N₀ * L ^ k), if jBlock d L N₀ k j y = jBlock d L N₀ k j x then V y ^ 2 else 0 := by
      intro x _
      rw [GeneratingSet.blk, Finset.sum_filter]
    rw [Finset.sum_congr rfl e, Finset.sum_comm]
    have e2 : ∀ y : Torus d (N₀ * L ^ k),
        ∑ x ∈ G.layer j, (if jBlock d L N₀ k j y = jBlock d L N₀ k j x then V y ^ 2 else 0) =
          if y ∈ G.layer j then ((L : ℝ) ^ j) ^ d * V y ^ 2 else 0 := by
      intro y
      by_cases hy : y ∈ G.layer j
      · simp only [hy, ↓reduceIte]
        rw [← Finset.sum_filter]
        have : (G.layer j).filter (fun x => jBlock d L N₀ k j y = jBlock d L N₀ k j x) =
            G.blk j y := by
          ext x
          simp only [Finset.mem_filter, GeneratingSet.mem_blk]
          constructor
          · exact fun h => h.2.symm
          · intro h
            exact ⟨(G.mem_layer_iff hj1 hjk h).2 hy, h.symm⟩
        rw [this, Finset.sum_const, nsmul_eq_mul, card_blk_cast G j hjk]
      · simp only [hy, ↓reduceIte]
        refine Finset.sum_eq_zero fun x hx => ?_
        have : jBlock d L N₀ k j y ≠ jBlock d L N₀ k j x := fun h =>
          hy ((G.mem_layer_iff hj1 hjk h).2 hx)
        simp [this]
    rw [Finset.sum_congr rfl fun y _ => e2 y, ← Finset.sum_filter]
    congr 1
    ext y; simp
  rw [h2]
  have : c * ∑ y ∈ G.layer j, ((L : ℝ) ^ j) ^ d * V y ^ 2 = ∑ y ∈ G.layer j, V y ^ 2 := by
    rw [← Finset.mul_sum, ← mul_assoc, mul_comm c, hcard, one_mul]
  exact this.le

end BlockAverage

/-! ### The pointwise weighted bound for the commutator -/

section Pointwise

variable (G : GeneratingSet d L N₀ k ϱ)

theorem commK_dirichlet_split (a : ℕ → ℝ) (ν : ℝ) (α : G.Ω 1 → ℂ)
    (φ : Torus d (N₀ * L ^ k) → Fin N → ℂ) (s : G.Ω 1 × Fin N → ℂ) (x : G.Ω 1) :
    (commK (dirichletOperator G a ν α) (restrictField G φ) *ᵥ s) x =
      lapTerm G φ s x +
        ((avgMatrix G a).map (algebraMap ℝ ℂ) *ᵥ commArg G φ s x) x := by
  rw [commK_dirichlet, ← lap_part_eq G ν φ s x]
  unfold fullMatrix
  have : ((latticeLaplacian d (N₀ * L ^ k) ν + avgMatrix G a).map (algebraMap ℝ ℂ)) =
      (latticeLaplacian d (N₀ * L ^ k) ν).map (algebraMap ℝ ℂ) +
        (avgMatrix G a).map (algebraMap ℝ ℂ) := by
    ext y z; simp
  rw [this, Matrix.add_mulVec, Pi.add_apply]

/-- **Pointwise weighted bound for `K(φ₀) s`.** -/
theorem commK_pointwise {a : ℕ → ℝ} (ha : IsAdmissibleWeights k a) (ν : ℝ) (α : G.Ω 1 → ℂ)
    {δ : ℝ} {φ : Torus d (N₀ * L ^ k) → Fin N → ℂ} (hφ : IsSmoothField G δ φ) (hδ : 0 ≤ δ)
    {r : Torus d (N₀ * L ^ k) → ℝ} (hr : IsAgmonWeight G r) {ε : ℝ} (hε0 : 0 ≤ ε)
    (s : G.Ω 1 × Fin N → ℂ) {j : ℕ} (hj1 : 1 ≤ j) (hjk : j ≤ k) (x : G.Ω 1)
    (hx : (x : Torus d (N₀ * L ^ k)) ∈ G.layer j) :
    G.spacing x * Real.exp (ε * r x) *
        ‖(commK (dirichletOperator G a ν α) (restrictField G φ) *ᵥ s) x‖ ≤
      δ * Real.exp (ε * r x) * ∑ μ : Fin d, (vn (svec G s ((x : Torus d (N₀ * L ^ k)) + Pi.single μ 1) - svec G s x) +
          vn (svec G s ((x : Torus d (N₀ * L ^ k)) - Pi.single μ 1) - svec G s x)) +
        δ * ((L : ℝ) ^ j)⁻¹ * (Real.exp (ε * r x) * vn (svec G s x)) +
        4 * d * δ * Real.exp (ε * (2 * d)) * ((L : ℝ) ^ j)⁻¹ *
          ((((L : ℝ) ^ j) ^ d)⁻¹ * ∑ y ∈ G.blk j x, Real.exp (ε * r y) * vn (svec G s y)) := by
  have hL : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hLj : (0 : ℝ) < (L : ℝ) ^ j := by positivity
  have hsp : G.spacing x = (L : ℝ) ^ j := G.spacing_eq hj1 hjk hx
  have hW0 : 0 < Real.exp (ε * r x) := Real.exp_pos _
  rw [commK_dirichlet_split, hsp]
  have hΩ : (x : Torus d (N₀ * L ^ k)) ∈ G.Ω 1 := x.2
  have h1 := lapTerm_norm_le G hφ s hΩ
  have h2 := blockPart_norm_le G ha hφ hδ s hj1 hjk hx
  rw [hsp] at h1
  have haj : a j ≤ 2 := (ha j hj1 hjk).2
  have haj0 : 0 ≤ a j := by linarith [(ha j hj1 hjk).1]
  -- the block part, weighted
  have h3 : Real.exp (ε * r x) * ∑ y ∈ G.blk j x, vn (svec G s y) ≤
      Real.exp (ε * (2 * d)) * ∑ y ∈ G.blk j x, Real.exp (ε * r y) * vn (svec G s y) := by
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_le_sum fun y hy => ?_
    have hb := hr.block j hj1 hjk x y hx (G.mem_blk.1 hy)
    have : r x ≤ r y + 2 * d := by linarith [(abs_le.1 hb).2, (abs_le.1 hb).1]
    have hexp : Real.exp (ε * r x) ≤ Real.exp (ε * (2 * d)) * Real.exp (ε * r y) := by
      rw [← Real.exp_add]
      exact Real.exp_le_exp.2 (by nlinarith)
    calc Real.exp (ε * r x) * vn (svec G s y)
        ≤ (Real.exp (ε * (2 * d)) * Real.exp (ε * r y)) * vn (svec G s y) :=
          mul_le_mul_of_nonneg_right hexp (vn_nonneg _)
      _ = _ := by ring
  have hK := norm_add_le (lapTerm G φ s x)
    (((avgMatrix G a).map (algebraMap ℝ ℂ) *ᵥ commArg G φ s x) x)
  calc (L : ℝ) ^ j * Real.exp (ε * r x) * ‖lapTerm G φ s x +
        ((avgMatrix G a).map (algebraMap ℝ ℂ) *ᵥ commArg G φ s x) x‖
      ≤ (L : ℝ) ^ j * Real.exp (ε * r x) * (‖lapTerm G φ s x‖ +
        ‖((avgMatrix G a).map (algebraMap ℝ ℂ) *ᵥ commArg G φ s x) x‖) :=
        mul_le_mul_of_nonneg_left hK (by positivity)
    _ ≤ (L : ℝ) ^ j * Real.exp (ε * r x) *
          ((δ / (L : ℝ) ^ j * ∑ μ : Fin d, (vn (svec G s ((x : Torus d (N₀ * L ^ k)) + Pi.single μ 1) - svec G s x) +
            vn (svec G s ((x : Torus d (N₀ * L ^ k)) - Pi.single μ 1) - svec G s x)) +
            δ / ((L : ℝ) ^ j) ^ 2 * vn (svec G s x)) +
          a j / ((L : ℝ) ^ j) ^ 2 * (2 * d * δ) * (((L : ℝ) ^ j) ^ d)⁻¹ *
            ∑ y ∈ G.blk j x, vn (svec G s y)) := by
        gcongr
    _ = δ * Real.exp (ε * r x) * ∑ μ : Fin d, (vn (svec G s ((x : Torus d (N₀ * L ^ k)) + Pi.single μ 1) - svec G s x) +
          vn (svec G s ((x : Torus d (N₀ * L ^ k)) - Pi.single μ 1) - svec G s x)) +
        δ * ((L : ℝ) ^ j)⁻¹ * (Real.exp (ε * r x) * vn (svec G s x)) +
        (a j * (2 * d * δ) * ((L : ℝ) ^ j)⁻¹ * (((L : ℝ) ^ j) ^ d)⁻¹) *
          (Real.exp (ε * r x) * ∑ y ∈ G.blk j x, vn (svec G s y)) := by
        field_simp
    _ ≤ _ := by
        have hc : 0 ≤ a j * (2 * d * δ) * ((L : ℝ) ^ j)⁻¹ * (((L : ℝ) ^ j) ^ d)⁻¹ := by positivity
        have h4 := mul_le_mul_of_nonneg_left h3 hc
        have h5 : (a j * (2 * d * δ) * ((L : ℝ) ^ j)⁻¹ * (((L : ℝ) ^ j) ^ d)⁻¹) *
            (Real.exp (ε * (2 * d)) * ∑ y ∈ G.blk j x, Real.exp (ε * r y) * vn (svec G s y)) ≤
            4 * d * δ * Real.exp (ε * (2 * d)) * ((L : ℝ) ^ j)⁻¹ *
              ((((L : ℝ) ^ j) ^ d)⁻¹ * ∑ y ∈ G.blk j x, Real.exp (ε * r y) * vn (svec G s y)) := by
          have hS : 0 ≤ ∑ y ∈ G.blk j x, Real.exp (ε * r y) * vn (svec G s y) :=
            Finset.sum_nonneg fun y _ => mul_nonneg (Real.exp_pos _).le (vn_nonneg _)
          have hE := Real.exp_pos (ε * (2 * d))
          have hq : 0 ≤ (d : ℝ) * δ * Real.exp (ε * (2 * d)) * ((L : ℝ) ^ j)⁻¹ *
              (((L : ℝ) ^ j) ^ d)⁻¹ * ∑ y ∈ G.blk j x, Real.exp (ε * r y) * vn (svec G s y) := by
            positivity
          nlinarith [mul_le_mul_of_nonneg_right haj hq]
        linarith

end Pointwise

/-! ### Summation over the layers -/

section Summation

variable (G : GeneratingSet d L N₀ k ϱ)

theorem Ω_eq_biUnion_layers : G.Ω 1 = (Finset.Icc 1 k).biUnion G.layer := by
  ext x
  simp only [Finset.mem_biUnion, Finset.mem_Icc]
  constructor
  · intro hx
    obtain ⟨j, hj1, hjk, hxj⟩ := G.exists_layer hx
    exact ⟨j, ⟨hj1, hjk⟩, hxj⟩
  · rintro ⟨j, ⟨hj1, hjk⟩, hxj⟩
    exact G.layer_subset hj1 hjk hxj

theorem sum_Ω_layers (F : Torus d (N₀ * L ^ k) → ℝ) :
    ∑ x ∈ G.Ω 1, F x = ∑ j ∈ Finset.Icc 1 k, ∑ x ∈ G.layer j, F x := by
  rw [Ω_eq_biUnion_layers G, Finset.sum_biUnion]
  intro j hj j' hj' hne
  refine Finset.disjoint_left.2 fun x hx hx' => ?_
  exact G.layer_disjoint (Finset.mem_Icc.1 hj).1 (Finset.mem_Icc.1 hj).2 (Finset.mem_Icc.1 hj').1
    (Finset.mem_Icc.1 hj').2 hne hx hx'

theorem sum_layer_sq_eq (j : ℕ) (V : Torus d (N₀ * L ^ k) → ℝ) :
    ∑ x, (layerPart G j V x) ^ 2 = ∑ x ∈ G.layer j, V x ^ 2 := by
  have : ∀ x, (layerPart G j V x) ^ 2 = if x ∈ G.layer j then V x ^ 2 else 0 := by
    intro x; by_cases h : x ∈ G.layer j <;> simp [layerPart, h]
  simp only [this]
  rw [← Finset.sum_filter]
  congr 1
  ext x; simp

theorem wsq_eq_layers (V : Torus d (N₀ * L ^ k) → ℝ) :
    wsq G V = ∑ j ∈ Finset.Icc 1 k, (((L : ℝ) ^ j) ^ 2)⁻¹ * ∑ x ∈ G.layer j, V x ^ 2 := by
  rw [wsq_eq_sum_layers]
  exact Finset.sum_congr rfl fun j _ => by rw [sum_layer_sq_eq]

/-- The vector-valued weighted gradient `‖w ∂ s‖²` in terms of Euclidean norms. -/
noncomputable def vecGrad (ε : ℝ) (r : Torus d (N₀ * L ^ k) → ℝ) (s : G.Ω 1 × Fin N → ℂ) : ℝ :=
  ∑ x ∈ G.Ω 1, ∑ μ : Fin d, Real.exp (ε * r x) ^ 2 *
    (vn (svec G s (x + Pi.single μ 1) - svec G s x) ^ 2 +
      vn (svec G s (x - Pi.single μ 1) - svec G s x) ^ 2)

/-- The vector-valued weighted norm `‖ℓ⁻¹ w s‖²`. -/
noncomputable def vecM (ε : ℝ) (r : Torus d (N₀ * L ^ k) → ℝ) (s : G.Ω 1 × Fin N → ℂ) : ℝ :=
  wsq G (fun y => Real.exp (ε * r y) * vn (svec G s y))

theorem vecGrad_nonneg (ε : ℝ) (r : Torus d (N₀ * L ^ k) → ℝ) (s : G.Ω 1 × Fin N → ℂ) :
    0 ≤ vecGrad G ε r s :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity

theorem vecM_nonneg (ε : ℝ) (r : Torus d (N₀ * L ^ k) → ℝ) (s : G.Ω 1 × Fin N → ℂ) :
    0 ≤ vecM G ε r s := wsq_nonneg G _

end Summation

/-! ### The weighted bound for the commutator -/

section Main

variable (G : GeneratingSet d L N₀ k ϱ)

theorem three_sq_le (a b c : ℝ) : (a + b + c) ^ 2 ≤ 3 * (a ^ 2 + b ^ 2 + c ^ 2) := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c)]

theorem sq_sum_pair_le (d : ℕ) (u v : Fin d → ℝ) :
    (∑ μ, (u μ + v μ)) ^ 2 ≤ 2 * d * ∑ μ, (u μ ^ 2 + v μ ^ 2) := by
  have h := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin d)))
    (f := fun μ => u μ + v μ)
  simp only [Finset.card_univ, Fintype.card_fin] at h
  refine h.trans ?_
  have : ∑ μ, (u μ + v μ) ^ 2 ≤ ∑ μ, 2 * (u μ ^ 2 + v μ ^ 2) :=
    Finset.sum_le_sum fun μ _ => by nlinarith [sq_nonneg (u μ - v μ)]
  calc (d : ℝ) * ∑ μ, (u μ + v μ) ^ 2 ≤ d * ∑ μ, 2 * (u μ ^ 2 + v μ ^ 2) :=
        mul_le_mul_of_nonneg_left this (Nat.cast_nonneg d)
    _ = 2 * d * ∑ μ, (u μ ^ 2 + v μ ^ 2) := by rw [← Finset.mul_sum]; ring

theorem commK_sq_pointwise {a : ℕ → ℝ} (ha : IsAdmissibleWeights k a) (ν : ℝ) (α : G.Ω 1 → ℂ)
    {δ : ℝ} {φ : Torus d (N₀ * L ^ k) → Fin N → ℂ} (hφ : IsSmoothField G δ φ) (hδ : 0 ≤ δ)
    {r : Torus d (N₀ * L ^ k) → ℝ} (hr : IsAgmonWeight G r) {ε : ℝ} (hε0 : 0 ≤ ε)
    (s : G.Ω 1 × Fin N → ℂ) {j : ℕ} (hj1 : 1 ≤ j) (hjk : j ≤ k) (x : G.Ω 1)
    (hx : (x : Torus d (N₀ * L ^ k)) ∈ G.layer j) :
    (G.spacing x * Real.exp (ε * r x) *
        ‖(commK (dirichletOperator G a ν α) (restrictField G φ) *ᵥ s) x‖) ^ 2 ≤
      3 * (2 * d * δ ^ 2 * (Real.exp (ε * r x) ^ 2 * ∑ μ : Fin d,
          (vn (svec G s ((x : Torus d (N₀ * L ^ k)) + Pi.single μ 1) - svec G s x) ^ 2 +
            vn (svec G s ((x : Torus d (N₀ * L ^ k)) - Pi.single μ 1) - svec G s x) ^ 2)) +
        δ ^ 2 * (((L : ℝ) ^ j) ^ 2)⁻¹ * (Real.exp (ε * r x) * vn (svec G s x)) ^ 2 +
        16 * d ^ 2 * δ ^ 2 * Real.exp (ε * (2 * d)) ^ 2 * (((L : ℝ) ^ j) ^ 2)⁻¹ *
          ((((L : ℝ) ^ j) ^ d)⁻¹ * ∑ y ∈ G.blk j x, Real.exp (ε * r y) * vn (svec G s y)) ^ 2) := by
  have h := commK_pointwise G ha ν α hφ hδ hr hε0 s hj1 hjk x hx
  set t1 := δ * Real.exp (ε * r x) * ∑ μ : Fin d,
    (vn (svec G s ((x : Torus d (N₀ * L ^ k)) + Pi.single μ 1) - svec G s x) +
      vn (svec G s ((x : Torus d (N₀ * L ^ k)) - Pi.single μ 1) - svec G s x)) with ht1
  set t2 := δ * ((L : ℝ) ^ j)⁻¹ * (Real.exp (ε * r x) * vn (svec G s x)) with ht2
  set t3 := 4 * d * δ * Real.exp (ε * (2 * d)) * ((L : ℝ) ^ j)⁻¹ *
    ((((L : ℝ) ^ j) ^ d)⁻¹ * ∑ y ∈ G.blk j x, Real.exp (ε * r y) * vn (svec G s y)) with ht3
  have hnn : 0 ≤ G.spacing x * Real.exp (ε * r x) *
      ‖(commK (dirichletOperator G a ν α) (restrictField G φ) *ᵥ s) x‖ := by
    have := spacing_pos G (x := (x : Torus d (N₀ * L ^ k)))
    positivity
  have h1 := pow_le_pow_left₀ hnn h 2
  refine h1.trans ((three_sq_le t1 t2 t3).trans ?_)
  have e1 : t1 ^ 2 ≤ 2 * d * δ ^ 2 * (Real.exp (ε * r x) ^ 2 * ∑ μ : Fin d,
      (vn (svec G s ((x : Torus d (N₀ * L ^ k)) + Pi.single μ 1) - svec G s x) ^ 2 +
        vn (svec G s ((x : Torus d (N₀ * L ^ k)) - Pi.single μ 1) - svec G s x) ^ 2)) := by
    have := sq_sum_pair_le d
      (fun μ => vn (svec G s ((x : Torus d (N₀ * L ^ k)) + Pi.single μ 1) - svec G s x))
      (fun μ => vn (svec G s ((x : Torus d (N₀ * L ^ k)) - Pi.single μ 1) - svec G s x))
    calc t1 ^ 2 = (δ * Real.exp (ε * r x)) ^ 2 * (∑ μ : Fin d,
        (vn (svec G s ((x : Torus d (N₀ * L ^ k)) + Pi.single μ 1) - svec G s x) +
        vn (svec G s ((x : Torus d (N₀ * L ^ k)) - Pi.single μ 1) - svec G s x))) ^ 2 := by
          rw [ht1]; ring
      _ ≤ (δ * Real.exp (ε * r x)) ^ 2 * (2 * d * ∑ μ : Fin d,
          (vn (svec G s ((x : Torus d (N₀ * L ^ k)) + Pi.single μ 1) - svec G s x) ^ 2 +
        vn (svec G s ((x : Torus d (N₀ * L ^ k)) - Pi.single μ 1) - svec G s x) ^ 2)) :=
          mul_le_mul_of_nonneg_left this (sq_nonneg _)
      _ = _ := by ring
  have e2 : t2 ^ 2 = δ ^ 2 * (((L : ℝ) ^ j) ^ 2)⁻¹ * (Real.exp (ε * r x) * vn (svec G s x)) ^ 2 := by
    rw [ht2, mul_pow, mul_pow, inv_pow]
  have e3 : t3 ^ 2 = 16 * d ^ 2 * δ ^ 2 * Real.exp (ε * (2 * d)) ^ 2 * (((L : ℝ) ^ j) ^ 2)⁻¹ *
      ((((L : ℝ) ^ j) ^ d)⁻¹ * ∑ y ∈ G.blk j x, Real.exp (ε * r y) * vn (svec G s y)) ^ 2 := by
    rw [ht3]
    simp only [mul_pow, inv_pow]
    ring
  rw [e2, e3]
  linarith

/-- The per-layer bound. -/
theorem commK_layer_sum_le {a : ℕ → ℝ} (ha : IsAdmissibleWeights k a) (ν : ℝ) (α : G.Ω 1 → ℂ)
    {δ : ℝ} {φ : Torus d (N₀ * L ^ k) → Fin N → ℂ} (hφ : IsSmoothField G δ φ) (hδ : 0 ≤ δ)
    {r : Torus d (N₀ * L ^ k) → ℝ} (hr : IsAgmonWeight G r) {ε : ℝ} (hε0 : 0 ≤ ε)
    (s : G.Ω 1 × Fin N → ℂ) {j : ℕ} (hj1 : 1 ≤ j) (hjk : j ≤ k) :
    ∑ x ∈ G.layer j, G.spacing x ^ 2 * ‖((Real.exp (ε * r x) : ℝ) : ℂ) *
        zeroExt (G.Ω 1) (commK (dirichletOperator G a ν α) (restrictField G φ) *ᵥ s) x‖ ^ 2 ≤
      3 * (2 * d * δ ^ 2 * ∑ x ∈ G.layer j, (Real.exp (ε * r x) ^ 2 * ∑ μ : Fin d,
          (vn (svec G s (x + Pi.single μ 1) - svec G s x) ^ 2 +
            vn (svec G s (x - Pi.single μ 1) - svec G s x) ^ 2)) +
        (δ ^ 2 + 16 * d ^ 2 * δ ^ 2 * Real.exp (ε * (2 * d)) ^ 2) * (((L : ℝ) ^ j) ^ 2)⁻¹ *
          ∑ y ∈ G.layer j, (Real.exp (ε * r y) * vn (svec G s y)) ^ 2) := by
  set V : Torus d (N₀ * L ^ k) → ℝ := fun y => Real.exp (ε * r y) * vn (svec G s y) with hV
  have hpt : ∀ x ∈ G.layer j, G.spacing x ^ 2 * ‖((Real.exp (ε * r x) : ℝ) : ℂ) *
        zeroExt (G.Ω 1) (commK (dirichletOperator G a ν α) (restrictField G φ) *ᵥ s) x‖ ^ 2 ≤
      3 * (2 * d * δ ^ 2 * (Real.exp (ε * r x) ^ 2 * ∑ μ : Fin d,
          (vn (svec G s (x + Pi.single μ 1) - svec G s x) ^ 2 +
            vn (svec G s (x - Pi.single μ 1) - svec G s x) ^ 2)) +
        δ ^ 2 * (((L : ℝ) ^ j) ^ 2)⁻¹ * V x ^ 2 +
        16 * d ^ 2 * δ ^ 2 * Real.exp (ε * (2 * d)) ^ 2 * (((L : ℝ) ^ j) ^ 2)⁻¹ *
          ((((L : ℝ) ^ j) ^ d)⁻¹ * ∑ y ∈ G.blk j x, V y) ^ 2) := by
    intro x hx
    have hxΩ : x ∈ G.Ω 1 := G.layer_subset hj1 hjk hx
    have h := commK_sq_pointwise G ha ν α hφ hδ hr hε0 s hj1 hjk ⟨x, hxΩ⟩ hx
    have e : G.spacing x ^ 2 * ‖((Real.exp (ε * r x) : ℝ) : ℂ) *
        zeroExt (G.Ω 1) (commK (dirichletOperator G a ν α) (restrictField G φ) *ᵥ s) x‖ ^ 2 =
        (G.spacing x * Real.exp (ε * r x) *
          ‖(commK (dirichletOperator G a ν α) (restrictField G φ) *ᵥ s) ⟨x, hxΩ⟩‖) ^ 2 := by
      have : zeroExt (G.Ω 1) (commK (dirichletOperator G a ν α) (restrictField G φ) *ᵥ s) x =
          (commK (dirichletOperator G a ν α) (restrictField G φ) *ᵥ s) ⟨x, hxΩ⟩ :=
        zeroExt_mem (G.Ω 1) _ ⟨x, hxΩ⟩
      rw [this, norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
      ring
    rw [e]
    exact h
  refine (Finset.sum_le_sum hpt).trans ?_
  rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_add_distrib]
  have hL : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hav := layer_block_sq_sum G hj1 hjk V
  have e1 : ∑ x ∈ G.layer j, 2 * d * δ ^ 2 * (Real.exp (ε * r x) ^ 2 * ∑ μ : Fin d,
          (vn (svec G s (x + Pi.single μ 1) - svec G s x) ^ 2 +
            vn (svec G s (x - Pi.single μ 1) - svec G s x) ^ 2)) =
      2 * d * δ ^ 2 * ∑ x ∈ G.layer j, (Real.exp (ε * r x) ^ 2 * ∑ μ : Fin d,
          (vn (svec G s (x + Pi.single μ 1) - svec G s x) ^ 2 +
            vn (svec G s (x - Pi.single μ 1) - svec G s x) ^ 2)) := by
    rw [Finset.mul_sum]
  have e2 : ∑ x ∈ G.layer j, δ ^ 2 * (((L : ℝ) ^ j) ^ 2)⁻¹ * V x ^ 2 =
      δ ^ 2 * (((L : ℝ) ^ j) ^ 2)⁻¹ * ∑ y ∈ G.layer j, V y ^ 2 := by rw [Finset.mul_sum]
  have e3 : ∑ x ∈ G.layer j, 16 * d ^ 2 * δ ^ 2 * Real.exp (ε * (2 * d)) ^ 2 *
      (((L : ℝ) ^ j) ^ 2)⁻¹ * ((((L : ℝ) ^ j) ^ d)⁻¹ * ∑ y ∈ G.blk j x, V y) ^ 2 ≤
      16 * d ^ 2 * δ ^ 2 * Real.exp (ε * (2 * d)) ^ 2 * (((L : ℝ) ^ j) ^ 2)⁻¹ *
        ∑ y ∈ G.layer j, V y ^ 2 := by
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left hav (by positivity)
  rw [e1, e2]
  have : (δ ^ 2 + 16 * d ^ 2 * δ ^ 2 * Real.exp (ε * (2 * d)) ^ 2) * (((L : ℝ) ^ j) ^ 2)⁻¹ *
      ∑ y ∈ G.layer j, V y ^ 2 = δ ^ 2 * (((L : ℝ) ^ j) ^ 2)⁻¹ * ∑ y ∈ G.layer j, V y ^ 2 +
      16 * d ^ 2 * δ ^ 2 * Real.exp (ε * (2 * d)) ^ 2 * (((L : ℝ) ^ j) ^ 2)⁻¹ *
        ∑ y ∈ G.layer j, V y ^ 2 := by ring
  rw [this]
  linarith

theorem exp_two_d_sq_le (hd : 0 < d) {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ agmonRate d) :
    Real.exp (ε * (2 * d)) ^ 2 ≤ 2 := by
  have h1 := rate_mul_le hd hε1
  have h2 : Real.exp (8 * (ε * d)) ≤ 2 := exp_eight_mul_le_two (by positivity) h1
  have e : Real.exp (ε * (2 * d)) ^ 2 = Real.exp (4 * (ε * d)) := by
    rw [sq, ← Real.exp_add]; congr 1; ring
  rw [e]
  refine le_trans (Real.exp_le_exp.2 ?_) h2
  have : 0 ≤ ε * d := by positivity
  linarith

/-- **The weighted bound for the commutator** (GREEN.md §4.5a, the three terms of `K(φ₀)`):
`‖ℓ w K(φ₀) s‖² ≤ 105 d² δ² (‖w ∂ s‖² + ‖ℓ⁻¹ w s‖²)`. -/
theorem agmonSource_commK_le (hd : 0 < d) {a : ℕ → ℝ} (ha : IsAdmissibleWeights k a) (ν : ℝ)
    (α : G.Ω 1 → ℂ) {δ : ℝ} {φ : Torus d (N₀ * L ^ k) → Fin N → ℂ}
    (hφ : IsSmoothField G δ φ) (hδ : 0 ≤ δ)
    {r : Torus d (N₀ * L ^ k) → ℝ} (hr : IsAgmonWeight G r) {ε : ℝ} (hε0 : 0 ≤ ε)
    (hε1 : ε ≤ agmonRate d) (s : G.Ω 1 × Fin N → ℂ) :
    agmonSource G ε r (commK (dirichletOperator G a ν α) (restrictField G φ) *ᵥ s) ≤
      105 * d ^ 2 * δ ^ 2 * (vecGrad G ε r s + vecM G ε r s) := by
  have hdd : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hE := exp_two_d_sq_le hd hε0 hε1
  set Kf := commK (dirichletOperator G a ν α) (restrictField G φ) *ᵥ s with hKf
  set F : Torus d (N₀ * L ^ k) → ℝ := fun x => G.spacing x ^ 2 *
    ‖((Real.exp (ε * r x) : ℝ) : ℂ) * zeroExt (G.Ω 1) Kf x‖ ^ 2 with hF
  have hF0 : ∀ x ∈ (Finset.univ : Finset (Torus d (N₀ * L ^ k))), x ∉ G.Ω 1 → F x = 0 := by
    intro x _ hx
    simp [hF, zeroExt_not_mem _ _ hx]
  have h1 : agmonSource G ε r Kf = ∑ j ∈ Finset.Icc 1 k, ∑ x ∈ G.layer j, F x := by
    rw [← sum_Ω_layers G F]
    unfold agmonSource
    exact (Finset.sum_subset (Finset.subset_univ _) hF0).symm
  set Vp : Torus d (N₀ * L ^ k) → ℝ := fun y => Real.exp (ε * r y) * vn (svec G s y) with hVp
  set Gp : Torus d (N₀ * L ^ k) → ℝ := fun x => Real.exp (ε * r x) ^ 2 * ∑ μ : Fin d,
    (vn (svec G s (x + Pi.single μ 1) - svec G s x) ^ 2 +
      vn (svec G s (x - Pi.single μ 1) - svec G s x) ^ 2) with hGp
  have h2 : ∀ j ∈ Finset.Icc 1 k, ∑ x ∈ G.layer j, F x ≤
      3 * (2 * d * δ ^ 2 * ∑ x ∈ G.layer j, Gp x + (δ ^ 2 + 16 * d ^ 2 * δ ^ 2 *
        Real.exp (ε * (2 * d)) ^ 2) * ((((L : ℝ) ^ j) ^ 2)⁻¹ * ∑ y ∈ G.layer j, Vp y ^ 2)) := by
    intro j hj
    have := commK_layer_sum_le G ha ν α hφ hδ hr hε0 s (Finset.mem_Icc.1 hj).1
      (Finset.mem_Icc.1 hj).2
    refine this.trans (le_of_eq ?_)
    ring
  have hGv : vecGrad G ε r s = ∑ x ∈ G.Ω 1, Gp x := by
    unfold vecGrad
    exact Finset.sum_congr rfl fun x _ => by simp only [hGp]; rw [Finset.mul_sum]
  have hMv : vecM G ε r s = ∑ j ∈ Finset.Icc 1 k, (((L : ℝ) ^ j) ^ 2)⁻¹ * ∑ y ∈ G.layer j, Vp y ^ 2 :=
    wsq_eq_layers G Vp
  have hC : δ ^ 2 + 16 * d ^ 2 * δ ^ 2 * Real.exp (ε * (2 * d)) ^ 2 ≤ δ ^ 2 * (1 + 32 * d ^ 2) := by
    have : 16 * d ^ 2 * δ ^ 2 * Real.exp (ε * (2 * d)) ^ 2 ≤ 16 * d ^ 2 * δ ^ 2 * 2 :=
      mul_le_mul_of_nonneg_left hE (by positivity)
    nlinarith
  rw [h1]
  refine (Finset.sum_le_sum h2).trans ?_
  rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← sum_Ω_layers G Gp,
    ← hGv, ← hMv]
  have hM0 := vecM_nonneg G ε r s
  have hG0 := vecGrad_nonneg G ε r s
  have hC0 : 0 ≤ δ ^ 2 + 16 * d ^ 2 * δ ^ 2 * Real.exp (ε * (2 * d)) ^ 2 := by positivity
  have h3 := mul_le_mul_of_nonneg_right hC hM0
  have hδ2 : 0 ≤ δ ^ 2 := sq_nonneg δ
  have hd2 : (1 : ℝ) ≤ d ^ 2 := by nlinarith
  have hdd2 : (d : ℝ) ≤ d ^ 2 := by nlinarith
  have := mul_nonneg hδ2 hG0
  have := mul_nonneg hδ2 hM0
  nlinarith [mul_le_mul_of_nonneg_left hdd2 (mul_nonneg hδ2 hG0),
    mul_le_mul_of_nonneg_left hd2 (mul_nonneg hδ2 hM0), mul_nonneg hδ2 (mul_nonneg (sq_nonneg (d:ℝ)) hM0)]

end Main

end Balaban.Multiscale
