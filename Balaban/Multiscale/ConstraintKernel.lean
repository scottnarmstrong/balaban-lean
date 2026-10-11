/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Multiscale.ConstraintDecay
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The unit-lattice kernel of `Q_k Π Q_k^*` (GREEN.md §4.5b (3), G-1(d)(3))

Dictionary (fine unit spacing, `η = L⁻ᵏ` in the units of GREEN.md): the unit blocks are the
`k`-blocks `Δ_k(y)` of the fine torus (`Balaban.Multiscale.GeneratingSet.blk`), `Q_k^* ψ = ψ ∘ (k-block
map)`, and `Q_k f (y) = L^{-k d} ∑_{x ∈ Δ_k(y)} f(x)`.  An operator `Π_η` of GREEN.md (scale `η`) is
`η² Π` with `Π` the matrix in fine units (`H_η = η⁻² H`), so that

`(Q_k Π_η Q_k^*)(y, y') = L^{-(k d + 2 k)} ⟨1_{Δ_k(y)}, Π 1_{Δ_k(y')}⟩`

(`Balaban.Multiscale.unitKernel`, componentwise in `ℂ^N`).
-/

@[expose] public section

namespace Balaban.Multiscale

open Matrix Finset

variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}

section Kernel

variable (G : GeneratingSet d L N₀ k ϱ)

/-- The indicator `1_{Δ_j(y)} ⊗ e_{i₀}` of a block, in the component `i₀`. -/
noncomputable def indVec (j : ℕ) (y : Torus d (N₀ * L ^ k)) (i₀ : Fin N) :
    G.Ω 1 × Fin N → ℂ :=
  fun p => if p.2 = i₀ ∧ (p.1 : Torus d (N₀ * L ^ k)) ∈ G.blk j y then 1 else 0

/-- **The unit-lattice kernel** of `Q_k Π_η Q_k^*` (component `(i, i₀)`, blocks `y`, `y'`):
`L^{-(k d + 2 k)} ⟨1_{Δ_k(y)} e_i, Π 1_{Δ_k(y')} e_{i₀}⟩`. -/
noncomputable def unitKernel (Pm : Matrix (G.Ω 1 × Fin N) (G.Ω 1 × Fin N) ℂ)
    (y y' : Torus d (N₀ * L ^ k)) (i i₀ : Fin N) : ℂ :=
  (((L : ℝ) ^ (k * d + 2 * k))⁻¹ : ℝ) *
    (star (indVec G k y i) ⬝ᵥ (Pm *ᵥ indVec G k y' i₀))

theorem blk_subset_Ω {j : ℕ} (hj1 : 1 ≤ j) (hjk : j ≤ k) {y : Torus d (N₀ * L ^ k)}
    (hy : y ∈ G.layer j) : G.blk j y ⊆ G.Ω 1 := fun _ hx =>
  G.layer_subset hj1 hjk ((G.mem_layer_iff hj1 hjk (G.mem_blk.1 hx)).2 hy)

theorem card_blk_sub {j : ℕ} (hj1 : 1 ≤ j) (hjk : j ≤ k) {y : Torus d (N₀ * L ^ k)}
    (hy : y ∈ G.layer j) :
    ((Finset.univ.filter fun x : G.Ω 1 => (x : Torus d (N₀ * L ^ k)) ∈ G.blk j y).card : ℝ) =
      ((L : ℝ) ^ j) ^ d := by
  rw [← card_blk G j hjk y]
  congr 1
  rw [← Finset.card_map (Function.Embedding.subtype _)]
  congr 1
  ext x
  simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
    Function.Embedding.coe_subtype]
  constructor
  · rintro ⟨z, hz, rfl⟩; exact hz
  · intro hx; exact ⟨⟨x, blk_subset_Ω G hj1 hjk hy hx⟩, hx, rfl⟩

theorem star_indVec_dot (j : ℕ) (y : Torus d (N₀ * L ^ k)) (i : Fin N)
    (w : G.Ω 1 × Fin N → ℂ) :
    star (indVec G j y i) ⬝ᵥ w = ∑ x ∈ G.blk j y, zeroExt (G.Ω 1) (comp G w i) x := by
  have h1 : star (indVec G j y i) ⬝ᵥ w =
      ∑ x : G.Ω 1, if (x : Torus d (N₀ * L ^ k)) ∈ G.blk j y then w (x, i) else 0 := by
    simp only [dotProduct, Fintype.sum_prod_type, Pi.star_apply, indVec]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.sum_eq_single i]
    · by_cases hx : (x : Torus d (N₀ * L ^ k)) ∈ G.blk j y <;> simp [hx]
    · intro i' _ hi'; simp [hi']
    · simp
  rw [h1]
  set g : Torus d (N₀ * L ^ k) → ℂ := fun x =>
    if x ∈ G.blk j y then zeroExt (G.Ω 1) (comp G w i) x else 0 with hg
  have h2 : ∑ x : G.Ω 1, g x = ∑ x : G.Ω 1, if (x : Torus d (N₀ * L ^ k)) ∈ G.blk j y
      then w (x, i) else 0 := by
    refine Finset.sum_congr rfl fun x _ => ?_
    simp only [hg]
    by_cases hx : (x : Torus d (N₀ * L ^ k)) ∈ G.blk j y
    · simp [hx, zeroExt_mem, comp]
    · simp [hx]
  rw [← h2, ← Green.sum_eq_sum_subtype (G.Ω 1) g (fun x hx => by
    simp only [hg]; split_ifs <;> simp [zeroExt_not_mem _ _ hx])]
  simp only [hg]
  rw [← Finset.sum_filter]
  congr 1
  ext x; simp

theorem sqNorm_indVec_sum {j : ℕ} (hj1 : 1 ≤ j) (hjk : j ≤ k) {y : Torus d (N₀ * L ^ k)}
    (hy : y ∈ G.layer j) (i₀ : Fin N) :
    ∑ i, Green.sqNorm (comp G (indVec G j y i₀) i) = ((L : ℝ) ^ j) ^ d := by
  have : ∀ i, Green.sqNorm (comp G (indVec G j y i₀) i) =
      if i = i₀ then ((L : ℝ) ^ j) ^ d else 0 := by
    intro i
    by_cases hi : i = i₀
    · simp only [hi, ↓reduceIte]
      rw [← card_blk_sub G hj1 hjk hy]
      unfold Green.sqNorm comp indVec
      rw [← Finset.sum_boole]
      refine Finset.sum_congr rfl fun x _ => ?_
      by_cases hx : (x : Torus d (N₀ * L ^ k)) ∈ G.blk j y <;> simp [hx]
    · simp only [hi, ↓reduceIte]
      unfold Green.sqNorm comp indVec
      exact Finset.sum_eq_zero fun x _ => by simp [hi]
  simp [this]

end Kernel

section KernelBound

variable {G : GeneratingSet d L N₀ k ϱ} {a : ℕ → ℝ} {ν : ℝ} {α : G.Ω 1 → ℂ} {δ : ℝ}
  {φ : Torus d (N₀ * L ^ k) → Fin N → ℂ}

theorem norm_blockSum_le {y : Torus d (N₀ * L ^ k)}
    (u : G.Ω 1 × Fin N → ℂ) (i : Fin N) :
    ‖∑ x ∈ G.blk k y, zeroExt (G.Ω 1) (comp G u i) x‖ ≤
      Real.sqrt (((L : ℝ) ^ k) ^ d) * Real.sqrt (blkNormSq G u k y) := by
  calc _ ≤ ∑ x ∈ G.blk k y, ‖zeroExt (G.Ω 1) (comp G u i) x‖ := norm_sum_le _ _
    _ = ∑ x ∈ G.blk k y, 1 * ‖zeroExt (G.Ω 1) (comp G u i) x‖ :=
        Finset.sum_congr rfl fun _ _ => (one_mul _).symm
    _ ≤ Real.sqrt (∑ x ∈ G.blk k y, (1 : ℝ) ^ 2) *
          Real.sqrt (∑ x ∈ G.blk k y, ‖zeroExt (G.Ω 1) (comp G u i) x‖ ^ 2) :=
        Real.sum_mul_le_sqrt_mul_sqrt _ _ _
    _ ≤ Real.sqrt (((L : ℝ) ^ k) ^ d) * Real.sqrt (blkNormSq G u k y) := by
        have h1 : ∑ x ∈ G.blk k y, (1 : ℝ) ^ 2 = ((L : ℝ) ^ k) ^ d := by
          simp [card_blk G k le_rfl y]
        rw [h1]
        refine mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ?_) (Real.sqrt_nonneg _)
        unfold blkNormSq
        refine Finset.sum_le_sum fun x _ => ?_
        exact Finset.single_le_sum (f := fun i' => ‖zeroExt (G.Ω 1) (comp G u i') x‖ ^ 2)
          (fun _ _ => sq_nonneg _) (Finset.mem_univ i)

variable (St : Standing G a ν α δ φ)

include St

/-- **G-1(d)(3), kernel decay.** For unit blocks `y, y'` (layer `k`) and every `0 ≤ t ≤ d(y, y')`,
`|(Q_k Π Q_k^*)(y, y')| ≤ (50 L / c) e^{-(ε/2) t}` (componentwise; here `ε = ε₀` is the Agmon
rate and `ϱ` satisfies the separation condition `L ≤ exp ((ε/2)(ϱ - 1))`). -/
theorem unitKernel_bound (hk : 1 ≤ k) {y y' : Torus d (N₀ * L ^ k)} (hy : y ∈ G.layer k)
    (hy' : y' ∈ G.layer k) {t : ℝ} (ht0 : 0 ≤ t) (ht : ENNReal.ofReal t ≤ G.pathDist y y')
    {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ agmonRate d) (hϱ : 1 ≤ ϱ)
    (hsep : (L : ℝ) ≤ Real.exp (ε / 2 * (ϱ - 1))) (i i₀ : Fin N) :
    ‖unitKernel G (constrainedOp (dirichletOperator G a ν α)⁻¹ (restrictField G φ)) y y' i i₀‖ ≤
      50 * L / poincareConst d * Real.exp (-(ε / 2 * t)) := by
  have hL0 : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hsupp : ∀ (x : G.Ω 1) (i' : Fin N), indVec G k y' i₀ (x, i') ≠ 0 →
      jBlock d L N₀ k k x = jBlock d L N₀ k k y' := by
    intro x i' h
    by_cases hx : (x : Torus d (N₀ * L ^ k)) ∈ G.blk k y'
    · exact G.mem_blk.1 hx
    · simp [indVec, hx] at h
  have hG := constrained_G2v St hk le_rfl hk le_rfl hy hy' hsupp ht0 ht hε0 hε1 hϱ hsep
  rw [sqNorm_indVec_sum G hk le_rfl hy' i₀] at hG
  set Nn := blkNormSq G (constrainedOp (dirichletOperator G a ν α)⁻¹ (restrictField G φ) *ᵥ
    indVec G k y' i₀) k y with hNn
  have hY0 := blkGradSq_nonneg G (constrainedOp (dirichletOperator G a ν α)⁻¹
    (restrictField G φ) *ᵥ indVec G k y' i₀) k y
  have hsN : Real.sqrt Nn ≤ 50 * L / poincareConst d * Real.exp (-(ε / 2 * t)) *
      ((L : ℝ) ^ k) ^ 2 * Real.sqrt (((L : ℝ) ^ k) ^ d) := by
    have : 0 ≤ (L : ℝ) ^ k * Real.sqrt (blkGradSq G (constrainedOp (dirichletOperator G a ν α)⁻¹
        (restrictField G φ) *ᵥ indVec G k y' i₀) k y) := by positivity
    linarith
  have hsum := norm_blockSum_le (G := G) (y := y) (constrainedOp (dirichletOperator G a ν α)⁻¹
    (restrictField G φ) *ᵥ indVec G k y' i₀) i
  unfold unitKernel
  rw [norm_mul, star_indVec_dot, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  have hLd : 0 ≤ ((L : ℝ) ^ k) ^ d := by positivity
  have hsq : Real.sqrt (((L : ℝ) ^ k) ^ d) * Real.sqrt (((L : ℝ) ^ k) ^ d) = ((L : ℝ) ^ k) ^ d :=
    Real.mul_self_sqrt hLd
  have hc0 := poincareConst_pos St.pos
  have hbd : ‖∑ x ∈ G.blk k y, zeroExt (G.Ω 1) (comp G (constrainedOp
      (dirichletOperator G a ν α)⁻¹ (restrictField G φ) *ᵥ indVec G k y' i₀) i) x‖ ≤
      50 * L / poincareConst d * Real.exp (-(ε / 2 * t)) * ((L : ℝ) ^ k) ^ 2 *
        ((L : ℝ) ^ k) ^ d := by
    calc _ ≤ Real.sqrt (((L : ℝ) ^ k) ^ d) * Real.sqrt Nn := hsum
      _ ≤ Real.sqrt (((L : ℝ) ^ k) ^ d) * (50 * L / poincareConst d * Real.exp (-(ε / 2 * t)) *
          ((L : ℝ) ^ k) ^ 2 * Real.sqrt (((L : ℝ) ^ k) ^ d)) :=
          mul_le_mul_of_nonneg_left hsN (Real.sqrt_nonneg _)
      _ = 50 * L / poincareConst d * Real.exp (-(ε / 2 * t)) * ((L : ℝ) ^ k) ^ 2 *
          (Real.sqrt (((L : ℝ) ^ k) ^ d) * Real.sqrt (((L : ℝ) ^ k) ^ d)) := by ring
      _ = _ := by rw [hsq]
  have hpow : ((L : ℝ) ^ (k * d + 2 * k))⁻¹ * (((L : ℝ) ^ k) ^ 2 * ((L : ℝ) ^ k) ^ d) = 1 := by
    have : ((L : ℝ) ^ k) ^ 2 * ((L : ℝ) ^ k) ^ d = (L : ℝ) ^ (k * d + 2 * k) := by
      rw [← pow_mul, ← pow_mul, ← pow_add]; congr 1; ring
    rw [this]; field_simp
  calc _ ≤ ((L : ℝ) ^ (k * d + 2 * k))⁻¹ * (50 * L / poincareConst d * Real.exp (-(ε / 2 * t)) *
        ((L : ℝ) ^ k) ^ 2 * ((L : ℝ) ^ k) ^ d) :=
        mul_le_mul_of_nonneg_left hbd (by positivity)
    _ = 50 * L / poincareConst d * Real.exp (-(ε / 2 * t)) *
        (((L : ℝ) ^ (k * d + 2 * k))⁻¹ * (((L : ℝ) ^ k) ^ 2 * ((L : ℝ) ^ k) ^ d)) := by ring
    _ = _ := by rw [hpow, mul_one]

end KernelBound

end Balaban.Multiscale
