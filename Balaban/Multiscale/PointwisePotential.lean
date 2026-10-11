/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Multiscale.PointwiseLift

/-!
# Lemma P: the equation `-Δ u = g` and the potential bound (GREEN.md (4.4))

For `u` with `H_D(α) u = f` and `ũ` its zero extension, at every `p ∈ Ω₁`

`-Δ ũ(p) = f̃(p) - (ν + α(p)) ũ(p) - (Q* a Q ũ)(p)`   (`laplacian_eq_of_dirichlet`),

and, if `‖ũ‖ ≤ M` on the `m`-block of `p` (`m` the layer of `p`),

`|(-Δ ũ)(p)| ≤ |f̃(p)| + 4 ℓ(p)⁻² M`   (`laplacian_bound`),

provided `ν ℓ(p)² ≤ 1` and `|α(p)| ≤ c₁ ℓ(p)⁻²/2` with `c₁ ≤ 1/2`.
-/

@[expose] public section

noncomputable section

namespace Balaban.Multiscale

open Finset Matrix Balaban

variable {d L N₀ k : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}

theorem latticeLaplacian_mulVec_complex (ν : ℝ) (ψ : Torus d (N₀ * L ^ k) → ℂ)
    (p : Torus d (N₀ * L ^ k)) :
    ((latticeLaplacian d (N₀ * L ^ k) ν).map (algebraMap ℝ ℂ) *ᵥ ψ) p =
      ∑ μ : Fin d, (2 * ψ p - ψ (p + Pi.single μ 1) - ψ (p - Pi.single μ 1)) + ν * ψ p := by
  apply Complex.ext
  · rw [re_mulVec_map, latticeLaplacian_mulVec]
    simp [Complex.re_sum]
  · rw [im_mulVec_map, latticeLaplacian_mulVec]
    simp [Complex.im_sum]

/-- The equation `H_D(α) u = f` rewritten as a Poisson equation at each point of `Ω₁`. -/
theorem laplacian_eq_of_dirichlet (G : GeneratingSet d L N₀ k ϱ) {a : ℕ → ℝ} {ν : ℝ}
    {α : G.Ω 1 → ℂ} {u f : G.Ω 1 → ℂ} (hu : dirichletOperator G a ν α *ᵥ u = f)
    {p : Torus d (N₀ * L ^ k)} (hp : p ∈ G.Ω 1) :
    ∑ μ : Fin d, (2 * zeroExt (G.Ω 1) u p -
        zeroExt (G.Ω 1) u (p + Pi.single μ 1) - zeroExt (G.Ω 1) u (p - Pi.single μ 1)) =
      f ⟨p, hp⟩ - ν * u ⟨p, hp⟩ - α ⟨p, hp⟩ * u ⟨p, hp⟩ -
        ((avgMatrix G a).map (algebraMap ℝ ℂ) *ᵥ zeroExt (G.Ω 1) u) p := by
  have h := dirichlet_eq G hu ⟨p, hp⟩
  unfold fullMatrix at h
  rw [Matrix.map_add (algebraMap ℝ ℂ) (map_add _), Matrix.add_mulVec, Pi.add_apply,
    latticeLaplacian_mulVec_complex] at h
  have hx : zeroExt (G.Ω 1) u p = u ⟨p, hp⟩ := zeroExt_mem _ _ ⟨p, hp⟩
  rw [hx] at h ⊢
  linear_combination h

theorem avgMatrix_apply_of_layer (G : GeneratingSet d L N₀ k ϱ) (a : ℕ → ℝ) {m : ℕ}
    (hm1 : 1 ≤ m) (hmk : m ≤ k) {p : Torus d (N₀ * L ^ k)} (hpl : p ∈ G.layer m)
    (q : Torus d (N₀ * L ^ k)) :
    avgMatrix G a p q = a m / ((L : ℝ) ^ m) ^ 2 *
      (if q ∈ G.layer m then
        blockProjMatrix d (N₀ * L ^ k) (L ^ m) (N₀ * L ^ (k - m)) p q else 0) := by
  unfold avgMatrix
  rw [Matrix.sum_apply, Finset.sum_eq_single m]
  · rw [Matrix.smul_apply, smul_eq_mul]
    congr 1
    simp only [layerProjMatrix, hpl, true_and]
  · intro j hj hne
    have : p ∉ G.layer j := G.layer_disjoint hm1 hmk (Finset.mem_Icc.1 hj).1
      (Finset.mem_Icc.1 hj).2 (Ne.symm hne) hpl
    simp [layerProjMatrix, this]
  · intro h
    exact absurd (Finset.mem_Icc.2 ⟨hm1, hmk⟩) h

/-- The block-average term of `H_D` is bounded by the sup of `ψ` on the block. -/
theorem avg_row_bound (G : GeneratingSet d L N₀ k ϱ) {a : ℕ → ℝ} (ha : IsAdmissibleWeights k a)
    {p : Torus d (N₀ * L ^ k)} (hp : p ∈ G.Ω 1) (ψ : Torus d (N₀ * L ^ k) → ℂ) {M : ℝ}
    (hM0 : 0 ≤ M)
    (hM : ∀ q, jBlock d L N₀ k (G.layerIndex p) q = jBlock d L N₀ k (G.layerIndex p) p →
      ‖ψ q‖ ≤ M) :
    ‖((avgMatrix G a).map (algebraMap ℝ ℂ) *ᵥ ψ) p‖ ≤ 2 * ((G.spacing p) ^ 2)⁻¹ * M := by
  obtain ⟨hm1, hmk, hpl⟩ := G.layerIndex_spec hp
  set m := G.layerIndex p with hm
  have ham := ha m hm1 hmk
  have hL0 : (0 : ℝ) < (L : ℝ) ^ m := by
    have : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
    positivity
  set cm : ℝ := a m / ((L : ℝ) ^ m) ^ 2 with hcm
  have hcm0 : 0 ≤ cm := div_nonneg (by linarith [ham.1]) (by positivity)
  have hcm2 : cm ≤ 2 * (((L : ℝ) ^ m) ^ 2)⁻¹ := by
    rw [hcm, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right ham.2 (by positivity)
  have hrow : ∀ q, (avgMatrix G a p q) ≤ cm * blockProjMatrix d (N₀ * L ^ k) (L ^ m)
      (N₀ * L ^ (k - m)) p q := by
    intro q
    rw [avgMatrix_apply_of_layer G a hm1 hmk hpl, ← hcm]
    split_ifs
    · exact le_rfl
    · rw [mul_zero]
      exact mul_nonneg hcm0 (blockProjMatrix_nonneg m p q)
  have hnn : ∀ q, 0 ≤ avgMatrix G a p q := by
    intro q
    rw [avgMatrix_apply_of_layer G a hm1 hmk hpl, ← hcm]
    split_ifs
    · exact mul_nonneg hcm0 (blockProjMatrix_nonneg m p q)
    · simp
  have hsupp : ∀ q, avgMatrix G a p q ≠ 0 → ‖ψ q‖ ≤ M := by
    intro q hq
    apply hM
    rw [avgMatrix_apply_of_layer G a hm1 hmk hpl, ← hcm] at hq
    by_contra hne
    apply hq
    have : blockProjMatrix d (N₀ * L ^ k) (L ^ m) (N₀ * L ^ (k - m)) p q = 0 := by
      unfold blockProjMatrix
      have : blockMap (L ^ m) (N₀ * L ^ (k - m)) p ≠ blockMap (L ^ m) (N₀ * L ^ (k - m)) q :=
        fun h => hne h.symm
      simp [this]
    split_ifs <;> simp [this]
  calc _ = ‖∑ q, ((avgMatrix G a p q : ℝ) : ℂ) * ψ q‖ := by
        congr 1
    _ ≤ ∑ q, ‖((avgMatrix G a p q : ℝ) : ℂ) * ψ q‖ := norm_sum_le _ _
    _ ≤ ∑ q, avgMatrix G a p q * M := by
        refine Finset.sum_le_sum fun q _ => ?_
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hnn q)]
        by_cases h0 : avgMatrix G a p q = 0
        · simp [h0]
        · exact mul_le_mul_of_nonneg_left (hsupp q h0) (hnn q)
    _ = (∑ q, avgMatrix G a p q) * M := by rw [Finset.sum_mul]
    _ ≤ cm * M := by
        refine mul_le_mul_of_nonneg_right ?_ hM0
        calc ∑ q, avgMatrix G a p q ≤ ∑ q, cm * blockProjMatrix d (N₀ * L ^ k) (L ^ m)
              (N₀ * L ^ (k - m)) p q := Finset.sum_le_sum fun q _ => hrow q
          _ = cm := by rw [← Finset.mul_sum, blockProjMatrix_row hmk, mul_one]
    _ ≤ _ := by
        rw [G.spacing_eq hm1 hmk hpl]
        exact mul_le_mul_of_nonneg_right hcm2 hM0

/-- **(4.4).** The Poisson-equation right-hand side `g = -Δũ` at `p ∈ Ω₁` is bounded by
`|f̃(p)| + 4 ℓ(p)⁻² M` when `‖ũ‖ ≤ M` on the block of `p`. -/
theorem laplacian_bound (G : GeneratingSet d L N₀ k ϱ) {a : ℕ → ℝ} {ν : ℝ} (hν : 0 ≤ ν)
    (hν1 : ν * ((L : ℝ) ^ k) ^ 2 ≤ 1) (ha : IsAdmissibleWeights k a) {α : G.Ω 1 → ℂ}
    (hα : ∀ x, ‖α x‖ ≤ coerciveConst d / (2 * (G.spacing x) ^ 2))
    {u f : G.Ω 1 → ℂ} (hu : dirichletOperator G a ν α *ᵥ u = f)
    {p : Torus d (N₀ * L ^ k)} (hp : p ∈ G.Ω 1) {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ q, jBlock d L N₀ k (G.layerIndex p) q = jBlock d L N₀ k (G.layerIndex p) p →
      ‖zeroExt (G.Ω 1) u q‖ ≤ M) :
    ‖∑ μ : Fin d, (2 * zeroExt (G.Ω 1) u p -
        zeroExt (G.Ω 1) u (p + Pi.single μ 1) - zeroExt (G.Ω 1) u (p - Pi.single μ 1))‖ ≤
      ‖zeroExt (G.Ω 1) f p‖ + 4 * ((G.spacing p) ^ 2)⁻¹ * M := by
  rw [laplacian_eq_of_dirichlet G hu hp]
  have hspk : G.spacing p ≤ (L : ℝ) ^ k := spacing_le G hp
  have hsp0 : 0 < G.spacing p := spacing_pos G
  set s := G.spacing p with hs
  have hfp : zeroExt (G.Ω 1) f p = f ⟨p, hp⟩ := zeroExt_mem _ _ ⟨p, hp⟩
  have hux : ‖u ⟨p, hp⟩‖ ≤ M := by
    have := hM p rfl
    have e : zeroExt (G.Ω 1) u p = u ⟨p, hp⟩ := zeroExt_mem _ _ ⟨p, hp⟩
    rwa [e] at this
  have hν' : ν ≤ (s ^ 2)⁻¹ := by
    rw [← one_div, le_div_iff₀ (by positivity)]
    calc ν * s ^ 2 ≤ ν * ((L : ℝ) ^ k) ^ 2 :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hsp0.le hspk 2) hν
      _ ≤ 1 := hν1
  have hαx : ‖α ⟨p, hp⟩‖ ≤ (s ^ 2)⁻¹ := by
    refine (hα ⟨p, hp⟩).trans ?_
    have h1 : coerciveConst d ≤ 1 / 4 := by
      unfold coerciveConst; linarith [poincareConst_le_half d]
    have : coerciveConst d / (2 * s ^ 2) ≤ (1 / 4) / (2 * s ^ 2) := by
      gcongr
    refine this.trans ?_
    rw [div_le_iff₀ (by positivity)]
    have : (s ^ 2)⁻¹ * (2 * s ^ 2) = 2 := by field_simp
    nlinarith [this]
  have hq := avg_row_bound G ha hp (zeroExt (G.Ω 1) u) hM0 hM
  rw [← hs] at hq
  rw [hfp]
  calc _ ≤ ‖f ⟨p, hp⟩‖ + ‖(ν : ℂ) * u ⟨p, hp⟩‖ + ‖α ⟨p, hp⟩ * u ⟨p, hp⟩‖ +
        ‖((avgMatrix G a).map (algebraMap ℝ ℂ) *ᵥ zeroExt (G.Ω 1) u) p‖ := by
        refine (norm_sub_le _ _).trans ?_
        gcongr
        refine (norm_sub_le _ _).trans ?_
        gcongr
        exact norm_sub_le _ _
    _ ≤ ‖f ⟨p, hp⟩‖ + (s ^ 2)⁻¹ * M + (s ^ 2)⁻¹ * M + 2 * (s ^ 2)⁻¹ * M := by
        gcongr
        · rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hν]
          exact mul_le_mul hν' hux (norm_nonneg _) (by positivity)
        · rw [norm_mul]
          exact mul_le_mul hαx hux (norm_nonneg _) (by positivity)
    _ = _ := by ring

end Balaban.Multiscale
