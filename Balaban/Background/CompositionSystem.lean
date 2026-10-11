/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Background.Composition
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

/-!
# The composed system `𝒮` and its equivalence with (EL) (BACKGROUND.md §6.5, Theorem 6.1 (iii))
-/

@[expose] public section

namespace Balaban.Background

open Balaban.Multiscale Matrix Finset

variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ ϱ' : ℝ}

section Blocks

variable {G : GeneratingSet d L N₀ k ϱ}

theorem blk_zero (z : Torus d (N₀ * L ^ k)) : G.blk 0 z = {z} := by
  ext y
  rw [GeneratingSet.mem_blk, Finset.mem_singleton]
  constructor
  · intro h
    unfold jBlock at h
    funext i
    have := congrFun h i
    simp only [blockMap_apply, blockCoord, pow_zero, Nat.div_one, ZMod.natCast_zmod_val] at this
    exact this
  · intro h; rw [h]

theorem blockMean_zero (w : Torus d (N₀ * L ^ k) → ℂ) (z : Torus d (N₀ * L ^ k)) :
    blockMean G 0 w z = w z := by
  simp [blockMean, blk_zero]

/-- Averaging over nested blocks: if a union `S` of blocks is closed under the blocks
`B_{n(z)}(z)` on which `n` is constant, then averaging the block averages over `S` is the sum. -/
theorem sum_blockMean_nested (G : GeneratingSet d L N₀ k ϱ) (S : Finset (Torus d (N₀ * L ^ k)))
    (n : Torus d (N₀ * L ^ k) → ℕ) (hn : ∀ z, n z ≤ k) (W : Torus d (N₀ * L ^ k) → ℂ)
    (hsub : ∀ z ∈ S, ∀ y ∈ G.blk (n z) z, y ∈ S ∧ n y = n z) :
    ∑ z ∈ S, blockMean G (n z) W z = ∑ z ∈ S, W z := by
  classical
  unfold blockMean
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm' (t' := S) (s' := fun y => G.blk (n y) y)]
  · refine Finset.sum_congr rfl fun y hy => ?_
    have hc : ∀ z ∈ G.blk (n y) y, ((((((L : ℝ) ^ n z) ^ d)⁻¹ : ℝ) : ℂ)) * W y =
        ((((((L : ℝ) ^ n y) ^ d)⁻¹ : ℝ) : ℂ)) * W y := by
      intro z hz
      have : n y = n z := by
        have h1 := hsub y hy z hz
        exact h1.2.symm
      rw [this]
    rw [Finset.sum_congr rfl hc, Finset.sum_const, nsmul_eq_mul]
    have hcard := card_blk_cast G (n y) (hn y) y
    have hL : (L : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne L
    rw [← mul_assoc]
    have : (((G.blk (n y) y).card : ℂ)) * ((((((L : ℝ) ^ n y) ^ d)⁻¹ : ℝ) : ℂ)) = 1 := by
      have h2 : (((G.blk (n y) y).card : ℝ)) * ((((L : ℝ) ^ n y) ^ d)⁻¹) = 1 := by
        rw [hcard]; field_simp
      exact_mod_cast h2
    rw [this, one_mul]
  · intro z y
    constructor
    · rintro ⟨hz, hy⟩
      obtain ⟨hyS, hny⟩ := hsub z hz y hy
      refine ⟨?_, hyS⟩
      rw [GeneratingSet.mem_blk, hny]
      exact (GeneratingSet.mem_blk.1 hy).symm
    · rintro ⟨hz, hy⟩
      obtain ⟨hzS, hnz⟩ := hsub y hy z hz
      refine ⟨hzS, ?_⟩
      rw [GeneratingSet.mem_blk, hnz]
      exact (GeneratingSet.mem_blk.1 hz).symm

end Blocks

/-! ### The system `𝒮` (6.6) -/

section System

variable (G : GeneratingSet d L N₀ k ϱ) (G' : GeneratingSet d L N₀ k ϱ')

/-- `1 / a^{(p)}(B) = ∑_x w_x u_{p - n_x}` of (6.5) for the `p`-block `B` of `x`:
`L^{-pd} ∑_{z ∈ B} 1 / a_{p - n(z)}` (`n(z)` the layer of `z` in `𝔹_j`, `0` off `Ω₁`). -/
noncomputable def invAp (a : ℕ → ℝ) (p : ℕ) (x : Torus d (N₀ * L ^ k)) : ℝ :=
  ((((L : ℝ) ^ p) ^ d)⁻¹) * ∑ z ∈ G'.blk p x, (a (p - G.layerIndex z))⁻¹

/-- The lifted unknown `ψ` extended by `φ̄'` off `Ω₁` (`ψ₀ = φ` on the gap, `Ψ'` outside `Ω'₁`). -/
noncomputable def psiExt (D' : BgData G' N) (φ : G'.Ω 1 × Fin N → ℂ)
    (ψ : Torus d (N₀ * L ^ k) → Fin N → ℂ) (z : Torus d (N₀ * L ^ k)) (i : Fin N) : ℂ := by
  classical
  exact if z ∈ G.Ω 1 then ψ z i else barField G' D'.Ψ φ z i

/-- **The composed system `𝒮`** (6.6; P2 (4.17) at `λ = ∞`), for unknowns `(ψ, φ, α)`, `ψ` a field
(only its values on `Ω₁` matter), `φ : Ω'₁ × [N] → ℂ`, `α : Ω'₁ → ℂ`, weights `a`, mass `ν`, datum
`D'` of `𝔹'_k`:
* `layerConst`: `ψ` is a lifted field of `𝔹_j`;
* `block` (6.3): for `x ∈ Ω₁` with `n < p`,
  `a^{(p)} L^{-2p} (𝒬_B ψ - ψ'_p) + a_n L^{-2n} (ψ_n - Q_n φ) = 0`
  (`B` the `p`-block of `x`, `𝒬_B` the volume average, `a^{(p)} = invAp⁻¹`);
* `compat`: `ψ = ψ'` on `Λ_p ∩ Λ'_p`;
* `site` (6.3'): the Euler–Lagrange equation at each site of `Ω'₁` with the block term of
  `𝔹_j` on `Ω₁` and the composed block term on the gap;
* `constraint`: `φ·φ = 1` on `Ω'₁`. -/
structure IsComposedSystem (a : ℕ → ℝ) (ν : ℝ) (D' : BgData G' N)
    (ψ : Torus d (N₀ * L ^ k) → Fin N → ℂ) (φ : G'.Ω 1 × Fin N → ℂ) (α : G'.Ω 1 → ℂ) :
    Prop where
  layerConst : IsLayerConstant G ψ
  block : ∀ x ∈ G.Ω 1, G.layerIndex x < G'.layerIndex x → ∀ i,
    ((invAp G G' a (G'.layerIndex x) x)⁻¹ / ((L : ℝ) ^ G'.layerIndex x) ^ 2 : ℝ) *
        (blockMean G' (G'.layerIndex x) (fun z => psiExt G G' D' φ ψ z i) x - D'.Ψ x i) +
      ((a (G.layerIndex x) / ((L : ℝ) ^ G.layerIndex x) ^ 2 : ℝ) : ℂ) *
        (ψ x i - blockMean G (G.layerIndex x) (fun y => svec G' φ y i) x) = 0
  compat : ∀ x ∈ G.Ω 1, G.layerIndex x = G'.layerIndex x → ψ x = D'.Ψ x
  site : ∀ (z : G'.Ω 1) (i : Fin N),
    negLap (fun y => barField G' D'.Ψ φ y i) (z : Torus d (N₀ * L ^ k)) +
      (if (z : Torus d (N₀ * L ^ k)) ∈ G.Ω 1 then
        ((a (G.layerIndex z) / ((L : ℝ) ^ G.layerIndex z) ^ 2 : ℝ) : ℂ) *
          (blockMean G (G.layerIndex z) (fun y => svec G' φ y i) z - ψ z i)
      else
        ((invAp G G' a (G'.layerIndex z) z)⁻¹ / ((L : ℝ) ^ G'.layerIndex z) ^ 2 : ℝ) *
          (blockMean G' (G'.layerIndex z) (fun y => psiExt G G' D' φ ψ y i) z - D'.Ψ z i)) +
      ν * (φ (z, i) - D'.h z i) + α z * φ (z, i) = 0
  constraint : ∀ z : G'.Ω 1, ∑ i, φ (z, i) * φ (z, i) = 1

variable {G G'}

/-- The structure of the `p`-block of `x₀ ∈ Ω'₁`: the `𝔹_j`-blocks `B_{n(z)}(z)` of its sites lie
in it and `n` is constant on them. -/
theorem Precedes.block_nested (h : Precedes G G') {x₀ : Torus d (N₀ * L ^ k)} (hx₀ : x₀ ∈ G'.Ω 1) :
    ∀ z ∈ G'.blk (G'.layerIndex x₀) x₀, ∀ y ∈ G.blk (G.layerIndex z) z,
      y ∈ G'.blk (G'.layerIndex x₀) x₀ ∧ G.layerIndex y = G.layerIndex z := by
  intro z hz y hy
  by_cases hzΩ : z ∈ G.Ω 1
  · obtain ⟨hp1, hpk, hxp⟩ := G'.layerIndex_spec hx₀
    obtain ⟨-, e1, -, e3, -⟩ := h.block_compat hzΩ hy
    refine ⟨?_, e1⟩
    have hzp : G'.layerIndex z = G'.layerIndex x₀ := by
      have hz' : z ∈ G'.layer (G'.layerIndex x₀) :=
        (G'.mem_layer_iff hp1 hpk (GeneratingSet.mem_blk.1 hz).symm).1 hxp
      exact G'.layerIndex_eq hp1 hpk hz'
    have hle := h.layerIndex_le hzΩ
    have hyz := jBlock_eq_of_le (hle.trans_eq hzp) hpk (GeneratingSet.mem_blk.1 hy)
    rw [GeneratingSet.mem_blk, hyz]
    exact GeneratingSet.mem_blk.1 hz
  · have hn : G.layerIndex z = 0 := layerIndex_of_not_mem G hzΩ
    rw [hn, blk_zero] at hy
    have : y = z := by simpa using hy
    subst this
    exact ⟨hz, rfl⟩

/-- On the `p`-block of `x₀ ∈ Ω'₁`, the extended composed field has the form
`Q_{n(z)} φ (z) + a_p (u_p - u_{p-n(z)}) (Ψ'_p - Q_p φ)` (this uses (C1)). -/
theorem psiExt_compose_block (h : Precedes G G') (a : ℕ → ℝ)
    (hC1 : ∀ n p : ℕ, n ≤ p → ((L : ℝ) ^ n) ^ 2 / ((L : ℝ) ^ p) ^ 2 * (a n)⁻¹ =
      (a p)⁻¹ - (a (p - n))⁻¹)
    (D' : BgData G' N) (φ : G'.Ω 1 × Fin N → ℂ) {x₀ : Torus d (N₀ * L ^ k)}
    (hx₀ : x₀ ∈ G'.Ω 1) {z : Torus d (N₀ * L ^ k)} (hz : z ∈ G'.blk (G'.layerIndex x₀) x₀)
    (i : Fin N) :
    psiExt G G' D' φ (fun y j => composeField G G' a φ D'.Ψ y j) z i =
      blockMean G (G.layerIndex z) (fun y => svec G' φ y i) z +
        ((a (G'.layerIndex x₀) * ((a (G'.layerIndex x₀))⁻¹ -
            (a (G'.layerIndex x₀ - G.layerIndex z))⁻¹) : ℝ) : ℂ) *
          (D'.Ψ x₀ i - blockMean G' (G'.layerIndex x₀) (fun y => svec G' φ y i) x₀) := by
  classical
  obtain ⟨hp1, hpk, hxp⟩ := G'.layerIndex_spec hx₀
  have hz' : z ∈ G'.layer (G'.layerIndex x₀) :=
    (G'.mem_layer_iff hp1 hpk (GeneratingSet.mem_blk.1 hz).symm).1 hxp
  have hzp : G'.layerIndex z = G'.layerIndex x₀ := G'.layerIndex_eq hp1 hpk hz'
  have hzΩ' : z ∈ G'.Ω 1 := G'.layer_subset hp1 hpk hz'
  by_cases hzΩ : z ∈ G.Ω 1
  · unfold psiExt
    simp only [hzΩ, ↓reduceIte]
    show composeField G G' a φ D'.Ψ z i = _
    rw [composeField_of_mem a φ D'.Ψ hzΩ, hzp]
    have hq : blockMean G' (G'.layerIndex x₀) (fun y => svec G' φ y i) z =
        blockMean G' (G'.layerIndex x₀) (fun y => svec G' φ y i) x₀ :=
      blockMean_congr _ (blk_eq_of_mem hz)
    have hΨ : D'.Ψ z i = D'.Ψ x₀ i := by
      rw [D'.Ψ_layerConst _ hp1 hpk x₀ hxp z hz]
    rw [hq, hΨ]
    have hle : G.layerIndex z ≤ G'.layerIndex x₀ := hzp ▸ h.layerIndex_le hzΩ
    have := hC1 _ _ hle
    have e : a (G'.layerIndex x₀) / a (G.layerIndex z) *
        (((L : ℝ) ^ G.layerIndex z) ^ 2 / ((L : ℝ) ^ G'.layerIndex x₀) ^ 2) =
        a (G'.layerIndex x₀) * ((a (G'.layerIndex x₀))⁻¹ - (a (G'.layerIndex x₀ - G.layerIndex z))⁻¹) := by
      rw [← this]; ring
    rw [e]
  · have hn : G.layerIndex z = 0 := layerIndex_of_not_mem G hzΩ
    unfold psiExt
    simp only [hzΩ, ↓reduceIte]
    rw [hn, blockMean_zero]
    simp [barField, svec, zeroExt, hzΩ']

theorem layerIndex_le_k (G : GeneratingSet d L N₀ k ϱ) (z : Torus d (N₀ * L ^ k)) :
    G.layerIndex z ≤ k := by
  by_cases hz : z ∈ G.Ω 1
  · exact (G.layerIndex_spec hz).2.1
  · rw [layerIndex_of_not_mem G hz]; exact Nat.zero_le _

theorem blockMean_const (G : GeneratingSet d L N₀ k ϱ) {p : ℕ} (hp : p ≤ k) (c : ℂ)
    (x : Torus d (N₀ * L ^ k)) : blockMean G p (fun _ => c) x = c := by
  unfold blockMean
  rw [Finset.sum_const, nsmul_eq_mul]
  have hcard := card_blk_cast G p hp x
  have hL : (L : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne L
  have h2 : (((G.blk p x).card : ℝ)) * ((((L : ℝ) ^ p) ^ d)⁻¹) = 1 := by
    rw [hcard]; field_simp
  have : (((G.blk p x).card : ℂ)) * ((((((L : ℝ) ^ p) ^ d)⁻¹ : ℝ) : ℂ)) = 1 := by
    exact_mod_cast h2
  calc _ = (((G.blk p x).card : ℂ)) * ((((((L : ℝ) ^ p) ^ d)⁻¹ : ℝ) : ℂ)) * c := by ring
    _ = c := by rw [this, one_mul]

/-- **The key averaging identity** (§6.5): for the composed field,
`𝒬_B ψ - ψ'_p = a_p (1/a^{(p)}) (Q_p φ - ψ'_p)`. -/
theorem blockMean_psiExt_compose (h : Precedes G G') (a : ℕ → ℝ)
    (hC1 : ∀ n p : ℕ, n ≤ p → ((L : ℝ) ^ n) ^ 2 / ((L : ℝ) ^ p) ^ 2 * (a n)⁻¹ =
      (a p)⁻¹ - (a (p - n))⁻¹)
    (D' : BgData G' N) (φ : G'.Ω 1 × Fin N → ℂ) {x₀ : Torus d (N₀ * L ^ k)}
    (hx₀ : x₀ ∈ G'.Ω 1) (hap : a (G'.layerIndex x₀) ≠ 0) (i : Fin N) :
    blockMean G' (G'.layerIndex x₀)
        (fun y => psiExt G G' D' φ (fun y j => composeField G G' a φ D'.Ψ y j) y i) x₀ -
      D'.Ψ x₀ i =
    ((a (G'.layerIndex x₀) * invAp G G' a (G'.layerIndex x₀) x₀ : ℝ) : ℂ) *
      (blockMean G' (G'.layerIndex x₀) (fun y => svec G' φ y i) x₀ - D'.Ψ x₀ i) := by
  classical
  obtain ⟨hp1, hpk, hxp⟩ := G'.layerIndex_spec hx₀
  set p := G'.layerIndex x₀ with hp
  set S := G'.blk p x₀ with hS
  set Qp := blockMean G' p (fun y => svec G' φ y i) x₀ with hQp
  set T := D'.Ψ x₀ i - Qp with hT
  have hL : (L : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne L
  have hKpos : ((((L : ℝ) ^ p) ^ d)) ≠ 0 := by positivity
  have hpt : ∀ z ∈ S, psiExt G G' D' φ (fun y j => composeField G G' a φ D'.Ψ y j) z i =
      blockMean G (G.layerIndex z) (fun y => svec G' φ y i) z +
        ((a p * ((a p)⁻¹ - (a (p - G.layerIndex z))⁻¹) : ℝ) : ℂ) * T :=
    fun z hz => psiExt_compose_block h a hC1 D' φ hx₀ hz i
  have hnest := sum_blockMean_nested G S G.layerIndex (layerIndex_le_k G)
    (fun y => svec G' φ y i) (h.block_nested hx₀)
  have hcard := card_blk_cast G' p hpk x₀
  have hF : ∑ z ∈ S, psiExt G G' D' φ (fun y j => composeField G G' a φ D'.Ψ y j) z i =
      (∑ z ∈ S, svec G' φ z i) + ((∑ z ∈ S, a p * ((a p)⁻¹ - (a (p - G.layerIndex z))⁻¹) : ℝ) : ℂ)
        * T := by
    rw [Finset.sum_congr rfl hpt, Finset.sum_add_distrib, hnest]
    push_cast
    rw [Finset.sum_mul]
  have hc : ∑ z ∈ S, a p * ((a p)⁻¹ - (a (p - G.layerIndex z))⁻¹) =
      (S.card : ℝ) - a p * ∑ z ∈ S, (a (p - G.layerIndex z))⁻¹ := by
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const,
      nsmul_eq_mul, mul_inv_cancel₀ hap]
    ring
  have hua : invAp G G' a p x₀ = ((((L : ℝ) ^ p) ^ d)⁻¹) * ∑ z ∈ S, (a (p - G.layerIndex z))⁻¹ := rfl
  unfold blockMean at hQp ⊢
  rw [hF, hc, hua]
  set X := ∑ z ∈ S, (a (p - G.layerIndex z))⁻¹ with hX
  set W := ∑ z ∈ S, svec G' φ z i with hW
  have hK1 : (S.card : ℝ) * ((((L : ℝ) ^ p) ^ d)⁻¹) = 1 := by
    rw [hcard]; field_simp
  generalize ((((L : ℝ) ^ p) ^ d)⁻¹) = K at *
  have hKc1 : ((S.card : ℝ) : ℂ) * (K : ℂ) = 1 := by exact_mod_cast hK1
  rw [hQp] at hT
  push_cast
  simp only [hT, hQp]
  linear_combination (D'.Ψ x₀ i - (K : ℂ) * W) * hKc1

/-- The residual of the linear equation of (EL) in "site form": the Laplacian of the extension
`φ̄` plus the block term plus the mass and multiplier terms. -/
theorem elResidual_site (G : GeneratingSet d L N₀ k ϱ) (a : ℕ → ℝ) (ν : ℝ) (D : BgData G N)
    (φ : G.Ω 1 × Fin N → ℂ) (α : G.Ω 1 → ℂ) (z : G.Ω 1) (i : Fin N) :
    elResidual G a ν D φ α (z, i) =
      negLap (fun y => barField G D.Ψ φ y i) (z : Torus d (N₀ * L ^ k)) +
        ((a (G.layerIndex z) / ((L : ℝ) ^ G.layerIndex z) ^ 2 : ℝ) : ℂ) *
          (blockMean G (G.layerIndex z) (fun y => svec G φ y i) z - D.Ψ z i) +
        ν * (φ (z, i) - D.h z i) + α z * φ (z, i) := by
  classical
  unfold elResidual source
  simp only [Pi.sub_apply]
  rw [liftOp_mulVec, dirichlet_apply]
  have hl := negLap_sub_boundary G D.Ψ φ i z
  have hz : zeroExt (G.Ω 1) (fun q => φ (q, i)) (z : Torus d (N₀ * L ^ k)) = φ (z, i) :=
    zeroExt_mem _ _ z
  have hbz : barField G D.Ψ φ (z : Torus d (N₀ * L ^ k)) i = φ (z, i) := by
    simp [barField]
  have hbl : blockTerm G a (zeroExt (G.Ω 1) (fun q => φ (q, i))) (z : Torus d (N₀ * L ^ k)) =
      ((a (G.layerIndex z) / ((L : ℝ) ^ G.layerIndex z) ^ 2 : ℝ) : ℂ) *
        blockMean G (G.layerIndex z) (fun y => svec G φ y i) z := rfl
  have hq : qStar G a D.Ψ (z, i) =
      ((a (G.layerIndex z) / ((L : ℝ) ^ G.layerIndex z) ^ 2 : ℝ) : ℂ) * D.Ψ z i := rfl
  have hneg : negLap (fun y => barField G D.Ψ φ y i) (z : Torus d (N₀ * L ^ k)) =
      ∑ μ : Fin d, (2 * φ (z, i) - barField G D.Ψ φ ((z : Torus d (N₀ * L ^ k)) + Pi.single μ 1) i -
        barField G D.Ψ φ ((z : Torus d (N₀ * L ^ k)) - Pi.single μ 1) i) := by
    unfold negLap
    simp only [hbz]
  rw [hneg, ← hl, hbl, hq]
  ring

/-- If one site of the `p`-block of `x₀ ∈ Ω'₁` has `n < p`, all do (a `p`-block lies in a layer
of `𝔹_j` or is disjoint from the layer `p`). -/
theorem Precedes.block_lt (h : Precedes G G') {x₀ : Torus d (N₀ * L ^ k)} (hx₀ : x₀ ∈ G'.Ω 1)
    {z₀ : Torus d (N₀ * L ^ k)} (hz₀ : z₀ ∈ G'.blk (G'.layerIndex x₀) x₀)
    (hlt : G.layerIndex z₀ < G'.layerIndex x₀) :
    ∀ z ∈ G'.blk (G'.layerIndex x₀) x₀, G.layerIndex z < G'.layerIndex x₀ := by
  intro z hz
  obtain ⟨hp1, hpk, hxp⟩ := G'.layerIndex_spec hx₀
  have hz' : z ∈ G'.layer (G'.layerIndex x₀) :=
    (G'.mem_layer_iff hp1 hpk (GeneratingSet.mem_blk.1 hz).symm).1 hxp
  have hzp : G'.layerIndex z = G'.layerIndex x₀ := G'.layerIndex_eq hp1 hpk hz'
  by_contra hge
  push Not at hge
  have hzΩ : z ∈ G.Ω 1 := by
    by_contra hn
    rw [layerIndex_of_not_mem G hn] at hge
    omega
  have hle := hzp ▸ h.layerIndex_le hzΩ
  have heq : G.layerIndex z = G'.layerIndex x₀ := le_antisymm hle hge
  obtain ⟨hn1, hnk, hzn⟩ := G.layerIndex_spec hzΩ
  rw [heq] at hzn
  have hb : jBlock d L N₀ k (G'.layerIndex x₀) z = jBlock d L N₀ k (G'.layerIndex x₀) z₀ :=
    (GeneratingSet.mem_blk.1 hz).trans (GeneratingSet.mem_blk.1 hz₀).symm
  have hz₀n : z₀ ∈ G.layer (G'.layerIndex x₀) := (G.mem_layer_iff hp1 hpk hb).1 hzn
  have := G.layerIndex_eq hp1 hpk hz₀n
  omega

/-- Positivity of `1 / a^{(p)}` on a block without a full `𝔹_j`-layer. -/
theorem invAp_pos (h : Precedes G G') (a : ℕ → ℝ) (hpos : ∀ r, 1 ≤ r → 0 < a r)
    {x₀ : Torus d (N₀ * L ^ k)} (hx₀ : x₀ ∈ G'.Ω 1)
    (hlt : G.layerIndex x₀ < G'.layerIndex x₀) :
    0 < invAp G G' a (G'.layerIndex x₀) x₀ := by
  have hself : x₀ ∈ G'.blk (G'.layerIndex x₀) x₀ := GeneratingSet.mem_blk.2 rfl
  have hall := h.block_lt hx₀ hself hlt
  unfold invAp
  have hL : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  refine mul_pos (by positivity) (Finset.sum_pos (fun z hz => ?_) ⟨x₀, hself⟩)
  have := hall z hz
  exact inv_pos.2 (hpos _ (by omega))

/-- The block-mean of a field of the form `Q_{n(z)} φ (z) + r(z) τ` on a `p`-block. -/
theorem blockMean_decomp (h : Precedes G G') {x₀ : Torus d (N₀ * L ^ k)} (hx₀ : x₀ ∈ G'.Ω 1)
    (W : Torus d (N₀ * L ^ k) → ℂ) (F : Torus d (N₀ * L ^ k) → ℂ) (r : Torus d (N₀ * L ^ k) → ℝ)
    (τ : ℂ)
    (hF : ∀ z ∈ G'.blk (G'.layerIndex x₀) x₀,
      F z = blockMean G (G.layerIndex z) W z + (r z : ℂ) * τ) :
    blockMean G' (G'.layerIndex x₀) F x₀ =
      blockMean G' (G'.layerIndex x₀) W x₀ +
        ((((((L : ℝ) ^ G'.layerIndex x₀) ^ d)⁻¹) * ∑ z ∈ G'.blk (G'.layerIndex x₀) x₀, r z : ℝ) : ℂ) *
          τ := by
  obtain ⟨hp1, hpk, hxp⟩ := G'.layerIndex_spec hx₀
  have hnest := sum_blockMean_nested G (G'.blk (G'.layerIndex x₀) x₀) G.layerIndex
    (layerIndex_le_k G) W (h.block_nested hx₀)
  unfold blockMean
  rw [Finset.sum_congr rfl hF, Finset.sum_add_distrib, hnest]
  push_cast
  rw [← Finset.sum_mul]
  ring

/-- `c_n κ = c_p`: `a_n L^{-2n} · (a_p / a_n) L^{2(n-p)} = a_p L^{-2p}` (the identity behind
(6.3)–(6.4)), in `ℂ`. -/
theorem coeff_mul_kappa (a : ℕ → ℝ) {n p : ℕ} (han : a n ≠ 0) :
    ((a n / ((L : ℝ) ^ n) ^ 2 : ℝ) : ℂ) *
      ((a p / a n * (((L : ℝ) ^ n) ^ 2 / ((L : ℝ) ^ p) ^ 2) : ℝ) : ℂ) =
      ((a p / ((L : ℝ) ^ p) ^ 2 : ℝ) : ℂ) := by
  have hL : (L : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne L
  rw [← Complex.ofReal_mul]
  congr 1
  field_simp

/-- **Theorem 6.1 (iii), existence**: the composed field with `(φ', α')` solves `𝒮`. -/
theorem isComposedSystem_of_isEL (h : Precedes G G') (a : ℕ → ℝ)
    (hC1 : ∀ n p : ℕ, n ≤ p → ((L : ℝ) ^ n) ^ 2 / ((L : ℝ) ^ p) ^ 2 * (a n)⁻¹ =
      (a p)⁻¹ - (a (p - n))⁻¹)
    (hpos : ∀ r, 1 ≤ r → 0 < a r) (ν : ℝ) (D' : BgData G' N) {φ : G'.Ω 1 × Fin N → ℂ}
    {α : G'.Ω 1 → ℂ} (hEL : IsEL G' a ν D' φ α) :
    IsComposedSystem G G' a ν D' (fun x i => composeField G G' a φ D'.Ψ x i) φ α := by
  have hL : (L : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne L
  have hres : ∀ (z : G'.Ω 1) (i : Fin N), elResidual G' a ν D' φ α (z, i) = 0 := by
    intro z i
    unfold elResidual; rw [hEL.1]; simp
  refine ⟨composeField_layerConst h a φ D'.Ψ_layerConst, ?_, ?_, ?_, hEL.2⟩
  · intro x hx hlt i
    obtain ⟨hn1, hnk, hxn⟩ := G.layerIndex_spec hx
    have hx' := h.mem_Ω1 hx
    have hua := invAp_pos h a hpos hx' hlt
    have hap : a (G'.layerIndex x) ≠ 0 :=
      (hpos _ (G'.layerIndex_spec hx').1).ne'
    have han : a (G.layerIndex x) ≠ 0 := (hpos _ hn1).ne'
    have KI := blockMean_psiExt_compose h a hC1 D' φ hx' hap i
    have hcf := composeField_of_mem a φ D'.Ψ hx i
    have e2 := coeff_mul_kappa (L := L) a (n := G.layerIndex x) (p := G'.layerIndex x) han
    have e1 : (((invAp G G' a (G'.layerIndex x) x)⁻¹ / ((L : ℝ) ^ G'.layerIndex x) ^ 2 : ℝ) : ℂ) *
        ((a (G'.layerIndex x) * invAp G G' a (G'.layerIndex x) x : ℝ) : ℂ) =
        ((a (G'.layerIndex x) / ((L : ℝ) ^ G'.layerIndex x) ^ 2 : ℝ) : ℂ) := by
      rw [← Complex.ofReal_mul]
      congr 1
      field_simp
    rw [KI, hcf]
    linear_combination
      (blockMean G' (G'.layerIndex x) (fun y => svec G' φ y i) x - D'.Ψ x i) * e1 +
      (D'.Ψ x i - blockMean G' (G'.layerIndex x) (fun y => svec G' φ y i) x) * e2
  · intro x hx hnp
    funext i
    show composeField G G' a φ D'.Ψ x i = D'.Ψ x i
    have hx' := h.mem_Ω1 hx
    have hap : a (G'.layerIndex x) ≠ 0 := (hpos _ (G'.layerIndex_spec hx').1).ne'
    rw [composeField_of_mem a φ D'.Ψ hx, hnp]
    have hb : blockMean G (G'.layerIndex x) (fun y => svec G' φ y i) x =
        blockMean G' (G'.layerIndex x) (fun y => svec G' φ y i) x := rfl
    have e : a (G'.layerIndex x) / a (G'.layerIndex x) *
        (((L : ℝ) ^ G'.layerIndex x) ^ 2 / ((L : ℝ) ^ G'.layerIndex x) ^ 2) = 1 := by
      field_simp
    rw [hb, e]
    simp
  · intro z i
    have hr := hres z i
    rw [elResidual_site] at hr
    by_cases hz : (z : Torus d (N₀ * L ^ k)) ∈ G.Ω 1
    · simp only [hz, ↓reduceIte]
      have hcf := composeField_of_mem a φ D'.Ψ hz i
      have han : a (G.layerIndex (z : Torus d (N₀ * L ^ k))) ≠ 0 :=
        (hpos _ (G.layerIndex_spec hz).1).ne'
      have e2 := coeff_mul_kappa (L := L) a (n := G.layerIndex (z : Torus d (N₀ * L ^ k)))
        (p := G'.layerIndex (z : Torus d (N₀ * L ^ k))) han
      rw [hcf]
      linear_combination hr - (D'.Ψ z i -
        blockMean G' (G'.layerIndex (z : Torus d (N₀ * L ^ k))) (fun y => svec G' φ y i) z) * e2
    · simp only [hz, ↓reduceIte]
      have hz' : (z : Torus d (N₀ * L ^ k)) ∈ G'.Ω 1 := z.2
      have hp1 := (G'.layerIndex_spec hz').1
      have hlt : G.layerIndex (z : Torus d (N₀ * L ^ k)) < G'.layerIndex (z : Torus d (N₀ * L ^ k)) := by
        rw [layerIndex_of_not_mem G hz]; omega
      have hua := invAp_pos h a hpos hz' hlt
      have hap : a (G'.layerIndex (z : Torus d (N₀ * L ^ k))) ≠ 0 := (hpos _ hp1).ne'
      have KI := blockMean_psiExt_compose h a hC1 D' φ hz' hap i
      have e1 : (((invAp G G' a (G'.layerIndex (z : Torus d (N₀ * L ^ k))) z)⁻¹ /
          ((L : ℝ) ^ G'.layerIndex (z : Torus d (N₀ * L ^ k))) ^ 2 : ℝ) : ℂ) *
          ((a (G'.layerIndex (z : Torus d (N₀ * L ^ k))) *
            invAp G G' a (G'.layerIndex (z : Torus d (N₀ * L ^ k))) z : ℝ) : ℂ) =
          ((a (G'.layerIndex (z : Torus d (N₀ * L ^ k))) /
            ((L : ℝ) ^ G'.layerIndex (z : Torus d (N₀ * L ^ k))) ^ 2 : ℝ) : ℂ) := by
        rw [← Complex.ofReal_mul]
        congr 1
        field_simp
      rw [KI]
      linear_combination hr + (blockMean G' (G'.layerIndex (z : Torus d (N₀ * L ^ k)))
        (fun y => svec G' φ y i) z - D'.Ψ z i) * e1

end System

end Balaban.Background
