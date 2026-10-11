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

end System

end Balaban.Background
