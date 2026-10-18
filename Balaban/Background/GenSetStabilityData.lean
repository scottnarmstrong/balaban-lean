/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Background.GenSetStabilityTransfer
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The change of the composed datum

For `𝔹_j ≺ 𝔹'_k`, two fields `φ, φ'` of `𝔹'_k` and two data `Ψ, Ψ'`, the composed fields (6.2)
`ψ(𝔹_j, 𝔹'_k)` differ at a site `x ∈ Ω₁` by at most `S + 4 (δ_d + S)` when the fields differ by at
most `S` on the block of `x` and the data by at most `δ_d` at `x` (admissible weights,
`compose_sub_le`).
-/

@[expose] public section

namespace Balaban.Background

open Balaban Balaban.Multiscale Finset

variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ ϱ' : ℝ}
  {G : GeneratingSet d L N₀ k ϱ} {G' : GeneratingSet d L N₀ k ϱ'}

/-- **The change of the composed field at a site of `Ω₁`**: with admissible weights, if
`|φ' - φ| ≤ S` (zero extensions) on the `𝔹'_k`-block of `x` and `|Ψ'(x) - Ψ(x)| ≤ δ_d`, then the
composed fields differ at `x` by at most `S + 4 (δ_d + S)`. -/
theorem compose_sub_le (hp : Precedes G G') {a : ℕ → ℝ} (ha : IsAdmissibleWeights k a)
    (φ φ' : G'.Ω 1 × Fin N → ℂ) (Ψ Ψ' : Torus d (N₀ * L ^ k) → Fin N → ℂ)
    {x : Torus d (N₀ * L ^ k)} (hx : x ∈ G.Ω 1) {S δd : ℝ}
    (hS : ∀ y ∈ G'.blk (G'.layerIndex x) x, vn (fun i => svec G' φ' y i - svec G' φ y i) ≤ S)
    (hΨ : vn (fun i => Ψ' x i - Ψ x i) ≤ δd) :
    vn (fun i => composeField G G' a φ' Ψ' x i - composeField G G' a φ Ψ x i) ≤
      S + 4 * (δd + S) := by
  obtain ⟨hm1, hmk, -⟩ := G.layerIndex_spec hx
  obtain ⟨hn1, hnk, -⟩ := G'.layerIndex_spec (hp.mem_Ω1 hx)
  have hmn := hp.layerIndex_le hx
  set m := G.layerIndex x with hm
  set n := G'.layerIndex x with hn
  set κ : ℝ := a n / a m * (((L : ℝ) ^ m) ^ 2 / ((L : ℝ) ^ n) ^ 2) with hκ
  set u : Torus d (N₀ * L ^ k) → Fin N → ℂ := fun y i => svec G' φ' y i - svec G' φ y i with hu
  have he : ∀ i, composeField G G' a φ' Ψ' x i - composeField G G' a φ Ψ x i =
      blockMean G m (fun y => u y i) x +
        (κ : ℂ) * ((Ψ' x i - Ψ x i) - blockMean G' n (fun y => u y i) x) := by
    intro i
    rw [composeField_of_mem a φ' Ψ' hx i, composeField_of_mem a φ Ψ hx i, ← hm, ← hn]
    simp only [hu, blockMean_sub, hκ]
    push_cast
    ring
  -- the two means
  have h1 : vn (fun i => blockMean G m (fun y => u y i) x) ≤ S := by
    refine vn_blockMean_le (G := G) hmk u x fun y hy => hS y ?_
    exact GeneratingSet.mem_blk.2 (jBlock_eq_of_le hmn hnk (GeneratingSet.mem_blk.1 hy))
  have h2 : vn (fun i => blockMean G' n (fun y => u y i) x) ≤ S :=
    vn_blockMean_le (G := G') hnk u x hS
  -- the coefficient
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne L)
  have hκ0 : 0 ≤ κ := by
    have := (ha n hn1 hnk).1; have := (ha m hm1 hmk).1
    rw [hκ]; positivity
  have hκ4 : κ ≤ 4 := by
    have han := (ha n hn1 hnk).2
    have ham := (ha m hm1 hmk).1
    have hr : a n / a m ≤ 4 := by
      rw [div_le_iff₀ (by linarith)]; linarith
    have hq0 : 0 ≤ ((L : ℝ) ^ m) ^ 2 / ((L : ℝ) ^ n) ^ 2 := by positivity
    have hq1 : ((L : ℝ) ^ m) ^ 2 / ((L : ℝ) ^ n) ^ 2 ≤ 1 := by
      rw [div_le_one (by positivity)]
      exact pow_le_pow_left₀ (by positivity) (pow_le_pow_right₀ hL1 hmn) 2
    have hr0 : 0 ≤ a n / a m := by
      have := (ha n hn1 hnk).1; positivity
    calc κ = a n / a m * (((L : ℝ) ^ m) ^ 2 / ((L : ℝ) ^ n) ^ 2) := rfl
      _ ≤ 4 * 1 := mul_le_mul hr hq1 hq0 (by norm_num)
      _ = 4 := by ring
  have h3 : vn (fun i => (Ψ' x i - Ψ x i) - blockMean G' n (fun y => u y i) x) ≤ δd + S := by
    have := vn_sub_le' (fun i => Ψ' x i - Ψ x i) (fun i => blockMean G' n (fun y => u y i) x)
    linarith
  have h4 : vn (fun i => (κ : ℂ) * ((Ψ' x i - Ψ x i) - blockMean G' n (fun y => u y i) x)) ≤
      4 * (δd + S) := by
    rw [vn_smul_real, abs_of_nonneg hκ0]
    have hδS : 0 ≤ vn (fun i => (Ψ' x i - Ψ x i) - blockMean G' n (fun y => u y i) x) :=
      vn_nonneg _
    nlinarith
  simp only [he]
  exact (vn_add' _ _).trans (add_le_add h1 h4)

end Balaban.Background
