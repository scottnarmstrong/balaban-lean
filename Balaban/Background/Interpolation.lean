/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Background.Weights
public import Balaban.Background.Normalize
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The interpolated vector (LEMMA53-astra.md, §4 (A3), §6 item 7)

`interp G Φ x = ∑_B h_B(x) Φ(B)`.  Because `∑_B h_B = 1`, differences of `interp` are the sums of
differences of weights against `Φ(B) - ref`, where `ref` is a common reference vector; only the blocks
of the support contribute.
-/

@[expose] public section

namespace Balaban.Background

open Balaban.Multiscale Finset

variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}

theorem cNorm_sum_le {ι : Type*} (s : Finset ι) (f : ι → Fin N → ℂ) :
    cNorm (∑ i ∈ s, f i) ≤ ∑ i ∈ s, cNorm (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [cNorm]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (cNorm_add_le _ _).trans (add_le_add_right ih _)

section Interp

variable (G : GeneratingSet d L N₀ k ϱ)

/-- The interpolated vector `φ̃(x) = ∑_B h_B(x) φ^B`. -/
noncomputable def interp (Φ : Torus d (N₀ * L ^ k) → Fin N → ℂ) (x : Torus d (N₀ * L ^ k)) :
    Fin N → ℂ := ∑ q ∈ blockIdx G, ((weight G q x : ℝ) : ℂ) • Φ q.2


theorem weighted_sum_le {ι : Type*} {S : Finset ι} {c : ι → ℝ} {v : ι → Fin N → ℂ} {C r : ℝ}
    (h : ∀ i ∈ S, |c i| ≤ C ∧ cNorm (v i) ≤ r) (hC : 0 ≤ C) :
    cNorm (∑ i ∈ S, ((c i : ℝ) : ℂ) • v i) ≤ S.card * (C * r) := by
  refine (cNorm_sum_le _ _).trans ?_
  calc ∑ i ∈ S, cNorm (((c i : ℝ) : ℂ) • v i) ≤ ∑ _i ∈ S, C * r := by
        refine Finset.sum_le_sum fun i hi => ?_
        rw [cNorm_smul, Complex.norm_real, Real.norm_eq_abs]
        exact mul_le_mul (h i hi).1 (h i hi).2 (cNorm_nonneg _) hC
    _ = S.card * (C * r) := by simp

theorem interp_sub_ref (Φ : Torus d (N₀ * L ^ k) → Fin N → ℂ) (ref : Fin N → ℂ) {n : ℕ}
    (hn1 : 1 ≤ n) (hnk : n ≤ k) {x : Torus d (N₀ * L ^ k)} (hx : x ∈ G.layer n) :
    interp G Φ x - ref = ∑ q ∈ blockIdx G, ((weight G q x : ℝ) : ℂ) • (Φ q.2 - ref) := by
  have h1 : ∑ q ∈ blockIdx G, ((weight G q x : ℝ) : ℂ) = 1 := by
    rw [← Complex.ofReal_sum, sum_weight G hn1 hnk hx]; simp
  simp only [smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul, h1, one_smul]
  rfl

theorem interp_near (Φ : Torus d (N₀ * L ^ k) → Fin N → ℂ) (ref : Fin N → ℂ) {r : ℝ}
    {n : ℕ} (hn1 : 1 ≤ n) (hnk : n ≤ k) {x : Torus d (N₀ * L ^ k)}
    (hx : x ∈ G.layer n) (h : ∀ q ∈ active G x, cNorm (Φ q.2 - ref) ≤ r) :
    cNorm (interp G Φ x - ref) ≤ r := by
  rw [interp_sub_ref G Φ ref hn1 hnk hx]
  refine (cNorm_sum_le _ _).trans ?_
  calc ∑ q ∈ blockIdx G, cNorm (((weight G q x : ℝ) : ℂ) • (Φ q.2 - ref))
      ≤ ∑ q ∈ blockIdx G, weight G q x * r := by
        refine Finset.sum_le_sum fun q hq => ?_
        rw [cNorm_smul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (weight_nonneg G hn1 hnk hx hq)]
        by_cases hqa : q ∈ active G x
        · exact mul_le_mul_of_nonneg_left (h q hqa) (weight_nonneg G hn1 hnk hx hq)
        · rw [weight_eq_zero G hq hqa]; simp
    _ = r := by rw [← Finset.sum_mul, sum_weight G hn1 hnk hx, one_mul]

/-- First and second differences of the interpolated vector. -/
theorem interp_diff (hϱ : (4 * d * L : ℝ) ≤ ϱ) (hd : 1 ≤ d) (hL : 2 ≤ L)
    (Φ : Torus d (N₀ * L ^ k) → Fin N → ℂ) (ref : Fin N → ℂ) {r : ℝ} (hr : 0 ≤ r) {n : ℕ}
    (hn2 : 2 ≤ n) (hnk : n ≤ k) {x : Torus d (N₀ * L ^ k)} (hx : x ∈ G.layer n) (μ : Fin d)
    (h : ∀ q ∈ supp G x μ, cNorm (Φ q.2 - ref) ≤ r) :
    cNorm (interp G Φ (x + Pi.single μ 1) - interp G Φ x) ≤
        9 * 3 ^ d * (wH1 d L / (L : ℝ) ^ n * r) ∧
    cNorm (interp G Φ (x - Pi.single μ 1) - interp G Φ x) ≤
        9 * 3 ^ d * (wH1 d L / (L : ℝ) ^ n * r) ∧
    cNorm (interp G Φ (x + Pi.single μ 1) + interp G Φ (x - Pi.single μ 1) -
        (2 : ℂ) • interp G Φ x) ≤ 9 * 3 ^ d * (wH2 d L / ((L : ℝ) ^ n) ^ 2 * r) := by
  have hn1 : 1 ≤ n := by omega
  have hLn : (0 : ℝ) < (L : ℝ) ^ n := by
    have : (0 : ℝ) < L := by exact_mod_cast (by omega : 0 < L)
    positivity
  obtain ⟨n₁, h11, h1k, hx₁⟩ := exists_layer_adj G hϱ hd (by omega) hn2 hnk hx (adj_add x μ)
  obtain ⟨n₂, h21, h2k, hx₂⟩ := exists_layer_adj G hϱ hd (by omega) hn2 hnk hx (adj_sub x μ)
  have hcard := card_supp_le G hϱ hd (by omega) hn1 hnk hx μ
  have hH1 := wH1_nonneg d L
  have hH2 := wH2_nonneg d L
  have hwd := fun q (hq : q ∈ blockIdx G) => weight_diff G hϱ hd hL hn2 hnk hx μ hq
  have hz : ∀ q ∈ blockIdx G, q ∉ supp G x μ →
      weight G q x = 0 ∧ weight G q (x + Pi.single μ 1) = 0 ∧
        weight G q (x - Pi.single μ 1) = 0 := fun q hq hqs => by
    obtain ⟨h1, h2, h3⟩ := not_mem_supp G hq hqs
    exact ⟨by unfold weight; rw [h1, zero_div], by unfold weight; rw [h2, zero_div],
      by unfold weight; rw [h3, zero_div]⟩
  have cardR : ((supp G x μ).card : ℝ) ≤ 9 * 3 ^ d := by exact_mod_cast hcard
  refine ⟨?_, ?_, ?_⟩
  · have e : interp G Φ (x + Pi.single μ 1) - interp G Φ x =
        ∑ q ∈ blockIdx G, ((weight G q (x + Pi.single μ 1) - weight G q x : ℝ) : ℂ) •
          (Φ q.2 - ref) := by
      rw [← sub_sub_sub_cancel_right (interp G Φ (x + Pi.single μ 1)) (interp G Φ x) ref,
        interp_sub_ref G Φ ref h11 h1k hx₁, interp_sub_ref G Φ ref hn1 hnk hx,
        ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun q _ => ?_
      push_cast; rw [sub_smul]
    rw [e, ← Finset.sum_subset (supp_subset G x μ) (fun q hq hqs => by
      obtain ⟨a, b, c⟩ := hz q hq hqs; simp [a, b])]
    refine (weighted_sum_le (C := wH1 d L / (L : ℝ) ^ n) (r := r) (fun q hq => ⟨?_, h q hq⟩)
      (by positivity)).trans ?_
    · exact (hwd q (supp_subset G x μ hq)).1
    · exact mul_le_mul_of_nonneg_right cardR (by positivity)
  · have e : interp G Φ (x - Pi.single μ 1) - interp G Φ x =
        ∑ q ∈ blockIdx G, ((weight G q (x - Pi.single μ 1) - weight G q x : ℝ) : ℂ) •
          (Φ q.2 - ref) := by
      rw [← sub_sub_sub_cancel_right (interp G Φ (x - Pi.single μ 1)) (interp G Φ x) ref,
        interp_sub_ref G Φ ref h21 h2k hx₂, interp_sub_ref G Φ ref hn1 hnk hx,
        ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun q _ => ?_
      push_cast; rw [sub_smul]
    rw [e, ← Finset.sum_subset (supp_subset G x μ) (fun q hq hqs => by
      obtain ⟨a, b, c⟩ := hz q hq hqs; simp [a, c])]
    refine (weighted_sum_le (C := wH1 d L / (L : ℝ) ^ n) (r := r) (fun q hq => ⟨?_, h q hq⟩)
      (by positivity)).trans ?_
    · exact (hwd q (supp_subset G x μ hq)).2.1
    · exact mul_le_mul_of_nonneg_right cardR (by positivity)
  · have e : interp G Φ (x + Pi.single μ 1) + interp G Φ (x - Pi.single μ 1) -
        (2 : ℂ) • interp G Φ x =
        ∑ q ∈ blockIdx G, ((weight G q (x + Pi.single μ 1) + weight G q (x - Pi.single μ 1)
          - 2 * weight G q x : ℝ) : ℂ) • (Φ q.2 - ref) := by
      have e1 := interp_sub_ref G Φ ref h11 h1k hx₁
      have e2 := interp_sub_ref G Φ ref h21 h2k hx₂
      have e3 := interp_sub_ref G Φ ref hn1 hnk hx
      have : interp G Φ (x + Pi.single μ 1) + interp G Φ (x - Pi.single μ 1) -
          (2 : ℂ) • interp G Φ x = (interp G Φ (x + Pi.single μ 1) - ref) +
          (interp G Φ (x - Pi.single μ 1) - ref) - (2 : ℂ) • (interp G Φ x - ref) := by
        funext i; simp [Pi.sub_apply, Pi.smul_apply]; ring
      rw [this, e1, e2, e3, Finset.smul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun q _ => ?_
      push_cast
      simp only [smul_smul, add_smul, sub_smul]
    rw [e, ← Finset.sum_subset (supp_subset G x μ) (fun q hq hqs => by
      obtain ⟨a, b, c⟩ := hz q hq hqs; simp [a, b, c])]
    refine (weighted_sum_le (C := wH2 d L / ((L : ℝ) ^ n) ^ 2) (r := r)
      (fun q hq => ⟨?_, h q hq⟩) (by positivity)).trans ?_
    · exact (hwd q (supp_subset G x μ hq)).2.2
    · exact mul_le_mul_of_nonneg_right cardR (by positivity)

end Interp

end Balaban.Background
