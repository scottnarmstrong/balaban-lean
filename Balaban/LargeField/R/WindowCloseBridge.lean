/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.CancelIdentity
public import Balaban.LargeField.R.RRemovedExponent

/-!
# Arithmetic of the bridge to the consumer's `e^{L_c}` (blocker 4, W1004)

`a_z ≤ a₁` for the composed weight (the harmonic mean of weights `a_r ≤ a₁`), and the comparison
`∏_{z ∈ Zb} (β a_z / 2π)^{N/2} ≤ ∏_i (w_i/π)^{N/2}` when the blocks of `Zb` inject into the blocks `i` with
`β a_z ≤ 2 w_i`.
-/

@[expose] public section

namespace Balaban.LargeField

open Balaban Balaban.Multiscale Balaban.Background Finset

/-- `a_r ≤ a₁` for `r ≥ 1`. -/
theorem compWeight_le_a₁ {L : ℕ} (hL : 2 ≤ L) {a₁ : ℝ} (ha : 0 < a₁) {r : ℕ} (hr : 1 ≤ r) :
    compWeight L a₁ r ≤ a₁ := by
  unfold compWeight
  have h2 : (2 : ℝ) ≤ L := by exact_mod_cast hL
  have h4 : (4 : ℝ) ≤ (L : ℝ) ^ 2 := by nlinarith
  have hLr : (L : ℝ) ^ 2 ≤ ((L : ℝ) ^ r) ^ 2 := by
    have : (L : ℝ) ≤ (L : ℝ) ^ r := by
      calc (L : ℝ) = (L : ℝ) ^ 1 := (pow_one _).symm
        _ ≤ (L : ℝ) ^ r := pow_le_pow_right₀ (by linarith) hr
    exact pow_le_pow_left₀ (by positivity) this 2
  have hinv : (((L : ℝ) ^ r) ^ 2)⁻¹ ≤ ((L : ℝ) ^ 2)⁻¹ := inv_anti₀ (by positivity) hLr
  have hlt : (((L : ℝ) ^ 2)⁻¹) < 1 := by
    rw [inv_lt_one₀ (by positivity)]; linarith
  have hpos : 0 < 1 - ((((L : ℝ) ^ r) ^ 2)⁻¹) := by
    have : (((L : ℝ) ^ r) ^ 2)⁻¹ < 1 := lt_of_le_of_lt hinv hlt
    linarith
  rw [div_le_iff₀ hpos]
  nlinarith


section Z

variable {d L N₀ k : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}

/-- `a_z ≤ a₁` for the composed weight of a block whose leaves lie in the layers `1 ≤ n < k`. -/
theorem compWeightZ_le_a₁ {a₁ : ℝ} (ha₁ : 0 < a₁) (hL : 2 ≤ L) (G : GeneratingSet d L N₀ k ϱ)
    {z : Torus d (N₀ * L ^ (k - k))}
    (hn : ∀ x ∈ fib d L N₀ k k z, 1 ≤ G.layerIndex x ∧ G.layerIndex x < k) :
    compWeightZ G a₁ z ≤ a₁ := by
  unfold compWeightZ
  have hV := ActionConv.blockVol_pos (d := d) (k := k) (by omega : 0 < L)
  have hcard : ((fib d L N₀ k k z).card : ℝ) = blockVol d L k := by
    rw [card_fib le_rfl, blockVol_eq]; push_cast; rfl
  have hsum : (fib d L N₀ k k z).card • (a₁⁻¹) ≤
      ∑ s ∈ fib d L N₀ k k z, (compWeight L a₁ (k - G.layerIndex s))⁻¹ := by
    rw [← Finset.sum_const]
    refine Finset.sum_le_sum fun x hx => ?_
    have h1 := hn x hx
    exact inv_anti₀ (compWeight_pos hL ha₁ (by omega)) (compWeight_le_a₁ hL ha₁ (by omega))
  have hsum' : blockVol d L k * a₁⁻¹ ≤
      ∑ s ∈ fib d L N₀ k k z, (compWeight L a₁ (k - G.layerIndex s))⁻¹ := by
    rw [← hcard, ← nsmul_eq_mul]; exact hsum
  have hne : (fib d L N₀ k k z).Nonempty := fib_nonempty le_rfl z
  have hpos : 0 < ((blockVol d L k)⁻¹ *
      ∑ s ∈ fib d L N₀ k k z, (compWeight L a₁ (k - G.layerIndex s))⁻¹) := by
    refine mul_pos (inv_pos.2 hV) (Finset.sum_pos (fun x hx => ?_) hne)
    exact inv_pos.2 (compWeight_pos hL ha₁ (by have := hn x hx; omega))
  rw [inv_le_comm₀ hpos ha₁]
  calc a₁⁻¹ = (blockVol d L k)⁻¹ * (blockVol d L k * a₁⁻¹) := by field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left hsum' (inv_pos.2 hV).le

end Z


section Prod

/-- The product `∏_{z ∈ g(Y)} (f z / 2π)^{N/2}` is at most `∏_i (w_i/π)^{N/2}` when `f (g i) / 2π ≤ w_i / π`
on `Y` and `π ≤ w_i` for all `i` (an injection of the blocks of `Zb` into the blocks of the tree). -/
theorem prod_rpow_image_le {X ι : Type*} [Fintype ι] [DecidableEq X] (N : ℕ) (Y : Finset ι) (g : ι → X)
    (hg : Function.Injective g) (f : X → ℝ) (wz : ι → ℝ)
    (hwz1 : ∀ i, Real.pi ≤ wz i) (hf : ∀ i ∈ Y, 0 ≤ f (g i))
    (hle : ∀ i ∈ Y, f (g i) / (2 * Real.pi) ≤ wz i / Real.pi) :
    ∏ z ∈ Y.image g, (f z / (2 * Real.pi)) ^ ((N : ℝ) / 2) ≤ ∏ i, (wz i / Real.pi) ^ ((N : ℝ) / 2) := by
  have hpi := Real.pi_pos
  have hone : ∀ i, 1 ≤ (wz i / Real.pi) ^ ((N : ℝ) / 2) := fun i =>
    Real.one_le_rpow ((one_le_div hpi).2 (hwz1 i)) (by positivity)
  rw [Finset.prod_image (fun a _ b _ h => hg h)]
  calc ∏ i ∈ Y, (f (g i) / (2 * Real.pi)) ^ ((N : ℝ) / 2)
      ≤ ∏ i ∈ Y, (wz i / Real.pi) ^ ((N : ℝ) / 2) :=
        Finset.prod_le_prod₀ (fun i hi => Real.rpow_nonneg (div_nonneg (hf i hi) (by positivity)) _)
          (fun i hi => Real.rpow_le_rpow (div_nonneg (hf i hi) (by positivity)) (hle i hi) (by positivity))
    _ ≤ ∏ i, (wz i / Real.pi) ^ ((N : ℝ) / 2) :=
        Finset.prod_le_prod_of_subset_of_one_le₀ (Finset.subset_univ _) (fun i _ => zero_le_one.trans (hone i)) (fun i _ _ => hone i)

/-- The number of elements of a subtype in bijection (through `c`, `c'`) with a finset. -/
theorem nat_card_subtype_eq_card {A X : Type*} (P : A → Prop) (c : A → X) (c' : X → A)
    (hcc : ∀ y, c' (c y) = y) (hcc' : ∀ x, c (c' x) = x) (B : Finset X)
    (h : ∀ y, P y ↔ c y ∈ B) : Nat.card {y // P y} = B.card := by
  have e : {y // P y} ≃ ↥B :=
    { toFun := fun y => ⟨c y.1, (h y.1).1 y.2⟩
      invFun := fun b => ⟨c' b.1, (h _).2 (by rw [hcc' b.1]; exact b.2)⟩
      left_inv := fun y => Subtype.ext (hcc y.1)
      right_inv := fun b => Subtype.ext (hcc' b.1) }
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_coe]

end Prod

end Balaban.LargeField
