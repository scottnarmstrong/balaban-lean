/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.WindowConvCoeff
public import Balaban.LargeField.R.ActionConvPieces

/-!
# The originating-piece factor in P7 (2.11)

The regional response estimate remains a named source hypothesis. The arithmetic below
turns its RG increment factor into the exact ratio used by the history window theorem.
-/

@[expose] public section

namespace Balaban.LargeField.ActionConv

open Balaban.SmallField

/-- The gap exponent cancels the RG increment exponent exactly. -/
theorem epsSeq_scale_rate_eq (L d : ℕ) (hL : 1 < L) (hd : 2 ≤ d)
    (α α₀ γ : ℝ) (hγα : (d : ℝ) - 2 - 2 * α = 2 * γ) (n : ℕ) :
    (L : ℝ) ^ ((d - 2) * n) * epsSeq L α α₀ n ^ 2 *
      ((L : ℝ) ^ (-(2 * γ))) ^ n =
      α₀ ^ 2 * epsTail n ^ 2 := by
  have hsf := scale_factor L d hL hd α γ hγα n
  have hfac : (L : ℝ) ^ ((d - 2) * n) * ((L : ℝ) ^ (-α)) ^ (2 * n) ≠ 0 := by
    positivity
  have hunit : ((L : ℝ) ^ ((d - 2) * n) * ((L : ℝ) ^ (-α)) ^ (2 * n)) *
      ((L : ℝ) ^ (-(2 * γ))) ^ n = 1 := by
    rw [← hsf]
    exact mul_inv_cancel₀ hfac
  unfold epsSeq
  have hp : (((L : ℝ) ^ (-α)) ^ n) ^ 2 = ((L : ℝ) ^ (-α)) ^ (2 * n) := by
    rw [← pow_mul, mul_comm]
  calc
    (L : ℝ) ^ ((d - 2) * n) * (α₀ * epsTail n * ((L : ℝ) ^ (-α)) ^ n) ^ 2 *
        ((L : ℝ) ^ (-(2 * γ))) ^ n
        = (α₀ ^ 2 * epsTail n ^ 2) *
          (((L : ℝ) ^ ((d - 2) * n) * ((L : ℝ) ^ (-α)) ^ (2 * n)) *
            ((L : ℝ) ^ (-(2 * γ))) ^ n) := by
              rw [mul_pow, mul_pow, hp]
              ring
    _ = _ := by rw [hunit, mul_one]

/-- The dimensionless factor left after extracting the P7 scale ratio is at most
the explicit factor nine from the epsilon tail. -/
theorem flow_eps_rate_le (L d : ℕ) (hL : 1 < L) (hd : 2 ≤ d)
    (α α₀ γ β η : ℝ) (hβ : 0 < β)
    (hγα : (d : ℝ) - 2 - 2 * α = 2 * γ)
    (g : ℕ → ℝ) (hg : ∀ n, g n ≤ Real.exp η) (n : ℕ) :
    (β * (L : ℝ) ^ ((d - 2) * n) * g n * epsSeq L α α₀ n ^ 2) *
        ((L : ℝ) ^ (-(2 * γ))) ^ n ≤
      9 * β * Real.exp η * α₀ ^ 2 := by
  have ht : epsTail n ^ 2 ≤ 9 := by
    have h1 := one_le_epsTail n
    have h2 := epsTail_lt_three n
    nlinarith
  have hprod : g n * epsTail n ^ 2 ≤ Real.exp η * 9 := by
    exact mul_le_mul (hg n) ht (sq_nonneg _) (le_of_lt (Real.exp_pos _))
  calc
    (β * (L : ℝ) ^ ((d - 2) * n) * g n * epsSeq L α α₀ n ^ 2) *
        ((L : ℝ) ^ (-(2 * γ))) ^ n
        = β * g n * ((L : ℝ) ^ ((d - 2) * n) *
            epsSeq L α α₀ n ^ 2 * ((L : ℝ) ^ (-(2 * γ))) ^ n) := by ring
    _ = (β * α₀ ^ 2) * (g n * epsTail n ^ 2) := by
          rw [epsSeq_scale_rate_eq L d hL hd α α₀ γ hγα n]
          ring
    _ ≤ (β * α₀ ^ 2) * (Real.exp η * 9) :=
          mul_le_mul_of_nonneg_left hprod (mul_nonneg hβ.le (sq_nonneg _))
    _ = _ := by ring

/-- Scalar form of the originating-energy calculation, with no action-specific premise
hidden in its hypotheses. -/
theorem source_ratio_scalar_le {β A D q K C α₀ η : ℝ}
    (hβ : 0 < β) (hA : 0 ≤ A) (hD : 0 < D)
    (hK : 0 ≤ K) (hC : 0 ≤ C)
    (hrate : D * q ≤ 9 * β * Real.exp η * α₀ ^ 2) :
    K * A * (C * β⁻¹ * q) ≤
      (9 * K * C * α₀ ^ 2 * Real.exp η) * (A / D) := by
  have hfactor : 0 ≤ K * A * C * β⁻¹ := by positivity
  have hprod : (K * A * (C * β⁻¹ * q)) * D ≤
      (9 * K * C * α₀ ^ 2 * Real.exp η) * A := by
    calc
      (K * A * (C * β⁻¹ * q)) * D = (K * A * C * β⁻¹) * (D * q) := by ring
      _ ≤ (K * A * C * β⁻¹) * (9 * β * Real.exp η * α₀ ^ 2) :=
        mul_le_mul_of_nonneg_left hrate hfactor
      _ = (9 * K * C * α₀ ^ 2 * Real.exp η) * A := by
        field_simp
  have hdiv := (le_div_iff₀ hD).2 hprod
  convert hdiv using 1; ring

variable {d L N₀ K N : ℕ} [NeZero N₀] [NeZero L]
  {U : Type*} {S : Set U} {ι : Type*} [Fintype ι]
  {sc : ι → ℕ} {k1 k : ℕ}

/-- P7 (2.11), conditional on its named regional response/source bound. The RG step
parameter supplies the scale factor, while the source premise retains the energy of
the originating piece and includes its half-bond cut. -/
theorem p7_first_of_rg_source
    (W : PieceWindowSetup d L N₀ K N S ι sc k1 k)
    (βs : ι → ℕ → ℝ) (ξ : ι → ℕ → Fin 3 → ℝ)
    (β Cξ Ksrc α α₀ γ η : ℝ)
    (hβ : 0 < β) (hC : 0 ≤ Cξ) (hK : 0 ≤ Ksrc)
    (hα₀ : 0 < α₀) (hL : 1 < L) (hd : 2 ≤ d)
    (hγα : (d : ℝ) - 2 - 2 * α = 2 * γ)
    (hflow : ∀ i, ∃ g : ℕ → ℝ,
      (∀ m, Real.exp (-η) ≤ g m ∧ g m ≤ Real.exp η) ∧
      ∀ m, βs i m = β * (L : ℝ) ^ ((d - 2) * m) * g m)
    (hξ : ∀ i t, ‖ξ i t‖ ≤ Cξ * β⁻¹ *
      ((L : ℝ) ^ (-(2 * γ))) ^ (t + 1))
    (hsource : ∀ i n, sc i + 2 ≤ n → n ≤ k → ∀ u ∈ S,
      ‖(W.chain i).cost u n‖ ≤
        Ksrc * (βs i (sc i + 1) * epsSeq L α α₀ (sc i + 1) ^ 2) *
          ‖ξ i (n - 1)‖ * W.mcount i) :
    ∀ i n, sc i + 2 ≤ n → n ≤ k → ∀ u ∈ S,
      ‖(W.chain i).cost u n‖ ≤
        (9 * Ksrc * Cξ * α₀ ^ 2 * Real.exp η) *
          ((βs i (sc i + 1) * epsSeq L α α₀ (sc i + 1) ^ 2) /
            (βs i n * epsSeq L α α₀ n ^ 2)) * W.mcount i := by
  intro i n hn1 hn2 u hu
  obtain ⟨g, hg, hβs⟩ := hflow i
  have hLpos : (0 : ℝ) < L := by exact_mod_cast (by omega : 0 < L)
  have hgp : ∀ m, 0 < g m := fun m =>
    lt_of_lt_of_le (Real.exp_pos _) (hg m).1
  have hβp : ∀ m, 0 < βs i m := by
    intro m
    rw [hβs]
    have hp := hgp m
    positivity
  have hεp : ∀ m, 0 < epsSeq L α α₀ m := by
    intro m
    unfold epsSeq
    have ht := epsTail_pos m
    positivity
  have hA : 0 ≤ βs i (sc i + 1) * epsSeq L α α₀ (sc i + 1) ^ 2 := by
    have hp := hβp (sc i + 1)
    positivity
  have hD : 0 < βs i n * epsSeq L α α₀ n ^ 2 := by
    have hp := hβp n
    have he := hεp n
    positivity
  have hrate : (βs i n * epsSeq L α α₀ n ^ 2) *
      ((L : ℝ) ^ (-(2 * γ))) ^ n ≤
      9 * β * Real.exp η * α₀ ^ 2 := by
    rw [hβs]
    exact flow_eps_rate_le L d hL hd α α₀ γ β η hβ hγα g
      (fun m => (hg m).2) n
  have hξn : ‖ξ i (n - 1)‖ ≤
      Cξ * β⁻¹ * ((L : ℝ) ^ (-(2 * γ))) ^ n := by
    simpa only [Nat.sub_add_cancel (by omega : 1 ≤ n)] using hξ i (n - 1)
  calc
    ‖(W.chain i).cost u n‖
        ≤ Ksrc * (βs i (sc i + 1) * epsSeq L α α₀ (sc i + 1) ^ 2) *
            ‖ξ i (n - 1)‖ * W.mcount i := hsource i n hn1 hn2 u hu
    _ ≤ Ksrc * (βs i (sc i + 1) * epsSeq L α α₀ (sc i + 1) ^ 2) *
          (Cξ * β⁻¹ * ((L : ℝ) ^ (-(2 * γ))) ^ n) * W.mcount i := by
        apply mul_le_mul_of_nonneg_right _ (W.mcount_nonneg i)
        exact mul_le_mul_of_nonneg_left hξn (mul_nonneg hK hA)
    _ ≤ (9 * Ksrc * Cξ * α₀ ^ 2 * Real.exp η) *
          ((βs i (sc i + 1) * epsSeq L α α₀ (sc i + 1) ^ 2) /
            (βs i n * epsSeq L α α₀ n ^ 2)) * W.mcount i := by
        apply mul_le_mul_of_nonneg_right _ (W.mcount_nonneg i)
        exact source_ratio_scalar_le hβ hA hD hK hC hrate

end Balaban.LargeField.ActionConv
