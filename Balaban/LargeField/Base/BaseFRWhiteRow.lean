/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Base.BaseFRWhiteConfig
public import Balaban.LargeField.Base.BaseFRWhiteFirst
public import Balaban.Multiscale.Counting

/-!
# The row sums of the finite-range whitening

`W = c_W^{-1/2} S_R(K_e)` has range `R (dL + 1)` (`baseWhite`) and `ℓ²` norm at most
`c_W^{-1/2} (1 - q)^{-1/2}` (`norm_sqrtTrunc_le`), `c_W = J²/γ`, `q = √(1 - (γ/J)²)`; the number of
indices `(y, j)` within distance `R (dL + 1)` of a given one is at most `N (2 R (dL + 1) + 1)^d`
(`card_ball_le`). Hence the maximal absolute row sum satisfies
`‖W‖_row ≤ N (2 R (dL+1) + 1)^d (γ/J²)^{1/2} (1 - q)^{-1/2}` (`matRowSum_baseWhiteW_le`).
-/

@[expose] public section

set_option linter.unusedSectionVars false

open Matrix Balaban.Green Balaban.LargeField.Base Balaban.Multiscale
open scoped Matrix.Norms.L2Operator

namespace Balaban.LargeField.FRWhite

variable {d L N₀ N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ} (G : GeneratingSet d L N₀ 1 ϱ)
variable {a : ℕ → ℝ} {ν : ℝ} {α : G.Ω 1 → ℂ} {η : ℝ} {s : FineBond d L N₀ → ℂ}
  (e : G.Ω 1 → Fin N → ℝ)

/-- **The row sums of the whitening.** -/
theorem matRowSum_baseWhiteW_le [Nonempty (G.Ω 1)] [NeZero N] (hν : 0 ≤ ν)
    (ha : IsAdmissibleWeights 1 a) (hα : ∀ z, ‖α z‖ ≤ 1 / (8 * (L : ℝ) ^ 2)) (hη0 : 0 ≤ η)
    (hη : η ≤ baseCoercivity L / (8 * d)) (hs : s ∈ baseParamNbhd G η)
    (he : ∀ z, ∑ i, e z i ^ 2 = 1) (R : ℕ) :
    matRowSum (baseWhiteW G a ν α s e R) ≤
      N * (2 * (R * (d * L + 1)) + 1) ^ d *
        (((baseJ d ν) ^ 2 / (baseCoercivity L / 2)) ^ (-(1 / 2 : ℝ)) *
          Real.sqrt (1 - Real.sqrt (1 - ((baseCoercivity L / 2) / baseJ d ν) ^ 2))⁻¹) := by
  classical
  obtain ⟨-, hrange, -, -⟩ := baseWhite G e hν ha hα hη0 hη hs he R
  obtain ⟨hK, hq⟩ := baseWhiteK_norm_le G e hν ha hα hη0 hη hs he
  have hq0 := Real.sqrt_nonneg (1 - ((baseCoercivity L / 2) / baseJ d ν) ^ 2)
  have hS := norm_sqrtTrunc_le hK hq0 hq R
  set c : ℝ := ((baseJ d ν) ^ 2 / (baseCoercivity L / 2)) ^ (-(1 / 2 : ℝ)) with hc
  have hc0 : 0 ≤ c := Real.rpow_nonneg (by
    have hL : 0 < L := Nat.pos_of_ne_zero (NeZero.ne L)
    have := baseCoercivity_pos hL
    have := baseJ_pos (d := d) hν
    positivity) _
  have hW : ‖baseWhiteW G a ν α s e R‖ ≤
      c * Real.sqrt (1 - Real.sqrt (1 - ((baseCoercivity L / 2) / baseJ d ν) ^ 2))⁻¹ := by
    unfold baseWhiteW whiteW
    rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg hc0]
    exact mul_le_mul_of_nonneg_left hS hc0
  have hcard : ∀ p : G.Ω 1 × Fin N,
      ((Finset.univ.filter fun q : G.Ω 1 × Fin N =>
        indexDist (N := N) G p q ≤ (R : ℝ) * baseRange d L).card : ℝ) ≤
        N * (2 * (R * (d * L + 1)) + 1) ^ d := by
    intro p
    have hρ : (R : ℝ) * baseRange d L = ((R * (d * L + 1) : ℕ) : ℝ) := by
      unfold baseRange; push_cast; ring
    set Rn : ℕ := R * (d * L + 1) with hRn
    set B : Finset (G.Ω 1) := Finset.univ.filter fun y : G.Ω 1 => siteDist G p.1 y ≤ (Rn : ℝ) with hB
    have hsub : (Finset.univ.filter fun q : G.Ω 1 × Fin N =>
        indexDist (N := N) G p q ≤ (R : ℝ) * baseRange d L) ⊆ B ×ˢ (Finset.univ : Finset (Fin N)) := by
      intro q hq
      rw [Finset.mem_filter, hρ] at hq
      simp only [Finset.mem_product, hB, Finset.mem_filter, Finset.mem_univ, true_and, and_true]
      exact hq.2
    have hBcard : B.card ≤ (2 * Rn + 1) ^ d := by
      have hmaps : Set.MapsTo (fun y : G.Ω 1 => y.1) (B : Set (G.Ω 1))
          (↑(Finset.univ.filter fun z : Torus d (N₀ * L ^ 1) => torusDist d (N₀ * L ^ 1) p.1.1 z ≤ Rn)) := by
        intro y hy
        simp only [hB, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hy
        simpa [siteDist] using hy
      exact (Finset.card_le_card_of_injOn _ hmaps Subtype.val_injective.injOn).trans
        (card_ball_le _ Rn)
    calc ((Finset.univ.filter fun q : G.Ω 1 × Fin N =>
          indexDist (N := N) G p q ≤ (R : ℝ) * baseRange d L).card : ℝ)
        ≤ ((B ×ˢ (Finset.univ : Finset (Fin N))).card : ℝ) := by exact_mod_cast Finset.card_le_card hsub
      _ = B.card * N := by simp
      _ ≤ (2 * Rn + 1) ^ d * N := by
          gcongr
          exact_mod_cast hBcard
      _ = N * (2 * (R * (d * L + 1)) + 1) ^ d := by push_cast [hRn]; ring
  have hrow : ∀ p : G.Ω 1 × Fin N, ∑ q, ‖baseWhiteW G a ν α s e R p q‖ ≤
      N * (2 * (R * (d * L + 1)) + 1) ^ d *
        (c * Real.sqrt (1 - Real.sqrt (1 - ((baseCoercivity L / 2) / baseJ d ν) ^ 2))⁻¹) := by
    intro p
    refine (sum_norm_row_le hrange p).trans ?_
    exact mul_le_mul (hcard p) hW (norm_nonneg _) (by positivity)
  unfold matRowSum
  have hB : 0 ≤ (N : ℝ) * (2 * (R * (d * L + 1)) + 1) ^ d *
      (c * Real.sqrt (1 - Real.sqrt (1 - ((baseCoercivity L / 2) / baseJ d ν) ^ 2))⁻¹) := by
    positivity
  have : (Finset.univ.sup fun p : G.Ω 1 × Fin N => ∑ q, ‖baseWhiteW G a ν α s e R p q‖₊) ≤
      Real.toNNReal ((N : ℝ) * (2 * (R * (d * L + 1)) + 1) ^ d *
        (c * Real.sqrt (1 - Real.sqrt (1 - ((baseCoercivity L / 2) / baseJ d ν) ^ 2))⁻¹)) :=
    Finset.sup_le fun p _ => by
      rw [← NNReal.coe_le_coe, NNReal.coe_sum, Real.coe_toNNReal _ hB]
      simpa using hrow p
  have h2 := NNReal.coe_le_coe.2 this
  rwa [Real.coe_toNNReal _ hB] at h2

end Balaban.LargeField.FRWhite
