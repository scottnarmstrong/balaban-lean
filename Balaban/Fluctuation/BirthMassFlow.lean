/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.ClassOldBirthRun
public import Balaban.Fluctuation.LocalClassBirthChart

/-!
# The birth masses of the old terms against the step mass (`BirthMassFlow`)

Ruling R6: the old term of level `j` lives on the domain at its birth mass
`μ_j = ν_j L^{-2j}`; the step from the scale `k` reads it at the step mass `ν_k L^{-2k}`.  Along the
renormalized flow `ν_{n+1} = ν_n L² (1 + ξ₃^{(n)})/(1 + ξ₂^{(n)})` with
`‖ξ_n‖ ≤ (c₈/4) q^{n+1}` (P4 (5.28), (5.31); the coefficient bounds of the class), the step mass is
the birth mass times `∏_{n ∈ [j, k)} (1 + ξ₃)/(1 + ξ₂)` (`mass_relation_of_nuSeq`), within the
factor `1 ± τ₁`, `τ₁ = exp (3 (c₈/4) q²/(1 - q)) - 1` for `j ≥ 1`
(`norm_ratio_prod_sub_one_le_geom`); hence the birth mass is the step mass times `1 + t_j` with
`|t_j| ≤ 2 τ₁` when `τ₁ ≤ 1/2`.

* `birthMass_defect_of_flow`.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Finset Balaban Balaban.SmallField Balaban.Flow

variable {L : ℕ} [NeZero L]

/-- **The birth masses are within the factor `1 ± 2τ₁` of the step mass along the flow.** For the
masses `ν_n = nuSeq ξ ν₀ n` of the flow up to the scale `k`, with `‖ξ_n‖ ≤ (c₈/4) q^{n+1}`,
`c₈ q ≤ 1 - q` and `τ₁ = exp (3 (c₈/4) q²/(1 - q)) - 1 ≤ 1/2`, the birth mass `ν_j L^{-2j}` of every
level `1 ≤ j ≤ k` is `ν_k L^{-2k} (1 + t_j)` with `|t_j| ≤ 2 τ₁`. -/
theorem birthMass_defect_of_flow {ξ : ℕ → Fin 3 → ℂ} {q c₈ ν₀ : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hc : 0 ≤ c₈) (hs : c₈ * q ≤ 1 - q) (hξ : ∀ n, ‖ξ n‖ ≤ c₈ / 4 * q ^ (n + 1))
    (hτ : Real.exp (3 * (c₈ / 4 * (q ^ 2 / (1 - q)))) - 1 ≤ 1 / 2)
    {νs : ℕ → ℝ} {k : ℕ} (hν : ∀ n, n ≤ k → ((νs n : ℝ) : ℂ) = nuSeq (L : ℝ) ξ (ν₀ : ℂ) n) :
    ∀ j, 1 ≤ j → j ≤ k → ∃ t : ℝ, Def6v2.physMass L j (νs j) =
      Def6v2.physMass L k (νs k) * (1 + t) ∧
      |t| ≤ 2 * (Real.exp (3 * (c₈ / 4 * (q ^ 2 / (1 - q)))) - 1) := by
  intro j hj1 hjk
  have hL : ((L : ℝ) : ℂ) ≠ 0 := by
    have : (L : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne L
    exact_mod_cast this
  have hLr : (L : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne L
  have hpm : ∀ n, ((Def6v2.physMass L n (νs n) : ℝ) : ℂ) * ((L : ℝ) : ℂ) ^ (2 * n) =
      nuSeq (L : ℝ) ξ (ν₀ : ℂ) n ∨ n > k := by
    intro n
    by_cases hn : n ≤ k
    · left
      rw [← hν n hn]
      have hLn : (L : ℝ) ^ n ≠ 0 := pow_ne_zero n hLr
      have hr : (νs n * ((L : ℝ) ^ n)⁻¹ ^ 2) * ((L : ℝ) ^ n) ^ 2 = νs n := by field_simp
      unfold Def6v2.physMass
      calc ((νs n * ((L : ℝ) ^ n)⁻¹ ^ 2 : ℝ) : ℂ) * ((L : ℝ) : ℂ) ^ (2 * n) =
          (((νs n * ((L : ℝ) ^ n)⁻¹ ^ 2) * ((L : ℝ) ^ n) ^ 2 : ℝ) : ℂ) := by
            push_cast; ring
        _ = ((νs n : ℝ) : ℂ) := by rw [hr]
    · exact Or.inr (by omega)
  have hj : ((Def6v2.physMass L j (νs j) : ℝ) : ℂ) * ((L : ℝ) : ℂ) ^ (2 * j) =
      nuSeq (L : ℝ) ξ (ν₀ : ℂ) j := (hpm j).resolve_right (by omega)
  have hk : ((Def6v2.physMass L k (νs k) : ℝ) : ℂ) * ((L : ℝ) : ℂ) ^ (2 * k) =
      nuSeq (L : ℝ) ξ (ν₀ : ℂ) k := (hpm k).resolve_right (by omega)
  have hrel := mass_relation_of_nuSeq hjk hj hk
  set P := ∏ n ∈ Ico j k, ((1 + ξ n 2) / (1 + ξ n 1)) with hP
  set τ₁ := Real.exp (3 * (c₈ / 4 * (q ^ 2 / (1 - q)))) - 1 with hτ₁
  have hbd : ‖P - 1‖ ≤ τ₁ := by
    refine (norm_ratio_prod_sub_one_le_geom hq0 hq1 hc hs hξ j k).trans ?_
    have hq : 0 < 1 - q := by linarith
    have hpow : q ^ (j + 1) ≤ q ^ 2 := pow_le_pow_of_le_one hq0 hq1.le (by omega)
    have : 3 * (c₈ / 4 * (q ^ (j + 1) / (1 - q))) ≤ 3 * (c₈ / 4 * (q ^ 2 / (1 - q))) := by
      gcongr
    linarith [Real.exp_le_exp.2 this]
  have hτ0 : 0 ≤ τ₁ := (norm_nonneg _).trans hbd
  have hP0 : P ≠ 0 := by
    intro h0
    rw [h0, zero_sub, norm_neg, norm_one] at hbd
    linarith
  have hnP : 1 - τ₁ ≤ ‖P‖ := by
    have := norm_sub_norm_le (1 : ℂ) P
    rw [norm_one, norm_sub_rev] at this
    linarith
  have hrel' : ((Def6v2.physMass L j (νs j) : ℝ) : ℂ) =
      (Def6v2.physMass L k (νs k) : ℝ) * P⁻¹ := by
    rw [hrel]
    field_simp
  obtain ⟨t, ht, htb⟩ := exists_real_defect hrel'
  refine ⟨t, ht, htb.trans ?_⟩
  have hnP0 : 0 < ‖P‖ := by linarith
  have e : P⁻¹ - 1 = (1 - P) / P := by field_simp
  rw [e, norm_div, ← norm_neg, neg_sub, div_le_iff₀ hnP0]
  nlinarith

end Balaban.Fluctuation
