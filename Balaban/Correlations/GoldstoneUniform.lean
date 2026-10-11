/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Correlations.Asymptotics

/-!
# The (4.18) step with a constant independent of the running coefficients

`goldstone_uniform` is `goldstone_rewriting` with the constant `C'` chosen before `ξ` (it depends
only on `d, L, γ₀, δ`, not on `c₈`); the proof is that of `goldstone_rewriting`.  Needed because the constants
of Root-C are fixed before `β`, hence before the running coefficients `ξ(0)` of C-1*.
-/

@[expose] public section

open Filter Topology Finset

namespace Balaban

open Flow

/-- The conclusion of `goldstone_uniform` for a given constant `C'`. -/
def GoldBound (L : ℝ) (d : ℕ) (γ₀ δ C' : ℝ) : Prop :=
  ∀ {c₈ : ℝ}, 0 ≤ c₈ → ∀ {ξ : ℕ → Fin 3 → ℂ}, c₈ * rate L γ₀ ≤ 1 - rate L γ₀ →
      (∀ k, ‖ξ k‖ ≤ c₈ / 4 * rate L γ₀ ^ (k + 1)) →
    ∃ γ : ℂ, Tendsto (gammaSeq ξ) atTop (𝓝 γ) ∧
      ‖γ - 1‖ ≤ c₈ * rate L γ₀ / (2 * (1 - rate L γ₀)) ∧
      ∀ (β : ℂ) (C r : ℝ) (t : ℕ → ℝ), 0 ≤ C → 0 ≤ r →
        KernelDecay d L C δ r t →
        Summable (fun j => (betaSeq L d ξ β j)⁻¹ * ((L : ℂ) ^ (j * (d - 2)) * (t j : ℂ))) ∧
        ‖∑' j, (betaSeq L d ξ β j)⁻¹ * ((L : ℂ) ^ (j * (d - 2)) * (t j : ℂ)) -
            (β * γ)⁻¹ * ∑' j, (t j : ℂ)‖ ≤
          Real.exp 2 * (c₈ * rate L γ₀ / (2 * (1 - rate L γ₀))) * ‖β⁻¹‖ * C * C' *
            (1 + r) ^ (-(((d - 2 : ℕ) : ℝ) + 2 * γ₀))

/-- `goldstone_rewriting` with `C'` independent of `ξ`. -/
theorem goldstone_uniform {L : ℝ} (hL : 1 < L) (d : ℕ) (hd : 3 ≤ d) {γ₀ δ : ℝ}
    (hγ₀ : 0 < γ₀) (hδ : 0 < δ) :
    ∃ C' : ℝ, 0 ≤ C' ∧ GoldBound L d γ₀ δ C' := by
  have hL0 : 0 < L := by linarith
  have hq0 : 0 ≤ rate L γ₀ := (rate_pos hL0 γ₀).le
  have hq1 : rate L γ₀ < 1 := rate_lt_one hL hγ₀
  have hσ : 0 < ((d - 2 : ℕ) : ℝ) + 2 * γ₀ := by positivity
  obtain ⟨C', hC'0, hC'⟩ := Correlations.sum_pow_exp_le hσ hδ hL
  refine ⟨C', hC'0, fun {c₈} hc {ξ} hs hξ => ?_⟩
  obtain ⟨γ, hT, hγ1, hasym⟩ :=
    exists_inv_betaSeq_asymptotics hL0 d hq0 hq1 hc hs hξ
  refine ⟨γ, hT, hγ1, ?_⟩
  intro β C r t hC hr ht
  set q := rate L γ₀ with hqdef
  set K : ℝ := Real.exp 2 * (c₈ * q / (2 * (1 - q))) with hK
  set σ : ℝ := ((d - 2 : ℕ) : ℝ) + 2 * γ₀ with hσdef
  have hK0 : 0 ≤ K := by
    have : 0 < 1 - q := by linarith
    rw [hK]; positivity
  -- the comparison terms
  set h : ℕ → ℝ := fun j => L ^ (-((j : ℝ) * σ)) * Real.exp (-(δ * r / L ^ j)) with hh
  have hh0 : ∀ j, 0 ≤ h j := fun j => by positivity
  set f : ℕ → ℝ := fun j => K * ‖β⁻¹‖ * C * h j with hf
  have hhsum : ∀ J, ∑ j ∈ range J, h j ≤ C' * (1 + r) ^ (-σ) := fun J => hC' J r hr
  have hhS : Summable h := summable_of_sum_range_le hh0 hhsum
  have hhtsum : ∑' j, h j ≤ C' * (1 + r) ^ (-σ) :=
    Real.tsum_le_of_sum_range_le hh0 hhsum
  have hfS : Summable f := hhS.mul_left _
  -- term bound
  have hterm : ∀ j, ‖(betaSeq L d ξ β j)⁻¹ * ((L : ℂ) ^ (j * (d - 2)) * (t j : ℂ)) -
      (β * γ)⁻¹ * (t j : ℂ)‖ ≤ f j := by
    intro j
    have hco := norm_inv_betaSeq_mul_sub_le hL0 d (γ := γ) (β := β) (q := q) (K := K) (ξ := ξ) j
      (by simpa only [hK, hqdef, mul_assoc] using hasym β j)
    have e : (betaSeq L d ξ β j)⁻¹ * ((L : ℂ) ^ (j * (d - 2)) * (t j : ℂ)) -
        (β * γ)⁻¹ * (t j : ℂ) =
        ((betaSeq L d ξ β j)⁻¹ * (L : ℂ) ^ (j * (d - 2)) - (β * γ)⁻¹) * (t j : ℂ) := by ring
    rw [e, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have hinv := inv_pow_mul_rate_pow hL0 γ₀ d j
    have h2 : K * ‖β⁻¹‖ * q ^ j * (C * (L ^ (j * (d - 2)))⁻¹ * Real.exp (-(δ * r / L ^ j))) =
        f j := by
      simp only [hf, hh]
      rw [← hσdef] at hinv
      rw [← hinv, hqdef]
      ring
    rw [← h2]
    exact mul_le_mul hco (ht j) (abs_nonneg _) (by positivity)
  -- summability of the kernel series
  have htS : Summable (fun j => (t j : ℂ)) := by
    have hgeo : Summable (fun j : ℕ => C * (((L ^ (d - 2))⁻¹) ^ j)) := by
      refine Summable.mul_left _ (summable_geometric_of_lt_one (by positivity) ?_)
      exact inv_lt_one_of_one_lt₀ (one_lt_pow₀ hL (by omega))
    refine Summable.of_norm_bounded hgeo fun j => ?_
    rw [Complex.norm_real, Real.norm_eq_abs]
    refine (ht j).trans ?_
    have hex : Real.exp (-(δ * r / L ^ j)) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      have : 0 ≤ δ * r / L ^ j := by positivity
      linarith
    have hx : (L ^ (j * (d - 2)))⁻¹ = ((L ^ (d - 2))⁻¹) ^ j := by
      rw [inv_pow, ← pow_mul, mul_comm]
    rw [hx]
    calc _ ≤ C * ((L ^ (d - 2))⁻¹) ^ j * 1 := by
          apply mul_le_mul_of_nonneg_left hex (by positivity)
      _ = _ := by ring
  have hdiffS : Summable (fun j => (betaSeq L d ξ β j)⁻¹ * ((L : ℂ) ^ (j * (d - 2)) * (t j : ℂ)) -
      (β * γ)⁻¹ * (t j : ℂ)) := Summable.of_norm_bounded hfS hterm
  have huS : Summable (fun j => (betaSeq L d ξ β j)⁻¹ * ((L : ℂ) ^ (j * (d - 2)) * (t j : ℂ))) := by
    have := hdiffS.add (htS.mul_left ((β * γ)⁻¹))
    simpa using this
  refine ⟨huS, ?_⟩
  have hsub : ∑' j, (betaSeq L d ξ β j)⁻¹ * ((L : ℂ) ^ (j * (d - 2)) * (t j : ℂ)) -
      (β * γ)⁻¹ * ∑' j, (t j : ℂ) =
      ∑' j, ((betaSeq L d ξ β j)⁻¹ * ((L : ℂ) ^ (j * (d - 2)) * (t j : ℂ)) -
        (β * γ)⁻¹ * (t j : ℂ)) := by
    rw [Summable.tsum_sub huS (htS.mul_left _), Summable.tsum_mul_left _ htS]
  rw [hsub]
  refine (tsum_of_norm_bounded hfS.hasSum hterm).trans ?_
  rw [hf]
  simp only
  rw [tsum_mul_left]
  calc K * ‖β⁻¹‖ * C * ∑' j, h j ≤ K * ‖β⁻¹‖ * C * (C' * (1 + r) ^ (-σ)) :=
        mul_le_mul_of_nonneg_left hhtsum (by positivity)
    _ = _ := by rw [hσdef]; ring


end Balaban
