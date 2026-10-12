/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Observables.SecondOrderCauchy
public import Balaban.Observables.SecondOrderSums
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The second-order step of OBSERVABLES.md §3.6, assembled

* `gaussian_main_term` (**Lemma 3.5**): for a centred probability measure with covariance `C` the
  truncated covariance of two linear functions of the vector is `H C H'ᵀ`; times the factors
  `β_k` and `β_k⁻¹` of (3.32) this is the new summand `G^{(k+1)} = H_k C^{(k)} H_k^*`.  (The
  statement that `R₁^{k+1,k+1}` is the first-order-in-`σ` part of the coupled truncated expectation
  concerns the step objects, which are not defined in Lean.)
* `shift_kernel_bound`: the `G^{(j)}`- and `R^{ij}`-shift kernels `C β^{-1} ξ_{k+1}^γ` of §3.7 are
  `≤ ½ β^{-1/2+ρ₁} ξ_{k+1}^{ρ₀}`, i.e. are `R^{j,k+1}`-terms (E5).
* `second_order_old`, `second_order_new`: the rows of the table of §3.6 assembled: for `i ≤ k`
  `R₁^{i,k+1} + R₂^{i,k+1} ≤ β^{-1/2+ρ₁} ξ_{k+1}^{ρ₀}`; for `i = k+1` the three rows
  `R₁^{k+1,k+1} + R₂^{k+1,k+1} + R₃^{k+1,k+1} ≤ β^{-1/2+ρ₁} ξ_{k+1}^{ρ₀}`.  The hypotheses are the
  Cauchy chains / size bounds of the rows (P9 (3.28), (3.30), (3.37), (3.39), (3.41)); the decay
  factors in `|x - x'|` are carried separately by the polymer.
-/

@[expose] public section

namespace Balaban.Observables

open Real MeasureTheory

/-- **Lemma 3.5 (the Gaussian main term).**  Let `μ` be a probability measure on `ι → ℝ` with
integrable coordinate products, mean zero and covariance `C a b = ∫ ψ_a ψ_b`.  For linear
functions `(Hψ)_p = ∑_a H p a ψ_a`, `(H'ψ)_q = ∑_b H' q b ψ_b`, and `β_k ≠ 0`,
`β_k · β_k⁻¹ · (E[(Hψ)_p (H'ψ)_q] - E[(Hψ)_p] E[(H'ψ)_q]) = ∑_{a,b} H p a C a b H' q b`. -/
theorem gaussian_main_term {ι κ : Type*} [Fintype ι] [Fintype κ] (μ : Measure (ι → ℝ))
    [IsProbabilityMeasure μ] (hint : ∀ a b, Integrable (fun ψ : ι → ℝ => ψ a * ψ b) μ)
    (hint1 : ∀ a, Integrable (fun ψ : ι → ℝ => ψ a) μ) (hmean : ∀ a, ∫ ψ, ψ a ∂μ = 0)
    (C : ι → ι → ℝ) (hC : ∀ a b, C a b = ∫ ψ, ψ a * ψ b ∂μ) (H H' : κ → ι → ℝ) (p q : κ)
    {βk : ℝ} (hβk : βk ≠ 0) :
    βk * (βk⁻¹ * ((∫ ψ, (∑ a, H p a * ψ a) * (∑ b, H' q b * ψ b) ∂μ) -
        (∫ ψ, ∑ a, H p a * ψ a ∂μ) * (∫ ψ, ∑ b, H' q b * ψ b ∂μ))) =
      ∑ a, ∑ b, H p a * C a b * H' q b := by
  have hmean1 : ∀ (K : ι → ℝ), ∫ ψ, ∑ a, K a * ψ a ∂μ = 0 := by
    intro K
    rw [integral_finsetSum _ (fun a _ => (hint1 a).const_mul (K a))]
    simp [integral_const_mul, hmean]
  have hexp : ∀ ψ : ι → ℝ, (∑ a, H p a * ψ a) * (∑ b, H' q b * ψ b) =
      ∑ a, ∑ b, H p a * H' q b * (ψ a * ψ b) := by
    intro ψ
    rw [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
    ring
  have hI : ∫ ψ, (∑ a, H p a * ψ a) * (∑ b, H' q b * ψ b) ∂μ =
      ∑ a, ∑ b, H p a * C a b * H' q b := by
    simp_rw [hexp]
    rw [integral_finsetSum _ (fun a _ => integrable_finsetSum _
      (fun b _ => (hint a b).const_mul _))]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [integral_finsetSum _ (fun b _ => (hint a b).const_mul _)]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    rw [integral_const_mul, ← hC]; ring
  rw [hI, hmean1, hmean1, zero_mul, sub_zero, ← mul_assoc, mul_inv_cancel₀ hβk, one_mul]

/-- The `G^{(j)}`- and `R^{ij}`-shift kernels of §3.7 (P9 (3.47)-(3.48)): `x ≤ C β^{-1} ξ_{k+1}^γ`
is a `R^{j,k+1}`-term, `x ≤ ½ β^{-1/2+ρ₁} ξ_{k+1}^{ρ₀}`, for `2 C ≤ β^{1/2+ρ₁}` (E5). -/
theorem shift_kernel_bound {d : ℕ} {γ α₁ ρ₀ ρ₁ ρ₂ : ℝ}
    (hE : ExponentConstraints d γ α₁ ρ₀ ρ₁ ρ₂) (S : StepScale ((d : ℝ) - 2) ρ₂) {C x : ℝ}
    (hC : 0 ≤ C) (hx : x ≤ C * (S.β ^ (-1 : ℝ) * S.ξ ^ γ))
    (hβ0 : 2 * C ≤ S.β ^ (1 / 2 + ρ₁)) :
    x ≤ 1 / 2 * S.β ^ (-(1 / 2 : ℝ) + ρ₁) * S.ξ ^ ρ₀ := by
  have hβp := S.β_pos
  have hξ := S.ξ_pos
  have hξγ : S.ξ ^ γ ≤ S.ξ ^ ρ₀ :=
    Real.rpow_le_rpow_of_exponent_ge hξ S.ξ_le_one hE.E5
  have hone : S.β ^ (1 / 2 + ρ₁) * S.β ^ (-1 : ℝ) = S.β ^ (-(1 / 2 : ℝ) + ρ₁) := by
    rw [← Real.rpow_add hβp]; congr 1; ring
  have hb : 0 ≤ S.β ^ (-1 : ℝ) := Real.rpow_nonneg hβp.le _
  calc x ≤ C * (S.β ^ (-1 : ℝ) * S.ξ ^ γ) := hx
    _ ≤ C * (S.β ^ (-1 : ℝ) * S.ξ ^ ρ₀) := by gcongr
    _ = (C * S.β ^ (-1 : ℝ)) * S.ξ ^ ρ₀ := by ring
    _ ≤ (1 / 2 * S.β ^ (-(1 / 2 : ℝ) + ρ₁)) * S.ξ ^ ρ₀ := by
        refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg hξ.le _)
        rw [← hone]
        have := mul_le_mul_of_nonneg_right hβ0 hb
        nlinarith [this]
    _ = _ := by ring

/-- The constant `K = 4 C/(c c₁)^{m+1} (2 C_p)^{m+1} √2` of `cauchy_chain_pre`. -/
noncomputable def chainConst (Cp c c₁ C : ℝ) (m : ℕ) : ℝ :=
  4 * C / (c * c₁) ^ (m + 1) * (2 * Cp) ^ (m + 1) * √2

theorem chainConst_nonneg {Cp c c₁ C : ℝ} (hCp : 0 ≤ Cp) (hc : 0 < c) (hc₁ : 0 < c₁)
    (hC : 0 ≤ C) (m : ℕ) : 0 ≤ chainConst Cp c c₁ C m := by
  unfold chainConst; positivity

section Assembly

variable {d : ℕ} {γ α₁ ρ₀ ρ₁ ρ₂ : ℝ}

/-- **The rows `R₁^{i,k+1} + R₂^{i,k+1}`, `i ≤ k`** (OBSERVABLES §3.6; P9 (3.28), (3.30)): the
coupling Cauchy chain of `R₁` (`m = 0`, background radius, `C_g = G₀`-type size) and the terms of
`R₂ = ∑_{i ≤ j ≤ k} ⟨δR^{ij}⟩` give, for `β ≥ β₀` (`hβ₁`, `hβ₂`),
`R₁ + R₂ ≤ β^{-1/2+ρ₁} ξ_{k+1}^{ρ₀}` (the decay in `|x-x'|` is carried separately). -/
theorem second_order_old (hE : ExponentConstraints d γ α₁ ρ₀ ρ₁ ρ₂)
    (S : StepScale ((d : ℝ) - 2) ρ₂) (k i : ℕ) (hηk : S.η = ((S.L ^ k)⁻¹ : ℝ))
    {c c₁ α εo εn Cg x₁ : ℝ} (hc : 0 < c) (hc₁ : 0 < c₁) (hCg : 0 ≤ Cg)
    (hx₁ : x₁ ≤ 4 / couplingRadius c c₁ S.βk S.p1 *
      (1 / fieldRadius c c₁ α εo εn S.p1 RadiusCase.background) ^ 0 * Cg)
    (xs : ℕ → ℝ) {K : ℝ} (hK : 0 ≤ K)
    (hj : ∀ j ∈ Finset.Icc i k, xs j ≤ K * S.β ^ (-1 + ρ₁ + ρ₂) *
      (((S.L ^ j)⁻¹ : ℝ)) ^ (ρ₀ - ((d : ℝ) - 2) / 2 + γ) *
        S.η ^ (((d : ℝ) - 2) / 2 - ((d : ℝ) - 2) * ρ₂))
    (hβ₁ : 2 * chainConst S.Cp c c₁ Cg 0 * S.L ^ ρ₀ ≤ S.β ^ ρ₂)
    (hβ₂ : 2 * (K * (S.L ^ (γ - ((d : ℝ) - 2) * ρ₂) /
        (S.L ^ (γ - ((d : ℝ) - 2) * ρ₂) - 1))) * S.L ^ ρ₀ ≤ S.β ^ (1 / 2 - ρ₂)) :
    x₁ + ∑ j ∈ Finset.Icc i k, xs j ≤ S.β ^ (-(1 / 2 : ℝ) + ρ₁) * S.ξ ^ ρ₀ := by
  have hρ2 := hE.ρ₂_pos
  have hρ2' : ρ₂ ≤ 1 := by have := hE.E1; have := hE.ρ₁_lt_one; linarith
  have hCp : 0 ≤ S.Cp := by linarith [S.hCp]
  have h1 := cauchy_chain_pre S hρ2 hρ2' 0 hc hc₁ hCg hx₁
  have h1' := cauchy_chain_final hE S 0 (by norm_num) (K := chainConst S.Cp c c₁ Cg 0)
    (chainConst_nonneg hCp hc hc₁ hCg 0) (by simpa [chainConst] using h1) hβ₁
  have h2 := R2old_final hE S k i hηk xs hK hj hβ₂
  linarith

/-- **The rows `R₁ + R₂ + R₃` at the new scale `k+1`** (P9 (3.37), (3.39), (3.41)): the three
rows are each `≤ ¼ β^{-1/2+ρ₁} ξ_{k+1}^{ρ₀}` for `β ≥ β₀` (the thresholds `hβ₁`-`hβ₃` carry the
factor `2` of the splitting), so their sum is `≤ β^{-1/2+ρ₁} ξ_{k+1}^{ρ₀}`. -/
theorem second_order_new (hE : ExponentConstraints d γ α₁ ρ₀ ρ₁ ρ₂)
    (S : StepScale ((d : ℝ) - 2) ρ₂) (k : ℕ) (hηk : S.η = ((S.L ^ k)⁻¹ : ℝ))
    {c c₁ α εo εn Cg x₁ : ℝ} (hc : 0 < c) (hc₁ : 0 < c₁) (hCg : 0 ≤ Cg)
    (hx₁ : x₁ ≤ 4 / couplingRadius c c₁ S.βk S.p1 *
      (1 / fieldRadius c c₁ α εo εn S.p1 RadiusCase.background) ^ 2 * Cg)
    (xs : ℕ → ℝ) {K₂ : ℝ} (hK₂ : 0 ≤ K₂)
    (hj₂ : ∀ j ∈ Finset.Icc 1 k, xs j ≤ K₂ * S.β ^ (-1 + ρ₁ + 2 * ρ₂) *
      (((S.L ^ j)⁻¹ : ℝ)) ^ (ρ₀ + γ - 1) * S.η ^ (1 - 2 * (((d : ℝ) - 2) * ρ₂)))
    (T : Finset (ℕ × ℕ)) (hT : T ⊆ Finset.Icc 1 k ×ˢ Finset.Icc 1 k) (ys : ℕ → ℕ → ℝ)
    {K₃ : ℝ} (hK₃ : 0 ≤ K₃)
    (hj₃ : ∀ p ∈ T, ys p.1 p.2 ≤ K₃ * S.β ^ (-2 + 2 * ρ₁ + 2 * ρ₂) *
      (((S.L ^ p.1)⁻¹ : ℝ)) ^ (ρ₀ + γ - 1) * (((S.L ^ p.2)⁻¹ : ℝ)) ^ (ρ₀ + γ - 1) *
        S.η ^ (2 - 2 * (((d : ℝ) - 2) * ρ₂)))
    (hβ₁ : 2 * (2 * chainConst S.Cp c c₁ Cg 2) * S.L ^ ρ₀ ≤ S.β ^ ρ₂)
    (hβ₂ : 2 * (2 * K₂ * S.L ^ ρ₀ / (S.L ^ (γ - 2 * (((d : ℝ) - 2) * ρ₂)) - 1)) ≤
      S.β ^ (1 / 2 - 2 * ρ₂))
    (hβ₃ : 2 * (2 * K₃ * S.L ^ ρ₀ / (S.L ^ (γ - ((d : ℝ) - 2) * ρ₂) - 1) ^ 2) ≤
      S.β ^ (3 / 2 - ρ₁ - 2 * ρ₂)) :
    x₁ + ∑ j ∈ Finset.Icc 1 k, xs j + ∑ p ∈ T, ys p.1 p.2 ≤
      S.β ^ (-(1 / 2 : ℝ) + ρ₁) * S.ξ ^ ρ₀ := by
  have hρ2 := hE.ρ₂_pos
  have hρ2' : ρ₂ ≤ 1 := by have := hE.E1; have := hE.ρ₁_lt_one; linarith
  have hCp : 0 ≤ S.Cp := by linarith [S.hCp]
  have h1 := cauchy_chain_pre S hρ2 hρ2' 2 hc hc₁ hCg hx₁
  have h1' := cauchy_chain_final hE S 2 le_rfl (K := 2 * chainConst S.Cp c c₁ Cg 2) (x := 2 * x₁)
    (by have := chainConst_nonneg hCp hc hc₁ hCg 2; positivity)
    (by
      have h := mul_le_mul_of_nonneg_left h1 (by norm_num : (0 : ℝ) ≤ 2)
      refine h.trans (le_of_eq ?_)
      unfold chainConst
      push_cast; ring) hβ₁
  have h2 := R2new_final hE S k hηk (fun j => 2 * xs j) (mm := 2) (K := 2 * K₂) le_rfl
    (by positivity)
    (fun j hjm => by
      have := mul_le_mul_of_nonneg_left (hj₂ j hjm) (by norm_num : (0 : ℝ) ≤ 2)
      refine this.trans (le_of_eq ?_); ring) (by simpa [mul_assoc] using hβ₂)
  have h3 := R3_final hE S k hηk T hT (fun a b => 2 * ys a b) (K := 2 * K₃) (by positivity)
    (fun p hp => by
      have := mul_le_mul_of_nonneg_left (hj₃ p hp) (by norm_num : (0 : ℝ) ≤ 2)
      refine this.trans (le_of_eq ?_); ring) (by simpa [mul_assoc] using hβ₃)
  rw [← Finset.mul_sum] at h2 h3
  have hpos : 0 ≤ S.β ^ (-(1 / 2 : ℝ) + ρ₁) * S.ξ ^ ρ₀ := by
    have := S.ξ_pos; have := S.β_pos; positivity
  nlinarith

end Assembly

end Balaban.Observables
