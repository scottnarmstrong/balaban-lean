/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Observables.FirstOrderBounds
public import Balaban.Observables.ImprovedBound
public import Balaban.SmallField.Def6
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The first-order step of OBSERVABLES.md §3.5-§3.7, assembled

The scalar inequalities of the first-order step (`FirstOrderBounds.lean`) are chained:

* `T1_pre_bound`: the *pre-conversion* form of (3.17), `x ≤ C β^{-1/2+2ρ₂} ξ^{(d-2)/2-2(d-2)ρ₂}`
  (the form `mu_bound` consumes; `T1_bound` is the final form);
* `T2_bound_ge`: T2 (3.6) with `ε_{k+1} ≥ α₀ ξ^{(d-2)/2-γ}` (the actual `ε_{k+1} = α₀ (1 + ∑_{n ≥
  k+1} n^{-2}) ξ_{k+1}^α` is *larger* than `α₀ ξ^α`; the former `T2_bound` assumed equality, which
  no admissible `ε` satisfies (`T2_bound_hyp_false`), and was deleted);
* `F0_of_improved`: the size `F₀` of Lemma 3.4 on `Ψ^c_j(C₀ L^j η, ε_k)`:
  `C₁ s / ε_j ≤ C (L^j η)^{(d-2)/2+1-γ}` for `s = σ ε_k`, `σ = C₀ L^j η`, `ε_k ≤ C_ε (L^jη)^α ε_j`;
* `T2_total_pre`, `T2_scale_total`: the sum over the scales `j ≤ k` of the terms (3.6) in the form
  `C₂ β^{-1+ρ₁+ρ₂} ξ_{k+1}^{ρ₀}` (P9 (3.23)), with `ξ_j = L^{-j}`, `η = L^{-k}`;
* `first_order_step`: the scalar `μ_{k+1}`: `K₀ (t₁ + ∑_j t₂ⱼ + t₃ + t₄ + t₅) ≤ ½ β^{-1/2+ρ₁}
  ξ_{k+1}^{ρ₀}` (§3.7), the terms (3.3) are `R^{j,k+1}`-terms, and the normalization (3.2).

The step objects themselves (the fluctuation expectation, `M_u^{(k+1)}`) are not defined in Lean, so
the hypotheses are the size inequalities that Proposition 3.3 (`coupled_marked_cubes_schwarz`), Lemma
3.4 (`improved_first_of_slice`, `improved_second_bound`) and the cited bounds on the renormalization
shifts (P4 (4.7)-(4.11)) and on `ℛ` (Lemma 3.2) deliver.
-/

@[expose] public section

namespace Balaban.Observables

open Real

section T1T2

/-- **T1, pre-conversion form** (P9 (3.17), second line): under the Cauchy chain of `T1_bound`,
`x ≤ K (2 C_p)² √2 L^{e} β^{-1/2+2ρ₂} ξ^{e}`, `e = (d-2)/2 - 2(d-2)ρ₂`, `K = 4 C_m/(c c₁)²`. -/
theorem T1_pre_bound {d : ℕ} {γ α₁ ρ₀ ρ₁ ρ₂ : ℝ} (hE : ExponentConstraints d γ α₁ ρ₀ ρ₁ ρ₂)
    (S : StepScale ((d : ℝ) - 2) ρ₂) {c c₁ α εo εn Cm x : ℝ} (hc : 0 < c) (hc₁ : 0 < c₁)
    (hCm : 0 ≤ Cm)
    (hx : x ≤ 4 / couplingRadius c c₁ S.βk S.p1 *
      (1 / fieldRadius c c₁ α εo εn S.p1 RadiusCase.background) * Cm) :
    x ≤ (4 * Cm / (c * c₁) ^ 2 * (2 * S.Cp) ^ 2 * √2 *
        S.L ^ (((d : ℝ) - 2) / 2 - 2 * ((d : ℝ) - 2) * ρ₂)) *
      (S.β ^ (-(1 / 2 : ℝ) + 2 * ρ₂) * S.ξ ^ (((d : ℝ) - 2) / 2 - 2 * ((d : ℝ) - 2) * ρ₂)) := by
  have hD : (1 : ℝ) ≤ (d : ℝ) - 2 := S.hD
  have hβp := S.β_pos
  have hβk := S.βk_pos
  have hp1 : 0 < S.p1 := by linarith [S.hp1]
  have hρ2 := hE.ρ₂_pos
  have hρ2' : ρ₂ ≤ 1 := by
    have := hE.E1; have := hE.ρ₁_lt_one; linarith
  have hsq : 0 < √S.βk := Real.sqrt_pos.2 hβk
  have h1 : 4 / couplingRadius c c₁ S.βk S.p1 *
      (1 / fieldRadius c c₁ α εo εn S.p1 RadiusCase.background) * Cm =
      (4 * Cm / (c * c₁) ^ 2) * S.p1 ^ 2 * S.βk ^ (-(1 / 2 : ℝ)) := by
    unfold couplingRadius fieldRadius
    rw [Real.rpow_neg hβk.le, ← Real.sqrt_eq_rpow]
    field_simp
  have hK : 0 ≤ 4 * Cm / (c * c₁) ^ 2 := by positivity
  have hp2 : S.p1 ^ 2 ≤ (2 * S.Cp) ^ 2 * S.β ^ (2 * ρ₂) * S.η ^ (-(2 * ((d - 2 : ℝ) * ρ₂))) := by
    have := S.p1_pow_le hρ2.le hρ2' (s := 2) (by norm_num)
    simpa [Real.rpow_two, Real.rpow_natCast] using this
  have hb1 := S.betak_inv_sqrt_le
  have hη0 := S.hη0
  rw [h1] at hx
  have hmain : x ≤ (4 * Cm / (c * c₁) ^ 2) *
      ((2 * S.Cp) ^ 2 * S.β ^ (2 * ρ₂) * S.η ^ (-(2 * ((d - 2 : ℝ) * ρ₂)))) *
      (√2 * S.β ^ (-(1 / 2 : ℝ)) * S.η ^ ((d - 2 : ℝ) / 2)) :=
    hx.trans (mul_le_mul (mul_le_mul_of_nonneg_left hp2 hK) hb1
      (Real.rpow_nonneg hβk.le _) (by positivity))
  refine hmain.trans (le_of_eq ?_)
  have e1 : S.β ^ (2 * ρ₂) * S.β ^ (-(1 / 2 : ℝ)) = S.β ^ (-(1 / 2 : ℝ) + 2 * ρ₂) := by
    rw [← Real.rpow_add hβp]; congr 1; ring
  have e2 : S.η ^ (-(2 * ((d - 2 : ℝ) * ρ₂))) * S.η ^ ((d - 2 : ℝ) / 2) =
      S.η ^ (((d : ℝ) - 2) / 2 - 2 * ((d : ℝ) - 2) * ρ₂) := by
    rw [← Real.rpow_add hη0]; congr 1; ring
  have e3 : S.η ^ (((d : ℝ) - 2) / 2 - 2 * ((d : ℝ) - 2) * ρ₂) =
      S.L ^ (((d : ℝ) - 2) / 2 - 2 * ((d : ℝ) - 2) * ρ₂) *
        S.ξ ^ (((d : ℝ) - 2) / 2 - 2 * ((d : ℝ) - 2) * ρ₂) := S.η_rpow_eq
  calc (4 * Cm / (c * c₁) ^ 2) * ((2 * S.Cp) ^ 2 * S.β ^ (2 * ρ₂) * S.η ^ (-(2 * ((d - 2 : ℝ) * ρ₂)))) *
        (√2 * S.β ^ (-(1 / 2 : ℝ)) * S.η ^ ((d - 2 : ℝ) / 2))
      = (4 * Cm / (c * c₁) ^ 2) * (2 * S.Cp) ^ 2 * √2 *
        (S.β ^ (2 * ρ₂) * S.β ^ (-(1 / 2 : ℝ))) *
        (S.η ^ (-(2 * ((d - 2 : ℝ) * ρ₂))) * S.η ^ ((d - 2 : ℝ) / 2)) := by ring
    _ = _ := by rw [e1, e2, e3]; ring

/-- **T2 with `ε_{k+1} ≥ α₀ ξ^{D/2-γ}`** (the former `T2_bound` assumed the equality, impossible by `T2_bound_hyp_false`). -/
theorem T2_bound_ge {D γ ρ₀ ρ₁ ρ₂ : ℝ} (S : StepScale D ρ₂)
    (hρ2 : 0 < ρ₂) (hρ2' : ρ₂ ≤ 1)
    {c c₁ a α₀ εo εn C₃ ξj bj x : ℝ} (hc : 0 < c) (ha : 0 < a) (hα₀ : 0 < α₀) (hC₃ : 0 ≤ C₃)
    (hξj : 0 < ξj) (hbj0 : 0 ≤ bj)
    (hbj : bj ≤ √2 * S.L ^ (D / 2) * S.β ^ (-(1 / 2 : ℝ)) * ξj ^ (D / 2))
    (hεn : α₀ * S.ξ ^ (D / 2 - γ) ≤ εn)
    (hx : x ≤ bj * (1 / fieldRadius c c₁ a εo εn S.p1 RadiusCase.new) *
      (C₃ * S.β ^ (-(1 / 2 : ℝ) + ρ₁) * ξj ^ ρ₀ * (S.η / ξj) ^ (D / 2 + 1 - γ))) :
    x ≤ √2 * S.L ^ (D / 2) * (2 * S.Cp) * S.L ^ (D / 2 - γ) * C₃ /
        (c * a * α₀) * S.β ^ (-1 + ρ₁ + ρ₂) * ξj ^ (ρ₀ + γ - 1) * S.η ^ (1 - D * ρ₂) := by
  have hξk : 0 < S.ξ := S.ξ_pos
  have hp1 : 0 < S.p1 := by linarith [S.hp1]
  have hεpos : 0 < α₀ * S.ξ ^ (D / 2 - γ) := by positivity
  have hmono : 1 / fieldRadius c c₁ a εo εn S.p1 RadiusCase.new ≤
      1 / fieldRadius c c₁ a εo (α₀ * S.ξ ^ (D / 2 - γ)) S.p1 RadiusCase.new := by
    simp only [fieldRadius]
    rw [one_div_div, one_div_div]
    exact div_le_div_of_nonneg_left hp1.le (by positivity)
      (mul_le_mul_of_nonneg_left hεn (by positivity))
  have hF0 : 0 ≤ C₃ * S.β ^ (-(1 / 2 : ℝ) + ρ₁) * ξj ^ ρ₀ * (S.η / ξj) ^ (D / 2 + 1 - γ) := by
    have := S.β_pos; have := S.hη0; positivity
  have hx' : x ≤ bj * (1 / fieldRadius c c₁ a εo (α₀ * S.ξ ^ (D / 2 - γ)) S.p1 RadiusCase.new) *
      (C₃ * S.β ^ (-(1 / 2 : ℝ) + ρ₁) * ξj ^ ρ₀ * (S.η / ξj) ^ (D / 2 + 1 - γ)) :=
    hx.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hmono hbj0) hF0)
  have key : ∀ εn : ℝ, εn = α₀ * S.ξ ^ (D / 2 - γ) →
      x ≤ bj * (1 / fieldRadius c c₁ a εo εn S.p1 RadiusCase.new) *
        (C₃ * S.β ^ (-(1 / 2 : ℝ) + ρ₁) * ξj ^ ρ₀ * (S.η / ξj) ^ (D / 2 + 1 - γ)) →
      x ≤ √2 * S.L ^ (D / 2) * (2 * S.Cp) * S.L ^ (D / 2 - γ) * C₃ /
        (c * a * α₀) * S.β ^ (-1 + ρ₁ + ρ₂) * ξj ^ (ρ₀ + γ - 1) * S.η ^ (1 - D * ρ₂) := by
    intro εn hεn hx
    have hβp := S.β_pos
    have hη0 := S.hη0
    have hLp := S.L_pos
    have hp1 : 0 < S.p1 := by linarith [S.hp1]
    have hξk : 0 < S.ξ := S.ξ_pos
    have hξα : 0 < S.ξ ^ (D / 2 - γ) := Real.rpow_pos_of_pos hξk _
    have hr : 1 / fieldRadius c c₁ a εo εn S.p1 RadiusCase.new = S.p1 / (c * a * εn) := by
      simp only [fieldRadius]
      rw [one_div_div]
    have hεpos : 0 < εn := by rw [hεn]; positivity
    have hp1b := S.p1_pow_le hρ2.le hρ2' (s := 1) (by norm_num)
    simp only [Real.rpow_one, one_mul] at hp1b
    have hF0 : 0 ≤ C₃ * S.β ^ (-(1 / 2 : ℝ) + ρ₁) * ξj ^ ρ₀ * (S.η / ξj) ^ (D / 2 + 1 - γ) := by
      positivity
    have h1 : x ≤ (√2 * S.L ^ (D / 2) * S.β ^ (-(1 / 2 : ℝ)) * ξj ^ (D / 2)) *
        ((2 * S.Cp * S.β ^ ρ₂ * S.η ^ (-(D * ρ₂))) / (c * a * εn)) *
        (C₃ * S.β ^ (-(1 / 2 : ℝ)  + ρ₁) * ξj ^ ρ₀ * (S.η / ξj) ^ (D / 2 + 1 - γ)) := by
      rw [hr] at hx
      refine hx.trans ?_
      have hd : 0 ≤ S.p1 / (c * a * εn) := by positivity
      have e1 : S.p1 / (c * a * εn) ≤ (2 * S.Cp * S.β ^ ρ₂ * S.η ^ (-(D * ρ₂))) / (c * a * εn) :=
        div_le_div_of_nonneg_right (by simpa [mul_assoc] using hp1b) (by positivity)
      exact mul_le_mul_of_nonneg_right (mul_le_mul hbj e1 hd (by positivity)) hF0
    refine h1.trans (le_of_eq ?_)
    -- exponent arithmetic
    have eξ : (S.ξ ^ (D / 2 - γ))⁻¹ = S.L ^ (D / 2 - γ) * S.η ^ (-(D / 2 - γ)) := by
      unfold StepScale.ξ
      rw [Real.div_rpow hη0.le hLp.le, Real.rpow_neg hη0.le]
      field_simp
    have eη : (S.η / ξj) ^ (D / 2 + 1 - γ) = S.η ^ (D / 2 + 1 - γ) * (ξj ^ (D / 2 + 1 - γ))⁻¹ := by
      rw [Real.div_rpow hη0.le hξj.le]; ring
    have eβ : S.β ^ (-(1 / 2 : ℝ)) * S.β ^ ρ₂ * S.β ^ (-(1 / 2 : ℝ) + ρ₁) = S.β ^ (-1 + ρ₁ + ρ₂) := by
      rw [← Real.rpow_add hβp, ← Real.rpow_add hβp]; congr 1; ring
    have eξj : ξj ^ (D / 2) * ξj ^ ρ₀ * (ξj ^ (D / 2 + 1 - γ))⁻¹ = ξj ^ (ρ₀ + γ - 1) := by
      rw [← Real.rpow_neg hξj.le, ← Real.rpow_add hξj, ← Real.rpow_add hξj]; congr 1; ring
    have eη' : S.η ^ (-(D * ρ₂)) * S.η ^ (-(D / 2 - γ)) * S.η ^ (D / 2 + 1 - γ) =
        S.η ^ (1 - D * ρ₂) := by
      rw [← Real.rpow_add hη0, ← Real.rpow_add hη0]; congr 1; ring
    rw [hεn, eη]
    have hc' : c * a * (α₀ * S.ξ ^ (D / 2 - γ)) ≠ 0 := by positivity
    have : (2 * S.Cp * S.β ^ ρ₂ * S.η ^ (-(D * ρ₂))) / (c * a * (α₀ * S.ξ ^ (D / 2 - γ))) =
        (2 * S.Cp * S.β ^ ρ₂ * S.η ^ (-(D * ρ₂))) / (c * a * α₀) * (S.ξ ^ (D / 2 - γ))⁻¹ := by
      field_simp
    rw [this, eξ]
    calc _ = √2 * S.L ^ (D / 2) * (2 * S.Cp) * S.L ^ (D / 2 - γ) * C₃ / (c * a * α₀) *
          (S.β ^ (-(1 / 2 : ℝ)) * S.β ^ ρ₂ * S.β ^ (-(1 / 2 : ℝ) + ρ₁)) *
          (ξj ^ (D / 2) * ξj ^ ρ₀ * (ξj ^ (D / 2 + 1 - γ))⁻¹) *
          (S.η ^ (-(D * ρ₂)) * S.η ^ (-(D / 2 - γ)) * S.η ^ (D / 2 + 1 - γ)) := by ring
      _ = _ := by rw [eβ, eξj, eη']
  exact key _ rfl hx'

/-- **The size `F₀` of Lemma 3.4 on `Ψ^c_j(C₀ L^j η, ε_k)`** (P9 (3.21), OBSERVABLES (3.6)):
with `u = L^j η`, `s ≤ C₀ u ε_k` (`s = σ ε`, `σ = C₀ L^j η`), `ε_k ≤ C_ε u^α ε_j`
(`ε_k/ε_j ≤ 2 (L^jη)^α`, (B2)) and the constant of the improved bound `C_δ ε_j ≤ C₁`
(`C_δ ∝ 1/ε_{j+1}`), `C_δ s ≤ C₁ C₀ C_ε u^{α+1}`; with `α + 1 = (d-2)/2 + 1 - γ`. -/
theorem F0_of_improved {u α C₁ C₀ Cε s εj εk Cδ : ℝ} (hu : 0 < u)
    (hCδ0 : 0 ≤ Cδ) (hC₀ : 0 ≤ C₀) (hCε : 0 ≤ Cε) (hCδ : Cδ * εj ≤ C₁)
    (hs : s ≤ C₀ * u * εk) (hεk : εk ≤ Cε * u ^ α * εj) :
    Cδ * s ≤ C₁ * C₀ * Cε * u ^ (α + 1) := by
  have hpa : 0 < u ^ α := Real.rpow_pos_of_pos hu α
  have e : u ^ (α + 1) = u ^ α * u := Real.rpow_add_one hu.ne' α
  have h1 : Cδ * s ≤ Cδ * (C₀ * u * εk) := mul_le_mul_of_nonneg_left hs hCδ0
  have h2 : Cδ * (C₀ * u * εk) ≤ Cδ * (C₀ * u * (Cε * u ^ α * εj)) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hεk (by positivity)) hCδ0
  have h3 : Cδ * (C₀ * u * (Cε * u ^ α * εj)) = (C₀ * Cε * u ^ (α + 1)) * (Cδ * εj) := by
    rw [e]; ring
  have h4 : (C₀ * Cε * u ^ (α + 1)) * (Cδ * εj) ≤ (C₀ * Cε * u ^ (α + 1)) * C₁ :=
    mul_le_mul_of_nonneg_left hCδ (by positivity)
  calc Cδ * s ≤ _ := h1
    _ ≤ _ := h2
    _ = _ := h3
    _ ≤ _ := h4
    _ = _ := by ring

/-- **T2 summed over the scales, pre-conversion** (P9 (3.23)): if each scale contributes
`x_j ≤ K β^{-1+ρ₁+ρ₂} ξ_j^{γ-(d-2)ρ₂} η^{ρ₀}` (`ξ_j = L^{-j}`), then
`∑_{j ≤ k} x_j ≤ (K L^{ρ₀} / (L^θ - 1)) β^{-1+ρ₁+ρ₂} ξ_{k+1}^{ρ₀}`, `θ = γ - (d-2)ρ₂ > 0` (E4). -/
theorem T2_total_pre {d : ℕ} {γ α₁ ρ₀ ρ₁ ρ₂ : ℝ} (hE : ExponentConstraints d γ α₁ ρ₀ ρ₁ ρ₂)
    (S : StepScale ((d : ℝ) - 2) ρ₂) (k : ℕ) (xs : ℕ → ℝ) {Kc : ℝ} (hK : 0 ≤ Kc)
    (hj : ∀ j ∈ Finset.Icc 1 k, xs j ≤ Kc * S.β ^ (-1 + ρ₁ + ρ₂) *
      (((S.L ^ j)⁻¹ : ℝ)) ^ (γ - ((d : ℝ) - 2) * ρ₂) * S.η ^ ρ₀) :
    ∑ j ∈ Finset.Icc 1 k, xs j ≤
      (Kc * S.L ^ ρ₀ / (S.L ^ (γ - ((d : ℝ) - 2) * ρ₂) - 1)) *
        (S.β ^ (-1 + ρ₁ + ρ₂) * S.ξ ^ ρ₀) := by
  have hβp := S.β_pos
  have hθ : 0 < γ - ((d : ℝ) - 2) * ρ₂ := by
    have := hE.E4; have := hE.ρ₂_pos; have := S.hD; nlinarith
  have hLθ : 1 < S.L ^ (γ - ((d : ℝ) - 2) * ρ₂) := Real.one_lt_rpow (by linarith [S.hL]) hθ
  have hgeo := sum_xi_pow_le S.hL hθ k
  have hsum : ∑ j ∈ Finset.Icc 1 k, xs j ≤ Kc * S.β ^ (-1 + ρ₁ + ρ₂) * S.η ^ ρ₀ *
      (1 / (S.L ^ (γ - ((d : ℝ) - 2) * ρ₂) - 1)) := by
    calc ∑ j ∈ Finset.Icc 1 k, xs j
        ≤ ∑ j ∈ Finset.Icc 1 k, Kc * S.β ^ (-1 + ρ₁ + ρ₂) * S.η ^ ρ₀ *
            (((S.L ^ j)⁻¹ : ℝ)) ^ (γ - ((d : ℝ) - 2) * ρ₂) :=
          Finset.sum_le_sum (fun j hjm => (hj j hjm).trans (le_of_eq (by ring)))
      _ = Kc * S.β ^ (-1 + ρ₁ + ρ₂) * S.η ^ ρ₀ *
            ∑ j ∈ Finset.Icc 1 k, (((S.L ^ j)⁻¹ : ℝ)) ^ (γ - ((d : ℝ) - 2) * ρ₂) :=
          (Finset.mul_sum _ _ _).symm
      _ ≤ _ := by
          have h0 : 0 ≤ Kc * S.β ^ (-1 + ρ₁ + ρ₂) * S.η ^ ρ₀ :=
            mul_nonneg (mul_nonneg hK (Real.rpow_nonneg hβp.le _)) (Real.rpow_nonneg S.hη0.le _)
          exact mul_le_mul_of_nonneg_left hgeo h0
  refine hsum.trans (le_of_eq ?_)
  rw [S.η_rpow_eq (e := ρ₀)]
  ring

/-- **T2, all scales** (the hypotheses are the Cauchy chains (3.20)-(3.21) of the scales `j ≤ k`):
with `ξ_j = L^{-j}`, `η = L^{-k}`, `b_j = β_{j-1}^{-1/2} ≤ √2 L^{D/2} β^{-1/2} ξ_j^{D/2}`, the radius
case `new` with `ε_{k+1} ≥ α₀ ξ_{k+1}^{D/2-γ}`, and the size `F₀` of Lemma 3.4 in the form of
`F0_of_improved`, the sum of the scale contributions is
`≤ C₂ β^{-1+ρ₁+ρ₂} ξ_{k+1}^{ρ₀}` with the explicit constant `C₂`. -/
theorem T2_scale_total {d : ℕ} {γ α₁ ρ₀ ρ₁ ρ₂ : ℝ} (hE : ExponentConstraints d γ α₁ ρ₀ ρ₁ ρ₂)
    (S : StepScale ((d : ℝ) - 2) ρ₂) (k : ℕ) (hηk : S.η = ((S.L ^ k)⁻¹ : ℝ))
    {c c₁ a α₀ εn C₃ : ℝ} (εo xs bj : ℕ → ℝ) (hc : 0 < c) (ha : 0 < a) (hα₀ : 0 < α₀)
    (hC₃ : 0 ≤ C₃) (hεn : α₀ * S.ξ ^ (((d : ℝ) - 2) / 2 - γ) ≤ εn)
    (hb0 : ∀ j ∈ Finset.Icc 1 k, 0 ≤ bj j)
    (hb : ∀ j ∈ Finset.Icc 1 k, bj j ≤ √2 * S.L ^ (((d : ℝ) - 2) / 2) * S.β ^ (-(1 / 2 : ℝ)) *
      (((S.L ^ j)⁻¹ : ℝ)) ^ (((d : ℝ) - 2) / 2))
    (hx : ∀ j ∈ Finset.Icc 1 k, xs j ≤ bj j *
      (1 / fieldRadius c c₁ a (εo j) εn S.p1 RadiusCase.new) *
      (C₃ * S.β ^ (-(1 / 2 : ℝ) + ρ₁) * (((S.L ^ j)⁻¹ : ℝ)) ^ ρ₀ *
        (S.η / (((S.L ^ j)⁻¹ : ℝ))) ^ (((d : ℝ) - 2) / 2 + 1 - γ))) :
    ∑ j ∈ Finset.Icc 1 k, xs j ≤
      ((√2 * S.L ^ (((d : ℝ) - 2) / 2) * (2 * S.Cp) * S.L ^ (((d : ℝ) - 2) / 2 - γ) * C₃ /
          (c * a * α₀)) * S.L ^ ρ₀ / (S.L ^ (γ - ((d : ℝ) - 2) * ρ₂) - 1)) *
        (S.β ^ (-1 + ρ₁ + ρ₂) * S.ξ ^ ρ₀) := by
  have hD : (1 : ℝ) ≤ (d : ℝ) - 2 := S.hD
  have hρ2 := hE.ρ₂_pos
  have hρ2' : ρ₂ ≤ 1 := by
    have := hE.E1; have := hE.ρ₁_lt_one; linarith
  have hLp := S.L_pos
  have hη0 := S.hη0
  have hρ : ρ₀ + ((d : ℝ) - 2) * ρ₂ ≤ 1 := by
    have := hE.E3; nlinarith
  set K : ℝ := √2 * S.L ^ (((d : ℝ) - 2) / 2) * (2 * S.Cp) * S.L ^ (((d : ℝ) - 2) / 2 - γ) * C₃ /
      (c * a * α₀) with hK
  have hK0 : 0 ≤ K := by
    have := S.hCp; have := Real.sqrt_nonneg 2; rw [hK]; positivity
  refine T2_total_pre hE S k xs hK0 (fun j hj => ?_)
  have hj' := Finset.mem_Icc.1 hj
  have hξj : 0 < ((S.L ^ j)⁻¹ : ℝ) := by positivity
  have hηξ : S.η ≤ ((S.L ^ j)⁻¹ : ℝ) := by
    rw [hηk]
    exact inv_anti₀ (by positivity) (pow_le_pow_right₀ (by linarith [S.hL]) hj'.2)
  have h1 := T2_bound_ge S hρ2 hρ2' hc ha hα₀ hC₃ hξj (hb0 j hj) (hb j hj) hεn (hx j hj)
  have h2 := xi_eta_split (γ := γ) (D := (d : ℝ) - 2) (ρ₂ := ρ₂) hξj hη0 hηξ hρ
  have hpre : 0 ≤ K * S.β ^ (-1 + ρ₁ + ρ₂) := by
    have := S.β_pos; positivity
  calc xs j ≤ K * S.β ^ (-1 + ρ₁ + ρ₂) * (((S.L ^ j)⁻¹ : ℝ)) ^ (ρ₀ + γ - 1) *
        S.η ^ (1 - ((d : ℝ) - 2) * ρ₂) := by rw [hK]; exact h1
    _ = K * S.β ^ (-1 + ρ₁ + ρ₂) * ((((S.L ^ j)⁻¹ : ℝ)) ^ (ρ₀ + γ - 1) *
        S.η ^ (1 - ((d : ℝ) - 2) * ρ₂)) := by ring
    _ ≤ K * S.β ^ (-1 + ρ₁ + ρ₂) * ((((S.L ^ j)⁻¹ : ℝ)) ^ (γ - ((d : ℝ) - 2) * ρ₂) *
        S.η ^ ρ₀) := mul_le_mul_of_nonneg_left h2 hpre
    _ = _ := by ring

end T1T2

section Step

/-- **The first-order step, assembled** (OBSERVABLES §3.5-§3.7; P9 pp. 504-514).

Typing data: the exponents `ρ₀, ρ₁, ρ₂` (`ExponentConstraints`, (E1)-(E7)), the step scale
(`StepScale`: `β_k`, `p₁`, `η = L^{-k}`), the radii of Proposition 3.1 (background case for T1, new
case for T2).  Source inputs: the Cauchy chains of T1 (`hx₁`, P9 (3.15)-(3.17)) and of T2 for every
scale `j ≤ k` (`hx`, (3.20)-(3.21), with the size `F₀` of Lemma 3.4), the bounds `t₃, t₄, t₅` of the
two renormalization shifts and of `ℛ` (P4 (4.7)-(4.11), Lemma 3.2), and the entropy constant `K₀ᴼ`.

Conclusions, for `β ≥ β₀` (the explicit inequality `hβ0`):
1. `|μ_{k+1}(x)| ≤ ½ β^{-1/2+ρ₁} ξ_{k+1}^{ρ₀}`;
2. `β_k^{-1/2} |μ_{k+1}| ≤ (√2/2) L^{D/2} β^{-1+ρ₁} ξ_{k+1}^{D/2+ρ₀}`;
3. the terms (3.3) are `R^{j,k+1}`-terms: `(√2/2) L^{D/2} β^{-1+ρ₁} ξ^{D/2+ρ₀} G₀ ≤ β^{-1/2+ρ₁} ξ^{ρ₀}`;
4. the normalization (3.2): `∑_Y (M_u(Y) - μ φ(Y)) = 0` if `∑_Y M_u(Y) = μ h`, `∑_Y φ(Y) = h`. -/
theorem first_order_step {d : ℕ} {γ α₁ ρ₀ ρ₁ ρ₂ : ℝ} (hE : ExponentConstraints d γ α₁ ρ₀ ρ₁ ρ₂)
    (S : StepScale ((d : ℝ) - 2) ρ₂) (k : ℕ) (hηk : S.η = ((S.L ^ k)⁻¹ : ℝ))
    -- T1
    {c₀ c₁ α εo₀ εn₀ Cm t₁ : ℝ} (hc₀ : 0 < c₀) (hc₁ : 0 < c₁) (hCm : 0 ≤ Cm)
    (hx₁ : t₁ ≤ 4 / couplingRadius c₀ c₁ S.βk S.p1 *
      (1 / fieldRadius c₀ c₁ α εo₀ εn₀ S.p1 RadiusCase.background) * Cm)
    -- T2
    {c a α₀ εn C₃ : ℝ} (εo xs bj : ℕ → ℝ) (hc : 0 < c) (ha : 0 < a) (hα₀ : 0 < α₀)
    (hC₃ : 0 ≤ C₃) (hεn : α₀ * S.ξ ^ (((d : ℝ) - 2) / 2 - γ) ≤ εn)
    (hb0 : ∀ j ∈ Finset.Icc 1 k, 0 ≤ bj j)
    (hb : ∀ j ∈ Finset.Icc 1 k, bj j ≤ √2 * S.L ^ (((d : ℝ) - 2) / 2) * S.β ^ (-(1 / 2 : ℝ)) *
      (((S.L ^ j)⁻¹ : ℝ)) ^ (((d : ℝ) - 2) / 2))
    (hx : ∀ j ∈ Finset.Icc 1 k, xs j ≤ bj j *
      (1 / fieldRadius c c₁ a (εo j) εn S.p1 RadiusCase.new) *
      (C₃ * S.β ^ (-(1 / 2 : ℝ) + ρ₁) * (((S.L ^ j)⁻¹ : ℝ)) ^ ρ₀ *
        (S.η / (((S.L ^ j)⁻¹ : ℝ))) ^ (((d : ℝ) - 2) / 2 + 1 - γ)))
    -- the shifts and `ℛ`
    {K0O C₃' C₄ C₅ t₃ t₄ t₅ μ G₀ : ℝ} (hK : 0 ≤ K0O)
    (ht₃ : t₃ ≤ C₃' * (S.β ^ (-(1 / 2 : ℝ)) * S.ξ ^ γ))
    (ht₄ : t₄ ≤ C₄ * (S.β ^ (-(3 / 2 : ℝ) + ρ₁) * S.ξ ^ (2 * γ)))
    (ht₅ : t₅ ≤ C₅ * (S.β ^ (-1 : ℝ) * S.ξ ^ ((d : ℝ) - 2)))
    (hC₃' : 0 ≤ C₃') (hC₄ : 0 ≤ C₄) (hC₅ : 0 ≤ C₅)
    -- `μ_{k+1}(x)` is `K₀ᴼ` times the five contributions, `β ≥ β₀`
    (hμ : |μ| ≤ K0O * (t₁ + ∑ j ∈ Finset.Icc 1 k, xs j + t₃ + t₄ + t₅))
    (hβ0 : 2 * K0O *
      ((4 * Cm / (c₀ * c₁) ^ 2 * (2 * S.Cp) ^ 2 * √2 *
          S.L ^ (((d : ℝ) - 2) / 2 - 2 * ((d : ℝ) - 2) * ρ₂)) +
        ((√2 * S.L ^ (((d : ℝ) - 2) / 2) * (2 * S.Cp) * S.L ^ (((d : ℝ) - 2) / 2 - γ) * C₃ /
          (c * a * α₀)) * S.L ^ ρ₀ / (S.L ^ (γ - ((d : ℝ) - 2) * ρ₂) - 1)) +
        C₃' + C₄ + C₅) ≤ S.β ^ (2 * ρ₂))
    (hG : 0 ≤ G₀) (hD0 : 0 ≤ (d : ℝ) - 2)
    (hβG : √2 / 2 * S.L ^ (((d : ℝ) - 2) / 2) * G₀ ≤ S.β ^ (1 / 2 : ℝ))
    -- the normalization (3.2)
    {ι V : Type*} [Fintype ι] [AddCommGroup V] [Module ℝ V] (Mu φ : ι → V) (h : V)
    (hMu : ∑ Y, Mu Y = μ • h) (hφ : ∑ Y, φ Y = h) :
    |μ| ≤ 1 / 2 * S.β ^ (-(1 / 2 : ℝ) + ρ₁) * S.ξ ^ ρ₀ ∧
    S.βk ^ (-(1 / 2 : ℝ)) * |μ| ≤ √2 / 2 * S.L ^ (((d : ℝ) - 2) / 2) * S.β ^ (-1 + ρ₁) *
      S.ξ ^ (((d : ℝ) - 2) / 2 + ρ₀) ∧
    √2 / 2 * S.L ^ (((d : ℝ) - 2) / 2) * S.β ^ (-1 + ρ₁) * S.ξ ^ (((d : ℝ) - 2) / 2 + ρ₀) * G₀ ≤
      S.β ^ (-(1 / 2 : ℝ) + ρ₁) * S.ξ ^ ρ₀ ∧
    ∑ Y, (Mu Y - μ • φ Y) = 0 := by
  have hρ2 := hE.ρ₂_pos
  set C₁ : ℝ := 4 * Cm / (c₀ * c₁) ^ 2 * (2 * S.Cp) ^ 2 * √2 *
    S.L ^ (((d : ℝ) - 2) / 2 - 2 * ((d : ℝ) - 2) * ρ₂) with hC₁def
  set C₂ : ℝ := (√2 * S.L ^ (((d : ℝ) - 2) / 2) * (2 * S.Cp) * S.L ^ (((d : ℝ) - 2) / 2 - γ) * C₃ /
          (c * a * α₀)) * S.L ^ ρ₀ / (S.L ^ (γ - ((d : ℝ) - 2) * ρ₂) - 1) with hC₂def
  have hLp := S.L_pos
  have hθ : 0 < γ - ((d : ℝ) - 2) * ρ₂ := by
    have := hE.E4; have := S.hD; nlinarith
  have hLθ : 1 < S.L ^ (γ - ((d : ℝ) - 2) * ρ₂) := Real.one_lt_rpow (by linarith [S.hL]) hθ
  have hC₁0 : 0 ≤ C₁ := by
    have := S.hCp; have := Real.sqrt_nonneg 2; rw [hC₁def]; positivity
  have hC₂0 : 0 ≤ C₂ := by
    have := S.hCp; have := Real.sqrt_nonneg 2
    have hden : 0 < S.L ^ (γ - ((d : ℝ) - 2) * ρ₂) - 1 := by linarith
    rw [hC₂def]; positivity
  have ht₁ := T1_pre_bound hE S hc₀ hc₁ hCm hx₁
  have ht₂ := T2_scale_total hE S k hηk εo xs bj hc ha hα₀ hC₃ hεn hb0 hb hx
  have hmu := mu_bound (K0O := K0O) (C₁ := C₁) (C₂ := C₂) (C₃ := C₃') (C₄ := C₄) (C₅ := C₅)
    (t₁ := t₁) (t₂ := ∑ j ∈ Finset.Icc 1 k, xs j) (t₃ := t₃) (t₄ := t₄) (t₅ := t₅) hE S hK
    ht₁ (by simpa [hC₂def] using ht₂) ht₃ ht₄ ht₅ hC₁0 hC₂0 hC₃' hC₄ hC₅ hβ0
  have hμb : |μ| ≤ 1 / 2 * S.β ^ (-(1 / 2 : ℝ) + ρ₁) * S.ξ ^ ρ₀ := hμ.trans hmu
  exact ⟨hμb, mu_shift_bound S hμb, mu_kernel_bound S hG hD0 hβG,
    normalization_sum_eq_zero Mu φ μ h hMu hφ⟩

end Step

section Eps

open Balaban.SmallField

/-- `ε_k ≤ (L^{-α})^{k-j} ε_j` for `j ≤ k` (iterated gap condition (E)). -/
theorem epsSeq_le_geom (L : ℕ) (α α₀ : ℝ) (hα₀ : 0 ≤ α₀) {j k : ℕ} (hjk : j ≤ k) :
    epsSeq L α α₀ k ≤ ((L : ℝ) ^ (-α)) ^ (k - j) * epsSeq L α α₀ j := by
  have hq : 0 ≤ (L : ℝ) ^ (-α) := Real.rpow_nonneg (Nat.cast_nonneg L) _
  induction k, hjk using Nat.le_induction with
  | base => simp
  | succ k hjk ih =>
    have hg := epsSeq_gapE L α α₀ hα₀ k
    have e : (1 - (1 - (L : ℝ) ^ (-α))) = (L : ℝ) ^ (-α) := by ring
    rw [e] at hg
    calc epsSeq L α α₀ (k + 1) ≤ (L : ℝ) ^ (-α) * epsSeq L α α₀ k := hg
      _ ≤ (L : ℝ) ^ (-α) * (((L : ℝ) ^ (-α)) ^ (k - j) * epsSeq L α α₀ j) :=
          mul_le_mul_of_nonneg_left ih hq
      _ = ((L : ℝ) ^ (-α)) ^ (k + 1 - j) * epsSeq L α α₀ j := by
          rw [show k + 1 - j = (k - j) + 1 by omega, pow_succ]; ring

/-- **(B2)**: `ε_k / ε_j ≤ (L^j η)^α` with `η = L^{-k}`, `j ≤ k` (so `C_ε = 1` in
`F0_of_improved`; the document has `2`). -/
theorem epsSeq_ratio_le (L : ℕ) [NeZero L] (α α₀ : ℝ) (hα₀ : 0 ≤ α₀) {j k : ℕ} (hjk : j ≤ k) :
    epsSeq L α α₀ k ≤ (((L : ℝ) ^ j) * ((L : ℝ) ^ k)⁻¹) ^ α * epsSeq L α α₀ j := by
  have hL : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have e : (((L : ℝ) ^ j) * ((L : ℝ) ^ k)⁻¹) ^ α = ((L : ℝ) ^ (-α)) ^ (k - j) := by
    have h1 : ((L : ℝ) ^ j) * ((L : ℝ) ^ k)⁻¹ = (((L : ℝ) ^ (k - j)))⁻¹ := by
      rw [show k = (k - j) + j by omega, pow_add]
      field_simp
      simp
    rw [h1, Real.inv_rpow (by positivity), ← Real.rpow_natCast, ← Real.rpow_mul hL.le,
      ← Real.rpow_neg_one, ← Real.rpow_mul hL.le, ← Real.rpow_natCast, ← Real.rpow_mul hL.le]
    congr 1; ring
  rw [e]
  exact epsSeq_le_geom L α α₀ hα₀ hjk

theorem one_lt_epsTail (j : ℕ) : 1 < epsTail j := by
  unfold epsTail
  have hpos : 0 < ∑' m : ℕ, if j ≤ m then ((m : ℝ) ^ 2)⁻¹ else 0 := by
    refine (summable_epsTail j).tsum_pos (fun m => by split_ifs <;> positivity) (max j 1) ?_
    have h1 : j ≤ max j 1 := le_max_left _ _
    have h2 : (0 : ℝ) < ((max j 1 : ℕ) : ℝ) := by
      have : 0 < max j 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
      exact_mod_cast this
    simp only [h1, ↓reduceIte]
    positivity
  linarith

/-- **`ε_n > α₀ (L^{-α})^n` strictly** (`ε_n = α₀ (1 + ∑_{m ≥ n} m^{-2}) L^{-nα}`): the landed
`T2_bound` assumes `ε_{k+1} = α₀ ξ_{k+1}^{α}` with equality, which is false for the sequence `ε_j`
of the class (`Consts.eps`); `T2_bound_ge` needs only `≥`, and this theorem provides it. -/
theorem epsSeq_gt_geom (L : ℕ) [NeZero L] (α α₀ : ℝ) (hα₀ : 0 < α₀) (n : ℕ) :
    α₀ * ((L : ℝ) ^ (-α)) ^ n < epsSeq L α α₀ n := by
  have hL : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hq : 0 < ((L : ℝ) ^ (-α)) ^ n := by positivity
  unfold epsSeq
  have := one_lt_epsTail n
  nlinarith [mul_pos hα₀ hq]

/-- **The equality hypothesis of the deleted `T2_bound` is unsatisfiable**: for `ξ_{n} = L^{-n}`
(`StepScale.ξ`) and `α = D/2 - γ`, the class sequence `ε_n = α₀ (1 + ∑_{m ≥ n} m^{-2}) L^{-nα}`
(`Consts.eps`) is never `α₀ ξ^{α}`. -/
theorem T2_bound_hyp_false {D γ ρ₂ : ℝ} (S : StepScale D ρ₂) (L : ℕ) [NeZero L] (n : ℕ)
    {α₀ : ℝ} (hα₀ : 0 < α₀) (hξ : S.ξ = ((L : ℝ) ^ n)⁻¹) :
    epsSeq L (D / 2 - γ) α₀ n ≠ α₀ * S.ξ ^ (D / 2 - γ) := by
  have hL : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have e : S.ξ ^ (D / 2 - γ) = ((L : ℝ) ^ (-(D / 2 - γ))) ^ n := by
    rw [hξ, Real.inv_rpow (by positivity), ← Real.rpow_natCast, ← Real.rpow_mul hL.le,
      ← Real.rpow_neg_one, ← Real.rpow_mul hL.le, ← Real.rpow_natCast, ← Real.rpow_mul hL.le]
    congr 1; ring
  rw [e]
  exact (epsSeq_gt_geom L (D / 2 - γ) α₀ hα₀ n).ne'

/-- `T2_bound_hyp_false` for the sequence `Consts.eps` of the class. -/
theorem T2_bound_hyp_false_eps {D γ ρ₂ : ℝ} (S : StepScale D ρ₂) (d L : ℕ) [NeZero L] (n : ℕ)
    (P : Balaban.SmallField.Def6.Consts) (hα₀ : 0 < P.α₀) (hα : P.alpha d = D / 2 - γ) (hξ : S.ξ = ((L : ℝ) ^ n)⁻¹) :
    P.eps d L n ≠ P.α₀ * S.ξ ^ (D / 2 - γ) := by
  unfold Balaban.SmallField.Def6.Consts.eps
  rw [hα]
  exact T2_bound_hyp_false S L n hα₀ hξ

end Eps

end Balaban.Observables
