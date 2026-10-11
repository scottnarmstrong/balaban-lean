/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Green.GeometricResolvent
public import Balaban.Green.Summation

/-!
# G-4(b): the domain difference of Green's functions

For `Λ' ⊆ Λ` and `x₂ ∈ Λ'` (and any `x₁`; both vanish off `Λ` otherwise), with `D_i = setDist (Λ \ Λ') x_i`,
`‖G_Λ(x₁,x₂) - G_{Λ'}(x₁,x₂)‖ ≤ 4 c₀ κ'² (γ₀+t)⁻² e^{-(μ₁/2)(D₁+D₂)}`, where
`μ₁ = min (ctRate c₀ δ₀ γ₀ κ) δ₀` and `κ'` bounds the ball sums `∑_y e^{-(μ₁/2) dist x y}`
(`Balaban.Green.domain_difference`).  Proof: the geometric resolvent identity
(`greenFn_resolvent_identity`), the Combes–Thomas bound for both restrictions and the summation
Lemma 4.10 (`sum_tail_sub_le`).
-/

@[expose] public section

open Matrix Finset

namespace Balaban.Green

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [PseudoMetricSpace ι]

/-- The Combes–Thomas bound for `greenFn` (valid for all `x y : ι`; zero off `Λ`). -/
theorem norm_greenFn_le {A : Matrix ι ι ℂ} {c₀ δ₀ γ₀ κ : ℝ} (hc : 0 ≤ c₀) (hδ : 0 < δ₀)
    (hγ : 0 < γ₀) (hκ : 0 ≤ κ)
    (hA : ∀ x y, ‖A x y‖ ≤ c₀ * Real.exp (-δ₀ * dist x y))
    (hK : ∀ x : ι, ∑ y, Real.exp (-(δ₀ / 4) * dist x y) ≤ κ)
    (hcoer : IsCoercive A γ₀) (Λ : Finset ι) {t : ℝ} (ht : 0 ≤ t) (x y : ι) :
    ‖greenFn A (t : ℂ) Λ x y‖ ≤
      2 * (γ₀ + t)⁻¹ * Real.exp (-(ctRate c₀ δ₀ γ₀ κ) * dist x y) := by
  unfold greenFn
  split_ifs with h
  · exact (combesThomas_restrict hc hδ hγ hκ hA hK hcoer Λ ht).2 ⟨x, h.1⟩ ⟨y, h.2⟩
  · rw [norm_zero]
    have : 0 < γ₀ + t := by linarith
    positivity

/-- **G-4(b)**: domain difference of Green's functions. -/
theorem domain_difference {A : Matrix ι ι ℂ} {c₀ δ₀ γ₀ κ κ' : ℝ} (hc : 0 ≤ c₀) (hδ : 0 < δ₀)
    (hγ : 0 < γ₀) (hκ : 0 ≤ κ) (hκ' : 0 ≤ κ')
    (hA : ∀ x y, ‖A x y‖ ≤ c₀ * Real.exp (-δ₀ * dist x y))
    (hK : ∀ x : ι, ∑ y, Real.exp (-(δ₀ / 4) * dist x y) ≤ κ)
    (hK' : ∀ x : ι, ∑ y, Real.exp (-(min (ctRate c₀ δ₀ γ₀ κ) δ₀ / 2) * dist x y) ≤ κ')
    (hcoer : IsCoercive A γ₀) {Λ' Λ : Finset ι} (hΛ : Λ' ⊆ Λ) {t : ℝ} (ht : 0 ≤ t)
    {x₁ x₂ : ι} (hx₂ : x₂ ∈ Λ') :
    ‖greenFn A (t : ℂ) Λ x₁ x₂ - greenFn A (t : ℂ) Λ' x₁ x₂‖ ≤
      4 * c₀ * κ' * κ' / (γ₀ + t) ^ 2 *
        Real.exp (-(min (ctRate c₀ δ₀ γ₀ κ) δ₀ / 2) *
          (setDist (↑(Λ \ Λ') : Set ι) x₁ + setDist (↑(Λ \ Λ') : Set ι) x₂)) := by
  set ρ := ctRate c₀ δ₀ γ₀ κ with hρ
  have hρ0 : 0 < ρ := ctRate_pos hc hδ hγ hκ
  set m := min ρ δ₀ with hm
  have hm0 : 0 < m := lt_min hρ0 hδ
  have hU := (combesThomas_restrict hc hδ hγ hκ hA hK hcoer Λ ht).1
  have hU' := (combesThomas_restrict hc hδ hγ hκ hA hK hcoer Λ' ht).1
  have hid := greenFn_resolvent_identity hΛ hU' hU x₁ hx₂
  -- hid : G_Λ' x₁ x₂ = G_Λ x₁ x₂ + ∑ ...
  have hγt : 0 < γ₀ + t := by linarith
  have hdiff : greenFn A (t : ℂ) Λ x₁ x₂ - greenFn A (t : ℂ) Λ' x₁ x₂ =
      -∑ u ∈ Λ \ Λ', ∑ z ∈ Λ', greenFn A (t : ℂ) Λ x₁ u * A u z * greenFn A (t : ℂ) Λ' z x₂ := by
    rw [hid]; ring
  rw [hdiff, norm_neg]
  refine (norm_sum_le _ _).trans ?_
  have hterm : ∀ u ∈ Λ \ Λ', ‖∑ z ∈ Λ', greenFn A (t : ℂ) Λ x₁ u * A u z *
        greenFn A (t : ℂ) Λ' z x₂‖ ≤
      ∑ z ∈ Λ', 4 * c₀ / (γ₀ + t) ^ 2 * (Real.exp (-ρ * dist x₁ u) *
        Real.exp (-δ₀ * dist u z) * Real.exp (-ρ * dist z x₂)) := by
    intro u _
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun z _ => ?_)
    rw [norm_mul, norm_mul]
    have g1 := norm_greenFn_le hc hδ hγ hκ hA hK hcoer Λ ht x₁ u
    have g2 := norm_greenFn_le hc hδ hγ hκ hA hK hcoer Λ' ht z x₂
    have a1 := hA u z
    calc _ ≤ (2 * (γ₀ + t)⁻¹ * Real.exp (-ρ * dist x₁ u)) *
          (c₀ * Real.exp (-δ₀ * dist u z)) * (2 * (γ₀ + t)⁻¹ * Real.exp (-ρ * dist z x₂)) := by
          gcongr
      _ = _ := by field_simp; ring
  refine (Finset.sum_le_sum hterm).trans ?_
  have hsum := sum_tail_sub_le (μ := ρ) (δ := δ₀) (m := m) (κ₁ := κ') hm0 (min_le_left _ _)
    (min_le_right _ _) hκ' hK' (Λ \ Λ') Λ' (D₁ := setDist (↑(Λ \ Λ') : Set ι) x₁)
    (D₂ := setDist (↑(Λ \ Λ') : Set ι) x₂) (x₁ := x₁) (x₂ := x₂)
    (fun z hz => setDist_le_dist (by exact_mod_cast hz))
    (fun z hz => setDist_le_dist (by exact_mod_cast hz))
  simp only [← Finset.mul_sum] at *
  calc _ ≤ 4 * c₀ / (γ₀ + t) ^ 2 * (κ' * κ' * Real.exp (-(m / 2) *
        (setDist (↑(Λ \ Λ') : Set ι) x₁ + setDist (↑(Λ \ Λ') : Set ι) x₂))) := by
        gcongr
    _ = _ := by ring

end Balaban.Green
