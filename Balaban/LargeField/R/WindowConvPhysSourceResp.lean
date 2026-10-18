/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.CoeffResponseHyp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The same-datum response to a joint change of coefficient and mass (P7 p. 500 (2.10)–(2.12))

One conversion step of the window changes the block coefficient and the mass of the Euler–Lagrange
system together.  Two backgrounds `φ⁰`, `φ¹` on one datum `D`, at `(a₀, ν₀)` and `(a₁, ν₁)`,
differ by the perturbed system at `(a₀, ν₀)` with the source
`f₁ = Q*(a₁ - a₀)(Ψ - Q φ¹) - (ν₁ - ν₀)(φ¹ - h)`; the weighted Proposition 5.1 gives the
weight-one bound `K_w S` of the response from `ℓ² |f₁| ≤ S`.

* `liftOp_dirichlet_coeff_mass`: the joint shift of the Dirichlet operator;
* `jointSource_perturbed`: the difference of the two backgrounds solves the perturbed system;
* `jointChange_sameData_response`: the response.
-/

@[expose] public section

namespace Balaban.LargeField.ActionConv

open Balaban.Multiscale Balaban.Background Balaban.Fluctuation Balaban.Localization Finset Matrix

section Source

variable {d L N₀ K N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ} {G : GeneratingSet d L N₀ K ϱ}

/-- **Joint shift of the Dirichlet operator** at the coefficients `a₁`, `a₀` and the masses
`ν₁`, `ν₀`. -/
theorem liftOp_dirichlet_coeff_mass (a₁ a₀ : ℕ → ℝ) (ν₁ ν₀ : ℝ) (α : G.Ω 1 → ℂ)
    (w : G.Ω 1 × Fin N → ℂ) (p : G.Ω 1 × Fin N) :
    (liftOp N (dirichletOperator G a₁ ν₁ α) *ᵥ w) p =
      (liftOp N (dirichletOperator G a₀ ν₀ α) *ᵥ w) p +
        qStar G (a₁ - a₀) (blockAvg G w) p + ((ν₁ - ν₀ : ℝ) : ℂ) * w p := by
  obtain ⟨x, i⟩ := p
  rw [liftOp_mulVec, liftOp_mulVec, dirichlet_apply, dirichlet_apply]
  simp only [qStar, blockAvg, blockTerm, Pi.sub_apply, svec]
  push_cast
  ring

/-- **The joint source**: two Euler–Lagrange systems on one datum, at `(a₀, ν₀)` and `(a₁, ν₁)`,
give the perturbed system at `(a₀, ν₀)` with base `φ̄⁰`, zero data change and the source
`Q*(a₁ - a₀)(Ψ - Q φ¹) - (ν₁ - ν₀)(φ¹ - h)`. -/
theorem jointSource_perturbed (a₀ a₁ : ℕ → ℝ) (ν₀ ν₁ : ℝ) (D : BgData G N)
    {φ0 φ1 : G.Ω 1 × Fin N → ℂ} {α0 α1 : G.Ω 1 → ℂ}
    (h0 : IsEL G a₀ ν₀ D φ0 α0) (h1 : IsEL G a₁ ν₁ D φ1 α1) :
    IsPerturbed G a₀ ν₀ α0 (barField G D.Ψ φ0)
      (fun p => qStar G (a₁ - a₀) (fun y j => D.Ψ y j - blockAvg G φ1 y j) p -
        ((ν₁ - ν₀ : ℝ) : ℂ) * (φ1 p - D.h p.1 p.2))
      (φ1 - φ0) (α1 - α0) := by
  have bar : ∀ (x : G.Ω 1) i, barField G D.Ψ φ0 x i = φ0 (x, i) := by
    intro x i; simp [barField, x.2]
  refine ⟨?_, ?_⟩
  · funext p
    have e0 := congrFun h0.1 p
    have e1 := congrFun h1.1 p
    rw [liftOp_dirichlet_coeff_mass a₁ a₀ ν₁ ν₀] at e1
    have ha := liftOp_dirichlet_add (G := G) (N := N) a₀ ν₀ α0 (α1 - α0) φ1 p
    rw [add_sub_cancel] at ha
    rw [ha] at e1
    have t := qStar_coeff_sub (G := G) a₁ a₀ D.Ψ p
    have u := qStar_sub_apply (G := G) a₁ a₀ D.Ψ (blockAvg G φ1) p
    simp only [source, Pi.sub_apply] at e0 e1
    simp only [Pi.add_apply, Pi.sub_apply, Matrix.mulVec_sub, bar]
    push_cast at e0 e1 ⊢
    linear_combination e1 - e0 + t - u
  · intro x
    have := h1.2 x
    simp only [bar, Pi.sub_apply]
    simpa using this

end Source

section Response

variable {d L N : ℕ} [NeZero L] {N₁ m₁ K : ℕ} [NeZero N₁] {ϱ : ℝ} {Kw δw : ℝ}

/-- **Joint response, conditional form**: given the weighted Proposition 5.1 predicate,
`Prop51Hyp` for the joint source and `Dec2.OpSetting`, the response is bounded with weight one by
`K_w S`. -/
theorem jointChange_sameData_response_of_weighted
    (hW : WeightedProp51S d L N Kw δw)
    {G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} (a₀ a₁ : ℕ → ℝ) (ν₀ ν₁ S δ₀ δ₁ : ℝ)
    (D : BgData G N) {φ0 φ1 : G.Ω 1 × Fin N → ℂ} {α0 α1 : G.Ω 1 → ℂ}
    (h0 : IsEL G a₀ ν₀ D φ0 α0) (h1 : IsEL G a₁ ν₁ D φ1 α1)
    (hP : Prop51Hyp G a₀ ν₀ α0 (barField G D.Ψ φ0)
      (0 : Torus d ((N₁ * L ^ m₁) * L ^ K) → Fin N → ℂ)
      (fun p => qStar G (a₁ - a₀) (fun y j => D.Ψ y j - blockAvg G φ1 y j) p -
        ((ν₁ - ν₀ : ℝ) : ℂ) * (φ1 p - D.h p.1 p.2)) δ₀ δ₁)
    (hO : Dec2.OpSetting G a₀ ν₀) (hδ₀ : δ₀ ≤ δw) (hδ₁ : δ₁ ≤ δw)
    (hS0 : 0 ≤ S)
    (hS : ∀ (x : G.Ω 1) (i : Fin N), G.spacing (x : Torus d ((N₁ * L ^ m₁) * L ^ K)) ^ 2 *
      ‖qStar G (a₁ - a₀) (fun y j => D.Ψ y j - blockAvg G φ1 y j) (x, i) -
        ((ν₁ - ν₀ : ℝ) : ℂ) * (φ1 (x, i) - D.h x i)‖ ≤ S)
    (hα : Small G (α1 - α0) (c6 d L N)) :
    SmallW G (fun _ => 1) (α1 - α0) (Kw * S) ∧
      SupBoundsW G (fun _ => 1) (φ1 - φ0) (Kw * S) := by
  have hg : ∀ x : G.Ω 1, gdef G (barField G D.Ψ φ0) x = 0 := by
    intro x
    have := h0.2 x
    simp only [gdef, barField, x.2, dite_true]
    rw [this]; ring
  have hd0 : 0 < d := by have := hP.green.hd; omega
  exact hW G a₀ ν₀ α0 (barField G D.Ψ φ0) 0 _ δ₀ δ₁ hP hO hg hδ₀ hδ₁
    (fun _ => 1) (IsWeight.one G (gammaW_nonneg hd0)) S hS0 (fun x i => by
      rw [pertSource_zero]; simpa using hS x i)
    (φ1 - φ0) (α1 - α0) (by rw [pertSource_zero]; exact jointSource_perturbed a₀ a₁ ν₀ ν₁ D h0 h1)
    hα

/-- **The joint same-datum response, premises only.**  There are `K_w, δ_w > 0` depending only on
`(d, L, N)` such that for two Euler–Lagrange backgrounds of one datum at `(a₀, ν₀)` and
`(a₁, ν₁)` with the background bounds, and a bound `S` of the weighted joint source
`ℓ² |Q*(a₁ - a₀)(Ψ - Q φ¹) - (ν₁ - ν₀)(φ¹ - h)| ≤ S`, the multiplier difference and the field
difference are bounded with weight one by `K_w S`. -/
theorem jointChange_sameData_response (N : ℕ) (hd : 3 ≤ d) (hL : 3 ≤ L) :
    ∃ Kw δw : ℝ, 0 < Kw ∧ 0 < δw ∧
      ∀ {N₁ m₁ K : ℕ} [NeZero N₁] {ϱ : ℝ} {G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ}
        (a₀ a₁ : ℕ → ℝ) (ν₀ ν₁ S δ₀ : ℝ) (D : BgData G N)
        {φ0 φ1 : G.Ω 1 × Fin N → ℂ} {α0 α1 : G.Ω 1 → ℂ},
        IsEL G a₀ ν₀ D φ0 α0 → IsEL G a₁ ν₁ D φ1 α1 →
        BgBounds G D φ0 α0 δ₀ → BgBounds G D φ1 α1 δ₀ →
        GreenSetting G a₀ ν₀ → Dec2.OpSetting G a₀ ν₀ →
        0 ≤ δ₀ → δ₀ ≤ min (deltaStar d L N) δw → 2 * δ₀ ≤ c6 d L N →
        0 ≤ S → S ≤ min (deltaStar d L N) δw →
        (∀ (x : G.Ω 1) (i : Fin N), G.spacing (x : CTorus d L N₁ m₁ K) ^ 2 *
          ‖qStar G (a₁ - a₀) (fun y j => D.Ψ y j - blockAvg G φ1 y j) (x, i) -
            ((ν₁ - ν₀ : ℝ) : ℂ) * (φ1 (x, i) - D.h x i)‖ ≤ S) →
        (∀ x : G.Ω 1, vn (fun i => φ0 (x, i)) ≤ 3 / 2) →
        (SmallW G (fun _ => 1) (α1 - α0) (Kw * S) ∧
          SupBoundsW G (fun _ => 1) (φ1 - φ0) (Kw * S)) := by
  obtain ⟨Kw, δw, hK, hδ, hW⟩ := weightedProp51S_exists N hd hL
  refine ⟨Kw, δw, hK, hδ, ?_⟩
  intro N₁ m₁ K _ ϱ G a₀ a₁ ν₀ ν₁ S δ₀ D φ0 φ1 α0 α1 h0 h1 b0 b1 hG hO hδ₀ hδs h2 hS0 hSB hS hφ
  have hP : Prop51Hyp G a₀ ν₀ α0 (barField G D.Ψ φ0)
      (0 : Torus d ((N₁ * L ^ m₁) * L ^ K) → Fin N → ℂ)
      (fun p => qStar G (a₁ - a₀) (fun y j => D.Ψ y j - blockAvg G φ1 y j) p -
        ((ν₁ - ν₀ : ℝ) : ℂ) * (φ1 p - D.h p.1 p.2)) δ₀ S :=
    prop51Hyp_of_zeroChange a₀ ν₀ δ₀ S D hG h0 b0 hφ hδ₀ hS0
      (hδs.trans (min_le_left _ _)) (hSB.trans (min_le_left _ _)) (fun x i => hS x i)
  have hα : Small G (α1 - α0) (c6 d L N) := fun x => by
    have := massMultiplier_small b0 b1 x
    linarith
  exact jointChange_sameData_response_of_weighted hW a₀ a₁ ν₀ ν₁ S δ₀ S D h0 h1 hP hO
    (hδs.trans (min_le_right _ _)) (hSB.trans (min_le_right _ _)) hS0 hS hα

end Response

end Balaban.LargeField.ActionConv
