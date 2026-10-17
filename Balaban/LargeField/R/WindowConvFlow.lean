/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.PieceChain
public import Balaban.Flow.RunningCoefficients

/-!
# Running coefficients of a converted window piece

The identification of the operator constants with the real RG flow is stated explicitly.
The recursion hypotheses are the real forms of P4 (5.28). No regional source estimate is
included in those hypotheses.
-/

@[expose] public section

namespace Balaban.LargeField.ActionConv

open Balaban.LargeField Balaban.Flow

theorem betaCanon_eq_of_flow (cs : OpConsts) (d L : ℕ) [NeZero L]
    (β : ℝ) (g : ℕ → ℝ)
    (hcs : ∀ n, cs.beta n = β * (L : ℝ) ^ ((d - 2) * n) * g n) (n : ℕ) :
    betaCanon d L (cs.beta n) n 0 = β * g n := by
  have hL : (L : ℝ) ≠ 0 := by exact_mod_cast (NeZero.ne L)
  unfold betaCanon
  rw [hcs]
  simp only [Nat.sub_zero]
  rw [Nat.mul_comm (d - 2) n]
  field_simp

/-- The fine-coupling and fine-mass increments of P6 (2.31), conditional on the
identification of the operator constants with a real RG solution. -/
theorem flow_increment_eq_of_ident (cs : OpConsts) (d L : ℕ) [NeZero L]
    (β ν : ℝ) (g δ : ℕ → ℝ) (ξ : ℕ → Fin 3 → ℝ)
    (hβ : ∀ n, cs.beta n = β * (L : ℝ) ^ ((d - 2) * n) * g n)
    (hμ : ∀ n, cs.muAct n = ν * δ n)
    (hg : ∀ n, g n = g (n + 1) * (1 + ξ n 2))
    (hδ : ∀ n, δ n * (1 + ξ n 2) = δ (n + 1) * (1 + ξ n 1))
    (hμne : ∀ n, cs.muAct n ≠ 0) (n : ℕ) :
    betaCanon d L (cs.beta n) n 0 -
        betaCanon d L (cs.beta (n + 1)) (n + 1) 0 =
          betaCanon d L (cs.beta (n + 1)) (n + 1) 0 * ξ n 2 ∧
      (betaCanon d L (cs.beta n) n 0 * cs.muAct n -
          betaCanon d L (cs.beta (n + 1)) (n + 1) 0 * cs.muAct (n + 1)) /
          cs.muAct (n + 1) =
        betaCanon d L (cs.beta (n + 1)) (n + 1) 0 * ξ n 1 := by
  have hbn := betaCanon_eq_of_flow cs d L β g hβ n
  have hbs := betaCanon_eq_of_flow cs d L β g hβ (n + 1)
  constructor
  · rw [hbn, hbs, hg n]
    ring
  · have hprod : (β * g n) * (ν * δ n) =
        (β * g (n + 1)) * (ν * δ (n + 1)) * (1 + ξ n 1) := by
      rw [hg n]
      linear_combination β * ν * g (n + 1) * hδ n
    rw [hbn, hbs, hμ n, hμ (n + 1), hprod]
    have hne : ν * δ (n + 1) ≠ 0 := by simpa [hμ] using hμne (n + 1)
    obtain ⟨hνne, hδne⟩ := mul_ne_zero_iff.mp hne
    field_simp [hνne, hδne]
    ring

/-- Quantitative form of both fine-unit increments. The RG step bound is an explicit
premise; the resulting constant is exactly `Cξ * exp η`. -/
theorem flow_increment_abs_le_of_ident (cs : OpConsts) (d L : ℕ) [NeZero L]
    (β ν η Cξ q : ℝ) (g δ : ℕ → ℝ) (ξ : ℕ → Fin 3 → ℝ)
    (hβpos : 0 < β) (hCξ : 0 ≤ Cξ) (hq : 0 ≤ q)
    (hβ : ∀ n, cs.beta n = β * (L : ℝ) ^ ((d - 2) * n) * g n)
    (hμ : ∀ n, cs.muAct n = ν * δ n)
    (hg : ∀ n, g n = g (n + 1) * (1 + ξ n 2))
    (hδ : ∀ n, δ n * (1 + ξ n 2) = δ (n + 1) * (1 + ξ n 1))
    (hμne : ∀ n, cs.muAct n ≠ 0)
    (hgenv : ∀ n, 0 ≤ g n ∧ g n ≤ Real.exp η)
    (hξ : ∀ n c, |ξ n c| ≤ Cξ * β⁻¹ * q ^ (n + 1)) (n : ℕ) :
    |betaCanon d L (cs.beta n) n 0 -
      betaCanon d L (cs.beta (n + 1)) (n + 1) 0| ≤
        Cξ * Real.exp η * q ^ (n + 1) ∧
    |(betaCanon d L (cs.beta n) n 0 * cs.muAct n -
      betaCanon d L (cs.beta (n + 1)) (n + 1) 0 * cs.muAct (n + 1)) /
      cs.muAct (n + 1)| ≤ Cξ * Real.exp η * q ^ (n + 1) := by
  have hinc := flow_increment_eq_of_ident cs d L β ν g δ ξ hβ hμ hg hδ hμne n
  have hcanon := betaCanon_eq_of_flow cs d L β g hβ (n + 1)
  have hbound (c : Fin 3) : |β * g (n + 1) * ξ n c| ≤
      Cξ * Real.exp η * q ^ (n + 1) := by
    have hgp := (hgenv (n + 1)).1
    have hgle := (hgenv (n + 1)).2
    have hfac : 0 ≤ Cξ * q ^ (n + 1) := mul_nonneg hCξ (pow_nonneg hq _)
    calc
      |β * g (n + 1) * ξ n c| = (β * g (n + 1)) * |ξ n c| := by
        rw [abs_mul, abs_of_nonneg (mul_nonneg hβpos.le hgp)]
      _ ≤ (β * g (n + 1)) * (Cξ * β⁻¹ * q ^ (n + 1)) :=
        mul_le_mul_of_nonneg_left (hξ n c) (mul_nonneg hβpos.le hgp)
      _ = g (n + 1) * (Cξ * q ^ (n + 1)) := by
        field_simp
      _ ≤ Real.exp η * (Cξ * q ^ (n + 1)) :=
        mul_le_mul_of_nonneg_right hgle hfac
      _ = _ := by ring
  constructor
  · rw [hinc.1, hcanon]
    exact hbound 2
  · rw [hinc.2, hcanon]
    exact hbound 1

/-- The dimensionless mass recursion in a division-free form. -/
theorem mass_increment_mul_eq_of_ident (cs : OpConsts) (ν : ℝ)
    (δ : ℕ → ℝ) (ξ : ℕ → Fin 3 → ℝ)
    (hμ : ∀ n, cs.muAct n = ν * δ n)
    (hδ : ∀ n, δ n * (1 + ξ n 2) = δ (n + 1) * (1 + ξ n 1))
    (n : ℕ) :
    (cs.muAct (n + 1) - cs.muAct n) * (1 + ξ n 1) =
      cs.muAct n * (ξ n 2 - ξ n 1) := by
  rw [hμ n, hμ (n + 1)]
  linear_combination -ν * hδ n

/-- The same recursion as a relative mass increment when its RG denominator is nonzero. -/
theorem mass_increment_eq_of_ident (cs : OpConsts) (ν : ℝ)
    (δ : ℕ → ℝ) (ξ : ℕ → Fin 3 → ℝ)
    (hμ : ∀ n, cs.muAct n = ν * δ n)
    (hδ : ∀ n, δ n * (1 + ξ n 2) = δ (n + 1) * (1 + ξ n 1))
    (n : ℕ) (hden : 1 + ξ n 1 ≠ 0) :
    cs.muAct (n + 1) - cs.muAct n =
      cs.muAct n * (ξ n 2 - ξ n 1) / (1 + ξ n 1) := by
  apply (eq_div_iff hden).2
  exact mass_increment_mul_eq_of_ident cs ν δ ξ hμ hδ n

/-- The RG envelope gives the exact scale-coupling witness expected by the
window theorem; its bounds must hold at every natural-number index. -/
theorem window_hflow_of_ident (cs : OpConsts) (d L : ℕ) (β η : ℝ)
    (g : ℕ → ℝ) (hβpos : 0 < β)
    (hβ : ∀ n, cs.beta n = β * (L : ℝ) ^ ((d - 2) * n) * g n)
    (hg : ∀ n, Real.exp (-η) ≤ g n ∧ g n ≤ Real.exp η) :
    ∀ (j k : ℕ), ∃ B : ℝ, 0 < B ∧ ∃ gg : ℕ → ℝ,
      (∀ m, Real.exp (-η) ≤ gg m ∧ gg m ≤ Real.exp η) ∧
      ∀ m, j + 1 ≤ m → m ≤ k →
        cs.beta m = B * (L : ℝ) ^ ((d - 2) * m) * gg m := by
  intro j k
  exact ⟨β, hβpos, g, hg, fun m _ _ => hβ m⟩

end Balaban.LargeField.ActionConv
