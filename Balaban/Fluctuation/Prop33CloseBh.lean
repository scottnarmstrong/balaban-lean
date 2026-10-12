/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.Prop33CloseNu
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The bound `‖h̃‖ ≤ Bh` on `Ξ^c` for `ν > 0` (W136b)

For a positive mass `ν`, the data domain bounds the external field: `ν L^{2K} |∑ h² - 1| < δ²`
(clause (R4)) and `ν L^{2n} |h'| < δ² / ε` (clause (C3)).  Hence `‖h̃‖ ≤ 1 + 2 / ν` on `Ξ^c_K(1, ε')`
whenever `C₁ ε' ≤ 1`.  This discharges the premise `hBh` of `nupart_locInt_bound` (the source
premise `|φ^0_{k+1} - h| ≤ 2` of the proof of Proposition 3.3) for `ν > 0`.
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation Finset

section Bh

variable {d L N₁ m₁ K N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
variable {Gp : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {a₁ ν eps : ℝ}

/-- **`hBh` from the data domain**: for `ν > 0`, `‖h̃‖ ≤ 1 + 2/ν` on `Ξ^c_K(1, ε')`. -/
theorem hBh_of_xi (H : BgHyp d L K ϱ (compWeight L a₁) ν) (hν : 0 < ν) {eps : ℝ}
    (hsmall : (4 * d + 6) * ((2 * d + 1) * eps) ≤ 1) (heps : 0 < eps) (hxi : xiC1 d * eps ≤ 1) :
    ∀ D : BgData Gp N, XiCData Gp (compWeight L a₁) ν K 1 eps D →
      ∀ x i, ‖D.h x i‖ ≤ 1 + 2 / ν := by
  intro D hD x i
  have hc1 := one_le_xiC1 d
  have hδ0 : 0 < xiC1 d * eps := by positivity
  obtain ⟨Ψ, h, Ψ', h', hP, hΨ, hh⟩ := xiCData_inDomainC H hsmall hD
  by_cases hx : x ∈ Gp.Ω 1
  swap
  · rw [D.h_zero x hx]; simp; positivity
  have hL1 : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  set δ := xiC1 d * eps with hδ
  -- the complex part
  have h3 := hP.c3a x hx
  have e : δ ^ 2 / δ = δ := by field_simp
  rw [e] at h3
  have hpow : (1 : ℝ) ≤ ((L : ℝ) ^ Gp.layerIndex x) ^ 2 :=
    one_le_pow₀ (one_le_pow₀ hL1)
  have hvn : vn (h' x) ≤ 1 / ν := by
    have hv0 := vn_nonneg (h' x)
    rw [le_div_iff₀ hν]
    nlinarith [mul_le_mul_of_nonneg_right hpow (mul_nonneg hν.le hv0)]
  -- the real part
  have h4 := hP.r4
  have hpowK : (1 : ℝ) ≤ ((L : ℝ) ^ K) ^ 2 := one_le_pow₀ (one_le_pow₀ hL1)
  have hS : ∑ j, h j ^ 2 ≤ 1 + 1 / ν := by
    have habs := le_abs_self (∑ j, h j ^ 2 - 1)
    have h5 : ν * ((L : ℝ) ^ K) ^ 2 * |∑ j, h j ^ 2 - 1| < δ ^ 2 := h4
    have h6 : ν * |∑ j, h j ^ 2 - 1| ≤ 1 := by
      nlinarith [abs_nonneg (∑ j, h j ^ 2 - 1), mul_nonneg hν.le (abs_nonneg (∑ j, h j ^ 2 - 1))]
    have h7 : ∑ j, h j ^ 2 - 1 ≤ 1 / ν := by
      rw [le_div_iff₀ hν]; nlinarith
    linarith
  have hhi : |h i| ≤ 1 + 1 / ν := by
    have hs1 : h i ^ 2 ≤ ∑ j, h j ^ 2 :=
      Finset.single_le_sum (f := fun j => h j ^ 2) (fun j _ => sq_nonneg _) (Finset.mem_univ i)
    have hpos : 0 ≤ 1 / ν := by positivity
    by_contra hcon
    push Not at hcon
    nlinarith [abs_nonneg (h i), sq_abs (h i)]
  rw [hh x hx i]
  calc ‖(h i : ℂ) + h' x i‖ ≤ ‖(h i : ℂ)‖ + ‖h' x i‖ := norm_add_le _ _
    _ ≤ (1 + 1 / ν) + 1 / ν := by
        refine add_le_add ?_ ((norm_le_vn _ i).trans hvn)
        simpa using hhi
    _ = 1 + 2 / ν := by ring

end Bh

end Balaban.Localization
