/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.WindowDomFacts
public import Balaban.LargeField.R.WindowDeltaRegime
public import Balaban.Fluctuation.ClassOldBirthConsts
public import Balaban.SmallField.LocalSuccessorRadius
public import Balaban.Green.FinalConstsClose

/-!
# The radii of the piece data against the class radii (blocker 4)

For the running tolerances `δ_j = (β_j a)^{-1/2} p₀(β_j)` (`cs.delta = deltaRun …`), the radius
`pieceRadiusWin S cs j` of the piece data of scale `j + 1` satisfies
`(2 K₁ + 2) · pieceRadiusWin ≤ ε_{j+1}` once `λ̂_0` is large (`pieceRadiusWin_regime`): the terms
`3dLδ_j`, `3δ_j`, `3dLδ_{j-1}`, `3δ_{j+1}` are bounded by `deltaRun_le_epsSeq` (for `δ_{j-1}` with the
extra factor `2 L^α` of `epsSeq_le_two_rpow_mul_succ`), and the test radius
`(d+1)δ_{j+1}(2 + (d+1)δ_{j+1})` by the same bound at `j + 1` and `α₀ ≤ 2`.
-/

@[expose] public section

namespace Balaban.LargeField

open Balaban Balaban.SmallField Balaban.Fluctuation Balaban.Green

/-- **`(2 K₁ + 2) · pieceRadiusWin ≤ ε_{j+1}`** in the regime `λ̂_0` large. -/
theorem pieceRadiusWin_regime (S : Setting) [NeZero S.L] (cs : OpConsts) {β ν a ε : ℝ}
    {b nu : ℕ → ℝ} (h : RunningHyp S.d S.L β ν a ε b nu) (hd3 : 3 ≤ S.d) {α γ α₀ : ℝ}
    (hα : 0 ≤ α) (hα₀ : 0 < α₀) (hα₀2 : α₀ ≤ 2) (hγ : 0 < γ)
    (hrel : (S.d : ℝ) - 2 - 2 * α = 2 * γ) {A0 K1 : ℝ} (hA0 : 0 ≤ A0) (hK1 : 0 ≤ K1) (p0 : ℕ)
    (h3 : 3 ≤ lamHat S.d S.L β a 0)
    (hcond : ((2 * K1 + 2) * (3 * (S.d : ℝ) * S.L) * (2 * (S.L : ℝ) ^ α)) *
        (Real.exp 1 * A0 * (p0.factorial : ℝ) / (γ / (2 * ((S.d : ℝ) - 2))) ^ p0) *
        (S.L : ℝ) ^ α ≤ α₀ * Real.exp (lamHat S.d S.L β a 0 / 4))
    (hcs : ∀ j, cs.delta j = deltaRun A0 p0 a b j) (hδnn : ∀ j, 0 ≤ cs.delta j) (j : ℕ) :
    (2 * K1 + 2) * pieceRadiusWin S cs j ≤ epsSeq S.L α α₀ (j + 1) := by
  have hL0 : (0 : ℝ) < S.L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne S.L)
  have hL2 : (2 : ℝ) ≤ S.L := by exact_mod_cast h.hL
  have hD3 : (3 : ℝ) ≤ S.d := by exact_mod_cast hd3
  have hc0 : 0 < 2 * K1 + 2 := by linarith
  set c0 := 2 * K1 + 2 with hc0def
  set C := c0 * (3 * (S.d : ℝ) * S.L) with hCdef
  have hCnn : 0 ≤ C := by positivity
  have hLα : 1 ≤ (S.L : ℝ) ^ α := Real.one_le_rpow (by linarith) hα
  have hLα0 : 0 < (S.L : ℝ) ^ α := by linarith
  have hC'nn : 0 ≤ C * (2 * (S.L : ℝ) ^ α) := by positivity
  have HF : ∀ j, C * (2 * (S.L : ℝ) ^ α) * cs.delta j ≤ epsSeq S.L α α₀ (j + 1) := fun j => by
    rw [hcs j]
    exact deltaRun_le_epsSeq h hd3 hα hα₀ hγ hrel hA0 hC'nn p0 h3 hcond j
  have hC1 : ∀ j, C * cs.delta j ≤ epsSeq S.L α α₀ (j + 1) := fun j => by
    have := HF j
    have h2 : C * cs.delta j ≤ C * (2 * (S.L : ℝ) ^ α) * cs.delta j := by
      have : C * 1 ≤ C * (2 * (S.L : ℝ) ^ α) := mul_le_mul_of_nonneg_left (by linarith) hCnn
      nlinarith [hδnn j]
    linarith
  have hEpos : ∀ j, 0 ≤ epsSeq S.L α α₀ j := fun j => epsSeq_nonneg' S.L α α₀ hα₀.le j
  have hdL : (1 : ℝ) ≤ (S.d : ℝ) * S.L := by nlinarith
  -- the individual bounds, in the form `c0 * term ≤ ε_{j+1}`
  have b1 : c0 * (3 * (S.d : ℝ) * S.L * cs.delta j) ≤ epsSeq S.L α α₀ (j + 1) := by
    have := hC1 j
    calc c0 * (3 * (S.d : ℝ) * S.L * cs.delta j) = C * cs.delta j := by rw [hCdef]; ring
      _ ≤ _ := this
  have b2 : c0 * (3 * cs.delta j) ≤ epsSeq S.L α α₀ (j + 1) := by
    refine le_trans ?_ b1
    have := hδnn j
    have : 3 * cs.delta j ≤ 3 * (S.d : ℝ) * S.L * cs.delta j := by nlinarith
    exact mul_le_mul_of_nonneg_left this hc0.le
  have b3 : c0 * (3 * (S.d : ℝ) * S.L * cs.delta (j - 1)) ≤ epsSeq S.L α α₀ (j + 1) := by
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · simpa using b1
    · obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
      have h1 := HF j'
      have h2 := GsSpec.epsSeq_le_two_rpow_mul_succ S.L α α₀ hα₀.le (j' + 1)
      have h4 : (2 * (S.L : ℝ) ^ α) * (C * cs.delta j') ≤
          (2 * (S.L : ℝ) ^ α) * epsSeq S.L α α₀ (j' + 1 + 1) := by nlinarith
      have h5 := le_of_mul_le_mul_left h4 (by positivity)
      calc c0 * (3 * (S.d : ℝ) * S.L * cs.delta (j' + 1 - 1)) = C * cs.delta j' := by
            rw [hCdef]; simp only [Nat.add_sub_cancel]; ring
        _ ≤ _ := h5
  have b4 : c0 * (3 * cs.delta (j + 1)) ≤ epsSeq S.L α α₀ (j + 1) := by
    have := hC1 (j + 1)
    have h6 := epsSeq_anti S.L α α₀ hα₀.le hα (Nat.le_succ (j + 1))
    have := hδnn (j + 1)
    have : 3 * cs.delta (j + 1) ≤ 3 * (S.d : ℝ) * S.L * cs.delta (j + 1) := by nlinarith
    nlinarith [hC1 (j + 1)]
  have b5 : c0 * ((S.d + 1) * cs.delta (j + 1) * (2 + (S.d + 1) * cs.delta (j + 1))) ≤
      epsSeq S.L α α₀ (j + 1) := by
    have hδ := hδnn (j + 1)
    have h6 := epsSeq_anti S.L α α₀ hα₀.le hα (Nat.le_succ (j + 1))
    have h7 := epsSeq_le_three_alpha S.L hα₀ hα (j + 1 + 1)
    have h8 := hC1 (j + 1)
    -- `(d+1) δ ≤ 1`
    have hx : ((S.d : ℝ) + 1) * cs.delta (j + 1) ≤ 1 := by
      have hCge : 6 * ((S.d : ℝ) + 1) ≤ C := by
        rw [hCdef]
        have : (2 : ℝ) ≤ c0 := by rw [hc0def]; linarith
        nlinarith
      have : 6 * (((S.d : ℝ) + 1) * cs.delta (j + 1)) ≤ 3 * α₀ := by nlinarith
      linarith
    have hdle : ((S.d : ℝ) + 1) ≤ (S.d : ℝ) * S.L := by nlinarith
    calc c0 * (((S.d : ℝ) + 1) * cs.delta (j + 1) * (2 + ((S.d : ℝ) + 1) * cs.delta (j + 1)))
        ≤ c0 * (((S.d : ℝ) + 1) * cs.delta (j + 1) * 3) := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg (by positivity) hδ)) hc0.le
      _ ≤ c0 * (3 * (S.d : ℝ) * S.L * cs.delta (j + 1)) := by
          refine mul_le_mul_of_nonneg_left ?_ hc0.le
          calc ((S.d : ℝ) + 1) * cs.delta (j + 1) * 3 = (3 * cs.delta (j + 1)) * ((S.d : ℝ) + 1) := by ring
            _ ≤ (3 * cs.delta (j + 1)) * ((S.d : ℝ) * S.L) :=
                mul_le_mul_of_nonneg_left hdle (by linarith)
            _ = 3 * (S.d : ℝ) * S.L * cs.delta (j + 1) := by ring
      _ = C * cs.delta (j + 1) := by rw [hCdef]; ring
      _ ≤ _ := by linarith
  unfold pieceRadiusWin
  rw [← le_div_iff₀' hc0]
  refine max_le (max_le ?_ ?_) (max_le ?_ (max_le ?_ ?_))
  · exact (le_div_iff₀' hc0).2 b1
  · exact (le_div_iff₀' hc0).2 b2
  · exact (le_div_iff₀' hc0).2 b3
  · exact (le_div_iff₀' hc0).2 b4
  · exact (le_div_iff₀' hc0).2 b5

end Balaban.LargeField
