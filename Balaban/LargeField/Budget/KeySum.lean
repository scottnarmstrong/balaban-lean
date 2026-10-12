module

public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The numerical sum of Lemma II.5.15

For a finite set `F` of `π_k`-cubes over a component `Z'` of `Z^pre_{k+1}` (`|F| = L^d |Z'|_#`),
the sum over the subsets `S ⊆ F` (the cubes of `Z_k`) of
`e^{-n₁ - (5/4) n₂} 2^{4 n₂ / L^d}`, with `n₁ = |S|`, `n₂ = |F| - |S|`, is
`∏_{□ ∈ F} (e^{-1} + e^{-(5/4 - 4 L^{-d} log 2)}) ≤ 1` for `L^d ≥ 8`.
-/

@[expose] public section

namespace Balaban.LargeField

theorem exp_neg_add_le_one {a : ℝ} (ha : a ≤ 7 / 20) :
    Real.exp (-1) + Real.exp (-(5 / 4 - a)) ≤ 1 := by
  have h1 : (2 : ℝ) ≤ Real.exp 1 := by
    have := Real.add_one_le_exp (1 : ℝ); linarith
  have h2 : (2.3 : ℝ) ≤ Real.exp (9 / 10) := by
    have := Real.quadratic_le_exp_of_nonneg (show (0 : ℝ) ≤ 9 / 10 by norm_num)
    nlinarith
  have e1 : Real.exp (-1) ≤ 1 / 2 := by
    rw [Real.exp_neg]
    calc (Real.exp 1)⁻¹ ≤ 2⁻¹ := inv_anti₀ (by norm_num) h1
      _ = 1 / 2 := by norm_num
  have e2 : Real.exp (-(5 / 4 - a)) ≤ Real.exp (-(9 / 10)) :=
    Real.exp_le_exp.mpr (by linarith)
  have e3 : Real.exp (-(9 / 10)) ≤ 1 / 2.3 := by
    rw [Real.exp_neg]
    calc (Real.exp (9 / 10))⁻¹ ≤ (2.3 : ℝ)⁻¹ := inv_anti₀ (by norm_num) h2
      _ = 1 / 2.3 := by norm_num
  linarith [show (1 / 2.3 : ℝ) ≤ 0.44 by norm_num]

/-- The sum over the subsets `S` of `F` of `e^{-(5|F| - |S|)/4} · 2^{4 t(S)}`, where
`u t(S) ≤ |F| - |S|` and `u ≥ 8`, is at most `1`. -/
theorem sum_powerset_le_one {α : Type*} [DecidableEq α] (F : Finset α) {u : ℝ} (hu : 8 ≤ u)
    (t : Finset α → ℕ) (ht : ∀ S ∈ F.powerset, u * t S ≤ (F.card : ℝ) - S.card) :
    ∑ S ∈ F.powerset, Real.exp (-((5 * (F.card : ℝ) - S.card) / 4)) * (2 : ℝ) ^ (4 * t S) ≤ 1 := by
  set a : ℝ := 4 * Real.log 2 / u with ha
  have hu0 : 0 < u := by linarith
  have hlog0 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  have ha0 : 0 ≤ a := by positivity
  have ha1 : a ≤ 7 / 20 := by
    rw [ha, div_le_iff₀ hu0]
    nlinarith
  have hterm : ∀ S ∈ F.powerset,
      Real.exp (-((5 * (F.card : ℝ) - S.card) / 4)) * (2 : ℝ) ^ (4 * t S) ≤
        (Real.exp (-1)) ^ S.card * (Real.exp (-(5 / 4 - a))) ^ (F \ S).card := by
    intro S hS
    have hSF : S ⊆ F := Finset.mem_powerset.mp hS
    have hcard : (F \ S).card = F.card - S.card := Finset.card_sdiff_of_subset hSF
    have hle : S.card ≤ F.card := Finset.card_le_card hSF
    have h2 : (2 : ℝ) ^ (4 * t S) = Real.exp ((4 * t S : ℕ) * Real.log 2) := by
      rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]
    have h3 : ((4 * t S : ℕ) : ℝ) * Real.log 2 ≤ a * ((F.card : ℝ) - S.card) := by
      have := ht S hS
      rw [ha]
      push_cast
      have : 4 * (t S : ℝ) ≤ 4 * (((F.card : ℝ) - S.card) / u) := by
        have : (t S : ℝ) ≤ ((F.card : ℝ) - S.card) / u := by
          rw [le_div_iff₀ hu0]; linarith
        linarith
      calc 4 * (t S : ℝ) * Real.log 2 ≤ 4 * (((F.card : ℝ) - S.card) / u) * Real.log 2 :=
            mul_le_mul_of_nonneg_right this hlog0.le
        _ = 4 * Real.log 2 / u * ((F.card : ℝ) - S.card) := by ring
    rw [h2, ← Real.exp_nat_mul, ← Real.exp_nat_mul, hcard, ← Real.exp_add]
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have e : ((F.card - S.card : ℕ) : ℝ) = (F.card : ℝ) - S.card := by
      rw [Nat.cast_sub hle]
    rw [e]
    nlinarith
  calc ∑ S ∈ F.powerset, Real.exp (-((5 * (F.card : ℝ) - S.card) / 4)) * (2 : ℝ) ^ (4 * t S)
      ≤ ∑ S ∈ F.powerset, (Real.exp (-1)) ^ S.card * (Real.exp (-(5 / 4 - a))) ^ (F \ S).card :=
        Finset.sum_le_sum hterm
    _ = ∏ _x ∈ F, (Real.exp (-1) + Real.exp (-(5 / 4 - a))) := by
        rw [Finset.prod_add]
        refine Finset.sum_congr rfl fun S _ => ?_
        simp
    _ ≤ 1 := by
        exact Finset.prod_le_one₀ (fun _ _ => by positivity)
          (fun _ _ => exp_neg_add_le_one ha1)

end Balaban.LargeField
