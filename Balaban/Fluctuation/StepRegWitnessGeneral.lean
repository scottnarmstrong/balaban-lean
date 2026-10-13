/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.StepRegWitness
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The witness parameters of the step for general `d`, `L`, `N`

The constants `witB5`, `witK2` of `StepRegWitness` at general dimension `d`, block size `L` and
number of spin components `N`, and the general version of `exists_witness_params`: for every
`d ≥ 1`, `L ≥ 2`, `N` and every lower bound `T₀ m₁` there are a scale `m₁`, radii `δ`, `δ'` and
`T` satisfying all the numerical conditions of the witness.  The landed theorem is the instance
`d = L = 3`, `N = 2`.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization Balaban.Inhabited
  Balaban.Localization.I5Inhabited Balaban.SmallField.Def6 Balaban.SmallField Finset

/-- The constant `B₅` of the witness at general `d`, `L`, `N`. -/
noncomputable def witB5G (d L N : ℕ) : ℝ :=
  max 1 (Real.sqrt (N : ℝ) * covSupConst d L N (compWeight L 1 1))

/-- The constant `K₂` of the witness at general `d`, `L`, `N`. -/
noncomputable def witK2G (d L N : ℕ) [NeZero L] : ℝ :=
  max (max 1 (cK2 d L N)) (Real.sqrt (N : ℝ) * cK2 d L N)

theorem witB5G_three_three_two : witB5G 3 3 2 = witB5 := rfl

theorem witK2G_three_three_two : witK2G 3 3 2 = witK2 := rfl

theorem fluctRadius_pos_general {d L N : ℕ} [NeZero L] (hd : 0 < d) : 0 < fluctRadius d L N := by
  have h1 := deltaStar_pos (d := d) (L := L) (N := N) hd
  have h2 := bgC0_pos d L N hd
  have h3 := cK2_pos d L N
  have h4 := bgC1_pos' (d := d) (L := L) (N := N) hd
  unfold fluctRadius
  refine lt_min (lt_min (by positivity) (by positivity)) (lt_min (by positivity) (by positivity))

theorem fluctRadius_pos_three_eq : fluctRadius_pos_general (d := 3) (L := 3) (N := 2)
    (by norm_num) = fluctRadius_pos_three := rfl

/-- Parameters of the witness at general `d`, `L`, `N`: the numerical conditions are satisfiable,
with an arbitrary lower bound `T₀` on `T = β_k^{1/2}`.  Here `0 < d` and `2 ≤ L`; the numerals
`2` (the radius `p⁺`), `3` (in `3 B₅ K₂ p⁺`) and `4` (`4 ≤ m₁`, `1/4`, `/ 4`) are those of the
step datum and do not depend on `d`, `L`, `N`. -/
theorem exists_witness_params_general (d L N : ℕ) [NeZero L] (hd : 0 < d) (hL : 2 ≤ L)
    (T₀ : ℕ → ℝ) :
    ∃ (m₁ : ℕ) (δ δ' T : ℝ), 4 ≤ m₁ ∧ cstarX d L ≤ (L : ℝ) ^ m₁ ∧ 0 < δ ∧
      δ ^ 2 * smallConstX d L 0 ≤ 1 / 4 ∧ 0 < δ' ∧ δ' ≤ thm73C3 d L N / 2 ∧
      bgK1 d L N * δ' ≤ δ / 4 ∧ bgK1 d L N * δ' ≤ coerciveConst d / 4 ∧ 0 < T ∧ T₀ m₁ ≤ T ∧
      3 * witB5G d L N * witK2G d L N * 2 ≤ T * δ ∧
      witB5G d L N * 2 ≤ T * fluctRadius d L N := by
  have hL1 : (1 : ℝ) < L := by exact_mod_cast hL
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (cstarX d L) hL1
  obtain ⟨δs, hδs, hδs'⟩ := exists_deltaStar d L 0
  have hsm : δs ^ 2 * smallConstX d L 0 ≤ 1 / 4 := by
    rcases hδs' δs le_rfl with h | h
    · exact h
    · exact absurd hδs h.not_gt
  have hK := bgK1_pos (d := d) (L := L) (N := N)
  have hc := coerciveConst_pos (d := d) hd
  have hC3 := thm73C3_pos (d := d) (L := L) (N := N) hd
  have hrad := fluctRadius_pos_general (d := d) (L := L) (N := N) hd
  set δ' : ℝ := min (thm73C3 d L N / 2) (min (δs / (4 * bgK1 d L N))
    (coerciveConst d / (4 * bgK1 d L N))) with hδ'
  have hδ'0 : 0 < δ' := lt_min (by positivity) (lt_min (by positivity) (by positivity))
  have hb1 : δ' ≤ δs / (4 * bgK1 d L N) := (min_le_right _ _).trans (min_le_left _ _)
  have hb2 : δ' ≤ coerciveConst d / (4 * bgK1 d L N) :=
    (min_le_right _ _).trans (min_le_right _ _)
  obtain ⟨T, hT, hT1, hT2⟩ := exists_large_T (B₅ := witB5G d L N) (K₂ := witK2G d L N) (pp := 2)
    hδs hrad
  refine ⟨max n 4, δs, δ', max T (T₀ (max n 4) + 1), le_max_right _ _,
    hn.le.trans (pow_le_pow_right₀ hL1.le (le_max_left _ _)), hδs, hsm, hδ'0, min_le_left _ _,
    ?_, ?_, lt_of_lt_of_le hT (le_max_left _ _), (le_trans (by linarith) (le_max_right _ _)),
    ?_, ?_⟩
  · calc bgK1 d L N * δ' ≤ bgK1 d L N * (δs / (4 * bgK1 d L N)) :=
          mul_le_mul_of_nonneg_left hb1 hK.le
      _ = δs / 4 := by field_simp
  · calc bgK1 d L N * δ' ≤ bgK1 d L N * (coerciveConst d / (4 * bgK1 d L N)) :=
          mul_le_mul_of_nonneg_left hb2 hK.le
      _ = coerciveConst d / 4 := by field_simp
  · exact hT1.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hδs.le)
  · exact hT2.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hrad.le)

/-- The landed `exists_witness_params` is the instance `d = L = 3`, `N = 2`. -/
theorem exists_witness_params_of_general (T₀ : ℕ → ℝ) :
    ∃ (m₁ : ℕ) (δ δ' T : ℝ), 4 ≤ m₁ ∧ cstarX 3 3 ≤ (3 : ℝ) ^ m₁ ∧ 0 < δ ∧
      δ ^ 2 * smallConstX 3 3 0 ≤ 1 / 4 ∧ 0 < δ' ∧ δ' ≤ thm73C3 3 3 2 / 2 ∧
      bgK1 3 3 2 * δ' ≤ δ / 4 ∧ bgK1 3 3 2 * δ' ≤ coerciveConst 3 / 4 ∧ 0 < T ∧ T₀ m₁ ≤ T ∧
      3 * witB5 * witK2 * 2 ≤ T * δ ∧ witB5 * 2 ≤ T * fluctRadius 3 3 2 := by
  have h := exists_witness_params_general 3 3 2 (by norm_num) (by norm_num) T₀
  rw [witB5G_three_three_two, witK2G_three_three_two] at h
  simpa only [Nat.cast_ofNat] using h

end Balaban.Fluctuation
