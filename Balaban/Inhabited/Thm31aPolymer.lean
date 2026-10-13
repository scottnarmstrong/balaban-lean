/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.Thm31bPolymerSupport
public import Balaban.Fluctuation.DetStepInstance
public import Balaban.Fluctuation.DetOutputTerms
public import Balaban.Fluctuation.RootActiveSize
import Mathlib.Tactic.Positivity

/-!
# Support of the canonical coefficients of Theorem 3.1 (a); the energy regrouped on collar hulls

The canonical coefficient of Theorem 3.1 (a) for the complex step is
`e1CoeffC I (E.toDetExpansionC hD) T = E.term S.D' T + interpCoeff I T`, for marks
`I : E1MarksC S C BS z` and localized determinant terms `E : DetExpansionLocC`.

* `e1CoeffC_loc_eq_zero_of_not_isPolyDom`: it vanishes unless `sitesOf T` is a polymer domain.
  The determinant part vanishes by the `anchor` field of `E`; the mark part by
  `interpCoeff_eq_zero_of_dOmega_top`.
* `e1CoeffC_loc_eq_zero_of_not_mem`: it vanishes unless the root cube of `z` lies in `T`, under the
  hypothesis that the blocks of every mark label contain the root cube of `z`.  The record
  `E1MarksC` has no such field, and no landed lemma gives it for an arbitrary record (the
  determinant part needs no hypothesis).
* `thm31aC_coeff_supp`: the expansion of `E0locC` over sets of cubes with the canonical
  coefficient, its bound with the stated constant, and its support, generic in the record.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Localization Balaban.Polymer Balaban.Multiscale Balaban.Background
  Balaban.SmallField Balaban.SmallField.Def6 Balaban.Inhabited MeasureTheory Metric

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}
  {S : StepSetting d L N₁ m₁ k N ϱ} {C : StepClass d L N₁ m₁ k N ϱ} {m₀ : ℕ}
  {BS : BlockSplit S m₀} {z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1)))}
  {eps κ'' cdet : ℝ}

/-- **The canonical coefficient vanishes off polymer domains.** -/
theorem e1CoeffC_loc_eq_zero_of_not_isPolyDom (E : DetExpansionLocC S m₀ z eps κ'' cdet)
    (hD : XiCData S.G' S.a S.ν (k + 1) 1 eps S.D') (I : E1MarksC S C BS z)
    {T : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) m₀ (k + 1)
      Set.univ)} (hT : ¬ IsPolyDom m₀ (k + 1) (sitesOf T)) :
    e1CoeffC I (E.toDetExpansionC hD) T = 0 := by
  unfold e1CoeffC
  rw [DetExpansionLocC.toDetExpansionC_term, E.term_eq_zero_of_not_isPolyDom hD hT,
    interpCoeff_eq_zero_of_dOmega_top I (dOmega_top_of_not_isPolyDom hT), add_zero]

/-- **The canonical coefficient vanishes unless the root cube lies in `T`**, given that the blocks
of each mark label contain the root cube of `z`. -/
theorem e1CoeffC_loc_eq_zero_of_not_mem (E : DetExpansionLocC S m₀ z eps κ'' cdet)
    (hD : XiCData S.G' S.a S.ν (k + 1) 1 eps S.D') (I : E1MarksC S C BS z)
    (hI : ∀ i, rootCube (m₀ := m₀) (K := k + 1) z ∈
      blocksOf m₀ (k + 1) Set.univ (I.Lab.ysite (I.y0 i)))
    {T : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) m₀ (k + 1)
      Set.univ)} (hT : rootCube (m₀ := m₀) (K := k + 1) z ∉ T) :
    e1CoeffC I (E.toDetExpansionC hD) T = 0 := by
  have hm : interpCoeff I T = 0 := by
    by_contra h
    obtain ⟨i, hi⟩ := exists_blocksOf_subset_of_interpCoeff_ne_zero I h
    exact hT (hi (hI i))
  unfold e1CoeffC
  rw [DetExpansionLocC.toDetExpansionC_term, E.term_eq_zero_of_not_mem hD hT, hm, add_zero]

open Classical in
/-- **Theorem 3.1 (a) with the canonical coefficient, its support and the stated constant**,
generic in the record.  With `e T = e1CoeffC I (E.toDetExpansionC hD) T`: `S.E0locC C z = ∑_T e T`,
`‖e T‖ ≤ (N L^d BL + 1) K0c e^{-κ' dExt T}`, `e T ≠ 0` implies that `sitesOf T` is a polymer
domain, and, if the blocks of every mark label contain the root cube of `z`, that the root cube
lies in `T`. -/
theorem thm31aC_coeff_supp (E : DetExpansionLocC S m₀ z eps κ'' cdet)
    (hD : XiCData S.G' S.a S.ν (k + 1) 1 eps S.D') (I : E1MarksC S C BS z)
    (hκ'' : I.κ' ≤ κ'') {BL K0c : ℝ}
    (hmark : CPE d L I.Kc I.κH I.κ0 I.κ' *
      (∑ i, I.F0 i * Real.exp (-I.κ0 * I.Lab.dl (I.y0 i))) ≤ K0c)
    (hdet : cdet ≤ N * (L : ℝ) ^ d * BL * K0c) :
    S.E0locC C z = ∑ T, e1CoeffC I (E.toDetExpansionC hD) T ∧
    (∀ T, ‖e1CoeffC I (E.toDetExpansionC hD) T‖ ≤
      (N * (L : ℝ) ^ d * BL + 1) * K0c * Real.exp (-I.κ' * dExt T)) ∧
    (∀ T, e1CoeffC I (E.toDetExpansionC hD) T ≠ 0 → IsPolyDom m₀ (k + 1) (sitesOf T)) ∧
    ((∀ i, rootCube (m₀ := m₀) (K := k + 1) z ∈
        blocksOf m₀ (k + 1) Set.univ (I.Lab.ysite (I.y0 i))) →
      ∀ T, e1CoeffC I (E.toDetExpansionC hD) T ≠ 0 → rootCube (m₀ := m₀) (K := k + 1) z ∈ T) := by
  obtain ⟨-, h2, h3⟩ := thm31aC_coeff I hκ'' (E.toDetExpansionC hD)
  refine ⟨h2, fun T => (h3 T).trans ?_, fun T hT => ?_, fun hI T hT => ?_⟩
  · exact mul_le_mul_of_nonneg_right (by nlinarith) (Real.exp_pos _).le
  · by_contra hp
    exact hT (e1CoeffC_loc_eq_zero_of_not_isPolyDom E hD I hp)
  · by_contra hp
    exact hT (e1CoeffC_loc_eq_zero_of_not_mem E hD I hI hp)

end Balaban.Fluctuation
