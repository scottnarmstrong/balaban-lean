/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Flow.CellMoments
public import Balaban.Flow.MatrixInfty
public import Balaban.SmallField.RenormMomentAlg

/-!
# The moment sum and the third row of `matrixInfty`

With the coarse parameters `a = a_n`, `v = M² ν` (`M = L^n`), `w = a/M²`, the limits
`y = d M^d cellAvg Φ₀`, `z = d M^d cellAvg Ψ₀` of the pairings `R₁`, `R₂` give

`secondVarScalar w ν ξ₂ ξ₃ ζ 0 y z =
   (-4 d M^d / M²) (ζ a₃₁ + ξ₂ a₃₂ + ξ₃ a₃₃) + ξ₃ ζ w² (w z - 2 y)`,

where `(a₃₁, a₃₂, a₃₃)` is the third row of `Flow.matrixInfty a v τ c₁ c₂ 1` with the lattice sums
`c_i = latticeSum M v i` and `τ = latticeTau M` (`moment_algebra`).  The factor `-4 d M^{d-2}` is
exact; `ζ a₃₁` is the term `a₃₁ ξ₁` of the matrix with `ζ = ε ξ₁` (the matrix entry carries `ε`).
-/

@[expose] public section

namespace Balaban.Flow

open Finset Balaban.Fluctuation

theorem cellSum_one_eq {M : ℕ} [NeZero M] {v : ℝ} (hM : (M : ℝ) ≠ 0) :
    cellSum M (v / (M : ℝ) ^ 2) 1 =
      (M : ℝ) ^ 2 * ∑ n ∈ (Finset.univ : Finset (ZMod M)).erase 0, 1 / (latticeSymbol M n + v) := by
  unfold cellSum
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun n hn => ?_
  have hp : 0 < cellEig M n := cellEig_pos (Finset.mem_erase.1 hn).1
  rw [latticeSymbol_eq_cellEig]
  field_simp

theorem cellSum_two_eq {M : ℕ} [NeZero M] {v : ℝ} (hM : (M : ℝ) ≠ 0) :
    cellSum M (v / (M : ℝ) ^ 2) 2 =
      (M : ℝ) ^ 4 * ∑ n ∈ (Finset.univ : Finset (ZMod M)).erase 0, 1 / (latticeSymbol M n + v) ^ 2 := by
  unfold cellSum
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun n hn => ?_
  have hp : 0 < cellEig M n := cellEig_pos (Finset.mem_erase.1 hn).1
  rw [latticeSymbol_eq_cellEig]
  field_simp

theorem moment_algebra {M : ℕ} [NeZero M] (d : ℕ) {a v : ℝ} (hv : 0 < v) (ha : 0 ≤ a)
    (ξ₂ ξ₃ ζ : ℝ) :
    secondVarScalar ((a / (M : ℝ) ^ 2 : ℝ) : ℂ) (v / (M : ℝ) ^ 2) ξ₂ ξ₃ ζ 0
        ((d : ℂ) * (M : ℂ) ^ d * cellAvg (phiF0 M (a / (M : ℝ) ^ 2) (v / (M : ℝ) ^ 2)))
        ((d : ℂ) * (M : ℂ) ^ d * cellAvg (psiF0 M (a / (M : ℝ) ^ 2) (v / (M : ℝ) ^ 2))) =
      (-4 * (d : ℂ) * (M : ℂ) ^ d / (M : ℂ) ^ 2) *
          ((ζ : ℂ) * infA31 (a : ℂ) (v : ℂ) (latticeTau M : ℂ) (latticeSum M v 1 : ℂ)
            (latticeSum M v 2 : ℂ) 1 +
            (ξ₂ : ℂ) * infA32 (a : ℂ) (v : ℂ) (latticeTau M : ℂ) (latticeSum M v 1 : ℂ)
              (latticeSum M v 2 : ℂ) +
            (ξ₃ : ℂ) * infA33 (a : ℂ) (v : ℂ) (latticeTau M : ℂ) (latticeSum M v 1 : ℂ)
              (latticeSum M v 2 : ℂ)) +
        (ξ₃ : ℂ) * (ζ : ℂ) * ((a / (M : ℝ) ^ 2 : ℝ) : ℂ) ^ 2 *
          (((a / (M : ℝ) ^ 2 : ℝ) : ℂ) *
            ((d : ℂ) * (M : ℂ) ^ d * cellAvg (psiF0 M (a / (M : ℝ) ^ 2) (v / (M : ℝ) ^ 2))) -
            2 * ((d : ℂ) * (M : ℂ) ^ d * cellAvg (phiF0 M (a / (M : ℝ) ^ 2) (v / (M : ℝ) ^ 2)))) := by
  have hM0 : (M : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne M
  have hMpos : (0 : ℝ) < M := lt_of_le_of_ne (Nat.cast_nonneg M) (Ne.symm hM0)
  have hw : 0 ≤ a / (M : ℝ) ^ 2 := by positivity
  have hν : 0 < v / (M : ℝ) ^ 2 := by positivity
  rw [cellAvg_phiF0 hw hν, cellAvg_psiF0 hw hν, cellAvg_phiF0 hw hν, cellSum_one_eq hM0,
    cellSum_two_eq hM0]
  have h1 := latticeSum_one_mul (M := M) hv
  have h2 := latticeSum_two_mul (M := M) hv
  set T1 := ∑ n ∈ (Finset.univ : Finset (ZMod M)).erase 0, 1 / (latticeSymbol M n + v) with hT1
  set T2 := ∑ n ∈ (Finset.univ : Finset (ZMod M)).erase 0, 1 / (latticeSymbol M n + v) ^ 2 with hT2
  have eT1 : T1 = latticeTau M / 12 - v * latticeSum M v 1 := by linarith
  have eT2 : T2 = latticeSum M v 1 - v * latticeSum M v 2 := by linarith
  rw [eT1, eT2]
  unfold secondVarScalar ccC infA31 infA32 infA33 infB1 infB2 latticeTau
  have hM : (M : ℂ) ≠ 0 := by exact_mod_cast hM0
  have hav : ((a : ℂ) + v) ≠ 0 := by exact_mod_cast (by linarith : a + v ≠ 0)
  push_cast
  field_simp
  ring

end Balaban.Flow
