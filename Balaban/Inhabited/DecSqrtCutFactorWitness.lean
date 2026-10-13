/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.YregBlocksWitness
public import Balaban.Inhabited.LocalizationSettings
public import Balaban.Localization.DecSqrtCutFactor
public import Balaban.Localization.DecoupledCovUnit
import Mathlib.Tactic.Positivity

/-!
# Non-vacuity of `DecSqrtCutFactor`

On the witness geometry of `YregBlocksWitness.lean` (`d = L = 3`, `N₁ = 6`, `k = 1`) with `N = 1`,
potential `α = 0`, constant field `φ ≡ 1` (`δ = 0`), `κ = 0` and the cut configuration
`extS (cutPt J)` with non-empty `Yreg`, `CovStanding` holds for the unit lattice, and the theorem
`CovStanding.decCovSqrt_BD_unit` applies with `Y' = Yreg` (a union of components of itself).
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization
  Balaban.Localization.I5Inhabited Balaban.Fluctuation Balaban.Analysis

/-- **Non-vacuity of the square-root block diagonality.** There is a witness geometry, a cut point
with non-empty `Yreg`, standing hypotheses `CovStanding` for the unit lattice and `HatConn`, and
the decoupled covariance square root is block diagonal for the labels of `Y' = Yreg`. -/
theorem decCovSqrt_bd_nonempty :
    ∃ (m₁ : ℕ) (ϱ : ℝ) (G : GeneratingSet 3 3 (6 * 3 ^ m₁) (1 + 1) ϱ)
      (J : Finset (cubeIdx G)),
      HatConn G ∧ (Yreg G (extS G (cutPt J))).Nonempty ∧
      CovStanding G (compWeight 3 1) 1 0 (0 : G.Ω 1 → ℂ) 0 (extS G (cutPt J)) 0
        (fun _ _ => (1 : ℂ) : _ → Fin 1 → ℂ) (unitQ G) (unitP G) ∧
      BD (fun p : unitPts G × Fin 1 => unitLabel G (Yreg G (extS G (cutPt J))) p.1)
        (fun p : unitPts G × Fin 1 => unitLabel G (Yreg G (extS G (cutPt J))) p.1)
        (decCovSqrt G (compWeight 3 1) 1 0 (0 : G.Ω 1 → ℂ) (extS G (cutPt J))
          (fun _ _ => (1 : ℂ) : _ → Fin 1 → ℂ) (unitQ G) (unitP G)) := by
  classical
  obtain ⟨m₁, h4, hc⟩ := exists_m₁_cstar
  have S := xSetting_pos h4
  set G := GP m₁ (rhoSep m₁) with hG
  have hz : ((2 : ℕ), (0 : CTorus 3 3 6 m₁ (1 + 1))) ∈ cubeIdx G := by
    rw [mem_cubeIdx]
    refine ⟨⟨by norm_num, by norm_num⟩, ?_, fun μ => by simp⟩
    show (0 : CTorus 3 3 6 m₁ (1 + 1)) ∈ G.layer 2
    rw [hG, GP_layer_two]; exact Finset.mem_univ _
  have hmem : (0 : CTorus 3 3 6 m₁ (1 + 1)) ∈ hatBox ((2 : ℕ), (0 : CTorus 3 3 6 m₁ (1 + 1))) := by
    unfold hatBox
    rw [mem_boxSet]
    intro μ
    refine ⟨0, ?_⟩
    have hB : (1 : ℝ) ≤ (3 : ℝ) ^ (2 + m₁) := one_le_pow₀ (by norm_num)
    simp only [Int.cast_zero, zero_mul, add_zero]
    unfold hatRad
    have h0 : (((0 : CTorus 3 3 6 m₁ (1 + 1)) μ).val : ℝ) = 0 := by simp
    rw [h0, zero_add, zero_sub, abs_neg, abs_of_nonneg (by push_cast; linarith)]
    push_cast
    have : (0 : ℝ) ≤ 3 * (3 : ℝ) ^ 2 * (3 : ℝ) ^ 2 := by positivity
    linarith
  set J : Finset (cubeIdx G) := (Qset G ((2 : ℕ), (0 : CTorus 3 3 6 m₁ (1 + 1)))).subtype
    (· ∈ cubeIdx G) with hJ
  have hne : (Yreg G (extS G (cutPt J))).Nonempty := by
    refine ⟨0, hatI_subset_Yreg_cutPt hz ?_⟩
    unfold hatI
    rw [Finset.mem_filter]
    exact ⟨hmem, by rw [hG, GP_Ω]; simp⟩
  have hCS : CovStanding G (compWeight 3 1) 1 0 (0 : G.Ω 1 → ℂ) 0 (extS G (cutPt J)) 0
      (fun _ _ => (1 : ℂ) : _ → Fin 1 → ℂ) (unitQ G) (unitP G) := by
    refine ⟨fun x hx => ⟨S, ?_, hx, le_rfl, by simpa using hc, ?_⟩, ?_, le_rfl, by simp,
      (isUnitLatticeB_unit (G := G)).toIsUnitLattice⟩
    · intro x
      simp only [Pi.zero_apply, norm_zero]
      have := coerciveConst_pos (by norm_num : 0 < 3)
      have hs := spacing_pos G (x := (x : CTorus 3 3 6 m₁ (1 + 1)))
      positivity
    · intro P
      unfold extS cutPt
      split_ifs <;> simp
    · refine ⟨⟨fun x _ μ => ?_, fun x _ => ?_⟩, fun x _ => ?_, fun x _ => ?_⟩
      · simp [vn]
      · have : (fun _ : Fin 1 => (3 : ℂ) + 3 - 3 * 2) = 0 := by funext i; norm_num
        simp [vn, this]
      · simp [vn, EuclideanSpace.norm_eq]; norm_num
      · simp
  exact ⟨m₁, rhoSep m₁, G, J, GP_hatConn, hne, hCS,
    hCS.decCovSqrt_BD_unit GP_hatConn ⟨Finset.Subset.refl _, fun x hx y hy _ => hy⟩⟩

end Balaban.Inhabited
