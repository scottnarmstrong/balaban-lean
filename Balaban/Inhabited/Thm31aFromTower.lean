/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.Thm31aPolymer
public import Balaban.Inhabited.E1RecordFromTower
public import Balaban.Inhabited.StepTowerScale
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

/-!
# Theorem 3.1 (a) at the tower: sum, bound, polymer support and root clause

At a scale of the shared tower `T`, beyond one threshold in `β`, for every root `z`: the local
term `ℰ₀^{(k+1)}(z)` of the zero class is a sum over finite sets `T'` of level-one blocks of
coefficients `e T'` with `‖e T'‖ ≤ (2 · 3³ · BL + 1) K₀ e^{-κ' d_Ext(T')}`, where
`BL = covBLogMax 3 3 κ / (1 - (detDeg 3 3 + 1)² · 2 / e^κ)` is the determinant constant of the
tower, and `e T' ≠ 0` implies that the blocks of `T'` form a polymer domain containing the root
cube of `z`.  The ingredients are the record of `e1MarksC_zeroClass_fromTower_anchor` (with its root
clause), the determinant expansion `detExpansionLocC_scale_fromTower` and the generic
`thm31aC_coeff_supp`.  The two numerical hypotheses of the generic theorem hold at the tower:
`κ' ≤ rate` is the field `det_rate` of the tower and
`cdet = 27 · BL ≤ 2 · 27 · BL · K₀` because `K₀ ≥ 1`.

This is the whole-lattice zero-class value at one base datum, with decay `κ'`; it does not give
the paper's rate `κ_a`, the boundary clauses, or a coefficient family in the datum.
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation
  Balaban.Localization Balaban.Localization.LevelPair Balaban.Localization.I5Inhabited
  Balaban.Polymer Balaban.SmallField.Def6 Balaban.Inhabited.LevelStep
  Balaban.Inhabited.MarkBudgetAudit Matrix Metric Set MeasureTheory

open Classical in
/-- **Theorem 3.1 (a) at the tower, with polymer support and root clause.**  See the module
doc-string. -/
theorem thm31a_zeroClass_supp_fromTower {κmin : ℝ} (T : StepTower κmin)
    (hHull : stepHullMin ≤ κmin) {A₁ : ℝ} (hA : 0 < A₁) (p : ℕ) :
    ∃ β₀ : ℝ, 3 ≤ β₀ ∧
      ∀ (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁], 3 ∣ N₁ → 5 < N₁ →
      ∀ ν : ℝ, 0 < ν → ν * 3 ^ (2 * (k + 1)) ≤ 1 → ∀ β : ℝ, β₀ ≤ β →
      ∀ p₁ : ℝ, ∀ _ : 0 < p₁, p₁ ≤ pLog A₁ p (β * 3 ^ k) →
      StepScaleData T k hk N₁ ν β p₁ →
      ∀ z : RootIdx 3 3 N₁ T.m₁ (k + 1),
        ∃ e : Finset (CubeB (d := 3) (L := 3) (N₁ := N₁) (m₁ := T.m₁) (K := k + 1) 1 (k + 1)
            Set.univ) → ℂ,
          (T.step k hk N₁ ν β p₁).E0locC (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) z =
            ∑ T', e T' ∧
          (∀ T', ‖e T'‖ ≤ (2 * (3 : ℝ) ^ 3 * (covBLogMax 3 3 T.κ /
              (1 - ((detDeg 3 3 + 1 : ℕ) : ℝ) ^ 2 * (2 / Real.exp T.κ))) + 1) *
            K0 3 3 T.κ0 * Real.exp (-T.κ' * dExt T')) ∧
          (∀ T', e T' ≠ 0 → rootCube (m₀ := 1) (K := k + 1) z ∈ T' ∧
            IsPolyDom 1 (k + 1) (sitesOf T')) := by
  obtain ⟨β₀, h3, h⟩ := e1MarksC_zeroClass_fromTower_anchor T hHull hA p
  refine ⟨β₀, h3, fun k hk N₁ _ h3N hN ν hν0 hν β hβ p₁ hp hp₁ D z => ?_⟩
  obtain ⟨I, -, -, hκ', -, hbud, hroot⟩ := h k hk N₁ h3N hN ν hν0 hν β hβ p₁ hp hp₁ D z
  obtain ⟨hE, -⟩ := detExpansionLocC_scale_fromTower T k hk N₁ h3N hN hν0.le hν β p₁
  obtain ⟨E, -⟩ := hE z
  have hz := T.det_z
  have hzpos : 0 < 1 - ((detDeg 3 3 + 1 : ℕ) : ℝ) ^ 2 * (2 / Real.exp T.κ) := by linarith
  have hκ : 0 ≤ T.κ := by
    have h1 := T.κ_lower
    have h0 := T.κ0_nonneg
    have h2 := T.κdec_lower
    have : (0 : ℝ) ≤ 4 * ((3 : ℕ) : ℝ) * (((2 * 3 + 1) ^ 3 : ℕ) : ℝ) * T.κdec := by
      have : (0 : ℝ) ≤ T.κdec := by linarith
      positivity
    linarith
  have hBL : 0 ≤ covBLogMax 3 3 T.κ /
      (1 - ((detDeg 3 3 + 1 : ℕ) : ℝ) ^ 2 * (2 / Real.exp T.κ)) := by
    have h1 := one_le_covBLog 3 (L := 3) (by norm_num) (a := 2) (by norm_num)
      (2 / (3 : ℝ) ^ 2) hκ
    unfold covBLogMax
    exact div_nonneg (by linarith) hzpos.le
  have hK1 : 1 ≤ K0 3 3 T.κ0 := by
    unfold K0
    have h1 : Real.exp (-1) < 1 := Real.exp_lt_one_iff.2 (by norm_num)
    have h2 : 0 < 1 - Real.exp (-1) := by linarith
    rw [le_div_iff₀ h2]
    have := Real.one_le_exp (aEnt_nonneg 3 3)
    have := Real.exp_pos (-1)
    linarith
  have hdet : 27 * covBLogMax 3 3 T.κ /
        (1 - ((detDeg 3 3 + 1 : ℕ) : ℝ) ^ 2 * (2 / Real.exp T.κ)) ≤
      ((2 : ℕ) : ℝ) * ((3 : ℕ) : ℝ) ^ 3 * (covBLogMax 3 3 T.κ /
        (1 - ((detDeg 3 3 + 1 : ℕ) : ℝ) ^ 2 * (2 / Real.exp T.κ))) * K0 3 3 T.κ0 := by
    rw [mul_div_assoc]
    simp only [Nat.cast_ofNat]
    nlinarith [mul_nonneg hBL (sub_nonneg.2 hK1)]
  obtain ⟨hs1, hs2, hs3, hs4⟩ := thm31aC_coeff_supp E D.xi I (by rw [hκ']; exact T.det_rate)
    hbud hdet
  refine ⟨_, hs1, fun T' => ?_, fun T' h => ⟨hs4 hroot T' h, hs3 T' h⟩⟩
  have := hs2 T'
  rw [hκ'] at this
  simp only [Nat.cast_ofNat] at this
  exact this

end Balaban.Inhabited
