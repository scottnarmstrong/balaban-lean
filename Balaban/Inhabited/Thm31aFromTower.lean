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
/-- **Theorem 3.1 (a) at the general tower, with polymer support and root clause.**  The statement
of `thm31a_zeroClass_supp_fromTower` at `T : StepTowerG d L N κmin` with `T.m₀ = 1`, a constants
record `C` with the rates and label constants of `T` (`StepTowerG.exists_outputConsts`) and the
step `S = hatStepKG … ϱ …` over any `ϱ = rhoSepG d L T.m₁`: beyond a threshold `β₀`, for every root
`z`, `ℰ₀^{(k+1)}(z)` is a sum over finite sets `T'` of level-one blocks of coefficients `e T'` with
`‖e T'‖ ≤ (N L^d BL + 1) K₀ e^{-κ' d_Ext(T')}`, where
`BL = covBLogMax d L κ / (1 - (detDeg d L + 1)² · 2 / e^κ)`, and `e T' ≠ 0` implies that the root
cube of `z` lies in `T'` and that `sitesOf T'` is a polymer domain.  The ingredients are the record
`e1MarksC_zeroClass_fromTowerG_anchor`, the determinant expansion
`detExpansionLocC_scale_fromTowerG` and the generic `thm31aC_coeff_supp`.  The fixed
`thm31a_zeroClass_supp_fromTower` is its corollary. -/
theorem thm31a_zeroClass_supp_fromTowerG {d L N : ℕ} [NeZero L] {κmin : ℝ}
    (T : StepTowerG d L N κmin) (hm₀ : T.m₀ = 1) (C : StepOutputConsts d L)
    (hKc : C.Kc = 2 * (K0 d L T.κ0 + 1))
    (hKall : C.Kall = max (2 * K0 d L T.κ0) (rootUnionK d L T.m₀ T.m₁ T.κ0))
    (hH : C.kH = 2 * T.κdec - 1) (h0 : C.k0 = T.κ0) (h' : C.k' = T.κ') {A₁ : ℝ}
    (hA : 0 < A₁) (p : ℕ) :
    ∃ β₀ : ℝ, 3 ≤ β₀ ∧
      ∀ (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁], L ^ T.m₀ ∣ N₁ → 5 < N₁ →
      ∀ ν : ℝ, 0 < ν → ν * (L : ℝ) ^ (2 * (k + 1)) ≤ 1 → ∀ β : ℝ, β₀ ≤ β →
      ∀ p₁ : ℝ, p₁ ≤ pLog A₁ p (β * (L : ℝ) ^ (k * (d - 2))) →
      StepScaleDataG T k hk N₁ ν β p₁ →
      ∀ {ϱ : ℝ}, ϱ = rhoSepG d L T.m₁ → ∀ (S : StepSetting d L N₁ T.m₁ k N ϱ),
        S = hatStepKG T.hN k T.m₁ ϱ hk ν β p₁ T.δ → 0 < S.p₁ →
      ∀ z : RootIdx d L N₁ T.m₁ (k + 1),
        ∃ e : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := T.m₁) (K := k + 1) 1 (k + 1)
            Set.univ) → ℂ,
          S.E0locC (zeroClass d L N₁ T.m₁ k N ϱ) z = ∑ T', e T' ∧
          (∀ T', ‖e T'‖ ≤ ((N : ℝ) * (L : ℝ) ^ d * (covBLogMax d L T.κ /
              (1 - ((detDeg d L + 1 : ℕ) : ℝ) ^ 2 * (2 / Real.exp T.κ))) + 1) *
            K0 d L T.κ0 * Real.exp (-T.κ' * dExt T')) ∧
          (∀ T', e T' ≠ 0 → rootCube (m₀ := 1) (K := k + 1) z ∈ T' ∧
            IsPolyDom 1 (k + 1) (sitesOf T')) := by
  obtain ⟨β₀, h3, h⟩ := e1MarksC_zeroClass_fromTowerG_anchor T hm₀ C hKc hKall hH h0 h' hA p
  refine ⟨β₀, h3, fun k hk N₁ _ h3N hN ν hν0 hν β hβ p₁ hp₁ D ϱ hϱ S hS hp z => ?_⟩
  obtain ⟨I, -, -, hκ', -, hbud, hroot⟩ := h k hk N₁ h3N hN ν hν0 hν β hβ p₁ hp₁ D hϱ S hS hp z
  have hLN : L ∣ N₁ := by rw [hm₀] at h3N; simpa using h3N
  obtain ⟨hE, -⟩ := detExpansionLocC_scale_fromTowerG T k hk N₁ hLN hN hν0.le hν β p₁ hϱ hS
  obtain ⟨E, -⟩ := hE z
  subst hϱ
  obtain rfl : S = T.step k hk N₁ ν β p₁ := hS
  have hz := T.det_z
  have hzpos : 0 < 1 - ((detDeg d L + 1 : ℕ) : ℝ) ^ 2 * (2 / Real.exp T.κ) := by linarith
  have hκ : 0 ≤ T.κ := by
    have h1 := T.κ_lower
    have h2 := T.marks_κdec_nonneg
    have : (0 : ℝ) ≤ 4 * (d : ℝ) * (((2 * L + 1) ^ d : ℕ) : ℝ) * T.κdec := by positivity
    linarith
  have hL1 : 1 ≤ L := le_trans (by norm_num) T.hL
  have hBL : 0 ≤ covBLogMax d L T.κ /
      (1 - ((detDeg d L + 1 : ℕ) : ℝ) ^ 2 * (2 / Real.exp T.κ)) := by
    have h1 := one_le_covBLog d hL1 (a := 2) (by norm_num) (2 / (L : ℝ) ^ 2) hκ
    unfold covBLogMax
    exact div_nonneg (by linarith) hzpos.le
  have hK1 : 1 ≤ K0 d L T.κ0 := by
    unfold K0
    have h1 : Real.exp (-1) < 1 := Real.exp_lt_one_iff.2 (by norm_num)
    have h2 : 0 < 1 - Real.exp (-1) := by linarith
    rw [le_div_iff₀ h2]
    have := Real.one_le_exp (aEnt_nonneg d L)
    have := Real.exp_pos (-1)
    linarith
  have hdet : (L : ℝ) ^ d * ((1 / 2 : ℝ) * N * covBLogMax d L T.κ /
        (1 - ((detDeg d L + 1 : ℕ) : ℝ) ^ 2 * (2 / Real.exp T.κ))) ≤
      (N : ℝ) * (L : ℝ) ^ d * (covBLogMax d L T.κ /
        (1 - ((detDeg d L + 1 : ℕ) : ℝ) ^ 2 * (2 / Real.exp T.κ))) * K0 d L T.κ0 := by
    have e : (1 / 2 : ℝ) * N * covBLogMax d L T.κ /
        (1 - ((detDeg d L + 1 : ℕ) : ℝ) ^ 2 * (2 / Real.exp T.κ)) =
        (1 / 2 : ℝ) * N * (covBLogMax d L T.κ /
        (1 - ((detDeg d L + 1 : ℕ) : ℝ) ^ 2 * (2 / Real.exp T.κ))) := by ring
    rw [e]
    have hP : 0 ≤ (N : ℝ) * (L : ℝ) ^ d * (covBLogMax d L T.κ /
        (1 - ((detDeg d L + 1 : ℕ) : ℝ) ^ 2 * (2 / Real.exp T.κ))) :=
      mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (Nat.cast_nonneg _) _)) hBL
    nlinarith [mul_nonneg hP (sub_nonneg.2 hK1)]
  obtain ⟨hs1, hs2, hs3, hs4⟩ := thm31aC_coeff_supp E D.xi I (by rw [hκ']; exact T.det_rate)
    hbud hdet
  refine ⟨_, hs1, fun T' => ?_, fun T' h => ⟨hs4 hroot T' h, hs3 T' h⟩⟩
  have := hs2 T'
  rw [hκ'] at this
  exact this

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
  obtain ⟨β₀, h3, H⟩ := thm31a_zeroClass_supp_fromTowerG T.toG rfl (stepOutputPhysical T hHull)
    rfl rfl rfl rfl rfl hA p
  refine ⟨β₀, h3, fun k hk N₁ _ h3N hN ν hν0 hν β hβ p₁ hp hp₁ D z => ?_⟩
  have e : (((3 : ℕ) : ℝ)) ^ (k * (3 - 2)) = 3 ^ k := by norm_num
  obtain ⟨e', hsum, hbd, hsupp⟩ := H k hk N₁ (by simpa using h3N) hN ν hν0 (by simpa using hν) β
    hβ p₁ (by rw [e]; exact hp₁) (StepTower.scaleDataG_of_fixed T D) (ϱ := rhoSep T.m₁)
    (rhoSepG_three _).symm (T.step k hk N₁ ν β p₁) rfl hp z
  refine ⟨e', hsum, fun T' => ?_, hsupp⟩
  have hb := hbd T'
  simp only [Nat.cast_ofNat] at hb
  exact hb

end Balaban.Inhabited
