/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.MarkBudgetAudit
public import Balaban.Inhabited.MarkCorrBudgetG
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

/-!
# The constants of the corrected marks at the tower

For `b = β 3^k` and `q = decMR T k b p₁` (the marked radius of the tower step, by `markedRad_eq`),
the corrected mark of one label has Cauchy radius `R = T.t / (4 q)` on the disc of radius
`U = 17/16`, and its per-root constant after the bridge count is `4 |β| E_* U² J / R³`.
This file proves the domain condition, the size `O(p₁³ / √b)`, the radius condition `R ≥ 2U`
and the smallness of the constant, uniformly in the scale `k`, when `p₁` is polylogarithmic.
-/

@[expose] public section

namespace Balaban.Inhabited.MarkBudgetAudit

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation
  Balaban.Localization Balaban.Localization.LevelPair Balaban.Localization.I5Inhabited
  Balaban.Polymer Balaban.SmallField.Def6 Balaban.Inhabited.LevelStep

variable {κmin : ℝ} (T : StepTower κmin)

/-- The radius `17/16` of the disc on which the corrected marks live. -/
noncomputable def corrU : ℝ := 17 / 16

/-- The Cauchy radius `T.t / (4 q)` of the corrected marks, `q = decMR T k b p₁`. -/
noncomputable def corrR (k : ℕ) (b p₁ : ℝ) : ℝ := T.t / (4 * decMR T k b p₁)

/-- The per-root constant `4 |β| E_* U² J / R³` of the corrected marks. -/
noncomputable def corrF0 (k : ℕ) (β p₁ : ℝ) : ℝ :=
  4 * |β| * Estar T k * corrU ^ 2 * Kmark T / (corrR T k (β * 3 ^ k) p₁) ^ 3

/-- The tower constant `512 √2 J E_max C_max³ U² / t³`. -/
noncomputable def Ccorr : ℝ :=
  512 * Real.sqrt 2 * Kmark T *
    (27 * (2 * (T.t + Vstar T) ^ 2 + 3 * Vstar T ^ 2 +
      (1 + rho4 3 3 2 T.BG T.κ) * Vstar T ^ 2 / 9)) *
    covSupMaxC 3 3 2 T.κ ^ 3 * corrU ^ 2 / T.t ^ 3

theorem corrU_pos : 0 < corrU := by unfold corrU; norm_num

/-- The fixed `corrR` is the general one at the tower `T.toG`. -/
theorem corrR_toG (k : ℕ) (b p₁ : ℝ) : corrR T k b p₁ = corrRG T.toG k b p₁ := by
  unfold corrR corrRG
  rw [decMR_toG]
  rfl

/-- The fixed `corrF0` is the general one at the tower `T.toG`. -/
theorem corrF0_toG (k : ℕ) (β p₁ : ℝ) : corrF0 T k β p₁ = corrF0G T.toG k β p₁ := by
  unfold corrF0 corrF0G
  rw [← scale_three_cast, corrR_toG]
  rfl

/-- The fixed `Ccorr` is the general one at the tower `T.toG`. -/
theorem Ccorr_toG : Ccorr T = CcorrG T.toG := by
  unfold Ccorr CcorrG corrU
  rw [← Kmark_toG, ← Vstar_toG]
  simp only [StepTower.toG_t, StepTower.toG_κ, StepTower.toG_BG]
  have h2 : Real.sqrt ((2 : ℕ) : ℝ) ^ 3 = 2 * Real.sqrt 2 := by
    have := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
    norm_num
    calc Real.sqrt 2 ^ 3 = Real.sqrt 2 ^ 2 * Real.sqrt 2 := by ring
      _ = 2 * Real.sqrt 2 := by rw [this]
  rw [h2]
  norm_num
  ring

theorem corrR_pos {k : ℕ} (hk : 1 ≤ k) {b p₁ : ℝ} (hb : 0 < b) (hp : 0 < p₁) :
    0 < corrR T k b p₁ := by
  rw [corrR_toG]; exact corrRG_pos T.toG hk hb hp

/-- The domain condition `(a + b) · markedRad < δ₁` with `a = b = R` and `δ₁ = T.t`
(`decMR` is the `markedRad` of the tower step, `markedRad_eq`): in fact `2 R q = T.t / 2`. -/
theorem two_corrR_mul_decMR_lt {k : ℕ} (hk : 1 ≤ k) {b p₁ : ℝ} (hb : 0 < b) (hp : 0 < p₁) :
    2 * corrR T k b p₁ * decMR T k b p₁ < T.t := by
  rw [corrR_toG, decMR_toG]
  exact two_corrRG_mul_decMRG_lt T.toG hk hb hp

theorem covSupMaxC_nonneg : 0 ≤ covSupMaxC 3 3 2 T.κ := covSupMaxC_nonnegG T.toG

theorem Ccorr_nonneg : 0 ≤ Ccorr T := by
  rw [Ccorr_toG]; exact CcorrG_nonneg T.toG

/-- **The cubic size**: `F₀^corr ≤ Ccorr · p₁³ / √(β 3^k)`.  Here `512 √2 J E_max C_max³ U² / t³`
is `Ccorr`. -/
theorem corrF0_le {k : ℕ} (hk : 1 ≤ k) {β p₁ : ℝ} (hβ : 0 < β) (hp : 0 < p₁) :
    corrF0 T k β p₁ ≤ Ccorr T * p₁ ^ 3 / Real.sqrt (β * 3 ^ k) := by
  have h := corrF0_leG T.toG hk hβ hp
  rw [scale_three_cast] at h
  rw [corrF0_toG, Ccorr_toG]
  exact h

/-- **The radius condition, uniformly in the scale**: `R ≥ 2U` for polylogarithmic `p₁`. -/
theorem exists_beta0_corrR {A₁ : ℝ} (hA : 0 < A₁) (p : ℕ) :
    ∃ β₀ : ℝ, ∀ k : ℕ, 1 ≤ k → ∀ β : ℝ, β₀ ≤ β → ∀ p₁ : ℝ, 0 < p₁ →
      p₁ ≤ pLog A₁ p (β * 3 ^ k) → 2 * corrU ≤ corrR T k (β * 3 ^ k) p₁ := by
  obtain ⟨β₀, h⟩ := exists_beta0_corrRG T.toG hA p
  refine ⟨β₀, fun k hk β hβ p₁ hp hp₁ => ?_⟩
  rw [← scale_three_cast] at hp₁ ⊢
  have := h k hk β hβ p₁ hp hp₁
  rw [corrR_toG]
  exact this

/-- **Smallness beyond a threshold**, uniformly in the scale. -/
theorem exists_beta0_corrF0_le {ε : ℝ} (hε : 0 < ε) {A₁ : ℝ} (hA : 0 < A₁) (p : ℕ) :
    ∃ β₀ : ℝ, ∀ k : ℕ, 1 ≤ k → ∀ β : ℝ, β₀ ≤ β → ∀ p₁ : ℝ, 0 < p₁ →
      p₁ ≤ pLog A₁ p (β * 3 ^ k) → corrF0 T k β p₁ ≤ ε := by
  obtain ⟨β₀, h⟩ := exists_beta0_corrF0_leG T.toG hε hA p
  refine ⟨β₀, fun k hk β hβ p₁ hp hp₁ => ?_⟩
  rw [← scale_three_cast] at hp₁
  have := h k hk β hβ p₁ hp hp₁
  rw [corrF0_toG]
  exact this

end Balaban.Inhabited.MarkBudgetAudit
