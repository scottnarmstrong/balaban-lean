/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.MarkBudgetAudit
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

theorem corrR_pos {k : ℕ} (hk : 1 ≤ k) {b p₁ : ℝ} (hb : 0 < b) (hp : 0 < p₁) :
    0 < corrR T k b p₁ := by
  have := decMR_pos T hk hb hp
  have := T.t_pos
  unfold corrR; positivity

/-- The domain condition `(a + b) · markedRad < δ₁` with `a = b = R` and `δ₁ = T.t`
(`decMR` is the `markedRad` of the tower step, `markedRad_eq`): in fact `2 R q = T.t / 2`. -/
theorem two_corrR_mul_decMR_lt {k : ℕ} (hk : 1 ≤ k) {b p₁ : ℝ} (hb : 0 < b) (hp : 0 < p₁) :
    2 * corrR T k b p₁ * decMR T k b p₁ < T.t := by
  have hq := decMR_pos T hk hb hp
  have := T.t_pos
  have : 2 * corrR T k b p₁ * decMR T k b p₁ = T.t / 2 := by
    unfold corrR; field_simp; ring
  linarith

private theorem alg_main {b s r t U K E Em C p₁ q : ℝ} (hs : 0 < s) (hsq : s ^ 2 = b)
    (hr : r ^ 2 = 2) (hr0 : 0 < r) (ht : 0 < t) (hU : 0 < U) (hK : 0 < K) (hE : 0 ≤ E)
    (hEm : E ≤ Em) (hp : 0 < p₁) (hq : 0 < q)
    (hqle : q ≤ r * (s⁻¹ * (C * p₁))) :
    256 * b * E * U ^ 2 * K * q ^ 3 / t ^ 3 ≤ 512 * r * K * Em * C ^ 3 * U ^ 2 / t ^ 3 * p₁ ^ 3 / s := by
  subst hsq
  have hr3 : r ^ 3 = 2 * r := by nlinarith
  have h1 : q ^ 3 ≤ (r * (s⁻¹ * (C * p₁))) ^ 3 := pow_le_pow_left₀ hq.le hqle 3
  have hEm0 : 0 ≤ Em := hE.trans hEm
  have h2 : 256 * s ^ 2 * E * U ^ 2 * K * q ^ 3 ≤
      256 * s ^ 2 * Em * U ^ 2 * K * (r * (s⁻¹ * (C * p₁))) ^ 3 := by
    have : 0 ≤ q ^ 3 := by positivity
    gcongr
  have h3 : 256 * s ^ 2 * Em * U ^ 2 * K * (r * (s⁻¹ * (C * p₁))) ^ 3 / t ^ 3 =
      512 * r * K * Em * C ^ 3 * U ^ 2 / t ^ 3 * p₁ ^ 3 / s := by
    have : (r * (s⁻¹ * (C * p₁))) ^ 3 = r ^ 3 * (s⁻¹) ^ 3 * C ^ 3 * p₁ ^ 3 := by ring
    rw [this, hr3]
    field_simp
    ring
  calc _ ≤ 256 * s ^ 2 * Em * U ^ 2 * K * (r * (s⁻¹ * (C * p₁))) ^ 3 / t ^ 3 :=
        div_le_div_of_nonneg_right h2 (by positivity)
    _ = _ := h3

theorem covSupMaxC_nonneg : 0 ≤ covSupMaxC 3 3 2 T.κ := by
  have h1 := covSupConstC_le_covSupMaxC (N := 2) (d := 3) (L := 3) (by norm_num) le_rfl T.κ
    (compWeight_three_mem (k := 1) le_rfl)
  have := covMin_le (compWeight_three_mem (k := 1) le_rfl) T.κ
  have := covMin_pos
  linarith

theorem Ccorr_nonneg : 0 ≤ Ccorr T := by
  have hK := Kmark_pos T
  have h1 := T.rho_nonneg
  have h2 := Vstar_nonneg T
  have ht := T.t_pos
  have hC := covSupMaxC_nonneg T
  have hU := corrU_pos
  unfold Ccorr
  generalize Kmark T = K at hK ⊢
  generalize corrU = U at hU ⊢
  generalize covSupMaxC 3 3 2 T.κ = C at hC ⊢
  generalize Vstar T = V at h2 ⊢
  generalize rho4 3 3 2 T.BG T.κ = ρ at h1 ⊢
  have := Real.sqrt_nonneg 2
  positivity

/-- **The cubic size**: `F₀^corr ≤ Ccorr · p₁³ / √(β 3^k)`.  Here `512 √2 J E_max C_max³ U² / t³`
is `Ccorr`. -/
theorem corrF0_le {k : ℕ} (hk : 1 ≤ k) {β p₁ : ℝ} (hβ : 0 < β) (hp : 0 < p₁) :
    corrF0 T k β p₁ ≤ Ccorr T * p₁ ^ 3 / Real.sqrt (β * 3 ^ k) := by
  have hb0 : 0 < β * 3 ^ k := by positivity
  have hs : 0 < Real.sqrt (β * 3 ^ k) := Real.sqrt_pos.2 hb0
  have hsq : Real.sqrt (β * 3 ^ k) ^ 2 = β * 3 ^ k := Real.sq_sqrt hb0.le
  have ht := T.t_pos
  have hq := decMR_pos T hk hb0 hp
  have hqle := decMR_le T hk hb0 hp.le
  have hEc := Ecst_hi T (compWeight_three_mem hk).2
  have hE0 := Ecst_pos T (compWeight_three_mem hk).1
  have hK := Kmark_pos T
  have hU := corrU_pos
  have hC := covSupMaxC_nonneg T
  have hr2 := Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 2)
  have hr := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have e1 : corrF0 T k β p₁ = 256 * (β * 3 ^ k) * Ecst T (compWeight 3 1 k) * corrU ^ 2 *
      Kmark T * decMR T k (β * 3 ^ k) p₁ ^ 3 / T.t ^ 3 := by
    unfold corrF0 corrR
    rw [Estar_eq T hk, abs_of_pos hβ]
    generalize Kmark T = K
    generalize corrU = U
    generalize Ecst T (compWeight 3 1 k) = E
    generalize decMR T k (β * 3 ^ k) p₁ = q at hq
    have : (3 : ℝ) ^ k ≠ 0 := by positivity
    field_simp
    ring
  rw [e1]
  unfold Ccorr
  exact alg_main hs hsq hr hr2 ht hU hK hE0.le hEc hp hq hqle

/-- **The radius condition, uniformly in the scale**: `R ≥ 2U` for polylogarithmic `p₁`. -/
theorem exists_beta0_corrR {A₁ : ℝ} (hA : 0 < A₁) (p : ℕ) :
    ∃ β₀ : ℝ, ∀ k : ℕ, 1 ≤ k → ∀ β : ℝ, β₀ ≤ β → ∀ p₁ : ℝ, 0 < p₁ →
      p₁ ≤ pLog A₁ p (β * 3 ^ k) → 2 * corrU ≤ corrR T k (β * 3 ^ k) p₁ := by
  have ht := T.t_pos
  have hU := corrU_pos
  have hC : 0 ≤ covSupMaxC 3 3 2 T.κ := by
    have h1 := covSupConstC_le_covSupMaxC (N := 2) (d := 3) (L := 3) (by norm_num) le_rfl T.κ
      (compWeight_three_mem (k := 1) le_rfl)
    have := covMin_pos
    have := covMin_le (compWeight_three_mem (k := 1) le_rfl) T.κ
    linarith
  set c : ℝ := T.t / (8 * corrU * (Real.sqrt 2 * covSupMaxC 3 3 2 T.κ + 1)) with hc
  have hc0 : 0 < c := by
    have : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
    rw [hc]; positivity
  refine ⟨max 1 (pLogThreshold A₁ p c), fun k hk β hβ p₁ hp hp₁ => ?_⟩
  have hβ1 : 1 ≤ β := (le_max_left _ _).trans hβ
  have hβ0 : 0 < β := by linarith
  have h3 : (1 : ℝ) ≤ 3 ^ k := one_le_pow₀ (by norm_num)
  have hb1 : 1 ≤ β * 3 ^ k := by nlinarith
  have hbt : pLogThreshold A₁ p c ≤ β * 3 ^ k := by
    have := (le_max_right _ _).trans hβ
    nlinarith
  have hb0 : 0 < β * 3 ^ k := by linarith
  have hs : 0 < Real.sqrt (β * 3 ^ k) := Real.sqrt_pos.2 hb0
  have hpl := pLog_le_mul_sqrt hA.le p hc0 hb1 hbt
  have hq := decMR_pos T hk hb0 hp
  have hqle := decMR_le T hk hb0 hp.le
  have hpc : p₁ ≤ c * Real.sqrt (β * 3 ^ k) := hp₁.trans hpl
  have hr2 := Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 2)
  have hqc : decMR T k (β * 3 ^ k) p₁ ≤ Real.sqrt 2 * covSupMaxC 3 3 2 T.κ * c := by
    refine hqle.trans ?_
    have : (Real.sqrt (β * 3 ^ k))⁻¹ * p₁ ≤ c := by
      rw [inv_mul_le_iff₀ hs]; linarith
    calc Real.sqrt 2 * ((Real.sqrt (β * 3 ^ k))⁻¹ * (covSupMaxC 3 3 2 T.κ * p₁))
        = Real.sqrt 2 * covSupMaxC 3 3 2 T.κ * ((Real.sqrt (β * 3 ^ k))⁻¹ * p₁) := by ring
      _ ≤ _ := by gcongr
  have hq2 : 8 * corrU * decMR T k (β * 3 ^ k) p₁ ≤ T.t := by
    have hm : Real.sqrt 2 * covSupMaxC 3 3 2 T.κ * c ≤ T.t / (8 * corrU) := by
      rw [hc]
      have hM : 0 ≤ Real.sqrt 2 * covSupMaxC 3 3 2 T.κ := by positivity
      rw [show T.t / (8 * corrU * (Real.sqrt 2 * covSupMaxC 3 3 2 T.κ + 1)) =
        (T.t / (8 * corrU)) / (Real.sqrt 2 * covSupMaxC 3 3 2 T.κ + 1) by
        field_simp]
      rw [← mul_div_assoc, div_le_iff₀ (by positivity)]
      have : 0 ≤ T.t / (8 * corrU) := by positivity
      nlinarith
    have := mul_le_mul_of_nonneg_left (hqc.trans hm) (by positivity : 0 ≤ 8 * corrU)
    have e : 8 * corrU * (T.t / (8 * corrU)) = T.t := by field_simp
    linarith
  unfold corrR
  rw [le_div_iff₀ (by positivity)]
  nlinarith

/-- **Smallness beyond a threshold**, uniformly in the scale. -/
theorem exists_beta0_corrF0_le {ε : ℝ} (hε : 0 < ε) {A₁ : ℝ} (hA : 0 < A₁) (p : ℕ) :
    ∃ β₀ : ℝ, ∀ k : ℕ, 1 ≤ k → ∀ β : ℝ, β₀ ≤ β → ∀ p₁ : ℝ, 0 < p₁ →
      p₁ ≤ pLog A₁ p (β * 3 ^ k) → corrF0 T k β p₁ ≤ ε := by
  have hC := Ccorr_nonneg T
  set c : ℝ := ε / (Ccorr T + 1) with hc
  have hc0 : 0 < c := by rw [hc]; positivity
  refine ⟨max 1 (pLogThreshold (A₁ ^ 3) (3 * p) c), fun k hk β hβ p₁ hp hp₁ => ?_⟩
  have hβ1 : 1 ≤ β := (le_max_left _ _).trans hβ
  have hβ0 : 0 < β := by linarith
  have h3 : (1 : ℝ) ≤ 3 ^ k := one_le_pow₀ (by norm_num)
  have hb1 : 1 ≤ β * 3 ^ k := by nlinarith
  have hbt : pLogThreshold (A₁ ^ 3) (3 * p) c ≤ β * 3 ^ k := by
    have := (le_max_right _ _).trans hβ
    nlinarith
  have hb0 : 0 < β * 3 ^ k := by linarith
  have hs : 0 < Real.sqrt (β * 3 ^ k) := Real.sqrt_pos.2 hb0
  have hpl := pLog_le_mul_sqrt (by positivity : 0 ≤ A₁ ^ 3) (3 * p) hc0 hb1 hbt
  have hp3 : p₁ ^ 3 ≤ pLog (A₁ ^ 3) (3 * p) (β * 3 ^ k) := by
    have h0 : p₁ ^ 3 ≤ pLog A₁ p (β * 3 ^ k) ^ 3 := pow_le_pow_left₀ hp.le hp₁ 3
    refine h0.trans (le_of_eq ?_)
    unfold pLog
    rw [mul_pow, ← pow_mul, mul_comm p 3]
  refine (corrF0_le T hk hβ0 hp).trans ?_
  have h4 : p₁ ^ 3 ≤ c * Real.sqrt (β * 3 ^ k) := hp3.trans hpl
  have h5 : Ccorr T * p₁ ^ 3 ≤ Ccorr T * (c * Real.sqrt (β * 3 ^ k)) :=
    mul_le_mul_of_nonneg_left h4 hC
  have h6 : Ccorr T * c ≤ ε := by
    rw [hc, ← mul_div_assoc, div_le_iff₀ (by positivity)]
    nlinarith
  rw [div_le_iff₀ hs]
  nlinarith [mul_le_mul_of_nonneg_right h6 hs.le]

end Balaban.Inhabited.MarkBudgetAudit
