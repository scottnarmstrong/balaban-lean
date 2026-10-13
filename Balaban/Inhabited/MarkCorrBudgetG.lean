/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.MarkBudgetAuditG
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

/-!
# The constants of the corrected marks at the general tower

The constants of `MarkCorrBudget` for `StepTowerG d L N κmin`, with the scale variable
`b = β L^{k(d-2)}`.  The disc radius is the number `17/16` (the fixed `corrU`).  The tower
constant `Ccorr` carries the factor `256 (√N)³`, which is `512 √2` at `N = 2`.
-/

@[expose] public section

namespace Balaban.Inhabited.MarkBudgetAudit

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation
  Balaban.Localization Balaban.Localization.LevelPair Balaban.Localization.I5Inhabited
  Balaban.Polymer Balaban.SmallField.Def6 Balaban.Inhabited.LevelStep

variable {d L N : ℕ} [NeZero L] {κmin : ℝ} (T : StepTowerG d L N κmin)

/-- The Cauchy radius `T.t / (4 q)` of the corrected marks, `q = decMRG T k b p₁`. -/
noncomputable def corrRG (k : ℕ) (b p₁ : ℝ) : ℝ := T.t / (4 * decMRG T k b p₁)

/-- The per-root constant `4 |β| E_* U² J / R³` of the corrected marks, `U = 17/16`. -/
noncomputable def corrF0G (k : ℕ) (β p₁ : ℝ) : ℝ :=
  4 * |β| * EstarG T k * (17 / 16 : ℝ) ^ 2 * KmarkG T /
    (corrRG T k (β * (L : ℝ) ^ (k * (d - 2))) p₁) ^ 3

/-- The tower constant `256 (√N)³ J E_max C_max³ U² / t³`, `U = 17/16`. -/
noncomputable def CcorrG : ℝ :=
  256 * Real.sqrt N ^ 3 * KmarkG T *
    ((L : ℝ) ^ d * ((N : ℝ) / 2 * (2 * (T.t + VstarG T) ^ 2 + (d : ℝ) * VstarG T ^ 2 +
      (1 + rho4 d L N T.BG T.κ) * VstarG T ^ 2 / (L : ℝ) ^ 2))) *
    covSupMaxC d L N T.κ ^ 3 * (17 / 16 : ℝ) ^ 2 / T.t ^ 3

theorem corrRG_pos {k : ℕ} (hk : 1 ≤ k) {b p₁ : ℝ} (hb : 0 < b) (hp : 0 < p₁) :
    0 < corrRG T k b p₁ := by
  have := decMRG_pos T hk hb hp
  have := T.t_pos
  unfold corrRG; positivity

theorem two_corrRG_mul_decMRG_lt {k : ℕ} (hk : 1 ≤ k) {b p₁ : ℝ} (hb : 0 < b) (hp : 0 < p₁) :
    2 * corrRG T k b p₁ * decMRG T k b p₁ < T.t := by
  have hq := decMRG_pos T hk hb hp
  have := T.t_pos
  have : 2 * corrRG T k b p₁ * decMRG T k b p₁ = T.t / 2 := by
    unfold corrRG; field_simp; ring
  linarith

private theorem alg_mainG {b s r t U K E Em C p₁ q : ℝ} (hs : 0 < s) (hsq : s ^ 2 = b)
    (hr0 : 0 < r) (ht : 0 < t) (hU : 0 < U) (hK : 0 < K) (hE : 0 ≤ E)
    (hEm : E ≤ Em) (hp : 0 < p₁) (hq : 0 < q)
    (hqle : q ≤ r * (s⁻¹ * (C * p₁))) :
    256 * b * E * U ^ 2 * K * q ^ 3 / t ^ 3 ≤
      256 * r ^ 3 * K * Em * C ^ 3 * U ^ 2 / t ^ 3 * p₁ ^ 3 / s := by
  subst hsq
  have h1 : q ^ 3 ≤ (r * (s⁻¹ * (C * p₁))) ^ 3 := pow_le_pow_left₀ hq.le hqle 3
  have hEm0 : 0 ≤ Em := hE.trans hEm
  have h2 : 256 * s ^ 2 * E * U ^ 2 * K * q ^ 3 ≤
      256 * s ^ 2 * Em * U ^ 2 * K * (r * (s⁻¹ * (C * p₁))) ^ 3 := by
    have : 0 ≤ q ^ 3 := by positivity
    gcongr
  have h3 : 256 * s ^ 2 * Em * U ^ 2 * K * (r * (s⁻¹ * (C * p₁))) ^ 3 / t ^ 3 =
      256 * r ^ 3 * K * Em * C ^ 3 * U ^ 2 / t ^ 3 * p₁ ^ 3 / s := by
    have : (r * (s⁻¹ * (C * p₁))) ^ 3 = r ^ 3 * (s⁻¹) ^ 3 * C ^ 3 * p₁ ^ 3 := by ring
    rw [this]
    field_simp
  calc _ ≤ 256 * s ^ 2 * Em * U ^ 2 * K * (r * (s⁻¹ * (C * p₁))) ^ 3 / t ^ 3 :=
        div_le_div_of_nonneg_right h2 (by positivity)
    _ = _ := h3

theorem covSupMaxC_nonnegG : 0 ≤ covSupMaxC d L N T.κ :=
  covSupMaxC_nonneg_general (by have := T.hd; omega) T.hL T.κ

theorem CcorrG_nonneg : 0 ≤ CcorrG T := by
  have hK := KmarkG_pos T
  have h1 := T.rho_nonneg
  have h2 := VstarG_nonneg T
  have ht := T.t_pos
  have hC := covSupMaxC_nonnegG T
  have hL := LposG T
  have hN := NposG T
  unfold CcorrG
  generalize KmarkG T = K at hK ⊢
  generalize covSupMaxC d L N T.κ = C at hC ⊢
  generalize VstarG T = V at h2 ⊢
  generalize rho4 d L N T.BG T.κ = ρ at h1 ⊢
  have := Real.sqrt_nonneg (N : ℝ)
  positivity

/-- **The size**: `F₀^corr ≤ Ccorr · p₁³ / √(β L^{k(d-2)})`. -/
theorem corrF0_leG {k : ℕ} (hk : 1 ≤ k) {β p₁ : ℝ} (hβ : 0 < β) (hp : 0 < p₁) :
    corrF0G T k β p₁ ≤ CcorrG T * p₁ ^ 3 / Real.sqrt (β * (L : ℝ) ^ (k * (d - 2))) := by
  have hLs := scalePosG T k
  have hb0 : 0 < β * (L : ℝ) ^ (k * (d - 2)) := by positivity
  have hs : 0 < Real.sqrt (β * (L : ℝ) ^ (k * (d - 2))) := Real.sqrt_pos.2 hb0
  have hsq : Real.sqrt (β * (L : ℝ) ^ (k * (d - 2))) ^ 2 = β * (L : ℝ) ^ (k * (d - 2)) :=
    Real.sq_sqrt hb0.le
  have ht := T.t_pos
  have hq := decMRG_pos T hk hb0 hp
  have hqle := decMRG_le T hk hb0 hp.le
  have hEc := EcstG_hi T (compWeightG_mem T hk).2
  have hE0 := EcstG_pos T (compWeightG_mem T hk).1
  have hK := KmarkG_pos T
  have hU : (0 : ℝ) < 17 / 16 := by norm_num
  have hC := covSupMaxC_nonnegG T
  have hr2 : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.2 (NposG T)
  have e1 : corrF0G T k β p₁ = 256 * (β * (L : ℝ) ^ (k * (d - 2))) *
      EcstG T (compWeight L 1 k) * (17 / 16 : ℝ) ^ 2 *
      KmarkG T * decMRG T k (β * (L : ℝ) ^ (k * (d - 2))) p₁ ^ 3 / T.t ^ 3 := by
    unfold corrF0G corrRG
    rw [EstarG_eq T (compWeightG_mem T hk), abs_of_pos hβ]
    generalize KmarkG T = K
    generalize EcstG T (compWeight L 1 k) = E
    generalize decMRG T k (β * (L : ℝ) ^ (k * (d - 2))) p₁ = q at hq
    have : (L : ℝ) ^ (k * (d - 2)) ≠ 0 := hLs.ne'
    field_simp
    ring
  rw [e1]
  unfold CcorrG
  exact alg_mainG hs hsq hr2 ht hU hK hE0.le hEc hp hq hqle

/-- **The radius condition, uniformly in the scale**: `R ≥ 2U` for polylogarithmic `p₁`. -/
theorem exists_beta0_corrRG {A₁ : ℝ} (hA : 0 < A₁) (p : ℕ) :
    ∃ β₀ : ℝ, ∀ k : ℕ, 1 ≤ k → ∀ β : ℝ, β₀ ≤ β → ∀ p₁ : ℝ, 0 < p₁ →
      p₁ ≤ pLog A₁ p (β * (L : ℝ) ^ (k * (d - 2))) →
      2 * (17 / 16 : ℝ) ≤ corrRG T k (β * (L : ℝ) ^ (k * (d - 2))) p₁ := by
  have ht := T.t_pos
  have hU : (0 : ℝ) < 17 / 16 := by norm_num
  have hC := covSupMaxC_nonnegG T
  have hN := NposG T
  set c : ℝ := T.t / (8 * (17 / 16 : ℝ) * (Real.sqrt N * covSupMaxC d L N T.κ + 1)) with hc
  have hc0 : 0 < c := by
    have : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.2 hN
    rw [hc]; positivity
  refine ⟨max 1 (pLogThreshold A₁ p c), fun k hk β hβ p₁ hp hp₁ => ?_⟩
  have hLge : (1 : ℝ) ≤ (L : ℝ) ^ (k * (d - 2)) :=
    one_le_pow₀ (by have := T.hL; exact_mod_cast (by omega : 1 ≤ L))
  have hβ1 : 1 ≤ β := (le_max_left _ _).trans hβ
  have hβ0 : 0 < β := by linarith
  have hb1 : 1 ≤ β * (L : ℝ) ^ (k * (d - 2)) := by nlinarith
  have hbt : pLogThreshold A₁ p c ≤ β * (L : ℝ) ^ (k * (d - 2)) := by
    have := (le_max_right _ _).trans hβ
    nlinarith
  have hb0 : 0 < β * (L : ℝ) ^ (k * (d - 2)) := by linarith
  have hs : 0 < Real.sqrt (β * (L : ℝ) ^ (k * (d - 2))) := Real.sqrt_pos.2 hb0
  have hpl := pLog_le_mul_sqrt hA.le p hc0 hb1 hbt
  have hq := decMRG_pos T hk hb0 hp
  have hqle := decMRG_le T hk hb0 hp.le
  have hpc : p₁ ≤ c * Real.sqrt (β * (L : ℝ) ^ (k * (d - 2))) := hp₁.trans hpl
  have hr2 : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.2 hN
  have hqc : decMRG T k (β * (L : ℝ) ^ (k * (d - 2))) p₁ ≤
      Real.sqrt N * covSupMaxC d L N T.κ * c := by
    refine hqle.trans ?_
    have : (Real.sqrt (β * (L : ℝ) ^ (k * (d - 2))))⁻¹ * p₁ ≤ c := by
      rw [inv_mul_le_iff₀ hs]; linarith
    calc Real.sqrt N * ((Real.sqrt (β * (L : ℝ) ^ (k * (d - 2))))⁻¹ * (covSupMaxC d L N T.κ * p₁))
        = Real.sqrt N * covSupMaxC d L N T.κ *
            ((Real.sqrt (β * (L : ℝ) ^ (k * (d - 2))))⁻¹ * p₁) := by ring
      _ ≤ _ := by gcongr
  have hq2 : 8 * (17 / 16 : ℝ) * decMRG T k (β * (L : ℝ) ^ (k * (d - 2))) p₁ ≤ T.t := by
    have hm : Real.sqrt N * covSupMaxC d L N T.κ * c ≤ T.t / (8 * (17 / 16 : ℝ)) := by
      rw [hc]
      have hM : 0 ≤ Real.sqrt (N : ℝ) * covSupMaxC d L N T.κ := by positivity
      rw [show T.t / (8 * (17 / 16 : ℝ) * (Real.sqrt N * covSupMaxC d L N T.κ + 1)) =
        (T.t / (8 * (17 / 16 : ℝ))) / (Real.sqrt N * covSupMaxC d L N T.κ + 1) by
        field_simp]
      rw [← mul_div_assoc, div_le_iff₀ (by positivity)]
      have : 0 ≤ T.t / (8 * (17 / 16 : ℝ)) := by positivity
      nlinarith
    have := mul_le_mul_of_nonneg_left (hqc.trans hm) (by positivity : 0 ≤ 8 * (17 / 16 : ℝ))
    have e : 8 * (17 / 16 : ℝ) * (T.t / (8 * (17 / 16 : ℝ))) = T.t := by field_simp
    linarith
  unfold corrRG
  rw [le_div_iff₀ (by positivity)]
  nlinarith

/-- **Smallness beyond a threshold**, uniformly in the scale. -/
theorem exists_beta0_corrF0_leG {ε : ℝ} (hε : 0 < ε) {A₁ : ℝ} (hA : 0 < A₁) (p : ℕ) :
    ∃ β₀ : ℝ, ∀ k : ℕ, 1 ≤ k → ∀ β : ℝ, β₀ ≤ β → ∀ p₁ : ℝ, 0 < p₁ →
      p₁ ≤ pLog A₁ p (β * (L : ℝ) ^ (k * (d - 2))) → corrF0G T k β p₁ ≤ ε := by
  have hC := CcorrG_nonneg T
  set c : ℝ := ε / (CcorrG T + 1) with hc
  have hc0 : 0 < c := by rw [hc]; positivity
  refine ⟨max 1 (pLogThreshold (A₁ ^ 3) (3 * p) c), fun k hk β hβ p₁ hp hp₁ => ?_⟩
  have hLge : (1 : ℝ) ≤ (L : ℝ) ^ (k * (d - 2)) :=
    one_le_pow₀ (by have := T.hL; exact_mod_cast (by omega : 1 ≤ L))
  have hβ1 : 1 ≤ β := (le_max_left _ _).trans hβ
  have hβ0 : 0 < β := by linarith
  have hb1 : 1 ≤ β * (L : ℝ) ^ (k * (d - 2)) := by nlinarith
  have hbt : pLogThreshold (A₁ ^ 3) (3 * p) c ≤ β * (L : ℝ) ^ (k * (d - 2)) := by
    have := (le_max_right _ _).trans hβ
    nlinarith
  have hb0 : 0 < β * (L : ℝ) ^ (k * (d - 2)) := by linarith
  have hs : 0 < Real.sqrt (β * (L : ℝ) ^ (k * (d - 2))) := Real.sqrt_pos.2 hb0
  have hpl := pLog_le_mul_sqrt (by positivity : 0 ≤ A₁ ^ 3) (3 * p) hc0 hb1 hbt
  have hp3 : p₁ ^ 3 ≤ pLog (A₁ ^ 3) (3 * p) (β * (L : ℝ) ^ (k * (d - 2))) := by
    have h0 : p₁ ^ 3 ≤ pLog A₁ p (β * (L : ℝ) ^ (k * (d - 2))) ^ 3 := pow_le_pow_left₀ hp.le hp₁ 3
    refine h0.trans (le_of_eq ?_)
    unfold pLog
    rw [mul_pow, ← pow_mul, mul_comm p 3]
  refine (corrF0_leG T hk hβ0 hp).trans ?_
  have h4 : p₁ ^ 3 ≤ c * Real.sqrt (β * (L : ℝ) ^ (k * (d - 2))) := hp3.trans hpl
  have h5 : CcorrG T * p₁ ^ 3 ≤ CcorrG T * (c * Real.sqrt (β * (L : ℝ) ^ (k * (d - 2)))) :=
    mul_le_mul_of_nonneg_left h4 hC
  have h6 : CcorrG T * c ≤ ε := by
    rw [hc, ← mul_div_assoc, div_le_iff₀ (by positivity)]
    nlinarith
  rw [div_le_iff₀ hs]
  nlinarith [mul_le_mul_of_nonneg_right h6 hs.le]

end Balaban.Inhabited.MarkBudgetAudit
