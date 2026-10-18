/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.MarkCorrBudgetG
public import Balaban.Inhabited.MarkCorrBudgetTMargin
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

/-!
# The corrected marks at the step radius `t`: the threshold is `t^{-2} (log b)^{2p}`

The tower constant `CcorrG` of the corrected marks is `M / t`, with `M` free of `t`: the energy
bound `E_*` is quadratic in the step radius (`E_* ≍ (t + V_*)² + V_*²`, `V_* = K t`), and the three
Cauchy factors `1/R³`, `R = t/(4 q)`, are paid by the `t²` of `E_*`.  So the budget
`F₀^corr ≤ 1/(C_PE + 1)` needs `p₁³ ≲ t √b`, the same order `b ≳ t^{-2} (log b)^{6p}` as the other
providers; with `t_k ≥ c L^{-α(k+1)}`, `b = β L^{k(d-2)}` and `2 α < d - 2` one `β₀` works for
every scale.

* `CcorrG_mul_t`: `CcorrG T * T.t` is the explicit `t`-free number;
* `CcorrG_mul_t_eq`: it is the same for towers that agree except for `t`;
* `exists_beta0_corrF0_leT`: smallness of `corrF0G` beyond one threshold, for all towers with
  `CcorrG * t ≤ M` and radii `t ≥ c L^{-α(k+1)}`;
* `exists_beta0_corrRT`: the radius condition `2 U ≤ corrRG` in the same form.
-/

@[expose] public section

namespace Balaban.Inhabited.MarkBudgetAudit

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation
  Balaban.Localization Balaban.Localization.LevelPair Balaban.Localization.I5Inhabited
  Balaban.Polymer Balaban.SmallField.Def6 Balaban.Inhabited.LevelStep Balaban.Inhabited

variable {d L N : ℕ} [NeZero L] {κmin : ℝ}

/-- **`CcorrG · t` does not depend on `t`.**  Here `Q = cK2' (famConst BG₂ κ)` is the ratio
`V_* / t`. -/
theorem CcorrG_mul_t (T : StepTowerG d L N κmin) :
    CcorrG T * T.t =
      256 * Real.sqrt N ^ 3 * KmarkG T *
        ((L : ℝ) ^ d * ((N : ℝ) / 2 * (2 * (1 + cK2' d L N (famConst d L T.BG₂ T.κ)) ^ 2 +
          (d : ℝ) * cK2' d L N (famConst d L T.BG₂ T.κ) ^ 2 +
          (1 + rho4 d L N T.BG T.κ) * cK2' d L N (famConst d L T.BG₂ T.κ) ^ 2 / (L : ℝ) ^ 2))) *
        covSupMaxC d L N T.κ ^ 3 * (17 / 16 : ℝ) ^ 2 := by
  have ht := T.t_pos
  unfold CcorrG VstarG
  field_simp

/-- **Towers that agree except for `t` have the same `CcorrG · t`.** -/
theorem CcorrG_mul_t_eq (T T' : StepTowerG d L N κmin) (hBG : T'.BG = T.BG)
    (hBG₂ : T'.BG₂ = T.BG₂) (hκ : T'.κ = T.κ) (hκdec : T'.κdec = T.κdec)
    (hm₁ : T'.m₁ = T.m₁) : CcorrG T' * T'.t = CcorrG T * T.t := by
  have ht := T.t_pos
  have ht' := T'.t_pos
  have h1 := CcorrG_mul_t T
  have h2 := CcorrG_mul_t T'
  have hK : KmarkG T' = KmarkG T := by unfold KmarkG; rw [hκdec, hm₁]
  rw [h1, h2, hBG, hBG₂, hκ, hK]

omit [NeZero L] in
/-- The scale `L^{k(d-2)}` as the `k`-th power of the base `Λ = L^{d-2}`. -/
private theorem scaleB_eq (k : ℕ) :
    (L : ℝ) ^ (k * (d - 2)) = ((L : ℝ) ^ (d - 2)) ^ k := by
  rw [mul_comm, pow_mul]

omit [NeZero L] in
/-- The radius `L^{-α(k+1)}` as a power of the base `Λ = L^{d-2}` with exponent `α/(d-2)`. -/
private theorem radiusB_eq (hL : 3 ≤ L) (hd : 3 ≤ d) (α : ℝ) (k : ℕ) :
    (L : ℝ) ^ (-(α * ((k : ℝ) + 1))) =
      ((L : ℝ) ^ (d - 2)) ^ (-((α / ((d - 2 : ℕ) : ℝ)) * ((k : ℝ) + 1))) := by
  have hL0 : (0 : ℝ) < L := by exact_mod_cast (by omega : 0 < L)
  have hd0 : ((d - 2 : ℕ) : ℝ) ≠ 0 := by
    have : 0 < d - 2 := by omega
    exact_mod_cast this.ne'
  rw [← Real.rpow_natCast (L : ℝ) (d - 2), ← Real.rpow_mul hL0.le]
  congr 1
  field_simp

omit [NeZero L] in
private theorem baseB_gt (hL : 3 ≤ L) (hd : 3 ≤ d) : (1 : ℝ) < (L : ℝ) ^ (d - 2) :=
  one_lt_pow₀ (by exact_mod_cast (by omega : 1 < L)) (by omega)

private theorem rateB_lt (hd : 3 ≤ d) {α : ℝ} (hα : 2 * α < ((d - 2 : ℕ) : ℝ)) :
    1 * (α / ((d - 2 : ℕ) : ℝ)) < 1 / 2 := by
  have hd0 : (0 : ℝ) < ((d - 2 : ℕ) : ℝ) := by
    have : 0 < d - 2 := by omega
    exact_mod_cast this
  rw [one_mul, div_lt_iff₀ hd0]
  linarith

/-- **Smallness of `F₀^corr` beyond one threshold, at every scale and every step radius
`t ≥ c L^{-α (k+1)}`.**  The threshold depends on `ε, A₁, p, M, c, α` only; the towers are
arbitrary with `CcorrG T' * T'.t ≤ M` (for example all towers that agree with a given one except
for `t`, by `CcorrG_mul_t_eq`).  Here `2 α < d - 2`. -/
theorem exists_beta0_corrF0_leT (hd : 3 ≤ d) (hL : 3 ≤ L) {ε : ℝ} (hε : 0 < ε) {A₁ : ℝ}
    (hA : 0 ≤ A₁) (p : ℕ) {M c α : ℝ} (hM : 0 ≤ M) (hc : 0 < c)
    (hα : 2 * α < ((d - 2 : ℕ) : ℝ)) :
    ∃ β₀ : ℝ, 3 ≤ β₀ ∧ ∀ (T : StepTowerG d L N κmin) (k : ℕ), 1 ≤ k → ∀ β p₁ : ℝ, β₀ ≤ β →
      0 < p₁ → p₁ ≤ pLog A₁ p (β * (L : ℝ) ^ (k * (d - 2))) → CcorrG T * T.t ≤ M →
      c * (L : ℝ) ^ (-(α * ((k : ℝ) + 1))) ≤ T.t → corrF0G T k β p₁ ≤ ε := by
  obtain ⟨β₀, h3, H⟩ := exists_beta0_marginB_pLog (Λ := (L : ℝ) ^ (d - 2)) (a := 1) (s := 1 / 2)
    (α := α / ((d - 2 : ℕ) : ℝ)) (c := c) (C := M / ε) (A₁ := A₁) p 3 (baseB_gt hL hd) hc
    zero_le_one (by norm_num) (rateB_lt hd hα) (by positivity) hA
  refine ⟨β₀, h3, fun T k hk β p₁ hβ hp hp₁ hCt hct => ?_⟩
  have hβ0 : 0 < β := by linarith
  have hLs := scalePosG T k
  have hb0 : 0 < β * (L : ℝ) ^ (k * (d - 2)) := by positivity
  have hs : 0 < Real.sqrt (β * (L : ℝ) ^ (k * (d - 2))) := Real.sqrt_pos.2 hb0
  have ht := T.t_pos
  have hmar := H k β T.t p₁ hβ (by rw [← radiusB_eq hL hd α k]; exact hct) hp
    (by rw [← scaleB_eq k]; exact hp₁)
  rw [← scaleB_eq k, Real.rpow_one, ← Real.sqrt_eq_rpow] at hmar
  have hC0 := CcorrG_nonneg T
  have hCle : CcorrG T ≤ M / T.t := by rw [le_div_iff₀ ht]; exact hCt
  refine (corrF0_leG T hk hβ0 hp).trans ?_
  rw [div_le_iff₀ hs]
  have h1 : M / ε * p₁ ^ 3 ≤ T.t * Real.sqrt (β * (L : ℝ) ^ (k * (d - 2))) := hmar
  have h2 : M * p₁ ^ 3 ≤ ε * (T.t * Real.sqrt (β * (L : ℝ) ^ (k * (d - 2)))) := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hε] at h1
    linarith
  calc CcorrG T * p₁ ^ 3 ≤ M / T.t * p₁ ^ 3 := by gcongr
    _ = M * p₁ ^ 3 / T.t := by ring
    _ ≤ ε * Real.sqrt (β * (L : ℝ) ^ (k * (d - 2))) := by
        rw [div_le_iff₀ ht]; nlinarith

/-- **The radius condition `2 U ≤ R` of the corrected marks beyond one threshold, at every scale
and every step radius `t ≥ c L^{-α (k+1)}`**, for towers with `C_max(κ) ≤ Cc`.  Here
`2 α < d - 2`. -/
theorem exists_beta0_corrRT (hd : 3 ≤ d) (hL : 3 ≤ L) {A₁ : ℝ} (hA : 0 ≤ A₁) (p : ℕ)
    {Cc c α : ℝ} (hCc : 0 ≤ Cc) (hc : 0 < c) (hα : 2 * α < ((d - 2 : ℕ) : ℝ)) :
    ∃ β₀ : ℝ, 3 ≤ β₀ ∧ ∀ (T : StepTowerG d L N κmin) (k : ℕ), 1 ≤ k → ∀ β p₁ : ℝ, β₀ ≤ β →
      0 < p₁ → p₁ ≤ pLog A₁ p (β * (L : ℝ) ^ (k * (d - 2))) → covSupMaxC d L N T.κ ≤ Cc →
      c * (L : ℝ) ^ (-(α * ((k : ℝ) + 1))) ≤ T.t →
      2 * (17 / 16 : ℝ) ≤ corrRG T (k := k) (β * (L : ℝ) ^ (k * (d - 2))) p₁ := by
  obtain ⟨β₀, h3, H⟩ := exists_beta0_marginB_pLog (Λ := (L : ℝ) ^ (d - 2)) (a := 1) (s := 1 / 2)
    (α := α / ((d - 2 : ℕ) : ℝ)) (c := c) (C := 8 * (17 / 16 : ℝ) * (Real.sqrt N * Cc))
    (A₁ := A₁) p 1 (baseB_gt hL hd) hc zero_le_one (by norm_num) (rateB_lt hd hα)
    (by positivity) hA
  refine ⟨β₀, h3, fun T k hk β p₁ hβ hp hp₁ hCmax hct => ?_⟩
  have hβ0 : 0 < β := by linarith
  have hLs := scalePosG T k
  have hb0 : 0 < β * (L : ℝ) ^ (k * (d - 2)) := by positivity
  have hs : 0 < Real.sqrt (β * (L : ℝ) ^ (k * (d - 2))) := Real.sqrt_pos.2 hb0
  have ht := T.t_pos
  have hmar := H k β T.t p₁ hβ (by rw [← radiusB_eq hL hd α k]; exact hct) hp
    (by rw [← scaleB_eq k]; exact hp₁)
  rw [← scaleB_eq k, Real.rpow_one, ← Real.sqrt_eq_rpow, pow_one] at hmar
  have hq := decMRG_pos T hk hb0 hp
  have hqle := decMRG_le T hk hb0 hp.le
  have hr2 : 0 ≤ Real.sqrt (N : ℝ) := Real.sqrt_nonneg _
  have hq2 : decMRG T k (β * (L : ℝ) ^ (k * (d - 2))) p₁ ≤
      Real.sqrt N * ((Real.sqrt (β * (L : ℝ) ^ (k * (d - 2))))⁻¹ * (Cc * p₁)) := by
    refine hqle.trans ?_
    gcongr
  have h8 : 8 * (17 / 16 : ℝ) * decMRG T k (β * (L : ℝ) ^ (k * (d - 2))) p₁ ≤ T.t := by
    have h1 : 8 * (17 / 16 : ℝ) * decMRG T k (β * (L : ℝ) ^ (k * (d - 2))) p₁ ≤
        8 * (17 / 16 : ℝ) * (Real.sqrt N * ((Real.sqrt (β * (L : ℝ) ^ (k * (d - 2))))⁻¹ *
          (Cc * p₁))) := by gcongr
    refine h1.trans ?_
    have e : 8 * (17 / 16 : ℝ) * (Real.sqrt N * ((Real.sqrt (β * (L : ℝ) ^ (k * (d - 2))))⁻¹ *
          (Cc * p₁))) = 8 * (17 / 16 : ℝ) * (Real.sqrt N * Cc) * p₁ /
          Real.sqrt (β * (L : ℝ) ^ (k * (d - 2))) := by
      field_simp
    rw [e, div_le_iff₀ hs]
    linarith
  unfold corrRG
  rw [le_div_iff₀ (by positivity)]
  nlinarith

end Balaban.Inhabited.MarkBudgetAudit
