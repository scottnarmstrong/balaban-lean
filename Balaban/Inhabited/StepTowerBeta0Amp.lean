/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.StepTowerBeta0Marks
public import Balaban.Inhabited.StepTowerChainStructAmp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp

/-!
# The source amplitude at a physical source, uniformly in the step radius

`sourceAmp_scale_general_agree`: the statement of `sourceAmp_scale_general` with the radius `t` a
variable after the threshold (`t ≥ c L^{-α(k+1)}`, `2 α < d - 2`; the cutoff condition is
`p₁ ≤ (κ₁/16) √b` with `κ₁ ∝ t`).  `StepTower.exists_beta0_amp_agree`: the first entry of the
numerical condition of the composed activity, for towers that agree with `T₀` on `m₁, BG, BG₂, κ`.
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation
  Balaban.Localization Balaban.Localization.I5Inhabited Balaban.Inhabited.LevelStep
  Balaban.Inhabited.MarkBudgetAudit

namespace LevelStep

/-- **The amplitude at a physical source at every scale, uniformly in the step radius.** -/
theorem sourceAmp_scale_general_agree {d L N : ℕ} (hd : 3 ≤ d) (hL : 3 ≤ L) (hN : 1 ≤ N)
    {A₁ κ : ℝ} (hA : 0 < A₁) (p : ℕ) {c α : ℝ} (hc : 0 < c)
    (hα : 2 * α < ((d - 2 : ℕ) : ℝ)) :
    ∃ β₁ : ℝ, 3 ≤ β₁ ∧ ∀ (k : ℕ) (β t b : ℝ), b = β * (L : ℝ) ^ (k * (d - 2)) → β₁ ≤ β →
      c * (L : ℝ) ^ (-(α * ((k : ℝ) + 1))) ≤ t → ∀ p₁ : ℝ, 0 < p₁ → p₁ ≤ pLog A₁ p b →
      0 < lvRG d L N κ t b p₁ ∧ ∀ P K q : ℝ, 0 ≤ P → 0 ≤ K → 0 ≤ q →
        b * (P / (lvRG d L N κ t b p₁) ^ 3) + q * K / lvRG d L N κ t b p₁ ≤
          P * (4 * A₁ / lvKappaG d L N κ t) ^ 3 * (Real.log b) ^ (3 * p) / Real.sqrt b +
          q * (4 * A₁ * K / lvKappaG d L N κ t) * (Real.log b) ^ p / Real.sqrt b := by
  have hd0 : 0 < d := by omega
  have hs : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hN)
  have hCm := covSupMaxC_nonneg_general (N := N) hd0 hL κ
  set κ₀ : ℝ := 1 / (2 * Real.sqrt (N : ℝ) * (covSupMaxC d L N κ + 1)) with hκ₀
  have hκ₀0 : 0 < κ₀ := by rw [hκ₀]; positivity
  obtain ⟨β₂, hβ₂, H⟩ := exists_beta0_pLog_le_t_sqrt hd hL hA.le p hc (c' := κ₀ / 16) (by positivity)
    hα
  refine ⟨β₂, hβ₂, ?_⟩
  intro k β t b hb hβ hct p₁ hp0 hp₁
  have ht : 0 < t := lt_of_lt_of_le (by positivity) hct
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast (by omega : 1 ≤ L)
  have h3k : (1 : ℝ) ≤ (L : ℝ) ^ (k * (d - 2)) := one_le_pow₀ hL1
  have hβ3 : 3 ≤ β := by linarith
  have hbβ : β ≤ b := by rw [hb]; nlinarith
  have hexp : Real.exp 1 ≤ b := by
    have := Real.exp_one_lt_three
    linarith
  have hb1 : 1 ≤ b := by linarith
  have hb0 : 0 < b := by linarith
  set κ₁ : ℝ := lvKappaG d L N κ t with hκ₁def
  have hκ₁t : κ₁ = κ₀ * t := by rw [hκ₁def, hκ₀]; unfold lvKappaG; field_simp
  have hκ₁ : 0 < κ₁ := by rw [hκ₁t]; positivity
  have hℓ : 1 ≤ Real.log b := (Real.le_log_iff_exp_le hb0).2 hexp
  have hx1 : 1 ≤ Real.sqrt b := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt hb1
  have hw1 : 1 ≤ (Real.log b) ^ p := one_le_pow₀ hℓ
  have hpL : pLog A₁ p b = A₁ * (Real.log b) ^ p := rfl
  have hp16 : p₁ ≤ κ₁ / 16 * Real.sqrt b := by
    have := H k β t p₁ (by linarith) hct hp0 (by rw [← hb]; exact hp₁)
    rw [hκ₁t, ← hb] at *
    calc p₁ ≤ κ₀ / 16 * t * Real.sqrt b := this
      _ = κ₀ * t / 16 * Real.sqrt b := by ring
  have hcψeq : lvCpsiG d L N κ t b = κ₁ * Real.sqrt b := lvCpsiG_eq d L N κ t b
  have hc16 : 16 * p₁ ≤ lvCpsiG d L N κ t b := by rw [hcψeq]; linarith
  have e : 4 * p₁ * lvRG d L N κ t b p₁ = 2 * lvCpsiG d L N κ t b - 16 * p₁ := by
    unfold lvRG; field_simp; ring
  have hcψ0 : 0 < lvCpsiG d L N κ t b := by rw [hcψeq]; positivity
  have hr0 : 0 < lvRG d L N κ t b p₁ := by
    by_contra h
    have h := not_lt.1 h
    have : 4 * p₁ * lvRG d L N κ t b p₁ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by positivity) h
    linarith
  have hrbound : κ₁ * Real.sqrt b ≤ 4 * A₁ * (Real.log b) ^ p * lvRG d L N κ t b p₁ := by
    calc κ₁ * Real.sqrt b = lvCpsiG d L N κ t b := hcψeq.symm
      _ ≤ 2 * lvCpsiG d L N κ t b - 16 * p₁ := by linarith
      _ = 4 * p₁ * lvRG d L N κ t b p₁ := e.symm
      _ ≤ 4 * pLog A₁ p b * lvRG d L N κ t b p₁ :=
        mul_le_mul_of_nonneg_right (by linarith) hr0.le
      _ = _ := by rw [hpL]; ring
  refine ⟨hr0, fun P K q hP hK hq => ?_⟩
  have hamp := sourceAmp_le (x := Real.sqrt b) (w := (Real.log b) ^ p)
    (r := lvRG d L N κ t b p₁) (P := P) (K := K) (A := A₁) (κ₁ := κ₁) (q := q) hx1 hw1 hA hκ₁
    hP hK hq hrbound
  rwa [Real.sq_sqrt hb0.le, ← pow_mul, show p * 3 = 3 * p by ring] at hamp

end LevelStep

/-- **The amplitude of the step at the source slice `q = 1` is small, uniformly in the scale and
the step radius.**  For towers `T` that agree with `T₀` on `m₁, BG, BG₂, κ` and every radius
`t ≥ c 3^{-α(k+1)}`, `2 α < 1`. -/
theorem StepTower.exists_beta0_amp_agree {κmin : ℝ} (T₀ : StepTower κmin) {A₁ : ℝ} (hA : 0 < A₁)
    (p : ℕ) {Kc' : ℝ} (hKc : 0 < Kc') {c α : ℝ} (hc : 0 < c) (hα : 2 * α < 1) :
    ∃ β₀ : ℝ, 3 ≤ β₀ ∧ ∀ T : StepTower κmin, T.m₁ = T₀.m₁ → T.BG = T₀.BG → T.BG₂ = T₀.BG₂ →
      T.κ = T₀.κ → ∀ k : ℕ, 1 ≤ k → ∀ β : ℝ, β₀ ≤ β →
      c * (3 : ℝ) ^ (-(α * ((k : ℝ) + 1))) ≤ T.t → ∀ p₁ : ℝ, 0 < p₁ →
      p₁ ≤ pLog A₁ p (β * 3 ^ k) →
      2 ^ 2 * (2 * (β * prop33EpsEtaScaled 3 3 2 T.m₁ k 1 1 T.BG T.BG₂ T.κ T.t
        (lvR T.κ T.t (β * 3 ^ k) p₁) 0 0 (1 / β))) ≤
      1 / (8 * (2 * Kc') ^ 3 * c1 3 3 *
        Real.exp ((2 * T.κdec - 1 - 2 * T.κ0) * cG 3 3 + c1 3 3 + T.κ' * cG 3 3)) := by
  have hc1 := one_le_c1 3 3
  obtain ⟨Q₀, hQ₀def⟩ : ∃ Q : ℝ, Q = cK2' 3 3 2 (famConst 3 3 T₀.BG₂ T₀.κ) := ⟨_, rfl⟩
  have hQ₀0 : 0 < Q₀ := by rw [hQ₀def]; exact cK2'_pos' T₀.fam_nonneg
  obtain ⟨Pc, hPcdef⟩ : ∃ Pc : ℝ, Pc = 3 * c1 3 3 * (((3 : ℕ) : ℝ) ^ (1 + T₀.m₁)) ^ 3 *
    (((3 : ℕ) : ℝ) ^ 3 * ((((2 : ℕ) : ℝ) / 2) * (2 * (1 + Q₀) ^ 2 +
      (((3 : ℕ) : ℝ) + 1 + rho4 3 3 2 T₀.BG T₀.κ) * Q₀ ^ 2))) := ⟨_, rfl⟩
  have hρ₀ := T₀.rho_nonneg
  have hPc0 : 0 ≤ Pc := by rw [hPcdef]; positivity
  have hs2 : 0 < Real.sqrt ((2 : ℕ) : ℝ) := Real.sqrt_pos.2 (by norm_num)
  have hCm := covSupMaxC_nonneg_general (N := 2) (d := 3) (L := 3) (by norm_num) le_rfl T₀.κ
  obtain ⟨κ₀, hκ₀def⟩ : ∃ κ₀ : ℝ, κ₀ = 1 / (2 * Real.sqrt ((2 : ℕ) : ℝ) *
    (covSupMaxC 3 3 2 T₀.κ + 1)) := ⟨_, rfl⟩
  have hκ₀0 : 0 < κ₀ := by rw [hκ₀def]; positivity
  have hdaT := daT_pos 3 3 (by norm_num : (0 : ℝ) < 4) (by positivity : 0 < 2 * Kc') T₀.κdec T₀.κ0
    T₀.κ'
  obtain ⟨β₁, hβ₁, hA'⟩ := LevelStep.sourceAmp_scale_general_agree (d := 3) (L := 3) (N := 2)
    (by norm_num) le_rfl (by norm_num) (A₁ := A₁) (κ := T₀.κ) hA p hc (alpha_three_cast hα)
  obtain ⟨β₂, hβ₂, hinv⟩ := exists_beta0_inv_t_le (d := 3) (L := 3) (by norm_num) le_rfl
    (M₁ := 2 * Pc * (4 * A₁ / κ₀) ^ 3) (M₂ := 8 * A₁ * Q₀ / κ₀)
    (η := daT 3 3 4 (2 * Kc') T₀.κdec T₀.κ0 T₀.κ') (c := c) (α := α)
    (3 * p) (by positivity) (by positivity) hdaT hc (alpha_three_cast hα)
  refine ⟨max β₁ β₂, hβ₁.trans (le_max_left _ _), ?_⟩
  intro T hm₁ hBG hBG₂ hκ k hk β hβ hct p₁ hp0 hp₁
  obtain ⟨h0, hdec, h'⟩ := StepTower.agree_rates T₀ T
  have hβ₁' : β₁ ≤ β := (le_max_left _ _).trans hβ
  have hβ₂' : β₂ ≤ β := (le_max_right _ _).trans hβ
  have hβ3 : 3 ≤ β := hβ₁.trans hβ₁'
  have ht0 := T.t_pos
  have hρ4 := T.rho_nonneg
  have hQ : cK2' 3 3 2 (famConst 3 3 T.BG₂ T.κ) = Q₀ := by rw [hQ₀def, hBG₂, hκ]
  have hQT0 : 0 < cK2' 3 3 2 (famConst 3 3 T.BG₂ T.κ) := by rw [hQ]; exact hQ₀0
  obtain ⟨Q, hQdef⟩ : ∃ Q : ℝ, Q = cK2' 3 3 2 (famConst 3 3 T.BG₂ T.κ) := ⟨_, rfl⟩
  have hQQ : Q = Q₀ := by rw [hQdef, hQ]
  have hQ0 : 0 < Q := by rw [hQQ]; exact hQ₀0
  obtain ⟨P, hPdef⟩ : ∃ P : ℝ, P = 3 * c1 3 3 * (((3 : ℕ) : ℝ) ^ (1 + T.m₁)) ^ 3 *
    (((3 : ℕ) : ℝ) ^ 3 * ((((2 : ℕ) : ℝ) / 2) * (2 * (1 + Q) ^ 2 +
      (((3 : ℕ) : ℝ) + 1 + rho4 3 3 2 T.BG T.κ) * Q ^ 2) * T.t ^ 2)) := ⟨_, rfl⟩
  have hPP : P = Pc * T.t ^ 2 := by
    rw [hPdef, hPcdef, hm₁, hBG, hκ, hQQ]; ring
  have hP0 : 0 ≤ P := by rw [hPP]; positivity
  have hK0 : 0 < Q * T.t := mul_pos hQ0 ht0
  have hβ0 : 0 < β := by linarith
  have h3k : (1 : ℝ) ≤ 3 ^ k := one_le_pow₀ (by norm_num)
  have hbβ : β ≤ β * 3 ^ k := le_mul_of_one_le_right hβ0.le h3k
  have hb0 : 0 < β * 3 ^ k := by positivity
  have hbeq : β * 3 ^ k = β * ((3 : ℕ) : ℝ) ^ (k * (3 - 2)) := by norm_num
  have hct' : c * ((3 : ℕ) : ℝ) ^ (-(α * ((k : ℝ) + 1))) ≤ T.t := by
    rw [radius_three_cast]; exact hct
  obtain ⟨hr0', hamp⟩ := hA' k β T.t (β * 3 ^ k) hbeq hβ₁' hct' p₁ hp0 hp₁
  rw [← hκ] at hr0' hamp
  have hr0 : 0 < lvR T.κ T.t (β * 3 ^ k) p₁ := hr0'
  have hamp' := hamp (2 * P) (2 * (Q * T.t)) 1 (by positivity) (by positivity) zero_le_one
  have hbU : (hatStepK (N₁ := 3) k T.m₁ hk 0 β p₁ T.δ).betaU = β * 3 ^ k :=
    hatStepK_betaU k T.m₁ hk 0 β p₁ T.δ
  obtain ⟨εU, hεU⟩ : ∃ εU : ℝ, εU = β * prop33EpsEtaScaled 3 3 2 T.m₁ k 1 1 T.BG T.BG₂ T.κ T.t
      (lvR T.κ T.t (β * 3 ^ k) p₁) 0 0 (1 / β) := ⟨_, rfl⟩
  obtain ⟨-, -, -, hεle', -⟩ := physAmp_facts (hatStepK (N₁ := 3) k T.m₁ hk 0 β p₁ T.δ)
    (by norm_num) le_rfl 1 (compWeight_three_mem hk) rfl hβ0 rfl hbU hQ0 ht0 hρ4 hr0 one_pos
    hQdef hPdef hεU
  have hεle : 2 * εU ≤ (β * 3 ^ k) * (2 * P / (lvR T.κ T.t (β * 3 ^ k) p₁) ^ 3) +
      1 * (2 * (Q * T.t)) / lvR T.κ T.t (β * 3 ^ k) p₁ := by
    have h := hεle' _ le_rfl
    have e : (β * 3 ^ k) * (2 * P / (lvR T.κ T.t (β * 3 ^ k) p₁) ^ 3) +
        1 * (2 * (Q * T.t)) / lvR T.κ T.t (β * 3 ^ k) p₁ =
        2 * ((β * 3 ^ k) * (P / (lvR T.κ T.t (β * 3 ^ k) p₁) ^ 3) +
          1 * (Q * T.t) / lvR T.κ T.t (β * 3 ^ k) p₁) := by ring
    rw [e]
    linarith
  have hε2 := hεle.trans hamp'
  -- the amplitude `P (4A₁/κ₁)³ = M₁ / t`, `K (4 A₁/κ₁) = M₂`
  have hκ₁ : lvKappaG 3 3 2 T.κ T.t = κ₀ * T.t := by
    rw [hκ, hκ₀def]; unfold lvKappaG; field_simp
  have hℓ : 1 ≤ Real.log (β * 3 ^ k) := by
    rw [Real.le_log_iff_exp_le hb0]
    exact (Real.exp_one_lt_three.le.trans hβ3).trans hbβ
  have hs : 0 < Real.sqrt (β * 3 ^ k) := Real.sqrt_pos.2 hb0
  have hw : (Real.log (β * 3 ^ k)) ^ p ≤ (Real.log (β * 3 ^ k)) ^ (3 * p) :=
    pow_le_pow_right₀ hℓ (by omega)
  have hw3 : 0 ≤ (Real.log (β * 3 ^ k)) ^ (3 * p) := by positivity
  have eP : 2 * P * (4 * A₁ / lvKappaG 3 3 2 T.κ T.t) ^ 3 = 2 * Pc * (4 * A₁ / κ₀) ^ 3 / T.t := by
    rw [hκ₁, hPP]; field_simp
  have eK : 4 * A₁ * (2 * (Q * T.t)) / lvKappaG 3 3 2 T.κ T.t = 8 * A₁ * Q₀ / κ₀ := by
    rw [hκ₁, hQQ]; field_simp; ring
  have hb' : (2 * Pc * (4 * A₁ / κ₀) ^ 3 / T.t + 8 * A₁ * Q₀ / κ₀) *
      Real.log (β * 3 ^ k) ^ (3 * p) / Real.sqrt (β * 3 ^ k) ≤
      daT 3 3 4 (2 * Kc') T₀.κdec T₀.κ0 T₀.κ' := by
    have := hinv k β T.t hβ₂' hct'
    rw [← hbeq] at this
    exact this
  have hε' : 2 * εU ≤ daT 3 3 4 (2 * Kc') T.κdec T.κ0 T.κ' := by
    rw [hdec, h0, h']
    refine le_trans (hε2.trans ?_) hb'
    rw [eP, eK, one_mul]
    have e1 : (2 * Pc * (4 * A₁ / κ₀) ^ 3 / T.t + 8 * A₁ * Q₀ / κ₀) *
        Real.log (β * 3 ^ k) ^ (3 * p) / Real.sqrt (β * 3 ^ k) =
        2 * Pc * (4 * A₁ / κ₀) ^ 3 / T.t * Real.log (β * 3 ^ k) ^ (3 * p) / Real.sqrt (β * 3 ^ k) +
        8 * A₁ * Q₀ / κ₀ * Real.log (β * 3 ^ k) ^ (3 * p) / Real.sqrt (β * 3 ^ k) := by ring
    rw [e1]
    have hM2 : 0 ≤ 8 * A₁ * Q₀ / κ₀ := by positivity
    have : 8 * A₁ * Q₀ / κ₀ * Real.log (β * 3 ^ k) ^ p / Real.sqrt (β * 3 ^ k) ≤
        8 * A₁ * Q₀ / κ₀ * Real.log (β * 3 ^ k) ^ (3 * p) / Real.sqrt (β * 3 ^ k) := by
      refine div_le_div_of_nonneg_right ?_ hs.le
      exact mul_le_mul_of_nonneg_left hw hM2
    linarith
  have hdo := (hDA_iff 3 3 (by norm_num : (0 : ℝ) < 4) (by positivity : 0 < 2 * Kc') T.κdec T.κ0
    T.κ' (2 * εU)).2 hε'
  rw [hεU] at hdo
  linarith

end Balaban.Inhabited
