/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.StepTowerBeta0Amp
public import Balaban.Inhabited.SourceFamilyRelativeFromTower
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

/-!
# The amplitude `4 ε_U` of the source family, uniformly in the step radius

`StepTowerG.srcAmp_agree`: for towers that agree with `T₀` on `m₀, m₁, BG, BG₂, κ`, every
`t ≥ c L^{-α(k+1)}` and one threshold `β₀`, the amplitude `ε_U = β · prop33EpsEtaScaled …` of the
source family is positive and
`4 ε_U ≤ (M₁ / t) (log b)^{3p}/√b + q M₂ (log b)^p/√b`
with `M₁, M₂` free of `t` (`P ∝ t²`, `κ₁ ∝ t`).
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation
  Balaban.Localization Balaban.Localization.LevelPair Balaban.Localization.I5Inhabited
  Balaban.Polymer Balaban.SmallField.Def6 Balaban.Inhabited.LevelStep

namespace StepTowerG

variable {d L N : ℕ} [NeZero L] {κmin : ℝ}

/-- **The amplitude of the source family, uniformly in the step radius.** -/
theorem srcAmp_agree (T₀ : StepTowerG d L N κmin) {A₁ : ℝ} (hA : 0 < A₁) (p : ℕ) {c α : ℝ}
    (hc : 0 < c) (hα : 2 * α < ((d - 2 : ℕ) : ℝ)) :
    ∃ (β₀ M₁ M₂ : ℝ), 3 ≤ β₀ ∧ 0 ≤ M₁ ∧ 0 < M₂ ∧
      ∀ T : StepTowerG d L N κmin, T.m₀ = T₀.m₀ → T.m₁ = T₀.m₁ → T.BG = T₀.BG →
      T.BG₂ = T₀.BG₂ → T.κ = T₀.κ →
      ∀ (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁] (ν β : ℝ), β₀ ≤ β →
      c * (L : ℝ) ^ (-(α * ((k : ℝ) + 1))) ≤ T.t → ∀ p₁ : ℝ, 0 < p₁ →
      p₁ ≤ pLog A₁ p (β * (L : ℝ) ^ (k * (d - 2))) → ∀ q : ℝ, 0 < q →
      ∀ S : StepSetting d L N₁ T.m₁ k N (rhoSepG d L T.m₁), S = T.step k hk N₁ ν β p₁ →
        0 < S.β * prop33EpsEtaScaled d L N T.m₁ k T.m₀ S.a₁ T.BG T.BG₂ T.κ T.t
          (lvRG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2))) p₁) 0 0 (q / S.β) ∧
        4 * (S.β * prop33EpsEtaScaled d L N T.m₁ k T.m₀ S.a₁ T.BG T.BG₂ T.κ T.t
          (lvRG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2))) p₁) 0 0 (q / S.β)) ≤
          M₁ / T.t * (Real.log (β * (L : ℝ) ^ (k * (d - 2)))) ^ (3 * p) /
            Real.sqrt (β * (L : ℝ) ^ (k * (d - 2))) +
          q * M₂ * (Real.log (β * (L : ℝ) ^ (k * (d - 2)))) ^ p /
            Real.sqrt (β * (L : ℝ) ^ (k * (d - 2))) := by
  have hd := T₀.hd
  have hL := T₀.hL
  have hN2 := T₀.hN
  have hd0 : 0 < d := by omega
  have hc1 := one_le_c1 d L
  obtain ⟨Q₀, hQ₀def⟩ : ∃ Q : ℝ, Q = cK2' d L N (famConst d L T₀.BG₂ T₀.κ) := ⟨_, rfl⟩
  have hQ₀0 : 0 < Q₀ := by rw [hQ₀def]; exact cK2'_pos_general T₀.fam_nonneg
  obtain ⟨Pc, hPcdef⟩ : ∃ Pc : ℝ, Pc = 3 * c1 d L * (((L : ℕ) : ℝ) ^ (T₀.m₀ + T₀.m₁)) ^ d *
    ((L : ℝ) ^ d * (((N : ℝ) / 2) * (2 * (1 + Q₀) ^ 2 +
      ((d : ℝ) + 1 + rho4 d L N T₀.BG T₀.κ) * Q₀ ^ 2))) := ⟨_, rfl⟩
  have hρ₀ := T₀.rho_nonneg
  have hPc0 : 0 ≤ Pc := by rw [hPcdef]; positivity
  have hsN : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast (by omega : 0 < N))
  have hCm := covSupMaxC_nonneg_general (N := N) hd0 hL T₀.κ
  obtain ⟨κ₀, hκ₀def⟩ : ∃ κ₀ : ℝ, κ₀ = 1 / (2 * Real.sqrt (N : ℝ) *
    (covSupMaxC d L N T₀.κ + 1)) := ⟨_, rfl⟩
  have hκ₀0 : 0 < κ₀ := by rw [hκ₀def]; positivity
  obtain ⟨β₁, hβ₁, hA'⟩ := sourceAmp_scale_general_agree (N := N) hd hL (by omega) (A₁ := A₁) (κ := T₀.κ) hA
    p hc hα
  refine ⟨β₁, 4 * Pc * (4 * A₁ / κ₀) ^ 3, 16 * A₁ * Q₀ / κ₀, hβ₁, by positivity, by positivity, ?_⟩
  intro T hm₀ hm₁ hBG hBG₂ hκ k hk N₁ _ ν β hβ hct p₁ hp0 hp₁ q hq0 S hS
  have ht0 := T.t_pos
  have hρ4 := T.rho_nonneg
  have hβ3 : 3 ≤ β := hβ₁.trans hβ
  have hβ0 : 0 < β := by linarith
  have hQ : cK2' d L N (famConst d L T.BG₂ T.κ) = Q₀ := by rw [hQ₀def, hBG₂, hκ]
  obtain ⟨Q, hQdef⟩ : ∃ Q : ℝ, Q = cK2' d L N (famConst d L T.BG₂ T.κ) := ⟨_, rfl⟩
  have hQQ : Q = Q₀ := by rw [hQdef, hQ]
  have hQ0 : 0 < Q := by rw [hQQ]; exact hQ₀0
  obtain ⟨P, hPdef⟩ : ∃ P : ℝ, P = 3 * c1 d L * (((L : ℕ) : ℝ) ^ (T.m₀ + T.m₁)) ^ d *
    ((L : ℝ) ^ d * (((N : ℝ) / 2) * (2 * (1 + Q) ^ 2 +
      ((d : ℝ) + 1 + rho4 d L N T.BG T.κ) * Q ^ 2) * T.t ^ 2)) := ⟨_, rfl⟩
  have hPP : P = Pc * T.t ^ 2 := by
    rw [hPdef, hPcdef, hm₀, hm₁, hBG, hκ, hQQ]; ring
  have hP0 : 0 ≤ P := by rw [hPP]; positivity
  have hK0 : 0 < Q * T.t := mul_pos hQ0 ht0
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast (by omega : 1 ≤ L)
  have h3k : (1 : ℝ) ≤ (L : ℝ) ^ (k * (d - 2)) := one_le_pow₀ hL1
  have hbβ : β ≤ β * (L : ℝ) ^ (k * (d - 2)) := le_mul_of_one_le_right hβ0.le h3k
  have hb0 : 0 < β * (L : ℝ) ^ (k * (d - 2)) := by linarith
  obtain ⟨hr0', hamp⟩ := hA' k β T.t _ rfl hβ (by rw [← hκ] at *; exact hct) p₁ hp0 hp₁
  have hamp' := hamp P (Q * T.t) q hP0 hK0.le hq0.le
  rw [← hκ] at hr0' hamp'
  have hbU : (T.step k hk N₁ ν β p₁).betaU = β * (L : ℝ) ^ (k * (d - 2)) :=
    hatStepKG_betaU (d := d) (L := L) (N₁ := N₁) T.hN (by omega) k T.m₁ (rhoSepG d L T.m₁) hk ν β
      p₁ T.δ
  subst hS
  obtain ⟨-, -, -, hεle', hεpos⟩ := physAmp_facts (T.step k hk N₁ ν β p₁)
    (by omega) hL T.m₀ (compWeight_one_mem hL hk) rfl hβ0 rfl hbU hQ0 ht0 hρ4 hr0' hq0 hQdef hPdef
    (εU := β * prop33EpsEtaScaled d L N T.m₁ k T.m₀ 1 T.BG T.BG₂ T.κ T.t
      (lvRG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2))) p₁) 0 0 (q / β)) rfl
  have hβS : (T.step k hk N₁ ν β p₁).β = β := rfl
  have ha₁ : (T.step k hk N₁ ν β p₁).a₁ = 1 := rfl
  rw [hβS, ha₁]
  refine ⟨hεpos, ?_⟩
  have hεle := hεle' _ hamp'
  have hκ₁ : lvKappaG d L N T.κ T.t = κ₀ * T.t := by
    rw [hκ, hκ₀def]; unfold lvKappaG; field_simp
  have hs : 0 < Real.sqrt (β * (L : ℝ) ^ (k * (d - 2))) := Real.sqrt_pos.2 hb0
  have eP : P * (4 * A₁ / lvKappaG d L N T.κ T.t) ^ 3 = Pc * (4 * A₁ / κ₀) ^ 3 / T.t := by
    rw [hκ₁, hPP]; field_simp
  have eK : 4 * A₁ * (Q * T.t) / lvKappaG d L N T.κ T.t = 4 * A₁ * Q₀ / κ₀ := by
    rw [hκ₁, hQQ]; field_simp
  rw [eP, eK] at hεle
  have e1 : 4 * (Pc * (4 * A₁ / κ₀) ^ 3 / T.t *
        (Real.log (β * (L : ℝ) ^ (k * (d - 2)))) ^ (3 * p) / Real.sqrt (β * (L : ℝ) ^ (k * (d - 2))) +
      q * (4 * A₁ * Q₀ / κ₀) * (Real.log (β * (L : ℝ) ^ (k * (d - 2)))) ^ p /
        Real.sqrt (β * (L : ℝ) ^ (k * (d - 2)))) =
      4 * Pc * (4 * A₁ / κ₀) ^ 3 / T.t * (Real.log (β * (L : ℝ) ^ (k * (d - 2)))) ^ (3 * p) /
        Real.sqrt (β * (L : ℝ) ^ (k * (d - 2))) +
      q * (16 * A₁ * Q₀ / κ₀) * (Real.log (β * (L : ℝ) ^ (k * (d - 2)))) ^ p /
        Real.sqrt (β * (L : ℝ) ^ (k * (d - 2))) := by ring
  rw [← e1]
  linarith

/-- **The amplitude of the step at the source slice `q = 1` is small, uniformly in the scale and the
step radius, general tower.**  For towers `T` that agree with `T₀` on `m₀, m₁, BG, BG₂, κ, κ₀, κ'`
and every radius `t ≥ c L^{-α(k+1)}`, `2 α < d - 2`: `2² · 2 ε_U` is at most the threshold of the
amplitude condition at the entropy constant `2 K_c'`. -/
theorem exists_beta0_amp_agree (T₀ : StepTowerG d L N κmin) {A₁ : ℝ} (hA : 0 < A₁) (p : ℕ)
    {Kc' : ℝ} (hKc : 0 < Kc') {c α : ℝ} (hc : 0 < c) (hα : 2 * α < ((d - 2 : ℕ) : ℝ)) :
    ∃ β₀ : ℝ, 3 ≤ β₀ ∧ ∀ T : StepTowerG d L N κmin, T.m₀ = T₀.m₀ → T.m₁ = T₀.m₁ →
      T.BG = T₀.BG → T.BG₂ = T₀.BG₂ → T.κ = T₀.κ → T.κ0 = T₀.κ0 → T.κ' = T₀.κ' →
      ∀ k : ℕ, 1 ≤ k → ∀ β : ℝ, β₀ ≤ β →
      c * (L : ℝ) ^ (-(α * ((k : ℝ) + 1))) ≤ T.t → ∀ p₁ : ℝ, 0 < p₁ →
      p₁ ≤ pLog A₁ p (β * (L : ℝ) ^ (k * (d - 2))) →
      2 ^ 2 * (2 * (β * prop33EpsEtaScaled d L N T.m₁ k T.m₀ 1 T.BG T.BG₂ T.κ T.t
        (lvRG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2))) p₁) 0 0 (1 / β))) ≤
      1 / (8 * (2 * Kc') ^ 3 * c1 d L *
        Real.exp ((2 * T.κdec - 1 - 2 * T.κ0) * cG d L + c1 d L + T.κ' * cG d L)) := by
  have hd := T₀.hd
  have hL := T₀.hL
  obtain ⟨β₁, M₁, M₂, hβ₁, hM₁, hM₂, H⟩ := srcAmp_agree T₀ hA p hc hα
  have hdaT := daT_pos d L (by norm_num : (0 : ℝ) < 4) (by positivity : 0 < 2 * Kc') T₀.κdec
    T₀.κ0 T₀.κ'
  obtain ⟨β₂, hβ₂, hinv⟩ := exists_beta0_inv_t_le (d := d) (L := L) hd hL (M₁ := 2 * M₁)
    (M₂ := 2 * M₂) (η := daT d L 4 (2 * Kc') T₀.κdec T₀.κ0 T₀.κ') (c := c) (α := α) (3 * p)
    (by positivity) (by positivity) hdaT hc hα
  refine ⟨max β₁ β₂, hβ₁.trans (le_max_left _ _), ?_⟩
  intro T hm₀ hm₁ hBG hBG₂ hκ h0 h' k hk β hβ hct p₁ hp0 hp₁
  have hdec : T.κdec = T₀.κdec := by rw [T.κdec_eq, T₀.κdec_eq, h0]
  have hβ₁' : β₁ ≤ β := (le_max_left _ _).trans hβ
  have hβ₂' : β₂ ≤ β := (le_max_right _ _).trans hβ
  have hβ0 : 0 < β := by linarith
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast (by omega : 1 ≤ L)
  have h3k : (1 : ℝ) ≤ (L : ℝ) ^ (k * (d - 2)) := one_le_pow₀ hL1
  have hbβ : β ≤ β * (L : ℝ) ^ (k * (d - 2)) := le_mul_of_one_le_right hβ0.le h3k
  have hb0 : 0 < β * (L : ℝ) ^ (k * (d - 2)) := by linarith
  have hℓ : 1 ≤ Real.log (β * (L : ℝ) ^ (k * (d - 2))) := by
    rw [Real.le_log_iff_exp_le hb0]
    exact (Real.exp_one_lt_three.le.trans (hβ₁.trans hβ₁')).trans hbβ
  have hs : 0 < Real.sqrt (β * (L : ℝ) ^ (k * (d - 2))) := Real.sqrt_pos.2 hb0
  have hw : (Real.log (β * (L : ℝ) ^ (k * (d - 2)))) ^ p ≤
      (Real.log (β * (L : ℝ) ^ (k * (d - 2)))) ^ (3 * p) := pow_le_pow_right₀ hℓ (by omega)
  have hw3 : 0 ≤ (Real.log (β * (L : ℝ) ^ (k * (d - 2)))) ^ (3 * p) := by positivity
  obtain ⟨-, hε⟩ := H T hm₀ hm₁ hBG hBG₂ hκ k hk 1 0 β hβ₁' hct p₁ hp0 hp₁ 1 one_pos
    (T.step k hk 1 0 β p₁) rfl
  have hβS : (T.step k hk 1 0 β p₁).β = β := rfl
  have ha₁ : (T.step k hk 1 0 β p₁).a₁ = 1 := rfl
  rw [hβS, ha₁] at hε
  have hb' := hinv k β T.t hβ₂' hct
  have ht0 := T.t_pos
  have hA0 : 0 ≤ M₁ / T.t * (Real.log (β * (L : ℝ) ^ (k * (d - 2)))) ^ (3 * p) /
      Real.sqrt (β * (L : ℝ) ^ (k * (d - 2))) := by positivity
  have hB : M₂ * (Real.log (β * (L : ℝ) ^ (k * (d - 2)))) ^ p /
      Real.sqrt (β * (L : ℝ) ^ (k * (d - 2))) ≤ M₂ *
      (Real.log (β * (L : ℝ) ^ (k * (d - 2)))) ^ (3 * p) /
        Real.sqrt (β * (L : ℝ) ^ (k * (d - 2))) :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hw hM₂.le) hs.le
  have hB0 : 0 ≤ M₂ * (Real.log (β * (L : ℝ) ^ (k * (d - 2)))) ^ (3 * p) /
      Real.sqrt (β * (L : ℝ) ^ (k * (d - 2))) := by positivity
  have e1 : (2 * M₁ / T.t + 2 * M₂) * (Real.log (β * (L : ℝ) ^ (k * (d - 2)))) ^ (3 * p) /
      Real.sqrt (β * (L : ℝ) ^ (k * (d - 2))) =
      2 * (M₁ / T.t * (Real.log (β * (L : ℝ) ^ (k * (d - 2)))) ^ (3 * p) /
        Real.sqrt (β * (L : ℝ) ^ (k * (d - 2)))) +
      2 * (M₂ * (Real.log (β * (L : ℝ) ^ (k * (d - 2)))) ^ (3 * p) /
        Real.sqrt (β * (L : ℝ) ^ (k * (d - 2)))) := by ring
  rw [one_mul] at hε
  have hε' : 2 * (β * prop33EpsEtaScaled d L N T.m₁ k T.m₀ 1 T.BG T.BG₂ T.κ T.t
      (lvRG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2))) p₁) 0 0 (1 / β)) ≤
      daT d L 4 (2 * Kc') T.κdec T.κ0 T.κ' := by
    rw [hdec, h0, h']
    refine le_trans ?_ hb'
    linarith
  have hdo := (hDA_iff d L (by norm_num : (0 : ℝ) < 4) (by positivity : 0 < 2 * Kc') T.κdec T.κ0
    T.κ' _).2 hε'
  rw [show (2 : ℝ) ^ 2 = 4 by norm_num]
  exact hdo

end StepTowerG

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
  obtain ⟨β₀, h3, H⟩ := StepTowerG.exists_beta0_amp_agree T₀.toG hA p hKc hc (alpha_three_cast hα)
  refine ⟨β₀, h3, fun T hm₁ hBG hBG₂ hκ k hk β hβ hct p₁ hp0 hp₁ => ?_⟩
  obtain ⟨h0, hdec, h'⟩ := StepTower.agree_rates T₀ T
  have hb : ∀ (k : ℕ) (β : ℝ), β * ((3 : ℕ) : ℝ) ^ (k * (3 - 2)) = β * 3 ^ k := by
    intro k β; norm_num
  have := H T.toG rfl hm₁ hBG hBG₂ hκ h0 h' k hk β hβ (by rw [radius_three_cast]; exact hct) p₁ hp0
    (by rw [hb]; exact hp₁)
  rw [hb] at this
  exact this


end Balaban.Inhabited
