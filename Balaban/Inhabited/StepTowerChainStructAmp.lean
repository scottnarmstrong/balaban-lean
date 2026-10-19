/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.StepTower
public import Balaban.Inhabited.SourceAmpScale
public import Balaban.Inhabited.PhysAmpFacts
public import Balaban.Inhabited.StepScaleDataGBridge
public import Balaban.Inhabited.MarkCorrBudget
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The composed-activity amplitude of the class chain is small at a tower

`StepTower.exists_beta0_amp`: for a tower `T`, a cutoff exponent `p` and any positive entropy
constant `K_c'`, there is `β₀ ≥ 3` such that for every scale `k ≥ 1`, every `β ≥ β₀` and every
cutoff `0 < p₁ ≤ A₁ (log β_k)^p`, the amplitude `ε_U = β · prop33EpsEtaScaled … (1/β)` of the
step satisfies `2² (2 ε_U) ≤ 1 / (8 (2 K_c')³ c₁ exp((2κ_dec - 1 - 2κ₀) c_G + c₁ + κ' c_G))`.
This is the first entry of the numerical condition of the composed activity in
`e0CoeffFamily_class_exists_tower_struct`.
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation
  Balaban.Localization Balaban.Localization.I5Inhabited Balaban.Inhabited.LevelStep
  Balaban.Inhabited.MarkBudgetAudit

/-- **The amplitude of the step at the source slice `q = 1` is small, uniformly in the scale.** -/
theorem StepTower.exists_beta0_amp {κmin : ℝ} (T : StepTower κmin) {A₁ : ℝ} (hA : 0 < A₁) (p : ℕ)
    {Kc' : ℝ} (hKc : 0 < Kc') :
    ∃ β₀ : ℝ, 3 ≤ β₀ ∧ ∀ k : ℕ, 1 ≤ k → ∀ β : ℝ, β₀ ≤ β → ∀ p₁ : ℝ, 0 < p₁ →
      p₁ ≤ pLog A₁ p (β * 3 ^ k) →
      2 ^ 2 * (2 * (β * prop33EpsEtaScaled 3 3 2 T.m₁ k 1 1 T.BG T.BG₂ T.κ T.t
        (lvR T.κ T.t (β * 3 ^ k) p₁) 0 0 (1 / β))) ≤
      1 / (8 * (2 * Kc') ^ 3 * c1 3 3 *
        Real.exp ((2 * T.κdec - 1 - 2 * T.κ0) * cG 3 3 + c1 3 3 + T.κ' * cG 3 3)) := by
  have ht0 := T.t_pos
  have hc1 := one_le_c1 3 3
  obtain ⟨Q, hQdef⟩ : ∃ Q : ℝ, Q = cK2' 3 3 2 (famConst 3 3 T.BG₂ T.κ) := ⟨_, rfl⟩
  have hQ0 : 0 < Q := by rw [hQdef]; exact cK2'_pos' T.fam_nonneg
  obtain ⟨P, hPdef⟩ : ∃ P : ℝ, P = 3 * c1 3 3 * (((3 : ℕ) : ℝ) ^ (1 + T.m₁)) ^ 3 *
    (((3 : ℕ) : ℝ) ^ 3 * ((((2 : ℕ) : ℝ) / 2) * (2 * (1 + Q) ^ 2 +
      (((3 : ℕ) : ℝ) + 1 + rho4 3 3 2 T.BG T.κ) * Q ^ 2) * T.t ^ 2)) := ⟨_, rfl⟩
  have hρ4 := T.rho_nonneg
  have hP0 : 0 ≤ P := by rw [hPdef]; positivity
  have hK0 : 0 < Q * T.t := mul_pos hQ0 ht0
  obtain ⟨β₁, hexp, hA'⟩ := sourceAmp_scale (A₁ := A₁) (κ := T.κ) (t := T.t) hA p ht0
  refine ⟨max (max β₁ (daThreshold ((srcCE A₁ T.κ T.t (2 * P) + srcCF A₁ T.κ T.t (2 * (Q * T.t))) / 4)
      (daT 3 3 4 (2 * Kc') T.κdec T.κ0 T.κ') (3 * p))) 3, le_max_right _ _, ?_⟩
  intro k hk β hβ p₁ hp0 hp₁
  obtain ⟨⟨hβ₁, hβd⟩, hβ3⟩ : (β₁ ≤ β ∧ daThreshold
      ((srcCE A₁ T.κ T.t (2 * P) + srcCF A₁ T.κ T.t (2 * (Q * T.t))) / 4)
      (daT 3 3 4 (2 * Kc') T.κdec T.κ0 T.κ') (3 * p) ≤ β) ∧ 3 ≤ β := by
    simpa only [max_le_iff] using hβ
  have hβ0 : 0 < β := by linarith
  have h3k : (1 : ℝ) ≤ 3 ^ k := one_le_pow₀ (by norm_num)
  have hbβ : β ≤ β * 3 ^ k := le_mul_of_one_le_right hβ0.le h3k
  have hb0 : 0 < β * 3 ^ k := by positivity
  have hexpb : Real.exp 1 ≤ β * 3 ^ k := le_trans hexp (hβ₁.trans hbβ)
  have hℓ : 1 ≤ Real.log (β * 3 ^ k) := (Real.le_log_iff_exp_le hb0).2 hexpb
  obtain ⟨hr0, hamp⟩ := hA' (β * 3 ^ k) (hβ₁.trans hbβ) p₁ hp0 hp₁
  have hamp' := hamp (2 * P) (2 * (Q * T.t)) 1 (by positivity) (by positivity) zero_le_one
  have hbU : (hatStepK (N₁ := 3) k T.m₁ hk 0 β p₁ T.δ).betaU = β * 3 ^ k :=
    hatStepK_betaU k T.m₁ hk 0 β p₁ T.δ
  obtain ⟨εU, hεU⟩ : ∃ εU : ℝ, εU = β * prop33EpsEtaScaled 3 3 2 T.m₁ k 1 1 T.BG T.BG₂ T.κ T.t
      (lvR T.κ T.t (β * 3 ^ k) p₁) 0 0 (1 / β) := ⟨_, rfl⟩
  obtain ⟨-, -, -, hεle', -⟩ := physAmp_facts (hatStepK (N₁ := 3) k T.m₁ hk 0 β p₁ T.δ)
    (by norm_num) le_rfl 1 (compWeight_three_mem hk) rfl hβ0 rfl hbU hQ0 ht0 hρ4 hr0 one_pos hQdef
    hPdef hεU
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
  have hdo := sourceAmp_doubled_hDA 3 3 (A₁ := A₁) (κ := T.κ) (t := T.t) (P := 2 * P)
    (K := 2 * (Q * T.t)) (q := 1) (b := β * 3 ^ k) (ε := 2 * εU) (Kc' := Kc') p hA ht0
    (by positivity) (by positivity) le_rfl hℓ hb0 hKc T.κdec T.κ0 T.κ' (hβd.trans hbβ)
    (by simpa using hε2)
  rw [hεU] at hdo
  linarith

/-- **The marked-radius numerics of the class chain at a general tower.**  If `2 U ≤ R`
(`R = corrRG`), the marked radius `decMRG` is positive and `2 U decMRG`, `(U + R) decMRG` are below
`T.t`. -/
theorem StepTowerG.marked_numerics {d L N : ℕ} [NeZero L] {κmin : ℝ} (T : StepTowerG d L N κmin)
    {k : ℕ} (hk : 1 ≤ k) {b p₁ : ℝ} (hb0 : 0 < b) (hp0 : 0 < p₁)
    (hRU : 2 * corrU ≤ corrRG T k b p₁) :
    0 < corrRG T k b p₁ ∧ 0 < decMRG T k b p₁ ∧ 2 * corrU * decMRG T k b p₁ < T.t ∧
      (corrU + corrRG T k b p₁) * decMRG T k b p₁ < T.t := by
  have hdec := decMRG_pos T hk hb0 hp0
  have hR2 := two_corrRG_mul_decMRG_lt T hk hb0 hp0
  have hRpos := corrRG_pos T hk hb0 hp0
  have hU := corrU_pos
  refine ⟨hRpos, hdec, ?_, ?_⟩
  · nlinarith [mul_pos hRpos hdec]
  · nlinarith [mul_pos hRpos hdec]

/-- **The marked-radius numerics of the class chain at a tower** (the tower at `d = L = 3`,
`N = 2`). -/
theorem StepTower.marked_numerics {κmin : ℝ} (T : StepTower κmin) {k : ℕ} (hk : 1 ≤ k) {β p₁ : ℝ}
    (hb0 : 0 < β * 3 ^ k) (hp0 : 0 < p₁) (hRU : 2 * corrU ≤ corrR T k (β * 3 ^ k) p₁) :
    0 < corrR T k (β * 3 ^ k) p₁ ∧ 0 < decMR T k (β * 3 ^ k) p₁ ∧
      2 * corrU * decMR T k (β * 3 ^ k) p₁ < T.t ∧
      (corrU + corrR T k (β * 3 ^ k) p₁) * decMR T k (β * 3 ^ k) p₁ < T.t := by
  have hb : β * ((3 : ℕ) : ℝ) ^ (k * (3 - 2)) = β * 3 ^ k := by norm_num
  have h := StepTowerG.marked_numerics T.toG hk (b := β * 3 ^ k) hb0 hp0
    (by rw [← corrR_toG]; exact hRU)
  simp only [corrR_toG, decMR_toG]
  exact h

/-- **The constant `ε_C` is nonnegative** (general `d`, `L`). -/
theorem epsC_nonnegG {d L : ℕ} [NeZero L] {mr t E₀ CI KL α₃ κdec κ0 κdec' : ℝ}
    {n₁ m₀ m₁ : ℕ} (hmr : 0 < mr)
    (ht : 0 < t) (hE₀ : 0 ≤ E₀) (hCI : 0 ≤ CI) (hKL : 0 ≤ KL) (hα₃ : 0 < α₃)
    (hK0 : 0 < K0 d L κ0) :
    0 ≤ corrU / (t / (2 * mr)) *
          (((2 ^ L ^ d : ℕ) : ℝ) * (c1 d L * ((((L : ℝ) ^ (1 + m₀ + m₁)) ^ d) * E₀ *
          (2 * K0 d L κ0 * (CI * Real.exp ((κdec - 1) * cG d L) * (1 - (L : ℝ) ^ (-α₃))⁻¹ +
            n₁ * (KL * Real.exp ((κdec - 1) * cG d L)) * (((L : ℝ) ^ (n₁ - 1)) ^ d)))) *
          Real.exp ((2 * κdec' - 1) * (2 * (d : ℝ) * (L : ℝ) ^ m₀ *
            ((((L ^ (m₀ - 1)) ^ d : ℕ)) : ℝ) * c1 d L)))) := by
  have hw : 0 ≤ (1 - (L : ℝ) ^ (-α₃))⁻¹ := by
    refine inv_nonneg.2 (sub_nonneg.2 ?_)
    exact Real.rpow_le_one_of_one_le_of_nonpos
      (by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne L)) (by linarith)
  have hc1 : 0 ≤ c1 d L := by have := one_le_c1 d L; linarith
  have hU := corrU_pos
  generalize (1 - (L : ℝ) ^ (-α₃))⁻¹ = w at hw ⊢
  positivity

/-- **The constant `ε_C` is nonnegative.** -/
theorem epsC_nonneg {mr t E₀ CI KL α₃ κdec κ0 κdec' : ℝ} {n₁ m₀ m₁ : ℕ} (hmr : 0 < mr)
    (ht : 0 < t) (hE₀ : 0 ≤ E₀) (hCI : 0 ≤ CI) (hKL : 0 ≤ KL) (hα₃ : 0 < α₃)
    (hK0 : 0 < K0 3 3 κ0) :
    0 ≤ corrU / (t / (2 * mr)) *
          (((2 ^ 3 ^ 3 : ℕ) : ℝ) * (c1 3 3 * ((((3 : ℕ) : ℝ) ^ (1 + m₀ + m₁)) ^ 3 * E₀ *
          (2 * K0 3 3 κ0 * (CI * Real.exp ((κdec - 1) * cG 3 3) * (1 - ((3 : ℕ) : ℝ) ^ (-α₃))⁻¹ +
            n₁ * (KL * Real.exp ((κdec - 1) * cG 3 3)) * ((((3 : ℕ) : ℝ) ^ (n₁ - 1)) ^ 3)))) *
          Real.exp ((2 * κdec' - 1) * (2 * ((3 : ℕ) : ℝ) * ((3 : ℕ) : ℝ) ^ m₀ *
            ((((3 ^ (m₀ - 1)) ^ 3 : ℕ)) : ℝ) * c1 3 3)))) :=
  epsC_nonnegG hmr ht hE₀ hCI hKL hα₃ hK0

end Balaban.Inhabited
