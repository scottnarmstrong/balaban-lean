/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.MarkCorrBudgetT
public import Balaban.Inhabited.StepTowerBeta0Marks

/-!
# The radius of the corrected marks beyond a threshold (`StepTowerNewLevelE0Beta`)

The constant `B` of the class chain is bounded by `C_PE (corrF0 K₀ + Q₁ E₀/(2 R) n₁ K₀ + n₂ K₀)`
(`StepTowerNewLevelE0Step`), `R = corrR`.  For the closure of `E₀` the quantities `corrF0` and `R` are
needed in the form: `corrF0 ≤ 1` and `R ≥ R₀` for every `R₀`, beyond one threshold of `β`, uniformly in
the scale and in the radius `t ≥ c 3^{-α(k+1)}`.

* `exists_beta0_corrRTge`: `R₀ ≤ corrRG` (the case `R₀ = 2U` of `exists_beta0_corrRT`);
* `exists_beta0_closureG_agree`, `exists_beta0_closure_agree`: both statements for the towers that
  agree with a reference tower except for `t`.
-/

@[expose] public section

namespace Balaban.Inhabited.MarkBudgetAudit

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation
  Balaban.Localization Balaban.Localization.LevelPair Balaban.Localization.I5Inhabited
  Balaban.Polymer Balaban.SmallField.Def6 Balaban.Inhabited.LevelStep Balaban.Inhabited

variable {d L N : ℕ} [NeZero L] {κmin : ℝ}

omit [NeZero L] in
private theorem scaleB_eq_ge (k : ℕ) :
    (L : ℝ) ^ (k * (d - 2)) = ((L : ℝ) ^ (d - 2)) ^ k := by
  rw [mul_comm, pow_mul]

omit [NeZero L] in
private theorem radiusB_eq_ge (hL : 3 ≤ L) (hd : 3 ≤ d) (α : ℝ) (k : ℕ) :
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
private theorem baseB_gt_ge (hL : 3 ≤ L) (hd : 3 ≤ d) : (1 : ℝ) < (L : ℝ) ^ (d - 2) :=
  one_lt_pow₀ (by exact_mod_cast (by omega : 1 < L)) (by omega)

private theorem rateB_lt_ge (hd : 3 ≤ d) {α : ℝ} (hα : 2 * α < ((d - 2 : ℕ) : ℝ)) :
    1 * (α / ((d - 2 : ℕ) : ℝ)) < 1 / 2 := by
  have hd0 : (0 : ℝ) < ((d - 2 : ℕ) : ℝ) := by
    have : 0 < d - 2 := by omega
    exact_mod_cast this
  rw [one_mul, div_lt_iff₀ hd0]
  linarith

/-- **The radius `R ≥ R₀` of the corrected marks beyond one threshold, at every scale and every
step radius `t ≥ c L^{-α (k+1)}`**, for towers with `C_max(κ) ≤ Cc`; `2 α < d - 2`. -/
theorem exists_beta0_corrRTge (hd : 3 ≤ d) (hL : 3 ≤ L) {A₁ : ℝ} (hA : 0 ≤ A₁) (p : ℕ)
    {Cc c α R₀ : ℝ} (hCc : 0 ≤ Cc) (hc : 0 < c) (hR₀ : 0 < R₀)
    (hα : 2 * α < ((d - 2 : ℕ) : ℝ)) :
    ∃ β₀ : ℝ, 3 ≤ β₀ ∧ ∀ (T : StepTowerG d L N κmin) (k : ℕ), 1 ≤ k → ∀ β p₁ : ℝ, β₀ ≤ β →
      0 < p₁ → p₁ ≤ pLog A₁ p (β * (L : ℝ) ^ (k * (d - 2))) → covSupMaxC d L N T.κ ≤ Cc →
      c * (L : ℝ) ^ (-(α * ((k : ℝ) + 1))) ≤ T.t →
      R₀ ≤ corrRG T (k := k) (β * (L : ℝ) ^ (k * (d - 2))) p₁ := by
  obtain ⟨β₀, h3, H⟩ := exists_beta0_marginB_pLog (Λ := (L : ℝ) ^ (d - 2)) (a := 1) (s := 1 / 2)
    (α := α / ((d - 2 : ℕ) : ℝ)) (c := c) (C := 4 * R₀ * (Real.sqrt N * Cc))
    (A₁ := A₁) p 1 (baseB_gt_ge hL hd) hc zero_le_one (by norm_num) (rateB_lt_ge hd hα)
    (by positivity) hA
  refine ⟨β₀, h3, fun T k hk β p₁ hβ hp hp₁ hCmax hct => ?_⟩
  have hβ0 : 0 < β := by linarith
  have hLs := scalePosG T k
  have hb0 : 0 < β * (L : ℝ) ^ (k * (d - 2)) := by positivity
  have hs : 0 < Real.sqrt (β * (L : ℝ) ^ (k * (d - 2))) := Real.sqrt_pos.2 hb0
  have ht := T.t_pos
  have hmar := H k β T.t p₁ hβ (by rw [← radiusB_eq_ge hL hd α k]; exact hct) hp
    (by rw [← scaleB_eq_ge k]; exact hp₁)
  rw [← scaleB_eq_ge k, Real.rpow_one, ← Real.sqrt_eq_rpow, pow_one] at hmar
  have hq := decMRG_pos T hk hb0 hp
  have hqle := decMRG_le T hk hb0 hp.le
  have hr2 : 0 ≤ Real.sqrt (N : ℝ) := Real.sqrt_nonneg _
  have hq2 : decMRG T k (β * (L : ℝ) ^ (k * (d - 2))) p₁ ≤
      Real.sqrt N * ((Real.sqrt (β * (L : ℝ) ^ (k * (d - 2))))⁻¹ * (Cc * p₁)) := by
    refine hqle.trans ?_
    gcongr
  have h8 : 4 * R₀ * decMRG T k (β * (L : ℝ) ^ (k * (d - 2))) p₁ ≤ T.t := by
    have h1 : 4 * R₀ * decMRG T k (β * (L : ℝ) ^ (k * (d - 2))) p₁ ≤
        4 * R₀ * (Real.sqrt N * ((Real.sqrt (β * (L : ℝ) ^ (k * (d - 2))))⁻¹ *
          (Cc * p₁))) := by gcongr
    refine h1.trans ?_
    have e : 4 * R₀ * (Real.sqrt N * ((Real.sqrt (β * (L : ℝ) ^ (k * (d - 2))))⁻¹ *
          (Cc * p₁))) = 4 * R₀ * (Real.sqrt N * Cc) * p₁ /
          Real.sqrt (β * (L : ℝ) ^ (k * (d - 2))) := by
      field_simp
    rw [e, div_le_iff₀ hs]
    linarith
  unfold corrRG
  rw [le_div_iff₀ (by positivity)]
  nlinarith

/-- **`corrF0 ≤ 1` and `R ≥ R₀` beyond one threshold**, for the towers that agree with a reference
tower except for `t`, at every scale and every radius `t ≥ c L^{-α(k+1)}` (general tower). -/
theorem exists_beta0_closureG_agree (hd : 3 ≤ d) (hL : 3 ≤ L) (T₀ : StepTowerG d L N κmin)
    {A₁ : ℝ} (hA : 0 ≤ A₁) (p : ℕ) {c α R₀ : ℝ} (hc : 0 < c) (hR₀ : 0 < R₀)
    (hα : 2 * α < ((d - 2 : ℕ) : ℝ)) :
    ∃ β₀ : ℝ, 3 ≤ β₀ ∧ ∀ T : StepTowerG d L N κmin, T.BG = T₀.BG → T.BG₂ = T₀.BG₂ →
      T.κ = T₀.κ → T.κdec = T₀.κdec → T.m₁ = T₀.m₁ → ∀ k : ℕ, 1 ≤ k → ∀ β p₁ : ℝ, β₀ ≤ β →
      0 < p₁ → p₁ ≤ pLog A₁ p (β * (L : ℝ) ^ (k * (d - 2))) →
      c * (L : ℝ) ^ (-(α * ((k : ℝ) + 1))) ≤ T.t →
      R₀ ≤ corrRG T (k := k) (β * (L : ℝ) ^ (k * (d - 2))) p₁ ∧ corrF0G T k β p₁ ≤ 1 := by
  obtain ⟨βR, hβR, hR⟩ := exists_beta0_corrRTge (N := N) (κmin := κmin) hd hL hA p
    (Cc := covSupMaxC d L N T₀.κ) (c := c) (α := α) (R₀ := R₀)
    (covSupMaxC_nonneg_general (by omega) hL T₀.κ) hc hR₀ hα
  obtain ⟨βF, hβF, hF⟩ := exists_beta0_corrF0_leT (N := N) (κmin := κmin) hd hL one_pos hA p
    (M := CcorrG T₀ * T₀.t) (c := c) (α := α) (mul_nonneg (CcorrG_nonneg T₀) T₀.t_pos.le) hc hα
  refine ⟨max βR βF, hβR.trans (le_max_left _ _), fun T hBG hBG₂ hκ hκdec hm₁ k hk β p₁ hβ hp hp₁
    hct => ⟨?_, ?_⟩⟩
  · exact hR T k hk β p₁ (le_max_left _ _ |>.trans hβ) hp hp₁ (by rw [hκ]) hct
  · exact hF T k hk β p₁ ((le_max_right _ _).trans hβ) hp hp₁
      (CcorrG_mul_t_eq T₀ T hBG hBG₂ hκ hκdec hm₁).le hct

end Balaban.Inhabited.MarkBudgetAudit

namespace Balaban.Inhabited

open Balaban Balaban.Inhabited.MarkBudgetAudit

/-- **`corrF0 ≤ 1` and `R ≥ R₀` beyond one threshold at the tower (`d = L = 3`, `N = 2`)**, for the
towers that agree with a reference tower `T₀` on `m₁, BG, BG₂, κ` (hence on the rates) and every
radius `t ≥ c 3^{-α(k+1)}`, `2 α < 1`. -/
theorem exists_beta0_closure_agree {κmin : ℝ} (T₀ : StepTower κmin) {A₁ : ℝ} (hA : 0 ≤ A₁) (p : ℕ)
    {c α R₀ : ℝ} (hc : 0 < c) (hR₀ : 0 < R₀) (hα : 2 * α < 1) :
    ∃ β₀ : ℝ, 3 ≤ β₀ ∧ ∀ T : StepTower κmin, T.m₁ = T₀.m₁ → T.BG = T₀.BG → T.BG₂ = T₀.BG₂ →
      T.κ = T₀.κ → ∀ k : ℕ, 1 ≤ k → ∀ β p₁ : ℝ, β₀ ≤ β → 0 < p₁ →
      p₁ ≤ pLog A₁ p (β * 3 ^ k) → c * (3 : ℝ) ^ (-(α * ((k : ℝ) + 1))) ≤ T.t →
      R₀ ≤ corrR T k (β * 3 ^ k) p₁ ∧ corrF0 T k β p₁ ≤ 1 := by
  obtain ⟨β₀, h3, H⟩ := exists_beta0_closureG_agree (N := 2) (κmin := κmin) (by norm_num)
    (by norm_num) T₀.toG hA p hc hR₀ (alpha_three_cast hα)
  have hb : ∀ (k : ℕ) (β : ℝ), β * ((3 : ℕ) : ℝ) ^ (k * (3 - 2)) = β * 3 ^ k := by
    intro k β; norm_num
  refine ⟨β₀, h3, fun T hm₁ hBG hBG₂ hκ k hk β p₁ hβ hp hp₁ hct => ?_⟩
  obtain ⟨h0, hdec, h'⟩ := StepTower.agree_rates T₀ T
  have := H T.toG hBG hBG₂ hκ hdec hm₁ k hk β p₁ hβ hp (by rw [hb]; exact hp₁)
    (by rw [radius_three_cast]; exact hct)
  rw [hb, ← corrR_toG] at this
  rw [corrF0_toG]
  exact this

end Balaban.Inhabited
