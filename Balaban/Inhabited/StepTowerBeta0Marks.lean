/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.StepTowerBeta0Scale
public import Balaban.Inhabited.MarkCorrBudgetTBudget
public import Balaban.Inhabited.E1LabelsBudget
public import Balaban.Inhabited.StepTowerChainStructAmp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

/-!
# The marks thresholds of the class chain, uniformly in the step radius

For towers that agree with a reference tower `T₀` on `m₁, BG, BG₂, κ` (hence on `κ₀, κ_dec, κ'`)
and every radius `t ≥ c L^{-α(k+1)}`, `2 α < d - 2`: `exists_beta0_e1G_agree`,
`exists_beta0_e1_agree` (the Cauchy radius and the budget of the corrected marks),
`exists_beta0_corrR_agree`, `StepTower.scale_agree`.
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation
  Balaban.Localization Balaban.Localization.LevelPair Balaban.Localization.I5Inhabited
  Balaban.Polymer Balaban.SmallField.Def6 Balaban.Inhabited.LevelStep
  Balaban.Inhabited.MarkBudgetAudit

/-- **One threshold for the marks record, uniformly in the step radius** (general tower). -/
theorem exists_beta0_e1G_agree {d L N : ℕ} [NeZero L] {κmin : ℝ} (T₀ : StepTowerG d L N κmin)
    (hm₀ : T₀.m₀ = 1) {A₁ : ℝ} (hA : 0 < A₁) (p : ℕ) {c α : ℝ} (hc : 0 < c)
    (hα : 2 * α < ((d - 2 : ℕ) : ℝ)) (βa : ℝ) :
    ∃ β₀ : ℝ, max 3 βa ≤ β₀ ∧ ∀ T : StepTowerG d L N κmin, T.m₀ = T₀.m₀ → T.m₁ = T₀.m₁ →
      T.BG = T₀.BG → T.BG₂ = T₀.BG₂ → T.κ = T₀.κ → T.κ0 = T₀.κ0 → T.κ' = T₀.κ' →
      T.κdec = T₀.κdec →
      (∀ k : ℕ, 1 ≤ k → ∀ β : ℝ, β₀ ≤ β →
        c * (L : ℝ) ^ (-(α * ((k : ℝ) + 1))) ≤ T.t → ∀ p₁ : ℝ, 0 < p₁ →
        p₁ ≤ pLog A₁ p (β * (L : ℝ) ^ (k * (d - 2))) →
        2 * (17 / 16 : ℝ) ≤ corrRG T k (β * (L : ℝ) ^ (k * (d - 2))) p₁) ∧
      ∀ (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁], L ^ T.m₀ ∣ N₁ →
        ∀ (ν β : ℝ), β₀ ≤ β → c * (L : ℝ) ^ (-(α * ((k : ℝ) + 1))) ≤ T.t →
        ∀ p₁ : ℝ, 0 < p₁ →
        p₁ ≤ pLog A₁ p (β * (L : ℝ) ^ (k * (d - 2))) →
        StepScaleDataG T k hk N₁ ν β p₁ →
        ∀ {ϱ : ℝ}, ϱ = rhoSepG d L T.m₁ → ∀ z : RootIdx d L N₁ T.m₁ (k + 1),
          CPE d L (2 * (K0 d L T.κ0 + 1) + rootUnionK d L T.m₀ T.m₁ T.κ0) (2 * T.κdec - 1)
              T.κ0 T.κ' *
            (∑ Y' : {Y' // Y' ∈ bridgeFamily 1 (fun _ => Set.univ)
                (e1DomG (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ)) z},
              corrF0G T k β p₁ * Real.exp (-T.κ0 * treeLenCovOne 1 (k + 1) Y'.1)) ≤
            K0 d L T.κ0 := by
  obtain ⟨βR, -, hR⟩ := exists_beta0_corrRT (N := N) (κmin := κmin) T₀.hd T₀.hL hA.le p
    (Cc := covSupMaxC d L N T₀.κ) (c := c) (α := α) (covSupMaxC_nonneg_general (by have := T₀.hd; omega)
      T₀.hL T₀.κ) hc hα
  obtain ⟨βF, -, hF⟩ := corrBudget_fromTowerT_agree T₀ hA.le p hc hα
  refine ⟨max (max 3 βa) (max βR βF), le_max_left _ _, fun T hm₀' hm₁ hBG hBG₂ hκ hκ0 hκ' hκdec => ?_⟩
  refine ⟨fun k hk β hβ hct p₁ hp hp₁ => ?_, fun k hk N₁ _ hdvd ν β hβ hct p₁ hp hp₁ D ϱ hϱ z => ?_⟩
  · exact hR T k hk β p₁ ((le_max_left _ _).trans ((le_max_right _ _).trans hβ)) hp hp₁
      (by rw [hκ]) hct
  · exact hF T (hm₀'.trans hm₀) hm₀' hm₁ hBG hBG₂ hκ hκ0 hκ' hκdec k hk N₁ hdvd ν β
      ((le_max_right _ _).trans ((le_max_right _ _).trans hβ)) p₁ hp hp₁ hct D hϱ z

/-- The rates `κ₀`, `κ_dec`, `κ'` are the same for all towers. -/
theorem StepTower.agree_rates {κmin : ℝ} (T T' : StepTower κmin) :
    T'.κ0 = T.κ0 ∧ T'.κdec = T.κdec ∧ T'.κ' = T.κ' := by
  have h0 : T'.κ0 = T.κ0 := by rw [T'.κ0_eq, T.κ0_eq]
  have hd : T'.κdec = T.κdec := by rw [T'.κdec_eq, T.κdec_eq, h0]
  exact ⟨h0, hd, by rw [T'.κ'_eq, T.κ'_eq, h0, hd]⟩

theorem radius_three_cast (c α : ℝ) (k : ℕ) :
    c * ((3 : ℕ) : ℝ) ^ (-(α * ((k : ℝ) + 1))) = c * (3 : ℝ) ^ (-(α * ((k : ℝ) + 1))) := by
  norm_num

theorem alpha_three_cast {α : ℝ} (hα : 2 * α < 1) : 2 * α < (((3 : ℕ) - 2 : ℕ) : ℝ) := by
  norm_num; exact hα

/-- **One threshold for the marks record, uniformly in the step radius** (the tower at
`d = L = 3`, `N = 2`). -/
theorem exists_beta0_e1_agree {κmin : ℝ} (T₀ : StepTower κmin) {A₁ : ℝ} (hA : 0 < A₁) (p : ℕ)
    {c α : ℝ} (hc : 0 < c) (hα : 2 * α < 1) (βa : ℝ) :
    ∃ β₀ : ℝ, max 3 βa ≤ β₀ ∧ ∀ T : StepTower κmin, T.m₁ = T₀.m₁ → T.BG = T₀.BG →
      T.BG₂ = T₀.BG₂ → T.κ = T₀.κ →
      (∀ k : ℕ, 1 ≤ k → ∀ β : ℝ, β₀ ≤ β → c * (3 : ℝ) ^ (-(α * ((k : ℝ) + 1))) ≤ T.t →
        ∀ p₁ : ℝ, 0 < p₁ → p₁ ≤ pLog A₁ p (β * 3 ^ k) → 2 * corrU ≤ corrR T k (β * 3 ^ k) p₁) ∧
      ∀ (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁], 3 ∣ N₁ →
        ∀ (ν β : ℝ), β₀ ≤ β → c * (3 : ℝ) ^ (-(α * ((k : ℝ) + 1))) ≤ T.t →
        ∀ p₁ : ℝ, 0 < p₁ → p₁ ≤ pLog A₁ p (β * 3 ^ k) →
        StepScaleData T k hk N₁ ν β p₁ →
        ∀ z : RootIdx 3 3 N₁ T.m₁ (k + 1),
          CPE 3 3 T.marksKc' (2 * T.κdec - 1) T.κ0 T.κ' *
            (∑ Y' : {Y' // Y' ∈ bridgeFamily 1 (fun _ => Set.univ)
                (e1Dom (T.step k hk N₁ ν β p₁)) z},
              corrF0 T k β p₁ * Real.exp (-T.κ0 * treeLenCovOne 1 (k + 1) Y'.1)) ≤
            K0 3 3 T.κ0 := by
  obtain ⟨β₀, hβ₀, H⟩ := exists_beta0_e1G_agree T₀.toG rfl hA p hc (alpha_three_cast hα) βa
  have hb : ∀ (k : ℕ) (β : ℝ), β * ((3 : ℕ) : ℝ) ^ (k * (3 - 2)) = β * 3 ^ k := by
    intro k β; norm_num
  refine ⟨β₀, hβ₀, fun T hm₁ hBG hBG₂ hκ => ?_⟩
  obtain ⟨h0, hdec, h'⟩ := StepTower.agree_rates T₀ T
  obtain ⟨hR, hF⟩ := H T.toG rfl hm₁ hBG hBG₂ hκ h0 h' hdec
  refine ⟨fun k hk β hβ hct p₁ hp hp₁ => ?_, fun k hk N₁ _ h3N ν β hβ hct p₁ hp hp₁ D z => ?_⟩
  · have := hR k hk β hβ (by rw [radius_three_cast]; exact hct) p₁ hp (by rw [hb]; exact hp₁)
    rw [hb, ← corrR_toG] at this
    exact this
  · have := hF k hk N₁ (by simpa using h3N) ν β hβ (by rw [radius_three_cast]; exact hct) p₁ hp
      (by rw [hb]; exact hp₁) (T.scaleDataG_of_fixed D) (ϱ := rhoSep T.m₁)
      (rhoSepG_three _).symm z
    simp only [corrF0_toG]
    exact this

/-- **The tower at every scale, uniformly in the step radius** (the tower at `d = L = 3`,
`N = 2`). -/
theorem StepTower.scale_agree {κmin : ℝ} (T₀ : StepTower κmin) {A₁ : ℝ} (hA : 0 < A₁) (p : ℕ)
    {c α : ℝ} (hc : 0 < c) (hα : 2 * α < 1) :
    ∃ βray : ℝ, 3 ≤ βray ∧ ∀ T : StepTower κmin, T.κ = T₀.κ → T.δ = T₀.δ →
      ∀ (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁], 3 ∣ N₁ → 5 < N₁ →
      ∀ ν : ℝ, 0 ≤ ν → ν * 3 ^ (2 * (k + 1)) ≤ 1 → ∀ β : ℝ, βray ≤ β →
      c * (3 : ℝ) ^ (-(α * ((k : ℝ) + 1))) ≤ T.t →
      ∀ p₁ : ℝ, 0 < p₁ → p₁ ≤ pLog A₁ p (β * 3 ^ k) →
      Nonempty (StepScaleData T k hk N₁ ν β p₁) := by
  obtain ⟨βray, h3, h⟩ := StepTowerG.scale_agree T₀.toG hA p hc (alpha_three_cast hα)
  refine ⟨βray, h3, ?_⟩
  intro T hκ hδ k hk N₁ _ h3N hN ν hν0 hν β hβ hct p₁ hp0 hp₁
  have hb : β * ((3 : ℕ) : ℝ) ^ (k * (3 - 2)) = β * 3 ^ k := by norm_num
  have h3 : 3 ^ T.toG.m₀ ∣ N₁ := by simpa using h3N
  obtain ⟨hS⟩ := h T.toG hκ hδ k hk N₁ h3 hN ν hν0 (by simpa using hν) β hβ
    (by rw [radius_three_cast]; exact hct) p₁ hp0 (by simpa [hb] using hp₁)
  exact ⟨T.scaleData_of_toG hS⟩

end Balaban.Inhabited
