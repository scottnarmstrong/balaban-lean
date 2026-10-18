/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.E1LabelsBudgetG
public import Balaban.Inhabited.MarkCorrBudgetT
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

/-!
# The budget of the corrected marks at the step radius `t`

`corrBudget_fromTowerG` with the threshold uniform in the step radius: one `β₀`, depending on
`A₁, p, M, c, α, P` only, gives `C_PE ∑ F₀ e^{-κ₀ d} ≤ K₀` at every scale `k`, for every tower with
`CcorrG * t ≤ M` and `C_PE ≤ P` (both are the same for towers that agree except for `t`) and every
radius `t ≥ c L^{-α(k+1)}`, `2 α < d - 2`.  The threshold is `b ≳ t^{-2} (log b)^{6p}`.
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation
  Balaban.Localization Balaban.Localization.LevelPair Balaban.Localization.I5Inhabited
  Balaban.Polymer Balaban.SmallField.Def6 Balaban.Inhabited.LevelStep
  Balaban.Inhabited.MarkBudgetAudit

open Classical in
/-- **The budget of the marks, uniformly in the step radius.** -/
theorem corrBudget_fromTowerT {d L N : ℕ} [NeZero L] {κmin : ℝ} (hd : 3 ≤ d) (hL : 3 ≤ L)
    {A₁ : ℝ} (hA : 0 ≤ A₁) (p : ℕ) {M c α P : ℝ} (hM : 0 ≤ M) (hc : 0 < c) (hP : 0 ≤ P)
    (hα : 2 * α < ((d - 2 : ℕ) : ℝ)) :
    ∃ β₀ : ℝ, 3 ≤ β₀ ∧ ∀ (T : StepTowerG d L N κmin), T.m₀ = 1 →
      CcorrG T * T.t ≤ M → CPE d L (2 * (K0 d L T.κ0 + 1) + rootUnionK d L T.m₀ T.m₁ T.κ0)
        (2 * T.κdec - 1) T.κ0 T.κ' ≤ P →
      ∀ (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁], L ^ T.m₀ ∣ N₁ →
      ∀ (ν β : ℝ), β₀ ≤ β → ∀ p₁ : ℝ, 0 < p₁ →
      p₁ ≤ pLog A₁ p (β * (L : ℝ) ^ (k * (d - 2))) →
      c * (L : ℝ) ^ (-(α * ((k : ℝ) + 1))) ≤ T.t →
      StepScaleDataG T k hk N₁ ν β p₁ →
      ∀ {ϱ : ℝ}, ϱ = rhoSepG d L T.m₁ → ∀ z : RootIdx d L N₁ T.m₁ (k + 1),
        CPE d L (2 * (K0 d L T.κ0 + 1) + rootUnionK d L T.m₀ T.m₁ T.κ0) (2 * T.κdec - 1)
            T.κ0 T.κ' *
          (∑ Y' : {Y' // Y' ∈ bridgeFamily 1 (fun _ => Set.univ)
              (e1DomG (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ)) z},
            corrF0G T k β p₁ * Real.exp (-T.κ0 * treeLenCovOne 1 (k + 1) Y'.1)) ≤
          K0 d L T.κ0 := by
  have hε : 0 < 1 / (P + 1) := by positivity
  obtain ⟨β₀, h3, h⟩ := exists_beta0_corrF0_leT (N := N) (κmin := κmin) hd hL hε hA p hM hc hα
  refine ⟨β₀, h3, fun T hm₀ hCt hPT k hk N₁ _ hdvd ν β hβ p₁ hp hp₁ hct D ϱ hϱ z => ?_⟩
  have hP' := cpe_marks_nonnegG T
  have hβ0 : 0 < β := by linarith
  have hF := h T k hk β p₁ hβ hp hp₁ hCt hct
  have hF0 := (corrF0G_pos T hk hβ0 hp).le
  have hdvd1 : L ^ 1 ∣ N₁ := by rwa [hm₀] at hdvd
  have hent := bridgeFamily_entropy (m₀ := 1) (d := d) (L := L) hdvd1
    (by have := T.hL; omega) (reads := fun _ => Set.univ)
    (e1DomG_isDj T hm₀ D hϱ) z T.marks_hκ0 hF0
  have hK := K0_pos d L T.κ0
  generalize CPE d L (2 * (K0 d L T.κ0 + 1) + rootUnionK d L T.m₀ T.m₁ T.κ0)
    (2 * T.κdec - 1) T.κ0 T.κ' = Cp at hP' hPT hent ⊢
  generalize corrF0G T k β p₁ = F at hF hF0 hent ⊢
  generalize K0 d L T.κ0 = K0v at hK hent ⊢
  have h1 : F * K0v ≤ 1 / (P + 1) * K0v := mul_le_mul_of_nonneg_right hF hK.le
  have h2 : Cp * (1 / (P + 1)) ≤ 1 := by
    rw [mul_one_div, div_le_one (by positivity)]
    linarith
  calc _ ≤ Cp * (F * K0v) := mul_le_mul_of_nonneg_left hent hP'
    _ ≤ Cp * (1 / (P + 1) * K0v) := mul_le_mul_of_nonneg_left h1 hP'
    _ = (Cp * (1 / (P + 1))) * K0v := by ring
    _ ≤ 1 * K0v := mul_le_mul_of_nonneg_right h2 hK.le
    _ = K0v := one_mul _

open Classical in
/-- **The budget along towers that agree with a reference tower except for `t`.**  One `β₀`
(depending on the reference tower, `A₁, p, c, α`) gives the budget at every scale for every tower
`T` with the same `BG, BG₂, κ, κ₀, κ', κ_dec, m₀, m₁` and every radius `t ≥ c L^{-α(k+1)}`. -/
theorem corrBudget_fromTowerT_agree {d L N : ℕ} [NeZero L] {κmin : ℝ} (T₀ : StepTowerG d L N κmin)
    {A₁ : ℝ} (hA : 0 ≤ A₁) (p : ℕ) {c α : ℝ} (hc : 0 < c)
    (hα : 2 * α < ((d - 2 : ℕ) : ℝ)) :
    ∃ β₀ : ℝ, 3 ≤ β₀ ∧ ∀ (T : StepTowerG d L N κmin), T.m₀ = 1 → T.m₀ = T₀.m₀ →
      T.m₁ = T₀.m₁ → T.BG = T₀.BG → T.BG₂ = T₀.BG₂ → T.κ = T₀.κ → T.κ0 = T₀.κ0 →
      T.κ' = T₀.κ' → T.κdec = T₀.κdec →
      ∀ (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁], L ^ T.m₀ ∣ N₁ →
      ∀ (ν β : ℝ), β₀ ≤ β → ∀ p₁ : ℝ, 0 < p₁ →
      p₁ ≤ pLog A₁ p (β * (L : ℝ) ^ (k * (d - 2))) →
      c * (L : ℝ) ^ (-(α * ((k : ℝ) + 1))) ≤ T.t →
      StepScaleDataG T k hk N₁ ν β p₁ →
      ∀ {ϱ : ℝ}, ϱ = rhoSepG d L T.m₁ → ∀ z : RootIdx d L N₁ T.m₁ (k + 1),
        CPE d L (2 * (K0 d L T.κ0 + 1) + rootUnionK d L T.m₀ T.m₁ T.κ0) (2 * T.κdec - 1)
            T.κ0 T.κ' *
          (∑ Y' : {Y' // Y' ∈ bridgeFamily 1 (fun _ => Set.univ)
              (e1DomG (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ)) z},
            corrF0G T k β p₁ * Real.exp (-T.κ0 * treeLenCovOne 1 (k + 1) Y'.1)) ≤
          K0 d L T.κ0 := by
  have hM : 0 ≤ CcorrG T₀ * T₀.t := mul_nonneg (CcorrG_nonneg T₀) T₀.t_pos.le
  have hP : 0 ≤ CPE d L (2 * (K0 d L T₀.κ0 + 1) + rootUnionK d L T₀.m₀ T₀.m₁ T₀.κ0)
      (2 * T₀.κdec - 1) T₀.κ0 T₀.κ' := by
    have := cpe_marks_nonnegG T₀
    exact this
  obtain ⟨β₀, h3, h⟩ := corrBudget_fromTowerT (N := N) (κmin := κmin) T₀.hd T₀.hL hA p hM hc hP hα
  refine ⟨β₀, h3, fun T hm₀ hm0 hm1 hBG hBG₂ hκ hκ0 hκ' hκdec => ?_⟩
  have hCt : CcorrG T * T.t ≤ CcorrG T₀ * T₀.t :=
    (CcorrG_mul_t_eq T₀ T hBG hBG₂ hκ hκdec hm1).le
  have hPT : CPE d L (2 * (K0 d L T.κ0 + 1) + rootUnionK d L T.m₀ T.m₁ T.κ0)
      (2 * T.κdec - 1) T.κ0 T.κ' ≤ CPE d L (2 * (K0 d L T₀.κ0 + 1) +
        rootUnionK d L T₀.m₀ T₀.m₁ T₀.κ0) (2 * T₀.κdec - 1) T₀.κ0 T₀.κ' := by
    rw [hm0, hm1, hκ0, hκ', hκdec]
  exact h T hm₀ hCt hPT

end Balaban.Inhabited
