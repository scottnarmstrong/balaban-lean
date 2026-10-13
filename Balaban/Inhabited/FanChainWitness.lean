/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.MarkedDecBall
public import Balaban.Fluctuation.HatEngineFan
public import Balaban.Fluctuation.ScaleUniform
public import Balaban.Fluctuation.Prop33SymmV
public import Balaban.Inhabited.MarkedSharpCountWitness
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

/-!
# Instances of the fan-level theorems at the zero-class witness step

PLACEHOLDER DOC (replaced below).
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation
  Balaban.Localization Balaban.Localization.LevelPair Balaban.Localization.I5Inhabited
  Balaban.Polymer Balaban.SmallField.Def6

open Classical in
/-- **Instance of `hatPsiF_mem_flBallLC` at the witness step.** -/
theorem fanChain_ball :
    ∃ (m₁ : ℕ) (BG κ t δ β₀ : ℝ), 2 ≤ β₀ ∧ 0 < t ∧ 0 < κ ∧
      ∀ β : ℝ, β₀ ≤ β → ∃ cψ : ℝ, 0 < cψ ∧
        XiCData (wStep m₁ β δ).G' (compWeight 3 1) nuW (1 + 1) 1 t (wStep m₁ β δ).D' ∧
        (∃ s : DecParams (wStep m₁ β δ).G', ∀ P, ‖s P‖ < Real.exp κ) ∧
        ∃ F₁ : DecParams (wStep m₁ β δ).G' × RawData 3 3 (9 * 3 ^ m₁) (1 + 1) 2 →
            ((wStep m₁ β δ).G'.Ω 1 × Fin 2 → ℂ) × ((wStep m₁ β δ).G'.Ω 1 → ℂ),
          F1Spec (wStep m₁ β δ).G' 1 nuW BG κ F₁ ∧
          ∀ s : DecParams (wStep m₁ β δ).G', (∀ P, ‖s P‖ < Real.exp κ) →
            ∀ D : BgData (wStep m₁ β δ).G' 2, XiCData (wStep m₁ β δ).G' (compWeight 3 1) nuW
              (1 + 1) 1 t D → ∀ ψh : unitPts (wStep m₁ β δ).G' × Fin 2 → ℂ, (∀ p, ‖ψh p‖ ≤ cψ) →
            hatPsiF (wStep m₁ β δ).G' 1 nuW (wStep m₁ β δ).hG'
              ((((wStep m₁ β δ).betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) F₁ s (rawOf D) ψh ∈
              FlBallLC (Hm m₁ (rhoSep m₁)) t := by
  classical
  obtain ⟨-, δ, δ', T, -, -, hδ, hsm, hδ'0, hδ'a, hδ'b, hδ'c, hT, -, hT1, hT2⟩ :=
    exists_witness_params (fun _ => 0)
  obtain ⟨m₁, c, BG, κ, t, c₂, BG₂, κdec, κ0, δc, h4, ht0, ⟨hC⟩, hκ0, hκdec, hκ, h1, hlog, hc7,
    hMX, hdm, hα, hsmX, g1, g2, g3, g4, g5, hκE, hκa, hB0⟩ := tower_core_fixed 2
  have hκdec0 : 0 ≤ κdec := by linarith
  have hκ_nn : 0 ≤ κ := le_trans (by positivity) hκ
  have hbig : cstarX 3 3 ≤ (3 : ℝ) ^ m₁ := by
    have h := Localization.cstarX_pos 3 3
    have h2 : cstarX 3 3 ≤ cstarX 3 3 * Real.exp ((N0 3 3 : ℝ) * κ) :=
      le_mul_of_one_le_right h.le (Real.one_le_exp (by positivity))
    have h3 : ((3 : ℕ) : ℝ) ^ m₁ = (3 : ℝ) ^ m₁ := by norm_num
    linarith
  have hκpos : 0 < κ := by
    have : 0 < κdec := by linarith
    have h5 : (0 : ℝ) < 4 * ((3 : ℕ) : ℝ) * (((2 * 3 + 1) ^ 3 : ℕ) : ℝ) * κdec := by positivity
    linarith
  obtain ⟨β₀t, hβ₀t, hitems⟩ := tower_C_items (A₁ := 1) one_pos 2 m₁ h4 hbig κ ht0 hδ hsm hδ'0
    hδ'a hδ'b hδ'c
  refine ⟨m₁, BG, κ, t, δ, β₀t, hβ₀t, ht0, hκpos, ?_⟩
  intro β hβ
  obtain ⟨hp, hcψ0, hr0, hδ₁, hc, hlt, ⟨R0⟩⟩ := hitems β hβ
  have hxi1 : xiC1 3 * t ≤ 1 := by
    have h1 := hC.c7le
    have h2 := c7_le_bgC1 3 3 2 BG κ
    have h3 := bgC1_le_small 3 3 2 (by norm_num)
    linarith
  have hD : XiCData (wStep m₁ β δ).G' (compWeight 3 1) nuW (1 + 1) 1 t (wStep m₁ β δ).D' := by
    refine ⟨fun _ => unitVec hN2, unitVec hN2, 0, 0,
      exists_xiC (bgHypNu m₁) (Gp m₁ (rhoSep m₁)) hN2 (by unfold nuW; norm_num) ht0, ?_, ?_⟩
    · intro x hx i
      have := unitBg_Ψ_of_mem (Gp m₁ (rhoSep m₁)) hN2 (unitVec hN2) hx i
      show (unitBg (Gp m₁ (rhoSep m₁)) hN2 (unitVec hN2)).Ψ x i = _
      rw [this]; simp
    · intro x hx i
      have := unitBg_h_of_mem (Gp m₁ (rhoSep m₁)) hN2 (unitVec hN2) hx i
      show (unitBg (Gp m₁ (rhoSep m₁)) hN2 (unitVec hN2)).h x i = _
      rw [this]; simp
  obtain ⟨F₁, hF₁⟩ := f1Spec_exists hC
  refine ⟨towerCpsi κ t β, hcψ0, hD, ⟨fun _ => 1, fun P => ?_⟩, F₁, hF₁, ?_⟩
  · simpa using Real.one_lt_exp_iff.2 hκpos
  · intro s hs D hDD ψh hψh
    exact hatPsiF_mem_flBallLC hC le_rfl isLevel_Hm (wStep m₁ β δ).hG' _ hcψ0.le hMX hdm hα hsmX
      hδ₁ hF₁ hs hDD hψh

open Classical in
/-- **Instance of `markedHatPsiF_mem_flBallLC` at the witness step.**  The hat variable is bounded
by the cutoff `p₁ = pLog 1 2 β`; the marked parameters range over `|u| ≤ 2` and `|t| ≤ t₁` with
`t₁ = 8 p₁ / c_ψ > 0` (so a non-trivial disc of `t`), where the radius inequality is the one of
`marked_radius_and_derivative_at_witness`. -/
theorem fanChain_markedBall :
    ∃ (m₁ : ℕ) (BG κ t δ β₀ : ℝ), 2 ≤ β₀ ∧ 0 < t ∧ 0 < κ ∧
      ∀ β : ℝ, β₀ ≤ β → ∃ t₁ : ℝ, 0 < t₁ ∧
        ∃ F₁ : DecParams (wStep m₁ β δ).G' × RawData 3 3 (9 * 3 ^ m₁) (1 + 1) 2 →
            ((wStep m₁ β δ).G'.Ω 1 × Fin 2 → ℂ) × ((wStep m₁ β δ).G'.Ω 1 → ℂ),
          F1Spec (wStep m₁ β δ).G' 1 nuW BG κ F₁ ∧
          ∀ (z : Torus 3 (9 * 3 ^ m₁ * 3 ^ (1 + 1 - (1 + 1)))),
          ∀ s : DecParams (wStep m₁ β δ).G', (∀ P, ‖s P‖ < Real.exp κ) →
            ∀ D : BgData (wStep m₁ β δ).G' 2, XiCData (wStep m₁ β δ).G' (compWeight 3 1) nuW
              (1 + 1) 1 t D → ∀ ψh : unitPts (wStep m₁ β δ).G' × Fin 2 → ℂ,
              (∀ p, ‖ψh p‖ ≤ pLog 1 2 β) → ∀ u τ : ℂ, ‖u‖ ≤ 2 → ‖τ‖ ≤ t₁ →
            markedHatPsiF (wStep m₁ β δ).a₁ (wStep m₁ β δ).ν (wStep m₁ β δ).hG'
              ((((wStep m₁ β δ).betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) F₁
              ((wStep m₁ β δ).blockU z) u τ s (rawOf D) ψh ∈
              FlBallLC (Hm m₁ (rhoSep m₁)) t := by
  classical
  obtain ⟨-, δ, δ', T, -, -, hδ, hsm, hδ'0, hδ'a, hδ'b, hδ'c, hT, -, hT1, hT2⟩ :=
    exists_witness_params (fun _ => 0)
  obtain ⟨m₁, c, BG, κ, t, c₂, BG₂, κdec, κ0, δc, h4, ht0, ⟨hC⟩, hκ0, hκdec, hκ, h1, hlog, hc7,
    hMX, hdm, hα, hsmX, g1, g2, g3, g4, g5, hκE, hκa, hB0⟩ := tower_core_fixed 2
  have hκdec0 : 0 ≤ κdec := by linarith
  have hκ_nn : 0 ≤ κ := le_trans (by positivity) hκ
  have hbig : cstarX 3 3 ≤ (3 : ℝ) ^ m₁ := by
    have h := Localization.cstarX_pos 3 3
    have h2 : cstarX 3 3 ≤ cstarX 3 3 * Real.exp ((N0 3 3 : ℝ) * κ) :=
      le_mul_of_one_le_right h.le (Real.one_le_exp (by positivity))
    have h3 : ((3 : ℕ) : ℝ) ^ m₁ = (3 : ℝ) ^ m₁ := by norm_num
    linarith
  have hκpos : 0 < κ := by
    have : 0 < κdec := by linarith
    have h5 : (0 : ℝ) < 4 * ((3 : ℕ) : ℝ) * (((2 * 3 + 1) ^ 3 : ℕ) : ℝ) * κdec := by positivity
    linarith
  obtain ⟨β₀t, hβ₀t, hitems⟩ := tower_C_items (A₁ := 1) one_pos 2 m₁ h4 hbig κ ht0 hδ hsm hδ'0
    hδ'a hδ'b hδ'c
  refine ⟨m₁, BG, κ, t, δ, β₀t, hβ₀t, ht0, hκpos, ?_⟩
  intro β hβ
  obtain ⟨hp, hcψ0, hr0, hδ₁, hc, hlt, ⟨R0⟩⟩ := hitems β hβ
  obtain ⟨F₁, hF₁⟩ := f1Spec_exists hC
  set p₁ := pLog 1 2 β with hp₁def
  set cψ := towerCpsi κ t β with hcψdef
  set W : ℝ := Real.sqrt ((2 : ℕ) : ℝ) *
    (‖(((hatStep m₁ β p₁ δ).betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)‖ *
      covSupConstC 3 3 2 (compWeight 3 (1 : ℝ) 1) κ) with hW
  have ha : 0 < compWeight 3 (1 : ℝ) 1 :=
    lt_of_lt_of_le (by norm_num) (hC.HBp.weights 1 le_rfl (by norm_num)).1
  have hCs := covSupConstC_nonneg (N := 2) (d := 3) (L := 3) (by norm_num) (by norm_num) ha κ
  have hW0 : 0 ≤ W := by
    rw [hW]; positivity
  have hWc : W * cψ < t := by rw [hW]; nlinarith [hδ₁]
  set t₁ : ℝ := 8 * p₁ / cψ with ht₁
  have ht₁0 : 0 < t₁ := by positivity
  have hmain : (2 + towerR κ t β p₁) * (2 + t₁) * p₁ ≤ cψ := by
    have e : (2 + towerR κ t β p₁) * (2 + t₁) * p₁ = cψ - 16 * p₁ ^ 2 / cψ := by
      unfold towerR
      rw [ht₁]
      field_simp
      ring
    rw [e]
    have : 0 ≤ 16 * p₁ ^ 2 / cψ := by positivity
    linarith
  have hrad : (2 + t₁) * (W * p₁) < t := by
    have hr' : 0 ≤ towerR κ t β p₁ := hr0.le
    have h2 : (2 + t₁) * (W * p₁) ≤ (2 + towerR κ t β p₁) * (2 + t₁) * (W * p₁) := by
      have : 0 ≤ (2 + t₁) * (W * p₁) := by positivity
      have h3 : 1 ≤ 2 + towerR κ t β p₁ := by linarith
      calc (2 + t₁) * (W * p₁) = 1 * ((2 + t₁) * (W * p₁)) := by ring
        _ ≤ (2 + towerR κ t β p₁) * ((2 + t₁) * (W * p₁)) := mul_le_mul_of_nonneg_right h3 this
        _ = _ := by ring
    refine lt_of_le_of_lt h2 ?_
    calc (2 + towerR κ t β p₁) * (2 + t₁) * (W * p₁)
        = ((2 + towerR κ t β p₁) * (2 + t₁) * p₁) * W := by ring
      _ ≤ cψ * W := mul_le_mul_of_nonneg_right hmain hW0
      _ = W * cψ := by ring
      _ < t := hWc
  refine ⟨t₁, ht₁0, F₁, hF₁, ?_⟩
  intro z s hs D hDD ψh hψh u τ hu hτ
  refine markedHatPsiF_mem_flBallLC hC le_rfl isLevel_Hm (wStep m₁ β δ).hG' _ (cψ := p₁) hp.le
    hMX hdm hα hsmX hF₁ hs hDD hψh _ ?_
  have hn : ‖u‖ + ‖τ‖ ≤ 2 + t₁ := add_le_add hu hτ
  refine lt_of_le_of_lt (mul_le_mul_of_nonneg_right hn (by have := hp.le; positivity)) ?_
  have e : Real.sqrt ((2 : ℕ) : ℝ) *
      (‖(((wStep m₁ β δ).betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)‖ *
        (covSupConstC 3 3 2 (compWeight 3 (1 : ℝ) 1) κ * p₁)) = W * p₁ := by
    rw [hW]; ring
  rw [e]; exact hrad

end Balaban.Inhabited
