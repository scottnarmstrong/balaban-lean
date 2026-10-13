/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.RenormDecAnalytic
public import Balaban.Fluctuation.RenormExpBounds
public import Balaban.Fluctuation.RenormExpLemma35
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Class bound for the shifted perturbation, at every complex cut

For the analytic family `F` of `renDec_sharp`, at every datum of `XiCOneReal`, every `ξ` with
`‖ξ‖ < r₀` and every cut `s` of the polydisc, the pair `(δφ, α_s + δα)` lies in
`pertClass G V A ν_u` and `δφ` satisfies `SupBounds G δφ V`, where `V = c_K C₂ B ‖ξ‖`,
`A = K₁ δ + c_K C₂ B r₀ + 2`, in the form quantified by the fields `locC2` and `locDφ` of
`RenormExpInput`.  The hypothesis is the constant inequality `C₂' b_* ε ≤ c_K C₂ B` (CB); it holds
as soon as `c_K` is at least the quotient (`renPertClass_CB_of_quotient_le`).

Not here: the endpoint `s = 1`, locality, `locC2` and `locDφ`.
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation
  Balaban.Analysis Finset

variable {d L N₁ m₁ K N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱm : ℝ}
variable {Gp : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {Hm : GeneratingSet d L (N₁ * L ^ m₁) K ϱm}
variable {a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁ : ℝ}

/-- The arithmetic of (CB): if `c_K ≥ C₂' b_* ε / (C₂ B)` and `C₂ B > 0`, then
`C₂' b_* ε ≤ c_K C₂ B`. -/
theorem renPertClass_CB_of_quotient_le {cK2' b eps cK cK2 B : ℝ} (hpos : 0 < cK2 * B)
    (hcK : cK2' * b * eps / (cK2 * B) ≤ cK) : cK2' * b * eps ≤ cK * cK2 * B := by
  have := (div_le_iff₀ hpos).1 hcK
  linarith

/-- **Class bound, family-free form.**  If `(δφ, δα)` obeys the two sharp bounds at `‖ξ‖`
and (CB) holds, then the pair is in `pertClass`. -/
theorem renPertClass_of_sharp
    (hC : FlCore N Gp Hm a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁) {r₀ : ℝ} (hr₀0 : 0 < r₀)
    (hr₀ : r₀ ≤ 1 / 16)
    (hD₀ : 2 * (K4 d L N BG κ * (xiC1 d * eps)) + 3 * r₀ ≤ 1)
    {B cK : ℝ} (hB0 : 0 ≤ B) (hcK : 1 ≤ cK)
    (hCB : cK2' d L N (famConst d L BG κ) *
      ((3 / 2 + 32 / 15 * (3 + (K4 d L N BG κ + bgK1 d L N) * xiC1 d)) * eps) ≤
        cK * cK2 d L N * B)
    {D : BgData Gp N} (hD : XiCOneReal Gp (compWeight L a₁) ν eps D) {ξ : Fin 3 → ℂ}
    (hξ : ‖ξ‖ < r₀) {s' : DecParams Gp} (hs : ∀ P, ‖s' P‖ ≤ Real.exp κ)
    {δφ : Gp.Ω 1 × Fin N → ℂ} {δα : Gp.Ω 1 → ℂ}
    (hsm : Small Gp δα (cK2' d L N (famConst d L BG κ) *
      ((3 / 2 + 32 / 15 * (3 + (K4 d L N BG κ + bgK1 d L N) * xiC1 d)) * eps * ‖ξ‖)))
    (hsup : SupBounds Gp δφ (cK2' d L N (famConst d L BG κ) *
      ((3 / 2 + 32 / 15 * (3 + (K4 d L N BG κ + bgK1 d L N) * xiC1 d)) * eps * ‖ξ‖))) :
    SupBounds Gp δφ (cK * (cK2 d L N * (B * ‖ξ‖))) ∧
    (δφ, decBgMult Gp (compWeight L a₁) ν (rho4 d L N BG κ) s' D + δα) ∈
      pertClass Gp (cK * (cK2 d L N * (B * ‖ξ‖)))
        (bgK1 d L N * (xiC1 d * eps) + cK * cK2 d L N * B * r₀ + 2) (renMassU ν ξ) := by
  have hn := norm_nonneg ξ
  have hK2 := cK2_pos d L N
  have hW : 0 ≤ cK * cK2 d L N * B := by positivity
  have hVV : cK2' d L N (famConst d L BG κ) *
      ((3 / 2 + 32 / 15 * (3 + (K4 d L N BG κ + bgK1 d L N) * xiC1 d)) * eps * ‖ξ‖) ≤
      cK * (cK2 d L N * (B * ‖ξ‖)) := by
    have := mul_le_mul_of_nonneg_right hCB hn
    nlinarith
  have hVr : cK * (cK2 d L N * (B * ‖ξ‖)) ≤ cK * cK2 d L N * B * r₀ := by
    have := mul_le_mul_of_nonneg_left hξ.le hW
    nlinarith
  have hsup' := hsup.mono hVV
  refine ⟨hsup', hsup', fun y => ?_⟩
  have hξ16 : ‖ξ‖ ≤ 1 / 16 := hξ.le.trans hr₀
  obtain ⟨hb, -, -, -⟩ := renDec_data_bounds_of_flCore hC hD hs
  have h1 := hb.alpha y
  have h2 := (hsm y).trans hVV
  have hsp := spacing_pos Gp (x := (y : CTorus d L N₁ m₁ K))
  have hℓ0 : 0 ≤ Gp.spacing (y : CTorus d L N₁ m₁ K) ^ 2 := by positivity
  have hν := renSpacing_mass_le hC y
  have hν0 := hC.HBp.mass
  have h3 : ‖renMassU ν ξ‖ ≤ ν + 32 / 15 * ν * ‖ξ‖ := by
    have := renMassU_sub_norm_le hν0 hξ16
    have e : renMassU ν ξ = (renMassU ν ξ - ν) + (ν : ℂ) := by ring
    rw [e]
    refine (norm_add_le _ _).trans ?_
    rw [Complex.norm_real, Real.norm_of_nonneg hν0]
    linarith
  have h4 : Gp.spacing (y : CTorus d L N₁ m₁ K) ^ 2 * ‖renMassU ν ξ‖ ≤ 17 / 15 := by
    calc Gp.spacing (y : CTorus d L N₁ m₁ K) ^ 2 * ‖renMassU ν ξ‖
        ≤ Gp.spacing (y : CTorus d L N₁ m₁ K) ^ 2 * (ν + 32 / 15 * ν * ‖ξ‖) :=
          mul_le_mul_of_nonneg_left h3 hℓ0
      _ = (ν * Gp.spacing (y : CTorus d L N₁ m₁ K) ^ 2) * (1 + 32 / 15 * ‖ξ‖) := by ring
      _ ≤ 1 * (1 + 32 / 15 * (1 / 16)) := by
          have h5 : 0 ≤ ν * Gp.spacing (y : CTorus d L N₁ m₁ K) ^ 2 := by positivity
          apply mul_le_mul hν (by linarith) (by positivity) (by norm_num)
      _ = 17 / 15 := by norm_num
  have hK4 : K4 d L N BG κ * (xiC1 d * eps) ≤ 1 / 2 := by linarith
  have hK1 : 0 ≤ bgK1 d L N * (xiC1 d * eps) := by
    have := hC.eps_pos
    have : 0 ≤ xiC1 d := by unfold xiC1; positivity
    have h := bgK1_pos d L N
    positivity
  simp only [Pi.add_apply]
  calc Gp.spacing (y : CTorus d L N₁ m₁ K) ^ 2 *
        ‖decBgMult Gp (compWeight L a₁) ν (rho4 d L N BG κ) s' D y + δα y + renMassU ν ξ‖
      ≤ Gp.spacing (y : CTorus d L N₁ m₁ K) ^ 2 *
        (‖decBgMult Gp (compWeight L a₁) ν (rho4 d L N BG κ) s' D y‖ + ‖δα y‖ +
          ‖renMassU ν ξ‖) := mul_le_mul_of_nonneg_left norm_add₃_le hℓ0
    _ = Gp.spacing (y : CTorus d L N₁ m₁ K) ^ 2 *
        ‖decBgMult Gp (compWeight L a₁) ν (rho4 d L N BG κ) s' D y‖ +
        Gp.spacing (y : CTorus d L N₁ m₁ K) ^ 2 * ‖δα y‖ +
        Gp.spacing (y : CTorus d L N₁ m₁ K) ^ 2 * ‖renMassU ν ξ‖ := by ring
    _ ≤ bgK1 d L N * (xiC1 d * eps) + cK * cK2 d L N * B * r₀ + 2 := by linarith

/-- **`renDec_pertClass`.**  For the analytic family `F` of `renDec_sharp`, at every datum of
`XiCOneReal`, every `ξ` with `‖ξ‖ < r₀` and every cut `s` of the polydisc (one statement for the
whole fixed domain), the field `δφ = (F (rawOf D, ξ) s).1` satisfies `SupBounds` at
`V = c_K C₂ B ‖ξ‖` and `(δφ, α_s + δα)` lies in `pertClass Gp V A ν_u`, `ν_u = renMassU ν ξ`,
`A = K₁ δ + c_K C₂ B r₀ + 2`, `α_s = decBgMult` at the extended cut. -/
theorem renDec_pertClass
    (hC : FlCore N Gp Hm a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁) {r₀ : ℝ} (hr₀0 : 0 < r₀)
    (hr₀ : r₀ ≤ 1 / 16) (X₁ : Set (CTorus d L N₁ m₁ K))
    (hD₀ : 2 * (K4 d L N BG κ * (xiC1 d * eps)) + 3 * r₀ ≤ 1)
    (hδ₀ : 2 * (K4 d L N BG κ * (xiC1 d * eps)) + 3 * r₀ ≤
      deltaStar' d L N (famConst d L BG κ) (gamma1 d / 8))
    (hδ₁ : (3 / 2 + 32 / 15 * (3 + (K4 d L N BG κ + bgK1 d L N) * xiC1 d)) * eps * r₀ ≤
      deltaStar' d L N (famConst d L BG κ) (gamma1 d / 8))
    {B cK : ℝ} (hB0 : 0 ≤ B) (hcK : 1 ≤ cK)
    (hCB : cK2' d L N (famConst d L BG κ) *
      ((3 / 2 + 32 / 15 * (3 + (K4 d L N BG κ + bgK1 d L N) * xiC1 d)) * eps) ≤
        cK * cK2 d L N * B) :
    ∃ F : RawData d L (N₁ * L ^ m₁) K N × (Fin 3 → ℂ) → (RenLabel Gp X₁ → ℂ) →
        (Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ),
      AnalyticOnNhd ℂ (fun p : (RawData d L (N₁ * L ^ m₁) K N × (Fin 3 → ℂ)) ×
          (RenLabel Gp X₁ → ℂ) => F p.1 p.2)
        (expDom Gp (XiCOneReal Gp (compWeight L a₁) ν eps) r₀ ×ˢ
          polydisc (0 : RenLabel Gp X₁ → ℂ) (fun _ => Real.exp κ)) ∧
      ∀ D : BgData Gp N, XiCOneReal Gp (compWeight L a₁) ν eps D → ∀ ξ : Fin 3 → ℂ, ‖ξ‖ < r₀ →
        ∀ s ∈ polydisc (0 : RenLabel Gp X₁ → ℂ) (fun _ => Real.exp κ),
          SupBounds Gp (F (rawOf D, ξ) s).1 (cK * (cK2 d L N * (B * ‖ξ‖))) ∧
          ((F (rawOf D, ξ) s).1,
            decBgMult Gp (compWeight L a₁) ν (rho4 d L N BG κ)
              (extParams Gp X₁ (s ∘ (renLabelEquiv Gp X₁).symm)) D + (F (rawOf D, ξ) s).2) ∈
            pertClass Gp (cK * (cK2 d L N * (B * ‖ξ‖)))
              (bgK1 d L N * (xiC1 d * eps) + cK * cK2 d L N * B * r₀ + 2) (renMassU ν ξ) := by
  obtain ⟨F, han, hpt⟩ := renDec_sharp hC hr₀0 hr₀ X₁ hD₀ hδ₀ hδ₁
  refine ⟨F, han, fun D hD ξ hξ s hs => ?_⟩
  have hE1 : 1 < Real.exp κ := Real.one_lt_exp_iff.2 hC.hκ
  have hs'' : ∀ i, ‖s i‖ < Real.exp κ := fun i => by simpa using hs i
  have hsx : ∀ P, ‖extParams Gp X₁ (s ∘ (renLabelEquiv Gp X₁).symm) P‖ ≤ Real.exp κ :=
    fun P => (norm_extParams_lt hE1 (fun i => hs'' _) P).le
  obtain ⟨-, -, -, h4, h5, -⟩ := hpt D hD ξ hξ s hs _ _ rfl rfl
  have := renPertClass_of_sharp hC hr₀0 hr₀ hD₀ hB0 hcK hCB hD hξ hsx h4 h5
  exact ⟨this.1, this.2⟩

end Balaban.Localization
