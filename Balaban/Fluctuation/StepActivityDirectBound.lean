/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.StepActivityHatBound
public import Balaban.Fluctuation.HatLabelsDirect
public import Balaban.Fluctuation.StepRatesDirect
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The step activity bound of the zero class from direct-label terms

`stepActivityBound_zeroClass_of_directTerms` is the direct-label counterpart of
`stepActivityBound_zeroClass_of_hatExpansion`.  The landed assembler passes through the halo
conversion `labelAct_of_hatTerms`, which turns the term rate `a` into `a / hatA - c₁` and the
prefactor `ε_U` into `hatEpsH`.  Here the labels are the domains themselves
(`labelAct_of_directTerms`), so the activities keep the rate `κ_H = a` and have the prefactor
`ε_H = R_σ ε_U`.  The numerical hypotheses become `κ' + 3κ₀ + c₁ + 3/2 ≤ a` and
`R_σ ε_U ≤ 1 / (8 K_c³ c₁ exp((a - 2κ₀) c_G + c₁ + κ' c_G))`.  The rest of the proof is that of the
landed assembler: the activities are rescaled by the Taylor factor `s²` on the first segment
(`StepSetting.Wone_zeroClass_eq_hat`), and the second segment has `W₂ = 0` for the source `0`.

**Conditional on the direct-label input.**  The theorem takes a `DirectTerms` instance `I`
for the physical expansion as a hypothesis.  The physical expansion is not yet shown to produce
one: that is the open locality theorem (`physical_directTerms`, OPEN-PHYSICAL-FOOTPRINT-LOCAL of
`notes/phase1/TRUE-LOCAL.md`, `notes/phase1/SHARPLOC.md`).  The identification of `val` at the
physical hat point (`hval`) is the same one the landed assembler obtains from
`labelAct_of_interaction_expansion_hat`.  The hypotheses that only served to build the expansion
(covers, rooted bounds, energy and observable terms) are not needed once `I` is given.
-/

@[expose] public section

namespace Balaban.Fluctuation

open MeasureTheory Balaban Balaban.Localization Balaban.Multiscale Balaban.Polymer
  Balaban.Background Balaban.SmallField Balaban.SmallField.Def6 Balaban.Analysis Finset Matrix Set
  Metric

section Main

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ} {c BG κ eps : ℝ}

variable
    (S : StepSetting d L N₁ m₁ k N ϱ)
  {ρ εU κ0 κ' Kc' a : ℝ} {Kc Cx c₂ BG₂ δ₁ δc : ℝ}
  (hC : FlCore N S.G' (stepG d L N₁ m₁ k ϱ) S.a₁ S.ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
  {R₁ : ℝ} (hR₁ : 1 < R₁) {r Rσ : ℝ} (hr : 0 < r)
  {cψ : ℝ} (hcψ : 0 ≤ cψ)
  (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
  (hdm : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
  (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
  (hsmX : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
  (hδ₁ : Real.sqrt N * (‖((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)‖ *
    (covSupConstC d L N (compWeight L S.a₁ k) κ * cψ)) < δ₁)
  (hc7 : c7 d L N BG κ ≤ thm73C3 d L N)
  {R : ℝ} (hR : 2 ≤ R)
  (hsm : 2 * (compC4 d * (bgK1 d L N * (xiC1 d * eps))) + 5 * (R * δ₁) ≤ bgC1 d L N)
  {m₀ : ℕ}
  (hRσ : 0 < Rσ) (hc : (Rσ * R₁ + r) * ρ < cψ)
  (hD : XiCData S.G' (compWeight L S.a₁) S.ν (k + 1) 1 eps S.D')
  (hN : L ^ m₀ ∣ N₁) (hp : 0 < S.p₁) (hpρ : S.p₁ ≤ ρ)
  (hεpos : 0 < εU)
  (hκE : aEnt d L + 1 ≤ κ0) (hKc : K0 d L κ0 + 1 ≤ Kc') (hκ' : 0 ≤ κ')
  (hκa : κ' + 3 * κ0 + c1 d L + 3 / 2 ≤ a)
  (hDA : Rσ * εU ≤ 1 / (8 * Kc' ^ 3 * c1 d L *
    Real.exp ((a - 2 * κ0) * cG d L + c1 d L + κ' * cG d L)))
  {pp : ℝ} (R0 : S.RayData pp) (hlt : S.p₁ < pp)
  (hbase : InUnionDomainC (stepG d L N₁ m₁ k ϱ) (bgC0 d L N) (bgC2 d L N) S.ν
    (S.dataU S.psi0))
  (hRσ1 : 1 < Rσ)
  {SΛ : Set (RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ))}
  {XW : Set (((S.U × Fin N → ℂ) × (S.U × Fin N → ℂ)) × ((S.U × Fin N → ℂ) × (S.U × Fin N → ℂ)))}
  {val : ((S.U × Fin N → ℂ) × (S.U × Fin N → ℂ)) → ((S.U × Fin N → ℂ) × (S.U × Fin N → ℂ)) →
    ℂ → (RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ)) → ℂ}
  {AgΘ : Set (CTorus d L N₁ m₁ (k + 1)) →
    (RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ)) →
    (RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ)) → Prop}
  {AgF : Set (CTorus d L N₁ m₁ (k + 1)) →
    ((S.U × Fin N → ℂ) × (S.U × Fin N → ℂ)) → ((S.U × Fin N → ℂ) × (S.U × Fin N → ℂ)) → Prop}
  (I : DirectTerms S m₀ hp (fun ψ => (ψ, ψ)) ρ Rσ εU a
    (rawOf S.D', (0 : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ)) SΛ XW val AgΘ AgF)
  (hval : ∀ (x : S.E) (u : ℂ), val (S.hatC x, S.hatC x) (S.hatC x, S.hatC x) u
      (rawOf S.D', (0 : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ)) =
    (-(S.β : ℂ)) * raySrc3 (hatFun S.G' S.a₁ S.ν eps S.hG' ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)
      (interactionOne S.hG S.hG' (le_refl (k + 1)) S.a₁ S.ν eps)) taylorWeight (S.hatC x)
      (S.hatC x) u (rawOf S.D'))

include hC hR₁ hr hcψ hMX hdm hα hsmX hδ₁ hc7 hR hsm hRσ hc hD hN hp hpρ hεpos hκE hKc hκ' hκa hDA R0 hlt hbase hRσ1 I hval

/-- **The step activity bound of the zero class from direct-label terms.**  Let `I` be a
`DirectTerms` instance (the terms of the expansion of the step exponent at the hat variable, indexed
by the domains `Y ∈ 𝒟_{k+1}` themselves, with sharp locality on the blocks inside `Y`, terms
bounded by `ε_U e^{-a 𝗱(Y)}`), whose value `val` is, at the hat variable `ψ̂`, the potential part
`(-β) raySrc3 (hat expansion)` of the step exponent at `Θ₀ = (rawOf D', 0)`.  Under the numerical
hypotheses `κ' + 3κ₀ + c₁ + 3/2 ≤ a` and
`R_σ ε_U ≤ 1 / (8 K_c³ c₁ exp((a - 2κ₀) c_G + c₁ + κ' c_G))`, there is a step activity bound of the
zero class for the source `0`, with rate `κ_H = a` and prefactor `ε_H = R_σ ε_U`.  This is
conditional on `I`: that the physical expansion gives such an `I` is open. -/
theorem stepActivityBound_zeroClass_of_directTerms_fields :
    ∃ B : StepActivityBound S (zeroClass d L N₁ m₁ k N ϱ) 0,
      B.κH = a ∧ B.εH = Rσ * εU := by
  classical
  have hpc : S.p₁ < cψ := p₁_lt_of_margin hp hpρ hRσ1 hR₁ hr hc
  have hρ : 0 < ρ := lt_of_lt_of_le hp hpρ
  have hK0 : K0 d L κ0 ≤ Kc' := by linarith
  obtain ⟨Ahat, hdiff, hid⟩ := labelAct_of_directTerms S m₀ I hN hρ hRσ.le hεpos.le hκE hK0
  have hcfun : ∀ s : ℝ, ‖((if s ∈ Icc (0 : ℝ) 1 then s ^ 2 else 0 : ℝ) : ℂ)‖ ≤ 1 :=
    norm_ite_sq_le
  have key : ∀ s : ℝ, s ∈ Icc (0 : ℝ) 1 → ∀ᵐ x ∂S.nuFl,
      S.Wone (zeroClass d L N₁ m₁ k N ϱ) s x = ∑ y, ((Ahat (s : ℂ)).cscale
        ((if s ∈ Icc (0 : ℝ) 1 then s ^ 2 else 0 : ℝ) : ℂ) (hcfun s)).H y
          ((S.blockSplit m₀ hp).restr x) := by
    intro s hs
    have hu : ‖(s : ℂ)‖ < Rσ := norm_ofReal_lt_of_mem hs hRσ1
    filter_upwards [S.ae_hatOf_restr m₀ hρ hp hpρ, S.ae_ball hp] with x hx hχ
    have hT1 := S.Wone_zeroClass_eq_hat hC R0 hlt hbase hD hc7 (lt_of_lt_of_le one_lt_two hR) hsm
      hMX hdm hα hsmX hp hcψ hpc hδ₁ hs hχ
    simp only [LabelAct.cscale, hs, ↓reduceIte]
    rw [← Finset.mul_sum, hid (s : ℂ) hu, hx, hval, ← hT1]
    push_cast
    rfl
  refine ⟨{
    m₀ := m₀
    hN := hN
    BS := S.blockSplit m₀ hp
    Lb := {Y // Y ∈ I.𝒴}
    Lab := thickLabels I.𝒴 I.dom
    εH := Rσ * εU
    κH := a
    κ0 := κ0
    κ' := κ'
    Kc := Kc'
    A := fun p => (Ahat (p.1 : ℂ)).cscale
      ((if p.1 ∈ Icc (0 : ℝ) 1 then p.1 ^ 2 else 0 : ℝ) : ℂ) (hcfun p.1)
    hκ0 := hκE
    hKc := hKc
    hεpos := by positivity
    hκ' := hκ'
    hκ := hκa
    hε := hDA
    hW := ?_ }, rfl, rfl⟩
  intro p hpS
  have hs : p.1 ∈ Icc (0 : ℝ) 1 := by
    rcases hpS with ⟨h1, -⟩ | ⟨h1, -⟩
    · exact h1
    · rw [h1]; exact ⟨zero_le_one, le_rfl⟩
  filter_upwards [key p.1 hs] with x hx
  rw [Wtwo_zero_class, add_zero]
  exact hx

/-- The conclusion of `stepActivityBound_zeroClass_of_directTerms_fields` without the fields:
**a step activity bound of the zero class exists**, conditional on the `DirectTerms` instance `I`
(open for the physical expansion). -/
theorem stepActivityBound_zeroClass_of_directTerms :
    Nonempty (StepActivityBound S (zeroClass d L N₁ m₁ k N ϱ) 0) :=
  ⟨(stepActivityBound_zeroClass_of_directTerms_fields S hC hR₁ hr hcψ hMX hdm hα hsmX hδ₁ hc7 hR
    hsm hRσ hc hD hN hp hpρ hεpos hκE hKc hκ' hκa hDA R0 hlt hbase hRσ1 I hval).choose⟩


end Main

section Corollaries

/-- The rate hypothesis and the output rate at `d = L = 3` and the constants (8) of
`notes/phase1/TRUE-LOCAL.md` (`κ₀ = a_Ent + 1`, `κ_dec = 100 (κ₀ + c₁ + 10)`, `a = 2κ_dec - 1`,
`κ' = (3/2) κ_dec + κ₀ + 1`): the rate hypothesis `κ' + 3κ₀ + c₁ + 3/2 ≤ a` of
`stepActivityBound_zeroClass_of_directTerms` holds, and the output rate
`min κ_h κ' - κ₀ - 1` (with `κ_h = κ'`) is `(3/2) κ_dec ≥ κ_in = κ_dec`: the class rate is
preserved.  Side by side with this, the landed halo route admits no such rates
(`stepRates_landed_impossible`).  The first conjunct is what `stepActivityBound_zeroClass_of_directTerms`
needs; the second is the landed obstruction. -/
theorem directRoute_rate_preserved :
    (∃ κ0 κdec a κ' κout : ℝ, κ0 = aEnt 3 3 + 1 ∧ κdec = 100 * (κ0 + c1 3 3 + 10) ∧
      a = 2 * κdec - 1 ∧ κ' = 3 / 2 * κdec + κ0 + 1 ∧ κout = 3 / 2 * κdec ∧
      aEnt 3 3 + 1 ≤ κ0 ∧ 0 ≤ κ' ∧ κ' + 3 * κ0 + c1 3 3 + 3 / 2 ≤ a ∧
      κout ≤ min κ' κ' - κ0 - 1 ∧ κdec ≤ κout) ∧
    ¬ ∃ κ0 κ' κH κh κin κdec κout : ℝ, aEnt 3 3 + 1 ≤ κ0 ∧ 0 < κin ∧
      hatKappaH 3 3 (2 * κdec - 1) = κH ∧ κ' + 3 * κ0 + c1 3 3 + 3 / 2 ≤ κH ∧ κ' ≤ κh ∧
      κdec - 1 ≤ κin ∧ κout ≤ min κh κ' - κ0 - 1 ∧ κin ≤ κout := by
  refine ⟨?_, stepRates_landed_impossible (by norm_num) (by norm_num)⟩
  have hc1 : 1 ≤ c1 3 3 := one_le_c1 3 3
  have hent : 0 ≤ aEnt 3 3 := aEnt_nonneg 3 3
  obtain ⟨κ0, h0⟩ : ∃ x : ℝ, x = aEnt 3 3 + 1 := ⟨_, rfl⟩
  obtain ⟨κdec, hdec⟩ : ∃ x : ℝ, x = 100 * (κ0 + c1 3 3 + 10) := ⟨_, rfl⟩
  have hκ0 : 0 ≤ κ0 := by linarith
  obtain ⟨-, h3, h4, -, h5⟩ := stepRates_direct_closure (κ0 := κ0) (c := c1 3 3) (κin := κdec)
    (κdec := κdec) (κH := 2 * κdec - 1) (κ' := 3 / 2 * κdec + κ0 + 1) (κout := 3 / 2 * κdec)
    hκ0 (by linarith) (by linarith) rfl rfl rfl rfl
  exact ⟨κ0, κdec, 2 * κdec - 1, 3 / 2 * κdec + κ0 + 1, 3 / 2 * κdec, h0, hdec, rfl, rfl, rfl,
    h0.ge, by linarith, by linarith, h4, h5⟩

/-- **The numerical hypotheses of `stepActivityBound_zeroClass_of_directTerms` are jointly
satisfiable** at `d = L = 3`: with `a = 2 κ_dec - 1` there are `κ₀, K_c, κ'`, `R_σ > 1` and
`ε_U > 0` satisfying the aggregate-entropy hypotheses, the rate hypothesis and the smallness
hypothesis (DA), together with the rate chain `κ_dec - 1 ≤ κ_in ≤ κ_out ≤ min κ_h κ' - κ₀ - 1`
of `stepRates_direct_witness`.  The remaining hypotheses (the step, its ray datum, the hat
expansion identities and the instance `I`) are not discharged here; see the module doc. -/
theorem directBound_numerics_nonempty (m₀ : ℕ) :
    ∃ κ0 Kc' κ' a Rσ εU κdec κin κout : ℝ, 1 < Rσ ∧ 0 < εU ∧ aEnt 3 3 + 1 ≤ κ0 ∧
      K0 3 3 κ0 + 1 ≤ Kc' ∧ 0 ≤ κ' ∧ κ' + 3 * κ0 + c1 3 3 + 3 / 2 ≤ a ∧
      Rσ * εU ≤ 1 / (8 * Kc' ^ 3 * c1 3 3 *
        Real.exp ((a - 2 * κ0) * cG 3 3 + c1 3 3 + κ' * cG 3 3)) ∧
      a = 2 * κdec - 1 ∧ κdec - 1 ≤ κin ∧ κin ≤ κout ∧ κout ≤ κ' - κ0 - 1 := by
  obtain ⟨κ0, Kc, κ', κH, κG, κh, κdet, κin, κdec, κout, κtr, κtr', κAE, εH, h1, h2, h3, h4, -,
    h6, h7, -, -, -, -, h12, -, h14, h15, h16, -⟩ := stepRates_direct_witness m₀
  refine ⟨κ0, Kc, κ', κH, 2, εH / 2, κdec, κin, κout, by norm_num, by positivity, h1, h2, h4, h6,
    ?_, h12, h14, h15, (le_trans h16 (by linarith [min_le_right κh κ']))⟩
  have : (2 : ℝ) * (εH / 2) = εH := by ring
  rw [this]; exact h7

end Corollaries

end Balaban.Fluctuation
