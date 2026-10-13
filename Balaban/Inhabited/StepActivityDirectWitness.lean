/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.StepActivityHatWitness
public import Balaban.Fluctuation.StepActivityDirectPhysical
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FunProp

/-!
# The direct step activity bound has an instance

`directWitness_core_amp` is `hatWitness_core_amp` with the direct numerics: the decay rate of the
terms is `a = 2 κ_dec - 1` with `κ_dec = 3 κ₀ + c₁ + 5`, `κ' = 0`, and the amplitude bound is
`prop33Eps(ε) · β ≤ B / 2`, where `B = [8 K_c'^3 c₁ exp((a - 2κ₀) c_G + c₁)]⁻¹` is the smallness
(DA) of `stepActivityBound_zeroClass_direct` at `R_σ = 2`.  The amplitude is `O(ε)` as the block
scale `ε = δ₁ → 0`, so it is met for every `β` once `ε` is small (the same mechanism as in
`hatWitness_core_amp`); the rate hypothesis does not depend on `ε`.

`directActivity_main` / `stepActivityBound_zeroClass_direct_hyps_nonempty`: at the step
`hatStep m₁ β p₁ δ` (`d = L = 3`, `β > 0`) every hypothesis of
`stepActivityBound_zeroClass_direct` holds (with `R_σ = 2`, `R₁ = 2`, `r = 1`), and the activity
bound has `κ_H = 2 κ_dec - 1`.
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation
  Balaban.Localization Balaban.Localization.LevelPair Balaban.Localization.I5Inhabited
  Balaban.Polymer Balaban.SmallField.Def6 Filter Topology

/-- **The numerical tower** (see the module docstring). -/
theorem directWitness_core_amp (N : ℕ) (β : ℝ) :
    ∃ (m₁ : ℕ) (c BG κ t c₂ BG₂ κdec κ0 δc : ℝ),
      4 ≤ m₁ ∧ 0 < t ∧
      Nonempty (FlCore N (Gp m₁ (rhoSep m₁)) (Hm m₁ (rhoSep m₁)) 1 nuW c BG κ t (levelKc 3 3)
        (Cchi 3 3) c₂ BG₂ t) ∧
      0 ≤ κ0 ∧ 3 * κ0 + 3 ≤ κdec ∧
      4 * ((3 : ℕ) : ℝ) * (((2 * 3 + 1) ^ 3 : ℕ) : ℝ) * κdec ≤ κ ∧ 1 ≤ (κ / 2 - 1) / 2 ∧
      Real.log ((((2 * 3 + 1) ^ 3 : ℕ) : ℝ) * (((3 ^ 1) ^ 3 : ℕ) : ℝ)) ≤ (κ / 2 - 1) / 2 ∧
      c7 3 3 N BG κ ≤ thm73C3 3 3 N ∧
      cstarX 3 3 * Real.exp (N0 3 3 * κ) ≤ ((3 : ℕ) : ℝ) ^ m₁ ∧
      decDomMargin 3 3 N BG κ (xiC1 3 * t) < δc ∧
      K4 3 3 N BG κ * (xiC1 3 * t) < coerciveConst 3 / 2 ∧
      δc ^ 2 * smallConstX 3 3 κ ≤ 1 / 4 ∧
      2 * t ≤ deltaStar 3 3 N ∧ cK2 3 3 N * (2 * t) < bgC0 3 3 N / 2 ∧
      cK2 3 3 N * t ≤ c6' 3 3 N (famConst 3 3 BG₂ κ) (gamma1 3 / 8) ∧
      cK2' 3 3 N (famConst 3 3 BG₂ κ) * t ≤ c6' 3 3 N (famConst 3 3 BG₂ κ) (gamma1 3 / 8) ∧
      2 * (compC4 3 * (bgK1 3 3 N * (xiC1 3 * t))) + 5 * (2 * t) ≤ bgC1 3 3 N ∧
      aEnt 3 3 + 1 ≤ κ0 ∧
      0 + 3 * κ0 + c1 3 3 + 3 / 2 ≤ 2 * κdec - 1 ∧
      prop33Eps 3 3 N m₁ 1 1 1 nuW BG BG₂ κ t 1 0 0 * β ≤
        1 / (8 * (K0 3 3 κ0 + 1) ^ 3 * c1 3 3 *
        Real.exp ((2 * κdec - 1 - 2 * κ0) * cG 3 3 + c1 3 3 + 0 * cG 3 3)) / 2 := by
  obtain ⟨c, BG0, hS0⟩ := decSpecs_exists (d := 3) (L := 3) (by norm_num) (by norm_num)
  set BG := max BG0 1 with hBGdef
  have hS : DecSpecs 3 3 c BG := hS0.mono_BG (le_max_left _ _)
  have hBG1 : 1 ≤ BG := le_max_right _ _
  obtain ⟨c₂, BG₂, hS2⟩ := Dec2.decSpecs_exists (d := 3) (L := 3) (Kc := levelKc 3 3)
    (Cx := Cchi 3 3) (by norm_num) (by norm_num) (levelKc_nonneg 3 3) (Cchi_nonneg 3 3)
  have hT3 := thm73C3_pos (d := 3) (L := 3) (N := N) (by norm_num)
  have hc1 := one_le_c1 3 3
  have hent := aEnt_nonneg 3 3
  set κ0 : ℝ := aEnt 3 3 + 1 with hκ0def
  set κdec : ℝ := 3 * κ0 + c1 3 3 + 5 with hκdecdef
  have hκdec0 : 0 ≤ κdec := by rw [hκdecdef]; linarith
  set κ : ℝ := 4 * ((3 : ℕ) : ℝ) * (((2 * 3 + 1) ^ 3 : ℕ) : ℝ) * κdec + 40000 +
    1 / thm73C3 3 3 N with hκdef
  have hinv : 0 ≤ 1 / thm73C3 3 3 N := by positivity
  have hcoef : (0 : ℝ) ≤ 4 * ((3 : ℕ) : ℝ) * (((2 * 3 + 1) ^ 3 : ℕ) : ℝ) := by positivity
  have hκ1 : 4 * ((3 : ℕ) : ℝ) * (((2 * 3 + 1) ^ 3 : ℕ) : ℝ) * κdec + 40000 ≤ κ := by
    rw [hκdef]; linarith
  have hκ2 : 1 / thm73C3 3 3 N ≤ κ := by
    rw [hκdef]; nlinarith [mul_nonneg hcoef hκdec0]
  have hκ3 : 40000 ≤ κ := by nlinarith [mul_nonneg hcoef hκdec0]
  obtain ⟨m₁, h4, hm⟩ := exists_m₁ (max (max (c * Real.exp ((N0 3 3 : ℝ) * κ))
    (c₂ * Real.exp ((N0 3 3 : ℝ) * κ))) (cstarX 3 3 * Real.exp ((N0 3 3 : ℝ) * κ)))
  have hm1 : c * Real.exp ((N0 3 3 : ℝ) * κ) ≤ ((3 : ℕ) : ℝ) ^ m₁ :=
    (le_max_left _ _).trans ((le_max_left _ _).trans (by exact_mod_cast hm))
  have hm2 : c₂ * Real.exp ((N0 3 3 : ℝ) * κ) ≤ ((3 : ℕ) : ℝ) ^ m₁ :=
    (le_max_right _ _).trans ((le_max_left _ _).trans (by exact_mod_cast hm))
  have hm3 : cstarX 3 3 * Real.exp ((N0 3 3 : ℝ) * κ) ≤ ((3 : ℕ) : ℝ) ^ m₁ :=
    (le_max_right _ _).trans (by exact_mod_cast hm)
  have S := dgSettingNu h4
  have SH := opSettingNu h4
  have hev := flCore_level_eventually (N := N) S SH isLevel_Hm isLevel_Gp (bgHypNu m₁)
    hS (κ := κ) (by linarith) hm1 hS2 hm2
  have hB0 : 0 ≤ famConst 3 3 BG₂ κ := by
    have := famConst_ge_one (L := 3) hS2.fam.2.1 κ (d := 3) (by norm_num); linarith
  have hc6 : 0 < c6' 3 3 N (famConst 3 3 BG₂ κ) (gamma1 3 / 8) :=
    c6'_pos hB0 (by have := gamma1_pos (d := 3) (by norm_num); positivity)
  have hDs : 0 < deltaStar 3 3 N := deltaStar_pos (d := 3) (L := 3) (N := N) (by norm_num)
  have hC0 : 0 < bgC0 3 3 N := bgC0_pos 3 3 N (by norm_num)
  have hC1 : 0 < bgC1 3 3 N := bgC1_pos' (d := 3) (L := 3) (N := N) (by norm_num)
  have hSX := smallConstX_pos 3 3 κ
  set SX := smallConstX 3 3 κ with hSXdef
  set δc : ℝ := 1 / (2 * (SX + 1)) with hδcdef
  have hδc0 : 0 < δc := by positivity
  have hδc1 : δc * (2 * (SX + 1)) = 1 := by rw [hδcdef]; field_simp
  have hδcSX : δc ^ 2 * SX ≤ 1 / 4 := by
    have h1 : δc * SX ≤ 1 / 2 := by nlinarith
    have h2 : δc ≤ 1 / 2 := by nlinarith
    nlinarith
  have hK4 : 0 < K4 3 3 N BG κ := K4_pos (by linarith) (by norm_num)
  have hcoer : 0 < coerciveConst 3 := coerciveConst_pos (by norm_num)
  have wk : ∀ {p : ℝ → Prop}, (∀ᶠ t in 𝓝 (0 : ℝ), p t) → ∀ᶠ t in 𝓝[>] (0 : ℝ), p t :=
    fun h => eventually_nhdsWithin_of_eventually_nhds h
  have e1 := ev_lt (f := fun t : ℝ => 2 * t) (by fun_prop) (c := deltaStar 3 3 N) (by simpa using hDs)
  have e2 := ev_lt (f := fun t : ℝ => cK2 3 3 N * (2 * t)) (by fun_prop) (c := bgC0 3 3 N / 2)
    (by simp; positivity)
  have e3 := ev_lt (f := fun t : ℝ => cK2 3 3 N * t) (by fun_prop)
    (c := c6' 3 3 N (famConst 3 3 BG₂ κ) (gamma1 3 / 8)) (by simpa using hc6)
  have e4 := ev_lt (f := fun t : ℝ => cK2' 3 3 N (famConst 3 3 BG₂ κ) * t) (by fun_prop)
    (c := c6' 3 3 N (famConst 3 3 BG₂ κ) (gamma1 3 / 8)) (by simpa using hc6)
  have e5 := ev_lt (f := fun t : ℝ => 2 * (compC4 3 * (bgK1 3 3 N * (xiC1 3 * t))) + 5 * (2 * t))
    (by fun_prop) (c := bgC1 3 3 N) (by simpa using hC1)
  have e6 := ev_lt (f := fun t : ℝ => decDomMargin 3 3 N BG κ (xiC1 3 * t))
    (by unfold decDomMargin; fun_prop) (c := δc) (by simp [decDomMargin]; exact hδc0)
  have e7 := ev_lt (f := fun t : ℝ => K4 3 3 N BG κ * (xiC1 3 * t)) (by fun_prop)
    (c := coerciveConst 3 / 2) (by simp; positivity)
  have hK0 : 0 ≤ K0 3 3 κ0 := by
    unfold K0
    apply div_nonneg (Real.exp_pos _).le
    have : Real.exp (-1) < 1 := by simp
    linarith
  have hEpsMax : 0 < (1 / (8 * (K0 3 3 κ0 + 1) ^ 3 * c1 3 3 *
        Real.exp ((2 * κdec - 1 - 2 * κ0) * cG 3 3 + c1 3 3 + 0 * cG 3 3)) / 2 : ℝ) := by
    have : 0 < c1 3 3 := by linarith
    have : 0 < K0 3 3 κ0 + 1 := by linarith
    positivity
  have e8 := ev_lt (f := fun t : ℝ => prop33Eps 3 3 N m₁ 1 1 1 nuW BG BG₂ κ t 1 0 0 * β)
    (by unfold prop33Eps energyBd; fun_prop)
    (c := 1 / (8 * (K0 3 3 κ0 + 1) ^ 3 * c1 3 3 *
        Real.exp ((2 * κdec - 1 - 2 * κ0) * cG 3 3 + c1 3 3 + 0 * cG 3 3)) / 2)
    (by simpa [prop33Eps, energyBd] using hEpsMax)
  have hpos : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < t := self_mem_nhdsWithin
  obtain ⟨t, hC, g1, g2, g3, g4, g5, g6, g7, g8, ht0⟩ := (hev.and ((wk e1).and ((wk e2).and
    ((wk e3).and ((wk e4).and ((wk e5).and ((wk e6).and ((wk e7).and ((wk e8).and hpos))))))))).exists
  have h343 : Real.log (9261 : ℝ) ≤ 9261 - 1 := Real.log_le_sub_one_of_pos (by norm_num)
  have hlogκ : Real.log ((((2 * 3 + 1) ^ 3 : ℕ) : ℝ) * (((3 ^ 1) ^ 3 : ℕ) : ℝ)) ≤ (κ / 2 - 1) / 2 := by
    norm_num at h343 ⊢
    linarith
  have hκdec3 : 3 * κ0 + 3 ≤ κdec := by rw [hκdecdef]; linarith [one_le_c1 3 3]
  refine ⟨m₁, c, BG, κ, t, c₂, BG₂, κdec, κ0, δc, h4, ht0, hC, by linarith, hκdec3,
    by linarith, by linarith, hlogκ, c7_le_thm73C3_of_large (by norm_num) hBG1 hκ2, hm3, g6, g7,
    hδcSX, g1.le, g2, g3.le, g4.le, g5.le, le_rfl, ?_, g8.le⟩
  rw [hκdecdef]; linarith [one_le_c1 3 3]


open Classical in
/-- **The main assembly**: the step `hatStep m₁ β p₁ δ` carries `RayData`, and the hat-derived
activity bound for the source `0` and for every source `g` with `‖g/β‖₁ < 1`. -/
theorem directActivity_main :
    ∃ (m₁ : ℕ) (β p₁ δ : ℝ), 0 < β ∧ 0 < p₁ ∧ p₁ < 2 ∧
      Nonempty ((hatStep m₁ β p₁ δ).RayData 2) ∧
      ∃ B : StepActivityBound (hatStep m₁ β p₁ δ) (zeroClass 3 3 9 m₁ 1 2 (rhoSep m₁)) 0,
        ∃ κdec Rσ εU : ℝ, B.κH = 2 * κdec - 1 ∧ B.εH = Rσ * εU ∧ 1 < Rσ ∧ 0 < εU := by
  classical
  obtain ⟨-, δ, δ', T, -, -, hδ, hsm, hδ'0, hδ'a, hδ'b, hδ'c, hT, -, hT1, hT2⟩ :=
    exists_witness_params (fun _ => 0)
  set β : ℝ := T ^ 2 / 3 with hβdef
  have hβ0 : 0 < β := by positivity
  obtain ⟨m₁, c, BG, κ, t, c₂, BG₂, κdec, κ0, δc, h4, ht0, ⟨hC⟩, hκ0, hκdec, hκ, h1, hlog, hc7,
    hMX, hdm, hα, hsmX, g1, g2, g3, g4, g5, hκE, hκa, hamp⟩ := directWitness_core_amp 2 β
  have hκdec0 : 0 ≤ κdec := by linarith
  have hκ_nn : 0 ≤ κ := le_trans (by positivity) hκ
  have hbig : cstarX 3 3 ≤ (3 : ℝ) ^ m₁ := by
    have h := Localization.cstarX_pos 3 3
    have h2 : cstarX 3 3 ≤ cstarX 3 3 * Real.exp ((N0 3 3 : ℝ) * κ) :=
      le_mul_of_one_le_right h.le (Real.one_le_exp (by positivity))
    have h3 : ((3 : ℕ) : ℝ) ^ m₁ = (3 : ℝ) ^ m₁ := by norm_num
    linarith
  obtain ⟨cψ, hcψ0, hcψ1, hδ₁⟩ := exists_cpsi_le_one (Real.sqrt ((2 : ℕ) : ℝ))
    ‖(((hatStep m₁ β 0 δ).betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)‖
    (covSupConstC 3 3 2 (compWeight 3 (1 : ℝ) 1) κ) ht0
  obtain ⟨R0⟩ := rayData_hatStep m₁ (cψ / 6) h4 hbig hδ hsm hδ'0 hδ'a hδ'b hδ'c hT hT1 hT2
  set S := hatStep m₁ β (cψ / 6) δ with hS
  have hp : 0 < S.p₁ := by show 0 < cψ / 6; positivity
  have hpρ : S.p₁ ≤ cψ / 6 := le_rfl
  have hlt : S.p₁ < 2 := by show cψ / 6 < 2; linarith
  have hc : ((2 : ℝ) * 2 + 1) * (cψ / 6) < cψ := by linarith
  have hxi1 : xiC1 3 * t ≤ 1 := by
    have h1 := hC.c7le
    have h2 := c7_le_bgC1 3 3 2 BG κ
    have h3 := bgC1_le_small 3 3 2 (by norm_num)
    linarith
  have hBh := hBh_of_xi (N := 2) (Gp := Gp m₁ (rhoSep m₁)) (bgHypNu m₁) nuW_pos hC.small1
    hC.eps_pos hxi1
  have hD : XiCData S.G' (compWeight 3 1) nuW (1 + 1) 1 t S.D' := by
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
  set Kc' : ℝ := K0 3 3 κ0 + 1 with hKc'
  have hK0 : 0 ≤ K0 3 3 κ0 := by
    unfold K0
    apply div_nonneg (Real.exp_pos _).le
    have : Real.exp (-1) < 1 := by simp
    linarith
  have hKc0 : 0 < Kc' := by rw [hKc']; linarith
  set εU : ℝ := 1 / (8 * Kc' ^ 3 * c1 3 3 *
    Real.exp ((2 * κdec - 1 - 2 * κ0) * cG 3 3 + c1 3 3 + 0 * cG 3 3)) / 2 with hεUdef
  have hc1p : 0 < c1 3 3 := by linarith [one_le_c1 3 3]
  have hεpos : 0 < εU := by rw [hεUdef]; positivity
  have hDA : 2 * εU ≤ 1 / (8 * Kc' ^ 3 * c1 3 3 *
      Real.exp ((2 * κdec - 1 - 2 * κ0) * cG 3 3 + c1 3 3 + 0 * cG 3 3)) := by
    rw [hεUdef]; linarith
  have hκa' : 0 + 3 * κ0 + c1 3 3 + 3 / 2 ≤ 2 * κdec - 1 := hκa
  have hεb : prop33Eps 3 3 2 m₁ 1 1 S.a₁ S.ν BG BG₂ κ t 1 0 0 * ‖(S.β : ℂ)‖ +
      ‖(0 : ℂ)‖ * (1 * (c1 3 3 * (((3 : ℕ) : ℝ) ^ (1 + m₁)) ^ 3 *
        nuBd 3 3 2 1 (cK2' 3 3 2 (famConst 3 3 BG₂ κ) * t)
          (K4 3 3 2 BG κ * (xiC1 3 * t) + (1 + 3 * (xiC1 3 * t)) + (1 + 2 / nuW)) / 1)) ≤ εU := by
    rw [norm_zero, zero_mul, add_zero, Complex.norm_real, Real.norm_of_nonneg (show (0 : ℝ) ≤ S.β from hβ0.le)]
    exact hamp
  refine ⟨m₁, β, cψ / 6, δ, hβ0, by positivity, by linarith, ⟨R0⟩, ?_⟩
  obtain ⟨B, hB1, hB2⟩ := stepActivityBound_zeroClass_direct S
      (ρ := cψ / 6) (εU := εU) (κ0 := κ0) (κ' := 0) (Kc' := Kc')
      (Rσ := 2) (R₁ := 2) (r := 1) (R := 2) (m₀ := 1) (κdec := κdec) (κ₀ := κ0) (ρE := 0)
      (ρM := 0) (Bh := 1 + 2 / nuW) (δc := δc) (cψ := cψ)
      (jV := fun _ => 1) (XV := fun _ => Xr) (𝒦XV := fun _ => {0})
      (X₁V := fun _ => Finset.univ) (jF := fun _ => 1) (XF := fun _ => Xr)
      (𝒦XF := fun _ => {0}) (X₁F := fun _ => Finset.univ)
      (τι := PEmpty.{1}) (μι := PEmpty.{1}) (ϱ₁ := fun _ => 0) (ϱ₂ := fun _ => 0)
      (GkE := fun τ => PEmpty.elim τ) (GjE := fun τ => PEmpty.elim τ) (r₀ := 0) (δ₃ := 0)
      (δfl := 0) (X₀E := fun _ => ∅) (X₁E := fun _ => ∅) (jE := fun _ => 0) (XE := fun _ => ∅)
      (𝒦XE := fun _ => ∅) (EbE := fun _ => 0) (EE := fun _ _ => 0)
      (ϱ₁M := fun _ => 0) (ϱ₂M := fun _ => 0)
      (GkM := fun τ => PEmpty.elim τ) (GjM := fun τ => PEmpty.elim τ)
      (X₀M := fun _ => ∅) (X₁M := fun _ => ∅) (jM := fun _ => 0) (XM := fun _ => ∅)
      (𝒦XM := fun _ => ∅) (EbM := fun _ => 0) (EM := fun _ _ => 0)
      hC hatConn (rowInHat_level (dgSettingNu h4) isLevel_Hm isLevel_Gp) hκ0
      hκdec (by exact_mod_cast hκ) h1 (by norm_num) (by norm_num) le_rfl isLevel_Hm
      hcψ0.le hMX hdm hα hsmX hδ₁ one_pos (bgHypNu m₁) hc7 le_rfl g1 g2 g3 g4 g5
      (fun _ => covSetup)
      (fun _ => by rw [Finset.coe_univ]; exact X1_eq_univ.symm) (fun _ => hopt)
      (fun _ => treeLen_zero) (fun _ => hlog)
      (fun z _ _ => Finset.mem_coe.2 (Finset.mem_univ _))
      (fun z => blockMargin_univ fun x _ _ => mem_some_intBox h4 x)
      (∅ : Finset PEmpty.{1}) (fun τ hτ => absurd hτ (by simp)) (fun τ hτ => absurd hτ (by simp))
      (fun τ hτ => absurd hτ (by simp)) (fun τ hτ => absurd hτ (by simp))
      (fun τ hτ => absurd hτ (by simp)) (fun τ hτ => absurd hτ (by simp))
      (fun τ hτ => absurd hτ (by simp)) (fun τ hτ => absurd hτ (by simp))
      (fun τ hτ => absurd hτ (by simp))
      (fun _ => covSetup) (fun _ => by rw [Finset.coe_univ]; exact X1_eq_univ.symm) (fun _ => hopt)
      (fun _ => treeLen_zero) (fun _ => hlog) (fun s => Finset.mem_univ _)
      (∅ : Finset PEmpty.{1}) (fun τ => PEmpty.elim τ) (fun τ => PEmpty.elim τ)
      (fun τ hτ => absurd hτ (by simp)) (fun τ hτ => absurd hτ (by simp))
      (fun τ hτ => absurd hτ (by simp)) (fun τ hτ => absurd hτ (by simp))
      (fun τ hτ => absurd hτ (by simp)) (fun τ hτ => absurd hτ (by simp))
      (fun τ hτ => absurd hτ (by simp)) (fun τ hτ => absurd hτ (by simp))
      (fun τ hτ => absurd hτ (by simp)) (fun τ hτ => absurd hτ (by simp))
      (fun τ => PEmpty.elim τ) (fun τ hτ => absurd hτ (by simp)) le_rfl (fun x => by simp) le_rfl
      (fun p => by simp) (by unfold nuW; norm_num) hBh
      (fun z x _ => Finset.mem_coe.2 (Finset.mem_univ _)) (by norm_num) hc hD
      (by norm_num) hp hpρ hεpos hεb hκE le_rfl le_rfl hκa' hDA R0 hlt (StepSetting.baseDomain_of_rayData R0) (by norm_num) rfl rfl
  exact ⟨B, κdec, 2, εU, hB1, hB2, one_lt_two, hεpos⟩

/-- **T5: the hypotheses of `stepActivityBound_zeroClass_direct` are jointly satisfiable** at an
actual step with `β > 0`: the activity bound of the zero class exists, with `κ_H = 2 κ_dec - 1`
and `ε_H = R_σ ε_U`, `R_σ > 1`, `ε_U > 0`. -/
theorem stepActivityBound_zeroClass_direct_hyps_nonempty :
    ∃ (m₁ : ℕ) (β p₁ δ : ℝ) (S : StepSetting 3 3 9 m₁ 1 2 (rhoSep m₁)),
      S = hatStep m₁ β p₁ δ ∧ 0 < S.β ∧ 0 < S.p₁ ∧ S.p₁ < 2 ∧ Nonempty (S.RayData 2) ∧
      ∃ B : StepActivityBound S (zeroClass 3 3 9 m₁ 1 2 (rhoSep m₁)) 0,
        ∃ κdec Rσ εU : ℝ, B.κH = 2 * κdec - 1 ∧ B.εH = Rσ * εU ∧ 1 < Rσ ∧ 0 < εU := by
  obtain ⟨m₁, β, p₁, δ, hβ, hp, hlt, hR, hA⟩ := directActivity_main
  exact ⟨m₁, β, p₁, δ, hatStep m₁ β p₁ δ, rfl, hβ, hp, hlt, hR, hA⟩

end Balaban.Inhabited
