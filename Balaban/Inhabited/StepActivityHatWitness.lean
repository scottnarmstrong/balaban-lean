/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.StepActivityHatWitnessRay
public import Balaban.Inhabited.StepActivityHatWitnessNum
public import Balaban.Fluctuation.StepActivityHatSourceCor
public import Balaban.Inhabited.StepActivityHatWitnessNe
public import Balaban.Fluctuation.StepActivityWitness
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FunProp

/-!
# The hat-derived activity bound has an instance, with a nonzero source

`hatActivity_witness`: at `d = L = 3`, `N₁ = 9`, `k = 1`, `N = 2`, mass `ν = 1/81`, the step
`hatStep` (constant unit block datum on the whole-lattice level-two set `Gp`) with
`β = T²/3 > 0` and `p₁ = c_ψ / 6`, `R_σ = 2`, `R₁ = 2`, `r = 1`, `ε_U = ε_max / 2` (so that the
strengthened smallness `2 ε_U ≤ hatEpsMax … (2 K_c')` holds), every hypothesis of
`stepActivityBound_zeroClass_of_hatExpansion'` (source `0`) and of
`stepActivityBound_zeroClass_source_of_hatExpansion` / `stepNonvanishing_zeroClass_source_of_hatExpansion`
/ `prop26_zeroClass_source_of_hatExpansion` (every source `g` with `‖g/β‖₁ < 1`) holds.

The amplitude `prop33Eps · β` of `hεb` is absorbed by the block scale `ε = δ₁` (it is `O(ε)`),
with `β` fixed first by `RayData` (`hatWitness_core_amp`); the hat radius `c_ψ` is then chosen
against `δ₁` and `‖β_k^{-1/2}‖`, and `p₁ = c_ψ/6` so that `(R_σ R₁ + r) p₁ < c_ψ`.
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation
  Balaban.Localization Balaban.Localization.LevelPair Balaban.Localization.I5Inhabited
  Balaban.Polymer Balaban.SmallField.Def6 Filter Topology

/-- A hat radius `0 < c_ψ ≤ 1` with `a (b (C c_ψ)) < t`. -/
theorem exists_cpsi_le_one (a b C : ℝ) {t : ℝ} (ht : 0 < t) :
    ∃ cψ : ℝ, 0 < cψ ∧ cψ ≤ 1 ∧ a * (b * (C * cψ)) < t := by
  have e := ev_lt (f := fun x : ℝ => a * (b * (C * x))) (by fun_prop) (c := t)
    (by simpa using ht)
  have hp : ∀ᶠ x in 𝓝[>] (0 : ℝ), 0 < x := self_mem_nhdsWithin
  have h1 : ∀ᶠ x in 𝓝[>] (0 : ℝ), x ≤ 1 :=
    eventually_nhdsWithin_of_eventually_nhds
      (eventually_le_nhds (show (0 : ℝ) < 1 by norm_num))
  obtain ⟨x, ⟨h1, h2⟩, h3⟩ := (((eventually_nhdsWithin_of_eventually_nhds e).and hp).and h1).exists
  exact ⟨x, h2, h3, h1⟩

/-- The source with a single nonzero component, of size `β / 2`, at `(y₁, i₁)`. -/
noncomputable def hatSource (m₁ : ℕ) (β : ℝ) (y₁ : CTorus 3 3 9 m₁ 2) (i₁ : Fin 2) :
    Fld 3 3 9 m₁ 2 2 :=
  fun y i => if y = y₁ ∧ i = i₁ then ((β / 2 : ℝ) : ℂ) else 0

theorem hatSource_ne (m₁ : ℕ) {β : ℝ} (hβ : 0 < β) (y₁ : CTorus 3 3 9 m₁ 2) (i₁ : Fin 2) :
    hatSource m₁ β y₁ i₁ ≠ 0 := by
  intro h
  have := congrFun (congrFun h y₁) i₁
  simp [hatSource] at this
  linarith

theorem hatSource_norm (m₁ : ℕ) {β : ℝ} (hβ : 0 < β) (y₁ : CTorus 3 3 9 m₁ 2) (i₁ : Fin 2) :
    ∑ x, ∑ i, ‖hatSource m₁ β y₁ i₁ x i / (β : ℂ)‖ < 1 := by
  have hβ' : (β : ℂ) ≠ 0 := by exact_mod_cast hβ.ne'
  have : ∑ x, ∑ i, ‖hatSource m₁ β y₁ i₁ x i / (β : ℂ)‖ = 1 / 2 := by
    rw [Finset.sum_eq_single y₁]
    · rw [Finset.sum_eq_single i₁]
      · simp only [hatSource, and_self, ↓reduceIte]
        rw [← Complex.ofReal_div, Complex.norm_real, Real.norm_eq_abs]
        rw [abs_of_pos (by positivity)]
        field_simp
      · intro i _ hi
        simp [hatSource, hi]
      · simp
    · intro y _ hy
      apply Finset.sum_eq_zero
      intro i _
      simp [hatSource, hy]
    · simp
  rw [this]; norm_num

open Classical in
/-- **The main assembly**: the step `hatStep m₁ β p₁ δ` carries `RayData`, and the hat-derived
activity bound for the source `0` and for every source `g` with `‖g/β‖₁ < 1`. -/
theorem hatActivity_main :
    ∃ (m₁ : ℕ) (β p₁ δ : ℝ), 0 < β ∧ 0 < p₁ ∧ p₁ < 2 ∧
      Nonempty ((hatStep m₁ β p₁ δ).RayData 2) ∧
      Nonempty (StepActivityBound (hatStep m₁ β p₁ δ) (zeroClass 3 3 9 m₁ 1 2 (rhoSep m₁)) 0) ∧
      ∀ g : Fld 3 3 9 m₁ 2 2, ∑ x, ∑ i, ‖g x i / ((hatStep m₁ β p₁ δ).β : ℂ)‖ < 1 →
        Nonempty (StepActivityBound (hatStep m₁ β p₁ δ) (zeroClass 3 3 9 m₁ 1 2 (rhoSep m₁)) g) := by
  classical
  obtain ⟨-, δ, δ', T, -, -, hδ, hsm, hδ'0, hδ'a, hδ'b, hδ'c, hT, -, hT1, hT2⟩ :=
    exists_witness_params (fun _ => 0)
  set β : ℝ := T ^ 2 / 3 with hβdef
  have hβ0 : 0 < β := by positivity
  obtain ⟨m₁, c, BG, κ, t, c₂, BG₂, κdec, κ0, δc, h4, ht0, ⟨hC⟩, hκ0, hκdec, hκ, h1, hlog, hc7,
    hMX, hdm, hα, hsmX, g1, g2, g3, g4, g5, hκE, hκa, hamp⟩ := hatWitness_core_amp 2 β
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
  have hεM : 0 < hatEpsMax 3 3 2 (2 * κdec - 1) κ0 0 (2 * Kc') := by
    unfold hatEpsMax
    have : 0 < c1 3 3 := by linarith [one_le_c1 3 3]
    have : 0 < 2 * Kc' := by linarith
    positivity
  set εU : ℝ := hatEpsMax 3 3 2 (2 * κdec - 1) κ0 0 (2 * Kc') / 2 with hεUdef
  have hεpos : 0 < εU := by rw [hεUdef]; positivity
  have hεU : 2 * εU ≤ hatEpsMax 3 3 2 (2 * κdec - 1) κ0 0 (2 * Kc') := by
    rw [hεUdef]; linarith
  have hεU' : εU ≤ hatEpsMax 3 3 2 (2 * κdec - 1) κ0 0 Kc' :=
    (by rw [hεUdef]; linarith : εU ≤ hatEpsMax 3 3 2 (2 * κdec - 1) κ0 0 (2 * Kc')).trans
      (hatEpsMax_two_le (by norm_num) hKc0)
  have hεb : prop33Eps 3 3 2 m₁ 1 1 S.a₁ S.ν BG BG₂ κ t 1 0 0 * ‖(S.β : ℂ)‖ +
      ‖(0 : ℂ)‖ * (1 * (c1 3 3 * (((3 : ℕ) : ℝ) ^ (1 + m₁)) ^ 3 *
        nuBd 3 3 2 1 (cK2' 3 3 2 (famConst 3 3 BG₂ κ) * t)
          (K4 3 3 2 BG κ * (xiC1 3 * t) + (1 + 3 * (xiC1 3 * t)) + (1 + 2 / nuW)) / 1)) ≤ εU := by
    rw [norm_zero, zero_mul, add_zero, Complex.norm_real, Real.norm_of_nonneg (show (0 : ℝ) ≤ S.β from hβ0.le)]
    exact hamp
  refine ⟨m₁, β, cψ / 6, δ, hβ0, by positivity, by linarith, ⟨R0⟩, ?_, ?_⟩
  · exact stepActivityBound_zeroClass_of_hatExpansion' S
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
      (by norm_num) (by norm_num) hp hpρ hεpos hεb hκE le_rfl le_rfl (by simpa using hκa) hεU' R0 hlt (by norm_num) rfl rfl
  · intro g hg
    exact stepActivityBound_zeroClass_source_of_hatExpansion S
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
      (by norm_num) (by norm_num) hp hpρ hεpos hεb hκE le_rfl le_rfl (by simpa using hκa) hεU g hg R0 hlt (by norm_num) rfl rfl

/-- **T2: the hypotheses of `stepActivityBound_zeroClass_of_hatExpansion'` (source `0`) are jointly
satisfiable** at an actual step with `β > 0`; the conclusion is instantiated. -/
theorem stepActivityBound_zeroClass_of_hatExpansion_hyps_nonempty :
    ∃ (m₁ : ℕ) (β p₁ δ : ℝ) (S : StepSetting 3 3 9 m₁ 1 2 (rhoSep m₁)),
      S = hatStep m₁ β p₁ δ ∧ 0 < S.β ∧ 0 < S.p₁ ∧ S.p₁ < 2 ∧ Nonempty (S.RayData 2) ∧
      Nonempty (StepActivityBound S (zeroClass 3 3 9 m₁ 1 2 (rhoSep m₁)) 0) := by
  obtain ⟨m₁, β, p₁, δ, hβ, hp, hlt, hR, hA, -⟩ := hatActivity_main
  exact ⟨m₁, β, p₁, δ, hatStep m₁ β p₁ δ, rfl, hβ, hp, hlt, hR, hA⟩

/-- **T3: the hypotheses of `stepActivityBound_zeroClass_source_of_hatExpansion` are jointly
satisfiable with a nonzero source** `g` (a single component of size `β / 2`, so that
`‖g/β‖₁ = 1/2 < 1`): the activity bound, `StepNonvanishing` and the Proposition 2.6 identity hold
at the datum. -/
theorem stepActivityBound_zeroClass_source_hyps_nonempty :
    ∃ (m₁ : ℕ) (β p₁ δ : ℝ) (S : StepSetting 3 3 9 m₁ 1 2 (rhoSep m₁)) (g : Fld 3 3 9 m₁ 2 2),
      S = hatStep m₁ β p₁ δ ∧ 0 < S.β ∧ 0 < S.p₁ ∧ S.p₁ < 2 ∧ Nonempty (S.RayData 2) ∧ g ≠ 0 ∧
      ∑ x, ∑ i, ‖g x i / (S.β : ℂ)‖ < 1 ∧
      Nonempty (StepActivityBound S (zeroClass 3 3 9 m₁ 1 2 (rhoSep m₁)) g) ∧
      S.StepNonvanishing (zeroClass 3 3 9 m₁ 1 2 (rhoSep m₁)) g ∧
      S.Tstep (zeroClass 3 3 9 m₁ 1 2 (rhoSep m₁)) g = Complex.exp (-(S.β : ℂ) * (S.Anew : ℂ) +
        EcompAt (zeroClass 3 3 9 m₁ 1 2 (rhoSep m₁)).m₀ (zeroClass 3 3 9 m₁ 1 2 (rhoSep m₁)).Tm
          S.a S.ν (Nat.le_succ 1) S.psiKd - (S.Eppp (zeroClass 3 3 9 m₁ 1 2 (rhoSep m₁)) : ℂ) *
          (S.nU : ℂ) + FcompAt (zeroClass 3 3 9 m₁ 1 2 (rhoSep m₁)).m₀
          (zeroClass 3 3 9 m₁ 1 2 (rhoSep m₁)).Tm S.a S.ν (Nat.le_succ 1) S.psiKd g +
        S.E0 (zeroClass 3 3 9 m₁ 1 2 (rhoSep m₁)) +
        S.F0 (zeroClass 3 3 9 m₁ 1 2 (rhoSep m₁)) g) := by
  obtain ⟨m₁, β, p₁, δ, hβ, hp, hlt, ⟨R0⟩, -, hA⟩ := hatActivity_main
  set S := hatStep m₁ β p₁ δ with hS
  have hβS : 0 < S.β := hβ
  have hg := hatSource_norm m₁ hβS 0 0
  obtain ⟨I⟩ := hA (hatSource m₁ S.β 0 0) hg
  refine ⟨m₁, β, p₁, δ, S, hatSource m₁ S.β 0 0, rfl, hβS, hp, hlt, ⟨R0⟩,
    hatSource_ne m₁ hβS 0 0, hg, ⟨I⟩, stepNonvanishing_of_activityBound I, ?_⟩
  exact prop26_complex_class_of_activity S (zeroClass 3 3 9 m₁ 1 2 (rhoSep m₁)) R0.ha₁ R0.H
    R0.hδ'0 R0.hδ' R0.hD'R R0.hδ0 R0.hfam R0.hsm R0.hχu R0.hnorm R0.hβ hp hlt R0.hB5 R0.hK2
    R0.hp40 R0.hrad (hatSource m₁ S.β 0 0) (classRegular_zeroClass R0 hp hlt _) I

/-- **T4 (non-degeneracy)**: for the datum of T2/T3 with a single-component source `g` of size
`β / 2` at a suitable `(y₁, i₁)`, the exponent `W₁(s, x) + W₂(t, x)` of the activity bound is not
identically zero on the segments: at a point `x₀` with `‖x₀‖ < p₁` the background field moves
along the ray (`RayData.bgField_ne_nu`), and either `V_k(ψ^{(k)} + ψ̂)` is nonzero at `s = 1`
(`(s, t) = (1, 0)`) or the background term gives `(1, 1)`. -/
theorem stepActivityBound_zeroClass_source_nondegenerate :
    ∃ (m₁ : ℕ) (β p₁ δ : ℝ) (S : StepSetting 3 3 9 m₁ 1 2 (rhoSep m₁)) (g : Fld 3 3 9 m₁ 2 2),
      S = hatStep m₁ β p₁ δ ∧ 0 < S.β ∧ 0 < S.p₁ ∧ S.p₁ < 2 ∧ Nonempty (S.RayData 2) ∧ g ≠ 0 ∧
      ∑ x, ∑ i, ‖g x i / (S.β : ℂ)‖ < 1 ∧
      Nonempty (StepActivityBound S (zeroClass 3 3 9 m₁ 1 2 (rhoSep m₁)) g) ∧
      ∃ p ∈ stepSegments, ∃ x : S.E,
        S.WoneT (zeroClass 3 3 9 m₁ 1 2 (rhoSep m₁)) p.1 x +
          S.WtwoT (zeroClass 3 3 9 m₁ 1 2 (rhoSep m₁)) g p.2 x ≠ 0 := by
  obtain ⟨m₁, β, p₁, δ, hβ, hp, hlt, ⟨R0⟩, -, hA⟩ := hatActivity_main
  set S := hatStep m₁ β p₁ δ with hS
  have hβS : 0 < S.β := hβ
  have hcons := theta_consts (d := 3) (L := 3) (N := 2) (by norm_num) R0.hδ'0 R0.hδ'
  have hDU : InUnionDomainR S.G' (bgC1 3 3 2) S.ν S.D' := ⟨R0.δ', R0.hδ'0, hcons.2.2.1, R0.hD'R⟩
  have ha : ∀ n, 0 ≤ compWeight 3 (1 : ℝ) n := fun n => compWeight_nonneg_three 1 zero_le_one n
  have hbg0 : bgField S.G' S.a S.ν S.D' = unitPhi S.G' hN2 :=
    bgField_unitBg_nu (isLevel_Gp (m₁ := m₁) (ϱ := rhoSep m₁)) hN2 (a := compWeight 3 1) ha
      R0.H hDU
  obtain ⟨x₀, hx₀, y₁, i₁, hne⟩ := R0.exists_move (rfl : S.h₀ = unitVec hN2) hbg0 hp
    (show S.p₁ < 2 from hlt)
  have hg := hatSource_norm m₁ hβS y₁ i₁
  obtain ⟨I⟩ := hA (hatSource m₁ S.β y₁ i₁) hg
  refine ⟨m₁, β, p₁, δ, S, hatSource m₁ S.β y₁ i₁, rfl, hβS, hp, hlt, ⟨R0⟩,
    hatSource_ne m₁ hβS y₁ i₁, hg, ⟨I⟩, ?_⟩
  have hχ : chiFl S.U 2 S.p₁ x₀ = 1 := (chiFl_eq_one_iff hp x₀).2 hx₀
  have hexp : ∀ s t : ℝ, S.WoneT (zeroClass 3 3 9 m₁ 1 2 (rhoSep m₁)) s x₀ +
      S.WtwoT (zeroClass 3 3 9 m₁ 1 2 (rhoSep m₁)) (hatSource m₁ S.β y₁ i₁) t x₀ =
      -(S.β : ℂ) * S.Vk (S.psiAt s x₀) + ((S.β / 2 : ℝ) : ℂ) *
        (S.bgComp y₁ i₁ (t, x₀) - S.bgComp y₁ i₁ (0, x₀)) := by
    intro s t
    rw [S.WoneT_of_chi _ s x₀ hχ, S.WtwoT_of_chi _ _ t x₀ hχ, S.Wone_zeroClass]
    exact congrArg _ (S.Wtwo_single y₁ i₁ (S.β / 2) t x₀)
  have hβc : (S.β : ℂ) ≠ 0 := by exact_mod_cast hβS.ne'
  have hlam : ((S.β / 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (by positivity : (S.β / 2 : ℝ) ≠ 0)
  by_cases hV : S.Vk (S.psiAt 1 x₀) = 0
  · refine ⟨(1, 1), Or.inr ⟨rfl, ⟨zero_le_one, le_rfl⟩⟩, x₀, ?_⟩
    show S.WoneT _ 1 x₀ + S.WtwoT _ _ 1 x₀ ≠ 0
    rw [hexp 1 1, hV, mul_zero, zero_add]
    exact mul_ne_zero hlam (sub_ne_zero.2 hne)
  · refine ⟨(1, 0), Or.inr ⟨rfl, ⟨le_rfl, zero_le_one⟩⟩, x₀, ?_⟩
    show S.WoneT _ 1 x₀ + S.WtwoT _ _ 0 x₀ ≠ 0
    rw [hexp 1 0, sub_self, mul_zero, add_zero]
    exact mul_ne_zero (neg_ne_zero.2 hβc) hV

end Balaban.Inhabited
