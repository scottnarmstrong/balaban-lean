/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.StepActivityDirectWitness
public import Balaban.Fluctuation.StepActivityDirectEta
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FunProp

/-!
# Non-vacuity of the `η`-weighted direct step activity bound

At the step `hatStep m₁ β p₁ δ` of `StepActivityDirectWitness` every hypothesis of
`stepActivityBound_zeroClass_direct_eta` holds with the explicit `η = 1/2 < 1`: the amplitude
hypothesis is the landed one (`directWitness_core_amp`) weakened by
`prop33EpsEta_hyp_of_old`, since `prop33EpsEta η ≤ prop33Eps` for `η ≤ 1`.  The witness is the
landed one (`ρ_E = ρ_M = 0`, empty old and observable families, `c_ν = 0`, source `0`); it
shows that the hypotheses of the theorem are jointly satisfiable and the activity bound exists.
It does not exhibit a regime where the weaker amplitude requirement is strictly weaker than the
landed one.
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation
  Balaban.Localization Balaban.Localization.LevelPair Balaban.Localization.I5Inhabited
  Balaban.Polymer Balaban.SmallField.Def6 Filter Topology

open Classical in
/-- **The main assembly with an `η`-weighted source allowance**: at the landed witness step
`hatStep m₁ β p₁ δ`, the hypotheses of `stepActivityBound_zeroClass_direct_eta` hold with
`η = 1/2 < 1` (the proof calls that theorem), and the activity bound of the zero class exists. -/
theorem directActivityEta_main :
    ∃ (m₁ : ℕ) (β p₁ δ η : ℝ), 0 < β ∧ 0 < p₁ ∧ p₁ < 2 ∧ 0 < η ∧ η < 1 ∧
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
  have hB0 : 0 ≤ famConst 3 3 BG₂ κ := by
    have := famConst_ge_one (L := 3) hC.hS2.fam.2.1 κ (d := 3) (by norm_num); linarith
  have hK : 0 ≤ cK2' 3 3 2 (famConst 3 3 BG₂ κ) * t :=
    mul_nonneg (cK2'_nonneg hB0) ht0.le
  have hεb' := prop33EpsEta_hyp_of_old 3 3 2 m₁ 1 1 S.a₁ S.ν BG BG₂ κ t 1 0 0 (1 / 2) εU _
    (S.β : ℂ) one_pos hK le_rfl (by norm_num) hεb
  refine ⟨m₁, β, cψ / 6, δ, 1 / 2, hβ0, by positivity, by linarith, by norm_num, by norm_num, ⟨R0⟩, ?_⟩
  obtain ⟨B, hB1, hB2⟩ := stepActivityBound_zeroClass_direct_eta S (η := 1 / 2) (hη0 := by norm_num)
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
      (by norm_num) hp hpρ hεpos hεb' hκE le_rfl le_rfl hκa' hDA R0 hlt (StepSetting.baseDomain_of_rayData R0) (by norm_num) rfl rfl
  exact ⟨B, κdec, 2, εU, hB1, hB2, one_lt_two, hεpos⟩

/-- **T5: the hypotheses of `stepActivityBound_zeroClass_direct_eta` are jointly satisfiable** at
an actual step with `β > 0`, for an explicit `η < 1`. -/
theorem stepActivityBound_zeroClass_direct_eta_hyps_nonempty :
    ∃ (m₁ : ℕ) (β p₁ δ η : ℝ) (S : StepSetting 3 3 9 m₁ 1 2 (rhoSep m₁)),
      S = hatStep m₁ β p₁ δ ∧ 0 < S.β ∧ 0 < S.p₁ ∧ S.p₁ < 2 ∧ 0 < η ∧ η < 1 ∧
      Nonempty (S.RayData 2) ∧
      ∃ B : StepActivityBound S (zeroClass 3 3 9 m₁ 1 2 (rhoSep m₁)) 0,
        ∃ κdec Rσ εU : ℝ, B.κH = 2 * κdec - 1 ∧ B.εH = Rσ * εU ∧ 1 < Rσ ∧ 0 < εU := by
  obtain ⟨m₁, β, p₁, δ, η, hβ, hp, hlt, hη, hη1, hR, hA⟩ := directActivityEta_main
  exact ⟨m₁, β, p₁, δ, η, hatStep m₁ β p₁ δ, rfl, hβ, hp, hlt, hη, hη1, hR, hA⟩

end Balaban.Inhabited
