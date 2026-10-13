/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.StepActivityDirectWitness
public import Balaban.Fluctuation.ParamActivitySubspace
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FunProp

/-!
# The physical `ParamMarkFamily` over the subspace of data has an instance

At the step `hatStep m₁ β p₁ δ` (`d = L = 3`, `β > 0`) of `directActivity_main`, with the datum
`Θ₀ = (rawOf S.D', 0)` of the step, all hypotheses of `physical_paramMarkFamily_exists` hold (they
are those of `stepActivityBound_zeroClass_direct`, with the same constants).  Hence the open set
`physV` of the parameter space `rawSub × sources` is non-empty (it contains the datum of the step
with source `0`), and the physical activities over it form a `ParamMarkFamily` (no marks).  The
generating set of the chart `physSΛ` and of the datum `Θ₀` are the same (`S.G'`, `S.D'`), so
nothing differs between the two witnesses.
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation
  Balaban.Localization Balaban.Localization.LevelPair Balaban.Localization.I5Inhabited
  Balaban.Polymer Balaban.SmallField.Def6 Filter Topology MeasureTheory Metric

open Classical in
/-- **A non-empty open parameter set with a `ParamMarkFamily` of physical activities.**  At a step
`hatStep m₁ β p₁ δ` with `β > 0`: the open set `physV` of the parameter space `rawSub × sources`
is non-empty, and there are labels and activities over `physParam` forming a `ParamMarkFamily`
over `physV` (carrier `physCarrier`, `𝒰 = ball 0 R_σ`, `R_σ > 1`); the activities are those of
`physical_paramMarkFamily_exists`. -/
theorem physical_paramMarkFamily_nonempty :
    ∃ (m₁ : ℕ) (β p₁ δ t : ℝ) (S : StepSetting 3 3 9 m₁ 1 2 (rhoSep m₁)),
      S = hatStep m₁ β p₁ δ ∧ 0 < β ∧
      ∃ (hp : 0 < S.p₁) (Rσ εU a κ0 Kc : ℝ) (𝒴 : Finset (Set (CTorus 3 3 9 m₁ (1 + 1))))
        (dom : ∀ Y ∈ 𝒴, IsDj 1 (1 + 1) Y)
        (A : physParam 2 S → ℂ → LabelAct (thickLabels 𝒴 dom) (S.blockSplit 1 hp).Ωb
          (Rσ * εU) a κ0 Kc),
        1 < Rσ ∧ (physV S S.a₁ S.ν t).Nonempty ∧
        Nonempty (ParamMarkFamily (S.blockSplit 1 hp).μ (thickLabels 𝒴 dom) A
          (fun e : Empty => e.elim) (fun _ _ _ _ => (0 : ℂ)) 0 (fun e : Empty => e.elim)
          (physV S S.a₁ S.ν t) (ball (0 : ℂ) Rσ) (physCarrier S 1 hp)) := by
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
  obtain ⟨I, hF, ⟨e₀, he₀, -⟩, ⟨P⟩⟩ := physical_paramMarkFamily_exists (S := S) (cβ := (S.β : ℂ))
      (cc := ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) (cν := 0)
      (Θ₀ := (rawOf S.D', (0 : CTorus 3 3 9 m₁ (1 + 1) → Fin 2 → ℂ)))
      (hΘ₀ := ⟨⟨S.D', hD, rfl⟩, by simp [l1Ball]⟩) (Hϱ := bgHypNu m₁) (hρ := by positivity)
      (hεU := hεpos.le) (hRσ1 := one_lt_two) (hκ0 := hκE) (hKc := by rw [hKc']; linarith)
      (ρ := cψ / 6) (εU := εU) (κ0 := κ0) (Kc' := Kc') (Rσ := 2) (R₁ := 2) (r := 1) (R := 2) (m₀ := 1) (κdec := κdec) (κ₀ := κ0) (ρE := 0) (ρM := 0) (Bh := 1 + 2 / nuW) (δc := δc) (cψ := cψ) (jV := fun _ => 1) (XV := fun _ => Xr) (𝒦XV := fun _ => {0}) (X₁V := fun _ => Finset.univ) (jF := fun _ => 1) (XF := fun _ => Xr) (𝒦XF := fun _ => {0}) (X₁F := fun _ => Finset.univ) (τι := PEmpty.{1}) (μι := PEmpty.{1}) (ϱ₁ := fun _ => 0) (ϱ₂ := fun _ => 0) (GkE := fun τ => PEmpty.elim τ) (GjE := fun τ => PEmpty.elim τ) (r₀ := 0) (δ₃ := 0) (δfl := 0) (X₀E := fun _ => ∅) (X₁E := fun _ => ∅) (jE := fun _ => 0) (XE := fun _ => ∅) (𝒦XE := fun _ => ∅) (EbE := fun _ => 0) (EE := fun _ _ => 0) (ϱ₁M := fun _ => 0) (ϱ₂M := fun _ => 0) (GkM := fun τ => PEmpty.elim τ) (GjM := fun τ => PEmpty.elim τ) (X₀M := fun _ => ∅) (X₁M := fun _ => ∅) (jM := fun _ => 0) (XM := fun _ => ∅) (𝒦XM := fun _ => ∅) (EbM := fun _ => 0) (EM := fun _ _ => 0) (hC := hC) (hconn := hatConn) (hrow := (rowInHat_level (dgSettingNu h4) isLevel_Hm isLevel_Gp)) (hκ₀ := hκ0) (hκdec := hκdec) (hκ := (by exact_mod_cast hκ)) (h1 := h1) (hR₁ := (by norm_num)) (hr := (by norm_num)) (hk := le_rfl) (hG := isLevel_Hm) (hcψ := hcψ0.le) (hMX := hMX) (hdm := hdm) (hα := hα) (hsmX := hsmX) (hδ₁ := hδ₁) (ha₁ := one_pos) (H := (bgHypNu m₁)) (hc7 := hc7) (hR := le_rfl) (hRs := g1) (hsmall := g2) (hnum := g3) (hnum' := g4) (hsm := g5) (hcovV := (fun _ => covSetup)) (hX₁V := (fun _ => by rw [Finset.coe_univ]; exact X1_eq_univ.symm)) (hoptV := (fun _ => hopt)) (hΔV := (fun _ => treeLen_zero)) (hlogV := (fun _ => hlog)) (hZV := (fun z _ _ => Finset.mem_coe.2 (Finset.mem_univ _))) (hmarV := (fun z => blockMargin_univ fun x _ _ => mem_some_intBox h4 x)) (𝒯E := (∅ : Finset PEmpty.{1})) (hBE := (fun τ hτ => absurd hτ (by simp))) (hFE := (fun τ hτ => absurd hτ (by simp))) (hcovE := (fun τ hτ => absurd hτ (by simp))) (hX₁E := (fun τ hτ => absurd hτ (by simp))) (hoptE := (fun τ hτ => absurd hτ (by simp))) (hlogE := (fun τ hτ => absurd hτ (by simp))) (hEbE := (fun τ hτ => absurd hτ (by simp))) (hEanE := (fun τ hτ => absurd hτ (by simp))) (hEbdE := (fun τ hτ => absurd hτ (by simp))) (hcovF := (fun _ => covSetup)) (hX₁F := (fun _ => by rw [Finset.coe_univ]; exact X1_eq_univ.symm)) (hoptF := (fun _ => hopt)) (hΔF := (fun _ => treeLen_zero)) (hlogF := (fun _ => hlog)) (hyF := (fun s => Finset.mem_univ _)) (𝒯M := (∅ : Finset PEmpty.{1})) (ys := (fun τ => PEmpty.elim τ)) (is := (fun τ => PEmpty.elim τ)) (hys := (fun τ hτ => absurd hτ (by simp))) (hBM := (fun τ hτ => absurd hτ (by simp))) (hFM := (fun τ hτ => absurd hτ (by simp))) (hcovM := (fun τ hτ => absurd hτ (by simp))) (hX₁M := (fun τ hτ => absurd hτ (by simp))) (hoptM := (fun τ hτ => absurd hτ (by simp))) (hlogM := (fun τ hτ => absurd hτ (by simp))) (hEbM := (fun τ hτ => absurd hτ (by simp))) (hEanM := (fun τ hτ => absurd hτ (by simp))) (hEbdM := (fun τ hτ => absurd hτ (by simp))) (rE := (fun τ => PEmpty.elim τ)) (hrE := (fun τ hτ => absurd hτ (by simp))) (hρE0 := le_rfl) (hρE := (fun x => by simp)) (hρM0 := le_rfl) (hρM := (fun p => by simp)) (hBh0 := (by unfold nuW; norm_num)) (hBh := hBh) (hZν := (fun z x _ => Finset.mem_coe.2 (Finset.mem_univ _))) (hRσ := (by norm_num)) (hc := hc) (hεb := hεb) (hN := (by norm_num)) (hp := hp)
  exact ⟨m₁, β, cψ / 6, δ, t, S, rfl, hβ0, hp, 2, εU, _, κ0, Kc', I.𝒴, I.dom, _, one_lt_two,
    ⟨e₀, he₀⟩, ⟨P⟩⟩

end Balaban.Inhabited
