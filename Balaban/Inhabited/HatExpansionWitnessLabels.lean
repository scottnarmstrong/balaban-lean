/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.HatExpansionWitness
public import Balaban.Fluctuation.HatLabelsDm
public import Balaban.Inhabited.XiCDomains
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FunProp

/-!
# The hypotheses of `labelAct_of_interaction_expansion_hat` are jointly satisfiable

`labelAct_of_interaction_expansion_hat_hyps_nonempty`: on the data of
`interaction_expansion_hat_hyps_nonempty` (for `0 < N`), with a step datum `S` on the same set
`S.G' = 𝔹_2` (zero block field, `p₁ = c_ψ / 4 = ρ`), the ray inequality `(R_σ R₁ + r) ρ < c_ψ`,
`L^{m₀} ∣ N₁`, the rates `κ₀ = a_ent + 1`, `K_c = K₀ + 1`, `κ' = 0`, `κ_dec` of `hatWitness_core`,
`ε_U = hatEpsMax`, and `c_β = c_ν > 0` small against `ε_U`, the label activities exist.
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation
  Balaban.Localization Balaban.Localization.LevelPair Balaban.Localization.I5Inhabited
  Balaban.Polymer MeasureTheory Filter Topology

/-- The step datum of the witness: `G' = 𝔹_2` of `LevelPair`, zero block field, radius `p₁`. -/
noncomputable def hatWitnessStep (N m₁ : ℕ) (p₁ : ℝ) :
    StepSetting 3 3 9 m₁ 1 N (rhoSep m₁) where
  G' := Gp m₁ (rhoSep m₁)
  hk1 := le_rfl
  hG' := isLevel_Gp
  D' := { Ψ := fun _ _ => 0, h := fun _ _ => 0
          Ψ_layerConst := fun _ _ _ _ _ _ _ => rfl
          h_layerConst := fun _ _ _ _ _ _ _ => rfl
          Ψ_zero := fun _ _ => rfl, h_zero := fun _ _ => rfl }
  h₀ := fun _ => 0
  hh₀ := fun _ _ => by simp
  a₁ := 1
  ν := nuW
  β := 0
  p₁ := p₁
  δ := 0

theorem hatWitnessStep_G' (N m₁ : ℕ) (p₁ : ℝ) :
    (hatWitnessStep N m₁ p₁).G' = Gp m₁ (rhoSep m₁) := rfl


open Classical in
/-- **The hypotheses of `labelAct_of_interaction_expansion_hat` are jointly satisfiable**, and its
conclusion holds for the resulting data (no old energy terms, no observable terms). -/
theorem labelAct_of_interaction_expansion_hat_hyps_nonempty (N : ℕ) (hN0 : 0 < N) :
    ∃ (m₁ : ℕ) (c BG κ eps c₂ BG₂ κdec κ0 κ' Kc' εU cψ : ℝ)
      (S : StepSetting 3 3 9 m₁ 1 N (rhoSep m₁))
      (_ : FlCore N S.G' (Hm m₁ (rhoSep m₁)) 1 nuW c BG κ eps (levelKc 3 3)
        (Cchi 3 3) c₂ BG₂ eps) (cβ cν : ℂ) (hp : 0 < S.p₁)
      (Θ₀ : RawData 3 3 (9 * 3 ^ m₁) 2 N × (CTorus 3 3 9 m₁ 2 → Fin N → ℂ)),
      S.G' = Gp m₁ (rhoSep m₁) ∧ 0 < eps ∧ 0 < cψ ∧ 0 < εU ∧ cβ ≠ 0 ∧ cν ≠ 0 ∧
      Θ₀ ∈ XiCRaw S.G' (compWeight 3 1) nuW (1 + 1) 1 eps ×ˢ l1Ball 3 3 9 m₁ 2 N ∧
      ∃ (Lb : Type) (_ : Fintype Lb)
        (Lab : CubeLabels (d := 3) (L := 3) (N₁ := 9) (m₁ := m₁) (K := 1 + 1) 1 (1 + 1)
          Set.univ Lb)
        (A : ℂ → LabelAct Lab (S.blockSplit 1 hp).Ωb (hatEpsH 3 3 1 εU (2 * κdec - 1))
          (hatKappaH 3 3 (2 * κdec - 1)) κ0 Kc'),
        (∀ y Φ, DifferentiableOn ℂ (fun u => (A u).H y Φ) (Metric.ball 0 1)) ∧
        (∀ u : ℂ, ‖u‖ < 1 → ∀ᵐ x ∂S.nuFl, ∑ y, (A u).H y ((S.blockSplit 1 hp).restr x) =
          (fun x w σ p =>
            (-cβ) * raySrc3 (hatFun S.G' 1 nuW eps S.hG' 1
                (interactionOne (isLevel_Hm (m₁ := m₁) (ϱ := rhoSep m₁)) S.hG' le_rfl 1 nuW eps))
              taylorWeight x.1 w.1 σ p.1 +
            cβ * (∑ s : CTorus 3 3 9 m₁ 2 × Fin N, p.2 s.1 s.2 *
              dirTermSrc (hatFun S.G' 1 nuW eps S.hG' 1
                (onXi S.G' 1 nuW eps
                  (fun D ψ' => svec (Hm m₁ (rhoSep m₁)) (flFieldOne S.G'
                    (Hm m₁ (rhoSep m₁)) BG₂ κ 1 nuW D ψ') s.1 s.2)))
                (fun _ => (1 : ℂ)) x.2 w.2 σ p.1) +
            cν * dirTermSrc (hatFun S.G' 1 nuW eps S.hG' 1
              (onXi S.G' 1 nuW eps
                (fun D ψ' => nuTotal S.G' (Hm m₁ (rhoSep m₁)) 1 nuW BG₂ κ D ψ')))
              (fun _ => (1 : ℂ)) x.1 w.1 σ p.1)
          (S.hatC x, S.hatC x) (S.hatC x, S.hatC x) u Θ₀) ∧
        (0 < hatEpsH 3 3 1 εU (2 * κdec - 1) ∧
          κ' + 3 * κ0 + c1 3 3 + 3 / 2 ≤ hatKappaH 3 3 (2 * κdec - 1) ∧
          hatEpsH 3 3 1 εU (2 * κdec - 1) ≤ 1 / (8 * Kc' ^ 3 * c1 3 3 *
            Real.exp ((hatKappaH 3 3 (2 * κdec - 1) - 2 * κ0) * cG 3 3 + c1 3 3 + κ' * cG 3 3))) := by
  obtain ⟨m₁, c, BG, κ, t, c₂, BG₂, κdec, κ0, δc, h4, ht0, ⟨hC⟩, hκ0, hκdec, hκ, h1, hlog, hc7,
    hMX, hdm, hα, hsmX, g1, g2, g3, g4, g5, hκE, hκa⟩ := hatWitness_core N
  obtain ⟨cψ, hcψ0, hδ₁⟩ := exists_cpsi (Real.sqrt N)
    (covSupConstC 3 3 N (compWeight 3 (1 : ℝ) 1) κ) ht0
  have hA2 : (1 : ℝ) ≤ c1 3 3 := one_le_c1 3 3
  -- the rates
  have hK0 : 0 ≤ K0 3 3 κ0 := by
    unfold K0
    apply div_nonneg (Real.exp_pos _).le
    have : Real.exp (-1) < 1 := by simp
    linarith
  set Kc' : ℝ := K0 3 3 κ0 + 1 with hKc'
  have hKc0 : 0 < Kc' := by rw [hKc']; linarith
  have hεpos' : 0 < hatEpsMax 3 3 1 (2 * κdec - 1) κ0 0 Kc' := by
    unfold hatEpsMax
    have : 0 < c1 3 3 := by linarith
    positivity
  set εU := hatEpsMax 3 3 1 (2 * κdec - 1) κ0 0 Kc' with hεU
  -- the coefficients
  obtain ⟨cc, hc0, hcc⟩ := exists_small_coeff
    (prop33Eps 3 3 N m₁ 1 1 1 nuW BG BG₂ κ t 1 0 0)
    (1 * (c1 3 3 * (((3 : ℕ) : ℝ) ^ (1 + m₁)) ^ 3 *
      nuBd 3 3 N 1 (cK2' 3 3 N (famConst 3 3 BG₂ κ) * t)
        (K4 3 3 N BG κ * (xiC1 3 * t) + (1 + 3 * (xiC1 3 * t)) + (1 + 2 / nuW)) / 1)) hεpos'
  have hnorm : ‖(cc : ℂ)‖ = cc := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc0]
  -- the step datum
  have hp : 0 < (hatWitnessStep N m₁ (cψ / 4)).p₁ := by
    show 0 < cψ / 4
    positivity
  have hxi1 : xiC1 3 * t ≤ 1 := by
    have h1 := hC.c7le
    have h2 := c7_le_bgC1 3 3 N BG κ
    have h3 := bgC1_le_small 3 3 N (by norm_num)
    linarith
  have hBh := hBh_of_xi (N := N) (Gp := Gp m₁ (rhoSep m₁)) (bgHypNu m₁) nuW_pos hC.small1
    hC.eps_pos hxi1
  obtain ⟨D, hD⟩ := exists_xiCData (N := N) (bgHypNu m₁)
    (Gp m₁ (rhoSep m₁)) hN0 (by unfold nuW; norm_num) hC.eps_pos
  have hΘ₀ : ((rawOf D, (0 : CTorus 3 3 9 m₁ 2 → Fin N → ℂ)) :
      RawData 3 3 (9 * 3 ^ m₁) 2 N × (CTorus 3 3 9 m₁ 2 → Fin N → ℂ)) ∈
      XiCRaw (hatWitnessStep N m₁ (cψ / 4)).G' (compWeight 3 1) nuW (1 + 1) 1 t ×ˢ
        l1Ball 3 3 9 m₁ 2 N :=
    ⟨⟨D, hD, rfl⟩, by simp [l1Ball]⟩
  refine ⟨m₁, c, BG, κ, t, c₂, BG₂, κdec, κ0, 0, Kc', εU, cψ, hatWitnessStep N m₁ (cψ / 4), hC,
    (cc : ℂ), (cc : ℂ), hp, (rawOf D, 0), rfl, ht0, hcψ0, hεpos', ?_, ?_, hΘ₀, ?_⟩
  · exact_mod_cast hc0.ne'
  · exact_mod_cast hc0.ne'
  have key := labelAct_of_interaction_expansion_hat (hatWitnessStep N m₁ (cψ / 4))
    (Rσ := 1) (R₁ := 2) (r := 1) (R := 2) (m₀ := 1) (κdec := κdec) (κ₀ := κ0) (ρE := 0)
    (ρM := 0) (Bh := 1 + 2 / nuW) (δc := δc) (cψ := cψ) (ρ := cψ / 4) (εU := εU) (κ0 := κ0)
    (κ' := 0) (Kc' := Kc')
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
    hC (cc : ℂ) hatConn (rowInHat_level (dgSettingNu h4) isLevel_Hm isLevel_Gp) hκ0
    hκdec (by exact_mod_cast hκ) h1 (by norm_num) (by norm_num) le_rfl isLevel_Hm 1
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
    (fun p => by simp) (by unfold nuW; norm_num) hBh (cc : ℂ)
    (fun z x _ => Finset.mem_coe.2 (Finset.mem_univ _)) one_pos
    (by show (1 * 2 + 1) * (cψ / 4) < cψ; linarith) hΘ₀ (by norm_num) (by norm_num) hp le_rfl
    hεpos' (by rw [hnorm]; exact hcc) hκE le_rfl le_rfl (by simpa using hκa) le_rfl
  obtain ⟨Lb, hLb, Lab, A, hA, hsum, hnum⟩ := key
  refine ⟨Lb, hLb, Lab, A, hA, fun u hu => ?_, hnum⟩
  filter_upwards [hsum u hu] with x hx
  rw [hx]
  simp

end Balaban.Inhabited
