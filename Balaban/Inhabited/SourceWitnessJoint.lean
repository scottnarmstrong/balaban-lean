/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.SourceExponentFamily
public import Balaban.Fluctuation.ObsRayActivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# One witness for the source lane at the shared tower

The landed theorems `sourceActivityC_scale_fromTower`, `sourceExponentFamily_fromTower` and
`obsRayActivity_fromTower` each call `sourceDirectTerms_scale_fromTower` separately, so the
direct-term value, the domain family `𝒴` and the terms `Tt` of their conclusions cannot be
identified.  `sourceWitness_fromTower` calls it once, per scale, and returns for that single
`val, 𝒴, Tt` the activity records of every source, the exponent family on the constant-`h_0`
fibre and the observable ray activities, together with the amplitude `ε_U`, `0 < ε_U`, and its
log-form bound `4 ε_U <= C_E (log b)^(3p) / sqrt b + C_F (log b)^p / sqrt b`, `b = β 3^k`.
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation
  Balaban.Localization Balaban.Localization.LevelPair Balaban.Localization.I5Inhabited
  Balaban.Polymer Balaban.SmallField.Def6 Balaban.Inhabited.LevelStep Filter Topology
  MeasureTheory Set

open Classical in
/-- **One witness for the source lane at the shared tower `T`.**  After `T` choose one threshold
`β₀` and one pair `C_E, C_F`.  For every scale and `D : StepScaleData T …` with `β ≥ β₀`,
`0 < p₁ ≤ A₁ (log β_k)^p`, there is ONE `val, 𝒴, Tt` (from a single call of
`sourceDirectTerms_scale_fromTower`), with its value formula, and `ε_U > 0` the physical amplitude
with `4 ε_U ≤ C_E (log b)^(3p)/√b + C_F (log b)^p/√b`, such that (a) every source `g` of the `l¹`
ball has the records `BR`, `BC` of `sourceActivityC_scale_fromTower` on the labels of `𝒴` with
`BR.ε_H = 4 ε_U`; (b) the exponent family of `sourceExponentFamily_fromTower` on the labels of `𝒴`
with amplitude `4 ε_U`; (c) the observable ray activities of `obsRayActivity_fromTower` on the
thick labels of `𝒴` and the terms `Tt`, with amplitude `ε_U`. -/
theorem sourceWitness_fromTower {κmin : ℝ} (T : StepTower κmin) {A₁ : ℝ}
    (hA : 0 < A₁) (p : ℕ) :
    ∃ β₀ CE CF : ℝ, 2 ≤ β₀ ∧ 0 < CE ∧ 0 < CF ∧
    ∀ (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁], 3 ∣ N₁ → 5 < N₁ →
    ∀ ν : ℝ, 0 < ν → ν * 3 ^ (2 * (k + 1)) ≤ 1 →
    ∀ β : ℝ, β₀ ≤ β → ∀ (p₁ : ℝ), 0 < p₁ →
    p₁ ≤ pLog A₁ p (β * 3 ^ k) → StepScaleData T k hk N₁ ν β p₁ →
    ∀ (S : StepSetting 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)), S = T.step k hk N₁ ν β p₁ →
    ∀ (hp : 0 < S.p₁),
    ∃ (val : ((S.U × Fin 2 → ℂ) × (S.U × Fin 2 → ℂ)) → ((S.U × Fin 2 → ℂ) × (S.U × Fin 2 → ℂ)) →
        ℂ → (RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2 × (CTorus 3 3 N₁ T.m₁ (k + 1) → Fin 2 → ℂ)) → ℂ)
      (𝒴 : Finset (Set (CTorus 3 3 N₁ T.m₁ (k + 1))))
      (Tt : Set (CTorus 3 3 N₁ T.m₁ (k + 1)) → ((S.U × Fin 2 → ℂ) × (S.U × Fin 2 → ℂ)) →
        ((S.U × Fin 2 → ℂ) × (S.U × Fin 2 → ℂ)) → ℂ →
        (RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2 × (CTorus 3 3 N₁ T.m₁ (k + 1) → Fin 2 → ℂ)) → ℂ)
      (hdom : ∀ Y ∈ 𝒴, IsDj 1 (k + 1) Y),
      (∀ x w σ Θ, val x w σ Θ =
        (-(S.β : ℂ)) * raySrc3 (hatFun S.G' S.a₁ S.ν T.t S.hG'
          ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)
          (interactionOne S.hG S.hG' (le_refl (k + 1)) S.a₁ S.ν T.t)) taylorWeight x.1 w.1 σ Θ.1 +
        (S.β : ℂ) * (∑ s : CTorus 3 3 N₁ T.m₁ (k + 1) × Fin 2, Θ.2 s.1 s.2 *
          dirTermSrc (hatFun S.G' S.a₁ S.ν T.t S.hG' ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)
            (onXi S.G' S.a₁ S.ν T.t
              (fun D ψ' => svec (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁))
                (flFieldOne S.G' (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) T.BG₂ T.κ S.a₁ S.ν D ψ')
                  s.1 s.2)))
            (fun _ => (1 : ℂ)) x.2 w.2 σ Θ.1)) ∧
      ∃ εU : ℝ,
      εU = β * prop33EpsEtaScaled 3 3 2 T.m₁ k 1 1 T.BG T.BG₂ T.κ T.t
        (lvR T.κ T.t (β * 3 ^ k) p₁) 0 0 (1 / β) ∧ 0 < εU ∧
      4 * εU ≤ CE * (Real.log (β * 3 ^ k)) ^ (3 * p) / Real.sqrt (β * 3 ^ k) +
        CF * (Real.log (β * 3 ^ k)) ^ p / Real.sqrt (β * 3 ^ k) ∧
      (∀ g : Fld 3 3 N₁ T.m₁ (k + 1) 2, g ∈ l1Ball 3 3 N₁ T.m₁ (k + 1) 2 →
        ∃ BR : StepActivityBound S (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) g,
        ∃ BC : StepActivityBoundC S (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) g,
          BR.m₀ = 1 ∧ BC.m₀ = 1 ∧ BR.Lb = ({Y // Y ∈ 𝒴} ⊕ {Y // Y ∈ 𝒴}) ∧ BC.Lb = BR.Lb ∧
          HEq BR.Lab ((thickLabels 𝒴 hdom).sum (thickLabels 𝒴 hdom)) ∧ HEq BC.Lab BR.Lab ∧
          HEq BR.BS (S.blockSplit 1 hp) ∧ HEq BC.BS BR.BS ∧
          BR.κ0 = T.κ0 ∧ BC.κ0 = T.κ0 ∧ BR.κ' = T.κ' ∧ BC.κ' = T.κ' ∧
          BR.κH = 2 * T.κdec - 1 ∧ BC.κH = BR.κH ∧
          BR.Kc = 2 * (K0 3 3 T.κ0 + 1) ∧ BC.Kc = BR.Kc ∧ BR.εH = BC.εH ∧ BR.εH = 4 * εU) ∧
      (∃ Jr : S.JointRep T.t (2 * p₁),
        ∃ Aseg : ∀ e : physParam 2 S, e ∈ physFibre S S.a₁ S.ν T.t → ℝ × ℝ →
          LabelAct ((thickLabels 𝒴 hdom).sum (thickLabels 𝒴 hdom)) (S.blockSplit 1 hp).Ωb
            (4 * εU) (2 * T.κdec - 1) T.κ0 (2 * (K0 3 3 T.κ0 + 1)),
        (∀ (e : physParam 2 S) (he : e ∈ physFibre S S.a₁ S.ν T.t), ∀ p ∈ stepSegments,
          ∀ᵐ x ∂S.nuFl,
            Jr.W1 (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁))
                ((e.1 : RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2), (p.1 : ℂ) • S.hatC x) +
              Jr.W2 (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) e.2
                ((e.1 : RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2), (p.2 : ℂ) • S.hatC x) =
            ∑ y, (Aseg e he p).H y ((S.blockSplit 1 hp).restr x)) ∧
        (∀ g : Fld 3 3 N₁ T.m₁ (k + 1) 2, ∑ x, ∑ i, ‖g x i‖ < 1 →
          ∃ he : ((⟨rawOf S.D', rawOf_mem_rawSub _⟩ : rawSub 2 S.G'), g) ∈
              physFibre S S.a₁ S.ν T.t,
            ∀ p ∈ stepSegments, ∀ᵐ x ∂S.nuFl,
              S.WoneC (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) p.1 x +
                S.WtwoC (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) g p.2 x =
              ∑ y, (Aseg (⟨rawOf S.D', rawOf_mem_rawSub _⟩, g) he p).H y
                ((S.blockSplit 1 hp).restr x))) ∧
      (0 < εU ∧ ∃ A₀ : ℂ → LabelAct (thickLabels 𝒴 hdom) (S.blockSplit 1 hp).Ωb
          εU (2 * T.κdec - 1) T.κ0 (K0 3 3 T.κ0 + 1),
        (∀ z : ℂ, ‖z‖ < 3 / 2 → ∀ y Φ, (A₀ z).H y Φ =
          Tt y.1 (z • S.hatOf 1 p₁ hp Φ, z • S.hatOf 1 p₁ hp Φ)
            (z • S.hatOf 1 p₁ hp Φ, z • S.hatOf 1 p₁ hp Φ) 1
            (rawOf S.D', (0 : CTorus 3 3 N₁ T.m₁ (k + 1) → Fin 2 → ℂ))) ∧
        (∀ z : ℂ, 3 / 2 ≤ ‖z‖ → ∀ y Φ, (A₀ z).H y Φ = 0) ∧
        ∀ g : Fld 3 3 N₁ T.m₁ (k + 1) 2, g ∈ l1Ball 3 3 N₁ T.m₁ (k + 1) 2 →
        ∃ Ag : ℂ → LabelAct (thickLabels 𝒴 hdom) (S.blockSplit 1 hp).Ωb
            εU (2 * T.κdec - 1) T.κ0 (K0 3 3 T.κ0 + 1),
          (∀ z : ℂ, ‖z‖ < 3 / 2 → ∀ y Φ, (Ag z).H y Φ =
            Tt y.1 (z • S.hatOf 1 p₁ hp Φ, z • S.hatOf 1 p₁ hp Φ)
              (z • S.hatOf 1 p₁ hp Φ, z • S.hatOf 1 p₁ hp Φ) 1
              (rawOf S.D', fun y i => g y i / (S.β : ℂ))) ∧
          (∀ z : ℂ, 3 / 2 ≤ ‖z‖ → ∀ y Φ, (Ag z).H y Φ = 0) ∧
          ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 → ∀ᵐ x ∂S.nuFl,
            ∑ y, (((A₀ 1).sub (A₀ (t : ℂ))).sum (Ag (t : ℂ))).H y
                (((S.blockSplit 1 hp).restr x)) =
              S.WoneC (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) 1 x +
              S.WtwoC (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) g t x) := by
  classical
  have hent := aEnt_nonneg 3 3
  have hc1 := one_le_c1 3 3
  have ht0 := T.t_pos
  have hρ4 := T.rho_nonneg
  have hB0 := T.fam_nonneg
  have hκ0 := T.κ0_nonneg
  obtain ⟨Q, hQdef⟩ : ∃ Q : ℝ, Q = cK2' 3 3 2 (famConst 3 3 T.BG₂ T.κ) := ⟨_, rfl⟩
  have hQ0 : 0 < Q := by rw [hQdef]; exact cK2'_pos' hB0
  obtain ⟨P, hPdef⟩ : ∃ P : ℝ, P = 3 * c1 3 3 * (((3 : ℕ) : ℝ) ^ (1 + T.m₁)) ^ 3 *
    (((3 : ℕ) : ℝ) ^ 3 * ((((2 : ℕ) : ℝ) / 2) * (2 * (1 + Q) ^ 2 +
      (((3 : ℕ) : ℝ) + 1 + rho4 3 3 2 T.BG T.κ) * Q ^ 2) * T.t ^ 2)) := ⟨_, rfl⟩
  have hP0 : 0 ≤ P := by
    rw [hPdef]; positivity
  have hK0 : 0 < Q * T.t := mul_pos hQ0 ht0
  obtain ⟨β₁, hexpβ₁, hA'⟩ := sourceAmp_scale (A₁ := A₁) (κ := T.κ) (t := T.t) hA p ht0
  obtain ⟨Kc'', hKc''⟩ : ∃ x : ℝ, x = K0 3 3 T.κ0 + 1 := ⟨_, rfl⟩
  have hKc''pos : 0 < Kc'' := by have := K0_pos 3 3 T.κ0; rw [hKc'']; linarith
  have hκdec0 : 0 ≤ T.κdec := by have := T.κdec_lower; linarith
  have hκ'0 : 0 ≤ T.κ' := by rw [T.κ'_eq]; linarith
  have hκa' : T.κ' + 3 * T.κ0 + c1 3 3 + 3 / 2 ≤ 2 * T.κdec - 1 := by
    rw [T.κ'_eq, T.κdec_eq]; linarith
  refine ⟨max (max 2 β₁) (daThreshold ((srcCE A₁ T.κ T.t P + srcCF A₁ T.κ T.t (Q * T.t)) / 4)
      (daT 3 3 4 (2 * Kc'') T.κdec T.κ0 T.κ') (3 * p)),
    srcCE A₁ T.κ T.t P, srcCF A₁ T.κ T.t (Q * T.t),
    le_trans (le_max_left _ _) (le_max_left _ _), srcCE_pos hA ht0 hP0,
    srcCF_pos hA ht0 hK0, ?_⟩
  intro k hk N₁ _ h3N hN ν hνpos hν β hβ p₁ hp0 hp₁ D S hS hp
  have hν0 : 0 ≤ ν := hνpos.le
  have hβ₁ : β₁ ≤ β := le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hβ)
  have hβd : daThreshold ((srcCE A₁ T.κ T.t P + srcCF A₁ T.κ T.t (Q * T.t)) / 4)
      (daT 3 3 4 (2 * Kc'') T.κdec T.κ0 T.κ') (3 * p) ≤ β := le_trans (le_max_right _ _) hβ
  have hβ2 : 2 ≤ β := le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hβ)
  have hβ0 : 0 < β := by linarith
  have hβ1 : 1 ≤ β := by linarith
  have h3k : (1 : ℝ) ≤ 3 ^ k := one_le_pow₀ (by norm_num)
  have hbβ : β ≤ β * 3 ^ k := le_mul_of_one_le_right hβ0.le h3k
  have hb0 : 0 < β * 3 ^ k := by positivity
  have hexp : Real.exp 1 ≤ β * 3 ^ k := le_trans hexpβ₁ (hβ₁.trans hbβ)
  have hℓ : 1 ≤ Real.log (β * 3 ^ k) := (Real.le_log_iff_exp_le hb0).2 hexp
  have hamp := (hA' (β * 3 ^ k) (hβ₁.trans hbβ) p₁ hp0 hp₁).2 P (Q * T.t) 1 hP0 hK0.le one_pos.le
  obtain ⟨R0⟩ := D.ray
  have hr0 := D.r_pos
  have hcψ0 := D.cψ_pos
  have hHB := bgHyp_lv (k := k) T.m₁ hν0 hν
  have hC := D.core
  have hD := D.xi
  -- the physical amplitude on the slice `η = 1/β`
  set εU : ℝ := β * prop33EpsEtaScaled 3 3 2 T.m₁ k 1 1 T.BG T.BG₂ T.κ T.t
      (lvR T.κ T.t (β * 3 ^ k) p₁) 0 0 (1 / β) with hεU
  have hid := sourceEta_scaled_identity 3 3 2 T.m₁ k 1 1 T.BG T.BG₂ T.κ T.t
    (lvR T.κ T.t (β * 3 ^ k) p₁) 1 β hβ0.ne'
  rw [← hεU, ← hQdef] at hid
  have hpot : β * (3 * c1 3 3 * (((3 : ℕ) : ℝ) ^ (1 + T.m₁)) ^ 3 *
      ‖energyBdScaled 3 3 2 (compWeight 3 1) k (Q * T.t) T.t (rho4 3 3 2 T.BG T.κ)‖ /
        lvR T.κ T.t (β * 3 ^ k) p₁ ^ 3) ≤ β * 3 ^ k * (P / lvR T.κ T.t (β * 3 ^ k) p₁ ^ 3) := by
    have h := beta_mul_potentialAmp_le (N := 2) (T.step k hk N₁ ν β p₁)
      (by norm_num) le_rfl (compWeight_three_mem hk).2
      (le_trans (by norm_num) (compWeight_three_mem hk).1) hβ0.le hQ0.le ht0.le hρ4 hr0 (1 + T.m₁)
    rw [hatStepK_betaU, ← hPdef] at h
    exact h
  have hterm0 : 0 ≤ β * (3 * c1 3 3 * (((3 : ℕ) : ℝ) ^ (1 + T.m₁)) ^ 3 *
      ‖energyBdScaled 3 3 2 (compWeight 3 1) k (Q * T.t) T.t (rho4 3 3 2 T.BG T.κ)‖ /
        lvR T.κ T.t (β * 3 ^ k) p₁ ^ 3) := by
    have h3 : (0 : ℝ) ≤ 3 * c1 3 3 := by linarith
    positivity
  have hεle : εU ≤ P * (4 * A₁ / lvKappa T.κ T.t) ^ 3 * (Real.log (β * 3 ^ k)) ^ (3 * p) /
        Real.sqrt (β * 3 ^ k) +
      1 * (4 * A₁ * (Q * T.t) / lvKappa T.κ T.t) * (Real.log (β * 3 ^ k)) ^ p /
        Real.sqrt (β * 3 ^ k) := by
    rw [hid]
    linarith
  have hεpos : 0 < εU := by
    rw [hid]
    have : 0 < 1 * (Q * T.t) / lvR T.κ T.t (β * 3 ^ k) p₁ := div_pos (by linarith) hr0
    linarith
  have hε4 := sourceAmp_scale_four (A₁ := A₁) (κ := T.κ) (t := T.t) (P := P) (K := Q * T.t)
    (q := 1) p hb0 (by linarith) hεle
  have hDA0 := sourceAmp_doubled_hDA 3 3 (A₁ := A₁) (κ := T.κ) (t := T.t) (P := P)
    (K := Q * T.t) (q := 1) (b := β * 3 ^ k) (ε := εU) (Kc' := Kc'') p hA ht0 hP0 hK0.le le_rfl
    hℓ hb0 hKc''pos T.κdec T.κ0 T.κ' (hβd.trans hbβ) hεle
  have hN3 : 3 ^ 1 ∣ N₁ := by simpa using h3N
  subst hS
  set S := T.step k hk N₁ ν β p₁ with hSdef
  -- the direct terms, selected once for the slice `η = 1/β`
  obtain ⟨val, 𝒴, Tt, hval, -, hcont, hI, hmem0, hmemg⟩ := sourceDirectTerms_scale_fromTower T k hk N₁
    h3N hN ν hνpos hν β hβ1 p₁ 1 one_pos le_rfl D (T.step k hk N₁ ν β p₁) rfl hp
  obtain ⟨I₀, h𝒴₀, hT₀⟩ := hI _ hmem0
  have hdom : ∀ Y ∈ 𝒴, IsDj 1 (k + 1) Y := fun Y hY => I₀.dom Y (h𝒴₀ ▸ hY)
  have hbound : 4 * εU ≤ srcCE A₁ T.κ T.t P * (Real.log (β * 3 ^ k)) ^ (3 * p) / Real.sqrt (β * 3 ^ k) +
      srcCF A₁ T.κ T.t (Q * T.t) * (Real.log (β * 3 ^ k)) ^ p / Real.sqrt (β * 3 ^ k) := by
    have := hε4
    rw [one_mul] at this
    exact this
  refine ⟨val, 𝒴, Tt, hdom, hval, εU, hεU, hεpos, hbound, ?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨Ig, h𝒴g, hTg⟩ := hI _ (hmemg g hg)
    obtain ⟨BR, hm, hLb, hLab, hBS, hk0, hk', hκH, hεH, hKc⟩ :=
      stepActivityBound_zeroClass_source_of_directTerms_shared (T.step k hk N₁ ν β p₁)
        (ρ := p₁) (κ0 := T.κ0) (κ' := T.κ') (Kc' := Kc'') (a := 2 * T.κdec - 1)
        hC (by norm_num) hr0 hcψ0.le T.large_block T.dom_margin T.coer_margin T.δc_small
        D.fl_radius T.c7_cap (R := 2) le_rfl T.t_cap T.bg0_cap T.cK2_cap T.cK2'_cap T.bg1_cap
        (by norm_num) D.ray_margin hD hN3 hp0 le_rfl (by rw [hεU] at hεpos; exact hεpos) T.κ0_ent hKc''.ge hκ'0 hκa'
        (by rw [hεU] at hDA0; exact hDA0) R0
        D.p_lt (by norm_num) g I₀ Ig
        (fun x u => by rw [hval]; simp)
        (fun x u => hval _ _ _ _) hdom h𝒴₀ h𝒴g
    obtain ⟨BC, hCm, hCLb, hCLab, hCBS, hCk0, hCk', hCκH, hCεH, hCKc⟩ :=
      stepActivityBoundC_of_activityBound_exposed R0 hp0 D.p_lt BR
    have hBε : BR.εH = 4 * εU := by
      rw [hεH, (fun E : ℝ => by ring : ∀ E : ℝ, 2 * (2 * E) = 4 * E)]
      exact congrArg _ hεU.symm
    exact ⟨BR, BC, hm, hCm.trans hm, hLb, hCLb, hLab, hCLab, hBS, hCBS, hk0, hCk0.trans hk0, hk',
      hCk'.trans hk', hκH, hCκH, by rw [hKc, hKc''], hCKc, hCεH.symm, hBε⟩
  · obtain ⟨Jr, hJ1, hJ2⟩ := wone_chartIdentity_fromTower T k hk N₁ ν hνpos hν β p₁ hp0 D S rfl
    have hεU0 : 0 ≤ εU := hεpos.le
    have hK0 : K0 3 3 T.κ0 ≤ K0 3 3 T.κ0 + 1 := by linarith
    have hRσ1 : (1 : ℝ) < 2 := by norm_num
    have hcfun : ∀ s : ℝ, ‖((if s ∈ Icc (0 : ℝ) 1 then s ^ 2 else 0 : ℝ) : ℂ)‖ ≤ 1 :=
      norm_ite_sq_le
    have hβS : 1 ≤ S.β := hβ1
    have hβS0 : 0 < S.β := hβ0
    have hex : ∀ e : physParam 2 S, e ∈ physFibre S S.a₁ S.ν T.t →
        ∃ Ae : ℝ × ℝ → LabelAct ((thickLabels 𝒴 hdom).sum (thickLabels 𝒴 hdom))
            (S.blockSplit 1 hp).Ωb (4 * εU) (2 * T.κdec - 1) T.κ0 (2 * (K0 3 3 T.κ0 + 1)),
          ∀ p ∈ stepSegments, ∀ᵐ x ∂S.nuFl,
            Jr.W1 (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁))
                ((e.1 : RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2), (p.1 : ℂ) • S.hatC x) +
              Jr.W2 (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) e.2
                ((e.1 : RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2), (p.2 : ℂ) • S.hatC x) =
            ∑ y, (Ae p).H y ((S.blockSplit 1 hp).restr x) := by
      intro e he
      have he1 : e ∈ physVq S S.a₁ S.ν T.t 1 := ⟨he.1, he.1.2⟩
      have hmemE := physInclScaled_image_subset S S.a₁ S.ν T.t hβS le_rfl ⟨e, he1, rfl⟩
      have hmem0E : physInclScaled 2 S ((1 / S.β : ℝ) : ℂ) (e.1, 0) ∈
          physSΛEta S S.a₁ S.ν T.t (1 / S.β) := by
        refine ⟨he.1.1, ?_⟩
        show (fun y i => ((1 / S.β : ℝ) : ℂ) * (0 : ℂ)) ∈ _
        simp only [mul_zero]
        refine ⟨by simp [l1Ball], ?_⟩
        simp only [norm_zero, Finset.sum_const_zero]
        exact (one_div_pos.2 hβS0).le
      obtain ⟨Ie, h𝒴e, -⟩ := hI _ hmemE
      obtain ⟨I0, h𝒴0, -⟩ := hI _ hmem0E
      have hεI : 0 ≤ S.β * prop33EpsEtaScaled 3 3 2 T.m₁ k 1 S.a₁ T.BG T.BG₂ T.κ T.t
          (lvR T.κ T.t (β * 3 ^ k) p₁) 0 0 (1 / S.β) := hεU0
      obtain ⟨A0, hid0⟩ := labelAct_of_directTerms_shared S 1 I0 hN3 hp0
        (by norm_num : (0 : ℝ) ≤ 2) hεI T.κ0_ent hK0 hdom h𝒴0 (ε' := 2 * εU) rfl
      obtain ⟨Ag, hidg⟩ := labelAct_of_directTerms_shared S 1 Ie hN3 hp0
        (by norm_num : (0 : ℝ) ≤ 2) hεI T.κ0_ent hK0 hdom h𝒴e (ε' := 2 * εU) rfl
      have hε2 : 0 ≤ 2 * εU := by linarith
      have hE : 2 * εU + 2 * εU ≤ 2 * (2 * εU) := by linarith
      let c : ℝ → ℂ := fun s => ((if s ∈ Icc (0 : ℝ) 1 then s ^ 2 else 0 : ℝ) : ℂ)
      -- the value of the two segment sum in terms of `val`
      have hid_val : ∀ x : S.E, ‖x‖ < 2 * p₁ → ∀ s τ : ℝ, s ∈ Icc (0 : ℝ) 1 → τ ∈ Icc (0 : ℝ) 1 →
          Jr.W1 (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁))
              ((e.1 : RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2), (s : ℂ) • S.hatC x) +
            Jr.W2 (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) e.2
              ((e.1 : RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2), (τ : ℂ) • S.hatC x) =
          (s : ℂ) ^ 2 * val (S.hatC x, S.hatC x) (S.hatC x, S.hatC x) (s : ℂ)
              (physInclScaled 2 S ((1 / S.β : ℝ) : ℂ) (e.1, 0)) +
            (val (S.hatC x, S.hatC x) (S.hatC x, S.hatC x) (τ : ℂ)
                (physInclScaled 2 S ((1 / S.β : ℝ) : ℂ) e) -
              val (S.hatC x, S.hatC x) (S.hatC x, S.hatC x) (τ : ℂ)
                (physInclScaled 2 S ((1 / S.β : ℝ) : ℂ) (e.1, 0))) := by
        intro x hxn s τ hs hτ
        have := @hJ2 0 0 0 Empty Empty _ _ (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0)
          (fun e => e.elim) (fun e => e.elim) (fun _ => ∅) (fun _ => ∅) (fun _ => 0)
          (fun e => e.elim) (fun e => e.elim) (fun _ => ∅) (fun _ => ∅) (fun _ => 0)
          (fun _ => 0) (fun _ => 0) ∅ ∅ (fun τ h => absurd h (by simp))
          (fun τ h => absurd h (by simp)) (fun e => e.elim) (fun e => e.elim)
          (fun τ h => absurd h (by simp)) (fun τ h => absurd h (by simp)) 0 rfl rfl rfl
          e he.1 he.2 x hxn s τ hs hτ
        simp only [physVal_zeroClass_eq] at this
        simp only [hval]
        exact this
      refine ⟨fun p => (segAct A0 Ag hε2 hE c hcfun p).mono
        (by rw [max_self]; linarith) (by rw [max_self]; linarith) le_rfl le_rfl
        (by linarith), ?_⟩
      intro p hp'
      obtain ⟨hs1, ht1⟩ := mem_Icc_of_mem_stepSegments hp'
      filter_upwards [S.ae_hatOf_restr 1 hp0 hp le_rfl, S.ae_ball hp] with x hx hχ
      have hxn : ‖x‖ < S.p₁ := (chiFl_eq_one_iff hp x).1 hχ
      have hxn2 : ‖x‖ < 2 * p₁ := by
        have : S.p₁ = p₁ := rfl
        linarith
      have key0 : ∀ u : ℝ, u ∈ Icc (0 : ℝ) 1 →
          ∑ y, (A0 (u : ℂ)).H y ((S.blockSplit 1 hp).restr x) =
            val (S.hatC x, S.hatC x) (S.hatC x, S.hatC x) (u : ℂ)
              (physInclScaled 2 S ((1 / S.β : ℝ) : ℂ) (e.1, 0)) := by
        intro u hu
        rw [hid0 (u : ℂ) (norm_ofReal_lt_of_mem hu hRσ1)]
        simp only [hx]
      have keyg : ∀ u : ℝ, u ∈ Icc (0 : ℝ) 1 →
          ∑ y, (Ag (u : ℂ)).H y ((S.blockSplit 1 hp).restr x) =
            val (S.hatC x, S.hatC x) (S.hatC x, S.hatC x) (u : ℂ)
              (physInclScaled 2 S ((1 / S.β : ℝ) : ℂ) e) := by
        intro u hu
        rw [hidg (u : ℂ) (norm_ofReal_lt_of_mem hu hRσ1)]
        simp only [hx]
      obtain ⟨s, t⟩ := p
      have hmono : ∀ y, ((segAct A0 Ag hε2 hE c hcfun (s, t)).mono
          (by rw [max_self]; linarith) (by rw [max_self]; linarith) le_rfl le_rfl
          (by linarith : (K0 3 3 T.κ0 + 1) + (K0 3 3 T.κ0 + 1) ≤
            2 * (K0 3 3 T.κ0 + 1)) : LabelAct _ _ (4 * εU) _ _ _).H y =
          (segAct A0 Ag hε2 hE c hcfun (s, t)).H y := fun y => rfl
      simp only [hmono]
      by_cases h0 : t = 0
      · rw [segAct_total_zero _ _ _ _ _ _ (p := (s, t)) h0, hid_val x hxn2 s t hs1 ht1, key0 s hs1]
        subst h0
        have hz : val (S.hatC x, S.hatC x) (S.hatC x, S.hatC x) ((0 : ℝ) : ℂ)
            (physInclScaled 2 S ((1 / S.β : ℝ) : ℂ) e) =
            val (S.hatC x, S.hatC x) (S.hatC x, S.hatC x) ((0 : ℝ) : ℂ)
            (physInclScaled 2 S ((1 / S.β : ℝ) : ℂ) (e.1, 0)) := by
          rw [hval, hval]
          simp [physInclScaled_apply, dirTermSrc]
        rw [hz, sub_self, add_zero]
        simp only [c, hs1, ite_true]
        push_cast
        rfl
      · have h1 : s = 1 := by
          rcases hp' with ⟨-, h2⟩ | ⟨h1, -⟩
          · exact absurd h2 h0
          · exact h1
        subst h1
        rw [segAct_total_ne _ _ _ _ _ _ (p := (1, t)) h0, hid_val x hxn2 1 t hs1 ht1, key0 t ht1, keyg t ht1]
        have := key0 1 hs1
        rw [Complex.ofReal_one] at this ⊢
        rw [this]
        simp only [one_pow, one_mul]
        ring
    choose Aseg hAseg using hex
    refine ⟨Jr, Aseg, fun e he p hp' => hAseg e he p hp', ?_⟩
    intro g hg
    have hmemS : ((⟨rawOf S.D', rawOf_mem_rawSub _⟩ : rawSub 2 S.G'), g) ∈
        physFibre S S.a₁ S.ν T.t := ⟨⟨⟨S.D', D.xi, rfl⟩, hg⟩, fun y i => S.hh₀ y i⟩
    refine ⟨hmemS, fun p hp' => ?_⟩
    obtain ⟨hs1, ht1⟩ := mem_Icc_of_mem_stepSegments hp'
    have hle : S.p₁ ≤ 2 * p₁ := by
      show p₁ ≤ 2 * p₁
      linarith
    filter_upwards [hAseg _ hmemS p hp',
      Jr.ae_W1_path (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) hp hle S.D' S.hh₀ D.xi hs1,
      Jr.ae_W2_path (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) hp hle S.D' S.hh₀ D.xi g ht1]
      with x h1 h2 h3
    have e1 : S.WoneC (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) p.1 x = _ := h2.symm
    have e2 : S.WtwoC (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) g p.2 x = _ := h3.symm
    rw [e1, e2]
    exact h1

  · refine ⟨hεpos, ?_⟩
    have hKc : K0 3 3 T.κ0 ≤ K0 3 3 T.κ0 + 1 := by linarith
    have hxwz : ∀ z : ℂ, ‖z‖ < 3 / 2 → ∀ ψ ∈ hatDisk (T.step k hk N₁ ν β p₁).U 2 p₁,
        ((z • ψ, z • ψ), (z • ψ, z • ψ)) ∈
          physXW (T.step k hk N₁ ν β p₁) (lvCpsi T.κ T.t (β * 3 ^ k)) 2 2
            (lvR T.κ T.t (β * 3 ^ k) p₁) :=
      fun z hz ψ hψ => scaled_pair_mem_physXW (T.step k hk N₁ ν β p₁) hψ hz (by norm_num)
        (by norm_num) hr0.le (D.ray_margin_scaled hp)
    have hAgF : ∀ (z : ℂ) (Y : Set (CTorus 3 3 N₁ T.m₁ (k + 1)))
        (ψ ψ' : (T.step k hk N₁ ν β p₁).U × Fin 2 → ℂ),
        AgFDirPair (T.step k hk N₁ ν β p₁) Y (ψ, ψ) (ψ', ψ') →
        AgFDirPair (T.step k hk N₁ ν β p₁) Y (z • ψ, z • ψ) (z • ψ', z • ψ') :=
      fun z Y ψ ψ' h => agFDirPair_smul _ z Y ψ ψ' h
    have hcont₀ := hcont
    rw [← h𝒴₀, ← hT₀] at hcont₀
    have hRσ1 : (1 : ℝ) < 2 := by norm_num
    have hpc : p₁ < lvCpsi T.κ T.t (β * 3 ^ k) :=
      p₁_lt_of_margin hp le_rfl hRσ1 hRσ1 hr0 D.ray_margin
    refine ⟨obsRayAct (T.step k hk N₁ ν β p₁) 1 I₀ hdom h𝒴₀ hxwz hAgF hcont₀ hN3 hp hRσ1 hεpos.le
        T.κ0_ent hKc, ?_, ?_, ?_⟩
    · intro z hz y Φ
      rw [obsRayAct_H_of_lt _ _ _ hdom h𝒴₀ hxwz hAgF hcont₀ hN3 hp hRσ1 hεpos.le T.κ0_ent hKc hz,
        hT₀]
    · intro z hz y Φ
      exact obsRayAct_H_of_not_lt _ _ _ hdom h𝒴₀ hxwz hAgF hcont₀ hN3 hp hRσ1 hεpos.le T.κ0_ent
        hKc hz y Φ
    · intro g hg
      obtain ⟨Ig, h𝒴g, hTg⟩ := hI _ (hmemg g hg)
      have hcontg := hcont
      rw [← h𝒴g, ← hTg] at hcontg
      refine ⟨obsRayAct (T.step k hk N₁ ν β p₁) 1 Ig hdom h𝒴g hxwz hAgF hcontg hN3 hp hRσ1
        hεpos.le T.κ0_ent hKc, ?_, ?_, ?_⟩
      · intro z hz y Φ
        rw [obsRayAct_H_of_lt _ _ _ hdom h𝒴g hxwz hAgF hcontg hN3 hp hRσ1 hεpos.le T.κ0_ent hKc hz,
          hTg]
      · intro z hz y Φ
        exact obsRayAct_H_of_not_lt _ _ _ hdom h𝒴g hxwz hAgF hcontg hN3 hp hRσ1 hεpos.le T.κ0_ent
          hKc hz y Φ
      · intro t ht
        exact ae_sum_A_phys_eq_WoneC_add_WtwoC (T.step k hk N₁ ν β p₁) hC R0 D.p_lt hD T.c7_cap
          (R := 2) le_rfl T.bg1_cap T.t_cap T.bg0_cap T.cK2_cap T.cK2'_cap T.large_block T.dom_margin
          T.coer_margin T.δc_small hp hcψ0.le hpc D.fl_radius g le_rfl I₀ Ig hval hdom h𝒴₀ h𝒴g
          hxwz hAgF hcont₀ hcontg hN3 hp hRσ1 hεpos.le T.κ0_ent hKc ht


open Classical in
/-- **Drift check (activity).**  `sourceActivityC_scale_fromTower` follows from
`sourceWitness_fromTower`: the bound on `BR.εH` is `BR.εH = 4 ε_U ≤ …`. -/
theorem sourceActivityC_scale_fromTower_of_witness {κmin : ℝ} (T : StepTower κmin) {A₁ : ℝ}
    (hA : 0 < A₁) (p : ℕ) :
    ∃ β₀ CE CF : ℝ, 2 ≤ β₀ ∧ 0 < CE ∧ 0 < CF ∧
    ∀ (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁], 3 ∣ N₁ → 5 < N₁ →
    ∀ ν : ℝ, 0 < ν → ν * 3 ^ (2 * (k + 1)) ≤ 1 →
    ∀ β : ℝ, β₀ ≤ β → ∀ (p₁ : ℝ) (hp : 0 < p₁),
    p₁ ≤ pLog A₁ p (β * 3 ^ k) → StepScaleData T k hk N₁ ν β p₁ →
    ∃ 𝒴 : Finset (Set (CTorus 3 3 N₁ T.m₁ (k + 1))),
    ∃ hdom : ∀ Y ∈ 𝒴, IsDj 1 (k + 1) Y,
    ∀ g : Fld 3 3 N₁ T.m₁ (k + 1) 2, g ∈ l1Ball 3 3 N₁ T.m₁ (k + 1) 2 →
    ∃ BR : StepActivityBound (T.step k hk N₁ ν β p₁)
        (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) g,
    ∃ BC : StepActivityBoundC (T.step k hk N₁ ν β p₁)
        (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) g,
      BR.m₀ = 1 ∧ BC.m₀ = 1 ∧ BR.Lb = ({Y // Y ∈ 𝒴} ⊕ {Y // Y ∈ 𝒴}) ∧ BC.Lb = BR.Lb ∧
      HEq BR.Lab ((thickLabels 𝒴 hdom).sum (thickLabels 𝒴 hdom)) ∧ HEq BC.Lab BR.Lab ∧
      HEq BR.BS ((T.step k hk N₁ ν β p₁).blockSplit 1 hp) ∧ HEq BC.BS BR.BS ∧
      BR.κ0 = T.κ0 ∧ BC.κ0 = T.κ0 ∧ BR.κ' = T.κ' ∧ BC.κ' = T.κ' ∧
      BR.κH = 2 * T.κdec - 1 ∧ BC.κH = BR.κH ∧
      BR.Kc = 2 * (K0 3 3 T.κ0 + 1) ∧ BC.Kc = BR.Kc ∧ BR.εH = BC.εH ∧
      BR.εH ≤ CE * (Real.log (β * 3 ^ k)) ^ (3 * p) / Real.sqrt (β * 3 ^ k) +
        CF * (Real.log (β * 3 ^ k)) ^ p / Real.sqrt (β * 3 ^ k) := by
  obtain ⟨β₀, CE, CF, h2, hCE, hCF, H⟩ := sourceWitness_fromTower T hA p
  refine ⟨β₀, CE, CF, h2, hCE, hCF, ?_⟩
  intro k hk N₁ _ h3N hN ν hνpos hν β hβ p₁ hp hp₁ D
  obtain ⟨val, 𝒴, Tt, hdom, -, εU, -, -, hb, ha, -, -⟩ :=
    H k hk N₁ h3N hN ν hνpos hν β hβ p₁ hp hp₁ D _ rfl hp
  refine ⟨𝒴, hdom, fun g hg => ?_⟩
  obtain ⟨BR, BC, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, hε⟩ :=
    ha g hg
  exact ⟨BR, BC, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17,
    by rw [hε]; exact hb⟩

open Classical in
/-- **Drift check (observable rays).**  `obsRayActivity_fromTower` follows from
`sourceWitness_fromTower` for `β ≥ β₀` and `p₁ ≤ A₁ (log β_k)^p` (the landed statement has only
`1 ≤ β`; the witness theorem has the threshold of the amplitude bound). -/
theorem obsRayActivity_fromTower_of_witness {κmin : ℝ} (T : StepTower κmin) {A₁ : ℝ}
    (hA : 0 < A₁) (p : ℕ) :
    ∃ β₀ : ℝ, ∀ (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁], 3 ∣ N₁ → 5 < N₁ →
    ∀ ν : ℝ, 0 < ν → ν * 3 ^ (2 * (k + 1)) ≤ 1 →
    ∀ β : ℝ, β₀ ≤ β → ∀ (p₁ : ℝ), 0 < p₁ → p₁ ≤ pLog A₁ p (β * 3 ^ k) →
    StepScaleData T k hk N₁ ν β p₁ → ∀ (hp : 0 < p₁),
    ∃ (val : (((T.step k hk N₁ ν β p₁).U × Fin 2 → ℂ) × ((T.step k hk N₁ ν β p₁).U × Fin 2 → ℂ)) →
        (((T.step k hk N₁ ν β p₁).U × Fin 2 → ℂ) × ((T.step k hk N₁ ν β p₁).U × Fin 2 → ℂ)) →
        ℂ → (RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2 ×
          (CTorus 3 3 N₁ T.m₁ (k + 1) → Fin 2 → ℂ)) → ℂ)
      (𝒴 : Finset (Set (CTorus 3 3 N₁ T.m₁ (k + 1))))
      (Tt : Set (CTorus 3 3 N₁ T.m₁ (k + 1)) →
        (((T.step k hk N₁ ν β p₁).U × Fin 2 → ℂ) × ((T.step k hk N₁ ν β p₁).U × Fin 2 → ℂ)) →
        (((T.step k hk N₁ ν β p₁).U × Fin 2 → ℂ) × ((T.step k hk N₁ ν β p₁).U × Fin 2 → ℂ)) →
        ℂ → (RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2 ×
          (CTorus 3 3 N₁ T.m₁ (k + 1) → Fin 2 → ℂ)) → ℂ)
      (hdom : ∀ Y ∈ 𝒴, IsDj 1 (k + 1) Y),
      (∀ x w σ Θ, val x w σ Θ =
        (-((T.step k hk N₁ ν β p₁).β : ℂ)) * raySrc3 (hatFun (T.step k hk N₁ ν β p₁).G' (T.step k hk N₁ ν β p₁).a₁ (T.step k hk N₁ ν β p₁).ν T.t (T.step k hk N₁ ν β p₁).hG'
          (((T.step k hk N₁ ν β p₁).betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)
          (interactionOne (T.step k hk N₁ ν β p₁).hG (T.step k hk N₁ ν β p₁).hG' (le_refl (k + 1)) (T.step k hk N₁ ν β p₁).a₁ (T.step k hk N₁ ν β p₁).ν T.t)) taylorWeight
          x.1 w.1 σ Θ.1 +
        ((T.step k hk N₁ ν β p₁).β : ℂ) * (∑ s : CTorus 3 3 N₁ T.m₁ (k + 1) × Fin 2, Θ.2 s.1 s.2 *
          dirTermSrc (hatFun (T.step k hk N₁ ν β p₁).G' (T.step k hk N₁ ν β p₁).a₁ (T.step k hk N₁ ν β p₁).ν T.t (T.step k hk N₁ ν β p₁).hG'
            (((T.step k hk N₁ ν β p₁).betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)
            (onXi (T.step k hk N₁ ν β p₁).G' (T.step k hk N₁ ν β p₁).a₁ (T.step k hk N₁ ν β p₁).ν T.t
              (fun D ψ' => svec (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁))
                (flFieldOne (T.step k hk N₁ ν β p₁).G' (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) T.BG₂ T.κ (T.step k hk N₁ ν β p₁).a₁ (T.step k hk N₁ ν β p₁).ν D ψ')
                  s.1 s.2)))
            (fun _ => (1 : ℂ)) x.2 w.2 σ Θ.1)) ∧
      0 < β * prop33EpsEtaScaled 3 3 2 T.m₁ k 1 1 T.BG T.BG₂ T.κ T.t
        (lvR T.κ T.t (β * 3 ^ k) p₁) 0 0 (1 / β) ∧
      ∃ A₀ : ℂ → LabelAct (thickLabels 𝒴 hdom) ((T.step k hk N₁ ν β p₁).blockSplit 1 hp).Ωb
          (β * prop33EpsEtaScaled 3 3 2 T.m₁ k 1 1 T.BG T.BG₂ T.κ T.t
            (lvR T.κ T.t (β * 3 ^ k) p₁) 0 0 (1 / β)) (2 * T.κdec - 1) T.κ0 (K0 3 3 T.κ0 + 1),
        (∀ z : ℂ, ‖z‖ < 3 / 2 → ∀ y Φ, (A₀ z).H y Φ =
          Tt y.1 (z • (T.step k hk N₁ ν β p₁).hatOf 1 p₁ hp Φ, z • (T.step k hk N₁ ν β p₁).hatOf 1 p₁ hp Φ)
            (z • (T.step k hk N₁ ν β p₁).hatOf 1 p₁ hp Φ, z • (T.step k hk N₁ ν β p₁).hatOf 1 p₁ hp Φ) 1
            (rawOf (T.step k hk N₁ ν β p₁).D', (0 : CTorus 3 3 N₁ T.m₁ (k + 1) → Fin 2 → ℂ))) ∧
        (∀ z : ℂ, 3 / 2 ≤ ‖z‖ → ∀ y Φ, (A₀ z).H y Φ = 0) ∧
        ∀ g : Fld 3 3 N₁ T.m₁ (k + 1) 2, g ∈ l1Ball 3 3 N₁ T.m₁ (k + 1) 2 →
        ∃ Ag : ℂ → LabelAct (thickLabels 𝒴 hdom) ((T.step k hk N₁ ν β p₁).blockSplit 1 hp).Ωb
            (β * prop33EpsEtaScaled 3 3 2 T.m₁ k 1 1 T.BG T.BG₂ T.κ T.t
              (lvR T.κ T.t (β * 3 ^ k) p₁) 0 0 (1 / β)) (2 * T.κdec - 1) T.κ0
            (K0 3 3 T.κ0 + 1),
          (∀ z : ℂ, ‖z‖ < 3 / 2 → ∀ y Φ, (Ag z).H y Φ =
            Tt y.1 (z • (T.step k hk N₁ ν β p₁).hatOf 1 p₁ hp Φ, z • (T.step k hk N₁ ν β p₁).hatOf 1 p₁ hp Φ)
              (z • (T.step k hk N₁ ν β p₁).hatOf 1 p₁ hp Φ, z • (T.step k hk N₁ ν β p₁).hatOf 1 p₁ hp Φ) 1
              (rawOf (T.step k hk N₁ ν β p₁).D', fun y i => g y i / ((T.step k hk N₁ ν β p₁).β : ℂ))) ∧
          (∀ z : ℂ, 3 / 2 ≤ ‖z‖ → ∀ y Φ, (Ag z).H y Φ = 0) ∧
          ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 → ∀ᵐ x ∂(T.step k hk N₁ ν β p₁).nuFl,
            ∑ y, (((A₀ 1).sub (A₀ (t : ℂ))).sum (Ag (t : ℂ))).H y
                (((T.step k hk N₁ ν β p₁).blockSplit 1 hp).restr x) =
              (T.step k hk N₁ ν β p₁).WoneC (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) 1 x +
              (T.step k hk N₁ ν β p₁).WtwoC (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) g t x := by
  obtain ⟨β₀, _CE, _CF, _h2, _hCE, _hCF, H⟩ := sourceWitness_fromTower T hA p
  refine ⟨β₀, ?_⟩
  intro k hk N₁ _ h3N hN ν hνpos hν β hβ p₁ hp0 hp₁ D hp
  obtain ⟨val, 𝒴, Tt, hdom, hval, εU, hεU, hεpos, -, -, -, hc⟩ :=
    H k hk N₁ h3N hN ν hνpos hν β hβ p₁ hp0 hp₁ D _ rfl hp
  subst hεU
  exact ⟨val, 𝒴, Tt, hdom, hval, hc.1, hc.2⟩

end Balaban.Inhabited
