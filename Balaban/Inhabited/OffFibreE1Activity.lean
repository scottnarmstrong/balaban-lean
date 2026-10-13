/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.OffFibreE1CoeffSum
public import Balaban.Inhabited.SourceExponentFamily

/-!
# The common E1 activity at a free datum

The common-label activity used for the first-energy marks has the raw first exponent as its
sum at every chart datum. The direct-term value and the free-datum interaction identity
identify both sides with the same cubic ray remainder.
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Fluctuation Balaban.Multiscale Balaban.Background Balaban.Localization
  Balaban.Localization.I5Inhabited
  Balaban.Polymer Balaban.SmallField Balaban.SmallField.Def6 Balaban.Inhabited.LevelStep
  MeasureTheory Set Metric

open Classical in
/-- The common first-energy activity has the raw interaction value at a free chart datum. -/
theorem e1_common_activity_freeDatum_of_directTerms {κmin : ℝ} (T : StepTower κmin)
    (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁] (h3N : 3 ∣ N₁)
    (ν : ℝ) (hνpos : 0 < ν) (hν : ν * 3 ^ (2 * (k + 1)) ≤ 1)
    (β p₁ : ℝ) (hp0 : 0 < p₁) (Dt : StepScaleData T k hk N₁ ν β p₁)
    (S : StepSetting 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁))
    (hS : S = T.step k hk N₁ ν β p₁) (hp : 0 < S.p₁)
    (Jr : S.JointRep T.t (2 * p₁))
    (val : ((S.U × Fin 2 → ℂ) × (S.U × Fin 2 → ℂ)) →
      ((S.U × Fin 2 → ℂ) × (S.U × Fin 2 → ℂ)) → ℂ →
      (RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2 ×
        (CTorus 3 3 N₁ T.m₁ (k + 1) → Fin 2 → ℂ)) → ℂ)
    (hval : ∀ x w σ Θ, val x w σ Θ =
      (-(S.β : ℂ)) * raySrc3 (hatFun S.G' S.a₁ S.ν T.t S.hG'
        ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)
        (interactionOne S.hG S.hG' (le_refl (k + 1)) S.a₁ S.ν T.t))
        taylorWeight x.1 w.1 σ Θ.1 +
      (S.β : ℂ) * (∑ s : CTorus 3 3 N₁ T.m₁ (k + 1) × Fin 2, Θ.2 s.1 s.2 *
        dirTermSrc (hatFun S.G' S.a₁ S.ν T.t S.hG'
          ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)
          (onXi S.G' S.a₁ S.ν T.t
            (fun D ψ' => svec (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁))
              (flFieldOne S.G' (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁))
                T.BG₂ T.κ S.a₁ S.ν D ψ') s.1 s.2)))
          (fun _ => (1 : ℂ)) x.2 w.2 σ Θ.1))
    (I : DirectTerms S 1 hp (fun ψ => (ψ, ψ)) p₁ 2
      (S.β * prop33EpsEtaScaled 3 3 2 T.m₁ k 1 S.a₁ T.BG T.BG₂ T.κ T.t
        (lvR T.κ T.t (β * 3 ^ k) p₁) 0 0 (1 / S.β)) (2 * T.κdec - 1)
      (rawOf S.D', (0 : CTorus 3 3 N₁ T.m₁ (k + 1) → Fin 2 → ℂ))
      (physSΛEta S S.a₁ S.ν T.t (1 / S.β))
      (physXW S (lvCpsi T.κ T.t (β * 3 ^ k)) 2 2
        (lvR T.κ T.t (β * 3 ^ k) p₁)) val (physAgΘ S) (AgFDirPair S))
    (hF : DirectTermsFamilyOn S 1 (physInclScaled 2 S (((1 / S.β : ℝ)) : ℂ)) I
      (physVq S S.a₁ S.ν T.t 1))
    (hεU : 0 ≤ S.β * prop33EpsEtaScaled 3 3 2 T.m₁ k 1 S.a₁ T.BG T.BG₂ T.κ T.t
      (lvR T.κ T.t (β * 3 ^ k) p₁) 0 0 (1 / S.β))
    (A : physParam 2 S → ℂ → LabelAct (thickLabels I.𝒴 I.dom) (S.blockSplit 1 hp).Ωb
      (2 * (S.β * prop33EpsEtaScaled 3 3 2 T.m₁ k 1 S.a₁ T.BG T.BG₂ T.κ T.t
        (lvR T.κ T.t (β * 3 ^ k) p₁) 0 0 (1 / S.β)))
      (2 * T.κdec - 1) T.κ0 (2 * (K0 3 3 T.κ0 + 1)))
    (hAeq : A = labelActFamilyOn S 1 (physInclScaled 2 S (((1 / S.β : ℝ)) : ℂ)) I hF
      (show 3 ^ 1 ∣ N₁ by simpa using h3N) hp0 (by norm_num) hεU T.κ0_ent
      T.marks_K0_le)
    {Lb₀ : Type} [Fintype Lb₀]
    {Lab₀ : CubeLabels (d := 3) (L := 3) (N₁ := N₁) (m₁ := T.m₁)
      (K := k + 1) 1 (k + 1) Set.univ Lb₀}
    {εH κH κ0 Kc : ℝ}
    (A₀ : physParam 2 S → ℂ → LabelAct Lab₀ (S.blockSplit 1 hp).Ωb εH κH κ0 Kc)
    (hA₀sum : ∀ (e : physParam 2 S) (u : ℂ)
      (Φ : ∀ b, (S.blockSplit 1 hp).Ωb b),
      ∑ y, (A₀ e u).H y Φ =
        sqFactor 2 u * ∑ y, (A ((e.1, 0) : physParam 2 S) u).H y Φ)
    (D : BgData S.G' 2) (hX : XiCData S.G' S.a S.ν (k + 1) 1 T.t D) :
    ∀ s : ℝ, s ∈ Icc (0 : ℝ) 1 → ∀ᵐ x ∂S.nuFl,
      Jr.W1 (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁))
        (rawOf D, (s : ℂ) • Balaban.Fluctuation.yhat x) =
        ∑ y, (A₀ ((⟨rawOf D, rawOf_mem_rawSub _⟩ : rawSub 2 S.G'),
          (0 : CTorus 3 3 N₁ T.m₁ (k + 1) → Fin 2 → ℂ)) (s : ℂ)).H y
          ((S.blockSplit 1 hp).restr x) := by
  classical
  intro s hs
  have hpc : 2 * p₁ < lvCpsi T.κ T.t (β * 3 ^ k) := by
    have hpos : 0 < lvR T.κ T.t (β * 3 ^ k) p₁ * p₁ :=
      mul_pos Dt.r_pos hp0
    nlinarith [Dt.ray_margin]
  have he : ((⟨rawOf D, rawOf_mem_rawSub _⟩ : rawSub 2 S.G'),
      (0 : CTorus 3 3 N₁ T.m₁ (k + 1) → Fin 2 → ℂ)) ∈
      physVq S S.a₁ S.ν T.t 1 := by
    rw [physVq_one]
    exact ⟨⟨D, hX, rfl⟩, by
      change (∑ x : CTorus 3 3 N₁ T.m₁ (k + 1),
        ∑ i : Fin 2, ‖(0 : ℂ)‖) < 1
      simp⟩
  have hpS : S.p₁ = p₁ := by rw [hS]; rfl
  filter_upwards [S.ae_hatOf_restr 1 hp0 hp hpS.le, S.ae_ball hp] with x hx hχ
  have hxn : ‖x‖ < 2 * p₁ := by
    have hx' := (chiFl_eq_one_iff hp x).1 hχ
    rw [hpS] at hx'
    linarith
  have hW : Jr.W1 (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁))
      (rawOf D, (s : ℂ) • S.hatC x) =
      (s : ℂ) ^ 2 * val (S.hatC x, S.hatC x) (S.hatC x, S.hatC x)
        (s : ℂ) (physInclScaled 2 S ((1 / S.β : ℝ) : ℂ)
          ((⟨rawOf D, rawOf_mem_rawSub _⟩ : rawSub 2 S.G'), 0)) := by
    subst hS
    rw [hval, physInclScaled_zeroClass_eq]
    simp only [Pi.zero_apply, zero_div, zero_mul, Finset.sum_const_zero, mul_zero, add_zero]
    exact Jr.W1_zeroClass_eq_hat_freeDatum D hX Dt.core one_pos
      (bgHyp_lv (k := k) T.m₁ hνpos.le hν) T.c7_cap (T.step k hk N₁ ν β p₁).hk1
      (R := 2) (by norm_num) T.bg1_cap T.large_block T.dom_margin
      T.coer_margin T.δc_small Dt.cψ_pos.le Dt.fl_radius hpc x hxn hs
  have hsum : ∑ y, (A ((⟨rawOf D, rawOf_mem_rawSub _⟩ : rawSub 2 S.G'),
      (0 : CTorus 3 3 N₁ T.m₁ (k + 1) → Fin 2 → ℂ)) (s : ℂ)).H y
      ((S.blockSplit 1 hp).restr x) =
      val (S.hatC x, S.hatC x) (S.hatC x, S.hatC x) (s : ℂ)
        (physInclScaled 2 S ((1 / S.β : ℝ) : ℂ)
          ((⟨rawOf D, rawOf_mem_rawSub _⟩ : rawSub 2 S.G'), 0)) := by
    rw [hAeq, labelActFamilyOn_sum S 1 _ hF (by simpa using h3N : 3 ^ 1 ∣ N₁)
      hp0 (by norm_num) hεU T.κ0_ent T.marks_K0_le he
      (norm_ofReal_lt_of_mem hs (by norm_num : (1 : ℝ) < 2)), hx]
  have hhat : S.hatC x = Balaban.Fluctuation.yhat x := rfl
  rw [← hhat, hA₀sum, sqFactor_ofReal (by norm_num : (1 : ℝ) < 2) hs, hsum]
  exact hW

open Classical in
/-- The tower supplies one common-label activity whose first-exponent sum is valid at
every datum of the complex chart. Its labels and activity are chosen before the datum. -/
theorem e1_common_activity_freeDatum_fromTower {κmin : ℝ} (T : StepTower κmin)
    (hHull : stepHullMin ≤ κmin) {A₁ : ℝ} (hA : 0 < A₁) (p : ℕ) :
    ∃ β₀ : ℝ, 3 ≤ β₀ ∧
      ∀ (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁] (h3N : 3 ∣ N₁), 5 < N₁ →
      ∀ ν : ℝ, 0 < ν → ν * 3 ^ (2 * (k + 1)) ≤ 1 → ∀ β : ℝ, β₀ ≤ β →
      ∀ p₁ : ℝ, 0 < p₁ → p₁ ≤ pLog A₁ p (β * 3 ^ k) →
      ∀ Dt : StepScaleData T k hk N₁ ν β p₁,
      ∀ hp : 0 < (T.step k hk N₁ ν β p₁).p₁,
      ∃ (Jr : (T.step k hk N₁ ν β p₁).JointRep T.t (2 * p₁))
        (Lb : Type) (_ : Fintype Lb)
        (Lab₀ : CubeLabels (d := 3) (L := 3) (N₁ := N₁) (m₁ := T.m₁)
          (K := k + 1) 1 (k + 1) Set.univ Lb) (εH : ℝ)
        (A₀ : physParam 2 (T.step k hk N₁ ν β p₁) → ℂ →
          LabelAct (commonLabels Lab₀ (by simpa using h3N : 3 ^ 1 ∣ N₁)
            (by norm_num) (fun _ => Set.univ) (e1Dom (T.step k hk N₁ ν β p₁))
            (e1Dom_isDj T Dt))
            ((T.step k hk N₁ ν β p₁).blockSplit 1 hp).Ωb εH
            (2 * T.κdec - 1) T.κ0 T.marksKc'),
        0 < εH ∧
        εH ≤ stepTheta 3 3 T.marksKc' (2 * T.κdec - 1) T.κ0 T.κ' ∧
        ∀ (D : BgData (T.step k hk N₁ ν β p₁).G' 2)
          (_hX : XiCData (T.step k hk N₁ ν β p₁).G' (T.step k hk N₁ ν β p₁).a
            (T.step k hk N₁ ν β p₁).ν (k + 1) 1 T.t D),
          ∀ s : ℝ, s ∈ Icc (0 : ℝ) 1 →
            ∀ᵐ x ∂(T.step k hk N₁ ν β p₁).nuFl,
              Jr.W1 (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁))
                (rawOf D, (s : ℂ) • Balaban.Fluctuation.yhat x) =
              ∑ y, (A₀ ((⟨rawOf D, rawOf_mem_rawSub _⟩ :
                rawSub 2 (T.step k hk N₁ ν β p₁).G'),
                (0 : CTorus 3 3 N₁ T.m₁ (k + 1) → Fin 2 → ℂ)) (s : ℂ)).H y
                (((T.step k hk N₁ ν β p₁).blockSplit 1 hp).restr x) := by
  classical
  obtain ⟨β₀, CE, CF, h3, hCE, hCF, H⟩ :=
    zeroSourceActivity_common_fromTower T hHull hA p
  refine ⟨β₀, h3, ?_⟩
  intro k hk N₁ _ h3N hN ν hνpos hν β hβ p₁ hp0 hp₁ Dt hp
  let S := T.step k hk N₁ ν β p₁
  obtain ⟨Jr, val, I, hF, hεU, hval, hεpos, -, -, hε, A, hAeq, -, -, hcom⟩ :=
    H k hk N₁ h3N hN ν hνpos hν β hβ p₁ hp0 hp₁ 1 one_pos le_rfl
      Dt S rfl hp
  obtain ⟨A₀, -, -, -, -, hsum, -, -, -, -⟩ :=
    hcom (fun _ => Set.univ) (e1Dom S) (e1Dom_isDj T Dt)
  refine ⟨Jr, {Y // Y ∈ I.𝒴}, inferInstance, thickLabels I.𝒴 I.dom,
    _, A₀, hεpos, hε, ?_⟩
  intro D hX
  exact e1_common_activity_freeDatum_of_directTerms T k hk N₁ h3N ν hνpos hν β p₁
    hp0 Dt S rfl hp Jr val hval I hF hεU A hAeq
    A₀ hsum D hX

end Balaban.Inhabited
