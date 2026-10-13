/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.ZeroSourceActivityCommon
public import Balaban.Fluctuation.WoneChartIdentity

/-!
# The common first-energy activity at a free datum in a general tower

The direct-term value of the activity on common labels equals the raw first exponent at
every chart datum. The same direct-term witness determines the labels and the activity.
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Fluctuation Balaban.Multiscale Balaban.Background Balaban.Localization
  Balaban.Localization.I5Inhabited Balaban.Polymer Balaban.SmallField Balaban.SmallField.Def6
  Balaban.Inhabited.LevelStep MeasureTheory Set Metric

open Classical in
/-- The common first-energy activity has the raw interaction value at a free chart datum. -/
theorem e1_common_activity_freeDatum_of_directTermsG {d L N : ℕ} [NeZero L]
    {κmin : ℝ} (T : StepTowerG d L N κmin)
    (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁] (hLN : L ^ 1 ∣ N₁)
    (ν : ℝ) (hνpos : 0 < ν) (hν : ν * (L : ℝ) ^ (2 * (k + 1)) ≤ 1)
    (β p₁ : ℝ) (hp0 : 0 < p₁) (Dt : StepScaleDataG T k hk N₁ ν β p₁)
    (S : StepSetting d L N₁ T.m₁ k N (rhoSepG d L T.m₁))
    (hS : S = T.step k hk N₁ ν β p₁) (hp : 0 < S.p₁)
    (Jr : S.JointRep T.t (2 * p₁))
    (val : ((S.U × Fin N → ℂ) × (S.U × Fin N → ℂ)) →
      ((S.U × Fin N → ℂ) × (S.U × Fin N → ℂ)) → ℂ →
      (RawData d L (N₁ * L ^ T.m₁) (k + 1) N ×
        (CTorus d L N₁ T.m₁ (k + 1) → Fin N → ℂ)) → ℂ)
    (hval : ∀ x w σ Θ, val x w σ Θ =
      (-(S.β : ℂ)) * raySrc3 (hatFun S.G' S.a₁ S.ν T.t S.hG'
        ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)
        (interactionOne S.hG S.hG' (le_refl (k + 1)) S.a₁ S.ν T.t))
        taylorWeight x.1 w.1 σ Θ.1 +
      (S.β : ℂ) * (∑ s : CTorus d L N₁ T.m₁ (k + 1) × Fin N, Θ.2 s.1 s.2 *
        dirTermSrc (hatFun S.G' S.a₁ S.ν T.t S.hG'
          ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)
          (onXi S.G' S.a₁ S.ν T.t
            (fun D ψ' => svec (stepG d L N₁ T.m₁ k (rhoSepG d L T.m₁))
              (flFieldOne S.G' (stepG d L N₁ T.m₁ k (rhoSepG d L T.m₁))
                T.BG₂ T.κ S.a₁ S.ν D ψ') s.1 s.2)))
          (fun _ => (1 : ℂ)) x.2 w.2 σ Θ.1))
    (I : DirectTerms S 1 hp (fun ψ => (ψ, ψ)) p₁ 2
      (S.β * prop33EpsEtaScaled d L N T.m₁ k 1 S.a₁ T.BG T.BG₂ T.κ T.t
        (lvRG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2))) p₁) 0 0 (1 / S.β))
      (2 * T.κdec - 1)
      (rawOf S.D', (0 : CTorus d L N₁ T.m₁ (k + 1) → Fin N → ℂ))
      (physSΛEta S S.a₁ S.ν T.t (1 / S.β))
      (physXW S (lvCpsiG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2)))) 2 2
        (lvRG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2))) p₁)) val
      (physAgΘ S) (AgFDirPair S))
    (hF : DirectTermsFamilyOn S 1 (physInclScaled N S (((1 / S.β : ℝ)) : ℂ)) I
      (physVq S S.a₁ S.ν T.t 1))
    (hεU : 0 ≤ S.β * prop33EpsEtaScaled d L N T.m₁ k 1 S.a₁ T.BG T.BG₂ T.κ T.t
      (lvRG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2))) p₁) 0 0 (1 / S.β))
    (A : physParam N S → ℂ → LabelAct (thickLabels I.𝒴 I.dom) (S.blockSplit 1 hp).Ωb
      (2 * (S.β * prop33EpsEtaScaled d L N T.m₁ k 1 S.a₁ T.BG T.BG₂ T.κ T.t
        (lvRG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2))) p₁) 0 0 (1 / S.β)))
      (2 * T.κdec - 1) T.κ0 (2 * (K0 d L T.κ0 + 1)))
    (hAeq : A = labelActFamilyOn S 1 (physInclScaled N S (((1 / S.β : ℝ)) : ℂ)) I hF
      hLN hp0 (by norm_num) hεU T.κ0_ent T.marks_K0_le)
    {Lb₀ : Type} [Fintype Lb₀]
    {Lab₀ : CubeLabels (d := d) (L := L) (N₁ := N₁) (m₁ := T.m₁)
      (K := k + 1) 1 (k + 1) Set.univ Lb₀}
    {εH κH κ0 Kc : ℝ}
    (A₀ : physParam N S → ℂ → LabelAct Lab₀ (S.blockSplit 1 hp).Ωb εH κH κ0 Kc)
    (hA₀sum : ∀ (e : physParam N S) (u : ℂ)
      (Φ : ∀ b, (S.blockSplit 1 hp).Ωb b),
      ∑ y, (A₀ e u).H y Φ =
        sqFactor 2 u * ∑ y, (A ((e.1, 0) : physParam N S) u).H y Φ)
    (D : BgData S.G' N) (hX : XiCData S.G' S.a S.ν (k + 1) 1 T.t D) :
    ∀ s : ℝ, s ∈ Icc (0 : ℝ) 1 → ∀ᵐ x ∂S.nuFl,
      Jr.W1 (zeroClass d L N₁ T.m₁ k N (rhoSepG d L T.m₁))
        (rawOf D, (s : ℂ) • Balaban.Fluctuation.yhat x) =
        ∑ y, (A₀ ((⟨rawOf D, rawOf_mem_rawSub _⟩ : rawSub N S.G'),
          (0 : CTorus d L N₁ T.m₁ (k + 1) → Fin N → ℂ)) (s : ℂ)).H y
          ((S.blockSplit 1 hp).restr x) := by
  classical
  intro s hs
  have hpc : 2 * p₁ < lvCpsiG d L N T.κ T.t
      (β * (L : ℝ) ^ (k * (d - 2))) := by
    have hpos : 0 < lvRG d L N T.κ T.t
        (β * (L : ℝ) ^ (k * (d - 2))) p₁ * p₁ := mul_pos Dt.r_pos hp0
    nlinarith [Dt.ray_margin]
  have he : ((⟨rawOf D, rawOf_mem_rawSub _⟩ : rawSub N S.G'),
      (0 : CTorus d L N₁ T.m₁ (k + 1) → Fin N → ℂ)) ∈
      physVq S S.a₁ S.ν T.t 1 := by
    rw [physVq_one]
    exact ⟨⟨D, hX, rfl⟩, by
      change (∑ x : CTorus d L N₁ T.m₁ (k + 1),
        ∑ i : Fin N, ‖(0 : ℂ)‖) < 1
      simp⟩
  have hpS : S.p₁ = p₁ := by rw [hS]; rfl
  filter_upwards [S.ae_hatOf_restr 1 hp0 hp hpS.le, S.ae_ball hp] with x hx hχ
  have hxn : ‖x‖ < 2 * p₁ := by
    have hx' := (chiFl_eq_one_iff hp x).1 hχ
    rw [hpS] at hx'
    linarith
  have hW : Jr.W1 (zeroClass d L N₁ T.m₁ k N (rhoSepG d L T.m₁))
      (rawOf D, (s : ℂ) • S.hatC x) =
      (s : ℂ) ^ 2 * val (S.hatC x, S.hatC x) (S.hatC x, S.hatC x)
        (s : ℂ) (physInclScaled N S ((1 / S.β : ℝ) : ℂ)
          ((⟨rawOf D, rawOf_mem_rawSub _⟩ : rawSub N S.G'), 0)) := by
    subst hS
    rw [hval, physInclScaled_zeroClass_eq]
    simp only [Pi.zero_apply, zero_div, zero_mul, Finset.sum_const_zero, mul_zero, add_zero]
    exact Jr.W1_zeroClass_eq_hat_freeDatum D hX Dt.core one_pos
      (bgHyp_lvG (k := k) T.hd T.hL (bgR0_le_rhoSepG T.m₁ T.hd T.hL)
        hνpos.le hν) T.c7_cap (T.step k hk N₁ ν β p₁).hk1
      (R := 2) (by norm_num) T.bg1_cap T.large_block T.dom_margin
      T.coer_margin T.δc_small Dt.cψ_pos.le Dt.fl_radius hpc x hxn hs
  have hsum : ∑ y, (A ((⟨rawOf D, rawOf_mem_rawSub _⟩ : rawSub N S.G'),
      (0 : CTorus d L N₁ T.m₁ (k + 1) → Fin N → ℂ)) (s : ℂ)).H y
      ((S.blockSplit 1 hp).restr x) =
      val (S.hatC x, S.hatC x) (S.hatC x, S.hatC x) (s : ℂ)
        (physInclScaled N S ((1 / S.β : ℝ) : ℂ)
          ((⟨rawOf D, rawOf_mem_rawSub _⟩ : rawSub N S.G'), 0)) := by
    rw [hAeq, labelActFamilyOn_sum S 1 _ hF hLN
      hp0 (by norm_num) hεU T.κ0_ent T.marks_K0_le he
      (norm_ofReal_lt_of_mem hs (by norm_num : (1 : ℝ) < 2)), hx]
  have hhat : S.hatC x = Balaban.Fluctuation.yhat x := rfl
  rw [← hhat, hA₀sum, sqFactor_ofReal (by norm_num : (1 : ℝ) < 2) hs, hsum]
  exact hW

end Balaban.Inhabited
