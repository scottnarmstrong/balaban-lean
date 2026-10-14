/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.ActivityFamilyAnalytic
public import Balaban.Fluctuation.ExpSourceChart
public import Balaban.Inhabited.OffFibreE1ActivityG
public import Balaban.Inhabited.ObsTiltFamily
public import Balaban.Inhabited.StepTowerScaleLemmas

/-! The raw observable activity identity for a general step tower. -/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Fluctuation Balaban.Multiscale Balaban.Background Balaban.Localization
  Balaban.Localization.I5Inhabited Balaban.Polymer Balaban.SmallField Balaban.SmallField.Def6
  Balaban.Inhabited.LevelStep MeasureTheory Set Metric

open Classical in
/-- At source radius `ρ` (`q ≤ ρ`); the case `ρ = 1` is `obs_physAct_raw_of_directTermsG`.  The direct-term value of the analytic activity gives the raw observable exponent
at every chart datum. -/
theorem obs_physAct_raw_of_directTermsG_rho {d L N : ℕ} [NeZero L]
    {κmin : ℝ} (T : StepTowerG d L N κmin)
    (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁]
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
    {Lb : Type} [Fintype Lb]
    {Lab : CubeLabels (d := d) (L := L) (N₁ := N₁) (m₁ := T.m₁)
      (K := k + 1) T.m₀ (k + 1) Set.univ Lb}
    (ρ : ℝ)
    {εH κH κ0 Kc q : ℝ} (hq : 0 < q) (hq1 : q ≤ ρ)
    (A : physParam N S → ℂ → LabelAct Lab (S.blockSplit T.m₀ hp).Ωb εH κH κ0 Kc)
    (hsum : ∀ᵐ x ∂S.nuFl,
      ∀ e ∈ physVqRho S S.a₁ S.ν T.t ρ q, ∀ u : ℂ, ‖u‖ < 2 →
        ∑ y, (A e u).H y ((S.blockSplit T.m₀ hp).restr x) =
          val (S.hatC x, S.hatC x) (S.hatC x, S.hatC x) u
            (physInclScaled N S ((1 / S.β : ℝ) : ℂ) e))
    (D : BgData S.G' N) (hX : XiCData S.G' S.a S.ν (k + 1) 1 T.t D)
    (g : Fld d L N₁ T.m₁ (k + 1) N)
    (hg : g ∈ l1BallRho d L N₁ T.m₁ (k + 1) N q) :
    ∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 → ∀ᵐ x ∂S.nuFl,
      Jr.W1 (zeroClass d L N₁ T.m₁ k N (rhoSepG d L T.m₁)) (rawOf D, yhat x) +
        Jr.W2 (zeroClass d L N₁ T.m₁ k N (rhoSepG d L T.m₁)) g
          (rawOf D, (t : ℂ) • yhat x) =
        ∑ y, (physAct A ((⟨rawOf D, rawOf_mem_rawSub _⟩ : rawSub N S.G'), g)
          (t : ℂ)).H y ((S.blockSplit T.m₀ hp).restr x) := by
  classical
  subst hS
  let S := T.step k hk N₁ ν β p₁
  intro t ht
  have hpS : (T.step k hk N₁ ν β p₁).p₁ = p₁ := rfl
  have hpc : 2 * p₁ < lvCpsiG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2))) := by
    have hpos : 0 < lvRG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2))) p₁ * p₁ := mul_pos Dt.r_pos hp0
    nlinarith [Dt.ray_margin]
  have hβpos : 0 < (T.step k hk N₁ ν β p₁).β := Dt.beta_pos
  have hβne : (S.β : ℂ) ≠ 0 := by exact_mod_cast hβpos.ne'
  let e : physParam N S := (⟨rawOf D, rawOf_mem_rawSub _⟩, g)
  have he : e ∈ physVqRho (T.step k hk N₁ ν β p₁)
      (T.step k hk N₁ ν β p₁).a₁ (T.step k hk N₁ ν β p₁).ν T.t ρ q :=
    ⟨⟨⟨D, hX, rfl⟩, lt_of_lt_of_le hg hq1⟩, hg⟩
  have he0 : ((e.1, 0) : physParam N S) ∈ physVqRho S S.a₁ S.ν T.t ρ q :=
    fst_zero_mem_physVqRho S (hq.trans_le hq1) (physVqRho_subset S _ _ _ _ _ he) hq
  filter_upwards [hsum, S.ae_hatOf_restr T.m₀ hp0 hp hpS.le, S.ae_ball hp] with x hx hhat hχ
  have hxn : ‖x‖ < 2 * p₁ := by
    have hx' := (chiFl_eq_one_iff hp x).1 hχ
    rw [hpS] at hx'
    linarith
  have hxb : ∀ r : ℝ, r ∈ Icc (0 : ℝ) 1 →
      ∀ p, ‖((r : ℂ) • S.hatC x) p‖ ≤ 2 * p₁ := by
    intro r hr p
    exact (S.norm_smul_yhat_le_mul r x p).trans (by
      rw [abs_of_nonneg hr.1]
      exact (mul_le_of_le_one_left (norm_nonneg _) hr.2).trans hxn.le)
  have hW1 : ∀ r : ℝ, r ∈ Icc (0 : ℝ) 1 →
      Jr.W1 (zeroClass d L N₁ T.m₁ k N (rhoSepG d L T.m₁))
        (rawOf D, (r : ℂ) • S.hatC x) =
        (r : ℂ) ^ 2 * val (S.hatC x, S.hatC x) (S.hatC x, S.hatC x) (r : ℂ)
          (physInclScaled N S ((1 / S.β : ℝ) : ℂ) (e.1, 0)) := by
    intro r hr
    rw [hval, physInclScaled_zeroClass_eq]
    simp only [Pi.zero_apply, zero_div, zero_mul, Finset.sum_const_zero, mul_zero, add_zero]
    exact Jr.W1_zeroClass_eq_hat_freeDatum D hX Dt.core one_pos
      (bgHyp_lvG (k := k) T.hd T.hL (bgR0_le_rhoSepG T.m₁ T.hd T.hL) hνpos.le hν) T.c7_cap
      (T.step k hk N₁ ν β p₁).hk1
      (R := 2) (by norm_num) T.bg1_cap T.large_block T.dom_margin
      T.coer_margin T.δc_small Dt.cψ_pos.le Dt.fl_radius hpc x hxn hr
  have hW2 : Jr.W2 (zeroClass d L N₁ T.m₁ k N (rhoSepG d L T.m₁)) g
      (rawOf D, (t : ℂ) • S.hatC x) =
      val (S.hatC x, S.hatC x) (S.hatC x, S.hatC x) (t : ℂ)
          (physInclScaled N S ((1 / S.β : ℝ) : ℂ) e) -
        val (S.hatC x, S.hatC x) (S.hatC x, S.hatC x) (t : ℂ)
          (physInclScaled N S ((1 / S.β : ℝ) : ℂ) (e.1, 0)) := by
    rw [physInclScaled_zeroClass_eq, physInclScaled_zeroClass_eq]
    have h0 : (fun y i => ((0 : CTorus d L N₁ T.m₁ (k + 1) → Fin N → ℂ) y i) /
        (S.β : ℂ)) = 0 := by funext y i; simp
    simpa only [h0] using
      (Jr.W2_eq_val_sub Dt.core one_pos (bgHyp_lvG (k := k) T.hd T.hL (bgR0_le_rhoSepG T.m₁ T.hd T.hL) hνpos.le hν)
        T.c7_cap (R := 2) le_rfl T.bg1_cap T.t_cap T.bg0_cap T.cK2_cap
        T.cK2'_cap T.large_block T.dom_margin T.coer_margin T.δc_small
        Dt.cψ_pos.le Dt.fl_radius hpc hX g hβne (S.hatC x) hxb ht val hval)
  have h0 := hx (e.1, 0) he0 (t : ℂ) (norm_ofReal_lt_of_mem ht (by norm_num))
  have h1 := hx e he (t : ℂ) (norm_ofReal_lt_of_mem ht (by norm_num))
  have h01 := hx (e.1, 0) he0 1 (by norm_num)
  rw [physAct_total, h01, h0, h1]
  change Jr.W1 _ (rawOf D, S.hatC x) + Jr.W2 _ g (rawOf D, (t : ℂ) • S.hatC x) = _
  have hW11 := hW1 1 ⟨zero_le_one, le_rfl⟩
  simp only [Complex.ofReal_one, one_smul, one_pow, one_mul] at hW11
  rw [hW11, hW2]
  ring



open Classical in
/-- The direct-term value of the analytic activity gives the raw observable exponent
at every chart datum. -/
theorem obs_physAct_raw_of_directTermsG {d L N : ℕ} [NeZero L]
    {κmin : ℝ} (T : StepTowerG d L N κmin)
    (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁]
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
    {Lb : Type} [Fintype Lb]
    {Lab : CubeLabels (d := d) (L := L) (N₁ := N₁) (m₁ := T.m₁)
      (K := k + 1) T.m₀ (k + 1) Set.univ Lb}
    {εH κH κ0 Kc q : ℝ} (hq : 0 < q) (hq1 : q ≤ 1)
    (A : physParam N S → ℂ → LabelAct Lab (S.blockSplit T.m₀ hp).Ωb εH κH κ0 Kc)
    (hsum : ∀ᵐ x ∂S.nuFl,
      ∀ e ∈ physVq S S.a₁ S.ν T.t q, ∀ u : ℂ, ‖u‖ < 2 →
        ∑ y, (A e u).H y ((S.blockSplit T.m₀ hp).restr x) =
          val (S.hatC x, S.hatC x) (S.hatC x, S.hatC x) u
            (physInclScaled N S ((1 / S.β : ℝ) : ℂ) e))
    (D : BgData S.G' N) (hX : XiCData S.G' S.a S.ν (k + 1) 1 T.t D)
    (g : Fld d L N₁ T.m₁ (k + 1) N)
    (hg : g ∈ l1BallRho d L N₁ T.m₁ (k + 1) N q) :
    ∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 → ∀ᵐ x ∂S.nuFl,
      Jr.W1 (zeroClass d L N₁ T.m₁ k N (rhoSepG d L T.m₁)) (rawOf D, yhat x) +
        Jr.W2 (zeroClass d L N₁ T.m₁ k N (rhoSepG d L T.m₁)) g
          (rawOf D, (t : ℂ) • yhat x) =
        ∑ y, (physAct A ((⟨rawOf D, rawOf_mem_rawSub _⟩ : rawSub N S.G'), g)
          (t : ℂ)).H y ((S.blockSplit T.m₀ hp).restr x) := by
  exact obs_physAct_raw_of_directTermsG_rho T k hk N₁ ν hνpos hν β p₁ hp0 Dt S hS hp Jr val hval 1 hq hq1 A hsum D hX g hg


end Balaban.Inhabited
