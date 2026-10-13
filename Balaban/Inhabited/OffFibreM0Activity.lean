/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.OffFibreM0CoeffSum
public import Balaban.Inhabited.SourceExponentFamily
public import Balaban.Inhabited.ObsTiltLabels
public import Balaban.Inhabited.StepTowerScaleLemmas

/-!
# The observable activity at a free datum

The direct-term sum of an analytic activity identifies the raw first and second exponents
at every datum in the complex chart. This is the value bridge for the observable tilt.
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Fluctuation Balaban.Multiscale Balaban.Background Balaban.Localization
  Balaban.Localization.I5Inhabited Balaban.Polymer Balaban.SmallField Balaban.SmallField.Def6
  Balaban.Inhabited.LevelStep MeasureTheory Set Metric

open Classical in
/-- The direct-term value of the analytic activity gives the raw observable exponent
at every chart datum. -/
theorem obs_physAct_raw_of_directTerms {κmin : ℝ} (T : StepTower κmin)
    (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁]
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
    {Lb : Type} [Fintype Lb]
    {Lab : CubeLabels (d := 3) (L := 3) (N₁ := N₁) (m₁ := T.m₁)
      (K := k + 1) 1 (k + 1) Set.univ Lb}
    {εH κH κ0 Kc q : ℝ} (hq : 0 < q) (hq1 : q ≤ 1)
    (A : physParam 2 S → ℂ → LabelAct Lab (S.blockSplit 1 hp).Ωb εH κH κ0 Kc)
    (hsum : ∀ᵐ x ∂S.nuFl,
      ∀ e ∈ physVq S S.a₁ S.ν T.t q, ∀ u : ℂ, ‖u‖ < 2 →
        ∑ y, (A e u).H y ((S.blockSplit 1 hp).restr x) =
          val (S.hatC x, S.hatC x) (S.hatC x, S.hatC x) u
            (physInclScaled 2 S ((1 / S.β : ℝ) : ℂ) e))
    (D : BgData S.G' 2) (hX : XiCData S.G' S.a S.ν (k + 1) 1 T.t D)
    (g : Fld 3 3 N₁ T.m₁ (k + 1) 2)
    (hg : g ∈ l1BallRho 3 3 N₁ T.m₁ (k + 1) 2 q) :
    ∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 → ∀ᵐ x ∂S.nuFl,
      Jr.W1 (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) (rawOf D, yhat x) +
        Jr.W2 (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) g
          (rawOf D, (t : ℂ) • yhat x) =
        ∑ y, (physAct A ((⟨rawOf D, rawOf_mem_rawSub _⟩ : rawSub 2 S.G'), g)
          (t : ℂ)).H y ((S.blockSplit 1 hp).restr x) := by
  classical
  subst hS
  let S := T.step k hk N₁ ν β p₁
  intro t ht
  have hpS : (T.step k hk N₁ ν β p₁).p₁ = p₁ := rfl
  have hpc : 2 * p₁ < lvCpsi T.κ T.t (β * 3 ^ k) := by
    have hpos : 0 < lvR T.κ T.t (β * 3 ^ k) p₁ * p₁ := mul_pos Dt.r_pos hp0
    nlinarith [Dt.ray_margin]
  have hβpos : 0 < (T.step k hk N₁ ν β p₁).β := Dt.beta_pos
  have hβne : (S.β : ℂ) ≠ 0 := by exact_mod_cast hβpos.ne'
  let e : physParam 2 S := (⟨rawOf D, rawOf_mem_rawSub _⟩, g)
  have he : e ∈ physVq (T.step k hk N₁ ν β p₁)
      (T.step k hk N₁ ν β p₁).a₁ (T.step k hk N₁ ν β p₁).ν T.t q :=
    ⟨⟨⟨D, hX, rfl⟩, lt_of_lt_of_le hg hq1⟩, hg⟩
  have he0 : ((e.1, 0) : physParam 2 S) ∈ physVq S S.a₁ S.ν T.t q :=
    fst_zero_mem_physVq S (physVq_subset S _ _ _ _ he) hq
  filter_upwards [hsum, S.ae_hatOf_restr 1 hp0 hp hpS.le, S.ae_ball hp] with x hx hhat hχ
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
      Jr.W1 (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁))
        (rawOf D, (r : ℂ) • S.hatC x) =
        (r : ℂ) ^ 2 * val (S.hatC x, S.hatC x) (S.hatC x, S.hatC x) (r : ℂ)
          (physInclScaled 2 S ((1 / S.β : ℝ) : ℂ) (e.1, 0)) := by
    intro r hr
    rw [hval, physInclScaled_zeroClass_eq]
    simp only [Pi.zero_apply, zero_div, zero_mul, Finset.sum_const_zero, mul_zero, add_zero]
    exact Jr.W1_zeroClass_eq_hat_freeDatum D hX Dt.core one_pos
      (bgHyp_lv (k := k) T.m₁ hνpos.le hν) T.c7_cap
      (T.step k hk N₁ ν β p₁).hk1
      (R := 2) (by norm_num) T.bg1_cap T.large_block T.dom_margin
      T.coer_margin T.δc_small Dt.cψ_pos.le Dt.fl_radius hpc x hxn hr
  have hW2 : Jr.W2 (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) g
      (rawOf D, (t : ℂ) • S.hatC x) =
      val (S.hatC x, S.hatC x) (S.hatC x, S.hatC x) (t : ℂ)
          (physInclScaled 2 S ((1 / S.β : ℝ) : ℂ) e) -
        val (S.hatC x, S.hatC x) (S.hatC x, S.hatC x) (t : ℂ)
          (physInclScaled 2 S ((1 / S.β : ℝ) : ℂ) (e.1, 0)) := by
    rw [physInclScaled_zeroClass_eq, physInclScaled_zeroClass_eq]
    have h0 : (fun y i => ((0 : CTorus 3 3 N₁ T.m₁ (k + 1) → Fin 2 → ℂ) y i) /
        (S.β : ℂ)) = 0 := by funext y i; simp
    simpa only [h0] using
      (Jr.W2_eq_val_sub Dt.core one_pos (bgHyp_lv (k := k) T.m₁ hνpos.le hν)
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
/-- The tower supplies an analytic physical observable activity whose exponent has its
raw value at every chart datum and every source in the radius-`q` ball. -/
theorem obs_physAct_raw_fromTower {κmin : ℝ} (T : StepTower κmin)
    {A₁ : ℝ} (hA : 0 < A₁) (p : ℕ) :
    ∃ (β₀ CE CF : ℝ), 3 ≤ β₀ ∧ 0 < CE ∧ 0 < CF ∧
      ∀ (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁] (_h3N : 3 ∣ N₁), 5 < N₁ →
      ∀ ν : ℝ, 0 < ν → ν * 3 ^ (2 * (k + 1)) ≤ 1 → ∀ β : ℝ, β₀ ≤ β →
      ∀ p₁ : ℝ, 0 < p₁ → p₁ ≤ pLog A₁ p (β * 3 ^ k) →
      ∀ q : ℝ, 0 < q → q ≤ 1 →
      ∀ (_Dt : StepScaleData T k hk N₁ ν β p₁)
        (S : StepSetting 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)),
        S = T.step k hk N₁ ν β p₁ → ∀ hp : 0 < S.p₁,
      ∃ (Jr : S.JointRep T.t (2 * p₁)) (Lb : Type) (_ : Fintype Lb)
        (Lab : CubeLabels (d := 3) (L := 3) (N₁ := N₁) (m₁ := T.m₁)
          (K := k + 1) 1 (k + 1) Set.univ Lb) (εH : ℝ)
        (A : physParam 2 S → ℂ →
          LabelAct Lab (S.blockSplit 1 hp).Ωb εH (2 * T.κdec - 1)
            T.κ0 (K0 3 3 T.κ0 + 1)),
        0 < εH ∧
        2 * εH ≤ CE * (Real.log (β * 3 ^ k)) ^ (3 * p) / Real.sqrt (β * 3 ^ k) +
          q * CF * (Real.log (β * 3 ^ k)) ^ p / Real.sqrt (β * 3 ^ k) ∧
        (∀ y Φ, AnalyticOnNhd ℂ
          (fun r : physParam 2 S × ℂ => (A r.1 r.2).H y Φ)
          (physVq S S.a₁ S.ν T.t q ×ˢ ball (0 : ℂ) 2)) ∧
        ∀ (D : BgData S.G' 2) (_hX : XiCData S.G' S.a S.ν (k + 1) 1 T.t D)
          (g : Fld 3 3 N₁ T.m₁ (k + 1) 2)
          (_hg : g ∈ l1BallRho 3 3 N₁ T.m₁ (k + 1) 2 q),
          ∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 → ∀ᵐ x ∂S.nuFl,
            Jr.W1 (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) (rawOf D, yhat x) +
              Jr.W2 (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) g
                (rawOf D, (t : ℂ) • yhat x) =
              ∑ y, (physAct A ((⟨rawOf D, rawOf_mem_rawSub _⟩ : rawSub 2 S.G'), g)
                (t : ℂ)).H y ((S.blockSplit 1 hp).restr x) := by
  classical
  obtain ⟨βa, CE, CF, hβa, hCE, hCF, H⟩ := activityFamilyAnalytic_fromTower T hA p
  refine ⟨max βa 3, CE, CF, le_max_right _ _, hCE, hCF, ?_⟩
  intro k hk N₁ _ h3N hN ν hνpos hν β hβ p₁ hp0 hp₁ q hq hq1 Dt S hS hp
  obtain ⟨Jr, val, 𝒴, Tt, I, -, -, hval, -, -, -, hF, hεU, hεpos, hε4, hrest⟩ :=
    H k hk N₁ h3N hN ν hνpos hν β ((le_max_left _ _).trans hβ)
      p₁ hp0 hp₁ q hq hq1 Dt S hS hp
  have hKc : K0 3 3 T.κ0 ≤ K0 3 3 T.κ0 + 1 := by linarith
  obtain ⟨A, hAeq, hhol, -, -, hae, -, -, -, -, -, -, -, -⟩ := hrest hKc
  refine ⟨Jr, {Y // Y ∈ I.𝒴}, inferInstance, thickLabels I.𝒴 I.dom,
    _, A, by linarith, by convert hε4 using 1; ring, hhol, ?_⟩
  intro D hX g hg
  subst hAeq
  exact obs_physAct_raw_of_directTerms T k hk N₁ ν hνpos hν β p₁ hp0 Dt
    S hS hp Jr val hval hq hq1 _ hae D hX g hg

open Classical in
/-- The scalar tilt at source parameter `1` preserves the free-datum observable
exponent supplied by the physical activity. -/
theorem obs_tiltAct_raw_of_physAct {N₁ m₁ k : ℕ} [NeZero N₁] {ϱ eps pp : ℝ}
    (S : StepSetting 3 3 N₁ m₁ k 2 ϱ) (Jr : S.JointRep eps pp)
    (hp : 0 < S.p₁) {Lb : Type} [Fintype Lb]
    {Lab : CubeLabels (d := 3) (L := 3) (N₁ := N₁) (m₁ := m₁)
      (K := k + 1) 1 (k + 1) Set.univ Lb}
    {εH κH κ0 Kc : ℝ}
    (A : physParam 2 S → ℂ → LabelAct Lab (S.blockSplit 1 hp).Ωb εH κH κ0 Kc)
    (hN : 3 ^ 1 ∣ N₁) (hκ0 : aEnt 3 3 + 1 ≤ κ0) (hεH : 0 ≤ εH)
    {𝒴obs : Finset (Set (CTorus 3 3 N₁ m₁ (k + 1)))}
    (hdj : ∀ Y ∈ 𝒴obs, IsDj 1 (k + 1) Y)
    {Kobs : ℝ} (hK : Kc + Kc + K0 3 3 κ0 + K0 3 3 κ0 ≤ Kobs)
    {Rg : ℝ} (hR : 0 ≤ Rg) (hRg : 1 < Rg)
    (D : BgData S.G' 2) (g : Fld 3 3 N₁ m₁ (k + 1) 2)
    (hphys : ∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 → ∀ᵐ x ∂S.nuFl,
      Jr.W1 (zeroClass 3 3 N₁ m₁ k 2 ϱ) (rawOf D, yhat x) +
        Jr.W2 (zeroClass 3 3 N₁ m₁ k 2 ϱ) g
          (rawOf D, (t : ℂ) • yhat x) =
        ∑ y, (physAct A ((⟨rawOf D, rawOf_mem_rawSub _⟩ : rawSub 2 S.G'), g)
          (t : ℂ)).H y ((S.blockSplit 1 hp).restr x)) :
    ∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 → ∀ᵐ x ∂S.nuFl,
      Jr.W1 (zeroClass 3 3 N₁ m₁ k 2 ϱ) (rawOf D, yhat x) +
        Jr.W2 (zeroClass 3 3 N₁ m₁ k 2 ϱ) g
          (rawOf D, (t : ℂ) • yhat x) =
        ∑ y, (tiltActObs A hN hκ0 hεH hdj hK Rg hR
          (ball (0 : ℂ) (3 / 2))
          ((⟨rawOf D, rawOf_mem_rawSub _⟩ : rawSub 2 S.G'), g)
          (t : ℂ) 1).H y ((S.blockSplit 1 hp).restr x) := by
  intro t ht
  filter_upwards [hphys t ht] with x hx
  rw [tiltActObs_total_one A hN hκ0 hεH hdj hK hR hRg
    (seg_mem_ball_three_halves t ht)]
  exact hx

end Balaban.Inhabited
