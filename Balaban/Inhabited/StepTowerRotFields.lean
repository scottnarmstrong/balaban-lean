/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.LocalClassDensityFamilyActTower
public import Balaban.Inhabited.StepTowerBeta0Zero
public import Balaban.Inhabited.E0CoeffFamilyRotCore

/-!
The zero-source family of the class chain at every tower radius, with the spin covariance of its activity

`zeroSourceFamily_fields_fromTower_agree_rot`: the statement of
`zeroSourceFamily_fields_fromTower_agree` with the covariance of the activity; the landed theorem is
its corollary.
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Fluctuation Balaban.Multiscale Balaban.Background Balaban.Localization
  Balaban.Localization.LevelPair Balaban.Localization.I5Inhabited Balaban.Polymer
  Balaban.SmallField Balaban.SmallField.Def6 Balaban.Inhabited.LevelStep Matrix Metric Set
  MeasureTheory Balaban.Inhabited.MarkBudgetAudit Balaban.SmallField.Def6v2
  Balaban.SmallField.GsSpec Balaban.Analysis

open Classical in
/-- **The zero-source family of the class chain at every tower radius, with the spin covariance of
its activity, general tower.**  The statement of `zeroSourceFamily_fields_fromTower_agree` with one more conjunct: for a
real orthogonal `Q` and `θ, θ' ∈ physV` with `θ'.1 = rotRaw (cmat Q) θ.1`, the activity at `θ'` of the
rotated block variable is the activity at `θ` of the block variable. -/
theorem StepTowerG.zeroSourceFamily_fields_agree_rot {d L N : ℕ} [NeZero L] {κmin : ℝ} (T₀ : StepTowerG d L N κmin) (hm₀ : T₀.m₀ = 1)
    (hhull : 2 * d * L * (1 + collarB d L) * (3 / 2 * T₀.κdec + c1 d L * Real.log 2) +
      Real.log 2 + 2 * Real.log ((detDeg d L + 1 : ℕ) : ℝ) ≤ T₀.κ) {A₁ : ℝ} (hA : 0 < A₁) (p : ℕ) {cR αR : ℝ} (hcR : 0 < cR) (hαR : 2 * αR < ((d - 2 : ℕ) : ℝ)) :
    ∃ β₀ : ℝ, 3 ≤ β₀ ∧ ∀ T : StepTowerG d L N κmin, T.m₀ = T₀.m₀ → T.m₁ = T₀.m₁ → T.BG = T₀.BG → T.BG₂ = T₀.BG₂ →
      T.κ = T₀.κ → T.κ0 = T₀.κ0 → T.κ' = T₀.κ' → T.δ = T₀.δ →
      ∀ (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁], L ^ T.m₀ ∣ N₁ → 5 < N₁ →
      ∀ ν : ℝ, 0 < ν → ν * (L : ℝ) ^ (2 * (k + 1)) ≤ 1 → ∀ β : ℝ, β₀ ≤ β →
      cR * (L : ℝ) ^ (-(αR * ((k : ℝ) + 1))) ≤ T.t →
      ∀ p₁ : ℝ, 0 < p₁ → p₁ ≤ pLog A₁ p (β * (L : ℝ) ^ (k * (d - 2))) →
      StepScaleDataG T k hk N₁ ν β p₁ → ∀ (S : StepSetting d L N₁ T.m₁ k N (rhoSepG d L T.m₁)),
        S = T.step k hk N₁ ν β p₁ → ∀ (hp : 0 < S.p₁),
      ∃ (Jr : S.JointRep T.t (2 * p₁)) (Lb₀ : Type) (_ : Fintype Lb₀)
        (Lab₀ : CubeLabels (d := d) (L := L) (N₁ := N₁) (m₁ := T.m₁) (K := k + 1) 1 (k + 1)
          Set.univ Lb₀)
        (A₀ : physParam N S → ℂ → LabelAct Lab₀ (S.blockSplit 1 hp).Ωb
          (2 ^ 2 * (2 * (S.β * prop33EpsEtaScaled d L N T.m₁ k 1 S.a₁ T.BG T.BG₂ T.κ T.t
            (lvRG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2))) p₁) 0 0 (1 / S.β))))
          (2 * T.κdec - 1) T.κ0 (2 * (K0 d L T.κ0 + 1))),
        0 < 2 ^ 2 * (2 * (S.β * prop33EpsEtaScaled d L N T.m₁ k 1 S.a₁ T.BG T.BG₂ T.κ T.t
            (lvRG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2))) p₁) 0 0 (1 / S.β))) ∧
        (∀ y, ∀ Φ ∈ physCarrier S 1 hp, AnalyticOnNhd ℂ
          (fun r : physParam N S × ℂ => (A₀ r.1 r.2).H y Φ)
          (physV S S.a₁ S.ν T.t ×ˢ Metric.ball (0 : ℂ) corrU)) ∧
        (∀ y, ∀ θ ∈ physV S S.a₁ S.ν T.t, ∀ u ∈ Metric.ball (0 : ℂ) corrU,
          ContinuousOn ((A₀ θ u).H y) (physCarrier S 1 hp)) ∧
        (∀ θ ∈ physV S S.a₁ S.ν T.t, ∀ y Φ,
          DifferentiableOn ℂ (fun u => (A₀ θ u).H y Φ) (Metric.ball (0 : ℂ) corrU)) ∧
        (∀ T' : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := T.m₁) (K := k + 1) 1 (k + 1)
            Set.univ), ∀ θ ∈ physV S S.a₁ S.ν T.t, ∀ θ' ∈ physV S S.a₁ S.ν T.t,
          physRestrict (N := N) (sitesOf T') (physIncl N S θ) =
            physRestrict (sitesOf T') (physIncl N S θ') →
          ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ y, Lab₀.ysite y ⊆ Yhat Set.univ (sitesOf T') →
            (A₀ θ (s : ℂ)).H y = (A₀ θ' (s : ℂ)).H y) ∧
        (∀ D : BgData S.G' N, XiCData S.G' S.a S.ν (k + 1) 1 T.t D →
          ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ᵐ x ∂S.nuFl,
            Jr.W1 (zeroClass d L N₁ T.m₁ k N (rhoSepG d L T.m₁))
                (rawOf D, (s : ℂ) • Balaban.Fluctuation.yhat x) =
              ∑ y, (A₀ ((⟨rawOf D, rawOf_mem_rawSub _⟩ : rawSub N S.G'),
                (0 : CTorus d L N₁ T.m₁ (k + 1) → Fin N → ℂ)) (s : ℂ)).H y
                ((S.blockSplit 1 hp).restr x)) ∧
        -- the spin covariance of the activity
        ∀ Q : Matrix (Fin N) (Fin N) ℝ, Qᵀ * Q = 1 →
          ∀ θ ∈ physV S S.a₁ S.ν T.t, ∀ θ' ∈ physV S S.a₁ S.ν T.t,
          (θ'.1 : RawData d L (N₁ * L ^ T.m₁) (k + 1) N) =
            rotRaw (cmat Q) (θ.1 : RawData d L (N₁ * L ^ T.m₁) (k + 1) N) →
          ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ y, ∀ Φ ∈ physCarrier S 1 hp,
            (A₀ θ' (s : ℂ)).H y (fun b u => WithLp.toLp 2 (Q *ᵥ (Φ b u).ofLp)) =
              (A₀ θ (s : ℂ)).H y Φ   := by
  classical
  obtain ⟨β₂, h3, H2⟩ := T₀.zeroSourceActivity_common_agree_rot hhull hA p hcR hαR
  refine ⟨β₂, h3, fun T hm₀T hm₁ hBG hBG₂ hκ h0 h' _ => ?_⟩
  have hm1 : T.m₀ = 1 := hm₀T.trans hm₀
  have H2T := H2 T hm₀T hm₁ hBG hBG₂ hκ h0 h'
  rw [hm1] at H2T
  intro k hk N₁ _ hLN hN₁ ν hν0 hν β hβ hct p₁ hp0 hp₁ Dt S hS hp
  have hN1 : L ^ 1 ∣ N₁ := by rwa [hm1] at hLN
  have H3 := H2T k hk N₁ hN1 hN₁ ν hν0 hν β hβ hct p₁ hp0 hp₁ 1 one_pos le_rfl Dt S hS hp
  obtain ⟨Jr, val, I, hF, hεU, ⟨-, F₂, Sol₂, hF₂, hSol₂, hTI⟩, hval, hεpos, -, -, A, hAeq, -, -,
    hcom⟩ := H3
  obtain ⟨A0, hA0eq, hAhol, hAdiff, hAcont, -, -, -, -, -⟩ :=
    hcom (fun _ => Set.univ) (e1DomG S) (e1DomG_isDj_of_eq T hm1 Dt rfl hS)
  subst hA0eq
  have hU2 : Metric.ball (0 : ℂ) corrU ⊆ Metric.ball (0 : ℂ) 2 :=
    Metric.ball_subset_ball (by unfold corrU; norm_num)
  have hεzs : 0 ≤ 2 ^ 2 * (2 * (S.β * prop33EpsEtaScaled d L N T.m₁ k 1 S.a₁ T.BG T.BG₂ T.κ T.t
      (lvRG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2))) p₁) 0 0 (1 / S.β))) :=
    mul_nonneg (sq_nonneg 2) (mul_nonneg zero_le_two hεU)
  refine ⟨Jr, {Y // Y ∈ I.𝒴}, inferInstance, thickLabels I.𝒴 I.dom, zeroSourceAct A 2 zero_le_two,
    hεpos,
    fun y Φ _ => (hAhol (Sum.inl y) Φ).mono (Set.prod_mono subset_rfl hU2),
    fun y θ hθ u hu => (hAcont (Sum.inl y) θ hθ u (hU2 hu)).continuousOn,
    fun θ hθ y Φ => (hAdiff θ hθ (Sum.inl y) Φ).mono hU2,
    fun T' θ hθ θ' hθ' hres s hs y hsub => by
      subst hAeq
      exact commonAct_zeroSourceAct_hA_rawY S 1 _ hF hN1 hp0 zero_le_two hεU T.κ0_ent
        T.marks_K0_le (fun _ => Set.univ) (e1DomG S) (e1DomG_isDj_of_eq T hm1 Dt rfl hS)
        (by have := T.hL; omega) hεzs T.κ0_two one_pos T' θ hθ θ' hθ' hres s hs (Sum.inl y) hsub,
    fun D hX => e1_common_activity_freeDatum_of_directTermsG T k hk N₁ hN1 ν hν0 hν β p₁ hp0 Dt
      S hS hp Jr val hval I hF hεU A hAeq (zeroSourceAct A 2 zero_le_two)
      (zeroSourceAct_total A 2 zero_le_two) D hX,
    fun Q hQ θ hθ θ' hθ' hrot s hs y Φ hΦ => ?_⟩
  subst hS
  subst hAeq
  obtain ⟨e, he⟩ := exists_linearIsometryEquiv_of_orth N hQ
  obtain ⟨D₀, hD₀, hD₀θ''⟩ := hθ.1
  have hD₀θ : (θ.1 : RawData d L (N₁ * L ^ T.m₁) (k + 1) N) = rawOf D₀ := hD₀θ''
  have hfun : (fun b u => WithLp.toLp 2 (Q *ᵥ (Φ b u).ofLp)) = fun b u => e (Φ b u) :=
    funext fun b => funext fun u => (he _).symm
  rw [hfun]
  refine commonAct_zeroSourceAct_H_rot (T.step k hk N₁ ν β p₁) 1 _ hF hN1 hp0 zero_le_two hεU
    T.κ0_ent T.marks_K0_le (fun _ => Set.univ) (e1DomG (T.step k hk N₁ ν β p₁))
    (e1DomG_isDj_of_eq T hm1 Dt rfl rfl) (by have := T.hL; omega) hεzs T.κ0_two one_pos le_rfl
    hθ hθ' (s : ℂ) (Sum.inl y) Φ (fun b u => e (Φ b u)) ?_
  intro z' hy hu
  have hψ : ∀ q, ‖((T.step k hk N₁ ν β p₁).hatOf 1 p₁ hp Φ) q‖ ≤ p₁ :=
    (T.step k hk N₁ ν β p₁).hatOf_mem 1 hp hp Φ
  have hh : (T.step k hk N₁ ν β p₁).hatOf 1 p₁ hp (fun b u => e (Φ b u)) =
      rotFld (cmat Q) ((T.step k hk N₁ ν β p₁).hatOf 1 p₁ hp Φ) :=
    hatOf_rot (T.step k hk N₁ ν β p₁) 1 hp e he le_rfl hΦ
  refine Eq.trans (congrArg (fun x => I.T z'.1 (x, x) (x, x) (s : ℂ)
    ((θ'.1 : RawData d L (N₁ * L ^ T.m₁) (k + 1) N), 0)) hh) ?_
  rw [hrot, hD₀θ]
  exact directTerm_rot_of_ray (T.step k hk N₁ ν β p₁) Dt.core hk (T.step k hk N₁ ν β p₁).hG
    T.large_block T.dom_margin T.coer_margin T.δc_small Dt.cψ_pos.le Dt.r_pos Dt.ray_margin
    Dt.fl_radius F₂ Sol₂ hF₂ hSol₂ I.T hTI hQ z'.1 hD₀ hψ hu

open Classical in
/-- **The zero-source family of the class chain at every tower radius, with the spin covariance of
its activity.**  The statement of `zeroSourceFamily_fields_fromTower_agree` with one more conjunct: for a
real orthogonal `Q` and `θ, θ' ∈ physV` with `θ'.1 = rotRaw (cmat Q) θ.1`, the activity at `θ'` of the
rotated block variable is the activity at `θ` of the block variable. -/
theorem zeroSourceFamily_fields_fromTower_agree_rot {κmin : ℝ} (T₀ : StepTower κmin)
    (hHull : stepHullMin ≤ κmin) {A₁ : ℝ} (hA : 0 < A₁) (p : ℕ) {cR αR : ℝ} (hcR : 0 < cR) (hαR : 2 * αR < 1) :
    ∃ β₀ : ℝ, 3 ≤ β₀ ∧ ∀ T : StepTower κmin, T.m₁ = T₀.m₁ → T.BG = T₀.BG → T.BG₂ = T₀.BG₂ →
      T.κ = T₀.κ → T.δ = T₀.δ →
      ∀ (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁], 3 ∣ N₁ → 5 < N₁ →
      ∀ ν : ℝ, 0 < ν → ν * 3 ^ (2 * (k + 1)) ≤ 1 → ∀ β : ℝ, β₀ ≤ β →
      cR * (3 : ℝ) ^ (-(αR * ((k : ℝ) + 1))) ≤ T.t →
      ∀ p₁ : ℝ, 0 < p₁ → p₁ ≤ pLog A₁ p (β * 3 ^ k) →
      StepScaleData T k hk N₁ ν β p₁ → ∀ (S : StepSetting 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)),
        S = T.step k hk N₁ ν β p₁ → ∀ (hp : 0 < S.p₁),
      ∃ (Jr : S.JointRep T.t (2 * p₁)) (Lb₀ : Type) (_ : Fintype Lb₀)
        (Lab₀ : CubeLabels (d := 3) (L := 3) (N₁ := N₁) (m₁ := T.m₁) (K := k + 1) 1 (k + 1)
          Set.univ Lb₀)
        (A₀ : physParam 2 S → ℂ → LabelAct Lab₀ (S.blockSplit 1 hp).Ωb
          (2 ^ 2 * (2 * (S.β * prop33EpsEtaScaled 3 3 2 T.m₁ k 1 S.a₁ T.BG T.BG₂ T.κ T.t
            (lvR T.κ T.t (β * 3 ^ k) p₁) 0 0 (1 / S.β))))
          (2 * T.κdec - 1) T.κ0 (2 * (K0 3 3 T.κ0 + 1))),
        0 < 2 ^ 2 * (2 * (S.β * prop33EpsEtaScaled 3 3 2 T.m₁ k 1 S.a₁ T.BG T.BG₂ T.κ T.t
            (lvR T.κ T.t (β * 3 ^ k) p₁) 0 0 (1 / S.β))) ∧
        (∀ y, ∀ Φ ∈ physCarrier S 1 hp, AnalyticOnNhd ℂ
          (fun r : physParam 2 S × ℂ => (A₀ r.1 r.2).H y Φ)
          (physV S S.a₁ S.ν T.t ×ˢ Metric.ball (0 : ℂ) corrU)) ∧
        (∀ y, ∀ θ ∈ physV S S.a₁ S.ν T.t, ∀ u ∈ Metric.ball (0 : ℂ) corrU,
          ContinuousOn ((A₀ θ u).H y) (physCarrier S 1 hp)) ∧
        (∀ θ ∈ physV S S.a₁ S.ν T.t, ∀ y Φ,
          DifferentiableOn ℂ (fun u => (A₀ θ u).H y Φ) (Metric.ball (0 : ℂ) corrU)) ∧
        (∀ T' : Finset (CubeB (d := 3) (L := 3) (N₁ := N₁) (m₁ := T.m₁) (K := k + 1) 1 (k + 1)
            Set.univ), ∀ θ ∈ physV S S.a₁ S.ν T.t, ∀ θ' ∈ physV S S.a₁ S.ν T.t,
          physRestrict (N := 2) (sitesOf T') (physIncl 2 S θ) =
            physRestrict (sitesOf T') (physIncl 2 S θ') →
          ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ y, Lab₀.ysite y ⊆ Yhat Set.univ (sitesOf T') →
            (A₀ θ (s : ℂ)).H y = (A₀ θ' (s : ℂ)).H y) ∧
        (∀ D : BgData S.G' 2, XiCData S.G' S.a S.ν (k + 1) 1 T.t D →
          ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ᵐ x ∂S.nuFl,
            Jr.W1 (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁))
                (rawOf D, (s : ℂ) • Balaban.Fluctuation.yhat x) =
              ∑ y, (A₀ ((⟨rawOf D, rawOf_mem_rawSub _⟩ : rawSub 2 S.G'),
                (0 : CTorus 3 3 N₁ T.m₁ (k + 1) → Fin 2 → ℂ)) (s : ℂ)).H y
                ((S.blockSplit 1 hp).restr x)) ∧
        -- the spin covariance of the activity
        ∀ Q : Matrix (Fin 2) (Fin 2) ℝ, Qᵀ * Q = 1 →
          ∀ θ ∈ physV S S.a₁ S.ν T.t, ∀ θ' ∈ physV S S.a₁ S.ν T.t,
          (θ'.1 : RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2) =
            rotRaw (cmat Q) (θ.1 : RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2) →
          ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ y, ∀ Φ ∈ physCarrier S 1 hp,
            (A₀ θ' (s : ℂ)).H y (fun b u => WithLp.toLp 2 (Q *ᵥ (Φ b u).ofLp)) =
              (A₀ θ (s : ℂ)).H y Φ   := by
  obtain ⟨β₀, h3, H⟩ := StepTowerG.zeroSourceFamily_fields_agree_rot T₀.toG rfl
    (T₀.hhull_toG_of_stepHullMin hHull) hA p hcR (alpha_three_cast hαR)
  refine ⟨β₀, h3, fun T hm₁ hBG hBG₂ hκ hδ k hk N₁ _ h3N hN ν hν0 hν β hβ hct p₁ hp0 hp₁ Dt S hS
    hp => ?_⟩
  obtain ⟨h0, -, h'⟩ := StepTower.agree_rates T₀ T
  subst hS
  have e : (((3 : ℕ) : ℝ)) ^ (k * (3 - 2)) = 3 ^ k := by norm_num
  have hp' : 0 < (T.toG.step k hk N₁ ν β p₁).p₁ := hp
  have G := H T.toG rfl hm₁ hBG hBG₂ hκ h0 h' hδ k hk N₁ (by simpa using h3N) hN ν hν0
    (by simpa using hν) β hβ (by rw [radius_three_cast]; exact hct) p₁ hp0 (by rw [e]; exact hp₁)
    (StepTower.scaleDataG_of_fixed T Dt) (T.toG.step k hk N₁ ν β p₁) rfl hp'
  unfold StepTowerG.step at G
  revert G
  generalize hb : β * ((3 : ℕ) : ℝ) ^ (k * (3 - 2)) = b
  generalize hϱ : rhoSepG 3 3 T.toG.m₁ = ϱ
  have hϱ' : ϱ = rhoSep T.m₁ := hϱ.symm.trans (rhoSepG_three _)
  have hb' : b = β * 3 ^ k := hb.symm.trans (by rw [e])
  subst hϱ' hb'
  intro G
  exact G

end Balaban.Inhabited
