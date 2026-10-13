/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.StepTowerScale
public import Balaban.Inhabited.ExpSourceChartFromTower
public import Balaban.Fluctuation.SourceAmpNonneg
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The source direct terms over the relative chart at every scale of a fixed tower

`sourceFamilyRelative_scale_fromTower` restates `sourceFamilyRelative_scale_nonneg` for one tower
`T : StepTower κmin` and its per-scale package `D : StepScaleData T …`: the landed proof is re-run
with its tower prologue replaced by the fields of `T` and `D`.  The only threshold is the one of
the amplitude estimate `sourceAmp_scale`, chosen after `T`.

Source activity with common labels and the chart/determinant joint endpoint are not in this file.
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation
  Balaban.Localization Balaban.Localization.LevelPair Balaban.Localization.I5Inhabited
  Balaban.Polymer Balaban.SmallField.Def6 Balaban.Inhabited.LevelStep Filter Topology Metric

open Classical in
/-- **The source direct terms as a family over the relative chart, at every scale of the tower
`T`.**  The conclusion of `sourceFamilyRelative_scale_nonneg` at the constants `T.m₁`, `T.t`,
`T.δ`, `T.BG`, `T.BG₂`, `T.κ`, `T.κ0`, `T.κdec`, with the threshold `β₀` and the amplitude
constants `C_E, C_F` chosen after `T`. -/
theorem sourceFamilyRelative_scale_fromTower {κmin : ℝ} (T : StepTower κmin) {A₁ : ℝ}
    (hA : 0 < A₁) (p : ℕ) :
    ∃ (β₀ CE CF : ℝ), 2 ≤ β₀ ∧ 0 < CE ∧ 0 < CF ∧
      ∀ (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁] (h3N : 3 ∣ N₁), 5 < N₁ →
      ∀ ν : ℝ, 0 < ν → ν * 3 ^ (2 * (k + 1)) ≤ 1 → ∀ β : ℝ, β₀ ≤ β →
      ∀ p₁ : ℝ, ∀ hp0 : 0 < p₁, p₁ ≤ pLog A₁ p (β * 3 ^ k) → ∀ q : ℝ, 0 < q → q ≤ 1 →
      StepScaleData T k hk N₁ ν β p₁ →
      ∀ S : StepSetting 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁),
        S = T.step k hk N₁ ν β p₁ → ∀ hp : 0 < S.p₁,
      ∃ (val : ((S.U × Fin 2 → ℂ) × (S.U × Fin 2 → ℂ)) → ((S.U × Fin 2 → ℂ) × (S.U × Fin 2 → ℂ)) →
            ℂ → (RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2 × (CTorus 3 3 N₁ T.m₁ (k + 1) → Fin 2 → ℂ)) → ℂ)
          (𝒴 : Finset (Set (CTorus 3 3 N₁ T.m₁ (k + 1))))
          (Tt : Set (CTorus 3 3 N₁ T.m₁ (k + 1)) → ((S.U × Fin 2 → ℂ) × (S.U × Fin 2 → ℂ)) →
            ((S.U × Fin 2 → ℂ) × (S.U × Fin 2 → ℂ)) → ℂ →
            (RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2 × (CTorus 3 3 N₁ T.m₁ (k + 1) → Fin 2 → ℂ)) → ℂ)
          (I : DirectTerms S 1 hp (fun ψ => (ψ, ψ)) p₁ 2
                (S.β * prop33EpsEtaScaled 3 3 2 T.m₁ k 1 S.a₁ T.BG T.BG₂ T.κ T.t
                  (lvR T.κ T.t (β * 3 ^ k) p₁) 0 0 (q / S.β)) (2 * T.κdec - 1)
                (rawOf S.D', (0 : CTorus 3 3 N₁ T.m₁ (k + 1) → Fin 2 → ℂ))
                (physSΛEta S S.a₁ S.ν T.t (q / S.β))
                (physXW S (lvCpsi T.κ T.t (β * 3 ^ k)) 2 2 (lvR T.κ T.t (β * 3 ^ k) p₁)) val (physAgΘ S)
                (AgFDirPair S)),
          I.𝒴 = 𝒴 ∧ I.T = Tt ∧
          ∃ hF : DirectTermsFamilyOn S 1 (physInclScaled 2 S (((1 / S.β : ℝ)) : ℂ)) I
              (physVq S 1 ν T.t q),
            (∀ g : Fld 3 3 N₁ T.m₁ (k + 1) 2, ∑ x, ∑ i, ‖g x i‖ < q →
              ∃ hg : (⟨rawOf S.D', rawOf_mem_rawSub _⟩, g) ∈ physVq S 1 ν T.t q,
                physInclScaled 2 S (((1 / S.β : ℝ)) : ℂ) (⟨rawOf S.D', rawOf_mem_rawSub _⟩, g) =
                  (rawOf S.D', fun y i => g y i / (S.β : ℂ)) ∧
                (I.atThetaOn S 1 _ hF hg).𝒴 = 𝒴 ∧ (I.atThetaOn S 1 _ hF hg).T = Tt) ∧
            ∃ hεU : 0 ≤ S.β * prop33EpsEtaScaled 3 3 2 T.m₁ k 1 S.a₁ T.BG T.BG₂ T.κ T.t
                  (lvR T.κ T.t (β * 3 ^ k) p₁) 0 0 (q / S.β),
              4 * (S.β * prop33EpsEtaScaled 3 3 2 T.m₁ k 1 S.a₁ T.BG T.BG₂ T.κ T.t
                  (lvR T.κ T.t (β * 3 ^ k) p₁) 0 0 (q / S.β)) ≤
                CE * (Real.log (β * 3 ^ k)) ^ (3 * p) / Real.sqrt (β * 3 ^ k) +
                  q * CF * (Real.log (β * 3 ^ k)) ^ p / Real.sqrt (β * 3 ^ k) ∧
              ∀ {Kc : ℝ} (hKc : K0 3 3 T.κ0 ≤ Kc),
              (∀ (y : {Y // Y ∈ I.𝒴}) (Φ : ∀ b, (S.blockSplit 1 hp).Ωb b),
                AnalyticOnNhd ℂ (fun r : physParam 2 S × ℂ =>
                  (labelActFamilyOn S 1 (physInclScaled 2 S (((1 / S.β : ℝ)) : ℂ)) I hF
                    (show 3 ^ 1 ∣ N₁ by simpa using h3N) hp0 (by norm_num) hεU
                    T.κ0_ent hKc r.1 r.2).H y Φ)
                  (physVq S 1 ν T.t q ×ˢ ball (0 : ℂ) 2)) ∧
              (∀ e (he : e ∈ physVq S 1 ν T.t q) (u : ℂ),
                labelActFamilyOn S 1 (physInclScaled 2 S (((1 / S.β : ℝ)) : ℂ)) I hF
                    (show 3 ^ 1 ∣ N₁ by simpa using h3N) hp0 (by norm_num) hεU
                    T.κ0_ent hKc e u =
                  dtAct S 1 (I.atThetaOn S 1 _ hF he)
                    (show 3 ^ 1 ∣ N₁ by simpa using h3N) hp0 (by norm_num) hεU
                    T.κ0_ent hKc u) ∧
              (∀ e ∈ physVq S 1 ν T.t q, ∀ u : ℂ, ‖u‖ < 2 →
                ∀ (y : {Y // Y ∈ I.𝒴}) (Φ : ∀ b, (S.blockSplit 1 hp).Ωb b),
                (labelActFamilyOn S 1 (physInclScaled 2 S (((1 / S.β : ℝ)) : ℂ)) I hF
                    (show 3 ^ 1 ∣ N₁ by simpa using h3N) hp0 (by norm_num) hεU
                    T.κ0_ent hKc e u).H y Φ =
                  I.T y.1 (S.hatOf 1 p₁ hp Φ, S.hatOf 1 p₁ hp Φ)
                    (S.hatOf 1 p₁ hp Φ, S.hatOf 1 p₁ hp Φ) u
                    (physInclScaled 2 S (((1 / S.β : ℝ)) : ℂ) e)) := by
  classical
  have h4 := T.m₁_four
  have ht0 := T.t_pos
  have hMX := T.large_block
  have hdm := T.dom_margin
  have hα := T.coer_margin
  have hsmX := T.δc_small
  have hc7 := T.c7_cap
  have g1 := T.t_cap
  have g2 := T.bg0_cap
  have g3 := T.cK2_cap
  have g4 := T.cK2'_cap
  have g5 := T.bg1_cap
  have hκ0 := T.κ0_nonneg
  have hκdec := T.κdec_lower
  have hκ := T.κ_lower
  have h1 := T.κ_one
  have hlog := T.κ_log
  have hxi1 := T.xi_small
  have hρ4 := T.rho_nonneg
  have hB0 := T.fam_nonneg
  have hc1 := one_le_c1 3 3
  have hent := aEnt_nonneg 3 3
  obtain ⟨Q, hQdef⟩ : ∃ Q : ℝ, Q = cK2' 3 3 2 (famConst 3 3 T.BG₂ T.κ) := ⟨_, rfl⟩
  have hQ0 : 0 < Q := by rw [hQdef]; exact cK2'_pos' hB0
  obtain ⟨P, hPdef⟩ : ∃ P : ℝ, P = 3 * c1 3 3 * (((3 : ℕ) : ℝ) ^ (1 + T.m₁)) ^ 3 *
    (((3 : ℕ) : ℝ) ^ 3 * ((((2 : ℕ) : ℝ) / 2) * (2 * (1 + Q) ^ 2 +
      (((3 : ℕ) : ℝ) + 1 + rho4 3 3 2 T.BG T.κ) * Q ^ 2) * T.t ^ 2)) := ⟨_, rfl⟩
  have hP0 : 0 ≤ P := by
    rw [hPdef]; positivity
  have hK0 : 0 < Q * T.t := mul_pos hQ0 ht0
  obtain ⟨β₁, hexpβ₁, hA'⟩ := sourceAmp_scale (A₁ := A₁) (κ := T.κ) (t := T.t) hA p ht0
  refine ⟨max 2 β₁, srcCE A₁ T.κ T.t P, srcCF A₁ T.κ T.t (Q * T.t), le_max_left _ _,
    srcCE_pos hA ht0 hP0, srcCF_pos hA ht0 hK0, ?_⟩
  intro k hk N₁ _ h3N hN ν hνpos hν β hβ p₁ hp0 hp₁ q hq0 hq D S hS hp
  subst hS
  have hν0 : 0 ≤ ν := hνpos.le
  have hβ₁ : β₁ ≤ β := le_trans (le_max_right _ _) hβ
  have hβ2 : 2 ≤ β := le_trans (le_max_left _ _) hβ
  have hβ0 : 0 < β := by linarith
  have hβ1 : 1 ≤ β := by linarith
  have h3k : (1 : ℝ) ≤ 3 ^ k := one_le_pow₀ (by norm_num)
  have hbβ : β ≤ β * 3 ^ k := le_mul_of_one_le_right hβ0.le h3k
  have hb0 : 0 < β * 3 ^ k := by positivity
  obtain ⟨R0⟩ := D.ray
  have hcψ0 := D.cψ_pos
  have hr0 := D.r_pos
  have hδ₁ := D.fl_radius
  have hc := D.ray_margin
  have hHB := bgHyp_lv (k := k) T.m₁ hνpos.le hν
  have hC := D.core
  have hD := D.xi
  have hexp : Real.exp 1 ≤ β * 3 ^ k := le_trans hexpβ₁ (hβ₁.trans hbβ)
  have hℓ : 1 ≤ Real.log (β * 3 ^ k) := (Real.le_log_iff_exp_le hb0).2 hexp
  have hamp := (hA' (β * 3 ^ k) (hβ₁.trans hbβ) p₁ hp0 hp₁).2 P (Q * T.t) q hP0 hK0.le hq0.le
  have hBh := hBh_of_xi (N := 2) (Gp := lvTop N₁ T.m₁ k (rhoSep T.m₁)) hHB hνpos hC.small1
    hC.eps_pos hxi1
  have hN3 : 3 ^ 1 ∣ N₁ := by simpa using h3N
  obtain ⟨hV, hF⟩ := D.covers
  have hBh0 : (0 : ℝ) ≤ 1 + 2 / ν := by positivity
  have hη0 : 0 < q / β := div_pos hq0 hβ0
  -- the sign and the size of the amplitude
  have hid := sourceEta_scaled_identity 3 3 2 T.m₁ k 1 1 T.BG T.BG₂ T.κ T.t (lvR T.κ T.t (β * 3 ^ k) p₁) q β
    hβ0.ne'
  rw [← hQdef] at hid
  have hpot : β * (3 * c1 3 3 * (((3 : ℕ) : ℝ) ^ (1 + T.m₁)) ^ 3 *
      ‖energyBdScaled 3 3 2 (compWeight 3 1) k (Q * T.t) T.t (rho4 3 3 2 T.BG T.κ)‖ /
        lvR T.κ T.t (β * 3 ^ k) p₁ ^ 3) ≤ β * 3 ^ k * (P / lvR T.κ T.t (β * 3 ^ k) p₁ ^ 3) := by
    have h := beta_mul_potentialAmp_le (N := 2) (hatStepK (N₁ := N₁) k T.m₁ hk ν β p₁ T.δ)
      (by norm_num) le_rfl (compWeight_three_mem hk).2
      (le_trans (by norm_num) (compWeight_three_mem hk).1) hβ0.le hQ0.le ht0.le hρ4 hr0 (1 + T.m₁)
    rw [hatStepK_betaU, ← hPdef] at h
    exact h
  have hterm0 : 0 ≤ β * (3 * c1 3 3 * (((3 : ℕ) : ℝ) ^ (1 + T.m₁)) ^ 3 *
      ‖energyBdScaled 3 3 2 (compWeight 3 1) k (Q * T.t) T.t (rho4 3 3 2 T.BG T.κ)‖ /
        lvR T.κ T.t (β * 3 ^ k) p₁ ^ 3) := by
    have h3 : (0 : ℝ) ≤ 3 * c1 3 3 := by linarith
    positivity
  have hsrc0 : 0 ≤ q * (Q * T.t) / lvR T.κ T.t (β * 3 ^ k) p₁ := by positivity
  have hεnn : 0 ≤ β * prop33EpsEtaScaled 3 3 2 T.m₁ k 1 1 T.BG T.BG₂ T.κ T.t
      (lvR T.κ T.t (β * 3 ^ k) p₁) 0 0 (q / β) := by
    rw [hid]; linarith
  have hεle : β * prop33EpsEtaScaled 3 3 2 T.m₁ k 1 1 T.BG T.BG₂ T.κ T.t
        (lvR T.κ T.t (β * 3 ^ k) p₁) 0 0 (q / β) ≤
      P * (4 * A₁ / lvKappa T.κ T.t) ^ 3 * (Real.log (β * 3 ^ k)) ^ (3 * p) /
        Real.sqrt (β * 3 ^ k) +
      q * (4 * A₁ * (Q * T.t) / lvKappa T.κ T.t) * (Real.log (β * 3 ^ k)) ^ p /
        Real.sqrt (β * 3 ^ k) := by
    rw [hid]
    linarith
  have hε4 := sourceAmp_scale_four (A₁ := A₁) (κ := T.κ) (t := T.t) (P := P) (K := Q * T.t) (q := q) p
    hb0 (by linarith) hεle
  -- the direct terms
  obtain ⟨val, 𝒴, Tt, hval, hloc, hcont, hI⟩ := sourceDirectTerms_slice
    (hatStepK (N₁ := N₁) k T.m₁ hk ν β p₁ T.δ)
    (ρ := p₁) (εU := β * prop33EpsEtaScaled 3 3 2 T.m₁ k 1 1 T.BG T.BG₂ T.κ T.t
      (lvR T.κ T.t (β * 3 ^ k) p₁) 0 0 (q / β))
    (Rσ := 2) (R₁ := 2) (r := lvR T.κ T.t (β * 3 ^ k) p₁) (R := 2) (m₀ := 1) (κdec := T.κdec)
    (κ₀ := T.κ0) (Bh := 1 + 2 / ν) (δc := T.δc) (cψ := lvCpsi T.κ T.t (β * 3 ^ k))
    (jV := fun _ => k) (XV := fun z => LocalCover.cube 1 k (LocalCover.blockSite k z))
    (𝒦XV := fun z => LocalCover.fam 1 (LocalCover.blockSite k z))
    (X₁V := fun z => LocalCover.nbhdF 1 (LocalCover.blockSite k z))
    (jF := fun _ => k) (XF := fun s => LocalCover.cube 1 k s.1)
    (𝒦XF := fun s => LocalCover.fam 1 s.1) (X₁F := fun s => LocalCover.nbhdF 1 s.1)
    (hC := hC) (hconn := hatConn_lvTop) (hrow := rowInHat_lv hk h4 hN hν0 hν)
    (hκ₀ := hκ0) (hκdec := hκdec) (hκ := by exact_mod_cast hκ) (h1 := h1)
    (hR₁ := by norm_num) (hr := hr0) (hcψ := hcψ0.le) (hMX := hMX) (hdm := hdm) (hα := hα)
    (hsmX := hsmX) (hδ₁ := hδ₁) (ha₁ := one_pos) (H := hHB) (hc7 := hc7) (hR := le_rfl)
    (hRs := g1) (hsmall := g2) (hnum := g3) (hnum' := g4) (hsm := g5)
    (hcovV := fun z => (hV z).1) (hX₁V := fun z => (hV z).2.1)
    (hoptV := fun z => (hV z).2.2.1) (hΔV := fun z => (hV z).2.2.2.1)
    (hlogV := fun _ => hlog) (hZV := fun z => (hV z).2.2.2.2.1)
    (hmarV := fun z => (hV z).2.2.2.2.2.1)
    (hcovF := fun s => (hF s).1) (hX₁F := fun s => (hF s).2.1)
    (hoptF := fun s => (hF s).2.2.1) (hΔF := fun s => (hF s).2.2.2.1)
    (hlogF := fun _ => hlog) (hyF := fun s => (hF s).2.2.2.2)
    (hBh0 := hBh0) (hBh := hBh) (hZν := fun z => (hV z).2.2.2.2.2.2)
    (hN := hN3) (hp := hp) (η := q / β) (hη0 := hη0) (hRσ := by norm_num) (hc := hc)
    (hεb := by
      have hnβ : ‖(((hatStepK (N₁ := N₁) k T.m₁ hk ν β p₁ T.δ).β : ℝ) : ℂ)‖ = β := by
        rw [Complex.norm_real]; exact Real.norm_of_nonneg hβ0.le
      rw [hnβ, mul_comm]
      exact le_of_eq rfl)
  have hmem0 := mk_mem_physSΛEta (hatStepK (N₁ := N₁) k T.m₁ hk ν β p₁ T.δ) 1 ν T.t hη0.le hD
  obtain ⟨I, h𝒴, hT'⟩ := hI _ hmem0
  have hF' := directTermsFamilyOn_scaled (hatStepK (N₁ := N₁) k T.m₁ hk ν β p₁ T.δ) 1 (I := I)
    (a₁ := 1) (ν := ν) (eps := T.t) (β := β) (q := q)
    (by rw [h𝒴, hT']; exact hcont) (bgHyp_lv (k := k) T.m₁ hν0 hν) hβ1 hq
  refine ⟨val, 𝒴, Tt, I, h𝒴, hT', hF', ?_, hεnn, hε4, ?_⟩
  · intro g hg
    have hmem : ((⟨rawOf (hatStepK (N₁ := N₁) k T.m₁ hk ν β p₁ T.δ).D', rawOf_mem_rawSub _⟩, g) :
        physParam 2 (hatStepK (N₁ := N₁) k T.m₁ hk ν β p₁ T.δ)) ∈
        physVq (hatStepK (N₁ := N₁) k T.m₁ hk ν β p₁ T.δ) 1 ν T.t q :=
      ⟨(hatStepK_physV k T.m₁ hk hνpos.le hν β p₁ T.δ ht0).2.1 g (by
        have := hg.trans_le hq
        exact this), hg⟩
    refine ⟨hmem, ?_, h𝒴, hT'⟩
    rw [physInclScaled_apply]
    refine Prod.ext rfl ?_
    funext y i
    push_cast
    ring
  · intro Kc hKc
    have hR : (0 : ℝ) ≤ 2 := by norm_num
    refine ⟨fun y Φ => labelActFamilyOn_analytic _ 1 _ hF' hN3 hp0 hR hεnn T.κ0_ent hKc y Φ,
      fun e he u => labelActFamilyOn_eq_dtAct _ 1 _ hF' hN3 hp0 hR hεnn T.κ0_ent hKc he u, ?_⟩
    intro e he u hu y Φ
    exact labelActFamilyOn_H _ 1 _ hF' hN3 hp0 hR hεnn T.κ0_ent hKc he hu y Φ

open Classical in
/-- **Non-vacuity, one tower and one scale for both endpoints.**  For one `T : StepTower 0`
(`exists_stepTower`), at `k = 1`, `N₁ = 6`, `ν = 1/81`, `A₁ = 1`, `p = 0` and a common `β`, the
package `D` exists, and `expSourceChart_scale_fromTower` and `sourceFamilyRelative_scale_fromTower`
both apply to the same `T`, the same `D` and the same step `T.step 1 _ 6 (1/81) β 1`. -/
example : ∃ (T : StepTower 0) (β : ℝ), Nonempty (StepScaleData T 1 le_rfl 6 (1 / 81) β 1) ∧
    Nonempty ((T.step 1 le_rfl 6 (1 / 81) β 1).JointRep T.t (2 * 1)) ∧
    Nonempty (Finset (Set (CTorus 3 3 6 T.m₁ 2))) := by
  obtain ⟨T⟩ := exists_stepTower 0
  obtain ⟨βray, hβray, hscale⟩ := T.scale (A₁ := 1) one_pos 0
  obtain ⟨β₀, CE, CF, hβ₀, -, -, hsrc⟩ := sourceFamilyRelative_scale_fromTower T (A₁ := 1) one_pos 0
  have hβ : βray ≤ max βray β₀ := le_max_left _ _
  have hβ' : β₀ ≤ max βray β₀ := le_max_right _ _
  have hν : (1 / 81 : ℝ) * 3 ^ (2 * (1 + 1)) ≤ 1 := by norm_num
  have hp₁ : (1 : ℝ) ≤ pLog 1 0 (max βray β₀ * 3 ^ 1) := by simp [pLog]
  obtain ⟨D⟩ := hscale 1 le_rfl 6 (by norm_num) (by norm_num) (1 / 81) (by norm_num) hν
    (max βray β₀) hβ 1 one_pos hp₁
  have h1 := expSourceChart_scale_fromTower T 1 le_rfl 6 (1 / 81) (by norm_num) hν
    (max βray β₀) 1 one_pos D
  have h2 := hsrc 1 le_rfl 6 (by norm_num) (by norm_num) (1 / 81) (by norm_num) hν
    (max βray β₀) hβ' 1 one_pos hp₁ 1 one_pos le_rfl D _ rfl one_pos
  obtain ⟨Jr, -⟩ := h1
  obtain ⟨val, 𝒴, -⟩ := h2
  exact ⟨T, max βray β₀, ⟨D⟩, ⟨Jr⟩, ⟨𝒴⟩⟩

end Balaban.Inhabited
