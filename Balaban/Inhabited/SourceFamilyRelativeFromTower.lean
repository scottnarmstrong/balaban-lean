/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.StepTowerGProducers
public import Balaban.Inhabited.StepTowerOfG
public import Balaban.Inhabited.StepTowerScale
public import Balaban.Inhabited.ExpSourceChartFromTower
public import Balaban.Fluctuation.SourceAmpNonneg
public import Balaban.Inhabited.SourceDirectTermsFromTower
public import Balaban.Inhabited.PhysAmpFacts
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The source direct terms over the relative chart at every scale of a tower

`sourceFamilyRelative_scale_fromTowerG_rho` is the statement for the general tower
`T : StepTowerG d L N κmin` on the carrier `physVqRho … ρ q`; it carries the proof, and the fixed
`sourceFamilyRelative_scale_fromTower_rho` is its corollary at `T.toG`.

`sourceFamilyRelative_scale_fromTower` restates `sourceFamilyRelative_scale_nonneg` for one tower
`T : StepTower κmin` and its per-scale package `D : StepScaleData T …`: the landed proof is re-run
with its tower prologue replaced by the fields of `T` and `D`.  The only threshold is the one of
the amplitude estimate `sourceAmp_scale`, chosen after `T`.

`sourceFamilyRelative_scale_fromTower_rho` is the same statement on the carrier `physVqRho … ρ q` of
radius `ρ` (`0 < q ≤ ρ`, `max 1 ρ ≤ β`), with the direct terms from
`sourceDirectTerms_scale_fromTower_rho`; `sourceFamilyRelative_scale_fromTower` is its case `ρ = 1`.

Source activity with common labels and the chart/determinant joint endpoint are not in this file.
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation
  Balaban.Localization Balaban.Localization.LevelPair Balaban.Localization.I5Inhabited
  Balaban.Polymer Balaban.SmallField.Def6 Balaban.Inhabited.LevelStep Filter Topology Metric

open Classical in
/-- **The source direct terms as a family over the relative chart of radius `ρ`, at every scale of
the general tower `T`.**  The conclusion of `sourceFamilyRelative_scale_fromTower` with the carrier
`physVqRho … ρ q`, for `0 < q ≤ ρ` and `max 1 ρ ≤ β`; the threshold `β₀` and the amplitude constants
`C_E`, `C_F` do not depend on `ρ`, and the amplitude bound is the one with `q C_F`. -/
theorem sourceFamilyRelative_scale_fromTowerG_rho {d L N : ℕ} [NeZero L] {κmin : ℝ}
    (T : StepTowerG d L N κmin) {A₁ : ℝ}
    (hA : 0 < A₁) (p : ℕ) :
    ∃ (β₀ CE CF : ℝ), 2 ≤ β₀ ∧ 0 < CE ∧ 0 < CF ∧
      ∀ (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁] (hLN : L ^ T.m₀ ∣ N₁), 5 < N₁ →
      ∀ ν : ℝ, 0 < ν → ν * (L : ℝ) ^ (2 * (k + 1)) ≤ 1 → ∀ β : ℝ, β₀ ≤ β → ∀ ρ : ℝ, max 1 ρ ≤ β →
      ∀ p₁ : ℝ, ∀ hp0 : 0 < p₁, p₁ ≤ pLog A₁ p (β * (L : ℝ) ^ (k * (d - 2))) → ∀ q : ℝ, 0 < q → q ≤ ρ →
      StepScaleDataG T k hk N₁ ν β p₁ →
      ∀ S : StepSetting d L N₁ T.m₁ k N (rhoSepG d L T.m₁),
        S = T.step k hk N₁ ν β p₁ → ∀ hp : 0 < S.p₁,
      ∃ (val : ((S.U × Fin N → ℂ) × (S.U × Fin N → ℂ)) → ((S.U × Fin N → ℂ) × (S.U × Fin N → ℂ)) →
            ℂ → (RawData d L (N₁ * L ^ T.m₁) (k + 1) N × (CTorus d L N₁ T.m₁ (k + 1) → Fin N → ℂ)) → ℂ)
          (𝒴 : Finset (Set (CTorus d L N₁ T.m₁ (k + 1))))
          (Tt : Set (CTorus d L N₁ T.m₁ (k + 1)) → ((S.U × Fin N → ℂ) × (S.U × Fin N → ℂ)) →
            ((S.U × Fin N → ℂ) × (S.U × Fin N → ℂ)) → ℂ →
            (RawData d L (N₁ * L ^ T.m₁) (k + 1) N × (CTorus d L N₁ T.m₁ (k + 1) → Fin N → ℂ)) → ℂ)
          (I : DirectTerms S T.m₀ hp (fun ψ => (ψ, ψ)) p₁ 2
                (S.β * prop33EpsEtaScaled d L N T.m₁ k T.m₀ S.a₁ T.BG T.BG₂ T.κ T.t
                  (lvRG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2))) p₁) 0 0 (q / S.β)) (2 * T.κdec - 1)
                (rawOf S.D', (0 : CTorus d L N₁ T.m₁ (k + 1) → Fin N → ℂ))
                (physSΛEta S S.a₁ S.ν T.t (q / S.β))
                (physXW S (lvCpsiG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2)))) 2 2 (lvRG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2))) p₁)) val (physAgΘ S)
                (AgFDirPair S)),
          I.𝒴 = 𝒴 ∧ I.T = Tt ∧
          ∃ hF : DirectTermsFamilyOn S T.m₀ (physInclScaled N S (((1 / S.β : ℝ)) : ℂ)) I
              (physVqRho S 1 ν T.t ρ q),
            (∀ g : Fld d L N₁ T.m₁ (k + 1) N, ∑ x, ∑ i, ‖g x i‖ < q →
              ∃ hg : (⟨rawOf S.D', rawOf_mem_rawSub _⟩, g) ∈ physVqRho S 1 ν T.t ρ q,
                physInclScaled N S (((1 / S.β : ℝ)) : ℂ) (⟨rawOf S.D', rawOf_mem_rawSub _⟩, g) =
                  (rawOf S.D', fun y i => g y i / (S.β : ℂ)) ∧
                (I.atThetaOn S T.m₀ _ hF hg).𝒴 = 𝒴 ∧ (I.atThetaOn S T.m₀ _ hF hg).T = Tt) ∧
            ∃ hεU : 0 ≤ S.β * prop33EpsEtaScaled d L N T.m₁ k T.m₀ S.a₁ T.BG T.BG₂ T.κ T.t
                  (lvRG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2))) p₁) 0 0 (q / S.β),
              4 * (S.β * prop33EpsEtaScaled d L N T.m₁ k T.m₀ S.a₁ T.BG T.BG₂ T.κ T.t
                  (lvRG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2))) p₁) 0 0 (q / S.β)) ≤
                CE * (Real.log (β * (L : ℝ) ^ (k * (d - 2)))) ^ (3 * p) / Real.sqrt (β * (L : ℝ) ^ (k * (d - 2))) +
                  q * CF * (Real.log (β * (L : ℝ) ^ (k * (d - 2)))) ^ p / Real.sqrt (β * (L : ℝ) ^ (k * (d - 2))) ∧
              ∀ {Kc : ℝ} (hKc : K0 d L T.κ0 ≤ Kc),
              (∀ (y : {Y // Y ∈ I.𝒴}) (Φ : ∀ b, (S.blockSplit T.m₀ hp).Ωb b),
                AnalyticOnNhd ℂ (fun r : physParam N S × ℂ =>
                  (labelActFamilyOn S T.m₀ (physInclScaled N S (((1 / S.β : ℝ)) : ℂ)) I hF
                    hLN hp0 (by norm_num) hεU
                    T.κ0_ent hKc r.1 r.2).H y Φ)
                  (physVqRho S 1 ν T.t ρ q ×ˢ ball (0 : ℂ) 2)) ∧
              (∀ e (he : e ∈ physVqRho S 1 ν T.t ρ q) (u : ℂ),
                labelActFamilyOn S T.m₀ (physInclScaled N S (((1 / S.β : ℝ)) : ℂ)) I hF
                    hLN hp0 (by norm_num) hεU
                    T.κ0_ent hKc e u =
                  dtAct S T.m₀ (I.atThetaOn S T.m₀ _ hF he)
                    hLN hp0 (by norm_num) hεU
                    T.κ0_ent hKc u) ∧
              (∀ e ∈ physVqRho S 1 ν T.t ρ q, ∀ u : ℂ, ‖u‖ < 2 →
                ∀ (y : {Y // Y ∈ I.𝒴}) (Φ : ∀ b, (S.blockSplit T.m₀ hp).Ωb b),
                (labelActFamilyOn S T.m₀ (physInclScaled N S (((1 / S.β : ℝ)) : ℂ)) I hF
                    hLN hp0 (by norm_num) hεU
                    T.κ0_ent hKc e u).H y Φ =
                  I.T y.1 (S.hatOf T.m₀ p₁ hp Φ, S.hatOf T.m₀ p₁ hp Φ)
                    (S.hatOf T.m₀ p₁ hp Φ, S.hatOf T.m₀ p₁ hp Φ) u
                    (physInclScaled N S (((1 / S.β : ℝ)) : ℂ) e)) := by
  classical
  have hd := T.hd
  have hL := T.hL
  have hN2 := T.hN
  have hd0 : 0 < d := by omega
  have ht0 := T.t_pos
  have hρ4 := T.rho_nonneg
  have hB0 := T.fam_nonneg
  have hc1 := one_le_c1 d L
  have hent := aEnt_nonneg d L
  obtain ⟨Q, hQdef⟩ : ∃ Q : ℝ, Q = cK2' d L N (famConst d L T.BG₂ T.κ) := ⟨_, rfl⟩
  have hQ0 : 0 < Q := by rw [hQdef]; exact cK2'_pos_general hB0
  obtain ⟨P, hPdef⟩ : ∃ P : ℝ, P = 3 * c1 d L * (((L : ℕ) : ℝ) ^ (T.m₀ + T.m₁)) ^ d *
    ((L : ℝ) ^ d * (((N : ℝ) / 2) * (2 * (1 + Q) ^ 2 +
      ((d : ℝ) + 1 + rho4 d L N T.BG T.κ) * Q ^ 2) * T.t ^ 2)) := ⟨_, rfl⟩
  have hP0 : 0 ≤ P := by
    rw [hPdef]; positivity
  have hK0 : 0 < Q * T.t := mul_pos hQ0 ht0
  have hκ1 := lvKappaG_pos hd0 hL (by omega : 1 ≤ N) T.κ ht0
  obtain ⟨β₁, hexpβ₁, hA'⟩ := sourceAmp_scale_general (d := d) (L := L) (N := N) hd0 hL
    (by omega) (A₁ := A₁) (κ := T.κ) (t := T.t) hA p ht0
  refine ⟨max 2 β₁, 4 * (P * (4 * A₁ / lvKappaG d L N T.κ T.t) ^ 3 + 1),
    16 * A₁ * (Q * T.t) / lvKappaG d L N T.κ T.t, le_max_left _ _, by positivity,
    by positivity, ?_⟩
  intro k hk N₁ _ hLN hN ν hνpos hν β hβ ρ hβρ p₁ hp0 hp₁ q hq0 hq D S hS hp
  subst hS
  have hν0 : 0 ≤ ν := hνpos.le
  have hβ₁ : β₁ ≤ β := le_trans (le_max_right _ _) hβ
  have hβ2 : 2 ≤ β := le_trans (le_max_left _ _) hβ
  have hβ0 : 0 < β := by linarith
  have hβ1 : 1 ≤ β := by linarith
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast (by omega : 1 ≤ L)
  have h3k : (1 : ℝ) ≤ (L : ℝ) ^ (k * (d - 2)) := one_le_pow₀ hL1
  have hbβ : β ≤ β * (L : ℝ) ^ (k * (d - 2)) := le_mul_of_one_le_right hβ0.le h3k
  have hb0 : 0 < β * (L : ℝ) ^ (k * (d - 2)) := by positivity
  have hr0 := D.r_pos
  have hexp : Real.exp 1 ≤ β * (L : ℝ) ^ (k * (d - 2)) := le_trans hexpβ₁ (hβ₁.trans hbβ)
  have hℓ : 1 ≤ Real.log (β * (L : ℝ) ^ (k * (d - 2))) :=
    (Real.le_log_iff_exp_le hb0).2 hexp
  have hamp := (hA' (β * (L : ℝ) ^ (k * (d - 2))) (hβ₁.trans hbβ) p₁ hp0 hp₁).2 P (Q * T.t) q hP0
    hK0.le hq0.le
  have hη0 : 0 < q / β := div_pos hq0 hβ0
  have hbU : (T.step k hk N₁ ν β p₁).betaU = β * (L : ℝ) ^ (k * (d - 2)) :=
    hatStepKG_betaU (d := d) (L := L) (N₁ := N₁) hN2 (by omega) k T.m₁ (rhoSepG d L T.m₁) hk ν β
      p₁ T.δ
  obtain ⟨hid, hpot, hterm0, hεle', hεpos⟩ := physAmp_facts (T.step k hk N₁ ν β p₁)
    (by omega) hL T.m₀ (compWeight_one_mem hL hk) rfl hβ0 rfl hbU hQ0 ht0 hρ4 hr0 hq0 hQdef hPdef
    (εU := β * prop33EpsEtaScaled d L N T.m₁ k T.m₀ 1 T.BG T.BG₂ T.κ T.t
      (lvRG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2))) p₁) 0 0 (q / β)) rfl
  have hεnn := hεpos.le
  have hεle := hεle' _ hamp
  have hε4 := sourceAmp_scale_four_general (A₁ := A₁) (κ₁ := lvKappaG d L N T.κ T.t) (P := P)
    (K := Q * T.t) (q := q) p hb0 (by linarith) rfl rfl hεle
  -- the direct terms and the family
  have hρ : 0 < ρ := lt_of_lt_of_le hq0 hq
  obtain ⟨val, 𝒴, Tt, -, -, hcont, hI, hmem0, -, -⟩ :=
    sourceDirectTerms_scale_fromTowerG_ray_rho T k hk N₁ hLN hN ν hνpos hν β ρ hρ hβρ p₁ q hq0 hq
      D (T.step k hk N₁ ν β p₁) rfl hp
  obtain ⟨I, h𝒴, hT'⟩ := hI _ hmem0
  have hHB := bgHyp_lvG (k := k) T.hd T.hL (bgR0_le_rhoSepG T.m₁ T.hd T.hL) hν0 hν
  have hF' := directTermsFamilyOn_scaled_rho (T.step k hk N₁ ν β p₁) T.m₀ (I := I)
    (a₁ := 1) (ν := ν) (eps := T.t) (β := β) (q := q) (ρ := ρ)
    (by rw [h𝒴, hT']; exact hcont) hHB hβρ hq
  refine ⟨val, 𝒴, Tt, I, h𝒴, hT', hF', ?_, hεnn, hε4, ?_⟩
  · intro g hg
    have hmem : ((⟨rawOf (T.step k hk N₁ ν β p₁).D', rawOf_mem_rawSub _⟩, g) :
        physParam N (T.step k hk N₁ ν β p₁)) ∈
        physVqRho (T.step k hk N₁ ν β p₁) 1 ν T.t ρ q :=
      ⟨⟨⟨_, D.xi, rfl⟩, hg.trans_le hq⟩, hg⟩
    refine ⟨hmem, ?_, h𝒴, hT'⟩
    rw [physInclScaled_apply]
    refine Prod.ext rfl ?_
    funext y i
    push_cast
    ring
  · intro Kc hKc
    have hR : (0 : ℝ) ≤ 2 := by norm_num
    refine ⟨fun y Φ => labelActFamilyOn_analytic _ T.m₀ _ hF' hLN hp0 hR hεnn T.κ0_ent hKc y Φ,
      fun e he u => labelActFamilyOn_eq_dtAct _ T.m₀ _ hF' hLN hp0 hR hεnn T.κ0_ent hKc he u, ?_⟩
    intro e he u hu y Φ
    exact labelActFamilyOn_H _ T.m₀ _ hF' hLN hp0 hR hεnn T.κ0_ent hKc he hu y Φ

open Classical in
/-- **The source direct terms as a family over the relative chart of radius `ρ`, at every scale of
the tower `T`.**  The conclusion of `sourceFamilyRelative_scale_fromTower` with the carrier
`physVqRho … ρ q`, for `0 < q ≤ ρ` and `max 1 ρ ≤ β`; the threshold `β₀` and the amplitude constants
`C_E`, `C_F` do not depend on `ρ`, and the amplitude bound is the one with `q C_F`. -/
theorem sourceFamilyRelative_scale_fromTower_rho {κmin : ℝ} (T : StepTower κmin) {A₁ : ℝ}
    (hA : 0 < A₁) (p : ℕ) :
    ∃ (β₀ CE CF : ℝ), 2 ≤ β₀ ∧ 0 < CE ∧ 0 < CF ∧
      ∀ (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁] (h3N : 3 ∣ N₁), 5 < N₁ →
      ∀ ν : ℝ, 0 < ν → ν * 3 ^ (2 * (k + 1)) ≤ 1 → ∀ β : ℝ, β₀ ≤ β → ∀ ρ : ℝ, max 1 ρ ≤ β →
      ∀ p₁ : ℝ, ∀ hp0 : 0 < p₁, p₁ ≤ pLog A₁ p (β * 3 ^ k) → ∀ q : ℝ, 0 < q → q ≤ ρ →
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
              (physVqRho S 1 ν T.t ρ q),
            (∀ g : Fld 3 3 N₁ T.m₁ (k + 1) 2, ∑ x, ∑ i, ‖g x i‖ < q →
              ∃ hg : (⟨rawOf S.D', rawOf_mem_rawSub _⟩, g) ∈ physVqRho S 1 ν T.t ρ q,
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
                  (physVqRho S 1 ν T.t ρ q ×ˢ ball (0 : ℂ) 2)) ∧
              (∀ e (he : e ∈ physVqRho S 1 ν T.t ρ q) (u : ℂ),
                labelActFamilyOn S 1 (physInclScaled 2 S (((1 / S.β : ℝ)) : ℂ)) I hF
                    (show 3 ^ 1 ∣ N₁ by simpa using h3N) hp0 (by norm_num) hεU
                    T.κ0_ent hKc e u =
                  dtAct S 1 (I.atThetaOn S 1 _ hF he)
                    (show 3 ^ 1 ∣ N₁ by simpa using h3N) hp0 (by norm_num) hεU
                    T.κ0_ent hKc u) ∧
              (∀ e ∈ physVqRho S 1 ν T.t ρ q, ∀ u : ℂ, ‖u‖ < 2 →
                ∀ (y : {Y // Y ∈ I.𝒴}) (Φ : ∀ b, (S.blockSplit 1 hp).Ωb b),
                (labelActFamilyOn S 1 (physInclScaled 2 S (((1 / S.β : ℝ)) : ℂ)) I hF
                    (show 3 ^ 1 ∣ N₁ by simpa using h3N) hp0 (by norm_num) hεU
                    T.κ0_ent hKc e u).H y Φ =
                  I.T y.1 (S.hatOf 1 p₁ hp Φ, S.hatOf 1 p₁ hp Φ)
                    (S.hatOf 1 p₁ hp Φ, S.hatOf 1 p₁ hp Φ) u
                    (physInclScaled 2 S (((1 / S.β : ℝ)) : ℂ) e)) := by
  obtain ⟨β₀, CE, CF, hβ₀, hCE, hCF, H⟩ := sourceFamilyRelative_scale_fromTowerG_rho T.toG hA p
  refine ⟨β₀, CE, CF, hβ₀, hCE, hCF, ?_⟩
  intro k hk N₁ _ h3N hN ν hνpos hν β hβ ρ hβρ p₁ hp0 hp₁ q hq0 hq D S hS hp
  subst hS
  have e : (((3 : ℕ) : ℝ)) ^ (k * (3 - 2)) = 3 ^ k := by norm_num
  have hp' : 0 < (T.toG.step k hk N₁ ν β p₁).p₁ := hp
  have G := H k hk N₁ (by simpa using h3N) hN ν hνpos (by simpa using hν) β hβ ρ hβρ p₁ hp0
    (by rw [e]; exact hp₁) q hq0 hq (StepTower.scaleDataG_of_fixed T D)
    (T.toG.step k hk N₁ ν β p₁) rfl hp'
  unfold StepTowerG.step at G
  revert G
  generalize hb : β * ((3 : ℕ) : ℝ) ^ (k * (3 - 2)) = b
  generalize hϱ : rhoSepG 3 3 T.toG.m₁ = ϱ
  have hϱ' : ϱ = rhoSep T.m₁ := hϱ.symm.trans (rhoSepG_three _)
  have hb' : b = β * 3 ^ k := hb.symm.trans (by rw [e])
  subst hϱ' hb'
  intro G
  exact G

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
  obtain ⟨β₀, CE, CF, hβ₀, hCE, hCF, h⟩ := sourceFamilyRelative_scale_fromTower_rho T hA p
  refine ⟨β₀, CE, CF, hβ₀, hCE, hCF, ?_⟩
  intro k hk N₁ _ h3N hN ν hν hν' β hβ p₁ hp0 hp₁ q hq0 hq D S hS hp
  exact h k hk N₁ h3N hN ν hν hν' β hβ 1 (by rw [max_self]; linarith) p₁ hp0 hp₁ q hq0 hq D S hS hp

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
