/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.ObsMarksFromTower
public import Balaban.Fluctuation.StepComplexThm31
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Theorem 3.1 (b) for the zero-class step at the shared tower

The observable marks record of `obsMarks_zeroClass_family_of_ray` is fed to the consumer
`thm31bC_of_input_M0`.  The result is the localized expansion of the observable term at the output
rate `(3/2) κ_dec`, with prefactor `obsW^4 b^{-1/2-s} + obsW^2 b^{-1}` (`b = β 3^k`).

* `stepTower_outRate_le`: the rate arithmetic `(3/2) κ_dec ≤ min (2 κ_dec) κ' - κ₀ - 1`
  (equality for the first factor).
* `thm31b_zeroClass_fromTower_of_ray`: the expansion.
* `obsPrefactor_small`, `obsPrefactor_small_scale`: the prefactor tends to `0`, uniformly in `k`.
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation
  Balaban.Localization Balaban.Localization.LevelPair Balaban.Localization.I5Inhabited
  Balaban.Polymer Balaban.SmallField.Def6 Balaban.Inhabited.LevelStep Filter Topology
  MeasureTheory Metric Finset Set

/-- The prefactor of Theorem 3.1 (b) for the observable term at the scale `b`. -/
noncomputable def obsPrefactor (p : ℕ) (s b : ℝ) : ℝ :=
  obsW p b ^ 4 * b ^ (-(1 / 2 : ℝ) - s) + obsW p b ^ 2 / b

/-- The rate arithmetic: with `κ' = (3/2) κ_dec + κ₀ + 1` and `κ_dec ≥ 3 κ₀ + 3`,
`min (2 κ_dec) κ' - κ₀ - 1 = (3/2) κ_dec`. -/
theorem stepTower_outRate_eq {κmin : ℝ} (T : StepTower κmin) :
    min (2 * T.κdec) T.κ' - T.κ0 - 1 = 3 / 2 * T.κdec := by
  have h1 := T.κ'_eq
  have h2 := T.κdec_lower
  have h3 := T.κ0_nonneg
  have : T.κ' ≤ 2 * T.κdec := by linarith
  rw [min_eq_right this]; linarith

theorem stepTower_outRate_le {κmin : ℝ} (T : StepTower κmin) :
    3 / 2 * T.κdec ≤ min (2 * T.κdec) T.κ' - T.κ0 - 1 :=
  (stepTower_outRate_eq T).ge

theorem obsPrefactor_nonneg (p : ℕ) (s : ℝ) {b : ℝ} (hb : 1 ≤ b) : 0 ≤ obsPrefactor p s b := by
  have hl : 0 ≤ Real.log b := Real.log_nonneg hb
  have hW : 0 ≤ obsW p b := by unfold obsW; positivity
  have hb0 : 0 < b := by linarith
  unfold obsPrefactor; positivity

/-- **Theorem 3.1 (b)** for the zero-class step at every scale of one tower, at the output rate
`(3/2) κ_dec`, conditional on ray holomorphy of the direct terms. -/
theorem thm31b_zeroClass_fromTower_of_ray {κmin : ℝ} (T : StepTower κmin)
    {A₁ : ℝ} (hA : 0 < A₁) (p : ℕ) {CR s : ℝ}
    (hCR : 0 < CR) (hs0 : 0 < s) (hs : s < 1 / 2)
    (hray : ∀ (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁], 3 ∣ N₁ → 5 < N₁ →
      ∀ ν : ℝ, 0 < ν → ν * 3 ^ (2 * (k + 1)) ≤ 1 → ∀ β : ℝ, 1 ≤ β →
      ∀ p₁ : ℝ, 0 < p₁ → StepScaleData T k hk N₁ ν β p₁ →
      ∀ S : StepSetting 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁), S = T.step k hk N₁ ν β p₁ →
      ∀ hp : 0 < S.p₁,
      ∃ (val : ((S.U × Fin 2 → ℂ) × (S.U × Fin 2 → ℂ)) → ((S.U × Fin 2 → ℂ) × (S.U × Fin 2 → ℂ)) →
          ℂ → (RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2 ×
            (CTorus 3 3 N₁ T.m₁ (k + 1) → Fin 2 → ℂ)) → ℂ)
        (𝒴 : Finset (Set (CTorus 3 3 N₁ T.m₁ (k + 1))))
        (Tt : Set (CTorus 3 3 N₁ T.m₁ (k + 1)) → ((S.U × Fin 2 → ℂ) × (S.U × Fin 2 → ℂ)) →
          ((S.U × Fin 2 → ℂ) × (S.U × Fin 2 → ℂ)) → ℂ →
          (RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2 ×
            (CTorus 3 3 N₁ T.m₁ (k + 1) → Fin 2 → ℂ)) → ℂ),
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
        DiagCont (fun ψ : S.U × Fin 2 → ℂ => (ψ, ψ))
          (physXW S (lvCpsi T.κ T.t (β * 3 ^ k)) 2 2 (lvR T.κ T.t (β * 3 ^ k) p₁))
          (physSΛEta S S.a₁ S.ν T.t (1 / S.β)) 2 𝒴 Tt ∧
        (∀ Θ ∈ physSΛEta S S.a₁ S.ν T.t (1 / S.β),
          ∃ I : DirectTerms S 1 hp (fun ψ => (ψ, ψ)) p₁ 2
              (S.β * prop33EpsEtaScaled 3 3 2 T.m₁ k 1 S.a₁ T.BG T.BG₂ T.κ T.t
                (lvR T.κ T.t (β * 3 ^ k) p₁) 0 0 (1 / S.β)) (2 * T.κdec - 1) Θ
              (physSΛEta S S.a₁ S.ν T.t (1 / S.β))
              (physXW S (lvCpsi T.κ T.t (β * 3 ^ k)) 2 2 (lvR T.κ T.t (β * 3 ^ k) p₁)) val
              (physAgΘ S) (AgFDirPair S),
            I.𝒴 = 𝒴 ∧ I.T = Tt) ∧
        (rawOf S.D', (0 : CTorus 3 3 N₁ T.m₁ (k + 1) → Fin 2 → ℂ)) ∈
          physSΛEta S S.a₁ S.ν T.t (1 / S.β) ∧
        (∀ g : Fld 3 3 N₁ T.m₁ (k + 1) 2, ∑ x, ∑ i, ‖g x i‖ < 1 →
          (rawOf S.D', fun y i => g y i / (S.β : ℂ)) ∈ physSΛEta S S.a₁ S.ν T.t (1 / S.β)) ∧
        (∀ Y ∈ 𝒴, ∀ Θ ∈ physSΛEta S S.a₁ S.ν T.t (1 / S.β),
          ∀ ψ ∈ hatDisk S.U 2 p₁,
            DifferentiableOn ℂ (fun z : ℂ => Tt Y (z • ψ, z • ψ) (z • ψ, z • ψ) 1 Θ)
              (ball (0 : ℂ) (3 / 2)))) :
  ∃ β₀ C : ℝ, 2 ≤ β₀ ∧ 0 ≤ C ∧
  ∀ (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁], 3 ∣ N₁ → 5 < N₁ →
  ∀ ν : ℝ, 0 < ν → ν * 3 ^ (2 * (k + 1)) ≤ 1 →
  ∀ β : ℝ, β₀ ≤ β → ∀ (p₁ : ℝ), 0 < p₁ →
  p₁ ≤ pLog A₁ p (β * 3 ^ k) →
  StepScaleData T k hk N₁ ν β p₁ →
  ∀ g : Fld 3 3 N₁ T.m₁ (k + 1) 2,
    g ∈ l1Ball 3 3 N₁ T.m₁ (k + 1) 2 →
  ∀ (y : CTorus 3 3 N₁ T.m₁ (k + 1)) (i : Fin 2),
    ∃ E : Finset (CubeB (d := 3) (L := 3) (N₁ := N₁) (m₁ := T.m₁) (K := k + 1) 1 (k + 1)
        Set.univ) → ℂ,
      (T.step k hk N₁ ν β p₁).M0C (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) g y i =
        (((T.step k hk N₁ ν β p₁).betaU ^ (1 / 2 : ℝ) : ℝ) : ℂ) * ∑ T', E T' ∧
      (∀ T', rootCube (m₀ := 1) (blockIndex y) ∉ T' → E T' = 0) ∧
      ∀ T', ‖E T'‖ ≤ C * obsPrefactor p s (β * 3 ^ k) * Real.exp (-(3 / 2 * T.κdec) * dExt T') := by
  obtain ⟨β₀, C₁, C₂, hβ₀, hC₁, hC₂, hfam⟩ := obsMarks_zeroClass_family_of_ray T hA p hCR hs0 hs hray
  refine ⟨β₀, max C₁ C₂, hβ₀, le_max_of_le_left hC₁, ?_⟩
  intro k hk N₁ _ h3 h5 ν hν hνk β hβ p₁ hp hp₁ hsc g hg y i
  obtain ⟨I, -, hκ0, hκH, hκ', hκh, -, hB1, hB2⟩ := hfam k hk N₁ h3 h5 ν hν hνk β hβ p₁ hp hp₁ hsc g hg y i
  have hrate : 3 / 2 * T.κdec ≤ min I.κh I.κ' - I.κ0 - 1 := by
    have := stepTower_outRate_le T
    rw [hκh, hκ', hκ0]
    exact this
  obtain ⟨E, h1, h2, h3'⟩ := thm31bC_of_input_M0 _ _ _ g y i I hrate
  refine ⟨E, h1, h2, fun T' => (h3' T').trans ?_⟩
  have hb : 1 ≤ β * 3 ^ k := by
    have : (1 : ℝ) ≤ 3 ^ k := one_le_pow₀ (by norm_num)
    nlinarith
  have hl : 0 ≤ Real.log (β * 3 ^ k) := Real.log_nonneg hb
  have hW : 0 ≤ obsW p (β * 3 ^ k) := by unfold obsW; positivity
  have hb0 : 0 < β * 3 ^ k := by linarith
  have hP1 : 0 ≤ obsW p (β * 3 ^ k) ^ 4 * (β * 3 ^ k) ^ (-(1 / 2 : ℝ) - s) := by positivity
  have hP2 : 0 ≤ obsW p (β * 3 ^ k) ^ 2 / (β * 3 ^ k) := by positivity
  have hsum : I.B1 + I.B2 ≤ max C₁ C₂ * obsPrefactor p s (β * 3 ^ k) := by
    unfold obsPrefactor
    have a1 : C₁ * obsW p (β * 3 ^ k) ^ 4 * (β * 3 ^ k) ^ (-(1 / 2 : ℝ) - s) ≤
        max C₁ C₂ * (obsW p (β * 3 ^ k) ^ 4 * (β * 3 ^ k) ^ (-(1 / 2 : ℝ) - s)) := by
      rw [mul_assoc]; exact mul_le_mul_of_nonneg_right (le_max_left _ _) hP1
    have a2 : C₂ * obsW p (β * 3 ^ k) ^ 2 / (β * 3 ^ k) ≤
        max C₁ C₂ * (obsW p (β * 3 ^ k) ^ 2 / (β * 3 ^ k)) := by
      rw [mul_div_assoc]; exact mul_le_mul_of_nonneg_right (le_max_right _ _) hP2
    nlinarith [hB1, hB2]
  exact mul_le_mul_of_nonneg_right hsum (Real.exp_nonneg _)

/-- Powers of the logarithm times a negative power tend to zero. -/
theorem log_rpow_mul_rpow_neg_tendsto (a : ℝ) {r : ℝ} (hr : 0 < r) :
    Tendsto (fun b : ℝ => Real.log b ^ a * b ^ (-r)) atTop (𝓝 0) := by
  have h := (isLittleO_log_rpow_rpow_atTop a hr).tendsto_div_nhds_zero
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with b hb
  rw [Real.rpow_neg hb.le, div_eq_mul_inv]

/-- The prefactor tends to `0` as the scale `b → ∞`. -/
theorem obsPrefactor_tendsto (p : ℕ) {s : ℝ} (hs0 : 0 < s) :
    Tendsto (fun b : ℝ => obsPrefactor p s b) atTop (𝓝 0) := by
  have t1 := log_rpow_mul_rpow_neg_tendsto (4 * (p : ℝ)) (r := 1 / 2 + s) (by linarith)
  have t2 := log_rpow_mul_rpow_neg_tendsto (2 * (p : ℝ)) (r := 1) one_pos
  have := t1.add t2
  rw [add_zero] at this
  refine this.congr' ?_
  filter_upwards [eventually_gt_atTop 1] with b hb
  have hl : 0 ≤ Real.log b := Real.log_nonneg hb.le
  unfold obsPrefactor obsW
  rw [← Real.rpow_natCast (Real.log b ^ (p : ℝ)) 4, ← Real.rpow_mul hl,
    ← Real.rpow_natCast (Real.log b ^ (p : ℝ)) 2, ← Real.rpow_mul hl,
    show -(1 / 2 : ℝ) - s = -(1 / 2 + s) by ring, Real.rpow_neg (by linarith : (0 : ℝ) ≤ b),
    Real.rpow_neg (by linarith : (0 : ℝ) ≤ b), Real.rpow_one, div_eq_mul_inv, div_eq_mul_inv]
  push_cast
  simp only [mul_comm (p : ℝ)]

/-- Smallness, uniform in the scale index: for every `ε > 0` there is `β₁` with
`obsPrefactor ≤ ε` at every `b = β 3^k`, `β ≥ β₁`, `k` arbitrary. -/
theorem obsPrefactor_small_scale (p : ℕ) {s : ℝ} (hs0 : 0 < s) {ε : ℝ} (hε : 0 < ε) :
    ∃ β₁ : ℝ, 1 ≤ β₁ ∧ ∀ (k : ℕ) (β : ℝ), β₁ ≤ β → obsPrefactor p s (β * 3 ^ k) ≤ ε := by
  have h := (obsPrefactor_tendsto p hs0).eventually (Iic_mem_nhds hε)
  obtain ⟨B, hB⟩ := eventually_atTop.1 h
  refine ⟨max B 1, le_max_right _ _, fun k β hβ => hB _ ?_⟩
  have : (1 : ℝ) ≤ 3 ^ k := one_le_pow₀ (by norm_num)
  have hβ1 : 0 ≤ β := by linarith [le_max_right B 1]
  nlinarith [le_max_left B 1]

end Balaban.Inhabited
