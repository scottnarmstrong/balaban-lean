/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.Thm31bPolymerSupport
public import Balaban.Inhabited.ObsOnCommonWitness
public import Balaban.Inhabited.Thm31bFromTower

/-!
# Theorem 3.1 (b) on the common witness, with coefficients on polymer sets

The coefficients of the expansion of the observable term at the tower are `obsCoeff I` for the record
`I` of `obsMarks_zeroClass_at_of_ray_ksupp`, whose kernel is supported on polymer labels.  By
`ObsMarks.obsCoeff_eq_zero_of_not_isPolyDom_of_kernel_supp` they vanish unless `sitesOf T` is a
polymer domain.

* `thm31b_zeroClass_at_of_ray_supp`: one scale.
* `thm31b_onCommonWitness_fromTower_supp`: the common-witness statement with this clause.

The clauses of Theorem 3.1 (b) that remain open are those listed in
`Balaban.Inhabited.Thm31bPolymer`.
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation
  Balaban.Localization Balaban.Localization.LevelPair Balaban.Localization.I5Inhabited
  Balaban.Polymer Balaban.SmallField.Def6 Balaban.Inhabited.LevelStep Filter Topology
  MeasureTheory Set Metric

section TowerG

open Classical in
/-- **Theorem 3.1 (b) for the zero-class step at ONE scale and source radius `ρ`, with the
coefficients on polymer sets, general tower.**  As `thm31b_zeroClass_at_of_ray_rhoG`, with
`E = obsCoeff I` for the record `I` of `obsMarks_zeroClass_at_of_ray_ksupp_rhoG`, and moreover
`E T' ≠ 0` only if `sitesOf T'` is a polymer domain (`IsPolyDom T.m₀ (k+1)`).  The fixed
`thm31b_zeroClass_at_of_ray_supp_rho` is its corollary. -/
theorem thm31b_zeroClass_at_of_ray_supp_rhoG {d L N : ℕ} [NeZero L] {κmin : ℝ}
    (T : StepTowerG d L N κmin)
    {A₁ : ℝ} (hA : 0 < A₁) (p : ℕ) {CR s : ℝ}
    (hCR : 0 < CR) (hs0 : 0 < s) (hs : s < 1 / 2) :
  ∃ C : ℝ, 0 ≤ C ∧ ∀ ρ : ℝ, 0 < ρ → ∃ β₀ : ℝ, 2 ≤ β₀ ∧
  ∀ (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁], L ^ T.m₀ ∣ N₁ → 5 < N₁ →
  ∀ ν : ℝ, 0 < ν → ν * (L : ℝ) ^ (2 * (k + 1)) ≤ 1 →
  ∀ β : ℝ, β₀ ≤ β → ∀ b : ℝ, b = β * (L : ℝ) ^ (k * (d - 2)) → ∀ (p₁ : ℝ), 0 < p₁ →
  p₁ ≤ pLog A₁ p b →
  StepScaleDataG T k hk N₁ ν β p₁ →
  ∀ (ϱ : ℝ), ϱ = rhoSepG d L T.m₁ →
  ∀ S : StepSetting d L N₁ T.m₁ k N ϱ, HEq S (T.step k hk N₁ ν β p₁) →
  ∀ hpS : 0 < S.p₁,
      ∀ (val : ((S.U × Fin N → ℂ) × (S.U × Fin N → ℂ)) → ((S.U × Fin N → ℂ) × (S.U × Fin N → ℂ)) →
          ℂ → (RawData d L (N₁ * L ^ T.m₁) (k + 1) N ×
            (CTorus d L N₁ T.m₁ (k + 1) → Fin N → ℂ)) → ℂ)
        (𝒴 : Finset (Set (CTorus d L N₁ T.m₁ (k + 1))))
        (Tt : Set (CTorus d L N₁ T.m₁ (k + 1)) → ((S.U × Fin N → ℂ) × (S.U × Fin N → ℂ)) →
          ((S.U × Fin N → ℂ) × (S.U × Fin N → ℂ)) → ℂ →
          (RawData d L (N₁ * L ^ T.m₁) (k + 1) N ×
            (CTorus d L N₁ T.m₁ (k + 1) → Fin N → ℂ)) → ℂ),
      (hval : (∀ x w σ Θ, val x w σ Θ =
          (-(S.β : ℂ)) * raySrc3 (hatFun S.G' S.a₁ S.ν T.t S.hG'
            ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)
            (interactionOne S.hG S.hG' (le_refl (k + 1)) S.a₁ S.ν T.t)) taylorWeight x.1 w.1 σ Θ.1 +
          (S.β : ℂ) * (∑ s : CTorus d L N₁ T.m₁ (k + 1) × Fin N, Θ.2 s.1 s.2 *
            dirTermSrc (hatFun S.G' S.a₁ S.ν T.t S.hG' ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)
              (onXi S.G' S.a₁ S.ν T.t
                (fun D ψ' => svec (stepG d L N₁ T.m₁ k ϱ)
                  (flFieldOne S.G' (stepG d L N₁ T.m₁ k ϱ) T.BG₂ T.κ S.a₁ S.ν D ψ')
                    s.1 s.2)))
              (fun _ => (1 : ℂ)) x.2 w.2 σ Θ.1))) →
      (hcont : DiagCont (fun ψ : S.U × Fin N → ℂ => (ψ, ψ))
          (physXW S (lvCpsiG d L N T.κ T.t b) 2 2 (lvRG d L N T.κ T.t b p₁))
          (physSΛEta S S.a₁ S.ν T.t (ρ / S.β)) 2 𝒴 Tt) →
      (hI : (∀ Θ ∈ physSΛEta S S.a₁ S.ν T.t (ρ / S.β),
          ∃ I : DirectTerms S T.m₀ hpS (fun ψ => (ψ, ψ)) p₁ 2
              (S.β * prop33EpsEtaScaled d L N T.m₁ k T.m₀ S.a₁ T.BG T.BG₂ T.κ T.t
                (lvRG d L N T.κ T.t b p₁) 0 0 (ρ / S.β)) (2 * T.κdec - 1) Θ
              (physSΛEta S S.a₁ S.ν T.t (ρ / S.β))
              (physXW S (lvCpsiG d L N T.κ T.t b) 2 2 (lvRG d L N T.κ T.t b p₁)) val
              (physAgΘ S) (AgFDirPair S),
            I.𝒴 = 𝒴 ∧ I.T = Tt)) →
      (hmem0 : (rawOf S.D', (0 : CTorus d L N₁ T.m₁ (k + 1) → Fin N → ℂ)) ∈
          physSΛEta S S.a₁ S.ν T.t (ρ / S.β)) →
      (hmemg : (∀ g : Fld d L N₁ T.m₁ (k + 1) N, ∑ x, ∑ i, ‖g x i‖ < ρ →
          (rawOf S.D', fun y i => g y i / (S.β : ℂ)) ∈ physSΛEta S S.a₁ S.ν T.t (ρ / S.β))) →
      (hrayTt : (∀ Y ∈ 𝒴, ∀ Θ ∈ physSΛEta S S.a₁ S.ν T.t (ρ / S.β),
          ∀ ψ ∈ hatDisk S.U N p₁,
            DifferentiableOn ℂ (fun z : ℂ => Tt Y (z • ψ, z • ψ) (z • ψ, z • ψ) 1 Θ)
              (ball (0 : ℂ) (3 / 2)))) →
  ∀ g : Fld d L N₁ T.m₁ (k + 1) N,
    g ∈ l1BallRho d L N₁ T.m₁ (k + 1) N ρ →
  ∀ (y : CTorus d L N₁ T.m₁ (k + 1)) (i : Fin N),
    ∃ E : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := T.m₁) (K := k + 1) T.m₀ (k + 1)
        Set.univ) → ℂ,
      S.M0C (zeroClass d L N₁ T.m₁ k N ϱ) g y i =
        ((S.betaU ^ (1 / 2 : ℝ) : ℝ) : ℂ) * ∑ T', E T' ∧
      (∀ T', rootCube (m₀ := T.m₀) (blockIndex y) ∉ T' → E T' = 0) ∧
      (∀ T', ‖E T'‖ ≤ C * obsPrefactor p s b * Real.exp (-(3 / 2 * T.κdec) * dExt T')) ∧
      ∀ T', E T' ≠ 0 → IsPolyDom T.m₀ (k + 1) (sitesOf T') := by
  classical
  obtain ⟨C₁, C₂, hC₁, hC₂, hfam⟩ := obsMarks_zeroClass_at_of_ray_ksupp_rhoG T hA p hCR hs0 hs
  refine ⟨max C₁ C₂, le_max_of_le_left hC₁, fun ρ hρ => ?_⟩
  obtain ⟨β₀, hβ₀, hfam⟩ := hfam ρ hρ
  refine ⟨β₀, hβ₀, ?_⟩
  intro k hk N₁ _ h3 h5 ν hν hνk β hβ b hb p₁ hp hp₁ hsc ϱ hϱ S hS hpS val 𝒴 Tt hval hcont hI hmem0 hmemg hrayTt g hg y i
  obtain ⟨I, -, hκ0, hκH, hκ', hκh, -, hB1, hB2, hsupp⟩ := hfam k hk N₁ h3 h5 ν hν hνk β hβ b hb p₁ hp hp₁ hsc ϱ hϱ S hS hpS val 𝒴 Tt hval hcont hI hmem0 hmemg hrayTt g hg y i
  have hrate : 3 / 2 * T.κdec ≤ min I.κh I.κ' - I.κ0 - 1 := by
    have := T.outRate_eq.ge
    rw [hκh, hκ', hκ0]
    exact this
  obtain ⟨h1, h2, h3'⟩ := thm31b_coeff I hrate
  refine ⟨obsCoeff I, ?_, h2, fun T' => (h3' T').trans ?_, fun T' hne => ?_⟩
  · rw [← h1]
    rfl
  · have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast (by have := T.hL; omega : 1 ≤ L)
    have h3k : (1 : ℝ) ≤ (L : ℝ) ^ (k * (d - 2)) := one_le_pow₀ hL1
    have hb1 : 1 ≤ b := by
      subst hb
      nlinarith [show (2 : ℝ) ≤ β from by linarith]
    have hl : 0 ≤ Real.log b := Real.log_nonneg hb1
    have hW : 0 ≤ obsW p b := by unfold obsW; positivity
    have hb0 : 0 < b := by linarith
    have hP1 : 0 ≤ obsW p b ^ 4 * b ^ (-(1 / 2 : ℝ) - s) := by positivity
    have hP2 : 0 ≤ obsW p b ^ 2 / b := by positivity
    have hsum : I.B1 + I.B2 ≤ max C₁ C₂ * obsPrefactor p s b := by
      unfold obsPrefactor
      have a1 : C₁ * obsW p b ^ 4 * b ^ (-(1 / 2 : ℝ) - s) ≤
          max C₁ C₂ * (obsW p b ^ 4 * b ^ (-(1 / 2 : ℝ) - s)) := by
        rw [mul_assoc]; exact mul_le_mul_of_nonneg_right (le_max_left _ _) hP1
      have a2 : C₂ * obsW p b ^ 2 / b ≤
          max C₁ C₂ * (obsW p b ^ 2 / b) := by
        rw [mul_div_assoc]; exact mul_le_mul_of_nonneg_right (le_max_right _ _) hP2
      nlinarith [hB1, hB2]
    exact mul_le_mul_of_nonneg_right hsum (Real.exp_nonneg _)
  · by_contra hp'
    exact hne (I.obsCoeff_eq_zero_of_not_isPolyDom_of_kernel_supp hsupp hp')

end TowerG

/-- **Theorem 3.1 (b) for the zero-class step at ONE scale and source radius `ρ`, with the
coefficients on polymer sets.**  As `thm31b_zeroClass_at_of_ray_rho` (the constant `C` first, then
`ρ > 0` and `β₀`), with `E = obsCoeff I` for the record `I` of
`obsMarks_zeroClass_at_of_ray_ksupp_rho`, and moreover `E T' ≠ 0` only if `sitesOf T'` is a polymer
domain (`IsPolyDom 1 (k+1)`). -/
theorem thm31b_zeroClass_at_of_ray_supp_rho {κmin : ℝ} (T : StepTower κmin)
    {A₁ : ℝ} (hA : 0 < A₁) (p : ℕ) {CR s : ℝ}
    (hCR : 0 < CR) (hs0 : 0 < s) (hs : s < 1 / 2) :
  ∃ C : ℝ, 0 ≤ C ∧ ∀ ρ : ℝ, 0 < ρ → ∃ β₀ : ℝ, 2 ≤ β₀ ∧
  ∀ (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁], 3 ∣ N₁ → 5 < N₁ →
  ∀ ν : ℝ, 0 < ν → ν * 3 ^ (2 * (k + 1)) ≤ 1 →
  ∀ β : ℝ, β₀ ≤ β → ∀ (p₁ : ℝ), 0 < p₁ →
  p₁ ≤ pLog A₁ p (β * 3 ^ k) →
  StepScaleData T k hk N₁ ν β p₁ →
  ∀ S : StepSetting 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁), S = T.step k hk N₁ ν β p₁ →
  ∀ hpS : 0 < S.p₁,
      ∀ (val : ((S.U × Fin 2 → ℂ) × (S.U × Fin 2 → ℂ)) → ((S.U × Fin 2 → ℂ) × (S.U × Fin 2 → ℂ)) →
          ℂ → (RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2 ×
            (CTorus 3 3 N₁ T.m₁ (k + 1) → Fin 2 → ℂ)) → ℂ)
        (𝒴 : Finset (Set (CTorus 3 3 N₁ T.m₁ (k + 1))))
        (Tt : Set (CTorus 3 3 N₁ T.m₁ (k + 1)) → ((S.U × Fin 2 → ℂ) × (S.U × Fin 2 → ℂ)) →
          ((S.U × Fin 2 → ℂ) × (S.U × Fin 2 → ℂ)) → ℂ →
          (RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2 ×
            (CTorus 3 3 N₁ T.m₁ (k + 1) → Fin 2 → ℂ)) → ℂ),
      (hval : (∀ x w σ Θ, val x w σ Θ =
          (-(S.β : ℂ)) * raySrc3 (hatFun S.G' S.a₁ S.ν T.t S.hG'
            ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)
            (interactionOne S.hG S.hG' (le_refl (k + 1)) S.a₁ S.ν T.t)) taylorWeight x.1 w.1 σ Θ.1 +
          (S.β : ℂ) * (∑ s : CTorus 3 3 N₁ T.m₁ (k + 1) × Fin 2, Θ.2 s.1 s.2 *
            dirTermSrc (hatFun S.G' S.a₁ S.ν T.t S.hG' ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)
              (onXi S.G' S.a₁ S.ν T.t
                (fun D ψ' => svec (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁))
                  (flFieldOne S.G' (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) T.BG₂ T.κ S.a₁ S.ν D ψ')
                    s.1 s.2)))
              (fun _ => (1 : ℂ)) x.2 w.2 σ Θ.1))) →
      (hcont : DiagCont (fun ψ : S.U × Fin 2 → ℂ => (ψ, ψ))
          (physXW S (lvCpsi T.κ T.t (β * 3 ^ k)) 2 2 (lvR T.κ T.t (β * 3 ^ k) p₁))
          (physSΛEta S S.a₁ S.ν T.t (ρ / S.β)) 2 𝒴 Tt) →
      (hI : (∀ Θ ∈ physSΛEta S S.a₁ S.ν T.t (ρ / S.β),
          ∃ I : DirectTerms S 1 hpS (fun ψ => (ψ, ψ)) p₁ 2
              (S.β * prop33EpsEtaScaled 3 3 2 T.m₁ k 1 S.a₁ T.BG T.BG₂ T.κ T.t
                (lvR T.κ T.t (β * 3 ^ k) p₁) 0 0 (ρ / S.β)) (2 * T.κdec - 1) Θ
              (physSΛEta S S.a₁ S.ν T.t (ρ / S.β))
              (physXW S (lvCpsi T.κ T.t (β * 3 ^ k)) 2 2 (lvR T.κ T.t (β * 3 ^ k) p₁)) val
              (physAgΘ S) (AgFDirPair S),
            I.𝒴 = 𝒴 ∧ I.T = Tt)) →
      (hmem0 : (rawOf S.D', (0 : CTorus 3 3 N₁ T.m₁ (k + 1) → Fin 2 → ℂ)) ∈
          physSΛEta S S.a₁ S.ν T.t (ρ / S.β)) →
      (hmemg : (∀ g : Fld 3 3 N₁ T.m₁ (k + 1) 2, ∑ x, ∑ i, ‖g x i‖ < ρ →
          (rawOf S.D', fun y i => g y i / (S.β : ℂ)) ∈ physSΛEta S S.a₁ S.ν T.t (ρ / S.β))) →
      (hrayTt : (∀ Y ∈ 𝒴, ∀ Θ ∈ physSΛEta S S.a₁ S.ν T.t (ρ / S.β),
          ∀ ψ ∈ hatDisk S.U 2 p₁,
            DifferentiableOn ℂ (fun z : ℂ => Tt Y (z • ψ, z • ψ) (z • ψ, z • ψ) 1 Θ)
              (ball (0 : ℂ) (3 / 2)))) →
  ∀ g : Fld 3 3 N₁ T.m₁ (k + 1) 2,
    g ∈ l1BallRho 3 3 N₁ T.m₁ (k + 1) 2 ρ →
  ∀ (y : CTorus 3 3 N₁ T.m₁ (k + 1)) (i : Fin 2),
    ∃ E : Finset (CubeB (d := 3) (L := 3) (N₁ := N₁) (m₁ := T.m₁) (K := k + 1) 1 (k + 1)
        Set.univ) → ℂ,
      S.M0C (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) g y i =
        ((S.betaU ^ (1 / 2 : ℝ) : ℝ) : ℂ) * ∑ T', E T' ∧
      (∀ T', rootCube (m₀ := 1) (blockIndex y) ∉ T' → E T' = 0) ∧
      (∀ T', ‖E T'‖ ≤ C * obsPrefactor p s (β * 3 ^ k) * Real.exp (-(3 / 2 * T.κdec) * dExt T')) ∧
      ∀ T', E T' ≠ 0 → IsPolyDom 1 (k + 1) (sitesOf T') := by
  classical
  obtain ⟨C, hC, hat⟩ := thm31b_zeroClass_at_of_ray_supp_rhoG T.toG hA p hCR hs0 hs
  refine ⟨C, hC, fun ρ hρ => ?_⟩
  obtain ⟨β₀, hβ₀, hb⟩ := hat ρ hρ
  refine ⟨β₀, hβ₀, ?_⟩
  intro k hk N₁ _ h3N hN ν hνpos hν β hβ p₁ hp hp₁ D S hS hpS val 𝒴 Tt hval hcont hI hmem0
    hmemg hrayTt g hg y i
  subst hS
  exact hb k hk N₁ (by simpa using h3N) hN ν hνpos (by simpa using hν) β hβ (β * 3 ^ k)
    (by norm_num) p₁ hp hp₁ (StepTower.scaleDataG_of_fixed T D) (rhoSep T.m₁)
    (rhoSepG_three _).symm _ (StepTower.toG_step_heq T k hk N₁ ν β p₁).symm hpS val 𝒴 Tt hval
    hcont hI hmem0 hmemg hrayTt g hg y i

/-- **Theorem 3.1 (b) for the zero-class step at ONE scale, with the coefficients on polymer sets.**
As `thm31b_zeroClass_at_of_ray`, with `E = obsCoeff I` for the record `I` of
`obsMarks_zeroClass_at_of_ray_ksupp`, and moreover `E T' ≠ 0` only if `sitesOf T'` is a polymer
domain (`IsPolyDom 1 (k+1)`). -/
theorem thm31b_zeroClass_at_of_ray_supp {κmin : ℝ} (T : StepTower κmin)
    {A₁ : ℝ} (hA : 0 < A₁) (p : ℕ) {CR s : ℝ}
    (hCR : 0 < CR) (hs0 : 0 < s) (hs : s < 1 / 2) :
  ∃ β₀ C : ℝ, 2 ≤ β₀ ∧ 0 ≤ C ∧
  ∀ (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁], 3 ∣ N₁ → 5 < N₁ →
  ∀ ν : ℝ, 0 < ν → ν * 3 ^ (2 * (k + 1)) ≤ 1 →
  ∀ β : ℝ, β₀ ≤ β → ∀ (p₁ : ℝ), 0 < p₁ →
  p₁ ≤ pLog A₁ p (β * 3 ^ k) →
  StepScaleData T k hk N₁ ν β p₁ →
  ∀ S : StepSetting 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁), S = T.step k hk N₁ ν β p₁ →
  ∀ hpS : 0 < S.p₁,
      ∀ (val : ((S.U × Fin 2 → ℂ) × (S.U × Fin 2 → ℂ)) → ((S.U × Fin 2 → ℂ) × (S.U × Fin 2 → ℂ)) →
          ℂ → (RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2 ×
            (CTorus 3 3 N₁ T.m₁ (k + 1) → Fin 2 → ℂ)) → ℂ)
        (𝒴 : Finset (Set (CTorus 3 3 N₁ T.m₁ (k + 1))))
        (Tt : Set (CTorus 3 3 N₁ T.m₁ (k + 1)) → ((S.U × Fin 2 → ℂ) × (S.U × Fin 2 → ℂ)) →
          ((S.U × Fin 2 → ℂ) × (S.U × Fin 2 → ℂ)) → ℂ →
          (RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2 ×
            (CTorus 3 3 N₁ T.m₁ (k + 1) → Fin 2 → ℂ)) → ℂ),
      (hval : (∀ x w σ Θ, val x w σ Θ =
          (-(S.β : ℂ)) * raySrc3 (hatFun S.G' S.a₁ S.ν T.t S.hG'
            ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)
            (interactionOne S.hG S.hG' (le_refl (k + 1)) S.a₁ S.ν T.t)) taylorWeight x.1 w.1 σ Θ.1 +
          (S.β : ℂ) * (∑ s : CTorus 3 3 N₁ T.m₁ (k + 1) × Fin 2, Θ.2 s.1 s.2 *
            dirTermSrc (hatFun S.G' S.a₁ S.ν T.t S.hG' ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)
              (onXi S.G' S.a₁ S.ν T.t
                (fun D ψ' => svec (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁))
                  (flFieldOne S.G' (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) T.BG₂ T.κ S.a₁ S.ν D ψ')
                    s.1 s.2)))
              (fun _ => (1 : ℂ)) x.2 w.2 σ Θ.1))) →
      (hcont : DiagCont (fun ψ : S.U × Fin 2 → ℂ => (ψ, ψ))
          (physXW S (lvCpsi T.κ T.t (β * 3 ^ k)) 2 2 (lvR T.κ T.t (β * 3 ^ k) p₁))
          (physSΛEta S S.a₁ S.ν T.t (1 / S.β)) 2 𝒴 Tt) →
      (hI : (∀ Θ ∈ physSΛEta S S.a₁ S.ν T.t (1 / S.β),
          ∃ I : DirectTerms S 1 hpS (fun ψ => (ψ, ψ)) p₁ 2
              (S.β * prop33EpsEtaScaled 3 3 2 T.m₁ k 1 S.a₁ T.BG T.BG₂ T.κ T.t
                (lvR T.κ T.t (β * 3 ^ k) p₁) 0 0 (1 / S.β)) (2 * T.κdec - 1) Θ
              (physSΛEta S S.a₁ S.ν T.t (1 / S.β))
              (physXW S (lvCpsi T.κ T.t (β * 3 ^ k)) 2 2 (lvR T.κ T.t (β * 3 ^ k) p₁)) val
              (physAgΘ S) (AgFDirPair S),
            I.𝒴 = 𝒴 ∧ I.T = Tt)) →
      (hmem0 : (rawOf S.D', (0 : CTorus 3 3 N₁ T.m₁ (k + 1) → Fin 2 → ℂ)) ∈
          physSΛEta S S.a₁ S.ν T.t (1 / S.β)) →
      (hmemg : (∀ g : Fld 3 3 N₁ T.m₁ (k + 1) 2, ∑ x, ∑ i, ‖g x i‖ < 1 →
          (rawOf S.D', fun y i => g y i / (S.β : ℂ)) ∈ physSΛEta S S.a₁ S.ν T.t (1 / S.β))) →
      (hrayTt : (∀ Y ∈ 𝒴, ∀ Θ ∈ physSΛEta S S.a₁ S.ν T.t (1 / S.β),
          ∀ ψ ∈ hatDisk S.U 2 p₁,
            DifferentiableOn ℂ (fun z : ℂ => Tt Y (z • ψ, z • ψ) (z • ψ, z • ψ) 1 Θ)
              (ball (0 : ℂ) (3 / 2)))) →
  ∀ g : Fld 3 3 N₁ T.m₁ (k + 1) 2,
    g ∈ l1Ball 3 3 N₁ T.m₁ (k + 1) 2 →
  ∀ (y : CTorus 3 3 N₁ T.m₁ (k + 1)) (i : Fin 2),
    ∃ E : Finset (CubeB (d := 3) (L := 3) (N₁ := N₁) (m₁ := T.m₁) (K := k + 1) 1 (k + 1)
        Set.univ) → ℂ,
      S.M0C (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) g y i =
        ((S.betaU ^ (1 / 2 : ℝ) : ℝ) : ℂ) * ∑ T', E T' ∧
      (∀ T', rootCube (m₀ := 1) (blockIndex y) ∉ T' → E T' = 0) ∧
      (∀ T', ‖E T'‖ ≤ C * obsPrefactor p s (β * 3 ^ k) * Real.exp (-(3 / 2 * T.κdec) * dExt T')) ∧
      ∀ T', E T' ≠ 0 → IsPolyDom 1 (k + 1) (sitesOf T') := by
  obtain ⟨C, hC, hat⟩ := thm31b_zeroClass_at_of_ray_supp_rho T hA p hCR hs0 hs
  obtain ⟨β₀, hβ₀, hat⟩ := hat 1 one_pos
  exact ⟨β₀, C, hβ₀, hC, hat⟩

open Classical in
/-- **`thm31b_onCommonWitness_fromTower_supp` at source radius `ρ`, general tower.**  For
`T : StepTowerG d L N κmin` and output constants `C` with the stated values, with `b = β L^{k(d-2)}`.
The constants `C_E, C_F, C` do not depend on `ρ`; for each `ρ > 0` the threshold `β₀` satisfies
`3 ≤ β₀` and `ρ ≤ β₀`.  The witness clauses are those of `commonWitness_joint_fromTowerG_rho_full`
(slice `ρ/β`, sources of `ℓ¹`-size `< ρ`), and the coefficient `E = obsCoeff I` is given for every
`g` of the `ℓ¹` ball of radius `ρ`.  The fixed `thm31b_onCommonWitness_fromTower_supp_rho` is its
corollary. -/
theorem thm31b_onCommonWitness_fromTowerG_supp_rho {d L N : ℕ} [NeZero L] {κmin : ℝ}
    (T : StepTowerG d L N κmin) (C : StepOutputConsts d L)
    (hKc : C.Kc = 2 * (K0 d L T.κ0 + 1))
    (hKall : C.Kall = max (2 * K0 d L T.κ0) (rootUnionK d L T.m₀ T.m₁ T.κ0))
    (hH : C.kH = 2 * T.κdec - 1) (h0 : C.k0 = T.κ0) (h' : C.k' = T.κ') {A₁ : ℝ}
    (hA : 0 < A₁) (p : ℕ) {CR s : ℝ}
    (hCR : 0 < CR) (hs0 : 0 < s) (hs : s < 1 / 2) :
    ∃ CE CF Cthm : ℝ, 0 < CE ∧ 0 < CF ∧ 0 ≤ Cthm ∧
    ∀ ρ : ℝ, 0 < ρ → ∃ β₀ : ℝ, 3 ≤ β₀ ∧ ρ ≤ β₀ ∧
    ∀ (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁] (hLN : L ^ T.m₀ ∣ N₁), 5 < N₁ →
    ∀ ν : ℝ, 0 < ν → ν * (L : ℝ) ^ (2 * (k + 1)) ≤ 1 →
    ∀ β : ℝ, β₀ ≤ β → ∀ (b : ℝ), b = β * (L : ℝ) ^ (k * (d - 2)) → ∀ (p₁ : ℝ) (hp0 : 0 < p₁),
    p₁ ≤ pLog A₁ p b → StepScaleDataG T k hk N₁ ν β p₁ →
    ∀ (ϱ : ℝ), ϱ = rhoSepG d L T.m₁ →
    ∀ (S : StepSetting d L N₁ T.m₁ k N ϱ), HEq S (T.step k hk N₁ ν β p₁) →
    ∀ (hp : 0 < S.p₁),
    ∃ (val : ((S.U × Fin N → ℂ) × (S.U × Fin N → ℂ)) → ((S.U × Fin N → ℂ) × (S.U × Fin N → ℂ)) →
        ℂ → (RawData d L (N₁ * L ^ T.m₁) (k + 1) N × (CTorus d L N₁ T.m₁ (k + 1) → Fin N → ℂ)) → ℂ)
      (𝒴 : Finset (Set (CTorus d L N₁ T.m₁ (k + 1))))
      (Tt : Set (CTorus d L N₁ T.m₁ (k + 1)) → ((S.U × Fin N → ℂ) × (S.U × Fin N → ℂ)) →
        ((S.U × Fin N → ℂ) × (S.U × Fin N → ℂ)) → ℂ →
        (RawData d L (N₁ * L ^ T.m₁) (k + 1) N × (CTorus d L N₁ T.m₁ (k + 1) → Fin N → ℂ)) → ℂ)
      (hdom : ∀ Y ∈ 𝒴, IsDj T.m₀ (k + 1) Y),
      (∀ x w σ Θ, val x w σ Θ =
        (-(S.β : ℂ)) * raySrc3 (hatFun S.G' S.a₁ S.ν T.t S.hG'
          ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)
          (interactionOne S.hG S.hG' (le_refl (k + 1)) S.a₁ S.ν T.t)) taylorWeight x.1 w.1 σ Θ.1 +
        (S.β : ℂ) * (∑ s : CTorus d L N₁ T.m₁ (k + 1) × Fin N, Θ.2 s.1 s.2 *
          dirTermSrc (hatFun S.G' S.a₁ S.ν T.t S.hG' ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)
            (onXi S.G' S.a₁ S.ν T.t
              (fun D ψ' => svec (stepG d L N₁ T.m₁ k ϱ)
                (flFieldOne S.G' (stepG d L N₁ T.m₁ k ϱ) T.BG₂ T.κ S.a₁ S.ν D ψ')
                  s.1 s.2)))
            (fun _ => (1 : ℂ)) x.2 w.2 σ Θ.1)) ∧
      (∃ εU : ℝ,
      εU = β * prop33EpsEtaScaled d L N T.m₁ k T.m₀ 1 T.BG T.BG₂ T.κ T.t
        (lvRG d L N T.κ T.t b p₁) 0 0 (ρ / β) ∧ 0 < εU ∧
      4 * εU ≤ CE * (Real.log b) ^ (3 * p) / Real.sqrt b +
        ρ * CF * (Real.log b) ^ p / Real.sqrt b ∧
      (∀ g : Fld d L N₁ T.m₁ (k + 1) N, g ∈ l1BallRho d L N₁ T.m₁ (k + 1) N ρ →
        ∃ BR : StepActivityBound S (zeroClass d L N₁ T.m₁ k N ϱ) g,
        ∃ BC : StepActivityBoundC S (zeroClass d L N₁ T.m₁ k N ϱ) g,
          BR.m₀ = T.m₀ ∧ BC.m₀ = T.m₀ ∧ BR.Lb = ({Y // Y ∈ 𝒴} ⊕ {Y // Y ∈ 𝒴}) ∧ BC.Lb = BR.Lb ∧
          HEq BR.Lab ((thickLabels 𝒴 hdom).sum (thickLabels 𝒴 hdom)) ∧ HEq BC.Lab BR.Lab ∧
          HEq BR.BS (S.blockSplit T.m₀ hp) ∧ HEq BC.BS BR.BS ∧
          BR.κ0 = T.κ0 ∧ BC.κ0 = T.κ0 ∧ BR.κ' = T.κ' ∧ BC.κ' = T.κ' ∧
          BR.κH = 2 * T.κdec - 1 ∧ BC.κH = BR.κH ∧
          BR.Kc = 2 * (K0 d L T.κ0 + 1) ∧ BC.Kc = BR.Kc ∧ BR.εH = BC.εH ∧ BR.εH = 4 * εU) ∧
      (∃ Jr : S.JointRep T.t (2 * p₁),
        ∃ Aseg : ∀ e : physParam N S, e ∈ physFibreRho S S.a₁ S.ν T.t ρ → ℝ × ℝ →
          LabelAct ((thickLabels 𝒴 hdom).sum (thickLabels 𝒴 hdom)) (S.blockSplit T.m₀ hp).Ωb
            (4 * εU) (2 * T.κdec - 1) T.κ0 (2 * (K0 d L T.κ0 + 1)),
        (∀ (e : physParam N S) (he : e ∈ physFibreRho S S.a₁ S.ν T.t ρ), ∀ p ∈ stepSegments,
          ∀ᵐ x ∂S.nuFl,
            Jr.W1 (zeroClass d L N₁ T.m₁ k N ϱ)
                ((e.1 : RawData d L (N₁ * L ^ T.m₁) (k + 1) N), (p.1 : ℂ) • S.hatC x) +
              Jr.W2 (zeroClass d L N₁ T.m₁ k N ϱ) e.2
                ((e.1 : RawData d L (N₁ * L ^ T.m₁) (k + 1) N), (p.2 : ℂ) • S.hatC x) =
            ∑ y, (Aseg e he p).H y ((S.blockSplit T.m₀ hp).restr x)) ∧
        (∀ g : Fld d L N₁ T.m₁ (k + 1) N, ∑ x, ∑ i, ‖g x i‖ < ρ →
          ∃ he : ((⟨rawOf S.D', rawOf_mem_rawSub _⟩ : rawSub N S.G'), g) ∈
              physFibreRho S S.a₁ S.ν T.t ρ,
            ∀ p ∈ stepSegments, ∀ᵐ x ∂S.nuFl,
              S.WoneC (zeroClass d L N₁ T.m₁ k N ϱ) p.1 x +
                S.WtwoC (zeroClass d L N₁ T.m₁ k N ϱ) g p.2 x =
              ∑ y, (Aseg (⟨rawOf S.D', rawOf_mem_rawSub _⟩, g) he p).H y
                ((S.blockSplit T.m₀ hp).restr x))) ∧
      (0 < εU ∧ ∃ A₀ : ℂ → LabelAct (thickLabels 𝒴 hdom) (S.blockSplit T.m₀ hp).Ωb
          εU (2 * T.κdec - 1) T.κ0 (K0 d L T.κ0 + 1),
        (∀ z : ℂ, ‖z‖ < 3 / 2 → ∀ y Φ, (A₀ z).H y Φ =
          Tt y.1 (z • S.hatOf T.m₀ p₁ hp Φ, z • S.hatOf T.m₀ p₁ hp Φ)
            (z • S.hatOf T.m₀ p₁ hp Φ, z • S.hatOf T.m₀ p₁ hp Φ) 1
            (rawOf S.D', (0 : CTorus d L N₁ T.m₁ (k + 1) → Fin N → ℂ))) ∧
        (∀ z : ℂ, 3 / 2 ≤ ‖z‖ → ∀ y Φ, (A₀ z).H y Φ = 0) ∧
        ∀ g : Fld d L N₁ T.m₁ (k + 1) N, g ∈ l1BallRho d L N₁ T.m₁ (k + 1) N ρ →
        ∃ Ag : ℂ → LabelAct (thickLabels 𝒴 hdom) (S.blockSplit T.m₀ hp).Ωb
            εU (2 * T.κdec - 1) T.κ0 (K0 d L T.κ0 + 1),
          (∀ z : ℂ, ‖z‖ < 3 / 2 → ∀ y Φ, (Ag z).H y Φ =
            Tt y.1 (z • S.hatOf T.m₀ p₁ hp Φ, z • S.hatOf T.m₀ p₁ hp Φ)
              (z • S.hatOf T.m₀ p₁ hp Φ, z • S.hatOf T.m₀ p₁ hp Φ) 1
              (rawOf S.D', fun y i => g y i / (S.β : ℂ))) ∧
          (∀ z : ℂ, 3 / 2 ≤ ‖z‖ → ∀ y Φ, (Ag z).H y Φ = 0) ∧
          ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 → ∀ᵐ x ∂S.nuFl,
            ∑ y, (((A₀ 1).sub (A₀ (t : ℂ))).sum (Ag (t : ℂ))).H y
                (((S.blockSplit T.m₀ hp).restr x)) =
              S.WoneC (zeroClass d L N₁ T.m₁ k N ϱ) 1 x +
              S.WtwoC (zeroClass d L N₁ T.m₁ k N ϱ) g t x) ∧
      (∃ (Jr : S.JointRep T.t (2 * p₁))
          (I : DirectTerms S T.m₀ hp (fun ψ => (ψ, ψ)) p₁ 2
                (S.β * prop33EpsEtaScaled d L N T.m₁ k T.m₀ S.a₁ T.BG T.BG₂ T.κ T.t
                  (lvRG d L N T.κ T.t b p₁) 0 0 (ρ / S.β)) (2 * T.κdec - 1)
                (rawOf S.D', (0 : CTorus d L N₁ T.m₁ (k + 1) → Fin N → ℂ))
                (physSΛEta S S.a₁ S.ν T.t (ρ / S.β))
                (physXW S (lvCpsiG d L N T.κ T.t b) 2 2 (lvRG d L N T.κ T.t b p₁)) val
                (physAgΘ S) (AgFDirPair S)),
          I.𝒴 = 𝒴 ∧ I.T = Tt ∧
          ∃ (hF : DirectTermsFamilyOn S T.m₀ (physInclScaled N S (((1 / S.β : ℝ)) : ℂ)) I
              (physVqRho S S.a₁ S.ν T.t ρ ρ))
            (hεU : 0 ≤ S.β * prop33EpsEtaScaled d L N T.m₁ k T.m₀ S.a₁ T.BG T.BG₂ T.κ T.t
                  (lvRG d L N T.κ T.t b p₁) 0 0 (ρ / S.β)),
            0 < S.β * prop33EpsEtaScaled d L N T.m₁ k T.m₀ S.a₁ T.BG T.BG₂ T.κ T.t
                  (lvRG d L N T.κ T.t b p₁) 0 0 (ρ / S.β) ∧
            ∀ {Kc : ℝ} (hKc : K0 d L T.κ0 ≤ Kc),
            ∃ A : physParam N S → ℂ → LabelAct (thickLabels I.𝒴 I.dom) (S.blockSplit T.m₀ hp).Ωb
                (2 * (S.β * prop33EpsEtaScaled d L N T.m₁ k T.m₀ S.a₁ T.BG T.BG₂ T.κ T.t
                  (lvRG d L N T.κ T.t b p₁) 0 0 (ρ / S.β))) (2 * T.κdec - 1) T.κ0 Kc,
              A = labelActFamilyOn S T.m₀ (physInclScaled N S (((1 / S.β : ℝ)) : ℂ)) I hF
                    (show L ^ T.m₀ ∣ N₁ by simpa using hLN) hp0 (by norm_num) hεU T.κ0_ent hKc ∧
              (∀ (y : {Y // Y ∈ I.𝒴}) (Φ : ∀ b, (S.blockSplit T.m₀ hp).Ωb b),
                AnalyticOnNhd ℂ (fun r : physParam N S × ℂ => (A r.1 r.2).H y Φ)
                  (physVqRho S S.a₁ S.ν T.t ρ ρ ×ˢ Metric.ball (0 : ℂ) 2)) ∧
              (∀ e ∈ physVqRho S S.a₁ S.ν T.t ρ ρ, ∀ u : ℂ, ‖u‖ < 2 → ∀ y : {Y // Y ∈ I.𝒴},
                Continuous ((A e u).H y)) ∧
              (∀ e ∈ physVqRho S S.a₁ S.ν T.t ρ ρ, ∀ u : ℂ, ‖u‖ < 2 →
                ∀ Φ : ∀ b, (S.blockSplit T.m₀ hp).Ωb b,
                ∑ y, (A e u).H y Φ =
                  val (S.hatOf T.m₀ p₁ hp Φ, S.hatOf T.m₀ p₁ hp Φ)
                    (S.hatOf T.m₀ p₁ hp Φ, S.hatOf T.m₀ p₁ hp Φ) u
                    (physInclScaled N S (((1 / S.β : ℝ)) : ℂ) e)) ∧
              (∀ᵐ x ∂S.nuFl, ∀ e ∈ physVqRho S S.a₁ S.ν T.t ρ ρ, ∀ u : ℂ, ‖u‖ < 2 →
                ∑ y, (A e u).H y ((S.blockSplit T.m₀ hp).restr x) =
                  val (S.hatC x, S.hatC x) (S.hatC x, S.hatC x) u
                    (physInclScaled N S (((1 / S.β : ℝ)) : ℂ) e)) ∧
              (∀ᵐ x ∂S.nuFl, ∀ e ∈ physFibreRho S S.a₁ S.ν T.t ρ, ∀ s ∈ Icc (0 : ℝ) 1,
                Jr.W1 (zeroClass d L N₁ T.m₁ k N ϱ)
                    ((e.1 : RawData d L (N₁ * L ^ T.m₁) (k + 1) N), (s : ℂ) • S.hatC x) =
                  (s : ℂ) ^ 2 * ∑ y, (A ((e.1, 0) : physParam N S) (s : ℂ)).H y
                    ((S.blockSplit T.m₀ hp).restr x)) ∧
              (∀ᵐ x ∂S.nuFl, ∀ e ∈ physFibreRho S S.a₁ S.ν T.t ρ, ∑ x', ∑ i, ‖e.2 x' i‖ < ρ →
                ∀ t ∈ Icc (0 : ℝ) 1,
                Jr.W2 (zeroClass d L N₁ T.m₁ k N ϱ) e.2
                    ((e.1 : RawData d L (N₁ * L ^ T.m₁) (k + 1) N), (t : ℂ) • S.hatC x) =
                  ∑ y, (A e (t : ℂ)).H y ((S.blockSplit T.m₀ hp).restr x) -
                    ∑ y, (A ((e.1, 0) : physParam N S) (t : ℂ)).H y
                      ((S.blockSplit T.m₀ hp).restr x)) ∧
              (∀ᵐ x ∂S.nuFl, ∀ (D' : BgData S.G' N) (hDh : ∀ y i, D'.h y i = (S.h₀ i : ℂ)),
                XiCData S.G' S.a S.ν (k + 1) 1 T.t D' → ∀ s ∈ Icc (0 : ℝ) 1,
                (S.withDatum D' hDh).WoneC (zeroClass d L N₁ T.m₁ k N ϱ) s x =
                  (s : ℂ) ^ 2 * ∑ y, (A ((⟨rawOf D', rawOf_mem_rawSub _⟩ : rawSub N S.G'),
                    (0 : CTorus d L N₁ T.m₁ (k + 1) → Fin N → ℂ)) (s : ℂ)).H y
                    ((S.blockSplit T.m₀ hp).restr x)) ∧
              (∀ᵐ x ∂S.nuFl, ∀ (D' : BgData S.G' N) (hDh : ∀ y i, D'.h y i = (S.h₀ i : ℂ)),
                XiCData S.G' S.a S.ν (k + 1) 1 T.t D' →
                ∀ g : Fld d L N₁ T.m₁ (k + 1) N, ∑ x', ∑ i, ‖g x' i‖ < ρ → ∀ t ∈ Icc (0 : ℝ) 1,
                (S.withDatum D' hDh).WtwoC (zeroClass d L N₁ T.m₁ k N ϱ) g t x =
                  ∑ y, (A ((⟨rawOf D', rawOf_mem_rawSub _⟩ : rawSub N S.G'), g) (t : ℂ)).H y
                      ((S.blockSplit T.m₀ hp).restr x) -
                    ∑ y, (A ((⟨rawOf D', rawOf_mem_rawSub _⟩ : rawSub N S.G'),
                      (0 : CTorus d L N₁ T.m₁ (k + 1) → Fin N → ℂ)) (t : ℂ)).H y
                      ((S.blockSplit T.m₀ hp).restr x)) ∧
              (∀ᵐ x ∂S.nuFl, ∀ e ∈ physFibreRho S S.a₁ S.ν T.t ρ, ∑ x', ∑ i, ‖e.2 x' i‖ < ρ →
                ∀ p ∈ stepSegments,
                Jr.W1 (zeroClass d L N₁ T.m₁ k N ϱ)
                    ((e.1 : RawData d L (N₁ * L ^ T.m₁) (k + 1) N), (p.1 : ℂ) • S.hatC x) +
                  Jr.W2 (zeroClass d L N₁ T.m₁ k N ϱ) e.2
                    ((e.1 : RawData d L (N₁ * L ^ T.m₁) (k + 1) N), (p.2 : ℂ) • S.hatC x) =
                  ∑ y, (segAct (A ((e.1, 0) : physParam N S)) (A e)
                    (mul_nonneg zero_le_two hεU) (two_mul _).ge
                    (fun s => ((if s ∈ Icc (0 : ℝ) 1 then s ^ 2 else 0 : ℝ) : ℂ))
                    norm_ite_sq_le p).H y ((S.blockSplit T.m₀ hp).restr x)) ∧
              (∀ (y : {Y // Y ∈ I.𝒴}) (Φ : ∀ b, (S.blockSplit T.m₀ hp).Ωb b),
                AnalyticOnNhd ℂ (fun r : physParam N S × ℂ =>
                  (zeroSourceAct A 2 zero_le_two r.1 r.2).H y Φ)
                  (physVRho S S.a₁ S.ν T.t ρ ×ˢ Metric.ball (0 : ℂ) 2)) ∧
              (∀ e ∈ physVRho S S.a₁ S.ν T.t ρ, ∀ u ∈ Metric.ball (0 : ℂ) 2, ∀ y : {Y // Y ∈ I.𝒴},
                Continuous ((zeroSourceAct A 2 zero_le_two e u).H y)) ∧
              (∀ (D' : BgData S.G' N) (hDh : ∀ y i, D'.h y i = (S.h₀ i : ℂ)),
                XiCData S.G' S.a S.ν (k + 1) 1 T.t D' → ∀ g : Fld d L N₁ T.m₁ (k + 1) N,
                ∀ s : ℝ, s ∈ Icc (0 : ℝ) 1 → ∀ᵐ x ∂S.nuFl,
                  (S.withDatum D' hDh).WoneC (zeroClass d L N₁ T.m₁ k N ϱ) s x =
                    ∑ y, (zeroSourceAct A 2 zero_le_two
                      ((⟨rawOf D', rawOf_mem_rawSub _⟩ : rawSub N S.G'), g) (s : ℂ)).H y
                      ((S.blockSplit T.m₀ hp).restr x))) ∧
      (∀ (Y : Set (CTorus d L N₁ T.m₁ (k + 1)))
        (Θ : RawData d L (N₁ * L ^ T.m₁) (k + 1) N × (CTorus d L N₁ T.m₁ (k + 1) → Fin N → ℂ)),
        Θ ∈ physSΛEta S S.a₁ S.ν T.t (ρ / S.β) → ∀ ψ : S.U × Fin N → ℂ,
        (∀ p, ‖ψ p‖ ≤ p₁) →
        DifferentiableOn ℂ (fun ζ : ℂ => Tt Y (ζ • ψ, ζ • ψ) (ζ • ψ, ζ • ψ) 1 Θ)
          (Metric.ball (0 : ℂ) (3 / 2))) ∧
      (DiagCont (fun ψ : S.U × Fin N → ℂ => (ψ, ψ))
          (physXW S (lvCpsiG d L N T.κ T.t b) 2 2 (lvRG d L N T.κ T.t b p₁))
          (physSΛEta S S.a₁ S.ν T.t (ρ / S.β)) 2 𝒴 Tt ∧
        (∀ Θ ∈ physSΛEta S S.a₁ S.ν T.t (ρ / S.β),
          ∃ I : DirectTerms S T.m₀ hp (fun ψ => (ψ, ψ)) p₁ 2
              (S.β * prop33EpsEtaScaled d L N T.m₁ k T.m₀ S.a₁ T.BG T.BG₂ T.κ T.t
                (lvRG d L N T.κ T.t b p₁) 0 0 (ρ / S.β)) (2 * T.κdec - 1) Θ
              (physSΛEta S S.a₁ S.ν T.t (ρ / S.β))
              (physXW S (lvCpsiG d L N T.κ T.t b) 2 2 (lvRG d L N T.κ T.t b p₁)) val
              (physAgΘ S) (AgFDirPair S),
            I.𝒴 = 𝒴 ∧ I.T = Tt) ∧
        (rawOf S.D', (0 : CTorus d L N₁ T.m₁ (k + 1) → Fin N → ℂ)) ∈
          physSΛEta S S.a₁ S.ν T.t (ρ / S.β) ∧
        (∀ g : Fld d L N₁ T.m₁ (k + 1) N, ∑ x, ∑ i, ‖g x i‖ < ρ →
          (rawOf S.D', fun y i => g y i / (S.β : ℂ)) ∈ physSΛEta S S.a₁ S.ν T.t (ρ / S.β)) ∧
        (∀ Y ∈ 𝒴, ∀ Θ ∈ physSΛEta S S.a₁ S.ν T.t (ρ / S.β),
          ∀ ψ ∈ hatDisk S.U N p₁,
            DifferentiableOn ℂ (fun z : ℂ => Tt Y (z • ψ, z • ψ) (z • ψ, z • ψ) 1 Θ)
              (Metric.ball (0 : ℂ) (3 / 2)))) ∧
      (∃ (Jr : S.JointRep T.t (2 * p₁))
          (I : DirectTerms S T.m₀ hp (fun ψ => (ψ, ψ)) p₁ 2
                (S.β * prop33EpsEtaScaled d L N T.m₁ k T.m₀ S.a₁ T.BG T.BG₂ T.κ T.t
                  (lvRG d L N T.κ T.t b p₁) 0 0 (ρ / S.β)) (2 * T.κdec - 1)
                (rawOf S.D', (0 : CTorus d L N₁ T.m₁ (k + 1) → Fin N → ℂ))
                (physSΛEta S S.a₁ S.ν T.t (ρ / S.β))
                (physXW S (lvCpsiG d L N T.κ T.t b) 2 2 (lvRG d L N T.κ T.t b p₁)) val
                (physAgΘ S) (AgFDirPair S)),
          I.𝒴 = 𝒴 ∧ I.T = Tt ∧
          ∃ (hF : DirectTermsFamilyOn S T.m₀ (physInclScaled N S (((1 / S.β : ℝ)) : ℂ)) I
              (physVqRho S S.a₁ S.ν T.t ρ ρ))
            (hεU : 0 ≤ S.β * prop33EpsEtaScaled d L N T.m₁ k T.m₀ S.a₁ T.BG T.BG₂ T.κ T.t
                  (lvRG d L N T.κ T.t b p₁) 0 0 (ρ / S.β)),
            0 < S.β * prop33EpsEtaScaled d L N T.m₁ k T.m₀ S.a₁ T.BG T.BG₂ T.κ T.t
                  (lvRG d L N T.κ T.t b p₁) 0 0 (ρ / S.β) ∧
            (
          0 < 2 ^ 2 * (2 * (S.β * prop33EpsEtaScaled d L N T.m₁ k T.m₀ S.a₁ T.BG T.BG₂ T.κ T.t
                  (lvRG d L N T.κ T.t b p₁) 0 0 (ρ / S.β))) ∧
          2 ^ 2 * (2 * (S.β * prop33EpsEtaScaled d L N T.m₁ k T.m₀ S.a₁ T.BG T.BG₂ T.κ T.t
                  (lvRG d L N T.κ T.t b p₁) 0 0 (ρ / S.β))) ≤
              2 * CE * (Real.log b) ^ (3 * p) / Real.sqrt b +
                2 * (ρ * CF) * (Real.log b) ^ p / Real.sqrt b ∧
          2 ^ 2 * (2 * (S.β * prop33EpsEtaScaled d L N T.m₁ k T.m₀ S.a₁ T.BG T.BG₂ T.κ T.t
                  (lvRG d L N T.κ T.t b p₁) 0 0 (ρ / S.β))) ≤
              C.theta ∧
          2 ^ 2 * (2 * (S.β * prop33EpsEtaScaled d L N T.m₁ k T.m₀ S.a₁ T.BG T.BG₂ T.κ T.t
                  (lvRG d L N T.κ T.t b p₁) 0 0 (ρ / S.β))) ≤
              stepTheta d L (2 * (K0 d L T.κ0 + 1) + rootUnionK d L T.m₀ T.m₁ T.κ0) (2 * T.κdec - 1) T.κ0 T.κ' ∧
          ∃ A : physParam N S → ℂ → LabelAct (thickLabels I.𝒴 I.dom) (S.blockSplit T.m₀ hp).Ωb
              (2 * (S.β * prop33EpsEtaScaled d L N T.m₁ k T.m₀ S.a₁ T.BG T.BG₂ T.κ T.t
                (lvRG d L N T.κ T.t b p₁) 0 0 (ρ / S.β))) (2 * T.κdec - 1) T.κ0
              (2 * (K0 d L T.κ0 + 1)),
            A = labelActFamilyOn S T.m₀ (physInclScaled N S (((1 / S.β : ℝ)) : ℂ)) I hF
                  (show L ^ T.m₀ ∣ N₁ by simpa using hLN) hp0 (by norm_num) hεU T.κ0_ent
                  T.marks_K0_le ∧
            (∀ᵐ x ∂S.nuFl, ∀ e ∈ physFibreRho S S.a₁ S.ν T.t ρ, ∀ s ∈ Icc (0 : ℝ) 1,
              Jr.W1 (zeroClass d L N₁ T.m₁ k N ϱ)
                  ((e.1 : RawData d L (N₁ * L ^ T.m₁) (k + 1) N), (s : ℂ) • S.hatC x) =
                (s : ℂ) ^ 2 * ∑ y, (A ((e.1, 0) : physParam N S) (s : ℂ)).H y
                  ((S.blockSplit T.m₀ hp).restr x)) ∧
            (∀ᵐ x ∂S.nuFl, ∀ e ∈ physFibreRho S S.a₁ S.ν T.t ρ, ∑ x', ∑ i, ‖e.2 x' i‖ < ρ →
              ∀ t ∈ Icc (0 : ℝ) 1,
              Jr.W2 (zeroClass d L N₁ T.m₁ k N ϱ) e.2
                  ((e.1 : RawData d L (N₁ * L ^ T.m₁) (k + 1) N), (t : ℂ) • S.hatC x) =
                ∑ y, (A e (t : ℂ)).H y ((S.blockSplit T.m₀ hp).restr x) -
                  ∑ y, (A ((e.1, 0) : physParam N S) (t : ℂ)).H y
                    ((S.blockSplit T.m₀ hp).restr x)) ∧
            ∀ {ι : Type} [Fintype ι] (reads : ι → Set (CTorus d L N₁ T.m₁ (k + 1)))
              (dom : ι → Finset (Set (CTorus d L N₁ T.m₁ (k + 1))))
              (hdomR : ∀ b, ∀ Y ∈ dom b, IsDj T.m₀ (k + 1) Y),
            ∃ A0 : physParam N S → ℂ → LabelAct
                (commonLabels (thickLabels I.𝒴 I.dom) (show L ^ T.m₀ ∣ N₁ by simpa using hLN)
                  (by have := T.hL; omega) reads dom hdomR) (S.blockSplit T.m₀ hp).Ωb
                (2 ^ 2 * (2 * (S.β * prop33EpsEtaScaled d L N T.m₁ k T.m₀ S.a₁ T.BG T.BG₂ T.κ T.t
                  (lvRG d L N T.κ T.t b p₁) 0 0 (ρ / S.β)))) (2 * T.κdec - 1) T.κ0 (2 * (K0 d L T.κ0 + 1) + rootUnionK d L T.m₀ T.m₁ T.κ0),
              A0 = commonAct (zeroSourceAct A 2 (by norm_num))
                  (show L ^ T.m₀ ∣ N₁ by simpa using hLN) (by have := T.hL; omega) reads dom hdomR
                  (mul_nonneg (sq_nonneg 2) (mul_nonneg zero_le_two hεU)) T.κ0_two ∧
              (∀ y (Φ : ∀ b, (S.blockSplit T.m₀ hp).Ωb b),
                AnalyticOnNhd ℂ (fun r : physParam N S × ℂ => (A0 r.1 r.2).H y Φ)
                  (physVRho S S.a₁ S.ν T.t ρ ×ˢ ball (0 : ℂ) 2)) ∧
              (∀ e ∈ physVRho S S.a₁ S.ν T.t ρ, ∀ y (Φ : ∀ b, (S.blockSplit T.m₀ hp).Ωb b),
                DifferentiableOn ℂ (fun u => (A0 e u).H y Φ) (ball (0 : ℂ) 2)) ∧
              (∀ y, ∀ e ∈ physVRho S S.a₁ S.ν T.t ρ, ∀ u ∈ ball (0 : ℂ) 2,
                Continuous ((A0 e u).H y)) ∧
              (∀ (e : physParam N S) (u : ℂ) (Φ : ∀ b, (S.blockSplit T.m₀ hp).Ωb b),
                ∑ y, (A0 e u).H y Φ =
                  sqFactor 2 u * ∑ y, (A ((e.1, 0) : physParam N S) u).H y Φ) ∧
              (∀ (D' : BgData S.G' N) (hDh : ∀ y i, D'.h y i = (S.h₀ i : ℂ)),
                XiCData S.G' S.a S.ν (k + 1) 1 T.t D' → ∀ g : Fld d L N₁ T.m₁ (k + 1) N,
                ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ᵐ x ∂S.nuFl,
                  (S.withDatum D' hDh).WoneC (zeroClass d L N₁ T.m₁ k N ϱ) s x =
                    ∑ y, (A0 ((⟨rawOf D', rawOf_mem_rawSub _⟩ : rawSub N S.G'), g) (s : ℂ)).H y
                      ((S.blockSplit T.m₀ hp).restr x)) ∧
              (∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ᵐ x ∂S.nuFl,
                S.WoneC (zeroClass d L N₁ T.m₁ k N ϱ) s x =
                  ∑ y, (A0 ((⟨rawOf S.D', rawOf_mem_rawSub _⟩ : rawSub N S.G'),
                    (0 : CTorus d L N₁ T.m₁ (k + 1) → Fin N → ℂ)) (s : ℂ)).H y
                    ((S.blockSplit T.m₀ hp).restr x)) ∧
              Nonempty (ParamMarkFamily (S.blockSplit T.m₀ hp).μ
                (commonLabels (thickLabels I.𝒴 I.dom) (show L ^ T.m₀ ∣ N₁ by simpa using hLN)
                  (by have := T.hL; omega) reads dom hdomR) A0
                (fun i : Empty => i.elim) (fun _ _ _ _ => (0 : ℂ)) 0 (fun i : Empty => i.elim)
                (physVRho S S.a₁ S.ν T.t ρ) (ball (0 : ℂ) 2) (physCarrier S T.m₀ hp)) ∧
              (∀ _y₀ : {Y // Y ∈ I.𝒴} ⊕ RootUnionLb T.m₀ reads dom,
                Nonempty (InterpMarks S.nuFl (S.blockSplit T.m₀ hp)
                  (S.WoneC (zeroClass d L N₁ T.m₁ k N ϱ)) (fun _ _ => (0 : ℂ))))))) ∧
    (∀ g : Fld d L N₁ T.m₁ (k + 1) N,
    g ∈ l1BallRho d L N₁ T.m₁ (k + 1) N ρ →
  ∀ (y : CTorus d L N₁ T.m₁ (k + 1)) (i : Fin N),
    ∃ E : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := T.m₁) (K := k + 1) T.m₀ (k + 1)
        Set.univ) → ℂ,
      S.M0C (zeroClass d L N₁ T.m₁ k N ϱ) g y i =
        ((S.betaU ^ (1 / 2 : ℝ) : ℝ) : ℂ) * ∑ T', E T' ∧
      (∀ T', rootCube (m₀ := T.m₀) (blockIndex y) ∉ T' → E T' = 0) ∧
      (∀ T', ‖E T'‖ ≤ Cthm * obsPrefactor p s b * Real.exp (-(3 / 2 * T.κdec) * dExt T')) ∧
      ∀ T', E T' ≠ 0 → IsPolyDom T.m₀ (k + 1) (sitesOf T')) := by
  classical
  obtain ⟨Cthm, hC, hat⟩ := thm31b_zeroClass_at_of_ray_supp_rhoG T hA p hCR hs0 hs
  obtain ⟨CE, CF, hCE, hCF, hj⟩ :=
    commonWitness_joint_fromTowerG_rho_full T C hKc hKall hH h0 h' hA p
  refine ⟨CE, CF, Cthm, hCE, hCF, hC, ?_⟩
  intro ρ hρ
  obtain ⟨β₀a, hβa, hat⟩ := hat ρ hρ
  obtain ⟨β₀j, hβj, hρj, hj⟩ := hj ρ hρ
  refine ⟨max β₀a β₀j, le_trans hβj (le_max_right _ _), le_trans hρj (le_max_right _ _), ?_⟩
  intro k hk N₁ _ hLN hN ν hν hνk β hβ b hb p₁ hp0 hp₁ D ϱ hϱ S hS hp
  obtain ⟨val, 𝒴, Tt, hdom, H⟩ := hj k hk N₁ hLN hN ν hν hνk β (le_trans (le_max_right _ _) hβ)
    b hb p₁ hp0 hp₁ D ϱ hϱ S hS hp
  have H' := H
  obtain ⟨hval, εU, -, -, -, -, -, -, -, -, ⟨hcont, hI, hmem0, hmemg, hrayTt⟩, -⟩ := H'
  refine ⟨val, 𝒴, Tt, hdom, H.1, H.2, ?_⟩
  intro g hg y i
  exact hat k hk N₁ hLN hN ν hν hνk β (le_trans (le_max_left _ _) hβ) b hb p₁ hp0 hp₁ D ϱ hϱ S hS hp
    val 𝒴 Tt hval hcont hI hmem0 hmemg hrayTt g hg y i

open Classical in
/-- **`thm31b_onCommonWitness_fromTower_supp` at source radius `ρ`.**  The constants
`C_E, C_F, C` do not depend on `ρ`; for each `ρ > 0` the threshold `β₀` satisfies `3 ≤ β₀` and
`ρ ≤ β₀`.  The witness clauses are those of `commonWitness_joint_fromTower_rho_full` (slice `ρ/β`,
sources of `ℓ¹`-size `< ρ`), and the coefficient `E = obsCoeff I` is given for every `g` of the
`ℓ¹` ball of radius `ρ`. -/
theorem thm31b_onCommonWitness_fromTower_supp_rho {κmin : ℝ} (T : StepTower κmin)
    (hHull : stepHullMin ≤ κmin) {A₁ : ℝ}
    (hA : 0 < A₁) (p : ℕ) {CR s : ℝ}
    (hCR : 0 < CR) (hs0 : 0 < s) (hs : s < 1 / 2) :
    ∃ CE CF C : ℝ, 0 < CE ∧ 0 < CF ∧ 0 ≤ C ∧
  ∀ ρ : ℝ, 0 < ρ → ∃ β₀ : ℝ, 3 ≤ β₀ ∧ ρ ≤ β₀ ∧
  ∀ (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁] (h3N : 3 ∣ N₁), 5 < N₁ →
  ∀ ν : ℝ, 0 < ν → ν * 3 ^ (2 * (k + 1)) ≤ 1 →
  ∀ β : ℝ, β₀ ≤ β → ∀ (p₁ : ℝ) (hp0 : 0 < p₁),
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
      (∃ εU : ℝ,
      εU = β * prop33EpsEtaScaled 3 3 2 T.m₁ k 1 1 T.BG T.BG₂ T.κ T.t
        (lvR T.κ T.t (β * 3 ^ k) p₁) 0 0 (ρ / β) ∧ 0 < εU ∧
      4 * εU ≤ CE * (Real.log (β * 3 ^ k)) ^ (3 * p) / Real.sqrt (β * 3 ^ k) +
        ρ * CF * (Real.log (β * 3 ^ k)) ^ p / Real.sqrt (β * 3 ^ k) ∧
      (∀ g : Fld 3 3 N₁ T.m₁ (k + 1) 2, g ∈ l1BallRho 3 3 N₁ T.m₁ (k + 1) 2 ρ →
        ∃ BR : StepActivityBound S (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) g,
        ∃ BC : StepActivityBoundC S (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) g,
          BR.m₀ = 1 ∧ BC.m₀ = 1 ∧ BR.Lb = ({Y // Y ∈ 𝒴} ⊕ {Y // Y ∈ 𝒴}) ∧ BC.Lb = BR.Lb ∧
          HEq BR.Lab ((thickLabels 𝒴 hdom).sum (thickLabels 𝒴 hdom)) ∧ HEq BC.Lab BR.Lab ∧
          HEq BR.BS (S.blockSplit 1 hp) ∧ HEq BC.BS BR.BS ∧
          BR.κ0 = T.κ0 ∧ BC.κ0 = T.κ0 ∧ BR.κ' = T.κ' ∧ BC.κ' = T.κ' ∧
          BR.κH = 2 * T.κdec - 1 ∧ BC.κH = BR.κH ∧
          BR.Kc = 2 * (K0 3 3 T.κ0 + 1) ∧ BC.Kc = BR.Kc ∧ BR.εH = BC.εH ∧ BR.εH = 4 * εU) ∧
      (∃ Jr : S.JointRep T.t (2 * p₁),
        ∃ Aseg : ∀ e : physParam 2 S, e ∈ physFibreRho S S.a₁ S.ν T.t ρ → ℝ × ℝ →
          LabelAct ((thickLabels 𝒴 hdom).sum (thickLabels 𝒴 hdom)) (S.blockSplit 1 hp).Ωb
            (4 * εU) (2 * T.κdec - 1) T.κ0 (2 * (K0 3 3 T.κ0 + 1)),
        (∀ (e : physParam 2 S) (he : e ∈ physFibreRho S S.a₁ S.ν T.t ρ), ∀ p ∈ stepSegments,
          ∀ᵐ x ∂S.nuFl,
            Jr.W1 (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁))
                ((e.1 : RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2), (p.1 : ℂ) • S.hatC x) +
              Jr.W2 (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) e.2
                ((e.1 : RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2), (p.2 : ℂ) • S.hatC x) =
            ∑ y, (Aseg e he p).H y ((S.blockSplit 1 hp).restr x)) ∧
        (∀ g : Fld 3 3 N₁ T.m₁ (k + 1) 2, ∑ x, ∑ i, ‖g x i‖ < ρ →
          ∃ he : ((⟨rawOf S.D', rawOf_mem_rawSub _⟩ : rawSub 2 S.G'), g) ∈
              physFibreRho S S.a₁ S.ν T.t ρ,
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
        ∀ g : Fld 3 3 N₁ T.m₁ (k + 1) 2, g ∈ l1BallRho 3 3 N₁ T.m₁ (k + 1) 2 ρ →
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
              S.WtwoC (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) g t x) ∧
      (∃ (Jr : S.JointRep T.t (2 * p₁))
          (I : DirectTerms S 1 hp (fun ψ => (ψ, ψ)) p₁ 2
                (S.β * prop33EpsEtaScaled 3 3 2 T.m₁ k 1 S.a₁ T.BG T.BG₂ T.κ T.t
                  (lvR T.κ T.t (β * 3 ^ k) p₁) 0 0 (ρ / S.β)) (2 * T.κdec - 1)
                (rawOf S.D', (0 : CTorus 3 3 N₁ T.m₁ (k + 1) → Fin 2 → ℂ))
                (physSΛEta S S.a₁ S.ν T.t (ρ / S.β))
                (physXW S (lvCpsi T.κ T.t (β * 3 ^ k)) 2 2 (lvR T.κ T.t (β * 3 ^ k) p₁)) val
                (physAgΘ S) (AgFDirPair S)),
          I.𝒴 = 𝒴 ∧ I.T = Tt ∧
          ∃ (hF : DirectTermsFamilyOn S 1 (physInclScaled 2 S (((1 / S.β : ℝ)) : ℂ)) I
              (physVqRho S S.a₁ S.ν T.t ρ ρ))
            (hεU : 0 ≤ S.β * prop33EpsEtaScaled 3 3 2 T.m₁ k 1 S.a₁ T.BG T.BG₂ T.κ T.t
                  (lvR T.κ T.t (β * 3 ^ k) p₁) 0 0 (ρ / S.β)),
            0 < S.β * prop33EpsEtaScaled 3 3 2 T.m₁ k 1 S.a₁ T.BG T.BG₂ T.κ T.t
                  (lvR T.κ T.t (β * 3 ^ k) p₁) 0 0 (ρ / S.β) ∧
            ∀ {Kc : ℝ} (hKc : K0 3 3 T.κ0 ≤ Kc),
            ∃ A : physParam 2 S → ℂ → LabelAct (thickLabels I.𝒴 I.dom) (S.blockSplit 1 hp).Ωb
                (2 * (S.β * prop33EpsEtaScaled 3 3 2 T.m₁ k 1 S.a₁ T.BG T.BG₂ T.κ T.t
                  (lvR T.κ T.t (β * 3 ^ k) p₁) 0 0 (ρ / S.β))) (2 * T.κdec - 1) T.κ0 Kc,
              A = labelActFamilyOn S 1 (physInclScaled 2 S (((1 / S.β : ℝ)) : ℂ)) I hF
                    (show 3 ^ 1 ∣ N₁ by simpa using h3N) hp0 (by norm_num) hεU T.κ0_ent hKc ∧
              (∀ (y : {Y // Y ∈ I.𝒴}) (Φ : ∀ b, (S.blockSplit 1 hp).Ωb b),
                AnalyticOnNhd ℂ (fun r : physParam 2 S × ℂ => (A r.1 r.2).H y Φ)
                  (physVqRho S S.a₁ S.ν T.t ρ ρ ×ˢ Metric.ball (0 : ℂ) 2)) ∧
              (∀ e ∈ physVqRho S S.a₁ S.ν T.t ρ ρ, ∀ u : ℂ, ‖u‖ < 2 → ∀ y : {Y // Y ∈ I.𝒴},
                Continuous ((A e u).H y)) ∧
              (∀ e ∈ physVqRho S S.a₁ S.ν T.t ρ ρ, ∀ u : ℂ, ‖u‖ < 2 →
                ∀ Φ : ∀ b, (S.blockSplit 1 hp).Ωb b,
                ∑ y, (A e u).H y Φ =
                  val (S.hatOf 1 p₁ hp Φ, S.hatOf 1 p₁ hp Φ)
                    (S.hatOf 1 p₁ hp Φ, S.hatOf 1 p₁ hp Φ) u
                    (physInclScaled 2 S (((1 / S.β : ℝ)) : ℂ) e)) ∧
              (∀ᵐ x ∂S.nuFl, ∀ e ∈ physVqRho S S.a₁ S.ν T.t ρ ρ, ∀ u : ℂ, ‖u‖ < 2 →
                ∑ y, (A e u).H y ((S.blockSplit 1 hp).restr x) =
                  val (S.hatC x, S.hatC x) (S.hatC x, S.hatC x) u
                    (physInclScaled 2 S (((1 / S.β : ℝ)) : ℂ) e)) ∧
              (∀ᵐ x ∂S.nuFl, ∀ e ∈ physFibreRho S S.a₁ S.ν T.t ρ, ∀ s ∈ Icc (0 : ℝ) 1,
                Jr.W1 (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁))
                    ((e.1 : RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2), (s : ℂ) • S.hatC x) =
                  (s : ℂ) ^ 2 * ∑ y, (A ((e.1, 0) : physParam 2 S) (s : ℂ)).H y
                    ((S.blockSplit 1 hp).restr x)) ∧
              (∀ᵐ x ∂S.nuFl, ∀ e ∈ physFibreRho S S.a₁ S.ν T.t ρ, ∑ x', ∑ i, ‖e.2 x' i‖ < ρ →
                ∀ t ∈ Icc (0 : ℝ) 1,
                Jr.W2 (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) e.2
                    ((e.1 : RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2), (t : ℂ) • S.hatC x) =
                  ∑ y, (A e (t : ℂ)).H y ((S.blockSplit 1 hp).restr x) -
                    ∑ y, (A ((e.1, 0) : physParam 2 S) (t : ℂ)).H y
                      ((S.blockSplit 1 hp).restr x)) ∧
              (∀ᵐ x ∂S.nuFl, ∀ (D' : BgData S.G' 2) (hDh : ∀ y i, D'.h y i = (S.h₀ i : ℂ)),
                XiCData S.G' S.a S.ν (k + 1) 1 T.t D' → ∀ s ∈ Icc (0 : ℝ) 1,
                (S.withDatum D' hDh).WoneC (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) s x =
                  (s : ℂ) ^ 2 * ∑ y, (A ((⟨rawOf D', rawOf_mem_rawSub _⟩ : rawSub 2 S.G'),
                    (0 : CTorus 3 3 N₁ T.m₁ (k + 1) → Fin 2 → ℂ)) (s : ℂ)).H y
                    ((S.blockSplit 1 hp).restr x)) ∧
              (∀ᵐ x ∂S.nuFl, ∀ (D' : BgData S.G' 2) (hDh : ∀ y i, D'.h y i = (S.h₀ i : ℂ)),
                XiCData S.G' S.a S.ν (k + 1) 1 T.t D' →
                ∀ g : Fld 3 3 N₁ T.m₁ (k + 1) 2, ∑ x', ∑ i, ‖g x' i‖ < ρ → ∀ t ∈ Icc (0 : ℝ) 1,
                (S.withDatum D' hDh).WtwoC (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) g t x =
                  ∑ y, (A ((⟨rawOf D', rawOf_mem_rawSub _⟩ : rawSub 2 S.G'), g) (t : ℂ)).H y
                      ((S.blockSplit 1 hp).restr x) -
                    ∑ y, (A ((⟨rawOf D', rawOf_mem_rawSub _⟩ : rawSub 2 S.G'),
                      (0 : CTorus 3 3 N₁ T.m₁ (k + 1) → Fin 2 → ℂ)) (t : ℂ)).H y
                      ((S.blockSplit 1 hp).restr x)) ∧
              (∀ᵐ x ∂S.nuFl, ∀ e ∈ physFibreRho S S.a₁ S.ν T.t ρ, ∑ x', ∑ i, ‖e.2 x' i‖ < ρ →
                ∀ p ∈ stepSegments,
                Jr.W1 (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁))
                    ((e.1 : RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2), (p.1 : ℂ) • S.hatC x) +
                  Jr.W2 (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) e.2
                    ((e.1 : RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2), (p.2 : ℂ) • S.hatC x) =
                  ∑ y, (segAct (A ((e.1, 0) : physParam 2 S)) (A e)
                    (mul_nonneg zero_le_two hεU) (two_mul _).ge
                    (fun s => ((if s ∈ Icc (0 : ℝ) 1 then s ^ 2 else 0 : ℝ) : ℂ))
                    norm_ite_sq_le p).H y ((S.blockSplit 1 hp).restr x)) ∧
              (∀ (y : {Y // Y ∈ I.𝒴}) (Φ : ∀ b, (S.blockSplit 1 hp).Ωb b),
                AnalyticOnNhd ℂ (fun r : physParam 2 S × ℂ =>
                  (zeroSourceAct A 2 zero_le_two r.1 r.2).H y Φ)
                  (physVRho S S.a₁ S.ν T.t ρ ×ˢ Metric.ball (0 : ℂ) 2)) ∧
              (∀ e ∈ physVRho S S.a₁ S.ν T.t ρ, ∀ u ∈ Metric.ball (0 : ℂ) 2, ∀ y : {Y // Y ∈ I.𝒴},
                Continuous ((zeroSourceAct A 2 zero_le_two e u).H y)) ∧
              (∀ (D' : BgData S.G' 2) (hDh : ∀ y i, D'.h y i = (S.h₀ i : ℂ)),
                XiCData S.G' S.a S.ν (k + 1) 1 T.t D' → ∀ g : Fld 3 3 N₁ T.m₁ (k + 1) 2,
                ∀ s : ℝ, s ∈ Icc (0 : ℝ) 1 → ∀ᵐ x ∂S.nuFl,
                  (S.withDatum D' hDh).WoneC (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) s x =
                    ∑ y, (zeroSourceAct A 2 zero_le_two
                      ((⟨rawOf D', rawOf_mem_rawSub _⟩ : rawSub 2 S.G'), g) (s : ℂ)).H y
                      ((S.blockSplit 1 hp).restr x))) ∧
      (∀ (Y : Set (CTorus 3 3 N₁ T.m₁ (k + 1)))
        (Θ : RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2 × (CTorus 3 3 N₁ T.m₁ (k + 1) → Fin 2 → ℂ)),
        Θ ∈ physSΛEta S S.a₁ S.ν T.t (ρ / S.β) → ∀ ψ : S.U × Fin 2 → ℂ,
        (∀ p, ‖ψ p‖ ≤ p₁) →
        DifferentiableOn ℂ (fun ζ : ℂ => Tt Y (ζ • ψ, ζ • ψ) (ζ • ψ, ζ • ψ) 1 Θ)
          (Metric.ball (0 : ℂ) (3 / 2))) ∧
      (DiagCont (fun ψ : S.U × Fin 2 → ℂ => (ψ, ψ))
          (physXW S (lvCpsi T.κ T.t (β * 3 ^ k)) 2 2 (lvR T.κ T.t (β * 3 ^ k) p₁))
          (physSΛEta S S.a₁ S.ν T.t (ρ / S.β)) 2 𝒴 Tt ∧
        (∀ Θ ∈ physSΛEta S S.a₁ S.ν T.t (ρ / S.β),
          ∃ I : DirectTerms S 1 hp (fun ψ => (ψ, ψ)) p₁ 2
              (S.β * prop33EpsEtaScaled 3 3 2 T.m₁ k 1 S.a₁ T.BG T.BG₂ T.κ T.t
                (lvR T.κ T.t (β * 3 ^ k) p₁) 0 0 (ρ / S.β)) (2 * T.κdec - 1) Θ
              (physSΛEta S S.a₁ S.ν T.t (ρ / S.β))
              (physXW S (lvCpsi T.κ T.t (β * 3 ^ k)) 2 2 (lvR T.κ T.t (β * 3 ^ k) p₁)) val
              (physAgΘ S) (AgFDirPair S),
            I.𝒴 = 𝒴 ∧ I.T = Tt) ∧
        (rawOf S.D', (0 : CTorus 3 3 N₁ T.m₁ (k + 1) → Fin 2 → ℂ)) ∈
          physSΛEta S S.a₁ S.ν T.t (ρ / S.β) ∧
        (∀ g : Fld 3 3 N₁ T.m₁ (k + 1) 2, ∑ x, ∑ i, ‖g x i‖ < ρ →
          (rawOf S.D', fun y i => g y i / (S.β : ℂ)) ∈ physSΛEta S S.a₁ S.ν T.t (ρ / S.β)) ∧
        (∀ Y ∈ 𝒴, ∀ Θ ∈ physSΛEta S S.a₁ S.ν T.t (ρ / S.β),
          ∀ ψ ∈ hatDisk S.U 2 p₁,
            DifferentiableOn ℂ (fun z : ℂ => Tt Y (z • ψ, z • ψ) (z • ψ, z • ψ) 1 Θ)
              (Metric.ball (0 : ℂ) (3 / 2)))) ∧
      (∃ (Jr : S.JointRep T.t (2 * p₁))
          (I : DirectTerms S 1 hp (fun ψ => (ψ, ψ)) p₁ 2
                (S.β * prop33EpsEtaScaled 3 3 2 T.m₁ k 1 S.a₁ T.BG T.BG₂ T.κ T.t
                  (lvR T.κ T.t (β * 3 ^ k) p₁) 0 0 (ρ / S.β)) (2 * T.κdec - 1)
                (rawOf S.D', (0 : CTorus 3 3 N₁ T.m₁ (k + 1) → Fin 2 → ℂ))
                (physSΛEta S S.a₁ S.ν T.t (ρ / S.β))
                (physXW S (lvCpsi T.κ T.t (β * 3 ^ k)) 2 2 (lvR T.κ T.t (β * 3 ^ k) p₁)) val
                (physAgΘ S) (AgFDirPair S)),
          I.𝒴 = 𝒴 ∧ I.T = Tt ∧
          ∃ (hF : DirectTermsFamilyOn S 1 (physInclScaled 2 S (((1 / S.β : ℝ)) : ℂ)) I
              (physVqRho S S.a₁ S.ν T.t ρ ρ))
            (hεU : 0 ≤ S.β * prop33EpsEtaScaled 3 3 2 T.m₁ k 1 S.a₁ T.BG T.BG₂ T.κ T.t
                  (lvR T.κ T.t (β * 3 ^ k) p₁) 0 0 (ρ / S.β)),
            0 < S.β * prop33EpsEtaScaled 3 3 2 T.m₁ k 1 S.a₁ T.BG T.BG₂ T.κ T.t
                  (lvR T.κ T.t (β * 3 ^ k) p₁) 0 0 (ρ / S.β) ∧
            (
          0 < 2 ^ 2 * (2 * (S.β * prop33EpsEtaScaled 3 3 2 T.m₁ k 1 S.a₁ T.BG T.BG₂ T.κ T.t
                  (lvR T.κ T.t (β * 3 ^ k) p₁) 0 0 (ρ / S.β))) ∧
          2 ^ 2 * (2 * (S.β * prop33EpsEtaScaled 3 3 2 T.m₁ k 1 S.a₁ T.BG T.BG₂ T.κ T.t
                  (lvR T.κ T.t (β * 3 ^ k) p₁) 0 0 (ρ / S.β))) ≤
              2 * CE * (Real.log (β * 3 ^ k)) ^ (3 * p) / Real.sqrt (β * 3 ^ k) +
                2 * (ρ * CF) * (Real.log (β * 3 ^ k)) ^ p / Real.sqrt (β * 3 ^ k) ∧
          2 ^ 2 * (2 * (S.β * prop33EpsEtaScaled 3 3 2 T.m₁ k 1 S.a₁ T.BG T.BG₂ T.κ T.t
                  (lvR T.κ T.t (β * 3 ^ k) p₁) 0 0 (ρ / S.β))) ≤
              (stepOutputPhysical T hHull).theta ∧
          2 ^ 2 * (2 * (S.β * prop33EpsEtaScaled 3 3 2 T.m₁ k 1 S.a₁ T.BG T.BG₂ T.κ T.t
                  (lvR T.κ T.t (β * 3 ^ k) p₁) 0 0 (ρ / S.β))) ≤
              stepTheta 3 3 T.marksKc' (2 * T.κdec - 1) T.κ0 T.κ' ∧
          ∃ A : physParam 2 S → ℂ → LabelAct (thickLabels I.𝒴 I.dom) (S.blockSplit 1 hp).Ωb
              (2 * (S.β * prop33EpsEtaScaled 3 3 2 T.m₁ k 1 S.a₁ T.BG T.BG₂ T.κ T.t
                (lvR T.κ T.t (β * 3 ^ k) p₁) 0 0 (ρ / S.β))) (2 * T.κdec - 1) T.κ0
              (2 * (K0 3 3 T.κ0 + 1)),
            A = labelActFamilyOn S 1 (physInclScaled 2 S (((1 / S.β : ℝ)) : ℂ)) I hF
                  (show 3 ^ 1 ∣ N₁ by simpa using h3N) hp0 (by norm_num) hεU T.κ0_ent
                  T.marks_K0_le ∧
            (∀ᵐ x ∂S.nuFl, ∀ e ∈ physFibreRho S S.a₁ S.ν T.t ρ, ∀ s ∈ Icc (0 : ℝ) 1,
              Jr.W1 (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁))
                  ((e.1 : RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2), (s : ℂ) • S.hatC x) =
                (s : ℂ) ^ 2 * ∑ y, (A ((e.1, 0) : physParam 2 S) (s : ℂ)).H y
                  ((S.blockSplit 1 hp).restr x)) ∧
            (∀ᵐ x ∂S.nuFl, ∀ e ∈ physFibreRho S S.a₁ S.ν T.t ρ, ∑ x', ∑ i, ‖e.2 x' i‖ < ρ →
              ∀ t ∈ Icc (0 : ℝ) 1,
              Jr.W2 (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) e.2
                  ((e.1 : RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2), (t : ℂ) • S.hatC x) =
                ∑ y, (A e (t : ℂ)).H y ((S.blockSplit 1 hp).restr x) -
                  ∑ y, (A ((e.1, 0) : physParam 2 S) (t : ℂ)).H y
                    ((S.blockSplit 1 hp).restr x)) ∧
            ∀ {ι : Type} [Fintype ι] (reads : ι → Set (CTorus 3 3 N₁ T.m₁ (k + 1)))
              (dom : ι → Finset (Set (CTorus 3 3 N₁ T.m₁ (k + 1))))
              (hdomR : ∀ b, ∀ Y ∈ dom b, IsDj 1 (k + 1) Y),
            ∃ A0 : physParam 2 S → ℂ → LabelAct
                (commonLabels (thickLabels I.𝒴 I.dom) (show 3 ^ 1 ∣ N₁ by simpa using h3N)
                  (by norm_num) reads dom hdomR) (S.blockSplit 1 hp).Ωb
                (2 ^ 2 * (2 * (S.β * prop33EpsEtaScaled 3 3 2 T.m₁ k 1 S.a₁ T.BG T.BG₂ T.κ T.t
                  (lvR T.κ T.t (β * 3 ^ k) p₁) 0 0 (ρ / S.β)))) (2 * T.κdec - 1) T.κ0 T.marksKc',
              A0 = commonAct (zeroSourceAct A 2 (by norm_num))
                  (show 3 ^ 1 ∣ N₁ by simpa using h3N) (by norm_num) reads dom hdomR
                  (mul_nonneg (sq_nonneg 2) (mul_nonneg zero_le_two hεU)) T.κ0_two ∧
              (∀ y (Φ : ∀ b, (S.blockSplit 1 hp).Ωb b),
                AnalyticOnNhd ℂ (fun r : physParam 2 S × ℂ => (A0 r.1 r.2).H y Φ)
                  (physVRho S S.a₁ S.ν T.t ρ ×ˢ ball (0 : ℂ) 2)) ∧
              (∀ e ∈ physVRho S S.a₁ S.ν T.t ρ, ∀ y (Φ : ∀ b, (S.blockSplit 1 hp).Ωb b),
                DifferentiableOn ℂ (fun u => (A0 e u).H y Φ) (ball (0 : ℂ) 2)) ∧
              (∀ y, ∀ e ∈ physVRho S S.a₁ S.ν T.t ρ, ∀ u ∈ ball (0 : ℂ) 2,
                Continuous ((A0 e u).H y)) ∧
              (∀ (e : physParam 2 S) (u : ℂ) (Φ : ∀ b, (S.blockSplit 1 hp).Ωb b),
                ∑ y, (A0 e u).H y Φ =
                  sqFactor 2 u * ∑ y, (A ((e.1, 0) : physParam 2 S) u).H y Φ) ∧
              (∀ (D' : BgData S.G' 2) (hDh : ∀ y i, D'.h y i = (S.h₀ i : ℂ)),
                XiCData S.G' S.a S.ν (k + 1) 1 T.t D' → ∀ g : Fld 3 3 N₁ T.m₁ (k + 1) 2,
                ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ᵐ x ∂S.nuFl,
                  (S.withDatum D' hDh).WoneC (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) s x =
                    ∑ y, (A0 ((⟨rawOf D', rawOf_mem_rawSub _⟩ : rawSub 2 S.G'), g) (s : ℂ)).H y
                      ((S.blockSplit 1 hp).restr x)) ∧
              (∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ᵐ x ∂S.nuFl,
                S.WoneC (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) s x =
                  ∑ y, (A0 ((⟨rawOf S.D', rawOf_mem_rawSub _⟩ : rawSub 2 S.G'),
                    (0 : CTorus 3 3 N₁ T.m₁ (k + 1) → Fin 2 → ℂ)) (s : ℂ)).H y
                    ((S.blockSplit 1 hp).restr x)) ∧
              Nonempty (ParamMarkFamily (S.blockSplit 1 hp).μ
                (commonLabels (thickLabels I.𝒴 I.dom) (show 3 ^ 1 ∣ N₁ by simpa using h3N)
                  (by norm_num) reads dom hdomR) A0
                (fun i : Empty => i.elim) (fun _ _ _ _ => (0 : ℂ)) 0 (fun i : Empty => i.elim)
                (physVRho S S.a₁ S.ν T.t ρ) (ball (0 : ℂ) 2) (physCarrier S 1 hp)) ∧
              (∀ _y₀ : {Y // Y ∈ I.𝒴} ⊕ RootUnionLb 1 reads dom,
                Nonempty (InterpMarks S.nuFl (S.blockSplit 1 hp)
                  (S.WoneC (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁))) (fun _ _ => (0 : ℂ))))))) ∧
    (∀ g : Fld 3 3 N₁ T.m₁ (k + 1) 2,
    g ∈ l1BallRho 3 3 N₁ T.m₁ (k + 1) 2 ρ →
  ∀ (y : CTorus 3 3 N₁ T.m₁ (k + 1)) (i : Fin 2),
    ∃ E : Finset (CubeB (d := 3) (L := 3) (N₁ := N₁) (m₁ := T.m₁) (K := k + 1) 1 (k + 1)
        Set.univ) → ℂ,
      S.M0C (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) g y i =
        ((S.betaU ^ (1 / 2 : ℝ) : ℝ) : ℂ) * ∑ T', E T' ∧
      (∀ T', rootCube (m₀ := 1) (blockIndex y) ∉ T' → E T' = 0) ∧
      (∀ T', ‖E T'‖ ≤ C * obsPrefactor p s (β * 3 ^ k) * Real.exp (-(3 / 2 * T.κdec) * dExt T')) ∧
      ∀ T', E T' ≠ 0 → IsPolyDom 1 (k + 1) (sitesOf T')) := by
  classical
  obtain ⟨CE, CF, Cthm, hCE, hCF, hC, H⟩ :=
    thm31b_onCommonWitness_fromTowerG_supp_rho T.toG (stepOutputPhysical T hHull) rfl rfl rfl
      rfl rfl hA p hCR hs0 hs
  refine ⟨CE, CF, Cthm, hCE, hCF, hC, fun ρ hρ => ?_⟩
  obtain ⟨β₀, h3, hρβ, H1⟩ := H ρ hρ
  refine ⟨β₀, h3, hρβ, ?_⟩
  intro k hk N₁ _ h3N hN ν hνpos hν β hβ p₁ hp0 hp₁ D S hS hp
  exact H1 k hk N₁ (by simpa using h3N) hN ν hνpos (by simpa using hν) β hβ (β * 3 ^ k)
    (by norm_num) p₁ hp0 hp₁ (StepTower.scaleDataG_of_fixed T D) _ (rhoSepG_three _).symm S
    (by rw [hS]; exact (StepTower.toG_step_heq T k hk N₁ ν β p₁).symm) hp

open Classical in
/-- **Theorem 3.1 (b) on the common source witness, with the coefficients on polymer sets.**  As
`thm31b_onCommonWitness_fromTower`, and moreover the coefficient `E` is `obsCoeff I` for the record
`I` of `obsMarks_zeroClass_at_of_ray_ksupp`, so `E T' ≠ 0` only if `sitesOf T'` is a polymer
domain (`IsPolyDom 1 (k+1)`; equivalently `dOmega 1 (k+1) univ (sitesOf T') ≠ ⊤` for nonempty
`T'`).  The kernel `I.hker` of the record is supported on the labels of the domains of the
expansion (`dOmega_ne_top_of_obsHker_ne_zero`).  The output rate `(3/2) κ_dec` is not claimed to be
positive.  The landed `thm31b_onCommonWitness_fromTower` is not a corollary of this statement in
Lean only because it sits upstream of `Thm31bPolymerSupport`, which this proof uses. -/
theorem thm31b_onCommonWitness_fromTower_supp {κmin : ℝ} (T : StepTower κmin)
    (hHull : stepHullMin ≤ κmin) {A₁ : ℝ}
    (hA : 0 < A₁) (p : ℕ) {CR s : ℝ}
    (hCR : 0 < CR) (hs0 : 0 < s) (hs : s < 1 / 2) :
    ∃ β₀ CE CF C : ℝ, 3 ≤ β₀ ∧ 0 < CE ∧ 0 < CF ∧ 0 ≤ C ∧
  ∀ (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁] (h3N : 3 ∣ N₁), 5 < N₁ →
  ∀ ν : ℝ, 0 < ν → ν * 3 ^ (2 * (k + 1)) ≤ 1 →
  ∀ β : ℝ, β₀ ≤ β → ∀ (p₁ : ℝ) (hp0 : 0 < p₁),
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
      (∃ εU : ℝ,
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
              S.WtwoC (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) g t x) ∧
      (∃ (Jr : S.JointRep T.t (2 * p₁))
          (I : DirectTerms S 1 hp (fun ψ => (ψ, ψ)) p₁ 2
                (S.β * prop33EpsEtaScaled 3 3 2 T.m₁ k 1 S.a₁ T.BG T.BG₂ T.κ T.t
                  (lvR T.κ T.t (β * 3 ^ k) p₁) 0 0 (1 / S.β)) (2 * T.κdec - 1)
                (rawOf S.D', (0 : CTorus 3 3 N₁ T.m₁ (k + 1) → Fin 2 → ℂ))
                (physSΛEta S S.a₁ S.ν T.t (1 / S.β))
                (physXW S (lvCpsi T.κ T.t (β * 3 ^ k)) 2 2 (lvR T.κ T.t (β * 3 ^ k) p₁)) val
                (physAgΘ S) (AgFDirPair S)),
          I.𝒴 = 𝒴 ∧ I.T = Tt ∧
          ∃ (hF : DirectTermsFamilyOn S 1 (physInclScaled 2 S (((1 / S.β : ℝ)) : ℂ)) I
              (physVq S S.a₁ S.ν T.t 1))
            (hεU : 0 ≤ S.β * prop33EpsEtaScaled 3 3 2 T.m₁ k 1 S.a₁ T.BG T.BG₂ T.κ T.t
                  (lvR T.κ T.t (β * 3 ^ k) p₁) 0 0 (1 / S.β)),
            0 < S.β * prop33EpsEtaScaled 3 3 2 T.m₁ k 1 S.a₁ T.BG T.BG₂ T.κ T.t
                  (lvR T.κ T.t (β * 3 ^ k) p₁) 0 0 (1 / S.β) ∧
            ∀ {Kc : ℝ} (hKc : K0 3 3 T.κ0 ≤ Kc),
            ∃ A : physParam 2 S → ℂ → LabelAct (thickLabels I.𝒴 I.dom) (S.blockSplit 1 hp).Ωb
                (2 * (S.β * prop33EpsEtaScaled 3 3 2 T.m₁ k 1 S.a₁ T.BG T.BG₂ T.κ T.t
                  (lvR T.κ T.t (β * 3 ^ k) p₁) 0 0 (1 / S.β))) (2 * T.κdec - 1) T.κ0 Kc,
              A = labelActFamilyOn S 1 (physInclScaled 2 S (((1 / S.β : ℝ)) : ℂ)) I hF
                    (show 3 ^ 1 ∣ N₁ by simpa using h3N) hp0 (by norm_num) hεU T.κ0_ent hKc ∧
              (∀ (y : {Y // Y ∈ I.𝒴}) (Φ : ∀ b, (S.blockSplit 1 hp).Ωb b),
                AnalyticOnNhd ℂ (fun r : physParam 2 S × ℂ => (A r.1 r.2).H y Φ)
                  (physVq S S.a₁ S.ν T.t 1 ×ˢ Metric.ball (0 : ℂ) 2)) ∧
              (∀ e ∈ physVq S S.a₁ S.ν T.t 1, ∀ u : ℂ, ‖u‖ < 2 → ∀ y : {Y // Y ∈ I.𝒴},
                Continuous ((A e u).H y)) ∧
              (∀ e ∈ physVq S S.a₁ S.ν T.t 1, ∀ u : ℂ, ‖u‖ < 2 →
                ∀ Φ : ∀ b, (S.blockSplit 1 hp).Ωb b,
                ∑ y, (A e u).H y Φ =
                  val (S.hatOf 1 p₁ hp Φ, S.hatOf 1 p₁ hp Φ)
                    (S.hatOf 1 p₁ hp Φ, S.hatOf 1 p₁ hp Φ) u
                    (physInclScaled 2 S (((1 / S.β : ℝ)) : ℂ) e)) ∧
              (∀ᵐ x ∂S.nuFl, ∀ e ∈ physVq S S.a₁ S.ν T.t 1, ∀ u : ℂ, ‖u‖ < 2 →
                ∑ y, (A e u).H y ((S.blockSplit 1 hp).restr x) =
                  val (S.hatC x, S.hatC x) (S.hatC x, S.hatC x) u
                    (physInclScaled 2 S (((1 / S.β : ℝ)) : ℂ) e)) ∧
              (∀ᵐ x ∂S.nuFl, ∀ e ∈ physFibre S S.a₁ S.ν T.t, ∀ s ∈ Icc (0 : ℝ) 1,
                Jr.W1 (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁))
                    ((e.1 : RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2), (s : ℂ) • S.hatC x) =
                  (s : ℂ) ^ 2 * ∑ y, (A ((e.1, 0) : physParam 2 S) (s : ℂ)).H y
                    ((S.blockSplit 1 hp).restr x)) ∧
              (∀ᵐ x ∂S.nuFl, ∀ e ∈ physFibre S S.a₁ S.ν T.t, ∑ x', ∑ i, ‖e.2 x' i‖ < 1 →
                ∀ t ∈ Icc (0 : ℝ) 1,
                Jr.W2 (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) e.2
                    ((e.1 : RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2), (t : ℂ) • S.hatC x) =
                  ∑ y, (A e (t : ℂ)).H y ((S.blockSplit 1 hp).restr x) -
                    ∑ y, (A ((e.1, 0) : physParam 2 S) (t : ℂ)).H y
                      ((S.blockSplit 1 hp).restr x)) ∧
              (∀ᵐ x ∂S.nuFl, ∀ (D' : BgData S.G' 2) (hDh : ∀ y i, D'.h y i = (S.h₀ i : ℂ)),
                XiCData S.G' S.a S.ν (k + 1) 1 T.t D' → ∀ s ∈ Icc (0 : ℝ) 1,
                (S.withDatum D' hDh).WoneC (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) s x =
                  (s : ℂ) ^ 2 * ∑ y, (A ((⟨rawOf D', rawOf_mem_rawSub _⟩ : rawSub 2 S.G'),
                    (0 : CTorus 3 3 N₁ T.m₁ (k + 1) → Fin 2 → ℂ)) (s : ℂ)).H y
                    ((S.blockSplit 1 hp).restr x)) ∧
              (∀ᵐ x ∂S.nuFl, ∀ (D' : BgData S.G' 2) (hDh : ∀ y i, D'.h y i = (S.h₀ i : ℂ)),
                XiCData S.G' S.a S.ν (k + 1) 1 T.t D' →
                ∀ g : Fld 3 3 N₁ T.m₁ (k + 1) 2, ∑ x', ∑ i, ‖g x' i‖ < 1 → ∀ t ∈ Icc (0 : ℝ) 1,
                (S.withDatum D' hDh).WtwoC (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) g t x =
                  ∑ y, (A ((⟨rawOf D', rawOf_mem_rawSub _⟩ : rawSub 2 S.G'), g) (t : ℂ)).H y
                      ((S.blockSplit 1 hp).restr x) -
                    ∑ y, (A ((⟨rawOf D', rawOf_mem_rawSub _⟩ : rawSub 2 S.G'),
                      (0 : CTorus 3 3 N₁ T.m₁ (k + 1) → Fin 2 → ℂ)) (t : ℂ)).H y
                      ((S.blockSplit 1 hp).restr x)) ∧
              (∀ᵐ x ∂S.nuFl, ∀ e ∈ physFibre S S.a₁ S.ν T.t, ∑ x', ∑ i, ‖e.2 x' i‖ < 1 →
                ∀ p ∈ stepSegments,
                Jr.W1 (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁))
                    ((e.1 : RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2), (p.1 : ℂ) • S.hatC x) +
                  Jr.W2 (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) e.2
                    ((e.1 : RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2), (p.2 : ℂ) • S.hatC x) =
                  ∑ y, (segAct (A ((e.1, 0) : physParam 2 S)) (A e)
                    (mul_nonneg zero_le_two hεU) (two_mul _).ge
                    (fun s => ((if s ∈ Icc (0 : ℝ) 1 then s ^ 2 else 0 : ℝ) : ℂ))
                    norm_ite_sq_le p).H y ((S.blockSplit 1 hp).restr x)) ∧
              (∀ (y : {Y // Y ∈ I.𝒴}) (Φ : ∀ b, (S.blockSplit 1 hp).Ωb b),
                AnalyticOnNhd ℂ (fun r : physParam 2 S × ℂ =>
                  (zeroSourceAct A 2 zero_le_two r.1 r.2).H y Φ)
                  (physV S S.a₁ S.ν T.t ×ˢ Metric.ball (0 : ℂ) 2)) ∧
              (∀ e ∈ physV S S.a₁ S.ν T.t, ∀ u ∈ Metric.ball (0 : ℂ) 2, ∀ y : {Y // Y ∈ I.𝒴},
                Continuous ((zeroSourceAct A 2 zero_le_two e u).H y)) ∧
              (∀ (D' : BgData S.G' 2) (hDh : ∀ y i, D'.h y i = (S.h₀ i : ℂ)),
                XiCData S.G' S.a S.ν (k + 1) 1 T.t D' → ∀ g : Fld 3 3 N₁ T.m₁ (k + 1) 2,
                ∀ s : ℝ, s ∈ Icc (0 : ℝ) 1 → ∀ᵐ x ∂S.nuFl,
                  (S.withDatum D' hDh).WoneC (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) s x =
                    ∑ y, (zeroSourceAct A 2 zero_le_two
                      ((⟨rawOf D', rawOf_mem_rawSub _⟩ : rawSub 2 S.G'), g) (s : ℂ)).H y
                      ((S.blockSplit 1 hp).restr x))) ∧
      (∀ (Y : Set (CTorus 3 3 N₁ T.m₁ (k + 1)))
        (Θ : RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2 × (CTorus 3 3 N₁ T.m₁ (k + 1) → Fin 2 → ℂ)),
        Θ ∈ physSΛEta S S.a₁ S.ν T.t (1 / S.β) → ∀ ψ : S.U × Fin 2 → ℂ,
        (∀ p, ‖ψ p‖ ≤ p₁) →
        DifferentiableOn ℂ (fun ζ : ℂ => Tt Y (ζ • ψ, ζ • ψ) (ζ • ψ, ζ • ψ) 1 Θ)
          (Metric.ball (0 : ℂ) (3 / 2))) ∧
      (DiagCont (fun ψ : S.U × Fin 2 → ℂ => (ψ, ψ))
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
              (Metric.ball (0 : ℂ) (3 / 2)))) ∧
      (∃ (Jr : S.JointRep T.t (2 * p₁))
          (I : DirectTerms S 1 hp (fun ψ => (ψ, ψ)) p₁ 2
                (S.β * prop33EpsEtaScaled 3 3 2 T.m₁ k 1 S.a₁ T.BG T.BG₂ T.κ T.t
                  (lvR T.κ T.t (β * 3 ^ k) p₁) 0 0 (1 / S.β)) (2 * T.κdec - 1)
                (rawOf S.D', (0 : CTorus 3 3 N₁ T.m₁ (k + 1) → Fin 2 → ℂ))
                (physSΛEta S S.a₁ S.ν T.t (1 / S.β))
                (physXW S (lvCpsi T.κ T.t (β * 3 ^ k)) 2 2 (lvR T.κ T.t (β * 3 ^ k) p₁)) val
                (physAgΘ S) (AgFDirPair S)),
          I.𝒴 = 𝒴 ∧ I.T = Tt ∧
          ∃ (hF : DirectTermsFamilyOn S 1 (physInclScaled 2 S (((1 / S.β : ℝ)) : ℂ)) I
              (physVq S S.a₁ S.ν T.t 1))
            (hεU : 0 ≤ S.β * prop33EpsEtaScaled 3 3 2 T.m₁ k 1 S.a₁ T.BG T.BG₂ T.κ T.t
                  (lvR T.κ T.t (β * 3 ^ k) p₁) 0 0 (1 / S.β)),
            0 < S.β * prop33EpsEtaScaled 3 3 2 T.m₁ k 1 S.a₁ T.BG T.BG₂ T.κ T.t
                  (lvR T.κ T.t (β * 3 ^ k) p₁) 0 0 (1 / S.β) ∧
            (
          0 < 2 ^ 2 * (2 * (S.β * prop33EpsEtaScaled 3 3 2 T.m₁ k 1 S.a₁ T.BG T.BG₂ T.κ T.t
                  (lvR T.κ T.t (β * 3 ^ k) p₁) 0 0 (1 / S.β))) ∧
          2 ^ 2 * (2 * (S.β * prop33EpsEtaScaled 3 3 2 T.m₁ k 1 S.a₁ T.BG T.BG₂ T.κ T.t
                  (lvR T.κ T.t (β * 3 ^ k) p₁) 0 0 (1 / S.β))) ≤
              2 * CE * (Real.log (β * 3 ^ k)) ^ (3 * p) / Real.sqrt (β * 3 ^ k) +
                2 * CF * (Real.log (β * 3 ^ k)) ^ p / Real.sqrt (β * 3 ^ k) ∧
          2 ^ 2 * (2 * (S.β * prop33EpsEtaScaled 3 3 2 T.m₁ k 1 S.a₁ T.BG T.BG₂ T.κ T.t
                  (lvR T.κ T.t (β * 3 ^ k) p₁) 0 0 (1 / S.β))) ≤
              (stepOutputPhysical T hHull).theta ∧
          2 ^ 2 * (2 * (S.β * prop33EpsEtaScaled 3 3 2 T.m₁ k 1 S.a₁ T.BG T.BG₂ T.κ T.t
                  (lvR T.κ T.t (β * 3 ^ k) p₁) 0 0 (1 / S.β))) ≤
              stepTheta 3 3 T.marksKc' (2 * T.κdec - 1) T.κ0 T.κ' ∧
          ∃ A : physParam 2 S → ℂ → LabelAct (thickLabels I.𝒴 I.dom) (S.blockSplit 1 hp).Ωb
              (2 * (S.β * prop33EpsEtaScaled 3 3 2 T.m₁ k 1 S.a₁ T.BG T.BG₂ T.κ T.t
                (lvR T.κ T.t (β * 3 ^ k) p₁) 0 0 (1 / S.β))) (2 * T.κdec - 1) T.κ0
              (2 * (K0 3 3 T.κ0 + 1)),
            A = labelActFamilyOn S 1 (physInclScaled 2 S (((1 / S.β : ℝ)) : ℂ)) I hF
                  (show 3 ^ 1 ∣ N₁ by simpa using h3N) hp0 (by norm_num) hεU T.κ0_ent
                  T.marks_K0_le ∧
            (∀ᵐ x ∂S.nuFl, ∀ e ∈ physFibre S S.a₁ S.ν T.t, ∀ s ∈ Icc (0 : ℝ) 1,
              Jr.W1 (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁))
                  ((e.1 : RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2), (s : ℂ) • S.hatC x) =
                (s : ℂ) ^ 2 * ∑ y, (A ((e.1, 0) : physParam 2 S) (s : ℂ)).H y
                  ((S.blockSplit 1 hp).restr x)) ∧
            (∀ᵐ x ∂S.nuFl, ∀ e ∈ physFibre S S.a₁ S.ν T.t, ∑ x', ∑ i, ‖e.2 x' i‖ < 1 →
              ∀ t ∈ Icc (0 : ℝ) 1,
              Jr.W2 (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) e.2
                  ((e.1 : RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2), (t : ℂ) • S.hatC x) =
                ∑ y, (A e (t : ℂ)).H y ((S.blockSplit 1 hp).restr x) -
                  ∑ y, (A ((e.1, 0) : physParam 2 S) (t : ℂ)).H y
                    ((S.blockSplit 1 hp).restr x)) ∧
            ∀ {ι : Type} [Fintype ι] (reads : ι → Set (CTorus 3 3 N₁ T.m₁ (k + 1)))
              (dom : ι → Finset (Set (CTorus 3 3 N₁ T.m₁ (k + 1))))
              (hdomR : ∀ b, ∀ Y ∈ dom b, IsDj 1 (k + 1) Y),
            ∃ A0 : physParam 2 S → ℂ → LabelAct
                (commonLabels (thickLabels I.𝒴 I.dom) (show 3 ^ 1 ∣ N₁ by simpa using h3N)
                  (by norm_num) reads dom hdomR) (S.blockSplit 1 hp).Ωb
                (2 ^ 2 * (2 * (S.β * prop33EpsEtaScaled 3 3 2 T.m₁ k 1 S.a₁ T.BG T.BG₂ T.κ T.t
                  (lvR T.κ T.t (β * 3 ^ k) p₁) 0 0 (1 / S.β)))) (2 * T.κdec - 1) T.κ0 T.marksKc',
              A0 = commonAct (zeroSourceAct A 2 (by norm_num))
                  (show 3 ^ 1 ∣ N₁ by simpa using h3N) (by norm_num) reads dom hdomR
                  (mul_nonneg (sq_nonneg 2) (mul_nonneg zero_le_two hεU)) T.κ0_two ∧
              (∀ y (Φ : ∀ b, (S.blockSplit 1 hp).Ωb b),
                AnalyticOnNhd ℂ (fun r : physParam 2 S × ℂ => (A0 r.1 r.2).H y Φ)
                  (physV S S.a₁ S.ν T.t ×ˢ ball (0 : ℂ) 2)) ∧
              (∀ e ∈ physV S S.a₁ S.ν T.t, ∀ y (Φ : ∀ b, (S.blockSplit 1 hp).Ωb b),
                DifferentiableOn ℂ (fun u => (A0 e u).H y Φ) (ball (0 : ℂ) 2)) ∧
              (∀ y, ∀ e ∈ physV S S.a₁ S.ν T.t, ∀ u ∈ ball (0 : ℂ) 2,
                Continuous ((A0 e u).H y)) ∧
              (∀ (e : physParam 2 S) (u : ℂ) (Φ : ∀ b, (S.blockSplit 1 hp).Ωb b),
                ∑ y, (A0 e u).H y Φ =
                  sqFactor 2 u * ∑ y, (A ((e.1, 0) : physParam 2 S) u).H y Φ) ∧
              (∀ (D' : BgData S.G' 2) (hDh : ∀ y i, D'.h y i = (S.h₀ i : ℂ)),
                XiCData S.G' S.a S.ν (k + 1) 1 T.t D' → ∀ g : Fld 3 3 N₁ T.m₁ (k + 1) 2,
                ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ᵐ x ∂S.nuFl,
                  (S.withDatum D' hDh).WoneC (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) s x =
                    ∑ y, (A0 ((⟨rawOf D', rawOf_mem_rawSub _⟩ : rawSub 2 S.G'), g) (s : ℂ)).H y
                      ((S.blockSplit 1 hp).restr x)) ∧
              (∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ᵐ x ∂S.nuFl,
                S.WoneC (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) s x =
                  ∑ y, (A0 ((⟨rawOf S.D', rawOf_mem_rawSub _⟩ : rawSub 2 S.G'),
                    (0 : CTorus 3 3 N₁ T.m₁ (k + 1) → Fin 2 → ℂ)) (s : ℂ)).H y
                    ((S.blockSplit 1 hp).restr x)) ∧
              Nonempty (ParamMarkFamily (S.blockSplit 1 hp).μ
                (commonLabels (thickLabels I.𝒴 I.dom) (show 3 ^ 1 ∣ N₁ by simpa using h3N)
                  (by norm_num) reads dom hdomR) A0
                (fun i : Empty => i.elim) (fun _ _ _ _ => (0 : ℂ)) 0 (fun i : Empty => i.elim)
                (physV S S.a₁ S.ν T.t) (ball (0 : ℂ) 2) (physCarrier S 1 hp)) ∧
              (∀ _y₀ : {Y // Y ∈ I.𝒴} ⊕ RootUnionLb 1 reads dom,
                Nonempty (InterpMarks S.nuFl (S.blockSplit 1 hp)
                  (S.WoneC (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁))) (fun _ _ => (0 : ℂ))))))) ∧
    (∀ g : Fld 3 3 N₁ T.m₁ (k + 1) 2,
    g ∈ l1Ball 3 3 N₁ T.m₁ (k + 1) 2 →
  ∀ (y : CTorus 3 3 N₁ T.m₁ (k + 1)) (i : Fin 2),
    ∃ E : Finset (CubeB (d := 3) (L := 3) (N₁ := N₁) (m₁ := T.m₁) (K := k + 1) 1 (k + 1)
        Set.univ) → ℂ,
      S.M0C (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) g y i =
        ((S.betaU ^ (1 / 2 : ℝ) : ℝ) : ℂ) * ∑ T', E T' ∧
      (∀ T', rootCube (m₀ := 1) (blockIndex y) ∉ T' → E T' = 0) ∧
      (∀ T', ‖E T'‖ ≤ C * obsPrefactor p s (β * 3 ^ k) * Real.exp (-(3 / 2 * T.κdec) * dExt T')) ∧
      ∀ T', E T' ≠ 0 → IsPolyDom 1 (k + 1) (sitesOf T')) := by
  obtain ⟨CE, CF, C, hCE, hCF, hC, H⟩ :=
    thm31b_onCommonWitness_fromTower_supp_rho T hHull hA p hCR hs0 hs
  obtain ⟨β₀, h3, -, H1⟩ := H 1 one_pos
  refine ⟨β₀, CE, CF, C, h3, hCE, hCF, hC, ?_⟩
  intro k hk N₁ _ h3N h5 ν hν hνk β hβ p₁ hp0 hp₁ hsc S hS hp
  have h := H1 k hk N₁ h3N h5 ν hν hνk β hβ p₁ hp0 hp₁ hsc S hS hp
  simp only [one_mul] at h
  exact h


end Balaban.Inhabited
