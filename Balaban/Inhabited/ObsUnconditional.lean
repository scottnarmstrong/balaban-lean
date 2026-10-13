/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.ObsMarksFromTower
public import Balaban.Inhabited.Thm31bFromTower
public import Balaban.Fluctuation.ObsRayActivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The observable marks record at the shared tower, unconditionally

The ray clause of `sourceDirectTerms_scale_fromTower_ray` holds on the full disc `‖ψ̂ p‖ ≤ p₁`
(the margin `(4 + r)(3/2) p₁ < c_ψ` is `StepScaleData.ray_margin_scaled`).  With it the single
hypothesis `hray` of `obsMarks_zeroClass_family_of_ray` is a theorem.
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation
  Balaban.Localization Balaban.Localization.LevelPair Balaban.Localization.I5Inhabited
  Balaban.Polymer Balaban.SmallField.Def6 Balaban.Inhabited.LevelStep Filter Topology
  MeasureTheory Metric

open Classical in
/-- **The direct terms of the zero class at the shared tower, with the ray clause on the full
disc.**  As `sourceDirectTerms_scale_fromTower_ray`, with the hat fields of the ray clause
ranging over `‖ψ̂ p‖ ≤ p₁` instead of `‖ψ̂ p‖ ≤ (2/3) p₁`. -/
theorem sourceDirectTerms_scale_fromTower_ray_full_rho {κmin : ℝ} (T : StepTower κmin)
    (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁] (h3N : 3 ∣ N₁) (hN : 5 < N₁)
    (ν : ℝ) (hνpos : 0 < ν) (hν : ν * 3 ^ (2 * (k + 1)) ≤ 1) (β : ℝ) (ρ : ℝ) (hρ : 0 < ρ) (hβρ : max 1 ρ ≤ β)
    (p₁ : ℝ) (q : ℝ) (hq0 : 0 < q) (hq : q ≤ ρ)
    (D : StepScaleData T k hk N₁ ν β p₁)
    (S : StepSetting 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) (hS : S = T.step k hk N₁ ν β p₁)
    (hp : 0 < S.p₁) :
    ∃ (val : ((S.U × Fin 2 → ℂ) × (S.U × Fin 2 → ℂ)) → ((S.U × Fin 2 → ℂ) × (S.U × Fin 2 → ℂ)) →
        ℂ → (RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2 × (CTorus 3 3 N₁ T.m₁ (k + 1) → Fin 2 → ℂ)) → ℂ)
      (𝒴 : Finset (Set (CTorus 3 3 N₁ T.m₁ (k + 1))))
      (Tt : Set (CTorus 3 3 N₁ T.m₁ (k + 1)) → ((S.U × Fin 2 → ℂ) × (S.U × Fin 2 → ℂ)) →
        ((S.U × Fin 2 → ℂ) × (S.U × Fin 2 → ℂ)) → ℂ →
        (RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2 × (CTorus 3 3 N₁ T.m₁ (k + 1) → Fin 2 → ℂ)) → ℂ),
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
      PhysicalSharpLocEta S (lvCpsi T.κ T.t (β * 3 ^ k)) 2 2 (lvR T.κ T.t (β * 3 ^ k) p₁) S.a₁
        S.ν T.t (q / S.β) 𝒴 Tt ∧
      DiagCont (fun ψ : S.U × Fin 2 → ℂ => (ψ, ψ))
        (physXW S (lvCpsi T.κ T.t (β * 3 ^ k)) 2 2 (lvR T.κ T.t (β * 3 ^ k) p₁))
        (physSΛEta S S.a₁ S.ν T.t (q / S.β)) 2 𝒴 Tt ∧
      (∀ Θ ∈ physSΛEta S S.a₁ S.ν T.t (q / S.β),
        ∃ I : DirectTerms S 1 hp (fun ψ => (ψ, ψ)) p₁ 2
            (S.β * prop33EpsEtaScaled 3 3 2 T.m₁ k 1 S.a₁ T.BG T.BG₂ T.κ T.t
              (lvR T.κ T.t (β * 3 ^ k) p₁) 0 0 (q / S.β)) (2 * T.κdec - 1) Θ
            (physSΛEta S S.a₁ S.ν T.t (q / S.β))
            (physXW S (lvCpsi T.κ T.t (β * 3 ^ k)) 2 2 (lvR T.κ T.t (β * 3 ^ k) p₁)) val
            (physAgΘ S) (AgFDirPair S),
          I.𝒴 = 𝒴 ∧ I.T = Tt) ∧
      (rawOf S.D', (0 : CTorus 3 3 N₁ T.m₁ (k + 1) → Fin 2 → ℂ)) ∈
        physSΛEta S S.a₁ S.ν T.t (q / S.β) ∧
      (∀ g : Fld 3 3 N₁ T.m₁ (k + 1) 2, ∑ x, ∑ i, ‖g x i‖ < q →
        (rawOf S.D', fun y i => g y i / (S.β : ℂ)) ∈ physSΛEta S S.a₁ S.ν T.t (q / S.β)) ∧
      ∀ (Y : Set (CTorus 3 3 N₁ T.m₁ (k + 1)))
        (Θ : RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2 × (CTorus 3 3 N₁ T.m₁ (k + 1) → Fin 2 → ℂ)),
        Θ ∈ physSΛEta S S.a₁ S.ν T.t (q / S.β) → ∀ ψ : S.U × Fin 2 → ℂ,
        (∀ p, ‖ψ p‖ ≤ p₁) →
        DifferentiableOn ℂ (fun ζ : ℂ => Tt Y (ζ • ψ, ζ • ψ) (ζ • ψ, ζ • ψ) 1 Θ)
          (Metric.ball (0 : ℂ) (3 / 2)) := by
  classical
  subst hS
  have hp' : 0 < (T.toG.step k hk N₁ ν β p₁).p₁ := hp
  have G := sourceDirectTerms_scale_fromTowerG_ray_full_rho T.toG k hk N₁ (by simpa using h3N) hN
    ν hνpos (by simpa using hν) β ρ hρ hβρ p₁ q hq0 hq (StepTower.scaleDataG_of_fixed T D)
    (T.toG.step k hk N₁ ν β p₁) rfl hp'
  have e : (((3 : ℕ) : ℝ)) ^ (k * (3 - 2)) = 3 ^ k := by norm_num
  unfold StepTowerG.step at G
  revert G
  generalize hb : β * ((3 : ℕ) : ℝ) ^ (k * (3 - 2)) = b
  generalize hϱ : rhoSepG 3 3 T.toG.m₁ = ϱ
  have hϱ' : ϱ = rhoSep T.m₁ := hϱ.symm.trans (rhoSepG_three _)
  have hb' : b = β * 3 ^ k := hb.symm.trans (by rw [e])
  subst hϱ' hb'
  intro G
  exact G.imp fun _ => Exists.imp fun _ => Exists.imp fun _ h =>
    ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1⟩

open Classical in
/-- **The direct terms of the zero class at the shared tower, with the ray clause on the full
disc.**  As `sourceDirectTerms_scale_fromTower_ray`, with the hat fields of the ray clause
ranging over `‖ψ̂ p‖ ≤ p₁` instead of `‖ψ̂ p‖ ≤ (2/3) p₁`. -/
theorem sourceDirectTerms_scale_fromTower_ray_full {κmin : ℝ} (T : StepTower κmin)
    (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁] (h3N : 3 ∣ N₁) (hN : 5 < N₁)
    (ν : ℝ) (hνpos : 0 < ν) (hν : ν * 3 ^ (2 * (k + 1)) ≤ 1) (β : ℝ) (hβ1 : 1 ≤ β)
    (p₁ : ℝ) (q : ℝ) (hq0 : 0 < q) (hq : q ≤ 1)
    (D : StepScaleData T k hk N₁ ν β p₁)
    (S : StepSetting 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) (hS : S = T.step k hk N₁ ν β p₁)
    (hp : 0 < S.p₁) :
    ∃ (val : ((S.U × Fin 2 → ℂ) × (S.U × Fin 2 → ℂ)) → ((S.U × Fin 2 → ℂ) × (S.U × Fin 2 → ℂ)) →
        ℂ → (RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2 × (CTorus 3 3 N₁ T.m₁ (k + 1) → Fin 2 → ℂ)) → ℂ)
      (𝒴 : Finset (Set (CTorus 3 3 N₁ T.m₁ (k + 1))))
      (Tt : Set (CTorus 3 3 N₁ T.m₁ (k + 1)) → ((S.U × Fin 2 → ℂ) × (S.U × Fin 2 → ℂ)) →
        ((S.U × Fin 2 → ℂ) × (S.U × Fin 2 → ℂ)) → ℂ →
        (RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2 × (CTorus 3 3 N₁ T.m₁ (k + 1) → Fin 2 → ℂ)) → ℂ),
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
      PhysicalSharpLocEta S (lvCpsi T.κ T.t (β * 3 ^ k)) 2 2 (lvR T.κ T.t (β * 3 ^ k) p₁) S.a₁
        S.ν T.t (q / S.β) 𝒴 Tt ∧
      DiagCont (fun ψ : S.U × Fin 2 → ℂ => (ψ, ψ))
        (physXW S (lvCpsi T.κ T.t (β * 3 ^ k)) 2 2 (lvR T.κ T.t (β * 3 ^ k) p₁))
        (physSΛEta S S.a₁ S.ν T.t (q / S.β)) 2 𝒴 Tt ∧
      (∀ Θ ∈ physSΛEta S S.a₁ S.ν T.t (q / S.β),
        ∃ I : DirectTerms S 1 hp (fun ψ => (ψ, ψ)) p₁ 2
            (S.β * prop33EpsEtaScaled 3 3 2 T.m₁ k 1 S.a₁ T.BG T.BG₂ T.κ T.t
              (lvR T.κ T.t (β * 3 ^ k) p₁) 0 0 (q / S.β)) (2 * T.κdec - 1) Θ
            (physSΛEta S S.a₁ S.ν T.t (q / S.β))
            (physXW S (lvCpsi T.κ T.t (β * 3 ^ k)) 2 2 (lvR T.κ T.t (β * 3 ^ k) p₁)) val
            (physAgΘ S) (AgFDirPair S),
          I.𝒴 = 𝒴 ∧ I.T = Tt) ∧
      (rawOf S.D', (0 : CTorus 3 3 N₁ T.m₁ (k + 1) → Fin 2 → ℂ)) ∈
        physSΛEta S S.a₁ S.ν T.t (q / S.β) ∧
      (∀ g : Fld 3 3 N₁ T.m₁ (k + 1) 2, ∑ x, ∑ i, ‖g x i‖ < q →
        (rawOf S.D', fun y i => g y i / (S.β : ℂ)) ∈ physSΛEta S S.a₁ S.ν T.t (q / S.β)) ∧
      ∀ (Y : Set (CTorus 3 3 N₁ T.m₁ (k + 1)))
        (Θ : RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2 × (CTorus 3 3 N₁ T.m₁ (k + 1) → Fin 2 → ℂ)),
        Θ ∈ physSΛEta S S.a₁ S.ν T.t (q / S.β) → ∀ ψ : S.U × Fin 2 → ℂ,
        (∀ p, ‖ψ p‖ ≤ p₁) →
        DifferentiableOn ℂ (fun ζ : ℂ => Tt Y (ζ • ψ, ζ • ψ) (ζ • ψ, ζ • ψ) 1 Θ)
          (Metric.ball (0 : ℂ) (3 / 2)) := by
  exact sourceDirectTerms_scale_fromTower_ray_full_rho T k hk N₁ h3N hN ν hνpos hν β 1 one_pos (by rw [max_self]; exact hβ1) p₁ q hq0 hq D S hS hp


/-- **The ray hypothesis of the observable lane holds, general tower.**  The statement of
`obsRay_hray_fromTower_rho` at `T : StepTowerG d L N κmin`: slice `q = ρ` of
`sourceDirectTerms_scale_fromTowerG_ray_full_rho`, for `max 1 ρ ≤ β`.  The fixed theorem is its
corollary. -/
theorem obsRay_hray_fromTowerG_rho {d L N : ℕ} [NeZero L] {κmin : ℝ} (T : StepTowerG d L N κmin) (ρ : ℝ) (hρ : 0 < ρ) :
    ∀ (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁], L ^ T.m₀ ∣ N₁ → 5 < N₁ →
      ∀ ν : ℝ, 0 < ν → ν * (L : ℝ) ^ (2 * (k + 1)) ≤ 1 → ∀ β : ℝ, max 1 ρ ≤ β →
      ∀ p₁ : ℝ, 0 < p₁ → StepScaleDataG T k hk N₁ ν β p₁ →
      ∀ S : StepSetting d L N₁ T.m₁ k N (rhoSepG d L T.m₁), S = T.step k hk N₁ ν β p₁ →
      ∀ hp : 0 < S.p₁,
      ∃ (val : ((S.U × Fin N → ℂ) × (S.U × Fin N → ℂ)) → ((S.U × Fin N → ℂ) × (S.U × Fin N → ℂ)) →
          ℂ → (RawData d L (N₁ * L ^ T.m₁) (k + 1) N ×
            (CTorus d L N₁ T.m₁ (k + 1) → Fin N → ℂ)) → ℂ)
        (𝒴 : Finset (Set (CTorus d L N₁ T.m₁ (k + 1))))
        (Tt : Set (CTorus d L N₁ T.m₁ (k + 1)) → ((S.U × Fin N → ℂ) × (S.U × Fin N → ℂ)) →
          ((S.U × Fin N → ℂ) × (S.U × Fin N → ℂ)) → ℂ →
          (RawData d L (N₁ * L ^ T.m₁) (k + 1) N ×
            (CTorus d L N₁ T.m₁ (k + 1) → Fin N → ℂ)) → ℂ),
        (∀ x w σ Θ, val x w σ Θ =
          (-(S.β : ℂ)) * raySrc3 (hatFun S.G' S.a₁ S.ν T.t S.hG'
            ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)
            (interactionOne S.hG S.hG' (le_refl (k + 1)) S.a₁ S.ν T.t)) taylorWeight x.1 w.1 σ Θ.1 +
          (S.β : ℂ) * (∑ s : CTorus d L N₁ T.m₁ (k + 1) × Fin N, Θ.2 s.1 s.2 *
            dirTermSrc (hatFun S.G' S.a₁ S.ν T.t S.hG' ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)
              (onXi S.G' S.a₁ S.ν T.t
                (fun D ψ' => svec (stepG d L N₁ T.m₁ k (rhoSepG d L T.m₁))
                  (flFieldOne S.G' (stepG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) T.BG₂ T.κ S.a₁ S.ν D ψ')
                    s.1 s.2)))
              (fun _ => (1 : ℂ)) x.2 w.2 σ Θ.1)) ∧
        DiagCont (fun ψ : S.U × Fin N → ℂ => (ψ, ψ))
          (physXW S (lvCpsiG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2)))) 2 2 (lvRG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2))) p₁))
          (physSΛEta S S.a₁ S.ν T.t (ρ / S.β)) 2 𝒴 Tt ∧
        (∀ Θ ∈ physSΛEta S S.a₁ S.ν T.t (ρ / S.β),
          ∃ I : DirectTerms S T.m₀ hp (fun ψ => (ψ, ψ)) p₁ 2
              (S.β * prop33EpsEtaScaled d L N T.m₁ k T.m₀ S.a₁ T.BG T.BG₂ T.κ T.t
                (lvRG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2))) p₁) 0 0 (ρ / S.β)) (2 * T.κdec - 1) Θ
              (physSΛEta S S.a₁ S.ν T.t (ρ / S.β))
              (physXW S (lvCpsiG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2)))) 2 2 (lvRG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2))) p₁)) val
              (physAgΘ S) (AgFDirPair S),
            I.𝒴 = 𝒴 ∧ I.T = Tt) ∧
        (rawOf S.D', (0 : CTorus d L N₁ T.m₁ (k + 1) → Fin N → ℂ)) ∈
          physSΛEta S S.a₁ S.ν T.t (ρ / S.β) ∧
        (∀ g : Fld d L N₁ T.m₁ (k + 1) N, ∑ x, ∑ i, ‖g x i‖ < ρ →
          (rawOf S.D', fun y i => g y i / (S.β : ℂ)) ∈ physSΛEta S S.a₁ S.ν T.t (ρ / S.β)) ∧
        (∀ Y ∈ 𝒴, ∀ Θ ∈ physSΛEta S S.a₁ S.ν T.t (ρ / S.β),
          ∀ ψ ∈ hatDisk S.U N p₁,
            DifferentiableOn ℂ (fun z : ℂ => Tt Y (z • ψ, z • ψ) (z • ψ, z • ψ) 1 Θ)
              (ball (0 : ℂ) (3 / 2))) := by
  classical
  intro k hk N₁ _ hLN hN ν hνpos hν β hβ1 p₁ hp0 D S hS hp
  obtain ⟨val, 𝒴, Tt, hval, -, hcont, hI, hm0, hmg, hr, -⟩ :=
    sourceDirectTerms_scale_fromTowerG_ray_full_rho T k hk N₁ hLN hN ν hνpos hν β ρ hρ hβ1 p₁ ρ hρ
      le_rfl D S hS hp
  exact ⟨val, 𝒴, Tt, hval, hcont, hI, hm0, hmg, fun Y _ Θ hΘ ψ hψ => hr Y Θ hΘ ψ hψ⟩

/-- **The ray hypothesis of `obsMarks_zeroClass_family_of_ray_ksupp_rho` holds.**  Slice `q = ρ` of
`sourceDirectTerms_scale_fromTower_ray_full_rho`, for `max 1 ρ ≤ β`. -/
theorem obsRay_hray_fromTower_rho {κmin : ℝ} (T : StepTower κmin) (ρ : ℝ) (hρ : 0 < ρ) :
    ∀ (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁], 3 ∣ N₁ → 5 < N₁ →
      ∀ ν : ℝ, 0 < ν → ν * 3 ^ (2 * (k + 1)) ≤ 1 → ∀ β : ℝ, max 1 ρ ≤ β →
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
              (ball (0 : ℂ) (3 / 2))) := by
  classical
  intro k hk N₁ _ h3N hN ν hνpos hν β hβ1 p₁ hp0 D S hS hp
  subst hS
  have e : (((3 : ℕ) : ℝ)) ^ (k * (3 - 2)) = 3 ^ k := by norm_num
  have hp' : 0 < (T.toG.step k hk N₁ ν β p₁).p₁ := hp
  have G := obsRay_hray_fromTowerG_rho T.toG ρ hρ k hk N₁ (by simpa using h3N) hN ν hνpos
    (by simpa using hν) β hβ1 p₁ hp0 (StepTower.scaleDataG_of_fixed T D)
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

/-- **The ray hypothesis of `obsMarks_zeroClass_family_of_ray` holds.**  Slice `q = 1` of
`sourceDirectTerms_scale_fromTower_ray_full`. -/
theorem obsRay_hray_fromTower {κmin : ℝ} (T : StepTower κmin) :
    ∀ (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁], 3 ∣ N₁ → 5 < N₁ →
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
              (ball (0 : ℂ) (3 / 2))) := by
  intro k hk N₁ _ h3N hN ν hνpos hν β hβ p₁ hp0 D S hS hp
  exact obsRay_hray_fromTower_rho T 1 one_pos k hk N₁ h3N hN ν hνpos hν β (by rw [max_self]; exact hβ) p₁ hp0 D S hS hp


open Classical in
/-- **`obsMarks_zeroClass_family_ksupp` at source radius `ρ`, general tower.**  The sources range
over the ball `∑ |g| < ρ`; the scale threshold satisfies `ρ ≤ β₀`, and `β₀, C₁, C₂` are chosen
after `ρ`.  From `obsRay_hray_fromTowerG_rho`.  The fixed `obsMarks_zeroClass_family_ksupp_rho`
is the same statement for `T : StepTower κmin`. -/
theorem obsMarks_zeroClass_family_ksupp_rhoG {d L N : ℕ} [NeZero L] {κmin : ℝ}
    (T : StepTowerG d L N κmin)
    {A₁ : ℝ} (hA : 0 < A₁) (p : ℕ) {CR s : ℝ}
    (hCR : 0 < CR) (hs0 : 0 < s) (hs : s < 1 / 2) (ρ : ℝ) (hρ : 0 < ρ) :
  ∃ β₀ C₁ C₂ : ℝ, 2 ≤ β₀ ∧ ρ ≤ β₀ ∧ 0 ≤ C₁ ∧ 0 ≤ C₂ ∧
  ∀ (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁], L ^ T.m₀ ∣ N₁ → 5 < N₁ →
  ∀ ν : ℝ, 0 < ν → ν * (L : ℝ) ^ (2 * (k + 1)) ≤ 1 →
  ∀ β : ℝ, β₀ ≤ β → ∀ (p₁ : ℝ) (hp : 0 < p₁),
  p₁ ≤ pLog A₁ p (β * (L : ℝ) ^ (k * (d - 2))) →
  StepScaleDataG T k hk N₁ ν β p₁ →
  ∀ g : Fld d L N₁ T.m₁ (k + 1) N,
    g ∈ l1BallRho d L N₁ T.m₁ (k + 1) N ρ →
  ∀ (y : CTorus d L N₁ T.m₁ (k + 1)) (i : Fin N),
    let S := T.step k hk N₁ ν β p₁;
    let C := zeroClass d L N₁ T.m₁ k N (rhoSepG d L T.m₁);
    ∃ I : ObsMarks S.nuFl (S.blockSplit T.m₀ hp)
      (fun r x => S.WoneC C 1 x + S.WtwoC C g r x)
      (fun r x => deriv (fun z => McompAtC C.m₀ C.Tm S.a S.ν
        (Nat.le_succ k) (S.dataUC (S.psiAtC z x)) g y i) r)
      (rootCube (m₀ := T.m₀) (blockIndex y)),
      I.Kc = 4 * K0 d L T.κ0 + 2 ∧ I.κ0 = T.κ0 ∧
      I.κH = 2 * T.κdec - 1 ∧ I.κ' = T.κ' ∧
      I.κh = 2 * T.κdec ∧ I.Rσ = obsRg CR s p (β * (L : ℝ) ^ (k * (d - 2))) ∧
      I.B1 ≤ C₁ * obsW p (β * (L : ℝ) ^ (k * (d - 2))) ^ 4 *
        (β * (L : ℝ) ^ (k * (d - 2))) ^ (-(1 / 2 : ℝ) - s) ∧
      I.B2 ≤ C₂ * obsW p (β * (L : ℝ) ^ (k * (d - 2))) ^ 2 / (β * (L : ℝ) ^ (k * (d - 2))) ∧
      ∀ (j : I.ι1) (T' : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := T.m₁) (K := k + 1)
        T.m₀ (k + 1) Set.univ)),
        I.hker j T' ≠ 0 → dOmega T.m₀ (k + 1) Set.univ (sitesOf T') ≠ ⊤ :=
  obsMarks_zeroClass_family_of_ray_ksupp_rhoG T hA p hCR hs0 hs ρ hρ (obsRay_hray_fromTowerG_rho T ρ hρ)

open Classical in
/-- **`obsMarks_zeroClass_family_ksupp` at source radius `ρ`.**  The sources range over the ball
`∑ |g| < ρ`; the scale threshold satisfies `ρ ≤ β₀`, and `β₀, C₁, C₂` are chosen after `ρ`.  From
`obsRay_hray_fromTower_rho`. -/
theorem obsMarks_zeroClass_family_ksupp_rho {κmin : ℝ} (T : StepTower κmin)
    {A₁ : ℝ} (hA : 0 < A₁) (p : ℕ) {CR s : ℝ}
    (hCR : 0 < CR) (hs0 : 0 < s) (hs : s < 1 / 2) (ρ : ℝ) (hρ : 0 < ρ) :
  ∃ β₀ C₁ C₂ : ℝ, 2 ≤ β₀ ∧ ρ ≤ β₀ ∧ 0 ≤ C₁ ∧ 0 ≤ C₂ ∧
  ∀ (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁], 3 ∣ N₁ → 5 < N₁ →
  ∀ ν : ℝ, 0 < ν → ν * 3 ^ (2 * (k + 1)) ≤ 1 →
  ∀ β : ℝ, β₀ ≤ β → ∀ (p₁ : ℝ) (hp : 0 < p₁),
  p₁ ≤ pLog A₁ p (β * 3 ^ k) →
  StepScaleData T k hk N₁ ν β p₁ →
  ∀ g : Fld 3 3 N₁ T.m₁ (k + 1) 2,
    g ∈ l1BallRho 3 3 N₁ T.m₁ (k + 1) 2 ρ →
  ∀ (y : CTorus 3 3 N₁ T.m₁ (k + 1)) (i : Fin 2),
    let S := T.step k hk N₁ ν β p₁;
    let C := zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁);
    ∃ I : ObsMarks S.nuFl (S.blockSplit 1 hp)
      (fun r x => S.WoneC C 1 x + S.WtwoC C g r x)
      (fun r x => deriv (fun z => McompAtC C.m₀ C.Tm S.a S.ν
        (Nat.le_succ k) (S.dataUC (S.psiAtC z x)) g y i) r)
      (rootCube (m₀ := 1) (blockIndex y)),
      I.Kc = 4 * K0 3 3 T.κ0 + 2 ∧ I.κ0 = T.κ0 ∧
      I.κH = 2 * T.κdec - 1 ∧ I.κ' = T.κ' ∧
      I.κh = 2 * T.κdec ∧ I.Rσ = obsRg CR s p (β * 3 ^ k) ∧
      I.B1 ≤ C₁ * obsW p (β * 3 ^ k) ^ 4 *
        (β * 3 ^ k) ^ (-(1 / 2 : ℝ) - s) ∧
      I.B2 ≤ C₂ * obsW p (β * 3 ^ k) ^ 2 / (β * 3 ^ k) ∧
      ∀ (j : I.ι1) (T : Finset (CubeB (d := 3) (L := 3) (N₁ := N₁) (m₁ := T.m₁) (K := k + 1)
        1 (k + 1) Set.univ)),
        I.hker j T ≠ 0 → dOmega 1 (k + 1) Set.univ (sitesOf T) ≠ ⊤ :=
  obsMarks_zeroClass_family_of_ray_ksupp_rho T hA p hCR hs0 hs ρ hρ (obsRay_hray_fromTower_rho T ρ hρ)

open Classical in
/-- **`obsMarks_zeroClass_family_ksupp`, general tower** (source radius `1`; see
`obsMarks_zeroClass_family_ksupp_rhoG`). -/
theorem obsMarks_zeroClass_family_ksuppG {d L N : ℕ} [NeZero L] {κmin : ℝ}
    (T : StepTowerG d L N κmin)
    {A₁ : ℝ} (hA : 0 < A₁) (p : ℕ) {CR s : ℝ}
    (hCR : 0 < CR) (hs0 : 0 < s) (hs : s < 1 / 2) :
  ∃ β₀ C₁ C₂ : ℝ, 2 ≤ β₀ ∧ 0 ≤ C₁ ∧ 0 ≤ C₂ ∧
  ∀ (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁], L ^ T.m₀ ∣ N₁ → 5 < N₁ →
  ∀ ν : ℝ, 0 < ν → ν * (L : ℝ) ^ (2 * (k + 1)) ≤ 1 →
  ∀ β : ℝ, β₀ ≤ β → ∀ (p₁ : ℝ) (hp : 0 < p₁),
  p₁ ≤ pLog A₁ p (β * (L : ℝ) ^ (k * (d - 2))) →
  StepScaleDataG T k hk N₁ ν β p₁ →
  ∀ g : Fld d L N₁ T.m₁ (k + 1) N,
    g ∈ l1Ball d L N₁ T.m₁ (k + 1) N →
  ∀ (y : CTorus d L N₁ T.m₁ (k + 1)) (i : Fin N),
    let S := T.step k hk N₁ ν β p₁;
    let C := zeroClass d L N₁ T.m₁ k N (rhoSepG d L T.m₁);
    ∃ I : ObsMarks S.nuFl (S.blockSplit T.m₀ hp)
      (fun r x => S.WoneC C 1 x + S.WtwoC C g r x)
      (fun r x => deriv (fun z => McompAtC C.m₀ C.Tm S.a S.ν
        (Nat.le_succ k) (S.dataUC (S.psiAtC z x)) g y i) r)
      (rootCube (m₀ := T.m₀) (blockIndex y)),
      I.Kc = 4 * K0 d L T.κ0 + 2 ∧ I.κ0 = T.κ0 ∧
      I.κH = 2 * T.κdec - 1 ∧ I.κ' = T.κ' ∧
      I.κh = 2 * T.κdec ∧ I.Rσ = obsRg CR s p (β * (L : ℝ) ^ (k * (d - 2))) ∧
      I.B1 ≤ C₁ * obsW p (β * (L : ℝ) ^ (k * (d - 2))) ^ 4 *
        (β * (L : ℝ) ^ (k * (d - 2))) ^ (-(1 / 2 : ℝ) - s) ∧
      I.B2 ≤ C₂ * obsW p (β * (L : ℝ) ^ (k * (d - 2))) ^ 2 / (β * (L : ℝ) ^ (k * (d - 2))) ∧
      ∀ (j : I.ι1) (T' : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := T.m₁) (K := k + 1)
        T.m₀ (k + 1) Set.univ)),
        I.hker j T' ≠ 0 → dOmega T.m₀ (k + 1) Set.univ (sitesOf T') ≠ ⊤ := by
  obtain ⟨β₀, C₁, C₂, h1, -, h2, h3, h⟩ := obsMarks_zeroClass_family_ksupp_rhoG T hA p hCR hs0 hs 1 one_pos
  exact ⟨β₀, C₁, C₂, h1, h2, h3, h⟩

open Classical in
/-- **The observable marks record of the zero-class step at the general tower**, with no
hypothesis beyond the tower: `obsMarks_zeroClass_family_ksuppG` without the kernel support.  The
fixed `obsMarks_zeroClass_family` is the same statement for `T : StepTower κmin`. -/
theorem obsMarks_zeroClass_familyG {d L N : ℕ} [NeZero L] {κmin : ℝ}
    (T : StepTowerG d L N κmin)
    {A₁ : ℝ} (hA : 0 < A₁) (p : ℕ) {CR s : ℝ}
    (hCR : 0 < CR) (hs0 : 0 < s) (hs : s < 1 / 2) :
  ∃ β₀ C₁ C₂ : ℝ, 2 ≤ β₀ ∧ 0 ≤ C₁ ∧ 0 ≤ C₂ ∧
  ∀ (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁], L ^ T.m₀ ∣ N₁ → 5 < N₁ →
  ∀ ν : ℝ, 0 < ν → ν * (L : ℝ) ^ (2 * (k + 1)) ≤ 1 →
  ∀ β : ℝ, β₀ ≤ β → ∀ (p₁ : ℝ) (hp : 0 < p₁),
  p₁ ≤ pLog A₁ p (β * (L : ℝ) ^ (k * (d - 2))) →
  StepScaleDataG T k hk N₁ ν β p₁ →
  ∀ g : Fld d L N₁ T.m₁ (k + 1) N,
    g ∈ l1Ball d L N₁ T.m₁ (k + 1) N →
  ∀ (y : CTorus d L N₁ T.m₁ (k + 1)) (i : Fin N),
    let S := T.step k hk N₁ ν β p₁;
    let C := zeroClass d L N₁ T.m₁ k N (rhoSepG d L T.m₁);
    ∃ I : ObsMarks S.nuFl (S.blockSplit T.m₀ hp)
      (fun r x => S.WoneC C 1 x + S.WtwoC C g r x)
      (fun r x => deriv (fun z => McompAtC C.m₀ C.Tm S.a S.ν
        (Nat.le_succ k) (S.dataUC (S.psiAtC z x)) g y i) r)
      (rootCube (m₀ := T.m₀) (blockIndex y)),
      I.Kc = 4 * K0 d L T.κ0 + 2 ∧ I.κ0 = T.κ0 ∧
      I.κH = 2 * T.κdec - 1 ∧ I.κ' = T.κ' ∧
      I.κh = 2 * T.κdec ∧ I.Rσ = obsRg CR s p (β * (L : ℝ) ^ (k * (d - 2))) ∧
      I.B1 ≤ C₁ * obsW p (β * (L : ℝ) ^ (k * (d - 2))) ^ 4 *
        (β * (L : ℝ) ^ (k * (d - 2))) ^ (-(1 / 2 : ℝ) - s) ∧
      I.B2 ≤ C₂ * obsW p (β * (L : ℝ) ^ (k * (d - 2))) ^ 2 / (β * (L : ℝ) ^ (k * (d - 2))) := by
  obtain ⟨β₀, C₁, C₂, h1, h2, h3, h⟩ := obsMarks_zeroClass_family_ksuppG T hA p hCR hs0 hs
  refine ⟨β₀, C₁, C₂, h1, h2, h3, ?_⟩
  intro k hk N₁ _ hLN hN ν hν0 hν β hβ p₁ hp₁p hp₁ D g hg y i S C
  obtain ⟨I, e1, e2, e3, e4, e5, e6, e7, e8, -⟩ := h k hk N₁ hLN hN ν hν0 hν β hβ p₁ hp₁p hp₁ D g
    hg y i
  exact ⟨I, e1, e2, e3, e4, e5, e6, e7, e8⟩

open Classical in
/-- **`obsMarks_zeroClass_family` with the kernel support** (see
`obsMarks_zeroClass_at_of_ray_ksupp`). -/
theorem obsMarks_zeroClass_family_ksupp {κmin : ℝ} (T : StepTower κmin)
    {A₁ : ℝ} (hA : 0 < A₁) (p : ℕ) {CR s : ℝ}
    (hCR : 0 < CR) (hs0 : 0 < s) (hs : s < 1 / 2) :
  ∃ β₀ C₁ C₂ : ℝ, 2 ≤ β₀ ∧ 0 ≤ C₁ ∧ 0 ≤ C₂ ∧
  ∀ (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁], 3 ∣ N₁ → 5 < N₁ →
  ∀ ν : ℝ, 0 < ν → ν * 3 ^ (2 * (k + 1)) ≤ 1 →
  ∀ β : ℝ, β₀ ≤ β → ∀ (p₁ : ℝ) (hp : 0 < p₁),
  p₁ ≤ pLog A₁ p (β * 3 ^ k) →
  StepScaleData T k hk N₁ ν β p₁ →
  ∀ g : Fld 3 3 N₁ T.m₁ (k + 1) 2,
    g ∈ l1Ball 3 3 N₁ T.m₁ (k + 1) 2 →
  ∀ (y : CTorus 3 3 N₁ T.m₁ (k + 1)) (i : Fin 2),
    let S := T.step k hk N₁ ν β p₁;
    let C := zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁);
    ∃ I : ObsMarks S.nuFl (S.blockSplit 1 hp)
      (fun r x => S.WoneC C 1 x + S.WtwoC C g r x)
      (fun r x => deriv (fun z => McompAtC C.m₀ C.Tm S.a S.ν
        (Nat.le_succ k) (S.dataUC (S.psiAtC z x)) g y i) r)
      (rootCube (m₀ := 1) (blockIndex y)),
      I.Kc = 4 * K0 3 3 T.κ0 + 2 ∧ I.κ0 = T.κ0 ∧
      I.κH = 2 * T.κdec - 1 ∧ I.κ' = T.κ' ∧
      I.κh = 2 * T.κdec ∧ I.Rσ = obsRg CR s p (β * 3 ^ k) ∧
      I.B1 ≤ C₁ * obsW p (β * 3 ^ k) ^ 4 *
        (β * 3 ^ k) ^ (-(1 / 2 : ℝ) - s) ∧
      I.B2 ≤ C₂ * obsW p (β * 3 ^ k) ^ 2 / (β * 3 ^ k) ∧
      ∀ (j : I.ι1) (T : Finset (CubeB (d := 3) (L := 3) (N₁ := N₁) (m₁ := T.m₁) (K := k + 1)
        1 (k + 1) Set.univ)),
        I.hker j T ≠ 0 → dOmega 1 (k + 1) Set.univ (sitesOf T) ≠ ⊤ := by
  obtain ⟨β₀, C₁, C₂, h1, -, h2, h3, h⟩ := obsMarks_zeroClass_family_ksupp_rho T hA p hCR hs0 hs 1 one_pos
  exact ⟨β₀, C₁, C₂, h1, h2, h3, h⟩

open Classical in
/-- **The observable marks record of the zero-class step at the shared tower** (OBSPHYS §4), with
no hypothesis beyond the tower: `obsMarks_zeroClass_family_of_ray` with `hray` supplied by
`obsRay_hray_fromTower`. -/
theorem obsMarks_zeroClass_family {κmin : ℝ} (T : StepTower κmin)
    {A₁ : ℝ} (hA : 0 < A₁) (p : ℕ) {CR s : ℝ}
    (hCR : 0 < CR) (hs0 : 0 < s) (hs : s < 1 / 2) :
  ∃ β₀ C₁ C₂ : ℝ, 2 ≤ β₀ ∧ 0 ≤ C₁ ∧ 0 ≤ C₂ ∧
  ∀ (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁], 3 ∣ N₁ → 5 < N₁ →
  ∀ ν : ℝ, 0 < ν → ν * 3 ^ (2 * (k + 1)) ≤ 1 →
  ∀ β : ℝ, β₀ ≤ β → ∀ (p₁ : ℝ) (hp : 0 < p₁),
  p₁ ≤ pLog A₁ p (β * 3 ^ k) →
  StepScaleData T k hk N₁ ν β p₁ →
  ∀ g : Fld 3 3 N₁ T.m₁ (k + 1) 2,
    g ∈ l1Ball 3 3 N₁ T.m₁ (k + 1) 2 →
  ∀ (y : CTorus 3 3 N₁ T.m₁ (k + 1)) (i : Fin 2),
    let S := T.step k hk N₁ ν β p₁;
    let C := zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁);
    ∃ I : ObsMarks S.nuFl (S.blockSplit 1 hp)
      (fun r x => S.WoneC C 1 x + S.WtwoC C g r x)
      (fun r x => deriv (fun z => McompAtC C.m₀ C.Tm S.a S.ν
        (Nat.le_succ k) (S.dataUC (S.psiAtC z x)) g y i) r)
      (rootCube (m₀ := 1) (blockIndex y)),
      I.Kc = 4 * K0 3 3 T.κ0 + 2 ∧ I.κ0 = T.κ0 ∧
      I.κH = 2 * T.κdec - 1 ∧ I.κ' = T.κ' ∧
      I.κh = 2 * T.κdec ∧ I.Rσ = obsRg CR s p (β * 3 ^ k) ∧
      I.B1 ≤ C₁ * obsW p (β * 3 ^ k) ^ 4 *
        (β * 3 ^ k) ^ (-(1 / 2 : ℝ) - s) ∧
      I.B2 ≤ C₂ * obsW p (β * 3 ^ k) ^ 2 / (β * 3 ^ k) := by
  obtain ⟨β₀, C₁, C₂, h1, h2, h3, h⟩ := obsMarks_zeroClass_family_ksupp T hA p hCR hs0 hs
  refine ⟨β₀, C₁, C₂, h1, h2, h3, ?_⟩
  intro k hk N₁ _ h3N hN ν hν0 hν β hβ p₁ hp₁p hp₁ D g hg y i S C
  obtain ⟨I, e1, e2, e3, e4, e5, e6, e7, e8, -⟩ := h k hk N₁ h3N hN ν hν0 hν β hβ p₁ hp₁p hp₁ D g
    hg y i
  exact ⟨I, e1, e2, e3, e4, e5, e6, e7, e8⟩

open Classical in
/-- **Non-vacuity of `obsMarks_zeroClass_family`.**  At `k = 1`, `N₁ = 18`, `ν = 1/81`, `p₁ = 1`
(`A₁ = 1`, `p = 0`), `C_R = 1`, `s = 1/4`, there is a scale with a `StepScaleData` record at which
the family gives an `ObsMarks` record for the source `g = 0`, at every site and spin. -/
theorem obsMarks_zeroClass_instance {κmin : ℝ} (T : StepTower κmin) :
    ∃ β : ℝ, 2 ≤ β ∧ ∃ _ : StepScaleData T 1 le_rfl 18 (1 / 81) β 1,
      ∀ (hp : 0 < (T.step 1 le_rfl 18 (1 / 81) β 1).p₁)
        (y : CTorus 3 3 18 T.m₁ (1 + 1)) (i : Fin 2),
        let S := T.step 1 le_rfl 18 (1 / 81) β 1;
        let C := zeroClass 3 3 18 T.m₁ 1 2 (rhoSep T.m₁);
        Nonempty (ObsMarks S.nuFl (S.blockSplit 1 hp)
          (fun r x => S.WoneC C 1 x + S.WtwoC C (0 : Fld 3 3 18 T.m₁ (1 + 1) 2) r x)
          (fun r x => deriv (fun z => McompAtC C.m₀ C.Tm S.a S.ν
            (Nat.le_succ 1) (S.dataUC (S.psiAtC z x)) (0 : Fld 3 3 18 T.m₁ (1 + 1) 2) y i) r)
          (rootCube (m₀ := 1) (blockIndex y)) ) := by
  obtain ⟨β₀, C₁, C₂, hβ₀, -, -, hfam⟩ := obsMarks_zeroClass_family T (A₁ := 1) one_pos 0
    (CR := 1) (s := 1 / 4) one_pos (by norm_num) (by norm_num)
  obtain ⟨βray, h2, hsc⟩ := T.scale (A₁ := 1) one_pos 0
  have hβ : 2 ≤ max β₀ βray := le_max_of_le_left hβ₀
  have hp1 : (1 : ℝ) ≤ pLog 1 0 (max β₀ βray * 3 ^ 1) := by simp [pLog]
  obtain ⟨D⟩ := hsc 1 le_rfl 18 (by norm_num) (by norm_num) (1 / 81) (by norm_num) (by norm_num)
    (max β₀ βray) (le_max_right _ _) 1 one_pos hp1
  refine ⟨max β₀ βray, hβ, D, fun hp y i => ?_⟩
  obtain ⟨I, -⟩ := hfam 1 le_rfl 18 (by norm_num) (by norm_num) (1 / 81) (by norm_num)
    (by norm_num) (max β₀ βray) (le_max_left _ _) 1 hp hp1 D 0
    (by simp [l1Ball]) y i
  exact ⟨I⟩

/-- **The coefficient sum and bound of Theorem 3.1 (b) for the zero-class step at every scale of
one tower and every source radius `ρ > 0`, with no hypothesis beyond the tower**, at the output rate `(3/2) κ_dec`:
`thm31b_zeroClass_fromTower_of_ray` with `hray` supplied by `obsRay_hray_fromTower`.

This is weaker than clause (b) of `notes/phase1/FLUCTUATION.md` Theorem 3.1 (audit
`notes/phase1/AUDIT-OBS.md`, A1): the terms are indexed by finite sets of block cubes with a root
clause, not by localization domains with a support clause; there is no termwise locality, no
analyticity in the source `g` (the coefficients are chosen after `g`), no reality or symmetry
clause; and the prefactor is `obsPrefactor`, not the paper's power of `β`. -/
theorem thm31b_zeroClass_fromTower_rho {κmin : ℝ} (T : StepTower κmin)
    {A₁ : ℝ} (hA : 0 < A₁) (p : ℕ) {CR s : ℝ}
    (hCR : 0 < CR) (hs0 : 0 < s) (hs : s < 1 / 2) (ρ : ℝ) (hρ : 0 < ρ) :
  ∃ β₀ C : ℝ, 2 ≤ β₀ ∧ ρ ≤ β₀ ∧ 0 ≤ C ∧
  ∀ (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁], 3 ∣ N₁ → 5 < N₁ →
  ∀ ν : ℝ, 0 < ν → ν * 3 ^ (2 * (k + 1)) ≤ 1 →
  ∀ β : ℝ, β₀ ≤ β → ∀ (p₁ : ℝ), 0 < p₁ →
  p₁ ≤ pLog A₁ p (β * 3 ^ k) →
  StepScaleData T k hk N₁ ν β p₁ →
  ∀ g : Fld 3 3 N₁ T.m₁ (k + 1) 2,
    g ∈ l1BallRho 3 3 N₁ T.m₁ (k + 1) 2 ρ →
  ∀ (y : CTorus 3 3 N₁ T.m₁ (k + 1)) (i : Fin 2),
    ∃ E : Finset (CubeB (d := 3) (L := 3) (N₁ := N₁) (m₁ := T.m₁) (K := k + 1) 1 (k + 1)
        Set.univ) → ℂ,
      (T.step k hk N₁ ν β p₁).M0C (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) g y i =
        (((T.step k hk N₁ ν β p₁).betaU ^ (1 / 2 : ℝ) : ℝ) : ℂ) * ∑ T', E T' ∧
      (∀ T', rootCube (m₀ := 1) (blockIndex y) ∉ T' → E T' = 0) ∧
      ∀ T', ‖E T'‖ ≤ C * obsPrefactor p s (β * 3 ^ k) * Real.exp (-(3 / 2 * T.κdec) * dExt T') :=
  thm31b_zeroClass_fromTower_of_ray_rho T hA p hCR hs0 hs ρ hρ (obsRay_hray_fromTower_rho T ρ hρ)

/-- **The coefficient sum and bound of Theorem 3.1 (b) for the zero-class step at every scale of
one tower, with no hypothesis beyond the tower**, at the output rate `(3/2) κ_dec`:
`thm31b_zeroClass_fromTower_of_ray` with `hray` supplied by `obsRay_hray_fromTower`.

This is weaker than clause (b) of `notes/phase1/FLUCTUATION.md` Theorem 3.1 (audit
`notes/phase1/AUDIT-OBS.md`, A1): the terms are indexed by finite sets of block cubes with a root
clause, not by localization domains with a support clause; there is no termwise locality, no
analyticity in the source `g` (the coefficients are chosen after `g`), no reality or symmetry
clause; and the prefactor is `obsPrefactor`, not the paper's power of `β`. -/
theorem thm31b_zeroClass_fromTower {κmin : ℝ} (T : StepTower κmin)
    {A₁ : ℝ} (hA : 0 < A₁) (p : ℕ) {CR s : ℝ}
    (hCR : 0 < CR) (hs0 : 0 < s) (hs : s < 1 / 2) :
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
  obtain ⟨β₀, C, hβ₀, -, hC, h⟩ := thm31b_zeroClass_fromTower_rho T hA p hCR hs0 hs 1 one_pos
  exact ⟨β₀, C, hβ₀, hC, h⟩

/-- **Smallness.**  For every `ε > 0` there is a threshold `β₁` after which the rooted terms of
`thm31b_zeroClass_fromTower_rho` satisfy `‖E T'‖ ≤ ε · exp(-(3/2 κ_dec) dExt T')`. -/
theorem thm31b_zeroClass_fromTower_small_rho {κmin : ℝ} (T : StepTower κmin)
    {A₁ : ℝ} (hA : 0 < A₁) (p : ℕ) {CR s : ℝ}
    (hCR : 0 < CR) (hs0 : 0 < s) (hs : s < 1 / 2) (ρ : ℝ) (hρ : 0 < ρ) {ε : ℝ} (hε : 0 < ε) :
  ∃ β₁ : ℝ, 2 ≤ β₁ ∧ ρ ≤ β₁ ∧
  ∀ (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁], 3 ∣ N₁ → 5 < N₁ →
  ∀ ν : ℝ, 0 < ν → ν * 3 ^ (2 * (k + 1)) ≤ 1 →
  ∀ β : ℝ, β₁ ≤ β → ∀ (p₁ : ℝ), 0 < p₁ →
  p₁ ≤ pLog A₁ p (β * 3 ^ k) →
  StepScaleData T k hk N₁ ν β p₁ →
  ∀ g : Fld 3 3 N₁ T.m₁ (k + 1) 2,
    g ∈ l1BallRho 3 3 N₁ T.m₁ (k + 1) 2 ρ →
  ∀ (y : CTorus 3 3 N₁ T.m₁ (k + 1)) (i : Fin 2),
    ∃ E : Finset (CubeB (d := 3) (L := 3) (N₁ := N₁) (m₁ := T.m₁) (K := k + 1) 1 (k + 1)
        Set.univ) → ℂ,
      (T.step k hk N₁ ν β p₁).M0C (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) g y i =
        (((T.step k hk N₁ ν β p₁).betaU ^ (1 / 2 : ℝ) : ℝ) : ℂ) * ∑ T', E T' ∧
      (∀ T', rootCube (m₀ := 1) (blockIndex y) ∉ T' → E T' = 0) ∧
      ∀ T', ‖E T'‖ ≤ ε * Real.exp (-(3 / 2 * T.κdec) * dExt T') := by
  obtain ⟨β₀, C, hβ₀, hρβ, hC, hmain⟩ := thm31b_zeroClass_fromTower_rho T hA p hCR hs0 hs ρ hρ
  obtain ⟨β₂, hβ₂, hsm⟩ := obsPrefactor_small_scale p hs0 (ε := ε / (C + 1)) (by positivity)
  refine ⟨max β₀ β₂, le_max_of_le_left hβ₀, le_max_of_le_left hρβ, ?_⟩
  intro k hk N₁ _ h3 h5 ν hν hνk β hβ p₁ hp hp₁ hsc g hg y i
  obtain ⟨E, h1, h2, h3'⟩ := hmain k hk N₁ h3 h5 ν hν hνk β (le_trans (le_max_left _ _) hβ) p₁ hp
    hp₁ hsc g hg y i
  refine ⟨E, h1, h2, fun T' => (h3' T').trans ?_⟩
  have hs' := hsm k β (le_trans (le_max_right _ _) hβ)
  have hCe : C * obsPrefactor p s (β * 3 ^ k) ≤ ε := by
    have h0 : 0 ≤ obsPrefactor p s (β * 3 ^ k) := by
      have hb : 1 ≤ β * 3 ^ k := by
        have : (1 : ℝ) ≤ 3 ^ k := one_le_pow₀ (by norm_num)
        have : (1 : ℝ) ≤ β := by linarith [le_max_left β₀ β₂, hβ₂, le_max_right β₀ β₂]
        nlinarith
      exact obsPrefactor_nonneg p s hb
    calc C * obsPrefactor p s (β * 3 ^ k) ≤ (C + 1) * (ε / (C + 1)) := by
          nlinarith
      _ = ε := by field_simp
  exact mul_le_mul_of_nonneg_right hCe (Real.exp_nonneg _)

/-- **Smallness.**  For every `ε > 0` there is a threshold `β₁` after which the rooted terms of
`thm31b_zeroClass_fromTower` satisfy `‖E T'‖ ≤ ε · exp(-(3/2 κ_dec) dExt T')`. -/
theorem thm31b_zeroClass_fromTower_small {κmin : ℝ} (T : StepTower κmin)
    {A₁ : ℝ} (hA : 0 < A₁) (p : ℕ) {CR s : ℝ}
    (hCR : 0 < CR) (hs0 : 0 < s) (hs : s < 1 / 2) {ε : ℝ} (hε : 0 < ε) :
  ∃ β₁ : ℝ, 2 ≤ β₁ ∧
  ∀ (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁], 3 ∣ N₁ → 5 < N₁ →
  ∀ ν : ℝ, 0 < ν → ν * 3 ^ (2 * (k + 1)) ≤ 1 →
  ∀ β : ℝ, β₁ ≤ β → ∀ (p₁ : ℝ), 0 < p₁ →
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
      ∀ T', ‖E T'‖ ≤ ε * Real.exp (-(3 / 2 * T.κdec) * dExt T') := by
  obtain ⟨β₁, hβ₁, -, h⟩ := thm31b_zeroClass_fromTower_small_rho T hA p hCR hs0 hs 1 one_pos hε
  exact ⟨β₁, hβ₁, h⟩

end Balaban.Inhabited
