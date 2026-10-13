/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.PhysAmpFacts
public import Balaban.Inhabited.ActivityFamilyAnalytic
public import Balaban.Inhabited.SourceWitnessJoint
public import Balaban.Inhabited.SourceWitnessOfWitnessG
public import Balaban.Inhabited.ObsUnconditional
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The analytic activity family on the common source witness

`sourceWitness_fromTower` and `activityFamilyAnalytic_fromTower` each call
`sourceDirectTerms_scale_fromTower` separately.  `sourceWitness_analytic_fromTower` returns the
conclusion of the first and, for the same `val, 𝒴, Tt`, the conclusion of
`activityFamilyAnalytic_of_witness` at `q = 1`.
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation
  Balaban.Localization Balaban.Localization.LevelPair Balaban.Localization.I5Inhabited
  Balaban.Polymer Balaban.SmallField.Def6 Balaban.Inhabited.LevelStep Filter Topology
  MeasureTheory Set

open Classical in
/-- **The exponent family of `sourceWitness_fromTower` for a given source witness, at source
radius `ρ`.**  The statement of `sourceWitness_exponent_of_witness` with the slice `η = ρ/β`
(`ε_U` is the amplitude at `ρ/β`), the fibre `physFibreRho … ρ`, and sources with `∑ |g| < ρ`,
for `0 < ρ` and `max 1 ρ ≤ β`.  The activity on the labels `thickLabels 𝒴 ⊕ thickLabels 𝒴` has
amplitude `4 ε_U`. -/
theorem sourceWitness_exponent_of_witness_rho {κmin : ℝ} (T : StepTower κmin)
    (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁] (h3N : 3 ∣ N₁)
    (ν : ℝ) (hνpos : 0 < ν) (hν : ν * 3 ^ (2 * (k + 1)) ≤ 1) (β ρ : ℝ) (hρ : 0 < ρ)
    (hβρ : max 1 ρ ≤ β)
    (p₁ : ℝ) (hp0 : 0 < p₁) (D : StepScaleData T k hk N₁ ν β p₁)
    (S : StepSetting 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) (hS : S = T.step k hk N₁ ν β p₁)
    (hp : 0 < S.p₁)
    :
    ∀ (val : ((S.U × Fin 2 → ℂ) × (S.U × Fin 2 → ℂ)) → ((S.U × Fin 2 → ℂ) × (S.U × Fin 2 → ℂ)) →
            ℂ → (RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2 × (CTorus 3 3 N₁ T.m₁ (k + 1) → Fin 2 → ℂ)) → ℂ)
    (𝒴 : Finset (Set (CTorus 3 3 N₁ T.m₁ (k + 1))))
    (Tt : Set (CTorus 3 3 N₁ T.m₁ (k + 1)) → ((S.U × Fin 2 → ℂ) × (S.U × Fin 2 → ℂ)) →
            ((S.U × Fin 2 → ℂ) × (S.U × Fin 2 → ℂ)) → ℂ →
            (RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2 × (CTorus 3 3 N₁ T.m₁ (k + 1) → Fin 2 → ℂ)) → ℂ)
    (hdom : ∀ Y ∈ 𝒴, IsDj 1 (k + 1) Y)
    (_hval : ∀ x w σ Θ, val x w σ Θ =
            (-(S.β : ℂ)) * raySrc3 (hatFun S.G' S.a₁ S.ν T.t S.hG'
              ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)
              (interactionOne S.hG S.hG' (le_refl (k + 1)) S.a₁ S.ν T.t)) taylorWeight x.1 w.1 σ
                Θ.1 +
            (S.β : ℂ) * (∑ s : CTorus 3 3 N₁ T.m₁ (k + 1) × Fin 2, Θ.2 s.1 s.2 *
              dirTermSrc (hatFun S.G' S.a₁ S.ν T.t S.hG' ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)
                (onXi S.G' S.a₁ S.ν T.t
                  (fun D ψ' => svec (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁))
                    (flFieldOne S.G' (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) T.BG₂ T.κ S.a₁ S.ν D ψ')
                      s.1 s.2)))
                (fun _ => (1 : ℂ)) x.2 w.2 σ Θ.1))
    (_hI : ∀ Θ ∈ physSΛEta S S.a₁ S.ν T.t (ρ / S.β),
            ∃ I' : DirectTerms S 1 hp (fun ψ => (ψ, ψ)) p₁ 2
                (S.β * prop33EpsEtaScaled 3 3 2 T.m₁ k 1 S.a₁ T.BG T.BG₂ T.κ T.t
                  (lvR T.κ T.t (β * 3 ^ k) p₁) 0 0 (ρ / S.β)) (2 * T.κdec - 1) Θ
                (physSΛEta S S.a₁ S.ν T.t (ρ / S.β))
                (physXW S (lvCpsi T.κ T.t (β * 3 ^ k)) 2 2 (lvR T.κ T.t (β * 3 ^ k) p₁)) val
                (physAgΘ S) (AgFDirPair S),
              I'.𝒴 = 𝒴 ∧ I'.T = Tt)
    (εU : ℝ) (_hεU : εU = β * prop33EpsEtaScaled 3 3 2 T.m₁ k 1 1 T.BG T.BG₂ T.κ T.t
      (lvR T.κ T.t (β * 3 ^ k) p₁) 0 0 (ρ / β)) (_hεpos : 0 < εU),
    ∃ Jr : S.JointRep T.t (2 * p₁),
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
                ((S.blockSplit 1 hp).restr x)) := by
  classical
  intro val 𝒴 Tt hdom hval hI εU hεU hεpos
  subst hS
  have e : (((3 : ℕ) : ℝ)) ^ (k * (3 - 2)) = 3 ^ k := by norm_num
  have hp' : 0 < (T.toG.step k hk N₁ ν β p₁).p₁ := hp
  have G := sourceWitness_exponent_of_witnessG_rho T.toG k hk N₁ (by simpa using h3N) ν hνpos
    (by simpa using hν) β ρ hρ hβρ p₁ hp0 (β * ((3 : ℕ) : ℝ) ^ (k * (3 - 2))) rfl
    (StepTower.scaleDataG_of_fixed T D) rfl (T.toG.step k hk N₁ ν β p₁) HEq.rfl hp'
  unfold StepTowerG.step at G
  revert G
  generalize hb : β * ((3 : ℕ) : ℝ) ^ (k * (3 - 2)) = b
  generalize hϱ : rhoSepG 3 3 T.toG.m₁ = ϱ
  have hϱ' : ϱ = rhoSep T.m₁ := hϱ.symm.trans (rhoSepG_three _)
  have hb' : b = β * 3 ^ k := hb.symm.trans (by rw [e])
  subst hϱ' hb'
  intro G
  exact G val 𝒴 Tt hdom hval hI εU hεU hεpos

open Classical in
/-- **The exponent family of `sourceWitness_fromTower` for a given source witness.**  Given
`val, 𝒴, Tt` with the formula for `val` and an instance at every point of the slice `η = 1/β`
(the output of `sourceDirectTerms_scale_fromTower` at `q = 1`), and `ε_U` the physical amplitude,
there are a joint representation `Jr` and, at every point of the constant-`h₀` fibre, an activity
on the labels `thickLabels 𝒴 ⊕ thickLabels 𝒴` of amplitude `4 ε_U` summing to
`W₁(s) + W₂(t)` along the segments. -/
theorem sourceWitness_exponent_of_witness {κmin : ℝ} (T : StepTower κmin)
    (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁] (h3N : 3 ∣ N₁)
    (ν : ℝ) (hνpos : 0 < ν) (hν : ν * 3 ^ (2 * (k + 1)) ≤ 1) (β : ℝ) (hβ1 : 1 ≤ β)
    (p₁ : ℝ) (hp0 : 0 < p₁) (D : StepScaleData T k hk N₁ ν β p₁)
    (S : StepSetting 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) (hS : S = T.step k hk N₁ ν β p₁)
    (hp : 0 < S.p₁)
    :
    ∀ (val : ((S.U × Fin 2 → ℂ) × (S.U × Fin 2 → ℂ)) → ((S.U × Fin 2 → ℂ) × (S.U × Fin 2 → ℂ)) →
            ℂ → (RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2 × (CTorus 3 3 N₁ T.m₁ (k + 1) → Fin 2 → ℂ)) → ℂ)
    (𝒴 : Finset (Set (CTorus 3 3 N₁ T.m₁ (k + 1))))
    (Tt : Set (CTorus 3 3 N₁ T.m₁ (k + 1)) → ((S.U × Fin 2 → ℂ) × (S.U × Fin 2 → ℂ)) →
            ((S.U × Fin 2 → ℂ) × (S.U × Fin 2 → ℂ)) → ℂ →
            (RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2 × (CTorus 3 3 N₁ T.m₁ (k + 1) → Fin 2 → ℂ)) → ℂ)
    (hdom : ∀ Y ∈ 𝒴, IsDj 1 (k + 1) Y)
    (_hval : ∀ x w σ Θ, val x w σ Θ =
            (-(S.β : ℂ)) * raySrc3 (hatFun S.G' S.a₁ S.ν T.t S.hG'
              ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)
              (interactionOne S.hG S.hG' (le_refl (k + 1)) S.a₁ S.ν T.t)) taylorWeight x.1 w.1 σ
                Θ.1 +
            (S.β : ℂ) * (∑ s : CTorus 3 3 N₁ T.m₁ (k + 1) × Fin 2, Θ.2 s.1 s.2 *
              dirTermSrc (hatFun S.G' S.a₁ S.ν T.t S.hG' ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)
                (onXi S.G' S.a₁ S.ν T.t
                  (fun D ψ' => svec (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁))
                    (flFieldOne S.G' (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) T.BG₂ T.κ S.a₁ S.ν D ψ')
                      s.1 s.2)))
                (fun _ => (1 : ℂ)) x.2 w.2 σ Θ.1))
    (_hI : ∀ Θ ∈ physSΛEta S S.a₁ S.ν T.t (1 / S.β),
            ∃ I' : DirectTerms S 1 hp (fun ψ => (ψ, ψ)) p₁ 2
                (S.β * prop33EpsEtaScaled 3 3 2 T.m₁ k 1 S.a₁ T.BG T.BG₂ T.κ T.t
                  (lvR T.κ T.t (β * 3 ^ k) p₁) 0 0 (1 / S.β)) (2 * T.κdec - 1) Θ
                (physSΛEta S S.a₁ S.ν T.t (1 / S.β))
                (physXW S (lvCpsi T.κ T.t (β * 3 ^ k)) 2 2 (lvR T.κ T.t (β * 3 ^ k) p₁)) val
                (physAgΘ S) (AgFDirPair S),
              I'.𝒴 = 𝒴 ∧ I'.T = Tt)
    (εU : ℝ) (_hεU : εU = β * prop33EpsEtaScaled 3 3 2 T.m₁ k 1 1 T.BG T.BG₂ T.κ T.t
      (lvR T.κ T.t (β * 3 ^ k) p₁) 0 0 (1 / β)) (_hεpos : 0 < εU),
    ∃ Jr : S.JointRep T.t (2 * p₁),
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
                ((S.blockSplit 1 hp).restr x)) := by
  classical
  exact sourceWitness_exponent_of_witness_rho T k hk N₁ h3N ν hνpos hν β 1 one_pos
    (max_le hβ1 hβ1) p₁ hp0 D S hS hp


open Classical in
/-- **The observable ray activities of `sourceWitness_fromTower` for a given source witness, at
source radius `ρ`.**  The statement of `sourceWitness_ray_of_witness` with the slice `η = ρ/β`
(`ε_U` is the amplitude at `ρ/β`) containing `(rawOf S.D', 0)` and `(rawOf S.D', g/β)` for
`∑ |g| < ρ`, and the conclusion for every `g` with `∑ |g| < ρ`, for `max 1 ρ ≤ β`. -/
theorem sourceWitness_ray_of_witness_rho {κmin : ℝ} (T : StepTower κmin)
    (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁] (h3N : 3 ∣ N₁)
    (ν : ℝ) (β ρ : ℝ) (hβρ : max 1 ρ ≤ β)
    (p₁ : ℝ) (D : StepScaleData T k hk N₁ ν β p₁)
    (S : StepSetting 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) (hS : S = T.step k hk N₁ ν β p₁)
    (hp : 0 < S.p₁)
    :
    ∀ (val : ((S.U × Fin 2 → ℂ) × (S.U × Fin 2 → ℂ)) → ((S.U × Fin 2 → ℂ) × (S.U × Fin 2 → ℂ)) →
            ℂ → (RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2 × (CTorus 3 3 N₁ T.m₁ (k + 1) → Fin 2 → ℂ)) → ℂ)
    (𝒴 : Finset (Set (CTorus 3 3 N₁ T.m₁ (k + 1))))
    (Tt : Set (CTorus 3 3 N₁ T.m₁ (k + 1)) → ((S.U × Fin 2 → ℂ) × (S.U × Fin 2 → ℂ)) →
            ((S.U × Fin 2 → ℂ) × (S.U × Fin 2 → ℂ)) → ℂ →
            (RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2 × (CTorus 3 3 N₁ T.m₁ (k + 1) → Fin 2 → ℂ)) → ℂ)
    (hdom : ∀ Y ∈ 𝒴, IsDj 1 (k + 1) Y)
    (_hval : ∀ x w σ Θ, val x w σ Θ =
            (-(S.β : ℂ)) * raySrc3 (hatFun S.G' S.a₁ S.ν T.t S.hG'
              ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)
              (interactionOne S.hG S.hG' (le_refl (k + 1)) S.a₁ S.ν T.t)) taylorWeight x.1 w.1 σ
                Θ.1 +
            (S.β : ℂ) * (∑ s : CTorus 3 3 N₁ T.m₁ (k + 1) × Fin 2, Θ.2 s.1 s.2 *
              dirTermSrc (hatFun S.G' S.a₁ S.ν T.t S.hG' ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)
                (onXi S.G' S.a₁ S.ν T.t
                  (fun D ψ' => svec (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁))
                    (flFieldOne S.G' (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) T.BG₂ T.κ S.a₁ S.ν D ψ')
                      s.1 s.2)))
                (fun _ => (1 : ℂ)) x.2 w.2 σ Θ.1))
    (_hcont : DiagCont (fun ψ : S.U × Fin 2 → ℂ => (ψ, ψ))
            (physXW S (lvCpsi T.κ T.t (β * 3 ^ k)) 2 2 (lvR T.κ T.t (β * 3 ^ k) p₁))
            (physSΛEta S S.a₁ S.ν T.t (ρ / S.β)) 2 𝒴 Tt)
    (_hI : ∀ Θ ∈ physSΛEta S S.a₁ S.ν T.t (ρ / S.β),
            ∃ I' : DirectTerms S 1 hp (fun ψ => (ψ, ψ)) p₁ 2
                (S.β * prop33EpsEtaScaled 3 3 2 T.m₁ k 1 S.a₁ T.BG T.BG₂ T.κ T.t
                  (lvR T.κ T.t (β * 3 ^ k) p₁) 0 0 (ρ / S.β)) (2 * T.κdec - 1) Θ
                (physSΛEta S S.a₁ S.ν T.t (ρ / S.β))
                (physXW S (lvCpsi T.κ T.t (β * 3 ^ k)) 2 2 (lvR T.κ T.t (β * 3 ^ k) p₁)) val
                (physAgΘ S) (AgFDirPair S),
              I'.𝒴 = 𝒴 ∧ I'.T = Tt)
    (_hmem0 : (rawOf S.D', (0 : CTorus 3 3 N₁ T.m₁ (k + 1) → Fin 2 → ℂ)) ∈
      physSΛEta S S.a₁ S.ν T.t (ρ / S.β))
    (_hmemg : ∀ g : Fld 3 3 N₁ T.m₁ (k + 1) 2, ∑ x, ∑ i, ‖g x i‖ < ρ →
      (rawOf S.D', fun y i => g y i / (S.β : ℂ)) ∈ physSΛEta S S.a₁ S.ν T.t (ρ / S.β))
    (εU : ℝ) (_hεU : εU = β * prop33EpsEtaScaled 3 3 2 T.m₁ k 1 1 T.BG T.BG₂ T.κ T.t
      (lvR T.κ T.t (β * 3 ^ k) p₁) 0 0 (ρ / β)) (_hεpos : 0 < εU),
    0 < εU ∧ ∃ A₀ : ℂ → LabelAct (thickLabels 𝒴 hdom) (S.blockSplit 1 hp).Ωb
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
              S.WtwoC (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) g t x := by
  classical
  intro val 𝒴 Tt hdom hval hcont hI hmem0 hmemg εU hεU hεpos
  subst hS
  have e : (((3 : ℕ) : ℝ)) ^ (k * (3 - 2)) = 3 ^ k := by norm_num
  have hp' : 0 < (T.toG.step k hk N₁ ν β p₁).p₁ := hp
  have G := sourceWitness_ray_of_witnessG_rho T.toG k hk N₁ (by simpa using h3N) ν β ρ hβρ p₁
    (β * ((3 : ℕ) : ℝ) ^ (k * (3 - 2))) rfl (StepTower.scaleDataG_of_fixed T D) rfl
    (T.toG.step k hk N₁ ν β p₁) HEq.rfl hp'
  unfold StepTowerG.step at G
  revert G
  generalize hb : β * ((3 : ℕ) : ℝ) ^ (k * (3 - 2)) = b
  generalize hϱ : rhoSepG 3 3 T.toG.m₁ = ϱ
  have hϱ' : ϱ = rhoSep T.m₁ := hϱ.symm.trans (rhoSepG_three _)
  have hb' : b = β * 3 ^ k := hb.symm.trans (by rw [e])
  subst hϱ' hb'
  intro G
  exact G val 𝒴 Tt hdom hval hcont hI hmem0 hmemg εU hεU hεpos

open Classical in
/-- **The observable ray activities of `sourceWitness_fromTower` for a given source witness.**
Given `val, 𝒴, Tt` as in `sourceWitness_exponent_of_witness`, with diagonal continuity of `𝒴, Tt`
and the slice containing `(rawOf S.D', 0)` and `(rawOf S.D', g/β)` for `∑ |g| < 1`: the ray
activities of amplitude `ε_U` on the thick labels of `𝒴`. -/
theorem sourceWitness_ray_of_witness {κmin : ℝ} (T : StepTower κmin)
    (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁] (h3N : 3 ∣ N₁)
    (ν : ℝ) (β : ℝ) (hβ1 : 1 ≤ β)
    (p₁ : ℝ) (D : StepScaleData T k hk N₁ ν β p₁)
    (S : StepSetting 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) (hS : S = T.step k hk N₁ ν β p₁)
    (hp : 0 < S.p₁)
    :
    ∀ (val : ((S.U × Fin 2 → ℂ) × (S.U × Fin 2 → ℂ)) → ((S.U × Fin 2 → ℂ) × (S.U × Fin 2 → ℂ)) →
            ℂ → (RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2 × (CTorus 3 3 N₁ T.m₁ (k + 1) → Fin 2 → ℂ)) → ℂ)
    (𝒴 : Finset (Set (CTorus 3 3 N₁ T.m₁ (k + 1))))
    (Tt : Set (CTorus 3 3 N₁ T.m₁ (k + 1)) → ((S.U × Fin 2 → ℂ) × (S.U × Fin 2 → ℂ)) →
            ((S.U × Fin 2 → ℂ) × (S.U × Fin 2 → ℂ)) → ℂ →
            (RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2 × (CTorus 3 3 N₁ T.m₁ (k + 1) → Fin 2 → ℂ)) → ℂ)
    (hdom : ∀ Y ∈ 𝒴, IsDj 1 (k + 1) Y)
    (_hval : ∀ x w σ Θ, val x w σ Θ =
            (-(S.β : ℂ)) * raySrc3 (hatFun S.G' S.a₁ S.ν T.t S.hG'
              ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)
              (interactionOne S.hG S.hG' (le_refl (k + 1)) S.a₁ S.ν T.t)) taylorWeight x.1 w.1 σ
                Θ.1 +
            (S.β : ℂ) * (∑ s : CTorus 3 3 N₁ T.m₁ (k + 1) × Fin 2, Θ.2 s.1 s.2 *
              dirTermSrc (hatFun S.G' S.a₁ S.ν T.t S.hG' ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)
                (onXi S.G' S.a₁ S.ν T.t
                  (fun D ψ' => svec (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁))
                    (flFieldOne S.G' (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) T.BG₂ T.κ S.a₁ S.ν D ψ')
                      s.1 s.2)))
                (fun _ => (1 : ℂ)) x.2 w.2 σ Θ.1))
    (_hcont : DiagCont (fun ψ : S.U × Fin 2 → ℂ => (ψ, ψ))
            (physXW S (lvCpsi T.κ T.t (β * 3 ^ k)) 2 2 (lvR T.κ T.t (β * 3 ^ k) p₁))
            (physSΛEta S S.a₁ S.ν T.t (1 / S.β)) 2 𝒴 Tt)
    (_hI : ∀ Θ ∈ physSΛEta S S.a₁ S.ν T.t (1 / S.β),
            ∃ I' : DirectTerms S 1 hp (fun ψ => (ψ, ψ)) p₁ 2
                (S.β * prop33EpsEtaScaled 3 3 2 T.m₁ k 1 S.a₁ T.BG T.BG₂ T.κ T.t
                  (lvR T.κ T.t (β * 3 ^ k) p₁) 0 0 (1 / S.β)) (2 * T.κdec - 1) Θ
                (physSΛEta S S.a₁ S.ν T.t (1 / S.β))
                (physXW S (lvCpsi T.κ T.t (β * 3 ^ k)) 2 2 (lvR T.κ T.t (β * 3 ^ k) p₁)) val
                (physAgΘ S) (AgFDirPair S),
              I'.𝒴 = 𝒴 ∧ I'.T = Tt)
    (_hmem0 : (rawOf S.D', (0 : CTorus 3 3 N₁ T.m₁ (k + 1) → Fin 2 → ℂ)) ∈
      physSΛEta S S.a₁ S.ν T.t (1 / S.β))
    (_hmemg : ∀ g : Fld 3 3 N₁ T.m₁ (k + 1) 2, ∑ x, ∑ i, ‖g x i‖ < 1 →
      (rawOf S.D', fun y i => g y i / (S.β : ℂ)) ∈ physSΛEta S S.a₁ S.ν T.t (1 / S.β))
    (εU : ℝ) (_hεU : εU = β * prop33EpsEtaScaled 3 3 2 T.m₁ k 1 1 T.BG T.BG₂ T.κ T.t
      (lvR T.κ T.t (β * 3 ^ k) p₁) 0 0 (1 / β)) (_hεpos : 0 < εU),
    0 < εU ∧ ∃ A₀ : ℂ → LabelAct (thickLabels 𝒴 hdom) (S.blockSplit 1 hp).Ωb
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
              S.WtwoC (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) g t x := by
  classical
  exact sourceWitness_ray_of_witness_rho T k hk N₁ h3N ν β 1 (max_le hβ1 hβ1) p₁ D S hS hp

open Classical in
/-- **One witness for the source lane and the analytic activity family, at source radius `ρ`,
general tower.**  The statement of `sourceWitness_analytic_fromTower_rho` at
`T : StepTowerG d L N κmin`: block scale `T.m₀`, block coupling `β L^{k (d-2)}`, step `T.step`.
The clauses of `commonWitness_joint_fromTowerG_rho` for one `val, 𝒴, Tt`, and for the same
`val, 𝒴, Tt` the conclusion of `activityFamilyAnalytic_of_witnessG_rho` at `q = ρ`.  The fixed
statement `sourceWitness_analytic_fromTower_rho` is its corollary. -/
theorem sourceWitness_analytic_fromTowerG_rho {d L N : ℕ} [NeZero L] {κmin : ℝ} (T : StepTowerG d L N κmin) {A₁ : ℝ}
    (hA : 0 < A₁) (p : ℕ) :
    ∃ CE CF : ℝ, 0 < CE ∧ 0 < CF ∧
    ∀ ρ : ℝ, 0 < ρ → ∃ β₀ : ℝ, 2 ≤ β₀ ∧ ρ ≤ β₀ ∧
    ∀ (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁] (hLN : L ^ T.m₀ ∣ N₁), 5 < N₁ →
    ∀ ν : ℝ, 0 < ν → ν * (L : ℝ) ^ (2 * (k + 1)) ≤ 1 →
    ∀ β : ℝ, β₀ ≤ β → ∀ (p₁ : ℝ) (hp0 : 0 < p₁),
    ∀ b : ℝ, b = β * (L : ℝ) ^ (k * (d - 2)) → p₁ ≤ pLog A₁ p b → StepScaleDataG T k hk N₁ ν β p₁ →
    ∀ {ϱ : ℝ}, ϱ = rhoSepG d L T.m₁ → ∀ (S : StepSetting d L N₁ T.m₁ k N ϱ),
    HEq S (T.step k hk N₁ ν β p₁) →
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
      ∃ εU : ℝ,
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
          (Metric.ball (0 : ℂ) (3 / 2))) := by
  classical
  obtain ⟨CE, CF, hCE, hCF, H⟩ := commonWitness_joint_fromTowerG_rho T hA p
  refine ⟨CE, CF, hCE, hCF, fun ρ hρ => ?_⟩
  obtain ⟨β₀, h2, hρβ, H1⟩ := H ρ hρ
  refine ⟨β₀, h2, hρβ, ?_⟩
  intro k hk N₁ _ hLN hN ν hνpos hν β hβ p₁ hp0 b hb hp₁ D ϱ hϱ S hS hp
  subst hϱ
  have hS' : S = T.step k hk N₁ ν β p₁ := eq_of_heq hS
  subst hb
  subst hS'
  obtain ⟨val, 𝒴, Tt, hdom, hval, εU, hεU, hεpos, hbd, h1, h2', h3, hdiff, hcont, hI, hmem0, -, -⟩ :=
    H1 k hk N₁ hLN hN ν hνpos hν β hβ p₁ hp0 hp₁ D _ rfl hp
  have hβρ : max 1 ρ ≤ β := max_le (by linarith) (hρβ.trans hβ)
  refine ⟨val, 𝒴, Tt, hdom, hval, εU, hεU, hεpos, hbd, h1, h2', h3, ?_, hdiff⟩
  exact activityFamilyAnalytic_of_witnessG_rho T k hk N₁ hLN ν hνpos hν β ρ hβρ p₁ hp0 ρ hρ le_rfl
    (β * (L : ℝ) ^ (k * (d - 2))) rfl D rfl _ HEq.rfl hp val 𝒴 Tt hval hcont hI hmem0

open Classical in
/-- **One witness for the source lane and the analytic activity family, at source radius `ρ`.**
The statement of `sourceWitness_analytic_fromTower` with the slice `η = ρ/β` (`ε_U` is the
amplitude at `ρ/β`), the carriers `l1BallRho`, `physVqRho`, `physFibreRho`, `physVRho` of radius
`ρ`, and `q = ρ` in the analytic activity family.  The amplitude constants `C_E`, `C_F` are chosen
after `T` and do not depend on `ρ`; the threshold `β₀` is chosen after `ρ`, with `ρ ≤ β₀`; the
bound is `4 ε_U ≤ C_E (log b)^{3p}/√b + ρ C_F (log b)^p/√b`.  The proof is the one of
`sourceWitness_fromTower_rho`, with the exponent family, the ray activities and
`activityFamilyAnalytic_of_witness_rho` on the same `val, 𝒴, Tt`. -/
theorem sourceWitness_analytic_fromTower_rho {κmin : ℝ} (T : StepTower κmin) {A₁ : ℝ}
    (hA : 0 < A₁) (p : ℕ) :
    ∃ CE CF : ℝ, 0 < CE ∧ 0 < CF ∧
    ∀ ρ : ℝ, 0 < ρ → ∃ β₀ : ℝ, 2 ≤ β₀ ∧ ρ ≤ β₀ ∧
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
      ∃ εU : ℝ,
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
          (Metric.ball (0 : ℂ) (3 / 2))) := by
  classical
  obtain ⟨CE, CF, hCE, hCF, H⟩ := sourceWitness_analytic_fromTowerG_rho T.toG hA p
  refine ⟨CE, CF, hCE, hCF, fun ρ hρ => ?_⟩
  obtain ⟨β₀, h2, hρβ, H1⟩ := H ρ hρ
  refine ⟨β₀, h2, hρβ, ?_⟩
  intro k hk N₁ _ h3N hN ν hνpos hν β hβ p₁ hp0 hp₁ D S hS hp
  exact H1 k hk N₁ (by simpa using h3N) hN ν hνpos (by simpa using hν) β hβ p₁ hp0 (β * 3 ^ k)
    (by norm_num) hp₁ (StepTower.scaleDataG_of_fixed T D) (rhoSepG_three _).symm S
    (by rw [hS]; exact (StepTower.toG_step_heq T k hk N₁ ν β p₁).symm) hp

open Classical in
/-- **One witness for the source lane and the analytic activity family.**  The conclusion of
`sourceWitness_fromTower` (source activity records, exponent family on the fibre, observable ray
activities, amplitude `ε_U`, all for one `val, 𝒴, Tt`), and, for the SAME `val, 𝒴, Tt` (slice
`η = 1/β`), the conclusion of `activityFamilyAnalytic_of_witness` at `q = 1` and the ray clause of
`sourceDirectTerms_scale_fromTower_ray_full`: a joint
representation, a `DirectTerms` record `I` with `I.𝒴 = 𝒴`, `I.T = Tt`, a relative family over
`physVq … 1`, and for every `K_c ≥ K₀(T.κ0)` the analytic family `labelActFamilyOn … I hF` with its
value, `W₁`, `W₂`, segment and zero-source identities.  The proof is the one of
`sourceWitness_fromTower`, run from the output of `sourceDirectTerms_scale_fromTower`. -/
theorem sourceWitness_analytic_fromTower {κmin : ℝ} (T : StepTower κmin) {A₁ : ℝ}
    (hA : 0 < A₁) (p : ℕ) :
    ∃ β₀ CE CF : ℝ, 2 ≤ β₀ ∧ 0 < CE ∧ 0 < CF ∧
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
      ∃ εU : ℝ,
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
          (Metric.ball (0 : ℂ) (3 / 2))) := by
  obtain ⟨CE, CF, hCE, hCF, H⟩ := sourceWitness_analytic_fromTower_rho T hA p
  obtain ⟨β₀, h2, -, H1⟩ := H 1 one_pos
  refine ⟨β₀, CE, CF, h2, hCE, hCF, ?_⟩
  intro k hk N₁ _ h3N hN ν hνpos hν β hβ p₁ hp0 hp₁ D S hS hp
  obtain ⟨val, 𝒴, Tt, hdom, hval, εU, hεU, hεpos, hbd, rest⟩ :=
    H1 k hk N₁ h3N hN ν hνpos hν β hβ p₁ hp0 hp₁ D S hS hp
  rw [one_mul] at hbd
  exact ⟨val, 𝒴, Tt, hdom, hval, εU, hεU, hεpos, hbd, rest⟩

end Balaban.Inhabited
