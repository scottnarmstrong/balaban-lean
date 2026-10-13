/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.PhysAmpFacts
public import Balaban.Inhabited.SourceExponentFamily
public import Balaban.Inhabited.SourceWitnessOfWitnessG
public import Balaban.Fluctuation.ObsRayActivity
public import Balaban.Inhabited.ObsUnconditional
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# One witness for the source lane at the shared tower

The landed theorems `sourceActivityC_scale_fromTower`, `sourceExponentFamily_fromTower` and
`obsRayActivity_fromTower` each call `sourceDirectTerms_scale_fromTower` separately, so the
direct-term value, the domain family `𝒴` and the terms `Tt` of their conclusions cannot be
identified.  `sourceWitness_fromTower` calls it once, per scale, and returns for that single
`val, 𝒴, Tt` the activity records of every source, the exponent family on the constant-`h_0`
fibre and the observable ray activities, together with the amplitude `ε_U`, `0 < ε_U`, and its
log-form bound `4 ε_U <= C_E (log b)^(3p) / sqrt b + C_F (log b)^p / sqrt b`, `b = β 3^k`.
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation
  Balaban.Localization Balaban.Localization.LevelPair Balaban.Localization.I5Inhabited
  Balaban.Polymer Balaban.SmallField.Def6 Balaban.Inhabited.LevelStep Filter Topology
  MeasureTheory Set

open Classical in
/-- **One witness for the source lane and the ray premise of the observable lane, sources of
`ℓ¹`-size `< ρ`, general tower.**  The statement of `commonWitness_joint_fromTower_rho` at
`T : StepTowerG d L N κmin`: block scale `T.m₀`, block coupling `β L^{k (d-2)}`, step `T.step`;
the fixed theorem is its corollary.  Original description of the fixed theorem:  After `T` choose `C_E, C_F`; for every `ρ > 0` a threshold `β₀` with
`2 ≤ β₀` and `ρ ≤ β₀`.  At every admissible scale there are `val, 𝒴, Tt` carrying every clause of
`sourceWitness_fromTower_rho` (slice `η = ρ/β`, `ε_U` on that slice, `4 ε_U ≤ C_E … + ρ C_F …`,
sources in `l1BallRho … ρ`, `Aseg` over `physFibreRho … ρ`) and the premise of
`obsMarks_zeroClass_family_of_ray_ksupp_rho` (`hray`: diagonal continuity, an instance at every
point of the slice `ρ/β`, the two source points in the slice, and the ray clause), for these
`val, 𝒴, Tt`.  The analytic family and the zero-source family of
`commonWitness_joint_fromTower` are not part of this statement. -/
theorem commonWitness_joint_fromTowerG_rho {d L N : ℕ} [NeZero L] {κmin : ℝ} (T : StepTowerG d L N κmin) {A₁ : ℝ}
    (hA : 0 < A₁) (p : ℕ) :
    ∃ CE CF : ℝ, 0 < CE ∧ 0 < CF ∧
    ∀ ρ : ℝ, 0 < ρ → ∃ β₀ : ℝ, 2 ≤ β₀ ∧ ρ ≤ β₀ ∧
    ∀ (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁], L ^ T.m₀ ∣ N₁ → 5 < N₁ →
    ∀ ν : ℝ, 0 < ν → ν * (L : ℝ) ^ (2 * (k + 1)) ≤ 1 →
    ∀ β : ℝ, β₀ ≤ β → ∀ (p₁ : ℝ), 0 < p₁ →
    p₁ ≤ pLog A₁ p (β * (L : ℝ) ^ (k * (d - 2))) → StepScaleDataG T k hk N₁ ν β p₁ →
    ∀ (S : StepSetting d L N₁ T.m₁ k N (rhoSepG d L T.m₁)), S = T.step k hk N₁ ν β p₁ →
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
              (fun D ψ' => svec (stepG d L N₁ T.m₁ k (rhoSepG d L T.m₁))
                (flFieldOne S.G' (stepG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) T.BG₂ T.κ S.a₁ S.ν D ψ')
                  s.1 s.2)))
            (fun _ => (1 : ℂ)) x.2 w.2 σ Θ.1)) ∧
      ∃ εU : ℝ,
      εU = β * prop33EpsEtaScaled d L N T.m₁ k T.m₀ 1 T.BG T.BG₂ T.κ T.t
        (lvRG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2))) p₁) 0 0 (ρ / β) ∧ 0 < εU ∧
      4 * εU ≤ CE * (Real.log (β * (L : ℝ) ^ (k * (d - 2)))) ^ (3 * p) / Real.sqrt (β * (L : ℝ) ^ (k * (d - 2))) +
        ρ * CF * (Real.log (β * (L : ℝ) ^ (k * (d - 2)))) ^ p / Real.sqrt (β * (L : ℝ) ^ (k * (d - 2))) ∧
      (∀ g : Fld d L N₁ T.m₁ (k + 1) N, g ∈ l1BallRho d L N₁ T.m₁ (k + 1) N ρ →
        ∃ BR : StepActivityBound S (zeroClass d L N₁ T.m₁ k N (rhoSepG d L T.m₁)) g,
        ∃ BC : StepActivityBoundC S (zeroClass d L N₁ T.m₁ k N (rhoSepG d L T.m₁)) g,
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
            Jr.W1 (zeroClass d L N₁ T.m₁ k N (rhoSepG d L T.m₁))
                ((e.1 : RawData d L (N₁ * L ^ T.m₁) (k + 1) N), (p.1 : ℂ) • S.hatC x) +
              Jr.W2 (zeroClass d L N₁ T.m₁ k N (rhoSepG d L T.m₁)) e.2
                ((e.1 : RawData d L (N₁ * L ^ T.m₁) (k + 1) N), (p.2 : ℂ) • S.hatC x) =
            ∑ y, (Aseg e he p).H y ((S.blockSplit T.m₀ hp).restr x)) ∧
        (∀ g : Fld d L N₁ T.m₁ (k + 1) N, ∑ x, ∑ i, ‖g x i‖ < ρ →
          ∃ he : ((⟨rawOf S.D', rawOf_mem_rawSub _⟩ : rawSub N S.G'), g) ∈
              physFibreRho S S.a₁ S.ν T.t ρ,
            ∀ p ∈ stepSegments, ∀ᵐ x ∂S.nuFl,
              S.WoneC (zeroClass d L N₁ T.m₁ k N (rhoSepG d L T.m₁)) p.1 x +
                S.WtwoC (zeroClass d L N₁ T.m₁ k N (rhoSepG d L T.m₁)) g p.2 x =
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
              S.WoneC (zeroClass d L N₁ T.m₁ k N (rhoSepG d L T.m₁)) 1 x +
              S.WtwoC (zeroClass d L N₁ T.m₁ k N (rhoSepG d L T.m₁)) g t x) ∧
      (∀ (Y : Set (CTorus d L N₁ T.m₁ (k + 1)))
        (Θ : RawData d L (N₁ * L ^ T.m₁) (k + 1) N × (CTorus d L N₁ T.m₁ (k + 1) → Fin N → ℂ)),
        Θ ∈ physSΛEta S S.a₁ S.ν T.t (ρ / S.β) → ∀ ψ : S.U × Fin N → ℂ,
        (∀ p, ‖ψ p‖ ≤ p₁) →
        DifferentiableOn ℂ (fun ζ : ℂ => Tt Y (ζ • ψ, ζ • ψ) (ζ • ψ, ζ • ψ) 1 Θ)
          (Metric.ball (0 : ℂ) (3 / 2))) ∧
      (DiagCont (fun ψ : S.U × Fin N → ℂ => (ψ, ψ))
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
              (Metric.ball (0 : ℂ) (3 / 2)))) := by
  classical
  have hd := T.hd
  have hL := T.hL
  have hN := T.hN
  have hd0 : 0 < d := by omega
  have hent := aEnt_nonneg d L
  have hc1 := one_le_c1 d L
  have ht0 := T.t_pos
  have hρ4 := T.rho_nonneg
  have hB0 := T.fam_nonneg
  have hκ0 := T.κ0_nonneg
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
  obtain ⟨Kc'', hKc''⟩ : ∃ x : ℝ, x = K0 d L T.κ0 + 1 := ⟨_, rfl⟩
  have hKc''pos : 0 < Kc'' := by have := K0_pos d L T.κ0; rw [hKc'']; linarith
  have hκdec0 : 0 ≤ T.κdec := by have := T.κdec_lower; linarith
  have hκ'0 : 0 ≤ T.κ' := by rw [T.κ'_eq]; linarith
  have hκa' : T.κ' + 3 * T.κ0 + c1 d L + 3 / 2 ≤ 2 * T.κdec - 1 := by
    rw [T.κ'_eq, T.κdec_eq]; linarith
  obtain ⟨CE, hCE⟩ : ∃ x : ℝ, x = 4 * (P * (4 * A₁ / lvKappaG d L N T.κ T.t) ^ 3 + 1) := ⟨_, rfl⟩
  obtain ⟨CF, hCF⟩ : ∃ x : ℝ, x = 16 * A₁ * (Q * T.t) / lvKappaG d L N T.κ T.t := ⟨_, rfl⟩
  have hCE0 : 0 < CE := by rw [hCE]; positivity
  have hCF0 : 0 < CF := by rw [hCF]; positivity
  refine ⟨CE, CF, hCE0, hCF0, ?_⟩
  intro ρ hρ
  refine ⟨max (max (max 2 β₁) (daThreshold ((CE + ρ * CF) / 4)
      (daT d L 4 (2 * Kc'') T.κdec T.κ0 T.κ') (3 * p))) ρ,
    le_trans (le_max_left _ _) ((le_max_left _ _).trans (le_max_left _ _)),
    le_max_right _ _, ?_⟩
  intro k hk N₁ _ hLN hN₁ ν hνpos hν β hβ p₁ hp0 hp₁ D S hS hp
  have hν0 : 0 ≤ ν := hνpos.le
  obtain ⟨⟨⟨hβ2, hβ₁⟩, hβd⟩, hβρ⟩ : ((2 ≤ β ∧ β₁ ≤ β) ∧ daThreshold ((CE + ρ * CF) / 4)
        (daT d L 4 (2 * Kc'') T.κdec T.κ0 T.κ') (3 * p) ≤ β) ∧ ρ ≤ β := by
    simpa only [max_le_iff] using hβ
  have hβ0 : 0 < β := by linarith
  have hβ1 : 1 ≤ β := by linarith
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast (by omega : 1 ≤ L)
  have h3k : (1 : ℝ) ≤ (L : ℝ) ^ (k * (d - 2)) := one_le_pow₀ hL1
  have hbβ : β ≤ β * (L : ℝ) ^ (k * (d - 2)) := le_mul_of_one_le_right hβ0.le h3k
  have hb0 : 0 < β * (L : ℝ) ^ (k * (d - 2)) := by positivity
  have hexp : Real.exp 1 ≤ β * (L : ℝ) ^ (k * (d - 2)) := le_trans hexpβ₁ (hβ₁.trans hbβ)
  have hℓ : 1 ≤ Real.log (β * (L : ℝ) ^ (k * (d - 2))) := (Real.le_log_iff_exp_le hb0).2 hexp
  have hamp := (hA' (β * (L : ℝ) ^ (k * (d - 2))) (hβ₁.trans hbβ) p₁ hp0 hp₁).2 P (Q * T.t) ρ hP0
    hK0.le hρ.le
  obtain ⟨R0⟩ := D.ray
  have hr0 := D.r_pos
  have hcψ0 := D.cψ_pos
  have hC := D.core
  have hD := D.xi
  -- the physical amplitude on the slice `η = ρ/β`
  set εU : ℝ := β * prop33EpsEtaScaled d L N T.m₁ k T.m₀ 1 T.BG T.BG₂ T.κ
      T.t (lvRG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2))) p₁) 0 0 (ρ / β) with hεU
  have hbU : (T.step k hk N₁ ν β p₁).betaU = β * (L : ℝ) ^ (k * (d - 2)) :=
    hatStepKG_betaU (d := d) (L := L) (N₁ := N₁) hN (by omega) k T.m₁ (rhoSepG d L T.m₁) hk ν β
      p₁ T.δ
  obtain ⟨hid, hpot, hterm0, hεle', hεpos⟩ := physAmp_facts (T.step k hk N₁ ν β p₁)
    (by omega) hL T.m₀ (compWeight_one_mem hL hk) rfl hβ0 rfl hbU hQ0 ht0 hρ4 hr0 hρ hQdef hPdef hεU
  have hεle := hεle' _ hamp
  have hε4 := sourceAmp_scale_four_general (A₁ := A₁) (κ₁ := lvKappaG d L N T.κ T.t) (P := P)
    (K := Q * T.t) (q := ρ) (CE := CE) (CF := CF) p hb0 (by linarith) hCE hCF hεle
  have hDA0 := sourceAmp_doubled_hDA_rho_general d L (A₁ := A₁) (κ₁ := lvKappaG d L N T.κ T.t)
    (P := P) (K := Q * T.t) (q := ρ) (ρ := ρ) (b := β * (L : ℝ) ^ (k * (d - 2))) (ε := εU)
    (Kc' := Kc'') (CE := CE) (CF := CF) p hA hκ1 hP0 hK0.le hρ.le le_rfl hCE hCF hℓ hb0 hKc''pos
    T.κdec T.κ0 T.κ' (hβd.trans hbβ) hεle
  subst hS
  set S := T.step k hk N₁ ν β p₁ with hSdef
  -- the direct terms, selected once for the slice `η = 1/β`
  obtain ⟨val, 𝒴, Tt, hval, -, hcont, hI, hmem0, hmemg, hray⟩ :=
    sourceDirectTerms_scale_fromTowerG_ray_full_rho T k hk N₁ hLN hN₁ ν hνpos hν β ρ hρ (max_le hβ1 hβρ) p₁ ρ hρ le_rfl D (T.step k hk N₁ ν β p₁) rfl hp
  obtain ⟨I₀, h𝒴₀, hT₀⟩ := hI _ hmem0
  have hdom : ∀ Y ∈ 𝒴, IsDj T.m₀ (k + 1) Y := fun Y hY => I₀.dom Y (h𝒴₀ ▸ hY)
  have hbound : 4 * εU ≤ CE * (Real.log (β * (L : ℝ) ^ (k * (d - 2)))) ^ (3 * p) / Real.sqrt (β * (L : ℝ) ^ (k * (d - 2))) +
      ρ * CF * (Real.log (β * (L : ℝ) ^ (k * (d - 2)))) ^ p / Real.sqrt (β * (L : ℝ) ^ (k * (d - 2))) :=
    hε4
  refine ⟨val, 𝒴, Tt, hdom, hval, εU, hεU, hεpos, hbound, ?_, ?_, ?_,
    fun Y Θ hΘ ψ hψ => hray Y Θ hΘ ψ hψ,
    ⟨hcont, hI, hmem0, hmemg, fun Y hY Θ hΘ ψ hψ => hray Y Θ hΘ ψ hψ⟩⟩
  · intro g hg
    obtain ⟨Ig, h𝒴g, hTg⟩ := hI _ (hmemg g hg)
    obtain ⟨BR, hm, hLb, hLab, hBS, hk0, hk', hκH, hεH, hKc⟩ :=
      stepActivityBound_zeroClass_source_of_directTerms_shared (T.step k hk N₁ ν β p₁)
        (ρ := p₁) (κ0 := T.κ0) (κ' := T.κ') (Kc' := Kc'') (a := 2 * T.κdec - 1)
        hC (by norm_num) hr0 hcψ0.le T.large_block T.dom_margin T.coer_margin T.δc_small
        D.fl_radius T.c7_cap (R := 2) le_rfl T.t_cap T.bg0_cap T.cK2_cap T.cK2'_cap T.bg1_cap
        (by norm_num) D.ray_margin hD hLN hp0 le_rfl (by rw [hεU] at hεpos; exact hεpos) T.κ0_ent hKc''.ge hκ'0 hκa'
        (by rw [hεU] at hDA0; exact hDA0) R0
        D.p_lt (by norm_num) g I₀ Ig
        (fun x u => by rw [hval]; simp)
        (fun x u => hval _ _ _ _) hdom h𝒴₀ h𝒴g
    obtain ⟨BC, hCm, hCLb, hCLab, hCBS, hCk0, hCk', hCκH, hCεH, hCKc⟩ :=
      stepActivityBoundC_of_activityBound_exposed R0 hp0 D.p_lt BR
    have hBε : BR.εH = 4 * εU := by
      rw [hεH, (fun E : ℝ => by ring : ∀ E : ℝ, 2 * (2 * E) = 4 * E)]
      exact congrArg _ hεU.symm
    exact ⟨BR, BC, hm, hCm.trans hm, hLb, hCLb, hLab, hCLab, hBS, hCBS, hk0, hCk0.trans hk0, hk',
      hCk'.trans hk', hκH, hCκH, by rw [hKc, hKc''], hCKc, hCεH.symm, hBε⟩
  · exact sourceWitness_exponent_of_witnessG_rho T k hk N₁ hLN ν hνpos hν β ρ hρ (max_le hβ1 hβρ) p₁ hp0
      (β * (L : ℝ) ^ (k * (d - 2))) rfl D rfl S HEq.rfl hp val 𝒴 Tt hdom hval hI εU hεU hεpos
  · exact sourceWitness_ray_of_witnessG_rho T k hk N₁ hLN ν β ρ (max_le hβ1 hβρ) p₁
      (β * (L : ℝ) ^ (k * (d - 2))) rfl D rfl S HEq.rfl hp val 𝒴 Tt hdom hval hcont hI hmem0 hmemg
      εU hεU hεpos


open Classical in
/-- **One witness for the source lane at the general tower, sources of `ℓ¹`-size `< ρ`.**  The
statement of `sourceWitness_fromTower_rho` at `T : StepTowerG d L N κmin`: the clauses of
`commonWitness_joint_fromTowerG_rho` for one `val, 𝒴, Tt` without the ray differentiability and the
witness data. -/
theorem sourceWitness_fromTowerG_rho {d L N : ℕ} [NeZero L] {κmin : ℝ} (T : StepTowerG d L N κmin) {A₁ : ℝ}
    (hA : 0 < A₁) (p : ℕ) :
    ∃ CE CF : ℝ, 0 < CE ∧ 0 < CF ∧
    ∀ ρ : ℝ, 0 < ρ → ∃ β₀ : ℝ, 2 ≤ β₀ ∧ ρ ≤ β₀ ∧
    ∀ (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁], L ^ T.m₀ ∣ N₁ → 5 < N₁ →
    ∀ ν : ℝ, 0 < ν → ν * (L : ℝ) ^ (2 * (k + 1)) ≤ 1 →
    ∀ β : ℝ, β₀ ≤ β → ∀ (p₁ : ℝ), 0 < p₁ →
    p₁ ≤ pLog A₁ p (β * (L : ℝ) ^ (k * (d - 2))) → StepScaleDataG T k hk N₁ ν β p₁ →
    ∀ (S : StepSetting d L N₁ T.m₁ k N (rhoSepG d L T.m₁)), S = T.step k hk N₁ ν β p₁ →
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
              (fun D ψ' => svec (stepG d L N₁ T.m₁ k (rhoSepG d L T.m₁))
                (flFieldOne S.G' (stepG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) T.BG₂ T.κ S.a₁ S.ν D ψ')
                  s.1 s.2)))
            (fun _ => (1 : ℂ)) x.2 w.2 σ Θ.1)) ∧
      ∃ εU : ℝ,
      εU = β * prop33EpsEtaScaled d L N T.m₁ k T.m₀ 1 T.BG T.BG₂ T.κ T.t
        (lvRG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2))) p₁) 0 0 (ρ / β) ∧ 0 < εU ∧
      4 * εU ≤ CE * (Real.log (β * (L : ℝ) ^ (k * (d - 2)))) ^ (3 * p) / Real.sqrt (β * (L : ℝ) ^ (k * (d - 2))) +
        ρ * CF * (Real.log (β * (L : ℝ) ^ (k * (d - 2)))) ^ p / Real.sqrt (β * (L : ℝ) ^ (k * (d - 2))) ∧
      (∀ g : Fld d L N₁ T.m₁ (k + 1) N, g ∈ l1BallRho d L N₁ T.m₁ (k + 1) N ρ →
        ∃ BR : StepActivityBound S (zeroClass d L N₁ T.m₁ k N (rhoSepG d L T.m₁)) g,
        ∃ BC : StepActivityBoundC S (zeroClass d L N₁ T.m₁ k N (rhoSepG d L T.m₁)) g,
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
            Jr.W1 (zeroClass d L N₁ T.m₁ k N (rhoSepG d L T.m₁))
                ((e.1 : RawData d L (N₁ * L ^ T.m₁) (k + 1) N), (p.1 : ℂ) • S.hatC x) +
              Jr.W2 (zeroClass d L N₁ T.m₁ k N (rhoSepG d L T.m₁)) e.2
                ((e.1 : RawData d L (N₁ * L ^ T.m₁) (k + 1) N), (p.2 : ℂ) • S.hatC x) =
            ∑ y, (Aseg e he p).H y ((S.blockSplit T.m₀ hp).restr x)) ∧
        (∀ g : Fld d L N₁ T.m₁ (k + 1) N, ∑ x, ∑ i, ‖g x i‖ < ρ →
          ∃ he : ((⟨rawOf S.D', rawOf_mem_rawSub _⟩ : rawSub N S.G'), g) ∈
              physFibreRho S S.a₁ S.ν T.t ρ,
            ∀ p ∈ stepSegments, ∀ᵐ x ∂S.nuFl,
              S.WoneC (zeroClass d L N₁ T.m₁ k N (rhoSepG d L T.m₁)) p.1 x +
                S.WtwoC (zeroClass d L N₁ T.m₁ k N (rhoSepG d L T.m₁)) g p.2 x =
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
              S.WoneC (zeroClass d L N₁ T.m₁ k N (rhoSepG d L T.m₁)) 1 x +
              S.WtwoC (zeroClass d L N₁ T.m₁ k N (rhoSepG d L T.m₁)) g t x) := by
  obtain ⟨CE, CF, hCE, hCF, H⟩ := commonWitness_joint_fromTowerG_rho T hA p
  refine ⟨CE, CF, hCE, hCF, fun ρ hρ => ?_⟩
  obtain ⟨β₀, h2, hρβ, H1⟩ := H ρ hρ
  refine ⟨β₀, h2, hρβ, ?_⟩
  intro k hk N₁ _ hLN hN ν hνpos hν β hβ p₁ hp0 hp₁ D S hS hp
  obtain ⟨val, 𝒴, Tt, hdom, hval, εU, hεU, hεpos, hbd, h4, h5, h6, -, -⟩ :=
    H1 k hk N₁ hLN hN ν hνpos hν β hβ p₁ hp0 hp₁ D S hS hp
  exact ⟨val, 𝒴, Tt, hdom, hval, εU, hεU, hεpos, hbd, h4, h5, h6⟩

open Classical in
/-- **One witness for the source lane and the ray premise of the observable lane, sources of
`ℓ¹`-size `< ρ`.**  After `T` choose `C_E, C_F`; for every `ρ > 0` a threshold `β₀` with
`2 ≤ β₀` and `ρ ≤ β₀`.  At every admissible scale there are `val, 𝒴, Tt` carrying every clause of
`sourceWitness_fromTower_rho` (slice `η = ρ/β`, `ε_U` on that slice, `4 ε_U ≤ C_E … + ρ C_F …`,
sources in `l1BallRho … ρ`, `Aseg` over `physFibreRho … ρ`) and the premise of
`obsMarks_zeroClass_family_of_ray_ksupp_rho` (`hray`: diagonal continuity, an instance at every
point of the slice `ρ/β`, the two source points in the slice, and the ray clause), for these
`val, 𝒴, Tt`.  The analytic family and the zero-source family of
`commonWitness_joint_fromTower` are not part of this statement. -/
theorem commonWitness_joint_fromTower_rho {κmin : ℝ} (T : StepTower κmin) {A₁ : ℝ}
    (hA : 0 < A₁) (p : ℕ) :
    ∃ CE CF : ℝ, 0 < CE ∧ 0 < CF ∧
    ∀ ρ : ℝ, 0 < ρ → ∃ β₀ : ℝ, 2 ≤ β₀ ∧ ρ ≤ β₀ ∧
    ∀ (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁], 3 ∣ N₁ → 5 < N₁ →
    ∀ ν : ℝ, 0 < ν → ν * 3 ^ (2 * (k + 1)) ≤ 1 →
    ∀ β : ℝ, β₀ ≤ β → ∀ (p₁ : ℝ), 0 < p₁ →
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
              (Metric.ball (0 : ℂ) (3 / 2)))) := by
  classical
  obtain ⟨CE, CF, hCE, hCF, H⟩ := commonWitness_joint_fromTowerG_rho T.toG hA p
  refine ⟨CE, CF, hCE, hCF, fun ρ hρ => ?_⟩
  obtain ⟨β₀, h2, hρβ, H1⟩ := H ρ hρ
  refine ⟨β₀, h2, hρβ, ?_⟩
  intro k hk N₁ _ h3N hN ν hνpos hν β hβ p₁ hp0 hp₁ D S hS hp
  subst hS
  have e : (((3 : ℕ) : ℝ)) ^ (k * (3 - 2)) = 3 ^ k := by norm_num
  have hp' : 0 < (T.toG.step k hk N₁ ν β p₁).p₁ := hp
  have G := H1 k hk N₁ (by simpa using h3N) hN ν hνpos (by simpa using hν) β hβ p₁ hp0
    (by rw [e]; exact hp₁) (StepTower.scaleDataG_of_fixed T D) (T.toG.step k hk N₁ ν β p₁) rfl hp'
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
/-- **One witness for the source lane at the shared tower `T`, sources of `ℓ¹`-size `< ρ`.**
After `T` choose `C_E, C_F`; for every `ρ > 0` a threshold `β₀ ≥ max 2 ρ`; the statement is that of
`sourceWitness_fromTower` on the carriers of radius `ρ`, with `ε_U` taken on the slice `η = ρ/β` and
the bound `4 ε_U ≤ C_E (log b)^(3p)/√b + ρ C_F (log b)^p/√b`.  Original description:  After `T` choose one threshold
`β₀` and one pair `C_E, C_F`.  For every scale and `D : StepScaleData T …` with `β ≥ β₀`,
`0 < p₁ ≤ A₁ (log β_k)^p`, there is ONE `val, 𝒴, Tt` (from a single call of
`sourceDirectTerms_scale_fromTower`), with its value formula, and `ε_U > 0` the physical amplitude
with `4 ε_U ≤ C_E (log b)^(3p)/√b + C_F (log b)^p/√b`, such that (a) every source `g` of the `l¹`
ball has the records `BR`, `BC` of `sourceActivityC_scale_fromTower` on the labels of `𝒴` with
`BR.ε_H = 4 ε_U`; (b) the exponent family of `sourceExponentFamily_fromTower` on the labels of `𝒴`
with amplitude `4 ε_U`; (c) the observable ray activities of `obsRayActivity_fromTower` on the
thick labels of `𝒴` and the terms `Tt`, with amplitude `ε_U`. -/
theorem sourceWitness_fromTower_rho {κmin : ℝ} (T : StepTower κmin) {A₁ : ℝ}
    (hA : 0 < A₁) (p : ℕ) :
    ∃ CE CF : ℝ, 0 < CE ∧ 0 < CF ∧
    ∀ ρ : ℝ, 0 < ρ → ∃ β₀ : ℝ, 2 ≤ β₀ ∧ ρ ≤ β₀ ∧
    ∀ (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁], 3 ∣ N₁ → 5 < N₁ →
    ∀ ν : ℝ, 0 < ν → ν * 3 ^ (2 * (k + 1)) ≤ 1 →
    ∀ β : ℝ, β₀ ≤ β → ∀ (p₁ : ℝ), 0 < p₁ →
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
              S.WtwoC (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) g t x) := by
  obtain ⟨CE, CF, hCE, hCF, H⟩ := commonWitness_joint_fromTower_rho T hA p
  refine ⟨CE, CF, hCE, hCF, fun ρ hρ => ?_⟩
  obtain ⟨β₀, h2, hρβ, H1⟩ := H ρ hρ
  refine ⟨β₀, h2, hρβ, ?_⟩
  intro k hk N₁ _ h3N hN ν hνpos hν β hβ p₁ hp0 hp₁ D S hS hp
  obtain ⟨val, 𝒴, Tt, hdom, hval, εU, hεU, hεpos, hbd, h4, h5, h6, -, -⟩ :=
    H1 k hk N₁ h3N hN ν hνpos hν β hβ p₁ hp0 hp₁ D S hS hp
  exact ⟨val, 𝒴, Tt, hdom, hval, εU, hεU, hεpos, hbd, h4, h5, h6⟩

open Classical in
/-- **One witness for the source lane at the shared tower `T`** (the radius `ρ = 1` case of
`sourceWitness_fromTower_rho`).  After `T` choose one threshold
`β₀` and one pair `C_E, C_F`.  For every scale and `D : StepScaleData T …` with `β ≥ β₀`,
`0 < p₁ ≤ A₁ (log β_k)^p`, there is ONE `val, 𝒴, Tt` (from a single call of
`sourceDirectTerms_scale_fromTower`), with its value formula, and `ε_U > 0` the physical amplitude
with `4 ε_U ≤ C_E (log b)^(3p)/√b + C_F (log b)^p/√b`, such that (a) every source `g` of the `l¹`
ball has the records `BR`, `BC` of `sourceActivityC_scale_fromTower` on the labels of `𝒴` with
`BR.ε_H = 4 ε_U`; (b) the exponent family of `sourceExponentFamily_fromTower` on the labels of `𝒴`
with amplitude `4 ε_U`; (c) the observable ray activities of `obsRayActivity_fromTower` on the
thick labels of `𝒴` and the terms `Tt`, with amplitude `ε_U`. -/
theorem sourceWitness_fromTower {κmin : ℝ} (T : StepTower κmin) {A₁ : ℝ}
    (hA : 0 < A₁) (p : ℕ) :
    ∃ β₀ CE CF : ℝ, 2 ≤ β₀ ∧ 0 < CE ∧ 0 < CF ∧
    ∀ (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁], 3 ∣ N₁ → 5 < N₁ →
    ∀ ν : ℝ, 0 < ν → ν * 3 ^ (2 * (k + 1)) ≤ 1 →
    ∀ β : ℝ, β₀ ≤ β → ∀ (p₁ : ℝ), 0 < p₁ →
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
              S.WtwoC (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) g t x) := by
  obtain ⟨CE, CF, hCE, hCF, H⟩ := sourceWitness_fromTower_rho T hA p
  obtain ⟨β₀, h2, -, H1⟩ := H 1 one_pos
  refine ⟨β₀, CE, CF, h2, hCE, hCF, ?_⟩
  intro k hk N₁ _ h3N hN ν hνpos hν β hβ p₁ hp0 hp₁ D S hS hp
  obtain ⟨val, 𝒴, Tt, hdom, hval, εU, hεU, hεpos, hbd, rest⟩ :=
    H1 k hk N₁ h3N hN ν hνpos hν β hβ p₁ hp0 hp₁ D S hS hp
  rw [one_mul] at hbd
  exact ⟨val, 𝒴, Tt, hdom, hval, εU, hεU, hεpos, hbd, rest⟩

open Classical in
/-- **Drift check (activity).**  `sourceActivityC_scale_fromTower` follows from
`sourceWitness_fromTower`: the bound on `BR.εH` is `BR.εH = 4 ε_U ≤ …`. -/
theorem sourceActivityC_scale_fromTower_of_witness {κmin : ℝ} (T : StepTower κmin) {A₁ : ℝ}
    (hA : 0 < A₁) (p : ℕ) :
    ∃ β₀ CE CF : ℝ, 2 ≤ β₀ ∧ 0 < CE ∧ 0 < CF ∧
    ∀ (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁], 3 ∣ N₁ → 5 < N₁ →
    ∀ ν : ℝ, 0 < ν → ν * 3 ^ (2 * (k + 1)) ≤ 1 →
    ∀ β : ℝ, β₀ ≤ β → ∀ (p₁ : ℝ) (hp : 0 < p₁),
    p₁ ≤ pLog A₁ p (β * 3 ^ k) → StepScaleData T k hk N₁ ν β p₁ →
    ∃ 𝒴 : Finset (Set (CTorus 3 3 N₁ T.m₁ (k + 1))),
    ∃ hdom : ∀ Y ∈ 𝒴, IsDj 1 (k + 1) Y,
    ∀ g : Fld 3 3 N₁ T.m₁ (k + 1) 2, g ∈ l1Ball 3 3 N₁ T.m₁ (k + 1) 2 →
    ∃ BR : StepActivityBound (T.step k hk N₁ ν β p₁)
        (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) g,
    ∃ BC : StepActivityBoundC (T.step k hk N₁ ν β p₁)
        (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) g,
      BR.m₀ = 1 ∧ BC.m₀ = 1 ∧ BR.Lb = ({Y // Y ∈ 𝒴} ⊕ {Y // Y ∈ 𝒴}) ∧ BC.Lb = BR.Lb ∧
      HEq BR.Lab ((thickLabels 𝒴 hdom).sum (thickLabels 𝒴 hdom)) ∧ HEq BC.Lab BR.Lab ∧
      HEq BR.BS ((T.step k hk N₁ ν β p₁).blockSplit 1 hp) ∧ HEq BC.BS BR.BS ∧
      BR.κ0 = T.κ0 ∧ BC.κ0 = T.κ0 ∧ BR.κ' = T.κ' ∧ BC.κ' = T.κ' ∧
      BR.κH = 2 * T.κdec - 1 ∧ BC.κH = BR.κH ∧
      BR.Kc = 2 * (K0 3 3 T.κ0 + 1) ∧ BC.Kc = BR.Kc ∧ BR.εH = BC.εH ∧
      BR.εH ≤ CE * (Real.log (β * 3 ^ k)) ^ (3 * p) / Real.sqrt (β * 3 ^ k) +
        CF * (Real.log (β * 3 ^ k)) ^ p / Real.sqrt (β * 3 ^ k) := by
  obtain ⟨β₀, CE, CF, h2, hCE, hCF, H⟩ := sourceWitness_fromTower T hA p
  refine ⟨β₀, CE, CF, h2, hCE, hCF, ?_⟩
  intro k hk N₁ _ h3N hN ν hνpos hν β hβ p₁ hp hp₁ D
  obtain ⟨val, 𝒴, Tt, hdom, -, εU, -, -, hb, ha, -, -⟩ :=
    H k hk N₁ h3N hN ν hνpos hν β hβ p₁ hp hp₁ D _ rfl hp
  refine ⟨𝒴, hdom, fun g hg => ?_⟩
  obtain ⟨BR, BC, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, hε⟩ :=
    ha g hg
  exact ⟨BR, BC, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17,
    by rw [hε]; exact hb⟩

open Classical in
/-- **Drift check (activity) at radius `ρ`.**  `sourceActivityC_scale_fromTower_rho` follows from
`sourceWitness_fromTower_rho`: the bound on `BR.εH` is `BR.εH = 4 ε_U ≤ …`. -/
theorem sourceActivityC_scale_fromTower_of_witness_rho {κmin : ℝ} (T : StepTower κmin) {A₁ : ℝ}
    (hA : 0 < A₁) (p : ℕ) :
    ∃ CE CF : ℝ, 0 < CE ∧ 0 < CF ∧
    ∀ ρ : ℝ, 0 < ρ → ∃ β₀ : ℝ, 2 ≤ β₀ ∧ ρ ≤ β₀ ∧
    ∀ (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁], 3 ∣ N₁ → 5 < N₁ →
    ∀ ν : ℝ, 0 < ν → ν * 3 ^ (2 * (k + 1)) ≤ 1 →
    ∀ β : ℝ, β₀ ≤ β → ∀ (p₁ : ℝ) (hp : 0 < p₁),
    p₁ ≤ pLog A₁ p (β * 3 ^ k) → StepScaleData T k hk N₁ ν β p₁ →
    ∃ 𝒴 : Finset (Set (CTorus 3 3 N₁ T.m₁ (k + 1))),
    ∃ hdom : ∀ Y ∈ 𝒴, IsDj 1 (k + 1) Y,
    ∀ g : Fld 3 3 N₁ T.m₁ (k + 1) 2, g ∈ l1BallRho 3 3 N₁ T.m₁ (k + 1) 2 ρ →
    ∃ BR : StepActivityBound (T.step k hk N₁ ν β p₁)
        (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) g,
    ∃ BC : StepActivityBoundC (T.step k hk N₁ ν β p₁)
        (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) g,
      BR.m₀ = 1 ∧ BC.m₀ = 1 ∧ BR.Lb = ({Y // Y ∈ 𝒴} ⊕ {Y // Y ∈ 𝒴}) ∧ BC.Lb = BR.Lb ∧
      HEq BR.Lab ((thickLabels 𝒴 hdom).sum (thickLabels 𝒴 hdom)) ∧ HEq BC.Lab BR.Lab ∧
      HEq BR.BS ((T.step k hk N₁ ν β p₁).blockSplit 1 hp) ∧ HEq BC.BS BR.BS ∧
      BR.κ0 = T.κ0 ∧ BC.κ0 = T.κ0 ∧ BR.κ' = T.κ' ∧ BC.κ' = T.κ' ∧
      BR.κH = 2 * T.κdec - 1 ∧ BC.κH = BR.κH ∧
      BR.Kc = 2 * (K0 3 3 T.κ0 + 1) ∧ BC.Kc = BR.Kc ∧ BR.εH = BC.εH ∧
      BR.εH ≤ CE * (Real.log (β * 3 ^ k)) ^ (3 * p) / Real.sqrt (β * 3 ^ k) +
        ρ * CF * (Real.log (β * 3 ^ k)) ^ p / Real.sqrt (β * 3 ^ k) := by
  obtain ⟨CE, CF, hCE, hCF, H0⟩ := sourceWitness_fromTower_rho T hA p
  refine ⟨CE, CF, hCE, hCF, fun ρ hρ => ?_⟩
  obtain ⟨β₀, h2, hρβ, H⟩ := H0 ρ hρ
  refine ⟨β₀, h2, hρβ, ?_⟩
  intro k hk N₁ _ h3N hN ν hνpos hν β hβ p₁ hp hp₁ D
  obtain ⟨val, 𝒴, Tt, hdom, -, εU, -, -, hb, ha, -, -⟩ :=
    H k hk N₁ h3N hN ν hνpos hν β hβ p₁ hp hp₁ D _ rfl hp
  refine ⟨𝒴, hdom, fun g hg => ?_⟩
  obtain ⟨BR, BC, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, hε⟩ :=
    ha g hg
  exact ⟨BR, BC, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17,
    by rw [hε]; exact hb⟩

open Classical in
/-- **The observable ray activities of the witness at source radius `ρ`.**  As
`obsRayActivity_fromTower_of_witness`, with the amplitude slice `ρ / β` and the sources in the ball
of radius `ρ`; the threshold satisfies `2 ≤ β₀` and `ρ ≤ β₀` and is chosen after `ρ`.  From
`sourceWitness_fromTower_rho`. -/
theorem obsRayActivity_fromTower_of_witness_rho {κmin : ℝ} (T : StepTower κmin) {A₁ : ℝ}
    (hA : 0 < A₁) (p : ℕ) (ρ : ℝ) (hρ : 0 < ρ) :
    ∃ β₀ : ℝ, 2 ≤ β₀ ∧ ρ ≤ β₀ ∧
    ∀ (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁], 3 ∣ N₁ → 5 < N₁ →
    ∀ ν : ℝ, 0 < ν → ν * 3 ^ (2 * (k + 1)) ≤ 1 →
    ∀ β : ℝ, β₀ ≤ β → ∀ (p₁ : ℝ), 0 < p₁ → p₁ ≤ pLog A₁ p (β * 3 ^ k) →
    StepScaleData T k hk N₁ ν β p₁ → ∀ (hp : 0 < p₁),
    ∃ (val : (((T.step k hk N₁ ν β p₁).U × Fin 2 → ℂ) × ((T.step k hk N₁ ν β p₁).U × Fin 2 → ℂ)) →
        (((T.step k hk N₁ ν β p₁).U × Fin 2 → ℂ) × ((T.step k hk N₁ ν β p₁).U × Fin 2 → ℂ)) →
        ℂ → (RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2 ×
          (CTorus 3 3 N₁ T.m₁ (k + 1) → Fin 2 → ℂ)) → ℂ)
      (𝒴 : Finset (Set (CTorus 3 3 N₁ T.m₁ (k + 1))))
      (Tt : Set (CTorus 3 3 N₁ T.m₁ (k + 1)) →
        (((T.step k hk N₁ ν β p₁).U × Fin 2 → ℂ) × ((T.step k hk N₁ ν β p₁).U × Fin 2 → ℂ)) →
        (((T.step k hk N₁ ν β p₁).U × Fin 2 → ℂ) × ((T.step k hk N₁ ν β p₁).U × Fin 2 → ℂ)) →
        ℂ → (RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2 ×
          (CTorus 3 3 N₁ T.m₁ (k + 1) → Fin 2 → ℂ)) → ℂ)
      (hdom : ∀ Y ∈ 𝒴, IsDj 1 (k + 1) Y),
      (∀ x w σ Θ, val x w σ Θ =
        (-((T.step k hk N₁ ν β p₁).β : ℂ)) * raySrc3 (hatFun (T.step k hk N₁ ν β p₁).G' (T.step k hk N₁ ν β p₁).a₁ (T.step k hk N₁ ν β p₁).ν T.t (T.step k hk N₁ ν β p₁).hG'
          (((T.step k hk N₁ ν β p₁).betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)
          (interactionOne (T.step k hk N₁ ν β p₁).hG (T.step k hk N₁ ν β p₁).hG' (le_refl (k + 1)) (T.step k hk N₁ ν β p₁).a₁ (T.step k hk N₁ ν β p₁).ν T.t)) taylorWeight
          x.1 w.1 σ Θ.1 +
        ((T.step k hk N₁ ν β p₁).β : ℂ) * (∑ s : CTorus 3 3 N₁ T.m₁ (k + 1) × Fin 2, Θ.2 s.1 s.2 *
          dirTermSrc (hatFun (T.step k hk N₁ ν β p₁).G' (T.step k hk N₁ ν β p₁).a₁ (T.step k hk N₁ ν β p₁).ν T.t (T.step k hk N₁ ν β p₁).hG'
            (((T.step k hk N₁ ν β p₁).betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)
            (onXi (T.step k hk N₁ ν β p₁).G' (T.step k hk N₁ ν β p₁).a₁ (T.step k hk N₁ ν β p₁).ν T.t
              (fun D ψ' => svec (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁))
                (flFieldOne (T.step k hk N₁ ν β p₁).G' (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) T.BG₂ T.κ (T.step k hk N₁ ν β p₁).a₁ (T.step k hk N₁ ν β p₁).ν D ψ')
                  s.1 s.2)))
            (fun _ => (1 : ℂ)) x.2 w.2 σ Θ.1)) ∧
      0 < β * prop33EpsEtaScaled 3 3 2 T.m₁ k 1 1 T.BG T.BG₂ T.κ T.t
        (lvR T.κ T.t (β * 3 ^ k) p₁) 0 0 (ρ / β) ∧
      ∃ A₀ : ℂ → LabelAct (thickLabels 𝒴 hdom) ((T.step k hk N₁ ν β p₁).blockSplit 1 hp).Ωb
          (β * prop33EpsEtaScaled 3 3 2 T.m₁ k 1 1 T.BG T.BG₂ T.κ T.t
            (lvR T.κ T.t (β * 3 ^ k) p₁) 0 0 (ρ / β)) (2 * T.κdec - 1) T.κ0 (K0 3 3 T.κ0 + 1),
        (∀ z : ℂ, ‖z‖ < 3 / 2 → ∀ y Φ, (A₀ z).H y Φ =
          Tt y.1 (z • (T.step k hk N₁ ν β p₁).hatOf 1 p₁ hp Φ, z • (T.step k hk N₁ ν β p₁).hatOf 1 p₁ hp Φ)
            (z • (T.step k hk N₁ ν β p₁).hatOf 1 p₁ hp Φ, z • (T.step k hk N₁ ν β p₁).hatOf 1 p₁ hp Φ) 1
            (rawOf (T.step k hk N₁ ν β p₁).D', (0 : CTorus 3 3 N₁ T.m₁ (k + 1) → Fin 2 → ℂ))) ∧
        (∀ z : ℂ, 3 / 2 ≤ ‖z‖ → ∀ y Φ, (A₀ z).H y Φ = 0) ∧
        ∀ g : Fld 3 3 N₁ T.m₁ (k + 1) 2, g ∈ l1BallRho 3 3 N₁ T.m₁ (k + 1) 2 ρ →
        ∃ Ag : ℂ → LabelAct (thickLabels 𝒴 hdom) ((T.step k hk N₁ ν β p₁).blockSplit 1 hp).Ωb
            (β * prop33EpsEtaScaled 3 3 2 T.m₁ k 1 1 T.BG T.BG₂ T.κ T.t
              (lvR T.κ T.t (β * 3 ^ k) p₁) 0 0 (ρ / β)) (2 * T.κdec - 1) T.κ0
            (K0 3 3 T.κ0 + 1),
          (∀ z : ℂ, ‖z‖ < 3 / 2 → ∀ y Φ, (Ag z).H y Φ =
            Tt y.1 (z • (T.step k hk N₁ ν β p₁).hatOf 1 p₁ hp Φ, z • (T.step k hk N₁ ν β p₁).hatOf 1 p₁ hp Φ)
              (z • (T.step k hk N₁ ν β p₁).hatOf 1 p₁ hp Φ, z • (T.step k hk N₁ ν β p₁).hatOf 1 p₁ hp Φ) 1
              (rawOf (T.step k hk N₁ ν β p₁).D', fun y i => g y i / ((T.step k hk N₁ ν β p₁).β : ℂ))) ∧
          (∀ z : ℂ, 3 / 2 ≤ ‖z‖ → ∀ y Φ, (Ag z).H y Φ = 0) ∧
          ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 → ∀ᵐ x ∂(T.step k hk N₁ ν β p₁).nuFl,
            ∑ y, (((A₀ 1).sub (A₀ (t : ℂ))).sum (Ag (t : ℂ))).H y
                (((T.step k hk N₁ ν β p₁).blockSplit 1 hp).restr x) =
              (T.step k hk N₁ ν β p₁).WoneC (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) 1 x +
              (T.step k hk N₁ ν β p₁).WtwoC (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) g t x := by
  obtain ⟨_CE, _CF, _hCE, _hCF, H0⟩ := sourceWitness_fromTower_rho T hA p
  obtain ⟨β₀, h2, hρβ, H⟩ := H0 ρ hρ
  refine ⟨β₀, h2, hρβ, ?_⟩
  intro k hk N₁ _ h3N hN ν hνpos hν β hβ p₁ hp0 hp₁ D hp
  obtain ⟨val, 𝒴, Tt, hdom, hval, εU, hεU, hεpos, -, -, -, hc⟩ :=
    H k hk N₁ h3N hN ν hνpos hν β hβ p₁ hp0 hp₁ D _ rfl hp
  subst hεU
  exact ⟨val, 𝒴, Tt, hdom, hval, hc.1, hc.2⟩

open Classical in
/-- **Drift check (observable rays).**  `obsRayActivity_fromTower` follows from
`sourceWitness_fromTower` for `β ≥ β₀` and `p₁ ≤ A₁ (log β_k)^p` (the landed statement has only
`1 ≤ β`; the witness theorem has the threshold of the amplitude bound). -/
theorem obsRayActivity_fromTower_of_witness {κmin : ℝ} (T : StepTower κmin) {A₁ : ℝ}
    (hA : 0 < A₁) (p : ℕ) :
    ∃ β₀ : ℝ, ∀ (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁], 3 ∣ N₁ → 5 < N₁ →
    ∀ ν : ℝ, 0 < ν → ν * 3 ^ (2 * (k + 1)) ≤ 1 →
    ∀ β : ℝ, β₀ ≤ β → ∀ (p₁ : ℝ), 0 < p₁ → p₁ ≤ pLog A₁ p (β * 3 ^ k) →
    StepScaleData T k hk N₁ ν β p₁ → ∀ (hp : 0 < p₁),
    ∃ (val : (((T.step k hk N₁ ν β p₁).U × Fin 2 → ℂ) × ((T.step k hk N₁ ν β p₁).U × Fin 2 → ℂ)) →
        (((T.step k hk N₁ ν β p₁).U × Fin 2 → ℂ) × ((T.step k hk N₁ ν β p₁).U × Fin 2 → ℂ)) →
        ℂ → (RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2 ×
          (CTorus 3 3 N₁ T.m₁ (k + 1) → Fin 2 → ℂ)) → ℂ)
      (𝒴 : Finset (Set (CTorus 3 3 N₁ T.m₁ (k + 1))))
      (Tt : Set (CTorus 3 3 N₁ T.m₁ (k + 1)) →
        (((T.step k hk N₁ ν β p₁).U × Fin 2 → ℂ) × ((T.step k hk N₁ ν β p₁).U × Fin 2 → ℂ)) →
        (((T.step k hk N₁ ν β p₁).U × Fin 2 → ℂ) × ((T.step k hk N₁ ν β p₁).U × Fin 2 → ℂ)) →
        ℂ → (RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2 ×
          (CTorus 3 3 N₁ T.m₁ (k + 1) → Fin 2 → ℂ)) → ℂ)
      (hdom : ∀ Y ∈ 𝒴, IsDj 1 (k + 1) Y),
      (∀ x w σ Θ, val x w σ Θ =
        (-((T.step k hk N₁ ν β p₁).β : ℂ)) * raySrc3 (hatFun (T.step k hk N₁ ν β p₁).G' (T.step k hk N₁ ν β p₁).a₁ (T.step k hk N₁ ν β p₁).ν T.t (T.step k hk N₁ ν β p₁).hG'
          (((T.step k hk N₁ ν β p₁).betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)
          (interactionOne (T.step k hk N₁ ν β p₁).hG (T.step k hk N₁ ν β p₁).hG' (le_refl (k + 1)) (T.step k hk N₁ ν β p₁).a₁ (T.step k hk N₁ ν β p₁).ν T.t)) taylorWeight
          x.1 w.1 σ Θ.1 +
        ((T.step k hk N₁ ν β p₁).β : ℂ) * (∑ s : CTorus 3 3 N₁ T.m₁ (k + 1) × Fin 2, Θ.2 s.1 s.2 *
          dirTermSrc (hatFun (T.step k hk N₁ ν β p₁).G' (T.step k hk N₁ ν β p₁).a₁ (T.step k hk N₁ ν β p₁).ν T.t (T.step k hk N₁ ν β p₁).hG'
            (((T.step k hk N₁ ν β p₁).betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)
            (onXi (T.step k hk N₁ ν β p₁).G' (T.step k hk N₁ ν β p₁).a₁ (T.step k hk N₁ ν β p₁).ν T.t
              (fun D ψ' => svec (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁))
                (flFieldOne (T.step k hk N₁ ν β p₁).G' (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) T.BG₂ T.κ (T.step k hk N₁ ν β p₁).a₁ (T.step k hk N₁ ν β p₁).ν D ψ')
                  s.1 s.2)))
            (fun _ => (1 : ℂ)) x.2 w.2 σ Θ.1)) ∧
      0 < β * prop33EpsEtaScaled 3 3 2 T.m₁ k 1 1 T.BG T.BG₂ T.κ T.t
        (lvR T.κ T.t (β * 3 ^ k) p₁) 0 0 (1 / β) ∧
      ∃ A₀ : ℂ → LabelAct (thickLabels 𝒴 hdom) ((T.step k hk N₁ ν β p₁).blockSplit 1 hp).Ωb
          (β * prop33EpsEtaScaled 3 3 2 T.m₁ k 1 1 T.BG T.BG₂ T.κ T.t
            (lvR T.κ T.t (β * 3 ^ k) p₁) 0 0 (1 / β)) (2 * T.κdec - 1) T.κ0 (K0 3 3 T.κ0 + 1),
        (∀ z : ℂ, ‖z‖ < 3 / 2 → ∀ y Φ, (A₀ z).H y Φ =
          Tt y.1 (z • (T.step k hk N₁ ν β p₁).hatOf 1 p₁ hp Φ, z • (T.step k hk N₁ ν β p₁).hatOf 1 p₁ hp Φ)
            (z • (T.step k hk N₁ ν β p₁).hatOf 1 p₁ hp Φ, z • (T.step k hk N₁ ν β p₁).hatOf 1 p₁ hp Φ) 1
            (rawOf (T.step k hk N₁ ν β p₁).D', (0 : CTorus 3 3 N₁ T.m₁ (k + 1) → Fin 2 → ℂ))) ∧
        (∀ z : ℂ, 3 / 2 ≤ ‖z‖ → ∀ y Φ, (A₀ z).H y Φ = 0) ∧
        ∀ g : Fld 3 3 N₁ T.m₁ (k + 1) 2, g ∈ l1Ball 3 3 N₁ T.m₁ (k + 1) 2 →
        ∃ Ag : ℂ → LabelAct (thickLabels 𝒴 hdom) ((T.step k hk N₁ ν β p₁).blockSplit 1 hp).Ωb
            (β * prop33EpsEtaScaled 3 3 2 T.m₁ k 1 1 T.BG T.BG₂ T.κ T.t
              (lvR T.κ T.t (β * 3 ^ k) p₁) 0 0 (1 / β)) (2 * T.κdec - 1) T.κ0
            (K0 3 3 T.κ0 + 1),
          (∀ z : ℂ, ‖z‖ < 3 / 2 → ∀ y Φ, (Ag z).H y Φ =
            Tt y.1 (z • (T.step k hk N₁ ν β p₁).hatOf 1 p₁ hp Φ, z • (T.step k hk N₁ ν β p₁).hatOf 1 p₁ hp Φ)
              (z • (T.step k hk N₁ ν β p₁).hatOf 1 p₁ hp Φ, z • (T.step k hk N₁ ν β p₁).hatOf 1 p₁ hp Φ) 1
              (rawOf (T.step k hk N₁ ν β p₁).D', fun y i => g y i / ((T.step k hk N₁ ν β p₁).β : ℂ))) ∧
          (∀ z : ℂ, 3 / 2 ≤ ‖z‖ → ∀ y Φ, (Ag z).H y Φ = 0) ∧
          ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 → ∀ᵐ x ∂(T.step k hk N₁ ν β p₁).nuFl,
            ∑ y, (((A₀ 1).sub (A₀ (t : ℂ))).sum (Ag (t : ℂ))).H y
                (((T.step k hk N₁ ν β p₁).blockSplit 1 hp).restr x) =
              (T.step k hk N₁ ν β p₁).WoneC (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) 1 x +
              (T.step k hk N₁ ν β p₁).WtwoC (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) g t x := by
  obtain ⟨β₀, -, -, H⟩ := obsRayActivity_fromTower_of_witness_rho T hA p 1 one_pos
  exact ⟨β₀, H⟩

end Balaban.Inhabited
