/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.PhysAmpFacts
public import Balaban.Inhabited.ActivityOfWitness
public import Balaban.Inhabited.ZeroSourceActivityCommon
public import Balaban.Inhabited.SourceWitnessJoint
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# One source witness for the source lane, the analytic family, the zero-source family and the
# ray premise of the observable lane

`commonWitness_joint_fromTower` returns, at every admissible scale of one tower, one
`val, 𝒴, Tt` (slice `η = 1/β`, `q = 1`) carrying

* the conclusion of `sourceWitness_analytic_fromTower`;
* the premise of `obsMarks_zeroClass_family_of_ray` (`hray`) at that scale: the formula for `val`
  (already in the first item), diagonal continuity, an instance at every point of the slice, the two
  source points in the slice, and the ray clause, all for these `val, 𝒴, Tt`;
* the conclusion of `zeroSourceActivity_common_of_witness` for a `DirectTerms` record `I` with
  `I.𝒴 = 𝒴`, `I.T = Tt` and its relative family.
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation
  Balaban.Localization Balaban.Localization.LevelPair Balaban.Localization.I5Inhabited
  Balaban.Polymer Balaban.SmallField.Def6 Balaban.Inhabited.LevelStep Filter Topology
  MeasureTheory Set Metric

open Classical in
/-- **The analytic family and the zero-source family on the common labels for a given source
witness, at source radius `ρ`, general tower.**  The statement of
`commonWitness_extra_of_witness_rho` at `T : StepTowerG d L N κmin`, the step `T.step` (given up to
the identification `ϱ = rhoSepG d L T.m₁` of the separation), the scale `b = β L^{k (d-2)}` and any
constants record `C` with the rates and label constants of `T`; the threshold on `β` is `3 ≤ β`
and that every `ε` below the amplitude bound lies below `C.theta` and below `stepTheta` at the
enlarged entropy constant (`StepTowerG.exists_beta0_marks`).  The fixed theorem is its corollary. -/
theorem commonWitness_extra_of_witnessG_rho {d L N : ℕ} [NeZero L] {κmin : ℝ}
    (T : StepTowerG d L N κmin) (C : StepOutputConsts d L) (p : ℕ) {CE CF : ℝ} (hCF : 0 < CF)
    (ρ : ℝ) (hρ : 0 < ρ)
    (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁] (hLN : L ^ T.m₀ ∣ N₁)
    (ν : ℝ) (hνpos : 0 < ν) (hν : ν * (L : ℝ) ^ (2 * (k + 1)) ≤ 1) (β : ℝ) (hβ3 : 3 ≤ β)
    (hβρ : max 1 ρ ≤ β) (b : ℝ) (hb : b = β * (L : ℝ) ^ (k * (d - 2)))
    (hβ : ∀ ε : ℝ, ε ≤ 2 * CE * (Real.log b) ^ (3 * p) / Real.sqrt b +
        2 * (ρ * CF) * (Real.log b) ^ p / Real.sqrt b →
      ε ≤ C.theta ∧
      ε ≤ stepTheta d L (2 * (K0 d L T.κ0 + 1) + rootUnionK d L T.m₀ T.m₁ T.κ0)
        (2 * T.κdec - 1) T.κ0 T.κ')
    (p₁ : ℝ) (hp0 : 0 < p₁) (D : StepScaleDataG T k hk N₁ ν β p₁) {ϱ : ℝ}
    (hϱ : ϱ = rhoSepG d L T.m₁)
    (S : StepSetting d L N₁ T.m₁ k N ϱ) (hS : HEq S (T.step k hk N₁ ν β p₁))
    (hp : 0 < S.p₁)
    (val : ((S.U × Fin N → ℂ) × (S.U × Fin N → ℂ)) → ((S.U × Fin N → ℂ) × (S.U × Fin N → ℂ)) →
            ℂ → (RawData d L (N₁ * L ^ T.m₁) (k + 1) N × (CTorus d L N₁ T.m₁ (k + 1) → Fin N → ℂ)) → ℂ)
    (𝒴 : Finset (Set (CTorus d L N₁ T.m₁ (k + 1))))
    (Tt : Set (CTorus d L N₁ T.m₁ (k + 1)) → ((S.U × Fin N → ℂ) × (S.U × Fin N → ℂ)) →
            ((S.U × Fin N → ℂ) × (S.U × Fin N → ℂ)) → ℂ →
            (RawData d L (N₁ * L ^ T.m₁) (k + 1) N × (CTorus d L N₁ T.m₁ (k + 1) → Fin N → ℂ)) → ℂ)
    (hval : ∀ x w σ Θ, val x w σ Θ =
            (-(S.β : ℂ)) * raySrc3 (hatFun S.G' S.a₁ S.ν T.t S.hG'
              ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)
              (interactionOne S.hG S.hG' (le_refl (k + 1)) S.a₁ S.ν T.t)) taylorWeight x.1 w.1 σ
                Θ.1 +
            (S.β : ℂ) * (∑ s : CTorus d L N₁ T.m₁ (k + 1) × Fin N, Θ.2 s.1 s.2 *
              dirTermSrc (hatFun S.G' S.a₁ S.ν T.t S.hG' ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)
                (onXi S.G' S.a₁ S.ν T.t
                  (fun D ψ' => svec (stepG d L N₁ T.m₁ k ϱ)
                    (flFieldOne S.G' (stepG d L N₁ T.m₁ k ϱ) T.BG₂ T.κ S.a₁ S.ν D ψ')
                      s.1 s.2)))
                (fun _ => (1 : ℂ)) x.2 w.2 σ Θ.1))
    (hcont : DiagCont (fun ψ : S.U × Fin N → ℂ => (ψ, ψ))
            (physXW S (lvCpsiG d L N T.κ T.t b) 2 2 (lvRG d L N T.κ T.t b p₁))
            (physSΛEta S S.a₁ S.ν T.t (ρ / S.β)) 2 𝒴 Tt)
    (hI : ∀ Θ ∈ physSΛEta S S.a₁ S.ν T.t (ρ / S.β),
            ∃ I' : DirectTerms S T.m₀ hp (fun ψ => (ψ, ψ)) p₁ 2
                (S.β * prop33EpsEtaScaled d L N T.m₁ k T.m₀ S.a₁ T.BG T.BG₂ T.κ T.t
                  (lvRG d L N T.κ T.t b p₁) 0 0 (ρ / S.β)) (2 * T.κdec - 1) Θ
                (physSΛEta S S.a₁ S.ν T.t (ρ / S.β))
                (physXW S (lvCpsiG d L N T.κ T.t b) 2 2 (lvRG d L N T.κ T.t b p₁)) val
                (physAgΘ S) (AgFDirPair S),
              I'.𝒴 = 𝒴 ∧ I'.T = Tt)
    (hmem0 : (rawOf S.D', (0 : CTorus d L N₁ T.m₁ (k + 1) → Fin N → ℂ)) ∈
      physSΛEta S S.a₁ S.ν T.t (ρ / S.β))
    (hbound : 4 * (S.β * prop33EpsEtaScaled d L N T.m₁ k T.m₀ S.a₁ T.BG T.BG₂ T.κ T.t
            (lvRG d L N T.κ T.t b p₁) 0 0 (ρ / S.β)) ≤
        CE * (Real.log b) ^ (3 * p) / Real.sqrt b +
          ρ * CF * (Real.log b) ^ p / Real.sqrt b) :

  (      (∃ (Jr : S.JointRep T.t (2 * p₁))
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
                      ((S.blockSplit T.m₀ hp).restr x)))) ∧
  ((∃ (Jr : S.JointRep T.t (2 * p₁))
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
                  (S.WoneC (zeroClass d L N₁ T.m₁ k N ϱ)) (fun _ _ => (0 : ℂ)))))))
  := by
  classical
  have hfam := activityFamilyAnalytic_of_witnessG_rho T k hk N₁ hLN ν hνpos hν β ρ hβρ p₁ hp0 ρ
    hρ le_rfl b hb D hϱ S hS hp val 𝒴 Tt hval hcont hI hmem0
  refine ⟨hfam, ?_⟩
  obtain ⟨Jr, I, h𝒴I, hTI, hF, hεU', hεpos', hA'⟩ := hfam
  obtain ⟨A, hAeq, han, hcA, -, -, hW1, hW2, hS1, -, -, -, -, -⟩ := hA' T.marks_K0_le
  refine ⟨Jr, I, h𝒴I, hTI, hF, hεU', hεpos', ?_⟩
  exact T.zeroSourceActivity_common_of_witness_rho C p hCF ρ hρ k hk N₁ hLN ν hνpos hν β hβ3 b hb
    hβ p₁ hp0 ρ hρ le_rfl D hϱ S hS hp val I hF hεU' hεpos' hbound Jr
    ⟨A, hAeq, han, hcA, hW1, hW2, hS1⟩


/-- **The analytic family and the zero-source family on the common labels for a given source
witness, at source radius `ρ`** (slice `η = ρ/β`, `q = ρ`, `max 1 ρ ≤ β`): the conclusion of
`activityFamilyAnalytic_of_witness_rho` at `q = ρ`, and the conclusion of
`zeroSourceActivity_common_of_witness_rho` for the `DirectTerms` record it produces.  The
carriers are `physVqRho … ρ ρ`, `physFibreRho … ρ`, `physVRho … ρ`; the threshold of `β` is that
of `exists_beta0_marks` for `2 C_E` and `2 ρ C_F`. -/
theorem commonWitness_extra_of_witness_rho {κmin : ℝ} (T : StepTower κmin)
    (hHull : stepHullMin ≤ κmin) (p : ℕ) {CE CF : ℝ} (hCE : 0 < CE) (hCF : 0 < CF)
    (ρ : ℝ) (hρ : 0 < ρ)
    (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁] (h3N : 3 ∣ N₁)
    (ν : ℝ) (hνpos : 0 < ν) (hν : ν * 3 ^ (2 * (k + 1)) ≤ 1) (β : ℝ) (hβρ : max 1 ρ ≤ β)
    (hβm : (exists_beta0_marks T hHull p (CE := 2 * CE) (CF := 2 * (ρ * CF))
      (mul_nonneg zero_le_two hCE.le)
      (mul_nonneg zero_le_two (mul_nonneg hρ.le hCF.le))).choose ≤ β)
    (p₁ : ℝ) (hp0 : 0 < p₁) (D : StepScaleData T k hk N₁ ν β p₁)
    (S : StepSetting 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) (hS : S = T.step k hk N₁ ν β p₁)
    (hp : 0 < S.p₁)
    (val : ((S.U × Fin 2 → ℂ) × (S.U × Fin 2 → ℂ)) → ((S.U × Fin 2 → ℂ) × (S.U × Fin 2 → ℂ)) →
            ℂ → (RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2 × (CTorus 3 3 N₁ T.m₁ (k + 1) → Fin 2 → ℂ)) → ℂ)
    (𝒴 : Finset (Set (CTorus 3 3 N₁ T.m₁ (k + 1))))
    (Tt : Set (CTorus 3 3 N₁ T.m₁ (k + 1)) → ((S.U × Fin 2 → ℂ) × (S.U × Fin 2 → ℂ)) →
            ((S.U × Fin 2 → ℂ) × (S.U × Fin 2 → ℂ)) → ℂ →
            (RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2 × (CTorus 3 3 N₁ T.m₁ (k + 1) → Fin 2 → ℂ)) → ℂ)
    (hval : ∀ x w σ Θ, val x w σ Θ =
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
    (hcont : DiagCont (fun ψ : S.U × Fin 2 → ℂ => (ψ, ψ))
            (physXW S (lvCpsi T.κ T.t (β * 3 ^ k)) 2 2 (lvR T.κ T.t (β * 3 ^ k) p₁))
            (physSΛEta S S.a₁ S.ν T.t (ρ / S.β)) 2 𝒴 Tt)
    (hI : ∀ Θ ∈ physSΛEta S S.a₁ S.ν T.t (ρ / S.β),
            ∃ I' : DirectTerms S 1 hp (fun ψ => (ψ, ψ)) p₁ 2
                (S.β * prop33EpsEtaScaled 3 3 2 T.m₁ k 1 S.a₁ T.BG T.BG₂ T.κ T.t
                  (lvR T.κ T.t (β * 3 ^ k) p₁) 0 0 (ρ / S.β)) (2 * T.κdec - 1) Θ
                (physSΛEta S S.a₁ S.ν T.t (ρ / S.β))
                (physXW S (lvCpsi T.κ T.t (β * 3 ^ k)) 2 2 (lvR T.κ T.t (β * 3 ^ k) p₁)) val
                (physAgΘ S) (AgFDirPair S),
              I'.𝒴 = 𝒴 ∧ I'.T = Tt)
    (hmem0 : (rawOf S.D', (0 : CTorus 3 3 N₁ T.m₁ (k + 1) → Fin 2 → ℂ)) ∈
      physSΛEta S S.a₁ S.ν T.t (ρ / S.β))
    (hbound : 4 * (S.β * prop33EpsEtaScaled 3 3 2 T.m₁ k 1 S.a₁ T.BG T.BG₂ T.κ T.t
            (lvR T.κ T.t (β * 3 ^ k) p₁) 0 0 (ρ / S.β)) ≤
        CE * (Real.log (β * 3 ^ k)) ^ (3 * p) / Real.sqrt (β * 3 ^ k) +
          ρ * CF * (Real.log (β * 3 ^ k)) ^ p / Real.sqrt (β * 3 ^ k)) :

  (      (∃ (Jr : S.JointRep T.t (2 * p₁))
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
                      ((S.blockSplit 1 hp).restr x)))) ∧
  ((∃ (Jr : S.JointRep T.t (2 * p₁))
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
                  (S.WoneC (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁))) (fun _ _ => (0 : ℂ))))))) := by
  obtain ⟨hm3, hm⟩ := (exists_beta0_marks T hHull p (CE := 2 * CE) (CF := 2 * (ρ * CF))
    (mul_nonneg zero_le_two hCE.le)
    (mul_nonneg zero_le_two (mul_nonneg hρ.le hCF.le))).choose_spec
  exact commonWitness_extra_of_witnessG_rho T.toG (stepOutputPhysical T hHull) p hCF ρ hρ k hk N₁
    (by simpa using h3N) ν hνpos (by simpa using hν) β (hm3.trans hβm) hβρ (β * 3 ^ k)
    (by norm_num) (fun ε hε => hm β k hβm ε hε) p₁ hp0 (StepTower.scaleDataG_of_fixed T D)
    (rhoSepG_three _).symm S
    (by rw [hS]; exact (StepTower.toG_step_heq T k hk N₁ ν β p₁).symm) hp val 𝒴 Tt hval hcont hI
    hmem0 hbound


/-- **Helper for `commonWitness_joint_fromTower`: the analytic family and the zero-source family on
the common labels for a given source witness** (slice `η = 1/β`, `q = 1`): the conclusion of
`activityFamilyAnalytic_of_witness` at `q = 1`, and the conclusion of
`zeroSourceActivity_common_of_witness` for the `DirectTerms` record it produces. -/
theorem commonWitness_extra_of_witness {κmin : ℝ} (T : StepTower κmin)
    (hHull : stepHullMin ≤ κmin) (p : ℕ) {CE CF : ℝ} (hCE : 0 < CE) (hCF : 0 < CF)
    (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁] (h3N : 3 ∣ N₁)
    (ν : ℝ) (hνpos : 0 < ν) (hν : ν * 3 ^ (2 * (k + 1)) ≤ 1) (β : ℝ) (hβ1 : 1 ≤ β)
    (hβm : (exists_beta0_marks T hHull p (CE := 2 * CE) (CF := 2 * CF)
      (mul_nonneg zero_le_two hCE.le) (mul_nonneg zero_le_two hCF.le)).choose ≤ β)
    (p₁ : ℝ) (hp0 : 0 < p₁) (D : StepScaleData T k hk N₁ ν β p₁)
    (S : StepSetting 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) (hS : S = T.step k hk N₁ ν β p₁)
    (hp : 0 < S.p₁)
    (val : ((S.U × Fin 2 → ℂ) × (S.U × Fin 2 → ℂ)) → ((S.U × Fin 2 → ℂ) × (S.U × Fin 2 → ℂ)) →
            ℂ → (RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2 × (CTorus 3 3 N₁ T.m₁ (k + 1) → Fin 2 → ℂ)) → ℂ)
    (𝒴 : Finset (Set (CTorus 3 3 N₁ T.m₁ (k + 1))))
    (Tt : Set (CTorus 3 3 N₁ T.m₁ (k + 1)) → ((S.U × Fin 2 → ℂ) × (S.U × Fin 2 → ℂ)) →
            ((S.U × Fin 2 → ℂ) × (S.U × Fin 2 → ℂ)) → ℂ →
            (RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2 × (CTorus 3 3 N₁ T.m₁ (k + 1) → Fin 2 → ℂ)) → ℂ)
    (hval : ∀ x w σ Θ, val x w σ Θ =
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
    (hcont : DiagCont (fun ψ : S.U × Fin 2 → ℂ => (ψ, ψ))
            (physXW S (lvCpsi T.κ T.t (β * 3 ^ k)) 2 2 (lvR T.κ T.t (β * 3 ^ k) p₁))
            (physSΛEta S S.a₁ S.ν T.t (1 / S.β)) 2 𝒴 Tt)
    (hI : ∀ Θ ∈ physSΛEta S S.a₁ S.ν T.t (1 / S.β),
            ∃ I' : DirectTerms S 1 hp (fun ψ => (ψ, ψ)) p₁ 2
                (S.β * prop33EpsEtaScaled 3 3 2 T.m₁ k 1 S.a₁ T.BG T.BG₂ T.κ T.t
                  (lvR T.κ T.t (β * 3 ^ k) p₁) 0 0 (1 / S.β)) (2 * T.κdec - 1) Θ
                (physSΛEta S S.a₁ S.ν T.t (1 / S.β))
                (physXW S (lvCpsi T.κ T.t (β * 3 ^ k)) 2 2 (lvR T.κ T.t (β * 3 ^ k) p₁)) val
                (physAgΘ S) (AgFDirPair S),
              I'.𝒴 = 𝒴 ∧ I'.T = Tt)
    (hmem0 : (rawOf S.D', (0 : CTorus 3 3 N₁ T.m₁ (k + 1) → Fin 2 → ℂ)) ∈
      physSΛEta S S.a₁ S.ν T.t (1 / S.β))
    (hbound : 4 * (S.β * prop33EpsEtaScaled 3 3 2 T.m₁ k 1 S.a₁ T.BG T.BG₂ T.κ T.t
            (lvR T.κ T.t (β * 3 ^ k) p₁) 0 0 (1 / S.β)) ≤
        CE * (Real.log (β * 3 ^ k)) ^ (3 * p) / Real.sqrt (β * 3 ^ k) +
          CF * (Real.log (β * 3 ^ k)) ^ p / Real.sqrt (β * 3 ^ k)) :

  (      (∃ (Jr : S.JointRep T.t (2 * p₁))
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
                      ((S.blockSplit 1 hp).restr x)))) ∧
  ((∃ (Jr : S.JointRep T.t (2 * p₁))
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
                  (S.WoneC (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁))) (fun _ _ => (0 : ℂ))))))) := by
  have hρ : (0 : ℝ) < 1 := one_pos
  have hβm' : (exists_beta0_marks T hHull p (CE := 2 * CE) (CF := 2 * (1 * CF))
      (mul_nonneg zero_le_two hCE.le)
      (mul_nonneg zero_le_two (mul_nonneg hρ.le hCF.le))).choose ≤ β := by
    simpa only [one_mul] using hβm
  obtain ⟨hact, Jr, I, h1, h2, hF, hεU, hpos, hz⟩ := commonWitness_extra_of_witness_rho T hHull p
    hCE hCF 1 hρ k hk N₁ h3N ν hνpos hν β (by simpa using hβ1) hβm' p₁ hp0 D S hS hp val 𝒴 Tt hval
    hcont hI hmem0 (by simpa only [one_mul] using hbound)
  refine ⟨hact, Jr, I, h1, h2, hF, hεU, hpos, hz.1, ?_, hz.2.2⟩
  simpa only [one_mul] using hz.2.1

open Classical in
/-- **The amplitude of the source direct terms at the slice `η = 1/β`, general tower.**  The statement
of `commonWitness_amplitude_fromTower` at `T : StepTowerG d L N κmin` (block scale `T.m₀`, scale
`β L^{k (d-2)}`); the fixed theorem is its corollary.  Original description of the fixed theorem:    For the tower `T` there are
`β₀, C_E, C_F` such that at every admissible scale the amplitude `ε_U = β · ε^{η}` of the slice
`η = 1/β` is positive, satisfies `4 ε_U ≤ C_E (log b)^{3p}/√b + C_F (log b)^p/√b`
(`b = β 3^k`), and `2 (2 ε_U)` is at most the amplitude threshold of the activity records at the
entropy constant `2 (K₀ + 1)`.  These are the numerical inputs of `sourceWitness_analytic_fromTower`,
without the direct terms. -/
theorem commonWitness_amplitude_fromTowerG {d L N : ℕ} [NeZero L] {κmin : ℝ} (T : StepTowerG d L N κmin) {A₁ : ℝ}
    (hA : 0 < A₁) (p : ℕ) :
    ∃ β₀ CE CF : ℝ, 2 ≤ β₀ ∧ 0 < CE ∧ 0 < CF ∧
    ∀ (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁] (ν : ℝ), 0 < ν → ν * (L : ℝ) ^ (2 * (k + 1)) ≤ 1 →
    ∀ β : ℝ, β₀ ≤ β → ∀ p₁ : ℝ, 0 < p₁ →
    p₁ ≤ pLog A₁ p (β * (L : ℝ) ^ (k * (d - 2))) → StepScaleDataG T k hk N₁ ν β p₁ →
    0 < β * prop33EpsEtaScaled d L N T.m₁ k T.m₀ 1 T.BG T.BG₂ T.κ T.t
        (lvRG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2))) p₁) 0 0 (1 / β) ∧
    4 * (β * prop33EpsEtaScaled d L N T.m₁ k T.m₀ 1 T.BG T.BG₂ T.κ T.t
        (lvRG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2))) p₁) 0 0 (1 / β)) ≤
      CE * (Real.log (β * (L : ℝ) ^ (k * (d - 2)))) ^ (3 * p) / Real.sqrt (β * (L : ℝ) ^ (k * (d - 2))) +
        CF * (Real.log (β * (L : ℝ) ^ (k * (d - 2)))) ^ p / Real.sqrt (β * (L : ℝ) ^ (k * (d - 2))) ∧
    2 * (2 * (β * prop33EpsEtaScaled d L N T.m₁ k T.m₀ 1 T.BG T.BG₂ T.κ T.t
        (lvRG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2))) p₁) 0 0 (1 / β))) ≤
      1 / (8 * (2 * (K0 d L T.κ0 + 1)) ^ 3 * c1 d L *
        Real.exp ((2 * T.κdec - 1 - 2 * T.κ0) * cG d L + c1 d L + T.κ' * cG d L))   := by
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
  obtain ⟨CE, hCE⟩ : ∃ x : ℝ, x = 4 * (P * (4 * A₁ / lvKappaG d L N T.κ T.t) ^ 3 + 1) := ⟨_, rfl⟩
  obtain ⟨CF, hCF⟩ : ∃ x : ℝ, x = 16 * A₁ * (Q * T.t) / lvKappaG d L N T.κ T.t := ⟨_, rfl⟩
  have hCE0 : 0 < CE := by rw [hCE]; positivity
  have hCF0 : 0 < CF := by rw [hCF]; positivity
  refine ⟨max (max 2 β₁) (daThreshold ((CE + CF) / 4)
      (daT d L 4 (2 * Kc'') T.κdec T.κ0 T.κ') (3 * p)),
    CE, CF, le_trans (le_max_left _ _) (le_max_left _ _), hCE0, hCF0, ?_⟩
  intro k hk N₁ _ ν hνpos hν β hβ p₁ hp0 hp₁ D
  have hν0 : 0 ≤ ν := hνpos.le
  have hβ₁ : β₁ ≤ β := le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hβ)
  have hβd : daThreshold ((CE + CF) / 4)
      (daT d L 4 (2 * Kc'') T.κdec T.κ0 T.κ') (3 * p) ≤ β := le_trans (le_max_right _ _) hβ
  have hβ2 : 2 ≤ β := le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hβ)
  have hβ0 : 0 < β := by linarith
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast (by omega : 1 ≤ L)
  have h3k : (1 : ℝ) ≤ (L : ℝ) ^ (k * (d - 2)) := one_le_pow₀ hL1
  have hbβ : β ≤ β * (L : ℝ) ^ (k * (d - 2)) := le_mul_of_one_le_right hβ0.le h3k
  have hb0 : 0 < β * (L : ℝ) ^ (k * (d - 2)) := by positivity
  have hexp : Real.exp 1 ≤ β * (L : ℝ) ^ (k * (d - 2)) := le_trans hexpβ₁ (hβ₁.trans hbβ)
  have hℓ : 1 ≤ Real.log (β * (L : ℝ) ^ (k * (d - 2))) := (Real.le_log_iff_exp_le hb0).2 hexp
  have hamp := (hA' (β * (L : ℝ) ^ (k * (d - 2))) (hβ₁.trans hbβ) p₁ hp0 hp₁).2 P (Q * T.t) 1 hP0
    hK0.le one_pos.le
  have hr0 := D.r_pos
  obtain ⟨εU, hεU⟩ : ∃ εU : ℝ, εU = β * prop33EpsEtaScaled d L N T.m₁ k T.m₀ 1 T.BG T.BG₂ T.κ
      T.t (lvRG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2))) p₁) 0 0 (1 / β) := ⟨_, rfl⟩
  have hbU : (T.step k hk N₁ ν β p₁).betaU = β * (L : ℝ) ^ (k * (d - 2)) :=
    hatStepKG_betaU (d := d) (L := L) (N₁ := N₁) hN (by omega) k T.m₁ (rhoSepG d L T.m₁) hk ν β
      p₁ T.δ
  obtain ⟨hid, hpot, hterm0, hεle', hεpos⟩ := physAmp_facts (T.step k hk N₁ ν β p₁)
    (by omega) hL T.m₀ (compWeight_one_mem hL hk) rfl hβ0 rfl hbU hQ0 ht0 hρ4 hr0 one_pos hQdef
    hPdef hεU
  have hεle := hεle' _ hamp
  have hε4 := sourceAmp_scale_four_general (A₁ := A₁) (κ₁ := lvKappaG d L N T.κ T.t) (P := P)
    (K := Q * T.t) (q := 1) (CE := CE) (CF := CF) p hb0 (by linarith) hCE hCF hεle
  have hDA0 := sourceAmp_doubled_hDA_rho_general d L (A₁ := A₁) (κ₁ := lvKappaG d L N T.κ T.t)
    (P := P) (K := Q * T.t) (q := 1) (ρ := 1) (b := β * (L : ℝ) ^ (k * (d - 2))) (ε := εU)
    (Kc' := Kc'') (CE := CE) (CF := CF) p hA hκ1 hP0 hK0.le zero_le_one le_rfl hCE hCF hℓ hb0
    hKc''pos T.κdec T.κ0 T.κ' (by simpa only [one_mul] using hβd.trans hbβ) hεle
  subst hKc''
  rw [hεU] at hεpos hε4 hDA0
  rw [one_mul] at hε4
  exact ⟨hεpos, hε4, hDA0⟩

open Classical in
/-- **The amplitude of the source direct terms at the slice `η = 1/β`.**  For the tower `T` there are
`β₀, C_E, C_F` such that at every admissible scale the amplitude `ε_U = β · ε^{η}` of the slice
`η = 1/β` is positive, satisfies `4 ε_U ≤ C_E (log b)^{3p}/√b + C_F (log b)^p/√b`
(`b = β 3^k`), and `2 (2 ε_U)` is at most the amplitude threshold of the activity records at the
entropy constant `2 (K₀ + 1)`.  These are the numerical inputs of `sourceWitness_analytic_fromTower`,
without the direct terms. -/
theorem commonWitness_amplitude_fromTower {κmin : ℝ} (T : StepTower κmin) {A₁ : ℝ}
    (hA : 0 < A₁) (p : ℕ) :
    ∃ β₀ CE CF : ℝ, 2 ≤ β₀ ∧ 0 < CE ∧ 0 < CF ∧
    ∀ (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁] (ν : ℝ), 0 < ν → ν * 3 ^ (2 * (k + 1)) ≤ 1 →
    ∀ β : ℝ, β₀ ≤ β → ∀ p₁ : ℝ, 0 < p₁ →
    p₁ ≤ pLog A₁ p (β * 3 ^ k) → StepScaleData T k hk N₁ ν β p₁ →
    0 < β * prop33EpsEtaScaled 3 3 2 T.m₁ k 1 1 T.BG T.BG₂ T.κ T.t
        (lvR T.κ T.t (β * 3 ^ k) p₁) 0 0 (1 / β) ∧
    4 * (β * prop33EpsEtaScaled 3 3 2 T.m₁ k 1 1 T.BG T.BG₂ T.κ T.t
        (lvR T.κ T.t (β * 3 ^ k) p₁) 0 0 (1 / β)) ≤
      CE * (Real.log (β * 3 ^ k)) ^ (3 * p) / Real.sqrt (β * 3 ^ k) +
        CF * (Real.log (β * 3 ^ k)) ^ p / Real.sqrt (β * 3 ^ k) ∧
    2 * (2 * (β * prop33EpsEtaScaled 3 3 2 T.m₁ k 1 1 T.BG T.BG₂ T.κ T.t
        (lvR T.κ T.t (β * 3 ^ k) p₁) 0 0 (1 / β))) ≤
      1 / (8 * (2 * (K0 3 3 T.κ0 + 1)) ^ 3 * c1 3 3 *
        Real.exp ((2 * T.κdec - 1 - 2 * T.κ0) * cG 3 3 + c1 3 3 + T.κ' * cG 3 3)) := by
  classical
  obtain ⟨β₀, CE, CF, h2, hCE, hCF, H⟩ := commonWitness_amplitude_fromTowerG T.toG hA p
  refine ⟨β₀, CE, CF, h2, hCE, hCF, ?_⟩
  intro k hk N₁ _ ν hνpos hν β hβ p₁ hp0 hp₁ D
  have e : (((3 : ℕ) : ℝ)) ^ (k * (3 - 2)) = 3 ^ k := by norm_num
  have G := H k hk N₁ ν hνpos (by simpa using hν) β hβ p₁ hp0 (by rw [e]; exact hp₁)
    (StepTower.scaleDataG_of_fixed T D)
  rw [e] at G
  exact G

open Classical in
/-- **The full joint statement on the common source witness, sources of `ℓ¹`-size `< ρ`.**
The statement of `commonWitness_joint_fromTower` at source radius `ρ` (slice `η = ρ/β`, carriers
`l1BallRho … ρ`, `physFibreRho … ρ`, `physVqRho … ρ ρ`, `physVRho … ρ`): all clauses of
`commonWitness_joint_fromTower_rho` together with the analytic family and the zero-source family
on the common labels.  After `T` choose `C_E, C_F` independent of `ρ`; for every `ρ > 0` a threshold
`β₀` with `3 ≤ β₀`, `ρ ≤ β₀` (the threshold of `exists_beta0_marks` for `2 C_E`, `2 ρ C_F` is
included).  The original docstring follows.

**One witness for the source lane, the analytic family, the zero-source family on the common
labels and the ray premise of the observable lane.**  For the tower `T` with `stepHullMin ≤ κmin`
there are `β₀, C_E, C_F` such that at every admissible scale there are `val, 𝒴, Tt` with
(i) every clause of `sourceWitness_analytic_fromTower`; (ii) the conclusions of
`obsRay_hray_fromTower` other than the formula for `val` (which is in (i)), for these `val, 𝒴, Tt`
at this scale; (iii) a `DirectTerms` record `I` with `I.𝒴 = 𝒴`, `I.T = Tt`, a relative family over
`physVq … 1`, and the conclusions 1–8 of `zeroSourceActivity_common_fromTower` at `q = 1` for
`A = labelActFamilyOn … I hF` at the entropy constant `2 (K₀ + 1)`. -/
theorem commonWitness_joint_fromTower_rho_full {κmin : ℝ} (T : StepTower κmin)
    (hHull : stepHullMin ≤ κmin) {A₁ : ℝ}
    (hA : 0 < A₁) (p : ℕ) :
    ∃ CE CF : ℝ, 0 < CE ∧ 0 < CF ∧
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
                  (S.WoneC (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁))) (fun _ _ => (0 : ℂ)))))) := by
  classical
  obtain ⟨CE, CF, hCE, hCF, H⟩ := commonWitness_joint_fromTower_rho T hA p
  refine ⟨CE, CF, hCE, hCF, ?_⟩
  intro ρ hρ
  obtain ⟨β₁, h2, hρβ₁, H1⟩ := H ρ hρ
  have hm := exists_beta0_marks T hHull p (CE := 2 * CE) (CF := 2 * (ρ * CF))
    (mul_nonneg zero_le_two hCE.le) (mul_nonneg zero_le_two (mul_nonneg hρ.le hCF.le))
  refine ⟨max β₁ hm.choose, le_trans hm.choose_spec.1 (le_max_right _ _),
    le_trans hρβ₁ (le_max_left _ _), ?_⟩
  intro k hk N₁ _ h3N hN ν hνpos hν β hβ p₁ hp0 hp₁ D S hS hp
  have hβm : hm.choose ≤ β := le_trans (le_max_right _ _) hβ
  have hβ1' : β₁ ≤ β := le_trans (le_max_left _ _) hβ
  have hβρ : max 1 ρ ≤ β := max_le (by linarith) (hρβ₁.trans hβ1')
  obtain ⟨val, 𝒴, Tt, hdom, hval, εU, hεU, hεpos, hbd, h4, h5, h6, hray, hb⟩ :=
    H1 k hk N₁ h3N hN ν hνpos hν β hβ1' p₁ hp0 hp₁ D S hS hp
  obtain ⟨hcont, hI, hmem0, hmemg, hrayd⟩ := hb
  subst hS
  obtain ⟨hact, hzero⟩ := commonWitness_extra_of_witness_rho T hHull p hCE hCF ρ hρ k hk N₁ h3N ν
    hνpos hν β hβρ hβm p₁ hp0 D _ rfl hp val 𝒴 Tt hval hcont hI hmem0
    (by rw [hεU] at hbd; exact hbd)
  exact ⟨val, 𝒴, Tt, hdom, hval, εU, hεU, hεpos, hbd, h4, h5, h6, hact, hray,
    ⟨hcont, hI, hmem0, hmemg, hrayd⟩, hzero⟩

open Classical in
/-- **One witness for the source lane, the analytic family, the zero-source family on the common
labels and the ray premise of the observable lane.**  For the tower `T` with `stepHullMin ≤ κmin`
there are `β₀, C_E, C_F` such that at every admissible scale there are `val, 𝒴, Tt` with
(i) every clause of `sourceWitness_analytic_fromTower`; (ii) the conclusions of
`obsRay_hray_fromTower` other than the formula for `val` (which is in (i)), for these `val, 𝒴, Tt`
at this scale; (iii) a `DirectTerms` record `I` with `I.𝒴 = 𝒴`, `I.T = Tt`, a relative family over
`physVq … 1`, and the conclusions 1–8 of `zeroSourceActivity_common_fromTower` at `q = 1` for
`A = labelActFamilyOn … I hF` at the entropy constant `2 (K₀ + 1)`. -/
theorem commonWitness_joint_fromTower {κmin : ℝ} (T : StepTower κmin)
    (hHull : stepHullMin ≤ κmin) {A₁ : ℝ}
    (hA : 0 < A₁) (p : ℕ) :
    ∃ β₀ CE CF : ℝ, 3 ≤ β₀ ∧ 0 < CE ∧ 0 < CF ∧
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
                  (S.WoneC (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁))) (fun _ _ => (0 : ℂ)))))) := by
  classical
  obtain ⟨CE, CF, hCE, hCF, H⟩ := commonWitness_joint_fromTower_rho_full T hHull hA p
  obtain ⟨β₀, h3, -, H1⟩ := H 1 one_pos
  refine ⟨β₀, CE, CF, h3, hCE, hCF, ?_⟩
  intro k hk N₁ _ h3N hN ν hνpos hν β hβ p₁ hp0 hp₁ D S hS hp
  have h := H1 k hk N₁ h3N hN ν hνpos hν β hβ p₁ hp0 hp₁ D S hS hp
  simp only [one_mul] at h
  exact h

end Balaban.Inhabited
