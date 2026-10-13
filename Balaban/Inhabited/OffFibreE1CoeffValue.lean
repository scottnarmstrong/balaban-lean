/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.OffFibreE1Activity

/-!
# The E1 coefficient value at a free datum

The direct-term activity and the marked coefficient theorem give the raw localized
first-energy value for every datum of the complex chart.
-/

@[expose] public section
namespace Balaban.Inhabited

open Balaban Balaban.Fluctuation Balaban.Multiscale Balaban.Background Balaban.Localization
  Balaban.Localization.LevelPair Balaban.Localization.I5Inhabited Balaban.Polymer
  Balaban.SmallField Balaban.SmallField.Def6 Balaban.Inhabited.LevelStep Matrix Metric Set
  MeasureTheory Balaban.Inhabited.MarkBudgetAudit

open Classical in
/-- The actual E1 parameter coefficients have the raw localized derivative value at a free datum. -/
theorem e1_param_coeff_sum_eq_raw_deriv_of_directTerms {κmin : ℝ} (T : StepTower κmin)
    {k : ℕ} {hk : 1 ≤ k} {N₁ : ℕ} [NeZero N₁] {ν β p₁ : ℝ}
    (Dt : StepScaleData T k hk N₁ ν β p₁)
    (hνpos : 0 < ν) (hν : ν * 3 ^ (2 * (k + 1)) ≤ 1)
    (S : StepSetting 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁))
    (hS : S = T.step k hk N₁ ν β p₁) (Jr : S.JointRep T.t (2 * p₁))
    (hp : 0 < S.p₁) (hp0 : 0 < p₁) (hlt : S.p₁ < 2 * p₁) (hβpos : 0 < β)
    {BG κdec : ℝ}
    (F₁ : Torus 3 (N₁ * 3 ^ T.m₁ * 3 ^ (k + 1 - (k + 1))) →
      DecParams S.G' × RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2 →
        (S.G'.Ω 1 × Fin 2 → ℂ) × (S.G'.Ω 1 → ℂ))
    (Sol : Torus 3 (N₁ * 3 ^ T.m₁ * 3 ^ (k + 1 - (k + 1))) →
      Dec2.DecParams (coverOf S.G') × Edat (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) 2 →
        ((stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)).Ω 1 × Fin 2 → ℂ) ×
          ((stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)).Ω 1 → ℂ))
    (z : RootIdx 3 3 N₁ T.m₁ (k + 1))
    (hP : ∀ b, MarkedBlockExpansionDecPair 2
      (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) S.hG'
      ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) S.a₁ S.ν BG T.BG₂ T.κ T.t T.t κdec p₁
      (S.blockU z) (LocalCover.nbhdF 1 (LocalCover.blockSite k b)) 1 k
      (LocalCover.fam 1 (LocalCover.blockSite k b)) b (F₁ b) (Sol b))
    (D : BgData S.G' 2) (hX : XiCData S.G' S.a S.ν (k + 1) 1 T.t D)
    (hN3 : 3 ^ 1 ∣ N₁) (hdj : ∀ b, ∀ Y ∈ e1Dom S b, IsDj 1 (k + 1) Y)
    {Lb : Type} [Fintype Lb]
    (Lab₀ : CubeLabels (d := 3) (L := 3) (N₁ := N₁) (m₁ := T.m₁)
      (K := k + 1) 1 (k + 1) Set.univ Lb)
    {εH : ℝ}
    (A₀ : physParam 2 S → ℂ →
      LabelAct (commonLabels Lab₀ hN3 (by norm_num) (fun _ => Set.univ) (e1Dom S) hdj)
        (S.blockSplit 1 hp).Ωb εH (2 * T.κdec - 1) T.κ0 T.marksKc')
    (θ : physParam 2 S)
    (hθ : θ = ((⟨rawOf D, rawOf_mem_rawSub _⟩ : rawSub 2 S.G'),
      (0 : CTorus 3 3 N₁ T.m₁ (k + 1) → Fin 2 → ℂ)))
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
    (I : DirectTerms S 1 hp (fun ψ => (ψ, ψ)) p₁ 2
      (S.β * prop33EpsEtaScaled 3 3 2 T.m₁ k 1 S.a₁ T.BG T.BG₂ T.κ T.t
        (lvR T.κ T.t (β * 3 ^ k) p₁) 0 0 (1 / S.β)) (2 * T.κdec - 1)
      (rawOf S.D', (0 : CTorus 3 3 N₁ T.m₁ (k + 1) → Fin 2 → ℂ))
      (physSΛEta S S.a₁ S.ν T.t (1 / S.β))
      (physXW S (lvCpsi T.κ T.t (β * 3 ^ k)) 2 2
        (lvR T.κ T.t (β * 3 ^ k) p₁)) val (physAgΘ S) (AgFDirPair S))
    (hF : DirectTermsFamilyOn S 1 (physInclScaled 2 S (((1 / S.β : ℝ)) : ℂ)) I
      (physVq S S.a₁ S.ν T.t 1))
    (hεU : 0 ≤ S.β * prop33EpsEtaScaled 3 3 2 T.m₁ k 1 S.a₁ T.BG T.BG₂ T.κ T.t
      (lvR T.κ T.t (β * 3 ^ k) p₁) 0 0 (1 / S.β))
    (A : physParam 2 S → ℂ → LabelAct (thickLabels I.𝒴 I.dom) (S.blockSplit 1 hp).Ωb
      (2 * (S.β * prop33EpsEtaScaled 3 3 2 T.m₁ k 1 S.a₁ T.BG T.BG₂ T.κ T.t
        (lvR T.κ T.t (β * 3 ^ k) p₁) 0 0 (1 / S.β)))
      (2 * T.κdec - 1) T.κ0 (2 * (K0 3 3 T.κ0 + 1)))
    (hAeq : A = labelActFamilyOn S 1 (physInclScaled 2 S (((1 / S.β : ℝ)) : ℂ)) I hF
      hN3 hp0 (by norm_num) hεU T.κ0_ent
      T.marks_K0_le)
    (hA₀sum : ∀ (e : physParam 2 S) (u : ℂ)
      (Φ : ∀ b, (S.blockSplit 1 hp).Ωb b),
      ∑ y, (A₀ e u).H y Φ =
        sqFactor 2 u * ∑ y, (A ((e.1, 0) : physParam 2 S) u).H y Φ)
    (hεpos : 0 < εH)
    (hε : εH ≤ stepTheta 3 3 T.marksKc' (2 * T.κdec - 1) T.κ0 T.κ')
    (hAhol : ∀ y Φ, DifferentiableOn ℂ (fun u => (A₀ θ u).H y Φ)
      (Metric.ball (0 : ℂ) corrU))
    (hmeas : ∀ (i : {Y' // Y' ∈ bridgeFamily 1 (fun _ => Set.univ) (e1Dom S) z})
      (u : ℂ), Measurable (e1MarkGParam S F₁ Sol p₁ hp z T.t θ i u))
    (hdep : ∀ (i : {Y' // Y' ∈ bridgeFamily 1 (fun _ => Set.univ) (e1Dom S) z})
      (u : ℂ), DepOn (blocksOf 1 (k + 1) Set.univ
        ((commonLabels Lab₀ hN3 (by norm_num) (fun _ => Set.univ) (e1Dom S) hdj).ysite
          (commonAnchor Lb (fun _ => Set.univ) (e1Dom S) z i)))
        (e1MarkGParam S F₁ Sol p₁ hp z T.t θ i u))
    (hbnd : ∀ (i : {Y' // Y' ∈ bridgeFamily 1 (fun _ => Set.univ) (e1Dom S) z})
      (u : ℂ) Φ, ‖e1MarkGParam S F₁ Sol p₁ hp z T.t θ i u Φ‖ ≤
        corrF0 T k β p₁ * Real.exp (-(2 * T.κdec - 1) *
          (commonLabels Lab₀ hN3 (by norm_num) (fun _ => Set.univ) (e1Dom S) hdj).dl
            (commonAnchor Lb (fun _ => Set.univ) (e1Dom S) z i)))
    (hGhol : ∀ (i : {Y' // Y' ∈ bridgeFamily 1 (fun _ => Set.univ) (e1Dom S) z}) Φ,
      DifferentiableOn ℂ (fun u => e1MarkGParam S F₁ Sol p₁ hp z T.t θ i u Φ)
        (Metric.ball (0 : ℂ) corrU)) :
    (∑ C, gsumCoeff (S.blockSplit 1 hp).μ
      (commonLabels Lab₀ hN3 (by norm_num) (fun _ => Set.univ) (e1Dom S) hdj)
      (A₀ θ)
      (fun i : {Y' // Y' ∈ bridgeFamily 1 (fun _ => Set.univ) (e1Dom S) z} =>
        commonAnchor Lb (fun _ => Set.univ) (e1Dom S) z i)
      (fun i u Φ => e1MarkGParam S F₁ Sol p₁ hp z T.t θ i u Φ) C) =
    ∫ s in (0 : ℝ)..1, avgFun S.nuFl
      (fun s x => Jr.W1 (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁))
        (rawOf D, (s : ℂ) • yhat x))
      (fun x => (fderiv ℂ (fun w : S.EC =>
        Jr.W1 (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) (rawOf D, w))
        ((s : ℂ) • yhat x))
        ((Jr.Mx (rawOf D))⁻¹ *ᵥ S.maskUC z (Jr.Mx (rawOf D) *ᵥ yhat x))) s := by
  subst hθ
  have hact := e1_common_activity_freeDatum_of_directTerms T k hk N₁
    (by simpa using hN3 : 3 ∣ N₁) ν hνpos hν β p₁ hp0 Dt S hS hp Jr
    val hval I hF hεU A hAeq A₀ hA₀sum D hX
  exact e1_param_coeff_sum_eq_raw_deriv_of_activity T Dt S hS Jr hp hlt hβpos
    F₁ Sol z hP D hX hN3 hdj Lab₀ A₀ _ rfl hact hεpos hε hAhol
    hmeas hdep hbnd hGhol

end Balaban.Inhabited
