/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.OffFibreM0Ray
public import Balaban.Inhabited.ObsCoeffFibreValue

/-!
# The observable coefficient sum at a free datum

The observable marks from one family `Ev` are assembled with an activity whose exponent is
the raw `W1 + W2`. The resulting coefficient sum has the raw `M0J` value.
-/

@[expose] public section

namespace Balaban.Fluctuation.StepSetting.JointRep

open Balaban Balaban.Background Balaban.Multiscale Balaban.Localization
  Balaban.SmallField Balaban.SmallField.Def6 MeasureTheory Metric Set

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ eps pp : ℝ}
  {S : StepSetting d L N₁ m₁ k N ϱ} (Jr : S.JointRep eps pp)
  (H : StepSettingH S)
  {c BG κ Kc Cx c₂ BG₂ δ₁ δc : ℝ}

open Classical in
/-- A free-datum activity identity for the observable labels gives a record whose
coefficient sum is the raw marked observable average. -/
theorem obsRecord_raw_M0_of_activity
    (hC : FlCore N S.G' (stepG d L N₁ m₁ k ϱ) S.a₁ S.ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
    (ha₁ : 0 < S.a₁) (HB : BgHyp d L (k + 1) ϱ (compWeight L S.a₁) S.ν)
    (hc7 : c7 d L N BG κ ≤ thm73C3 d L N) {R : ℝ} (hR : 2 ≤ R)
    (hsmR : 2 * (compC4 d * (bgK1 d L N * (xiC1 d * eps))) +
      5 * (R * δ₁) ≤ bgC1 d L N)
    (hRs : R * δ₁ ≤ deltaStar d L N)
    (hsmall : cK2 d L N * (R * δ₁) < bgC0 d L N / 2)
    (hnum : cK2 d L N * δ₁ ≤ c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8))
    (hnum' : cK2' d L N (famConst d L BG₂ κ) * δ₁ ≤
      c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8))
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    (hdm : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    {cψ : ℝ} (hcψ : 0 ≤ cψ)
    (hδ₁ : Real.sqrt N * (‖((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)‖ *
      (covSupConstC d L N (compWeight L S.a₁ k) κ * cψ)) < δ₁)
    (hpc : pp < cψ) (hX : XiCData S.G' S.a S.ν (k + 1) 1 eps H.D')
    (hp : 0 < S.p₁) (hlt : S.p₁ < pp) {m₀ : ℕ}
    (hN : L ^ m₀ ∣ N₁)
    {Lb₀ : Type} [Fintype Lb₀]
    (Lab₀ : CubeLabels (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) m₀
      (k + 1) Set.univ Lb₀)
    (𝒴 : Finset (Set (CTorus d L N₁ m₁ (k + 1))))
    (hdj : ∀ Y ∈ 𝒴, IsDj m₀ (k + 1) Y)
    (Ev : Set (CTorus d L N₁ m₁ (k + 1)) →
      RawData d L (N₁ * L ^ m₁) (k + 1) N × (S.U × Fin N → ℂ) → ℂ)
    (g : Fld d L N₁ m₁ (k + 1) N)
    (y : CTorus d L N₁ m₁ (k + 1)) (i : Fin N)
    (bx : CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) m₀
      (k + 1) Set.univ)
    {C0 Ch κh κ0 κH : ℝ} (hCh : 0 ≤ Ch) (hκ0 : aEnt d L + 1 ≤ κ0)
    (hκ0h : κ0 ≤ κh)
    (hhalf : ObsMarkHalf S m₀ hp Ev H.D' 𝒴 (obsLab Lab₀ hdj)
      cψ C0 κH κ0 Ch κh bx)
    (hid : ObsRayIdentity S m₀ hp
      (fun ψh => svec (stepG d L N₁ m₁ k ϱ)
        (flFieldOne S.G' (stepG d L N₁ m₁ k ϱ) BG₂ κ S.a₁ S.ν H.D'
          (hatLift S.G' S.a₁ S.ν S.hG'
            ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) H.D' ψh)) y i)
      Ev H.D' 𝒴)
    {εH κ' Kc' Rσ : ℝ}
    (𝒰 : Set ℂ) (hRσ : 1 < Rσ) (hOpen : IsOpen 𝒰)
    (hseg : ∀ s : ℝ, s ∈ Icc (0 : ℝ) 1 → (s : ℂ) ∈ 𝒰)
    (h𝒰 : 𝒰 ⊆ ball (0 : ℂ) (3 / 2))
    (A : ℂ → ℂ → LabelAct (obsLab Lab₀ hdj) (S.blockSplit m₀ hp).Ωb εH κH κ0 Kc')
    (holt : ∀ z Φ, DifferentiableOn ℂ (fun t => (A t 1).H z Φ) 𝒰)
    (holσ : ∀ s : ℝ, s ∈ Icc (0 : ℝ) 1 → ∀ z Φ,
      DifferentiableOn ℂ (fun σ => (A (s : ℂ) σ).H z Φ) (ball (0 : ℂ) Rσ))
    (zero : ∀ s : ℝ, s ∈ Icc (0 : ℝ) 1 → ∀ z Φ, (A (s : ℂ) 0).H z Φ = 0)
    (hact : ∀ s : ℝ, s ∈ Icc (0 : ℝ) 1 → ∀ᵐ x ∂S.nuFl,
      Jr.W1 (zeroClass d L N₁ m₁ k N ϱ) (rawOf H.D', yhat x) +
        Jr.W2 (zeroClass d L N₁ m₁ k N ϱ) g
          (rawOf H.D', (s : ℂ) • yhat x) =
        ∑ z, (A (s : ℂ) 1).H z ((S.blockSplit m₀ hp).restr x))
    (hKc : K0 d L κ0 + 1 ≤ Kc') (hεpos : 0 < εH) (hκ'0 : 0 ≤ κ')
    (hκ0' : κ0 ≤ κ') (hκH' : κ' + 3 * κ0 + c1 d L + 3 / 2 ≤ κH)
    (hε : εH ≤ 1 / (8 * Kc' ^ 3 * c1 d L *
      Real.exp ((κH - 2 * κ0) * cG d L + c1 d L + κ' * cG d L))) :
    ∃ I : ObsMarks S.nuFl (S.blockSplit m₀ hp)
      (fun t x => Jr.W1 (zeroClass d L N₁ m₁ k N ϱ) (rawOf H.D', yhat x) +
        Jr.W2 (zeroClass d L N₁ m₁ k N ϱ) g
          (rawOf H.D', (t : ℂ) • yhat x))
      (fun t x => obsRayFun S (fun ψh => svec (stepG d L N₁ m₁ k ϱ)
        (flFieldOne S.G' (stepG d L N₁ m₁ k ϱ) BG₂ κ S.a₁ S.ν H.D'
          (hatLift S.G' S.a₁ S.ν S.hG'
            ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) H.D' ψh)) y i) x t) bx,
      (∀ T, obsCoeff I T =
        kernelMarkSum (fun (j : ObsMarkIdx S) T' =>
          obsHker 𝒴 (obsRowCoeff S Ev H.D' j) m₀ T')
          (fun j S' => markIntTerm (S.blockSplit m₀ hp).μ A
            (obsY1 m₀ S Lb₀ 𝒴 j) (blockMark S m₀ hp j.1 j.2) S') T +
        gsumCoeff (S.blockSplit m₀ hp).μ (obsLab Lab₀ hdj) (fun t => A t 1)
          (obsRemLab 𝒴 (fun Y => Sum.inl (Sum.inr Y))
            (obsY0 m₀ Lb₀ 𝒴 bx)) (obsGr S m₀ hp Ev H.D' 𝒴) T) ∧
      ((S.betaU ^ (1 / 2 : ℝ) : ℝ) : ℂ) * ∑ T, obsCoeff I T =
        ((S.betaU ^ (1 / 2 : ℝ) : ℝ) : ℂ) *
          S.avgJ (Jr.W1 (zeroClass d L N₁ m₁ k N ϱ))
            (Jr.W2 (zeroClass d L N₁ m₁ k N ϱ) g)
            (Jr.McJ (zeroClass d L N₁ m₁ k N ϱ) g y i) (rawOf H.D') := by
  obtain ⟨I, hI⟩ := obsRecord_of_halves S m₀ hp Lab₀ 𝒴 hdj hN Ev H.D'
    (fun ψh => svec (stepG d L N₁ m₁ k ϱ)
      (flFieldOne S.G' (stepG d L N₁ m₁ k ϱ) BG₂ κ S.a₁ S.ν H.D'
        (hatLift S.G' S.a₁ S.ν S.hG'
          ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) H.D' ψh)) y i)
    bx hCh hκ0 hκ0h hhalf hid
    (fun t x => Jr.W1 (zeroClass d L N₁ m₁ k N ϱ) (rawOf H.D', yhat x) +
      Jr.W2 (zeroClass d L N₁ m₁ k N ϱ) g (rawOf H.D', (t : ℂ) • yhat x))
    𝒰 hRσ hOpen hseg h𝒰 A holt holσ zero hact hKc hεpos hκ'0 hκ0' hκH' hε
  exact ⟨I, hI, Jr.obsCoeff_sum_eq_raw_M0J_zeroClass H hC ha₁ HB hc7 hR hsmR hRs
    hsmall hnum hnum' hMX hdm hα hsm hcψ hδ₁ hpc hX hp hlt g y i (S.blockSplit m₀ hp) I⟩

end Balaban.Fluctuation.StepSetting.JointRep
