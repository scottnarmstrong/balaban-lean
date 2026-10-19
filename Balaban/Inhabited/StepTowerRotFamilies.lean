/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.StepTowerRotOld
public import Balaban.Fluctuation.LocalClassDensityFamilyActTower
public import Balaban.Inhabited.StepTowerBeta0Labels
public import Balaban.Inhabited.E0CoeffFamilyRotBlock
public import Balaban.Inhabited.E0CoeffFamilyRotMarkG

/-!
# Spin covariance of the activities and marks built from the localized old terms

`rotFam_of_term`: a function of the parameter and of the block variables of the form
`θ, Φ ↦ [θ ∈ chart ∧ ‖u‖ < corrU] · g u (θ.raw, ψ̂(Φ))` is covariant under the real orthogonal
rotation of the parameter and of the block variables when `g` is invariant under the simultaneous
rotation of the raw datum and of the hat variable.  `rotG1_of_ev` is the case of the marks
`G₁ = β ∂_t |_{t=0} ev (u, t) (θ.raw, ψ̂)`: the invariance of `ev` for `‖t‖ < bb` gives that of the
derivative.
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Fluctuation Balaban.Multiscale Balaban.Background Balaban.Localization
  Balaban.Localization.LevelPair Balaban.Localization.I5Inhabited Balaban.Polymer
  Balaban.SmallField Balaban.SmallField.Def6 Balaban.Inhabited.LevelStep Matrix Metric Set
  MeasureTheory Balaban.Inhabited.MarkBudgetAudit Balaban.SmallField.Def6v2
  Balaban.SmallField.GsSpec Balaban.Analysis

section FamG

variable {d L N N₁ m₁ k : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}

open Classical in
/-- **Covariance of a family of the form `[θ ∈ chart ∧ ‖u‖ < corrU] g u (θ.raw, ψ̂(Φ))`.** -/
theorem rotFam_of_termG (S : StepSetting d L N₁ m₁ k N ϱ) {hp : 0 < S.p₁} {ρ eps : ℝ}
    (hρ : 0 < ρ) (hρp : S.p₁ ≤ ρ) {ι' : Type*}
    (Gf : physParam N S → ι' → ℂ → (∀ b, (S.blockSplit 1 hp).Ωb b) → ℂ)
    (g : ι' → ℂ → RawData d L (N₁ * L ^ m₁) (k + 1) N × (S.U × Fin N → ℂ) → ℂ)
    (hG : ∀ θ i u Φ, Gf θ i u Φ =
      if (θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) ∈
          XiCRaw S.G' (compWeight L S.a₁) S.ν (k + 1) 1 eps ∧ ‖u‖ < corrU then
        g i u ((θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N), S.hatOf 1 ρ hp Φ)
      else 0)
    (hg : ∀ i u, ‖u‖ < corrU → ∀ Q : Matrix (Fin N) (Fin N) ℝ, Qᵀ * Q = 1 →
      ∀ D : BgData S.G' N, XiCData S.G' (compWeight L S.a₁) S.ν (k + 1) 1 eps D →
      ∀ ψh : S.U × Fin N → ℂ, (∀ q, ‖ψh q‖ ≤ ρ) →
      g i u (rotRaw (cmat Q) (rawOf D), rotFld (cmat Q) ψh) = g i u (rawOf D, ψh)) :
    ∀ Q : Matrix (Fin N) (Fin N) ℝ, Qᵀ * Q = 1 →
      ∀ θ ∈ physV S S.a₁ S.ν eps, ∀ θ' ∈ physV S S.a₁ S.ν eps,
      (θ'.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) =
        rotRaw (cmat Q) (θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) →
      ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ i, ∀ Φ ∈ physCarrier S 1 hp,
        Gf θ' i (s : ℂ) (fun b u => WithLp.toLp 2 (Q *ᵥ (Φ b u).ofLp)) = Gf θ i (s : ℂ) Φ := by
  intro Q hQ θ hθ θ' hθ' hrot s hs i Φ hΦ
  obtain ⟨e', he'⟩ := exists_linearIsometryEquiv_of_orth N hQ
  have hfun : (fun b u => WithLp.toLp 2 (Q *ᵥ (Φ b u).ofLp)) = fun b u => e' (Φ b u) :=
    funext fun b => funext fun u => (he' _).symm
  rw [hfun]
  have hs1 : ‖(s : ℂ)‖ < corrU := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs.1]
    unfold corrU
    linarith [hs.2]
  obtain ⟨D₀, hD₀, hD₀θ''⟩ := hθ.1
  have hD₀θ : (θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) = rawOf D₀ := hD₀θ''
  have hθ'mem : (θ'.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) ∈
      XiCRaw S.G' (compWeight L S.a₁) S.ν (k + 1) 1 eps := by
    rw [hrot]; exact rotRaw_mem hQ hθ.1
  rw [hG θ' i (s : ℂ) (fun b u => e' (Φ b u)), hG θ i (s : ℂ) Φ, ite_eq_left ⟨hθ'mem, hs1⟩,
    ite_eq_left ⟨hθ.1, hs1⟩, hrot, hD₀θ, hatOf_rot S 1 hp e' he' hρp hΦ]
  exact hg i (s : ℂ) hs1 Q hQ D₀ hD₀ _ (fun q => S.hatOf_mem 1 hρ hp Φ q)

open Classical in
/-- **Covariance of the marks `G₁ = β ∂_t|₀ ev`.** -/
theorem rotG1_of_evG (S : StepSetting d L N₁ m₁ k N ϱ) {hp : 0 < S.p₁} {ρ eps bb : ℝ}
    (hρ : 0 < ρ) (hρp : S.p₁ ≤ ρ) (hbb : 0 < bb) {ι' : Type*}
    (G : physParam N S → ι' → ℂ → (∀ b, (S.blockSplit 1 hp).Ωb b) → ℂ)
    (ev : ι' → ℂ → ℂ → RawData d L (N₁ * L ^ m₁) (k + 1) N × (S.U × Fin N → ℂ) → ℂ)
    (hG : ∀ θ i u Φ, G θ i u Φ =
      if (θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) ∈
          XiCRaw S.G' (compWeight L S.a₁) S.ν (k + 1) 1 eps ∧ ‖u‖ < corrU then
        (S.β : ℂ) * deriv (fun t : ℂ => ev i u t
          ((θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N), S.hatOf 1 ρ hp Φ)) 0
      else 0)
    (hev : ∀ i u t, ‖u‖ < corrU → ‖t‖ < bb → ∀ Q : Matrix (Fin N) (Fin N) ℝ, Qᵀ * Q = 1 →
      ∀ D : BgData S.G' N, XiCData S.G' (compWeight L S.a₁) S.ν (k + 1) 1 eps D →
      ∀ ψh : S.U × Fin N → ℂ, (∀ q, ‖ψh q‖ ≤ ρ) →
      ev i u t (rotRaw (cmat Q) (rawOf D), rotFld (cmat Q) ψh) = ev i u t (rawOf D, ψh)) :
    ∀ Q : Matrix (Fin N) (Fin N) ℝ, Qᵀ * Q = 1 →
      ∀ θ ∈ physV S S.a₁ S.ν eps, ∀ θ' ∈ physV S S.a₁ S.ν eps,
      (θ'.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) =
        rotRaw (cmat Q) (θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) →
      ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ i, ∀ Φ ∈ physCarrier S 1 hp,
        G θ' i (s : ℂ) (fun b u => WithLp.toLp 2 (Q *ᵥ (Φ b u).ofLp)) = G θ i (s : ℂ) Φ := by
  refine rotFam_of_termG S hρ hρp G (fun i u x => (S.β : ℂ) * deriv (fun t : ℂ => ev i u t x) 0)
    hG ?_
  intro i u hu Q hQ D hD ψh hψh
  refine congrArg (fun w => (S.β : ℂ) * w) (Filter.EventuallyEq.deriv_eq ?_)
  filter_upwards [Metric.ball_mem_nhds (0 : ℂ) hbb] with t ht
  exact hev i u t hu (mem_ball_zero_iff.1 ht) Q hQ D hD ψh hψh

end FamG

section Fam

variable {N₁ m₁ k : ℕ} [NeZero N₁] {ϱ : ℝ}

open Classical in
/-- **Covariance of a family of the form `[θ ∈ chart ∧ ‖u‖ < corrU] g u (θ.raw, ψ̂(Φ))`.** -/
theorem rotFam_of_term (S : StepSetting 3 3 N₁ m₁ k 2 ϱ) {hp : 0 < S.p₁} {ρ eps : ℝ}
    (hρ : 0 < ρ) (hρp : S.p₁ ≤ ρ) {ι' : Type*}
    (Gf : physParam 2 S → ι' → ℂ → (∀ b, (S.blockSplit 1 hp).Ωb b) → ℂ)
    (g : ι' → ℂ → RawData 3 3 (N₁ * 3 ^ m₁) (k + 1) 2 × (S.U × Fin 2 → ℂ) → ℂ)
    (hG : ∀ θ i u Φ, Gf θ i u Φ =
      if (θ.1 : RawData 3 3 (N₁ * 3 ^ m₁) (k + 1) 2) ∈
          XiCRaw S.G' (compWeight 3 S.a₁) S.ν (k + 1) 1 eps ∧ ‖u‖ < corrU then
        g i u ((θ.1 : RawData 3 3 (N₁ * 3 ^ m₁) (k + 1) 2), S.hatOf 1 ρ hp Φ)
      else 0)
    (hg : ∀ i u, ‖u‖ < corrU → ∀ Q : Matrix (Fin 2) (Fin 2) ℝ, Qᵀ * Q = 1 →
      ∀ D : BgData S.G' 2, XiCData S.G' (compWeight 3 S.a₁) S.ν (k + 1) 1 eps D →
      ∀ ψh : S.U × Fin 2 → ℂ, (∀ q, ‖ψh q‖ ≤ ρ) →
      g i u (rotRaw (cmat Q) (rawOf D), rotFld (cmat Q) ψh) = g i u (rawOf D, ψh)) :
    ∀ Q : Matrix (Fin 2) (Fin 2) ℝ, Qᵀ * Q = 1 →
      ∀ θ ∈ physV S S.a₁ S.ν eps, ∀ θ' ∈ physV S S.a₁ S.ν eps,
      (θ'.1 : RawData 3 3 (N₁ * 3 ^ m₁) (k + 1) 2) =
        rotRaw (cmat Q) (θ.1 : RawData 3 3 (N₁ * 3 ^ m₁) (k + 1) 2) →
      ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ i, ∀ Φ ∈ physCarrier S 1 hp,
        Gf θ' i (s : ℂ) (fun b u => WithLp.toLp 2 (Q *ᵥ (Φ b u).ofLp)) = Gf θ i (s : ℂ) Φ := rotFam_of_termG S hρ hρp Gf g hG hg

open Classical in
/-- **Covariance of the marks `G₁ = β ∂_t|₀ ev`.** -/
theorem rotG1_of_ev (S : StepSetting 3 3 N₁ m₁ k 2 ϱ) {hp : 0 < S.p₁} {ρ eps bb : ℝ}
    (hρ : 0 < ρ) (hρp : S.p₁ ≤ ρ) (hbb : 0 < bb) {ι' : Type*}
    (G : physParam 2 S → ι' → ℂ → (∀ b, (S.blockSplit 1 hp).Ωb b) → ℂ)
    (ev : ι' → ℂ → ℂ → RawData 3 3 (N₁ * 3 ^ m₁) (k + 1) 2 × (S.U × Fin 2 → ℂ) → ℂ)
    (hG : ∀ θ i u Φ, G θ i u Φ =
      if (θ.1 : RawData 3 3 (N₁ * 3 ^ m₁) (k + 1) 2) ∈
          XiCRaw S.G' (compWeight 3 S.a₁) S.ν (k + 1) 1 eps ∧ ‖u‖ < corrU then
        (S.β : ℂ) * deriv (fun t : ℂ => ev i u t
          ((θ.1 : RawData 3 3 (N₁ * 3 ^ m₁) (k + 1) 2), S.hatOf 1 ρ hp Φ)) 0
      else 0)
    (hev : ∀ i u t, ‖u‖ < corrU → ‖t‖ < bb → ∀ Q : Matrix (Fin 2) (Fin 2) ℝ, Qᵀ * Q = 1 →
      ∀ D : BgData S.G' 2, XiCData S.G' (compWeight 3 S.a₁) S.ν (k + 1) 1 eps D →
      ∀ ψh : S.U × Fin 2 → ℂ, (∀ q, ‖ψh q‖ ≤ ρ) →
      ev i u t (rotRaw (cmat Q) (rawOf D), rotFld (cmat Q) ψh) = ev i u t (rawOf D, ψh)) :
    ∀ Q : Matrix (Fin 2) (Fin 2) ℝ, Qᵀ * Q = 1 →
      ∀ θ ∈ physV S S.a₁ S.ν eps, ∀ θ' ∈ physV S S.a₁ S.ν eps,
      (θ'.1 : RawData 3 3 (N₁ * 3 ^ m₁) (k + 1) 2) =
        rotRaw (cmat Q) (θ.1 : RawData 3 3 (N₁ * 3 ^ m₁) (k + 1) 2) →
      ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ i, ∀ Φ ∈ physCarrier S 1 hp,
        G θ' i (s : ℂ) (fun b u => WithLp.toLp 2 (Q *ᵥ (Φ b u).ofLp)) = G θ i (s : ℂ) Φ := rotG1_of_evG S hρ hρp hbb G ev hG hev


open Classical in
theorem StepTowerG.famRot_GH {d L N : ℕ} [NeZero L] {κmin : ℝ} (T : StepTowerG d L N κmin) {k : ℕ} (hk : 1 ≤ k) {N₁ : ℕ}
    [NeZero N₁] {ν β p₁ : ℝ} {ϱ : ℝ} (S : StepSetting d L N₁ T.m₁ k N ϱ)
    (hS : S = hatStepKG T.hN k T.m₁ ϱ hk ν β p₁ T.δ) (hp : 0 < S.p₁) (z : RootIdx d L N₁ T.m₁ (k + 1))
        (ι : Type) [Fintype ι]
        {m₀ : ℕ}
        {ϱ₁ : ℝ}
        {cB BG κ r₀ δ₃ KcL Cx c₂ BG₂ δ₁ δfl : ℝ}
        {bL : ℝ}
        (hb₁ : 1 ≤ bL)
        (hbC : bL ≤ scaledC0 d)
        (Eτ : ι → RawData d L (N₁ * L ^ T.m₁) (k + 1) N → ℂ)
        (jL : ι → ℕ)
        (Gk : ι → GeneratingSet d L (N₁ * L ^ T.m₁) (k + 1) ϱ₁)
        (Gj : ι → GeneratingSet d L (N₁ * L ^ T.m₁) (k + 1) ϱ)
        (X₀ X₁f : ι → Finset (CTorus d L N₁ T.m₁ (k + 1)))
        (𝒦X : ι → Set (CTorus d L N₁ T.m₁ (k + 1)))
        (hB : ∀ τ, BgSetting N S.G' (Gk τ) (Gj τ) S.a₁ S.ν cB BG κ r₀ T.t δ₃
          (X₀ τ)          (X₁f τ) (jL τ))
        (hFl : ∀ τ, FlSetting N S.G' (Gk τ) (stepG d L N₁ T.m₁ k ϱ) S.a₁ S.ν κ BG
            T.t δ₃ KcL Cx c₂ BG₂
          δ₁ δfl (X₁f τ))
        {cψ : ℝ}
        (hcψ : 0 ≤ cψ)
        (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ T.m₁)
        {δc : ℝ}
        (hdm : decDomMargin d L N BG κ (xiC1 d * T.t) < δc)
        (hα : K4 d L N BG κ * (xiC1 d * T.t) < coerciveConst d / 2)
        (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
        {𝒮 : ι → Set (RawData d L (N₁ * L ^ T.m₁) (k + 1) N)}
        (F₁L : ι → DecParams S.G' × RawData d L (N₁ * L ^ T.m₁) (k + 1) N →
          (S.G'.Ω 1 × Fin N → ℂ) × (S.G'.Ω 1 → ℂ))
        (hF₁ : ∀ τ, ∀ (s : DecParams S.G') (D : BgData S.G' N), (∀ P, ‖s P‖ < Real.exp κ) →
          InUnionDomainC S.G' (bgC0 d L N) (c7 d L N BG κ) S.ν D → ∀ (φ : S.G'.Ω 1 × Fin N → ℂ)
            (α : S.G'.Ω 1 → ℂ), IsDecBg S.G' (compWeight L S.a₁) S.ν (rho4 d L N BG κ) s D φ α →
            F₁L τ (s, rawOf D) = (φ, α))
        (SolL : ι → Dec2.DecParams (coverOf S.G') × Edat (stepG d L N₁ T.m₁ k ϱ) N →
          ((stepG d L N₁ T.m₁ k ϱ).Ω 1 × Fin N → ℂ) × ((stepG d L N₁ T.m₁ k ϱ).Ω 1 → ℂ))
        (hSolprop : ∀ τ, ∀ p : Dec2.DecParams (coverOf S.G') × Edat (stepG d L N₁ T.m₁ k
            ϱ) N,
          (∀ P, ‖p.1 P‖ < Real.exp κ) →
          StrictDataM (stepG d L N₁ T.m₁ k ϱ) N false (2 * (K4 d L N BG κ * (xiC1 d *
              T.t)))
            δ₁ p.2 →
            (SolL τ p).1 = dphi (stepG d L N₁ T.m₁ k ϱ)
                (Dec2.decG (coverOf S.G') (stepG d L N₁ T.m₁ k ϱ) (compWeight L S.a₁)
                    S.ν p.1)
                p.2.2.1 p.2.1
                (pertSource (stepG d L N₁ T.m₁ k ϱ) (compWeight L S.a₁) p.2.2.2.1
                    p.2.2.2.2)
                (SolL τ p).2 ∧
            Dec2.DecFixed (coverOf S.G') (stepG d L N₁ T.m₁ k ϱ) (compWeight L S.a₁)
                S.ν p.1
              false p.2.2.1 p.2.1
              (pertSource (stepG d L N₁ T.m₁ k ϱ) (compWeight L S.a₁) p.2.2.2.1
                  p.2.2.2.2)
              (SolL τ p).2 ∧
            Background.Small (stepG d L N₁ T.m₁ k ϱ) (SolL τ p).2
              (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
            Background.Small (stepG d L N₁ T.m₁ k ϱ) (SolL τ p).2 (cK2' d L N (famConst d L BG₂ κ)
                * δ₁) ∧
            SupBounds (stepG d L N₁ T.m₁ k ϱ) (SolL τ p).1
              (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
            (∀ δα' : (stepG d L N₁ T.m₁ k ϱ).Ω 1 → ℂ,
              Background.Small (stepG d L N₁ T.m₁ k ϱ) δα' (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) →
              Dec2.DecFixed (coverOf S.G') (stepG d L N₁ T.m₁ k ϱ) (compWeight L S.a₁)
                  S.ν p.1
                false p.2.2.1 p.2.1
                (pertSource (stepG d L N₁ T.m₁ k ϱ) (compWeight L S.a₁) p.2.2.2.1
                    p.2.2.2.2) δα' →
              δα' = (SolL τ p).2))
        (FkL : ∀ τ, RawData d L (N₁ * L ^ T.m₁) (k + 1) N →
          ((Gk τ).Ω 1 × Fin N → ℂ) × ((Gk τ).Ω 1 → ℂ))
        (hFk : ∀ τ, ∀ D : BgData (Gk τ) N, InUnionDomainC (Gk τ) (bgC0 d L N) (bgC1 d L N) S.ν
            D →
          FkL τ (rawOf D) = (bgFieldC (Gk τ) (compWeight L S.a₁) S.ν (bgC0 d L N) D,
            bgMultC (Gk τ) (compWeight L S.a₁) S.ν (bgC0 d L N) D))
        (h𝒮 : ∀ τ, ∀ t ∈ FlRealLC S.G' (stepG d L N₁ T.m₁ k ϱ) S.a₁ S.ν BG κ T.t
            (X₁f τ) BG₂ δ₁,
          D2raw (Gk τ) (Gj τ) (compWeight L S.a₁) (FkL τ)
            (d1Triple S.G' (Gk τ) (stepG d L N₁ T.m₁ k ϱ) (compWeight L S.a₁) t.1.1
              t.2.1 t.2.2) ∈ 𝒮 τ)
        {ρ : ℝ}
        (hρ : 0 < ρ)
        (hρc : ρ ≤ cψ)
        {bb : ℝ}
        (hbb : 0 < bb)
        (hab : (corrU + bb) * markedRad d L N k S.a₁ κ cψ ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) < δ₁)
        (G₁ : physParam N S →
          {q // q ∈ markedIdx (fun _ => (Set.univ : Set (CTorus d L N₁ T.m₁ (k + 1))))
            (fun τ => polyDom S.G' (X₁f τ) m₀ (jL τ) (𝒦X τ)) z} →
          ℂ → (∀ b, (S.blockSplit 1 hp).Ωb b) → ℂ)
        (hG₁ : ∀ θ q u Φ, G₁ θ q u Φ =
          if (θ.1 : RawData d L (N₁ * L ^ T.m₁) (k + 1) N) ∈
              XiCRaw S.G' (compWeight L S.a₁) S.ν (k + 1) 1 T.t ∧ ‖u‖ < corrU then
            (S.β : ℂ) * deriv (fun t : ℂ => evDec (X₁f q.1.1) m₀ (jL q.1.1) (𝒦X q.1.1) S.a₁ S.ν
              S.hG' ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) (F₁L q.1.1) (SolL q.1.1)
              (eTermFun S.G' (Gk q.1.1) (Gj q.1.1) (stepG d L N₁ T.m₁ k
                  ϱ)
                (compWeight L S.a₁) (FkL q.1.1)
                (fun r => (S.β : ℂ)⁻¹ * Eτ q.1.1 r))
              (S.blockU z) u t q.1.2
              ((θ.1 : RawData d L (N₁ * L ^ T.m₁) (k + 1) N), S.hatOf 1 ρ hp Φ)) 0
          else 0)
        (hρp : S.p₁ ≤ ρ)
        (𝒴C : Finset (Set (CTorus d L N₁ T.m₁ (k + 1))))
        (H : physParam N S → {Y // Y ∈ 𝒴C} → ℂ → (∀ b, (S.blockSplit 1 hp).Ωb b) → ℂ)
        (hH : ∀ θ Y u Φ, H θ Y u Φ =
          if (θ.1 : RawData d L (N₁ * L ^ T.m₁) (k + 1) N) ∈
              XiCRaw S.G' (compWeight L S.a₁) S.ν (k + 1) 1 T.t ∧ ‖u‖ < corrU then
            ∑ τ, if Y.1 ∈ polyDom S.G' (X₁f τ) m₀ (jL τ) (𝒦X τ) then
              (S.β : ℂ) * (evDec (X₁f τ) m₀ (jL τ) (𝒦X τ) S.a₁ S.ν S.hG'
                ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) (F₁L τ) (SolL τ)
                (eTermFun S.G' (Gk τ) (Gj τ) (stepG d L N₁ T.m₁ k ϱ)
                  (compWeight L S.a₁) (FkL τ)
                  (fun r => (S.β : ℂ)⁻¹ * Eτ τ r)) (S.blockU z) u 0
                  Y.1 ((θ.1 : RawData d L (N₁ * L ^ T.m₁) (k + 1) N), S.hatOf 1 ρ hp Φ) -
                evDec (X₁f τ) m₀ (jL τ) (𝒦X τ) S.a₁ S.ν S.hG'
                ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) (F₁L τ) (SolL τ)
                (eTermFun S.G' (Gk τ) (Gj τ) (stepG d L N₁ T.m₁ k ϱ)
                  (compWeight L S.a₁) (FkL τ)
                  (fun r => (S.β : ℂ)⁻¹ * Eτ τ r)) (S.blockU z) 0 0
                  Y.1 ((θ.1 : RawData d L (N₁ * L ^ T.m₁) (k + 1) N), S.hatOf 1 ρ hp Φ))
            else 0
          else 0)
        (hErot : ∀ τ, ∀ Q : Matrix (Fin N) (Fin N) ℝ, Qᵀ * Q = 1 → ∀ r ∈ 𝒮 τ,
          rotRaw (cmat Q) r ∈ 𝒮 τ → Eτ τ (rotRaw (cmat Q) r) = Eτ τ r) :
    (∀ Q : Matrix (Fin N) (Fin N) ℝ, Qᵀ * Q = 1 →
        ∀ θ ∈ physV S S.a₁ S.ν T.t, ∀ θ' ∈ physV S S.a₁ S.ν T.t,
        (θ'.1 : RawData d L (N₁ * L ^ T.m₁) (k + 1) N) =
          rotRaw (cmat Q) (θ.1 : RawData d L (N₁ * L ^ T.m₁) (k + 1) N) →
        ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ j, ∀ Φ ∈ physCarrier S 1 hp,
          G₁ θ' j (s : ℂ) (fun b u => WithLp.toLp 2 (Q *ᵥ (Φ b u).ofLp)) = G₁ θ j (s : ℂ) Φ) ∧
    (∀ Q : Matrix (Fin N) (Fin N) ℝ, Qᵀ * Q = 1 →
        ∀ θ ∈ physV S S.a₁ S.ν T.t, ∀ θ' ∈ physV S S.a₁ S.ν T.t,
        (θ'.1 : RawData d L (N₁ * L ^ T.m₁) (k + 1) N) =
          rotRaw (cmat Q) (θ.1 : RawData d L (N₁ * L ^ T.m₁) (k + 1) N) →
        ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ Y : {Y // Y ∈ 𝒴C}, ∀ Φ ∈ physCarrier S 1 hp,
          H θ' Y (s : ℂ) (fun b u => WithLp.toLp 2 (Q *ᵥ (Φ b u).ofLp)) = H θ Y (s : ℂ) Φ) := by
  have hmr0 : 0 ≤ markedRad d L N k S.a₁ κ cψ ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) := by
    have ha₁S : 0 < S.a₁ := by rw [hS]; show (0 : ℝ) < 1; norm_num
    have ha0 : 0 < compWeight L S.a₁ k := compWeight_pos (by have := T.hL; omega) ha₁S hk
    have hCs := covSupConstC_nonneg (d := d) (L := L) (N := N) (by have := T.hd; omega) T.hL ha0 κ
    unfold markedRad
    positivity
  have hδmr : ∀ um tm : ℂ, ‖um‖ < corrU → ‖tm‖ < bb →
      (‖um‖ + ‖tm‖) * markedRad d L N k S.a₁ κ cψ ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) < δ₁ :=
    fun um tm h1 h2 => lt_of_le_of_lt
      (mul_le_mul_of_nonneg_right (by linarith [h1.le, h2.le]) hmr0) hab
  have hev : ∀ (τ : ι) (Y : Set (CTorus d L N₁ T.m₁ (k + 1))) (um tm : ℂ), ‖um‖ < corrU →
      ‖tm‖ < bb → ∀ Q : Matrix (Fin N) (Fin N) ℝ, Qᵀ * Q = 1 →
      ∀ D : BgData S.G' N, XiCData S.G' S.a S.ν (k + 1) 1 T.t D →
      ∀ ψh : unitPts S.G' × Fin N → ℂ, (∀ q, ‖ψh q‖ ≤ cψ) →
      evDec (X₁f τ) m₀ (jL τ) (𝒦X τ) S.a₁ S.ν S.hG' ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)
        (F₁L τ) (SolL τ)
        (eTermFun S.G' (Gk τ) (Gj τ) (stepG d L N₁ T.m₁ k (rhoSep T.m₁)) (compWeight L S.a₁)
          (FkL τ) (fun r => (S.β : ℂ)⁻¹ * Eτ τ r))
        (S.blockU z) um tm Y (rotRaw (cmat Q) (rawOf D), rotFld (cmat Q) ψh) =
      evDec (X₁f τ) m₀ (jL τ) (𝒦X τ) S.a₁ S.ν S.hG' ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)
        (F₁L τ) (SolL τ)
        (eTermFun S.G' (Gk τ) (Gj τ) (stepG d L N₁ T.m₁ k (rhoSep T.m₁)) (compWeight L S.a₁)
          (FkL τ) (fun r => (S.β : ℂ)⁻¹ * Eτ τ r))
        (S.blockU z) um tm Y (rawOf D, ψh) :=
    fun τ Y um tm hum htm Q hQ D hD ψh hψh => by
      have h := evDec_eTerm_rot (d := d) (L := L) (N₁ := N₁) (m₁ := T.m₁) (k := k) (N := N)
        (Gp := S.G') (Gk := Gk τ) (Gj := Gj τ) (Hm := stepG d L N₁ T.m₁ k ϱ)
        (E := fun r => (S.β : ℂ)⁻¹ * Eτ τ r) (m₀ := m₀) hb₁ hbC (hB τ)
        (hFl τ) hk S.hG S.hG'
        ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) hcψ hMX hdm hα hsm (hF₁ τ) (hSolprop τ) hQ
        (hFk τ) (h𝒮 τ)
        (fun r hr hr' => congrArg (fun w => (S.β : ℂ)⁻¹ * w) (hErot τ Q hQ r hr hr'))
        (S.blockU z) (jL τ) (𝒦X τ) (hδmr um tm hum htm) Y hD hψh
      exact h
  have h0b : ‖(0 : ℂ)‖ < bb := by rw [norm_zero]; exact hbb
  have h0c : ‖(0 : ℂ)‖ < corrU := by rw [norm_zero]; unfold corrU; norm_num
  refine ⟨rotG1_of_evG S hρ hρp hbb G₁
    (fun (q : {q // q ∈ markedIdx (fun _ => (Set.univ : Set (CTorus d L N₁ T.m₁ (k + 1))))
      (fun τ => polyDom S.G' (X₁f τ) m₀ (jL τ) (𝒦X τ)) z}) u t x =>
      evDec (X₁f q.1.1) m₀ (jL q.1.1) (𝒦X q.1.1) S.a₁ S.ν S.hG'
        ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) (F₁L q.1.1) (SolL q.1.1)
        (eTermFun S.G' (Gk q.1.1) (Gj q.1.1) (stepG d L N₁ T.m₁ k (rhoSep T.m₁))
          (compWeight L S.a₁) (FkL q.1.1) (fun r => (S.β : ℂ)⁻¹ * Eτ q.1.1 r))
        (S.blockU z) u t q.1.2 x) hG₁
    (fun q u t hu ht Q hQ D hD ψh hψh =>
      hev q.1.1 q.1.2 u t hu ht Q hQ D hD ψh (fun p => (hψh p).trans hρc)), ?_⟩
  refine rotFam_of_termG S hρ hρp H
    (fun (Y : {Y // Y ∈ 𝒴C}) u x => ∑ τ, if Y.1 ∈ polyDom S.G' (X₁f τ) m₀ (jL τ) (𝒦X τ) then
      (S.β : ℂ) * (evDec (X₁f τ) m₀ (jL τ) (𝒦X τ) S.a₁ S.ν S.hG'
        ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) (F₁L τ) (SolL τ)
        (eTermFun S.G' (Gk τ) (Gj τ) (stepG d L N₁ T.m₁ k (rhoSep T.m₁))
          (compWeight L S.a₁) (FkL τ) (fun r => (S.β : ℂ)⁻¹ * Eτ τ r))
        (S.blockU z) u 0 Y.1 x -
        evDec (X₁f τ) m₀ (jL τ) (𝒦X τ) S.a₁ S.ν S.hG'
        ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) (F₁L τ) (SolL τ)
        (eTermFun S.G' (Gk τ) (Gj τ) (stepG d L N₁ T.m₁ k (rhoSep T.m₁))
          (compWeight L S.a₁) (FkL τ) (fun r => (S.β : ℂ)⁻¹ * Eτ τ r))
        (S.blockU z) 0 0 Y.1 x)
      else 0) hH ?_
  intro Y u hu Q hQ D hD ψh hψh
  refine Finset.sum_congr rfl fun τ _ => ?_
  by_cases hY : Y.1 ∈ polyDom S.G' (X₁f τ) m₀ (jL τ) (𝒦X τ)
  · rw [ite_eq_left hY, ite_eq_left hY,
      hev τ Y.1 u 0 hu h0b Q hQ D hD ψh (fun p => (hψh p).trans hρc),
      hev τ Y.1 0 0 h0c h0b Q hQ D hD ψh (fun p => (hψh p).trans hρc)]
  · rw [ite_eq_right hY, ite_eq_right hY]


open Classical in
/-- **The covariance of the marks `G₁` and of the activity `H` of the localized old terms.**  If the
old terms `Eτ` are invariant under the real rotations on the sets `𝒮` that contain the composed
step data, then `G₁` and `H` (given through their formulas by `evDec`, the localized terms along the
masked tangent) are covariant under the rotation of the parameter and of the block variables. -/
theorem famRot_GH {κmin : ℝ} (T : StepTower κmin) {k : ℕ} (hk : 1 ≤ k) {N₁ : ℕ} [NeZero N₁]
    {ν β p₁ : ℝ} (S : StepSetting 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁))
    (hS : S = T.step k hk N₁ ν β p₁) (hp : 0 < S.p₁) (z : RootIdx 3 3 N₁ T.m₁ (k + 1))
        (ι : Type) [Fintype ι]
        {m₀ : ℕ}
        {ϱ₁ : ℝ}
        {cB BG κ r₀ δ₃ KcL Cx c₂ BG₂ δ₁ δfl : ℝ}
        {bL : ℝ}
        (hb₁ : 1 ≤ bL)
        (hbC : bL ≤ scaledC0 3)
        (Eτ : ι → RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2 → ℂ)
        (jL : ι → ℕ)
        (Gk : ι → GeneratingSet 3 3 (N₁ * 3 ^ T.m₁) (k + 1) ϱ₁)
        (Gj : ι → GeneratingSet 3 3 (N₁ * 3 ^ T.m₁) (k + 1) (rhoSep T.m₁))
        (X₀ X₁f : ι → Finset (CTorus 3 3 N₁ T.m₁ (k + 1)))
        (𝒦X : ι → Set (CTorus 3 3 N₁ T.m₁ (k + 1)))
        (hB : ∀ τ, BgSetting 2 S.G' (Gk τ) (Gj τ) S.a₁ S.ν cB BG κ r₀ T.t δ₃
          (X₀ τ)          (X₁f τ) (jL τ))
        (hFl : ∀ τ, FlSetting 2 S.G' (Gk τ) (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) S.a₁ S.ν κ BG
            T.t δ₃ KcL Cx c₂ BG₂
          δ₁ δfl (X₁f τ))
        {cψ : ℝ}
        (hcψ : 0 ≤ cψ)
        (hMX : cstarX 3 3 * Real.exp (N0 3 3 * κ) ≤ (3 : ℝ) ^ T.m₁)
        {δc : ℝ}
        (hdm : decDomMargin 3 3 2 BG κ (xiC1 3 * T.t) < δc)
        (hα : K4 3 3 2 BG κ * (xiC1 3 * T.t) < coerciveConst 3 / 2)
        (hsm : δc ^ 2 * smallConstX 3 3 κ ≤ 1 / 4)
        {𝒮 : ι → Set (RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2)}
        (F₁L : ι → DecParams S.G' × RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2 →
          (S.G'.Ω 1 × Fin 2 → ℂ) × (S.G'.Ω 1 → ℂ))
        (hF₁ : ∀ τ, ∀ (s : DecParams S.G') (D : BgData S.G' 2), (∀ P, ‖s P‖ < Real.exp κ) →
          InUnionDomainC S.G' (bgC0 3 3 2) (c7 3 3 2 BG κ) S.ν D → ∀ (φ : S.G'.Ω 1 × Fin 2 → ℂ)
            (α : S.G'.Ω 1 → ℂ), IsDecBg S.G' (compWeight 3 S.a₁) S.ν (rho4 3 3 2 BG κ) s D φ α →
            F₁L τ (s, rawOf D) = (φ, α))
        (SolL : ι → Dec2.DecParams (coverOf S.G') × Edat (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) 2 →
          ((stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)).Ω 1 × Fin 2 → ℂ) × ((stepG 3 3 N₁ T.m₁ k (rhoSep
              T.m₁)).Ω 1 → ℂ))
        (hSolprop : ∀ τ, ∀ p : Dec2.DecParams (coverOf S.G') × Edat (stepG 3 3 N₁ T.m₁ k
            (rhoSep T.m₁)) 2,
          (∀ P, ‖p.1 P‖ < Real.exp κ) →
          StrictDataM (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) 2 false (2 * (K4 3 3 2 BG κ * (xiC1 3 *
              T.t)))
            δ₁ p.2 →
            (SolL τ p).1 = dphi (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁))
                (Dec2.decG (coverOf S.G') (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) (compWeight 3 S.a₁)
                    S.ν p.1)
                p.2.2.1 p.2.1
                (pertSource (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) (compWeight 3 S.a₁) p.2.2.2.1
                    p.2.2.2.2)
                (SolL τ p).2 ∧
            Dec2.DecFixed (coverOf S.G') (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) (compWeight 3 S.a₁)
                S.ν p.1
              false p.2.2.1 p.2.1
              (pertSource (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) (compWeight 3 S.a₁) p.2.2.2.1
                  p.2.2.2.2)
              (SolL τ p).2 ∧
            Small (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) (SolL τ p).2
              (c6' 3 3 2 (famConst 3 3 BG₂ κ) (gamma1 3 / 8)) ∧
            Small (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) (SolL τ p).2 (cK2' 3 3 2 (famConst 3 3 BG₂ κ)
                * δ₁) ∧
            SupBounds (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) (SolL τ p).1
              (cK2' 3 3 2 (famConst 3 3 BG₂ κ) * δ₁) ∧
            (∀ δα' : (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)).Ω 1 → ℂ,
              Small (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) δα' (c6' 3 3 2 (famConst 3 3 BG₂ κ) (gamma1
                  3 / 8)) →
              Dec2.DecFixed (coverOf S.G') (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) (compWeight 3 S.a₁)
                  S.ν p.1
                false p.2.2.1 p.2.1
                (pertSource (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) (compWeight 3 S.a₁) p.2.2.2.1
                    p.2.2.2.2) δα' →
              δα' = (SolL τ p).2))
        (FkL : ∀ τ, RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2 →
          ((Gk τ).Ω 1 × Fin 2 → ℂ) × ((Gk τ).Ω 1 → ℂ))
        (hFk : ∀ τ, ∀ D : BgData (Gk τ) 2, InUnionDomainC (Gk τ) (bgC0 3 3 2) (bgC1 3 3 2) S.ν
            D →
          FkL τ (rawOf D) = (bgFieldC (Gk τ) (compWeight 3 S.a₁) S.ν (bgC0 3 3 2) D,
            bgMultC (Gk τ) (compWeight 3 S.a₁) S.ν (bgC0 3 3 2) D))
        (h𝒮 : ∀ τ, ∀ t ∈ FlRealLC S.G' (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) S.a₁ S.ν BG κ T.t
            (X₁f τ) BG₂ δ₁,
          D2raw (Gk τ) (Gj τ) (compWeight 3 S.a₁) (FkL τ)
            (d1Triple S.G' (Gk τ) (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) (compWeight 3 S.a₁) t.1.1
              t.2.1 t.2.2) ∈ 𝒮 τ)
        {ρ : ℝ}
        (hρ : 0 < ρ)
        (hρc : ρ ≤ cψ)
        {bb : ℝ}
        (hbb : 0 < bb)
        (hab : (corrU + bb) * markedRad 3 3 2 k S.a₁ κ cψ ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) < δ₁)
        (G₁ : physParam 2 S →
          {q // q ∈ markedIdx (fun _ => (Set.univ : Set (CTorus 3 3 N₁ T.m₁ (k + 1))))
            (fun τ => polyDom S.G' (X₁f τ) m₀ (jL τ) (𝒦X τ)) z} →
          ℂ → (∀ b, (S.blockSplit 1 hp).Ωb b) → ℂ)
        (hG₁ : ∀ θ q u Φ, G₁ θ q u Φ =
          if (θ.1 : RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2) ∈
              XiCRaw S.G' (compWeight 3 S.a₁) S.ν (k + 1) 1 T.t ∧ ‖u‖ < corrU then
            (S.β : ℂ) * deriv (fun t : ℂ => evDec (X₁f q.1.1) m₀ (jL q.1.1) (𝒦X q.1.1) S.a₁ S.ν
              S.hG' ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) (F₁L q.1.1) (SolL q.1.1)
              (eTermFun S.G' (Gk q.1.1) (Gj q.1.1) (stepG 3 3 N₁ T.m₁ k
                  (rhoSep T.m₁))
                (compWeight 3 S.a₁) (FkL q.1.1)
                (fun r => (S.β : ℂ)⁻¹ * Eτ q.1.1 r))
              (S.blockU z) u t q.1.2
              ((θ.1 : RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2), S.hatOf 1 ρ hp Φ)) 0
          else 0)
        (hρp : S.p₁ ≤ ρ)
        (𝒴C : Finset (Set (CTorus 3 3 N₁ T.m₁ (k + 1))))
        (H : physParam 2 S → {Y // Y ∈ 𝒴C} → ℂ → (∀ b, (S.blockSplit 1 hp).Ωb b) → ℂ)
        (hH : ∀ θ Y u Φ, H θ Y u Φ =
          if (θ.1 : RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2) ∈
              XiCRaw S.G' (compWeight 3 S.a₁) S.ν (k + 1) 1 T.t ∧ ‖u‖ < corrU then
            ∑ τ, if Y.1 ∈ polyDom S.G' (X₁f τ) m₀ (jL τ) (𝒦X τ) then
              (S.β : ℂ) * (evDec (X₁f τ) m₀ (jL τ) (𝒦X τ) S.a₁ S.ν S.hG'
                ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) (F₁L τ) (SolL τ)
                (eTermFun S.G' (Gk τ) (Gj τ) (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁))
                  (compWeight 3 S.a₁) (FkL τ)
                  (fun r => (S.β : ℂ)⁻¹ * Eτ τ r)) (S.blockU z) u 0
                  Y.1 ((θ.1 : RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2), S.hatOf 1 ρ hp Φ) -
                evDec (X₁f τ) m₀ (jL τ) (𝒦X τ) S.a₁ S.ν S.hG'
                ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) (F₁L τ) (SolL τ)
                (eTermFun S.G' (Gk τ) (Gj τ) (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁))
                  (compWeight 3 S.a₁) (FkL τ)
                  (fun r => (S.β : ℂ)⁻¹ * Eτ τ r)) (S.blockU z) 0 0
                  Y.1 ((θ.1 : RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2), S.hatOf 1 ρ hp Φ))
            else 0
          else 0)
        (hErot : ∀ τ, ∀ Q : Matrix (Fin 2) (Fin 2) ℝ, Qᵀ * Q = 1 → ∀ r ∈ 𝒮 τ,
          rotRaw (cmat Q) r ∈ 𝒮 τ → Eτ τ (rotRaw (cmat Q) r) = Eτ τ r) :
    (∀ Q : Matrix (Fin 2) (Fin 2) ℝ, Qᵀ * Q = 1 →
        ∀ θ ∈ physV S S.a₁ S.ν T.t, ∀ θ' ∈ physV S S.a₁ S.ν T.t,
        (θ'.1 : RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2) =
          rotRaw (cmat Q) (θ.1 : RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2) →
        ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ j, ∀ Φ ∈ physCarrier S 1 hp,
          G₁ θ' j (s : ℂ) (fun b u => WithLp.toLp 2 (Q *ᵥ (Φ b u).ofLp)) = G₁ θ j (s : ℂ) Φ) ∧
    (∀ Q : Matrix (Fin 2) (Fin 2) ℝ, Qᵀ * Q = 1 →
        ∀ θ ∈ physV S S.a₁ S.ν T.t, ∀ θ' ∈ physV S S.a₁ S.ν T.t,
        (θ'.1 : RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2) =
          rotRaw (cmat Q) (θ.1 : RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2) →
        ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ Y : {Y // Y ∈ 𝒴C}, ∀ Φ ∈ physCarrier S 1 hp,
          H θ' Y (s : ℂ) (fun b u => WithLp.toLp 2 (Q *ᵥ (Φ b u).ofLp)) = H θ Y (s : ℂ) Φ) := by
  subst hS
  exact T.toG.famRot_GH hk (ϱ := rhoSep T.m₁) (T.step k hk N₁ ν β p₁) rfl hp z ι hb₁ hbC Eτ jL Gk Gj X₀ X₁f 𝒦X hB hFl hcψ hMX hdm hα hsm F₁L hF₁ SolL hSolprop FkL hFk h𝒮 hρ hρc hbb hab G₁ hG₁ hρp 𝒴C H hH hErot

end Fam

end Balaban.Inhabited
