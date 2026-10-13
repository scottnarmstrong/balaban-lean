/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.StepTowerScale
public import Balaban.Inhabited.StepScaleDataGBridge
public import Balaban.Fluctuation.SourceDirectTermsScale
public import Balaban.Fluctuation.ParamActivitySubspace
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The source direct terms at the shared tower, with the domain family chosen once

`sourceDirectTerms_scale_fromTower` restates `sourceDirectTerms_scale` for one tower
`T : StepTower κmin` and its per-scale package `D : StepScaleData T …`: the landed proof is re-run
with its tower prologue (the choice of the constants and of the radii, `FlCore`, `XiCData` and the
covers) replaced by the fields of `T` and `D`.  The expanded function `val`, the domains `𝒴` and
the terms `Tt` are chosen before the chart point; at every point of the source slice a
`DirectTerms` instance with these domains and terms exists.  No threshold in `β` is needed beyond
`1 ≤ β`.

`directTermsFamily_shared_labels` and `directTerms_sharedLabels_heq` record that two `DirectTerms`
instances with the same domain family have the same thick labels and the same block split, so the
label activities built from them live on one label type.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Localization Balaban.Multiscale Balaban.Polymer Balaban.Background

section Shared

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}
  {S : StepSetting d L N₁ m₁ k N ϱ} {m₀ : ℕ} {Λ F' E : Type}
  [NormedAddCommGroup Λ] [NormedSpace ℂ Λ] [NormedAddCommGroup E] [NormedSpace ℂ E]
  {hp : 0 < S.p₁} {emb : (S.U × Fin N → ℂ) → F'} {ρ Rσ εU a : ℝ} {Θ₀ : Λ}
  {SΛ : Set Λ} {XW : Set (F' × F')} {val : F' → F' → ℂ → Λ → ℂ}
  {AgΘ : Set (CTorus d L N₁ m₁ (k + 1)) → Λ → Λ → Prop}
  {AgF : Set (CTorus d L N₁ m₁ (k + 1)) → F' → F' → Prop}
  {J : E →L[ℂ] Λ}

/-- **Two sources of one family have the same labels.**  For `I` a `DirectTerms` instance and
`hF` the relative family over `V`, the instances `I.atThetaOn e₀` and `I.atThetaOn e` at two
points `e₀, e ∈ V` have the domains and terms of `I`, and their thick labels are those of `I`
(definitionally); the block split `S.blockSplit m₀ hp` does not depend on the instance. -/
theorem directTermsFamily_shared_labels
    (I : DirectTerms S m₀ hp emb ρ Rσ εU a Θ₀ SΛ XW val AgΘ AgF) {V : Set E}
    (hF : DirectTermsFamilyOn S m₀ J I V) {e₀ e : E} (he₀ : e₀ ∈ V) (he : e ∈ V) :
    ((I.atThetaOn S m₀ J hF he₀).𝒴 = I.𝒴 ∧ (I.atThetaOn S m₀ J hF he).𝒴 = I.𝒴 ∧
      (I.atThetaOn S m₀ J hF he₀).T = I.T ∧ (I.atThetaOn S m₀ J hF he).T = I.T) ∧
    thickLabels (I.atThetaOn S m₀ J hF he₀).𝒴 (I.atThetaOn S m₀ J hF he₀).dom =
      thickLabels I.𝒴 I.dom ∧
    thickLabels (I.atThetaOn S m₀ J hF he).𝒴 (I.atThetaOn S m₀ J hF he).dom =
      thickLabels I.𝒴 I.dom :=
  ⟨⟨rfl, rfl, rfl, rfl⟩, rfl, rfl⟩

omit [NeZero L] [NeZero N₁] in
/-- **Instances with equal domain families have the same thick labels.**  If `I₁` and `I₂` are
`DirectTerms` instances (at any data, for any admissible sets and terms) whose domain families both
equal `𝒴`, then `thickLabels` of `I₁` and of `I₂` are, up to the transport along `I₁.𝒴 = 𝒴`,
`I₂.𝒴 = 𝒴`, the thick labels of `𝒴` for the domain proof `hdom`. -/
theorem directTerms_sharedLabels_heq {𝒴 : Finset (Set (CTorus d L N₁ m₁ (k + 1)))}
    (hdom : ∀ Y ∈ 𝒴, IsDj m₀ (k + 1) Y)
    (𝒴₁ 𝒴₂ : Finset (Set (CTorus d L N₁ m₁ (k + 1))))
    (d₁ : ∀ Y ∈ 𝒴₁, IsDj m₀ (k + 1) Y) (d₂ : ∀ Y ∈ 𝒴₂, IsDj m₀ (k + 1) Y)
    (h₁ : 𝒴₁ = 𝒴) (h₂ : 𝒴₂ = 𝒴) :
    HEq (thickLabels 𝒴₁ d₁) (thickLabels 𝒴 hdom) ∧ HEq (thickLabels 𝒴₂ d₂) (thickLabels 𝒴 hdom) ∧
    HEq ((thickLabels 𝒴₁ d₁).sum (thickLabels 𝒴₂ d₂))
      ((thickLabels 𝒴 hdom).sum (thickLabels 𝒴 hdom)) := by
  subst h₁ h₂
  exact ⟨HEq.rfl, HEq.rfl, HEq.rfl⟩

end Shared

end Balaban.Fluctuation

namespace Balaban.Inhabited

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation
  Balaban.Localization Balaban.Localization.LevelPair Balaban.Localization.I5Inhabited
  Balaban.Polymer Balaban.SmallField.Def6 Balaban.Inhabited.LevelStep Filter Topology

/-- **The radius margin at the ray `3/2`, general `d`, `L`, `N`** (OBSRAY §2–§3): with
`r = c_ψ / (2 p₁) - 4`, positivity of `c_ψ` gives `(4 + r) (3/2) p₁ = 3 c_ψ / 4 < c_ψ`. -/
theorem lvRG_ray_margin_scaled (d L N : ℕ) (κ t b p₁ : ℝ)
    (hc : 0 < lvCpsiG d L N κ t b) (hp : 0 < p₁) :
    ((2 : ℝ) * 2 + lvRG d L N κ t b p₁) * (3 / 2 * p₁) < lvCpsiG d L N κ t b := by
  have e : ((2 : ℝ) * 2 + lvRG d L N κ t b p₁) * (3 / 2 * p₁) =
      3 / 4 * lvCpsiG d L N κ t b := by
    unfold lvRG
    field_simp
    ring
  rw [e]
  linarith

/-- **The radius margin at the ray `3/2` at the general tower** (OBSRAY §2–§3): the landed
`StepScaleDataG.ray_margin`-type bound `(4 + r) (3/2) p₁ < c_ψ`. -/
theorem StepScaleDataG.ray_margin_scaled {d L N : ℕ} [NeZero L] {κmin : ℝ}
    {T : StepTowerG d L N κmin} {k : ℕ} {hk : 1 ≤ k}
    {N₁ : ℕ} [NeZero N₁] {ν β p₁ : ℝ} (D : StepScaleDataG T k hk N₁ ν β p₁) (hp : 0 < p₁) :
    ((2 : ℝ) * 2 + lvRG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2))) p₁) * (3 / 2 * p₁) <
      lvCpsiG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2))) :=
  lvRG_ray_margin_scaled d L N _ _ _ _ D.cψ_pos hp


open Classical in
/-- **The direct terms of the zero class at the shared general tower `T`, on the source slice
`η = q/β`, general `d`, `L`, `N`.**  As `sourceDirectTerms_scale_fromTower_ray_rho` for
`T : StepTowerG d L N κmin` and `D : StepScaleDataG T …`, at the step
`T.step k hk N₁ ν β p₁ = hatStepKG … T.δ`, the block scale `T.m₀` and the block coupling
`β L^{k(d-2)}`.  The expanded function, the domains and the terms are chosen before the chart point
and the source; the hypotheses are `max 1 ρ ≤ β`, `0 < q ≤ ρ`, `L ^ T.m₀ ∣ N₁` and `5 < N₁`.  The ray clause ranges over the hat fields with `‖ψ̂ p‖ ≤ p₁` (the full disc; the
margin is `StepScaleDataG.ray_margin_scaled`).
The last two conjuncts make the terms explicit, as in `sourceDirectTerms_slice_ray`. -/

theorem sourceDirectTerms_scale_fromTowerG_ray_full_rho {d L N : ℕ} [NeZero L] {κmin : ℝ} (T : StepTowerG d L N κmin)
    (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁] (hLN : L ^ T.m₀ ∣ N₁) (hN : 5 < N₁)
    (ν : ℝ) (hνpos : 0 < ν) (hν : ν * (L : ℝ) ^ (2 * (k + 1)) ≤ 1) (β : ℝ) (ρ : ℝ) (hρ : 0 < ρ) (hβρ : max 1 ρ ≤ β)
    (p₁ : ℝ) (q : ℝ) (hq0 : 0 < q) (hq : q ≤ ρ)
    (D : StepScaleDataG T k hk N₁ ν β p₁)
    (S : StepSetting d L N₁ T.m₁ k N (rhoSepG d L T.m₁)) (hS : S = T.step k hk N₁ ν β p₁)
    (hp : 0 < S.p₁) :
    ∃ (val : ((S.U × Fin N → ℂ) × (S.U × Fin N → ℂ)) → ((S.U × Fin N → ℂ) × (S.U × Fin N → ℂ)) →
        ℂ → (RawData d L (N₁ * L ^ T.m₁) (k + 1) N × (CTorus d L N₁ T.m₁ (k + 1) → Fin N → ℂ)) → ℂ)
      (𝒴 : Finset (Set (CTorus d L N₁ T.m₁ (k + 1))))
      (Tt : Set (CTorus d L N₁ T.m₁ (k + 1)) → ((S.U × Fin N → ℂ) × (S.U × Fin N → ℂ)) →
        ((S.U × Fin N → ℂ) × (S.U × Fin N → ℂ)) → ℂ →
        (RawData d L (N₁ * L ^ T.m₁) (k + 1) N × (CTorus d L N₁ T.m₁ (k + 1) → Fin N → ℂ)) → ℂ),
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
      PhysicalSharpLocEta S (lvCpsiG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2)))) 2 2 (lvRG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2))) p₁) S.a₁
        S.ν T.t (q / S.β) 𝒴 Tt ∧
      DiagCont (fun ψ : S.U × Fin N → ℂ => (ψ, ψ))
        (physXW S (lvCpsiG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2)))) 2 2 (lvRG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2))) p₁))
        (physSΛEta S S.a₁ S.ν T.t (q / S.β)) 2 𝒴 Tt ∧
      (∀ Θ ∈ physSΛEta S S.a₁ S.ν T.t (q / S.β),
        ∃ I : DirectTerms S T.m₀ hp (fun ψ => (ψ, ψ)) p₁ 2
            (S.β * prop33EpsEtaScaled d L N T.m₁ k T.m₀ S.a₁ T.BG T.BG₂ T.κ T.t
              (lvRG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2))) p₁) 0 0 (q / S.β)) (2 * T.κdec - 1) Θ
            (physSΛEta S S.a₁ S.ν T.t (q / S.β))
            (physXW S (lvCpsiG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2)))) 2 2 (lvRG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2))) p₁)) val
            (physAgΘ S) (AgFDirPair S),
          I.𝒴 = 𝒴 ∧ I.T = Tt) ∧
      (rawOf S.D', (0 : CTorus d L N₁ T.m₁ (k + 1) → Fin N → ℂ)) ∈
        physSΛEta S S.a₁ S.ν T.t (q / S.β) ∧
      (∀ g : Fld d L N₁ T.m₁ (k + 1) N, ∑ x, ∑ i, ‖g x i‖ < q →
        (rawOf S.D', fun y i => g y i / (S.β : ℂ)) ∈ physSΛEta S S.a₁ S.ν T.t (q / S.β)) ∧
      (∀ (Y : Set (CTorus d L N₁ T.m₁ (k + 1)))
        (Θ : RawData d L (N₁ * L ^ T.m₁) (k + 1) N × (CTorus d L N₁ T.m₁ (k + 1) → Fin N → ℂ)),
        Θ ∈ physSΛEta S S.a₁ S.ν T.t (q / S.β) → ∀ ψ : S.U × Fin N → ℂ,
        (∀ p, ‖ψ p‖ ≤ p₁) →
        DifferentiableOn ℂ (fun ζ : ℂ => Tt Y (ζ • ψ, ζ • ψ) (ζ • ψ, ζ • ψ) 1 Θ)
          (Metric.ball (0 : ℂ) (3 / 2))) ∧
      𝒴 = (Finset.univ.biUnion fun z : Torus d (N₁ * L ^ T.m₁ * L ^ (k + 1 - (k + 1))) =>
          polyDom S.G' (LocalCover.nbhdF T.m₀ (LocalCover.blockSite k z)) T.m₀ k
            (LocalCover.fam T.m₀ (LocalCover.blockSite k z))) ∪
        (Finset.univ.biUnion fun s : CTorus d L N₁ T.m₁ (k + 1) × Fin N =>
          polyDom S.G' (LocalCover.nbhdF T.m₀ s.1) T.m₀ k (LocalCover.fam T.m₀ s.1)) ∧
      ∃ (F₁ : Torus d (N₁ * L ^ T.m₁ * L ^ (k + 1 - (k + 1))) →
            DecParams S.G' × RawData d L (N₁ * L ^ T.m₁) (k + 1) N → (S.G'.Ω 1 × Fin N → ℂ) × (S.G'.Ω 1 → ℂ))
          (Sol : Torus d (N₁ * L ^ T.m₁ * L ^ (k + 1 - (k + 1))) →
            Dec2.DecParams (coverOf S.G') × Edat (stepG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) N → ((stepG d L N₁ T.m₁ k (rhoSepG d L T.m₁)).Ω 1 × Fin N → ℂ) × ((stepG d L N₁ T.m₁ k (rhoSepG d L T.m₁)).Ω 1 → ℂ)),
        (∀ (z : Torus d (N₁ * L ^ T.m₁ * L ^ (k + 1 - (k + 1)))) (s : DecParams S.G') (D : BgData S.G' N), (∀ P, ‖s P‖ < Real.exp T.κ) →
          InUnionDomainC S.G' (bgC0 d L N) (c7 d L N T.BG T.κ) S.ν D → ∀ (φ : S.G'.Ω 1 × Fin N → ℂ)
            (α : S.G'.Ω 1 → ℂ), IsDecBg S.G' (compWeight L S.a₁) S.ν (rho4 d L N T.BG T.κ) s D φ α →
            F₁ z (s, rawOf D) = (φ, α)) ∧
        (∀ (z : Torus d (N₁ * L ^ T.m₁ * L ^ (k + 1 - (k + 1)))) (p : Dec2.DecParams (coverOf S.G') × Edat (stepG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) N), (∀ P, ‖p.1 P‖ < Real.exp T.κ) →
          StrictDataM (stepG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) N false (2 * (K4 d L N T.BG T.κ * (xiC1 d * T.t))) T.t p.2 →
            (Sol z p).1 = dphi (stepG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) (Dec2.decG (coverOf S.G') (stepG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) (compWeight L S.a₁) S.ν p.1) p.2.2.1 p.2.1
              (pertSource (stepG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) (Sol z p).2 ∧
            Dec2.DecFixed (coverOf S.G') (stepG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) (compWeight L S.a₁) S.ν p.1 false p.2.2.1 p.2.1
              (pertSource (stepG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) (Sol z p).2 ∧
            Small (stepG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) (Sol z p).2 (c6' d L N (famConst d L T.BG₂ T.κ) (gamma1 d / 8)) ∧
            Small (stepG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) (Sol z p).2 (cK2' d L N (famConst d L T.BG₂ T.κ) * T.t) ∧
            SupBounds (stepG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) (Sol z p).1 (cK2' d L N (famConst d L T.BG₂ T.κ) * T.t) ∧
            (∀ δα' : (stepG d L N₁ T.m₁ k (rhoSepG d L T.m₁)).Ω 1 → ℂ, Small (stepG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) δα' (c6' d L N (famConst d L T.BG₂ T.κ) (gamma1 d / 8)) →
              Dec2.DecFixed (coverOf S.G') (stepG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) (compWeight L S.a₁) S.ν p.1 false p.2.2.1 p.2.1
                (pertSource (stepG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol z p).2)) ∧
        ∀ (Y : Set (CTorus d L N₁ T.m₁ (k + 1)))
          (x w : (S.U × Fin N → ℂ) × (S.U × Fin N → ℂ)) (σ : ℂ)
          (Θ : RawData d L (N₁ * L ^ T.m₁) (k + 1) N),
          Tt Y x w σ (Θ, 0) = -(S.β : ℂ) *
            ∑ z : Torus d (N₁ * L ^ T.m₁ * L ^ (k + 1 - (k + 1))), if Y ∈ polyDom S.G'
                (LocalCover.nbhdF T.m₀ (LocalCover.blockSite k z)) T.m₀ k
                (LocalCover.fam T.m₀ (LocalCover.blockSite k z)) then
              rayTerm (dl3 (evTerm
                (fun i : ParIdx S.G' (↑(LocalCover.nbhdF T.m₀ (LocalCover.blockSite k z)) : Set (CTorus d L N₁ T.m₁ (k + 1))) => i.1.1)
                S.G' T.m₀ (X1 S.G' T.m₀ k (LocalCover.fam T.m₀ (LocalCover.blockSite k z)))
                (fun u s => blockEnergyFun S.G' (stepG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) (compWeight L S.a₁) S.ν k z
                  (F₁ z (extParams S.G' (↑(LocalCover.nbhdF T.m₀ (LocalCover.blockSite k z)) : Set (CTorus d L N₁ T.m₁ (k + 1))) s, u.1))
                  (Sol z (extParams S.G' (↑(LocalCover.nbhdF T.m₀ (LocalCover.blockSite k z)) : Set (CTorus d L N₁ T.m₁ (k + 1))) s,
                    flEdat S.G' (stepG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) (F₁ z (extParams S.G' (↑(LocalCover.nbhdF T.m₀ (LocalCover.blockSite k z)) : Set (CTorus d L N₁ T.m₁ (k + 1))) s, u.1))
                      u.1.1 (hatPsiF S.G' S.a₁ S.ν S.hG' ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) (F₁ z)
                        (extParams S.G' (↑(LocalCover.nbhdF T.m₀ (LocalCover.blockSite k z)) : Set (CTorus d L N₁ T.m₁ (k + 1))) s) u.1 u.2))).1
                  (u.1, hatPsiF S.G' S.a₁ S.ν S.hG' ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) (F₁ z)
                    (extParams S.G' (↑(LocalCover.nbhdF T.m₀ (LocalCover.blockSite k z)) : Set (CTorus d L N₁ T.m₁ (k + 1))) s) u.1 u.2)) Y) w.1) taylorWeight x.1 σ Θ
            else 0 := by
  classical
  subst hS
  have h4 := T.m₁_four
  have ht0 := T.t_pos
  have hMX := T.large_block
  have hdm := T.dom_margin
  have hα := T.coer_margin
  have hsmX := T.δc_small
  have hc7 := T.c7_cap
  have g1 := T.t_cap
  have g2 := T.bg0_cap
  have g3 := T.cK2_cap
  have g4 := T.cK2'_cap
  have g5 := T.bg1_cap
  have hκ0 := T.κ0_nonneg
  have hκdec := T.κdec_lower
  have hκ := T.κ_lower
  have h1 := T.κ_one
  have hlog := T.κ_log
  have hxi1 := T.xi_small
  have hν0 : 0 ≤ ν := hνpos.le
  have hβ0 : 0 < β := lt_of_lt_of_le hρ (le_trans (le_max_right _ _) hβρ)
  obtain ⟨R0⟩ := D.ray
  have hcψ0 := D.cψ_pos
  have hr0 := D.r_pos
  have hδ₁ := D.fl_radius
  have hc := D.ray_margin
  have hHB := bgHyp_lvG (k := k) T.hd T.hL (bgR0_le_rhoSepG T.m₁ T.hd T.hL) hν0 hν
  have hSD := dgSetting_lvG (d := d) (L := L) (N₁ := N₁) (k := k) T.hd T.hL h4 hN hν0 hν
  have hC := D.core
  have hD := D.xi
  have hBh := hBh_of_xi (N := N) (Gp := lvTopG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) hHB hνpos
    hC.small1 hC.eps_pos hxi1
  obtain ⟨hV, hF⟩ := D.covers
  have hBh0 : (0 : ℝ) ≤ 1 + 2 / ν := by positivity
  have hη0 : 0 < q / β := div_pos hq0 hβ0
  obtain ⟨val, 𝒴, Tt, hval, hloc, hcont, hI, hrayT, h𝒴, F₁, Sol, hF₁, hSol, hTt⟩ :=
    sourceDirectTerms_slice_ray
    (T.step k hk N₁ ν β p₁)
    (ρ := p₁) (εU := β * prop33EpsEtaScaled d L N T.m₁ k T.m₀ 1 T.BG T.BG₂ T.κ T.t
      (lvRG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2))) p₁) 0 0 (q / β))
    (Rσ := 2) (R₁ := 2) (r := lvRG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2))) p₁) (R := 2)
    (m₀ := T.m₀) (κdec := T.κdec)
    (κ₀ := T.κ0) (Bh := 1 + 2 / ν) (δc := T.δc)
    (cψ := lvCpsiG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2))))
    (jV := fun _ => k) (XV := fun z => LocalCover.cube T.m₀ k (LocalCover.blockSite k z))
    (𝒦XV := fun z => LocalCover.fam T.m₀ (LocalCover.blockSite k z))
    (X₁V := fun z => LocalCover.nbhdF T.m₀ (LocalCover.blockSite k z))
    (jF := fun _ => k) (XF := fun s => LocalCover.cube T.m₀ k s.1)
    (𝒦XF := fun s => LocalCover.fam T.m₀ s.1) (X₁F := fun s => LocalCover.nbhdF T.m₀ s.1)
    (hC := hC) (hconn := hatConn_lvTopG T.hL) (hrow := rowInHat_lvG hk hSD)
    (hκ₀ := hκ0) (hκdec := hκdec) (hκ := hκ) (h1 := h1)
    (hR₁ := by norm_num) (hr := hr0) (hcψ := hcψ0.le) (hMX := hMX) (hdm := hdm) (hα := hα)
    (hsmX := hsmX) (hδ₁ := hδ₁) (ha₁ := one_pos) (H := hHB) (hc7 := hc7) (hR := le_rfl)
    (hRs := g1) (hsmall := g2) (hnum := g3) (hnum' := g4) (hsm := g5)
    (hcovV := fun z => (hV z).1) (hX₁V := fun z => (hV z).2.1)
    (hoptV := fun z => (hV z).2.2.1) (hΔV := fun z => (hV z).2.2.2.1)
    (hlogV := fun _ => hlog) (hZV := fun z => (hV z).2.2.2.2.1)
    (hmarV := fun z => (hV z).2.2.2.2.2.1)
    (hcovF := fun s => (hF s).1) (hX₁F := fun s => (hF s).2.1)
    (hoptF := fun s => (hF s).2.2.1) (hΔF := fun s => (hF s).2.2.2.1)
    (hlogF := fun _ => hlog) (hyF := fun s => (hF s).2.2.2.2)
    (hBh0 := hBh0) (hBh := hBh) (hZν := fun z => (hV z).2.2.2.2.2.2)
    (hN := hLN) (hp := hp) (η := q / β) (hη0 := hη0) (hRσ := by norm_num) (hc := hc)
    (hεb := by
      have hnβ : ‖(((T.step k hk N₁ ν β p₁).β : ℝ) : ℂ)‖ = β := by
        rw [Complex.norm_real]; exact Real.norm_of_nonneg hβ0.le
      rw [hnβ, mul_comm]
      exact le_of_eq rfl)
  exact ⟨val, 𝒴, Tt, hval, hloc, hcont, hI,
    mk_mem_physSΛEta (T.step k hk N₁ ν β p₁) 1 ν T.t hη0.le hD,
    fun g hg => ⟨⟨_, hD, rfl⟩, sourceSlice_mem_restricted_radius hβρ hg hq⟩,
    fun Y Θ hΘ ψ hψ => hrayT Y Θ hΘ ψ fun p => by
      have hp1 := D.ray_margin_scaled hp
      have := hψ p
      have hpp : 0 < p₁ := hp
      nlinarith [norm_nonneg (ψ p), hr0], h𝒴, F₁, Sol, hF₁, hSol, hTt⟩

open Classical in
/-- **The direct terms of the zero class at the shared general tower `T`, on the source slice
`η = q/β`, general `d`, `L`, `N`.**  As `sourceDirectTerms_scale_fromTower_ray_rho` for
`T : StepTowerG d L N κmin` and `D : StepScaleDataG T …`, at the step
`T.step k hk N₁ ν β p₁ = hatStepKG … T.δ`, the block scale `T.m₀` and the block coupling
`β L^{k(d-2)}`.  The expanded function, the domains and the terms are chosen before the chart point
and the source; the hypotheses are `max 1 ρ ≤ β`, `0 < q ≤ ρ`, `L ^ T.m₀ ∣ N₁` and `5 < N₁`.
The last two conjuncts make the terms explicit, as in `sourceDirectTerms_slice_ray`. -/

theorem sourceDirectTerms_scale_fromTowerG_ray_rho {d L N : ℕ} [NeZero L] {κmin : ℝ} (T : StepTowerG d L N κmin)
    (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁] (hLN : L ^ T.m₀ ∣ N₁) (hN : 5 < N₁)
    (ν : ℝ) (hνpos : 0 < ν) (hν : ν * (L : ℝ) ^ (2 * (k + 1)) ≤ 1) (β : ℝ) (ρ : ℝ) (hρ : 0 < ρ) (hβρ : max 1 ρ ≤ β)
    (p₁ : ℝ) (q : ℝ) (hq0 : 0 < q) (hq : q ≤ ρ)
    (D : StepScaleDataG T k hk N₁ ν β p₁)
    (S : StepSetting d L N₁ T.m₁ k N (rhoSepG d L T.m₁)) (hS : S = T.step k hk N₁ ν β p₁)
    (hp : 0 < S.p₁) :
    ∃ (val : ((S.U × Fin N → ℂ) × (S.U × Fin N → ℂ)) → ((S.U × Fin N → ℂ) × (S.U × Fin N → ℂ)) →
        ℂ → (RawData d L (N₁ * L ^ T.m₁) (k + 1) N × (CTorus d L N₁ T.m₁ (k + 1) → Fin N → ℂ)) → ℂ)
      (𝒴 : Finset (Set (CTorus d L N₁ T.m₁ (k + 1))))
      (Tt : Set (CTorus d L N₁ T.m₁ (k + 1)) → ((S.U × Fin N → ℂ) × (S.U × Fin N → ℂ)) →
        ((S.U × Fin N → ℂ) × (S.U × Fin N → ℂ)) → ℂ →
        (RawData d L (N₁ * L ^ T.m₁) (k + 1) N × (CTorus d L N₁ T.m₁ (k + 1) → Fin N → ℂ)) → ℂ),
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
      PhysicalSharpLocEta S (lvCpsiG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2)))) 2 2 (lvRG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2))) p₁) S.a₁
        S.ν T.t (q / S.β) 𝒴 Tt ∧
      DiagCont (fun ψ : S.U × Fin N → ℂ => (ψ, ψ))
        (physXW S (lvCpsiG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2)))) 2 2 (lvRG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2))) p₁))
        (physSΛEta S S.a₁ S.ν T.t (q / S.β)) 2 𝒴 Tt ∧
      (∀ Θ ∈ physSΛEta S S.a₁ S.ν T.t (q / S.β),
        ∃ I : DirectTerms S T.m₀ hp (fun ψ => (ψ, ψ)) p₁ 2
            (S.β * prop33EpsEtaScaled d L N T.m₁ k T.m₀ S.a₁ T.BG T.BG₂ T.κ T.t
              (lvRG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2))) p₁) 0 0 (q / S.β)) (2 * T.κdec - 1) Θ
            (physSΛEta S S.a₁ S.ν T.t (q / S.β))
            (physXW S (lvCpsiG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2)))) 2 2 (lvRG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2))) p₁)) val
            (physAgΘ S) (AgFDirPair S),
          I.𝒴 = 𝒴 ∧ I.T = Tt) ∧
      (rawOf S.D', (0 : CTorus d L N₁ T.m₁ (k + 1) → Fin N → ℂ)) ∈
        physSΛEta S S.a₁ S.ν T.t (q / S.β) ∧
      (∀ g : Fld d L N₁ T.m₁ (k + 1) N, ∑ x, ∑ i, ‖g x i‖ < q →
        (rawOf S.D', fun y i => g y i / (S.β : ℂ)) ∈ physSΛEta S S.a₁ S.ν T.t (q / S.β)) ∧
      (∀ (Y : Set (CTorus d L N₁ T.m₁ (k + 1)))
        (Θ : RawData d L (N₁ * L ^ T.m₁) (k + 1) N × (CTorus d L N₁ T.m₁ (k + 1) → Fin N → ℂ)),
        Θ ∈ physSΛEta S S.a₁ S.ν T.t (q / S.β) → ∀ ψ : S.U × Fin N → ℂ,
        (∀ p, ‖ψ p‖ ≤ 2 / 3 * p₁) →
        DifferentiableOn ℂ (fun ζ : ℂ => Tt Y (ζ • ψ, ζ • ψ) (ζ • ψ, ζ • ψ) 1 Θ)
          (Metric.ball (0 : ℂ) (3 / 2))) ∧
      𝒴 = (Finset.univ.biUnion fun z : Torus d (N₁ * L ^ T.m₁ * L ^ (k + 1 - (k + 1))) =>
          polyDom S.G' (LocalCover.nbhdF T.m₀ (LocalCover.blockSite k z)) T.m₀ k
            (LocalCover.fam T.m₀ (LocalCover.blockSite k z))) ∪
        (Finset.univ.biUnion fun s : CTorus d L N₁ T.m₁ (k + 1) × Fin N =>
          polyDom S.G' (LocalCover.nbhdF T.m₀ s.1) T.m₀ k (LocalCover.fam T.m₀ s.1)) ∧
      ∃ (F₁ : Torus d (N₁ * L ^ T.m₁ * L ^ (k + 1 - (k + 1))) →
            DecParams S.G' × RawData d L (N₁ * L ^ T.m₁) (k + 1) N → (S.G'.Ω 1 × Fin N → ℂ) × (S.G'.Ω 1 → ℂ))
          (Sol : Torus d (N₁ * L ^ T.m₁ * L ^ (k + 1 - (k + 1))) →
            Dec2.DecParams (coverOf S.G') × Edat (stepG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) N → ((stepG d L N₁ T.m₁ k (rhoSepG d L T.m₁)).Ω 1 × Fin N → ℂ) × ((stepG d L N₁ T.m₁ k (rhoSepG d L T.m₁)).Ω 1 → ℂ)),
        (∀ (z : Torus d (N₁ * L ^ T.m₁ * L ^ (k + 1 - (k + 1)))) (s : DecParams S.G') (D : BgData S.G' N), (∀ P, ‖s P‖ < Real.exp T.κ) →
          InUnionDomainC S.G' (bgC0 d L N) (c7 d L N T.BG T.κ) S.ν D → ∀ (φ : S.G'.Ω 1 × Fin N → ℂ)
            (α : S.G'.Ω 1 → ℂ), IsDecBg S.G' (compWeight L S.a₁) S.ν (rho4 d L N T.BG T.κ) s D φ α →
            F₁ z (s, rawOf D) = (φ, α)) ∧
        (∀ (z : Torus d (N₁ * L ^ T.m₁ * L ^ (k + 1 - (k + 1)))) (p : Dec2.DecParams (coverOf S.G') × Edat (stepG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) N), (∀ P, ‖p.1 P‖ < Real.exp T.κ) →
          StrictDataM (stepG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) N false (2 * (K4 d L N T.BG T.κ * (xiC1 d * T.t))) T.t p.2 →
            (Sol z p).1 = dphi (stepG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) (Dec2.decG (coverOf S.G') (stepG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) (compWeight L S.a₁) S.ν p.1) p.2.2.1 p.2.1
              (pertSource (stepG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) (Sol z p).2 ∧
            Dec2.DecFixed (coverOf S.G') (stepG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) (compWeight L S.a₁) S.ν p.1 false p.2.2.1 p.2.1
              (pertSource (stepG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) (Sol z p).2 ∧
            Small (stepG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) (Sol z p).2 (c6' d L N (famConst d L T.BG₂ T.κ) (gamma1 d / 8)) ∧
            Small (stepG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) (Sol z p).2 (cK2' d L N (famConst d L T.BG₂ T.κ) * T.t) ∧
            SupBounds (stepG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) (Sol z p).1 (cK2' d L N (famConst d L T.BG₂ T.κ) * T.t) ∧
            (∀ δα' : (stepG d L N₁ T.m₁ k (rhoSepG d L T.m₁)).Ω 1 → ℂ, Small (stepG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) δα' (c6' d L N (famConst d L T.BG₂ T.κ) (gamma1 d / 8)) →
              Dec2.DecFixed (coverOf S.G') (stepG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) (compWeight L S.a₁) S.ν p.1 false p.2.2.1 p.2.1
                (pertSource (stepG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol z p).2)) ∧
        ∀ (Y : Set (CTorus d L N₁ T.m₁ (k + 1)))
          (x w : (S.U × Fin N → ℂ) × (S.U × Fin N → ℂ)) (σ : ℂ)
          (Θ : RawData d L (N₁ * L ^ T.m₁) (k + 1) N),
          Tt Y x w σ (Θ, 0) = -(S.β : ℂ) *
            ∑ z : Torus d (N₁ * L ^ T.m₁ * L ^ (k + 1 - (k + 1))), if Y ∈ polyDom S.G'
                (LocalCover.nbhdF T.m₀ (LocalCover.blockSite k z)) T.m₀ k
                (LocalCover.fam T.m₀ (LocalCover.blockSite k z)) then
              rayTerm (dl3 (evTerm
                (fun i : ParIdx S.G' (↑(LocalCover.nbhdF T.m₀ (LocalCover.blockSite k z)) : Set (CTorus d L N₁ T.m₁ (k + 1))) => i.1.1)
                S.G' T.m₀ (X1 S.G' T.m₀ k (LocalCover.fam T.m₀ (LocalCover.blockSite k z)))
                (fun u s => blockEnergyFun S.G' (stepG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) (compWeight L S.a₁) S.ν k z
                  (F₁ z (extParams S.G' (↑(LocalCover.nbhdF T.m₀ (LocalCover.blockSite k z)) : Set (CTorus d L N₁ T.m₁ (k + 1))) s, u.1))
                  (Sol z (extParams S.G' (↑(LocalCover.nbhdF T.m₀ (LocalCover.blockSite k z)) : Set (CTorus d L N₁ T.m₁ (k + 1))) s,
                    flEdat S.G' (stepG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) (F₁ z (extParams S.G' (↑(LocalCover.nbhdF T.m₀ (LocalCover.blockSite k z)) : Set (CTorus d L N₁ T.m₁ (k + 1))) s, u.1))
                      u.1.1 (hatPsiF S.G' S.a₁ S.ν S.hG' ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) (F₁ z)
                        (extParams S.G' (↑(LocalCover.nbhdF T.m₀ (LocalCover.blockSite k z)) : Set (CTorus d L N₁ T.m₁ (k + 1))) s) u.1 u.2))).1
                  (u.1, hatPsiF S.G' S.a₁ S.ν S.hG' ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) (F₁ z)
                    (extParams S.G' (↑(LocalCover.nbhdF T.m₀ (LocalCover.blockSite k z)) : Set (CTorus d L N₁ T.m₁ (k + 1))) s) u.1 u.2)) Y) w.1) taylorWeight x.1 σ Θ
            else 0 := by
  classical
  refine (sourceDirectTerms_scale_fromTowerG_ray_full_rho T k hk N₁ hLN hN ν hνpos hν β ρ hρ hβρ p₁ q hq0 hq D S hS hp).imp fun _ => Exists.imp fun _ => Exists.imp fun _ h => ?_
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1,
    fun Y Θ hΘ ψ hψ => h.2.2.2.2.2.2.1 Y Θ hΘ ψ fun p => by
      have := hψ p
      have hpp : 0 < p₁ := by subst hS; exact hp
      linarith, h.2.2.2.2.2.2.2⟩

open Classical in
/-- **The direct terms of the zero class at the shared tower `T`, on the source slice
`η = q/β`.**  For `S = T.step k hk N₁ ν β p₁` and `D : StepScaleData T …`, the conclusion of
`sourceDirectTerms_scale` at the constants `T.m₁, T.t, T.δ, T.BG, T.BG₂, T.κ, T.κ0, T.κdec`:
there are `val`, `𝒴`, `Tt`, chosen before the chart point and the source, with the formula for
`val`, sharp locality and diagonal continuity on the slice, a `DirectTerms` instance with domains
`𝒴` and terms `Tt` at every point of the slice, and the slice contains `(rawOf S.D', 0)` and
`(rawOf S.D', g/β)` for `∑ |g| < q`.  The hypotheses are `max 1 ρ ≤ β` and `0 < q ≤ ρ`; there is no
other threshold.

The last conjunct is the differentiability of the terms `Tt` along the complex hat ray `ζ ↦ ζ ψ̂` on
`‖ζ‖ < 3/2`, at every point of the slice and every hat field with `‖ψ̂ p‖ ≤ (2/3) p₁` (so the ray
stays in `‖·‖ < p₁`); the margin is discharged by `StepScaleData.ray_margin`. -/

theorem sourceDirectTerms_scale_fromTower_ray_rho {κmin : ℝ} (T : StepTower κmin)
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
        (∀ p, ‖ψ p‖ ≤ 2 / 3 * p₁) →
        DifferentiableOn ℂ (fun ζ : ℂ => Tt Y (ζ • ψ, ζ • ψ) (ζ • ψ, ζ • ψ) 1 Θ)
          (Metric.ball (0 : ℂ) (3 / 2)) := by
  classical
  subst hS
  have hp' : 0 < (T.toG.step k hk N₁ ν β p₁).p₁ := hp
  have G := sourceDirectTerms_scale_fromTowerG_ray_rho T.toG k hk N₁ (by simpa using h3N) hN ν
    hνpos (by simpa using hν) β ρ hρ hβρ p₁ q hq0 hq (StepTower.scaleDataG_of_fixed T D)
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
/-- **The direct terms of the zero class at the shared tower `T`, on the source slice
`η = q/β`.**  For `S = T.step k hk N₁ ν β p₁` and `D : StepScaleData T …`, the conclusion of
`sourceDirectTerms_scale` at the constants `T.m₁, T.t, T.δ, T.BG, T.BG₂, T.κ, T.κ0, T.κdec`:
there are `val`, `𝒴`, `Tt`, chosen before the chart point and the source, with the formula for
`val`, sharp locality and diagonal continuity on the slice, a `DirectTerms` instance with domains
`𝒴` and terms `Tt` at every point of the slice, and the slice contains `(rawOf S.D', 0)` and
`(rawOf S.D', g/β)` for `∑ |g| < q`.  The hypotheses are `1 ≤ β` and `0 < q ≤ 1`; there is no
other threshold.

The last conjunct is the differentiability of the terms `Tt` along the complex hat ray `ζ ↦ ζ ψ̂` on
`‖ζ‖ < 3/2`, at every point of the slice and every hat field with `‖ψ̂ p‖ ≤ (2/3) p₁` (so the ray
stays in `‖·‖ < p₁`); the margin is discharged by `StepScaleData.ray_margin`. -/

theorem sourceDirectTerms_scale_fromTower_ray {κmin : ℝ} (T : StepTower κmin)
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
        (∀ p, ‖ψ p‖ ≤ 2 / 3 * p₁) →
        DifferentiableOn ℂ (fun ζ : ℂ => Tt Y (ζ • ψ, ζ • ψ) (ζ • ψ, ζ • ψ) 1 Θ)
          (Metric.ball (0 : ℂ) (3 / 2)) := by
  exact sourceDirectTerms_scale_fromTower_ray_rho T k hk N₁ h3N hN ν hνpos hν β 1 one_pos (by rw [max_self]; exact hβ1) p₁ q hq0 hq D S hS hp


/-- **The direct terms of the zero class at the shared tower `T`, on the source slice
`η = q/β`.**  For `S = T.step k hk N₁ ν β p₁` and `D : StepScaleData T …`, the conclusion of
`sourceDirectTerms_scale` at the constants `T.m₁, T.t, T.δ, T.BG, T.BG₂, T.κ, T.κ0, T.κdec`:
there are `val`, `𝒴`, `Tt`, chosen before the chart point and the source, with the formula for
`val`, sharp locality and diagonal continuity on the slice, a `DirectTerms` instance with domains
`𝒴` and terms `Tt` at every point of the slice, and the slice contains `(rawOf S.D', 0)` and
`(rawOf S.D', g/β)` for `∑ |g| < q`.  The hypotheses are `max 1 ρ ≤ β` and `0 < q ≤ ρ`; there is no
other threshold. -/
theorem sourceDirectTerms_scale_fromTower_rho {κmin : ℝ} (T : StepTower κmin)
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
      ∀ g : Fld 3 3 N₁ T.m₁ (k + 1) 2, ∑ x, ∑ i, ‖g x i‖ < q →
        (rawOf S.D', fun y i => g y i / (S.β : ℂ)) ∈ physSΛEta S S.a₁ S.ν T.t (q / S.β) := by
  classical
  exact (sourceDirectTerms_scale_fromTower_ray_rho T k hk N₁ h3N hN ν hνpos hν β ρ hρ hβρ p₁ q hq0 hq D S hS hp).imp fun _ => Exists.imp fun _ => Exists.imp fun _ h =>
    ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1⟩

/-- **The direct terms of the zero class at the shared tower `T`, on the source slice
`η = q/β`.**  For `S = T.step k hk N₁ ν β p₁` and `D : StepScaleData T …`, the conclusion of
`sourceDirectTerms_scale` at the constants `T.m₁, T.t, T.δ, T.BG, T.BG₂, T.κ, T.κ0, T.κdec`:
there are `val`, `𝒴`, `Tt`, chosen before the chart point and the source, with the formula for
`val`, sharp locality and diagonal continuity on the slice, a `DirectTerms` instance with domains
`𝒴` and terms `Tt` at every point of the slice, and the slice contains `(rawOf S.D', 0)` and
`(rawOf S.D', g/β)` for `∑ |g| < q`.  The hypotheses are `1 ≤ β` and `0 < q ≤ 1`; there is no
other threshold. -/
theorem sourceDirectTerms_scale_fromTower {κmin : ℝ} (T : StepTower κmin)
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
      ∀ g : Fld 3 3 N₁ T.m₁ (k + 1) 2, ∑ x, ∑ i, ‖g x i‖ < q →
        (rawOf S.D', fun y i => g y i / (S.β : ℂ)) ∈ physSΛEta S S.a₁ S.ν T.t (q / S.β) := by
  exact sourceDirectTerms_scale_fromTower_rho T k hk N₁ h3N hN ν hνpos hν β 1 one_pos (by rw [max_self]; exact hβ1) p₁ q hq0 hq D S hS hp


end Balaban.Inhabited
