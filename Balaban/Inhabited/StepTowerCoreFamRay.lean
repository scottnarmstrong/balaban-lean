/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.StepTowerCoreFamPin
public import Balaban.Inhabited.E0CoeffFamilyRotTower
public import Balaban.Polymer.TwoTorusDirectTerms
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Uniqueness of the zero-source direct terms of the core

For two pairs of pinned maps `(F₂, Sol₂)`, `(F₂', Sol₂')` of a step of the general tower, two
families `Tt`, `Tt'` of direct terms whose values at zero source are the explicit ray terms of the
core agree at the datum `rawOf D₀` of the chart, the hat variable `ψ` of sup norm at most `p₁` and
`‖u‖ < 2` (`directTerm_unique_tower`).
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation
  Balaban.Localization Balaban.Inhabited.LevelStep Balaban.Polymer.TwoTorusStep Finset Matrix

section General

variable {d L N N₁ m₁ k : ℕ} [NeZero L] [NeZero N₁] {ϱ ϱm : ℝ}

/-- **The ray terms of the block expansion agree for two pinned pairs.** -/
theorem rayTermHat_unique_of_ray (S : StepSetting d L N₁ m₁ k N ϱ)
    {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}
    {c BG κ Kc Cx c₂ BG₂ eps : ℝ}
    (hC : FlCore N S.G' Hm S.a₁ S.ν c BG κ eps Kc Cx c₂ BG₂ eps) (hk : 1 ≤ k)
    (hG : IsLevel Hm k)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δc : ℝ}
    (hmar : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4) {cψ' r p : ℝ} (hcψ : 0 ≤ cψ') (hr : 0 < r)
    (hray : (2 * 2 + r) * p < cψ')
    (hfl : Real.sqrt N * (‖(((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ))‖ *
      (covSupConstC d L N (compWeight L S.a₁ k) κ * cψ')) < eps)
    {X₁f : Finset (CTorus d L N₁ m₁ (k + 1))} {m₀ : ℕ} {X₁ : Set (CTorus d L N₁ m₁ (k + 1))}
    {F₁ F₁' : DecParams S.G' × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      (S.G'.Ω 1 × Fin N → ℂ) × (S.G'.Ω 1 → ℂ)}
    (hF₁ : ∀ (s : DecParams S.G') (D' : BgData S.G' N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC S.G' (bgC0 d L N) (c7 d L N BG κ) S.ν D' → ∀ (φ : S.G'.Ω 1 × Fin N → ℂ)
        (α : S.G'.Ω 1 → ℂ), IsDecBg S.G' (compWeight L S.a₁) S.ν (rho4 d L N BG κ) s D' φ α →
        F₁ (s, rawOf D') = (φ, α))
    (hF₁' : ∀ (s : DecParams S.G') (D' : BgData S.G' N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC S.G' (bgC0 d L N) (c7 d L N BG κ) S.ν D' → ∀ (φ : S.G'.Ω 1 × Fin N → ℂ)
        (α : S.G'.Ω 1 → ℂ), IsDecBg S.G' (compWeight L S.a₁) S.ν (rho4 d L N BG κ) s D' φ α →
        F₁' (s, rawOf D') = (φ, α))
    {Sol Sol' : Dec2.DecParams (coverOf S.G') × Edat Hm N → (Hm.Ω 1 × Fin N → ℂ) × (Hm.Ω 1 → ℂ)}
    (hSol : SolSpec S.G' Hm S.a₁ S.ν BG BG₂ κ eps eps Sol)
    (hSol' : SolSpec S.G' Hm S.a₁ S.ν BG BG₂ κ eps eps Sol')
    {En : ((S.G'.Ω 1 × Fin N → ℂ) × (S.G'.Ω 1 → ℂ)) → (Hm.Ω 1 × Fin N → ℂ) →
      RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) → ℂ}
    (Y : Set (CTorus d L N₁ m₁ (k + 1))) {D₀ : BgData S.G' N}
    (hD₀ : XiCData S.G' (compWeight L S.a₁) S.ν (k + 1) 1 eps D₀)
    {ψ : unitPts S.G' × Fin N → ℂ} (hψ : ∀ q, ‖ψ q‖ ≤ p) {u : ℂ} (hu : ‖u‖ < 2) :
    rayTerm (dl3 (evTerm (fun i : ParIdx S.G'
        (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) => i.1.1) S.G' m₀ X₁
      (fun u s => fnOfDec S.G' Hm X₁f F₁ Sol En
        (u.1, hatPsiF S.G' S.a₁ S.ν S.hG'
          (((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) F₁
          (extParams S.G' (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s) u.1 u.2) s) Y) ψ)
      taylorWeight ψ u (rawOf D₀) =
    rayTerm (dl3 (evTerm (fun i : ParIdx S.G'
        (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) => i.1.1) S.G' m₀ X₁
      (fun u s => fnOfDec S.G' Hm X₁f F₁' Sol' En
        (u.1, hatPsiF S.G' S.a₁ S.ν S.hG'
          (((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) F₁'
          (extParams S.G' (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s) u.1 u.2) s) Y) ψ)
      taylorWeight ψ u (rawOf D₀) := by
  refine (rayTerm_dl3_eq_of_line _ _ taylorWeight ψ ψ ψ ψ u (rawOf D₀) (rawOf D₀) fun t ht τ hτ => ?_).symm
  refine (evTermHat_unique hC hk hG S.hG' _ hcψ hMX hmar hα hsm hfl hF₁ hF₁' hSol hSol' (Φ := En)
    Y hD₀ (ψh := (u * (t : ℂ)) • ψ + τ • ψ) ?_).symm
  intro q
  have h1 : ‖u * (t : ℂ) + τ‖ ≤ 3 := by
    have : ‖u * (t : ℂ)‖ ≤ 2 := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht.1]
      nlinarith [norm_nonneg u, ht.2, ht.1]
    have := norm_add_le (u * (t : ℂ)) τ
    linarith
  have key : ‖((u * (t : ℂ)) • ψ + τ • ψ) q‖ = ‖u * (t : ℂ) + τ‖ * ‖ψ q‖ := by
    simp [← add_mul]
  have hp0 : 0 ≤ p := (norm_nonneg _).trans (hψ q)
  rw [key]
  calc ‖u * (t : ℂ) + τ‖ * ‖ψ q‖ ≤ 3 * p := mul_le_mul h1 (hψ q) (norm_nonneg _) (by norm_num)
    _ ≤ (2 * 2 + r) * p := by nlinarith
    _ ≤ _ := hray.le

end General

variable {d L N : ℕ} [NeZero L] {κmin : ℝ}

/-- **The zero-source direct terms of the core agree for two pinned pairs, at the general tower.**
For families `Tt`, `Tt'` whose values at zero source are the explicit ray terms of the core with
the pairs `(F₂, Sol₂)`, `(F₂', Sol₂')`, the values at the datum `rawOf D₀` of the chart and the hat
variable `ψ` of sup norm at most `p₁`, `‖u‖ < 2`, coincide. -/
theorem directTerm_unique_tower (T : StepTowerG d L N κmin) {k : ℕ} (hk : 1 ≤ k) {N₁ : ℕ}
    [NeZero N₁] {ν β p₁ : ℝ} (D : StepScaleDataG T k hk N₁ ν β p₁) (_hp : 0 < p₁)
    (S : StepSetting d L N₁ T.m₁ k N (rhoSepG d L T.m₁))
    (hS : S = T.step k hk N₁ ν β p₁)
    (F₂ F₂' : Torus d (N₁ * L ^ T.m₁ * L ^ (k + 1 - (k + 1))) →
      DecParams S.G' × RawData d L (N₁ * L ^ T.m₁) (k + 1) N →
        (S.G'.Ω 1 × Fin N → ℂ) × (S.G'.Ω 1 → ℂ))
    (Sol₂ Sol₂' : Torus d (N₁ * L ^ T.m₁ * L ^ (k + 1 - (k + 1))) →
      Dec2.DecParams (coverOf S.G') × Edat (stepG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) N →
        ((stepG d L N₁ T.m₁ k (rhoSepG d L T.m₁)).Ω 1 × Fin N → ℂ) × ((stepG d L N₁ T.m₁ k (rhoSepG d L T.m₁)).Ω 1 → ℂ))
    (hF₂ : ∀ (z : Torus d (N₁ * L ^ T.m₁ * L ^ (k + 1 - (k + 1)))) (s : DecParams S.G')
      (D' : BgData S.G' N), (∀ P, ‖s P‖ < Real.exp T.κ) →
      InUnionDomainC S.G' (bgC0 d L N) (c7 d L N T.BG T.κ) S.ν D' → ∀ (φ : S.G'.Ω 1 × Fin N → ℂ)
        (α : S.G'.Ω 1 → ℂ), IsDecBg S.G' (compWeight L S.a₁) S.ν (rho4 d L N T.BG T.κ) s D' φ α →
        F₂ z (s, rawOf D') = (φ, α))
    (hF₂' : ∀ (z : Torus d (N₁ * L ^ T.m₁ * L ^ (k + 1 - (k + 1)))) (s : DecParams S.G')
      (D' : BgData S.G' N), (∀ P, ‖s P‖ < Real.exp T.κ) →
      InUnionDomainC S.G' (bgC0 d L N) (c7 d L N T.BG T.κ) S.ν D' → ∀ (φ : S.G'.Ω 1 × Fin N → ℂ)
        (α : S.G'.Ω 1 → ℂ), IsDecBg S.G' (compWeight L S.a₁) S.ν (rho4 d L N T.BG T.κ) s D' φ α →
        F₂' z (s, rawOf D') = (φ, α))
    (hSol₂ : ∀ z : Torus d (N₁ * L ^ T.m₁ * L ^ (k + 1 - (k + 1))),
      SolSpec S.G' (stepG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) S.a₁ S.ν T.BG T.BG₂ T.κ T.t T.t (Sol₂ z))
    (hSol₂' : ∀ z : Torus d (N₁ * L ^ T.m₁ * L ^ (k + 1 - (k + 1))),
      SolSpec S.G' (stepG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) S.a₁ S.ν T.BG T.BG₂ T.κ T.t T.t (Sol₂' z))
    (Tt Tt' : Set (CTorus d L N₁ T.m₁ (k + 1)) → (S.U × Fin N → ℂ) × (S.U × Fin N → ℂ) →
      (S.U × Fin N → ℂ) × (S.U × Fin N → ℂ) → ℂ →
      RawData d L (N₁ * L ^ T.m₁) (k + 1) N × (CTorus d L N₁ T.m₁ (k + 1) → Fin N → ℂ) → ℂ)
        (hT : ∀ (Y : Set (CTorus d L N₁ T.m₁ (k + 1)))
                (x w : (S.U × Fin N → ℂ) × (S.U × Fin N → ℂ)) (σ : ℂ)
                (Θ : RawData d L (N₁ * L ^ T.m₁) (k + 1) N),
                Tt Y x w σ (Θ, 0) = -(S.β : ℂ) *
                  ∑ z : Torus d (N₁ * L ^ T.m₁ * L ^ (k + 1 - (k + 1))), if Y ∈ polyDom S.G'
                      (LocalCover.nbhdF 1 (LocalCover.blockSite k z)) 1 k
                      (LocalCover.fam 1 (LocalCover.blockSite k z)) then
                    rayTerm (dl3 (evTerm
                      (fun i : ParIdx S.G' (↑(LocalCover.nbhdF 1 (LocalCover.blockSite k z)) : Set (CTorus d L N₁ T.m₁ (k + 1))) => i.1.1)
                      S.G' 1 (X1 S.G' 1 k (LocalCover.fam 1 (LocalCover.blockSite k z)))
                      (fun u s => blockEnergyFun S.G' (stepG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) (compWeight L S.a₁) S.ν k z
                        (F₂ z (extParams S.G' (↑(LocalCover.nbhdF 1 (LocalCover.blockSite k z)) : Set (CTorus d L N₁ T.m₁ (k + 1))) s, u.1))
                        (Sol₂ z (extParams S.G' (↑(LocalCover.nbhdF 1 (LocalCover.blockSite k z)) : Set (CTorus d L N₁ T.m₁ (k + 1))) s,
                          flEdat S.G' (stepG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) (F₂ z (extParams S.G' (↑(LocalCover.nbhdF 1 (LocalCover.blockSite k z)) : Set (CTorus d L N₁ T.m₁ (k + 1))) s, u.1))
                            u.1.1 (hatPsiF S.G' S.a₁ S.ν S.hG' ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) (F₂ z)
                              (extParams S.G' (↑(LocalCover.nbhdF 1 (LocalCover.blockSite k z)) : Set (CTorus d L N₁ T.m₁ (k + 1))) s) u.1 u.2))).1
                        (u.1, hatPsiF S.G' S.a₁ S.ν S.hG' ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) (F₂ z)
                          (extParams S.G' (↑(LocalCover.nbhdF 1 (LocalCover.blockSite k z)) : Set (CTorus d L N₁ T.m₁ (k + 1))) s) u.1 u.2)) Y) w.1) taylorWeight x.1 σ Θ
                  else 0)
        (hT' : ∀ (Y : Set (CTorus d L N₁ T.m₁ (k + 1)))
                (x w : (S.U × Fin N → ℂ) × (S.U × Fin N → ℂ)) (σ : ℂ)
                (Θ : RawData d L (N₁ * L ^ T.m₁) (k + 1) N),
                Tt' Y x w σ (Θ, 0) = -(S.β : ℂ) *
                  ∑ z : Torus d (N₁ * L ^ T.m₁ * L ^ (k + 1 - (k + 1))), if Y ∈ polyDom S.G'
                      (LocalCover.nbhdF 1 (LocalCover.blockSite k z)) 1 k
                      (LocalCover.fam 1 (LocalCover.blockSite k z)) then
                    rayTerm (dl3 (evTerm
                      (fun i : ParIdx S.G' (↑(LocalCover.nbhdF 1 (LocalCover.blockSite k z)) : Set (CTorus d L N₁ T.m₁ (k + 1))) => i.1.1)
                      S.G' 1 (X1 S.G' 1 k (LocalCover.fam 1 (LocalCover.blockSite k z)))
                      (fun u s => blockEnergyFun S.G' (stepG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) (compWeight L S.a₁) S.ν k z
                        (F₂' z (extParams S.G' (↑(LocalCover.nbhdF 1 (LocalCover.blockSite k z)) : Set (CTorus d L N₁ T.m₁ (k + 1))) s, u.1))
                        (Sol₂' z (extParams S.G' (↑(LocalCover.nbhdF 1 (LocalCover.blockSite k z)) : Set (CTorus d L N₁ T.m₁ (k + 1))) s,
                          flEdat S.G' (stepG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) (F₂' z (extParams S.G' (↑(LocalCover.nbhdF 1 (LocalCover.blockSite k z)) : Set (CTorus d L N₁ T.m₁ (k + 1))) s, u.1))
                            u.1.1 (hatPsiF S.G' S.a₁ S.ν S.hG' ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) (F₂' z)
                              (extParams S.G' (↑(LocalCover.nbhdF 1 (LocalCover.blockSite k z)) : Set (CTorus d L N₁ T.m₁ (k + 1))) s) u.1 u.2))).1
                        (u.1, hatPsiF S.G' S.a₁ S.ν S.hG' ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) (F₂' z)
                          (extParams S.G' (↑(LocalCover.nbhdF 1 (LocalCover.blockSite k z)) : Set (CTorus d L N₁ T.m₁ (k + 1))) s) u.1 u.2)) Y) w.1) taylorWeight x.1 σ Θ
                  else 0)
    (Y : Set (CTorus d L N₁ T.m₁ (k + 1)))
    {D₀ : BgData S.G' N}
    (hD₀ : XiCData S.G' (compWeight L S.a₁) S.ν (k + 1) 1 T.t D₀)
    {ψ : S.U × Fin N → ℂ} (hψ : ∀ q, ‖ψ q‖ ≤ p₁) {u : ℂ} (hu : ‖u‖ < 2) :
    Tt Y (ψ, ψ) (ψ, ψ) u (rawOf D₀, 0) = Tt' Y (ψ, ψ) (ψ, ψ) u (rawOf D₀, 0) := by
  subst hS
  rw [hT, hT']
  refine congrArg (fun w => -((T.step k hk N₁ ν β p₁).β : ℂ) * w)
    (Finset.sum_congr rfl fun z _ => ?_)
  split_ifs with hz
  · exact rayTermHat_unique_of_ray (T.step k hk N₁ ν β p₁) D.core hk
      (T.step k hk N₁ ν β p₁).hG T.large_block T.dom_margin T.coer_margin T.δc_small
      D.cψ_pos.le D.r_pos D.ray_margin D.fl_radius (hF₂ z) (hF₂' z) (hSol₂ z) (hSol₂' z)
      (En := blockEnergyFun (T.step k hk N₁ ν β p₁).G'
        (stepG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) (compWeight L (T.step k hk N₁ ν β p₁).a₁)
        (T.step k hk N₁ ν β p₁).ν k z) Y hD₀ hψ hu
  · rfl

end Balaban.Inhabited
