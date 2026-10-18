/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.E0CoeffFamilyRotAct
public import Balaban.Inhabited.StepScaleDataG
public import Balaban.Fluctuation.Prop33SymmEnergy
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Spin covariance of the ray terms of the block expansion at the general tower

`rayTermHat_rot_tower` is `rayTermHat_rot` for the objects of a step of the general tower `T` with
scale data `D`, for the hat variable `ψ` of sup norm at most `p₁` on the ray `u ψ` with `‖u‖ < 2`
(the ray data of `D` give room for the direction `ψ`).
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation
  Balaban.Localization Balaban.Inhabited.LevelStep Finset Matrix

variable {d L N : ℕ} [NeZero L] {κmin : ℝ}

/-- **Spin covariance of the ray terms of the block expansion at the general tower.** -/
theorem rayTermHat_rot_tower (T : StepTowerG d L N κmin) {k : ℕ} (hk : 1 ≤ k) {N₁ : ℕ}
    [NeZero N₁] {ν β p₁ : ℝ} (D : StepScaleDataG T k hk N₁ ν β p₁) (hp : 0 < p₁)
    {X₁f : Finset (CTorus d L N₁ T.m₁ (k + 1))} {m₀ : ℕ}
    {X₁ : Set (CTorus d L N₁ T.m₁ (k + 1))}
    {F₁ : DecParams (T.step k hk N₁ ν β p₁).G' × RawData d L (N₁ * L ^ T.m₁) (k + 1) N →
      ((T.step k hk N₁ ν β p₁).G'.Ω 1 × Fin N → ℂ) × ((T.step k hk N₁ ν β p₁).G'.Ω 1 → ℂ)}
    (hF₁ : ∀ (s : DecParams (T.step k hk N₁ ν β p₁).G') (D' : BgData (T.step k hk N₁ ν β p₁).G' N),
      (∀ P, ‖s P‖ < Real.exp T.κ) →
      InUnionDomainC (T.step k hk N₁ ν β p₁).G' (bgC0 d L N) (c7 d L N T.BG T.κ)
        (T.step k hk N₁ ν β p₁).ν D' → ∀ (φ : (T.step k hk N₁ ν β p₁).G'.Ω 1 × Fin N → ℂ)
        (α : (T.step k hk N₁ ν β p₁).G'.Ω 1 → ℂ),
        IsDecBg (T.step k hk N₁ ν β p₁).G' (compWeight L (T.step k hk N₁ ν β p₁).a₁)
          (T.step k hk N₁ ν β p₁).ν (rho4 d L N T.BG T.κ) s D' φ α → F₁ (s, rawOf D') = (φ, α))
    {Sol : Dec2.DecParams (coverOf (T.step k hk N₁ ν β p₁).G') ×
        Edat (stepG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) N →
      ((stepG d L N₁ T.m₁ k (rhoSepG d L T.m₁)).Ω 1 × Fin N → ℂ) ×
        ((stepG d L N₁ T.m₁ k (rhoSepG d L T.m₁)).Ω 1 → ℂ)}
    (hSol : SolSpec (T.step k hk N₁ ν β p₁).G' (stepG d L N₁ T.m₁ k (rhoSepG d L T.m₁))
      (T.step k hk N₁ ν β p₁).a₁ (T.step k hk N₁ ν β p₁).ν T.BG T.BG₂ T.κ T.t T.t Sol)
    {Q : Matrix (Fin N) (Fin N) ℝ} (hQ : Qᵀ * Q = 1) (z : Torus d (N₁ * L ^ T.m₁ * L ^ (k + 1 - (k + 1))))
    (Y : Set (CTorus d L N₁ T.m₁ (k + 1)))
    {D₀ : BgData (T.step k hk N₁ ν β p₁).G' N}
    (hD₀ : XiCData (T.step k hk N₁ ν β p₁).G' (compWeight L (T.step k hk N₁ ν β p₁).a₁)
      (T.step k hk N₁ ν β p₁).ν (k + 1) 1 T.t D₀)
    {ψ : unitPts (T.step k hk N₁ ν β p₁).G' × Fin N → ℂ} (hψ : ∀ q, ‖ψ q‖ ≤ p₁) {u : ℂ} (hu : ‖u‖ < 2) :
    rayTerm (dl3 (evTerm (fun i : ParIdx (T.step k hk N₁ ν β p₁).G'
        (↑X₁f : Set (CTorus d L N₁ T.m₁ (k + 1))) => i.1.1) (T.step k hk N₁ ν β p₁).G' m₀ X₁
      (fun u s => fnOfDec (T.step k hk N₁ ν β p₁).G' (stepG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) X₁f
        F₁ Sol (blockEnergyFun (T.step k hk N₁ ν β p₁).G'
          (stepG d L N₁ T.m₁ k (rhoSepG d L T.m₁))
          (compWeight L (T.step k hk N₁ ν β p₁).a₁) (T.step k hk N₁ ν β p₁).ν k z)
        (u.1, hatPsiF (T.step k hk N₁ ν β p₁).G' (T.step k hk N₁ ν β p₁).a₁
          (T.step k hk N₁ ν β p₁).ν (T.step k hk N₁ ν β p₁).hG'
          ((((T.step k hk N₁ ν β p₁).betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) F₁
          (extParams (T.step k hk N₁ ν β p₁).G' (↑X₁f : Set (CTorus d L N₁ T.m₁ (k + 1))) s)
          u.1 u.2) s) Y) (rotFld (cmat Q) ψ)) taylorWeight (rotFld (cmat Q) ψ) u
      (rotRaw (cmat Q) (rawOf D₀)) =
    rayTerm (dl3 (evTerm (fun i : ParIdx (T.step k hk N₁ ν β p₁).G'
        (↑X₁f : Set (CTorus d L N₁ T.m₁ (k + 1))) => i.1.1) (T.step k hk N₁ ν β p₁).G' m₀ X₁
      (fun u s => fnOfDec (T.step k hk N₁ ν β p₁).G' (stepG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) X₁f
        F₁ Sol (blockEnergyFun (T.step k hk N₁ ν β p₁).G'
          (stepG d L N₁ T.m₁ k (rhoSepG d L T.m₁))
          (compWeight L (T.step k hk N₁ ν β p₁).a₁) (T.step k hk N₁ ν β p₁).ν k z)
        (u.1, hatPsiF (T.step k hk N₁ ν β p₁).G' (T.step k hk N₁ ν β p₁).a₁
          (T.step k hk N₁ ν β p₁).ν (T.step k hk N₁ ν β p₁).hG'
          ((((T.step k hk N₁ ν β p₁).betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) F₁
          (extParams (T.step k hk N₁ ν β p₁).G' (↑X₁f : Set (CTorus d L N₁ T.m₁ (k + 1))) s)
          u.1 u.2) s) Y) ψ) taylorWeight ψ u (rawOf D₀) := by
  have hQ' : (cmat Q)ᵀ * cmat Q = 1 := (isRealOrth_ofReal hQ).1
  refine rayTermHat_rot D.core hk (T.step k hk N₁ ν β p₁).hG (T.step k hk N₁ ν β p₁).hG' _
    D.cψ_pos.le T.large_block T.dom_margin T.coer_margin T.δc_small D.fl_radius hF₁ hSol hQ
    (fun bg δφ u' => energyBlock_rot hQ' _ _ k bg.2 δφ u'.2 z) Y hD₀ D.r_pos ?_
  intro t ht τ hτ q
  have h1 : ‖u * (t : ℂ) + τ‖ ≤ 2 + lvRG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2))) p₁ := by
    refine (norm_add_le _ _).trans (add_le_add ?_ hτ)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht.1]
    nlinarith [norm_nonneg u, ht.2, ht.1]
  have hr := D.r_pos
  have key : ∀ {ι : Type} (ψ : ι → ℂ) (q : ι) (a b : ℂ),
      ‖(a • ψ + b • ψ) q‖ = ‖a + b‖ * ‖ψ q‖ := by
    intro ι ψ q a b
    simp [← add_mul, norm_mul]
  refine (le_of_eq (key _ q _ _)).trans ?_
  calc ‖u * (t : ℂ) + τ‖ * ‖ψ q‖
      ≤ (2 + lvRG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2))) p₁) * p₁ :=
        mul_le_mul h1 (hψ q) (norm_nonneg _) (by positivity)
    _ ≤ (2 * 2 + lvRG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2))) p₁) * p₁ := by nlinarith
    _ ≤ _ := D.ray_margin.le

end Balaban.Inhabited
