/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.E0CoeffFamilyRotMarkG
public import Balaban.Inhabited.StepScaleDataG
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Spin covariance of the mark family at the general tower

`e1MarkGParamG_rot_tower` is `e1MarkGParamG_rot` for the step `T.step k hk N₁ ν β p₁` of the general
tower with scale data `D`; the radius condition on the marks of the disc `‖u‖ < 17/16` follows
from the fluctuation radius and the ray margin of `D`.
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation
  Balaban.Localization Balaban.Inhabited.LevelStep Matrix

/-- **The marks of the disc `‖u‖ < 17/16` are admissible for the hat radius `p₁`.** -/
theorem markRadius_of_ray {X cψ p₁ r t : ℝ} (hp : 0 ≤ p₁) (hr : 0 < r) (ht : 0 < t)
    (hray : (2 * 2 + r) * p₁ < cψ) (hfl : X * cψ < t) {u : ℂ} (hu : ‖u‖ < (17 / 16 : ℝ)) :
    (‖u‖ + ‖(0 : ℂ)‖) * (X * p₁) < t := by
  simp only [norm_zero, add_zero]
  rcases le_or_gt X 0 with hX | hX
  · have : ‖u‖ * (X * p₁) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (norm_nonneg _) (mul_nonpos_of_nonpos_of_nonneg hX hp)
    linarith
  · have h1 : 4 * p₁ < cψ := by nlinarith
    have h2 : X * p₁ * 4 ≤ X * cψ := by nlinarith
    have h3 : ‖u‖ * (X * p₁) ≤ 17 / 16 * (X * p₁) :=
      mul_le_mul_of_nonneg_right hu.le (by positivity)
    nlinarith [mul_nonneg hX.le hp]

variable {d L N : ℕ} [NeZero L] {κmin : ℝ}

/-- **Spin covariance of the mark family at the general tower.** -/
theorem e1MarkGParamG_rot_tower (T : StepTowerG d L N κmin) {k : ℕ} (hk : 1 ≤ k) {N₁ : ℕ}
    [NeZero N₁] {ν β p₁ : ℝ} (D : StepScaleDataG T k hk N₁ ν β p₁)
    (S : StepSetting d L N₁ T.m₁ k N (rhoSepG d L T.m₁)) (hS : S = T.step k hk N₁ ν β p₁)
    (hp : 0 < S.p₁)
    (F₁ : Torus d (N₁ * L ^ T.m₁ * L ^ (k + 1 - (k + 1))) →
      DecParams S.G' × RawData d L (N₁ * L ^ T.m₁) (k + 1) N →
        (S.G'.Ω 1 × Fin N → ℂ) × (S.G'.Ω 1 → ℂ))
    (hF₁ : ∀ b, ∀ (s : DecParams S.G') (D' : BgData S.G' N), (∀ P, ‖s P‖ < Real.exp T.κ) →
      InUnionDomainC S.G' (bgC0 d L N) (c7 d L N T.BG T.κ) S.ν D' → ∀ (φ : S.G'.Ω 1 × Fin N → ℂ)
        (α : S.G'.Ω 1 → ℂ), IsDecBg S.G' (compWeight L S.a₁) S.ν (rho4 d L N T.BG T.κ) s D' φ α →
        F₁ b (s, rawOf D') = (φ, α))
    (Sol : Torus d (N₁ * L ^ T.m₁ * L ^ (k + 1 - (k + 1))) →
      Dec2.DecParams (coverOf S.G') × Edat (stepG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) N →
        ((stepG d L N₁ T.m₁ k (rhoSepG d L T.m₁)).Ω 1 × Fin N → ℂ) ×
          ((stepG d L N₁ T.m₁ k (rhoSepG d L T.m₁)).Ω 1 → ℂ))
    (hSol : ∀ b, SolSpec S.G' (stepG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) S.a₁ S.ν T.BG T.BG₂ T.κ
      T.t T.t (Sol b))
    {Q : Matrix (Fin N) (Fin N) ℝ} (hQ : Qᵀ * Q = 1) (e : Rn N ≃ₗᵢ[ℝ] Rn N)
    (he : ∀ x : Rn N, e x = WithLp.toLp 2 (Q *ᵥ x.ofLp))
    (z : RootIdx d L N₁ T.m₁ (k + 1)) (θ θ' : physParam N S)
    (hθ : (θ.1 : RawData d L (N₁ * L ^ T.m₁) (k + 1) N) ∈
      XiCRaw S.G' (compWeight L S.a₁) S.ν (k + 1) 1 T.t)
    (hθθ' : (θ'.1 : RawData d L (N₁ * L ^ T.m₁) (k + 1) N) =
      rotRaw (cmat Q) (θ.1 : RawData d L (N₁ * L ^ T.m₁) (k + 1) N))
    (Y' : {Y' // Y' ∈ bridgeFamily 1 (fun _ => Set.univ) (e1DomG S) z}) (u : ℂ)
    {Φ : ∀ b, (S.blockSplit 1 hp).Ωb b} (hΦc : Φ ∈ physCarrier S 1 hp) :
    e1MarkGParamG S F₁ Sol S.p₁ hp z T.t θ' Y' u (fun b x => e (Φ b x)) =
      e1MarkGParamG S F₁ Sol S.p₁ hp z T.t θ Y' u Φ := by
  subst hS
  refine e1MarkGParamG_rot (T.step k hk N₁ ν β p₁) D.core hk (T.step k hk N₁ ν β p₁).hG
    (cψ := (T.step k hk N₁ ν β p₁).p₁) hp.le T.large_block T.dom_margin T.coer_margin
    T.δc_small F₁ hF₁ Sol hSol hQ e he le_rfl le_rfl hp ?_ z θ θ' hθ hθθ' Y' u hΦc
  intro u' hu'
  have h := markRadius_of_ray (X := Real.sqrt N * (‖((((T.step k hk N₁ ν β p₁).betaU ^
      (-(1 / 2 : ℝ)) : ℝ) : ℂ))‖ * covSupConstC d L N (compWeight L (T.step k hk N₁ ν β p₁).a₁ k)
      T.κ)) (cψ := lvCpsiG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2))))
    (p₁ := (T.step k hk N₁ ν β p₁).p₁) hp.le D.r_pos T.t_pos D.ray_margin
    (by
      convert D.fl_radius using 1
      have ha : (T.step k hk N₁ ν β p₁).a₁ = 1 := rfl
      rw [ha]; ring) hu'
  nlinarith [h]

end Balaban.Inhabited
