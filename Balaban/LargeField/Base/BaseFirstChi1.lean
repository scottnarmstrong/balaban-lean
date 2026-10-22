/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Base.BaseCutoffClass
public import Balaban.LargeField.Base.BaseFirstProductForm

/-!
# The small-fluctuation part of the all-good sector without the cutoff premise

`baseRho1_allGood_baseWhite_chi1` is `baseRho1_allGood_baseWhite_product` with its premise on the
chart cutoff replaced by the scale-one cube test `χ₁(□) = 1` (`ChiKProp`, tolerance `δ₁`) on every
cube and the numerical conditions of `baseSectorCubeProduct_eq_one_of_chi1`
(`δ₁ ≤ δ₀/2`, `√N E ≤ δ₀/8`, and `N ‖W‖_row p₁ ≤ √β δ₀/12`).
-/

@[expose] public section

namespace Balaban.LargeField

open Balaban Balaban.Background Balaban.Multiscale Matrix Classical
open Balaban.LargeField.Base MeasureTheory SphereChart
open Balaban.LargeField.FRWhite Balaban.Localization Balaban.SmallField

variable {d N L n : ℕ} [NeZero L] [NeZero n] [NeZero N]

open Classical in
/-- **The all-good sector in product-measure form from the scale-one cube test.** -/
theorem baseRho1_allGood_baseWhite_chi1 (hd : 3 ≤ d) (hL : 3 ≤ L) :
    ∃ Kw δw : ℝ, 0 < Kw ∧ 0 < δw ∧
    ∀
    {β a z₁ : ℝ} (_hβ : 0 < β) (_ha0 : 0 < a)
    (ν δ₀ : ℝ) (ϱ : ℝ) (aw : ℕ → ℝ) (_ha : aw 1 = a)
    (regimeB : Prop) (_hδ : 0 < δ₀)
    (h : EuclideanSpace ℝ (Fin N)) (hh : ‖h‖ = 1)
    (H : BgHyp d L 1 ϱ aw (if regimeB then ν else 0))
    (_hΛ1 : 4 * d * L * δ₀ ≤ bgC1 d L N)
    (_hΛ2 : (d + 2 + 4 * d * bgK1 d L N) * L * δ₀ ≤ 1 / 4)
    (g : Torus d (L * n) → Fin N → ℂ)
    (ψ : Torus d n → EuclideanSpace ℝ (Fin N))
    (φ₀ : CfgT d N L n)
    (_hp : baseSectorCubeProduct regimeB ν δ₀ h (z₁ • ψ) φ₀ ≠ 0) (R : ℕ) (p₁ : ℝ) (_hp₁ : 0 < p₁)
    (_hR : 4 * Real.sqrt (1 - Real.sqrt (1 - ((baseCoercivity L / 2) /
        baseJ d (if regimeB then ν else 0)) ^ 2))⁻¹ *
      (Real.sqrt (1 - ((baseCoercivity L / 2) / baseJ d (if regimeB then ν else 0)) ^ 2) ^ (R + 1) /
        (1 - Real.sqrt (1 - ((baseCoercivity L / 2) /
          baseJ d (if regimeB then ν else 0)) ^ 2))) < 1) 
    {M1 N₁ m₁ c n' : ℕ} [NeZero M1] [NeZero N₁] [NeZero n']
    (hn : 1 * n = M1 * N₁) (_hM1 : M1 = L ^ m₁) (_hm : N₁ * L ^ (1 - 1) = c * n')
    {a₁ δ₁ BG κ' : ℝ} (_ha₁ : 0 < a₁) (_hw : aw = compWeight L a₁)
    (_hΛ7 : 4 * d * L * δ₀ ≤ c7 d L N BG κ')
    (_H0 : BgHyp d L 1 (minSep L M1) (compWeight L a₁) (if regimeB then ν else 0))
    (_hν : 0 ≤ ν) (_hνle : (if regimeB then ν else 0) * ((L : ℝ) ^ 1) ^ 2 ≤ 1)
    (_hsep : 2 * d * Real.log L ≤ agmonRate d / 16 * (minSep L M1 - 1))
    (_hδc : 4 * d * L * δ₀ ≤ thm73C1 d L N)
    (_hε' : 4 * d * L * δ₀ ≤ bgC0 d L N)
    (_hχ1 : ∀ y0 : Torus d n', ChiKProp (compWeight L a₁) (if regimeB then ν else 0) δ₁
      (fun i => h i) c n' y0
      (show BlockCfg d (M1 * N₁) L 1 1 N from
        fun y i => baseSectorTheta (z₁ • ψ) (castCoarse hn y) i))
    (_hδ₁0 : 0 ≤ δ₁) (_hδ₁ : δ₁ ≤ δ₀ / 2)
    (_hKs : bgK1 d L N * bgC1 d L N ≤ min (deltaStar d L N) δw)
    (_hK1' : (2 * d + 2) * (bgK1 d L N * (4 * d * L * δ₀)) ≤ deltaStar d L N)
    (_hKw' : (2 * d + 2) * (bgK1 d L N * (4 * d * L * δ₀)) ≤ δw)
    (_hE : Real.sqrt N * (Kw * (cF d L * ((2 * d + 2) * (bgK1 d L N * (4 * d * L * δ₀)))) *
      Real.exp (-(gammaW d * ((c * M1 : ℕ) : ℝ)))) ≤ δ₀ / 8) ,
    let θ : Torus d n → EuclideanSpace ℝ (Fin N) := z₁ • ψ
    let G : GeneratingSet d L (1 * n) 1 ϱ := GeneratingSet.single ϱ
    let α := bgMult G aw (if regimeB then ν else 0) (baseSectorDatum ϱ θ h)
    let e : Config (Torus d (L * n)) N := baseSectorCenter ϱ aw regimeB ν h θ
    let he := baseSectorCenter_unit ϱ aw regimeB ν h hh H θ
    let Hα : Config (Torus d (L * n)) N →ₗ[ℝ] Config (Torus d (L * n)) N :=
      baseSectorHessian ϱ aw (if regimeB then ν else 0) (fun z => (α z).re)
    let χ := baseSectorCubeProduct regimeB ν δ₀ h θ
    let κ : ℂ := ((∏ _y : Torus d n,
      ((β * a * (L : ℝ) ^ d / (L : ℝ) ^ 2) / (2 * Real.pi)) ^
        ((N : ℝ) / 2) : ℝ) : ℂ)
    let F := baseSectorF β a ν regimeB h g θ e he Hα χ κ
    let ea : G.Ω 1 → Fin N → ℝ := fun z i => e (baseSectorSiteEquiv ϱ z) i
    let c : G.Ω 1 × Fin N ≃ (Σ _ : Torus d (L * n), Fin N) :=
      (Equiv.prodCongr (baseSectorSiteEquiv ϱ) (Equiv.refl (Fin N))).trans
        (Equiv.sigmaEquivProd (Torus d (L * n)) (Fin N)).symm
    let Wc := baseWhiteW G aw (if regimeB then ν else 0) α (fun _ => 1) ea R
    let Dc := whiteDefect (baseWhiteK G aw (if regimeB then ν else 0) α (fun _ => 1) ea) R
    let ec : CfgT d N L n := fun x => ⟨e x, mem_sphere_zero_iff_norm.mpr (he x)⟩
    let aM := baseSectorHessianEntries ϱ aw (if regimeB then ν else 0) (fun z => (α z).re)
    ∃ W : Config (Torus d (L * n)) N ≃ₗ[ℝ] Config (Torus d (L * n)) N,
      (∀ (φ : Config (Torus d (L * n)) N) (x : Torus d (L * n)),
        ‖W φ x‖ ≤ N * matRowSum Wc * ‖φ‖) ∧
      (N * matRowSum Wc * p₁ ≤ Real.sqrt β * δ₀ / 12 →
        let Ψ : Config (Torus d (L * n)) N → ℂ := fun φ =>
          (((Real.exp (-(1 / 2) * (cinner φ φ +
            ((fun p => ((φ (c p).1 (c p).2 : ℝ) : ℂ)) ⬝ᵥ
              (Dc *ᵥ fun p => ((φ (c p).1 (c p).2 : ℝ) : ℂ))).re))) : ℝ) : ℂ) *
            F (tangentProj e he (W φ))
        baseRho1 d N L n β a z₁ ν h ψ g =
          ((z₁ ^ (N * Fintype.card (Torus d n)) : ℝ) : ℂ) *
            ((((Real.sqrt β)⁻¹ ^ (Fintype.card (Torus d (L * n)) * (N - 1))) •
              ((((2 * Real.pi) ^ (-(Fintype.card (Torus d (L * n)) : ℝ) / 2) * ‖Wc.det‖ :
                  ℝ) : ℂ) *
                ((((2 * Real.pi) ^ (((N * Fintype.card (Torus d (L * n)) : ℕ) : ℝ) / 2) *
                    gaussCutMass (Torus d (L * n)) N p₁ : ℝ) : ℂ) *
                  (κ * Complex.exp (-((β * (energy d N (L * n) (if regimeB then ν else 0) h ec +
                    (a * (L : ℝ) ^ d / (2 * (L : ℝ) ^ 2)) *
                      ∑ y : Torus d n, ‖θ y - baseQ d N L n ec y‖ ^ 2) : ℝ) : ℂ) +
                    ∑ x : Torus d (L * n), ∑ i : Fin N, g x i * (((e x) i : ℝ) : ℂ)) *
                  ∫ φ, Complex.exp (-(∑ x, chartSiteReal β e aM
                      (β * (ν - (if regimeB then ν else 0)) / 2) h g
                      (fun x => (tangentProj e he (W φ) x : EuclideanSpace ℝ (Fin N))) x) -
                    (((1 / 2 * ((fun p => ((φ (c p).1 (c p).2 : ℝ) : ℂ)) ⬝ᵥ
                      (Dc *ᵥ fun p => ((φ (c p).1 (c p).2 : ℝ) : ℂ))).re : ℝ)) : ℂ))
                    ∂(gaussCut (Torus d (L * n)) N p₁)) +
                  ∫ φ : Config (Torus d (L * n)) N,
                    ((1 - rSmall (ι := Torus d (L * n)) (N := N) p₁ φ : ℝ) : ℂ) * Ψ φ))) +
              baseFirstRest d N L n β a z₁ ν regimeB δ₀ h g ψ)) := by
  obtain ⟨Kw, δw, hK, hδw, hsm⟩ := baseSectorCubeProduct_eq_one_of_chi1 (N := N) hd hL
  refine ⟨Kw, δw, hK, hδw, ?_⟩
  intro β a z₁ hβ ha0 ν δ₀ ϱ aw ha regimeB hδ h hh H hΛ1 hΛ2 g ψ φ₀ hp R p₁ hp₁ hR M1 N₁ m₁ c n' _ _ _
    hn hM1 hm a₁ δ₁ BG κ' ha₁ hw hΛ7 H0 hν hνle hsep hδc hε' hχ1 hδ₁0 hδ₁ hKs hK1' hKw' hE
  subst hw
  intro θ G α e he Hα χ κ F ea c Wc Dc ec aM
  obtain ⟨W, hrow, hprod⟩ := baseRho1_allGood_baseWhite_product hβ ha0 ν δ₀ (ϱ := ϱ)
    (compWeight L a₁) ha regimeB hδ h hh H hΛ1 hΛ2 g ψ φ₀ hp R p₁ hp₁ hR
  refine ⟨W, hrow, fun hρ => ?_⟩
  have hδ4 : δ₀ ≤ 1 / 4 := by
    have hK1 := bgK1_pos d L N
    have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne L)
    have h1 : (1 : ℝ) ≤ d + 2 + 4 * d * bgK1 d L N := by nlinarith
    have h2 : (1 : ℝ) ≤ (d + 2 + 4 * d * bgK1 d L N) * L := one_le_mul_of_one_le_of_one_le h1 hL1
    have h3 : δ₀ ≤ (d + 2 + 4 * d * bgK1 d L N) * L * δ₀ := le_mul_of_one_le_left hδ.le h2
    linarith
  have hs : 0 < Real.sqrt β := Real.sqrt_pos.2 hβ
  have hcr : 0 ≤ (N : ℝ) * matRowSum Wc := by
    have : 0 ≤ matRowSum Wc := NNReal.coe_nonneg _
    positivity
  have hρ0 : 0 ≤ (N : ℝ) * matRowSum Wc * p₁ := by positivity
  have hsδ : Real.sqrt β * δ₀ ≤ Real.sqrt β * (1 / 4) := mul_le_mul_of_nonneg_left hδ4 hs.le
  have hlt : (N : ℝ) * matRowSum Wc * p₁ < Real.sqrt β := by linarith
  have hρ2 : (N : ℝ) * matRowSum Wc * p₁ ≤ Real.sqrt β / 2 := by linarith
  have hχ : ∀ φ : Config (Torus d (L * n)) N,
      rSmall (ι := Torus d (L * n)) (N := N) p₁ φ ≠ 0 →
        χ (chartMapPi e he ((Real.sqrt β)⁻¹ • tangentProj e he (W φ))) = 1 := by
    intro φ hφ
    have hφ' := (rSmall_ne_zero_iff p₁ φ).1 hφ
    have hn' : ‖φ‖ ≤ p₁ := (pi_norm_le_iff_of_nonneg hp₁.le).2 fun y => (hφ' y).le
    have hwρ : ∀ x, ‖(tangentProj e he (W φ) x : EuclideanSpace ℝ (Fin N))‖ ≤
        (N : ℝ) * matRowSum Wc * p₁ := fun x =>
      (norm_tangentProj_le e he (W φ) x).trans
        ((hrow φ x).trans (mul_le_mul_of_nonneg_left hn' hcr))
    have hv : ∀ x, ‖tangentProj e he (W φ) x‖ < Real.sqrt β := fun x => lt_of_le_of_lt (hwρ x) hlt
    have hpt := chartMapPi_inv_sqrt_eq_chartPoint e he hβ (tangentProj e he (W φ)) hv
    exact hsm hn hM1 hm ha₁ regimeB hδ h hh H hΛ1 hΛ7 H0 hν hνle hsep hKs hδc hε' hK1' hKw'
      (z₁ • ψ) φ₀ _ hp hχ1 hβ (fun x => (tangentProj e he (W φ) x : EuclideanSpace ℝ (Fin N)))
      hρ0 hρ2 hwρ (fun y => congrFun hpt y) hδ₁0 hδ₁ hE (tangent_small hβ hρ)
  exact hprod hlt hχ

end Balaban.LargeField
