/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Base.BaseFirstSiteSum
public import Balaban.LargeField.Base.BaseGaussCut
public import Balaban.LargeField.Base.BaseFirstAllGoodWhiteInst

/-!
# The small-fluctuation part of the all-good sector in product-measure form

For the whitened integrand `Ψ(φ) = e^{-½(|φ|² + q_D(φ))} F(P(Wφ))` and the test `rSmall p₁`,
`integral_rSmall_mul_Psi` writes
`∫ rSmall p₁ · Ψ = κ e^{-β B(e) + ⟨g, e⟩} (2π)^{N|ι|/2} Z_cut
   ∫ exp(-∑_x V_x(P(Wφ)) - ½ q_D(φ)) dμ_cut(φ)`
with `μ_cut` the truncated product measure (`gaussCut`) and `V_x` the site exponents
(`chartSiteReal`), provided that on the support of `rSmall p₁` the tangent vector stays inside the
chart balls and the chart cutoff is `1`.
-/

@[expose] public section

namespace Balaban.LargeField

open Balaban Balaban.Background Balaban.Multiscale Matrix Classical
open Balaban.LargeField.Base MeasureTheory SphereChart
open Balaban.LargeField.FRWhite

variable {d N L n : ℕ} [NeZero L] [NeZero n]

/-- The entries of the physical first-step Hessian (`baseSectorHessian_apply`). -/
noncomputable def baseSectorHessianEntries (ϱ : ℝ) (aw : ℕ → ℝ) (μ : ℝ)
    (α : (GeneratingSet.single (d := d) (L := L) (N₀ := 1 * n) (k := 1) ϱ).Ω 1 → ℝ)
    (x y : Torus d (L * n)) : ℝ :=
  fullMatrix (GeneratingSet.single (d := d) (L := L) (N₀ := 1 * n) (k := 1) ϱ) aw μ
    ((baseSector_side L n).symm ▸ x) ((baseSector_side L n).symm ▸ y) +
    if x = y then α ⟨(baseSector_side L n).symm ▸ x,
      baseSector_mem_single ϱ ((baseSector_side L n).symm ▸ x)⟩ else 0

theorem rSmall_ne_zero_iff {ι : Type*} [Fintype ι] (p₁ : ℝ) (φ : Config ι N) :
    rSmall (ι := ι) (N := N) p₁ φ ≠ 0 ↔ ∀ x, ‖φ x‖ < p₁ := by
  classical
  unfold rSmall
  rw [Finset.prod_ne_zero_iff]
  refine forall_congr' fun x => ?_
  simp only [Finset.mem_univ, true_implies]
  split_ifs with h <;> simp [h]

/-- The tangent projection does not increase the norm of a site. -/
theorem norm_tangentProj_le {ι : Type*} (e : Config ι N) (he : ∀ x, ‖e x‖ = 1)
    (u : Config ι N) (x : ι) : ‖tangentProj e he u x‖ ≤ ‖u x‖ := by
  have h := norm_sq_eq_inner_sq_add (e x) (he x) (u x)
  have h2 : ‖tangentProj e he u x‖ = ‖perpProj (e x) (u x)‖ := rfl
  rw [h2]
  nlinarith [norm_nonneg (perpProj (e x) (u x)), norm_nonneg (u x), sq_nonneg (inner ℝ (e x) (u x))]

/-- **The small-fluctuation part in product-measure form.** -/
theorem integral_rSmall_mul_Psi {β : ℝ} (hβ : 0 < β) (a₀ ν : ℝ) (regimeB : Prop)
    (h : EuclideanSpace ℝ (Fin N)) (g : Torus d (L * n) → Fin N → ℂ)
    (θ : Torus d n → EuclideanSpace ℝ (Fin N)) (e : Config (Torus d (L * n)) N)
    (he : ∀ x, ‖e x‖ = 1)
    (Hα : Config (Torus d (L * n)) N →ₗ[ℝ] Config (Torus d (L * n)) N)
    (a : Torus d (L * n) → Torus d (L * n) → ℝ)
    (hH : ∀ u x i, (Hα u x i : ℝ) = ∑ y, a x y * (u y i : ℝ))
    (χ : CfgT d N L n → ℝ) (κ : ℂ)
    (W : Config (Torus d (L * n)) N ≃ₗ[ℝ] Config (Torus d (L * n)) N)
    (qD : Config (Torus d (L * n)) N → ℝ) {p₁ : ℝ} (hp : 0 < p₁)
    (hsmall : ∀ φ : Config (Torus d (L * n)) N,
      rSmall (ι := Torus d (L * n)) (N := N) p₁ φ ≠ 0 →
        (∀ x, ‖tangentProj e he (W φ) x‖ < Real.sqrt β) ∧
          χ (chartMapPi e he ((Real.sqrt β)⁻¹ • tangentProj e he (W φ))) = 1) :
    let ec : CfgT d N L n := fun x => ⟨e x, mem_sphere_zero_iff_norm.mpr (he x)⟩
    ∫ φ : Config (Torus d (L * n)) N, ((rSmall (ι := Torus d (L * n)) (N := N) p₁ φ : ℝ) : ℂ) *
        ((((Real.exp (-(1 / 2) * (cinner φ φ + qD φ))) : ℝ) : ℂ) *
          baseSectorF β a₀ ν regimeB h g θ e he Hα χ κ (tangentProj e he (W φ))) =
      (((2 * Real.pi) ^ (((N * Fintype.card (Torus d (L * n)) : ℕ) : ℝ) / 2) *
          gaussCutMass (Torus d (L * n)) N p₁ : ℝ) : ℂ) *
        (κ * Complex.exp (-((β * (energy d N (L * n) (if regimeB then ν else 0) h ec +
            (a₀ * (L : ℝ) ^ d / (2 * (L : ℝ) ^ 2)) *
              ∑ y : Torus d n, ‖θ y - baseQ d N L n ec y‖ ^ 2) : ℝ) : ℂ) +
          ∑ x : Torus d (L * n), ∑ i : Fin N, g x i * (((e x) i : ℝ) : ℂ)) *
        ∫ φ, Complex.exp (-(∑ x, chartSiteReal β e a (β * (ν - (if regimeB then ν else 0)) / 2) h g
              (fun x => (tangentProj e he (W φ) x : EuclideanSpace ℝ (Fin N))) x) -
            (((1 / 2 * qD φ : ℝ)) : ℂ)) ∂(gaussCut (Torus d (L * n)) N p₁)) := by
  intro ec
  set T0 : ℂ := Complex.exp (-((β * (energy d N (L * n) (if regimeB then ν else 0) h ec +
            (a₀ * (L : ℝ) ^ d / (2 * (L : ℝ) ^ 2)) *
              ∑ y : Torus d n, ‖θ y - baseQ d N L n ec y‖ ^ 2) : ℝ) : ℂ) +
          ∑ x : Torus d (L * n), ∑ i : Fin N, g x i * (((e x) i : ℝ) : ℂ)) with hT0
  set Gf : Config (Torus d (L * n)) N → ℂ := fun φ => (κ * T0) *
    Complex.exp (-(∑ x, chartSiteReal β e a (β * (ν - (if regimeB then ν else 0)) / 2) h g
              (fun x => (tangentProj e he (W φ) x : EuclideanSpace ℝ (Fin N))) x) -
            (((1 / 2 * qD φ : ℝ)) : ℂ)) with hGf
  have h1 := integral_rSmall_gaussian (Torus d (L * n)) N hp Gf
  have h2 : ∫ φ : Config (Torus d (L * n)) N, ((rSmall (ι := Torus d (L * n)) (N := N) p₁ φ : ℝ) : ℂ) *
        ((((Real.exp (-(1 / 2) * (cinner φ φ + qD φ))) : ℝ) : ℂ) *
          baseSectorF β a₀ ν regimeB h g θ e he Hα χ κ (tangentProj e he (W φ))) =
      ∫ φ : Config (Torus d (L * n)) N, ((rSmall (ι := Torus d (L * n)) (N := N) p₁ φ : ℝ) : ℂ) *
        ((((Real.exp (-(1 / 2) * cinner φ φ)) : ℝ) : ℂ) * Gf φ) := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun φ => ?_)
    dsimp only
    rcases rSmall_zero_or_one (ι := Torus d (L * n)) (N := N) p₁ φ with h0 | h0
    · rw [h0]; simp
    · have hne : rSmall (ι := Torus d (L * n)) (N := N) p₁ φ ≠ 0 := by rw [h0]; exact one_ne_zero
      obtain ⟨hv, hχ⟩ := hsmall φ hne
      have hF := baseSectorF_eq_exp_neg_sum hβ a₀ ν regimeB h g θ e he Hα a hH χ κ
        (tangentProj e he (W φ)) hv
      dsimp only at hF
      rw [hF, hχ, h0]
      simp only [Gf, Complex.ofReal_one, one_mul]
      have : -(1 / 2) * (cinner φ φ + qD φ) = -(1 / 2) * cinner φ φ + -(1 / 2 * qD φ) := by ring
      have hq : (((Real.exp (-(1 / 2 * qD φ)) : ℝ)) : ℂ) =
          Complex.exp (-(((1 / 2 * qD φ : ℝ)) : ℂ)) := by
        rw [Complex.ofReal_exp]; push_cast; ring_nf
      have hsplit : ∀ A B : ℂ, Complex.exp (A - B) = Complex.exp A * Complex.exp (-B) := by
        intro A B; rw [sub_eq_add_neg, Complex.exp_add]
      rw [this, Real.exp_add, Complex.ofReal_mul, hq, hsplit]
      simp only [hT0, ec]
      ring
  rw [h2, h1, integral_const_mul]


/-- The defect form of the whitening is a real quadratic form in the sites: for a real
configuration, `Re ⟨ψ, D ψ⟩ = ∑_{p,q} Re D_{pq} ψ_p ψ_q` (here `ψ_p = φ_{c p}`), i.e. the
exponent `-½ q_D(φ)` of `baseRho1_allGood_baseWhite` is `-½ ∑_{x,y} D_{xy} φ_x · φ_y`. -/
theorem re_dotProduct_defect {κ : Type*} [Fintype κ] (D : Matrix κ κ ℂ) (ψ : κ → ℝ) :
    ((fun p => ((ψ p : ℝ) : ℂ)) ⬝ᵥ (D *ᵥ fun p => ((ψ p : ℝ) : ℂ))).re =
      ∑ p, ∑ q, (D p q).re * (ψ p * ψ q) := by
  simp only [dotProduct, Matrix.mulVec, Complex.re_sum, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero, Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
  ring

variable [NeZero N]

open Classical in
/-- **The small-fluctuation part of the all-good sector in product-measure form** (end of T-A).
For `p₁ > 0` with `N ‖W_c‖_∞ p₁ < √β` (`‖W_c‖_∞` the maximal absolute row sum of the whitening
matrix), and provided the chart cutoff `χ` equals `1` on the chart
points of the small-fluctuation configurations (the margins of `BaseCutoffMargins`, see the
docstring there: this is not implied by the base record), the part of the all-good sector on
`rSmall p₁` is `κ e^{-β B(e) + ⟨g, e⟩} (2π)^{N|𝕋|/2} Z_cut ∫ exp(-∑_x V_x(P(Wφ)) - ½ q_D(φ)) dμ_cut`. -/
theorem baseRho1_allGood_baseWhite_product
    {β a z₁ : ℝ} (hβ : 0 < β) (ha0 : 0 < a)
    (ν δ₀ : ℝ) (ϱ : ℝ) (aw : ℕ → ℝ) (ha : aw 1 = a)
    (regimeB : Prop) (hδ : 0 < δ₀)
    (h : EuclideanSpace ℝ (Fin N)) (hh : ‖h‖ = 1)
    (H : BgHyp d L 1 ϱ aw (if regimeB then ν else 0))
    (hΛ1 : 4 * d * L * δ₀ ≤ bgC1 d L N)
    (hΛ2 : (d + 2 + 4 * d * bgK1 d L N) * L * δ₀ ≤ 1 / 4)
    (g : Torus d (L * n) → Fin N → ℂ)
    (ψ : Torus d n → EuclideanSpace ℝ (Fin N))
    (φ₀ : CfgT d N L n)
    (hp : baseSectorCubeProduct regimeB ν δ₀ h (z₁ • ψ) φ₀ ≠ 0) (R : ℕ) (p₁ : ℝ) (hp₁ : 0 < p₁)
    (hR : 4 * Real.sqrt (1 - Real.sqrt (1 - ((baseCoercivity L / 2) /
        baseJ d (if regimeB then ν else 0)) ^ 2))⁻¹ *
      (Real.sqrt (1 - ((baseCoercivity L / 2) / baseJ d (if regimeB then ν else 0)) ^ 2) ^ (R + 1) /
        (1 - Real.sqrt (1 - ((baseCoercivity L / 2) /
          baseJ d (if regimeB then ν else 0)) ^ 2))) < 1) :
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
      (N * matRowSum Wc * p₁ < Real.sqrt β →
        (∀ φ : Config (Torus d (L * n)) N,
          rSmall (ι := Torus d (L * n)) (N := N) p₁ φ ≠ 0 →
            χ (chartMapPi e he ((Real.sqrt β)⁻¹ • tangentProj e he (W φ))) = 1) →
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
  intro θ G α e he Hα χ κ F ea c Wc Dc ec aM
  obtain ⟨W, hrow, hρ⟩ := baseRho1_allGood_baseWhite_split hβ ha0 ν δ₀ ϱ aw ha regimeB hδ h hh H hΛ1
    hΛ2 g ψ φ₀ hp R p₁ hR
  refine ⟨W, hrow, fun hsz hχ => ?_⟩
  dsimp only at hρ ⊢
  rw [hρ]
  have hH : ∀ u x i, (Hα u x i : ℝ) = ∑ y, aM x y * (u y i : ℝ) := fun u x i => rfl
  have hsm : ∀ φ : Config (Torus d (L * n)) N,
      rSmall (ι := Torus d (L * n)) (N := N) p₁ φ ≠ 0 →
        (∀ x, ‖tangentProj e he (W φ) x‖ < Real.sqrt β) ∧
          χ (chartMapPi e he ((Real.sqrt β)⁻¹ • tangentProj e he (W φ))) = 1 := by
    intro φ hφ
    refine ⟨fun x => ?_, hχ φ hφ⟩
    have hφ' := (rSmall_ne_zero_iff p₁ φ).1 hφ
    have hn : ‖φ‖ ≤ p₁ := (pi_norm_le_iff_of_nonneg hp₁.le).2 fun y => (hφ' y).le
    have hcr : 0 ≤ (N : ℝ) * matRowSum Wc := by
      have : 0 ≤ matRowSum Wc := NNReal.coe_nonneg _
      positivity
    calc ‖tangentProj e he (W φ) x‖ ≤ ‖W φ x‖ := norm_tangentProj_le e he (W φ) x
      _ ≤ N * matRowSum Wc * ‖φ‖ := hrow φ x
      _ ≤ N * matRowSum Wc * p₁ := mul_le_mul_of_nonneg_left hn hcr
      _ < Real.sqrt β := hsz
  have hprod := integral_rSmall_mul_Psi hβ a ν regimeB h g θ e he Hα aM hH χ κ W
    (fun φ => ((fun p => ((φ (c p).1 (c p).2 : ℝ) : ℂ)) ⬝ᵥ
      (Dc *ᵥ fun p => ((φ (c p).1 (c p).2 : ℝ) : ℂ))).re) hp₁ hsm
  dsimp only at hprod
  rw [hprod]


end Balaban.LargeField
