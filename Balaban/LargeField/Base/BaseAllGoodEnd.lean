/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Base.BaseCutoffClass
public import Balaban.LargeField.Base.BaseFirstChi1
public import Balaban.LargeField.Base.BaseFRWhiteLogDetBase

/-!
# The all-good sector of the first step, end to end

`baseAllGood_endToEnd`: the small-fluctuation part of the all-good term of the first density is
`z₁^{N|𝕋_n|} (√β)^{-(N-1)|𝕋_{Ln}|} (2π)^{-|𝕋_{Ln}|/2} |det W| (2π)^{N|𝕋_{Ln}|/2} Z_cut
κ e^{-β A₁(e;θ) + ⟨g, e⟩} ∫ exp(-∑_x V_x(P(Wφ)) - ½ ⟨φ, D_R φ⟩) dμ_cut` (plus the large-fluctuation
part and the failed-cube sectors), under the scale-one cube test, and
`log |det W| = ½ Re ∑_{n ≥ 1} (-1)^{n+1} tr(D_R^n)/n - ½ log |det A_e|`.
-/

@[expose] public section

namespace Balaban.LargeField

open Balaban Balaban.Background Balaban.Multiscale Matrix Classical
open Balaban.LargeField.Base MeasureTheory SphereChart
open Balaban.LargeField.FRWhite Balaban.Localization Balaban.SmallField

variable {d N L n : ℕ} [NeZero L] [NeZero n] [NeZero N]

open Classical in
/-- **The all-good sector end to end.** -/
theorem baseAllGood_endToEnd (hd : 3 ≤ d) (hL : 3 ≤ L) :
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
      Real.exp (-(gammaW d * ((c * M1 : ℕ) : ℝ)))) ≤ δ₀ / 8) 
    (_hrowD : (N : ℝ) * (2 * ((2 * R + 1) * (d * L + 1)) + 1) ^ d *
      (4 * Real.sqrt (1 - Real.sqrt (1 - ((baseCoercivity L / 2) /
        baseJ d (if regimeB then ν else 0)) ^ 2))⁻¹ *
        (Real.sqrt (1 - ((baseCoercivity L / 2) / baseJ d (if regimeB then ν else 0)) ^ 2) ^ (R + 1) /
          (1 - Real.sqrt (1 - ((baseCoercivity L / 2) / baseJ d (if regimeB then ν else 0)) ^ 2)))) < 1),
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
      Real.log ‖Wc.det‖ = (1 / 2) * (∑' n : ℕ, (-1) ^ n * (Dc ^ (n + 1)).trace /
          ((n : ℂ) + 1)).re - (1 / 2) * Real.log ‖(baseOp N (fun z i => (ea z i : ℂ))
          (baseHamiltonian G (compWeight L a₁) (if regimeB then ν else 0) α (fun _ => 1))).det‖ ∧
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
  obtain ⟨Kw, δw, hK, hδw, hch⟩ := baseRho1_allGood_baseWhite_chi1 (N := N) (n := n) hd hL
  refine ⟨Kw, δw, hK, hδw, ?_⟩
  intro β a z₁ hβ ha0 ν δ₀ ϱ aw ha regimeB hδ h hh H hΛ1 hΛ2 g ψ φ₀ hp R p₁ hp₁ hR M1 N₁ m₁ c n' _ _ _
    hn hM1 hm a₁ δ₁ BG κ' ha₁ hw hΛ7 H0 hν hνle hsep hδc hε' hχ1 hδ₁0 hδ₁ hKs hK1' hKw' hE hrowD
  subst hw
  obtain ⟨W, hrow, hid⟩ := hch hβ ha0 ν δ₀ ϱ (compWeight L a₁) ha regimeB hδ h hh H hΛ1 hΛ2 g ψ φ₀
    hp R p₁ hp₁ hR hn hM1 hm ha₁ rfl hΛ7 H0 hν hνle hsep hδc hε' hχ1 hδ₁0 hδ₁ hKs hK1' hKw' hE
  intro θ G α e he Hα χ κ F ea c Wc Dc ec aM
  have hL0 : 0 < L := Nat.pos_of_ne_zero (NeZero.ne L)
  have hμ := H.mass
  have hαn := baseSector_bgMult_norm_le_of_product_ne_zero ϱ (compWeight L a₁) regimeB ν δ₀ hδ h hh
    H hΛ1 θ φ₀ hp
  have hune : ∀ z, ∑ i, ea z i ^ 2 = 1 := fun z =>
    baseSector_center_sq_sum ϱ (compWeight L a₁) regimeB ν h hh H θ z
  have hs : (fun _ => (1 : ℂ)) ∈ baseParamNbhd G 0 := fun b _ => ⟨1, zero_le_one, le_rfl, by simp⟩
  have hη : (0 : ℝ) ≤ baseCoercivity L / (8 * d) := by
    have := baseCoercivity_pos hL0
    positivity
  have : Nonempty (G.Ω 1) := ⟨(baseSectorSiteEquiv ϱ).symm (Classical.arbitrary (Torus d (L * n)))⟩
  have hlog := log_abs_det_baseWhiteW G ea hμ H.weights hαn le_rfl hη hs hune R hrowD
  refine ⟨W, hrow, hlog, hid⟩

end Balaban.LargeField
