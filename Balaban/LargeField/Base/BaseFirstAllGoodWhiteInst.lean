/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Base.BaseFirstAllGoodWhite
public import Balaban.LargeField.Base.BaseFRWhiteConfig
public import Balaban.LargeField.Base.BaseFRWhiteReal
public import Balaban.LargeField.Base.BaseFRWhiteSymm

/-!
# The all-good sector of the first density with the finite-range whitening

`baseRho1_allGood_baseWhite` instantiates `baseRho1_allGood_whitened` with the finite-range
whitening `W = baseWhiteW` of `BaseFRWhiteFirst.lean` (route FR-1), transported to a linear
equivalence of `Config (𝕋_{Ln}) N` (`exists_config_whitening`; `W` is real because the cut
Hamiltonian at the physical parameter `s = 1` is real, `whiteW_im_eq_zero`). The determinant is
`|det W| = ‖det baseWhiteW‖` and the defect form is `q_D(φ) = Re ⟨ψ_φ, D_R ψ_φ⟩` with
`D_R = whiteDefect (baseWhiteK …) R`, `ψ_φ` the coordinates of `φ`. The truncation order `R` is
only required to make the defect bound `4 (1-q)^{-1/2} q^{R+1}/(1-q)` of `baseWhite` less than 1.
-/

@[expose] public section

namespace Balaban.LargeField

open Balaban Balaban.Background Balaban.Multiscale Matrix Classical
open Balaban.LargeField.Base MeasureTheory SphereChart
open Balaban.LargeField.FRWhite

variable {d N L n : ℕ} [NeZero L] [NeZero n] [NeZero N]

open Classical in
/-- **The all-good sector of the first density with the explicit finite-range whitening.** -/
theorem baseRho1_allGood_baseWhite
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
    (hp : baseSectorCubeProduct regimeB ν δ₀ h (z₁ • ψ) φ₀ ≠ 0) (R : ℕ)
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
    let ea : G.Ω 1 → Fin N → ℝ := fun z i => e (baseSiteEquiv ϱ z) i
    let c : G.Ω 1 × Fin N ≃ (Σ _ : Torus d (L * n), Fin N) :=
      (Equiv.prodCongr (baseSiteEquiv ϱ) (Equiv.refl (Fin N))).trans
        (Equiv.sigmaEquivProd (Torus d (L * n)) (Fin N)).symm
    let Wc := baseWhiteW G aw (if regimeB then ν else 0) α (fun _ => 1) ea R
    let Dc := whiteDefect (baseWhiteK G aw (if regimeB then ν else 0) α (fun _ => 1) ea) R
    ∃ W : Config (Torus d (L * n)) N ≃ₗ[ℝ] Config (Torus d (L * n)) N,
      baseRho1 d N L n β a z₁ ν h ψ g =
        ((z₁ ^ (N * Fintype.card (Torus d n)) : ℝ) : ℂ) *
          ((((Real.sqrt β)⁻¹ ^ (Fintype.card (Torus d (L * n)) * (N - 1))) •
            ((((2 * Real.pi) ^ (-(Fintype.card (Torus d (L * n)) : ℝ) / 2) * ‖Wc.det‖ :
                ℝ) : ℂ) *
              ∫ φ : Config (Torus d (L * n)) N,
                (((Real.exp (-(1 / 2) * (cinner φ φ +
                  ((fun p => ((φ (c p).1 (c p).2 : ℝ) : ℂ)) ⬝ᵥ
                    (Dc *ᵥ fun p => ((φ (c p).1 (c p).2 : ℝ) : ℂ))).re))) : ℝ) : ℂ) *
                  F (tangentProj e he (W φ)))) +
            baseFirstRest d N L n β a z₁ ν regimeB δ₀ h g ψ) := by
  intro θ G α e he Hα χ κ F ea c Wc Dc
  have hL : 0 < L := Nat.pos_of_ne_zero (NeZero.ne L)
  have hμ := H.mass
  have hαn := baseSector_bgMult_norm_le_of_product_ne_zero ϱ aw regimeB ν δ₀ hδ h hh H hΛ1 θ φ₀ hp
  have hune : ∀ z, ∑ i, ea z i ^ 2 = 1 := fun z =>
    baseSector_center_sq_sum ϱ aw regimeB ν h hh H θ z
  have hs : (fun _ => (1 : ℂ)) ∈ baseParamNbhd G 0 := fun b _ => ⟨1, zero_le_one, le_rfl, by simp⟩
  have hη : (0 : ℝ) ≤ baseCoercivity L / (8 * d) := by
    have := baseCoercivity_pos hL
    positivity
  have : Nonempty (G.Ω 1) := ⟨(baseSiteEquiv ϱ).symm (Classical.arbitrary _)⟩
  obtain ⟨-, -, -, hnorm⟩ := baseWhite G ea hμ H.weights hαn le_rfl hη hs hune R
  have hU : IsUnit Wc :=
    whiteW_isUnit (half_pos (baseCoercivity_pos hL)) (baseJ_pos hμ) _ R (hnorm.trans_lt hR)
  have hdet : Wc.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det _).1 hU).ne_zero
  have hmap := baseSector_gaussForm_map_eq_reindex ϱ aw regimeB ν δ₀ hδ h hh H hΛ1 θ φ₀ hp
  have hAc : ∀ p q, baseOp N (fun z i => ((ea z i : ℝ) : ℂ))
      (baseHamiltonian G aw (if regimeB then ν else 0) α (fun _ => 1)) p q =
      ((LinearMap.toMatrix (configBasis (Torus d (L * n)) N) (configBasis (Torus d (L * n)) N)
        (gaussForm e Hα) (c p) (c q) : ℝ) : ℂ) := fun p q => by
    have := congrArg (fun M => M (c p) (c q)) hmap
    simp only [c, Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply,
      Matrix.map_apply] at this ⊢
    exact this.symm
  have hWim : ∀ p q, (Wc p q).im = 0 := fun p q =>
    whiteW_im_eq_zero _ _ _ (fun i j => by rw [hAc]; simp) R p q
  obtain ⟨W, hW1, hW2⟩ := exists_config_whitening e Hα c Wc Dc _ (fun p q => hAc p q) hWim hdet
    (fun ψ' => baseWhite_bilinear G ea hμ R ψ')
  refine ⟨W, ?_⟩
  rw [← hW1]
  exact baseRho1_allGood_whitened hβ ha0 ν δ₀ ϱ aw ha regimeB hδ h hh H hΛ1 hΛ2 g ψ φ₀ hp W
    (fun φ => ((fun p => ((φ (c p).1 (c p).2 : ℝ) : ℂ)) ⬝ᵥ
      (Dc *ᵥ fun p => ((φ (c p).1 (c p).2 : ℝ) : ℂ))).re) hW2

end Balaban.LargeField
