/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Spine.LastIntegral
public import Balaban.Green.FinalSpinCurry

/-!
# The Gaussian reduction of the small-field factor over a cut

A6-3 (a), first step (`notes/phase1/SPINE-PLAN.md`; P7 (4.3)-(4.7), P4 (6.4)-(6.6)). The last
integral of the small-field factor `sfFactor2 C vc Y` on a cut `Y` is an integral over the fields
`ψ_k` of the `k`-blocks. For every real symmetric positive definite form `K` on
`blocks × Fin N` and every centre `ψ₀`, the change of variables `ψ = ψ₀ + K^{-1/2} w` turns it
into the average over the standard Gaussian `w` of

`sfGaussIntegrand = sfFactor2 C vc Y (ψ₀ + K^{-1/2} w) · exp(½ Q_K(K^{-1/2} w))`

times the normalizer `Z_K = (2π)^{n/2} det K^{-1/2}` (`integral_sfFactor2_gauss`). The cut `Y`
enters only through the integrand, so the statement is the same for every cut; `Y = univ`
is `sfIntegral` (`sfIntegral_eq_gauss`). The form `K` is a parameter: in the source it is the
Hessian of the main action at the constant saddle (`finalHessian`), and the factor
`exp(½ Q_K)` cancels the Gaussian part of the exponent of `sfFactor2`, so that what remains under
the Gaussian average is the interaction.

The measurability of `ψ ↦ sfFactor2 C vc Y ψ hv g` is a hypothesis (otherwise the Bochner
integral is `0` by convention).
-/

@[expose] public section

open MeasureTheory Matrix Balaban Balaban.LargeField Balaban.LargeField.Def7
  Balaban.LargeField.Def7v2 Balaban.Green

namespace Balaban.RootFSpine

section Core

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {N : ℕ}

/-- **The Gaussian reduction for fields of `N`-vectors**: for `K` positive definite on
`ι × Fin N`, a centre `ψ₀` and a measurable `f`,
`∫ f = Z_K ∫ f(ψ₀ + K^{-1/2} w) exp(½ Q_K(K^{-1/2} w)) dγ(w)`. -/
theorem integral_spin_gaussian {K : Matrix (ι × Fin N) (ι × Fin N) ℝ} (hK : K.PosDef)
    (ψ0 : ι → EuclideanSpace ℝ (Fin N)) {f : (ι → EuclideanSpace ℝ (Fin N)) → ℂ}
    (hf : Measurable f) :
    ∫ ψ, f ψ = (pdGaussNorm (ι × Fin N) ℝ K : ℂ) *
      ∫ w, f ((spinField ι N).symm (spinField ι N ψ0 + matAct (pdSqrtInv K) w)) *
        ((Real.exp ((1 / 2) * pdQuad K (matAct (pdSqrtInv K) w)) : ℝ) : ℂ)
        ∂(pdGaussian (ι × Fin N) ℝ) := by
  have h1 : ∫ ψ, f ψ = ∫ v : ι × Fin N → ℝ, f ((spinField ι N).symm v) := by
    have := integral_spinField ι N (fun v => f ((spinField ι N).symm v))
    simpa using this
  have h2 : ∫ v : ι × Fin N → ℝ, f ((spinField ι N).symm v) =
      ∫ v : ι × Fin N → ℝ, f ((spinField ι N).symm (spinField ι N ψ0 + v)) :=
    (integral_add_left_eq_self (μ := (volume : Measure (ι × Fin N → ℝ))) _ _).symm
  have hF : Measurable fun v : ι × Fin N → ℝ =>
      f ((spinField ι N).symm (spinField ι N ψ0 + v)) *
        ((Real.exp ((1 / 2) * pdQuad K v) : ℝ) : ℂ) := by
    have hq : Measurable fun v : ι × Fin N → ℝ => Real.exp ((1 / 2) * pdQuad K v) := by
      refine Real.measurable_exp.comp (Measurable.const_mul ?_ _)
      unfold pdQuad pdBil
      fun_prop
    exact (hf.comp ((spinField ι N).symm.measurable.comp
      (measurable_const.add measurable_id))).mul (Complex.measurable_ofReal.comp hq)
  have h3 := integral_pd_gaussian_change (ι := ι × Fin N) (W := ℝ) hK hF
  rw [h1, h2]
  convert h3 using 2
  funext v
  rw [mul_left_comm, ← Complex.ofReal_mul, ← Real.exp_add]
  simp

end Core

section Sf

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {M K : ℕ} [NeZero M]
  [NeZero S.L] {N k m₁ : ℕ} {ϱ : ℝ}

/-- **The integrand of the small-field factor in the Gaussian variable** (cut `Y`, form `Kq`,
centre `ψ₀`): `sfFactor2 C vc Y (ψ₀ + Kq^{-1/2} w) · exp(½ Q_{Kq}(Kq^{-1/2} w))`. -/
noncomputable def sfGaussIntegrand (C : SFCtx S n R M K N k m₁ ϱ) (vc : CorrCoef S.d)
    (Y : Set (Torus S.d (n k))) (hv : EuclideanSpace ℝ (Fin N)) (g : GIdx S n M K N → ℂ)
    (Kq : Matrix (BlockAt S n M K k × Fin N) (BlockAt S n M K k × Fin N) ℝ)
    (ψ0 : BlockAt S n M K k → EuclideanSpace ℝ (Fin N))
    (w : BlockAt S n M K k × Fin N → ℝ) : ℂ :=
  sfFactor2 C vc Y ((spinField (BlockAt S n M K k) N).symm
      (spinField (BlockAt S n M K k) N ψ0 + matAct (pdSqrtInv Kq) w)) hv g *
    ((Real.exp ((1 / 2) * pdQuad Kq (matAct (pdSqrtInv Kq) w)) : ℝ) : ℂ)

/-- **The Gaussian reduction of the last integral over a cut `Y`** (A6-3 (a), P7 (4.3)-(4.7)):
`∫ sfFactor2 C vc Y dψ_k = Z_K ∫ sfGaussIntegrand dγ`, for every positive definite form `Kq`
and centre `ψ₀`. -/
theorem integral_sfFactor2_gauss (C : SFCtx S n R M K N k m₁ ϱ) (vc : CorrCoef S.d)
    (Y : Set (Torus S.d (n k))) (hv : EuclideanSpace ℝ (Fin N)) (g : GIdx S n M K N → ℂ)
    {Kq : Matrix (BlockAt S n M K k × Fin N) (BlockAt S n M K k × Fin N) ℝ} (hK : Kq.PosDef)
    (ψ0 : BlockAt S n M K k → EuclideanSpace ℝ (Fin N))
    (hmeas : Measurable fun ψ => sfFactor2 C vc Y ψ hv g) :
    ∫ ψ, sfFactor2 C vc Y ψ hv g =
      (pdGaussNorm (BlockAt S n M K k × Fin N) ℝ Kq : ℂ) *
        ∫ w, sfGaussIntegrand C vc Y hv g Kq ψ0 w ∂(pdGaussian (BlockAt S n M K k × Fin N) ℝ) :=
  integral_spin_gaussian hK ψ0 hmeas

/-- **`Ξ^sf` as a Gaussian average** (the empty cut `Y = univ`). -/
theorem sfIntegral_eq_gauss {P : BudgetConsts} {cs : OpConsts} {k0 : ℕ}
    {geo : ∀ (nK : ℕ) [NeZero nK], Geo S (sides S.L K nK) R M}
    {P6 : Balaban.SmallField.Def6.Consts} {C7 : Consts7}
    (F : RepFam S R k0 K M N geo cs P k C7.m₁ ϱ) (hM6 : M = S.L ^ (P6.m₀ + C7.m₁))
    (hkK : k ≤ K) (vc : CorrCoef S.d) (hv : EuclideanSpace ℝ (Fin N)) (nK : ℕ) [NeZero nK]
    (g : GIdx S (sides S.L K nK) M K N → ℂ)
    {Kq : Matrix (BlockAt S (sides S.L K nK) M K k × Fin N)
      (BlockAt S (sides S.L K nK) M K k × Fin N) ℝ} (hK : Kq.PosDef)
    (ψ0 : BlockAt S (sides S.L K nK) M K k → EuclideanSpace ℝ (Fin N))
    (hmeas : Measurable fun ψ => sfFactor2 (F.ctx hM6 hkK nK) vc Set.univ ψ hv g) :
    sfIntegral F hM6 hkK vc hv nK g =
      (pdGaussNorm (BlockAt S (sides S.L K nK) M K k × Fin N) ℝ Kq : ℂ) *
        ∫ w, sfGaussIntegrand (F.ctx hM6 hkK nK) vc Set.univ hv g Kq ψ0 w
          ∂(pdGaussian (BlockAt S (sides S.L K nK) M K k × Fin N) ℝ) :=
  integral_sfFactor2_gauss _ vc Set.univ hv g hK ψ0 hmeas

end Sf

end Balaban.RootFSpine
