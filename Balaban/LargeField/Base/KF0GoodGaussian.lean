/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Base.KF0Gaussian
public import Balaban.LargeField.Base.KF0BlockSplit
public import Balaban.Green.KF0DetWalks
import Mathlib.Analysis.Matrix.Order
import Mathlib.Tactic.Linarith

/-!
# The Gaussian change of variables on the good region of a fixed bad set (package W383)

Fixed bad set `D ⊂ (ℤ/m)^d` (a finset of sites) and good sites `G = Dᶜ` (the subtype `Good D`).
`K_G = kwOpSub d m ν D` is the principal submatrix of `-Δ + ν` on `G` (landed in
`Balaban/Green/KF0KilledWalks.lean`).  This file contains only the linear algebra and the
Gaussian change of variables for a **fixed** `D`:

* `kwOpSub_posDef`: `K_G` is positive definite (principal submatrix of the positive definite
  `-Δ + ν`).
* `kwSqrt d m ν D := CFC.sqrt (K_G⁻¹)`: the positive definite square root of `K_G⁻¹`, built from
  Mathlib's continuous functional calculus square root `CFC.sqrt` on matrices (scoped order
  `MatrixOrder`).  Theorems: `kwSqrt_mul_self` (`C * C = K_G⁻¹`), `kwSqrt_mul_mul`
  (`C * K_G * C = 1`), `kwSqrt_transpose`, `kwSqrt_posDef`, `kwSqrt_det_sq`, `kwSqrt_det_pos`.
* `goodVol`, `goodGaussian`: the Lebesgue measure and the standard Gaussian probability measure
  on tangent fields `Good D → h^⊥` (`goodGaussian_univ`).
* `lintegral_matAct_good`: `∫ f(v) dv = |det C|^{N-1} ∫ f(Cψ) dψ`.
* `goodQuad_matAct`: `⟨Cψ, K_G Cψ⟩ = ∑_{x ∈ G} ‖ψ_x‖²`.
* `lintegral_good_gaussian_change`: for every `F ≥ 0`,
  `∫ F(v) exp(-½ ⟨v, K_G v⟩) dv = N_G ∫ F(Cψ) dγ_G(ψ)` with
  `N_G = kwGaussNorm = (2π)^{n_G/2} det(K_G)^{-(N-1)/2}`, `n_G = |G|(N-1)`.
* `kwGaussNorm_empty`: for `D = ∅` the normalizer is that of the landed full-torus theorem
  (`kf0GaussNorm`), the determinants being identified through the equivalence
  `Good ∅ ≃ Torus`.
* `kwGoodGaussian_instance`: `d = m = 3`, `ν = 1/8`, `D = {0}`.

NOT proved here: the sum over sectors with a common reference measure (H37.6), the linked
expansion and the one-scale theorem.

**Target (T4), not proved.**  For `D = siteUnion B` and a bad configuration `q`, the inner
good-spin integral `I_G(q, g)` of `kf0Sector_iterated` (an integral over `sigmaOut D`, the product
of the sphere measures over the good sites, of `goodWeight` times `exp(-β goodEnergy(glue q p) +
⟨g_G, p⟩)`) should equal `c_β^{|G|} det(K_G)^{-(N-1)/2} ∫ dγ_G(ψ)` of the indicator of the
hemisphere event, the chart Jacobian `∏_{x∈G} 1_{‖v_x‖²<β}(1 - ‖v_x‖²/β)^{-1/2}`, `goodWeight` and
`exp(-β (boundary + normal + interaction terms) + sources)` evaluated at `v = C_G ψ` (the
expansion `goodEnergy_expand` of the good energy into `½⟨v, K_G v⟩`, terms linear in `v` through
the crossing bonds to `q`, and the normal-component terms).  The lemmas missing for this are:
(i) the chart measure formula on a subset of sites: the product of the sphere measures over `G`
restricted to the product of open hemispheres equals `β^{-|G|(N-1)/2}` times the pushforward under
`v ↦ chartCfg` of Lebesgue measure on `Good D → h^⊥` with density `chartJac` (the landed
`lintegral_restrictedIntegrand` is for the index set `Torus d ℓ` only); (ii) the transfer of
`goodEnergy_expand` and of `sourceOut` to chart coordinates on `Good D` with the crossing-bond
terms depending on `q`; (iii) the hemisphere event is implied by `goodWeight`-support or by the
cutoffs, and the complement of the hemisphere product is accounted for.  None of these is in the
repository.

Source: `notes/phase1/KF0-HEAVY.md` §1 and §3.
-/

@[expose] public section

open Matrix MeasureTheory
open scoped MatrixOrder

namespace Balaban.LargeField

open SphereChart

open Balaban.Green

variable {d N m : ℕ} [NeZero m]

/-- The good sites `G = Dᶜ` as a type. -/
abbrev Good (D : Finset (Torus d m)) : Type := {x : Torus d m // x ∉ D}

section Sqrt

variable (ν : ℝ) (D : Finset (Torus d m))

theorem kwOpSub_posDef (hν : 0 < ν) : (kwOpSub d m ν D).PosDef :=
  (latticeLaplacian_posDef hν).submatrix Subtype.val_injective

/-- The positive definite square root `C_G` of `K_G⁻¹`, `K_G = kwOpSub d m ν D`, from Mathlib's
continuous-functional-calculus square root. -/
noncomputable def kwSqrt : Matrix (Good D) (Good D) ℝ :=
  CFC.sqrt (kwOpSub d m ν D)⁻¹

variable {ν} (hν : 0 < ν)
include hν

omit hν in
theorem kwSqrt_posSemidef : (kwSqrt ν D).PosSemidef :=
  Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg _)

theorem kwSqrt_mul_self : kwSqrt ν D * kwSqrt ν D = (kwOpSub d m ν D)⁻¹ :=
  CFC.sqrt_mul_sqrt_self _ (Matrix.nonneg_iff_posSemidef.mpr (kwOpSub_posDef ν D hν).inv.posSemidef)

omit hν in
theorem kwSqrt_transpose : (kwSqrt ν D)ᵀ = kwSqrt ν D := by
  have := (kwSqrt_posSemidef (d := d) (m := m) (ν := ν) D).isHermitian
  rw [← Matrix.conjTranspose_eq_transpose_of_trivial]
  exact this

theorem kwSqrt_det_sq : (kwSqrt ν D).det ^ 2 = ((kwOpSub d m ν D).det)⁻¹ := by
  have := congrArg Matrix.det (kwSqrt_mul_self (d := d) (m := m) D hν)
  rw [Matrix.det_mul, Matrix.det_nonsing_inv] at this
  rw [sq, this]
  exact Ring.inverse_eq_inv _

theorem kwSqrt_posDef : (kwSqrt ν D).PosDef := by
  have hdet : 0 < ((kwOpSub d m ν D).det)⁻¹ := inv_pos.2 (kwOpSub_posDef ν D hν).det_pos
  have hne : (kwSqrt ν D).det ≠ 0 := by
    intro h0
    have := kwSqrt_det_sq (d := d) (m := m) D hν
    rw [h0] at this
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow] at this
    rw [← this] at hdet
    exact lt_irrefl _ hdet
  exact (kwSqrt_posSemidef (d := d) (m := m) (ν := ν) D).posDef_iff_isUnit.2
    ((Matrix.isUnit_iff_isUnit_det _).2 hne.isUnit)

theorem kwSqrt_det_pos : 0 < (kwSqrt ν D).det := (kwSqrt_posDef (d := d) (m := m) D hν).det_pos

theorem kwSqrt_mul_mul : kwSqrt ν D * kwOpSub d m ν D * kwSqrt ν D = 1 := by
  set S := kwSqrt ν D
  set K := kwOpSub d m ν D
  have hKu : IsUnit K.det :=
    (Matrix.isUnit_iff_isUnit_det K).1 (kwOpSub_posDef ν D hν).isUnit
  have h1 : S * (S * K) = 1 := by
    rw [← Matrix.mul_assoc, kwSqrt_mul_self D hν]
    exact Matrix.nonsing_inv_mul K hKu
  exact mul_eq_one_comm.1 h1

theorem kwSqrt_det_pow (k : ℕ) :
    (kwSqrt ν D).det ^ k = (kwOpSub d m ν D).det ^ (-(k : ℝ) / 2) := by
  have hKpos : 0 < (kwOpSub d m ν D).det := (kwOpSub_posDef ν D hν).det_pos
  have hsq := kwSqrt_det_sq (d := d) (m := m) D hν
  have hSpos := kwSqrt_det_pos (d := d) (m := m) D hν
  have h1 : (kwSqrt ν D).det = (kwOpSub d m ν D).det ^ (-(1 / 2 : ℝ)) := by
    have h2 : ((kwOpSub d m ν D).det ^ (-(1 / 2 : ℝ))) ^ 2 = ((kwOpSub d m ν D).det)⁻¹ := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hKpos.le]
      norm_num
      exact Real.rpow_neg_one _
    have h3 : 0 < (kwOpSub d m ν D).det ^ (-(1 / 2 : ℝ)) := Real.rpow_pos_of_pos hKpos _
    nlinarith [sq_nonneg ((kwSqrt ν D).det - (kwOpSub d m ν D).det ^ (-(1 / 2 : ℝ))),
      sq_nonneg ((kwSqrt ν D).det + (kwOpSub d m ν D).det ^ (-(1 / 2 : ℝ)))]
  rw [h1, ← Real.rpow_natCast, ← Real.rpow_mul hKpos.le]
  congr 1
  ring

end Sqrt

/-! ### Tangent fields on the good sites -/

section Tangent

variable (D : Finset (Torus d m))

/-- The Lebesgue measure on the tangent fields `∏_{x ∈ G} h^⊥` of the good sites. -/
noncomputable abbrev goodVol (h : EuclideanSpace ℝ (Fin N)) : Measure (Good D → perp h) :=
  Measure.pi fun _ => (volume : Measure (perp h))

/-- The dimension `n_G = |G| (N - 1)` of the tangent fields of the good sites. -/
abbrev goodDim (N : ℕ) : ℕ := Fintype.card (Good D) * (N - 1)

/-- The standard Gaussian probability measure `(2π)^{-n_G/2} exp(-½ ∑_{x∈G} ‖ψ_x‖²) dψ` on the
tangent fields of the good sites. -/
noncomputable def goodGaussian (h : EuclideanSpace ℝ (Fin N)) : Measure (Good D → perp h) :=
  (goodVol D h).withDensity fun ψ =>
    ENNReal.ofReal ((2 * Real.pi) ^ (-(goodDim D N : ℝ) / 2) *
      Real.exp (-(1 / 2) * ∑ x : Good D, ‖ψ x‖ ^ 2))

/-- The quadratic form `⟨v, K_G v⟩ = ∑_i ⟨v^i, K_G v^i⟩` of a good-site tangent field. -/
noncomputable def goodQuad (ν : ℝ) {h : EuclideanSpace ℝ (Fin N)} (v : Good D → perp h) : ℝ :=
  ∑ i : Fin N, (fun x => ((v x : EuclideanSpace ℝ (Fin N)) i)) ⬝ᵥ
    kwOpSub d m ν D *ᵥ (fun x => ((v x : EuclideanSpace ℝ (Fin N)) i))

/-- The normalizer `N_G = (2π)^{n_G/2} det(K_G)^{-(N-1)/2}`. -/
noncomputable def kwGaussNorm (d m N : ℕ) [NeZero m] (ν : ℝ) (D : Finset (Torus d m)) : ℝ :=
  (2 * Real.pi) ^ ((goodDim D N : ℝ) / 2) *
    (kwOpSub d m ν D).det ^ (-((N - 1 : ℕ) : ℝ) / 2)

theorem kwGaussNorm_pos {ν : ℝ} (hν : 0 < ν) : 0 < kwGaussNorm d m N ν D :=
  mul_pos (Real.rpow_pos_of_pos (by positivity) _)
    (Real.rpow_pos_of_pos (kwOpSub_posDef ν D hν).det_pos _)

theorem lintegral_matAct_good {h : EuclideanSpace ℝ (Fin N)} (hh : ‖h‖ = 1)
    (S : Matrix (Good D) (Good D) ℝ) (hS : IsUnit S.det)
    (f : (Good D → perp h) → ENNReal) :
    ∫⁻ v, f v ∂(goodVol D h) =
      ENNReal.ofReal |S.det ^ (N - 1)| * ∫⁻ ψ, f (matAct S ψ) ∂(goodVol D h) := by
  have := lintegral_eq_ofReal_abs_det_mul (goodVol D h) (matActEquiv S hS) f
  rw [det_matActEquiv] at this
  have hr : Module.finrank ℝ (perp h) = N - 1 := by
    have := finrank_perp h hh; omega
  rw [hr] at this
  exact this

theorem coord_matAct_good {h : EuclideanSpace ℝ (Fin N)} (S : Matrix (Good D) (Good D) ℝ)
    (ψ : Good D → perp h) (x : Good D) (i : Fin N) :
    ((matAct S ψ x : perp h) : EuclideanSpace ℝ (Fin N)) i =
      (S *ᵥ fun y => ((ψ y : perp h) : EuclideanSpace ℝ (Fin N)) i) x := by
  simp [matAct, Matrix.mulVec, dotProduct]

/-- **The quadratic exponent in the new variables** (T3): if `S` is symmetric with
`S K_G S = 1` then `⟨Sψ, K_G Sψ⟩ = ∑_{x∈G} ‖ψ_x‖²`. -/
theorem goodQuad_matAct {h : EuclideanSpace ℝ (Fin N)} (ν : ℝ)
    {S : Matrix (Good D) (Good D) ℝ} (hSt : Sᵀ = S)
    (hSKS : S * kwOpSub d m ν D * S = 1) (ψ : Good D → perp h) :
    goodQuad D ν (matAct S ψ) = ∑ x : Good D, ‖ψ x‖ ^ 2 := by
  have hn : ∀ u : perp h, ‖u‖ ^ 2 = ∑ i : Fin N, ((u : EuclideanSpace ℝ (Fin N)) i) ^ 2 := by
    intro u
    rw [← norm_coe_perp, EuclideanSpace.norm_sq_eq]
    simp
  unfold goodQuad
  have hcoord : ∀ i : Fin N, (fun x => ((matAct S ψ x : perp h) : EuclideanSpace ℝ (Fin N)) i) =
      S *ᵥ fun y => ((ψ y : perp h) : EuclideanSpace ℝ (Fin N)) i := fun i => by
    funext x; exact coord_matAct_good D S ψ x i
  have hq : ∀ i : Fin N, (S *ᵥ fun y => ((ψ y : perp h) : EuclideanSpace ℝ (Fin N)) i) ⬝ᵥ
      kwOpSub d m ν D *ᵥ (S *ᵥ fun y => ((ψ y : perp h) : EuclideanSpace ℝ (Fin N)) i) =
      ∑ y, (((ψ y : perp h) : EuclideanSpace ℝ (Fin N)) i) ^ 2 := by
    intro i
    set w : Good D → ℝ := fun y => ((ψ y : perp h) : EuclideanSpace ℝ (Fin N)) i with hw
    have e1 : (S *ᵥ w) ⬝ᵥ kwOpSub d m ν D *ᵥ (S *ᵥ w) =
        w ⬝ᵥ (Sᵀ * kwOpSub d m ν D * S) *ᵥ w := by
      have hT : ∀ u : Good D → ℝ, (S *ᵥ w) ⬝ᵥ u = w ⬝ᵥ (Sᵀ *ᵥ u) := fun u => by
        rw [Matrix.dotProduct_transpose_mulVec, dotProduct_comm]
      rw [hT, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    rw [e1, hSt, hSKS, Matrix.one_mulVec]
    simp [dotProduct, sq, hw]
  simp only [hcoord, hq]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun x _ => (hn (ψ x)).symm

theorem lintegral_gauss_good {h : EuclideanSpace ℝ (Fin N)} (hh : ‖h‖ = 1) :
    ∫⁻ ψ, ENNReal.ofReal (Real.exp (-(1 / 2) * ∑ x : Good D, ‖ψ x‖ ^ 2)) ∂(goodVol D h) =
      ENNReal.ofReal ((2 * Real.pi) ^ ((goodDim D N : ℝ) / 2)) := by
  have e1 : ∀ ψ : Good D → perp h,
      ENNReal.ofReal (Real.exp (-(1 / 2) * ∑ x : Good D, ‖ψ x‖ ^ 2)) =
        ∏ x : Good D, ENNReal.ofReal (Real.exp (-(1 / 2) * ‖ψ x‖ ^ 2)) := by
    intro ψ
    rw [Finset.mul_sum, Real.exp_sum,
      ENNReal.ofReal_prod_of_nonneg (fun x _ => (Real.exp_pos _).le)]
  simp_rw [e1]
  have hmeas : Measurable fun u : perp h => ENNReal.ofReal (Real.exp (-(1 / 2) * ‖u‖ ^ 2)) :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (by fun_prop))
  rw [PiTools.lintegral_fintype_prod_eq_prod (Good D)
    (fun _ u => ENNReal.ofReal (Real.exp (-(1 / 2) * ‖u‖ ^ 2))) (fun _ => hmeas)]
  rw [Finset.prod_const, lintegral_gauss_perp hh, Finset.card_univ, ← ENNReal.ofReal_pow
    (Real.rpow_nonneg (by positivity) _), ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
  congr 2
  push_cast
  ring

/-- **The good-site tangent Gaussian is a probability measure.** -/
theorem goodGaussian_univ {h : EuclideanSpace ℝ (Fin N)} (hh : ‖h‖ = 1) :
    goodGaussian D h Set.univ = 1 := by
  unfold goodGaussian
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  have hc : ∀ ψ : Good D → perp h,
      ENNReal.ofReal ((2 * Real.pi) ^ (-(goodDim D N : ℝ) / 2) *
        Real.exp (-(1 / 2) * ∑ x : Good D, ‖ψ x‖ ^ 2)) =
      ENNReal.ofReal ((2 * Real.pi) ^ (-(goodDim D N : ℝ) / 2)) *
        ENNReal.ofReal (Real.exp (-(1 / 2) * ∑ x : Good D, ‖ψ x‖ ^ 2)) := fun ψ =>
    ENNReal.ofReal_mul (Real.rpow_nonneg (by positivity) _)
  simp_rw [hc]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_gauss_good D hh,
    ← ENNReal.ofReal_mul (Real.rpow_nonneg (by positivity) _), ← Real.rpow_add (by positivity)]
  have : -(goodDim D N : ℝ) / 2 + (goodDim D N : ℝ) / 2 = 0 := by ring
  rw [this, Real.rpow_zero, ENNReal.ofReal_one]

/-- **The Gaussian change of variables on the good region** `v = C_G ψ` (T2).  For `ν > 0`,
`|h| = 1` and every `F ≥ 0` on good-site tangent fields,
`∫ F(v) exp(-½⟨v, K_G v⟩) dv = N_G ∫ F(C_G ψ) dγ_G(ψ)`,
`N_G = (2π)^{n_G/2} det(K_G)^{-(N-1)/2}` (`kwGaussNorm`), `n_G = |G|(N-1)`, `C_G = kwSqrt`. -/
theorem lintegral_good_gaussian_change {h : EuclideanSpace ℝ (Fin N)} (hh : ‖h‖ = 1)
    {ν : ℝ} (hν : 0 < ν) (F : (Good D → perp h) → ENNReal) :
    ∫⁻ v, F v * ENNReal.ofReal (Real.exp (-(1 / 2) * goodQuad D ν v)) ∂(goodVol D h) =
      ENNReal.ofReal (kwGaussNorm d m N ν D) *
        ∫⁻ ψ, F (matAct (kwSqrt ν D) ψ) ∂(goodGaussian D h) := by
  set S := kwSqrt ν D with hS
  have hSpos : 0 < S.det := kwSqrt_det_pos (d := d) (m := m) D hν
  have hSu : IsUnit S.det := hSpos.ne'.isUnit
  rw [lintegral_matAct_good D hh S hSu]
  have hq : ∀ ψ : Good D → perp h,
      F (matAct S ψ) * ENNReal.ofReal (Real.exp (-(1 / 2) * goodQuad D ν (matAct S ψ))) =
      F (matAct S ψ) * ENNReal.ofReal (Real.exp (-(1 / 2) * ∑ x : Good D, ‖ψ x‖ ^ 2)) := by
    intro ψ
    rw [goodQuad_matAct D ν (kwSqrt_transpose (d := d) (m := m) (ν := ν) D)
      (kwSqrt_mul_mul D hν)]
  simp_rw [hq]
  set c₀ : ℝ := (2 * Real.pi) ^ (-(goodDim D N : ℝ) / 2) with hc₀
  have hc₀pos : 0 < c₀ := Real.rpow_pos_of_pos (by positivity) _
  have hγ : ∫⁻ ψ, F (matAct S ψ) ∂(goodGaussian D h) =
      ENNReal.ofReal c₀ * ∫⁻ ψ, F (matAct S ψ) *
        ENNReal.ofReal (Real.exp (-(1 / 2) * ∑ x : Good D, ‖ψ x‖ ^ 2)) ∂(goodVol D h) := by
    unfold goodGaussian
    rw [lintegral_withDensity_eq_lintegral_mul_non_measurable]
    · rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      refine lintegral_congr fun ψ => ?_
      simp only [Pi.mul_apply]
      rw [ENNReal.ofReal_mul hc₀pos.le]
      ring
    · exact ENNReal.measurable_ofReal.comp (by fun_prop)
    · exact ae_of_all _ fun ψ => ENNReal.ofReal_lt_top
  rw [hγ, ← mul_assoc, ← ENNReal.ofReal_mul (kwGaussNorm_pos D hν).le]
  congr 2
  have h2 : (2 * Real.pi) ^ ((goodDim D N : ℝ) / 2) * c₀ = 1 := by
    rw [hc₀, ← Real.rpow_add (by positivity)]
    have : (goodDim D N : ℝ) / 2 + -(goodDim D N : ℝ) / 2 = 0 := by ring
    rw [this, Real.rpow_zero]
  rw [abs_of_pos (pow_pos hSpos _), kwSqrt_det_pow D hν, kwGaussNorm, mul_right_comm, h2, one_mul]

end Tangent

/-! ### The case `D = ∅` and the instance -/

section Empty

/-- For `D = ∅` the good sites are all sites; the principal submatrix has the determinant of the
full operator. -/
theorem kwOpSub_empty_det (ν : ℝ) :
    (kwOpSub d m ν (∅ : Finset (Torus d m))).det = (latticeLaplacian d m ν).det := by
  let e : Good (∅ : Finset (Torus d m)) ≃ Torus d m :=
    Equiv.subtypeUnivEquiv (fun x => Finset.notMem_empty x)
  unfold kwOpSub
  have : (latticeLaplacian d m ν).submatrix (Subtype.val : Good (∅ : Finset (Torus d m)) → _)
      Subtype.val = (latticeLaplacian d m ν).submatrix e e := by ext i j; rfl
  rw [this, Matrix.det_submatrix_equiv_self]

/-- **The `D = ∅` case of the normalizer**: `N_∅ = kf0GaussNorm` of the landed full-torus theorem
(`lintegral_tangent_gaussian_change`), the index type `Good ∅` being identified with the torus
by `Equiv.subtypeUnivEquiv`. -/
theorem kwGaussNorm_empty (ν : ℝ) :
    kwGaussNorm d m N ν (∅ : Finset (Torus d m)) = kf0GaussNorm d m N ν := by
  have hc : Fintype.card (Good (∅ : Finset (Torus d m))) = Fintype.card (Torus d m) :=
    Fintype.card_congr (Equiv.subtypeUnivEquiv (fun x => Finset.notMem_empty x))
  unfold kwGaussNorm kf0GaussNorm goodDim tangentDim
  rw [kwOpSub_empty_det, hc]

end Empty

/-- **Non-vacuity** (T5): for `d = m = 3`, `ν = 1/8`, `D = {0}` the square root `C_G` exists with
all the stated identities, and the good-site Gaussian is a probability measure (`N = 2`). -/
theorem kwGoodGaussian_instance :
    (kwSqrt (d := 3) (m := 3) (1 / 8 : ℝ) kwInstD).PosDef ∧
    kwSqrt (d := 3) (m := 3) (1 / 8 : ℝ) kwInstD * kwSqrt (d := 3) (m := 3) (1 / 8 : ℝ) kwInstD =
      (kwOpSub 3 3 (1 / 8 : ℝ) kwInstD)⁻¹ ∧
    kwSqrt (d := 3) (m := 3) (1 / 8 : ℝ) kwInstD * kwOpSub 3 3 (1 / 8 : ℝ) kwInstD *
      kwSqrt (d := 3) (m := 3) (1 / 8 : ℝ) kwInstD = 1 ∧
    (kwSqrt (d := 3) (m := 3) (1 / 8 : ℝ) kwInstD).det ^ 2 =
      ((kwOpSub 3 3 (1 / 8 : ℝ) kwInstD).det)⁻¹ ∧
    0 < (kwSqrt (d := 3) (m := 3) (1 / 8 : ℝ) kwInstD).det ∧
    goodGaussian (N := 2) kwInstD (EuclideanSpace.single 0 1) Set.univ = 1 := by
  have hν : (0 : ℝ) < 1 / 8 := by norm_num
  refine ⟨kwSqrt_posDef kwInstD hν, kwSqrt_mul_self kwInstD hν, kwSqrt_mul_mul kwInstD hν,
    kwSqrt_det_sq kwInstD hν, kwSqrt_det_pos kwInstD hν, goodGaussian_univ _ ?_⟩
  simp

end Balaban.LargeField
