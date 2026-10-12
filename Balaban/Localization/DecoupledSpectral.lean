/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.DecoupledIntegral
public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

/-!
# The resolvent integrals for a positive definite matrix

For a positive definite `A` with spectral decomposition `A = U diag(λ) U*` and `f : ℝ → ℂ`, put
`specFun A f = U diag(f(λᵢ)) U*` (the functional calculus of the Hermitian matrix `A`). Then

* `resolvent_sqrt`: `π⁻¹ ∫₀^∞ x^{-1/2} (x + A)⁻¹ dx = specFun A (t ↦ t^{-1/2})`, a Hermitian positive
  definite matrix whose square is `A⁻¹` (the inverse square root);
* `resolvent_log`: `log a_k (1 - P) + log (a_k + b) P - ∫₀^∞ ((x + A)⁻¹ - (x + A₀)⁻¹) dx =
  specFun A log` for `A₀ = a_k + b P`, i.e. `𝕃 = log A`.
-/

@[expose] public section

open MeasureTheory Set Real Filter Topology Matrix
open scoped ComplexOrder

namespace Balaban.Localization

section Spec

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {A : Matrix ι ι ℂ}

/-- The functional calculus of a Hermitian matrix. -/
noncomputable def specFun (hA : A.IsHermitian) (f : ℝ → ℂ) : Matrix ι ι ℂ :=
  (hA.eigenvectorUnitary : Matrix ι ι ℂ) * Matrix.diagonal (fun i => f (hA.eigenvalues i)) *
    star (hA.eigenvectorUnitary : Matrix ι ι ℂ)

variable (hA : A.IsHermitian)

theorem specFun_congr {f g : ℝ → ℂ} (h : ∀ i, f (hA.eigenvalues i) = g (hA.eigenvalues i)) :
    specFun hA f = specFun hA g := by
  unfold specFun
  simp only [h]

theorem specFun_mul (f g : ℝ → ℂ) :
    specFun hA f * specFun hA g = specFun hA (fun t => f t * g t) := by
  have h : star (hA.eigenvectorUnitary : Matrix ι ι ℂ) * (hA.eigenvectorUnitary : Matrix ι ι ℂ) = 1 :=
    Unitary.coe_star_mul_self _
  have e : (specFun hA f * specFun hA g) =
      (hA.eigenvectorUnitary : Matrix ι ι ℂ) * (Matrix.diagonal (fun i => f (hA.eigenvalues i)) *
        (star (hA.eigenvectorUnitary : Matrix ι ι ℂ) * (hA.eigenvectorUnitary : Matrix ι ι ℂ)) *
        Matrix.diagonal (fun i => g (hA.eigenvalues i))) *
        star (hA.eigenvectorUnitary : Matrix ι ι ℂ) := by
    unfold specFun; simp only [Matrix.mul_assoc]
  rw [e, h, Matrix.mul_one, Matrix.diagonal_mul_diagonal]
  rfl

theorem specFun_one : specFun hA (fun _ => 1) = 1 := by
  unfold specFun
  rw [Matrix.diagonal_one]
  simp only [Matrix.mul_one]
  exact Unitary.coe_mul_star_self _

theorem specFun_self : specFun hA (fun t => (t : ℂ)) = A := by
  unfold specFun
  have := hA.spectral_theorem
  rw [Unitary.conjStarAlgAut_apply] at this
  exact this.symm

theorem specFun_add (f g : ℝ → ℂ) :
    specFun hA (fun t => f t + g t) = specFun hA f + specFun hA g := by
  have e : Matrix.diagonal (fun i => (f (hA.eigenvalues i) + g (hA.eigenvalues i))) =
      Matrix.diagonal (fun i => f (hA.eigenvalues i)) +
        Matrix.diagonal (fun i => g (hA.eigenvalues i)) := by
    rw [Matrix.diagonal_add]
  unfold specFun
  simp only [e, Matrix.mul_add, Matrix.add_mul]

theorem specFun_smul (c : ℂ) (f : ℝ → ℂ) :
    specFun hA (fun t => c * f t) = c • specFun hA f := by
  have e : Matrix.diagonal (fun i => c * f (hA.eigenvalues i)) =
      c • Matrix.diagonal (fun i => f (hA.eigenvalues i)) := by
    ext i j
    by_cases h : i = j <;> simp [h]
  unfold specFun
  simp only [e, Matrix.mul_smul, Matrix.smul_mul]

theorem specFun_apply (f : ℝ → ℂ) (p q : ι) :
    specFun hA f p q = ∑ i, (hA.eigenvectorUnitary : Matrix ι ι ℂ) p i * f (hA.eigenvalues i) *
      star ((hA.eigenvectorUnitary : Matrix ι ι ℂ) q i) := by
  unfold specFun
  rw [Matrix.mul_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.mul_diagonal]
  rfl

/-- The resolvent of a positive definite matrix in the spectral calculus. -/
theorem resolvent_eq_specFun (hP : A.PosDef) {x : ℝ} (hx : 0 ≤ x) :
    ((x : ℂ) • (1 : Matrix ι ι ℂ) + A)⁻¹ = specFun hP.isHermitian (fun t => ((x : ℂ) + t)⁻¹) := by
  have hH := hP.isHermitian
  have hne : ∀ i, ((x : ℂ) + (hH.eigenvalues i : ℂ)) ≠ 0 := by
    intro i
    have := hP.eigenvalues_pos i
    have : (0 : ℝ) < x + hH.eigenvalues i := by linarith
    exact_mod_cast this.ne'
  have h1 : (x : ℂ) • (1 : Matrix ι ι ℂ) + A = specFun hH (fun t => (x : ℂ) + t) := by
    rw [specFun_add hH (fun _ => (x : ℂ)) (fun t => (t : ℂ)), specFun_self hH]
    have := specFun_smul hH (x : ℂ) (fun _ => 1)
    simp only [mul_one] at this
    rw [this, specFun_one]
  refine Matrix.inv_eq_right_inv ?_
  rw [h1, specFun_mul, ← specFun_one hH]
  exact specFun_congr hH fun i => mul_inv_cancel₀ (hne i)

end Spec

/-! ### Integrals in the spectral calculus -/

section SpecIntegral

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {A : Matrix ι ι ℂ} (hA : A.IsHermitian)

theorem intMat_specFun (μ : Measure ℝ) (g : ℝ → ℝ → ℂ)
    (hg : ∀ i, Integrable (fun x => g x (hA.eigenvalues i)) μ) :
    intMat μ (fun x => specFun hA (g x)) = specFun hA (fun t => ∫ x, g x t ∂μ) := by
  ext p q
  unfold intMat
  simp only [specFun_apply]
  rw [integral_finsetSum]
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_mul_const, integral_const_mul]
  · intro i _
    exact ((hg i).const_mul _).mul_const _

theorem integrable_specFun_entry (μ : Measure ℝ) (g : ℝ → ℝ → ℂ)
    (hg : ∀ i, Integrable (fun x => g x (hA.eigenvalues i)) μ) (p q : ι) :
    Integrable (fun x => specFun hA (g x) p q) μ := by
  simp only [specFun_apply]
  exact integrable_finsetSum _ fun i _ => ((hg i).const_mul _).mul_const _

end SpecIntegral

/-- Spectral calculus of the two-block operator `a (1 - P) + (a + b) P`. -/
noncomputable def blockFun {ι : Type*} [Fintype ι] [DecidableEq ι] (c₁ c₂ : ℝ) (P : Matrix ι ι ℂ)
    (f : ℝ → ℂ) : Matrix ι ι ℂ :=
  f c₁ • (1 - P) + f c₂ • P

theorem blockFun_one {ι : Type*} [Fintype ι] [DecidableEq ι] (c₁ c₂ : ℝ) (P : Matrix ι ι ℂ) :
    blockFun c₁ c₂ P (fun _ => 1) = 1 := by
  unfold blockFun; simp

theorem blockFun_sub {ι : Type*} [Fintype ι] [DecidableEq ι] (c₁ c₂ : ℝ) (P : Matrix ι ι ℂ)
    (f g : ℝ → ℂ) :
    blockFun c₁ c₂ P (fun t => f t - g t) = blockFun c₁ c₂ P f - blockFun c₁ c₂ P g := by
  unfold blockFun
  module

theorem blockFun_smul {ι : Type*} [Fintype ι] [DecidableEq ι] (c₁ c₂ : ℝ) (P : Matrix ι ι ℂ)
    (c : ℂ) (f : ℝ → ℂ) :
    blockFun c₁ c₂ P (fun t => c * f t) = c • blockFun c₁ c₂ P f := by
  unfold blockFun
  module

theorem blockFun_apply {ι : Type*} [Fintype ι] [DecidableEq ι] (c₁ c₂ : ℝ) (P : Matrix ι ι ℂ)
    (f : ℝ → ℂ) (p q : ι) :
    blockFun c₁ c₂ P f p q = f c₁ * (1 - P) p q + f c₂ * P p q := by
  unfold blockFun
  simp

theorem intMat_blockFun {ι : Type*} [Fintype ι] [DecidableEq ι] (μ : Measure ℝ) (c₁ c₂ : ℝ)
    (P : Matrix ι ι ℂ) (g : ℝ → ℝ → ℂ) (h1 : Integrable (fun x => g x c₁) μ)
    (h2 : Integrable (fun x => g x c₂) μ) :
    intMat μ (fun x => blockFun c₁ c₂ P (g x)) = blockFun c₁ c₂ P (fun t => ∫ x, g x t ∂μ) := by
  ext p q
  unfold intMat
  simp only [blockFun_apply]
  rw [integral_add (h1.mul_const _) (h2.mul_const _), integral_mul_const, integral_mul_const]

theorem integrable_blockFun_entry {ι : Type*} [Fintype ι] [DecidableEq ι] (μ : Measure ℝ)
    (c₁ c₂ : ℝ) (P : Matrix ι ι ℂ) (g : ℝ → ℝ → ℂ) (h1 : Integrable (fun x => g x c₁) μ)
    (h2 : Integrable (fun x => g x c₂) μ) (p q : ι) :
    Integrable (fun x => blockFun c₁ c₂ P (g x) p q) μ := by
  simp only [blockFun_apply]
  exact (h1.mul_const _).add (h2.mul_const _)


section Sqrt

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {A : Matrix ι ι ℂ}

theorem resolvent_sqrt (hP : A.PosDef) :
    intMat (volume.restrict (Ioi (0 : ℝ)))
        (fun x => ((x ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) • ((x : ℂ) • (1 : Matrix ι ι ℂ) + A)⁻¹) =
      specFun hP.isHermitian (fun t => ((π / Real.sqrt t : ℝ) : ℂ)) := by
  have hH := hP.isHermitian
  set g : ℝ → ℝ → ℂ := fun x t => ((x ^ (-(1 / 2 : ℝ)) * (t + x)⁻¹ : ℝ) : ℂ) with hg
  have step1 : ∀ x ∈ Ioi (0 : ℝ),
      ((x ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) • ((x : ℂ) • (1 : Matrix ι ι ℂ) + A)⁻¹ =
        specFun hH (g x) := by
    intro x hx
    rw [resolvent_eq_specFun hP (mem_Ioi.mp hx).le, ← specFun_smul]
    congr 1
    funext t
    simp only [hg]
    push_cast
    rw [add_comm (x : ℂ) (t : ℂ), div_eq_mul_inv]
  have step2 : intMat (volume.restrict (Ioi (0 : ℝ)))
      (fun x => ((x ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) • ((x : ℂ) • (1 : Matrix ι ι ℂ) + A)⁻¹) =
      intMat (volume.restrict (Ioi (0 : ℝ))) (fun x => specFun hH (g x)) := by
    ext p q
    unfold intMat
    refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
    simp only [step1 x hx]
  rw [step2]
  have hint : ∀ i, Integrable (fun x => g x (hH.eigenvalues i)) (volume.restrict (Ioi (0 : ℝ))) :=
    fun i => (integrableOn_rpow_inv_add (hP.eigenvalues_pos i)).ofReal
  rw [intMat_specFun hH _ g hint]
  refine specFun_congr hH fun i => ?_
  have hpos := hP.eigenvalues_pos i
  simp only [hg]
  rw [integral_complex_ofReal, integral_rpow_inv_add hpos]

/-- **The positive inverse square root** `A^{-1/2}` of a positive definite matrix. -/
noncomputable def invSqrtMat (hP : A.PosDef) : Matrix ι ι ℂ :=
  specFun hP.isHermitian (fun t => (((Real.sqrt t)⁻¹ : ℝ) : ℂ))

theorem posDef_specFun_real (hH : A.IsHermitian) {f : ℝ → ℝ}
    (hf : ∀ i, 0 < f (hH.eigenvalues i)) : (specFun hH (fun t => (f t : ℂ))).PosDef := by
  unfold specFun
  rw [Matrix.IsUnit.posDef_star_right_conjugate_iff Unitary.isUnit_coe, Matrix.posDef_diagonal_iff]
  intro i
  show (0 : ℂ) < ((f (hH.eigenvalues i) : ℝ) : ℂ)
  exact_mod_cast hf i

theorem invSqrtMat_posDef (hP : A.PosDef) : (invSqrtMat hP).PosDef :=
  posDef_specFun_real hP.isHermitian fun i =>
    inv_pos.2 (Real.sqrt_pos.2 (hP.eigenvalues_pos i))

theorem inv_eq_specFun (hP : A.PosDef) :
    A⁻¹ = specFun hP.isHermitian (fun t => ((t⁻¹ : ℝ) : ℂ)) := by
  have hH := hP.isHermitian
  have h := specFun_mul hH (fun t => (t : ℂ)) (fun t => ((t⁻¹ : ℝ) : ℂ))
  rw [specFun_self hH] at h
  refine Matrix.inv_eq_right_inv (h.trans ?_)
  rw [← specFun_one hH]
  refine specFun_congr hH fun i => ?_
  have := (hP.eigenvalues_pos i).ne'
  push_cast
  field_simp

theorem invSqrtMat_mul_self (hP : A.PosDef) : invSqrtMat hP * invSqrtMat hP = A⁻¹ := by
  rw [invSqrtMat, specFun_mul, inv_eq_specFun hP]
  refine specFun_congr hP.isHermitian fun i => ?_
  have hpos := hP.eigenvalues_pos i
  push_cast
  rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt hpos.le]

/-- **The resolvent integral for the square root**: `π⁻¹ ∫₀^∞ x^{-1/2} (x + A)⁻¹ dx = A^{-1/2}`. -/
theorem resolvent_sqrt_eq (hP : A.PosDef) :
    ((1 / π : ℝ) : ℂ) • intMat (volume.restrict (Ioi (0 : ℝ)))
        (fun x => ((x ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) • ((x : ℂ) • (1 : Matrix ι ι ℂ) + A)⁻¹) =
      invSqrtMat hP := by
  rw [resolvent_sqrt hP, ← specFun_smul]
  refine specFun_congr hP.isHermitian fun i => ?_
  have hpi : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_pos.ne'
  push_cast
  field_simp

end Sqrt

section Log

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {A : Matrix ι ι ℂ}

omit [Fintype ι] [DecidableEq ι] in
theorem intMat_sub' {μ : Measure ℝ} {F H : ℝ → Matrix ι ι ℂ}
    (hF : ∀ p q, Integrable (fun x => F x p q) μ) (hH : ∀ p q, Integrable (fun x => H x p q) μ) :
    intMat μ (fun x => F x - H x) = intMat μ F - intMat μ H := by
  ext p q
  unfold intMat
  simp only [Matrix.sub_apply]
  exact integral_sub (hF p q) (hH p q)

theorem blockFun_add_const {c₁ c₂ : ℝ} (P : Matrix ι ι ℂ) (f : ℝ → ℂ) (s : ℂ) :
    blockFun c₁ c₂ P (fun t => f t + s) = blockFun c₁ c₂ P f + s • (1 : Matrix ι ι ℂ) := by
  unfold blockFun
  module

theorem resolvent_log (hP : A.PosDef) {c₁ c₂ : ℝ} (hc₁ : 0 < c₁) (hc₂ : 0 < c₂)
    (Pm : Matrix ι ι ℂ) :
    blockFun c₁ c₂ Pm (fun t => (Real.log t : ℂ)) -
        intMat (volume.restrict (Ioi (0 : ℝ)))
          (fun x => ((x : ℂ) • (1 : Matrix ι ι ℂ) + A)⁻¹ -
            blockFun c₁ c₂ Pm (fun t => ((t : ℂ) + x)⁻¹)) =
      specFun hP.isHermitian (fun t => (Real.log t : ℂ)) := by
  have hH := hP.isHermitian
  set μ := volume.restrict (Ioi (0 : ℝ)) with hμ
  set g : ℝ → ℝ → ℂ := fun x t => (((t + x)⁻¹ - (1 + x)⁻¹ : ℝ) : ℂ) with hg
  have step1 : ∀ x ∈ Ioi (0 : ℝ), ((x : ℂ) • (1 : Matrix ι ι ℂ) + A)⁻¹ -
      blockFun c₁ c₂ Pm (fun t => ((t : ℂ) + x)⁻¹) = specFun hH (g x) - blockFun c₁ c₂ Pm (g x) := by
    intro x hx
    rw [resolvent_eq_specFun hP (mem_Ioi.mp hx).le]
    have e1 : (fun t : ℝ => ((x : ℂ) + t)⁻¹) = fun t => g x t + ((1 + x)⁻¹ : ℝ) := by
      funext t; simp only [hg]; push_cast; rw [add_comm (x : ℂ) (t : ℂ)]; ring
    have e2 : (fun t : ℝ => ((t : ℂ) + x)⁻¹) = fun t => g x t + ((1 + x)⁻¹ : ℝ) := by
      funext t; simp only [hg]; push_cast; ring
    rw [e1, e2, specFun_add hH, blockFun_add_const]
    have : specFun hH (fun _ => (((1 + x)⁻¹ : ℝ) : ℂ)) = (((1 + x)⁻¹ : ℝ) : ℂ) • (1 : Matrix ι ι ℂ) := by
      have := specFun_smul hH (((1 + x)⁻¹ : ℝ) : ℂ) (fun _ => 1)
      simp only [mul_one] at this
      rw [this, specFun_one]
    rw [this]
    abel
  have hint : ∀ t : ℝ, 0 < t → Integrable (fun x => g x t) μ := fun t ht =>
    (integrableOn_inv_add_sub ht one_pos).ofReal
  have hval : ∀ t : ℝ, 0 < t → ∫ x, g x t ∂μ = -(Real.log t : ℂ) := by
    intro t ht
    simp only [hg]
    rw [integral_complex_ofReal, hμ, integral_inv_add_sub ht one_pos]
    push_cast
    simp
  have hI : ∀ i, Integrable (fun x => g x (hH.eigenvalues i)) μ :=
    fun i => hint _ (hP.eigenvalues_pos i)
  have hc1 := hint c₁ hc₁
  have hc2 := hint c₂ hc₂
  have step2 : intMat μ (fun x => ((x : ℂ) • (1 : Matrix ι ι ℂ) + A)⁻¹ -
      blockFun c₁ c₂ Pm (fun t => ((t : ℂ) + x)⁻¹)) =
      intMat μ (fun x => specFun hH (g x) - blockFun c₁ c₂ Pm (g x)) := by
    ext p q
    unfold intMat
    refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
    simp only [step1 x hx]
  rw [step2, intMat_sub' (integrable_specFun_entry hH μ g hI)
    (integrable_blockFun_entry μ c₁ c₂ Pm g hc1 hc2),
    intMat_specFun hH μ g hI, intMat_blockFun μ c₁ c₂ Pm g hc1 hc2]
  have e1 : specFun hH (fun t => ∫ x, g x t ∂μ) = (-1 : ℂ) • specFun hH (fun t => (Real.log t : ℂ)) := by
    rw [← specFun_smul]
    exact specFun_congr hH fun i => by rw [hval _ (hP.eigenvalues_pos i)]; ring
  have e2 : blockFun c₁ c₂ Pm (fun t => ∫ x, g x t ∂μ) =
      (-1 : ℂ) • blockFun c₁ c₂ Pm (fun t => (Real.log t : ℂ)) := by
    unfold blockFun
    simp only []
    rw [hval c₁ hc₁, hval c₂ hc₂]
    module
  rw [e1, e2]
  module

end Log

end Balaban.Localization
