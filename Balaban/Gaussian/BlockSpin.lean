module

public import Balaban.Gaussian.Measure
public import Balaban.Gaussian.Schur
public import Balaban.Lattice.BlockAverage

/-!
# The Gaussian block-spin identity

Exact Gaussian integration of the fine field against the quadratic coupling to a block field
(Balaban's renormalization transformation, P1 §1 (1.11)-(1.12); composition E3 (3.8)).

Euclidean form (matrices over plain sums): for `A` positive definite, `Q : Matrix κ ι ℝ`, `a > 0`,
`M = A + a QᵀQ` and `Δ = a - a² Q M⁻¹ Qᵀ`,
`∫ exp(-(½ φᵀAφ + (a/2) ‖ψ - Qφ‖²)) dφ = Z(M) exp(-½ ψᵀΔψ)` with `Z(M) = (2π)^{n/2} (det M)^{-1/2}`
(`integral_blockSpin`), minimizer `φ* = M⁻¹ (a Qᵀ ψ)` (`blockSpin_completeSquare`,
`blockSpin_exponent_ge`), positivity of `Δ` (`Balaban.Gaussian.Schur`), composition of two steps
(`integral_blockSpin_comp`, `blockSpinOperator_comp_inv`).

Weighted form (`integral_blockSpin_weighted`): for the inner products `latticeInner w_f` on fine
and `latticeInner w_c` on block fields, `Q* = (w_c / w_f) Qᵀ`, and an operator `A_w` positive
definite, `Δ_w = a - a² Q (A_w + a Q*Q)⁻¹ Q*`; the lattice instance is
`blockAverageMatrix`/`blockPullback_eq_mulVec`.
-/

@[expose] public section

namespace Balaban

open Matrix MeasureTheory Complex
open scoped Real

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

omit [DecidableEq ι] [DecidableEq κ] in
theorem blockSpin_exponent (A : Matrix ι ι ℝ) (Q : Matrix κ ι ℝ) (a : ℝ) (ψ : κ → ℝ) (φ : ι → ℝ) :
    (1 / 2) * (φ ⬝ᵥ A *ᵥ φ) + (a / 2) * ∑ k, (ψ k - (Q *ᵥ φ) k) ^ 2 =
      (1 / 2) * (φ ⬝ᵥ blockSpinPrecision A Q a *ᵥ φ) - (∑ i, (a • (Qᵀ *ᵥ ψ)) i * φ i)
        + (a / 2) * (ψ ⬝ᵥ ψ) := by
  have h1 : φ ⬝ᵥ blockSpinPrecision A Q a *ᵥ φ = φ ⬝ᵥ A *ᵥ φ + a * ((Q *ᵥ φ) ⬝ᵥ (Q *ᵥ φ)) := by
    unfold blockSpinPrecision
    have h0 : φ ⬝ᵥ (Qᵀ *ᵥ (Q *ᵥ φ)) = (Q *ᵥ φ) ⬝ᵥ (Q *ᵥ φ) := by
      rw [dotProduct_comm, Matrix.mulVec_transpose, ← Matrix.dotProduct_mulVec]
    rw [Matrix.add_mulVec, dotProduct_add, Matrix.smul_mulVec, dotProduct_smul,
      ← Matrix.mulVec_mulVec, h0, smul_eq_mul]
  have h2 : ∑ i, (a • (Qᵀ *ᵥ ψ)) i * φ i = a * (ψ ⬝ᵥ (Q *ᵥ φ)) := by
    have : ∑ i, (a • (Qᵀ *ᵥ ψ)) i * φ i = (a • (Qᵀ *ᵥ ψ)) ⬝ᵥ φ := rfl
    rw [this, smul_dotProduct, Matrix.mulVec_transpose, ← Matrix.dotProduct_mulVec, smul_eq_mul]
  have h3 : ∑ k, (ψ k - (Q *ᵥ φ) k) ^ 2 =
      ψ ⬝ᵥ ψ - 2 * (ψ ⬝ᵥ (Q *ᵥ φ)) + (Q *ᵥ φ) ⬝ᵥ (Q *ᵥ φ) := by
    simp only [dotProduct, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => by ring
  rw [h1, h2, h3]; ring

theorem dotProduct_blockSpinOperator (A : Matrix ι ι ℝ) (Q : Matrix κ ι ℝ) (a : ℝ) (ψ : κ → ℝ) :
    ψ ⬝ᵥ blockSpinOperator A Q a *ᵥ ψ =
      a * (ψ ⬝ᵥ ψ) - a ^ 2 * ((Qᵀ *ᵥ ψ) ⬝ᵥ ((blockSpinPrecision A Q a)⁻¹ *ᵥ (Qᵀ *ᵥ ψ))) := by
  unfold blockSpinOperator
  have key : ψ ⬝ᵥ (Q * (blockSpinPrecision A Q a)⁻¹ * Qᵀ) *ᵥ ψ =
      (Qᵀ *ᵥ ψ) ⬝ᵥ ((blockSpinPrecision A Q a)⁻¹ *ᵥ (Qᵀ *ᵥ ψ)) := by
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
      Matrix.mulVec_transpose]
  rw [Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec, dotProduct_smul, Matrix.one_mulVec,
    Matrix.smul_mulVec, dotProduct_smul, key, smul_eq_mul, smul_eq_mul]

theorem integral_blockSpin {A : Matrix ι ι ℝ} (hA : A.PosDef) (Q : Matrix κ ι ℝ) {a : ℝ}
    (ha : 0 < a) (ψ : κ → ℝ) :
    ∫ φ : ι → ℝ, Real.exp (-((1 / 2) * (φ ⬝ᵥ A *ᵥ φ) + (a / 2) * ∑ k, (ψ k - (Q *ᵥ φ) k) ^ 2))
      = gaussianNormalization (blockSpinPrecision A Q a) *
          Real.exp (-((1 / 2) * (ψ ⬝ᵥ blockSpinOperator A Q a *ᵥ ψ))) := by
  set M := blockSpinPrecision A Q a with hMdef
  have hM : M.PosDef := blockSpinPrecision_posDef hA Q ha
  set u : ι → ℝ := Qᵀ *ᵥ ψ
  have h := integral_cexp_quadratic_form' M hM (fun i => (((a • u) i : ℝ) : ℂ))
  have hpt : ∀ φ : ι → ℝ, (((Real.exp (-((1 / 2) * (φ ⬝ᵥ A *ᵥ φ) + (a / 2) * ∑ k, (ψ k - (Q *ᵥ φ) k) ^ 2))) : ℝ) : ℂ) =
      cexp (-(1 / 2 : ℂ) * ((φ ⬝ᵥ M *ᵥ φ : ℝ) : ℂ) + ∑ i, (((a • u) i : ℝ) : ℂ) * (φ i : ℂ)) *
        cexp (-((a / 2 * (ψ ⬝ᵥ ψ) : ℝ) : ℂ)) := by
    intro φ
    rw [← Complex.exp_add, Complex.ofReal_exp]
    congr 1
    have := blockSpin_exponent A Q a ψ φ
    have hc := congrArg (fun r : ℝ => (r : ℂ)) this
    simp only [Complex.ofReal_add, Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_sum] at hc
    push_cast at hc ⊢
    have hu : u = Qᵀ *ᵥ ψ := rfl
    rw [← hu, ← hMdef] at hc
    rw [neg_add, ← sub_eq_add_neg] at *
    linear_combination (-1 : ℂ) * hc
  have hreal : (1 / 2 : ℝ) * (∑ i, ∑ j, (a • u) i * (M⁻¹ i j) * (a • u) j) - a / 2 * (ψ ⬝ᵥ ψ) =
      -((1 / 2) * (ψ ⬝ᵥ blockSpinOperator A Q a *ᵥ ψ)) := by
    rw [dotProduct_blockSpinOperator, ← hMdef]
    have : ∑ i, ∑ j, (a • u) i * (M⁻¹ i j) * (a • u) j = a ^ 2 * (u ⬝ᵥ (M⁻¹ *ᵥ u)) := by
      simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, Pi.smul_apply, smul_eq_mul]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
    rw [this]; ring
  have hI : ((∫ φ : ι → ℝ, Real.exp (-((1 / 2) * (φ ⬝ᵥ A *ᵥ φ) + (a / 2) * ∑ k, (ψ k - (Q *ᵥ φ) k) ^ 2)) : ℝ) : ℂ) =
      (gaussianNormalization M : ℂ) * cexp ((1 / 2 : ℂ) * ∑ i, ∑ j, (((a • u) i : ℝ) : ℂ) * ((M⁻¹ i j : ℝ) : ℂ) * (((a • u) j : ℝ) : ℂ)) * cexp (-((a / 2 * (ψ ⬝ᵥ ψ) : ℝ) : ℂ)) := by
    rw [← integral_complex_ofReal]
    simp_rw [hpt]
    rw [integral_mul_const, h]
  have hfin : (gaussianNormalization M : ℂ) * cexp ((1 / 2 : ℂ) * ∑ i, ∑ j, (((a • u) i : ℝ) : ℂ) * ((M⁻¹ i j : ℝ) : ℂ) * (((a • u) j : ℝ) : ℂ)) * cexp (-((a / 2 * (ψ ⬝ᵥ ψ) : ℝ) : ℂ)) =
      ((gaussianNormalization M * Real.exp (-((1 / 2) * (ψ ⬝ᵥ blockSpinOperator A Q a *ᵥ ψ))) : ℝ) : ℂ) := by
    rw [mul_assoc, ← Complex.exp_add]
    have hc := congrArg (fun r : ℝ => (r : ℂ)) hreal
    simp only [Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_sum, Complex.ofReal_neg] at hc
    push_cast at hc ⊢
    congr 2
  exact_mod_cast hI.trans hfin

/-- The minimizer `φ* = M⁻¹ (a Qᵀ ψ)`. -/
noncomputable def blockSpinMinimizer (A : Matrix ι ι ℝ) (Q : Matrix κ ι ℝ) (a : ℝ) (ψ : κ → ℝ) :
    ι → ℝ := (blockSpinPrecision A Q a)⁻¹ *ᵥ (a • (Qᵀ *ᵥ ψ))

/-- Completing the square. -/
theorem blockSpin_completeSquare {A : Matrix ι ι ℝ} (hA : A.PosDef) (Q : Matrix κ ι ℝ) {a : ℝ}
    (ha : 0 < a) (ψ : κ → ℝ) (φ : ι → ℝ) :
    (1 / 2) * (φ ⬝ᵥ A *ᵥ φ) + (a / 2) * ∑ k, (ψ k - (Q *ᵥ φ) k) ^ 2 =
      (1 / 2) * (ψ ⬝ᵥ blockSpinOperator A Q a *ᵥ ψ) +
        (1 / 2) * ((φ - blockSpinMinimizer A Q a ψ) ⬝ᵥ
          blockSpinPrecision A Q a *ᵥ (φ - blockSpinMinimizer A Q a ψ)) := by
  set M := blockSpinPrecision A Q a with hMdef
  have hM : M.PosDef := blockSpinPrecision_posDef hA Q ha
  have hMu : IsUnit M.det := isUnit_iff_ne_zero.mpr hM.det_pos.ne'
  set J : ι → ℝ := a • (Qᵀ *ᵥ ψ) with hJ
  have hsym : Mᵀ = M := by
    have := hM.isHermitian
    rwa [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] at this
  have hsymi : (M⁻¹)ᵀ = M⁻¹ := by rw [Matrix.transpose_nonsing_inv, hsym]
  have hMs : M *ᵥ blockSpinMinimizer A Q a ψ = J := by
    rw [blockSpinMinimizer, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hMu, Matrix.one_mulVec]
  have e1 := blockSpin_exponent A Q a ψ φ
  have e2 := dotProduct_blockSpinOperator A Q a ψ
  rw [e1, e2, ← hMdef]
  have hJd : ∑ i, (a • (Qᵀ *ᵥ ψ)) i * φ i = J ⬝ᵥ φ := rfl
  rw [hJd]
  have hq : (φ - blockSpinMinimizer A Q a ψ) ⬝ᵥ M *ᵥ (φ - blockSpinMinimizer A Q a ψ) =
      φ ⬝ᵥ M *ᵥ φ - 2 * (J ⬝ᵥ φ) + J ⬝ᵥ (M⁻¹ *ᵥ J) := by
    set s := blockSpinMinimizer A Q a ψ with hs
    have hsJ : s = M⁻¹ *ᵥ J := rfl
    have c1 : φ ⬝ᵥ M *ᵥ s = J ⬝ᵥ φ := by rw [hMs, dotProduct_comm]
    have c2 : s ⬝ᵥ M *ᵥ φ = J ⬝ᵥ φ := by
      rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hsym, hMs]
    have c3 : s ⬝ᵥ M *ᵥ s = J ⬝ᵥ (M⁻¹ *ᵥ J) := by rw [hMs, hsJ, dotProduct_comm]
    rw [Matrix.mulVec_sub, dotProduct_sub, sub_dotProduct, sub_dotProduct, c1, c2, c3]
    ring
  have hu : (a ^ 2) * ((Qᵀ *ᵥ ψ) ⬝ᵥ (M⁻¹ *ᵥ (Qᵀ *ᵥ ψ))) = J ⬝ᵥ (M⁻¹ *ᵥ J) := by
    rw [hJ, Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul]; simp [smul_eq_mul]; ring
  rw [hq, ← hu]; ring

/-- The minimum of the exponent over `φ` is attained exactly at `φ*`, with value `½⟨ψ, Δψ⟩`. -/
theorem blockSpin_exponent_ge {A : Matrix ι ι ℝ} (hA : A.PosDef) (Q : Matrix κ ι ℝ) {a : ℝ}
    (ha : 0 < a) (ψ : κ → ℝ) (φ : ι → ℝ) :
    (1 / 2) * (ψ ⬝ᵥ blockSpinOperator A Q a *ᵥ ψ) ≤
      (1 / 2) * (φ ⬝ᵥ A *ᵥ φ) + (a / 2) * ∑ k, (ψ k - (Q *ᵥ φ) k) ^ 2 ∧
    ((1 / 2) * (φ ⬝ᵥ A *ᵥ φ) + (a / 2) * ∑ k, (ψ k - (Q *ᵥ φ) k) ^ 2 =
        (1 / 2) * (ψ ⬝ᵥ blockSpinOperator A Q a *ᵥ ψ) ↔ φ = blockSpinMinimizer A Q a ψ) := by
  have hM := blockSpinPrecision_posDef hA Q ha
  rw [blockSpin_completeSquare hA Q ha]
  constructor
  · have := hM.posSemidef.dotProduct_mulVec_nonneg (φ - blockSpinMinimizer A Q a ψ)
    simp only [star_trivial] at this
    linarith
  · constructor
    · intro h
      have h0 : (φ - blockSpinMinimizer A Q a ψ) ⬝ᵥ blockSpinPrecision A Q a *ᵥ (φ - blockSpinMinimizer A Q a ψ) = 0 := by
        linarith
      by_contra hne
      have := hM.dotProduct_mulVec_pos (x := φ - blockSpinMinimizer A Q a ψ) (sub_ne_zero.mpr hne)
      simp only [star_trivial] at this
      linarith
    · intro h
      subst h
      simp

/-- Composition of two block-spin steps (E3 (3.8)): integrating out `φ` and then `ψ₁`. -/
theorem integral_blockSpin_comp {A : Matrix ι ι ℝ} (hA : A.PosDef) (Q₁ : Matrix κ ι ℝ) {a₁ : ℝ}
    (ha₁ : 0 < a₁) {κ₂ : Type*} [Fintype κ₂] [DecidableEq κ₂] (Q₂ : Matrix κ₂ κ ℝ) {a₂ : ℝ}
    (ha₂ : 0 < a₂) (ψ₂ : κ₂ → ℝ) :
    ∫ ψ₁ : κ → ℝ, (∫ φ : ι → ℝ, Real.exp (-((1 / 2) * (φ ⬝ᵥ A *ᵥ φ) +
        (a₁ / 2) * ∑ k, (ψ₁ k - (Q₁ *ᵥ φ) k) ^ 2))) *
        Real.exp (-((a₂ / 2) * ∑ k, (ψ₂ k - (Q₂ *ᵥ ψ₁) k) ^ 2))
      = gaussianNormalization (blockSpinPrecision A Q₁ a₁) *
        (gaussianNormalization (blockSpinPrecision (blockSpinOperator A Q₁ a₁) Q₂ a₂) *
          Real.exp (-((1 / 2) * (ψ₂ ⬝ᵥ blockSpinOperator (blockSpinOperator A Q₁ a₁) Q₂ a₂ *ᵥ ψ₂)))) := by
  have hΔ := blockSpinOperator_posDef hA Q₁ ha₁
  have step : ∀ ψ₁ : κ → ℝ, (∫ φ : ι → ℝ, Real.exp (-((1 / 2) * (φ ⬝ᵥ A *ᵥ φ) +
        (a₁ / 2) * ∑ k, (ψ₁ k - (Q₁ *ᵥ φ) k) ^ 2))) *
        Real.exp (-((a₂ / 2) * ∑ k, (ψ₂ k - (Q₂ *ᵥ ψ₁) k) ^ 2)) =
      gaussianNormalization (blockSpinPrecision A Q₁ a₁) *
        Real.exp (-((1 / 2) * (ψ₁ ⬝ᵥ blockSpinOperator A Q₁ a₁ *ᵥ ψ₁) +
          (a₂ / 2) * ∑ k, (ψ₂ k - (Q₂ *ᵥ ψ₁) k) ^ 2)) := by
    intro ψ₁
    rw [integral_blockSpin hA Q₁ ha₁, mul_assoc, ← Real.exp_add]
    congr 2
    ring
  simp_rw [step]
  rw [integral_const_mul, integral_blockSpin hΔ Q₂ ha₂]

/-- Composition of the operators: `Δ₂⁻¹ = a₂⁻¹ + a₁⁻¹ Q₂Q₂ᵀ + (Q₂Q₁) A⁻¹ (Q₂Q₁)ᵀ`. -/
theorem blockSpinOperator_comp_inv {A : Matrix ι ι ℝ} (hA : A.PosDef) (Q₁ : Matrix κ ι ℝ) {a₁ : ℝ}
    (ha₁ : 0 < a₁) {κ₂ : Type*} [Fintype κ₂] [DecidableEq κ₂] (Q₂ : Matrix κ₂ κ ℝ) {a₂ : ℝ}
    (ha₂ : 0 < a₂) :
    (blockSpinOperator (blockSpinOperator A Q₁ a₁) Q₂ a₂)⁻¹ =
      a₂⁻¹ • (1 : Matrix κ₂ κ₂ ℝ) + a₁⁻¹ • (Q₂ * Q₂ᵀ) + (Q₂ * Q₁) * A⁻¹ * (Q₂ * Q₁)ᵀ := by
  have hΔ := blockSpinOperator_posDef hA Q₁ ha₁
  have h1 : (blockSpinOperator (blockSpinOperator A Q₁ a₁) Q₂ a₂)⁻¹ =
      a₂⁻¹ • (1 : Matrix κ₂ κ₂ ℝ) + Q₂ * (blockSpinOperator A Q₁ a₁)⁻¹ * Q₂ᵀ := by
    rw [blockSpinOperator_eq_inv hΔ Q₂ ha₂]
    exact Matrix.nonsing_inv_nonsing_inv _
      (isUnit_iff_ne_zero.mpr (woodbury_posDef hΔ Q₂ ha₂).det_pos.ne')
  have h2 : (blockSpinOperator A Q₁ a₁)⁻¹ = a₁⁻¹ • (1 : Matrix κ κ ℝ) + Q₁ * A⁻¹ * Q₁ᵀ := by
    rw [blockSpinOperator_eq_inv hA Q₁ ha₁]
    exact Matrix.nonsing_inv_nonsing_inv _
      (isUnit_iff_ne_zero.mpr (woodbury_posDef hA Q₁ ha₁).det_pos.ne')
  rw [h1, h2]
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
    Matrix.transpose_mul, Matrix.mul_assoc, add_assoc]

/-- Weighted form (P1 (1.11)): `Q* = (w_c / w_f) Qᵀ` is the adjoint of `Q` for the inner products
`latticeInner w_f` on fine and `latticeInner w_c` on coarse fields. -/
noncomputable def weightedBlockSpinOperator (Aw : Matrix ι ι ℝ) (Q : Matrix κ ι ℝ) (Qs : Matrix ι κ ℝ)
    (a : ℝ) : Matrix κ κ ℝ :=
  a • (1 : Matrix κ κ ℝ) - (a ^ 2) • (Q * (Aw + a • (Qs * Q))⁻¹ * Qs)

theorem integral_blockSpin_weighted {Aw : Matrix ι ι ℝ} (Q : Matrix κ ι ℝ) (Qs : Matrix ι κ ℝ)
    {a wf wc : ℝ} (ha : 0 < a) (hwf : 0 < wf) (hwc : 0 < wc) (hQs : Qs = (wc / wf) • Qᵀ)
    (hA : Aw.PosDef) (ψ : κ → ℝ) :
    ∫ φ : ι → ℝ, Real.exp (-((1 / 2) * latticeInner wf φ (Aw *ᵥ φ) +
        (a / 2) * latticeInner wc (ψ - Q *ᵥ φ) (ψ - Q *ᵥ φ)))
      = gaussianNormalization (wf • Aw + (a * wc) • (Qᵀ * Q)) *
        Real.exp (-((1 / 2) * latticeInner wc ψ (weightedBlockSpinOperator Aw Q Qs a *ᵥ ψ))) := by
  have hA' : (wf • Aw).PosDef := hA.smul hwf
  have h := integral_blockSpin hA' Q (mul_pos ha hwc) ψ
  have hΔ : blockSpinOperator (wf • Aw) Q (a * wc) = wc • weightedBlockSpinOperator Aw Q Qs a := by
    have hM : Aw + a • (Qs * Q) = wf⁻¹ • blockSpinPrecision (wf • Aw) Q (a * wc) := by
      rw [hQs]
      simp only [blockSpinPrecision, smul_add, Matrix.smul_mul, smul_smul]
      congr 2
      · simp [hwf.ne']
      · field_simp
    have hMP := blockSpinPrecision_posDef hA' Q (mul_pos ha hwc)
    have hinv : (Aw + a • (Qs * Q))⁻¹ = wf • (blockSpinPrecision (wf • Aw) Q (a * wc))⁻¹ := by
      have : Invertible wf⁻¹ := invertibleOfNonzero (inv_ne_zero hwf.ne')
      rw [hM, Matrix.inv_smul _ _ (isUnit_iff_ne_zero.mpr hMP.det_pos.ne'), invOf_eq_inv, inv_inv]
    unfold blockSpinOperator weightedBlockSpinOperator
    rw [hinv, hQs]
    simp only [Matrix.mul_smul, Matrix.smul_mul, smul_smul, smul_sub]
    congr 1
    · congr 1; ring
    · congr 1
      field_simp
  have hq1 : ∀ φ : ι → ℝ, latticeInner wf φ (Aw *ᵥ φ) = φ ⬝ᵥ (wf • Aw) *ᵥ φ := by
    intro φ
    rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
    simp [latticeInner, dotProduct]
  have hq2 : ∀ φ : ι → ℝ, latticeInner wc (ψ - Q *ᵥ φ) (ψ - Q *ᵥ φ) =
      wc * ∑ k, (ψ k - (Q *ᵥ φ) k) ^ 2 := by
    intro φ
    simp [latticeInner, sq]
  have hq3 : latticeInner wc ψ (weightedBlockSpinOperator Aw Q Qs a *ᵥ ψ) =
      ψ ⬝ᵥ blockSpinOperator (wf • Aw) Q (a * wc) *ᵥ ψ := by
    rw [hΔ, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
    simp [latticeInner, dotProduct]
  simp_rw [hq1, hq2]
  rw [hq3]
  have hZ : gaussianNormalization (wf • Aw + (a * wc) • (Qᵀ * Q)) =
      gaussianNormalization (blockSpinPrecision (wf • Aw) Q (a * wc)) := rfl
  rw [hZ, ← h]
  congr 1
  funext φ
  congr 2
  ring

section Lattice

variable {d ℓ N m : ℕ} [NeZero ℓ] [NeZero m]

/-- The matrix of the block averaging `Q`. -/
noncomputable def blockAverageMatrix (N m : ℕ) : Matrix (Torus d m) (Torus d ℓ) ℝ :=
  fun y x => if blockMap N m x = y then ((N : ℝ) ^ d)⁻¹ else 0

omit [NeZero m] in
theorem blockAverage_eq_mulVec (φ : Torus d ℓ → ℝ) :
    blockAverage N m φ = blockAverageMatrix N m *ᵥ φ := by
  funext y
  simp only [blockAverage_apply, Matrix.mulVec, dotProduct, blockAverageMatrix, ite_mul, zero_mul]
  rw [← Finset.sum_filter, ← Finset.mul_sum]
  rfl

omit [NeZero ℓ] in
theorem blockPullback_eq_mulVec (hN : 0 < N) (ψ : Torus d m → ℝ) :
    (blockPullback N m ψ : Torus d ℓ → ℝ) =
      (((N : ℝ) ^ d) • (blockAverageMatrix N m : Matrix (Torus d m) (Torus d ℓ) ℝ)ᵀ) *ᵥ ψ := by
  have hNd : ((N : ℝ) ^ d) ≠ 0 := by positivity
  funext x
  simp [Matrix.mulVec, dotProduct, blockAverageMatrix, Matrix.smul_apply, blockPullback_apply, hNd]

end Lattice
end Balaban
