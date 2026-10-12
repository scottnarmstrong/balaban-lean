/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.CovarianceSpectral

/-!
# Lemma 2.4: the covariance `C^{(k)} = (a L⁻² Q*Q + Δ^{(k)})⁻¹` (FLUCTUATION.md §2.4)

Everything is stated for the concrete unit lattice (`unitQ`, `unitP`) and the operator
`𝒜 = covOp … = a L⁻² Q*Q + Δ^{(k)}`, under the premises of Theorem I-4c (the family of x-variant
data, the constraint field, the smallness of `δ`).

* `lemma24_a` (real data): `𝒜` is positive definite with `Re ⟨v, 𝒜 v⟩ ≥ covGap ‖v‖²`;
* `lemma24_b`, `lemma24_b_resolvent`: `𝒜` is invertible, its inverse and all the resolvents
  `(x + 𝒜)⁻¹` have exponentially decaying kernels, uniformly in `x ≥ 0` (complex data allowed);
* `lemma24_c_principal`, `lemma24_c_real`, `lemma24_c_l2`, `lemma24_c_sup`, `lemma24_c_logdet`:
  `C^{1/2}` is the principal square root, with `ℓ²` and `ℓ^∞` bounds, and the determinant identity;
* `lemma24_d`, `lemma24_d_identification`: the resolvent identity and the identification with the
  decoupled objects of Theorem I-4c at `s = 1`.
-/

@[expose] public section

open Balaban Balaban.Localization Balaban.Multiscale Matrix
open scoped ComplexOrder

namespace Balaban.Fluctuation


variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
  {G : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
  {a : ℕ → ℝ} {aT ν : ℝ} {α : G.Ω 1 → ℂ} {δ : ℝ}
  {φ : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ}

/-- The gap constant of Lemma 2.4 (a). -/
noncomputable def covGap (d L : ℕ) (ak : ℝ) : ℝ :=
  (ak⁻¹ + covB4 d L ak 0 * (ak⁻¹) ^ 2)⁻¹

theorem covOp_inv_eq (hfam : ∀ x, 0 ≤ x → XData G a aT ν x α 0 (fun _ => 1))
    (hφ : IsConstraintField G δ φ) (hδ : 0 ≤ δ) (hsm : δ ^ 2 * smallConstX d L 0 ≤ 1 / 4) :
    IsUnit (covOp G a aT ν α φ (unitQ G) (unitP G)) ∧
      decCov G a aT 0 ν α (fun _ => 1) φ (unitQ G) (unitP G) =
        (covOp G a aT ν α φ (unitQ G) (unitP G))⁻¹ := by
  have h := decCov_one_eq hfam hφ hδ hsm (isUnitLatticeB_unit (G := G)) (le_refl (0 : ℝ))
  simpa using h

/-- **Lemma 2.4 (a)** (real data). -/
theorem lemma24_a (hfam : ∀ x, 0 ≤ x → XData G a aT ν x α 0 (fun _ => 1))
    (hφ : IsConstraintField G δ φ) (hδ : 0 ≤ δ) (hsm : δ ^ 2 * smallConstX d L 0 ≤ 1 / 4)
    (hα : ∀ w, star (α w) = α w) (hφr : ∀ y i, star (φ y i) = φ y i) :
    (covOp G a aT ν α φ (unitQ G) (unitP G)).PosDef ∧ 0 < covGap d L (a k) ∧
      Green.IsCoercive (covOp G a aT ν α φ (unitQ G) (unitP G)) (covGap d L (a k)) := by
  have hU := isUnitLatticeB_unit (G := G)
  have hP := covOp_posDef_of_real hfam hφ hδ hsm hU hα (fun b y => unitQ_real G b y) hφr
  obtain ⟨H, -⟩ := standing_pair hfam hφ hδ hsm
  have hak := H.hak
  have hB4 := covB4_nonneg d L (a k) 0
  have hBpos : 0 < (a k)⁻¹ + covB4 d L (a k) 0 * ((a k)⁻¹) ^ 2 := by positivity
  have hgap : 0 < covGap d L (a k) := inv_pos.2 hBpos
  refine ⟨hP, hgap, fun v => ?_⟩
  have hC := (covOp_inv_eq hfam hφ hδ hsm).2
  have hB : ∀ f, n2 ((covOp G a aT ν α φ (unitQ G) (unitP G))⁻¹ *ᵥ f) ≤
      ((a k)⁻¹ + covB4 d L (a k) 0 * ((a k)⁻¹) ^ 2) * n2 f := by
    intro f
    have := H.decCov_le (le_refl (0 : ℝ)) f
    rw [hC, add_zero] at this
    exact (sqNorm_le_iff hBpos.le).1 this
  have key := cov_gap_aux hP hBpos.le hB v
  unfold covGap
  rw [inv_mul_le_iff₀ hBpos]
  exact key


/-- The prefactor of the kernel decay of `C^{(k)}` (Lemma 2.4 (b)). -/
noncomputable def covInvConst (d L : ℕ) (ak : ℝ) : ℝ :=
  covDecayConst d L ak (xAgmonRate d L) * Real.exp (xAgmonRate d L * d / L) * ak⁻¹

/-- **Lemma 2.4 (b)**: `𝒜` is invertible and the kernel of `C^{(k)} = 𝒜⁻¹` decays exponentially
in the `ℓ¹` distance of the unit torus, at the rate `xAgmonRate d L / L`. -/
theorem lemma24_b (hfam : ∀ x, 0 ≤ x → XData G a aT ν x α 0 (fun _ => 1))
    (hφ : IsConstraintField G δ φ) (hδ : 0 ≤ δ) (hsm : δ ^ 2 * smallConstX d L 0 ≤ 1 / 4) :
    IsUnit (covOp G a aT ν α φ (unitQ G) (unitP G)) ∧
      ∀ (p q : unitPts G) (i i' : Fin N),
        ‖(covOp G a aT ν α φ (unitQ G) (unitP G))⁻¹ (p, i) (q, i')‖ ≤
          covInvConst d L (a k) * Real.exp (-(xAgmonRate d L / L) *
            Green.torusDist d ((N₁ * L ^ m₁) * L ^ (k + 1 - k)) p.1 q.1) := by
  obtain ⟨hU, hC⟩ := covOp_inv_eq hfam hφ hδ hsm
  refine ⟨hU, fun p q i i' => ?_⟩
  have := cov_entry_decay hfam hφ hδ hsm (le_refl (0 : ℝ)) p q i i'
  rw [hC, add_zero] at this
  unfold covInvConst
  calc _ ≤ _ := this
    _ = _ := by ring

/-- **Lemma 2.4 (b), resolvent form**: the same decay for `(x + 𝒜)⁻¹`, uniformly in `x ≥ 0`, with
the prefactor `(a_k + x)⁻¹`. -/
theorem lemma24_b_resolvent (hfam : ∀ x, 0 ≤ x → XData G a aT ν x α 0 (fun _ => 1))
    (hφ : IsConstraintField G δ φ) (hδ : 0 ≤ δ) (hsm : δ ^ 2 * smallConstX d L 0 ≤ 1 / 4)
    {x : ℝ} (hx : 0 ≤ x) (p q : unitPts G) (i i' : Fin N) :
    ‖((x : ℂ) • (1 : Matrix (unitPts G × Fin N) (unitPts G × Fin N) ℂ) +
        covOp G a aT ν α φ (unitQ G) (unitP G))⁻¹ (p, i) (q, i')‖ ≤
      covDecayConst d L (a k) (xAgmonRate d L) * Real.exp (xAgmonRate d L * d / L) *
        (a k + x)⁻¹ * Real.exp (-(xAgmonRate d L / L) *
          Green.torusDist d ((N₁ * L ^ m₁) * L ^ (k + 1 - k)) p.1 q.1) := by
  have := cov_entry_decay hfam hφ hδ hsm hx p q i i'
  rw [(decCov_one_eq hfam hφ hδ hsm (isUnitLatticeB_unit (G := G)) hx).2] at this
  exact this

/-- **Lemma 2.4 (c), square root, principal.** `C^{(k)1/2}` (the resolvent integral) squares to
`C^{(k)}`, commutes with `𝒜` and has all eigenvalues in `Re > 0`; for real data it is the positive
inverse square root. -/
theorem lemma24_c_principal (hfam : ∀ x, 0 ≤ x → XData G a aT ν x α 0 (fun _ => 1))
    (hφ : IsConstraintField G δ φ) (hδ : 0 ≤ δ) (hsm : δ ^ 2 * smallConstX d L 0 ≤ 1 / 4) :
    decCovSqrt G a aT ν α (fun _ => 1) φ (unitQ G) (unitP G) =
        sqrtMat (covOp G a aT ν α φ (unitQ G) (unitP G)) ∧
      sqrtMat (covOp G a aT ν α φ (unitQ G) (unitP G)) *
          sqrtMat (covOp G a aT ν α φ (unitQ G) (unitP G)) =
        (covOp G a aT ν α φ (unitQ G) (unitP G))⁻¹ ∧
      sqrtMat (covOp G a aT ν α φ (unitQ G) (unitP G)) * covOp G a aT ν α φ (unitQ G) (unitP G) =
        covOp G a aT ν α φ (unitQ G) (unitP G) *
          sqrtMat (covOp G a aT ν α φ (unitQ G) (unitP G)) ∧
      ∀ (μ : ℂ) (v : unitPts G × Fin N → ℂ), v ≠ 0 →
        sqrtMat (covOp G a aT ν α φ (unitQ G) (unitP G)) *ᵥ v = μ • v → 0 < μ.re := by
  have hU := isUnitLatticeB_unit (G := G)
  have h1 := decCovSqrt_one_principal hfam hφ hδ hsm hU
  have h2 := decCovSqrt_one_eq_sqrtMat hfam hφ hδ hsm hU
  have hC := (covOp_inv_eq hfam hφ hδ hsm).2
  rw [hC, h2] at h1
  exact ⟨h2, h1⟩


/-- **Lemma 2.4 (c), real data**: `C^{(k)1/2}` is the positive inverse square root of `𝒜`. -/
theorem lemma24_c_real (hfam : ∀ x, 0 ≤ x → XData G a aT ν x α 0 (fun _ => 1))
    (hφ : IsConstraintField G δ φ) (hδ : 0 ≤ δ) (hsm : δ ^ 2 * smallConstX d L 0 ≤ 1 / 4)
    (hα : ∀ w, star (α w) = α w) (hφr : ∀ y i, star (φ y i) = φ y i) :
    decCovSqrt G a aT ν α (fun _ => 1) φ (unitQ G) (unitP G) =
      invSqrtMat (lemma24_a hfam hφ hδ hsm hα hφr).1 := by
  have := decCovSqrt_one_eq_real hfam hφ hδ hsm (isUnitLatticeB_unit (G := G)) hα
    (fun b y => unitQ_real G b y) hφr
  exact this

/-- **Lemma 2.4 (c), the `ℓ²` bound**: `‖C^{(k)1/2} v‖₂ ≤ B₅ ‖v‖₂`, `B₅ = covB5 d L (a_k) 0`. -/
theorem lemma24_c_l2 (hfam : ∀ x, 0 ≤ x → XData G a aT ν x α 0 (fun _ => 1))
    (hφ : IsConstraintField G δ φ) (hδ : 0 ≤ δ) (hsm : δ ^ 2 * smallConstX d L 0 ≤ 1 / 4)
    (v : unitPts G × Fin N → ℂ) :
    Green.sqNorm (decCovSqrt G a aT ν α (fun _ => 1) φ (unitQ G) (unitP G) *ᵥ v) ≤
      (covB5 d L (a k) 0) ^ 2 * Green.sqNorm v :=
  decCovSqrt_bound (standing_pair hfam hφ hδ hsm).1 v

/-- **Lemma 2.4 (c), the `ℓ^∞` bound** (Finding F-5): if `|v(p)| ≤ c` for all `p` then
`|(C^{(k)1/2} v)(p)| ≤ B_∞ c`, `B_∞ = covSupConst d L N (a_k)`. -/
theorem lemma24_c_sup (hfam : ∀ x, 0 ≤ x → XData G a aT ν x α 0 (fun _ => 1))
    (hφ : IsConstraintField G δ φ) (hδ : 0 ≤ δ) (hsm : δ ^ 2 * smallConstX d L 0 ≤ 1 / 4)
    (v : unitPts G × Fin N → ℂ) {c : ℝ} (hc : 0 ≤ c) (hv : ∀ p, ‖v p‖ ≤ c)
    (p : unitPts G × Fin N) :
    ‖(decCovSqrt G a aT ν α (fun _ => 1) φ (unitQ G) (unitP G) *ᵥ v) p‖ ≤
      covSupConst d L N (a k) * c :=
  cov_sqrt_supNorm hfam hφ hδ hsm v hc hv p

/-- **Lemma 2.4 (c), logarithm and determinant** (real data): with
`𝕃 = decLog = log 𝒜`, `det C^{(k)} > 0` and `½ log det C^{(k)} = -½ ∑_y tr 𝕃(y,y)`
(the trace is real). -/
theorem lemma24_c_logdet (hfam : ∀ x, 0 ≤ x → XData G a aT ν x α 0 (fun _ => 1))
    (hφ : IsConstraintField G δ φ) (hδ : 0 ≤ δ) (hsm : δ ^ 2 * smallConstX d L 0 ≤ 1 / 4)
    (hα : ∀ w, star (α w) = α w) (hφr : ∀ y i, star (φ y i) = φ y i) :
    0 < ((covOp G a aT ν α φ (unitQ G) (unitP G))⁻¹.det).re ∧
      ((covOp G a aT ν α φ (unitQ G) (unitP G))⁻¹.det).im = 0 ∧
      (∑ y : unitPts G, ∑ i : Fin N,
          decLog G a aT ν α (fun _ => 1) φ (unitQ G) (unitP G) (y, i) (y, i)).im = 0 ∧
      (1 / 2 : ℝ) * Real.log ((covOp G a aT ν α φ (unitQ G) (unitP G))⁻¹.det).re =
        -(1 / 2 : ℝ) * (∑ y : unitPts G, ∑ i : Fin N,
          decLog G a aT ν α (fun _ => 1) φ (unitQ G) (unitP G) (y, i) (y, i)).re := by
  have hP := (lemma24_a hfam hφ hδ hsm hα hφr).1
  have hL := decLog_one_eq_real hfam hφ hδ hsm (isUnitLatticeB_unit (G := G)) hα
    (fun b y => unitQ_real G b y) hφr
  obtain ⟨htr, hdpos, hdim⟩ := cov_trace_log_posDef hP
  have hsum : (∑ y : unitPts G, ∑ i : Fin N,
      decLog G a aT ν α (fun _ => 1) φ (unitQ G) (unitP G) (y, i) (y, i)) =
      ((Real.log (covOp G a aT ν α φ (unitQ G) (unitP G)).det.re : ℝ) : ℂ) := by
    rw [← htr, hL, Matrix.trace]
    simp only [Matrix.diag_apply]
    rw [Fintype.sum_prod_type]
  have hdet : (covOp G a aT ν α φ (unitQ G) (unitP G))⁻¹.det =
      (((covOp G a aT ν α φ (unitQ G) (unitP G)).det)⁻¹) := by
    rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv']
  obtain ⟨r, hr⟩ : ∃ r : ℝ, (covOp G a aT ν α φ (unitQ G) (unitP G)).det = (r : ℂ) :=
    ⟨(covOp G a aT ν α φ (unitQ G) (unitP G)).det.re, Complex.ext (by simp) (by simpa using hdim)⟩
  have hrpos : 0 < r := by
    have := hdpos; rw [hr, Complex.ofReal_re] at this; exact this
  have hdi : (covOp G a aT ν α φ (unitQ G) (unitP G))⁻¹.det = ((r⁻¹ : ℝ) : ℂ) := by
    rw [hdet, hr]; push_cast; rfl
  have hre : ((covOp G a aT ν α φ (unitQ G) (unitP G))⁻¹.det).re = r⁻¹ := by
    rw [hdi, Complex.ofReal_re]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hre]; positivity
  · rw [hdi, Complex.ofReal_im]
  · rw [hsum, Complex.ofReal_im]
  · rw [hsum, Complex.ofReal_re, hre, hr, Complex.ofReal_re, Real.log_inv]; ring


/-- **Lemma 2.4 (d)**, the resolvent identity: for `x ≥ 0`, `x + 𝒜` is invertible and
`(x + 𝒜)⁻¹ = A_{k,x} + a_k² L^{-2k} A_{k,x} Q (G_{k,x} - Π_{k,x}) Q* A_{k,x}` with
`G_{k,x} = H_{k,x}⁻¹`, `Π_{k,x}` the constrained operator of `G_{k,x}` and `φ₀`. -/
theorem lemma24_d (hfam : ∀ x, 0 ≤ x → XData G a aT ν x α 0 (fun _ => 1))
    (hφ : IsConstraintField G δ φ) (hδ : 0 ≤ δ) (hsm : δ ^ 2 * smallConstX d L 0 ≤ 1 / 4)
    {x : ℝ} (hx : 0 ≤ x) :
    IsUnit ((x : ℂ) • (1 : Matrix (unitPts G × Fin N) (unitPts G × Fin N) ℂ) +
        covOp G a aT ν α φ (unitQ G) (unitP G)) ∧
      ((x : ℂ) • (1 : Matrix (unitPts G × Fin N) (unitPts G × Fin N) ℂ) +
          covOp G a aT ν α φ (unitQ G) (unitP G))⁻¹ =
        covA (a k) (aT / (L : ℝ) ^ 2) x (liftOp N (unitP G)) +
          (((a k) ^ 2 / (L : ℝ) ^ (2 * k) : ℝ) : ℂ) •
            (covA (a k) (aT / (L : ℝ) ^ 2) x (liftOp N (unitP G)) * liftRect N (unitQ G) *
              (liftOp N (xDirichletOperator G a aT x ν α)⁻¹ -
                constrainedOp (xDirichletOperator G a aT x ν α)⁻¹ (restrictField G φ)) *
              (liftRect N (unitQ G))ᵀ *
              covA (a k) (aT / (L : ℝ) ^ 2) x (liftOp N (unitP G))) := by
  obtain ⟨hU, hEq⟩ := decCov_one_eq hfam hφ hδ hsm (isUnitLatticeB_unit (G := G)) hx
  refine ⟨hU, ?_⟩
  rw [← hEq]
  have D := hfam x hx
  set Hx := xDirichletOperator G a aT x ν α with hHx
  have hHxU : IsUnit Hx := xDirichlet_isUnit D.st D.pot hx
  have hHxG : Hx * Hx⁻¹ = 1 := Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hHxU)
  have hGxH : Hx⁻¹ * Hx = 1 := Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 hHxU)
  have hGs : Gsx G a aT x ν α (fun _ => 1) = Hx⁻¹ := Gsx_one D.st D.pot hx D.isUnit_one_sub
  have hPi : decPi G a aT x ν α (fun _ => 1) φ = constrainedOp Hx⁻¹ (restrictField G φ) := by
    rw [constrainedOp_eq hHxG hGxH]
    unfold decPi decM decN
    rw [hGs]
  unfold decCov
  rw [hGs, hPi]

/-- **Lemma 2.4 (d), identification with the decoupled objects at `s = 1`**:
`C_x(1) = (x + 𝒜)⁻¹`, `C^{1/2}(1)` is the resolvent integral of `𝒜`, and `𝕃(1)` is the matrix
logarithm integral `logMat 𝒜`. -/
theorem lemma24_d_identification (hfam : ∀ x, 0 ≤ x → XData G a aT ν x α 0 (fun _ => 1))
    (hφ : IsConstraintField G δ φ) (hδ : 0 ≤ δ) (hsm : δ ^ 2 * smallConstX d L 0 ≤ 1 / 4) :
    (∀ x : ℝ, 0 ≤ x → decCov G a aT x ν α (fun _ => 1) φ (unitQ G) (unitP G) =
      ((x : ℂ) • (1 : Matrix (unitPts G × Fin N) (unitPts G × Fin N) ℂ) +
        covOp G a aT ν α φ (unitQ G) (unitP G))⁻¹) ∧
    decCovSqrt G a aT ν α (fun _ => 1) φ (unitQ G) (unitP G) =
      sqrtMat (covOp G a aT ν α φ (unitQ G) (unitP G)) ∧
    decLog G a aT ν α (fun _ => 1) φ (unitQ G) (unitP G) =
      logMat (covOp G a aT ν α φ (unitQ G) (unitP G)) := by
  have hU := isUnitLatticeB_unit (G := G)
  exact ⟨fun x hx => (decCov_one_eq hfam hφ hδ hsm hU hx).2,
    decCovSqrt_one_eq_sqrtMat hfam hφ hδ hsm hU, decLog_one_eq_logMat hfam hφ hδ hsm hU⟩

end Balaban.Fluctuation
