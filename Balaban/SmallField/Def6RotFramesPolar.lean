/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Frames of the renormalization chain: polar decomposition of a complex orthogonal matrix

A complex orthogonal matrix `M` (`Mᵀ M = 1`) is written `M = Q · H`, with `Q` real orthogonal and
`H` the positive square root of `Mᴴ M`; `H` is again complex orthogonal (`Hᵀ H = 1`).  The
matrix `H = cay(S)` is the Cayley transform of a complex antisymmetric `S`, and the path
`s ↦ cay(sS)`, `s ∈ [0, 1]`, joins `1` to `H` through the functions of `H` with eigenvalues between
those of `1` and of `H`.  This file is linear algebra only:

* `exists_polar`: the decomposition `M = Q H`;
* `frame_decomp`: `M = Q · cay(S)`, `Sᵀ = -S`, `1 - sS` invertible on `[0, 1]`, and the two norm
  bounds along the path, `‖cay(sS) u‖² ≤ ‖u‖² + ‖M u‖²` and
  `‖cay(sS) e - e‖ ≤ ‖Mᴴ M e - e‖`.
-/

@[expose] public section

namespace Balaban.SmallField.RotFrames

open Matrix
open scoped MatrixOrder ComplexOrder

variable {N : ℕ}


theorem exists_polar {M : Matrix (Fin N) (Fin N) ℂ} (hM : M.transpose * M = 1) :
    ∃ Q H : Matrix (Fin N) (Fin N) ℂ, M = Q * H ∧ Q.transpose * Q = 1 ∧ (∀ i j, (Q i j).im = 0) ∧
      H.IsHermitian ∧ H.PosSemidef ∧ H.transpose * H = 1 ∧ H * H = Mᴴ * M := by
  set P : Matrix (Fin N) (Fin N) ℂ := Mᴴ * M with hPdef
  have hPpsd : P.PosSemidef := posSemidef_conjTranspose_mul_self M
  have hMM : M * M.transpose = 1 := mul_eq_one_comm.1 hM
  have hPT : P.transpose * P = 1 := by
    have h1 : (M.transpose)ᴴ * Mᴴ = 1 := by
      rw [← conjTranspose_mul, hMM, conjTranspose_one]
    have h2 : (Mᴴ).transpose = (M.transpose)ᴴ := by
      rw [conjTranspose_transpose, transpose_conjTranspose]
    rw [hPdef, transpose_mul, h2, Matrix.mul_assoc, ← Matrix.mul_assoc (M.transpose)ᴴ, h1,
      Matrix.one_mul, hM]
  have hPPT : P * P.transpose = 1 := mul_eq_one_comm.1 hPT
  have hPinv : P⁻¹ = P.transpose := (inv_eq_right_inv hPPT)
  -- the square root
  have hPnn : 0 ≤ P := hPpsd.nonneg
  set H : Matrix (Fin N) (Fin N) ℂ := CFC.sqrt P with hHdef
  have hHnn : 0 ≤ H := CFC.sqrt_nonneg P
  have hHpsd : H.PosSemidef := hHnn.posSemidef
  have hHH : H * H = P := CFC.sqrt_mul_sqrt_self P hPnn
  have hHTnn : 0 ≤ H.transpose := hHpsd.transpose.nonneg
  have hHTHT : H.transpose * H.transpose = P.transpose := by
    rw [← transpose_mul, hHH]
  have h3 : CFC.sqrt P.transpose = H.transpose :=
    ((CFC.sqrt_eq_iff _ _ hPpsd.transpose.nonneg hHTnn).2 hHTHT)
  have h4 : H⁻¹ = CFC.sqrt P⁻¹ := hPpsd.inv_sqrt
  have hHTinv : H.transpose = H⁻¹ := by rw [h4, hPinv, h3]
  have hdetH : IsUnit H.det := by
    have : IsUnit (H * H).det := by
      rw [hHH]; exact isUnit_det_of_right_inverse hPPT
    rw [det_mul] at this
    exact (isUnit_mul_self_iff.1 (by simpa using this))
  have hHTH : H.transpose * H = 1 := by
    rw [hHTinv]; exact nonsing_inv_mul _ hdetH
  have hHherm : H.IsHermitian := hHpsd.isHermitian
  have hHHT : H * H.transpose = 1 := mul_eq_one_comm.1 hHTH
  refine ⟨M * H.transpose, H, ?_, ?_, ?_, hHherm, hHpsd, hHTH, hHH⟩
  · rw [Matrix.mul_assoc, hHTH, Matrix.mul_one]
  · rw [transpose_mul, transpose_transpose, Matrix.mul_assoc, ← Matrix.mul_assoc M.transpose, hM,
      Matrix.one_mul, hHHT]
  · have hQQT : (M * H.transpose).transpose * (M * H.transpose) = 1 := by
      rw [transpose_mul, transpose_transpose, Matrix.mul_assoc, ← Matrix.mul_assoc M.transpose, hM,
        Matrix.one_mul, hHHT]
    have hHTc : (H.transpose)ᴴ = H.transpose := by
      rw [transpose_conjTranspose]
      calc H.map star = (Hᴴ)ᵀ := by ext i j; simp [conjTranspose]
        _ = Hᵀ := by rw [hHherm.eq]
    have hQQ : (M * H.transpose)ᴴ * (M * H.transpose) = 1 := by
      rw [conjTranspose_mul, hHTc]
      calc H.transpose * Mᴴ * (M * H.transpose) = H.transpose * (Mᴴ * M) * H.transpose := by
            simp only [Matrix.mul_assoc]
        _ = H.transpose * (H * H) * H.transpose := by rw [hHH]
        _ = (H.transpose * H) * (H * H.transpose) := by simp only [Matrix.mul_assoc]
        _ = 1 := by rw [hHTH, hHHT, Matrix.one_mul]
    have hQ' : (M * H.transpose) * (M * H.transpose).transpose = 1 := mul_eq_one_comm.1 hQQT
    have hconj : (M * H.transpose)ᴴ = (M * H.transpose).transpose := by
      calc (M * H.transpose)ᴴ = (M * H.transpose)ᴴ * ((M * H.transpose) * (M * H.transpose).transpose) := by
            rw [hQ', Matrix.mul_one]
        _ = ((M * H.transpose)ᴴ * (M * H.transpose)) * (M * H.transpose).transpose :=
            (Matrix.mul_assoc _ _ _).symm
        _ = _ := by rw [hQQ, Matrix.one_mul]
    intro i j
    have := congrFun (congrFun hconj j) i
    simp only [conjTranspose_apply, transpose_apply] at this
    exact Complex.conj_eq_iff_im.1 this



/-- The Cayley parameter `(l - 1)/(l + 1)` of an eigenvalue `l > 0`. -/
noncomputable def sig (l : ℝ) : ℝ := (l - 1) / (l + 1)
/-- The eigenvalue of `cay(sS)` for the eigenvalue `l` of `H = cay(S)`. -/
noncomputable def gs (s l : ℝ) : ℝ := (1 + s * sig l) / (1 - s * sig l)

theorem gs_eq {s l : ℝ} (hl : 0 < l) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    gs s l = ((1 + s) * l + (1 - s)) / ((1 - s) * l + (1 + s)) := by
  have h1 : l + 1 ≠ 0 := by positivity
  have h2 : 0 < (1 - s) * l + (1 + s) := by nlinarith
  unfold gs sig
  have h3 : 1 - s * ((l - 1) / (l + 1)) = ((1 - s) * l + (1 + s)) / (l + 1) := by
    field_simp; ring
  have h4 : 1 + s * ((l - 1) / (l + 1)) = ((1 + s) * l + (1 - s)) / (l + 1) := by
    field_simp; ring
  rw [h3, h4, div_div_div_cancel_right₀ h1]

theorem one_sub_sig_pos {s l : ℝ} (hl : 0 < l) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) : 0 < 1 - s * sig l := by
  have h1 : 0 < l + 1 := by positivity
  have : 1 - s * sig l = ((1 - s) * l + (1 + s)) / (l + 1) := by
    unfold sig; field_simp; ring
  rw [this]; apply div_pos _ h1; nlinarith

theorem gs_sub_one {s l : ℝ} (hl : 0 < l) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    gs s l - 1 = 2 * s * (l - 1) / ((1 - s) * l + (1 + s)) := by
  have h2 : 0 < (1 - s) * l + (1 + s) := by nlinarith
  rw [gs_eq hl hs0 hs1, div_sub_one h2.ne']; congr 1; ring

theorem abs_gs_sub_one_le {s l : ℝ} (hl : 0 < l) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    |gs s l - 1| ≤ |l ^ 2 - 1| := by
  have h2 : 0 < (1 - s) * l + (1 + s) := by nlinarith
  rw [gs_sub_one hl hs0 hs1, abs_div, abs_of_pos h2, div_le_iff₀ h2]
  have hA : |l ^ 2 - 1| = |l - 1| * (l + 1) := by
    rw [show l ^ 2 - 1 = (l - 1) * (l + 1) by ring, abs_mul, abs_of_pos (by linarith : 0 < l + 1)]
  rw [hA, abs_mul, abs_of_nonneg (by linarith : (0:ℝ) ≤ 2 * s)]
  have h5 : 2 * s * |l - 1| ≤ |l - 1| * (l + 1) * ((1 - s) * l + (1 + s)) := by
    have : 2 * s ≤ (l + 1) * ((1 - s) * l + (1 + s)) := by nlinarith [sq_nonneg l]
    nlinarith [abs_nonneg (l - 1)]
  linarith

theorem gs_sq_le {s l : ℝ} (hl : 0 < l) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    gs s l ^ 2 ≤ 1 + l ^ 2 := by
  have h2 : 0 < (1 - s) * l + (1 + s) := by nlinarith
  have hg := gs_sub_one hl hs0 hs1
  have hpos : 0 < gs s l := by
    rw [gs_eq hl hs0 hs1]; apply div_pos _ h2; nlinarith
  rcases le_total l 1 with h | h
  · have : gs s l - 1 ≤ 0 := by
      rw [hg]; apply div_nonpos_of_nonpos_of_nonneg _ h2.le; nlinarith
    nlinarith
  · have : gs s l - 1 ≤ l - 1 := by
      rw [hg, div_le_iff₀ h2]; nlinarith [mul_nonneg (sub_nonneg.2 h) (sub_nonneg.2 hs1), mul_nonneg (sub_nonneg.2 h) hs0]
    nlinarith



theorem spec_of_herm {H : Matrix (Fin N) (Fin N) ℂ} (hH : H.IsHermitian) (hpsd : H.PosSemidef)
    (hHT : H.transpose * H = 1) :
    ∃ (V : Matrix (Fin N) (Fin N) ℂ) (lam : Fin N → ℝ), star V * V = 1 ∧ V * star V = 1 ∧
      (∀ i, 0 < lam i) ∧ H = V * diagonal (fun i => (lam i : ℂ)) * star V := by
  have hsp := hH.spectral_theorem
  rw [Unitary.conjStarAlgAut_apply] at hsp
  refine ⟨(hH.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℂ), hH.eigenvalues, ?_, ?_, ?_, ?_⟩
  · exact Unitary.coe_star_mul_self _
  · exact Unitary.coe_mul_star_self _
  · intro i
    refine lt_of_le_of_ne (hpsd.eigenvalues_nonneg i) (fun h0 => ?_)
    have hdet : H.det ≠ 0 := by
      have := congrArg det hHT
      rw [det_mul, det_transpose, det_one] at this
      intro h; rw [h] at this; simp at this
    apply hdet
    rw [hH.det_eq_prod_eigenvalues]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [← h0])
  · exact hsp



/-- The matrix `V diag(f) V*`. -/
noncomputable def specMat (V : Matrix (Fin N) (Fin N) ℂ) (f : Fin N → ℂ) :
    Matrix (Fin N) (Fin N) ℂ := V * diagonal f * star V

/-- The squared Euclidean norm of a vector of `ℂ^N`. -/
noncomputable def nsq (x : Fin N → ℂ) : ℝ := ∑ i, ‖x i‖ ^ 2

section Spec

variable {V : Matrix (Fin N) (Fin N) ℂ}

theorem specMat_mul (hV : star V * V = 1) (f g : Fin N → ℂ) :
    specMat V f * specMat V g = specMat V (f * g) := by
  unfold specMat
  calc V * diagonal f * star V * (V * diagonal g * star V)
      = V * diagonal f * (star V * V) * diagonal g * star V := by simp only [Matrix.mul_assoc]
    _ = V * (diagonal f * diagonal g) * star V := by rw [hV, Matrix.mul_one]; simp only [Matrix.mul_assoc]
    _ = _ := by rw [diagonal_mul_diagonal]; rfl

theorem specMat_one (hV : V * star V = 1) : specMat V 1 = 1 := by
  unfold specMat
  have : diagonal (1 : Fin N → ℂ) = 1 := diagonal_one
  rw [this, Matrix.mul_one, hV]

theorem specMat_add (f g : Fin N → ℂ) : specMat V (f + g) = specMat V f + specMat V g := by
  unfold specMat
  have h : diagonal (f + g) = diagonal f + diagonal g := (diagonal_add f g).symm
  rw [h, Matrix.mul_add, Matrix.add_mul]

theorem specMat_sub (f g : Fin N → ℂ) : specMat V (f - g) = specMat V f - specMat V g := by
  unfold specMat
  have h : diagonal (f - g) = diagonal f - diagonal g := (diagonal_sub f g).symm
  rw [h, Matrix.mul_sub, Matrix.sub_mul]

theorem specMat_smul (c : ℂ) (f : Fin N → ℂ) : specMat V (c • f) = c • specMat V f := by
  unfold specMat
  rw [diagonal_smul, Matrix.mul_smul, Matrix.smul_mul]

theorem specMat_inv (hV1 : star V * V = 1) (hV2 : V * star V = 1) (f : Fin N → ℂ)
    (hf : ∀ i, f i ≠ 0) : (specMat V f)⁻¹ = specMat V f⁻¹ := by
  apply inv_eq_right_inv
  rw [specMat_mul hV1, show f * f⁻¹ = 1 from funext fun i => by simp [hf i], specMat_one hV2]

theorem nsq_eq_dot (x : Fin N → ℂ) : (nsq x : ℂ) = star x ⬝ᵥ x := by
  unfold nsq
  simp only [dotProduct, Pi.star_apply, Complex.star_def]
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.conj_mul']

theorem nsq_unitary_mulVec (hV : star V * V = 1) (z : Fin N → ℂ) : nsq (V *ᵥ z) = nsq z := by
  have h : (nsq (V *ᵥ z) : ℂ) = nsq z := by
    rw [nsq_eq_dot, nsq_eq_dot, star_mulVec, dotProduct_mulVec, vecMul_vecMul]
    have hV' : Vᴴ * V = 1 := hV
    rw [hV', vecMul_one]
  exact_mod_cast h

theorem nsq_diag_mulVec (f y : Fin N → ℂ) :
    nsq (diagonal f *ᵥ y) = ∑ i, ‖f i‖ ^ 2 * ‖y i‖ ^ 2 := by
  unfold nsq
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mulVec_diagonal, norm_mul, mul_pow]

theorem nsq_specMat_mulVec (hV1 : star V * V = 1) (f u : Fin N → ℂ) :
    nsq (specMat V f *ᵥ u) = ∑ i, ‖f i‖ ^ 2 * ‖(star V *ᵥ u) i‖ ^ 2 := by
  unfold specMat
  rw [← mulVec_mulVec, ← mulVec_mulVec, nsq_unitary_mulVec hV1, nsq_diag_mulVec]

theorem nsq_eq_spec (hV2 : V * star V = 1) (u : Fin N → ℂ) :
    nsq u = ∑ i, ‖(star V *ᵥ u) i‖ ^ 2 := by
  have : star (star V) * star V = 1 := by rw [star_star]; exact hV2
  rw [← nsq_unitary_mulVec this u]
  rfl

end Spec

/-- The Cayley transform `(1 - sS)⁻¹ (1 + sS)`. -/
noncomputable def cayMat (S : Matrix (Fin N) (Fin N) ℂ) (s : ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  (1 - s • S)⁻¹ * (1 + s • S)

section Cay

variable {V : Matrix (Fin N) (Fin N) ℂ} {lam : Fin N → ℝ}

/-- The Cayley parameters of the eigenvalues, as complex numbers. -/
noncomputable def sigC (lam : Fin N → ℝ) : Fin N → ℂ := fun i => ((sig (lam i) : ℝ) : ℂ)
/-- The eigenvalues, as complex numbers. -/
noncomputable def lamC (lam : Fin N → ℝ) : Fin N → ℂ := fun i => ((lam i : ℝ) : ℂ)

theorem lamC_add_one_ne (hl : ∀ i, 0 < lam i) (i : Fin N) : (1 + lamC lam) i ≠ 0 := by
  have := hl i
  simp only [Pi.add_apply, Pi.one_apply, lamC]
  exact_mod_cast (by positivity : (1 + lam i) ≠ 0)

theorem sig_mul (hl : ∀ i, 0 < lam i) : sigC lam * (1 + lamC lam) = lamC lam - 1 := by
  funext i
  have h1 : (lam i : ℝ) + 1 ≠ 0 := by have := hl i; positivity
  simp only [sigC, lamC, Pi.mul_apply, Pi.add_apply, Pi.one_apply, Pi.sub_apply, sig]
  have h1' : ((lam i : ℂ)) + 1 ≠ 0 := by exact_mod_cast h1
  push_cast
  field_simp
  ring

theorem S_mul_A (hV1 : star V * V = 1) (hV2 : V * star V = 1) (hl : ∀ i, 0 < lam i) :
    specMat V (sigC lam) * (1 + specMat V (lamC lam)) = specMat V (lamC lam) - 1 := by
  rw [← specMat_one hV2, ← specMat_add, specMat_mul hV1, sig_mul hl, specMat_sub, specMat_one hV2]

theorem one_add_H (hV2 : V * star V = 1) :
    1 + specMat V (lamC lam) = specMat V (1 + lamC lam) := by
  rw [specMat_add, specMat_one hV2]

theorem S_skew (hV1 : star V * V = 1) (hV2 : V * star V = 1) (hl : ∀ i, 0 < lam i)
    (hHT : (specMat V (lamC lam)).transpose * specMat V (lamC lam) = 1) :
    (specMat V (sigC lam)).transpose = -specMat V (sigC lam) := by
  set S := specMat V (sigC lam) with hS
  set H := specMat V (lamC lam) with hH
  have hHHT : H * H.transpose = 1 := mul_eq_one_comm.1 hHT
  have hSA : S * (1 + H) = H - 1 := S_mul_A hV1 hV2 hl
  have hAS : (1 + H) * S = H - 1 := by
    rw [one_add_H hV2, hS, specMat_mul hV1, mul_comm (1 + lamC lam), sig_mul hl, specMat_sub,
      specMat_one hV2]
  have h1 : (1 + H.transpose) * S.transpose = H.transpose - 1 := by
    have := congrArg transpose hSA
    rwa [transpose_mul, transpose_add, transpose_one, transpose_sub, transpose_one] at this
  have h2 : (1 + H) * S.transpose = 1 - H := by
    have := congrArg (fun X => H * X) h1
    rw [← Matrix.mul_assoc, Matrix.mul_add, Matrix.mul_one, hHHT, add_comm, Matrix.mul_sub,
      hHHT, Matrix.mul_one] at this
    exact this
  have h3 : (1 + H) * (S.transpose + S) = 0 := by
    rw [Matrix.mul_add, h2, hAS]; abel
  have hinv : specMat V (1 + lamC lam)⁻¹ * (1 + H) = 1 := by
    rw [one_add_H hV2, specMat_mul hV1,
      show (1 + lamC lam)⁻¹ * (1 + lamC lam) = 1 from funext fun i => by
        exact inv_mul_cancel₀ (lamC_add_one_ne hl i), specMat_one hV2]
  have h4 : S.transpose + S = 0 := by
    have := congrArg (fun X => specMat V (1 + lamC lam)⁻¹ * X) h3
    simp only [Matrix.mul_zero] at this
    rwa [← Matrix.mul_assoc, hinv, Matrix.one_mul] at this
  exact eq_neg_of_add_eq_zero_left h4

end Cay

section Final

variable {V : Matrix (Fin N) (Fin N) ℂ} {lam : Fin N → ℝ}

theorem one_sub_sS (hV2 : V * star V = 1) (s : ℝ) :
    1 - (s : ℂ) • specMat V (sigC lam) = specMat V (1 - (s : ℂ) • sigC lam) := by
  rw [specMat_sub, specMat_one hV2, specMat_smul]

theorem one_add_sS (hV2 : V * star V = 1) (s : ℝ) :
    1 + (s : ℂ) • specMat V (sigC lam) = specMat V (1 + (s : ℂ) • sigC lam) := by
  rw [specMat_add, specMat_one hV2, specMat_smul]

theorem one_sub_sig_ne (hl : ∀ i, 0 < lam i) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (i : Fin N) :
    (1 - (s : ℂ) • sigC lam) i ≠ 0 := by
  have h := one_sub_sig_pos (hl i) hs0 hs1
  simp only [Pi.sub_apply, Pi.one_apply, Pi.smul_apply, sigC, smul_eq_mul]
  exact_mod_cast h.ne'

theorem isUnit_det_one_sub (hV1 : star V * V = 1) (hV2 : V * star V = 1) (hl : ∀ i, 0 < lam i)
    {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    IsUnit (1 - (s : ℂ) • specMat V (sigC lam)).det := by
  rw [one_sub_sS hV2]
  refine isUnit_det_of_right_inverse (B := specMat V (1 - (s : ℂ) • sigC lam)⁻¹) ?_
  rw [specMat_mul hV1, show (1 - (s : ℂ) • sigC lam) * (1 - (s : ℂ) • sigC lam)⁻¹ = 1 from
    funext fun i => by exact mul_inv_cancel₀ (one_sub_sig_ne hl hs0 hs1 i), specMat_one hV2]

theorem cayMat_eq (hV1 : star V * V = 1) (hV2 : V * star V = 1) (hl : ∀ i, 0 < lam i)
    {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    cayMat (specMat V (sigC lam)) (s : ℂ) = specMat V (fun i => ((gs s (lam i) : ℝ) : ℂ)) := by
  unfold cayMat
  rw [one_sub_sS hV2, one_add_sS hV2, specMat_inv hV1 hV2 _ (one_sub_sig_ne hl hs0 hs1),
    specMat_mul hV1]
  congr 1
  funext i
  have h := (one_sub_sig_pos (hl i) hs0 hs1).ne'
  have h' : (1 - (s : ℂ) * ((sig (lam i) : ℝ) : ℂ)) ≠ 0 := by exact_mod_cast h
  simp only [Pi.mul_apply, Pi.inv_apply, Pi.sub_apply, Pi.add_apply, Pi.one_apply, Pi.smul_apply,
    sigC, smul_eq_mul, gs]
  push_cast
  field_simp

theorem star_eq_transpose_of_real {Q : Matrix (Fin N) (Fin N) ℂ} (hQ : ∀ i j, (Q i j).im = 0) :
    star Q = Q.transpose := by
  ext i j
  simp only [star_apply, transpose_apply]
  exact Complex.conj_eq_iff_im.2 (hQ j i)

theorem frame_decomp {M : Matrix (Fin N) (Fin N) ℂ} (hM : M.transpose * M = 1) :
    ∃ Q S : Matrix (Fin N) (Fin N) ℂ, Q.transpose * Q = 1 ∧ (∀ i j, (Q i j).im = 0) ∧
      S.transpose = -S ∧ M = Q * cayMat S 1 ∧
      ∀ s : ℝ, 0 ≤ s → s ≤ 1 → IsUnit (1 - (s : ℂ) • S).det ∧
        (∀ u : Fin N → ℂ, nsq (cayMat S (s : ℂ) *ᵥ u) ≤ nsq u + nsq (M *ᵥ u)) ∧
        (∀ e : Fin N → ℂ, nsq (cayMat S (s : ℂ) *ᵥ e - e) ≤ nsq ((Mᴴ * M) *ᵥ e - e)) := by
  obtain ⟨Q, H, hMQH, hQQ, hQre, hHherm, hHpsd, hHTH, hHH⟩ := exists_polar hM
  obtain ⟨V, lam, hV1, hV2, hl, hHV⟩ := spec_of_herm hHherm hHpsd hHTH
  have hH : H = specMat V (lamC lam) := hHV
  have hHT' : (specMat V (lamC lam)).transpose * specMat V (lamC lam) = 1 := by rw [← hH]; exact hHTH
  have hQu : star Q * Q = 1 := by rw [star_eq_transpose_of_real hQre]; exact hQQ
  have hcay1 : cayMat (specMat V (sigC lam)) 1 = H := by
    have := cayMat_eq hV1 hV2 hl (s := 1) zero_le_one le_rfl
    rw [Complex.ofReal_one] at this
    rw [this, hH]
    congr 1
    funext i
    have h1 : (lam i : ℝ) + 1 ≠ 0 := by have := hl i; positivity
    simp only [gs, sig, lamC]
    have h2 : (1 - 1 * ((lam i - 1) / (lam i + 1))) ≠ 0 := by
      have := one_sub_sig_pos (hl i) zero_le_one le_rfl; unfold sig at this; exact this.ne'
    field_simp
    ring_nf
  refine ⟨Q, specMat V (sigC lam), hQQ, hQre, S_skew hV1 hV2 hl hHT', by rw [hcay1]; exact hMQH, ?_⟩
  intro s hs0 hs1
  refine ⟨isUnit_det_one_sub hV1 hV2 hl hs0 hs1, ?_, ?_⟩
  · intro u
    have hMu : nsq (M *ᵥ u) = nsq (specMat V (lamC lam) *ᵥ u) := by
      rw [hMQH, ← mulVec_mulVec, nsq_unitary_mulVec hQu, hH]
    rw [hMu, cayMat_eq hV1 hV2 hl hs0 hs1, nsq_specMat_mulVec hV1, nsq_specMat_mulVec hV1,
      nsq_eq_spec hV2 u, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun i _ => ?_
    have := gs_sq_le (hl i) hs0 hs1
    simp only [Complex.norm_real, Real.norm_eq_abs, lamC, sq_abs]
    nlinarith [sq_nonneg ‖(star V *ᵥ u) i‖]
  · intro e
    have e1 : cayMat (specMat V (sigC lam)) (s : ℂ) *ᵥ e - e =
        specMat V (fun i => ((gs s (lam i) : ℝ) : ℂ) - 1) *ᵥ e := by
      rw [cayMat_eq hV1 hV2 hl hs0 hs1]
      have : (fun i => ((gs s (lam i) : ℝ) : ℂ) - 1) = (fun i => ((gs s (lam i) : ℝ) : ℂ)) - 1 := rfl
      rw [this, specMat_sub, specMat_one hV2, sub_mulVec, one_mulVec]
    have e2 : (Mᴴ * M) *ᵥ e - e = specMat V (fun i => ((lam i : ℂ)) * (lam i : ℂ) - 1) *ᵥ e := by
      have : (fun i => ((lam i : ℂ)) * (lam i : ℂ) - 1) = lamC lam * lamC lam - 1 := rfl
      rw [← hHH, hH, this, specMat_sub, specMat_one hV2, specMat_mul hV1, sub_mulVec, one_mulVec]
    rw [e1, e2, nsq_specMat_mulVec hV1, nsq_specMat_mulVec hV1]
    refine Finset.sum_le_sum fun i _ => ?_
    refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
    have := abs_gs_sub_one_le (hl i) hs0 hs1
    have h3 : ‖((gs s (lam i) : ℝ) : ℂ) - 1‖ = |gs s (lam i) - 1| := by
      rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    have h4 : ‖((lam i : ℂ)) * (lam i : ℂ) - 1‖ = |lam i ^ 2 - 1| := by
      rw [show ((lam i : ℂ)) * (lam i : ℂ) - 1 = ((lam i ^ 2 - 1 : ℝ) : ℂ) by push_cast; ring,
        Complex.norm_real, Real.norm_eq_abs]
    rw [h3, h4]
    exact pow_le_pow_left₀ (abs_nonneg _) this 2

end Final

end Balaban.SmallField.RotFrames
