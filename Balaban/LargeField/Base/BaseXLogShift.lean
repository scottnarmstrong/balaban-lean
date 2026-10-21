/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Base.BaseXLogShiftCube
public import Balaban.LargeField.Base.BaseXLog
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The shifted logarithm of the base covariance family: second-order large-`x` expansion

Part A: the Green function `Ĝ_{x,s}` satisfies `x Ĝ_{x,s} = σ_s + O(1/x)` in `ℓ²` operator norm,
with `‖(1 - 𝒦)⁻¹‖ ≤ 2 L`.
-/

@[expose] public section

namespace Balaban.LargeField.Base

open Matrix Balaban Balaban.Green Balaban.Multiscale Balaban.Localization
open scoped Matrix.Norms.L2Operator

section Green

variable {d L N₁ m₁ N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
  {G : GeneratingSet d L (N₁ * L ^ m₁) 1 ϱ} {a : ℕ → ℝ} {aT ν x Cx κ : ℝ} {α : G.Ω 1 → ℂ}
  {s : ℕ × Balaban.Localization.CTorus d L N₁ m₁ 1 → ℂ}

/-- The decoupled data of the first step at mass `ν + x` and `x' = 0`. -/
theorem xData_base (S : Dec2.XCover (coverOf G) G a aT (ν + x) Cx) (hCx : 0 ≤ Cx) (hα : AdmPot G α)
    (hκ : 0 ≤ κ) (hM : Dec2.cstarX d L Cx * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    (hs : ∀ P, ‖s P‖ ≤ Real.exp κ) : Dec2.XData (coverOf G) G a aT (ν + x) 0 α κ s Cx :=
  ⟨S, hCx, hα, le_rfl, hκ, hM, hs⟩

/-- **`‖(1 - 𝒦_{x,s})⁻¹‖ ≤ 2 L`**, uniformly in `x ≥ 0`. -/
theorem opNorm_Kinv_le (D : Dec2.XData (coverOf G) G a aT (ν + x) 0 α κ s Cx) :
    ‖(1 - Dec2.Kcalx (coverOf G) G a aT 0 (ν + x) α s)⁻¹‖ ≤ 2 * L := by
  have hd : 0 < d := by have := D.st.hd; omega
  have hL1 : 1 ≤ L := by have := D.st.hL; omega
  have hL0 : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have W : XWeight G 0 (fun _ => 0) :=
    ⟨isAgmonWeight_zero G, le_rfl, (xAgmonRate_pos hd D.st.hL).le⟩
  refine l2_opNorm_le_of_sqNorm _ (by positivity) fun g => ?_
  have h1 : sqNorm ((1 - Dec2.Kcalx (coverOf G) G a aT 0 (ν + x) α s)⁻¹ *ᵥ g) ≤
      (16 / 9) * (((L : ℝ) ^ (0 + 1)) ^ 2 * sqNorm g) :=
    ((sqNorm_le_agmonSource_zero hL1 _).1.trans (D.neumann_src W g)).trans
      (mul_le_mul_of_nonneg_left (sqNorm_le_agmonSource_zero hL1 g).2 (by norm_num))
  refine h1.trans ?_
  simp only [zero_add, pow_one]
  nlinarith [mul_nonneg (sq_nonneg (L : ℝ)) (sqNorm_nonneg g)]

/-- **First order of the decoupled Green function**: `‖x Ĝ_{x,s} - σ_s‖ ≤ c / Γ`,
`c = 2 L · 3·5^d e^{N₀ κ} ((ν + 4 d + 3) + 3·5^d e^{N₀ κ} · 2 (4 d + 2))`. -/
theorem opNorm_x_Gsx_sub_sigma_le (D : Dec2.XData (coverOf G) G a aT (ν + x) 0 α κ s Cx)
    (hν : 0 ≤ ν) (hx : 0 ≤ x)
    (ha0 : a 0 = 2) (ha1 : 0 ≤ a 1) (ha1' : a 1 ≤ 2)
    (haT : aT = 2 * a 1 * (L : ℝ) ^ 2 / (2 * (L : ℝ) ^ 2 - a 1)) :
    ‖(x : ℂ) • Dec2.Gsx (coverOf G) G a aT 0 (ν + x) α s - Matrix.diagonal (cubeSigma G s)‖ ≤
      2 * L * ((3 * 5 ^ d : ℝ) * Real.exp (N0 d L * κ) * ((ν + 4 * d + 3) +
        (3 * 5 ^ d : ℝ) * Real.exp (N0 d L * κ) * (2 * (4 * d + 2)))) / (cubeGap L + x) := by
  have hΓ : 0 < cubeGap L + x := by have := cubeGap_pos L; positivity
  set c3 : ℝ := 3 * 5 ^ d with hc3
  set e := Real.exp (N0 d L * κ) with he
  have hc30 : 0 ≤ c3 := by positivity
  have he0 : 0 ≤ e := (Real.exp_pos _).le
  set b : ℝ := ν + 4 * d + 3 with hb
  have hb0 : 0 ≤ b := by positivity
  set P : ℝ := 2 * (4 * d + 2) with hP
  have hP0 : 0 ≤ P := by positivity
  set Ki := (1 - Dec2.Kcalx (coverOf G) G a aT 0 (ν + x) α s)⁻¹ with hKi
  set Kc := Dec2.Kcalx (coverOf G) G a aT 0 (ν + x) α s with hKc
  set Gs := Dec2.Gstarx (coverOf G) G a aT 0 (ν + x) α s with hGs
  set σm : Matrix (G.Ω 1) (G.Ω 1) ℂ := Matrix.diagonal (cubeSigma G s) with hσm
  have hdet := (Matrix.isUnit_iff_isUnit_det _).1 D.isUnit_one_sub
  have hT : (1 - Kc) * Ki = 1 := Matrix.mul_nonsing_inv _ hdet
  have h1 : Ki - Kc * Ki = 1 := by simpa [Matrix.sub_mul] using hT
  have hid : (x : ℂ) • Dec2.Gsx (coverOf G) G a aT 0 (ν + x) α s - σm =
      ((x : ℂ) • Gs - σm) * Ki + σm * (Kc * Ki) := by
    have : Dec2.Gsx (coverOf G) G a aT 0 (ν + x) α s = Gs * Ki := rfl
    rw [this, Matrix.sub_mul, Matrix.smul_mul]
    have h2 : σm * (Kc * Ki) = σm * Ki - σm := by
      have : Kc * Ki = Ki - 1 := by rw [← h1]; abel
      rw [this, Matrix.mul_sub, Matrix.mul_one]
    rw [h2]; abel
  have hA := opNorm_x_Gstarx_sub_sigma_le D.st hν hx D.κ0 D.sb D.pot ha0 ha1 ha1' haT
  have hB := opNorm_Kcalx_le D.st hν hx D.κ0 D.sb D.pot ha0 ha1 ha1' haT
  have hS : ‖σm‖ ≤ c3 * e := by
    refine l2_opNorm_le_of_sqNorm _ (by positivity) fun g => ?_
    unfold sqNorm
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun y _ => ?_
    rw [hσm, Matrix.mulVec_diagonal, norm_mul, mul_pow]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _)
      (norm_cubeSigma_le D.st D.κ0 D.sb y) 2) (sq_nonneg _)
  have hKi' := opNorm_Kinv_le D
  rw [hid]
  have hL0 : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  calc ‖((x : ℂ) • Gs - σm) * Ki + σm * (Kc * Ki)‖
      ≤ ‖((x : ℂ) • Gs - σm) * Ki‖ + ‖σm * (Kc * Ki)‖ := norm_add_le _ _
    _ ≤ ‖(x : ℂ) • Gs - σm‖ * ‖Ki‖ + ‖σm‖ * (‖Kc‖ * ‖Ki‖) := by
        gcongr
        · exact Matrix.l2_opNorm_mul _ _
        · exact (Matrix.l2_opNorm_mul _ _).trans
            (mul_le_mul_of_nonneg_left (Matrix.l2_opNorm_mul _ _) (norm_nonneg _))
    _ ≤ (c3 * e * b / (cubeGap L + x)) * (2 * L) +
          (c3 * e) * ((c3 * e * P / (cubeGap L + x)) * (2 * L)) := by
        gcongr
    _ = _ := by field_simp

end Green

section Coef

variable {d L N₁ m₁ N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
  {G : GeneratingSet d L (N₁ * L ^ m₁) 1 ϱ} {a : ℕ → ℝ} {aT ν x Cx κ : ℝ} {α : G.Ω 1 → ℂ}
  {s : ℕ × Balaban.Localization.CTorus d L N₁ m₁ 1 → ℂ}
  {φ : Balaban.Localization.CTorus d L N₁ m₁ 1 → Fin N → ℂ}

/-- **The field projection `Q_φ = φ₀ (φ₀·φ₀)⁻¹ φ₀ᵀ`**: the projection onto the direction of the
constraint field, site by site (`φ₀·φ₀` the bilinear square).  It equals `P_e` when
`φ₀·φ₀ = 1`. -/
noncomputable def fieldProj (G : GeneratingSet d L (N₁ * L ^ m₁) 1 ϱ)
    (φ : Balaban.Localization.CTorus d L N₁ m₁ 1 → Fin N → ℂ) :
    Matrix (G.Ω 1 × Fin N) (G.Ω 1 × Fin N) ℂ :=
  fieldMul (restrictField G φ) *
    Matrix.diagonal (fun y : G.Ω 1 => (∑ i, φ y i * φ y i)⁻¹) * (fieldMul (restrictField G φ))ᵀ

/-- **The large-`x` coefficient `c(s)` of the decoupled covariance** of the first step
(`BASEX.md`, Q5): `C_x(s) = x⁻¹ c(s) + O(x⁻²)`, with
`c(s) = P_e + σ_s (1 - φ₀ (φ₀·φ₀)⁻¹ φ₀ᵀ)`, `σ_s = Σ_q s_q χ_q`.  It is the identity at the physical
point `s ≡ 1`, `φ₀·φ₀ = 1`. -/
noncomputable def baseCovXCoef (G : GeneratingSet d L (N₁ * L ^ m₁) 1 ϱ)
    (s : ℕ × Balaban.Localization.CTorus d L N₁ m₁ 1 → ℂ)
    (φ : Balaban.Localization.CTorus d L N₁ m₁ 1 → Fin N → ℂ) :
    Matrix (G.Ω 1 × Fin N) (G.Ω 1 × Fin N) ℂ :=
  basePart (restrictField G φ) + liftOp N (Matrix.diagonal (cubeSigma G s)) * (1 - fieldProj G φ)

theorem fieldMul_transpose_mul_diag (φ : G.Ω 1 → Fin N → ℂ) :
    (fieldMul φ)ᵀ * fieldMul φ = Matrix.diagonal (fun y : G.Ω 1 => ∑ i, φ y i * φ y i) := by
  ext y z
  simp only [Matrix.mul_apply, Matrix.transpose_apply, fieldMul, Fintype.sum_prod_type,
    Matrix.diagonal_apply]
  by_cases h : y = z
  · subst h
    simp
  · have h' : ¬ z = y := fun hh => h hh.symm
    simp [h, h']

/-- **The remainder of the covariance after the leading term**:
`C_x(s) - (1+x)⁻¹ c(s) = (Ĝ - (1+x)⁻¹ σ + Ĝ φ₀ M⁻¹ K(φ₀) Ĝ) (1 - Q_φ)`. -/
theorem covX_sub_coef (hMu : IsUnit (Dec2.decM (coverOf G) G a aT 0 (ν + x) α s φ))
    (hD : ∀ y : G.Ω 1, ∑ i, φ y i * φ y i ≠ 0) :
    ((1 + (x : ℂ))⁻¹ • basePart (restrictField G φ) +
        liftOp N (Dec2.Gsx (coverOf G) G a aT 0 (ν + x) α s) -
        Dec2.decPi (coverOf G) G a aT 0 (ν + x) α s φ) -
      (1 + (x : ℂ))⁻¹ • baseCovXCoef G s φ =
    (liftOp N (Dec2.Gsx (coverOf G) G a aT 0 (ν + x) α s) -
        (1 + (x : ℂ))⁻¹ • liftOp N (Matrix.diagonal (cubeSigma G s)) +
        liftOp N (Dec2.Gsx (coverOf G) G a aT 0 (ν + x) α s) * fieldMul (restrictField G φ) *
          (Dec2.decM (coverOf G) G a aT 0 (ν + x) α s φ)⁻¹ *
          commK (xDirichletOperator G a aT 0 (ν + x) α) (restrictField G φ) *
          liftOp N (Dec2.Gsx (coverOf G) G a aT 0 (ν + x) α s)) * (1 - fieldProj G φ) := by
  set Gl := liftOp N (Dec2.Gsx (coverOf G) G a aT 0 (ν + x) α s) with hGl
  set F := fieldMul (restrictField G φ) with hF
  set K := commK (xDirichletOperator G a aT 0 (ν + x) α) (restrictField G φ) with hK
  have hdet := (Matrix.isUnit_iff_isUnit_det _).1 hMu
  have hMi : (Dec2.decM (coverOf G) G a aT 0 (ν + x) α s φ)⁻¹ *
      Dec2.decM (coverOf G) G a aT 0 (ν + x) α s φ = 1 := Matrix.nonsing_inv_mul _ hdet
  have hDi : Matrix.diagonal (fun y : G.Ω 1 => ∑ i, φ y i * φ y i) *
      Matrix.diagonal (fun y : G.Ω 1 => (∑ i, φ y i * φ y i)⁻¹) = 1 := by
    rw [Matrix.diagonal_mul_diagonal]
    ext y z
    by_cases h : y = z
    · subst h; simp [hD y]
    · simp [h, Matrix.one_apply_ne h]
  have hid := constrained_pi_identity F K Gl _ _ (fieldMul_transpose_mul_diag _) hDi hMi
  have hPi : Dec2.decPi (coverOf G) G a aT 0 (ν + x) α s φ =
      Gl * F * (Dec2.decM (coverOf G) G a aT 0 (ν + x) α s φ)⁻¹ *
        (Dec2.decN (coverOf G) G a aT 0 (ν + x) α s φ) := rfl
  have hPi' : Dec2.decPi (coverOf G) G a aT 0 (ν + x) α s φ =
      Gl * fieldProj G φ - Gl * F * (Dec2.decM (coverOf G) G a aT 0 (ν + x) α s φ)⁻¹ * K * Gl *
        (1 - fieldProj G φ) := by
    rw [hPi]
    exact hid
  rw [hPi']
  unfold baseCovXCoef
  simp only [Matrix.sub_mul, Matrix.add_mul, Matrix.smul_mul, Matrix.mul_sub, Matrix.mul_one,
    smul_add, smul_sub, Matrix.mul_assoc]
  abel

end Coef

end Balaban.LargeField.Base
