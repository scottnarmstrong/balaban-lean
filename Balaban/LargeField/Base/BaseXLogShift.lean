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
# The shifted logarithm of the base covariance family: the large-`x` expansion (item 1)

The decoupled covariance of the first step, `C_x(s) = (1+x)⁻¹ P_e + Ĝ_{0,s} - Π_{0,s}` at mass
`ν + x` (`BaseXCov`), is `x⁻¹ c(s) + O(x⁻²)` with the exact large-`x` coefficient
`c(s) = P_e + σ_s (1 - φ₀ (φ₀·φ₀)⁻¹ φ₀ᵀ)`, `σ_s = Σ_q s_q χ_q` (`baseCovXCoef`, `cubeSigma`,
`fieldProj`); it is the identity only at the physical point, which is why `baseCovX_log` exists only
there (`baseCovX_log_not_integrable`).

* `opNorm_Kinv_le`, `opNorm_x_Gsx_sub_sigma_le`, `opNorm_Gsx_sub_sigma_le`: `‖(1-𝒦)⁻¹‖ ≤ 2L`,
  `‖x Ĝ - σ‖ = O(1/x)` and `‖Ĝ - (1+x)⁻¹ σ‖ = O((1+x)⁻²)`;
* `covX_sub_coef`: the exact algebraic identity
  `C_x(s) - (1+x)⁻¹ c(s) = (Ĝ - (1+x)⁻¹ σ + Ĝ φ₀ M⁻¹ K(φ₀) Ĝ)(1 - Q_φ)`
  (from `constrained_pi_identity`);
* `covX_remainder_opNorm_le`: its `ℓ²` operator norm is at most `shiftConst · (1+ν)(1+x)⁻²` for
  `x ≥ 1`;
* `baseCovXShift_entry_le`: **item 1**: the entries of the shifted integrand
  `baseCovXShiftIntegrand = (1+x)⁻¹ c(s) - C_x(s)` are `≤ B (1+ν)(1+x)⁻²` for all `x ≥ 0`,
  uniformly in `s` on the discs `‖s_P‖ ≤ e^κ` and in the constraint fields, with `B = B(d, L, N, κ)`.
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

/-- **Second order of the decoupled Green function**: for `x ≥ 1`,
`‖Ĝ_{x,s} - (1+x)⁻¹ σ_s‖ ≤ (4 c₄ + 2 c₃ e^{N₀κ}) (1+x)⁻²`, `c₃ = 3·5^d`,
`c₄ = 2 L c₃ e^{N₀κ} ((ν+4d+3) + c₃ e^{N₀κ} · 2 (4d+2))`. -/
theorem opNorm_Gsx_sub_sigma_le (D : Dec2.XData (coverOf G) G a aT (ν + x) 0 α κ s Cx)
    (hν : 0 ≤ ν) (hx : 1 ≤ x)
    (ha0 : a 0 = 2) (ha1 : 0 ≤ a 1) (ha1' : a 1 ≤ 2)
    (haT : aT = 2 * a 1 * (L : ℝ) ^ 2 / (2 * (L : ℝ) ^ 2 - a 1)) :
    ‖Dec2.Gsx (coverOf G) G a aT 0 (ν + x) α s -
        (1 + (x : ℂ))⁻¹ • Matrix.diagonal (cubeSigma G s)‖ ≤
      (4 * (2 * L * ((3 * 5 ^ d : ℝ) * Real.exp (N0 d L * κ) * ((ν + 4 * d + 3) +
        (3 * 5 ^ d : ℝ) * Real.exp (N0 d L * κ) * (2 * (4 * d + 2))))) +
        2 * ((3 * 5 ^ d : ℝ) * Real.exp (N0 d L * κ))) * ((1 + x)⁻¹) ^ 2 := by
  have hx0 : 0 ≤ x := by linarith
  have hx1 : 0 < x := by linarith
  set c3 : ℝ := 3 * 5 ^ d with hc3
  set e := Real.exp (N0 d L * κ) with he
  have hc30 : 0 ≤ c3 := by positivity
  have he0 : 0 ≤ e := (Real.exp_pos _).le
  set c4 : ℝ := 2 * L * (c3 * e * ((ν + 4 * d + 3) + c3 * e * (2 * (4 * d + 2)))) with hc4
  have hc40 : 0 ≤ c4 := by positivity
  set u : ℝ := (1 + x)⁻¹ with hu
  have hu0 : 0 < u := by positivity
  have hΓ : 0 < cubeGap L + x := by have := cubeGap_pos L; positivity
  have hΓu : 1 / (cubeGap L + x) ≤ 2 * u := by
    rw [hu, div_le_iff₀ hΓ]
    have := cubeGap_pos L
    field_simp
    nlinarith
  have hxu : 1 / x ≤ 2 * u := by
    rw [hu, div_le_iff₀ hx1]
    field_simp
    nlinarith
  have hxu2 : 1 / (x * (1 + x)) ≤ 2 * u ^ 2 := by
    rw [hu, div_le_iff₀ (by positivity)]
    field_simp
    nlinarith
  set σm : Matrix (G.Ω 1) (G.Ω 1) ℂ := Matrix.diagonal (cubeSigma G s) with hσm
  have h1 := opNorm_x_Gsx_sub_sigma_le D hν hx0 ha0 ha1 ha1' haT
  have hS : ‖σm‖ ≤ c3 * e := by
    refine l2_opNorm_le_of_sqNorm _ (by positivity) fun g => ?_
    unfold sqNorm
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun y _ => ?_
    rw [hσm, Matrix.mulVec_diagonal, norm_mul, mul_pow]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _)
      (norm_cubeSigma_le D.st D.κ0 D.sb y) 2) (sq_nonneg _)
  have hxc : (x : ℂ) ≠ 0 := by exact_mod_cast hx1.ne'
  have h1x : (1 + (x : ℂ)) ≠ 0 := by
    have : (1 : ℝ) + x ≠ 0 := by linarith
    exact_mod_cast this
  have hid : Dec2.Gsx (coverOf G) G a aT 0 (ν + x) α s - (1 + (x : ℂ))⁻¹ • σm =
      (x : ℂ)⁻¹ • ((x : ℂ) • Dec2.Gsx (coverOf G) G a aT 0 (ν + x) α s - σm) +
        (((x : ℂ)⁻¹ - (1 + (x : ℂ))⁻¹) • σm) := by
    rw [smul_sub, smul_smul, inv_mul_cancel₀ hxc, one_smul, sub_smul]
    abel
  have hn1 : ‖(x : ℂ)⁻¹‖ = 1 / x := by
    rw [norm_inv, Complex.norm_real, Real.norm_of_nonneg hx0, one_div]
  have hn2 : ‖(x : ℂ)⁻¹ - (1 + (x : ℂ))⁻¹‖ = 1 / (x * (1 + x)) := by
    have : (x : ℂ)⁻¹ - (1 + (x : ℂ))⁻¹ = (((1 / (x * (1 + x)) : ℝ)) : ℂ) := by
      push_cast
      field_simp
      ring
    rw [this, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  rw [hid]
  have hcx : ‖(x : ℂ) • Dec2.Gsx (coverOf G) G a aT 0 (ν + x) α s - σm‖ ≤ 2 * c4 * u := by
    refine h1.trans ?_
    calc c4 / (cubeGap L + x) = c4 * (1 / (cubeGap L + x)) := by ring
      _ ≤ c4 * (2 * u) := mul_le_mul_of_nonneg_left hΓu hc40
      _ = _ := by ring
  calc _ ≤ ‖(x : ℂ)⁻¹ • ((x : ℂ) • Dec2.Gsx (coverOf G) G a aT 0 (ν + x) α s - σm)‖ +
        ‖((x : ℂ)⁻¹ - (1 + (x : ℂ))⁻¹) • σm‖ := norm_add_le _ _
    _ = (1 / x) * ‖(x : ℂ) • Dec2.Gsx (coverOf G) G a aT 0 (ν + x) α s - σm‖ +
        1 / (x * (1 + x)) * ‖σm‖ := by rw [norm_smul, norm_smul, hn1, hn2]
    _ ≤ (2 * u) * (2 * c4 * u) + (2 * u ^ 2) * (c3 * e) := by
        gcongr
    _ = _ := by ring

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

section Constrained

variable {d L N₁ m₁ N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
  {G : GeneratingSet d L (N₁ * L ^ m₁) 1 ϱ} {a : ℕ → ℝ} {aT ν x Cx κ δ : ℝ} {α : G.Ω 1 → ℂ}
  {s : ℕ × Balaban.Localization.CTorus d L N₁ m₁ 1 → ℂ}
  {φ : Balaban.Localization.CTorus d L N₁ m₁ 1 → Fin N → ℂ}

omit [NeZero L] in
/-- The smallness regime `δ² C ≤ 1/4` forces `δ ≤ 1/2`. -/
theorem delta_le_half (hδ : 0 ≤ δ) (hsm : δ ^ 2 * smallConstX d L κ ≤ 1 / 4) : δ ≤ 1 / 2 := by
  have h2 : (2 : ℝ) ≤ smallConstX d L κ := by
    unfold smallConstX
    have := kConstX_nonneg d L κ
    linarith
  by_contra h
  push Not at h
  nlinarith [mul_le_mul_of_nonneg_left h2 (sq_nonneg δ)]

/-- The bilinear squares of a constraint field stay away from zero. -/
theorem norm_sq_ge_half (hφ : IsConstraintField G δ φ) (hδ : 0 ≤ δ)
    (hsm : δ ^ 2 * smallConstX d L κ ≤ 1 / 4) (y : G.Ω 1) : 1 / 2 ≤ ‖∑ i, φ y i * φ y i‖ := by
  have h1 := hφ.sq y y.2
  have h2 := delta_le_half (κ := κ) (d := d) (L := L) hδ hsm
  have h3 : ‖(1 : ℂ)‖ ≤ ‖∑ i, φ y i * φ y i‖ + ‖∑ i, φ y i * φ y i - 1‖ := by
    have := norm_add_le (∑ i, φ y i * φ y i) (1 - ∑ i, φ y i * φ y i)
    simp only [add_sub_cancel] at this
    rw [norm_sub_rev] at this
    simpa using this
  simp only [norm_one] at h3
  linarith

/-- `‖φ₀ (y)‖` bounds. -/
theorem vn_le_three_halves (hφ : IsConstraintField G δ φ) (y : G.Ω 1) :
    vn (restrictField G φ y) ≤ 3 / 2 := hφ.bound y y.2

/-- **The field projection is bounded**: `‖Q_φ‖ ≤ 9/2`. -/
theorem opNorm_fieldProj_le (hφ : IsConstraintField G δ φ) (hδ : 0 ≤ δ)
    (hsm : δ ^ 2 * smallConstX d L κ ≤ 1 / 4) : ‖fieldProj G φ‖ ≤ 9 / 2 := by
  have hF := l2_opNorm_fieldMul_le (restrictField G φ) (c := 3 / 2) (by norm_num)
    (vn_le_three_halves hφ)
  have hFt := l2_opNorm_fieldMul_transpose_le (restrictField G φ) (c := 3 / 2) (by norm_num)
    (vn_le_three_halves hφ)
  have hDi : ‖Matrix.diagonal (fun y : G.Ω 1 => (∑ i, φ y i * φ y i)⁻¹)‖ ≤ 2 := by
    refine l2_opNorm_le_of_sqNorm _ (by norm_num) fun g => ?_
    unfold sqNorm
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun y _ => ?_
    rw [Matrix.mulVec_diagonal, norm_mul, mul_pow]
    have h1 := norm_sq_ge_half hφ hδ hsm (κ := κ) y
    have h2 : ‖(∑ i, φ y i * φ y i)⁻¹‖ ≤ 2 := by
      rw [norm_inv]
      calc (‖∑ i, φ y i * φ y i‖)⁻¹ ≤ (1 / 2)⁻¹ := inv_anti₀ (by norm_num) h1
        _ = 2 := by norm_num
    exact mul_le_mul_of_nonneg_right (by nlinarith [norm_nonneg (∑ i, φ y i * φ y i)⁻¹]) (sq_nonneg _)
  unfold fieldProj
  calc ‖fieldMul (restrictField G φ) * Matrix.diagonal (fun y : G.Ω 1 => (∑ i, φ y i * φ y i)⁻¹) *
        (fieldMul (restrictField G φ))ᵀ‖
      ≤ ‖fieldMul (restrictField G φ) * Matrix.diagonal (fun y : G.Ω 1 => (∑ i, φ y i * φ y i)⁻¹)‖ *
        ‖(fieldMul (restrictField G φ))ᵀ‖ := Matrix.l2_opNorm_mul _ _
    _ ≤ (‖fieldMul (restrictField G φ)‖ *
        ‖Matrix.diagonal (fun y : G.Ω 1 => (∑ i, φ y i * φ y i)⁻¹)‖) *
        ‖(fieldMul (restrictField G φ))ᵀ‖ := by
        gcongr; exact Matrix.l2_opNorm_mul _ _
    _ ≤ (3 / 2 * 2) * (3 / 2) := by gcongr
    _ = 9 / 2 := by norm_num

/-- The identity has operator norm at most one. -/
theorem l2_opNorm_one_le {ι : Type*} [Fintype ι] [DecidableEq ι] :
    ‖(1 : Matrix ι ι ℂ)‖ ≤ 1 := by
  refine l2_opNorm_le_of_sqNorm _ zero_le_one fun v => ?_
  simp

/-- **`‖1 - Q_φ‖ ≤ 11/2`.** -/
theorem opNorm_one_sub_fieldProj_le (hφ : IsConstraintField G δ φ) (hδ : 0 ≤ δ)
    (hsm : δ ^ 2 * smallConstX d L κ ≤ 1 / 4) : ‖1 - fieldProj G φ‖ ≤ 11 / 2 := by
  have := opNorm_fieldProj_le (κ := κ) hφ hδ hsm
  calc ‖1 - fieldProj G φ‖ ≤ ‖(1 : Matrix (G.Ω 1 × Fin N) (G.Ω 1 × Fin N) ℂ)‖ + ‖fieldProj G φ‖ :=
        norm_sub_le _ _
    _ ≤ 1 + 9 / 2 := add_le_add l2_opNorm_one_le this
    _ = 11 / 2 := by norm_num

/-- **The commutator `K_x(φ₀)` is bounded**, uniformly in the mass and the potential. -/
theorem opNorm_commK_xDir_le (S : Dec2.XCover (coverOf G) G a aT (ν + x) Cx)
    (hφ : IsConstraintField G δ φ)
    (ha0 : a 0 = 2) (ha1 : 0 ≤ a 1) (ha1' : a 1 ≤ 2)
    (haT : aT = 2 * a 1 * (L : ℝ) ^ 2 / (2 * (L : ℝ) ^ 2 - a 1)) :
    ‖commK (xDirichletOperator G a aT 0 (ν + x) α) (restrictField G φ)‖ ≤
      Real.sqrt ((3 * N * (4 * d + 2)) * (3 * (4 * d + 2))) := by
  have hL : 2 ≤ L := by have := S.hL; omega
  have hH : xDirichletOperator (k := 0) G a aT 0 (ν + x) α = dirichletOperator G a (ν + x) α :=
    xDirichletOperator_zero_eq_dirichletOperator G hL ha0 ha1 ha1' haT (ν + x) α
  rw [hH]
  refine opNorm_commK_le _ _ (by positivity)
    (fun z => dirichlet_offdiag_row_le G S.weights (ν + x) α z)
    (fun y => dirichlet_offdiag_col_le G S.weights (ν + x) α y) (fun y i => ?_)
  exact (norm_le_vn (restrictField G φ y) i).trans (vn_le_three_halves hφ y)

/-- **`‖M_{x,s}⁻¹‖ ≤ 2 L`.** -/
theorem opNorm_decM_inv_le (D : Dec2.XData (coverOf G) G a aT (ν + x) 0 α κ s Cx)
    (hφ : IsConstraintField G δ φ) (hδ : 0 ≤ δ) (hsm : δ ^ 2 * smallConstX d L κ ≤ 1 / 4) :
    ‖(Dec2.decM (coverOf G) G a aT 0 (ν + x) α s φ)⁻¹‖ ≤ 2 * L := by
  have hd : 0 < d := by have := D.st.hd; omega
  have hL1 : 1 ≤ L := by have := D.st.hL; omega
  have hL0 : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have W : XWeight G 0 (fun _ => 0) :=
    ⟨isAgmonWeight_zero G, le_rfl, (xAgmonRate_pos hd D.st.hL).le⟩
  refine l2_opNorm_le_of_sqNorm _ (by positivity) fun f => ?_
  have h1 := decM_inv_le_cover D W hφ hδ hsm f
  have h2 := (sqNorm_le_agmonSource_zero hL1 ((Dec2.decM (coverOf G) G a aT 0 (ν + x) α s φ)⁻¹ *ᵥ f)).1
  have h3 := (sqNorm_le_agmonSource_zero (k := 0) hL1 f).2
  refine h2.trans (h1.trans ?_)
  simp only [zero_add, pow_one] at h3
  nlinarith

/-- **`‖Ĝ_{x,s}‖ ≤ (4/3) L · 3·5^d e^{N₀κ} / Γ`.** -/
theorem opNorm_Gsx_le (D : Dec2.XData (coverOf G) G a aT (ν + x) 0 α κ s Cx) (hν : 0 ≤ ν)
    (hx : 0 ≤ x) :
    ‖Dec2.Gsx (coverOf G) G a aT 0 (ν + x) α s‖ ≤
      (4 / 3) * L * ((3 * 5 ^ d : ℝ) * Real.exp (N0 d L * κ)) / (cubeGap L + x) := by
  have hL0 : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hΓ : 0 < cubeGap L + x := by have := cubeGap_pos L; positivity
  set K : ℝ := (4 / 3) * L * ((3 * 5 ^ d : ℝ) * Real.exp (N0 d L * κ)) with hK
  have hK0 : 0 ≤ K := by positivity
  refine l2_opNorm_le_of_sqNorm _ (by positivity) fun g => ?_
  have h := Gsx_sqNorm_le D hν hx g
  have e : (16 / 9) * ((L : ℝ) ^ (0 + 1)) ^ 2 * (3 * 5 ^ d : ℝ) ^ 2 *
      Real.exp (N0 d L * κ) ^ 2 = K ^ 2 := by
    rw [hK]; simp only [zero_add, pow_one]; ring
  rw [e] at h
  have h' : (cubeGap L + x) ^ 2 * sqNorm (Dec2.Gsx (coverOf G) G a aT 0 (ν + x) α s *ᵥ g) ≤
      K ^ 2 * sqNorm g := by simpa [cubeGap] using h
  rw [div_pow, div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
  linarith

end Constrained

section Remainder

variable {d L N₁ m₁ N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
  {G : GeneratingSet d L (N₁ * L ^ m₁) 1 ϱ} {a : ℕ → ℝ} {aT ν x Cx κ δ : ℝ} {α : G.Ω 1 → ℂ}
  {s : ℕ × Balaban.Localization.CTorus d L N₁ m₁ 1 → ℂ}
  {φ : Balaban.Localization.CTorus d L N₁ m₁ 1 → Fin N → ℂ}

/-- Bookkeeping for the constant of `covX_remainder_opNorm_le`. -/
theorem final_ineq {T T' C X u ν : ℝ} (hT : T ≤ T' * (1 + ν)) (hC : 0 ≤ C)
    (hX : 0 ≤ X) (hu : 0 ≤ u ^ 2) (hν : 0 ≤ ν) :
    ((T + C) * u ^ 2 + X * u ^ 2) * (11 / 2) ≤
      (11 / 2 * (T' + C + X)) * (1 + ν) * u ^ 2 := by
  have h1 : T + C ≤ (T' + C) * (1 + ν) := by nlinarith
  have h2 : X ≤ X * (1 + ν) := by nlinarith
  have h3 : (T + C) * u ^ 2 ≤ (T' + C) * (1 + ν) * u ^ 2 := mul_le_mul_of_nonneg_right h1 hu
  have h4 : X * u ^ 2 ≤ X * (1 + ν) * u ^ 2 := mul_le_mul_of_nonneg_right h2 hu
  nlinarith [add_le_add h3 h4]

/-- The componentwise lift is linear. -/
theorem liftOp_sub_smul {ι : Type*} [Fintype ι] [DecidableEq ι] (A B : Matrix ι ι ℂ) (t : ℂ) :
    liftOp N (A - t • B) = liftOp N A - t • liftOp N B := by
  ext p q
  simp only [liftOp, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  split_ifs <;> simp

/-- **The constant of the shifted remainder** (depends on `d, L, N, κ` only). -/
noncomputable def shiftConst (d L N : ℕ) (κ : ℝ) : ℝ :=
  (11 / 2) * (4 * (2 * L * ((3 * 5 ^ d : ℝ) * Real.exp (N0 d L * κ) * ((4 * d + 3) +
      (3 * 5 ^ d : ℝ) * Real.exp (N0 d L * κ) * (2 * (4 * d + 2))))) +
    2 * ((3 * 5 ^ d : ℝ) * Real.exp (N0 d L * κ)) +
    (64 / 3) * (L : ℝ) ^ 3 * ((3 * 5 ^ d : ℝ) * Real.exp (N0 d L * κ)) ^ 2 *
      Real.sqrt ((3 * N * (4 * d + 2)) * (3 * (4 * d + 2))))

theorem shiftConst_nonneg (d L N : ℕ) (κ : ℝ) : 0 ≤ shiftConst d L N κ := by
  unfold shiftConst; positivity

/-- **Second-order large-`x` expansion of the decoupled covariance** (operator norm, `x ≥ 1`):
`‖C_x(s) - (1+x)⁻¹ c(s)‖ ≤ shiftConst · (1+ν) (1+x)⁻²`. -/
theorem covX_remainder_opNorm_le (S : Dec2.XCover (coverOf G) G a aT (ν + x) Cx) (hCx : 0 ≤ Cx)
    (hν : 0 ≤ ν) (hx : 1 ≤ x) (hκ : 0 ≤ κ)
    (hM : Dec2.cstarX d L Cx * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) (hδ : 0 ≤ δ)
    (hsm : δ ^ 2 * smallConstX d L κ ≤ 1 / 4) (hα : AdmPot G α)
    (hs : ∀ P, ‖s P‖ ≤ Real.exp κ) (hφ : IsConstraintField G δ φ)
    (ha0 : a 0 = 2) (ha1 : 0 ≤ a 1) (ha1' : a 1 ≤ 2)
    (haT : aT = 2 * a 1 * (L : ℝ) ^ 2 / (2 * (L : ℝ) ^ 2 - a 1)) :
    ‖((1 + (x : ℂ))⁻¹ • basePart (restrictField G φ) +
        liftOp N (Dec2.Gsx (coverOf G) G a aT 0 (ν + x) α s) -
        Dec2.decPi (coverOf G) G a aT 0 (ν + x) α s φ) -
      (1 + (x : ℂ))⁻¹ • baseCovXCoef G s φ‖ ≤
      shiftConst d L N κ * (1 + ν) * ((1 + x)⁻¹) ^ 2 := by
  have hx0 : 0 ≤ x := by linarith
  have hx1 : 0 < x := by linarith
  have hL0 : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have D := xData_base S hCx hα hκ hM hs
  set c3 : ℝ := 3 * 5 ^ d with hc3
  set e := Real.exp (N0 d L * κ) with he
  have hc30 : 0 ≤ c3 := by positivity
  have he0 : 0 ≤ e := (Real.exp_pos _).le
  set u : ℝ := (1 + x)⁻¹ with hu
  have hu0 : 0 < u := by positivity
  have hΓ : 0 < cubeGap L + x := by have := cubeGap_pos L; positivity
  have hΓu : 1 / (cubeGap L + x) ≤ 2 * u := by
    rw [hu, div_le_iff₀ hΓ]
    have := cubeGap_pos L
    field_simp
    nlinarith
  set κK : ℝ := Real.sqrt ((3 * N * (4 * d + 2)) * (3 * (4 * d + 2))) with hκK
  have hκK0 : 0 ≤ κK := Real.sqrt_nonneg _
  have hMu := decM_isUnit_cover D hφ hδ hsm
  have hDne : ∀ y : G.Ω 1, ∑ i, φ y i * φ y i ≠ 0 := by
    intro y h0
    have := norm_sq_ge_half hφ hδ hsm (κ := κ) y
    rw [h0] at this
    simp at this
    linarith
  rw [covX_sub_coef hMu hDne]
  -- the norms
  set Gl := liftOp N (Dec2.Gsx (coverOf G) G a aT 0 (ν + x) α s) with hGl
  set F := fieldMul (restrictField G φ) with hF
  set Mi := (Dec2.decM (coverOf G) G a aT 0 (ν + x) α s φ)⁻¹ with hMi
  set K := commK (xDirichletOperator G a aT 0 (ν + x) α) (restrictField G φ) with hK
  have hGn : ‖Gl‖ ≤ (8 / 3) * L * (c3 * e) * u := by
    refine (l2_opNorm_liftOp_le _).trans ((opNorm_Gsx_le D hν hx0).trans ?_)
    calc (4 / 3) * L * (c3 * e) / (cubeGap L + x) = ((4 / 3) * L * (c3 * e)) * (1 / (cubeGap L + x)) := by
          ring
      _ ≤ ((4 / 3) * L * (c3 * e)) * (2 * u) :=
          mul_le_mul_of_nonneg_left hΓu (by positivity)
      _ = _ := by ring
  have hFn : ‖F‖ ≤ 3 / 2 :=
    l2_opNorm_fieldMul_le _ (by norm_num) (vn_le_three_halves hφ)
  have hMn : ‖Mi‖ ≤ 2 * L := opNorm_decM_inv_le D hφ hδ hsm
  have hKn : ‖K‖ ≤ κK := opNorm_commK_xDir_le S hφ ha0 ha1 ha1' haT
  have hX : ‖Gl * F * Mi * K * Gl‖ ≤ ((8 / 3) * L * (c3 * e) * u) * (3 / 2) * (2 * L) * κK *
      ((8 / 3) * L * (c3 * e) * u) := by
    calc ‖Gl * F * Mi * K * Gl‖ ≤ ‖Gl * F * Mi * K‖ * ‖Gl‖ := Matrix.l2_opNorm_mul _ _
      _ ≤ (‖Gl * F * Mi‖ * ‖K‖) * ‖Gl‖ := by gcongr; exact Matrix.l2_opNorm_mul _ _
      _ ≤ ((‖Gl * F‖ * ‖Mi‖) * ‖K‖) * ‖Gl‖ := by gcongr; exact Matrix.l2_opNorm_mul _ _
      _ ≤ (((‖Gl‖ * ‖F‖) * ‖Mi‖) * ‖K‖) * ‖Gl‖ := by gcongr; exact Matrix.l2_opNorm_mul _ _
      _ ≤ _ := by gcongr
  have hA1 : ‖Gl - (1 + (x : ℂ))⁻¹ • liftOp N (Matrix.diagonal (cubeSigma G s))‖ ≤
      (4 * (2 * L * (c3 * e * ((ν + 4 * d + 3) + c3 * e * (2 * (4 * d + 2))))) +
        2 * (c3 * e)) * u ^ 2 := by
    rw [hGl, ← liftOp_sub_smul]
    exact (l2_opNorm_liftOp_le _).trans (opNorm_Gsx_sub_sigma_le D hν hx ha0 ha1 ha1' haT)
  have hQ := opNorm_one_sub_fieldProj_le (κ := κ) hφ hδ hsm
  have hν1 : 1 ≤ 1 + ν := by linarith
  calc ‖(Gl - (1 + (x : ℂ))⁻¹ • liftOp N (Matrix.diagonal (cubeSigma G s)) +
          Gl * F * Mi * K * Gl) * (1 - fieldProj G φ)‖
      ≤ ‖Gl - (1 + (x : ℂ))⁻¹ • liftOp N (Matrix.diagonal (cubeSigma G s)) +
          Gl * F * Mi * K * Gl‖ * ‖1 - fieldProj G φ‖ := Matrix.l2_opNorm_mul _ _
    _ ≤ ((4 * (2 * L * (c3 * e * ((ν + 4 * d + 3) + c3 * e * (2 * (4 * d + 2))))) +
        2 * (c3 * e)) * u ^ 2 + ((8 / 3) * L * (c3 * e) * u) * (3 / 2) * (2 * L) * κK *
          ((8 / 3) * L * (c3 * e) * u)) * (11 / 2) := by
        gcongr
        exact (norm_add_le _ _).trans (add_le_add hA1 hX)
    _ ≤ _ := by
        unfold shiftConst
        have hd0 : (0 : ℝ) ≤ d := by positivity
        have hZ0 : 0 ≤ c3 * e * (2 * (4 * d + 2)) := by positivity
        have hT : 4 * (2 * L * (c3 * e * ((ν + 4 * d + 3) + c3 * e * (2 * (4 * d + 2))))) ≤
            4 * (2 * L * (c3 * e * ((4 * d + 3) + c3 * e * (2 * (4 * d + 2))))) * (1 + ν) := by
          have h1 : (ν + 4 * d + 3) + c3 * e * (2 * (4 * d + 2)) ≤
              ((4 * d + 3) + c3 * e * (2 * (4 * d + 2))) * (1 + ν) := by nlinarith
          have h2 : 0 ≤ 4 * (2 * L * c3 * e) := by positivity
          have := mul_le_mul_of_nonneg_left h1 h2
          calc _ = 4 * (2 * L * c3 * e) * ((ν + 4 * d + 3) + c3 * e * (2 * (4 * d + 2))) := by ring
            _ ≤ _ := this
            _ = _ := by ring
        have hX : ((8 / 3) * L * (c3 * e) * u) * (3 / 2) * (2 * L) * κK *
            ((8 / 3) * L * (c3 * e) * u) = (64 / 3) * (L : ℝ) ^ 3 * (c3 * e) ^ 2 * κK * u ^ 2 := by
          ring
        rw [hX]
        exact final_ineq hT (by positivity) (by positivity) (sq_nonneg u) hν

end Remainder

section Integrand

variable {d L N₁ m₁ N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}

/-- **The shifted logarithm integrand** `(1+x)⁻¹ c(s) - C_x(s)` of the first step
(`BASEX.md`, Q5), with `C_x(s) = (1+x)⁻¹ P_e + Ĝ_{0,s} - Π_{0,s}` at mass `ν + x` and
`c(s)` the large-`x` coefficient `baseCovXCoef`.  At the physical point it is
`(1+x)⁻¹ - C_x`, the integrand of `-log A_e` (`baseCovX_log`). -/
noncomputable def baseCovXShiftIntegrand (G : GeneratingSet d L (N₁ * L ^ m₁) 1 ϱ) (a : ℕ → ℝ)
    (aT ν : ℝ) (α : G.Ω 1 → ℂ) (s : ℕ × Balaban.Localization.CTorus d L N₁ m₁ 1 → ℂ)
    (φ : Balaban.Localization.CTorus d L N₁ m₁ 1 → Fin N → ℂ) (x : ℝ) :
    Matrix (G.Ω 1 × Fin N) (G.Ω 1 × Fin N) ℂ :=
  (1 + (x : ℂ))⁻¹ • baseCovXCoef G s φ -
    ((1 + (x : ℂ))⁻¹ • basePart (restrictField G φ) +
      liftOp N (Dec2.Gsx (coverOf G) G a aT 0 (ν + x) α s) -
      Dec2.decPi (coverOf G) G a aT 0 (ν + x) α s φ)

/-- **The coefficient `c(s)` is bounded**: `‖c(s)‖ ≤ 9/4 + (11/2) · 3·5^d e^{N₀κ}`. -/
theorem opNorm_baseCovXCoef_le {G : GeneratingSet d L (N₁ * L ^ m₁) 1 ϱ} {a : ℕ → ℝ}
    {aT ν Cx κ δ : ℝ} {s : ℕ × Balaban.Localization.CTorus d L N₁ m₁ 1 → ℂ}
    {φ : Balaban.Localization.CTorus d L N₁ m₁ 1 → Fin N → ℂ}
    (S : Dec2.XCover (coverOf G) G a aT ν Cx) (hκ : 0 ≤ κ) (hs : ∀ P, ‖s P‖ ≤ Real.exp κ)
    (hφ : IsConstraintField G δ φ) (hδ : 0 ≤ δ) (hsm : δ ^ 2 * smallConstX d L κ ≤ 1 / 4) :
    ‖baseCovXCoef G s φ‖ ≤ 9 / 4 + 11 / 2 * ((3 * 5 ^ d : ℝ) * Real.exp (N0 d L * κ)) := by
  have hF := l2_opNorm_fieldMul_le (restrictField G φ) (c := 3 / 2) (by norm_num)
    (vn_le_three_halves hφ)
  have hFt := l2_opNorm_fieldMul_transpose_le (restrictField G φ) (c := 3 / 2) (by norm_num)
    (vn_le_three_halves hφ)
  have hP : ‖basePart (restrictField G φ)‖ ≤ 9 / 4 := by
    unfold basePart
    calc _ ≤ ‖fieldMul (restrictField G φ)‖ * ‖(fieldMul (restrictField G φ))ᵀ‖ :=
          Matrix.l2_opNorm_mul _ _
      _ ≤ 3 / 2 * (3 / 2) := by gcongr
      _ = 9 / 4 := by norm_num
  have hS : ‖Matrix.diagonal (cubeSigma G s)‖ ≤ (3 * 5 ^ d : ℝ) * Real.exp (N0 d L * κ) := by
    refine l2_opNorm_le_of_sqNorm _ (by positivity) fun g => ?_
    unfold sqNorm
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun y _ => ?_
    rw [Matrix.mulVec_diagonal, norm_mul, mul_pow]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _)
      (norm_cubeSigma_le S hκ hs y) 2) (sq_nonneg _)
  have hQ := opNorm_one_sub_fieldProj_le (κ := κ) hφ hδ hsm
  unfold baseCovXCoef
  calc _ ≤ ‖basePart (restrictField G φ)‖ +
        ‖liftOp N (Matrix.diagonal (cubeSigma G s)) * (1 - fieldProj G φ)‖ := norm_add_le _ _
    _ ≤ 9 / 4 + ‖liftOp N (Matrix.diagonal (cubeSigma G s))‖ * ‖1 - fieldProj G φ‖ :=
        add_le_add hP (Matrix.l2_opNorm_mul _ _)
    _ ≤ 9 / 4 + ((3 * 5 ^ d : ℝ) * Real.exp (N0 d L * κ)) * (11 / 2) := by
        gcongr
        exact (l2_opNorm_liftOp_le _).trans hS
    _ = _ := by ring

/-- **The shifted integrand is `O((1+x)⁻²)` entrywise, uniformly in `x ≥ 0`** (item 1 of the
shifted logarithm): the constant depends on `d, L, N, κ` only, and linearly on `1 + ν`. -/
theorem baseCovXShift_entry_le (d L N : ℕ) [NeZero L] (κ : ℝ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ {N₁ m₁ : ℕ} [NeZero N₁] {ϱ : ℝ}
      {G : GeneratingSet d L (N₁ * L ^ m₁) 1 ϱ} {a : ℕ → ℝ} {aT ν Cx x : ℝ}
      (_S : Dec2.XCover (coverOf G) G a aT (ν + x) Cx) (_hCx : 0 ≤ Cx) (_hν : 0 ≤ ν)
      (_hx : 0 ≤ x) (_hκ : 0 ≤ κ)
      (_hM : Dec2.cstarX d L Cx * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
      {δ : ℝ} (_hδ : 0 ≤ δ) (_hsm : δ ^ 2 * smallConstX d L κ ≤ 1 / 4)
      {α : G.Ω 1 → ℂ} (_hα : AdmPot G α)
      {s : ℕ × Balaban.Localization.CTorus d L N₁ m₁ 1 → ℂ} (_hs : ∀ P, ‖s P‖ ≤ Real.exp κ)
      {φ : Balaban.Localization.CTorus d L N₁ m₁ 1 → Fin N → ℂ}
      (_hφ : IsConstraintField G δ φ)
      (_ha0 : a 0 = 2) (_ha1 : 0 ≤ a 1) (_ha1' : a 1 ≤ 2)
      (_haT : aT = 2 * a 1 * (L : ℝ) ^ 2 / (2 * (L : ℝ) ^ 2 - a 1)) (y z : G.Ω 1 × Fin N),
      ‖baseCovXShiftIntegrand G a aT ν α s φ x y z‖ ≤ B * (1 + ν) * ((1 + x)⁻¹) ^ 2 := by
  obtain ⟨B0, hB00, hdec⟩ := baseCovX_decay d L κ
  set Cc : ℝ := 9 / 4 + 11 / 2 * ((3 * 5 ^ d : ℝ) * Real.exp (N0 d L * κ)) with hCc
  have hCc0 : 0 ≤ Cc := by positivity
  refine ⟨max (shiftConst d L N κ) (4 * (B0 + Cc)), le_max_of_le_left (shiftConst_nonneg d L N κ), ?_⟩
  intro N₁ m₁ _ ϱ G a aT ν Cx x S hCx hν hx hκ hM δ hδ hsm α hα s hs φ hφ ha0 ha1 ha1' haT y z
  have hu0 : 0 < (1 + x)⁻¹ := by positivity
  have hν1 : 1 ≤ 1 + ν := by linarith
  have hneg : baseCovXShiftIntegrand G a aT ν α s φ x =
      -(((1 + (x : ℂ))⁻¹ • basePart (restrictField G φ) +
        liftOp N (Dec2.Gsx (coverOf G) G a aT 0 (ν + x) α s) -
        Dec2.decPi (coverOf G) G a aT 0 (ν + x) α s φ) -
        (1 + (x : ℂ))⁻¹ • baseCovXCoef G s φ) := by
    unfold baseCovXShiftIntegrand; abel
  by_cases hx1 : 1 ≤ x
  · rw [hneg, Matrix.neg_apply, norm_neg]
    refine (norm_entry_le_l2_opNorm _ y z).trans ?_
    refine (covX_remainder_opNorm_le S hCx hν hx1 hκ hM hδ hsm hα hs hφ ha0 ha1 ha1' haT).trans ?_
    gcongr
    exact le_max_left _ _
  · push Not at hx1
    have hu : (1 / 2 : ℝ) ≤ (1 + x)⁻¹ := by
      rw [← one_div, div_le_div_iff₀ (by norm_num) (by linarith)]; linarith
    have hC := hdec S hCx hν hx hκ hM hδ hsm hα hs hφ y z
    have hc := (norm_entry_le_l2_opNorm (baseCovXCoef G s φ) y z).trans
      (opNorm_baseCovXCoef_le S hκ hs hφ hδ hsm)
    have h1 : ‖(1 + (x : ℂ))⁻¹‖ ≤ 1 := by
      have : (1 + (x : ℂ)) = ((1 + x : ℝ) : ℂ) := by push_cast; ring
      rw [this, norm_inv, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
      exact inv_le_one_of_one_le₀ (by linarith)
    have hsum : ‖baseCovXShiftIntegrand G a aT ν α s φ x y z‖ ≤ Cc + B0 := by
      unfold baseCovXShiftIntegrand
      simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
      refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
      · rw [norm_mul]
        calc ‖(1 + (x : ℂ))⁻¹‖ * ‖baseCovXCoef G s φ y z‖ ≤ 1 * Cc :=
              mul_le_mul h1 hc (norm_nonneg _) zero_le_one
          _ = Cc := one_mul _
      · refine hC.trans ?_
        rw [div_le_iff₀ (by linarith)]
        nlinarith
    calc _ ≤ Cc + B0 := hsum
      _ = B0 + Cc := add_comm _ _
      _ ≤ 4 * (B0 + Cc) * (1 + ν) * ((1 + x)⁻¹) ^ 2 := by
          have : (1 : ℝ) ≤ 4 * ((1 + x)⁻¹) ^ 2 := by nlinarith
          have h2 : 0 ≤ B0 + Cc := by positivity
          nlinarith [mul_le_mul_of_nonneg_left this h2]
      _ ≤ _ := by
          gcongr
          exact le_max_right _ _

end Integrand

end Balaban.LargeField.Base
