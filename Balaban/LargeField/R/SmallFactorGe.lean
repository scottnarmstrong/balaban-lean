module

public import Balaban.LargeField.R.SmallFactorConsts
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.GCongr

/-!
# The bound (III.5.1): `γ_i - log C_dec(ϰ_i) ≥ 2 A'₃ λ̂_k^{p_R}`

`smallFactor_ge` (Lemma III.5.3, last display) from the explicit exponents of
`SmallFactorConsts.lean`.  The proof is the one of the source: each `γ_i + 3` is at least
`4 A'₃ λ̂_k^{p_R + 4}` (the exponents `2p₀` of `γ₁, γ₂, γ₅` are larger), and (Λ24) absorbs `3 + log 5`.
-/

@[expose] public section

namespace Balaban.LargeField

namespace SmallFactorPar

variable {P : SmallFactorPar} (h : P.Hyp)

include h

private theorem x_pos : 0 < P.lamHat := by linarith [h.lamHat_ge]

private theorem x_ge_one : 1 ≤ P.lamHat := by linarith [h.lamHat_ge]

/-- `λ̂^{2p₀} = λ̂^{p_R} λ̂⁴ (λ̂^{wE})²`. -/
private theorem pow_decomp :
    P.lamHat ^ (2 * P.p0) = P.lamHat ^ P.pR * P.lamHat ^ 4 * (P.lamHat ^ P.wE) ^ 2 := by
  have hx := x_pos h
  have e1 : (P.lamHat ^ P.wE) ^ 2 = P.lamHat ^ (P.wE * 2) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx.le]; norm_num
  have e2 : P.lamHat ^ 4 = P.lamHat ^ (4 : ℝ) := by
    rw [← Real.rpow_natCast]; norm_num
  have e3 : P.lamHat ^ (2 * P.p0) = P.lamHat ^ ((2 * P.p0 : ℕ) : ℝ) := by
    rw [Real.rpow_natCast]
  rw [e1, e2, e3, ← Real.rpow_add hx, ← Real.rpow_add hx]
  congr 1
  unfold pR
  push_cast
  ring

private theorem Y_ge_one : 1 ≤ P.lamHat ^ P.wE :=
  Real.one_le_rpow (x_ge_one h) h.wE_nonneg

private theorem Z_pos : 0 < P.lamHat ^ P.pR := Real.rpow_pos_of_pos (x_pos h) _

private theorem x4_ge : 1 ≤ P.lamHat ^ 4 := one_le_pow₀ (x_ge_one h)

private theorem c4_ge : (16 : ℝ) ^ P.p0 ≤ (4 * P.cStar) ^ (2 * P.p0) := by
  have h1 : (4 : ℝ) ≤ 4 * P.cStar := by nlinarith [h.cStar_ge]
  calc (16 : ℝ) ^ P.p0 = (4 : ℝ) ^ (2 * P.p0) := by rw [pow_mul]; norm_num
    _ ≤ _ := pow_le_pow_left₀ (by norm_num) h1 _

private theorem e2_le : Real.exp (-2 * P.eps) ≤ 1 := by
  rw [Real.exp_le_one_iff]; linarith [h.eps_nonneg]

omit h in
private theorem e2_pos : 0 < Real.exp (-2 * P.eps) := Real.exp_pos _

private theorem c4_pos : 0 < (4 * P.cStar) ^ (2 * P.p0) := by
  have := h.cStar_ge
  positivity

/-- `4 A'₃ ≤ e^{-2ε} γ₀ A₀²/(144 a C_Ŵ² (4c_*)^{2p₀} K₁²)`. -/
private theorem A3_le_a :
    4 * P.A3 ≤ Real.exp (-2 * P.eps) * P.gamma0 * P.A0 ^ 2 /
      (144 * P.a * P.CW ^ 2 * (4 * P.cStar) ^ (2 * P.p0) * P.K1 ^ 2) := by
  have ha := h.a_pos
  have hK := h.K1_ge
  have hC := h.CW_ge
  have hc4 := c4_pos h
  have hQ : 0 ≤ Real.exp (-2 * P.eps) * P.gamma0 / (8 * P.a * P.CW ^ 2 * (4 * P.cStar) ^ (2 * P.p0)) := by
    have := h.gamma0_pos
    have := e2_pos (P := P)
    positivity
  unfold A3
  calc 4 * (Real.exp (-2 * P.eps) * P.gamma0 / (8 * P.a * P.CW ^ 2 * (4 * P.cStar) ^ (2 * P.p0)) *
        min (P.A0 ^ 2 / (72 * P.K1 ^ 2)) (P.A1 ^ 2 / 2))
      ≤ 4 * (Real.exp (-2 * P.eps) * P.gamma0 / (8 * P.a * P.CW ^ 2 * (4 * P.cStar) ^ (2 * P.p0)) *
        (P.A0 ^ 2 / (72 * P.K1 ^ 2))) := by
        gcongr; exact min_le_left _ _
    _ = _ := by
        have : (P.K1) ≠ 0 := by linarith
        have : P.a ≠ 0 := ha.ne'
        have : P.CW ≠ 0 := by linarith
        field_simp
        ring

/-- `4 A'₃ ≤ e^{-2ε} γ₀ A₁²/(4 a C_Ŵ² (4c_*)^{2p₀})`. -/
private theorem A3_le_b :
    4 * P.A3 ≤ Real.exp (-2 * P.eps) * P.gamma0 * P.A1 ^ 2 /
      (4 * P.a * P.CW ^ 2 * (4 * P.cStar) ^ (2 * P.p0)) := by
  have ha := h.a_pos
  have hC := h.CW_ge
  have hc4 := c4_pos h
  have hQ : 0 ≤ Real.exp (-2 * P.eps) * P.gamma0 / (8 * P.a * P.CW ^ 2 * (4 * P.cStar) ^ (2 * P.p0)) := by
    have := h.gamma0_pos
    have := e2_pos (P := P)
    positivity
  unfold A3
  calc 4 * (Real.exp (-2 * P.eps) * P.gamma0 / (8 * P.a * P.CW ^ 2 * (4 * P.cStar) ^ (2 * P.p0)) *
        min (P.A0 ^ 2 / (72 * P.K1 ^ 2)) (P.A1 ^ 2 / 2))
      ≤ 4 * (Real.exp (-2 * P.eps) * P.gamma0 / (8 * P.a * P.CW ^ 2 * (4 * P.cStar) ^ (2 * P.p0)) *
        (P.A1 ^ 2 / 2)) := by
        gcongr; exact min_le_right _ _
    _ = _ := by
        have : P.a ≠ 0 := ha.ne'
        have : P.CW ≠ 0 := by linarith
        field_simp
        ring

/-- `4 A'₃ ≤ γ₀ A₀²/(144 a K₁² 16^{p₀})`. -/
private theorem A3_le_c :
    4 * P.A3 ≤ P.gamma0 * P.A0 ^ 2 / (144 * P.a * P.K1 ^ 2 * 16 ^ P.p0) := by
  refine (A3_le_a h).trans ?_
  have ha := h.a_pos
  have hK := h.K1_ge
  have hC := h.CW_ge
  have hg := h.gamma0_pos
  have hc4 := c4_pos h
  have h16 : (0 : ℝ) < 16 ^ P.p0 := by positivity
  have hCW2 : (1 : ℝ) ≤ P.CW ^ 2 := one_le_pow₀ hC
  have hden : 144 * P.a * P.K1 ^ 2 * 16 ^ P.p0 ≤
      144 * P.a * P.CW ^ 2 * (4 * P.cStar) ^ (2 * P.p0) * P.K1 ^ 2 := by
    have h1 : (16 : ℝ) ^ P.p0 ≤ P.CW ^ 2 * (4 * P.cStar) ^ (2 * P.p0) := by
      calc (16 : ℝ) ^ P.p0 ≤ (4 * P.cStar) ^ (2 * P.p0) := c4_ge h
        _ = 1 * (4 * P.cStar) ^ (2 * P.p0) := by ring
        _ ≤ _ := by gcongr
    have : (0 : ℝ) < 144 * P.a * P.K1 ^ 2 := by positivity
    nlinarith
  have hnum : Real.exp (-2 * P.eps) * P.gamma0 * P.A0 ^ 2 ≤ P.gamma0 * P.A0 ^ 2 := by
    have : 0 ≤ P.gamma0 * P.A0 ^ 2 := by positivity
    nlinarith [e2_le (P := P) h]
  exact div_le_div₀ (by positivity) hnum (by positivity) hden

/-- The lower bound `λ_k^{2p₀} ≥ λ̂^{p_R} λ̂⁴ / 4^{p₀}`. -/
private theorem lamK_pow :
    P.lamHat ^ P.pR * P.lamHat ^ 4 / (4 : ℝ) ^ P.p0 ≤ P.lamK ^ (2 * P.p0) := by
  have hx := x_pos h
  have h1 : (P.lamHat / 2) ^ (2 * P.p0) ≤ P.lamK ^ (2 * P.p0) :=
    pow_le_pow_left₀ (by positivity) h.lamK_ge _
  have h2 : (P.lamHat / 2) ^ (2 * P.p0) = P.lamHat ^ (2 * P.p0) / (4 : ℝ) ^ P.p0 := by
    rw [div_pow]; congr 1; rw [pow_mul]; norm_num
  have h3 : P.lamHat ^ P.pR * P.lamHat ^ 4 ≤ P.lamHat ^ (2 * P.p0) := by
    rw [pow_decomp h]
    have := Y_ge_one h
    have hZ := Z_pos h
    have h4 : (1 : ℝ) ≤ (P.lamHat ^ P.wE) ^ 2 := one_le_pow₀ this
    have : 0 < P.lamHat ^ P.pR * P.lamHat ^ 4 := by positivity
    nlinarith
  calc _ ≤ P.lamHat ^ (2 * P.p0) / (4 : ℝ) ^ P.p0 := by gcongr
    _ = _ := h2.symm
    _ ≤ _ := h1

/-- The lower bound `λ_{k₁}^{2p₀}/Ŵ² ≥ λ̂^{p_R} λ̂⁴/(C_Ŵ² (4c_*)^{2p₀})`. -/
private theorem lamK1_pow :
    P.lamHat ^ P.pR * P.lamHat ^ 4 / (P.CW ^ 2 * (4 * P.cStar) ^ (2 * P.p0)) ≤
      P.lamK1 ^ (2 * P.p0) / P.What ^ 2 := by
  have hx := x_pos h
  have hc := h.cStar_ge
  have hC := h.CW_ge
  have hW := h.What_pos
  have hc4 := c4_pos h
  have hY : 0 < P.lamHat ^ P.wE := Real.rpow_pos_of_pos hx _
  have h1 : (P.lamHat / (4 * P.cStar)) ^ (2 * P.p0) ≤ P.lamK1 ^ (2 * P.p0) :=
    pow_le_pow_left₀ (by positivity) h.lamK1_ge _
  have h2 : (P.lamHat / (4 * P.cStar)) ^ (2 * P.p0) =
      P.lamHat ^ (2 * P.p0) / (4 * P.cStar) ^ (2 * P.p0) := div_pow _ _ _
  have h3 : P.What ^ 2 ≤ (P.CW * P.lamHat ^ P.wE) ^ 2 := by
    gcongr; exact h.What_le
  calc P.lamHat ^ P.pR * P.lamHat ^ 4 / (P.CW ^ 2 * (4 * P.cStar) ^ (2 * P.p0))
      = (P.lamHat ^ (2 * P.p0) / (4 * P.cStar) ^ (2 * P.p0)) / (P.CW * P.lamHat ^ P.wE) ^ 2 := by
        rw [pow_decomp h]
        field_simp
    _ ≤ P.lamK1 ^ (2 * P.p0) / P.What ^ 2 := by
        rw [← h2]
        have hk1 : 0 ≤ P.lamK1 := le_trans (by positivity) h.lamK1_ge
        exact div_le_div₀ (by positivity) h1 (by positivity) h3

private theorem W_pos : 0 < P.lamHat ^ P.pR * P.lamHat ^ 4 := by
  have := Z_pos h
  have := x_pos h
  positivity

theorem gamma3_ge : 4 * P.A3 * (P.lamHat ^ P.pR * P.lamHat ^ 4) ≤ P.gamma3 := by
  have hW := W_pos h
  have ha := h.a_pos
  have hK := h.K1_ge
  have hC := h.CW_ge
  have hg := h.gamma0_pos
  have hc4 := c4_pos h
  have hWh := h.What_pos
  have e2p := e2_pos (P := P)
  have h1 := lamK1_pow h
  have h2 : P.gamma3 = Real.exp (-2 * P.eps) * P.gamma0 * P.A0 ^ 2 / (72 * P.a * P.K1 ^ 2) *
      (P.lamK1 ^ (2 * P.p0) / P.What ^ 2) := by
    unfold gamma3; field_simp
  rw [h2]
  calc 4 * P.A3 * (P.lamHat ^ P.pR * P.lamHat ^ 4)
      ≤ (Real.exp (-2 * P.eps) * P.gamma0 * P.A0 ^ 2 /
      (144 * P.a * P.CW ^ 2 * (4 * P.cStar) ^ (2 * P.p0) * P.K1 ^ 2)) *
        (P.lamHat ^ P.pR * P.lamHat ^ 4) := by gcongr; exact A3_le_a h
    _ ≤ Real.exp (-2 * P.eps) * P.gamma0 * P.A0 ^ 2 / (72 * P.a * P.K1 ^ 2) *
        (P.lamHat ^ P.pR * P.lamHat ^ 4 / (P.CW ^ 2 * (4 * P.cStar) ^ (2 * P.p0))) := by
        have : (0 : ℝ) < P.K1 := by linarith
        have : P.CW ≠ 0 := by linarith
        rw [← sub_nonneg]
        have e : Real.exp (-2 * P.eps) * P.gamma0 * P.A0 ^ 2 / (72 * P.a * P.K1 ^ 2) *
            (P.lamHat ^ P.pR * P.lamHat ^ 4 / (P.CW ^ 2 * (4 * P.cStar) ^ (2 * P.p0))) -
            (Real.exp (-2 * P.eps) * P.gamma0 * P.A0 ^ 2 /
              (144 * P.a * P.CW ^ 2 * (4 * P.cStar) ^ (2 * P.p0) * P.K1 ^ 2)) *
              (P.lamHat ^ P.pR * P.lamHat ^ 4) =
            (Real.exp (-2 * P.eps) * P.gamma0 * P.A0 ^ 2 /
              (144 * P.a * P.CW ^ 2 * (4 * P.cStar) ^ (2 * P.p0) * P.K1 ^ 2)) *
              (P.lamHat ^ P.pR * P.lamHat ^ 4) := by
          field_simp; ring
        rw [e]; positivity
    _ ≤ _ := by
        gcongr

theorem gamma4_ge : 4 * P.A3 * (P.lamHat ^ P.pR * P.lamHat ^ 4) ≤ P.gamma4 + 1 := by
  have hW := W_pos h
  have ha := h.a_pos
  have hC := h.CW_ge
  have hg := h.gamma0_pos
  have hc4 := c4_pos h
  have hWh := h.What_pos
  have e2p := e2_pos (P := P)
  have h1 := lamK1_pow h
  have h2 : P.gamma4 + 1 = Real.exp (-2 * P.eps) * P.gamma0 * P.A1 ^ 2 / (2 * P.a) *
      (P.lamK1 ^ (2 * P.p0) / P.What ^ 2) := by
    unfold gamma4; field_simp; ring
  rw [h2]
  calc 4 * P.A3 * (P.lamHat ^ P.pR * P.lamHat ^ 4)
      ≤ (Real.exp (-2 * P.eps) * P.gamma0 * P.A1 ^ 2 /
      (4 * P.a * P.CW ^ 2 * (4 * P.cStar) ^ (2 * P.p0))) *
        (P.lamHat ^ P.pR * P.lamHat ^ 4) := by gcongr; exact A3_le_b h
    _ ≤ Real.exp (-2 * P.eps) * P.gamma0 * P.A1 ^ 2 / (2 * P.a) *
        (P.lamHat ^ P.pR * P.lamHat ^ 4 / (P.CW ^ 2 * (4 * P.cStar) ^ (2 * P.p0))) := by
        have : P.CW ≠ 0 := by linarith
        rw [← sub_nonneg]
        have e : Real.exp (-2 * P.eps) * P.gamma0 * P.A1 ^ 2 / (2 * P.a) *
            (P.lamHat ^ P.pR * P.lamHat ^ 4 / (P.CW ^ 2 * (4 * P.cStar) ^ (2 * P.p0))) -
            (Real.exp (-2 * P.eps) * P.gamma0 * P.A1 ^ 2 /
              (4 * P.a * P.CW ^ 2 * (4 * P.cStar) ^ (2 * P.p0))) *
              (P.lamHat ^ P.pR * P.lamHat ^ 4) =
            (Real.exp (-2 * P.eps) * P.gamma0 * P.A1 ^ 2 /
              (4 * P.a * P.CW ^ 2 * (4 * P.cStar) ^ (2 * P.p0))) *
              (P.lamHat ^ P.pR * P.lamHat ^ 4) := by
          field_simp; ring
        rw [e]; positivity
    _ ≤ _ := by
        gcongr

/-- The common bound for the exponents `γ₁, γ₂, γ₅`:
`4 A'₃ λ̂^{p_R} λ̂⁴ ≤ G (λ̂^{p_R} λ̂⁴/4^{p₀})/288`, `G = γ₀ A₀²/(a K₁²)`. -/
private theorem core :
    4 * P.A3 * (P.lamHat ^ P.pR * P.lamHat ^ 4) ≤
      P.gamma0 * P.A0 ^ 2 / (P.a * P.K1 ^ 2) *
        ((P.lamHat ^ P.pR * P.lamHat ^ 4) / (4 : ℝ) ^ P.p0) / 288 := by
  have hW := W_pos h
  have ha := h.a_pos
  have hK := h.K1_ge
  have hg := h.gamma0_pos
  have hA0 := h.A0_pos
  have hq4 : (4 : ℝ) ≤ (4 : ℝ) ^ P.p0 := by
    calc (4 : ℝ) = 4 ^ 1 := by norm_num
      _ ≤ 4 ^ P.p0 := pow_le_pow_right₀ (by norm_num) h.p0_pos
  have hq : (0 : ℝ) < (4 : ℝ) ^ P.p0 := by linarith
  have h16 : (16 : ℝ) ^ P.p0 = ((4 : ℝ) ^ P.p0) ^ 2 := by
    rw [← pow_mul, mul_comm, pow_mul]; norm_num
  have hc := A3_le_c h
  rw [h16] at hc
  have hK0 : P.K1 ≠ 0 := by linarith
  have e1 : P.gamma0 * P.A0 ^ 2 / (144 * P.a * P.K1 ^ 2 * ((4 : ℝ) ^ P.p0) ^ 2) =
      P.gamma0 * P.A0 ^ 2 / (P.a * P.K1 ^ 2) / (144 * ((4 : ℝ) ^ P.p0) ^ 2) := by
    field_simp
  rw [e1] at hc
  have hG : 0 < P.gamma0 * P.A0 ^ 2 / (P.a * P.K1 ^ 2) := by positivity
  calc 4 * P.A3 * (P.lamHat ^ P.pR * P.lamHat ^ 4)
      ≤ P.gamma0 * P.A0 ^ 2 / (P.a * P.K1 ^ 2) / (144 * ((4 : ℝ) ^ P.p0) ^ 2) *
        (P.lamHat ^ P.pR * P.lamHat ^ 4) := by gcongr
    _ ≤ _ := by
        rw [← sub_nonneg]
        have e : P.gamma0 * P.A0 ^ 2 / (P.a * P.K1 ^ 2) *
            ((P.lamHat ^ P.pR * P.lamHat ^ 4) / (4 : ℝ) ^ P.p0) / 288 -
            P.gamma0 * P.A0 ^ 2 / (P.a * P.K1 ^ 2) / (144 * ((4 : ℝ) ^ P.p0) ^ 2) *
              (P.lamHat ^ P.pR * P.lamHat ^ 4) =
            P.gamma0 * P.A0 ^ 2 / (P.a * P.K1 ^ 2) * (P.lamHat ^ P.pR * P.lamHat ^ 4) *
              ((4 : ℝ) ^ P.p0 - 2) / (288 * ((4 : ℝ) ^ P.p0) ^ 2) := by
          field_simp; ring
        rw [e]
        have : 0 ≤ (4 : ℝ) ^ P.p0 - 2 := by linarith
        positivity

theorem gamma5_ge : 4 * P.A3 * (P.lamHat ^ P.pR * P.lamHat ^ 4) ≤ P.gamma5 := by
  have hW := W_pos h
  have ha := h.a_pos
  have hK := h.K1_ge
  have hg := h.gamma0_pos
  have hA0 := h.A0_pos
  have hq : (0 : ℝ) < (4 : ℝ) ^ P.p0 := by positivity
  have hK0 : P.K1 ≠ 0 := by linarith
  have hL := lamK_pow h
  have hG : 0 < P.gamma0 * P.A0 ^ 2 / (P.a * P.K1 ^ 2) := by positivity
  have e : P.gamma5 = P.gamma0 * P.A0 ^ 2 / (P.a * P.K1 ^ 2) * P.lamK ^ (2 * P.p0) / 72 := by
    unfold gamma5; field_simp
  refine (core h).trans ?_
  rw [e]
  have := mul_le_mul_of_nonneg_left hL hG.le
  have h0 : 0 ≤ P.gamma0 * P.A0 ^ 2 / (P.a * P.K1 ^ 2) *
      ((P.lamHat ^ P.pR * P.lamHat ^ 4) / (4 : ℝ) ^ P.p0) := by positivity
  linarith

theorem gamma2_ge : 4 * P.A3 * (P.lamHat ^ P.pR * P.lamHat ^ 4) ≤ P.gamma2 + 1 := by
  have hW := W_pos h
  have ha := h.a_pos
  have hK := h.K1_ge
  have hg := h.gamma0_pos
  have hA0 := h.A0_pos
  have hq : (0 : ℝ) < (4 : ℝ) ^ P.p0 := by positivity
  have hK0 : P.K1 ≠ 0 := by linarith
  have hL := lamK_pow h
  have hG : 0 < P.gamma0 * P.A0 ^ 2 / (P.a * P.K1 ^ 2) := by positivity
  have e : P.gamma2 + 1 = (1 - P.eta) * (P.gamma0 * P.A0 ^ 2 / (P.a * P.K1 ^ 2) *
      P.lamK ^ (2 * P.p0)) / 144 := by
    unfold gamma2; field_simp; ring
  refine (core h).trans ?_
  rw [e]
  have h1 := mul_le_mul_of_nonneg_left hL hG.le
  have h2 : 0 ≤ P.gamma0 * P.A0 ^ 2 / (P.a * P.K1 ^ 2) * P.lamK ^ (2 * P.p0) :=
    le_trans (by positivity) h1
  have h3 : (1 / 2 : ℝ) ≤ 1 - P.eta := by linarith [h.eta_le]
  nlinarith

theorem gamma1_ge : 4 * P.A3 * (P.lamHat ^ P.pR * P.lamHat ^ 4) ≤ P.gamma1 + 1 / 2 := by
  have hW := W_pos h
  have ha := h.a_pos
  have hK := h.K1_ge
  have hg := h.gamma0_pos
  have hA0 := h.A0_pos
  have hq : (0 : ℝ) < (4 : ℝ) ^ P.p0 := by positivity
  have hK0 : P.K1 ≠ 0 := by linarith
  have hL := lamK_pow h
  have hG : 0 < P.gamma0 * P.A0 ^ 2 / (P.a * P.K1 ^ 2) := by positivity
  have e : P.gamma1 + 1 / 2 = 9 / 8 * (1 - P.eta) * P.K1 ^ 2 *
      (P.gamma0 * P.A0 ^ 2 / (P.a * P.K1 ^ 2) * P.lamK ^ (2 * P.p0)) := by
    unfold gamma1; field_simp; ring
  refine (core h).trans ?_
  rw [e]
  have h1 := mul_le_mul_of_nonneg_left hL hG.le
  have h2 : 0 ≤ P.gamma0 * P.A0 ^ 2 / (P.a * P.K1 ^ 2) * P.lamK ^ (2 * P.p0) :=
    le_trans (by positivity) h1
  have h3 : (1 / 2 : ℝ) ≤ 1 - P.eta := by linarith [h.eta_le]
  have h4 : (1 : ℝ) ≤ P.K1 ^ 2 := one_le_pow₀ h.K1_ge
  have h5 : (9 / 16 : ℝ) ≤ 9 / 8 * (1 - P.eta) * P.K1 ^ 2 := by nlinarith
  nlinarith

omit h in
theorem A3_nonneg (hh : P.Hyp) : 0 ≤ P.A3 := by
  have ha := hh.a_pos
  have hg := hh.gamma0_pos
  have hC := hh.CW_ge
  have hc4 := c4_pos hh
  have hA0 := hh.A0_pos
  have hA1 := hh.A1_pos
  have hK : 0 < P.K1 := by linarith [hh.K1_ge]
  have := e2_pos (P := P)
  unfold A3
  have : 0 ≤ min (P.A0 ^ 2 / (72 * P.K1 ^ 2)) (P.A1 ^ 2 / 2) :=
    le_min (by positivity) (by positivity)
  positivity

/-- **(III.5.1)** (Lemma III.5.3): `γ_i - log C_dec(ϰ_i) ≥ 2 A'₃ λ̂_k^{p_R}` for the five exponents
(`i = 0, …, 4` for `ϰ₁, …, ϰ₅`, `C_dec ≡ 5`). -/
theorem smallFactor_ge (i : Fin 5) :
    2 * P.A3 * P.lamHat ^ P.pR ≤ P.gamma i - Real.log (cDec i) := by
  have hZ := Z_pos h
  have hA3 := A3_nonneg (P := P) h
  have hx4 := x4_ge h
  have hW : P.lamHat ^ P.pR ≤ P.lamHat ^ P.pR * P.lamHat ^ 4 := by nlinarith
  have hab := h.absorb
  have hc : cDec i = 5 := rfl
  rw [hc]
  have key : 4 * P.A3 * P.lamHat ^ P.pR ≤ P.gamma i + 3 := by
    have h4 : 4 * P.A3 * P.lamHat ^ P.pR ≤ 4 * P.A3 * (P.lamHat ^ P.pR * P.lamHat ^ 4) := by
      gcongr
    fin_cases i
    · have := gamma1_ge h; simp only [gamma]; linarith
    · have := gamma2_ge h; simp only [gamma]; linarith
    · have := gamma3_ge h; simp only [gamma]; linarith
    · have := gamma4_ge h; simp only [gamma]; linarith
    · have := gamma5_ge h; simp only [gamma]; linarith
  linarith

end SmallFactorPar

/-! ### Inhabitation of the hypotheses -/

/-- An admissible choice of the constants of Lemma III.5.3 (`γ₀ = A₀ = A₁ = a = K₁ = c_* = C_Ŵ = 1`,
`ε = η = 0`, `p₀ = 10`, `wE = 0`, `λ̂ = 100`). -/
noncomputable def SmallFactorPar.example : SmallFactorPar where
  gamma0 := 1
  A0 := 1
  A1 := 1
  a := 1
  K1 := 1
  eps := 0
  cStar := 1
  CW := 1
  p0 := 10
  wE := 0
  eta := 0
  lamK := 50
  lamK1 := 25
  What := 1
  lamHat := 100

/-- The hypotheses of Lemma III.5.3 are inhabited. -/
theorem SmallFactorPar.example_hyp : SmallFactorPar.example.Hyp := by
  have hpR : SmallFactorPar.example.pR = ((16 : ℕ) : ℝ) := by
    unfold SmallFactorPar.pR SmallFactorPar.example; norm_num
  have hA3 : SmallFactorPar.example.A3 = 1 / (8 * 4 ^ 20 * 72) := by
    unfold SmallFactorPar.A3 SmallFactorPar.example
    norm_num
  have hlog : Real.log 5 ≤ 5 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 5 by norm_num)
    linarith
  have hab : 3 + Real.log 5 ≤ 2 * SmallFactorPar.example.A3 * SmallFactorPar.example.lamHat ^
      SmallFactorPar.example.pR := by
    rw [hA3, hpR, Real.rpow_natCast]
    show 3 + Real.log 5 ≤ 2 * (1 / (8 * 4 ^ 20 * 72)) * (100 : ℝ) ^ 16
    norm_num
    linarith
  have hWle : SmallFactorPar.example.What ≤ SmallFactorPar.example.CW *
      SmallFactorPar.example.lamHat ^ SmallFactorPar.example.wE := by
    show (1 : ℝ) ≤ 1 * (100 : ℝ) ^ (0 : ℝ)
    norm_num
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hWle, ?_, hab⟩
  all_goals (unfold SmallFactorPar.example; norm_num)

/-- The set of admissible parameters of Lemma III.5.3 is nonempty. -/
theorem nonempty_smallFactorPar : ∃ P : SmallFactorPar, P.Hyp := ⟨_, SmallFactorPar.example_hyp⟩

end Balaban.LargeField
