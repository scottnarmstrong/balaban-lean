/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.Decoupled2XBounds
public import Balaban.Localization.DecoupledXGreen

/-!
# (DG1), (DG2) for the x-variant decoupled Green's operator, weighted `L²` form, for a cover `C`

`XData C H a aT ν x α κ s Cx` collects the standing data; `XData.dg1`, `XData.isUnit_one_sub`,
`XData.neumann_src`, and the value bound `cwsq_Gstarx_le`.
-/

@[expose] public section

namespace Balaban.Localization.Dec2

open Balaban Balaban.Multiscale Balaban.Background Finset Matrix

variable {d L N₁ m₁ k : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}

/-- The standing data of (DG7): the setting, the potential, `x ≥ 0`, the decoupling vector `s` with
`|s_P| ≤ e^{κ}` and `M₁ ≥ c_* e^{N₀ κ}`. -/
structure XData (C : DecCover d L N₁ m₁ (k + 1)) (H : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ)
    (a : ℕ → ℝ) (aT ν x : ℝ) (α : H.Ω 1 → ℂ) (κ : ℝ)
    (s : ℕ × CTorus d L N₁ m₁ (k + 1) → ℂ) (Cx : ℝ) : Prop where
  st : XCover C H a aT ν Cx
  Cx_nn : 0 ≤ Cx
  pot : AdmPot H α
  x0 : 0 ≤ x
  κ0 : 0 ≤ κ
  big : cstarX d L Cx * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁
  sb : ∀ P, ‖s P‖ ≤ Real.exp κ

variable {C : DecCover d L N₁ m₁ (k + 1)} {H : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
  {a : ℕ → ℝ} {aT x ν Cx : ℝ} {α : H.Ω 1 → ℂ} {κ : ℝ}
  {s : ℕ × CTorus d L N₁ m₁ (k + 1) → ℂ} {ε : ℝ} {r : CTorus d L N₁ m₁ (k + 1) → ℝ}

theorem XData.dg1 (D : XData C H a aT ν x α κ s Cx) (W : XWeight H ε r) (f : H.Ω 1 → ℂ) :
    agmonSource H ε r (Kcalx C H a aT x ν α s *ᵥ f) ≤ (1 / 16) * agmonSource H ε r f :=
  dg1x D.st D.Cx_nn D.pot D.x0 D.κ0 D.big D.sb W.agm W.ε0 W.ε1 f

theorem XData.isUnit_one_sub (D : XData C H a aT ν x α κ s Cx) :
    IsUnit (1 - Kcalx C H a aT x ν α s) := by
  have hW : XWeight H 0 (fun _ => 0) :=
    ⟨isAgmonWeight_zero H, le_rfl, by
      have hd : 0 < d := by have := D.st.hd; omega
      exact (xAgmonRate_pos hd D.st.hL).le⟩
  rw [← Matrix.mulVec_injective_iff_isUnit]
  intro v w hvw
  set z := v - w with hz
  have h0 : (1 - Kcalx C H a aT x ν α s) *ᵥ z = 0 := by
    rw [hz, Matrix.mulVec_sub, hvw, sub_self]
  have h1 : z = Kcalx C H a aT x ν α s *ᵥ z := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec] at h0
    exact sub_eq_zero.1 h0
  have h2 := D.dg1 hW z
  have h3 : agmonSource H 0 (fun _ => 0) z ≤ (1 / 16) * agmonSource H 0 (fun _ => 0) z := by
    calc _ = agmonSource H 0 (fun _ => 0) (Kcalx C H a aT x ν α s *ᵥ z) := by rw [← h1]
      _ ≤ _ := h2
  have hz0 : z = 0 := eq_zero_of_agmonSource_zero (by
    have := agmonSource_nonneg H 0 (fun _ => 0) z
    linarith)
  exact sub_eq_zero.1 hz0

theorem XData.neumann_src (D : XData C H a aT ν x α κ s Cx) (W : XWeight H ε r) (f : H.Ω 1 → ℂ) :
    agmonSource H ε r ((1 - Kcalx C H a aT x ν α s)⁻¹ *ᵥ f) ≤ (16 / 9) * agmonSource H ε r f := by
  set g := (1 - Kcalx C H a aT x ν α s)⁻¹ *ᵥ f with hg
  have hdet := (Matrix.isUnit_iff_isUnit_det _).1 D.isUnit_one_sub
  have hgf : g = f + Kcalx C H a aT x ν α s *ᵥ g := by
    have : (1 - Kcalx C H a aT x ν α s) *ᵥ g = f := by
      rw [hg, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec]
    rw [Matrix.sub_mulVec, Matrix.one_mulVec] at this
    rw [← this]; abel
  have h1 := agmonSource_add_le_t (G := H) ε r f (Kcalx C H a aT x ν α s *ᵥ g) (t := 1 / 3)
    (by norm_num)
  have h2 := D.dg1 W g
  rw [← hgf] at h1
  have hS := agmonSource_nonneg H ε r g
  norm_num at h1
  linarith

theorem Gsx_mulVec (f : H.Ω 1 → ℂ) :
    Gsx C H a aT x ν α s *ᵥ f =
      Gstarx C H a aT x ν α s *ᵥ ((1 - Kcalx C H a aT x ν α s)⁻¹ *ᵥ f) := by
  unfold Gsx
  rw [Matrix.mulVec_mulVec]


theorem chi_mem_Icc (S : XCover C H a aT ν Cx) {q : ℕ × CTorus d L N₁ m₁ (k + 1)}
    (hq : q ∈ C.cubeIdx) (z : H.Ω 1) : 0 ≤ C.chi q z ∧ C.chi q z ≤ 1 :=
  S.chi_unit q hq z.2 (Or.inl rfl)

/-- The zero extension of `G*_{x,s} g` is `∑_q s_q χ_q ũ_q`. -/
theorem zeroExt_Gstarx (g : H.Ω 1 → ℂ) (z : CTorus d L N₁ m₁ (k + 1)) :
    zeroExt (H.Ω 1) (Gstarx C H a aT x ν α s *ᵥ g) z =
      ∑ q ∈ C.cubeIdx, C.sProd s q * (((C.chi q z : ℝ) : ℂ) *
        zeroExt (H.Ω 1) (cubeGx H a aT x ν α q *ᵥ g) z) := by
  by_cases hz : z ∈ H.Ω 1
  · rw [zeroExt_mem' _ hz, Gstarx_mulVec]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [chiD_mulVec, zeroExt_mem' _ hz]
  · rw [zeroExt_not_mem _ _ hz]
    symm
    refine Finset.sum_eq_zero fun q _ => ?_
    rw [zeroExt_not_mem _ _ hz]; simp

theorem norm_sq_Gstarx_le (D : XData C H a aT ν x α κ s Cx) (g : H.Ω 1 → ℂ)
    (z : CTorus d L N₁ m₁ (k + 1)) :
    ‖zeroExt (H.Ω 1) (Gstarx C H a aT x ν α s *ᵥ g) z‖ ^ 2 ≤
      (3 * 5 ^ d : ℝ) * (Real.exp (N0 d L * κ) ^ 2 * ∑ q ∈ C.cubeIdx,
        ‖zeroExt (H.Ω 1) (cubeGx H a aT x ν α q *ᵥ g) z‖ ^ 2) := by
  by_cases hz : z ∈ H.Ω 1
  · set y : H.Ω 1 := ⟨z, hz⟩ with hy
    rw [zeroExt_Gstarx]
    set F : ℕ × CTorus d L N₁ m₁ (k + 1) → H.Ω 1 → ℂ := fun q y' =>
      C.sProd s q * (((C.chi q y' : ℝ) : ℂ) * (cubeGx H a aT x ν α q *ᵥ g) y') with hF
    have hFs : ∀ q ∈ C.cubeIdx, ∀ y' : H.Ω 1,
        (y' : CTorus d L N₁ m₁ (k + 1)) ∉ intBox q → F q y' = 0 := by
      intro q hq y' hy'
      simp only [hF]
      rw [cubeGx_supp D.st D.pot D.x0 hq g y' hy']; simp
    have h := sq_norm_sum_overlap D.st hFs y
    have e : ∑ q ∈ C.cubeIdx, C.sProd s q * (((C.chi q z : ℝ) : ℂ) *
        zeroExt (H.Ω 1) (cubeGx H a aT x ν α q *ᵥ g) z) = ∑ q ∈ C.cubeIdx, F q y := by
      refine Finset.sum_congr rfl fun q _ => ?_
      simp only [hF, zeroExt_mem' _ hz]
      rfl
    rw [e]
    refine h.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun q hq => ?_
    have hsp : ‖C.sProd s q‖ ≤ Real.exp (N0 d L * κ) :=
      C.norm_sProd_le (D.st.card_qset q hq) D.κ0 D.sb
    have hc := chi_mem_Icc D.st hq y
    have hn : ‖F q y‖ ≤ Real.exp (N0 d L * κ) * ‖zeroExt (H.Ω 1) (cubeGx H a aT x ν α q *ᵥ g) z‖ := by
      simp only [hF, norm_mul, Complex.norm_real, Real.norm_of_nonneg hc.1, zeroExt_mem' _ hz]
      calc ‖C.sProd s q‖ * (C.chi q y * ‖(cubeGx H a aT x ν α q *ᵥ g) y‖)
          ≤ Real.exp (N0 d L * κ) * (1 * ‖(cubeGx H a aT x ν α q *ᵥ g) y‖) :=
            mul_le_mul hsp (mul_le_mul_of_nonneg_right hc.2 (norm_nonneg _)) (by
              have := hc.1; positivity) (Real.exp_pos _).le
        _ = _ := by ring
    calc ‖F q y‖ ^ 2 ≤ (Real.exp (N0 d L * κ) *
          ‖zeroExt (H.Ω 1) (cubeGx H a aT x ν α q *ᵥ g) z‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) hn 2
      _ = _ := by ring
  · rw [zeroExt_not_mem _ _ hz]
    simp only [norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
    positivity

theorem cwsq_Gstarx_le (D : XData C H a aT ν x α κ s Cx) (W : XWeight H ε r) (g : H.Ω 1 → ℂ) :
    cwsq H (agmonField H ε r (Gstarx C H a aT x ν α s *ᵥ g)) ≤
      256 * (3 * 5 ^ d : ℝ) ^ 2 * Real.exp (N0 d L * κ) ^ 2 * agmonSource H ε r g := by
  have hn0 : (0 : ℝ) ≤ 3 * 5 ^ d := by positivity
  unfold cwsq
  have h1 : ∀ z : CTorus d L N₁ m₁ (k + 1), invSqSpacing H z *
      ‖agmonField H ε r (Gstarx C H a aT x ν α s *ᵥ g) z‖ ^ 2 ≤
      (3 * 5 ^ d : ℝ) * (Real.exp (N0 d L * κ) ^ 2 * ∑ q ∈ C.cubeIdx,
        invSqSpacing H z * ‖agmonField H ε r (cubeGx H a aT x ν α q *ᵥ g) z‖ ^ 2) := by
    intro z
    have h := norm_sq_Gstarx_le D g z
    have hi := invSqSpacing_nonneg H z
    have hw := Real.exp_pos (ε * r z)
    rw [norm_agmonField, mul_pow]
    calc invSqSpacing H z * (Real.exp (ε * r z) ^ 2 *
          ‖zeroExt (H.Ω 1) (Gstarx C H a aT x ν α s *ᵥ g) z‖ ^ 2)
        ≤ invSqSpacing H z * (Real.exp (ε * r z) ^ 2 * ((3 * 5 ^ d : ℝ) *
          (Real.exp (N0 d L * κ) ^ 2 * ∑ q ∈ C.cubeIdx,
            ‖zeroExt (H.Ω 1) (cubeGx H a aT x ν α q *ᵥ g) z‖ ^ 2))) := by
          gcongr
      _ = _ := by
          rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
            Finset.mul_sum]
          refine Finset.sum_congr rfl fun q _ => ?_
          rw [norm_agmonField]; ring
  calc ∑ z, invSqSpacing H z * ‖agmonField H ε r (Gstarx C H a aT x ν α s *ᵥ g) z‖ ^ 2
      ≤ ∑ z, (3 * 5 ^ d : ℝ) * (Real.exp (N0 d L * κ) ^ 2 * ∑ q ∈ C.cubeIdx,
        invSqSpacing H z * ‖agmonField H ε r (cubeGx H a aT x ν α q *ᵥ g) z‖ ^ 2) :=
        Finset.sum_le_sum fun z _ => h1 z
    _ = (3 * 5 ^ d : ℝ) * (Real.exp (N0 d L * κ) ^ 2 * ∑ q ∈ C.cubeIdx,
        cwsq H (agmonField H ε r (cubeGx H a aT x ν α q *ᵥ g))) := by
        rw [← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_comm]
        rfl
    _ ≤ (3 * 5 ^ d : ℝ) * (Real.exp (N0 d L * κ) ^ 2 * ∑ q ∈ C.cubeIdx,
        256 * agmonSource H ε r (cD H q *ᵥ g)) := by
        gcongr with q hq
        exact cube_cwsq_le D.st D.pot D.x0 hq W.agm W.ε0 W.ε1 g
    _ = 256 * (3 * 5 ^ d : ℝ) * Real.exp (N0 d L * κ) ^ 2 *
        ∑ q ∈ C.cubeIdx, agmonSource H ε r (cD H q *ᵥ g) := by
        rw [← Finset.mul_sum]; ring
    _ ≤ 256 * (3 * 5 ^ d : ℝ) * Real.exp (N0 d L * κ) ^ 2 *
        ((3 * 5 ^ d : ℝ) * agmonSource H ε r g) := by
        gcongr
        exact sum_agmonSource_cD_le D.st ε r g
    _ = _ := by ring

end Balaban.Localization.Dec2
