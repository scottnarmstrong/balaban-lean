/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.Decoupled2XLocal
public import Balaban.Localization.Decoupled2XGrad
public import Balaban.Localization.DecoupledXClose

/-!
# (DG6): closeness of `G_{k,x,s}(A)` to `G_{k,x}(A)` away from the parameters, for a cover `C`
-/

@[expose] public section

namespace Balaban.Localization.Dec2

open Balaban Balaban.Multiscale Balaban.Background Finset Matrix

variable {d L N₁ m₁ k : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
variable {C : DecCover d L N₁ m₁ (k + 1)} {H : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
  {a : ℕ → ℝ} {aT x ν Cx : ℝ} {α : H.Ω 1 → ℂ} {κ : ℝ}
  {s : ℕ × CTorus d L N₁ m₁ (k + 1) → ℂ}

theorem xDirichlet_isUnit (S : XCover C H a aT ν Cx) (hα : AdmPot H α) (hx : 0 ≤ x) :
    IsUnit (xDirichletOperator H a aT x ν α) :=
  xDirichletOperator_isUnit_sharp H S.hL S.hk S.mass S.ha S.haT1 S.haT2 hx α
    (AdmPot.le_eighth' S.hd hα)

/-- **The algebraic identity behind (DG6)**:
`(G_s - G_D) f = (G*_s - G*_1) g + G_D (𝒦_s - 𝒦_1) g`, `g = (1 - 𝒦_s)⁻¹ f`. -/
theorem Gsx_sub_Gd (S : XCover C H a aT ν Cx) (hα : AdmPot H α) (hx : 0 ≤ x)
    (hU : IsUnit (1 - Kcalx C H a aT x ν α s)) (f : H.Ω 1 → ℂ) :
    Gsx C H a aT x ν α s *ᵥ f - (xDirichletOperator H a aT x ν α)⁻¹ *ᵥ f =
      (Gstarx C H a aT x ν α s - Gstarx C H a aT x ν α (fun _ => 1)) *ᵥ
          ((1 - Kcalx C H a aT x ν α s)⁻¹ *ᵥ f) +
      (xDirichletOperator H a aT x ν α)⁻¹ *ᵥ
        ((Kcalx C H a aT x ν α s - Kcalx C H a aT x ν α (fun _ => 1)) *ᵥ
          ((1 - Kcalx C H a aT x ν α s)⁻¹ *ᵥ f)) := by
  have hHU := xDirichlet_isUnit S hα hx
  have hdetH := (Matrix.isUnit_iff_isUnit_det _).1 hHU
  have hdetK := (Matrix.isUnit_iff_isUnit_det _).1 hU
  have hpar := parametrix_x S hα hx
  set Gd := (xDirichletOperator H a aT x ν α)⁻¹ with hGd
  have h1 : Gstarx C H a aT x ν α (fun _ => 1) =
      Gd * (1 - Kcalx C H a aT x ν α (fun _ => 1)) := by
    rw [← hpar, ← Matrix.mul_assoc, hGd, Matrix.nonsing_inv_mul _ hdetH, Matrix.one_mul]
  set g := (1 - Kcalx C H a aT x ν α s)⁻¹ *ᵥ f with hg
  have hg1 : (1 - Kcalx C H a aT x ν α s) *ᵥ g = f := by
    rw [hg, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdetK, Matrix.one_mulVec]
  have e : Gsx C H a aT x ν α s *ᵥ f = Gstarx C H a aT x ν α s *ᵥ g := by
    rw [hg, Gsx, ← Matrix.mulVec_mulVec]
  have hA1g : Gstarx C H a aT x ν α (fun _ => 1) *ᵥ g =
      Gd *ᵥ (g - Kcalx C H a aT x ν α (fun _ => 1) *ᵥ g) := by
    rw [h1, ← Matrix.mulVec_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec]
  have hf : f = g - Kcalx C H a aT x ν α s *ᵥ g := by
    rw [← hg1, Matrix.sub_mulVec, Matrix.one_mulVec]
  rw [e, Matrix.sub_mulVec, Matrix.sub_mulVec, hA1g, Matrix.mulVec_sub, Matrix.mulVec_sub]
  conv_lhs => rw [hf, Matrix.mulVec_sub]
  abel

/-- At `s ≡ 1` with `1 - 𝒦_1` invertible, `G_{k,x,1} = H_{k,x}⁻¹`. -/
theorem Gsx_one (S : XCover C H a aT ν Cx) (hα : AdmPot H α) (hx : 0 ≤ x)
    (hU : IsUnit (1 - Kcalx C H a aT x ν α (fun _ => 1))) :
    Gsx C H a aT x ν α (fun _ => 1) = (xDirichletOperator H a aT x ν α)⁻¹ := by
  have hdetK := (Matrix.isUnit_iff_isUnit_det _).1 hU
  have hpar := parametrix_x S hα hx
  have h1 : xDirichletOperator H a aT x ν α * Gsx C H a aT x ν α (fun _ => 1) = 1 := by
    unfold Gsx
    rw [← Matrix.mul_assoc, hpar, Matrix.mul_nonsing_inv _ hdetK]
  exact (Matrix.inv_eq_right_inv h1).symm

/-- `(G*_s - G*_1) g` vanishes off `W`. -/
theorem Gstarx_diff_zero (S : XCover C H a aT ν Cx) (hα : AdmPot H α) (hx : 0 ≤ x)
    {W : Finset (CTorus d L N₁ m₁ (k + 1))}
    (hW : ∀ z ∈ C.cubeIdx, C.sProd s z ≠ 1 → intBox z ⊆ W) (g : H.Ω 1 → ℂ)
    {y : CTorus d L N₁ m₁ (k + 1)} (hy : y ∉ W) :
    zeroExt (H.Ω 1) (Gstarx C H a aT x ν α s *ᵥ g) y -
      zeroExt (H.Ω 1) (Gstarx C H a aT x ν α (fun _ => 1) *ᵥ g) y = 0 := by
  rw [zeroExt_Gstarx, zeroExt_Gstarx, ← Finset.sum_sub_distrib]
  refine Finset.sum_eq_zero fun z hz => ?_
  by_cases hc : C.sProd s z = 1
  · rw [hc, C.sProd_one]; ring
  · have hb : y ∉ intBox z := fun h => hy (hW z hz hc h)
    have : zeroExt (H.Ω 1) (cubeGx H a aT x ν α z *ᵥ g) y = 0 := by
      by_cases hyΩ : y ∈ H.Ω 1
      · rw [zeroExt_mem' _ hyΩ]; exact cubeGx_supp S hα hx hz g ⟨y, hyΩ⟩ hb
      · exact zeroExt_not_mem _ _ hyΩ
    rw [this]; simp

/-- `(𝒦_s - 𝒦_1) g` vanishes off `W`. -/
theorem Kcalx_diff_zero (S : XCover C H a aT ν Cx)
    {W : Finset (CTorus d L N₁ m₁ (k + 1))}
    (hW : ∀ z ∈ C.cubeIdx, C.sProd s z ≠ 1 → intBox z ⊆ W) (g : H.Ω 1 → ℂ) {y : H.Ω 1}
    (hy : (y : CTorus d L N₁ m₁ (k + 1)) ∉ W) :
    ((Kcalx C H a aT x ν α s - Kcalx C H a aT x ν α (fun _ => 1)) *ᵥ g) y = 0 := by
  rw [Matrix.sub_mulVec, Pi.sub_apply]
  unfold Kcalx
  rw [Matrix.sum_mulVec, Matrix.sum_mulVec, Finset.sum_apply, Finset.sum_apply,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_eq_zero fun z hz => ?_
  by_cases hc : C.sProd s z = 1
  · rw [hc, C.sProd_one]; ring
  · have hb : (y : CTorus d L N₁ m₁ (k + 1)) ∉ intBox z := fun h => hy (hW z hz hc h)
    have := rowSupp_Kzx_cubeGx (x := x) (α := α) S hz g y hb
    rw [Matrix.smul_mulVec, Matrix.smul_mulVec, Pi.smul_apply, Pi.smul_apply, smul_eq_mul,
      smul_eq_mul, this]
    simp


/-! ### (DG6) in the weighted `L²` form -/


theorem Gd_cwsq_le (S : XCover C H a aT ν Cx) (hα : AdmPot H α) (hx : 0 ≤ x)
    {r : CTorus d L N₁ m₁ (k + 1) → ℝ} (hr : IsAgmonWeight H r) {ε : ℝ} (hε0 : 0 ≤ ε)
    (hε1 : ε ≤ xAgmonRate d L) (h : H.Ω 1 → ℂ) :
    cwsq H (agmonField H ε r ((xDirichletOperator H a aT x ν α)⁻¹ *ᵥ h)) ≤
      256 * agmonSource H ε r h := by
  have hdet := (Matrix.isUnit_iff_isUnit_det _).1 (xDirichlet_isUnit S hα hx)
  have hu : cutXOperator H a aT x ν ∅ α *ᵥ ((xDirichletOperator H a aT x ν α)⁻¹ *ᵥ h) = h := by
    rw [cutXOperator_empty, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet,
      Matrix.one_mulVec]
  have hen := x_agmon_energy_cut H (cutAligned_empty H) (by have := S.hd; omega) S.hL S.hk
    S.mass S.ha S.haT1 S.haT2 hx α (AdmPot.le_eighth' S.hd hα) hr hε0 hε1 hu
  have hE := cutEnergy_nonneg (∅ : Finset (CTorus d L N₁ m₁ (k + 1) × Fin d))
    (agmonField H ε r ((xDirichletOperator H a aT x ν α)⁻¹ *ᵥ h))
  linarith

/-- The closeness constant. -/
noncomputable def closeConstX (d : ℕ) : ℝ := (2048 * (3 * 5 ^ d) ^ 2 + 128) * (16 / 9)

/-- **(DG6), closeness, weighted `L²` form.** If every centre `z` with `s_z ≠ 1` has its
interaction cube inside `W`, then with the weight `e^{ε r}`, `r` the truncated path distance to `W`,
`‖ℓ⁻¹ e^{ε r} (G_{k,x,s} - H_{k,x}⁻¹) f‖² ≤ B e^{2 N₀ κ} ‖ℓ f‖²` (unweighted source). -/
theorem XData.dg6 (D : XData C H a aT ν x α κ s Cx) {W : Finset (CTorus d L N₁ m₁ (k + 1))}
    (hW : ∀ z ∈ C.cubeIdx, C.sProd s z ≠ 1 → intBox z ⊆ W) (T : ℝ) {ε : ℝ} (hε0 : 0 ≤ ε)
    (hε1 : ε ≤ xAgmonRate d L) (f : H.Ω 1 → ℂ) :
    cwsq H (agmonField H ε (truncSetDistR H W T)
        (Gsx C H a aT x ν α s *ᵥ f - (xDirichletOperator H a aT x ν α)⁻¹ *ᵥ f)) ≤
      closeConstX d * Real.exp (N0 d L * κ) ^ 2 * agmonSource H 0 (fun _ => 0) f := by
  have hd : 0 < d := by have := D.st.hd; omega
  have hr := isAgmonWeight_truncSetDistR H W T
  have Hh0 : XWeight H 0 (fun _ => 0) :=
    ⟨isAgmonWeight_zero H, le_rfl, (xAgmonRate_pos hd D.st.hL).le⟩
  have hE1 : 1 ≤ Real.exp (N0 d L * κ) := Real.one_le_exp (by have := D.κ0; positivity)
  have D1 : XData C H a aT ν x α 0 (fun _ => 1) Cx :=
    ⟨D.st, D.Cx_nn, D.pot, D.x0, le_rfl, by
      simp only [mul_zero, Real.exp_zero, mul_one]
      have := cstarX_pos d L D.Cx_nn
      nlinarith [D.big], fun P => by simp⟩
  set g := (1 - Kcalx C H a aT x ν α s)⁻¹ *ᵥ f with hg
  set A := (Gstarx C H a aT x ν α s - Gstarx C H a aT x ν α (fun _ => 1)) *ᵥ g with hA
  set h := (Kcalx C H a aT x ν α s - Kcalx C H a aT x ν α (fun _ => 1)) *ᵥ g with hh
  rw [Gsx_sub_Gd D.st D.pot D.x0 D.isUnit_one_sub f]
  have hsplit : cwsq H (agmonField H ε (truncSetDistR H W T)
      (A + (xDirichletOperator H a aT x ν α)⁻¹ *ᵥ h)) ≤
      2 * cwsq H (agmonField H ε (truncSetDistR H W T) A) +
      2 * cwsq H (agmonField H ε (truncSetDistR H W T) ((xDirichletOperator H a aT x ν α)⁻¹ *ᵥ h)) := by
    unfold cwsq
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun z _ => ?_
    have e : agmonField H ε (truncSetDistR H W T) (A + (xDirichletOperator H a aT x ν α)⁻¹ *ᵥ h) z =
        agmonField H ε (truncSetDistR H W T) A z +
          agmonField H ε (truncSetDistR H W T) ((xDirichletOperator H a aT x ν α)⁻¹ *ᵥ h) z := by
      unfold agmonField; rw [zeroExt_add']; ring
    rw [e]
    set p := agmonField H ε (truncSetDistR H W T) A z
    set q := agmonField H ε (truncSetDistR H W T) ((xDirichletOperator H a aT x ν α)⁻¹ *ᵥ h) z
    have h2 : ‖p + q‖ ^ 2 ≤ 2 * ‖p‖ ^ 2 + 2 * ‖q‖ ^ 2 := by
      have h := norm_add_le p q
      nlinarith [sq_nonneg (‖p‖ - ‖q‖), norm_nonneg p, norm_nonneg q, norm_nonneg (p + q)]
    have h0 := invSqSpacing_nonneg H z
    nlinarith [mul_le_mul_of_nonneg_left h2 h0]
  refine hsplit.trans ?_
  -- the Neumann bound for the intermediate vector
  have hg0 := D.neumann_src Hh0 f
  have hgnn := agmonSource_nonneg H 0 (fun _ => 0) g
  -- the term `A`
  have hAeq : cwsq H (agmonField H ε (truncSetDistR H W T) A) =
      cwsq H (agmonField H 0 (fun _ => 0) A) := by
    unfold cwsq
    refine Finset.sum_congr rfl fun z _ => ?_
    congr 1
    rw [norm_agmonField, norm_agmonField]
    by_cases hz0 : zeroExt (H.Ω 1) A z = 0
    · rw [hz0]; simp
    · have hzΩ : z ∈ H.Ω 1 := by
        by_contra hn; exact hz0 (zeroExt_not_mem _ _ hn)
      have hzW : z ∈ W := by
        by_contra hn
        apply hz0
        have := Gstarx_diff_zero D.st D.pot D.x0 hW g hn
        rw [hA, Matrix.sub_mulVec, zeroExt_sub']
        exact this
      rw [truncSetDistR_of_mem H T hzW hzΩ]
      simp
  have hAbd : cwsq H (agmonField H 0 (fun _ => 0) A) ≤
      2 * (256 * (3 * 5 ^ d : ℝ) ^ 2 * Real.exp (N0 d L * κ) ^ 2 * agmonSource H 0 (fun _ => 0) g) +
      2 * (256 * (3 * 5 ^ d : ℝ) ^ 2 * Real.exp (N0 d L * 0) ^ 2 *
        agmonSource H 0 (fun _ => 0) g) := by
    have := cwsq_agmonField_sub_le (G := H) 0 (fun _ => 0)
      (Gstarx C H a aT x ν α s *ᵥ g) (Gstarx C H a aT x ν α (fun _ => 1) *ᵥ g)
    rw [hA, Matrix.sub_mulVec]
    refine this.trans ?_
    have h1 := cwsq_Gstarx_le D Hh0 g
    have h2 := cwsq_Gstarx_le D1 Hh0 g
    linarith
  -- the term `G_D h`
  have hh_supp : ∀ z : H.Ω 1, h z ≠ 0 → (z : CTorus d L N₁ m₁ (k + 1)) ∈ W := by
    intro z hz
    by_contra hn
    exact hz (Kcalx_diff_zero D.st hW g hn)
  have hSrc : agmonSource H ε (truncSetDistR H W T) h = agmonSource H 0 (fun _ => 0) h := by
    simp only [agmonSource_eq]
    refine Finset.sum_congr rfl fun z _ => ?_
    by_cases hz : h z = 0
    · rw [hz]; simp
    · rw [truncSetDistR_of_mem H T (hh_supp z hz) z.2]; simp
  have hhK : agmonSource H 0 (fun _ => 0) h ≤ (1 / 4) * agmonSource H 0 (fun _ => 0) g := by
    rw [hh, Matrix.sub_mulVec]
    have := agmonSource_sub_le H 0 (fun _ => 0) (Kcalx C H a aT x ν α s *ᵥ g)
      (Kcalx C H a aT x ν α (fun _ => 1) *ᵥ g)
    have h1 := D.dg1 Hh0 g
    have h2 := D1.dg1 Hh0 g
    linarith
  have hBd := Gd_cwsq_le D.st D.pot D.x0 hr hε0 hε1 h
  rw [hAeq]
  have hE2 : 1 ≤ Real.exp (N0 d L * κ) ^ 2 := one_le_pow₀ hE1
  have hn0 : (0 : ℝ) ≤ (3 * 5 ^ d : ℝ) ^ 2 := sq_nonneg _
  simp only [mul_zero, Real.exp_zero, one_pow, mul_one] at hAbd
  have hS0 := agmonSource_nonneg H 0 (fun _ => 0) f
  have key : 2 * cwsq H (agmonField H 0 (fun _ => 0) A) +
      2 * cwsq H (agmonField H ε (truncSetDistR H W T) ((xDirichletOperator H a aT x ν α)⁻¹ *ᵥ h)) ≤
      (1024 * (3 * 5 ^ d : ℝ) ^ 2 * (Real.exp (N0 d L * κ) ^ 2 + 1) + 128) *
        agmonSource H 0 (fun _ => 0) g := by
    have := mul_le_mul_of_nonneg_left hhK (by norm_num : (0 : ℝ) ≤ 256)
    rw [hSrc] at hBd
    nlinarith
  calc _ ≤ _ := key
    _ ≤ (1024 * (3 * 5 ^ d : ℝ) ^ 2 * (Real.exp (N0 d L * κ) ^ 2 + 1) + 128) *
        ((16 / 9) * agmonSource H 0 (fun _ => 0) f) :=
        mul_le_mul_of_nonneg_left hg0 (by positivity)
    _ ≤ _ := by
        unfold closeConstX
        have : (1024 * (3 * 5 ^ d : ℝ) ^ 2 * (Real.exp (N0 d L * κ) ^ 2 + 1) + 128) ≤
            (2048 * (3 * 5 ^ d : ℝ) ^ 2 + 128) * Real.exp (N0 d L * κ) ^ 2 := by
          nlinarith [mul_nonneg hn0 (sub_nonneg.2 hE2)]
        calc _ ≤ ((2048 * (3 * 5 ^ d : ℝ) ^ 2 + 128) * Real.exp (N0 d L * κ) ^ 2) *
              ((16 / 9) * agmonSource H 0 (fun _ => 0) f) :=
            mul_le_mul_of_nonneg_right this (by positivity)
          _ = _ := by ring

end Balaban.Localization.Dec2
