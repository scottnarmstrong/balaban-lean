/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Base.BaseMassShift
public import Balaban.Localization.Decoupled2XAnalytic
public import Balaban.Localization.DecoupledCovariance
public import Balaban.Localization.Dec2Covariance

/-!
# The x-dependent constrained covariance of the first step

For `x ≥ 0` the first step's resolvent `(A_e + x)⁻¹` is the step's machinery at `x' = 0` and
mass `ν + x` (`xDirichletOperator_zero_eq_dirichletOperator`, `base_xCover_massShift_exists`).
The constants of the step's Green function chain do not involve the mass, so the covariance
`(1 + x)⁻¹ P_e + Ĝ_{x,s} - Π_{x,s}` is analytic on the polydisc and bounded there with
constants depending only on `d, L, κ`.
-/

@[expose] public section

namespace Balaban.LargeField.Base

open Balaban Balaban.Multiscale Balaban.Localization Matrix

section Mass

variable {d L N₀ : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ} (G : GeneratingSet d L N₀ 1 ϱ)

/-- The mass enters the Dirichlet operator as a multiple of the identity. -/
theorem dirichletOperator_add_mass (a : ℕ → ℝ) (ν x : ℝ) (α : G.Ω 1 → ℂ) :
    dirichletOperator G a (ν + x) α =
      dirichletOperator G a ν α + (x : ℂ) • (1 : Matrix (G.Ω 1) (G.Ω 1) ℂ) := by
  have h1 : fullMatrix G a (ν + x) =
      fullMatrix G a ν + x • (1 : Matrix (Torus d (N₀ * L ^ 1)) (Torus d (N₀ * L ^ 1)) ℝ) := by
    unfold fullMatrix latticeLaplacian
    have e : (2 * (d : ℝ) + (ν + x)) • (1 : Matrix (Torus d (N₀ * L ^ 1)) (Torus d (N₀ * L ^ 1)) ℝ) =
        (2 * (d : ℝ) + ν) • (1 : Matrix (Torus d (N₀ * L ^ 1)) (Torus d (N₀ * L ^ 1)) ℝ) +
          x • (1 : Matrix (Torus d (N₀ * L ^ 1)) (Torus d (N₀ * L ^ 1)) ℝ) := by
      rw [← add_smul]; congr 1; ring
    rw [e]; abel
  have h2 : ((fullMatrix G a ν +
      x • (1 : Matrix (Torus d (N₀ * L ^ 1)) (Torus d (N₀ * L ^ 1)) ℝ)).map (algebraMap ℝ ℂ)) =
      (fullMatrix G a ν).map (algebraMap ℝ ℂ) +
        (x : ℂ) • (1 : Matrix (Torus d (N₀ * L ^ 1)) (Torus d (N₀ * L ^ 1)) ℂ) := by
    ext i j
    by_cases h : i = j <;> simp [h]
  have h3 : ∀ B : Matrix (Torus d (N₀ * L ^ 1)) (Torus d (N₀ * L ^ 1)) ℂ,
      Green.restrictOp (B + (x : ℂ) • 1) (G.Ω 1) =
        Green.restrictOp B (G.Ω 1) + (x : ℂ) • (1 : Matrix (G.Ω 1) (G.Ω 1) ℂ) := by
    intro B
    ext i j
    by_cases h : i = j
    · subst h; simp [Green.restrictOp]
    · have h' : (i : Torus d (N₀ * L ^ 1)) ≠ j := fun hh => h (Subtype.ext hh)
      simp [Green.restrictOp, h, h']
  unfold dirichletOperator
  rw [h1, h2, h3]
  abel

/-- **The shifted operator is the step's x-variant operator at `x' = 0`, mass `ν + x`.** -/
theorem xDirichletOperator_zero_massShift (hL : 2 ≤ L) {a : ℕ → ℝ} {aT : ℝ} (ha0 : a 0 = 2)
    (ha1 : 0 ≤ a 1) (ha1' : a 1 ≤ 2)
    (haT : aT = 2 * a 1 * (L : ℝ) ^ 2 / (2 * (L : ℝ) ^ 2 - a 1)) (ν x : ℝ) (α : G.Ω 1 → ℂ) :
    xDirichletOperator (k := 0) G a aT 0 (ν + x) α =
      dirichletOperator G a ν α + (x : ℂ) • (1 : Matrix (G.Ω 1) (G.Ω 1) ℂ) := by
  rw [xDirichletOperator_zero_eq_dirichletOperator G hL ha0 ha1 ha1' haT, dirichletOperator_add_mass]

end Mass

section One

variable {d L N₁ m₁ N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ} {x : ℝ}

/-- **L5, the physical point.**  At `s ≡ 1` the x-dependent constrained covariance
`(1 + x)⁻¹ P_e + Ĝ_{0,1} - Π_{0,1}` (the step's `Gsx` and `decPi` at `x' = 0` and mass `ν + x`) is
the two-sided inverse of `A_e + x`, hence equals `baseResolvent`. -/
theorem baseCovX_one {G : GeneratingSet d L (N₁ * L ^ m₁) 1 ϱ} {a : ℕ → ℝ} {aT ν Cx : ℝ}
    (S : Dec2.XCover (coverOf G) G a aT (ν + x) Cx) (hCx : 0 ≤ Cx) (hx : 0 ≤ x)
    (ha0 : a 0 = 2) (ha1 : 0 ≤ a 1) (ha1' : a 1 ≤ 2)
    (haT : aT = 2 * a 1 * (L : ℝ) ^ 2 / (2 * (L : ℝ) ^ 2 - a 1))
    {α : G.Ω 1 → ℂ} (hα : AdmPot G α)
    (hM : Dec2.cstarX d L Cx ≤ (L : ℝ) ^ m₁) {δ : ℝ} (hδ : 0 ≤ δ)
    (hsm : δ ^ 2 * smallConstX d L 0 ≤ 1 / 4)
    {φ : Balaban.Localization.CTorus d L N₁ m₁ 1 → Fin N → ℂ} (hφ : IsConstraintField G δ φ)
    (hsq : ∀ z : G.Ω 1, ∑ i, φ z i * φ z i = 1) :
    baseResolvent N (restrictField G φ) (baseHamiltonian G a ν α (fun _ => 1)) x =
      (1 + (x : ℂ))⁻¹ • basePart (restrictField G φ) +
        liftOp N (Dec2.Gsx (coverOf G) G a aT 0 (ν + x) α (fun _ => 1)) -
        Dec2.decPi (coverOf G) G a aT 0 (ν + x) α (fun _ => 1) φ ∧
      (baseOp N (restrictField G φ) (baseHamiltonian G a ν α (fun _ => 1)) +
          (x : ℂ) • (1 : Matrix (G.Ω 1 × Fin N) (G.Ω 1 × Fin N) ℂ)) *
        ((1 + (x : ℂ))⁻¹ • basePart (restrictField G φ) +
          liftOp N (Dec2.Gsx (coverOf G) G a aT 0 (ν + x) α (fun _ => 1)) -
          Dec2.decPi (coverOf G) G a aT 0 (ν + x) α (fun _ => 1) φ) = 1 := by
  have hL3 : 3 ≤ L := S.hL
  have D : Dec2.XData (coverOf G) G a aT (ν + x) 0 α 0 (fun _ => 1) Cx :=
    ⟨S, hCx, hα, le_rfl, le_rfl, by simpa using hM, fun P => by simp⟩
  have hGs := Dec2.Gsx_one S hα le_rfl D.isUnit_one_sub
  have hXD := xDirichletOperator_zero_massShift G (by omega) ha0 ha1 ha1' haT ν x α
  have hMu := decM_isUnit_cover D hφ hδ hsm
  rw [hXD] at hGs
  have hHu : IsUnit (dirichletOperator G a ν α + (x : ℂ) • (1 : Matrix (G.Ω 1) (G.Ω 1) ℂ)) := by
    rw [← hXD]; exact Dec2.xDirichlet_isUnit S hα le_rfl
  have hdet := (Matrix.isUnit_iff_isUnit_det _).1 hHu
  have hHG := Matrix.mul_nonsing_inv _ hdet
  have hGH := Matrix.nonsing_inv_mul _ hdet
  have hx1 : 1 + (x : ℂ) ≠ 0 := by
    have : (1 : ℝ) + x ≠ 0 := by linarith
    exact_mod_cast this
  have hMu' : IsUnit (constraintM (dirichletOperator G a ν α + (x : ℂ) • 1)
      (dirichletOperator G a ν α + (x : ℂ) • 1)⁻¹ (restrictField G φ)) := by
    have e : Dec2.decM (coverOf G) G a aT 0 (ν + x) α (fun _ => 1) φ =
        constraintM (dirichletOperator G a ν α + (x : ℂ) • 1)
          (dirichletOperator G a ν α + (x : ℂ) • 1)⁻¹ (restrictField G φ) := by
      simp only [Dec2.decM, hXD, hGs]
    rw [← e]; exact hMu
  have key := baseOp_shift_mul_constrainedCov (N := N) (H := dirichletOperator G a ν α) x hx1
    hHG hGH (fun z => hsq z) hMu'
  have eN : Dec2.decN (coverOf G) G a aT 0 (ν + x) α (fun _ => 1) φ =
      constraintN (dirichletOperator G a ν α + (x : ℂ) • 1)
        (dirichletOperator G a ν α + (x : ℂ) • 1)⁻¹ (restrictField G φ) := by
    simp only [Dec2.decN, hXD, hGs]
  have eM : Dec2.decM (coverOf G) G a aT 0 (ν + x) α (fun _ => 1) φ =
      constraintM (dirichletOperator G a ν α + (x : ℂ) • 1)
        (dirichletOperator G a ν α + (x : ℂ) • 1)⁻¹ (restrictField G φ) := by
    simp only [Dec2.decM, hXD, hGs]
  have hPi : Dec2.decPi (coverOf G) G a aT 0 (ν + x) α (fun _ => 1) φ =
      liftOp N (dirichletOperator G a ν α + (x : ℂ) • 1)⁻¹ * fieldMul (restrictField G φ) *
        (constraintM (dirichletOperator G a ν α + (x : ℂ) • 1)
          (dirichletOperator G a ν α + (x : ℂ) • 1)⁻¹ (restrictField G φ))⁻¹ *
        constraintN (dirichletOperator G a ν α + (x : ℂ) • 1)
          (dirichletOperator G a ν α + (x : ℂ) • 1)⁻¹ (restrictField G φ) := by
    unfold Dec2.decPi
    rw [eN, eM, hGs]
  rw [hPi, hGs, baseHamiltonian_one]
  refine ⟨?_, key.1⟩
  unfold baseResolvent
  exact Matrix.inv_eq_right_inv key.1

end One

section Analytic

variable {d L N₁ m₁ N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ} {x : ℝ}

/-- **L5, analyticity.**  Every entry of the x-dependent constrained covariance
`(1 + x)⁻¹ P_e + Ĝ_{0,s} - Π_{0,s}` (at `x' = 0` and mass `ν + x`) is analytic in
`(s, φ₀, α)` on `DecDom G N κ δ`.  The hypotheses on `κ`, `δ` are those of the step's chain and
do not involve `x` or `ν`. -/
theorem baseCovX_analytic {G : GeneratingSet d L (N₁ * L ^ m₁) 1 ϱ} {a : ℕ → ℝ} {aT ν Cx : ℝ}
    (S : Dec2.XCover (coverOf G) G a aT (ν + x) Cx) (hCx : 0 ≤ Cx) {κ : ℝ} (hκ : 0 ≤ κ)
    (hM : Dec2.cstarX d L Cx * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δ : ℝ} (hδ : 0 ≤ δ)
    (hsm : δ ^ 2 * smallConstX d L κ ≤ 1 / 4) (y z : G.Ω 1 × Fin N) :
    AnalyticOnNhd ℂ
      (fun p : DecData G N =>
        ((1 + (x : ℂ))⁻¹ • basePart (restrictField G p.2.1) +
          liftOp N (Dec2.Gsx (coverOf G) G a aT 0 (ν + x) p.2.2 (Dec2.extS (coverOf G) p.1)) -
          Dec2.decPi (coverOf G) G a aT 0 (ν + x) p.2.2 (Dec2.extS (coverOf G) p.1) p.2.1) y z)
      (DecDom G N κ δ) := by
  intro e he
  have hα : AdmPot G e.2.2 := fun w => (he.2.2 w).le
  have D := xData_cover_of_mem (N := N) S hCx (le_refl (0 : ℝ)) hκ hM he
  have hφ : IsConstraintField G δ e.2.1 := he.2.1.toIsConstraintField
  have hpr : AnalyticAt ℂ (fun p : DecData G N => ((p.1, p.2.2) : DecParams G × (G.Ω 1 → ℂ))) e :=
    AnalyticAt.prod analyticAt_fst (analyticAt_snd.comp analyticAt_snd)
  have hHx : RectAt (fun p : DecData G N => xDirichletOperator G a aT 0 (ν + x) p.2.2) e :=
    RectAt.comp' (f := fun p : DecData G N => ((p.1, p.2.2) : DecParams G × (G.Ω 1 → ℂ)))
      (rectAt_xDirichlet (G := G) a aT 0 (ν + x) ((e.1, e.2.2) : DecParams G × (G.Ω 1 → ℂ))) hpr
  have hGs : RectAt (fun p : DecData G N =>
      Dec2.Gsx (coverOf G) G a aT 0 (ν + x) p.2.2 (Dec2.extS (coverOf G) p.1)) e :=
    RectAt.comp' (f := fun p : DecData G N => ((p.1, p.2.2) : DecParams G × (G.Ω 1 → ℂ)))
      (Dec2.matAt_Gsx S (le_refl (0 : ℝ)) hα D.isUnit_one_sub) hpr
  have hGl := hGs.liftOp (N := N)
  have hHl := hHx.liftOp (N := N)
  have hF := rectAt_fieldMul (G := G) (N := N) e
  have hK : RectAt (fun p : DecData G N =>
      commK (xDirichletOperator G a aT 0 (ν + x) p.2.2) (restrictField G p.2.1)) e := by
    unfold commK
    exact (hF.transpose'.mul hHl).sub (hHx.mul hF.transpose')
  have hMa : RectAt (fun p : DecData G N =>
      Dec2.decM (coverOf G) G a aT 0 (ν + x) p.2.2 (Dec2.extS (coverOf G) p.1) p.2.1) e := by
    unfold Dec2.decM constraintM
    exact (hF.transpose'.mul hF).sub ((hK.mul hGl).mul hF)
  have hNa : RectAt (fun p : DecData G N =>
      Dec2.decN (coverOf G) G a aT 0 (ν + x) p.2.2 (Dec2.extS (coverOf G) p.1) p.2.1) e := by
    unfold Dec2.decN constraintN
    exact hF.transpose'.sub (hK.mul hGl)
  have hdet : (Dec2.decM (coverOf G) G a aT 0 (ν + x) e.2.2 (Dec2.extS (coverOf G) e.1)
      e.2.1).det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).1 (decM_isUnit_cover D hφ hδ hsm)).ne_zero
  have hMi := hMa.inv hdet
  have hPi : RectAt (fun p : DecData G N =>
      Dec2.decPi (coverOf G) G a aT 0 (ν + x) p.2.2 (Dec2.extS (coverOf G) p.1) p.2.1) e := by
    unfold Dec2.decPi
    exact (((hGl.mul hF).mul hMi).mul hNa)
  have hP : RectAt (fun p : DecData G N => basePart (restrictField G p.2.1)) e := by
    unfold basePart
    exact hF.mul hF.transpose'
  exact (((hP.smul_const ((1 + (x : ℂ))⁻¹)).add hGl).sub hPi) y z

end Analytic

end Balaban.LargeField.Base
