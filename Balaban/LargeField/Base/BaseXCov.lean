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
public import Balaban.Multiscale.ConstraintMain
public import Balaban.Multiscale.ConstraintSandwich

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

section Bound

variable {d L N₁ m₁ N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}

/-- An entry of a vector field is bounded by the weighted norm `vecM`. -/
theorem entry_sq_le_vecM (G : GeneratingSet d L (N₁ * L ^ m₁) 1 ϱ) (s : G.Ω 1 × Fin N → ℂ)
    (p : G.Ω 1) (i : Fin N) :
    ‖s (p, i)‖ ^ 2 ≤ (L : ℝ) ^ 2 * vecM G 0 (fun _ => 0) s := by
  have hsp : G.spacing (p : Torus d (N₁ * L ^ m₁ * L ^ 1)) = (L : ℝ) ^ 1 :=
    spacing_of_mem_Ωk G (le_refl 1) p.2
  have hL0 : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  unfold vecM wsq
  have h1 := Finset.single_le_sum
    (f := fun y : Torus d (N₁ * L ^ m₁ * L ^ 1) =>
      invSqSpacing G y * (Real.exp (0 * (fun _ => (0 : ℝ)) y) * vn (svec G s y)) ^ 2)
    (fun y _ => mul_nonneg (invSqSpacing_nonneg G y) (sq_nonneg _))
    (Finset.mem_univ (p : Torus d (N₁ * L ^ m₁ * L ^ 1)))
  have h2 : ‖s (p, i)‖ ^ 2 ≤ vn (svec G s p) ^ 2 := by
    rw [vn_sq]
    have := Finset.single_le_sum (f := fun i' : Fin N => ‖svec G s p i'‖ ^ 2)
      (fun _ _ => sq_nonneg _) (Finset.mem_univ i)
    simpa [svec_of_mem] using this
  have h3 : invSqSpacing G (p : Torus d (N₁ * L ^ m₁ * L ^ 1)) = ((L : ℝ) ^ 2)⁻¹ := by
    rw [invSqSpacing_eq G p.2, hsp]; simp
  simp only [zero_mul, Real.exp_zero, one_mul] at h1 ⊢
  rw [h3] at h1
  calc ‖s (p, i)‖ ^ 2 ≤ vn (svec G s p) ^ 2 := h2
    _ = (L : ℝ) ^ 2 * (((L : ℝ) ^ 2)⁻¹ * vn (svec G s p) ^ 2) := by
        field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left h1 (by positivity)

omit [NeZero N₁] in
/-- Entries of a matrix are the components of its action on a basis vector. -/
theorem mulVec_single_entry {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℂ) (p q : ι) :
    (M *ᵥ (Pi.single q 1 : ι → ℂ)) p = M p q := by
  simp [Matrix.mulVec, dotProduct, Pi.single_apply]

/-- The weighted source norm of a basis vector is at most `L²`. -/
theorem vecSrc_single_le (G : GeneratingSet d L (N₁ * L ^ m₁) 1 ϱ) (q : G.Ω 1) (j : Fin N) :
    vecSrc G 0 (fun _ => 0) (Pi.single (q, j) 1 : G.Ω 1 × Fin N → ℂ) ≤ (L : ℝ) ^ 2 := by
  have hsp : G.spacing (q : Torus d (N₁ * L ^ m₁ * L ^ 1)) = (L : ℝ) ^ 1 :=
    spacing_of_mem_Ωk G (le_refl 1) q.2
  unfold vecSrc
  rw [Finset.sum_eq_single j]
  · rw [agmonSource_eq, Finset.sum_eq_single q]
    · simp [Multiscale.comp, hsp]
    · intro z _ hz
      have : Multiscale.comp G (Pi.single (q, j) 1 : G.Ω 1 × Fin N → ℂ) j z = 0 := by
        simp [Multiscale.comp, hz]
      simp [this]
    · simp
  · intro i _ hi
    rw [agmonSource_eq]
    refine Finset.sum_eq_zero fun z _ => ?_
    have : Multiscale.comp G (Pi.single (q, j) 1 : G.Ω 1 × Fin N → ℂ) i z = 0 := by
      simp [Multiscale.comp, hi]
    simp [this]
  · simp

/-- `|u - v|² ≤ 2|u|² + 2|v|²` for the weighted source norm. -/
theorem agmonSource_sub_le (G : GeneratingSet d L (N₁ * L ^ m₁) 1 ϱ) (u v : G.Ω 1 → ℂ) :
    agmonSource G 0 (fun _ => 0) (u - v) ≤
      2 * agmonSource G 0 (fun _ => 0) u + 2 * agmonSource G 0 (fun _ => 0) v := by
  simp only [agmonSource_eq, Pi.sub_apply]
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun x _ => ?_
  have h2 : ‖u x - v x‖ ^ 2 ≤ 2 * ‖u x‖ ^ 2 + 2 * ‖v x‖ ^ 2 := by
    have h := norm_sub_le (u x) (v x)
    nlinarith [sq_nonneg (‖u x‖ - ‖v x‖), norm_nonneg (u x), norm_nonneg (v x),
      norm_nonneg (u x - v x)]
  have h0 : 0 ≤ G.spacing x ^ 2 * Real.exp (0 * (fun _ => (0 : ℝ)) x) ^ 2 := by positivity
  nlinarith [mul_le_mul_of_nonneg_left h2 h0]

/-- **Weighted bounds on vector fields.**  With the data `Dec2.XData` at `x' = 0` (the mass `ν` is
arbitrary), the vector fields `Ĝ g` and `Π g` obey `vecM ≤ c E² vecSrc g` with `c` depending on `d`
only and `E = e^{N₀ κ}`. -/
theorem baseCovX_vec_bound {G : GeneratingSet d L (N₁ * L ^ m₁) 1 ϱ} {a : ℕ → ℝ}
    {aT ν Cx κ δ : ℝ} {α : G.Ω 1 → ℂ}
    {s : ℕ × Balaban.Localization.CTorus d L N₁ m₁ 1 → ℂ}
    (D : Dec2.XData (coverOf G) G a aT ν 0 α κ s Cx)
    {φ : Balaban.Localization.CTorus d L N₁ m₁ 1 → Fin N → ℂ} (hφ : IsConstraintField G δ φ)
    (hδ : 0 ≤ δ) (hsm : δ ^ 2 * smallConstX d L κ ≤ 1 / 4) (g : G.Ω 1 × Fin N → ℂ) :
    vecM G 0 (fun _ => 0) (liftOp N (Dec2.Gsx (coverOf G) G a aT 0 ν α s) *ᵥ g) ≤
        valConstX d * Real.exp (N0 d L * κ) ^ 2 * vecSrc G 0 (fun _ => 0) g ∧
      vecM G 0 (fun _ => 0) (Dec2.decPi (coverOf G) G a aT 0 ν α s φ *ᵥ g) ≤
        42 * (valConstX d * Real.exp (N0 d L * κ) ^ 2) * vecSrc G 0 (fun _ => 0) g := by
  have hd : 0 < d := by have := D.st.hd; omega
  have W : XWeight G 0 (fun _ => 0) :=
    ⟨isAgmonWeight_zero G, le_rfl, (xAgmonRate_pos hd D.st.hL).le⟩
  have hV : 0 ≤ valConstX d * Real.exp (N0 d L * κ) ^ 2 := by
    unfold valConstX; positivity
  have hS := vecSrc_nonneg G 0 (fun _ => 0) g
  refine ⟨(Gsx_vec_bounds_cover D W g).1, ?_⟩
  set h : G.Ω 1 → ℂ := (Dec2.decM (coverOf G) G a aT 0 ν α s φ)⁻¹ *ᵥ
    (Dec2.decN (coverOf G) G a aT 0 ν α s φ *ᵥ g) with hh
  have e1 : Dec2.decPi (coverOf G) G a aT 0 ν α s φ *ᵥ g =
      liftOp N (Dec2.Gsx (coverOf G) G a aT 0 ν α s) *ᵥ (fieldMul (restrictField G φ) *ᵥ h) := by
    unfold Dec2.decPi
    rw [hh, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  have A1 : vecM G 0 (fun _ => 0) (liftOp N (Dec2.Gsx (coverOf G) G a aT 0 ν α s) *ᵥ
      (fieldMul (restrictField G φ) *ᵥ h)) ≤ valConstX d * Real.exp (N0 d L * κ) ^ 2 *
        vecSrc G 0 (fun _ => 0) (fieldMul (restrictField G φ) *ᵥ h) :=
    (Gsx_vec_bounds_cover D W (fieldMul (restrictField G φ) *ᵥ h)).1
  have A2 := vecSrc_fieldMul_le (ε := 0) (r := fun _ => 0) hφ h
  have A3 : agmonSource G 0 (fun _ => 0) h ≤
      4 * agmonSource G 0 (fun _ => 0) (Dec2.decN (coverOf G) G a aT 0 ν α s φ *ᵥ g) :=
    decM_inv_le_cover D W hφ hδ hsm (Dec2.decN (coverOf G) G a aT 0 ν α s φ *ᵥ g)
  have hN : Dec2.decN (coverOf G) G a aT 0 ν α s φ *ᵥ g =
      (fieldMul (restrictField G φ))ᵀ *ᵥ g -
        commK (xDirichletOperator G a aT 0 ν α) (restrictField G φ) *ᵥ
          (liftOp N (Dec2.Gsx (coverOf G) G a aT 0 ν α s) *ᵥ g) := by
    unfold Dec2.decN constraintN
    rw [Matrix.sub_mulVec, Matrix.mulVec_mulVec]
  have A4 := agmonSource_sub_le G ((fieldMul (restrictField G φ))ᵀ *ᵥ g)
    (commK (xDirichletOperator G a aT 0 ν α) (restrictField G φ) *ᵥ
          (liftOp N (Dec2.Gsx (coverOf G) G a aT 0 ν α s) *ᵥ g))
  have A5 := agmonSource_fieldMul_transpose_le (ε := 0) (r := fun _ => 0) hφ g
  have A6 : agmonSource G 0 (fun _ => 0) (commK (xDirichletOperator G a aT 0 ν α)
      (restrictField G φ) *ᵥ (liftOp N (Dec2.Gsx (coverOf G) G a aT 0 ν α s) *ᵥ g)) ≤
        δ ^ 2 * kConstX d L κ * vecSrc G 0 (fun _ => 0) g :=
    commKx_Gsx_le_cover D W hφ.toIsSmoothField hδ g
  rw [← hN] at A4
  have hk0 := kConstX_nonneg d L κ
  have hsm' : δ ^ 2 * kConstX d L κ ≤ 1 / 18 := by
    unfold smallConstX at hsm
    nlinarith [sq_nonneg δ]
  have hAh := agmonSource_nonneg G 0 (fun _ => 0) h
  have hn0 := agmonSource_nonneg G 0 (fun _ => 0)
    (Dec2.decN (coverOf G) G a aT 0 ν α s φ *ᵥ g)
  rw [e1]
  have hv : δ ^ 2 * kConstX d L κ * vecSrc G 0 (fun _ => 0) g ≤
      1 / 18 * vecSrc G 0 (fun _ => 0) g := mul_le_mul_of_nonneg_right hsm' hS
  have hb : agmonSource G 0 (fun _ => 0) h ≤
      4 * (2 * (9 / 4 * vecSrc G 0 (fun _ => 0) g) + 2 * (1 / 18 * vecSrc G 0 (fun _ => 0) g)) := by
    calc _ ≤ _ := A3
      _ ≤ _ := by nlinarith
  have hc : vecSrc G 0 (fun _ => 0) (fieldMul (restrictField G φ) *ᵥ h) ≤
      9 / 4 * (4 * (2 * (9 / 4 * vecSrc G 0 (fun _ => 0) g) +
        2 * (1 / 18 * vecSrc G 0 (fun _ => 0) g))) := A2.trans (by nlinarith)
  calc _ ≤ _ := A1
    _ ≤ valConstX d * Real.exp (N0 d L * κ) ^ 2 *
        (9 / 4 * (4 * (2 * (9 / 4 * vecSrc G 0 (fun _ => 0) g) +
          2 * (1 / 18 * vecSrc G 0 (fun _ => 0) g)))) := mul_le_mul_of_nonneg_left hc hV
    _ ≤ _ := by nlinarith [mul_nonneg hV hS]

omit [NeZero N₁] in
theorem basePart_apply {ι : Type*} [Fintype ι] [DecidableEq ι] (e : ι → Fin N → ℂ) (p q : ι)
    (i j : Fin N) :
    basePart e (p, i) (q, j) = if p = q then e p i * e p j else 0 := by
  by_cases h : p = q
  · subst h
    simp [basePart, fieldMul, Matrix.mul_apply, Matrix.transpose_apply]
  · simp [basePart, fieldMul, Matrix.mul_apply, Matrix.transpose_apply, h]

/-- **L5, boundedness, uniform in `x ≥ 0`.**  There is `B`, depending only on `d, L, κ`, such that
every entry of the x-dependent constrained covariance `(1 + x)⁻¹ P_e + Ĝ_{0,s} - Π_{0,s}` (at
`x' = 0` and mass `ν + x`) is bounded by `B`, for every `x ≥ 0`, every mass `ν`, every weights
`a` and `aT`, every setting `G` and every `s` with `‖s_P‖ ≤ e^κ`, in the regime `δ² C(κ) ≤ 1/4`. -/
theorem baseCovX_bound (d L : ℕ) [NeZero L] (κ : ℝ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ {N₁ m₁ N : ℕ} [NeZero N₁] {ϱ : ℝ}
      {G : GeneratingSet d L (N₁ * L ^ m₁) 1 ϱ} {a : ℕ → ℝ} {aT ν Cx x : ℝ}
      (_S : Dec2.XCover (coverOf G) G a aT (ν + x) Cx) (_hCx : 0 ≤ Cx) (_hx : 0 ≤ x)
      (_hκ : 0 ≤ κ) (_hM : Dec2.cstarX d L Cx * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
      {δ : ℝ} (_hδ : 0 ≤ δ) (_hsm : δ ^ 2 * smallConstX d L κ ≤ 1 / 4)
      {α : G.Ω 1 → ℂ} (_hα : AdmPot G α)
      {s : ℕ × Balaban.Localization.CTorus d L N₁ m₁ 1 → ℂ} (_hs : ∀ P, ‖s P‖ ≤ Real.exp κ)
      {φ : Balaban.Localization.CTorus d L N₁ m₁ 1 → Fin N → ℂ}
      (_hφ : IsConstraintField G δ φ) (y z : G.Ω 1 × Fin N),
      ‖((1 + (x : ℂ))⁻¹ • basePart (restrictField G φ) +
          liftOp N (Dec2.Gsx (coverOf G) G a aT 0 (ν + x) α s) -
          Dec2.decPi (coverOf G) G a aT 0 (ν + x) α s φ) y z‖ ≤ B := by
  set V : ℝ := valConstX d * Real.exp (N0 d L * κ) ^ 2 with hV
  have hV0 : 0 ≤ V := by rw [hV]; unfold valConstX; positivity
  have hL0 : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  refine ⟨9 / 4 + Real.sqrt ((L : ℝ) ^ 2 * (V * (L : ℝ) ^ 2)) +
    Real.sqrt ((L : ℝ) ^ 2 * (42 * V * (L : ℝ) ^ 2)), by positivity, ?_⟩
  intro N₁ m₁ N _ ϱ G a aT ν Cx x S hCx hx hκ hM δ hδ hsm α hα s hs φ hφ y z
  obtain ⟨p, i⟩ := y
  obtain ⟨q, j⟩ := z
  have D : Dec2.XData (coverOf G) G a aT (ν + x) 0 α κ s Cx := ⟨S, hCx, hα, le_rfl, hκ, hM, hs⟩
  obtain ⟨hb1, hb2⟩ := baseCovX_vec_bound D hφ hδ hsm (Pi.single (q, j) 1 : G.Ω 1 × Fin N → ℂ)
  have hS := vecSrc_single_le G q j
  have hE1 := entry_sq_le_vecM G (liftOp N (Dec2.Gsx (coverOf G) G a aT 0 (ν + x) α s) *ᵥ
    (Pi.single (q, j) 1 : G.Ω 1 × Fin N → ℂ)) p i
  have hE2 := entry_sq_le_vecM G (Dec2.decPi (coverOf G) G a aT 0 (ν + x) α s φ *ᵥ
    (Pi.single (q, j) 1 : G.Ω 1 × Fin N → ℂ)) p i
  rw [mulVec_single_entry] at hE1 hE2
  have hG : ‖liftOp N (Dec2.Gsx (coverOf G) G a aT 0 (ν + x) α s) (p, i) (q, j)‖ ≤
      Real.sqrt ((L : ℝ) ^ 2 * (V * (L : ℝ) ^ 2)) := by
    refine Real.le_sqrt_of_sq_le (hE1.trans ?_)
    refine mul_le_mul_of_nonneg_left (hb1.trans ?_) (by positivity)
    exact mul_le_mul_of_nonneg_left hS hV0
  have hP : ‖Dec2.decPi (coverOf G) G a aT 0 (ν + x) α s φ (p, i) (q, j)‖ ≤
      Real.sqrt ((L : ℝ) ^ 2 * (42 * V * (L : ℝ) ^ 2)) := by
    refine Real.le_sqrt_of_sq_le (hE2.trans ?_)
    refine mul_le_mul_of_nonneg_left (hb2.trans ?_) (by positivity)
    exact mul_le_mul_of_nonneg_left hS (by positivity)
  have hBase : ‖basePart (restrictField G φ) (p, i) (q, j)‖ ≤ 9 / 4 := by
    rw [basePart_apply]
    split_ifs
    · have h1 : ‖restrictField G φ p i‖ ≤ 3 / 2 :=
        (norm_le_vn (φ p) i).trans (hφ.bound p p.2)
      have h2 : ‖restrictField G φ p j‖ ≤ 3 / 2 :=
        (norm_le_vn (φ p) j).trans (hφ.bound p p.2)
      rw [norm_mul]
      nlinarith [norm_nonneg (restrictField G φ p i), norm_nonneg (restrictField G φ p j)]
    · simp; norm_num
  have hc : ‖(1 + (x : ℂ))⁻¹‖ ≤ 1 := by
    have : (1 + (x : ℂ)) = ((1 + x : ℝ) : ℂ) := by push_cast; ring
    rw [this, norm_inv, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
    exact inv_le_one_of_one_le₀ (by linarith)
  simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  have t1 := norm_sub_le ((1 + (x : ℂ))⁻¹ * basePart (restrictField G φ) (p, i) (q, j) +
    liftOp N (Dec2.Gsx (coverOf G) G a aT 0 (ν + x) α s) (p, i) (q, j))
    (Dec2.decPi (coverOf G) G a aT 0 (ν + x) α s φ (p, i) (q, j))
  have t2 := norm_add_le ((1 + (x : ℂ))⁻¹ * basePart (restrictField G φ) (p, i) (q, j))
    (liftOp N (Dec2.Gsx (coverOf G) G a aT 0 (ν + x) α s) (p, i) (q, j))
  rw [norm_mul] at t2
  have t3 : ‖(1 + (x : ℂ))⁻¹‖ * ‖basePart (restrictField G φ) (p, i) (q, j)‖ ≤ 1 * (9 / 4) :=
    mul_le_mul hc hBase (norm_nonneg _) zero_le_one
  linarith

/-- **The first step's resolvent `(A_e + x)⁻¹` is bounded entrywise, uniformly in `x ≥ 0`.**  The
bound `B` depends only on `d` and `L`. -/
theorem baseResolvent_entry_bound (d L : ℕ) [NeZero L] :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ {N₁ m₁ N : ℕ} [NeZero N₁] {ϱ : ℝ}
      {G : GeneratingSet d L (N₁ * L ^ m₁) 1 ϱ} {a : ℕ → ℝ} {aT ν Cx x : ℝ}
      (_S : Dec2.XCover (coverOf G) G a aT (ν + x) Cx) (_hCx : 0 ≤ Cx) (_hx : 0 ≤ x)
      (_ha0 : a 0 = 2) (_ha1 : 0 ≤ a 1) (_ha1' : a 1 ≤ 2)
      (_haT : aT = 2 * a 1 * (L : ℝ) ^ 2 / (2 * (L : ℝ) ^ 2 - a 1))
      {α : G.Ω 1 → ℂ} (_hα : AdmPot G α)
      (_hM : Dec2.cstarX d L Cx ≤ (L : ℝ) ^ m₁) {δ : ℝ} (_hδ : 0 ≤ δ)
      (_hsm : δ ^ 2 * smallConstX d L 0 ≤ 1 / 4)
      {φ : Balaban.Localization.CTorus d L N₁ m₁ 1 → Fin N → ℂ}
      (_hφ : IsConstraintField G δ φ) (_hsq : ∀ z : G.Ω 1, ∑ i, φ z i * φ z i = 1)
      (y z : G.Ω 1 × Fin N),
      ‖baseResolvent N (restrictField G φ) (baseHamiltonian G a ν α (fun _ => 1)) x y z‖ ≤ B := by
  obtain ⟨B, hB0, H⟩ := baseCovX_bound d L 0
  refine ⟨B, hB0, ?_⟩
  intro N₁ m₁ N _ ϱ G a aT ν Cx x S hCx hx ha0 ha1 ha1' haT α hα hM δ hδ hsm φ hφ hsq y z
  rw [(baseCovX_one S hCx hx ha0 ha1 ha1' haT hα hM hδ hsm hφ hsq).1]
  exact H S hCx hx le_rfl (by simpa using hM) hδ hsm hα (fun P => by simp) hφ y z

end Bound

end Balaban.LargeField.Base
