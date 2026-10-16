/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Base.BaseXSqrt
public import Balaban.LargeField.Base.BaseResolventRange

/-!
# The logarithm of the first step's operator as an integral of the shifted resolvent

The principal logarithm is `log A = ∫₀^∞ ((1 + x)⁻¹ - (A + x)⁻¹) dx`.  For the first step's operator
`A_e = Q_e (H ⊗ I) Q_e + P_e` the integrand is `(1 + x)⁻¹ (A_e - 1) (A_e + x)⁻¹`, which decays like
`(1 + x)⁻²` once the resolvent decays like `(1 + x)⁻¹` (`baseCovX_decay`) and the row sums of
`A_e - 1` are bounded (row sums of `H` are at most `ν + 12 d + 3`).

The integral is taken over the physical point only: `s ≡ 1` and `φ₀ · φ₀ = 1`.  Off this locus the
integral does not exist.  At a parameter `s` the covariance `(1 + x)⁻¹ P_e + Ĝ_{0,s} - Π_{0,s}`
behaves like `x⁻¹ (P_e + (Σ_z s_z χ_z)(1 - φ₀ φ₀ᵀ / (φ₀ · φ₀)))` as `x → ∞`, whose coefficient is
the identity only if `Σ_z s_z χ_z = 1` and `φ₀ · φ₀ = 1`; for example at `s ≡ 0` the covariance is
`(1 + x)⁻¹ P_e`, and `∫ ((1 + x)⁻¹ - (1 + x)⁻¹ P_e) dx` diverges.  The step's logarithm `decLog`
avoids this because the comparison there is `covA`, whose large-`x` behaviour is matched by the
`A Q ⋯ Q* A` structure of its covariance; for `k = 0` there is no such factor.
-/

@[expose] public section

namespace Balaban.LargeField.Base

open Balaban Balaban.Multiscale Balaban.Localization Matrix MeasureTheory Set

section RowSums

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- Row sums of a product. -/
theorem rowSum_mul_le {X Y : Matrix ι ι ℂ} {a b : ℝ} (hb : 0 ≤ b)
    (hX : ∀ y, ∑ w, ‖X y w‖ ≤ a) (hY : ∀ w, ∑ z, ‖Y w z‖ ≤ b) (y : ι) :
    ∑ z, ‖(X * Y) y z‖ ≤ a * b := by
  calc ∑ z, ‖(X * Y) y z‖ ≤ ∑ z, ∑ w, ‖X y w‖ * ‖Y w z‖ := by
        refine Finset.sum_le_sum fun z _ => ?_
        rw [Matrix.mul_apply]
        exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun w _ => (norm_mul _ _).le)
    _ = ∑ w, ‖X y w‖ * ∑ z, ‖Y w z‖ := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun w _ => by rw [Finset.mul_sum]
    _ ≤ ∑ w, ‖X y w‖ * b :=
        Finset.sum_le_sum fun w _ => mul_le_mul_of_nonneg_left (hY w) (norm_nonneg _)
    _ = (∑ w, ‖X y w‖) * b := by rw [Finset.sum_mul]
    _ ≤ a * b := mul_le_mul_of_nonneg_right (hX y) hb

omit [DecidableEq ι] in
/-- Entries of a product, bounded through row sums. -/
theorem entry_mul_le {X Y : Matrix ι ι ℂ} {a b : ℝ} (hb : 0 ≤ b)
    (hX : ∀ y, ∑ w, ‖X y w‖ ≤ a) (hY : ∀ w z, ‖Y w z‖ ≤ b) (y z : ι) :
    ‖(X * Y) y z‖ ≤ a * b := by
  rw [Matrix.mul_apply]
  calc ‖∑ w, X y w * Y w z‖ ≤ ∑ w, ‖X y w‖ * ‖Y w z‖ :=
        (norm_sum_le _ _).trans (Finset.sum_le_sum fun w _ => (norm_mul _ _).le)
    _ ≤ ∑ w, ‖X y w‖ * b :=
        Finset.sum_le_sum fun w _ => mul_le_mul_of_nonneg_left (hY w z) (norm_nonneg _)
    _ = (∑ w, ‖X y w‖) * b := by rw [Finset.sum_mul]
    _ ≤ a * b := mul_le_mul_of_nonneg_right (hX y) hb

theorem rowSum_one (y : ι) : ∑ z, ‖(1 : Matrix ι ι ℂ) y z‖ = 1 := by
  rw [Finset.sum_eq_single y]
  · simp
  · intro z _ hz
    simp [Ne.symm hz]
  · simp

variable {N : ℕ}

omit [DecidableEq ι] in
/-- Row sums of the lift. -/
theorem rowSum_liftOp {A : Matrix ι ι ℂ} {h : ℝ} (hA : ∀ y, ∑ z, ‖A y z‖ ≤ h)
    (y : ι × Fin N) : ∑ z, ‖liftOp N A y z‖ ≤ h := by
  obtain ⟨p, i⟩ := y
  rw [Fintype.sum_prod_type]
  calc ∑ q, ∑ j : Fin N, ‖liftOp N A (p, i) (q, j)‖ = ∑ q, ‖A p q‖ := by
        refine Finset.sum_congr rfl fun q _ => ?_
        rw [Finset.sum_eq_single i]
        · simp [liftOp]
        · intro j _ hj
          simp [liftOp, Ne.symm hj]
        · simp
    _ ≤ h := hA p

/-- Row sums of the projection `P_e`. -/
theorem rowSum_basePart_le (e : ι → Fin N → ℂ) {c : ℝ} (hc : 0 ≤ c) (he : ∀ p i, ‖e p i‖ ≤ c)
    (y : ι × Fin N) : ∑ z, ‖basePart e y z‖ ≤ N * c ^ 2 := by
  obtain ⟨p, i⟩ := y
  rw [Fintype.sum_prod_type]
  rw [Finset.sum_eq_single p]
  · calc ∑ j : Fin N, ‖basePart e (p, i) (p, j)‖ ≤ ∑ j : Fin N, c * c := by
          refine Finset.sum_le_sum fun j _ => ?_
          rw [basePart_apply]
          simp only [ite_true, norm_mul]
          exact mul_le_mul (he p i) (he p j) (norm_nonneg _) hc
      _ = N * c ^ 2 := by simp [sq]
  · intro q _ hq
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [basePart_apply]
    simp [Ne.symm hq]
  · simp

/-- Row sums of `1 - P_e`. -/
theorem rowSum_one_sub_basePart_le (e : ι → Fin N → ℂ) {c : ℝ} (hc : 0 ≤ c)
    (he : ∀ p i, ‖e p i‖ ≤ c) (y : ι × Fin N) :
    ∑ z, ‖(1 - basePart e) y z‖ ≤ 1 + N * c ^ 2 := by
  calc ∑ z, ‖(1 - basePart e) y z‖ ≤ ∑ z, (‖(1 : Matrix (ι × Fin N) (ι × Fin N) ℂ) y z‖ +
        ‖basePart e y z‖) := Finset.sum_le_sum fun z _ => by
          rw [Matrix.sub_apply]; exact norm_sub_le _ _
    _ = 1 + ∑ z, ‖basePart e y z‖ := by rw [Finset.sum_add_distrib, rowSum_one]
    _ ≤ _ := by linarith [rowSum_basePart_le e hc he y]

/-- Row sums of `1 - A_e`. -/
theorem rowSum_one_sub_baseOp_le (e : ι → Fin N → ℂ) {c : ℝ} (hc : 0 ≤ c)
    (he : ∀ p i, ‖e p i‖ ≤ c) {H : Matrix ι ι ℂ} {h : ℝ} (hh : 0 ≤ h)
    (hH : ∀ y, ∑ z, ‖H y z‖ ≤ h) (y : ι × Fin N) :
    ∑ z, ‖(1 - baseOp N e H) y z‖ ≤ (1 + N * c ^ 2) + (1 + N * c ^ 2) ^ 2 * h := by
  have ha : 0 ≤ 1 + (N : ℝ) * c ^ 2 := by positivity
  have h1 := rowSum_one_sub_basePart_le e hc he
  have h2 : ∀ y, ∑ z, ‖(((1 - basePart e) * liftOp N H) * (1 - basePart e)) y z‖ ≤
      (1 + N * c ^ 2) * h * (1 + N * c ^ 2) := fun y =>
    rowSum_mul_le ha (fun y => rowSum_mul_le hh h1 (fun w => rowSum_liftOp hH _) y) h1 y
  have h3 := rowSum_basePart_le e hc he y
  calc ∑ z, ‖(1 - baseOp N e H) y z‖ ≤ ∑ z, (‖(1 : Matrix (ι × Fin N) (ι × Fin N) ℂ) y z‖ +
        ‖(((1 - basePart e) * liftOp N H) * (1 - basePart e)) y z‖ + ‖basePart e y z‖) := by
        refine Finset.sum_le_sum fun z _ => ?_
        unfold baseOp
        rw [Matrix.sub_apply, Matrix.add_apply]
        have e1 : (1 : Matrix (ι × Fin N) (ι × Fin N) ℂ) y z -
            (((1 - basePart e) * liftOp N H * (1 - basePart e)) y z + basePart e y z) =
            (1 : Matrix (ι × Fin N) (ι × Fin N) ℂ) y z -
              ((1 - basePart e) * liftOp N H * (1 - basePart e)) y z - basePart e y z := by ring
        rw [e1]
        exact (norm_sub_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
    _ = 1 + ∑ z, ‖(((1 - basePart e) * liftOp N H) * (1 - basePart e)) y z‖ +
          ∑ z, ‖basePart e y z‖ := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib, rowSum_one]
    _ ≤ _ := by nlinarith [h2 y]

end RowSums

section Generic

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The resolvent of `A` commutes with `1 - A`. -/
theorem resolvent_mul_one_sub_comm {A : Matrix ι ι ℂ} {x : ℝ}
    (hu : IsUnit ((x : ℂ) • (1 : Matrix ι ι ℂ) + A)) :
    ((x : ℂ) • (1 : Matrix ι ι ℂ) + A)⁻¹ * (1 - A) =
      (1 - A) * ((x : ℂ) • (1 : Matrix ι ι ℂ) + A)⁻¹ := by
  set X := (x : ℂ) • (1 : Matrix ι ι ℂ) + A with hX
  have hXR : X * X⁻¹ = 1 := Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hu)
  have hRX : X⁻¹ * X = 1 := Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 hu)
  have h1 : A * X⁻¹ = 1 - (x : ℂ) • X⁻¹ := by
    have : A = X - (x : ℂ) • 1 := by rw [hX]; abel
    rw [this, Matrix.sub_mul, hXR, Matrix.smul_mul, Matrix.one_mul]
  have h2 : X⁻¹ * A = 1 - (x : ℂ) • X⁻¹ := by
    have : A = X - (x : ℂ) • 1 := by rw [hX]; abel
    rw [this, Matrix.mul_sub, hRX, Matrix.mul_smul, Matrix.mul_one]
  rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul, h1, h2]

/-- **Pointwise decay of the logarithm integrand.**  If the resolvent entries are at most
`B / (1 + x)` and the row sums of `1 - A` are at most `M`, the entries of
`(A + x)⁻¹ - (1 + x)⁻¹` are at most `B M (1 + x)⁻²`. -/
theorem resolvent_sub_scalar_entry_le {A : Matrix ι ι ℂ} {B M x : ℝ} (hB : 0 ≤ B) (hx : 0 ≤ x)
    (hu : IsUnit ((x : ℂ) • (1 : Matrix ι ι ℂ) + A))
    (hR : ∀ y z, ‖((x : ℂ) • (1 : Matrix ι ι ℂ) + A)⁻¹ y z‖ ≤ B / (1 + x))
    (hrow : ∀ y, ∑ w, ‖(1 - A) y w‖ ≤ M) (y z : ι) :
    ‖(((x : ℂ) • (1 : Matrix ι ι ℂ) + A)⁻¹ - (((1 + x)⁻¹ : ℝ) : ℂ) • (1 : Matrix ι ι ℂ)) y z‖ ≤
      B * M * ((1 + x)⁻¹) ^ 2 := by
  have h1x : 0 < 1 + x := by linarith
  rw [resolvent_sub_scalar hx hu, resolvent_mul_one_sub_comm hu, Matrix.smul_apply, smul_eq_mul,
    norm_mul, Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.2 h1x.le)]
  have := entry_mul_le (X := 1 - A) (Y := ((x : ℂ) • (1 : Matrix ι ι ℂ) + A)⁻¹)
    (div_nonneg hB h1x.le) hrow hR y z
  calc (1 + x)⁻¹ * ‖((1 - A) * ((x : ℂ) • (1 : Matrix ι ι ℂ) + A)⁻¹) y z‖
      ≤ (1 + x)⁻¹ * (M * (B / (1 + x))) := mul_le_mul_of_nonneg_left this (inv_nonneg.2 h1x.le)
    _ = B * M * ((1 + x)⁻¹) ^ 2 := by field_simp

/-- **Integrability and the bound of the logarithm.**  Under the hypotheses of
`resolvent_sub_scalar_entry_le` for all `x ≥ 0`, every entry of the logarithm integrand is
integrable on `(0, ∞)` and every entry of `logMat A` is at most `B M`. -/
theorem logMat_entry_integrable_bound {A : Matrix ι ι ℂ} (hA : ResOK A) {B M : ℝ} (hB : 0 ≤ B)
    (hR : ∀ x : ℝ, 0 ≤ x → ∀ y z, ‖((x : ℂ) • (1 : Matrix ι ι ℂ) + A)⁻¹ y z‖ ≤ B / (1 + x))
    (hrow : ∀ y, ∑ w, ‖(1 - A) y w‖ ≤ M) (y z : ι) :
    IntegrableOn (fun x : ℝ =>
      (((x : ℂ) • (1 : Matrix ι ι ℂ) + A)⁻¹ - (((1 + x)⁻¹ : ℝ) : ℂ) • (1 : Matrix ι ι ℂ)) y z)
      (Ioi 0) ∧ ‖logMat A y z‖ ≤ B * M := by
  have hbd : ∀ x ∈ Ioi (0 : ℝ),
      ‖(((x : ℂ) • (1 : Matrix ι ι ℂ) + A)⁻¹ - (((1 + x)⁻¹ : ℝ) : ℂ) • (1 : Matrix ι ι ℂ)) y z‖ ≤
        B * M * ((1 + x)⁻¹) ^ 2 := fun x hx =>
    resolvent_sub_scalar_entry_le hB (mem_Ioi.mp hx).le (hA x (mem_Ioi.mp hx).le)
      (hR x (mem_Ioi.mp hx).le) hrow y z
  have hgi : IntegrableOn (fun x : ℝ => B * M * ((1 + x)⁻¹) ^ 2) (Ioi 0) :=
    (integrableOn_inv_add_sq (a := 1) one_pos).const_mul _
  have hint : IntegrableOn (fun x : ℝ =>
      (((x : ℂ) • (1 : Matrix ι ι ℂ) + A)⁻¹ - (((1 + x)⁻¹ : ℝ) : ℂ) • (1 : Matrix ι ι ℂ)) y z)
      (Ioi 0) := by
    refine Integrable.mono' hgi ?_ ((ae_restrict_iff' measurableSet_Ioi).2
      (Filter.Eventually.of_forall hbd))
    refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
    simp only [Matrix.sub_apply]
    refine (continuousOn_resolvent_entry (fun x hx => hA x hx.le) y z).sub ?_
    simp only [Matrix.smul_apply]
    exact (Complex.continuous_ofReal.comp_continuousOn
      (continuousOn_inv_add_Ioi (ak := 1) one_pos)).mul continuousOn_const
  refine ⟨hint, ?_⟩
  have hn := norm_integral_le_of_norm_le (μ := volume.restrict (Ioi (0 : ℝ))) hgi
    ((ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall hbd))
  have hval : ∫ x in Ioi (0 : ℝ), B * M * ((1 + x)⁻¹) ^ 2 = B * M := by
    rw [integral_const_mul, integral_inv_add_sq one_pos]
    simp
  rw [hval] at hn
  have e : logMat A y z = -∫ x in Ioi (0 : ℝ),
      (((x : ℂ) • (1 : Matrix ι ι ℂ) + A)⁻¹ - (((1 + x)⁻¹ : ℝ) : ℂ) • (1 : Matrix ι ι ℂ)) y z := rfl
  rw [e, norm_neg]
  exact hn

end Generic

section Physical

open scoped Matrix

/-- **The logarithm of the first step's operator as an integral of the shifted resolvent.**
At the physical point (`s ≡ 1`, `φ₀ · φ₀ = 1`) the covariance
`(1 + x)⁻¹ P_e + Ĝ_{0,1} - Π_{0,1}` of the x-variant chain at mass `ν + x` is `(A_e + x)⁻¹`
(`baseCovX_one`).  With `B` depending only on `d, L, N`:
* the entries of `C_x - (1 + x)⁻¹` are at most `B (1 + ν) (1 + x)⁻²`, so they are integrable on
  `(0, ∞)` and the entries of the integral are at most `B (1 + ν)`;
* `-∫₀^∞ (C_x - (1 + x)⁻¹) dx = logMat A_e`, and this is the principal logarithm of `A_e`:
  `exp` of it is `A_e`, it commutes with `A_e`, and its eigenvalues have imaginary part in
  `(-π, π)`.

The dependence on the mass is only through the row sums `ν + 12 d + 3` of `H`. -/
theorem baseCovX_log (d L N : ℕ) [NeZero L] :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ {N₁ m₁ : ℕ} [NeZero N₁] {ϱ : ℝ} {G : GeneratingSet d L (N₁ * L ^ m₁) 1 ϱ}
      [Nonempty (G.Ω 1 × Fin N)] {a : ℕ → ℝ} {aT ν Cx : ℝ}
      (_S : Dec2.XCover (coverOf G) G a aT ν Cx) (_hCx : 0 ≤ Cx)
      (_ha0 : a 0 = 2) (_ha1 : 0 ≤ a 1) (_ha1' : a 1 ≤ 2)
      (_haT : aT = 2 * a 1 * (L : ℝ) ^ 2 / (2 * (L : ℝ) ^ 2 - a 1))
      {α : G.Ω 1 → ℂ} (_hα : AdmPot G α) (_hM : Dec2.cstarX d L Cx ≤ (L : ℝ) ^ m₁)
      {δ : ℝ} (_hδ : 0 ≤ δ) (_hsm : δ ^ 2 * smallConstX d L 0 ≤ 1 / 4)
      {φ : Balaban.Localization.CTorus d L N₁ m₁ 1 → Fin N → ℂ}
      (_hφ : IsConstraintField G δ φ) (_hsq : ∀ z : G.Ω 1, ∑ i, φ z i * φ z i = 1),
      (∀ x : ℝ, 0 ≤ x → ∀ y z : G.Ω 1 × Fin N,
        ‖((1 + (x : ℂ))⁻¹ • basePart (restrictField G φ) +
            liftOp N (Dec2.Gsx (coverOf G) G a aT 0 (ν + x) α (fun _ => 1)) -
            Dec2.decPi (coverOf G) G a aT 0 (ν + x) α (fun _ => 1) φ -
            (((1 + x)⁻¹ : ℝ) : ℂ) • (1 : Matrix (G.Ω 1 × Fin N) (G.Ω 1 × Fin N) ℂ)) y z‖ ≤
          B * (1 + ν) * ((1 + x)⁻¹) ^ 2) ∧
      (∀ y z : G.Ω 1 × Fin N, IntegrableOn (fun x : ℝ =>
        ((1 + (x : ℂ))⁻¹ • basePart (restrictField G φ) +
            liftOp N (Dec2.Gsx (coverOf G) G a aT 0 (ν + x) α (fun _ => 1)) -
            Dec2.decPi (coverOf G) G a aT 0 (ν + x) α (fun _ => 1) φ -
            (((1 + x)⁻¹ : ℝ) : ℂ) • (1 : Matrix (G.Ω 1 × Fin N) (G.Ω 1 × Fin N) ℂ)) y z)
        (Ioi 0)) ∧
      (∀ y z : G.Ω 1 × Fin N, ‖∫ x in Ioi (0 : ℝ),
        ((1 + (x : ℂ))⁻¹ • basePart (restrictField G φ) +
            liftOp N (Dec2.Gsx (coverOf G) G a aT 0 (ν + x) α (fun _ => 1)) -
            Dec2.decPi (coverOf G) G a aT 0 (ν + x) α (fun _ => 1) φ -
            (((1 + x)⁻¹ : ℝ) : ℂ) • (1 : Matrix (G.Ω 1 × Fin N) (G.Ω 1 × Fin N) ℂ)) y z‖ ≤
          B * (1 + ν)) ∧
      (∀ y z : G.Ω 1 × Fin N, -∫ x in Ioi (0 : ℝ),
        ((1 + (x : ℂ))⁻¹ • basePart (restrictField G φ) +
            liftOp N (Dec2.Gsx (coverOf G) G a aT 0 (ν + x) α (fun _ => 1)) -
            Dec2.decPi (coverOf G) G a aT 0 (ν + x) α (fun _ => 1) φ -
            (((1 + x)⁻¹ : ℝ) : ℂ) • (1 : Matrix (G.Ω 1 × Fin N) (G.Ω 1 × Fin N) ℂ)) y z =
        Localization.logMat (baseOp N (restrictField G φ)
          (baseHamiltonian G a ν α (fun _ => 1))) y z) ∧
      (NormedSpace.exp (Localization.logMat (baseOp N (restrictField G φ)
          (baseHamiltonian G a ν α (fun _ => 1)))) =
        baseOp N (restrictField G φ) (baseHamiltonian G a ν α (fun _ => 1)) ∧
      Localization.logMat (baseOp N (restrictField G φ) (baseHamiltonian G a ν α (fun _ => 1))) *
          baseOp N (restrictField G φ) (baseHamiltonian G a ν α (fun _ => 1)) =
        baseOp N (restrictField G φ) (baseHamiltonian G a ν α (fun _ => 1)) *
          Localization.logMat (baseOp N (restrictField G φ)
            (baseHamiltonian G a ν α (fun _ => 1))) ∧
      ∀ (μ : ℂ) (v : G.Ω 1 × Fin N → ℂ), v ≠ 0 →
        Localization.logMat (baseOp N (restrictField G φ)
          (baseHamiltonian G a ν α (fun _ => 1))) *ᵥ v = μ • v → |μ.im| < Real.pi) := by
  obtain ⟨B0, hB00, hdec⟩ := baseCovX_decay d L 0
  set a1 : ℝ := 1 + N * (3 / 2 : ℝ) ^ 2 with ha1def
  have ha1p : 0 ≤ a1 := by rw [ha1def]; positivity
  set K : ℝ := a1 + a1 ^ 2 * (12 * d + 3) + a1 ^ 2 with hK
  have hK0 : 0 ≤ K := by rw [hK]; positivity
  refine ⟨B0 * K, by positivity, ?_⟩
  intro N₁ m₁ _ ϱ G _ a aT ν Cx S hCx ha0 ha1 ha1' haT α hα hM δ hδ hsm φ hφ hsq
  have hν : 0 ≤ ν := S.mass
  have hL0 : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hsp : ∀ z : G.Ω 1, G.spacing (z : Balaban.Localization.CTorus d L N₁ m₁ 1) = (L : ℝ) :=
    fun z => by
      obtain ⟨h1, h2, _⟩ := G.layerIndex_spec z.2
      have : G.layerIndex (z : Balaban.Localization.CTorus d L N₁ m₁ 1) = 1 := le_antisymm h2 h1
      rw [GeneratingSet.spacing, this, pow_one]
  have hα' : ∀ z, ‖α z‖ ≤ 1 / (8 * (L : ℝ) ^ 2) := fun z => by
    refine (Dec2.AdmPot.le_eighth' S.hd hα z).trans (le_of_eq ?_)
    rw [hsp z]
    field_simp
  set A := baseOp N (restrictField G φ) (baseHamiltonian G a ν α (fun _ => 1)) with hAdef
  have hone := fun x (hx : 0 ≤ x) => baseCovX_one (xCover_add_mass S hx) hCx hx ha0 ha1 ha1' haT
    hα hM hδ hsm hφ hsq
  have hres : ResOK A := by
    intro x hx
    have h := (hone x hx).2
    rw [add_comm] at h
    exact (Matrix.isUnit_iff_isUnit_det _).2 (Matrix.isUnit_det_of_right_inverse h)
  have hCd : ∀ x : ℝ, 0 ≤ x → ((x : ℂ) • (1 : Matrix (G.Ω 1 × Fin N) (G.Ω 1 × Fin N) ℂ) + A)⁻¹ =
      (1 + (x : ℂ))⁻¹ • basePart (restrictField G φ) +
        liftOp N (Dec2.Gsx (coverOf G) G a aT 0 (ν + x) α (fun _ => 1)) -
        Dec2.decPi (coverOf G) G a aT 0 (ν + x) α (fun _ => 1) φ := fun x hx => by
    rw [← (hone x hx).1, baseResolvent, add_comm]
  -- the resolvent decay
  have hR : ∀ x : ℝ, 0 ≤ x → ∀ y z, ‖((x : ℂ) • (1 : Matrix (G.Ω 1 × Fin N) (G.Ω 1 × Fin N) ℂ) +
      A)⁻¹ y z‖ ≤ B0 / (1 + x) := fun x hx y z => by
    rw [hCd x hx]
    exact hdec (xCover_add_mass S hx) hCx hν hx le_rfl (by simpa using hM) hδ hsm hα
      (fun P => by simp) hφ y z
  -- the row sums of `1 - A`
  have hη : (0 : ℝ) ≤ baseCoercivity L / (8 * d) :=
    div_nonneg (baseCoercivity_pos (Nat.pos_of_ne_zero (NeZero.ne L))).le (by positivity)
  have hs1 : (fun _ => (1 : ℂ)) ∈ baseParamNbhd G 0 :=
    fun _ _ => ⟨1, zero_le_one, le_rfl, by simp⟩
  have hH : ∀ y : G.Ω 1, ∑ z : G.Ω 1, ‖baseHamiltonian G a ν α (fun _ => 1) y z‖ ≤
      ν + 12 * d + 3 := fun y =>
    baseHamiltonian_row_le G hν (S.weights) hα' (η := 0) hη hs1 y
  have he : ∀ (p : G.Ω 1) (i : Fin N), ‖restrictField G φ p i‖ ≤ 3 / 2 := fun p i =>
    (norm_le_vn (φ p) i).trans (hφ.bound p p.2)
  have hrow0 := fun y => rowSum_one_sub_baseOp_le (restrictField G φ) (c := 3 / 2) (by norm_num) he
    (H := baseHamiltonian G a ν α (fun _ => 1)) (h := ν + 12 * d + 3) (by positivity) hH y
  have hrow : ∀ y, ∑ w, ‖(1 - A) y w‖ ≤ K * (1 + ν) := fun y => by
    refine (hrow0 y).trans ?_
    rw [hK, ← ha1def]
    nlinarith [sq_nonneg a1, mul_nonneg (sq_nonneg a1) hν]
  have hgen := fun y z => logMat_entry_integrable_bound hres hB00 hR hrow y z
  have hEq : ∀ y z : G.Ω 1 × Fin N, ∫ x in Ioi (0 : ℝ),
      ((1 + (x : ℂ))⁻¹ • basePart (restrictField G φ) +
          liftOp N (Dec2.Gsx (coverOf G) G a aT 0 (ν + x) α (fun _ => 1)) -
          Dec2.decPi (coverOf G) G a aT 0 (ν + x) α (fun _ => 1) φ -
          (((1 + x)⁻¹ : ℝ) : ℂ) • (1 : Matrix (G.Ω 1 × Fin N) (G.Ω 1 × Fin N) ℂ)) y z =
      ∫ x in Ioi (0 : ℝ), (((x : ℂ) • (1 : Matrix (G.Ω 1 × Fin N) (G.Ω 1 × Fin N) ℂ) + A)⁻¹ -
          (((1 + x)⁻¹ : ℝ) : ℂ) • (1 : Matrix (G.Ω 1 × Fin N) (G.Ω 1 × Fin N) ℂ)) y z :=
    fun y z => setIntegral_congr_fun measurableSet_Ioi fun x hx => by
      rw [hCd x (mem_Ioi.mp hx).le]
  have hlog : ∀ y z : G.Ω 1 × Fin N, Localization.logMat A y z = -∫ x in Ioi (0 : ℝ),
      (((x : ℂ) • (1 : Matrix (G.Ω 1 × Fin N) (G.Ω 1 × Fin N) ℂ) + A)⁻¹ -
        (((1 + x)⁻¹ : ℝ) : ℂ) • (1 : Matrix (G.Ω 1 × Fin N) (G.Ω 1 × Fin N) ℂ)) y z :=
    fun y z => rfl
  refine ⟨fun x hx y z => ?_, fun y z => ?_, fun y z => ?_, fun y z => ?_, ?_⟩
  · rw [← hCd x hx]
    calc _ ≤ B0 * (K * (1 + ν)) * ((1 + x)⁻¹) ^ 2 :=
          resolvent_sub_scalar_entry_le hB00 hx (hres x hx) (hR x hx) hrow y z
      _ = _ := by ring
  · refine (hgen y z).1.congr_fun (fun x hx => ?_) measurableSet_Ioi
    simp only
    rw [hCd x (mem_Ioi.mp hx).le]
  · rw [hEq, ← norm_neg, ← hlog]
    calc _ ≤ B0 * (K * (1 + ν)) := (hgen y z).2
      _ = _ := by ring
  · rw [hEq, hlog]
  · exact Localization.logMat_principal hres

end Physical

end Balaban.LargeField.Base
