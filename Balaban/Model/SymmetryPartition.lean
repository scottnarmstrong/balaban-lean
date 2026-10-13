/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Model.Symmetry

/-!
# Rotation covariance of the partition function in the external field and the source

For a linear isometry `R` of `ℝ^N`, `Z(R h, g) = Z(h, Rᵀ g)`, where the rotated source is
`(Rᵀ g)_j(x) = ∑_i R_{ij} g_i(x)` (`rotSource`).  The rotated source satisfies the `ℓ¹` comparison
`‖Rᵀ g‖₁ ≤ √N ‖g‖₁`, and the factor `√N` cannot be removed (an explicit example for `N = 2`).
A family of terms `T` is transported to `x X g ↦ R (T x X (Rᵀ g))`; locality, analyticity, the
pairing identity and a sup-norm bound are proved clause by clause.
-/

@[expose] public section

namespace Balaban

open MeasureTheory

variable {d N ℓ : ℕ} [NeZero ℓ]

/-- The rotated source `(Rᵀ g)_i(x) = ∑_j R_{ji} g_j(x)`, with `R_{ji} = rotEntry R j i =
(R e_i)_j`. -/
noncomputable def rotSource (R : EuclideanSpace ℝ (Fin N) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin N))
    (g : Torus d ℓ → Fin N → ℂ) (x : Torus d ℓ) (i : Fin N) : ℂ :=
  ∑ j, (rotEntry R j i : ℂ) * g x j

/-- The complex-linear extension of `R` to `ℂ^N`: `(R v)_i = ∑_j R_{ij} v_j`. -/
noncomputable def rotVec (R : EuclideanSpace ℝ (Fin N) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin N))
    (v : Fin N → ℂ) (i : Fin N) : ℂ :=
  ∑ j, (rotEntry R i j : ℂ) * v j

/-- The family `T` transported by `R`: `T' x X g = R (T x X (Rᵀ g))`. -/
noncomputable def rotFamily (R : EuclideanSpace ℝ (Fin N) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin N))
    (T : Torus d ℓ → Finset (Torus d ℓ) → (Torus d ℓ → Fin N → ℂ) → (Fin N → ℂ))
    (x : Torus d ℓ) (X : Finset (Torus d ℓ)) (g : Torus d ℓ → Fin N → ℂ) : Fin N → ℂ :=
  rotVec R (T x X (rotSource R g))

/-! ### T1: the partition function -/

theorem sum_rot_source_mul (R : EuclideanSpace ℝ (Fin N) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin N))
    (g : Torus d ℓ → Fin N → ℂ) (ψ : Torus d ℓ → SpinSphere N) :
    ∑ x : Torus d ℓ, ∑ i : Fin N,
        g x i * ((((rotConfig d N ℓ R ψ) x : EuclideanSpace ℝ (Fin N)) i : ℝ) : ℂ) =
      ∑ x : Torus d ℓ, ∑ i : Fin N,
        rotSource R g x i * (((ψ x : EuclideanSpace ℝ (Fin N)) i : ℝ) : ℂ) := by
  refine Finset.sum_congr rfl fun x _ => ?_
  simp only [rotConfig_apply, rot_apply_coord R, rotSource, Complex.ofReal_sum,
    Complex.ofReal_mul, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/-- **Rotation covariance of the partition function:** `Z(R h, g) = Z(h, Rᵀ g)`. -/
theorem partitionFunction_rot (R : EuclideanSpace ℝ (Fin N) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin N))
    (β ν : ℝ) (h : EuclideanSpace ℝ (Fin N)) (g : Torus d ℓ → Fin N → ℂ) :
    partitionFunction d N ℓ β ν (R h) g = partitionFunction d N ℓ β ν h (rotSource R g) := by
  unfold partitionFunction
  have key := (measurePreserving_rotConfig d N ℓ R).integral_comp'
    (f := rotConfig d N ℓ R) (g := fun φ : Torus d ℓ → SpinSphere N =>
      Complex.exp (-((β * energy d N ℓ ν (R h) φ : ℝ) : ℂ)
        + ∑ x : Torus d ℓ, ∑ i : Fin N,
          g x i * (((φ x : EuclideanSpace ℝ (Fin N)) i : ℝ) : ℂ)))
  rw [← key]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ψ => ?_)
  dsimp only
  rw [energy_rotConfig, sum_rot_source_mul]

/-! ### T2: the `ℓ¹` comparison -/

theorem rotEntry_eq_symm (R : EuclideanSpace ℝ (Fin N) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin N))
    (i j : Fin N) :
    rotEntry R i j = (R.symm (EuclideanSpace.single i 1) : EuclideanSpace ℝ (Fin N)) j := by
  unfold rotEntry
  have h1 : inner ℝ (EuclideanSpace.single i (1 : ℝ)) (R (EuclideanSpace.single j 1)) =
      inner ℝ (R.symm (EuclideanSpace.single i (1 : ℝ))) (EuclideanSpace.single j 1) := by
    rw [← R.symm.inner_map_map, R.symm_apply_apply]
  simp only [EuclideanSpace.inner_single_left, EuclideanSpace.inner_single_right] at h1
  simpa using h1

theorem sum_sq_rotEntry_row (R : EuclideanSpace ℝ (Fin N) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin N))
    (i : Fin N) : ∑ j, rotEntry R i j ^ 2 = 1 := by
  have h := EuclideanSpace.norm_sq_eq (R.symm (EuclideanSpace.single i (1 : ℝ)))
  rw [LinearIsometryEquiv.norm_map] at h
  simp only [rotEntry_eq_symm]
  simpa [Real.norm_eq_abs, sq_abs] using h.symm

theorem sum_abs_rotEntry_row_le (R : EuclideanSpace ℝ (Fin N) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin N))
    (i : Fin N) : ∑ j, |rotEntry R i j| ≤ Real.sqrt N := by
  apply Real.le_sqrt_of_sq_le
  have := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin N))
    (fun j => |rotEntry R i j|) (fun _ => (1 : ℝ))
  simpa [sq_abs, sum_sq_rotEntry_row R i] using this

/-- **The source ball:** `∑_y ∑_i ‖(Rᵀ g)_i(y)‖ ≤ √N ∑_y ∑_i ‖g_i(y)‖`. -/
theorem sum_norm_rotSource_le (R : EuclideanSpace ℝ (Fin N) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin N))
    (g : Torus d ℓ → Fin N → ℂ) :
    ∑ y, ∑ i, ‖rotSource R g y i‖ ≤ Real.sqrt N * ∑ y, ∑ i, ‖g y i‖ := by
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun y _ => ?_
  calc ∑ i, ‖rotSource R g y i‖
      ≤ ∑ i, ∑ j, |rotEntry R j i| * ‖g y j‖ := by
        refine Finset.sum_le_sum fun i _ => (norm_sum_le _ _).trans ?_
        simp
    _ = ∑ j, (∑ i, |rotEntry R j i|) * ‖g y j‖ := by
        rw [Finset.sum_comm]
        simp [Finset.sum_mul]
    _ ≤ ∑ j, Real.sqrt N * ‖g y j‖ :=
        Finset.sum_le_sum fun j _ =>
          mul_le_mul_of_nonneg_right (sum_abs_rotEntry_row_le R j) (norm_nonneg _)
    _ = Real.sqrt N * ∑ j, ‖g y j‖ := by rw [Finset.mul_sum]

/-- The quarter-turn-composed-with-scaling isometry of `ℝ²`: `(a, b) ↦ ((a - b)/√2, (a + b)/√2)`
(rotation by `π/4`). -/
noncomputable def eighthTurn : EuclideanSpace ℝ (Fin 2) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2) where
  toFun v := !₂[(v 0 - v 1) / Real.sqrt 2, (v 0 + v 1) / Real.sqrt 2]
  invFun v := !₂[(v 0 + v 1) / Real.sqrt 2, (v 1 - v 0) / Real.sqrt 2]
  map_add' v w := by
    ext i; fin_cases i <;> simp <;> ring
  map_smul' c v := by
    ext i; fin_cases i <;> simp <;> ring
  left_inv v := by
    have h2 : (0 : ℝ) < Real.sqrt 2 := by positivity
    have h3' : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    ext i; fin_cases i <;> simp <;> field_simp <;> rw [h3'] <;> ring
  right_inv v := by
    have h2 : (0 : ℝ) < Real.sqrt 2 := by positivity
    have h3' : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    ext i; fin_cases i <;> simp <;> field_simp <;> rw [h3'] <;> ring
  norm_map' v := by
    have h2 : (0 : ℝ) < Real.sqrt 2 := by positivity
    have h3 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
    congr 1
    simp only [Fin.sum_univ_two]
    simp only [Real.norm_eq_abs, sq_abs]
    simp [div_pow, h3]
    ring

/-- **The factor `√N` is needed** (`N = 2`): for the rotation `eighthTurn` and the source
`g = δ_{(x₀, 0)}` of `ℓ¹`-norm `1`, the rotated source has `ℓ¹`-norm `√2`. -/
theorem sum_norm_rotSource_example (x₀ : Torus d ℓ) :
    ∃ g : Torus d ℓ → Fin 2 → ℂ, ∑ y, ∑ i, ‖g y i‖ = 1 ∧
      ∑ y, ∑ i, ‖rotSource eighthTurn g y i‖ = Real.sqrt 2 := by
  classical
  refine ⟨fun y i => if y = x₀ ∧ i = 0 then 1 else 0, ?_, ?_⟩
  · rw [Finset.sum_eq_single x₀ (fun y _ hy => by simp [hy]) (by simp)]
    simp [Fin.sum_univ_two]
  · have e0 : rotEntry eighthTurn 0 0 = 1 / Real.sqrt 2 := by simp [rotEntry, eighthTurn]
    have e1 : rotEntry eighthTurn 0 1 = -(1 / Real.sqrt 2) := by simp [rotEntry, eighthTurn, neg_div]
    have h2 : (0 : ℝ) < Real.sqrt 2 := by positivity
    have h3 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
    have hs : ∀ y i, rotSource eighthTurn (fun y i => if y = x₀ ∧ i = 0 then (1 : ℂ) else 0) y i =
        if y = x₀ then (rotEntry eighthTurn 0 i : ℂ) else 0 := by
      intro y i
      unfold rotSource
      by_cases hy : y = x₀
      · subst hy
        rw [Fin.sum_univ_two]
        fin_cases i <;> simp [rotEntry, eighthTurn]
      · simp [hy]
    simp only [hs]
    rw [Finset.sum_eq_single x₀ (fun y _ hy => by simp [hy]) (by simp)]
    simp only [ite_true, Fin.sum_univ_two, e0, e1, Complex.norm_real, Real.norm_eq_abs, abs_neg,
      abs_of_pos (one_div_pos.2 h2)]
    field_simp
    nlinarith

/-! ### T3: transport of the terms -/

section Transport

variable (R : EuclideanSpace ℝ (Fin N) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin N))
  (T : Torus d ℓ → Finset (Torus d ℓ) → (Torus d ℓ → Fin N → ℂ) → (Fin N → ℂ))

omit [NeZero ℓ] in
/-- Locality is preserved. -/
theorem rotFamily_local (x : Torus d ℓ) (X : Finset (Torus d ℓ))
    (hT : ∀ g g' : Torus d ℓ → Fin N → ℂ, (∀ y ∈ X, g y = g' y) → T x X g = T x X g')
    (g g' : Torus d ℓ → Fin N → ℂ) (hg : ∀ y ∈ X, g y = g' y) :
    rotFamily R T x X g = rotFamily R T x X g' := by
  unfold rotFamily
  congr 1
  refine hT _ _ fun y hy => ?_
  funext i
  simp only [rotSource, hg y hy]

/-- `Rᵀ` as a continuous linear map on sources. -/
noncomputable def rotSourceCLM :
    (Torus d ℓ → Fin N → ℂ) →L[ℂ] (Torus d ℓ → Fin N → ℂ) :=
  LinearMap.toContinuousLinearMap
    { toFun := rotSource R
      map_add' := fun g g' => by
        funext x i; simp [rotSource, mul_add, Finset.sum_add_distrib]
      map_smul' := fun c g => by
        funext x i; simp [rotSource, Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring }

/-- `R` on `ℂ^N` as a continuous linear map. -/
noncomputable def rotVecCLM : (Fin N → ℂ) →L[ℂ] (Fin N → ℂ) :=
  LinearMap.toContinuousLinearMap
    { toFun := rotVec R
      map_add' := fun v w => by
        funext i; simp [rotVec, mul_add, Finset.sum_add_distrib]
      map_smul' := fun c v => by
        funext i; simp [rotVec, Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring }

/-- Analyticity on the ball of radius `√N ρ` gives analyticity of the transported term on the
ball of radius `ρ`. -/
theorem rotFamily_analytic (hN : 0 < N) (x : Torus d ℓ) (X : Finset (Torus d ℓ)) (ρ : ℝ)
    (hT : AnalyticOnNhd ℂ (T x X) {g | ∑ y, ∑ i, ‖g y i‖ < Real.sqrt N * ρ}) :
    AnalyticOnNhd ℂ (rotFamily R T x X) {g | ∑ y, ∑ i, ‖g y i‖ < ρ} := by
  have hmap : Set.MapsTo (rotSourceCLM R) {g : Torus d ℓ → Fin N → ℂ | ∑ y, ∑ i, ‖g y i‖ < ρ}
      {g | ∑ y, ∑ i, ‖g y i‖ < Real.sqrt N * ρ} := by
    intro g hg
    show ∑ y, ∑ i, ‖rotSource R g y i‖ < _
    calc _ ≤ _ := sum_norm_rotSource_le R g
      _ < _ := mul_lt_mul_of_pos_left hg (Real.sqrt_pos.2 (by exact_mod_cast hN))
  have h1 : AnalyticOnNhd ℂ (fun g => T x X (rotSourceCLM R g))
      {g | ∑ y, ∑ i, ‖g y i‖ < ρ} :=
    hT.comp (fun g _ => (rotSourceCLM R).analyticAt g) hmap
  have h2 : AnalyticOnNhd ℂ (fun g => rotVecCLM R (T x X (rotSourceCLM R g)))
      {g | ∑ y, ∑ i, ‖g y i‖ < ρ} :=
    AnalyticOnNhd.comp (g := rotVecCLM R) (t := Set.univ)
      (fun v _ => (rotVecCLM R).analyticAt v) h1 (fun _ _ => Set.mem_univ _)
  exact h2

omit [NeZero ℓ] in
/-- The pairing identity. -/
theorem rotFamily_pairing (x : Torus d ℓ) (X : Finset (Torus d ℓ))
    (g : Torus d ℓ → Fin N → ℂ) :
    ∑ i, g x i * rotFamily R T x X g i =
      ∑ i, rotSource R g x i * T x X (rotSource R g) i := by
  unfold rotFamily rotVec rotSource
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

omit [NeZero ℓ] in
/-- The sup-norm bound with constant `c_N = √N`. -/
theorem norm_rotFamily_le (x : Torus d ℓ) (X : Finset (Torus d ℓ))
    (g : Torus d ℓ → Fin N → ℂ) :
    ‖rotFamily R T x X g‖ ≤ Real.sqrt N * ‖T x X (rotSource R g)‖ := by
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
  unfold rotFamily rotVec
  calc ‖∑ j, (rotEntry R i j : ℂ) * T x X (rotSource R g) j‖
      ≤ ∑ j, |rotEntry R i j| * ‖T x X (rotSource R g)‖ := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
        rw [norm_mul]
        simp only [Complex.norm_real, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left (norm_le_pi_norm _ j) (abs_nonneg _)
    _ = (∑ j, |rotEntry R i j|) * ‖T x X (rotSource R g)‖ := by rw [Finset.sum_mul]
    _ ≤ Real.sqrt N * ‖T x X (rotSource R g)‖ :=
        mul_le_mul_of_nonneg_right (sum_abs_rotEntry_row_le R i) (norm_nonneg _)

end Transport

end Balaban
