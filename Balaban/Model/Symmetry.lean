/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Model.SphereMeasure
public import Balaban.Frozen.Model.TwoPointTruncated
public import Balaban.Frozen.Model.PartitionFunction

/-!
# Symmetries of the hard-spin model (Lemma 0.2, parts (a) and (b))

The energy and the Gibbs weight are invariant under simultaneous rotation of the spins and of
the field direction (`energy_rotConfig`) and under translations of the torus
(`energy_shiftConfig`).  Consequently the one-point and truncated two-point functions are
translation invariant and transform as a vector and as a two-tensor under `O(N)`.
-/

@[expose] public section

namespace Balaban

open MeasureTheory

variable {d N ℓ : ℕ} [NeZero ℓ]

/-! ### Continuity and integrability -/

omit [NeZero ℓ] in
theorem continuous_spin_coord (x : Torus d ℓ) (i : Fin N) :
    Continuous fun φ : Torus d ℓ → SpinSphere N => (φ x : EuclideanSpace ℝ (Fin N)) i :=
  (EuclideanSpace.proj i).continuous.comp (continuous_subtype_val.comp (continuous_apply x))

theorem continuous_energy (ν : ℝ) (h : EuclideanSpace ℝ (Fin N)) :
    Continuous (energy d N ℓ ν h) := by
  unfold energy
  have hc : ∀ x : Torus d ℓ, Continuous fun φ : Torus d ℓ → SpinSphere N =>
      (φ x : EuclideanSpace ℝ (Fin N)) :=
    fun x => continuous_subtype_val.comp (continuous_apply x)
  fun_prop

/-- Continuous functions on the (compact) configuration space are integrable for the a priori
measure. -/
theorem integrable_of_continuous {E : Type*} [NormedAddCommGroup E]
    {F : (Torus d ℓ → SpinSphere N) → E} (hF : Continuous F) :
    Integrable F (aprioriMeasure d N ℓ) :=
  hF.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace F)

/-! ### Invariance of the energy -/

theorem energy_rotConfig (R : EuclideanSpace ℝ (Fin N) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin N))
    (ν : ℝ) (h : EuclideanSpace ℝ (Fin N)) (φ : Torus d ℓ → SpinSphere N) :
    energy d N ℓ ν (R h) (rotConfig d N ℓ R φ) = energy d N ℓ ν h φ := by
  unfold energy
  simp only [rotConfig_apply, ← map_sub, LinearIsometryEquiv.norm_map]

theorem energy_shiftConfig (a : Torus d ℓ) (ν : ℝ) (h : EuclideanSpace ℝ (Fin N))
    (φ : Torus d ℓ → SpinSphere N) :
    energy d N ℓ ν h (shiftConfig d N ℓ a φ) = energy d N ℓ ν h φ := by
  unfold energy
  simp only [shiftConfig_apply]
  congr 1
  · congr 1
    refine Fintype.sum_equiv (Equiv.addRight a) _ _ fun x => ?_
    refine Finset.sum_congr rfl fun μ _ => ?_
    simp [add_right_comm]
  · congr 1
    exact Fintype.sum_equiv (Equiv.addRight a) _ _ fun x => rfl

/-! ### Transformation of the Gibbs expectation -/

theorem gibbsExpectation_rotConfig (R : EuclideanSpace ℝ (Fin N) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin N))
    (β ν : ℝ) (h : EuclideanSpace ℝ (Fin N)) (F : (Torus d ℓ → SpinSphere N) → ℝ) :
    gibbsExpectation d N ℓ β ν (R h) F =
      gibbsExpectation d N ℓ β ν h fun φ => F (rotConfig d N ℓ R φ) := by
  unfold gibbsExpectation
  congr 1
  · rw [← (measurePreserving_rotConfig d N ℓ R).integral_comp' (f := rotConfig d N ℓ R)]
    simp only [energy_rotConfig]
  · rw [← (measurePreserving_rotConfig d N ℓ R).integral_comp' (f := rotConfig d N ℓ R)]
    simp only [energy_rotConfig]

theorem gibbsExpectation_shiftConfig (a : Torus d ℓ) (β ν : ℝ) (h : EuclideanSpace ℝ (Fin N))
    (F : (Torus d ℓ → SpinSphere N) → ℝ) :
    gibbsExpectation d N ℓ β ν h (fun φ => F (shiftConfig d N ℓ a φ)) =
      gibbsExpectation d N ℓ β ν h F := by
  unfold gibbsExpectation
  congr 1
  · rw [← (measurePreserving_shiftConfig d N ℓ a).integral_comp'
      (f := shiftConfig d N ℓ a)
      (g := fun φ => F φ * Real.exp (-(β * energy d N ℓ ν h φ)))]
    simp only [energy_shiftConfig]

/-! ### Linearity of the Gibbs expectation on continuous observables -/

theorem continuous_gibbs_integrand (β ν : ℝ) (h : EuclideanSpace ℝ (Fin N))
    {F : (Torus d ℓ → SpinSphere N) → ℝ} (hF : Continuous F) :
    Continuous fun φ => F φ * Real.exp (-(β * energy d N ℓ ν h φ)) := by
  have := continuous_energy (d := d) (N := N) (ℓ := ℓ) ν h
  fun_prop

theorem gibbsExpectation_add (β ν : ℝ) (h : EuclideanSpace ℝ (Fin N))
    {F G : (Torus d ℓ → SpinSphere N) → ℝ} (hF : Continuous F) (hG : Continuous G) :
    gibbsExpectation d N ℓ β ν h (fun φ => F φ + G φ) =
      gibbsExpectation d N ℓ β ν h F + gibbsExpectation d N ℓ β ν h G := by
  unfold gibbsExpectation
  rw [← add_div, ← integral_add (integrable_of_continuous (continuous_gibbs_integrand β ν h hF))
    (integrable_of_continuous (continuous_gibbs_integrand β ν h hG))]
  simp only [add_mul]

theorem gibbsExpectation_const_mul (β ν : ℝ) (h : EuclideanSpace ℝ (Fin N)) (c : ℝ)
    (F : (Torus d ℓ → SpinSphere N) → ℝ) :
    gibbsExpectation d N ℓ β ν h (fun φ => c * F φ) = c * gibbsExpectation d N ℓ β ν h F := by
  unfold gibbsExpectation
  rw [← mul_div_assoc, ← integral_const_mul]
  simp only [mul_assoc]

theorem gibbsExpectation_sum {ι : Type*} (s : Finset ι) (β ν : ℝ)
    (h : EuclideanSpace ℝ (Fin N)) {F : ι → (Torus d ℓ → SpinSphere N) → ℝ}
    (hF : ∀ j ∈ s, Continuous (F j)) :
    gibbsExpectation d N ℓ β ν h (fun φ => ∑ j ∈ s, F j φ) =
      ∑ j ∈ s, gibbsExpectation d N ℓ β ν h (F j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [gibbsExpectation]
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    rw [gibbsExpectation_add β ν h (hF a (Finset.mem_insert_self a s))
      (continuous_finsetSum _ fun j hj => hF j (Finset.mem_insert_of_mem hj)),
      ih fun j hj => hF j (Finset.mem_insert_of_mem hj)]

/-! ### Translation invariance (Lemma 0.2 (a)) -/

theorem onePoint_add (β ν : ℝ) (h : EuclideanSpace ℝ (Fin N)) (a x : Torus d ℓ) (i : Fin N) :
    onePoint d N ℓ β ν h (x + a) i = onePoint d N ℓ β ν h x i := by
  have := gibbsExpectation_shiftConfig a β ν h
    (fun φ => (φ x : EuclideanSpace ℝ (Fin N)) i)
  simp only [shiftConfig_apply] at this
  exact this

theorem twoPointTruncated_add (β ν : ℝ) (h : EuclideanSpace ℝ (Fin N)) (a x y : Torus d ℓ)
    (i k : Fin N) :
    twoPointTruncated d N ℓ β ν h (x + a) (y + a) i k = twoPointTruncated d N ℓ β ν h x y i k := by
  unfold twoPointTruncated
  rw [onePoint_add, onePoint_add]
  have := gibbsExpectation_shiftConfig a β ν h
    (fun φ => (φ x : EuclideanSpace ℝ (Fin N)) i * (φ y : EuclideanSpace ℝ (Fin N)) k)
  simp only [shiftConfig_apply] at this
  rw [this]

/-! ### Orthogonal covariance (Lemma 0.2 (b)) -/

/-- The matrix entry `R_{ij} = (R e_j)_i` of a linear isometry. -/
noncomputable def rotEntry (R : EuclideanSpace ℝ (Fin N) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin N))
    (i j : Fin N) : ℝ :=
  (R (EuclideanSpace.single j 1) : EuclideanSpace ℝ (Fin N)) i

omit [NeZero ℓ] in
theorem rot_apply_coord (R : EuclideanSpace ℝ (Fin N) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin N))
    (v : EuclideanSpace ℝ (Fin N)) (i : Fin N) :
    (R v : EuclideanSpace ℝ (Fin N)) i = ∑ j, rotEntry R i j * v j := by
  conv_lhs => rw [← (EuclideanSpace.basisFun (Fin N) ℝ).sum_repr v]
  simp [map_sum, rotEntry, mul_comm]

theorem onePoint_rot (R : EuclideanSpace ℝ (Fin N) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin N))
    (β ν : ℝ) (h : EuclideanSpace ℝ (Fin N)) (x : Torus d ℓ) (i : Fin N) :
    onePoint d N ℓ β ν (R h) x i = ∑ j, rotEntry R i j * onePoint d N ℓ β ν h x j := by
  unfold onePoint
  rw [gibbsExpectation_rotConfig]
  simp only [rotConfig_apply, rot_apply_coord R]
  rw [gibbsExpectation_sum _ _ _ _ (F := fun j (φ : Torus d ℓ → SpinSphere N) =>
    rotEntry R i j * (φ x : EuclideanSpace ℝ (Fin N)) j)
    fun j _ => continuous_const.mul (continuous_spin_coord x j)]
  exact Finset.sum_congr rfl fun j _ => gibbsExpectation_const_mul _ _ _ _ _

theorem gibbsExpectation_rot_mul (R : EuclideanSpace ℝ (Fin N) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin N))
    (β ν : ℝ) (h : EuclideanSpace ℝ (Fin N)) (x y : Torus d ℓ) (i k : Fin N) :
    gibbsExpectation d N ℓ β ν (R h) (fun φ =>
        (φ x : EuclideanSpace ℝ (Fin N)) i * (φ y : EuclideanSpace ℝ (Fin N)) k) =
      ∑ j, ∑ l, rotEntry R i j * rotEntry R k l *
        gibbsExpectation d N ℓ β ν h (fun φ =>
          (φ x : EuclideanSpace ℝ (Fin N)) j * (φ y : EuclideanSpace ℝ (Fin N)) l) := by
  rw [gibbsExpectation_rotConfig]
  simp only [rotConfig_apply, rot_apply_coord R, Finset.sum_mul_sum]
  have hc : ∀ j l : Fin N, Continuous fun φ : Torus d ℓ → SpinSphere N =>
      (φ x : EuclideanSpace ℝ (Fin N)) j * (φ y : EuclideanSpace ℝ (Fin N)) l :=
    fun j l => (continuous_spin_coord x j).mul (continuous_spin_coord y l)
  rw [gibbsExpectation_sum _ _ _ _ (F := fun j (φ : Torus d ℓ → SpinSphere N) =>
      ∑ l, rotEntry R i j * (φ x : EuclideanSpace ℝ (Fin N)) j *
        (rotEntry R k l * (φ y : EuclideanSpace ℝ (Fin N)) l))
    fun j _ => continuous_finsetSum _ fun l _ =>
      ((continuous_const.mul (continuous_spin_coord x j)).mul
        (continuous_const.mul (continuous_spin_coord y l)))]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [gibbsExpectation_sum _ _ _ _ (F := fun l (φ : Torus d ℓ → SpinSphere N) =>
      rotEntry R i j * (φ x : EuclideanSpace ℝ (Fin N)) j *
        (rotEntry R k l * (φ y : EuclideanSpace ℝ (Fin N)) l))
    fun l _ => ((continuous_const.mul (continuous_spin_coord x j)).mul
        (continuous_const.mul (continuous_spin_coord y l)))]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [show (fun φ : Torus d ℓ → SpinSphere N => rotEntry R i j * (φ x : EuclideanSpace ℝ (Fin N)) j *
      (rotEntry R k l * (φ y : EuclideanSpace ℝ (Fin N)) l)) =
      fun φ => (rotEntry R i j * rotEntry R k l) * ((φ x : EuclideanSpace ℝ (Fin N)) j *
        (φ y : EuclideanSpace ℝ (Fin N)) l) from funext fun φ => by ring]
  exact gibbsExpectation_const_mul _ _ _ _ _

theorem twoPointTruncated_rot (R : EuclideanSpace ℝ (Fin N) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin N))
    (β ν : ℝ) (h : EuclideanSpace ℝ (Fin N)) (x y : Torus d ℓ) (i k : Fin N) :
    twoPointTruncated d N ℓ β ν (R h) x y i k =
      ∑ j, ∑ l, rotEntry R i j * rotEntry R k l * twoPointTruncated d N ℓ β ν h x y j l := by
  unfold twoPointTruncated
  rw [gibbsExpectation_rot_mul, onePoint_rot, onePoint_rot, Finset.sum_mul_sum]
  simp only [mul_sub, Finset.sum_sub_distrib]
  congr 1
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => by ring

end Balaban
