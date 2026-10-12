/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.RegionalFlux
public import Balaban.Frozen.Model.Torus
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Limits of the unpaired marginal flux (Q13-TESTS §A, after (A3))

Whole-torus antisymmetry (`AtermRegion_univ`) and the flux identity
(`regional_marginal_flux_finset`) do not bound the regional flux by a factor `C s^(d+α)`.
The datum `s = u · 1_{x=1}` on `ZMod 5` with the nearest-neighbour kernel and `R = {0}` has
regional sum `u/2` for every `u`, while the whole-torus sum is `0`.  Reusing this same datum for
each scale index `q` (the datum does not depend on `q`), the flux stays `‖u‖/2` while
`C · sL^(-q(D+α))` tends to `0`.  The same holds on the campaign torus `Torus d ℓ`,
`1 ≤ d`, `3 ≤ ℓ`, with the kernel `1_{±e₁}` and `s = u · 1_{e₁}`.  (For `ℓ = 2` one has
`e₁ = -e₁`; the kernel is then `1_{e₁}` and the same value is obtained with a different
count, so `3 ≤ ℓ` is kept.)

## What this does and does not show

It concerns the unpaired marginal channel `Σ_{y∈R} A_j(y)` only.  The model does not impose the
I6 relation of `a_j` to the actual `v₁, v₂`, the omitted-polymer tail, the background response or
the rescaling of the cube.  Hence it is not a counterexample to the grouped bound for
`Σ_R A_j - Corr_j(R_j, B_j)` (`corrSum` in `Def7v2Corr.lean`), which stays open (astra task
Q13-GROUPED).

## Comparison with `regional_flux_diff_le` (no tension)

On the model the sharp value is `‖u‖/2`.  The landed bound has the form `c · Ka · |R|` for the
flux of a field `D` with `‖D z‖ ≤ c` (`crossFlux_le`); here `c = ‖u‖`, `Ka = 2`, `|R| = 1`, so
the bound is `2‖u‖`, a factor `4` above the model value and consistent with it.  Its right side
has no `s^(d+α)` factor, and the model shows none can follow from these facts alone.
-/

@[expose] public section

open Finset

namespace Balaban.LargeField.RegionalFlux

section Linear

variable {ι : Type*} [AddCommGroup ι] [Fintype ι] [DecidableEq ι]

/-- The crossing flux is homogeneous in the field. -/
theorem crossFlux_smul (a s : ι → ℂ) (c : ℂ) (R : Finset ι) :
    crossFlux a (fun x => c * s x) R = c * crossFlux a s R := by
  unfold crossFlux
  rw [mul_left_comm c]
  congr 1
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  ring

/-- The crossing flux is additive in the field. -/
theorem crossFlux_add (a s s' : ι → ℂ) (R : Finset ι) :
    crossFlux a (fun x => s x + s' x) R = crossFlux a s R + crossFlux a s' R := by
  unfold crossFlux
  rw [← mul_add, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  ring

/-- The regional sum is homogeneous in the field (even kernel). -/
theorem AtermRegion_smul (a s : ι → ℂ) (hev : ∀ z, a (-z) = a z) (c : ℂ) (R : Finset ι) :
    AtermRegion a (fun x => c * s x) R = c * AtermRegion a s R := by
  rw [regional_marginal_flux_finset _ _ hev, regional_marginal_flux_finset _ _ hev,
    crossFlux_smul]

end Linear

/-- A positive constant eventually exceeds `C · sL^(-(q (D+α)))`. -/
theorem exists_q_lt_of_pos (C m sL D α : ℝ) (hm : 0 < m) (hα : 0 < α) (hs : 1 < sL)
    (hD : 0 ≤ D) : ∃ q : ℕ, C * sL ^ (-((q : ℝ) * (D + α))) < m := by
  by_cases hC : C ≤ 0
  · refine ⟨0, ?_⟩
    simp only [Nat.cast_zero, zero_mul, neg_zero, Real.rpow_zero, mul_one]
    linarith
  replace hC := not_le.1 hC
  set r : ℝ := sL ^ (-(D + α)) with hr
  have hr0 : 0 < r := Real.rpow_pos_of_pos (by linarith) _
  have hr1 : r < 1 := Real.rpow_lt_one_of_one_lt_of_neg hs (by linarith)
  obtain ⟨q, hq⟩ := exists_pow_lt_of_lt_one (div_pos hm hC) hr1
  refine ⟨q, ?_⟩
  have e : sL ^ (-((q : ℝ) * (D + α))) = r ^ q := by
    rw [hr, ← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]
    congr 1; ring
  rw [e]
  rw [lt_div_iff₀ hC] at hq
  linarith

section Scaled

/-- Scaled model: `s = u · bump` has crossing flux `u/2` at `R = {0}`. -/
theorem crossFlux_nn_scaled (u : ℂ) :
    crossFlux nnKernel (fun x => u * bump x) {0} = u / 2 := by
  rw [crossFlux_smul, crossFlux_nn_example]; ring

/-- The whole-torus regional sum of the scaled model vanishes. -/
theorem AtermRegion_nn_scaled_univ (u : ℂ) :
    AtermRegion nnKernel (fun x => u * bump x) Finset.univ = 0 :=
  AtermRegion_univ _ _ nnKernel_even

/-- The regional sum of the scaled model at `R = {0}` is `u/2`. -/
theorem AtermRegion_nn_scaled (u : ℂ) :
    AtermRegion nnKernel (fun x => u * bump x) {0} = u / 2 := by
  rw [regional_marginal_flux_finset _ _ nnKernel_even, crossFlux_nn_scaled]

/-- **No irrelevant bound for the crossing flux**: the flux is the constant `‖u‖/2`, while
`C sL^(-q (D+α))` tends to `0`. -/
theorem crossFlux_nn_not_irrelevant (u : ℂ) (hu : u ≠ 0) (C α sL D : ℝ) (hα : 0 < α)
    (hs : 1 < sL) (hD : 0 ≤ D) :
    ∃ q : ℕ, C * sL ^ (-((q : ℝ) * (D + α))) <
      ‖crossFlux nnKernel (fun x => u * bump x) {0}‖ := by
  rw [crossFlux_nn_scaled]
  refine exists_q_lt_of_pos C _ sL D α ?_ hα hs hD
  simpa using hu

/-- Closed form: no constants `C`, `α > 0` give `‖Σ_{y∈{0}} A(y)‖ ≤ C sL^(-q (D+α))` for all `q`. -/
theorem AtermRegion_nn_not_irrelevant (u : ℂ) (hu : u ≠ 0) (sL D : ℝ) (hs : 1 < sL)
    (hD : 0 ≤ D) :
    ¬ ∃ C α : ℝ, 0 < α ∧ ∀ q : ℕ,
      ‖AtermRegion nnKernel (fun x => u * bump x) {0}‖ ≤ C * sL ^ (-((q : ℝ) * (D + α))) := by
  rintro ⟨C, α, hα, h⟩
  obtain ⟨q, hq⟩ := crossFlux_nn_not_irrelevant u hu C α sL D hα hs hD
  have := h q
  rw [regional_marginal_flux_finset _ _ nnKernel_even] at this
  linarith

end Scaled

section Lattice

variable {d ℓ : ℕ} [NeZero ℓ]

open Balaban

/-- The first unit vector of the torus. -/
def unitVec (hd : 1 ≤ d) : Torus d ℓ := Pi.single ⟨0, hd⟩ 1

/-- The kernel `1_{±e₁}` on the torus. -/
noncomputable def latKernel (hd : 1 ≤ d) (z : Torus d ℓ) : ℂ :=
  by classical exact if z = unitVec hd ∨ z = -unitVec hd then 1 else 0

/-- The field `u · 1_{e₁}`. -/
noncomputable def latField (hd : 1 ≤ d) (u : ℂ) (x : Torus d ℓ) : ℂ :=
  by classical exact if x = unitVec hd then u else 0

omit [NeZero ℓ] in
theorem latKernel_even (hd : 1 ≤ d) (z : Torus d ℓ) :
    latKernel hd (-z) = latKernel hd z := by
  classical
  unfold latKernel
  have h : (-z = unitVec hd ∨ -z = -unitVec hd) ↔ (z = unitVec hd ∨ z = -unitVec hd) := by
    constructor
    · rintro (h | h)
      · right; rw [← h]; simp
      · left; exact neg_inj.1 h
    · rintro (h | h)
      · right; rw [h]
      · left; rw [h]; simp
  simp only [h]

omit [NeZero ℓ] in
theorem unitVec_ne_zero (hd : 1 ≤ d) (hℓ : 3 ≤ ℓ) : (unitVec hd : Torus d ℓ) ≠ 0 := by
  intro h
  have := congrFun h ⟨0, hd⟩
  simp only [unitVec, Pi.single_eq_same, Pi.zero_apply] at this
  have hf : Fact (1 < ℓ) := ⟨by omega⟩
  exact one_ne_zero (α := ZMod ℓ) this

omit [NeZero ℓ] in
theorem unitVec_ne_neg (hd : 1 ≤ d) (hℓ : 3 ≤ ℓ) : (unitVec hd : Torus d ℓ) ≠ -unitVec hd := by
  intro h
  have := congrFun h ⟨0, hd⟩
  simp only [unitVec, Pi.single_eq_same, Pi.neg_apply] at this
  have h2 : (2 : ZMod ℓ) = 0 := by linear_combination this
  have h3 : ((2 : ℕ) : ZMod ℓ) = 0 := by exact_mod_cast h2
  rw [ZMod.natCast_eq_zero_iff] at h3
  have := Nat.le_of_dvd (by norm_num) h3
  omega

/-- The regional sum on the torus: `u/2` for `R = {0}`. -/
theorem crossFlux_lat (hd : 1 ≤ d) (hℓ : 3 ≤ ℓ) (u : ℂ) :
    crossFlux (latKernel (ℓ := ℓ) hd) (latField hd u) {0} = u / 2 := by
  classical
  have h0 := unitVec_ne_zero (ℓ := ℓ) hd hℓ
  have h1 := unitVec_ne_neg (ℓ := ℓ) hd hℓ
  have hs0 : latField (ℓ := ℓ) hd u (0 : Torus d ℓ) = 0 := by
    simp [latField, h0.symm]
  have key : ∀ x : Torus d ℓ, latKernel hd (x - 0) * (latField hd u x - latField hd u (0 : Torus d ℓ)) =
      if x = unitVec hd then u else 0 := by
    intro x
    rw [hs0, sub_zero, sub_zero]
    by_cases hx : x = unitVec hd
    · subst hx; simp [latKernel, latField]
    · simp [latField, hx]
  unfold crossFlux
  rw [Finset.sum_singleton]
  simp_rw [key]
  rw [Finset.sum_ite_eq' ]
  have : unitVec (ℓ := ℓ) hd ∈ ({0} : Finset (Torus d ℓ))ᶜ := by simpa using h0
  simp only [this, ite_true]; ring

theorem AtermRegion_lat (hd : 1 ≤ d) (hℓ : 3 ≤ ℓ) (u : ℂ) :
    AtermRegion (latKernel (ℓ := ℓ) hd) (latField hd u) {0} = u / 2 := by
  rw [regional_marginal_flux_finset _ _ (latKernel_even hd), crossFlux_lat hd hℓ]

theorem AtermRegion_lat_univ (hd : 1 ≤ d) (u : ℂ) :
    AtermRegion (latKernel (ℓ := ℓ) hd) (latField hd u) Finset.univ = 0 :=
  AtermRegion_univ _ _ (latKernel_even hd)

theorem AtermRegion_lat_not_irrelevant (hd : 1 ≤ d) (hℓ : 3 ≤ ℓ) (u : ℂ) (hu : u ≠ 0)
    (sL D : ℝ) (hs : 1 < sL) (hD : 0 ≤ D) :
    ¬ ∃ C α : ℝ, 0 < α ∧ ∀ q : ℕ,
      ‖AtermRegion (latKernel (ℓ := ℓ) hd) (latField hd u) {0}‖
        ≤ C * sL ^ (-((q : ℝ) * (D + α))) := by
  rintro ⟨C, α, hα, h⟩
  obtain ⟨q, hq⟩ := exists_q_lt_of_pos C (‖u / 2‖) sL D α (by simpa using hu) hα hs hD
  have := h q
  rw [AtermRegion_lat hd hℓ] at this
  linarith

end Lattice

end Balaban.LargeField.RegionalFlux
