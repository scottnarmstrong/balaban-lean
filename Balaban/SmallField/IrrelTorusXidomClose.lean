/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.SmallField.IrrelTorusXidomScaled
public import Balaban.SmallField.XiD1C
public import Balaban.SmallField.XiUnitWitness
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Close field estimate for a real-centred complex datum

The vector field `b = ν(h+h')` differs from `ν(p+z)` by a term of order `τ²ζ`.
-/

@[expose] public section

namespace Balaban.SmallField

open Balaban.Background Balaban.Multiscale

/-- Source tube bounds imply the field closeness part of `DataHyp`. -/
theorem b_close_of_source_tube {N : ℕ} {p h : Fin N → ℝ} {z h' : Fin N → ℂ}
    {ν τ ζ : ℝ} (hν : 0 < ν) (hτ : 0 < τ) (hτ1 : τ ≤ 1)
    (hντ : ν ≤ τ ^ 2) (hζ : 0 < ζ) (hζ1 : ζ ≤ 1 / 200)
    (hp : |∑ i, p i ^ 2 - 1| < τ ^ 2 * ζ)
    (hh1 : ν * |1 - (∑ i, p i * h i) / rn p| < τ ^ 2 * ζ ^ 2)
    (hh2 : ν * |∑ i, h i ^ 2 - 1| < τ ^ 2 * ζ ^ 2)
    (hz : vn z < ζ + τ * ζ)
    (hh' : ν * vn h' < τ ^ 2 * ζ)
    (hph' : ν * ‖∑ i, ((p i / rn p : ℝ) : ℂ) * h' i‖ < τ ^ 2 * ζ ^ 2) :
    ‖((ν : ℂ) • fun i => (h i : ℂ) + h' i) -
      ((ν : ℂ) • fun i => (p i : ℂ) + z i)‖ ≤ 10 * τ ^ 2 * ζ := by
  have hζ2 : 0 < 2 * ζ := by positivity
  have hζ200 : 2 * ζ ≤ 1 / 100 := by linarith
  have hp2 : |∑ i, p i ^ 2 - 1| < τ ^ 2 * (2 * ζ) := by nlinarith [sq_nonneg τ]
  have hh12 : ν * |1 - (∑ i, p i * h i) / rn p| < τ ^ 2 * (2 * ζ) ^ 2 := by
    nlinarith [sq_nonneg τ, sq_nonneg ζ, mul_nonneg (sq_nonneg τ) (sq_nonneg ζ)]
  have hh22 : ν * |∑ i, h i ^ 2 - 1| < τ ^ 2 * (2 * ζ) ^ 2 := by
    nlinarith [sq_nonneg τ, sq_nonneg ζ, mul_nonneg (sq_nonneg τ) (sq_nonneg ζ)]
  have hh'2 : ν * vn h' < τ ^ 2 * (2 * ζ) := by nlinarith [sq_nonneg τ]
  have hph'2 : ν * ‖∑ i, ((p i / rn p : ℝ) : ℂ) * h' i‖ <
      τ ^ 2 * (2 * ζ) ^ 2 := by
    nlinarith [sq_nonneg τ, sq_nonneg ζ, mul_nonneg (sq_nonneg τ) (sq_nonneg ζ)]
  have hs := tube_sizes hν hτ hτ1 hντ hζ2 hζ200 hp2 hh12 hh22 hh'2 hph'2
  let e : Fin N → ℂ := fun i => ((p i / rn p : ℝ) : ℂ)
  have hreal : ν * vn ((fun i => (h i : ℂ)) - e) ≤ 7 / 2 * τ ^ 2 * ζ := by
    have hh := hs.2.2.2.1
    change vn ((fun i => (h i : ℂ)) - e) ≤ 7 / 4 * (τ ^ 2 * (2 * ζ) / ν) at hh
    calc
      _ ≤ ν * (7 / 4 * (τ ^ 2 * (2 * ζ) / ν)) :=
        mul_le_mul_of_nonneg_left hh hν.le
      _ = 7 / 2 * τ ^ 2 * ζ := by field_simp [hν.ne']; ring
  have hcomplex : ν * vn h' ≤ 2 * τ ^ 2 * ζ := by
    have hh := hs.2.2.2.2
    calc
      _ ≤ ν * (τ ^ 2 * (2 * ζ) / ν) :=
        mul_le_mul_of_nonneg_left hh.le hν.le
      _ = 2 * τ ^ 2 * ζ := by field_simp [hν.ne']
  have hrpos : 0 < rn p := rn_pos_of_close hτ hτ1 hζ (by linarith) hp
  have hnorm : vn (e - fun i => (p i : ℂ)) = |1 - rn p| :=
    vn_normalize_sub p hrpos
  have hnormle : vn (e - fun i => (p i : ℂ)) ≤ τ ^ 2 * ζ := by
    rw [hnorm]
    have hh := abs_rn_sub_one_le p
    rw [abs_sub_comm] at hh
    exact hh.trans hp.le
  have hnormν : ν * vn (e - fun i => (p i : ℂ)) ≤ τ ^ 2 * ζ := by
    have hν1 : ν ≤ 1 := hντ.trans (by nlinarith)
    calc
      _ ≤ ν * (τ ^ 2 * ζ) := mul_le_mul_of_nonneg_left hnormle hν.le
      _ ≤ τ ^ 2 * ζ := by nlinarith [mul_nonneg (sub_nonneg.mpr hν1) (by positivity : 0 ≤ τ ^ 2 * ζ)]
  have hzν : ν * vn z ≤ 2 * τ ^ 2 * ζ := by
    have hz2 : vn z ≤ 2 * ζ := by nlinarith [mul_nonneg (sub_nonneg.mpr hτ1) hζ.le]
    calc
      _ ≤ ν * (2 * ζ) := mul_le_mul_of_nonneg_left hz2 hν.le
      _ ≤ τ ^ 2 * (2 * ζ) := mul_le_mul_of_nonneg_right hντ (by positivity)
      _ = 2 * τ ^ 2 * ζ := by ring
  have hpi (v : Fin N → ℂ) : ‖v‖ ≤ vn v :=
    (pi_norm_le_iff_of_nonneg (vn_nonneg v)).2 fun i => norm_le_vn v i
  have he : ((fun i => (h i : ℂ) + h' i) - fun i => (p i : ℂ) + z i) =
      (((fun i => (h i : ℂ)) - e) + (e - fun i => (p i : ℂ))) + (h' - z) := by
    funext i; simp only [Pi.sub_apply, Pi.add_apply]; ring
  rw [← smul_sub, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hν, he]
  have hsum : ‖((fun i => (h i : ℂ)) - e) + (e - fun i => (p i : ℂ)) + (h' - z)‖ ≤
      vn ((fun i => (h i : ℂ)) - e) + vn (e - fun i => (p i : ℂ)) + vn h' + vn z := by
    calc
      _ ≤ ‖(fun i => (h i : ℂ)) - e‖ + ‖e - fun i => (p i : ℂ)‖ +
          ‖h'‖ + ‖z‖ := by
        nlinarith only [norm_add_le ((fun i => (h i : ℂ)) - e + (e - fun i => (p i : ℂ))) (h' - z),
          norm_add_le ((fun i => (h i : ℂ)) - e) (e - fun i => (p i : ℂ)),
          norm_sub_le h' z]
      _ ≤ _ := by
        exact add_le_add (add_le_add (add_le_add (hpi _) (hpi _)) (hpi _)) (hpi _)
  calc
    ν * ‖((fun i => (h i : ℂ)) - e) + (e - fun i => (p i : ℂ)) + (h' - z)‖
        ≤ ν * (vn ((fun i => (h i : ℂ)) - e) + vn (e - fun i => (p i : ℂ)) +
          vn h' + vn z) := mul_le_mul_of_nonneg_left hsum hν.le
    _ = ν * vn ((fun i => (h i : ℂ)) - e) +
        ν * vn (e - fun i => (p i : ℂ)) + ν * vn h' + ν * vn z := by ring
    _ ≤ 7 / 2 * τ ^ 2 * ζ + τ ^ 2 * ζ + 2 * τ ^ 2 * ζ + 2 * τ ^ 2 * ζ := by
      linarith only [hreal, hcomplex, hnormν, hzν]
    _ ≤ 10 * τ ^ 2 * ζ := by nlinarith [sq_nonneg τ]

variable {d L N₀ k N j : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}
  {G : GeneratingSet d L N₀ k ϱ} {ν τ ζ : ℝ}
  {p : Torus d (N₀ * L ^ k) → Fin N → ℝ} {h : Fin N → ℝ}
  {z h' : Torus d (N₀ * L ^ k) → Fin N → ℂ}

/-- The source `ScaledPsiC` witness gives the field closeness estimate at a level site. -/
theorem ScaledPsiC.b_close (H : ScaledPsiC G ν τ ζ j p h z h')
    {y : Torus d (N₀ * L ^ k)} (hy : y ∈ G.Ω 1) (hyj : G.layerIndex y = j)
    (hν : 0 < ν * ((L : ℝ) ^ j) ^ 2) (hτ : 0 < τ) (hτ1 : τ ≤ 1)
    (hντ : ν * ((L : ℝ) ^ j) ^ 2 ≤ τ ^ 2)
    (hζ : 0 < ζ) (hζ1 : ζ ≤ 1 / 200) :
    ‖(((ν * ((L : ℝ) ^ j) ^ 2 : ℝ) : ℂ) • fun i => (h i : ℂ) + h' y i) -
      (((ν * ((L : ℝ) ^ j) ^ 2 : ℝ) : ℂ) • fun i => (p y i : ℂ) + z y i)‖ ≤
      10 * τ ^ 2 * ζ := by
  have hyd : y ∈ dataSites G := (mem_dataSites G).2 (Or.inl hy)
  apply b_close_of_source_tube (p := p y) (h := h) (z := z y) (h' := h' y)
    hν hτ hτ1 hντ hζ hζ1
  · exact H.r2 y hyd
  · simpa [hyj, mul_pow] using H.r3 y hyd
  · simpa [mul_pow] using H.r4
  · exact H.c2a y hyd
  · have hc := H.c3a y hy
    rw [hyj] at hc
    have he : (τ * ζ) ^ 2 / ζ = τ ^ 2 * ζ := by field_simp [hζ.ne']
    rwa [he] at hc
  · simpa [hyj, mul_pow] using H.c3b y hy

end Balaban.SmallField
