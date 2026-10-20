/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Base.KF0FRKernelTorus
public import Balaban.LargeField.Base.KF0FRBall
public import Balaban.LargeField.Base.KF0BoxLift
import Mathlib.Tactic.Linarith

/-!
# `KF0FRLiftGeom`: balls and kernels near the center of two tori (route FR, (T))

`notes/phase1/KF0-FR.md` (T). Through the centred representatives (`boxMap`), the sites of the
box `InBox R₀` of a torus of side `n` are identified with those of a torus of side `n'`. When
`2(R₀ + r) + 1 < n, n'`:

* `torusBall_image_boxMap`: the `ℓ¹` ball of radius `r` around a site of the box is carried onto
  the ball around its image, and its sites lie in `InBox (R₀ + r)` (`inBox_of_mem_torusBall`);
* `torusDisp_boxMap`: the centred displacements of pairs at distance `≤ r` are preserved;
* `sum_torusBall_boxMap`: sums of functions supported in a ball are carried over.
-/

@[expose] public section

open Balaban.Green Balaban.Polymer

namespace Balaban.LargeField.KF0FR

variable {d : ℕ}

theorem cycRep_eq_valMinAbs {n : ℕ} [NeZero n] (a : ZMod n) : cycRep a = a.valMinAbs := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by have := NeZero.ne n; omega⟩
  rfl

theorem distN_eq_valMinAbs {n : ℕ} [NeZero n] (x y : Torus d n) :
    distN x y = ∑ μ, ((x μ - y μ).valMinAbs).natAbs := by
  simp [distN, cycRep_eq_valMinAbs]

/-- A coordinate near the center plus a small displacement is represented exactly. -/
theorem valMinAbs_add_of_abs {n : ℕ} [NeZero n] (a : ZMod n) (k : ℤ)
    (h : 2 * |a.valMinAbs + k| + 1 < n) : (a + (k : ZMod n)).valMinAbs = a.valMinAbs + k := by
  have e : a + (k : ZMod n) = ((a.valMinAbs + k : ℤ) : ZMod n) := by
    rw [Int.cast_add, ZMod.coe_valMinAbs]
  rw [e]
  exact valMinAbs_intCast_of_abs_le (r := (|a.valMinAbs + k|).toNat)
    (by have := abs_nonneg (a.valMinAbs + k); omega)
    (by rw [Int.toNat_of_nonneg (abs_nonneg _)])

theorem natAbs_valMinAbs_sub_comm {n : ℕ} [NeZero n] (a b : ZMod n) :
    ((a - b).valMinAbs).natAbs = ((b - a).valMinAbs).natAbs := by
  rw [← cycRep_eq_valMinAbs, ← cycRep_eq_valMinAbs, ← neg_sub, natAbs_cycRep_neg]

theorem abs_valMinAbs_sub_le_dist {n : ℕ} [NeZero n] {x y : Torus d n} {r : ℝ}
    (h : torusDist d n x y ≤ r) (μ : Fin d) : (|(y μ - x μ).valMinAbs| : ℝ) ≤ r := by
  rw [torusDist_eq_distN, distN_eq_valMinAbs] at h
  have h1 : (((x μ - y μ).valMinAbs).natAbs : ℝ) ≤
      ∑ ν, (((x ν - y ν).valMinAbs).natAbs : ℝ) :=
    Finset.single_le_sum (f := fun ν => (((x ν - y ν).valMinAbs).natAbs : ℝ))
      (fun _ _ => Nat.cast_nonneg _) (Finset.mem_univ μ)
  have h2 : (y μ - x μ).valMinAbs.natAbs = (x μ - y μ).valMinAbs.natAbs :=
    natAbs_valMinAbs_sub_comm _ _
  have h3 : (|(y μ - x μ).valMinAbs| : ℝ) = (((y μ - x μ).valMinAbs).natAbs : ℝ) := by
    rw [Nat.cast_natAbs, Int.cast_abs]
  rw [h3, h2]
  push_cast at h ⊢
  linarith

variable {n n' : ℕ} [NeZero n] [NeZero n']

/-- The sites of a ball around a site of the box lie in a slightly larger box. -/
theorem inBox_of_mem_torusBall {R₀ r : ℕ} (h1 : 2 * (R₀ + r) + 1 < n) {x y : Torus d n}
    (hx : InBox d R₀ n x) (hy : y ∈ torusBall x r) : InBox d (R₀ + r) n y := by
  intro μ
  have hk := abs_valMinAbs_sub_le_dist (mem_torusBall.1 hy) μ
  have hk' : |(y μ - x μ).valMinAbs| ≤ r := by exact_mod_cast hk
  have hxμ := hx μ
  have hsum : |(x μ).valMinAbs + (y μ - x μ).valMinAbs| ≤ R₀ + r :=
    (abs_add_le _ _).trans (by linarith)
  have e : y μ = x μ + (((y μ - x μ).valMinAbs : ℤ) : ZMod n) := by
    rw [ZMod.coe_valMinAbs]; ring
  rw [e, valMinAbs_add_of_abs _ _ (by omega)]
  exact hsum

omit [NeZero n'] in
/-- **Centred displacements of nearby pairs are preserved by `boxMap`.** -/
theorem torusDisp_boxMap {R₁ r : ℕ} (h1 : 2 * (R₁ + r) + 1 < n) (h2 : 2 * r + 1 < n')
    {x y : Torus d n} (hx : InBox d R₁ n x) (hxy : torusDist d n x y ≤ r) :
    torusDisp (boxMap n n' x) (boxMap n n' y) = torusDisp x y := by
  funext μ
  set k := (y μ - x μ).valMinAbs with hk
  have hk' : |k| ≤ r := by exact_mod_cast abs_valMinAbs_sub_le_dist hxy μ
  have hsum : |(x μ).valMinAbs + k| ≤ R₁ + r := (abs_add_le _ _).trans (by have := hx μ; omega)
  have e : y μ = x μ + ((k : ℤ) : ZMod n) := by rw [hk, ZMod.coe_valMinAbs]; ring
  have hy : (y μ).valMinAbs = (x μ).valMinAbs + k := by
    rw [e, valMinAbs_add_of_abs _ _ (by omega)]
  show (boxMap n n' y μ - boxMap n n' x μ).valMinAbs = (y μ - x μ).valMinAbs
  simp only [boxMap]
  rw [hy, Int.cast_add, add_sub_cancel_left, ← hk]
  exact valMinAbs_intCast_of_abs_le h2 hk'

/-- `boxMap` preserves the distance of nearby pairs. -/
theorem torusDist_boxMap {R₁ r : ℕ} (h1 : 2 * (R₁ + r) + 1 < n) (h2 : 2 * r + 1 < n')
    {x y : Torus d n} (hx : InBox d R₁ n x) (hxy : torusDist d n x y ≤ r) :
    torusDist d n' (boxMap n n' x) (boxMap n n' y) = torusDist d n x y := by
  have hd := torusDisp_boxMap h1 h2 hx hxy
  rw [torusDist_eq_distN, torusDist_eq_distN, distN_eq_valMinAbs, distN_eq_valMinAbs]
  congr 1
  refine Finset.sum_congr rfl fun μ _ => ?_
  have := congrFun hd μ
  simp only [torusDisp] at this
  rw [natAbs_valMinAbs_sub_comm, this, natAbs_valMinAbs_sub_comm]

/-- **Balls are carried onto balls.** -/
theorem torusBall_image_boxMap {R₀ r : ℕ} (h1 : 2 * (R₀ + r) + 1 < n)
    (h2 : 2 * (R₀ + r) + 1 < n') {x : Torus d n} (hx : InBox d R₀ n x) :
    (torusBall x r).image (boxMap n n') = torusBall (boxMap n n' x) r := by
  ext z'
  constructor
  · intro hz'
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hz'
    rw [mem_torusBall, torusDist_boxMap (R₁ := R₀) (r := r) h1 (by omega) hx
      (mem_torusBall.1 hy)]
    exact mem_torusBall.1 hy
  · intro hz'
    have hx' : InBox d R₀ n' (boxMap n n' x) := inBox_boxMap (by omega) hx
    have hzbox : InBox d (R₀ + r) n' z' := inBox_of_mem_torusBall h2 hx' hz'
    set z := boxMap n' n z' with hz
    have hzz : boxMap n n' z = z' := boxMap_boxMap (by omega) hzbox
    have hzbox1 : InBox d (R₀ + r) n z := inBox_boxMap (by omega) hzbox
    refine Finset.mem_image.2 ⟨z, ?_, hzz⟩
    have hback : boxMap n' n (boxMap n n' x) = x := boxMap_boxMap (by omega) hx
    have := torusDist_boxMap (n := n') (n' := n) (R₁ := R₀) (r := r) h2 (by omega) hx'
      (mem_torusBall.1 hz')
    rw [hback] at this
    rw [mem_torusBall, this]
    exact mem_torusBall.1 hz'

omit [NeZero n] [NeZero n'] in
/-- `boxMap` is injective on a box. -/
theorem boxMap_injOn_inBox {R : ℕ} (h : 2 * R + 1 < n') (S : Finset (Torus d n))
    (hS : ∀ y ∈ S, InBox d R n y) : Set.InjOn (boxMap n n') (S : Set (Torus d n)) :=
  fun a ha b hb hab => by
    have := congrArg (boxMap n' n) hab
    rwa [boxMap_boxMap h (hS a ha), boxMap_boxMap h (hS b hb)] at this

/-- **Sums of functions supported in a ball are carried over**: if `F` vanishes off the ball of
radius `r` around `x` and `F'` off the ball around its image, and they agree through `boxMap` on the
ball, then `∑ F' = ∑ F`. -/
theorem sum_torusBall_boxMap {M : Type*} [AddCommMonoid M] {R₀ r : ℕ}
    (h1 : 2 * (R₀ + r) + 1 < n) (h2 : 2 * (R₀ + r) + 1 < n') {x : Torus d n}
    (hx : InBox d R₀ n x) (F : Torus d n → M) (F' : Torus d n' → M)
    (hF : ∀ y, y ∉ torusBall x r → F y = 0)
    (hF' : ∀ y', y' ∉ torusBall (boxMap n n' x) r → F' y' = 0)
    (hFF : ∀ y ∈ torusBall x r, F' (boxMap n n' y) = F y) :
    ∑ y', F' y' = ∑ y, F y := by
  rw [← Finset.sum_subset (Finset.subset_univ _) fun y' _ hy' => hF' y' hy',
    ← Finset.sum_subset (Finset.subset_univ (torusBall x r)) fun y _ hy => hF y hy,
    ← torusBall_image_boxMap h1 h2 hx,
    Finset.sum_image (boxMap_injOn_inBox (R := R₀ + r) (by omega) _
      fun y hy => inBox_of_mem_torusBall h1 hx hy)]
  exact Finset.sum_congr rfl hFF

end Balaban.LargeField.KF0FR
