/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.RegionalSourceTerm
public import Balaban.SmallField.RenormAnisoCtx
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# From the class data hypothesis to the pair bound of the regional source term

`RegionalSourceTerm.pair_bound_of_data` asks for pair data `‖ψ_x - ψ_y‖₂ ≤ D σ ε`, a uniform
`ℓ²` bound `‖ψ_x‖₂ ≤ B`, `‖ψ_x·ψ_x - 1‖ ≤ 1/2` and `‖ν_j h - ν' ψ_y‖₂ ≤ σ² ε`.  The class gives
`SmallField.DataHyp` (and `DataHypAniso`, which extends it): nearest-neighbour differences only,
`‖ψ 0‖ ≤ 2`, `‖b - ν ψ 0‖ ≤ σ² ε`, in the sup norm of `Fin N → ℂ`.  This file bridges the two.

* (T1) `norm_sub_le_l1Dist_mul`: the nearest-neighbour bound gives `‖ψ x - ψ y‖ ≤ ℓ¹(x - y) σ ε`,
  hence `≤ d r σ ε` when all coordinates of `x - y` are at most `r`.
* (T2) `norm_le_two_add_l1Dist`: `‖ψ x‖ ≤ 2 + ℓ¹(x) σ ε` (grows with the distance);
  `nrm2_sq_le_of_real`: for real-valued `ψ`, `‖ψ x‖₂² ≤ 1 + σ² ε`.  For complex data no uniform
  bound follows from `DataHyp` (see below).
* (T3) `norm_le_nrm2`, `nrm2_le_sqrt_mul_norm`: `‖v‖ ≤ ‖v‖₂ ≤ √N ‖v‖`.
* (T4) `pointwise_bound_of_unifBound` (named premise: an `ℓ²` bound `B` of `ψ x` and `ψ 0`),
  `pointwise_bound_of_real` (premise: `ψ` real-valued, `B = 3/2`), and
  `pointwise_bound_of_distance` (no premise; `B = √N (2 + ℓ¹ σ ε)`).  The conclusion is the
  pointwise hypothesis `hpt` of `v2Part_le` for the pair `(y, x) = (0, x)`.
* (T5) `hpt_of_dataHyp_at_centres`: the hypothesis `hpt` of `v2Part_le` on the torus, from a
  `DataHyp` for the pulled-back field at each centre.
* (T6) `nonempty_dataHyp_rotating`: a non-constant real field satisfies `DataHyp`, and the bridge
  applies to it (`rotating_pointwise_bound`).

## What is supplied from the class and what is not

Supplied from `DataHyp`: the pair bound `hD` (with `D = √N ℓ¹`), `hn`, `hb` (given
`ν_j h = b` and `ν' = ν`), and `hax` (from `σ² ε ≤ 1/2`).  Not supplied by `DataHyp`: the numerical
premises `σ² ε ≤ 1/2`, `0 ≤ σ ≤ 1`, `0 ≤ ν ≤ σ²`, `ε ≥ 0`; the uniform bound `B` for complex data
(the example `ψ = (cosh t, i sinh t)` has `ψ·ψ = 1` and unbounded norm; `Dom` is abstract and
carries no tube information); the translation of the data hypothesis to every centre of `R`
(one `DataHyp` at each centre is the premise of `hpt_of_dataHyp_at_centres`); and the identification
of the weight `D y x` of the regional lemma with `√N` times the `ℓ¹` distance of the relative
position of the blocks on the model lattice.
-/

@[expose] public section

open Finset Real

namespace Balaban.LargeField.RegionalDataBridge

open Balaban.SmallField Balaban.LargeField.RegionalArith

variable {d N : ℕ}

/-! ### (T1) Path summation on the model lattice -/

/-- The `ℓ¹` distance `Σ_μ |x_μ - y_μ|` of two sites of `ℤ^d`. -/
def l1Dist (x y : SmallField.Site d) : ℝ := ∑ μ, |((x μ : ℝ) - (y μ : ℝ))|

theorem l1Dist_nonneg (x y : SmallField.Site d) : 0 ≤ l1Dist x y := Finset.sum_nonneg fun _ _ => abs_nonneg _

/-- If all coordinates of `x - y` are at most `r` in absolute value, `ℓ¹(x - y) ≤ d r`. -/
theorem l1Dist_le_card_mul {x y : SmallField.Site d} {r : ℝ} (h : ∀ μ, |((x μ : ℝ) - (y μ : ℝ))| ≤ r) :
    l1Dist x y ≤ d * r := by
  unfold l1Dist
  calc ∑ μ, |((x μ : ℝ) - (y μ : ℝ))| ≤ ∑ _μ : Fin d, r := Finset.sum_le_sum fun μ _ => h μ
    _ = d * r := by simp

private theorem step_bound {E : Type*} [SeminormedAddCommGroup E] (f : SmallField.Site d → E) {c : ℝ}
    (hadj : ∀ x μ, ‖f (x + Pi.single μ 1) - f x‖ ≤ c) (z : SmallField.Site d) (μ : Fin d) (n : ℤ) :
    ‖f (z + Pi.single μ n) - f z‖ ≤ |(n : ℝ)| * c := by
  have hc : 0 ≤ c := (norm_nonneg _).trans (hadj z μ)
  induction n using Int.induction_on with
  | zero => simp
  | succ i ih =>
    have e : z + Pi.single μ ((i : ℤ) + 1) = (z + Pi.single μ (i : ℤ)) + Pi.single μ 1 := by
      rw [Pi.single_add]; abel
    have h1 := hadj (z + Pi.single μ (i : ℤ)) μ
    rw [e]
    calc ‖f (z + Pi.single μ (i : ℤ) + Pi.single μ 1) - f z‖
        = ‖(f (z + Pi.single μ (i : ℤ) + Pi.single μ 1) - f (z + Pi.single μ (i : ℤ))) +
            (f (z + Pi.single μ (i : ℤ)) - f z)‖ := by congr 1; abel
      _ ≤ c + |((i : ℤ) : ℝ)| * c := (norm_add_le _ _).trans (add_le_add h1 ih)
      _ = |(((i : ℤ) + 1 : ℤ) : ℝ)| * c := by
          push_cast
          rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ (i : ℝ)),
            abs_of_nonneg (by positivity : (0 : ℝ) ≤ (i : ℝ) + 1)]
          ring
  | pred i ih =>
    have e : (z + Pi.single μ (-(i : ℤ) - 1)) + Pi.single μ 1 = z + Pi.single μ (-(i : ℤ)) := by
      rw [add_assoc, ← Pi.single_add]; congr 2; ring
    have h1 := hadj (z + Pi.single μ (-(i : ℤ) - 1)) μ
    rw [e] at h1
    calc ‖f (z + Pi.single μ (-(i : ℤ) - 1)) - f z‖
        = ‖(f (z + Pi.single μ (-(i : ℤ))) - f z) -
            (f (z + Pi.single μ (-(i : ℤ))) - f (z + Pi.single μ (-(i : ℤ) - 1)))‖ := by
          congr 1; abel
      _ ≤ |((-(i : ℤ) : ℤ) : ℝ)| * c + c := (norm_sub_le _ _).trans (add_le_add ih h1)
      _ = |((-(i : ℤ) - 1 : ℤ) : ℝ)| * c := by
          push_cast
          have h0 : (0 : ℝ) ≤ (i : ℝ) := by positivity
          have : |(-(i : ℝ) - 1)| = (i : ℝ) + 1 := by
            rw [show -(i : ℝ) - 1 = -((i : ℝ) + 1) by ring, abs_neg, abs_of_nonneg (by linarith)]
          rw [abs_neg, abs_of_nonneg h0, this]
          ring

/-- **(T1)** If all nearest-neighbour differences of `f` are at most `c`, then
`‖f x - f y‖ ≤ ℓ¹(x - y) c`. -/
theorem norm_sub_le_l1Dist_mul {E : Type*} [SeminormedAddCommGroup E] (f : SmallField.Site d → E)
    {c : ℝ} (hadj : ∀ x μ, ‖f (x + Pi.single μ 1) - f x‖ ≤ c) (x y : SmallField.Site d) :
    ‖f x - f y‖ ≤ l1Dist x y * c := by
  classical
  have key : ∀ s : Finset (Fin d),
      ‖f (fun ν => if ν ∈ s then x ν else y ν) - f y‖ ≤ (∑ μ ∈ s, |((x μ : ℝ) - (y μ : ℝ))|) * c := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert μ s hμ ih =>
      have e : (fun ν => if ν ∈ insert μ s then x ν else y ν) =
          (fun ν => if ν ∈ s then x ν else y ν) + Pi.single μ (x μ - y μ) := by
        funext ν
        by_cases h : ν = μ
        · subst h; simp [hμ]
        · simp [h]
      rw [e, Finset.sum_insert hμ]
      have h1 := step_bound f hadj (fun ν => if ν ∈ s then x ν else y ν) μ (x μ - y μ)
      calc ‖f ((fun ν => if ν ∈ s then x ν else y ν) + Pi.single μ (x μ - y μ)) - f y‖
          = ‖(f ((fun ν => if ν ∈ s then x ν else y ν) + Pi.single μ (x μ - y μ)) -
              f (fun ν => if ν ∈ s then x ν else y ν)) +
              (f (fun ν => if ν ∈ s then x ν else y ν) - f y)‖ := by congr 1; abel
        _ ≤ |(((x μ - y μ : ℤ)) : ℝ)| * c + (∑ μ ∈ s, |((x μ : ℝ) - (y μ : ℝ))|) * c :=
            (norm_add_le _ _).trans (add_le_add h1 ih)
        _ = _ := by push_cast; ring
  have := key Finset.univ
  simpa [l1Dist] using this

/-! ### (T3) The two norms on `Fin N → ℂ` -/

/-- The sup norm of `Fin N → ℂ` (the norm of `Spin N`) is at most the `ℓ²` norm. -/
theorem norm_le_nrm2 (v : Fin N → ℂ) : ‖v‖ ≤ nrm2 v := by
  rw [nrm2_eq]
  refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun i => ?_
  refine Real.le_sqrt_of_sq_le ?_
  exact Finset.single_le_sum (f := fun j => ‖v j‖ ^ 2) (fun j _ => by positivity)
    (Finset.mem_univ i)

/-- The `ℓ²` norm is at most `√N` times the sup norm. -/
theorem nrm2_le_sqrt_mul_norm (v : Fin N → ℂ) : nrm2 v ≤ Real.sqrt N * ‖v‖ := by
  rw [nrm2_eq]
  have h : ∑ i, ‖v i‖ ^ 2 ≤ N * ‖v‖ ^ 2 := by
    calc ∑ i, ‖v i‖ ^ 2 ≤ ∑ _i : Fin N, ‖v‖ ^ 2 :=
          Finset.sum_le_sum fun i _ => pow_le_pow_left₀ (norm_nonneg _) (norm_le_pi_norm v i) 2
      _ = N * ‖v‖ ^ 2 := by simp
  calc Real.sqrt (∑ i, ‖v i‖ ^ 2) ≤ Real.sqrt (N * ‖v‖ ^ 2) := Real.sqrt_le_sqrt h
    _ = Real.sqrt N * ‖v‖ := by
        rw [Real.sqrt_mul (Nat.cast_nonneg _), Real.sqrt_sq (norm_nonneg _)]

/-! ### (T2) Bounds on `ψ x` from the data hypothesis -/

section Data

variable {Dom : Set ((SmallField.Site d → Spin N) × Spin N)} {ν σ ε K₂ : ℝ}
  {ψ : SmallField.Site d → Spin N} {b : Spin N}

/-- **(T1 for `DataHyp`)** `‖ψ x - ψ y‖ ≤ ℓ¹(x - y) σ ε`. -/
theorem dataHyp_norm_sub_le (H : DataHyp Dom ν σ ε K₂ ψ b) (x y : SmallField.Site d) :
    ‖ψ x - ψ y‖ ≤ l1Dist x y * (σ * ε) :=
  norm_sub_le_l1Dist_mul ψ H.adj x y

/-- **(T2b)** `‖ψ x‖ ≤ 2 + ℓ¹(x) σ ε`: the bound grows with the distance from the centre. -/
theorem norm_le_two_add_l1Dist (H : DataHyp Dom ν σ ε K₂ ψ b) (x : SmallField.Site d) :
    ‖ψ x‖ ≤ 2 + l1Dist x 0 * (σ * ε) := by
  have h := dataHyp_norm_sub_le H x 0
  have := H.bdd0
  have := norm_le_insert' (ψ x) (ψ 0)
  linarith

/-- **(T2a)** For a real-valued field, `‖ψ x‖₂² ≤ 1 + σ² ε`: here `ψ·ψ = ‖ψ‖₂²`. -/
theorem nrm2_sq_le_of_real (H : DataHyp Dom ν σ ε K₂ ψ b)
    (hreal : ∀ x i, (ψ x i).im = 0) (x : SmallField.Site d) :
    nrm2 (ψ x) ^ 2 ≤ 1 + σ ^ 2 * ε := by
  have h1 := (Complex.abs_re_le_norm _).trans (H.sq x)
  have h2 : (dot (ψ x) (ψ x)).re = ∑ i, ‖ψ x i‖ ^ 2 := by
    unfold dot
    rw [Complex.re_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Complex.mul_re, hreal x i, Complex.sq_norm, Complex.normSq_apply, hreal x i]
    ring
  rw [nrm2_eq, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => by positivity), ← h2]
  have := (abs_le.1 (by simpa using h1 : |(dot (ψ x) (ψ x)).re - 1| ≤ σ ^ 2 * ε)).2
  linarith

/-- For a real-valued field with `σ² ε ≤ 1/2`, `‖ψ x‖₂ ≤ 3/2`. -/
theorem nrm2_le_of_real (H : DataHyp Dom ν σ ε K₂ ψ b) (hreal : ∀ x i, (ψ x i).im = 0)
    (hη : σ ^ 2 * ε ≤ 1 / 2) (x : SmallField.Site d) : nrm2 (ψ x) ≤ 3 / 2 := by
  have := nrm2_sq_le_of_real H hreal x
  nlinarith [nrm2_nonneg (ψ x)]

/-! ### (T4) The bridge

The `ℓ²` norm costs a factor `√N` against the sup norm of `Spin N` (`‖b - ν ψ 0‖ ≤ σ² ε` only gives
`‖·‖₂ ≤ √N σ² ε`).  It is absorbed into the field size: the regional hypotheses are used with
`ε' = √N ε`, so that `σ² ε' ≤ 1/2` is the numerical premise, the weight is the plain `ℓ¹` distance
and the conclusion carries `ε'^2 = N ε²`. -/

/-- **(T4, with a named premise)** The pointwise hypothesis of `v2Part_le` for the pair `(0, x)`,
from a `DataHyp` datum, given an `ℓ²` bound `B` of `ψ x` and `ψ 0` (the regularity premise; for
real-valued data see `pointwise_bound_of_real`) and a weight `D ≥ ℓ¹(x)`.  Here `ν_j h = b`,
`ν' = ν`, `N ≥ 1`, and the numerical premises are `σ² √N ε ≤ 1/2`, `0 ≤ σ ≤ 1`, `0 ≤ ν ≤ σ²`,
`ε ≥ 0`.  The field size of the regional lemma is `ε' = √N ε`. -/
theorem pointwise_bound_of_unifBound (H : DataHyp Dom ν σ ε K₂ ψ b) {νj B D : ℝ}
    {h : Fin N → ℂ} (hN : 1 ≤ N) (hbh : (νj : ℂ) • h = b) (x : SmallField.Site d)
    (hBx : nrm2 (ψ x) ≤ B) (hB0 : nrm2 (ψ 0) ≤ B) (hD : l1Dist x 0 ≤ D)
    (hη : σ ^ 2 * (Real.sqrt N * ε) ≤ 1 / 2) (hν0 : 0 ≤ ν) (hνσ : ν ≤ σ ^ 2) (hσ0 : 0 ≤ σ)
    (hσ1 : σ ≤ 1) (hε0 : 0 ≤ ε) :
    ‖(νj : ℂ) * (dot h (Def7v2.unitDirC (ψ x)) - dot h (Def7v2.unitDirC (ψ 0)))‖ ≤
      sourceConstC B * (D ^ 2 + D) * σ ^ 3 * (Real.sqrt N * ε) ^ 2 := by
  have hD0 : 0 ≤ D := (l1Dist_nonneg _ _).trans hD
  have hs1 : 1 ≤ Real.sqrt N := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt (by exact_mod_cast hN)
  have hs0 : 0 ≤ Real.sqrt N := by linarith
  have hε' : 0 ≤ Real.sqrt N * ε := mul_nonneg hs0 hε0
  have hσ2 : 0 ≤ σ ^ 2 := by positivity
  have hεle : σ ^ 2 * ε ≤ σ ^ 2 * (Real.sqrt N * ε) :=
    mul_le_mul_of_nonneg_left (by nlinarith) hσ2
  refine RegionalSourceTerm.pair_bound_of_data (ψx := ψ x) (ψy := ψ 0) (ν' := ν) (ε := Real.sqrt N * ε)
    ((H.sq x).trans (hεle.trans hη)) hBx hB0 ?_ ?_ ((H.sq 0).trans hεle) hη hν0 hνσ hσ0 hσ1 hε' hD0
  · calc nrm2 (ψ x - ψ 0) ≤ Real.sqrt N * ‖ψ x - ψ 0‖ := nrm2_le_sqrt_mul_norm _
      _ ≤ Real.sqrt N * (l1Dist x 0 * (σ * ε)) :=
          mul_le_mul_of_nonneg_left (dataHyp_norm_sub_le H x 0) hs0
      _ = l1Dist x 0 * σ * (Real.sqrt N * ε) := by ring
      _ ≤ D * σ * (Real.sqrt N * ε) := by gcongr
  · rw [hbh]
    calc nrm2 (b - (ν : ℂ) • ψ 0) ≤ Real.sqrt N * ‖b - (ν : ℂ) • ψ 0‖ := nrm2_le_sqrt_mul_norm _
      _ ≤ Real.sqrt N * (σ ^ 2 * ε) := mul_le_mul_of_nonneg_left H.b_close hs0
      _ = σ ^ 2 * (Real.sqrt N * ε) := by ring

/-- **(T4, real-valued data)** For a real-valued `ψ` (each component has zero imaginary part) no
extra premise is needed: `B = 3/2`. -/
theorem pointwise_bound_of_real (H : DataHyp Dom ν σ ε K₂ ψ b) {νj D : ℝ}
    {h : Fin N → ℂ} (hN : 1 ≤ N) (hbh : (νj : ℂ) • h = b) (hreal : ∀ x i, (ψ x i).im = 0)
    (x : SmallField.Site d) (hD : l1Dist x 0 ≤ D)
    (hη : σ ^ 2 * (Real.sqrt N * ε) ≤ 1 / 2) (hν0 : 0 ≤ ν) (hνσ : ν ≤ σ ^ 2) (hσ0 : 0 ≤ σ)
    (hσ1 : σ ≤ 1) (hε0 : 0 ≤ ε) :
    ‖(νj : ℂ) * (dot h (Def7v2.unitDirC (ψ x)) - dot h (Def7v2.unitDirC (ψ 0)))‖ ≤
      sourceConstC (3 / 2) * (D ^ 2 + D) * σ ^ 3 * (Real.sqrt N * ε) ^ 2 := by
  have hs1 : 1 ≤ Real.sqrt N := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt (by exact_mod_cast hN)
  have hη' : σ ^ 2 * ε ≤ 1 / 2 :=
    (mul_le_mul_of_nonneg_left (by nlinarith) (by positivity : 0 ≤ σ ^ 2)).trans hη
  exact pointwise_bound_of_unifBound H hN hbh x (nrm2_le_of_real H hreal hη' x)
    (nrm2_le_of_real H hreal hη' 0) hD hη hν0 hνσ hσ0 hσ1 hε0

/-- **(T4, no regularity premise)** For general complex data the bound `B` degrades with the
distance: `B = √N (2 + ℓ¹(x) σ ε)`. -/
theorem pointwise_bound_of_distance (H : DataHyp Dom ν σ ε K₂ ψ b) {νj D : ℝ}
    {h : Fin N → ℂ} (hN : 1 ≤ N) (hbh : (νj : ℂ) • h = b) (x : SmallField.Site d)
    (hD : l1Dist x 0 ≤ D)
    (hη : σ ^ 2 * (Real.sqrt N * ε) ≤ 1 / 2) (hν0 : 0 ≤ ν) (hνσ : ν ≤ σ ^ 2) (hσ0 : 0 ≤ σ)
    (hσ1 : σ ≤ 1) (hε0 : 0 ≤ ε) :
    ‖(νj : ℂ) * (dot h (Def7v2.unitDirC (ψ x)) - dot h (Def7v2.unitDirC (ψ 0)))‖ ≤
      sourceConstC (Real.sqrt N * (2 + l1Dist x 0 * (σ * ε))) * (D ^ 2 + D) * σ ^ 3 *
        (Real.sqrt N * ε) ^ 2 := by
  have hs0 : 0 ≤ Real.sqrt N := Real.sqrt_nonneg _
  have hl := l1Dist_nonneg x 0
  have hσε : 0 ≤ σ * ε := mul_nonneg hσ0 hε0
  refine pointwise_bound_of_unifBound H hN hbh x
    (B := Real.sqrt N * (2 + l1Dist x 0 * (σ * ε))) ((nrm2_le_sqrt_mul_norm _).trans (mul_le_mul_of_nonneg_left (norm_le_two_add_l1Dist H x) hs0))
    ((nrm2_le_sqrt_mul_norm _).trans (mul_le_mul_of_nonneg_left ?_ hs0)) hD hη hν0 hνσ hσ0 hσ1 hε0
  have := H.bdd0
  nlinarith [mul_nonneg hl hσε]

/-- The same for `DataHypAniso`, which extends `DataHyp`. -/
theorem pointwise_bound_of_real_aniso (H : DataHypAniso Dom ν σ ε K₂ ψ b) {νj D : ℝ}
    {h : Fin N → ℂ} (hN : 1 ≤ N) (hbh : (νj : ℂ) • h = b) (hreal : ∀ x i, (ψ x i).im = 0)
    (x : SmallField.Site d) (hD : l1Dist x 0 ≤ D)
    (hη : σ ^ 2 * (Real.sqrt N * ε) ≤ 1 / 2) (hν0 : 0 ≤ ν) (hνσ : ν ≤ σ ^ 2) (hσ0 : 0 ≤ σ)
    (hσ1 : σ ≤ 1) (hε0 : 0 ≤ ε) :
    ‖(νj : ℂ) * (dot h (Def7v2.unitDirC (ψ x)) - dot h (Def7v2.unitDirC (ψ 0)))‖ ≤
      sourceConstC (3 / 2) * (D ^ 2 + D) * σ ^ 3 * (Real.sqrt N * ε) ^ 2 :=
  pointwise_bound_of_real H.toDataHyp hN hbh hreal x hD hη hν0 hνσ hσ0 hσ1 hε0

end Data

/-! ### (T5) The hypothesis `hpt` of `v2Part_le` on the torus -/

section Torus

variable {L N₁ m₁ k : ℕ} {Dom : Set ((SmallField.Site d → Spin N) × Spin N)} {ν σ ε K₂ : ℝ}

/-- **(T5)** The hypothesis `hpt` of `v2Part_le` (with `Cs = sourceConstC B` and field size
`√N ε`) from a class data hypothesis at each centre `y ∈ R`.

The typing data: for each centre `y` a relative-position map `pos y : CTorus → Site d` (the block of
a fine site seen from the block of `y`, `pos y y = 0`) and a model-lattice field `ψt y` with
`ψ x = ψt y (pos y x)` for the sites `x ∈ Bc ∪ {y}`; the data hypothesis `DataHyp … (ψt y) (b y)`
at each centre (translation covariance of the renormalization theorem); `ν_j h = b y`;
the regularity premise `‖ψ x‖₂, ‖ψ y‖₂ ≤ B`; and the weight `D y x ≥ ℓ¹(pos y x)`. -/
theorem hpt_of_dataHyp_at_centres [NeZero L] [NeZero N₁]
    (R Bc : Finset (Localization.CTorus d L N₁ m₁ k))
    (ψ : Localization.CTorus d L N₁ m₁ k → Fin N → ℂ) (h : Fin N → ℂ) {νj B : ℝ}
    (D : Localization.CTorus d L N₁ m₁ k → Localization.CTorus d L N₁ m₁ k → ℝ)
    (pos : Localization.CTorus d L N₁ m₁ k → Localization.CTorus d L N₁ m₁ k → SmallField.Site d)
    (ψt : Localization.CTorus d L N₁ m₁ k → SmallField.Site d → Spin N)
    (b : Localization.CTorus d L N₁ m₁ k → Spin N) (hN : 1 ≤ N)
    (hdata : ∀ y ∈ R, DataHyp Dom ν σ ε K₂ (ψt y) (b y))
    (hpull : ∀ y ∈ R, ∀ x ∈ Bc, ψ x = ψt y (pos y x)) (hpull0 : ∀ y ∈ R, ψ y = ψt y 0)
    (hbh : ∀ y ∈ R, (νj : ℂ) • h = b y)
    (hBx : ∀ y ∈ R, ∀ x ∈ Bc, nrm2 (ψ x) ≤ B) (hBy : ∀ y ∈ R, nrm2 (ψ y) ≤ B)
    (hD : ∀ y ∈ R, ∀ x ∈ Bc, l1Dist (pos y x) 0 ≤ D y x)
    (hη : σ ^ 2 * (Real.sqrt N * ε) ≤ 1 / 2) (hν0 : 0 ≤ ν) (hνσ : ν ≤ σ ^ 2) (hσ0 : 0 ≤ σ)
    (hσ1 : σ ≤ 1) (hε0 : 0 ≤ ε) :
    ∀ y ∈ R, ∀ x ∈ Bc,
      ‖(νj : ℂ) * (dot h (Def7v2.unitDirC (ψ x)) - dot h (Def7v2.unitDirC (ψ y)))‖ ≤
        sourceConstC B * (D y x ^ 2 + D y x) * σ ^ 3 * (Real.sqrt N * ε) ^ 2 := by
  intro y hy x hx
  have h1 := pointwise_bound_of_unifBound (B := B) (hdata y hy) hN (hbh y hy) (pos y x)
    (by rw [← hpull y hy x hx]; exact hBx y hy x hx) (by rw [← hpull0 y hy]; exact hBy y hy)
    (hD y hy x hx) hη hν0 hνσ hσ0 hσ1 hε0
  rwa [← hpull y hy x hx, ← hpull0 y hy] at h1

end Torus

/-! ### (T6) Non-vacuity: a slowly rotating real unit field -/

/-- The real unit field rotating in the plane `(e_{i₀}, e_{i₁})` with angle `t x_{μ₀}`. -/
noncomputable def rotField (i₀ i₁ : Fin N) (μ₀ : Fin d) (t : ℝ) (x : SmallField.Site d) : Spin N :=
  fun i => if i = i₀ then ((Real.cos (t * (x μ₀ : ℝ)) : ℝ) : ℂ)
    else if i = i₁ then ((Real.sin (t * (x μ₀ : ℝ)) : ℝ) : ℂ) else 0

variable {i₀ i₁ : Fin N} {μ₀ : Fin d} {t : ℝ}

theorem rotField_norm_le (x : SmallField.Site d) : ‖rotField i₀ i₁ μ₀ t x‖ ≤ 1 := by
  refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun i => ?_
  unfold rotField
  split_ifs
  · rw [Complex.norm_real, Real.norm_eq_abs]; exact Real.abs_cos_le_one _
  · rw [Complex.norm_real, Real.norm_eq_abs]; exact Real.abs_sin_le_one _
  · simp

theorem rotField_sub_norm_le (x y : SmallField.Site d) :
    ‖rotField i₀ i₁ μ₀ t x - rotField i₀ i₁ μ₀ t y‖ ≤ |t| * |((x μ₀ : ℝ) - (y μ₀ : ℝ))| := by
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
  have e : |t| * |((x μ₀ : ℝ) - (y μ₀ : ℝ))| = |t * (x μ₀ : ℝ) - t * (y μ₀ : ℝ)| := by
    rw [← mul_sub, abs_mul]
  rw [e]
  simp only [rotField, Pi.sub_apply]
  split_ifs
  · rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]; exact Real.abs_cos_sub_cos_le _ _
  · rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]; exact Real.abs_sin_sub_sin_le _ _
  · simp

theorem rotField_real (x : SmallField.Site d) (i : Fin N) : (rotField i₀ i₁ μ₀ t x i).im = 0 := by
  unfold rotField; split_ifs <;> simp only [Complex.ofReal_im, Complex.zero_im]

theorem dot_rotField (hne : i₀ ≠ i₁) (x : SmallField.Site d) :
    dot (rotField i₀ i₁ μ₀ t x) (rotField i₀ i₁ μ₀ t x) = 1 := by
  unfold dot
  rw [Finset.sum_eq_add i₀ i₁ hne]
  · simp only [rotField, ite_true, hne.symm, ite_false]
    rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, ← Complex.ofReal_add]
    simp [← sq]
  · intro c _ hc; simp [rotField, hc.1, hc.2]
  · simp
  · simp

/-- **(T6)** The rotating field satisfies `DataHyp` on the data domain `univ`, with `b = ν ψ 0`,
for `0 ≤ σ ε`-slow angle `|t| ≤ σ ε`, `σ² ε ≥ 0`, `K₂ ≥ 4`. -/
theorem nonempty_dataHyp_rotating (hne : i₀ ≠ i₁) (ν σ ε K₂ : ℝ) (hε : 0 ≤ ε) (hK₂ : 4 ≤ K₂)
    (ht : |t| ≤ σ * ε) :
    DataHyp (Set.univ : Set ((SmallField.Site d → Spin N) × Spin N)) ν σ ε K₂
      (rotField i₀ i₁ μ₀ t) ((ν : ℂ) • rotField i₀ i₁ μ₀ t 0) := by
  have hσε : 0 ≤ σ * ε := (abs_nonneg t).trans ht
  have hnn : 0 ≤ σ ^ 2 * ε := by nlinarith [sq_nonneg σ]
  refine ⟨by linarith, fun x => ?_, ?_, fun x μ => ?_, ?_, fun x μ μ' => ?_, trivial, trivial⟩
  · rw [dot_rotField hne]; simpa using hnn
  · exact (rotField_norm_le 0).trans (by norm_num)
  · refine (rotField_sub_norm_le _ _).trans ?_
    have : |((((x + Pi.single μ 1 : SmallField.Site d) μ₀ : ℤ)) : ℝ) - ((x μ₀ : ℤ) : ℝ)| ≤ 1 := by
      by_cases h : μ = μ₀
      · subst h; simp
      · simp [Ne.symm h]
    exact (mul_le_mul_of_nonneg_left this (abs_nonneg _)).trans (by linarith)
  · simpa using hnn
  · have := fun z => rotField_norm_le (i₀ := i₀) (i₁ := i₁) (μ₀ := μ₀) (t := t) z
    set a := rotField i₀ i₁ μ₀ t (x + Pi.single μ 1 + Pi.single μ' 1)
    set b' := rotField i₀ i₁ μ₀ t (x + Pi.single μ 1)
    set c := rotField i₀ i₁ μ₀ t (x + Pi.single μ' 1)
    set e := rotField i₀ i₁ μ₀ t x
    have h1 := norm_add_le (a - b' - c) e
    have h2 := norm_sub_le (a - b') c
    have h3 := norm_sub_le a b'
    have ha : ‖a‖ ≤ 1 := rotField_norm_le _
    have hb : ‖b'‖ ≤ 1 := rotField_norm_le _
    have hc : ‖c‖ ≤ 1 := rotField_norm_le _
    have he : ‖e‖ ≤ 1 := rotField_norm_le _
    linarith


/-- The field of `nonempty_dataHyp_rotating` is non-constant when `0 < t < π`. -/
theorem rotField_ne (hne : i₀ ≠ i₁) (ht0 : 0 < t) (ht1 : t ≤ 1) :
    rotField i₀ i₁ μ₀ t (Pi.single μ₀ 1) ≠ rotField i₀ i₁ μ₀ t 0 := by
  intro h
  have := congrFun h i₁
  simp only [rotField, ite_true, hne.symm, ite_false] at this
  simp at this
  have hs : 0 < Real.sin t := Real.sin_pos_of_pos_of_lt_pi ht0 (by linarith [Real.pi_gt_three])
  exact hs.ne' (by exact_mod_cast this)

/-- **(T6)** The bridge applies to the rotating field (`h = ψ 0`, `ν_j = ν`, `D = ℓ¹`). -/
theorem rotating_pointwise_bound (hne : i₀ ≠ i₁) (hN : 1 ≤ N) (ν σ ε K₂ : ℝ) (hε : 0 ≤ ε)
    (hK₂ : 4 ≤ K₂) (ht : |t| ≤ σ * ε) (hη : σ ^ 2 * (Real.sqrt N * ε) ≤ 1 / 2) (hν0 : 0 ≤ ν)
    (hνσ : ν ≤ σ ^ 2) (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1) (x : SmallField.Site d) :
    ‖(ν : ℂ) * (dot (rotField i₀ i₁ μ₀ t 0) (Def7v2.unitDirC (rotField i₀ i₁ μ₀ t x)) -
        dot (rotField i₀ i₁ μ₀ t 0) (Def7v2.unitDirC (rotField i₀ i₁ μ₀ t 0)))‖ ≤
      sourceConstC (3 / 2) * (l1Dist x 0 ^ 2 + l1Dist x 0) * σ ^ 3 * (Real.sqrt N * ε) ^ 2 :=
  pointwise_bound_of_real (nonempty_dataHyp_rotating (d := d) (μ₀ := μ₀) hne ν σ ε K₂ hε hK₂ ht)
    hN rfl (fun x i => rotField_real x i) x le_rfl hη hν0 hνσ hσ0 hσ1 hε

end Balaban.LargeField.RegionalDataBridge
