/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Correlations.Clauses
public import Balaban.Correlations.KF0Cauchy
public import Balaban.Model.Analytic

/-!
# `KF0RootFPartial`: the clauses of Root-F with scale witness `k_f = 0`, from a one-scale input

**Status: CONDITIONAL.**  Every theorem of this file whose name contains `of_oneScaleInput` assumes
the *one-scale input* `KF0OneScaleInput` of `notes/phase1/KF0.md`: local analytic functions
`p_ℓ(X; g)` for connected unions `X` of blocks of side `s = M L`, with an exponential identity for
`Z(g)/Z(0)`.  That input is **not proved** (its main missing estimate is `CompleteHeavyLocality`
of the note).  Nothing here proves the frozen root `Balaban.logPartition_multiscale`, not even
on the sub-range `ν ∈ [7/(8 L²), 1]`: the frozen root needs every `ν ∈ (0, 1]`, and for
`ν < 7/(8 L²)` the witness `k_f = 0` is not admissible.  The frozen root is not imported; the
clause copies of `Balaban/Correlations/Clauses.lean` are used.

## What is proved

From the one-scale input (hypotheses (0)–(v) below) and the model-independent lemmas of
`KF0Cauchy.lean` the file proves, for `T_1(x, X; g)_i = ∫₀¹ ∂_{g_i(x)} p_ℓ(X; t g) dt` when
`x ∈ X` and `X` is an `s`-block polymer (`kf0Term`, zero otherwise and for `j ≠ 1`):

* `log (Z(g)/Z(0)) = ⟨g, h⟩ + ∑_X [p_ℓ(X; g) − p_ℓ(X; 0)]` on `∑|g| < 1`
  (`log_partition_eq_of_exp`; `Re (Z(g)/Z(0)) > 0` there is the landed
  `Balaban.re_partitionFunction_div_pos`, the exponential identity and the vanishing at `0` fix
  the branch);
* every clause of `RootFTorusClauses … 0` and `RootFAgreement … 0`, and the scale clause
  `1^0 · √ν ≤ L`, `1/2 ≤ L^1 · √ν` for `7/(8L²) ≤ ν ≤ 1`.

## The hypotheses of the one-scale input (fixed `d N L M β ν h κ`)

For every `ℓ` with `[NeZero ℓ]` and `M * L ∣ ℓ`, with `s = M L`, `U = {g | ∑∑ ‖g y i‖ < 1}`:

* (0) support: `p ℓ X = 0` unless `IsPolymer d ℓ (M * L) X`;
* (i) analyticity: `AnalyticOnNhd ℂ (p ℓ X) U` for every finite `X`;
* (ii) locality: `p ℓ X g = p ℓ X g'` whenever `g = g'` on `X`;
* (iii) bound: `‖p ℓ X g‖ ≤ B · exp(−κ |X| / s^d)` on `U`;
* (iv) exponential identity: on `U`,
  `Z(g)/Z(0) = exp(⟨g, h⟩ + ∑_X [p ℓ X g − p ℓ X 0])`;
and across tori
* (v) agreement: for admissible `ℓ, ℓ'` and `A ⊂ ℤ^d` in the box `4|y_μ| < min(ℓ, ℓ')`,
  `a ∈ A`: `p ℓ (image A) (g ∘ val) = p ℓ' (image A) (g ∘ val')` for every `g`
  (the form of `RootFAgreement`; for all `g` and not only on `U`).

Hypotheses (ii) and (v) are asked for all sources `g`, not only on `U`, because the clauses of
Root-F (locality, agreement) are statements about all sources; a provider can extend `p` by zero
outside `U` consistently (the functions of the provider depend on `g|_X` only).

## Clause table (T6): frozen root ↔ `Clauses.lean` copy ↔ proved here from

The frozen statement `Balaban.logPartition_multiscale` and `Balaban.Correlations.RootFStatement`
were compared clause by clause; they are textually identical (same quantifier order, same
exponents, same sums; `RootFTorusClauses` is the five torus clauses, `RootFAgreement` the last).

| frozen clause | copy | proved from |
| --- | --- | --- |
| `T = 0` unless `j ∈ [1,k_f+1]`, `x ∈ X`, `IsPolymer d ℓ (M L^j) X` | `RootFTorusClauses` 1 | definition of `kf0Term` |
| locality in `g|_X` | `RootFTorusClauses` 2 | (ii), `kf0Deriv_congr` |
| analytic on `∑|g| < 1` | `RootFTorusClauses` 3 | (i), (iii), `analyticOnNhd_kf0Deriv` |
| `‖T‖ ≤ c₉ L^{−j((d−2)/2+δ)} e^{−κ|X|/(ML^j)^d}` on `∑|g| ≤ 1/2` | `RootFTorusClauses` 4 | (iii), `norm_kf0Deriv_le`, and `4√N B ≤ c₉ L^{−((d−2)/2+δ)}` |
| `log (Z(g)/Z(0)) = ⟨g,h⟩ + ∑ ∑ ∑ ∑ g T` on `∑|g| < 1` | `RootFTorusClauses` 5 | (0), (i), (iv), `sub_zero_eq_sum_kf0Deriv`, `log_partition_eq_of_exp` |
| agreement of `T` on the quarter box | `RootFAgreement` | (0), (v) |
| scale `L^{k_f}√ν ≤ L`, `1/2 ≤ L^{k_f+1}√ν` | `RootFStatement` | `k_f = 0`, `7/(8L²) ≤ ν ≤ 1` |

The sup norm on `Fin N → ℂ` gives `‖T_1‖ ≤ 4 B e^{…}`; the factor `√N ≥ 1` of the note is not
needed, and the provider hypothesis `4 √N B ≤ c₉ L^{−((d−2)/2+δ)}` (with `N ≥ 1`) implies it.

## Non-vacuity

The Cauchy / fundamental-theorem lemmas are exercised on explicit functions in
`kf0Deriv_linear` below.  The conditional theorem itself has no instance: its hypothesis is the
open one-scale input.
-/

@[expose] public section

namespace Balaban.Correlations

open Balaban Set

/-! ### The terms -/

open Classical in
/-- The terms of the `k_f = 0` branch: `T_1(x, X; g)_i = ∫₀¹ ∂_{g_i(x)} p_ℓ(X; t g) dt` when
`x ∈ X` and `X` is a polymer of block side `M L`; zero otherwise, and `T_j = 0` for `j ≠ 1`. -/
noncomputable def kf0Term {d N : ℕ} (M L : ℕ)
    (p : (ℓ : ℕ) → Finset (Torus d ℓ) → (Torus d ℓ → Fin N → ℂ) → ℂ) : RootFFamily d N :=
  fun ℓ j x X g =>
    if _hℓ : NeZero ℓ then
      (if j = 1 ∧ x ∈ X ∧ IsPolymer d ℓ (M * L) X then fun i => kf0Deriv (p ℓ X) g x i else 0)
    else 0

section Terms

variable {d N : ℕ} {M L : ℕ} {p : (ℓ : ℕ) → Finset (Torus d ℓ) → (Torus d ℓ → Fin N → ℂ) → ℂ}
  {ℓ : ℕ} [NeZero ℓ]

open Classical in
theorem kf0Term_apply (j : ℕ) (x : Torus d ℓ) (X : Finset (Torus d ℓ))
    (g : Torus d ℓ → Fin N → ℂ) :
    kf0Term M L p ℓ j x X g =
      if j = 1 ∧ x ∈ X ∧ IsPolymer d ℓ (M * L) X then fun i => kf0Deriv (p ℓ X) g x i else 0 := by
  unfold kf0Term
  split
  · rfl
  · rename_i hne
    exact (hne inferInstance).elim

/-- For `j = 1` the term is the Cauchy integral for every `x` and every finite `X`. -/
theorem kf0Term_one (hsupp : ∀ X : Finset (Torus d ℓ), ¬ IsPolymer d ℓ (M * L) X →
      ∀ g, p ℓ X g = 0)
    (hloc : ∀ (X : Finset (Torus d ℓ)) (g g' : Torus d ℓ → Fin N → ℂ),
      (∀ y ∈ X, g y = g' y) → p ℓ X g = p ℓ X g')
    (x : Torus d ℓ) (X : Finset (Torus d ℓ)) (g : Torus d ℓ → Fin N → ℂ) (i : Fin N) :
    kf0Term M L p ℓ 1 x X g i = kf0Deriv (p ℓ X) g x i := by
  rw [kf0Term_apply]
  by_cases hx : x ∈ X
  · by_cases hP : IsPolymer d ℓ (M * L) X
    · simp [hx, hP]
    · have h0 : p ℓ X = fun _ => 0 := funext (hsupp X hP)
      have : kf0Deriv (p ℓ X) g x i = 0 := by
        rw [h0]; simp [kf0Deriv]
      simp [hx, hP, this]
  · have hc : ¬ (1 = 1 ∧ x ∈ X ∧ IsPolymer d ℓ (M * L) X) := fun h => hx h.2.1
    split_ifs
    exact (kf0Deriv_eq_zero (hloc X) g hx i).symm

end Terms

/-! ### The principal logarithm -/

section Log

variable {d N : ℕ} [NeZero N] {β ν : ℝ} {h : EuclideanSpace ℝ (Fin N)}
  {p : (ℓ : ℕ) → Finset (Torus d ℓ) → (Torus d ℓ → Fin N → ℂ) → ℂ}
  {ℓ : ℕ} [NeZero ℓ]

/-- Under the exponential identity (iv) the principal logarithm of `Z(g)/Z(0)` is the exponent, on
the whole source ball.  (`Re (Z(g)/Z(0)) > 0` there is `Balaban.re_partitionFunction_div_pos`.) -/
theorem log_partition_eq_of_exp
    (hana : ∀ X : Finset (Torus d ℓ), AnalyticOnNhd ℂ (p ℓ X) (ball1 (Torus d ℓ) (Fin N)))
    (hexp : ∀ g : Torus d ℓ → Fin N → ℂ, l1 g < 1 →
      partitionFunction d N ℓ β ν h g / partitionFunction d N ℓ β ν h 0 =
        Complex.exp (∑ x, ∑ i, g x i * (h i : ℂ)
          + ∑ X : Finset (Torus d ℓ), (p ℓ X g - p ℓ X 0)))
    {g : Torus d ℓ → Fin N → ℂ} (hg : l1 g < 1) :
    Complex.log (partitionFunction d N ℓ β ν h g / partitionFunction d N ℓ β ν h 0) =
      ∑ x, ∑ i, g x i * (h i : ℂ) + ∑ X : Finset (Torus d ℓ), (p ℓ X g - p ℓ X 0) := by
  have hb : ball1 (Torus d ℓ) (Fin N) = sourceBall d N ℓ := rfl
  set S : (Torus d ℓ → Fin N → ℂ) → ℂ := fun g => ∑ x, ∑ i, g x i * (h i : ℂ)
    + ∑ X : Finset (Torus d ℓ), (p ℓ X g - p ℓ X 0) with hS
  set D : (Torus d ℓ → Fin N → ℂ) → ℂ := fun g =>
    Complex.log (partitionFunction d N ℓ β ν h g / partitionFunction d N ℓ β ν h 0) - S g
    with hD
  have hSd : DifferentiableOn ℂ S (sourceBall d N ℓ) := by
    refine DifferentiableOn.add (Differentiable.differentiableOn (𝕜 := ℂ)
      (f := fun g : Torus d ℓ → Fin N → ℂ => ∑ x, ∑ i, g x i * (h i : ℂ)) (by fun_prop)) ?_
    apply DifferentiableOn.fun_sum
    intro X _
    exact ((hana X).differentiableOn).sub_const _
  have hDd : DifferentiableOn ℂ D (sourceBall d N ℓ) :=
    (differentiableOn_logPartition (d := d) (N := N) (ℓ := ℓ) β ν h).sub hSd
  have hexp1 : ∀ g' ∈ sourceBall d N ℓ, Complex.exp (D g') = 1 := by
    intro g' hg'
    have hne := (partitionFunction_div_mem_slitPlane β ν h hg')
    have hne' := Complex.slitPlane_ne_zero hne
    simp only [hD]
    rw [Complex.exp_sub, Complex.exp_log hne', hS]
    simp only
    rw [← hexp g' hg']
    exact div_self hne'
  have hder : ∀ g' ∈ sourceBall d N ℓ, fderiv ℂ D g' = 0 := by
    intro g' hg'
    have hD1 : HasFDerivAt D (fderiv ℂ D g') g' :=
      (hDd.differentiableAt (isOpen_sourceBall.mem_nhds hg')).hasFDerivAt
    have h2 := hD1.cexp
    have h3 : HasFDerivAt (fun _ : Torus d ℓ → Fin N → ℂ => (1 : ℂ))
        (Complex.exp (D g') • fderiv ℂ D g') g' := by
      refine h2.congr_of_eventuallyEq ?_
      filter_upwards [isOpen_sourceBall.mem_nhds hg'] with x hx
      exact (hexp1 x hx).symm
    have h4 := (hasFDerivAt_const (1 : ℂ) g').unique h3
    have h6 : Complex.exp (D g') • fderiv ℂ D g' = 0 := h4.symm
    exact (smul_eq_zero.1 h6).resolve_left (Complex.exp_ne_zero _)
  have hconst := (convex_ball1 (α := Torus d ℓ) (β := Fin N)).is_const_of_fderivWithin_eq_zero
    (𝕜 := ℂ) (f := D) hDd (fun x hx => by
      rw [fderivWithin_of_isOpen isOpen_ball1 hx]; exact hder x hx) hg
    (zero_mem_ball1)
  have hD0 : D 0 = 0 := by
    simp only [hD, hS]
    have hZ := partitionFunction_zero_ne_zero (d := d) (N := N) (ℓ := ℓ) β ν h
    simp [div_self hZ]
  have : D g = 0 := hconst.trans hD0
  simp only [hD] at this
  exact sub_eq_zero.1 this

end Log

/-! ### The clauses on one torus -/

section Clauses

variable {d N L M : ℕ} {β ν κ c₉ δ B : ℝ} {h : EuclideanSpace ℝ (Fin N)}
  {p : (ℓ : ℕ) → Finset (Torus d ℓ) → (Torus d ℓ → Fin N → ℂ) → ℂ} {ℓ : ℕ} [NeZero ℓ]

/-- The five clauses of Root-F on one admissible torus, with `k_f = 0`, for the terms `kf0Term`,
from the one-scale hypotheses (0)–(iv) on that torus and `4 B ≤ c₉ L^{−((d−2)/2+δ)}`. -/
theorem rootFTorusClauses_kf0_of_oneScaleInput [NeZero N] (hc₉ : 0 < c₉)
    (hB : 4 * B ≤ c₉ * (L : ℝ) ^ (-(((d : ℝ) - 2) / 2 + δ)))
    (hsupp : ∀ X : Finset (Torus d ℓ), ¬ IsPolymer d ℓ (M * L) X → ∀ g, p ℓ X g = 0)
    (hana : ∀ X : Finset (Torus d ℓ), AnalyticOnNhd ℂ (p ℓ X) {g | ∑ y, ∑ i, ‖g y i‖ < 1})
    (hloc : ∀ (X : Finset (Torus d ℓ)) (g g' : Torus d ℓ → Fin N → ℂ),
      (∀ y ∈ X, g y = g' y) → p ℓ X g = p ℓ X g')
    (hbd : ∀ (X : Finset (Torus d ℓ)) (g : Torus d ℓ → Fin N → ℂ), ∑ y, ∑ i, ‖g y i‖ < 1 →
      ‖p ℓ X g‖ ≤ B * Real.exp (-κ * (X.card : ℝ) / ((M : ℝ) * (L : ℝ)) ^ d))
    (hexp : ∀ g : Torus d ℓ → Fin N → ℂ, ∑ y, ∑ i, ‖g y i‖ < 1 →
      partitionFunction d N ℓ β ν h g / partitionFunction d N ℓ β ν h 0 =
        Complex.exp (∑ x, ∑ i, g x i * (h i : ℂ)
          + ∑ X : Finset (Torus d ℓ), (p ℓ X g - p ℓ X 0))) :
    RootFTorusClauses d N L M β ν h 0 κ c₉ δ (kf0Term M L p) ℓ := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro j x X hnot
    funext g
    rw [kf0Term_apply]
    have hc : ¬ (j = 1 ∧ x ∈ X ∧ IsPolymer d ℓ (M * L) X) := by
      rintro ⟨rfl, hx, hP⟩
      exact hnot ⟨Finset.mem_Icc.2 ⟨le_rfl, le_rfl⟩, hx, by simpa using hP⟩
    split_ifs
    rfl
  · intro j x X g g' hgg
    rw [kf0Term_apply, kf0Term_apply]
    split_ifs
    · funext i
      exact kf0Deriv_congr (hloc X) hgg x i
    · rfl
  · intro j x X
    by_cases hcnd : j = 1 ∧ x ∈ X ∧ IsPolymer d ℓ (M * L) X
    · have : kf0Term M L p ℓ j x X = fun g i => kf0Deriv (p ℓ X) g x i := by
        funext g
        rw [kf0Term_apply]
        simp [hcnd]
      rw [this]
      exact AnalyticOnNhd.pi fun i => analyticOnNhd_kf0Deriv (α := Torus d ℓ) (β := Fin N)
        (F := p ℓ X) (hana X) (B := B * Real.exp (-κ * (X.card : ℝ) / ((M : ℝ) * (L : ℝ)) ^ d))
        (fun g hg => hbd X g hg) x i
    · have : kf0Term M L p ℓ j x X = fun _ => 0 := by
        funext g
        rw [kf0Term_apply]
        simp [hcnd]
      rw [this]
      exact analyticOnNhd_const
  · intro j hj x X g hg
    have hj1 : j = 1 := by
      have := Finset.mem_Icc.1 hj
      omega
    subst hj1
    simp only [Nat.cast_one, one_mul, pow_one]
    have hE := Real.exp_pos (-κ * (X.card : ℝ) / ((M : ℝ) * (L : ℝ)) ^ d)
    have hR : 0 ≤ c₉ * (L : ℝ) ^ (-(((d : ℝ) - 2) / 2 + δ)) *
        Real.exp (-κ * (X.card : ℝ) / ((M : ℝ) * (L : ℝ)) ^ d) := by
      have hLpos : 0 ≤ (L : ℝ) ^ (-(((d : ℝ) - 2) / 2 + δ)) := Real.rpow_nonneg (Nat.cast_nonneg _) _
      positivity
    rw [kf0Term_apply]
    split_ifs with hcnd
    · have h0 : 0 ≤ 4 * (B * Real.exp (-κ * (X.card : ℝ) / ((M : ℝ) * (L : ℝ)) ^ d)) := by
        have := (norm_nonneg _).trans (hbd X 0 (by simp))
        linarith
      calc ‖fun i => kf0Deriv (p ℓ X) g x i‖
          ≤ 4 * (B * Real.exp (-κ * (X.card : ℝ) / ((M : ℝ) * (L : ℝ)) ^ d)) := by
            refine (pi_norm_le_iff_of_nonneg h0).2 fun i => ?_
            exact norm_kf0Deriv_le (α := Torus d ℓ) (β := Fin N) (F := p ℓ X) (hana X)
              (B := B * Real.exp (-κ * (X.card : ℝ) / ((M : ℝ) * (L : ℝ)) ^ d))
              (fun g hg => hbd X g hg) hg x i
        _ ≤ _ := by nlinarith
    · simpa using hR
  · intro g hg
    have hlog := log_partition_eq_of_exp (β := β) (ν := ν) (h := h) (p := p) hana hexp hg
    rw [hlog]
    have hIcc : Finset.Icc 1 (0 + 1) = {1} := rfl
    rw [hIcc, Finset.sum_singleton]
    congr 1
    refine Eq.trans ?_ Finset.sum_comm
    refine Finset.sum_congr rfl fun X _ => ?_
    have hF := sub_zero_eq_sum_kf0Deriv (α := Torus d ℓ) (β := Fin N) (F := p ℓ X) (hana X)
      (g := g) hg
    rw [hF]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun i _ => ?_
    rw [kf0Term_one hsupp hloc]

end Clauses

/-! ### Agreement across tori -/

section Agreement

variable {d N L M : ℕ}
  {p : (ℓ : ℕ) → Finset (Torus d ℓ) → (Torus d ℓ → Fin N → ℂ) → ℂ}

theorem valMinAbs_intCast_of_box {ℓ : ℕ} [NeZero ℓ] (n : ℤ) (hn : 4 * |n| < (ℓ : ℤ)) :
    ZMod.valMinAbs (n : ZMod ℓ) = n := by
  rw [ZMod.valMinAbs_spec]
  refine ⟨rfl, ?_, ?_⟩
  · have := neg_abs_le n
    show -(ℓ : ℤ) < n * 2
    omega
  · have := le_abs_self n
    show n * 2 ≤ (ℓ : ℤ)
    omega

/-- For a point `a` of the quarter box, `z ↦ val z` hits `a` exactly at the image of `a`. -/
theorem valMinAbs_eq_iff {ℓ : ℕ} [NeZero ℓ] (a : Fin d → ℤ) (ha : ∀ μ, 4 * |a μ| < (ℓ : ℤ))
    (z : Torus d ℓ) :
    ((fun μ => ZMod.valMinAbs (n := ℓ) (z μ)) = a) ↔ z = fun μ => (a μ : ZMod ℓ) := by
  constructor
  · intro hz
    funext μ
    rw [← ZMod.coe_valMinAbs (z μ), congrFun hz μ]
  · rintro rfl
    funext μ
    exact valMinAbs_intCast_of_box _ (ha μ)

theorem shift_eq {ℓ : ℕ} [NeZero ℓ] (a : Fin d → ℤ) (ha : ∀ μ, 4 * |a μ| < (ℓ : ℤ))
    (g : (Fin d → ℤ) → Fin N → ℂ) (i : Fin N) (t s : ℂ) :
    (t • (fun z : Torus d ℓ => g fun μ => ZMod.valMinAbs (n := ℓ) (z μ))
        + s • unitSource (fun μ => (a μ : ZMod ℓ)) i) =
      fun z : Torus d ℓ => (t • g + s • unitSource a i) fun μ => ZMod.valMinAbs (n := ℓ) (z μ) := by
  funext z j
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, unitSource, Pi.single_apply,
    valMinAbs_eq_iff a ha z]

/-- Agreement clause of Root-F with `k_f = 0` for `kf0Term`, from (0), (ii) and (v). -/
theorem rootFAgreement_kf0_of_oneScaleInput
    (hsupp : ∀ (ℓ : ℕ) [NeZero ℓ], M * L ∣ ℓ → ∀ X : Finset (Torus d ℓ),
      ¬ IsPolymer d ℓ (M * L) X → ∀ g, p ℓ X g = 0)
    (hloc : ∀ (ℓ : ℕ) [NeZero ℓ], M * L ∣ ℓ → ∀ (X : Finset (Torus d ℓ))
      (g g' : Torus d ℓ → Fin N → ℂ), (∀ y ∈ X, g y = g' y) → p ℓ X g = p ℓ X g')
    (hagr : ∀ (ℓ ℓ' : ℕ) [NeZero ℓ] [NeZero ℓ'], M * L ∣ ℓ → M * L ∣ ℓ' →
      ∀ (a : Fin d → ℤ) (A : Finset (Fin d → ℤ)) (g : (Fin d → ℤ) → Fin N → ℂ),
        a ∈ A → (∀ y ∈ A, ∀ μ, 4 * |y μ| < (ℓ : ℤ) ∧ 4 * |y μ| < (ℓ' : ℤ)) →
        p ℓ (A.image fun y μ => (y μ : ZMod ℓ))
            (fun z => g fun μ => ZMod.valMinAbs (n := ℓ) (z μ)) =
          p ℓ' (A.image fun y μ => (y μ : ZMod ℓ'))
            (fun z => g fun μ => ZMod.valMinAbs (n := ℓ') (z μ))) :
    RootFAgreement d N L M 0 (kf0Term M L p) := by
  intro ℓ ℓ' _ _ hℓ hℓ' j a A g ha hbox
  have hℓ1 : M * L ∣ ℓ := by simpa using hℓ
  have hℓ1' : M * L ∣ ℓ' := by simpa using hℓ'
  by_cases hj : j = 1
  · subst hj
    funext i
    rw [kf0Term_one (hsupp ℓ hℓ1) (hloc ℓ hℓ1), kf0Term_one (hsupp ℓ' hℓ1') (hloc ℓ' hℓ1')]
    unfold kf0Deriv
    refine intervalIntegral.integral_congr fun t _ => ?_
    have haℓ : ∀ μ, 4 * |a μ| < (ℓ : ℤ) := fun μ => (hbox a ha μ).1
    have haℓ' : ∀ μ, 4 * |a μ| < (ℓ' : ℤ) := fun μ => (hbox a ha μ).2
    have e1 := fun s : ℂ => shift_eq (N := N) a haℓ g i (t : ℂ) s
    have e2 := fun s : ℂ => shift_eq (N := N) a haℓ' g i (t : ℂ) s
    congr 1
    funext s
    rw [e1 s, e2 s]
    exact hagr ℓ ℓ' hℓ1 hℓ1' a A (fun y => ((t : ℂ) • g + s • unitSource a i) y) ha hbox
  · rw [kf0Term_apply, kf0Term_apply]
    simp [hj]

end Agreement

/-! ### The partial theorem -/

/-- **Conditional.**  Root-F with the scale witness `k_f = 0`, on the range
`ν ∈ [7/(8 L²), 1]`, from the one-scale input (hypothesis `hprov`, which is the open statement
`KF0OneScaleInput` of `notes/phase1/KF0.md`; it is not proved).  The input provides, for every
`κ, c₉ > 0`, scales `L ≥ 2`, `M ≥ 1` and `β₀`, and for every `β ≥ β₀`, `ν ∈ [7/(8L²), 1]` and unit
`h`, functions `p` and a number `B` with `4 √N B ≤ c₉ L^{−((d−2)/2+1/8)}` and the hypotheses
(0)–(iv) on every torus of side divisible by `M L`, and (v) across tori.  This does not prove the
frozen root, not even on the sub-range: the root needs all `ν ∈ (0, 1]`.  The condition
`3 ≤ d` of the frozen root is not used here. -/
theorem rootF_kf0_partial_of_oneScaleInput (d N : ℕ) (hN : 2 ≤ N)
    (hprov : ∀ κ : ℝ, 0 < κ → ∀ c₉ : ℝ, 0 < c₉ →
      ∃ L M : ℕ, 2 ≤ L ∧ 1 ≤ M ∧ ∃ β₀ : ℝ, ∀ β : ℝ, β₀ ≤ β →
      ∀ ν : ℝ, 7 / (8 * (L : ℝ) ^ 2) ≤ ν → ν ≤ 1 → ∀ h : EuclideanSpace ℝ (Fin N), ‖h‖ = 1 →
      ∃ (p : (ℓ : ℕ) → Finset (Torus d ℓ) → (Torus d ℓ → Fin N → ℂ) → ℂ) (B : ℝ),
        4 * Real.sqrt N * B ≤ c₉ * (L : ℝ) ^ (-(((d : ℝ) - 2) / 2 + 1 / 8)) ∧
        (∀ (ℓ : ℕ) [NeZero ℓ], M * L ∣ ℓ →
          (∀ X : Finset (Torus d ℓ), ¬ IsPolymer d ℓ (M * L) X → ∀ g, p ℓ X g = 0) ∧
          (∀ X : Finset (Torus d ℓ),
            AnalyticOnNhd ℂ (p ℓ X) {g | ∑ y, ∑ i, ‖g y i‖ < 1}) ∧
          (∀ (X : Finset (Torus d ℓ)) (g g' : Torus d ℓ → Fin N → ℂ),
            (∀ y ∈ X, g y = g' y) → p ℓ X g = p ℓ X g') ∧
          (∀ (X : Finset (Torus d ℓ)) (g : Torus d ℓ → Fin N → ℂ), ∑ y, ∑ i, ‖g y i‖ < 1 →
            ‖p ℓ X g‖ ≤ B * Real.exp (-κ * (X.card : ℝ) / ((M : ℝ) * (L : ℝ)) ^ d)) ∧
          (∀ g : Torus d ℓ → Fin N → ℂ, ∑ y, ∑ i, ‖g y i‖ < 1 →
            partitionFunction d N ℓ β ν h g / partitionFunction d N ℓ β ν h 0 =
              Complex.exp (∑ x, ∑ i, g x i * (h i : ℂ)
                + ∑ X : Finset (Torus d ℓ), (p ℓ X g - p ℓ X 0)))) ∧
        (∀ (ℓ ℓ' : ℕ) [NeZero ℓ] [NeZero ℓ'], M * L ∣ ℓ → M * L ∣ ℓ' →
          ∀ (a : Fin d → ℤ) (A : Finset (Fin d → ℤ)) (g : (Fin d → ℤ) → Fin N → ℂ),
            a ∈ A → (∀ y ∈ A, ∀ μ, 4 * |y μ| < (ℓ : ℤ) ∧ 4 * |y μ| < (ℓ' : ℤ)) →
            p ℓ (A.image fun y μ => (y μ : ZMod ℓ))
                (fun z => g fun μ => ZMod.valMinAbs (n := ℓ) (z μ)) =
              p ℓ' (A.image fun y μ => (y μ : ZMod ℓ'))
                (fun z => g fun μ => ZMod.valMinAbs (n := ℓ') (z μ)))) :
    ∃ δ : ℝ, 0 < δ ∧
    ∀ κ : ℝ, 0 < κ → ∀ c₉ : ℝ, 0 < c₉ →
    ∃ L M : ℕ, 2 ≤ L ∧ 1 ≤ M ∧ ∃ β₀ : ℝ, ∀ β : ℝ, β₀ ≤ β →
    ∀ ν : ℝ, 7 / (8 * (L : ℝ) ^ 2) ≤ ν → ν ≤ 1 → ∀ h : EuclideanSpace ℝ (Fin N), ‖h‖ = 1 →
    ∃ kf : ℕ, kf = 0 ∧ (L : ℝ) ^ kf * Real.sqrt ν ≤ L ∧ 1 / 2 ≤ (L : ℝ) ^ (kf + 1) * Real.sqrt ν ∧
    ∃ T : RootFFamily d N, RootFClauses d N L M β ν h kf κ c₉ δ T := by
  have : NeZero N := ⟨by omega⟩
  refine ⟨1 / 8, by norm_num, ?_⟩
  intro κ hκ c₉ hc₉
  obtain ⟨L, M, hL, hM, β₀, hprov'⟩ := hprov κ hκ c₉ hc₉
  refine ⟨L, M, hL, hM, β₀, ?_⟩
  intro β hβ ν hν1 hν2 h hh
  obtain ⟨p, B, hB, hper, hagr⟩ := hprov' β hβ ν hν1 hν2 h hh
  have hLr : (2 : ℝ) ≤ L := by exact_mod_cast hL
  have hν0 : 0 < ν := lt_of_lt_of_le (by positivity) hν1
  refine ⟨0, rfl, ?_, ?_, kf0Term M L p, ?_, ?_⟩
  · have : Real.sqrt ν ≤ 1 := Real.sqrt_le_one.2 hν2
    simp only [pow_zero, one_mul]
    linarith
  · have hs := Real.sq_sqrt hν0.le
    have hs0 := Real.sqrt_nonneg ν
    have h78 : 7 ≤ ν * (8 * (L : ℝ) ^ 2) := (div_le_iff₀ (by positivity)).1 hν1
    simp only [zero_add, pow_one]
    by_contra hcon
    have h1 : (L : ℝ) * Real.sqrt ν < 1 / 2 := not_le.1 hcon
    have h2 : 0 ≤ (L : ℝ) * Real.sqrt ν := by positivity
    nlinarith [mul_self_nonneg (L : ℝ), sq_nonneg (L * Real.sqrt ν)]
  · intro ℓ _ hℓ
    have hℓ1 : M * L ∣ ℓ := by simpa using hℓ
    obtain ⟨hs, ha, hl, hb, he⟩ := hper ℓ hℓ1
    have hB0 : 0 ≤ B := by
      have := (norm_nonneg _).trans (hb ∅ 0 (by simp))
      exact nonneg_of_mul_nonneg_left this (Real.exp_pos _)
    have hsq : (1 : ℝ) ≤ Real.sqrt N := Real.one_le_sqrt.2 (by exact_mod_cast (by omega : 1 ≤ N))
    have hB4 : 4 * B ≤ c₉ * (L : ℝ) ^ (-(((d : ℝ) - 2) / 2 + 1 / 8)) := by nlinarith
    exact rootFTorusClauses_kf0_of_oneScaleInput hc₉ hB4 hs ha hl hb he
  · exact rootFAgreement_kf0_of_oneScaleInput
      (fun ℓ _ hℓ => (hper ℓ hℓ).1) (fun ℓ _ hℓ => (hper ℓ hℓ).2.2.1)
      (fun ℓ ℓ' _ _ hℓ hℓ' => hagr ℓ ℓ' hℓ hℓ')

/-! ### Non-vacuity of the Cauchy lemmas -/

section Example

variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

omit [Fintype α] [Fintype β] in
theorem unitSource_apply (a : α) (b : β) (x : α) (y : β) :
    unitSource a b x y = if x = a ∧ y = b then 1 else 0 := by
  unfold unitSource
  by_cases hx : x = a <;> by_cases hy : y = b <;> simp [hx, hy]

/-- A linear function `F g = ∑ c_{a,b} g_b(a)` has `kf0Deriv F g a b = c_{a,b}`. -/
theorem kf0Deriv_linear (c : α → β → ℂ) (g : α → β → ℂ) (a : α) (b : β) :
    kf0Deriv (fun g' => ∑ x, ∑ y, c x y * g' x y) g a b = c a b := by
  unfold kf0Deriv
  have h : ∀ t : ℝ, deriv (fun s : ℂ =>
      ∑ x, ∑ y, c x y * ((t : ℂ) • g + s • unitSource a b) x y) 0 = c a b := by
    intro t
    have : (fun s : ℂ => ∑ x, ∑ y, c x y * ((t : ℂ) • g + s • unitSource a b) x y) =
        fun s => (∑ x, ∑ y, c x y * ((t : ℂ) * g x y)) + s * c a b := by
      funext s
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, unitSource_apply, mul_add,
        Finset.sum_add_distrib]
      congr 1
      simp [mul_ite, Finset.sum_ite_eq', ite_and]
      ring
    rw [this]
    simp
  rw [intervalIntegral.integral_congr (g := fun _ => c a b) (fun t _ => h t)]
  simp

/-- The fundamental-theorem lemma of `KF0Cauchy` on the linear function:
`F g - F 0 = ∑ g c`. -/
theorem linear_sub_zero (c : α → β → ℂ) (g : α → β → ℂ) (hg : g ∈ ball1 α β) :
    (∑ x, ∑ y, c x y * g x y) - (∑ x, ∑ y, c x y * (0 : α → β → ℂ) x y) =
      ∑ a, ∑ b, g a b * c a b := by
  have hF : AnalyticOnNhd ℂ (fun g' : α → β → ℂ => ∑ x, ∑ y, c x y * g' x y) (ball1 α β) := by
    intro g' _
    apply Finset.analyticAt_fun_sum
    intro x _
    apply Finset.analyticAt_fun_sum
    intro y _
    have hproj : AnalyticAt ℂ (fun g'' : α → β → ℂ => g'' x y) g' :=
      (((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : β => ℂ) y).comp
        (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : α => β → ℂ) x) :
          (α → β → ℂ) →L[ℂ] ℂ).analyticAt g')
    exact analyticAt_const.mul hproj
  have := sub_zero_eq_sum_kf0Deriv hF hg
  simpa [kf0Deriv_linear] using this

end Example

end Balaban.Correlations
