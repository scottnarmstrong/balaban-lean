/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Observables.MarkedCoupled
public import Balaban.Observables.LayerDef
import Mathlib.Analysis.Complex.Schwarz
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Lemma 3.4 (P9 Lemma 2, (2.21)-(2.24)): the Schwarz step, the case split, the resummation

OBSERVABLES.md §3.4.  This file proves the parts of the proof of P9 Lemma 2 that are independent
of the geometry of the domains `Ψ^c_j(X; σ, ε)` of P1:

* `slice_diff_le_inv`, `slice_diff_le_inv_vec`: **the Cauchy step on a slice** (P9 p. 499,
  "by a Cauchy estimate it can be bounded by `(1/r₀) β^{-1/2+ρ₁} ξ^{ρ₀} e^{-κ d_j(X)}`"): if `g` is
  holomorphic on the disc `|t| < r` and bounded by `B` there, and `|g 1| ≤ B`, then
  `|g 1 - g 0| ≤ 2B / r`.  For `r > 1` this is the Schwarz lemma; for `r ≤ 1` it is trivial.
  (Scalar and `ℂ`-inner-product-space valued.)
* `improved_delta_bound`: the **case split** of (2.24): with `D = d_j(X)`, `s = σε`,
  `B = A e^{-κ D}`, the radius `r₀ = Rad / (c (1 + D/(2L)) s)` for `D ≤ D*` (small polymers) and the
  trivial bound `2B` for `D > D*` with `D* = c' / s`, give
  `|g 1 - g 0| ≤ C A s e^{-(κ-1) D}`.  `C` is explicit (`improvedConst`).
* `improved_second_of_first` (**(2.22) from (2.21)**): if for every polymer `X ∋ x` the term
  `M(x, X; ψ, h)` is within `b_X` of its value at a constant unit configuration `(v, v)` (`v` real,
  `v · v = 1`), then, by the normalization (2.1), `|M(x; ψ, h)| ≤ ∑_X b_X`
  (`Mobs_const_zero` is `IsObs.normM`).

**Corrected form of (2.21) (finding).**  P9 prints (2.21) with the subtrahend `M(x, X; h, h)`.  The
proof of P9 delivers `M(x, X; ψ_j, h) - m₁^{(j)}(x, X; 1, 1, 0) ψ̂_j(y)`, with
`m₁^{(j)}(x, X; 1, 1, 0) = M^{(j)}(x, X; e₁, e₁) · e₁`, i.e. the subtrahend is the value at the
constant unit configuration **in the direction `ψ̂_j(y)` of the spin**, `M(x, X; ψ̂_j(y), ψ̂_j(y))`.
These agree only when `ψ̂_j(y) = h`.  The printed form is false per polymer: two polymers `X₁, X₂ ∋ x`
with `M(x, X₁; ψ, h) = -M(x, X₂; ψ, h) = c ψ(x)`, `c = ½ β^{-1/2+ρ₁} ξ^{ρ₀} e^{-κ d}`, satisfy every
clause of `IsObs` that concerns the terms (bound, covariance, locality, `∑_X M(x, X; h, h) = 0`),
but `|M(x, X₁; ψ, h) - M(x, X₁; h, h)| = c |ψ - h| = √2 c` for a constant unit `ψ ⟂ h`, which is
a point of the domain whenever the background mass is zero (the domain places no condition on `h`)
or `ν_j < (σε)²/2`.  (Summed over `X`, (2.22) is true: the leading parts cancel.)  The statements
here use the corrected subtrahend (`ψ` against `(v, v)` for any real unit `v`).
-/

@[expose] public section

namespace Balaban.Observables

open Balaban Balaban.Multiscale Balaban.Localization Balaban.SmallField Balaban.SmallField.Def6
  Metric Finset

/-! ### The Cauchy step on a slice -/

section Slice

/-- **The Cauchy step (scalar).** -/
theorem slice_diff_le_inv {g : ℂ → ℂ} {r B : ℝ} (hr : 0 < r)
    (hg : DifferentiableOn ℂ g (ball 0 r)) (hB : ∀ t, ‖t‖ < r → ‖g t‖ ≤ B)
    (h1 : ‖g 1‖ ≤ B) : ‖g 1 - g 0‖ ≤ 2 * B / r := by
  have hB0 : 0 ≤ B := le_trans (norm_nonneg _) (hB 0 (by simpa using hr))
  by_cases hr1 : 1 < r
  · have h := norm_le_mul_div_of_vanish_zero (f := fun t => g t - g 0) (R := r) (B := 2 * B) hr
      (hg.sub (differentiableOn_const _)) (fun t ht => by
        calc ‖g t - g 0‖ ≤ ‖g t‖ + ‖g 0‖ := norm_sub_le _ _
          _ ≤ B + B := add_le_add (hB t ht) (hB 0 (by simpa using hr))
          _ = 2 * B := by ring) (by simp) (σ := 1) (by simpa using hr1)
    simpa using h
  · push Not at hr1
    calc ‖g 1 - g 0‖ ≤ ‖g 1‖ + ‖g 0‖ := norm_sub_le _ _
      _ ≤ B + B := add_le_add h1 (hB 0 (by simpa using hr))
      _ = 2 * B := by ring
      _ ≤ 2 * B / r := by
          rw [le_div_iff₀ hr]; nlinarith

/-- **The Cauchy step (valued in a complex inner product space).** -/
theorem slice_diff_le_inv_vec {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {G : ℂ → E} {r B : ℝ} (hr : 0 < r) (hG : DifferentiableOn ℂ G (ball 0 r))
    (hB : ∀ t, ‖t‖ < r → ‖G t‖ ≤ B) (h1 : ‖G 1‖ ≤ B) : ‖G 1 - G 0‖ ≤ 2 * B / r := by
  set w : E := G 1 - G 0 with hw
  by_cases hw0 : w = 0
  · rw [hw0, norm_zero]
    have hB0 : 0 ≤ B := le_trans (norm_nonneg _) (hB 0 (by simpa using hr))
    positivity
  have hwp : 0 < ‖w‖ := norm_pos_iff.2 hw0
  have hB0 : 0 ≤ B := le_trans (norm_nonneg _) (hB 0 (by simpa using hr))
  -- the scalar function `t ↦ ⟪w, G t⟫`
  set g : ℂ → ℂ := fun t => inner ℂ w (G t) with hg
  have hgd : DifferentiableOn ℂ g (ball 0 r) := by
    have hl : Differentiable ℂ (fun x : E => inner ℂ w x) :=
      (innerSL ℂ w).differentiable
    exact hl.comp_differentiableOn hG
  have hgB : ∀ t, ‖t‖ < r → ‖g t‖ ≤ ‖w‖ * B := fun t ht =>
    (norm_inner_le_norm w (G t)).trans (mul_le_mul_of_nonneg_left (hB t ht) hwp.le)
  have hg1 : ‖g 1‖ ≤ ‖w‖ * B :=
    (norm_inner_le_norm w (G 1)).trans (mul_le_mul_of_nonneg_left h1 hwp.le)
  have key := slice_diff_le_inv hr hgd hgB hg1
  have e : g 1 - g 0 = inner ℂ w w := by
    simp only [hg, hw, ← inner_sub_right]
  have h3 : ‖(inner ℂ w w : ℂ)‖ = ‖w‖ ^ 2 := by
    rw [inner_self_eq_norm_sq_to_K]; simp [norm_pow]
  rw [e, h3] at key
  have h2 : ‖w‖ ^ 2 ≤ ‖w‖ * (2 * B / r) := by
    calc ‖w‖ ^ 2 ≤ 2 * (‖w‖ * B) / r := key
      _ = ‖w‖ * (2 * B / r) := by ring
  nlinarith

end Slice

/-! ### The case split of (2.24) -/

section CaseSplit

/-- `1 + D/(2L) ≤ e^D` for `D ≥ 0` and `L ≥ 1/2`. -/
theorem one_add_div_le_exp {D L : ℝ} (hD : 0 ≤ D) (hL : 1 / 2 ≤ L) :
    1 + D / (2 * L) ≤ Real.exp D := by
  have hL0 : 0 < L := by linarith
  have h1 : D / (2 * L) ≤ D := by
    rw [div_le_iff₀ (by positivity)]; nlinarith
  have h2 := Real.add_one_le_exp D
  linarith

/-- `e^{-x} ≤ 1/x` for `x > 0`. -/
theorem exp_neg_le_inv {x : ℝ} (hx : 0 < x) : Real.exp (-x) ≤ 1 / x := by
  have h := Real.add_one_le_exp x
  have h2 : x ≤ Real.exp x := by linarith
  rw [Real.exp_neg, one_div]
  exact inv_anti₀ hx h2

/-- The constant of the improved bound: `2 c / Rad` in the small case, `2 c'` in the large case
(the polymer-size threshold is `D* = c' / s`; here `c'⁻¹` is multiplied in). -/
noncomputable def improvedConst (c Rad c' : ℝ) : ℝ := max (2 * c / Rad) (2 / c')

/-- **The case split of (2.24).**  Let `g(t) = M(x, X; ψ_y + tδψ, h)` along the slice, `B = A e^{-κ D}`
with `D = d_j(X)`, and `s = σε`.

* (small polymers) if `D ≤ D*` and `g` is holomorphic and bounded by `B` on `|t| < r₀` with
  `r₀ = Rad / (c (1 + D/(2L)) s)`, then `|g 1 - g 0| ≤ 2B/r₀`;
* (large polymers) if `D > D* = c' / s`, then `|g 1 - g 0| ≤ 2B` (both values are in the domain).

In both cases `|g 1 - g 0| ≤ C A s e^{-(κ-1) D}` with `C = improvedConst c Rad c'`. -/
theorem improved_delta_bound {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {G : ℂ → E} {A κ D s L c Rad c' : ℝ} (hA : 0 ≤ A) (hD : 0 ≤ D) (hs : 0 < s)
    (hL : 1 / 2 ≤ L) (hc : 0 < c) (hRad : 0 < Rad) (hc' : 0 < c')
    (hB1 : ‖G 1‖ ≤ A * Real.exp (-κ * D)) (hB0 : ‖G 0‖ ≤ A * Real.exp (-κ * D))
    (hsmall : D ≤ c' / s →
      DifferentiableOn ℂ G (ball 0 (Rad / (c * (1 + D / (2 * L)) * s))) ∧
      ∀ t, ‖t‖ < Rad / (c * (1 + D / (2 * L)) * s) → ‖G t‖ ≤ A * Real.exp (-κ * D)) :
    ‖G 1 - G 0‖ ≤ improvedConst c Rad c' * (A * s * Real.exp (-(κ - 1) * D)) := by
  have hL0 : 0 < L := by linarith
  have hexp : 0 < Real.exp (-κ * D) := Real.exp_pos _
  have hexp' : 0 < Real.exp (-(κ - 1) * D) := Real.exp_pos _
  have hsplit : Real.exp (-κ * D) = Real.exp (-(κ - 1) * D) * Real.exp (-D) := by
    rw [← Real.exp_add]; congr 1; ring
  by_cases hDs : D ≤ c' / s
  · -- small polymers
    obtain ⟨hdiff, hbd⟩ := hsmall hDs
    have hden : 0 < c * (1 + D / (2 * L)) * s := by positivity
    have hr0 : 0 < Rad / (c * (1 + D / (2 * L)) * s) := div_pos hRad hden
    have h := slice_diff_le_inv_vec hr0 hdiff hbd hB1
    have e : 2 * (A * Real.exp (-κ * D)) / (Rad / (c * (1 + D / (2 * L)) * s)) =
        (2 * c / Rad) * (A * s) * ((1 + D / (2 * L)) * Real.exp (-κ * D)) := by
      field_simp
    rw [e] at h
    refine h.trans ?_
    have h1 : (1 + D / (2 * L)) * Real.exp (-κ * D) ≤ Real.exp (-(κ - 1) * D) := by
      calc (1 + D / (2 * L)) * Real.exp (-κ * D) ≤ Real.exp D * Real.exp (-κ * D) :=
            mul_le_mul_of_nonneg_right (one_add_div_le_exp hD hL) hexp.le
        _ = Real.exp (-(κ - 1) * D) := by rw [← Real.exp_add]; congr 1; ring
    have hcc : 2 * c / Rad ≤ improvedConst c Rad c' := le_max_left _ _
    have h3 : 0 ≤ A * s := by positivity
    calc (2 * c / Rad) * (A * s) * ((1 + D / (2 * L)) * Real.exp (-κ * D))
        ≤ (2 * c / Rad) * (A * s) * Real.exp (-(κ - 1) * D) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = (2 * c / Rad) * (A * s * Real.exp (-(κ - 1) * D)) := by ring
      _ ≤ improvedConst c Rad c' * (A * s * Real.exp (-(κ - 1) * D)) :=
          mul_le_mul_of_nonneg_right hcc (by positivity)
  · -- large polymers
    push Not at hDs
    have hlt : c' / s < D := hDs
    have hDp : 0 < D := lt_of_le_of_lt (by positivity) hlt
    have h1 : ‖G 1 - G 0‖ ≤ 2 * (A * Real.exp (-κ * D)) := by
      calc ‖G 1 - G 0‖ ≤ ‖G 1‖ + ‖G 0‖ := norm_sub_le _ _
        _ ≤ _ := by linarith
    refine h1.trans ?_
    have h2 : Real.exp (-D) ≤ s / c' := by
      have hx : 0 < c' / s := by positivity
      have := exp_neg_le_inv hx
      calc Real.exp (-D) ≤ Real.exp (-(c' / s)) := Real.exp_le_exp.2 (by linarith)
        _ ≤ 1 / (c' / s) := this
        _ = s / c' := by field_simp
    have hcc : 2 / c' ≤ improvedConst c Rad c' := le_max_right _ _
    rw [hsplit]
    calc 2 * (A * (Real.exp (-(κ - 1) * D) * Real.exp (-D)))
        = 2 * A * Real.exp (-(κ - 1) * D) * Real.exp (-D) := by ring
      _ ≤ 2 * A * Real.exp (-(κ - 1) * D) * (s / c') :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = (2 / c') * (A * s * Real.exp (-(κ - 1) * D)) := by field_simp
      _ ≤ improvedConst c Rad c' * (A * s * Real.exp (-(κ - 1) * D)) :=
          mul_le_mul_of_nonneg_right hcc (by positivity)

end CaseSplit

/-! ### The resummation: (2.22) from (2.21) -/

section Resum

open Classical

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}
  {P : Consts} {Q : ObsConsts} {β ν a : ℕ → ℝ} {Tm : Terms d L N₁ m₁ k N ϱ}
  {Ot : ObsTerms d L N₁ m₁ k N}
  {Gker : ℕ → CTorus d L N₁ m₁ k → CTorus d L N₁ m₁ k → Fld d L N₁ m₁ k N →
    Fld d L N₁ m₁ k N → Matrix (Fin N) (Fin N) ℂ}

/-- **The normalization (2.1) at a constant unit configuration**: `M^{(j)}(x; v, v) = 0`. -/
theorem Mobs_const_zero (hO : IsObs P Q β ν a Tm Ot Gker) {j : ℕ} (hj1 : 1 ≤ j) (hjk : j ≤ k)
    (x : CTorus d L N₁ m₁ k) {v : Fin N → ℝ} (hv : v ⬝ᵥ v = 1) :
    Mobs P.m₀ Ot j x (constFld (fun i => (v i : ℂ))) (constFld (fun i => (v i : ℂ))) = 0 :=
  hO.normM j hj1 hjk x v hv

theorem vn_finsum_le {ι : Type*} (S : Set ι) (hS : S.Finite) (g : ι → Fin N → ℂ) :
    vn (∑ᶠ X ∈ S, g X) ≤ ∑ᶠ X ∈ S, vn (g X) := by
  rw [finsum_mem_eq_finite_toFinset_sum g hS, finsum_mem_eq_finite_toFinset_sum (fun X => vn (g X)) hS]
  have := Balaban.Background.vn_sum_le hS.toFinset g
  have e : (∑ i ∈ hS.toFinset, g i) = fun i => ∑ y ∈ hS.toFinset, g y i := by
    funext i; simp [Finset.sum_apply]
  rw [e]
  exact this

/-- **(2.22) from (2.21).**  Suppose that, for a pair `(ψ, h)` and a real unit vector `v`, every term
`M(x, X; ψ, h)`, `X ∈ 𝒟_j`, `X ∋ x`, is within `b X` of its value at the constant unit configuration
`(v, v)`.  Then `|M^{(j)}(x; ψ, h)| ≤ ∑_{X ∋ x} b_X`: the leading parts `M(x, X; v, v)` sum to zero by
the normalization. -/
theorem improved_second_of_first (hO : IsObs P Q β ν a Tm Ot Gker) {j : ℕ} (hj1 : 1 ≤ j)
    (hjk : j ≤ k) (x : CTorus d L N₁ m₁ k) (Ψ h : Fld d L N₁ m₁ k N) {v : Fin N → ℝ}
    (hv : v ⬝ᵥ v = 1) (b : Set (CTorus d L N₁ m₁ k) → ℝ)
    (hfirst : ∀ X ∈ polysAt P.m₀ j x,
      vn (Ot.M j x X Ψ h - Ot.M j x X (constFld (fun i => (v i : ℂ)))
        (constFld (fun i => (v i : ℂ)))) ≤ b X) :
    vn (Mobs P.m₀ Ot j x Ψ h) ≤ ∑ᶠ X ∈ polysAt P.m₀ j x, b X := by
  have hS : (polysAt P.m₀ j x).Finite := Set.toFinite _
  have h0 := Mobs_const_zero hO hj1 hjk x hv
  have hdiff : Mobs P.m₀ Ot j x Ψ h = ∑ᶠ X ∈ polysAt P.m₀ j x,
      (Ot.M j x X Ψ h - Ot.M j x X (constFld (fun i => (v i : ℂ)))
        (constFld (fun i => (v i : ℂ)))) := by
    have e : ∑ᶠ X ∈ polysAt P.m₀ j x, (Ot.M j x X Ψ h - Ot.M j x X (constFld (fun i => (v i : ℂ)))
        (constFld (fun i => (v i : ℂ)))) =
        Mobs P.m₀ Ot j x Ψ h - Mobs P.m₀ Ot j x (constFld (fun i => (v i : ℂ)))
          (constFld (fun i => (v i : ℂ))) := by
      unfold Mobs
      rw [finsum_mem_eq_finite_toFinset_sum _ hS, finsum_mem_eq_finite_toFinset_sum _ hS,
        finsum_mem_eq_finite_toFinset_sum _ hS, ← Finset.sum_sub_distrib]
    rw [e, h0, sub_zero]
  rw [hdiff]
  refine (vn_finsum_le _ hS _).trans ?_
  rw [finsum_mem_eq_finite_toFinset_sum _ hS, finsum_mem_eq_finite_toFinset_sum _ hS]
  exact Finset.sum_le_sum fun X hX => hfirst X (hS.mem_toFinset.1 hX)

/-- **(2.22) with the entropy bound** (P5 (1.35)): if each term obeys the improved bound
`C A s e^{-(κ-1) d_j(X)}` and `∑_{X ∋ x} e^{-(κ-1) d_j(X)} ≤ K₀`, then
`|M^{(j)}(x; ψ, h)| ≤ C K₀ A s`. -/
theorem improved_second_bound (hO : IsObs P Q β ν a Tm Ot Gker) {j : ℕ} (hj1 : 1 ≤ j)
    (hjk : j ≤ k) (x : CTorus d L N₁ m₁ k) (Ψ h : Fld d L N₁ m₁ k N) {v : Fin N → ℝ}
    (hv : v ⬝ᵥ v = 1) {C A s K₀ : ℝ} (hC : 0 ≤ C)
    (hfirst : ∀ X ∈ polysAt P.m₀ j x,
      vn (Ot.M j x X Ψ h - Ot.M j x X (constFld (fun i => (v i : ℂ)))
        (constFld (fun i => (v i : ℂ)))) ≤
        C * (A * s * Real.exp (-(P.κ - 1) * sizeJ P.m₀ j X)))
    (hK : ∑ᶠ X ∈ polysAt P.m₀ j x, Real.exp (-(P.κ - 1) * sizeJ P.m₀ j X) ≤ K₀) (hAs : 0 ≤ A * s) :
    vn (Mobs P.m₀ Ot j x Ψ h) ≤ C * K₀ * (A * s) := by
  have hS : (polysAt P.m₀ j x).Finite := Set.toFinite _
  refine (improved_second_of_first hO hj1 hjk x Ψ h hv _ hfirst).trans ?_
  rw [finsum_mem_eq_finite_toFinset_sum _ hS]
  rw [finsum_mem_eq_finite_toFinset_sum _ hS] at hK
  calc ∑ X ∈ hS.toFinset, C * (A * s * Real.exp (-(P.κ - 1) * sizeJ P.m₀ j X))
      = C * (A * s) * ∑ X ∈ hS.toFinset, Real.exp (-(P.κ - 1) * sizeJ P.m₀ j X) := by
        rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun X _ => by ring
    _ ≤ C * (A * s) * K₀ := mul_le_mul_of_nonneg_left hK (by positivity)
    _ = C * K₀ * (A * s) := by ring

end Resum

end Balaban.Observables
