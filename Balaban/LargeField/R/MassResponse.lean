/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Background.Prop51Mass
public import Balaban.Background.ExistenceBounds
public import Balaban.Fluctuation.WeightedProp51
public import Balaban.Fluctuation.Lemma25Xi
public import Balaban.LargeField.R.MassChangeWall
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The same-datum mass source (MASS-RESPONSE.md §1)

The massless background `(φ⁰, α⁰)` and the massive background `(φᵐ, αᵐ)` on the **same** datum
solve `IsEL` at masses `0` and `μ`.  In the landed `source`, the mass `ν` already enters as the
term `ν h`.  Subtracting the two equations gives the perturbed system `IsPerturbed` at mass `0`
with the source `massSource = -μ (φᵐ - h)` and zero data change.

* `massSource`, `massSource_perturbed`, `pertSource_zero_massSource`;
* `massSource_bound` (note (1.4)), `massSource_bound_unit`;
* `massMultiplier_small`;
* `massChange_sameData_response_of_weighted` (note (1.5), conditional on the weighted
  Proposition 5.1 predicate and its operator hypotheses).
-/

@[expose] public section

namespace Balaban.LargeField.ActionConv

open Balaban.Multiscale Balaban.Background Balaban.Fluctuation Balaban.Localization Finset Matrix

variable {d L N₀ K N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ} {G : GeneratingSet d L N₀ K ϱ}

/-- The mass source `f₁ = -μ (φᵐ - h)` of the same-datum comparison (note (1.2)). -/
noncomputable def massSource (μ : ℝ) (D : BgData G N) (φm : G.Ω 1 × Fin N → ℂ) :
    G.Ω 1 × Fin N → ℂ := fun p => -(μ : ℂ) * (φm p - D.h p.1 p.2)

/-- With zero data change, `pertSource` is the free source `f₁`. -/
theorem pertSource_zero (a : ℕ → ℝ) (f₁ : G.Ω 1 × Fin N → ℂ) :
    pertSource G a (0 : Torus d (N₀ * L ^ K) → Fin N → ℂ) f₁ = f₁ := by
  funext p
  simp [pertSource, qStar, boundaryTerm]

/-- The mass source is `pertSource` with `δΨ = 0`. -/
theorem pertSource_zero_massSource (a : ℕ → ℝ) (μ : ℝ) (D : BgData G N)
    (φm : G.Ω 1 × Fin N → ℂ) :
    pertSource G a (0 : Torus d (N₀ * L ^ K) → Fin N → ℂ) (massSource μ D φm) =
      massSource μ D φm := pertSource_zero a _

/-- **Same-datum mass source** (note (1.1)–(1.2)): the two Euler–Lagrange systems on one datum,
at masses `0` and `μ`, give the perturbed system at mass `0` with base `φ̄⁰`, source
`massSource`, `δφ = φᵐ - φ⁰`, `δα = αᵐ - α⁰`.  (The landed `source` contains `ν h`.) -/
theorem massSource_perturbed (a : ℕ → ℝ) (μ : ℝ) (D : BgData G N)
    {φ0 φm : G.Ω 1 × Fin N → ℂ} {α0 αm : G.Ω 1 → ℂ}
    (h0 : IsEL G a 0 D φ0 α0) (hm : IsEL G a μ D φm αm) :
    IsPerturbed G a 0 α0 (barField G D.Ψ φ0) (massSource μ D φm) (φm - φ0) (αm - α0) := by
  have bar : ∀ (x : G.Ω 1) i, barField G D.Ψ φ0 x i = φ0 (x, i) := by
    intro x i; simp [barField, x.2]
  refine ⟨?_, ?_⟩
  · funext p
    have e0 := congrFun h0.1 p
    have em := congrFun hm.1 p
    rw [dirichletOperator_mass_shift G a 0 μ αm] at em
    have hα : (αm + fun _ => ((μ - 0 : ℝ) : ℂ)) = α0 + ((αm - α0) + fun _ => ((μ - 0 : ℝ) : ℂ)) := by
      funext x; simp only [Pi.add_apply, Pi.sub_apply]; ring
    rw [hα, liftOp_dirichlet_add] at em
    simp only [source, Pi.add_apply, Pi.sub_apply, sub_zero,
      Complex.ofReal_zero, zero_mul] at e0 em
    simp only [Pi.add_apply, Pi.sub_apply, Matrix.mulVec_sub, massSource, bar]
    linear_combination em - e0
  · intro x
    have := hm.2 x
    simp only [bar, Pi.sub_apply]
    simpa using this

/-- **Note (1.4)**: `ℓ² |f₁| ≤ m Bh` from `μ ℓ² ≤ m` and `|φᵐ - h| ≤ Bh`. -/
theorem massSource_bound {μ m Bh : ℝ} (D : BgData G N) (φm : G.Ω 1 × Fin N → ℂ) (hμ : 0 ≤ μ)
    (hμℓ : ∀ x : G.Ω 1, μ * G.spacing (x : Torus d (N₀ * L ^ K)) ^ 2 ≤ m)
    (hB : ∀ (x : G.Ω 1) (i : Fin N), ‖φm (x, i) - D.h x i‖ ≤ Bh)
    (x : G.Ω 1) (i : Fin N) :
    G.spacing (x : Torus d (N₀ * L ^ K)) ^ 2 * ‖massSource μ D φm (x, i)‖ ≤ m * Bh := by
  have hB0 : 0 ≤ Bh := (norm_nonneg _).trans (hB x i)
  unfold massSource
  rw [norm_mul, norm_neg, Complex.norm_real, Real.norm_of_nonneg hμ]
  calc G.spacing (x : Torus d (N₀ * L ^ K)) ^ 2 * (μ * ‖φm (x, i) - D.h x i‖)
      = (μ * G.spacing (x : Torus d (N₀ * L ^ K)) ^ 2) * ‖φm (x, i) - D.h x i‖ := by ring
    _ ≤ m * Bh := mul_le_mul (hμℓ x) (hB x i) (norm_nonneg _) ((mul_nonneg hμ (sq_nonneg _)).trans (hμℓ x))

/-- Real hard-spin instance of the componentwise bound: unit vectors `φᵐ(x)`, `h(x)` give
`‖φᵐ (x,i) - h x i‖ ≤ 2`. -/
theorem norm_sub_le_two_of_unit {φm : G.Ω 1 × Fin N → ℂ} (D : BgData G N)
    (hφ : ∀ x : G.Ω 1, ∑ i, ‖φm (x, i)‖ ^ 2 = 1) (hh : ∀ x : G.Ω 1, ∑ i, ‖D.h x i‖ ^ 2 = 1)
    (x : G.Ω 1) (i : Fin N) : ‖φm (x, i) - D.h x i‖ ≤ 2 := by
  have h1 : ‖φm (x, i)‖ ≤ 1 := by
    have := Finset.single_le_sum (f := fun j => ‖φm (x, j)‖ ^ 2) (fun j _ => by positivity)
      (Finset.mem_univ i)
    rw [hφ x] at this
    nlinarith [norm_nonneg (φm (x, i))]
  have h2 : ‖D.h x i‖ ≤ 1 := by
    have := Finset.single_le_sum (f := fun j => ‖D.h x j‖ ^ 2) (fun j _ => by positivity)
      (Finset.mem_univ i)
    rw [hh x] at this
    nlinarith [norm_nonneg (D.h x i)]
  linarith [norm_sub_le (φm (x, i)) (D.h x i)]

/-- Note (1.4) with `Bh = 2` for unit vectors. -/
theorem massSource_bound_unit {μ m : ℝ} (D : BgData G N) (φm : G.Ω 1 × Fin N → ℂ) (hμ : 0 ≤ μ)
    (hμℓ : ∀ x : G.Ω 1, μ * G.spacing (x : Torus d (N₀ * L ^ K)) ^ 2 ≤ m)
    (hφ : ∀ x : G.Ω 1, ∑ i, ‖φm (x, i)‖ ^ 2 = 1) (hh : ∀ x : G.Ω 1, ∑ i, ‖D.h x i‖ ^ 2 = 1)
    (x : G.Ω 1) (i : Fin N) :
    G.spacing (x : Torus d (N₀ * L ^ K)) ^ 2 * ‖massSource μ D φm (x, i)‖ ≤ m * 2 :=
  massSource_bound D φm hμ hμℓ (norm_sub_le_two_of_unit D hφ hh) x i

/-- The two multiplier bounds give `|αᵐ - α⁰|₂ ≤ 2c`. -/
theorem massMultiplier_small {D : BgData G N} {φ0 φm : G.Ω 1 × Fin N → ℂ}
    {α0 αm : G.Ω 1 → ℂ} {c : ℝ} (h0 : BgBounds G D φ0 α0 c) (hm : BgBounds G D φm αm c) :
    Small G (αm - α0) (2 * c) := by
  intro x
  have := norm_sub_le (αm x) (α0 x)
  have a0 := h0.alpha x
  have a1 := hm.alpha x
  have hp : 0 ≤ G.spacing (x : Torus d (N₀ * L ^ K)) ^ 2 := by positivity
  simp only [Pi.sub_apply]
  nlinarith [mul_le_mul_of_nonneg_left this hp]

section Response

variable {N₁ m₁ : ℕ} [NeZero N₁] {Kw δw : ℝ}

/-- **Note (1.5), conditional form.**  On one datum `D`, with `φ⁰`, `φᵐ` solving (EL) at masses
`0`, `μ`: given the weighted Proposition 5.1 predicate `WeightedProp51S d L N Kw δw`, the
hypotheses `Prop51Hyp` (at `ν = 0`, `δΨ = 0`, `f₁ = massSource`) and `Dec2.OpSetting`, and
`|αᵐ - α⁰|₂ ≤ c₆`, the response is bounded with weight one by `Kw · (m Bh)`.  Remaining
hypotheses: `WeightedProp51S` (from `weightedProp51S_exists`), `Prop51Hyp` and `OpSetting`
(from the data/separation conditions), and the multiplier class (from `massMultiplier_small`). -/
theorem massChange_sameData_response_of_weighted
    (hd : 0 < d) (hW : WeightedProp51S d L N Kw δw)
    {G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} (a : ℕ → ℝ) (μ m Bh δ₀ δ₁ : ℝ)
    (D : BgData G N) {φ0 φm : G.Ω 1 × Fin N → ℂ} {α0 αm : G.Ω 1 → ℂ}
    (h0 : IsEL G a 0 D φ0 α0) (hm : IsEL G a μ D φm αm)
    (hP : Prop51Hyp G a 0 α0 (barField G D.Ψ φ0) (0 : Torus d ((N₁ * L ^ m₁) * L ^ K) → Fin N → ℂ)
      (massSource μ D φm) δ₀ δ₁)
    (hO : Dec2.OpSetting G a 0) (hδ₀ : δ₀ ≤ δw) (hδ₁ : δ₁ ≤ δw)
    (hm0 : 0 ≤ m) (hBh0 : 0 ≤ Bh) (hμ : 0 ≤ μ) (hμℓ : ∀ x : G.Ω 1, μ * G.spacing (x : Torus d ((N₁ * L ^ m₁) * L ^ K)) ^ 2 ≤ m)
    (hB : ∀ (x : G.Ω 1) (i : Fin N), ‖φm (x, i) - D.h x i‖ ≤ Bh)
    (hα : Small G (αm - α0) (c6 d L N)) :
    SmallW G (fun _ => 1) (αm - α0) (Kw * (m * Bh)) ∧
      SupBoundsW G (fun _ => 1) (φm - φ0) (Kw * (m * Bh)) := by
  have hg : ∀ x : G.Ω 1, gdef G (barField G D.Ψ φ0) x = 0 := by
    intro x
    have := h0.2 x
    simp only [gdef, barField, x.2, dite_true]
    rw [this]; ring
  have hB0 : 0 ≤ m * Bh := mul_nonneg hm0 hBh0
  have hone := hW G a 0 α0 (barField G D.Ψ φ0) 0 (massSource μ D φm) δ₀ δ₁ hP hO hg hδ₀ hδ₁
    (fun _ => 1) (IsWeight.one G (gammaW_nonneg hd)) (m * Bh) hB0 (fun x i => by
      rw [pertSource_zero]; simpa using massSource_bound D φm hμ hμℓ hB x i)
    (φm - φ0) (αm - α0) (by rw [pertSource_zero]; exact massSource_perturbed a μ D h0 hm) hα
  exact hone

/-- **Note (1.5) in the consumer's form**: the hypothesis `hresp` of
`massChange_wall_bound_of_bounds` with `Km = √N · Kw`. -/
theorem massChange_sameData_hresp_of_weighted
    (hd : 0 < d) (hW : WeightedProp51S d L N Kw δw)
    {G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} (a : ℕ → ℝ) (μ m Bh δ₀ δ₁ : ℝ)
    (D : BgData G N) {φ0 φm : G.Ω 1 × Fin N → ℂ} {α0 αm : G.Ω 1 → ℂ}
    (h0 : IsEL G a 0 D φ0 α0) (hm : IsEL G a μ D φm αm)
    (hP : Prop51Hyp G a 0 α0 (barField G D.Ψ φ0) (0 : Torus d ((N₁ * L ^ m₁) * L ^ K) → Fin N → ℂ)
      (massSource μ D φm) δ₀ δ₁)
    (hO : Dec2.OpSetting G a 0) (hδ₀ : δ₀ ≤ δw) (hδ₁ : δ₁ ≤ δw)
    (hm0 : 0 ≤ m) (hBh0 : 0 ≤ Bh) (hμ : 0 ≤ μ)
    (hμℓ : ∀ x : G.Ω 1, μ * G.spacing (x : Torus d ((N₁ * L ^ m₁) * L ^ K)) ^ 2 ≤ m)
    (hB : ∀ (x : G.Ω 1) (i : Fin N), ‖φm (x, i) - D.h x i‖ ≤ Bh)
    (hα : Small G (αm - α0) (c6 d L N)) (hKw : 0 ≤ Kw) :
    ∀ x, vnorm (wExt D D φm φ0 x) ≤ (Real.sqrt N * Kw) * Bh * m := by
  intro x
  have hres := (massChange_sameData_response_of_weighted hd hW a μ m Bh δ₀ δ₁ D h0 hm hP hO hδ₀
    hδ₁ hm0 hBh0 hμ hμℓ hB hα).2
  have hV : 0 ≤ Kw * (m * Bh) := by positivity
  have key : vnorm (wExt D D φm φ0 x) ≤ Real.sqrt N * (Kw * (m * Bh)) := by
    refine vn_le_sqrt_mul hV fun i => ?_
    unfold wExt
    by_cases hx : x ∈ G.Ω 1
    · have := hres.val ⟨x, hx⟩ i
      simp only [one_mul, Pi.sub_apply] at this
      simp only [barField, hx, dite_true]
      rwa [norm_sub_rev]
    · simp only [barField, hx, dite_false, sub_self, norm_zero]
      exact hV
  calc _ ≤ _ := key
    _ = _ := by ring

end Response

end Balaban.LargeField.ActionConv
