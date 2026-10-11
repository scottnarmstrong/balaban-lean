/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Background.MinimizerExpansion
public import Balaban.Multiscale.CoercivitySharp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The minimizer identity (5.3) and the unique global minimizer (BACKGROUND.md §5.4)

For real data `D` and a real solution `(φ, α)` of (EL) with `α` real and `|α|₂ < c₀ ≤ 1/16`:
for every real unit field `σ`,
`A(σ) - A(φ) = ½ ∑_i Re ⟨σ_i - φ_i, H_D(α) (σ_i - φ_i)⟩`  (`action_sub_eq`),
which is positive for `σ ≠ φ` by the coercivity of `H_D(α)` (`multiscale_coercive_sharp_gen`):
`φ` is the unique global minimizer (`isMinimizer_of_smallSolution`, `eq_of_isMinimizer`).
-/

@[expose] public section

namespace Balaban.Background

open Balaban.Multiscale Matrix Finset

variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}

variable {G : GeneratingSet d L N₀ k ϱ} {a : ℕ → ℝ} {ν : ℝ}

theorem sq_norm_cast {z : ℂ} (h : z.im = 0) : ((‖z‖ : ℝ) : ℂ) ^ 2 = z * z := by
  have : z = (z.re : ℂ) := Complex.ext (by simp) (by simp [h])
  rw [this, Complex.norm_real, Real.norm_eq_abs, ← Complex.ofReal_pow, sq_abs,
    Complex.ofReal_pow]
  ring

section RealField

theorem svec_im {φ : G.Ω 1 × Fin N → ℂ} (h : ∀ (x : G.Ω 1) i, (φ (x, i)).im = 0)
    (y : Torus d (N₀ * L ^ k)) (i : Fin N) : (svec G φ y i).im = 0 := by
  by_cases hy : y ∈ G.Ω 1
  · have := h ⟨y, hy⟩ i
    rwa [← svec_of_mem G φ ⟨y, hy⟩ i] at this
  · rw [svec_of_not_mem G _ hy]; simp

theorem blockAvg_im {φ : G.Ω 1 × Fin N → ℂ} (h : ∀ (x : G.Ω 1) i, (φ (x, i)).im = 0)
    (x : Torus d (N₀ * L ^ k)) (i : Fin N) : (blockAvg G φ x i).im = 0 := by
  unfold blockAvg
  rw [Complex.im_ofReal_mul, Complex.im_sum]
  simp [svec_im h]

theorem barField_im {Ψ : Torus d (N₀ * L ^ k) → Fin N → ℂ} (hΨ : ∀ x i, (Ψ x i).im = 0)
    {φ : G.Ω 1 × Fin N → ℂ} (h : ∀ (x : G.Ω 1) i, (φ (x, i)).im = 0)
    (y : Torus d (N₀ * L ^ k)) (i : Fin N) : (barField G Ψ φ y i).im = 0 := by
  classical
  by_cases hy : y ∈ G.Ω 1
  · simp only [barField, hy, dite_true]; exact h _ i
  · simp only [barField, hy, dite_false]; exact hΨ y i

/-- On real data and real fields the action is the real part of `actionC`. -/
theorem action_cast (D : BgData G N) (hD : D.IsReal) {φ : G.Ω 1 × Fin N → ℂ}
    (hφ : ∀ (x : G.Ω 1) i, (φ (x, i)).im = 0) :
    ((action G a ν D φ : ℝ) : ℂ) = actionC G a ν D φ := by
  have hΨ : ∀ x i, (D.Ψ x i).im = 0 := fun x i => (hD x i).1
  have hh : ∀ x i, (D.h x i).im = 0 := fun x i => (hD x i).2
  have e1 : ∀ x : G.Ω 1, ∑ i, ((‖D.Ψ x i - blockAvg G φ x i‖ : ℝ) : ℂ) ^ 2 =
      ∑ i, (D.Ψ x i - blockAvg G φ x i) * (D.Ψ x i - blockAvg G φ x i) := fun x =>
    Finset.sum_congr rfl fun i _ => sq_norm_cast (by simp [hΨ, blockAvg_im hφ])
  have e2 : ∀ (x : Torus d (N₀ * L ^ k)) (μ : Fin d), (if x ∈ G.Ω 1 ∨ x + Pi.single μ 1 ∈ G.Ω 1 then
      ∑ i, ((‖barField G D.Ψ φ (x + Pi.single μ 1) i - barField G D.Ψ φ x i‖ : ℝ) : ℂ) ^ 2
        else 0) = (if x ∈ G.Ω 1 ∨ x + Pi.single μ 1 ∈ G.Ω 1 then
      ∑ i, (barField G D.Ψ φ (x + Pi.single μ 1) i - barField G D.Ψ φ x i) *
          (barField G D.Ψ φ (x + Pi.single μ 1) i - barField G D.Ψ φ x i) else 0) := by
    intro x μ
    refine if_congr Iff.rfl (Finset.sum_congr rfl fun i _ => sq_norm_cast ?_) rfl
    simp [barField_im hΨ hφ]
  have e3 : ∀ x : G.Ω 1, ∑ i, ((‖φ (x, i) - D.h x i‖ : ℝ) : ℂ) ^ 2 =
      ∑ i, (φ (x, i) - D.h x i) * (φ (x, i) - D.h x i) := fun x =>
    Finset.sum_congr rfl fun i _ => sq_norm_cast (by simp [hφ, hh])
  have ite_cast : ∀ (P : Prop) [Decidable P] (u : ℝ),
      (((if P then u else 0 : ℝ)) : ℂ) = if P then (u : ℂ) else 0 := by
    intros; split_ifs <;> simp
  unfold action actionC
  push_cast
  simp only [ite_cast]
  push_cast
  simp only [e1, e2, e3]

end RealField

section Identity

theorem H_alpha_apply (α : G.Ω 1 → ℂ) (w : G.Ω 1 × Fin N → ℂ) (p : G.Ω 1 × Fin N) :
    (liftOp N (dirichletOperator G a ν α) *ᵥ w) p =
      (liftOp N (dirichletOperator G a ν 0) *ᵥ w) p + α p.1 * w p := by
  have := liftOp_dirichlet_add (G := G) a ν 0 α w p
  rwa [zero_add] at this

/-- **The identity (5.3), algebraic form.**  For a solution `(φ, α)` of (EL) and any field `σ` with
`σ · σ = 1` on `Ω₁`: `A_C(σ) - A_C(φ) = ½ ⟨σ - φ, H_D(α) (σ - φ)⟩`. -/
theorem actionC_sub_eq (D : BgData G N) {φ σ : G.Ω 1 × Fin N → ℂ} {α : G.Ω 1 → ℂ}
    (hφ : IsEL G a ν D φ α) (hσ : ∀ x : G.Ω 1, ∑ i, σ (x, i) * σ (x, i) = 1) :
    actionC G a ν D σ - actionC G a ν D φ =
      (1 / 2) * pair G (σ - φ) (liftOp N (dirichletOperator G a ν α) *ᵥ (σ - φ)) := by
  have hsum : σ = φ + (σ - φ) := by funext p; simp
  have h1 := actionC_add (a := a) (ν := ν) D φ (σ - φ)
  rw [← hsum] at h1
  rw [h1]
  set τ := σ - φ with hτ
  have hS : ∀ p, source G a ν D p = (liftOp N (dirichletOperator G a ν 0) *ᵥ φ) p + α p.1 * φ p := by
    intro p
    rw [← hφ.1, H_alpha_apply]
  have hP1 : pair G τ (liftOp N (dirichletOperator G a ν 0) *ᵥ φ - source G a ν D) =
      -∑ p : G.Ω 1 × Fin N, α p.1 * (τ p * φ p) := by
    unfold pair
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Pi.sub_apply, hS p]; ring
  have hP2 : pair G τ (liftOp N (dirichletOperator G a ν α) *ᵥ τ) =
      pair G τ (liftOp N (dirichletOperator G a ν 0) *ᵥ τ) +
        ∑ p : G.Ω 1 × Fin N, α p.1 * (τ p * τ p) := by
    unfold pair
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [H_alpha_apply]; ring
  have hcon : ∑ p : G.Ω 1 × Fin N, α p.1 * (τ p * (τ p + 2 * φ p)) = 0 := by
    rw [Fintype.sum_prod_type]
    refine Finset.sum_eq_zero fun x _ => ?_
    dsimp only
    rw [← Finset.mul_sum]
    have : ∑ i, τ (x, i) * (τ (x, i) + 2 * φ (x, i)) =
        ∑ i, σ (x, i) * σ (x, i) - ∑ i, φ (x, i) * φ (x, i) := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [hτ, Pi.sub_apply]; ring
    rw [this, hσ x, hφ.2 x]; ring
  have hexp : ∑ p : G.Ω 1 × Fin N, α p.1 * (τ p * (τ p + 2 * φ p)) =
      ∑ p : G.Ω 1 × Fin N, α p.1 * (τ p * τ p) + 2 * ∑ p : G.Ω 1 × Fin N, α p.1 * (τ p * φ p) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun p _ => by ring
  rw [hP1, hP2]
  linear_combination (-1 / 2 : ℂ) * hcon + (1 / 2 : ℂ) * hexp

theorem dot_eq_one_of_unit {σ : G.Ω 1 × Fin N → ℂ} (h : IsRealUnitField G σ) (x : G.Ω 1) :
    ∑ i, σ (x, i) * σ (x, i) = 1 := by
  obtain ⟨hre, hn⟩ := h x
  have : ∑ i, σ (x, i) * σ (x, i) = ((∑ i, ‖σ (x, i)‖ ^ 2 : ℝ) : ℂ) := by
    push_cast
    exact Finset.sum_congr rfl fun i _ => (sq_norm_cast (hre i)).symm
  rw [this, hn]; simp

theorem isRealUnit_of_dot {φ : G.Ω 1 × Fin N → ℂ} (hre : ∀ (x : G.Ω 1) i, (φ (x, i)).im = 0)
    (hd : ∀ x : G.Ω 1, ∑ i, φ (x, i) * φ (x, i) = 1) : IsRealUnitField G φ := by
  intro x
  refine ⟨hre x, ?_⟩
  have h1 : ((∑ i, ‖φ (x, i)‖ ^ 2 : ℝ) : ℂ) = 1 := by
    push_cast
    rw [← hd x]
    exact Finset.sum_congr rfl fun i _ => sq_norm_cast (hre x i)
  exact_mod_cast h1

/-- The real quadratic form: for a real field `τ`, `Re ⟨τ, H τ⟩ = ∑_i reQuad H τ_i`. -/
theorem pair_re (H : Matrix (G.Ω 1) (G.Ω 1) ℂ) {τ : G.Ω 1 × Fin N → ℂ}
    (hτ : ∀ (x : G.Ω 1) i, (τ (x, i)).im = 0) :
    (pair G τ (liftOp N H *ᵥ τ)).re = ∑ i, Green.reQuad H (fun x => τ (x, i)) := by
  unfold pair Green.reQuad
  rw [Fintype.sum_prod_type_right]
  simp only [Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun x _ => ?_
  have : star (τ (x, i)) = τ (x, i) := by
    rw [Complex.star_def, Complex.conj_eq_iff_im]; exact hτ x i
  rw [this, liftOp_mulVec]

end Identity

section Positivity

/-- **The identity (5.3), real form with coercivity**: for real data and a small solution
(`c₀ ≤ 1/16`, `0 ≤ ν`, admissible weights), the action difference to any real unit field is
`½ ∑_i Re ⟨τ_i, H_D(α) τ_i⟩ ≥ (7/32) ∑_i ‖ℓ⁻¹ τ_i‖²`. -/
theorem action_sub_ge {c₀ : ℝ} (hc₀ : c₀ ≤ 1 / 16) (hν : 0 ≤ ν) (ha : IsAdmissibleWeights k a)
    (D : BgData G N) (hD : D.IsReal) {φ : G.Ω 1 × Fin N → ℂ} {α : G.Ω 1 → ℂ}
    (hs : IsSmallSolution G a ν c₀ D φ α) (hφ : IsRealUnitField G φ) {σ : G.Ω 1 × Fin N → ℂ}
    (hσ : IsRealUnitField G σ) :
    action G a ν D σ - action G a ν D φ =
        (1 / 2) * ∑ i, Green.reQuad (dirichletOperator G a ν α) (fun x => σ (x, i) - φ (x, i)) ∧
      (7 / 32) * ∑ i, weightedSqNorm G (fun x => σ (x, i) - φ (x, i)) ≤
        action G a ν D σ - action G a ν D φ := by
  have hφim : ∀ (x : G.Ω 1) i, (φ (x, i)).im = 0 := fun x i => (hφ x).1 i
  have hσim : ∀ (x : G.Ω 1) i, (σ (x, i)).im = 0 := fun x i => (hσ x).1 i
  have hτim : ∀ (x : G.Ω 1) i, ((σ - φ) (x, i)).im = 0 := fun x i => by
    simp [hφim, hσim]
  have hid := actionC_sub_eq (a := a) (ν := ν) D hs.1 (dot_eq_one_of_unit hσ)
  have hcast : ((action G a ν D σ - action G a ν D φ : ℝ) : ℂ) =
      (1 / 2) * pair G (σ - φ) (liftOp N (dirichletOperator G a ν α) *ᵥ (σ - φ)) := by
    push_cast
    rw [action_cast D hD hσim, action_cast D hD hφim]
    exact hid
  have hre : action G a ν D σ - action G a ν D φ =
      (1 / 2) * ∑ i, Green.reQuad (dirichletOperator G a ν α) (fun x => σ (x, i) - φ (x, i)) := by
    have := congrArg Complex.re hcast
    rw [Complex.ofReal_re] at this
    rw [this]
    have h2 : ((1 / 2 : ℂ) * pair G (σ - φ) (liftOp N (dirichletOperator G a ν α) *ᵥ (σ - φ))).re =
        (1 / 2) * (pair G (σ - φ) (liftOp N (dirichletOperator G a ν α) *ᵥ (σ - φ))).re := by
      simp
    rw [h2, pair_re _ hτim]
    rfl
  refine ⟨hre, ?_⟩
  rw [hre]
  have hα' : ∀ x : G.Ω 1, ‖α x‖ ≤ (1 / 16) / (G.spacing (x : Torus d (N₀ * L ^ k))) ^ 2 := by
    intro x
    have hp : 0 < (G.spacing (x : Torus d (N₀ * L ^ k))) ^ 2 := by
      have := spacing_pos G (x := (x : Torus d (N₀ * L ^ k))); positivity
    rw [le_div_iff₀ hp]
    have := hs.2 x
    nlinarith
  have hcoer : ∀ i, (7 / 16 : ℝ) * weightedSqNorm G (fun x => σ (x, i) - φ (x, i)) ≤
      Green.reQuad (dirichletOperator G a ν α) (fun x => σ (x, i) - φ (x, i)) := by
    intro i
    have h := multiscale_coercive_sharp_gen G hν ha (θ := 1 / 16) (by norm_num) α hα'
      (fun x => σ (x, i) - φ (x, i))
    have hE := dirichletEnergy_nonneg G (fun x => σ (x, i) - φ (x, i))
    nlinarith
  rw [Finset.mul_sum]
  have : ∑ i, (7 / 32 : ℝ) * weightedSqNorm G (fun x => σ (x, i) - φ (x, i)) ≤
      ∑ i, (1 / 2 : ℝ) * Green.reQuad (dirichletOperator G a ν α) (fun x => σ (x, i) - φ (x, i)) :=
    Finset.sum_le_sum fun i _ => by linarith [hcoer i]
  simpa [Finset.mul_sum] using this

theorem weightedSqNorm_eq_zero {u : G.Ω 1 → ℂ} (h : weightedSqNorm G u ≤ 0) (x : G.Ω 1) :
    u x = 0 := by
  have hnn : ∀ y ∈ (Finset.univ : Finset (G.Ω 1)),
      0 ≤ ‖u y‖ ^ 2 / (G.spacing (y : Torus d (N₀ * L ^ k))) ^ 2 := fun y _ => by positivity
  have h0 : ∑ y : G.Ω 1, ‖u y‖ ^ 2 / (G.spacing (y : Torus d (N₀ * L ^ k))) ^ 2 = 0 :=
    le_antisymm h (Finset.sum_nonneg hnn)
  have := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 h0 x (Finset.mem_univ x)
  have hp : 0 < (G.spacing (x : Torus d (N₀ * L ^ k))) ^ 2 := by
    have := spacing_pos G (x := (x : Torus d (N₀ * L ^ k))); positivity
  rw [div_eq_zero_iff] at this
  rcases this with h1 | h1
  · exact norm_eq_zero.1 (pow_eq_zero_iff (two_ne_zero) |>.1 h1)
  · exact absurd h1 hp.ne'

/-- **A small real solution is a global minimizer** (BACKGROUND.md §5.4). -/
theorem isMinimizer_of_smallSolution {c₀ : ℝ} (hc₀ : c₀ ≤ 1 / 16) (hν : 0 ≤ ν)
    (ha : IsAdmissibleWeights k a) (D : BgData G N) (hD : D.IsReal)
    {φ : G.Ω 1 × Fin N → ℂ} {α : G.Ω 1 → ℂ} (hs : IsSmallSolution G a ν c₀ D φ α)
    (hφ : IsRealUnitField G φ) : IsMinimizer G a ν D φ := by
  refine ⟨hD, hφ, fun σ hσ => ?_⟩
  obtain ⟨-, h2⟩ := action_sub_ge hc₀ hν ha D hD hs hφ hσ
  have : 0 ≤ ∑ i, weightedSqNorm G (fun x => σ (x, i) - φ (x, i)) :=
    Finset.sum_nonneg fun i _ => weightedSqNorm_nonneg G _
  linarith

/-- **The small real solution is the unique global minimizer.** -/
theorem eq_of_isMinimizer {c₀ : ℝ} (hc₀ : c₀ ≤ 1 / 16) (hν : 0 ≤ ν)
    (ha : IsAdmissibleWeights k a) (D : BgData G N) (hD : D.IsReal)
    {φ : G.Ω 1 × Fin N → ℂ} {α : G.Ω 1 → ℂ} (hs : IsSmallSolution G a ν c₀ D φ α)
    (hφ : IsRealUnitField G φ) {φ' : G.Ω 1 × Fin N → ℂ} (hφ' : IsMinimizer G a ν D φ') :
    φ' = φ := by
  obtain ⟨-, hφ'r, hφ'm⟩ := hφ'
  have hle := hφ'm φ hφ
  obtain ⟨-, h2⟩ := action_sub_ge hc₀ hν ha D hD hs hφ hφ'r
  have hzero : ∑ i, weightedSqNorm G (fun x => φ' (x, i) - φ (x, i)) ≤ 0 := by linarith
  have hnn : ∀ i ∈ (Finset.univ : Finset (Fin N)),
      0 ≤ weightedSqNorm G (fun x => φ' (x, i) - φ (x, i)) := fun i _ => weightedSqNorm_nonneg G _
  funext ⟨x, i⟩
  have h0 := (Finset.sum_eq_zero_iff_of_nonneg hnn).1
    (le_antisymm hzero (Finset.sum_nonneg hnn)) i (Finset.mem_univ i)
  have := weightedSqNorm_eq_zero h0.le x
  exact sub_eq_zero.1 this

end Positivity

end Balaban.Background
