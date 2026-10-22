/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Multiscale.Agmon
public import Balaban.Multiscale.AgmonWeight
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

/-!
# Block-to-block decay (GREEN.md Corollary 4.6, first half of G-2(i))

For `f` supported in the `j'`-block `Δ_{j'}(y')` (`y'` in layer `j'`) and `u` with
`H_D(α) u = f`, the Agmon inequality with the truncated path distance to `y'` gives, for every
`t ≥ 0` with `t ≤ d(y, y')` (`y` in layer `j`) and `0 ≤ ε ≤ ε₀`:

* `Σ_{x ∈ Δ_j(y)} |ũ(x)|² ≤ (8 / c²) ℓ_j² ℓ_{j'}² e^{-2εt} ‖f‖²`,
* `Σ_{x ∈ Δ_j(y)} Σ_μ |ũ(x + e_μ) - ũ(x)|² ≤ (10 / c) ℓ_{j'}² e^{-2εt} ‖f‖²`,

`c = poincareConst d`, `ℓ_j = L ^ j` (`Balaban.Multiscale.agmon_block`).  Taking `t = d(y, y')` when
the distance is finite, and `t → ∞` otherwise, this is the exponential decay in the path metric.
-/

@[expose] public section

namespace Balaban.Multiscale

open Finset Matrix Balaban

variable {d L N₀ k : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}

namespace GeneratingSet

/-- The `j`-block `Δ_j(y)` of the fine torus containing `y`. -/
def blk (_G : GeneratingSet d L N₀ k ϱ) (j : ℕ) (y : Torus d (N₀ * L ^ k)) :
    Finset (Torus d (N₀ * L ^ k)) :=
  Finset.univ.filter fun x => jBlock d L N₀ k j x = jBlock d L N₀ k j y

theorem mem_blk {G : GeneratingSet d L N₀ k ϱ} {j : ℕ} {y x : Torus d (N₀ * L ^ k)} :
    x ∈ G.blk j y ↔ jBlock d L N₀ k j x = jBlock d L N₀ k j y := by
  simp [blk]

end GeneratingSet

theorem exp_eight_mul_le_two {s : ℝ} (h0 : 0 ≤ s) (h1 : s ≤ 1 / 32) : Real.exp (8 * s) ≤ 2 := by
  have h := Real.exp_bound_div_one_sub_of_interval (x := 8 * s) (by positivity) (by linarith)
  have : 1 / (1 - 8 * s) ≤ 2 := by
    rw [div_le_iff₀ (by linarith)]; linarith
  linarith

theorem rate_mul_le {ε : ℝ} (hd : 0 < d) (hε1 : ε ≤ agmonRate d) :
    ε * d ≤ 1 / 32 := by
  have hdd : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hp := poincareConst_le_half d
  have hp0 := poincareConst_pos hd
  have : ε * d ≤ agmonRate d * d := by gcongr
  have e : agmonRate d * d = poincareConst d / 16 := by
    unfold agmonRate; field_simp
  linarith

theorem sum_shift_cwsq (G : GeneratingSet d L N₀ k ϱ) (v : Torus d (N₀ * L ^ k) → ℂ) :
    ∑ x : Torus d (N₀ * L ^ k), ∑ μ : Fin d,
        invSqSpacing G (x + Pi.single μ 1) * ‖v (x + Pi.single μ 1)‖ ^ 2 = d * cwsq G v := by
  rw [Finset.sum_comm]
  have : ∀ μ : Fin d, ∑ x : Torus d (N₀ * L ^ k),
      invSqSpacing G (x + Pi.single μ 1) * ‖v (x + Pi.single μ 1)‖ ^ 2 = cwsq G v := fun μ =>
    sum_shift (Pi.single μ 1) (fun x => invSqSpacing G x * ‖v x‖ ^ 2)
  simp only [this, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- A support condition on `f` transfers to its zero extension. -/
theorem zeroExt_supp_of (G : GeneratingSet d L N₀ k ϱ) {f : G.Ω 1 → ℂ} {P : Torus d (N₀ * L ^ k) → Prop}
    (hsupp : ∀ x : G.Ω 1, f x ≠ 0 → P x) (x : Torus d (N₀ * L ^ k))
    (hx : zeroExt (G.Ω 1) f x ≠ 0) : P x := by
  have hxm : x ∈ G.Ω 1 := by
    by_contra h; exact hx (zeroExt_not_mem _ _ h)
  have hfx : f ⟨x, hxm⟩ ≠ 0 := by
    simpa [zeroExt, hxm] using hx
  exact hsupp ⟨x, hxm⟩ hfx

section Pieces

variable (G : GeneratingSet d L N₀ k ϱ)

/-- The weighted source norm is controlled by the plain one, when `f̃` is supported in a block of
the layer `j'`, on which the weight exponent is at most `2 d` (fields on the torus; shared core). -/
theorem agmonSource_le_fun {r : Torus d (N₀ * L ^ k) → ℝ} (hr : IsAgmonWeight G r) {ε : ℝ}
    (hε0 : 0 ≤ ε) {j' : ℕ} (hj'1 : 1 ≤ j') (hj'k : j' ≤ k) {y' : Torus d (N₀ * L ^ k)}
    (hy' : y' ∈ G.layer j') (hry' : r y' = 0) {ft : Torus d (N₀ * L ^ k) → ℂ}
    (hsupp : ∀ x, ft x ≠ 0 → jBlock d L N₀ k j' x = jBlock d L N₀ k j' y') :
    ∑ x, (G.spacing x) ^ 2 * ‖((Real.exp (ε * r x) : ℝ) : ℂ) * ft x‖ ^ 2 ≤
      ((L : ℝ) ^ j') ^ 2 * Real.exp (4 * ε * d) * Green.sqNorm ft := by
  unfold Green.sqNorm
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun x _ => ?_
  by_cases hx : ft x = 0
  · simp [hx]
  · have hxb := hsupp x hx
    have hxl : x ∈ G.layer j' := (G.mem_layer_iff hj'1 hj'k hxb).2 hy'
    rw [G.spacing_eq hj'1 hj'k hxl]
    have hrx : r x ≤ 2 * d := by
      have := hr.block j' hj'1 hj'k y' x hy' hxb
      rw [hry'] at this
      have := (abs_le.1 this).1
      linarith
    have hw : Real.exp (ε * r x) ≤ Real.exp (ε * (2 * d)) :=
      Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hrx hε0)
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le, mul_pow]
    have e4 : Real.exp (4 * ε * d) = Real.exp (ε * (2 * d)) ^ 2 := by
      rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
    rw [e4]
    have h2 : Real.exp (ε * r x) ^ 2 ≤ Real.exp (ε * (2 * d)) ^ 2 :=
      pow_le_pow_left₀ (Real.exp_pos _).le hw 2
    have hL2 : 0 ≤ ((L : ℝ) ^ j') ^ 2 := by positivity
    calc ((L : ℝ) ^ j') ^ 2 * (Real.exp (ε * r x) ^ 2 * ‖ft x‖ ^ 2)
        ≤ ((L : ℝ) ^ j') ^ 2 * (Real.exp (ε * (2 * d)) ^ 2 * ‖ft x‖ ^ 2) := by
          gcongr
      _ = _ := by ring

/-- The weighted source norm is controlled by the plain one, when `f` is supported in a block of
the layer `j'`, on which the weight exponent is at most `2 d`. -/
theorem agmonSource_le {r : Torus d (N₀ * L ^ k) → ℝ} (hr : IsAgmonWeight G r) {ε : ℝ}
    (hε0 : 0 ≤ ε) {j' : ℕ} (hj'1 : 1 ≤ j') (hj'k : j' ≤ k) {y' : Torus d (N₀ * L ^ k)}
    (hy' : y' ∈ G.layer j') (hry' : r y' = 0) {f : G.Ω 1 → ℂ}
    (hsupp : ∀ x : G.Ω 1, f x ≠ 0 → jBlock d L N₀ k j' x = jBlock d L N₀ k j' y') :
    agmonSource G ε r f ≤ ((L : ℝ) ^ j') ^ 2 * Real.exp (4 * ε * d) * Green.sqNorm f := by
  rw [agmonSource, ← sqNorm_zeroExt (G.Ω 1) f]
  exact agmonSource_le_fun G hr hε0 hj'1 hj'k hy' hry' (zeroExt_supp_of G hsupp)

/-- On the block `Δ_j(y)` the weight is at least `exp (ε (t - 2 d))`, `t = r(y)`. -/
theorem blk_weight_ge {r : Torus d (N₀ * L ^ k) → ℝ} (hr : IsAgmonWeight G r) {ε : ℝ}
    (hε0 : 0 ≤ ε) {j : ℕ} (hj1 : 1 ≤ j) (hjk : j ≤ k) {y : Torus d (N₀ * L ^ k)}
    (hy : y ∈ G.layer j) {x : Torus d (N₀ * L ^ k)} (hx : x ∈ G.blk j y) :
    Real.exp (2 * ε * (r y - 2 * d)) ≤ Real.exp (ε * r x) ^ 2 := by
  have hxb := G.mem_blk.1 hx
  have h := hr.block j hj1 hjk y x hy hxb
  have := (abs_le.1 h).2
  rw [sq, ← Real.exp_add]
  exact Real.exp_le_exp.2 (by nlinarith)

/-- The weighted norm `‖ℓ⁻¹ w ũ‖²` dominates the block norm of `ũ` (lower bound on the weight;
fields on the torus; shared core). -/
theorem blk_lower_fun {r : Torus d (N₀ * L ^ k) → ℝ} (hr : IsAgmonWeight G r) {ε : ℝ}
    (hε0 : 0 ≤ ε) {j : ℕ} (hj1 : 1 ≤ j) (hjk : j ≤ k) {y : Torus d (N₀ * L ^ k)}
    (hy : y ∈ G.layer j) (ut : Torus d (N₀ * L ^ k) → ℂ) :
    (((L : ℝ) ^ j) ^ 2)⁻¹ * Real.exp (2 * ε * (r y - 2 * d)) *
        ∑ x ∈ G.blk j y, ‖ut x‖ ^ 2 ≤
      cwsq G (fun x => ((Real.exp (ε * r x) : ℝ) : ℂ) * ut x) := by
  calc _ = ∑ x ∈ G.blk j y, (((L : ℝ) ^ j) ^ 2)⁻¹ * Real.exp (2 * ε * (r y - 2 * d)) *
          ‖ut x‖ ^ 2 := by rw [Finset.mul_sum]
    _ ≤ ∑ x ∈ G.blk j y, invSqSpacing G x *
          ‖((Real.exp (ε * r x) : ℝ) : ℂ) * ut x‖ ^ 2 := by
        refine Finset.sum_le_sum fun x hx => ?_
        have hxl : x ∈ G.layer j := (G.mem_layer_iff hj1 hjk (G.mem_blk.1 hx)).2 hy
        have hxm : x ∈ G.Ω 1 := G.layer_subset hj1 hjk hxl
        rw [invSqSpacing_eq G hxm, G.spacing_eq hj1 hjk hxl, norm_mul, Complex.norm_real,
          Real.norm_of_nonneg (Real.exp_pos _).le, mul_pow]
        have := blk_weight_ge G hr hε0 hj1 hjk hy hx
        rw [mul_assoc]
        gcongr
    _ ≤ _ := by
        unfold cwsq
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun x _ _ =>
          mul_nonneg (invSqSpacing_nonneg G x) (sq_nonneg _)

/-- The weighted norm `‖ℓ⁻¹ v‖²` dominates the block norm of `ũ` (lower bound on the weight). -/
theorem blk_lower {r : Torus d (N₀ * L ^ k) → ℝ} (hr : IsAgmonWeight G r) {ε : ℝ}
    (hε0 : 0 ≤ ε) {j : ℕ} (hj1 : 1 ≤ j) (hjk : j ≤ k) {y : Torus d (N₀ * L ^ k)}
    (hy : y ∈ G.layer j) (u : G.Ω 1 → ℂ) :
    (((L : ℝ) ^ j) ^ 2)⁻¹ * Real.exp (2 * ε * (r y - 2 * d)) *
        ∑ x ∈ G.blk j y, ‖zeroExt (G.Ω 1) u x‖ ^ 2 ≤ cwsq G (agmonField G ε r u) :=
  blk_lower_fun G hr hε0 hj1 hjk hy (zeroExt (G.Ω 1) u)

/-- The weighted gradient on the block is controlled by the energy and the weighted norm (fields
on the torus vanishing off `Ω₁`; shared core). -/
theorem blk_grad_le_fun {r : Torus d (N₀ * L ^ k) → ℝ} (hr : IsAgmonWeight G r) {ε : ℝ}
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1 / 2) {j : ℕ} (hj1 : 1 ≤ j) (hjk : j ≤ k)
    {y : Torus d (N₀ * L ^ k)} (hy : y ∈ G.layer j) {ut : Torus d (N₀ * L ^ k) → ℂ}
    (hut : ∀ x, x ∉ G.Ω 1 → ut x = 0) :
    Real.exp (2 * ε * (r y - 2 * d)) * ∑ x ∈ G.blk j y, ∑ μ : Fin d,
        ‖ut (x + Pi.single μ 1) - ut x‖ ^ 2 ≤
      2 * cEnergy (fun x => ((Real.exp (ε * r x) : ℝ) : ℂ) * ut x) +
        8 * ε ^ 2 * (d * cwsq G (fun x => ((Real.exp (ε * r x) : ℝ) : ℂ) * ut x)) := by
  set v : Torus d (N₀ * L ^ k) → ℂ := fun x => ((Real.exp (ε * r x) : ℝ) : ℂ) * ut x with hv
  calc _ = ∑ x ∈ G.blk j y, ∑ μ : Fin d, Real.exp (2 * ε * (r y - 2 * d)) *
          ‖ut (x + Pi.single μ 1) - ut x‖ ^ 2 := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun x _ => by rw [Finset.mul_sum]
    _ ≤ ∑ x ∈ G.blk j y, ∑ μ : Fin d,
          (2 * ‖v (x + Pi.single μ 1) - v x‖ ^ 2 +
            8 * ε ^ 2 * (invSqSpacing G (x + Pi.single μ 1) * ‖v (x + Pi.single μ 1)‖ ^ 2)) := by
        refine Finset.sum_le_sum fun x hx => Finset.sum_le_sum fun μ _ => ?_
        have hxl : x ∈ G.layer j := (G.mem_layer_iff hj1 hjk (G.mem_blk.1 hx)).2 hy
        have hxm : x ∈ G.Ω 1 := G.layer_subset hj1 hjk hxl
        have h1 := agmon_grad_pointwise_fun G hr hε0 hε1 hut hxm μ
        calc _ ≤ Real.exp (ε * r x) ^ 2 * ‖ut (x + Pi.single μ 1) - ut x‖ ^ 2 :=
              mul_le_mul_of_nonneg_right (blk_weight_ge G hr hε0 hj1 hjk hy hx) (sq_nonneg _)
          _ ≤ _ := h1
    _ ≤ ∑ x, ∑ μ : Fin d,
          (2 * ‖v (x + Pi.single μ 1) - v x‖ ^ 2 +
            8 * ε ^ 2 * (invSqSpacing G (x + Pi.single μ 1) * ‖v (x + Pi.single μ 1)‖ ^ 2)) := by
        refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun x _ _ => ?_
        refine Finset.sum_nonneg fun μ _ => ?_
        have := invSqSpacing_nonneg G (x + Pi.single μ 1)
        positivity
    _ = 2 * cEnergy v + 8 * ε ^ 2 * (d * cwsq G v) := by
        simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
        rw [sum_shift_cwsq]
        rfl

/-- The weighted gradient on the block is controlled by the energy and the weighted norm. -/
theorem blk_grad_le {r : Torus d (N₀ * L ^ k) → ℝ} (hr : IsAgmonWeight G r) {ε : ℝ}
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1 / 2) {j : ℕ} (hj1 : 1 ≤ j) (hjk : j ≤ k)
    {y : Torus d (N₀ * L ^ k)} (hy : y ∈ G.layer j) (u : G.Ω 1 → ℂ) :
    Real.exp (2 * ε * (r y - 2 * d)) * ∑ x ∈ G.blk j y, ∑ μ : Fin d,
        ‖zeroExt (G.Ω 1) u (x + Pi.single μ 1) - zeroExt (G.Ω 1) u x‖ ^ 2 ≤
      2 * cEnergy (agmonField G ε r u) + 8 * ε ^ 2 * (d * cwsq G (agmonField G ε r u)) :=
  blk_grad_le_fun G hr hε0 hε1 hj1 hjk hy (fun _ hx => zeroExt_not_mem _ _ hx)

end Pieces

/-! ### Numerical bookkeeping -/

theorem numeric_a {p A A' Z Et F X Hh S : ℝ} (hp : 0 < p) (hA : 0 ≤ A) (hA' : 0 ≤ A')
    (hZ : 0 ≤ Z) (hEt : 0 ≤ Et) (hF : 0 ≤ F)
    (hX : X ≤ A * (Et * Z) * S) (hS : S ≤ 4 / p ^ 2 * Hh) (hHh : Hh ≤ A' * Z * F)
    (hZZ : Z * Z ≤ 2) : X ≤ 8 / p ^ 2 * A * A' * Et * F := by
  have h1 : S ≤ 4 / p ^ 2 * (A' * Z * F) :=
    hS.trans (mul_le_mul_of_nonneg_left hHh (by positivity))
  calc X ≤ A * (Et * Z) * (4 / p ^ 2 * (A' * Z * F)) :=
        hX.trans (mul_le_mul_of_nonneg_left h1 (by positivity))
    _ = 4 / p ^ 2 * A * A' * Et * F * (Z * Z) := by ring
    _ ≤ 4 / p ^ 2 * A * A' * Et * F * 2 :=
        mul_le_mul_of_nonneg_left hZZ (by positivity)
    _ = _ := by ring

theorem numeric_b {p A' Z Et F Y Hh : ℝ} (hp : 0 < p) (hA' : 0 ≤ A') (hZ : 0 ≤ Z) (hEt : 0 ≤ Et)
    (hF : 0 ≤ F) (hY : Y ≤ (Et * Z) * (5 / p * Hh)) (hHh : Hh ≤ A' * Z * F)
    (hZZ : Z * Z ≤ 2) : Y ≤ 10 / p * A' * Et * F := by
  calc Y ≤ (Et * Z) * (5 / p * Hh) := hY
    _ ≤ (Et * Z) * (5 / p * (A' * Z * F)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hHh (by positivity)) (by positivity)
    _ = 5 / p * A' * Et * F * (Z * Z) := by ring
    _ ≤ 5 / p * A' * Et * F * 2 := mul_le_mul_of_nonneg_left hZZ (by positivity)
    _ = _ := by ring

theorem eps_sq_mul_le (hd : 0 < d) {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ agmonRate d) :
    ε ^ 2 * d ≤ poincareConst d ^ 2 / 256 := by
  have hdd : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hp0 := poincareConst_pos hd
  have e : agmonRate d * d = poincareConst d / 16 := by
    unfold agmonRate; field_simp
  have h1 : ε * d ≤ poincareConst d / 16 := by
    have : ε * d ≤ agmonRate d * d := by gcongr
    linarith
  have h2 : ε ≤ poincareConst d / 16 := by
    have : agmonRate d ≤ poincareConst d / 16 := by
      unfold agmonRate
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    linarith
  nlinarith [mul_le_mul h1 h2 hε0 (by positivity)]

/-- `2 E + 8 ε² d S ≤ (5 / c) ‖ℓ w f‖²` from the two Agmon bounds. -/
theorem numeric_grad (hd : 0 < d) {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ agmonRate d)
    {E S Hh : ℝ} (hHh0 : 0 ≤ Hh) (hS : S ≤ 4 / poincareConst d ^ 2 * Hh)
    (hE : E ≤ 2 / poincareConst d * Hh) :
    2 * E + 8 * ε ^ 2 * (d * S) ≤ 5 / poincareConst d * Hh := by
  have hp0 := poincareConst_pos hd
  have hph := poincareConst_le_half d
  have hε2 := eps_sq_mul_le hd hε0 hε1
  have h3 : 8 * ε ^ 2 * (d * S) ≤ 1 / 8 * Hh := by
    have hc : 0 ≤ 8 * ε ^ 2 * d :=
      mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg ε)) (Nat.cast_nonneg d)
    calc 8 * ε ^ 2 * (d * S) = (8 * ε ^ 2 * d) * S := by ring
      _ ≤ (8 * ε ^ 2 * d) * (4 / poincareConst d ^ 2 * Hh) := mul_le_mul_of_nonneg_left hS hc
      _ = (32 * (ε ^ 2 * d) / poincareConst d ^ 2) * Hh := by ring
      _ ≤ (32 * (poincareConst d ^ 2 / 256) / poincareConst d ^ 2) * Hh := by gcongr
      _ = 1 / 8 * Hh := by field_simp; ring
  have h4 : 1 / 8 * Hh ≤ 1 / poincareConst d * Hh := by
    have : 1 / 8 ≤ 1 / poincareConst d := by
      rw [div_le_div_iff₀ (by norm_num) hp0]; linarith
    exact mul_le_mul_of_nonneg_right this hHh0
  have e : 5 / poincareConst d * Hh = 4 / poincareConst d * Hh + 1 / poincareConst d * Hh := by ring
  have e2 : 2 * (2 / poincareConst d * Hh) = 4 / poincareConst d * Hh := by ring
  linarith

/-- **Agmon block decay**, for fields `ũ, f̃` on the torus with `ũ = 0` off `Ω₁` and the equation
`f̃ = (H + α) ũ` wherever `ũ ≠ 0` (shared core; see the module docstring). -/
theorem agmon_block_fun (G : GeneratingSet d L N₀ k ϱ) (hd : 0 < d) {a : ℕ → ℝ} {ν : ℝ}
    (hν : 0 ≤ ν) (ha : IsAdmissibleWeights k a) (αt : Torus d (N₀ * L ^ k) → ℂ)
    (hα : ∀ x ∈ G.Ω 1, ‖αt x‖ ≤ coerciveConst d / (2 * (G.spacing x) ^ 2))
    {j j' : ℕ} (hj1 : 1 ≤ j) (hjk : j ≤ k) (hj'1 : 1 ≤ j') (hj'k : j' ≤ k)
    {y y' : Torus d (N₀ * L ^ k)} (hy : y ∈ G.layer j) (hy' : y' ∈ G.layer j')
    {ut ft : Torus d (N₀ * L ^ k) → ℂ} (hut : ∀ x, x ∉ G.Ω 1 → ut x = 0)
    (heq : ∀ x, ut x ≠ 0 → ft x = ((fullMatrix G a ν).map (algebraMap ℝ ℂ) *ᵥ ut) x + αt x * ut x)
    (hsupp : ∀ x, ft x ≠ 0 → jBlock d L N₀ k j' x = jBlock d L N₀ k j' y')
    {t : ℝ} (ht0 : 0 ≤ t) (ht : ENNReal.ofReal t ≤ G.pathDist y y') {ε : ℝ} (hε0 : 0 ≤ ε)
    (hε1 : ε ≤ agmonRate d) :
    (∑ x ∈ G.blk j y, ‖ut x‖ ^ 2 ≤
        8 / poincareConst d ^ 2 * ((L : ℝ) ^ j) ^ 2 * ((L : ℝ) ^ j') ^ 2 * Real.exp (-(2 * ε * t)) *
          Green.sqNorm ft) ∧
    (∑ x ∈ G.blk j y, ∑ μ : Fin d, ‖ut (x + Pi.single μ 1) - ut x‖ ^ 2 ≤
        10 / poincareConst d * ((L : ℝ) ^ j') ^ 2 * Real.exp (-(2 * ε * t)) *
          Green.sqNorm ft) := by
  have hp0 := poincareConst_pos hd
  have hε12 : ε ≤ 1 / 2 := by linarith [agmonRate_le hd]
  have hεd := rate_mul_le hd hε1
  have h8 : Real.exp (8 * (ε * d)) ≤ 2 := exp_eight_mul_le_two (by positivity) hεd
  have hr : IsAgmonWeight G (G.truncDist y' t) := G.isAgmonWeight_truncDist y' t
  have hry : G.truncDist y' t y = t := G.truncDist_eq_of_le ht0 ht
  have hry' : G.truncDist y' t y' = 0 := G.truncDist_self (G.layer_subset hj'1 hj'k hy') t
  have hS := agmon_wsq_le_fun G hd hν ha αt hα hr hε0 hε1 hut heq
  have hE := agmon_cEnergy_le_fun G hd hν ha αt hα hr hε0 hε1 hut heq
  have hsrc := agmonSource_le_fun G hr hε0 hj'1 hj'k hy' hry' hsupp
  have hlow := blk_lower_fun G hr hε0 hj1 hjk hy ut
  have hgrad := blk_grad_le_fun G hr hε0 hε12 hj1 hjk hy hut
  rw [hry] at hlow hgrad
  have hHh0 : 0 ≤ ∑ x, (G.spacing x) ^ 2 *
      ‖((Real.exp (ε * G.truncDist y' t x) : ℝ) : ℂ) * ft x‖ ^ 2 :=
    Finset.sum_nonneg fun _ _ => by positivity
  have hZZ : Real.exp (4 * ε * d) * Real.exp (4 * ε * d) ≤ 2 := by
    rw [← Real.exp_add]
    have : 4 * ε * d + 4 * ε * d = 8 * (ε * d) := by ring
    rw [this]; exact h8
  have hE20 : 0 < Real.exp (2 * ε * (t - 2 * d)) := Real.exp_pos _
  have hA0 : 0 < ((L : ℝ) ^ j) ^ 2 := by
    have : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
    positivity
  have hLj : ((L : ℝ) ^ j) ≠ 0 := by
    have : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
    positivity
  have hE2inv : (Real.exp (2 * ε * (t - 2 * d)))⁻¹ =
      Real.exp (-(2 * ε * t)) * Real.exp (4 * ε * d) := by
    rw [← Real.exp_neg, ← Real.exp_add]; congr 1; ring
  have hsf := Green.sqNorm_nonneg ft
  refine ⟨?_, ?_⟩
  · have hX2 : ∑ x ∈ G.blk j y, ‖ut x‖ ^ 2 ≤ ((L : ℝ) ^ j) ^ 2 *
        (Real.exp (-(2 * ε * t)) * Real.exp (4 * ε * d)) *
          cwsq G (fun x => ((Real.exp (ε * G.truncDist y' t x) : ℝ) : ℂ) * ut x) := by
      rw [← hE2inv]
      have := mul_le_mul_of_nonneg_left hlow
        (mul_nonneg hA0.le (inv_nonneg.2 hE20.le))
      calc _ = (((L : ℝ) ^ j) ^ 2 * (Real.exp (2 * ε * (t - 2 * d)))⁻¹) *
            ((((L : ℝ) ^ j) ^ 2)⁻¹ * Real.exp (2 * ε * (t - 2 * d)) *
              ∑ x ∈ G.blk j y, ‖ut x‖ ^ 2) := by field_simp
        _ ≤ _ := this
        _ = _ := by ring
    exact numeric_a hp0 hA0.le (by positivity) (Real.exp_pos _).le (Real.exp_pos _).le hsf
      hX2 hS hsrc hZZ
  · have hY2 : ∑ x ∈ G.blk j y, ∑ μ : Fin d, ‖ut (x + Pi.single μ 1) - ut x‖ ^ 2 ≤
        (Real.exp (-(2 * ε * t)) * Real.exp (4 * ε * d)) *
          (5 / poincareConst d * ∑ x, (G.spacing x) ^ 2 *
            ‖((Real.exp (ε * G.truncDist y' t x) : ℝ) : ℂ) * ft x‖ ^ 2) := by
      have h1 := hgrad.trans (numeric_grad hd hε0 hε1 hHh0 hS hE)
      rw [← hE2inv, ← div_eq_inv_mul, le_div_iff₀ hE20]
      linarith
    exact numeric_b hp0 (by positivity) (Real.exp_pos _).le (Real.exp_pos _).le hsf hY2 hsrc hZZ

/-- **Agmon block decay.**  See the module docstring. -/
theorem agmon_block (G : GeneratingSet d L N₀ k ϱ) (hd : 0 < d) {a : ℕ → ℝ} {ν : ℝ} (hν : 0 ≤ ν)
    (ha : IsAdmissibleWeights k a) (α : G.Ω 1 → ℂ)
    (hα : ∀ x, ‖α x‖ ≤ coerciveConst d / (2 * (G.spacing x) ^ 2))
    {j j' : ℕ} (hj1 : 1 ≤ j) (hjk : j ≤ k) (hj'1 : 1 ≤ j') (hj'k : j' ≤ k)
    {y y' : Torus d (N₀ * L ^ k)} (hy : y ∈ G.layer j) (hy' : y' ∈ G.layer j')
    {u f : G.Ω 1 → ℂ} (hu : dirichletOperator G a ν α *ᵥ u = f)
    (hsupp : ∀ x : G.Ω 1, f x ≠ 0 → jBlock d L N₀ k j' x = jBlock d L N₀ k j' y')
    {t : ℝ} (ht0 : 0 ≤ t) (ht : ENNReal.ofReal t ≤ G.pathDist y y') {ε : ℝ} (hε0 : 0 ≤ ε)
    (hε1 : ε ≤ agmonRate d) :
    (∑ x ∈ G.blk j y, ‖zeroExt (G.Ω 1) u x‖ ^ 2 ≤
        8 / poincareConst d ^ 2 * ((L : ℝ) ^ j) ^ 2 * ((L : ℝ) ^ j') ^ 2 * Real.exp (-(2 * ε * t)) *
          Green.sqNorm f) ∧
    (∑ x ∈ G.blk j y, ∑ μ : Fin d,
        ‖zeroExt (G.Ω 1) u (x + Pi.single μ 1) - zeroExt (G.Ω 1) u x‖ ^ 2 ≤
        10 / poincareConst d * ((L : ℝ) ^ j') ^ 2 * Real.exp (-(2 * ε * t)) * Green.sqNorm f) := by
  rw [← sqNorm_zeroExt (G.Ω 1) f]
  exact agmon_block_fun G hd hν ha (zeroExt (G.Ω 1) α)
    (fun x hx => by rw [zeroExt_mem (G.Ω 1) α ⟨x, hx⟩]; exact hα ⟨x, hx⟩) hj1 hjk hj'1 hj'k hy hy'
    (fun _ hx => zeroExt_not_mem _ _ hx) (zeroExt_dirichlet_eq G hu) (zeroExt_supp_of G hsupp)
    ht0 ht hε0 hε1

end Balaban.Multiscale
