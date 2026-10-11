/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Multiscale.AgmonDecay
public import Balaban.Multiscale.ScaleMismatch
public import Balaban.Multiscale.Constrained
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

/-!
# Weighted gradient bounds for the Green's function (both bond orientations)

`Balaban.Multiscale.agmon_bond_pointwise` is `Balaban.Multiscale.agmon_grad_pointwise` for an
arbitrary neighbour `b` of `x ∈ Ω₁` (the weight sits at the endpoint in `Ω₁`).  With the *two-sided
weighted gradient* (`Balaban.Multiscale.wGrad`)

`‖w ∂ u‖² = ∑_{x ∈ Ω₁} ∑_μ w(x)² (|ũ(x + e_μ) - ũ(x)|² + |ũ(x - e_μ) - ũ(x)|²)`

(each bond touching `Ω₁` counted from its end in `Ω₁`) this gives the weighted gradient bound for
`u = G_D(α) f` (`Balaban.Multiscale.agmon_wgrad_le`):

`‖w ∂ u‖² ≤ (10 / c) ‖ℓ w f‖²`,

the second estimate of GREEN.md §4.5, in the form used for the constraint sandwich.
-/

@[expose] public section

namespace Balaban.Multiscale

open Matrix Finset

variable {d L N₀ k : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}

section Pointwise

variable (G : GeneratingSet d L N₀ k ϱ)

/-- Pointwise form of the weighted gradient bound:
`w(x)² |ũ(x + e_μ) - ũ(x)|² ≤ 2 |v(x + e_μ) - v(x)|² + 8 ε² ℓ(x + e_μ)⁻² |v(x + e_μ)|²`. -/
theorem agmon_bond_pointwise {r : Torus d (N₀ * L ^ k) → ℝ} (hr : IsAgmonWeight G r) {ε : ℝ}
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1 / 2) (u : G.Ω 1 → ℂ) {x b : Torus d (N₀ * L ^ k)}
    (hx : x ∈ G.Ω 1) (hadj : Adj x b) :
    Real.exp (ε * r x) ^ 2 * ‖zeroExt (G.Ω 1) u b - zeroExt (G.Ω 1) u x‖ ^ 2 ≤
      2 * ‖agmonField G ε r u b - agmonField G ε r u x‖ ^ 2 +
        8 * ε ^ 2 * (invSqSpacing G b * ‖agmonField G ε r u b‖ ^ 2) := by
  set Ex := Real.exp (ε * r x) with hEx
  set Eb := Real.exp (ε * r b) with hEb
  have hEx0 : 0 < Ex := Real.exp_pos _
  have hEb0 : 0 < Eb := Real.exp_pos _
  set ut := zeroExt (G.Ω 1) u with hut
  set v := agmonField G ε r u with hv
  have hvx : v x = (Ex : ℂ) * ut x := rfl
  have hvb : v b = (Eb : ℂ) * ut b := rfl
  have hnn : 0 ≤ 8 * ε ^ 2 * (invSqSpacing G b * ‖v b‖ ^ 2) := by
    have := invSqSpacing_nonneg G b
    positivity
  have hnorm : Ex ^ 2 * ‖ut b - ut x‖ ^ 2 = ‖(Ex : ℂ) * (ut b - ut x)‖ ^ 2 := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hEx0.le, mul_pow]
  by_cases hbm : b ∈ G.Ω 1
  · have hbc := hr.bond x b hx hbm hadj
    have hc0 := G.bondCost_nonneg x b
    have hc1 : G.bondCost x b ≤ 1 := G.bondCost_le_one hx b
    have hεc : ε * G.bondCost x b ≤ 1 / 2 := by nlinarith
    have hBb := exp_sub_one_sq_le hε0 hc0 hεc (G.bondCost_le_inv_right x b)
    rw [← invSqSpacing_eq G hbm] at hBb
    have h2 := exp_sq_sub_le hε0 (show |r b - r x| ≤ G.bondCost x b by rwa [abs_sub_comm])
    set B := (Real.exp (ε * G.bondCost x b) - 1) ^ 2 with hB
    -- decomposition
    have hdec : (Ex : ℂ) * (ut b - ut x) = (v b - v x) + ((Ex / Eb - 1 : ℝ) : ℂ) * v b := by
      rw [hvb, hvx]
      have : (Eb : ℂ) ≠ 0 := by exact_mod_cast hEb0.ne'
      push_cast
      field_simp
      ring
    have hY : ‖((Ex / Eb - 1 : ℝ) : ℂ) * v b‖ ^ 2 ≤ B * ‖v b‖ ^ 2 := by
      rw [norm_mul, Complex.norm_real, mul_pow, Real.norm_eq_abs, sq_abs]
      refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
      have : (Ex / Eb - 1) ^ 2 = (Eb - Ex) ^ 2 / Eb ^ 2 := by field_simp; ring
      rw [this, div_le_iff₀ (by positivity)]
      have h2' : (Eb - Ex) ^ 2 ≤ B * Eb ^ 2 := h2
      exact h2'
    have hsum : ‖(v b - v x) + ((Ex / Eb - 1 : ℝ) : ℂ) * v b‖ ^ 2 ≤
        2 * ‖v b - v x‖ ^ 2 + 2 * ‖((Ex / Eb - 1 : ℝ) : ℂ) * v b‖ ^ 2 := by
      have h1 := norm_add_le (v b - v x) (((Ex / Eb - 1 : ℝ) : ℂ) * v b)
      have h3 := pow_le_pow_left₀ (norm_nonneg _) h1 2
      nlinarith [sq_nonneg (‖v b - v x‖ - ‖((Ex / Eb - 1 : ℝ) : ℂ) * v b‖)]
    rw [hnorm, hdec]
    have hBv : B * ‖v b‖ ^ 2 ≤ 4 * ε ^ 2 * invSqSpacing G b * ‖v b‖ ^ 2 :=
      mul_le_mul_of_nonneg_right hBb (sq_nonneg _)
    have hY2 : 2 * ‖((Ex / Eb - 1 : ℝ) : ℂ) * v b‖ ^ 2 ≤
        8 * ε ^ 2 * (invSqSpacing G b * ‖v b‖ ^ 2) :=
      calc 2 * ‖((Ex / Eb - 1 : ℝ) : ℂ) * v b‖ ^ 2
          ≤ 2 * (4 * ε ^ 2 * invSqSpacing G b * ‖v b‖ ^ 2) :=
            mul_le_mul_of_nonneg_left (hY.trans hBv) (by norm_num)
        _ = _ := by ring
    linarith [hsum, hY2]
  · have hub : ut b = 0 := zeroExt_not_mem _ _ hbm
    have hvb0 : v b = 0 := by rw [hvb, hub]; simp
    rw [hnorm, hub, zero_sub, mul_neg, norm_neg]
    have : (Ex : ℂ) * ut x = v x := rfl
    rw [this, hvb0, zero_sub, norm_neg]
    simp only [norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero,
      add_zero]
    nlinarith [sq_nonneg ‖v x‖]


end Pointwise

section Grad

variable (G : GeneratingSet d L N₀ k ϱ)

/-- The two-sided weighted gradient `‖w ∂ u‖²`: for every `x ∈ Ω₁` and direction `μ`, the two bonds
at `x` are weighted by `w(x)² = exp (2 ε r(x))`. -/
noncomputable def wGrad (ε : ℝ) (r : Torus d (N₀ * L ^ k) → ℝ) (u : G.Ω 1 → ℂ) : ℝ :=
  ∑ x ∈ G.Ω 1, ∑ μ : Fin d, Real.exp (ε * r x) ^ 2 *
    (‖zeroExt (G.Ω 1) u (x + Pi.single μ 1) - zeroExt (G.Ω 1) u x‖ ^ 2 +
      ‖zeroExt (G.Ω 1) u (x - Pi.single μ 1) - zeroExt (G.Ω 1) u x‖ ^ 2)

theorem wGrad_nonneg (ε : ℝ) (r : Torus d (N₀ * L ^ k) → ℝ) (u : G.Ω 1 → ℂ) :
    0 ≤ wGrad G ε r u :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity

theorem sum_shift_cEnergy_back (v : Torus d (N₀ * L ^ k) → ℂ) :
    ∑ x : Torus d (N₀ * L ^ k), ∑ μ : Fin d, ‖v (x - Pi.single μ 1) - v x‖ ^ 2 = cEnergy v := by
  have e : ∀ μ : Fin d, ∑ x : Torus d (N₀ * L ^ k), ‖v (x - Pi.single μ 1) - v x‖ ^ 2 =
      ∑ x : Torus d (N₀ * L ^ k), ‖v (x + Pi.single μ 1) - v x‖ ^ 2 := by
    intro μ
    have := sum_shift (Pi.single μ 1) (fun x : Torus d (N₀ * L ^ k) => ‖v (x - Pi.single μ 1) - v x‖ ^ 2)
    simp only [add_sub_cancel_right] at this
    rw [← this]
    exact Finset.sum_congr rfl fun x _ => by rw [norm_sub_rev]
  calc _ = ∑ μ : Fin d, ∑ x : Torus d (N₀ * L ^ k), ‖v (x - Pi.single μ 1) - v x‖ ^ 2 :=
        Finset.sum_comm
    _ = ∑ μ : Fin d, ∑ x : Torus d (N₀ * L ^ k), ‖v (x + Pi.single μ 1) - v x‖ ^ 2 :=
        Finset.sum_congr rfl fun μ _ => e μ
    _ = cEnergy v := Finset.sum_comm

theorem sum_shift_cwsq_back (v : Torus d (N₀ * L ^ k) → ℂ) :
    ∑ x : Torus d (N₀ * L ^ k), ∑ μ : Fin d,
        invSqSpacing G (x - Pi.single μ 1) * ‖v (x - Pi.single μ 1)‖ ^ 2 = d * cwsq G v := by
  rw [Finset.sum_comm]
  have : ∀ μ : Fin d, ∑ x : Torus d (N₀ * L ^ k),
      invSqSpacing G (x - Pi.single μ 1) * ‖v (x - Pi.single μ 1)‖ ^ 2 = cwsq G v := fun μ => by
    have := sum_shift (-Pi.single μ 1) (fun x => invSqSpacing G x * ‖v x‖ ^ 2)
    simpa [sub_eq_add_neg, cwsq] using this
  simp only [this, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- **Weighted gradient bound** (GREEN.md §4.5): for `H_D(α) u = f`,
`‖w ∂ u‖² ≤ (10 / c) ‖ℓ w f‖²`, `w = exp (ε r)`, `0 ≤ ε ≤ ε₀`. -/
theorem agmon_wgrad_le (hd : 0 < d) {a : ℕ → ℝ} {ν : ℝ} (hν : 0 ≤ ν)
    (ha : IsAdmissibleWeights k a) (α : G.Ω 1 → ℂ)
    (hα : ∀ x, ‖α x‖ ≤ coerciveConst d / (2 * (G.spacing x) ^ 2))
    {r : Torus d (N₀ * L ^ k) → ℝ} (hr : IsAgmonWeight G r) {ε : ℝ} (hε0 : 0 ≤ ε)
    (hε1 : ε ≤ agmonRate d) {u f : G.Ω 1 → ℂ} (hu : dirichletOperator G a ν α *ᵥ u = f) :
    wGrad G ε r u ≤ 10 / poincareConst d * agmonSource G ε r f := by
  have hp0 := poincareConst_pos hd
  have hε12 : ε ≤ 1 / 2 := by linarith [agmonRate_le hd]
  set v := agmonField G ε r u with hv
  have hS := agmon_wsq_le G hd hν ha α hα hr hε0 hε1 hu
  have hE := agmon_cEnergy_le G hd hν ha α hα hr hε0 hε1 hu
  have hHh0 := agmonSource_nonneg G ε r f
  set B : Torus d (N₀ * L ^ k) → ℝ := fun x => ∑ μ : Fin d,
      ((2 * ‖v (x + Pi.single μ 1) - v x‖ ^ 2 +
        8 * ε ^ 2 * (invSqSpacing G (x + Pi.single μ 1) * ‖v (x + Pi.single μ 1)‖ ^ 2)) +
       (2 * ‖v (x - Pi.single μ 1) - v x‖ ^ 2 +
        8 * ε ^ 2 * (invSqSpacing G (x - Pi.single μ 1) * ‖v (x - Pi.single μ 1)‖ ^ 2))) with hB
  have hB0 : ∀ x, 0 ≤ B x := fun x => Finset.sum_nonneg fun μ _ => by
    have h1 := invSqSpacing_nonneg G (x + Pi.single μ 1)
    have h2 := invSqSpacing_nonneg G (x - Pi.single μ 1)
    positivity
  have hpt : ∀ x ∈ G.Ω 1, ∑ μ : Fin d, Real.exp (ε * r x) ^ 2 *
      (‖zeroExt (G.Ω 1) u (x + Pi.single μ 1) - zeroExt (G.Ω 1) u x‖ ^ 2 +
        ‖zeroExt (G.Ω 1) u (x - Pi.single μ 1) - zeroExt (G.Ω 1) u x‖ ^ 2) ≤ B x := by
    intro x hx
    refine Finset.sum_le_sum fun μ _ => ?_
    have h1 := agmon_bond_pointwise G hr hε0 hε12 u hx (b := x + Pi.single μ 1)
      ⟨μ, Or.inl rfl⟩
    have h2 := agmon_bond_pointwise G hr hε0 hε12 u hx (b := x - Pi.single μ 1)
      ⟨μ, Or.inr (by simp)⟩
    rw [mul_add]
    exact add_le_add h1 h2
  have hsum : wGrad G ε r u ≤ ∑ x, B x := by
    calc wGrad G ε r u ≤ ∑ x ∈ G.Ω 1, B x := Finset.sum_le_sum fun x hx => hpt x hx
      _ ≤ ∑ x, B x := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          fun x _ _ => hB0 x
  have hBsum : ∑ x, B x = 4 * cEnergy v + 16 * ε ^ 2 * (d * cwsq G v) := by
    have e1 : ∑ x : Torus d (N₀ * L ^ k), ∑ μ : Fin d, ‖v (x + Pi.single μ 1) - v x‖ ^ 2 =
        cEnergy v := rfl
    have e2 := sum_shift_cEnergy_back (d := d) (L := L) (N₀ := N₀) (k := k) v
    have e3 := sum_shift_cwsq G v
    have e4 := sum_shift_cwsq_back G v
    simp only [hB, Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [e1, e2, e3, e4]
    ring
  have hfin := numeric_grad hd hε0 hε1 hHh0 hS hE
  have h2 : 2 * (2 * cEnergy v + 8 * ε ^ 2 * (d * cwsq G v)) ≤ 2 * (5 / poincareConst d *
      agmonSource G ε r f) := by linarith
  calc wGrad G ε r u ≤ _ := hsum
    _ = 2 * (2 * cEnergy v + 8 * ε ^ 2 * (d * cwsq G v)) := by rw [hBsum]; ring
    _ ≤ _ := h2
    _ = _ := by ring

end Grad

end Balaban.Multiscale
