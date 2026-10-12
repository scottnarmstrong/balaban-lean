/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.SmallField.RenormTheorem
public import Balaban.Frozen.Model.Torus

/-!
# The antisymmetric term and its sum over a torus (Theorem 2.1 (b))

* `Aterm_eq_sum`: `A_0(ψ) = ½ Σ_x a^{(j)}(x) (ψ(x)·ψ(x) - ψ(0)·ψ(0))` for bounded `ψ·ψ`;
* `Aterm_torus_sum`: on a torus, for the periodic lift of `ψ_T`, the sum over the centres `y`
  of the terms `A_y` vanishes (no parity of `a^{(j)}` is needed).
-/

@[expose] public section

open Metric Set Matrix

namespace Balaban.SmallField

variable {d N : ℕ}

variable {T : TermFamily d N} {i₀ i₁ : Fin N} {ν ρ E₀ κ A K₀ : ℝ}
  {Dom : Set ((Site d → Spin N) × Spin N)}

theorem aCoefX_zero {X : Finset (Site d)} {x : Site d} (hx : x ∉ X) :
    aCoefX T i₀ ν X x = 0 := by
  simp [aCoefX, hx]

theorem aCoefX_norm_le (hP : Premises T i₀ i₁ ν ρ E₀ κ A K₀ Dom) (hρ : 0 < ρ) (hE0 : 0 ≤ E₀)
    {X : Finset (Site d)} (hX : X ∈ T.polys) (x : Site d) :
    ‖aCoefX T i₀ ν X x‖ ≤ E₀ * Real.exp (-κ * T.dist X) / ρ := by
  by_cases hx : x ∈ X
  · have hok := hP.termOK hρ hX
    have hM : ∀ y ∈ ball (refPt i₀ ν X) ρ, ‖T.term X y‖ ≤ E₀ * Real.exp (-κ * T.dist X) :=
      fun y hy => hP.bdd_tube X hX y (ball_subset_tube i₀ ν ρ X hy)
    simpa [aCoefX, hx] using hok.norm_tensA_le hM ⟨x, hx⟩
  · rw [aCoefX_zero hx]; simp; positivity

theorem aCoefX_summable_prod (hP : Premises T i₀ i₁ ν ρ E₀ κ A K₀ Dom) (hρ : 0 < ρ)
    (hE0 : 0 ≤ E₀) :
    Summable fun p : T.polys × Site d => ‖aCoefX T i₀ ν p.1.1 p.2‖ := by
  rw [summable_prod_of_nonneg (fun p => norm_nonneg _)]
  have hfin : ∀ X : T.polys, ∀ x ∉ X.1, ‖aCoefX T i₀ ν X.1 x‖ = 0 := fun X x hx => by
    rw [aCoefX_zero hx]; simp
  refine ⟨fun X => summable_of_ne_finset_zero (s := X.1) (fun x hx => hfin X x hx), ?_⟩
  refine Summable.of_nonneg_of_le (fun X => tsum_nonneg fun _ => norm_nonneg _) ?_
    (hP.count_summable.mul_left (E₀ / ρ))
  intro X
  rw [tsum_eq_sum (s := X.1) (fun x hx => hfin X x hx)]
  have hd0 := hP.dist_nonneg X.1 X.2
  have hcard : 1 ≤ X.1.card := Finset.card_pos.mpr ⟨0, hP.zero_mem X.1 X.2⟩
  have hw := wt_ge (κ := κ) X.1 hd0 hcard 1 0 (by norm_num) (by norm_num)
  simp only [pow_one, pow_zero, mul_one] at hw
  calc ∑ x ∈ X.1, ‖aCoefX T i₀ ν X.1 x‖ ≤ ∑ _x ∈ X.1, E₀ * Real.exp (-κ * T.dist X.1) / ρ :=
        Finset.sum_le_sum fun x _ => aCoefX_norm_le hP hρ hE0 X.2 x
    _ = (X.1.card : ℝ) * (E₀ * Real.exp (-κ * T.dist X.1)) / ρ := by simp; ring
    _ ≤ (E₀ * wt κ X.1 (T.dist X.1)) / ρ := by
        have : (X.1.card : ℝ) * (E₀ * Real.exp (-κ * T.dist X.1)) ≤
            E₀ * ((X.1.card : ℝ) * Real.exp (-κ * T.dist X.1)) := by
          rw [mul_left_comm]
        refine div_le_div_of_nonneg_right ?_ hρ.le
        exact this.trans (mul_le_mul_of_nonneg_left hw hE0)
    _ = _ := by ring

theorem Aterm_eq_sum (hP : Premises T i₀ i₁ ν ρ E₀ κ A K₀ Dom) (hρ : 0 < ρ) (hE0 : 0 ≤ E₀)
    (ψ : Site d → Spin N) {H : ℝ} (hg : ∀ x, ‖dot (ψ x) (ψ x) - dot (ψ 0) (ψ 0)‖ ≤ H) :
    Aterm T i₀ ν ψ = (1 / 2 : ℂ) * ∑' x : Site d, aCoef T i₀ ν x *
      (dot (ψ x) (ψ x) - dot (ψ 0) (ψ 0)) := by
  classical
  unfold Aterm aCoef
  congr 1
  have e1 : ∀ X : T.polys, ∑ x ∈ X.1, aCoefX T i₀ ν X.1 x *
      (dot (ψ x) (ψ x) - dot (ψ 0) (ψ 0)) =
      ∑' x : Site d, aCoefX T i₀ ν X.1 x * (dot (ψ x) (ψ x) - dot (ψ 0) (ψ 0)) := fun X => by
    rw [tsum_eq_sum (s := X.1)]
    intro x hx
    rw [aCoefX_zero hx, zero_mul]
  simp only [e1]
  have hsum : Summable (Function.uncurry fun (X : T.polys) (x : Site d) =>
      aCoefX T i₀ ν X.1 x * (dot (ψ x) (ψ x) - dot (ψ 0) (ψ 0))) := by
    refine Summable.of_norm_bounded ((aCoefX_summable_prod hP hρ hE0).mul_right H) ?_
    rintro ⟨X, x⟩
    simp only [Function.uncurry_apply_pair, norm_mul]
    exact mul_le_mul_of_nonneg_left (hg x) (norm_nonneg _)
  rw [← Summable.tsum_comm hsum]
  refine tsum_congr fun x => ?_
  rw [tsum_mul_right]

end Balaban.SmallField
