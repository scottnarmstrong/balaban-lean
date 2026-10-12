/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.SmallField.RenormShape
public import Balaban.SmallField.RenormLattice

/-!
# Expansion of one term around the reference point

For `f = 𝓔(0, X; ·)` with `TermOK`, bounded by `M` on the polydisc of radius `ρ`:

* `TermOK.taylor_diff`: the second-order expansion of `f(P₀ + z) - f(P₀ + z_c)`;
* `lin_pack`, `quad_pack`: the first and second derivatives in a direction `pack X φ 0`
  expressed through the tensors `a_X`, `A_X`, `B_X` (the shape lemma).
-/

@[expose] public section

open Metric Set

namespace Balaban.SmallField

variable {d N : ℕ}

section Taylor

variable {i₀ : Fin N} {ν ρ : ℝ} {X : Finset (Site d)} {f : Cfg d N X → ℂ}

theorem TermOK.taylor_diff (hf : TermOK i₀ ν ρ X f) {M : ℝ}
    (hM : ∀ x ∈ ball (refPt i₀ ν X) ρ, ‖f x‖ ≤ M) {z zc : Cfg d N X}
    (hz : ‖z‖ ≤ ρ / 2) (hzc : ‖zc‖ ≤ ρ / 2) :
    ‖f (refPt i₀ ν X + z) - f (refPt i₀ ν X + zc)
        - fderiv ℂ f (refPt i₀ ν X) (z - zc)
        - D2 f (refPt i₀ ν X) zc (z - zc)
        - (1 / 2 : ℂ) * D2 f (refPt i₀ ν X) (z - zc) (z - zc)‖ ≤
      2 * M * (‖z‖ / ρ) ^ 3 + 2 * M * (‖zc‖ / ρ) ^ 3 := by
  have hρ := hf.rho_pos
  have h1 := taylor_second hρ hf.analytic_ball hM hz
  have h2 := taylor_second hρ hf.analytic_ball hM hzc
  have hs := D2_symm (hf.analytic_ball (refPt i₀ ν X) (mem_ball_self hρ)) zc (z - zc)
  have hD : D2 f (refPt i₀ ν X) z z = D2 f (refPt i₀ ν X) zc zc +
      2 * D2 f (refPt i₀ ν X) zc (z - zc) + D2 f (refPt i₀ ν X) (z - zc) (z - zc) := by
    have : z = zc + (z - zc) := by abel
    conv_lhs => rw [this]
    simp only [D2_add_left, D2_add_right]
    rw [← hs]; ring
  have e : f (refPt i₀ ν X + z) - f (refPt i₀ ν X + zc)
        - fderiv ℂ f (refPt i₀ ν X) (z - zc)
        - D2 f (refPt i₀ ν X) zc (z - zc)
        - (1 / 2 : ℂ) * D2 f (refPt i₀ ν X) (z - zc) (z - zc) =
      (f (refPt i₀ ν X + z) - f (refPt i₀ ν X) - fderiv ℂ f (refPt i₀ ν X) z
          - (1 / 2 : ℂ) * D2 f (refPt i₀ ν X) z z) -
      (f (refPt i₀ ν X + zc) - f (refPt i₀ ν X) - fderiv ℂ f (refPt i₀ ν X) zc
          - (1 / 2 : ℂ) * D2 f (refPt i₀ ν X) zc zc) := by
    rw [map_sub, hD]; ring
  rw [e]
  exact (norm_sub_le _ _).trans (add_le_add h1 h2)

end Taylor

section Pack

/-- The longitudinal-longitudinal second derivative at the reference point. -/
noncomputable def tensAA (i₀ : Fin N) (ν : ℝ) (X : Finset (Site d)) (f : Cfg d N X → ℂ)
    (x x' : ↥X) : ℂ :=
  D2 f (refPt i₀ ν X) (Pi.single (Sum.inl (x, i₀)) 1) (Pi.single (Sum.inl (x', i₀)) 1)

theorem pack_zero_eq_sum (X : Finset (Site d)) (φ : Site d → Spin N) :
    pack X φ 0 = ∑ x : ↥X, ∑ j, φ x.1 j • (Pi.single (Sum.inl (x, j)) (1 : ℂ) : Cfg d N X) := by
  ext (⟨x, i⟩ | i)
  · simp only [pack, Sum.elim_inl, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    simp [Pi.single_apply, ite_and]
  · simp [pack, Finset.sum_apply]

variable {i₀ i₁ : Fin N} {ν ρ : ℝ} {X : Finset (Site d)} {f : Cfg d N X → ℂ}

theorem TermOK.lin_pack (hf : TermOK i₀ ν ρ X f) (φ : Site d → Spin N) :
    fderiv ℂ f (refPt i₀ ν X) (pack X φ 0) = ∑ x : ↥X, tensA i₀ ν X f x * φ x.1 i₀ := by
  rw [pack_zero_eq_sum]
  simp only [map_sum, map_smul, smul_eq_mul]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.sum_eq_single i₀]
  · simp [tensA, mul_comm]
  · intro j _ hj
    rw [hf.fderiv_inl_transverse hj]; simp
  · simp

theorem TermOK.D2_basis (hf : TermOK i₀ ν ρ X f) (hi : i₁ ≠ i₀) (x x' : ↥X) (j k : Fin N) :
    D2 f (refPt i₀ ν X) (Pi.single (Sum.inl (x, j)) 1) (Pi.single (Sum.inl (x', k)) 1) =
      if j = k then (if j = i₀ then tensAA i₀ ν X f x x' else tensB i₀ i₁ ν X f x x') else 0 := by
  have hsym := D2_symm (hf.analytic_ball (refPt i₀ ν X) (mem_ball_self hf.rho_pos))
  by_cases hjk : j = k
  · subst hjk
    by_cases hj : j = i₀
    · subst hj; simp [tensAA]
    · simp only [hj, ite_false, ite_true]
      rw [hf.D2_swap hi hj x x']; rfl
  · simp only [hjk, ite_false]
    by_cases hj : j = i₀
    · subst hj
      rw [hsym]
      exact hf.D2_inl_inl_ne (Ne.symm hjk) (Ne.symm hjk) x' x
    · exact hf.D2_inl_inl_ne hj hjk x x'

theorem D2_sum_left {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {ι : Type*}
    (s : Finset ι) (f : E → ℂ) (c : E) (v : ι → E) (w : E) :
    D2 f c (∑ i ∈ s, v i) w = ∑ i ∈ s, D2 f c (v i) w := by
  simp [D2, map_sum]

theorem D2_sum_right {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {ι : Type*}
    (s : Finset ι) (f : E → ℂ) (c : E) (v : E) (w : ι → E) :
    D2 f c v (∑ i ∈ s, w i) = ∑ i ∈ s, D2 f c v (w i) := by
  simp [D2, map_sum]

theorem D2_left_expand {ι : Type*} [Fintype ι] [DecidableEq ι] (f : (ι → ℂ) → ℂ)
    (c v w : ι → ℂ) :
    D2 f c v w = ∑ p, v p * D2 f c (Pi.single p 1) w := by
  have hv : v = ∑ p, v p • (Pi.single p (1 : ℂ) : ι → ℂ) := by
    ext r; simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hv]
  simp only [D2_sum_left, D2_smul_left]

theorem D2_right_expand {ι : Type*} [Fintype ι] [DecidableEq ι] (f : (ι → ℂ) → ℂ)
    (c v w : ι → ℂ) :
    D2 f c v w = ∑ q, w q * D2 f c v (Pi.single q 1) := by
  have hw : w = ∑ q, w q • (Pi.single q (1 : ℂ) : ι → ℂ) := by
    ext r; simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hw]
  simp only [D2_sum_right, D2_smul_right]

theorem TermOK.quad_pack (hf : TermOK i₀ ν ρ X f) (hi : i₁ ≠ i₀) (φ φ' : Site d → Spin N) :
    D2 f (refPt i₀ ν X) (pack X φ 0) (pack X φ' 0) =
      ∑ x : ↥X, ∑ x' : ↥X, (tensAA i₀ ν X f x x' * (φ x.1 i₀ * φ' x'.1 i₀) +
        tensB i₀ i₁ ν X f x x' * dotT i₀ (φ x.1) (φ' x'.1)) := by
  set c : Fin N → ↥X → ↥X → ℂ := fun j x x' =>
    if j = i₀ then tensAA i₀ ν X f x x' else tensB i₀ i₁ ν X f x x' with hc
  have step : ∀ (x : ↥X) (j : Fin N),
      D2 f (refPt i₀ ν X) (Pi.single (Sum.inl (x, j)) 1) (pack X φ' 0) =
        ∑ x' : ↥X, φ' x'.1 j * c j x x' := by
    intro x j
    rw [D2_right_expand]
    simp only [Fintype.sum_sum_type, Fintype.sum_prod_type]
    simp only [pack, Sum.elim_inl, Sum.elim_inr, Pi.zero_apply, zero_mul, Finset.sum_const_zero,
      add_zero, hf.D2_basis hi]
    refine Finset.sum_congr rfl fun x' _ => ?_
    rw [Finset.sum_eq_single j]
    · simp [hc]
    · intro k _ hk; simp [Ne.symm hk]
    · simp
  have hinl : ∀ (x : ↥X) (j : Fin N), pack X φ 0 (Sum.inl (x, j)) = φ x.1 j := fun _ _ => rfl
  have hinr : ∀ i : Fin N, pack X φ 0 (Sum.inr i) = 0 := fun _ => rfl
  rw [D2_left_expand]
  simp only [Fintype.sum_sum_type, Fintype.sum_prod_type, hinl, hinr, zero_mul,
    Finset.sum_const_zero, add_zero]
  simp only [step]
  refine Finset.sum_congr rfl fun x _ => ?_
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x' _ => ?_
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i₀)]
  simp only [hc, ite_true, dotT, Finset.mul_sum]
  have h2 : ∀ j ∈ Finset.univ.erase i₀, φ x.1 j * (φ' x'.1 j * (if j = i₀ then tensAA i₀ ν X f x x'
      else tensB i₀ i₁ ν X f x x')) = tensB i₀ i₁ ν X f x x' * (φ x.1 j * φ' x'.1 j) := by
    intro j hj
    have : j ≠ i₀ := Finset.ne_of_mem_erase hj
    simp [this]; ring
  rw [Finset.sum_congr rfl h2]
  ring

theorem norm_pack_le (X : Finset (Site d)) (φ : Site d → Spin N) {D : ℝ} (hD0 : 0 ≤ D)
    (hD : ∀ x ∈ X, ‖φ x‖ ≤ D) : ‖pack X φ 0‖ ≤ D := by
  rw [pi_norm_le_iff_of_nonneg hD0]
  rintro (⟨x, j⟩ | i)
  · exact (norm_le_pi_norm (φ x.1) j).trans (hD x.1 x.2)
  · simpa [pack] using hD0

theorem norm_single_one_le {ι : Type*} [Fintype ι] [DecidableEq ι] (p : ι) :
    ‖(Pi.single p (1 : ℂ) : ι → ℂ)‖ ≤ 1 := by
  rw [pi_norm_le_iff_of_nonneg zero_le_one]
  intro q
  by_cases h : q = p <;> simp [Pi.single_apply, h]

theorem TermOK.norm_tensA_le (hf : TermOK i₀ ν ρ X f) {M : ℝ}
    (hM : ∀ c ∈ ball (refPt i₀ ν X) ρ, ‖f c‖ ≤ M) (x : ↥X) :
    ‖tensA i₀ ν X f x‖ ≤ M / ρ := by
  have := norm_fderiv_apply_le hf.rho_pos hf.analytic_ball hM
    (Pi.single (Sum.inl (x, i₀)) (1 : ℂ) : Cfg d N X)
  have h1 := norm_single_one_le (Sum.inl (x, i₀) : Idx d N X)
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (hM _ (mem_ball_self hf.rho_pos))
  unfold tensA
  refine this.trans ?_
  rw [div_le_div_iff_of_pos_right hf.rho_pos]
  nlinarith

theorem TermOK.norm_D2_basis_le (hf : TermOK i₀ ν ρ X f) {M : ℝ}
    (hM : ∀ c ∈ ball (refPt i₀ ν X) ρ, ‖f c‖ ≤ M) (p q : Idx d N X) :
    ‖D2 f (refPt i₀ ν X) (Pi.single p 1) (Pi.single q 1)‖ ≤ 4 * M / ρ ^ 2 := by
  have := norm_D2_le hf.rho_pos hf.analytic_ball hM (Pi.single p (1 : ℂ) : Cfg d N X)
    (Pi.single q (1 : ℂ) : Cfg d N X)
  have h1 := norm_single_one_le p
  have h2 := norm_single_one_le q
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (hM _ (mem_ball_self hf.rho_pos))
  refine this.trans ?_
  rw [div_le_div_iff_of_pos_right (by have := hf.rho_pos; positivity)]
  nlinarith [mul_nonneg hM0 (norm_nonneg (Pi.single p (1 : ℂ) : Cfg d N X)),
    mul_le_mul h1 h2 (norm_nonneg _) zero_le_one]

theorem TermOK.tensB_symm (hf : TermOK i₀ ν ρ X f) (x x' : ↥X) :
    tensB i₀ i₁ ν X f x x' = tensB i₀ i₁ ν X f x' x :=
  D2_symm (hf.analytic_ball (refPt i₀ ν X) (mem_ball_self hf.rho_pos)) _ _

end Pack

section Algebra

theorem dotT_comm (i₀ : Fin N) (u v : Spin N) : dotT i₀ u v = dotT i₀ v u := by
  simp [dotT, mul_comm]

theorem dotT_sub_self (i₀ : Fin N) (u v : Spin N) :
    dotT i₀ (u - v) (u - v) = dotT i₀ u u - 2 * dotT i₀ u v + dotT i₀ v v := by
  simp only [dotT, Pi.sub_apply, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

/-- The algebraic consequence of the Ward identity: `Q_X` in terms of the differences. -/
theorem ward_algebra {ι : Type*} [Fintype ι] (i₀ : Fin N) (ν : ℂ) (a m : ι → ℂ)
    (B : ι → ι → ℂ) (hB : ∀ x x', B x x' = B x' x)
    (hW : ∀ x', ∑ x, B x x' + ν * m x' - a x' = 0) (Θ : ι → Spin N) :
    (1 / 2 : ℂ) * ∑ x, ∑ x', B x x' * dotT i₀ (Θ x) (Θ x') -
        (1 / 2 : ℂ) * ∑ x, a x * dotT i₀ (Θ x) (Θ x) =
      -(ν / 2) * ∑ x, m x * dotT i₀ (Θ x) (Θ x) -
        (1 / 4 : ℂ) * ∑ x, ∑ x', B x x' * dotT i₀ (Θ x - Θ x') (Θ x - Θ x') := by
  have hcol : ∀ x', ∑ x, B x x' = a x' - ν * m x' := fun x' => by linear_combination hW x'
  have hrow : ∀ x, ∑ x', B x x' = a x - ν * m x := fun x => by
    rw [← hcol x]; exact Finset.sum_congr rfl fun x' _ => hB x x'
  simp only [dotT_sub_self, mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  have hsplit : ∑ x, (a x - ν * m x) * dotT i₀ (Θ x) (Θ x) =
      ∑ x, a x * dotT i₀ (Θ x) (Θ x) - ν * ∑ x, m x * dotT i₀ (Θ x) (Θ x) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun x _ => by ring
  have e1 : ∑ x, ∑ x', B x x' * dotT i₀ (Θ x) (Θ x) =
      ∑ x, a x * dotT i₀ (Θ x) (Θ x) - ν * ∑ x, m x * dotT i₀ (Θ x) (Θ x) := by
    rw [← hsplit]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← Finset.sum_mul, hrow]
  have e2 : ∑ x, ∑ x', B x x' * dotT i₀ (Θ x') (Θ x') =
      ∑ x, a x * dotT i₀ (Θ x) (Θ x) - ν * ∑ x, m x * dotT i₀ (Θ x) (Θ x) := by
    rw [← hsplit, Finset.sum_comm]
    refine Finset.sum_congr rfl fun x' _ => ?_
    rw [← Finset.sum_mul, hcol]
  have e3 : ∑ x, ∑ x', B x x' * (2 * dotT i₀ (Θ x) (Θ x')) =
      2 * ∑ x, ∑ x', B x x' * dotT i₀ (Θ x) (Θ x') := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun x' _ => by ring
  have e4 : ∑ x, m x * dotT i₀ (Θ x) (Θ x) = ∑ x, m x * dotT i₀ (Θ x) (Θ x) := rfl
  rw [e1, e2, e3]
  ring

end Algebra

end Balaban.SmallField
