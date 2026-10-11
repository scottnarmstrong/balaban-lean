/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Multiscale.PointwisePotential

/-!
# Lemma P: the setting and the weighted Agmon bounds at points

`PtSetting G Λ` bundles the data and hypotheses of GREEN.md Lemma P / Proposition 4.8:
`f` supported in the `j'`-block of `y' ∈ layer j'`, `u = G_D(α) f = H_D(α)⁻¹ f`,
`ν ℓ_k² ≤ Λ` (unit-scale mass `ν_unit = ν L^{2k} ≤ Λ`), `|α| ≤ c₁ ℓ⁻²/2`, weights `a_j ∈ [1/2, 2]`,
`ϱ ≥ 1`, and the separation `L^d ≤ exp ((ε₀/2)(ϱ - 1))` (the absorption (4.2)).

From the global weighted Agmon estimate (`agmon_wsq_le`, `agmon_cEnergy_le`) with the weight
`exp (ε₀ r)`, `r = truncDist y' t`, we derive pointwise bounds:

* `pt_bound`: `|ũ(p)| ≤ (2/c) ℓ(p) e^{-ε₀ r(p)} A`;
* `grad_bound`: `|ũ(p + e_μ) - ũ(p)| ≤ (2/c) e^{-ε₀ r(p)} A`;
* `sum_bound`: `∑_{p ∈ T} ℓ(p)⁻² e^{2 ε₀ r(p)} |ũ(p)|² ≤ (4/c²) A²`;

with `A = ℓ_{j'} e^{2 ε₀ d} ‖f‖_{ℓ²}` and `c = poincareConst d`.
-/

@[expose] public section

noncomputable section

namespace Balaban.Multiscale

open Finset Matrix Balaban

variable {d L N₀ k : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}

/-- The data and hypotheses of Lemma P and Proposition 4.8. -/
structure PtSetting (G : GeneratingSet d L N₀ k ϱ) (Λ : ℝ) where
  /-- the multiscale weights -/
  a : ℕ → ℝ
  /-- the mass (fine units) -/
  ν : ℝ
  /-- the diagonal perturbation -/
  α : G.Ω 1 → ℂ
  /-- the source -/
  f : G.Ω 1 → ℂ
  /-- the layer of the source block -/
  j' : ℕ
  /-- a point of the source block -/
  y' : Torus d (N₀ * L ^ k)
  hd : 3 ≤ d
  hL : 3 ≤ L
  hν0 : 0 ≤ ν
  hν1 : ν * ((L : ℝ) ^ k) ^ 2 ≤ Λ
  ha : IsAdmissibleWeights k a
  hα : ∀ x, ‖α x‖ ≤ coerciveConst d / (2 * (G.spacing x) ^ 2)
  hϱ : 1 ≤ ϱ
  hsep : (L : ℝ) ^ d ≤ Real.exp (agmonRate d / 2 * (ϱ - 1))
  hj'1 : 1 ≤ j'
  hj'k : j' ≤ k
  hy' : y' ∈ G.layer j'
  hsupp : ∀ x : G.Ω 1, f x ≠ 0 → jBlock d L N₀ k j' x = jBlock d L N₀ k j' y'

namespace PtSetting

variable {G : GeneratingSet d L N₀ k ϱ} {Λ : ℝ} (S : PtSetting G Λ)

include S in
theorem hd0 : 0 < d := by have := S.hd; omega

/-- The solution `u = G_D(α) f`. -/
def u : G.Ω 1 → ℂ := (dirichletOperator G S.a S.ν S.α)⁻¹ *ᵥ S.f

/-- The zero extension of `u` to the whole torus. -/
def ut : Torus d (N₀ * L ^ k) → ℂ := zeroExt (G.Ω 1) S.u

theorem hu : dirichletOperator G S.a S.ν S.α *ᵥ S.u = S.f :=
  dirichletOperator_mulVec_inv G S.hd0 S.hν0 S.ha S.α S.hα S.f

/-- The amplitude `A = ℓ_{j'} e^{2 ε₀ d} ‖f‖`. -/
def amp : ℝ := (L : ℝ) ^ S.j' * Real.exp (2 * agmonRate d * d) * Real.sqrt (Green.sqNorm S.f)

theorem amp_nonneg : 0 ≤ S.amp := by
  unfold amp
  positivity

theorem agmonSource_le_amp (t : ℝ) :
    agmonSource G (agmonRate d) (G.truncDist S.y' t) S.f ≤ S.amp ^ 2 := by
  have h := agmonSource_le G (G.isAgmonWeight_truncDist S.y' t) (agmonRate_pos S.hd0).le
    S.hj'1 S.hj'k S.hy' (G.truncDist_self (G.layer_subset S.hj'1 S.hj'k S.hy') t) S.hsupp
  refine h.trans (le_of_eq ?_)
  unfold amp
  have h1 : Real.exp (4 * agmonRate d * d) = Real.exp (2 * agmonRate d * d) ^ 2 := by
    rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  rw [h1, mul_pow, mul_pow, Real.sq_sqrt (Green.sqNorm_nonneg _)]

theorem weighted_cwsq (t : ℝ) :
    cwsq G (agmonField G (agmonRate d) (G.truncDist S.y' t) S.u) ≤
      4 / poincareConst d ^ 2 * S.amp ^ 2 :=
  (agmon_wsq_le G S.hd0 S.hν0 S.ha S.α S.hα (G.isAgmonWeight_truncDist S.y' t)
    (agmonRate_pos S.hd0).le le_rfl S.hu).trans
    (mul_le_mul_of_nonneg_left (S.agmonSource_le_amp t) (by
      have := poincareConst_pos S.hd0; positivity))

theorem weighted_cEnergy (t : ℝ) :
    cEnergy (agmonField G (agmonRate d) (G.truncDist S.y' t) S.u) ≤
      2 / poincareConst d * S.amp ^ 2 :=
  (agmon_cEnergy_le G S.hd0 S.hν0 S.ha S.α S.hα (G.isAgmonWeight_truncDist S.y' t)
    (agmonRate_pos S.hd0).le le_rfl S.hu).trans
    (mul_le_mul_of_nonneg_left (S.agmonSource_le_amp t) (by
      have := poincareConst_pos S.hd0; positivity))

/-- Sub-sums of the weighted `ℓ²` norm. -/
theorem sum_bound (t : ℝ) (T : Finset (Torus d (N₀ * L ^ k))) (hT : ∀ p ∈ T, p ∈ G.Ω 1) :
    ∑ p ∈ T, ((G.spacing p) ^ 2)⁻¹ * (Real.exp (agmonRate d * G.truncDist S.y' t p) ^ 2 *
        ‖S.ut p‖ ^ 2) ≤ 4 / poincareConst d ^ 2 * S.amp ^ 2 := by
  refine le_trans ?_ (S.weighted_cwsq t)
  unfold cwsq
  calc _ = ∑ p ∈ T, invSqSpacing G p * ‖agmonField G (agmonRate d) (G.truncDist S.y' t) S.u p‖ ^ 2 :=
        Finset.sum_congr rfl fun p hp => by
          rw [invSqSpacing_eq G (hT p hp), norm_agmonField, mul_pow]
          rfl
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun x _ _ =>
          mul_nonneg (invSqSpacing_nonneg G x) (sq_nonneg _)

/-- **Pointwise weighted bound.** -/
theorem pt_bound (t : ℝ) {p : Torus d (N₀ * L ^ k)} (hp : p ∈ G.Ω 1) :
    ‖S.ut p‖ ≤ 2 / poincareConst d * G.spacing p *
      Real.exp (-(agmonRate d * G.truncDist S.y' t p)) * S.amp := by
  have hc := poincareConst_pos S.hd0
  have h1 := S.sum_bound t {p} (by simpa using hp)
  rw [Finset.sum_singleton] at h1
  have hs0 : 0 < G.spacing p := spacing_pos G
  set E := Real.exp (agmonRate d * G.truncDist S.y' t p) with hE
  have hE0 : 0 < E := Real.exp_pos _
  have h2 : (E * ‖S.ut p‖) ^ 2 ≤ (2 / poincareConst d * G.spacing p * S.amp) ^ 2 := by
    have : (E * ‖S.ut p‖) ^ 2 = (G.spacing p) ^ 2 * (((G.spacing p) ^ 2)⁻¹ * (E ^ 2 * ‖S.ut p‖ ^ 2)) := by
      field_simp
    rw [this]
    calc _ ≤ (G.spacing p) ^ 2 * (4 / poincareConst d ^ 2 * S.amp ^ 2) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = _ := by field_simp; ring
  have h3 : E * ‖S.ut p‖ ≤ 2 / poincareConst d * G.spacing p * S.amp :=
    (sq_le_sq₀ (by positivity) (by have := S.amp_nonneg; positivity)).1 h2
  have h4 : Real.exp (-(agmonRate d * G.truncDist S.y' t p)) = E⁻¹ := by
    rw [hE, Real.exp_neg]
  rw [h4]
  have h5 : ‖S.ut p‖ ≤ (2 / poincareConst d * G.spacing p * S.amp) * E⁻¹ := by
    rw [← div_eq_mul_inv, le_div_iff₀ hE0]
    linarith [h3]
  calc _ ≤ _ := h5
    _ = _ := by ring

/-- **Weighted gradient bound** for the forward bond at `p`. -/
theorem grad_bound (t : ℝ) {p : Torus d (N₀ * L ^ k)} (hp : p ∈ G.Ω 1) (μ : Fin d) :
    ‖S.ut (p + Pi.single μ 1) - S.ut p‖ ≤ 2 / poincareConst d *
      Real.exp (-(agmonRate d * G.truncDist S.y' t p)) * S.amp := by
  have hc := poincareConst_pos S.hd0
  have hch := poincareConst_le_half d
  have hε0 := agmonRate_pos S.hd0
  have hε1 := agmonRate_le S.hd0
  have hpt := agmon_grad_pointwise G (G.isAgmonWeight_truncDist S.y' t) hε0.le
    (by linarith) S.u hp μ
  have hW := S.weighted_cwsq t
  have hE := S.weighted_cEnergy t
  set v := agmonField G (agmonRate d) (G.truncDist S.y' t) S.u with hv
  have t1 : ‖v (p + Pi.single μ 1) - v p‖ ^ 2 ≤ cEnergy v := by
    unfold cEnergy
    calc _ ≤ ∑ μ' : Fin d, ‖v (p + Pi.single μ' 1) - v p‖ ^ 2 :=
          Finset.single_le_sum (f := fun μ' : Fin d => ‖v (p + Pi.single μ' 1) - v p‖ ^ 2)
            (fun _ _ => sq_nonneg _) (Finset.mem_univ μ)
      _ ≤ _ := Finset.single_le_sum (f := fun x : Torus d (N₀ * L ^ k) =>
            ∑ μ' : Fin d, ‖v (x + Pi.single μ' 1) - v x‖ ^ 2)
            (fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _) (Finset.mem_univ p)
  have t2 : invSqSpacing G (p + Pi.single μ 1) * ‖v (p + Pi.single μ 1)‖ ^ 2 ≤ cwsq G v := by
    unfold cwsq
    exact Finset.single_le_sum (f := fun x : Torus d (N₀ * L ^ k) =>
      invSqSpacing G x * ‖v x‖ ^ 2) (fun x _ => mul_nonneg (invSqSpacing_nonneg G x)
      (sq_nonneg _)) (Finset.mem_univ _)
  set E := Real.exp (agmonRate d * G.truncDist S.y' t p) with hE'
  have hE0 : 0 < E := Real.exp_pos _
  have hA := S.amp_nonneg
  have h2 : (E * ‖S.ut (p + Pi.single μ 1) - S.ut p‖) ^ 2 ≤ (2 / poincareConst d * S.amp) ^ 2 := by
    have e : (E * ‖S.ut (p + Pi.single μ 1) - S.ut p‖) ^ 2 =
        E ^ 2 * ‖zeroExt (G.Ω 1) S.u (p + Pi.single μ 1) - zeroExt (G.Ω 1) S.u p‖ ^ 2 := by
      rw [mul_pow]; rfl
    rw [e]
    refine hpt.trans ?_
    have hε2 : 8 * agmonRate d ^ 2 ≤ 1 / 128 := by nlinarith
    have hc2 : 1 / poincareConst d ≤ 1 / poincareConst d ^ 2 * (1 / 2) := by
      rw [div_mul_eq_mul_div, one_mul, div_le_div_iff₀ hc (by positivity)]
      nlinarith
    have hb := add_le_add
      (mul_le_mul_of_nonneg_left (t1.trans hE) (by norm_num : (0 : ℝ) ≤ 2))
      (mul_le_mul_of_nonneg_left (t2.trans hW) (by positivity : (0 : ℝ) ≤ 8 * agmonRate d ^ 2))
    refine hb.trans ?_
    set X := 1 / poincareConst d ^ 2 * S.amp ^ 2 with hX
    have hX0 : 0 ≤ X := by positivity
    have e1 : 2 / poincareConst d * S.amp ^ 2 ≤ X := by
      have : 2 / poincareConst d ≤ 1 / poincareConst d ^ 2 := by
        rw [div_le_div_iff₀ hc (by positivity)]
        nlinarith
      calc 2 / poincareConst d * S.amp ^ 2 ≤ 1 / poincareConst d ^ 2 * S.amp ^ 2 :=
            mul_le_mul_of_nonneg_right this (by positivity)
        _ = X := rfl
    have e2 : 4 / poincareConst d ^ 2 * S.amp ^ 2 = 4 * X := by rw [hX]; ring
    have e3 : (2 / poincareConst d * S.amp) ^ 2 = 4 * X := by
      rw [hX]; field_simp; ring
    rw [e3]
    rw [e2] at *
    nlinarith [mul_le_mul_of_nonneg_right hε2 (by positivity : (0 : ℝ) ≤ 4 * X)]
  have h3 : E * ‖S.ut (p + Pi.single μ 1) - S.ut p‖ ≤ 2 / poincareConst d * S.amp :=
    (sq_le_sq₀ (by positivity) (by positivity)).1 h2
  have h4 : Real.exp (-(agmonRate d * G.truncDist S.y' t p)) = E⁻¹ := by
    rw [hE', Real.exp_neg]
  rw [h4]
  have h5 : ‖S.ut (p + Pi.single μ 1) - S.ut p‖ ≤ (2 / poincareConst d * S.amp) * E⁻¹ := by
    rw [← div_eq_mul_inv, le_div_iff₀ hE0]
    linarith [h3]
  calc _ ≤ _ := h5
    _ = _ := by ring

end PtSetting

end Balaban.Multiscale
