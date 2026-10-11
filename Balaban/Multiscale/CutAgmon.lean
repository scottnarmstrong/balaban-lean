/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Multiscale.CutCoercivity
public import Balaban.Multiscale.ScaleMismatch
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

/-!
# The Agmon estimate for the cut operator: block decay (statement NC2 of LOCALIZATION.md §3.1)

`Balaban/Multiscale/AgmonCore.lean` and `Agmon.lean` for the cut operator
`Balaban.Multiscale.cutOperator` (a set `cut` of removed bonds with `CutAligned`).  The weights
are those of the landed development (`IsAgmonWeight`, the path metric `d` of `Ω₁`).  What changes:

* the Laplacian conjugation error is summed over the retained bonds, each bond error being bounded
  by the (non-negative) bound of the landed `bond_term_le`, so the sum over the retained bonds is at
  most the sum over all bonds (`lap_error_le_cut`);
* the block error `avg_diff_ge` has no Laplacian and is used unchanged;
* the coercive core is `core_real_cut` (the layer blocks are untouched by the cut);
* the energy of the conjugated field is the retained energy `cutEnergy`.

The gradient of a block is measured over the retained bonds only (`cutBlockGrad`); the removed
bonds are not controlled by the form.  The block decay is stated with the path metric `d` of `Ω₁`.

Main results: `weighted_core_cut`, `agmon_energy_cut`, `agmon_wsq_le_cut`, `agmon_cEnergy_le_cut`,
`agmon_block_cut` (the Agmon block decay), `green_G2i_cut` and `green_G2i_cut_green` (**NC2**,
the analogues of `green_G2i`, `green_G2i_green`).
-/

@[expose] public section

namespace Balaban.Multiscale

open Finset Matrix Balaban

variable {d L N₀ k : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}

variable (G : GeneratingSet d L N₀ k ϱ) {cut : Finset (Torus d (N₀ * L ^ k) × Fin d)}

/-- **Laplacian error over the retained bonds.** -/
theorem lap_error_le_cut {r : Torus d (N₀ * L ^ k) → ℝ} (hr : IsAgmonWeight G r) {ε : ℝ}
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1 / 2) {φ : Torus d (N₀ * L ^ k) → ℝ}
    (hφ : ∀ x, x ∉ G.Ω 1 → φ x = 0) :
    ∑ x, ∑ μ : Fin d, (if (x, μ) ∈ cut then 0 else
        (Real.exp (ε * r (x + Pi.single μ 1)) - Real.exp (ε * r x)) ^ 2 *
          (φ x * φ (x + Pi.single μ 1))) ≤
      4 * d * ε ^ 2 * wsq G (fun x => Real.exp (ε * r x) * φ x) := by
  set F : Torus d (N₀ * L ^ k) → ℝ := fun x => invSqSpacing G x * (Real.exp (ε * r x) * φ x) ^ 2
    with hF
  have hshift : ∀ μ : Fin d, ∑ x, F (x + Pi.single μ 1) = ∑ x, F x := fun μ =>
    sum_shift (Pi.single μ 1) F
  have hF0 : ∀ x, 0 ≤ F x := fun x => mul_nonneg (invSqSpacing_nonneg G x) (sq_nonneg _)
  calc _ ≤ ∑ x, ∑ μ : Fin d, 2 * ε ^ 2 * (F x + F (x + Pi.single μ 1)) := by
        refine Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun μ _ => ?_
        split_ifs
        · have := hF0 x
          have := hF0 (x + Pi.single μ 1)
          positivity
        · exact bond_term_le G hr hε0 hε1 hφ x μ
    _ = ∑ μ : Fin d, 2 * ε ^ 2 * (∑ x, F x + ∑ x, F (x + Pi.single μ 1)) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun μ _ => ?_
        rw [← Finset.mul_sum, Finset.sum_add_distrib]
        rfl
    _ = 4 * d * ε ^ 2 * wsq G (fun x => Real.exp (ε * r x) * φ x) := by
        simp only [hshift]
        have hw : wsq G (fun x => Real.exp (ε * r x) * φ x) = ∑ x, F x := rfl
        rw [hw, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

theorem lap_diff_cut (r : Torus d (N₀ * L ^ k) → ℝ) (ε ν : ℝ)
    (cut : Finset (Torus d (N₀ * L ^ k) × Fin d)) (φ : Torus d (N₀ * L ^ k) → ℝ) :
    (fun x => Real.exp (ε * r x) ^ 2 * φ x) ⬝ᵥ cutLaplacian ν cut *ᵥ φ =
      (fun x => Real.exp (ε * r x) * φ x) ⬝ᵥ cutLaplacian ν cut *ᵥ
          (fun x => Real.exp (ε * r x) * φ x) -
        ∑ x, ∑ μ : Fin d, (if (x, μ) ∈ cut then 0 else
          (Real.exp (ε * r (x + Pi.single μ 1)) - Real.exp (ε * r x)) ^ 2 *
            (φ x * φ (x + Pi.single μ 1))) := by
  rw [cutLaplacian_bilinear, cutLaplacian_bilinear]
  have h1 : ∑ x, Real.exp (ε * r x) ^ 2 * φ x * φ x =
      ∑ x, Real.exp (ε * r x) * φ x * (Real.exp (ε * r x) * φ x) :=
    Finset.sum_congr rfl fun x _ => by ring
  have h2 : ∀ (x : Torus d (N₀ * L ^ k)) (μ : Fin d),
      (if (x, μ) ∈ cut then (0 : ℝ) else
        (Real.exp (ε * r (x + Pi.single μ 1)) ^ 2 * φ (x + Pi.single μ 1) -
          Real.exp (ε * r x) ^ 2 * φ x) * (φ (x + Pi.single μ 1) - φ x)) =
      (if (x, μ) ∈ cut then 0 else
        (Real.exp (ε * r (x + Pi.single μ 1)) * φ (x + Pi.single μ 1) -
          Real.exp (ε * r x) * φ x) * (Real.exp (ε * r (x + Pi.single μ 1)) *
            φ (x + Pi.single μ 1) - Real.exp (ε * r x) * φ x)) -
      (if (x, μ) ∈ cut then 0 else
        (Real.exp (ε * r (x + Pi.single μ 1)) - Real.exp (ε * r x)) ^ 2 *
          (φ x * φ (x + Pi.single μ 1))) := by
    intro x μ
    split_ifs
    · simp
    · ring
  simp only [h2, Finset.sum_sub_distrib]
  rw [h1]
  ring

/-- **The conjugated real form for the cut operator.** For `w = exp (ε r)` and a real field `φ`
supported in `Ω₁`, with `v = w φ`: `½ E_cut(v) + (c - κ) ‖ℓ⁻¹ v‖² ≤ ∑ w² φ (A_cut φ)`. -/
theorem weighted_core_cut (hcut : CutAligned G cut) (hd : 0 < d) {a : ℕ → ℝ} {ν : ℝ}
    (hν : 0 ≤ ν) (ha : IsAdmissibleWeights k a)
    {r : Torus d (N₀ * L ^ k) → ℝ} (hr : IsAgmonWeight G r) {ε : ℝ} (hε0 : 0 ≤ ε)
    (hε1 : ε ≤ 1 / 2) {φ : Torus d (N₀ * L ^ k) → ℝ} (hφ : ∀ x, x ∉ G.Ω 1 → φ x = 0) :
    (1 / 2) * cutLatticeEnergy cut (fun x => Real.exp (ε * r x) * φ x) +
        (poincareConst d - (4 * d * ε ^ 2 + (Real.exp (ε * (2 * d)) - 1) ^ 2)) *
          wsq G (fun x => Real.exp (ε * r x) * φ x) ≤
      (fun x => Real.exp (ε * r x) ^ 2 * φ x) ⬝ᵥ cutFullMatrix G a ν cut *ᵥ φ := by
  set v : Torus d (N₀ * L ^ k) → ℝ := fun x => Real.exp (ε * r x) * φ x with hv
  have hcore := core_real_cut G hcut hd hν ha v
  have hlap := lap_diff_cut r ε ν cut φ
  have hlapE := lap_error_le_cut G (cut := cut) hr hε0 hε1 hφ
  have havg := avg_diff_ge G ha hr hε0 φ
  have hwsq : ∑ x, invSqSpacing G x * v x ^ 2 = wsq G v := rfl
  rw [hwsq] at hcore
  have hsplit : ∀ ψ : Torus d (N₀ * L ^ k) → ℝ, ∀ g : Torus d (N₀ * L ^ k) → ℝ,
      g ⬝ᵥ cutFullMatrix G a ν cut *ᵥ ψ =
        g ⬝ᵥ cutLaplacian ν cut *ᵥ ψ + g ⬝ᵥ avgMatrix G a *ᵥ ψ := by
    intro ψ g
    unfold cutFullMatrix
    rw [Matrix.add_mulVec, dotProduct_add]
  rw [hsplit] at hcore ⊢
  rw [hlap]
  nlinarith [hcore, hlapE, havg]

/-- **The Agmon energy inequality** (GREEN.md Prop. 4.5): with `v = w ũ`,
`½ ‖∂v‖² + (c/4) ‖ℓ⁻¹ v‖² ≤ c⁻¹ ‖ℓ w f‖²`, `c = poincareConst d`. -/
theorem agmon_energy_cut (G : GeneratingSet d L N₀ k ϱ) (hcut : CutAligned G cut) (hd : 0 < d)
    {a : ℕ → ℝ} {ν : ℝ} (hν : 0 ≤ ν)
    (ha : IsAdmissibleWeights k a) (α : G.Ω 1 → ℂ)
    (hα : ∀ x, ‖α x‖ ≤ coerciveConst d / (2 * (G.spacing x) ^ 2))
    {r : Torus d (N₀ * L ^ k) → ℝ} (hr : IsAgmonWeight G r) {ε : ℝ} (hε0 : 0 ≤ ε)
    (hε1 : ε ≤ agmonRate d) {u f : G.Ω 1 → ℂ} (hu : cutOperator G a ν cut α *ᵥ u = f) :
    (1 / 2) * cutEnergy cut (agmonField G ε r u) + (poincareConst d / 4) * cwsq G
    (agmonField G ε r u) ≤
      (1 / poincareConst d) * agmonSource G ε r f := by
  have hp0 := poincareConst_pos hd
  have hpc : coerciveConst d = poincareConst d / 2 := rfl
  have hε12 : ε ≤ 1 / 2 := by linarith [agmonRate_le hd]
  set w : Torus d (N₀ * L ^ k) → ℝ := fun x => Real.exp (ε * r x) with hw
  have hwpos : ∀ x, 0 < w x := fun x => Real.exp_pos _
  set ut := zeroExt (G.Ω 1) u with hut
  set ft := zeroExt (G.Ω 1) f with hft
  set αt := zeroExt (G.Ω 1) α with hαt
  set p : Torus d (N₀ * L ^ k) → ℝ := fun x => (ut x).re with hp
  set q : Torus d (N₀ * L ^ k) → ℝ := fun x => (ut x).im with hq
  have hpz : ∀ x, x ∉ G.Ω 1 → p x = 0 := fun x hx => by simp [hp, hut, zeroExt_not_mem _ _ hx]
  have hqz : ∀ x, x ∉ G.Ω 1 → q x = 0 := fun x hx => by simp [hq, hut, zeroExt_not_mem _ _ hx]
  have core_p := weighted_core_cut G hcut hd hν ha hr hε0 hε12 hpz
  have core_q := weighted_core_cut G hcut hd hν ha hr hε0 hε12 hqz
  have hκ := kappa_le hd hε0 hε1
  set v := agmonField G ε r u with hv
  have hvre : (fun x => (v x).re) = fun x => w x * p x := by
    funext x; exact Complex.re_ofReal_mul _ _
  have hvim : (fun x => (v x).im) = fun x => w x * q x := by
    funext x; exact Complex.im_ofReal_mul _ _
  have hE : cutEnergy cut v = cutLatticeEnergy cut (fun x => w x * p x) + cutLatticeEnergy cut
    (fun x => w x * q x) := by
    rw [cutEnergy_eq, hvre, hvim]
  have hS : cwsq G v = wsq G (fun x => w x * p x) + wsq G (fun x => w x * q x) := by
    rw [cwsq_eq, hvre, hvim]
  -- the pointwise identity coming from the equation
  set Ap := cutFullMatrix G a ν cut *ᵥ p with hAp
  set Aq := cutFullMatrix G a ν cut *ᵥ q with hAq
  have hpt : ∀ x : Torus d (N₀ * L ^ k), w x ^ 2 * (star (ut x) * ft x).re =
      w x ^ 2 * p x * Ap x + w x ^ 2 * q x * Aq x + w x ^ 2 * (αt x).re * ‖ut x‖ ^ 2 := by
    intro x
    by_cases hx : x ∈ G.Ω 1
    · have heq := cutOperator_eq G hu ⟨x, hx⟩
      have h1 : ft x = ((cutFullMatrix G a ν cut).map (algebraMap ℝ ℂ) *ᵥ ut) x + αt x * ut x := by
        have e1 : ft x = f ⟨x, hx⟩ := zeroExt_mem (G.Ω 1) f ⟨x, hx⟩
        have e2 : αt x = α ⟨x, hx⟩ := zeroExt_mem (G.Ω 1) α ⟨x, hx⟩
        have e3 : ut x = u ⟨x, hx⟩ := zeroExt_mem (G.Ω 1) u ⟨x, hx⟩
        rw [e1, e2, e3]
        exact heq.symm
      rw [h1, mul_add, Complex.add_re, re_star_mul, re_star_mul_mul, re_mulVec_map, im_mulVec_map]
      simp only [hp, hq, hAp, hAq]
      ring
    · have : ut x = 0 := zeroExt_not_mem _ _ hx
      simp [this, hp, hq]
  -- the three sums
  set T : ℝ := ∑ x, w x ^ 2 * (star (ut x) * ft x).re with hT
  have hTsum : T = (∑ x, w x ^ 2 * p x * Ap x) + (∑ x, w x ^ 2 * q x * Aq x) +
      ∑ x, w x ^ 2 * (αt x).re * ‖ut x‖ ^ 2 := by
    rw [hT, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun x _ => hpt x
  have hRp : (∑ x, w x ^ 2 * p x * Ap x) =
      (fun x => Real.exp (ε * r x) ^ 2 * p x) ⬝ᵥ cutFullMatrix G a ν cut *ᵥ p := rfl
  have hRq : (∑ x, w x ^ 2 * q x * Aq x) =
      (fun x => Real.exp (ε * r x) ^ 2 * q x) ⬝ᵥ cutFullMatrix G a ν cut *ᵥ q := rfl
  -- the potential term
  have hpot : -(poincareConst d / 4 * cwsq G v) ≤ ∑ x, w x ^ 2 * (αt x).re * ‖ut x‖ ^ 2 := by
    unfold cwsq
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_le_sum fun x _ => ?_
    by_cases hx : x ∈ G.Ω 1
    · have hαx : ‖αt x‖ ≤ poincareConst d / (4 * (G.spacing x) ^ 2) := by
        have e : αt x = α ⟨x, hx⟩ := zeroExt_mem (G.Ω 1) α ⟨x, hx⟩
        rw [e]
        have := hα ⟨x, hx⟩
        rw [hpc] at this
        calc _ ≤ _ := this
          _ = _ := by field_simp; ring
      have hre : -(poincareConst d / (4 * (G.spacing x) ^ 2)) ≤ (αt x).re := by
        have := Complex.abs_re_le_norm (αt x)
        linarith [neg_abs_le (αt x).re]
      have hnv : ‖v x‖ ^ 2 = w x ^ 2 * ‖ut x‖ ^ 2 := by
        rw [hv, norm_agmonField]; ring
      rw [invSqSpacing_eq G hx, hnv]
      have hsp : 0 < (G.spacing x) ^ 2 := by have := spacing_pos G (x := x); positivity
      have e2 : -(poincareConst d / 4 * ((G.spacing x ^ 2)⁻¹ * (w x ^ 2 * ‖ut x‖ ^ 2))) =
          -(poincareConst d / (4 * (G.spacing x) ^ 2)) * (w x ^ 2 * ‖ut x‖ ^ 2) := by
        field_simp
      rw [e2]
      calc -(poincareConst d / (4 * (G.spacing x) ^ 2)) * (w x ^ 2 * ‖ut x‖ ^ 2)
          ≤ (αt x).re * (w x ^ 2 * ‖ut x‖ ^ 2) :=
            mul_le_mul_of_nonneg_right hre (by positivity)
        _ = _ := by ring
    · have h0 : ut x = 0 := zeroExt_not_mem _ _ hx
      have h1 : 0 ≤ poincareConst d / 4 * (invSqSpacing G x * ‖v x‖ ^ 2) := by
        have := invSqSpacing_nonneg G x
        positivity
      have h2 : w x ^ 2 * (αt x).re * ‖ut x‖ ^ 2 = 0 := by rw [h0]; simp
      linarith
  -- the source term
  have hsrc : T ≤ poincareConst d / 4 * cwsq G v + (1 / poincareConst d) * agmonSource G ε r f := by
    unfold cwsq agmonSource
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun x _ => ?_
    by_cases hx : x ∈ G.Ω 1
    · have hsp : 0 < G.spacing x := spacing_pos G
      have hnv : ‖v x‖ = w x * ‖ut x‖ := by rw [hv, norm_agmonField]
      have hnh : ‖((Real.exp (ε * r x) : ℝ) : ℂ) * ft x‖ = w x * ‖ft x‖ := by
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
      have hre : (star (ut x) * ft x).re ≤ ‖ut x‖ * ‖ft x‖ := by
        calc _ ≤ ‖star (ut x) * ft x‖ := Complex.re_le_norm _
          _ = _ := by rw [norm_mul, norm_star]
      have h1 : w x ^ 2 * (star (ut x) * ft x).re ≤ ‖v x‖ * (w x * ‖ft x‖) := by
        rw [hnv]
        have := mul_le_mul_of_nonneg_left hre (sq_nonneg (w x))
        nlinarith [this]
      rw [invSqSpacing_eq G hx, hnh]
      -- AM-GM
      set A := ‖v x‖
      set B := w x * ‖ft x‖
      set s := G.spacing x
      have hs2 : 0 < s ^ 2 := by positivity
      have key : A * B ≤ poincareConst d / 4 * ((s ^ 2)⁻¹ * A ^ 2) +
          1 / poincareConst d * (s ^ 2 * B ^ 2) := by
        have h0 : 0 ≤ 1 / poincareConst d * (s * B - poincareConst d / 2 * (A / s)) ^ 2 := by
          positivity
        have e : poincareConst d / 4 * ((s ^ 2)⁻¹ * A ^ 2) +
            1 / poincareConst d * (s ^ 2 * B ^ 2) - A * B =
            1 / poincareConst d * (s * B - poincareConst d / 2 * (A / s)) ^ 2 := by
          field_simp; ring
        linarith
      linarith
    · have : ut x = 0 := zeroExt_not_mem _ _ hx
      have h0 : 0 ≤ poincareConst d / 4 * (invSqSpacing G x * ‖v x‖ ^ 2) := by
        have := invSqSpacing_nonneg G x
        positivity
      have h1 : 0 ≤ 1 / poincareConst d * (G.spacing x ^ 2 * ‖((Real.exp (ε * r x) : ℝ) : ℂ) *
          zeroExt (G.Ω 1) f x‖ ^ 2) := by positivity
      simp only [this, star_zero, zero_mul, Complex.zero_re, mul_zero]
      linarith
  -- assemble
  have hcomb : (1 / 2) * cutEnergy cut v + (poincareConst d - (4 * d * ε ^ 2 + (Real.exp (ε *
    (2 * d)) - 1) ^ 2)) *
      cwsq G v ≤ (∑ x, w x ^ 2 * p x * Ap x) + (∑ x, w x ^ 2 * q x * Aq x) := by
    rw [hE, hS, hRp, hRq]
    nlinarith [core_p, core_q]
  have hS0 := cwsq_nonneg G v
  have hE0 := cEnergy_nonneg v
  nlinarith [hcomb, hTsum, hpot, hsrc, hκ, mul_nonneg hS0 (sub_nonneg.2 hκ)]



section Consequences

/-- `‖ℓ⁻¹ w u‖² ≤ 4 c⁻² ‖ℓ w f‖²`. -/
theorem agmon_wsq_le_cut (hcut : CutAligned G cut) (hd : 0 < d) {a : ℕ → ℝ} {ν : ℝ} (hν : 0 ≤ ν)
    (ha : IsAdmissibleWeights k a)
    (α : G.Ω 1 → ℂ) (hα : ∀ x, ‖α x‖ ≤ coerciveConst d / (2 * (G.spacing x) ^ 2))
    {r : Torus d (N₀ * L ^ k) → ℝ} (hr : IsAgmonWeight G r) {ε : ℝ} (hε0 : 0 ≤ ε)
    (hε1 : ε ≤ agmonRate d) {u f : G.Ω 1 → ℂ} (hu : cutOperator G a ν cut α *ᵥ u = f) :
    cwsq G (agmonField G ε r u) ≤ 4 / poincareConst d ^ 2 * agmonSource G ε r f := by
  have h := agmon_energy_cut G hcut hd hν ha α hα hr hε0 hε1 hu
  have hp0 := poincareConst_pos hd
  have hE := cutEnergy_nonneg cut (agmonField G ε r u)
  have h2 : poincareConst d / 4 * cwsq G (agmonField G ε r u) ≤
      1 / poincareConst d * agmonSource G ε r f := by linarith
  have h3 : cwsq G (agmonField G ε r u) ≤
      4 / poincareConst d ^ 2 * agmonSource G ε r f := by
    have e : 4 / poincareConst d ^ 2 * agmonSource G ε r f =
        4 / poincareConst d * (1 / poincareConst d * agmonSource G ε r f) := by
      field_simp
    rw [e]
    rw [show cwsq G (agmonField G ε r u) = 4 / poincareConst d *
      (poincareConst d / 4 * cwsq G (agmonField G ε r u)) by field_simp]
    exact mul_le_mul_of_nonneg_left h2 (by positivity)
  exact h3

/-- `‖∂(w ũ)‖² ≤ 2 c⁻¹ ‖ℓ w f‖²`. -/
theorem agmon_cEnergy_le_cut (hcut : CutAligned G cut) (hd : 0 < d) {a : ℕ → ℝ} {ν : ℝ} (hν : 0 ≤ ν)
    (ha : IsAdmissibleWeights k a) (α : G.Ω 1 → ℂ)
    (hα : ∀ x, ‖α x‖ ≤ coerciveConst d / (2 * (G.spacing x) ^ 2))
    {r : Torus d (N₀ * L ^ k) → ℝ} (hr : IsAgmonWeight G r) {ε : ℝ} (hε0 : 0 ≤ ε)
    (hε1 : ε ≤ agmonRate d) {u f : G.Ω 1 → ℂ} (hu : cutOperator G a ν cut α *ᵥ u = f) :
    cutEnergy cut (agmonField G ε r u) ≤ 2 / poincareConst d * agmonSource G ε r f := by
  have h := agmon_energy_cut G hcut hd hν ha α hα hr hε0 hε1 hu
  have hp0 := poincareConst_pos hd
  have hS := cwsq_nonneg G (agmonField G ε r u)
  have : (1 / 2) * cutEnergy cut
    (agmonField G ε r u) ≤ 1 / poincareConst d * agmonSource G ε r f := by
    nlinarith [mul_nonneg hp0.le hS]
  have e : 2 / poincareConst d * agmonSource G ε r f =
      2 * (1 / poincareConst d * agmonSource G ε r f) := by ring
  linarith


end Consequences

/-- `∑_{x ∈ Δ_j(y)} ∑_μ |ṽ(x + e_μ) - ṽ(x)|²` over the retained bonds only (the gradient energy of
the block `Δ_j(y)`; the removed bonds are not counted). -/
noncomputable def cutBlockGrad (cut : Finset (Torus d (N₀ * L ^ k) × Fin d)) (j : ℕ)
    (y : Torus d (N₀ * L ^ k)) (v : Torus d (N₀ * L ^ k) → ℂ) : ℝ :=
  ∑ x ∈ G.blk j y, ∑ μ : Fin d, if (x, μ) ∈ cut then 0 else ‖v (x + Pi.single μ 1) - v x‖ ^ 2

theorem cutBlockGrad_nonneg (cut : Finset (Torus d (N₀ * L ^ k) × Fin d)) (j : ℕ)
    (y : Torus d (N₀ * L ^ k)) (v : Torus d (N₀ * L ^ k) → ℂ) : 0 ≤ cutBlockGrad G cut j y v :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by split_ifs <;> positivity


/-- The weighted gradient on the block, over the retained bonds, is controlled by the retained
energy and the weighted norm. -/
theorem blk_grad_le_cut {r : Torus d (N₀ * L ^ k) → ℝ} (hr : IsAgmonWeight G r) {ε : ℝ}
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1 / 2) {j : ℕ} (hj1 : 1 ≤ j) (hjk : j ≤ k)
    {y : Torus d (N₀ * L ^ k)} (hy : y ∈ G.layer j) (u : G.Ω 1 → ℂ) :
    Real.exp (2 * ε * (r y - 2 * d)) * cutBlockGrad G cut j y (zeroExt (G.Ω 1) u) ≤
      2 * cutEnergy cut (agmonField G ε r u) + 8 * ε ^ 2 * (d * cwsq G (agmonField G ε r u)) := by
  unfold cutBlockGrad
  set v := agmonField G ε r u with hv
  have hF0 : ∀ x, 0 ≤ 8 * ε ^ 2 * (invSqSpacing G x * ‖v x‖ ^ 2) := fun x => by
    have := invSqSpacing_nonneg G x
    positivity
  calc _ = ∑ x ∈ G.blk j y, ∑ μ : Fin d, Real.exp (2 * ε * (r y - 2 * d)) *
          (if (x, μ) ∈ cut then 0 else
          ‖zeroExt (G.Ω 1) u (x + Pi.single μ 1) - zeroExt (G.Ω 1) u x‖ ^ 2) := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun x _ => by rw [Finset.mul_sum]
    _ ≤ ∑ x ∈ G.blk j y, ∑ μ : Fin d,
          ((if (x, μ) ∈ cut then 0 else 2 * ‖v (x + Pi.single μ 1) - v x‖ ^ 2) +
            8 * ε ^ 2 * (invSqSpacing G (x + Pi.single μ 1) * ‖v (x + Pi.single μ 1)‖ ^ 2)) := by
        refine Finset.sum_le_sum fun x hx => Finset.sum_le_sum fun μ _ => ?_
        have hxl : x ∈ G.layer j := (G.mem_layer_iff hj1 hjk (G.mem_blk.1 hx)).2 hy
        have hxm : x ∈ G.Ω 1 := G.layer_subset hj1 hjk hxl
        split_ifs with hc
        · simpa using hF0 (x + Pi.single μ 1)
        · have h1 := agmon_grad_pointwise G hr hε0 hε1 u hxm μ
          calc _ ≤ Real.exp (ε * r x) ^ 2 *
                ‖zeroExt (G.Ω 1) u (x + Pi.single μ 1) - zeroExt (G.Ω 1) u x‖ ^ 2 :=
                mul_le_mul_of_nonneg_right (blk_weight_ge G hr hε0 hj1 hjk hy hx) (sq_nonneg _)
            _ ≤ _ := h1
    _ ≤ ∑ x, ∑ μ : Fin d,
          ((if (x, μ) ∈ cut then 0 else 2 * ‖v (x + Pi.single μ 1) - v x‖ ^ 2) +
            8 * ε ^ 2 * (invSqSpacing G (x + Pi.single μ 1) * ‖v (x + Pi.single μ 1)‖ ^ 2)) := by
        refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun x _ _ => ?_
        refine Finset.sum_nonneg fun μ _ => ?_
        have := hF0 (x + Pi.single μ 1)
        split_ifs <;> positivity
    _ = 2 * cutEnergy cut v + 8 * ε ^ 2 * (d * cwsq G v) := by
        simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
        rw [sum_shift_cwsq]
        unfold cutEnergy
        rw [Finset.mul_sum]
        congr 1
        · refine Finset.sum_congr rfl fun x _ => ?_
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun μ _ => by split_ifs <;> simp

/-- **Agmon block decay.**  See the module docstring. -/
theorem agmon_block_cut (G : GeneratingSet d L N₀ k ϱ) (hcut : CutAligned G cut) (hd : 0 < d)
    {a : ℕ → ℝ} {ν : ℝ} (hν : 0 ≤ ν)
    (ha : IsAdmissibleWeights k a) (α : G.Ω 1 → ℂ)
    (hα : ∀ x, ‖α x‖ ≤ coerciveConst d / (2 * (G.spacing x) ^ 2))
    {j j' : ℕ} (hj1 : 1 ≤ j) (hjk : j ≤ k) (hj'1 : 1 ≤ j') (hj'k : j' ≤ k)
    {y y' : Torus d (N₀ * L ^ k)} (hy : y ∈ G.layer j) (hy' : y' ∈ G.layer j')
    {u f : G.Ω 1 → ℂ} (hu : cutOperator G a ν cut α *ᵥ u = f)
    (hsupp : ∀ x : G.Ω 1, f x ≠ 0 → jBlock d L N₀ k j' x = jBlock d L N₀ k j' y')
    {t : ℝ} (ht0 : 0 ≤ t) (ht : ENNReal.ofReal t ≤ G.pathDist y y') {ε : ℝ} (hε0 : 0 ≤ ε)
    (hε1 : ε ≤ agmonRate d) :
    (∑ x ∈ G.blk j y, ‖zeroExt (G.Ω 1) u x‖ ^ 2 ≤
        8 / poincareConst d ^ 2 * ((L : ℝ) ^ j) ^ 2 * ((L : ℝ) ^ j') ^ 2 * Real.exp (-(2 * ε * t)) *
          Green.sqNorm f) ∧
    (cutBlockGrad G cut j y (zeroExt (G.Ω 1) u) ≤
        10 / poincareConst d * ((L : ℝ) ^ j') ^ 2 * Real.exp (-(2 * ε * t)) * Green.sqNorm f) := by
  have hp0 := poincareConst_pos hd
  have hε12 : ε ≤ 1 / 2 := by linarith [agmonRate_le hd]
  have hεd := rate_mul_le hd hε1
  have h8 : Real.exp (8 * (ε * d)) ≤ 2 := exp_eight_mul_le_two (by positivity) hεd
  have hr : IsAgmonWeight G (G.truncDist y' t) := G.isAgmonWeight_truncDist y' t
  have hry : G.truncDist y' t y = t := G.truncDist_eq_of_le ht0 ht
  have hry' : G.truncDist y' t y' = 0 := G.truncDist_self (G.layer_subset hj'1 hj'k hy') t
  have hS := agmon_wsq_le_cut G hcut hd hν ha α hα hr hε0 hε1 hu
  have hE := agmon_cEnergy_le_cut G hcut hd hν ha α hα hr hε0 hε1 hu
  have hsrc := agmonSource_le G hr hε0 hj'1 hj'k hy' hry' hsupp
  have hlow := blk_lower G hr hε0 hj1 hjk hy u
  have hgrad := blk_grad_le_cut G (cut := cut) hr hε0 hε12 hj1 hjk hy u
  rw [hry] at hlow hgrad
  have hHh0 := agmonSource_nonneg G ε (G.truncDist y' t) f
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
  have hsf := Green.sqNorm_nonneg f
  refine ⟨?_, ?_⟩
  · have hX2 : ∑ x ∈ G.blk j y, ‖zeroExt (G.Ω 1) u x‖ ^ 2 ≤ ((L : ℝ) ^ j) ^ 2 *
        (Real.exp (-(2 * ε * t)) * Real.exp (4 * ε * d)) *
          cwsq G (agmonField G ε (G.truncDist y' t) u) := by
      rw [← hE2inv]
      have := mul_le_mul_of_nonneg_left hlow
        (mul_nonneg hA0.le (inv_nonneg.2 hE20.le))
      calc _ = (((L : ℝ) ^ j) ^ 2 * (Real.exp (2 * ε * (t - 2 * d)))⁻¹) *
            ((((L : ℝ) ^ j) ^ 2)⁻¹ * Real.exp (2 * ε * (t - 2 * d)) *
              ∑ x ∈ G.blk j y, ‖zeroExt (G.Ω 1) u x‖ ^ 2) := by field_simp
        _ ≤ _ := this
        _ = _ := by ring
    exact numeric_a hp0 hA0.le (by positivity) (Real.exp_pos _).le (Real.exp_pos _).le hsf
      hX2 hS hsrc hZZ
  · have hY2 : cutBlockGrad G cut j y (zeroExt (G.Ω 1) u) ≤
        (Real.exp (-(2 * ε * t)) * Real.exp (4 * ε * d)) *
          (5 / poincareConst d * agmonSource G ε (G.truncDist y' t) f) := by
      have h1 := hgrad.trans (numeric_grad hd hε0 hε1 hHh0 hS hE)
      rw [← hE2inv, ← div_eq_inv_mul, le_div_iff₀ hE20]
      linarith
    exact numeric_b hp0 (by positivity) (Real.exp_pos _).le (Real.exp_pos _).le hsf hY2 hsrc hZZ


/-- **G-2(i).**  For `f` supported in the block `Δ_{j'}(y')` (`y'` in layer `j'`), `u` with
`H_D(α) u = f`, `y` in layer `j`, `0 ≤ ε ≤ ε₀`, `ϱ ≥ 1` with `L ≤ exp ((ε/2)(ϱ - 1))`, and every
`t ≥ 0` with `t ≤ d(y, y')`:
`ℓ_j ‖χ_{Δ_j(y)} ∂ũ‖ + ‖χ_{Δ_j(y)} ũ‖ ≤ (13 L / c) e^{-(ε/2) t} ℓ_{j'}² ‖f‖`. -/
theorem green_G2i_cut (G : GeneratingSet d L N₀ k ϱ) (hcut : CutAligned G cut) (hd : 0 < d)
    {a : ℕ → ℝ} {ν : ℝ} (hν : 0 ≤ ν)
    (ha : IsAdmissibleWeights k a) (α : G.Ω 1 → ℂ)
    (hα : ∀ x, ‖α x‖ ≤ coerciveConst d / (2 * (G.spacing x) ^ 2))
    {j j' : ℕ} (hj1 : 1 ≤ j) (hjk : j ≤ k) (hj'1 : 1 ≤ j') (hj'k : j' ≤ k)
    {y y' : Torus d (N₀ * L ^ k)} (hy : y ∈ G.layer j) (hy' : y' ∈ G.layer j')
    {u f : G.Ω 1 → ℂ} (hu : cutOperator G a ν cut α *ᵥ u = f)
    (hsupp : ∀ x : G.Ω 1, f x ≠ 0 → jBlock d L N₀ k j' x = jBlock d L N₀ k j' y')
    {t : ℝ} (ht0 : 0 ≤ t) (ht : ENNReal.ofReal t ≤ G.pathDist y y') {ε : ℝ} (hε0 : 0 ≤ ε)
    (hε1 : ε ≤ agmonRate d) (hϱ : 1 ≤ ϱ) (hsep : (L : ℝ) ≤ Real.exp (ε / 2 * (ϱ - 1))) :
    (L : ℝ) ^ j * Real.sqrt (cutBlockGrad G cut j y (zeroExt (G.Ω 1) u)) +
      Real.sqrt (∑ x ∈ G.blk j y, ‖zeroExt (G.Ω 1) u x‖ ^ 2) ≤
    13 * L / poincareConst d * Real.exp (-(ε / 2 * t)) * ((L : ℝ) ^ j') ^ 2 *
      Real.sqrt (Green.sqNorm f) := by
  have hp0 := poincareConst_pos hd
  have hph := poincareConst_le_half d
  have hL : (1 : ℝ) ≤ L := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne L)
  have hL0 : (0 : ℝ) < L := by linarith
  -- the separation lower bound for the distance
  have hyΩ : y ∈ G.Ω j := (G.mem_layer.1 hy).1
  have hsep0 := G.pathDist_separation_le hϱ hj'1 hjk hy' hyΩ
  rw [GeneratingSet.pathDist_comm] at hsep0
  set s₀ : ℝ := (ϱ - 1) * ((j - j' - 1 : ℕ) : ℝ) with hs₀
  have hs₀0 : 0 ≤ s₀ := mul_nonneg (by linarith) (Nat.cast_nonneg _)
  set t₂ := max t s₀ with ht₂
  have ht₂0 : 0 ≤ t₂ := ht0.trans (le_max_left _ _)
  have ht₂d : ENNReal.ofReal t₂ ≤ G.pathDist y y' := by
    rcases le_total t s₀ with h | h
    · rw [ht₂, max_eq_right h]; exact hsep0
    · rw [ht₂, max_eq_left h]; exact ht
  obtain ⟨hA, hB⟩ := agmon_block_cut G hcut hd hν ha α hα hj1 hjk hj'1 hj'k hy hy' hu hsupp ht₂0 ht₂d hε0 hε1
  have hmis := scale_mismatch (L := L) (ε := ε) (t := t) (t₂ := t₂) hε0 j j' hsep
    (le_max_left _ _) (le_max_right _ _)
  set F := Green.sqNorm f with hF
  have hF0 : 0 ≤ F := Green.sqNorm_nonneg f
  set P : ℝ := (L : ℝ) ^ j * (L : ℝ) ^ j' * Real.exp (-(ε * t₂)) * Real.sqrt F with hP
  have hP0 : 0 ≤ P := by positivity
  have hP2 : P ^ 2 = ((L : ℝ) ^ j) ^ 2 * ((L : ℝ) ^ j') ^ 2 * Real.exp (-(2 * ε * t₂)) * F := by
    rw [hP, mul_pow, mul_pow, mul_pow, Real.sq_sqrt hF0, ← Real.exp_nat_mul]
    congr 2
    · push_cast; ring_nf
  have hPle : P ≤ L * ((L : ℝ) ^ j') ^ 2 * Real.exp (-(ε / 2 * t)) * Real.sqrt F := by
    rw [hP]
    exact mul_le_mul_of_nonneg_right hmis (Real.sqrt_nonneg _)
  clear_value P
  set Nn := ∑ x ∈ G.blk j y, ‖zeroExt (G.Ω 1) u x‖ ^ 2 with hNn
  set Yy := cutBlockGrad G cut j y (zeroExt (G.Ω 1) u) with hYy
  have hY0 : 0 ≤ Yy := cutBlockGrad_nonneg G cut j y _
  have hN0 : 0 ≤ Nn := Finset.sum_nonneg fun _ _ => sq_nonneg _
  -- the two square-root bounds
  have h1 : Real.sqrt Nn ≤ 3 / poincareConst d * P := by
    rw [Real.sqrt_le_iff]
    refine ⟨by positivity, ?_⟩
    calc Nn ≤ 8 / poincareConst d ^ 2 * P ^ 2 := by rw [hP2]; convert hA using 1; ring
      _ ≤ (3 / poincareConst d * P) ^ 2 := by
        rw [mul_pow, div_pow]
        have : 8 / poincareConst d ^ 2 ≤ 3 ^ 2 / poincareConst d ^ 2 :=
          div_le_div_of_nonneg_right (by norm_num) (by positivity)
        exact mul_le_mul_of_nonneg_right this (sq_nonneg _)
  have h2 : (L : ℝ) ^ j * Real.sqrt Yy ≤ 10 / poincareConst d * P := by
    have hsq : ((L : ℝ) ^ j * Real.sqrt Yy) ^ 2 ≤ (10 / poincareConst d * P) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hY0, mul_pow]
      have hB' : ((L : ℝ) ^ j) ^ 2 * Yy ≤ 10 / poincareConst d * P ^ 2 := by
        rw [hP2]
        calc ((L : ℝ) ^ j) ^ 2 * Yy ≤ ((L : ℝ) ^ j) ^ 2 *
              (10 / poincareConst d * ((L : ℝ) ^ j') ^ 2 * Real.exp (-(2 * ε * t₂)) * F) :=
            mul_le_mul_of_nonneg_left hB (by positivity)
          _ = _ := by ring
      have h10 : 10 / poincareConst d ≤ (10 / poincareConst d) ^ 2 := by
        have : 1 ≤ 10 / poincareConst d := by
          rw [le_div_iff₀ hp0]; linarith
        nlinarith
      calc _ ≤ 10 / poincareConst d * P ^ 2 := hB'
        _ ≤ (10 / poincareConst d) ^ 2 * P ^ 2 := mul_le_mul_of_nonneg_right h10 (sq_nonneg _)
    exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).1 hsq
  calc (L : ℝ) ^ j * Real.sqrt Yy + Real.sqrt Nn ≤ 10 / poincareConst d * P + 3 / poincareConst d * P :=
        add_le_add h2 h1
    _ = 13 / poincareConst d * P := by ring
    _ ≤ 13 / poincareConst d * (L * ((L : ℝ) ^ j') ^ 2 * Real.exp (-(ε / 2 * t)) * Real.sqrt F) :=
        mul_le_mul_of_nonneg_left hPle (by positivity)
    _ = _ := by ring


/-- G-2(i) with the distance of the path metric itself: if `d(y, y') < ⊤`, the bound holds with
`t = d(y, y')`; if `d(y, y') = ⊤` (no path in `Ω₁`), `u` vanishes on `Δ_j(y)` (it has zero gradient
energy and zero norm there). -/
theorem green_G2i_cut_of_pathDist (G : GeneratingSet d L N₀ k ϱ) (hcut : CutAligned G cut)
    (hd : 0 < d) {a : ℕ → ℝ} {ν : ℝ}
    (hν : 0 ≤ ν) (ha : IsAdmissibleWeights k a) (α : G.Ω 1 → ℂ)
    (hα : ∀ x, ‖α x‖ ≤ coerciveConst d / (2 * (G.spacing x) ^ 2))
    {j j' : ℕ} (hj1 : 1 ≤ j) (hjk : j ≤ k) (hj'1 : 1 ≤ j') (hj'k : j' ≤ k)
    {y y' : Torus d (N₀ * L ^ k)} (hy : y ∈ G.layer j) (hy' : y' ∈ G.layer j')
    {u f : G.Ω 1 → ℂ} (hu : cutOperator G a ν cut α *ᵥ u = f)
    (hsupp : ∀ x : G.Ω 1, f x ≠ 0 → jBlock d L N₀ k j' x = jBlock d L N₀ k j' y')
    (hϱ : 1 ≤ ϱ) (hsep : (L : ℝ) ≤ Real.exp (agmonRate d / 2 * (ϱ - 1))) :
    (G.pathDist y y' ≠ ⊤ →
      (L : ℝ) ^ j * Real.sqrt (cutBlockGrad G cut j y (zeroExt (G.Ω 1) u)) +
        Real.sqrt (∑ x ∈ G.blk j y, ‖zeroExt (G.Ω 1) u x‖ ^ 2) ≤
      13 * L / poincareConst d * Real.exp (-(agmonRate d / 2 * (G.pathDist y y').toReal)) *
        ((L : ℝ) ^ j') ^ 2 * Real.sqrt (Green.sqNorm f)) ∧
    (G.pathDist y y' = ⊤ →
      (L : ℝ) ^ j * Real.sqrt (cutBlockGrad G cut j y (zeroExt (G.Ω 1) u)) +
        Real.sqrt (∑ x ∈ G.blk j y, ‖zeroExt (G.Ω 1) u x‖ ^ 2) ≤ 0) := by
  have hε0 : 0 < agmonRate d := agmonRate_pos hd
  have hp0 := poincareConst_pos hd
  have hL0 : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  refine ⟨fun hne => ?_, fun htop => ?_⟩
  · exact green_G2i_cut G hcut hd hν ha α hα hj1 hjk hj'1 hj'k hy hy' hu hsupp ENNReal.toReal_nonneg
      (by rw [ENNReal.ofReal_toReal hne]) hε0.le le_rfl hϱ hsep
  · set LHS := (L : ℝ) ^ j * Real.sqrt (cutBlockGrad G cut j y (zeroExt (G.Ω 1) u)) +
        Real.sqrt (∑ x ∈ G.blk j y, ‖zeroExt (G.Ω 1) u x‖ ^ 2) with hLHS
    set K : ℝ := 13 * L / poincareConst d * ((L : ℝ) ^ j') ^ 2 * Real.sqrt (Green.sqNorm f) with hK
    have hK0 : 0 ≤ K := by positivity
    have hbound : ∀ t : ℝ, 0 ≤ t → LHS ≤ K * Real.exp (-(agmonRate d / 2 * t)) := by
      intro t ht0
      have := green_G2i_cut G hcut hd hν ha α hα hj1 hjk hj'1 hj'k hy hy' hu hsupp ht0
        (by rw [htop]; exact le_top) hε0.le le_rfl hϱ hsep
      calc LHS ≤ _ := this
        _ = _ := by rw [hK]; ring
    have hLHS0 : 0 ≤ LHS := by positivity
    by_contra hpos
    push Not at hpos
    set c := agmonRate d / 2 with hc
    have hc0 : 0 < c := by positivity
    set t := K / (c * LHS) with ht
    have ht0 : 0 ≤ t := by positivity
    have h1 := hbound t ht0
    have h2 : Real.exp (c * t) ≥ 1 + c * t := by linarith [Real.add_one_le_exp (c * t)]
    have h3 : K * Real.exp (-(c * t)) * (1 + c * t) ≤ K := by
      have : Real.exp (-(c * t)) * Real.exp (c * t) = 1 := by rw [← Real.exp_add]; simp
      calc K * Real.exp (-(c * t)) * (1 + c * t) ≤ K * Real.exp (-(c * t)) * Real.exp (c * t) :=
            mul_le_mul_of_nonneg_left h2 (by positivity)
        _ = K := by rw [mul_assoc, this, mul_one]
    have h4 : c * t = K / LHS := by rw [ht]; field_simp
    rw [h4] at h3 h1
    have h5 : LHS * (1 + K / LHS) = LHS + K := by field_simp
    have h6 : LHS * (1 + K / LHS) ≤ K * Real.exp (-(K / LHS)) * (1 + K / LHS) :=
      mul_le_mul_of_nonneg_right (by simpa [h4] using h1) (by positivity)
    nlinarith


/-- `H_D(α) G_D(α) f = f` for the Green's function `G_D(α) = H_D(α)⁻¹`. -/
theorem cutOperator_mulVec_inv (G : GeneratingSet d L N₀ k ϱ) (hcut : CutAligned G cut)
    (hd : 0 < d) {a : ℕ → ℝ}
    {ν : ℝ} (hν : 0 ≤ ν) (ha : IsAdmissibleWeights k a) (α : G.Ω 1 → ℂ)
    (hα : ∀ x, ‖α x‖ ≤ coerciveConst d / (2 * (G.spacing x) ^ 2)) (f : G.Ω 1 → ℂ) :
    cutOperator G a ν cut α *ᵥ ((cutOperator G a ν cut α)⁻¹ *ᵥ f) = f := by
  have hU := cutOperator_isUnit G hcut hd hν ha α hα
  rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hU),
    Matrix.one_mulVec]

/-- **G-2(i) for the Green's function** `G_D(α) = H_D(α)⁻¹`: the block-to-block bound
`ℓ_j ‖χ_{Δ_j(y)} ∂ G_D f‖ + ‖χ_{Δ_j(y)} G_D f‖ ≤ (13 L / c) e^{-(ε/2) t} ℓ_{j'}² ‖f‖` for `f`
supported in `Δ_{j'}(y')` and `0 ≤ t ≤ d(y, y')`, uniformly over `α` with `|α| ≤ c₁ ℓ⁻²/2`. -/
theorem green_G2i_cut_green (G : GeneratingSet d L N₀ k ϱ) (hcut : CutAligned G cut) (hd : 0 < d)
    {a : ℕ → ℝ} {ν : ℝ}
    (hν : 0 ≤ ν) (ha : IsAdmissibleWeights k a) (α : G.Ω 1 → ℂ)
    (hα : ∀ x, ‖α x‖ ≤ coerciveConst d / (2 * (G.spacing x) ^ 2))
    {j j' : ℕ} (hj1 : 1 ≤ j) (hjk : j ≤ k) (hj'1 : 1 ≤ j') (hj'k : j' ≤ k)
    {y y' : Torus d (N₀ * L ^ k)} (hy : y ∈ G.layer j) (hy' : y' ∈ G.layer j')
    {f : G.Ω 1 → ℂ}
    (hsupp : ∀ x : G.Ω 1, f x ≠ 0 → jBlock d L N₀ k j' x = jBlock d L N₀ k j' y')
    {t : ℝ} (ht0 : 0 ≤ t) (ht : ENNReal.ofReal t ≤ G.pathDist y y') {ε : ℝ} (hε0 : 0 ≤ ε)
    (hε1 : ε ≤ agmonRate d) (hϱ : 1 ≤ ϱ) (hsep : (L : ℝ) ≤ Real.exp (ε / 2 * (ϱ - 1))) :
    (L : ℝ) ^ j * Real.sqrt (cutBlockGrad G cut j y (zeroExt (G.Ω 1)
    ((cutOperator G a ν cut α)⁻¹ *ᵥ f))) +
      Real.sqrt (∑ x ∈ G.blk j y, ‖zeroExt (G.Ω 1) ((cutOperator G a ν cut α)⁻¹ *ᵥ f) x‖ ^ 2) ≤
    13 * L / poincareConst d * Real.exp (-(ε / 2 * t)) * ((L : ℝ) ^ j') ^ 2 *
      Real.sqrt (Green.sqNorm f) :=
  green_G2i_cut G hcut hd hν ha α hα hj1 hjk hj'1 hj'k hy hy'
    (cutOperator_mulVec_inv G hcut hd hν ha α hα f) hsupp ht0 ht hε0 hε1 hϱ hsep


end Balaban.Multiscale
