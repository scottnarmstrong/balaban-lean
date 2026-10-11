/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Multiscale.AgmonCore
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

/-!
# The Agmon estimate (GREEN.md §4.2, Proposition 4.5)

Let `u` solve `H_D(α) u = f` on `Ω₁` (`Balaban.Multiscale.dirichletOperator`), and let `r` be an
admissible weight exponent (`Balaban.Multiscale.IsAgmonWeight`; the truncated path distance to a
point is one, `Balaban/Multiscale/AgmonWeight.lean`), `w = exp (ε r)` with `0 ≤ ε ≤ ε₀`,
`ε₀ = c / (16 d)` (`Balaban.Multiscale.agmonRate`), `c = poincareConst d` the Poincaré constant of
the landed block Poincaré inequality (GREEN.md has `ε₀ = 1/(184 d)`, constants differ because
`c` depends on `d`).  With `v = w ũ` (`ũ` the zero extension of `u`) the main inequality is

`½ ‖∂v‖² + (c/4) ‖ℓ⁻¹ v‖² ≤ c⁻¹ ‖ℓ w f‖²`   (`Balaban.Multiscale.agmon_energy`),

hence `‖ℓ⁻¹ w u‖² ≤ 4 c⁻² ‖ℓ w f‖²`, `‖∂(w ũ)‖² ≤ 2 c⁻¹ ‖ℓ w f‖²` and the weighted gradient bound
`‖w ∂ũ‖² ≤ 5 c⁻¹ ‖ℓ w f‖²` (`agmon_wsq_le`, `agmon_grad_le`).  The proof is the test-function
form of §4.2: the real part of `⟨w² ũ, H ũ⟩ = ⟨w² ũ, f⟩`, the conjugation errors of
`Balaban.Multiscale.weighted_core`, coercivity (`core_real`), and Cauchy–Schwarz.
-/

@[expose] public section

namespace Balaban.Multiscale

open Finset Matrix Balaban

variable {d L N₀ k : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}

/-! ### Algebra of the zero extension -/

theorem restrictOp_mulVec {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℂ)
    (Λ : Finset ι) (u : Λ → ℂ) (x : Λ) :
    (Green.restrictOp A Λ *ᵥ u) x = (A *ᵥ zeroExt Λ u) (x : ι) := by
  simp only [Matrix.mulVec, dotProduct]
  rw [Green.sum_eq_sum_subtype Λ _ (fun i hi => by simp [zeroExt, hi])]
  refine Finset.sum_congr rfl fun z _ => ?_
  simp [Green.restrictOp, zeroExt, z.2]

theorem dirichlet_eq (G : GeneratingSet d L N₀ k ϱ) {a : ℕ → ℝ} {ν : ℝ} {α : G.Ω 1 → ℂ}
    {u f : G.Ω 1 → ℂ} (hu : dirichletOperator G a ν α *ᵥ u = f) (x : G.Ω 1) :
    ((fullMatrix G a ν).map (algebraMap ℝ ℂ) *ᵥ zeroExt (G.Ω 1) u) (x : Torus d (N₀ * L ^ k)) +
      α x * u x = f x := by
  have h := congrFun hu x
  unfold dirichletOperator at h
  rw [Matrix.add_mulVec, Pi.add_apply, Matrix.mulVec_diagonal, restrictOp_mulVec] at h
  exact h

theorem re_mulVec_map {ι : Type*} [Fintype ι] (A : Matrix ι ι ℝ) (ψ : ι → ℂ) (x : ι) :
    ((A.map (algebraMap ℝ ℂ) *ᵥ ψ) x).re = (A *ᵥ fun i => (ψ i).re) x := by
  simp [Matrix.mulVec, dotProduct, Complex.re_sum, Complex.mul_re]

theorem im_mulVec_map {ι : Type*} [Fintype ι] (A : Matrix ι ι ℝ) (ψ : ι → ℂ) (x : ι) :
    ((A.map (algebraMap ℝ ℂ) *ᵥ ψ) x).im = (A *ᵥ fun i => (ψ i).im) x := by
  simp [Matrix.mulVec, dotProduct, Complex.im_sum, Complex.mul_im]

theorem re_star_mul (a z : ℂ) : (star a * z).re = a.re * z.re + a.im * z.im := by
  simp [Complex.mul_re]

theorem zeroExt_mem {ι : Type*} [DecidableEq ι] (Λ : Finset ι) (u : Λ → ℂ) (i : Λ) :
    zeroExt Λ u i = u i := by simp [zeroExt, i.2]

theorem zeroExt_not_mem {ι : Type*} [DecidableEq ι] (Λ : Finset ι) (u : Λ → ℂ) {i : ι}
    (h : i ∉ Λ) : zeroExt Λ u i = 0 := by simp [zeroExt, h]

/-! ### The rate -/

/-- The Agmon rate `ε₀ = c / (16 d)`, `c = poincareConst d`. -/
noncomputable def agmonRate (d : ℕ) : ℝ := poincareConst d / (16 * d)

theorem agmonRate_pos (hd : 0 < d) : 0 < agmonRate d := by
  unfold agmonRate
  have := poincareConst_pos hd
  have : (0 : ℝ) < d := by exact_mod_cast hd
  positivity

theorem poincareConst_le_half (d : ℕ) : poincareConst d ≤ 1 / 2 := min_le_right _ _

theorem agmonRate_le (hd : 0 < d) : agmonRate d ≤ 1 / 32 := by
  have hp := poincareConst_le_half d
  have hdd : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hp0 := poincareConst_pos hd
  unfold agmonRate
  rw [div_le_iff₀ (by positivity)]
  nlinarith

/-- The total conjugation error is at most a quarter of the Poincaré constant. -/
theorem kappa_le (hd : 0 < d) {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ agmonRate d) :
    4 * d * ε ^ 2 + (Real.exp (ε * (2 * d)) - 1) ^ 2 ≤ poincareConst d / 4 := by
  have hdd : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hp := poincareConst_le_half d
  have hp0 := poincareConst_pos hd
  have hεd : ε * d ≤ poincareConst d / 16 := by
    have : ε * d ≤ agmonRate d * d := by gcongr
    have e : agmonRate d * d = poincareConst d / 16 := by
      unfold agmonRate; field_simp
    linarith
  have hs : ε * (2 * d) ≤ 1 / 2 := by nlinarith
  have h1 : Real.exp (ε * (2 * d)) - 1 ≤ 2 * (ε * (2 * d)) :=
    exp_sub_one_le_two_mul (by positivity) hs
  have h0 : 0 ≤ Real.exp (ε * (2 * d)) - 1 := by
    have := Real.add_one_le_exp (ε * (2 * d)); have : 0 ≤ ε * (2 * d) := by positivity
    linarith
  have h2 : (Real.exp (ε * (2 * d)) - 1) ^ 2 ≤ (4 * (ε * d)) ^ 2 := by
    have : Real.exp (ε * (2 * d)) - 1 ≤ 4 * (ε * d) := by linarith
    exact pow_le_pow_left₀ h0 this 2
  have h3 : 4 * (d : ℝ) * ε ^ 2 ≤ 4 * (ε * d) ^ 2 := by
    have : (d : ℝ) ≤ (d : ℝ) ^ 2 := by nlinarith
    nlinarith [sq_nonneg ε]
  have hεd0 : 0 ≤ ε * d := by positivity
  nlinarith [mul_nonneg hεd0 hεd0]


/-! ### Weighted norms of complex fields -/

section Norms

variable (G : GeneratingSet d L N₀ k ϱ)

/-- `‖ℓ⁻¹ v‖²` for a complex field on the torus (`ℓ⁻² = 0` off `Ω₁`). -/
noncomputable def cwsq (v : Torus d (N₀ * L ^ k) → ℂ) : ℝ :=
  ∑ x, invSqSpacing G x * ‖v x‖ ^ 2

/-- `‖∂ v‖²`: the sum of `|v(x + e_μ) - v(x)|²` over all bonds of the torus. -/
noncomputable def cEnergy (v : Torus d (N₀ * L ^ k) → ℂ) : ℝ :=
  ∑ x, ∑ μ : Fin d, ‖v (x + Pi.single μ 1) - v x‖ ^ 2

theorem cwsq_eq (v : Torus d (N₀ * L ^ k) → ℂ) :
    cwsq G v = wsq G (fun x => (v x).re) + wsq G (fun x => (v x).im) := by
  unfold cwsq wsq
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Complex.sq_norm, Complex.normSq_apply]; ring

theorem cEnergy_eq (v : Torus d (N₀ * L ^ k) → ℂ) :
    cEnergy v = latticeEnergy (fun x => (v x).re) + latticeEnergy (fun x => (v x).im) := by
  unfold cEnergy latticeEnergy
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.sub_im]
  ring

theorem cwsq_nonneg (v : Torus d (N₀ * L ^ k) → ℂ) : 0 ≤ cwsq G v :=
  Finset.sum_nonneg fun x _ => mul_nonneg (invSqSpacing_nonneg G x) (sq_nonneg _)

theorem cEnergy_nonneg (v : Torus d (N₀ * L ^ k) → ℂ) : 0 ≤ cEnergy v :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- The conjugated field `v = w ũ`, `w = exp (ε r)`, `ũ` the zero extension of `u`. -/
noncomputable def agmonField (ε : ℝ) (r : Torus d (N₀ * L ^ k) → ℝ) (u : G.Ω 1 → ℂ)
    (x : Torus d (N₀ * L ^ k)) : ℂ :=
  ((Real.exp (ε * r x) : ℝ) : ℂ) * zeroExt (G.Ω 1) u x

/-- `‖ℓ w f‖²`, the weighted source norm (`f` extended by zero). -/
noncomputable def agmonSource (ε : ℝ) (r : Torus d (N₀ * L ^ k) → ℝ) (f : G.Ω 1 → ℂ) : ℝ :=
  ∑ x, (G.spacing x) ^ 2 * ‖((Real.exp (ε * r x) : ℝ) : ℂ) * zeroExt (G.Ω 1) f x‖ ^ 2

theorem agmonSource_nonneg (ε : ℝ) (r : Torus d (N₀ * L ^ k) → ℝ) (f : G.Ω 1 → ℂ) :
    0 ≤ agmonSource G ε r f :=
  Finset.sum_nonneg fun _ _ => by positivity

theorem norm_agmonField (ε : ℝ) (r : Torus d (N₀ * L ^ k) → ℝ) (u : G.Ω 1 → ℂ)
    (x : Torus d (N₀ * L ^ k)) :
    ‖agmonField G ε r u x‖ = Real.exp (ε * r x) * ‖zeroExt (G.Ω 1) u x‖ := by
  unfold agmonField
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]

end Norms

theorem re_star_mul_mul (z a : ℂ) : (star z * (a * z)).re = a.re * ‖z‖ ^ 2 := by
  simp only [Complex.mul_re, Complex.mul_im, Complex.star_def, Complex.conj_re, Complex.conj_im,
    Complex.sq_norm, Complex.normSq_apply]
  ring

/-- **The Agmon energy inequality** (GREEN.md Prop. 4.5): with `v = w ũ`,
`½ ‖∂v‖² + (c/4) ‖ℓ⁻¹ v‖² ≤ c⁻¹ ‖ℓ w f‖²`, `c = poincareConst d`. -/
theorem agmon_energy (G : GeneratingSet d L N₀ k ϱ) (hd : 0 < d) {a : ℕ → ℝ} {ν : ℝ} (hν : 0 ≤ ν)
    (ha : IsAdmissibleWeights k a) (α : G.Ω 1 → ℂ)
    (hα : ∀ x, ‖α x‖ ≤ coerciveConst d / (2 * (G.spacing x) ^ 2))
    {r : Torus d (N₀ * L ^ k) → ℝ} (hr : IsAgmonWeight G r) {ε : ℝ} (hε0 : 0 ≤ ε)
    (hε1 : ε ≤ agmonRate d) {u f : G.Ω 1 → ℂ} (hu : dirichletOperator G a ν α *ᵥ u = f) :
    (1 / 2) * cEnergy (agmonField G ε r u) + (poincareConst d / 4) * cwsq G (agmonField G ε r u) ≤
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
  have core_p := weighted_core G hd hν ha hr hε0 hε12 hpz
  have core_q := weighted_core G hd hν ha hr hε0 hε12 hqz
  have hκ := kappa_le hd hε0 hε1
  set v := agmonField G ε r u with hv
  have hvre : (fun x => (v x).re) = fun x => w x * p x := by
    funext x; exact Complex.re_ofReal_mul _ _
  have hvim : (fun x => (v x).im) = fun x => w x * q x := by
    funext x; exact Complex.im_ofReal_mul _ _
  have hE : cEnergy v = latticeEnergy (fun x => w x * p x) + latticeEnergy (fun x => w x * q x) := by
    rw [cEnergy_eq, hvre, hvim]
  have hS : cwsq G v = wsq G (fun x => w x * p x) + wsq G (fun x => w x * q x) := by
    rw [cwsq_eq, hvre, hvim]
  -- the pointwise identity coming from the equation
  set Ap := fullMatrix G a ν *ᵥ p with hAp
  set Aq := fullMatrix G a ν *ᵥ q with hAq
  have hpt : ∀ x : Torus d (N₀ * L ^ k), w x ^ 2 * (star (ut x) * ft x).re =
      w x ^ 2 * p x * Ap x + w x ^ 2 * q x * Aq x + w x ^ 2 * (αt x).re * ‖ut x‖ ^ 2 := by
    intro x
    by_cases hx : x ∈ G.Ω 1
    · have heq := dirichlet_eq G hu ⟨x, hx⟩
      have h1 : ft x = ((fullMatrix G a ν).map (algebraMap ℝ ℂ) *ᵥ ut) x + αt x * ut x := by
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
      (fun x => Real.exp (ε * r x) ^ 2 * p x) ⬝ᵥ fullMatrix G a ν *ᵥ p := rfl
  have hRq : (∑ x, w x ^ 2 * q x * Aq x) =
      (fun x => Real.exp (ε * r x) ^ 2 * q x) ⬝ᵥ fullMatrix G a ν *ᵥ q := rfl
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
  have hcomb : (1 / 2) * cEnergy v + (poincareConst d - (4 * d * ε ^ 2 + (Real.exp (ε * (2 * d)) - 1) ^ 2)) *
      cwsq G v ≤ (∑ x, w x ^ 2 * p x * Ap x) + (∑ x, w x ^ 2 * q x * Aq x) := by
    rw [hE, hS, hRp, hRq]
    nlinarith [core_p, core_q]
  have hS0 := cwsq_nonneg G v
  have hE0 := cEnergy_nonneg v
  nlinarith [hcomb, hTsum, hpot, hsrc, hκ, mul_nonneg hS0 (sub_nonneg.2 hκ)]


/-! ### Consequences -/

section Consequences

variable (G : GeneratingSet d L N₀ k ϱ)

/-- `‖ℓ⁻¹ w u‖² ≤ 4 c⁻² ‖ℓ w f‖²`. -/
theorem agmon_wsq_le (hd : 0 < d) {a : ℕ → ℝ} {ν : ℝ} (hν : 0 ≤ ν) (ha : IsAdmissibleWeights k a)
    (α : G.Ω 1 → ℂ) (hα : ∀ x, ‖α x‖ ≤ coerciveConst d / (2 * (G.spacing x) ^ 2))
    {r : Torus d (N₀ * L ^ k) → ℝ} (hr : IsAgmonWeight G r) {ε : ℝ} (hε0 : 0 ≤ ε)
    (hε1 : ε ≤ agmonRate d) {u f : G.Ω 1 → ℂ} (hu : dirichletOperator G a ν α *ᵥ u = f) :
    cwsq G (agmonField G ε r u) ≤ 4 / poincareConst d ^ 2 * agmonSource G ε r f := by
  have h := agmon_energy G hd hν ha α hα hr hε0 hε1 hu
  have hp0 := poincareConst_pos hd
  have hE := cEnergy_nonneg (agmonField G ε r u)
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
theorem agmon_cEnergy_le (hd : 0 < d) {a : ℕ → ℝ} {ν : ℝ} (hν : 0 ≤ ν)
    (ha : IsAdmissibleWeights k a) (α : G.Ω 1 → ℂ)
    (hα : ∀ x, ‖α x‖ ≤ coerciveConst d / (2 * (G.spacing x) ^ 2))
    {r : Torus d (N₀ * L ^ k) → ℝ} (hr : IsAgmonWeight G r) {ε : ℝ} (hε0 : 0 ≤ ε)
    (hε1 : ε ≤ agmonRate d) {u f : G.Ω 1 → ℂ} (hu : dirichletOperator G a ν α *ᵥ u = f) :
    cEnergy (agmonField G ε r u) ≤ 2 / poincareConst d * agmonSource G ε r f := by
  have h := agmon_energy G hd hν ha α hα hr hε0 hε1 hu
  have hp0 := poincareConst_pos hd
  have hS := cwsq_nonneg G (agmonField G ε r u)
  have : (1 / 2) * cEnergy (agmonField G ε r u) ≤ 1 / poincareConst d * agmonSource G ε r f := by
    nlinarith [mul_nonneg hp0.le hS]
  have e : 2 / poincareConst d * agmonSource G ε r f =
      2 * (1 / poincareConst d * agmonSource G ε r f) := by ring
  linarith

/-- Pointwise form of the weighted gradient bound:
`w(x)² |ũ(x + e_μ) - ũ(x)|² ≤ 2 |v(x + e_μ) - v(x)|² + 8 ε² ℓ(x + e_μ)⁻² |v(x + e_μ)|²`. -/
theorem agmon_grad_pointwise {r : Torus d (N₀ * L ^ k) → ℝ} (hr : IsAgmonWeight G r) {ε : ℝ}
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1 / 2) (u : G.Ω 1 → ℂ) {x : Torus d (N₀ * L ^ k)} (hx : x ∈ G.Ω 1)
    (μ : Fin d) :
    Real.exp (ε * r x) ^ 2 * ‖zeroExt (G.Ω 1) u (x + Pi.single μ 1) - zeroExt (G.Ω 1) u x‖ ^ 2 ≤
      2 * ‖agmonField G ε r u (x + Pi.single μ 1) - agmonField G ε r u x‖ ^ 2 +
        8 * ε ^ 2 * (invSqSpacing G (x + Pi.single μ 1) *
          ‖agmonField G ε r u (x + Pi.single μ 1)‖ ^ 2) := by
  set b := x + Pi.single μ 1 with hb
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
  · have hadj : Adj x b := ⟨μ, Or.inl rfl⟩
    have hbc := hr.bond x b hx hbm hadj
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

end Consequences

end Balaban.Multiscale
