/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Green.TranslationInvariant
public import Balaban.Green.CombesThomas
public import Balaban.Green.BallSums
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

/-!
# G-5(a), coarse part: `C_tr = (Δ_tr + a' L⁻² Q* Q)⁻¹`

On the coarse torus `Torus d m` of the unit lattice (`m = N₀`, any volume), with
`Δ_tr = a - a² Q G Q* = unconstrainedUnitOperator` (GREEN.md (1.8), the translation-invariant
operator of G-5) and the next-scale averaging `Q*Q = blockProjMatrix d m L M` (`m = L M`), put

`A = coarseOperator = Δ_tr + (a'/L²) Q*Q`,   `C_tr = A⁻¹`.

* `Balaban.Green.unconstrainedUnitOperator_decay`: `|Δ_tr(y, y')| ≤ c e^{-δ₀ dist(y, y')}`;
* `Balaban.Green.coarseOperator_form`: `A ≥ γ`, `γ = trGamma d L` (coercivity, from the landed
  `unconstrainedUnitOperator_lower` and `blockHamiltonian_coercive_real`);
* `Balaban.Green.coarseGreen_decay` (**G-5(a), second half**): `|C_tr(y, y')| ≤ (2/γ) e^{-δ dist}`
  with `δ = trRate d L`, via the landed Combes–Thomas estimate `Balaban.Green.combesThomas`
  (G-4).

Constants `trC0, trGamma, trRate` depend on `d, L` only; the bounds are uniform in `k ≥ 1`, the
volume `N₀ = L M`, `ν ∈ [0, 2]`, `a ∈ [1/2, 2]`, `a' ∈ [1/2, 2]`.
-/

@[expose] public section

namespace Balaban.Green

open Matrix Finset Balaban

/-! ### Definitions and constants -/

/-- The coarse operator `A = Δ_tr + (a'/L²) Q*Q` on the coarse torus (`m = L M`). -/
noncomputable def coarseOperator (d ℓ N m L M : ℕ) [NeZero ℓ] [NeZero m] (ν a a' : ℝ) :
    Matrix (Torus d m) (Torus d m) ℝ :=
  unconstrainedUnitOperator d ℓ N m ν a + (a' / (L : ℝ) ^ 2) • blockProjMatrix d m L M

/-- The entry-decay constant of `A`. -/
noncomputable def trC0 (d L : ℕ) : ℝ :=
  2 + 4 * blockDecayConst d L + 2 / (L : ℝ) ^ 2 * Real.exp (blockDecayRate d * (d * L))

/-- The coercivity constant of `A`. -/
noncomputable def trGamma (d L : ℕ) : ℝ :=
  min (1 / (8 * (d : ℝ) + 5)) (1 / (2 * (L : ℝ) ^ 2)) * min (2 / ((d : ℝ) * (L : ℝ) ^ 2)) 1

/-- The decay rate of `C_tr`. -/
noncomputable def trRate (d L : ℕ) : ℝ :=
  ctRate (trC0 d L) (blockDecayRate d) (trGamma d L) (ballConst d (blockDecayRate d / 4))

theorem trGamma_pos {d L : ℕ} [NeZero L] (hd : 0 < d) : 0 < trGamma d L := by
  have hL : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  unfold trGamma
  exact mul_pos (lt_min (by positivity) (by positivity)) (lt_min (by positivity) one_pos)

theorem trC0_nonneg {d L : ℕ} [NeZero L] (hd : 0 < d) : 0 ≤ trC0 d L := by
  unfold trC0
  have := blockDecayConst_pos (L := L) hd
  positivity

theorem trRate_pos {d L : ℕ} [NeZero L] (hd : 0 < d) : 0 < trRate d L := by
  unfold trRate
  have hr := blockDecayRate_pos hd
  have hq : 0 < Real.exp (-(blockDecayRate d / 4)) ∧ Real.exp (-(blockDecayRate d / 4)) < 1 :=
    exp_one_sub_pos (by positivity)
  refine ctRate_pos (trC0_nonneg hd) hr (trGamma_pos hd) ?_
  unfold ballConst
  have h1 : 0 < 1 - Real.exp (-(blockDecayRate d / 4)) := by linarith [hq.2]
  have h2 : 0 < 1 + Real.exp (-(blockDecayRate d / 4)) := by linarith [hq.1]
  positivity

/-! ### Entry decay -/

section Entries

variable {d ℓ N m L M : ℕ} [NeZero ℓ] [NeZero m]

/-- Entry decay of `Δ_tr`. -/
theorem unconstrainedUnitOperator_decay {N₀ k : ℕ} [NeZero N₀] [NeZero L] (hd : 0 < d)
    (hk : 1 ≤ k) {ν a : ℝ} (hν : 0 ≤ ν) (ha1 : 1 / 2 ≤ a) (ha2 : a ≤ 2) (y y' : Torus d N₀) :
    |unconstrainedUnitOperator d (N₀ * L ^ k) (L ^ k) N₀ ν a y y'| ≤
      (2 + 4 * blockDecayConst d L) * Real.exp (-(blockDecayRate d * torusDist d N₀ y y')) := by
  have hK := blockGreenKernel_decay (L := L) hd hk hν ha1 ha2 y y'
  have hC := blockDecayConst_pos (L := L) hd
  have hE : 0 < Real.exp (-(blockDecayRate d * torusDist d N₀ y y')) := Real.exp_pos _
  have e : unconstrainedUnitOperator d (N₀ * L ^ k) (L ^ k) N₀ ν a y y' =
      (if y = y' then a else 0) - a ^ 2 *
        blockGreenKernel d (N₀ * L ^ k) (L ^ k) N₀ ν a y y' := by
    simp only [unconstrainedUnitOperator, blockGreenKernel, Matrix.sub_apply, Matrix.smul_apply,
      Matrix.one_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
  rw [e]
  have ha0 : 0 ≤ a := by linarith
  have hKa : a ^ 2 * |blockGreenKernel d (N₀ * L ^ k) (L ^ k) N₀ ν a y y'| ≤
      4 * (blockDecayConst d L * Real.exp (-(blockDecayRate d * torusDist d N₀ y y'))) := by
    have : a ^ 2 ≤ 4 := by nlinarith
    calc _ ≤ 4 * |blockGreenKernel d (N₀ * L ^ k) (L ^ k) N₀ ν a y y'| :=
          mul_le_mul this le_rfl (abs_nonneg _) (by norm_num)
      _ ≤ _ := mul_le_mul_of_nonneg_left hK (by norm_num)
  by_cases h : y = y'
  · subst h
    rw [torusDist_self_eq_zero] at *
    simp only [mul_zero, neg_zero, Real.exp_zero, mul_one, ite_true] at *
    calc _ ≤ |a| + |a ^ 2 * blockGreenKernel d (N₀ * L ^ k) (L ^ k) N₀ ν a y y| := abs_sub _ _
      _ ≤ 2 + 4 * blockDecayConst d L := by
        rw [abs_mul, abs_of_nonneg ha0, abs_of_nonneg (sq_nonneg a)]
        linarith
  · simp only [h, ite_false, zero_sub, abs_neg]
    rw [abs_mul, abs_of_nonneg (sq_nonneg a)]
    nlinarith

/-- Entry decay of the next-scale averaging term. -/
theorem blockProj_entry_decay [NeZero M] [NeZero L] (hd : 0 < d) (hm : m = L * M) {a' : ℝ} (ha'0 : 0 ≤ a')
    (ha' : a' ≤ 2) (y y' : Torus d m) :
    |(a' / (L : ℝ) ^ 2) * blockProjMatrix d m L M y y'| ≤
      2 / (L : ℝ) ^ 2 * Real.exp (blockDecayRate d * (d * L)) *
        Real.exp (-(blockDecayRate d * torusDist d m y y')) := by
  have hL : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne L)
  have hLd : (1 : ℝ) ≤ (L : ℝ) ^ d := one_le_pow₀ hL1
  have hr : 0 ≤ blockDecayRate d := (blockDecayRate_pos hd).le
  by_cases h : blockMap L M y = blockMap L M y'
  · have hdist := torusDist_le_of_blockMap_eq hm (Nat.pos_of_ne_zero (NeZero.ne L)) h
    rw [show blockProjMatrix d m L M y y' = ((L : ℝ) ^ d)⁻¹ by simp [blockProjMatrix, h]]
    have h1 : ((L : ℝ) ^ d)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hLd
    have h2 : 1 ≤ Real.exp (blockDecayRate d * (d * L)) *
        Real.exp (-(blockDecayRate d * torusDist d m y y')) := by
      rw [← Real.exp_add]
      apply Real.one_le_exp
      nlinarith [mul_le_mul_of_nonneg_left hdist hr]
    rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ a' / (L : ℝ) ^ 2),
      abs_of_nonneg (by positivity : 0 ≤ ((L : ℝ) ^ d)⁻¹)]
    have h3 : a' / (L : ℝ) ^ 2 ≤ 2 / (L : ℝ) ^ 2 := by gcongr
    calc a' / (L : ℝ) ^ 2 * ((L : ℝ) ^ d)⁻¹ ≤ 2 / (L : ℝ) ^ 2 * 1 :=
          mul_le_mul h3 h1 (by positivity) (by positivity)
      _ ≤ 2 / (L : ℝ) ^ 2 * (Real.exp (blockDecayRate d * (d * L)) *
          Real.exp (-(blockDecayRate d * torusDist d m y y'))) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = _ := by ring
  · simp only [blockProjMatrix, h, ite_false, mul_zero, abs_zero]
    positivity

end Entries

/-! ### Coercivity -/

section Coercive

variable {d ℓ N m L M : ℕ} [NeZero ℓ] [NeZero m]

/-- A real quadratic-form lower bound gives coercivity of the complexification. -/
theorem isCoercive_map_of_real {ι : Type*} [Fintype ι] [DecidableEq ι] (B : Matrix ι ι ℝ) {γ : ℝ}
    (h : ∀ φ : ι → ℝ, γ * ∑ i, φ i ^ 2 ≤ φ ⬝ᵥ B *ᵥ φ) :
    IsCoercive (B.map (algebraMap ℝ ℂ)) γ := by
  intro v
  rw [reQuad_map_ofReal, sqNorm_eq_re_im, mul_add]
  have h1 := h fun i => (v i).re
  have h2 := h fun i => (v i).im
  linarith

theorem a_div_ge {d : ℕ} {ν a : ℝ} (hν : 0 ≤ ν) (hν2 : ν ≤ 2) (ha : 1 / 2 ≤ a) :
    1 / (8 * (d : ℝ) + 5) ≤ a / (a + 4 * d + ν) := by
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith

theorem blockProj_quadratic [NeZero M] (hm : m = L * M) (hL : 0 < L) (φ : Torus d m → ℝ) :
    φ ⬝ᵥ blockProjMatrix d m L M *ᵥ φ = ∑ x, (blockProjection L M φ x) ^ 2 := by
  simp only [dotProduct, blockProjMatrix_mulVec]
  exact sum_mul_blockProjection hm hL φ

/-- **Coercivity of `A = Δ_tr + (a'/L²) Q*Q`**: `⟨φ, A φ⟩ ≥ γ ‖φ‖²`, `γ = trGamma d L`. -/
theorem coarseOperator_form [NeZero M] [NeZero L] (hd : 0 < d) (hℓ : ℓ = N * m) (hN : 0 < N)
    (hm : m = L * M) {ν a a' : ℝ} (hν0 : 0 ≤ ν) (hν2 : ν ≤ 2) (ha1 : 1 / 2 ≤ a)
    (ha'1 : 1 / 2 ≤ a') (φ : Torus d m → ℝ) :
    trGamma d L * ∑ x, φ x ^ 2 ≤ φ ⬝ᵥ coarseOperator d ℓ N m L M ν a a' *ᵥ φ := by
  have hL : 0 < L := Nat.pos_of_ne_zero (NeZero.ne L)
  have hLr : (0 : ℝ) < L := by exact_mod_cast hL
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have ha0 : 0 < a := by linarith
  have hΔ := unconstrainedUnitOperator_lower hℓ hN hd hν0 ha0 φ
  have hE : 0 ≤ latticeEnergy φ := latticeEnergy_nonneg φ
  have hSum : 0 ≤ ∑ x, φ x ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hg := a_div_ge (d := d) hν0 hν2 ha1
  have hS := blockProj_quadratic hm hL φ
  have hSnn : 0 ≤ ∑ x, (blockProjection L M φ x) ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hcoer := blockHamiltonian_coercive_real hm hL hd 0 1 φ
  have hq := blockHamiltonian_quadratic hm hL 0 1 φ
  set c1 := min (1 / (8 * (d : ℝ) + 5)) (1 / (2 * (L : ℝ) ^ 2)) with hc1
  set c2 := min (2 / ((d : ℝ) * (L : ℝ) ^ 2)) 1 with hc2
  set S := ∑ x, (blockProjection L M φ x) ^ 2 with hSdef
  have hc1a : c1 ≤ 1 / (8 * (d : ℝ) + 5) := min_le_left _ _
  have hc1b : c1 ≤ 1 / (2 * (L : ℝ) ^ 2) := min_le_right _ _
  have hc10 : 0 ≤ c1 := le_min (by positivity) (by positivity)
  have hg0 : 0 ≤ a / (a + 4 * d + ν) := by positivity
  have h1 : c1 * latticeEnergy φ ≤ a / (a + 4 * d + ν) * (latticeEnergy φ + ν * ∑ x, φ x ^ 2) := by
    calc c1 * latticeEnergy φ ≤ a / (a + 4 * d + ν) * latticeEnergy φ :=
          mul_le_mul_of_nonneg_right (hc1a.trans hg) hE
      _ ≤ _ := mul_le_mul_of_nonneg_left (by nlinarith [mul_nonneg hν0 hSum]) hg0
  have h2 : c1 * S ≤ a' / (L : ℝ) ^ 2 * S := by
    refine mul_le_mul_of_nonneg_right (hc1b.trans ?_) hSnn
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [sq_nonneg (L : ℝ)]
  have h3 : c2 * ∑ x, φ x ^ 2 ≤ latticeEnergy φ + S := by
    rw [hq] at hcoer
    linarith
  have hform : φ ⬝ᵥ coarseOperator d ℓ N m L M ν a a' *ᵥ φ =
      φ ⬝ᵥ unconstrainedUnitOperator d ℓ N m ν a *ᵥ φ + a' / (L : ℝ) ^ 2 * S := by
    unfold coarseOperator
    rw [Matrix.add_mulVec, dotProduct_add, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul,
      blockProj_quadratic hm hL]
  rw [hform]
  have h4 : c1 * c2 * ∑ x, φ x ^ 2 ≤ c1 * (latticeEnergy φ + S) := by
    rw [mul_assoc]; exact mul_le_mul_of_nonneg_left h3 hc10
  unfold trGamma
  rw [← hc1, ← hc2]
  nlinarith

/-- The real inverse of a real matrix with unit complexification is the real part of the complex
inverse. -/
theorem map_inv_real {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℝ)
    (h : IsUnit (A.map (algebraMap ℝ ℂ))) :
    (A.map (algebraMap ℝ ℂ))⁻¹ = (A⁻¹).map (algebraMap ℝ ℂ) := by
  have hdet : IsUnit A.det := by
    rw [Matrix.isUnit_iff_isUnit_det] at h
    have e : (A.map (algebraMap ℝ ℂ)).det = algebraMap ℝ ℂ A.det := by
      rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    rw [e] at h
    rw [isUnit_iff_ne_zero] at h ⊢
    intro h0
    exact h (by rw [h0, map_zero])
  apply Matrix.inv_eq_right_inv
  rw [← Matrix.map_mul, Matrix.mul_nonsing_inv _ hdet, Matrix.map_one _ (map_zero _) (map_one _)]

end Coercive

/-! ### Decay of `C_tr` -/

section Main

variable {d L N₀ k M : ℕ} [NeZero N₀] [NeZero L] [NeZero M]

/-- Entry decay of `A = Δ_tr + (a'/L²) Q*Q`. -/
theorem coarseOperator_entry (hd : 0 < d) (hk : 1 ≤ k) (hm : N₀ = L * M) {ν a a' : ℝ}
    (hν : 0 ≤ ν) (ha1 : 1 / 2 ≤ a) (ha2 : a ≤ 2) (ha'1 : 1 / 2 ≤ a') (ha'2 : a' ≤ 2)
    (y y' : Torus d N₀) :
    |coarseOperator d (N₀ * L ^ k) (L ^ k) N₀ L M ν a a' y y'| ≤
      trC0 d L * Real.exp (-(blockDecayRate d * torusDist d N₀ y y')) := by
  unfold coarseOperator
  rw [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  refine (abs_add_le _ _).trans ?_
  have h1 := unconstrainedUnitOperator_decay (L := L) hd hk hν ha1 ha2 y y'
  have h2 := blockProj_entry_decay (L := L) (M := M) hd hm (a' := a') (by linarith) ha'2 y y'
  unfold trC0
  nlinarith [h1, h2]

/-- **G-5(a), second half.**  `C_tr = (Δ_tr + (a'/L²) Q*Q)⁻¹` has exponentially decaying entries,
`|C_tr(y, y')| ≤ (2/γ) e^{-δ dist(y, y')}`, with `γ = trGamma d L`, `δ = trRate d L`, uniformly
in `k ≥ 1`, the volume `N₀ = L M`, `ν ∈ [0, 2]`, `a, a' ∈ [1/2, 2]`. -/
theorem coarseGreen_decay (hd : 0 < d) (hk : 1 ≤ k) (hm : N₀ = L * M) {ν a a' : ℝ}
    (hν0 : 0 ≤ ν) (hν2 : ν ≤ 2) (ha1 : 1 / 2 ≤ a) (ha2 : a ≤ 2) (ha'1 : 1 / 2 ≤ a')
    (ha'2 : a' ≤ 2) (y y' : Torus d N₀) :
    |(coarseOperator d (N₀ * L ^ k) (L ^ k) N₀ L M ν a a')⁻¹ y y'| ≤
      2 * (trGamma d L)⁻¹ * Real.exp (-(trRate d L * torusDist d N₀ y y')) := by
  have hN : 0 < L ^ k := Nat.pos_of_ne_zero (pow_ne_zero _ (NeZero.ne L))
  have hℓ : N₀ * L ^ k = L ^ k * N₀ := mul_comm _ _
  set A := coarseOperator d (N₀ * L ^ k) (L ^ k) N₀ L M ν a a' with hAdef
  have hγ := trGamma_pos (L := L) hd
  have hδ := blockDecayRate_pos hd
  have hcoer : IsCoercive (A.map (algebraMap ℝ ℂ)) (trGamma d L) :=
    isCoercive_map_of_real A fun φ =>
      coarseOperator_form hd hℓ hN hm hν0 hν2 ha1 ha'1 φ
  set Ac : Matrix (L1Torus d N₀) (L1Torus d N₀) ℂ := A.map (algebraMap ℝ ℂ) with hAc
  have hA : ∀ x y : L1Torus d N₀, ‖Ac x y‖ ≤
      trC0 d L * Real.exp (-blockDecayRate d * dist x y) := by
    intro x y
    have := coarseOperator_entry (L := L) (M := M) hd hk hm hν0 ha1 ha2 ha'1 ha'2 x y
    have e : ‖Ac x y‖ = |A x y| := by
      show ‖algebraMap ℝ ℂ (A x y)‖ = |A x y|
      simp
    rw [e, dist_L1Torus, neg_mul]
    exact this
  have hκ : 0 ≤ ballConst d (blockDecayRate d / 4) := by
    unfold ballConst
    have hq : 0 < Real.exp (-(blockDecayRate d / 4)) ∧ Real.exp (-(blockDecayRate d / 4)) < 1 :=
      exp_one_sub_pos (by positivity)
    have h1 : 0 < 1 - Real.exp (-(blockDecayRate d / 4)) := by linarith [hq.2]
    have h2 : 0 < 1 + Real.exp (-(blockDecayRate d / 4)) := by linarith [hq.1]
    positivity
  have hK : ∀ x : L1Torus d N₀, ∑ y, Real.exp (-(blockDecayRate d / 4) * dist x y) ≤
      ballConst d (blockDecayRate d / 4) := fun x => ballSum_L1Torus d N₀ (by positivity) x
  obtain ⟨hU, hb⟩ := combesThomas (trC0_nonneg hd) hδ hγ hκ hA hK hcoer (t := 0) le_rfl
  simp only [Complex.ofReal_zero, zero_smul, add_zero] at hU hb
  have hinv : Ac⁻¹ = A⁻¹.map (algebraMap ℝ ℂ) := map_inv_real A hU
  have e2 : ‖Ac⁻¹ y y'‖ = |A⁻¹ y y'| := by
    rw [hinv]
    show ‖algebraMap ℝ ℂ (A⁻¹ y y')‖ = |A⁻¹ y y'|
    simp
  have := hb y y'
  rw [e2, neg_mul] at this
  exact this

end Main

end Balaban.Green
