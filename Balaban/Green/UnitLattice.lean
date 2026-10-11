/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Green.Coercivity
public import Balaban.Green.SchurVariational
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr

/-!
# The unconstrained unit-lattice operator and its coercivity (single scale)

Item 3 of brief W2b; GREEN.md Lemma 4.2 and the proof of G-1(b) (§4.1), single-scale,
small-field case, `α = 0`.

**This is the unconstrained operator** `Δ^{(k)}_unc = a - a² Q (-Δ^η + ν + a Q* Q)⁻¹ Q*`
(GREEN.md (1.8)), the Schur complement; it is *not* P4's constrained `Δ^{(k)}` (GREEN review F-02).

Conventions: fields on `Torus d ℓ` (fine, `ℓ = N * m`) and `Torus d m` (coarse); `latticeLaplacian`
and `latticeEnergy` are for unit spacing. The fine spacing `η = 1/N` of GREEN.md is restored by the
factor `N²`: `fineHamiltonian = N² (-Δ_unit) + ν + a P`.

* `blockSum_shift_sq`, `latticeEnergy_orthoBlock_le`, `sum_sq_orthoBlock_le`: Lemma 4.2,
  `E_coarse(Qo φ) ≤ N² E(φ)`, `‖Qo φ‖ ≤ ‖φ‖` for `Qo = orthoBlockMatrix` (`Qo Qoᵀ = 1`, `Qoᵀ Qo = P`);
* `unitLattice_lower`: unit-spacing form of the bound with `blockSpinOperator`;
* `unconstrainedUnitOperator` (definition), `unconstrainedUnitOperator_eq`
  (`= N² • blockSpinOperator (-Δ_unit + ν/N²) Qo (a/N²)`);
* `unconstrainedUnitOperator_lower` (**G-1(b)**): for `ν ≥ 0`, `a > 0`, `d > 0`,
  `a / (a + 4d + ν) · (E(ψ) + ν ‖ψ‖²) ≤ ⟨ψ, Δ_unc ψ⟩`, and `unconstrained_gamma_ge`: for `a ≥ 1/2`,
  `ν ≤ 1` the constant is `≥ 1/(8d + 3)` (GREEN.md states `1/(2(8d+5))`);
* `unconstrainedUnitOperator_le`: `⟨ψ, Δ_unc ψ⟩ ≤ a ‖ψ‖²`.
-/

@[expose] public section

namespace Balaban

open Matrix Finset

section Shift

variable {d ℓ N m : ℕ} [NeZero ℓ] [NeZero m]

omit [NeZero m] in
theorem blockCoord_add_natCast (hℓ : ℓ = N * m) (hN : 0 < N) (a : ZMod ℓ) :
    blockCoord N m (a + (N : ZMod ℓ)) = blockCoord N m a + 1 := by
  have h1 : a + (N : ZMod ℓ) = ((a.val + N : ℕ) : ZMod ℓ) := by
    push_cast; rw [ZMod.natCast_zmod_val]
  rw [h1, blockCoord, ZMod.val_natCast, blockCoord]
  generalize a.val = v
  rw [hℓ, Nat.mod_mul_right_div_self, Nat.add_div_right _ hN]
  rw [ZMod.natCast_mod]
  push_cast
  rfl

omit [NeZero m] in
theorem blockMap_add_shift (hℓ : ℓ = N * m) (hN : 0 < N) (μ : Fin d) (x : Torus d ℓ) :
    blockMap N m (x + Pi.single μ (N : ZMod ℓ)) = blockMap N m x + Pi.single μ 1 := by
  funext i
  by_cases h : i = μ
  · subst h
    simp [blockMap_apply, blockCoord_add_natCast hℓ hN]
  · simp [blockMap_apply, h]

omit [NeZero m] in
omit [NeZero ℓ] [NeZero m] in
theorem N_nsmul_single (μ : Fin d) (k : ℕ) :
    k • (Pi.single μ (1 : ZMod ℓ) : Torus d ℓ) = Pi.single μ (k : ZMod ℓ) := by
  funext i
  by_cases h : i = μ
  · subst h; simp
  · simp [h]

omit [NeZero m] in
/-- Shifting the block index by `e_μ` shifts the fibre by `N e_μ`. -/
theorem sum_fibre_shift (hℓ : ℓ = N * m) (hN : 0 < N) (μ : Fin d) (y : Torus d m)
    (g : Torus d ℓ → ℝ) :
    ∑ x' ∈ blockFibre N m (y + Pi.single μ 1), g x' =
      ∑ x ∈ blockFibre N m y, g (x + Pi.single μ (N : ZMod ℓ)) := by
  refine Finset.sum_nbij' (fun x' => x' - Pi.single μ (N : ZMod ℓ))
    (fun x => x + Pi.single μ (N : ZMod ℓ)) ?_ ?_ ?_ ?_ ?_
  · intro x' hx'
    rw [mem_blockFibre] at hx' ⊢
    have := blockMap_add_shift (m := m) hℓ hN μ (x' - Pi.single μ (N : ZMod ℓ))
    rw [sub_add_cancel, hx'] at this
    exact (add_right_cancel this.symm)
  · intro x hx
    rw [mem_blockFibre] at hx ⊢
    rw [blockMap_add_shift hℓ hN, hx]
  · intro x' _; simp
  · intro x _; simp
  · intro x' _; simp

/-- The block sum `(S φ) y = ∑_{x ∈ block y} φ x` (equal to `N^d` times `blockAverage`). -/
noncomputable def blockSum (N m : ℕ) (φ : Torus d ℓ → ℝ) (y : Torus d m) : ℝ :=
  ∑ x ∈ blockFibre N m y, φ x

omit [NeZero ℓ] [NeZero m] in
theorem sq_telescope_le (g : Torus d ℓ → ℝ) (μ : Fin d) (x : Torus d ℓ) :
    (g (x + Pi.single μ (N : ZMod ℓ)) - g x) ^ 2 ≤
      N * ∑ k ∈ Finset.range N, (g (x + Pi.single μ (k : ZMod ℓ) + Pi.single μ 1) -
        g (x + Pi.single μ (k : ZMod ℓ))) ^ 2 := by
  have htel := Finset.sum_range_sub (fun k : ℕ => g (x + Pi.single μ (k : ZMod ℓ))) N
  have hstep : ∀ k : ℕ, x + Pi.single μ ((k + 1 : ℕ) : ZMod ℓ) =
      x + Pi.single μ (k : ZMod ℓ) + Pi.single μ 1 := fun k => by
    rw [add_assoc, ← Pi.single_add]; push_cast; rfl
  simp only [hstep, Nat.cast_zero, Pi.single_zero, add_zero] at htel
  rw [← htel]
  have := sq_sum_le_card_mul_sum_sq (s := Finset.range N)
    (f := fun k : ℕ => g (x + Pi.single μ (k : ZMod ℓ) + Pi.single μ 1) -
      g (x + Pi.single μ (k : ZMod ℓ)))
  simpa using this

/-- Gradient of block sums (GREEN.md Lemma 4.2, in the unnormalised form):
`∑_y (S φ (y + e_μ) - S φ y)² ≤ N^{d+2} ∑_x (φ(x + e_μ) - φ x)²`. -/
theorem blockSum_shift_sq (hℓ : ℓ = N * m) (hN : 0 < N) (μ : Fin d) (φ : Torus d ℓ → ℝ) :
    ∑ y : Torus d m, (blockSum N m φ (y + Pi.single μ 1) - blockSum N m φ y) ^ 2 ≤
      (N : ℝ) ^ (d + 2) * ∑ x, (φ (x + Pi.single μ 1) - φ x) ^ 2 := by
  set gap : Torus d ℓ → ℝ := fun z => (φ (z + Pi.single μ 1) - φ z) ^ 2 with hgap
  have hdiff : ∀ y, blockSum N m φ (y + Pi.single μ 1) - blockSum N m φ y =
      ∑ x ∈ blockFibre N m y, (φ (x + Pi.single μ (N : ZMod ℓ)) - φ x) := by
    intro y
    unfold blockSum
    rw [sum_fibre_shift hℓ hN, Finset.sum_sub_distrib]
  have hy : ∀ y : Torus d m, (blockSum N m φ (y + Pi.single μ 1) - blockSum N m φ y) ^ 2 ≤
      (N : ℝ) ^ d * ∑ x ∈ blockFibre N m y, ((N : ℝ) * ∑ k ∈ Finset.range N,
        gap (x + Pi.single μ (k : ZMod ℓ))) := by
    intro y
    rw [hdiff]
    have h1 := sq_sum_le_card_mul_sum_sq (s := blockFibre N m y)
      (f := fun x => φ (x + Pi.single μ (N : ZMod ℓ)) - φ x)
    rw [card_blockFibre hℓ] at h1
    refine h1.trans ?_
    simp only [Nat.cast_pow]
    gcongr with x _
    exact sq_telescope_le φ μ x
  set hh : Torus d ℓ → ℝ := fun x => (N : ℝ) * ∑ k ∈ Finset.range N,
    gap (x + Pi.single μ (k : ZMod ℓ)) with hhh
  have e1 : ∑ y : Torus d m, (N : ℝ) ^ d * ∑ x ∈ blockFibre N m y, hh x =
      (N : ℝ) ^ d * ∑ x : Torus d ℓ, hh x := by
    rw [← Finset.mul_sum]
    congr 1
    exact Finset.sum_fiberwise Finset.univ (blockMap N m) hh
  have e2 : ∑ x : Torus d ℓ, hh x = (N : ℝ) * ∑ k ∈ Finset.range N, ∑ x : Torus d ℓ, gap x := by
    simp only [hhh]
    rw [← Finset.mul_sum, Finset.sum_comm]
    congr 1
    refine Finset.sum_congr rfl fun k _ => sum_shift (Pi.single μ (k : ZMod ℓ)) gap
  have e3 : ∑ y : Torus d m, (blockSum N m φ (y + Pi.single μ 1) - blockSum N m φ y) ^ 2 ≤
      ∑ y : Torus d m, (N : ℝ) ^ d * ∑ x ∈ blockFibre N m y, hh x :=
    Finset.sum_le_sum fun y _ => hy y
  rw [e1, e2, Finset.sum_const, Finset.card_range, nsmul_eq_mul] at *
  calc _ ≤ _ := e3
    _ = _ := by simp only [hgap]; ring

end Shift

section Ortho

variable {d ℓ N m : ℕ} [NeZero ℓ] [NeZero m]

/-- The block averaging in the orthonormal normalisation:
`(Qo φ) y = N^{-d/2} ∑_{x ∈ block y} φ x`, so that `Qo Qoᵀ = 1` and `Qoᵀ Qo = P = Q* Q`. -/
noncomputable def orthoBlockMatrix (d ℓ N m : ℕ) [NeZero ℓ] [NeZero m] :
    Matrix (Torus d m) (Torus d ℓ) ℝ :=
  fun y x => if blockMap N m x = y then (Real.sqrt ((N : ℝ) ^ d))⁻¹ else 0

theorem orthoBlockMatrix_mulVec (φ : Torus d ℓ → ℝ) (y : Torus d m) :
    (orthoBlockMatrix d ℓ N m *ᵥ φ) y = (Real.sqrt ((N : ℝ) ^ d))⁻¹ * blockSum N m φ y := by
  simp only [Matrix.mulVec, dotProduct, orthoBlockMatrix, blockSum, ite_mul, zero_mul]
  rw [← Finset.sum_filter, ← Finset.mul_sum]
  congr 2

theorem orthoBlockMatrix_transpose_mul_self (hN : 0 < N) :
    (orthoBlockMatrix d ℓ N m)ᵀ * orthoBlockMatrix d ℓ N m = blockProjMatrix d ℓ N m := by
  ext x x'
  simp only [Matrix.mul_apply, Matrix.transpose_apply, orthoBlockMatrix, blockProjMatrix]
  have hs : (Real.sqrt ((N : ℝ) ^ d))⁻¹ * (Real.sqrt ((N : ℝ) ^ d))⁻¹ = ((N : ℝ) ^ d)⁻¹ := by
    rw [← mul_inv, Real.mul_self_sqrt (by positivity)]
  by_cases h : blockMap N m x = blockMap N m x'
  · have e : (if blockMap N m x = blockMap N m x' then ((N : ℝ) ^ d)⁻¹ else 0) = ((N : ℝ) ^ d)⁻¹ := by
      simp [h]
    rw [e, Finset.sum_eq_single (blockMap N m x)]
    · simp [h, hs]
    · intro y _ hy; simp [Ne.symm hy]
    · simp
  · have e : (if blockMap N m x = blockMap N m x' then ((N : ℝ) ^ d)⁻¹ else 0) = 0 := by
      simp [h]
    rw [e]
    refine Finset.sum_eq_zero fun y _ => ?_
    by_cases hx : blockMap N m x = y
    · have : ¬ blockMap N m x' = y := fun e => h (hx.trans e.symm)
      simp [this]
    · simp [hx]

theorem sum_sq_orthoBlock_le (hℓ : ℓ = N * m) (hN : 0 < N) (φ : Torus d ℓ → ℝ) :
    ∑ y, ((orthoBlockMatrix d ℓ N m *ᵥ φ) y) ^ 2 ≤ ∑ x, φ x ^ 2 := by
  have hNd : (0 : ℝ) < (N : ℝ) ^ d := by positivity
  have hs : ((Real.sqrt ((N : ℝ) ^ d))⁻¹) ^ 2 = ((N : ℝ) ^ d)⁻¹ := by
    rw [inv_pow, Real.sq_sqrt hNd.le]
  have hy : ∀ y : Torus d m, ((orthoBlockMatrix d ℓ N m *ᵥ φ) y) ^ 2 ≤
      ∑ x ∈ blockFibre N m y, φ x ^ 2 := by
    intro y
    rw [orthoBlockMatrix_mulVec, mul_pow, hs, blockSum]
    have := sq_sum_le_card_mul_sum_sq (s := blockFibre N m y) (f := φ)
    rw [card_blockFibre hℓ] at this
    simp only [Nat.cast_pow] at this
    calc ((N : ℝ) ^ d)⁻¹ * (∑ x ∈ blockFibre N m y, φ x) ^ 2
        ≤ ((N : ℝ) ^ d)⁻¹ * ((N : ℝ) ^ d * ∑ x ∈ blockFibre N m y, φ x ^ 2) := by gcongr
      _ = _ := by field_simp
  calc _ ≤ ∑ y : Torus d m, ∑ x ∈ blockFibre N m y, φ x ^ 2 := Finset.sum_le_sum fun y _ => hy y
    _ = _ := Finset.sum_fiberwise Finset.univ (blockMap N m) (fun x => φ x ^ 2)

theorem latticeEnergy_orthoBlock_le (hℓ : ℓ = N * m) (hN : 0 < N) (φ : Torus d ℓ → ℝ) :
    latticeEnergy (orthoBlockMatrix d ℓ N m *ᵥ φ) ≤ (N : ℝ) ^ 2 * latticeEnergy φ := by
  have hNd : (0 : ℝ) < (N : ℝ) ^ d := by positivity
  have hs : ((Real.sqrt ((N : ℝ) ^ d))⁻¹) ^ 2 = ((N : ℝ) ^ d)⁻¹ := by
    rw [inv_pow, Real.sq_sqrt hNd.le]
  unfold latticeEnergy
  rw [Finset.sum_comm, Finset.sum_comm (s := (Finset.univ : Finset (Torus d ℓ))), Finset.mul_sum]
  refine Finset.sum_le_sum fun μ _ => ?_
  have h := blockSum_shift_sq hℓ hN μ φ
  have e : ∑ y : Torus d m, ((orthoBlockMatrix d ℓ N m *ᵥ φ) (y + Pi.single μ 1) -
        (orthoBlockMatrix d ℓ N m *ᵥ φ) y) ^ 2 =
      ((N : ℝ) ^ d)⁻¹ * ∑ y : Torus d m, (blockSum N m φ (y + Pi.single μ 1) -
        blockSum N m φ y) ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [orthoBlockMatrix_mulVec, orthoBlockMatrix_mulVec, ← mul_sub, mul_pow, hs]
  rw [e]
  calc ((N : ℝ) ^ d)⁻¹ * _ ≤ ((N : ℝ) ^ d)⁻¹ * ((N : ℝ) ^ (d + 2) * ∑ x, (φ (x + Pi.single μ 1) - φ x) ^ 2) := by
        gcongr
    _ = _ := by field_simp; ring

end Ortho




section Lower

variable {d ℓ N m : ℕ} [NeZero ℓ] [NeZero m]

omit [NeZero m] in
theorem blockProjMatrix_isHermitian : (blockProjMatrix d ℓ N m).IsHermitian := by
  ext x x'
  simp only [Matrix.conjTranspose_apply, blockProjMatrix, star_trivial]
  simp only [eq_comm]

omit [NeZero m] in
theorem blockHamiltonian_isHermitian (ν a : ℝ) : (blockHamiltonian d ℓ N m ν a).IsHermitian := by
  unfold blockHamiltonian
  refine (latticeLaplacian_isHermitian ν).add ?_
  have h := (blockProjMatrix_isHermitian (d := d) (ℓ := ℓ) (N := N) (m := m))
  unfold Matrix.IsHermitian at h ⊢
  rw [Matrix.conjTranspose_smul, h, star_trivial]

theorem blockHamiltonian_posDef (hℓ : ℓ = N * m) (hN : 0 < N) (hd : 0 < d) {ν a : ℝ}
    (hν : 0 ≤ ν) (ha : 0 < a) : (blockHamiltonian d ℓ N m ν a).PosDef := by
  refine Matrix.posDef_iff_dotProduct_mulVec.mpr ⟨blockHamiltonian_isHermitian ν a, ?_⟩
  intro φ hφ
  obtain ⟨x₀, hx₀⟩ := Function.ne_iff.mp hφ
  have hpos : 0 < ∑ x, φ x ^ 2 :=
    lt_of_lt_of_le (by have : φ x₀ ≠ 0 := hx₀; positivity) (Finset.single_le_sum
      (f := fun x => φ x ^ 2) (fun x _ => sq_nonneg _) (Finset.mem_univ x₀))
  have hc : 0 < min (2 / ((d : ℝ) * (N : ℝ) ^ 2)) a + ν := by
    have : 0 < min (2 / ((d : ℝ) * (N : ℝ) ^ 2)) a := lt_min (by positivity) ha
    linarith
  have := blockHamiltonian_coercive_real hℓ hN hd ν a φ
  simp only [star_trivial]
  exact lt_of_lt_of_le (mul_pos hc hpos) this

end Lower

section Coarse

variable {d n : ℕ} [NeZero n]

theorem sq_add_le_weighted {w₁ w₂ : ℝ} (h₁ : 0 < w₁) (h₂ : 0 < w₂) (p q : ℝ) :
    (p + q) ^ 2 ≤ (w₁ + w₂) * (p ^ 2 / w₁ + q ^ 2 / w₂) := by
  have key : 0 ≤ (w₂ * p - w₁ * q) ^ 2 := sq_nonneg _
  have e : (w₁ + w₂) * (p ^ 2 / w₁ + q ^ 2 / w₂) - (p + q) ^ 2 =
      (w₂ * p - w₁ * q) ^ 2 / (w₁ * w₂) := by
    field_simp
    ring
  have : 0 ≤ (w₂ * p - w₁ * q) ^ 2 / (w₁ * w₂) := div_nonneg key (by positivity)
  linarith

theorem latticeEnergy_le_four_mul (u : Torus d n → ℝ) :
    latticeEnergy u ≤ 4 * d * ∑ x, u x ^ 2 := by
  unfold latticeEnergy
  rw [Finset.sum_comm]
  have : ∀ μ : Fin d, ∑ x : Torus d n, (u (x + Pi.single μ 1) - u x) ^ 2 ≤ 4 * ∑ x, u x ^ 2 := by
    intro μ
    have h1 : ∑ x : Torus d n, (u (x + Pi.single μ 1) - u x) ^ 2 ≤
        ∑ x : Torus d n, (2 * u (x + Pi.single μ 1) ^ 2 + 2 * u x ^ 2) :=
      Finset.sum_le_sum fun x _ => by nlinarith [sq_nonneg (u (x + Pi.single μ 1) + u x)]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
      sum_shift (Pi.single μ 1) (fun x => u x ^ 2)] at h1
    linarith
  calc _ ≤ ∑ _μ : Fin d, 4 * ∑ x, u x ^ 2 := Finset.sum_le_sum fun μ _ => this μ
    _ = _ := by simp; ring

theorem latticeEnergy_add_le {w₁ w₂ : ℝ} (h₁ : 0 < w₁) (h₂ : 0 < w₂) (χ δ : Torus d n → ℝ) :
    latticeEnergy (χ + δ) ≤
      (w₁ + w₂) * (latticeEnergy χ / w₁ + latticeEnergy δ / w₂) := by
  unfold latticeEnergy
  simp only [Finset.sum_div, ← Finset.sum_add_distrib, Finset.mul_sum]
  refine Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun μ _ => ?_
  have := sq_add_le_weighted h₁ h₂ (χ (x + Pi.single μ 1) - χ x) (δ (x + Pi.single μ 1) - δ x)
  simpa [Pi.add_apply, add_sub_add_comm] using this

theorem sum_sq_add_le {w₁ w₂ : ℝ} (h₁ : 0 < w₁) (h₂ : 0 < w₂) (χ δ : Torus d n → ℝ) :
    ∑ x, (χ + δ) x ^ 2 ≤ (w₁ + w₂) * ((∑ x, χ x ^ 2) / w₁ + (∑ x, δ x ^ 2) / w₂) := by
  simp only [Finset.sum_div, ← Finset.sum_add_distrib, Finset.mul_sum]
  exact Finset.sum_le_sum fun x _ => sq_add_le_weighted h₁ h₂ (χ x) (δ x)

/-- The coarse quadratic form `T ψ = N^{-2} ∑ ... + ν' ‖ψ‖²` (the form of `(-Δ + ν)` of
GREEN.md after the rescaling by the block side `N`). -/
noncomputable def coarseForm (N : ℕ) (ν : ℝ) (u : Torus d n → ℝ) : ℝ :=
  latticeEnergy u / (N : ℝ) ^ 2 + ν * ∑ x, u x ^ 2

theorem coarseForm_add_le {N : ℕ} (hN : 0 < N) {ν w₁ w₂ : ℝ} (hν : 0 ≤ ν) (h₁ : 0 < w₁)
    (h₂ : 0 < w₂) (χ δ : Torus d n → ℝ) :
    coarseForm N ν (χ + δ) ≤ (w₁ + w₂) * (coarseForm N ν χ / w₁ + coarseForm N ν δ / w₂) := by
  have hN2 : (0 : ℝ) < (N : ℝ) ^ 2 := by positivity
  have a1 := latticeEnergy_add_le h₁ h₂ χ δ
  have a2 := sum_sq_add_le h₁ h₂ χ δ
  unfold coarseForm
  have a1' := div_le_div_of_nonneg_right a1 hN2.le
  have a2' := mul_le_mul_of_nonneg_left a2 hν
  have e : (w₁ + w₂) * ((latticeEnergy χ / (N : ℝ) ^ 2 + ν * ∑ x, χ x ^ 2) / w₁ +
        (latticeEnergy δ / (N : ℝ) ^ 2 + ν * ∑ x, δ x ^ 2) / w₂) =
      (w₁ + w₂) * (latticeEnergy χ / w₁ + latticeEnergy δ / w₂) / (N : ℝ) ^ 2 +
        ν * ((w₁ + w₂) * ((∑ x, χ x ^ 2) / w₁ + (∑ x, δ x ^ 2) / w₂)) := by
    field_simp
    ring
  rw [e]
  linarith

theorem coarseForm_le {N : ℕ} (hN : 0 < N) {ν : ℝ} (u : Torus d n → ℝ) :
    coarseForm N ν u ≤ (4 * d / (N : ℝ) ^ 2 + ν) * ∑ x, u x ^ 2 := by
  have hN2 : (0 : ℝ) < (N : ℝ) ^ 2 := by positivity
  unfold coarseForm
  have h := div_le_div_of_nonneg_right (latticeEnergy_le_four_mul u) hN2.le
  have : 4 * (d : ℝ) * (∑ x, u x ^ 2) / (N : ℝ) ^ 2 = 4 * d / (N : ℝ) ^ 2 * ∑ x, u x ^ 2 := by
    ring
  nlinarith

/-- The coarse minimisation: for `ν ≥ 0`, `a > 0`,
`a / (a + λ) · T ψ ≤ a ‖ψ - χ‖² + T χ` with `λ = 4 d / N² + ν`, for every `χ`. -/
theorem coarse_lower {N : ℕ} (hN : 0 < N) (hd : 0 < d) {ν a : ℝ} (hν : 0 ≤ ν) (ha : 0 < a)
    (ψ χ : Torus d n → ℝ) :
    a / (a + (4 * d / (N : ℝ) ^ 2 + ν)) * coarseForm N ν ψ ≤
      a * ∑ x, (ψ x - χ x) ^ 2 + coarseForm N ν χ := by
  have hN2 : (0 : ℝ) < (N : ℝ) ^ 2 := by positivity
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  set lam : ℝ := 4 * d / (N : ℝ) ^ 2 + ν with hlam
  have hl : 0 < lam := by positivity
  have hψ : ψ = χ + (ψ - χ) := by abel
  have h1 := coarseForm_add_le hN hν ha hl χ (ψ - χ)
  rw [← hψ] at h1
  have h2 := coarseForm_le hN (ν := ν) (ψ - χ)
  have h3 : coarseForm N ν (ψ - χ) / lam ≤ ∑ x, (ψ x - χ x) ^ 2 := by
    rw [div_le_iff₀ hl]
    have h2' : coarseForm N ν (ψ - χ) ≤ lam * ∑ x, (ψ x - χ x) ^ 2 := h2
    linarith
  have h4 : coarseForm N ν ψ ≤ (a + lam) * (coarseForm N ν χ / a + ∑ x, (ψ x - χ x) ^ 2) := by
    refine h1.trans ?_
    gcongr
  have hal : 0 < a + lam := by positivity
  calc a / (a + lam) * coarseForm N ν ψ
      ≤ a / (a + lam) * ((a + lam) * (coarseForm N ν χ / a + ∑ x, (ψ x - χ x) ^ 2)) := by
        gcongr
    _ = _ := by field_simp; ring

end Coarse

section Main

variable {d ℓ N m : ℕ} [NeZero ℓ] [NeZero m]

theorem blockSpinPrecision_ortho (hN : 0 < N) (ν a : ℝ) :
    blockSpinPrecision (latticeLaplacian d ℓ ν) (orthoBlockMatrix d ℓ N m) a =
      blockHamiltonian d ℓ N m ν a := by
  unfold blockSpinPrecision blockHamiltonian
  rw [orthoBlockMatrix_transpose_mul_self hN]

/-- **Lower bound for the unit-lattice operator (single scale, unit spacing).**
With `Δ' = blockSpinOperator (-Δ + ν') Qo a'` (the block-spin operator for the unit-spacing
Laplacian on the fine torus and the orthonormal block average `Qo`), `ν' ≥ 0`, `a' > 0`:
`a' / (a' + 4d/N² + ν') · (N⁻² E(ψ) + ν' ‖ψ‖²) ≤ ψᵀ Δ' ψ`. -/
theorem unitLattice_lower (hℓ : ℓ = N * m) (hN : 0 < N) (hd : 0 < d) {ν a : ℝ} (hν : 0 ≤ ν)
    (ha : 0 < a) (ψ : Torus d m → ℝ) :
    a / (a + (4 * d / (N : ℝ) ^ 2 + ν)) * coarseForm N ν ψ ≤
      ψ ⬝ᵥ blockSpinOperator (latticeLaplacian d ℓ ν) (orthoBlockMatrix d ℓ N m) a *ᵥ ψ := by
  have hM : (blockSpinPrecision (latticeLaplacian d ℓ ν) (orthoBlockMatrix d ℓ N m) a).PosDef := by
    rw [blockSpinPrecision_ortho hN]
    exact blockHamiltonian_posDef hℓ hN hd hν ha
  rw [← blockSpinOperator_form_attained hM ψ]
  set φ := a • ((blockSpinPrecision (latticeLaplacian d ℓ ν) (orthoBlockMatrix d ℓ N m) a)⁻¹ *ᵥ
    ((orthoBlockMatrix d ℓ N m)ᵀ *ᵥ ψ)) with hφ
  set χ := orthoBlockMatrix d ℓ N m *ᵥ φ with hχ
  have h1 := coarse_lower hN hd hν ha ψ χ
  have h2 := latticeEnergy_orthoBlock_le hℓ hN φ
  have h3 := sum_sq_orthoBlock_le hℓ hN φ
  unfold schurFunctional
  rw [latticeLaplacian_quadratic]
  have e : (ψ - χ) ⬝ᵥ (ψ - χ) = ∑ x, (ψ x - χ x) ^ 2 := by
    simp only [dotProduct, Pi.sub_apply, sq]
  rw [e]
  have hN2 : (0 : ℝ) < (N : ℝ) ^ 2 := by positivity
  have h2' : latticeEnergy χ / (N : ℝ) ^ 2 ≤ latticeEnergy φ := by
    rw [div_le_iff₀ hN2]; linarith
  have h5 : ∑ x, (∑ μ : Fin d, (φ (x + Pi.single μ 1) - φ x) ^ 2) = latticeEnergy φ := rfl
  unfold coarseForm at h1 ⊢
  rw [h5]
  nlinarith [mul_le_mul_of_nonneg_left h3 hν]

end Main

section Green

variable {d ℓ N m : ℕ} [NeZero ℓ] [NeZero m]

/-- The matrix of the block averaging `Q` of `blockAverage`: `(Q φ) y = N^{-d} ∑_{x ∈ block y} φ x`. -/
noncomputable def blockAverageMatrix (d ℓ N m : ℕ) [NeZero ℓ] [NeZero m] :
    Matrix (Torus d m) (Torus d ℓ) ℝ :=
  fun y x => if blockMap N m x = y then ((N : ℝ) ^ d)⁻¹ else 0

/-- The matrix of the pull-back `Q*` of `blockPullback`: `(Q* ψ) x = ψ (block x)`. -/
noncomputable def blockPullbackMatrix (d ℓ N m : ℕ) [NeZero ℓ] [NeZero m] :
    Matrix (Torus d ℓ) (Torus d m) ℝ :=
  fun x y => if blockMap N m x = y then 1 else 0

theorem blockAverageMatrix_mulVec (φ : Torus d ℓ → ℝ) :
    blockAverageMatrix d ℓ N m *ᵥ φ = blockAverage N m φ := by
  funext y
  simp only [Matrix.mulVec, dotProduct, blockAverageMatrix, ite_mul, zero_mul,
    blockAverage_apply]
  rw [← Finset.sum_filter, ← Finset.mul_sum]
  congr 2

theorem blockPullbackMatrix_mulVec (ψ : Torus d m → ℝ) :
    blockPullbackMatrix d ℓ N m *ᵥ ψ = blockPullback N m ψ := by
  funext x
  simp [Matrix.mulVec, dotProduct, blockPullbackMatrix, blockPullback_apply]

/-- The operator `-Δ^η + ν + a Q* Q` on the fine torus of spacing `η = 1/N` (GREEN.md (1.6) with
`Ω₁ = T_η`, single layer): `N² (-Δ_unit) + ν + a P`. -/
noncomputable def fineHamiltonian (d ℓ N m : ℕ) [NeZero ℓ] [NeZero m] (ν a : ℝ) :
    Matrix (Torus d ℓ) (Torus d ℓ) ℝ :=
  ((N : ℝ) ^ 2) • latticeLaplacian d ℓ (ν / (N : ℝ) ^ 2) + a • blockProjMatrix d ℓ N m

/-- **The unconstrained unit-lattice operator** `Δ^{(k)}_unc = a - a² Q (-Δ^η + ν + aQ*Q)^{-1} Q*`
(GREEN.md (1.8), small-field single-scale case; `Q`, `Q*` the block average and its pull-back).
This is the Schur complement and not P4's constrained `Δ^{(k)}`. -/
noncomputable def unconstrainedUnitOperator (d ℓ N m : ℕ) [NeZero ℓ] [NeZero m] (ν a : ℝ) :
    Matrix (Torus d m) (Torus d m) ℝ :=
  a • (1 : Matrix (Torus d m) (Torus d m) ℝ) -
    (a ^ 2) • (blockAverageMatrix d ℓ N m * (fineHamiltonian d ℓ N m ν a)⁻¹ *
      blockPullbackMatrix d ℓ N m)

theorem unconstrainedUnitOperator_eq (hN : 0 < N) (hd : 0 < d) (hℓ : ℓ = N * m) {ν a : ℝ}
    (hν : 0 ≤ ν) (ha : 0 < a) :
    unconstrainedUnitOperator d ℓ N m ν a =
      ((N : ℝ) ^ 2) • blockSpinOperator (latticeLaplacian d ℓ (ν / (N : ℝ) ^ 2))
        (orthoBlockMatrix d ℓ N m) (a / (N : ℝ) ^ 2) := by
  have hc : (N : ℝ) ^ 2 ≠ 0 := by positivity
  set c : ℝ := (N : ℝ) ^ 2 with hcdef
  have hs : Real.sqrt ((N : ℝ) ^ d) ≠ 0 := by positivity
  have hQa : blockAverageMatrix d ℓ N m = (Real.sqrt ((N : ℝ) ^ d))⁻¹ • orthoBlockMatrix d ℓ N m := by
    ext y x
    simp only [blockAverageMatrix, orthoBlockMatrix, Matrix.smul_apply, smul_eq_mul]
    split_ifs
    · rw [← mul_inv, Real.mul_self_sqrt (by positivity)]
    · simp
  have hQp : blockPullbackMatrix d ℓ N m = Real.sqrt ((N : ℝ) ^ d) • (orthoBlockMatrix d ℓ N m)ᵀ := by
    ext x y
    simp only [blockPullbackMatrix, orthoBlockMatrix, Matrix.smul_apply, Matrix.transpose_apply,
      smul_eq_mul]
    split_ifs
    · field_simp
    · simp
  have hH : fineHamiltonian d ℓ N m ν a =
      c • blockHamiltonian d ℓ N m (ν / c) (a / c) := by
    unfold fineHamiltonian blockHamiltonian
    rw [smul_add, smul_smul, mul_div_cancel₀ _ hc]
  have hMpd := blockHamiltonian_posDef hℓ hN hd (ν := ν / c) (a := a / c) (by positivity)
    (by positivity)
  have hdet : IsUnit (blockHamiltonian d ℓ N m (ν / c) (a / c)).det :=
    (Matrix.isUnit_iff_isUnit_det _).1 hMpd.isUnit
  have hinv : (fineHamiltonian d ℓ N m ν a)⁻¹ =
      c⁻¹ • (blockHamiltonian d ℓ N m (ν / c) (a / c))⁻¹ := by
    rw [hH]
    have : Invertible c := invertibleOfNonzero hc
    rw [Matrix.inv_smul (k := c) (h := hdet), invOf_eq_inv]
  unfold unconstrainedUnitOperator blockSpinOperator
  rw [blockSpinPrecision_ortho hN, hQa, hQp, hinv]
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  rw [smul_sub, smul_smul, smul_smul]
  have h1 : c * (a / c) = a := by field_simp
  have h2 : a ^ 2 * (Real.sqrt ((N : ℝ) ^ d) * (c⁻¹ * (Real.sqrt ((N : ℝ) ^ d))⁻¹)) =
      c * (a / c) ^ 2 := by field_simp
  rw [h1, h2]

/-- **G-1(b), single scale, `α = 0` (GREEN.md §4.1).** For the unconstrained unit-lattice operator
`Δ^{(k)}_unc` and `ν ≥ 0`, `a > 0`:
`a / (a + 4d + ν) · (E(ψ) + ν ‖ψ‖²) ≤ ⟨ψ, Δ^{(k)}_unc ψ⟩`, with `E` the unit-spacing Dirichlet energy
on the coarse torus. -/
theorem unconstrainedUnitOperator_lower (hℓ : ℓ = N * m) (hN : 0 < N) (hd : 0 < d) {ν a : ℝ}
    (hν : 0 ≤ ν) (ha : 0 < a) (ψ : Torus d m → ℝ) :
    a / (a + 4 * d + ν) * (latticeEnergy ψ + ν * ∑ x, ψ x ^ 2) ≤
      ψ ⬝ᵥ unconstrainedUnitOperator d ℓ N m ν a *ᵥ ψ := by
  have hc : (0 : ℝ) < (N : ℝ) ^ 2 := by positivity
  set c : ℝ := (N : ℝ) ^ 2 with hcdef
  have h := unitLattice_lower hℓ hN hd (ν := ν / c) (a := a / c) (by positivity) (by positivity) ψ
  rw [← hcdef] at h
  rw [unconstrainedUnitOperator_eq hN hd hℓ hν ha, Matrix.smul_mulVec, dotProduct_smul,
    smul_eq_mul]
  have e : a / c / (a / c + (4 * d / c + ν / c)) = a / (a + 4 * d + ν) := by
    have : 0 < a + 4 * d + ν := by positivity
    field_simp
    ring
  rw [e] at h
  unfold coarseForm at h
  have h2 := mul_le_mul_of_nonneg_left h hc.le
  have e2 : c * (a / (a + 4 * d + ν) * (latticeEnergy ψ / c + ν / c * ∑ x, ψ x ^ 2)) =
      a / (a + 4 * d + ν) * (latticeEnergy ψ + ν * ∑ x, ψ x ^ 2) := by
    field_simp
  linarith

/-- The quantitative constant: for `1/2 ≤ a` and `ν ≤ 1`, `a / (a + 4d + ν) ≥ 1/(8d+3)`. -/
theorem unconstrained_gamma_ge {d : ℕ} {ν a : ℝ} (hν : 0 ≤ ν) (hν1 : ν ≤ 1) (ha : 1 / 2 ≤ a) :
    1 / (8 * (d : ℝ) + 3) ≤ a / (a + 4 * d + ν) := by
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith

/-- Upper bound `ψᵀ Δ_unc ψ ≤ a ‖ψ‖²`. -/
theorem unconstrainedUnitOperator_le (hℓ : ℓ = N * m) (hN : 0 < N) (hd : 0 < d) {ν a : ℝ}
    (hν : 0 ≤ ν) (ha : 0 < a) (ψ : Torus d m → ℝ) :
    ψ ⬝ᵥ unconstrainedUnitOperator d ℓ N m ν a *ᵥ ψ ≤ a * ∑ x, ψ x ^ 2 := by
  have hc : (0 : ℝ) < (N : ℝ) ^ 2 := by positivity
  set c : ℝ := (N : ℝ) ^ 2 with hcdef
  have hM : (blockSpinPrecision (latticeLaplacian d ℓ (ν / c)) (orthoBlockMatrix d ℓ N m)
      (a / c)).PosDef := by
    rw [blockSpinPrecision_ortho hN]
    exact blockHamiltonian_posDef hℓ hN hd (by positivity) (by positivity)
  have h := blockSpinOperator_form_le hM ψ 0
  unfold schurFunctional at h
  simp only [Matrix.mulVec_zero, sub_zero, dotProduct_zero, add_zero] at h
  rw [unconstrainedUnitOperator_eq hN hd hℓ hν ha, Matrix.smul_mulVec, dotProduct_smul,
    smul_eq_mul]
  have e : ψ ⬝ᵥ ψ = ∑ x, ψ x ^ 2 := by simp only [dotProduct, sq]
  rw [e] at h
  have := mul_le_mul_of_nonneg_left h hc.le
  have e2 : c * (a / c * ∑ x, ψ x ^ 2) = a * ∑ x, ψ x ^ 2 := by field_simp
  linarith

end Green

end Balaban
