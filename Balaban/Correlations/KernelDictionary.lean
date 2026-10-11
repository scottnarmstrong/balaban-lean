module

public import Balaban.Gaussian.TermDictionary
public import Balaban.Correlations.TermKernel
public import Balaban.Green.CoarseOperator
public import Balaban.Green.TranslationInvariant
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-!
# The term dictionary: `T_j = L^{-j(d-2)} K C_tr K^T` (CORRELATIONS.md (2.2))

The `j`-th term `T_j` of the multiscale decomposition of `-Δ + μ` for the free flow
`α_i = a L^{(i+1)(d-2)}` (`termDirect`, `freeSeq`), written with the objects of the unit-lattice
Green package (G-5):

* `schurFluct A Q s = A⁻¹ - H Δ⁻¹ Hᵀ` is the fluctuation covariance of a one-shot step; for
  `s > 0` it is `(A + s⁻¹ Qᵀ Q)⁻¹` (`schurFluct_eq_inv`);
* `termDirect_freeSeq_succ`, `termDirect_freeSeq_zero`: `T_j = F_{j+1} - F_j`, `F_J` the inverse
  of the fine operator `blockHamiltonian μ (a_J / L^{2J})` (`F_0 = 0`),
  `a_J = aScale L a J = a (1 - L^{-2}) / (1 - L^{-2J})`;
* `termDirect_freeSeq_unit` (`j ≥ 1`): `T_j = L^{-j(d-2)} K C_tr Kᵀ` with the fine-to-block kernel
  `K = a_j G Q*` (`Balaban.Green.fineToBlockKernel`) and `C_tr = (Δ_tr + a L⁻² Q* Q)⁻¹`
  (`Balaban.Green.coarseOperator`) at the unit-lattice mass `ν_j = μ L^{2j}`;
* `schurProlong_blockAverage`: the prolongation `H = A⁻¹ Qᵀ Δ` is `K`.
-/

@[expose] public section

namespace Balaban

open Matrix

section Abstract
variable {ι κ ρ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  [Fintype ρ] [DecidableEq ρ]

/-- The fluctuation covariance of a one-shot block-spin step with inverse penalty `s`:
`A⁻¹ - H Δ⁻¹ Hᵀ` (`H = schurProlong`, `Δ = schurOp`). For `s > 0` this is
`(A + s⁻¹ Qᵀ Q)⁻¹` (`schurFluct_eq_inv`); for the identity average and `s = 0` it is `0`. -/
noncomputable def schurFluct (A : Matrix ι ι ℝ) (Q : Matrix κ ι ℝ) (s : ℝ) : Matrix ι ι ℝ :=
  A⁻¹ - schurProlong A Q s * (schurOp A Q s)⁻¹ * (schurProlong A Q s)ᵀ

theorem schurFluct_eq_inv {A : Matrix ι ι ℝ} (hA : A.PosDef) (Q : Matrix κ ι ℝ) {s : ℝ}
    (hs : 0 < s) : schurFluct A Q s = (A + s⁻¹ • (Qᵀ * Q))⁻¹ := by
  have ha : 0 < s⁻¹ := inv_pos.mpr hs
  have h := inv_eq_blockSpin_decomposition hA Q ha
  rw [blockSpinProlong_eq_schurProlong hA Q ha, blockSpinOperator_eq_schurOp hA Q ha,
    inv_inv] at h
  unfold schurFluct
  have h' : A⁻¹ = (A + s⁻¹ • (Qᵀ * Q))⁻¹ + schurProlong A Q s * (schurOp A Q s)⁻¹ *
      (schurProlong A Q s)ᵀ := h
  rw [h']
  abel

/-- The `j`-th term as a difference of two fluctuation covariances. -/
theorem schurProlong_term {A : Matrix ι ι ℝ} (hA : A.PosDef) (Q : Matrix κ ι ℝ) {s₀ : ℝ}
    (hs₀ : 0 < s₀) (R : Matrix ρ κ ℝ) {r : ℝ} (hR : R * Rᵀ = r • (1 : Matrix ρ ρ ℝ)) {a : ℝ}
    (ha : 0 < a) :
    schurProlong A Q s₀ * (schurOp A Q s₀ + a • (Rᵀ * R))⁻¹ * (schurProlong A Q s₀)ᵀ =
      schurFluct A (R * Q) (a⁻¹ + r * s₀) - schurFluct A Q s₀ := by
  have hΔ := blockSpinOperator_posDef hA Q (inv_pos.mpr hs₀)
  rw [blockSpinOperator_eq_schurOp hA Q (inv_pos.mpr hs₀), inv_inv] at hΔ
  have hdec := inv_eq_blockSpin_decomposition hΔ R ha
  rw [blockSpinProlong_eq_schurProlong hΔ R ha, blockSpinOperator_eq_schurOp hΔ R ha] at hdec
  unfold schurFluct
  rw [← schurProlong_comp hA Q hs₀ R hR a⁻¹, ← schurOp_comp hA Q hs₀ R hR a⁻¹]
  have hdec' : (schurOp A Q s₀)⁻¹ = (schurOp A Q s₀ + a • (Rᵀ * R))⁻¹ +
      schurProlong (schurOp A Q s₀) R a⁻¹ * (schurOp (schurOp A Q s₀) R a⁻¹)⁻¹ *
        (schurProlong (schurOp A Q s₀) R a⁻¹)ᵀ := hdec
  rw [hdec']
  simp only [Matrix.transpose_mul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
  abel

end Abstract

section Levels

variable {d L : ℕ} [NeZero L] {ℓ ℓ₁ m₂ : ℕ} [NeZero ℓ] [NeZero ℓ₁] [NeZero m₂]

/-- `Qᵀ Q = N^{-d} P` for the block average `Q` and the block projection `P`. -/
theorem blockAverageMatrix_transpose_mul (N m : ℕ) [NeZero m] :
    (blockAverageMatrix N m : Matrix (Torus d m) (Torus d ℓ) ℝ)ᵀ *
        (blockAverageMatrix N m : Matrix (Torus d m) (Torus d ℓ) ℝ) =
      ((N : ℝ) ^ d)⁻¹ • blockProjMatrix d ℓ N m := by
  ext x x'
  simp only [Matrix.mul_apply, Matrix.transpose_apply, blockAverageMatrix, blockProjMatrix,
    Matrix.smul_apply, smul_eq_mul]
  by_cases h : blockMap N m x = blockMap N m x'
  · rw [Finset.sum_eq_single (blockMap N m x)]
    · simp [h]
    · intro y _ hy
      have : ¬ blockMap N m x = y := fun h' => hy h'.symm
      simp [this]
    · simp
  · simp only [h, ite_false, mul_zero]
    refine Finset.sum_eq_zero fun y _ => ?_
    by_cases h1 : blockMap N m x = y
    · have : ¬ blockMap N m x' = y := fun h2 => h (h1.trans h2.symm)
      simp [this]
    · simp [h1]

/-- `a_J = a (1 - L^{-2}) / (1 - L^{-2J})`, the unit-lattice penalty at scale `J`. -/
noncomputable def aScale (L : ℕ) (a : ℝ) (J : ℕ) : ℝ :=
  a * (1 - ((L : ℝ) ^ 2)⁻¹) / (1 - ((L : ℝ) ^ (2 * J))⁻¹)

omit [NeZero L] in
theorem aScale_one (hL : 1 < L) (a : ℝ) : aScale L a 1 = a := by
  unfold aScale
  have hx : (1 : ℝ) < L := by exact_mod_cast hL
  have h : (1 : ℝ) - ((L : ℝ) ^ 2)⁻¹ ≠ 0 := by
    have : ((L : ℝ) ^ 2)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (one_lt_pow₀ hx (by norm_num))
    linarith
  rw [Nat.mul_one, mul_div_assoc, div_self h, mul_one]

omit [NeZero L] in
theorem aScale_pos (hL : 1 < L) {a : ℝ} (ha : 0 < a) {J : ℕ} (hJ : 1 ≤ J) : 0 < aScale L a J := by
  unfold aScale
  have hx : (1 : ℝ) < L := by exact_mod_cast hL
  have h1 : ((L : ℝ) ^ 2)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (one_lt_pow₀ hx (by norm_num))
  have h2 : ((L : ℝ) ^ (2 * J))⁻¹ < 1 :=
    inv_lt_one_of_one_lt₀ (one_lt_pow₀ hx (by omega))
  have h3 : 0 < 1 - ((L : ℝ) ^ 2)⁻¹ := by linarith
  have h4 : 0 < 1 - ((L : ℝ) ^ (2 * J))⁻¹ := by linarith
  positivity

theorem inv_invScale_freeSeq (hd : 2 ≤ d) (hL : 1 < L) {a : ℝ} (ha : 0 < a) {J : ℕ}
    (hJ : 1 ≤ J) :
    (invScale d L J (freeSeq d L a))⁻¹ = aScale L a J * (L : ℝ) ^ (J * (d - 2)) := by
  rw [invScale_freeSeq hd hL ha J]
  unfold aScale
  have hx : (1 : ℝ) < L := by exact_mod_cast hL
  have h1 : ((L : ℝ) ^ 2)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (one_lt_pow₀ hx (by norm_num))
  have h2 : ((L : ℝ) ^ (2 * J))⁻¹ < 1 :=
    inv_lt_one_of_one_lt₀ (one_lt_pow₀ hx (by omega))
  have h3 : 1 - ((L : ℝ) ^ 2)⁻¹ ≠ 0 := by linarith
  have h4 : 1 - ((L : ℝ) ^ (2 * J))⁻¹ ≠ 0 := by linarith
  have h5 : (0 : ℝ) < (L : ℝ) ^ (J * (d - 2)) := by positivity
  field_simp

theorem invScale_succ_freeSeq (hd : 2 ≤ d) (hL : 1 < L) {a : ℝ} (ha : 0 < a) (j : ℕ) :
    invScale d L (j + 1) (freeSeq d L a) =
      (freeSeq d L a j)⁻¹ + ((L : ℝ) ^ d)⁻¹ * invScale d L j (freeSeq d L a) := by
  obtain ⟨e, rfl⟩ : ∃ e, d = e + 2 := ⟨d - 2, by omega⟩
  rw [invScale_freeSeq hd hL ha, invScale_freeSeq hd hL ha]
  unfold freeSeq
  have hx : (1 : ℝ) < L := by exact_mod_cast hL
  have hx0 : (0 : ℝ) < L := by linarith
  have h1 : ((L : ℝ) ^ 2)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (one_lt_pow₀ hx (by norm_num))
  have h3 : 1 - ((L : ℝ) ^ 2)⁻¹ ≠ 0 := by linarith
  simp only [Nat.add_sub_cancel]
  have e1 : (L : ℝ) ^ ((j + 1) * e) = (L : ℝ) ^ (j * e) * (L : ℝ) ^ e := by
    rw [← pow_add]; congr 1; ring
  have e2 : (L : ℝ) ^ (2 * (j + 1)) = (L : ℝ) ^ (2 * j) * (L : ℝ) ^ 2 := by
    rw [show 2 * (j + 1) = 2 * j + 2 by ring, pow_add]
  have e3 : (L : ℝ) ^ (e + 2) = (L : ℝ) ^ e * (L : ℝ) ^ 2 := pow_add _ _ _
  rw [e1, e2, e3]
  have hy : (0 : ℝ) < (L : ℝ) ^ e := by positivity
  have hz : (0 : ℝ) < (L : ℝ) ^ (j * e) := by positivity
  have hw : (0 : ℝ) < (L : ℝ) ^ (2 * j) := by positivity
  have hv : (0 : ℝ) < (L : ℝ) ^ 2 := by positivity
  have hv1 : (L : ℝ) ^ 2 - 1 ≠ 0 := by
    have : (1 : ℝ) < (L : ℝ) ^ 2 := one_lt_pow₀ hx (by norm_num)
    linarith
  generalize (L : ℝ) ^ e = Y at *
  generalize (L : ℝ) ^ (j * e) = Z at *
  generalize (L : ℝ) ^ (2 * j) = W at *
  generalize (L : ℝ) ^ 2 = V at *
  have hW1 : W ≠ 0 := hw.ne'
  field_simp
  ring

theorem schurFluct_freeSeq (hd : 2 ≤ d) (hL : 1 < L) {a μ : ℝ} (ha : 0 < a) (hμ : 0 < μ)
    {J m : ℕ} [NeZero m] (hJ : 1 ≤ J) (hℓ : ℓ = L ^ J * m) :
    schurFluct (latticeLaplacian d ℓ μ)
        (blockAverageMatrix (L ^ J) m : Matrix (Torus d m) (Torus d ℓ) ℝ)
        (invScale d L J (freeSeq d L a)) =
      (blockHamiltonian d ℓ (L ^ J) m μ (aScale L a J / ((L : ℝ) ^ J) ^ 2))⁻¹ := by
  obtain ⟨n, rfl⟩ : ∃ n, J = n + 1 := ⟨J - 1, by omega⟩
  have hpos := invScale_pos d L n (a := freeSeq d L a) (fun i => freeSeq_pos ha i)
  rw [schurFluct_eq_inv (latticeLaplacian_posDef hμ) _ hpos]
  congr 1
  unfold blockHamiltonian
  rw [blockAverageMatrix_transpose_mul, smul_smul, inv_invScale_freeSeq hd hL ha hJ]
  congr 2
  obtain ⟨e, rfl⟩ : ∃ e, d = e + 2 := ⟨d - 2, by omega⟩
  have hx0 : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  simp only [Nat.add_sub_cancel, Nat.cast_pow]
  have e1 : (L : ℝ) ^ ((n + 1) * e) = ((L : ℝ) ^ (n + 1)) ^ e := by rw [← pow_mul, mul_comm]
  rw [e1]
  have : (0 : ℝ) < (L : ℝ) ^ (n + 1) := by positivity
  generalize (L : ℝ) ^ (n + 1) = Y at *
  field_simp
  ring

theorem termDirect_freeSeq_succ (hd : 2 ≤ d) (hL : 1 < L) {a μ : ℝ} (ha : 0 < a) (hμ : 0 < μ)
    {j : ℕ} (hj : 1 ≤ j) (hℓ : ℓ = L ^ j * ℓ₁) (hℓ₁ : ℓ₁ = L * m₂) :
    termDirect d L j ℓ ℓ₁ m₂ (latticeLaplacian d ℓ μ) (freeSeq d L a) =
      (blockHamiltonian d ℓ (L ^ (j + 1)) m₂ μ (aScale L a (j + 1) / ((L : ℝ) ^ (j + 1)) ^ 2))⁻¹ -
      (blockHamiltonian d ℓ (L ^ j) ℓ₁ μ (aScale L a j / ((L : ℝ) ^ j) ^ 2))⁻¹ := by
  have hA := latticeLaplacian_posDef (d := d) (ℓ := ℓ) hμ
  have hL0 : 0 < L := Nat.pos_of_ne_zero (NeZero.ne L)
  obtain ⟨n, rfl⟩ : ∃ n, j = n + 1 := ⟨j - 1, by omega⟩
  have hs₀ := invScale_pos d L n (a := freeSeq d L a) (fun i => freeSeq_pos ha i)
  have hR := blockAverageMatrix_mul_transpose (d := d) (ℓ := ℓ₁) (N := L) (m := m₂) hℓ₁ hL0
  have key := schurProlong_term hA
    (blockAverageMatrix (L ^ (n + 1)) ℓ₁ : Matrix (Torus d ℓ₁) (Torus d ℓ) ℝ) hs₀
    (blockAverageMatrix L m₂ : Matrix (Torus d m₂) (Torus d ℓ₁) ℝ) hR
    (freeSeq_pos (d := d) (L := L) ha (n + 1))
  have hRQ := blockAverageMatrix_mul (d := d) (ℓ := ℓ) (m₁ := ℓ₁) (m₂ := m₂) (N := L ^ (n + 1))
    (M := L) hℓ hℓ₁
  have hpow : L ^ (n + 1) * L = L ^ (n + 1 + 1) := (pow_succ L (n + 1)).symm
  rw [hpow] at hRQ
  have hs := invScale_succ_freeSeq hd hL ha (n + 1)
  have hℓ' : ℓ = L ^ (n + 1 + 1) * m₂ := by rw [hℓ, hℓ₁, pow_succ]; ring
  unfold termDirect
  simp only []
  rw [key, hRQ, ← hs, schurFluct_freeSeq hd hL ha hμ (by omega) hℓ',
    schurFluct_freeSeq hd hL ha hμ (by omega) hℓ]

theorem termDirect_freeSeq_zero (hd : 2 ≤ d) (hL : 1 < L) {a μ : ℝ} (ha : 0 < a) (hμ : 0 < μ) :
    termDirect d L 0 ℓ ℓ m₂ (latticeLaplacian d ℓ μ) (freeSeq d L a) =
      (blockHamiltonian d ℓ (L ^ (0 + 1)) m₂ μ (aScale L a (0 + 1) / ((L : ℝ) ^ (0 + 1)) ^ 2))⁻¹ := by
  have hA := latticeLaplacian_posDef (d := d) (ℓ := ℓ) hμ
  have hC : (blockAverageMatrix (L ^ 0) ℓ : Matrix (Torus d ℓ) (Torus d ℓ) ℝ) = 1 :=
    blockAverageMatrix_of_eq_one (pow_zero L)
  unfold termDirect
  simp only [hC]
  have h1 : invScale d L 0 (freeSeq d L a) = 0 := rfl
  rw [h1, schurProlong_one hA, schurOp_one hA]
  simp only [Matrix.one_mul, Matrix.transpose_one, Matrix.mul_one]
  congr 1
  unfold blockHamiltonian
  rw [blockAverageMatrix_transpose_mul, smul_smul, aScale_one hL]
  simp only [zero_add, pow_one]
  congr 2
  obtain ⟨e, rfl⟩ : ∃ e, d = e + 2 := ⟨d - 2, by omega⟩
  have hx0 : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  simp only [freeSeq, Nat.add_sub_cancel, zero_add, one_mul]
  field_simp
  ring

end Levels

section Unit

variable {d ℓ N m : ℕ} [NeZero ℓ] [NeZero m]

theorem blockAverageMatrix_eq_ortho (N : ℕ) :
    (blockAverageMatrix N m : Matrix (Torus d m) (Torus d ℓ) ℝ) =
      (Real.sqrt ((N : ℝ) ^ d))⁻¹ • orthoBlockMatrix d ℓ N m := by
  ext y x
  simp only [orthoBlockMatrix, blockAverageMatrix, Matrix.smul_apply, smul_eq_mul]
  split_ifs
  · rw [← mul_inv, Real.mul_self_sqrt (by positivity)]
  · simp

theorem blockPullback_eq_ortho (N : ℕ) (hN : 0 < N) :
    (blockPullbackMatrix d ℓ N m) =
      Real.sqrt ((N : ℝ) ^ d) • (orthoBlockMatrix d ℓ N m)ᵀ := by
  have hs : Real.sqrt ((N : ℝ) ^ d) ≠ 0 := by positivity
  ext x y
  simp only [blockPullbackMatrix, orthoBlockMatrix, Matrix.smul_apply, Matrix.transpose_apply,
    smul_eq_mul]
  split_ifs
  · field_simp
  · simp

theorem schurOp_blockAverage (hℓ : ℓ = N * m) (hN : 0 < N) (hd : 0 < d) {μ s aJ : ℝ} (hμ : 0 < μ)
    (haJ : 0 < aJ) (hs : s * (N : ℝ) ^ d = (N : ℝ) ^ 2 / aJ) :
    schurOp (latticeLaplacian d ℓ μ) (blockAverageMatrix N m : Matrix (Torus d m) (Torus d ℓ) ℝ)
        s = ((N : ℝ) ^ d / (N : ℝ) ^ 2) • unconstrainedUnitOperator d ℓ N m (μ * (N : ℝ) ^ 2) aJ := by
  have hA := latticeLaplacian_posDef (d := d) (ℓ := ℓ) hμ
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hc : (N : ℝ) ^ 2 ≠ 0 := by positivity
  have hσ : 0 < Real.sqrt ((N : ℝ) ^ d) := Real.sqrt_pos.2 (by positivity)
  have hσ2 : Real.sqrt ((N : ℝ) ^ d) * Real.sqrt ((N : ℝ) ^ d) = (N : ℝ) ^ d :=
    Real.mul_self_sqrt (by positivity)
  set Qo : Matrix (Torus d m) (Torus d ℓ) ℝ := orthoBlockMatrix d ℓ N m with hQo
  have hs'' : 0 < s * (N : ℝ) ^ d := by rw [hs]; positivity
  -- the orthonormal version
  have h1 : schurOp (latticeLaplacian d ℓ μ) Qo (s * (N : ℝ) ^ d) =
      blockSpinOperator (latticeLaplacian d ℓ μ) Qo (aJ / (N : ℝ) ^ 2) := by
    rw [blockSpinOperator_eq_schurOp hA Qo (by positivity), hs, inv_div]
  have h2 := unconstrainedUnitOperator_eq (d := d) (ℓ := ℓ) (N := N) (m := m) hN hd hℓ
    (ν := μ * (N : ℝ) ^ 2) (a := aJ) (by positivity) haJ
  rw [mul_div_cancel_right₀ _ hc] at h2
  rw [h2, ← h1]
  -- scaling
  have hM : IsUnit (((s * (N : ℝ) ^ d) • (1 : Matrix (Torus d m) (Torus d m) ℝ) +
      Qo * (latticeLaplacian d ℓ μ)⁻¹ * Qoᵀ)).det := by
    have := woodbury_posDef hA Qo (inv_pos.mpr hs'')
    rw [inv_inv] at this
    exact isUnit_iff_ne_zero.mpr this.det_pos.ne'
  unfold schurOp
  rw [blockAverageMatrix_eq_ortho]
  have e : (s • (1 : Matrix (Torus d m) (Torus d m) ℝ) +
      ((Real.sqrt ((N : ℝ) ^ d))⁻¹ • Qo) * (latticeLaplacian d ℓ μ)⁻¹ *
        ((Real.sqrt ((N : ℝ) ^ d))⁻¹ • Qo)ᵀ) =
      ((N : ℝ) ^ d)⁻¹ • ((s * (N : ℝ) ^ d) • (1 : Matrix (Torus d m) (Torus d m) ℝ) +
        Qo * (latticeLaplacian d ℓ μ)⁻¹ * Qoᵀ) := by
    simp only [Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_add, smul_smul]
    congr 1
    · congr 1; field_simp
    · congr 1
      rw [← mul_inv, hσ2]
  rw [e]
  have : Invertible (((N : ℝ) ^ d)⁻¹) := invertibleOfNonzero (by positivity)
  rw [Matrix.inv_smul (k := ((N : ℝ) ^ d)⁻¹) (h := hM), invOf_eq_inv, inv_inv, smul_smul]
  congr 1
  field_simp

theorem schurProlong_blockAverage (hℓ : ℓ = N * m) (hN : 0 < N) (hd : 0 < d) {μ s aJ : ℝ}
    (hμ : 0 < μ) (haJ : 0 < aJ) (hs : s * (N : ℝ) ^ d = (N : ℝ) ^ 2 / aJ) :
    schurProlong (latticeLaplacian d ℓ μ)
        (blockAverageMatrix N m : Matrix (Torus d m) (Torus d ℓ) ℝ) s =
      Green.fineToBlockKernel d ℓ N m (μ * (N : ℝ) ^ 2) aJ := by
  have hA := latticeLaplacian_posDef (d := d) (ℓ := ℓ) hμ
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hc : (N : ℝ) ^ 2 ≠ 0 := by positivity
  have hσ : 0 < Real.sqrt ((N : ℝ) ^ d) := Real.sqrt_pos.2 (by positivity)
  have hσ2 : Real.sqrt ((N : ℝ) ^ d) * Real.sqrt ((N : ℝ) ^ d) = (N : ℝ) ^ d :=
    Real.mul_self_sqrt (by positivity)
  set Qo : Matrix (Torus d m) (Torus d ℓ) ℝ := orthoBlockMatrix d ℓ N m with hQo
  have ha' : 0 < aJ / (N : ℝ) ^ 2 := by positivity
  have hop := schurOp_blockAverage (m := m) hℓ hN hd hμ haJ hs
  have h2 := unconstrainedUnitOperator_eq (d := d) (ℓ := ℓ) (N := N) (m := m) hN hd hℓ
    (ν := μ * (N : ℝ) ^ 2) (a := aJ) (by positivity) haJ
  rw [mul_div_cancel_right₀ _ hc] at h2
  have hpro := blockSpinProlong_eq hA Qo ha'
  have hprec := blockSpinPrecision_ortho (d := d) (ℓ := ℓ) (N := N) (m := m) hN μ (aJ / (N : ℝ) ^ 2)
  unfold schurProlong
  rw [hop, blockAverageMatrix_eq_ortho]
  unfold Green.fineToBlockKernel
  rw [Green.fineHamiltonian_inv hℓ hN hd (by positivity) haJ, blockPullback_eq_ortho N hN,
    mul_div_cancel_right₀ _ hc]
  have hP : (latticeLaplacian d ℓ μ)⁻¹ * (Qoᵀ * blockSpinOperator (latticeLaplacian d ℓ μ) Qo
      (aJ / (N : ℝ) ^ 2)) = (aJ / (N : ℝ) ^ 2) • ((blockHamiltonian d ℓ N m μ (aJ / (N : ℝ) ^ 2))⁻¹ * Qoᵀ) := by
    rw [← hpro]
    unfold blockSpinProlong
    rw [hprec]
  rw [h2]
  simp only [Matrix.transpose_smul, Matrix.mul_smul, Matrix.smul_mul, smul_smul]
  rw [Matrix.mul_assoc, hP]
  simp only [smul_smul]
  congr 1
  generalize Real.sqrt ((N : ℝ) ^ d) = σ at *
  rw [← hσ2]
  field_simp

end Unit

section Dictionary

variable {d L : ℕ} [NeZero L] {ℓ ℓ₁ m₂ : ℕ} [NeZero ℓ] [NeZero ℓ₁] [NeZero m₂]

theorem invScale_freeSeq_mul (hd : 2 ≤ d) (hL : 1 < L) {a : ℝ} (ha : 0 < a) {j : ℕ}
    (hj : 1 ≤ j) :
    invScale d L j (freeSeq d L a) * ((L ^ j : ℕ) : ℝ) ^ d =
      ((L ^ j : ℕ) : ℝ) ^ 2 / aScale L a j := by
  have hx0 : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have haJ0 : 0 < aScale L a j := aScale_pos hL ha hj
  have h := inv_invScale_freeSeq hd hL ha hj
  obtain ⟨e, rfl⟩ : ∃ e, d = e + 2 := ⟨d - 2, by omega⟩
  rw [← inv_inv (invScale (e + 2) L j (freeSeq (e + 2) L a)), h]
  simp only [Nat.add_sub_cancel, Nat.cast_pow]
  have e1 : ((L : ℝ) ^ j) ^ (e + 2) = (L : ℝ) ^ (j * e) * ((L : ℝ) ^ j) ^ 2 := by
    rw [← pow_mul, ← pow_mul, ← pow_add]; congr 1; ring
  rw [e1]
  have : (0 : ℝ) < (L : ℝ) ^ (j * e) := by positivity
  field_simp

/-- **The dictionary** (CORRELATIONS.md (2.2)): for `j ≥ 1` the `j`-th term of the free flow is
`T_j = L^{-j(d-2)} K C_tr K^T`, with `K = a_j G Q_j^*` (`fineToBlockKernel`) and
`C_tr = (Δ_tr + a L^{-2} Q^* Q)⁻¹` (`coarseOperator`) of the unit lattice at mass
`ν_j = μ L^{2j}` and penalty `a_j`. -/
theorem termDirect_freeSeq_unit (hd : 2 ≤ d) (hL : 1 < L) {a μ : ℝ} (ha : 0 < a) (hμ : 0 < μ)
    {j : ℕ} (hj : 1 ≤ j) (hℓ : ℓ = L ^ j * ℓ₁) (hℓ₁ : ℓ₁ = L * m₂) (hν2 : μ * ((L : ℝ) ^ j) ^ 2 ≤ 2)
    (haJ : 1 / 2 ≤ aScale L a j) (ha1 : 1 / 2 ≤ a) :
    termDirect d L j ℓ ℓ₁ m₂ (latticeLaplacian d ℓ μ) (freeSeq d L a) =
      (((L : ℝ) ^ (j * (d - 2)))⁻¹) •
        (Green.fineToBlockKernel d ℓ (L ^ j) ℓ₁ (μ * ((L ^ j : ℕ) : ℝ) ^ 2) (aScale L a j) *
          (Green.coarseOperator d ℓ (L ^ j) ℓ₁ L m₂ (μ * ((L ^ j : ℕ) : ℝ) ^ 2) (aScale L a j)
            a)⁻¹ *
          (Green.fineToBlockKernel d ℓ (L ^ j) ℓ₁ (μ * ((L ^ j : ℕ) : ℝ) ^ 2) (aScale L a j))ᵀ) := by
  have hd0 : 0 < d := by omega
  have hL0 : 0 < L := Nat.pos_of_ne_zero (NeZero.ne L)
  have hN : 0 < L ^ j := Nat.pos_of_ne_zero (pow_ne_zero _ (NeZero.ne L))
  have haJ0 : 0 < aScale L a j := aScale_pos hL ha hj
  have hx0 : (0 : ℝ) < L := by exact_mod_cast hL0
  obtain ⟨e, rfl⟩ : ∃ e, d = e + 2 := ⟨d - 2, by omega⟩
  have hs := invScale_freeSeq_mul (d := e + 2) (L := L) hd hL ha hj
  have hK := schurProlong_blockAverage (m := ℓ₁) hℓ (by exact hN) hd0 hμ haJ0 hs
  have hΔ := schurOp_blockAverage (m := ℓ₁) hℓ hN hd0 hμ haJ0 hs
  unfold termDirect
  simp only []
  rw [hK, hΔ, blockAverageMatrix_transpose_mul (ℓ := ℓ₁) L m₂]
  have hc : (((L ^ j : ℕ) : ℝ) ^ (e + 2) / ((L ^ j : ℕ) : ℝ) ^ 2) = (L : ℝ) ^ (j * e) := by
    simp only [Nat.cast_pow]
    rw [← pow_mul, ← pow_mul, show j * (e + 2) = j * 2 + j * e by ring, pow_add]
    have : (0 : ℝ) < (L : ℝ) ^ (j * 2) := by positivity
    rw [mul_comm j 2]
    field_simp
  have hmid : (((L ^ j : ℕ) : ℝ) ^ (e + 2) / ((L ^ j : ℕ) : ℝ) ^ 2) •
      unconstrainedUnitOperator (e + 2) ℓ (L ^ j) ℓ₁ (μ * ((L ^ j : ℕ) : ℝ) ^ 2) (aScale L a j) +
      freeSeq (e + 2) L a j • (((L : ℝ) ^ (e + 2))⁻¹ • blockProjMatrix (e + 2) ℓ₁ L m₂) =
      (L : ℝ) ^ (j * e) • Green.coarseOperator (e + 2) ℓ (L ^ j) ℓ₁ L m₂
        (μ * ((L ^ j : ℕ) : ℝ) ^ 2) (aScale L a j) a := by
    unfold Green.coarseOperator
    rw [smul_add, smul_smul, smul_smul, hc]
    congr 2
    simp only [freeSeq, Nat.add_sub_cancel]
    have e1 : (L : ℝ) ^ ((j + 1) * e) = (L : ℝ) ^ (j * e) * (L : ℝ) ^ e := by
      rw [← pow_add]; congr 1; ring
    rw [e1, pow_add]
    field_simp
  have hdet : IsUnit (Green.coarseOperator (e + 2) ℓ (L ^ j) ℓ₁ L m₂
      (μ * ((L ^ j : ℕ) : ℝ) ^ 2) (aScale L a j) a).det := by
    refine Green.coarseOperator_det_isUnit (L := L) (M := m₂) hd0 hℓ hN hℓ₁ ?_ ?_ haJ ha1
    · positivity
    · simpa [Nat.cast_pow] using hν2
  rw [hmid]
  have : Invertible ((L : ℝ) ^ (j * e)) := invertibleOfNonzero (by positivity)
  rw [Matrix.inv_smul (k := (L : ℝ) ^ (j * e)) (h := hdet), invOf_eq_inv]
  simp only [Nat.add_sub_cancel, Matrix.mul_smul, Matrix.smul_mul]

end Dictionary
end Balaban
