/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.DetCauchyBgActivity
public import Balaban.Fluctuation.DetOutputTerms
public import Balaban.Fluctuation.ExpansionSymm
public import Balaban.Fluctuation.InteractionSymmRot
public import Balaban.Localization.DecEquivRot

/-!
# Spin-rotation invariance of the root trace and of the determinant activities

Let `R` be a complex `N × N` matrix with `Rᵀ * R = 1` (transpose orthogonality; no Hermitian
conjugate is used) and `1 ⊗ R = rotLift R` its lift to `ι × Fin N`.  The operators `Q`, `P`,
`G_{s,x}` act on sites and are spin scalars, so they commute with the lift, and the bilinear field
forms in `M`, `N`, `Π` transform through `R` and `Rᵀ`:

* `decM_rot`: `M` is unchanged; `decN_rot`: `N ↦ N (1 ⊗ Rᵀ)`; `decPi_rot`: `Π ↦ (1 ⊗ R) Π (1 ⊗ Rᵀ)`;
* `decCov_rot`: `C_x ↦ (1 ⊗ R) C_x (1 ⊗ Rᵀ)` (no hypothesis beyond `Rᵀ R = 1`);
* `decLog_rot`: the same for the logarithm, the integral being entrywise
  (needs entrywise integrability of the integrand, supplied by `CovStanding`);
* `rootTrace_rot`: the diagonal trace over a set of unit points is unchanged;
* `rootTraceBg_rot`: `rootTraceBg (D.rot R) s = rootTraceBg D s` for a datum `D` of the chart and
  `|s_P| < e^κ`, using `decBg_rot`;
* `detActivityBg_rot`, `sum_detActivityBg_rot`, `detExpansionLocC_term_rot`: the activities, their
  sums over the unit blocks, and the terms of the landed determinant expansion.

The rotated datum `D.rot R` need not lie in the chart for these statements (complex `R`);
for real orthogonal `R` it does (`xiCData_rot`).  Class data and lattice symmetries are not
treated here (the lattice case is `DetSymmGroup`); the rotation clause of the class is NOT proved
here.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization Balaban.Analysis
  Balaban.SmallField Balaban.SmallField.Def6 Balaban.Localization.DecEquiv MeasureTheory
  Finset Matrix

/-! ### Matrix level -/

section MatrixLevel

variable {N : ℕ} {ι κι : Type*} [Fintype ι] [DecidableEq ι] [Fintype κι] [DecidableEq κι]

/-- `(1 ⊗ Rᵀ)(1 ⊗ R) = 1` for `Rᵀ R = 1`. -/
theorem rotLift_transpose_mul {R : Matrix (Fin N) (Fin N) ℂ} (hR : Rᵀ * R = 1) :
    (rotLift Rᵀ : Matrix (ι × Fin N) (ι × Fin N) ℂ) * rotLift R = 1 := by
  rw [rotLift_mul, hR, rotLift_one]

/-- `(1 ⊗ R)(1 ⊗ Rᵀ) = 1` for `Rᵀ R = 1`. -/
theorem rotLift_mul_transpose {R : Matrix (Fin N) (Fin N) ℂ} (hR : Rᵀ * R = 1) :
    (rotLift R : Matrix (ι × Fin N) (ι × Fin N) ℂ) * rotLift Rᵀ = 1 := by
  rw [rotLift_mul, mul_eq_one_comm.1 hR, rotLift_one]

/-- The lift `1 ⊗ R` is invertible with inverse `1 ⊗ Rᵀ`. -/
theorem isUnit_rotLift {R : Matrix (Fin N) (Fin N) ℂ} (hR : Rᵀ * R = 1) :
    IsUnit (rotLift R : Matrix (ι × Fin N) (ι × Fin N) ℂ) :=
  ⟨⟨rotLift R, rotLift Rᵀ, rotLift_mul_transpose hR, rotLift_transpose_mul hR⟩, rfl⟩

/-- A rectangular spin-scalar operator commutes with the lift. -/
theorem liftRect_mul_rotLift (Q : Matrix κι ι ℂ) (R : Matrix (Fin N) (Fin N) ℂ) :
    liftRect N Q * (rotLift R : Matrix (ι × Fin N) (ι × Fin N) ℂ) =
      (rotLift R : Matrix (κι × Fin N) (κι × Fin N) ℂ) * liftRect N Q := by
  ext p r
  simp only [mul_apply, liftRect, rotLift, Fintype.sum_prod_type]
  have e1 : ∑ y, ∑ j, (if p.2 = j then Q p.1 y else 0) * (if y = r.1 then R j r.2 else 0) =
      Q p.1 r.1 * R p.2 r.2 := by
    rw [Finset.sum_eq_single r.1]
    · rw [Finset.sum_eq_single p.2]
      · simp
      · intro j _ hj; simp [Ne.symm hj]
      · simp
    · intro y _ hy; simp [hy]
    · simp
  have e2 : ∑ y, ∑ j, (if p.1 = y then R p.2 j else 0) * (if j = r.2 then Q y r.1 else 0) =
      R p.2 r.2 * Q p.1 r.1 := by
    rw [Finset.sum_eq_single p.1]
    · rw [Finset.sum_eq_single r.2]
      · simp
      · intro j _ hj; simp [hj]
      · simp
    · intro y _ hy; simp [Ne.symm hy]
    · simp
  rw [e1, e2, mul_comm]

/-- The lift `1 ⊗ Rᵀ` commutes with a spin-scalar operator. -/
theorem rotLift_mul_liftOp (A : Matrix ι ι ℂ) (R : Matrix (Fin N) (Fin N) ℂ) :
    (rotLift R : Matrix (ι × Fin N) (ι × Fin N) ℂ) * liftOp N A = liftOp N A * rotLift R :=
  (liftOp_mul_rotLift A R).symm

/-- `A = (1 ⊗ R) A (1 ⊗ Rᵀ)` for a spin-scalar `A`. -/
theorem rotLift_conj_liftOp {R : Matrix (Fin N) (Fin N) ℂ} (hR : Rᵀ * R = 1) (A : Matrix ι ι ℂ) :
    (rotLift R : Matrix (ι × Fin N) (ι × Fin N) ℂ) * liftOp N A * rotLift Rᵀ = liftOp N A := by
  rw [rotLift_mul_liftOp, Matrix.mul_assoc, rotLift_mul_transpose hR, Matrix.mul_one]

/-- The operator `A(x)` built from a spin-scalar `P` commutes with the lift. -/
theorem covA_mul_rotLift (c b x : ℝ) (P : Matrix ι ι ℂ) (R : Matrix (Fin N) (Fin N) ℂ) :
    covA c b x (liftOp N P) * (rotLift R : Matrix (ι × Fin N) (ι × Fin N) ℂ) =
      rotLift R * covA c b x (liftOp N P) := by
  unfold covA
  rw [add_mul, mul_add, smul_mul_assoc, smul_mul_assoc, mul_smul_comm, mul_smul_comm,
    sub_mul, mul_sub, Matrix.one_mul, Matrix.mul_one, ← rotLift_mul_liftOp P R]

/-- `A(x) = (1 ⊗ R) A(x) (1 ⊗ Rᵀ)`. -/
theorem rotLift_conj_covA {R : Matrix (Fin N) (Fin N) ℂ} (hR : Rᵀ * R = 1) (c b x : ℝ)
    (P : Matrix ι ι ℂ) :
    (rotLift R : Matrix (ι × Fin N) (ι × Fin N) ℂ) * covA c b x (liftOp N P) * rotLift Rᵀ =
      covA c b x (liftOp N P) := by
  rw [← covA_mul_rotLift, Matrix.mul_assoc, rotLift_mul_transpose hR, Matrix.mul_one]

end MatrixLevel

/-! ### `M`, `N`, `Π`, `C_x` under the rotation of the field -/

section Forms

variable {N : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem commK_rot (H : Matrix ι ι ℂ) (R : Matrix (Fin N) (Fin N) ℂ) (φ : ι → Fin N → ℂ) :
    commK H (fun x => R *ᵥ φ x) = commK H φ * (rotLift Rᵀ : Matrix (ι × Fin N) (ι × Fin N) ℂ) := by
  unfold commK
  rw [fieldMul_rot, Matrix.transpose_mul, rotLift_transpose]
  have h := rotLift_mul_liftOp (N := N) H Rᵀ
  simp only [Matrix.sub_mul, Matrix.mul_assoc, h]

theorem constraintM_rot {R : Matrix (Fin N) (Fin N) ℂ} (hR : Rᵀ * R = 1) (H Gm : Matrix ι ι ℂ)
    (φ : ι → Fin N → ℂ) :
    constraintM H Gm (fun x => R *ᵥ φ x) = constraintM H Gm φ := by
  unfold constraintM
  rw [fieldMul_rot, commK_rot, Matrix.transpose_mul, rotLift_transpose]
  have h := rotLift_mul_liftOp (N := N) Gm Rᵀ
  have hrr : (rotLift Rᵀ : Matrix (ι × Fin N) (ι × Fin N) ℂ) *
      ((rotLift R : Matrix (ι × Fin N) (ι × Fin N) ℂ) * (fieldMul φ : Matrix (ι × Fin N) ι ℂ)) =
      (fieldMul φ : Matrix (ι × Fin N) ι ℂ) := by
    rw [← Matrix.mul_assoc, rotLift_transpose_mul hR, Matrix.one_mul]
  simp only [Matrix.mul_assoc, h, hrr]

theorem constraintN_rot (H Gm : Matrix ι ι ℂ) (R : Matrix (Fin N) (Fin N) ℂ)
    (φ : ι → Fin N → ℂ) :
    constraintN H Gm (fun x => R *ᵥ φ x) =
      constraintN H Gm φ * (rotLift Rᵀ : Matrix (ι × Fin N) (ι × Fin N) ℂ) := by
  unfold constraintN
  rw [fieldMul_rot, commK_rot, Matrix.transpose_mul, rotLift_transpose]
  have h := rotLift_mul_liftOp (N := N) Gm Rᵀ
  simp only [Matrix.sub_mul, Matrix.mul_assoc, h]

end Forms

/-! ### The decoupled covariance -/

section Cov

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
variable {G : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
variable {κι : Type*} [Fintype κι] [DecidableEq κι]

/-- The restriction to `Ω₁` commutes with the rotation of the field. -/
theorem restrictField_rot (R : Matrix (Fin N) (Fin N) ℂ)
    (φ : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) :
    restrictField G (rotSite R φ) = fun x => R *ᵥ restrictField G φ x := rfl

theorem decM_rot {R : Matrix (Fin N) (Fin N) ℂ} (hR : Rᵀ * R = 1) (a : ℕ → ℝ) (aT x ν : ℝ)
    (α : G.Ω 1 → ℂ) (s : ℕ × CTorus d L N₁ m₁ (k + 1) → ℂ)
    (φ : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) :
    decM G a aT x ν α s (rotSite R φ) = decM G a aT x ν α s φ := by
  unfold decM
  rw [restrictField_rot]
  exact constraintM_rot hR _ _ _

theorem decN_rot (R : Matrix (Fin N) (Fin N) ℂ) (a : ℕ → ℝ) (aT x ν : ℝ)
    (α : G.Ω 1 → ℂ) (s : ℕ × CTorus d L N₁ m₁ (k + 1) → ℂ)
    (φ : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) :
    decN G a aT x ν α s (rotSite R φ) =
      decN G a aT x ν α s φ * (rotLift Rᵀ : Matrix (G.Ω 1 × Fin N) (G.Ω 1 × Fin N) ℂ) := by
  unfold decN
  rw [restrictField_rot]
  exact constraintN_rot _ _ _ _

theorem decPi_rot {R : Matrix (Fin N) (Fin N) ℂ} (hR : Rᵀ * R = 1) (a : ℕ → ℝ) (aT x ν : ℝ)
    (α : G.Ω 1 → ℂ) (s : ℕ × CTorus d L N₁ m₁ (k + 1) → ℂ)
    (φ : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) :
    decPi G a aT x ν α s (rotSite R φ) =
      (rotLift R : Matrix (G.Ω 1 × Fin N) (G.Ω 1 × Fin N) ℂ) * decPi G a aT x ν α s φ *
        rotLift Rᵀ := by
  unfold decPi
  rw [decM_rot hR, decN_rot, restrictField_rot, fieldMul_rot]
  have h := rotLift_mul_liftOp (N := N) (Gsx G a aT x ν α s) R
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (liftOp N (Gsx G a aT x ν α s)), ← h]
  simp only [Matrix.mul_assoc]

/-- **Covariance of `C_x(s)` under spin rotations**: `C_x ↦ (1 ⊗ R) C_x (1 ⊗ Rᵀ)`. -/
theorem decCov_rot {R : Matrix (Fin N) (Fin N) ℂ} (hR : Rᵀ * R = 1) (a : ℕ → ℝ) (aT x ν : ℝ)
    (α : G.Ω 1 → ℂ) (s : ℕ × CTorus d L N₁ m₁ (k + 1) → ℂ)
    (φ : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) (Q : Matrix κι (G.Ω 1) ℂ) (P : Matrix κι κι ℂ) :
    decCov G a aT x ν α s (rotSite R φ) Q P =
      (rotLift R : Matrix (κι × Fin N) (κι × Fin N) ℂ) * decCov G a aT x ν α s φ Q P *
        rotLift Rᵀ := by
  unfold decCov
  rw [decPi_rot hR]
  set A := covA (a k) (aT / (L : ℝ) ^ 2) x (liftOp N P) with hA
  set LG := liftOp N (Gsx G a aT x ν α s) with hLG
  set Pi := decPi G a aT x ν α s φ with hPi
  set RK : Matrix (κι × Fin N) (κι × Fin N) ℂ := rotLift R with hRK
  set TK : Matrix (κι × Fin N) (κι × Fin N) ℂ := rotLift Rᵀ with hTK
  set RI : Matrix (G.Ω 1 × Fin N) (G.Ω 1 × Fin N) ℂ := rotLift R with hRI
  set TI : Matrix (G.Ω 1 × Fin N) (G.Ω 1 × Fin N) ℂ := rotLift Rᵀ with hTI
  have hAc : A * RK = RK * A := covA_mul_rotLift _ _ _ _ _
  have hAt : TK * A = A * TK := by
    have := covA_mul_rotLift (N := N) (a k) (aT / (L : ℝ) ^ 2) x P Rᵀ
    exact this.symm
  have hQ : liftRect N Q * RI = RK * liftRect N Q := liftRect_mul_rotLift Q R
  have hQt : TI * (liftRect N Q)ᵀ = (liftRect N Q)ᵀ * TK := by
    have := congrArg Matrix.transpose hQ
    rw [Matrix.transpose_mul, Matrix.transpose_mul, hRI, hRK, rotLift_transpose, rotLift_transpose] at this
    exact this
  have hLGc : LG * RI = RI * LG := (liftOp_mul_rotLift _ R)
  have hRT : RI * TI = 1 := rotLift_mul_transpose hR
  have hRT' : RK * TK = 1 := rotLift_mul_transpose hR
  have hTR' : TK * RK = 1 := rotLift_transpose_mul hR
  have hLG' : LG - RI * Pi * TI = RI * (LG - Pi) * TI := by
    have h1 : RI * LG * TI = LG := by
      rw [← hLGc, Matrix.mul_assoc, hRT, Matrix.mul_one]
    rw [Matrix.mul_sub, Matrix.sub_mul, h1]
  rw [hLG']
  have hAA : RK * A * TK = A := by
    rw [← hAc, Matrix.mul_assoc, hRT', Matrix.mul_one]
  have hmain : A * liftRect N Q * (RI * (LG - Pi) * TI) * (liftRect N Q)ᵀ * A =
      RK * (A * liftRect N Q * (LG - Pi) * (liftRect N Q)ᵀ * A) * TK := by
    calc A * liftRect N Q * (RI * (LG - Pi) * TI) * (liftRect N Q)ᵀ * A
        = A * (liftRect N Q * RI) * (LG - Pi) * (TI * (liftRect N Q)ᵀ) * A := by
          simp only [Matrix.mul_assoc]
      _ = A * (RK * liftRect N Q) * (LG - Pi) * ((liftRect N Q)ᵀ * TK) * A := by rw [hQ, hQt]
      _ = (A * RK) * liftRect N Q * (LG - Pi) * (liftRect N Q)ᵀ * (TK * A) := by
          simp only [Matrix.mul_assoc]
      _ = (RK * A) * liftRect N Q * (LG - Pi) * (liftRect N Q)ᵀ * (A * TK) := by
          rw [hAc, hAt]
      _ = _ := by simp only [Matrix.mul_assoc]
  rw [hmain, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, hAA]

end Cov

/-! ### The logarithm and the trace -/

section Log

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
variable {G : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
variable {κι : Type*} [Fintype κι] [DecidableEq κι]

/-- The entrywise integral commutes with a constant two-sided matrix factor, when the entries
are integrable. -/
theorem intMat_conj {ι : Type*} [Fintype ι] [DecidableEq ι] {μ : Measure ℝ}
    {F : ℝ → Matrix ι ι ℂ} (hint : ∀ p q, Integrable (fun x => F x p q) μ)
    (U V : Matrix ι ι ℂ) :
    intMat μ (fun x => U * F x * V) = U * intMat μ F * V := by
  ext p q
  unfold intMat
  simp only [Matrix.mul_apply]
  have h1 : ∀ a, Integrable (fun x => (∑ b, U p b * F x b a) * V a q) μ := fun a =>
    (integrable_finsetSum _ fun b _ => (hint b a).const_mul _).mul_const _
  rw [integral_finsetSum _ fun a _ => h1 a]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [integral_mul_const, integral_finsetSum _ fun b _ => (hint b a).const_mul _]
  simp only [integral_const_mul]
  rfl

theorem rotLift_conj_one {R : Matrix (Fin N) (Fin N) ℂ} (hR : Rᵀ * R = 1) :
    (rotLift R : Matrix (κι × Fin N) (κι × Fin N) ℂ) * 1 * rotLift Rᵀ = 1 := by
  rw [Matrix.mul_one, rotLift_mul_transpose hR]

/-- **Covariance of the logarithm `𝕃(s)` under spin rotations**:
`𝕃 ↦ (1 ⊗ R) 𝕃 (1 ⊗ Rᵀ)`.  The integral is entrywise; its entries are integrable under
`CovStanding`. -/
theorem decLog_rot {R : Matrix (Fin N) (Fin N) ℂ} (hR : Rᵀ * R = 1) {a : ℕ → ℝ} {aT ν : ℝ}
    {α : G.Ω 1 → ℂ} {κ : ℝ} {s : ℕ × CTorus d L N₁ m₁ (k + 1) → ℂ} {δ : ℝ}
    {φ : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ} {Q : Matrix κι (G.Ω 1) ℂ} {P : Matrix κι κι ℂ}
    (H : CovStanding G a aT ν α κ s δ φ Q P) :
    decLog G a aT ν α s (rotSite R φ) Q P =
      (rotLift R : Matrix (κι × Fin N) (κι × Fin N) ℂ) * decLog G a aT ν α s φ Q P *
        rotLift Rᵀ := by
  have hint := fun p q => integrable_decSub H p q
  have hfun : (fun x => decCov G a aT x ν α s (rotSite R φ) Q P -
        covA (a k) (aT / (L : ℝ) ^ 2) x (liftOp N P)) =
      fun x => (rotLift R : Matrix (κι × Fin N) (κι × Fin N) ℂ) *
        (decCov G a aT x ν α s φ Q P - covA (a k) (aT / (L : ℝ) ^ 2) x (liftOp N P)) *
          rotLift Rᵀ := by
    funext x
    rw [decCov_rot hR, Matrix.mul_sub, Matrix.sub_mul, rotLift_conj_covA hR]
  unfold decLog
  rw [hfun, intMat_conj hint]
  have hP := rotLift_conj_liftOp hR P (ι := κι)
  have h1 := rotLift_conj_one hR (κι := κι)
  simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul,
    Matrix.smul_mul, hP, h1]

theorem rotLift_mul_apply (R : Matrix (Fin N) (Fin N) ℂ) (M : Matrix (κι × Fin N) (κι × Fin N) ℂ)
    (y : κι) (i : Fin N) (q : κι × Fin N) :
    ((rotLift R : Matrix (κι × Fin N) (κι × Fin N) ℂ) * M) (y, i) q = ∑ j, R i j * M (y, j) q := by
  simp [Matrix.mul_apply, rotLift, Fintype.sum_prod_type]

theorem mul_rotLift_apply (S : Matrix (Fin N) (Fin N) ℂ) (M : Matrix (κι × Fin N) (κι × Fin N) ℂ)
    (p : κι × Fin N) (y : κι) (l : Fin N) :
    (M * (rotLift S : Matrix (κι × Fin N) (κι × Fin N) ℂ)) p (y, l) = ∑ j, M p (y, j) * S j l := by
  simp [Matrix.mul_apply, rotLift, Fintype.sum_prod_type]

/-- The diagonal trace of a block is unchanged by the conjugation `M ↦ (1 ⊗ R) M (1 ⊗ Rᵀ)`
(this uses `Rᵀ R = 1`). -/
theorem sum_diag_rotLift_conj {R : Matrix (Fin N) (Fin N) ℂ} (hR : Rᵀ * R = 1)
    (M : Matrix (κι × Fin N) (κι × Fin N) ℂ) (y : κι) :
    ∑ i : Fin N, (((rotLift R : Matrix (κι × Fin N) (κι × Fin N) ℂ) * M * rotLift Rᵀ :
        Matrix (κι × Fin N) (κι × Fin N) ℂ) (y, i) (y, i)) = ∑ i : Fin N, M (y, i) (y, i) := by
  have e : ∀ i : Fin N, (((rotLift R : Matrix (κι × Fin N) (κι × Fin N) ℂ) * M * rotLift Rᵀ :
      Matrix (κι × Fin N) (κι × Fin N) ℂ) (y, i) (y, i)) =
        ∑ j, ∑ l, R i j * R i l * M (y, j) (y, l) := by
    intro i
    rw [mul_rotLift_apply]
    simp only [rotLift_mul_apply, Finset.sum_mul, Matrix.transpose_apply]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
    ring
  simp only [e]
  have e3 : ∀ j, ∑ i, ∑ l, R i j * R i l * M (y, j) (y, l) = M (y, j) (y, j) := by
    intro j
    have e2 : ∑ i, ∑ l, R i j * R i l * M (y, j) (y, l) =
        ∑ l, (Rᵀ * R) j l * M (y, j) (y, l) := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun l _ => ?_
      simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
    rw [e2, hR]
    simp [Matrix.one_apply]
  calc ∑ i, ∑ j, ∑ l, R i j * R i l * M (y, j) (y, l)
      = ∑ j, ∑ i, ∑ l, R i j * R i l * M (y, j) (y, l) := Finset.sum_comm
    _ = ∑ j, M (y, j) (y, j) := Finset.sum_congr rfl fun j _ => e3 j

/-- **The root trace is invariant under a spin rotation of the field.** -/
theorem rootTrace_rot {R : Matrix (Fin N) (Fin N) ℂ} (hR : Rᵀ * R = 1) {a : ℕ → ℝ} {aT ν : ℝ}
    {α : G.Ω 1 → ℂ} {κ : ℝ} {s : DecParams G} {δ : ℝ}
    {φ : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ} {Q : Matrix κι (G.Ω 1) ℂ} {P : Matrix κι κι ℂ}
    (H : CovStanding G a aT ν α κ (extS G s) δ φ Q P) (B : Finset κι) :
    rootTrace G a aT ν Q P B s (rotSite R φ) α = rootTrace G a aT ν Q P B s φ α := by
  unfold rootTrace
  rw [decLog_rot hR H]
  congr 1
  exact Finset.sum_congr rfl fun y _ => sum_diag_rotLift_conj hR _ y

end Log

/-! ### The chart: root trace and activities of a rotated datum -/

section Chart

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱm : ℝ} {m₀ : ℕ}
variable {Gp : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
  {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}
variable {a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁ : ℝ}
variable {κι : Type*} [Fintype κι] [DecidableEq κι]

/-- The extension of a field by the datum commutes with the rotation. -/
theorem barField_rot (R : Matrix (Fin N) (Fin N) ℂ) (D : BgData Gp N)
    (φ : Gp.Ω 1 × Fin N → ℂ) :
    barField Gp (D.rot R).Ψ (rotFld R φ) = rotSite R (barField Gp D.Ψ φ) := by
  funext x i
  classical
  unfold barField
  by_cases h : x ∈ Gp.Ω 1
  · simp only [h, ↓reduceDIte, rotSite_apply, rotFld]
  · simp only [h, ↓reduceDIte, rotSite_apply]
    rfl

variable (hC : FlCore N Gp Hm a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁) (hk : 1 ≤ k) {δc : ℝ}
  (hδc : 0 ≤ δc) (hcap : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
  (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
  (hmar : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
  (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)

include hC hk hδc hcap hsm hmar hα in
/-- **T2. The rooted trace at the decoupled background is invariant under a spin rotation of the
datum**: for `Rᵀ R = 1`, a datum `D` of the chart `Ξ^c(𝔹_{k+1}; 1, ε)` and cut parameters with
`|s_P| < e^κ`,
`rootTraceBg B (D.rot R) s = rootTraceBg B D s`.  The rotated datum need not be in the chart. -/
theorem rootTraceBg_rot {R : Matrix (Fin N) (Fin N) ℂ} (hR : Rᵀ * R = 1)
    {Q : Matrix κι (Gp.Ω 1) ℂ} {P : Matrix κι κι ℂ} (hU : IsUnitLattice Gp Q P) (B : Finset κι)
    {D : BgData Gp N} (hD : XiCData Gp (compWeight L a₁) ν (k + 1) 1 eps D)
    {s : DecParams Gp} (hs : ∀ P, ‖s P‖ < Real.exp κ) :
    rootTraceBg Gp (compWeight L a₁) a₁ ν (rho4 d L N BG κ) Q P B (D.rot R) s =
      rootTraceBg Gp (compWeight L a₁) a₁ ν (rho4 d L N BG κ) Q P B D s := by
  have hmem := mem_decDom_rootTraceBg hC hs hD hmar hα
  have H := covStanding_of_mem (xSetting_of_flCore hC hk) hC.hκ.le hcap hδc hsm hU hmem
  obtain ⟨h1, h2⟩ := decBg_rot hR (G := Gp) (a := compWeight L a₁) (ν := ν)
    (rho4 d L N BG κ) s D
  unfold rootTraceBg
  rw [h1, h2, barField_rot]
  exact rootTrace_rot hR H B

include hC hk hδc hcap hsm hmar hα in
open Classical in
/-- **T3. The determinant activity at the decoupled background is invariant under a spin
rotation of the datum**: `detActivityBg (D.rot R) y Y = detActivityBg D y Y` for `Rᵀ R = 1` and
`D` in the chart.  The mixed differences `Δ_J` evaluate `rootTraceBg` only at the cut values
`cutPt I ∈ {0, 1}^{cubeIdx}`, which satisfy `|s_P| < e^κ` since `κ > 0`. -/
theorem detActivityBg_rot {R : Matrix (Fin N) (Fin N) ℂ} (hR : Rᵀ * R = 1)
    {D : BgData Gp N} (hD : XiCData Gp (compWeight L a₁) ν (k + 1) 1 eps D) (y : unitPts Gp)
    (Y : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) m₀ (k + 1)
      Set.univ)) :
    detActivityBg m₀ (compWeight L a₁) a₁ ν (rho4 d L N BG κ) (D.rot R) y Y =
      detActivityBg m₀ (compWeight L a₁) a₁ ν (rho4 d L N BG κ) D y Y := by
  have hκ : 0 < κ := hC.hκ
  have hcut : ∀ I : Finset (cubeIdx Gp), ∀ P, ‖cutPt I P‖ < Real.exp κ := by
    intro I P
    unfold cutPt
    split_ifs
    · simpa using Real.one_lt_exp_iff.2 hκ
    · simpa using Real.exp_pos κ
  unfold detActivityBg mixDiff
  refine Finset.sum_congr rfl fun J _ => Finset.sum_congr rfl fun I _ => ?_
  rw [rootTraceBg_rot hC hk hδc hcap hsm hmar hα hR (isUnitLatticeB_unit (G := Gp)).toIsUnitLattice
    ({y} : Finset (unitPts Gp)) hD (hcut I)]

end Chart

section Record

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ ϱm : ℝ} {m₀ : ℕ}
variable (S : StepSetting d L N₁ m₁ k N ϱ)
  {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}
  {c BG κ eps Kc Cx c₂ BG₂ δ₁ δc : ℝ}

open Classical in
/-- **T3. The terms of the localized determinant family are invariant under a spin rotation of
the datum.**  Under the hypotheses of `exists_detExpansionLocC_of_chart` and for `Rᵀ R = 1`
there is a record `E` whose terms are the sums of the activities over the unit blocks
(as in `exists_detExpansionLocC_of_chart`) and satisfy `E.term (D.rot R) T = E.term D T` for every
datum `D` of the chart `Ξ^c(𝔹_{k+1}; 1, eps)` and every set `T` of cubes. -/
theorem exists_detExpansionLocC_rot
    (hC : FlCore N S.G' Hm S.a₁ S.ν c BG κ eps Kc Cx c₂ BG₂ δ₁) (hδc : 0 ≤ δc)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    (hdm : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4) (hconn : HatConn S.G') (hN : L ^ m₀ ∣ N₁)
    (hz : ((detDeg d L + 1 : ℕ) : ℝ) ^ 2 * (2 / Real.exp κ) < 1)
    (z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))))
    {R : Matrix (Fin N) (Fin N) ℂ} (hR : Rᵀ * R = 1) :
    ∃ E : DetExpansionLocC S m₀ z eps
        ((κ - Real.log 2 - 2 * Real.log ((detDeg d L + 1 : ℕ) : ℝ)) / (2 * d * L))
        ((L : ℝ) ^ d * ((1 / 2 : ℝ) * N * covBLog d L (S.a k) (S.a₁ / (L : ℝ) ^ 2) κ /
          (1 - ((detDeg d L + 1 : ℕ) : ℝ) ^ 2 * (2 / Real.exp κ)))),
      (∀ D T, E.term D T =
        ∑ y ∈ S.blockU z, detActivityBg m₀ S.a S.a₁ S.ν (rho4 d L N BG κ) D y T) ∧
      ∀ D : BgData S.G' N, XiCData S.G' S.a S.ν (k + 1) 1 eps D →
        ∀ T, E.term (D.rot R) T = E.term D T := by
  obtain ⟨E, hE⟩ := exists_detExpansionLocC_of_chart S hC hδc hMX hdm hα hsm hconn hN hz z
  refine ⟨E, hE, fun D hD T => ?_⟩
  rw [hE, hE]
  exact Finset.sum_congr rfl fun y _ =>
    detActivityBg_rot hC S.hk1 hδc hMX hsm hdm hα hR hD y T

open Classical in
/-- **T3, real orthogonal rotations.**  For `Qᵀ Q = 1` with `Q` real, the rotation `cmat Q` maps
the data of the chart to data of the chart (`xiCData_rot`), and the terms of the record are
invariant. -/
theorem exists_detExpansionLocC_rot_real
    (hC : FlCore N S.G' Hm S.a₁ S.ν c BG κ eps Kc Cx c₂ BG₂ δ₁) (hδc : 0 ≤ δc)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    (hdm : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4) (hconn : HatConn S.G') (hN : L ^ m₀ ∣ N₁)
    (hz : ((detDeg d L + 1 : ℕ) : ℝ) ^ 2 * (2 / Real.exp κ) < 1)
    (z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))))
    {Q : Matrix (Fin N) (Fin N) ℝ} (hQ : Qᵀ * Q = 1) :
    ∃ E : DetExpansionLocC S m₀ z eps
        ((κ - Real.log 2 - 2 * Real.log ((detDeg d L + 1 : ℕ) : ℝ)) / (2 * d * L))
        ((L : ℝ) ^ d * ((1 / 2 : ℝ) * N * covBLog d L (S.a k) (S.a₁ / (L : ℝ) ^ 2) κ /
          (1 - ((detDeg d L + 1 : ℕ) : ℝ) ^ 2 * (2 / Real.exp κ)))),
      (∀ D : BgData S.G' N, XiCData S.G' S.a S.ν (k + 1) 1 eps D →
        XiCData S.G' S.a S.ν (k + 1) 1 eps (D.rot (cmat Q))) ∧
      ∀ D : BgData S.G' N, XiCData S.G' S.a S.ν (k + 1) 1 eps D →
        ∀ T, E.term (D.rot (cmat Q)) T = E.term D T := by
  obtain ⟨E, -, hE⟩ := exists_detExpansionLocC_rot S hC hδc hMX hdm hα hsm hconn hN hz z
    (R := cmat Q) (isRealOrth_ofReal hQ).1
  exact ⟨E, fun D hD => xiCData_rot hQ hD, hE⟩

end Record

end Balaban.Fluctuation
