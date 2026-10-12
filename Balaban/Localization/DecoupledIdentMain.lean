/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.DecoupledLimit
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

/-!
# I-4c (iv): the decoupled covariance at `s = 1` is `(x + 𝒜)⁻¹`

`decCov_one_eq`: for `s ≡ 1` and every `x ≥ 0`,

`C_x(1) = (x + 𝒜)⁻¹`,  `𝒜 = a_k + b P - a_k² L^{-2k} Q (G_D - Π_D) Q*`  (`covOp`),

with `G_D = H₀⁻¹`, `Π_D = G_D φ₀ [φ₀ · G_D φ₀]⁻¹ φ₀ · G_D` the constrained operator of GREEN.md
(1.8') for the Dirichlet operator `H₀` of `𝔹_k` (`xH0`), i.e. `𝒜 = a L⁻² Q*Q + Δ^{(k)}`. The
operator `𝒜` does not depend on `x`.
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background Finset Matrix

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}

section Main

variable {G : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ} {a : ℕ → ℝ} {aT ν : ℝ}
  {α : G.Ω 1 → ℂ} {δ : ℝ} {φ : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ}
  {κι : Type*} [Fintype κι] [DecidableEq κι] {Q : Matrix κι (G.Ω 1) ℂ} {P : Matrix κι κι ℂ}

variable (G a aT ν α φ Q P) in
/-- **The operator `𝒜 = a L⁻² Q*Q + Δ^{(k)}`** with the constrained
`Δ^{(k)} = a_k - a_k² L^{-2k} Q (G_D - Π_D) Q*` (GREEN.md (1.8')). -/
noncomputable def covOp : Matrix (κι × Fin N) (κι × Fin N) ℂ :=
  ((a k : ℝ) : ℂ) • (1 : Matrix (κι × Fin N) (κι × Fin N) ℂ) +
      ((aT / (L : ℝ) ^ 2 : ℝ) : ℂ) • liftOp N P -
    (((a k) ^ 2 / (L : ℝ) ^ (2 * k) : ℝ) : ℂ) •
      (liftRect N Q * (liftOp N (xH0 G a ν α)⁻¹ - constrainedOp (xH0 G a ν α)⁻¹ (restrictField G φ)) *
        (liftRect N Q)ᵀ)

end Main

section Helpers

omit [NeZero N₁] [NeZero L] in
theorem liftOp_inv_of_isUnit {ι : Type*} [Fintype ι] [DecidableEq ι] {A : Matrix ι ι ℂ}
    (hA : IsUnit A) : (liftOp N A)⁻¹ = liftOp N A⁻¹ := by
  have h : A * A⁻¹ = 1 := Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hA)
  refine Matrix.inv_eq_right_inv ?_
  rw [← liftOp_mul, h, liftOp_one]

omit [NeZero N₁] [NeZero L] in
theorem isUnit_liftOp {ι : Type*} [Fintype ι] [DecidableEq ι] {A : Matrix ι ι ℂ}
    (hA : IsUnit A) : IsUnit (liftOp N A) := by
  have h : A * A⁻¹ = 1 := Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hA)
  rw [Matrix.isUnit_iff_isUnit_det]
  refine Matrix.isUnit_det_of_right_inverse (B := liftOp N A⁻¹) ?_
  rw [← liftOp_mul, h, liftOp_one]

/-- `L^k` squared, positive. -/
theorem L2k_pos : (0 : ℝ) < ((L : ℝ) ^ k) ^ 2 := by
  have : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  positivity

omit [NeZero L] in
theorem L2k_eq : ((L : ℝ) ^ k) ^ 2 = (L : ℝ) ^ (2 * k) := by
  rw [← pow_mul, mul_comm]

end Helpers

section BlockOp

variable {G : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ} {a : ℕ → ℝ} {aT ν : ℝ}
  {α : G.Ω 1 → ℂ} {κι : Type*} [Fintype κι] [DecidableEq κι] {Q : Matrix κι (G.Ω 1) ℂ}
  {P : Matrix κι κι ℂ}

variable (a aT P) in
/-- The unit-lattice matrix `T = (c + x') + b' P` of `xOperator_blocks`, in units `L^{-2k}`. -/
noncomputable def covT (x : ℝ) : Matrix (κι × Fin N) (κι × Fin N) ℂ :=
  (((a k / ((L : ℝ) ^ k) ^ 2 : ℝ) : ℂ) + ((x / ((L : ℝ) ^ k) ^ 2 : ℝ) : ℂ)) •
      (1 : Matrix (κι × Fin N) (κι × Fin N) ℂ) +
    (((aT / (L : ℝ) ^ 2) / ((L : ℝ) ^ k) ^ 2 : ℝ) : ℂ) • liftOp N P

omit [Fintype κι] in
theorem covT_eq (x : ℝ) :
    covT (N := N) (L := L) (k := k) a aT P x = (((L : ℝ) ^ k) ^ 2 : ℂ)⁻¹ •
      (((a k : ℝ) + x : ℝ) : ℂ) • (1 : Matrix (κι × Fin N) (κι × Fin N) ℂ) +
      (((L : ℝ) ^ k) ^ 2 : ℂ)⁻¹ • ((aT / (L : ℝ) ^ 2 : ℝ) : ℂ) • liftOp N P := by
  unfold covT
  have hL : (((L : ℝ) ^ k) ^ 2 : ℝ) ≠ 0 := (L2k_pos (L := L) (k := k)).ne'
  have hL' : ((((L : ℝ) ^ k) ^ 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hL
  push_cast at hL' ⊢
  module

theorem covT_mul_covA {x : ℝ} (hcx : 0 < a k + x) (hb : 0 ≤ aT / (L : ℝ) ^ 2)
    (hi : liftOp N P * liftOp N P = liftOp N P) :
    covT (N := N) (L := L) (k := k) a aT P x *
      ((((L : ℝ) ^ k) ^ 2 : ℂ) • covA (a k) (aT / (L : ℝ) ^ 2) x (liftOp N P)) = 1 := by
  have h := covA_mul_T hcx hb hi
  have hL : (((L : ℝ) ^ k) ^ 2 : ℂ) ≠ 0 := by
    have := (L2k_pos (L := L) (k := k)).ne'
    exact_mod_cast this
  have e : (((L : ℝ) ^ k) ^ 2 : ℂ)⁻¹ • (((a k + x : ℝ) : ℂ) • (1 : Matrix (κι × Fin N) (κι × Fin N) ℂ)) +
      (((L : ℝ) ^ k) ^ 2 : ℂ)⁻¹ • ((aT / (L : ℝ) ^ 2 : ℝ) : ℂ) • liftOp N P =
      (((L : ℝ) ^ k) ^ 2 : ℂ)⁻¹ • ((((a k : ℝ) : ℂ) + x) • (1 : Matrix (κι × Fin N) (κι × Fin N) ℂ) +
        ((aT / (L : ℝ) ^ 2 : ℝ) : ℂ) • liftOp N P) := by
    push_cast; module
  rw [covT_eq, e, Matrix.smul_mul, Matrix.mul_smul, h, smul_smul, inv_mul_cancel₀ hL, one_smul]


omit [NeZero N₁] [NeZero L] in
theorem coeff_xS1 {ak x L2 : ℝ} (hcx : 0 < ak + x) (hL2 : 0 < L2) :
    (((ak / L2 : ℝ) : ℂ) * ((x / L2 : ℝ) : ℂ)) / (((ak / L2 : ℝ) : ℂ) + ((x / L2 : ℝ) : ℂ)) =
      ((xS1 ak x / L2 : ℝ) : ℂ) := by
  unfold xS1
  have h3 : ((ak : ℂ) + x) ≠ 0 := by exact_mod_cast hcx.ne'
  have hL : (L2 : ℂ) ≠ 0 := by exact_mod_cast hL2.ne'
  push_cast
  field_simp

omit [NeZero N₁] [NeZero L] in
theorem coeff_xS2 {ak x b L2 : ℝ} (hcx : 0 < ak + x) (hb : 0 ≤ b) (hL2 : 0 < L2) :
    (((ak / L2 : ℝ) : ℂ) * (((x / L2 : ℝ) : ℂ) + ((b / L2 : ℝ) : ℂ))) /
        (((ak / L2 : ℝ) : ℂ) + ((x / L2 : ℝ) : ℂ) + ((b / L2 : ℝ) : ℂ)) -
      (((ak / L2 : ℝ) : ℂ) * ((x / L2 : ℝ) : ℂ)) / (((ak / L2 : ℝ) : ℂ) + ((x / L2 : ℝ) : ℂ)) =
      (((xS2 ak b x - xS1 ak x) / L2 : ℝ) : ℂ) := by
  unfold xS1 xS2
  have h3 : ((ak : ℂ) + x) ≠ 0 := by exact_mod_cast hcx.ne'
  have h4 : ((ak : ℂ) + x + b) ≠ 0 := by
    have : 0 < ak + x + b := by linarith
    exact_mod_cast this.ne'
  have hL : (L2 : ℂ) ≠ 0 := by exact_mod_cast hL2.ne'
  push_cast
  field_simp

theorem xOperator_covT (hU : IsUnitLatticeB G Q P) {x : ℝ} (hx : 0 ≤ x) (hak : 0 < a k)
    (hb : 0 ≤ aT / (L : ℝ) ^ 2) :
    xOperator (liftOp N (xHt G a ν α)) (liftRect N Q) ((a k / ((L : ℝ) ^ k) ^ 2 : ℝ) : ℂ)
        (covT (N := N) (L := L) (k := k) a aT P x) =
      liftOp N (xDirichletOperator G a aT x ν α) := by
  have hL2p : (0 : ℝ) < ((L : ℝ) ^ k) ^ 2 := L2k_pos
  have hcx : 0 < a k + x := by linarith
  have hPP : liftOp N P * liftOp N P = liftOp N P := by rw [← liftOp_mul, hU.idem]
  have h1 : ((a k / ((L : ℝ) ^ k) ^ 2 : ℝ) : ℂ) + ((x / ((L : ℝ) ^ k) ^ 2 : ℝ) : ℂ) ≠ 0 := by
    rw [← Complex.ofReal_add, ← add_div]
    exact_mod_cast (div_pos hcx hL2p).ne'
  have h2 : ((a k / ((L : ℝ) ^ k) ^ 2 : ℝ) : ℂ) + ((x / ((L : ℝ) ^ k) ^ 2 : ℝ) : ℂ) +
      (((aT / (L : ℝ) ^ 2) / ((L : ℝ) ^ k) ^ 2 : ℝ) : ℂ) ≠ 0 := by
    rw [← Complex.ofReal_add, ← Complex.ofReal_add, ← add_div, ← add_div]
    have : 0 < a k + x + aT / (L : ℝ) ^ 2 := by linarith
    exact_mod_cast (div_pos this hL2p).ne'
  have hblocks := xOperator_blocks ((a k / ((L : ℝ) ^ k) ^ 2 : ℝ) : ℂ)
    ((x / ((L : ℝ) ^ k) ^ 2 : ℝ) : ℂ) (((aT / (L : ℝ) ^ 2) / ((L : ℝ) ^ k) ^ 2 : ℝ) : ℂ)
    (liftRect N Q) (liftOp N P) hPP h1 h2
    (liftOp N (xHt G a ν α)) (liftOp N (Pk G)) (liftOp N (Pk1 G)) hU.blk1v hU.blk2v
  unfold covT
  rw [hblocks, xDirichlet_eq_blocks, coeff_xS2 hcx hb hL2p, coeff_xS1 hcx hL2p]
  show _ = liftRect N _
  rw [liftRect_add, liftRect_add, liftRect_smul, liftRect_smul]
  rfl

end BlockOp

section Assembly

variable {G : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ} {a : ℕ → ℝ} {aT ν : ℝ}
  {α : G.Ω 1 → ℂ} {δ : ℝ} {φ : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ}
  {κι : Type*} [Fintype κι] [DecidableEq κι] {Q : Matrix κι (G.Ω 1) ℂ} {P : Matrix κι κι ℂ}

theorem liftOp_add' {ι : Type*} (A B : Matrix ι ι ℂ) :
    liftOp N (A + B) = liftOp N A + liftOp N B := liftRect_add A B

theorem liftOp_smul' {ι : Type*} (c : ℂ) (A : Matrix ι ι ℂ) :
    liftOp N (c • A) = c • liftOp N A := liftRect_smul c A

/-- The product identity at `s ≡ 1`, in the units of the landed reduction. -/
theorem decCov_one_prod (hfam : ∀ x, 0 ≤ x → XData G a aT ν x α 0 (fun _ => 1))
    (hφ : IsConstraintField G δ φ) (hδ : 0 ≤ δ) (hsm : δ ^ 2 * smallConstX d L 0 ≤ 1 / 4)
    (hU : IsUnitLatticeB G Q P) {x : ℝ} (hx : 0 ≤ x) :
      (covT (N := N) (L := L) (k := k) a aT P x -
          ((a k / ((L : ℝ) ^ k) ^ 2 : ℝ) : ℂ) ^ 2 •
            (liftRect N Q * (liftOp N (xH0 G a ν α)⁻¹ - constrainedOp (xH0 G a ν α)⁻¹ (restrictField G φ)) *
              (liftRect N Q)ᵀ)) *
        ((covT (N := N) (L := L) (k := k) a aT P x)⁻¹ +
          ((a k / ((L : ℝ) ^ k) ^ 2 : ℝ) : ℂ) ^ 2 •
            ((covT (N := N) (L := L) (k := k) a aT P x)⁻¹ * liftRect N Q *
              (liftOp N (xDirichletOperator G a aT x ν α)⁻¹ -
                constrainedOp (xDirichletOperator G a aT x ν α)⁻¹ (restrictField G φ)) *
              (liftRect N Q)ᵀ * (covT (N := N) (L := L) (k := k) a aT P x)⁻¹)) = 1 := by
  classical
  have D := hfam x hx
  have hak : 0 < a k := by
    have := D.st.ha k D.st.hk le_rfl
    linarith [this.1]
  have hb : 0 ≤ aT / (L : ℝ) ^ 2 := by
    have := D.st.haT1
    positivity
  have hcx : 0 < a k + x := by linarith
  set φ' := restrictField G φ with hφ'
  set B : Matrix (G.Ω 1) (G.Ω 1 × Fin N) ℂ := (fieldMul φ')ᵀ with hB
  obtain ⟨n, E, hE⟩ := exists_kernelEmbedding B
  have hPP : liftOp N P * liftOp N P = liftOp N P := by rw [← liftOp_mul, hU.idem]
  -- T
  have hTmul := covT_mul_covA (N := N) (L := L) (k := k) (a := a) (aT := aT) (P := P) hcx hb hPP
  have hTunit : IsUnit (covT (N := N) (L := L) (k := k) a aT P x) :=
    (Matrix.isUnit_iff_isUnit_det _).2 (Matrix.isUnit_det_of_right_inverse hTmul)
  -- the operator
  have hOp := xOperator_covT (N := N) (ν := ν) (α := α) hU hx hak hb
  set Hx := xDirichletOperator G a aT x ν α with hHx
  have hHxU : IsUnit Hx := xDirichlet_isUnit D.st D.pot hx
  have hHxG : Hx * Hx⁻¹ = 1 := Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hHxU)
  have hGxH : Hx⁻¹ * Hx = 1 := Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 hHxU)
  have hOpU : IsUnit (xOperator (liftOp N (xHt G a ν α)) (liftRect N Q)
      ((a k / ((L : ℝ) ^ k) ^ 2 : ℝ) : ℂ) (covT (N := N) (L := L) (k := k) a aT P x)) := by
    rw [hOp]; exact isUnit_liftOp hHxU
  have hGreen : xGreen (liftOp N (xHt G a ν α)) (liftRect N Q) ((a k / ((L : ℝ) ^ k) ^ 2 : ℝ) : ℂ)
      (covT (N := N) (L := L) (k := k) a aT P x) = liftOp N Hx⁻¹ := by
    unfold xGreen; rw [hOp, liftOp_inv_of_isUnit hHxU]
  have hMx : IsUnit (constraintM Hx Hx⁻¹ φ') := by
    have := decM_isUnit D hφ hδ hsm
    rwa [decM_one_eq hfam hx] at this
  have hS : IsUnit (B * xGreen (liftOp N (xHt G a ν α)) (liftRect N Q)
      ((a k / ((L : ℝ) ^ k) ^ 2 : ℝ) : ℂ) (covT (N := N) (L := L) (k := k) a aT P x) * Bᵀ) := by
    rw [hGreen]
    have : B * liftOp N Hx⁻¹ * Bᵀ = constraintForm Hx⁻¹ φ' := by
      rw [hB, Matrix.transpose_transpose]; rfl
    rw [this, constraintForm_eq_mul hHxG hGxH]
    exact (Matrix.isUnit_nonsing_inv_iff.2 hHxU).mul hMx
  -- the Dirichlet operator H₀
  have hH0U := xH0_isUnit hfam
  have hG0H : (xH0 G a ν α)⁻¹ * xH0 G a ν α = 1 :=
    Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 hH0U)
  have hH0G : xH0 G a ν α * (xH0 G a ν α)⁻¹ = 1 :=
    Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hH0U)
  have hM0 := xM0_isUnit hfam hφ hδ hsm
  have hGH0 : liftOp N (xH0 G a ν α)⁻¹ * liftOp N (xH0 G a ν α) = 1 := by
    rw [← liftOp_mul, hG0H, liftOp_one]
  have hS0 : IsUnit (B * liftOp N (xH0 G a ν α)⁻¹ * Bᵀ) := by
    have : B * liftOp N (xH0 G a ν α)⁻¹ * Bᵀ = constraintForm (xH0 G a ν α)⁻¹ φ' := by
      rw [hB, Matrix.transpose_transpose]; rfl
    rw [this, constraintForm_eq_mul hH0G hG0H]
    exact (Matrix.isUnit_nonsing_inv_iff.2 hH0U).mul hM0
  obtain ⟨hX, hEq0⟩ := constrained_green_eq (liftOp N (xH0 G a ν α)⁻¹) (liftOp N (xH0 G a ν α))
    hGH0 B E hE hS0
  have hHt : liftOp N (xHt G a ν α) +
      ((a k / ((L : ℝ) ^ k) ^ 2 : ℝ) : ℂ) • ((liftRect N Q)ᵀ * liftRect N Q) =
      liftOp N (xH0 G a ν α) := by
    rw [hU.blk1v]; unfold xH0; rw [liftOp_add', liftOp_smul']
  have hprod := xVariant_constrained_mul ((a k / ((L : ℝ) ^ k) ^ 2 : ℝ) : ℂ) (liftRect N Q)
    (liftOp N (xHt G a ν α)) (covT (N := N) (L := L) (k := k) a aT P x) hTunit B E hE
    (by rw [hHt]; exact hX) hOpU hS
  rw [hHt, hEq0, hGreen] at hprod
  have e1 : constraintPi (liftOp N (xH0 G a ν α)⁻¹) B =
      constrainedOp (xH0 G a ν α)⁻¹ (restrictField G φ) :=
    (constrainedOp_eq_constraintPi _ _).symm
  have e2 : constraintPi (liftOp N Hx⁻¹) B = constrainedOp Hx⁻¹ (restrictField G φ) :=
    (constrainedOp_eq_constraintPi _ _).symm
  rw [e1, e2] at hprod
  exact hprod

/-- **I-4c (iv), algebraic form**: `(x + 𝒜) C_x(1) = 1`. -/
theorem decCov_one_mul (hfam : ∀ x, 0 ≤ x → XData G a aT ν x α 0 (fun _ => 1))
    (hφ : IsConstraintField G δ φ) (hδ : 0 ≤ δ) (hsm : δ ^ 2 * smallConstX d L 0 ≤ 1 / 4)
    (hU : IsUnitLatticeB G Q P) {x : ℝ} (hx : 0 ≤ x) :
    ((x : ℂ) • (1 : Matrix (κι × Fin N) (κι × Fin N) ℂ) + covOp G a aT ν α φ Q P) *
      decCov G a aT x ν α (fun _ => 1) φ Q P = 1 := by
  have hprod := decCov_one_prod hfam hφ hδ hsm hU hx
  have D := hfam x hx
  have hak : 0 < a k := by
    have := D.st.ha k D.st.hk le_rfl
    linarith [this.1]
  have hb : 0 ≤ aT / (L : ℝ) ^ 2 := by
    have := D.st.haT1
    positivity
  have hcx : 0 < a k + x := by linarith
  have hPP : liftOp N P * liftOp N P = liftOp N P := by rw [← liftOp_mul, hU.idem]
  have hTmul := covT_mul_covA (N := N) (L := L) (k := k) (a := a) (aT := aT) (P := P) hcx hb hPP
  have hTinv : (covT (N := N) (L := L) (k := k) a aT P x)⁻¹ =
      (((L : ℝ) ^ k) ^ 2 : ℂ) • covA (a k) (aT / (L : ℝ) ^ 2) x (liftOp N P) :=
    Matrix.inv_eq_right_inv hTmul
  set Hx := xDirichletOperator G a aT x ν α with hHx
  have hHxU : IsUnit Hx := xDirichlet_isUnit D.st D.pot hx
  have hHxG : Hx * Hx⁻¹ = 1 := Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hHxU)
  have hGxH : Hx⁻¹ * Hx = 1 := Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 hHxU)
  have hGs : Gsx G a aT x ν α (fun _ => 1) = Hx⁻¹ := Gsx_one D.st D.pot hx D.isUnit_one_sub
  have hPi : decPi G a aT x ν α (fun _ => 1) φ = constrainedOp Hx⁻¹ (restrictField G φ) := by
    rw [constrainedOp_eq hHxG hGxH]
    unfold decPi decM decN
    rw [hGs]
  have hdec : decCov G a aT x ν α (fun _ => 1) φ Q P =
      covA (a k) (aT / (L : ℝ) ^ 2) x (liftOp N P) +
        (((a k) ^ 2 / (L : ℝ) ^ (2 * k) : ℝ) : ℂ) •
          (covA (a k) (aT / (L : ℝ) ^ 2) x (liftOp N P) * liftRect N Q *
            (liftOp N Hx⁻¹ - constrainedOp Hx⁻¹ (restrictField G φ)) * (liftRect N Q)ᵀ *
            covA (a k) (aT / (L : ℝ) ^ 2) x (liftOp N P)) := by
    unfold decCov
    rw [hGs, hPi]
  rw [hTinv] at hprod
  rw [hdec]
  have hL2 : (0 : ℝ) < ((L : ℝ) ^ k) ^ 2 := L2k_pos
  have hL2c : ((((L : ℝ) ^ k) ^ 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hL2.ne'
  have hc2 : ((a k / ((L : ℝ) ^ k) ^ 2 : ℝ) : ℂ) ^ 2 =
      ((((L : ℝ) ^ k) ^ 2 : ℝ) : ℂ)⁻¹ * (((a k) ^ 2 / (L : ℝ) ^ (2 * k) : ℝ) : ℂ) := by
    rw [← L2k_eq]; push_cast; field_simp
  have hc3 : ((a k / ((L : ℝ) ^ k) ^ 2 : ℝ) : ℂ) ^ 2 * ((((L : ℝ) ^ k) ^ 2 : ℝ) : ℂ) *
      ((((L : ℝ) ^ k) ^ 2 : ℝ) : ℂ) =
      ((((L : ℝ) ^ k) ^ 2 : ℝ) : ℂ) * (((a k) ^ 2 / (L : ℝ) ^ (2 * k) : ℝ) : ℂ) := by
    rw [hc2]; field_simp
  have hL : covT (N := N) (L := L) (k := k) a aT P x -
      ((a k / ((L : ℝ) ^ k) ^ 2 : ℝ) : ℂ) ^ 2 •
        (liftRect N Q * (liftOp N (xH0 G a ν α)⁻¹ - constrainedOp (xH0 G a ν α)⁻¹
          (restrictField G φ)) * (liftRect N Q)ᵀ) =
      ((((L : ℝ) ^ k) ^ 2 : ℝ) : ℂ)⁻¹ •
        ((x : ℂ) • (1 : Matrix (κι × Fin N) (κι × Fin N) ℂ) + covOp G a aT ν α φ Q P) := by
    rw [covT_eq, hc2]
    unfold covOp
    push_cast
    module
  set Av := covA (a k) (aT / (L : ℝ) ^ 2) x (liftOp N P) with hAv
  set Wx := liftOp N Hx⁻¹ - constrainedOp Hx⁻¹ (restrictField G φ) with hWx
  have hR : ((((L : ℝ) ^ k) ^ 2 : ℂ) • Av) + ((a k / ((L : ℝ) ^ k) ^ 2 : ℝ) : ℂ) ^ 2 •
      ((((L : ℝ) ^ k) ^ 2 : ℂ) • Av * liftRect N Q * Wx * (liftRect N Q)ᵀ *
        ((((L : ℝ) ^ k) ^ 2 : ℂ) • Av)) =
      ((((L : ℝ) ^ k) ^ 2 : ℝ) : ℂ) • (Av + (((a k) ^ 2 / (L : ℝ) ^ (2 * k) : ℝ) : ℂ) •
        (Av * liftRect N Q * Wx * (liftRect N Q)ᵀ * Av)) := by
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    push_cast at hc3 ⊢
    rw [smul_add, smul_smul]
    congr 2
    rw [← mul_assoc]
    exact hc3
  rw [hL, hR] at hprod
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, inv_mul_cancel₀ hL2c, one_smul] at hprod
  exact hprod

/-- **I-4c (iv), the identification at `s ≡ 1`.** For every `x ≥ 0`,
`x + 𝒜` is invertible and `C_x(1) = (x + 𝒜)⁻¹`, where `𝒜 = a L⁻² Q*Q + Δ^{(k)}` is
`x`-independent (`covOp`). -/
theorem decCov_one_eq (hfam : ∀ x, 0 ≤ x → XData G a aT ν x α 0 (fun _ => 1))
    (hφ : IsConstraintField G δ φ) (hδ : 0 ≤ δ) (hsm : δ ^ 2 * smallConstX d L 0 ≤ 1 / 4)
    (hU : IsUnitLatticeB G Q P) {x : ℝ} (hx : 0 ≤ x) :
    IsUnit ((x : ℂ) • (1 : Matrix (κι × Fin N) (κι × Fin N) ℂ) + covOp G a aT ν α φ Q P) ∧
      decCov G a aT x ν α (fun _ => 1) φ Q P =
        ((x : ℂ) • (1 : Matrix (κι × Fin N) (κι × Fin N) ℂ) + covOp G a aT ν α φ Q P)⁻¹ := by
  have h := decCov_one_mul hfam hφ hδ hsm hU hx
  refine ⟨(Matrix.isUnit_iff_isUnit_det _).2 (Matrix.isUnit_det_of_right_inverse h), ?_⟩
  exact (Matrix.inv_eq_right_inv h).symm

end Assembly

end Balaban.Localization
