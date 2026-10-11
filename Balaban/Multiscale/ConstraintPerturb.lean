/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Multiscale.ConstraintKernel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Perturbation of the constrained operator in the data (GREEN.md §4.5b (2))

For two sets of data `(α₁, φ₁)`, `(α₂, φ₂)` obeying the hypotheses of G-2(v) and `ε`-close
(`ℓ² |α₁ - α₂| ≤ ε`, `ℓ |∂(φ₁ - φ₂)| ≤ ε`, `ℓ² |Δ(φ₁ - φ₂)| ≤ ε`, `|φ₁ - φ₂| ≤ ε`) the constrained
operators satisfy `‖ℓ⁻¹ (Π₁ - Π₂) f‖² ≤ C(d) ε² ‖ℓ f‖²`.
-/

@[expose] public section

namespace Balaban.Multiscale

open Matrix Finset
open scoped ComplexOrder

variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}

section Infra

variable (G : GeneratingSet d L N₀ k ϱ)

theorem comp_add (u v : G.Ω 1 × Fin N → ℂ) (i : Fin N) :
    comp G (u + v) i = comp G u i + comp G v i := rfl

theorem comp_sub (u v : G.Ω 1 × Fin N → ℂ) (i : Fin N) :
    comp G (u - v) i = comp G u i - comp G v i := rfl

theorem vecSrc_add_le (ε : ℝ) (r : Torus d (N₀ * L ^ k) → ℝ) (u v : G.Ω 1 × Fin N → ℂ) :
    vecSrc G ε r (u + v) ≤ 2 * vecSrc G ε r u + 2 * vecSrc G ε r v := by
  unfold vecSrc
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun i _ => by
    rw [comp_add]; exact agmonSource_add_le G ε r _ _

theorem vecSrc_sub_le (ε : ℝ) (r : Torus d (N₀ * L ^ k) → ℝ) (u v : G.Ω 1 × Fin N → ℂ) :
    vecSrc G ε r (u - v) ≤ 2 * vecSrc G ε r u + 2 * vecSrc G ε r v := by
  unfold vecSrc
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun i _ => by
    rw [comp_sub]; exact agmonSource_sub_le G ε r _ _

theorem cwsq_agmonField_zero (s : G.Ω 1 → ℂ) :
    cwsq G (agmonField G 0 (fun _ => 0) s) = ∑ x : G.Ω 1, ((G.spacing x) ^ 2)⁻¹ * ‖s x‖ ^ 2 := by
  unfold cwsq
  rw [Green.sum_eq_sum_subtype (G.Ω 1) _ (fun i hi => by
    simp [norm_agmonField, zeroExt_not_mem _ _ hi])]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [invSqSpacing_eq G x.2, norm_agmonField, zeroExt_mem]
  simp

/-- Multiplication by a function `β` with `ℓ² |β| ≤ ε`: `‖ℓ β s‖² ≤ ε² ‖ℓ⁻¹ s‖²`. -/
theorem agmonSource_mul_small (β s : G.Ω 1 → ℂ) {ε : ℝ}
    (hβ : ∀ x : G.Ω 1, ‖β x‖ ≤ ε / G.spacing x ^ 2) :
    agmonSource G 0 (fun _ => 0) (fun x => β x * s x) ≤
      ε ^ 2 * cwsq G (agmonField G 0 (fun _ => 0) s) := by
  rw [agmonSource_eq, cwsq_agmonField_zero, Finset.mul_sum]
  refine Finset.sum_le_sum fun x _ => ?_
  have hsp : 0 < G.spacing x := spacing_pos G
  have h1 : ‖β x‖ ^ 2 ≤ (ε / G.spacing x ^ 2) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) (hβ x) 2
  rw [norm_mul, mul_pow]
  simp only [mul_zero, Real.exp_zero, one_pow, mul_one]
  have e : G.spacing x ^ 2 * (‖β x‖ ^ 2 * ‖s x‖ ^ 2) ≤
      G.spacing x ^ 2 * ((ε / G.spacing x ^ 2) ^ 2 * ‖s x‖ ^ 2) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h1 (sq_nonneg _)) (by positivity)
  refine e.trans (le_of_eq ?_)
  field_simp

end Infra

section Diff

variable (G : GeneratingSet d L N₀ k ϱ)

theorem dirichlet_sub (a : ℕ → ℝ) (ν : ℝ) (α₁ α₂ : G.Ω 1 → ℂ) :
    dirichletOperator G a ν α₂ - dirichletOperator G a ν α₁ =
      Matrix.diagonal (fun x => α₂ x - α₁ x) := by
  unfold dirichletOperator
  rw [add_sub_add_left_eq_sub, ← Matrix.diagonal_sub]

/-- `‖ℓ D t‖² ≤ ε² ‖ℓ⁻¹ t‖²` for a diagonal operator `D` with `ℓ² |D| ≤ ε` (vector fields). -/
theorem vecSrc_diag_le (β : G.Ω 1 → ℂ) {ε : ℝ} (hβ : ∀ x : G.Ω 1, ‖β x‖ ≤ ε / G.spacing x ^ 2)
    (t : G.Ω 1 × Fin N → ℂ) :
    vecSrc G 0 (fun _ => 0) (liftOp N (Matrix.diagonal β) *ᵥ t) ≤
      ε ^ 2 * vecM G 0 (fun _ => 0) t := by
  rw [vecM_eq, Finset.mul_sum]
  unfold vecSrc
  refine Finset.sum_le_sum fun i _ => ?_
  have : comp G (liftOp N (Matrix.diagonal β) *ᵥ t) i = fun x => β x * comp G t i x := by
    rw [comp_liftOp]
    funext x
    rw [Matrix.mulVec_diagonal]
  rw [this]
  exact agmonSource_mul_small G β (comp G t i) hβ

end Diff

section Algebra

variable {G : GeneratingSet d L N₀ k ϱ} {a : ℕ → ℝ} {ν : ℝ}

omit [NeZero N₀] [NeZero L] in
theorem liftOp_sub {ι : Type*} [Fintype ι] [DecidableEq ι] (A B : Matrix ι ι ℂ) :
    liftOp N (A - B) = liftOp N A - liftOp N B := by
  ext p q
  by_cases h : p.2 = q.2 <;> simp [liftOp, h]

/-- The resolvent identity in the form `Ĝ₁ x₁ - Ĝ₂ x₂ = Ĝ₁ (x₁ - x₂ + (Ĥ₂ - Ĥ₁) Ĝ₂ x₂)`. -/
theorem green_diff {α₁ α₂ : G.Ω 1 → ℂ} {δ₁ δ₂ : ℝ}
    {φ₁ φ₂ : Torus d (N₀ * L ^ k) → Fin N → ℂ}
    (St₁ : Standing G a ν α₁ δ₁ φ₁) (St₂ : Standing G a ν α₂ δ₂ φ₂)
    (x₁ x₂ : G.Ω 1 × Fin N → ℂ) :
    liftOp N (dirichletOperator G a ν α₁)⁻¹ *ᵥ x₁ - liftOp N (dirichletOperator G a ν α₂)⁻¹ *ᵥ x₂ =
      liftOp N (dirichletOperator G a ν α₁)⁻¹ *ᵥ
        (x₁ - x₂ + liftOp N (dirichletOperator G a ν α₂ - dirichletOperator G a ν α₁) *ᵥ
          (liftOp N (dirichletOperator G a ν α₂)⁻¹ *ᵥ x₂)) := by
  have e1 : (dirichletOperator G a ν α₁)⁻¹ * dirichletOperator G a ν α₂ *
      (dirichletOperator G a ν α₂)⁻¹ = (dirichletOperator G a ν α₁)⁻¹ := by
    rw [Matrix.mul_assoc, dirichlet_mul_inv St₂, Matrix.mul_one]
  have e2 : (dirichletOperator G a ν α₁)⁻¹ * dirichletOperator G a ν α₁ *
      (dirichletOperator G a ν α₂)⁻¹ = (dirichletOperator G a ν α₂)⁻¹ := by
    rw [dirichlet_inv_mul St₁, Matrix.one_mul]
  have h1 : (dirichletOperator G a ν α₁)⁻¹ * (dirichletOperator G a ν α₂ -
      dirichletOperator G a ν α₁) * (dirichletOperator G a ν α₂)⁻¹ =
      (dirichletOperator G a ν α₁)⁻¹ - (dirichletOperator G a ν α₂)⁻¹ := by
    rw [Matrix.mul_sub, Matrix.sub_mul, e1, e2]
  have hmat : liftOp N (dirichletOperator G a ν α₁)⁻¹ *
      liftOp N (dirichletOperator G a ν α₂ - dirichletOperator G a ν α₁) *
      liftOp N (dirichletOperator G a ν α₂)⁻¹ =
      liftOp N (dirichletOperator G a ν α₁)⁻¹ - liftOp N (dirichletOperator G a ν α₂)⁻¹ := by
    rw [← liftOp_mul, ← liftOp_mul, h1, liftOp_sub]
  rw [Matrix.mulVec_add, Matrix.mulVec_sub, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hmat,
    Matrix.sub_mulVec]
  abel

end Algebra

section Identities

variable {G : GeneratingSet d L N₀ k ϱ} {a : ℕ → ℝ} {ν : ℝ}

theorem constraintN_mulVec (H Gm : Matrix (G.Ω 1) (G.Ω 1) ℂ) (φ' : G.Ω 1 → Fin N → ℂ)
    (f : G.Ω 1 × Fin N → ℂ) :
    constraintN H Gm φ' *ᵥ f =
      (fieldMul φ')ᵀ *ᵥ f - commK H φ' *ᵥ (liftOp N Gm *ᵥ f) := by
  unfold constraintN
  rw [sub_mulVec, ← mulVec_mulVec]

theorem constraintM_apply (H Gm : Matrix (G.Ω 1) (G.Ω 1) ℂ) (φ' : G.Ω 1 → Fin N → ℂ)
    (h : G.Ω 1 → ℂ) :
    constraintM H Gm φ' *ᵥ h =
      (fieldMul φ')ᵀ *ᵥ (fieldMul φ' *ᵥ h) -
        commK H φ' *ᵥ (liftOp N Gm *ᵥ (fieldMul φ' *ᵥ h)) := by
  unfold constraintM
  have e1 : (commK H φ' * liftOp N Gm * fieldMul φ') *ᵥ h =
      commK H φ' *ᵥ (liftOp N Gm *ᵥ (fieldMul φ' *ᵥ h)) := by
    rw [mulVec_mulVec, mulVec_mulVec, Matrix.mul_assoc]
  have e2 : ((fieldMul φ')ᵀ * fieldMul φ') *ᵥ h = (fieldMul φ')ᵀ *ᵥ (fieldMul φ' *ᵥ h) := by
    rw [mulVec_mulVec]
  rw [sub_mulVec, e1, e2]

/-- `K(φ₁) - K(φ₂) = K(φ₁ - φ₂)` for the Dirichlet operators (the diagonal terms, in particular
`α`, cancel in the commutator). -/
theorem commK_diff (α₁ α₂ : G.Ω 1 → ℂ) (φ₁ φ₂ : Torus d (N₀ * L ^ k) → Fin N → ℂ)
    (t : G.Ω 1 × Fin N → ℂ) :
    commK (dirichletOperator G a ν α₁) (restrictField G φ₁) *ᵥ t -
        commK (dirichletOperator G a ν α₂) (restrictField G φ₂) *ᵥ t =
      commK (dirichletOperator G a ν α₁) (restrictField G (fun x j => φ₁ x j - φ₂ x j)) *ᵥ t := by
  funext x
  rw [Pi.sub_apply, commK_dirichlet, commK_dirichlet, commK_dirichlet]
  have : commArg G (fun x j => φ₁ x j - φ₂ x j) t (x : Torus d (N₀ * L ^ k)) =
      commArg G φ₁ t x - commArg G φ₂ t x := by
    funext y
    rw [Pi.sub_apply]
    unfold commArg
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [this, Matrix.mulVec_sub, Pi.sub_apply]

end Identities

section Bounds

variable {G : GeneratingSet d L N₀ k ϱ} {a : ℕ → ℝ} {ν : ℝ}

/-- `4 / c²`, the constant of `‖ℓ⁻¹ G f‖² ≤ (4/c²) ‖ℓ f‖²`. -/
noncomputable def Ac (d : ℕ) : ℝ := 4 / poincareConst d ^ 2
/-- `10 / c`, the constant of `‖∂ G f‖² ≤ (10/c) ‖ℓ f‖²`. -/
noncomputable def Bc (d : ℕ) : ℝ := 10 / poincareConst d
/-- `105 d²`, the constant of the commutator bound. -/
noncomputable def Kc (d : ℕ) : ℝ := 105 * (d : ℝ) ^ 2

theorem poincareConst_nonneg' (d : ℕ) : 0 ≤ poincareConst d :=
  le_min (by positivity) (by norm_num)

theorem Ac_nonneg (d : ℕ) : 0 ≤ Ac d := by unfold Ac; positivity
theorem Bc_nonneg (d : ℕ) : 0 ≤ Bc d := by
  have := poincareConst_nonneg' d
  unfold Bc; positivity
theorem Kc_nonneg (d : ℕ) : 0 ≤ Kc d := by unfold Kc; positivity

/-- Closeness of two sets of data. -/
structure Close (G : GeneratingSet d L N₀ k ϱ) (ε : ℝ) (α₁ α₂ : G.Ω 1 → ℂ)
    (φ₁ φ₂ : Torus d (N₀ * L ^ k) → Fin N → ℂ) : Prop where
  nonneg : 0 ≤ ε
  alpha : ∀ x : G.Ω 1, ‖α₂ x - α₁ x‖ ≤ ε / G.spacing x ^ 2
  smooth : IsSmoothField G ε (fun x j => φ₁ x j - φ₂ x j)
  bound : ∀ x ∈ G.Ω 1, vn (fun j => φ₁ x j - φ₂ x j) ≤ ε

theorem green0 {α : G.Ω 1 → ℂ} {δ : ℝ} {φ : Torus d (N₀ * L ^ k) → Fin N → ℂ}
    (St : Standing G a ν α δ φ) (g : G.Ω 1 × Fin N → ℂ) :
    vecM G 0 (fun _ => 0) (liftOp N (dirichletOperator G a ν α)⁻¹ *ᵥ g) ≤
        Ac d * vecSrc G 0 (fun _ => 0) g ∧
      vecGrad G 0 (fun _ => 0) (liftOp N (dirichletOperator G a ν α)⁻¹ *ᵥ g) ≤
        Bc d * vecSrc G 0 (fun _ => 0) g :=
  green_vec_bounds St (isAgmonWeight_zero G) le_rfl (agmonRate_pos St.pos).le g

theorem green0_sum {α : G.Ω 1 → ℂ} {δ : ℝ} {φ : Torus d (N₀ * L ^ k) → Fin N → ℂ}
    (St : Standing G a ν α δ φ) (g : G.Ω 1 × Fin N → ℂ) :
    vecGrad G 0 (fun _ => 0) (liftOp N (dirichletOperator G a ν α)⁻¹ *ᵥ g) +
      vecM G 0 (fun _ => 0) (liftOp N (dirichletOperator G a ν α)⁻¹ *ᵥ g) ≤
        (Ac d + Bc d) * vecSrc G 0 (fun _ => 0) g := by
  obtain ⟨h1, h2⟩ := green0 St g
  linarith

theorem delta_sq_le_one {α : G.Ω 1 → ℂ} {δ : ℝ} {φ : Torus d (N₀ * L ^ k) → Fin N → ℂ}
    (St : Standing G a ν α δ φ) : δ ^ 2 ≤ 1 := by
  have h2 : 2 ≤ smallnessConst d := by
    unfold smallnessConst
    have := poincareConst_inv_nonneg St.pos
    have hd : (0 : ℝ) ≤ (d : ℝ) ^ 2 := by positivity
    nlinarith [mul_nonneg hd this]
  have := St.small
  nlinarith [sq_nonneg δ]

/-- The commutator bound at weight `1`. -/
theorem src0_commK {α : G.Ω 1 → ℂ} {δ : ℝ} {φ : Torus d (N₀ * L ^ k) → Fin N → ℂ}
    (St : Standing G a ν α δ φ) (t : G.Ω 1 × Fin N → ℂ) :
    agmonSource G 0 (fun _ => 0)
      (commK (dirichletOperator G a ν α) (restrictField G φ) *ᵥ t) ≤
      Kc d * (vecGrad G 0 (fun _ => 0) t + vecM G 0 (fun _ => 0) t) := by
  have h := agmonSource_commK_le G St.pos St.weights ν α St.field.toIsSmoothField St.nonneg
    (isAgmonWeight_zero G) le_rfl (agmonRate_pos St.pos).le t
  have h1 := delta_sq_le_one St
  have h2 : 0 ≤ vecGrad G 0 (fun _ => 0) t + vecM G 0 (fun _ => 0) t :=
    add_nonneg (vecGrad_nonneg G _ _ _) (vecM_nonneg G _ _ _)
  have h3 : 0 ≤ (d : ℝ) ^ 2 := by positivity
  unfold Kc
  refine h.trans ?_
  nlinarith [mul_nonneg h3 h2]

/-- The commutator difference bound at weight `1`. -/
theorem src0_commK_diff {α₁ α₂ : G.Ω 1 → ℂ} {φ₁ φ₂ : Torus d (N₀ * L ^ k) → Fin N → ℂ}
    {ε : ℝ} (hd : 0 < d) (ha : IsAdmissibleWeights k a) (hC : Close G ε α₁ α₂ φ₁ φ₂)
    (t : G.Ω 1 × Fin N → ℂ) :
    agmonSource G 0 (fun _ => 0)
      (commK (dirichletOperator G a ν α₁) (restrictField G φ₁) *ᵥ t -
        commK (dirichletOperator G a ν α₂) (restrictField G φ₂) *ᵥ t) ≤
      Kc d * ε ^ 2 * (vecGrad G 0 (fun _ => 0) t + vecM G 0 (fun _ => 0) t) := by
  rw [commK_diff]
  have h := agmonSource_commK_le G hd ha ν α₁ hC.smooth hC.nonneg
    (isAgmonWeight_zero G) le_rfl (agmonRate_pos hd).le t
  unfold Kc
  refine h.trans (le_of_eq ?_)
  ring

/-- The multiplier `D̂ = Ĥ₂ - Ĥ₁ = diag (α₂ - α₁)` in the weighted norm. -/
theorem vecSrc_Dhat {α₁ α₂ : G.Ω 1 → ℂ} {φ₁ φ₂ : Torus d (N₀ * L ^ k) → Fin N → ℂ} {ε : ℝ}
    (hC : Close G ε α₁ α₂ φ₁ φ₂) (t : G.Ω 1 × Fin N → ℂ) :
    vecSrc G 0 (fun _ => 0)
      (liftOp N (dirichletOperator G a ν α₂ - dirichletOperator G a ν α₁) *ᵥ t) ≤
      ε ^ 2 * vecM G 0 (fun _ => 0) t := by
  rw [dirichlet_sub]
  exact vecSrc_diag_le G _ hC.alpha t

end Bounds

section Mult

variable {G : GeneratingSet d L N₀ k ϱ} {a : ℕ → ℝ} {ν : ℝ}

/-- Multiplication `s ↦ (φ'ᵢ s)ᵢ` with `|φ'| ≤ c`, in the weighted source norm. -/
theorem vecSrc_fieldMul_le_of {φ' : Torus d (N₀ * L ^ k) → Fin N → ℂ} {c : ℝ}
    (hφ : ∀ x ∈ G.Ω 1, vn (φ' x) ≤ c) (s : G.Ω 1 → ℂ) :
    vecSrc G 0 (fun _ => 0) (fieldMul (restrictField G φ') *ᵥ s) ≤
      c ^ 2 * agmonSource G 0 (fun _ => 0) s := by
  unfold vecSrc
  simp only [agmonSource_eq]
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_le_sum fun x _ => ?_
  have hx := hφ x x.2
  have e : ∀ i, comp G (fieldMul (restrictField G φ') *ᵥ s) i x = φ' x i * s x := fun i => by
    simp only [comp]; rw [fieldMul_mulVec]; rfl
  simp only [e, norm_mul, mul_pow]
  have h1 : ∑ i, ‖φ' x i‖ ^ 2 = vn (φ' x) ^ 2 := (vn_sq _).symm
  have h2 : vn (φ' x) ^ 2 ≤ c ^ 2 := pow_le_pow_left₀ (vn_nonneg _) hx 2
  have h3 : 0 ≤ G.spacing x ^ 2 * Real.exp (0 * (fun _ => (0:ℝ)) x) ^ 2 * ‖s x‖ ^ 2 := by positivity
  calc ∑ i, G.spacing x ^ 2 * Real.exp (0 * (fun _ => (0:ℝ)) x) ^ 2 * (‖φ' x i‖ ^ 2 * ‖s x‖ ^ 2)
      = (∑ i, ‖φ' x i‖ ^ 2) * (G.spacing x ^ 2 * Real.exp (0 * (fun _ => (0:ℝ)) x) ^ 2 * ‖s x‖ ^ 2) := by
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun i _ => by ring
    _ ≤ c ^ 2 * (G.spacing x ^ 2 * Real.exp (0 * (fun _ => (0:ℝ)) x) ^ 2 * ‖s x‖ ^ 2) := by
        rw [h1]; exact mul_le_mul_of_nonneg_right h2 h3

theorem agmonSource_transpose_le_of {φ' : Torus d (N₀ * L ^ k) → Fin N → ℂ} {c : ℝ}
    (hφ : ∀ x ∈ G.Ω 1, vn (φ' x) ≤ c) (f : G.Ω 1 × Fin N → ℂ) :
    agmonSource G 0 (fun _ => 0) ((fieldMul (restrictField G φ'))ᵀ *ᵥ f) ≤
      c ^ 2 * vecSrc G 0 (fun _ => 0) f := by
  unfold vecSrc
  simp only [agmonSource_eq]
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_le_sum fun x _ => ?_
  have hx := hφ x x.2
  have e : ((fieldMul (restrictField G φ'))ᵀ *ᵥ f) x = ∑ i, φ' x i * f (x, i) :=
    fieldMul_transpose_mulVec _ _ _
  rw [e]
  have h1 : ‖∑ i, φ' x i * f (x, i)‖ ≤ vn (φ' x) * vn (fun i => f (x, i)) :=
    norm_dot_le (φ' x) (fun i => f (x, i))
  have h2 : ‖∑ i, φ' x i * f (x, i)‖ ^ 2 ≤ (c * vn (fun i => f (x, i))) ^ 2 := by
    refine pow_le_pow_left₀ (norm_nonneg _) (h1.trans ?_) 2
    exact mul_le_mul_of_nonneg_right hx (vn_nonneg _)
  have h3 : vn (fun i => f (x, i)) ^ 2 = ∑ i, ‖comp G f i x‖ ^ 2 := vn_sq _
  have h4 : 0 ≤ G.spacing x ^ 2 * Real.exp (0 * (fun _ => (0:ℝ)) x) ^ 2 := by positivity
  calc G.spacing x ^ 2 * Real.exp (0 * (fun _ => (0:ℝ)) x) ^ 2 * ‖∑ i, φ' x i * f (x, i)‖ ^ 2
      ≤ G.spacing x ^ 2 * Real.exp (0 * (fun _ => (0:ℝ)) x) ^ 2 *
          (c * vn (fun i => f (x, i))) ^ 2 := mul_le_mul_of_nonneg_left h2 h4
    _ = c ^ 2 * ∑ i, G.spacing x ^ 2 * Real.exp (0 * (fun _ => (0:ℝ)) x) ^ 2 *
          ‖comp G f i x‖ ^ 2 := by
        rw [← Finset.mul_sum, ← h3]; ring

end Mult

section Chain

variable {G : GeneratingSet d L N₀ k ϱ} {a : ℕ → ℝ} {ν : ℝ}

/-- Two `ε`-close sets of data obeying the hypotheses of G-2(v). -/
structure PertData (G : GeneratingSet d L N₀ k ϱ) (a : ℕ → ℝ) (ν : ℝ) (α₁ α₂ : G.Ω 1 → ℂ)
    (δ₁ δ₂ ε : ℝ) (φ₁ φ₂ : Torus d (N₀ * L ^ k) → Fin N → ℂ) : Prop where
  st₁ : Standing G a ν α₁ δ₁ φ₁
  st₂ : Standing G a ν α₂ δ₂ φ₂
  close : Close G ε α₁ α₂ φ₁ φ₂

section Pieces

variable {α : G.Ω 1 → ℂ} {δ : ℝ} {φ : Torus d (N₀ * L ^ k) → Fin N → ℂ}
  (St : Standing G a ν α δ φ)

include St

theorem constrainedOp_mulVec_eq (f : G.Ω 1 × Fin N → ℂ) :
    constrainedOp (dirichletOperator G a ν α)⁻¹ (restrictField G φ) *ᵥ f =
      liftOp N (dirichletOperator G a ν α)⁻¹ *ᵥ (fieldMul (restrictField G φ) *ᵥ
        ((constraintM (dirichletOperator G a ν α) (dirichletOperator G a ν α)⁻¹
          (restrictField G φ))⁻¹ *ᵥ (constraintN (dirichletOperator G a ν α)
            (dirichletOperator G a ν α)⁻¹ (restrictField G φ) *ᵥ f))) := by
  rw [constrainedOp_eq (dirichlet_mul_inv St) (dirichlet_inv_mul St)]
  rw [← mulVec_mulVec, ← mulVec_mulVec, ← mulVec_mulVec]

theorem h_src_le (f : G.Ω 1 × Fin N → ℂ) :
    agmonSource G 0 (fun _ => 0)
      ((constraintM (dirichletOperator G a ν α) (dirichletOperator G a ν α)⁻¹
          (restrictField G φ))⁻¹ *ᵥ (constraintN (dirichletOperator G a ν α)
            (dirichletOperator G a ν α)⁻¹ (restrictField G φ) *ᵥ f)) ≤
      20 * vecSrc G 0 (fun _ => 0) f := by
  have hU := constraintM_isUnit St
  have hMinv : constraintM (dirichletOperator G a ν α) (dirichletOperator G a ν α)⁻¹
      (restrictField G φ) * (constraintM (dirichletOperator G a ν α) (dirichletOperator G a ν α)⁻¹
      (restrictField G φ))⁻¹ = 1 :=
    Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hU)
  set h : G.Ω 1 → ℂ := (constraintM (dirichletOperator G a ν α) (dirichletOperator G a ν α)⁻¹
      (restrictField G φ))⁻¹ *ᵥ (constraintN (dirichletOperator G a ν α)
        (dirichletOperator G a ν α)⁻¹ (restrictField G φ) *ᵥ f) with hh
  have hMh : constraintM (dirichletOperator G a ν α) (dirichletOperator G a ν α)⁻¹
      (restrictField G φ) *ᵥ h = constraintN (dirichletOperator G a ν α)
        (dirichletOperator G a ν α)⁻¹ (restrictField G φ) *ᵥ f := by
    rw [hh, mulVec_mulVec, hMinv, one_mulVec]
  have := constraintM_lower St (isAgmonWeight_zero G) le_rfl (agmonRate_pos St.pos).le h
  rw [hMh] at this
  have h5 := constraintN_src_le St (isAgmonWeight_zero G) le_rfl (agmonRate_pos St.pos).le f
  linarith

end Pieces

end Chain

section Diffs

variable {G : GeneratingSet d L N₀ k ϱ} {a : ℕ → ℝ} {ν : ℝ}
  {α₁ α₂ : G.Ω 1 → ℂ} {δ₁ δ₂ ε : ℝ} {φ₁ φ₂ : Torus d (N₀ * L ^ k) → Fin N → ℂ}

theorem fieldMul_sub' (ψ₁ ψ₂ : G.Ω 1 → Fin N → ℂ) :
    fieldMul (fun x j => ψ₁ x j - ψ₂ x j) = fieldMul ψ₁ - fieldMul ψ₂ := by
  ext p y
  by_cases h : p.1 = y <;> simp [fieldMul, h]

/-- Tg = Ac + Bc. -/
noncomputable def Tg (d : ℕ) : ℝ := Ac d + Bc d

theorem Tg_nonneg (d : ℕ) : 0 ≤ Tg d := add_nonneg (Ac_nonneg d) (Bc_nonneg d)

/-- `‖ℓ w_N‖`: the resolvent-difference source `D̂ Ĝ₂ x` is `O(ε)`. -/
theorem vecSrc_w_le (P : PertData G a ν α₁ α₂ δ₁ δ₂ ε φ₁ φ₂) (x₁ x₂ : G.Ω 1 × Fin N → ℂ) :
    vecSrc G 0 (fun _ => 0) (x₁ - x₂ + liftOp N (dirichletOperator G a ν α₂ -
        dirichletOperator G a ν α₁) *ᵥ (liftOp N (dirichletOperator G a ν α₂)⁻¹ *ᵥ x₂)) ≤
      2 * vecSrc G 0 (fun _ => 0) (x₁ - x₂) + 2 * (ε ^ 2 * Ac d) * vecSrc G 0 (fun _ => 0) x₂ := by
  refine (vecSrc_add_le G 0 _ _ _).trans ?_
  have h1 := vecSrc_Dhat (a := a) (ν := ν) P.close (liftOp N (dirichletOperator G a ν α₂)⁻¹ *ᵥ x₂)
  have h2 := (green0 P.st₂ x₂).1
  have h3 : ε ^ 2 * vecM G 0 (fun _ => 0) (liftOp N (dirichletOperator G a ν α₂)⁻¹ *ᵥ x₂) ≤
      ε ^ 2 * (Ac d * vecSrc G 0 (fun _ => 0) x₂) :=
    mul_le_mul_of_nonneg_left h2 (sq_nonneg ε)
  nlinarith

theorem K_Ghat_diff (P : PertData G a ν α₁ α₂ δ₁ δ₂ ε φ₁ φ₂) (x₁ x₂ : G.Ω 1 × Fin N → ℂ) :
    commK (dirichletOperator G a ν α₁) (restrictField G φ₁) *ᵥ
        (liftOp N (dirichletOperator G a ν α₁)⁻¹ *ᵥ x₁) -
      commK (dirichletOperator G a ν α₂) (restrictField G φ₂) *ᵥ
        (liftOp N (dirichletOperator G a ν α₂)⁻¹ *ᵥ x₂) =
    commK (dirichletOperator G a ν α₁) (restrictField G φ₁) *ᵥ
        (liftOp N (dirichletOperator G a ν α₁)⁻¹ *ᵥ (x₁ - x₂ + liftOp N (dirichletOperator G a ν α₂ -
          dirichletOperator G a ν α₁) *ᵥ (liftOp N (dirichletOperator G a ν α₂)⁻¹ *ᵥ x₂))) +
      (commK (dirichletOperator G a ν α₁) (restrictField G φ₁) *ᵥ
          (liftOp N (dirichletOperator G a ν α₂)⁻¹ *ᵥ x₂) -
        commK (dirichletOperator G a ν α₂) (restrictField G φ₂) *ᵥ
          (liftOp N (dirichletOperator G a ν α₂)⁻¹ *ᵥ x₂)) := by
  rw [← green_diff P.st₁ P.st₂ x₁ x₂, Matrix.mulVec_sub]
  abel


theorem transpose_diff (f : G.Ω 1 × Fin N → ℂ) :
    (fieldMul (restrictField G φ₁))ᵀ *ᵥ f - (fieldMul (restrictField G φ₂))ᵀ *ᵥ f =
      (fieldMul (restrictField G (fun x j => φ₁ x j - φ₂ x j)))ᵀ *ᵥ f := by
  have : restrictField G (fun x j => φ₁ x j - φ₂ x j) =
      fun x j => restrictField G φ₁ x j - restrictField G φ₂ x j := rfl
  rw [this, fieldMul_sub', Matrix.transpose_sub, Matrix.sub_mulVec]

theorem fieldMul_diff (s : G.Ω 1 → ℂ) :
    fieldMul (restrictField G φ₁) *ᵥ s - fieldMul (restrictField G φ₂) *ᵥ s =
      fieldMul (restrictField G (fun x j => φ₁ x j - φ₂ x j)) *ᵥ s := by
  have : restrictField G (fun x j => φ₁ x j - φ₂ x j) =
      fun x j => restrictField G φ₁ x j - restrictField G φ₂ x j := rfl
  rw [this, fieldMul_sub', Matrix.sub_mulVec]

theorem N_diff (P : PertData G a ν α₁ α₂ δ₁ δ₂ ε φ₁ φ₂) (f : G.Ω 1 × Fin N → ℂ) :
    agmonSource G 0 (fun _ => 0)
      (constraintN (dirichletOperator G a ν α₁) (dirichletOperator G a ν α₁)⁻¹
          (restrictField G φ₁) *ᵥ f -
        constraintN (dirichletOperator G a ν α₂) (dirichletOperator G a ν α₂)⁻¹
          (restrictField G φ₂) *ᵥ f) ≤
      4 * (1 + Kc d * Tg d * (Ac d + 1)) * ε ^ 2 * vecSrc G 0 (fun _ => 0) f := by
  rw [constraintN_mulVec, constraintN_mulVec]
  have hK := K_Ghat_diff P f f
  rw [sub_self, zero_add] at hK
  set wN := liftOp N (dirichletOperator G a ν α₂ - dirichletOperator G a ν α₁) *ᵥ
    (liftOp N (dirichletOperator G a ν α₂)⁻¹ *ᵥ f) with hwN
  set Bv := commK (dirichletOperator G a ν α₁) (restrictField G φ₁) *ᵥ
    (liftOp N (dirichletOperator G a ν α₁)⁻¹ *ᵥ wN) with hBv
  set Cv := commK (dirichletOperator G a ν α₁) (restrictField G φ₁) *ᵥ
        (liftOp N (dirichletOperator G a ν α₂)⁻¹ *ᵥ f) -
      commK (dirichletOperator G a ν α₂) (restrictField G φ₂) *ᵥ
        (liftOp N (dirichletOperator G a ν α₂)⁻¹ *ᵥ f) with hCv
  set Av := (fieldMul (restrictField G φ₁))ᵀ *ᵥ f - (fieldMul (restrictField G φ₂))ᵀ *ᵥ f with hAv
  have e : ((fieldMul (restrictField G φ₁))ᵀ *ᵥ f - commK (dirichletOperator G a ν α₁)
        (restrictField G φ₁) *ᵥ (liftOp N (dirichletOperator G a ν α₁)⁻¹ *ᵥ f)) -
      ((fieldMul (restrictField G φ₂))ᵀ *ᵥ f - commK (dirichletOperator G a ν α₂)
        (restrictField G φ₂) *ᵥ (liftOp N (dirichletOperator G a ν α₂)⁻¹ *ᵥ f)) =
      Av - (Bv + Cv) := by
    rw [← hK, hAv]; abel
  rw [e]
  have hA : agmonSource G 0 (fun _ => 0) Av ≤ ε ^ 2 * vecSrc G 0 (fun _ => 0) f := by
    rw [hAv, transpose_diff]
    exact agmonSource_transpose_le_of P.close.bound f
  have hwN : vecSrc G 0 (fun _ => 0) wN ≤ ε ^ 2 * Ac d * vecSrc G 0 (fun _ => 0) f := by
    have h1 := vecSrc_Dhat (a := a) (ν := ν) P.close
      (liftOp N (dirichletOperator G a ν α₂)⁻¹ *ᵥ f)
    have h2 := (green0 P.st₂ f).1
    have h3 : ε ^ 2 * vecM G 0 (fun _ => 0) (liftOp N (dirichletOperator G a ν α₂)⁻¹ *ᵥ f) ≤
        ε ^ 2 * (Ac d * vecSrc G 0 (fun _ => 0) f) :=
      mul_le_mul_of_nonneg_left h2 (sq_nonneg ε)
    rw [hwN]
    nlinarith
  have hB : agmonSource G 0 (fun _ => 0) Bv ≤
      Kc d * Tg d * (ε ^ 2 * Ac d * vecSrc G 0 (fun _ => 0) f) := by
    have h1 := src0_commK P.st₁ (liftOp N (dirichletOperator G a ν α₁)⁻¹ *ᵥ wN)
    have h2 := green0_sum P.st₁ wN
    have hKc := Kc_nonneg d
    calc _ ≤ Kc d * (vecGrad G 0 (fun _ => 0) (liftOp N (dirichletOperator G a ν α₁)⁻¹ *ᵥ wN) +
          vecM G 0 (fun _ => 0) (liftOp N (dirichletOperator G a ν α₁)⁻¹ *ᵥ wN)) := h1
      _ ≤ Kc d * (Tg d * vecSrc G 0 (fun _ => 0) wN) :=
          mul_le_mul_of_nonneg_left h2 hKc
      _ ≤ Kc d * (Tg d * (ε ^ 2 * Ac d * vecSrc G 0 (fun _ => 0) f)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hwN (Tg_nonneg d)) hKc
      _ = _ := by ring
  have hC : agmonSource G 0 (fun _ => 0) Cv ≤
      Kc d * ε ^ 2 * (Tg d * vecSrc G 0 (fun _ => 0) f) := by
    have h1 := src0_commK_diff (a := a) (ν := ν) P.st₁.pos P.st₁.weights P.close
      (liftOp N (dirichletOperator G a ν α₂)⁻¹ *ᵥ f)
    have h2 := green0_sum P.st₂ f
    have hKe : 0 ≤ Kc d * ε ^ 2 := mul_nonneg (Kc_nonneg d) (sq_nonneg ε)
    exact h1.trans (mul_le_mul_of_nonneg_left h2 hKe)
  have hsub := agmonSource_sub_le G 0 (fun _ => 0) Av (Bv + Cv)
  have hadd := agmonSource_add_le G 0 (fun _ => 0) Bv Cv
  have hX := vecSrc_nonneg G 0 (fun _ => 0) f
  unfold Tg at hB hC ⊢
  nlinarith [hsub, hadd, hA, hB, hC]


theorem transpose_fieldMul_apply (ψ : G.Ω 1 → Fin N → ℂ) (h : G.Ω 1 → ℂ) :
    (fieldMul ψ)ᵀ *ᵥ (fieldMul ψ *ᵥ h) = fun x => (∑ i, ψ x i * ψ x i) * h x := by
  funext x
  rw [fieldMul_transpose_mulVec, Finset.sum_mul]
  exact Finset.sum_congr rfl fun i _ => by rw [fieldMul_mulVec]; ring

theorem M_diff (P : PertData G a ν α₁ α₂ δ₁ δ₂ ε φ₁ φ₂) (h : G.Ω 1 → ℂ) :
    agmonSource G 0 (fun _ => 0)
      (constraintM (dirichletOperator G a ν α₂) (dirichletOperator G a ν α₂)⁻¹
          (restrictField G φ₂) *ᵥ h -
        constraintM (dirichletOperator G a ν α₁) (dirichletOperator G a ν α₁)⁻¹
          (restrictField G φ₁) *ᵥ h) ≤
      (18 + Kc d * Tg d * (17 + 18 * Ac d)) * ε ^ 2 * agmonSource G 0 (fun _ => 0) h := by
  rw [constraintM_apply, constraintM_apply]
  set x₁ := fieldMul (restrictField G φ₁) *ᵥ h with hx₁
  set x₂ := fieldMul (restrictField G φ₂) *ᵥ h with hx₂
  have hK := K_Ghat_diff P x₁ x₂
  set wM := x₁ - x₂ + liftOp N (dirichletOperator G a ν α₂ - dirichletOperator G a ν α₁) *ᵥ
    (liftOp N (dirichletOperator G a ν α₂)⁻¹ *ᵥ x₂) with hwM
  set Bv := commK (dirichletOperator G a ν α₁) (restrictField G φ₁) *ᵥ
    (liftOp N (dirichletOperator G a ν α₁)⁻¹ *ᵥ wM) with hBv
  set Cv := commK (dirichletOperator G a ν α₁) (restrictField G φ₁) *ᵥ
        (liftOp N (dirichletOperator G a ν α₂)⁻¹ *ᵥ x₂) -
      commK (dirichletOperator G a ν α₂) (restrictField G φ₂) *ᵥ
        (liftOp N (dirichletOperator G a ν α₂)⁻¹ *ᵥ x₂) with hCv
  set Fv : G.Ω 1 → ℂ := (fieldMul (restrictField G φ₂))ᵀ *ᵥ x₂ -
    (fieldMul (restrictField G φ₁))ᵀ *ᵥ x₁ with hFv
  have e : ((fieldMul (restrictField G φ₂))ᵀ *ᵥ x₂ - commK (dirichletOperator G a ν α₂)
        (restrictField G φ₂) *ᵥ (liftOp N (dirichletOperator G a ν α₂)⁻¹ *ᵥ x₂)) -
      ((fieldMul (restrictField G φ₁))ᵀ *ᵥ x₁ - commK (dirichletOperator G a ν α₁)
        (restrictField G φ₁) *ᵥ (liftOp N (dirichletOperator G a ν α₁)⁻¹ *ᵥ x₁)) =
      Fv + (Bv + Cv) := by
    rw [← hK, hFv]
    abel
  rw [e]
  have h3 : ∀ x ∈ G.Ω 1, vn (fun j => φ₁ x j - φ₂ x j) ≤ ε := P.close.bound
  have hF : agmonSource G 0 (fun _ => 0) Fv ≤ (3 * ε) ^ 2 * agmonSource G 0 (fun _ => 0) h := by
    have : Fv = fun x : G.Ω 1 => ((∑ i, φ₂ x i * φ₂ x i) - (∑ i, φ₁ x i * φ₁ x i)) * h x := by
      rw [hFv, hx₁, hx₂, transpose_fieldMul_apply, transpose_fieldMul_apply]
      funext x; simp only [Pi.sub_apply, restrictField]; ring
    rw [this]
    refine agmonSource_mul_le G 0 (fun _ => 0) _ h (c := 3 * ε) fun x => ?_
    have hsum : (∑ i, φ₂ x i * φ₂ x i) - (∑ i, φ₁ x i * φ₁ x i) =
        ∑ i, (φ₂ x i - φ₁ x i) * (φ₂ x i + φ₁ x i) := by
      rw [← Finset.sum_sub_distrib]; exact Finset.sum_congr rfl fun i _ => by ring
    have hd := norm_dot_le (fun i => φ₂ x i - φ₁ x i) (fun i => φ₂ x i + φ₁ x i)
    have hv1 : vn (fun i => φ₂ x i - φ₁ x i) ≤ ε := by
      have e : vn (φ₂ x - φ₁ x) = vn (φ₁ x - φ₂ x) := vn_sub_comm _ _
      exact e.le.trans (h3 x x.2)
    have hv2 : vn (fun i => φ₂ x i + φ₁ x i) ≤ 3 := by
      have := vn_add (φ₂ x) (φ₁ x)
      have b1 := P.st₂.field.bound x x.2
      have b2 := P.st₁.field.bound x x.2
      calc vn (fun i => φ₂ x i + φ₁ x i) = vn (φ₂ x + φ₁ x) := rfl
        _ ≤ _ := this
        _ ≤ 3 := by linarith
    rw [hsum]
    calc _ ≤ vn (fun i => φ₂ x i - φ₁ x i) * vn (fun i => φ₂ x i + φ₁ x i) := hd
      _ ≤ ε * 3 := mul_le_mul hv1 hv2 (vn_nonneg _) P.close.nonneg
      _ = 3 * ε := by ring
  have hx₁₂ : vecSrc G 0 (fun _ => 0) (x₁ - x₂) ≤ ε ^ 2 * agmonSource G 0 (fun _ => 0) h := by
    rw [hx₁, hx₂, fieldMul_diff]
    exact vecSrc_fieldMul_le_of h3 h
  have hx₂b : vecSrc G 0 (fun _ => 0) x₂ ≤ 9 / 4 * agmonSource G 0 (fun _ => 0) h := by
    have := vecSrc_fieldMul_le_of (G := G) (φ' := φ₂) (c := 3 / 2) P.st₂.field.bound h
    rw [hx₂]; linarith
  have hw := vecSrc_w_le P x₁ x₂
  have hwb : vecSrc G 0 (fun _ => 0) wM ≤
      (2 * ε ^ 2 + 2 * (ε ^ 2 * Ac d) * (9 / 4)) * agmonSource G 0 (fun _ => 0) h := by
    have hAc := Ac_nonneg d
    have hy := agmonSource_nonneg G 0 (fun _ => 0) h
    have h1 : 2 * (ε ^ 2 * Ac d) * vecSrc G 0 (fun _ => 0) x₂ ≤
        2 * (ε ^ 2 * Ac d) * (9 / 4 * agmonSource G 0 (fun _ => 0) h) :=
      mul_le_mul_of_nonneg_left hx₂b (by positivity)
    rw [hwM]
    nlinarith
  have hB : agmonSource G 0 (fun _ => 0) Bv ≤
      Kc d * Tg d * ((2 * ε ^ 2 + 2 * (ε ^ 2 * Ac d) * (9 / 4)) * agmonSource G 0 (fun _ => 0) h) := by
    have h1 := src0_commK P.st₁ (liftOp N (dirichletOperator G a ν α₁)⁻¹ *ᵥ wM)
    have h2 := green0_sum P.st₁ wM
    have hKc := Kc_nonneg d
    calc _ ≤ Kc d * (vecGrad G 0 (fun _ => 0) (liftOp N (dirichletOperator G a ν α₁)⁻¹ *ᵥ wM) +
          vecM G 0 (fun _ => 0) (liftOp N (dirichletOperator G a ν α₁)⁻¹ *ᵥ wM)) := h1
      _ ≤ Kc d * (Tg d * vecSrc G 0 (fun _ => 0) wM) :=
          mul_le_mul_of_nonneg_left h2 hKc
      _ ≤ Kc d * (Tg d * ((2 * ε ^ 2 + 2 * (ε ^ 2 * Ac d) * (9 / 4)) *
            agmonSource G 0 (fun _ => 0) h)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hwb (Tg_nonneg d)) hKc
      _ = _ := by ring
  have hC : agmonSource G 0 (fun _ => 0) Cv ≤
      Kc d * ε ^ 2 * (Tg d * (9 / 4 * agmonSource G 0 (fun _ => 0) h)) := by
    have h1 := src0_commK_diff (a := a) (ν := ν) P.st₁.pos P.st₁.weights P.close
      (liftOp N (dirichletOperator G a ν α₂)⁻¹ *ᵥ x₂)
    have h2 := green0_sum P.st₂ x₂
    have hKe : 0 ≤ Kc d * ε ^ 2 := mul_nonneg (Kc_nonneg d) (sq_nonneg ε)
    exact h1.trans (mul_le_mul_of_nonneg_left (h2.trans
      (mul_le_mul_of_nonneg_left hx₂b (Tg_nonneg d))) hKe)
  have hsub := agmonSource_add_le G 0 (fun _ => 0) Fv (Bv + Cv)
  have hadd := agmonSource_add_le G 0 (fun _ => 0) Bv Cv
  have hy := agmonSource_nonneg G 0 (fun _ => 0) h
  unfold Tg at hB hC ⊢
  nlinarith [hsub, hadd, hF, hB, hC]


/-- The constants of the perturbation estimate. -/
noncomputable def nNc (d : ℕ) : ℝ := 4 * (1 + Kc d * Tg d * (Ac d + 1))
noncomputable def nMc (d : ℕ) : ℝ := 18 + Kc d * Tg d * (17 + 18 * Ac d)
noncomputable def nHc (d : ℕ) : ℝ := 8 * nNc d + 160 * nMc d
/-- The perturbation constant `C(d)`: `‖ℓ⁻¹ (Π₁ - Π₂) f‖² ≤ C(d) ε² ‖ℓ f‖²`. -/
noncomputable def pertConst (d : ℕ) : ℝ := Ac d * (80 + 9 * nHc d + 90 * Ac d)

theorem nHc_nonneg (d : ℕ) : 0 ≤ nHc d := by
  unfold nHc nNc nMc
  have := Kc_nonneg d; have := Tg_nonneg d; have := Ac_nonneg d
  positivity

theorem pertConst_nonneg (d : ℕ) : 0 ≤ pertConst d := by
  unfold pertConst
  have := nHc_nonneg d; have := Ac_nonneg d
  positivity

theorem h_diff (P : PertData G a ν α₁ α₂ δ₁ δ₂ ε φ₁ φ₂) (f : G.Ω 1 × Fin N → ℂ) :
    agmonSource G 0 (fun _ => 0)
      ((constraintM (dirichletOperator G a ν α₁) (dirichletOperator G a ν α₁)⁻¹
          (restrictField G φ₁))⁻¹ *ᵥ (constraintN (dirichletOperator G a ν α₁)
            (dirichletOperator G a ν α₁)⁻¹ (restrictField G φ₁) *ᵥ f) -
        (constraintM (dirichletOperator G a ν α₂) (dirichletOperator G a ν α₂)⁻¹
          (restrictField G φ₂))⁻¹ *ᵥ (constraintN (dirichletOperator G a ν α₂)
            (dirichletOperator G a ν α₂)⁻¹ (restrictField G φ₂) *ᵥ f)) ≤
      nHc d * ε ^ 2 * vecSrc G 0 (fun _ => 0) f := by
  set M₁ := constraintM (dirichletOperator G a ν α₁) (dirichletOperator G a ν α₁)⁻¹
    (restrictField G φ₁) with hM₁
  set M₂ := constraintM (dirichletOperator G a ν α₂) (dirichletOperator G a ν α₂)⁻¹
    (restrictField G φ₂) with hM₂
  set N₁ := constraintN (dirichletOperator G a ν α₁) (dirichletOperator G a ν α₁)⁻¹
    (restrictField G φ₁) with hN₁
  set N₂ := constraintN (dirichletOperator G a ν α₂) (dirichletOperator G a ν α₂)⁻¹
    (restrictField G φ₂) with hN₂
  set h₁ := M₁⁻¹ *ᵥ (N₁ *ᵥ f) with hh₁
  set h₂ := M₂⁻¹ *ᵥ (N₂ *ᵥ f) with hh₂
  have hU₁ := constraintM_isUnit P.st₁
  have hU₂ := constraintM_isUnit P.st₂
  have hM₁inv : M₁ * M₁⁻¹ = 1 := Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hU₁)
  have hM₂inv : M₂ * M₂⁻¹ = 1 := Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hU₂)
  have e₁ : M₁ *ᵥ h₁ = N₁ *ᵥ f := by rw [hh₁, mulVec_mulVec, hM₁inv, one_mulVec]
  have e₂ : M₂ *ᵥ h₂ = N₂ *ᵥ f := by rw [hh₂, mulVec_mulVec, hM₂inv, one_mulVec]
  have hlow := constraintM_lower P.st₁ (isAgmonWeight_zero G) le_rfl
    (agmonRate_pos P.st₁.pos).le (h₁ - h₂)
  have hid : M₁ *ᵥ (h₁ - h₂) = (N₁ *ᵥ f - N₂ *ᵥ f) + (M₂ *ᵥ h₂ - M₁ *ᵥ h₂) := by
    rw [Matrix.mulVec_sub, e₁, e₂]; abel
  rw [hid] at hlow
  have hN := N_diff P f
  have hM := M_diff P h₂
  have hh₂b := h_src_le P.st₂ f
  have hadd := agmonSource_add_le G 0 (fun _ => 0) (N₁ *ᵥ f - N₂ *ᵥ f) (M₂ *ᵥ h₂ - M₁ *ᵥ h₂)
  have hX := vecSrc_nonneg G 0 (fun _ => 0) f
  have hnM : 0 ≤ (18 + Kc d * Tg d * (17 + 18 * Ac d)) * ε ^ 2 := by
    have := Kc_nonneg d; have := Tg_nonneg d; have := Ac_nonneg d
    positivity
  have h20 := mul_le_mul_of_nonneg_left hh₂b hnM
  unfold nHc nNc nMc
  nlinarith [hlow, hN, hM, hadd, h20]

theorem pert_main (P : PertData G a ν α₁ α₂ δ₁ δ₂ ε φ₁ φ₂) (f : G.Ω 1 × Fin N → ℂ) :
    vecM G 0 (fun _ => 0)
      (constrainedOp (dirichletOperator G a ν α₁)⁻¹ (restrictField G φ₁) *ᵥ f -
        constrainedOp (dirichletOperator G a ν α₂)⁻¹ (restrictField G φ₂) *ᵥ f) ≤
      pertConst d * ε ^ 2 * vecSrc G 0 (fun _ => 0) f := by
  rw [constrainedOp_mulVec_eq P.st₁, constrainedOp_mulVec_eq P.st₂]
  set h₁ := (constraintM (dirichletOperator G a ν α₁) (dirichletOperator G a ν α₁)⁻¹
          (restrictField G φ₁))⁻¹ *ᵥ (constraintN (dirichletOperator G a ν α₁)
            (dirichletOperator G a ν α₁)⁻¹ (restrictField G φ₁) *ᵥ f) with hh₁
  set h₂ := (constraintM (dirichletOperator G a ν α₂) (dirichletOperator G a ν α₂)⁻¹
          (restrictField G φ₂))⁻¹ *ᵥ (constraintN (dirichletOperator G a ν α₂)
            (dirichletOperator G a ν α₂)⁻¹ (restrictField G φ₂) *ᵥ f) with hh₂
  rw [green_diff P.st₁ P.st₂]
  set x₁ := fieldMul (restrictField G φ₁) *ᵥ h₁ with hx₁
  set x₂ := fieldMul (restrictField G φ₂) *ᵥ h₂ with hx₂
  set w := x₁ - x₂ + liftOp N (dirichletOperator G a ν α₂ - dirichletOperator G a ν α₁) *ᵥ
    (liftOp N (dirichletOperator G a ν α₂)⁻¹ *ᵥ x₂) with hw
  have hG := (green0 P.st₁ w).1
  have hw1 := vecSrc_w_le P x₁ x₂
  have hY₁ := h_src_le P.st₁ f
  have hY₂ := h_src_le P.st₂ f
  have hH := h_diff P f
  have hx₁₂ : x₁ - x₂ = fieldMul (restrictField G (fun x j => φ₁ x j - φ₂ x j)) *ᵥ h₁ +
      fieldMul (restrictField G φ₂) *ᵥ (h₁ - h₂) := by
    rw [← fieldMul_diff, Matrix.mulVec_sub, hx₁, hx₂]; abel
  have hA : vecSrc G 0 (fun _ => 0) (fieldMul (restrictField G (fun x j => φ₁ x j - φ₂ x j)) *ᵥ h₁)
      ≤ ε ^ 2 * agmonSource G 0 (fun _ => 0) h₁ :=
    vecSrc_fieldMul_le_of P.close.bound h₁
  have hB : vecSrc G 0 (fun _ => 0) (fieldMul (restrictField G φ₂) *ᵥ (h₁ - h₂)) ≤
      9 / 4 * agmonSource G 0 (fun _ => 0) (h₁ - h₂) := by
    have := vecSrc_fieldMul_le_of (G := G) (φ' := φ₂) (c := 3 / 2) P.st₂.field.bound (h₁ - h₂)
    linarith
  have hx₂b : vecSrc G 0 (fun _ => 0) x₂ ≤ 9 / 4 * agmonSource G 0 (fun _ => 0) h₂ := by
    have := vecSrc_fieldMul_le_of (G := G) (φ' := φ₂) (c := 3 / 2) P.st₂.field.bound h₂
    rw [hx₂]; linarith
  have hadd := vecSrc_add_le G 0 (fun _ => 0)
    (fieldMul (restrictField G (fun x j => φ₁ x j - φ₂ x j)) *ᵥ h₁)
    (fieldMul (restrictField G φ₂) *ᵥ (h₁ - h₂))
  rw [← hx₁₂] at hadd
  have hAc := Ac_nonneg d
  have hε2 : 0 ≤ ε ^ 2 := sq_nonneg ε
  have hX := vecSrc_nonneg G 0 (fun _ => 0) f
  have hy₁ := agmonSource_nonneg G 0 (fun _ => 0) h₁
  have hy₂ := agmonSource_nonneg G 0 (fun _ => 0) h₂
  have hs1 : vecSrc G 0 (fun _ => 0) w ≤
      (80 + 9 * nHc d + 90 * Ac d) * ε ^ 2 * vecSrc G 0 (fun _ => 0) f := by
    have h2 : 2 * (ε ^ 2 * Ac d) * vecSrc G 0 (fun _ => 0) x₂ ≤
        2 * (ε ^ 2 * Ac d) * (9 / 4 * (20 * vecSrc G 0 (fun _ => 0) f)) :=
      mul_le_mul_of_nonneg_left (hx₂b.trans (mul_le_mul_of_nonneg_left hY₂ (by norm_num)))
        (by positivity)
    have h3 : ε ^ 2 * agmonSource G 0 (fun _ => 0) h₁ ≤
        ε ^ 2 * (20 * vecSrc G 0 (fun _ => 0) f) := mul_le_mul_of_nonneg_left hY₁ hε2
    nlinarith [hw1, hadd, hA, hB, hH, h2, h3]
  calc _ ≤ Ac d * vecSrc G 0 (fun _ => 0) w := hG
    _ ≤ Ac d * ((80 + 9 * nHc d + 90 * Ac d) * ε ^ 2 * vecSrc G 0 (fun _ => 0) f) :=
        mul_le_mul_of_nonneg_left hs1 hAc
    _ = _ := by unfold pertConst; ring

end Diffs


section Quad

variable {G : GeneratingSet d L N₀ k ϱ} {a : ℕ → ℝ} {ν : ℝ}
  {α₁ α₂ : G.Ω 1 → ℂ} {δ₁ δ₂ ε : ℝ} {φ₁ φ₂ : Torus d (N₀ * L ^ k) → Fin N → ℂ}

theorem vecM0_eq (u : G.Ω 1 × Fin N → ℂ) :
    vecM G 0 (fun _ => 0) u = ∑ x : G.Ω 1, ∑ i, ((G.spacing x) ^ 2)⁻¹ * ‖u (x, i)‖ ^ 2 := by
  rw [vecM_eq]
  simp only [cwsq_agmonField_zero]
  rw [Finset.sum_comm]
  rfl

theorem vecSrc0_eq (f : G.Ω 1 × Fin N → ℂ) :
    vecSrc G 0 (fun _ => 0) f = ∑ x : G.Ω 1, ∑ i, G.spacing x ^ 2 * ‖f (x, i)‖ ^ 2 := by
  unfold vecSrc
  simp only [agmonSource_eq]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun i _ => ?_
  simp [comp]

/-- Weighted Cauchy–Schwarz for the quadratic form: `|⟨f, u⟩| ≤ ‖ℓ f‖ ‖ℓ⁻¹ u‖`. -/
theorem norm_star_dot_le (f u : G.Ω 1 × Fin N → ℂ) :
    ‖star f ⬝ᵥ u‖ ≤ Real.sqrt (vecSrc G 0 (fun _ => 0) f) *
      Real.sqrt (vecM G 0 (fun _ => 0) u) := by
  rw [vecM0_eq, vecSrc0_eq]
  calc ‖star f ⬝ᵥ u‖ ≤ ∑ p : G.Ω 1 × Fin N, ‖star (f p) * u p‖ := norm_sum_le _ _
    _ = ∑ p : G.Ω 1 × Fin N, (G.spacing p.1 * ‖f p‖) * (((G.spacing p.1) ^ 2)⁻¹.sqrt * ‖u p‖) := by
        refine Finset.sum_congr rfl fun p _ => ?_
        have hsp : 0 < G.spacing p.1 := spacing_pos G
        rw [norm_mul, norm_star]
        have : Real.sqrt (((G.spacing p.1) ^ 2)⁻¹) = (G.spacing p.1)⁻¹ := by
          rw [← inv_pow, Real.sqrt_sq (by positivity)]
        rw [this]
        field_simp
    _ ≤ Real.sqrt (∑ p : G.Ω 1 × Fin N, (G.spacing p.1 * ‖f p‖) ^ 2) *
          Real.sqrt (∑ p : G.Ω 1 × Fin N, (((G.spacing p.1) ^ 2)⁻¹.sqrt * ‖u p‖) ^ 2) :=
        Real.sum_mul_le_sqrt_mul_sqrt _ _ _
    _ = _ := by
        congr 2
        · rw [Fintype.sum_prod_type]
          exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun i _ => by ring
        · rw [Fintype.sum_prod_type]
          refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun i _ => ?_
          rw [mul_pow, Real.sq_sqrt (by positivity)]

/-- **G-1(d)(2), the constrained term for complex data.**  Let `(α₂, φ₂)` be real data
(`α₂` real, `φ₂` real) obeying the hypotheses of G-2(v), and `(α₁, φ₁)` complex data obeying them
that is `ε`-close to `(α₂, φ₂)` (`φ₁ = φ₂ + i φ_i`, `α₁ = α₂ + i α_i` with `(φ_i, α_i)` of size `ε`).
Then, for every vector field `f` on `Ω₁` (e.g. `f = Q_k^* ψ`),

`Re ⟨f, Π₁ f⟩ ≥ - C_*(d)^{1/2} ε ‖ℓ f‖²`, `C_* = pertConst d`. -/
theorem constrained_re_lower (P : PertData G a ν α₁ α₂ δ₁ δ₂ ε φ₁ φ₂)
    (hα : ∀ x, star (α₂ x) = α₂ x) (hφ : ∀ x i, star (φ₂ x i) = φ₂ x i)
    (f : G.Ω 1 × Fin N → ℂ) :
    -(Real.sqrt (pertConst d) * ε * vecSrc G 0 (fun _ => 0) f) ≤
      (star f ⬝ᵥ (constrainedOp (dirichletOperator G a ν α₁)⁻¹ (restrictField G φ₁) *ᵥ f)).re := by
  set Pi₁ := constrainedOp (dirichletOperator G a ν α₁)⁻¹ (restrictField G φ₁) *ᵥ f with hP1
  set Pi₂ := constrainedOp (dirichletOperator G a ν α₂)⁻¹ (restrictField G φ₂) *ᵥ f with hP2
  have hpsd := constrainedOp_dirichlet_posSemidef G P.st₂.pos P.st₂.mass P.st₂.weights α₂
    P.st₂.alpha hα (φ := restrictField G φ₂) (fun x i => hφ x i)
  have h0 : 0 ≤ (star f ⬝ᵥ Pi₂).re := (Complex.nonneg_iff.1 (hpsd.dotProduct_mulVec_nonneg f)).1
  have hsplit : (star f ⬝ᵥ Pi₁).re = (star f ⬝ᵥ Pi₂).re + (star f ⬝ᵥ (Pi₁ - Pi₂)).re := by
    rw [dotProduct_sub, Complex.sub_re]; ring
  have hCS := norm_star_dot_le f (Pi₁ - Pi₂)
  have hpm := pert_main P f
  have hX := vecSrc_nonneg G 0 (fun _ => 0) f
  have hre : -‖star f ⬝ᵥ (Pi₁ - Pi₂)‖ ≤ (star f ⬝ᵥ (Pi₁ - Pi₂)).re :=
    (abs_le.1 (Complex.abs_re_le_norm _)).1
  have hsq : Real.sqrt (vecM G 0 (fun _ => 0) (Pi₁ - Pi₂)) ≤
      Real.sqrt (pertConst d) * ε * Real.sqrt (vecSrc G 0 (fun _ => 0) f) := by
    have hε := P.close.nonneg
    calc _ ≤ Real.sqrt (pertConst d * ε ^ 2 * vecSrc G 0 (fun _ => 0) f) := Real.sqrt_le_sqrt hpm
      _ = _ := by
        rw [Real.sqrt_mul (mul_nonneg (pertConst_nonneg d) (sq_nonneg ε)), Real.sqrt_mul (pertConst_nonneg d),
          Real.sqrt_sq hε]
  have hfin : ‖star f ⬝ᵥ (Pi₁ - Pi₂)‖ ≤ Real.sqrt (pertConst d) * ε * vecSrc G 0 (fun _ => 0) f := by
    calc _ ≤ _ := hCS
      _ ≤ Real.sqrt (vecSrc G 0 (fun _ => 0) f) *
          (Real.sqrt (pertConst d) * ε * Real.sqrt (vecSrc G 0 (fun _ => 0) f)) :=
          mul_le_mul_of_nonneg_left hsq (Real.sqrt_nonneg _)
      _ = Real.sqrt (pertConst d) * ε *
          (Real.sqrt (vecSrc G 0 (fun _ => 0) f) * Real.sqrt (vecSrc G 0 (fun _ => 0) f)) := by ring
      _ = _ := by rw [Real.mul_self_sqrt hX]
  linarith

end Quad

end Balaban.Multiscale
