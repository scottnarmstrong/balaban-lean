/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Multiscale.ConstraintComm
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The constraint sandwich (GREEN.md G-2(v), §4.5a)

Weighted norms of vector fields and the bridge to the scalar Agmon bounds.
-/

@[expose] public section

namespace Balaban.Multiscale

open Matrix Finset

variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}

section Bridge

variable (G : GeneratingSet d L N₀ k ϱ)

/-- The `i`-th component of a vector field on `Ω₁`. -/
def comp (f : G.Ω 1 × Fin N → ℂ) (i : Fin N) : G.Ω 1 → ℂ := fun z => f (z, i)

/-- The weighted source norm `‖ℓ w f‖²` of a vector field (sum over the components). -/
noncomputable def vecSrc (ε : ℝ) (r : Torus d (N₀ * L ^ k) → ℝ) (f : G.Ω 1 × Fin N → ℂ) : ℝ :=
  ∑ i, agmonSource G ε r (comp G f i)

theorem vecSrc_nonneg (ε : ℝ) (r : Torus d (N₀ * L ^ k) → ℝ) (f : G.Ω 1 × Fin N → ℂ) :
    0 ≤ vecSrc G ε r f :=
  Finset.sum_nonneg fun _ _ => agmonSource_nonneg G ε r _

theorem svec_eq (s : G.Ω 1 × Fin N → ℂ) (y : Torus d (N₀ * L ^ k)) (i : Fin N) :
    svec G s y i = zeroExt (G.Ω 1) (comp G s i) y := rfl

theorem vecM_eq (ε : ℝ) (r : Torus d (N₀ * L ^ k) → ℝ) (s : G.Ω 1 × Fin N → ℂ) :
    vecM G ε r s = ∑ i, cwsq G (agmonField G ε r (comp G s i)) := by
  unfold vecM wsq cwsq
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [← Finset.mul_sum]
  congr 1
  simp only [norm_agmonField, mul_pow]
  rw [← Finset.mul_sum, vn_sq]
  rfl

theorem vecGrad_eq (ε : ℝ) (r : Torus d (N₀ * L ^ k) → ℝ) (s : G.Ω 1 × Fin N → ℂ) :
    vecGrad G ε r s = ∑ i, wGrad G ε r (comp G s i) := by
  unfold vecGrad wGrad
  rw [Finset.sum_comm (s := (Finset.univ : Finset (Fin N)))]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.sum_comm (s := (Finset.univ : Finset (Fin N)))]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [← Finset.mul_sum, Finset.sum_add_distrib, vn_sq, vn_sq]
  rfl

end Bridge

section Mult

variable (G : GeneratingSet d L N₀ k ϱ) (ε : ℝ) (r : Torus d (N₀ * L ^ k) → ℝ)

theorem agmonSource_eq (f : G.Ω 1 → ℂ) :
    agmonSource G ε r f =
      ∑ x : G.Ω 1, G.spacing x ^ 2 * Real.exp (ε * r x) ^ 2 * ‖f x‖ ^ 2 := by
  unfold agmonSource
  rw [Green.sum_eq_sum_subtype (G.Ω 1) _ (fun i hi => by simp [zeroExt_not_mem _ _ hi])]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [zeroExt_mem, norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le, mul_pow]
  ring

/-- Multiplication by a bounded function. -/
theorem agmonSource_mul_le (m f : G.Ω 1 → ℂ) {c : ℝ} (hm : ∀ x, ‖m x‖ ≤ c) :
    agmonSource G ε r (fun x => m x * f x) ≤ c ^ 2 * agmonSource G ε r f := by
  rw [agmonSource_eq, agmonSource_eq, Finset.mul_sum]
  refine Finset.sum_le_sum fun x _ => ?_
  have hc : 0 ≤ c := (norm_nonneg _).trans (hm x)
  rw [norm_mul, mul_pow]
  have h2 : ‖m x‖ ^ 2 ≤ c ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hm x) 2
  have h3 : 0 ≤ G.spacing x ^ 2 * Real.exp (ε * r x) ^ 2 * ‖f x‖ ^ 2 := by positivity
  nlinarith [mul_le_mul_of_nonneg_right h2 h3]

variable {G ε r}

/-- Multiplication `s ↦ (φ₀ᵢ s)ᵢ` is bounded by `|φ₀| ≤ 3/2` in the weighted source norm. -/
theorem vecSrc_fieldMul_le {δ : ℝ} {φ : Torus d (N₀ * L ^ k) → Fin N → ℂ}
    (hφ : IsConstraintField G δ φ) (s : G.Ω 1 → ℂ) :
    vecSrc G ε r (fieldMul (restrictField G φ) *ᵥ s) ≤ 9 / 4 * agmonSource G ε r s := by
  unfold vecSrc
  simp only [agmonSource_eq]
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_le_sum fun x _ => ?_
  have hx := hφ.bound x x.2
  have e : ∀ i, comp G (fieldMul (restrictField G φ) *ᵥ s) i x = φ x i * s x := fun i => by
    simp only [comp]; rw [fieldMul_mulVec]; rfl
  simp only [e, norm_mul, mul_pow]
  have h1 : ∑ i, ‖φ x i‖ ^ 2 = vn (φ x) ^ 2 := (vn_sq _).symm
  have h2 : vn (φ x) ^ 2 ≤ (3 / 2) ^ 2 := pow_le_pow_left₀ (vn_nonneg _) hx 2
  have h3 : 0 ≤ G.spacing x ^ 2 * Real.exp (ε * r x) ^ 2 * ‖s x‖ ^ 2 := by positivity
  calc ∑ i, G.spacing x ^ 2 * Real.exp (ε * r x) ^ 2 * (‖φ x i‖ ^ 2 * ‖s x‖ ^ 2)
      = (∑ i, ‖φ x i‖ ^ 2) * (G.spacing x ^ 2 * Real.exp (ε * r x) ^ 2 * ‖s x‖ ^ 2) := by
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun i _ => by ring
    _ ≤ (3 / 2) ^ 2 * (G.spacing x ^ 2 * Real.exp (ε * r x) ^ 2 * ‖s x‖ ^ 2) := by
        rw [h1]; exact mul_le_mul_of_nonneg_right h2 h3
    _ = _ := by ring

theorem agmonSource_fieldMul_transpose_le {δ : ℝ} {φ : Torus d (N₀ * L ^ k) → Fin N → ℂ}
    (hφ : IsConstraintField G δ φ) (f : G.Ω 1 × Fin N → ℂ) :
    agmonSource G ε r ((fieldMul (restrictField G φ))ᵀ *ᵥ f) ≤ 9 / 4 * vecSrc G ε r f := by
  unfold vecSrc
  simp only [agmonSource_eq]
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_le_sum fun x _ => ?_
  have hx := hφ.bound x x.2
  have e : ((fieldMul (restrictField G φ))ᵀ *ᵥ f) x = ∑ i, φ x i * f (x, i) :=
    fieldMul_transpose_mulVec _ _ _
  rw [e]
  have h1 : ‖∑ i, φ x i * f (x, i)‖ ≤ vn (φ x) * vn (fun i => f (x, i)) :=
    norm_dot_le (φ x) (fun i => f (x, i))
  have h2 : ‖∑ i, φ x i * f (x, i)‖ ^ 2 ≤ (3 / 2 * vn (fun i => f (x, i))) ^ 2 := by
    refine pow_le_pow_left₀ (norm_nonneg _) (h1.trans ?_) 2
    exact mul_le_mul_of_nonneg_right hx (vn_nonneg _)
  have h3 : vn (fun i => f (x, i)) ^ 2 = ∑ i, ‖comp G f i x‖ ^ 2 := vn_sq _
  have h4 : 0 ≤ G.spacing x ^ 2 * Real.exp (ε * r x) ^ 2 := by positivity
  calc G.spacing x ^ 2 * Real.exp (ε * r x) ^ 2 * ‖∑ i, φ x i * f (x, i)‖ ^ 2
      ≤ G.spacing x ^ 2 * Real.exp (ε * r x) ^ 2 * (3 / 2 * vn (fun i => f (x, i))) ^ 2 :=
        mul_le_mul_of_nonneg_left h2 h4
    _ = 9 / 4 * ∑ i, G.spacing x ^ 2 * Real.exp (ε * r x) ^ 2 * ‖comp G f i x‖ ^ 2 := by
        rw [← Finset.mul_sum, ← h3]; ring

end Mult

section Neumann

variable (G : GeneratingSet d L N₀ k ϱ)

/-- `|a + b|² ≤ 2 |a|² + 2 |b|²` for the weighted source norm. -/
theorem agmonSource_add_le (ε : ℝ) (r : Torus d (N₀ * L ^ k) → ℝ) (u v : G.Ω 1 → ℂ) :
    agmonSource G ε r (u + v) ≤ 2 * agmonSource G ε r u + 2 * agmonSource G ε r v := by
  simp only [agmonSource_eq, Pi.add_apply]
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun x _ => ?_
  have h := norm_add_le (u x) (v x)
  have h2 : ‖u x + v x‖ ^ 2 ≤ 2 * ‖u x‖ ^ 2 + 2 * ‖v x‖ ^ 2 := by
    nlinarith [sq_nonneg (‖u x‖ - ‖v x‖), norm_nonneg (u x), norm_nonneg (v x),
      norm_nonneg (u x + v x)]
  have h0 : 0 ≤ G.spacing x ^ 2 * Real.exp (ε * r x) ^ 2 := by positivity
  nlinarith [mul_le_mul_of_nonneg_left h2 h0]

/-- The smallness constant `C_E = 2 + 473 d² (10/c + 4/c²)` of the Neumann argument. -/
noncomputable def smallnessConst (d : ℕ) : ℝ :=
  2 + 473 * (d : ℝ) ^ 2 * (10 / poincareConst d + 4 / poincareConst d ^ 2)

/-- The standing hypotheses of the constraint sandwich (G-2(v)). -/
structure Standing (G : GeneratingSet d L N₀ k ϱ) (a : ℕ → ℝ) (ν : ℝ) (α : G.Ω 1 → ℂ)
    (δ : ℝ) (φ : Torus d (N₀ * L ^ k) → Fin N → ℂ) : Prop where
  pos : 0 < d
  mass : 0 ≤ ν
  weights : IsAdmissibleWeights k a
  alpha : ∀ x, ‖α x‖ ≤ coerciveConst d / (2 * (G.spacing x) ^ 2)
  field : IsConstraintField G δ φ
  nonneg : 0 ≤ δ
  small : δ ^ 2 * smallnessConst d ≤ 1 / 4

variable {G}

theorem poincareConst_inv_nonneg (hd : 0 < d) : 0 ≤ 10 / poincareConst d + 4 / poincareConst d ^ 2 := by
  have := poincareConst_pos hd
  positivity

end Neumann

section GreenVec

variable {G : GeneratingSet d L N₀ k ϱ} {a : ℕ → ℝ} {ν : ℝ} {α : G.Ω 1 → ℂ} {δ : ℝ}
  {φ : Torus d (N₀ * L ^ k) → Fin N → ℂ}

theorem comp_liftOp (A : Matrix (G.Ω 1) (G.Ω 1) ℂ) (g : G.Ω 1 × Fin N → ℂ) (i : Fin N) :
    comp G (liftOp N A *ᵥ g) i = A *ᵥ comp G g i := by
  funext x
  exact liftOp_mulVec A g x i

/-- The Agmon bounds for `Ĝ g` (componentwise `G_D(α) g_i`). -/
theorem green_vec_bounds (St : Standing G a ν α δ φ) {r : Torus d (N₀ * L ^ k) → ℝ}
    (hr : IsAgmonWeight G r) {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ agmonRate d)
    (g : G.Ω 1 × Fin N → ℂ) :
    vecM G ε r (liftOp N (dirichletOperator G a ν α)⁻¹ *ᵥ g) ≤
        4 / poincareConst d ^ 2 * vecSrc G ε r g ∧
      vecGrad G ε r (liftOp N (dirichletOperator G a ν α)⁻¹ *ᵥ g) ≤
        10 / poincareConst d * vecSrc G ε r g := by
  have hu : ∀ i, dirichletOperator G a ν α *ᵥ comp G (liftOp N (dirichletOperator G a ν α)⁻¹ *ᵥ g) i
      = comp G g i := by
    intro i
    rw [comp_liftOp]
    exact dirichletOperator_mulVec_inv G St.pos St.mass St.weights α St.alpha _
  refine ⟨?_, ?_⟩
  · rw [vecM_eq, vecSrc, Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ =>
      agmon_wsq_le G St.pos St.mass St.weights α St.alpha hr hε0 hε1 (hu i)
  · rw [vecGrad_eq, vecSrc, Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ =>
      agmon_wgrad_le G St.pos St.mass St.weights α St.alpha hr hε0 hε1 (hu i)

end GreenVec

section Neumann2

variable {G : GeneratingSet d L N₀ k ϱ} {a : ℕ → ℝ} {ν : ℝ} {α : G.Ω 1 → ℂ} {δ : ℝ}
  {φ : Torus d (N₀ * L ^ k) → Fin N → ℂ}

theorem constraintM_mulVec (s : G.Ω 1 → ℂ) :
    s - constraintM (dirichletOperator G a ν α) (dirichletOperator G a ν α)⁻¹
        (restrictField G φ) *ᵥ s =
      (fun x : G.Ω 1 => (1 - ∑ i, φ x i * φ x i) * s x) +
        commK (dirichletOperator G a ν α) (restrictField G φ) *ᵥ
          (liftOp N (dirichletOperator G a ν α)⁻¹ *ᵥ (fieldMul (restrictField G φ) *ᵥ s)) := by
  unfold constraintM
  have e1 : (commK (dirichletOperator G a ν α) (restrictField G φ) *
        liftOp N (dirichletOperator G a ν α)⁻¹ * fieldMul (restrictField G φ)) *ᵥ s =
      commK (dirichletOperator G a ν α) (restrictField G φ) *ᵥ
        (liftOp N (dirichletOperator G a ν α)⁻¹ *ᵥ (fieldMul (restrictField G φ) *ᵥ s)) := by
    rw [mulVec_mulVec, mulVec_mulVec, Matrix.mul_assoc]
  have e2 : ((fieldMul (restrictField G φ))ᵀ * fieldMul (restrictField G φ)) *ᵥ s =
      (fieldMul (restrictField G φ))ᵀ *ᵥ (fieldMul (restrictField G φ) *ᵥ s) := by
    rw [mulVec_mulVec]
  rw [sub_mulVec, e1, e2]
  funext x
  simp only [Pi.sub_apply, Pi.add_apply]
  have h1 : ((fieldMul (restrictField G φ))ᵀ *ᵥ (fieldMul (restrictField G φ) *ᵥ s)) x =
      (∑ i, φ x i * φ x i) * s x := by
    rw [fieldMul_transpose_mulVec, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => by rw [fieldMul_mulVec]; simp [restrictField]; ring
  rw [h1]
  ring

variable (St : Standing G a ν α δ φ) {r : Torus d (N₀ * L ^ k) → ℝ} (hr : IsAgmonWeight G r)
  {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ agmonRate d)

include St hr hε0 hε1

/-- **The Neumann estimate.** `‖ℓ w (s - M s)‖² ≤ δ² C_E ‖ℓ w s‖²`. -/
theorem constraintM_error_le (s : G.Ω 1 → ℂ) :
    agmonSource G ε r (s - constraintM (dirichletOperator G a ν α) (dirichletOperator G a ν α)⁻¹
        (restrictField G φ) *ᵥ s) ≤ δ ^ 2 * smallnessConst d * agmonSource G ε r s := by
  rw [constraintM_mulVec]
  refine (agmonSource_add_le G ε r _ _).trans ?_
  have hA : agmonSource G ε r (fun x : G.Ω 1 => (1 - ∑ i, φ x i * φ x i) * s x) ≤
      δ ^ 2 * agmonSource G ε r s := by
    refine agmonSource_mul_le G ε r _ s (c := δ) fun x => ?_
    rw [norm_sub_rev]
    exact St.field.sq x x.2
  have hK := agmonSource_commK_le G St.pos St.weights ν α St.field.toIsSmoothField St.nonneg hr hε0 hε1
    (liftOp N (dirichletOperator G a ν α)⁻¹ *ᵥ (fieldMul (restrictField G φ) *ᵥ s))
  obtain ⟨hM, hGr⟩ := green_vec_bounds St hr hε0 hε1 (fieldMul (restrictField G φ) *ᵥ s)
  have hΦ := vecSrc_fieldMul_le (ε := ε) (r := r) St.field s
  have hc0 := poincareConst_pos St.pos
  have hd1 : (0 : ℝ) ≤ (d : ℝ) ^ 2 := by positivity
  have hδ2 : 0 ≤ δ ^ 2 := sq_nonneg δ
  have hS0 := agmonSource_nonneg G ε r s
  have hV0 := vecSrc_nonneg G ε r (fieldMul (restrictField G φ) *ᵥ s)
  have hsum : vecGrad G ε r (liftOp N (dirichletOperator G a ν α)⁻¹ *ᵥ
      (fieldMul (restrictField G φ) *ᵥ s)) + vecM G ε r (liftOp N (dirichletOperator G a ν α)⁻¹ *ᵥ
      (fieldMul (restrictField G φ) *ᵥ s)) ≤
      (10 / poincareConst d + 4 / poincareConst d ^ 2) *
        (9 / 4 * agmonSource G ε r s) := by
    have := mul_le_mul_of_nonneg_left hΦ (poincareConst_inv_nonneg St.pos)
    calc _ ≤ 10 / poincareConst d * vecSrc G ε r (fieldMul (restrictField G φ) *ᵥ s) +
          4 / poincareConst d ^ 2 * vecSrc G ε r (fieldMul (restrictField G φ) *ᵥ s) := by linarith
      _ = (10 / poincareConst d + 4 / poincareConst d ^ 2) *
          vecSrc G ε r (fieldMul (restrictField G φ) *ᵥ s) := by ring
      _ ≤ _ := this
  have hB := hK.trans (mul_le_mul_of_nonneg_left hsum (by positivity))
  unfold smallnessConst
  have hCg := poincareConst_inv_nonneg St.pos
  nlinarith [mul_nonneg hd1 (mul_nonneg hδ2 (mul_nonneg hCg hS0))]

/-- `‖ℓ w s‖² ≤ 4 ‖ℓ w M s‖²`: the weighted lower bound for `M = φ₀² - K(φ₀) Ĝ φ₀`. -/
theorem constraintM_lower (s : G.Ω 1 → ℂ) :
    agmonSource G ε r s ≤ 4 * agmonSource G ε r
      (constraintM (dirichletOperator G a ν α) (dirichletOperator G a ν α)⁻¹
        (restrictField G φ) *ᵥ s) := by
  set Ms := constraintM (dirichletOperator G a ν α) (dirichletOperator G a ν α)⁻¹
    (restrictField G φ) *ᵥ s with hMs
  have h1 := constraintM_error_le St hr hε0 hε1 s
  have h2 : s = Ms + (s - Ms) := by abel
  have h3 := agmonSource_add_le G ε r Ms (s - Ms)
  rw [← h2] at h3
  have h4 : δ ^ 2 * smallnessConst d * agmonSource G ε r s ≤ 1 / 4 * agmonSource G ε r s :=
    mul_le_mul_of_nonneg_right St.small (agmonSource_nonneg G ε r s)
  have h5 : agmonSource G ε r (s - Ms) ≤ 1 / 4 * agmonSource G ε r s := h1.trans h4
  linarith

end Neumann2

section Unit

variable {G : GeneratingSet d L N₀ k ϱ} {a : ℕ → ℝ} {ν : ℝ} {α : G.Ω 1 → ℂ} {δ : ℝ}
  {φ : Torus d (N₀ * L ^ k) → Fin N → ℂ}

theorem isAgmonWeight_zero (G : GeneratingSet d L N₀ k ϱ) : IsAgmonWeight G (fun _ => 0) where
  bond := fun x x' _ _ _ => by simpa using G.bondCost_nonneg x x'
  block := fun _ _ _ _ _ _ _ => by simp

theorem agmonSource_zero_eq (s : G.Ω 1 → ℂ) :
    agmonSource G 0 (fun _ => 0) s = ∑ x : G.Ω 1, G.spacing x ^ 2 * ‖s x‖ ^ 2 := by
  rw [agmonSource_eq]
  simp

theorem eq_zero_of_agmonSource_zero {s : G.Ω 1 → ℂ} (h : agmonSource G 0 (fun _ => 0) s ≤ 0) :
    s = 0 := by
  rw [agmonSource_zero_eq] at h
  funext x
  have hnn : ∀ y ∈ (Finset.univ : Finset (G.Ω 1)), 0 ≤ G.spacing y ^ 2 * ‖s y‖ ^ 2 :=
    fun y _ => by positivity
  have := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 (le_antisymm h (Finset.sum_nonneg hnn)) x
    (Finset.mem_univ x)
  have hsp : 0 < G.spacing x := spacing_pos G
  have : ‖s x‖ ^ 2 = 0 := by
    rcases mul_eq_zero.1 this with h0 | h0
    · exact absurd h0 (by positivity)
    · exact h0
  simpa using this

/-- **`M = φ₀² - K(φ₀) Ĝ φ₀` is invertible** (so `φ₀ · G φ₀ = G M` is invertible, G-2(v)). -/
theorem constraintM_isUnit (St : Standing G a ν α δ φ) :
    IsUnit (constraintM (dirichletOperator G a ν α) (dirichletOperator G a ν α)⁻¹
      (restrictField G φ)) := by
  rw [← Matrix.mulVec_injective_iff_isUnit]
  intro s s' hss
  have hlin : constraintM (dirichletOperator G a ν α) (dirichletOperator G a ν α)⁻¹
      (restrictField G φ) *ᵥ (s - s') = 0 := by
    rw [Matrix.mulVec_sub, hss, sub_self]
  have h := constraintM_lower St (isAgmonWeight_zero G) (le_refl (0 : ℝ))
    (agmonRate_pos St.pos).le (s - s')
  rw [hlin] at h
  have h0 : agmonSource G 0 (fun _ => 0) (0 : G.Ω 1 → ℂ) = 0 := by
    rw [agmonSource_zero_eq]; simp
  rw [h0, mul_zero] at h
  have := eq_zero_of_agmonSource_zero h
  exact sub_eq_zero.1 this

end Unit

section Pi

variable {G : GeneratingSet d L N₀ k ϱ} {a : ℕ → ℝ} {ν : ℝ} {α : G.Ω 1 → ℂ} {δ : ℝ}
  {φ : Torus d (N₀ * L ^ k) → Fin N → ℂ}

theorem agmonSource_sub_le (G : GeneratingSet d L N₀ k ϱ) (ε : ℝ)
    (r : Torus d (N₀ * L ^ k) → ℝ) (u v : G.Ω 1 → ℂ) :
    agmonSource G ε r (u - v) ≤ 2 * agmonSource G ε r u + 2 * agmonSource G ε r v := by
  simp only [agmonSource_eq, Pi.sub_apply]
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun x _ => ?_
  have h2 : ‖u x - v x‖ ^ 2 ≤ 2 * ‖u x‖ ^ 2 + 2 * ‖v x‖ ^ 2 := by
    have h := norm_sub_le (u x) (v x)
    nlinarith [sq_nonneg (‖u x‖ - ‖v x‖), norm_nonneg (u x), norm_nonneg (v x),
      norm_nonneg (u x - v x)]
  have h0 : 0 ≤ G.spacing x ^ 2 * Real.exp (ε * r x) ^ 2 := by positivity
  nlinarith [mul_le_mul_of_nonneg_left h2 h0]

theorem dirichlet_mul_inv (St : Standing G a ν α δ φ) :
    dirichletOperator G a ν α * (dirichletOperator G a ν α)⁻¹ = 1 :=
  Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1
    (dirichletOperator_isUnit G St.pos St.mass St.weights α St.alpha))

theorem dirichlet_inv_mul (St : Standing G a ν α δ φ) :
    (dirichletOperator G a ν α)⁻¹ * dirichletOperator G a ν α = 1 :=
  Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1
    (dirichletOperator_isUnit G St.pos St.mass St.weights α St.alpha))

variable (St : Standing G a ν α δ φ) {r : Torus d (N₀ * L ^ k) → ℝ} (hr : IsAgmonWeight G r)
  {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ agmonRate d)

include St hr hε0 hε1

theorem constraintN_src_le (f : G.Ω 1 × Fin N → ℂ) :
    agmonSource G ε r (constraintN (dirichletOperator G a ν α) (dirichletOperator G a ν α)⁻¹
      (restrictField G φ) *ᵥ f) ≤ 5 * vecSrc G ε r f := by
  unfold constraintN
  rw [sub_mulVec, ← mulVec_mulVec]
  refine (agmonSource_sub_le G ε r _ _).trans ?_
  have h1 := agmonSource_fieldMul_transpose_le (ε := ε) (r := r) St.field f
  have hK := agmonSource_commK_le G St.pos St.weights ν α St.field.toIsSmoothField St.nonneg hr hε0 hε1
    (liftOp N (dirichletOperator G a ν α)⁻¹ *ᵥ f)
  obtain ⟨hM, hGr⟩ := green_vec_bounds St hr hε0 hε1 f
  have hc0 := poincareConst_pos St.pos
  have hCg := poincareConst_inv_nonneg St.pos
  have hV0 := vecSrc_nonneg G ε r f
  have hsum : vecGrad G ε r (liftOp N (dirichletOperator G a ν α)⁻¹ *ᵥ f) +
      vecM G ε r (liftOp N (dirichletOperator G a ν α)⁻¹ *ᵥ f) ≤
      (10 / poincareConst d + 4 / poincareConst d ^ 2) * vecSrc G ε r f := by
    linarith
  have hB := hK.trans (mul_le_mul_of_nonneg_left hsum (by positivity : (0 : ℝ) ≤ 105 * d ^ 2 * δ ^ 2))
  have hsm := St.small
  unfold smallnessConst at hsm
  have hd1 : (0 : ℝ) ≤ (d : ℝ) ^ 2 := by positivity
  have hδ2 : 0 ≤ δ ^ 2 := sq_nonneg δ
  have hq : 0 ≤ (d : ℝ) ^ 2 * δ ^ 2 * (10 / poincareConst d + 4 / poincareConst d ^ 2) := by positivity
  have hkey : 210 * ((d : ℝ) ^ 2 * δ ^ 2 * (10 / poincareConst d + 4 / poincareConst d ^ 2)) ≤ 1 / 2 := by
    nlinarith
  nlinarith [mul_le_mul_of_nonneg_right hkey hV0]

/-- **G-2(v), weighted `L²` form.**  For the constrained operator `Π = Ĝ φ₀ [φ₀ · Ĝ φ₀]⁻¹ φ₀ · Ĝ`
of (1.8′) built from `G_D(α)` and `0 ≤ ε ≤ ε₀`, `w = exp (ε r)`:
`‖ℓ⁻¹ w Π f‖² ≤ (180 / c²) ‖ℓ w f‖²` and `‖w ∂ Π f‖² ≤ (450 / c) ‖ℓ w f‖²`. -/
theorem constrained_weighted_bounds (f : G.Ω 1 × Fin N → ℂ) :
    vecM G ε r (constrainedOp (dirichletOperator G a ν α)⁻¹ (restrictField G φ) *ᵥ f) ≤
        180 / poincareConst d ^ 2 * vecSrc G ε r f ∧
      vecGrad G ε r (constrainedOp (dirichletOperator G a ν α)⁻¹ (restrictField G φ) *ᵥ f) ≤
        450 / poincareConst d * vecSrc G ε r f := by
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
  have hsrc : agmonSource G ε r h ≤ 20 * vecSrc G ε r f := by
    have := constraintM_lower St hr hε0 hε1 h
    rw [hMh] at this
    have h5 := constraintN_src_le St hr hε0 hε1 f
    linarith
  have hPi : constrainedOp (dirichletOperator G a ν α)⁻¹ (restrictField G φ) *ᵥ f =
      liftOp N (dirichletOperator G a ν α)⁻¹ *ᵥ (fieldMul (restrictField G φ) *ᵥ h) := by
    rw [constrainedOp_eq (dirichlet_mul_inv St) (dirichlet_inv_mul St), hh]
    rw [← mulVec_mulVec, ← mulVec_mulVec, ← mulVec_mulVec]
  rw [hPi]
  obtain ⟨hM, hGr⟩ := green_vec_bounds St hr hε0 hε1 (fieldMul (restrictField G φ) *ᵥ h)
  have hΦ := vecSrc_fieldMul_le (ε := ε) (r := r) St.field h
  have hc0 := poincareConst_pos St.pos
  have hV0 := vecSrc_nonneg G ε r f
  refine ⟨?_, ?_⟩
  · calc _ ≤ 4 / poincareConst d ^ 2 * vecSrc G ε r (fieldMul (restrictField G φ) *ᵥ h) := hM
      _ ≤ 4 / poincareConst d ^ 2 * (9 / 4 * agmonSource G ε r h) :=
          mul_le_mul_of_nonneg_left hΦ (by positivity)
      _ ≤ 4 / poincareConst d ^ 2 * (9 / 4 * (20 * vecSrc G ε r f)) := by
          gcongr
      _ = _ := by ring
  · calc _ ≤ 10 / poincareConst d * vecSrc G ε r (fieldMul (restrictField G φ) *ᵥ h) := hGr
      _ ≤ 10 / poincareConst d * (9 / 4 * agmonSource G ε r h) :=
          mul_le_mul_of_nonneg_left hΦ (by positivity)
      _ ≤ 10 / poincareConst d * (9 / 4 * (20 * vecSrc G ε r f)) := by
          gcongr
      _ = _ := by ring

end Pi

end Balaban.Multiscale
