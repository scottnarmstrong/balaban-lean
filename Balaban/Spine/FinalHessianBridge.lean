/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Spine.FinalValueBridge
public import Balaban.Green.FinalHessian
public import Balaban.Spine.FinalHessianAlg

/-!
# The Dirichlet operator of the top layer is the fine Hamiltonian

A6-3 (a), step (P1d). For a generating set with `Ω_n = univ` for `1 ≤ n ≤ k` (the single layer `k`),
`fullMatrix G a ν = -Δ + ν + (a_k / L^{2k}) P` is the fine Hamiltonian of the unit lattice
(`Balaban.fineHamiltonian`) rescaled by `L^{-2k}`.
-/

@[expose] public section

open Matrix Balaban Balaban.Multiscale Balaban.Background Balaban.LargeField

namespace Balaban.RootFSpine

variable {d L N₀ k : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}

/-- The layer projection of the top layer, when the top layer is the whole torus. -/
theorem layerProjMatrix_top {G : GeneratingSet d L N₀ k ϱ}
    (hΩ : ∀ n, 1 ≤ n → n ≤ k → G.Ω n = Finset.univ) (hk : 1 ≤ k) :
    layerProjMatrix G k = blockProjMatrix d (N₀ * L ^ k) (L ^ k) (N₀ * L ^ (k - k)) := by
  ext x x'
  have h : ∀ y, y ∈ G.layer k := fun y => by
    simp [GeneratingSet.layer, hΩ k hk le_rfl, G.top]
  simp [layerProjMatrix, h]

theorem layerProjMatrix_of_lt {G : GeneratingSet d L N₀ k ϱ}
    (hΩ : ∀ n, 1 ≤ n → n ≤ k → G.Ω n = Finset.univ) {j : ℕ} (hj : 1 ≤ j) (hjk : j < k) :
    layerProjMatrix G j = 0 := by
  ext x x'
  have h : ∀ y, y ∉ G.layer j := fun y => by
    simp [GeneratingSet.layer, hΩ j hj hjk.le, hΩ (j + 1) (by omega) hjk]
  simp [layerProjMatrix, h]

/-- The multiscale averaging form of a single top layer. -/
theorem avgMatrix_top {G : GeneratingSet d L N₀ k ϱ}
    (hΩ : ∀ n, 1 ≤ n → n ≤ k → G.Ω n = Finset.univ) (hk : 1 ≤ k) (a : ℕ → ℝ) :
    avgMatrix G a = (a k / ((L : ℝ) ^ k) ^ 2) •
      blockProjMatrix d (N₀ * L ^ k) (L ^ k) (N₀ * L ^ (k - k)) := by
  unfold avgMatrix
  rw [Finset.sum_eq_single k]
  · rw [layerProjMatrix_top hΩ hk]
  · intro j hj hne
    obtain ⟨hj1, hjk⟩ := Finset.mem_Icc.1 hj
    rw [layerProjMatrix_of_lt hΩ hj1 (lt_of_le_of_ne hjk hne), smul_zero]
  · intro h; exact absurd (Finset.mem_Icc.2 ⟨hk, le_rfl⟩) h

/-- **The full matrix of the top layer is the rescaled fine Hamiltonian**:
`-Δ + ν + (a_k/L^{2k}) P = L^{-2k} · fineHamiltonian (ν L^{2k}) a_k`. -/
theorem fullMatrix_top {G : GeneratingSet d L N₀ k ϱ}
    (hΩ : ∀ n, 1 ≤ n → n ≤ k → G.Ω n = Finset.univ) (hk : 1 ≤ k) (a : ℕ → ℝ) (ν : ℝ) :
    fullMatrix G a ν = (((L : ℝ) ^ k) ^ 2)⁻¹ •
      fineHamiltonian d (N₀ * L ^ k) (L ^ k) (N₀ * L ^ (k - k)) (ν * ((L : ℝ) ^ k) ^ 2) (a k) := by
  have hN : (((L : ℝ) ^ k) ^ 2) ≠ 0 := by
    have : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
    positivity
  unfold fullMatrix fineHamiltonian
  rw [avgMatrix_top hΩ hk]
  push_cast
  rw [mul_div_cancel_right₀ _ hN, smul_add, smul_smul, smul_smul, inv_mul_cancel₀ hN, one_smul]
  simp [div_eq_inv_mul]

section Transfer

variable {G : GeneratingSet d L N₀ k ϱ} {N : ℕ}

/-- When `Ω₁` is the whole torus, the subtype `Ω₁` is the torus. -/
def omegaEquiv (hmem : ∀ x, x ∈ G.Ω 1) : G.Ω 1 ≃ Torus d (N₀ * L ^ k) :=
  Equiv.subtypeUnivEquiv hmem

/-- A real field on the torus, as a complex field on `Ω₁`. -/
def cplxLift (hmem : ∀ x, x ∈ G.Ω 1) (v : Torus d (N₀ * L ^ k) × Fin N → ℝ) :
    G.Ω 1 × Fin N → ℂ := fun p => ((v (omegaEquiv hmem p.1, p.2) : ℝ) : ℂ)

theorem dirichletOperator_zero_eq (hmem : ∀ x, x ∈ G.Ω 1) (a : ℕ → ℝ) (ν : ℝ) :
    dirichletOperator G a ν 0 =
      ((fullMatrix G a ν).map (algebraMap ℝ ℂ)).submatrix (omegaEquiv hmem) (omegaEquiv hmem) := by
  unfold dirichletOperator Green.restrictOp
  ext x y
  simp [omegaEquiv]

theorem liftOp_submatrix_cplxLift (hmem : ∀ x, x ∈ G.Ω 1) (A : Matrix (Torus d (N₀ * L ^ k))
    (Torus d (N₀ * L ^ k)) ℝ) (v : Torus d (N₀ * L ^ k) × Fin N → ℝ) :
    liftOp N ((A.map (algebraMap ℝ ℂ)).submatrix (omegaEquiv hmem) (omegaEquiv hmem)) *ᵥ
        cplxLift hmem v = cplxLift hmem (spinLift N A *ᵥ v) := by
  funext ⟨x, i⟩
  simp only [cplxLift, liftOp, Matrix.mulVec, dotProduct, Fintype.sum_prod_type, spinLift,
    Matrix.submatrix_apply, Matrix.map_apply, Complex.coe_algebraMap]
  push_cast
  refine (Equiv.sum_comp (omegaEquiv hmem) (fun y => ∑ x₂, (if i = x₂ then
    ((A ((omegaEquiv hmem) x) y : ℝ) : ℂ) else 0) * ((v (y, x₂) : ℝ) : ℂ))).trans ?_
  refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun j _ => ?_
  split_ifs <;> simp

end Transfer

section SpinAlgebra

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {N : ℕ}

/-- For a constant unit direction `e`, `TᵀT = 1` (`T = fieldMul (constVec e)`). -/
theorem fieldMul_transpose_mul_self {e : Fin N → ℝ} (he : ∑ i, e i ^ 2 = 1) :
    (fieldMul (fun (_ : ι) i => (e i : ℂ)))ᵀ * fieldMul (fun (_ : ι) i => (e i : ℂ)) = 1 := by
  have h2 : ∑ i, (e i : ℂ) * (e i : ℂ) = 1 := by
    have := congrArg (fun r : ℝ => (r : ℂ)) he
    simpa [sq] using this
  ext y z
  simp only [Matrix.mul_apply, Matrix.transpose_apply, fieldMul, Fintype.sum_prod_type,
    Matrix.one_apply]
  by_cases hyz : y = z
  · subst hyz
    simp [h2]
  · simp [hyz, Ne.symm hyz]

/-- **The multiplier of the linearized system at a constant unit direction**: from
`H φ̇ + T α̇ = S`, `Tᵀ φ̇ = 0` and `TᵀT = 1`, `α̇ = Tᵀ S`. -/
theorem response_alpha_of_system {e : Fin N → ℝ} (he : ∑ i, e i ^ 2 = 1) {Hm : Matrix ι ι ℂ}
    {φd S : ι × Fin N → ℂ} {αd : ι → ℂ}
    (E1 : liftOp N Hm *ᵥ φd + fieldMul (fun (_ : ι) i => (e i : ℂ)) *ᵥ αd = S)
    (E2 : (fieldMul (fun (_ : ι) i => (e i : ℂ)))ᵀ *ᵥ φd = 0) :
    αd = (fieldMul (fun (_ : ι) i => (e i : ℂ)))ᵀ *ᵥ S := by
  set T := fieldMul (fun (_ : ι) i => (e i : ℂ)) with hT
  have hcomm : Tᵀ * liftOp N Hm = Hm * Tᵀ := by
    ext x ⟨y, j⟩
    simp [hT, Matrix.mul_apply, Matrix.transpose_apply, fieldMul, liftOp, Fintype.sum_prod_type,
      mul_comm]
  have h := congrArg (fun w => Tᵀ *ᵥ w) E1
  rw [Matrix.mulVec_add, Matrix.mulVec_mulVec φd Tᵀ (liftOp N Hm), hcomm,
    ← Matrix.mulVec_mulVec φd Hm Tᵀ, E2, Matrix.mulVec_zero, zero_add,
    Matrix.mulVec_mulVec αd Tᵀ T, hT, fieldMul_transpose_mul_self he, Matrix.one_mulVec] at h
  exact h

end SpinAlgebra

section Transfer2

variable {G : GeneratingSet d L N₀ k ϱ} {N : ℕ}

/-- The pairing of two transported real fields is the transported dot product. -/
theorem pair_cplxLift (hmem : ∀ x, x ∈ G.Ω 1) (v w : Torus d (N₀ * L ^ k) × Fin N → ℝ) :
    pair G (cplxLift hmem v) (cplxLift hmem w) = ((v ⬝ᵥ w : ℝ) : ℂ) := by
  unfold pair
  rw [dotProduct, Complex.ofReal_sum]
  exact Fintype.sum_equiv (Equiv.prodCongr (omegaEquiv hmem) (Equiv.refl _)) _ _ fun p => by
    simp [cplxLift]; rfl

/-- The projection onto the constant direction `e` acts on transported fields as `projH e`. -/
theorem fieldMul_fieldMul_transpose_cplxLift (hmem : ∀ x, x ∈ G.Ω 1) (e : Fin N → ℝ)
    (v : Torus d (N₀ * L ^ k) × Fin N → ℝ) :
    fieldMul (fun (_ : G.Ω 1) i => (e i : ℂ)) *ᵥ ((fieldMul (fun (_ : G.Ω 1) i => (e i : ℂ)))ᵀ *ᵥ
      cplxLift hmem v) = cplxLift hmem (projH (ι := Torus d (N₀ * L ^ k)) e *ᵥ v) := by
  funext ⟨x, i⟩
  rw [fieldMul_mulVec, fieldMul_transpose_mulVec]
  simp only [cplxLift, projH, Matrix.mulVec, dotProduct, Fintype.sum_prod_type]
  push_cast
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp [apply_ite Complex.ofReal, ite_mul, Finset.sum_ite_eq]
  ring

/-- `L^{-2k}`-rescaled fine Hamiltonians are positive definite. -/
theorem fullMatrix_top_posDef {G : GeneratingSet d L N₀ k ϱ}
    (hΩ : ∀ n, 1 ≤ n → n ≤ k → G.Ω n = Finset.univ) (hk : 1 ≤ k) (hd : 0 < d) (a : ℕ → ℝ)
    (ha : 0 < a k) {ν : ℝ} (hν : 0 ≤ ν) : (fullMatrix G a ν).PosDef := by
  have hLpos : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hN : (0 : ℝ) < ((L : ℝ) ^ k) ^ 2 := by positivity
  rw [fullMatrix_top hΩ hk]
  refine Matrix.PosDef.smul ?_ (inv_pos.2 hN)
  exact fineHamiltonian_posDef (by rw [Nat.mul_comm]; simp)
    (pow_pos (Nat.pos_of_ne_zero (NeZero.ne L)) k) hd (mul_nonneg hν hN.le) ha

theorem fullMatrix_mul_inv {G : GeneratingSet d L N₀ k ϱ}
    (hΩ : ∀ n, 1 ≤ n → n ≤ k → G.Ω n = Finset.univ) (hk : 1 ≤ k) (hd : 0 < d) (a : ℕ → ℝ)
    (ha : 0 < a k) {ν : ℝ} (hν : 0 ≤ ν) : fullMatrix G a ν * (fullMatrix G a ν)⁻¹ = 1 :=
  Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1
    (fullMatrix_top_posDef hΩ hk hd a ha hν).isUnit)

/-- The inverse Dirichlet operator acts on transported fields as the inverse real matrix. -/
theorem liftOp_inv_cplxLift {G : GeneratingSet d L N₀ k ϱ} {N : ℕ}
    (hmem : ∀ x, x ∈ G.Ω 1) {Hr : Matrix (Torus d (N₀ * L ^ k)) (Torus d (N₀ * L ^ k)) ℝ}
    (hHr : Hr * Hr⁻¹ = 1)
    (hHc : IsUnit ((Hr.map (algebraMap ℝ ℂ)).submatrix (omegaEquiv hmem) (omegaEquiv hmem)))
    (v : Torus d (N₀ * L ^ k) × Fin N → ℝ) :
    liftOp N (((Hr.map (algebraMap ℝ ℂ)).submatrix (omegaEquiv hmem) (omegaEquiv hmem))⁻¹) *ᵥ
        cplxLift hmem v = cplxLift hmem (spinLift N Hr⁻¹ *ᵥ v) := by
  have h1 := liftOp_submatrix_cplxLift hmem Hr (spinLift N Hr⁻¹ *ᵥ v)
  rw [Matrix.mulVec_mulVec, ← spinLift_mul, hHr, spinLift_one, Matrix.one_mulVec] at h1
  rw [← h1]
  exact Balaban.Background.liftOp_inv_mulVec hHc _

end Transfer2

section Source

variable {G : GeneratingSet d L N₀ k ϱ} {N : ℕ}

/-- When `Ω₁` is the whole torus, the layer index is `k` and the collar is empty. -/
theorem layerIndex_top {G : GeneratingSet d L N₀ k ϱ}
    (hΩ : ∀ n, 1 ≤ n → n ≤ k → G.Ω n = Finset.univ) (hk : 1 ≤ k) (x : Torus d (N₀ * L ^ k)) :
    G.layerIndex x = k :=
  G.layerIndex_eq hk le_rfl (by simp [GeneratingSet.layer, hΩ k hk le_rfl, G.top])

theorem collar_top {G : GeneratingSet d L N₀ k ϱ}
    (hmem : ∀ x, x ∈ G.Ω 1) (x : Torus d (N₀ * L ^ k)) : x ∉ collar G := fun h =>
  ((mem_collar G).1 h).1 (hmem x)

/-- **The tangent source of a block-lifted datum on the whole torus**:
`Ṡ = (a_k/L^{2k}) · (lift of E)`. -/
theorem source_top (hΩ : ∀ n, 1 ≤ n → n ≤ k → G.Ω n = Finset.univ) (hk : 1 ≤ k)
    (hmem : ∀ x, x ∈ G.Ω 1) (a : ℕ → ℝ) (ν : ℝ) (E : BgData G N)
    (Ustar : Torus d (N₀ * L ^ k) × Fin N → ℝ)
    (hEΨ : ∀ x i, E.Ψ x i = ((Ustar (x, i) : ℝ) : ℂ)) (hEh : ∀ x, E.h x = 0) :
    source G a ν E = cplxLift hmem ((a k / ((L : ℝ) ^ k) ^ 2) • Ustar) := by
  funext ⟨x, i⟩
  simp only [source, qStar, boundaryTerm, hEh, cplxLift, hEΨ, layerIndex_top hΩ hk]
  have hb : ∀ μ : Fin d, ((if (x : Torus d (N₀ * L ^ k)) + Pi.single μ 1 ∈ collar G then
      ((Ustar ((x : Torus d (N₀ * L ^ k)) + Pi.single μ 1, i) : ℝ) : ℂ) else 0) +
      (if (x : Torus d (N₀ * L ^ k)) - Pi.single μ 1 ∈ collar G then
        ((Ustar ((x : Torus d (N₀ * L ^ k)) - Pi.single μ 1, i) : ℝ) : ℂ) else 0)) = 0 :=
    fun μ => by simp [collar_top hmem]
  simp only [hb, Finset.sum_const_zero]
  simp [omegaEquiv]

end Source

section Assembly

variable {G : GeneratingSet d L N₀ k ϱ} {N : ℕ} {a : ℕ → ℝ} {ν : ℝ}

theorem cplxLift_sub (hmem : ∀ x, x ∈ G.Ω 1) (v w : Torus d (N₀ * L ^ k) × Fin N → ℝ) :
    cplxLift hmem (v - w) = cplxLift hmem v - cplxLift hmem w := by
  funext p; simp [cplxLift]

/-- **The second variation at the constant configuration is the final Hessian** (A6-3 (a), P1d):
for the single top layer (`Ω_n = univ`), a tangent datum that is the block lift of `U`, and equal
action and background masses,
`2 · Re secondVariation = L^{k(d-2)} ⟨U, finalHessian U⟩` with the unit-lattice mass `ν L^{2k}`. -/
theorem secondVariation_top (H : BgHyp d L k ϱ a ν)
    (hΩ : ∀ n, 1 ≤ n → n ≤ k → G.Ω n = Finset.univ) (hk : 1 ≤ k) (hd2 : 2 ≤ d)
    {e : Fin N → ℝ} (he : ∑ i, e i ^ 2 = 1) (E : BgData G N)
    (Uv : Torus d (N₀ * L ^ (k - k)) × Fin N → ℝ)
    (hEΨ : ∀ x i, E.Ψ x i = ((Uv (blockMap (L ^ k) (N₀ * L ^ (k - k)) x, i) : ℝ) : ℂ))
    (hEh : ∀ x, E.h x = 0) :
    2 * (secondVariation G a ν ν e E).re =
      ((L : ℝ) ^ k) ^ (d - 2) * (Uv ⬝ᵥ (finalHessian d (N₀ * L ^ k) (L ^ k) (N₀ * L ^ (k - k))
        (ν * ((L : ℝ) ^ k) ^ 2) (a k) e *ᵥ Uv)) := by
  classical
  have hmem : ∀ x, x ∈ G.Ω 1 := fun x => by rw [hΩ 1 le_rfl hk]; exact Finset.mem_univ x
  have hd0 : 0 < d := by omega
  have hapos : 0 < a k := by
    have := (H.weights k hk le_rfl).1; linarith
  set Ustar : Torus d (N₀ * L ^ k) × Fin N → ℝ :=
    fun p => Uv (blockMap (L ^ k) (N₀ * L ^ (k - k)) p.1, p.2) with hUstar
  have hΛ : Ustar = spinLift N (blockPullbackMatrix d (N₀ * L ^ k) (L ^ k) (N₀ * L ^ (k - k))) *ᵥ
      Uv := by
    funext ⟨x, i⟩
    simp only [hUstar, spinLift, blockPullbackMatrix, Matrix.mulVec, dotProduct,
      Fintype.sum_prod_type]
    simp [ite_mul, Finset.sum_ite_eq]
  have hν : 0 ≤ ν := H.mass
  set c : ℝ := a k / ((L : ℝ) ^ k) ^ 2 with hc
  have hS : source G a ν E = cplxLift hmem (c • Ustar) :=
    source_top hΩ hk hmem a ν E Ustar hEΨ hEh
  obtain ⟨φd, αd, hφ, -, -, E1, E2⟩ := const_response E H he
  have hα := response_alpha_of_system he E1 E2
  have hHr : fullMatrix G a ν * (fullMatrix G a ν)⁻¹ = 1 :=
    fullMatrix_mul_inv hΩ hk hd0 a hapos hν
  have hHrU : IsUnit (fullMatrix G a ν) := (fullMatrix_top_posDef hΩ hk hd0 a hapos hν).isUnit
  have hHc := dirichletOperator_zero_eq hmem a ν
  have hHu : IsUnit (dirichletOperator G a ν 0) := by
    rw [hHc, Matrix.isUnit_submatrix_equiv]
    exact hHrU.map (algebraMap ℝ ℂ).mapMatrix
  have hLg : ∀ z, liftOp N ((dirichletOperator G a ν 0)⁻¹) *ᵥ cplxLift hmem z =
      cplxLift hmem (spinLift N (fullMatrix G a ν)⁻¹ *ᵥ z) := by
    intro z
    rw [hHc]
    exact liftOp_inv_cplxLift hmem hHr (by rw [← hHc]; exact hHu) z
  set Pf := projH (ι := Torus d (N₀ * L ^ k)) e with hPf
  have hφ2 : φd = cplxLift hmem (spinLift N (fullMatrix G a ν)⁻¹ *ᵥ ((1 - Pf) *ᵥ (c • Ustar))) := by
    have h1 : liftOp N (dirichletOperator G a ν 0) *ᵥ φd =
        source G a ν E - fieldMul (constVec G e) *ᵥ αd := by
      rw [eq_sub_iff_add_eq]; exact E1
    have h2 : φd = liftOp N ((dirichletOperator G a ν 0)⁻¹) *ᵥ
        (liftOp N (dirichletOperator G a ν 0) *ᵥ φd) :=
      (Balaban.Background.liftOp_inv_mulVec hHu φd).symm
    have hcv : constVec G e = fun _ i => (e i : ℂ) := rfl
    rw [h2, h1, hcv, hα, hS, fieldMul_fieldMul_transpose_cplxLift hmem e (c • Ustar),
      ← cplxLift_sub, hLg, Matrix.sub_mulVec, Matrix.one_mulVec]
  have hE : ∀ x, x ∉ G.Ω 1 → E.Ψ x = 0 := fun x hx => absurd (hmem x) hx
  have hW : actionC G a ν ((bgZero G N).lineAt E 1) 0 =
      (((1 / 2) * c * (Ustar ⬝ᵥ Ustar) : ℝ) : ℂ) := by
    have hp := pair_cplxLift hmem Ustar Ustar
    unfold pair at hp
    rw [Fintype.sum_prod_type] at hp
    rw [actionC_zero_line_eq E hE hEh 1]
    simp only [layerIndex_top hΩ hk, hEΨ]
    push_cast
    rw [← hp, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [mul_assoc]
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    simp only [cplxLift, hUstar, omegaEquiv, hc, Equiv.subtypeUnivEquiv_apply]
    push_cast
    ring
  have hsv : secondVariation G a ν ν e E = (((1 / 2) * c * (Ustar ⬝ᵥ Ustar) - (1 / 2) *
      ((spinLift N (fullMatrix G a ν)⁻¹ *ᵥ ((1 - Pf) *ᵥ (c • Ustar))) ⬝ᵥ (c • Ustar)) : ℝ) : ℂ) := by
    unfold secondVariation
    rw [← hφ, hW, sub_self, hφ2, hS, pair_cplxLift]
    push_cast
    ring
  rw [hsv, Complex.ofReal_re, fullMatrix_top hΩ hk]
  have hNb : 0 < L ^ k := pow_pos (Nat.pos_of_ne_zero (NeZero.ne L)) k
  have hLpos : (0 : ℝ) < ((L : ℝ) ^ k) ^ 2 := by
    have : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
    positivity
  have key := second_variation_quad (d := d) (ℓ := N₀ * L ^ k) (Nb := L ^ k)
    (m := N₀ * L ^ (k - k)) (N := N) (by rw [Nat.sub_self, pow_zero, mul_one, Nat.mul_comm])
    hNb hd2 (νu := ν * ((L : ℝ) ^ k) ^ 2) (a := a k) (mul_nonneg hν hLpos.le) hapos he Uv
  rw [← hΛ] at key
  push_cast at key
  simp only [hc] at *
  linarith

end Assembly

end Balaban.RootFSpine
