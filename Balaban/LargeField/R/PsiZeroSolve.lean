/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.PsiZeroExists
public import Balaban.LargeField.R.DeltaPsiDef

/-!
# Lemma III.3.3: the solution `ψ⁰_k`, its characterization, equivariance, and `PsiZeroSpec`

`psiZeroOf` is the unique solution of (2.34) (defined from the `∃!` statement of
`psiZero_exists_unique_of_input`), `psiZeroOf_spec` characterizes it, `psiZeroOf_rot` is its `O(N)`-equivariance
(the effective action is rotation invariant, `effAction_rot`), and `solveBlockV` assembles it into a block field
(`PsiZeroSpec` is derived in `PsiZeroWindowSpec` / `PsiZeroWindowRipe`; the earlier `psiZeroSpec_of_input` was deleted since its
premises force an empty collar, see `collar_eq_empty_of_overTop`).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open Balaban Balaban.Multiscale Balaban.Background Matrix

section Solve

variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ} (G : GeneratingSet d L N₀ k ϱ) (a : ℕ → ℝ)
  {b0 : Torus d (N₀ * L ^ (k - k))} {w : Fin d → ℕ} {X : Set (Torus d (N₀ * L ^ (k - k)))} {κ : ℝ}
  {ψk : BlockField d L N₀ k N}

/-- **`ψ⁰_k`**, the unique solution of (2.34) in `Ψ̃(X; κ)` (its existence and uniqueness is the hypothesis `h`,
proved in `psiZero_exists_unique_of_input`). -/
noncomputable def psiZeroOf (h : ∃! ψ, PsiZeroSol G a b0 w X κ ψk ψ) : BlockField d L N₀ k N :=
  h.exists.choose

/-- **Characterization of `ψ⁰_k`**: it is a solution of (2.34), and every solution equals it. -/
theorem psiZeroOf_spec (h : ∃! ψ, PsiZeroSol G a b0 w X κ ψk ψ) :
    PsiZeroSol G a b0 w X κ ψk (psiZeroOf G a h) ∧ ∀ ψ, PsiZeroSol G a b0 w X κ ψk ψ → ψ = psiZeroOf G a h :=
  ⟨h.exists.choose_spec, fun _ hψ => h.unique hψ h.exists.choose_spec⟩

theorem psiZeroOf_eq_off (h : ∃! ψ, PsiZeroSol G a b0 w X κ ψk ψ) {z} (hz : z ∉ box b0 w) :
    psiZeroOf G a h z = ψk z :=
  (psiZeroOf_spec G a h).1.2.1 z hz

theorem psiZeroOf_tube (h : ∃! ψ, PsiZeroSol G a b0 w X κ ψk ψ) : TubeOn G X κ (psiZeroOf G a h) :=
  (psiZeroOf_spec G a h).1.1

section Rot

variable {Q : Matrix (Fin N) (Fin N) ℝ}

theorem rn_mulVec (hQ : Qᵀ * Q = 1) (v : Fin N → ℝ) : rn (Q *ᵥ v) = rn v := by
  have h : ∑ i, (Q *ᵥ v) i ^ 2 = ∑ i, v i ^ 2 := by
    have h1 : (Q *ᵥ v) ⬝ᵥ (Q *ᵥ v) = v ⬝ᵥ v :=
      calc (Q *ᵥ v) ⬝ᵥ (Q *ᵥ v) = (v ᵥ* Qᵀ) ⬝ᵥ (Q *ᵥ v) := by rw [vecMul_transpose]
        _ = v ⬝ᵥ (Qᵀ *ᵥ (Q *ᵥ v)) := (dotProduct_mulVec _ _ _).symm
        _ = v ⬝ᵥ v := by rw [mulVec_mulVec, hQ, one_mulVec]
    simpa [dotProduct, pow_two] using h1
  unfold rn; rw [h]

theorem tubeOn_rot (hQ : Qᵀ * Q = 1) {X : Set (Torus d (N₀ * L ^ (k - k)))} {δ : ℝ}
    (ψ : BlockField d L N₀ k N) : TubeOn G X δ (rotBlock Q ψ) ↔ TubeOn G X δ ψ := by
  have e1 : ∀ x x', rn (fun i => liftR (rotBlock Q ψ) x i - liftR (rotBlock Q ψ) x' i) =
      rn (fun i => liftR ψ x i - liftR ψ x' i) := by
    intro x x'
    have : (fun i => liftR (rotBlock Q ψ) x i - liftR (rotBlock Q ψ) x' i) =
        Q *ᵥ (fun i => liftR ψ x i - liftR ψ x' i) := by
      have hs : (fun i => liftR ψ x i - liftR ψ x' i) = liftR ψ x - liftR ψ x' := rfl
      rw [hs, mulVec_sub]; rfl
    rw [this, rn_mulVec hQ]
  have e2 : ∀ z, ∑ i, rotBlock Q ψ z i ^ 2 = ∑ i, ψ z i ^ 2 := by
    intro z
    have := rn_mulVec hQ (ψ z)
    unfold rn at this
    have h0 : 0 ≤ ∑ i, (Q *ᵥ ψ z) i ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
    have h1 : 0 ≤ ∑ i, ψ z i ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
    have := congrArg (· ^ 2) this
    simpa [Real.sq_sqrt h0, Real.sq_sqrt h1, rotBlock] using this
  unfold TubeOn
  simp only [e1, e2]

/-- A rotated solution is a solution of the rotated problem. -/
theorem psiZeroSol_rot (hQ : Qᵀ * Q = 1) {ψ : BlockField d L N₀ k N}
    (h : PsiZeroSol G a b0 w X κ ψk ψ) : PsiZeroSol G a b0 w X κ (rotBlock Q ψk) (rotBlock Q ψ) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨(tubeOn_rot G hQ ψ).2 h1, fun z hz => by simp [rotBlock, h2 z hz], fun ψ' ht hag => ?_⟩
  -- `ψ' = Q (Qᵀ ψ')`
  have hQ' : Q * Qᵀ = 1 := by
    exact mul_eq_one_comm.1 hQ
  have hQt : (Qᵀ)ᵀ * Qᵀ = 1 := by simpa using hQ'
  have hrr : ∀ φ : BlockField d L N₀ k N, rotBlock Q (rotBlock Qᵀ φ) = φ := by
    intro φ; funext z; simp [rotBlock, mulVec_mulVec, hQ']
  have := h3 (rotBlock Qᵀ ψ') ((tubeOn_rot G hQt ψ').2 ht) (fun z hz => by
    show Qᵀ *ᵥ ψ' z = ψk z
    rw [hag z hz]
    show Qᵀ *ᵥ (Q *ᵥ ψk z) = _
    rw [mulVec_mulVec, hQ, one_mulVec])
  calc effAction G a (rotBlock Q ψ) = effAction G a ψ := effAction_rot G hQ ψ
    _ ≤ effAction G a (rotBlock Qᵀ ψ') := this
    _ = effAction G a (rotBlock Q (rotBlock Qᵀ ψ')) := (effAction_rot G hQ _).symm
    _ = effAction G a ψ' := by rw [hrr]

/-- **`O(N)`-equivariance of `ψ⁰_k`** (Lemma III.3.3): for real orthogonal `Q`,
`ψ⁰_k(Q ψ_k) = Q ψ⁰_k(ψ_k)`. -/
theorem psiZeroOf_rot (hQ : Qᵀ * Q = 1) (h : ∃! ψ, PsiZeroSol G a b0 w X κ ψk ψ)
    (h' : ∃! ψ, PsiZeroSol G a b0 w X κ (rotBlock Q ψk) ψ) :
    psiZeroOf G a h' = rotBlock Q (psiZeroOf G a h) :=
  ((psiZeroOf_spec G a h').2 _ (psiZeroSol_rot G a hQ (psiZeroOf_spec G a h).1)).symm

end Rot

section Spec

variable [NeZero N]

/-- The block field `ψ⁰_k` as a field on all blocks of the multiscale lattice: the solution on the `k`-blocks, `ψ`
elsewhere. -/
noncomputable def solveBlockV (ψ : BlockV d L N₀ k → EuclideanSpace ℝ (Fin N))
    (sol : BlockField d L N₀ k N) : BlockV d L N₀ k → EuclideanSpace ℝ (Fin N) :=
  fun b => if h : ∃ z, b = ⟨k, z⟩ then WithLp.toLp 2 (sol h.choose) else ψ b

theorem solveBlockV_k (ψ : BlockV d L N₀ k → EuclideanSpace ℝ (Fin N)) (sol : BlockField d L N₀ k N)
    (z : Torus d (N₀ * L ^ (k - k))) : solveBlockV ψ sol ⟨k, z⟩ = WithLp.toLp 2 (sol z) := by
  have h : ∃ z', (⟨k, z⟩ : BlockV d L N₀ k) = ⟨k, z'⟩ := ⟨z, rfl⟩
  unfold solveBlockV
  simp only [h, dite_true]
  have := h.choose_spec
  have e : h.choose = z := (eq_of_heq (Sigma.mk.inj_iff.1 this).2).symm
  rw [e]

end Spec

end Solve

end Balaban.LargeField
