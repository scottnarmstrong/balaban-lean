/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.PsiZeroSpace
public import Balaban.LargeField.R.PsiZeroTube

/-!
# The variational problem (2.34) and its cited expansion estimates (Lemma III.3.3)

`effOn G a Zf ψk` is the function `ψ_k↾Z₀ ↦ A_k(𝔹_k(U_k); ψ̃_k, φ_k(𝔹_k(U_k); ψ̃_k))` on the perturbation space
`ℝ^{Zf × N}` of the box `Z₀`.  `PsiZeroInput` packages the one cited estimate of P7 (2.35)–(2.38) / P4 (2.24)
that is not proved here: the Hessian of this function (the form `⟨δψ, Δ^{(k)} δψ⟩`) is bounded below by `c ‖δψ‖²`
at every point of a small tube, and its gradient at `ψ_{k,0}` is `O(δ)` (the linear term of (2.36)).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open Balaban Balaban.Multiscale Balaban.Background

section Input

variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}

/-- The finite set of `k`-blocks of the box `Z₀ = box b₀ w`. -/
noncomputable def boxFinset (b0 : Torus d (N₀ * L ^ (k - k))) (w : Fin d → ℕ) :
    Finset (Torus d (N₀ * L ^ (k - k))) :=
  (Set.toFinite (box b0 w)).toFinset

theorem mem_boxFinset {b0 : Torus d (N₀ * L ^ (k - k))} {w : Fin d → ℕ} {z} :
    z ∈ boxFinset (L := L) (N₀ := N₀) (k := k) b0 w ↔ z ∈ box b0 w := by
  simp [boxFinset]

variable (G : GeneratingSet d L N₀ k ϱ) (a : ℕ → ℝ)

/-- **The variational function of (2.34)**: `u ↦ A_k(𝔹_k(U_k); ψ̃, φ_k(𝔹_k(U_k); ψ̃))` for the block field equal to `u`
on `Zf` and to `ψ_k` off `Zf`. -/
noncomputable def effOn (Zf : Finset (Torus d (N₀ * L ^ (k - k)))) (ψk : BlockField d L N₀ k N)
    (u : SuppSpace Zf N) : ℝ :=
  effAction G a (mergeField Zf ψk u)

theorem effOn_merge (Zf : Finset (Torus d (N₀ * L ^ (k - k)))) (ψk : BlockField d L N₀ k N)
    (u : SuppSpace Zf N) : effOn G a Zf (mergeField Zf ψk u) = effOn G a Zf ψk := by
  funext w; simp [effOn, mergeField_mergeField]

variable [NeZero N]

/-- **The cited estimate of P7 (2.35)–(2.38), P4 (2.24)** for the box `Z₀ = box b₀ w` inside the region `X = U^∼_k`:
constants `c > 0`, `Gr ≥ 0`, `η₀ > 0` (depending on `d, L, N, D₀`, not on `ψ_k`, `δ`) such that

* (Hessian, (2.37)) at every block field `ψ` of the tube `Ψ̃(𝔹_k; η)`, `η ≤ η₀`, the second derivative of the
  variational function at `ψ↾Z₀` satisfies `⟨δψ, Δ^{(k)} δψ⟩ ≥ c ‖δψ‖²` for `δψ` supported in `Z₀`;
* (gradient, (2.36)) for `ψ_k ∈ Ψ̃(X ∖ Z₀; δ)`, `δ ≤ η₀`, the derivative of the variational function at the constant
  configuration `ψ₀ = refVec ψ_k Z₀` on `Z₀` has norm `≤ Gr δ`. -/
structure PsiZeroInput (b0 : Torus d (N₀ * L ^ (k - k))) (w : Fin d → ℕ)
    (X : Set (Torus d (N₀ * L ^ (k - k)))) where
  c : ℝ
  Gr : ℝ
  η₀ : ℝ
  c_pos : 0 < c
  Gr_nonneg : 0 ≤ Gr
  η₀_pos : 0 < η₀
  hess : ∀ (ψ : BlockField d L N₀ k N) (η : ℝ), 0 < η → η ≤ η₀ → TubeOn G Set.univ η ψ →
    ∀ v : SuppSpace (boxFinset b0 w) N,
      c * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ (effOn G a (boxFinset b0 w) ψ)) (restrictSupp (boxFinset b0 w) ψ) v v
  grad : ∀ (ψk : BlockField d L N₀ k N) (δ : ℝ), 0 < δ → δ ≤ η₀ → TubeOn G (X \ box b0 w) δ ψk →
    ‖fderiv ℝ (effOn G a (boxFinset b0 w) ψk)
      (constSupp (boxFinset b0 w) (refVec (fun z => eu (ψk z)) (box b0 w)))‖ ≤ Gr * δ

end Input

end Balaban.LargeField
