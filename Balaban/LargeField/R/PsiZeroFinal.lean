/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.PsiZeroHessRef
public import Balaban.LargeField.R.PsiZeroSolve

/-!
# Lemma III.3.3, unconditional: existence, uniqueness, the solution `ψ⁰_k` and its equivariance

The cited expansion estimate `PsiZeroInput` is now a theorem under the actual-step geometry (1.1)
(`psiZeroInput_of_geometry`); the existence and uniqueness theorem `psiZero_exists_unique`, the solution
`psiZero` and its `O(N)`-equivariance `psiZero_equivariant` therefore carry the geometry as hypotheses (typing and
source data of the step) and no longer an estimate.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open Balaban Balaban.Multiscale Balaban.Background Matrix

section Final

variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ} (G : GeneratingSet d L N₀ k ϱ) (a : ℕ → ℝ)
  [NeZero N]

/-- **Lemma III.3.3, existence and uniqueness (unconditional)**: under the geometry of the actual step there are
`K₆, c₁₁ > 0` such that for `0 < δ ≤ c₁₁` and `ψ_k ∈ Ψ̃(X ∖ Z₀; δ)` the variational problem (2.34) has exactly one
solution in `Ψ̃(X; K₆ δ)`. -/
theorem psiZero_exists_unique {D : ℕ} (hd : 2 ≤ d) (hk : 1 ≤ k) (b0 : Torus d (N₀ * L ^ (k - k)))
    (w : Fin d → ℕ) (hw1 : ∀ i, 1 ≤ w i) (hwD : ∀ i, w i ≤ D) (hm : D + 2 ≤ N₀ * L ^ (k - k))
    {X : Set (Torus d (N₀ * L ^ (k - k)))} (hXreg : box b0 w ∪ shellOut (box b0 w) ⊆ X)
    (hΩ : OverTop G (box b0 w ∪ shellOut (box b0 w)))
    (hdata : ∀ x ∈ dataSites G, jBlock d L N₀ k k x ∈ X) (H : BgHyp d L k ϱ a 0) :
    ∃ K c11 : ℝ, 0 < K ∧ 0 < c11 ∧ ∀ δ : ℝ, 0 < δ → δ ≤ c11 → ∀ ψk : BlockField d L N₀ k N,
      TubeOn G (X \ box b0 w) δ ψk → ∃! ψ, PsiZeroSol G a b0 w X (K * δ) ψk ψ :=
  psiZero_exists_unique_of_input G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H
    (psiZeroInput_of_geometry H hk b0 w hw1 hwD hm hXreg hΩ hdata)

section Solution

variable (N)

variable {D : ℕ} (hd : 2 ≤ d) (hk : 1 ≤ k) (b0 : Torus d (N₀ * L ^ (k - k))) (w : Fin d → ℕ)
  (hw1 : ∀ i, 1 ≤ w i) (hwD : ∀ i, w i ≤ D) (hm : D + 2 ≤ N₀ * L ^ (k - k))
  {X : Set (Torus d (N₀ * L ^ (k - k)))} (hXreg : box b0 w ∪ shellOut (box b0 w) ⊆ X)
  (hΩ : OverTop G (box b0 w ∪ shellOut (box b0 w)))
  (hdata : ∀ x ∈ dataSites G, jBlock d L N₀ k k x ∈ X) (H : BgHyp d L k ϱ a 0)

/-- The constant `K₆` of Lemma III.3.3 (chosen from `psiZero_exists_unique`). -/
noncomputable def psiZeroK : ℝ :=
  (psiZero_exists_unique (N := N) G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H).choose

/-- The constant `c₁₁` of Lemma III.3.3 (chosen from `psiZero_exists_unique`). -/
noncomputable def psiZeroC11 : ℝ :=
  (psiZero_exists_unique (N := N) G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H).choose_spec.choose

include hd hk hw1 hwD hm hXreg hΩ hdata H in
theorem psiZeroK_pos : 0 < psiZeroK N G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H :=
  (psiZero_exists_unique (N := N) G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H).choose_spec.choose_spec.1

include hd hk hw1 hwD hm hXreg hΩ hdata H in
theorem psiZeroC11_pos : 0 < psiZeroC11 N G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H :=
  (psiZero_exists_unique (N := N) G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H).choose_spec.choose_spec.2.1

include hd hk hw1 hwD hm hXreg hΩ hdata H in
theorem psiZero_existsUnique {δ : ℝ} (hδ : 0 < δ)
    (hδc : δ ≤ psiZeroC11 N G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H) {ψk : BlockField d L N₀ k N}
    (hψk : TubeOn G (X \ box b0 w) δ ψk) :
    ∃! ψ, PsiZeroSol G a b0 w X (psiZeroK N G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H * δ) ψk ψ :=
  (psiZero_exists_unique (N := N) G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H).choose_spec.choose_spec.2.2 δ hδ hδc
    ψk hψk

/-- **`ψ⁰_k`** (Lemma III.3.3): the unique solution of (2.34) in `Ψ̃(X; K₆ δ)`. -/
noncomputable def psiZero {δ : ℝ} (hδ : 0 < δ)
    (hδc : δ ≤ psiZeroC11 N G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H) {ψk : BlockField d L N₀ k N}
    (hψk : TubeOn G (X \ box b0 w) δ ψk) : BlockField d L N₀ k N :=
  psiZeroOf G a (psiZero_existsUnique N G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H hδ hδc hψk)

include hd hk hw1 hwD hm hXreg hΩ hdata H in
/-- **Characterization of `ψ⁰_k`**: it solves (2.34) in `Ψ̃(X; K₆ δ)` and every solution equals it. -/
theorem psiZero_spec {δ : ℝ} (hδ : 0 < δ)
    (hδc : δ ≤ psiZeroC11 N G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H) {ψk : BlockField d L N₀ k N}
    (hψk : TubeOn G (X \ box b0 w) δ ψk) :
    PsiZeroSol G a b0 w X (psiZeroK N G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H * δ) ψk
        (psiZero N G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H hδ hδc hψk) ∧
      ∀ ψ, PsiZeroSol G a b0 w X (psiZeroK N G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H * δ) ψk ψ →
        ψ = psiZero N G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H hδ hδc hψk :=
  psiZeroOf_spec G a (psiZero_existsUnique N G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H hδ hδc hψk)

include hd hk hw1 hwD hm hXreg hΩ hdata H in
/-- **`O(N)`-equivariance of `ψ⁰_k`** (Lemma III.3.3): for real orthogonal `Q`, `ψ⁰_k(Q ψ_k) = Q ψ⁰_k(ψ_k)`. -/
theorem psiZero_equivariant {δ : ℝ} (hδ : 0 < δ)
    (hδc : δ ≤ psiZeroC11 N G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H) {ψk : BlockField d L N₀ k N}
    (hψk : TubeOn G (X \ box b0 w) δ ψk) {Q : Matrix (Fin N) (Fin N) ℝ} (hQ : Qᵀ * Q = 1)
    (hψk' : TubeOn G (X \ box b0 w) δ (rotBlock Q ψk)) :
    psiZero N G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H hδ hδc hψk' =
      rotBlock Q (psiZero N G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H hδ hδc hψk) :=
  psiZeroOf_rot G a hQ _ _

end Solution

end Final

end Balaban.LargeField
