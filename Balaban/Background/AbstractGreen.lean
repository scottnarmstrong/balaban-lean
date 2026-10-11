/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Background.Calculus
public import Balaban.Background.Data
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# An abstract Green family (BACKGROUND.md §5.1; LOCALIZATION.md requirement R-B2)

The fixed-point core of Proposition 5.1 (`Balaban/Background/ContractionCore.lean`) uses the
Green's function `G_D(α) = H_D(α)⁻¹` only through three properties: the bound
`‖𝒢(α) f‖_* ≤ B |f|₂` on the polydisc `|α|₂ ≤ γ`, a difference bound replacing the resolvent
identity, and (for analyticity) analyticity of the entries of `𝒢`.  `GreenFamily` records the first
two, for an arbitrary family `𝒢 : (Ω₁ → ℂ) → Matrix`.  The instance
`𝒢(α) = (dirichletOperator G a ν α)⁻¹` is built in `Balaban/Background/Contraction.lean`.

Also here: the rescaling `δα ↦ ℓ² δα`, the norm predicate `Small` (`|δα|₂ ≤ r`), the source
`F_s - δα φ₀` and the defect `g = φ₀ · φ₀ - 1`.
-/

@[expose] public section

namespace Balaban.Background

open Balaban.Multiscale Matrix Finset

variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}

/-- `|δα|₂ ≤ r`. -/
def Small (G : GeneratingSet d L N₀ k ϱ) (δα : G.Ω 1 → ℂ) (r : ℝ) : Prop :=
  ∀ x : G.Ω 1, G.spacing (x : Torus d (N₀ * L ^ k)) ^ 2 * ‖δα x‖ ≤ r

/-- `|g|₂ ≤ C` for a vector field on `Ω₁`, componentwise. -/
abbrev SrcBound (G : GeneratingSet d L N₀ k ϱ) (g : G.Ω 1 × Fin N → ℂ) (C : ℝ) : Prop :=
  ∀ (x : G.Ω 1) (i : Fin N), G.spacing (x : Torus d (N₀ * L ^ k)) ^ 2 * ‖g (x, i)‖ ≤ C

section Rescale

variable {G : GeneratingSet d L N₀ k ϱ}

theorem Small.add {α β : G.Ω 1 → ℂ} {r s : ℝ} (hα : Small G α r) (hβ : Small G β s) :
    Small G (α + β) (r + s) := by
  intro x
  have hp : 0 ≤ G.spacing (x : Torus d (N₀ * L ^ k)) ^ 2 := by positivity
  calc _ ≤ G.spacing (x : Torus d (N₀ * L ^ k)) ^ 2 * (‖α x‖ + ‖β x‖) :=
        mul_le_mul_of_nonneg_left (norm_add_le _ _) hp
    _ = G.spacing (x : Torus d (N₀ * L ^ k)) ^ 2 * ‖α x‖ +
        G.spacing (x : Torus d (N₀ * L ^ k)) ^ 2 * ‖β x‖ := by ring
    _ ≤ _ := add_le_add (hα x) (hβ x)

theorem small_two_mul {δα : G.Ω 1 → ℂ} {r : ℝ} (h : Small G δα r) : Small G (2 * δα) (2 * r) := by
  intro x
  have hp : 0 ≤ G.spacing (x : Torus d (N₀ * L ^ k)) ^ 2 := by positivity
  have := h x
  calc G.spacing (x : Torus d (N₀ * L ^ k)) ^ 2 * ‖(2 * δα) x‖
      = 2 * (G.spacing (x : Torus d (N₀ * L ^ k)) ^ 2 * ‖δα x‖) := by
        simp only [Pi.mul_apply, Pi.ofNat_apply, norm_mul, Complex.norm_ofNat]; ring
    _ ≤ 2 * r := by linarith

variable (G) in
/-- Rescaling `ξ ↦ δα = ξ / ℓ²` (so that `|δα|₂ = ‖ξ‖_∞`). -/
noncomputable def toAlpha (ξ : G.Ω 1 → ℂ) : G.Ω 1 → ℂ :=
  fun x => ξ x / ((G.spacing (x : Torus d (N₀ * L ^ k)) ^ 2 : ℝ) : ℂ)

theorem small_toAlpha (G : GeneratingSet d L N₀ k ϱ) (ξ : G.Ω 1 → ℂ) {r : ℝ}
    (h : ∀ x, ‖ξ x‖ ≤ r) : Small G (toAlpha G ξ) r := by
  intro x
  have hp : 0 < G.spacing (x : Torus d (N₀ * L ^ k)) ^ 2 := by
    have := spacing_pos G (x := (x : Torus d (N₀ * L ^ k))); positivity
  unfold toAlpha
  rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hp.le, mul_div_cancel₀ _ hp.ne']
  exact h x

theorem toAlpha_sub (G : GeneratingSet d L N₀ k ϱ) (ξ ξ' : G.Ω 1 → ℂ) :
    toAlpha G ξ - toAlpha G ξ' = toAlpha G (ξ - ξ') := by
  funext x; simp [toAlpha, sub_div]

theorem toAlpha_zero (G : GeneratingSet d L N₀ k ϱ) : toAlpha G (0 : G.Ω 1 → ℂ) = 0 := by
  funext x; simp [toAlpha]

variable (G) in
/-- The inverse rescaling `δα ↦ ℓ² δα`. -/
noncomputable def ofAlpha (δα : G.Ω 1 → ℂ) : G.Ω 1 → ℂ :=
  fun x => ((G.spacing (x : Torus d (N₀ * L ^ k)) ^ 2 : ℝ) : ℂ) * δα x

theorem toAlpha_ofAlpha (G : GeneratingSet d L N₀ k ϱ) (δα : G.Ω 1 → ℂ) :
    toAlpha G (ofAlpha G δα) = δα := by
  funext x
  have hp : 0 < G.spacing (x : Torus d (N₀ * L ^ k)) ^ 2 := by
    have := spacing_pos G (x := (x : Torus d (N₀ * L ^ k))); positivity
  have : ((G.spacing (x : Torus d (N₀ * L ^ k)) ^ 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  simp only [toAlpha, ofAlpha]
  field_simp

theorem ofAlpha_toAlpha (G : GeneratingSet d L N₀ k ϱ) (ξ : G.Ω 1 → ℂ) :
    ofAlpha G (toAlpha G ξ) = ξ := by
  funext x
  have hp : 0 < G.spacing (x : Torus d (N₀ * L ^ k)) ^ 2 := by
    have := spacing_pos G (x := (x : Torus d (N₀ * L ^ k))); positivity
  have : ((G.spacing (x : Torus d (N₀ * L ^ k)) ^ 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  simp only [toAlpha, ofAlpha]
  field_simp

theorem norm_ofAlpha (G : GeneratingSet d L N₀ k ϱ) (δα : G.Ω 1 → ℂ) (x : G.Ω 1) :
    ‖ofAlpha G δα x‖ = G.spacing (x : Torus d (N₀ * L ^ k)) ^ 2 * ‖δα x‖ := by
  have hp : 0 ≤ G.spacing (x : Torus d (N₀ * L ^ k)) ^ 2 := by positivity
  simp only [ofAlpha, norm_mul, Complex.norm_real, Real.norm_of_nonneg hp]

variable (G) in
/-- The defect `g = φ₀ · φ₀ - 1` on `Ω₁` (BACKGROUND.md (P4)). -/
def gdef (φ₀ : Torus d (N₀ * L ^ k) → Fin N → ℂ) : G.Ω 1 → ℂ :=
  fun x => ∑ i, φ₀ x i * φ₀ x i - 1

/-- The source of the linear problem: `F_s - δα φ₀`. -/
def Fsrc (φ₀ : Torus d (N₀ * L ^ k) → Fin N → ℂ) (Fs : G.Ω 1 × Fin N → ℂ) (δα : G.Ω 1 → ℂ) :
    G.Ω 1 × Fin N → ℂ := fun p => Fs p - δα p.1 * φ₀ p.1 p.2

end Rescale

/-- **An abstract Green family** for Proposition 5.1 (requirement R-B2 of LOCALIZATION.md §3.3).
`𝒢 α` is the Green's function at the multiplier `α`; on the polydisc `|α|₂ ≤ γ` it satisfies

* `bound`: `|𝒢(α) g|₀, |∂𝒢(α) g|₁ ≤ B C` for every source with `|g|₂ ≤ C`;
* `diff`: for `α, α'` in the polydisc with `|α - α'|₂ ≤ Δ`, the difference
  `(𝒢(α) - 𝒢(α')) g` has `|·|₀, |∂·|₁ ≤ B Δ (B C)` (the resolvent identity
  `𝒢(α) - 𝒢(α') = -𝒢(α)(α - α')𝒢(α')` combined with `bound` gives this for `G_D`).

No relation between `𝒢` and any operator is assumed. -/
structure GreenFamily (G : GeneratingSet d L N₀ k ϱ) (N : ℕ)
    (𝒢 : (G.Ω 1 → ℂ) → Matrix (G.Ω 1) (G.Ω 1) ℂ) (B γ : ℝ) : Prop where
  B_nn : 0 ≤ B
  bound : ∀ {α : G.Ω 1 → ℂ}, Small G α γ → ∀ (g : G.Ω 1 × Fin N → ℂ) {C : ℝ}, 0 ≤ C →
    SrcBound G g C → StarBound G (liftOp N (𝒢 α) *ᵥ g) (B * C)
  diff : ∀ {α α' : G.Ω 1 → ℂ}, Small G α γ → Small G α' γ → ∀ (g : G.Ω 1 × Fin N → ℂ) {C Δ : ℝ},
    0 ≤ C → SrcBound G g C → 0 ≤ Δ → Small G (α - α') Δ →
    StarBound G ((liftOp N (𝒢 α) - liftOp N (𝒢 α')) *ᵥ g) (B * (Δ * (B * C)))

end Balaban.Background
