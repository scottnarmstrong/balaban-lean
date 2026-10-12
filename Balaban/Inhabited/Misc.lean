/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Observables.LayerConstants
public import Balaban.Observables.LayerStructure
public import Balaban.Observables.LayerSchur
public import Balaban.Localization.DecoupledFieldClose
public import Balaban.SmallField.RenormNumeric
public import Balaban.SmallField.RenormShape
public import Balaban.LargeField.Background.StepGenSets
public import Balaban.LargeField.Background.Factorization
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Inhabitation witnesses for small hypothesis structures

* `ExponentConstraints` (`exponentConstraints_nonempty`, any `d ≥ 3`);
* `SigPow` (`sigPow_nonempty`, `σ = 1/2`);
* `Localization.DataAgree` (`dataAgree_self`);
* `LargeField.PieceDecomp` (`pieceDecomp_self`: a single piece);
* `LargeField.BoundaryHyp` (`boundaryHyp_empty`: `W = U = Ω = ∅`);
* `SmallField.TermOK` (`termOK_zero`: the zero term);
* `Observables.IsBgAt` (`isBgAt_const`: the constant background);
* `Localization.WSup` (`wSup_zero`: the zero field).
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Multiscale Balaban.Background

/-- **`ExponentConstraints` is inhabited** for every `d ≥ 3`. -/
theorem exponentConstraints_nonempty {d : ℕ} (hd : 3 ≤ d) :
    ∃ γ α₁ ρ₀ ρ₁ ρ₂ : ℝ, Balaban.Observables.ExponentConstraints d γ α₁ ρ₀ ρ₁ ρ₂ := by
  have hd' : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have h1 : ((d : ℝ) - 2) * (1 / (100 * d)) ≤ 1 / 100 := by
    rw [mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have h0 : 0 ≤ ((d : ℝ) - 2) * (1 / (100 * d)) := by
    apply mul_nonneg <;> [linarith; positivity]
  refine ⟨1 / 4, 1 / 4, 1 / 4, 1 / 10, 1 / (100 * d), ?_⟩
  exact
    { ρ₂_pos := by positivity
      ρ₀_pos := by norm_num
      ρ₁_pos := by norm_num
      ρ₁_lt_one := by norm_num
      E1 := by
        rw [mul_one_div, div_le_iff₀ (by positivity)]
        nlinarith
      E2 := by nlinarith
      E3 := by nlinarith
      E4 := by nlinarith
      E5 := le_rfl
      E6 := by linarith
      E7 := by norm_num }

/-- **`SigPow` is inhabited** (`σ = 1/2`, `Sσ = 1/2`, `Tσ = 1/4`). -/
theorem sigPow_nonempty (α₁ : ℝ) :
    ∃ σ Tσ Sσ : ℝ, Balaban.SmallField.SigPow σ α₁ Tσ Sσ :=
  ⟨1 / 2, 1 / 4, 1 / 2, by
    constructor <;> norm_num⟩

section Loc

open Balaban.Localization

variable {d L N₁ m₁ K N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}

/-- **`DataAgree` is inhabited**: a data set agrees with itself. -/
theorem dataAgree_self (G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ)
    (Y : Finset (CTorus d L N₁ m₁ K)) (α₀ : G.Ω 1 → ℂ)
    (φ₀ δΨ : CTorus d L N₁ m₁ K → Fin N → ℂ) (f₁ : G.Ω 1 × Fin N → ℂ) :
    DataAgree G N Y α₀ α₀ φ₀ φ₀ δΨ δΨ f₁ f₁ :=
  ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ => rfl⟩

/-- **`WSup` is inhabited**: the zero field has every sup-bound `V ≥ 0`. -/
theorem wSup_zero (G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ) (ω : CTorus d L N₁ m₁ K → ℝ)
    {V : ℝ} (hV : 0 ≤ V) : WSup G ω (0 : G.Ω 1 × Fin N → ℂ) V := by
  have e : ∀ (y : CTorus d L N₁ m₁ K) (i : Fin N), svec G (0 : G.Ω 1 × Fin N → ℂ) y i = 0 := by
    intro y i
    by_cases hy : y ∈ G.Ω 1
    · rw [svec_of_mem G _ ⟨y, hy⟩ i]; rfl
    · exact svec_of_not_mem G _ hy i
  refine ⟨fun y i => ?_, fun x _ μ i => ?_, fun x _ μ i => ?_, fun x _ i => ?_⟩ <;>
    simpa [e] using hV

end Loc

section Large

open Balaban.LargeField

/-- **`PieceDecomp` is inhabited**: a single piece. -/
theorem pieceDecomp_self {d L N₀ k : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ} (hk : 1 ≤ k)
    (G : GeneratingSet d L N₀ k ϱ) :
    PieceDecomp G (fun _ : Unit => G) :=
  ⟨hk, fun _ _ _ _ => ⟨fun h => ⟨(), h⟩, fun ⟨_, h⟩ => h⟩, fun i j hij => absurd (Subsingleton.elim i j) hij⟩

/-- **`BoundaryHyp` is inhabited** (the degenerate member `W = U = Ω = ∅`). -/
theorem boundaryHyp_empty {d M1 N₁ L k : ℕ} [NeZero L] [NeZero M1] [NeZero N₁] :
    BoundaryHyp (d := d) (M1 := M1) (N₁ := N₁) (L := L) (k := k) ∅ ∅ ∅ :=
  ⟨fun _ _ _ => by simp, fun _ _ _ => by simp, fun _ _ _ => by simp, by simp, by simp⟩

end Large

section Small

/-- **`TermOK` is inhabited**: the zero term. -/
theorem termOK_zero {d N : ℕ} (i₀ : Fin N) (ν : ℝ) {ρ : ℝ} (hρ : 0 < ρ) (X : Finset (Balaban.SmallField.Site d)) :
    Balaban.SmallField.TermOK i₀ ν ρ X (fun _ => (0 : ℂ)) :=
  ⟨hρ, analyticOnNhd_const, fun _ _ _ _ _ _ => rfl⟩

end Small

section Obs

open Balaban.Observables

/-- **`IsBgAt` is inhabited**: the constant background `φ(x; ψ, h) = h`, for a unit vector `h`. -/
theorem isBgAt_const {X Y : Type*} [Fintype Y] [DecidableEq Y] {N : ℕ} (h : Fin N → ℝ)
    (hh : h ⬝ᵥ h = 1) : IsBgAt (X := X) (Y := Y) (fun _ _ h => h) h where
  diff := fun _ => differentiableAt_const _
  value := fun _ => rfl
  sphere := fun _ => Filter.Eventually.of_forall fun _ => hh
  cov := fun _ _ hS => Filter.Eventually.of_forall fun _ => hS.2.symm

end Obs

end Balaban.Inhabited
