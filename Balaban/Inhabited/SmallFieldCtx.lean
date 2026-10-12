/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.SmallField.RenormAnisoInhabited
public import Balaban.SmallField.RenormTermwiseCtx
public import Balaban.SmallField.Def6AvgTube
public import Balaban.SmallField.RenormClassTube
import Mathlib.Tactic.Positivity

/-!
# Inhabitation witnesses for `CtxTw`, `TubeHyp`, `TubeHypA`

* `CtxTw`: the one-polymer family `constTerms d N a` (polymer `{0}`, distance `0`, constant term
  `a` with `‖a‖ ≤ E₀`), the constant configuration `ψ ≡ e_{i₀}`, `b = ν e_{i₀}`, the trivial
  frame.  The term is constant and the polymer family is a single polymer: this is a witness for
  the hypothesis set, degenerate in the sense that the effective action is a constant.
* `TubeHyp`, `TubeHypA`: any constant function (analytic, rotation invariant).
-/

@[expose] public section

open Metric Set

namespace Balaban.Inhabited

open Balaban.SmallField

variable {d N : ℕ}

theorem latFlip_zero (μ : Fin d) : latFlip μ (0 : Site d) = 0 := by
  ext ν
  by_cases h : ν = μ <;> simp [latFlip, h]

theorem latSwap_zero (μ ν : Fin d) : latSwap μ ν (0 : Site d) = 0 := by
  ext x; simp [latSwap]

theorem premisesTerm_const (i₀ i₁ : Fin N) (h : i₀ ≠ i₁) (ν ρ E₀ κ A K₀ : ℝ) (a : ℂ)
    (ha : ‖a‖ ≤ E₀) (hA : 0 ≤ A) (hK₀ : 1 ≤ K₀) (Dom : Set ((Site d → Spin N) × Spin N)) :
    PremisesTerm (constTerms d N a) i₀ i₁ ν ρ E₀ κ A K₀ Dom := by
  have hpol : ∀ X ∈ (constTerms d N a).polys, X = {0} := fun X hX => hX
  have hbd : ‖a‖ ≤ E₀ * Real.exp (-κ * 0) := by simpa using ha
  have hfin : Finite ↥(constTerms d N a).polys := Set.finite_singleton _ |>.to_subtype
  refine ⟨h, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro X hX; rw [hpol X hX]; simp
  · intro X _; exact le_rfl
  · intro X hX x hx
    rw [hpol X hX, Finset.mem_singleton] at hx
    subst hx
    simp only [Pi.zero_apply, abs_zero, Finset.sum_const_zero, Int.cast_zero]
    show (0 : ℝ) ≤ A * (1 + 0)
    linarith
  · exact Summable.of_finite
  · have e : (∑' X : ↥(constTerms d N a).polys, wt κ X.1 ((constTerms d N a).dist X.1)) =
        wt κ ({0} : Finset (Site d)) 0 :=
      tsum_singleton (({0} : Finset (Site d))) (fun X => wt κ X 0)
    rw [e]
    simp [wt, hK₀]
  · intro X _; exact analyticOnNhd_const
  · intro X _ c _; exact hbd
  · intro X _ p _; exact hbd
  · intro X _ c _ R _ _ _; rfl
  · intro r hr X hX
    rw [hpol X hX]
    show Finset.image r {0} ∈ ({{0}} : Set (Finset (Site d)))
    rw [Finset.image_singleton]
    rcases hr with ⟨μ, rfl⟩ | ⟨μ, ν, rfl⟩
    · simp [latFlip_zero]
    · simp [latSwap_zero]
  · intro r _ X _ ψ b; rfl

/-- **`CtxTw` is inhabited** for all admissible numerical parameters. -/
theorem ctxTw_nonempty (i₀ i₁ : Fin N) (h : i₀ ≠ i₁) (ν ρ E₀ κ A K₀ σ ε K₂ : ℝ) (a : ℂ)
    (ha : ‖a‖ ≤ E₀) (hA : 0 ≤ A) (hK₀ : 1 ≤ K₀) (hσ : 0 < σ) (hσ1 : σ ≤ 1) (hε : 0 < ε)
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hν : 0 ≤ ν) (hνσ : ν ≤ σ ^ 2)
    (hτ : σ ^ 2 * ε ≤ 1 / 4) (hK₂ : 0 ≤ K₂) :
    Nonempty (CtxTw (constTerms d N a) i₀ i₁ ν ρ E₀ κ A K₀ (univ : Set ((Site d → Spin N) × Spin N))
      (fun _ => Pi.single i₀ 1) ((ν : ℂ) • Pi.single i₀ 1) σ ε K₂ 1 1) := by
  obtain ⟨hD⟩ := nonempty_dataHypAniso (d := d) (N := N) i₀ ν σ ε K₂ hσ.le hε.le hK₂
  have hE₀ : 0 ≤ E₀ := le_trans (norm_nonneg _) ha
  exact ⟨⟨premisesTerm_const i₀ i₁ h ν ρ E₀ κ A K₀ a ha hA hK₀ _, hD.toDataHyp,
    frame_const_single i₀ σ ε (by positivity), hσ, hσ1, hε, hρ, hρ1, hν, hνσ, hE₀, hA, hτ⟩⟩

/-- **`TubeHyp` is inhabited** by every constant function. -/
theorem tubeHyp_const {X : Finset (Site d)} (i₀ : Fin N) (νj ρ : ℝ) (c : ℂ) :
    Def6.TubeHyp (X := X) i₀ νj ρ (fun _ : Cfg d N X => c) where
  analytic := fun _ _ => analyticAt_const
  rot := fun _ _ _ _ _ _ _ _ => rfl

/-- **`TubeHypA` is inhabited** by every constant function. -/
theorem tubeHypA_const {X : Finset (Site d)} (i₀ : Fin N) (νj r : ℝ) (c : ℂ) :
    Def6.TubeHypA (X := X) i₀ νj r (fun _ : Cfg d N X => c) where
  analytic := fun _ _ => analyticAt_const
  rot := fun _ _ _ _ _ _ _ _ => rfl

end Balaban.Inhabited
