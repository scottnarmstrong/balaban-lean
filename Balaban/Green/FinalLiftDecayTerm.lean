/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Green.FinalLiftDecayCauchy
public import Balaban.SmallField.Def6v2

/-!
# The Lipschitz bound of the class terms (blocker 5, piece (2))

`SFTermClauses` gives `analyticE` and `boundE` on `Dom.dom`.  If the field domain contains the complex
line through `(Ψ, h)` in the direction `(u, u_h)` up to the radius `ρ > 1`, and `(Ψ', h')` agrees on
`X` with `(Ψ + u, h + u_h)`, then (locality `localE`, Cauchy estimate along the line)
`‖ℰ(y, X; Ψ', h') - ℰ(y, X; Ψ, h)‖ ≤ (2 / ρ) E₀ e^{-κ d_j(X)}`.
-/

@[expose] public section

open Metric Set Balaban Balaban.Multiscale Balaban.Background Balaban.Localization Balaban.SmallField
  Balaban.SmallField.Def6 Balaban.SmallField.Def6v2

namespace Balaban.Green

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}

/-- **Lipschitz bound of a term along a line in the field domain.** -/
theorem norm_E_sub_le_of_line {P : Consts} {Dom : FieldDom d L N₁ m₁ k N ϱ}
    {Tm : Terms d L N₁ m₁ k N ϱ} (hT : SFTermClauses P Dom Tm) {j : ℕ} (hj1 : 1 ≤ j)
    (hjk : j ≤ k) {y : CTorus d L N₁ m₁ k} {X : Set (CTorus d L N₁ m₁ k)}
    (hX : IsPolyDom P.m₀ j X) (hy : y ∈ X) {Ψ h Ψ' h' u uh : Fld d L N₁ m₁ k N} {ρ : ℝ}
    (hρ : 1 < ρ) (hag : ∀ x ∈ X, Ψ' x = Ψ x + u x ∧ h' x = h x + uh x)
    (htube : ∀ t : ℂ, ‖t‖ < ρ → Dom.dom j (Tm.gs j X) (Ψ + t • u) (h + t • uh)) :
    ‖Tm.E j y X Ψ' h' - Tm.E j y X Ψ h‖ ≤ 2 * (P.E₀ * Real.exp (-P.κ * sizeJ P.m₀ j X)) / ρ := by
  have hf := hT.analyticE j hj1 hjk y X hX hy
  have hB : ∀ p ∈ {p : Fld d L N₁ m₁ k N × Fld d L N₁ m₁ k N | Dom.dom j (Tm.gs j X) p.1 p.2},
      ‖Tm.E j y X p.1 p.2‖ ≤ P.E₀ * Real.exp (-P.κ * sizeJ P.m₀ j X) :=
    fun p hp => hT.boundE j hj1 hjk y X hX hy p.1 p.2 hp
  have key := norm_sub_le_of_analytic_step (x := (Ψ, h)) (v := (u, uh)) hρ hf hB (fun t ht => by
    have := htube t ht
    simpa using this)
  have e : Tm.E j y X Ψ' h' = Tm.E j y X (Ψ + u) (h + uh) :=
    hT.localE j y X Ψ' (Ψ + u) h' (h + uh) fun x hx => by
      have := hag x hx
      exact ⟨by simpa using this.1, by simpa using this.2⟩
  rw [e]
  simpa using key

end Balaban.Green
