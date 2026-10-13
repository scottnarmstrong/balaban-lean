/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.MarkedHatRows
public import Balaban.Inhabited.StepActivityHatWitnessRay

/-!
# Non-vacuity of the masked decoupled tangent

At the landed witness step `hatStep m₁ β p₁ δ` the masked decoupled tangent `markedHatPsiF` over the
block of an arbitrary marked point is defined for every decoupled background, and the
characterization of it holds there: at `t = 0` it is `u • hatPsiF`, and at the sites of the block it
is `(u + t) • hatPsiF`.  No landed instance of the row theorem `hatPsiF_rows` (all its hypotheses at
the witness) exists, so none is given for `markedHatPsiF_rows`.  The marked family of the assembly
is not constructed here.
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization Balaban.Fluctuation

theorem markedHatPsiF_hatStep (m₁ : ℕ) (β p₁ δ : ℝ)
    (z : Torus 3 (9 * 3 ^ m₁ * 3 ^ (1 + 1 - (1 + 1))))
    (cc : ℂ) (F₁ : DecParams (hatStep m₁ β p₁ δ).G' × RawData 3 3 (9 * 3 ^ m₁) (1 + 1) 2 →
      ((hatStep m₁ β p₁ δ).G'.Ω 1 × Fin 2 → ℂ) × ((hatStep m₁ β p₁ δ).G'.Ω 1 → ℂ))
    (u t : ℂ) (s : DecParams (hatStep m₁ β p₁ δ).G') (Θ : RawData 3 3 (9 * 3 ^ m₁) (1 + 1) 2)
    (ψh : unitPts (hatStep m₁ β p₁ δ).G' × Fin 2 → ℂ) :
    markedHatPsiF (hatStep m₁ β p₁ δ).a₁ (hatStep m₁ β p₁ δ).ν (hatStep m₁ β p₁ δ).hG' cc F₁
        ((hatStep m₁ β p₁ δ).blockU z) u 0 s Θ ψh =
      u • hatPsiF _ (hatStep m₁ β p₁ δ).a₁ (hatStep m₁ β p₁ δ).ν (hatStep m₁ β p₁ δ).hG' cc F₁ s Θ ψh ∧
    (∀ (y : CTorus 3 3 9 m₁ (1 + 1)) (i : Fin 2),
      unitPt (hatStep m₁ β p₁ δ).hG' y ∈ (hatStep m₁ β p₁ δ).blockU z →
      markedHatPsiF (hatStep m₁ β p₁ δ).a₁ (hatStep m₁ β p₁ δ).ν (hatStep m₁ β p₁ δ).hG' cc F₁
          ((hatStep m₁ β p₁ δ).blockU z) u t s Θ ψh y i =
        (u + t) * hatPsiF _ (hatStep m₁ β p₁ δ).a₁ (hatStep m₁ β p₁ δ).ν (hatStep m₁ β p₁ δ).hG'
          cc F₁ s Θ ψh y i) :=
  ⟨markedHatPsiF_zero_t _ _ _ _ _ _ _ _, fun _ _ hy => markedHatPsiF_of_mem _ _ _ _ _ _ _ _ _ hy _⟩

end Balaban.Inhabited
