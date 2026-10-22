/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Base.BaseChartRot
public import Balaban.LargeField.Base.BaseChartDefectAct
public import Balaban.Fluctuation.InteractionSymmRot
import Mathlib.Tactic.Linarith

/-!
# `O(N)` covariance of the activities of the labels

`chartFe_rot`, `chartTerm_rot`: for a covariant whitening (`W (R u) (R ψ) = R (W u ψ)`) and a covariant
background map (`F (s, R e) = R F (s, e)`, with `rotRaw`), the activity `chartTerm` of a label at the rotated
datum, source and field equals the unrotated one.  `defTerm_rot`: the same for the defect when its form is
invariant.  (The covariance of `Pst` additionally needs the invariance of the block measures.)
-/

@[expose] public section

namespace Balaban.LargeField.Base

open Balaban Balaban.Multiscale Balaban.Localization Balaban.Background Balaban.Fluctuation
  Balaban.LargeField Balaban.SmallField Balaban.Green Balaban.Analysis Matrix

section RotTerm

variable {d L N₁ m₁ N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}

/-- The action of a matrix on the background `(φ, α)` of the chart: on the components of `φ`. -/
def rotBg (R : Matrix (Fin N) (Fin N) ℂ) {ι : Type*} (u : (ι × Fin N → ℂ) × (ι → ℂ)) :
    (ι × Fin N → ℂ) × (ι → ℂ) := (rotVec R u.1, u.2)

/-- **Covariance of the chart exponent as a function of the background.**  If the whitening is
covariant, `W (R u) (R ψ) = R (W u ψ)`, then `V_x(R u; R ψ, R g) = V_x(u; ψ, g)` for `Rᵀ R = 1`. -/
theorem chartFe_rot (G : GeneratingSet d L (N₁ * L ^ m₁) 1 ϱ) (a : ℕ → ℝ) (ν β : ℝ)
    {R : Matrix (Fin N) (Fin N) ℂ} (hR : R.transpose * R = 1) (g ψ : G.Ω 1 × Fin N → ℂ)
    (W : ((G.Ω 1 × Fin N → ℂ) × (G.Ω 1 → ℂ)) → Matrix (G.Ω 1 × Fin N) (G.Ω 1 × Fin N) ℂ)
    (hW : ∀ u, W (rotBg R u) *ᵥ rotVec R ψ = rotVec R (W u *ᵥ ψ)) (x : G.Ω 1)
    (u : (G.Ω 1 × Fin N → ℂ) × (G.Ω 1 → ℂ)) :
    chartFe G a ν β (rotVec R g) (rotVec R ψ) W x (rotBg R u) = chartFe G a ν β g ψ W x u := by
  unfold chartFe
  rw [hW u]
  exact chartSite_rot hR β (fun y i => u.1 (y, i)) _ g _ x

/-- **Covariance of the activity of a label.**  For a covariant whitening and a covariant background
map, `chartTerm` at the rotated datum, source and field equals `chartTerm`. -/
theorem chartTerm_rot (G : GeneratingSet d L (N₁ * L ^ m₁) 1 ϱ) (a : ℕ → ℝ) (ν β : ℝ)
    {R : Matrix (Fin N) (Fin N) ℂ} (hR : R.transpose * R = 1) (g ψ : G.Ω 1 × Fin N → ℂ)
    (W : ((G.Ω 1 × Fin N → ℂ) × (G.Ω 1 → ℂ)) → Matrix (G.Ω 1 × Fin N) (G.Ω 1 × Fin N) ℂ)
    (hW : ∀ u, W (rotBg R u) *ᵥ rotVec R ψ = rotVec R (W u *ᵥ ψ))
    (F : Dec2.DecParams (coverOf G) × RawData d L (N₁ * L ^ m₁) 1 N →
      (G.Ω 1 × Fin N → ℂ) × (G.Ω 1 → ℂ))
    (hF : ∀ s e, F (s, rotRaw R e) = rotBg R (F (s, e))) (m₀ ρs : ℕ)
    (Y : Set (Balaban.Localization.CTorus d L N₁ m₁ 1)) (e : RawData d L (N₁ * L ^ m₁) 1 N) :
    chartTerm G a ν β (rotVec R g) W F m₀ ρs Y (rotRaw R e) (rotVec R ψ) =
      chartTerm G a ν β g W F m₀ ρs Y e ψ := by
  unfold chartTerm
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun Cs _ => ?_
  refine congrArg (fun f => coef f Cs) (funext fun s => ?_)
  rw [hF s e]
  exact chartFe_rot G a ν β hR g ψ W hW x _

/-- **Covariance of the activity of the defect labels** when the defect form is `O(N)`-invariant. -/
theorem defTerm_rot (G : GeneratingSet d L (N₁ * L ^ m₁) 1 ϱ)
    (D : Matrix (G.Ω 1 × Fin N) (G.Ω 1 × Fin N) ℂ) {R : Matrix (Fin N) (Fin N) ℂ}
    (hD : ∀ ψ x, defPt G D (rotVec R ψ) x = defPt G D ψ x) (m₀ r : ℕ)
    (Y : Set (Balaban.Localization.CTorus d L N₁ m₁ 1)) (ψ : G.Ω 1 × Fin N → ℂ) :
    defTerm G D m₀ r Y (rotVec R ψ) = defTerm G D m₀ r Y ψ := by
  unfold defTerm
  exact Finset.sum_congr rfl fun x _ => by simp only [hD]

end RotTerm

end Balaban.LargeField.Base
