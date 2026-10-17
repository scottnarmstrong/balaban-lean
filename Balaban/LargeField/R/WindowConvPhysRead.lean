module

public import Balaban.LargeField.R.WindowOfHistoryCollar
public import Balaban.LargeField.R.DeltaPsiCollar
public import Balaban.LargeField.R.ActionConvDef

/-!
# The physical datum on an actual history window

P7 p. 501 (2.14)–(2.16) uses the datum inherited from the parent generating set.
This specializes the landed trace theorem to `windowOfHistory`.  It identifies the
window-side reads; comparison with each piece's `locData` requires a common
configuration and transport of its local read sites and bonds.
-/

@[expose] public section

namespace Balaban.LargeField

open Balaban Balaban.Multiscale Balaban.Background Balaban.LargeField.ActionConv

namespace RegionHistory

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K : ℕ}
  (H : RegionHistory S n R k0 K) {k : ℕ} (Z : H.Comp k) {M : ℕ} [NeZero M]
  [NeZero S.L] (g : Geo S n R M) (hkK : k ≤ K) (hW : H.RipeWindow k Z)

/-- The actual window datum reads the inherited parent spin on every action data site,
and any datum with this same trace gives the same window action and source.  This is
the window-side read identity in P7 p. 501 (2.14)–(2.16). -/
theorem windowOfHistory_physical_action_reads {N : ℕ}
    (ψ : BlockV S.d S.L (M * n k) k → EuclideanSpace ℝ (Fin N)) (h : Fin N → ℝ) :
    let W := windowOfHistory H Z g hkK hW
    let hWh := windowOfHistory_hyp hkK hW
    (∀ x ∈ dataSites (W.windowGenSet hWh), ∀ i,
      (physicalWindowData W hWh (windowOfHistory_parentRefines H Z g hkK hW) ψ h).Ψ x i =
        ((ψ (parentBlock W.full x) i : ℝ) : ℂ)) ∧
    (∀ x ∈ (W.windowGenSet hWh).Ω 1, ∀ i,
      (physicalWindowData W hWh (windowOfHistory_parentRefines H Z g hkK hW) ψ h).h x i =
        ((h i : ℝ) : ℂ)) ∧
    ∀ D' : BgData (W.windowGenSet hWh) N,
      (∀ x ∈ dataSites (W.windowGenSet hWh), ∀ i,
        D'.Ψ x i = ((ψ (parentBlock W.full x) i : ℝ) : ℂ)) →
      (∀ x ∈ (W.windowGenSet hWh).Ω 1, ∀ i, D'.h x i = ((h i : ℝ) : ℂ)) →
      ∀ (a : ℕ → ℝ) (ν : ℝ) (φ : (W.windowGenSet hWh).Ω 1 × Fin N → ℂ),
        action (W.windowGenSet hWh) a ν D' φ =
          action (W.windowGenSet hWh) a ν
            (physicalWindowData W hWh (windowOfHistory_parentRefines H Z g hkK hW) ψ h) φ ∧
        source (W.windowGenSet hWh) a ν D' =
          source (W.windowGenSet hWh) a ν
            (physicalWindowData W hWh (windowOfHistory_parentRefines H Z g hkK hW) ψ h) := by
  exact physical_window_action_reads_inherited
    (windowOfHistory H Z g hkK hW) (windowOfHistory_hyp hkK hW)
    (windowOfHistory_parentRefines H Z g hkK hW) ψ h

/-- A trace-identical datum gives exactly the same *restricted* action on every
region of the actual window.  This is the window-side `actionRegionC` read
transport; the local-to-window torus transport is a separate geometric input. -/
theorem windowOfHistory_actionRegionC_congr {N : ℕ}
    (ψ : BlockV S.d S.L (M * n k) k → EuclideanSpace ℝ (Fin N)) (h : Fin N → ℝ)
    (D' : BgData ((windowOfHistory H Z g hkK hW).windowGenSet
      (windowOfHistory_hyp hkK hW)) N)
    (hΨ : ∀ x ∈ dataSites ((windowOfHistory H Z g hkK hW).windowGenSet
      (windowOfHistory_hyp hkK hW)), ∀ i,
      D'.Ψ x i = ((ψ (parentBlock (windowOfHistory H Z g hkK hW).full x) i : ℝ) : ℂ))
    (hh : ∀ x ∈ ((windowOfHistory H Z g hkK hW).windowGenSet
      (windowOfHistory_hyp hkK hW)).Ω 1, ∀ i, D'.h x i = ((h i : ℝ) : ℂ))
    (X : Region ((windowOfHistory H Z g hkK hW).windowGenSet
      (windowOfHistory_hyp hkK hW))) (a : ℕ → ℝ) (ν : ℝ)
    (φ : ((windowOfHistory H Z g hkK hW).windowGenSet
      (windowOfHistory_hyp hkK hW)).Ω 1 × Fin N → ℂ) :
    actionRegionC X a ν D' φ = actionRegionC X a ν
      (physicalWindowData (windowOfHistory H Z g hkK hW) (windowOfHistory_hyp hkK hW)
        (windowOfHistory_parentRefines H Z g hkK hW) ψ h) φ := by
  let W := windowOfHistory H Z g hkK hW
  let hWh : (windowOfHistory H Z g hkK hW).Hyp := windowOfHistory_hyp hkK hW
  let D := physicalWindowData W hWh (windowOfHistory_parentRefines H Z g hkK hW) ψ h
  have hD : D' = D := by
    apply BgData.ext'
    · funext x i
      by_cases hx : x ∈ dataSites (W.windowGenSet hWh)
      · rw [hΨ x hx i, physicalWindowData_Ψ W hWh
          (windowOfHistory_parentRefines H Z g hkK hW) ψ h hx,
          inheritedField_eq_parentBlock]
      · rw [D'.Ψ_zero x hx, D.Ψ_zero x hx]
    · funext x i
      by_cases hx : x ∈ (W.windowGenSet hWh).Ω 1
      · rw [hh x hx i, physicalWindowData_h W hWh
          (windowOfHistory_parentRefines H Z g hkK hW) ψ h hx]
      · rw [D'.h_zero x hx, D.h_zero x hx]
  rw [hD]

end RegionHistory

end Balaban.LargeField
