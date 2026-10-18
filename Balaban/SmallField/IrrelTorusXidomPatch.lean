/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.SmallField.IrrelTorusXidomPatchGeom
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The small-polymer class-chart comparison

The inverse-rotated full field and the rotated polydisc field both lie in the class chart at
the term's mass. The complex rotation bridge then identifies the class term with its tube
extension at the local datum.
-/

@[expose] public section

namespace Balaban.SmallField.Def6v2

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization Balaban.SmallField
  Balaban.SmallField.Def6 Metric Set Filter

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}
  {P : Consts} {a : ℕ → ℝ} {μ ν : ℝ} {Tm : Terms d L N₁ m₁ k N ϱ} {j : ℕ}
  {y : CTorus d L N₁ m₁ k} {X : Set (CTorus d L N₁ m₁ k)} {S : Finset (Site d)}

open Classical in
/-- The tube extension equals the class term when the datum in the real-centre frame is
locally within the spin radius and its field coordinates satisfy the source tube estimates. -/
theorem trickFnA_shiftTerm_eq_of_local_bounds
    (hcl : SFTermClauses P (xiFieldDom a μ (P.eps d L)) Tm)
    (hBg : BgHyp d L k ϱ a μ) (hν : 0 < ν)
    (hμν : μ * ((L : ℝ) ^ j) ^ 2 ≤ ν) (hνb : ν ≤ 1) (hj1 : 1 ≤ j) (hjk : j ≤ k)
    (hy : Aligned (L ^ j) y) (hX : IsPolyDom P.m₀ j X) (hyX : y ∈ X)
    (hS : ∀ z ∈ X, unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j (z - y) ∈ S)
    {i₀ i₁ : Fin N} (hne : i₁ ≠ i₀) {r : ℝ} (hrad : AnisoRadiusOK d L N P j r)
    (c : Cfg d N S) (hc : c ∈ TubeAniso i₀ ν r S)
    (hlocal : ∀ z, unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j (z - y) ∈ S →
      ∀ i, ‖fieldOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j i₀ S c (z - y) i -
        (Pi.single i₀ 1 : Spin N) i‖ ≤ r)
    (hb : ∀ i, ‖c (Sum.inr i) - (ν : ℂ) * (Pi.single i₀ 1 : Spin N) i‖ ≤ r)
    (hbl : ‖c (Sum.inr i₀) - (ν : ℂ)‖ < r ^ 2) :
    trickFnA i₀ ν r (fun c' : Cfg d N S =>
      Tm.E j y X
        (fun z => fieldOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j i₀ S c' (z - y))
        (hOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) ν S c')) c =
      Tm.E j y X
        (fun z => fieldOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j i₀ S c (z - y))
        (hOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) ν S c) := by
  obtain ⟨R, hR, hRb, hRc⟩ := tubeAniso_witness_isCRot hne hc
  exact trickFnA_shiftTerm_eq_of_full_chart_rot hcl hBg hν hμν hνb hj1 hjk hy hX hyX hS hne hrad c R
    hR hRb hRc hlocal hb hbl.le

end Balaban.SmallField.Def6v2
