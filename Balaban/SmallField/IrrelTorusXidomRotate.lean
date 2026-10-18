/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.SmallField.IrrelTorusXidomDefect

/-!
# Comparing the class term with its tube extension through the class domain

The class rotation clause applies when full extensions of both configurations lie in the
same-mass class chart. This lemma records the exact domain gate for that application.
-/

@[expose] public section

namespace Balaban.SmallField.Def6v2

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization Balaban.SmallField
  Balaban.SmallField.Def6

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}
  {P : Consts} {a : ℕ → ℝ} {μ ν : ℝ} {Tm : Terms d L N₁ m₁ k N ϱ} {j : ℕ}
  {y : CTorus d L N₁ m₁ k} {X : Set (CTorus d L N₁ m₁ k)} {S : Finset (Site d)}

open Classical in
/-- The class term and its anisotropic tube extension agree at a configuration `c` of the tube
whose datum is within the spin radius on the blocks of `X` and whose source satisfies the
polydisc bounds (the complex rotation invariance along the two-stage Cayley path,
`shiftTerm_rotA_bd`, relates `c` to the polydisc point `R c`). -/
theorem trickFnA_shiftTerm_eq_of_full_chart_rot
    (hcl : SFTermClauses P (xiFieldDom a μ (P.eps d L)) Tm)
    (hBg : BgHyp d L k ϱ a μ) (hν : 0 < ν)
    (hμν : μ * ((L : ℝ) ^ j) ^ 2 ≤ ν) (hνb : ν ≤ 1) (hj1 : 1 ≤ j) (hjk : j ≤ k)
    (hy : Aligned (L ^ j) y) (hX : IsPolyDom P.m₀ j X) (hyX : y ∈ X)
    (hS : ∀ z ∈ X, unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j (z - y) ∈ S)
    {i₀ i₁ : Fin N} (hne : i₁ ≠ i₀) {r : ℝ} (hrad : AnisoRadiusOK d L N P j r)
    (c : Cfg d N S) (R : Matrix (Fin N) (Fin N) ℂ) (hR : IsCRot R)
    (hRb : EntryBd N R) (hRc : rotCfgL R S c ∈ polyAniso i₀ ν r S)
    (hlocal : ∀ z, unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j (z - y) ∈ S →
      ∀ i, ‖fieldOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j i₀ S c (z - y) i -
        (Pi.single i₀ 1 : Spin N) i‖ ≤ r)
    (hb : ∀ i, ‖c (Sum.inr i) - (ν : ℂ) * (Pi.single i₀ 1 : Spin N) i‖ ≤ r)
    (hbl : ‖c (Sum.inr i₀) - (ν : ℂ)‖ ≤ r ^ 2) :
    trickFnA i₀ ν r (fun c' : Cfg d N S =>
      Tm.E j y X (fun z => fieldOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j i₀ S c' (z - y))
        (hOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) ν S c')) c =
      Tm.E j y X (fun z => fieldOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j i₀ S c (z - y))
        (hOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) ν S c) := by
  let F : Cfg d N S → ℂ := fun c' =>
    Tm.E j y X (fun z => fieldOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j i₀ S c' (z - y))
      (hOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) ν S c')
  change trickFnA i₀ ν r F c = F c
  have hT := tubeHypA_shiftTerm hcl hBg hν hμν hνb hj1 hjk hy hX hyX hS hne hrad
  rw [hT.trickFnA_eq hR.1 hRb hRc]
  obtain ⟨hr0, hr1, δ, hδ0, hδc0, hδc1, hε, hrδ⟩ := hrad
  have hB0 : 0 ≤ rotB N := by unfold rotB; positivity
  have h40 : ∀ i k, ‖R i k‖ ≤ rotB N := fun i k => by
    have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast Fin.pos i₀
    exact (entryBd_bound hRb i k).trans (by unfold rotB; nlinarith)
  exact shiftTerm_rotA_bd hcl hBg hν hμν hνb hj1 hjk hy hX hyX hS i₀ hδ0 hδc0 hδc1 hr0 hr1 hB0 hrδ
    hε hR.1 h40 hb hbl (fun i => (polyAniso_inr hRc hr0 hr1 i).le)
    (polyAniso_inr_self hRc).le rfl hlocal (fun z _ i => fieldOf_sub_le_poly hRc hr0.le (z - y) i)

end Balaban.SmallField.Def6v2
