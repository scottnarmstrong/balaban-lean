/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.SmallField.IrrelTorusXidomTail
import Mathlib.Tactic.Positivity

/-!
# Large-polymer bound for the tube discrepancy

The class bound controls the actual term, while the tube bound controls its extension. The
large-polymer threshold pays for their possible difference.
-/

@[expose] public section

namespace Balaban.SmallField.Def6v2

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization Balaban.SmallField
  Balaban.SmallField.Def6 Metric Set Filter

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}
  {P : Consts} {a : ℕ → ℝ} {μ ν : ℝ} {Tm : Terms d L N₁ m₁ k N ϱ} {j : ℕ}
  {y : CTorus d L N₁ m₁ k} {X : Set (CTorus d L N₁ m₁ k)} {S : Finset (Site d)}

open Classical in
/-- The discrepancy of the class term and its tube extension is paid by one unit of
polymer decay when the diameter crosses the comparison threshold. -/
theorem shiftTerm_discrepancy_bound_of_large
    (hcl : SFTermClauses P (xiFieldDom a μ (P.eps d L)) Tm)
    (hcr : CRotE P (xiFieldDom a μ (P.eps d L)) Tm)
    (hBg : BgHyp d L k ϱ a μ) (hν : 0 < ν)
    (hμν : μ * ((L : ℝ) ^ j) ^ 2 ≤ ν) (hj1 : 1 ≤ j) (hjk : j ≤ k)
    (hy : Aligned (L ^ j) y) (hX : IsPolyDom P.m₀ j X) (hyX : y ∈ X)
    (hS : ∀ z ∈ X, unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j (z - y) ∈ S)
    {i₀ i₁ : Fin N} (hne : i₁ ≠ i₀) {r : ℝ} (hrad : AnisoRadiusOK d L N P j r)
    (c : Cfg d N S)
    (hchart : ∃ Ψ' h' : Fld d L N₁ m₁ k N,
      (∀ z ∈ X, Ψ' z = fieldOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j i₀ S c (z - y) ∧
        h' z = hOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) ν S c z) ∧
      XiDom (Tm.gs j X) a μ j (P.eps d L j) Ψ' h')
    {ρ : ℝ} (hρ : 0 ≤ ρ) (hlarge : 1 ≤ ρ * (1 + sizeJ P.m₀ j X)) :
    ‖Tm.E j y X
        (fun z => fieldOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j i₀ S c (z - y))
        (hOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) ν S c) -
      trickFnA i₀ ν r (fun c' : Cfg d N S =>
        Tm.E j y X
          (fun z => fieldOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j i₀ S c' (z - y))
          (hOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) ν S c')) c‖ ≤
      12 * Real.exp 1 * P.E₀ * ρ ^ 3 *
        Real.exp (-(P.κ - 1) * sizeJ P.m₀ j X) := by
  let F : Cfg d N S → ℂ := fun c' => Tm.E j y X
    (fun z => fieldOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j i₀ S c' (z - y))
    (hOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) ν S c')
  let M : ℝ := P.E₀ * Real.exp (-P.κ * sizeJ P.m₀ j X)
  have hF : ‖F c‖ ≤ M := by
    obtain ⟨Ψ', h', hag, hXi⟩ := hchart
    change ‖Tm.E j y X _ _‖ ≤ _
    rw [hcl.localE j y X _ Ψ' _ h'
      (fun z hz => ⟨(hag z hz).1.symm, (hag z hz).2.symm⟩)]
    exact hcl.boundE j hj1 hjk y X hX hyX Ψ' h' hXi
  have hM : 0 ≤ M := (norm_nonneg _).trans hF
  have hE₀ : 0 ≤ P.E₀ := by
    exact nonneg_of_mul_nonneg_right
      (by simpa only [M, mul_comm] using hM) (Real.exp_pos _)
  have hT := tubeHypA_shiftTerm hcl hcr hBg hν hμν hj1 hjk hy hX hyX hS hne hrad
  have hExt : ‖trickFnA i₀ ν r F c‖ ≤ M := by
    by_cases hc : c ∈ TubeAniso i₀ ν r S
    · exact hT.trickFnA_bound
        (fun u hu => shiftTerm_norm_le hcl hBg hν hμν hj1 hjk hy hX hyX i₀ hrad hu) hc
    · change ¬ (∃ R : Matrix (Fin N) (Fin N) ℂ,
        IsOrth R ∧ EntryBd N R ∧ rotCfgL R S c ∈ polyAniso i₀ ν r S) at hc
      unfold trickFnA
      simp only [hc, dite_false]
      exact hF
  have hdiff : ‖F c - trickFnA i₀ ν r F c‖ ≤ 2 * M := by
    calc
      _ ≤ ‖F c‖ + ‖trickFnA i₀ ν r F c‖ := norm_sub_le _ _
      _ ≤ M + M := add_le_add hF hExt
      _ = 2 * M := by ring
  have hsz : 0 ≤ sizeJ P.m₀ j X := treeLenCovOne_nonneg _ _ _
  change ‖F c - trickFnA i₀ ν r F c‖ ≤ _
  have htail := discrepancy_tail_le (κ := P.κ) (M := P.E₀) hsz hρ hE₀ hlarge
  have hMexp : 2 * M = 2 * P.E₀ * Real.exp (-P.κ * sizeJ P.m₀ j X) := by
    dsimp [M]
    ring
  rw [hMexp] at hdiff
  exact hdiff.trans htail

end Balaban.SmallField.Def6v2
