/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.SmallField.IrrelTorusXidomThreshold
public import Balaban.SmallField.IrrelTorusXidomLarge
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The labelwise tube discrepancy, for both polymer sizes
-/

@[expose] public section

namespace Balaban.SmallField.Def6v2

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization Balaban.SmallField
  Balaban.SmallField.Def6 Metric Set Filter

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}
  {P : Consts} {a : ℕ → ℝ} {μ ν : ℝ} {Tm : Terms d L N₁ m₁ k N ϱ} {j : ℕ}
  {y : CTorus d L N₁ m₁ k} {X : Set (CTorus d L N₁ m₁ k)} {S : Finset (Site d)}

open Classical in
/-- The exact tube discrepancy vanishes on small polymers and is paid by decay on large
ones. The class-chart input is at the same mass as the term. -/
theorem shiftTerm_discrepancy_bound_of_threshold
    (hP : P.Admissible d L)
    (hcl : SFTermClauses P (xiFieldDom a μ (P.eps d L)) Tm)
    (hcr : CRotE P (xiFieldDom a μ (P.eps d L)) Tm)
    (hBg : BgHyp d L k ϱ a μ) (hν : 0 < ν)
    (hμν : μ * ((L : ℝ) ^ j) ^ 2 ≤ ν) (hj1 : 1 ≤ j) (hjk : j ≤ k)
    (hy : Aligned (L ^ j) y) (hX : IsPolyDom P.m₀ j X) (hyX : y ∈ X)
    (hS : ∀ z ∈ X, unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j (z - y) ∈ S)
    (hS' : ∀ s ∈ S, ∃ x ∈ X, Aligned (L ^ j) x ∧
      unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j (x - y) = s)
    {i₀ i₁ : Fin N} (hne : i₁ ≠ i₀) {r : ℝ} (hrad : AnisoRadiusOK d L N P j r)
    {σ ε K₂ q ρ : ℝ} {ψ : Site d → Spin N} {b : Spin N}
    {Dom : Set ((Site d → Spin N) × Spin N)}
    (dat : DataHypAniso Dom ν σ ε K₂ ψ b) (hσε : 0 ≤ σ * ε)
    (hcentre : ∀ i, ‖ψ 0 i - (Pi.single i₀ 1 : Spin N) i‖ ≤ q)
    (hb : ∀ i, ‖b i - (ν : ℂ) * (Pi.single i₀ 1 : Spin N) i‖ ≤ r)
    (hbl : ‖b i₀ - (ν : ℂ)‖ < r ^ 2)
    (hρ : 0 < ρ)
    (hbase : q + diamA d L P.m₀ m₁ * (σ * ε) / ρ ≤ r)
    (hchart : ∃ Ψ' h' : Fld d L N₁ m₁ k N,
      (∀ z ∈ X, Ψ' z = fieldOf (L := L) (N₁ := N₁) (m₁ := m₁)
          (k := k) j i₀ S (pack S ψ b) (z - y) ∧
        h' z = hOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k)
          ν S (pack S ψ b) z) ∧
      XiDom (Tm.gs j X) a μ j (P.eps d L j) Ψ' h') :
    ‖Tm.E j y X
        (fun z => fieldOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j i₀ S
          (pack S ψ b) (z - y))
        (hOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) ν S (pack S ψ b)) -
      trickFnA i₀ ν r (fun c' : Cfg d N S =>
        Tm.E j y X
          (fun z => fieldOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j i₀ S c' (z - y))
          (hOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) ν S c'))
        (pack S ψ b)‖ ≤
      12 * Real.exp 1 * P.E₀ * ρ ^ 3 *
        Real.exp (-(P.κ - 1) * sizeJ P.m₀ j X) := by
  have hE0 := hP.E₀_nonneg
  by_cases hlarge : 1 ≤ ρ * (1 + sizeJ P.m₀ j X)
  · exact shiftTerm_discrepancy_bound_of_large hcl hcr hBg hν hμν hj1 hjk
      hy hX hyX hS hne hrad (pack S ψ b) hchart hρ.le hlarge
  have hA : 0 ≤ diamA d L P.m₀ m₁ := diamA_nonneg d L P.m₀ m₁
  have hsmall : q + diamA d L P.m₀ m₁ *
      (1 + sizeJ P.m₀ j X) * (σ * ε) ≤ r :=
    path_fits_of_not_large hA hσε hρ hbase hlarge
  by_cases hc : pack S ψ b ∈ TubeAniso i₀ ν r S
  · have he := trickFnA_shiftTerm_eq_of_dataHyp_small hcl hcr hBg hν hμν
      hj1 hjk hy hX hyX hS hS' hne hrad dat hσε hcentre hsmall hb hbl hc
    rw [he]
    simp only [sub_self, norm_zero]
    positivity
  · have he : trickFnA i₀ ν r (fun c' : Cfg d N S =>
        Tm.E j y X
          (fun z => fieldOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j i₀ S c' (z - y))
          (hOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) ν S c'))
        (pack S ψ b) =
        Tm.E j y X
          (fun z => fieldOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j i₀ S
            (pack S ψ b) (z - y))
          (hOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) ν S (pack S ψ b)) := by
      change ¬ (∃ R : Matrix (Fin N) (Fin N) ℂ,
        IsOrth R ∧ EntryBd N R ∧ rotCfgL R S (pack S ψ b) ∈ polyAniso i₀ ν r S) at hc
      unfold trickFnA
      simp only [hc, dite_false]
    rw [he]
    simp only [sub_self, norm_zero]
    positivity

end Balaban.SmallField.Def6v2
