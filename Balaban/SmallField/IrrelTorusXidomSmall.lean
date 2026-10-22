/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.SmallField.IrrelTorusXidomLocal
public import Balaban.SmallField.IrrelTorusXidomSourceFrame

/-!
# The small-polymer tube comparison from anisotropic data
-/

@[expose] public section

namespace Balaban.SmallField.Def6v2

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization Balaban.SmallField
  Balaban.SmallField.Def6 Metric Set Filter

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}
  {P : Consts} {a : ℕ → ℝ} {μ ν : ℝ} {Tm : Terms d L N₁ m₁ k N ϱ} {j : ℕ}
  {y : CTorus d L N₁ m₁ k} {X : Set (CTorus d L N₁ m₁ k)} {S : Finset (Site d)}

open Classical in
/-- **The small-polymer tube comparison from bounded increments** (core of
`trickFnA_shiftTerm_eq_of_dataHyp_small`): increments `‖ψ(s) - ψ(0)‖ ≤ ℓ σ ε` on `S` and the
real-frame centre estimate place the whole local datum inside the class chart needed by the
complex rotation step. -/
theorem trickFnA_shiftTerm_eq_of_incr_small
    (hcl : SFTermClauses P (xiFieldDom a μ (P.eps d L)) Tm)
    (hBg : BgHyp d L k ϱ a μ) (hν : 0 < ν)
    (hμν : μ * ((L : ℝ) ^ j) ^ 2 ≤ ν) (hνb : ν ≤ 1) (hj1 : 1 ≤ j) (hjk : j ≤ k)
    (hy : Aligned (L ^ j) y) (hX : IsPolyDom P.m₀ j X) (hyX : y ∈ X)
    (hS : ∀ z ∈ X, unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j (z - y) ∈ S)
    {i₀ i₁ : Fin N} (hne : i₁ ≠ i₀) {r : ℝ} (hrad : AnisoRadiusOK d L N P j r)
    {σ ε q ℓ : ℝ} {ψ : Site d → Spin N} {b : Spin N}
    (hincr : ∀ s ∈ S, ‖ψ s - ψ 0‖ ≤ ℓ * (σ * ε))
    (hcentre : ∀ i, ‖ψ 0 i - (Pi.single i₀ 1 : Spin N) i‖ ≤ q)
    (hsmall : q + ℓ * (σ * ε) ≤ r)
    (hb : ∀ i, ‖b i - (ν : ℂ) * (Pi.single i₀ 1 : Spin N) i‖ ≤ r)
    (hbl : ‖b i₀ - (ν : ℂ)‖ < r ^ 2)
    (hc : pack S ψ b ∈ TubeAniso i₀ ν r S) :
    trickFnA i₀ ν r (fun c' : Cfg d N S =>
      Tm.E j y X
        (fun z => fieldOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j i₀ S c' (z - y))
        (hOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) ν S c')) (pack S ψ b) =
      Tm.E j y X
        (fun z => fieldOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j i₀ S
          (pack S ψ b) (z - y))
        (hOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) ν S (pack S ψ b)) := by
  exact trickFnA_shiftTerm_eq_of_local_bounds hcl hBg hν hμν hνb hj1 hjk hy hX hyX
    hS hne hrad (pack S ψ b) hc
    (local_spin_bound_of_incr hincr hcentre hsmall)
    (by intro i; simpa only [pack, Sum.elim_inr] using hb i)
    (by simpa only [pack, Sum.elim_inr] using hbl)


open Classical in
/-- On a small polymer, anisotropic first differences and the real-frame centre estimate
place the whole local datum inside the class chart needed by the complex rotation step. -/
theorem trickFnA_shiftTerm_eq_of_dataHyp_small
    (hcl : SFTermClauses P (xiFieldDom a μ (P.eps d L)) Tm)
    (hBg : BgHyp d L k ϱ a μ) (hν : 0 < ν)
    (hμν : μ * ((L : ℝ) ^ j) ^ 2 ≤ ν) (hνb : ν ≤ 1) (hj1 : 1 ≤ j) (hjk : j ≤ k)
    (hy : Aligned (L ^ j) y) (hX : IsPolyDom P.m₀ j X) (hyX : y ∈ X)
    (hS : ∀ z ∈ X, unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j (z - y) ∈ S)
    (hS' : ∀ s ∈ S, ∃ x ∈ X, Aligned (L ^ j) x ∧
      unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j (x - y) = s)
    {i₀ i₁ : Fin N} (hne : i₁ ≠ i₀) {r : ℝ} (hrad : AnisoRadiusOK d L N P j r)
    {σ ε K₂ q : ℝ} {ψ : Site d → Spin N} {b : Spin N}
    {Dom : Set ((Site d → Spin N) × Spin N)}
    (dat : DataHypAniso Dom ν σ ε K₂ ψ b) (hσε : 0 ≤ σ * ε)
    (hcentre : ∀ i, ‖ψ 0 i - (Pi.single i₀ 1 : Spin N) i‖ ≤ q)
    (hsmall : q + diamA d L P.m₀ m₁ * (1 + sizeJ P.m₀ j X) * (σ * ε) ≤ r)
    (hb : ∀ i, ‖b i - (ν : ℂ) * (Pi.single i₀ 1 : Spin N) i‖ ≤ r)
    (hbl : ‖b i₀ - (ν : ℂ)‖ < r ^ 2)
    (hc : pack S ψ b ∈ TubeAniso i₀ ν r S) :
    trickFnA i₀ ν r (fun c' : Cfg d N S =>
      Tm.E j y X
        (fun z => fieldOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j i₀ S c' (z - y))
        (hOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) ν S c')) (pack S ψ b) =
      Tm.E j y X
        (fun z => fieldOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j i₀ S
          (pack S ψ b) (z - y))
        (hOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) ν S (pack S ψ b)) :=
  trickFnA_shiftTerm_eq_of_incr_small hcl hBg hν hμν hνb hj1 hjk hy hX hyX hS hne hrad
    (incr_of_dataHyp hjk hy hX hyX hS' dat hσε) hcentre hsmall hb hbl hc

end Balaban.SmallField.Def6v2
