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
/-- Two full class-chart extensions related by a complex rotation give equality of the
class term and its anisotropic tube extension at the original local configuration. -/
theorem trickFnA_shiftTerm_eq_of_full_chart_rot
    (hcl : SFTermClauses P (xiFieldDom a μ (P.eps d L)) Tm)
    (hBg : BgHyp d L k ϱ a μ) (hν : 0 < ν)
    (hμν : μ * ((L : ℝ) ^ j) ^ 2 ≤ ν) (hj1 : 1 ≤ j) (hjk : j ≤ k)
    (hy : Aligned (L ^ j) y) (hX : IsPolyDom P.m₀ j X) (hyX : y ∈ X)
    (hS : ∀ z ∈ X, unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j (z - y) ∈ S)
    {i₀ i₁ : Fin N} (hne : i₁ ≠ i₀) {r : ℝ} (hrad : AnisoRadiusOK d L N P j r)
    (c : Cfg d N S) (R : Matrix (Fin N) (Fin N) ℂ) (hR : IsCRot R)
    (hRb : EntryBd N R) (hRc : rotCfgL R S c ∈ polyAniso i₀ ν r S)
    (Ψ₁ h₁ Ψ₂ h₂ : Fld d L N₁ m₁ k N)
    (hXi₁ : XiDom (Tm.gs j X) a μ j (P.eps d L j) Ψ₁ h₁)
    (hXi₂ : XiDom (Tm.gs j X) a μ j (P.eps d L j) Ψ₂ h₂)
    (hrotΨ : Ψ₂ = rotField R Ψ₁) (hroth : h₂ = rotField R h₁)
    (hag₁ : ∀ z ∈ X,
      Ψ₁ z = fieldOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j i₀ S c (z - y) ∧
      h₁ z = hOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) ν S c z)
    (hag₂ : ∀ z ∈ X,
      Ψ₂ z = fieldOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j i₀ S
        (rotCfgL R S c) (z - y) ∧
      h₂ z = hOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) ν S (rotCfgL R S c) z) :
    trickFnA i₀ ν r (fun c' : Cfg d N S =>
      Tm.E j y X (fun z => fieldOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j i₀ S c' (z - y))
        (hOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) ν S c')) c =
      Tm.E j y X (fun z => fieldOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j i₀ S c (z - y))
        (hOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) ν S c) := by
  let F : Cfg d N S → ℂ := fun c' =>
    Tm.E j y X (fun z => fieldOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j i₀ S c' (z - y))
      (hOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) ν S c')
  change trickFnA i₀ ν r F c = F c
  have hT := tubeHypA_shiftTerm hcl hBg hν hμν hj1 hjk hy hX hyX hS hne hrad
  rw [hT.trickFnA_eq hR.1 hRb hRc]
  have hterm₁ : F c = Tm.E j y X Ψ₁ h₁ := by
    exact hcl.localE j y X _ Ψ₁ _ h₁
      (fun z hz => ⟨(hag₁ z hz).1.symm, (hag₁ z hz).2.symm⟩)
  have hterm₂ : F (rotCfgL R S c) = Tm.E j y X Ψ₂ h₂ := by
    exact hcl.localE j y X _ Ψ₂ _ h₂
      (fun z hz => ⟨(hag₂ z hz).1.symm, (hag₂ z hz).2.symm⟩)
  have hXiRot : XiDom (Tm.gs j X) a μ j (P.eps d L j) (rotField R Ψ₁)
      (rotField R h₁) := by rwa [← hrotΨ, ← hroth]
  have he := j hj1 hjk y X hX hyX R hR Ψ₁ h₁ hXi₁ hXiRot
  calc
    F (rotCfgL R S c) = Tm.E j y X Ψ₂ h₂ := hterm₂
    _ = Tm.E j y X Ψ₁ h₁ := by rw [hrotΨ, hroth]; exact he
    _ = F c := hterm₁.symm

end Balaban.SmallField.Def6v2
