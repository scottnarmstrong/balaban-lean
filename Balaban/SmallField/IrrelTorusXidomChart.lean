/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.SmallField.IrrelTorusXidomNumeric

/-!
# Anisotropic data from a strict composition chart witness
-/

@[expose] public section

namespace Balaban.SmallField

open Balaban Balaban.Background Balaban.Multiscale Balaban.Localization Balaban.SmallField.Def6
  Balaban.SmallField.GsSpec

variable {d L N₁ m₁ k N j : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱ' : ℝ}
  {G' : GeneratingSet d L (N₁ * L ^ m₁) k ϱ'}
  {a₁ ν s e ε K₂ : ℝ}
  {Ψ0 : CTorus d L N₁ m₁ k → Fin N → ℝ} {h0 : Fin N → ℝ}
  {Ψ'' h'' : CTorus d L N₁ m₁ k → Fin N → ℂ}
  {φr φc : G'.Ω 1 × Fin N → ℂ}

/-- The strict source chart witness gives the anisotropic datum on the pulled-back whole-level
lattice. Domain inclusion is at the same mass as the class term; the second difference is
P1 (3.107). -/
theorem HypS.dataHypAniso_of_levelGS
    (hL : 2 ≤ L) (hj1 : 1 ≤ j) (hjk : j < k)
    (HS : HypS
      (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) (ϱ := ϱ) j hjk.le)
      G' a₁ ν (xiC1 d * e) (xiC1 d * e) (xiC1 d * e) s j
      Ψ0 h0 Ψ'' h'' φr φc)
    (y : CTorus d L N₁ m₁ k) (f : Site d → CTorus d L N₁ m₁ k)
    (hf : f = fun x => y + ibase (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j x)
    (ψ : Site d → Spin N) (b : Spin N)
    (hψ : ∀ x i, ψ x i =
      (reR (levelGS (ϱ := ϱ) j hjk.le) G' a₁ φr Ψ0 (f x) i : ℂ) + dPsi (levelGS (ϱ := ϱ) j hjk.le) G' a₁ φr φc Ψ0 Ψ'' (f x) i)
    (hb : b = (((ν * ((L : ℝ) ^ j) ^ 2 : ℝ) : ℂ) •
      fun i => (h0 i : ℂ) + hRes (levelGS (ϱ := ϱ) j hjk.le) h'' (f 0) i))
    (hν : 0 < ν * ((L : ℝ) ^ j) ^ 2)
    (hτ1 : scaledC0 d * s ≤ 1)
    (hντ : ν * ((L : ℝ) ^ j) ^ 2 ≤ (scaledC0 d * s) ^ 2)
    (hζ1 : xiC1 d * e ≤ 1 / 200) (hee : e ≤ ε)
    {Dom : Set ((Site d → Spin N) × Spin N)}
    (hchart : (ψ, b) ∈ Dom ∧ ((fun _ => ψ 0), b) ∈ Dom)
    (hK₂ : 0 ≤ K₂)
    (hsec : ∀ x μ μ', ‖ψ (x + Pi.single μ 1 + Pi.single μ' 1) -
      ψ (x + Pi.single μ 1) - ψ (x + Pi.single μ' 1) + ψ x‖ ≤ K₂) :
    DataHypAniso Dom (ν * ((L : ℝ) ^ j) ^ 2)
      (16 * scaledC0 d * xiC1 d * s) ε K₂ ψ b := by
  have he : 0 < e := by
    have hη := HS.ηpos
    have hH := one_le_xiC1 d
    by_contra hn
    have : e ≤ 0 := le_of_not_gt hn
    nlinarith
  have hsharp : ∀ x, ‖∑ i,
        ((reR (levelGS (ϱ := ϱ) j hjk.le) G' a₁ φr Ψ0 (f x) i : ℝ) + dPsi (levelGS (ϱ := ϱ) j hjk.le) G' a₁ φr φc Ψ0 Ψ'' (f x) i) *
        ((reR (levelGS (ϱ := ϱ) j hjk.le) G' a₁ φr Ψ0 (f x) i : ℝ) + dPsi (levelGS (ϱ := ϱ) j hjk.le) G' a₁ φr φc Ψ0 Ψ'' (f x) i) -
      ∑ i, (reR (levelGS (ϱ := ϱ) j hjk.le) G' a₁ φr Ψ0 (f x) i : ℂ) * (reR (levelGS (ϱ := ϱ) j hjk.le) G' a₁ φr Ψ0 (f x) i : ℂ)‖ <
      (scaledC0 d * s) ^ 2 * (xiC1 d * e) := by
    intro x
    exact Balaban.SmallField.HypS.comp_square_scaled HS
      (by rw [hf]; simp [levelGS_Ω, hj1])
  exact ScaledPsiC.dataHypAniso_of_levelGS_scaled hL hj1 hjk
    (scaledComposition HS) y f hf ψ b hψ hb hsharp hν HS.hθ0 hτ1 hντ he hζ1 hee
    hchart hK₂ hsec

end Balaban.SmallField
