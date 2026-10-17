/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.SmallField.Def6v2Bridge

/-!
# The birth-mass domains of Def-6 v2

The level-`j` terms keep the fine mass `μ_j = ν_j L⁻²ʲ` of the scale at which they were born.
Their wide complex chart is `Ξᶜ_j(G; aIdeal L k (a k), μ_j, 1, ε_j)`, with the same physical
carrier and ideal kernel sequence as `completeXiDom`. This is the birth-frozen interpretation of
P4 p. 704 (4.19) and the inherited term domains in P1 (H.4)–(H.7), under author ruling R6.
-/

@[expose] public section

namespace Balaban.SmallField.Def6v2

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField
  Balaban.SmallField.Def6

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}

/-- The wide level-`j` field domain with its background mass fixed at the birth scale `j`:
`Ξᶜ_j(G; aIdeal L k (a k), ν_j L⁻²ʲ, 1, ε_j)`. The real carrier is all external fields, as in
`completeXiDom`. See P4 p. 704 (4.19), P1 (H.4)–(H.7), and ruling R6. -/
noncomputable def birthXiDom (P : Consts) (Rg : Regime L) (a : ℕ → ℝ) :
    ∀ (N₁ : ℕ) [NeZero N₁], FieldDom d L N₁ m₁ k N ϱ :=
  fun _ _ =>
    { phys := Set.univ
      dom := fun j G Ψ h =>
        XiDom G (aIdeal L k (a k)) (physMass L j (Rg.ν j)) j (P.eps d L j) Ψ h }

theorem birthXiDom_phys (P : Consts) (Rg : Regime L) (a : ℕ → ℝ) :
    (birthXiDom (d := d) (m₁ := m₁) (k := k) (N := N) (ϱ := ϱ) P Rg a N₁).phys =
      Set.univ := rfl

theorem birthXiDom_dom_iff (P : Consts) (Rg : Regime L) (a : ℕ → ℝ) (j : ℕ)
    (G : GeneratingSet d L (N₁ * L ^ m₁) k ϱ) (Ψ h : Fld d L N₁ m₁ k N) :
    (birthXiDom P Rg a N₁).dom j G Ψ h ↔
      XiDom G (aIdeal L k (a k)) (physMass L j (Rg.ν j)) j (P.eps d L j) Ψ h :=
  Iff.rfl

theorem birthXiDom_dom_self (P : Consts) (Rg : Regime L) (a : ℕ → ℝ)
    (G : GeneratingSet d L (N₁ * L ^ m₁) k ϱ) (Ψ h : Fld d L N₁ m₁ k N) :
    (birthXiDom P Rg a N₁).dom k G Ψ h ↔ (completeXiDom P Rg a N₁).dom k G Ψ h :=
  Iff.rfl

/-- On a fixed fine torus, an old level has the same chart whenever its birth mass and its
ideal kernel sequence agree. This isolates the two coefficient identities needed when old terms
are transported to the next scale. -/
theorem birthXiDom_dom_congr (P : Consts) {Rg Rg' : Regime L} {a a' : ℕ → ℝ}
    (ha : aIdeal L k (a k) = aIdeal L k (a' k)) {j : ℕ} (hν : Rg.ν j = Rg'.ν j)
    (G : GeneratingSet d L (N₁ * L ^ m₁) k ϱ) (Ψ h : Fld d L N₁ m₁ k N) :
    (birthXiDom P Rg a N₁).dom j G Ψ h ↔ (birthXiDom P Rg' a' N₁).dom j G Ψ h := by
  rw [birthXiDom_dom_iff, birthXiDom_dom_iff, ha, hν]

end Balaban.SmallField.Def6v2
