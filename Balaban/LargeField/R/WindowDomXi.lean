/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.SmallField.XiD2
public import Balaban.Fluctuation.RenormExpBounds
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

/-!
# The class domain from a small real domain (blocker 4)

A datum in the real domain `Ψ̃(G; ν, δ)` of a small radius lies in the fixed-`h` class domain
`Ξ^c(G; 1, ε)` of Lemma 3.5 once `(2 K₁ + 2) δ ≤ ε` (the case `ε = δ` of (D2), zero displacement).
`xiCOneReal_of_inDomainR` turns the `XiCOneReal` families of the window conversion into the
statement that the datum of every piece has the radius `ε_i / (2 K₁ + 2)`.
-/

@[expose] public section

namespace Balaban.LargeField

open Balaban Balaban.Background Balaban.Multiscale Balaban.SmallField Balaban.Fluctuation

variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ} {G : GeneratingSet d L N₀ k ϱ}

/-- A real datum of the domain `Ψ̃(G; ν, δ)` with the zero complex displacement is in
`Ψ̃^c(G; ν, δ, δ)`. -/
theorem inPsiTildeC_zero_of_inPsiTilde {ν δ : ℝ} {Ψ : Torus d (N₀ * L ^ k) → Fin N → ℝ}
    {h : Fin N → ℝ} (H : InPsiTilde G ν δ Ψ h) (hδ0 : 0 < δ) :
    InPsiTildeC G ν δ δ Ψ h 0 0 where
  toInPsiTilde := H
  eps_pos := hδ0
  layerConst' := fun _ _ _ _ _ _ _ => rfl
  hLayerConst' := fun _ _ _ _ _ _ _ => rfl
  c1 x x' _ := by simpa [vn_zero] using hδ0
  c2a x _ := by simpa [vn_zero] using hδ0.trans (lt_add_of_pos_left δ hδ0)
  c2b x _ := by simpa using hδ0
  c3a x _ := by
    simp [vn_zero]
    positivity
  c3b x _ := by
    simp
    positivity

/-- **A datum of the real domain of radius `δ` is a datum of the class domain `Ξ^c(G; 1, ε)`**
(zero displacement) when `(2 K₁ + 2) δ ≤ ε`. -/
theorem xiCOneReal_of_inDomainR {a : ℕ → ℝ} {ν δ ε : ℝ} (H : BgHyp d L k ϱ a ν) (hδ0 : 0 < δ)
    (hδc : δ ≤ bgC1 d L N) (hε : (2 * bgK1 d L N + 2) * δ ≤ ε) {D : BgData G N}
    (hD : InDomainR G ν δ D) : XiCOneReal G a ν ε D := by
  obtain ⟨Ψ, h, hP, hΨ, hh⟩ := hD
  have hd0 : 0 < d := by have := H.hd; omega
  have hPC := inPsiTildeC_zero_of_inPsiTilde hP hδ0
  have hδ0c : δ ≤ bgC0 d L N := hδc.trans (bgC1_le_bgC0 (d := d) (L := L) (N := N) hd0)
  have hνε : ν * ((L : ℝ) ^ k) ^ 2 * δ ^ 2 ≤ δ ^ 2 := by
    have := H.massLe
    nlinarith [sq_nonneg δ]
  have hX := psiTildeC_subset_xiC (a := a) H hδ0 le_rfl hδ0c hδc hνε hPC
    (εb := ε) (by nlinarith)
  exact ⟨Ψ, h, 0, hX, fun x hx i => by simpa using hΨ x hx i,
    fun x hx i => by simpa using hh x hx i⟩

end Balaban.LargeField
