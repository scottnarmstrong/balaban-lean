/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.LocalClassDensityChart
public import Balaban.Localization.I5FluctChain
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The local chart is stable under small layer-constant perturbations (blocker 5, piece (2))

A pair `(Ψ, h)` that agrees, on the data sites of `𝔹_j(X)`, with a layer-constant perturbation of
size `δ₃` of a datum of `Ξ^c_K(𝔹_j; 1, ε)` lies in `Ξ^c_j(𝔹_j(X); 1, ε_b)` for
`K_loc (ε + K₂' δ₃) ≤ ε_b` ((Ξ2) at the level `j`, then the restriction to the local set).  This is the
tube around the lifted fields in which the terms of the class are analytic.
-/

@[expose] public section

namespace Balaban.Green

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.SmallField.Def6
  Balaban.SmallField.Def6v2 Balaban.SmallField.GsSpec Balaban.Localization Balaban.LargeField
  Balaban.Fluctuation

variable {d L N₁ m₁ K N : ℕ} [NeZero L] [NeZero N₁]

/-- **The tube of the local chart.** -/
theorem xiDom_localB_tube {j : ℕ} (hj1 : 1 ≤ j) (hj : j ≤ K)
    {X : Set (CTorus d L N₁ m₁ K)} {ϱ : ℝ} {hsep : ϱ ≤ minSep L (L ^ m₁)} {a : ℕ → ℝ}
    {ν ε εb δ₃ : ℝ} (H : BgHyp d L K ϱ a ν) (hδ₃ : 0 ≤ δ₃) (hδ₃1 : δ₃ ≤ 1)
    (hsmall0 : (4 * d + 6) * ((2 * d + 1) * ε) ≤ 1)
    (hδ₂ : xiC1 d * ε + 5 * δ₃ ≤ bgC1 d L N) (hstar : δ₃ ≤ deltaStar d L N)
    (hK1s : bgK1 d L N * (xiC1 d * ε) ≤ deltaStar d L N)
    (hsm : bgK1 d L N * (xiC1 d * ε) + cK2 d L N * δ₃ < bgC0 d L N)
    (hsmall : (4 * d + 6) * ((2 * d + 1) * (ε + xiK2 d L N * δ₃)) ≤ 1)
    (hc0 : xiC1 d * (ε + xiK2 d L N * δ₃) ≤ bgC0 d L N)
    (hc1 : xiC1 d * (ε + xiK2 d L N * δ₃) ≤ bgC1 d L N)
    (hεb : (2 * bgK1 d L N + 2) * (xiC1 d * (ε + xiK2 d L N * δ₃)) ≤ εb)
    {D : BgData (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) (ϱ := ϱ) j hj) N}
    (hD : XiCData (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) (ϱ := ϱ) j hj)
      a ν K 1 ε D)
    {δΨ : CTorus d L N₁ m₁ K → Fin N → ℂ}
    (hc : IsLayerConstant
      (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) (ϱ := ϱ) j hj) δΨ)
    (hδΨ : ∀ x ∈ dataSites
      (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) (ϱ := ϱ) j hj), vn (δΨ x) ≤ δ₃)
    {Ψ h : Fld d L N₁ m₁ K N}
    (hΨ : ∀ x ∈ dataSites (localB j hj X hsep), ∀ i, Ψ x i =
      (perturbData (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) (ϱ := ϱ) j hj)
        D δΨ hc).Ψ x i)
    (hh : ∀ x ∈ (localB j hj X hsep).Ω 1, ∀ i, h x i = D.h x i) :
    XiDom (localB j hj X hsep) a ν j εb Ψ h := by
  have hD' := xiCData_perturb H hδ₃ hδ₃1 hsmall0 hδ₂ hstar hK1s hsm hc hδΨ hD
  exact localB_xiDom_level_linear hj1 hj H hsmall hc0 hc1 hεb hD' hΨ (fun x hx i => hh x hx i)

end Balaban.Green
