/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.SmallField.IrrelTorusXidomSecondDiff
public import Balaban.Localization.I5Chain

/-!
# P1 (3.107) at the exact step chart realization
-/

@[expose] public section

namespace Balaban.SmallField

open Balaban Balaban.Background Balaban.Multiscale Balaban.Localization
  Balaban.SmallField.GsSpec Balaban.SmallField.Def6 Matrix Finset

/-- P1 (3.107) for the exact `XiCData` realization supplied by a strict step chart test. -/
theorem xiCData_second_diff_levelGS_pullback
    {d L N₁ m₁ k N j : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱ' : ℝ}
    (hd : 3 ≤ d) (hL : 3 ≤ L) (hj1 : 1 ≤ j) (hjk : j ≤ k)
    {G' : GeneratingSet d L (N₁ * L ^ m₁) k ϱ'}
    {a₁ ν θ ε' θh : ℝ} (ha₁ : 0 < a₁)
    (hBg : BgHyp d L k ϱ' (compWeight L a₁) ν)
    (hprec : Precedes (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
      (k := k) (ϱ := ϱ) j hjk) G')
    (hgap : ScaleGap (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
      (k := k) (ϱ := ϱ) j hjk) G' θ)
    (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) (hθh0 : 0 < θh) (hθh1 : θh < 1)
    (hsmall : (4 * d + 6) * ((2 * d + 1) * ε') ≤ 1)
    (hc1 : xiC1 d * ε' ≤ bgC1 d L N)
    (D : BgData G' N)
    (hD : XiCData G' (compWeight L a₁) ν k 1 ε' D) :
    ∃ B : ℝ, 0 ≤ B ∧
      ∀ (y : CTorus d L N₁ m₁ k) (ψ : Site d → Spin N),
        (∀ s, ψ s = composeField
            (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
              (k := k) (ϱ := ϱ) j hjk)
            G' (compWeight L a₁)
            (bgFieldC G' (compWeight L a₁) ν (bgC0 d L N) D) D.Ψ
            (y + ibase (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j s)) →
        ∀ x μ μ', ‖ψ (x + Pi.single μ 1 + Pi.single μ' 1) -
          ψ (x + Pi.single μ 1) - ψ (x + Pi.single μ' 1) + ψ x‖ ≤
            xiSigma d L N B θh * θ ^ (2 - θh) * ε' := by
  obtain ⟨Ψ₀, h₀, Ψ'', h'', hXi, hReal⟩ := hD
  exact xiC_second_diff_levelGS_pullback_realization hd hL hj1 hjk
    ha₁ hBg hprec hgap hθ0 hθ1 hθh0 hθh1 hsmall hc1 hXi D hReal

end Balaban.SmallField
