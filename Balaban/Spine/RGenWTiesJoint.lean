/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Spine.RGenWTies
public import Balaban.Spine.NewLevelTies

/-!
# `PrefixInput`, the ties of the new level and the ties of the generating sets of `R` at one choice

`prefixInput_newLevelTies_rGenWTies_exists`: at the witness of
`prefixInput_newLevelTies_exists_gap` (`c = L³`, `M₁ = L^{m₀ + m₁ - 3}`, `R₀(d, L) < L^{m₀ - 3}`, the
block exponent `m₁` of the base tower, `m₁ ≥ 4`) the conditions `RGenWTies` hold
(`rGenWTies_of_pow`), so the three side inputs hold at one choice of the constants; the witness has
`m₀ ≥ s₀ + 3` with `s₀` a bound of the cube exponent of the local sets, so also
`hatScale + 3 ≤ m₀`.
-/

@[expose] public section

namespace Balaban.RootFSpine

open Balaban Balaban.LargeField Balaban.LargeField.Def7 Balaban.Multiscale

/-- **`PrefixInput`, `NewLevelTiesInput` and `RGenWTies` hold together**, with the room
`hatScale + 3 ≤ m₀` of the cube exponent of the local sets (the domain estimate of the terms of `R`,
`SFCtx.sfTerm_nearCompose_xiDom`), for `d ≥ 3`, `N ≥ 2`, `0 < δ < 1/2` and every block size `L ≥ 3`
with `L^{-((d-2)/2 - γ)} ≤ 1/16`, `γ = (1 + 2δ)/4`. -/
theorem prefixInput_newLevelTies_rGenWTies_exists (d N L : ℕ) (hd : 3 ≤ d) (hN : 2 ≤ N)
    (hL : 3 ≤ L) {δ : ℝ} (hδ : 0 < δ) (hδ' : δ < 1 / 2)
    (hLq : (L : ℝ) ^ (-(((d : ℝ) - 2) / 2 - (1 + 2 * δ) / 4)) ≤ 1 / 16) :
    ∃ (Ty : ℝ → ℝ → LargeField.Typing) (P6 : ℝ → ℝ → SmallField.Def6.Consts)
      (C7 : ℝ → ℝ → Consts7) (PB : ℝ → ℝ → LargeField.BudgetConsts)
      (cs₀ : ℝ → ℝ → LargeField.OpConsts)
      (M1 c : ℝ → ℝ → ℕ) (ϱ : ℝ → ℝ → ℝ),
      PrefixInput d δ Ty P6 C7 PB cs₀ M1 c ϱ ∧ NewLevelTiesInput d N Ty P6 C7 ϱ ∧
        RGenWTies d Ty C7 M1 ∧
        ∀ κ c₉ : ℝ, SmallField.GsSpec.hatScale (Ty κ c₉).L (C7 κ c₉).m₁ (ϱ κ c₉) + 3 ≤ (P6 κ c₉).m₀ := by
  obtain ⟨Ty, P6, C7, PB, cs₀, M1, c, ϱ, hPre, hNL, hgap⟩ :=
    prefixInput_newLevelTies_exists_gap d N L hd hN hL hδ hδ' hLq
  refine ⟨Ty, P6, C7, PB, cs₀, M1, c, ϱ, hPre, hNL, fun κ hκ c₉ hc₉ => ?_, fun κ c₉ => ?_⟩
  swap
  · obtain ⟨hTL, -, -, -, hs⟩ := hgap κ c₉
    rw [hTL]; exact hs
  obtain ⟨hTL, hR, hM1, -, -⟩ := hgap κ c₉
  have : NeZero (Ty κ c₉).L := ⟨by rw [hTL]; omega⟩
  obtain ⟨κmin, T₀, κdec, -, -, -, hm₁, -⟩ := (hNL κ hκ c₉ hc₉).tower
  have hm₁4 : 4 ≤ (C7 κ c₉).m₁ := hm₁ ▸ T₀.m₁_four
  have hb : 4 * (d : ℝ) * L ≤ Background.bgR0 d L := le_max_left _ _
  have hm₀ : 3 ≤ (P6 κ c₉).m₀ := by
    by_contra h
    have h0 : (P6 κ c₉).m₀ - 3 = 0 := by omega
    rw [h0, pow_zero] at hR
    have : (1 : ℝ) ≤ 4 * (d : ℝ) * L := by
      have h3 : (3 : ℝ) ≤ d := by exact_mod_cast hd
      have h3' : (3 : ℝ) ≤ L := by exact_mod_cast hL
      nlinarith
    linarith
  rw [hTL, hM1]
  exact rGenWTies_of_pow hd hL hm₀ hm₁4 hR

end Balaban.RootFSpine
