/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.OldTermClassDomain
public import Balaban.SmallField.XiUnitWitness

/-!
# The charts of the old terms lie in the class term domain at the birth mass (`OldTermBirthDomain`)

Ruling R13 together with ruling R6: the class term domain of a level-`j` term is `birthXiDom`, the
domain `Ξ^c_j(Tm.gs j X; 1, ε_j)` with the class weights `aIdeal L K (a K)` and the birth mass
`μ_j = ν_j L^{-2j}` of the level (`physMass L j (Rg.ν j)`).  The new level reads the term at the
step's weights `compWeight L a₁` and mass `ν`, on the chart `Ξ^c_j(Gj; b, e)`.  The weights agree
when the step's kernel coefficient is the class's (`hA`; `aIdeal_compWeight`); the masses differ by
the cumulated factor of the flow, `μ_j = ν (1 + t)` with `|t| ≤ τ` (`LocalClassBirth`), and the
passage between them is the mass response at a unit real witness
(`xiDom_birth_chart_unitfree_gen`, decision D2(b)).

* `xiCRaw_mem_birthXiDom`: the chart `Ξ^c_j(G; b, e)` of the step lies in the class term domain at
  the birth mass, and `Ψ(y)·Ψ(y)` lies in the slit plane at the data sites `y` of `G`, under the
  (DL-gap) `(2 E₁ + 2 (N + 1) K₂ E₁²) (1 + K_m τ) ≤ ε_j`, `E₁ = b² e`, when the layers of `G`
  above `j` are empty.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Localization
  Balaban.SmallField.Def6 Balaban.SmallField.Def6v2

variable {d L N₁ m₁ K N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}

/-- **The chart of the step lies in the class term domain at the birth mass** (rulings R6, R13;
decision D2(b)).  For a generating set `G` with no layer above `j`, the raw data of the chart
`Ξ^c_j(G; b, e)` at the step's weights `compWeight L a₁` and mass `ν` lie in the domain
`(birthXiDom P Rg a).dom j G` of the class, whose weights are the step's (`hA`) and whose mass
`μ_j = physMass L j (Rg.ν j)` is `ν (1 + t)`, `|t| ≤ τ < r ≤ 1/16`, under the (DL-gap)
`(2 b² e + 2 (N + 1) K₂ (b² e)²) (1 + K_m τ) ≤ ε_j` and the smallness of `ε_j`; and the square
`Ψ(y)·Ψ(y)` lies in the slit plane at every data site `y` of `G`. -/
theorem xiCRaw_mem_birthXiDom [NeZero N] (P : Consts) (Rg : Regime L) (a : ℕ → ℝ)
    {G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {a₁ ν b e t τ r : ℝ} {j : ℕ}
    (hA : aIdeal L K (a K) = compWeight L a₁)
    (H : BgHyp d L K ϱ (compWeight L a₁) ν)
    (H' : BgHyp d L K ϱ (compWeight L a₁) (physMass L j (Rg.ν j)))
    (hΩ : G.Ω (j + 1) = ∅) (hb : 1 ≤ b) (he : 0 < e)
    (hμ : physMass L j (Rg.ν j) = ν * (1 + t)) (ht : |t| ≤ τ) (hτr : τ < r) (hr : r ≤ 1 / 16)
    (hDL : (2 * (b ^ 2 * e) + 2 * ((N : ℝ) + 1) * (cK2 d L N * (b ^ 2 * e) ^ 2)) *
      (1 + (1 + 16 * ((N : ℝ) + 1) * cK2 d L N) * τ) ≤ P.eps d L j)
    (hsmε : (4 * d + 6) * ((2 * d + 1) * P.eps d L j) ≤ 1)
    (hc1ε : 4 * (xiC1 d * P.eps d L j) ≤ bgC1 d L N)
    (hKε : bgK1 d L N * (xiC1 d * P.eps d L j) + 3 * r ≤ deltaStar d L N)
    (hζε : 8 * P.eps d L j * r ≤ deltaStar d L N) :
    ∀ p ∈ XiCRaw G (compWeight L a₁) ν j b e,
      (birthXiDom P Rg a N₁ : FieldDom d L N₁ m₁ K N ϱ).dom j G p.1 p.2 ∧
        ∀ y ∈ dataSites G, dot (p.1 y) (p.1 y) ∈ Complex.slitPlane := by
  rintro p ⟨D, hD, rfl⟩
  refine ⟨?_, fun y hy => dot_mem_slitPlane_of_xiDom (xiDom_of_xiCData_of_one_le hb le_rfl hD) hy⟩
  rw [birthXiDom_dom_iff, hA]
  exact xiDom_birth_chart_unitfree_gen H H' hΩ hb he hμ ht hτr hr hDL hsmε hc1ε hKε hζε hD

end Balaban.Fluctuation
