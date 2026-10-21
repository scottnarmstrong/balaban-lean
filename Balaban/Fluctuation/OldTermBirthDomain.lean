/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.OldTermClassDomain
public import Balaban.SmallField.XiUnitWitness
public import Balaban.Fluctuation.OldTermComposedChart

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
  above `j` are empty;
* `d2raw_mem_birthXiDom_of_class`: the chart premise `hchart` of the class chain on its formula path:
  the composed step data of a label whose term is composed on the class generating set
  `Tm.gs j X` lie in the class term domain at the birth mass, with `Ψ(y)·Ψ(y)` in the slit plane;
* `composedChart_mem_birthXiDom`: the composed chart of a class generating set lies in the class
  term domain at the birth mass (so a bound of the class on its term domain gives the bound at the
  composed data the step reads).
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Localization
  Balaban.SmallField.Def6 Balaban.SmallField.Def6v2

section Chart

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

end Chart

section Composed

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ ϱ₁ ϱm : ℝ}
  {Gp : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
  {Gk : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ₁}
  {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}
  {a₁ ν c BG κ r₀ eps δ₃ Kc Cx c₂ BG₂ δ₁ δfl : ℝ} {X₀ X₁f : Finset (CTorus d L N₁ m₁ (k + 1))}

/-- **The chart premise of the class chain from the inclusion** (`hchart` on the formula path;
rulings R2, R6, R13).  For a label `(j, y, X)` of the class whose term is composed on the class
generating set `Tm.gs j X` with the step's settings at the radius `ε′`, and the class terms on the
birth-mass domain, the composed step data `D2raw Gk (Tm.gs j X) a Fk (d1Triple Gp Gk Hm a t)` of the
realizable triples `t` lie in the class term domain at the birth mass, and `Ψ(y)·Ψ(y)` lies in the
slit plane, under the (DL-gap) `(2 E + 2 (N + 1) K₂ E²) (1 + K_m τ) ≤ ε_j`,
`E = ε′ + K₂ δ₃ + K₂ δ_fl`, and the hypotheses of `xiCRaw_mem_birthXiDom`. -/
theorem d2raw_mem_birthXiDom_of_class [NeZero N] (P : Consts) (Rg : Regime L) (a : ℕ → ℝ)
    {Tm : Terms d L N₁ m₁ (k + 1) N ϱ} (hcl : SFTermClauses P (birthXiDom P Rg a N₁) Tm)
    {j : ℕ} {X : Set (CTorus d L N₁ m₁ (k + 1))} {y : CTorus d L N₁ m₁ (k + 1)}
    (hj1 : 1 ≤ j) (hjk : j ≤ k + 1) (hX : IsPolyDom P.m₀ j X) (hy : y ∈ X)
    (hB : BgSetting N Gp Gk (Tm.gs j X) a₁ ν c BG κ r₀ eps δ₃ X₀ X₁f j)
    (hF : FlSetting N Gp Gk Hm a₁ ν κ BG eps δ₃ Kc Cx c₂ BG₂ δ₁ δfl X₁f)
    (hA : aIdeal L (k + 1) (a (k + 1)) = compWeight L a₁)
    (H : BgHyp d L (k + 1) ϱ (compWeight L a₁) ν)
    (H' : BgHyp d L (k + 1) ϱ (compWeight L a₁) (physMass L j (Rg.ν j)))
    {t τ r : ℝ} (hμ : physMass L j (Rg.ν j) = ν * (1 + t)) (ht : |t| ≤ τ) (hτr : τ < r)
    (hr : r ≤ 1 / 16) (he : 0 < eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl)
    (hDL : (2 * (eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl) + 2 * ((N : ℝ) + 1) *
        (cK2 d L N * (eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl) ^ 2)) *
      (1 + (1 + 16 * ((N : ℝ) + 1) * cK2 d L N) * τ) ≤ P.eps d L j)
    (hsmε : (4 * d + 6) * ((2 * d + 1) * P.eps d L j) ≤ 1)
    (hc1ε : 4 * (xiC1 d * P.eps d L j) ≤ bgC1 d L N)
    (hKε : bgK1 d L N * (xiC1 d * P.eps d L j) + 3 * r ≤ deltaStar d L N)
    (hζε : 8 * P.eps d L j * r ≤ deltaStar d L N)
    {Fk : RawData d L (N₁ * L ^ m₁) (k + 1) N → (Gk.Ω 1 × Fin N → ℂ) × (Gk.Ω 1 → ℂ)}
    (hFk : ∀ D : BgData Gk N, InUnionDomainC Gk (bgC0 d L N) (bgC1 d L N) ν D →
      Fk (rawOf D) = (bgFieldC Gk (compWeight L a₁) ν (bgC0 d L N) D,
        bgMultC Gk (compWeight L a₁) ν (bgC0 d L N) D))
    {tr : ((Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)) × (Hm.Ω 1 × Fin N → ℂ) ×
      (RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ))}
    (htr : tr ∈ FlRealLC Gp Hm a₁ ν BG κ eps X₁f BG₂ δ₁) :
    (birthXiDom P Rg a N₁ : FieldDom d L N₁ m₁ (k + 1) N ϱ).dom j (Tm.gs j X)
        (D2raw Gk (Tm.gs j X) (compWeight L a₁) Fk
          (d1Triple Gp Gk Hm (compWeight L a₁) tr.1.1 tr.2.1 tr.2.2)).1
        (D2raw Gk (Tm.gs j X) (compWeight L a₁) Fk
          (d1Triple Gp Gk Hm (compWeight L a₁) tr.1.1 tr.2.1 tr.2.2)).2 ∧
      dot ((D2raw Gk (Tm.gs j X) (compWeight L a₁) Fk
          (d1Triple Gp Gk Hm (compWeight L a₁) tr.1.1 tr.2.1 tr.2.2)).1 y)
        ((D2raw Gk (Tm.gs j X) (compWeight L a₁) Fk
          (d1Triple Gp Gk Hm (compWeight L a₁) tr.1.1 tr.2.1 tr.2.2)).1 y) ∈
        Complex.slitPlane := by
  have hmem := d2raw_d1Triple_mem_xiCRaw (b := 1) le_rfl (one_le_scaledC0 d) hB hF hFk htr
  simp only [one_pow, one_mul] at hmem
  have h := xiCRaw_mem_birthXiDom P Rg a hA H H' ((hcl.gs_spec j hj1 hjk X hX).2 (j + 1)
    (Nat.lt_succ_self j)) le_rfl he hμ ht hτr hr (by simpa using hDL) hsmε hc1ε hKε hζε _ hmem
  exact ⟨h.1, h.2 y ((mem_dataSites (G := Tm.gs j X)).2
    (Or.inl ((hcl.gs_spec j hj1 hjk X hX).1 hy)))⟩

/-- **The composed chart of a class generating set lies in the class term domain at the birth
mass** (from `composedChart_subset_xiCRaw` and `xiCRaw_mem_birthXiDom`), with `Ψ(y)·Ψ(y)` in the
slit plane at `y ∈ X`: a bound of the class on its term domain gives the bound at the data composed
from the charts of level `k + 1` (the form of P1 (3.128) the step reads). -/
theorem composedChart_mem_birthXiDom [NeZero N] (P : Consts) (Rg : Regime L) (a : ℕ → ℝ)
    {Tm : Terms d L N₁ m₁ (k + 1) N ϱ} (hcl : SFTermClauses P (birthXiDom P Rg a N₁) Tm)
    {a₁ ν : ℝ} (hA : aIdeal L (k + 1) (a (k + 1)) = compWeight L a₁)
    (H : BgHyp d L (k + 1) ϱ (compWeight L a₁) ν)
    {b e t τ r : ℝ} {j : ℕ} (hj1 : 1 ≤ j) (hjk : j ≤ k + 1)
    (H' : BgHyp d L (k + 1) ϱ (compWeight L a₁) (physMass L j (Rg.ν j)))
    (hb : 1 ≤ b) (he : 0 < e)
    (hμ : physMass L j (Rg.ν j) = ν * (1 + t)) (ht : |t| ≤ τ) (hτr : τ < r) (hr : r ≤ 1 / 16)
    (hDL : (2 * (b ^ 2 * e) + 2 * ((N : ℝ) + 1) * (cK2 d L N * (b ^ 2 * e) ^ 2)) *
      (1 + (1 + 16 * ((N : ℝ) + 1) * cK2 d L N) * τ) ≤ P.eps d L j)
    (hsmε : (4 * d + 6) * ((2 * d + 1) * P.eps d L j) ≤ 1)
    (hc1ε : 4 * (xiC1 d * P.eps d L j) ≤ bgC1 d L N)
    (hKε : bgK1 d L N * (xiC1 d * P.eps d L j) + 3 * r ≤ deltaStar d L N)
    (hζε : 8 * P.eps d L j * r ≤ deltaStar d L N)
    {X : Set (CTorus d L N₁ m₁ (k + 1))} {y : CTorus d L N₁ m₁ (k + 1)}
    (hX : IsPolyDom P.m₀ j X) (hy : y ∈ X) :
    ∀ q ∈ composedChart (N := N) (Tm.gs j X) (compWeight L a₁) ν j b e,
      (birthXiDom P Rg a N₁ : FieldDom d L N₁ m₁ (k + 1) N ϱ).dom j (Tm.gs j X) q.1 q.2 ∧
        dot (q.1 y) (q.1 y) ∈ Complex.slitPlane := by
  intro q hq
  have h := xiCRaw_mem_birthXiDom P Rg a hA H H' ((hcl.gs_spec j hj1 hjk X hX).2 (j + 1)
    (Nat.lt_succ_self j)) hb he hμ ht hτr hr hDL hsmε hc1ε hKε hζε q
    (composedChart_subset_xiCRaw hq)
  exact ⟨h.1, h.2 y ((mem_dataSites (G := Tm.gs j X)).2
    (Or.inl ((hcl.gs_spec j hj1 hjk X hX).1 hy)))⟩

end Composed

end Balaban.Fluctuation
