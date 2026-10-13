/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.ClassOldTermInputE
public import Balaban.Fluctuation.SharpENu
public import Balaban.SmallField.GsSpecClass
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The inherited energy terms of a class member as inputs of the decoupled expansion

For an admissible inherited label `τ = (j, y, X)` of a class member `C` (`mem_classLabels_E_iff`)
the raw functional is `Eτ(r) = β⁻¹ ℰ^{(j)}(y, X; r.1, r.2)` and the generator of the term is
`𝔹_j(X) = C.Tm.gs j X`.  This file sets up `Eτ` as the input of the decoupled expansion
`eterm_expansion_hat_rawY` (the first leaf of `notes/phase1/GENCLASS-OLD.md`).

* `classOldDec_precedes`, `classOldDec_collar`: the two facts about `𝔹_j(X)` that `BgSetting`
  asks of the term generator, `𝔹_j(X) ≺ 𝔹_k` and `collar 𝔹_j(X) ⊆ Ω₁(𝔹_k)`, from the clause
  `gs_spec` of the class.
* `classOldDec_bgSetting`: `BgSetting` for the generator `𝔹_j(X)` from `BgSetting` for any other
  generator of the term (for instance the whole level `levelGS j`), the two facts above supplying
  the only fields that mention the term generator.
* `classOldDecEnergy_chart`: the hypotheses `hEan`, `hEbd` of `eterm_expansion_hat_rawY` for `Eτ`
  and `𝔹_j(X)`, from the clauses `analyticE`, `boundE` and an explicit chart inclusion.
* `classOldDec_expansion`: `eterm_expansion_hat_rawY` applied to one label.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Localization Balaban.Multiscale Balaban.Background Balaban.SmallField
  Balaban.SmallField.Def6 Balaban.SmallField.Def6v2 Finset

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}

/-- **`𝔹_j(X) ≺ 𝔹_k`** for the term generator of a polymer of `𝒟_j`, `1 ≤ j ≤ k`: `Ω_i(𝔹_j(X))`
is empty for `i > j` (clause `gs_spec`), and `Ω_i(𝔹_k)` is everything for `i ≤ k`. -/
theorem classOldDec_precedes {P : Consts} {Dom : FieldDom d L N₁ m₁ (k + 1) N ϱ}
    {Tm : Terms d L N₁ m₁ (k + 1) N ϱ} (hcl : SFTermClauses P Dom Tm) {j : ℕ} (hj1 : 1 ≤ j)
    (hjk : j ≤ k) {X : Set (CTorus d L N₁ m₁ (k + 1))} (hX : IsPolyDom P.m₀ j X) :
    Precedes (Tm.gs j X) (stepG d L N₁ m₁ k ϱ) := by
  intro i hi1 hik
  by_cases h : i ≤ k
  · intro x _
    simp [stepG, levelGS, h]
  · have hi : j < i := by omega
    rw [(hcl.gs_spec j hj1 (by omega) X hX).2 i hi]
    exact Finset.empty_subset _

/-- **The collar of `𝔹_j(X)` lies in `Ω₁(𝔹_k)`**, since `Ω₁(𝔹_k)` is the whole torus for `k ≥ 1`. -/
theorem classOldDec_collar {Gj : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ} (hk : 1 ≤ k) :
    ∀ z ∈ collar Gj, z ∈ (stepG d L N₁ m₁ k ϱ).Ω 1 := by
  intro z _
  simp [stepG, levelGS, hk]

variable {Gp : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
  {Gk : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
  {Gj0 Gj : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
  {a₁ ν c BG κ r₀ eps δ₃ : ℝ} {X₀ X₁f : Finset (CTorus d L N₁ m₁ (k + 1))} {j₁ : ℕ}

/-- **`BgSetting` for the term generator.**  Of the fields of `BgSetting` only `hq`
(`𝔹_j(X) ≺ 𝔹_k`), `colj` (`collar 𝔹_j(X) ⊆ Ω₁(𝔹_k)`) and `HBj` (the numerical hypothesis, which
does not depend on the generator) mention it.  So `BgSetting` for `𝔹_j(X) = C.Tm.gs j X` follows
from `BgSetting` for any other generator `Gj0` of the term (the whole-level set in the landed
whole-lattice results) and the two facts `classOldDec_precedes`, `classOldDec_collar`. -/
theorem classOldDec_bgSetting
    (hB0 : BgSetting N Gp Gk Gj0 a₁ ν c BG κ r₀ eps δ₃ X₀ X₁f j₁)
    (hq : Precedes Gj Gk) (hcol : ∀ z ∈ collar Gj, z ∈ Gk.Ω 1) :
    BgSetting N Gp Gk Gj a₁ ν c BG κ r₀ eps δ₃ X₀ X₁f j₁ :=
  { hB0 with hq := hq, colj := hcol, HBj := hB0.HBp }

open Classical in
/-- **The chart hypotheses of `eterm_expansion_hat_rawY` for one inherited label.**  For a label
`(j, y, X)` of `C` (`1 ≤ j ≤ k`, `X ∈ 𝒟_j`, `y ∈ X`), the functional
`Eτ(r) = β⁻¹ ℰ^{(j)}(y, X; r.1, r.2)` is analytic on the chart `Ξ^c(𝔹_j(X); C₀, ε₂)` of the
expansion and bounded there by `β⁻¹ E₀ exp(-(κ_dec - 1) d_j(X))`, provided the chart lies in the
field domain `Dom` of the class (hypothesis `hchart`, kept explicit). -/
theorem classOldDecEnergy_chart {P : Consts} {Dom : FieldDom d L N₁ m₁ (k + 1) N ϱ}
    (C : StepClass d L N₁ m₁ k N ϱ) (hm : P.m₀ = C.m₀)
    (hcl : SFTermClauses P Dom C.Tm) {β : ℝ} (hβ : 0 < β) {κdec : ℝ} (hκ : κdec - 1 ≤ P.κ)
    (hE₀ : 0 ≤ P.E₀) (a₁ ν δ₃ eps δfl : ℝ) {j : ℕ} (hj1 : 1 ≤ j) (hjk : j ≤ k) {y : CTorus d L N₁ m₁ (k + 1)}
    {X : Set (CTorus d L N₁ m₁ (k + 1))} (hX : IsPolyDom C.m₀ j X) (hy : y ∈ X)
    (hchart : ∀ r ∈ XiCRaw (C.Tm.gs j X) (compWeight L a₁) ν j (scaledC0 d)
      (scaledC0 d ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl),
      Dom.dom j (C.Tm.gs j X) r.1 r.2) :
    AnalyticOnNhd ℂ
      (fun r : RawData d L (N₁ * L ^ m₁) (k + 1) N => (β : ℂ)⁻¹ * C.Tm.E j y X r.1 r.2)
      (XiCRaw (C.Tm.gs j X) (compWeight L a₁) ν j (scaledC0 d)
        (scaledC0 d ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl)) ∧
    (∀ r ∈ XiCRaw (C.Tm.gs j X) (compWeight L a₁) ν j (scaledC0 d)
        (scaledC0 d ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl),
      ‖(β : ℂ)⁻¹ * C.Tm.E j y X r.1 r.2‖ ≤
        (β⁻¹ * P.E₀) * Real.exp (-(κdec - 1) * treeLenCovOne C.m₀ j X)) := by
  have h := classOldEnergy_analytic_bound C hm hcl hβ hκ hE₀ (compWeight L a₁) ν (scaledC0 d)
    (scaledC0 d ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl) {(j, y, X)}
    (by
      intro τ hτ
      rw [Finset.mem_singleton] at hτ
      subst hτ
      exact ⟨⟨hj1, hjk⟩, hX, hy⟩)
    (by
      intro τ hτ r hr
      rw [Finset.mem_singleton] at hτ
      subst hτ
      exact hchart r hr)
  exact ⟨h.1 (j, y, X) (Finset.mem_singleton_self _), fun r hr =>
    (h.2 (j, y, X) (Finset.mem_singleton_self _) r hr)⟩

variable {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ} {Kc Cx c₂ BG₂ δ₁ δfl : ℝ}
  {X 𝒦X : Set (CTorus d L N₁ m₁ (k + 1))}

open Classical in
/-- **One inherited energy label expands over the decoupled domains** (`eterm_expansion_hat_rawY`
at `Eτ(r) = β⁻¹ ℰ^{(j)}(y, X; r.1, r.2)`, generator `𝔹_j(X) = C.Tm.gs j X`).  The class supplies
`hEan`, `hEbd` (clauses `analyticE`, `boundE`, `classOldDecEnergy_chart`) and, through
`classOldDec_bgSetting`, the two generator facts of `hB`.  Everything else stays explicit, as
in `eterm_expansion_hat_rawY`: the setting `hB` for the other generators and numerical data, `hF`,
the cover data `hcov hX₁ hopt` of `X` (`IsPolyDom` gives only the chosen family of
`CovSetup.chosen`), `hconn hrow`, the chart inclusion `hchart`, and the constants.  Conclusion:
`flComp hB hF Eτ = ∑_{Y ∈ polymerDomains(X₁)} Ev Y` with raw-`Y` locality, the bound
`β⁻¹ E₀ exp(-κ₀ d_j(X) - 2 κ_dec d(Y))` and analyticity. -/
theorem classOldDec_expansion {P : Consts} {Dom : FieldDom d L N₁ m₁ (k + 1) N ϱ}
    (C : StepClass d L N₁ m₁ k N ϱ) (hm : P.m₀ = C.m₀) (hcl : SFTermClauses P Dom C.Tm)
    {β : ℝ} (hβ : 0 < β) (hE₀ : 0 ≤ P.E₀) {j : ℕ} (hj1 : 1 ≤ j) (hjk : j ≤ k)
    {y : CTorus d L N₁ m₁ (k + 1)} (hXp : IsPolyDom C.m₀ j X) (hy : y ∈ X)
    (hB : BgSetting N Gp Gk (C.Tm.gs j X) a₁ ν c BG κ r₀ eps δ₃ X₀ X₁f j)
    (hF : FlSetting N Gp Gk Hm a₁ ν κ BG eps δ₃ Kc Cx c₂ BG₂ δ₁ δfl X₁f)
    (hk : 1 ≤ k) (hG : IsLevel Hm k) (hG' : IsLevel Gp (k + 1)) (cc : ℂ)
    {cψ : ℝ} (hcψ : 0 ≤ cψ)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δc : ℝ}
    (hdm : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    (hδ₁ : Real.sqrt N * (‖cc‖ * (covSupConstC d L N (compWeight L a₁ k) κ * cψ)) < δ₁)
    (hcov : CovSetup Gp C.m₀ j X 𝒦X)
    (hX₁ : (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) = X1 Gp C.m₀ j 𝒦X)
    (hconn : HatConn Gp) (hrow : RowInHat (coverOf Gp) Hm (compWeight L a₁) ν)
    (hopt : ∃ (W₀ : Finset (CTorus d L N₁ m₁ (k + 1)))
      (E₀ : Finset (CTorus d L N₁ m₁ (k + 1) × CTorus d L N₁ m₁ (k + 1))),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ X) ∧ MeetsOne C.m₀ j 𝒦X W₀ ∧
        bondCost (scaleW L C.m₀ m₁ j) E₀ = treeLenCovOne C.m₀ j X)
    {κdec κ₀ : ℝ} (hκ₀ : 0 ≤ κ₀) (hκdec : 3 * κ₀ + 3 ≤ κdec)
    (hκ : 4 * d * (((2 * L + 1) ^ d : ℕ) : ℝ) * κdec ≤ κ) (h1 : 1 ≤ (κ / 2 - 1) / 2)
    (hlog : Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) * (((L ^ C.m₀) ^ d : ℕ) : ℝ)) ≤ (κ / 2 - 1) / 2)
    (hκP : κdec - 1 ≤ P.κ)
    (hchart : ∀ r ∈ XiCRaw (C.Tm.gs j X) (compWeight L a₁) ν j (scaledC0 d)
      (scaledC0 d ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl),
      Dom.dom j (C.Tm.gs j X) r.1 r.2) :
    ∃ Ev : Set (CTorus d L N₁ m₁ (k + 1)) →
        RawData d L (N₁ * L ^ m₁) (k + 1) N × (unitPts Gp × Fin N → ℂ) → ℂ,
      (∀ D : BgData Gp N, XiCData Gp (compWeight L a₁) ν (k + 1) 1 eps D →
        ∀ ψh : unitPts Gp × Fin N → ℂ, (∀ p, ‖ψh p‖ ≤ cψ) →
        flComp hB hF (fun r => (β : ℂ)⁻¹ * C.Tm.E j y X r.1 r.2)
          (rawOf D, hatLift Gp a₁ ν hG' cc D ψh) =
        ∑ Y ∈ polymerDomains (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) => i.1.1)
          Gp C.m₀ (X1 Gp C.m₀ j 𝒦X), Ev Y (rawOf D, ψh)) ∧
      (∀ Y, ∀ u ∈ XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
          {ψh : unitPts Gp × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ},
        ∀ u' ∈ XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
          {ψh : unitPts Gp × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ},
        agreeOn Y u.1 u'.1 → (∀ y ∈ Y, ∀ i, u.2 (unitPt hG' y, i) = u'.2 (unitPt hG' y, i)) →
        Ev Y u = Ev Y u') ∧
      (∀ Y, ∀ u ∈ XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
          {ψh : unitPts Gp × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ},
        ‖Ev Y u‖ ≤ (β⁻¹ * P.E₀) *
          Real.exp (-κ₀ * treeLenCovOne C.m₀ j X - 2 * κdec * treeLenCov Gp C.m₀ Y)) ∧
      (∀ Y, AnalyticOnNhd ℂ (Ev Y) (XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
          {ψh : unitPts Gp × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ})) := by
  obtain ⟨hEan, hEbd⟩ := classOldDecEnergy_chart (N := N) C hm hcl hβ hκP hE₀ a₁ ν δ₃ eps δfl hj1 hjk
    hXp hy hchart
  exact eterm_expansion_hat_rawY hB hF hk hG hG' cc hcψ hMX hdm hα hsm hδ₁ hcov hX₁ hconn hrow hopt
    hκ₀ hκdec hκ h1 hlog (mul_nonneg (inv_nonneg.2 hβ.le) hE₀) hEan hEbd

end Balaban.Fluctuation
