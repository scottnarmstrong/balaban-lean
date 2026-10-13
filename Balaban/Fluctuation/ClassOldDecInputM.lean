/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.ClassOldTermInputM
public import Balaban.Fluctuation.SharpENu
public import Balaban.SmallField.GsSpecClass
public import Balaban.Fluctuation.ClassOldDecInputE
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The inherited observable terms of a class member as inputs of the decoupled expansion

The observable counterpart of `ClassOldDecInputE`.  For an admissible label `τ = (j, y, i, X)` of a
class member `C` (`mem_classLabels_M_iff`) and a fixed source `g` with `‖g‖ < 1`, the raw
functional is `Mτ(r) = ℳ^{(j)}_i(y, X; r.1, r.2, g)` and the generator of the term is
`𝔹_j(X) = C.Tm.gs j X`.  The source factor `g_{y,i}` is not part of the functional.  The
generator facts `classOldDec_precedes`, `classOldDec_collar`, `classOldDec_bgSetting` are those of
`ClassOldDecInputE` (they do not mention the kind of term).

* `classOldDecObs_chart`: the hypotheses `hEan`, `hEbd` of `eterm_expansion_hat_rawY` for `Mτ`
  and `𝔹_j(X)`, from `classOldObs_analytic_bound` and an explicit chart inclusion;
* `classOldDecObs_expansion`: `eterm_expansion_hat_rawY` applied to one observable label.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Localization Balaban.Multiscale Balaban.Background Balaban.SmallField
  Balaban.SmallField.Def6 Balaban.SmallField.Def6v2 Finset

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}

open Classical in
/-- **The chart hypotheses of `eterm_expansion_hat_rawY` for one inherited observable label.**
For a label `(j, y, i, X)` of `C` (`1 ≤ j ≤ k`, `X ∈ 𝒟_j`, `y ∈ X`) and a source `g`,
`Def6.l1 g < 1`, the functional `Mτ(r) = ℳ^{(j)}_i(y, X; r.1, r.2, g)` is analytic on the chart
`Ξ^c(𝔹_j(X); σ, ε)` and bounded there by `c₉ (L^j)^{-((d-2)/2 + γ - α₁)} exp(-(κ_dec - 1) d_j(X))`,
provided the chart lies in the field domain `Dom` (hypothesis `hchart`). -/
theorem classOldDecObs_chart {P : Consts} {Dom : FieldDom d L N₁ m₁ (k + 1) N ϱ}
    (C : StepClass d L N₁ m₁ k N ϱ) (hm : P.m₀ = C.m₀) (hcl : SFTermClauses P Dom C.Tm)
    {κdec : ℝ} (hκ : κdec - 1 ≤ P.κ) (hc₉ : 0 ≤ P.c₉) (g : Fld d L N₁ m₁ (k + 1) N)
    (hg : Def6.l1 g < 1) (a : ℕ → ℝ) (ν σ ε : ℝ) {j : ℕ} (hj1 : 1 ≤ j) (hjk : j ≤ k)
    {y : CTorus d L N₁ m₁ (k + 1)} (i : Fin N) {X : Set (CTorus d L N₁ m₁ (k + 1))}
    (hX : IsPolyDom C.m₀ j X) (hy : y ∈ X)
    (hchart : ∀ r ∈ XiCRaw (C.Tm.gs j X) a ν j σ ε, Dom.dom j (C.Tm.gs j X) r.1 r.2) :
    AnalyticOnNhd ℂ
      (fun r : RawData d L (N₁ * L ^ m₁) (k + 1) N => C.Tm.M j y X r.1 r.2 g i)
      (XiCRaw (C.Tm.gs j X) a ν j σ ε) ∧
    (∀ r ∈ XiCRaw (C.Tm.gs j X) a ν j σ ε,
      ‖C.Tm.M j y X r.1 r.2 g i‖ ≤
        P.c₉ * ((L : ℝ) ^ j)⁻¹ ^ (((d : ℝ) - 2) / 2 + P.γ - P.α₁) *
          Real.exp (-(κdec - 1) * treeLenCovOne C.m₀ j X)) := by
  have h := classOldObs_analytic_bound C hm hcl hκ hc₉ g hg a ν σ ε {(j, y, i, X)}
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
  exact ⟨h.1 (j, y, i, X) (Finset.mem_singleton_self _), fun r hr =>
    (h.2 (j, y, i, X) (Finset.mem_singleton_self _) r hr)⟩

variable {Gp Gk Gj0 Gj : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
  {a₁ ν c BG κ r₀ eps δ₃ : ℝ} {X₀ X₁f : Finset (CTorus d L N₁ m₁ (k + 1))} {j₁ : ℕ}
  {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ} {Kc Cx c₂ BG₂ δ₁ δfl : ℝ}
  {X 𝒦X : Set (CTorus d L N₁ m₁ (k + 1))}

open Classical in
/-- **One inherited energy label expands over the decoupled domains** (`eterm_expansion_hat_rawY`
at `Mτ(r) = ℳ^{(j)}_i(y, X; r.1, r.2, g)`, generator `𝔹_j(X) = C.Tm.gs j X`).  The class supplies
`hEan`, `hEbd` (clauses `analyticE`, `boundE`, `classOldDecEnergy_chart`) and, through
`classOldDec_bgSetting`, the two generator facts of `hB`.  Everything else stays explicit, as
in `eterm_expansion_hat_rawY`: the setting `hB` for the other generators and numerical data, `hF`,
the cover data `hcov hX₁ hopt` of `X` (`IsPolyDom` gives only the chosen family of
`CovSetup.chosen`), `hconn hrow`, the chart inclusion `hchart`, and the constants.  Conclusion:
`flComp hB hF Eτ = ∑_{Y ∈ polymerDomains(X₁)} Ev Y` with raw-`Y` locality, the bound
`c₉ (L^j)^{-((d-2)/2 + γ - α₁)} exp(-κ₀ d_j(X) - 2 κ_dec d(Y))` and analyticity. -/
theorem classOldDecObs_expansion {P : Consts} {Dom : FieldDom d L N₁ m₁ (k + 1) N ϱ}
    (C : StepClass d L N₁ m₁ k N ϱ) (hm : P.m₀ = C.m₀) (hcl : SFTermClauses P Dom C.Tm)
    (hc₉ : 0 ≤ P.c₉) (g : Fld d L N₁ m₁ (k + 1) N) (hg : Def6.l1 g < 1) {j : ℕ}
    (hj1 : 1 ≤ j) (hjk : j ≤ k)
    {y : CTorus d L N₁ m₁ (k + 1)} (i : Fin N) (hXp : IsPolyDom C.m₀ j X) (hy : y ∈ X)
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
        flComp hB hF (fun r => C.Tm.M j y X r.1 r.2 g i)
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
        ‖Ev Y u‖ ≤ (P.c₉ * ((L : ℝ) ^ j)⁻¹ ^ (((d : ℝ) - 2) / 2 + P.γ - P.α₁)) *
          Real.exp (-κ₀ * treeLenCovOne C.m₀ j X - 2 * κdec * treeLenCov Gp C.m₀ Y)) ∧
      (∀ Y, AnalyticOnNhd ℂ (Ev Y) (XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
          {ψh : unitPts Gp × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ})) := by
  obtain ⟨hEan, hEbd⟩ := classOldDecObs_chart C hm hcl hκP hc₉ g hg (compWeight L a₁) ν (scaledC0 d)
    (scaledC0 d ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl) hj1 hjk i hXp hy hchart
  exact eterm_expansion_hat_rawY hB hF hk hG hG' cc hcψ hMX hdm hα hsm hδ₁ hcov hX₁ hconn hrow hopt
    hκ₀ hκdec hκ h1 hlog (mul_nonneg hc₉ (Real.rpow_nonneg (inv_nonneg.2 (pow_nonneg (Nat.cast_nonneg _) _)) _)) hEan hEbd

end Balaban.Fluctuation
