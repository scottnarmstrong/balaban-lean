/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.ClassOldCover
public import Balaban.Fluctuation.ClassOldCoverSlices
public import Balaban.SmallField.XiUnitWitness
import Mathlib.Tactic.Linarith

/-!
# The old-class expansion on the birth-mass domain (decision D2(b))

An old term `𝒟_j`, `j ≤ k`, keeps the field domain of its birth scale: the wide domain
`xiFieldDom A μ εs` at the mass `μ` of the birth step.  The cover expansion
`classOldDec_expansion_cover` needs, for this domain, the inclusion of the chart data
`XiCRaw (𝔹_j(X)) A ν j …` (at the current mass `ν`) into the domain.

* `gs_top_layer_empty_of_clauses`: the empty-layers condition `(𝔹_j(X)).Ω (j+1) = ∅` is the
  clause `gs_spec` of the term clauses `SFTermClauses P Dom C.Tm` (already a hypothesis of the
  cover expansion).
* `classOldDec_expansion_cover_birth`: `classOldDec_expansion_cover` with
  `Dom = xiFieldDom A μ εs`, where `hchart` is derived from `xiCRaw_dom_birth_flow_unitfree`.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Localization Balaban.Multiscale Balaban.Background Balaban.SmallField
  Balaban.SmallField.Def6 Balaban.SmallField.Def6v2 Finset

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}

/-- **The empty-layers condition from `gs_spec`.**  For a polymer `X ∈ 𝒟_j`, `1 ≤ j ≤ k`, the
generating set `Tm.gs j X` of the term clauses has no layer above `j`. -/
theorem gs_top_layer_empty_of_clauses {P : Consts} {Dom : FieldDom d L N₁ m₁ k N ϱ}
    {Tm : Terms d L N₁ m₁ k N ϱ} (hcl : SFTermClauses P Dom Tm) {j : ℕ} (hj1 : 1 ≤ j)
    (hjk : j ≤ k) {X : Set (CTorus d L N₁ m₁ k)} (hX : IsPolyDom P.m₀ j X) :
    (Tm.gs j X).Ω (j + 1) = ∅ :=
  (hcl.gs_spec j hj1 hjk X hX).2 (j + 1) (Nat.lt_succ_self j)

variable {Gp : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
  {Gk : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
  {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
  {a₁ ν c BG κ r₀ eps δ₃ : ℝ} {X₀ : Finset (CTorus d L N₁ m₁ (k + 1))}
  {Kc Cx c₂ BG₂ δ₁ δfl : ℝ} {X : Set (CTorus d L N₁ m₁ (k + 1))}

open Classical in
/-- **`classOldDec_expansion_cover` on the birth-mass domain.**  The domain is
`xiFieldDom (compWeight L a₁) μ εs`; `hchart` is `xiCRaw_dom_birth_flow_unitfree` with
`hΩ` from `gs_spec` (`gs_top_layer_empty_of_clauses`).  The mass `μ` is the birth mass obtained from
the current mass `ν` by the flow factors `ξ`. -/
theorem classOldDec_expansion_cover_birth [NeZero N] {P : Consts} {εs : ℕ → ℝ} {μ : ℝ}
    (C : StepClass d L N₁ m₁ k N ϱ) (hm : P.m₀ = C.m₀) (hcl : SFTermClauses P (xiFieldDom (compWeight L a₁) μ εs) C.Tm)
    {β : ℝ} (hβ : 0 < β) (hE₀ : 0 ≤ P.E₀) {j : ℕ} (hN : L ^ C.m₀ ∣ N₁) (hj1 : 1 ≤ j) (hjk : j ≤ k)
    {y : CTorus d L N₁ m₁ (k + 1)} (hXp : IsPolyDom C.m₀ j X) (hy : y ∈ X)
    (hk : 1 ≤ k) (hG : IsLevel Hm k) (hG' : IsLevel Gp (k + 1)) (cc : ℂ)
    {cψ : ℝ} (hcψ : 0 ≤ cψ)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δc : ℝ}
    (hdm : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    (hδ₁ : Real.sqrt N * (‖cc‖ * (covSupConstC d L N (compWeight L a₁ k) κ * cψ)) < δ₁)
    (hconn : HatConn Gp) (hrow : RowInHat (coverOf Gp) Hm (compWeight L a₁) ν)
    {κdec κ₀ : ℝ} (hκ₀ : 0 ≤ κ₀) (hκdec : 3 * κ₀ + 3 ≤ κdec)
    (hκ : 4 * d * (((2 * L + 1) ^ d : ℕ) : ℝ) * κdec ≤ κ) (h1 : 1 ≤ (κ / 2 - 1) / 2)
    (hlog : Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) * (((L ^ C.m₀) ^ d : ℕ) : ℝ)) ≤ (κ / 2 - 1) / 2)
    (hκP : κdec - 1 ≤ P.κ)
    {K : ℕ} {ξ : ℕ → Fin 3 → ℂ} {q c₈ r : ℝ}
    (H : BgHyp d L (k + 1) ϱ (compWeight L a₁) ν) (H' : BgHyp d L (k + 1) ϱ (compWeight L a₁) μ)
    (heps : 0 < eps) (hδ₃ : 0 ≤ δ₃) (hδfl : 0 ≤ δfl)
    (hq0 : 0 ≤ q) (hq1 : q < 1) (hc : 0 ≤ c₈) (hs : c₈ * q ≤ 1 - q)
    (hξ : ∀ n, ‖ξ n‖ ≤ c₈ / 4 * q ^ (n + 1))
    (hμ : (μ : ℂ) = ν * ∏ n ∈ Ico j K, ((1 + ξ n 2) / (1 + ξ n 1)))
    (hτr : Real.exp (3 * (c₈ / 4 * (q ^ (j + 1) / (1 - q)))) - 1 < r) (hr : r ≤ 1 / 16)
    (hDL : (2 * (scaledC0 d ^ 2 *
          (scaledC0 d ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl)) +
        2 * ((N : ℝ) + 1) * (cK2 d L N * (scaledC0 d ^ 2 *
          (scaledC0 d ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl)) ^ 2)) *
      (1 + (1 + 16 * ((N : ℝ) + 1) * cK2 d L N) *
        (Real.exp (3 * (c₈ / 4 * (q ^ (j + 1) / (1 - q)))) - 1)) ≤ εs j)
    (hsmε : (4 * d + 6) * ((2 * d + 1) * εs j) ≤ 1) (hc1ε : 4 * (xiC1 d * εs j) ≤ bgC1 d L N)
    (hKε : bgK1 d L N * (xiC1 d * εs j) + 3 * r ≤ deltaStar d L N)
    (hζε : 8 * εs j * r ≤ deltaStar d L N) :
    ∃ 𝒦X : Set (CTorus d L N₁ m₁ (k + 1)),
      ∀ X₁f : Finset (CTorus d L N₁ m₁ (k + 1)),
        (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) = X1 Gp C.m₀ j 𝒦X →
        ∀ (hB : BgSetting N Gp Gk (C.Tm.gs j X) a₁ ν c BG κ r₀ eps δ₃ X₀ X₁f j) (hF : FlSetting N Gp Gk Hm a₁ ν κ BG eps δ₃ Kc Cx c₂ BG₂ δ₁ δfl X₁f),
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
            {ψh : unitPts Gp × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ})) :=
  classOldDec_expansion_cover_birth_slices C hm (hcl.gs_spec j hj1 (by omega) X (hm ▸ hXp))
    (hcl.analyticE j hj1 (by omega) y X (hm ▸ hXp) hy)
    (fun Ψ h hd => hcl.boundE j hj1 (by omega) y X (hm ▸ hXp) hy Ψ h hd)
    hβ hE₀ hN hjk hXp hk hG hG' cc hcψ hMX hdm hα hsm hδ₁ hconn hrow hκ₀ hκdec hκ h1 hlog hκP
    H H' heps hδ₃ hδfl hq0 hq1 hc hs hξ hμ hτr hr hDL hsmε hc1ε hKε hζε

end Balaban.Fluctuation
