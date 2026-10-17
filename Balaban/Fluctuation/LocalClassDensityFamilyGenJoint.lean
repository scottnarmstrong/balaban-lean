/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.ClassOldDecInputE
public import Balaban.Fluctuation.ClassOldMarksY
public import Balaban.Fluctuation.MarkedEvJoint
public import Balaban.Fluctuation.DecMarkBlocks

/-!
# The marked terms of a generic label functional (`LocalClassDensityFamilyGenJoint`)

`classOldMarkedLocal_joint_of` expands the functional `r ↦ β⁻¹ ℰ^{(j)}(y, X; r)` of one inherited
label.  Of the class `C` it uses only three facts about the label functional: it is analytic on the
chart image `Ξ^c(𝔹_j(X); b, ε₂)`, it is bounded there by `B_τ e^{-(κ_dec - 1) d^cov_{m₀}(X)}`,
and the generator `𝔹_j` of the label (`Gj`, any generating set with the background setting `hB`)
carries the locality of the label: the expansion of `eTermFun` is local through the dependence of
`Gj` and `Gk` (`eTermFun_local_dir`).  The generic version below takes any
`Eτ : RawData → ℂ` with these properties; the generating set `Gj` may be the one of the support
`X^⋆ = X ∪ st₊(y)` of the label.

* `classOldEnergy_chart_radius_raw`: the functional `C.Tm.E j y X` of an inherited label is
  analytic on the chart image and bounded there by `E₀ e^{-(κ_dec - 1) d^cov_{C.m₀}(X)}`
  (`classOldDecEnergy_chart_radius` at `β = 1`).
* `classOldMarkedLocal_joint_gen`: the six clauses of `classOldMarkedLocal_joint_of` for the label
  functional `r ↦ β⁻¹ Eτ r`, with the bound `β⁻¹ B_τ e^{-κ₀ d(X) - 2κ_dec d^cov_{m₀}(Y)}`.
-/

@[expose] public section

namespace Balaban.Fluctuation

open MeasureTheory Balaban Balaban.Localization Balaban.Multiscale
  Balaban.Background Balaban.SmallField Balaban.SmallField.Def6 Balaban.SmallField.Def6v2
  Balaban.SmallField.GsSpec Balaban.Analysis Balaban.Polymer Finset Matrix

section LabelJointGen

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}

/-- **The chart hypotheses of the generic label functional for the label of a class.**  For a
label `(j, y, X)` of `C` (`1 ≤ j ≤ k`, `X ∈ 𝒟_j`, `y ∈ X`) whose chart lies in the field domain
`Dom`, the unscaled functional `r ↦ ℰ^{(j)}(y, X; r.1, r.2)` is analytic on the chart image and
bounded there by `E₀ e^{-(κ_dec - 1) d^cov_{C.m₀}(X)}`. -/
theorem classOldEnergy_chart_radius_raw {b : ℝ} {P : Consts}
    {Dom : FieldDom d L N₁ m₁ (k + 1) N ϱ}
    (C : StepClass d L N₁ m₁ k N ϱ) (hm : P.m₀ = C.m₀)
    (hcl : SFTermClauses P Dom C.Tm) {κdec : ℝ} (hκ : κdec - 1 ≤ P.κ)
    (hE₀ : 0 ≤ P.E₀) (a₁ ν δ₃ eps δfl : ℝ) {j : ℕ} (hj1 : 1 ≤ j) (hjk : j ≤ k)
    {y : CTorus d L N₁ m₁ (k + 1)} {X : Set (CTorus d L N₁ m₁ (k + 1))}
    (hX : IsPolyDom C.m₀ j X) (hy : y ∈ X)
    (hchart : ∀ r ∈ XiCRaw (C.Tm.gs j X) (compWeight L a₁) ν j b
      (b ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl),
      Dom.dom j (C.Tm.gs j X) r.1 r.2) :
    AnalyticOnNhd ℂ
      (fun r : RawData d L (N₁ * L ^ m₁) (k + 1) N => C.Tm.E j y X r.1 r.2)
      (XiCRaw (C.Tm.gs j X) (compWeight L a₁) ν j b
        (b ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl)) ∧
    (∀ r ∈ XiCRaw (C.Tm.gs j X) (compWeight L a₁) ν j b
        (b ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl),
      ‖C.Tm.E j y X r.1 r.2‖ ≤ P.E₀ * Real.exp (-(κdec - 1) * treeLenCovOne C.m₀ j X)) := by
  obtain ⟨h1, h2⟩ := classOldDecEnergy_chart_radius (N := N) (b := b) C hm hcl
    (β := 1) one_pos hκ hE₀ a₁ ν δ₃ eps δfl hj1 hjk hX hy hchart
  refine ⟨?_, fun r hr => ?_⟩
  · simpa using h1
  · simpa using h2 r hr

variable {ϱ₁ ϱ₂ ϱm : ℝ}
variable {Gp : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
  {Gk : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ₁}
  {Gj : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ₂}
  {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}
  {a₁ ν c BG κ r₀ eps δ₃ : ℝ} {X₀ X₁f : Finset (CTorus d L N₁ m₁ (k + 1))}
  {Kc Cx c₂ BG₂ δ₁ δfl : ℝ} {X 𝒦X : Set (CTorus d L N₁ m₁ (k + 1))}

/-- **The expansion of one label with a generic label functional along the masked tangent, with
joint analyticity of the marked terms.**  As `classOldMarkedLocal_joint_of`, for the functional
`r ↦ β⁻¹ Eτ r` with `Eτ` analytic on the chart image of `Gj` and bounded there by
`B_τ e^{-(κ_dec - 1) d^cov_{m₀}(X)}`. -/
theorem classOldMarkedLocal_joint_gen {b : ℝ} (hb₁ : 1 ≤ b) (hbC : b ≤ scaledC0 d)
    {m₀ : ℕ} (Eτ : RawData d L (N₁ * L ^ m₁) (k + 1) N → ℂ) {Bτ : ℝ} (hBτ : 0 ≤ Bτ)
    {β : ℝ} (hβ : 0 < β) {j : ℕ}
    (hB : BgSetting N Gp Gk Gj a₁ ν c BG κ r₀ eps δ₃ X₀ X₁f j)
    (hF : FlSetting N Gp Gk Hm a₁ ν κ BG eps δ₃ Kc Cx c₂ BG₂ δ₁ δfl X₁f)
    (hk : 1 ≤ k) (hG : IsLevel Hm k) (hG' : IsLevel Gp (k + 1)) (cc : ℂ)
    {cψ : ℝ} (hcψ : 0 ≤ cψ)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δc : ℝ}
    (hdm : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    (hcov : CovSetup Gp m₀ j X 𝒦X)
    (hX₁ : (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) = X1 Gp m₀ j 𝒦X)
    (hconn : HatConn Gp) (hrow : RowInHat (coverOf Gp) Hm (compWeight L a₁) ν)
    (hopt : ∃ (W₀ : Finset (CTorus d L N₁ m₁ (k + 1)))
      (E₀ : Finset (CTorus d L N₁ m₁ (k + 1) × CTorus d L N₁ m₁ (k + 1))),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ X) ∧ MeetsOne m₀ j 𝒦X W₀ ∧
        bondCost (scaleW L m₀ m₁ j) E₀ = treeLenCovOne m₀ j X)
    {κdec κ₀ : ℝ} (hκ₀ : 0 ≤ κ₀) (hκdec : 3 * κ₀ + 3 ≤ κdec)
    (hκ : 4 * d * (((2 * L + 1) ^ d : ℕ) : ℝ) * κdec ≤ κ) (h1 : 1 ≤ (κ / 2 - 1) / 2)
    (hlog : Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) * (((L ^ m₀) ^ d : ℕ) : ℝ)) ≤ (κ / 2 - 1) / 2)
    (hEan : AnalyticOnNhd ℂ Eτ (XiCRaw Gj (compWeight L a₁) ν j b
      (b ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl)))
    (hEbd : ∀ r ∈ XiCRaw Gj (compWeight L a₁) ν j b
      (b ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl),
      ‖Eτ r‖ ≤ Bτ * Real.exp (-(κdec - 1) * treeLenCovOne m₀ j X))
    {F₁ : DecParams Gp × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      (Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)}
    (hF₁an : AnalyticOnNhd ℂ F₁ {q | (∀ P, ‖q.1 P‖ < Real.exp κ) ∧ ∃ D : BgData Gp N,
      InUnionDomainC Gp (bgC0 d L N) (c7 d L N BG κ) ν D ∧ q.2 = (D.Ψ, D.h)})
    (hF₁ : ∀ (s : DecParams Gp) (D : BgData Gp N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC Gp (bgC0 d L N) (c7 d L N BG κ) ν D → ∀ (φ : Gp.Ω 1 × Fin N → ℂ)
        (α : Gp.Ω 1 → ℂ), IsDecBg Gp (compWeight L a₁) ν (rho4 d L N BG κ) s D φ α →
        F₁ (s, rawOf D) = (φ, α))
    {Sol : Dec2.DecParams (coverOf Gp) × Edat Hm N → (Hm.Ω 1 × Fin N → ℂ) × (Hm.Ω 1 → ℂ)}
    (hSolan : AnalyticOnNhd ℂ Sol {p | (∀ P, ‖p.1 P‖ < Real.exp κ) ∧
      StrictDataM Hm N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2})
    (hSolprop : ∀ p : Dec2.DecParams (coverOf Gp) × Edat Hm N, (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM Hm N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2 →
        (Sol p).1 = dphi Hm (Dec2.decG (coverOf Gp) Hm (compWeight L a₁) ν p.1) p.2.2.1 p.2.1
          (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol p).2 ∧
        Dec2.DecFixed (coverOf Gp) Hm (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
          (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol p).2 ∧
        Small Hm (Sol p).2 (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
        Small Hm (Sol p).2 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        SupBounds Hm (Sol p).1 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        (∀ δα' : Hm.Ω 1 → ℂ, Small Hm δα' (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf Gp) Hm (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
            (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol p).2))
    {Fk : RawData d L (N₁ * L ^ m₁) (k + 1) N → (Gk.Ω 1 × Fin N → ℂ) × (Gk.Ω 1 → ℂ)}
    (hFkan : AnalyticOnNhd ℂ Fk {p | ∃ D : BgData Gk N,
      InUnionDomainC Gk (bgC0 d L N) (bgC1 d L N) ν D ∧ p = (D.Ψ, D.h)})
    (hFk : ∀ D : BgData Gk N, InUnionDomainC Gk (bgC0 d L N) (bgC1 d L N) ν D →
      Fk (rawOf D) = (bgFieldC Gk (compWeight L a₁) ν (bgC0 d L N) D,
        bgMultC Gk (compWeight L a₁) ν (bgC0 d L N) D))
    (Zm : Finset (unitPts Gp)) :
    -- 1. sum identity
    (∀ um tm : ℂ, (‖um‖ + ‖tm‖) * markedRad d L N k a₁ κ cψ cc < δ₁ →
      ∀ D : BgData Gp N, XiCData Gp (compWeight L a₁) ν (k + 1) 1 eps D →
      ∀ ψh : unitPts Gp × Fin N → ℂ, (∀ p, ‖ψh p‖ ≤ cψ) →
      flComp hB hF (fun r => (β : ℂ)⁻¹ * Eτ r)
          (rawOf D, markedTangDec hG' cc a₁ ν Zm um tm D ψh) =
        ∑ Y ∈ polyDom Gp X₁f m₀ j 𝒦X, evDec X₁f m₀ j 𝒦X a₁ ν hG' cc F₁ Sol
          (eTermFun Gp Gk Gj Hm (compWeight L a₁) Fk
            (fun r => (β : ℂ)⁻¹ * Eτ r)) Zm um tm Y (rawOf D, ψh)) ∧
    -- 2. locality
    (∀ um tm : ℂ, (‖um‖ + ‖tm‖) * markedRad d L N k a₁ κ cψ cc < δ₁ →
      ∀ Y, ∀ u ∈ XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
        {ψh : unitPts Gp × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ},
      ∀ u' ∈ XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
        {ψh : unitPts Gp × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ},
      AgHatDir hG' Y u u' →
        evDec X₁f m₀ j 𝒦X a₁ ν hG' cc F₁ Sol
          (eTermFun Gp Gk Gj Hm (compWeight L a₁) Fk
            (fun r => (β : ℂ)⁻¹ * Eτ r)) Zm um tm Y u =
        evDec X₁f m₀ j 𝒦X a₁ ν hG' cc F₁ Sol
          (eTermFun Gp Gk Gj Hm (compWeight L a₁) Fk
            (fun r => (β : ℂ)⁻¹ * Eτ r)) Zm um tm Y u') ∧
    -- 3. bound on closed bidiscs
    (∀ a b : ℝ, 0 ≤ a → 0 ≤ b → (a + b) * markedRad d L N k a₁ κ cψ cc < δ₁ →
      ∀ um tm : ℂ, ‖um‖ ≤ a → ‖tm‖ ≤ b →
      ∀ Y, ∀ u ∈ XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
        {ψh : unitPts Gp × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ},
      ‖evDec X₁f m₀ j 𝒦X a₁ ν hG' cc F₁ Sol
          (eTermFun Gp Gk Gj Hm (compWeight L a₁) Fk
            (fun r => (β : ℂ)⁻¹ * Eτ r)) Zm um tm Y u‖ ≤
        (β⁻¹ * Bτ) * Real.exp (-κ₀ * treeLenCovOne m₀ j X - 2 * κdec * treeLenCov Gp m₀ Y)) ∧
    -- 4. Cauchy estimate
    (∀ a b t₀ : ℝ, 0 ≤ a → 0 ≤ b → 0 < t₀ → t₀ ≤ b →
      (a + b) * markedRad d L N k a₁ κ cψ cc < δ₁ →
      ∀ um : ℂ, ‖um‖ ≤ a →
      ∀ Y, ∀ u ∈ XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
        {ψh : unitPts Gp × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ},
      ‖deriv (fun t : ℂ => evDec X₁f m₀ j 𝒦X a₁ ν hG' cc F₁ Sol
          (eTermFun Gp Gk Gj Hm (compWeight L a₁) Fk
            (fun r => (β : ℂ)⁻¹ * Eτ r)) Zm um t Y u) 0‖ ≤
        (β⁻¹ * Bτ) *
          Real.exp (-κ₀ * treeLenCovOne m₀ j X - 2 * κdec * treeLenCov Gp m₀ Y) / t₀) ∧
    -- 5. mark-locality
    (∀ um tm tm' : ℂ, (‖um‖ + ‖tm‖) * markedRad d L N k a₁ κ cψ cc < δ₁ →
      (‖um‖ + ‖tm'‖) * markedRad d L N k a₁ κ cψ cc < δ₁ →
      ∀ Y : Set (CTorus d L N₁ m₁ (k + 1)), (∀ y ∈ Y, unitPt hG' y ∉ Zm) →
      ∀ u ∈ XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
        {ψh : unitPts Gp × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ},
      evDec X₁f m₀ j 𝒦X a₁ ν hG' cc F₁ Sol
          (eTermFun Gp Gk Gj Hm (compWeight L a₁) Fk
            (fun r => (β : ℂ)⁻¹ * Eτ r)) Zm um tm Y u =
        evDec X₁f m₀ j 𝒦X a₁ ν hG' cc F₁ Sol
          (eTermFun Gp Gk Gj Hm (compWeight L a₁) Fk
            (fun r => (β : ℂ)⁻¹ * Eτ r)) Zm um tm' Y u) ∧
    -- 6. joint analyticity
    (∀ Y, AnalyticOnNhd ℂ
      (fun p : (RawData d L (N₁ * L ^ m₁) (k + 1) N × (unitPts Gp × Fin N → ℂ)) × (ℂ × ℂ) =>
        evDec X₁f m₀ j 𝒦X a₁ ν hG' cc F₁ Sol
          (eTermFun Gp Gk Gj Hm (compWeight L a₁) Fk
            (fun r => (β : ℂ)⁻¹ * Eτ r)) Zm p.2.1 p.2.2 Y p.1)
      ((XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
        {ψh : unitPts Gp × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ}) ×ˢ
        {w : ℂ × ℂ | (‖w.1‖ + ‖w.2‖) * markedRad d L N k a₁ κ cψ cc < δ₁})) := by
  have hC := flCore_of hB hF
  have hEan' : AnalyticOnNhd ℂ (fun r : RawData d L (N₁ * L ^ m₁) (k + 1) N => (β : ℂ)⁻¹ * Eτ r)
      (XiCRaw Gj (compWeight L a₁) ν j b
        (b ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl)) :=
    analyticOnNhd_const.mul hEan
  have hEbd' : ∀ r ∈ XiCRaw Gj (compWeight L a₁) ν j b
      (b ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl),
      ‖(β : ℂ)⁻¹ * Eτ r‖ ≤ (β⁻¹ * Bτ) * Real.exp (-(κdec - 1) * treeLenCovOne m₀ j X) := by
    intro r hr
    rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hβ.le, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hEbd r hr) (inv_nonneg.2 hβ.le)
  have hEb : 0 ≤ β⁻¹ * Bτ := mul_nonneg (inv_nonneg.2 hβ.le) hBτ
  have hΦan := eTermFun_analytic_of_one_le hb₁ hbC hB hF hFkan hFk hEan'
  have hR : ∀ t ∈ FlReal Gp Hm a₁ ν BG κ eps X₁f BG₂ δ₁, ∀ (a b : ℂ)
      (s : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) → ℂ)
      (F₁' : DecParams Gp × RawData d L (N₁ * L ^ m₁) (k + 1) N →
        (Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)) (D : BgData Gp N)
      (ψh : unitPts Gp × Fin N → ℂ),
      t.2.2.2 = markedHatPsiF a₁ ν hG' cc F₁' Zm a b
        (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s) (rawOf D) ψh →
      t ∈ FlRealLC Gp Hm a₁ ν BG κ eps X₁f BG₂ δ₁ := fun t ht a b s F₁' D ψh h =>
    ⟨ht, h ▸ isLayerConstant_markedHatPsiF hG hG' cc F₁' Zm a b _ _ _⟩
  have hΦbd := fun t (ht : t ∈ FlRealLC Gp Hm a₁ ν BG κ eps X₁f BG₂ δ₁) =>
    eTermFun_bound_of_one_le hb₁ hbC hB hF hFk hEbd' ht
  have hBM : BlockMargin Gp X₁f (∅ : Set (CTorus d L N₁ m₁ (k + 1))) :=
    fun x hx => absurd hx (Set.notMem_empty x)
  obtain ⟨e1, e2, -, e4, -, -, e7, -, e9⟩ := i5_functional_hat_marked_exposed_pair_of hC hk hG
    hG' cc hcψ Zm hMX hdm hα hsm hcov hX₁ hopt hκ₀ hκdec hκ h1 hlog hEb hΦan hR hΦbd
    hconn hrow (Z := ↑X₁f) subset_rfl hBM
    (fun t _ t' _ hφ _ hδ hag hψ => eTermFun_local_dir hB hF hcov hX₁ Fk _ hφ hδ hag hψ)
    hF₁an hF₁ hSolan hSolprop
  obtain ⟨-, -, -, hJ⟩ := marked_expansion_product_pair_of hC hk hG hG'
    cc hcψ Zm hMX hdm hα hsm hcov hX₁ hopt hκ₀ hκdec hκ h1 hlog hEb hΦan hR hΦbd
    hconn hrow (Z := ↑X₁f) subset_rfl hBM
    (fun t _ t' _ hφ _ hδ hag hψ => eTermFun_local_dir hB hF hcov hX₁ Fk _ hφ hδ hag hψ)
    hF₁an hF₁ hSolan hSolprop
  refine ⟨fun um tm hw D hD ψh hψh => ?_, e2, e4, e7, e9, hJ⟩
  rw [← e1 um tm hw D hD ψh hψh]
  exact (eTermFun_value hB hF hFk _ hD
    (markedTangDec_mem_flBallLC hC hk hG hG' cc hcψ Zm hMX hdm hα hsm hw hD hψh)).symm


end LabelJointGen

end Balaban.Fluctuation
