/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.LocalClassDensityMarksLabel
public import Balaban.Fluctuation.MarkedEvJoint
public import Balaban.Fluctuation.DecMarkBlocks

/-!
# Joint analyticity of the marked terms of an inherited label (`LocalClassDensityFamily`)

The input (M2) of `e0CoeffFamily_class_fromTower` asks for marks `G₁ θ j u Φ` of the inherited
energy that are jointly analytic in the parameter `θ` and the first mark `u` (the field `holG` of
`ParamMarkFamily`).  Label by label, the marks are the `t`-derivatives at `0` of the marked terms
`evDec … Eτ … um t Y (Θ, ψ̂)` of the expansion of the label functional `Eτ = eTermFun … ℰ^{(j)}`
along the masked tangent (`JointRep.deriv_classLabel_PJ_eq_sum_marked`).  The label functional is
analytic only on the layer-constant realizable triples `FlRealLC`, so the landed joint statement
`marked_expansion_product_pair` (analyticity asked on `FlReal`) does not apply; its core
`marked_expansion_product_pair_of` (analyticity on a region `R` containing the points met by the
fan) does, with `R = FlRealLC`.

* `exists_classOldLabel_maps`: the three maps of one label (the decoupled background `F₁` of `Gp`,
  the decoupled fluctuation solution `Sol` of `Hm`, the background `Fk` of the ambient set `Gk`),
  with their analyticity and defining properties.
* `classOldMarkedLocal_joint_of`: **for given maps**, the expansion of the label along the masked
  tangent with its clauses: the sum identity (`flComp` of the label at the masked tangent is the sum
  of the marked terms over the decoupled domains), locality (`AgHatDir`), the bound on closed
  bidiscs, the Cauchy estimate of the mark derivative, mark-locality, and **joint analyticity of the
  marked terms in `((Θ, ψ̂), (um, tm))`** on `(Ξ^c × B̂) × W`,
  `W = {(u, t) | (‖u‖ + ‖t‖) · markedRad < δ₁}`.
* `classOldMarkedLocal_blockMarks_of`: **the block-level marks of a label** for a step `S`
  (`Gp = S.G'`), given maps and any block index `mb`:
  `Φ ↦ ∂_t evDec … Eτ … um t Y (Θ, S.hatOf mb ρ hp Φ)|_{t=0}` depends only on the blocks of any
  `mb`-cell union `Y′ ⊇ Y`, is continuous and measurable, is bounded by
  `β⁻¹ E₀ e^{-κ₀ d(X) - 2κ_dec d(Y)} / t₀`, and is analytic in `(e, u)` on `physV × {‖u‖ < a}`
  (`deriv_evDec_hatOf_fields`, with `markedEv_physV_of_joint` for the analyticity on `physV`).  The
  block index of (M2) is `1`, while the cover of the label expansion has the index `C.m₀` of the
  class; the landed `decMarkG` uses one index for both, which is why the block index is free here.
* `StepSetting.JointRep.deriv_classLabel_PJ_eq_sum_marked_joint_of`: **the mark identity of the
  label for the same given maps**: the derivative at `0` of
  `t ↦ ℰ^{(j)}(y, X; Jr.PJ j (rawOf D, s ψ̂ + t v_z))` is `β ∑_Y ∂_t|₀` of the marked terms
  (`deriv_classLabel_PJ_eq_sum_marked_of` with the expansion property from
  `classOldMarkedLocal_joint_of`).  The maps of the landed `deriv_classLabel_PJ_eq_sum_marked` are
  hidden in an existential, so the identity is restated for given maps.

The composed family `G₁` of (M2) (rooting of the label domains into the common labels, the cut-off
outside the chart and the disc of `u`, the sum over the labels of the class) and the activity family
(M1) are not constructed here.
-/

@[expose] public section

namespace Balaban.Fluctuation

open MeasureTheory Balaban Balaban.Localization Balaban.Multiscale
  Balaban.Background Balaban.SmallField Balaban.SmallField.Def6 Balaban.SmallField.Def6v2
  Balaban.SmallField.GsSpec Balaban.Analysis Balaban.Polymer Finset Matrix

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ ϱ₁ ϱ₂ ϱm : ℝ}

section Maps

variable {Gp : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
  {Gk : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ₁}
  {Gj : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ₂}
  {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}
  {a₁ ν c BG κ r₀ eps δ₃ : ℝ} {X₀ X₁f : Finset (CTorus d L N₁ m₁ (k + 1))}
  {Kc Cx c₂ BG₂ δ₁ δfl : ℝ} {j : ℕ}

/-- **The maps of one inherited label.**  Under a background setting `hB` and a fluctuation
setting `hF`, there are a decoupled background map `F₁` of `Gp`, a decoupled fluctuation solution
`Sol` of `Hm` and a background map `Fk` of the ambient set `Gk`, analytic on their domains, with
their defining properties (`i4b_analytic`, `Dec2.i4a_analytic`, `theorem72_analytic`). -/
theorem exists_classOldLabel_maps
    (hB : BgSetting N Gp Gk Gj a₁ ν c BG κ r₀ eps δ₃ X₀ X₁f j)
    (hF : FlSetting N Gp Gk Hm a₁ ν κ BG eps δ₃ Kc Cx c₂ BG₂ δ₁ δfl X₁f) :
    ∃ (F₁ : DecParams Gp × RawData d L (N₁ * L ^ m₁) (k + 1) N →
        (Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ))
      (Sol : Dec2.DecParams (coverOf Gp) × Edat Hm N → (Hm.Ω 1 × Fin N → ℂ) × (Hm.Ω 1 → ℂ))
      (Fk : RawData d L (N₁ * L ^ m₁) (k + 1) N → (Gk.Ω 1 × Fin N → ℂ) × (Gk.Ω 1 → ℂ)),
      AnalyticOnNhd ℂ F₁ {q | (∀ P, ‖q.1 P‖ < Real.exp κ) ∧ ∃ D : BgData Gp N,
        InUnionDomainC Gp (bgC0 d L N) (c7 d L N BG κ) ν D ∧ q.2 = (D.Ψ, D.h)} ∧
      (∀ (s : DecParams Gp) (D : BgData Gp N), (∀ P, ‖s P‖ < Real.exp κ) →
        InUnionDomainC Gp (bgC0 d L N) (c7 d L N BG κ) ν D → ∀ (φ : Gp.Ω 1 × Fin N → ℂ)
          (α : Gp.Ω 1 → ℂ), IsDecBg Gp (compWeight L a₁) ν (rho4 d L N BG κ) s D φ α →
          F₁ (s, rawOf D) = (φ, α)) ∧
      AnalyticOnNhd ℂ Sol {p | (∀ P, ‖p.1 P‖ < Real.exp κ) ∧
        StrictDataM Hm N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2} ∧
      (∀ p : Dec2.DecParams (coverOf Gp) × Edat Hm N, (∀ P, ‖p.1 P‖ < Real.exp κ) →
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
              (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol p).2)) ∧
      AnalyticOnNhd ℂ Fk {p | ∃ D : BgData Gk N,
        InUnionDomainC Gk (bgC0 d L N) (bgC1 d L N) ν D ∧ p = (D.Ψ, D.h)} ∧
      (∀ D : BgData Gk N, InUnionDomainC Gk (bgC0 d L N) (bgC1 d L N) ν D →
        Fk (rawOf D) = (bgFieldC Gk (compWeight L a₁) ν (bgC0 d L N) D,
          bgMultC Gk (compWeight L a₁) ν (bgC0 d L N) D)) := by
  have hC := flCore_of hB hF
  have hd0 : 0 < d := by have := hC.HBp.hd; omega
  have hB2 : 0 ≤ 2 * (K4 d L N BG κ * (xiC1 d * eps)) :=
    mul_nonneg (by norm_num) (mul_nonneg (K4_pos hC.hS.fam.2.1 hd0).le
      (by have := one_le_xiC1 d; have := hC.eps_pos; positivity))
  obtain ⟨Fk, hFkan, hFk⟩ := theorem72_analytic (G := Gk) (a := compWeight L a₁) (ν := ν) hB.HBk
  obtain ⟨F₁, hF₁an, hF₁⟩ := i4b_analytic hC.hS hC.Sp hC.HBp hC.hκ.le hC.hM
  obtain ⟨Sol, hSolan, hSolprop⟩ := Dec2.i4a_analytic (N := N) hC.hS2.fam hC.hS2.an
    hC.SM.toCoverBase hC.hκ.le hC.hM2 false hB2 hC.δ₁_pos.le hC.B_le hC.δ₁_le
  exact ⟨F₁, Sol, Fk, hF₁an, hF₁, hSolan, hSolprop, hFkan, hFk⟩

end Maps

section LabelJoint

variable {Gp : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
  {Gk : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ₁}
  {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}
  {a₁ ν c BG κ r₀ eps δ₃ : ℝ} {X₀ X₁f : Finset (CTorus d L N₁ m₁ (k + 1))}
  {Kc Cx c₂ BG₂ δ₁ δfl : ℝ} {X 𝒦X : Set (CTorus d L N₁ m₁ (k + 1))}

/-- **The expansion of one inherited label along the masked tangent, for given maps, with joint
analyticity of the marked terms.**  For a label `τ = (j, y, X)` of the class `C` with a localized
ambient set `Gk` (the hypotheses of `classOldMarkedLocal_sum`) and given maps `(F₁, Sol, Fk)` with
their analyticity and defining properties, for every mask `Zm`, the marked terms
`evDec … Eτ … um tm Y (Θ, ψ̂)` of the label functional `Eτ = eTermFun … (β⁻¹ ℰ^{(j)}(y, X; ·))`:

1. sum to `flComp` of the label at the masked tangent, at every datum of the chart, every hat
   variable of the box and every pair of marks of the radius set `W`;
2. are local: `AgHatDir Y` on the data at fixed marks;
3. are bounded by `β⁻¹ E₀ e^{-κ₀ d(X) - 2 κ_dec d(Y)}` on every closed bidisc of `W`;
4. have mark derivatives at `t = 0` bounded by that bound divided by `t₀` (Cauchy);
5. do not depend on the second mark when no site of `Y` has its unit point in the mask;
6. are **analytic in `((Θ, ψ̂), (um, tm))`** at every point of `(Ξ^c × B̂) × W` (the core
   `marked_expansion_product_pair_of` with the region `FlRealLC`). -/
theorem classOldMarkedLocal_joint_of {b : ℝ} (hb₁ : 1 ≤ b) (hbC : b ≤ scaledC0 d)
    {P : Consts} {Dom : FieldDom d L N₁ m₁ (k + 1) N ϱ}
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
    (hchart : ∀ r ∈ XiCRaw (C.Tm.gs j X) (compWeight L a₁) ν j b
      (b ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl),
      Dom.dom j (C.Tm.gs j X) r.1 r.2)
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
      flComp hB hF (fun r => (β : ℂ)⁻¹ * C.Tm.E j y X r.1 r.2)
          (rawOf D, markedTangDec hG' cc a₁ ν Zm um tm D ψh) =
        ∑ Y ∈ polyDom Gp X₁f C.m₀ j 𝒦X, evDec X₁f C.m₀ j 𝒦X a₁ ν hG' cc F₁ Sol
          (eTermFun Gp Gk (C.Tm.gs j X) Hm (compWeight L a₁) Fk
            (fun r => (β : ℂ)⁻¹ * C.Tm.E j y X r.1 r.2)) Zm um tm Y (rawOf D, ψh)) ∧
    -- 2. locality
    (∀ um tm : ℂ, (‖um‖ + ‖tm‖) * markedRad d L N k a₁ κ cψ cc < δ₁ →
      ∀ Y, ∀ u ∈ XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
        {ψh : unitPts Gp × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ},
      ∀ u' ∈ XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
        {ψh : unitPts Gp × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ},
      AgHatDir hG' Y u u' →
        evDec X₁f C.m₀ j 𝒦X a₁ ν hG' cc F₁ Sol
          (eTermFun Gp Gk (C.Tm.gs j X) Hm (compWeight L a₁) Fk
            (fun r => (β : ℂ)⁻¹ * C.Tm.E j y X r.1 r.2)) Zm um tm Y u =
        evDec X₁f C.m₀ j 𝒦X a₁ ν hG' cc F₁ Sol
          (eTermFun Gp Gk (C.Tm.gs j X) Hm (compWeight L a₁) Fk
            (fun r => (β : ℂ)⁻¹ * C.Tm.E j y X r.1 r.2)) Zm um tm Y u') ∧
    -- 3. bound on closed bidiscs
    (∀ a b : ℝ, 0 ≤ a → 0 ≤ b → (a + b) * markedRad d L N k a₁ κ cψ cc < δ₁ →
      ∀ um tm : ℂ, ‖um‖ ≤ a → ‖tm‖ ≤ b →
      ∀ Y, ∀ u ∈ XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
        {ψh : unitPts Gp × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ},
      ‖evDec X₁f C.m₀ j 𝒦X a₁ ν hG' cc F₁ Sol
          (eTermFun Gp Gk (C.Tm.gs j X) Hm (compWeight L a₁) Fk
            (fun r => (β : ℂ)⁻¹ * C.Tm.E j y X r.1 r.2)) Zm um tm Y u‖ ≤
        (β⁻¹ * P.E₀) * Real.exp (-κ₀ * treeLenCovOne C.m₀ j X - 2 * κdec * treeLenCov Gp C.m₀ Y)) ∧
    -- 4. Cauchy estimate
    (∀ a b t₀ : ℝ, 0 ≤ a → 0 ≤ b → 0 < t₀ → t₀ ≤ b →
      (a + b) * markedRad d L N k a₁ κ cψ cc < δ₁ →
      ∀ um : ℂ, ‖um‖ ≤ a →
      ∀ Y, ∀ u ∈ XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
        {ψh : unitPts Gp × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ},
      ‖deriv (fun t : ℂ => evDec X₁f C.m₀ j 𝒦X a₁ ν hG' cc F₁ Sol
          (eTermFun Gp Gk (C.Tm.gs j X) Hm (compWeight L a₁) Fk
            (fun r => (β : ℂ)⁻¹ * C.Tm.E j y X r.1 r.2)) Zm um t Y u) 0‖ ≤
        (β⁻¹ * P.E₀) *
          Real.exp (-κ₀ * treeLenCovOne C.m₀ j X - 2 * κdec * treeLenCov Gp C.m₀ Y) / t₀) ∧
    -- 5. mark-locality
    (∀ um tm tm' : ℂ, (‖um‖ + ‖tm‖) * markedRad d L N k a₁ κ cψ cc < δ₁ →
      (‖um‖ + ‖tm'‖) * markedRad d L N k a₁ κ cψ cc < δ₁ →
      ∀ Y : Set (CTorus d L N₁ m₁ (k + 1)), (∀ y ∈ Y, unitPt hG' y ∉ Zm) →
      ∀ u ∈ XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
        {ψh : unitPts Gp × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ},
      evDec X₁f C.m₀ j 𝒦X a₁ ν hG' cc F₁ Sol
          (eTermFun Gp Gk (C.Tm.gs j X) Hm (compWeight L a₁) Fk
            (fun r => (β : ℂ)⁻¹ * C.Tm.E j y X r.1 r.2)) Zm um tm Y u =
        evDec X₁f C.m₀ j 𝒦X a₁ ν hG' cc F₁ Sol
          (eTermFun Gp Gk (C.Tm.gs j X) Hm (compWeight L a₁) Fk
            (fun r => (β : ℂ)⁻¹ * C.Tm.E j y X r.1 r.2)) Zm um tm' Y u) ∧
    -- 6. joint analyticity
    (∀ Y, AnalyticOnNhd ℂ
      (fun p : (RawData d L (N₁ * L ^ m₁) (k + 1) N × (unitPts Gp × Fin N → ℂ)) × (ℂ × ℂ) =>
        evDec X₁f C.m₀ j 𝒦X a₁ ν hG' cc F₁ Sol
          (eTermFun Gp Gk (C.Tm.gs j X) Hm (compWeight L a₁) Fk
            (fun r => (β : ℂ)⁻¹ * C.Tm.E j y X r.1 r.2)) Zm p.2.1 p.2.2 Y p.1)
      ((XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
        {ψh : unitPts Gp × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ}) ×ˢ
        {w : ℂ × ℂ | (‖w.1‖ + ‖w.2‖) * markedRad d L N k a₁ κ cψ cc < δ₁})) := by
  have hC := flCore_of hB hF
  obtain ⟨hEan, hEbd⟩ := classOldDecEnergy_chart_radius (N := N) C hm hcl hβ hκP hE₀ a₁ ν δ₃ eps
    δfl hj1 hjk hXp hy hchart
  have hEb : 0 ≤ β⁻¹ * P.E₀ := mul_nonneg (inv_nonneg.2 hβ.le) hE₀
  have hΦan := eTermFun_analytic_of_one_le hb₁ hbC hB hF hFkan hFk hEan
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
    eTermFun_bound_of_one_le hb₁ hbC hB hF hFk hEbd ht
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

end LabelJoint

section BlockMarks

variable (S : StepSetting d L N₁ m₁ k N ϱ)
  {Gk : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ₁}
  {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}
  {a₁ ν c BG κ r₀ eps δ₃ : ℝ} {X₀ X₁f : Finset (CTorus d L N₁ m₁ (k + 1))}
  {Kc Cx c₂ BG₂ δ₁ δfl : ℝ} {X 𝒦X : Set (CTorus d L N₁ m₁ (k + 1))}

/-- **The block-level marks of one inherited label, for given maps and any block index `mb`.**  For
a step `S` (`Gp = S.G'`), a label `τ = (j, y, X)` of the class `C` with the hypotheses of
`classOldMarkedLocal_joint_of`, given maps `(F₁, Sol, Fk)`, a mask `Zm`, a block index `mb` and a
clamp radius `0 < ρ ≤ c_ψ`, the block-level mark of the domain `Y`,
`Φ ↦ ∂_t evDec … Eτ … Zm um t Y (Θ, S.hatOf mb ρ hp Φ)|_{t=0}`:

1. depends only on the blocks inside any `mb`-cell union `Y′ ⊇ Y`;
2. is continuous, hence measurable, in the block configuration;
3. is bounded by `β⁻¹ E₀ e^{-κ₀ d(X) - 2 κ_dec d(Y)} / t₀` for every configuration
   (`‖um‖ ≤ a`, `0 < t₀ ≤ b`, `(a + b) · markedRad < δ₁`);
4. is analytic in `(e, u)` on `physV × {‖u‖ < a}` for every configuration (`b > 0`,
   `(a + b) · markedRad < δ₁`): the shape of the field `holG` of `ParamMarkFamily`. -/
theorem classOldMarkedLocal_blockMarks_of {b : ℝ} (hb₁ : 1 ≤ b) (hbC : b ≤ scaledC0 d)
    {P : Consts} {Dom : FieldDom d L N₁ m₁ (k + 1) N ϱ}
    (C : StepClass d L N₁ m₁ k N ϱ) (hm : P.m₀ = C.m₀) (hcl : SFTermClauses P Dom C.Tm)
    {β : ℝ} (hβ : 0 < β) (hE₀ : 0 ≤ P.E₀) {j : ℕ} (hj1 : 1 ≤ j) (hjk : j ≤ k)
    {y : CTorus d L N₁ m₁ (k + 1)} (hXp : IsPolyDom C.m₀ j X) (hy : y ∈ X)
    (hB : BgSetting N S.G' Gk (C.Tm.gs j X) a₁ ν c BG κ r₀ eps δ₃ X₀ X₁f j)
    (hF : FlSetting N S.G' Gk Hm a₁ ν κ BG eps δ₃ Kc Cx c₂ BG₂ δ₁ δfl X₁f)
    (hG : IsLevel Hm k) (cc : ℂ)
    {cψ : ℝ} (hcψ : 0 ≤ cψ)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δc : ℝ}
    (hdm : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    (hcov : CovSetup S.G' C.m₀ j X 𝒦X)
    (hX₁ : (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) = X1 S.G' C.m₀ j 𝒦X)
    (hconn : HatConn S.G') (hrow : RowInHat (coverOf S.G') Hm (compWeight L a₁) ν)
    (hopt : ∃ (W₀ : Finset (CTorus d L N₁ m₁ (k + 1)))
      (E₀ : Finset (CTorus d L N₁ m₁ (k + 1) × CTorus d L N₁ m₁ (k + 1))),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ X) ∧ MeetsOne C.m₀ j 𝒦X W₀ ∧
        bondCost (scaleW L C.m₀ m₁ j) E₀ = treeLenCovOne C.m₀ j X)
    {κdec κ₀ : ℝ} (hκ₀ : 0 ≤ κ₀) (hκdec : 3 * κ₀ + 3 ≤ κdec)
    (hκ : 4 * d * (((2 * L + 1) ^ d : ℕ) : ℝ) * κdec ≤ κ) (h1 : 1 ≤ (κ / 2 - 1) / 2)
    (hlog : Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) * (((L ^ C.m₀) ^ d : ℕ) : ℝ)) ≤ (κ / 2 - 1) / 2)
    (hκP : κdec - 1 ≤ P.κ)
    (hchart : ∀ r ∈ XiCRaw (C.Tm.gs j X) (compWeight L a₁) ν j b
      (b ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl),
      Dom.dom j (C.Tm.gs j X) r.1 r.2)
    {F₁ : DecParams S.G' × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      (S.G'.Ω 1 × Fin N → ℂ) × (S.G'.Ω 1 → ℂ)}
    (hF₁an : AnalyticOnNhd ℂ F₁ {q | (∀ P, ‖q.1 P‖ < Real.exp κ) ∧ ∃ D : BgData S.G' N,
      InUnionDomainC S.G' (bgC0 d L N) (c7 d L N BG κ) ν D ∧ q.2 = (D.Ψ, D.h)})
    (hF₁ : ∀ (s : DecParams S.G') (D : BgData S.G' N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC S.G' (bgC0 d L N) (c7 d L N BG κ) ν D → ∀ (φ : S.G'.Ω 1 × Fin N → ℂ)
        (α : S.G'.Ω 1 → ℂ), IsDecBg S.G' (compWeight L a₁) ν (rho4 d L N BG κ) s D φ α →
        F₁ (s, rawOf D) = (φ, α))
    {Sol : Dec2.DecParams (coverOf S.G') × Edat Hm N → (Hm.Ω 1 × Fin N → ℂ) × (Hm.Ω 1 → ℂ)}
    (hSolan : AnalyticOnNhd ℂ Sol {p | (∀ P, ‖p.1 P‖ < Real.exp κ) ∧
      StrictDataM Hm N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2})
    (hSolprop : ∀ p : Dec2.DecParams (coverOf S.G') × Edat Hm N, (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM Hm N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2 →
        (Sol p).1 = dphi Hm (Dec2.decG (coverOf S.G') Hm (compWeight L a₁) ν p.1) p.2.2.1 p.2.1
          (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol p).2 ∧
        Dec2.DecFixed (coverOf S.G') Hm (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
          (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol p).2 ∧
        Small Hm (Sol p).2 (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
        Small Hm (Sol p).2 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        SupBounds Hm (Sol p).1 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        (∀ δα' : Hm.Ω 1 → ℂ, Small Hm δα' (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf S.G') Hm (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
            (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol p).2))
    {Fk : RawData d L (N₁ * L ^ m₁) (k + 1) N → (Gk.Ω 1 × Fin N → ℂ) × (Gk.Ω 1 → ℂ)}
    (hFkan : AnalyticOnNhd ℂ Fk {p | ∃ D : BgData Gk N,
      InUnionDomainC Gk (bgC0 d L N) (bgC1 d L N) ν D ∧ p = (D.Ψ, D.h)})
    (hFk : ∀ D : BgData Gk N, InUnionDomainC Gk (bgC0 d L N) (bgC1 d L N) ν D →
      Fk (rawOf D) = (bgFieldC Gk (compWeight L a₁) ν (bgC0 d L N) D,
        bgMultC Gk (compWeight L a₁) ν (bgC0 d L N) D))
    (Zm : Finset (unitPts S.G')) (mb : ℕ) {ρ : ℝ} (hρ : 0 < ρ) (hρc : ρ ≤ cψ)
    (hp : 0 < S.p₁) :
      (∀ (Y Y' : Set (CTorus d L N₁ m₁ (k + 1))), Y ⊆ Y' →
        (∀ y ∈ Y', box (cbase (cellSide L mb m₁ (k + 1)) y) (cellSide L mb m₁ (k + 1)) ⊆ Y') →
        ∀ Θ ∈ XiCRaw S.G' (compWeight L a₁) ν (k + 1) 1 eps, ∀ um : ℂ,
        (‖um‖ + ‖(0 : ℂ)‖) * markedRad d L N k a₁ κ cψ cc < δ₁ →
        DepOn (blocksOf mb (k + 1) Set.univ Y')
          (fun Φ : ∀ b, (S.blockSplit mb hp).Ωb b =>
            deriv (fun t : ℂ => evDec X₁f C.m₀ j 𝒦X a₁ ν S.hG' cc F₁ Sol
            (eTermFun S.G' Gk (C.Tm.gs j X) Hm (compWeight L a₁) Fk
              (fun r => (β : ℂ)⁻¹ * C.Tm.E j y X r.1 r.2)) Zm um t Y
            (Θ, S.hatOf mb ρ hp Φ)) 0)) ∧
      (∀ Y, ∀ Θ ∈ XiCRaw S.G' (compWeight L a₁) ν (k + 1) 1 eps, ∀ um : ℂ,
        (‖um‖ + ‖(0 : ℂ)‖) * markedRad d L N k a₁ κ cψ cc < δ₁ →
        Continuous (fun Φ : ∀ b, (S.blockSplit mb hp).Ωb b =>
          deriv (fun t : ℂ => evDec X₁f C.m₀ j 𝒦X a₁ ν S.hG' cc F₁ Sol
            (eTermFun S.G' Gk (C.Tm.gs j X) Hm (compWeight L a₁) Fk
              (fun r => (β : ℂ)⁻¹ * C.Tm.E j y X r.1 r.2)) Zm um t Y
            (Θ, S.hatOf mb ρ hp Φ)) 0) ∧
        Measurable (fun Φ : ∀ b, (S.blockSplit mb hp).Ωb b =>
          deriv (fun t : ℂ => evDec X₁f C.m₀ j 𝒦X a₁ ν S.hG' cc F₁ Sol
            (eTermFun S.G' Gk (C.Tm.gs j X) Hm (compWeight L a₁) Fk
              (fun r => (β : ℂ)⁻¹ * C.Tm.E j y X r.1 r.2)) Zm um t Y
            (Θ, S.hatOf mb ρ hp Φ)) 0)) ∧
      (∀ Y, ∀ Θ ∈ XiCRaw S.G' (compWeight L a₁) ν (k + 1) 1 eps, ∀ a b t₀ : ℝ, 0 ≤ a → 0 ≤ b →
        0 < t₀ → t₀ ≤ b → (a + b) * markedRad d L N k a₁ κ cψ cc < δ₁ → ∀ um : ℂ, ‖um‖ ≤ a →
        ∀ Φ : (∀ b, (S.blockSplit mb hp).Ωb b),
        ‖deriv (fun t : ℂ => evDec X₁f C.m₀ j 𝒦X a₁ ν S.hG' cc F₁ Sol
            (eTermFun S.G' Gk (C.Tm.gs j X) Hm (compWeight L a₁) Fk
              (fun r => (β : ℂ)⁻¹ * C.Tm.E j y X r.1 r.2)) Zm um t Y
            (Θ, S.hatOf mb ρ hp Φ)) 0‖ ≤
          (β⁻¹ * P.E₀) *
            Real.exp (-κ₀ * treeLenCovOne C.m₀ j X - 2 * κdec * treeLenCov S.G' C.m₀ Y) / t₀) ∧
      (∀ Y, ∀ Φ : (∀ b, (S.blockSplit mb hp).Ωb b), ∀ a b : ℝ, 0 ≤ a → 0 < b →
        (a + b) * markedRad d L N k a₁ κ cψ cc < δ₁ →
        AnalyticOnNhd ℂ (fun p : physParam N S × ℂ =>
          deriv (fun t : ℂ => evDec X₁f C.m₀ j 𝒦X a₁ ν S.hG' cc F₁ Sol
            (eTermFun S.G' Gk (C.Tm.gs j X) Hm (compWeight L a₁) Fk
              (fun r => (β : ℂ)⁻¹ * C.Tm.E j y X r.1 r.2)) Zm p.2 t Y
            ((p.1.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N), S.hatOf mb ρ hp Φ)) 0)
          (physV S a₁ ν eps ×ˢ Metric.ball (0 : ℂ) a)) := by
  obtain ⟨-, e2, e3, e4, -, hJ⟩ := classOldMarkedLocal_joint_of hb₁ hbC C hm hcl hβ hE₀ hj1 hjk
    hXp hy hB hF S.hk1 hG S.hG' cc hcψ hMX hdm hα hsm hcov hX₁ hconn hrow hopt hκ₀ hκdec hκ h1
    hlog hκP hchart hF₁an hF₁ hSolan hSolprop hFkan hFk Zm
  obtain ⟨-, hJ4, -⟩ := markedEv_physV_of_joint S (flCore_of hB hF) cc Zm
    (B := fun Y => (β⁻¹ * P.E₀) *
      Real.exp (-κ₀ * treeLenCovOne C.m₀ j X - 2 * κdec * treeLenCov S.G' C.m₀ Y)) hJ e3
  exact deriv_evDec_hatOf_fields S mb F₁ Sol (B := fun Y => (β⁻¹ * P.E₀) *
      Real.exp (-κ₀ * treeLenCovOne C.m₀ j X - 2 * κdec * treeLenCov S.G' C.m₀ Y)) e2 e4 hJ hJ4
    hρ hρc hp

end BlockMarks

section JointIdentity

namespace StepSetting.JointRep

variable {S : StepSetting d L N₁ m₁ k N ϱ} {eps pp : ℝ} (Jr : S.JointRep eps pp)

open Classical in
/-- **The mark identity of an inherited label, for given maps.**  For a step `S`, a label
`τ = (j, y, X)` of the class `C` with the hypotheses of `deriv_classLabel_PJ_eq_sum_marked`, and
given maps `(F₁, Sol, Fk)` with their analyticity and defining properties: at every datum `D` of
the chart, every root `z`, every `x` with `|ψ̂(x)| ≤ c_ψ` and every first mark `s` with `s ψ̂`
inside the box of `Jr` and `‖s‖` in the radius of the marks, the derivative at `0` of
`t ↦ ℰ^{(j)}(y, X; Jr.PJ j (rawOf D, s ψ̂ + t v_z))` is
`β ∑_Y ∂_t|₀ evDec … (blockU z) s t Y (rawOf D, ψ̂)` for the marked terms of these maps
(`deriv_classLabel_PJ_eq_sum_marked_of`, its expansion property from
`classOldMarkedLocal_joint_of`), and this function of `t` is differentiable at `0`.  With
`classOldMarkedLocal_blockMarks_of` for the same maps, the marks of the label are jointly
analytic. -/
theorem deriv_classLabel_PJ_eq_sum_marked_joint_of {b : ℝ} (hb₁ : 1 ≤ b)
    (hbC : b ≤ scaledC0 d) {P : Consts} {Dom : FieldDom d L N₁ m₁ (k + 1) N ϱ}
    (C : StepClass d L N₁ m₁ k N ϱ) (hm : P.m₀ = C.m₀) (hcl : SFTermClauses P Dom C.Tm)
    (hE₀ : 0 ≤ P.E₀) {j : ℕ} (hj1 : 1 ≤ j) (hjk : j ≤ k)
    {y : CTorus d L N₁ m₁ (k + 1)} {X : Set (CTorus d L N₁ m₁ (k + 1))}
    (hXp : IsPolyDom C.m₀ j X) (hy : y ∈ X)
    (hS : GsSpecStrong j (hjk.trans (Nat.le_succ k)) X (C.Tm.gs j X))
    {Gk : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ₁}
    {c BG κ r₀ δ₃ Kc Cx c₂ BG₂ δ₁ δfl : ℝ} {X₀ X₁f : Finset (CTorus d L N₁ m₁ (k + 1))}
    (hB : BgSetting N S.G' Gk (C.Tm.gs j X) S.a₁ S.ν c BG κ r₀ eps δ₃ X₀ X₁f j)
    (hF : FlSetting N S.G' Gk (stepG d L N₁ m₁ k ϱ) S.a₁ S.ν κ BG eps δ₃ Kc Cx c₂ BG₂ δ₁ δfl
      X₁f)
    (hc7 : c7 d L N BG κ ≤ thm73C3 d L N) {R : ℝ} (hR : 2 ≤ R)
    (hsmR : 2 * (compC4 d * (bgK1 d L N * (xiC1 d * eps))) + 5 * (R * δ₁) ≤ bgC1 d L N)
    (hRs : R * δ₁ ≤ deltaStar d L N) (hsmall : cK2 d L N * (R * δ₁) < bgC0 d L N / 2)
    (hnum : cK2 d L N * δ₁ ≤ c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8))
    (hnum' : cK2' d L N (famConst d L BG₂ κ) * δ₁ ≤
      c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8))
    {cψ : ℝ} (hcψ : 0 ≤ cψ)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δc : ℝ}
    (hdm : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    {𝒦X : Set (CTorus d L N₁ m₁ (k + 1))} (hcov : CovSetup S.G' C.m₀ j X 𝒦X)
    (hX₁ : (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) = X1 S.G' C.m₀ j 𝒦X)
    (hconn : HatConn S.G')
    (hrow : RowInHat (coverOf S.G') (stepG d L N₁ m₁ k ϱ) (compWeight L S.a₁) S.ν)
    (hopt : ∃ (W₀ : Finset (CTorus d L N₁ m₁ (k + 1)))
      (E₀ : Finset (CTorus d L N₁ m₁ (k + 1) × CTorus d L N₁ m₁ (k + 1))),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ X) ∧ MeetsOne C.m₀ j 𝒦X W₀ ∧
        bondCost (scaleW L C.m₀ m₁ j) E₀ = treeLenCovOne C.m₀ j X)
    {κdec κ₀ : ℝ} (hκ₀ : 0 ≤ κ₀) (hκdec : 3 * κ₀ + 3 ≤ κdec)
    (hκ : 4 * d * (((2 * L + 1) ^ d : ℕ) : ℝ) * κdec ≤ κ) (h1 : 1 ≤ (κ / 2 - 1) / 2)
    (hlog : Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) * (((L ^ C.m₀) ^ d : ℕ) : ℝ)) ≤ (κ / 2 - 1) / 2)
    (hκP : κdec - 1 ≤ P.κ)
    (hchart : ∀ r ∈ XiCRaw (C.Tm.gs j X) (compWeight L S.a₁) S.ν j b
      (b ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl),
      Dom.dom j (C.Tm.gs j X) r.1 r.2)
    (hβ : 0 < S.β)
    {F₁ : DecParams S.G' × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      (S.G'.Ω 1 × Fin N → ℂ) × (S.G'.Ω 1 → ℂ)}
    (hF₁an : AnalyticOnNhd ℂ F₁ {q | (∀ P, ‖q.1 P‖ < Real.exp κ) ∧ ∃ D : BgData S.G' N,
      InUnionDomainC S.G' (bgC0 d L N) (c7 d L N BG κ) S.ν D ∧ q.2 = (D.Ψ, D.h)})
    (hF₁ : ∀ (s : DecParams S.G') (D : BgData S.G' N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC S.G' (bgC0 d L N) (c7 d L N BG κ) S.ν D → ∀ (φ : S.G'.Ω 1 × Fin N → ℂ)
        (α : S.G'.Ω 1 → ℂ), IsDecBg S.G' (compWeight L S.a₁) S.ν (rho4 d L N BG κ) s D φ α →
        F₁ (s, rawOf D) = (φ, α))
    {Sol : Dec2.DecParams (coverOf S.G') × Edat (stepG d L N₁ m₁ k ϱ) N →
      ((stepG d L N₁ m₁ k ϱ).Ω 1 × Fin N → ℂ) × ((stepG d L N₁ m₁ k ϱ).Ω 1 → ℂ)}
    (hSolan : AnalyticOnNhd ℂ Sol {p | (∀ P, ‖p.1 P‖ < Real.exp κ) ∧
      StrictDataM (stepG d L N₁ m₁ k ϱ) N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2})
    (hSolprop : ∀ p : Dec2.DecParams (coverOf S.G') × Edat (stepG d L N₁ m₁ k ϱ) N,
      (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM (stepG d L N₁ m₁ k ϱ) N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2 →
        (Sol p).1 = dphi (stepG d L N₁ m₁ k ϱ)
            (Dec2.decG (coverOf S.G') (stepG d L N₁ m₁ k ϱ) (compWeight L S.a₁) S.ν p.1)
            p.2.2.1 p.2.1
            (pertSource (stepG d L N₁ m₁ k ϱ) (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2)
            (Sol p).2 ∧
        Dec2.DecFixed (coverOf S.G') (stepG d L N₁ m₁ k ϱ) (compWeight L S.a₁) S.ν p.1 false
          p.2.2.1 p.2.1
          (pertSource (stepG d L N₁ m₁ k ϱ) (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) (Sol p).2 ∧
        Small (stepG d L N₁ m₁ k ϱ) (Sol p).2 (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
        Small (stepG d L N₁ m₁ k ϱ) (Sol p).2 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        SupBounds (stepG d L N₁ m₁ k ϱ) (Sol p).1 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        (∀ δα' : (stepG d L N₁ m₁ k ϱ).Ω 1 → ℂ,
          Small (stepG d L N₁ m₁ k ϱ) δα' (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf S.G') (stepG d L N₁ m₁ k ϱ) (compWeight L S.a₁) S.ν p.1 false
            p.2.2.1 p.2.1
            (pertSource (stepG d L N₁ m₁ k ϱ) (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) δα' →
          δα' = (Sol p).2))
    {Fk : RawData d L (N₁ * L ^ m₁) (k + 1) N → (Gk.Ω 1 × Fin N → ℂ) × (Gk.Ω 1 → ℂ)}
    (hFkan : AnalyticOnNhd ℂ Fk {p | ∃ D : BgData Gk N,
      InUnionDomainC Gk (bgC0 d L N) (bgC1 d L N) S.ν D ∧ p = (D.Ψ, D.h)})
    (hFk : ∀ D : BgData Gk N, InUnionDomainC Gk (bgC0 d L N) (bgC1 d L N) S.ν D →
      Fk (rawOf D) = (bgFieldC Gk (compWeight L S.a₁) S.ν (bgC0 d L N) D,
        bgMultC Gk (compWeight L S.a₁) S.ν (bgC0 d L N) D)) :
    ∀ D : BgData S.G' N, XiCData S.G' S.a S.ν (k + 1) 1 eps D →
    ∀ (z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1)))) (x : S.E),
      (∀ p, ‖yhat x p‖ ≤ cψ) → ∀ s : ℂ, (∀ p, ‖(s • yhat x) p‖ < pp) →
      ‖s‖ * (Real.sqrt N * (‖((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)‖ *
        (covSupConstC d L N (compWeight L S.a₁ k) κ * cψ))) < δ₁ →
      deriv (fun t : ℂ => C.Tm.E j y X
          (Jr.PJ j (rawOf D, s • yhat x + t • ((Jr.Mx (rawOf D))⁻¹ *ᵥ
            S.maskUC z (Jr.Mx (rawOf D) *ᵥ yhat x)))).1
          (Jr.PJ j (rawOf D, s • yhat x + t • ((Jr.Mx (rawOf D))⁻¹ *ᵥ
            S.maskUC z (Jr.Mx (rawOf D) *ᵥ yhat x)))).2) 0 =
        (S.β : ℂ) * ∑ Y ∈ polymerDomains
          (fun i : ParIdx S.G' (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) => i.1.1)
          S.G' C.m₀ (X1 S.G' C.m₀ j 𝒦X),
          deriv (fun t : ℂ => evTerm
            (fun i : ParIdx S.G' (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) => i.1.1) S.G' C.m₀
            (X1 S.G' C.m₀ j 𝒦X) (FFmarked X₁f S.a₁ S.ν S.hG'
              ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) F₁ Sol
              (eTermFun S.G' Gk (C.Tm.gs j X) (stepG d L N₁ m₁ k ϱ) (compWeight L S.a₁) Fk
                (fun r => (S.β : ℂ)⁻¹ * C.Tm.E j y X r.1 r.2)) (S.blockU z) s t) Y
            (rawOf D, yhat x)) 0 ∧
      DifferentiableAt ℂ (fun t : ℂ => C.Tm.E j y X
          (Jr.PJ j (rawOf D, s • yhat x + t • ((Jr.Mx (rawOf D))⁻¹ *ᵥ
            S.maskUC z (Jr.Mx (rawOf D) *ᵥ yhat x)))).1
          (Jr.PJ j (rawOf D, s • yhat x + t • ((Jr.Mx (rawOf D))⁻¹ *ᵥ
            S.maskUC z (Jr.Mx (rawOf D) *ᵥ yhat x)))).2) 0 := by
  refine Jr.deriv_classLabel_PJ_eq_sum_marked_of C hcl hj1 hjk hS hB hF hc7 hR hsmR hRs hsmall
    hnum hnum' hcψ hMX hdm hα hsm hβ (y := y) (𝒦X := 𝒦X) (fun z => ?_)
  obtain ⟨e1, -, -, -, -, hJ⟩ := classOldMarkedLocal_joint_of hb₁ hbC C hm hcl hβ hE₀ hj1 hjk
    hXp hy hB hF S.hk1 S.hG S.hG' ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) hcψ hMX hdm hα hsm hcov
    hX₁ hconn hrow hopt hκ₀ hκdec hκ h1 hlog hκP hchart hF₁an hF₁ hSolan hSolprop hFkan hFk
    (S.blockU z)
  refine ⟨fun um tm hw D hD ψh hψh => ?_, fun Y u hu w hw => ?_⟩
  · have key := e1 um tm hw D hD ψh hψh
    exact key
  · have key := AnalyticAt.comp_of_eq
      (g := fun p : (RawData d L (N₁ * L ^ m₁) (k + 1) N × (unitPts S.G' × Fin N → ℂ)) ×
          (ℂ × ℂ) => evDec X₁f C.m₀ j 𝒦X S.a₁ S.ν S.hG'
        ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) F₁ Sol
        (eTermFun S.G' Gk (C.Tm.gs j X) (stepG d L N₁ m₁ k ϱ) (compWeight L S.a₁) Fk
          (fun r => (S.β : ℂ)⁻¹ * C.Tm.E j y X r.1 r.2)) (S.blockU z) p.2.1 p.2.2 Y p.1)
      (f := fun w' : ℂ × ℂ => (u, w')) (hJ Y (u, w) ⟨hu, hw⟩)
      (analyticAt_const.prod analyticAt_id) rfl
    rw [Function.comp_def] at key
    exact key

end StepSetting.JointRep

end JointIdentity

end Balaban.Fluctuation
