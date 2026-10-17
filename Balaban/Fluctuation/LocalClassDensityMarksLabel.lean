/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.LocalClassDensityMarksH
public import Balaban.Fluctuation.LocalClassDensityMarks
public import Balaban.Fluctuation.DetCauchyChart
public import Balaban.Fluctuation.StepComplexOffFibreCoeff
public import Balaban.Fluctuation.LocalClassDensityHRep
public import Balaban.Inhabited.OffFibreE1Compare
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The marks of an inherited label at every datum of the chart

The input (M2) of `e0CoeffFamily_class_fromTower` asks, at every datum `D` of the chart (any
external field), for marks whose sum is the derivative of the inherited energy
`ℰ_k = Jr.EJ C = ∑_τ ℰ^{(j)}(y, X; Jr.PJ j ·)` in the masked direction
`v_z = C^{-1/2} 1_{B(z)} C^{1/2} ψ̂` (`fderiv_EJ_eq_sum_sigma` splits it label by label).  Here,
for one label `τ = (j, y, X)` with a localized ambient set `𝔹_k(X)` at its own separation index:

* `classOldMarkedLocal_sum`: **the expansion of the label along the masked tangent, localized
  ambient set.**  One pair of maps `(F₁, Sol)` of the decoupled background and fluctuation and one
  background map `Fk` of `𝔹_k(X)` such that, for every pair of marks `(um, tm)` of the radius set,
  every datum `D` of the chart and every hat variable of the box, `flComp` of the label at the
  masked tangent `markedTangDec … Zm um tm D ψ̂` is the sum over the decoupled domains `Y` of the
  marked terms `evTerm … (FFmarked … Zm um tm) Y (rawOf D, ψ̂)`, each analytic in the marks
  (`i5_functional_hat_marked_exposed_pair_of` with the label functional `eTermFun`; the landed
  `classOldMarksY_expansion` has the ambient set at the class index, which a local set
  `𝔹_k(X)` does not have);
* `StepSetting.JointRep.PJ_masked_eq_dataUCH`: the joint representative at the old spin
  `s ψ̂ + t v_z` is the composed pair of the free datum `H.dataUCH (ψ^{(k)} + s ψ' + t 1_{B(z)} ψ')`;
  `StepSetting.JointRep.classLabel_PJ_masked_eq_flComp`: the label term there is
  `β flComp Eτ (rawOf D, markedTangDec … (blockU z) s t D ψ̂)` (any field);
* `StepSetting.JointRep.deriv_classLabel_PJ_eq_sum_marked`: **the mark identity of the label at
  every chart datum.**  For `D` in the chart, `x` with `|ψ̂(x)| ≤ c_ψ` and a first mark `s` with
  `s ψ̂` inside the box of the joint representative, the derivative at `0` of
  `t ↦ ℰ^{(j)}(y, X; Jr.PJ j (rawOf D, s ψ̂ + t v_z))` is
  `β ∑_Y ∂_t|₀ evTerm … (FFmarked … (blockU z) s t) Y (rawOf D, ψ̂)`.  Proof: the joint representative
  at the old spin `s ψ̂ + t v_z` is the composed pair of the free datum
  (`JointRep.PJ_dataUCH`, `hatField_inv_mask_of_chart`), which is the endpoint of `flComp` at the
  masked tangent (`StepSettingH.classOldEndpointLocalH_liftC`, `markedTangDec_eq_liftC_raw`); then
  `classOldMarkedLocal_sum` near `t = 0`.

With `evTerm_FFmarked_replacement_localB` (`LocalClassDensityMarks.lean`) every marked term of the
right-hand side is the marked term recomputed on `𝔹_{k+1}(Y⁺)`.
-/

@[expose] public section

namespace Balaban.Fluctuation

open MeasureTheory Balaban Balaban.Localization Balaban.Multiscale
  Balaban.Background Balaban.SmallField Balaban.SmallField.Def6 Balaban.SmallField.Def6v2
  Balaban.SmallField.GsSpec Balaban.Analysis Balaban.Polymer Finset Matrix

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ ϱ₁ ϱm : ℝ}

section LabelExpansion

variable {Gp : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
  {Gk : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ₁}
  {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}
  {a₁ ν c BG κ r₀ eps δ₃ : ℝ} {X₀ X₁f : Finset (CTorus d L N₁ m₁ (k + 1))}
  {Kc Cx c₂ BG₂ δ₁ δfl : ℝ} {X 𝒦X : Set (CTorus d L N₁ m₁ (k + 1))}

open Classical in
/-- **One inherited energy label expands over the decoupled domains along the masked tangent, with
a localized ambient set** (the ambient set `Gk` and the fluctuation set `Hm` at their own separation
indices).  There are maps `F₁` (the decoupled background of `Gp`), `Sol` (the decoupled fluctuation
solution of `Hm`) and `Fk` (the background of `Gk`), with their specifications, such that for every
pair of marks `(um, tm)` of the radius set `(‖um‖ + ‖tm‖) √N ‖cc‖ K c_ψ < δ₁`, every datum `D` of
the chart and every hat variable `ψ̂` of the box, and every mask `Zm` of unit points, `flComp` of
`Eτ = β⁻¹ ℰ^{(j)}(y, X; ·)` at the masked tangent `markedTangDec … Zm um tm D ψ̂` is `∑_{Y ∈ polymerDomains(X₁)} evTerm … (FFmarked … Zm um tm) Y`
at `(rawOf D, ψ̂)`, and every term is analytic in the marks on the radius set. -/
theorem classOldMarkedLocal_sum {b : ℝ} (hb₁ : 1 ≤ b) (hbC : b ≤ scaledC0 d) {P : Consts}
    {Dom : FieldDom d L N₁ m₁ (k + 1) N ϱ}
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
      Dom.dom j (C.Tm.gs j X) r.1 r.2) :
    ∃ (F₁ : DecParams Gp × RawData d L (N₁ * L ^ m₁) (k + 1) N →
        (Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ))
      (Sol : Dec2.DecParams (coverOf Gp) × Edat Hm N → (Hm.Ω 1 × Fin N → ℂ) × (Hm.Ω 1 → ℂ))
      (Fk : RawData d L (N₁ * L ^ m₁) (k + 1) N → (Gk.Ω 1 × Fin N → ℂ) × (Gk.Ω 1 → ℂ)),
      (∀ (s : Dec2.DecParams (coverOf Gp)) (D : BgData Gp N), (∀ P, ‖s P‖ < Real.exp κ) →
        InUnionDomainC Gp (bgC0 d L N) (c7 d L N BG κ) ν D → ∀ (φ : Gp.Ω 1 × Fin N → ℂ)
          (α : Gp.Ω 1 → ℂ), Dec2.IsDecBg (coverOf Gp) Gp (compWeight L a₁) ν (rho4 d L N BG κ)
            s D φ α → F₁ (s, rawOf D) = (φ, α)) ∧
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
      ∀ Zm : Finset (unitPts Gp),
      (∀ um tm : ℂ, (‖um‖ + ‖tm‖) *
        (Real.sqrt N * (‖cc‖ * (covSupConstC d L N (compWeight L a₁ k) κ * cψ))) < δ₁ →
        ∀ D : BgData Gp N, XiCData Gp (compWeight L a₁) ν (k + 1) 1 eps D →
        ∀ ψh : unitPts Gp × Fin N → ℂ, (∀ p, ‖ψh p‖ ≤ cψ) →
        flComp hB hF (fun r => (β : ℂ)⁻¹ * C.Tm.E j y X r.1 r.2)
          (rawOf D, markedTangDec hG' cc a₁ ν Zm um tm D ψh) =
        ∑ Y ∈ polymerDomains (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) => i.1.1)
          Gp C.m₀ (X1 Gp C.m₀ j 𝒦X), evTerm
            (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) => i.1.1) Gp C.m₀
            (X1 Gp C.m₀ j 𝒦X) (FFmarked X₁f a₁ ν hG' cc F₁ Sol
              (eTermFun Gp Gk (C.Tm.gs j X) Hm (compWeight L a₁) Fk
                (fun r => (β : ℂ)⁻¹ * C.Tm.E j y X r.1 r.2)) Zm um tm) Y (rawOf D, ψh)) ∧
      (∀ Y, ∀ u ∈ XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
          {ψh : unitPts Gp × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ},
        AnalyticOnNhd ℂ (fun w : ℂ × ℂ =>
          evTerm (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) => i.1.1) Gp C.m₀
            (X1 Gp C.m₀ j 𝒦X) (FFmarked X₁f a₁ ν hG' cc F₁ Sol
              (eTermFun Gp Gk (C.Tm.gs j X) Hm (compWeight L a₁) Fk
                (fun r => (β : ℂ)⁻¹ * C.Tm.E j y X r.1 r.2)) Zm w.1 w.2) Y u)
          {w : ℂ × ℂ | (‖w.1‖ + ‖w.2‖) *
            (Real.sqrt N * (‖cc‖ * (covSupConstC d L N (compWeight L a₁ k) κ * cψ))) < δ₁}) := by
  classical
  have hC := flCore_of hB hF
  obtain ⟨hEan, hEbd⟩ := classOldDecEnergy_chart_radius (N := N) C hm hcl hβ hκP hE₀ a₁ ν δ₃ eps
    δfl hj1 hjk hXp hy hchart
  have hEb : 0 ≤ β⁻¹ * P.E₀ := mul_nonneg (inv_nonneg.2 hβ.le) hE₀
  obtain ⟨Fk, hFkan, hFk⟩ := theorem72_analytic (G := Gk) (a := compWeight L a₁) (ν := ν) hB.HBk
  have hd0 : 0 < d := by have := hC.HBp.hd; omega
  have hB2 : 0 ≤ 2 * (K4 d L N BG κ * (xiC1 d * eps)) :=
    mul_nonneg (by norm_num) (mul_nonneg (K4_pos hC.hS.fam.2.1 hd0).le
      (by have := one_le_xiC1 d; have := hC.eps_pos; positivity))
  obtain ⟨F₁, hF₁an, hF₁⟩ := i4b_analytic hC.hS hC.Sp hC.HBp hC.hκ.le hC.hM
  obtain ⟨Sol, hSolan, hSolprop⟩ := Dec2.i4a_analytic (N := N) hC.hS2.fam hC.hS2.an
    hC.SM.toCoverBase hC.hκ.le hC.hM2 false hB2 hC.δ₁_pos.le hC.B_le hC.δ₁_le
  refine ⟨F₁, Sol, Fk, fun s D hs hDd φ α hI => hF₁ s D hs hDd φ α
    ((dec2_isDecBg_iff Gp _ ν _ s D φ α).1 hI), hSolprop, fun Zm => ?_⟩
  obtain ⟨e1, -, -, -, -, e6, -, -, -⟩ := i5_functional_hat_marked_exposed_pair_of hC hk hG
    hG' cc hcψ Zm hMX hdm hα hsm hcov hX₁ hopt hκ₀ hκdec hκ h1 hlog hEb
    (Φ := eTermFun Gp Gk (C.Tm.gs j X) Hm (compWeight L a₁) Fk
      (fun r => (β : ℂ)⁻¹ * C.Tm.E j y X r.1 r.2))
    (R := FlRealLC Gp Hm a₁ ν BG κ eps X₁f BG₂ δ₁)
    (eTermFun_analytic_of_one_le hb₁ hbC hB hF hFkan hFk hEan)
    (fun t ht a b s F₁' D ψh h => ⟨ht, h ▸ isLayerConstant_markedHatPsiF hG hG' cc F₁' Zm a b _ _ _⟩)
    (fun t ht => eTermFun_bound_of_one_le hb₁ hbC hB hF hFk hEbd ht)
    hconn hrow (Z := ↑X₁f) (Zα := ∅) subset_rfl (fun x hx => absurd hx (Set.notMem_empty x))
    (fun t _ t' _ hφ _ hδ hag hψ => eTermFun_local_dir hB hF hcov hX₁ Fk _ hφ hδ hag hψ)
    hF₁an hF₁ hSolan hSolprop
  refine ⟨fun um tm hw D hD ψh hψh => ?_, e6⟩
  rw [← e1 um tm hw D hD ψh hψh]
  exact (eTermFun_value hB hF hFk _ hD
    (markedTangDec_mem_flBallLC hC hk hG hG' cc hcψ Zm hMX hdm hα hsm hw hD hψh)).symm

end LabelExpansion

section JointMarks

namespace StepSetting.JointRep

variable {S : StepSetting d L N₁ m₁ k N ϱ} {eps pp : ℝ} (Jr : S.JointRep eps pp)

/-- The substitution `ψ' = β_k^{-1/2} M ψ̂` is additive in `ψ̂`. -/
theorem _root_.Balaban.Fluctuation.StepSetting.hatField_add
    (M : Matrix (S.U × Fin N) (S.U × Fin N) ℂ) (u v : S.EC) :
    S.hatField M (u + v) = S.hatField M u + S.hatField M v := by
  unfold StepSetting.hatField
  rw [Matrix.mulVec_add, smul_add]

/-- **The joint representative along the masked direction is the composed pair of the free
datum.**  At a datum `D` of the chart, for `s ψ̂ + t v_z` in the box of the joint representative
(`v_z = C^{-1/2} 1_{B(z)} C^{1/2} ψ̂`), `Jr.PJ j (rawOf D, s ψ̂ + t v_z)` is the composed pair of the
old datum `H.dataUCH (ψ^{(k)} + s ψ' + t 1_{B(z)} ψ')`, `ψ' = β_k^{-1/2} C^{1/2} ψ̂`
(`JointRep.PJ_dataUCH`, `hatField_inv_mask_of_chart`). -/
theorem PJ_masked_eq_dataUCH {c BG κ Kc Cx c₂ BG₂ δ₁ : ℝ}
    (hC : FlCore N S.G' (stepG d L N₁ m₁ k ϱ) S.a₁ S.ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δc : ℝ}
    (hdm : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    {D : BgData S.G' N} (hD : XiCData S.G' S.a S.ν (k + 1) 1 eps D)
    (z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1)))) (x : S.E) (s t : ℂ)
    (hw : ∀ p, ‖(s • yhat x + t • ((Jr.Mx (rawOf D))⁻¹ *ᵥ
        S.maskUC z (Jr.Mx (rawOf D) *ᵥ yhat x))) p‖ ≤ pp) (j : ℕ) :
    Jr.PJ j (rawOf D, s • yhat x + t • ((Jr.Mx (rawOf D))⁻¹ *ᵥ
        S.maskUC z (Jr.Mx (rawOf D) *ᵥ yhat x))) =
      composedPairAtC S.a S.ν (Nat.le_succ k) j ((S.withDatumH D).dataUCH ((fun q =>
        (composeData (S.hG.precedes S.hG' (le_refl (k + 1))) S.a
          (bgFieldC S.G' S.a S.ν (bgC0 d L N) D) D).Ψ
            (unitRep (G' := S.G') q.1) q.2) +
        (s • S.hatField (hatCovSqrt S.G' S.a₁ S.ν D) (yhat x) +
          t • S.maskUC z (S.hatField (hatCovSqrt S.G' S.a₁ S.ν D) (yhat x))))) := by
  have hm : S.hatField (Jr.Mx (rawOf D))
      ((Jr.Mx (rawOf D))⁻¹ *ᵥ S.maskUC z (Jr.Mx (rawOf D) *ᵥ yhat x)) =
      S.maskUC z (S.hatField (Jr.Mx (rawOf D)) (yhat x)) :=
    Jr.hatField_inv_mask_of_chart (S.withDatumH D) hC hMX hdm hα hsm hD z x
  have hv : S.hatField (hatCovSqrt S.G' S.a₁ S.ν D) (s • yhat x + t • ((Jr.Mx (rawOf D))⁻¹ *ᵥ
      S.maskUC z (Jr.Mx (rawOf D) *ᵥ yhat x))) =
      s • S.hatField (hatCovSqrt S.G' S.a₁ S.ν D) (yhat x) +
        t • S.maskUC z (S.hatField (hatCovSqrt S.G' S.a₁ S.ν D) (yhat x)) := by
    rw [S.hatField_add, S.hatField_smul', S.hatField_smul', ← Jr.Mx_eq D hD, hm]
  rw [← hv]
  exact Jr.PJ_dataUCH (S.withDatumH D) hD hw j

/-- **The label term along the masked direction is `β flComp` at the masked tangent** (the
endpoint identity in the form of the joint representative, at every chart datum): with a
localized ambient set, for `s ψ̂ + t v_z` in the box of `Jr` and `(s, t)` in the radius set of the
marks, `ℰ^{(j)}(y, X; Jr.PJ j (rawOf D, s ψ̂ + t v_z)) = β flComp Eτ (rawOf D, markedTangDec …
(blockU z) s t D ψ̂)`. -/
theorem classLabel_PJ_masked_eq_flComp {P : Consts} {Dom : FieldDom d L N₁ m₁ (k + 1) N ϱ}
    (C : StepClass d L N₁ m₁ k N ϱ) (hcl : SFTermClauses P Dom C.Tm)
    {j : ℕ} (hj1 : 1 ≤ j) (hjk : j ≤ k)
    {y : CTorus d L N₁ m₁ (k + 1)} {X : Set (CTorus d L N₁ m₁ (k + 1))}
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
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4) (hβ : 0 < S.β)
    {D : BgData S.G' N} (hD : XiCData S.G' S.a S.ν (k + 1) 1 eps D)
    (z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1)))) (x : S.E) (hx : ∀ p, ‖yhat x p‖ ≤ cψ)
    (s t : ℂ)
    (hw : ∀ p, ‖(s • yhat x + t • ((Jr.Mx (rawOf D))⁻¹ *ᵥ
        S.maskUC z (Jr.Mx (rawOf D) *ᵥ yhat x))) p‖ ≤ pp)
    (hst : (‖s‖ + ‖t‖) * (Real.sqrt N * (‖((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)‖ *
        (covSupConstC d L N (compWeight L S.a₁ k) κ * cψ))) < δ₁) :
    C.Tm.E j y X
        (Jr.PJ j (rawOf D, s • yhat x + t • ((Jr.Mx (rawOf D))⁻¹ *ᵥ
          S.maskUC z (Jr.Mx (rawOf D) *ᵥ yhat x)))).1
        (Jr.PJ j (rawOf D, s • yhat x + t • ((Jr.Mx (rawOf D))⁻¹ *ᵥ
          S.maskUC z (Jr.Mx (rawOf D) *ᵥ yhat x)))).2 =
      (S.β : ℂ) * flComp hB hF (fun r => (S.β : ℂ)⁻¹ * C.Tm.E j y X r.1 r.2)
        (rawOf D, markedTangDec S.hG' ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) S.a₁ S.ν
          (S.blockU z) s t D (yhat x)) := by
  have hC := flCore_of hB hF
  have hβ0 : (S.β : ℂ) ≠ 0 := by exact_mod_cast hβ.ne'
  have hball := markedTangDec_mem_flBallLC hC S.hk1 S.hG S.hG'
    ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) hcψ (S.blockU z) hMX hdm hα hsm hst hD hx
  rw [S.markedTangDec_eq_liftC_raw D z s t x] at hball ⊢
  have hend := (S.withDatumH D).classOldEndpointLocalH_liftC hcl hj1 hjk (y := y) hS hB hF hD
    hc7 hR hsmR hRs hsmall hnum hnum' _ hball.1
  rw [Jr.PJ_masked_eq_dataUCH hC hMX hdm hα hsm hD z x s t hw j]
  change _ = (S.β : ℂ) * flComp hB hF (fun r => (S.β : ℂ)⁻¹ * C.Tm.E j y X r.1 r.2)
    (rawOf (S.withDatumH D).D', _)
  rw [hend, ← mul_assoc, mul_inv_cancel₀ hβ0, one_mul]
  rfl

open Classical in
/-- **Core of `deriv_classLabel_PJ_eq_sum_marked`, for given maps.**  For maps `(F₁, Sol, Fk)` whose
expansion of the label along the masked tangent of every root `z` has the sum identity and the
analyticity in the marks of `classOldMarkedLocal_sum` (`hexp`), the mark identity of the label holds
at every datum of the chart: the derivative at `0` of
`t ↦ ℰ^{(j)}(y, X; Jr.PJ j (rawOf D, s ψ̂ + t v_z))` is
`β ∑_Y ∂_t|₀ evTerm … (FFmarked … (blockU z) s t) Y (rawOf D, ψ̂)`, and this function of `t` is
differentiable at `0` (it agrees near `0` with `β` times the sum of the marked terms). -/
theorem deriv_classLabel_PJ_eq_sum_marked_of {P : Consts} {Dom : FieldDom d L N₁ m₁ (k + 1) N ϱ}
    (C : StepClass d L N₁ m₁ k N ϱ) (hcl : SFTermClauses P Dom C.Tm)
    {j : ℕ} (hj1 : 1 ≤ j) (hjk : j ≤ k)
    {y : CTorus d L N₁ m₁ (k + 1)} {X : Set (CTorus d L N₁ m₁ (k + 1))}
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
    {𝒦X : Set (CTorus d L N₁ m₁ (k + 1))} (hβ : 0 < S.β)
    {F₁ : DecParams S.G' × RawData d L (N₁ * L ^ m₁) (k + 1) N →
        (S.G'.Ω 1 × Fin N → ℂ) × (S.G'.Ω 1 → ℂ)}
    {Sol : Dec2.DecParams (coverOf S.G') × Edat (stepG d L N₁ m₁ k ϱ) N →
        ((stepG d L N₁ m₁ k ϱ).Ω 1 × Fin N → ℂ) × ((stepG d L N₁ m₁ k ϱ).Ω 1 → ℂ)}
    {Fk : RawData d L (N₁ * L ^ m₁) (k + 1) N → (Gk.Ω 1 × Fin N → ℂ) × (Gk.Ω 1 → ℂ)}
    (hexp : ∀ z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))),
      (∀ um tm : ℂ, (‖um‖ + ‖tm‖) *
        (Real.sqrt N * (‖((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)‖ *
          (covSupConstC d L N (compWeight L S.a₁ k) κ * cψ))) < δ₁ →
        ∀ D : BgData S.G' N, XiCData S.G' (compWeight L S.a₁) S.ν (k + 1) 1 eps D →
        ∀ ψh : unitPts S.G' × Fin N → ℂ, (∀ p, ‖ψh p‖ ≤ cψ) →
        flComp hB hF (fun r => (S.β : ℂ)⁻¹ * C.Tm.E j y X r.1 r.2)
          (rawOf D, markedTangDec S.hG' ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) S.a₁ S.ν
            (S.blockU z) um tm D ψh) =
        ∑ Y ∈ polymerDomains
          (fun i : ParIdx S.G' (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) => i.1.1)
          S.G' C.m₀ (X1 S.G' C.m₀ j 𝒦X), evTerm
            (fun i : ParIdx S.G' (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) => i.1.1) S.G' C.m₀
            (X1 S.G' C.m₀ j 𝒦X) (FFmarked X₁f S.a₁ S.ν S.hG'
              ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) F₁ Sol
              (eTermFun S.G' Gk (C.Tm.gs j X) (stepG d L N₁ m₁ k ϱ) (compWeight L S.a₁) Fk
                (fun r => (S.β : ℂ)⁻¹ * C.Tm.E j y X r.1 r.2)) (S.blockU z) um tm) Y
            (rawOf D, ψh)) ∧
      (∀ Y, ∀ u ∈ XiCRaw S.G' (compWeight L S.a₁) S.ν (k + 1) 1 eps ×ˢ
          {ψh : unitPts S.G' × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ},
        AnalyticOnNhd ℂ (fun w : ℂ × ℂ =>
          evTerm (fun i : ParIdx S.G' (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) => i.1.1) S.G'
            C.m₀ (X1 S.G' C.m₀ j 𝒦X) (FFmarked X₁f S.a₁ S.ν S.hG'
              ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) F₁ Sol
              (eTermFun S.G' Gk (C.Tm.gs j X) (stepG d L N₁ m₁ k ϱ) (compWeight L S.a₁) Fk
                (fun r => (S.β : ℂ)⁻¹ * C.Tm.E j y X r.1 r.2)) (S.blockU z) w.1 w.2) Y u)
          {w : ℂ × ℂ | (‖w.1‖ + ‖w.2‖) *
            (Real.sqrt N * (‖((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)‖ *
              (covSupConstC d L N (compWeight L S.a₁ k) κ * cψ))) < δ₁})) :
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
  intro D hD z x hx s hs hsr
  obtain ⟨hsum, han⟩ := hexp z
  have hu : ((rawOf D, yhat x) : RawData d L (N₁ * L ^ m₁) (k + 1) N × S.EC) ∈
      XiCRaw S.G' (compWeight L S.a₁) S.ν (k + 1) 1 eps ×ˢ
        {ψh : unitPts S.G' × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ} := ⟨⟨D, hD, rfl⟩, hx⟩
  have hU : ∀ᶠ t : ℂ in nhds 0,
      (∀ p, ‖(s • yhat x + t • ((Jr.Mx (rawOf D))⁻¹ *ᵥ
        S.maskUC z (Jr.Mx (rawOf D) *ᵥ yhat x))) p‖ < pp) ∧
      (‖s‖ + ‖t‖) * (Real.sqrt N * (‖((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)‖ *
        (covSupConstC d L N (compWeight L S.a₁ k) κ * cψ))) < δ₁ := by
    refine Filter.Eventually.and (Filter.eventually_all.2 fun p => ?_) ?_
    · have hc : Continuous fun t : ℂ => ‖(s • yhat x + t • ((Jr.Mx (rawOf D))⁻¹ *ᵥ
          S.maskUC z (Jr.Mx (rawOf D) *ᵥ yhat x))) p‖ := by fun_prop
      exact hc.continuousAt.eventually_lt continuousAt_const (by simpa using hs p)
    · have hc : Continuous fun t : ℂ => (‖s‖ + ‖t‖) *
          (Real.sqrt N * (‖((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)‖ *
            (covSupConstC d L N (compWeight L S.a₁ k) κ * cψ))) := by fun_prop
      exact hc.continuousAt.eventually_lt continuousAt_const (by simpa using hsr)
  have hβ0 : (S.β : ℂ) ≠ 0 := by exact_mod_cast hβ.ne'
  have h0 : (s, (0 : ℂ)) ∈ {w : ℂ × ℂ | (‖w.1‖ + ‖w.2‖) *
      (Real.sqrt N * (‖((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)‖ *
        (covSupConstC d L N (compWeight L S.a₁ k) κ * cψ))) < δ₁} := by
    show (‖s‖ + ‖(0 : ℂ)‖) * _ < δ₁
    rw [norm_zero, add_zero]
    exact hsr
  have han' := fun Y => differentiableAt_mark_slice (han Y (rawOf D, yhat x) hu (s, 0) h0)
  set Ev : Set (CTorus d L N₁ m₁ (k + 1)) → ℂ → ℂ := fun Y t => evTerm
      (fun i : ParIdx S.G' (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) => i.1.1) S.G' C.m₀
      (X1 S.G' C.m₀ j 𝒦X) (FFmarked X₁f S.a₁ S.ν S.hG'
        ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) F₁ Sol
        (eTermFun S.G' Gk (C.Tm.gs j X) (stepG d L N₁ m₁ k ϱ) (compWeight L S.a₁) Fk
          (fun r => (S.β : ℂ)⁻¹ * C.Tm.E j y X r.1 r.2)) (S.blockU z) s t) Y
      (rawOf D, yhat x) with hEv
  set Etil : ℂ → ℂ := fun t => C.Tm.E j y X
      (Jr.PJ j (rawOf D, s • yhat x + t • ((Jr.Mx (rawOf D))⁻¹ *ᵥ
        S.maskUC z (Jr.Mx (rawOf D) *ᵥ yhat x)))).1
      (Jr.PJ j (rawOf D, s • yhat x + t • ((Jr.Mx (rawOf D))⁻¹ *ᵥ
        S.maskUC z (Jr.Mx (rawOf D) *ᵥ yhat x)))).2 with hEtil
  have hsum' : ∀ t ∈ {t : ℂ | (∀ p, ‖(s • yhat x + t • ((Jr.Mx (rawOf D))⁻¹ *ᵥ
        S.maskUC z (Jr.Mx (rawOf D) *ᵥ yhat x))) p‖ < pp) ∧
      (‖s‖ + ‖t‖) * (Real.sqrt N * (‖((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)‖ *
        (covSupConstC d L N (compWeight L S.a₁ k) κ * cψ))) < δ₁},
      flComp hB hF (fun r => (S.β : ℂ)⁻¹ * C.Tm.E j y X r.1 r.2)
        (rawOf D, markedTangDec S.hG' ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) S.a₁ S.ν
          (S.blockU z) s t D (yhat x)) =
        ∑ Y ∈ polymerDomains (fun i : ParIdx S.G' (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) => i.1.1)
          S.G' C.m₀ (X1 S.G' C.m₀ j 𝒦X), Ev Y t := fun t ht => by
    exact hsum s t ht.2 D hD (yhat x) hx
  have hend : ∀ t ∈ {t : ℂ | (∀ p, ‖(s • yhat x + t • ((Jr.Mx (rawOf D))⁻¹ *ᵥ
        S.maskUC z (Jr.Mx (rawOf D) *ᵥ yhat x))) p‖ < pp) ∧
      (‖s‖ + ‖t‖) * (Real.sqrt N * (‖((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)‖ *
        (covSupConstC d L N (compWeight L S.a₁ k) κ * cψ))) < δ₁},
      flComp hB hF (fun r => (S.β : ℂ)⁻¹ * C.Tm.E j y X r.1 r.2)
        (rawOf D, markedTangDec S.hG' ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) S.a₁ S.ν
          (S.blockU z) s t D (yhat x)) = (S.β : ℂ)⁻¹ * Etil t := fun t ht => by
    rw [hEtil]
    beta_reduce
    rw [Jr.classLabel_PJ_masked_eq_flComp C hcl hj1 hjk (y := y) hS hB hF hc7 hR hsmR hRs
      hsmall hnum hnum' hcψ hMX hdm hα hsm hβ hD z x hx s t (fun p => (ht.1 p).le) ht.2,
      ← mul_assoc, inv_mul_cancel₀ hβ0, one_mul]
  refine ⟨deriv_eq_sum_of_expansion _ Ev _ Etil (S.β : ℂ) hβ0 hU hsum' hend
    (fun Y _ => han' Y), ?_⟩
  have hev : Etil =ᶠ[nhds (0 : ℂ)] fun t => (S.β : ℂ) * ∑ Y ∈ polymerDomains
      (fun i : ParIdx S.G' (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) => i.1.1)
      S.G' C.m₀ (X1 S.G' C.m₀ j 𝒦X), Ev Y t := by
    filter_upwards [hU] with t ht
    rw [← hsum' t ht, hend t ht, ← mul_assoc, mul_inv_cancel₀ hβ0, one_mul]
  exact ((DifferentiableAt.fun_sum fun Y _ => han' Y).const_mul _).congr_of_eventuallyEq hev

open Classical in
/-- **The mark identity of an inherited label at every datum of the chart** (any external field),
with a localized ambient set `Gk`.  There are maps `(F₁, Sol, Fk)` (those of
`classOldMarkedLocal_sum`) such that for every datum `D` of the chart, every root `z`, every `x` with
`|ψ̂(x)| ≤ c_ψ` and every first mark `s` with `s ψ̂` strictly inside the box of the joint
representative and `‖s‖` in the radius of the marks, the derivative at `0` of the label term along
the masked direction `v_z = C^{-1/2} 1_{B(z)} C^{1/2} ψ̂`,
`t ↦ ℰ^{(j)}(y, X; Jr.PJ j (rawOf D, s ψ̂ + t v_z))`, is
`β ∑_Y ∂_t|₀ evTerm … (FFmarked … (blockU z) s t) Y (rawOf D, ψ̂)`, the sum over the decoupled domains
of the `t`-derivatives of the marked terms. -/
theorem deriv_classLabel_PJ_eq_sum_marked {b : ℝ} (hb₁ : 1 ≤ b) (hbC : b ≤ scaledC0 d)
    {P : Consts} {Dom : FieldDom d L N₁ m₁ (k + 1) N ϱ}
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
    (hβ : 0 < S.β) :
    ∃ (F₁ : DecParams S.G' × RawData d L (N₁ * L ^ m₁) (k + 1) N →
        (S.G'.Ω 1 × Fin N → ℂ) × (S.G'.Ω 1 → ℂ))
      (Sol : Dec2.DecParams (coverOf S.G') × Edat (stepG d L N₁ m₁ k ϱ) N →
        ((stepG d L N₁ m₁ k ϱ).Ω 1 × Fin N → ℂ) × ((stepG d L N₁ m₁ k ϱ).Ω 1 → ℂ))
      (Fk : RawData d L (N₁ * L ^ m₁) (k + 1) N → (Gk.Ω 1 × Fin N → ℂ) × (Gk.Ω 1 → ℂ)),
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
              (rawOf D, yhat x)) 0 := by
  obtain ⟨F₁, Sol, Fk, -, -, hexp⟩ := classOldMarkedLocal_sum hb₁ hbC C hm hcl hβ hE₀ hj1 hjk
    hXp hy hB hF S.hk1 S.hG S.hG' ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) hcψ hMX hdm hα hsm hcov
    hX₁ hconn hrow hopt hκ₀ hκdec hκ h1 hlog hκP hchart
  exact ⟨F₁, Sol, Fk, fun D hD z x hx s hs hsr =>
    (Jr.deriv_classLabel_PJ_eq_sum_marked_of C hcl hj1 hjk hS hB hF hc7 hR hsmR hRs hsmall hnum
      hnum' hcψ hMX hdm hα hsm hβ (fun z => hexp (S.blockU z)) D hD z x hx s hs hsr).1⟩

end StepSetting.JointRep

end JointMarks

end Balaban.Fluctuation
