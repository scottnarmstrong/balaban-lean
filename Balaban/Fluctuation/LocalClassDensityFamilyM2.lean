/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.LocalClassDensityFamilyLocal

/-!
# The input (M2) of the general class, assembled (`LocalClassDensityFamilyM2`)

`StepSetting.JointRep.classMarks_M2_of_family`: for a class `C` whose inherited labels (`𝒯E`)
carry their settings and given maps, the marks family `G₁` of `LocalClassDensityFamilyMarks`
(rooted pairs of `markedIdx`, formula `hG₁`), with any common label system
`commonLabels Lab … reads₀ dom₀ …` and labels `y1` of the rooted pairs whose sites are the bridge
labels (`hy1`; e.g. `Lab` the root-union labels of the class domains, `rootUnionLabels`, with
`polyDom_isDj_one`), satisfies every hypothesis (M2) of `e0CoeffFamily_class_fromTower` in its
form: measurability, block locality on the label, the bound `F1 q e^{-κ_G 𝗱(y1 q)}` (with `F1 q` the
bound of `classMarksFamily_fields` times `e^{κ_G 𝗱(y1 q)}`, so no decay in the label size is
claimed), analyticity in `(θ, u)` on `physV × {‖u‖ < a}`, continuity on the carrier, holomorphy in
`u`, locality in the parameter, the root cube in every label, and the identity
`Dℰ_k(rawOf D, s ψ̂)[v_z] = ∑_q G₁ (rawOf D, 0) q s (restr x)` `ν_{p₁}`-almost surely
(under the analyticity `hE` of the old densities along the path, the hypothesis of
`e0CoeffFamily_class_fromTower`).

The per-label settings (`hB`, `hF`, `hcov`, `hX₁`, `hopt`, `hS`, `hchart` and the numerical
conditions) are hypotheses; at the tower they are the per-label settings of the brief
(`bgSetting_localGk`, the D2(b) mass response for `hchart`).  The activity family (M1) is not
constructed.
-/

@[expose] public section

namespace Balaban.Fluctuation

open MeasureTheory Balaban Balaban.Localization Balaban.Multiscale
  Balaban.Background Balaban.SmallField Balaban.SmallField.Def6 Balaban.SmallField.Def6v2
  Balaban.SmallField.GsSpec Balaban.Analysis Balaban.Polymer Finset Matrix

namespace StepSetting.JointRep

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ ϱ₁ ϱ₂ : ℝ}
variable {S : StepSetting d L N₁ m₁ k N ϱ} {eps pp : ℝ} (Jr : S.JointRep eps pp)
  {c BG κ r₀ δ₃ Kc Cx c₂ BG₂ δ₁ δfl : ℝ}

open Classical in
/-- **The marks family (M2) of a class with an explicit constant.**  See the module doc-string. -/
theorem classMarks_M2_of_family_gen_onSet_pad {ι : Type*} [Fintype ι]
    (C : StepClass d L N₁ m₁ k N ϱ) {b : ℝ} (hb₁ : 1 ≤ b) (hbC : b ≤ scaledC0 d)
    {m₀ : ℕ} (Eτ : ι → RawData d L (N₁ * L ^ m₁) (k + 1) N → ℂ) (Bτ : ι → ℝ)
    (hBτ : ∀ τ, 0 ≤ Bτ τ) (hβ : 0 < S.β)
    (jL : ι → ℕ) (XL : ι → Set (CTorus d L N₁ m₁ (k + 1)))
    (hj1 : ∀ τ, 1 ≤ jL τ) (hjk : ∀ τ, jL τ ≤ k)
    (Gk : ι → GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ₁)
    (Gj : ι → GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ)
    (hlocE : ∀ τ Ψ Ψ' h h', (∀ x ∈ XL τ, Ψ x = Ψ' x ∧ h x = h' x) →
      Eτ τ (Ψ, h) = Eτ τ (Ψ', h'))
    (X₀ X₁f : ι → Finset (CTorus d L N₁ m₁ (k + 1))) (𝒦X : ι → Set (CTorus d L N₁ m₁ (k + 1)))
    (hB : ∀ τ, BgSetting N S.G' (Gk τ) (Gj τ) S.a₁ S.ν c BG κ r₀ eps δ₃ (X₀ τ)
      (X₁f τ) (jL τ))
    (hF : ∀ τ, FlSetting N S.G' (Gk τ) (stepG d L N₁ m₁ k ϱ) S.a₁ S.ν κ BG eps δ₃ Kc Cx c₂ BG₂
      δ₁ δfl (X₁f τ))
    {cψ : ℝ} (hcψ : 0 ≤ cψ)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δc : ℝ}
    (hdm : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    (hcov : ∀ τ, CovSetup S.G' m₀ (jL τ) (XL τ) (𝒦X τ))
    (hX₁ : ∀ τ, (↑(X₁f τ) : Set (CTorus d L N₁ m₁ (k + 1))) = X1 S.G' m₀ (jL τ) (𝒦X τ))
    (hconn : HatConn S.G')
    (hrow : RowInHat (coverOf S.G') (stepG d L N₁ m₁ k ϱ) (compWeight L S.a₁) S.ν)
    (hopt : ∀ τ, ∃ (W₀ : Finset (CTorus d L N₁ m₁ (k + 1)))
      (E₀ : Finset (CTorus d L N₁ m₁ (k + 1) × CTorus d L N₁ m₁ (k + 1))),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ XL τ) ∧ MeetsOne m₀ (jL τ) (𝒦X τ) W₀ ∧
        bondCost (scaleW L m₀ m₁ (jL τ)) E₀ = treeLenCovOne m₀ (jL τ) (XL τ))
    {κdec κ₀ : ℝ} (hκ₀ : 0 ≤ κ₀) (hκdec : 3 * κ₀ + 3 ≤ κdec)
    (hκ : 4 * d * (((2 * L + 1) ^ d : ℕ) : ℝ) * κdec ≤ κ) (h1 : 1 ≤ (κ / 2 - 1) / 2)
    (hlog : Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) * (((L ^ m₀) ^ d : ℕ) : ℝ)) ≤ (κ / 2 - 1) / 2)
    {𝒮 : ι → Set (RawData d L (N₁ * L ^ m₁) (k + 1) N)}
    (hEan : ∀ τ, AnalyticOnNhd ℂ (Eτ τ) (𝒮 τ))
    (hEbd : ∀ τ, ∀ r ∈ 𝒮 τ,
      ‖Eτ τ r‖ ≤ Bτ τ * Real.exp (-(κdec - 1) * treeLenCovOne m₀ (jL τ) (XL τ)))
    (F₁ : ι → DecParams S.G' × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      (S.G'.Ω 1 × Fin N → ℂ) × (S.G'.Ω 1 → ℂ))
    (hF₁an : ∀ τ, AnalyticOnNhd ℂ (F₁ τ) {q | (∀ P, ‖q.1 P‖ < Real.exp κ) ∧
      ∃ D : BgData S.G' N, InUnionDomainC S.G' (bgC0 d L N) (c7 d L N BG κ) S.ν D ∧
        q.2 = (D.Ψ, D.h)})
    (hF₁ : ∀ τ, ∀ (s : DecParams S.G') (D : BgData S.G' N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC S.G' (bgC0 d L N) (c7 d L N BG κ) S.ν D → ∀ (φ : S.G'.Ω 1 × Fin N → ℂ)
        (α : S.G'.Ω 1 → ℂ), IsDecBg S.G' (compWeight L S.a₁) S.ν (rho4 d L N BG κ) s D φ α →
        F₁ τ (s, rawOf D) = (φ, α))
    (Sol : ι → Dec2.DecParams (coverOf S.G') × Edat (stepG d L N₁ m₁ k ϱ) N → ((stepG d L N₁ m₁ k
        ϱ).Ω 1 × Fin N → ℂ) × ((stepG d L N₁ m₁ k ϱ).Ω 1 → ℂ))
    (hSolan : ∀ τ, AnalyticOnNhd ℂ (Sol τ) {p | (∀ P, ‖p.1 P‖ < Real.exp κ) ∧
      StrictDataM (stepG d L N₁ m₁ k ϱ) N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2})
    (hSolprop : ∀ τ, ∀ p : Dec2.DecParams (coverOf S.G') × Edat (stepG d L N₁ m₁ k ϱ) N,
      (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM (stepG d L N₁ m₁ k ϱ) N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2 →
        (Sol τ p).1 = dphi (stepG d L N₁ m₁ k ϱ) (Dec2.decG (coverOf S.G') (stepG d L N₁ m₁ k ϱ)
            (compWeight L S.a₁) S.ν p.1) p.2.2.1
          p.2.1 (pertSource (stepG d L N₁ m₁ k ϱ) (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) (Sol τ
              p).2 ∧
        Dec2.DecFixed (coverOf S.G') (stepG d L N₁ m₁ k ϱ) (compWeight L S.a₁) S.ν p.1 false
            p.2.2.1 p.2.1
          (pertSource (stepG d L N₁ m₁ k ϱ) (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) (Sol τ p).2 ∧
        Small (stepG d L N₁ m₁ k ϱ) (Sol τ p).2 (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
        Small (stepG d L N₁ m₁ k ϱ) (Sol τ p).2 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        SupBounds (stepG d L N₁ m₁ k ϱ) (Sol τ p).1 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        (∀ δα' : (stepG d L N₁ m₁ k ϱ).Ω 1 → ℂ, Small (stepG d L N₁ m₁ k ϱ) δα' (c6' d L N
            (famConst d L BG₂ κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf S.G') (stepG d L N₁ m₁ k ϱ) (compWeight L S.a₁) S.ν p.1 false
              p.2.2.1 p.2.1
            (pertSource (stepG d L N₁ m₁ k ϱ) (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) δα' → δα' =
                (Sol τ p).2))
    (Fk : ∀ τ, RawData d L (N₁ * L ^ m₁) (k + 1) N →
      ((Gk τ).Ω 1 × Fin N → ℂ) × ((Gk τ).Ω 1 → ℂ))
    (hFkan : ∀ τ, AnalyticOnNhd ℂ (Fk τ) {p | ∃ D : BgData (Gk τ) N,
      InUnionDomainC (Gk τ) (bgC0 d L N) (bgC1 d L N) S.ν D ∧ p = (D.Ψ, D.h)})
    (hFk : ∀ τ, ∀ D : BgData (Gk τ) N, InUnionDomainC (Gk τ) (bgC0 d L N) (bgC1 d L N) S.ν D →
      Fk τ (rawOf D) = (bgFieldC (Gk τ) (compWeight L S.a₁) S.ν (bgC0 d L N) D,
        bgMultC (Gk τ) (compWeight L S.a₁) S.ν (bgC0 d L N) D))
    (hS : ∀ τ, GsSpecStrong (jL τ) ((hjk τ).trans (Nat.le_succ k)) (XL τ)
      (Gj τ))
    (hc7 : c7 d L N BG κ ≤ thm73C3 d L N) {R : ℝ} (hR : 2 ≤ R)
    (hsmR : 2 * (compC4 d * (bgK1 d L N * (xiC1 d * eps))) + 5 * (R * δ₁) ≤ bgC1 d L N)
    (hRs : R * δ₁ ≤ deltaStar d L N) (hsmall : cK2 d L N * (R * δ₁) < bgC0 d L N / 2)
    (hnum : cK2 d L N * δ₁ ≤ c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8))
    (hnum' : cK2' d L N (famConst d L BG₂ κ) * δ₁ ≤
      c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8))
    (hN : L ^ m₀ ∣ N₁) (hm1 : 1 ≤ m₀) (hd : 3 ≤ d) (hL : 2 ≤ L)
    (z : RootIdx d L N₁ m₁ (k + 1)) {ρ : ℝ} (hρ : 0 < ρ) (hρc : ρ ≤ cψ) (hρpp : ρ < pp)
    (hp : 0 < S.p₁) {a bb : ℝ} (ha1 : 1 < a) (hbb : 0 < bb)
    (hab : (a + bb) * markedRad d L N k S.a₁ κ cψ ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) < δ₁)
    (G₁ : physParam N S →
      {q // q ∈ markedIdx (fun _ => (Set.univ : Set (CTorus d L N₁ m₁ (k + 1))))
        (fun τ => polyDom S.G' (X₁f τ) m₀ (jL τ) (𝒦X τ)) z} →
      ℂ → (∀ b, (S.blockSplit 1 hp).Ωb b) → ℂ)
    (hG₁ : ∀ θ q u Φ, G₁ θ q u Φ =
      if (θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) ∈
          XiCRaw S.G' (compWeight L S.a₁) S.ν (k + 1) 1 eps ∧ ‖u‖ < a then
        (S.β : ℂ) * deriv (fun t : ℂ => evDec (X₁f q.1.1) m₀ (jL q.1.1) (𝒦X q.1.1) S.a₁ S.ν
          S.hG' ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) (F₁ q.1.1) (Sol q.1.1)
          (eTermFun S.G' (Gk q.1.1) (Gj q.1.1) (stepG d L N₁ m₁ k ϱ)
            (compWeight L S.a₁) (Fk q.1.1)
            (fun r => (S.β : ℂ)⁻¹ * Eτ q.1.1 r))
          (S.blockU z) u t q.1.2
          ((θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N), S.hatOf 1 ρ hp Φ)) 0
      else 0)
    (hEJ : ∀ D : BgData S.G' N, XiCData S.G' S.a S.ν (k + 1) 1 eps D → ∀ w : S.EC,
      Jr.EJ C (rawOf D, w) = ∑ τ, Eτ τ (Jr.PJ (jL τ) (rawOf D, w)))
    (hρp : S.p₁ ≤ ρ)
    (hE : ∀ D : BgData S.G' N, XiCData S.G' S.a S.ν (k + 1) 1 eps D →
      ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ x : S.E, ‖x‖ ≤ S.p₁ → ∀ j ∈ Finset.Icc 1 k,
      AnalyticAt ℂ
        (fun p : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N => Edens C.m₀ C.Tm j p.1 p.2)
        (Jr.PJ j (rawOf D, (s : ℂ) • yhat x)))
    {Lb : Type*} (Lab : CubeLabels (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) 1 (k + 1)
      Set.univ Lb)
    {β₀ : Type*} [Fintype β₀] (reads₀ : β₀ → Set (CTorus d L N₁ m₁ (k + 1)))
    (dom₀ : β₀ → Finset (Set (CTorus d L N₁ m₁ (k + 1))))
    (hN1 : L ^ 1 ∣ N₁) (hdom₀ : ∀ b, ∀ Y ∈ dom₀ b, IsDj 1 (k + 1) Y)
    (y1 : {q // q ∈ markedIdx (fun _ => (Set.univ : Set (CTorus d L N₁ m₁ (k + 1))))
        (fun τ => polyDom S.G' (X₁f τ) m₀ (jL τ) (𝒦X τ)) z} → Lb ⊕ RootUnionLb 1 reads₀ dom₀)
    (hy1 : ∀ q, (commonLabels Lab hN1 hL reads₀ dom₀ hdom₀).ysite (y1 q) = bridge 1 z q.1.2)
    (κG : ℝ)
    (h𝒮 : ∀ τ, ∀ t ∈ FlRealLC S.G' (stepG d L N₁ m₁ k ϱ) S.a₁ S.ν BG κ eps (X₁f τ) BG₂ δ₁,
      D2raw (Gk τ) (Gj τ) (compWeight L S.a₁) (Fk τ)
        (d1Triple S.G' (Gk τ) (stepG d L N₁ m₁ k ϱ) (compWeight L S.a₁) t.1.1 t.2.1 t.2.2) ∈ 𝒮 τ)
    (pad : {q // q ∈ markedIdx (fun _ => (Set.univ : Set (CTorus d L N₁ m₁ (k + 1))))
        (fun τ => polyDom S.G' (X₁f τ) m₀ (jL τ) (𝒦X τ)) z} → ℝ) (hpad : ∀ q, 0 < pad q) :
    ∃ F1 : {q // q ∈ markedIdx (fun _ => (Set.univ : Set (CTorus d L N₁ m₁ (k + 1))))
        (fun τ => polyDom S.G' (X₁f τ) m₀ (jL τ) (𝒦X τ)) z} → ℝ,
    (∀ q, F1 q = (‖(S.β : ℂ)‖ * ((S.β⁻¹ * Bτ q.1.1) * Real.exp (-κ₀ *
      treeLenCovOne m₀ (jL q.1.1) (XL q.1.1) - 2 * κdec * treeLenCov S.G' m₀ q.1.2) / bb) +
      pad q) * Real.exp (κG * (commonLabels Lab hN1 hL reads₀ dom₀ hdom₀).dl (y1 q))) ∧
    (∀ q, 0 < F1 q) ∧
    -- measurability
    (∀ θ q u, Measurable (G₁ θ q u)) ∧
    -- block locality on the label of the mark
    (∀ θ q u, DepOn (blocksOf 1 (k + 1) Set.univ
      ((commonLabels Lab hN1 hL reads₀ dom₀ hdom₀).ysite (y1 q))) (G₁ θ q u)) ∧
    -- the bound
    (∀ θ q u Φ, ‖G₁ θ q u Φ‖ ≤ F1 q * Real.exp (-κG *
      (commonLabels Lab hN1 hL reads₀ dom₀ hdom₀).dl (y1 q))) ∧
    -- analyticity in the parameter and the first mark
    (∀ q, ∀ Φ ∈ physCarrier S 1 hp, AnalyticOnNhd ℂ (fun r : physParam N S × ℂ => G₁ r.1 q r.2 Φ)
      (physV S S.a₁ S.ν eps ×ˢ Metric.ball (0 : ℂ) a)) ∧
    -- continuity on the carrier
    (∀ q, ∀ θ ∈ physV S S.a₁ S.ν eps, ∀ u ∈ Metric.ball (0 : ℂ) a,
      ContinuousOn (G₁ θ q u) (physCarrier S 1 hp)) ∧
    -- holomorphy in the first mark
    (∀ θ ∈ physV S S.a₁ S.ν eps, ∀ q Φ,
      DifferentiableOn ℂ (fun u => G₁ θ q u Φ) (Metric.ball (0 : ℂ) a)) ∧
    -- locality in the parameter
    (∀ A : Set (CTorus d L N₁ m₁ (k + 1)), ∀ θ ∈ physV S S.a₁ S.ν eps,
      ∀ θ' ∈ physV S S.a₁ S.ν eps,
      physRestrict (N := N) A (physIncl N S θ) = physRestrict A (physIncl N S θ') →
      ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ q,
        (commonLabels Lab hN1 hL reads₀ dom₀ hdom₀).ysite (y1 q) ⊆ Yhat Set.univ A →
        G₁ θ q (s : ℂ) = G₁ θ' q (s : ℂ)) ∧
    -- the root cube in every label
    (∀ q, rootCube (m₀ := 1) z ∈ blocksOf 1 (k + 1) Set.univ
      ((commonLabels Lab hN1 hL reads₀ dom₀ hdom₀).ysite (y1 q))) ∧
    -- the identity of the marks
    (∀ D : BgData S.G' N, XiCData S.G' S.a S.ν (k + 1) 1 eps D →
      ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ᵐ x ∂S.nuFl,
        (fderiv ℂ (fun w : S.EC => Jr.EJ C (rawOf D, w)) ((s : ℂ) • yhat x))
            ((Jr.Mx (rawOf D))⁻¹ *ᵥ S.maskUC z (Jr.Mx (rawOf D) *ᵥ yhat x)) =
          ∑ q, G₁ ((⟨rawOf D, rawOf_mem_rawSub _⟩ : rawSub N S.G'),
            (0 : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ)) q (s : ℂ)
            ((S.blockSplit 1 hp).restr x))     := by
  classical
  have ha : 0 ≤ a := (zero_lt_one.trans ha1).le
  -- the fields, the locality and the identity of the marks family
  obtain ⟨hmeas, hdep, hbd, hhol, hcont, hdiff, hroot⟩ := classMarksFamily_fields_gen_onSet (h𝒮 := h𝒮)
      S hb₁ hbC Eτ
    Bτ hBτ hβ jL XL Gk Gj X₀ X₁f 𝒦X hB hF S.hG ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) hcψ hMX hdm
    hα hsm hcov hX₁ hconn hrow hopt hκ₀ hκdec hκ h1 hlog hEan hEbd F₁ hF₁an hF₁ Sol hSolan
    hSolprop Fk hFkan hFk hN hm1 hd hL z hρ hρc hp ha hbb hab G₁ (fun θ q u Φ => by rw [hG₁])
  have hloc := classMarksFamily_local_gen S Eτ jL XL Gk Gj X₀ X₁f 𝒦X hB hF S.hG
    ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) hcψ hMX hdm hα hsm hcov hX₁ hconn hrow F₁ hF₁ Sol
    hSolprop Fk z hρ hρc hp ha1 hbb hab G₁ (fun θ q u Φ => by rw [hG₁])
  have hae := Jr.classMarksFamily_ae_fderiv_eq_sum_gen_onSet (h𝒮 := h𝒮)
      C hb₁ hbC Eτ Bτ hBτ hβ jL XL hj1 hjk Gk Gj
    hlocE X₀ X₁f 𝒦X hB hF hcψ hMX hdm hα hsm hcov hX₁ hconn hrow hopt hκ₀ hκdec hκ h1 hlog hEan
    hEbd F₁ hF₁an hF₁ Sol hSolan hSolprop Fk hFkan hFk hS hc7 hR hsmR hRs hsmall hnum hnum' hN hm1
    hd hL z hρ hρc hρpp hp ha1 hbb hab G₁ hG₁ hEJ hρp hE
  -- the constants of the bound
  set M : {q // q ∈ markedIdx (fun _ => (Set.univ : Set (CTorus d L N₁ m₁ (k + 1))))
      (fun τ => polyDom S.G' (X₁f τ) m₀ (jL τ) (𝒦X τ)) z} → ℝ := fun q =>
    ‖(S.β : ℂ)‖ * ((S.β⁻¹ * Bτ q.1.1) * Real.exp (-κ₀ * treeLenCovOne m₀ (jL q.1.1) (XL q.1.1) -
      2 * κdec * treeLenCov S.G' m₀ q.1.2) / bb) with hMdef
  have hM0 : ∀ q, 0 ≤ M q := fun q => mul_nonneg (norm_nonneg _) (div_nonneg (mul_nonneg
    (mul_nonneg (inv_nonneg.2 hβ.le) (hBτ q.1.1)) (Real.exp_pos _).le) hbb.le)
  refine ⟨fun q => (M q + pad q) *
      Real.exp (κG * (commonLabels Lab hN1 hL reads₀ dom₀ hdom₀).dl (y1 q)),
    fun q => rfl, fun q => mul_pos (by linarith [hM0 q, hpad q]) (Real.exp_pos _), hmeas,
    fun θ q u => ?_,
    fun θ q u Φ => ?_, fun q Φ _ => hhol q Φ,
    fun q θ hθ u hu => (hcont q θ hθ u hu).continuousOn, hdiff,
    fun A θ hθ θ' hθ' hres s hs q hsub =>
      hloc A θ hθ θ' hθ' hres s hs q (by rw [← hy1 q]; exact hsub),
    fun q => ?_, hae⟩
  · rw [hy1 q]; exact hdep θ q u
  · calc ‖G₁ θ q u Φ‖ ≤ M q := hbd θ q u Φ
      _ ≤ M q + pad q := le_add_of_nonneg_right (hpad q).le
      _ = (M q + pad q) * Real.exp (κG * (commonLabels Lab hN1 hL reads₀ dom₀ hdom₀).dl (y1 q)) *
          Real.exp (-κG * (commonLabels Lab hN1 hL reads₀ dom₀ hdom₀).dl (y1 q)) := by
        rw [mul_assoc, ← Real.exp_add, neg_mul, add_neg_cancel, Real.exp_zero, mul_one]
  · rw [hy1 q]; exact (hroot q).2

open Classical in
/-- **The marks family (M2) of a class, with the label charts replaced by any sets containing the
composed step data** (`h𝒮`).  `classMarks_M2_of_family_gen` is the case of the label charts. -/
theorem classMarks_M2_of_family_gen_onSet {ι : Type*} [Fintype ι]
    (C : StepClass d L N₁ m₁ k N ϱ) {b : ℝ} (hb₁ : 1 ≤ b) (hbC : b ≤ scaledC0 d)
    {m₀ : ℕ} (Eτ : ι → RawData d L (N₁ * L ^ m₁) (k + 1) N → ℂ) (Bτ : ι → ℝ)
    (hBτ : ∀ τ, 0 ≤ Bτ τ) (hβ : 0 < S.β)
    (jL : ι → ℕ) (XL : ι → Set (CTorus d L N₁ m₁ (k + 1)))
    (hj1 : ∀ τ, 1 ≤ jL τ) (hjk : ∀ τ, jL τ ≤ k)
    (Gk : ι → GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ₁)
    (Gj : ι → GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ)
    (hlocE : ∀ τ Ψ Ψ' h h', (∀ x ∈ XL τ, Ψ x = Ψ' x ∧ h x = h' x) →
      Eτ τ (Ψ, h) = Eτ τ (Ψ', h'))
    (X₀ X₁f : ι → Finset (CTorus d L N₁ m₁ (k + 1))) (𝒦X : ι → Set (CTorus d L N₁ m₁ (k + 1)))
    (hB : ∀ τ, BgSetting N S.G' (Gk τ) (Gj τ) S.a₁ S.ν c BG κ r₀ eps δ₃ (X₀ τ)
      (X₁f τ) (jL τ))
    (hF : ∀ τ, FlSetting N S.G' (Gk τ) (stepG d L N₁ m₁ k ϱ) S.a₁ S.ν κ BG eps δ₃ Kc Cx c₂ BG₂
      δ₁ δfl (X₁f τ))
    {cψ : ℝ} (hcψ : 0 ≤ cψ)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δc : ℝ}
    (hdm : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    (hcov : ∀ τ, CovSetup S.G' m₀ (jL τ) (XL τ) (𝒦X τ))
    (hX₁ : ∀ τ, (↑(X₁f τ) : Set (CTorus d L N₁ m₁ (k + 1))) = X1 S.G' m₀ (jL τ) (𝒦X τ))
    (hconn : HatConn S.G')
    (hrow : RowInHat (coverOf S.G') (stepG d L N₁ m₁ k ϱ) (compWeight L S.a₁) S.ν)
    (hopt : ∀ τ, ∃ (W₀ : Finset (CTorus d L N₁ m₁ (k + 1)))
      (E₀ : Finset (CTorus d L N₁ m₁ (k + 1) × CTorus d L N₁ m₁ (k + 1))),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ XL τ) ∧ MeetsOne m₀ (jL τ) (𝒦X τ) W₀ ∧
        bondCost (scaleW L m₀ m₁ (jL τ)) E₀ = treeLenCovOne m₀ (jL τ) (XL τ))
    {κdec κ₀ : ℝ} (hκ₀ : 0 ≤ κ₀) (hκdec : 3 * κ₀ + 3 ≤ κdec)
    (hκ : 4 * d * (((2 * L + 1) ^ d : ℕ) : ℝ) * κdec ≤ κ) (h1 : 1 ≤ (κ / 2 - 1) / 2)
    (hlog : Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) * (((L ^ m₀) ^ d : ℕ) : ℝ)) ≤ (κ / 2 - 1) / 2)
    {𝒮 : ι → Set (RawData d L (N₁ * L ^ m₁) (k + 1) N)}
    (hEan : ∀ τ, AnalyticOnNhd ℂ (Eτ τ) (𝒮 τ))
    (hEbd : ∀ τ, ∀ r ∈ 𝒮 τ,
      ‖Eτ τ r‖ ≤ Bτ τ * Real.exp (-(κdec - 1) * treeLenCovOne m₀ (jL τ) (XL τ)))
    (F₁ : ι → DecParams S.G' × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      (S.G'.Ω 1 × Fin N → ℂ) × (S.G'.Ω 1 → ℂ))
    (hF₁an : ∀ τ, AnalyticOnNhd ℂ (F₁ τ) {q | (∀ P, ‖q.1 P‖ < Real.exp κ) ∧
      ∃ D : BgData S.G' N, InUnionDomainC S.G' (bgC0 d L N) (c7 d L N BG κ) S.ν D ∧
        q.2 = (D.Ψ, D.h)})
    (hF₁ : ∀ τ, ∀ (s : DecParams S.G') (D : BgData S.G' N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC S.G' (bgC0 d L N) (c7 d L N BG κ) S.ν D → ∀ (φ : S.G'.Ω 1 × Fin N → ℂ)
        (α : S.G'.Ω 1 → ℂ), IsDecBg S.G' (compWeight L S.a₁) S.ν (rho4 d L N BG κ) s D φ α →
        F₁ τ (s, rawOf D) = (φ, α))
    (Sol : ι → Dec2.DecParams (coverOf S.G') × Edat (stepG d L N₁ m₁ k ϱ) N → ((stepG d L N₁ m₁ k
        ϱ).Ω 1 × Fin N → ℂ) × ((stepG d L N₁ m₁ k ϱ).Ω 1 → ℂ))
    (hSolan : ∀ τ, AnalyticOnNhd ℂ (Sol τ) {p | (∀ P, ‖p.1 P‖ < Real.exp κ) ∧
      StrictDataM (stepG d L N₁ m₁ k ϱ) N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2})
    (hSolprop : ∀ τ, ∀ p : Dec2.DecParams (coverOf S.G') × Edat (stepG d L N₁ m₁ k ϱ) N,
      (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM (stepG d L N₁ m₁ k ϱ) N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2 →
        (Sol τ p).1 = dphi (stepG d L N₁ m₁ k ϱ) (Dec2.decG (coverOf S.G') (stepG d L N₁ m₁ k ϱ)
            (compWeight L S.a₁) S.ν p.1) p.2.2.1
          p.2.1 (pertSource (stepG d L N₁ m₁ k ϱ) (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) (Sol τ
              p).2 ∧
        Dec2.DecFixed (coverOf S.G') (stepG d L N₁ m₁ k ϱ) (compWeight L S.a₁) S.ν p.1 false
            p.2.2.1 p.2.1
          (pertSource (stepG d L N₁ m₁ k ϱ) (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) (Sol τ p).2 ∧
        Small (stepG d L N₁ m₁ k ϱ) (Sol τ p).2 (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
        Small (stepG d L N₁ m₁ k ϱ) (Sol τ p).2 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        SupBounds (stepG d L N₁ m₁ k ϱ) (Sol τ p).1 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        (∀ δα' : (stepG d L N₁ m₁ k ϱ).Ω 1 → ℂ, Small (stepG d L N₁ m₁ k ϱ) δα' (c6' d L N
            (famConst d L BG₂ κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf S.G') (stepG d L N₁ m₁ k ϱ) (compWeight L S.a₁) S.ν p.1 false
              p.2.2.1 p.2.1
            (pertSource (stepG d L N₁ m₁ k ϱ) (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) δα' → δα' =
                (Sol τ p).2))
    (Fk : ∀ τ, RawData d L (N₁ * L ^ m₁) (k + 1) N →
      ((Gk τ).Ω 1 × Fin N → ℂ) × ((Gk τ).Ω 1 → ℂ))
    (hFkan : ∀ τ, AnalyticOnNhd ℂ (Fk τ) {p | ∃ D : BgData (Gk τ) N,
      InUnionDomainC (Gk τ) (bgC0 d L N) (bgC1 d L N) S.ν D ∧ p = (D.Ψ, D.h)})
    (hFk : ∀ τ, ∀ D : BgData (Gk τ) N, InUnionDomainC (Gk τ) (bgC0 d L N) (bgC1 d L N) S.ν D →
      Fk τ (rawOf D) = (bgFieldC (Gk τ) (compWeight L S.a₁) S.ν (bgC0 d L N) D,
        bgMultC (Gk τ) (compWeight L S.a₁) S.ν (bgC0 d L N) D))
    (hS : ∀ τ, GsSpecStrong (jL τ) ((hjk τ).trans (Nat.le_succ k)) (XL τ)
      (Gj τ))
    (hc7 : c7 d L N BG κ ≤ thm73C3 d L N) {R : ℝ} (hR : 2 ≤ R)
    (hsmR : 2 * (compC4 d * (bgK1 d L N * (xiC1 d * eps))) + 5 * (R * δ₁) ≤ bgC1 d L N)
    (hRs : R * δ₁ ≤ deltaStar d L N) (hsmall : cK2 d L N * (R * δ₁) < bgC0 d L N / 2)
    (hnum : cK2 d L N * δ₁ ≤ c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8))
    (hnum' : cK2' d L N (famConst d L BG₂ κ) * δ₁ ≤
      c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8))
    (hN : L ^ m₀ ∣ N₁) (hm1 : 1 ≤ m₀) (hd : 3 ≤ d) (hL : 2 ≤ L)
    (z : RootIdx d L N₁ m₁ (k + 1)) {ρ : ℝ} (hρ : 0 < ρ) (hρc : ρ ≤ cψ) (hρpp : ρ < pp)
    (hp : 0 < S.p₁) {a bb : ℝ} (ha1 : 1 < a) (hbb : 0 < bb)
    (hab : (a + bb) * markedRad d L N k S.a₁ κ cψ ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) < δ₁)
    (G₁ : physParam N S →
      {q // q ∈ markedIdx (fun _ => (Set.univ : Set (CTorus d L N₁ m₁ (k + 1))))
        (fun τ => polyDom S.G' (X₁f τ) m₀ (jL τ) (𝒦X τ)) z} →
      ℂ → (∀ b, (S.blockSplit 1 hp).Ωb b) → ℂ)
    (hG₁ : ∀ θ q u Φ, G₁ θ q u Φ =
      if (θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) ∈
          XiCRaw S.G' (compWeight L S.a₁) S.ν (k + 1) 1 eps ∧ ‖u‖ < a then
        (S.β : ℂ) * deriv (fun t : ℂ => evDec (X₁f q.1.1) m₀ (jL q.1.1) (𝒦X q.1.1) S.a₁ S.ν
          S.hG' ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) (F₁ q.1.1) (Sol q.1.1)
          (eTermFun S.G' (Gk q.1.1) (Gj q.1.1) (stepG d L N₁ m₁ k ϱ)
            (compWeight L S.a₁) (Fk q.1.1)
            (fun r => (S.β : ℂ)⁻¹ * Eτ q.1.1 r))
          (S.blockU z) u t q.1.2
          ((θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N), S.hatOf 1 ρ hp Φ)) 0
      else 0)
    (hEJ : ∀ D : BgData S.G' N, XiCData S.G' S.a S.ν (k + 1) 1 eps D → ∀ w : S.EC,
      Jr.EJ C (rawOf D, w) = ∑ τ, Eτ τ (Jr.PJ (jL τ) (rawOf D, w)))
    (hρp : S.p₁ ≤ ρ)
    (hE : ∀ D : BgData S.G' N, XiCData S.G' S.a S.ν (k + 1) 1 eps D →
      ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ x : S.E, ‖x‖ ≤ S.p₁ → ∀ j ∈ Finset.Icc 1 k,
      AnalyticAt ℂ
        (fun p : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N => Edens C.m₀ C.Tm j p.1 p.2)
        (Jr.PJ j (rawOf D, (s : ℂ) • yhat x)))
    {Lb : Type*} (Lab : CubeLabels (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) 1 (k + 1)
      Set.univ Lb)
    {β₀ : Type*} [Fintype β₀] (reads₀ : β₀ → Set (CTorus d L N₁ m₁ (k + 1)))
    (dom₀ : β₀ → Finset (Set (CTorus d L N₁ m₁ (k + 1))))
    (hN1 : L ^ 1 ∣ N₁) (hdom₀ : ∀ b, ∀ Y ∈ dom₀ b, IsDj 1 (k + 1) Y)
    (y1 : {q // q ∈ markedIdx (fun _ => (Set.univ : Set (CTorus d L N₁ m₁ (k + 1))))
        (fun τ => polyDom S.G' (X₁f τ) m₀ (jL τ) (𝒦X τ)) z} → Lb ⊕ RootUnionLb 1 reads₀ dom₀)
    (hy1 : ∀ q, (commonLabels Lab hN1 hL reads₀ dom₀ hdom₀).ysite (y1 q) = bridge 1 z q.1.2)
    (κG : ℝ)
    (h𝒮 : ∀ τ, ∀ t ∈ FlRealLC S.G' (stepG d L N₁ m₁ k ϱ) S.a₁ S.ν BG κ eps (X₁f τ) BG₂ δ₁,
      D2raw (Gk τ) (Gj τ) (compWeight L S.a₁) (Fk τ)
        (d1Triple S.G' (Gk τ) (stepG d L N₁ m₁ k ϱ) (compWeight L S.a₁) t.1.1 t.2.1 t.2.2) ∈ 𝒮 τ) :
    ∃ F1 : {q // q ∈ markedIdx (fun _ => (Set.univ : Set (CTorus d L N₁ m₁ (k + 1))))
        (fun τ => polyDom S.G' (X₁f τ) m₀ (jL τ) (𝒦X τ)) z} → ℝ, (∀ q, 0 < F1 q) ∧
    -- measurability
    (∀ θ q u, Measurable (G₁ θ q u)) ∧
    -- block locality on the label of the mark
    (∀ θ q u, DepOn (blocksOf 1 (k + 1) Set.univ
      ((commonLabels Lab hN1 hL reads₀ dom₀ hdom₀).ysite (y1 q))) (G₁ θ q u)) ∧
    -- the bound
    (∀ θ q u Φ, ‖G₁ θ q u Φ‖ ≤ F1 q * Real.exp (-κG *
      (commonLabels Lab hN1 hL reads₀ dom₀ hdom₀).dl (y1 q))) ∧
    -- analyticity in the parameter and the first mark
    (∀ q, ∀ Φ ∈ physCarrier S 1 hp, AnalyticOnNhd ℂ (fun r : physParam N S × ℂ => G₁ r.1 q r.2 Φ)
      (physV S S.a₁ S.ν eps ×ˢ Metric.ball (0 : ℂ) a)) ∧
    -- continuity on the carrier
    (∀ q, ∀ θ ∈ physV S S.a₁ S.ν eps, ∀ u ∈ Metric.ball (0 : ℂ) a,
      ContinuousOn (G₁ θ q u) (physCarrier S 1 hp)) ∧
    -- holomorphy in the first mark
    (∀ θ ∈ physV S S.a₁ S.ν eps, ∀ q Φ,
      DifferentiableOn ℂ (fun u => G₁ θ q u Φ) (Metric.ball (0 : ℂ) a)) ∧
    -- locality in the parameter
    (∀ A : Set (CTorus d L N₁ m₁ (k + 1)), ∀ θ ∈ physV S S.a₁ S.ν eps,
      ∀ θ' ∈ physV S S.a₁ S.ν eps,
      physRestrict (N := N) A (physIncl N S θ) = physRestrict A (physIncl N S θ') →
      ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ q,
        (commonLabels Lab hN1 hL reads₀ dom₀ hdom₀).ysite (y1 q) ⊆ Yhat Set.univ A →
        G₁ θ q (s : ℂ) = G₁ θ' q (s : ℂ)) ∧
    -- the root cube in every label
    (∀ q, rootCube (m₀ := 1) z ∈ blocksOf 1 (k + 1) Set.univ
      ((commonLabels Lab hN1 hL reads₀ dom₀ hdom₀).ysite (y1 q))) ∧
    -- the identity of the marks
    (∀ D : BgData S.G' N, XiCData S.G' S.a S.ν (k + 1) 1 eps D →
      ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ᵐ x ∂S.nuFl,
        (fderiv ℂ (fun w : S.EC => Jr.EJ C (rawOf D, w)) ((s : ℂ) • yhat x))
            ((Jr.Mx (rawOf D))⁻¹ *ᵥ S.maskUC z (Jr.Mx (rawOf D) *ᵥ yhat x)) =
          ∑ q, G₁ ((⟨rawOf D, rawOf_mem_rawSub _⟩ : rawSub N S.G'),
            (0 : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ)) q (s : ℂ)
            ((S.blockSplit 1 hp).restr x))     := by
  obtain ⟨F1, -, hpos, hrest⟩ := Jr.classMarks_M2_of_family_gen_onSet_pad C hb₁ hbC Eτ Bτ hBτ hβ jL XL hj1 hjk Gk Gj hlocE X₀ X₁f 𝒦X hB hF hcψ hMX hdm hα hsm hcov hX₁ hconn hrow hopt hκ₀ hκdec hκ h1 hlog hEan hEbd F₁ hF₁an hF₁ Sol hSolan hSolprop Fk hFkan hFk hS hc7 hR hsmR hRs hsmall hnum hnum' hN hm1 hd hL z hρ hρc hρpp hp ha1 hbb hab G₁ hG₁ hEJ hρp hE Lab reads₀ dom₀ hN1 hdom₀ y1 hy1 κG h𝒮
    (fun _ => 1) (fun _ => one_pos)
  exact ⟨F1, hpos, hrest⟩

open Classical in
/-- The generic version of `classMarks_M2_of_family` (any label functionals `Eτ`). -/
theorem classMarks_M2_of_family_gen {ι : Type*} [Fintype ι]
    (C : StepClass d L N₁ m₁ k N ϱ) {b : ℝ} (hb₁ : 1 ≤ b) (hbC : b ≤ scaledC0 d)
    {m₀ : ℕ} (Eτ : ι → RawData d L (N₁ * L ^ m₁) (k + 1) N → ℂ) (Bτ : ι → ℝ)
    (hBτ : ∀ τ, 0 ≤ Bτ τ) (hβ : 0 < S.β)
    (jL : ι → ℕ) (XL : ι → Set (CTorus d L N₁ m₁ (k + 1)))
    (hj1 : ∀ τ, 1 ≤ jL τ) (hjk : ∀ τ, jL τ ≤ k)
    (Gk : ι → GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ₁)
    (Gj : ι → GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ)
    (hlocE : ∀ τ Ψ Ψ' h h', (∀ x ∈ XL τ, Ψ x = Ψ' x ∧ h x = h' x) →
      Eτ τ (Ψ, h) = Eτ τ (Ψ', h'))
    (X₀ X₁f : ι → Finset (CTorus d L N₁ m₁ (k + 1))) (𝒦X : ι → Set (CTorus d L N₁ m₁ (k + 1)))
    (hB : ∀ τ, BgSetting N S.G' (Gk τ) (Gj τ) S.a₁ S.ν c BG κ r₀ eps δ₃ (X₀ τ)
      (X₁f τ) (jL τ))
    (hF : ∀ τ, FlSetting N S.G' (Gk τ) (stepG d L N₁ m₁ k ϱ) S.a₁ S.ν κ BG eps δ₃ Kc Cx c₂ BG₂
      δ₁ δfl (X₁f τ))
    {cψ : ℝ} (hcψ : 0 ≤ cψ)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δc : ℝ}
    (hdm : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    (hcov : ∀ τ, CovSetup S.G' m₀ (jL τ) (XL τ) (𝒦X τ))
    (hX₁ : ∀ τ, (↑(X₁f τ) : Set (CTorus d L N₁ m₁ (k + 1))) = X1 S.G' m₀ (jL τ) (𝒦X τ))
    (hconn : HatConn S.G')
    (hrow : RowInHat (coverOf S.G') (stepG d L N₁ m₁ k ϱ) (compWeight L S.a₁) S.ν)
    (hopt : ∀ τ, ∃ (W₀ : Finset (CTorus d L N₁ m₁ (k + 1)))
      (E₀ : Finset (CTorus d L N₁ m₁ (k + 1) × CTorus d L N₁ m₁ (k + 1))),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ XL τ) ∧ MeetsOne m₀ (jL τ) (𝒦X τ) W₀ ∧
        bondCost (scaleW L m₀ m₁ (jL τ)) E₀ = treeLenCovOne m₀ (jL τ) (XL τ))
    {κdec κ₀ : ℝ} (hκ₀ : 0 ≤ κ₀) (hκdec : 3 * κ₀ + 3 ≤ κdec)
    (hκ : 4 * d * (((2 * L + 1) ^ d : ℕ) : ℝ) * κdec ≤ κ) (h1 : 1 ≤ (κ / 2 - 1) / 2)
    (hlog : Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) * (((L ^ m₀) ^ d : ℕ) : ℝ)) ≤ (κ / 2 - 1) / 2)
    (hEan : ∀ τ, AnalyticOnNhd ℂ (Eτ τ) (XiCRaw (Gj τ) (compWeight L S.a₁) S.ν (jL τ) b
      (b ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl)))
    (hEbd : ∀ τ, ∀ r ∈ XiCRaw (Gj τ) (compWeight L S.a₁) S.ν (jL τ) b
      (b ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl),
      ‖Eτ τ r‖ ≤ Bτ τ * Real.exp (-(κdec - 1) * treeLenCovOne m₀ (jL τ) (XL τ)))
    (F₁ : ι → DecParams S.G' × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      (S.G'.Ω 1 × Fin N → ℂ) × (S.G'.Ω 1 → ℂ))
    (hF₁an : ∀ τ, AnalyticOnNhd ℂ (F₁ τ) {q | (∀ P, ‖q.1 P‖ < Real.exp κ) ∧
      ∃ D : BgData S.G' N, InUnionDomainC S.G' (bgC0 d L N) (c7 d L N BG κ) S.ν D ∧
        q.2 = (D.Ψ, D.h)})
    (hF₁ : ∀ τ, ∀ (s : DecParams S.G') (D : BgData S.G' N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC S.G' (bgC0 d L N) (c7 d L N BG κ) S.ν D → ∀ (φ : S.G'.Ω 1 × Fin N → ℂ)
        (α : S.G'.Ω 1 → ℂ), IsDecBg S.G' (compWeight L S.a₁) S.ν (rho4 d L N BG κ) s D φ α →
        F₁ τ (s, rawOf D) = (φ, α))
    (Sol : ι → Dec2.DecParams (coverOf S.G') × Edat (stepG d L N₁ m₁ k ϱ) N → ((stepG d L N₁ m₁ k
        ϱ).Ω 1 × Fin N → ℂ) × ((stepG d L N₁ m₁ k ϱ).Ω 1 → ℂ))
    (hSolan : ∀ τ, AnalyticOnNhd ℂ (Sol τ) {p | (∀ P, ‖p.1 P‖ < Real.exp κ) ∧
      StrictDataM (stepG d L N₁ m₁ k ϱ) N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2})
    (hSolprop : ∀ τ, ∀ p : Dec2.DecParams (coverOf S.G') × Edat (stepG d L N₁ m₁ k ϱ) N,
      (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM (stepG d L N₁ m₁ k ϱ) N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2 →
        (Sol τ p).1 = dphi (stepG d L N₁ m₁ k ϱ) (Dec2.decG (coverOf S.G') (stepG d L N₁ m₁ k ϱ)
            (compWeight L S.a₁) S.ν p.1) p.2.2.1
          p.2.1 (pertSource (stepG d L N₁ m₁ k ϱ) (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) (Sol τ
              p).2 ∧
        Dec2.DecFixed (coverOf S.G') (stepG d L N₁ m₁ k ϱ) (compWeight L S.a₁) S.ν p.1 false
            p.2.2.1 p.2.1
          (pertSource (stepG d L N₁ m₁ k ϱ) (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) (Sol τ p).2 ∧
        Small (stepG d L N₁ m₁ k ϱ) (Sol τ p).2 (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
        Small (stepG d L N₁ m₁ k ϱ) (Sol τ p).2 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        SupBounds (stepG d L N₁ m₁ k ϱ) (Sol τ p).1 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        (∀ δα' : (stepG d L N₁ m₁ k ϱ).Ω 1 → ℂ, Small (stepG d L N₁ m₁ k ϱ) δα' (c6' d L N
            (famConst d L BG₂ κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf S.G') (stepG d L N₁ m₁ k ϱ) (compWeight L S.a₁) S.ν p.1 false
              p.2.2.1 p.2.1
            (pertSource (stepG d L N₁ m₁ k ϱ) (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) δα' → δα' =
                (Sol τ p).2))
    (Fk : ∀ τ, RawData d L (N₁ * L ^ m₁) (k + 1) N →
      ((Gk τ).Ω 1 × Fin N → ℂ) × ((Gk τ).Ω 1 → ℂ))
    (hFkan : ∀ τ, AnalyticOnNhd ℂ (Fk τ) {p | ∃ D : BgData (Gk τ) N,
      InUnionDomainC (Gk τ) (bgC0 d L N) (bgC1 d L N) S.ν D ∧ p = (D.Ψ, D.h)})
    (hFk : ∀ τ, ∀ D : BgData (Gk τ) N, InUnionDomainC (Gk τ) (bgC0 d L N) (bgC1 d L N) S.ν D →
      Fk τ (rawOf D) = (bgFieldC (Gk τ) (compWeight L S.a₁) S.ν (bgC0 d L N) D,
        bgMultC (Gk τ) (compWeight L S.a₁) S.ν (bgC0 d L N) D))
    (hS : ∀ τ, GsSpecStrong (jL τ) ((hjk τ).trans (Nat.le_succ k)) (XL τ)
      (Gj τ))
    (hc7 : c7 d L N BG κ ≤ thm73C3 d L N) {R : ℝ} (hR : 2 ≤ R)
    (hsmR : 2 * (compC4 d * (bgK1 d L N * (xiC1 d * eps))) + 5 * (R * δ₁) ≤ bgC1 d L N)
    (hRs : R * δ₁ ≤ deltaStar d L N) (hsmall : cK2 d L N * (R * δ₁) < bgC0 d L N / 2)
    (hnum : cK2 d L N * δ₁ ≤ c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8))
    (hnum' : cK2' d L N (famConst d L BG₂ κ) * δ₁ ≤
      c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8))
    (hN : L ^ m₀ ∣ N₁) (hm1 : 1 ≤ m₀) (hd : 3 ≤ d) (hL : 2 ≤ L)
    (z : RootIdx d L N₁ m₁ (k + 1)) {ρ : ℝ} (hρ : 0 < ρ) (hρc : ρ ≤ cψ) (hρpp : ρ < pp)
    (hp : 0 < S.p₁) {a bb : ℝ} (ha1 : 1 < a) (hbb : 0 < bb)
    (hab : (a + bb) * markedRad d L N k S.a₁ κ cψ ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) < δ₁)
    (G₁ : physParam N S →
      {q // q ∈ markedIdx (fun _ => (Set.univ : Set (CTorus d L N₁ m₁ (k + 1))))
        (fun τ => polyDom S.G' (X₁f τ) m₀ (jL τ) (𝒦X τ)) z} →
      ℂ → (∀ b, (S.blockSplit 1 hp).Ωb b) → ℂ)
    (hG₁ : ∀ θ q u Φ, G₁ θ q u Φ =
      if (θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) ∈
          XiCRaw S.G' (compWeight L S.a₁) S.ν (k + 1) 1 eps ∧ ‖u‖ < a then
        (S.β : ℂ) * deriv (fun t : ℂ => evDec (X₁f q.1.1) m₀ (jL q.1.1) (𝒦X q.1.1) S.a₁ S.ν
          S.hG' ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) (F₁ q.1.1) (Sol q.1.1)
          (eTermFun S.G' (Gk q.1.1) (Gj q.1.1) (stepG d L N₁ m₁ k ϱ)
            (compWeight L S.a₁) (Fk q.1.1)
            (fun r => (S.β : ℂ)⁻¹ * Eτ q.1.1 r))
          (S.blockU z) u t q.1.2
          ((θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N), S.hatOf 1 ρ hp Φ)) 0
      else 0)
    (hEJ : ∀ D : BgData S.G' N, XiCData S.G' S.a S.ν (k + 1) 1 eps D → ∀ w : S.EC,
      Jr.EJ C (rawOf D, w) = ∑ τ, Eτ τ (Jr.PJ (jL τ) (rawOf D, w)))
    (hρp : S.p₁ ≤ ρ)
    (hE : ∀ D : BgData S.G' N, XiCData S.G' S.a S.ν (k + 1) 1 eps D →
      ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ x : S.E, ‖x‖ ≤ S.p₁ → ∀ j ∈ Finset.Icc 1 k,
      AnalyticAt ℂ
        (fun p : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N => Edens C.m₀ C.Tm j p.1 p.2)
        (Jr.PJ j (rawOf D, (s : ℂ) • yhat x)))
    {Lb : Type*} (Lab : CubeLabels (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) 1 (k + 1)
      Set.univ Lb)
    {β₀ : Type*} [Fintype β₀] (reads₀ : β₀ → Set (CTorus d L N₁ m₁ (k + 1)))
    (dom₀ : β₀ → Finset (Set (CTorus d L N₁ m₁ (k + 1))))
    (hN1 : L ^ 1 ∣ N₁) (hdom₀ : ∀ b, ∀ Y ∈ dom₀ b, IsDj 1 (k + 1) Y)
    (y1 : {q // q ∈ markedIdx (fun _ => (Set.univ : Set (CTorus d L N₁ m₁ (k + 1))))
        (fun τ => polyDom S.G' (X₁f τ) m₀ (jL τ) (𝒦X τ)) z} → Lb ⊕ RootUnionLb 1 reads₀ dom₀)
    (hy1 : ∀ q, (commonLabels Lab hN1 hL reads₀ dom₀ hdom₀).ysite (y1 q) = bridge 1 z q.1.2)
    (κG : ℝ) :
    ∃ F1 : {q // q ∈ markedIdx (fun _ => (Set.univ : Set (CTorus d L N₁ m₁ (k + 1))))
        (fun τ => polyDom S.G' (X₁f τ) m₀ (jL τ) (𝒦X τ)) z} → ℝ, (∀ q, 0 < F1 q) ∧
    -- measurability
    (∀ θ q u, Measurable (G₁ θ q u)) ∧
    -- block locality on the label of the mark
    (∀ θ q u, DepOn (blocksOf 1 (k + 1) Set.univ
      ((commonLabels Lab hN1 hL reads₀ dom₀ hdom₀).ysite (y1 q))) (G₁ θ q u)) ∧
    -- the bound
    (∀ θ q u Φ, ‖G₁ θ q u Φ‖ ≤ F1 q * Real.exp (-κG *
      (commonLabels Lab hN1 hL reads₀ dom₀ hdom₀).dl (y1 q))) ∧
    -- analyticity in the parameter and the first mark
    (∀ q, ∀ Φ ∈ physCarrier S 1 hp, AnalyticOnNhd ℂ (fun r : physParam N S × ℂ => G₁ r.1 q r.2 Φ)
      (physV S S.a₁ S.ν eps ×ˢ Metric.ball (0 : ℂ) a)) ∧
    -- continuity on the carrier
    (∀ q, ∀ θ ∈ physV S S.a₁ S.ν eps, ∀ u ∈ Metric.ball (0 : ℂ) a,
      ContinuousOn (G₁ θ q u) (physCarrier S 1 hp)) ∧
    -- holomorphy in the first mark
    (∀ θ ∈ physV S S.a₁ S.ν eps, ∀ q Φ,
      DifferentiableOn ℂ (fun u => G₁ θ q u Φ) (Metric.ball (0 : ℂ) a)) ∧
    -- locality in the parameter
    (∀ A : Set (CTorus d L N₁ m₁ (k + 1)), ∀ θ ∈ physV S S.a₁ S.ν eps,
      ∀ θ' ∈ physV S S.a₁ S.ν eps,
      physRestrict (N := N) A (physIncl N S θ) = physRestrict A (physIncl N S θ') →
      ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ q,
        (commonLabels Lab hN1 hL reads₀ dom₀ hdom₀).ysite (y1 q) ⊆ Yhat Set.univ A →
        G₁ θ q (s : ℂ) = G₁ θ' q (s : ℂ)) ∧
    -- the root cube in every label
    (∀ q, rootCube (m₀ := 1) z ∈ blocksOf 1 (k + 1) Set.univ
      ((commonLabels Lab hN1 hL reads₀ dom₀ hdom₀).ysite (y1 q))) ∧
    -- the identity of the marks
    (∀ D : BgData S.G' N, XiCData S.G' S.a S.ν (k + 1) 1 eps D →
      ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ᵐ x ∂S.nuFl,
        (fderiv ℂ (fun w : S.EC => Jr.EJ C (rawOf D, w)) ((s : ℂ) • yhat x))
            ((Jr.Mx (rawOf D))⁻¹ *ᵥ S.maskUC z (Jr.Mx (rawOf D) *ᵥ yhat x)) =
          ∑ q, G₁ ((⟨rawOf D, rawOf_mem_rawSub _⟩ : rawSub N S.G'),
            (0 : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ)) q (s : ℂ)
            ((S.blockSplit 1 hp).restr x))     :=
  Jr.classMarks_M2_of_family_gen_onSet C hb₁ hbC Eτ Bτ hBτ hβ jL XL hj1 hjk Gk Gj hlocE X₀ X₁f 𝒦X hB
    hF hcψ hMX hdm hα hsm hcov hX₁ hconn hrow hopt hκ₀ hκdec hκ h1 hlog hEan hEbd F₁ hF₁an hF₁ Sol
    hSolan hSolprop Fk hFkan hFk hS hc7 hR hsmR hRs hsmall hnum hnum' hN hm1 hd hL z hρ hρc hρpp hp
    ha1 hbb hab G₁ hG₁ hEJ hρp hE Lab reads₀ dom₀ hN1 hdom₀ y1 hy1 κG
    (fun τ _ ht => d2raw_d1Triple_mem_xiCRaw hb₁ hbC (hB τ) (hF τ) (hFk τ) ht)


open Classical in
/-- **The input (M2) of a class with inherited labels.**  See the module doc-string: under the
hypotheses of `classMarksFamily_ae_fderiv_eq_sum`, for every common label system with labels `y1` of
the rooted pairs whose sites are the bridge labels, there is `F1 > 0` such that the marks `G₁`
satisfy the hypotheses (M2) of `e0CoeffFamily_class_fromTower` (measurability, block locality,
bound, analyticity, continuity, holomorphy in `u`, locality in the parameter, the root cube, the
identity almost surely). -/
theorem classMarks_M2_of_family {P : Consts} {Dom : FieldDom d L N₁ m₁ (k + 1) N ϱ}
    (C : StepClass d L N₁ m₁ k N ϱ)
    (𝒯E : Finset (ℕ × CTorus d L N₁ m₁ (k + 1) × Set (CTorus d L N₁ m₁ (k + 1))))
    (h𝒯 : 𝒯E = ((Finset.Icc 1 k) ×ˢ (Finset.univ : Finset (CTorus d L N₁ m₁ (k + 1) ×
        Set (CTorus d L N₁ m₁ (k + 1))))).filter
      (fun τ => Aligned (L ^ τ.1) τ.2.1 ∧ IsPolyDom C.m₀ τ.1 τ.2.2 ∧ τ.2.1 ∈ τ.2.2))
    {b : ℝ} (hb₁ : 1 ≤ b) (hbC : b ≤ scaledC0 d)
    (hm : P.m₀ = C.m₀) (hcl : SFTermClauses P Dom C.Tm)
    (hβ : 0 < S.β) (hE₀ : 0 ≤ P.E₀)
    (Gk : 𝒯E → GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ₁)
    (X₀ X₁f : 𝒯E → Finset (CTorus d L N₁ m₁ (k + 1))) (𝒦X : 𝒯E → Set (CTorus d L N₁ m₁ (k + 1)))
    (hB : ∀ τ : 𝒯E, BgSetting N S.G' (Gk τ) (C.Tm.gs τ.1.1 τ.1.2.2) S.a₁ S.ν c BG κ r₀ eps δ₃ (X₀ τ)
      (X₁f τ) τ.1.1)
    (hF : ∀ τ : 𝒯E, FlSetting N S.G' (Gk τ) (stepG d L N₁ m₁ k ϱ) S.a₁ S.ν κ BG eps δ₃ Kc Cx c₂ BG₂
      δ₁ δfl (X₁f τ))
    {cψ : ℝ} (hcψ : 0 ≤ cψ)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δc : ℝ}
    (hdm : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    (hcov : ∀ τ : 𝒯E, CovSetup S.G' C.m₀ τ.1.1 τ.1.2.2 (𝒦X τ))
    (hX₁ : ∀ τ : 𝒯E, (↑(X₁f τ) : Set (CTorus d L N₁ m₁ (k + 1))) = X1 S.G' C.m₀ τ.1.1 (𝒦X τ))
    (hconn : HatConn S.G')
    (hrow : RowInHat (coverOf S.G') (stepG d L N₁ m₁ k ϱ) (compWeight L S.a₁) S.ν)
    (hopt : ∀ τ : 𝒯E, ∃ (W₀ : Finset (CTorus d L N₁ m₁ (k + 1)))
      (E₀ : Finset (CTorus d L N₁ m₁ (k + 1) × CTorus d L N₁ m₁ (k + 1))),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ τ.1.2.2) ∧ MeetsOne C.m₀ τ.1.1 (𝒦X τ) W₀ ∧
        bondCost (scaleW L C.m₀ m₁ τ.1.1) E₀ = treeLenCovOne C.m₀ τ.1.1 τ.1.2.2)
    {κdec κ₀ : ℝ} (hκ₀ : 0 ≤ κ₀) (hκdec : 3 * κ₀ + 3 ≤ κdec)
    (hκ : 4 * d * (((2 * L + 1) ^ d : ℕ) : ℝ) * κdec ≤ κ) (h1 : 1 ≤ (κ / 2 - 1) / 2)
    (hlog : Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) * (((L ^ C.m₀) ^ d : ℕ) : ℝ)) ≤ (κ / 2 - 1) / 2)
    (hκP : κdec - 1 ≤ P.κ)
    (hchart : ∀ τ : 𝒯E, ∀ r ∈ XiCRaw (C.Tm.gs τ.1.1 τ.1.2.2) (compWeight L S.a₁) S.ν τ.1.1 b
      (b ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl),
      Dom.dom τ.1.1 (C.Tm.gs τ.1.1 τ.1.2.2) r.1 r.2)
    (F₁ : 𝒯E → DecParams S.G' × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      (S.G'.Ω 1 × Fin N → ℂ) × (S.G'.Ω 1 → ℂ))
    (hF₁an : ∀ τ : 𝒯E, AnalyticOnNhd ℂ (F₁ τ) {q | (∀ P, ‖q.1 P‖ < Real.exp κ) ∧
      ∃ D : BgData S.G' N, InUnionDomainC S.G' (bgC0 d L N) (c7 d L N BG κ) S.ν D ∧
        q.2 = (D.Ψ, D.h)})
    (hF₁ : ∀ τ : 𝒯E, ∀ (s : DecParams S.G') (D : BgData S.G' N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC S.G' (bgC0 d L N) (c7 d L N BG κ) S.ν D → ∀ (φ : S.G'.Ω 1 × Fin N → ℂ)
        (α : S.G'.Ω 1 → ℂ), IsDecBg S.G' (compWeight L S.a₁) S.ν (rho4 d L N BG κ) s D φ α →
        F₁ τ (s, rawOf D) = (φ, α))
    (Sol : 𝒯E → Dec2.DecParams (coverOf S.G') × Edat (stepG d L N₁ m₁ k ϱ) N →
      ((stepG d L N₁ m₁ k ϱ).Ω 1 × Fin N → ℂ) × ((stepG d L N₁ m₁ k ϱ).Ω 1 → ℂ))
    (hSolan : ∀ τ : 𝒯E, AnalyticOnNhd ℂ (Sol τ) {p | (∀ P, ‖p.1 P‖ < Real.exp κ) ∧
      StrictDataM (stepG d L N₁ m₁ k ϱ) N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2})
    (hSolprop : ∀ τ : 𝒯E, ∀ p : Dec2.DecParams (coverOf S.G') × Edat (stepG d L N₁ m₁ k ϱ) N,
      (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM (stepG d L N₁ m₁ k ϱ) N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2 →
        (Sol τ p).1 = dphi (stepG d L N₁ m₁ k ϱ)
            (Dec2.decG (coverOf S.G') (stepG d L N₁ m₁ k ϱ) (compWeight L S.a₁) S.ν p.1)
            p.2.2.1 p.2.1
            (pertSource (stepG d L N₁ m₁ k ϱ) (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) (Sol τ p).2 ∧
        Dec2.DecFixed (coverOf S.G') (stepG d L N₁ m₁ k ϱ) (compWeight L S.a₁) S.ν p.1 false
          p.2.2.1 p.2.1
          (pertSource (stepG d L N₁ m₁ k ϱ) (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) (Sol τ p).2 ∧
        Small (stepG d L N₁ m₁ k ϱ) (Sol τ p).2 (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
        Small (stepG d L N₁ m₁ k ϱ) (Sol τ p).2 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        SupBounds (stepG d L N₁ m₁ k ϱ) (Sol τ p).1 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        (∀ δα' : (stepG d L N₁ m₁ k ϱ).Ω 1 → ℂ,
          Small (stepG d L N₁ m₁ k ϱ) δα' (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf S.G') (stepG d L N₁ m₁ k ϱ) (compWeight L S.a₁) S.ν p.1 false
            p.2.2.1 p.2.1
            (pertSource (stepG d L N₁ m₁ k ϱ) (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) δα' →
          δα' = (Sol τ p).2))
    (Fk : ∀ τ : 𝒯E, RawData d L (N₁ * L ^ m₁) (k + 1) N →
      ((Gk τ).Ω 1 × Fin N → ℂ) × ((Gk τ).Ω 1 → ℂ))
    (hFkan : ∀ τ : 𝒯E, AnalyticOnNhd ℂ (Fk τ) {p | ∃ D : BgData (Gk τ) N,
      InUnionDomainC (Gk τ) (bgC0 d L N) (bgC1 d L N) S.ν D ∧ p = (D.Ψ, D.h)})
    (hFk : ∀ τ : 𝒯E, ∀ D : BgData (Gk τ) N, InUnionDomainC (Gk τ) (bgC0 d L N) (bgC1 d L N) S.ν D →
      Fk τ (rawOf D) = (bgFieldC (Gk τ) (compWeight L S.a₁) S.ν (bgC0 d L N) D,
        bgMultC (Gk τ) (compWeight L S.a₁) S.ν (bgC0 d L N) D))
    (hS : ∀ (τ : 𝒯E) (h : τ.1.1 ≤ k + 1), GsSpecStrong τ.1.1 h τ.1.2.2
      (C.Tm.gs τ.1.1 τ.1.2.2))
    (hc7 : c7 d L N BG κ ≤ thm73C3 d L N) {R : ℝ} (hR : 2 ≤ R)
    (hsmR : 2 * (compC4 d * (bgK1 d L N * (xiC1 d * eps))) + 5 * (R * δ₁) ≤ bgC1 d L N)
    (hRs : R * δ₁ ≤ deltaStar d L N) (hsmall : cK2 d L N * (R * δ₁) < bgC0 d L N / 2)
    (hnum : cK2 d L N * δ₁ ≤ c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8))
    (hnum' : cK2' d L N (famConst d L BG₂ κ) * δ₁ ≤
      c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8))
    (hN : L ^ C.m₀ ∣ N₁) (hm1 : 1 ≤ C.m₀) (hd : 3 ≤ d) (hL : 2 ≤ L)
    (z : RootIdx d L N₁ m₁ (k + 1)) {ρ : ℝ} (hρ : 0 < ρ) (hρc : ρ ≤ cψ) (hρpp : ρ < pp)
    (hp : 0 < S.p₁) {a bb : ℝ} (ha1 : 1 < a) (hbb : 0 < bb)
    (hab : (a + bb) * markedRad d L N k S.a₁ κ cψ ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) < δ₁)
    (G₁ : physParam N S →
      {q // q ∈ markedIdx (fun _ => (Set.univ : Set (CTorus d L N₁ m₁ (k + 1))))
        (fun τ => polyDom S.G' (X₁f τ) C.m₀ τ.1.1 (𝒦X τ)) z} →
      ℂ → (∀ b, (S.blockSplit 1 hp).Ωb b) → ℂ)
    (hG₁ : ∀ θ q u Φ, G₁ θ q u Φ =
      if (θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) ∈
          XiCRaw S.G' (compWeight L S.a₁) S.ν (k + 1) 1 eps ∧ ‖u‖ < a then
        (S.β : ℂ) * deriv (fun t : ℂ => evDec (X₁f q.1.1) C.m₀ q.1.1.1.1 (𝒦X q.1.1) S.a₁ S.ν
          S.hG' ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) (F₁ q.1.1) (Sol q.1.1)
          (eTermFun S.G' (Gk q.1.1) (C.Tm.gs q.1.1.1.1 q.1.1.1.2.2) (stepG d L N₁ m₁ k ϱ)
            (compWeight L S.a₁) (Fk q.1.1)
            (fun r => (S.β : ℂ)⁻¹ * C.Tm.E q.1.1.1.1 q.1.1.1.2.1 q.1.1.1.2.2 r.1 r.2))
          (S.blockU z) u t q.1.2
          ((θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N), S.hatOf 1 ρ hp Φ)) 0
      else 0)
    (hρp : S.p₁ ≤ ρ)
    (hE : ∀ D : BgData S.G' N, XiCData S.G' S.a S.ν (k + 1) 1 eps D →
      ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ x : S.E, ‖x‖ ≤ S.p₁ → ∀ j ∈ Finset.Icc 1 k,
      AnalyticAt ℂ
        (fun p : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N => Edens C.m₀ C.Tm j p.1 p.2)
        (Jr.PJ j (rawOf D, (s : ℂ) • yhat x)))
    {Lb : Type*} (Lab : CubeLabels (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) 1 (k + 1)
      Set.univ Lb)
    {β₀ : Type*} [Fintype β₀] (reads₀ : β₀ → Set (CTorus d L N₁ m₁ (k + 1)))
    (dom₀ : β₀ → Finset (Set (CTorus d L N₁ m₁ (k + 1))))
    (hN1 : L ^ 1 ∣ N₁) (hdom₀ : ∀ b, ∀ Y ∈ dom₀ b, IsDj 1 (k + 1) Y)
    (y1 : {q // q ∈ markedIdx (fun _ => (Set.univ : Set (CTorus d L N₁ m₁ (k + 1))))
        (fun τ => polyDom S.G' (X₁f τ) C.m₀ τ.1.1 (𝒦X τ)) z} → Lb ⊕ RootUnionLb 1 reads₀ dom₀)
    (hy1 : ∀ q, (commonLabels Lab hN1 hL reads₀ dom₀ hdom₀).ysite (y1 q) = bridge 1 z q.1.2)
    (κG : ℝ) :
    ∃ F1 : {q // q ∈ markedIdx (fun _ => (Set.univ : Set (CTorus d L N₁ m₁ (k + 1))))
        (fun τ => polyDom S.G' (X₁f τ) C.m₀ τ.1.1 (𝒦X τ)) z} → ℝ, (∀ q, 0 < F1 q) ∧
    -- measurability
    (∀ θ q u, Measurable (G₁ θ q u)) ∧
    -- block locality on the label of the mark
    (∀ θ q u, DepOn (blocksOf 1 (k + 1) Set.univ
      ((commonLabels Lab hN1 hL reads₀ dom₀ hdom₀).ysite (y1 q))) (G₁ θ q u)) ∧
    -- the bound
    (∀ θ q u Φ, ‖G₁ θ q u Φ‖ ≤ F1 q * Real.exp (-κG *
      (commonLabels Lab hN1 hL reads₀ dom₀ hdom₀).dl (y1 q))) ∧
    -- analyticity in the parameter and the first mark
    (∀ q, ∀ Φ ∈ physCarrier S 1 hp, AnalyticOnNhd ℂ (fun r : physParam N S × ℂ => G₁ r.1 q r.2 Φ)
      (physV S S.a₁ S.ν eps ×ˢ Metric.ball (0 : ℂ) a)) ∧
    -- continuity on the carrier
    (∀ q, ∀ θ ∈ physV S S.a₁ S.ν eps, ∀ u ∈ Metric.ball (0 : ℂ) a,
      ContinuousOn (G₁ θ q u) (physCarrier S 1 hp)) ∧
    -- holomorphy in the first mark
    (∀ θ ∈ physV S S.a₁ S.ν eps, ∀ q Φ,
      DifferentiableOn ℂ (fun u => G₁ θ q u Φ) (Metric.ball (0 : ℂ) a)) ∧
    -- locality in the parameter
    (∀ A : Set (CTorus d L N₁ m₁ (k + 1)), ∀ θ ∈ physV S S.a₁ S.ν eps,
      ∀ θ' ∈ physV S S.a₁ S.ν eps,
      physRestrict (N := N) A (physIncl N S θ) = physRestrict A (physIncl N S θ') →
      ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ q,
        (commonLabels Lab hN1 hL reads₀ dom₀ hdom₀).ysite (y1 q) ⊆ Yhat Set.univ A →
        G₁ θ q (s : ℂ) = G₁ θ' q (s : ℂ)) ∧
    -- the root cube in every label
    (∀ q, rootCube (m₀ := 1) z ∈ blocksOf 1 (k + 1) Set.univ
      ((commonLabels Lab hN1 hL reads₀ dom₀ hdom₀).ysite (y1 q))) ∧
    -- the identity of the marks
    (∀ D : BgData S.G' N, XiCData S.G' S.a S.ν (k + 1) 1 eps D →
      ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ᵐ x ∂S.nuFl,
        (fderiv ℂ (fun w : S.EC => Jr.EJ C (rawOf D, w)) ((s : ℂ) • yhat x))
            ((Jr.Mx (rawOf D))⁻¹ *ᵥ S.maskUC z (Jr.Mx (rawOf D) *ᵥ yhat x)) =
          ∑ q, G₁ ((⟨rawOf D, rawOf_mem_rawSub _⟩ : rawSub N S.G'),
            (0 : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ)) q (s : ℂ)
            ((S.blockSplit 1 hp).restr x)) := by
  classical
  have hmem : ∀ τ : 𝒯E, τ.1.1 ∈ Finset.Icc 1 k ∧ Aligned (L ^ τ.1.1) τ.1.2.1 ∧
      IsPolyDom C.m₀ τ.1.1 τ.1.2.2 ∧ τ.1.2.1 ∈ τ.1.2.2 := by
    intro τ
    have h : τ.1 ∈ ((Finset.Icc 1 k) ×ˢ (Finset.univ : Finset (CTorus d L N₁ m₁ (k + 1) ×
        Set (CTorus d L N₁ m₁ (k + 1))))).filter
        (fun τ => Aligned (L ^ τ.1) τ.2.1 ∧ IsPolyDom C.m₀ τ.1 τ.2.2 ∧ τ.2.1 ∈ τ.2.2) := by
      rw [← h𝒯]; exact τ.2
    rw [Finset.mem_filter, Finset.mem_product] at h
    exact ⟨h.1.1, h.2⟩
  have hj1 : ∀ τ : 𝒯E, 1 ≤ τ.1.1 := fun τ => (Finset.mem_Icc.1 (hmem τ).1).1
  have hjk : ∀ τ : 𝒯E, τ.1.1 ≤ k := fun τ => (Finset.mem_Icc.1 (hmem τ).1).2
  have hXp : ∀ τ : 𝒯E, IsPolyDom C.m₀ τ.1.1 τ.1.2.2 := fun τ => (hmem τ).2.2.1
  have hy : ∀ τ : 𝒯E, τ.1.2.1 ∈ τ.1.2.2 := fun τ => (hmem τ).2.2.2
  have hraw := fun τ : 𝒯E => classOldEnergy_chart_radius_raw (N := N) (b := b) C hm hcl hκP hE₀
    S.a₁ S.ν δ₃ eps δfl (hj1 τ) (hjk τ) (hXp τ) (hy τ) (hchart τ)
  have hEJ : ∀ D : BgData S.G' N, XiCData S.G' S.a S.ν (k + 1) 1 eps D → ∀ w : S.EC,
      Jr.EJ C (rawOf D, w) = ∑ τ : 𝒯E,
        C.Tm.E τ.1.1 τ.1.2.1 τ.1.2.2 (Jr.PJ τ.1.1 (rawOf D, w)).1
          (Jr.PJ τ.1.1 (rawOf D, w)).2 := fun D _ w => by
    unfold StepSetting.JointRep.EJ
    rw [Finset.sum_coe_sort 𝒯E (fun τ => C.Tm.E τ.1 τ.2.1 τ.2.2 (Jr.PJ τ.1 (rawOf D, w)).1
      (Jr.PJ τ.1 (rawOf D, w)).2), h𝒯,
      sum_classLabels_E_eq_Edens C.m₀ C.Tm (fun j => (Jr.PJ j (rawOf D, w)).1)
      (fun j => (Jr.PJ j (rawOf D, w)).2)]
  have key := Jr.classMarks_M2_of_family_gen (ι := 𝒯E) (m₀ := C.m₀) C hb₁ hbC
    (fun τ r => C.Tm.E τ.1.1 τ.1.2.1 τ.1.2.2 r.1 r.2) (fun _ => P.E₀) (fun _ => hE₀) hβ
    (fun τ => τ.1.1) (fun τ => τ.1.2.2) hj1 hjk Gk (fun τ => C.Tm.gs τ.1.1 τ.1.2.2)
    (fun τ Ψ Ψ' h h' hag => hcl.localE τ.1.1 τ.1.2.1 τ.1.2.2 Ψ Ψ' h h' hag) X₀ X₁f 𝒦X hB hF hcψ
    hMX hdm hα hsm hcov hX₁ hconn hrow hopt hκ₀ hκdec hκ h1 hlog (fun τ => (hraw τ).1)
    (fun τ => (hraw τ).2) F₁ hF₁an hF₁ Sol hSolan hSolprop Fk hFkan hFk
    (fun τ => hS τ ((hjk τ).trans (Nat.le_succ k))) hc7 hR hsmR hRs hsmall hnum hnum' hN hm1 hd hL
    z hρ hρc hρpp hp ha1 hbb hab G₁ hG₁ hEJ hρp hE Lab reads₀ dom₀ hN1 hdom₀ y1 hy1 κG
  exact key

end StepSetting.JointRep

end Balaban.Fluctuation
