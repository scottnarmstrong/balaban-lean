/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.LocalClassDensityFamilyActSum
public import Balaban.Fluctuation.MarkedCommonLabels
public import Balaban.Polymer.LabelSum

/-!
# The input (M1) of a class with inherited labels (`LocalClassDensityFamilyActM1`)

The input (M1) of `e0CoeffFamily_class_fromTower` is one activity family `A` on the common labels
`commonLabels Lab …` with the label sum `W₁^C(rawOf D, s ψ̂)` at every chart datum, analytic in
`(θ, u)`, continuous on the carrier, holomorphic in `u` and local on `sitesOf T`.  Since
`W₁^C = W₁^0 + (ℰ_k(·) - ℰ_k(·, 0))` (`W1_eq_zeroClass_add_EJ`), the family is the sum
(`LabelAct.sum`) of an activity family `A₀` of the zero class (for the tower: the zero-source
activity) and the activity family `A₁` of the inherited energy, extended by zero to the labels of
all roots (`commonAct`).

* `classActivityFamily_sum_fields`: for two activity families `A₀`, `A₁` on labels `Lab₀`, `Lab₁`
  with the analyticity, continuity, holomorphy and locality fields, with
  `W₁^0 = ∑ A₀` and `W₁^C = W₁^0 + ∑ A₁` almost surely at every chart datum, the family
  `commonAct (A₀.sum A₁)` on `commonLabels (Lab₀.sum Lab₁)` has the five fields (M1) with
  `W₁^C = ∑ commonAct (A₀.sum A₁)`.
* `classE1_M1_of_family`: **the input (M1) of a class with inherited labels.**  For a family `A₀`
  of the zero class with these fields, and the labels of the class with their settings, given maps
  and the numerical conditions, there is an activity family `A_C` on the labels of the domains of
  the class (`classActivityFamily_labelAct`) such that
  `commonAct (A₀.sum (commonAct A_C …))` on the common labels
  `commonLabels (Lab₀.sum (commonLabels (thickLabels 𝒴C) … polyDom …))` satisfies (M1); the
  root-union labels of the class domains (the bridges of the rooted pairs) are the labels of the
  marks (M2).
-/

@[expose] public section

namespace Balaban.Fluctuation

open MeasureTheory Balaban Balaban.Localization Balaban.Multiscale
  Balaban.Background Balaban.SmallField Balaban.SmallField.Def6 Balaban.SmallField.Def6v2
  Balaban.SmallField.GsSpec Balaban.Analysis Balaban.Polymer Finset Matrix

namespace StepSetting.JointRep

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ ϱ₁ : ℝ}
variable {S : StepSetting d L N₁ m₁ k N ϱ} {eps pp : ℝ} (Jr : S.JointRep eps pp)
  {c BG κ r₀ δ₃ Kc Cx c₂ BG₂ δ₁ δfl : ℝ}

open Classical in
/-- **The fields (M1) of a sum of two activity families on the common labels.**  For activity
families `A₀` on `Lab₀` and `A₁` on `Lab₁` (block index `1`, the same rates) with the analyticity
on `V × 𝒰`, the continuity on `Q`, the holomorphy in `u` on `𝒰`, the locality on `sitesOf T` and
the identities `W₁^0(rawOf D, s ψ̂) = ∑ A₀` and `W₁^C(rawOf D, s ψ̂) = W₁^0(rawOf D, s ψ̂) + ∑ A₁`
almost surely at every chart datum, the family `commonAct (A₀.sum A₁)` on
`commonLabels (Lab₀.sum Lab₁) … reads dom …` has the same fields and
`W₁^C(rawOf D, s ψ̂) = ∑ commonAct (A₀.sum A₁)` almost surely (`commonAct_total`,
`LabelAct.sum_total`). -/
theorem classActivityFamily_sum_fields (C : StepClass d L N₁ m₁ k N ϱ) (hp : 0 < S.p₁)
    {Lb₀ Lb₁ : Type*} [Fintype Lb₀] [Fintype Lb₁]
    {Lab₀ : CubeLabels (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) 1 (k + 1)
      Set.univ Lb₀}
    {Lab₁ : CubeLabels (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) 1 (k + 1)
      Set.univ Lb₁}
    {ε₀ ε₁ κH κ0 K₀ K₁ : ℝ}
    (A₀ : physParam N S → ℂ → LabelAct Lab₀ (S.blockSplit 1 hp).Ωb ε₀ κH κ0 K₀)
    (A₁ : physParam N S → ℂ → LabelAct Lab₁ (S.blockSplit 1 hp).Ωb ε₁ κH κ0 K₁)
    {β : Type*} [Fintype β] (reads : β → Set (CTorus d L N₁ m₁ (k + 1)))
    (dom : β → Finset (Set (CTorus d L N₁ m₁ (k + 1))))
    (hdom : ∀ b, ∀ Y ∈ dom b, IsDj 1 (k + 1) Y) (hN : L ^ 1 ∣ N₁) (hL : 2 ≤ L)
    (hε : 0 ≤ max ε₀ ε₁) (hκ0 : aEnt d L + 2 ≤ κ0)
    {V : Set (physParam N S)} {𝒰 : Set ℂ} {Q : Set (∀ b, (S.blockSplit 1 hp).Ωb b)}
    (h0hol : ∀ y, ∀ Φ ∈ Q, AnalyticOnNhd ℂ (fun r : physParam N S × ℂ => (A₀ r.1 r.2).H y Φ)
      (V ×ˢ 𝒰))
    (h1hol : ∀ y, ∀ Φ ∈ Q, AnalyticOnNhd ℂ (fun r : physParam N S × ℂ => (A₁ r.1 r.2).H y Φ)
      (V ×ˢ 𝒰))
    (h0cont : ∀ y, ∀ θ ∈ V, ∀ u ∈ 𝒰, ContinuousOn ((A₀ θ u).H y) Q)
    (h1cont : ∀ y, ∀ θ ∈ V, ∀ u ∈ 𝒰, ContinuousOn ((A₁ θ u).H y) Q)
    (h0diff : ∀ θ ∈ V, ∀ y Φ, DifferentiableOn ℂ (fun u => (A₀ θ u).H y Φ) 𝒰)
    (h1diff : ∀ θ ∈ V, ∀ y Φ, DifferentiableOn ℂ (fun u => (A₁ θ u).H y Φ) 𝒰)
    (h0loc : ∀ T' : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) 1 (k + 1)
        Set.univ), ∀ θ ∈ V, ∀ θ' ∈ V,
      physRestrict (N := N) (sitesOf T') (physIncl N S θ) =
        physRestrict (sitesOf T') (physIncl N S θ') →
      ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ y, Lab₀.ysite y ⊆ Yhat Set.univ (sitesOf T') →
        (A₀ θ (s : ℂ)).H y = (A₀ θ' (s : ℂ)).H y)
    (h1loc : ∀ T' : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) 1 (k + 1)
        Set.univ), ∀ θ ∈ V, ∀ θ' ∈ V,
      physRestrict (N := N) (sitesOf T') (physIncl N S θ) =
        physRestrict (sitesOf T') (physIncl N S θ') →
      ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ y, Lab₁.ysite y ⊆ Yhat Set.univ (sitesOf T') →
        (A₁ θ (s : ℂ)).H y = (A₁ θ' (s : ℂ)).H y)
    (h0W : ∀ D : BgData S.G' N, XiCData S.G' S.a S.ν (k + 1) 1 eps D →
      ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ᵐ x ∂S.nuFl,
        Jr.W1 (zeroClass d L N₁ m₁ k N ϱ) (rawOf D, (s : ℂ) • yhat x) =
          ∑ y, (A₀ ((⟨rawOf D, rawOf_mem_rawSub _⟩ : rawSub N S.G'),
            (0 : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ)) (s : ℂ)).H y
            ((S.blockSplit 1 hp).restr x))
    (h1W : ∀ D : BgData S.G' N, XiCData S.G' S.a S.ν (k + 1) 1 eps D →
      ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ᵐ x ∂S.nuFl,
        Jr.W1 C (rawOf D, (s : ℂ) • yhat x) =
          Jr.W1 (zeroClass d L N₁ m₁ k N ϱ) (rawOf D, (s : ℂ) • yhat x) +
            ∑ y, (A₁ ((⟨rawOf D, rawOf_mem_rawSub _⟩ : rawSub N S.G'),
              (0 : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ)) (s : ℂ)).H y
              ((S.blockSplit 1 hp).restr x)) :
    (∀ y, ∀ Φ ∈ Q, AnalyticOnNhd ℂ (fun r : physParam N S × ℂ =>
      (commonAct (fun θ u => (A₀ θ u).sum (A₁ θ u)) hN hL reads dom hdom hε hκ0 r.1 r.2).H y Φ)
      (V ×ˢ 𝒰)) ∧
    (∀ y, ∀ θ ∈ V, ∀ u ∈ 𝒰, ContinuousOn
      ((commonAct (fun θ u => (A₀ θ u).sum (A₁ θ u)) hN hL reads dom hdom hε hκ0 θ u).H y) Q) ∧
    (∀ θ ∈ V, ∀ y Φ, DifferentiableOn ℂ (fun u =>
      (commonAct (fun θ u => (A₀ θ u).sum (A₁ θ u)) hN hL reads dom hdom hε hκ0 θ u).H y Φ) 𝒰) ∧
    (∀ T' : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) 1 (k + 1)
        Set.univ), ∀ θ ∈ V, ∀ θ' ∈ V,
      physRestrict (N := N) (sitesOf T') (physIncl N S θ) =
        physRestrict (sitesOf T') (physIncl N S θ') →
      ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ y,
        (commonLabels (Lab₀.sum Lab₁) hN hL reads dom hdom).ysite y ⊆
          Yhat Set.univ (sitesOf T') →
        (commonAct (fun θ u => (A₀ θ u).sum (A₁ θ u)) hN hL reads dom hdom hε hκ0 θ
          (s : ℂ)).H y =
        (commonAct (fun θ u => (A₀ θ u).sum (A₁ θ u)) hN hL reads dom hdom hε hκ0 θ'
          (s : ℂ)).H y) ∧
    (∀ D : BgData S.G' N, XiCData S.G' S.a S.ν (k + 1) 1 eps D →
      ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ᵐ x ∂S.nuFl,
        Jr.W1 C (rawOf D, (s : ℂ) • yhat x) =
          ∑ y, (commonAct (fun θ u => (A₀ θ u).sum (A₁ θ u)) hN hL reads dom hdom hε hκ0
            ((⟨rawOf D, rawOf_mem_rawSub _⟩ : rawSub N S.G'),
              (0 : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ)) (s : ℂ)).H y
            ((S.blockSplit 1 hp).restr x)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · refine commonAct_holA_analytic _ hN hL reads dom hdom hε hκ0 fun y Φ hΦ => ?_
    cases y with
    | inl y => exact h0hol y Φ hΦ
    | inr y => exact h1hol y Φ hΦ
  · refine commonAct_contA _ hN hL reads dom hdom hε hκ0 fun y θ hθ u hu => ?_
    cases y with
    | inl y => exact h0cont y θ hθ u hu
    | inr y => exact h1cont y θ hθ u hu
  · intro θ hθ
    refine commonAct_holA_differentiableOn _ hN hL reads dom hdom hε hκ0 θ fun y Φ => ?_
    cases y with
    | inl y => exact h0diff θ hθ y Φ
    | inr y => exact h1diff θ hθ y Φ
  · intro T' θ hθ θ' hθ' hres s hs y hsub
    rcases y with (y | y) | y
    · exact h0loc T' θ hθ θ' hθ' hres s hs y hsub
    · exact h1loc T' θ hθ θ' hθ' hres s hs y hsub
    · rfl
  · intro D hD s hs
    filter_upwards [h0W D hD s hs, h1W D hD s hs] with x h0 h1
    rw [h1, h0, commonAct_total _ hN hL reads dom hdom hε hκ0]
    exact (LabelAct.sum_total _ _ _).symm

open Classical in
/-- **The input (M1) of a class with inherited labels.**  For the labels of the class (`𝒯E`) with
their settings, given maps and the hypotheses of `classActivityFamily_ae_W1_eq`, the domains `𝒴C`
of their expansions (`h𝒴dj`: domains of `𝒟_{k+1}` for the index `1`, `classActivityDomains_isDj`;
`hdomC`: the same for each label, `polyDom_isDj_one`), the activities `H` (formula `hH`), the
numerical condition `hnumH` of `classActivityFamily_labelAct`, and an activity family `A₀` of the
zero class on labels `Lab₀` with the fields (M1) for `W₁^0` (analytic on `physV × {‖u‖ < a}`,
continuous on `Q`, holomorphic in `u`, local on `sitesOf T`, `W₁^0 = ∑ A₀` almost surely at every
chart datum): there is an activity family `A_C` on the labels `thickLabels 𝒴C` with
`(A_C θ u).H Y = H θ Y u` such that the family
`commonAct (A₀.sum (commonAct A_C … polyDom …))` on
`commonLabels (Lab₀.sum (commonLabels (thickLabels 𝒴C) … polyDom …)) … reads₀ dom₀ …` satisfies
every hypothesis (M1) of `e0CoeffFamily_class_fromTower` in its form: analytic in `(θ, u)` on
`physV × {‖u‖ < a}`, continuous on `Q`, holomorphic in `u`, local on `sitesOf T`, and
`W₁^C(rawOf D, s ψ̂) = ∑_y (A (rawOf D, 0) s).H y (restr x)` almost surely at every chart datum. -/
theorem classE1_M1_of_family {P : Consts} {Dom : FieldDom d L N₁ m₁ (k + 1) N ϱ}
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
    (z : RootIdx d L N₁ m₁ (k + 1)) {ρ : ℝ} (hρ : 0 < ρ) (hρc : ρ ≤ cψ) (hρpp : ρ < pp)
    (hp : 0 < S.p₁) {a bb : ℝ} (ha1 : 1 < a) (hbb : 0 ≤ bb)
    (hab : (a + bb) * markedRad d L N k S.a₁ κ cψ ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) < δ₁)
    (𝒴C : Finset (Set (CTorus d L N₁ m₁ (k + 1))))
    (h𝒴 : 𝒴C = Finset.univ.biUnion fun τ => polyDom S.G' (X₁f τ) C.m₀ τ.1.1 (𝒦X τ))
    (H : physParam N S → {Y // Y ∈ 𝒴C} → ℂ → (∀ b, (S.blockSplit 1 hp).Ωb b) → ℂ)
    (hH : ∀ θ Y u Φ, H θ Y u Φ =
      if (θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) ∈
          XiCRaw S.G' (compWeight L S.a₁) S.ν (k + 1) 1 eps ∧ ‖u‖ < a then
        ∑ τ, if Y.1 ∈ polyDom S.G' (X₁f τ) C.m₀ τ.1.1 (𝒦X τ) then
          (S.β : ℂ) * (evDec (X₁f τ) C.m₀ τ.1.1 (𝒦X τ) S.a₁ S.ν S.hG'
            ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) (F₁ τ) (Sol τ)
            (eTermFun S.G' (Gk τ) (C.Tm.gs τ.1.1 τ.1.2.2) (stepG d L N₁ m₁ k ϱ)
              (compWeight L S.a₁) (Fk τ)
              (fun r => (S.β : ℂ)⁻¹ * C.Tm.E τ.1.1 τ.1.2.1 τ.1.2.2 r.1 r.2)) (S.blockU z) u 0 Y.1
              ((θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N), S.hatOf 1 ρ hp Φ) -
            evDec (X₁f τ) C.m₀ τ.1.1 (𝒦X τ) S.a₁ S.ν S.hG'
            ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) (F₁ τ) (Sol τ)
            (eTermFun S.G' (Gk τ) (C.Tm.gs τ.1.1 τ.1.2.2) (stepG d L N₁ m₁ k ϱ)
              (compWeight L S.a₁) (Fk τ)
              (fun r => (S.β : ℂ)⁻¹ * C.Tm.E τ.1.1 τ.1.2.1 τ.1.2.2 r.1 r.2)) (S.blockU z) 0 0 Y.1
              ((θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N), S.hatOf 1 ρ hp Φ))
        else 0
      else 0)
    (hρp : S.p₁ ≤ ρ)
    (hN : L ^ C.m₀ ∣ N₁) (hm1 : 1 ≤ C.m₀) (hd : 3 ≤ d) (hL : 2 ≤ L) (hN1 : L ^ 1 ∣ N₁)
    (h𝒴dj : ∀ Y ∈ 𝒴C, IsDj 1 (k + 1) Y)
    (hdomC : ∀ τ : 𝒯E, ∀ Y ∈ polyDom S.G' (X₁f τ) C.m₀ τ.1.1 (𝒦X τ), IsDj 1 (k + 1) Y)
    {εC κH κ0 : ℝ} (hκ0 : aEnt d L + 2 ≤ κ0) (hεC : 0 ≤ εC)
    (hnumH : ∀ Y ∈ 𝒴C, (∑ τ : 𝒯E, if Y ∈ polyDom S.G' (X₁f τ) C.m₀ τ.1.1 (𝒦X τ) then
        2 * P.E₀ * Real.exp (-κ₀ * treeLenCovOne C.m₀ τ.1.1 τ.1.2.2 -
          2 * κdec * treeLenCov S.G' C.m₀ Y)
      else 0) ≤ εC * Real.exp (-κH * treeLenCovOne 1 (k + 1) Y))
    {Lb₀ : Type*} [Fintype Lb₀]
    (Lab₀ : CubeLabels (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) 1 (k + 1)
      Set.univ Lb₀) {ε₀ K₀ : ℝ}
    (A₀ : physParam N S → ℂ → LabelAct Lab₀ (S.blockSplit 1 hp).Ωb ε₀ κH κ0 K₀)
    {β₀ : Type*} [Fintype β₀] (reads₀ : β₀ → Set (CTorus d L N₁ m₁ (k + 1)))
    (dom₀ : β₀ → Finset (Set (CTorus d L N₁ m₁ (k + 1))))
    (hdom₀ : ∀ b, ∀ Y ∈ dom₀ b, IsDj 1 (k + 1) Y) (hε : 0 ≤ max ε₀ εC)
    {Q : Set (∀ b, (S.blockSplit 1 hp).Ωb b)}
    (h0hol : ∀ y, ∀ Φ ∈ Q, AnalyticOnNhd ℂ (fun r : physParam N S × ℂ => (A₀ r.1 r.2).H y Φ)
      (physV S S.a₁ S.ν eps ×ˢ Metric.ball (0 : ℂ) a))
    (h0cont : ∀ y, ∀ θ ∈ physV S S.a₁ S.ν eps, ∀ u ∈ Metric.ball (0 : ℂ) a,
      ContinuousOn ((A₀ θ u).H y) Q)
    (h0diff : ∀ θ ∈ physV S S.a₁ S.ν eps, ∀ y Φ,
      DifferentiableOn ℂ (fun u => (A₀ θ u).H y Φ) (Metric.ball (0 : ℂ) a))
    (h0loc : ∀ T' : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) 1 (k + 1)
        Set.univ), ∀ θ ∈ physV S S.a₁ S.ν eps, ∀ θ' ∈ physV S S.a₁ S.ν eps,
      physRestrict (N := N) (sitesOf T') (physIncl N S θ) =
        physRestrict (sitesOf T') (physIncl N S θ') →
      ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ y, Lab₀.ysite y ⊆ Yhat Set.univ (sitesOf T') →
        (A₀ θ (s : ℂ)).H y = (A₀ θ' (s : ℂ)).H y)
    (h0W : ∀ D : BgData S.G' N, XiCData S.G' S.a S.ν (k + 1) 1 eps D →
      ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ᵐ x ∂S.nuFl,
        Jr.W1 (zeroClass d L N₁ m₁ k N ϱ) (rawOf D, (s : ℂ) • yhat x) =
          ∑ y, (A₀ ((⟨rawOf D, rawOf_mem_rawSub _⟩ : rawSub N S.G'),
            (0 : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ)) (s : ℂ)).H y
            ((S.blockSplit 1 hp).restr x)) :
    ∃ AC : physParam N S → ℂ → LabelAct (thickLabels (m₀ := 1) (j := k + 1) 𝒴C h𝒴dj)
        (S.blockSplit 1 hp).Ωb εC κH κ0 (K0 d L κ0),
      (∀ θ u Y, (AC θ u).H Y = H θ Y u) ∧
      (∀ y, ∀ Φ ∈ Q, AnalyticOnNhd ℂ (fun r : physParam N S × ℂ =>
        (commonAct (fun θ u => (A₀ θ u).sum (commonAct AC hN1 hL (fun _ => Set.univ)
          (fun τ : 𝒯E => polyDom S.G' (X₁f τ) C.m₀ τ.1.1 (𝒦X τ)) hdomC hεC hκ0 θ u))
          hN1 hL reads₀ dom₀ hdom₀ hε hκ0 r.1 r.2).H y Φ)
        (physV S S.a₁ S.ν eps ×ˢ Metric.ball (0 : ℂ) a)) ∧
      (∀ y, ∀ θ ∈ physV S S.a₁ S.ν eps, ∀ u ∈ Metric.ball (0 : ℂ) a, ContinuousOn
        ((commonAct (fun θ u => (A₀ θ u).sum (commonAct AC hN1 hL (fun _ => Set.univ)
          (fun τ : 𝒯E => polyDom S.G' (X₁f τ) C.m₀ τ.1.1 (𝒦X τ)) hdomC hεC hκ0 θ u))
          hN1 hL reads₀ dom₀ hdom₀ hε hκ0 θ u).H y) Q) ∧
      (∀ θ ∈ physV S S.a₁ S.ν eps, ∀ y Φ, DifferentiableOn ℂ (fun u =>
        (commonAct (fun θ u => (A₀ θ u).sum (commonAct AC hN1 hL (fun _ => Set.univ)
          (fun τ : 𝒯E => polyDom S.G' (X₁f τ) C.m₀ τ.1.1 (𝒦X τ)) hdomC hεC hκ0 θ u))
          hN1 hL reads₀ dom₀ hdom₀ hε hκ0 θ u).H y Φ) (Metric.ball (0 : ℂ) a)) ∧
      (∀ T' : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) 1 (k + 1)
          Set.univ), ∀ θ ∈ physV S S.a₁ S.ν eps, ∀ θ' ∈ physV S S.a₁ S.ν eps,
        physRestrict (N := N) (sitesOf T') (physIncl N S θ) =
          physRestrict (sitesOf T') (physIncl N S θ') →
        ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ y,
          (commonLabels (Lab₀.sum (commonLabels (thickLabels (m₀ := 1) (j := k + 1) 𝒴C h𝒴dj)
            hN1 hL (fun _ => Set.univ)
            (fun τ : 𝒯E => polyDom S.G' (X₁f τ) C.m₀ τ.1.1 (𝒦X τ)) hdomC))
            hN1 hL reads₀ dom₀ hdom₀).ysite y ⊆ Yhat Set.univ (sitesOf T') →
          (commonAct (fun θ u => (A₀ θ u).sum (commonAct AC hN1 hL (fun _ => Set.univ)
            (fun τ : 𝒯E => polyDom S.G' (X₁f τ) C.m₀ τ.1.1 (𝒦X τ)) hdomC hεC hκ0 θ u))
            hN1 hL reads₀ dom₀ hdom₀ hε hκ0 θ (s : ℂ)).H y =
          (commonAct (fun θ u => (A₀ θ u).sum (commonAct AC hN1 hL (fun _ => Set.univ)
            (fun τ : 𝒯E => polyDom S.G' (X₁f τ) C.m₀ τ.1.1 (𝒦X τ)) hdomC hεC hκ0 θ u))
            hN1 hL reads₀ dom₀ hdom₀ hε hκ0 θ' (s : ℂ)).H y) ∧
      (∀ D : BgData S.G' N, XiCData S.G' S.a S.ν (k + 1) 1 eps D →
        ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ᵐ x ∂S.nuFl,
          Jr.W1 C (rawOf D, (s : ℂ) • yhat x) =
            ∑ y, (commonAct (fun θ u => (A₀ θ u).sum (commonAct AC hN1 hL (fun _ => Set.univ)
              (fun τ : 𝒯E => polyDom S.G' (X₁f τ) C.m₀ τ.1.1 (𝒦X τ)) hdomC hεC hκ0 θ u))
              hN1 hL reads₀ dom₀ hdom₀ hε hκ0
              ((⟨rawOf D, rawOf_mem_rawSub _⟩ : rawSub N S.G'),
                (0 : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ)) (s : ℂ)).H y
              ((S.blockSplit 1 hp).restr x)) := by
  classical
  have hmem𝒯 : ∀ τ : 𝒯E, τ.1.1 ∈ Finset.Icc 1 k ∧ Aligned (L ^ τ.1.1) τ.1.2.1 ∧
      IsPolyDom C.m₀ τ.1.1 τ.1.2.2 ∧ τ.1.2.1 ∈ τ.1.2.2 := by
    intro τ
    have h : τ.1 ∈ ((Finset.Icc 1 k) ×ˢ (Finset.univ : Finset (CTorus d L N₁ m₁ (k + 1) ×
        Set (CTorus d L N₁ m₁ (k + 1))))).filter
        (fun τ => Aligned (L ^ τ.1) τ.2.1 ∧ IsPolyDom C.m₀ τ.1 τ.2.2 ∧ τ.2.1 ∈ τ.2.2) := by
      rw [← h𝒯]; exact τ.2
    rw [Finset.mem_filter, Finset.mem_product] at h
    exact ⟨h.1.1, h.2⟩
  have hj1 : ∀ τ : 𝒯E, 1 ≤ τ.1.1 := fun τ => (Finset.mem_Icc.1 (hmem𝒯 τ).1).1
  have hjk : ∀ τ : 𝒯E, τ.1.1 ≤ k := fun τ => (Finset.mem_Icc.1 (hmem𝒯 τ).1).2
  have hXp : ∀ τ : 𝒯E, IsPolyDom C.m₀ τ.1.1 τ.1.2.2 := fun τ => (hmem𝒯 τ).2.2.1
  have hy : ∀ τ : 𝒯E, τ.1.2.1 ∈ τ.1.2.2 := fun τ => (hmem𝒯 τ).2.2.2
  have hκ0' : aEnt d L + 1 ≤ κ0 := by linarith
  obtain ⟨AC, hAC⟩ := classActivityFamily_labelAct S hb₁ hbC C hm hcl hβ hE₀ (fun τ => τ.1.1)
    (fun τ => τ.1.2.1) (fun τ => τ.1.2.2) hj1 hjk hXp hy Gk X₀ X₁f 𝒦X hB hF S.hG
    ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) hcψ hMX hdm hα hsm hcov hX₁ hconn hrow hopt hκ₀ hκdec hκ
    h1 hlog hκP hchart F₁ hF₁an hF₁ Sol hSolan hSolprop Fk hFkan hFk hN hm1 hd (S.blockU z) hρ hρc
    hp ha1 hbb hab 𝒴C h𝒴 h𝒴dj H (fun θ Y u Φ => by rw [hH]) hκ0' hnumH
  obtain ⟨-, -, -, hhol, hcont, hdiff, hloc⟩ := classActivityFamily_fields S hb₁ hbC C hm hcl hβ
    hE₀ (fun τ => τ.1.1) (fun τ => τ.1.2.1) (fun τ => τ.1.2.2) hj1 hjk hXp hy Gk X₀ X₁f 𝒦X hB hF
    S.hG ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) hcψ hMX hdm hα hsm hcov hX₁ hconn hrow hopt hκ₀
    hκdec hκ h1 hlog hκP hchart F₁ hF₁an hF₁ Sol hSolan hSolprop Fk hFkan hFk hN hm1 hd
    (S.blockU z) hρ hρc hp ha1 hbb hab 𝒴C h𝒴 H (fun θ Y u Φ => by rw [hH])
  have hW := Jr.classActivityFamily_ae_W1_eq C 𝒯E h𝒯 hb₁ hbC hm hcl hβ hE₀ Gk X₀ X₁f 𝒦X hB hF
    hcψ hMX hdm hα hsm hcov hX₁ hconn hrow hopt hκ₀ hκdec hκ h1 hlog hκP hchart F₁ hF₁an hF₁ Sol
    hSolan hSolprop Fk hFkan hFk hS hc7 hR hsmR hRs hsmall hnum hnum' z hρ hρc hρpp hp ha1 hbb hab
    𝒴C h𝒴 H hH hρp
  have hfun : ∀ Y (Φ : ∀ b, (S.blockSplit 1 hp).Ωb b),
      (fun r : physParam N S × ℂ => (AC r.1 r.2).H Y Φ) = fun r => H r.1 Y r.2 Φ :=
    fun Y Φ => funext fun r => by rw [hAC]
  refine ⟨AC, hAC, Jr.classActivityFamily_sum_fields C hp A₀ (fun θ u => commonAct AC hN1 hL
    (fun _ => Set.univ) (fun τ : 𝒯E => polyDom S.G' (X₁f τ) C.m₀ τ.1.1 (𝒦X τ)) hdomC hεC hκ0 θ u)
    reads₀ dom₀ hdom₀ hN1 hL hε hκ0 h0hol ?_ h0cont ?_ h0diff ?_ h0loc ?_ h0W ?_⟩
  · refine commonAct_holA_analytic AC hN1 hL _ _ hdomC hεC hκ0 fun Y Φ _ => ?_
    rw [hfun Y Φ]
    exact hhol Y Φ
  · refine commonAct_contA AC hN1 hL _ _ hdomC hεC hκ0 fun Y θ hθ u hu => ?_
    rw [show (AC θ u).H Y = fun Φ => H θ Y u Φ from funext fun Φ => by rw [hAC]]
    exact (hcont Y θ hθ u hu).continuousOn
  · intro θ hθ
    refine commonAct_holA_differentiableOn AC hN1 hL _ _ hdomC hεC hκ0 θ fun Y Φ => ?_
    rw [show (fun u => (AC θ u).H Y Φ) = fun u => H θ Y u Φ from funext fun u => by rw [hAC]]
    exact hdiff θ hθ Y Φ
  · intro T' θ hθ θ' hθ' hres s hs y hsub
    cases y with
    | inl Y =>
      show (AC θ (s : ℂ)).H Y = (AC θ' (s : ℂ)).H Y
      rw [hAC, hAC]
      exact hloc (sitesOf T') θ hθ θ' hθ' hres s hs Y hsub
    | inr _ => rfl
  · intro D hD s hs
    filter_upwards [hW D hD s hs] with x hx
    rw [hx, commonAct_total AC hN1 hL _ _ hdomC hεC hκ0]
    simp only [hAC]

end StepSetting.JointRep

end Balaban.Fluctuation
