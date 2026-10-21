/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.NewLevelCoeffBgClass
public import Balaban.Inhabited.NewLevelBridgeMarksBgCast
public import Balaban.Fluctuation.NewLevelZeroSourceBg
public import Balaban.Inhabited.ActivityFamilyAnalytic

/-!
# The coefficient of the new level of a class recomputed on a local generating set (`NewLevelCoeffBgClassCast`)

P3 pp. 78-79, (4.44)-(4.47): the coefficient of a polymer `T` of the new level, recomputed on a local
generating set `Gl` of `T` with the canonical transport, equals the step's coefficient at the datum
read from a datum `D` of the step chart.  The step's class family is
`commonAct (A₀.sum (commonAct A_C …))` with the zero-source activities `A₀` on the domains `𝒴₀` of the
direct terms and the activities `A_C` of the inherited energy on the domains `𝒴_C` of the old terms;
the marks are the bridge marks of the root and the marks `G₁` of the old terms.  On `Gl` the
activities are `zeroActBg`, `oldActBg` and the marks `e1MarkGParamGBgOn`, `oldMarkGBg` at the
canonical transport (mask `maskPre` of the block of the root).

* `ysite_subset_sitesOf`: a label whose blocks lie in `T` lies in the sites of `T`;
* `newLevelCoeffBg_class_canon_eq_of_det`: **the replacement identity (A5) of the coefficient,
  reduced to the determinant part**.  If the step's activities and marks are the formulas at the
  step's own set (`zeroActBg`, `oldActBg`, `oldMarkGBg` at `BgTransport.self`, the hypotheses
  `h0eq`, `h1eq`, `hG₁eq`) and the sites of `T` have the margin `2 M₁ L^{k+1}` in the top layer of
  `Gl`, then the coefficient of the step equals the formula `newLevelCoeffBg` on `Gl` at the read
  datum as soon as the determinant parts agree (`newLevelCoeffBg_class_eq_of_agree` with
  `zeroActBg_canon_eq`, `oldActBg_canon_eq`, `e1MarkGParamGBgOn_canon_eq`, `oldMarkGBg_canon_eq`).
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Fluctuation Balaban.Multiscale Balaban.Background Balaban.Localization
  Balaban.SmallField Balaban.LargeField Balaban.Polymer Finset MeasureTheory

section Sites

variable {d L N₁ m₁ k : ℕ} [NeZero L] [NeZero N₁] {Lb : Type*}

/-- **A label whose blocks lie in `T` lies in the sites of `T`.** -/
theorem ysite_subset_sitesOf (hN1 : L ^ 1 ∣ N₁)
    (Lab : CubeLabels (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) 1 (k + 1) Set.univ Lb)
    (y : Lb)
    {T : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) 1 (k + 1) Set.univ)}
    (h : blocksOf 1 (k + 1) Set.univ (Lab.ysite y) ⊆ T) : Lab.ysite y ⊆ sitesOf T := by
  have hs := ysite_subset_Yhat hN1 le_rfl isPiUnion_univ_aux Lab y h
  rwa [Yhat_univ] at hs

end Sites

section Radius

/-- `a m < δ` from `b m < δ`, `0 ≤ a ≤ b` and `δ > 0` (whatever the sign of `m`). -/
theorem mul_lt_of_le_of_mul_lt {a b m δ : ℝ} (hab : a ≤ b) (hb : b * m < δ) (hδ : 0 < δ)
    (ha : 0 ≤ a) : a * m < δ := by
  rcases le_or_gt 0 m with h | h
  · exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right hab h) hb
  · exact lt_of_le_of_lt (mul_nonpos_of_nonneg_of_nonpos ha h.le) hδ

end Radius

section ZeroSource

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ ϱm : ℝ}

/-- **The zero-source family of the direct terms is the formula `zeroActBg` at the step's own set.**
For a direct-terms record `I` (embedding `ψ ↦ (ψ, ψ)`, source radius `2`) whose terms at zero source
are the zero-source terms `zeroTermBg` of the step's own set (`hT`; the explicit clause of
`zeroSourceActivity_common_fromTowerG_core` is of this form by `zeroTermBg_self`), and the family
`A = labelActFamilyOn … I` over the parameters with the scaled inclusion: at a parameter `θ` whose
zero-source point lies in the parameter set `V` and whose datum lies in the chart, and `‖u‖ < 2`, the
zero-source family `zeroSourceAct A 2` is `zeroActBg` at the step's own set and transport. -/
theorem zeroSourceAct_labelActFamilyOn_H_eq (S : StepSetting d L N₁ m₁ k N ϱ) {m₀ : ℕ}
    {hp : 0 < S.p₁} {ρ εU a : ℝ}
    {Θ₀ : RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ)}
    {SΛ : Set (RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ))}
    {XW : Set (((S.U × Fin N → ℂ) × (S.U × Fin N → ℂ)) × ((S.U × Fin N → ℂ) × (S.U × Fin N → ℂ)))}
    {val : ((S.U × Fin N → ℂ) × (S.U × Fin N → ℂ)) → ((S.U × Fin N → ℂ) × (S.U × Fin N → ℂ)) →
      ℂ → RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) → ℂ}
    {AgΘ : Set (CTorus d L N₁ m₁ (k + 1)) →
      RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) →
      RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) → Prop}
    {AgF : Set (CTorus d L N₁ m₁ (k + 1)) → ((S.U × Fin N → ℂ) × (S.U × Fin N → ℂ)) →
      ((S.U × Fin N → ℂ) × (S.U × Fin N → ℂ)) → Prop}
    {I : DirectTerms S m₀ hp (fun ψ => (ψ, ψ)) ρ 2 εU a Θ₀ SΛ XW val AgΘ AgF}
    {V : Set (physParam N S)} {cs : ℂ} (hF : DirectTermsFamilyOn S m₀ (physInclScaled N S cs) I V)
    (hN : L ^ m₀ ∣ N₁) (hρ : 0 < ρ) (hεU : 0 ≤ εU) {κ0 Kc : ℝ} (hκ0 : aEnt d L + 1 ≤ κ0)
    (hKc : K0 d L κ0 ≤ Kc) {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}
    (X₁V : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) → Finset (CTorus d L N₁ m₁ (k + 1)))
    (jV : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) → ℕ)
    (𝒦XV : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) → Set (CTorus d L N₁ m₁ (k + 1)))
    (F₂ : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) →
      DecParams S.G' × RawData d L (N₁ * L ^ m₁) (k + 1) N →
        (S.G'.Ω 1 × Fin N → ℂ) × (S.G'.Ω 1 → ℂ))
    (Sol₂ : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) →
      Dec2.DecParams (coverOf S.G') × Edat Hm N → (Hm.Ω 1 × Fin N → ℂ) × (Hm.Ω 1 → ℂ))
    (ω : ℂ → ℂ)
    (hT : ∀ (Y : Set (CTorus d L N₁ m₁ (k + 1))) (x w : (S.U × Fin N → ℂ) × (S.U × Fin N → ℂ))
      (σ : ℂ) (Θ : RawData d L (N₁ * L ^ m₁) (k + 1) N),
      I.T Y x w σ (Θ, 0) =
        zeroTermBg S S.G' (BgTransport.self S.hG') X₁V jV 𝒦XV m₀ F₂ Sol₂ ω Y x.1 w.1 σ Θ)
    {eps : ℝ} (θ : physParam N S) (hθV : ((θ.1, 0) : physParam N S) ∈ V)
    (hθ : (θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) ∈
      XiCRaw S.G' (compWeight L S.a₁) S.ν (k + 1) 1 eps)
    {u : ℂ} (hu : ‖u‖ < 2) (Y : {Y // Y ∈ I.𝒴}) (Φ : ∀ b, (S.blockSplit m₀ hp).Ωb b) :
    (zeroSourceAct (labelActFamilyOn S m₀ (physInclScaled N S cs) I hF hN hρ zero_le_two hεU hκ0
        hKc) 2 zero_le_two θ u).H Y Φ =
      zeroActBg S S.G' (BgTransport.self S.hG') X₁V jV 𝒦XV m₀ F₂ Sol₂ ω ρ hp eps θ u Y.1 Φ := by
  have hJ : physInclScaled N S cs ((θ.1, 0) : physParam N S) =
      ((θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N), 0) := by
    rw [physInclScaled_apply]
    refine Prod.ext rfl (funext fun y => funext fun i => ?_)
    simp
  rw [zeroSourceAct_H, labelActFamilyOn_H S m₀ _ hF hN hρ zero_le_two hεU hκ0 hKc hθV hu, hJ,
    hT, sqFactor_of_lt hu]
  simp only [zeroActBg, hθ, hu, and_self, ↓reduceIte]

end ZeroSource

section Assembly

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ ϱm ϱl ϱl' ϱ₁ ϱ₂ : ℝ}

open Classical in
/-- **The replacement identity (A5) of a class on a local generating set, label by label** (P3
pp. 78-79, (4.44)-(4.47)).  Under the hypotheses of `newLevelCoeffBg_class_canon_eq_of_det_gen`
(without the determinant part), at the step's parameter `θ` with the datum `D` of the step chart and
the parameter `θ_b` of `Gl` with the read datum: the step's zero-source activities agree with
`zeroActBg` on `Gl`, the step's inherited activities with `oldActBg` on `Gl` (labels whose blocks
lie in `T`), and the step's marks with the bridge marks `e1MarkGParamGBgOn` and the marks
`oldMarkGBg` on `Gl` (anchors whose blocks lie in `T`), for `s ∈ [0, 1]`. -/
theorem newLevelCoeffBg_class_canon_agree (S : StepSetting d L N₁ m₁ k N ϱ)
    {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm} (hG : IsLevel Hm k)
    {Gl : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱl}
    {Gd : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱl'}
    (hA : CubeAligned Gl m₁) (hSS : SupSep Gl m₁) (hPd : Precedes Gd Gl)
    (hdk : Gd.Ω k = Gl.Ω k) (hdtop : Gd.Ω (k + 1) = ∅)
    (hN : 5 < N₁) (hm₁ : 2 ≤ m₁) (hM : 4 * L ^ 2 ≤ L ^ m₁)
    (hag : 2 * d * Real.log L ≤ agmonRate d / 16 * (ϱ - 1))
    (hagm : 2 * d * Real.log L ≤ agmonRate d / 16 * (ϱm - 1))
    (hagl : 2 * d * Real.log L ≤ agmonRate d / 16 * (ϱl - 1))
    (hagd : 2 * d * Real.log L ≤ agmonRate d / 16 * (ϱl' - 1))
    {c BG : ℝ} (hS : Dec2.DecSpecs d L (Dec2.mixedKc d L) (Cchi d L) c BG)
    (HB : BgHyp d L (k + 1) ϱ (compWeight L S.a₁) S.ν)
    (HB' : BgHyp d L (k + 1) ϱl (compWeight L S.a₁) S.ν)
    (ha₁ : 1 / 2 ≤ S.a₁) (ha₂ : S.a₁ ≤ 2)
    {κ : ℝ} (hκ : 0 < κ) (hMc : c * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    (hMX : Dec2.cstarX d L (Cchi d L) * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    {c₂ BG₂ : ℝ} (hF₂ : Dec2.FamSpec d L (Dec2.mixedKc d L) (Cchi d L) c₂ BG₂)
    (hM₂ : c₂ * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δ₀ δ₀' δ₁ : ℝ} (h0 : 0 ≤ δ₀) (h0' : 0 ≤ δ₀')
    (h1 : 0 < δ₁)
    (hδ₀ : δ₀ ≤ deltaStar' d L N (famConst d L BG₂ κ) (gamma1 d / 8))
    (hδ₀' : δ₀' ≤ deltaStar' d L N (famConst d L BG₂ κ) (gamma1 d / 8))
    (hδ₁ : δ₁ ≤ deltaStar' d L N (famConst d L BG₂ κ) (gamma1 d / 8))
    {eps eps₀ eps' : ℝ} (heps : 0 < eps) (hsmall : (4 * d + 6) * ((2 * d + 1) * eps) ≤ 1)
    (hc7 : xiC1 d * eps ≤ c7 d L N BG κ) (hphi : (3 + K4 d L N BG κ) * (xiC1 d * eps) < 1 / 2)
    (heps₀ : eps ≤ eps₀) (hεr : (2 * bgK1 d L N + 2) * xiC1 d * eps ≤ eps')
    (hsmall' : (4 * d + 6) * ((2 * d + 1) * eps') ≤ 1) (hc7' : xiC1 d * eps' ≤ c7 d L N BG κ)
    (hphi' : (3 + K4 d L N BG κ) * (xiC1 d * eps') < 1 / 2)
    (hδ₀a : 2 * (K4 d L N BG κ * (xiC1 d * eps)) ≤ δ₀)
    (hδ₀e : 2 * (K4 d L N BG κ * (xiC1 d * eps')) ≤ δ₀')
    {δc : ℝ} (hmarD' : decDomMargin d L N BG κ (xiC1 d * eps') < δc)
    (hαD' : K4 d L N BG κ * (xiC1 d * eps') < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4) {cψ ρ₀ ρ : ℝ} (hρ₀ : 0 < ρ₀) (hρ₀c : 2 * ρ₀ ≤ cψ)
    (hρ : 0 < ρ) (hp : 0 < S.p₁) {Ru : ℝ} (hRu1 : 17 / 16 ≤ Ru)
    (hRu : Ru * markedRad d L N k S.a₁ κ cψ ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) < δ₁)
    (hN1 : L ^ 1 ∣ N₁) (hL : 2 ≤ L)
    -- the zero-source part
    (𝒴₀ : Finset (Set (CTorus d L N₁ m₁ (k + 1)))) (h𝒴₀ : ∀ Y ∈ 𝒴₀, IsDj 1 (k + 1) Y)
    {X₁V : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) → Finset (CTorus d L N₁ m₁ (k + 1))}
    {jV : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) → ℕ}
    {XV 𝒦XV : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) → Set (CTorus d L N₁ m₁ (k + 1))}
    (hcovV : ∀ z, CovSetup S.G' 1 (jV z) (XV z) (𝒦XV z))
    (hX₁V : ∀ z, (↑(X₁V z) : Set (CTorus d L N₁ m₁ (k + 1))) = X1 S.G' 1 (jV z) (𝒦XV z))
    (hzXV : ∀ z, ∀ x ∈ blockSites d L N₁ m₁ (k + 1) k z, x ∈ X1 S.G' 1 (jV z) (𝒦XV z))
    {F₂ : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) →
      Dec2.DecParams (coverOf S.G') × RawData d L (N₁ * L ^ m₁) (k + 1) N →
        (S.G'.Ω 1 × Fin N → ℂ) × (S.G'.Ω 1 → ℂ)}
    {F₂' : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) →
      Dec2.DecParams (coverOf Gl) × RawData d L (N₁ * L ^ m₁) (k + 1) N →
        (Gl.Ω 1 × Fin N → ℂ) × (Gl.Ω 1 → ℂ)}
    (hF₂s : ∀ z (s : Dec2.DecParams (coverOf S.G')) (D : BgData S.G' N),
      (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC S.G' (bgC0 d L N) (c7 d L N BG κ) S.ν D → ∀ (φ : S.G'.Ω 1 × Fin N → ℂ)
        (α : S.G'.Ω 1 → ℂ), Dec2.IsDecBg (coverOf S.G') S.G' (compWeight L S.a₁) S.ν
          (rho4 d L N BG κ) s D φ α → F₂ z (s, rawOf D) = (φ, α))
    (hF₂s' : ∀ z (s : Dec2.DecParams (coverOf Gl)) (D : BgData Gl N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC Gl (bgC0 d L N) (c7 d L N BG κ) S.ν D → ∀ (φ : Gl.Ω 1 × Fin N → ℂ)
        (α : Gl.Ω 1 → ℂ), Dec2.IsDecBg (coverOf Gl) Gl (compWeight L S.a₁) S.ν
          (rho4 d L N BG κ) s D φ α → F₂' z (s, rawOf D) = (φ, α))
    {Sol₂ : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) →
      Dec2.DecParams (coverOf S.G') × Edat Hm N → (Hm.Ω 1 × Fin N → ℂ) × (Hm.Ω 1 → ℂ)}
    {Sol₂' : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) →
      Dec2.DecParams (coverOf Gl) × Edat Gd N → (Gd.Ω 1 × Fin N → ℂ) × (Gd.Ω 1 → ℂ)}
    (hSol₂ : ∀ z (p : Dec2.DecParams (coverOf S.G') × Edat Hm N), (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM Hm N false δ₀ δ₁ p.2 →
        (Sol₂ z p).1 = dphi Hm (Dec2.decG (coverOf S.G') Hm (compWeight L S.a₁) S.ν p.1) p.2.2.1
          p.2.1 (pertSource Hm (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) (Sol₂ z p).2 ∧
        Dec2.DecFixed (coverOf S.G') Hm (compWeight L S.a₁) S.ν p.1 false p.2.2.1 p.2.1
          (pertSource Hm (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) (Sol₂ z p).2 ∧
        Small Hm (Sol₂ z p).2 (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
        Small Hm (Sol₂ z p).2 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        SupBounds Hm (Sol₂ z p).1 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        (∀ δα' : Hm.Ω 1 → ℂ, Small Hm δα' (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf S.G') Hm (compWeight L S.a₁) S.ν p.1 false p.2.2.1 p.2.1
            (pertSource Hm (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol₂ z p).2))
    (hSol₂' : ∀ z (p : Dec2.DecParams (coverOf Gl) × Edat Gd N), (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM Gd N false δ₀' δ₁ p.2 →
        (Sol₂' z p).1 = dphi Gd (Dec2.decG (coverOf Gl) Gd (compWeight L S.a₁) S.ν p.1) p.2.2.1
          p.2.1 (pertSource Gd (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) (Sol₂' z p).2 ∧
        Dec2.DecFixed (coverOf Gl) Gd (compWeight L S.a₁) S.ν p.1 false p.2.2.1 p.2.1
          (pertSource Gd (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) (Sol₂' z p).2 ∧
        Small Gd (Sol₂' z p).2 (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
        Small Gd (Sol₂' z p).2 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        SupBounds Gd (Sol₂' z p).1 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        (∀ δα' : Gd.Ω 1 → ℂ, Small Gd δα' (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf Gl) Gd (compWeight L S.a₁) S.ν p.1 false p.2.2.1 p.2.1
            (pertSource Gd (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol₂' z p).2))
    (ω : ℂ → ℂ)
    -- the old terms
    {ι : Type*} [Fintype ι] {m₀ : ℕ} (hNm : L ^ m₀ ∣ N₁)
    {X₁f : ι → Finset (CTorus d L N₁ m₁ (k + 1))} {jL : ι → ℕ}
    {XL 𝒦X : ι → Set (CTorus d L N₁ m₁ (k + 1))}
    (hcovL : ∀ τ, CovSetup S.G' m₀ (jL τ) (XL τ) (𝒦X τ))
    (hX₁L : ∀ τ, (↑(X₁f τ) : Set (CTorus d L N₁ m₁ (k + 1))) = X1 S.G' m₀ (jL τ) (𝒦X τ))
    (Gk : ι → GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ₁)
    (Gj : ι → GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ₂)
    (hkX : ∀ τ, ∀ x ∈ dataSites (Gk τ), x ∈ X1 S.G' m₀ (jL τ) (𝒦X τ)) (ac : ℕ → ℝ)
    (Fk : ∀ τ, RawData d L (N₁ * L ^ m₁) (k + 1) N → ((Gk τ).Ω 1 × Fin N → ℂ) × ((Gk τ).Ω 1 → ℂ))
    (E : ι → RawData d L (N₁ * L ^ m₁) (k + 1) N → ℂ)
    -- the constants of the decoupling pairs of the old terms
    {cL BGL : ℝ} (hSL : Dec2.DecSpecs d L (Dec2.mixedKc d L) (Cchi d L) cL BGL)
    {κL : ℝ} (hκL : 0 < κL) (hMcL : cL * Real.exp (N0 d L * κL) ≤ (L : ℝ) ^ m₁)
    (hMXL : Dec2.cstarX d L (Cchi d L) * Real.exp (N0 d L * κL) ≤ (L : ℝ) ^ m₁)
    {c₂L BG₂L : ℝ} (hF₂L : Dec2.FamSpec d L (Dec2.mixedKc d L) (Cchi d L) c₂L BG₂L)
    (hM₂L : c₂L * Real.exp (N0 d L * κL) ≤ (L : ℝ) ^ m₁) {δ₀L δ₀L' δ₁L : ℝ} (h0L : 0 ≤ δ₀L)
    (h0L' : 0 ≤ δ₀L') (h1L : 0 < δ₁L)
    (hδ₀L : δ₀L ≤ deltaStar' d L N (famConst d L BG₂L κL) (gamma1 d / 8))
    (hδ₀L' : δ₀L' ≤ deltaStar' d L N (famConst d L BG₂L κL) (gamma1 d / 8))
    (hδ₁L : δ₁L ≤ deltaStar' d L N (famConst d L BG₂L κL) (gamma1 d / 8))
    (hc7L : xiC1 d * eps ≤ c7 d L N BGL κL)
    (hphiL : (3 + K4 d L N BGL κL) * (xiC1 d * eps) < 1 / 2)
    (hc7L' : xiC1 d * eps' ≤ c7 d L N BGL κL)
    (hphiL' : (3 + K4 d L N BGL κL) * (xiC1 d * eps') < 1 / 2)
    (hδ₀aL : 2 * (K4 d L N BGL κL * (xiC1 d * eps)) ≤ δ₀L)
    (hδ₀eL : 2 * (K4 d L N BGL κL * (xiC1 d * eps')) ≤ δ₀L')
    {δcL : ℝ} (hmarDL' : decDomMargin d L N BGL κL (xiC1 d * eps') < δcL)
    (hαDL' : K4 d L N BGL κL * (xiC1 d * eps') < coerciveConst d / 2)
    (hsmL : δcL ^ 2 * smallConstX d L κL ≤ 1 / 4) {cψL : ℝ} (hρcL : ρ ≤ cψL)
    (hRuL : Ru * markedRad d L N k S.a₁ κL cψL ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) < δ₁L)
    {F₁L : ι → Dec2.DecParams (coverOf S.G') × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      (S.G'.Ω 1 × Fin N → ℂ) × (S.G'.Ω 1 → ℂ)}
    {F₁L' : ι → Dec2.DecParams (coverOf Gl) × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      (Gl.Ω 1 × Fin N → ℂ) × (Gl.Ω 1 → ℂ)}
    (hF₁L : ∀ τ (s : Dec2.DecParams (coverOf S.G')) (D : BgData S.G' N),
      (∀ P, ‖s P‖ < Real.exp κL) →
      InUnionDomainC S.G' (bgC0 d L N) (c7 d L N BGL κL) S.ν D → ∀ (φ : S.G'.Ω 1 × Fin N → ℂ)
        (α : S.G'.Ω 1 → ℂ), Dec2.IsDecBg (coverOf S.G') S.G' (compWeight L S.a₁) S.ν
          (rho4 d L N BGL κL) s D φ α → F₁L τ (s, rawOf D) = (φ, α))
    (hF₁L' : ∀ τ (s : Dec2.DecParams (coverOf Gl)) (D : BgData Gl N), (∀ P, ‖s P‖ < Real.exp κL) →
      InUnionDomainC Gl (bgC0 d L N) (c7 d L N BGL κL) S.ν D → ∀ (φ : Gl.Ω 1 × Fin N → ℂ)
        (α : Gl.Ω 1 → ℂ), Dec2.IsDecBg (coverOf Gl) Gl (compWeight L S.a₁) S.ν
          (rho4 d L N BGL κL) s D φ α → F₁L' τ (s, rawOf D) = (φ, α))
    {SolL : ι → Dec2.DecParams (coverOf S.G') × Edat Hm N → (Hm.Ω 1 × Fin N → ℂ) × (Hm.Ω 1 → ℂ)}
    {SolL' : ι → Dec2.DecParams (coverOf Gl) × Edat Gd N → (Gd.Ω 1 × Fin N → ℂ) × (Gd.Ω 1 → ℂ)}
    (hSolL : ∀ τ (p : Dec2.DecParams (coverOf S.G') × Edat Hm N), (∀ P, ‖p.1 P‖ < Real.exp κL) →
      StrictDataM Hm N false δ₀L δ₁L p.2 →
        (SolL τ p).1 = dphi Hm (Dec2.decG (coverOf S.G') Hm (compWeight L S.a₁) S.ν p.1) p.2.2.1
          p.2.1 (pertSource Hm (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) (SolL τ p).2 ∧
        Dec2.DecFixed (coverOf S.G') Hm (compWeight L S.a₁) S.ν p.1 false p.2.2.1 p.2.1
          (pertSource Hm (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) (SolL τ p).2 ∧
        Small Hm (SolL τ p).2 (c6' d L N (famConst d L BG₂L κL) (gamma1 d / 8)) ∧
        Small Hm (SolL τ p).2 (cK2' d L N (famConst d L BG₂L κL) * δ₁L) ∧
        SupBounds Hm (SolL τ p).1 (cK2' d L N (famConst d L BG₂L κL) * δ₁L) ∧
        (∀ δα' : Hm.Ω 1 → ℂ, Small Hm δα' (c6' d L N (famConst d L BG₂L κL) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf S.G') Hm (compWeight L S.a₁) S.ν p.1 false p.2.2.1 p.2.1
            (pertSource Hm (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (SolL τ p).2))
    (hSolL' : ∀ τ (p : Dec2.DecParams (coverOf Gl) × Edat Gd N), (∀ P, ‖p.1 P‖ < Real.exp κL) →
      StrictDataM Gd N false δ₀L' δ₁L p.2 →
        (SolL' τ p).1 = dphi Gd (Dec2.decG (coverOf Gl) Gd (compWeight L S.a₁) S.ν p.1) p.2.2.1
          p.2.1 (pertSource Gd (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) (SolL' τ p).2 ∧
        Dec2.DecFixed (coverOf Gl) Gd (compWeight L S.a₁) S.ν p.1 false p.2.2.1 p.2.1
          (pertSource Gd (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) (SolL' τ p).2 ∧
        Small Gd (SolL' τ p).2 (c6' d L N (famConst d L BG₂L κL) (gamma1 d / 8)) ∧
        Small Gd (SolL' τ p).2 (cK2' d L N (famConst d L BG₂L κL) * δ₁L) ∧
        SupBounds Gd (SolL' τ p).1 (cK2' d L N (famConst d L BG₂L κL) * δ₁L) ∧
        (∀ δα' : Gd.Ω 1 → ℂ, Small Gd δα' (c6' d L N (famConst d L BG₂L κL) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf Gl) Gd (compWeight L S.a₁) S.ν p.1 false p.2.2.1 p.2.1
            (pertSource Gd (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (SolL' τ p).2))
    (𝒴C : Finset (Set (CTorus d L N₁ m₁ (k + 1)))) (h𝒴C : ∀ Y ∈ 𝒴C, IsDj 1 (k + 1) Y)
    (hdomC : ∀ τ, ∀ Y ∈ polyDom S.G' (X₁f τ) m₀ (jL τ) (𝒦X τ), IsDj 1 (k + 1) Y)
    -- the bridge marks
    {F₁b : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) →
      Dec2.DecParams (coverOf S.G') × RawData d L (N₁ * L ^ m₁) (k + 1) N →
        (S.G'.Ω 1 × Fin N → ℂ) × (S.G'.Ω 1 → ℂ)}
    {F₁b' : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) →
      Dec2.DecParams (coverOf Gl) × RawData d L (N₁ * L ^ m₁) (k + 1) N →
        (Gl.Ω 1 × Fin N → ℂ) × (Gl.Ω 1 → ℂ)}
    (hF₁b : ∀ b (s : Dec2.DecParams (coverOf S.G')) (D : BgData S.G' N),
      (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC S.G' (bgC0 d L N) (c7 d L N BG κ) S.ν D → ∀ (φ : S.G'.Ω 1 × Fin N → ℂ)
        (α : S.G'.Ω 1 → ℂ), Dec2.IsDecBg (coverOf S.G') S.G' (compWeight L S.a₁) S.ν
          (rho4 d L N BG κ) s D φ α → F₁b b (s, rawOf D) = (φ, α))
    (hF₁b' : ∀ b (s : Dec2.DecParams (coverOf Gl)) (D : BgData Gl N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC Gl (bgC0 d L N) (c7 d L N BG κ) S.ν D → ∀ (φ : Gl.Ω 1 × Fin N → ℂ)
        (α : Gl.Ω 1 → ℂ), Dec2.IsDecBg (coverOf Gl) Gl (compWeight L S.a₁) S.ν
          (rho4 d L N BG κ) s D φ α → F₁b' b (s, rawOf D) = (φ, α))
    {Solb : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) →
      Dec2.DecParams (coverOf S.G') × Edat Hm N → (Hm.Ω 1 × Fin N → ℂ) × (Hm.Ω 1 → ℂ)}
    {Solb' : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) →
      Dec2.DecParams (coverOf Gl) × Edat Gd N → (Gd.Ω 1 × Fin N → ℂ) × (Gd.Ω 1 → ℂ)}
    (hSolb : ∀ b (p : Dec2.DecParams (coverOf S.G') × Edat Hm N), (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM Hm N false δ₀ δ₁ p.2 →
        (Solb b p).1 = dphi Hm (Dec2.decG (coverOf S.G') Hm (compWeight L S.a₁) S.ν p.1) p.2.2.1
          p.2.1 (pertSource Hm (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) (Solb b p).2 ∧
        Dec2.DecFixed (coverOf S.G') Hm (compWeight L S.a₁) S.ν p.1 false p.2.2.1 p.2.1
          (pertSource Hm (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) (Solb b p).2 ∧
        Small Hm (Solb b p).2 (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
        Small Hm (Solb b p).2 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        SupBounds Hm (Solb b p).1 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        (∀ δα' : Hm.Ω 1 → ℂ, Small Hm δα' (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf S.G') Hm (compWeight L S.a₁) S.ν p.1 false p.2.2.1 p.2.1
            (pertSource Hm (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Solb b p).2))
    (hSolb' : ∀ b (p : Dec2.DecParams (coverOf Gl) × Edat Gd N), (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM Gd N false δ₀' δ₁ p.2 →
        (Solb' b p).1 = dphi Gd (Dec2.decG (coverOf Gl) Gd (compWeight L S.a₁) S.ν p.1) p.2.2.1
          p.2.1 (pertSource Gd (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) (Solb' b p).2 ∧
        Dec2.DecFixed (coverOf Gl) Gd (compWeight L S.a₁) S.ν p.1 false p.2.2.1 p.2.1
          (pertSource Gd (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) (Solb' b p).2 ∧
        Small Gd (Solb' b p).2 (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
        Small Gd (Solb' b p).2 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        SupBounds Gd (Solb' b p).1 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        (∀ δα' : Gd.Ω 1 → ℂ, Small Gd δα' (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf Gl) Gd (compWeight L S.a₁) S.ν p.1 false p.2.2.1 p.2.1
            (pertSource Gd (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Solb' b p).2))
    (z : RootIdx d L N₁ m₁ (k + 1)) (hdomE : ∀ b, ∀ Y ∈ e1DomG S b, IsDj 1 (k + 1) Y)
    -- the step's class family and marks
    {ε₀ ε₁ κH κ0 K₀ K₁ : ℝ}
    (A₀ : physParam N S → ℂ →
      LabelAct (thickLabels (m₀ := 1) (j := k + 1) 𝒴₀ h𝒴₀) (S.blockSplit 1 hp).Ωb ε₀ κH κ0 K₀)
    (AC : physParam N S → ℂ →
      LabelAct (thickLabels (m₀ := 1) (j := k + 1) 𝒴C h𝒴C) (S.blockSplit 1 hp).Ωb ε₁ κH κ0 K₁)
    (y1 : {q // q ∈ markedIdx (fun _ => (Set.univ : Set (CTorus d L N₁ m₁ (k + 1))))
        (fun τ => polyDom S.G' (X₁f τ) m₀ (jL τ) (𝒦X τ)) z} →
      ({Y // Y ∈ 𝒴₀} ⊕ ({Y // Y ∈ 𝒴C} ⊕ RootUnionLb 1
        (fun _ => (Set.univ : Set (CTorus d L N₁ m₁ (k + 1))))
        (fun τ => polyDom S.G' (X₁f τ) m₀ (jL τ) (𝒦X τ)))) ⊕
        RootUnionLb 1 (fun _ => (Set.univ : Set (CTorus d L N₁ m₁ (k + 1)))) (e1DomG S))
    (hy1 : ∀ q, (commonLabels ((thickLabels (m₀ := 1) (j := k + 1) 𝒴₀ h𝒴₀).sum
        (commonLabels (thickLabels (m₀ := 1) (j := k + 1) 𝒴C h𝒴C) hN1 hL (fun _ => Set.univ)
          (fun τ => polyDom S.G' (X₁f τ) m₀ (jL τ) (𝒦X τ)) hdomC)) hN1 hL (fun _ => Set.univ)
        (e1DomG S) hdomE).ysite (y1 q) = bridge 1 z q.1.2)
    (G₁ : physParam N S →
      {q // q ∈ markedIdx (fun _ => (Set.univ : Set (CTorus d L N₁ m₁ (k + 1))))
        (fun τ => polyDom S.G' (X₁f τ) m₀ (jL τ) (𝒦X τ)) z} →
      ℂ → (∀ b, (S.blockSplit 1 hp).Ωb b) → ℂ)
    -- the read datum
    {D : BgData S.G' N} (hD : XiCData S.G' (compWeight L S.a₁) S.ν (k + 1) 1 eps D)
    (θ : physParam N S) (hθ : (θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) = rawOf D)
    (θb : physParamBg N Gl)
    (hθb : (θb.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) = clipRaw Gl (rawOf D))
    -- the step's activities and marks are the formulas at the step's own set
    (h0eq : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ Y Φ, (A₀ θ (s : ℂ)).H Y Φ =
      zeroActBg S S.G' (BgTransport.self S.hG') X₁V jV 𝒦XV 1 F₂ Sol₂ ω ρ₀ hp eps₀ θ (s : ℂ) Y.1 Φ)
    (h1eq : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ Y Φ, (AC θ (s : ℂ)).H Y Φ =
      oldActBg S S.G' (BgTransport.self S.hG') (S.blockU z) X₁f m₀ jL 𝒦X F₁L SolL
        (fun τ => eTermFun S.G' (Gk τ) (Gj τ) Hm ac (Fk τ) (E τ)) ρ hp Ru eps₀ 𝒴C θ Y (s : ℂ) Φ)
    (hG₁eq : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ q Φ, G₁ θ q (s : ℂ) Φ =
      oldMarkGBg S S.G' (BgTransport.self S.hG') (S.blockU z) X₁f m₀ jL 𝒦X F₁L SolL
        (fun τ => eTermFun S.G' (Gk τ) (Gj τ) Hm ac (Fk τ) (E τ)) ρ hp Ru eps₀ z θ q (s : ℂ) Φ)
    -- the polymer and its margin
    (T : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) 1 (k + 1) Set.univ))
    (hTmar : ∀ x ∈ sitesOf T, ∀ y, supDist x y ≤ 2 * L ^ (k + 1 + m₁) → y ∈ Gl.Ω (k + 1)) :
    (∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ Y,
      blocksOf 1 (k + 1) Set.univ ((thickLabels (m₀ := 1) (j := k + 1) 𝒴₀ h𝒴₀).ysite Y) ⊆ T →
      (A₀ θ (s : ℂ)).H Y = fun Φ => zeroActBg S Gl (BgTransport.canon S.G' Gl N) X₁V jV 𝒦XV 1
        F₂' Sol₂' ω ρ₀ hp eps' θb (s : ℂ) Y.1 Φ) ∧
    (∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ Y,
      blocksOf 1 (k + 1) Set.univ ((thickLabels (m₀ := 1) (j := k + 1) 𝒴C h𝒴C).ysite Y) ⊆ T →
      (AC θ (s : ℂ)).H Y = fun Φ => oldActBg S Gl (BgTransport.canon S.G' Gl N)
        (maskPre S.hG' Gl (S.blockU z)) X₁f m₀ jL 𝒦X F₁L' SolL'
        (fun τ => eTermFun Gl (Gk τ) (Gj τ) Gd ac (Fk τ) (E τ)) ρ hp Ru eps' 𝒴C θb Y (s : ℂ) Φ) ∧
    (∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ i,
      blocksOf 1 (k + 1) Set.univ
        ((commonLabels ((thickLabels (m₀ := 1) (j := k + 1) 𝒴₀ h𝒴₀).sum
          (commonLabels (thickLabels (m₀ := 1) (j := k + 1) 𝒴C h𝒴C) hN1 hL (fun _ => Set.univ)
            (fun τ => polyDom S.G' (X₁f τ) m₀ (jL τ) (𝒦X τ)) hdomC)) hN1 hL (fun _ => Set.univ)
          (e1DomG S) hdomE).ysite
          (Sum.elim (commonAnchor ({Y // Y ∈ 𝒴₀} ⊕ ({Y // Y ∈ 𝒴C} ⊕ RootUnionLb 1
            (fun _ => (Set.univ : Set (CTorus d L N₁ m₁ (k + 1))))
            (fun τ => polyDom S.G' (X₁f τ) m₀ (jL τ) (𝒦X τ)))) (fun _ => Set.univ) (e1DomG S) z)
            y1 i)) ⊆ T →
      Sum.elim (fun i u Φ => e1MarkGParamG S F₁b Solb ρ₀ hp z eps₀ θ i u Φ) (G₁ θ) i (s : ℂ) =
        Sum.elim
          (fun i u Φ => e1MarkGParamGBgOn S Gl (BgTransport.canon S.G' Gl N)
            (maskPre S.hG' Gl (S.blockU z)) F₁b' Solb' ρ₀ hp z Gl eps' θb i u Φ)
          (oldMarkGBg S Gl (BgTransport.canon S.G' Gl N) (maskPre S.hG' Gl (S.blockU z)) X₁f m₀ jL
            𝒦X F₁L' SolL' (fun τ => eTermFun Gl (Gk τ) (Gj τ) Gd ac (Fk τ) (E τ)) ρ hp Ru eps' z
            θb) i (s : ℂ)) := by
  classical
  -- the radius conditions of the three kinds of terms
  have hmR : markedRad d L N k S.a₁ κ cψ ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) < δ₁ := by
    have h := mul_lt_of_le_of_mul_lt (show (1 : ℝ) ≤ Ru by linarith) hRu h1 zero_le_one
    rwa [one_mul] at h
  have hmR17 : (17 / 16 : ℝ) *
      markedRad d L N k S.a₁ κ cψ ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) < δ₁ :=
    mul_lt_of_le_of_mul_lt hRu1 hRu h1 (by norm_num)
  -- labels inside `T` have the margin
  have hmar : ∀ Y : Set (CTorus d L N₁ m₁ (k + 1)), Y ⊆ sitesOf T →
      ∀ x ∈ Y, ∀ y, supDist x y ≤ 2 * L ^ (k + 1 + m₁) → y ∈ Gl.Ω (k + 1) :=
    fun Y hY x hx => hTmar x (hY hx)
  -- the read conditions of an old label
  have hXYL : ∀ τ (Y : Set (CTorus d L N₁ m₁ (k + 1))),
      Y ∈ polyDom S.G' (X₁f τ) m₀ (jL τ) (𝒦X τ) → ∀ P ∈ cubeIdx S.G',
      ¬ Disjoint (Pset m₁ P) (↑(X₁f τ) : Set (CTorus d L N₁ m₁ (k + 1))) → ∀ y ∈ Pset m₁ P, y ∈ Y :=
    fun τ Y hY P hP hdis y hy => by
      rw [hX₁L τ] at hdis
      exact subset_polyDom hY (Pset_subset_of_not_disjoint (hcovL τ).polySetup hP hdis hy)
  have hkYL : ∀ τ (Y : Set (CTorus d L N₁ m₁ (k + 1))),
      Y ∈ polyDom S.G' (X₁f τ) m₀ (jL τ) (𝒦X τ) → ∀ x ∈ dataSites (Gk τ), x ∈ Y :=
    fun τ Y hY x hx => subset_polyDom hY (hkX τ x hx)
  refine ⟨fun s hs Y hY => ?_, fun s hs Y hY => ?_, fun s hs i hi => ?_⟩
  · -- the zero-source activities
    have hYs := ysite_subset_sitesOf hN1 (thickLabels (m₀ := 1) (j := k + 1) 𝒴₀ h𝒴₀) Y hY
    funext Φ
    rw [h0eq s hs Y Φ]
    exact (zeroActBg_canon_eq S hG hA hSS hPd hdk hdtop hN hm₁ hM hag hagm hagl hagd hS HB HB' ha₁
      ha₂ hκ hMc hMX hF₂s hF₂s' hF₂ hM₂ h0 h0' h1 hδ₀ hδ₀' hδ₁ hSol₂ hSol₂' heps hsmall hc7 hphi
      heps₀ hεr hsmall' hc7' hphi' hδ₀a hδ₀e hmarD' hαD' hsm hρ₀ hρ₀c hmR hp hcovV hX₁V hzXV ω Y.1
      (hmar Y.1 hYs) hD θ hθ θb hθb (s : ℂ) Φ).symm
  · -- the inherited activities
    have hYs := ysite_subset_sitesOf hN1 (thickLabels (m₀ := 1) (j := k + 1) 𝒴C h𝒴C) Y hY
    funext Φ
    rw [h1eq s hs Y Φ]
    exact (oldActBg_canon_eq S hG hA hSS hPd hdk hdtop hN hm₁ hM hag hagm hagl hagd hSL HB HB' ha₁
      ha₂ hκL hMcL hMXL hF₁L hF₁L' hF₂L hM₂L h0L h0L' h1L hδ₀L hδ₀L' hδ₁L hSolL hSolL' Gk Gj ac Fk
      E heps hsmall hc7L hphiL heps₀ hεr hsmall' hc7L' hphiL' hδ₀aL hδ₀eL hmarDL' hαDL' hsmL hρ hρcL hp
      hRuL X₁f m₀
      jL 𝒦X (layerUnion_of_isLevel S.hG' m₀) hNm (S.blockU z) 𝒴C Y (fun τ hτ => hXYL τ Y.1 hτ)
      (fun τ hτ => hkYL τ Y.1 hτ) (hmar Y.1 hYs) hD θ hθ θb hθb (s : ℂ) Φ).symm
  · -- the marks
    have hYs := ysite_subset_sitesOf hN1 _ _ hi
    rcases i with i | q
    · funext Φ
      exact (e1MarkGParamGBgOn_canon_eq S hG hA hSS hPd hdk hdtop hN hm₁ hM hag hagm hagl hagd hS
        HB HB' ha₁ ha₂ hκ hMc hMX hF₁b hF₁b' hF₂ hM₂ h0 h0' h1 hδ₀ hδ₀' hδ₁ hSolb hSolb' heps
        hsmall hc7 hphi heps₀ hεr hsmall' hc7' hphi' hδ₀a hδ₀e hmarD' hαD' hsm hρ₀
        (by linarith) hp hmR17 hN1 z i (hmar i.1 hYs) hD θ hθ θb hθb (s : ℂ) Φ).symm
    · funext Φ
      have hq := (mem_markedIdx (b := q.1.1) (Y := q.1.2)).1 q.2 |>.1
      have hbr : q.1.2 ⊆ sitesOf T := by
        have h' : bridge 1 z q.1.2 ⊆ sitesOf T := by
          rw [← hy1 q]
          exact hYs
        exact (subset_bridge z q.1.2).trans h'
      show G₁ θ q (s : ℂ) Φ = _
      rw [hG₁eq s hs q Φ]
      exact (oldMarkGBg_canon_eq S hG hA hSS hPd hdk hdtop hN hm₁ hM hag hagm hagl hagd hSL HB HB'
        ha₁ ha₂ hκL hMcL hMXL hF₁L hF₁L' hF₂L hM₂L h0L h0L' h1L hδ₀L hδ₀L' hδ₁L hSolL hSolL' Gk Gj
        ac Fk E heps hsmall hc7L hphiL heps₀ hεr hsmall' hc7L' hphiL' hδ₀aL hδ₀eL hmarDL' hαDL' hsmL hρ
        hρcL hp hRuL X₁f m₀
        jL 𝒦X (layerUnion_of_isLevel S.hG' m₀) hNm (S.blockU z) z q (hXYL q.1.1 q.1.2 hq)
        (hkYL q.1.1 q.1.2 hq) (hmar q.1.2 hbr) hD θ hθ θb hθb (s : ℂ) Φ).symm

open Classical in
/-- **The replacement identity (A5) of the coefficient of a class on a local generating set,
reduced to the determinant part, core** (P3 pp. 78-79, (4.44)-(4.47)).  Let `Gl` be cube aligned and
sup-separated, `Gd ≺ Gl` with the layer `k` of `Gl` and no layer `k + 1`, and let the decoupling maps
of the step and of `(Gl, Gd)` be given by their specifications: per block for the zero-source terms
(`F₂`, `Sol₂`; `F₂'`, `Sol₂'`) and for the bridge marks (`F₁b`, `Solb`; `F₁b'`, `Solb'`), per old term
(`F₁L`, `SolL`; `F₁L'`, `SolL'`).  Let `θ` be the step's parameter with the datum `D` of the step
chart and `θ_b` the parameter of `Gl` with the read datum.  If the step's class family
`commonAct (A₀.sum (commonAct A_C …))` and its marks are the formulas at the step's own set at `θ`
(`h0eq`, `h1eq`, `hG₁eq`; the bridge marks are `e1MarkGParamG`), the marks are local (`hGdep`), and
the sites of `T` have the margin `2 M₁ L^{k+1}` in the top layer of `Gl`, then the coefficient of the
step (determinant part plus `gsumCoeff`) equals the formula `newLevelCoeffBg` on `Gl` at `θ_b` with
the recomputed activities and marks, when the determinant parts agree.  The conditions on `ε′`,
`Ru` and the radii are smallness conditions against absolute constants.  The
decoupling pairs of the old terms have their own constants (`κL`, `BGL`, `BG₂L`, `δ₀L`, `δ₁L`, …);
`newLevelCoeffBg_class_canon_eq_of_det` is the instance with the constants of the zero-source terms. -/
theorem newLevelCoeffBg_class_canon_eq_of_det_gen (S : StepSetting d L N₁ m₁ k N ϱ)
    {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm} (hG : IsLevel Hm k)
    {Gl : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱl}
    {Gd : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱl'}
    (hA : CubeAligned Gl m₁) (hSS : SupSep Gl m₁) (hPd : Precedes Gd Gl)
    (hdk : Gd.Ω k = Gl.Ω k) (hdtop : Gd.Ω (k + 1) = ∅)
    (hN : 5 < N₁) (hm₁ : 2 ≤ m₁) (hM : 4 * L ^ 2 ≤ L ^ m₁)
    (hag : 2 * d * Real.log L ≤ agmonRate d / 16 * (ϱ - 1))
    (hagm : 2 * d * Real.log L ≤ agmonRate d / 16 * (ϱm - 1))
    (hagl : 2 * d * Real.log L ≤ agmonRate d / 16 * (ϱl - 1))
    (hagd : 2 * d * Real.log L ≤ agmonRate d / 16 * (ϱl' - 1))
    {c BG : ℝ} (hS : Dec2.DecSpecs d L (Dec2.mixedKc d L) (Cchi d L) c BG)
    (HB : BgHyp d L (k + 1) ϱ (compWeight L S.a₁) S.ν)
    (HB' : BgHyp d L (k + 1) ϱl (compWeight L S.a₁) S.ν)
    (ha₁ : 1 / 2 ≤ S.a₁) (ha₂ : S.a₁ ≤ 2)
    {κ : ℝ} (hκ : 0 < κ) (hMc : c * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    (hMX : Dec2.cstarX d L (Cchi d L) * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    {c₂ BG₂ : ℝ} (hF₂ : Dec2.FamSpec d L (Dec2.mixedKc d L) (Cchi d L) c₂ BG₂)
    (hM₂ : c₂ * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δ₀ δ₀' δ₁ : ℝ} (h0 : 0 ≤ δ₀) (h0' : 0 ≤ δ₀')
    (h1 : 0 < δ₁)
    (hδ₀ : δ₀ ≤ deltaStar' d L N (famConst d L BG₂ κ) (gamma1 d / 8))
    (hδ₀' : δ₀' ≤ deltaStar' d L N (famConst d L BG₂ κ) (gamma1 d / 8))
    (hδ₁ : δ₁ ≤ deltaStar' d L N (famConst d L BG₂ κ) (gamma1 d / 8))
    {eps eps₀ eps' : ℝ} (heps : 0 < eps) (hsmall : (4 * d + 6) * ((2 * d + 1) * eps) ≤ 1)
    (hc7 : xiC1 d * eps ≤ c7 d L N BG κ) (hphi : (3 + K4 d L N BG κ) * (xiC1 d * eps) < 1 / 2)
    (heps₀ : eps ≤ eps₀) (hεr : (2 * bgK1 d L N + 2) * xiC1 d * eps ≤ eps')
    (hsmall' : (4 * d + 6) * ((2 * d + 1) * eps') ≤ 1) (hc7' : xiC1 d * eps' ≤ c7 d L N BG κ)
    (hphi' : (3 + K4 d L N BG κ) * (xiC1 d * eps') < 1 / 2)
    (hδ₀a : 2 * (K4 d L N BG κ * (xiC1 d * eps)) ≤ δ₀)
    (hδ₀e : 2 * (K4 d L N BG κ * (xiC1 d * eps')) ≤ δ₀')
    {δc : ℝ} (hmarD' : decDomMargin d L N BG κ (xiC1 d * eps') < δc)
    (hαD' : K4 d L N BG κ * (xiC1 d * eps') < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4) {cψ ρ₀ ρ : ℝ} (hρ₀ : 0 < ρ₀) (hρ₀c : 2 * ρ₀ ≤ cψ)
    (hρ : 0 < ρ) (hp : 0 < S.p₁) {Ru : ℝ} (hRu1 : 17 / 16 ≤ Ru)
    (hRu : Ru * markedRad d L N k S.a₁ κ cψ ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) < δ₁)
    (hN1 : L ^ 1 ∣ N₁) (hL : 2 ≤ L)
    -- the zero-source part
    (𝒴₀ : Finset (Set (CTorus d L N₁ m₁ (k + 1)))) (h𝒴₀ : ∀ Y ∈ 𝒴₀, IsDj 1 (k + 1) Y)
    {X₁V : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) → Finset (CTorus d L N₁ m₁ (k + 1))}
    {jV : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) → ℕ}
    {XV 𝒦XV : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) → Set (CTorus d L N₁ m₁ (k + 1))}
    (hcovV : ∀ z, CovSetup S.G' 1 (jV z) (XV z) (𝒦XV z))
    (hX₁V : ∀ z, (↑(X₁V z) : Set (CTorus d L N₁ m₁ (k + 1))) = X1 S.G' 1 (jV z) (𝒦XV z))
    (hzXV : ∀ z, ∀ x ∈ blockSites d L N₁ m₁ (k + 1) k z, x ∈ X1 S.G' 1 (jV z) (𝒦XV z))
    {F₂ : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) →
      Dec2.DecParams (coverOf S.G') × RawData d L (N₁ * L ^ m₁) (k + 1) N →
        (S.G'.Ω 1 × Fin N → ℂ) × (S.G'.Ω 1 → ℂ)}
    {F₂' : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) →
      Dec2.DecParams (coverOf Gl) × RawData d L (N₁ * L ^ m₁) (k + 1) N →
        (Gl.Ω 1 × Fin N → ℂ) × (Gl.Ω 1 → ℂ)}
    (hF₂s : ∀ z (s : Dec2.DecParams (coverOf S.G')) (D : BgData S.G' N),
      (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC S.G' (bgC0 d L N) (c7 d L N BG κ) S.ν D → ∀ (φ : S.G'.Ω 1 × Fin N → ℂ)
        (α : S.G'.Ω 1 → ℂ), Dec2.IsDecBg (coverOf S.G') S.G' (compWeight L S.a₁) S.ν
          (rho4 d L N BG κ) s D φ α → F₂ z (s, rawOf D) = (φ, α))
    (hF₂s' : ∀ z (s : Dec2.DecParams (coverOf Gl)) (D : BgData Gl N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC Gl (bgC0 d L N) (c7 d L N BG κ) S.ν D → ∀ (φ : Gl.Ω 1 × Fin N → ℂ)
        (α : Gl.Ω 1 → ℂ), Dec2.IsDecBg (coverOf Gl) Gl (compWeight L S.a₁) S.ν
          (rho4 d L N BG κ) s D φ α → F₂' z (s, rawOf D) = (φ, α))
    {Sol₂ : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) →
      Dec2.DecParams (coverOf S.G') × Edat Hm N → (Hm.Ω 1 × Fin N → ℂ) × (Hm.Ω 1 → ℂ)}
    {Sol₂' : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) →
      Dec2.DecParams (coverOf Gl) × Edat Gd N → (Gd.Ω 1 × Fin N → ℂ) × (Gd.Ω 1 → ℂ)}
    (hSol₂ : ∀ z (p : Dec2.DecParams (coverOf S.G') × Edat Hm N), (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM Hm N false δ₀ δ₁ p.2 →
        (Sol₂ z p).1 = dphi Hm (Dec2.decG (coverOf S.G') Hm (compWeight L S.a₁) S.ν p.1) p.2.2.1
          p.2.1 (pertSource Hm (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) (Sol₂ z p).2 ∧
        Dec2.DecFixed (coverOf S.G') Hm (compWeight L S.a₁) S.ν p.1 false p.2.2.1 p.2.1
          (pertSource Hm (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) (Sol₂ z p).2 ∧
        Small Hm (Sol₂ z p).2 (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
        Small Hm (Sol₂ z p).2 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        SupBounds Hm (Sol₂ z p).1 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        (∀ δα' : Hm.Ω 1 → ℂ, Small Hm δα' (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf S.G') Hm (compWeight L S.a₁) S.ν p.1 false p.2.2.1 p.2.1
            (pertSource Hm (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol₂ z p).2))
    (hSol₂' : ∀ z (p : Dec2.DecParams (coverOf Gl) × Edat Gd N), (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM Gd N false δ₀' δ₁ p.2 →
        (Sol₂' z p).1 = dphi Gd (Dec2.decG (coverOf Gl) Gd (compWeight L S.a₁) S.ν p.1) p.2.2.1
          p.2.1 (pertSource Gd (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) (Sol₂' z p).2 ∧
        Dec2.DecFixed (coverOf Gl) Gd (compWeight L S.a₁) S.ν p.1 false p.2.2.1 p.2.1
          (pertSource Gd (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) (Sol₂' z p).2 ∧
        Small Gd (Sol₂' z p).2 (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
        Small Gd (Sol₂' z p).2 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        SupBounds Gd (Sol₂' z p).1 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        (∀ δα' : Gd.Ω 1 → ℂ, Small Gd δα' (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf Gl) Gd (compWeight L S.a₁) S.ν p.1 false p.2.2.1 p.2.1
            (pertSource Gd (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol₂' z p).2))
    (ω : ℂ → ℂ)
    -- the old terms
    {ι : Type*} [Fintype ι] {m₀ : ℕ} (hNm : L ^ m₀ ∣ N₁)
    {X₁f : ι → Finset (CTorus d L N₁ m₁ (k + 1))} {jL : ι → ℕ}
    {XL 𝒦X : ι → Set (CTorus d L N₁ m₁ (k + 1))}
    (hcovL : ∀ τ, CovSetup S.G' m₀ (jL τ) (XL τ) (𝒦X τ))
    (hX₁L : ∀ τ, (↑(X₁f τ) : Set (CTorus d L N₁ m₁ (k + 1))) = X1 S.G' m₀ (jL τ) (𝒦X τ))
    (Gk : ι → GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ₁)
    (Gj : ι → GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ₂)
    (hkX : ∀ τ, ∀ x ∈ dataSites (Gk τ), x ∈ X1 S.G' m₀ (jL τ) (𝒦X τ)) (ac : ℕ → ℝ)
    (Fk : ∀ τ, RawData d L (N₁ * L ^ m₁) (k + 1) N → ((Gk τ).Ω 1 × Fin N → ℂ) × ((Gk τ).Ω 1 → ℂ))
    (E : ι → RawData d L (N₁ * L ^ m₁) (k + 1) N → ℂ)
    -- the constants of the decoupling pairs of the old terms
    {cL BGL : ℝ} (hSL : Dec2.DecSpecs d L (Dec2.mixedKc d L) (Cchi d L) cL BGL)
    {κL : ℝ} (hκL : 0 < κL) (hMcL : cL * Real.exp (N0 d L * κL) ≤ (L : ℝ) ^ m₁)
    (hMXL : Dec2.cstarX d L (Cchi d L) * Real.exp (N0 d L * κL) ≤ (L : ℝ) ^ m₁)
    {c₂L BG₂L : ℝ} (hF₂L : Dec2.FamSpec d L (Dec2.mixedKc d L) (Cchi d L) c₂L BG₂L)
    (hM₂L : c₂L * Real.exp (N0 d L * κL) ≤ (L : ℝ) ^ m₁) {δ₀L δ₀L' δ₁L : ℝ} (h0L : 0 ≤ δ₀L)
    (h0L' : 0 ≤ δ₀L') (h1L : 0 < δ₁L)
    (hδ₀L : δ₀L ≤ deltaStar' d L N (famConst d L BG₂L κL) (gamma1 d / 8))
    (hδ₀L' : δ₀L' ≤ deltaStar' d L N (famConst d L BG₂L κL) (gamma1 d / 8))
    (hδ₁L : δ₁L ≤ deltaStar' d L N (famConst d L BG₂L κL) (gamma1 d / 8))
    (hc7L : xiC1 d * eps ≤ c7 d L N BGL κL)
    (hphiL : (3 + K4 d L N BGL κL) * (xiC1 d * eps) < 1 / 2)
    (hc7L' : xiC1 d * eps' ≤ c7 d L N BGL κL)
    (hphiL' : (3 + K4 d L N BGL κL) * (xiC1 d * eps') < 1 / 2)
    (hδ₀aL : 2 * (K4 d L N BGL κL * (xiC1 d * eps)) ≤ δ₀L)
    (hδ₀eL : 2 * (K4 d L N BGL κL * (xiC1 d * eps')) ≤ δ₀L')
    {δcL : ℝ} (hmarDL' : decDomMargin d L N BGL κL (xiC1 d * eps') < δcL)
    (hαDL' : K4 d L N BGL κL * (xiC1 d * eps') < coerciveConst d / 2)
    (hsmL : δcL ^ 2 * smallConstX d L κL ≤ 1 / 4) {cψL : ℝ} (hρcL : ρ ≤ cψL)
    (hRuL : Ru * markedRad d L N k S.a₁ κL cψL ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) < δ₁L)
    {F₁L : ι → Dec2.DecParams (coverOf S.G') × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      (S.G'.Ω 1 × Fin N → ℂ) × (S.G'.Ω 1 → ℂ)}
    {F₁L' : ι → Dec2.DecParams (coverOf Gl) × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      (Gl.Ω 1 × Fin N → ℂ) × (Gl.Ω 1 → ℂ)}
    (hF₁L : ∀ τ (s : Dec2.DecParams (coverOf S.G')) (D : BgData S.G' N),
      (∀ P, ‖s P‖ < Real.exp κL) →
      InUnionDomainC S.G' (bgC0 d L N) (c7 d L N BGL κL) S.ν D → ∀ (φ : S.G'.Ω 1 × Fin N → ℂ)
        (α : S.G'.Ω 1 → ℂ), Dec2.IsDecBg (coverOf S.G') S.G' (compWeight L S.a₁) S.ν
          (rho4 d L N BGL κL) s D φ α → F₁L τ (s, rawOf D) = (φ, α))
    (hF₁L' : ∀ τ (s : Dec2.DecParams (coverOf Gl)) (D : BgData Gl N), (∀ P, ‖s P‖ < Real.exp κL) →
      InUnionDomainC Gl (bgC0 d L N) (c7 d L N BGL κL) S.ν D → ∀ (φ : Gl.Ω 1 × Fin N → ℂ)
        (α : Gl.Ω 1 → ℂ), Dec2.IsDecBg (coverOf Gl) Gl (compWeight L S.a₁) S.ν
          (rho4 d L N BGL κL) s D φ α → F₁L' τ (s, rawOf D) = (φ, α))
    {SolL : ι → Dec2.DecParams (coverOf S.G') × Edat Hm N → (Hm.Ω 1 × Fin N → ℂ) × (Hm.Ω 1 → ℂ)}
    {SolL' : ι → Dec2.DecParams (coverOf Gl) × Edat Gd N → (Gd.Ω 1 × Fin N → ℂ) × (Gd.Ω 1 → ℂ)}
    (hSolL : ∀ τ (p : Dec2.DecParams (coverOf S.G') × Edat Hm N), (∀ P, ‖p.1 P‖ < Real.exp κL) →
      StrictDataM Hm N false δ₀L δ₁L p.2 →
        (SolL τ p).1 = dphi Hm (Dec2.decG (coverOf S.G') Hm (compWeight L S.a₁) S.ν p.1) p.2.2.1
          p.2.1 (pertSource Hm (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) (SolL τ p).2 ∧
        Dec2.DecFixed (coverOf S.G') Hm (compWeight L S.a₁) S.ν p.1 false p.2.2.1 p.2.1
          (pertSource Hm (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) (SolL τ p).2 ∧
        Small Hm (SolL τ p).2 (c6' d L N (famConst d L BG₂L κL) (gamma1 d / 8)) ∧
        Small Hm (SolL τ p).2 (cK2' d L N (famConst d L BG₂L κL) * δ₁L) ∧
        SupBounds Hm (SolL τ p).1 (cK2' d L N (famConst d L BG₂L κL) * δ₁L) ∧
        (∀ δα' : Hm.Ω 1 → ℂ, Small Hm δα' (c6' d L N (famConst d L BG₂L κL) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf S.G') Hm (compWeight L S.a₁) S.ν p.1 false p.2.2.1 p.2.1
            (pertSource Hm (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (SolL τ p).2))
    (hSolL' : ∀ τ (p : Dec2.DecParams (coverOf Gl) × Edat Gd N), (∀ P, ‖p.1 P‖ < Real.exp κL) →
      StrictDataM Gd N false δ₀L' δ₁L p.2 →
        (SolL' τ p).1 = dphi Gd (Dec2.decG (coverOf Gl) Gd (compWeight L S.a₁) S.ν p.1) p.2.2.1
          p.2.1 (pertSource Gd (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) (SolL' τ p).2 ∧
        Dec2.DecFixed (coverOf Gl) Gd (compWeight L S.a₁) S.ν p.1 false p.2.2.1 p.2.1
          (pertSource Gd (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) (SolL' τ p).2 ∧
        Small Gd (SolL' τ p).2 (c6' d L N (famConst d L BG₂L κL) (gamma1 d / 8)) ∧
        Small Gd (SolL' τ p).2 (cK2' d L N (famConst d L BG₂L κL) * δ₁L) ∧
        SupBounds Gd (SolL' τ p).1 (cK2' d L N (famConst d L BG₂L κL) * δ₁L) ∧
        (∀ δα' : Gd.Ω 1 → ℂ, Small Gd δα' (c6' d L N (famConst d L BG₂L κL) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf Gl) Gd (compWeight L S.a₁) S.ν p.1 false p.2.2.1 p.2.1
            (pertSource Gd (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (SolL' τ p).2))
    (𝒴C : Finset (Set (CTorus d L N₁ m₁ (k + 1)))) (h𝒴C : ∀ Y ∈ 𝒴C, IsDj 1 (k + 1) Y)
    (hdomC : ∀ τ, ∀ Y ∈ polyDom S.G' (X₁f τ) m₀ (jL τ) (𝒦X τ), IsDj 1 (k + 1) Y)
    -- the bridge marks
    {F₁b : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) →
      Dec2.DecParams (coverOf S.G') × RawData d L (N₁ * L ^ m₁) (k + 1) N →
        (S.G'.Ω 1 × Fin N → ℂ) × (S.G'.Ω 1 → ℂ)}
    {F₁b' : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) →
      Dec2.DecParams (coverOf Gl) × RawData d L (N₁ * L ^ m₁) (k + 1) N →
        (Gl.Ω 1 × Fin N → ℂ) × (Gl.Ω 1 → ℂ)}
    (hF₁b : ∀ b (s : Dec2.DecParams (coverOf S.G')) (D : BgData S.G' N),
      (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC S.G' (bgC0 d L N) (c7 d L N BG κ) S.ν D → ∀ (φ : S.G'.Ω 1 × Fin N → ℂ)
        (α : S.G'.Ω 1 → ℂ), Dec2.IsDecBg (coverOf S.G') S.G' (compWeight L S.a₁) S.ν
          (rho4 d L N BG κ) s D φ α → F₁b b (s, rawOf D) = (φ, α))
    (hF₁b' : ∀ b (s : Dec2.DecParams (coverOf Gl)) (D : BgData Gl N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC Gl (bgC0 d L N) (c7 d L N BG κ) S.ν D → ∀ (φ : Gl.Ω 1 × Fin N → ℂ)
        (α : Gl.Ω 1 → ℂ), Dec2.IsDecBg (coverOf Gl) Gl (compWeight L S.a₁) S.ν
          (rho4 d L N BG κ) s D φ α → F₁b' b (s, rawOf D) = (φ, α))
    {Solb : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) →
      Dec2.DecParams (coverOf S.G') × Edat Hm N → (Hm.Ω 1 × Fin N → ℂ) × (Hm.Ω 1 → ℂ)}
    {Solb' : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) →
      Dec2.DecParams (coverOf Gl) × Edat Gd N → (Gd.Ω 1 × Fin N → ℂ) × (Gd.Ω 1 → ℂ)}
    (hSolb : ∀ b (p : Dec2.DecParams (coverOf S.G') × Edat Hm N), (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM Hm N false δ₀ δ₁ p.2 →
        (Solb b p).1 = dphi Hm (Dec2.decG (coverOf S.G') Hm (compWeight L S.a₁) S.ν p.1) p.2.2.1
          p.2.1 (pertSource Hm (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) (Solb b p).2 ∧
        Dec2.DecFixed (coverOf S.G') Hm (compWeight L S.a₁) S.ν p.1 false p.2.2.1 p.2.1
          (pertSource Hm (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) (Solb b p).2 ∧
        Small Hm (Solb b p).2 (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
        Small Hm (Solb b p).2 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        SupBounds Hm (Solb b p).1 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        (∀ δα' : Hm.Ω 1 → ℂ, Small Hm δα' (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf S.G') Hm (compWeight L S.a₁) S.ν p.1 false p.2.2.1 p.2.1
            (pertSource Hm (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Solb b p).2))
    (hSolb' : ∀ b (p : Dec2.DecParams (coverOf Gl) × Edat Gd N), (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM Gd N false δ₀' δ₁ p.2 →
        (Solb' b p).1 = dphi Gd (Dec2.decG (coverOf Gl) Gd (compWeight L S.a₁) S.ν p.1) p.2.2.1
          p.2.1 (pertSource Gd (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) (Solb' b p).2 ∧
        Dec2.DecFixed (coverOf Gl) Gd (compWeight L S.a₁) S.ν p.1 false p.2.2.1 p.2.1
          (pertSource Gd (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) (Solb' b p).2 ∧
        Small Gd (Solb' b p).2 (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
        Small Gd (Solb' b p).2 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        SupBounds Gd (Solb' b p).1 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        (∀ δα' : Gd.Ω 1 → ℂ, Small Gd δα' (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf Gl) Gd (compWeight L S.a₁) S.ν p.1 false p.2.2.1 p.2.1
            (pertSource Gd (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Solb' b p).2))
    (z : RootIdx d L N₁ m₁ (k + 1)) (hdomE : ∀ b, ∀ Y ∈ e1DomG S b, IsDj 1 (k + 1) Y)
    -- the step's class family and marks
    {ε₀ ε₁ κH κ0 K₀ K₁ : ℝ}
    (A₀ : physParam N S → ℂ →
      LabelAct (thickLabels (m₀ := 1) (j := k + 1) 𝒴₀ h𝒴₀) (S.blockSplit 1 hp).Ωb ε₀ κH κ0 K₀)
    (AC : physParam N S → ℂ →
      LabelAct (thickLabels (m₀ := 1) (j := k + 1) 𝒴C h𝒴C) (S.blockSplit 1 hp).Ωb ε₁ κH κ0 K₁)
    (hε₁ : 0 ≤ ε₁) (hε : 0 ≤ max ε₀ ε₁) (hκ0 : aEnt d L + 2 ≤ κ0)
    (y1 : {q // q ∈ markedIdx (fun _ => (Set.univ : Set (CTorus d L N₁ m₁ (k + 1))))
        (fun τ => polyDom S.G' (X₁f τ) m₀ (jL τ) (𝒦X τ)) z} →
      ({Y // Y ∈ 𝒴₀} ⊕ ({Y // Y ∈ 𝒴C} ⊕ RootUnionLb 1
        (fun _ => (Set.univ : Set (CTorus d L N₁ m₁ (k + 1))))
        (fun τ => polyDom S.G' (X₁f τ) m₀ (jL τ) (𝒦X τ)))) ⊕
        RootUnionLb 1 (fun _ => (Set.univ : Set (CTorus d L N₁ m₁ (k + 1)))) (e1DomG S))
    (hy1 : ∀ q, (commonLabels ((thickLabels (m₀ := 1) (j := k + 1) 𝒴₀ h𝒴₀).sum
        (commonLabels (thickLabels (m₀ := 1) (j := k + 1) 𝒴C h𝒴C) hN1 hL (fun _ => Set.univ)
          (fun τ => polyDom S.G' (X₁f τ) m₀ (jL τ) (𝒦X τ)) hdomC)) hN1 hL (fun _ => Set.univ)
        (e1DomG S) hdomE).ysite (y1 q) = bridge 1 z q.1.2)
    (G₁ : physParam N S →
      {q // q ∈ markedIdx (fun _ => (Set.univ : Set (CTorus d L N₁ m₁ (k + 1))))
        (fun τ => polyDom S.G' (X₁f τ) m₀ (jL τ) (𝒦X τ)) z} →
      ℂ → (∀ b, (S.blockSplit 1 hp).Ωb b) → ℂ)
    -- the read datum
    {D : BgData S.G' N} (hD : XiCData S.G' (compWeight L S.a₁) S.ν (k + 1) 1 eps D)
    (θ : physParam N S) (hθ : (θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) = rawOf D)
    (θb : physParamBg N Gl)
    (hθb : (θb.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) = clipRaw Gl (rawOf D))
    -- the step's activities and marks are the formulas at the step's own set
    (h0eq : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ Y Φ, (A₀ θ (s : ℂ)).H Y Φ =
      zeroActBg S S.G' (BgTransport.self S.hG') X₁V jV 𝒦XV 1 F₂ Sol₂ ω ρ₀ hp eps₀ θ (s : ℂ) Y.1 Φ)
    (h1eq : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ Y Φ, (AC θ (s : ℂ)).H Y Φ =
      oldActBg S S.G' (BgTransport.self S.hG') (S.blockU z) X₁f m₀ jL 𝒦X F₁L SolL
        (fun τ => eTermFun S.G' (Gk τ) (Gj τ) Hm ac (Fk τ) (E τ)) ρ hp Ru eps₀ 𝒴C θ Y (s : ℂ) Φ)
    (hG₁eq : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ q Φ, G₁ θ q (s : ℂ) Φ =
      oldMarkGBg S S.G' (BgTransport.self S.hG') (S.blockU z) X₁f m₀ jL 𝒦X F₁L SolL
        (fun τ => eTermFun S.G' (Gk τ) (Gj τ) Hm ac (Fk τ) (E τ)) ρ hp Ru eps₀ z θ q (s : ℂ) Φ)
    (hGdep : ∀ i s, DepOn (blocksOf 1 (k + 1) Set.univ
      ((commonLabels ((thickLabels (m₀ := 1) (j := k + 1) 𝒴₀ h𝒴₀).sum
        (commonLabels (thickLabels (m₀ := 1) (j := k + 1) 𝒴C h𝒴C) hN1 hL (fun _ => Set.univ)
          (fun τ => polyDom S.G' (X₁f τ) m₀ (jL τ) (𝒦X τ)) hdomC)) hN1 hL (fun _ => Set.univ)
        (e1DomG S) hdomE).ysite
        (Sum.elim (commonAnchor ({Y // Y ∈ 𝒴₀} ⊕ ({Y // Y ∈ 𝒴C} ⊕ RootUnionLb 1
          (fun _ => (Set.univ : Set (CTorus d L N₁ m₁ (k + 1))))
          (fun τ => polyDom S.G' (X₁f τ) m₀ (jL τ) (𝒦X τ)))) (fun _ => Set.univ) (e1DomG S) z)
          y1 i)))
      (Sum.elim (fun i u Φ => e1MarkGParamG S F₁b Solb ρ₀ hp z eps₀ θ i u Φ) (G₁ θ) i s))
    -- the polymer, its margin, and the determinant part
    (a : ℕ → ℝ) (aT ν' ρd : ℝ) (Zb : Finset (unitPts Gl))
    (T : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) 1 (k + 1) Set.univ))
    (hTmar : ∀ x ∈ sitesOf T, ∀ y, supDist x y ≤ 2 * L ^ (k + 1 + m₁) → y ∈ Gl.Ω (k + 1))
    (hdet : newLevelDetBg S.G' a aT ν' ρd (S.blockU z) θ T = newLevelDetBg Gl a aT ν' ρd Zb θb T) :
    newLevelDetBg S.G' a aT ν' ρd (S.blockU z) θ T +
        gsumCoeff (S.blockSplit 1 hp).μ
          (commonLabels ((thickLabels (m₀ := 1) (j := k + 1) 𝒴₀ h𝒴₀).sum
            (commonLabels (thickLabels (m₀ := 1) (j := k + 1) 𝒴C h𝒴C) hN1 hL (fun _ => Set.univ)
              (fun τ => polyDom S.G' (X₁f τ) m₀ (jL τ) (𝒦X τ)) hdomC)) hN1 hL (fun _ => Set.univ)
            (e1DomG S) hdomE)
          (commonAct (fun θ u => (A₀ θ u).sum (commonAct AC hN1 hL (fun _ => Set.univ)
              (fun τ => polyDom S.G' (X₁f τ) m₀ (jL τ) (𝒦X τ)) hdomC hε₁ hκ0 θ u))
            hN1 hL (fun _ => Set.univ) (e1DomG S) hdomE hε hκ0 θ)
          (Sum.elim (commonAnchor ({Y // Y ∈ 𝒴₀} ⊕ ({Y // Y ∈ 𝒴C} ⊕ RootUnionLb 1
            (fun _ => (Set.univ : Set (CTorus d L N₁ m₁ (k + 1))))
            (fun τ => polyDom S.G' (X₁f τ) m₀ (jL τ) (𝒦X τ)))) (fun _ => Set.univ) (e1DomG S) z)
            y1)
          (Sum.elim (fun i u Φ => e1MarkGParamG S F₁b Solb ρ₀ hp z eps₀ θ i u Φ) (G₁ θ)) T =
      newLevelCoeffBg Gl (S.blockSplit 1 hp).μ a aT ν' ρd Zb
        (commonLabels ((thickLabels (m₀ := 1) (j := k + 1) 𝒴₀ h𝒴₀).sum
          (commonLabels (thickLabels (m₀ := 1) (j := k + 1) 𝒴C h𝒴C) hN1 hL (fun _ => Set.univ)
            (fun τ => polyDom S.G' (X₁f τ) m₀ (jL τ) (𝒦X τ)) hdomC)) hN1 hL (fun _ => Set.univ)
          (e1DomG S) hdomE)
        (classActFun
          (fun θb u (Y : {Y // Y ∈ 𝒴₀}) Φ => zeroActBg S Gl (BgTransport.canon S.G' Gl N) X₁V jV
            𝒦XV 1 F₂' Sol₂' ω ρ₀ hp eps' θb u Y.1 Φ)
          (fun θb u Y Φ => oldActBg S Gl (BgTransport.canon S.G' Gl N) (maskPre S.hG' Gl (S.blockU z))
            X₁f m₀ jL 𝒦X F₁L' SolL' (fun τ => eTermFun Gl (Gk τ) (Gj τ) Gd ac (Fk τ) (E τ)) ρ hp Ru
            eps' 𝒴C θb Y u Φ))
        (Sum.elim (commonAnchor ({Y // Y ∈ 𝒴₀} ⊕ ({Y // Y ∈ 𝒴C} ⊕ RootUnionLb 1
          (fun _ => (Set.univ : Set (CTorus d L N₁ m₁ (k + 1))))
          (fun τ => polyDom S.G' (X₁f τ) m₀ (jL τ) (𝒦X τ)))) (fun _ => Set.univ) (e1DomG S) z) y1)
        (fun θb => Sum.elim
          (fun i u Φ => e1MarkGParamGBgOn S Gl (BgTransport.canon S.G' Gl N)
            (maskPre S.hG' Gl (S.blockU z)) F₁b' Solb' ρ₀ hp z Gl eps' θb i u Φ)
          (oldMarkGBg S Gl (BgTransport.canon S.G' Gl N) (maskPre S.hG' Gl (S.blockU z)) X₁f m₀ jL
            𝒦X F₁L' SolL' (fun τ => eTermFun Gl (Gk τ) (Gj τ) Gd ac (Fk τ) (E τ)) ρ hp Ru eps' z
            θb))
        θb T := by
  have h :=
    newLevelCoeffBg_class_canon_agree S hG hA hSS hPd hdk hdtop hN hm₁ hM hag hagm hagl hagd hS HB
      HB' ha₁ ha₂ hκ hMc hMX hF₂ hM₂ h0 h0' h1 hδ₀ hδ₀' hδ₁ heps hsmall hc7 hphi heps₀ hεr hsmall'
      hc7' hphi' hδ₀a hδ₀e hmarD' hαD' hsm hρ₀ hρ₀c hρ hp hRu1 hRu hN1 hL 𝒴₀ h𝒴₀ hcovV hX₁V hzXV
      hF₂s hF₂s' hSol₂ hSol₂' ω hNm hcovL hX₁L Gk Gj hkX ac Fk E hSL hκL hMcL hMXL hF₂L hM₂L h0L
      h0L' h1L hδ₀L hδ₀L' hδ₁L hc7L hphiL hc7L' hphiL' hδ₀aL hδ₀eL hmarDL' hαDL' hsmL hρcL hRuL
      hF₁L hF₁L' hSolL hSolL' 𝒴C h𝒴C hdomC hF₁b hF₁b' hSolb hSolb' z hdomE A₀ AC y1 hy1 G₁
      hD θ hθ θb hθb h0eq h1eq hG₁eq T hTmar
  exact newLevelCoeffBg_class_eq_of_agree S.G' Gl _ a aT ν' ρd (S.blockU z) Zb A₀ AC hN1 hL _ _
    hdomC _ _ hdomE hε₁ hε hκ0 θ _ _ θ _ _ _ θb T hdet hGdep h.1 h.2.1 h.2.2

open Classical in
/-- **The replacement identity (A5) of the coefficient of a class on a local generating set,
reduced to the determinant part** (P3 pp. 78-79, (4.44)-(4.47)).  Let `Gl` be cube aligned and
sup-separated, `Gd ≺ Gl` with the layer `k` of `Gl` and no layer `k + 1`, and let the decoupling maps
of the step and of `(Gl, Gd)` be given by their specifications: per block for the zero-source terms
(`F₂`, `Sol₂`; `F₂'`, `Sol₂'`) and for the bridge marks (`F₁b`, `Solb`; `F₁b'`, `Solb'`), per old term
(`F₁L`, `SolL`; `F₁L'`, `SolL'`).  Let `θ` be the step's parameter with the datum `D` of the step
chart and `θ_b` the parameter of `Gl` with the read datum.  If the step's class family
`commonAct (A₀.sum (commonAct A_C …))` and its marks are the formulas at the step's own set at `θ`
(`h0eq`, `h1eq`, `hG₁eq`; the bridge marks are `e1MarkGParamG`), the marks are local (`hGdep`), and
the sites of `T` have the margin `2 M₁ L^{k+1}` in the top layer of `Gl`, then the coefficient of the
step (determinant part plus `gsumCoeff`) equals the formula `newLevelCoeffBg` on `Gl` at `θ_b` with
the recomputed activities and marks, when the determinant parts agree.  The conditions on `ε′`,
`Ru` and the radii are smallness conditions against absolute constants. -/
theorem newLevelCoeffBg_class_canon_eq_of_det (S : StepSetting d L N₁ m₁ k N ϱ)
    {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm} (hG : IsLevel Hm k)
    {Gl : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱl}
    {Gd : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱl'}
    (hA : CubeAligned Gl m₁) (hSS : SupSep Gl m₁) (hPd : Precedes Gd Gl)
    (hdk : Gd.Ω k = Gl.Ω k) (hdtop : Gd.Ω (k + 1) = ∅)
    (hN : 5 < N₁) (hm₁ : 2 ≤ m₁) (hM : 4 * L ^ 2 ≤ L ^ m₁)
    (hag : 2 * d * Real.log L ≤ agmonRate d / 16 * (ϱ - 1))
    (hagm : 2 * d * Real.log L ≤ agmonRate d / 16 * (ϱm - 1))
    (hagl : 2 * d * Real.log L ≤ agmonRate d / 16 * (ϱl - 1))
    (hagd : 2 * d * Real.log L ≤ agmonRate d / 16 * (ϱl' - 1))
    {c BG : ℝ} (hS : Dec2.DecSpecs d L (Dec2.mixedKc d L) (Cchi d L) c BG)
    (HB : BgHyp d L (k + 1) ϱ (compWeight L S.a₁) S.ν)
    (HB' : BgHyp d L (k + 1) ϱl (compWeight L S.a₁) S.ν)
    (ha₁ : 1 / 2 ≤ S.a₁) (ha₂ : S.a₁ ≤ 2)
    {κ : ℝ} (hκ : 0 < κ) (hMc : c * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    (hMX : Dec2.cstarX d L (Cchi d L) * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    {c₂ BG₂ : ℝ} (hF₂ : Dec2.FamSpec d L (Dec2.mixedKc d L) (Cchi d L) c₂ BG₂)
    (hM₂ : c₂ * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δ₀ δ₀' δ₁ : ℝ} (h0 : 0 ≤ δ₀) (h0' : 0 ≤ δ₀')
    (h1 : 0 < δ₁)
    (hδ₀ : δ₀ ≤ deltaStar' d L N (famConst d L BG₂ κ) (gamma1 d / 8))
    (hδ₀' : δ₀' ≤ deltaStar' d L N (famConst d L BG₂ κ) (gamma1 d / 8))
    (hδ₁ : δ₁ ≤ deltaStar' d L N (famConst d L BG₂ κ) (gamma1 d / 8))
    {eps eps₀ eps' : ℝ} (heps : 0 < eps) (hsmall : (4 * d + 6) * ((2 * d + 1) * eps) ≤ 1)
    (hc7 : xiC1 d * eps ≤ c7 d L N BG κ) (hphi : (3 + K4 d L N BG κ) * (xiC1 d * eps) < 1 / 2)
    (heps₀ : eps ≤ eps₀) (hεr : (2 * bgK1 d L N + 2) * xiC1 d * eps ≤ eps')
    (hsmall' : (4 * d + 6) * ((2 * d + 1) * eps') ≤ 1) (hc7' : xiC1 d * eps' ≤ c7 d L N BG κ)
    (hphi' : (3 + K4 d L N BG κ) * (xiC1 d * eps') < 1 / 2)
    (hδ₀a : 2 * (K4 d L N BG κ * (xiC1 d * eps)) ≤ δ₀)
    (hδ₀e : 2 * (K4 d L N BG κ * (xiC1 d * eps')) ≤ δ₀')
    {δc : ℝ} (hmarD' : decDomMargin d L N BG κ (xiC1 d * eps') < δc)
    (hαD' : K4 d L N BG κ * (xiC1 d * eps') < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4) {cψ ρ₀ ρ : ℝ} (hρ₀ : 0 < ρ₀) (hρ₀c : 2 * ρ₀ ≤ cψ)
    (hρ : 0 < ρ) (hρc : ρ ≤ cψ) (hp : 0 < S.p₁) {Ru : ℝ} (hRu1 : 17 / 16 ≤ Ru)
    (hRu : Ru * markedRad d L N k S.a₁ κ cψ ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) < δ₁)
    (hN1 : L ^ 1 ∣ N₁) (hL : 2 ≤ L)
    -- the zero-source part
    (𝒴₀ : Finset (Set (CTorus d L N₁ m₁ (k + 1)))) (h𝒴₀ : ∀ Y ∈ 𝒴₀, IsDj 1 (k + 1) Y)
    {X₁V : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) → Finset (CTorus d L N₁ m₁ (k + 1))}
    {jV : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) → ℕ}
    {XV 𝒦XV : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) → Set (CTorus d L N₁ m₁ (k + 1))}
    (hcovV : ∀ z, CovSetup S.G' 1 (jV z) (XV z) (𝒦XV z))
    (hX₁V : ∀ z, (↑(X₁V z) : Set (CTorus d L N₁ m₁ (k + 1))) = X1 S.G' 1 (jV z) (𝒦XV z))
    (hzXV : ∀ z, ∀ x ∈ blockSites d L N₁ m₁ (k + 1) k z, x ∈ X1 S.G' 1 (jV z) (𝒦XV z))
    {F₂ : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) →
      Dec2.DecParams (coverOf S.G') × RawData d L (N₁ * L ^ m₁) (k + 1) N →
        (S.G'.Ω 1 × Fin N → ℂ) × (S.G'.Ω 1 → ℂ)}
    {F₂' : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) →
      Dec2.DecParams (coverOf Gl) × RawData d L (N₁ * L ^ m₁) (k + 1) N →
        (Gl.Ω 1 × Fin N → ℂ) × (Gl.Ω 1 → ℂ)}
    (hF₂s : ∀ z (s : Dec2.DecParams (coverOf S.G')) (D : BgData S.G' N),
      (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC S.G' (bgC0 d L N) (c7 d L N BG κ) S.ν D → ∀ (φ : S.G'.Ω 1 × Fin N → ℂ)
        (α : S.G'.Ω 1 → ℂ), Dec2.IsDecBg (coverOf S.G') S.G' (compWeight L S.a₁) S.ν
          (rho4 d L N BG κ) s D φ α → F₂ z (s, rawOf D) = (φ, α))
    (hF₂s' : ∀ z (s : Dec2.DecParams (coverOf Gl)) (D : BgData Gl N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC Gl (bgC0 d L N) (c7 d L N BG κ) S.ν D → ∀ (φ : Gl.Ω 1 × Fin N → ℂ)
        (α : Gl.Ω 1 → ℂ), Dec2.IsDecBg (coverOf Gl) Gl (compWeight L S.a₁) S.ν
          (rho4 d L N BG κ) s D φ α → F₂' z (s, rawOf D) = (φ, α))
    {Sol₂ : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) →
      Dec2.DecParams (coverOf S.G') × Edat Hm N → (Hm.Ω 1 × Fin N → ℂ) × (Hm.Ω 1 → ℂ)}
    {Sol₂' : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) →
      Dec2.DecParams (coverOf Gl) × Edat Gd N → (Gd.Ω 1 × Fin N → ℂ) × (Gd.Ω 1 → ℂ)}
    (hSol₂ : ∀ z (p : Dec2.DecParams (coverOf S.G') × Edat Hm N), (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM Hm N false δ₀ δ₁ p.2 →
        (Sol₂ z p).1 = dphi Hm (Dec2.decG (coverOf S.G') Hm (compWeight L S.a₁) S.ν p.1) p.2.2.1
          p.2.1 (pertSource Hm (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) (Sol₂ z p).2 ∧
        Dec2.DecFixed (coverOf S.G') Hm (compWeight L S.a₁) S.ν p.1 false p.2.2.1 p.2.1
          (pertSource Hm (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) (Sol₂ z p).2 ∧
        Small Hm (Sol₂ z p).2 (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
        Small Hm (Sol₂ z p).2 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        SupBounds Hm (Sol₂ z p).1 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        (∀ δα' : Hm.Ω 1 → ℂ, Small Hm δα' (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf S.G') Hm (compWeight L S.a₁) S.ν p.1 false p.2.2.1 p.2.1
            (pertSource Hm (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol₂ z p).2))
    (hSol₂' : ∀ z (p : Dec2.DecParams (coverOf Gl) × Edat Gd N), (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM Gd N false δ₀' δ₁ p.2 →
        (Sol₂' z p).1 = dphi Gd (Dec2.decG (coverOf Gl) Gd (compWeight L S.a₁) S.ν p.1) p.2.2.1
          p.2.1 (pertSource Gd (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) (Sol₂' z p).2 ∧
        Dec2.DecFixed (coverOf Gl) Gd (compWeight L S.a₁) S.ν p.1 false p.2.2.1 p.2.1
          (pertSource Gd (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) (Sol₂' z p).2 ∧
        Small Gd (Sol₂' z p).2 (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
        Small Gd (Sol₂' z p).2 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        SupBounds Gd (Sol₂' z p).1 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        (∀ δα' : Gd.Ω 1 → ℂ, Small Gd δα' (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf Gl) Gd (compWeight L S.a₁) S.ν p.1 false p.2.2.1 p.2.1
            (pertSource Gd (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol₂' z p).2))
    (ω : ℂ → ℂ)
    -- the old terms
    {ι : Type*} [Fintype ι] {m₀ : ℕ} (hNm : L ^ m₀ ∣ N₁)
    {X₁f : ι → Finset (CTorus d L N₁ m₁ (k + 1))} {jL : ι → ℕ}
    {XL 𝒦X : ι → Set (CTorus d L N₁ m₁ (k + 1))}
    (hcovL : ∀ τ, CovSetup S.G' m₀ (jL τ) (XL τ) (𝒦X τ))
    (hX₁L : ∀ τ, (↑(X₁f τ) : Set (CTorus d L N₁ m₁ (k + 1))) = X1 S.G' m₀ (jL τ) (𝒦X τ))
    (Gk : ι → GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ₁)
    (Gj : ι → GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ₂)
    (hkX : ∀ τ, ∀ x ∈ dataSites (Gk τ), x ∈ X1 S.G' m₀ (jL τ) (𝒦X τ)) (ac : ℕ → ℝ)
    (Fk : ∀ τ, RawData d L (N₁ * L ^ m₁) (k + 1) N → ((Gk τ).Ω 1 × Fin N → ℂ) × ((Gk τ).Ω 1 → ℂ))
    (E : ι → RawData d L (N₁ * L ^ m₁) (k + 1) N → ℂ)
    {F₁L : ι → Dec2.DecParams (coverOf S.G') × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      (S.G'.Ω 1 × Fin N → ℂ) × (S.G'.Ω 1 → ℂ)}
    {F₁L' : ι → Dec2.DecParams (coverOf Gl) × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      (Gl.Ω 1 × Fin N → ℂ) × (Gl.Ω 1 → ℂ)}
    (hF₁L : ∀ τ (s : Dec2.DecParams (coverOf S.G')) (D : BgData S.G' N),
      (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC S.G' (bgC0 d L N) (c7 d L N BG κ) S.ν D → ∀ (φ : S.G'.Ω 1 × Fin N → ℂ)
        (α : S.G'.Ω 1 → ℂ), Dec2.IsDecBg (coverOf S.G') S.G' (compWeight L S.a₁) S.ν
          (rho4 d L N BG κ) s D φ α → F₁L τ (s, rawOf D) = (φ, α))
    (hF₁L' : ∀ τ (s : Dec2.DecParams (coverOf Gl)) (D : BgData Gl N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC Gl (bgC0 d L N) (c7 d L N BG κ) S.ν D → ∀ (φ : Gl.Ω 1 × Fin N → ℂ)
        (α : Gl.Ω 1 → ℂ), Dec2.IsDecBg (coverOf Gl) Gl (compWeight L S.a₁) S.ν
          (rho4 d L N BG κ) s D φ α → F₁L' τ (s, rawOf D) = (φ, α))
    {SolL : ι → Dec2.DecParams (coverOf S.G') × Edat Hm N → (Hm.Ω 1 × Fin N → ℂ) × (Hm.Ω 1 → ℂ)}
    {SolL' : ι → Dec2.DecParams (coverOf Gl) × Edat Gd N → (Gd.Ω 1 × Fin N → ℂ) × (Gd.Ω 1 → ℂ)}
    (hSolL : ∀ τ (p : Dec2.DecParams (coverOf S.G') × Edat Hm N), (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM Hm N false δ₀ δ₁ p.2 →
        (SolL τ p).1 = dphi Hm (Dec2.decG (coverOf S.G') Hm (compWeight L S.a₁) S.ν p.1) p.2.2.1
          p.2.1 (pertSource Hm (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) (SolL τ p).2 ∧
        Dec2.DecFixed (coverOf S.G') Hm (compWeight L S.a₁) S.ν p.1 false p.2.2.1 p.2.1
          (pertSource Hm (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) (SolL τ p).2 ∧
        Small Hm (SolL τ p).2 (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
        Small Hm (SolL τ p).2 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        SupBounds Hm (SolL τ p).1 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        (∀ δα' : Hm.Ω 1 → ℂ, Small Hm δα' (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf S.G') Hm (compWeight L S.a₁) S.ν p.1 false p.2.2.1 p.2.1
            (pertSource Hm (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (SolL τ p).2))
    (hSolL' : ∀ τ (p : Dec2.DecParams (coverOf Gl) × Edat Gd N), (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM Gd N false δ₀' δ₁ p.2 →
        (SolL' τ p).1 = dphi Gd (Dec2.decG (coverOf Gl) Gd (compWeight L S.a₁) S.ν p.1) p.2.2.1
          p.2.1 (pertSource Gd (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) (SolL' τ p).2 ∧
        Dec2.DecFixed (coverOf Gl) Gd (compWeight L S.a₁) S.ν p.1 false p.2.2.1 p.2.1
          (pertSource Gd (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) (SolL' τ p).2 ∧
        Small Gd (SolL' τ p).2 (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
        Small Gd (SolL' τ p).2 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        SupBounds Gd (SolL' τ p).1 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        (∀ δα' : Gd.Ω 1 → ℂ, Small Gd δα' (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf Gl) Gd (compWeight L S.a₁) S.ν p.1 false p.2.2.1 p.2.1
            (pertSource Gd (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (SolL' τ p).2))
    (𝒴C : Finset (Set (CTorus d L N₁ m₁ (k + 1)))) (h𝒴C : ∀ Y ∈ 𝒴C, IsDj 1 (k + 1) Y)
    (hdomC : ∀ τ, ∀ Y ∈ polyDom S.G' (X₁f τ) m₀ (jL τ) (𝒦X τ), IsDj 1 (k + 1) Y)
    -- the bridge marks
    {F₁b : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) →
      Dec2.DecParams (coverOf S.G') × RawData d L (N₁ * L ^ m₁) (k + 1) N →
        (S.G'.Ω 1 × Fin N → ℂ) × (S.G'.Ω 1 → ℂ)}
    {F₁b' : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) →
      Dec2.DecParams (coverOf Gl) × RawData d L (N₁ * L ^ m₁) (k + 1) N →
        (Gl.Ω 1 × Fin N → ℂ) × (Gl.Ω 1 → ℂ)}
    (hF₁b : ∀ b (s : Dec2.DecParams (coverOf S.G')) (D : BgData S.G' N),
      (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC S.G' (bgC0 d L N) (c7 d L N BG κ) S.ν D → ∀ (φ : S.G'.Ω 1 × Fin N → ℂ)
        (α : S.G'.Ω 1 → ℂ), Dec2.IsDecBg (coverOf S.G') S.G' (compWeight L S.a₁) S.ν
          (rho4 d L N BG κ) s D φ α → F₁b b (s, rawOf D) = (φ, α))
    (hF₁b' : ∀ b (s : Dec2.DecParams (coverOf Gl)) (D : BgData Gl N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC Gl (bgC0 d L N) (c7 d L N BG κ) S.ν D → ∀ (φ : Gl.Ω 1 × Fin N → ℂ)
        (α : Gl.Ω 1 → ℂ), Dec2.IsDecBg (coverOf Gl) Gl (compWeight L S.a₁) S.ν
          (rho4 d L N BG κ) s D φ α → F₁b' b (s, rawOf D) = (φ, α))
    {Solb : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) →
      Dec2.DecParams (coverOf S.G') × Edat Hm N → (Hm.Ω 1 × Fin N → ℂ) × (Hm.Ω 1 → ℂ)}
    {Solb' : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) →
      Dec2.DecParams (coverOf Gl) × Edat Gd N → (Gd.Ω 1 × Fin N → ℂ) × (Gd.Ω 1 → ℂ)}
    (hSolb : ∀ b (p : Dec2.DecParams (coverOf S.G') × Edat Hm N), (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM Hm N false δ₀ δ₁ p.2 →
        (Solb b p).1 = dphi Hm (Dec2.decG (coverOf S.G') Hm (compWeight L S.a₁) S.ν p.1) p.2.2.1
          p.2.1 (pertSource Hm (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) (Solb b p).2 ∧
        Dec2.DecFixed (coverOf S.G') Hm (compWeight L S.a₁) S.ν p.1 false p.2.2.1 p.2.1
          (pertSource Hm (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) (Solb b p).2 ∧
        Small Hm (Solb b p).2 (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
        Small Hm (Solb b p).2 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        SupBounds Hm (Solb b p).1 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        (∀ δα' : Hm.Ω 1 → ℂ, Small Hm δα' (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf S.G') Hm (compWeight L S.a₁) S.ν p.1 false p.2.2.1 p.2.1
            (pertSource Hm (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Solb b p).2))
    (hSolb' : ∀ b (p : Dec2.DecParams (coverOf Gl) × Edat Gd N), (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM Gd N false δ₀' δ₁ p.2 →
        (Solb' b p).1 = dphi Gd (Dec2.decG (coverOf Gl) Gd (compWeight L S.a₁) S.ν p.1) p.2.2.1
          p.2.1 (pertSource Gd (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) (Solb' b p).2 ∧
        Dec2.DecFixed (coverOf Gl) Gd (compWeight L S.a₁) S.ν p.1 false p.2.2.1 p.2.1
          (pertSource Gd (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) (Solb' b p).2 ∧
        Small Gd (Solb' b p).2 (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
        Small Gd (Solb' b p).2 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        SupBounds Gd (Solb' b p).1 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        (∀ δα' : Gd.Ω 1 → ℂ, Small Gd δα' (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf Gl) Gd (compWeight L S.a₁) S.ν p.1 false p.2.2.1 p.2.1
            (pertSource Gd (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Solb' b p).2))
    (z : RootIdx d L N₁ m₁ (k + 1)) (hdomE : ∀ b, ∀ Y ∈ e1DomG S b, IsDj 1 (k + 1) Y)
    -- the step's class family and marks
    {ε₀ ε₁ κH κ0 K₀ K₁ : ℝ}
    (A₀ : physParam N S → ℂ →
      LabelAct (thickLabels (m₀ := 1) (j := k + 1) 𝒴₀ h𝒴₀) (S.blockSplit 1 hp).Ωb ε₀ κH κ0 K₀)
    (AC : physParam N S → ℂ →
      LabelAct (thickLabels (m₀ := 1) (j := k + 1) 𝒴C h𝒴C) (S.blockSplit 1 hp).Ωb ε₁ κH κ0 K₁)
    (hε₁ : 0 ≤ ε₁) (hε : 0 ≤ max ε₀ ε₁) (hκ0 : aEnt d L + 2 ≤ κ0)
    (y1 : {q // q ∈ markedIdx (fun _ => (Set.univ : Set (CTorus d L N₁ m₁ (k + 1))))
        (fun τ => polyDom S.G' (X₁f τ) m₀ (jL τ) (𝒦X τ)) z} →
      ({Y // Y ∈ 𝒴₀} ⊕ ({Y // Y ∈ 𝒴C} ⊕ RootUnionLb 1
        (fun _ => (Set.univ : Set (CTorus d L N₁ m₁ (k + 1))))
        (fun τ => polyDom S.G' (X₁f τ) m₀ (jL τ) (𝒦X τ)))) ⊕
        RootUnionLb 1 (fun _ => (Set.univ : Set (CTorus d L N₁ m₁ (k + 1)))) (e1DomG S))
    (hy1 : ∀ q, (commonLabels ((thickLabels (m₀ := 1) (j := k + 1) 𝒴₀ h𝒴₀).sum
        (commonLabels (thickLabels (m₀ := 1) (j := k + 1) 𝒴C h𝒴C) hN1 hL (fun _ => Set.univ)
          (fun τ => polyDom S.G' (X₁f τ) m₀ (jL τ) (𝒦X τ)) hdomC)) hN1 hL (fun _ => Set.univ)
        (e1DomG S) hdomE).ysite (y1 q) = bridge 1 z q.1.2)
    (G₁ : physParam N S →
      {q // q ∈ markedIdx (fun _ => (Set.univ : Set (CTorus d L N₁ m₁ (k + 1))))
        (fun τ => polyDom S.G' (X₁f τ) m₀ (jL τ) (𝒦X τ)) z} →
      ℂ → (∀ b, (S.blockSplit 1 hp).Ωb b) → ℂ)
    -- the read datum
    {D : BgData S.G' N} (hD : XiCData S.G' (compWeight L S.a₁) S.ν (k + 1) 1 eps D)
    (θ : physParam N S) (hθ : (θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) = rawOf D)
    (θb : physParamBg N Gl)
    (hθb : (θb.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) = clipRaw Gl (rawOf D))
    -- the step's activities and marks are the formulas at the step's own set
    (h0eq : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ Y Φ, (A₀ θ (s : ℂ)).H Y Φ =
      zeroActBg S S.G' (BgTransport.self S.hG') X₁V jV 𝒦XV 1 F₂ Sol₂ ω ρ₀ hp eps₀ θ (s : ℂ) Y.1 Φ)
    (h1eq : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ Y Φ, (AC θ (s : ℂ)).H Y Φ =
      oldActBg S S.G' (BgTransport.self S.hG') (S.blockU z) X₁f m₀ jL 𝒦X F₁L SolL
        (fun τ => eTermFun S.G' (Gk τ) (Gj τ) Hm ac (Fk τ) (E τ)) ρ hp Ru eps₀ 𝒴C θ Y (s : ℂ) Φ)
    (hG₁eq : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ q Φ, G₁ θ q (s : ℂ) Φ =
      oldMarkGBg S S.G' (BgTransport.self S.hG') (S.blockU z) X₁f m₀ jL 𝒦X F₁L SolL
        (fun τ => eTermFun S.G' (Gk τ) (Gj τ) Hm ac (Fk τ) (E τ)) ρ hp Ru eps₀ z θ q (s : ℂ) Φ)
    (hGdep : ∀ i s, DepOn (blocksOf 1 (k + 1) Set.univ
      ((commonLabels ((thickLabels (m₀ := 1) (j := k + 1) 𝒴₀ h𝒴₀).sum
        (commonLabels (thickLabels (m₀ := 1) (j := k + 1) 𝒴C h𝒴C) hN1 hL (fun _ => Set.univ)
          (fun τ => polyDom S.G' (X₁f τ) m₀ (jL τ) (𝒦X τ)) hdomC)) hN1 hL (fun _ => Set.univ)
        (e1DomG S) hdomE).ysite
        (Sum.elim (commonAnchor ({Y // Y ∈ 𝒴₀} ⊕ ({Y // Y ∈ 𝒴C} ⊕ RootUnionLb 1
          (fun _ => (Set.univ : Set (CTorus d L N₁ m₁ (k + 1))))
          (fun τ => polyDom S.G' (X₁f τ) m₀ (jL τ) (𝒦X τ)))) (fun _ => Set.univ) (e1DomG S) z)
          y1 i)))
      (Sum.elim (fun i u Φ => e1MarkGParamG S F₁b Solb ρ₀ hp z eps₀ θ i u Φ) (G₁ θ) i s))
    -- the polymer, its margin, and the determinant part
    (a : ℕ → ℝ) (aT ν' ρd : ℝ) (Zb : Finset (unitPts Gl))
    (T : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) 1 (k + 1) Set.univ))
    (hTmar : ∀ x ∈ sitesOf T, ∀ y, supDist x y ≤ 2 * L ^ (k + 1 + m₁) → y ∈ Gl.Ω (k + 1))
    (hdet : newLevelDetBg S.G' a aT ν' ρd (S.blockU z) θ T = newLevelDetBg Gl a aT ν' ρd Zb θb T) :
    newLevelDetBg S.G' a aT ν' ρd (S.blockU z) θ T +
        gsumCoeff (S.blockSplit 1 hp).μ
          (commonLabels ((thickLabels (m₀ := 1) (j := k + 1) 𝒴₀ h𝒴₀).sum
            (commonLabels (thickLabels (m₀ := 1) (j := k + 1) 𝒴C h𝒴C) hN1 hL (fun _ => Set.univ)
              (fun τ => polyDom S.G' (X₁f τ) m₀ (jL τ) (𝒦X τ)) hdomC)) hN1 hL (fun _ => Set.univ)
            (e1DomG S) hdomE)
          (commonAct (fun θ u => (A₀ θ u).sum (commonAct AC hN1 hL (fun _ => Set.univ)
              (fun τ => polyDom S.G' (X₁f τ) m₀ (jL τ) (𝒦X τ)) hdomC hε₁ hκ0 θ u))
            hN1 hL (fun _ => Set.univ) (e1DomG S) hdomE hε hκ0 θ)
          (Sum.elim (commonAnchor ({Y // Y ∈ 𝒴₀} ⊕ ({Y // Y ∈ 𝒴C} ⊕ RootUnionLb 1
            (fun _ => (Set.univ : Set (CTorus d L N₁ m₁ (k + 1))))
            (fun τ => polyDom S.G' (X₁f τ) m₀ (jL τ) (𝒦X τ)))) (fun _ => Set.univ) (e1DomG S) z)
            y1)
          (Sum.elim (fun i u Φ => e1MarkGParamG S F₁b Solb ρ₀ hp z eps₀ θ i u Φ) (G₁ θ)) T =
      newLevelCoeffBg Gl (S.blockSplit 1 hp).μ a aT ν' ρd Zb
        (commonLabels ((thickLabels (m₀ := 1) (j := k + 1) 𝒴₀ h𝒴₀).sum
          (commonLabels (thickLabels (m₀ := 1) (j := k + 1) 𝒴C h𝒴C) hN1 hL (fun _ => Set.univ)
            (fun τ => polyDom S.G' (X₁f τ) m₀ (jL τ) (𝒦X τ)) hdomC)) hN1 hL (fun _ => Set.univ)
          (e1DomG S) hdomE)
        (classActFun
          (fun θb u (Y : {Y // Y ∈ 𝒴₀}) Φ => zeroActBg S Gl (BgTransport.canon S.G' Gl N) X₁V jV
            𝒦XV 1 F₂' Sol₂' ω ρ₀ hp eps' θb u Y.1 Φ)
          (fun θb u Y Φ => oldActBg S Gl (BgTransport.canon S.G' Gl N) (maskPre S.hG' Gl (S.blockU z))
            X₁f m₀ jL 𝒦X F₁L' SolL' (fun τ => eTermFun Gl (Gk τ) (Gj τ) Gd ac (Fk τ) (E τ)) ρ hp Ru
            eps' 𝒴C θb Y u Φ))
        (Sum.elim (commonAnchor ({Y // Y ∈ 𝒴₀} ⊕ ({Y // Y ∈ 𝒴C} ⊕ RootUnionLb 1
          (fun _ => (Set.univ : Set (CTorus d L N₁ m₁ (k + 1))))
          (fun τ => polyDom S.G' (X₁f τ) m₀ (jL τ) (𝒦X τ)))) (fun _ => Set.univ) (e1DomG S) z) y1)
        (fun θb => Sum.elim
          (fun i u Φ => e1MarkGParamGBgOn S Gl (BgTransport.canon S.G' Gl N)
            (maskPre S.hG' Gl (S.blockU z)) F₁b' Solb' ρ₀ hp z Gl eps' θb i u Φ)
          (oldMarkGBg S Gl (BgTransport.canon S.G' Gl N) (maskPre S.hG' Gl (S.blockU z)) X₁f m₀ jL
            𝒦X F₁L' SolL' (fun τ => eTermFun Gl (Gk τ) (Gj τ) Gd ac (Fk τ) (E τ)) ρ hp Ru eps' z
            θb))
        θb T :=
  newLevelCoeffBg_class_canon_eq_of_det_gen S hG hA hSS hPd hdk hdtop hN hm₁ hM hag hagm hagl hagd
    hS HB HB' ha₁ ha₂ hκ hMc hMX hF₂ hM₂ h0 h0' h1 hδ₀ hδ₀' hδ₁ heps hsmall hc7 hphi heps₀ hεr
    hsmall' hc7' hphi' hδ₀a hδ₀e hmarD' hαD' hsm hρ₀ hρ₀c hρ hp hRu1 hRu hN1 hL 𝒴₀ h𝒴₀ hcovV hX₁V
    hzXV hF₂s hF₂s' hSol₂ hSol₂' ω hNm hcovL hX₁L Gk Gj hkX ac Fk E hS hκ hMc hMX hF₂ hM₂ h0 h0'
    h1 hδ₀ hδ₀' hδ₁ hc7 hphi hc7' hphi' hδ₀a hδ₀e hmarD' hαD' hsm hρc hRu hF₁L hF₁L' hSolL hSolL'
    𝒴C h𝒴C hdomC hF₁b hF₁b' hSolb hSolb' z hdomE A₀ AC hε₁ hε hκ0 y1 hy1 G₁ hD θ hθ θb hθb h0eq
    h1eq hG₁eq hGdep a aT ν' ρd Zb T hTmar hdet

end Assembly

end Balaban.Inhabited
