/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.NewLevelLocalCast
public import Balaban.Inhabited.NewLevelOldTermsClass
public import Balaban.Fluctuation.LocalClassDensityIrrelCount
public import Balaban.Fluctuation.HatPolyDom

/-!
# The family of the new level on the local sets, for a system of the class (route R-LOC, L5)

`NewLevelSystem.localFamily_castLocal_of` takes, besides the numerical conditions of the step and of
the local pairs, the settings of the old terms, their analyticity, bound and spin covariance on
their charts, and the bounds of the activities and marks of the cluster expansion in the class form
(`hεz`, `hεo`, `hFb`, `hFo`).  For a system whose old terms are the irrelevant terms of a class
(`OldTermsAreIrrel`, ruling R13) these are supplied here:

* the settings of the old terms are those the system carries (`NewLevelSystem.OS`);
* the analyticity, bound and covariance of the old terms on their charts come from the class
  clauses on the birth-mass domain and the bound of the class on its term domain (the open input
  A4-1b (ii)), through the inclusion of the charts (`oldTerm_charts_of_labels`);
* the bound of the old activities in the class form is the sum over the labels of the decaying
  label bounds (`classActivity_hnumH_of_uniform_mult`, with the label multiplicity `2^{L^d}` of
  `fibre_card_le`), times the amplitude `corrU / a_R` of Schwarz's lemma; the amplitude `ε_H` of the
  activities is the cap of the numerical condition of Theorem 3.4, which the zero-source and the old
  activity bounds are assumed not to exceed (`hsmZ`, `hsmO`, conditions on constants);
* the bounds `F₀` of the marks are chosen per anchor.

`NewLevelSystem.localFamily_of_class`: the clauses (A1)–(A5) of the family of the new level on the
cast local sets, for the coefficient of a system of the class.
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Fluctuation Balaban.Multiscale Balaban.Background Balaban.Localization
  Balaban.SmallField Balaban.SmallField.Def6 Balaban.SmallField.Def6v2 Balaban.SmallField.GsSpec
  Balaban.LargeField Balaban.Inhabited.MarkBudgetAudit Matrix

namespace NewLevelSystem

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}
  {S : StepSetting d L N₁ m₁ k N ϱ} {C : StepClass d L N₁ m₁ k N ϱ}
  {z : RootIdx d L N₁ m₁ (k + 1)} {t pp : ℝ} {Jr : S.JointRep t pp}
  (NS : NewLevelSystem S C z Jr)

open Classical in
/-- **The family of the new level on the cast local sets, for a system of the class** (route R-LOC,
L5; rulings R2, R6, R13).  For the coefficient `e` of a system `NS` of the step on its chart
(`he`, supported on the polymers rooted at `z`), whose old terms are the irrelevant terms of the
class `C` composed on its generating sets (`OldTermsAreIrrel`): if the class terms satisfy the
clauses on the birth-mass domain (`hcl`) with the class weights those of the step (`hA`), the birth
masses within the factor `1 + τ_m` of the step mass (`hμ`), the (DL-gap) of the charts of the old
terms (`hDL`) and the bound of the class on its term domain with its decay in the level
(`hB`, `hEbI`, `hEbL`; the open input A4-1b (ii)), then under the numerical conditions of
`localFamily_castLocal_of` that do not concern the old terms, the rate `κ_H ≤ 2κ_dec - 1` of the
activities (`hrate`) and the smallness of the zero-source and old activity bounds against the cap of
Theorem 3.4 (`hsmZ`, `hsmO`), there are a family `f T` of the pair of fields and bounds `b T` with
(A1)–(A5) on the cast local sets `castG hc (𝔹_{k+1}(Yp Y⁺(T)))`. -/
theorem localFamily_of_class [NeZero N] (hO : OldTermsAreIrrel S C NS.O)
    (hS1 : S.a₁ = 1) (hβS : 0 < S.β) (hd : 3 ≤ d)
    (SpG : DGSetting S.G' (compWeight L S.a₁) S.ν)
    -- the class
    {P : Consts} (Rg : Regime L) (a : ℕ → ℝ) (hPm : P.m₀ = C.m₀) (hm1 : 1 ≤ C.m₀)
    (hcl : SFTermClauses P (birthXiDom P Rg a N₁) C.Tm)
    (hA : aIdeal L (k + 1) (a (k + 1)) = compWeight L S.a₁)
    (H : BgHyp d L (k + 1) ϱ (compWeight L S.a₁) S.ν)
    (H' : ∀ j, 1 ≤ j → j ≤ k → BgHyp d L (k + 1) ϱ (compWeight L S.a₁) (physMass L j (Rg.ν j)))
    {τm rm : ℝ}
    (hμ : ∀ j, 1 ≤ j → j ≤ k → ∃ tm, physMass L j (Rg.ν j) = S.ν * (1 + tm) ∧ |tm| ≤ τm)
    (hτr : τm < rm) (hrm : rm ≤ 1 / 16)
    (hδ₃0 : 0 ≤ NS.OS.δ₃) (hδfl0 : 0 ≤ NS.OS.δfl)
    (hDL : ∀ j, 1 ≤ j → j ≤ k →
      (2 * (t + xiK2 d L N * NS.OS.δ₃ + xiK2 d L N * NS.OS.δfl) + 2 * ((N : ℝ) + 1) *
        (cK2 d L N * (t + xiK2 d L N * NS.OS.δ₃ + xiK2 d L N * NS.OS.δfl) ^ 2)) *
        (1 + (1 + 16 * ((N : ℝ) + 1) * cK2 d L N) * τm) ≤ P.eps d L j)
    (hsmε : ∀ j, 1 ≤ j → j ≤ k → (4 * d + 6) * ((2 * d + 1) * P.eps d L j) ≤ 1)
    (hc1ε : ∀ j, 1 ≤ j → j ≤ k → 4 * (xiC1 d * P.eps d L j) ≤ bgC1 d L N)
    (hKε : ∀ j, 1 ≤ j → j ≤ k → bgK1 d L N * (xiC1 d * P.eps d L j) + 3 * rm ≤ deltaStar d L N)
    (hζε : ∀ j, 1 ≤ j → j ≤ k → 8 * P.eps d L j * rm ≤ deltaStar d L N)
    -- the bound of the class on its term domain (A4-1b (ii)) and its decay in the level
    {κdec : ℝ}
    (Bl : ℕ → CTorus d L N₁ m₁ (k + 1) → Set (CTorus d L N₁ m₁ (k + 1)) → ℝ)
    (hBl : ∀ j y X, 0 ≤ Bl j y X)
    (hB : ∀ (i₀ i₁ : Fin N) (j : ℕ) (y : CTorus d L N₁ m₁ (k + 1))
      (X : Set (CTorus d L N₁ m₁ (k + 1))), 1 ≤ j → j ≤ k → IsPolyDom C.m₀ j X → y ∈ X →
      ∀ Ψ h : Fld d L N₁ m₁ (k + 1) N, (birthXiDom P Rg a N₁).dom j (C.Tm.gs j X) Ψ h →
      dot (Ψ y) (Ψ y) ∈ Complex.slitPlane →
      ‖irrelTorus C.m₀ C.Tm i₀ i₁ j y X Ψ h‖ ≤
        Bl j y X * Real.exp (-(κdec - 1) * treeLenCovOne C.m₀ j X))
    {CI KL α₃ : ℝ} (n₁ : ℕ) (hCI : 0 ≤ CI) (hKL : 0 ≤ KL) (hα₃ : 0 < α₃) (hE₀ : 0 ≤ P.E₀)
    (hEbI : ∀ j y X, j + n₁ ≤ k →
      Bl j y X ≤ CI * P.E₀ * ((((L : ℝ)⁻¹ ^ (k - j)) ^ ((d : ℝ) + α₃))))
    (hEbL : ∀ j y X, k < j + n₁ → Bl j y X ≤ KL * P.E₀)
    -- the local sets
    {N₁' m₁' : ℕ} [NeZero N₁'] (hc : N₁' * L ^ m₁' = N₁ * L ^ m₁) (hm : m₁ + 2 ≤ m₁')
    (hsep : ϱ ≤ minSep L (L ^ m₁'))
    (Yp : Set (CTorus d L N₁ m₁ (k + 1)) → Set (CTorus d L N₁' m₁' (k + 1)))
    (hmarg : ∀ (T : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) 1 (k + 1)
        Set.univ)), ∀ x ∈ sitesOf T, ∀ y : CTorus d L N₁ m₁ (k + 1),
      supDist x y ≤ 2 * L ^ (k + 1 + m₁') →
      y ∈ (castG hc (localB (k + 1) (le_refl (k + 1))
        (Yp (sitesOf (piHull P.m₀ (thickSet S.G' (sitesOf T))))) hsep)).Ω (k + 1))
    -- the numerical conditions of the step and of the local pairs
    {eps' : ℝ} (hle : t ≤ eps') (hεr : (2 * bgK1 d L N + 2) * xiC1 d * t ≤ eps')
    (hεt : P.eps d L (k + 1) ≤ t)
    {c c₂ : ℝ} (hS : Dec2.DecSpecs d L (Dec2.mixedKc d L) (Cchi d L) c NS.BG)
    {ϱf : ℝ} {Hf : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱf}
    {Kc₀ Cx₀ c₂₀ : ℝ}
    (hCs : FlCore N S.G' Hf S.a₁ S.ν c NS.BG NS.κ t Kc₀ Cx₀ c₂₀ NS.BG₂ t)
    (hCs' : FlCore N S.G' Hf S.a₁ S.ν c NS.BG NS.κ eps' Kc₀ Cx₀ c₂₀ NS.BG₂ t)
    (hS2m : Dec2.DecSpecs d L (Dec2.mixedKc d L) (Cchi d L) c₂ NS.BG₂)
    (hM2m : c₂ * Real.exp (N0 d L * NS.κ) ≤ (L : ℝ) ^ m₁)
    (hMXd : Dec2.cstarX d L (Cchi d L) * Real.exp (N0 d L * NS.κ) ≤ (L : ℝ) ^ m₁)
    (hMXn : cstarX d L * Real.exp (N0 d L * NS.κ) ≤ (L : ℝ) ^ m₁)
    {δc : ℝ} (hδc : 0 ≤ δc)
    (hdm : decDomMargin d L N NS.BG NS.κ (xiC1 d * t) < δc)
    (hα : K4 d L N NS.BG NS.κ * (xiC1 d * t) < coerciveConst d / 2)
    (hdm' : decDomMargin d L N NS.BG NS.κ (xiC1 d * eps') < δc)
    (hα' : K4 d L N NS.BG NS.κ * (xiC1 d * eps') < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L NS.κ ≤ 1 / 4)
    {cψ : ℝ} (hcψ : 0 ≤ cψ) (hρ₀c : 2 * NS.p₁ ≤ cψ) (hρp : S.p₁ ≤ NS.p₁)
    (hRu : corrU * markedRad d L N k S.a₁ NS.κ cψ ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) < t)
    (hBG₂ : 0 ≤ NS.BG₂)
    {κ₀ : ℝ} (hκ₀ : 0 ≤ κ₀) (hκ₀e : aEnt d L + 1 ≤ κ₀) (hκdec : 3 * κ₀ + 3 ≤ κdec)
    (hκκ : 4 * d * (((2 * L + 1) ^ d : ℕ) : ℝ) * κdec ≤ NS.κ) (h1 : 1 ≤ (NS.κ / 2 - 1) / 2)
    (hlog : Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) * (((L ^ 1) ^ d : ℕ) : ℝ)) ≤ (NS.κ / 2 - 1) / 2)
    {R₁ r : ℝ} (hR₁ : 1 < R₁) (hr : 0 < r) (hrays : (2 * R₁ + r) * NS.p₁ ≤ cψ)
    {R U : ℝ} (hR : 0 < R)
    (hRR : (R + R) * markedRad d L N k S.a₁ NS.κ cψ ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) < t)
    (hUR : 2 * U ≤ R) (hU : 17 / 16 ≤ U)
    {c₂L : ℝ}
    (hSL : Dec2.DecSpecs d L (Dec2.mixedKc d L) (Cchi d L) NS.OS.cB NS.O.BG)
    {ϱfL : ℝ} {HfL : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱfL}
    {KcL₀ CxL₀ c₂L₀ : ℝ}
    (hCLs : FlCore N S.G' HfL S.a₁ S.ν NS.OS.cB NS.O.BG NS.O.κ t KcL₀ CxL₀ c₂L₀ NS.O.BG₂ NS.O.δ₁)
    (hCLs' : FlCore N S.G' HfL S.a₁ S.ν NS.OS.cB NS.O.BG NS.O.κ eps' KcL₀ CxL₀ c₂L₀ NS.O.BG₂
      NS.O.δ₁)
    (hS2mL : Dec2.DecSpecs d L (Dec2.mixedKc d L) (Cchi d L) c₂L NS.O.BG₂)
    (hM2mL : c₂L * Real.exp (N0 d L * NS.O.κ) ≤ (L : ℝ) ^ m₁)
    (hMXLd : Dec2.cstarX d L (Cchi d L) * Real.exp (N0 d L * NS.O.κ) ≤ (L : ℝ) ^ m₁)
    (hMXLn : cstarX d L * Real.exp (N0 d L * NS.O.κ) ≤ (L : ℝ) ^ m₁)
    {δcL : ℝ}
    (hdmL : decDomMargin d L N NS.O.BG NS.O.κ (xiC1 d * t) < δcL)
    (hαL : K4 d L N NS.O.BG NS.O.κ * (xiC1 d * t) < coerciveConst d / 2)
    (hdmL' : decDomMargin d L N NS.O.BG NS.O.κ (xiC1 d * eps') < δcL)
    (hαL' : K4 d L N NS.O.BG NS.O.κ * (xiC1 d * eps') < coerciveConst d / 2)
    (hsmL : δcL ^ 2 * smallConstX d L NS.O.κ ≤ 1 / 4)
    {cψL : ℝ} (hcψL : 0 ≤ cψL)
    (hκκL : 4 * d * (((2 * L + 1) ^ d : ℕ) : ℝ) * κdec ≤ NS.O.κ) (h1L : 1 ≤ (NS.O.κ / 2 - 1) / 2)
    (hlogL : Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) * (((L ^ NS.O.m₀) ^ d : ℕ) : ℝ)) ≤
      (NS.O.κ / 2 - 1) / 2)
    (hρL : 0 < NS.O.ρ) (hρcL : NS.O.ρ ≤ cψL) (hρpL : S.p₁ ≤ NS.O.ρ)
    (hRuL : corrU * markedRad d L N k S.a₁ NS.O.κ cψL ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) <
      NS.O.δ₁)
    {aR : ℝ} (hca : corrU ≤ aR)
    (haL : aR * markedRad d L N k S.a₁ NS.O.κ cψL ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) < NS.O.δ₁)
    {t₀ : ℝ} (ht₀ : 0 < t₀)
    (hRt : (corrU + t₀) *
      markedRad d L N k S.a₁ NS.O.κ cψL ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) < NS.O.δ₁)
    {δ₃' δfl' : ℝ}
    (hCN' : ChainNum d L N m₁ NS.O.BG NS.O.κ NS.OS.r₀ eps' δ₃')
    (hFN' : FlNum d L N NS.O.BG NS.O.BG₂ NS.O.κ eps' δ₃' NS.O.δ₁ δfl')
    (hrb : NS.OS.r₀ * (L : ℝ) ^ m₁ ≤ ϱ - 1)
    -- the rates and the smallness of the activities (Theorem 3.4)
    {κH κ' : ℝ} (hκH : κH ≤ 2 * κdec - 1) (hκH0 : 0 ≤ κH)
    (hrate : κH * ((L : ℝ) ^ (C.m₀ - 1) + 2 * d * (L : ℝ) ^ C.m₀ *
      (((L ^ (C.m₀ - 1)) ^ d : ℕ) : ℝ) * c1 d L) + 1 ≤ 2 * κdec)
    (hκ' : 0 ≤ κ') (hκ : κ' + 3 * NS.Z.κ0 + c1 d L + 3 / 2 ≤ κH)
    (hsmZ : 8 * (|S.β| * (6 * (1 / 2) * c1 d L * ((L : ℝ) ^ (1 + m₁)) ^ d *
      ‖energyBdScaled d L N (compWeight L S.a₁) k (cK2' d L N (famConst d L NS.BG₂ NS.κ) * t) t
        (rho4 d L N NS.BG NS.κ)‖ / r ^ 3)) ≤
      1 / (8 * (2 * (K0 d L NS.Z.κ0 + 1) + (K0 d L NS.Z.κ0 +
        rootUnionK d L 1 m₁ NS.Z.κ0) + rootUnionK d L 1 m₁ NS.Z.κ0) ^ 3 * c1 d L *
        Real.exp ((κH - 2 * NS.Z.κ0) * cG d L + c1 d L + κ' * cG d L)))
    (hsmO : corrU / aR *
      (((2 ^ L ^ d : ℕ) : ℝ) * (c1 d L * ((((L : ℝ) ^ (1 + C.m₀ + m₁)) ^ d) * P.E₀ *
        (2 * K0 d L κ₀ * (CI * Real.exp ((κdec - 1) * cG d L) * (1 - (L : ℝ) ^ (-α₃))⁻¹ +
          n₁ * (KL * Real.exp ((κdec - 1) * cG d L)) * ((((L : ℝ) ^ (n₁ - 1)) ^ d))))) *
        Real.exp (κH * (2 * (d : ℝ) * (L : ℝ) ^ C.m₀ *
          ((((L ^ (C.m₀ - 1)) ^ d : ℕ)) : ℝ) * c1 d L)))) ≤
      1 / (8 * (2 * (K0 d L NS.Z.κ0 + 1) + (K0 d L NS.Z.κ0 +
        rootUnionK d L 1 m₁ NS.Z.κ0) + rootUnionK d L 1 m₁ NS.Z.κ0) ^ 3 * c1 d L *
        Real.exp ((κH - 2 * NS.Z.κ0) * cG d L + c1 d L + κ' * cG d L)))
    (hι : Nonempty ({Y' // Y' ∈ bridgeFamily 1
      (fun _ : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) =>
        (Set.univ : Set (CTorus d L N₁ m₁ (k + 1)))) (e1DomG S) z} ⊕
      {q // q ∈ markedIdx (fun _ : NS.O.ι => (Set.univ : Set (CTorus d L N₁ m₁ (k + 1))))
        (fun τ => polyDom S.G' (NS.O.X₁f τ) NS.O.m₀ (NS.O.jL τ) (NS.O.𝒦X τ)) z}))
    (hz : ((detDeg d L + 1 : ℕ) : ℝ) ^ 2 * (2 / Real.exp NS.κ) < 1)
    {c₃ : ℝ}
    (hS3 : Dec2.DecSpecs d L (Dec2.selfKc d L) (Cchi d L) c₃ NS.BG)
    (hM3 : c₃ * Real.exp (N0 d L * NS.κ) ≤ (L : ℝ) ^ m₁)
    (hc0 : xiC1 d * t ≤ bgC0 d L N)
    (hN1 : L ^ 1 ∣ N₁)
    -- the coefficient of the system on the step chart, supported on the rooted polymers
    (e : physParam N S → Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) 1
      (k + 1) Set.univ) → ℂ)
    (he : ∀ θ ∈ physV S S.a₁ S.ν t, ∀ T, e θ T = NS.coeff θ T)
    (hsupp : ∀ θ T, e θ T ≠ 0 → rootCube (m₀ := 1) z ∈ T ∧ IsPolyDom 1 (k + 1) (sitesOf T))
    (π : RawData d L (N₁ * L ^ m₁) (k + 1) N →L[ℂ] rawSub N S.G')
    (hπ : ∀ r (h : r ∈ rawSub N S.G'), π r = ⟨r, h⟩) :
    ∃ (f : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) 1 (k + 1) Set.univ) →
        Def6.Fld d L N₁ m₁ (k + 1) N × Def6.Fld d L N₁ m₁ (k + 1) N → ℂ)
      (b : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) 1 (k + 1) Set.univ) →
        ℝ),
      (∀ T, IsPolyDom P.m₀ (k + 1) (sitesOf (piHull P.m₀ (thickSet S.G' (sitesOf T)))) →
        AnalyticOnNhd ℂ (f T)
          {p | (xiFieldDom S.a S.ν (P.eps d L) : FieldDom d L N₁ m₁ (k + 1) N ϱ).dom (k + 1)
            (castG hc (localB (k + 1) (le_refl (k + 1))
                (Yp (sitesOf (piHull P.m₀ (thickSet S.G' (sitesOf T))))) hsep)) p.1 p.2}) ∧
      (∀ T, IsPolyDom P.m₀ (k + 1) (sitesOf (piHull P.m₀ (thickSet S.G' (sitesOf T)))) →
        ∀ p : Def6.Fld d L N₁ m₁ (k + 1) N × Def6.Fld d L N₁ m₁ (k + 1) N,
        (xiFieldDom S.a S.ν (P.eps d L) : FieldDom d L N₁ m₁ (k + 1) N ϱ).dom (k + 1)
          (castG hc (localB (k + 1) (le_refl (k + 1))
              (Yp (sitesOf (piHull P.m₀ (thickSet S.G' (sitesOf T))))) hsep)) p.1 p.2 →
        ‖f T p‖ ≤ b T) ∧
      (∀ T, IsPolyDom P.m₀ (k + 1) (sitesOf (piHull P.m₀ (thickSet S.G' (sitesOf T)))) →
        ∀ p p' : Def6.Fld d L N₁ m₁ (k + 1) N × Def6.Fld d L N₁ m₁ (k + 1) N,
        (xiFieldDom S.a S.ν (fun j => (2 * bgK1 d L N + 2) * xiC1 d * P.eps d L j) :
          FieldDom d L N₁ m₁ (k + 1) N ϱ).dom (k + 1)
          (castG hc (localB (k + 1) (le_refl (k + 1))
              (Yp (sitesOf (piHull P.m₀ (thickSet S.G' (sitesOf T))))) hsep)) p.1 p.2 →
        (xiFieldDom S.a S.ν (fun j => (2 * bgK1 d L N + 2) * xiC1 d * P.eps d L j) :
          FieldDom d L N₁ m₁ (k + 1) N ϱ).dom (k + 1)
          (castG hc (localB (k + 1) (le_refl (k + 1))
              (Yp (sitesOf (piHull P.m₀ (thickSet S.G' (sitesOf T))))) hsep)) p'.1 p'.2 →
        (∀ x ∈ sitesOf (piHull P.m₀ (thickSet S.G' (sitesOf T))), p.1 x = p'.1 x ∧ p.2 x = p'.2 x) →
        f T p = f T p') ∧
      (∀ T, IsPolyDom P.m₀ (k + 1) (sitesOf (piHull P.m₀ (thickSet S.G' (sitesOf T)))) →
        ∀ Q : Matrix (Fin N) (Fin N) ℝ, Qᵀ * Q = 1 →
        ∀ p : Def6.Fld d L N₁ m₁ (k + 1) N × Def6.Fld d L N₁ m₁ (k + 1) N,
        (xiFieldDom S.a S.ν (P.eps d L) : FieldDom d L N₁ m₁ (k + 1) N ϱ).dom (k + 1)
          (castG hc (localB (k + 1) (le_refl (k + 1))
              (Yp (sitesOf (piHull P.m₀ (thickSet S.G' (sitesOf T))))) hsep)) p.1 p.2 →
        f T (rotField (cmat Q) p.1, rotField (cmat Q) p.2) = f T p) ∧
      (∀ T (q : Def6.Fld d L N₁ m₁ (k + 1) N × Def6.Fld d L N₁ m₁ (k + 1) N),
        Def6.XiDom S.G' S.a S.ν (k + 1) (P.eps d L (k + 1)) q.1 q.2 →
        f T q = e (π (clipRaw S.G' q), 0) T) := by
  classical
  obtain ⟨hm0, i₀, i₁, y, X, hE, hlab, hinj⟩ := hO
  have hL2 : 2 ≤ L := NS.hL
  have hN : L ^ NS.O.m₀ ∣ N₁ := NS.OS.hN
  have hNP : L ^ P.m₀ ∣ N₁ := by rw [hPm, ← hm0]; exact hN
  have hκ1 : 1 ≤ κdec := by linarith
  have ht0 : 0 < t := hCs.eps_pos
  have hK2 : 0 < xiK2 d L N := by
    have := cK2_pos d L N
    unfold xiK2; positivity
  have he0 : 0 < 1 ^ 2 * t + xiK2 d L N * NS.OS.δ₃ + xiK2 d L N * NS.OS.δfl := by
    have := mul_nonneg hK2.le hδ₃0
    have := mul_nonneg hK2.le hδfl0
    simp only [one_pow, one_mul]
    linarith
  -- the old terms on their charts, from the class
  obtain ⟨hEan, hEbd, hEr⟩ := NS.oldTerm_charts_of_labels Rg a hPm hcl hA H H' (b := 1)
    (e := 1 ^ 2 * t + xiK2 d L N * NS.OS.δ₃ + xiK2 d L N * NS.OS.δfl) le_rfl he0 hμ hτr hrm
    (fun j hj1 hjk => by simpa only [one_pow, one_mul] using hDL j hj1 hjk) hsmε hc1ε hKε hζε hκ1
    Bl hBl hB hm0 i₀ i₁ y X hE hlab
  -- the labels, their polymers and their multiplicity
  have hjk : ∀ τ, NS.O.jL τ ≤ k := fun τ => (hlab τ).2.2.1
  have hj1 : ∀ τ, 1 ≤ NS.O.jL τ := fun τ => (hlab τ).2.1
  have hXL : ∀ τ, NS.O.XL τ = X τ ∪ Localization.box (cbase (cellSide L C.m₀ m₁ (NS.O.jL τ)) (y τ) -
      natT fun _ => L / 2 * cellSide L C.m₀ m₁ (NS.O.jL τ))
        (L * cellSide L C.m₀ m₁ (NS.O.jL τ)) := fun τ => (hlab τ).2.2.2.2.2.2
  have hNC : L ^ C.m₀ ∣ N₁ := hm0 ▸ hN
  have hXLpoly : ∀ τ, IsPolyDom C.m₀ (NS.O.jL τ) (NS.O.XL τ) := fun τ => by
    rw [hXL τ]
    exact isPolyDom_union (hlab τ).2.2.2.2.1
      (isPolyDom_cubeAt hNC ((hjk τ).trans (Nat.le_succ k)) (y τ)) (hlab τ).2.2.2.2.2.1
      (mem_cubeAt (y τ))
  have hyXL : ∀ τ, y τ ∈ NS.O.XL τ := fun τ => by
    rw [hXL τ]; exact Or.inl (hlab τ).2.2.2.2.2.1
  have hmult : ∀ τ, (Finset.univ.filter fun τ' : NS.O.ι =>
      NS.O.jL τ' = NS.O.jL τ ∧ y τ' = y τ ∧ NS.O.XL τ' = NS.O.XL τ).card ≤ 2 ^ L ^ d := fun τ => by
    simp only [hXL]
    exact fibre_card_le hNC NS.O.jL (fun τ => (hjk τ).trans (Nat.le_succ k)) y X
      (fun τ => (hlab τ).2.2.2.2.1) hinj τ
  have hdj : ∀ Y ∈ NS.𝒴C, IsDj C.m₀ (k + 1) Y := by
    intro Y hY
    rw [NS.h𝒴, Finset.mem_biUnion] at hY
    obtain ⟨τ, -, hYτ⟩ := hY
    have h := isDj_of_polyDom S.hG' (NS.OS.hcov τ) hd (NS.OS.hopt τ) hYτ
    rwa [hm0] at h
  -- the amplitude of the activities and the bounds of the marks
  set εcap : ℝ := 1 / (8 * (2 * (K0 d L NS.Z.κ0 + 1) + (K0 d L NS.Z.κ0 +
        rootUnionK d L 1 m₁ NS.Z.κ0) + rootUnionK d L 1 m₁ NS.Z.κ0) ^ 3 * c1 d L *
        Real.exp ((κH - 2 * NS.Z.κ0) * cG d L + c1 d L + κ' * cG d L)) with hεcap
  have hεpos : 0 < εcap := by
    have h0 := K0_pos d L NS.Z.κ0
    have h1' := rootUnionK_nonneg (d := d) (L := L) (m₁ := m₁) 1 NS.Z.κ0
    have hc1 : 0 < c1 d L := zero_lt_one.trans_le (one_le_c1 d L)
    rw [hεcap]
    positivity
  set Eb : NS.O.ι → ℝ := fun τ =>
    |S.β|⁻¹ * Bl (NS.O.jL τ) (y τ) (X τ) * Real.exp ((κdec - 1) * cG d L) with hEbdef
  have hEb : ∀ τ, 0 ≤ Eb τ := fun τ => by
    have := hBl (NS.O.jL τ) (y τ) (X τ)
    simp only [hEbdef]; positivity
  set F0 : ({Y' // Y' ∈ bridgeFamily 1 (fun _ : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) =>
      (Set.univ : Set (CTorus d L N₁ m₁ (k + 1)))) (e1DomG S) z} ⊕
      {q // q ∈ markedIdx (fun _ : NS.O.ι => (Set.univ : Set (CTorus d L N₁ m₁ (k + 1))))
        (fun τ => polyDom S.G' (NS.O.X₁f τ) NS.O.m₀ (NS.O.jL τ) (NS.O.𝒦X τ)) z}) → ℝ :=
    Sum.elim (fun _ => max (‖(S.β : ℂ)‖ * 4 * ‖energyBdScaled d L N (compWeight L S.a₁) k
          (cK2' d L N (famConst d L NS.BG₂ NS.κ) * t) t (rho4 d L N NS.BG NS.κ)‖ * U ^ 2 / R ^ 3 *
          (c1 d L * ((L : ℝ) ^ (1 + m₁)) ^ d) *
          ((nFibre d L : ℝ) * Real.exp ((2 * κdec - 1) * cBr d L))) 1)
      (fun q => max (|S.β| * (Eb q.1.1 * Real.exp (-κ₀ * treeLenCovOne NS.O.m₀ (NS.O.jL q.1.1)
        (NS.O.XL q.1.1) - 2 * κdec * treeLenCov S.G' NS.O.m₀ q.1.2) / t₀) *
          Real.exp ((2 * κdec - 1) * treeLenCovOne 1 (k + 1) (bridge 1 z q.1.2))) 1) with hF0def
  have hF0 : ∀ i, 0 < F0 i := by
    rintro (i | q)
    · exact lt_of_lt_of_le zero_lt_one (le_max_right _ _)
    · exact lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hFb : ∀ i, ‖(S.β : ℂ)‖ * 4 * ‖energyBdScaled d L N (compWeight L S.a₁) k
          (cK2' d L N (famConst d L NS.BG₂ NS.κ) * t) t (rho4 d L N NS.BG NS.κ)‖ * U ^ 2 / R ^ 3 *
          (c1 d L * ((L : ℝ) ^ (1 + m₁)) ^ d) *
          ((nFibre d L : ℝ) * Real.exp ((2 * κdec - 1) * cBr d L)) ≤ F0 (Sum.inl i) :=
    fun _ => le_max_left _ _
  have hFo : ∀ q, |S.β| * (Eb q.1.1 * Real.exp (-κ₀ * treeLenCovOne NS.O.m₀ (NS.O.jL q.1.1)
        (NS.O.XL q.1.1) - 2 * κdec * treeLenCov S.G' NS.O.m₀ q.1.2) / t₀) ≤
      F0 (Sum.inr q) * Real.exp (-(2 * κdec - 1) * treeLenCovOne 1 (k + 1) (bridge 1 z q.1.2)) := by
    intro q
    have h := mul_le_mul_of_nonneg_right (le_max_left (|S.β| * (Eb q.1.1 *
      Real.exp (-κ₀ * treeLenCovOne NS.O.m₀ (NS.O.jL q.1.1) (NS.O.XL q.1.1) -
        2 * κdec * treeLenCov S.G' NS.O.m₀ q.1.2) / t₀) *
          Real.exp ((2 * κdec - 1) * treeLenCovOne 1 (k + 1) (bridge 1 z q.1.2))) 1)
      (Real.exp_pos (-(2 * κdec - 1) * treeLenCovOne 1 (k + 1) (bridge 1 z q.1.2))).le
    rw [mul_assoc, ← Real.exp_add, show (2 * κdec - 1) * treeLenCovOne 1 (k + 1)
      (bridge 1 z q.1.2) + -(2 * κdec - 1) * treeLenCovOne 1 (k + 1) (bridge 1 z q.1.2) = 0 by
        ring, Real.exp_zero, mul_one] at h
    exact h
  -- the bound of the old activities in the class form
  have hεo : ∀ Y ∈ NS.𝒴C, corrU / aR * (|S.β| * (∑ τ, if Y ∈ polyDom S.G' (NS.O.X₁f τ) NS.O.m₀
      (NS.O.jL τ) (NS.O.𝒦X τ) then 2 * (Eb τ * Real.exp (-κ₀ * treeLenCovOne NS.O.m₀ (NS.O.jL τ)
        (NS.O.XL τ) - 2 * κdec * treeLenCov S.G' NS.O.m₀ Y)) else 0)) ≤
      εcap * Real.exp (-κH * treeLenCovOne 1 (k + 1) Y) := by
    intro Y hY
    have hβ0 : |S.β| ≠ 0 := (abs_pos.2 hβS.ne').ne'
    have hsum := classActivity_hnumH_of_uniform_mult S hm1 hNC hL2 hκ₀e hκH0 hrate NS.O.jL y
      NS.O.XL NS.O.X₁f NS.O.𝒦X (fun τ => ⟨hj1 τ, hjk τ⟩) hXLpoly hyXL (fun τ => (hlab τ).2.2.2.1)
      (2 ^ L ^ d) hmult (fun τ => hm0 ▸ NS.OS.hcov τ) NS.𝒴C hdj
      (fun τ => Bl (NS.O.jL τ) (y τ) (X τ) * Real.exp ((κdec - 1) * cG d L)) n₁
      (mul_nonneg hCI (Real.exp_pos _).le) (mul_nonneg hKL (Real.exp_pos _).le) hE₀ hα₃
      (fun τ h => by
        have := mul_le_mul_of_nonneg_right (hEbI _ (y τ) (X τ) h) (Real.exp_pos
          ((κdec - 1) * cG d L)).le
        calc _ ≤ _ := this
          _ = _ := by ring)
      (fun τ h => by
        have := mul_le_mul_of_nonneg_right (hEbL _ (y τ) (X τ) h) (Real.exp_pos
          ((κdec - 1) * cG d L)).le
        calc _ ≤ _ := this
          _ = _ := by ring) Y hY
    have heq : |S.β| * (∑ τ, if Y ∈ polyDom S.G' (NS.O.X₁f τ) NS.O.m₀ (NS.O.jL τ) (NS.O.𝒦X τ)
        then 2 * (Eb τ * Real.exp (-κ₀ * treeLenCovOne NS.O.m₀ (NS.O.jL τ) (NS.O.XL τ) -
          2 * κdec * treeLenCov S.G' NS.O.m₀ Y)) else 0) =
        ∑ τ, if Y ∈ polyDom S.G' (NS.O.X₁f τ) C.m₀ (NS.O.jL τ) (NS.O.𝒦X τ) then
          2 * (Bl (NS.O.jL τ) (y τ) (X τ) * Real.exp ((κdec - 1) * cG d L)) *
            Real.exp (-κ₀ * treeLenCovOne C.m₀ (NS.O.jL τ) (NS.O.XL τ) -
              2 * κdec * treeLenCov S.G' C.m₀ Y) else 0 := by
      rw [Finset.mul_sum, hm0]
      refine Finset.sum_congr rfl fun τ _ => ?_
      split_ifs
      · simp only [hEbdef]
        field_simp
      · simp
    have hca0 : 0 ≤ corrU / aR := div_nonneg corrU_pos.le (corrU_pos.trans_le hca).le
    rw [heq]
    have h2 := mul_le_mul_of_nonneg_left hsum hca0
    have h3 := mul_le_mul_of_nonneg_right hsmO
      (Real.exp_pos (-κH * treeLenCovOne 1 (k + 1) Y)).le
    linarith [h2, h3]
  exact NS.localFamily_castLocal_of hS1 SpG hc hm hsep hNP Yp hmarg hle hεr hεt hS hCs hCs' hS2m hM2m hMXd
    (Cchi_nonneg d L) hMXn hδc hdm hα hdm' hα' hsm hcψ hρ₀c hρp hRu hBG₂ hκ₀ hκdec hκκ h1 hlog
    hR₁ hr hrays hR hRR hUR hU hSL hCLs hCLs' hS2mL hM2mL hMXLd hMXLn hdmL hαL hdmL' hαL' hsmL hcψL hκκL h1L
    hlogL hρL hρcL hρpL hRuL hca haL ht₀ hRt hN NS.OS.hcov NS.OS.hX₁ NS.OS.hopt hEb le_rfl
    (one_le_scaledC0 d) (X₀ := NS.OS.X₀) NS.OS.hB NS.OS.hF hCN' hFN' S.hG hrb NS.OS.hFkan hEan
    hEbd hEr hκH hsmZ hεo hFb hFo hεpos hι hF0 hκ' hκ le_rfl hz hS3 hM3 hc0 hN1
    (fun _ _ => 0) (fun _ _ => rfl) e he hsupp π hπ

end NewLevelSystem

end Balaban.Inhabited
