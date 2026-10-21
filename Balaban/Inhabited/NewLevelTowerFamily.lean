/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.NewLevelLocalFamilyClass
public import Balaban.Inhabited.NewLevelHatLocal
public import Balaban.Inhabited.NewLevelNumerics
public import Balaban.Inhabited.E1LabelsBudgetG
public import Balaban.Inhabited.DetOutputTermsWitnessG
public import Balaban.Fluctuation.BirthMassFlow
public import Balaban.Fluctuation.LocalClassDensityIrrelBaseSet

/-!
# The clauses (A1)–(A5) of the new level at a step of a tower (route R-LOC, L5; blocker 6)

The step `S = hatStepKG …` of a tower `Tk` (the step of the class chain at the scale `k`) and a
family `e` of the new level which is the coefficient of a system of the class (`NewLevelFormula`
with the constants of the chain, in the regime `ClassHatCond` of ruling R13): the clauses
(A1)–(A5) of `newLabels_castInputs_of_localFamily` hold for `e` on the cast local sets
`castG hc (𝔹_{k+1}(Ŷ⁺(T′)))`, `Ŷ = hatSet m₀ (k + 1) Y`, read on the torus of the cube exponent `s`.

The premises are those of the class (its clauses on the birth-mass domain, its weights, its flow,
the bound of its irrelevant terms on their term domain with its decay in the level: the open input
A4-1b (ii)), the numerics bundle of the new level `NewLevelNumerics`, and the conditions on the
constants of the step that L5 uses beyond it (the radii of the zero-source and bridge marks, the
smallness of their bound and of the class bound against the cap of Theorem 3.4, the marked radius
of the old terms, and the (DL-gap) of the charts of the old terms at their birth masses).  The
settings, the constants and the inclusion of the charts of the old terms are supplied by the system,
the tower and `NewLevelSystem.localFamily_of_class`.

* `StepTowerG.newLevel_localFamily_of_class`.
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Fluctuation Balaban.Multiscale Balaban.Background Balaban.Localization
  Balaban.SmallField Balaban.SmallField.Def6 Balaban.SmallField.Def6v2 Balaban.SmallField.GsSpec
  Balaban.LargeField Balaban.Inhabited.MarkBudgetAudit Balaban.Inhabited.LevelStep Matrix

/-- The collar `4 d L³ + L` of the old terms at the block scale fits in the separation of the
step: `(4 d L³ + L) L^{m₁} ≤ rhoSepG d L m₁ - 1`. -/
theorem collar_le_rhoSepG {d L : ℕ} (hd : 3 ≤ d) (hL : 3 ≤ L) (m₁ : ℕ) :
    (4 * (d : ℝ) * (L : ℝ) ^ 3 + L) * (L : ℝ) ^ m₁ ≤ rhoSepG d L m₁ - 1 := by
  have ht := rhoSepG_tail_nonneg hd hL (L := L)
  have hb := bgR0_nonneg_G (d := d) (L := L)
  have h0 : (0 : ℝ) ≤ (L : ℝ) * (L : ℝ) ^ m₁ := by positivity
  have hd' : (1 : ℝ) ≤ 4 * d := by
    have : (3 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have hLm := mul_le_mul_of_nonneg_right hd' h0
  have e : (4 * (d : ℝ) * (L : ℝ) ^ 3 + L) * (L : ℝ) ^ m₁ =
      4 * (d : ℝ) * (L : ℝ) ^ 3 * (L : ℝ) ^ m₁ + (L : ℝ) * (L : ℝ) ^ m₁ := by ring
  rw [e]
  unfold rhoSepG
  linarith only [ht, hb, hLm]

open Classical in
/-- **The clauses (A1)–(A5) of the new level at a step of a tower** (route R-LOC, L5; rulings R3,
R6, R13).  Let `S` be the step of the tower `Tk` at the scale `k` on a read torus, `C` a class of
the step whose terms satisfy the clauses on the birth-mass domain (`hcl`), with the step's weights
(`hA`) and the masses of its flow (`hξ`, `hνflow`, the step mass `ν = ν_k L^{-2k}`), in the regime
`ClassHatCond C s r₀` of ruling R13, and let `e` be the coefficient of a system of the class with the
constants of the chain (`hnl`), supported on the polymers rooted at `z`.  If the irrelevant terms of
the class are bounded on their term domain with the decay in the level of the chain (`hB`, `hEbI`,
`hEbL`; A4-1b (ii)), the numerics `NewLevelNumerics` hold at the tower's constants, and the
conditions on constants of the radii, of the smallness against the cap of Theorem 3.4 and of the
(DL-gap) hold, then on the cast local sets of the thickenings `Ŷ⁺(T′)` there are a family `f T′` of
the pair of fields and bounds `b T′` with (A1)–(A5). -/
theorem StepTowerG.newLevel_localFamily_of_class {d L N : ℕ} [NeZero L] [NeZero N] {κmin : ℝ}
    (Tk : StepTowerG d L N κmin) (hm₀ : Tk.m₀ = 1) {k : ℕ} (hk : 1 ≤ k) {N₁ : ℕ} [NeZero N₁]
    (hN₁ : L ^ Tk.m₀ ∣ N₁) (h5 : 5 < N₁) {ν β p₁ : ℝ} (hν0 : 0 < ν)
    (hν : ν * (L : ℝ) ^ (2 * (k + 1)) ≤ 1) (hβ : 0 < β) (hp₁ : 0 < p₁)
    {ϱ : ℝ} (hϱ : ϱ = rhoSepG d L Tk.m₁) (S : StepSetting d L N₁ Tk.m₁ k N ϱ)
    (hS : S = hatStepKG Tk.hN k Tk.m₁ ϱ hk ν β p₁ Tk.δ) {pp : ℝ} (Jr : S.JointRep Tk.t pp)
    (C : StepClass d L N₁ Tk.m₁ k N ϱ) (z : RootIdx d L N₁ Tk.m₁ (k + 1))
    -- the constants of the inherited levels and the rates
    {κdec δ₁O δ₃ δfl : ℝ} (hδ₁O : 0 < δ₁O) (hδ₁Ot : δ₁O ≤ Tk.t) (hδ₃ : 0 ≤ δ₃) (hδfl : 0 ≤ δfl)
    (hmd : d ≤ C.m₀) (hκ4 : 4 * d * (((2 * L + 1) ^ d : ℕ) : ℝ) * κdec ≤ Tk.κ)
    (hrate : (2 * Tk.κdec - 1) * ((L : ℝ) ^ (C.m₀ - 1) + 2 * d * (L : ℝ) ^ C.m₀ *
      (((L ^ (C.m₀ - 1)) ^ d : ℕ) : ℝ) * c1 d L) + 1 ≤ 2 * κdec)
    -- the family of the step and its formula (regime of ruling R13)
    (e : physParam N S → Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := Tk.m₁) (K := k + 1) 1
      (k + 1) Set.univ) → ℂ)
    (hsupp : ∀ θ T', e θ T' ≠ 0 → rootCube (m₀ := 1) z ∈ T' ∧ IsPolyDom 1 (k + 1) (sitesOf T'))
    {s : ℕ} (hHat : ClassHatCond C s (4 * (d : ℝ) * (L : ℝ) ^ 3 + L))
    (hnl : NewLevelFormula S C z Jr ⟨Tk.κ, Tk.BG, Tk.BG₂, p₁, Tk.κ0, Tk.κ, Tk.BG, Tk.BG₂, δ₁O, p₁,
      C.m₀, Tk.c, 4 * (d : ℝ) * (L : ℝ) ^ 3 + L, δ₃, levelKc d L, Cchi d L, Tk.c₂, δfl⟩ e)
    -- the class: clauses on the birth-mass domain, weights, flow
    {P : Consts} (hPm : P.m₀ = C.m₀) (Rg : Regime L) (a : ℕ → ℝ)
    (hcl : SFTermClauses P (birthXiDom P Rg a N₁) C.Tm)
    (hA : aIdeal L (k + 1) (a (k + 1)) = compWeight L S.a₁)
    {ξ : ℕ → Fin 3 → ℂ} {q c₈ ν₀ : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) (hc₈ : 0 ≤ c₈)
    (hc₈q : c₈ * q ≤ 1 - q) (hξ : ∀ n, ‖ξ n‖ ≤ c₈ / 4 * q ^ (n + 1))
    (hνflow : ∀ n, n ≤ k → ((Rg.ν n : ℝ) : ℂ) = Flow.nuSeq (L : ℝ) ξ (ν₀ : ℂ) n)
    (hνS : ν = physMass L k (Rg.ν k))
    {rm : ℝ} (hτ : Real.exp (3 * (c₈ / 4 * (q ^ 2 / (1 - q)))) - 1 ≤ 1 / 2)
    (hτr : 2 * (Real.exp (3 * (c₈ / 4 * (q ^ 2 / (1 - q)))) - 1) < rm) (hrm : rm ≤ 1 / 16)
    (hmass : ν * ((L : ℝ) ^ (k + 1)) ^ 2 *
      (1 + 2 * (Real.exp (3 * (c₈ / 4 * (q ^ 2 / (1 - q)))) - 1)) ≤ 1)
    -- the (DL-gap) of the charts of the old terms at their birth masses
    (hDL : ∀ j, 1 ≤ j → j ≤ k →
      (2 * (Tk.t + xiK2 d L N * δ₃ + xiK2 d L N * δfl) + 2 * ((N : ℝ) + 1) *
        (cK2 d L N * (Tk.t + xiK2 d L N * δ₃ + xiK2 d L N * δfl) ^ 2)) *
        (1 + (1 + 16 * ((N : ℝ) + 1) * cK2 d L N) *
          (2 * (Real.exp (3 * (c₈ / 4 * (q ^ 2 / (1 - q)))) - 1))) ≤ P.eps d L j)
    (hsmε : ∀ j, 1 ≤ j → j ≤ k → (4 * d + 6) * ((2 * d + 1) * P.eps d L j) ≤ 1)
    (hc1ε : ∀ j, 1 ≤ j → j ≤ k → 4 * (xiC1 d * P.eps d L j) ≤ bgC1 d L N)
    (hKε : ∀ j, 1 ≤ j → j ≤ k → bgK1 d L N * (xiC1 d * P.eps d L j) + 3 * rm ≤ deltaStar d L N)
    (hζε : ∀ j, 1 ≤ j → j ≤ k → 8 * P.eps d L j * rm ≤ deltaStar d L N)
    -- the bound of the class on its term domain (A4-1b (ii)) and its decay in the level
    (Bl : ℕ → CTorus d L N₁ Tk.m₁ (k + 1) → Set (CTorus d L N₁ Tk.m₁ (k + 1)) → ℝ)
    (hBl : ∀ j y X, 0 ≤ Bl j y X)
    (hB : ∀ (i₀ i₁ : Fin N) (j : ℕ) (y : CTorus d L N₁ Tk.m₁ (k + 1))
      (X : Set (CTorus d L N₁ Tk.m₁ (k + 1))), 1 ≤ j → j ≤ k → IsPolyDom C.m₀ j X → y ∈ X →
      ∀ Ψ h : Fld d L N₁ Tk.m₁ (k + 1) N, (birthXiDom P Rg a N₁).dom j (C.Tm.gs j X) Ψ h →
      dot (Ψ y) (Ψ y) ∈ Complex.slitPlane →
      ‖irrelTorus C.m₀ C.Tm i₀ i₁ j y X Ψ h‖ ≤
        Bl j y X * Real.exp (-(κdec - 1) * treeLenCovOne C.m₀ j X))
    {CI KL α₃ : ℝ} (n₁ : ℕ) (hCI : 0 ≤ CI) (hKL : 0 ≤ KL) (hα₃ : 0 < α₃) (hE₀ : 0 ≤ P.E₀)
    (hEbI : ∀ j y X, j + n₁ ≤ k →
      Bl j y X ≤ CI * P.E₀ * ((((L : ℝ)⁻¹ ^ (k - j)) ^ ((d : ℝ) + α₃))))
    (hEbL : ∀ j y X, k < j + n₁ → Bl j y X ≤ KL * P.E₀)
    -- the radius of the new level and the numerics of the new level (ruling R3)
    (hεt : P.eps d L (k + 1) ≤ Tk.t)
    (hNLN : NewLevelNumerics d L N Tk.m₁ Tk.c Tk.BG Tk.κ Tk.t Tk.c₂ Tk.BG₂ Tk.δc
      (4 * (d : ℝ) * (L : ℝ) ^ 3 + L) ((2 * bgK1 d L N + 2) * xiC1 d * Tk.t))
    -- the radii of the zero-source and bridge marks
    {cψ r R₁ R U : ℝ} (hcψ : 0 ≤ cψ) (hρ₀c : 2 * p₁ ≤ cψ)
    (hRu : corrU * markedRad d L N k S.a₁ Tk.κ cψ ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) < Tk.t)
    (hR₁ : 1 < R₁) (hr : 0 < r) (hrays : (2 * R₁ + r) * p₁ ≤ cψ) (hR : 0 < R)
    (hRR : (R + R) * markedRad d L N k S.a₁ Tk.κ cψ ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) < Tk.t)
    (hUR : 2 * U ≤ R) (hU : 17 / 16 ≤ U)
    (hsmZ : 8 * (|S.β| * (6 * (1 / 2) * c1 d L * ((L : ℝ) ^ (1 + Tk.m₁)) ^ d *
      ‖energyBdScaled d L N (compWeight L S.a₁) k (cK2' d L N (famConst d L Tk.BG₂ Tk.κ) * Tk.t)
        Tk.t (rho4 d L N Tk.BG Tk.κ)‖ / r ^ 3)) ≤
      1 / (8 * (2 * (K0 d L Tk.κ0 + 1) + (K0 d L Tk.κ0 + rootUnionK d L 1 Tk.m₁ Tk.κ0) +
        rootUnionK d L 1 Tk.m₁ Tk.κ0) ^ 3 * c1 d L *
        Real.exp (((2 * Tk.κdec - 1) - 2 * Tk.κ0) * cG d L + c1 d L + Tk.κ' * cG d L)))
    -- the marked radius of the old terms and the smallness of the class (Theorem 3.4)
    (hmr : 0 < markedRad d L N k S.a₁ Tk.κ p₁ ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ))
    (hca : corrU ≤ δ₁O / (2 * markedRad d L N k S.a₁ Tk.κ p₁ ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)))
    (hsmO : corrU / (δ₁O / (2 * markedRad d L N k S.a₁ Tk.κ p₁
        ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ))) *
      (((2 ^ L ^ d : ℕ) : ℝ) * (c1 d L * ((((L : ℝ) ^ (1 + C.m₀ + Tk.m₁)) ^ d) * P.E₀ *
        (2 * K0 d L Tk.κ0 * (CI * Real.exp ((κdec - 1) * cG d L) * (1 - (L : ℝ) ^ (-α₃))⁻¹ +
          n₁ * (KL * Real.exp ((κdec - 1) * cG d L)) * ((((L : ℝ) ^ (n₁ - 1)) ^ d))))) *
        Real.exp ((2 * Tk.κdec - 1) * (2 * (d : ℝ) * (L : ℝ) ^ C.m₀ *
          ((((L ^ (C.m₀ - 1)) ^ d : ℕ)) : ℝ) * c1 d L)))) ≤
      1 / (8 * (2 * (K0 d L Tk.κ0 + 1) + (K0 d L Tk.κ0 + rootUnionK d L 1 Tk.m₁ Tk.κ0) +
        rootUnionK d L 1 Tk.m₁ Tk.κ0) ^ 3 * c1 d L *
        Real.exp (((2 * Tk.κdec - 1) - 2 * Tk.κ0) * cG d L + c1 d L + Tk.κ' * cG d L)))
    -- the cast of the local sets `𝔹_{k+1}(Ŷ)` and the projection onto the data of the step
    {N₁' : ℕ} [NeZero N₁'] (hc : N₁' * L ^ (Tk.m₁ + s) = N₁ * L ^ Tk.m₁)
    (hsep : ϱ ≤ minSep L (L ^ (Tk.m₁ + s)))
    (π : RawData d L (N₁ * L ^ Tk.m₁) (k + 1) N →L[ℂ] rawSub N S.G')
    (hπ : ∀ r (h : r ∈ rawSub N S.G'), π r = ⟨r, h⟩) :
    ∃ (f : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := Tk.m₁) (K := k + 1) 1 (k + 1)
        Set.univ) → Def6.Fld d L N₁ Tk.m₁ (k + 1) N × Def6.Fld d L N₁ Tk.m₁ (k + 1) N → ℂ)
      (b : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := Tk.m₁) (K := k + 1) 1 (k + 1)
        Set.univ) → ℝ),
      (∀ T, IsPolyDom P.m₀ (k + 1) (sitesOf (piHull P.m₀ (thickSet S.G' (sitesOf T)))) →
        AnalyticOnNhd ℂ (f T)
          {p | (xiFieldDom S.a S.ν (P.eps d L) : FieldDom d L N₁ Tk.m₁ (k + 1) N ϱ).dom (k + 1)
            (castG hc (localB (k + 1) (le_refl (k + 1))
              {x' : CTorus d L N₁' (Tk.m₁ + s) (k + 1) | (torusCast x' : CTorus d L N₁ Tk.m₁ (k + 1)) ∈
                hatSet P.m₀ (k + 1) (sitesOf (piHull P.m₀ (thickSet S.G' (sitesOf T))))} hsep))
            p.1 p.2}) ∧
      (∀ T, IsPolyDom P.m₀ (k + 1) (sitesOf (piHull P.m₀ (thickSet S.G' (sitesOf T)))) →
        ∀ p : Def6.Fld d L N₁ Tk.m₁ (k + 1) N × Def6.Fld d L N₁ Tk.m₁ (k + 1) N,
        (xiFieldDom S.a S.ν (P.eps d L) : FieldDom d L N₁ Tk.m₁ (k + 1) N ϱ).dom (k + 1)
          (castG hc (localB (k + 1) (le_refl (k + 1))
            {x' : CTorus d L N₁' (Tk.m₁ + s) (k + 1) | (torusCast x' : CTorus d L N₁ Tk.m₁ (k + 1)) ∈
              hatSet P.m₀ (k + 1) (sitesOf (piHull P.m₀ (thickSet S.G' (sitesOf T))))} hsep))
          p.1 p.2 →
        ‖f T p‖ ≤ b T) ∧
      (∀ T, IsPolyDom P.m₀ (k + 1) (sitesOf (piHull P.m₀ (thickSet S.G' (sitesOf T)))) →
        ∀ p p' : Def6.Fld d L N₁ Tk.m₁ (k + 1) N × Def6.Fld d L N₁ Tk.m₁ (k + 1) N,
        (xiFieldDom S.a S.ν (fun j => (2 * bgK1 d L N + 2) * xiC1 d * P.eps d L j) :
          FieldDom d L N₁ Tk.m₁ (k + 1) N ϱ).dom (k + 1)
          (castG hc (localB (k + 1) (le_refl (k + 1))
            {x' : CTorus d L N₁' (Tk.m₁ + s) (k + 1) | (torusCast x' : CTorus d L N₁ Tk.m₁ (k + 1)) ∈
              hatSet P.m₀ (k + 1) (sitesOf (piHull P.m₀ (thickSet S.G' (sitesOf T))))} hsep))
          p.1 p.2 →
        (xiFieldDom S.a S.ν (fun j => (2 * bgK1 d L N + 2) * xiC1 d * P.eps d L j) :
          FieldDom d L N₁ Tk.m₁ (k + 1) N ϱ).dom (k + 1)
          (castG hc (localB (k + 1) (le_refl (k + 1))
            {x' : CTorus d L N₁' (Tk.m₁ + s) (k + 1) | (torusCast x' : CTorus d L N₁ Tk.m₁ (k + 1)) ∈
              hatSet P.m₀ (k + 1) (sitesOf (piHull P.m₀ (thickSet S.G' (sitesOf T))))} hsep))
          p'.1 p'.2 →
        (∀ x ∈ sitesOf (piHull P.m₀ (thickSet S.G' (sitesOf T))), p.1 x = p'.1 x ∧ p.2 x = p'.2 x) →
        f T p = f T p') ∧
      (∀ T, IsPolyDom P.m₀ (k + 1) (sitesOf (piHull P.m₀ (thickSet S.G' (sitesOf T)))) →
        ∀ Q : Matrix (Fin N) (Fin N) ℝ, Qᵀ * Q = 1 →
        ∀ p : Def6.Fld d L N₁ Tk.m₁ (k + 1) N × Def6.Fld d L N₁ Tk.m₁ (k + 1) N,
        (xiFieldDom S.a S.ν (P.eps d L) : FieldDom d L N₁ Tk.m₁ (k + 1) N ϱ).dom (k + 1)
          (castG hc (localB (k + 1) (le_refl (k + 1))
            {x' : CTorus d L N₁' (Tk.m₁ + s) (k + 1) | (torusCast x' : CTorus d L N₁ Tk.m₁ (k + 1)) ∈
              hatSet P.m₀ (k + 1) (sitesOf (piHull P.m₀ (thickSet S.G' (sitesOf T))))} hsep))
          p.1 p.2 →
        f T (rotField (cmat Q) p.1, rotField (cmat Q) p.2) = f T p) ∧
      (∀ T (q : Def6.Fld d L N₁ Tk.m₁ (k + 1) N × Def6.Fld d L N₁ Tk.m₁ (k + 1) N),
        Def6.XiDom S.G' S.a S.ν (k + 1) (P.eps d L (k + 1)) q.1 q.2 →
        f T q = e (π (clipRaw S.G' q), 0) T) := by
  classical
  obtain ⟨NS, hO, hK, he⟩ := hnl
  subst hS
  subst hϱ
  have hd : 3 ≤ d := Tk.hd
  have hL : 3 ≤ L := Tk.hL
  have hd0 : 0 < d := by omega
  have hm1 : 1 ≤ C.m₀ := by omega
  -- the step's fluctuation cores
  obtain ⟨hC₀⟩ := Tk.core
  have hCs := flCore_stepG (N := N) hd hL Tk.m₁_four hC₀ hk h5 hν0.le hν
  have hBG₂ : 0 ≤ Tk.BG₂ := hCs.hS2.fam.2.1
  have hδc : 0 ≤ Tk.δc := δc_nonneg_of_flCore hd Tk.t_pos hCs Tk.dom_margin
  have hCs' : FlCore N (GpG d L N₁ Tk.m₁ k) (HmG d L N₁ Tk.m₁ k) 1 ν Tk.c Tk.BG Tk.κ
      ((2 * bgK1 d L N + 2) * xiC1 d * Tk.t) (levelKc d L) (Cchi d L) Tk.c₂ Tk.BG₂ Tk.t :=
    { hCs with
      eps_pos := hNLN.chain'.eps_pos
      small1 := hNLN.chain'.small1
      c7le := hNLN.chain'.c7le
      B_le := hNLN.fl'.B_le
      B_one := hNLN.fl'.B_one
      phi_lt := hNLN.fl'.phi_lt }
  have hCLs : FlCore N (GpG d L N₁ Tk.m₁ k) (HmG d L N₁ Tk.m₁ k) 1 ν Tk.c Tk.BG Tk.κ Tk.t
      (levelKc d L) (Cchi d L) Tk.c₂ Tk.BG₂ δ₁O :=
    { hCs with δ₁_pos := hδ₁O, δ₁_le := hδ₁Ot.trans hCs.δ₁_le }
  have hCLs' : FlCore N (GpG d L N₁ Tk.m₁ k) (HmG d L N₁ Tk.m₁ k) 1 ν Tk.c Tk.BG Tk.κ
      ((2 * bgK1 d L N + 2) * xiC1 d * Tk.t) (levelKc d L) (Cchi d L) Tk.c₂ Tk.BG₂ δ₁O :=
    { hCs' with δ₁_pos := hδ₁O, δ₁_le := hδ₁Ot.trans hCs.δ₁_le }
  -- the rates
  have hT3 : 3 ≤ Tk.κdec := by
    have := Tk.κdec_lower
    have := Tk.κ0_nonneg
    linarith
  obtain ⟨hκle, hlogL⟩ := rate_consequencesG hd (by omega) hm1 hmd hT3 (one_le_c1 d L) hκ4
    (by simpa using hrate)
  have hκdec : 3 * Tk.κ0 + 3 ≤ κdec := Tk.κdec_lower.trans hκle
  have hκ'0 : 0 ≤ Tk.κ' := by
    rw [Tk.κ'_eq]
    have := Tk.κ0_nonneg
    linarith
  have hκrel : Tk.κ' + 3 * Tk.κ0 + c1 d L + 3 / 2 ≤ 2 * Tk.κdec - 1 := by
    rw [Tk.κ'_eq, Tk.κdec_eq]
    have := Tk.κ0_nonneg
    have := one_le_c1 d L
    linarith
  -- the birth masses
  have hμ := birthMass_defect_of_flow hq0 hq1 hc₈ hc₈q hξ hτ hνflow
  set τ₁ := Real.exp (3 * (c₈ / 4 * (q ^ 2 / (1 - q)))) - 1 with hτ₁
  have hH := hCs.HBp
  have H' := birthMass_bgHyp_of_flow hH hq0 hq1 hc₈ hc₈q hξ hτ hνflow hνS hmass
  have hμ' : ∀ j, 1 ≤ j → j ≤ k → ∃ tm, physMass L j (Rg.ν j) =
      (hatStepKG (d := d) (L := L) (N₁ := N₁) Tk.hN k Tk.m₁ (rhoSepG d L Tk.m₁) hk ν β p₁
        Tk.δ).ν * (1 + tm) ∧ |tm| ≤ 2 * τ₁ := by
    intro j hj1 hjk
    obtain ⟨t', ht', htb⟩ := hμ j hj1 hjk
    exact ⟨t', by rw [ht', ← hνS]; rfl, htb⟩
  -- the local sets
  have hs2 : 2 ≤ s := hHat.2.1 ▸ two_le_hatScale_rhoSepG hd hL Tk.m₁
  have hsP : s < P.m₀ := hPm ▸ hHat.2.2.1
  have hNP : L ^ P.m₀ ∣ N₁ := by
    have h := NS.OS.hN
    rw [hK.m₀O] at h
    rw [hPm]
    exact h
  -- the old terms' marked radius
  set mR := markedRad d L N k
    (hatStepKG (d := d) (L := L) (N₁ := N₁) Tk.hN k Tk.m₁ (rhoSepG d L Tk.m₁) hk ν β p₁ Tk.δ).a₁
    Tk.κ p₁
    ((((hatStepKG (d := d) (L := L) (N₁ := N₁) Tk.hN k Tk.m₁ (rhoSepG d L Tk.m₁) hk ν β p₁
      Tk.δ).betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) with hmRdef
  have hcu := corrU_pos
  have hmRδ : corrU * mR ≤ δ₁O / 2 := by
    have := mul_le_mul_of_nonneg_right hca hmr.le
    rw [div_mul_eq_mul_div, mul_div_assoc] at this
    calc corrU * mR ≤ δ₁O * (mR / (2 * mR)) := this
      _ = δ₁O / 2 := by field_simp
  -- the bridge family of the root is nonempty
  have hcovs := levelCoversG_of_dvd (N := N) (lvLowG d L N₁ Tk.m₁ k (rhoSepG d L Tk.m₁))
    hCs.Sp isLevel_lvTopG (by omega : 1 ≤ Tk.m₀) hN₁
  obtain ⟨Y0, hY0⟩ := e1DomG_bridgeFamily_nonempty_of_covers (hk := hk) (ν := ν) (β := β) (p₁ := p₁) Tk hm₀
    hcovs rfl z
  refine NS.localFamily_of_class (c := Tk.c) (c₂ := hNLN.c₂m) (ϱf := rhoSepG d L Tk.m₁)
    (Hf := HmG d L N₁ Tk.m₁ k) (Kc₀ := levelKc d L) (Cx₀ := Cchi d L) (c₂₀ := Tk.c₂)
    (c₂L := hNLN.c₂m) (ϱfL := rhoSepG d L Tk.m₁) (HfL := HmG d L N₁ Tk.m₁ k)
    (KcL₀ := levelKc d L) (CxL₀ := Cchi d L) (c₂L₀ := Tk.c₂) (δcL := Tk.δc)
    (δ₃' := hNLN.δ₃') (δfl' := hNLN.δfl') (c₃ := hNLN.c₃)
    (hO := hO)
    (hS1 := rfl)
    (hβS := hβ)
    (hd := hd)
    (SpG := hCs.Sp)
    (Rg := Rg)
    (a := a)
    (hPm := hPm)
    (hm1 := hm1)
    (hcl := hcl)
    (hA := hA)
    (H := hH)
    (H' := H')
    (hμ := hμ')
    (hτr := hτr)
    (hrm := hrm)
    (hδ₃0 := ?g_hδ₃0)
    (hδfl0 := ?g_hδfl0)
    (hDL := ?g_hDL)
    (hsmε := hsmε)
    (hc1ε := hc1ε)
    (hKε := hKε)
    (hζε := hζε)
    (Bl := Bl)
    (hBl := hBl)
    (hB := hB)
    (n₁ := n₁)
    (hCI := hCI)
    (hKL := hKL)
    (hα₃ := hα₃)
    (hE₀ := hE₀)
    (hEbI := hEbI)
    (hEbL := hEbL)
    (hc := hc)
    (hm := ?g_hm)
    (hsep := hsep)
    (Yp := fun Y => {x' : CTorus d L N₁' (Tk.m₁ + s) (k + 1) |
      (torusCast x' : CTorus d L N₁ Tk.m₁ (k + 1)) ∈ hatSet P.m₀ (k + 1) Y})
    (hmarg := fun T => hatLocal_margin hsP hL hc hsep
      (Set.subset_union_left.trans (subset_sitesOf_piHull hNP _)))
    (hle := hNLN.hle)
    (hεr := le_rfl)
    (hεt := hεt)
    (hS := ?g_hS)
    (hCs := ?g_hCs)
    (hCs' := ?g_hCsp)
    (hS2m := ?g_hS2m)
    (hM2m := ?g_hM2m)
    (hMXd := ?g_hMXd)
    (hMXn := ?g_hMXn)
    (hδc := hδc)
    (hdm := ?g_hdm)
    (hα := ?g_hα)
    (hdm' := ?g_hdmp)
    (hα' := ?g_hαp)
    (hsm := ?g_hsm)
    (hcψ := hcψ)
    (hρ₀c := ?g_hρ₀c)
    (hρp := ?g_hρp)
    (hRu := ?g_hRu)
    (hBG₂ := ?g_hBG₂)
    (hκ₀ := Tk.κ0_nonneg)
    (hκ₀e := Tk.κ0_ent)
    (hκdec := hκdec)
    (hκκ := ?g_hκκ)
    (h1 := ?g_h1)
    (hlog := ?g_hlog)
    (hR₁ := hR₁)
    (hr := hr)
    (hrays := ?g_hrays)
    (hR := hR)
    (hRR := ?g_hRR)
    (hUR := hUR)
    (hU := hU)
    (hSL := ?g_hSL)
    (hCLs := ?g_hCLs)
    (hCLs' := ?g_hCLsp)
    (hS2mL := ?g_hS2mL)
    (hM2mL := ?g_hM2mL)
    (hMXLd := ?g_hMXLd)
    (hMXLn := ?g_hMXLn)
    (hdmL := ?g_hdmL)
    (hαL := ?g_hαL)
    (hdmL' := ?g_hdmLp)
    (hαL' := ?g_hαLp)
    (hsmL := ?g_hsmL)
    (cψL := p₁)
    (hcψL := hp₁.le)
    (hκκL := ?g_hκκL)
    (h1L := ?g_h1L)
    (hlogL := ?g_hlogL)
    (hρL := ?g_hρL)
    (hρcL := ?g_hρcL)
    (hρpL := ?g_hρpL)
    (hRuL := ?g_hRuL)
    (aR := δ₁O / (2 * mR))
    (hca := hca)
    (haL := ?g_haL)
    (ht₀ := half_pos hcu)
    (hRt := ?g_hRt)
    (hCN' := ?g_hCNp)
    (hFN' := ?g_hFNp)
    (hrb := ?g_hrb)
    (κH := 2 * Tk.κdec - 1)
    (κ' := Tk.κ')
    (hκH := ?g_hκH)
    (hκH0 := ?g_hκH0)
    (hrate := hrate)
    (hκ' := hκ'0)
    (hκ := ?g_hκ)
    (hsmZ := ?g_hsmZ)
    (hsmO := ?g_hsmO)
    (hι := ⟨Sum.inl ⟨Y0, hY0⟩⟩)
    (hz := ?g_hz)
    (hS3 := ?g_hS3)
    (hM3 := ?g_hM3)
    (hc0 := (hCs.c7le.trans (c7_le_bgC1 d L N Tk.BG Tk.κ)).trans (bgC1_le_bgC0 d L N hd0))
    (hN1 := ?g_hN1)
    (e := e)
    (he := he)
    (hsupp := hsupp)
    (π := π)
    (hπ := hπ)
  case g_hδ₃0 =>
    rw [hK.δ₃]; exact hδ₃
  case g_hδfl0 =>
    rw [hK.δfl]; exact hδfl
  case g_hDL =>
    rw [hK.δ₃, hK.δfl]; exact hDL
  case g_hm =>
    omega
  case g_hS =>
    rw [hK.BG]; exact hNLN.hSm
  case g_hCs =>
    rw [hK.BG, hK.κ, hK.BG₂]; exact hCs
  case g_hCsp =>
    rw [hK.BG, hK.κ, hK.BG₂]; exact hCs'
  case g_hS2m =>
    rw [hK.BG₂]; exact hNLN.hS2m
  case g_hM2m =>
    rw [hK.κ]; exact hNLN.hM2m
  case g_hMXd =>
    rw [hK.κ]; exact hNLN.hMXd
  case g_hMXn =>
    rw [hK.κ]; exact Tk.large_block
  case g_hdm =>
    rw [hK.BG, hK.κ]; exact Tk.dom_margin
  case g_hα =>
    rw [hK.BG, hK.κ]; exact Tk.coer_margin
  case g_hdmp =>
    rw [hK.BG, hK.κ]; exact hNLN.dm'
  case g_hαp =>
    rw [hK.BG, hK.κ]; exact hNLN.α'
  case g_hsm =>
    rw [hK.κ]; exact Tk.δc_small
  case g_hρ₀c =>
    rw [hK.p₁]; exact hρ₀c
  case g_hρp =>
    rw [hK.p₁]; exact le_rfl
  case g_hRu =>
    rw [hK.κ]; exact hRu
  case g_hBG₂ =>
    rw [hK.BG₂]; exact hBG₂
  case g_hκκ =>
    rw [hK.κ]; exact hκ4
  case g_h1 =>
    rw [hK.κ]; exact Tk.κ_one
  case g_hlog =>
    rw [hK.κ]; simpa [hm₀] using Tk.κ_log
  case g_hrays =>
    rw [hK.p₁]; exact hrays
  case g_hRR =>
    rw [hK.κ]; exact hRR
  case g_hSL =>
    rw [hK.cB, hK.BGO]; exact hNLN.hSm
  case g_hCLs =>
    rw [hK.cB, hK.BGO, hK.κO, hK.BG₂O, hK.δ₁O]; exact hCLs
  case g_hCLsp =>
    rw [hK.cB, hK.BGO, hK.κO, hK.BG₂O, hK.δ₁O]; exact hCLs'
  case g_hS2mL =>
    rw [hK.BG₂O]; exact hNLN.hS2m
  case g_hM2mL =>
    rw [hK.κO]; exact hNLN.hM2m
  case g_hMXLd =>
    rw [hK.κO]; exact hNLN.hMXd
  case g_hMXLn =>
    rw [hK.κO]; exact Tk.large_block
  case g_hdmL =>
    rw [hK.BGO, hK.κO]; exact Tk.dom_margin
  case g_hαL =>
    rw [hK.BGO, hK.κO]; exact Tk.coer_margin
  case g_hdmLp =>
    rw [hK.BGO, hK.κO]; exact hNLN.dm'
  case g_hαLp =>
    rw [hK.BGO, hK.κO]; exact hNLN.α'
  case g_hsmL =>
    rw [hK.κO]; exact Tk.δc_small
  case g_hκκL =>
    rw [hK.κO]; exact hκ4
  case g_h1L =>
    rw [hK.κO]; exact Tk.κ_one
  case g_hlogL =>
    rw [hK.κO, hK.m₀O]; exact hlogL
  case g_hρL =>
    rw [hK.ρO]; exact hp₁
  case g_hρcL =>
    rw [hK.ρO]
  case g_hρpL =>
    rw [hK.ρO]; exact le_rfl
  case g_hRuL =>
    rw [hK.κO, hK.δ₁O]
    show corrU * mR < δ₁O
    linarith only [hmRδ, hδ₁O]
  case g_haL =>
    rw [hK.κO, hK.δ₁O]
    show δ₁O / (2 * mR) * mR < δ₁O
    rw [div_mul_eq_mul_div, mul_div_mul_right _ _ hmr.ne']
    linarith only [hδ₁O]
  case g_hRt =>
    rw [hK.κO, hK.δ₁O]
    show (corrU + corrU / 2) * mR < δ₁O
    have e : (corrU + corrU / 2) * mR = 3 / 2 * (corrU * mR) := by ring
    rw [e]
    linarith only [hmRδ, hδ₁O]
  case g_hCNp =>
    rw [hK.BGO, hK.κO, hK.r₀]; exact hNLN.chain'
  case g_hFNp =>
    rw [hK.BGO, hK.BG₂O, hK.κO, hK.δ₁O]
    exact hNLN.fl'.mono_δ₁ hd0 hBG₂ hδ₁O (hδ₁Ot.trans hNLN.hle)
  case g_hrb =>
    rw [hK.r₀]
    exact collar_le_rhoSepG hd hL Tk.m₁
  case g_hκH =>
    linarith only [hκle]
  case g_hκH0 =>
    linarith only [hT3]
  case g_hκ =>
    rw [hK.κ0]; exact hκrel
  case g_hsmZ =>
    rw [hK.κ0, hK.BG₂, hK.κ, hK.BG]; exact hsmZ
  case g_hsmO =>
    rw [hK.κ0]; exact hsmO
  case g_hz =>
    rw [hK.κ]; exact Tk.det_z
  case g_hS3 =>
    rw [hK.BG]; exact hNLN.hS3
  case g_hM3 =>
    rw [hK.κ]; exact hNLN.hM3
  case g_hN1 =>
    simpa [hm₀] using hN₁

end Balaban.Inhabited
