/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Base.BaseLocalCongr
public import Balaban.LargeField.Base.BaseChartTermCross
public import Balaban.LargeField.Base.BaseDefectCross

/-!
# The masked activity of a local generating set is the activity of the level set

For a level set `Gp` (with `Ω₁` the whole torus) and a generating set `Gl` of the first step, and a
label `Y ⊆ R` whose `8 L^{1+m₁}`-neighbourhood lies in `Ω₁(Gl)`, the masked activity of `Gl`
(`maskedTerm`) equals the activity `chartTerm + defTerm` of `Gp` when the data, the sources, the fields, the
whitenings and the defect matrices correspond (`maskedTerm_cross`): `chartTerm_cross` and `defTerm_cross`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField.Base

open Balaban Balaban.Multiscale Balaban.Localization Balaban.Background Balaban.Fluctuation
  Balaban.LargeField Balaban.SmallField Balaban.SmallField.Def6 Balaban.Green Balaban.Analysis
  Balaban.Polymer Matrix

section Cross

variable {d L N₁ m₁ N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱl : ℝ} {m₀ : ℕ}
  {Gl : GeneratingSet d L (N₁ * L ^ m₁) 1 ϱl} {Gp : GeneratingSet d L (N₁ * L ^ m₁) 1 ϱ}

local notation "𝕋₁" => Balaban.Localization.CTorus d L N₁ m₁ 1

open Classical in
/-- **The masked activity of a local generating set is the activity of the level set.** -/
theorem maskedTerm_cross (hG' : IsLevel Gp 1) (hm₁ : 2 ≤ m₁) (hN : L ^ m₀ ∣ N₁)
    {Kc Cx c BG : ℝ} {a : ℕ → ℝ} {ν β : ℝ} (hS : Dec2.DecSpecs d L Kc Cx c BG)
    (Sl : Dec2.CoverBase (coverOf Gl) Gl a ν Kc Cx) (Sp : Dec2.CoverBase (coverOf Gp) Gp a ν Kc Cx)
    (HBl : BgHyp d L 1 ϱl a ν) (HBp : BgHyp d L 1 ϱ a ν) {κ : ℝ} (hκ : 0 < κ)
    (hM : c * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    {Fl : Dec2.DecParams (coverOf Gl) × RawData d L (N₁ * L ^ m₁) 1 N →
      (Gl.Ω 1 × Fin N → ℂ) × (Gl.Ω 1 → ℂ)}
    {Fp : Dec2.DecParams (coverOf Gp) × RawData d L (N₁ * L ^ m₁) 1 N →
      (Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)}
    (hFl : ∀ (s : Dec2.DecParams (coverOf Gl)) (D : BgData Gl N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC Gl (bgC0 d L N) (c7 d L N BG κ) ν D → ∀ (φ : Gl.Ω 1 × Fin N → ℂ)
        (α : Gl.Ω 1 → ℂ), Dec2.IsDecBg (coverOf Gl) Gl a ν (rho4 d L N BG κ) s D φ α →
          Fl (s, (D.Ψ, D.h)) = (φ, α))
    (hFp : ∀ (s : Dec2.DecParams (coverOf Gp)) (D : BgData Gp N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC Gp (bgC0 d L N) (c7 d L N BG κ) ν D → ∀ (φ : Gp.Ω 1 × Fin N → ℂ)
        (α : Gp.Ω 1 → ℂ), Dec2.IsDecBg (coverOf Gp) Gp a ν (rho4 d L N BG κ) s D φ α →
          Fp (s, (D.Ψ, D.h)) = (φ, α))
    {D : BgData Gl N} {D' : BgData Gp N}
    (hDu : InUnionDomainC Gl (bgC0 d L N) (c7 d L N BG κ) ν D)
    (hDu' : InUnionDomainC Gp (bgC0 d L N) (c7 d L N BG κ) ν D')
    (gl ψl : Gl.Ω 1 × Fin N → ℂ) (gp ψp : Gp.Ω 1 × Fin N → ℂ)
    (Wl : ((Gl.Ω 1 × Fin N → ℂ) × (Gl.Ω 1 → ℂ)) → Matrix (Gl.Ω 1 × Fin N) (Gl.Ω 1 × Fin N) ℂ)
    (Wp : ((Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)) → Matrix (Gp.Ω 1 × Fin N) (Gp.Ω 1 × Fin N) ℂ)
    (Dl : Matrix (Gl.Ω 1 × Fin N) (Gl.Ω 1 × Fin N) ℂ) (Dp : Matrix (Gp.Ω 1 × Fin N) (Gp.Ω 1 × Fin N) ℂ)
    (ρ rD : ℕ) (R : Set 𝕋₁) (Y : Set 𝕋₁) (hYR : Y ⊆ R)
    (hRdeep : ∀ w : 𝕋₁, (∃ t ∈ R, supDist w t ≤ 8 * L ^ (0 + 1 + m₁)) → w ∈ Gl.Ω (0 + 1))
    (hρ : ρ + L ≤ 8 * L ^ (0 + 1 + m₁))
    (hdat0 : ∀ z : 𝕋₁, (∃ t ∈ Y, supDist z t ≤ 4 * L ^ (0 + 1)) → D.Ψ z = D'.Ψ z ∧ D.h z = D'.h z)
    (hfl : ∀ x : Gl.Ω 1, AnalyticOnNhd ℂ
      (fun s => chartFe Gl a ν β gl ψl Wl x (Fl (s, (D.Ψ, D.h))))
      (polydisc (0 : Dec2.DecParams (coverOf Gl)) (fun _ => Real.exp κ)))
    (hgc : ∀ (x : Gl.Ω 1) (x' : Gp.Ω 1), (x : 𝕋₁) = x' → (x : 𝕋₁) ∈ Y → ∀ i, gp (x', i) = gl (x, i))
    (hWlr : ∀ u p r, Wl u p r ≠ 0 → supDist (p.1 : 𝕋₁) r.1 ≤ ρ)
    (hWpr : ∀ u p r, Wp u p r ≠ 0 → supDist (p.1 : 𝕋₁) r.1 ≤ ρ)
    (hWc : ∀ (u : (Gl.Ω 1 × Fin N → ℂ) × (Gl.Ω 1 → ℂ)) (u' : (Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ))
      (p : Gl.Ω 1 × Fin N) (p' : Gp.Ω 1 × Fin N) (r : Gl.Ω 1 × Fin N) (r' : Gp.Ω 1 × Fin N),
      (p.1 : 𝕋₁) = p'.1 → p.2 = p'.2 → (r.1 : 𝕋₁) = r'.1 → r.2 = r'.2 →
      (∀ (y : Gl.Ω 1) (y' : Gp.Ω 1), (y : 𝕋₁) = y' → supDist (p.1 : 𝕋₁) y ≤ ρ →
        (∀ i, u.1 (y, i) = u'.1 (y', i)) ∧ u.2 y = u'.2 y') → Wp u' p' r' = Wl u p r)
    (d0 : ↥(coverOf Gp).cubeIdx) (d0l : ↥(coverOf Gl).cubeIdx)
    (hWl : ∀ (x : Gl.Ω 1) i r, Dl (x, i) r ≠ 0 → supDist (x : 𝕋₁) r.1 ≤ rD)
    (hWp : ∀ (x' : Gp.Ω 1) i r, Dp (x', i) r ≠ 0 → supDist (x' : 𝕋₁) r.1 ≤ rD)
    (hWx : ∀ (x : Gl.Ω 1) (x' : Gp.Ω 1), (x : 𝕋₁) = x' → (x : 𝕋₁) ∈ Y → ∀ i (r : Gl.Ω 1 × Fin N)
      (r' : Gp.Ω 1 × Fin N), (r.1 : 𝕋₁) = r'.1 → r.2 = r'.2 → Dp (x', i) r' = Dl (x, i) r)
    (hψ : ∀ (r : Gl.Ω 1 × Fin N) (r' : Gp.Ω 1 × Fin N), (r.1 : 𝕋₁) = r'.1 → r.2 = r'.2 →
      (r.1 : 𝕋₁) ∈ Y → ψp r' = ψl r) :
    chartTerm Gp a ν β gp Wp Fp m₀ (ρ + L) Y (D'.Ψ, D'.h) ψp + defTerm Gp Dp m₀ rD Y ψp =
      maskedTerm Gl a ν β gl Wl Fl Dl m₀ (ρ + L) rD R Y (D.Ψ, D.h) ψl := by
  unfold maskedTerm
  simp only [hYR, ↓reduceIte]
  have hΩp : ∀ z, z ∈ Gp.Ω 1 := fun z => (hG' z).1
  have hreads : ∀ (x : Gl.Ω 1) (x' : Gp.Ω 1), (x : 𝕋₁) = x' → (∀ z : 𝕋₁, supDist (x : 𝕋₁) z ≤ ρ + L → z ∈ Y) →
      ReadsSeedCross Gl Gp (seedBall (x : 𝕋₁) (ρ + L)) (chartFe Gl a ν β gl ψl Wl x)
        (chartFe Gp a ν β gp ψp Wp x') := by
    intro x x' hxx hball
    have hxY : (x : 𝕋₁) ∈ Y := hball _ (by rw [supDist_self]; exact Nat.zero_le _)
    refine chartFe_readsSeedCross hΩp a ν β gl ψl gp ψp Wl Wp x x' hxx ρ
      (fun z hz => hRdeep z ⟨z, hYR (hball z hz), by rw [supDist_self]; exact Nat.zero_le _⟩)
      (fun z hz j hj1 hj2 => by
        have hzΩ := hRdeep z ⟨z, hYR (hball z hz), by rw [supDist_self]; exact Nat.zero_le _⟩
        have hj : j = 1 := by omega
        subst hj
        exact (level_layer_iff_of_mem_top hG' hzΩ (le_refl 1) (le_refl 1)).symm)
      (fun i => hgc x x' hxx hxY i)
      (fun r r' h1 h2 hr => hψ r r' h1 h2 (hball _ hr)) hWlr hWpr hWc
    -- the seed ball of `x` is the set read
  rw [chartTerm_cross hG' hm₁ hN hS Sl Sp HBl HBp hκ hM hFl hFp hDu hDu' gl ψl gp ψp Wl Wp (ρ + L) Y
    (fun z hz => hRdeep z (by obtain ⟨t, ht, h⟩ := hz; exact ⟨t, hYR ht, h⟩)) hdat0 hfl hreads d0 d0l,
    defTerm_cross hN hΩp rD Dl Dp ψl ψp Y
      (fun z hz => hRdeep z ⟨z, hYR hz, by rw [supDist_self]; exact Nat.zero_le _⟩) hWl hWp hWx hψ]


section PstCross

variable {Ωb : CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := 1) m₀ 1 Set.univ → Type*}
  [∀ b, MeasurableSpace (Ωb b)]

open Classical in
/-- **The cluster-expansion coefficient of the masked activities of a local generating set is that of the
level set** (the clause (A5) of the local family).  If the labels of the family with blocks in `T` lie in `R`
(whose `8 L^{1+m₁}`-neighbourhood is in `Ω₁(Gl)`), then `P(T)` of the masked family of `Gl` at a parameter `q`
equals `P(T)` of the family of `Gp` at the corresponding datum. -/
theorem masked_Pst_cross (hG' : IsLevel Gp 1) (hm₁ : 2 ≤ m₁) (hN : L ^ m₀ ∣ N₁)
    {Kc Cx c BG : ℝ} {a : ℕ → ℝ} {ν β : ℝ} (hS : Dec2.DecSpecs d L Kc Cx c BG)
    (Sl : Dec2.CoverBase (coverOf Gl) Gl a ν Kc Cx) (Sp : Dec2.CoverBase (coverOf Gp) Gp a ν Kc Cx)
    (HBl : BgHyp d L 1 ϱl a ν) (HBp : BgHyp d L 1 ϱ a ν) {κ : ℝ} (hκ : 0 < κ)
    (hM : c * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    {Fl : Dec2.DecParams (coverOf Gl) × RawData d L (N₁ * L ^ m₁) 1 N →
      (Gl.Ω 1 × Fin N → ℂ) × (Gl.Ω 1 → ℂ)}
    {Fp : Dec2.DecParams (coverOf Gp) × RawData d L (N₁ * L ^ m₁) 1 N →
      (Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)}
    (hFl : ∀ (s : Dec2.DecParams (coverOf Gl)) (D : BgData Gl N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC Gl (bgC0 d L N) (c7 d L N BG κ) ν D → ∀ (φ : Gl.Ω 1 × Fin N → ℂ)
        (α : Gl.Ω 1 → ℂ), Dec2.IsDecBg (coverOf Gl) Gl a ν (rho4 d L N BG κ) s D φ α →
          Fl (s, (D.Ψ, D.h)) = (φ, α))
    (hFp : ∀ (s : Dec2.DecParams (coverOf Gp)) (D : BgData Gp N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC Gp (bgC0 d L N) (c7 d L N BG κ) ν D → ∀ (φ : Gp.Ω 1 × Fin N → ℂ)
        (α : Gp.Ω 1 → ℂ), Dec2.IsDecBg (coverOf Gp) Gp a ν (rho4 d L N BG κ) s D φ α →
          Fp (s, (D.Ψ, D.h)) = (φ, α))
    {D : BgData Gl N} {D' : BgData Gp N}
    (hDu : InUnionDomainC Gl (bgC0 d L N) (c7 d L N BG κ) ν D)
    (hDu' : InUnionDomainC Gp (bgC0 d L N) (c7 d L N BG κ) ν D')
    (gl : Gl.Ω 1 × Fin N → ℂ) (gp : Gp.Ω 1 × Fin N → ℂ)
    (fldl : (∀ b, Ωb b) → Gl.Ω 1 × Fin N → ℂ) (fldp : (∀ b, Ωb b) → Gp.Ω 1 × Fin N → ℂ)
    (Wl : ((Gl.Ω 1 × Fin N → ℂ) × (Gl.Ω 1 → ℂ)) → Matrix (Gl.Ω 1 × Fin N) (Gl.Ω 1 × Fin N) ℂ)
    (Wp : ((Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)) → Matrix (Gp.Ω 1 × Fin N) (Gp.Ω 1 × Fin N) ℂ)
    (Dl : Matrix (Gl.Ω 1 × Fin N) (Gl.Ω 1 × Fin N) ℂ) (Dp : Matrix (Gp.Ω 1 × Fin N) (Gp.Ω 1 × Fin N) ℂ)
    (ρ rD : ℕ) (R : Set 𝕋₁)
    (hRdeep : ∀ w : 𝕋₁, (∃ t ∈ R, supDist w t ≤ 8 * L ^ (0 + 1 + m₁)) → w ∈ Gl.Ω (0 + 1))
    (hρ : ρ + L ≤ 8 * L ^ (0 + 1 + m₁))
    (d0 : ↥(coverOf Gp).cubeIdx) (d0l : ↥(coverOf Gl).cubeIdx)
    (hWl : ∀ (x : Gl.Ω 1) i r, Dl (x, i) r ≠ 0 → supDist (x : 𝕋₁) r.1 ≤ rD)
    (hWp : ∀ (x' : Gp.Ω 1) i r, Dp (x', i) r ≠ 0 → supDist (x' : 𝕋₁) r.1 ≤ rD)
    (𝒴 : Finset (Set 𝕋₁)) (hdom : ∀ Y ∈ 𝒴, IsDj m₀ 1 Y) {εH κH κ0 Kc' : ℝ}
    (Al Ap : LabelAct (thickLabels (m₀ := m₀) (j := 1) 𝒴 hdom) Ωb εH κH κ0 Kc')
    (hAl : ∀ (y : {Y // Y ∈ 𝒴}) Φ,
      Al.H y Φ = maskedTerm Gl a ν β gl Wl Fl Dl m₀ (ρ + L) rD R y.1 (D.Ψ, D.h) (fldl Φ))
    (hAp : ∀ (y : {Y // Y ∈ 𝒴}) Φ,
      Ap.H y Φ = chartTerm Gp a ν β gp Wp Fp m₀ (ρ + L) y.1 (D'.Ψ, D'.h) (fldp Φ) +
        defTerm Gp Dp m₀ rD y.1 (fldp Φ))
    (μ : ∀ b, MeasureTheory.Measure (Ωb b)) [∀ b, MeasureTheory.IsProbabilityMeasure (μ b)]
    (T : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := 1) m₀ 1 Set.univ))
    (hlabR : ∀ y : {Y // Y ∈ 𝒴}, blocksOf m₀ 1 Set.univ y.1 ⊆ T → y.1 ⊆ R)
    (hdat0 : ∀ z : 𝕋₁, (∃ t ∈ sitesOf T, supDist z t ≤ 4 * L ^ (0 + 1)) →
      D.Ψ z = D'.Ψ z ∧ D.h z = D'.h z)
    (hfl : ∀ Φ, ∀ x : Gl.Ω 1, AnalyticOnNhd ℂ
      (fun s => chartFe Gl a ν β gl (fldl Φ) Wl x (Fl (s, (D.Ψ, D.h))))
      (polydisc (0 : Dec2.DecParams (coverOf Gl)) (fun _ => Real.exp κ)))
    (hgc : ∀ (x : Gl.Ω 1) (x' : Gp.Ω 1), (x : 𝕋₁) = x' → (x : 𝕋₁) ∈ sitesOf T → ∀ i, gp (x', i) = gl (x, i))
    (hWlr : ∀ u p r, Wl u p r ≠ 0 → supDist (p.1 : 𝕋₁) r.1 ≤ ρ)
    (hWpr : ∀ u p r, Wp u p r ≠ 0 → supDist (p.1 : 𝕋₁) r.1 ≤ ρ)
    (hWc : ∀ (u : (Gl.Ω 1 × Fin N → ℂ) × (Gl.Ω 1 → ℂ)) (u' : (Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ))
      (p : Gl.Ω 1 × Fin N) (p' : Gp.Ω 1 × Fin N) (r : Gl.Ω 1 × Fin N) (r' : Gp.Ω 1 × Fin N),
      (p.1 : 𝕋₁) = p'.1 → p.2 = p'.2 → (r.1 : 𝕋₁) = r'.1 → r.2 = r'.2 →
      (∀ (y : Gl.Ω 1) (y' : Gp.Ω 1), (y : 𝕋₁) = y' → supDist (p.1 : 𝕋₁) y ≤ ρ →
        (∀ i, u.1 (y, i) = u'.1 (y', i)) ∧ u.2 y = u'.2 y') → Wp u' p' r' = Wl u p r)
    (hWx : ∀ (x : Gl.Ω 1) (x' : Gp.Ω 1), (x : 𝕋₁) = x' → (x : 𝕋₁) ∈ sitesOf T → ∀ i (r : Gl.Ω 1 × Fin N)
      (r' : Gp.Ω 1 × Fin N), (r.1 : 𝕋₁) = r'.1 → r.2 = r'.2 → Dp (x', i) r' = Dl (x, i) r)
    (hψ : ∀ Φ, ∀ (r : Gl.Ω 1 × Fin N) (r' : Gp.Ω 1 × Fin N), (r.1 : 𝕋₁) = r'.1 → r.2 = r'.2 →
      (r.1 : 𝕋₁) ∈ sitesOf T → fldp Φ r' = fldl Φ r) :
    Pst μ (thickLabels (m₀ := m₀) (j := 1) 𝒴 hdom) Al.H T =
      Pst μ (thickLabels (m₀ := m₀) (j := 1) 𝒴 hdom) Ap.H T := by
  refine Pst_congr μ μ Al Ap.H T (fun _ _ => rfl) (fun y hy => ?_)
  funext Φ
  have hYT : y.1 ⊆ sitesOf T := by
    have hs := sitesOf_blocksOf hN (le_refl 1) isPiUnion_univ_K
      ((thickLabels (m₀ := m₀) (j := 1) 𝒴 hdom).isDj y).2.1
    intro z hz
    have hz' : z ∈ sitesOf (blocksOf m₀ 1 Set.univ y.1) := by
      rw [show (thickLabels (m₀ := m₀) (j := 1) 𝒴 hdom).ysite y = y.1 from rfl] at hs
      rw [hs]; exact ⟨hz, Set.mem_univ _⟩
    exact sitesOf_mono hy hz'
  rw [hAl y Φ, hAp y Φ]
  exact (maskedTerm_cross hG' hm₁ hN hS Sl Sp HBl HBp hκ hM hFl hFp hDu hDu' gl (fldl Φ) gp (fldp Φ) Wl Wp
    Dl Dp ρ rD R y.1 (hlabR y hy) hRdeep hρ
    (fun z ⟨t, ht, hd⟩ => hdat0 z ⟨t, hYT ht, hd⟩) (hfl Φ)
    (fun x x' hxx hx i => hgc x x' hxx (hYT hx) i) hWlr hWpr hWc d0 d0l hWl hWp
    (fun x x' hxx hx => hWx x x' hxx (hYT hx))
    (fun r r' h1 h2 hr => hψ Φ r r' h1 h2 (hYT hr))).symm

end PstCross

end Cross

end Balaban.LargeField.Base
