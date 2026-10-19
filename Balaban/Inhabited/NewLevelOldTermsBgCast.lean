/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.NewLevelOldTermsBg
public import Balaban.Inhabited.NewLevelCoeffBgCast
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The marks and activities of the old labels recomputed on a local generating set
(`NewLevelOldTermsBgCast`)

P3 pp. 78-79, (4.44)-(4.47): the marks `G₁` and the activities `H` of the localized old terms of the
new level, recomputed on a local generating set `Gl` with the canonical transport
(`oldMarkGBg`, `oldActBg` at `BgTransport.canon`), equal the step's objects (`oldMarkGBg`,
`oldActBg` at `BgTransport.self`) at the datum read from a datum `D` of the step chart, on the
labels whose `2 M₁ L^{k+1}`-neighbourhood lies in the top layer of `Gl` and whose read region (the
cubes meeting the set `X₁` of the old term and the data sites of its generating set) lies in the
label.  The step's maps are pinned at the levels of the step (`δ₀ ≥ 2 K₄ C₁ ε`); the recomputed
maps at the levels of the read datum (`δ₀' ≥ 2 K₄ C₁ ε′`, `ε′ ≥ (2 K₁ + 2) C₁ ε`).

* `oldMarkGBg_canon_eq`: the replacement identity for the marks;
* `oldActBg_canon_eq`: the replacement identity for the activities;
* `eventually_markedRad_lt`: the radius set of the marks is a neighbourhood of `0` in the second
  mark.
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Fluctuation Balaban.Multiscale Balaban.Background Balaban.Localization
  Balaban.SmallField Balaban.LargeField Finset

section Marks

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ ϱm ϱl ϱl' ϱ₁ ϱ₂ : ℝ}

/-- The mark radius set contains a neighbourhood of `0` in the second mark. -/
theorem eventually_markedRad_lt {mR δ₁ Ru : ℝ} (h1 : 0 < δ₁) (hRu : Ru * mR < δ₁) {u : ℂ}
    (hu : ‖u‖ < Ru) : ∀ᶠ t in nhds (0 : ℂ), (‖u‖ + ‖t‖) * mR < δ₁ := by
  have hopen : IsOpen {t : ℂ | (‖u‖ + ‖t‖) * mR < δ₁} :=
    isOpen_lt (by fun_prop) continuous_const
  refine hopen.mem_nhds ?_
  show (‖u‖ + ‖(0 : ℂ)‖) * mR < δ₁
  rw [norm_zero, add_zero]
  rcases le_or_gt 0 mR with h | h
  · nlinarith [norm_nonneg u]
  · nlinarith [norm_nonneg u]

/-- **The marks of an old label recomputed on a local generating set equal the step's marks**
(P3 pp. 78-79, (4.46)).  Let `Gl` be cube aligned and sup-separated, `Gd ≺ Gl` with the layer `k`
of `Gl` and no layer `k + 1`, and let the maps `F₁ τ`, `Sol τ` of the step and `F₁' τ`, `Sol' τ` of
`(Gl, Gd)` be given by their specifications (the step's at the levels `(δ₀, δ₁)`, the recomputed
ones at `(δ₀', δ₁)`).  For a datum `D` of the step chart of radius `ε`, the step's parameter `θ`
with the datum `D` and the parameter `θ_b` of `Gl` with the read datum, the mark of the pair
`q = (τ, Y)` recomputed on `Gl` (mask `maskPre`, gate radius `ε′ ≥ (2 K₁ + 2) C₁ ε`) equals the
step's mark (gate radius `ε₀ ≥ ε`), when the cubes meeting `X₁(τ)` and the data sites of `Gk τ`
lie in `Y` and the `2 M₁ L^{k+1}`-neighbourhood of `Y` lies in the top layer of `Gl`. -/
theorem oldMarkGBg_canon_eq (S : StepSetting d L N₁ m₁ k N ϱ)
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
    {ι : Type*} [Fintype ι]
    {F₁ : ι → Dec2.DecParams (coverOf S.G') × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      (S.G'.Ω 1 × Fin N → ℂ) × (S.G'.Ω 1 → ℂ)}
    {F₁' : ι → Dec2.DecParams (coverOf Gl) × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      (Gl.Ω 1 × Fin N → ℂ) × (Gl.Ω 1 → ℂ)}
    (hF₁ : ∀ τ (s : Dec2.DecParams (coverOf S.G')) (D : BgData S.G' N),
      (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC S.G' (bgC0 d L N) (c7 d L N BG κ) S.ν D → ∀ (φ : S.G'.Ω 1 × Fin N → ℂ)
        (α : S.G'.Ω 1 → ℂ), Dec2.IsDecBg (coverOf S.G') S.G' (compWeight L S.a₁) S.ν
          (rho4 d L N BG κ) s D φ α → F₁ τ (s, rawOf D) = (φ, α))
    (hF₁' : ∀ τ (s : Dec2.DecParams (coverOf Gl)) (D : BgData Gl N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC Gl (bgC0 d L N) (c7 d L N BG κ) S.ν D → ∀ (φ : Gl.Ω 1 × Fin N → ℂ)
        (α : Gl.Ω 1 → ℂ), Dec2.IsDecBg (coverOf Gl) Gl (compWeight L S.a₁) S.ν
          (rho4 d L N BG κ) s D φ α → F₁' τ (s, rawOf D) = (φ, α))
    {c₂ BG₂ : ℝ} (hF₂ : Dec2.FamSpec d L (Dec2.mixedKc d L) (Cchi d L) c₂ BG₂)
    (hM₂ : c₂ * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δ₀ δ₀' δ₁ : ℝ} (h0 : 0 ≤ δ₀) (h0' : 0 ≤ δ₀')
    (h1 : 0 < δ₁)
    (hδ₀ : δ₀ ≤ deltaStar' d L N (famConst d L BG₂ κ) (gamma1 d / 8))
    (hδ₀' : δ₀' ≤ deltaStar' d L N (famConst d L BG₂ κ) (gamma1 d / 8))
    (hδ₁ : δ₁ ≤ deltaStar' d L N (famConst d L BG₂ κ) (gamma1 d / 8))
    {Sol : ι → Dec2.DecParams (coverOf S.G') × Edat Hm N → (Hm.Ω 1 × Fin N → ℂ) × (Hm.Ω 1 → ℂ)}
    {Sol' : ι → Dec2.DecParams (coverOf Gl) × Edat Gd N → (Gd.Ω 1 × Fin N → ℂ) × (Gd.Ω 1 → ℂ)}
    (hSol : ∀ τ (p : Dec2.DecParams (coverOf S.G') × Edat Hm N), (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM Hm N false δ₀ δ₁ p.2 →
        (Sol τ p).1 = dphi Hm (Dec2.decG (coverOf S.G') Hm (compWeight L S.a₁) S.ν p.1) p.2.2.1
          p.2.1 (pertSource Hm (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) (Sol τ p).2 ∧
        Dec2.DecFixed (coverOf S.G') Hm (compWeight L S.a₁) S.ν p.1 false p.2.2.1 p.2.1
          (pertSource Hm (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) (Sol τ p).2 ∧
        Small Hm (Sol τ p).2 (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
        Small Hm (Sol τ p).2 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        SupBounds Hm (Sol τ p).1 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        (∀ δα' : Hm.Ω 1 → ℂ, Small Hm δα' (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf S.G') Hm (compWeight L S.a₁) S.ν p.1 false p.2.2.1 p.2.1
            (pertSource Hm (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol τ p).2))
    (hSol' : ∀ τ (p : Dec2.DecParams (coverOf Gl) × Edat Gd N), (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM Gd N false δ₀' δ₁ p.2 →
        (Sol' τ p).1 = dphi Gd (Dec2.decG (coverOf Gl) Gd (compWeight L S.a₁) S.ν p.1) p.2.2.1
          p.2.1 (pertSource Gd (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) (Sol' τ p).2 ∧
        Dec2.DecFixed (coverOf Gl) Gd (compWeight L S.a₁) S.ν p.1 false p.2.2.1 p.2.1
          (pertSource Gd (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) (Sol' τ p).2 ∧
        Small Gd (Sol' τ p).2 (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
        Small Gd (Sol' τ p).2 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        SupBounds Gd (Sol' τ p).1 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        (∀ δα' : Gd.Ω 1 → ℂ, Small Gd δα' (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf Gl) Gd (compWeight L S.a₁) S.ν p.1 false p.2.2.1 p.2.1
            (pertSource Gd (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol' τ p).2))
    (Gk : ι → GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ₁)
    (Gj : ι → GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ₂) (ac : ℕ → ℝ)
    (Fk : ∀ τ, RawData d L (N₁ * L ^ m₁) (k + 1) N → ((Gk τ).Ω 1 × Fin N → ℂ) × ((Gk τ).Ω 1 → ℂ))
    (E : ι → RawData d L (N₁ * L ^ m₁) (k + 1) N → ℂ)
    {eps eps₀ eps' : ℝ} (heps : 0 < eps) (hsmall : (4 * d + 6) * ((2 * d + 1) * eps) ≤ 1)
    (hc7 : xiC1 d * eps ≤ c7 d L N BG κ) (hphi : (3 + K4 d L N BG κ) * (xiC1 d * eps) < 1 / 2)
    (heps₀ : eps ≤ eps₀) (hεr : (2 * bgK1 d L N + 2) * xiC1 d * eps ≤ eps')
    (hsmall' : (4 * d + 6) * ((2 * d + 1) * eps') ≤ 1) (hc7' : xiC1 d * eps' ≤ c7 d L N BG κ)
    (hphi' : (3 + K4 d L N BG κ) * (xiC1 d * eps') < 1 / 2)
    (hδ₀a : 2 * (K4 d L N BG κ * (xiC1 d * eps)) ≤ δ₀)
    (hδ₀e : 2 * (K4 d L N BG κ * (xiC1 d * eps')) ≤ δ₀')
    {δc : ℝ} (hmarD' : decDomMargin d L N BG κ (xiC1 d * eps') < δc)
    (hαD' : K4 d L N BG κ * (xiC1 d * eps') < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4) {cψ ρ : ℝ} (hρ : 0 < ρ) (hρc : ρ ≤ cψ)
    (hp : 0 < S.p₁) {Ru : ℝ}
    (hRu : Ru * markedRad d L N k S.a₁ κ cψ ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) < δ₁)
    (X₁f : ι → Finset (CTorus d L N₁ m₁ (k + 1))) (m₀ : ℕ) (jL : ι → ℕ)
    (𝒦X : ι → Set (CTorus d L N₁ m₁ (k + 1))) (hU : LayerUnion S.G' m₀) (hNm : L ^ m₀ ∣ N₁)
    (Zm : Finset (unitPts S.G')) (z : RootIdx d L N₁ m₁ (k + 1))
    (q : {q // q ∈ markedIdx (fun _ => (Set.univ : Set (CTorus d L N₁ m₁ (k + 1))))
      (fun τ => polyDom S.G' (X₁f τ) m₀ (jL τ) (𝒦X τ)) z})
    (hXY : ∀ P ∈ cubeIdx S.G',
      ¬ Disjoint (Pset m₁ P) (↑(X₁f q.1.1) : Set (CTorus d L N₁ m₁ (k + 1))) →
      ∀ y ∈ Pset m₁ P, y ∈ q.1.2)
    (hkY : ∀ x ∈ dataSites (Gk q.1.1), x ∈ q.1.2)
    (hYmar : ∀ x ∈ q.1.2, ∀ y, supDist x y ≤ 2 * L ^ (k + 1 + m₁) → y ∈ Gl.Ω (k + 1))
    {D : BgData S.G' N} (hD : XiCData S.G' (compWeight L S.a₁) S.ν (k + 1) 1 eps D)
    (θ : physParam N S) (hθ : (θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) = rawOf D)
    (θb : physParamBg N Gl)
    (hθb : (θb.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) = clipRaw Gl (rawOf D))
    (u : ℂ) (Ψ : ∀ b, (S.blockSplit 1 hp).Ωb b) :
    oldMarkGBg S Gl (BgTransport.canon S.G' Gl N) (maskPre S.hG' Gl Zm) X₁f m₀ jL 𝒦X F₁' Sol'
        (fun τ => eTermFun Gl (Gk τ) (Gj τ) Gd ac (Fk τ) (E τ)) ρ hp Ru eps' z θb q u Ψ =
      oldMarkGBg S S.G' (BgTransport.self S.hG') Zm X₁f m₀ jL 𝒦X F₁ Sol
        (fun τ => eTermFun S.G' (Gk τ) (Gj τ) Hm ac (Fk τ) (E τ)) ρ hp Ru eps₀ z θ q u Ψ := by
  classical
  obtain ⟨⟨θr, hθr⟩, θs⟩ := θ
  obtain ⟨⟨θbr, hθbr⟩, θbs⟩ := θb
  simp only at hθ hθb
  subst hθ hθb
  by_cases hu : ‖u‖ < Ru
  · have hd0 : 0 < d := by have := HB.hd; omega
    have hc1 : xiC1 d * eps ≤ bgC1 d L N := hc7.trans (c7_le_bgC1 d L N BG κ)
    have hc0 : xiC1 d * eps ≤ bgC0 d L N := hc1.trans (bgC1_le_bgC0 d L N hd0)
    have hgate : rawOf D ∈ XiCRaw S.G' (compWeight L S.a₁) S.ν (k + 1) 1 eps₀ :=
      ⟨D, xiCData_mono_radius zero_le_one heps₀ hD, rfl⟩
    have hgateb : clipRaw Gl (rawOf D) ∈ XiCRaw Gl (compWeight L S.a₁) S.ν (k + 1) 1 eps' :=
      ⟨_, canon_gdat_xiCData_of_xiCData (Gb := Gl) S.hG' HB HB' heps hsmall hc0 hc1 hεr D hD, rfl⟩
    simp only [oldMarkGBg, hgateb, hgate, hu, and_self, ↓reduceIte]
    refine congrArg (fun x => (S.β : ℂ) * x) (Filter.EventuallyEq.deriv_eq ?_)
    filter_upwards [eventually_markedRad_lt h1 hRu hu] with t ht
    have hdat : (BgTransport.canon S.G' Gl N).dat (clipRaw Gl (rawOf D)) =
        (BgTransport.canon S.G' Gl N).dat (rawOf D) := by
      show clipRaw Gl _ = clipRaw Gl _
      rw [clipRaw_clipRaw]
    exact (evDecBg_congr_dat (X₁f q.1.1) m₀ (jL q.1.1) (𝒦X q.1.1) S.a₁ S.ν
      (BgTransport.canon S.G' Gl N) _ (F₁' q.1.1) (Sol' q.1.1) _ (maskPre S.hG' Gl Zm) u t q.1.2
      hdat _).trans
      (evDecBg_canon_eq_evDec S.hG' hG S.hk1 hA hSS hPd hdk hdtop hN hm₁ hM hag hagm hagl hagd hS
        HB HB' ha₁ ha₂ hκ hMc hMX (hF₁ q.1.1) (hF₁' q.1.1) hF₂ hM₂ h0 h0' h1 hδ₀ hδ₀' hδ₁
        (hSol q.1.1) (hSol' q.1.1) ac (Fk q.1.1) (E q.1.1) heps hsmall hc7 hphi hεr hsmall' hc7'
        hphi' hδ₀a hδ₀e hmarD' hαD' hsm _ (hρ.le.trans hρc) Zm u t ht hU hNm q.1.2 hXY hkY hYmar hD
        _ (fun p => (S.hatOf_mem 1 hρ hp Ψ p).trans hρc))
  · simp only [oldMarkGBg, hu, and_false, ↓reduceIte]

/-- **The activities of an old label recomputed on a local generating set equal the step's
activities** (P3 pp. 78-79, (4.46)): the statement of `oldMarkGBg_canon_eq` for the activity of
a label `Y` of the old terms, `β (evDec(u, 0) − evDec(0, 0))` summed over the old terms whose
expansion has the domain `Y`, when for each of them the cubes meeting its set `X₁` and the data
sites of its generating set lie in `Y`. -/
theorem oldActBg_canon_eq (S : StepSetting d L N₁ m₁ k N ϱ)
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
    {ι : Type*} [Fintype ι]
    {F₁ : ι → Dec2.DecParams (coverOf S.G') × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      (S.G'.Ω 1 × Fin N → ℂ) × (S.G'.Ω 1 → ℂ)}
    {F₁' : ι → Dec2.DecParams (coverOf Gl) × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      (Gl.Ω 1 × Fin N → ℂ) × (Gl.Ω 1 → ℂ)}
    (hF₁ : ∀ τ (s : Dec2.DecParams (coverOf S.G')) (D : BgData S.G' N),
      (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC S.G' (bgC0 d L N) (c7 d L N BG κ) S.ν D → ∀ (φ : S.G'.Ω 1 × Fin N → ℂ)
        (α : S.G'.Ω 1 → ℂ), Dec2.IsDecBg (coverOf S.G') S.G' (compWeight L S.a₁) S.ν
          (rho4 d L N BG κ) s D φ α → F₁ τ (s, rawOf D) = (φ, α))
    (hF₁' : ∀ τ (s : Dec2.DecParams (coverOf Gl)) (D : BgData Gl N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC Gl (bgC0 d L N) (c7 d L N BG κ) S.ν D → ∀ (φ : Gl.Ω 1 × Fin N → ℂ)
        (α : Gl.Ω 1 → ℂ), Dec2.IsDecBg (coverOf Gl) Gl (compWeight L S.a₁) S.ν
          (rho4 d L N BG κ) s D φ α → F₁' τ (s, rawOf D) = (φ, α))
    {c₂ BG₂ : ℝ} (hF₂ : Dec2.FamSpec d L (Dec2.mixedKc d L) (Cchi d L) c₂ BG₂)
    (hM₂ : c₂ * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δ₀ δ₀' δ₁ : ℝ} (h0 : 0 ≤ δ₀) (h0' : 0 ≤ δ₀')
    (h1 : 0 < δ₁)
    (hδ₀ : δ₀ ≤ deltaStar' d L N (famConst d L BG₂ κ) (gamma1 d / 8))
    (hδ₀' : δ₀' ≤ deltaStar' d L N (famConst d L BG₂ κ) (gamma1 d / 8))
    (hδ₁ : δ₁ ≤ deltaStar' d L N (famConst d L BG₂ κ) (gamma1 d / 8))
    {Sol : ι → Dec2.DecParams (coverOf S.G') × Edat Hm N → (Hm.Ω 1 × Fin N → ℂ) × (Hm.Ω 1 → ℂ)}
    {Sol' : ι → Dec2.DecParams (coverOf Gl) × Edat Gd N → (Gd.Ω 1 × Fin N → ℂ) × (Gd.Ω 1 → ℂ)}
    (hSol : ∀ τ (p : Dec2.DecParams (coverOf S.G') × Edat Hm N), (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM Hm N false δ₀ δ₁ p.2 →
        (Sol τ p).1 = dphi Hm (Dec2.decG (coverOf S.G') Hm (compWeight L S.a₁) S.ν p.1) p.2.2.1
          p.2.1 (pertSource Hm (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) (Sol τ p).2 ∧
        Dec2.DecFixed (coverOf S.G') Hm (compWeight L S.a₁) S.ν p.1 false p.2.2.1 p.2.1
          (pertSource Hm (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) (Sol τ p).2 ∧
        Small Hm (Sol τ p).2 (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
        Small Hm (Sol τ p).2 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        SupBounds Hm (Sol τ p).1 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        (∀ δα' : Hm.Ω 1 → ℂ, Small Hm δα' (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf S.G') Hm (compWeight L S.a₁) S.ν p.1 false p.2.2.1 p.2.1
            (pertSource Hm (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol τ p).2))
    (hSol' : ∀ τ (p : Dec2.DecParams (coverOf Gl) × Edat Gd N), (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM Gd N false δ₀' δ₁ p.2 →
        (Sol' τ p).1 = dphi Gd (Dec2.decG (coverOf Gl) Gd (compWeight L S.a₁) S.ν p.1) p.2.2.1
          p.2.1 (pertSource Gd (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) (Sol' τ p).2 ∧
        Dec2.DecFixed (coverOf Gl) Gd (compWeight L S.a₁) S.ν p.1 false p.2.2.1 p.2.1
          (pertSource Gd (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) (Sol' τ p).2 ∧
        Small Gd (Sol' τ p).2 (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
        Small Gd (Sol' τ p).2 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        SupBounds Gd (Sol' τ p).1 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        (∀ δα' : Gd.Ω 1 → ℂ, Small Gd δα' (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf Gl) Gd (compWeight L S.a₁) S.ν p.1 false p.2.2.1 p.2.1
            (pertSource Gd (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol' τ p).2))
    (Gk : ι → GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ₁)
    (Gj : ι → GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ₂) (ac : ℕ → ℝ)
    (Fk : ∀ τ, RawData d L (N₁ * L ^ m₁) (k + 1) N → ((Gk τ).Ω 1 × Fin N → ℂ) × ((Gk τ).Ω 1 → ℂ))
    (E : ι → RawData d L (N₁ * L ^ m₁) (k + 1) N → ℂ)
    {eps eps₀ eps' : ℝ} (heps : 0 < eps) (hsmall : (4 * d + 6) * ((2 * d + 1) * eps) ≤ 1)
    (hc7 : xiC1 d * eps ≤ c7 d L N BG κ) (hphi : (3 + K4 d L N BG κ) * (xiC1 d * eps) < 1 / 2)
    (heps₀ : eps ≤ eps₀) (hεr : (2 * bgK1 d L N + 2) * xiC1 d * eps ≤ eps')
    (hsmall' : (4 * d + 6) * ((2 * d + 1) * eps') ≤ 1) (hc7' : xiC1 d * eps' ≤ c7 d L N BG κ)
    (hphi' : (3 + K4 d L N BG κ) * (xiC1 d * eps') < 1 / 2)
    (hδ₀a : 2 * (K4 d L N BG κ * (xiC1 d * eps)) ≤ δ₀)
    (hδ₀e : 2 * (K4 d L N BG κ * (xiC1 d * eps')) ≤ δ₀')
    {δc : ℝ} (hmarD' : decDomMargin d L N BG κ (xiC1 d * eps') < δc)
    (hαD' : K4 d L N BG κ * (xiC1 d * eps') < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4) {cψ ρ : ℝ} (hρ : 0 < ρ) (hρc : ρ ≤ cψ)
    (hp : 0 < S.p₁) {Ru : ℝ}
    (hRu : Ru * markedRad d L N k S.a₁ κ cψ ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) < δ₁)
    (X₁f : ι → Finset (CTorus d L N₁ m₁ (k + 1))) (m₀ : ℕ) (jL : ι → ℕ)
    (𝒦X : ι → Set (CTorus d L N₁ m₁ (k + 1))) (hU : LayerUnion S.G' m₀) (hNm : L ^ m₀ ∣ N₁)
    (Zm : Finset (unitPts S.G')) (𝒴C : Finset (Set (CTorus d L N₁ m₁ (k + 1))))
    (Y : {Y // Y ∈ 𝒴C})
    (hXY : ∀ τ, Y.1 ∈ polyDom S.G' (X₁f τ) m₀ (jL τ) (𝒦X τ) → ∀ P ∈ cubeIdx S.G',
      ¬ Disjoint (Pset m₁ P) (↑(X₁f τ) : Set (CTorus d L N₁ m₁ (k + 1))) → ∀ y ∈ Pset m₁ P, y ∈ Y.1)
    (hkY : ∀ τ, Y.1 ∈ polyDom S.G' (X₁f τ) m₀ (jL τ) (𝒦X τ) → ∀ x ∈ dataSites (Gk τ), x ∈ Y.1)
    (hYmar : ∀ x ∈ Y.1, ∀ y, supDist x y ≤ 2 * L ^ (k + 1 + m₁) → y ∈ Gl.Ω (k + 1))
    {D : BgData S.G' N} (hD : XiCData S.G' (compWeight L S.a₁) S.ν (k + 1) 1 eps D)
    (θ : physParam N S) (hθ : (θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) = rawOf D)
    (θb : physParamBg N Gl)
    (hθb : (θb.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) = clipRaw Gl (rawOf D))
    (u : ℂ) (Ψ : ∀ b, (S.blockSplit 1 hp).Ωb b) :
    oldActBg S Gl (BgTransport.canon S.G' Gl N) (maskPre S.hG' Gl Zm) X₁f m₀ jL 𝒦X F₁' Sol'
        (fun τ => eTermFun Gl (Gk τ) (Gj τ) Gd ac (Fk τ) (E τ)) ρ hp Ru eps' 𝒴C θb Y u Ψ =
      oldActBg S S.G' (BgTransport.self S.hG') Zm X₁f m₀ jL 𝒦X F₁ Sol
        (fun τ => eTermFun S.G' (Gk τ) (Gj τ) Hm ac (Fk τ) (E τ)) ρ hp Ru eps₀ 𝒴C θ Y u Ψ := by
  classical
  obtain ⟨⟨θr, hθr⟩, θs⟩ := θ
  obtain ⟨⟨θbr, hθbr⟩, θbs⟩ := θb
  simp only at hθ hθb
  subst hθ hθb
  by_cases hu : ‖u‖ < Ru
  · have hd0 : 0 < d := by have := HB.hd; omega
    have hc1 : xiC1 d * eps ≤ bgC1 d L N := hc7.trans (c7_le_bgC1 d L N BG κ)
    have hc0 : xiC1 d * eps ≤ bgC0 d L N := hc1.trans (bgC1_le_bgC0 d L N hd0)
    have hgate : rawOf D ∈ XiCRaw S.G' (compWeight L S.a₁) S.ν (k + 1) 1 eps₀ :=
      ⟨D, xiCData_mono_radius zero_le_one heps₀ hD, rfl⟩
    have hgateb : clipRaw Gl (rawOf D) ∈ XiCRaw Gl (compWeight L S.a₁) S.ν (k + 1) 1 eps' :=
      ⟨_, canon_gdat_xiCData_of_xiCData (Gb := Gl) S.hG' HB HB' heps hsmall hc0 hc1 hεr D hD, rfl⟩
    have hdat : (BgTransport.canon S.G' Gl N).dat (clipRaw Gl (rawOf D)) =
        (BgTransport.canon S.G' Gl N).dat (rawOf D) := by
      show clipRaw Gl _ = clipRaw Gl _
      rw [clipRaw_clipRaw]
    have hu0 : ‖(0 : ℂ)‖ < Ru := lt_of_le_of_lt (by rw [norm_zero]; exact norm_nonneg u) hu
    -- the replacement of the term of the label `Y` of the old term `τ` at the marks `(um, 0)`
    have key : ∀ τ, Y.1 ∈ polyDom S.G' (X₁f τ) m₀ (jL τ) (𝒦X τ) → ∀ um : ℂ, ‖um‖ < Ru →
        evDecBg S.G' (X₁f τ) m₀ (jL τ) (𝒦X τ) Gl S.a₁ S.ν (BgTransport.canon S.G' Gl N)
          ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) (F₁' τ) (Sol' τ)
          (eTermFun Gl (Gk τ) (Gj τ) Gd ac (Fk τ) (E τ)) (maskPre S.hG' Gl Zm) um 0 Y.1
          (clipRaw Gl (rawOf D), (BgTransport.canon S.G' Gl N).res (S.hatOf 1 ρ hp Ψ)) =
        evDecBg S.G' (X₁f τ) m₀ (jL τ) (𝒦X τ) S.G' S.a₁ S.ν (BgTransport.self S.hG')
          ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) (F₁ τ) (Sol τ)
          (eTermFun S.G' (Gk τ) (Gj τ) Hm ac (Fk τ) (E τ)) Zm um 0 Y.1
          (rawOf D, (BgTransport.self S.hG').res (S.hatOf 1 ρ hp Ψ)) := fun τ hτ um hum =>
      (evDecBg_congr_dat (X₁f τ) m₀ (jL τ) (𝒦X τ) S.a₁ S.ν (BgTransport.canon S.G' Gl N) _
        (F₁' τ) (Sol' τ) _ (maskPre S.hG' Gl Zm) um 0 Y.1 hdat _).trans
        (evDecBg_canon_eq_evDec S.hG' hG S.hk1 hA hSS hPd hdk hdtop hN hm₁ hM hag hagm hagl hagd
          hS HB HB' ha₁ ha₂ hκ hMc hMX (hF₁ τ) (hF₁' τ) hF₂ hM₂ h0 h0' h1 hδ₀ hδ₀' hδ₁ (hSol τ)
          (hSol' τ) ac (Fk τ) (E τ) heps hsmall hc7 hphi hεr hsmall' hc7' hphi' hδ₀a hδ₀e hmarD'
          hαD' hsm _ (hρ.le.trans hρc) Zm um 0 (eventually_markedRad_lt h1 hRu hum).self_of_nhds
          hU hNm Y.1 (hXY τ hτ) (hkY τ hτ) hYmar hD _
          (fun p => (S.hatOf_mem 1 hρ hp Ψ p).trans hρc))
    simp only [oldActBg, hgateb, hgate, hu, and_self, ↓reduceIte]
    refine Finset.sum_congr rfl fun τ _ => ?_
    by_cases hτ : Y.1 ∈ polyDom S.G' (X₁f τ) m₀ (jL τ) (𝒦X τ)
    · simp only [hτ, ↓reduceIte]
      rw [key τ hτ u hu, key τ hτ 0 hu0]
    · simp only [hτ, ↓reduceIte]
  · simp only [oldActBg, hu, and_false, ↓reduceIte]

end Marks

end Balaban.Inhabited
