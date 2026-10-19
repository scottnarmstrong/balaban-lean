/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.NewLevelBlockTermsBg
public import Balaban.Inhabited.E1MarkParamCommonG
public import Balaban.Inhabited.NewLevelOldTermsBgCast

/-!
# The bridge marks recomputed on a local generating set (`NewLevelBridgeMarksBgCast`)

P3 pp. 78-79, (4.44)-(4.47): the mark of the root `z` at a bridge label `Y′` of the new level, the
rooted corrected output of the marked terms of the localized block energies, recomputed on a local
generating set `Gl` (pairs `(F₁′, Sol′)` of `(Gl, Gd)`, the canonical transport, the mask `maskPre`
of the block of the root, the parameter of `Gl`) equals the step's mark at the datum read from a
datum of the step chart, when the `2 M₁ L^{k+1}`-neighbourhood of `Y′` lies in the top layer of `Gl`.

* `e1Dom_read`: the read region of a label `Y` of the local cover of a block `b` (the cubes meeting
  the region `X₁` of the cover and the block itself) lies in `Y`;
* `e1MarkGParamGBgOn_canon_eq`: **the replacement identity for the bridge marks**.  For every pair
  `(b, Y)` of the fibre of `Y′` (`Y ⊆ bridge z Y = Y′`) the terms of the block energy agree on the
  radius set of the marks (`evDecBg_canon_eq_evDec_block`), hence so do the marks and their Taylor
  remainders (`decMarkCorrBg_eq_of_evDecBg`) and the rooted outputs.  The radius condition is
  `(17/16) m_R < δ₁` (the marks are gated at `‖u‖ < 17/16`).
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Fluctuation Balaban.Multiscale Balaban.Background Balaban.Localization
  Balaban.SmallField Balaban.LargeField Finset

section Read

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}

/-- **The read region of a label of the local cover of a block lies in the label**: for
`Y ∈ e1DomG S b` (a domain of the expansion of the local cover of the block `b`), the cubes of the
step's set meeting the region `X₁ = nbhdF 1 (blockSite k b)` lie in `Y`, and so does the block
`B_{k+1}(b)`. -/
theorem e1Dom_read (S : StepSetting d L N₁ m₁ k N ϱ) (hN1 : L ^ 1 ∣ N₁)
    (b : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1)))) {Y : Set (CTorus d L N₁ m₁ (k + 1))}
    (hY : Y ∈ e1DomG S b) :
    (∀ P ∈ cubeIdx S.G', ¬ Disjoint (Pset m₁ P)
        (↑(LocalCover.nbhdF 1 (LocalCover.blockSite k b)) : Set (CTorus d L N₁ m₁ (k + 1))) →
      ∀ y ∈ Pset m₁ P, y ∈ Y) ∧
      ∀ x ∈ blockSites d L N₁ m₁ (k + 1) k b, x ∈ Y := by
  have hX := LocalCover.coe_nbhdF_eq_X1 S.hG' hN1 (le_refl (k + 1)) (LocalCover.blockSite k b)
  have hcov := LocalCover.covSetup S.hG' hN1 (le_refl (k + 1)) (LocalCover.blockSite k b)
  have hXY := subset_polyDom hY
  refine ⟨fun P hP hdis y hy => ?_, fun x hx => ?_⟩
  · rw [hX] at hdis
    exact hXY (Pset_subset_of_not_disjoint hcov.polySetup hP hdis hy)
  · refine hXY ?_
    rw [← hX]
    exact LocalCover.blockSites_subset_nbhdF 1 (le_refl (k + 1)) b (Finset.mem_coe.2 hx)

end Read

section Marks

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ ϱm ϱl ϱl' : ℝ}

/-- **The bridge marks recomputed on a local generating set equal the step's marks** (P3
pp. 78-79, (4.46)).  Let `Gl` be cube aligned and sup-separated, `Gd ≺ Gl` with the layer `k` of `Gl`
and no layer `k + 1`, and let the maps `F₁ b`, `Sol b` of the step and `F₁' b`, `Sol' b` of
`(Gl, Gd)` be given by their specifications (the step's at the levels `(δ₀, δ₁)`, the recomputed ones
at `(δ₀', δ₁)`).  For a datum `D` of the step chart of radius `ε`, the step's parameter `θ` with the
datum `D` and the parameter `θ_b` of `Gl` with the read datum, the mark of the root `z` at the bridge
label `Y′` recomputed on `Gl` (canonical transport, mask `maskPre` of the block of the root, gate
radius `ε′ ≥ (2 K₁ + 2) C₁ ε` on the chart of `Gl`) equals the step's mark (gate radius `ε₀ ≥ ε`),
when the `2 M₁ L^{k+1}`-neighbourhood of `Y′` lies in the top layer of `Gl`.  The hypotheses on
`ε′` are smallness conditions against absolute constants; `(17/16) m_R < δ₁` is the radius condition
of the marks. -/
theorem e1MarkGParamGBgOn_canon_eq (S : StepSetting d L N₁ m₁ k N ϱ)
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
    {F₁ : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) →
      Dec2.DecParams (coverOf S.G') × RawData d L (N₁ * L ^ m₁) (k + 1) N →
        (S.G'.Ω 1 × Fin N → ℂ) × (S.G'.Ω 1 → ℂ)}
    {F₁' : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) →
      Dec2.DecParams (coverOf Gl) × RawData d L (N₁ * L ^ m₁) (k + 1) N →
        (Gl.Ω 1 × Fin N → ℂ) × (Gl.Ω 1 → ℂ)}
    (hF₁ : ∀ b (s : Dec2.DecParams (coverOf S.G')) (D : BgData S.G' N),
      (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC S.G' (bgC0 d L N) (c7 d L N BG κ) S.ν D → ∀ (φ : S.G'.Ω 1 × Fin N → ℂ)
        (α : S.G'.Ω 1 → ℂ), Dec2.IsDecBg (coverOf S.G') S.G' (compWeight L S.a₁) S.ν
          (rho4 d L N BG κ) s D φ α → F₁ b (s, rawOf D) = (φ, α))
    (hF₁' : ∀ b (s : Dec2.DecParams (coverOf Gl)) (D : BgData Gl N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC Gl (bgC0 d L N) (c7 d L N BG κ) S.ν D → ∀ (φ : Gl.Ω 1 × Fin N → ℂ)
        (α : Gl.Ω 1 → ℂ), Dec2.IsDecBg (coverOf Gl) Gl (compWeight L S.a₁) S.ν
          (rho4 d L N BG κ) s D φ α → F₁' b (s, rawOf D) = (φ, α))
    {c₂ BG₂ : ℝ} (hF₂ : Dec2.FamSpec d L (Dec2.mixedKc d L) (Cchi d L) c₂ BG₂)
    (hM₂ : c₂ * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δ₀ δ₀' δ₁ : ℝ} (h0 : 0 ≤ δ₀) (h0' : 0 ≤ δ₀')
    (h1 : 0 < δ₁)
    (hδ₀ : δ₀ ≤ deltaStar' d L N (famConst d L BG₂ κ) (gamma1 d / 8))
    (hδ₀' : δ₀' ≤ deltaStar' d L N (famConst d L BG₂ κ) (gamma1 d / 8))
    (hδ₁ : δ₁ ≤ deltaStar' d L N (famConst d L BG₂ κ) (gamma1 d / 8))
    {Sol : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) →
      Dec2.DecParams (coverOf S.G') × Edat Hm N → (Hm.Ω 1 × Fin N → ℂ) × (Hm.Ω 1 → ℂ)}
    {Sol' : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) →
      Dec2.DecParams (coverOf Gl) × Edat Gd N → (Gd.Ω 1 × Fin N → ℂ) × (Gd.Ω 1 → ℂ)}
    (hSol : ∀ b (p : Dec2.DecParams (coverOf S.G') × Edat Hm N), (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM Hm N false δ₀ δ₁ p.2 →
        (Sol b p).1 = dphi Hm (Dec2.decG (coverOf S.G') Hm (compWeight L S.a₁) S.ν p.1) p.2.2.1
          p.2.1 (pertSource Hm (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) (Sol b p).2 ∧
        Dec2.DecFixed (coverOf S.G') Hm (compWeight L S.a₁) S.ν p.1 false p.2.2.1 p.2.1
          (pertSource Hm (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) (Sol b p).2 ∧
        Small Hm (Sol b p).2 (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
        Small Hm (Sol b p).2 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        SupBounds Hm (Sol b p).1 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        (∀ δα' : Hm.Ω 1 → ℂ, Small Hm δα' (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf S.G') Hm (compWeight L S.a₁) S.ν p.1 false p.2.2.1 p.2.1
            (pertSource Hm (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol b p).2))
    (hSol' : ∀ b (p : Dec2.DecParams (coverOf Gl) × Edat Gd N), (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM Gd N false δ₀' δ₁ p.2 →
        (Sol' b p).1 = dphi Gd (Dec2.decG (coverOf Gl) Gd (compWeight L S.a₁) S.ν p.1) p.2.2.1
          p.2.1 (pertSource Gd (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) (Sol' b p).2 ∧
        Dec2.DecFixed (coverOf Gl) Gd (compWeight L S.a₁) S.ν p.1 false p.2.2.1 p.2.1
          (pertSource Gd (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) (Sol' b p).2 ∧
        Small Gd (Sol' b p).2 (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
        Small Gd (Sol' b p).2 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        SupBounds Gd (Sol' b p).1 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        (∀ δα' : Gd.Ω 1 → ℂ, Small Gd δα' (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf Gl) Gd (compWeight L S.a₁) S.ν p.1 false p.2.2.1 p.2.1
            (pertSource Gd (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol' b p).2))
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
    (hp : 0 < S.p₁)
    (hRu : (17 / 16 : ℝ) * markedRad d L N k S.a₁ κ cψ ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) < δ₁)
    (hN1 : L ^ 1 ∣ N₁) (z : RootIdx d L N₁ m₁ (k + 1))
    (Y' : {Y' // Y' ∈ bridgeFamily 1 (fun _ => Set.univ) (e1DomG S) z})
    (hYmar : ∀ x ∈ Y'.1, ∀ y, supDist x y ≤ 2 * L ^ (k + 1 + m₁) → y ∈ Gl.Ω (k + 1))
    {D : BgData S.G' N} (hD : XiCData S.G' (compWeight L S.a₁) S.ν (k + 1) 1 eps D)
    (θ : physParam N S) (hθ : (θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) = rawOf D)
    (θb : physParamBg N Gl)
    (hθb : (θb.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) = clipRaw Gl (rawOf D))
    (u : ℂ) (Φ : ∀ b, (S.blockSplit 1 hp).Ωb b) :
    e1MarkGParamGBgOn S Gl (BgTransport.canon S.G' Gl N) (maskPre S.hG' Gl (S.blockU z)) F₁' Sol'
        ρ hp z Gl eps' θb Y' u Φ =
      e1MarkGParamG S F₁ Sol ρ hp z eps₀ θ Y' u Φ := by
  classical
  obtain ⟨⟨θr, hθr⟩, θs⟩ := θ
  obtain ⟨⟨θbr, hθbr⟩, θbs⟩ := θb
  simp only at hθ hθb
  subst hθ hθb
  by_cases hu : ‖u‖ < (17 / 16 : ℝ)
  · obtain ⟨-, hD'x, -⟩ := canon_gdat_read (Gl := Gl) S.hG' HB HB' heps hsmall hc7 hεr hD
    have hgate : rawOf D ∈ XiCRaw S.G' (compWeight L S.a₁) S.ν (k + 1) 1 eps₀ :=
      ⟨D, xiCData_mono_radius zero_le_one heps₀ hD, rfl⟩
    have hgateb : clipRaw Gl (rawOf D) ∈ XiCRaw Gl (compWeight L S.a₁) S.ν (k + 1) 1 eps' :=
      ⟨_, hD'x, rfl⟩
    have hum : ‖u‖ * markedRad d L N k S.a₁ κ cψ ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) < δ₁ := by
      rcases le_or_gt 0 (markedRad d L N k S.a₁ κ cψ ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) with
        h | h
      · nlinarith [norm_nonneg u]
      · nlinarith [norm_nonneg u]
    have hdat : (BgTransport.canon S.G' Gl N).dat (clipRaw Gl (rawOf D)) =
        (BgTransport.canon S.G' Gl N).dat (rawOf D) := by
      show clipRaw Gl _ = clipRaw Gl _
      rw [clipRaw_clipRaw]
    rw [e1MarkGParamGBgOn_of_mem S Gl _ _ F₁' Sol' ρ hp z Gl eps' _ Y' u Φ hgateb hu,
      e1MarkGParamG_of_mem S F₁ Sol ρ hp z eps₀ _ Y' u Φ hgate hu]
    refine (markedOutDec_decMarkCorrTermBg_eq S F₁' Sol' ρ hp (S.β : ℂ) _ u Φ z Y'.1).trans
      (Eq.trans ?_ (markedOutDec_decMarkCorrTermBg_eq S F₁ Sol ρ hp (S.β : ℂ) _ u Φ z Y'.1).symm)
    refine Finset.sum_congr rfl fun q hq => congrArg (fun x => -(S.β : ℂ) * x) ?_
    obtain ⟨hqm, hbr⟩ := Finset.mem_filter.1 hq
    have hqY : q.2 ∈ e1DomG S q.1 := (mem_markedIdx (b := q.1) (Y := q.2)).1 hqm |>.1
    obtain ⟨hXY, hzY⟩ := e1Dom_read S hN1 q.1 hqY
    have hYm : ∀ x ∈ q.2, ∀ y, supDist x y ≤ 2 * L ^ (k + 1 + m₁) → y ∈ Gl.Ω (k + 1) :=
      fun x hx => hYmar x (hbr ▸ subset_bridge z q.2 hx)
    refine decMarkCorrBg_eq_of_evDecBg S (fun v t hvt => ?_) hum h1
    exact (evDecBg_congr_dat _ 1 k _ S.a₁ S.ν (BgTransport.canon S.G' Gl N) _ (F₁' q.1)
      (Sol' q.1) _ (maskPre S.hG' Gl (S.blockU z)) v t q.2 hdat _).trans
      (evDecBg_canon_eq_evDec_block S.hG' hG S.hk1 hA hSS hPd hdk hdtop hN hm₁ hM hag hagm hagl
        hagd hS HB HB' ha₁ ha₂ hκ hMc hMX (hF₁ q.1) (hF₁' q.1) hF₂ hM₂ h0 h0' h1 hδ₀ hδ₀' hδ₁
        (hSol q.1) (hSol' q.1) heps hsmall hc7 hphi hεr hsmall' hc7' hphi' hδ₀a hδ₀e hmarD' hαD'
        hsm _ (hρ.le.trans hρc) (S.blockU z) v t hvt (layerUnion_of_isLevel S.hG' 1) hN1 q.2 hXY
        (Nat.le_succ k) q.1 hzY hYm hD _ (fun p => (S.hatOf_mem 1 hρ hp Φ p).trans hρc))
  · rw [e1MarkGParamGBgOn_of_not S Gl _ _ F₁' Sol' ρ hp z Gl eps' _ Y' u Φ fun h => hu h.2,
      e1MarkGParamG_of_not S F₁ Sol ρ hp z eps₀ _ Y' u Φ fun h => hu h.2]

end Marks

end Balaban.Inhabited
