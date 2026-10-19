/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.LocalSetActLocalB
public import Balaban.Fluctuation.LocalClassDensityMarks

/-!
# The block energy recomputed on a local generating set along the masked tangent

P3 pp. 78-79, (4.46) for the marks of the new level: the bridge marks of the step are the `t`-derivatives
of the terms of the block energy along the masked tangent `um ψ' + tm M_Z ψ'`, and the potential part
of the zero-source activities is the term at the marks `(1, 0)`.  The term recomputed on a local
generating set `Gl` is evaluated at the same site-wise multiple `(um + tm 1[unitPt · ∈ Z])` of the
local hat lift.

* `coef_blockEnergyFun_replacement_marked_gen`: the coefficient equality of Lemma AE for the block
  energy `blockEnergyFun … n z` between the ambient pair along the masked tangent and the pair
  `(Gl, Gd)` along the masked local hat lift, for a cube-aligned, sup-separated `Gl`, `Gd ≺ Gl` with
  the layer `k` of `Gl` and no layer `k + 1`, a datum `D` of the chart `Ξ^c(𝔹_{k+1}; 1, ε)`, a datum
  `D'` of `Ξ^c(Gl; 1, ε')` agreeing with `D` on the top layer of `Gl` (`ε ≤ ε'`), a read region `R`
  (the cubes of `𝒞`, the cubes meeting `X₁` and the block `B_{n+1}(z)`) with the margin
  `2 M₁ L^{k+1}` in the top layer of `Gl`, and the radius condition of the marks.
  Proof: `coef_blockEnergyFun_replacement_gen` with `ψ₁ = markedHatPsiF`, `ψ₂` the masked local
  lift; the strict data inequalities by `strictDataM_flEdat_cover` (both lifts lie in the
  fluctuation ball: `markedHatPsiF_mem_flBall_of`, `maskedLocalLift_mem_flBall`), and the agreement
  within `L^{k+1}` of `R` by `localHatLift_eq_hatPsiF` and `markedHatPsiF_apply`.
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Finset
  Balaban.LargeField Balaban.SmallField.GsSpec Balaban.Fluctuation Matrix

section Assembly

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱm : ℝ}
variable {Gp : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
variable {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}
variable {ν : ℝ}

/-- **The block energy recomputed on a local generating set along the masked tangent** (P3
pp. 78-79, (4.46)).  Let `𝔹_{k+1} = Gp`, `Hm` be level sets of levels `k + 1`, `k` (`k ≥ 1`), `Gl`
a cube-aligned, sup-separated generating set and `Gd ≺ Gl` with the layer `k` of `Gl` and no layer
`k + 1`; let the decoupled maps `F₁`, `Sol` of the step (`Sol` at the levels `(δ₀, δ₁)`) and `F₁'`,
`Sol'` of `(Gl, Gd)` (`Sol'` at the levels `(δ₀', δ₁)`) be given by their specifications.  For a
datum `D` of the chart `Ξ^c(𝔹_{k+1}; 1, ε)`, a datum `D'` of `Ξ^c(Gl; 1, ε')` (`ε ≤ ε'`) agreeing
with `D` on the top layer of `Gl`, a hat variable `|ψ̂| ≤ c_ψ`, marks `(um, tm)` of the radius set,
and a read region `R` (the cubes of `𝒞`, the cubes meeting `X₁`, the block `B_{n+1}(z)`) whose
`2 M₁ L^{k+1}`-neighbourhood lies in the top layer of `Gl`, the coefficient `coef (·) 𝒞` of the
block energy of the step along the masked tangent `markedHatPsiF … Zm um tm` equals that of the block
energy recomputed on `(Gl, Gd)` (transported parameters, datum `D'`) along the site-wise multiple
`(um + tm 1[unitPt · ∈ Zm])` of the local hat lift. -/
theorem coef_blockEnergyFun_replacement_marked_gen (hG' : IsLevel Gp (k + 1))
    (hG : IsLevel Hm k) (hk1 : 1 ≤ k) {ϱl ϱl' : ℝ} {Gl : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱl}
    {Gd : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱl'}
    (hA : CubeAligned Gl m₁) (hSS : SupSep Gl m₁) (hPd : Precedes Gd Gl)
    (hdk : Gd.Ω k = Gl.Ω k) (hdtop : Gd.Ω (k + 1) = ∅)
    (hN : 5 < N₁) (hm₁ : 2 ≤ m₁) (hM : 4 * L ^ 2 ≤ L ^ m₁)
    (hag : 2 * d * Real.log L ≤ agmonRate d / 16 * (ϱ - 1))
    (hagm : 2 * d * Real.log L ≤ agmonRate d / 16 * (ϱm - 1))
    (hagl : 2 * d * Real.log L ≤ agmonRate d / 16 * (ϱl - 1))
    (hagd : 2 * d * Real.log L ≤ agmonRate d / 16 * (ϱl' - 1))
    {c BG a₁ : ℝ} (hS : Dec2.DecSpecs d L (Dec2.mixedKc d L) (Cchi d L) c BG)
    (HB : BgHyp d L (k + 1) ϱ (compWeight L a₁) ν) (HB' : BgHyp d L (k + 1) ϱl (compWeight L a₁) ν)
    (ha₁ : 1 / 2 ≤ a₁) (ha₂ : a₁ ≤ 2)
    {κ : ℝ} (hκ : 0 < κ) (hMc : c * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    (hMX : Dec2.cstarX d L (Cchi d L) * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    {F₁ : Dec2.DecParams (coverOf Gp) × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      (Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)}
    {F₁' : Dec2.DecParams (coverOf Gl) × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      (Gl.Ω 1 × Fin N → ℂ) × (Gl.Ω 1 → ℂ)}
    (hF₁ : ∀ (s : Dec2.DecParams (coverOf Gp)) (D : BgData Gp N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC Gp (bgC0 d L N) (c7 d L N BG κ) ν D → ∀ (φ : Gp.Ω 1 × Fin N → ℂ)
        (α : Gp.Ω 1 → ℂ), Dec2.IsDecBg (coverOf Gp) Gp (compWeight L a₁) ν (rho4 d L N BG κ)
          s D φ α → F₁ (s, rawOf D) = (φ, α))
    (hF₁' : ∀ (s : Dec2.DecParams (coverOf Gl)) (D : BgData Gl N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC Gl (bgC0 d L N) (c7 d L N BG κ) ν D → ∀ (φ : Gl.Ω 1 × Fin N → ℂ)
        (α : Gl.Ω 1 → ℂ), Dec2.IsDecBg (coverOf Gl) Gl (compWeight L a₁) ν (rho4 d L N BG κ)
          s D φ α → F₁' (s, rawOf D) = (φ, α))
    {c₂ BG₂ : ℝ} (hF₂ : Dec2.FamSpec d L (Dec2.mixedKc d L) (Cchi d L) c₂ BG₂)
    (hM₂ : c₂ * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δ₀ δ₀' δ₁ : ℝ} (h0 : 0 ≤ δ₀) (h0' : 0 ≤ δ₀')
    (h1 : 0 < δ₁)
    (hδ₀ : δ₀ ≤ deltaStar' d L N (famConst d L BG₂ κ) (gamma1 d / 8))
    (hδ₀' : δ₀' ≤ deltaStar' d L N (famConst d L BG₂ κ) (gamma1 d / 8))
    (hδ₁ : δ₁ ≤ deltaStar' d L N (famConst d L BG₂ κ) (gamma1 d / 8))
    {Sol : Dec2.DecParams (coverOf Gp) × Edat Hm N → (Hm.Ω 1 × Fin N → ℂ) × (Hm.Ω 1 → ℂ)}
    {Sol' : Dec2.DecParams (coverOf Gl) × Edat Gd N → (Gd.Ω 1 × Fin N → ℂ) × (Gd.Ω 1 → ℂ)}
    (hSol : ∀ p : Dec2.DecParams (coverOf Gp) × Edat Hm N, (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM Hm N false δ₀ δ₁ p.2 →
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
    (hSol' : ∀ p : Dec2.DecParams (coverOf Gl) × Edat Gd N, (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM Gd N false δ₀' δ₁ p.2 →
        (Sol' p).1 = dphi Gd (Dec2.decG (coverOf Gl) Gd (compWeight L a₁) ν p.1) p.2.2.1 p.2.1
          (pertSource Gd (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol' p).2 ∧
        Dec2.DecFixed (coverOf Gl) Gd (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
          (pertSource Gd (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol' p).2 ∧
        Small Gd (Sol' p).2 (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
        Small Gd (Sol' p).2 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        SupBounds Gd (Sol' p).1 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        (∀ δα' : Gd.Ω 1 → ℂ, Small Gd δα' (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf Gl) Gd (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
            (pertSource Gd (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol' p).2))
    {X₁ : Set (CTorus d L N₁ m₁ (k + 1))} (C : Finset (ParIdx Gp X₁)) {R' : ℝ} (hR' : 1 < R')
    (hRκ : R' ≤ Real.exp κ)
    {eps eps' : ℝ} (heps : 0 < eps) (hsmall : (4 * d + 6) * ((2 * d + 1) * eps) ≤ 1)
    (hc7 : xiC1 d * eps ≤ c7 d L N BG κ) (hphi : (3 + K4 d L N BG κ) * (xiC1 d * eps) < 1 / 2)
    (hle : eps ≤ eps')
    (hsmall' : (4 * d + 6) * ((2 * d + 1) * eps') ≤ 1) (hc7' : xiC1 d * eps' ≤ c7 d L N BG κ)
    (hphi' : (3 + K4 d L N BG κ) * (xiC1 d * eps') < 1 / 2)
    (hδ₀a : 2 * (K4 d L N BG κ * (xiC1 d * eps)) ≤ δ₀)
    (hδ₀e : 2 * (K4 d L N BG κ * (xiC1 d * eps')) ≤ δ₀')
    {D : BgData Gp N} (hD : XiCData Gp (compWeight L a₁) ν (k + 1) 1 eps D)
    {D' : BgData Gl N} (hD'x : XiCData Gl (compWeight L a₁) ν (k + 1) 1 eps' D')
    (hD' : ∀ x ∈ Gl.Ω (k + 1), D'.Ψ x = D.Ψ x ∧ D'.h x = D.h x)
    {δc : ℝ} (hmarD' : decDomMargin d L N BG κ (xiC1 d * eps') < δc)
    (hαD' : K4 d L N BG κ * (xiC1 d * eps') < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4) (cc : ℂ) {cψ : ℝ} (hcψ : 0 ≤ cψ)
    (Zm : Finset (unitPts Gp)) (um tm : ℂ)
    (hδ₁m : (‖um‖ + ‖tm‖) *
      (Real.sqrt N * (‖cc‖ * (covSupConstC d L N (compWeight L a₁ k) κ * cψ))) < δ₁)
    (ψh : unitPts Gp × Fin N → ℂ) (hψh : ∀ p, ‖ψh p‖ ≤ cψ)
    {R : Finset (CTorus d L N₁ m₁ (k + 1))}
    (hRC : ∀ i ∈ C, ∀ y ∈ Pset m₁ i.1.1, y ∈ R)
    (hRX : ∀ P ∈ cubeIdx Gp, ¬ Disjoint (Pset m₁ P) X₁ → ∀ y ∈ Pset m₁ P, y ∈ R)
    {n : ℕ} (hn : n ≤ k + 1) (z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (n + 1))))
    (hRz : ∀ x ∈ blockSites d L N₁ m₁ (k + 1) n z, x ∈ R)
    (hmar : ∀ x ∈ R, ∀ y, supDist x y ≤ 2 * L ^ (k + 1 + m₁) → y ∈ Gl.Ω (k + 1)) :
    coef (fun w => blockEnergyFun Gp Hm (compWeight L a₁) ν n z
        (F₁ (extParams Gp X₁ w, rawOf D))
        (Sol (extParams Gp X₁ w, flEdat Gp Hm (F₁ (extParams Gp X₁ w, rawOf D)) D.Ψ
          (markedHatPsiF a₁ ν hG' cc F₁ Zm um tm (extParams Gp X₁ w) (rawOf D) ψh))).1
        (rawOf D, markedHatPsiF a₁ ν hG' cc F₁ Zm um tm (extParams Gp X₁ w) (rawOf D) ψh)) C =
      coef (fun w => blockEnergyFun Gl Gd (compWeight L a₁) ν n z
        (F₁' ((fun P => if P.1.2 ∈ Gl.Ω (k + 1)
            then Dec2.extS (coverOf Gp) (extParams Gp X₁ w) P.1 else 0), rawOf D'))
        (Sol' ((fun P => if P.1.2 ∈ Gl.Ω (k + 1)
            then Dec2.extS (coverOf Gp) (extParams Gp X₁ w) P.1 else 0),
          flEdat Gl Gd
            (F₁' ((fun P => if P.1.2 ∈ Gl.Ω (k + 1)
              then Dec2.extS (coverOf Gp) (extParams Gp X₁ w) P.1 else 0), rawOf D'))
            D'.Ψ
            (fun x i => (um + if unitPt hG' x ∈ Zm then tm else 0) *
              (if h : unitBlock x ∈ unitPts Gl then
                (cc • (decCovSqrt Gl (compWeight L a₁) a₁ ν
                  (F₁' ((fun P => if P.1.2 ∈ Gl.Ω (k + 1)
                    then Dec2.extS (coverOf Gp) (extParams Gp X₁ w) P.1 else 0), rawOf D')).2
                  (Dec2.extS (coverOf Gl) (fun P => if P.1.2 ∈ Gl.Ω (k + 1)
                    then Dec2.extS (coverOf Gp) (extParams Gp X₁ w) P.1 else 0))
                  (barField Gl D'.Ψ (F₁' ((fun P => if P.1.2 ∈ Gl.Ω (k + 1)
                    then Dec2.extS (coverOf Gp) (extParams Gp X₁ w) P.1 else 0), rawOf D')).1)
                  (unitQ Gl) (unitP Gl) *ᵥ
                  (fun p => if hp : p.1.1 ∈ unitPts Gp then ψh (⟨p.1.1, hp⟩, p.2) else 0)))
                  (⟨unitBlock x, h⟩, i)
              else 0)))).1
        (rawOf D', fun x i => (um + if unitPt hG' x ∈ Zm then tm else 0) *
          (if h : unitBlock x ∈ unitPts Gl then
            (cc • (decCovSqrt Gl (compWeight L a₁) a₁ ν
              (F₁' ((fun P => if P.1.2 ∈ Gl.Ω (k + 1)
                then Dec2.extS (coverOf Gp) (extParams Gp X₁ w) P.1 else 0), rawOf D')).2
              (Dec2.extS (coverOf Gl) (fun P => if P.1.2 ∈ Gl.Ω (k + 1)
                then Dec2.extS (coverOf Gp) (extParams Gp X₁ w) P.1 else 0))
              (barField Gl D'.Ψ (F₁' ((fun P => if P.1.2 ∈ Gl.Ω (k + 1)
                then Dec2.extS (coverOf Gp) (extParams Gp X₁ w) P.1 else 0), rawOf D')).1)
              (unitQ Gl) (unitP Gl) *ᵥ
              (fun p => if hp : p.1.1 ∈ unitPts Gp then ψh (⟨p.1.1, hp⟩, p.2) else 0)))
              (⟨unitBlock x, h⟩, i)
          else 0))) C := by
  classical
  obtain ⟨Sb, Sb', -, -⟩ := replacement_coverBases hG' Hm hA hSS hPd hN hm₁ hM HB hag hagm hagl hagd
  have hd0 : 0 < d := by have := HB.hd; omega
  have hxi := one_le_xiC1 d
  have heps' : 0 < eps' := lt_of_lt_of_le heps hle
  have hK4 : 0 ≤ K4 d L N BG κ := (K4_pos hS.fam.2.1 hd0).le
  have hxle : xiC1 d * eps ≤ xiC1 d * eps' := mul_le_mul_of_nonneg_left hle (by linarith)
  have hαD : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2 :=
    lt_of_le_of_lt (mul_le_mul_of_nonneg_left hxle hK4) hαD'
  have hmarD : decDomMargin d L N BG κ (xiC1 d * eps) < δc := by
    refine lt_of_le_of_lt ?_ hmarD'
    unfold decDomMargin
    gcongr
  have hδ0 : 0 < xiC1 d * eps := by positivity
  have hδ0' : 0 < xiC1 d * eps' := by positivity
  have hDd : InUnionDomainC Gp (bgC0 d L N) (c7 d L N BG κ) ν D := by
    have hc1 : xiC1 d * eps ≤ bgC1 d L N := hc7.trans (c7_le_bgC1 d L N BG κ)
    exact inUnionDomainC_of_inDomainC HB hδ0 (hc1.trans (bgC1_le_bgC0 d L N hd0)) hc7
      (xiCData_inDomainC HB hsmall hD)
  have hDd' : InUnionDomainC Gl (bgC0 d L N) (c7 d L N BG κ) ν D' := by
    have hc1 : xiC1 d * eps' ≤ bgC1 d L N := hc7'.trans (c7_le_bgC1 d L N BG κ)
    exact inUnionDomainC_of_inDomainC HB' hδ0' (hc1.trans (bgC1_le_bgC0 d L N hd0)) hc7'
      (xiCData_inDomainC HB' hsmall' hD'x)
  have hsσ : ∀ w ∈ supN C R', ∀ P, ‖extParams _ X₁ w P‖ < Real.exp κ := fun w hw P =>
    (norm_extParams_lt hR' hw.2 P).trans_le hRκ
  have hE1 : 1 < Real.exp κ := Real.one_lt_exp_iff.2 hκ
  have hHm : Hm.Ω (k + 1) = ∅ :=
    Finset.eq_empty_of_forall_notMem fun x => isLevel_not_mem_Ω hG le_rfl (by omega) x
  have hψh' : ∀ p : unitPts Gl × Fin N,
      ‖(fun p : unitPts Gl × Fin N =>
        if hp : p.1.1 ∈ unitPts Gp then ψh (⟨p.1.1, hp⟩, p.2) else 0) p‖ ≤ cψ := by
    intro p
    dsimp only
    split_ifs
    · exact hψh _
    · simpa using hcψ
  have hcm : 0 ≤ ‖um‖ + ‖tm‖ := by positivity
  have hδ₁cm : Real.sqrt N * (‖((‖um‖ + ‖tm‖ : ℝ) : ℂ) * cc‖ *
      (covSupConstC d L N (compWeight L a₁ k) κ * cψ)) < δ₁ := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hcm]
    calc Real.sqrt N * ((‖um‖ + ‖tm‖) * ‖cc‖ * (covSupConstC d L N (compWeight L a₁ k) κ * cψ))
        = (‖um‖ + ‖tm‖) *
          (Real.sqrt N * (‖cc‖ * (covSupConstC d L N (compWeight L a₁ k) κ * cψ))) := by ring
      _ < δ₁ := hδ₁m
  -- the masked local lift lies in the fluctuation ball of `Hm`, hence of `Gd`
  have hψl := fun w (hw : w ∈ supN C R') =>
    maskedLocalLift_mem_flBall _ _ cc um tm (fun x => unitPt hG' x ∈ Zm)
      (localHatLift_mem_flBallLC_of_spec hHm hk1 ha₁ ha₂ hS Sb' HB' hκ.le hMc hMX
        (Cchi_nonneg d L) hF₁' heps' hsmall' hc7' hphi' hmarD' hαD' hsm
        (tau_norm_lt (Gl := Gl) (hsσ w hw) hE1) hD'x _ hcψ h1 hδ₁cm hψh').1
  refine coef_blockEnergyFun_replacement_gen hG' hG hk1 hA hSS hPd hdk hdtop hN hm₁ hM hag hagm
    hagl hagd hS HB HB' hκ.le hMc hF₁ hF₁' hF₂ hM₂ h0 h0' h1.le hδ₀ hδ₀' hδ₁ hSol hSol' C hR' hRκ
    hDd hDd' hD' _ _ (fun w hw => ?_) (fun w hw => ?_) hRC hRX hn z hRz hmar
    (fun w hw x hx y hy => ?_) (rawOf D) (rawOf D')
  · -- the strict data inequalities of the ambient fluctuation problem
    have hamb : hatPsiF Gp a₁ ν hG' (((‖um‖ + ‖tm‖ : ℝ) : ℂ) * cc) F₁ (extParams _ X₁ w)
        (rawOf D) ψh ∈ FlBall Hm δ₁ := by
      rw [hatPsiF_eq_dite (a₁ := a₁) (ν := ν) hG' (((‖um‖ + ‖tm‖ : ℝ) : ℂ) * cc) F₁
        (extParams _ X₁ w) (rawOf D) ψh]
      exact (localHatLift_mem_flBallLC_of_spec hHm hk1 ha₁ ha₂ hS Sb HB hκ.le hMc hMX
        (Cchi_nonneg d L) hF₁ heps hsmall hc7 hphi hmarD hαD hsm (hsσ w hw) hD _ hcψ h1 hδ₁cm
        hψh).1
    exact strictDataM_flEdat_cover hS Sb HB hκ hMc heps hsmall hc7 hphi h1 hδ₀a
      (isLevel_top_precedes hG' Hm) hF₁ hSol (hsσ w hw) hD
      (markedHatPsiF_mem_flBall_of hG' cc F₁ Zm um tm _ _ ψh hamb)
  · -- the strict data inequalities of the local fluctuation problem
    exact strictDataM_flEdat_cover hS Sb' HB' hκ hMc heps' hsmall' hc7' hphi' h1 hδ₀e hPd hF₁'
      hSol' (tau_norm_lt (Gl := Gl) (hsσ w hw) hE1) hD'x
      (fun x _ => hψl w hw x ((mem_dataSites Hm).2 (Or.inl (hG x).1)))
  · -- the two masked lifts agree within `L^{k+1}` of the read region
    exact funext fun i => (markedHatPsiF_apply hG' cc F₁ Zm um tm _ _ ψh y i).trans
      (congrArg _ (localHatLift_eq_hatPsiF hSS hA hG' hk1 hN hm₁ hM hag hagl hS HB HB' ha₁ ha₂
        hκ hMc hMX hF₁ hF₁' heps hsmall hc7 hphi heps' hsmall' hc7' hphi' hmarD hαD hmarD' hαD'
        hsm hD hD'x hD' hRC hRX hmar hw.1 (hsσ w hw) cc ψh ⟨x, hx, hy⟩ i).symm)

end Assembly

end Balaban.Localization
