/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.LocalSetActMarked
public import Balaban.Fluctuation.NewLevelOldTermsBg
public import Balaban.Fluctuation.DecMarkCorrCount

/-!
# The marked terms of the block energy recomputed on a local generating set (`NewLevelBlockTermsBg`)

P3 pp. 78-79, (4.44)-(4.47): the bridge marks of the new level are the `t`-derivatives of the
terms of the localized block energy along the masked tangent, and the potential part of the
zero-source activities is the term of the block energy at the marks `(1, 0)`.  Recomputed on a
local generating set `Gl` with the canonical transport, these terms equal the step's at the datum
read from a datum of the step chart.

* `evDecBg_canon_eq_evDec_block`: **the replacement identity for the marked term of a label `Y` of
  the block energy** `blockEnergyFun … n z` (the instance `Φ = blockEnergyFun` of
  `evDecBg_canon_eq_evDec_of_coef`, by `coef_blockEnergyFun_replacement_marked_gen`): the cubes
  meeting `X₁` and the block `B_{n+1}(z)` lie in `Y`, whose `2 M₁ L^{k+1}`-neighbourhood lies in the
  top layer of `Gl`;
* `decMarkGBg_eq_of_evDecBg`, `decMarkCorrBg_eq_of_evDecBg`: the block-level marks (`∂_t|₀`) and
  their corrections (the Taylor remainder in the first mark) computed on two generating sets agree
  when the terms agree on the radius set of the marks.
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Finset
  Balaban.LargeField Balaban.SmallField.GsSpec Balaban.Fluctuation Matrix

section Term

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱm ϱl ϱl' : ℝ}
variable {Gp : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
  {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}
  {Gl : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱl}
  {Gd : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱl'} {ν : ℝ}

/-- **The marked term of a label of the block energy recomputed on a local generating set** (P3
pp. 78-79, (4.46)).  The statement of `evDecBg_canon_eq_evDec` for the block energy
`blockEnergyFun … n z` of the block `B_{n+1}(z)` in place of the old term: for a label `Y` whose
`2 M₁ L^{k+1}`-neighbourhood lies in the top layer of `Gl`, with the cubes meeting `X₁` and the block
`B_{n+1}(z)` inside `Y`, at a datum `D` of the step chart of radius `ε`, a hat variable of the box and
marks `(um, tm)` of the radius set, the term recomputed on `(Gl, Gd)` with the canonical transport
(at the read datum, of radius `ε′ ≥ (2 K₁ + 2) C₁ ε`, and the restricted hat variable) equals the
step's term. -/
theorem evDecBg_canon_eq_evDec_block (hG' : IsLevel Gp (k + 1)) (hG : IsLevel Hm k) (hk1 : 1 ≤ k)
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
    {eps eps' : ℝ} (heps : 0 < eps) (hsmall : (4 * d + 6) * ((2 * d + 1) * eps) ≤ 1)
    (hc7 : xiC1 d * eps ≤ c7 d L N BG κ) (hphi : (3 + K4 d L N BG κ) * (xiC1 d * eps) < 1 / 2)
    (hεr : (2 * bgK1 d L N + 2) * xiC1 d * eps ≤ eps')
    (hsmall' : (4 * d + 6) * ((2 * d + 1) * eps') ≤ 1) (hc7' : xiC1 d * eps' ≤ c7 d L N BG κ)
    (hphi' : (3 + K4 d L N BG κ) * (xiC1 d * eps') < 1 / 2)
    (hδ₀a : 2 * (K4 d L N BG κ * (xiC1 d * eps)) ≤ δ₀)
    (hδ₀e : 2 * (K4 d L N BG κ * (xiC1 d * eps')) ≤ δ₀')
    {δc : ℝ} (hmarD' : decDomMargin d L N BG κ (xiC1 d * eps') < δc)
    (hαD' : K4 d L N BG κ * (xiC1 d * eps') < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4) (cc : ℂ) {cψ : ℝ} (hcψ : 0 ≤ cψ)
    (Zm : Finset (unitPts Gp)) (um tm : ℂ)
    (hδ₁m : (‖um‖ + ‖tm‖) * markedRad d L N k a₁ κ cψ cc < δ₁)
    {X₁f : Finset (CTorus d L N₁ m₁ (k + 1))} {m₀ j : ℕ} {𝒦X : Set (CTorus d L N₁ m₁ (k + 1))}
    (hU : LayerUnion Gp m₀) (hNm : L ^ m₀ ∣ N₁) (Y : Set (CTorus d L N₁ m₁ (k + 1)))
    (hXY : ∀ P ∈ cubeIdx Gp, ¬ Disjoint (Pset m₁ P) (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) →
      ∀ y ∈ Pset m₁ P, y ∈ Y)
    {n : ℕ} (hn : n ≤ k + 1) (z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (n + 1))))
    (hzY : ∀ x ∈ blockSites d L N₁ m₁ (k + 1) n z, x ∈ Y)
    (hYmar : ∀ x ∈ Y, ∀ y, supDist x y ≤ 2 * L ^ (k + 1 + m₁) → y ∈ Gl.Ω (k + 1))
    {D : BgData Gp N} (hD : XiCData Gp (compWeight L a₁) ν (k + 1) 1 eps D)
    (ψh : unitPts Gp × Fin N → ℂ) (hψh : ∀ p, ‖ψh p‖ ≤ cψ) :
    evDecBg Gp X₁f m₀ j 𝒦X Gl a₁ ν (BgTransport.canon Gp Gl N) cc F₁' Sol'
        (blockEnergyFun Gl Gd (compWeight L a₁) ν n z) (maskPre hG' Gl Zm) um tm Y
        (rawOf D, (BgTransport.canon Gp Gl N).res ψh) =
      evDec X₁f m₀ j 𝒦X a₁ ν hG' cc F₁ Sol (blockEnergyFun Gp Hm (compWeight L a₁) ν n z) Zm um tm
        Y (rawOf D, ψh) := by
  classical
  obtain ⟨hle, hD'x, hD'⟩ := canon_gdat_read (Gl := Gl) hG' HB HB' heps hsmall hc7 hεr hD
  have hE1 : 1 < Real.exp κ := Real.one_lt_exp_iff.2 hκ
  refine evDecBg_canon_eq_evDec_of_coef hG' a₁ cc F₁ F₁' Sol Sol' _ _ Zm um tm X₁f m₀ j 𝒦X Y D
    ((BgTransport.canon Gp Gl N).gdat (BgTransport.reads_canon hG') D) rfl ψh fun C hC => ?_
  exact coef_blockEnergyFun_replacement_marked_gen hG' hG hk1 hA hSS hPd hdk hdtop hN hm₁ hM hag
    hagm hagl hagd hS HB HB' ha₁ ha₂ hκ hMc hMX hF₁ hF₁' hF₂ hM₂ h0 h0' h1 hδ₀ hδ₀' hδ₁ hSol hSol' C
    hE1 le_rfl heps hsmall hc7 hphi hle hsmall' hc7' hphi' hδ₀a hδ₀e hD hD'x hD' hmarD' hαD' hsm cc
    hcψ Zm um tm hδ₁m ψh hψh (mem_filter_of_mem_connFams hU hNm hC)
    (fun P hP hdis y hy => Finset.mem_filter.2 ⟨Finset.mem_univ _, hXY P hP hdis y hy⟩) hn z
    (fun x hx => Finset.mem_filter.2 ⟨Finset.mem_univ _, hzY x hx⟩)
    (fun x hx => hYmar x (Finset.mem_filter.1 hx).2)

end Term

end Balaban.Localization

namespace Balaban.Fluctuation

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Localization

section Transfer

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ ϱb ϱb' ϱm ϱm' : ℝ}
  (S : StepSetting d L N₁ m₁ k N ϱ)
  {Gb : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱb}
  {Gb' : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱb'}
  {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}
  {Hm' : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm'}
  {T : BgTransport S.G' Gb N} {T' : BgTransport S.G' Gb' N}
  {X₁f : Finset (CTorus d L N₁ m₁ (k + 1))} {m₀ j : ℕ} {𝒦X : Set (CTorus d L N₁ m₁ (k + 1))}
  {a₁ ν : ℝ} {cc : ℂ}
  {F₁ : DecParams Gb × RawData d L (N₁ * L ^ m₁) (k + 1) N → (Gb.Ω 1 × Fin N → ℂ) × (Gb.Ω 1 → ℂ)}
  {F₁' : DecParams Gb' × RawData d L (N₁ * L ^ m₁) (k + 1) N →
    (Gb'.Ω 1 × Fin N → ℂ) × (Gb'.Ω 1 → ℂ)}
  {Sol : Dec2.DecParams (coverOf Gb) × Edat Hm N → (Hm.Ω 1 × Fin N → ℂ) × (Hm.Ω 1 → ℂ)}
  {Sol' : Dec2.DecParams (coverOf Gb') × Edat Hm' N → (Hm'.Ω 1 × Fin N → ℂ) × (Hm'.Ω 1 → ℂ)}
  {En : ((Gb.Ω 1 × Fin N → ℂ) × (Gb.Ω 1 → ℂ)) → (Hm.Ω 1 × Fin N → ℂ) →
    RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) → ℂ}
  {En' : ((Gb'.Ω 1 × Fin N → ℂ) × (Gb'.Ω 1 → ℂ)) → (Hm'.Ω 1 × Fin N → ℂ) →
    RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) → ℂ}
  {Zm : Finset (unitPts Gb)} {Zm' : Finset (unitPts Gb')} {Y : Set (CTorus d L N₁ m₁ (k + 1))}
  {ρ : ℝ} {hp : 0 < S.p₁} {Θ Θ' : RawData d L (N₁ * L ^ m₁) (k + 1) N}

/-- **The block-level marks on two generating sets at two configurations agree when their terms
do** on the radius set: if the terms `evDecBg` of `(Gb, T)` at `(Θ, T.res ψ̂(Φ))` and of `(Gb', T')`
at `(Θ', T'.res ψ̂(Φ'))` agree at the first mark `um` and every second mark `t` with
`(‖um‖ + ‖t‖) m_R < δ₁`, and `‖um‖ m_R < δ₁`, then the marks `∂_t|₀` agree. -/
theorem decMarkGBg_eq_of_evDecBg_conf {mR δ₁ : ℝ} {um : ℂ}
    {Φ Φ' : ∀ b, (S.blockSplit m₀ hp).Ωb b}
    (h : ∀ t : ℂ, (‖um‖ + ‖t‖) * mR < δ₁ →
      evDecBg S.G' X₁f m₀ j 𝒦X Gb a₁ ν T cc F₁ Sol En Zm um t Y
          (Θ, T.res (S.hatOf m₀ ρ hp Φ)) =
        evDecBg S.G' X₁f m₀ j 𝒦X Gb' a₁ ν T' cc F₁' Sol' En' Zm' um t Y
          (Θ', T'.res (S.hatOf m₀ ρ hp Φ')))
    (hum : ‖um‖ * mR < δ₁) :
    decMarkGBg S Gb T X₁f m₀ j 𝒦X a₁ ν cc F₁ Sol En Zm Y ρ hp Θ um Φ =
      decMarkGBg S Gb' T' X₁f m₀ j 𝒦X a₁ ν cc F₁' Sol' En' Zm' Y ρ hp Θ' um Φ' := by
  unfold decMarkGBg
  refine Filter.EventuallyEq.deriv_eq ?_
  have hopen : IsOpen {t : ℂ | (‖um‖ + ‖t‖) * mR < δ₁} :=
    isOpen_lt (by fun_prop) continuous_const
  have h0 : (0 : ℂ) ∈ {t : ℂ | (‖um‖ + ‖t‖) * mR < δ₁} := by
    show (‖um‖ + ‖(0 : ℂ)‖) * mR < δ₁
    rw [norm_zero, add_zero]
    exact hum
  filter_upwards [hopen.mem_nhds h0] with t ht
  exact h t ht

/-- **The block-level marks on two generating sets agree when their terms do** on the radius set:
if the terms `evDecBg` of `(Gb, T)` at `(Θ, T.res ψ̂(Φ))` and of `(Gb', T')` at `(Θ', T'.res ψ̂(Φ))`
agree at the first mark `um` and every second mark `t` with `(‖um‖ + ‖t‖) m_R < δ₁`, and
`‖um‖ m_R < δ₁`, then the marks `∂_t|₀` agree. -/
theorem decMarkGBg_eq_of_evDecBg {mR δ₁ : ℝ} {um : ℂ} {Φ : ∀ b, (S.blockSplit m₀ hp).Ωb b}
    (h : ∀ t : ℂ, (‖um‖ + ‖t‖) * mR < δ₁ →
      evDecBg S.G' X₁f m₀ j 𝒦X Gb a₁ ν T cc F₁ Sol En Zm um t Y
          (Θ, T.res (S.hatOf m₀ ρ hp Φ)) =
        evDecBg S.G' X₁f m₀ j 𝒦X Gb' a₁ ν T' cc F₁' Sol' En' Zm' um t Y
          (Θ', T'.res (S.hatOf m₀ ρ hp Φ)))
    (hum : ‖um‖ * mR < δ₁) :
    decMarkGBg S Gb T X₁f m₀ j 𝒦X a₁ ν cc F₁ Sol En Zm Y ρ hp Θ um Φ =
      decMarkGBg S Gb' T' X₁f m₀ j 𝒦X a₁ ν cc F₁' Sol' En' Zm' Y ρ hp Θ' um Φ :=
  decMarkGBg_eq_of_evDecBg_conf S h hum

/-- **The corrected marks on two generating sets at two configurations agree when their terms
do** on the radius set: if the terms at `(Θ, T.res ψ̂(Φ))` and `(Θ', T'.res ψ̂(Φ'))` agree at every
pair of marks `(v, t)` with `(‖v‖ + ‖t‖) m_R < δ₁`, `‖um‖ m_R < δ₁` and `δ₁ > 0`, the Taylor
remainders `f(um) − f(0) − um f′(0)` of the marks agree. -/
theorem decMarkCorrBg_eq_of_evDecBg_conf {mR δ₁ : ℝ} {um : ℂ}
    {Φ Φ' : ∀ b, (S.blockSplit m₀ hp).Ωb b}
    (h : ∀ v t : ℂ, (‖v‖ + ‖t‖) * mR < δ₁ →
      evDecBg S.G' X₁f m₀ j 𝒦X Gb a₁ ν T cc F₁ Sol En Zm v t Y
          (Θ, T.res (S.hatOf m₀ ρ hp Φ)) =
        evDecBg S.G' X₁f m₀ j 𝒦X Gb' a₁ ν T' cc F₁' Sol' En' Zm' v t Y
          (Θ', T'.res (S.hatOf m₀ ρ hp Φ')))
    (hum : ‖um‖ * mR < δ₁) (hδ : 0 < δ₁) :
    decMarkCorrBg S Gb T X₁f m₀ j 𝒦X a₁ ν cc F₁ Sol En Zm Y ρ hp Θ um Φ =
      decMarkCorrBg S Gb' T' X₁f m₀ j 𝒦X a₁ ν cc F₁' Sol' En' Zm' Y ρ hp Θ' um Φ' := by
  have h0 : ‖(0 : ℂ)‖ * mR < δ₁ := by rw [norm_zero, zero_mul]; exact hδ
  have hopen : IsOpen {v : ℂ | ‖v‖ * mR < δ₁} := isOpen_lt (by fun_prop) continuous_const
  have e3 : deriv (fun v : ℂ => decMarkGBg S Gb T X₁f m₀ j 𝒦X a₁ ν cc F₁ Sol En Zm Y ρ hp Θ v Φ) 0 =
      deriv (fun v : ℂ => decMarkGBg S Gb' T' X₁f m₀ j 𝒦X a₁ ν cc F₁' Sol' En' Zm' Y ρ hp Θ' v Φ')
        0 := by
    refine Filter.EventuallyEq.deriv_eq ?_
    filter_upwards [hopen.mem_nhds h0] with v hv
    exact decMarkGBg_eq_of_evDecBg_conf S (h v) hv
  unfold decMarkCorrBg
  rw [decMarkGBg_eq_of_evDecBg_conf S (h um) hum, decMarkGBg_eq_of_evDecBg_conf S (h 0) h0, e3]

/-- **The corrected marks on two generating sets agree when their terms do** on the radius set:
if the terms agree at every pair of marks `(v, t)` with `(‖v‖ + ‖t‖) m_R < δ₁`, `‖um‖ m_R < δ₁` and
`δ₁ > 0`, the Taylor remainders `f(um) − f(0) − um f′(0)` of the marks agree. -/
theorem decMarkCorrBg_eq_of_evDecBg {mR δ₁ : ℝ} {um : ℂ} {Φ : ∀ b, (S.blockSplit m₀ hp).Ωb b}
    (h : ∀ v t : ℂ, (‖v‖ + ‖t‖) * mR < δ₁ →
      evDecBg S.G' X₁f m₀ j 𝒦X Gb a₁ ν T cc F₁ Sol En Zm v t Y
          (Θ, T.res (S.hatOf m₀ ρ hp Φ)) =
        evDecBg S.G' X₁f m₀ j 𝒦X Gb' a₁ ν T' cc F₁' Sol' En' Zm' v t Y
          (Θ', T'.res (S.hatOf m₀ ρ hp Φ)))
    (hum : ‖um‖ * mR < δ₁) (hδ : 0 < δ₁) :
    decMarkCorrBg S Gb T X₁f m₀ j 𝒦X a₁ ν cc F₁ Sol En Zm Y ρ hp Θ um Φ =
      decMarkCorrBg S Gb' T' X₁f m₀ j 𝒦X a₁ ν cc F₁' Sol' En' Zm' Y ρ hp Θ' um Φ :=
  decMarkCorrBg_eq_of_evDecBg_conf S h hum hδ

end Transfer

end Balaban.Fluctuation
