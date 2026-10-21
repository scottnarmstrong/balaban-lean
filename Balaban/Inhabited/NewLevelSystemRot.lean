/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.NewLevelSystemLoc
public import Balaban.Inhabited.NewLevelObjectsBgRot
public import Balaban.Fluctuation.NewLevelDetBgLocal
public import Balaban.Inhabited.NewLevelBridgeMarksBgFields
public import Balaban.Fluctuation.NewLevelOldTermsBgFields

/-!
# Spin covariance of the coefficient recomputed from the labels inside the polymer

Route R-LOC, L5, the clause (A4) of `newLabels_castInputs_of_localFamily` (P3 pp. 78-79): the
coefficient of the system recomputed on a local generating set `Gl` from the labels inside the
polymer `T` (`NewLevelSystem.coeffLoc`) is invariant under the real rotations of the parameter on the
chart of `Gl` of the analyticity radius `ε ≤ ε′`.

The determinant part is invariant by `newLevelDetBg_rot_param`; the zero-source activities by
`zeroActBg_canon_rot`; the bridge marks by `e1MarkGParamGBgOn_congr_of_terms` with the covariance of
the block-energy terms (`blockEvBg_canon_rot_of_margin`); the old activities and marks by
`oldActBg_congr_of_terms`, `oldMarkGBg_congr_of_terms` from the covariance of the terms of the old
terms (`holdrot`).  The block variables are rotated sitewise (`exists_blockSplit_equiv`), the
reference configuration is `0` and the carrier is the product of the balls of radius `p₁`.

* `blockEvBg_canon_rot_of_margin`: the covariance of the block-energy terms of a label with the
  margin in `Gl` (the terms vanish unless the region of the block lies in the label);
* `NewLevelSystem.coeffLoc_rot_of`.
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Fluctuation Balaban.Multiscale Balaban.Background Balaban.Localization
  Balaban.SmallField Balaban.LargeField Balaban.Polymer Finset MeasureTheory Matrix
  Balaban.Inhabited.MarkBudgetAudit

section Block

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ ϱb ϱm : ℝ}
  (S : StepSetting d L N₁ m₁ k N ϱ) {Gb : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱb}
  {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm} {Kc Cx : ℝ}

open Classical in
/-- **Spin covariance of the block-energy terms of a label with the margin in `Gb`**: for a label
`Y` with `LabelMargin Gb Y`, the term `evDecBg … (blockEnergyFun … z) … Y` at the rotated datum and
the rotated hat variable equals its value at the datum and the hat variable (when the region of the
block lies in `Y` it lies in the top layer of `Gb`, `blockEvBg_canon_rot`; otherwise both terms
vanish, `evDecBg_eq_zero_of_not_subset`). -/
theorem blockEvBg_canon_rot_of_margin {c BG : ℝ} (hS : Dec2.DecSpecs d L Kc Cx c BG)
    (Sb : Dec2.CoverBase (coverOf Gb) Gb (compWeight L S.a₁) S.ν Kc Cx)
    {κ eps c₂ BG₂ δ₁ Kf Cf : ℝ} (hC : FlCore N Gb Hm S.a₁ S.ν c BG κ eps Kf Cf c₂ BG₂ δ₁)
    (hHm : Hm.Ω (k + 1) = ∅) (cc : ℂ) {cψ : ℝ} (hcψ : 0 ≤ cψ)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δc : ℝ}
    (hmar : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    {F₁ : DecParams Gb × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      (Gb.Ω 1 × Fin N → ℂ) × (Gb.Ω 1 → ℂ)}
    (hF₁ : ∀ (s : DecParams Gb) (D : BgData Gb N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC Gb (bgC0 d L N) (c7 d L N BG κ) S.ν D → ∀ (φ : Gb.Ω 1 × Fin N → ℂ)
        (α : Gb.Ω 1 → ℂ), IsDecBg Gb (compWeight L S.a₁) S.ν (rho4 d L N BG κ) s D φ α →
        F₁ (s, rawOf D) = (φ, α))
    {Sol : Dec2.DecParams (coverOf Gb) × Edat Hm N → (Hm.Ω 1 × Fin N → ℂ) × (Hm.Ω 1 → ℂ)}
    (hSol : ∀ p : Dec2.DecParams (coverOf Gb) × Edat Hm N, (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM Hm N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2 →
        (Sol p).1 = dphi Hm (Dec2.decG (coverOf Gb) Hm (compWeight L S.a₁) S.ν p.1) p.2.2.1
          p.2.1 (pertSource Hm (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) (Sol p).2 ∧
        Dec2.DecFixed (coverOf Gb) Hm (compWeight L S.a₁) S.ν p.1 false p.2.2.1 p.2.1
          (pertSource Hm (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) (Sol p).2 ∧
        Small Hm (Sol p).2 (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
        Small Hm (Sol p).2 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        SupBounds Hm (Sol p).1 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        (∀ δα' : Hm.Ω 1 → ℂ, Small Hm δα' (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf Gb) Hm (compWeight L S.a₁) S.ν p.1 false p.2.2.1 p.2.1
            (pertSource Hm (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol p).2))
    {X₁f : Finset (CTorus d L N₁ m₁ (k + 1))} {m₀ j : ℕ} {𝒦X : Set (CTorus d L N₁ m₁ (k + 1))}
    (hX₁ : (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) = X1 S.G' m₀ j 𝒦X)
    (z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1)))) {Q : Matrix (Fin N) (Fin N) ℝ}
    (hQ : Qᵀ * Q = 1) (Zb : Finset (unitPts Gb)) {um tm : ℂ}
    (hW : (‖um‖ + ‖tm‖) * markedRad d L N k S.a₁ κ cψ cc < δ₁)
    {Y : Set (CTorus d L N₁ m₁ (k + 1))} (hYm : LabelMargin Gb Y) {D : BgData Gb N}
    (hD : XiCData Gb (compWeight L S.a₁) S.ν (k + 1) 1 eps D) {ψh : unitPts S.G' × Fin N → ℂ}
    (hψh : ∀ p, ‖ψh p‖ ≤ cψ) :
    evDecBg S.G' X₁f m₀ j 𝒦X Gb S.a₁ S.ν (BgTransport.canon S.G' Gb N) cc F₁ Sol
        (blockEnergyFun Gb Hm (compWeight L S.a₁) S.ν k z) Zb um tm Y
        (rotRaw (cmat Q) (rawOf D), (BgTransport.canon S.G' Gb N).res (rotFld (cmat Q) ψh)) =
      evDecBg S.G' X₁f m₀ j 𝒦X Gb S.a₁ S.ν (BgTransport.canon S.G' Gb N) cc F₁ Sol
        (blockEnergyFun Gb Hm (compWeight L S.a₁) S.ν k z) Zb um tm Y
        (rawOf D, (BgTransport.canon S.G' Gb N).res ψh) := by
  by_cases hsub : ∀ x ∈ X₁f, x ∈ Y
  · exact blockEvBg_canon_rot S hS Sb hC hHm cc hcψ hMX hmar hα hsm hF₁ hSol
      (fun x hx => hYm.subset x (hsub x hx)) z hQ Zb hW Y hD hψh
  · rw [evDecBg_eq_zero_of_not_subset _ hX₁ hsub, evDecBg_eq_zero_of_not_subset _ hX₁ hsub]

end Block

namespace NewLevelSystem

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ ϱl ϱl' : ℝ}
  {S : StepSetting d L N₁ m₁ k N ϱ} {C : StepClass d L N₁ m₁ k N ϱ}
  {z : RootIdx d L N₁ m₁ (k + 1)} {t pp : ℝ} {Jr : S.JointRep t pp}
  (NS : NewLevelSystem S C z Jr) {Gl : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱl}
  {Gd : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱl'}
  (F₂' : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) →
    Dec2.DecParams (coverOf Gl) × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      (Gl.Ω 1 × Fin N → ℂ) × (Gl.Ω 1 → ℂ))
  (Sol₂' : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) →
    Dec2.DecParams (coverOf Gl) × Edat Gd N → (Gd.Ω 1 × Fin N → ℂ) × (Gd.Ω 1 → ℂ))
  (F₁L' : NS.O.ι → Dec2.DecParams (coverOf Gl) × RawData d L (N₁ * L ^ m₁) (k + 1) N →
    (Gl.Ω 1 × Fin N → ℂ) × (Gl.Ω 1 → ℂ))
  (SolL' : NS.O.ι → Dec2.DecParams (coverOf Gl) × Edat Gd N →
    (Gd.Ω 1 × Fin N → ℂ) × (Gd.Ω 1 → ℂ))
  (F₁b' : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) →
    Dec2.DecParams (coverOf Gl) × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      (Gl.Ω 1 × Fin N → ℂ) × (Gl.Ω 1 → ℂ))
  (Solb' : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) →
    Dec2.DecParams (coverOf Gl) × Edat Gd N → (Gd.Ω 1 × Fin N → ℂ) × (Gd.Ω 1 → ℂ))

open Classical in
/-- **Spin covariance of the coefficient recomputed from the labels inside `T`** (P3 pp. 78-79;
the form of (A4)).  Let `(Gl, Gd)` have a cover base and the fluctuation core at the analyticity
radius `ε ≤ ε′` with the constants of the system, `Gd` without layer `k + 1`, the zero-source and
bridge pairs of `(Gl, Gd)` given by their specifications, the terms of the old terms covariant at
`Gl` (`holdrot`), the sites of `T` with the label margin in `Gl`, the reference configuration `0`,
and `A` a bundled family of the activities gated at `ε` with the local activities.  For a real
orthogonal `Q`, a parameter `θ_b` of the chart of radius `ε` and a parameter `θ_b'` whose raw data
are the rotation of those of `θ_b`, the coefficients gated at `ε′` agree. -/
theorem coeffLoc_rot_of (hS1 : S.a₁ = 1) {eps eps' : ℝ} (hle : eps ≤ eps')
    {c c₂ Kc Cx Kf Cf : ℝ} (hS : Dec2.DecSpecs d L Kc Cx c NS.BG)
    (Sb : Dec2.CoverBase (coverOf Gl) Gl (compWeight L S.a₁) S.ν Kc Cx)
    (hC : FlCore N Gl Gd S.a₁ S.ν c NS.BG NS.κ eps Kf Cf c₂ NS.BG₂ t)
    (hHm : Gd.Ω (k + 1) = ∅) {cψ : ℝ} (hcψ : 0 ≤ cψ)
    (hMX : cstarX d L * Real.exp (N0 d L * NS.κ) ≤ (L : ℝ) ^ m₁) {δc : ℝ} (hδc : 0 ≤ δc)
    (hdm : decDomMargin d L N NS.BG NS.κ (xiC1 d * eps) < δc)
    (hα : K4 d L N NS.BG NS.κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L NS.κ ≤ 1 / 4) (hρ₀c : 2 * NS.p₁ ≤ cψ)
    (hρp : S.p₁ ≤ NS.p₁)
    (hRu : corrU * markedRad d L N k S.a₁ NS.κ cψ ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) < t)
    {Q : Matrix (Fin N) (Fin N) ℝ} (hQ : Qᵀ * Q = 1)
    -- the old terms
    {cψL : ℝ} (hρpL : S.p₁ ≤ NS.O.ρ) (hρcL : NS.O.ρ ≤ cψL) {t₀ : ℝ} (ht₀ : 0 < t₀)
    (hδ₁L : 0 < NS.O.δ₁)
    (hRt : (corrU + t₀) *
      markedRad d L N k S.a₁ NS.O.κ cψL ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) < NS.O.δ₁)
    (holdrot : ∀ τ (um tm : ℂ), (‖um‖ + ‖tm‖) *
        markedRad d L N k S.a₁ NS.O.κ cψL ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) < NS.O.δ₁ →
      ∀ Y, LabelMargin Gl Y → ∀ D : BgData Gl N,
      XiCData Gl (compWeight L S.a₁) S.ν (k + 1) 1 eps D →
      ∀ ψh : unitPts S.G' × Fin N → ℂ, (∀ p, ‖ψh p‖ ≤ cψL) →
        evDecBg S.G' (NS.O.X₁f τ) NS.O.m₀ (NS.O.jL τ) (NS.O.𝒦X τ) Gl S.a₁ S.ν
            (BgTransport.canon S.G' Gl N) ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) (F₁L' τ)
            (SolL' τ) (eTermFun Gl (NS.O.Gk τ) (NS.O.Gj τ) Gd (compWeight L S.a₁) (NS.O.FkL τ)
              (fun r => (S.β : ℂ)⁻¹ * NS.O.Eτ τ r)) (maskPre S.hG' Gl (S.blockU z)) um tm Y
            (rotRaw (cmat Q) (rawOf D),
              (BgTransport.canon S.G' Gl N).res (rotFld (cmat Q) ψh)) =
          evDecBg S.G' (NS.O.X₁f τ) NS.O.m₀ (NS.O.jL τ) (NS.O.𝒦X τ) Gl S.a₁ S.ν
            (BgTransport.canon S.G' Gl N) ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) (F₁L' τ)
            (SolL' τ) (eTermFun Gl (NS.O.Gk τ) (NS.O.Gj τ) Gd (compWeight L S.a₁) (NS.O.FkL τ)
              (fun r => (S.β : ℂ)⁻¹ * NS.O.Eτ τ r)) (maskPre S.hG' Gl (S.blockU z)) um tm Y
            (rawOf D, (BgTransport.canon S.G' Gl N).res ψh))
    -- the zero-source and bridge pairs of `(Gl, Gd)`
    (hF₂s' : ∀ b (s : Dec2.DecParams (coverOf Gl)) (D : BgData Gl N),
      (∀ P, ‖s P‖ < Real.exp NS.κ) →
      InUnionDomainC Gl (bgC0 d L N) (c7 d L N NS.BG NS.κ) S.ν D → ∀ (φ : Gl.Ω 1 × Fin N → ℂ)
        (α : Gl.Ω 1 → ℂ), Dec2.IsDecBg (coverOf Gl) Gl (compWeight L S.a₁) S.ν
          (rho4 d L N NS.BG NS.κ) s D φ α → F₂' b (s, rawOf D) = (φ, α))
    (hSol₂' : ∀ b (p : Dec2.DecParams (coverOf Gl) × Edat Gd N),
      (∀ P, ‖p.1 P‖ < Real.exp NS.κ) →
      StrictDataM Gd N false (2 * (K4 d L N NS.BG NS.κ * (xiC1 d * eps))) t p.2 →
        (Sol₂' b p).1 = dphi Gd (Dec2.decG (coverOf Gl) Gd (compWeight L S.a₁) S.ν p.1) p.2.2.1
          p.2.1 (pertSource Gd (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) (Sol₂' b p).2 ∧
        Dec2.DecFixed (coverOf Gl) Gd (compWeight L S.a₁) S.ν p.1 false p.2.2.1 p.2.1
          (pertSource Gd (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) (Sol₂' b p).2 ∧
        Small Gd (Sol₂' b p).2 (c6' d L N (famConst d L NS.BG₂ NS.κ) (gamma1 d / 8)) ∧
        Small Gd (Sol₂' b p).2 (cK2' d L N (famConst d L NS.BG₂ NS.κ) * t) ∧
        SupBounds Gd (Sol₂' b p).1 (cK2' d L N (famConst d L NS.BG₂ NS.κ) * t) ∧
        (∀ δα' : Gd.Ω 1 → ℂ, Small Gd δα' (c6' d L N (famConst d L NS.BG₂ NS.κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf Gl) Gd (compWeight L S.a₁) S.ν p.1 false p.2.2.1 p.2.1
            (pertSource Gd (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol₂' b p).2))
    (hF₁b' : ∀ b (s : Dec2.DecParams (coverOf Gl)) (D : BgData Gl N),
      (∀ P, ‖s P‖ < Real.exp NS.κ) →
      InUnionDomainC Gl (bgC0 d L N) (c7 d L N NS.BG NS.κ) S.ν D → ∀ (φ : Gl.Ω 1 × Fin N → ℂ)
        (α : Gl.Ω 1 → ℂ), Dec2.IsDecBg (coverOf Gl) Gl (compWeight L S.a₁) S.ν
          (rho4 d L N NS.BG NS.κ) s D φ α → F₁b' b (s, rawOf D) = (φ, α))
    (hSolb' : ∀ b (p : Dec2.DecParams (coverOf Gl) × Edat Gd N),
      (∀ P, ‖p.1 P‖ < Real.exp NS.κ) →
      StrictDataM Gd N false (2 * (K4 d L N NS.BG NS.κ * (xiC1 d * eps))) t p.2 →
        (Solb' b p).1 = dphi Gd (Dec2.decG (coverOf Gl) Gd (compWeight L S.a₁) S.ν p.1) p.2.2.1
          p.2.1 (pertSource Gd (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) (Solb' b p).2 ∧
        Dec2.DecFixed (coverOf Gl) Gd (compWeight L S.a₁) S.ν p.1 false p.2.2.1 p.2.1
          (pertSource Gd (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) (Solb' b p).2 ∧
        Small Gd (Solb' b p).2 (c6' d L N (famConst d L NS.BG₂ NS.κ) (gamma1 d / 8)) ∧
        Small Gd (Solb' b p).2 (cK2' d L N (famConst d L NS.BG₂ NS.κ) * t) ∧
        SupBounds Gd (Solb' b p).1 (cK2' d L N (famConst d L NS.BG₂ NS.κ) * t) ∧
        (∀ δα' : Gd.Ω 1 → ℂ, Small Gd δα' (c6' d L N (famConst d L NS.BG₂ NS.κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf Gl) Gd (compWeight L S.a₁) S.ν p.1 false p.2.2.1 p.2.1
            (pertSource Gd (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Solb' b p).2))
    -- the polymer, the bundled activities and the two parameters
    (Zb : Finset (unitPts Gl)) (Φ₀ : ∀ b, (S.blockSplit 1 NS.hp).Ωb b)
    (hΦ₀ : ∀ b u, Φ₀ b u = 0)
    (T : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) 1 (k + 1) Set.univ))
    (hTm : LabelMargin Gl (sitesOf T)) {εH κH κ0 Kc' : ℝ}
    (A : physParamBg N Gl → ℂ → LabelAct NS.Lab (S.blockSplit 1 NS.hp).Ωb εH κH κ0 Kc')
    (hAH : ∀ θb u y Φ, (A θb u).H y Φ =
      locAct NS.Lab T Φ₀ (NS.actBg F₂' Sol₂' F₁L' SolL' eps) θb u y Φ)
    {θb θb' : physParamBg N Gl}
    (hθb : (θb.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) ∈
      XiCRaw Gl (compWeight L S.a₁) S.ν (k + 1) 1 eps)
    (hrot : (θb'.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) =
      rotRaw (cmat Q) (θb.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N)) :
    NS.coeffLoc F₂' Sol₂' F₁L' SolL' F₁b' Solb' eps' Zb Φ₀ θb' T =
      NS.coeffLoc F₂' Sol₂' F₁L' SolL' F₁b' Solb' eps' Zb Φ₀ θb T := by
  have ht : 0 < t := hC.δ₁_pos
  have hθb' : (θb'.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) ∈
      XiCRaw Gl (compWeight L S.a₁) S.ν (k + 1) 1 eps := by
    rw [hrot]; exact rotRaw_mem hQ hθb
  obtain ⟨D, hD, hθD⟩ := hθb
  have hθ'D : (θb'.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) = rotRaw (cmat Q) (rawOf D) := by
    rw [hrot, hθD]
  obtain ⟨e, he⟩ := exists_linearIsometryEquiv_of_orth N hQ
  obtain ⟨E, hE, hEeq⟩ := exists_blockSplit_equiv S 1 NS.hp e
  have hE₀ : ∀ b, E b (Φ₀ b) = Φ₀ b := fun b => by
    have h : E b (Φ₀ b) = fun u => e (Φ₀ b u) := congrFun (hEeq Φ₀) b
    rw [h]
    funext u
    rw [hΦ₀ b u, map_zero]
  have hQr : ∀ Φ ∈ physCarrier S 1 NS.hp, ∀ S' : Finset (CubeB (d := d) (L := L) (N₁ := N₁)
      (m₁ := m₁) (K := k + 1) 1 (k + 1) Set.univ), restrConf S' Φ₀ Φ ∈ physCarrier S 1 NS.hp := by
    intro Φ hΦ S'
    show ∀ b u, ‖restrConf S' Φ₀ Φ b u‖ ≤ S.p₁
    intro b u
    simp only [restrConf]
    split_ifs
    · exact hΦ b u
    · rw [hΦ₀ b u, norm_zero]
      exact NS.hp.le
  -- labels inside `T` have the margin
  have hsub : ∀ {Y : Set (CTorus d L N₁ m₁ (k + 1))}, Y ⊆ sitesOf T → LabelMargin Gl Y :=
    fun hY => labelMargin_of_subset hY hTm
  -- the cover of the blocks
  have hX₁B := fun b => LocalCover.coe_nbhdF_eq_X1 S.hG' NS.Z.hN (le_refl (k + 1))
    (LocalCover.blockSite k b)
  -- the pins in the form of the covariance lemmas
  have hF₂n : ∀ b (s : DecParams Gl) (D : BgData Gl N), (∀ P, ‖s P‖ < Real.exp NS.κ) →
      InUnionDomainC Gl (bgC0 d L N) (c7 d L N NS.BG NS.κ) S.ν D → ∀ (φ : Gl.Ω 1 × Fin N → ℂ)
        (α : Gl.Ω 1 → ℂ), IsDecBg Gl (compWeight L S.a₁) S.ν (rho4 d L N NS.BG NS.κ) s D φ α →
        F₂' b (s, rawOf D) = (φ, α) := fun b s D hs hD φ α hI =>
    hF₂s' b s D hs hD φ α ((dec2_isDecBg_iff Gl _ _ _ s D φ α).2 hI)
  have hF₁n : ∀ b (s : DecParams Gl) (D : BgData Gl N), (∀ P, ‖s P‖ < Real.exp NS.κ) →
      InUnionDomainC Gl (bgC0 d L N) (c7 d L N NS.BG NS.κ) S.ν D → ∀ (φ : Gl.Ω 1 × Fin N → ℂ)
        (α : Gl.Ω 1 → ℂ), IsDecBg Gl (compWeight L S.a₁) S.ν (rho4 d L N NS.BG NS.κ) s D φ α →
        F₁b' b (s, rawOf D) = (φ, α) := fun b s D hs hD φ α hI =>
    hF₁b' b s D hs hD φ α ((dec2_isDecBg_iff Gl _ _ _ s D φ α).2 hI)
  -- the radii of the marks
  have hδ₁c : markedRad d L N k S.a₁ NS.κ cψ ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) < t := by
    have h := mul_lt_of_le_of_mul_lt (a := 1) (by norm_num [corrU]) hRu ht zero_le_one
    rwa [one_mul] at h
  have hRuL : corrU * markedRad d L N k S.a₁ NS.O.κ cψL ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) <
      NS.O.δ₁ :=
    mul_lt_of_le_of_mul_lt (by linarith) hRt hδ₁L (by norm_num [corrU])
  have hρL : 0 < NS.O.ρ := lt_of_lt_of_le NS.hp hρpL
  refine NS.coeffLoc_rot_of_parts F₂' Sol₂' F₁L' SolL' F₁b' Solb' hle Zb Φ₀ T A hAH E hE hE₀
    (ae_mem_physCarrier S 1 NS.hp) hQr ⟨D, hD, hθD⟩ hθb' ?_ (fun s _ Y hY Φ hΦ => ?_)
    (fun s _ Y hY Φ hΦ => ?_) (fun s _ i hi Φ hΦ => ?_)
  · -- the determinant part
    have h := newLevelDetBg_rot_param hC S.hk1 hδc hMX hsm hdm hα (isRealOrth_ofReal hQ).1 Zb T
      ⟨D, hD, hθD⟩ hrot
    rw [hS1] at h
    exact h
  · -- the zero-source activities
    have hYm := hsub (Y := Y.1) (ysite_subset_sitesOf NS.Z.hN NS.Lab (Sum.inl (Sum.inl Y)) hY)
    rw [hEeq Φ]
    exact zeroActBg_canon_rot S hS Sb hC hHm hcψ hMX hdm hα hsm hX₁B hF₂n hSol₂' hδ₁c taylorWeight
      hρp hρ₀c NS.hp hYm hQ e he hD hθD hrot (s : ℂ) hΦ
  · -- the old activities
    have hYm := hsub (Y := Y.1)
      (ysite_subset_sitesOf NS.Z.hN NS.Lab (Sum.inl (Sum.inr (Sum.inl Y))) hY)
    refine oldActBg_congr_of_terms S Gl (BgTransport.canon S.G' Gl N)
      (maskPre S.hG' Gl (S.blockU z)) NS.O.X₁f NS.O.m₀ NS.O.jL NS.O.𝒦X F₁L' SolL' _ NS.O.ρ
      NS.hp corrU eps NS.𝒴C hθb' ⟨D, hD, hθD⟩ Y (fun b => E b (Φ b)) Φ
      (fun τ _ um hum => ?_) (by norm_num [corrU]) (s : ℂ)
    rw [hEeq Φ, hatOf_rot S 1 NS.hp e he hρpL hΦ, hθ'D, hθD]
    exact holdrot τ um 0 (mem_markedRad_of_le hδ₁L hRuL hum.le) Y.1 hYm D hD _
      fun q => (S.hatOf_mem 1 hρL NS.hp Φ q).trans hρcL
  · rcases i with i | q
    · -- the bridge marks
      have hiT : i.1 ⊆ sitesOf T := ysite_subset_sitesOf NS.Z.hN NS.Lab (NS.y0 (Sum.inl i)) hi
      show e1MarkGParamGBgOn S Gl (BgTransport.canon S.G' Gl N) (maskPre S.hG' Gl (S.blockU z))
          F₁b' Solb' NS.p₁ NS.hp z Gl eps θb' i (s : ℂ) (fun b => E b (Φ b)) =
        e1MarkGParamGBgOn S Gl (BgTransport.canon S.G' Gl N) (maskPre S.hG' Gl (S.blockU z))
          F₁b' Solb' NS.p₁ NS.hp z Gl eps θb i (s : ℂ) Φ
      refine e1MarkGParamGBgOn_congr_of_terms S (BgTransport.canon S.G' Gl N)
        (maskPre S.hG' Gl (S.blockU z)) F₁b' Solb' NS.p₁ NS.hp z eps (δ₁ := t) hRu ht hθb'
        ⟨D, hD, hθD⟩ i (fun b => E b (Φ b)) Φ (fun q hqm hbr v w hvw => ?_) (s : ℂ)
      have hbT : bridge 1 z q.2 ⊆ sitesOf T := by rw [hbr]; exact hiT
      have hYm := hsub (Y := q.2) ((subset_bridge z q.2).trans hbT)
      rw [hEeq Φ, hatOf_rot S 1 NS.hp e he hρp hΦ, hθ'D, hθD]
      exact blockEvBg_canon_rot_of_margin S hS Sb hC hHm _ hcψ hMX hdm hα hsm (hF₁n q.1)
        (hSolb' q.1) (hX₁B q.1) q.1 hQ _ hvw hYm hD
        fun p => (S.hatOf_mem 1 NS.Z.hp₁ NS.hp Φ p).trans (by linarith [NS.Z.hp₁])
    · -- the old marks
      have hqT : bridge 1 z q.1.2 ⊆ sitesOf T :=
        ysite_subset_sitesOf NS.Z.hN NS.Lab (NS.y0 (Sum.inr q)) hi
      have hYm := hsub (Y := q.1.2) ((subset_bridge z q.1.2).trans hqT)
      show oldMarkGBg S Gl (BgTransport.canon S.G' Gl N) (maskPre S.hG' Gl (S.blockU z)) NS.O.X₁f
          NS.O.m₀ NS.O.jL NS.O.𝒦X F₁L' SolL'
          (fun τ => eTermFun Gl (NS.O.Gk τ) (NS.O.Gj τ) Gd (compWeight L S.a₁) (NS.O.FkL τ)
            (fun r => (S.β : ℂ)⁻¹ * NS.O.Eτ τ r)) NS.O.ρ NS.hp corrU eps z θb' q (s : ℂ)
            (fun b => E b (Φ b)) =
        oldMarkGBg S Gl (BgTransport.canon S.G' Gl N) (maskPre S.hG' Gl (S.blockU z)) NS.O.X₁f
          NS.O.m₀ NS.O.jL NS.O.𝒦X F₁L' SolL'
          (fun τ => eTermFun Gl (NS.O.Gk τ) (NS.O.Gj τ) Gd (compWeight L S.a₁) (NS.O.FkL τ)
            (fun r => (S.β : ℂ)⁻¹ * NS.O.Eτ τ r)) NS.O.ρ NS.hp corrU eps z θb q (s : ℂ) Φ
      refine oldMarkGBg_congr_of_terms S Gl (BgTransport.canon S.G' Gl N)
        (maskPre S.hG' Gl (S.blockU z)) NS.O.X₁f NS.O.m₀ NS.O.jL NS.O.𝒦X F₁L' SolL' _ NS.O.ρ
        NS.hp corrU eps z hθb' ⟨D, hD, hθD⟩ q ht₀ (fun b => E b (Φ b)) Φ
        (fun um hum w hw => ?_) (s : ℂ)
      have hW : (‖um‖ + ‖w‖) *
          markedRad d L N k S.a₁ NS.O.κ cψL ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) < NS.O.δ₁ :=
        mul_lt_of_le_of_mul_lt (by linarith) hRt hδ₁L (by positivity)
      rw [hEeq Φ, hatOf_rot S 1 NS.hp e he hρpL hΦ, hθ'D, hθD]
      exact holdrot q.1.1 um w hW q.1.2 hYm D hD _
        fun p => (S.hatOf_mem 1 hρL NS.hp Φ p).trans hρcL

end NewLevelSystem

end Balaban.Inhabited
