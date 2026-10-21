/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.NewLevelCoeffTwoTorus

/-!
# The premises of the comparison of two old terms from the data of the systems

`termPairPremisesAt_of_data`: for the old term `τ` of a system `NS` and the old term `τ'` of a system
`NS'` on the second torus whose label cubes are the image of those of `τ` under `boxMap`, and whose
level and cover parameter agree, the premises structure `OldTermPair` of the comparison of the
localized old terms (`TermPairPremisesAt`) is assembled from

* the settings of the inherited levels `OldTermSettings` of the two systems (`hB`, `hF`, `hcov`,
  `hX₁`; `FlCore` is `flCore_of` of them), the pins of the decoupled fields (`hF₁L`, `hSolL`, `hFkL`)
  and the equality of the constants of the two systems (`HasConsts`);
* the geometry of the old term on the margin `Z` (the label cubes, the correspondence of the
  localized generating sets on `Z`, the old terms agree on fields that agree on `Z`);
* the numerical conditions on the radii and the analyticity of the old-term functional.
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Localization Balaban.Fluctuation Balaban.SmallField Balaban.SmallField.Def6
  Balaban.Polymer Balaban.Polymer.TwoTorusStep Balaban.Multiscale Balaban.Background
  Balaban.Inhabited.LevelStep


open Balaban Balaban.Localization Balaban.Fluctuation Balaban.SmallField Balaban.SmallField.Def6
  Balaban.Polymer Balaban.Polymer.TwoTorusStep Balaban.Multiscale Balaban.Background
  Balaban.Inhabited.LevelStep

variable {d L N₁ N₁' m₁ k N : ℕ} [NeZero N₁] [NeZero N₁'] [NeZero L] {ϱ : ℝ}

set_option hygiene false in
local notation "bm" => boxMap ((N₁ * L ^ m₁) * L ^ (k + 1)) ((N₁' * L ^ m₁) * L ^ (k + 1))
set_option hygiene false in
local notation "GA" => levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ)
  (k + 1) le_rfl
set_option hygiene false in
local notation "GB" => levelGS (d := d) (L := L) (N₁ := N₁') (m₁ := m₁) (k := k + 1) (ϱ := ϱ)
  (k + 1) le_rfl
set_option hygiene false in
local notation "SA" => hatStepKG (d := d) (L := L) (N := N) (N₁ := N₁) hN2 k m₁ ϱ hk νS β p₁ δ
set_option hygiene false in
local notation "SB" => hatStepKG (d := d) (L := L) (N := N) (N₁ := N₁') hN2 k m₁ ϱ hk νS β p₁ δ

set_option hygiene false in
local notation "HA" => levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ)
  k (Nat.le_succ k)
set_option hygiene false in
local notation "HB" => levelGS (d := d) (L := L) (N₁ := N₁') (m₁ := m₁) (k := k + 1) (ϱ := ϱ)
  k (Nat.le_succ k)

/-- **The premises of the comparison of two old terms from the canonical data.**  See the module
doc-string. -/
theorem termPairPremisesAt_of_data
    (hN2 : 2 ≤ N) (hk : 1 ≤ k) (νS β p₁ δ : ℝ)
    {C : StepClass d L N₁ m₁ k N ϱ} {z : RootIdx d L N₁ m₁ (k + 1)} {t pp : ℝ}
    {Jr : (SA).JointRep t pp}
    {C' : StepClass d L N₁' m₁ k N ϱ} {z' : RootIdx d L N₁' m₁ (k + 1)} {t' pp' : ℝ}
    {Jr' : (SB).JointRep t' pp'}
    (NS : NewLevelSystem (SA) C z Jr) (NS' : NewLevelSystem (SB) C' z' Jr')
    (τ : NS.O.ι) (τ' : NS'.O.ι) (θ : physParam N (SA)) (θ' : physParam N (SB))
    (Y : Set (CTorus d L N₁ m₁ (k + 1)))
    (Φ : ∀ b, ((SA).blockSplit 1 NS.hp).Ωb b) (Φ' : ∀ b, ((SB).blockSplit 1 NS'.hp).Ωb b)
    (u t₀ : ℂ)
    {K : NewLevelConsts} (hK : NS.HasConsts K) (hK' : NS'.HasConsts K) (ht : t' = t)
    (hX : NS'.O.X₁f τ' = (NS.O.X₁f τ).image bm) (hm₀ : NS'.O.m₀ = NS.O.m₀)
    (hj : NS'.O.jL τ' = NS.O.jL τ)
    (hθ : θ ∈ physV (SA) (SA).a₁ (SA).ν t) (hθ' : θ' ∈ physV (SB) (SB).a₁ (SB).ν t')
    {R : ℕ} {Z : Set (CTorus d L N₁ m₁ (k + 1))}
    (hZX : Z ⊆ ↑(NS.O.X₁f τ)) (hBMZ : BlockMargin (SA).G' (NS.O.X₁f τ) Z)
    (hGk : GSCorr (NS.O.Gk τ) (NS'.O.Gk τ') bm Z) (hGj : GSCorr (NS.O.Gj τ) (NS'.O.Gj τ') bm Z)
    (hiso : GSIso (compWeight L (SA).a₁) (SA).ν (NS.O.Gk τ) (NS'.O.Gk τ') bm Z)
    (hblk : ∀ z ∈ Z, z ∈ (NS.O.Gk τ).Ω 1 →
      (∀ y ∈ (NS.O.Gk τ).blk ((NS.O.Gk τ).layerIndex z) z, y ∈ Z) ∧
      (∀ y ∈ (SA).G'.blk ((SA).G'.layerIndex z) z, y ∈ Z) ∧
      (∀ y ∈ (stepG d L N₁ m₁ k ϱ).blk ((stepG d L N₁ m₁ k ϱ).layerIndex z) z, y ∈ Z))
    (hblk2 : ∀ z ∈ Z, z ∈ (NS.O.Gj τ).Ω 1 →
      (∀ y ∈ (NS.O.Gj τ).blk ((NS.O.Gj τ).layerIndex z) z, y ∈ Z) ∧
      (∀ y ∈ (NS.O.Gk τ).blk ((NS.O.Gk τ).layerIndex z) z, y ∈ Z))
    (hE : ∀ (r : RawData d L (N₁ * L ^ m₁) (k + 1) N) (r' : RawData d L (N₁' * L ^ m₁) (k + 1) N),
      (∀ z ∈ Z, r.1 z = r'.1 (bm z) ∧ r.2 z = r'.2 (bm z)) →
      ((SB).β : ℂ)⁻¹ * NS'.O.Eτ τ' r' = ((SA).β : ℂ)⁻¹ * NS.O.Eτ τ r)
    (hX₁R : ∀ x ∈ NS.O.X₁f τ, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x)
    (hYR : ∀ y ∈ Y, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) y)
    (hn : 4 * R + 12 * L ^ (k + 1 + m₁) + 7 * L ^ (k + 1) + 5 < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hn' : 4 * R + 12 * L ^ (k + 1 + m₁) + 7 * L ^ (k + 1) + 5 < (N₁' * L ^ m₁) * L ^ (k + 1))
    (hnS : 2 * (R + (3 * L ^ (k + 1 + m₁) + 3 * L ^ (k + 1 + 2)) + L ^ (k + 1 + m₁)) +
      5 * (L * cellSide L 0 m₁ (k + 1)) < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hnS' : 2 * (R + (3 * L ^ (k + 1 + m₁) + 3 * L ^ (k + 1 + 2)) + L ^ (k + 1 + m₁)) +
      5 * (L * cellSide L 0 m₁ (k + 1)) < (N₁' * L ^ m₁) * L ^ (k + 1))
    (hnF : 2 * R + 5 * (L * cellSide L NS.O.m₀ m₁ (k + 1)) < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hnF' : 2 * R + 5 * (L * cellSide L NS.O.m₀ m₁ (k + 1)) < (N₁' * L ^ m₁) * L ^ (k + 1))
    (hΦan : AnalyticOnNhd ℂ (fun t' => (eTermFun (SA).G' (NS.O.Gk τ) (NS.O.Gj τ)
      (stepG d L N₁ m₁ k ϱ) (compWeight L (SA).a₁) (NS.O.FkL τ)
      (fun r => ((SA).β : ℂ)⁻¹ * NS.O.Eτ τ r)) t'.1 t'.2.1 t'.2.2)
      (FlReal (SA).G' (stepG d L N₁ m₁ k ϱ) (SA).a₁ (SA).ν NS.O.BG NS.O.κ t (NS.O.X₁f τ)
        NS.O.BG₂ NS.O.δ₁))
    (hraw : RawBoxAgree {z | InBox d (R + 3 * L ^ (k + 1)) ((N₁ * L ^ m₁) * L ^ (k + 1)) z}
      (θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) (θ'.1 : RawData d L (N₁' * L ^ m₁) (k + 1) N))
    (hR : ∀ x, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x →
      Φ' ((SB).cellOf 1 (unitPt (SB).hG' (bm x))) ⟨unitPt (SB).hG' (bm x), rfl⟩ =
        Φ ((SA).cellOf 1 (unitPt (SA).hG' x)) ⟨unitPt (SA).hG' x, rfl⟩)
    (hZm : ∀ x, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x →
      (unitPt (SB).hG' (bm x) ∈ (SB).blockU z' ↔ unitPt (SA).hG' x ∈ (SA).blockU z))
    {δc : ℝ} (hMX : cstarX d L * Real.exp (N0 d L * NS.O.κ) ≤ (L : ℝ) ^ m₁)
    (hmar : decDomMargin d L N NS.O.BG NS.O.κ (xiC1 d * t) < δc)
    (hαK : K4 d L N NS.O.BG NS.O.κ * (xiC1 d * t) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L NS.O.κ ≤ 1 / 4) (hρ : 0 < NS.O.ρ)
    (hum : (‖u‖ + ‖t₀‖) * markedRad d L N k (SA).a₁ NS.O.κ NS.O.ρ
      (((SA).betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) < NS.O.δ₁) :
    TermPairPremisesAt NS NS' τ τ' θ θ' Y Φ Φ' u t₀ := by
  subst ht
  have hcB : NS'.OS.cB = NS.OS.cB := hK'.cB.trans hK.cB.symm
  have hr₀ : NS'.OS.r₀ = NS.OS.r₀ := hK'.r₀.trans hK.r₀.symm
  have hδ₃ : NS'.OS.δ₃ = NS.OS.δ₃ := hK'.δ₃.trans hK.δ₃.symm
  have hKc : NS'.OS.Kc = NS.OS.Kc := hK'.Kc.trans hK.Kc.symm
  have hCx : NS'.OS.Cx = NS.OS.Cx := hK'.Cx.trans hK.Cx.symm
  have hc₂ : NS'.OS.c₂ = NS.OS.c₂ := hK'.c₂.trans hK.c₂.symm
  have hδfl : NS'.OS.δfl = NS.OS.δfl := hK'.δfl.trans hK.δfl.symm
  have hBG : NS'.O.BG = NS.O.BG := hK'.BGO.trans hK.BGO.symm
  have hκ : NS'.O.κ = NS.O.κ := hK'.κO.trans hK.κO.symm
  have hBG₂ : NS'.O.BG₂ = NS.O.BG₂ := hK'.BG₂O.trans hK.BG₂O.symm
  have hδ₁ : NS'.O.δ₁ = NS.O.δ₁ := hK'.δ₁O.trans hK.δ₁O.symm
  have hρe : NS'.O.ρ = NS.O.ρ := hK'.ρO.trans hK.ρO.symm
  have hθ1 : (θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) ∈
      XiCRaw (SA).G' (compWeight L (SA).a₁) (SA).ν (k + 1) 1 t' := hθ.1
  have hθ1' : (θ'.1 : RawData d L (N₁' * L ^ m₁) (k + 1) N) ∈
      XiCRaw (SB).G' (compWeight L (SB).a₁) (SB).ν (k + 1) 1 t' := hθ'.1
  obtain ⟨D, hD, hDe⟩ := hθ1
  obtain ⟨D', hD', hDe'⟩ := hθ1'
  have hB' := NS'.OS.hB τ'
  have hF' := NS'.OS.hF τ'
  have hcov' := NS'.OS.hcov τ'
  have hX₁' := NS'.OS.hX₁ τ'
  rw [hcB, hr₀, hδ₃, hBG, hκ, hX, hj] at hB'
  rw [hκ, hBG, hδ₃, hKc, hCx, hc₂, hBG₂, hδ₁, hδfl, hX] at hF'
  rw [hm₀, hj] at hcov' hX₁'
  rw [hX] at hX₁'
  have hhat := hatOf_boxMap (SA).hG' (SB).hG' hN2 hk νS β p₁ δ 1 NS.O.ρ NS.hp NS'.hp Φ Φ' hR
  refine ⟨NS.OS.cB, NS.O.BG, NS.O.κ, t', NS.OS.Kc, NS.OS.Cx, NS.OS.c₂, NS.O.BG₂, NS.O.δ₁,
    NS.O.ρ, δc, NS.OS.XL τ, NS'.OS.XL τ', NS.OS.r₀, NS.OS.δ₃, NS.OS.δfl, NS.O.jL τ,
    NS.OS.X₀ τ, NS'.OS.X₀ τ', R, Z, D, D', hDe, hDe', ⟨?_⟩⟩
  exact
    { eGA := rfl, eGB := rfl, eHA := rfl, eHB := rfl
      hC := flCore_of (NS.OS.hB τ) (NS.OS.hF τ)
      hC' := flCore_of hB' hF'
      hk := hk
      hGA := (SA).hG'
      hGB := (SB).hG'
      hcψ := hρ.le
      hMX := hMX
      hmar := hmar
      hαK := hαK
      hsm := hsm
      hF₁ := NS.O.hF₁L τ
      hF₁' := by
        have := NS'.O.hF₁L τ'
        rw [hκ, hBG] at this
        exact this
      hSol := NS.O.hSolL τ
      hSol' := by
        have := NS'.O.hSolL τ'
        rw [hκ, hBG, hBG₂, hδ₁] at this
        exact this
      hcov := NS.OS.hcov τ
      hX₁ := NS.OS.hX₁ τ
      hcov' := hcov'
      hX₁' := hX₁'
      hB := NS.OS.hB τ
      hF := NS.OS.hF τ
      hB' := hB'
      hF' := hF'
      hFk := NS.O.hFkL τ
      hFk' := NS'.O.hFkL τ'
      hZX := hZX
      hBMZ := hBMZ
      hGk := hGk
      hGj := hGj
      hiso := hiso
      hblk := hblk
      hblk2 := hblk2
      hE := hE
      hX₁R := hX₁R
      hYR := hYR
      hn := hn
      hn' := hn'
      hnS := hnS
      hnS' := hnS'
      hnF := hnF
      hnF' := hnF'
      hΦan := hΦan
      hD := hD
      hD' := hD'
      hraw := by rw [hDe, hDe'] at hraw; exact hraw
      hψh := fun p => (SA).hatOf_mem 1 hρ NS.hp Φ p
      hψh' := fun p => by
        have h := (SB).hatOf_mem 1 (hρe ▸ hρ) NS'.hp Φ' p
        exact h.trans (le_of_eq hρe)
      hhat := fun x hx i => by
        have := hhat x hx i
        rw [hρe]
        exact this
      hZm := hZm
      hum := hum }


end Balaban.Inhabited
