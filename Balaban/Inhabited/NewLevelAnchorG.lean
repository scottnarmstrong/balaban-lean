/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.NewLevelAnchorCorr
public import Balaban.Inhabited.NewLevelZeroCorr

/-!
# The marks of two systems of the new level on two tori

* `anchor_G_inl`: the marks `e1MarkGParamG` of the bridge anchors of two systems agree at
  corresponding anchors (`e1MarkGParamG_twoTorus` with the pins of the decoupling pairs);
* `anchor_G_inr`: the marks `G₁` of the old terms agree at corresponding anchors
  (`NewLevelSystem.G₁_twoTorus_at_of_pairs` and the premises `hprem` of the comparison of corresponding
  old terms, eventually in the second mark variable).
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation
  Balaban.Localization Balaban.Localization.LevelPair Balaban.Localization.I5Inhabited
  Balaban.Polymer Balaban.SmallField.Def6 Balaban.Inhabited.LevelStep
  Balaban.Inhabited.MarkBudgetAudit Matrix Metric Set MeasureTheory Balaban.Polymer.TwoTorusStep

section AnchorG

variable {d L N₁ N₁' m₁ k N : ℕ} [NeZero N₁] [NeZero N₁'] [NeZero L] {ϱ : ℝ}

set_option hygiene false in
local notation "bm" => boxMap ((N₁ * L ^ m₁) * L ^ (k + 1)) ((N₁' * L ^ m₁) * L ^ (k + 1))
set_option hygiene false in
local notation "bc" => boxMap (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1)))
  (N₁' * L ^ m₁ * L ^ (k + 1 - (k + 1)))
set_option hygiene false in
local notation "SA" => hatStepKG (d := d) (L := L) (N := N) (N₁ := N₁) hN2 k m₁ ϱ hk νS β p₁ δ
set_option hygiene false in
local notation "SB" => hatStepKG (d := d) (L := L) (N := N) (N₁ := N₁') hN2 k m₁ ϱ hk νS β p₁ δ
set_option hygiene false in
local notation "GA" => levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ)
  (k + 1) le_rfl
set_option hygiene false in
local notation "GB" => levelGS (d := d) (L := L) (N₁ := N₁') (m₁ := m₁) (k := k + 1) (ϱ := ϱ)
  (k + 1) le_rfl
set_option hygiene false in
local notation "HA" => levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ)
  k (Nat.le_succ k)
set_option hygiene false in
local notation "HB" => levelGS (d := d) (L := L) (N₁ := N₁') (m₁ := m₁) (k := k + 1) (ϱ := ϱ)
  k (Nat.le_succ k)
set_option hygiene false in
local notation "TA" => Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1)))
set_option hygiene false in
local notation "TB" => Torus d (N₁' * L ^ m₁ * L ^ (k + 1 - (k + 1)))

theorem e1MarkGParamG_congr_rho {S : StepSetting d L N₁ m₁ k N ϱ} {ρ ρ' : ℝ} (h : ρ = ρ')
    {F₁ : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) →
      DecParams S.G' × RawData d L (N₁ * L ^ m₁) (k + 1) N →
        (S.G'.Ω 1 × Fin N → ℂ) × (S.G'.Ω 1 → ℂ)}
    {Sol : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) →
      Dec2.DecParams (coverOf S.G') × Edat (stepG d L N₁ m₁ k ϱ) N →
        ((stepG d L N₁ m₁ k ϱ).Ω 1 × Fin N → ℂ) × ((stepG d L N₁ m₁ k ϱ).Ω 1 → ℂ)}
    (hp : 0 < S.p₁) (z : RootIdx d L N₁ m₁ (k + 1)) (eps : ℝ) (θ : physParam N S)
    (i : {Y' // Y' ∈ bridgeFamily 1 (fun _ : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) =>
      (Set.univ : Set (CTorus d L N₁ m₁ (k + 1)))) (e1DomG S) z}) (u : ℂ)
    (Φ : ∀ b, (S.blockSplit 1 hp).Ωb b) :
    e1MarkGParamG S F₁ Sol ρ hp z eps θ i u Φ = e1MarkGParamG S F₁ Sol ρ' hp z eps θ i u Φ := by
  subst h; rfl

attribute [local irreducible] NewLevelSystem.Dom

/-- **The marks of the bridge anchors of two systems agree on two tori.** -/
theorem anchor_G_inl
    (hN2 : 2 ≤ N) (hk : 1 ≤ k) (νS β p₁ δ : ℝ)
    {C : StepClass d L N₁ m₁ k N ϱ} {z : RootIdx d L N₁ m₁ (k + 1)} {t pp : ℝ} {Jr : (SA).JointRep t pp} {C' : StepClass d L N₁' m₁ k N ϱ} {pp' : ℝ} {Jr' : (SB).JointRep t pp'} (NS : NewLevelSystem (SA) C z Jr) (NS' : NewLevelSystem (SB) C' (bc z) Jr')
    (hN : L ^ 1 ∣ N₁) (hN' : L ^ 1 ∣ N₁')
    (hm₁ : 1 ≤ m₁)
    {rc R : ℕ}
    (hz : InBox d rc (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) z) (hrc : L ^ (k + 1) * rc ≤ R) (hroot : ∀ x ∈ rootSet 1 z, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x)
    (hn : 4 * R + 19 * L ^ (k + 2 + 1 + m₁) + 5 < (N₁ * L ^ m₁) * L ^ (k + 1)) (hn' : 4 * R + 19 * L ^ (k + 2 + 1 + m₁) + 5 < (N₁' * L ^ m₁) * L ^ (k + 1))
    {c Kc Cx c₂ : ℝ}
    (hC : FlCore N (GA) (HA) 1 νS c NS.BG NS.κ t Kc Cx c₂ NS.BG₂ t) (hC' : FlCore N (GB) (HB) 1 νS c NS.BG NS.κ t Kc Cx c₂ NS.BG₂ t)
    (hκ : NS'.κ = NS.κ) (hBG : NS'.BG = NS.BG) (hBG₂ : NS'.BG₂ = NS.BG₂) (hp₁ : NS'.p₁ = NS.p₁)
    (hGA : IsLevel (GA) (k + 1)) (hGB : IsLevel (GB) (k + 1))
    (hMX : cstarX d L * Real.exp (N0 d L * NS.κ) ≤ (L : ℝ) ^ m₁) {δc : ℝ} (hmar : decDomMargin d L N NS.BG NS.κ (xiC1 d * t) < δc) (hαK : K4 d L N NS.BG NS.κ * (xiC1 d * t) < coerciveConst d / 2) (hsm : δc ^ 2 * smallConstX d L NS.κ ≤ 1 / 4)
    (θ : physParam N (SA)) (θ' : physParam N (SB)) (hθ : θ ∈ physV (SA) (SA).a₁ (SA).ν t) (hθ' : θ' ∈ physV (SB) (SB).a₁ (SB).ν t) (hraw : RawBoxAgree {z | InBox d (R + 3 * L ^ (k + 1)) ((N₁ * L ^ m₁) * L ^ (k + 1)) z} (θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) (θ'.1 : RawData d L (N₁' * L ^ m₁) (k + 1) N))
    (hum : ∀ u : ℂ, ‖u‖ ≤ 1 → ‖u‖ * markedRad d L N k 1 NS.κ NS.p₁ (((SA).betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) < t)
    (a : {Y' // Y' ∈ bridgeFamily 1 (fun _ : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) => (Set.univ : Set (CTorus d L N₁ m₁ (k + 1)))) (e1DomG (SA)) z}) (b : {Y' // Y' ∈ bridgeFamily 1 (fun _ : Torus d (N₁' * L ^ m₁ * L ^ (k + 1 - (k + 1))) => (Set.univ : Set (CTorus d L N₁' m₁ (k + 1)))) (e1DomG (SB)) (bc z)}) (hab : b.1 = bm '' a.1)
    (haR : ∀ y ∈ a.1, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) y) :
    ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ Φ Φ', (∀ x, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x → Φ' ((SB).cellOf 1 (unitPt (SB).hG' (bm x))) ⟨unitPt (SB).hG' (bm x), rfl⟩ = Φ ((SA).cellOf 1 (unitPt (SA).hG' x)) ⟨unitPt (SA).hG' x, rfl⟩) →
      (NS'.G θ') (Sum.inl b) (s : ℂ) Φ' = (NS.G θ) (Sum.inl a) (s : ℂ) Φ := by
  intro s hs Φ Φ' hΦ
  have hs1 : ‖(s : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs.1]; exact hs.2
  obtain ⟨⟨hn1, hnS, hnF, hnH, hnM⟩, ⟨hn1', hnS', hnF', hnH', hnM'⟩⟩ :=
    twoTorus_margins_of_lt_min (R := R) (k := k) (m₀ := 1) (m₁ := m₁) hm₁ (lt_min hn hn')
  have hF₁ : ∀ (b : TA) (s : DecParams (GA)) (D : BgData (GA) N),
      (∀ P, ‖s P‖ < Real.exp NS.κ) →
      InUnionDomainC (GA) (bgC0 d L N) (c7 d L N NS.BG NS.κ) νS D → ∀ (φ : (GA).Ω 1 × Fin N → ℂ)
        (α : (GA).Ω 1 → ℂ), IsDecBg (GA) (compWeight L 1) νS (rho4 d L N NS.BG NS.κ) s D φ α →
        NS.F₁ (z, b) (s, rawOf D) = (φ, α) :=
    fun b => NS.hF₁ b
  have hF₁' : ∀ (b : TB) (s : DecParams (GB)) (D : BgData (GB) N),
      (∀ P, ‖s P‖ < Real.exp NS.κ) →
      InUnionDomainC (GB) (bgC0 d L N) (c7 d L N NS.BG NS.κ) νS D → ∀ (φ : (GB).Ω 1 × Fin N → ℂ)
        (α : (GB).Ω 1 → ℂ), IsDecBg (GB) (compWeight L 1) νS (rho4 d L N NS.BG NS.κ) s D φ α →
        NS'.F₁ (bc z, b) (s, rawOf D) = (φ, α) :=
    fun b => (NS'.hF₁ b).congr hκ hBG
  have hSol : ∀ (b : TA) (p : Dec2.DecParams (coverOf (GA)) × Edat (HA) N),
      (∀ P, ‖p.1 P‖ < Real.exp NS.κ) →
      StrictDataM (HA) N false (2 * (K4 d L N NS.BG NS.κ * (xiC1 d * t))) t p.2 →
        (NS.Sol (z, b) p).1 = dphi (HA) (Dec2.decG (coverOf (GA)) (HA) (compWeight L 1) νS p.1) p.2.2.1
          p.2.1 (pertSource (HA) (compWeight L 1) p.2.2.2.1 p.2.2.2.2) (NS.Sol (z, b) p).2 ∧
        Dec2.DecFixed (coverOf (GA)) (HA) (compWeight L 1) νS p.1 false p.2.2.1 p.2.1
          (pertSource (HA) (compWeight L 1) p.2.2.2.1 p.2.2.2.2) (NS.Sol (z, b) p).2 ∧
        Small (HA) (NS.Sol (z, b) p).2 (c6' d L N (famConst d L NS.BG₂ NS.κ) (gamma1 d / 8)) ∧
        Small (HA) (NS.Sol (z, b) p).2 (cK2' d L N (famConst d L NS.BG₂ NS.κ) * t) ∧
        SupBounds (HA) (NS.Sol (z, b) p).1 (cK2' d L N (famConst d L NS.BG₂ NS.κ) * t) ∧
        (∀ δα' : (HA).Ω 1 → ℂ, Small (HA) δα' (c6' d L N (famConst d L NS.BG₂ NS.κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf (GA)) (HA) (compWeight L 1) νS p.1 false p.2.2.1 p.2.1
            (pertSource (HA) (compWeight L 1) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (NS.Sol (z, b) p).2) :=
    fun b => NS.hSol b
  have hSol' : ∀ (b : TB) (p : Dec2.DecParams (coverOf (GB)) × Edat (HB) N),
      (∀ P, ‖p.1 P‖ < Real.exp NS.κ) →
      StrictDataM (HB) N false (2 * (K4 d L N NS.BG NS.κ * (xiC1 d * t))) t p.2 →
        (NS'.Sol (bc z, b) p).1 = dphi (HB) (Dec2.decG (coverOf (GB)) (HB) (compWeight L 1) νS p.1) p.2.2.1
          p.2.1 (pertSource (HB) (compWeight L 1) p.2.2.2.1 p.2.2.2.2) (NS'.Sol (bc z, b) p).2 ∧
        Dec2.DecFixed (coverOf (GB)) (HB) (compWeight L 1) νS p.1 false p.2.2.1 p.2.1
          (pertSource (HB) (compWeight L 1) p.2.2.2.1 p.2.2.2.2) (NS'.Sol (bc z, b) p).2 ∧
        Small (HB) (NS'.Sol (bc z, b) p).2 (c6' d L N (famConst d L NS.BG₂ NS.κ) (gamma1 d / 8)) ∧
        Small (HB) (NS'.Sol (bc z, b) p).2 (cK2' d L N (famConst d L NS.BG₂ NS.κ) * t) ∧
        SupBounds (HB) (NS'.Sol (bc z, b) p).1 (cK2' d L N (famConst d L NS.BG₂ NS.κ) * t) ∧
        (∀ δα' : (HB).Ω 1 → ℂ, Small (HB) δα' (c6' d L N (famConst d L NS.BG₂ NS.κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf (GB)) (HB) (compWeight L 1) νS p.1 false p.2.2.1 p.2.1
            (pertSource (HB) (compWeight L 1) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (NS'.Sol (bc z, b) p).2) :=
    fun b => (NS'.hSol b).congr hκ hBG₂ (by rw [hκ, hBG]) rfl
  have hmain := e1MarkGParamG_twoTorus (hN2 := hN2) (hk := hk) (νS := νS) (β := β) (p₁ := p₁)
    (δ := δ) hC hC' hGA hGB hMX hmar hαK hsm hF₁ hF₁' hSol hSol' hN hN' hm₁ z hz hrc hroot hn hn'
    a b hab haR θ θ' hθ.1 hθ'.1 hraw NS.Z.hp₁ NS.hp NS'.hp Φ Φ' hΦ
    (u := (s : ℂ)) (by
      have : ‖(s : ℂ)‖ < 17 / 16 := by linarith
      exact this) (hum _ hs1)
  show e1MarkGParamG (SB) (fun b => NS'.F₁ (bc z, b)) (fun b => NS'.Sol (bc z, b)) NS'.p₁ NS'.hp
      (bc z) t θ' b (s : ℂ) Φ' =
    e1MarkGParamG (SA) (fun b => NS.F₁ (z, b)) (fun b => NS.Sol (z, b)) NS.p₁ NS.hp z t θ a (s : ℂ) Φ
  rw [e1MarkGParamG_congr_rho hp₁]
  exact hmain

/-- **The marks of the old terms of two systems agree on two tori.** -/
theorem anchor_G_inr
    (hN2 : 2 ≤ N) (hk : 1 ≤ k) (νS β p₁ δ : ℝ)
    {C : StepClass d L N₁ m₁ k N ϱ} {z : RootIdx d L N₁ m₁ (k + 1)} {t pp : ℝ} {Jr : (SA).JointRep t pp} {C' : StepClass d L N₁' m₁ k N ϱ} {pp' : ℝ} {Jr' : (SB).JointRep t pp'} (NS : NewLevelSystem (SA) C z Jr) (NS' : NewLevelSystem (SB) C' (bc z) Jr')
    (Q : NS.O.ι → NS'.O.ι → Prop)
    {R : ℕ}
    (θ : physParam N (SA)) (θ' : physParam N (SB)) (hθ : θ ∈ physV (SA) (SA).a₁ (SA).ν t) (hθ' : θ' ∈ physV (SB) (SB).a₁ (SB).ν t) (hraw : RawBoxAgree {z | InBox d (R + 3 * L ^ (k + 1)) ((N₁ * L ^ m₁) * L ^ (k + 1)) z} (θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) (θ'.1 : RawData d L (N₁' * L ^ m₁) (k + 1) N))
    (hm₀ : NS'.O.m₀ = NS.O.m₀)
    (hprem : ∀ (τ : NS.O.ι) (τ' : NS'.O.ι) (θ : physParam N (SA)) (θ' : physParam N (SB))
      (Y : Set (CTorus d L N₁ m₁ (k + 1)))
      (Φ : ∀ b, ((SA).blockSplit 1 NS.hp).Ωb b) (Φ' : ∀ b, ((SB).blockSplit 1 NS'.hp).Ωb b)
      (u t₀ : ℂ), θ ∈ physV (SA) (SA).a₁ (SA).ν t → θ' ∈ physV (SB) (SB).a₁ (SB).ν t →
      RawBoxAgree {z | InBox d (R + 3 * L ^ (k + 1)) ((N₁ * L ^ m₁) * L ^ (k + 1)) z}
        (θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) (θ'.1 : RawData d L (N₁' * L ^ m₁) (k + 1) N) →
      Q τ τ' → NS.Dom Y τ → NS'.O.jL τ' = NS.O.jL τ →
      NS'.O.X₁f τ' = (NS.O.X₁f τ).image bm → (∀ x ∈ Y, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x) →
      (∀ x, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x →
        Φ' ((SB).cellOf 1 (unitPt (SB).hG' (bm x))) ⟨unitPt (SB).hG' (bm x), rfl⟩ =
          Φ ((SA).cellOf 1 (unitPt (SA).hG' x)) ⟨unitPt (SA).hG' x, rfl⟩) →
      (‖u‖ + ‖t₀‖) * markedRad d L N k (SA).a₁ NS.O.κ NS.O.ρ
        (((SA).betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) < NS.O.δ₁ →
      TermPairPremisesAt NS NS' τ τ' θ θ' Y Φ Φ' u t₀)
    (hum : ∀ u : ℂ, ‖u‖ ≤ 1 → ‖u‖ * markedRad d L N k (SA).a₁ NS.O.κ NS.O.ρ (((SA).betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) < NS.O.δ₁)
    
    (q : {q // q ∈ markedIdx (fun _ : NS.O.ι => (Set.univ : Set (CTorus d L N₁ m₁ (k + 1)))) (fun τ => polyDom (SA).G' (NS.O.X₁f τ) NS.O.m₀ (NS.O.jL τ) (NS.O.𝒦X τ)) z}) (q' : {q // q ∈ markedIdx (fun _ : NS'.O.ι => (Set.univ : Set (CTorus d L N₁' m₁ (k + 1)))) (fun τ => polyDom (SB).G' (NS'.O.X₁f τ) NS'.O.m₀ (NS'.O.jL τ) (NS'.O.𝒦X τ)) (bc z)})
    (hq2 : q'.1.2 = bm '' q.1.2) (hYR : ∀ x ∈ q.1.2, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x)
    (hDom : NS.Dom q.1.2 q.1.1) (hj : NS'.O.jL q'.1.1 = NS.O.jL q.1.1)
    (hX : NS'.O.X₁f q'.1.1 = (NS.O.X₁f q.1.1).image bm) (hQ : Q q.1.1 q'.1.1) :
    ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ Φ Φ', (∀ x, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x → Φ' ((SB).cellOf 1 (unitPt (SB).hG' (bm x))) ⟨unitPt (SB).hG' (bm x), rfl⟩ = Φ ((SA).cellOf 1 (unitPt (SA).hG' x)) ⟨unitPt (SA).hG' x, rfl⟩) →
      (NS'.G θ') (Sum.inr q') (s : ℂ) Φ' = (NS.G θ) (Sum.inr q) (s : ℂ) Φ := by
  intro s hs Φ Φ' hΦ
  have hs1 : ‖(s : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs.1]; exact hs.2
  have hu : ‖(s : ℂ)‖ < corrU := by
    have : (corrU : ℝ) = 17 / 16 := rfl
    rw [this]; linarith
  have hmr := hum (s : ℂ) hs1
  have hev : ∀ᶠ t₀ in nhds (0 : ℂ), (‖(s : ℂ)‖ + ‖t₀‖) * markedRad d L N k (SA).a₁ NS.O.κ NS.O.ρ
      (((SA).betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) < NS.O.δ₁ := by
    have ht : Filter.Tendsto (fun t₀ : ℂ => (‖(s : ℂ)‖ + ‖t₀‖) * markedRad d L N k (SA).a₁ NS.O.κ
        NS.O.ρ (((SA).betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) (nhds 0)
        (nhds ((‖(s : ℂ)‖ + ‖(0 : ℂ)‖) * markedRad d L N k (SA).a₁ NS.O.κ NS.O.ρ
          (((SA).betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ))) :=
      ((continuous_const.add continuous_norm).mul continuous_const).tendsto 0
    exact ht.eventually_lt_const (by simpa using hmr)
  exact NS.G₁_twoTorus_at_of_pairs NS' q'.1.1 θ θ' q q' (s : ℂ) Φ Φ'
    ⟨fun _ => ⟨hθ'.1, hu⟩, fun _ => ⟨hθ.1, hu⟩⟩ rfl rfl rfl rfl rfl hq2 hX hm₀ hj
    (hev.mono fun t₀ ht => hprem q.1.1 q'.1.1 θ θ' q.1.2 Φ Φ' (s : ℂ) t₀ hθ hθ' hraw hQ hDom hj hX
      hYR hΦ ht)

end AnchorG

end Balaban.Inhabited
