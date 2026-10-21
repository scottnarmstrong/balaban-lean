/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.NewLevelCoeffPairs
public import Balaban.Inhabited.NewLevelCanonBox
public import Balaban.Inhabited.NewLevelClassPair
public import Balaban.Inhabited.NewLevelClassE

/-!
# The premises of the comparison of corresponding old terms of canonically pinned systems

`canon_hprem`: the premises `TermPairPremisesAt` of two corresponding old terms (`termPairPremisesAt_of_data`),
with the agreement of the old terms on the margin from `oldTerm_E_agree` (the torus independence of the
small-field terms away from the distinguished cell and the cell case `hcellcase` of the geometry data) and
the geometry of the canonical covers (`hgeom`).
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation
  Balaban.Localization Balaban.Localization.LevelPair Balaban.Localization.I5Inhabited
  Balaban.Polymer Balaban.SmallField.Def6 Balaban.Inhabited.LevelStep
  Balaban.Inhabited.MarkBudgetAudit Matrix Metric Set MeasureTheory Balaban.Polymer.TwoTorusStep
  Balaban.SmallField.Def6v2

section ClassCoeff

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

attribute [local irreducible] NewLevelSystem.Dom

/-- **The premises of the comparison of corresponding old terms of two canonically pinned
systems.** -/
theorem canon_hprem
    (hN2 : 2 ≤ N) (hk : 1 ≤ k) (νS β p₁ δ : ℝ)
    {C : StepClass d L N₁ m₁ k N ϱ} {z : RootIdx d L N₁ m₁ (k + 1)} {t pp : ℝ} {Jr : (SA).JointRep t pp} {C' : StepClass d L N₁' m₁ k N ϱ} {pp' : ℝ} {Jr' : (SB).JointRep t pp'} (NS : NewLevelSystem (SA) C z Jr) (NS' : NewLevelSystem (SB) C' (bc z) Jr')
    {i₀ i₁ : Fin N}
    {F : CanonCover d L N₁ m₁ k ϱ NS.O.ϱ₁} {F' : CanonCover d L N₁' m₁ k ϱ NS'.O.ϱ₁}
    {y : NS.O.ι → CTorus d L N₁ m₁ (k + 1)} {X : NS.O.ι → Set (CTorus d L N₁ m₁ (k + 1))}
    {y' : NS'.O.ι → CTorus d L N₁' m₁ (k + 1)} {X' : NS'.O.ι → Set (CTorus d L N₁' m₁ (k + 1))}
    (hB : Set.BijOn (fun τ => (NS.O.jL τ, y τ, X τ)) Set.univ (AdmPairs L N₁ m₁ k d C.m₀ k))
    (hX₁ : ∀ τ, NS.O.X₁f τ = F.X₁fC (NS.O.jL τ) (y τ) (X τ))
    (hm₀ : NS.O.m₀ = C.m₀) (hm₀' : NS'.O.m₀ = C'.m₀) (hC : C'.m₀ = C.m₀)
    (hEτ : ∀ τ r, NS.O.Eτ τ r = irrelTorus C.m₀ C.Tm i₀ i₁ (NS.O.jL τ) (y τ) (X τ) r.1 r.2)
    (hEτ' : ∀ τ r, NS'.O.Eτ τ r = irrelTorus C'.m₀ C'.Tm i₀ i₁ (NS'.O.jL τ) (y' τ) (X' τ) r.1 r.2)
    (hGk : ∀ τ, NS.O.Gk τ = F.GkC (NS.O.jL τ) (y τ) (X τ))
    (hGk' : ∀ τ, NS'.O.Gk τ = F'.GkC (NS'.O.jL τ) (y' τ) (X' τ))
    (hGj : ∀ τ, NS.O.Gj τ = F.GjC (NS.O.jL τ) (y τ) (X τ))
    (hGj' : ∀ τ, NS'.O.Gj τ = F'.GjC (NS'.O.jL τ) (y' τ) (X' τ))
    (hcX : ∀ j y₀ X₀, (j, y₀, X₀) ∈ AdmPairs L N₁ m₁ k d C.m₀ k → insert y₀ X₀ ⊆ ↑(F.X₁fC j y₀ X₀))
    {Tm : ∀ (M : ℕ) [NeZero M], Terms d L M m₁ (k + 1) N ϱ} (hCT : C.Tm = Tm N₁)
    (hCT' : C'.Tm = Tm N₁') (hTI : TorusIndep C.m₀ Tm)
    (hlocB : ∀ j y X Ψ Ψ' h h', (∀ x ∈ X, Ψ x = Ψ' x ∧ h x = h' x) →
      (Tm N₁').E j y X Ψ h = (Tm N₁').E j y X Ψ' h')
    (hM8 : 8 ≤ L ^ (C.m₀ + m₁))
    {R : ℕ}
    (hgeom : ∀ j y₀ X₀, (j, y₀, X₀) ∈ AdmPairs L N₁ m₁ k d C.m₀ k →
      (∀ x ∈ insert y₀ X₀, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x) →
      (∀ μ : Fin d, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1))
        (y₀ + (L ^ j) • (Pi.single μ 1 : CTorus d L N₁ m₁ (k + 1)))) ∧
      (∀ z ∈ box (cbase (cellSide L C.m₀ m₁ j) y₀ - natT (fun _ => L / 2 * cellSide L C.m₀ m₁ j)) (L * cellSide L C.m₀ m₁ j), InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) z) ∧
      ∃ Z : Set (CTorus d L N₁ m₁ (k + 1)), X₀ ⊆ Z ∧
        (∀ μ : Fin d, y₀ + (L ^ j) • (Pi.single μ 1 : CTorus d L N₁ m₁ (k + 1)) ∈ Z) ∧
        Z ⊆ ↑(F.X₁fC j y₀ X₀) ∧ BlockMargin (SA).G' (F.X₁fC j y₀ X₀) Z ∧
        GSCorr (F.GkC j y₀ X₀) (F'.GkC j (bm y₀) (bm '' X₀)) bm Z ∧
        GSCorr (F.GjC j y₀ X₀) (F'.GjC j (bm y₀) (bm '' X₀)) bm Z ∧
        GSIso (compWeight L (SA).a₁) (SA).ν (F.GkC j y₀ X₀) (F'.GkC j (bm y₀) (bm '' X₀)) bm Z ∧
        (∀ z ∈ Z, z ∈ (F.GkC j y₀ X₀).Ω 1 →
          (∀ y ∈ (F.GkC j y₀ X₀).blk ((F.GkC j y₀ X₀).layerIndex z) z, y ∈ Z) ∧
          (∀ y ∈ (SA).G'.blk ((SA).G'.layerIndex z) z, y ∈ Z) ∧
          (∀ y ∈ (stepG d L N₁ m₁ k ϱ).blk ((stepG d L N₁ m₁ k ϱ).layerIndex z) z, y ∈ Z)) ∧
        (∀ z ∈ Z, z ∈ (F.GjC j y₀ X₀).Ω 1 →
          (∀ y ∈ (F.GjC j y₀ X₀).blk ((F.GjC j y₀ X₀).layerIndex z) z, y ∈ Z) ∧
          (∀ y ∈ (F.GkC j y₀ X₀).blk ((F.GkC j y₀ X₀).layerIndex z) z, y ∈ Z)) ∧
        (X₀ = box (cbase (cellSide L C.m₀ m₁ j) y₀ - natT (fun _ => L / 2 * cellSide L C.m₀ m₁ j)) (L * cellSide L C.m₀ m₁ j) →
          ∀ (r : RawData d L (N₁ * L ^ m₁) (k + 1) N) (r' : RawData d L (N₁' * L ^ m₁) (k + 1) N),
            (∀ z ∈ Z, r.1 z = r'.1 (bm z) ∧ r.2 z = r'.2 (bm z)) →
            irrelTorus C'.m₀ C'.Tm i₀ i₁ j (bm y₀) (bm '' X₀) r'.1 r'.2 =
              irrelTorus C.m₀ C.Tm i₀ i₁ j y₀ X₀ r.1 r.2))
    {K : NewLevelConsts} (hK : NS.HasConsts K) (hK' : NS'.HasConsts K)
    {δc : ℝ} (hMX : cstarX d L * Real.exp (N0 d L * NS.O.κ) ≤ (L : ℝ) ^ m₁)
    (hmar : decDomMargin d L N NS.O.BG NS.O.κ (xiC1 d * t) < δc)
    (hαK : K4 d L N NS.O.BG NS.O.κ * (xiC1 d * t) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L NS.O.κ ≤ 1 / 4) (hρ : 0 < NS.O.ρ)
    (hΦan : ∀ τ, AnalyticOnNhd ℂ (fun t' => (eTermFun (SA).G' (NS.O.Gk τ) (NS.O.Gj τ)
      (stepG d L N₁ m₁ k ϱ) (compWeight L (SA).a₁) (NS.O.FkL τ)
      (fun r => ((SA).β : ℂ)⁻¹ * NS.O.Eτ τ r)) t'.1 t'.2.1 t'.2.2)
      (FlReal (SA).G' (stepG d L N₁ m₁ k ϱ) (SA).a₁ (SA).ν NS.O.BG NS.O.κ t (NS.O.X₁f τ)
        NS.O.BG₂ NS.O.δ₁))
    (hm₁ : 1 ≤ m₁)
    (hn19 : 4 * R + 19 * L ^ (k + 2 + NS.O.m₀ + m₁) + 5 < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hn19' : 4 * R + 19 * L ^ (k + 2 + NS.O.m₀ + m₁) + 5 < (N₁' * L ^ m₁) * L ^ (k + 1))
    (hm₀N : NS'.O.m₀ = NS.O.m₀)
    (hmE₁ : 8 * R + 3 * L ^ (k + 1) + L * cellSide L C.m₀ m₁ (k + 1) < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hmE₂ : 8 * R + 3 * L ^ (k + 1) + L * cellSide L C.m₀ m₁ (k + 1) < (N₁' * L ^ m₁) * L ^ (k + 1))
    {rc : ℕ} (hz : InBox d rc (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) z)
    (hrc : L ^ (k + 1) * rc ≤ R)
    (hGA : IsLevel (GA) (k + 1)) (hGB : IsLevel (GB) (k + 1)) :
    ∀ (τ : NS.O.ι) (τ' : NS'.O.ι) (θ : physParam N (SA)) (θ' : physParam N (SB))
      (Y : Set (CTorus d L N₁ m₁ (k + 1)))
      (Φ : ∀ b, ((SA).blockSplit 1 NS.hp).Ωb b) (Φ' : ∀ b, ((SB).blockSplit 1 NS'.hp).Ωb b)
      (u t₀ : ℂ), θ ∈ physV (SA) (SA).a₁ (SA).ν t → θ' ∈ physV (SB) (SB).a₁ (SB).ν t →
      RawBoxAgree {z | InBox d (R + 3 * L ^ (k + 1)) ((N₁ * L ^ m₁) * L ^ (k + 1)) z}
        (θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) (θ'.1 : RawData d L (N₁' * L ^ m₁) (k + 1) N) →
      (y' τ' = bm (y τ) ∧ X' τ' = bm '' X τ) → NS.Dom Y τ → NS'.O.jL τ' = NS.O.jL τ →
      NS'.O.X₁f τ' = (NS.O.X₁f τ).image bm → (∀ x ∈ Y, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x) →
      (∀ x, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x → Φ' ((SB).cellOf 1 (unitPt (SB).hG' (bm x))) ⟨unitPt (SB).hG' (bm x), rfl⟩ = Φ ((SA).cellOf 1 (unitPt (SA).hG' x)) ⟨unitPt (SA).hG' x, rfl⟩) →
      (‖u‖ + ‖t₀‖) * markedRad d L N k (SA).a₁ NS.O.κ NS.O.ρ
        (((SA).betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) < NS.O.δ₁ →
      TermPairPremisesAt NS NS' τ τ' θ θ' Y Φ Φ' u t₀ := by
  classical
  intro τ τ' θ θ' Y Φ Φ' u t₀ hθ hθ' hraw hQ hDom hj hX hYR hΦ hum
  obtain ⟨hy', hX'⟩ := hQ
  obtain ⟨⟨hn1, hnS, hnF, hnH, hnM⟩, ⟨hn1', hnS', hnF', hnH', hnM'⟩⟩ :=
    twoTorus_margins_of_lt_min (R := R) (k := k) (m₀ := NS.O.m₀) (m₁ := m₁) hm₁ (lt_min hn19 hn19')
  have hadm := hB.mapsTo (Set.mem_univ τ)
  have hbox : ∀ x ∈ insert (y τ) (X τ), InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x :=
    insert_subset_box_of_dom NS hB hX₁ hcX hYR hDom
  obtain ⟨hstep, hcell, Z, hZX, hZs, hZcov, hBMZ, hGkc, hGjc, hisoc, hblkc, hblk2c, hcellc⟩ :=
    hgeom _ _ _ hadm hbox
  obtain ⟨hj1, hjk, hal, hpoly, hyX⟩ := hadm
  have hGkτ : NS.O.Gk τ = F.GkC (NS.O.jL τ) (y τ) (X τ) := hGk τ
  have hGjτ : NS.O.Gj τ = F.GjC (NS.O.jL τ) (y τ) (X τ) := hGj τ
  have hGk'τ : NS'.O.Gk τ' = F'.GkC (NS.O.jL τ) (bm (y τ)) (bm '' X τ) := by
    rw [hGk' τ', hj, hy', hX']
  have hGj'τ : NS'.O.Gj τ' = F'.GjC (NS.O.jL τ) (bm (y τ)) (bm '' X τ) := by
    rw [hGj' τ', hj, hy', hX']
  have hN₁ : L ^ C.m₀ ∣ N₁ := by have := NS.OS.hN; rwa [hm₀] at this
  have hN₂ : L ^ C.m₀ ∣ N₁' := by have := NS'.OS.hN; rwa [hm₀', hC] at this
  have hcsj : L * cellSide L C.m₀ m₁ (NS.O.jL τ) ≤ L * cellSide L C.m₀ m₁ (k + 1) :=
    Nat.mul_le_mul_left L (cellSide_le_of_le (by omega))
  have hEval := oldTerm_E_agree NS.O NS'.O hCT hCT' hC hTI hlocB rfl hEτ hEτ' τ τ' hy' hX' hj
    hj1 (by omega) hN₁ hN₂ hM8 (R := R) (by omega) (by omega) hal hyX hpoly
    (fun x hx => hbox x (Set.mem_insert_of_mem _ hx)) hstep hcell hZX hZs
    (fun hc => by rw [hj, hy', hX']; exact hcellc hc)
  have hZm : ∀ x, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x →
      (unitPt (SB).hG' (bm x) ∈ (SB).blockU (bc z) ↔ unitPt (SA).hG' x ∈ (SA).blockU z) := by
    intro x hx
    have h := rootMask_bc (N₁' := N₁') hnM hnM' hGA hGB z hz hrc hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h
    exact (mem_blockU_iff_unitBlock1 (SB) _ _).trans
      (h.trans (mem_blockU_iff_unitBlock1 (SA) _ _).symm)
  have hX₁R : ∀ x ∈ NS.O.X₁f τ, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x := fun x hx =>
    hYR x (x1f_subset_of_mem_polyDom (NS.OS.hX₁ τ) ((NS.dom_iff _ _).1 hDom) (Finset.mem_coe.2 hx))
  exact termPairPremisesAt_of_data (hN2 := hN2) (hk := hk) (νS := νS) (β := β) (p₁ := p₁) (δ := δ) (NS := NS) (NS' := NS') (τ := τ) (τ' := τ') (θ := θ) (θ' := θ') (Y := Y) (Φ := Φ) (Φ' := Φ') (u := u) (t₀ := t₀) (hK := hK) (hK' := hK') (ht := rfl) (hX := hX) (hm₀ := hm₀N) (hj := hj) (hθ := hθ) (hθ' := hθ') (hZX := (by rw [hX₁ τ]; exact hZcov)) (hBMZ := (by rw [hX₁ τ]; exact hBMZ)) (hGk := (by rw [hGkτ, hGk'τ]; exact hGkc)) (hGj := (by rw [hGjτ, hGj'τ]; exact hGjc)) (hiso := (by rw [hGkτ, hGk'τ]; exact hisoc)) (hblk := (by rw [hGkτ]; exact hblkc)) (hblk2 := (by rw [hGjτ, hGkτ]; exact hblk2c)) (hE := hEval) (hX₁R := hX₁R) (hYR := hYR) (hn := hn1) (hn' := hn1') (hnS := hnS) (hnS' := hnS') (hnF := hnF) (hnF' := hnF') (hΦan := hΦan τ) (hraw := hraw) (hR := hΦ) (hZm := hZm) (hMX := hMX) (hmar := hmar) (hαK := hαK) (hsm := hsm) (hρ := hρ) (hum := hum)

end ClassCoeff

end Balaban.Inhabited
