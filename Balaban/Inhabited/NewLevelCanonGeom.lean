/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.NewLevelCanonLocal
public import Balaban.Inhabited.NewLevelCanonMargin

/-!
# `HGeom` for canonical covers built from local generating sets

`hgeom_of_local`.  The cover requirement is the hypothesis `hX1`: the region `X₁` of a pair contains the
neighbourhood of the cell of every site within `zRad` of the polymer, the neighbours of `y₀` and the
polymers of `Gk`, `Gj`.
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation
  Balaban.Localization Balaban.Localization.LocalCover Balaban.Polymer Balaban.SmallField.Def6
  Balaban.Polymer.TwoTorusStep Balaban.SmallField.Def6v2 Balaban.SmallField.GsSpec
  Balaban.LargeField

section Geom

variable {d L N₁ N₁' m₁ k N : ℕ} [NeZero N₁] [NeZero N₁'] [NeZero L] {ϱ ϱ₁ ϱ₁' ϱ' ϱ'' : ℝ}

set_option hygiene false in
local notation "bm" => boxMap ((N₁ * L ^ m₁) * L ^ (k + 1)) ((N₁' * L ^ m₁) * L ^ (k + 1))

/-- `GSCorr` of local generating sets on a set inside the box. -/
theorem gsCorr_local {n : ℕ} (hn : n ≤ k + 1) {P : Set (CTorus d L N₁ m₁ (k + 1))}
    {P' : Set (CTorus d L N₁' m₁ (k + 1))} {hs : ϱ' ≤ minSep L (L ^ m₁)}
    {hs' : ϱ'' ≤ minSep L (L ^ m₁)} {R : ℕ}
    (hP : ∀ x ∈ P, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x) (hPP : P' = bm '' P)
    (hbig : 2 * (R + 1 + 6 * (k + 1) * L ^ (k + 1 + m₁) + (5 * L + 2) * L ^ (k + 1 + m₁) +
      L ^ (k + 1)) + 3 * L ^ (k + 1) + 5 < N₁ * L ^ m₁ * L ^ (k + 1))
    (hbig' : 2 * (R + 1 + 6 * (k + 1) * L ^ (k + 1 + m₁) + (5 * L + 2) * L ^ (k + 1 + m₁) +
      L ^ (k + 1)) + 3 * L ^ (k + 1) + 5 < N₁' * L ^ m₁ * L ^ (k + 1))
    {Z : Set (CTorus d L N₁ m₁ (k + 1))}
    (hZ : ∀ z ∈ Z, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) z) :
    GSCorr (localB n hn P hs) (localB n hn P' hs') bm Z := by
  obtain ⟨a1, a2⟩ := margins_of_big (m₁ := m₁) (R := R) hn hbig
  obtain ⟨b1, b2⟩ := margins_of_big (m₁ := m₁) (R := R) hn hbig'
  exact (gsCorr_localB (k := k + 1) hn (by omega) hP hPP a1 b1 a2 b2).mono
    fun z hz => inBox_mono (by omega) (hZ z hz)

/-- The data sites of a local generating set of a polymer in the set of points `Pt` lie within `zRad`
of `Pt`. -/
theorem dataSite_mem_nearSet {n : ℕ} (hn : n ≤ k + 1) (hL : 2 ≤ L)
    {P Pt : Set (CTorus d L N₁ m₁ (k + 1))} (hPPt : P ⊆ Pt) {hs : ϱ' ≤ minSep L (L ^ m₁)}
    {x : CTorus d L N₁ m₁ (k + 1)} (hx : x ∈ dataSites (localB n hn P hs)) :
    x ∈ nearSet (zRad L m₁ k) Pt := by
  obtain ⟨y, hy, hd⟩ := localB_dataSites_range hL hx
  refine ⟨y, hPPt hy, hd.trans ?_⟩
  have hLp : 0 < L := by omega
  have : L ^ m₁ * L ^ n ≤ L ^ (m₁ + (k + 1)) := by
    rw [← pow_add]; exact Nat.pow_le_pow_right hLp (by omega)
  unfold zRad
  have h2 : 11 * L ^ m₁ * L ^ n ≤ 11 * L ^ (m₁ + (k + 1)) := by nlinarith
  omega

/-- **The blocks (of side at most `L^{k+1}`) of a site of the margin lie in the margin.** -/
theorem blk_subset_canonZ {Pt : Set (CTorus d L N₁ m₁ (k + 1))} {r : ℕ} {ϱ' : ℝ}
    (G : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ') {n : ℕ} (hn : n ≤ k + 1)
    {z y : CTorus d L N₁ m₁ (k + 1)}
    (hz : z ∈ {y | ∃ x ∈ nearSet r Pt, SameCell (L ^ (k + 1)) y x})
    (hy : y ∈ G.blk n z) : y ∈ {y | ∃ x ∈ nearSet r Pt, SameCell (L ^ (k + 1)) y x} := by
  obtain ⟨x, hx, hzx⟩ := hz
  have hsc : SameCell (L ^ n) y z := sameCell_of_jBlock_eq hn (GeneratingSet.mem_blk.1 hy)
  exact ⟨x, hx, (SameCell.mono (pow_dvd_pow L hn) hsc).trans hzx⟩

/-- **`HGeom` for canonical covers built from local generating sets.**  The margin is the set of sites
within `zRad + L^{k+1}` of the polymer, its neighbours and the polymers of `Gk`, `Gj`; the cover
requirement `hmarg` is that the `6 M`-neighbourhood of the margin lies in the region `X₁`
(`M = L^{k+1+m₁}`), and `hcb` that `X₁` contains the cell box of `y₀`. -/
theorem hgeom_of_local {S : StepSetting d L N₁ m₁ k N ϱ} {C : StepClass d L N₁ m₁ k N ϱ}
    {C' : StepClass d L N₁' m₁ k N ϱ} {F : CanonCover d L N₁ m₁ k ϱ ϱ₁}
    {F' : CanonCover d L N₁' m₁ k ϱ ϱ₁'} (LC : CanonCoverLocal F F') {i₀ i₁ : Fin N} {R : ℕ}
    (hL : 2 ≤ L) (SpG : DGSetting S.G' (compWeight L S.a₁) S.ν)
    (hbig : 2 * (R + 1 + 6 * (k + 1) * L ^ (k + 1 + m₁) + (5 * L + 2) * L ^ (k + 1 + m₁) +
      L ^ (k + 1)) + 3 * L ^ (k + 1) + 5 < N₁ * L ^ m₁ * L ^ (k + 1))
    (hbig' : 2 * (R + 1 + 6 * (k + 1) * L ^ (k + 1 + m₁) + (5 * L + 2) * L ^ (k + 1 + m₁) +
      L ^ (k + 1)) + 3 * L ^ (k + 1) + 5 < N₁' * L ^ m₁ * L ^ (k + 1))
    (hmarg : ∀ j y₀ X₀, (j, y₀, X₀) ∈ AdmPairs L N₁ m₁ k d C.m₀ k →
      ∀ x ∈ canonZ LC j y₀ X₀, ∀ w : Fin d → ℤ,
        (∀ μ, |(w μ : ℝ)| < 6 * (L : ℝ) ^ ((k + 1) + m₁)) →
        x + (intTorus w : CTorus d L N₁ m₁ (k + 1)) ∈
          (↑(F.X₁fC j y₀ X₀) : Set (CTorus d L N₁ m₁ (k + 1))))
    (hcb : ∀ j y₀ X₀, (j, y₀, X₀) ∈ AdmPairs L N₁ m₁ k d C.m₀ k →
      Localization.box (cbase (cellSide L C.m₀ m₁ j) y₀ - natT (fun _ => L / 2 * cellSide L C.m₀ m₁ j))
        (L * cellSide L C.m₀ m₁ j) ⊆ (↑(F.X₁fC j y₀ X₀) : Set (CTorus d L N₁ m₁ (k + 1))))
    (hPK : ∀ j y₀ X₀, (j, y₀, X₀) ∈ AdmPairs L N₁ m₁ k d C.m₀ k →
      (∀ x ∈ (↑(F.X₁fC j y₀ X₀) : Set (CTorus d L N₁ m₁ (k + 1))),
        InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x) →
      LC.PK' j (bm y₀) (bm '' X₀) = bm '' LC.PK j y₀ X₀)
    (hPJ : ∀ j y₀ X₀, (j, y₀, X₀) ∈ AdmPairs L N₁ m₁ k d C.m₀ k →
      (∀ x ∈ (↑(F.X₁fC j y₀ X₀) : Set (CTorus d L N₁ m₁ (k + 1))),
        InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x) →
      LC.PJ' j (bm y₀) (bm '' X₀) = bm '' LC.PJ j y₀ X₀)
    (hcell : ∀ j y₀ X₀, (j, y₀, X₀) ∈ AdmPairs L N₁ m₁ k d C.m₀ k →
      (∀ x ∈ (↑(F.X₁fC j y₀ X₀) : Set (CTorus d L N₁ m₁ (k + 1))),
        InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x) →
      CellTermsAgree C C' i₀ i₁ j y₀ X₀ (canonZ LC j y₀ X₀)) :
    HGeom S C C' F F' i₀ i₁ R := by
  classical
  intro j y₀ X₀ hadm hbox
  have hsub : ∀ w ∈ canonPts LC j y₀ X₀, w ∈ canonZ LC j y₀ X₀ := fun w hw =>
    ⟨w, ⟨w, hw, by simp [supDist_self]⟩, SameCell.refl _ _⟩
  have hZX : canonZ LC j y₀ X₀ ⊆ ↑(F.X₁fC j y₀ X₀) := fun x hx => by
    have h0 : (intTorus (0 : Fin d → ℤ) : CTorus d L N₁ m₁ (k + 1)) = 0 := by
      funext μ; simp [intTorus_apply]
    have := hmarg j y₀ X₀ hadm x hx 0 (fun μ => by simp; positivity)
    rwa [h0, add_zero] at this
  have hZbox : ∀ z ∈ canonZ LC j y₀ X₀, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) z :=
    fun z hz => hbox z (hZX hz)
  have hnb : ∀ μ : Fin d, y₀ + (L ^ j) • (Pi.single μ 1 : CTorus d L N₁ m₁ (k + 1)) ∈
      canonPts LC j y₀ X₀ := fun μ => Or.inl (Or.inl (Or.inr ⟨μ, rfl⟩))
  have hPKs : LC.PK j y₀ X₀ ⊆ canonPts LC j y₀ X₀ := fun x hx => Or.inl (Or.inr hx)
  have hPJs : LC.PJ j y₀ X₀ ⊆ canonPts LC j y₀ X₀ := fun x hx => Or.inr hx
  have hPKb := hPK j y₀ X₀ hadm hbox
  have hPJb := hPJ j y₀ X₀ hadm hbox
  have hmono : ∀ x, x ∈ nearSet (zRad L m₁ k) (canonPts LC j y₀ X₀) → x ∈ canonZ LC j y₀ X₀ :=
    fun x hx => ⟨x, hx, SameCell.refl _ _⟩
  refine ⟨fun μ => hZbox _ (hsub _ (hnb μ)), fun z hz => hbox z (hcb j y₀ X₀ hadm hz),
    canonZ LC j y₀ X₀,
    fun x hx => hsub x (Or.inl (Or.inl (Or.inl (Set.mem_insert_of_mem _ hx)))),
    fun μ => hsub _ (hnb μ), hZX,
    blockMargin_core SpG S.hG' _ (hmarg j y₀ X₀ hadm), ?_, ?_, ?_, ?_, ?_,
    hcell j y₀ X₀ hadm hbox⟩
  · rw [LC.hGk j y₀ X₀, LC.hGk' j (bm y₀) (bm '' X₀), hPKb]
    exact gsCorr_local (LC.hnK j) (fun x hx => hZbox x (hsub x (hPKs hx))) rfl hbig hbig' hZbox
  · rw [LC.hGj j y₀ X₀, LC.hGj' j (bm y₀) (bm '' X₀), hPJb]
    exact gsCorr_local (LC.hnJ j) (fun x hx => hZbox x (hsub x (hPJs hx))) rfl hbig hbig' hZbox
  · rw [LC.hGk j y₀ X₀, LC.hGk' j (bm y₀) (bm '' X₀), hPKb]
    obtain ⟨a1, a2⟩ := margins_of_big (m₁ := m₁) (R := R) (LC.hnK j) hbig
    obtain ⟨b1, b2⟩ := margins_of_big (m₁ := m₁) (R := R) (LC.hnK j) hbig'
    refine gsIso_localB_on (k := k + 1) (LC.hnK j) (by omega)
      (fun x hx => hZbox x (hsub x (hPKs hx))) rfl
      (fun n' hn' => by have := a1 n' hn'; omega) (fun n' hn' => by have := b1 n' hn'; omega)
      (by omega) (by omega) _ _ _ fun x hx => ?_
    have hd : ∀ x', x' ∈ dataSites (localB (LC.nK j) (LC.hnK j) (LC.PK j y₀ X₀) LC.hsepK) →
        x' ∈ canonZ LC j y₀ X₀ := fun x' h =>
      hmono _ (dataSite_mem_nearSet (LC.hnK j) hL hPKs h)
    refine ⟨hd x ((mem_dataSites _).2 (Or.inl hx)), fun μ => ⟨hd _ ?_, hd _ ?_⟩⟩
    · by_cases h : x + Pi.single μ 1 ∈ (localB (LC.nK j) (LC.hnK j) (LC.PK j y₀ X₀) LC.hsepK).Ω 1
      · exact (mem_dataSites _).2 (Or.inl h)
      · exact (mem_dataSites _).2 (Or.inr (mem_collar_of_adj _ hx h ⟨μ, Or.inl rfl⟩))
    · by_cases h : x - Pi.single μ 1 ∈ (localB (LC.nK j) (LC.hnK j) (LC.PK j y₀ X₀) LC.hsepK).Ω 1
      · exact (mem_dataSites _).2 (Or.inl h)
      · exact (mem_dataSites _).2
          (Or.inr (mem_collar_of_adj _ hx h ⟨μ, Or.inr (sub_add_cancel _ _).symm⟩))
  · intro z hz _
    exact ⟨fun y hy => blk_subset_canonZ _ (layerIndex_le_top _ _) hz hy,
      fun y hy => blk_subset_canonZ _ (layerIndex_le_top _ _) hz hy,
      fun y hy => blk_subset_canonZ _ (layerIndex_le_top _ _) hz hy⟩
  · intro z hz _
    exact ⟨fun y hy => blk_subset_canonZ _ (layerIndex_le_top _ _) hz hy,
      fun y hy => blk_subset_canonZ _ (layerIndex_le_top _ _) hz hy⟩

end Geom

end Balaban.Inhabited
