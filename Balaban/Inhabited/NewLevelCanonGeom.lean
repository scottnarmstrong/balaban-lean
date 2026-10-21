/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.NewLevelCanonLocal
public import Balaban.Inhabited.NewLevelCanonMargin
public import Balaban.Inhabited.NewLevelCanonX1

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

theorem supDist_nsmul_single (a : ℕ) (y : CTorus d L N₁ m₁ (k + 1)) (μ : Fin d) :
    supDist (y + a • (Pi.single μ 1 : CTorus d L N₁ m₁ (k + 1))) y ≤ a := by
  rw [supDist_le_iff]
  intro ν
  rw [cycNorm_le_iff]
  refine ⟨if ν = μ then (a : ℤ) else 0, ?_, ?_⟩
  · split_ifs <;> simp
  · by_cases h : ν = μ <;> simp [h]

/-- **The `6 M`-neighbourhood of the margin lies in the region** (numeric tie `18 ≤ (L-2) L^{m₀}`,
`1 ≤ m₁`, `3 ≤ L`, `1 ≤ k`), from the region containing the `(L-2)`-cell neighbourhood of the polymer. -/
theorem margin_in_region {m₀ : ℕ} {F : CanonCover d L N₁ m₁ k ϱ ϱ₁}
    {F' : CanonCover d L N₁' m₁ k ϱ ϱ₁'} (LC : CanonCoverLocal m₀ F F') (hL : 3 ≤ L)
    (hm₁ : 1 ≤ m₁) (htie : 18 ≤ (L - 2) * L ^ m₀) {j : ℕ} {y₀ : CTorus d L N₁ m₁ (k + 1)}
    {X₀ : Set (CTorus d L N₁ m₁ (k + 1))} {Xr : Set (CTorus d L N₁ m₁ (k + 1))}
    (hfar : ∀ p ∈ canonPts LC j y₀ X₀, ∀ v : Fin d → ℤ,
      (∀ μ, |v μ| ≤ (((L - 2) * cellSide L m₀ m₁ (k + 1) : ℕ) : ℤ)) →
      p + (intTorus v : CTorus d L N₁ m₁ (k + 1)) ∈ Xr)
    {x : CTorus d L N₁ m₁ (k + 1)} (hx : x ∈ canonZ LC j y₀ X₀) (w : Fin d → ℤ)
    (hw : ∀ μ, |(w μ : ℝ)| < 6 * (L : ℝ) ^ ((k + 1) + m₁)) :
    x + (intTorus w : CTorus d L N₁ m₁ (k + 1)) ∈ Xr := by
  obtain ⟨x', ⟨pt, hpt, hd⟩, hsc⟩ := hx
  have hLp : 0 < L ^ (k + 1) := pow_pos (by omega) _
  have h1 := supDist_sameCell hLp hsc
  have h2 : supDist x pt ≤ zRad L m₁ k + L ^ (k + 1) :=
    (supDist_triangle x x' pt).trans (by omega)
  obtain ⟨u, hxu, hu⟩ := exists_int_of_supDist h2
  have e : x + (intTorus w : CTorus d L N₁ m₁ (k + 1)) =
      pt + (intTorus (u + w) : CTorus d L N₁ m₁ (k + 1)) := by
    rw [hxu]; funext μ; simp only [Pi.add_apply, intTorus_apply]; push_cast; ring
  rw [e]
  refine hfar pt hpt _ fun μ => ?_
  -- the integer arithmetic
  set M := L ^ ((k + 1) + m₁) with hM
  have hwM : |w μ| ≤ 6 * (M : ℤ) := by
    have := hw μ
    have h3 : |w μ| < (6 * M : ℕ) := by
      have : ((|w μ| : ℤ) : ℝ) < ((6 * M : ℕ) : ℝ) := by
        rw [Int.cast_abs]; push_cast; exact_mod_cast this
      exact_mod_cast this
    push_cast at h3; linarith
  have hr : (zRad L m₁ k + L ^ (k + 1) : ℕ) ≤ 12 * M := by
    have hA : 3 ≤ L ^ (k + 1) := by
      calc 3 ≤ L := hL
        _ = L ^ 1 := (pow_one _).symm
        _ ≤ L ^ (k + 1) := Nat.pow_le_pow_right (by omega) (by omega)
    have hLm : L ≤ L ^ m₁ := by
      calc L = L ^ 1 := (pow_one _).symm
        _ ≤ L ^ m₁ := Nat.pow_le_pow_right (by omega) hm₁
    have hMA : L * L ^ (k + 1) ≤ M := by
      calc L * L ^ (k + 1) ≤ L ^ m₁ * L ^ (k + 1) := Nat.mul_le_mul_right _ hLm
        _ = M := by rw [hM, pow_add]; ring
    have hz : zRad L m₁ k = 11 * M + 2 := by
      unfold zRad; rw [hM]; ring_nf
    rw [hz]
    nlinarith
  have hcs : cellSide L m₀ m₁ (k + 1) = L ^ m₀ * M := by
    unfold cellSide; rw [hM, ← pow_add]; congr 1; omega
  have h5 : (zRad L m₁ k + L ^ (k + 1)) + 6 * M ≤ (L - 2) * cellSide L m₀ m₁ (k + 1) := by
    rw [hcs]
    have : 18 * M ≤ (L - 2) * L ^ m₀ * M := Nat.mul_le_mul_right _ htie
    have h4 : (L - 2) * (L ^ m₀ * M) = (L - 2) * L ^ m₀ * M := by ring
    rw [h4]; omega
  have h6 : (((zRad L m₁ k + L ^ (k + 1)) + 6 * M : ℕ) : ℤ) ≤
      (((L - 2) * cellSide L m₀ m₁ (k + 1) : ℕ) : ℤ) := by exact_mod_cast h5
  have hu' := hu μ
  push_cast at hu'
  simp only [Pi.add_apply]
  have h7 := abs_add_le (u μ) (w μ)
  generalize (((L - 2) * cellSide L m₀ m₁ (k + 1) : ℕ) : ℤ) = Q at h6 ⊢
  push_cast at h6
  have h8 : |(u + w) μ| ≤ |u μ| + |w μ| := by simpa using h7
  simp only [Pi.add_apply] at h8
  linarith

/-- **The region contains the `(L-2)`-cell neighbourhood of the polymer** (`X1_far`). -/
theorem hfar_of_isX1 {S : StepSetting d L N₁ m₁ k N ϱ} {C : StepClass d L N₁ m₁ k N ϱ}
    {F : CanonCover d L N₁ m₁ k ϱ ϱ₁} (hF : CanonCoverIsX1 S C F) (hL : 2 ≤ L)
    (hN : L ^ C.m₀ ∣ N₁) :
    ∀ j y₀ X₀, (j, y₀, X₀) ∈ AdmPairs L N₁ m₁ k d C.m₀ k →
      ∀ p ∈ polySet C.m₀ j y₀ X₀, ∀ v : Fin d → ℤ,
        (∀ μ, |v μ| ≤ (((L - 2) * cellSide L C.m₀ m₁ (k + 1) : ℕ) : ℤ)) →
        p + (intTorus v : CTorus d L N₁ m₁ (k + 1)) ∈
          (↑(F.X₁fC j y₀ X₀) : Set (CTorus d L N₁ m₁ (k + 1))) := by
  intro j y₀ X₀ hadm p hp v hv
  obtain ⟨𝒦, hch, hX⟩ := hF j y₀ X₀ hadm
  rw [hX]
  exact X1_far S.hG' hN (by have := hadm.2.1; omega) hL hch hp v hv

/-- **`HGeom` for canonical covers built from local generating sets.**  The margin is the union of the
`L^{k+1}`-cells of the sites within `zRad` of the polymer `X ∪ □(y)` of the term, its polymers of `Gk`,
`Gj`.  The region `X₁` contains the `(L-2)`-cell neighbourhood of that polymer (`hfar`; it is the
region `X1` of a chosen family, `X1_far`); with the numeric tie `18 ≤ (L-2) L^{m₀}` (`htie`) the
`6 M`-neighbourhood of the margin lies in the region. -/
theorem hgeom_of_local {S : StepSetting d L N₁ m₁ k N ϱ} {C : StepClass d L N₁ m₁ k N ϱ}
    {C' : StepClass d L N₁' m₁ k N ϱ} {F : CanonCover d L N₁ m₁ k ϱ ϱ₁}
    {F' : CanonCover d L N₁' m₁ k ϱ ϱ₁'} (LC : CanonCoverLocal C.m₀ F F') {i₀ i₁ : Fin N}
    {R : ℕ} (hL : 3 ≤ L) (hm₁ : 1 ≤ m₁) (htie : 18 ≤ (L - 2) * L ^ C.m₀)
    (SpG : DGSetting S.G' (compWeight L S.a₁) S.ν)
    (hbig : 2 * (R + 1 + 6 * (k + 1) * L ^ (k + 1 + m₁) + (5 * L + 2) * L ^ (k + 1 + m₁) +
      L ^ (k + 1)) + 3 * L ^ (k + 1) + 5 < N₁ * L ^ m₁ * L ^ (k + 1))
    (hbig' : 2 * (R + 1 + 6 * (k + 1) * L ^ (k + 1 + m₁) + (5 * L + 2) * L ^ (k + 1 + m₁) +
      L ^ (k + 1)) + 3 * L ^ (k + 1) + 5 < N₁' * L ^ m₁ * L ^ (k + 1))
    (hfar : ∀ j y₀ X₀, (j, y₀, X₀) ∈ AdmPairs L N₁ m₁ k d C.m₀ k →
      ∀ p ∈ polySet C.m₀ j y₀ X₀, ∀ v : Fin d → ℤ,
        (∀ μ, |v μ| ≤ (((L - 2) * cellSide L C.m₀ m₁ (k + 1) : ℕ) : ℤ)) →
        p + (intTorus v : CTorus d L N₁ m₁ (k + 1)) ∈
          (↑(F.X₁fC j y₀ X₀) : Set (CTorus d L N₁ m₁ (k + 1))))
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
  have hL2 : 2 ≤ L := by omega
  intro j y₀ X₀ hadm hbox
  have hpoly : ∀ p ∈ canonPts LC j y₀ X₀, p ∈ polySet C.m₀ j y₀ X₀ := by
    rintro p ((hp | hp) | hp)
    · rcases hp with rfl | hp
      · exact Or.inl hadm.2.2.2.2
      · exact Or.inl hp
    · exact LC.hPK_sub j y₀ X₀ hp
    · exact LC.hPJ_sub j y₀ X₀ hp
  have hfar' : ∀ p ∈ canonPts LC j y₀ X₀, ∀ v : Fin d → ℤ,
      (∀ μ, |v μ| ≤ (((L - 2) * cellSide L C.m₀ m₁ (k + 1) : ℕ) : ℤ)) →
      p + (intTorus v : CTorus d L N₁ m₁ (k + 1)) ∈
        (↑(F.X₁fC j y₀ X₀) : Set (CTorus d L N₁ m₁ (k + 1))) :=
    fun p hp v hv => hfar j y₀ X₀ hadm p (hpoly p hp) v hv
  have hmarg : ∀ x ∈ canonZ LC j y₀ X₀, ∀ w : Fin d → ℤ,
      (∀ μ, |(w μ : ℝ)| < 6 * (L : ℝ) ^ ((k + 1) + m₁)) →
      x + (intTorus w : CTorus d L N₁ m₁ (k + 1)) ∈
        (↑(F.X₁fC j y₀ X₀) : Set (CTorus d L N₁ m₁ (k + 1))) :=
    fun x hx w hw => margin_in_region LC hL hm₁ htie hfar' hx w hw
  have hsub : ∀ w ∈ canonPts LC j y₀ X₀, w ∈ canonZ LC j y₀ X₀ := fun w hw =>
    ⟨w, ⟨w, hw, by simp [supDist_self]⟩, SameCell.refl _ _⟩
  have hZX : canonZ LC j y₀ X₀ ⊆ ↑(F.X₁fC j y₀ X₀) := fun x hx => by
    have h0 : (intTorus (0 : Fin d → ℤ) : CTorus d L N₁ m₁ (k + 1)) = 0 := by
      funext μ; simp [intTorus_apply]
    have := hmarg x hx 0 (fun μ => by simp; positivity)
    rwa [h0, add_zero] at this
  have hZbox : ∀ z ∈ canonZ LC j y₀ X₀, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) z :=
    fun z hz => hbox z (hZX hz)
  have hy₀ : y₀ ∈ canonPts LC j y₀ X₀ := Or.inl (Or.inl (Set.mem_insert _ _))
  have hPKs : LC.PK j y₀ X₀ ⊆ canonPts LC j y₀ X₀ := fun x hx => Or.inl (Or.inr hx)
  have hPJs : LC.PJ j y₀ X₀ ⊆ canonPts LC j y₀ X₀ := fun x hx => Or.inr hx
  have hPKb := hPK j y₀ X₀ hadm hbox
  have hPJb := hPJ j y₀ X₀ hadm hbox
  have hmono : ∀ x, x ∈ nearSet (zRad L m₁ k) (canonPts LC j y₀ X₀) → x ∈ canonZ LC j y₀ X₀ :=
    fun x hx => ⟨x, hx, SameCell.refl _ _⟩
  have hnb : ∀ μ : Fin d, y₀ + (L ^ j) • (Pi.single μ 1 : CTorus d L N₁ m₁ (k + 1)) ∈
      canonZ LC j y₀ X₀ := fun μ => by
    refine hmono _ ⟨y₀, hy₀, (supDist_nsmul_single _ _ μ).trans ?_⟩
    have hjk : j ≤ k + 1 := by have := hadm.2.1; omega
    have h1 : L ^ j ≤ L ^ (m₁ + (k + 1)) :=
      Nat.pow_le_pow_right (by omega) (by omega)
    have h2 : 0 < L ^ (m₁ + (k + 1)) := pow_pos (by omega) _
    unfold zRad; omega
  have h0 : (intTorus (0 : Fin d → ℤ) : CTorus d L N₁ m₁ (k + 1)) = 0 := by
    funext μ; simp [intTorus_apply]
  have hcb : ∀ z ∈ Localization.box (cbase (cellSide L C.m₀ m₁ j) y₀ -
      natT (fun _ => L / 2 * cellSide L C.m₀ m₁ j)) (L * cellSide L C.m₀ m₁ j),
      InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) z := fun z hz => hbox z (by
    have := hfar j y₀ X₀ hadm z (Or.inr hz) 0 (fun μ => by simp only [Pi.zero_apply, abs_zero]; positivity)
    rwa [h0, add_zero] at this)
  refine ⟨fun μ => hZbox _ (hnb μ), hcb,
    canonZ LC j y₀ X₀,
    fun x hx => hsub x (Or.inl (Or.inl (Set.mem_insert_of_mem _ hx))),
    hnb, hZX,
    blockMargin_core SpG S.hG' _ hmarg, ?_, ?_, ?_, ?_, ?_,
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
      hmono _ (dataSite_mem_nearSet (LC.hnK j) hL2 hPKs h)
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
