/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Polymer.TwoTorusGapStepObsDom
public import Balaban.Polymer.TwoTorusGapIdentSite

/-!
# The site term of the observable under the recentring map (item 24, blocker 7)

`siteEv_recentred`: the terms `Ev` of the site functionals `δφ(xs, iy)` (the terms of the expansion
along the fluctuation field `hatPsiF`) of the local covers of `xs` and of `xs'`, `xs' + tB = bm (xs + tA)`,
agree at `φ '' Y`, `φ x = bm (x + tA) - tB`, for a given recentring vector (`hEvT` of
`obsCoeffParam_recentred`).  By `FFmarked_one_zero` the fan functional is the marked functional at the
marks `(1, 0)`, and `evDec_recentred` applies, with `hfamΦ_siteFun_at` at the vector.
-/

@[expose] public section

noncomputable section

open scoped Classical

namespace Balaban.Polymer.TwoTorusStep

open Balaban Balaban.Localization Balaban.Analysis Balaban.Fluctuation Balaban.SmallField
  Balaban.SmallField.Def6 Balaban.Polymer Balaban.Multiscale Balaban.Background
  Balaban.Localization.DecEquiv

section SiteRec

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
local notation "HA" => levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ)
  k (Nat.le_succ k)
set_option hygiene false in
local notation "HB" => levelGS (d := d) (L := L) (N₁ := N₁') (m₁ := m₁) (k := k + 1) (ϱ := ϱ)
  k (Nat.le_succ k)
set_option hygiene false in
local notation "XA" => (↑(LocalCover.nbhdF m₀ xs) : Set (CTorus d L N₁ m₁ (k + 1)))
set_option hygiene false in
local notation "XB" => (↑(LocalCover.nbhdF m₀ xs') : Set (CTorus d L N₁' m₁ (k + 1)))

/-- **The region of the local cover under the recentring map.** -/
theorem nbhdF_recentred {m₀ R : ℕ} (hN : L ^ m₀ ∣ N₁) (hN' : L ^ m₀ ∣ N₁')
    (tA : CTorus d L N₁ m₁ (k + 1)) (tB : CTorus d L N₁' m₁ (k + 1))
    (htA : ∀ μ, L ^ ((k + 1) + m₀ + m₁) ∣ (tA μ).val)
    (htB : ∀ μ, L ^ ((k + 1) + m₀ + m₁) ∣ (tB μ).val)
    (hnF : 2 * R + ((L - 1) * cellSide L m₀ m₁ (k + 1) + L * cellSide L m₀ m₁ (k + 1)) <
      (N₁ * L ^ m₁) * L ^ (k + 1))
    (xs : CTorus d L N₁ m₁ (k + 1)) (xs' : CTorus d L N₁' m₁ (k + 1))
    (hxs : xs' + tB = bm (xs + tA))
    (hX₁R : ∀ x ∈ LocalCover.nbhd m₀ xs, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) (x + tA)) :
    LocalCover.nbhdF m₀ xs' = (LocalCover.nbhdF m₀ xs).image (fun x => bm (x + tA) - tB) := by
  apply Finset.coe_injective
  have hbx : ∀ y ∈ LocalCover.nbhd m₀ (xs + tA),
      InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) y := by
    rw [nbhd_translate hN tA htA]
    rintro _ ⟨x, hx, rfl⟩
    exact hX₁R x hx
  have e1 := nbhdF_translate hN' tB htB xs'
  have e2 := nbhdF_image_finset hN hN' hnF (xs + tA) hbx
  have e3 := nbhdF_translate hN tA htA xs
  rw [hxs, ← e2, Finset.coe_image, e3, Set.image_image] at e1
  have e4 : (↑(LocalCover.nbhdF m₀ xs') : Set (CTorus d L N₁' m₁ (k + 1))) =
      (Equiv.addRight tB).symm '' ((Equiv.addRight tB) '' ↑(LocalCover.nbhdF m₀ xs')) :=
    (Equiv.symm_image_image _ _).symm
  rw [e4, ← e1, Finset.coe_image, Set.image_image]
  refine Set.image_congr (fun x _ => ?_)
  simp [sub_eq_add_neg]

/-- **The region of a local cover in the recentred box has width `L a_K ≤ 2 R + 1`.** -/
theorem width_nbhd_recentred {m₀ R : ℕ} (hd : 0 < d) (t : CTorus d L N₁ m₁ (k + 1))
    (xs : CTorus d L N₁ m₁ (k + 1))
    (hX₁R : ∀ x ∈ LocalCover.nbhd m₀ xs, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) (x + t))
    (hn20 : 20 * R + 20 < (N₁ * L ^ m₁) * L ^ (k + 1)) :
    L * cellSide L m₀ m₁ (k + 1) ≤ 2 * R + 1 := by
  have hw0 := width_le_of_box_subset_inBox (n := (N₁ * L ^ m₁) * L ^ (k + 1)) hd
    (b := LocalCover.corner m₀ xs - natT (n := (N₁ * L ^ m₁) * L ^ (k + 1))
      (fun _ => (L - 1) * cellSide L m₀ m₁ (k + 1)) + t)
    (s := L * cellSide L m₀ m₁ (k + 1)) (r := R)
    (t := min (L * cellSide L m₀ m₁ (k + 1)) ((N₁ * L ^ m₁) * L ^ (k + 1)))
    (min_le_left _ _) (min_le_right _ _) (fun x hx => by
      obtain ⟨y, rfl⟩ : ∃ y, x = y + t := ⟨x - t, by abel⟩
      exact hX₁R y (by
        have := (mem_box_add_iff _ t y _).1 hx
        unfold LocalCover.nbhd cellNbhd
        exact box_mono _ (by nlinarith) this))
  rcases min_choice (L * cellSide L m₀ m₁ (k + 1)) ((N₁ * L ^ m₁) * L ^ (k + 1)) with h | h
  · rwa [h] at hw0
  · rw [h] at hw0; omega

/-- **The marked block term `evDec … ∅ 1 0` of the local cover under the recentring map** (the core
of `siteEv_recentred` and of `evDec_blockEnergy_recentred`).  For translated functionals
`ΦT`, `ΦT'` with corresponding reads at the given recentring vector. -/
theorem evDec_localCover_recentred
    {a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁ : ℝ}
    (hC : FlCore N (GA) (HA) a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
    (hC' : FlCore N (GB) (HB) a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁) (hk : 1 ≤ k)
    (hGA : IsLevel (GA) (k + 1)) (hGB : IsLevel (GB) (k + 1)) (cc : ℂ) {cψ : ℝ} (hcψ : 0 ≤ cψ)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δc : ℝ}
    (hmar : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hαK : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    {F₁ : DecParams (GA) × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      ((GA).Ω 1 × Fin N → ℂ) × ((GA).Ω 1 → ℂ)}
    {F₁' : DecParams (GB) × RawData d L (N₁' * L ^ m₁) (k + 1) N →
      ((GB).Ω 1 × Fin N → ℂ) × ((GB).Ω 1 → ℂ)}
    (hF₁ : ∀ (s : DecParams (GA)) (D : BgData (GA) N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC (GA) (bgC0 d L N) (c7 d L N BG κ) ν D → ∀ (φ : (GA).Ω 1 × Fin N → ℂ)
        (α : (GA).Ω 1 → ℂ), IsDecBg (GA) (compWeight L a₁) ν (rho4 d L N BG κ) s D φ α →
        F₁ (s, rawOf D) = (φ, α))
    (hF₁' : ∀ (s : DecParams (GB)) (D : BgData (GB) N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC (GB) (bgC0 d L N) (c7 d L N BG κ) ν D → ∀ (φ : (GB).Ω 1 × Fin N → ℂ)
        (α : (GB).Ω 1 → ℂ), IsDecBg (GB) (compWeight L a₁) ν (rho4 d L N BG κ) s D φ α →
        F₁' (s, rawOf D) = (φ, α))
    {Sol : Dec2.DecParams (coverOf (GA)) × Edat (HA) N → ((HA).Ω 1 × Fin N → ℂ) × ((HA).Ω 1 → ℂ)}
    {Sol' : Dec2.DecParams (coverOf (GB)) × Edat (HB) N →
      ((HB).Ω 1 × Fin N → ℂ) × ((HB).Ω 1 → ℂ)}
    (hSol : ∀ p : Dec2.DecParams (coverOf (GA)) × Edat (HA) N, (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM (HA) N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2 →
        (Sol p).1 = dphi (HA) (Dec2.decG (coverOf (GA)) (HA) (compWeight L a₁) ν p.1) p.2.2.1
          p.2.1 (pertSource (HA) (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol p).2 ∧
        Dec2.DecFixed (coverOf (GA)) (HA) (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
          (pertSource (HA) (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol p).2 ∧
        Small (HA) (Sol p).2 (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
        Small (HA) (Sol p).2 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        SupBounds (HA) (Sol p).1 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        (∀ δα' : (HA).Ω 1 → ℂ, Small (HA) δα' (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf (GA)) (HA) (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
            (pertSource (HA) (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol p).2))
    (hSol' : ∀ p : Dec2.DecParams (coverOf (GB)) × Edat (HB) N, (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM (HB) N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2 →
        (Sol' p).1 = dphi (HB) (Dec2.decG (coverOf (GB)) (HB) (compWeight L a₁) ν p.1) p.2.2.1
          p.2.1 (pertSource (HB) (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol' p).2 ∧
        Dec2.DecFixed (coverOf (GB)) (HB) (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
          (pertSource (HB) (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol' p).2 ∧
        Small (HB) (Sol' p).2 (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
        Small (HB) (Sol' p).2 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        SupBounds (HB) (Sol' p).1 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        (∀ δα' : (HB).Ω 1 → ℂ, Small (HB) δα' (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf (GB)) (HB) (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
            (pertSource (HB) (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol' p).2))
    {m₀ : ℕ} (hd : 0 < d) (hL : 2 ≤ L) (hm₀ : 1 ≤ m₀) (hm₁ : 1 ≤ m₁)
    (hN : L ^ m₀ ∣ N₁) (hN' : L ^ m₀ ∣ N₁')
    (z : Fin d → ℤ) (hz : ∀ μ, ((cellSide L m₀ m₁ (k + 1) : ℕ) : ℤ) ∣ z μ)
    (xs : CTorus d L N₁ m₁ (k + 1)) (xs' : CTorus d L N₁' m₁ (k + 1))
    (hxs : xs' + (fun μ => ((z μ : ℤ) : ZMod ((N₁' * L ^ m₁) * L ^ (k + 1)))) =
      bm (xs + fun μ => ((z μ : ℤ) : ZMod ((N₁ * L ^ m₁) * L ^ (k + 1)))))
    {Φ ΦT : ((GA).Ω 1 × Fin N → ℂ) × ((GA).Ω 1 → ℂ) → ((HA).Ω 1 × Fin N → ℂ) →
      RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) → ℂ}
    {Φ' ΦT' : ((GB).Ω 1 × Fin N → ℂ) × ((GB).Ω 1 → ℂ) → ((HB).Ω 1 × Fin N → ℂ) →
      RawData d L (N₁' * L ^ m₁) (k + 1) N × (CTorus d L N₁' m₁ (k + 1) → Fin N → ℂ) → ℂ}
    (hΦan : AnalyticOnNhd ℂ (fun t => Φ t.1 t.2.1 t.2.2)
      (FlReal (GA) (HA) a₁ ν BG κ eps (LocalCover.nbhdF m₀ xs) BG₂ δ₁))
    (hΦan' : AnalyticOnNhd ℂ (fun t => Φ' t.1 t.2.1 t.2.2)
      (FlReal (GB) (HB) a₁ ν BG κ eps (LocalCover.nbhdF m₀ xs') BG₂ δ₁))
    (SA : LatSymm (GA) (GA)
      (Equiv.addRight (fun μ => ((z μ : ℤ) : ZMod ((N₁ * L ^ m₁) * L ^ (k + 1))))))
    (SmA : LatSymm (HA) (HA)
      (Equiv.addRight (fun μ => ((z μ : ℤ) : ZMod ((N₁ * L ^ m₁) * L ^ (k + 1))))))
    (SB : LatSymm (GB) (GB)
      (Equiv.addRight (fun μ => ((z μ : ℤ) : ZMod ((N₁' * L ^ m₁) * L ^ (k + 1))))))
    (SmB : LatSymm (HB) (HB)
      (Equiv.addRight (fun μ => ((z μ : ℤ) : ZMod ((N₁' * L ^ m₁) * L ^ (k + 1))))))
    {Rα Rδ Rψ : Set (CTorus d L N₁ m₁ (k + 1))}
    (hΦA : ∀ (bg : ((GA).Ω 1 × Fin N → ℂ) × ((GA).Ω 1 → ℂ)) δφ u,
      ΦT (SA.fld bg.1, SA.mul bg.2) (SmA.fld δφ) (symU (Equiv.addRight
        (fun μ => ((z μ : ℤ) : ZMod ((N₁ * L ^ m₁) * L ^ (k + 1))))) u) = Φ bg δφ u)
    (hΦB : ∀ (bg : ((GB).Ω 1 × Fin N → ℂ) × ((GB).Ω 1 → ℂ)) δφ u,
      ΦT' (SB.fld bg.1, SB.mul bg.2) (SmB.fld δφ) (symU (Equiv.addRight
        (fun μ => ((z μ : ℤ) : ZMod ((N₁' * L ^ m₁) * L ^ (k + 1))))) u) = Φ' bg δφ u)
    (hBM : BlockMargin (GA) ((LocalCover.nbhdF m₀ xs).image (Equiv.addRight
      (fun μ => ((z μ : ℤ) : ZMod ((N₁ * L ^ m₁) * L ^ (k + 1)))))) Rα)
    (hRδ : Rδ ⊆ ↑((LocalCover.nbhdF m₀ xs).image (Equiv.addRight
      (fun μ => ((z μ : ℤ) : ZMod ((N₁ * L ^ m₁) * L ^ (k + 1)))))))
    (hRψ : Rψ ⊆ ↑((LocalCover.nbhdF m₀ xs).image (Equiv.addRight
      (fun μ => ((z μ : ℤ) : ZMod ((N₁ * L ^ m₁) * L ^ (k + 1)))))))
    (hΦ : ∀ (t : (((GA).Ω 1 × Fin N → ℂ) × ((GA).Ω 1 → ℂ)) × ((HA).Ω 1 × Fin N → ℂ) ×
        (RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ)))
      (t' : (((GB).Ω 1 × Fin N → ℂ) × ((GB).Ω 1 → ℂ)) × ((HB).Ω 1 × Fin N → ℂ) ×
        (RawData d L (N₁' * L ^ m₁) (k + 1) N × (CTorus d L N₁' m₁ (k + 1) → Fin N → ℂ))),
      (∀ (y : (GA).Ω 1) (y' : (GB).Ω 1), (y : CTorus d L N₁ m₁ (k + 1)) ∈ Rα →
        (y' : CTorus d L N₁' m₁ (k + 1)) = bm (y : CTorus d L N₁ m₁ (k + 1)) →
          t'.1.2 y' = t.1.2 y) →
      (∀ (w : (HA).Ω 1) (w' : (HB).Ω 1), (w : CTorus d L N₁ m₁ (k + 1)) ∈ Rδ →
        (w' : CTorus d L N₁' m₁ (k + 1)) = bm (w : CTorus d L N₁ m₁ (k + 1)) →
        ∀ i, t'.2.1 (w', i) = t.2.1 (w, i)) →
      (∀ x ∈ Rψ, t'.2.2.2 (bm x) = t.2.2.2 x) →
      ΦT' t'.1 t'.2.1 t'.2.2 = ΦT t.1 t.2.1 t.2.2)
    {R : ℕ} (hX₁R : ∀ x ∈ LocalCover.nbhd m₀ xs, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1))
      (x + fun μ => ((z μ : ℤ) : ZMod ((N₁ * L ^ m₁) * L ^ (k + 1)))))
    {Y : Set (CTorus d L N₁ m₁ (k + 1))}
    (hYR : ∀ y ∈ Y, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1))
      (y + fun μ => ((z μ : ℤ) : ZMod ((N₁ * L ^ m₁) * L ^ (k + 1)))))
    (hn20 : 20 * R + 20 < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hn20' : 20 * R + 20 < (N₁' * L ^ m₁) * L ^ (k + 1))
    {D : BgData (GA) N} {D' : BgData (GB) N}
    (hD : XiCData (GA) (compWeight L a₁) ν (k + 1) 1 eps D)
    (hD' : XiCData (GB) (compWeight L a₁) ν (k + 1) 1 eps D')
    (hraw : RawBoxAgree {w | InBox d (R + 3 * L ^ (k + 1)) ((N₁ * L ^ m₁) * L ^ (k + 1)) w}
      (symRaw (Equiv.addRight (fun μ => ((z μ : ℤ) : ZMod ((N₁ * L ^ m₁) * L ^ (k + 1)))))
        (rawOf D))
      (symRaw (Equiv.addRight (fun μ => ((z μ : ℤ) : ZMod ((N₁' * L ^ m₁) * L ^ (k + 1)))))
        (rawOf D')))
    {ψh : unitPts (GA) × Fin N → ℂ} {ψh' : unitPts (GB) × Fin N → ℂ}
    (hψh : ∀ p, ‖ψh p‖ ≤ cψ) (hψh' : ∀ p, ‖ψh' p‖ ≤ cψ)
    (hhat : ∀ y, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1))
        (y + fun μ => ((z μ : ℤ) : ZMod ((N₁ * L ^ m₁) * L ^ (k + 1)))) →
      ∀ i, ψh' (unitPt hGB (bm (y + fun μ => ((z μ : ℤ) : ZMod ((N₁ * L ^ m₁) * L ^ (k + 1)))) -
        fun μ => ((z μ : ℤ) : ZMod ((N₁' * L ^ m₁) * L ^ (k + 1)))), i) = ψh (unitPt hGA y, i))
    (hrad : markedRad d L N k a₁ κ cψ cc < δ₁) :
    evDec (LocalCover.nbhdF m₀ xs') m₀ k (LocalCover.fam m₀ xs') a₁ ν hGB cc F₁' Sol' Φ' ∅ 1 0
        ((fun x => bm (x + fun μ => ((z μ : ℤ) : ZMod ((N₁ * L ^ m₁) * L ^ (k + 1)))) -
          fun μ => ((z μ : ℤ) : ZMod ((N₁' * L ^ m₁) * L ^ (k + 1)))) '' Y) (rawOf D', ψh') =
      evDec (LocalCover.nbhdF m₀ xs) m₀ k (LocalCover.fam m₀ xs) a₁ ν hGA cc F₁ Sol Φ ∅ 1 0
        Y (rawOf D, ψh) := by
  classical
  set tA : CTorus d L N₁ m₁ (k + 1) := fun μ => ((z μ : ℤ) : ZMod ((N₁ * L ^ m₁) * L ^ (k + 1)))
    with htAdef
  set tB : CTorus d L N₁' m₁ (k + 1) := fun μ => ((z μ : ℤ) : ZMod ((N₁' * L ^ m₁) * L ^ (k + 1)))
    with htBdef
  have htA : ∀ μ, L ^ ((k + 1) + m₀ + m₁) ∣ (tA μ).val := fun μ =>
    dvd_val_intCast (cellSide_dvd hN le_rfl) (hz μ)
  have htB : ∀ μ, L ^ ((k + 1) + m₀ + m₁) ∣ (tB μ).val := fun μ =>
    dvd_val_intCast (cellSide_dvd hN' le_rfl) (hz μ)
  have hHA : IsLevel (HA) k := isLevel_levelGS hk (Nat.le_succ k)
  have hHB : IsLevel (HB) k := isLevel_levelGS hk (Nat.le_succ k)
  -- the width of the region and the margins
  have hbox : ∃ b, box b (L * cellSide L m₀ m₁ (k + 1)) ⊆
      (↑(LocalCover.nbhdF m₀ xs) : Set (CTorus d L N₁ m₁ (k + 1))) := by
    refine ⟨LocalCover.corner m₀ xs - natT (n := (N₁ * L ^ m₁) * L ^ (k + 1))
      (fun _ => (L - 1) * cellSide L m₀ m₁ (k + 1)), ?_⟩
    rw [LocalCover.coe_nbhdF]
    exact box_mono _ (by nlinarith)
  obtain ⟨b, hb⟩ := hbox
  have hw0 := width_le_of_box_subset_inBox (n := (N₁ * L ^ m₁) * L ^ (k + 1)) hd
    (b := b + tA) (s := L * cellSide L m₀ m₁ (k + 1)) (r := R)
    (t := min (L * cellSide L m₀ m₁ (k + 1)) ((N₁ * L ^ m₁) * L ^ (k + 1)))
    (min_le_left _ _) (min_le_right _ _) (fun x hx => by
      obtain ⟨y, rfl⟩ : ∃ y, x = y + tA := ⟨x - tA, by abel⟩
      exact hX₁R y (by
        rw [← LocalCover.coe_nbhdF]
        exact hb ((mem_box_add_iff b tA y _).1 hx)))
  have hw : L * cellSide L m₀ m₁ (k + 1) ≤ 2 * R + 1 := by
    rcases min_choice (L * cellSide L m₀ m₁ (k + 1)) ((N₁ * L ^ m₁) * L ^ (k + 1)) with h | h
    · rwa [h] at hw0
    · rw [h] at hw0; omega
  obtain ⟨hnF, -, -, -⟩ := gapMargins_of_width hL hm₀ hm₁ hw hn20
  have hLa : (L - 1) * cellSide L m₀ m₁ (k + 1) ≤ L * cellSide L m₀ m₁ (k + 1) :=
    Nat.mul_le_mul_right _ (Nat.sub_le L 1)
  have hnF1 : 2 * R + ((L - 1) * cellSide L m₀ m₁ (k + 1) + L * cellSide L m₀ m₁ (k + 1)) <
      (N₁ * L ^ m₁) * L ^ (k + 1) := by omega
  -- covers
  have hcov := LocalCover.covSetup (m₀ := m₀) hGA hN (j := k) le_rfl xs
  have hX₁ := LocalCover.coe_nbhdF_eq_X1 (m₀ := m₀) hGA hN (j := k) le_rfl xs
  have hcov' := LocalCover.covSetup (m₀ := m₀) hGB hN' (j := k) le_rfl xs'
  have hX₁' := LocalCover.coe_nbhdF_eq_X1 (m₀ := m₀) hGB hN' (j := k) le_rfl xs'
  have hX' := nbhdF_recentred hN hN' tA tB htA htB hnF1 xs xs' hxs hX₁R
  have hSA := LatSymm.ofTranslateLevel hGA tA (fun μ => (pow_dvd_pow L (by omega)).trans (htA μ))
  have hSmA := LatSymm.ofTranslateLevel hHA tA (fun μ => (pow_dvd_pow L (by omega)).trans (htA μ))
  have hSB := LatSymm.ofTranslateLevel hGB tB (fun μ => (pow_dvd_pow L (by omega)).trans (htB μ))
  have hSmB := LatSymm.ofTranslateLevel hHB tB (fun μ => (pow_dvd_pow L (by omega)).trans (htB μ))
  have h := evDec_recentred hC hC' hk hGA hGB cc hcψ hMX hmar hαK hsm hF₁ hF₁' hSol hSol'
    hN hN' tA tB htA htB rfl hX' rfl hcov hX₁ hcov' hX₁' hSA hSmA hSB hSmB
    hΦan hΦan' hΦA hΦB hBM hRδ hRψ hΦ
    (fun x hx => hX₁R x (by rw [← LocalCover.coe_nbhdF]; exact Finset.mem_coe.2 hx)) hYR hD hD'
    hraw hψh hψh' hhat (Zm := ∅) (Zm' := ∅) (fun y _ => by simp)
    (um := 1) (tm := 0) (by rw [norm_one, norm_zero, add_zero, one_mul]; exact hrad)
    hd hL hm₀ hm₁ ⟨b, hb⟩ hn20 hn20'
  exact h

/-- **The site term of the observable at a given recentring vector.** -/
theorem siteEv_recentred
    {a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁ : ℝ}
    (hC : FlCore N (GA) (HA) a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
    (hC' : FlCore N (GB) (HB) a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁) (hk : 1 ≤ k)
    (hGA : IsLevel (GA) (k + 1)) (hGB : IsLevel (GB) (k + 1)) (cc : ℂ) {cψ : ℝ} (hcψ : 0 ≤ cψ)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δc : ℝ}
    (hmar : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hαK : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    {F₁ : DecParams (GA) × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      ((GA).Ω 1 × Fin N → ℂ) × ((GA).Ω 1 → ℂ)}
    {F₁' : DecParams (GB) × RawData d L (N₁' * L ^ m₁) (k + 1) N →
      ((GB).Ω 1 × Fin N → ℂ) × ((GB).Ω 1 → ℂ)}
    (hF₁ : ∀ (s : DecParams (GA)) (D : BgData (GA) N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC (GA) (bgC0 d L N) (c7 d L N BG κ) ν D → ∀ (φ : (GA).Ω 1 × Fin N → ℂ)
        (α : (GA).Ω 1 → ℂ), IsDecBg (GA) (compWeight L a₁) ν (rho4 d L N BG κ) s D φ α →
        F₁ (s, rawOf D) = (φ, α))
    (hF₁' : ∀ (s : DecParams (GB)) (D : BgData (GB) N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC (GB) (bgC0 d L N) (c7 d L N BG κ) ν D → ∀ (φ : (GB).Ω 1 × Fin N → ℂ)
        (α : (GB).Ω 1 → ℂ), IsDecBg (GB) (compWeight L a₁) ν (rho4 d L N BG κ) s D φ α →
        F₁' (s, rawOf D) = (φ, α))
    {Sol : Dec2.DecParams (coverOf (GA)) × Edat (HA) N → ((HA).Ω 1 × Fin N → ℂ) × ((HA).Ω 1 → ℂ)}
    {Sol' : Dec2.DecParams (coverOf (GB)) × Edat (HB) N →
      ((HB).Ω 1 × Fin N → ℂ) × ((HB).Ω 1 → ℂ)}
    (hSol : ∀ p : Dec2.DecParams (coverOf (GA)) × Edat (HA) N, (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM (HA) N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2 →
        (Sol p).1 = dphi (HA) (Dec2.decG (coverOf (GA)) (HA) (compWeight L a₁) ν p.1) p.2.2.1
          p.2.1 (pertSource (HA) (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol p).2 ∧
        Dec2.DecFixed (coverOf (GA)) (HA) (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
          (pertSource (HA) (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol p).2 ∧
        Small (HA) (Sol p).2 (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
        Small (HA) (Sol p).2 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        SupBounds (HA) (Sol p).1 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        (∀ δα' : (HA).Ω 1 → ℂ, Small (HA) δα' (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf (GA)) (HA) (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
            (pertSource (HA) (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol p).2))
    (hSol' : ∀ p : Dec2.DecParams (coverOf (GB)) × Edat (HB) N, (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM (HB) N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2 →
        (Sol' p).1 = dphi (HB) (Dec2.decG (coverOf (GB)) (HB) (compWeight L a₁) ν p.1) p.2.2.1
          p.2.1 (pertSource (HB) (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol' p).2 ∧
        Dec2.DecFixed (coverOf (GB)) (HB) (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
          (pertSource (HB) (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol' p).2 ∧
        Small (HB) (Sol' p).2 (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
        Small (HB) (Sol' p).2 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        SupBounds (HB) (Sol' p).1 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        (∀ δα' : (HB).Ω 1 → ℂ, Small (HB) δα' (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf (GB)) (HB) (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
            (pertSource (HB) (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol' p).2))
    {m₀ : ℕ} (hd : 0 < d) (hL : 2 ≤ L) (hm₀ : 1 ≤ m₀) (hm₁ : 1 ≤ m₁)
    (hN : L ^ m₀ ∣ N₁) (hN' : L ^ m₀ ∣ N₁')
    (z : Fin d → ℤ) (hz : ∀ μ, ((cellSide L m₀ m₁ (k + 1) : ℕ) : ℤ) ∣ z μ)
    (xs : CTorus d L N₁ m₁ (k + 1)) (xs' : CTorus d L N₁' m₁ (k + 1)) (iy : Fin N)
    (hxs : xs' + (fun μ => ((z μ : ℤ) : ZMod ((N₁' * L ^ m₁) * L ^ (k + 1)))) =
      bm (xs + fun μ => ((z μ : ℤ) : ZMod ((N₁ * L ^ m₁) * L ^ (k + 1)))))
    {R : ℕ} (hX₁R : ∀ x ∈ LocalCover.nbhd m₀ xs, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1))
      (x + fun μ => ((z μ : ℤ) : ZMod ((N₁ * L ^ m₁) * L ^ (k + 1)))))
    {Y : Set (CTorus d L N₁ m₁ (k + 1))}
    (hYR : ∀ y ∈ Y, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1))
      (y + fun μ => ((z μ : ℤ) : ZMod ((N₁ * L ^ m₁) * L ^ (k + 1)))))
    (hn20 : 20 * R + 20 < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hn20' : 20 * R + 20 < (N₁' * L ^ m₁) * L ^ (k + 1))
    {D : BgData (GA) N} {D' : BgData (GB) N}
    (hD : XiCData (GA) (compWeight L a₁) ν (k + 1) 1 eps D)
    (hD' : XiCData (GB) (compWeight L a₁) ν (k + 1) 1 eps D')
    (hraw : RawBoxAgree {w | InBox d (R + 3 * L ^ (k + 1)) ((N₁ * L ^ m₁) * L ^ (k + 1)) w}
      (symRaw (Equiv.addRight (fun μ => ((z μ : ℤ) : ZMod ((N₁ * L ^ m₁) * L ^ (k + 1)))))
        (rawOf D))
      (symRaw (Equiv.addRight (fun μ => ((z μ : ℤ) : ZMod ((N₁' * L ^ m₁) * L ^ (k + 1)))))
        (rawOf D')))
    {ψh : unitPts (GA) × Fin N → ℂ} {ψh' : unitPts (GB) × Fin N → ℂ}
    (hψh : ∀ p, ‖ψh p‖ ≤ cψ) (hψh' : ∀ p, ‖ψh' p‖ ≤ cψ)
    (hhat : ∀ y, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1))
        (y + fun μ => ((z μ : ℤ) : ZMod ((N₁ * L ^ m₁) * L ^ (k + 1)))) →
      ∀ i, ψh' (unitPt hGB (bm (y + fun μ => ((z μ : ℤ) : ZMod ((N₁ * L ^ m₁) * L ^ (k + 1)))) -
        fun μ => ((z μ : ℤ) : ZMod ((N₁' * L ^ m₁) * L ^ (k + 1)))), i) = ψh (unitPt hGA y, i))
    (hrad : markedRad d L N k a₁ κ cψ cc < δ₁) :
    evTerm (fun i : ParIdx (GB) (XB) => i.1.1) (GB)
        m₀ (X1 (GB) m₀ k (LocalCover.fam m₀ xs'))
        (fun u s => siteFun (GB) (HB) xs' iy
          (F₁' (extParams (GB) (XB) s, u.1))
          (Sol' (extParams (GB) (XB) s,
            flEdat (GB) (HB) (F₁' (extParams (GB)
              (XB) s, u.1)) u.1.1
              (hatPsiF (GB) a₁ ν hGB cc F₁'
                (extParams (GB) (XB) s) u.1 u.2))).1
          (u.1, hatPsiF (GB) a₁ ν hGB cc F₁'
            (extParams (GB) (XB) s) u.1 u.2))
        ((fun x => bm (x + fun μ => ((z μ : ℤ) : ZMod ((N₁ * L ^ m₁) * L ^ (k + 1)))) -
          fun μ => ((z μ : ℤ) : ZMod ((N₁' * L ^ m₁) * L ^ (k + 1)))) '' Y) (rawOf D', ψh') =
      evTerm (fun i : ParIdx (GA) (XA) => i.1.1) (GA) m₀
        (X1 (GA) m₀ k (LocalCover.fam m₀ xs))
        (fun u s => siteFun (GA) (HA) xs iy (F₁ (extParams (GA) (XA) s, u.1))
          (Sol (extParams (GA) (XA) s,
            flEdat (GA) (HA) (F₁ (extParams (GA) (XA) s, u.1))
              u.1.1 (hatPsiF (GA) a₁ ν hGA cc F₁
                (extParams (GA) (XA) s) u.1 u.2))).1
          (u.1, hatPsiF (GA) a₁ ν hGA cc F₁
            (extParams (GA) (XA) s) u.1 u.2))
        Y (rawOf D, ψh) := by
  classical
  have hHA : IsLevel (HA) k := isLevel_levelGS hk (Nat.le_succ k)
  have hHB : IsLevel (HB) k := isLevel_levelGS hk (Nat.le_succ k)
  have hSA := LatSymm.ofTranslateLevel hGA (fun μ => ((z μ : ℤ) : ZMod ((N₁ * L ^ m₁) * L ^ (k + 1))))
    (fun μ => (pow_dvd_pow L (by omega)).trans (dvd_val_intCast (cellSide_dvd hN le_rfl) (hz μ)))
  have hSmA := LatSymm.ofTranslateLevel hHA (fun μ => ((z μ : ℤ) : ZMod ((N₁ * L ^ m₁) * L ^ (k + 1))))
    (fun μ => (pow_dvd_pow L (by omega)).trans (dvd_val_intCast (cellSide_dvd hN le_rfl) (hz μ)))
  have hSB := LatSymm.ofTranslateLevel hGB (fun μ => ((z μ : ℤ) : ZMod ((N₁' * L ^ m₁) * L ^ (k + 1))))
    (fun μ => (pow_dvd_pow L (by omega)).trans (dvd_val_intCast (cellSide_dvd hN' le_rfl) (hz μ)))
  have hSmB := LatSymm.ofTranslateLevel hHB (fun μ => ((z μ : ℤ) : ZMod ((N₁' * L ^ m₁) * L ^ (k + 1))))
    (fun μ => (pow_dvd_pow L (by omega)).trans (dvd_val_intCast (cellSide_dvd hN' le_rfl) (hz μ)))
  obtain ⟨ΦT, ΦT', Rα, Rδ, Rψ, hBM, hRδ, hRψ, hΦA, hΦB, hΦ⟩ :=
    hfamΦ_siteFun_at hk iy (X₁f := LocalCover.nbhdF m₀ xs) (x₀ := xs) xs'
      (LocalCover.mem_nbhdF_self m₀ xs) z hxs hSA hSmA hSB hSmB
  have h := evDec_localCover_recentred hC hC' hk hGA hGB cc hcψ hMX hmar hαK hsm hF₁ hF₁' hSol hSol'
    hd hL hm₀ hm₁ hN hN' z hz xs xs' hxs ((siteFun_analytic xs iy).mono (Set.subset_univ _))
    ((siteFun_analytic xs' iy).mono (Set.subset_univ _)) hSA hSmA hSB hSmB hΦA hΦB hBM hRδ hRψ hΦ
    hX₁R hYR hn20 hn20' hD hD' hraw hψh hψh' hhat hrad
  unfold evDec at h
  rw [FFmarked_one_zero, FFmarked_one_zero] at h
  exact h

end SiteRec

end Balaban.Polymer.TwoTorusStep
