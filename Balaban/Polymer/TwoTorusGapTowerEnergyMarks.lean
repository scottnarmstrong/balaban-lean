/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Polymer.TwoTorusGapTowerEnergyMarkCorr

/-!
# The marks of the energy coefficient under the recentring map (blocker 7)

* `markedOutDec_eq_of_pairs`: the marked output `markedOutDec` is carried along inverse
  correspondences of the marked pairs that carry the `t`-derivatives of the terms.
* `recentred_inv`, `image_recentred_inv`, `coarse_recentred_inv`: the reverse recentring undoes the
  recentring on the recentred boxes.
* `markedOutDec_recentred`: the marked output of the corrected marks at the label `φ '' Y′` of the
  root `bc (z + τA) - τB` equals that at `Y′` of `z`: the marked pairs correspond by
  `(b, Y) ↦ (bc (b + τA) - τB, φ '' Y)` (`markedPair_recentred_iff` in both directions) and the terms
  by `decMarkCorr_rootBlock_recentred` with the root masks of `rootMask_recentred`.
* `e1MarkGParamG_recentred`: the marks of the parameter family of the energy coefficient at
  corresponding bridge labels agree.
-/

@[expose] public section

noncomputable section

open scoped Classical

namespace Balaban.Polymer.TwoTorusStep

open Balaban Balaban.Localization Balaban.Analysis Balaban.Fluctuation Balaban.SmallField
  Balaban.SmallField.Def6 Balaban.Polymer Balaban.Multiscale Balaban.Background
  Balaban.Localization.DecEquiv Balaban.Inhabited Balaban.Inhabited.LevelStep

section OutDec

/-- **Transport of the marked output along a correspondence of the marked pairs.**  If `e`, `e'` are
inverse correspondences between the marked pairs of the root `z` with bridge `Y'` and those of `z'`
with bridge `Y''`, carrying the `t`-derivatives of the terms at `0` to each other, the marked outputs
agree. -/
theorem markedOutDec_eq_of_pairs {d L N₁ N₁' m₁ K m₀ : ℕ} [NeZero N₁] [NeZero N₁'] [NeZero L]
    {β β' : Type*} [Fintype β] [Fintype β']
    {reads : β → Set (CTorus d L N₁ m₁ K)} {dom : β → Finset (Set (CTorus d L N₁ m₁ K))}
    {z : RootIdx d L N₁ m₁ K} {T : β → Set (CTorus d L N₁ m₁ K) → ℂ → ℂ}
    {Y' : Set (CTorus d L N₁ m₁ K)}
    {reads' : β' → Set (CTorus d L N₁' m₁ K)} {dom' : β' → Finset (Set (CTorus d L N₁' m₁ K))}
    {z' : RootIdx d L N₁' m₁ K} {T' : β' → Set (CTorus d L N₁' m₁ K) → ℂ → ℂ}
    {Y'' : Set (CTorus d L N₁' m₁ K)}
    (e : β × Set (CTorus d L N₁ m₁ K) → β' × Set (CTorus d L N₁' m₁ K))
    (e' : β' × Set (CTorus d L N₁' m₁ K) → β × Set (CTorus d L N₁ m₁ K))
    (he : ∀ q ∈ (markedIdx reads dom z).filter (fun q => bridge m₀ z q.2 = Y'),
      e q ∈ (markedIdx reads' dom' z').filter (fun q => bridge m₀ z' q.2 = Y''))
    (he' : ∀ q ∈ (markedIdx reads' dom' z').filter (fun q => bridge m₀ z' q.2 = Y''),
      e' q ∈ (markedIdx reads dom z).filter (fun q => bridge m₀ z q.2 = Y'))
    (hl : ∀ q ∈ (markedIdx reads dom z).filter (fun q => bridge m₀ z q.2 = Y'), e' (e q) = q)
    (hr : ∀ q ∈ (markedIdx reads' dom' z').filter (fun q => bridge m₀ z' q.2 = Y''),
      e (e' q) = q)
    (hT : ∀ q ∈ (markedIdx reads dom z).filter (fun q => bridge m₀ z q.2 = Y'),
      deriv (T' (e q).1 (e q).2) 0 = deriv (T q.1 q.2) 0) :
    markedOutDec m₀ reads' dom' z' T' Y'' = markedOutDec m₀ reads dom z T Y' := by
  unfold markedOutDec
  refine Finset.sum_nbij' e' e he' he hr hl fun q hq => ?_
  rw [← hT (e' q) (he' q hq), hr q hq]

end OutDec

section OutDecRec

variable {d L N₁ N₁' m₁ k N : ℕ} [NeZero N₁] [NeZero N₁'] [NeZero L] {ϱ : ℝ}

set_option hygiene false in
local notation "bm" => boxMap ((N₁ * L ^ m₁) * L ^ (k + 1)) ((N₁' * L ^ m₁) * L ^ (k + 1))
set_option hygiene false in
local notation "bm'" => boxMap ((N₁' * L ^ m₁) * L ^ (k + 1)) ((N₁ * L ^ m₁) * L ^ (k + 1))
set_option hygiene false in
local notation "bc" => boxMap (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1)))
  (N₁' * L ^ m₁ * L ^ (k + 1 - (k + 1)))
set_option hygiene false in
local notation "bc'" => boxMap (N₁' * L ^ m₁ * L ^ (k + 1 - (k + 1)))
  (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1)))
set_option hygiene false in
local notation "TA" => Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1)))
set_option hygiene false in
local notation "TB" => Torus d (N₁' * L ^ m₁ * L ^ (k + 1 - (k + 1)))
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
local notation "aK" => cellSide L m₀ m₁ (k + 1)
set_option hygiene false in
local notation "tAz" => (fun μ => ((zv μ : ℤ) : ZMod ((N₁ * L ^ m₁) * L ^ (k + 1))))
set_option hygiene false in
local notation "tBz" => (fun μ => ((zv μ : ℤ) : ZMod ((N₁' * L ^ m₁) * L ^ (k + 1))))
set_option hygiene false in
local notation "τA" => (fun μ => ((((tAz μ).val / L ^ (k + 1) : ℕ)) :
  ZMod (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1)))))
set_option hygiene false in
local notation "τB" => (fun μ => ((((tBz μ).val / L ^ (k + 1) : ℕ)) :
  ZMod (N₁' * L ^ m₁ * L ^ (k + 1 - (k + 1)))))
set_option hygiene false in
local notation "domA" => fun b : TA => polyDom (GA) (LocalCover.nbhdF m₀ (LocalCover.blockSite k b))
  m₀ k (LocalCover.fam m₀ (LocalCover.blockSite k b))
set_option hygiene false in
local notation "domB" => fun b : TB => polyDom (GB) (LocalCover.nbhdF m₀ (LocalCover.blockSite k b))
  m₀ k (LocalCover.fam m₀ (LocalCover.blockSite k b))
set_option hygiene false in
local notation "SA" => hatStepKG (d := d) (L := L) (N := N) (N₁ := N₁) hN2 k m₁ ϱ hk νS β p₁ δ
set_option hygiene false in
local notation "SB" => hatStepKG (d := d) (L := L) (N := N) (N₁ := N₁') hN2 k m₁ ϱ hk νS β p₁ δ

omit [NeZero N₁] [NeZero N₁'] [NeZero L] in
/-- The reverse recentring undoes the recentring on the recentred box. -/
theorem recentred_inv {R : ℕ} (hn' : 2 * R + 1 < (N₁' * L ^ m₁) * L ^ (k + 1))
    (tA : CTorus d L N₁ m₁ (k + 1)) (tB : CTorus d L N₁' m₁ (k + 1)) {x : CTorus d L N₁ m₁ (k + 1)}
    (hx : InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) (x + tA)) :
    bm' ((bm (x + tA) - tB) + tB) - tA = x := by
  rw [sub_add_cancel, boxMap_boxMap hn' hx, add_sub_cancel_right]

omit [NeZero N₁] [NeZero N₁'] [NeZero L] in
/-- The reverse recentring of the recentred set of a set of the recentred box is the set. -/
theorem image_recentred_inv {R : ℕ} (hn' : 2 * R + 1 < (N₁' * L ^ m₁) * L ^ (k + 1))
    (tA : CTorus d L N₁ m₁ (k + 1)) (tB : CTorus d L N₁' m₁ (k + 1))
    {W : Set (CTorus d L N₁ m₁ (k + 1))}
    (hW : ∀ x ∈ W, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) (x + tA)) :
    (fun y => bm' (y + tB) - tA) '' ((fun x => bm (x + tA) - tB) '' W) = W := by
  rw [Set.image_image]
  conv_rhs => rw [← Set.image_id W]
  exact Set.image_congr fun x hx => recentred_inv hn' tA tB (hW x hx)

omit [NeZero N₁] [NeZero N₁'] in
/-- The reverse coarse recentring undoes the coarse recentring on the recentred coarse box. -/
theorem coarse_recentred_inv {R : ℕ} (hn' : 2 * R + L ^ (k + 1) < (N₁' * L ^ m₁) * L ^ (k + 1))
    (tA : CTorus d L N₁ m₁ (k + 1)) (tB : CTorus d L N₁' m₁ (k + 1)) {b : TA}
    (hb : InBox d (R / L ^ (k + 1)) (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1)))
      (b + fun μ => ((((tA μ).val / L ^ (k + 1) : ℕ)) :
        ZMod (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1)))))) :
    bc' ((bc (b + fun μ => ((((tA μ).val / L ^ (k + 1) : ℕ)) :
        ZMod (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))))) -
      fun μ => ((((tB μ).val / L ^ (k + 1) : ℕ)) : ZMod (N₁' * L ^ m₁ * L ^ (k + 1 - (k + 1))))) +
      fun μ => ((((tB μ).val / L ^ (k + 1) : ℕ)) : ZMod (N₁' * L ^ m₁ * L ^ (k + 1 - (k + 1))))) -
      (fun μ => ((((tA μ).val / L ^ (k + 1) : ℕ)) : ZMod (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))))) =
      b := by
  rw [sub_add_cancel, boxMap_boxMap (coarse_margin (N₁ := N₁') hn') hb, add_sub_cancel_right]

/-- **The marked output of a label under the recentring map.** -/
theorem markedOutDec_recentred
    {a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁ : ℝ}
    (hC : FlCore N (GA) (HA) a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
    (hC' : FlCore N (GB) (HB) a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁) (hk : 1 ≤ k)
    (hGA : IsLevel (GA) (k + 1)) (hGB : IsLevel (GB) (k + 1)) (cc : ℂ)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δc : ℝ}
    (hmar : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hαK : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    {F₁ : TA → DecParams (GA) × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      ((GA).Ω 1 × Fin N → ℂ) × ((GA).Ω 1 → ℂ)}
    {F₁' : TB → DecParams (GB) × RawData d L (N₁' * L ^ m₁) (k + 1) N →
      ((GB).Ω 1 × Fin N → ℂ) × ((GB).Ω 1 → ℂ)}
    (hF₁ : ∀ (b : TA) (s : DecParams (GA)) (D : BgData (GA) N),
      (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC (GA) (bgC0 d L N) (c7 d L N BG κ) ν D → ∀ (φ : (GA).Ω 1 × Fin N → ℂ)
        (α : (GA).Ω 1 → ℂ), IsDecBg (GA) (compWeight L a₁) ν (rho4 d L N BG κ) s D φ α →
        F₁ b (s, rawOf D) = (φ, α))
    (hF₁' : ∀ (b : TB) (s : DecParams (GB)) (D : BgData (GB) N),
      (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC (GB) (bgC0 d L N) (c7 d L N BG κ) ν D → ∀ (φ : (GB).Ω 1 × Fin N → ℂ)
        (α : (GB).Ω 1 → ℂ), IsDecBg (GB) (compWeight L a₁) ν (rho4 d L N BG κ) s D φ α →
        F₁' b (s, rawOf D) = (φ, α))
    {Sol : TA → Dec2.DecParams (coverOf (GA)) × Edat (HA) N →
      ((HA).Ω 1 × Fin N → ℂ) × ((HA).Ω 1 → ℂ)}
    {Sol' : TB → Dec2.DecParams (coverOf (GB)) × Edat (HB) N →
      ((HB).Ω 1 × Fin N → ℂ) × ((HB).Ω 1 → ℂ)}
    (hSol : ∀ (b : TA) (p : Dec2.DecParams (coverOf (GA)) × Edat (HA) N),
      (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM (HA) N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2 →
        (Sol b p).1 = dphi (HA) (Dec2.decG (coverOf (GA)) (HA) (compWeight L a₁) ν p.1) p.2.2.1
          p.2.1 (pertSource (HA) (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol b p).2 ∧
        Dec2.DecFixed (coverOf (GA)) (HA) (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
          (pertSource (HA) (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol b p).2 ∧
        Small (HA) (Sol b p).2 (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
        Small (HA) (Sol b p).2 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        SupBounds (HA) (Sol b p).1 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        (∀ δα' : (HA).Ω 1 → ℂ, Small (HA) δα' (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf (GA)) (HA) (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
            (pertSource (HA) (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol b p).2))
    (hSol' : ∀ (b : TB) (p : Dec2.DecParams (coverOf (GB)) × Edat (HB) N),
      (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM (HB) N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2 →
        (Sol' b p).1 = dphi (HB) (Dec2.decG (coverOf (GB)) (HB) (compWeight L a₁) ν p.1) p.2.2.1
          p.2.1 (pertSource (HB) (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol' b p).2 ∧
        Dec2.DecFixed (coverOf (GB)) (HB) (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
          (pertSource (HB) (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol' b p).2 ∧
        Small (HB) (Sol' b p).2 (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
        Small (HB) (Sol' b p).2 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        SupBounds (HB) (Sol' b p).1 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        (∀ δα' : (HB).Ω 1 → ℂ, Small (HB) δα' (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf (GB)) (HB) (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
            (pertSource (HB) (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol' b p).2))
    {m₀ : ℕ} (hd : 0 < d) (hL : 2 ≤ L) (hm₀ : 1 ≤ m₀) (hm₁ : 1 ≤ m₁)
    (hN : L ^ m₀ ∣ N₁) (hN' : L ^ m₀ ∣ N₁')
    (zv : Fin d → ℤ) (hz : ∀ μ, ((cellSide L m₀ m₁ (k + 1) : ℕ) : ℤ) ∣ zv μ)
    (z : TA) {R : ℕ} (hw : L * aK ≤ 2 * R + 1)
    (hn20 : 20 * R + 20 < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hn20' : 20 * R + 20 < (N₁' * L ^ m₁) * L ^ (k + 1))
    (hzc : InBox d (R / L ^ (k + 1)) (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) (z + τA))
    (hroot : ∀ x ∈ rootSet m₀ z, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) (x + tAz))
    {Y' : Set (CTorus d L N₁ m₁ (k + 1))}
    (hY'R : ∀ y ∈ Y', InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) (y + tAz))
    {D : BgData (GA) N} {D' : BgData (GB) N}
    (hD : XiCData (GA) (compWeight L a₁) ν (k + 1) 1 eps D)
    (hD' : XiCData (GB) (compWeight L a₁) ν (k + 1) 1 eps D')
    (hraw : RawBoxAgree {w | InBox d (R + 3 * L ^ (k + 1)) ((N₁ * L ^ m₁) * L ^ (k + 1)) w}
      (symRaw (Equiv.addRight tAz) (rawOf D)) (symRaw (Equiv.addRight tBz) (rawOf D')))
    (hN2 : 2 ≤ N) (νS β p₁ δ : ℝ) {ρ : ℝ} (hρ : 0 < ρ)
    (hp : 0 < (SA).p₁) (hp' : 0 < (SB).p₁)
    (Φ : ∀ c, ((SA).blockSplit m₀ hp).Ωb c) (Φ' : ∀ c, ((SB).blockSplit m₀ hp').Ωb c)
    (hΦ : ∀ x, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) (x + tAz) →
      Φ' ((SB).cellOf m₀ (unitPt (SB).hG' (bm (x + tAz) - tBz)))
        ⟨unitPt (SB).hG' (bm (x + tAz) - tBz), rfl⟩ =
        Φ ((SA).cellOf m₀ (unitPt (SA).hG' x)) ⟨unitPt (SA).hG' x, rfl⟩)
    {um : ℂ} (hum : ‖um‖ * markedRad d L N k a₁ κ ρ cc < δ₁) (βc : ℂ) :
    markedOutDec m₀ (fun _ : TB => (Set.univ : Set (CTorus d L N₁' m₁ (k + 1)))) (domB)
        (bc (z + τA) - τB)
        (decMarkCorrTerm (SB) (fun b => LocalCover.nbhdF m₀ (LocalCover.blockSite k b))
          (fun _ => k) (fun b => LocalCover.fam m₀ (LocalCover.blockSite k b)) m₀ a₁ ν cc F₁' Sol'
          ((SB).blockU (bc (z + τA) - τB)) ρ hp' βc (rawOf D') um Φ')
        ((fun x => bm (x + tAz) - tBz) '' Y') =
      markedOutDec m₀ (fun _ : TA => (Set.univ : Set (CTorus d L N₁ m₁ (k + 1)))) (domA) z
        (decMarkCorrTerm (SA) (fun b => LocalCover.nbhdF m₀ (LocalCover.blockSite k b))
          (fun _ => k) (fun b => LocalCover.fam m₀ (LocalCover.blockSite k b)) m₀ a₁ ν cc F₁ Sol
          ((SA).blockU z) ρ hp βc (rawOf D) um Φ) Y' := by
  classical
  obtain ⟨hnF, hn1, -, hnH⟩ := gapMargins_of_width hL hm₀ hm₁ hw hn20
  obtain ⟨hnF', hn1', -, hnH'⟩ := gapMargins_of_width hL hm₀ hm₁ hw hn20'
  have hK1 : 1 ≤ L ^ (k + 1) := Nat.one_le_pow _ _ (Nat.pos_of_ne_zero (NeZero.ne L))
  have hsa : aK ≤ L * aK := cellSide_le_mul
  have hKa : L ^ (k + 1) ≤ L * aK := by
    unfold cellSide
    calc L ^ (k + 1) ≤ L ^ ((k + 1) + m₀ + m₁) := Nat.pow_le_pow_right (by omega) (by omega)
      _ ≤ L * L ^ ((k + 1) + m₀ + m₁) := Nat.le_mul_of_pos_left _ (by omega)
  have htA : ∀ μ, L ^ ((k + 1) + m₀ + m₁) ∣ (tAz μ).val := fun μ =>
    dvd_val_intCast (cellSide_dvd hN le_rfl) (hz μ)
  have htB : ∀ μ, L ^ ((k + 1) + m₀ + m₁) ∣ (tBz μ).val := fun μ =>
    dvd_val_intCast (cellSide_dvd hN' le_rfl) (hz μ)
  have htA1 : ∀ μ, L ^ (k + 1) ∣ (tAz μ).val := fun μ => (pow_dvd_pow L (by omega)).trans (htA μ)
  have htB1 : ∀ μ, L ^ (k + 1) ∣ (tBz μ).val := fun μ => (pow_dvd_pow L (by omega)).trans (htB μ)
  have hσB := genSymm_mem_pavingSymGroup (GenSymm.translate (n := k + 1) (m₀ := m₀) tBz htB)
  have hσA := genSymm_mem_pavingSymGroup (GenSymm.translate (n := k + 1) (m₀ := m₀) tAz htA)
  have hcm := coarse_margin (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) (r := R) (by omega)
  have hcm' := coarse_margin (L := L) (N₁ := N₁') (m₁ := m₁) (k := k) (r := R) (by omega)
  -- the root of the second torus
  have hzB : InBox d (R / L ^ (k + 1)) (N₁' * L ^ m₁ * L ^ (k + 1 - (k + 1)))
      ((bc (z + τA) - τB) + τB) := by
    rw [sub_add_cancel]; exact inBox_boxMap hcm' hzc
  have hzz : bc' ((bc (z + τA) - τB) + τB) - τA = z :=
    coarse_recentred_inv (by omega) tAz tBz hzc
  have hrootB : ∀ x ∈ rootSet m₀ (bc (z + τA) - τB),
      InBox d R ((N₁' * L ^ m₁) * L ^ (k + 1)) (x + tBz) := by
    intro x hx
    have hrA : ∀ y ∈ box (rootCube (m₀ := m₀) (z + τA)).1 aK,
        InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) y := by
      intro y hy
      have hy' : y ∈ rootSet m₀ (z + τA) := hy
      rw [← rootAct_addRight tAz htA1 z, rootSet_rootAct hN hσA] at hy'
      obtain ⟨w, hw', rfl⟩ := hy'
      exact hroot w hw'
    have hx' : x + tBz ∈ rootSet m₀ (bc (z + τA)) := by
      have := rootSet_rootAct hN' hσB (bc (z + τA) - τB)
      rw [rootAct_addRight tBz htB1, sub_add_cancel] at this
      rw [this]
      exact ⟨x, hx, rfl⟩
    have hcube := cubeMap_rootCube (r := R) hN hN' (z + τA) hzc (Nat.mul_div_le R _) (by omega) hrA
    unfold rootSet at hx'
    rw [← hcube, cubeMap_val, ← image_box_boxMap (by omega) (cellSide_pos m₀ m₁ _) hrA] at hx'
    obtain ⟨y, hy, hyx⟩ := hx'
    rw [← hyx]
    exact inBox_boxMap (by omega) (hrA y hy)
  -- the pairs lie in the recentred boxes
  have hpairA : ∀ q ∈ (markedIdx (fun _ : TA => (Set.univ : Set (CTorus d L N₁ m₁ (k + 1))))
      (domA) z).filter (fun q => bridge m₀ z q.2 = Y'),
      (∀ y ∈ q.2, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) (y + tAz)) ∧
      (∀ x ∈ LocalCover.nbhd m₀ (LocalCover.blockSite k q.1),
        InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) (x + tAz)) := by
    intro q hq
    obtain ⟨hq1, hbr⟩ := Finset.mem_filter.1 hq
    have hYd := ((mem_markedIdx (b := q.1) (Y := q.2)).1 hq1).1
    have hYR : ∀ y ∈ q.2, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) (y + tAz) :=
      fun y hy => hY'R y (hbr ▸ subset_bridge m₀ z q.2 hy)
    exact ⟨hYR, fun x hx => hYR x (nbhd_subset_of_mem_polyDom hN _ hYd hx)⟩
  have hY''R : ∀ y ∈ (fun x => bm (x + tAz) - tBz) '' Y',
      InBox d R ((N₁' * L ^ m₁) * L ^ (k + 1)) (y + tBz) := by
    rintro _ ⟨x, hx, rfl⟩
    rw [sub_add_cancel]
    exact inBox_boxMap (by omega) (hY'R x hx)
  have hpairB : ∀ q ∈ (markedIdx (fun _ : TB => (Set.univ : Set (CTorus d L N₁' m₁ (k + 1))))
      (domB) (bc (z + τA) - τB)).filter
        (fun q => bridge m₀ (bc (z + τA) - τB) q.2 = (fun x => bm (x + tAz) - tBz) '' Y'),
      (∀ y ∈ q.2, InBox d R ((N₁' * L ^ m₁) * L ^ (k + 1)) (y + tBz)) ∧
      (∀ x ∈ LocalCover.nbhd m₀ (LocalCover.blockSite k q.1),
        InBox d R ((N₁' * L ^ m₁) * L ^ (k + 1)) (x + tBz)) := by
    intro q hq
    obtain ⟨hq1, hbr⟩ := Finset.mem_filter.1 hq
    have hYd := ((mem_markedIdx (b := q.1) (Y := q.2)).1 hq1).1
    have hYR : ∀ y ∈ q.2, InBox d R ((N₁' * L ^ m₁) * L ^ (k + 1)) (y + tBz) :=
      fun y hy => hY''R y (hbr ▸ subset_bridge m₀ _ q.2 hy)
    exact ⟨hYR, fun x hx => hYR x (nbhd_subset_of_mem_polyDom hN' _ hYd hx)⟩
  have hYY : (fun y => bm' (y + tBz) - tAz) '' ((fun x => bm (x + tAz) - tBz) '' Y') = Y' :=
    image_recentred_inv (by omega) tAz tBz hY'R
  have hbA : ∀ b : TA, (∀ x ∈ LocalCover.nbhd m₀ (LocalCover.blockSite k b),
      InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) (x + tAz)) →
      InBox d (R / L ^ (k + 1)) (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) (b + τA) := by
    intro b hb
    have hx : InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) (LocalCover.blockSite k b + tAz) :=
      hb _ (by rw [← LocalCover.coe_nbhdF]; exact LocalCover.mem_nbhdF_self m₀ _)
    rw [← blockSite_add_coarse tAz htA1 b] at hx
    exact inBox_coarse_of_blockSite _ hx
  have hbB : ∀ b : TB, (∀ x ∈ LocalCover.nbhd m₀ (LocalCover.blockSite k b),
      InBox d R ((N₁' * L ^ m₁) * L ^ (k + 1)) (x + tBz)) →
      InBox d (R / L ^ (k + 1)) (N₁' * L ^ m₁ * L ^ (k + 1 - (k + 1))) (b + τB) := by
    intro b hb
    have hx : InBox d R ((N₁' * L ^ m₁) * L ^ (k + 1)) (LocalCover.blockSite k b + tBz) :=
      hb _ (by rw [← LocalCover.coe_nbhdF]; exact LocalCover.mem_nbhdF_self m₀ _)
    rw [← blockSite_add_coarse tBz htB1 b] at hx
    exact inBox_coarse_of_blockSite _ hx
  refine markedOutDec_eq_of_pairs
    (fun q => (bc (q.1 + τA) - τB, (fun x => bm (x + tAz) - tBz) '' q.2))
    (fun q' => (bc' (q'.1 + τB) - τA, (fun y => bm' (y + tBz) - tAz) '' q'.2)) ?_ ?_ ?_ ?_ ?_
  · intro q hq
    obtain ⟨hYR, hbR⟩ := hpairA q hq
    obtain ⟨hq1, hbr⟩ := Finset.mem_filter.1 hq
    exact Finset.mem_filter.2 ((markedPair_recentred_iff (ϱ := ϱ) hGA hGB hN hN' tAz tBz htA htB
      hn1 hn1' hnF hnF' hnH hnH' z hzc (Nat.mul_div_le R _) hroot hY'R q.1 q.2 hYR hbR).2
      ⟨hq1, hbr⟩)
  · intro q' hq'
    obtain ⟨hYR, hbR⟩ := hpairB q' hq'
    obtain ⟨hq1, hbr⟩ := Finset.mem_filter.1 hq'
    have h := (markedPair_recentred_iff (ϱ := ϱ) hGB hGA hN' hN tBz tAz htB htA hn1' hn1 hnF' hnF
      hnH' hnH (bc (z + τA) - τB) hzB (Nat.mul_div_le R _) hrootB hY''R q'.1 q'.2 hYR hbR).2
      ⟨hq1, hbr⟩
    rw [hzz, hYY] at h
    exact Finset.mem_filter.2 h
  · intro q hq
    obtain ⟨hYR, hbR⟩ := hpairA q hq
    exact Prod.ext (coarse_recentred_inv (by omega) tAz tBz (hbA q.1 hbR))
      (image_recentred_inv (by omega) tAz tBz hYR)
  · intro q' hq'
    obtain ⟨hYR, hbR⟩ := hpairB q' hq'
    exact Prod.ext (coarse_recentred_inv (N₁ := N₁') (N₁' := N₁) (by omega) tBz tAz (hbB q'.1 hbR))
      (image_recentred_inv (N₁ := N₁') (N₁' := N₁) (by omega) tBz tAz hYR)
  · intro q hq
    obtain ⟨hYR, hbR⟩ := hpairA q hq
    have hbb := blockSite_recentred (r := R) tAz tBz htA1 htB1 q.1 (hbA q.1 hbR)
      (Nat.mul_div_le R _) (by omega)
    refine (deriv_decMarkCorrTerm (SB) F₁' Sol' ρ hp' βc (rawOf D') um Φ' _ _).trans ?_
    refine Eq.trans ?_ (deriv_decMarkCorrTerm (SA) F₁ Sol ρ hp βc (rawOf D) um Φ q.1 q.2).symm
    refine congrArg (fun x => -βc * x) ?_
    exact decMarkCorr_rootBlock_recentred hC hC' hk hGA hGB cc hMX hmar hαK hsm (hF₁ q.1)
      (hF₁' _) (hSol q.1) (hSol' _) hd hL hm₀ hm₁ hN hN' zv hz q.1 _ hbb hbR hYR hn20 hn20' hD hD'
      hraw hN2 νS β p₁ δ hρ hp hp' Φ Φ' hΦ
      (fun y hy => (mem_blockU_iff_unitBlock1 (SB) _ _).trans ((rootMask_recentred hGA hGB tAz tBz
        htA1 htB1 (by omega) (by omega) z hzc (Nat.mul_div_le R _) hy).trans
        (mem_blockU_iff_unitBlock1 (SA) _ _).symm)) hum

/-- **The marks of the energy coefficient under the recentring map.**  At a bridge label `Y′` of the
root `z` whose translate by `tA` lies in the box, and the label `φ '' Y′` of the root
`bc (z + τA) - τB`, for parameters in the charts whose raw data agree after the translations, block
variables agreeing at corresponding unit points and `‖u‖ < 17/16`, the marks `e1MarkGParamG` of the
two steps are equal (`markedOutDec_recentred` under the guards of `e1MarkGParamG_of_mem`). -/
theorem e1MarkGParamG_recentred
    {c BG κ eps Kc Cx c₂ BG₂ δ₁ : ℝ} (hN2 : 2 ≤ N) (hk : 1 ≤ k) (νS β p₁ δ : ℝ)
    (hC : FlCore N (GA) (HA) 1 νS c BG κ eps Kc Cx c₂ BG₂ δ₁)
    (hC' : FlCore N (GB) (HB) 1 νS c BG κ eps Kc Cx c₂ BG₂ δ₁)
    (hGA : IsLevel (GA) (k + 1)) (hGB : IsLevel (GB) (k + 1))
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δc : ℝ}
    (hmar : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hαK : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    {F₁ : TA → DecParams (GA) × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      ((GA).Ω 1 × Fin N → ℂ) × ((GA).Ω 1 → ℂ)}
    {F₁' : TB → DecParams (GB) × RawData d L (N₁' * L ^ m₁) (k + 1) N →
      ((GB).Ω 1 × Fin N → ℂ) × ((GB).Ω 1 → ℂ)}
    (hF₁ : ∀ (b : TA) (s : DecParams (GA)) (D : BgData (GA) N),
      (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC (GA) (bgC0 d L N) (c7 d L N BG κ) νS D → ∀ (φ : (GA).Ω 1 × Fin N → ℂ)
        (α : (GA).Ω 1 → ℂ), IsDecBg (GA) (compWeight L 1) νS (rho4 d L N BG κ) s D φ α →
        F₁ b (s, rawOf D) = (φ, α))
    (hF₁' : ∀ (b : TB) (s : DecParams (GB)) (D : BgData (GB) N),
      (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC (GB) (bgC0 d L N) (c7 d L N BG κ) νS D → ∀ (φ : (GB).Ω 1 × Fin N → ℂ)
        (α : (GB).Ω 1 → ℂ), IsDecBg (GB) (compWeight L 1) νS (rho4 d L N BG κ) s D φ α →
        F₁' b (s, rawOf D) = (φ, α))
    {Sol : TA → Dec2.DecParams (coverOf (GA)) × Edat (HA) N →
      ((HA).Ω 1 × Fin N → ℂ) × ((HA).Ω 1 → ℂ)}
    {Sol' : TB → Dec2.DecParams (coverOf (GB)) × Edat (HB) N →
      ((HB).Ω 1 × Fin N → ℂ) × ((HB).Ω 1 → ℂ)}
    (hSol : ∀ (b : TA) (p : Dec2.DecParams (coverOf (GA)) × Edat (HA) N),
      (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM (HA) N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2 →
        (Sol b p).1 = dphi (HA) (Dec2.decG (coverOf (GA)) (HA) (compWeight L 1) νS p.1) p.2.2.1
          p.2.1 (pertSource (HA) (compWeight L 1) p.2.2.2.1 p.2.2.2.2) (Sol b p).2 ∧
        Dec2.DecFixed (coverOf (GA)) (HA) (compWeight L 1) νS p.1 false p.2.2.1 p.2.1
          (pertSource (HA) (compWeight L 1) p.2.2.2.1 p.2.2.2.2) (Sol b p).2 ∧
        Small (HA) (Sol b p).2 (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
        Small (HA) (Sol b p).2 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        SupBounds (HA) (Sol b p).1 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        (∀ δα' : (HA).Ω 1 → ℂ, Small (HA) δα' (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf (GA)) (HA) (compWeight L 1) νS p.1 false p.2.2.1 p.2.1
            (pertSource (HA) (compWeight L 1) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol b p).2))
    (hSol' : ∀ (b : TB) (p : Dec2.DecParams (coverOf (GB)) × Edat (HB) N),
      (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM (HB) N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2 →
        (Sol' b p).1 = dphi (HB) (Dec2.decG (coverOf (GB)) (HB) (compWeight L 1) νS p.1) p.2.2.1
          p.2.1 (pertSource (HB) (compWeight L 1) p.2.2.2.1 p.2.2.2.2) (Sol' b p).2 ∧
        Dec2.DecFixed (coverOf (GB)) (HB) (compWeight L 1) νS p.1 false p.2.2.1 p.2.1
          (pertSource (HB) (compWeight L 1) p.2.2.2.1 p.2.2.2.2) (Sol' b p).2 ∧
        Small (HB) (Sol' b p).2 (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
        Small (HB) (Sol' b p).2 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        SupBounds (HB) (Sol' b p).1 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        (∀ δα' : (HB).Ω 1 → ℂ, Small (HB) δα' (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf (GB)) (HB) (compWeight L 1) νS p.1 false p.2.2.1 p.2.1
            (pertSource (HB) (compWeight L 1) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol' b p).2))
    (hd : 0 < d) (hL : 2 ≤ L) (hm₁ : 1 ≤ m₁) (hN : L ^ 1 ∣ N₁) (hN' : L ^ 1 ∣ N₁')
    (zv : Fin d → ℤ) (hz : ∀ μ, ((cellSide L 1 m₁ (k + 1) : ℕ) : ℤ) ∣ zv μ)
    (z : TA) {R : ℕ} (hw : L * cellSide L 1 m₁ (k + 1) ≤ 2 * R + 1)
    (hn20 : 20 * R + 20 < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hn20' : 20 * R + 20 < (N₁' * L ^ m₁) * L ^ (k + 1))
    (hzc : InBox d (R / L ^ (k + 1)) (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) (z + τA))
    (hroot : ∀ x ∈ rootSet 1 z, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) (x + tAz))
    (i : {Y' // Y' ∈ bridgeFamily 1 (fun _ => Set.univ) (e1DomG (SA)) z})
    (i' : {Y' // Y' ∈ bridgeFamily 1 (fun _ => Set.univ) (e1DomG (SB)) (bc (z + τA) - τB)})
    (hi : i'.1 = (fun x => bm (x + tAz) - tBz) '' i.1)
    (hiR : ∀ y ∈ i.1, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) (y + tAz))
    (θ : physParam N (SA)) (θ' : physParam N (SB))
    (hθ : (θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) ∈
      XiCRaw (GA) (compWeight L 1) νS (k + 1) 1 eps)
    (hθ' : (θ'.1 : RawData d L (N₁' * L ^ m₁) (k + 1) N) ∈
      XiCRaw (GB) (compWeight L 1) νS (k + 1) 1 eps)
    (hraw : RawBoxAgree {w | InBox d (R + 3 * L ^ (k + 1)) ((N₁ * L ^ m₁) * L ^ (k + 1)) w}
      (symRaw (Equiv.addRight tAz) (θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N))
      (symRaw (Equiv.addRight tBz) (θ'.1 : RawData d L (N₁' * L ^ m₁) (k + 1) N)))
    {ρ : ℝ} (hρ : 0 < ρ) (hp : 0 < (SA).p₁) (hp' : 0 < (SB).p₁)
    (Φ : ∀ c, ((SA).blockSplit 1 hp).Ωb c) (Φ' : ∀ c, ((SB).blockSplit 1 hp').Ωb c)
    (hΦ : ∀ x, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) (x + tAz) →
      Φ' ((SB).cellOf 1 (unitPt (SB).hG' (bm (x + tAz) - tBz)))
        ⟨unitPt (SB).hG' (bm (x + tAz) - tBz), rfl⟩ =
        Φ ((SA).cellOf 1 (unitPt (SA).hG' x)) ⟨unitPt (SA).hG' x, rfl⟩)
    {u : ℂ} (hu : ‖u‖ < (17 / 16 : ℝ))
    (hum : ‖u‖ * markedRad d L N k 1 κ ρ (((SA).betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) < δ₁) :
    e1MarkGParamG (SB) F₁' Sol' ρ hp' (bc (z + τA) - τB) eps θ' i' u Φ' =
      e1MarkGParamG (SA) F₁ Sol ρ hp z eps θ i u Φ := by
  rw [e1MarkGParamG_of_mem (SB) F₁' Sol' ρ hp' _ eps θ' i' u Φ' hθ' hu,
    e1MarkGParamG_of_mem (SA) F₁ Sol ρ hp z eps θ i u Φ hθ hu]
  obtain ⟨D, hD, hDθ⟩ := hθ
  obtain ⟨D', hD', hDθ'⟩ := hθ'
  rw [hDθ] at hraw ⊢
  rw [hDθ'] at hraw ⊢
  rw [hi]
  exact markedOutDec_recentred hC hC' hk hGA hGB _ hMX hmar hαK hsm hF₁ hF₁' hSol hSol' hd hL le_rfl
    hm₁ hN hN' zv hz z hw hn20 hn20' hzc hroot hiR hD hD' hraw hN2 νS β p₁ δ hρ hp hp' Φ Φ' hΦ hum _

end OutDecRec

end Balaban.Polymer.TwoTorusStep
