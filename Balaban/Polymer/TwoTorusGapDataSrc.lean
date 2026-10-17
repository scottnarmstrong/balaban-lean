/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Polymer.TwoTorusObsSourceSite
public import Balaban.Polymer.TwoTorusGapStepObsEv
public import Balaban.Polymer.TwoTorusGapStepObsAct
public import Balaban.Polymer.TwoTorusGapStepObsBlocks
public import Balaban.Polymer.TwoTorusObsSource

/-!
# The source part of the activities of the observable under the recentring map

`dirTerm_siteEv_recentred`, `sourceSum_recentred`, `labelActSource_recentred`: the recentred analogues
of `dirTerm_siteEv_twoTorus`, `sourceSum_twoTorus`, `labelActSource_twoTorus`, for `hAeqθ`.
-/

@[expose] public section

noncomputable section

open scoped Classical

namespace Balaban.Polymer.TwoTorusStep

open Balaban Balaban.Localization Balaban.Fluctuation Balaban.SmallField Balaban.SmallField.Def6
  Balaban.Background Balaban.Analysis Balaban.Polymer Balaban.Multiscale Filter Topology

section SrcRec

open Balaban.Inhabited Balaban.Inhabited.LevelStep

variable {d L N₁ N₁' m₁ k N : ℕ} [NeZero N₁] [NeZero N₁'] [NeZero L] {ϱ : ℝ}

set_option hygiene false in
local notation "bm" => boxMap ((N₁ * L ^ m₁) * L ^ (k + 1)) ((N₁' * L ^ m₁) * L ^ (k + 1))
set_option hygiene false in
local notation "bm'" => boxMap ((N₁' * L ^ m₁) * L ^ (k + 1)) ((N₁ * L ^ m₁) * L ^ (k + 1))
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
local notation "ρ₁" => R + (3 * L ^ (k + 1 + m₁) + 3 * L ^ (k + 1 + 2)) + L ^ (k + 1 + m₁)
set_option hygiene false in
local notation "XA" => (↑(LocalCover.nbhdF m₀ xs) : Set (CTorus d L N₁ m₁ (k + 1)))
set_option hygiene false in
local notation "XB" => (↑(LocalCover.nbhdF m₀ xs') : Set (CTorus d L N₁' m₁ (k + 1)))

/-- **The terms `dirTerm (Ev Y) …` of the site functional under the recentring map.** -/
theorem dirTerm_siteEv_recentred
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
    (tA : CTorus d L N₁ m₁ (k + 1)) (tB : CTorus d L N₁' m₁ (k + 1))
    (htAz : tA = (fun μ => ((z μ : ℤ) : ZMod ((N₁ * L ^ m₁) * L ^ (k + 1)))))
    (htBz : tB = (fun μ => ((z μ : ℤ) : ZMod ((N₁' * L ^ m₁) * L ^ (k + 1)))))
    (xs : CTorus d L N₁ m₁ (k + 1)) (xs' : CTorus d L N₁' m₁ (k + 1))
    (hxs : xs' + tB = bm (xs + tA)) (iy : Fin N) {R : ℕ}
    (hX₁R : ∀ x ∈ LocalCover.nbhd m₀ xs, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) (x + tA))
    {Y : Set (CTorus d L N₁ m₁ (k + 1))}
    (hYR : ∀ y ∈ Y, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) (y + tA))
    (hn20 : 20 * R + 20 < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hn20' : 20 * R + 20 < (N₁' * L ^ m₁) * L ^ (k + 1))
    {D : BgData (GA) N} {D' : BgData (GB) N}
    (hD : XiCData (GA) (compWeight L a₁) ν (k + 1) 1 eps D)
    (hD' : XiCData (GB) (compWeight L a₁) ν (k + 1) 1 eps D')
    (hraw : RawBoxAgree {w | InBox d (R + 3 * L ^ (k + 1)) ((N₁ * L ^ m₁) * L ^ (k + 1)) w}
      (symRaw (Equiv.addRight tA) (rawOf D))
      (symRaw (Equiv.addRight tB) (rawOf D')))
    {x₀ w : unitPts (GA) × Fin N → ℂ} {x₀' w' : unitPts (GB) × Fin N → ℂ} {ρ₀ : ℝ}
    (hx₀ : ∀ p, ‖x₀ p‖ ≤ ρ₀) (hw : ∀ p, ‖w p‖ ≤ ρ₀) (hx₀' : ∀ p, ‖x₀' p‖ ≤ ρ₀)
    (hw' : ∀ p, ‖w' p‖ ≤ ρ₀) (hρ₀ : 2 * ρ₀ ≤ cψ)
    (hhx : ∀ x, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) (x + tA) →
      ∀ i, x₀' (unitPt hGB (bm (x + tA) - tB), i) = x₀ (unitPt hGA x, i))
    (hhw : ∀ x, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) (x + tA) →
      ∀ i, w' (unitPt hGB (bm (x + tA) - tB), i) = w (unitPt hGA x, i))
    (hrad : markedRad d L N k a₁ κ cψ cc < δ₁)
    {Ev : Set (CTorus d L N₁ m₁ (k + 1)) →
      RawData d L (N₁ * L ^ m₁) (k + 1) N × (unitPts (GA) × Fin N → ℂ) → ℂ}
    {Ev' : Set (CTorus d L N₁' m₁ (k + 1)) →
      RawData d L (N₁' * L ^ m₁) (k + 1) N × (unitPts (GB) × Fin N → ℂ) → ℂ}
    (hEv : Ev = evTerm (fun i : ParIdx (GA) (XA) => i.1.1) (GA) m₀
        (X1 (GA) m₀ k (LocalCover.fam m₀ xs))
        (fun u s => siteFun (GA) (HA) xs iy (F₁ (extParams (GA) (XA) s, u.1))
          (Sol (extParams (GA) (XA) s,
            flEdat (GA) (HA) (F₁ (extParams (GA) (XA) s, u.1))
              u.1.1 (hatPsiF (GA) a₁ ν hGA cc F₁
                (extParams (GA) (XA) s) u.1 u.2))).1
          (u.1, hatPsiF (GA) a₁ ν hGA cc F₁
            (extParams (GA) (XA) s) u.1 u.2)))
    (hEv' : Ev' = evTerm (fun i : ParIdx (GB) (XB) => i.1.1) (GB)
        m₀ (X1 (GB) m₀ k (LocalCover.fam m₀ xs'))
        (fun u s => siteFun (GB) (HB) xs' iy
          (F₁' (extParams (GB) (XB) s, u.1))
          (Sol' (extParams (GB) (XB) s,
            flEdat (GB) (HB) (F₁' (extParams (GB)
              (XB) s, u.1)) u.1.1
              (hatPsiF (GB) a₁ ν hGB cc F₁'
                (extParams (GB) (XB) s) u.1 u.2))).1
          (u.1, hatPsiF (GB) a₁ ν hGB cc F₁'
            (extParams (GB) (XB) s) u.1 u.2)))
    (hanEv : AnalyticOnNhd ℂ (Ev Y) (XiCRaw (GA) (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
      {ψh : unitPts (GA) × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ}))
    (hanEv' : AnalyticOnNhd ℂ (Ev' ((fun x => bm (x + tA) - tB) '' Y)) (XiCRaw (GB) (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
      {ψh : unitPts (GB) × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ}))
    {σ : ℂ} (hσ : ‖σ‖ ≤ 1) :
    dirTerm (Ev' ((fun x => bm (x + tA) - tB) '' Y)) (fun _ => (1 : ℂ)) x₀' w' σ (rawOf D') =
      dirTerm (Ev Y) (fun _ => (1 : ℂ)) x₀ w σ (rawOf D) := by
  subst htAz htBz
  have hst : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 → ‖σ * (t : ℂ)‖ ≤ 1 := fun t ht => by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg ht.1]
    nlinarith [norm_nonneg σ, ht.2]
  have hpt : ∀ {U : Type} (z : U × Fin N → ℂ), (∀ p, ‖z p‖ ≤ ρ₀) → ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 →
      ∀ p, ‖((σ * (t : ℂ)) • z) p‖ ≤ cψ := fun z hz t ht p => by
    rw [Pi.smul_apply, smul_eq_mul, norm_mul]
    calc ‖σ * (t : ℂ)‖ * ‖z p‖ ≤ 1 * ρ₀ :=
          mul_le_mul (hst t ht) (hz p) (norm_nonneg _) zero_le_one
      _ ≤ cψ := by linarith
  refine dirTerm_eq_of_line _ _ _ x₀ w x₀' w' σ _ _ (fun t ht => ?_) (fun t ht => ?_)
    (fun t ht τ hτ => ?_)
  · exact (hanEv (rawOf D, (σ * (t : ℂ)) • x₀) ⟨⟨D, hD, rfl⟩, hpt x₀ hx₀ t ht⟩).differentiableAt
  · exact (hanEv' (rawOf D', (σ * (t : ℂ)) • x₀') ⟨⟨D', hD', rfl⟩, hpt x₀' hx₀' t ht⟩).differentiableAt
  · have hb : ∀ {U : Type} (z z' : U × Fin N → ℂ), (∀ p, ‖z p‖ ≤ ρ₀) → (∀ p, ‖z' p‖ ≤ ρ₀) →
        ∀ p, ‖((σ * (t : ℂ)) • z + τ • z') p‖ ≤ cψ := fun z z' hz hz' p =>
      (norm_ray_add_le hz hz' (hst t ht) hτ p).trans hρ₀
    rw [hEv, hEv']
    refine siteEv_recentred hC hC' hk hGA hGB cc hcψ hMX hmar hαK hsm hF₁ hF₁' hSol hSol' hd hL hm₀ hm₁
      hN hN' z hz xs xs' iy hxs hX₁R hYR hn20 hn20' hD hD' hraw (hb x₀ w hx₀ hw) (hb x₀' w' hx₀' hw')
      (fun x hx i => ?_) hrad
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hhx x hx i, hhw x hx i]

omit [NeZero N₁] [NeZero N₁'] in
theorem srcRec_inv {R : ℕ} {m₀ : ℕ}
    (hnF' : 2 * R + 5 * (L * cellSide L m₀ m₁ (k + 1)) < (N₁' * L ^ m₁) * L ^ (k + 1))
    (tA : CTorus d L N₁ m₁ (k + 1)) (tB : CTorus d L N₁' m₁ (k + 1))
    {Y : Set (CTorus d L N₁ m₁ (k + 1))}
    (hYR : ∀ y ∈ Y, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) (y + tA)) :
    ∀ y ∈ Y, bm' (bm (y + tA) - tB + tB) - tA = y := fun y hy => by
  have hc1 : 1 ≤ 5 * (L * cellSide L m₀ m₁ (k + 1)) :=
    Nat.succ_le_of_lt (Nat.mul_pos (by norm_num)
      (Nat.mul_pos (Nat.pos_of_ne_zero (NeZero.ne L)) (cellSide_pos m₀ m₁ (k + 1))))
  have hsB : 2 * R + 1 < (N₁' * L ^ m₁) * L ^ (k + 1) := by omega
  rw [sub_add_cancel, boxMap_boxMap hsB (hYR y hy)]; abel

theorem srcRec_fwd     {m₀ R : ℕ} (hGA : IsLevel (GA) (k + 1)) (hGB : IsLevel (GB) (k + 1))
    (hN : L ^ m₀ ∣ N₁) (hN' : L ^ m₀ ∣ N₁')
    (tA : CTorus d L N₁ m₁ (k + 1)) (tB : CTorus d L N₁' m₁ (k + 1))
    (htA : ∀ μ, L ^ ((k + 1) + m₀ + m₁) ∣ (tA μ).val)
    (htB : ∀ μ, L ^ ((k + 1) + m₀ + m₁) ∣ (tB μ).val)
    (hnF : 2 * R + 5 * (L * cellSide L m₀ m₁ (k + 1)) < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hnF' : 2 * R + 5 * (L * cellSide L m₀ m₁ (k + 1)) < (N₁' * L ^ m₁) * L ^ (k + 1))
    {Y : Set (CTorus d L N₁ m₁ (k + 1))}
    (hYR : ∀ y ∈ Y, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) (y + tA))
    (s : CTorus d L N₁ m₁ (k + 1) × Fin N)
    (hs : Y ∈ polyDom (GA) (LocalCover.nbhdF m₀ s.1) m₀ k (LocalCover.fam m₀ s.1)) :
    (fun x => bm (x + tA) - tB) '' Y ∈ polyDom (GB) (LocalCover.nbhdF m₀ (bm (s.1 + tA) - tB))
        m₀ k (LocalCover.fam m₀ (bm (s.1 + tA) - tB)) := by
  have hX : ∀ x ∈ LocalCover.nbhd m₀ s.1, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) (x + tA) :=
    fun x hx => hYR x (nbhd_subset_of_mem_polyDom hN s.1 hs hx)
  exact (mem_polyDom_site_recentred_iff hGA hGB hN hN' tA tB htA htB hnF hnF' s.1 _
    (sub_add_cancel _ _) hX hYR).2 hs

theorem srcRec_back     {m₀ R : ℕ} (hGA : IsLevel (GA) (k + 1)) (hGB : IsLevel (GB) (k + 1))
    (hN : L ^ m₀ ∣ N₁) (hN' : L ^ m₀ ∣ N₁')
    (tA : CTorus d L N₁ m₁ (k + 1)) (tB : CTorus d L N₁' m₁ (k + 1))
    (htA : ∀ μ, L ^ ((k + 1) + m₀ + m₁) ∣ (tA μ).val)
    (htB : ∀ μ, L ^ ((k + 1) + m₀ + m₁) ∣ (tB μ).val)
    (hnF : 2 * R + 5 * (L * cellSide L m₀ m₁ (k + 1)) < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hnF' : 2 * R + 5 * (L * cellSide L m₀ m₁ (k + 1)) < (N₁' * L ^ m₁) * L ^ (k + 1))
    {Y : Set (CTorus d L N₁ m₁ (k + 1))}
    (hYR : ∀ y ∈ Y, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) (y + tA))
    (s' : CTorus d L N₁' m₁ (k + 1))
    (hs' : (fun x => bm (x + tA) - tB) '' Y ∈
        polyDom (GB) (LocalCover.nbhdF m₀ s') m₀ k (LocalCover.fam m₀ s')) :
    Y ∈ polyDom (GA) (LocalCover.nbhdF m₀ (bm' (s' + tB) - tA)) m₀ k
        (LocalCover.fam m₀ (bm' (s' + tB) - tA)) ∧
      bm (bm' (s' + tB) - tA + tA) - tB = s' := by
  have hc1 : 1 ≤ 5 * (L * cellSide L m₀ m₁ (k + 1)) :=
    Nat.succ_le_of_lt (Nat.mul_pos (by norm_num)
      (Nat.mul_pos (Nat.pos_of_ne_zero (NeZero.ne L)) (cellSide_pos m₀ m₁ (k + 1))))
  have hsB : 2 * R + 1 < (N₁' * L ^ m₁) * L ^ (k + 1) := by omega
  have hY'R : ∀ y' ∈ (fun x => bm (x + tA) - tB) '' Y,
      InBox d R ((N₁' * L ^ m₁) * L ^ (k + 1)) (y' + tB) := by
    rintro _ ⟨y, hy, rfl⟩
    rw [sub_add_cancel]
    exact inBox_boxMap hsB (hYR y hy)
  have hψφ := srcRec_inv hnF' tA tB hYR
  have hYY : (fun x' => bm' (x' + tB) - tA) '' ((fun x => bm (x + tA) - tB) '' Y) = Y := by
    rw [Set.image_image]
    conv_rhs => rw [← Set.image_id Y]
    exact Set.image_congr (fun y hy => hψφ y hy)
  have hX : ∀ x ∈ LocalCover.nbhd m₀ s', InBox d R ((N₁' * L ^ m₁) * L ^ (k + 1)) (x + tB) :=
    fun x hx => hY'R x (nbhd_subset_of_mem_polyDom hN' s' hs' hx)
  refine ⟨?_, ?_⟩
  · have h := (mem_polyDom_site_recentred_iff hGB hGA hN' hN tB tA htB htA hnF' hnF s'
      (bm' (s' + tB) - tA) (sub_add_cancel _ _) hX hY'R).2 hs'
    rwa [hYY] at h
  · obtain ⟨y, hy, he⟩ := mem_of_mem_polyDom_site hN' s' hs'
    have key : bm' (s' + tB) = y + tA := by
      rw [← he]
      show bm' (bm (y + tA) - tB + tB) = _
      rw [sub_add_cancel, boxMap_boxMap hsB (hYR y hy)]
    rw [key, sub_add_cancel]
    exact he

/-- **The sums over the source sites under the recentring map.**  For a set `Y` with `Y + tA` in the box
of radius `R` and summands `a`, `b` of the sites of the two tori with `b (φ x, i) = a (x, i)` whenever
`Y` is a domain of the expansion with the local cover of `x`, `φ x = bm (x + tA) - tB`, the sums over
the sites whose local cover has `φ '' Y` (resp. `Y`) as a domain agree. -/
theorem sourceSum_recentred     {m₀ R : ℕ} (hGA : IsLevel (GA) (k + 1)) (hGB : IsLevel (GB) (k + 1))
    (hN : L ^ m₀ ∣ N₁) (hN' : L ^ m₀ ∣ N₁')
    (tA : CTorus d L N₁ m₁ (k + 1)) (tB : CTorus d L N₁' m₁ (k + 1))
    (htA : ∀ μ, L ^ ((k + 1) + m₀ + m₁) ∣ (tA μ).val)
    (htB : ∀ μ, L ^ ((k + 1) + m₀ + m₁) ∣ (tB μ).val)
    (hnF : 2 * R + 5 * (L * cellSide L m₀ m₁ (k + 1)) < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hnF' : 2 * R + 5 * (L * cellSide L m₀ m₁ (k + 1)) < (N₁' * L ^ m₁) * L ^ (k + 1))
    {Y : Set (CTorus d L N₁ m₁ (k + 1))}
    (hYR : ∀ y ∈ Y, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) (y + tA))
    (a : CTorus d L N₁ m₁ (k + 1) × Fin N → ℂ)
    (b : CTorus d L N₁' m₁ (k + 1) × Fin N → ℂ)
    (hab : ∀ s : CTorus d L N₁ m₁ (k + 1) × Fin N,
      Y ∈ polyDom (GA) (LocalCover.nbhdF m₀ s.1) m₀ k (LocalCover.fam m₀ s.1) →
        b (bm (s.1 + tA) - tB, s.2) = a s) :
    (∑ s' : CTorus d L N₁' m₁ (k + 1) × Fin N,
      if (fun x => bm (x + tA) - tB) '' Y ∈
          polyDom (GB) (LocalCover.nbhdF m₀ s'.1) m₀ k (LocalCover.fam m₀ s'.1)
        then b s' else 0) =
    ∑ s : CTorus d L N₁ m₁ (k + 1) × Fin N,
      if Y ∈ polyDom (GA) (LocalCover.nbhdF m₀ s.1) m₀ k (LocalCover.fam m₀ s.1)
        then a s else 0 := by
  have hψφ := srcRec_inv hnF' tA tB hYR
  refine sum_ite_bij
    (fun s : CTorus d L N₁ m₁ (k + 1) × Fin N =>
      Y ∈ polyDom (GA) (LocalCover.nbhdF m₀ s.1) m₀ k (LocalCover.fam m₀ s.1))
    (fun s' : CTorus d L N₁' m₁ (k + 1) × Fin N =>
      (fun x => bm (x + tA) - tB) '' Y ∈
        polyDom (GB) (LocalCover.nbhdF m₀ s'.1) m₀ k (LocalCover.fam m₀ s'.1)) a b
    (fun s => (bm (s.1 + tA) - tB, s.2)) ?_ ?_ ?_
  · intro s hs
    exact ⟨srcRec_fwd hGA hGB hN hN' tA tB htA htB hnF hnF' hYR s hs, hab s hs⟩
  · intro s₁ s₂ h₁ h₂ h
    have e1 := hψφ _ (mem_of_mem_polyDom_site hN s₁.1 h₁)
    have e2 := hψφ _ (mem_of_mem_polyDom_site hN s₂.1 h₂)
    have e := congrArg (fun q => bm' (q.1 + tB) - tA) h
    exact Prod.ext (by rw [← e1, ← e2]; exact e) (by simpa using congrArg Prod.snd h)
  · intro s' hs'
    obtain ⟨h1, h2⟩ := srcRec_back hGA hGB hN hN' tA tB htA htB hnF hnF' hYR s'.1 hs'
    exact ⟨(bm' (s'.1 + tB) - tA, s'.2), h1, Prod.ext h2 rfl⟩

set_option hygiene false in
local notation "aK" => cellSide L m₀ m₁ (k + 1)
set_option hygiene false in
local notation "SA" => hatStepKG (d := d) (L := L) (N := N) (N₁ := N₁) hN2 k m₁ ϱ hk νS β p₁ δ
set_option hygiene false in
local notation "SB" => hatStepKG (d := d) (L := L) (N := N) (N₁ := N₁') hN2 k m₁ ϱ hk νS β p₁ δ
set_option hygiene false in
local notation "TA" => Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1)))
set_option hygiene false in
local notation "TB" => Torus d (N₁' * L ^ m₁ * L ^ (k + 1 - (k + 1)))

/-- **The activities of corresponding labels at nonzero source under the recentring map** (the
source part, `hAeqθ`): `labelActZero_recentred` and the source sums `sourceSum_recentred` of the
terms `dirTerm_siteEv_recentred`. -/
theorem labelActSource_recentred (hN2 : 2 ≤ N) (hk : 1 ≤ k) (νS β p₁ δ : ℝ)
    {c BG κ eps Kc Cx c₂ BG₂ δ₁ : ℝ}
    (hC : FlCore N (GA) (HA) 1 νS c BG κ eps Kc Cx c₂ BG₂ δ₁)
    (hC' : FlCore N (GB) (HB) 1 νS c BG κ eps Kc Cx c₂ BG₂ δ₁)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δc : ℝ}
    (hmar : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hαK : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    {m₀ R : ℕ} (hd : 0 < d) (hL : 2 ≤ L) (hm₀ : 1 ≤ m₀) (hm₁ : 1 ≤ m₁)
    (hN : L ^ m₀ ∣ N₁) (hN' : L ^ m₀ ∣ N₁')
    (z : Fin d → ℤ) (hz : ∀ μ, ((cellSide L m₀ m₁ (k + 1) : ℕ) : ℤ) ∣ z μ)
    (tA : CTorus d L N₁ m₁ (k + 1)) (tB : CTorus d L N₁' m₁ (k + 1))
    (htAz : tA = (fun μ => ((z μ : ℤ) : ZMod ((N₁ * L ^ m₁) * L ^ (k + 1)))))
    (htBz : tB = (fun μ => ((z μ : ℤ) : ZMod ((N₁' * L ^ m₁) * L ^ (k + 1)))))
    (hn20 : 20 * R + 20 < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hn20' : 20 * R + 20 < (N₁' * L ^ m₁) * L ^ (k + 1))
    (hnF : 2 * R + 5 * (L * aK) < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hnF' : 2 * R + 5 * (L * aK) < (N₁' * L ^ m₁) * L ^ (k + 1))
    (cc : ℂ) {cψ : ℝ} (hcψ : 0 ≤ cψ) (hρ : 2 * p₁ ≤ cψ)
    (hrad : markedRad d L N k 1 κ cψ cc < δ₁)
    {F₂ : TA → DecParams (GA) × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      ((GA).Ω 1 × Fin N → ℂ) × ((GA).Ω 1 → ℂ)}
    {F₂' : TB → DecParams (GB) × RawData d L (N₁' * L ^ m₁) (k + 1) N →
      ((GB).Ω 1 × Fin N → ℂ) × ((GB).Ω 1 → ℂ)}
    (hF₂ : ∀ (b : TA) (s : DecParams (GA)) (D : BgData (GA) N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC (GA) (bgC0 d L N) (c7 d L N BG κ) νS D → ∀ (φ : (GA).Ω 1 × Fin N → ℂ)
        (α : (GA).Ω 1 → ℂ), IsDecBg (GA) (compWeight L 1) νS (rho4 d L N BG κ) s D φ α →
        F₂ b (s, rawOf D) = (φ, α))
    (hF₂' : ∀ (b : TB) (s : DecParams (GB)) (D : BgData (GB) N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC (GB) (bgC0 d L N) (c7 d L N BG κ) νS D → ∀ (φ : (GB).Ω 1 × Fin N → ℂ)
        (α : (GB).Ω 1 → ℂ), IsDecBg (GB) (compWeight L 1) νS (rho4 d L N BG κ) s D φ α →
        F₂' b (s, rawOf D) = (φ, α))
    {Sol₂ : TA → Dec2.DecParams (coverOf (GA)) × Edat (HA) N →
      ((HA).Ω 1 × Fin N → ℂ) × ((HA).Ω 1 → ℂ)}
    {Sol₂' : TB → Dec2.DecParams (coverOf (GB)) × Edat (HB) N →
      ((HB).Ω 1 × Fin N → ℂ) × ((HB).Ω 1 → ℂ)}
    (hSol₂ : ∀ (b : TA) (p : Dec2.DecParams (coverOf (GA)) × Edat (HA) N),
      (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM (HA) N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2 →
        (Sol₂ b p).1 = dphi (HA) (Dec2.decG (coverOf (GA)) (HA) (compWeight L 1) νS p.1) p.2.2.1
          p.2.1 (pertSource (HA) (compWeight L 1) p.2.2.2.1 p.2.2.2.2) (Sol₂ b p).2 ∧
        Dec2.DecFixed (coverOf (GA)) (HA) (compWeight L 1) νS p.1 false p.2.2.1 p.2.1
          (pertSource (HA) (compWeight L 1) p.2.2.2.1 p.2.2.2.2) (Sol₂ b p).2 ∧
        Small (HA) (Sol₂ b p).2 (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
        Small (HA) (Sol₂ b p).2 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        SupBounds (HA) (Sol₂ b p).1 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        (∀ δα' : (HA).Ω 1 → ℂ, Small (HA) δα' (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf (GA)) (HA) (compWeight L 1) νS p.1 false p.2.2.1 p.2.1
            (pertSource (HA) (compWeight L 1) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol₂ b p).2))
    (hSol₂' : ∀ (b : TB) (p : Dec2.DecParams (coverOf (GB)) × Edat (HB) N),
      (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM (HB) N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2 →
        (Sol₂' b p).1 = dphi (HB) (Dec2.decG (coverOf (GB)) (HB) (compWeight L 1) νS p.1) p.2.2.1
          p.2.1 (pertSource (HB) (compWeight L 1) p.2.2.2.1 p.2.2.2.2) (Sol₂' b p).2 ∧
        Dec2.DecFixed (coverOf (GB)) (HB) (compWeight L 1) νS p.1 false p.2.2.1 p.2.1
          (pertSource (HB) (compWeight L 1) p.2.2.2.1 p.2.2.2.2) (Sol₂' b p).2 ∧
        Small (HB) (Sol₂' b p).2 (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
        Small (HB) (Sol₂' b p).2 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        SupBounds (HB) (Sol₂' b p).1 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        (∀ δα' : (HB).Ω 1 → ℂ, Small (HB) δα' (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf (GB)) (HB) (compWeight L 1) νS p.1 false p.2.2.1 p.2.1
            (pertSource (HB) (compWeight L 1) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol₂' b p).2))
    (hp : 0 < (SA).p₁) (hp' : 0 < (SB).p₁)
    {Lb Lb' : Type*} [Fintype Lb] [Fintype Lb']
    (Lab : CubeLabels (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) m₀ (k + 1)
      Set.univ Lb)
    (Lab' : CubeLabels (d := d) (L := L) (N₁ := N₁') (m₁ := m₁) (K := k + 1) m₀ (k + 1)
      Set.univ Lb')
    {εH κH κ0 Kco εH' κH' κ0' Kco' : ℝ}
    (A : physParam N (SA) → ℂ → LabelAct Lab ((SA).blockSplit m₀ hp).Ωb εH κH κ0 Kco)
    (A' : physParam N (SB) → ℂ → LabelAct Lab' ((SB).blockSplit m₀ hp').Ωb εH' κH' κ0' Kco')
    {V : Set (physParam N (SA))} {V' : Set (physParam N (SB))}
    (hAx : ∀ e ∈ V, ∀ σ : ℂ, ‖σ‖ < 2 → ∀ (l : Lb) (Φ : ∀ b, ((SA).blockSplit m₀ hp).Ωb b),
      (A ((e.1, 0) : physParam N (SA)) σ).H l Φ = -(β : ℂ) *
        ∑ z : TA, if Lab.ysite l ∈ polyDom (GA) (LocalCover.nbhdF m₀ (LocalCover.blockSite k z))
            m₀ k (LocalCover.fam m₀ (LocalCover.blockSite k z)) then
          rayTerm (dl3 (evDec (LocalCover.nbhdF m₀ (LocalCover.blockSite k z)) m₀ k
            (LocalCover.fam m₀ (LocalCover.blockSite k z)) 1 νS (SA).hG' cc (F₂ z) (Sol₂ z)
            (blockEnergyFun (GA) (HA) (compWeight L 1) νS k z) ∅ 1 0 (Lab.ysite l))
            ((SA).hatOf m₀ p₁ hp Φ)) taylorWeight ((SA).hatOf m₀ p₁ hp Φ) σ
            (e.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N)
        else 0)
    (hAx' : ∀ e ∈ V', ∀ σ : ℂ, ‖σ‖ < 2 → ∀ (l : Lb') (Φ : ∀ b, ((SB).blockSplit m₀ hp').Ωb b),
      (A' ((e.1, 0) : physParam N (SB)) σ).H l Φ = -(β : ℂ) *
        ∑ z : TB, if Lab'.ysite l ∈ polyDom (GB) (LocalCover.nbhdF m₀ (LocalCover.blockSite k z))
            m₀ k (LocalCover.fam m₀ (LocalCover.blockSite k z)) then
          rayTerm (dl3 (evDec (LocalCover.nbhdF m₀ (LocalCover.blockSite k z)) m₀ k
            (LocalCover.fam m₀ (LocalCover.blockSite k z)) 1 νS (SB).hG' cc (F₂' z) (Sol₂' z)
            (blockEnergyFun (GB) (HB) (compWeight L 1) νS k z) ∅ 1 0 (Lab'.ysite l))
            ((SB).hatOf m₀ p₁ hp' Φ)) taylorWeight ((SB).hatOf m₀ p₁ hp' Φ) σ
            (e.1 : RawData d L (N₁' * L ^ m₁) (k + 1) N)
        else 0)
    {F₃ : CTorus d L N₁ m₁ (k + 1) × Fin N →
      DecParams (GA) × RawData d L (N₁ * L ^ m₁) (k + 1) N →
        ((GA).Ω 1 × Fin N → ℂ) × ((GA).Ω 1 → ℂ)}
    {Sol₃ : CTorus d L N₁ m₁ (k + 1) × Fin N →
      Dec2.DecParams (coverOf (GA)) × Edat (HA) N → ((HA).Ω 1 × Fin N → ℂ) × ((HA).Ω 1 → ℂ)}
    {Ev₃ : CTorus d L N₁ m₁ (k + 1) × Fin N → Set (CTorus d L N₁ m₁ (k + 1)) →
      RawData d L (N₁ * L ^ m₁) (k + 1) N × (unitPts (GA) × Fin N → ℂ) → ℂ}
    (hF₃ : ∀ (a : CTorus d L N₁ m₁ (k + 1) × Fin N) (s : DecParams (GA)) (D : BgData (GA) N),
      (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC (GA) (bgC0 d L N) (c7 d L N BG κ) νS D → ∀ (φ : (GA).Ω 1 × Fin N → ℂ)
        (α : (GA).Ω 1 → ℂ), IsDecBg (GA) (compWeight L 1) νS (rho4 d L N BG κ) s D φ α →
        F₃ a (s, rawOf D) = (φ, α))
    (hSol₃ : ∀ (a : CTorus d L N₁ m₁ (k + 1) × Fin N)
      (p : Dec2.DecParams (coverOf (GA)) × Edat (HA) N), (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM (HA) N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2 →
        (Sol₃ a p).1 = dphi (HA) (Dec2.decG (coverOf (GA)) (HA) (compWeight L 1) νS p.1) p.2.2.1
          p.2.1 (pertSource (HA) (compWeight L 1) p.2.2.2.1 p.2.2.2.2) (Sol₃ a p).2 ∧
        Dec2.DecFixed (coverOf (GA)) (HA) (compWeight L 1) νS p.1 false p.2.2.1 p.2.1
          (pertSource (HA) (compWeight L 1) p.2.2.2.1 p.2.2.2.2) (Sol₃ a p).2 ∧
        Small (HA) (Sol₃ a p).2 (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
        Small (HA) (Sol₃ a p).2 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        SupBounds (HA) (Sol₃ a p).1 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        (∀ δα' : (HA).Ω 1 → ℂ, Small (HA) δα' (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf (GA)) (HA) (compWeight L 1) νS p.1 false p.2.2.1 p.2.1
            (pertSource (HA) (compWeight L 1) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol₃ a p).2))
    (hEv₃ : ∀ a : CTorus d L N₁ m₁ (k + 1) × Fin N, Ev₃ a =
      evTerm (fun i : ParIdx (GA) (↑(LocalCover.nbhdF m₀ a.1) : Set (CTorus d L N₁ m₁ (k + 1))) =>
        i.1.1) (GA) m₀ (X1 (GA) m₀ k (LocalCover.fam m₀ a.1))
        (fun u t => siteFun (GA) (HA) a.1 a.2
          (F₃ a (extParams (GA) (↑(LocalCover.nbhdF m₀ a.1) : Set (CTorus d L N₁ m₁ (k + 1))) t,
            u.1))
          (Sol₃ a (extParams (GA) (↑(LocalCover.nbhdF m₀ a.1) : Set (CTorus d L N₁ m₁ (k + 1))) t,
            flEdat (GA) (HA)
              (F₃ a (extParams (GA) (↑(LocalCover.nbhdF m₀ a.1) : Set (CTorus d L N₁ m₁ (k + 1))) t,
                u.1))
              u.1.1 (hatPsiF (GA) 1 νS (SA).hG' cc (F₃ a)
                (extParams (GA) (↑(LocalCover.nbhdF m₀ a.1) : Set (CTorus d L N₁ m₁ (k + 1))) t)
                u.1 u.2))).1
          (u.1, hatPsiF (GA) 1 νS (SA).hG' cc (F₃ a)
            (extParams (GA) (↑(LocalCover.nbhdF m₀ a.1) : Set (CTorus d L N₁ m₁ (k + 1))) t)
            u.1 u.2)))
    (hanEv₃ : ∀ (a : CTorus d L N₁ m₁ (k + 1) × Fin N) (Y : Set (CTorus d L N₁ m₁ (k + 1))),
      AnalyticOnNhd ℂ (Ev₃ a Y) (XiCRaw (GA) (compWeight L 1) νS (k + 1) 1 eps ×ˢ
        {ψh : unitPts (GA) × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ}))
    {F₃' : CTorus d L N₁' m₁ (k + 1) × Fin N →
      DecParams (GB) × RawData d L (N₁' * L ^ m₁) (k + 1) N →
        ((GB).Ω 1 × Fin N → ℂ) × ((GB).Ω 1 → ℂ)}
    {Sol₃' : CTorus d L N₁' m₁ (k + 1) × Fin N →
      Dec2.DecParams (coverOf (GB)) × Edat (HB) N → ((HB).Ω 1 × Fin N → ℂ) × ((HB).Ω 1 → ℂ)}
    {Ev₃' : CTorus d L N₁' m₁ (k + 1) × Fin N → Set (CTorus d L N₁' m₁ (k + 1)) →
      RawData d L (N₁' * L ^ m₁) (k + 1) N × (unitPts (GB) × Fin N → ℂ) → ℂ}
    (hF₃' : ∀ (a : CTorus d L N₁' m₁ (k + 1) × Fin N) (s : DecParams (GB)) (D : BgData (GB) N),
      (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC (GB) (bgC0 d L N) (c7 d L N BG κ) νS D → ∀ (φ : (GB).Ω 1 × Fin N → ℂ)
        (α : (GB).Ω 1 → ℂ), IsDecBg (GB) (compWeight L 1) νS (rho4 d L N BG κ) s D φ α →
        F₃' a (s, rawOf D) = (φ, α))
    (hSol₃' : ∀ (a : CTorus d L N₁' m₁ (k + 1) × Fin N)
      (p : Dec2.DecParams (coverOf (GB)) × Edat (HB) N), (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM (HB) N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2 →
        (Sol₃' a p).1 = dphi (HB) (Dec2.decG (coverOf (GB)) (HB) (compWeight L 1) νS p.1) p.2.2.1
          p.2.1 (pertSource (HB) (compWeight L 1) p.2.2.2.1 p.2.2.2.2) (Sol₃' a p).2 ∧
        Dec2.DecFixed (coverOf (GB)) (HB) (compWeight L 1) νS p.1 false p.2.2.1 p.2.1
          (pertSource (HB) (compWeight L 1) p.2.2.2.1 p.2.2.2.2) (Sol₃' a p).2 ∧
        Small (HB) (Sol₃' a p).2 (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
        Small (HB) (Sol₃' a p).2 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        SupBounds (HB) (Sol₃' a p).1 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        (∀ δα' : (HB).Ω 1 → ℂ, Small (HB) δα' (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf (GB)) (HB) (compWeight L 1) νS p.1 false p.2.2.1 p.2.1
            (pertSource (HB) (compWeight L 1) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol₃' a p).2))
    (hEv₃' : ∀ a : CTorus d L N₁' m₁ (k + 1) × Fin N, Ev₃' a =
      evTerm (fun i : ParIdx (GB) (↑(LocalCover.nbhdF m₀ a.1) : Set (CTorus d L N₁' m₁ (k + 1))) =>
        i.1.1) (GB) m₀ (X1 (GB) m₀ k (LocalCover.fam m₀ a.1))
        (fun u t => siteFun (GB) (HB) a.1 a.2
          (F₃' a (extParams (GB) (↑(LocalCover.nbhdF m₀ a.1) : Set (CTorus d L N₁' m₁ (k + 1))) t,
            u.1))
          (Sol₃' a (extParams (GB) (↑(LocalCover.nbhdF m₀ a.1) : Set (CTorus d L N₁' m₁ (k + 1))) t,
            flEdat (GB) (HB)
              (F₃' a (extParams (GB) (↑(LocalCover.nbhdF m₀ a.1) : Set (CTorus d L N₁' m₁ (k + 1))) t,
                u.1))
              u.1.1 (hatPsiF (GB) 1 νS (SB).hG' cc (F₃' a)
                (extParams (GB) (↑(LocalCover.nbhdF m₀ a.1) : Set (CTorus d L N₁' m₁ (k + 1))) t)
                u.1 u.2))).1
          (u.1, hatPsiF (GB) 1 νS (SB).hG' cc (F₃' a)
            (extParams (GB) (↑(LocalCover.nbhdF m₀ a.1) : Set (CTorus d L N₁' m₁ (k + 1))) t)
            u.1 u.2)))
    (hanEv₃' : ∀ (a : CTorus d L N₁' m₁ (k + 1) × Fin N) (Y : Set (CTorus d L N₁' m₁ (k + 1))),
      AnalyticOnNhd ℂ (Ev₃' a Y) (XiCRaw (GB) (compWeight L 1) νS (k + 1) 1 eps ×ˢ
        {ψh : unitPts (GB) × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ}))
    (hAs : ∀ e ∈ V, ∀ σ : ℂ, ‖σ‖ < 2 → ∀ (l : Lb)
      (Φ : ∀ b, ((SA).blockSplit m₀ hp).Ωb b),
      (A e σ).H l Φ = (A ((e.1, 0) : physParam N (SA)) σ).H l Φ +
        ∑ s : CTorus d L N₁ m₁ (k + 1) × Fin N,
          if Lab.ysite l ∈ polyDom (GA) (LocalCover.nbhdF m₀ s.1) m₀ k (LocalCover.fam m₀ s.1) then
            e.2 s.1 s.2 * dirTerm (Ev₃ s (Lab.ysite l)) (fun _ => (1 : ℂ))
              ((SA).hatOf m₀ p₁ hp Φ) ((SA).hatOf m₀ p₁ hp Φ) σ
              (e.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N)
          else 0)
    (hAs' : ∀ e ∈ V', ∀ σ : ℂ, ‖σ‖ < 2 → ∀ (l : Lb')
      (Φ : ∀ b, ((SB).blockSplit m₀ hp').Ωb b),
      (A' e σ).H l Φ = (A' ((e.1, 0) : physParam N (SB)) σ).H l Φ +
        ∑ s : CTorus d L N₁' m₁ (k + 1) × Fin N,
          if Lab'.ysite l ∈ polyDom (GB) (LocalCover.nbhdF m₀ s.1) m₀ k (LocalCover.fam m₀ s.1) then
            e.2 s.1 s.2 * dirTerm (Ev₃' s (Lab'.ysite l)) (fun _ => (1 : ℂ))
              ((SB).hatOf m₀ p₁ hp' Φ) ((SB).hatOf m₀ p₁ hp' Φ) σ
              (e.1 : RawData d L (N₁' * L ^ m₁) (k + 1) N)
          else 0)
    (θ : physParam N (SA)) (θ' : physParam N (SB)) (hθV : θ ∈ V) (hθV' : θ' ∈ V')
    (hθ : (θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) ∈
      XiCRaw (GA) (compWeight L 1) νS (k + 1) 1 eps)
    (hθ' : (θ'.1 : RawData d L (N₁' * L ^ m₁) (k + 1) N) ∈
      XiCRaw (GB) (compWeight L 1) νS (k + 1) 1 eps)
    (hraw : RawBoxAgree {w | InBox d (R + 3 * L ^ (k + 1)) ((N₁ * L ^ m₁) * L ^ (k + 1)) w}
      (symRaw (Equiv.addRight tA) (θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N))
      (symRaw (Equiv.addRight tB) (θ'.1 : RawData d L (N₁' * L ^ m₁) (k + 1) N)))
    (hsrc : ∀ x, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) (x + tA) → ∀ i, θ'.2 (bm (x + tA) - tB) i = θ.2 x i)
    {σ : ℂ} (hσ : ‖σ‖ ≤ 1) (l : Lb) (l' : Lb')
    (hlR : ∀ x ∈ Lab.ysite l, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) (x + tA))
    (hl' : Lab'.ysite l' = (fun x => bm (x + tA) - tB) '' Lab.ysite l)
    (Φ : ∀ b, ((SA).blockSplit m₀ hp).Ωb b) (Φ' : ∀ b, ((SB).blockSplit m₀ hp').Ωb b)
    (hΦ : ∀ x, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) (x + tA) →
      Φ' ((SB).cellOf m₀ (unitPt (SB).hG' (bm (x + tA) - tB))) ⟨unitPt (SB).hG' (bm (x + tA) - tB), rfl⟩ =
        Φ ((SA).cellOf m₀ (unitPt (SA).hG' x)) ⟨unitPt (SA).hG' x, rfl⟩) :
    (A' θ' σ).H l' Φ' = (A θ σ).H l Φ := by
  classical
  have hσ2 : ‖σ‖ < 2 := by linarith
  have hp1 : (0 : ℝ) < p₁ := hp
  have htA : ∀ μ, L ^ ((k + 1) + m₀ + m₁) ∣ (tA μ).val := fun μ => by
    rw [htAz]; exact dvd_val_intCast (cellSide_dvd hN le_rfl) (hz μ)
  have htB : ∀ μ, L ^ ((k + 1) + m₀ + m₁) ∣ (tB μ).val := fun μ => by
    rw [htBz]; exact dvd_val_intCast (cellSide_dvd hN' le_rfl) (hz μ)
  have h0 := labelActZero_recentred hN2 hk νS β p₁ δ hC hC' hMX hmar hαK hsm hd hL hm₀ hm₁ hN hN' z hz
    tA tB htAz htBz hn20 hn20' hnF hnF' cc hcψ hρ hrad hF₂ hF₂' hSol₂ hSol₂' hp hp' Lab Lab' A A'
    hAx hAx' θ θ' hθV hθV' hθ hθ' hraw hσ l l' hlR hl' Φ Φ' hΦ
  rw [hAs' θ' hθV' σ hσ2 l' Φ', hAs θ hθV σ hσ2 l Φ, h0]
  congr 1
  obtain ⟨D, hD, hDe⟩ := hθ
  obtain ⟨D', hD', hDe'⟩ := hθ'
  have hhat := hatOf_rec (hN2 := hN2) (hk := hk) (νS := νS) (β := β) (p₁ := p₁) (δ := δ) m₀ p₁ hp hp'
    (R := R) (tA := tA) (tB := tB) hΦ
  rw [hl', hDe, hDe']
  rw [hDe, hDe'] at hraw
  refine sourceSum_recentred (SA).hG' (SB).hG' hN hN' tA tB htA htB hnF hnF' hlR _ _ (fun s hs => ?_)
  have hxR := hlR _ (mem_of_mem_polyDom_site hN s.1 hs)
  have hX₁R : ∀ x ∈ LocalCover.nbhd m₀ s.1, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) (x + tA) :=
    fun x hx => hlR x (nbhd_subset_of_mem_polyDom hN s.1 hs hx)
  simp only
  rw [hsrc s.1 hxR s.2]
  congr 1
  exact dirTerm_siteEv_recentred hC hC' hk (SA).hG' (SB).hG' cc hcψ hMX hmar hαK hsm
    (hF₃ s) (hF₃' (bm (s.1 + tA) - tB, s.2)) (hSol₃ s) (hSol₃' (bm (s.1 + tA) - tB, s.2)) hd hL hm₀ hm₁
    hN hN' z hz tA tB htAz htBz s.1 (bm (s.1 + tA) - tB)
    (sub_add_cancel _ _) s.2
    hX₁R hlR hn20 hn20' hD hD' hraw
    (fun p => (SA).hatOf_mem m₀ hp1 hp Φ p) (fun p => (SA).hatOf_mem m₀ hp1 hp Φ p)
    (fun p => (SB).hatOf_mem m₀ hp1 hp' Φ' p) (fun p => (SB).hatOf_mem m₀ hp1 hp' Φ' p) hρ hhat hhat
    hrad (hEv₃ s) (hEv₃' (bm (s.1 + tA) - tB, s.2)) (hanEv₃ s _)
    (hanEv₃' (bm (s.1 + tA) - tB, s.2) _) hσ

end SrcRec

end Balaban.Polymer.TwoTorusStep
