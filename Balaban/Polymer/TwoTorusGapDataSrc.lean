/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Polymer.TwoTorusObsSourceSite
public import Balaban.Polymer.TwoTorusGapStepObsEv
public import Balaban.Polymer.TwoTorusGapStepObsAct

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
    (xs : CTorus d L N₁ m₁ (k + 1)) (xs' : CTorus d L N₁' m₁ (k + 1))
    (hxs : xs' + (fun μ => ((z μ : ℤ) : ZMod ((N₁' * L ^ m₁) * L ^ (k + 1)))) = bm (xs + (fun μ => ((z μ : ℤ) : ZMod ((N₁ * L ^ m₁) * L ^ (k + 1)))))) (iy : Fin N) {R : ℕ}
    (hX₁R : ∀ x ∈ LocalCover.nbhd m₀ xs, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) (x + (fun μ => ((z μ : ℤ) : ZMod ((N₁ * L ^ m₁) * L ^ (k + 1))))))
    {Y : Set (CTorus d L N₁ m₁ (k + 1))}
    (hYR : ∀ y ∈ Y, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) (y + (fun μ => ((z μ : ℤ) : ZMod ((N₁ * L ^ m₁) * L ^ (k + 1))))))
    (hn20 : 20 * R + 20 < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hn20' : 20 * R + 20 < (N₁' * L ^ m₁) * L ^ (k + 1))
    {D : BgData (GA) N} {D' : BgData (GB) N}
    (hD : XiCData (GA) (compWeight L a₁) ν (k + 1) 1 eps D)
    (hD' : XiCData (GB) (compWeight L a₁) ν (k + 1) 1 eps D')
    (hraw : RawBoxAgree {w | InBox d (R + 3 * L ^ (k + 1)) ((N₁ * L ^ m₁) * L ^ (k + 1)) w}
      (symRaw (Equiv.addRight (fun μ => ((z μ : ℤ) : ZMod ((N₁ * L ^ m₁) * L ^ (k + 1))))) (rawOf D))
      (symRaw (Equiv.addRight (fun μ => ((z μ : ℤ) : ZMod ((N₁' * L ^ m₁) * L ^ (k + 1))))) (rawOf D')))
    {x₀ w : unitPts (GA) × Fin N → ℂ} {x₀' w' : unitPts (GB) × Fin N → ℂ} {ρ₀ : ℝ}
    (hx₀ : ∀ p, ‖x₀ p‖ ≤ ρ₀) (hw : ∀ p, ‖w p‖ ≤ ρ₀) (hx₀' : ∀ p, ‖x₀' p‖ ≤ ρ₀)
    (hw' : ∀ p, ‖w' p‖ ≤ ρ₀) (hρ₀ : 2 * ρ₀ ≤ cψ)
    (hhx : ∀ x, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) (x + (fun μ => ((z μ : ℤ) : ZMod ((N₁ * L ^ m₁) * L ^ (k + 1))))) →
      ∀ i, x₀' (unitPt hGB (bm (x + (fun μ => ((z μ : ℤ) : ZMod ((N₁ * L ^ m₁) * L ^ (k + 1))))) - (fun μ => ((z μ : ℤ) : ZMod ((N₁' * L ^ m₁) * L ^ (k + 1))))), i) = x₀ (unitPt hGA x, i))
    (hhw : ∀ x, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) (x + (fun μ => ((z μ : ℤ) : ZMod ((N₁ * L ^ m₁) * L ^ (k + 1))))) →
      ∀ i, w' (unitPt hGB (bm (x + (fun μ => ((z μ : ℤ) : ZMod ((N₁ * L ^ m₁) * L ^ (k + 1))))) - (fun μ => ((z μ : ℤ) : ZMod ((N₁' * L ^ m₁) * L ^ (k + 1))))), i) = w (unitPt hGA x, i))
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
    (hanEv' : AnalyticOnNhd ℂ (Ev' ((fun x => bm (x + (fun μ => ((z μ : ℤ) : ZMod ((N₁ * L ^ m₁) * L ^ (k + 1))))) - (fun μ => ((z μ : ℤ) : ZMod ((N₁' * L ^ m₁) * L ^ (k + 1))))) '' Y)) (XiCRaw (GB) (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
      {ψh : unitPts (GB) × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ}))
    {σ : ℂ} (hσ : ‖σ‖ ≤ 1) :
    dirTerm (Ev' ((fun x => bm (x + (fun μ => ((z μ : ℤ) : ZMod ((N₁ * L ^ m₁) * L ^ (k + 1))))) - (fun μ => ((z μ : ℤ) : ZMod ((N₁' * L ^ m₁) * L ^ (k + 1))))) '' Y)) (fun _ => (1 : ℂ)) x₀' w' σ (rawOf D') =
      dirTerm (Ev Y) (fun _ => (1 : ℂ)) x₀ w σ (rawOf D) := by
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

end SrcRec

end Balaban.Polymer.TwoTorusStep
