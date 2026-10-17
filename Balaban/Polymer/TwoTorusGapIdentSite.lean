/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Polymer.TwoTorusGapIdentBlock

/-!
# The site terms of the observable under the recentring map (item 24, blocker 7)

The terms `Ev` of the observable kernel are `evDec` (at the marks `(1, 0)`, `FFmarked_one_zero`)
of the site functional `siteFun Gp Hm y i = δφ(y, i)`.  `hfamΦ_siteFun` gives its translated
functionals for `hfamΦ` of `evDec_boxMap_of_diameter`: the site functional at the translated site
(`LatSymm.svec_sym`), whose read is the fluctuation field at that site; `evDec_boxMap_siteFun` is the
resulting torus independence of `evDec` for the site functional at a compact support anywhere on the
torus.
-/

@[expose] public section

noncomputable section

open scoped Classical

namespace Balaban.Polymer.TwoTorusStep

open Balaban Balaban.Localization Balaban.Analysis Balaban.Fluctuation Balaban.SmallField
  Balaban.SmallField.Def6 Balaban.Polymer Balaban.Multiscale Balaban.Background

section Fam

open Balaban.Localization.DetUnitIncidence Balaban.Localization.DecEquiv

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

/-- **The translated site functionals** (`hfamΦ` of `evDec_boxMap_of_diameter` for `Φ = siteFun` at
`x₀` and `Φ' = siteFun` at `bm x₀`): the site functional at the translated site, whose read is the
fluctuation field at that site. -/
theorem hfamΦ_siteFun {Ds : ℕ} (hk : 1 ≤ k) (i : Fin N) {X₁f : Finset (CTorus d L N₁ m₁ (k + 1))}
    {Y : Set (CTorus d L N₁ m₁ (k + 1))} {x₀ : CTorus d L N₁ m₁ (k + 1)}
    (hx₀ : x₀ ∈ X₁f)
    (hnR : 2 * (Ds + (Ds + 1) / 4) + 1 < (N₁ * L ^ m₁) * L ^ (k + 1))
    (z : Fin d → ℤ)
    (hint : ∀ x ∈ (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) ∪ Y, ∀ μ,
      |(x μ).valMinAbs + z μ| ≤ ((Ds + (Ds + 1) / 4 : ℕ) : ℤ))
    (SA : LatSymm (GA) (GA)
      (Equiv.addRight (fun μ => ((z μ : ℤ) : ZMod ((N₁ * L ^ m₁) * L ^ (k + 1))))))
    (SmA : LatSymm (HA) (HA)
      (Equiv.addRight (fun μ => ((z μ : ℤ) : ZMod ((N₁ * L ^ m₁) * L ^ (k + 1))))))
    (SB : LatSymm (GB) (GB)
      (Equiv.addRight (fun μ => ((z μ : ℤ) : ZMod ((N₁' * L ^ m₁) * L ^ (k + 1))))))
    (SmB : LatSymm (HB) (HB)
      (Equiv.addRight (fun μ => ((z μ : ℤ) : ZMod ((N₁' * L ^ m₁) * L ^ (k + 1)))))) :
    ∃ (ΦT : ((GA).Ω 1 × Fin N → ℂ) × ((GA).Ω 1 → ℂ) → ((HA).Ω 1 × Fin N → ℂ) →
        RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) → ℂ)
      (ΦT' : ((GB).Ω 1 × Fin N → ℂ) × ((GB).Ω 1 → ℂ) → ((HB).Ω 1 × Fin N → ℂ) →
        RawData d L (N₁' * L ^ m₁) (k + 1) N × (CTorus d L N₁' m₁ (k + 1) → Fin N → ℂ) → ℂ)
      (Rα Rδ Rψ : Set (CTorus d L N₁ m₁ (k + 1))),
      BlockMargin (GA) (X₁f.image (Equiv.addRight
        (fun μ => ((z μ : ℤ) : ZMod ((N₁ * L ^ m₁) * L ^ (k + 1)))))) Rα ∧
      Rδ ⊆ ↑(X₁f.image (Equiv.addRight
        (fun μ => ((z μ : ℤ) : ZMod ((N₁ * L ^ m₁) * L ^ (k + 1)))))) ∧
      Rψ ⊆ ↑(X₁f.image (Equiv.addRight
        (fun μ => ((z μ : ℤ) : ZMod ((N₁ * L ^ m₁) * L ^ (k + 1)))))) ∧
      (∀ (bg : ((GA).Ω 1 × Fin N → ℂ) × ((GA).Ω 1 → ℂ)) δφ u,
        ΦT (SA.fld bg.1, SA.mul bg.2) (SmA.fld δφ) (symU (Equiv.addRight
          (fun μ => ((z μ : ℤ) : ZMod ((N₁ * L ^ m₁) * L ^ (k + 1))))) u) =
        siteFun (GA) (HA) x₀ i bg δφ u) ∧
      (∀ (bg : ((GB).Ω 1 × Fin N → ℂ) × ((GB).Ω 1 → ℂ)) δφ u,
        ΦT' (SB.fld bg.1, SB.mul bg.2) (SmB.fld δφ) (symU (Equiv.addRight
          (fun μ => ((z μ : ℤ) : ZMod ((N₁' * L ^ m₁) * L ^ (k + 1))))) u) =
        siteFun (GB) (HB) (bm x₀) i bg δφ u) ∧
      (∀ (t : (((GA).Ω 1 × Fin N → ℂ) × ((GA).Ω 1 → ℂ)) × ((HA).Ω 1 × Fin N → ℂ) ×
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
        ΦT' t'.1 t'.2.1 t'.2.2 = ΦT t.1 t.2.1 t.2.2) := by
  classical
  set tA : CTorus d L N₁ m₁ (k + 1) :=
    fun μ => ((z μ : ℤ) : ZMod ((N₁ * L ^ m₁) * L ^ (k + 1))) with htAdef
  set tB : CTorus d L N₁' m₁ (k + 1) :=
    fun μ => ((z μ : ℤ) : ZMod ((N₁' * L ^ m₁) * L ^ (k + 1))) with htBdef
  have hφ : bm (x₀ + tA) - tB = bm x₀ := by
    have := boxMap_add_intCast (m' := (N₁' * L ^ m₁) * L ^ (k + 1)) hnR x₀ z
      (hint x₀ (Or.inl (Finset.mem_coe.2 hx₀)))
    rw [this]; exact add_sub_cancel_right _ _
  have hφ' : bm x₀ + tB = bm (x₀ + tA) := by rw [← hφ]; abel
  refine ⟨siteFun (GA) (HA) (x₀ + tA) i, siteFun (GB) (HB) (bm x₀ + tB) i, ∅,
    {x₀ + tA}, ∅, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx; exact absurd hx (Set.notMem_empty x)
  · intro w hw
    rw [Set.mem_singleton_iff] at hw
    rw [hw]
    exact Finset.mem_coe.2 (Finset.mem_image.2 ⟨x₀, hx₀, rfl⟩)
  · intro w hw; exact absurd hw (Set.notMem_empty w)
  · intro bg δφ u
    exact SmA.svec_sym δφ x₀ i
  · intro bg δφ u
    exact SmB.svec_sym δφ (bm x₀) i
  · intro t t' hα hδ hψ
    show svec (HB) t'.2.1 (bm x₀ + tB) i = svec (HA) t.2.1 (x₀ + tA) i
    rw [hφ']
    exact svec_levelGS_boxMap hk (fun w w' hw hw' i => hδ w w' (by rw [Set.mem_singleton_iff]; exact hw)
      (by rw [hw]; exact hw') i) i

end Fam



section RecentredSite

open Balaban.Localization.DetUnitIncidence Balaban.Localization.DecEquiv
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
local notation "ρ₁" => R + (3 * L ^ (k + 1 + m₁) + 3 * L ^ (k + 1 + 2)) + L ^ (k + 1 + m₁)

variable
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

variable {m₀ j : ℕ} (hd : 0 < d) (hL : 2 ≤ L) (hm₀ : 1 ≤ m₀) (hm₁ : 1 ≤ m₁)
    (hN : L ^ m₀ ∣ N₁) (hN' : L ^ m₀ ∣ N₁')
    {X 𝒦X : Set (CTorus d L N₁ m₁ (k + 1))} {X' 𝒦X' : Set (CTorus d L N₁' m₁ (k + 1))}
    {X₁f : Finset (CTorus d L N₁ m₁ (k + 1))} {X₁f' : Finset (CTorus d L N₁' m₁ (k + 1))}
    (hX' : X₁f' = X₁f.image bm)
    (hcov : CovSetup (GA) m₀ j X 𝒦X)
    (hX₁ : (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) = X1 (GA) m₀ j 𝒦X)
    (hcov' : CovSetup (GB) m₀ j X' 𝒦X')
    (hX₁' : (↑X₁f' : Set (CTorus d L N₁' m₁ (k + 1))) = X1 (GB) m₀ j 𝒦X')
    (h𝒦 : 𝒦X.Nonempty)

variable {Ds q : ℕ} {Y : Set (CTorus d L N₁ m₁ (k + 1))}
    (hDs : ∀ x ∈ (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))), ∀ y ∈ (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) ∪ Y,
      ∀ μ, |(x μ - y μ).valMinAbs| ≤ Ds)
    (hn25 : 25 * Ds + 25 < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hn25' : 25 * Ds + 25 < (N₁' * L ^ m₁) * L ^ (k + 1))
    (hq : ∀ x ∈ (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) ∪ Y, ∀ μ, |(x μ).valMinAbs| ≤ q)
    (hqn : 2 * q + 2 * (Ds + (Ds + 1) / 4) < (N₁ * L ^ m₁) * L ^ (k + 1))


    {D : BgData (GA) N} {D' : BgData (GB) N}
    (hD : XiCData (GA) (compWeight L a₁) ν (k + 1) 1 eps D)
    (hD' : XiCData (GB) (compWeight L a₁) ν (k + 1) 1 eps D')
    {ψh : unitPts (GA) × Fin N → ℂ} {ψh' : unitPts (GB) × Fin N → ℂ}
    (hψh : ∀ p, ‖ψh p‖ ≤ cψ) (hψh' : ∀ p, ‖ψh' p‖ ≤ cψ)
    {Zm : Finset (unitPts (GA))} {Zm' : Finset (unitPts (GB))}
    {um tm : ℂ} (hum : (‖um‖ + ‖tm‖) * markedRad d L N k a₁ κ cψ cc < δ₁)

variable
    (hfamD : ∀ z : Fin d → ℤ, (∀ μ, ((cellSide L m₀ m₁ (k + 1) : ℕ) : ℤ) ∣ z μ) →
      (∀ x ∈ (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) ∪ Y, ∀ μ,
        |(x μ).valMinAbs + z μ| ≤ ((Ds + (Ds + 1) / 4 : ℕ) : ℤ)) →
      RawBoxAgree {w | InBox d (Ds + (Ds + 1) / 4 + 3 * L ^ (k + 1)) ((N₁ * L ^ m₁) * L ^ (k + 1)) w}
        (symRaw (Equiv.addRight (fun μ => ((z μ : ℤ) : ZMod ((N₁ * L ^ m₁) * L ^ (k + 1)))))
          (rawOf D))
        (symRaw (Equiv.addRight (fun μ => ((z μ : ℤ) : ZMod ((N₁' * L ^ m₁) * L ^ (k + 1)))))
          (rawOf D')) ∧
      (∀ y, InBox d (Ds + (Ds + 1) / 4) ((N₁ * L ^ m₁) * L ^ (k + 1))
          (y + fun μ => ((z μ : ℤ) : ZMod ((N₁ * L ^ m₁) * L ^ (k + 1)))) →
        ∀ i, ψh' (unitPt hGB (bm (y + fun μ => ((z μ : ℤ) : ZMod ((N₁ * L ^ m₁) * L ^ (k + 1)))) -
          fun μ => ((z μ : ℤ) : ZMod ((N₁' * L ^ m₁) * L ^ (k + 1)))), i) = ψh (unitPt hGA y, i)) ∧
      (∀ y, InBox d (Ds + (Ds + 1) / 4) ((N₁ * L ^ m₁) * L ^ (k + 1))
          (y + fun μ => ((z μ : ℤ) : ZMod ((N₁ * L ^ m₁) * L ^ (k + 1)))) →
        (unitPt hGB (bm (y + fun μ => ((z μ : ℤ) : ZMod ((N₁ * L ^ m₁) * L ^ (k + 1)))) -
          fun μ => ((z μ : ℤ) : ZMod ((N₁' * L ^ m₁) * L ^ (k + 1)))) ∈ Zm' ↔
          unitPt hGA y ∈ Zm)))

variable {x₀ : CTorus d L N₁ m₁ (k + 1)} (hx₀ : x₀ ∈ X₁f) (i : Fin N)

include hC hC' hk hGA hGB hcψ hMX hmar hαK hsm hF₁ hF₁' hSol hSol' hd hL hm₀ hm₁ hN hN' hX'
  hcov hX₁ hcov' hX₁' h𝒦 hDs hn25 hn25' hq hqn hD hD' hψh hψh' hum hfamD hx₀

/-- **The torus clause for the site term of the observable at a compact support** (item 24,
part 2): `evDec_boxMap_of_diameter` for the site functional `δφ(x₀, i)` of the first torus and
`δφ(bm x₀, i)` of the second (`hfamΦ_siteFun`). -/
theorem evDec_boxMap_siteFun :
    evDec X₁f' m₀ j 𝒦X' a₁ ν hGB cc F₁' Sol' (siteFun (GB) (HB) (bm x₀) i) Zm' um tm (bm '' Y)
        (rawOf D', ψh') =
      evDec X₁f m₀ j 𝒦X a₁ ν hGA cc F₁ Sol (siteFun (GA) (HA) x₀ i) Zm um tm Y (rawOf D, ψh) :=
  evDec_boxMap_of_diameter hC hC' hk hGA hGB cc hcψ hMX hmar hαK hsm hF₁ hF₁' hSol hSol' hd hL hm₀
    hm₁ hN hN' hX' hcov hX₁ hcov' hX₁' h𝒦 hDs hn25 hn25' hq hqn
    ((siteFun_analytic _ _).mono (Set.subset_univ _))
    ((siteFun_analytic _ _).mono (Set.subset_univ _)) hD hD' hψh hψh' hum hfamD
    (fun z _ hint SA SmA SB SmB =>
      hfamΦ_siteFun hk i hx₀ (by omega) z hint SA SmA SB SmB)

end RecentredSite

end Balaban.Polymer.TwoTorusStep
