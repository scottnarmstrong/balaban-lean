/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Polymer.TwoTorusObsExplicit

/-!
# The coefficient of the observable on two tori: the terms of the site functional and the kernel

The terms `Ev Y` of the expansion of the site functional `δφ(y, i)` over the domains of the local
cover of the site `y` are explicit: `Ev = evTerm … (siteFun …)` for a decoupled pair `(F₁, Sol)`
(the appended conjunct of `obsEv_fromTower_rawYG`).  For the local covers of `y` and of `bm y`, the
terms of corresponding domains of the box agree on corresponding data (`Ev_localCover_twoTorus` for
the site functional, which reads `δφ` at `y` only).  Consequently the coefficients
`a_Y(m) = d/dζ|₀ Ev Y (Θ, ζ e_m)` of corresponding marks agree, and so does the kernel
`h(m, T) = Σ_{Y, obsRowLabel Y = T} a_Y(m)` on sets of cubes of the box.

## Main statements

* `remExt_congr_of_eqOn`, `hatCoeff_congr_of_eqOn`: the remainder extension and the coordinate
  derivative read their function only near the disc of radius `3/2`, resp. near `0`.
* `unitImage_unitPt`, `unitPt_eq_of_unitImage_eq`: the image `ιu` of the unit point of a site of
  the box is the unit point of the image site, and `ιu` is injective on the unit points of the box.
* `siteEv_twoTorus`: the terms of the site functional on two tori.
* `mem_polyDom_site_boxMap_iff`: the domains of the local cover of a site of the box on two tori.
-/

@[expose] public section

noncomputable section

open scoped Classical

namespace Balaban.Polymer.TwoTorusStep

open Balaban Balaban.Localization Balaban.Fluctuation Balaban.SmallField Balaban.SmallField.Def6
  Balaban.Background Balaban.Analysis Balaban.Polymer Balaban.Multiscale MeasureTheory Metric

/-! ### Functions read near a disc -/

section Read

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

omit [NormedSpace ℂ E] in
/-- **The remainder extension reads its function only on a disc of radius `ρ ≥ 3/2`.** -/
theorem remExt_congr_of_eqOn [NormedSpace ℂ E] {e e' : ℂ → E} {ρ : ℝ} (hρ : 3 / 2 ≤ ρ)
    (h : ∀ ζ : ℂ, ‖ζ‖ < ρ → e' ζ = e ζ) (u : ℂ) : remExt e' u = remExt e u := by
  by_cases hu : ‖u‖ < 3 / 2
  · have hd : ∀ v : ℂ, ‖v‖ < 3 / 2 → deriv e' v = deriv e v := by
      intro v hv
      refine Filter.EventuallyEq.deriv_eq ?_
      filter_upwards [(isOpen_ball (x := (0 : ℂ)) (ε := ρ)).mem_nhds
        (show v ∈ ball (0 : ℂ) ρ by rw [mem_ball_zero_iff]; linarith)] with ζ hζ
      exact h ζ (by simpa using hζ)
    rw [remExt_eq_of_lt _ hu, remExt_eq_of_lt _ hu, hd u hu, hd 0 (by simp)]
  · rw [remExt_eq_zero_of_le _ (not_lt.1 hu), remExt_eq_zero_of_le _ (not_lt.1 hu)]

/-- **The coordinate derivative reads its function only near `0`.**  If
`E' (r', ζ • e') = E (r, ζ • e)` for `‖ζ‖ < ρ` (`ρ > 0`), the coefficients agree. -/
theorem hatCoeff_congr_of_eqOn {R R' P P' : Type*} {E : R × (P → ℂ) → ℂ}
    {E' : R' × (P' → ℂ) → ℂ} {r : R} {r' : R'} {e : P → ℂ} {e' : P' → ℂ} {ρ : ℝ} (hρ : 0 < ρ)
    (h : ∀ ζ : ℂ, ‖ζ‖ < ρ → E' (r', ζ • e') = E (r, ζ • e)) :
    hatCoeff E' r' e' = hatCoeff E r e := by
  unfold hatCoeff
  refine Filter.EventuallyEq.deriv_eq ?_
  filter_upwards [ball_mem_nhds (0 : ℂ) hρ] with ζ hζ
  exact h ζ (by simpa using hζ)

end Read

/-! ### The unit points of the box -/

section UnitPoints

variable {d L N₁ N₁' m₁ k : ℕ} [NeZero N₁] [NeZero N₁'] [NeZero L] {ϱ : ℝ}

set_option hygiene false in
local notation "bm" => boxMap ((N₁ * L ^ m₁) * L ^ (k + 1)) ((N₁' * L ^ m₁) * L ^ (k + 1))
set_option hygiene false in
local notation "bm'" => boxMap ((N₁' * L ^ m₁) * L ^ (k + 1)) ((N₁ * L ^ m₁) * L ^ (k + 1))
set_option hygiene false in
local notation "bU" => boxMap ((N₁ * L ^ m₁) * L ^ (k + 1 - k)) ((N₁' * L ^ m₁) * L ^ (k + 1 - k))
set_option hygiene false in
local notation "GA" => levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ)
  (k + 1) le_rfl
set_option hygiene false in
local notation "GB" => levelGS (d := d) (L := L) (N₁ := N₁') (m₁ := m₁) (k := k + 1) (ϱ := ϱ)
  (k + 1) le_rfl
set_option hygiene false in
local notation "ιu" b:max => (Subtype.mk (bU (b : UnitTorus d L N₁ m₁ k))
  (mem_unitPts_levelTop (d := d) (L := L) (N₁ := N₁') (m₁ := m₁) (k := k) (ϱ := ϱ) _) :
    unitPts (GB))

/-- The image `ιu` of the unit point of a site of the box is the unit point of the image site.
Margin: `2 ρ + 3 L^(k+1) + 5 < N₁ L^m₁ L^(k+1)`. -/
theorem unitImage_unitPt {ρ : ℕ} (hn : 2 * ρ + 3 * L ^ (k + 1) + 5 < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hGA : IsLevel (GA) (k + 1)) (hGB : IsLevel (GB) (k + 1))
    {x : CTorus d L N₁ m₁ (k + 1)} (hx : InBox d ρ ((N₁ * L ^ m₁) * L ^ (k + 1)) x) :
    ιu (unitPt hGA x) = unitPt hGB (bm x) :=
  Subtype.ext (unitBlock_boxMap hn hx).symm

/-- **`ιu` is injective on the unit points of the box.**  Margins:
`2 ρ + 3 L^(k+1) + 5 < N₁ L^m₁ L^(k+1), N₁′ L^m₁ L^(k+1)`. -/
theorem unitPt_eq_of_unitImage_eq {ρ : ℕ}
    (hn : 2 * ρ + 3 * L ^ (k + 1) + 5 < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hn' : 2 * ρ + 3 * L ^ (k + 1) + 5 < (N₁' * L ^ m₁) * L ^ (k + 1))
    (hGA : IsLevel (GA) (k + 1)) (hGB : IsLevel (GB) (k + 1))
    {x₁ x₂ : CTorus d L N₁ m₁ (k + 1)} (hx₁ : InBox d ρ ((N₁ * L ^ m₁) * L ^ (k + 1)) x₁)
    (hx₂ : InBox d ρ ((N₁ * L ^ m₁) * L ^ (k + 1)) x₂)
    (h : ιu (unitPt hGA x₁) = ιu (unitPt hGA x₂)) : unitPt hGA x₁ = unitPt hGA x₂ := by
  have hm' : 2 * ρ + 1 < (N₁' * L ^ m₁) * L ^ (k + 1) := by omega
  rw [unitImage_unitPt hn hGA hGB hx₁, unitImage_unitPt hn hGA hGB hx₂] at h
  have h1 : unitBlock (bm x₁) = unitBlock (bm x₂) := congrArg Subtype.val h
  have e1 := unitBlock_boxMap (N₁ := N₁') (N₁' := N₁) hn' (inBox_boxMap hm' hx₁)
  have e2 := unitBlock_boxMap (N₁ := N₁') (N₁' := N₁) hn' (inBox_boxMap hm' hx₂)
  rw [boxMap_boxMap hm' hx₁] at e1
  rw [boxMap_boxMap hm' hx₂] at e2
  apply Subtype.ext
  show unitBlock x₁ = unitBlock x₂
  rw [e1, e2, h1]

end UnitPoints

/-! ### The terms of the site functional on two tori -/

section SiteEv

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
set_option hygiene false in
local notation "XA" => (↑(LocalCover.nbhdF m₀ xs) : Set (CTorus d L N₁ m₁ (k + 1)))
set_option hygiene false in
local notation "XB" => (↑(LocalCover.nbhdF m₀ (bm xs)) : Set (CTorus d L N₁' m₁ (k + 1)))

/-- **D3 (a): the terms of the site functional on two tori.**  `Ev_localCover_twoTorus` for the
site functional `siteFun … xs iy` (`δφ(xs, iy)`, which reads the fluctuation field at `xs` only)
and its image at `bm xs`: for the local covers of a site `xs` and of `bm xs`, a domain `Y` of the
box and corresponding data (raw data agreeing on the box, hat variables agreeing at corresponding
unit points), the terms `evTerm … (siteFun …)` of `bm '' Y` and of `Y` are equal. -/
theorem siteEv_twoTorus
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
    {m₀ : ℕ} (hN : L ^ m₀ ∣ N₁) (hN' : L ^ m₀ ∣ N₁') (xs : CTorus d L N₁ m₁ (k + 1))
    (iy : Fin N)
    {R : ℕ} (hX₁R : ∀ x ∈ LocalCover.nbhd m₀ xs, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x)
    {Y : Set (CTorus d L N₁ m₁ (k + 1))}
    (hYR : ∀ y ∈ Y, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) y)
    (hn : 4 * R + 12 * L ^ (k + 1 + m₁) + 7 * L ^ (k + 1) + 5 < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hn' : 4 * R + 12 * L ^ (k + 1 + m₁) + 7 * L ^ (k + 1) + 5 < (N₁' * L ^ m₁) * L ^ (k + 1))
    (hnS : 2 * (ρ₁) + 5 * (L * cellSide L 0 m₁ (k + 1)) < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hnS' : 2 * (ρ₁) + 5 * (L * cellSide L 0 m₁ (k + 1)) < (N₁' * L ^ m₁) * L ^ (k + 1))
    (hnF : 2 * R + 5 * (L * cellSide L m₀ m₁ (k + 1)) < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hnF' : 2 * R + 5 * (L * cellSide L m₀ m₁ (k + 1)) < (N₁' * L ^ m₁) * L ^ (k + 1))
    {D : BgData (GA) N} {D' : BgData (GB) N}
    (hD : XiCData (GA) (compWeight L a₁) ν (k + 1) 1 eps D)
    (hD' : XiCData (GB) (compWeight L a₁) ν (k + 1) 1 eps D')
    (hraw : RawBoxAgree {z | InBox d (R + 3 * L ^ (k + 1)) ((N₁ * L ^ m₁) * L ^ (k + 1)) z}
      (rawOf D) (rawOf D'))
    {ψh : unitPts (GA) × Fin N → ℂ} {ψh' : unitPts (GB) × Fin N → ℂ}
    (hψh : ∀ p, ‖ψh p‖ ≤ cψ) (hψh' : ∀ p, ‖ψh' p‖ ≤ cψ)
    (hhat : ∀ x, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x →
      ∀ i, ψh' (unitPt hGB (bm x), i) = ψh (unitPt hGA x, i))
    (hrad : markedRad d L N k a₁ κ cψ cc < δ₁) :
    evTerm (fun i : ParIdx (GB) (XB) => i.1.1) (GB)
        m₀ (X1 (GB) m₀ k (LocalCover.fam m₀ (bm xs)))
        (fun u s => siteFun (GB) (HB) (bm xs) iy
          (F₁' (extParams (GB) (XB) s, u.1))
          (Sol' (extParams (GB) (XB) s,
            flEdat (GB) (HB) (F₁' (extParams (GB)
              (XB) s, u.1)) u.1.1
              (hatPsiF (GB) a₁ ν hGB cc F₁'
                (extParams (GB) (XB) s) u.1 u.2))).1
          (u.1, hatPsiF (GB) a₁ ν hGB cc F₁'
            (extParams (GB) (XB) s) u.1 u.2))
        (bm '' Y) (rawOf D', ψh') =
      evTerm (fun i : ParIdx (GA) (XA) => i.1.1) (GA) m₀
        (X1 (GA) m₀ k (LocalCover.fam m₀ xs))
        (fun u s => siteFun (GA) (HA) xs iy (F₁ (extParams (GA) (XA) s, u.1))
          (Sol (extParams (GA) (XA) s,
            flEdat (GA) (HA) (F₁ (extParams (GA) (XA) s, u.1))
              u.1.1 (hatPsiF (GA) a₁ ν hGA cc F₁
                (extParams (GA) (XA) s) u.1 u.2))).1
          (u.1, hatPsiF (GA) a₁ ν hGA cc F₁
            (extParams (GA) (XA) s) u.1 u.2))
        Y (rawOf D, ψh) :=
  Ev_localCover_twoTorus hC hC' hk hGA hGB cc hcψ hMX hmar hαK hsm hF₁ hF₁' hSol hSol' hN hN' xs
    (Φ := siteFun (GA) (HA) xs iy) (Φ' := siteFun (GB) (HB) (bm xs) iy)
    (Rα := ∅) (Rδ := {xs}) (Rψ := ∅) (fun x hx => absurd hx (Set.notMem_empty x))
    (Set.singleton_subset_iff.2 (Finset.mem_coe.2 (LocalCover.mem_nbhdF_self m₀ xs)))
    (Set.empty_subset _)
    (fun t t' _ hδ _ => svec_levelGS_boxMap hk (fun w w' hw hw' i =>
      hδ w w' (by rw [hw]; exact Set.mem_singleton _) (by rw [hw', hw]) i) iy)
    hX₁R hYR hn hn' hnS hnS' hnF hnF' ((siteFun_analytic xs iy).mono (Set.subset_univ _))
    hD hD' hraw hψh hψh' hhat hrad

end SiteEv

/-! ### The domains of the local cover of a site, the labels of the kernel -/

section Domains

variable {d L N₁ N₁' m₁ k : ℕ} [NeZero N₁] [NeZero N₁'] [NeZero L] {ϱ : ℝ}

set_option hygiene false in
local notation "bm" => boxMap ((N₁ * L ^ m₁) * L ^ (k + 1)) ((N₁' * L ^ m₁) * L ^ (k + 1))
set_option hygiene false in
local notation "GA" => levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ)
  (k + 1) le_rfl
set_option hygiene false in
local notation "GB" => levelGS (d := d) (L := L) (N₁ := N₁') (m₁ := m₁) (k := k + 1) (ϱ := ϱ)
  (k + 1) le_rfl
set_option hygiene false in
local notation "aK" => cellSide L m₀ m₁ (k + 1)
set_option hygiene false in
local notation "σc" => cubeMap (d := d) (L := L) (N₁ := N₁) (N₁' := N₁') (m₁ := m₁) (K := k + 1)
  hN hN' (le_refl (k + 1))

/-- **The domains of the local cover of a site of the box on two tori.**  If the neighbourhood of
the site `xs` and the set `Y` lie in the box of radius `R`, then `bm '' Y` is a domain of the
expansion with the local cover of `bm xs` iff `Y` is one with the local cover of `xs`.  Margin:
`2 R + 5 L a_K < N₁ L^m₁ L^(k+1), N₁′ L^m₁ L^(k+1)`. -/
theorem mem_polyDom_site_boxMap_iff {m₀ R : ℕ} (hN : L ^ m₀ ∣ N₁) (hN' : L ^ m₀ ∣ N₁')
    (hnF : 2 * R + 5 * (L * aK) < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hnF' : 2 * R + 5 * (L * aK) < (N₁' * L ^ m₁) * L ^ (k + 1))
    (xs : CTorus d L N₁ m₁ (k + 1))
    (hX₁R : ∀ x ∈ LocalCover.nbhd m₀ xs, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x)
    {Y : Set (CTorus d L N₁ m₁ (k + 1))}
    (hYR : ∀ y ∈ Y, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) y) :
    bm '' Y ∈ polyDom (GB) (LocalCover.nbhdF m₀ (bm xs)) m₀ k (LocalCover.fam m₀ (bm xs)) ↔
      Y ∈ polyDom (GA) (LocalCover.nbhdF m₀ xs) m₀ k (LocalCover.fam m₀ xs) := by
  have hcs : (L - 1) * aK ≤ L * aK := Nat.mul_le_mul_right _ (Nat.sub_le L 1)
  obtain ⟨hcov, hX₁, hcov', hX₁'⟩ := covSetup_localCover_image (ϱ := ϱ) hN hN' (j := k) le_rfl
    (R := R) (by omega) xs hX₁R
  have hF := nbhdF_image_finset hN hN' (R := R) (by omega) xs hX₁R
  have hXR : ∀ x ∈ LocalCover.nbhdF m₀ xs, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x :=
    fun x hx => hX₁R x (by rw [← LocalCover.coe_nbhdF]; exact hx)
  have h := mem_polyDom_boxMap_iff hcov hX₁ hcov' hX₁' hXR hnF hnF' Y hYR
  rw [hF] at h
  exact h

omit [NeZero N₁] [NeZero L] in
/-- The sites of a set of cubes of the box lie in the box. -/
theorem inBox_of_mem_sitesOf {m₀ R : ℕ}
    {T : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) m₀ (k + 1)
      Set.univ)}
    (hT : ∀ b ∈ T, ∀ x ∈ box b.1 aK, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x)
    {x : CTorus d L N₁ m₁ (k + 1)} (hx : x ∈ sitesOf T) :
    InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x := by
  obtain ⟨b, hb, hxb⟩ := mem_sitesOf.1 hx
  exact hT b hb x hxb

/-- A domain whose cube label lies in `T` (cubes of the box) lies in the box. -/
theorem inBox_of_blocksOf_subset {m₀ R : ℕ} (hN : L ^ m₀ ∣ N₁)
    {T : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) m₀ (k + 1)
      Set.univ)}
    (hT : ∀ b ∈ T, ∀ x ∈ box b.1 aK, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x)
    {Y : Set (CTorus d L N₁ m₁ (k + 1))} (hY : IsDj m₀ (k + 1) Y)
    (hYT : blocksOf m₀ (k + 1) Set.univ Y ⊆ T) :
    ∀ x ∈ Y, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x := by
  intro x hx
  have hs := sitesOf_blocksOf hN (le_refl (k + 1)) isPiUnion_univ_aux hY.2.1
  have hx' : x ∈ sitesOf (blocksOf m₀ (k + 1) Set.univ Y) := by rw [hs]; exact ⟨hx, trivial⟩
  obtain ⟨b, hb, hxb⟩ := mem_sitesOf.1 hx'
  exact hT b (hYT hb) x hxb

/-- `cubeMap` is injective on the cubes whose base point lies in the box. -/
theorem cubeMap_injOn_box {m₀ R : ℕ} (hN : L ^ m₀ ∣ N₁) (hN' : L ^ m₀ ∣ N₁')
    (hm' : 2 * R + 1 < (N₁' * L ^ m₁) * L ^ (k + 1))
    {S : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) m₀ (k + 1)
      Set.univ)}
    (hS : ∀ b ∈ S, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) b.1) :
    Set.InjOn (σc) (S : Set _) := by
  intro b₁ hb₁ b₂ hb₂ h
  have h1 := congrArg Subtype.val h
  rw [cubeMap_val, cubeMap_val] at h1
  exact Subtype.ext (boxMap_inj (hm' := hm') (hS b₁ hb₁) (hS b₂ hb₂) h1)

/-- **D3 (b): the kernel of the observable on two tori.**  For the local covers of a site `xs` of
the box and of `bm xs`, coefficients `c`, `c'` of the domains with `c' (bm '' Y) = c Y` for the
domains `Y` of the box, and a set `T₁` of cubes of the box: the kernels
`obsHker 𝒴 c m₀ T = Σ_{Y ∈ 𝒴, obsRowLabel Y = T} c Y` of the domain families of the two local
covers agree at `cubeMap '' T₁` and at `T₁`.  The domains with label `T₁` (resp. `cubeMap '' T₁`)
are the domains of the box with these labels, and they correspond by `bm`
(`mem_polyDom_site_boxMap_iff`, `blocksOf_image_boxMap`).  Margin:
`2 R + 5 L a_K < N₁ L^m₁ L^(k+1), N₁′ L^m₁ L^(k+1)`. -/
theorem obsHker_twoTorus {m₀ R : ℕ} (hN : L ^ m₀ ∣ N₁) (hN' : L ^ m₀ ∣ N₁')
    (hnF : 2 * R + 5 * (L * aK) < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hnF' : 2 * R + 5 * (L * aK) < (N₁' * L ^ m₁) * L ^ (k + 1))
    (xs : CTorus d L N₁ m₁ (k + 1))
    (hX₁R : ∀ x ∈ LocalCover.nbhd m₀ xs, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x)
    (hdj : ∀ Y ∈ polyDom (GA) (LocalCover.nbhdF m₀ xs) m₀ k (LocalCover.fam m₀ xs),
      IsDj m₀ (k + 1) Y)
    (hdj' : ∀ Y ∈ polyDom (GB) (LocalCover.nbhdF m₀ (bm xs)) m₀ k (LocalCover.fam m₀ (bm xs)),
      IsDj m₀ (k + 1) Y)
    (c : Set (CTorus d L N₁ m₁ (k + 1)) → ℂ) (c' : Set (CTorus d L N₁' m₁ (k + 1)) → ℂ)
    (hc : ∀ Y ∈ polyDom (GA) (LocalCover.nbhdF m₀ xs) m₀ k (LocalCover.fam m₀ xs),
      (∀ y ∈ Y, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) y) → c' (bm '' Y) = c Y)
    (T₁ : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) m₀ (k + 1)
      Set.univ))
    (hT₁ : ∀ b ∈ T₁, ∀ x ∈ box b.1 aK, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x) :
    obsHker (polyDom (GB) (LocalCover.nbhdF m₀ (bm xs)) m₀ k (LocalCover.fam m₀ (bm xs))) c' m₀
        (T₁.image (σc)) =
      obsHker (polyDom (GA) (LocalCover.nbhdF m₀ xs) m₀ k (LocalCover.fam m₀ xs)) c m₀ T₁ := by
  classical
  have ha := cellSide_pos (L := L) m₀ m₁ (k + 1)
  have hcs : aK ≤ L * aK := cellSide_le_mul
  have hm : 2 * R + 1 < (N₁ * L ^ m₁) * L ^ (k + 1) := by omega
  have hm' : 2 * R + 1 < (N₁' * L ^ m₁) * L ^ (k + 1) := by omega
  have hsT := sitesOf_image_cubeMap hN hN' (le_refl (k + 1)) (r := R) (by omega) T₁
    (fun x hx => inBox_of_mem_sitesOf hT₁ hx)
  unfold obsHker
  refine sum_image_boxMap_of_inBox hm hm' _ _ c c' ?_ ?_ ?_ ?_
  · intro Y hY
    rw [Finset.mem_filter] at hY
    exact inBox_of_blocksOf_subset hN hT₁ (hdj Y hY.1) (le_of_eq hY.2)
  · intro Y' hY'
    rw [Finset.mem_filter] at hY'
    intro y hy
    have hDj := hdj' Y' hY'.1
    have hs := sitesOf_blocksOf hN' (le_refl (k + 1)) isPiUnion_univ_aux hDj.2.1
    have hy' : y ∈ sitesOf (blocksOf m₀ (k + 1) Set.univ Y') := by rw [hs]; exact ⟨hy, trivial⟩
    change y ∈ sitesOf (obsRowLabel m₀ (k + 1) Y') at hy'
    rw [hY'.2, hsT] at hy'
    obtain ⟨w, hw, rfl⟩ := hy'
    exact inBox_boxMap hm' (inBox_of_mem_sitesOf hT₁ hw)
  · intro Y hYR
    rw [Finset.mem_filter, Finset.mem_filter,
      mem_polyDom_site_boxMap_iff (ϱ := ϱ) hN hN' hnF hnF' xs hX₁R hYR]
    refine and_congr_right fun _ => ?_
    change blocksOf m₀ (k + 1) Set.univ (bm '' Y) = T₁.image (σc) ↔
      blocksOf m₀ (k + 1) Set.univ Y = T₁
    rw [blocksOf_image_boxMap hN hN' (by omega) (by omega) hYR]
    refine ⟨fun h => ?_, fun h => by rw [h]⟩
    have hS : ∀ b ∈ blocksOf m₀ (k + 1) Set.univ Y ∪ T₁,
        InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) b.1 := by
      intro b hb
      rcases Finset.mem_union.1 hb with hb | hb
      · exact hYR b.1 ((mem_blocksOf.1 hb) (mem_box_self _ ha))
      · exact hT₁ b hb b.1 (mem_box_self _ ha)
    exact eq_of_image_eq_of_injOn (cubeMap_injOn_box hN hN' hm' hS) Finset.subset_union_left
      Finset.subset_union_right h
  · intro Y hY
    rw [Finset.mem_filter] at hY
    exact hc Y hY.1 (inBox_of_blocksOf_subset hN hT₁ (hdj Y hY.1) (le_of_eq hY.2))

end Domains

/-! ### The coefficients and the marks of two steps -/

section StepMarks

open Balaban.Inhabited Balaban.Inhabited.LevelStep

variable {d L N₁ N₁' m₁ k N : ℕ} [NeZero N₁] [NeZero N₁'] [NeZero L] {ϱ : ℝ}

set_option hygiene false in
local notation "bm" => boxMap ((N₁ * L ^ m₁) * L ^ (k + 1)) ((N₁' * L ^ m₁) * L ^ (k + 1))
set_option hygiene false in
local notation "bU" => boxMap ((N₁ * L ^ m₁) * L ^ (k + 1 - k)) ((N₁' * L ^ m₁) * L ^ (k + 1 - k))
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
local notation "ιu" b:max => (Subtype.mk (bU (b : UnitTorus d L N₁ m₁ k))
  (mem_unitPts_levelTop (d := d) (L := L) (N₁ := N₁') (m₁ := m₁) (k := k) (ϱ := ϱ) _) : (SB).U)

/-- The unit vectors of corresponding marks agree at corresponding unit points of the box: for a
site `x₀` of the box and every site `x` of the box,
`e_{(ιu u₀, a)}(unitPt (bm x), i) = e_{(u₀, a)}(unitPt x, i)` with `u₀ = unitPt x₀`.  Margins:
`2 R + 3 L^(k+1) + 5 < N₁ L^m₁ L^(k+1), N₁′ L^m₁ L^(k+1)`. -/
theorem obsUnitVec_unitImage (hN2 : 2 ≤ N) (hk : 1 ≤ k) (νS β p₁ δ : ℝ) {R : ℕ}
    (hn : 2 * R + 3 * L ^ (k + 1) + 5 < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hn' : 2 * R + 3 * L ^ (k + 1) + 5 < (N₁' * L ^ m₁) * L ^ (k + 1))
    {x₀ : CTorus d L N₁ m₁ (k + 1)} (hx₀ : InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x₀)
    (a : Fin N) {x : CTorus d L N₁ m₁ (k + 1)} (hx : InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x)
    (i : Fin N) :
    obsUnitVec (SB) (ιu (unitPt (SA).hG' x₀), a) (unitPt (SB).hG' (bm x), i) =
      obsUnitVec (SA) (unitPt (SA).hG' x₀, a) (unitPt (SA).hG' x, i) := by
  have hx' : unitPt (SB).hG' (bm x) = ιu (unitPt (SA).hG' x) :=
    (unitImage_unitPt hn (SA).hG' (SB).hG' hx).symm
  rw [hx']
  unfold obsUnitVec
  by_cases h : (unitPt (SA).hG' x, i) = (unitPt (SA).hG' x₀, a)
  · rw [Prod.mk.injEq] at h
    rw [h.1, h.2, Pi.single_eq_same, Pi.single_eq_same]
  · rw [Pi.single_eq_of_ne h, Pi.single_eq_of_ne]
    intro h'
    rw [Prod.mk.injEq] at h'
    exact h (Prod.ext (unitPt_eq_of_unitImage_eq hn hn' (SA).hG' (SB).hG' hx hx₀ h'.1) h'.2)

/-- **D3 (b): the coefficients of corresponding marks on two tori.**  Let the terms `Ev' Y'` and
`Ev Y` take equal values at hat variables of norm `≤ c_ψ` that agree at corresponding unit points of
the box.  Then for a site `x₀` of the box the coordinate derivatives along the unit vectors of the
marks `(ιu u₀, a)` and `(u₀, a)`, `u₀ = unitPt x₀`, agree. -/
theorem hatCoeff_obsUnitVec_twoTorus (hN2 : 2 ≤ N) (hk : 1 ≤ k) (νS β p₁ δ : ℝ) {R : ℕ}
    (hn : 2 * R + 3 * L ^ (k + 1) + 5 < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hn' : 2 * R + 3 * L ^ (k + 1) + 5 < (N₁' * L ^ m₁) * L ^ (k + 1))
    {Rw Rw' : Type*} {E : Rw × ((SA).U × Fin N → ℂ) → ℂ} {E' : Rw' × ((SB).U × Fin N → ℂ) → ℂ}
    {r : Rw} {r' : Rw'} {cψ : ℝ} (hcψ : 0 < cψ)
    (hE : ∀ (ψh : (SA).U × Fin N → ℂ) (ψh' : (SB).U × Fin N → ℂ), (∀ q, ‖ψh q‖ ≤ cψ) →
      (∀ q, ‖ψh' q‖ ≤ cψ) →
      (∀ x, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x →
        ∀ i, ψh' (unitPt (SB).hG' (bm x), i) = ψh (unitPt (SA).hG' x, i)) →
      E' (r', ψh') = E (r, ψh))
    {x₀ : CTorus d L N₁ m₁ (k + 1)} (hx₀ : InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x₀)
    (a : Fin N) :
    hatCoeff E' r' (obsUnitVec (SB) (ιu (unitPt (SA).hG' x₀), a)) =
      hatCoeff E r (obsUnitVec (SA) (unitPt (SA).hG' x₀, a)) := by
  refine hatCoeff_congr_of_eqOn hcψ fun ζ hζ => hE _ _ (smul_mem_ball (norm_obsUnitVec_le _ _) hζ)
    (smul_mem_ball (norm_obsUnitVec_le _ _) hζ) fun x hx i => ?_
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [obsUnitVec_unitImage hN2 hk νS β p₁ δ hn hn' hx₀ a hx i]

/-- **D3 (c): the first-order marks on two tori.**  For a site `x₀` of the box and block variables
`Φ`, `Φ'` agreeing at corresponding unit points of the box, the clamped first-order marks of
`(ιu u₀, a)` and `(u₀, a)`, `u₀ = unitPt x₀`, agree (`hatOf_boxMap`).  Margin:
`2 R + 3 L^(k+1) + 5 < N₁ L^m₁ L^(k+1)`. -/
theorem blockMarkC_twoTorus (hN2 : 2 ≤ N) (hk : 1 ≤ k) (νS β p₁ δ : ℝ) {m₀ R : ℕ}
    (hn : 2 * R + 3 * L ^ (k + 1) + 5 < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hp : 0 < (SA).p₁) (hp' : 0 < (SB).p₁)
    {Φ : ∀ c, ((SA).blockSplit m₀ hp).Ωb c} {Φ' : ∀ c, ((SB).blockSplit m₀ hp').Ωb c}
    (hΦ : ∀ x, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x →
      Φ' ((SB).cellOf m₀ (unitPt (SB).hG' (bm x))) ⟨unitPt (SB).hG' (bm x), rfl⟩ =
        Φ ((SA).cellOf m₀ (unitPt (SA).hG' x)) ⟨unitPt (SA).hG' x, rfl⟩)
    {x₀ : CTorus d L N₁ m₁ (k + 1)} (hx₀ : InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x₀)
    (a : Fin N) :
    blockMarkC (SB) m₀ hp' (ιu (unitPt (SA).hG' x₀)) a Φ' =
      blockMarkC (SA) m₀ hp (unitPt (SA).hG' x₀) a Φ := by
  have h2 : unitPt (SB).hG' (bm x₀) = ιu (unitPt (SA).hG' x₀) :=
    unitPt_boxMap hn (SA).hG' (SB).hG' hx₀
  have h : (SB).hatOf m₀ (SB).p₁ hp' Φ' (unitPt (SB).hG' (bm x₀), a) =
      (SA).hatOf m₀ (SA).p₁ hp Φ (unitPt (SA).hG' x₀, a) :=
    hatOf_boxMap (SA).hG' (SB).hG' hN2 hk νS β p₁ δ m₀ p₁ hp hp' Φ Φ' hΦ x₀ hx₀ a
  rw [h2] at h
  exact h

/-- **D3 (d): the remainder marks on two tori.**  Let the terms `Ev' Y'` and `Ev Y` take equal
values at hat variables of norm `≤ c_ψ` that agree at corresponding unit points of the box.  For
block variables `Φ`, `Φ'` agreeing at corresponding unit points of the box, the remainder marks
`obsGrRawC` of `Y'` and `Y` (the remainders of the expansion along the ray `ζ ↦ ζ ψ̂(Φ)` of the
clamped hat variables) agree, for `p₁ / c_ψ ≤ 1/4`. -/
theorem obsGrRawC_twoTorus (hN2 : 2 ≤ N) (hk : 1 ≤ k) (νS β p₁ δ : ℝ) {m₀ R : ℕ}
    (hp : 0 < (SA).p₁) (hp' : 0 < (SB).p₁)
    {Ev : Set (CTorus d L N₁ m₁ (k + 1)) →
      RawData d L (N₁ * L ^ m₁) (k + 1) N × ((SA).U × Fin N → ℂ) → ℂ}
    {Ev' : Set (CTorus d L N₁' m₁ (k + 1)) →
      RawData d L (N₁' * L ^ m₁) (k + 1) N × ((SB).U × Fin N → ℂ) → ℂ}
    {𝒴 : Finset (Set (CTorus d L N₁ m₁ (k + 1)))} {𝒴' : Finset (Set (CTorus d L N₁' m₁ (k + 1)))}
    (Y : {Y // Y ∈ 𝒴}) (Y' : {Y' // Y' ∈ 𝒴'})
    {r : RawData d L (N₁ * L ^ m₁) (k + 1) N} {r' : RawData d L (N₁' * L ^ m₁) (k + 1) N}
    {cψ : ℝ} (hcψ : 0 < cψ) (hq : (SA).p₁ / cψ ≤ 1 / 4)
    (hE : ∀ (ψh : (SA).U × Fin N → ℂ) (ψh' : (SB).U × Fin N → ℂ), (∀ q, ‖ψh q‖ ≤ cψ) →
      (∀ q, ‖ψh' q‖ ≤ cψ) →
      (∀ x, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x →
        ∀ i, ψh' (unitPt (SB).hG' (bm x), i) = ψh (unitPt (SA).hG' x, i)) →
      Ev' Y'.1 (r', ψh') = Ev Y.1 (r, ψh))
    {Φ : ∀ c, ((SA).blockSplit m₀ hp).Ωb c} {Φ' : ∀ c, ((SB).blockSplit m₀ hp').Ωb c}
    (hΦ : ∀ x, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x →
      Φ' ((SB).cellOf m₀ (unitPt (SB).hG' (bm x))) ⟨unitPt (SB).hG' (bm x), rfl⟩ =
        Φ ((SA).cellOf m₀ (unitPt (SA).hG' x)) ⟨unitPt (SA).hG' x, rfl⟩) (u : ℂ) :
    obsGrRawC (SB) m₀ hp' Ev' 𝒴' r' (some Y') u Φ' = obsGrRawC (SA) m₀ hp Ev 𝒴 r (some Y) u Φ := by
  have h4 : 4 ≤ cψ / p₁ := four_le_of hcψ hp hq
  have hhat : ∀ x, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x → ∀ i,
      (SB).hatOf m₀ (SB).p₁ hp' Φ' (unitPt (SB).hG' (bm x), i) =
        (SA).hatOf m₀ (SA).p₁ hp Φ (unitPt (SA).hG' x, i) :=
    hatOf_boxMap (SA).hG' (SB).hG' hN2 hk νS β p₁ δ m₀ p₁ hp hp' Φ Φ' hΦ
  show remExt (fun ζ : ℂ => Ev' Y'.1 (r', ζ • (SB).hatOf m₀ (SB).p₁ hp' Φ')) u =
    remExt (fun ζ : ℂ => Ev Y.1 (r, ζ • (SA).hatOf m₀ (SA).p₁ hp Φ)) u
  refine remExt_congr_of_eqOn (ρ := cψ / p₁) (by linarith) (fun ζ hζ => ?_) u
  refine hE _ _ (smul_mem_ball_p hp (norm_hatOf_p₁_le Φ) hζ)
    (smul_mem_ball_p hp' (norm_hatOf_p₁_le Φ') hζ) fun x hx i => ?_
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [hhat x hx i]

end StepMarks

end Balaban.Polymer.TwoTorusStep
