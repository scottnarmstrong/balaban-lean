/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Polymer.TwoTorusObsKernel

/-!
# The coefficient of the observable on two tori, given the correspondence of the activities

The coefficient of the observable of one step is
`obsCoeffParam μ Aact y1 G1 hker yr Gr θ T`: the resummed products of the kernel `hker` (the
coefficients `a_Y(m) = d/dζ|₀ Ev Y (Θ, ζ e_m)` regrouped by the cube labels of the domains `Y` of
the local cover of the site `y`) with the first-order terms of the clamped first-order marks
`blockMarkC`, plus the coefficient of the remainder marks `obsGrFam`, all on the observable labels
`obsLab Lab₀ _`.  Here the terms `Ev` are those of the site functional, in the explicit form
`Ev = evTerm … (siteFun …)` (the appended conjunct of `obsEv_fromTower_rawYG`).

`obsCoeffParam_twoTorus_of_activities` compares this coefficient on two tori, for the local covers
of a site `y` of the box and of `bm y`, corresponding parameters (raw data agreeing on the box) and
a set `T` of cubes of the box: the first-order labels and marks (D1, `blockMarkC_twoTorus`), the
kernel (`obsHker_twoTorus`, `hatCoeff_obsUnitVec_twoTorus`, `siteEv_twoTorus`) and the remainder
marks (`obsGrRawC_twoTorus`) are carried along `cubeMap` here; the correspondence of the active
labels and their activities (the hypotheses of `obsCoeffParam_blockSplit_twoTorus` on `Aact`)
remains a hypothesis.
-/

@[expose] public section

noncomputable section

open scoped Classical

namespace Balaban.Polymer.TwoTorusStep

open Balaban Balaban.Localization Balaban.Fluctuation Balaban.SmallField Balaban.SmallField.Def6
  Balaban.Background Balaban.Analysis Balaban.Polymer Balaban.Multiscale MeasureTheory Metric

section Assembly

open Balaban.Inhabited Balaban.Inhabited.LevelStep

variable {d L N₁ N₁' m₁ k N : ℕ} [NeZero N₁] [NeZero N₁'] [NeZero L] {ϱ : ℝ}

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
local notation "HA" => levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ)
  k (Nat.le_succ k)
set_option hygiene false in
local notation "HB" => levelGS (d := d) (L := L) (N₁ := N₁') (m₁ := m₁) (k := k + 1) (ϱ := ϱ)
  k (Nat.le_succ k)
set_option hygiene false in
local notation "ρ₁" => R + (3 * L ^ (k + 1 + m₁) + 3 * L ^ (k + 1 + 2)) + L ^ (k + 1 + m₁)
set_option hygiene false in
local notation "aK" => cellSide L m₀ m₁ (k + 1)
set_option hygiene false in
local notation "SA" => hatStepKG (d := d) (L := L) (N := N) (N₁ := N₁) hN2 k m₁ ϱ hk νS β p₁ δ
set_option hygiene false in
local notation "SB" => hatStepKG (d := d) (L := L) (N := N) (N₁ := N₁') hN2 k m₁ ϱ hk νS β p₁ δ
set_option hygiene false in
local notation "σc" => cubeMap (d := d) (L := L) (N₁ := N₁) (N₁' := N₁') (m₁ := m₁) (K := k + 1)
  hN hN' (le_refl (k + 1))
set_option hygiene false in
local notation "ιu" b:max => (Subtype.mk (bU (b : UnitTorus d L N₁ m₁ k))
  (mem_unitPts_levelTop (d := d) (L := L) (N₁ := N₁') (m₁ := m₁) (k := k) (ϱ := ϱ) _) : (SB).U)
set_option hygiene false in
local notation "XA" => (↑(LocalCover.nbhdF m₀ y) : Set (CTorus d L N₁ m₁ (k + 1)))
set_option hygiene false in
local notation "XB" => (↑(LocalCover.nbhdF m₀ (bm y)) : Set (CTorus d L N₁' m₁ (k + 1)))
set_option hygiene false in
local notation "𝒴A" => polyDom (GA) (LocalCover.nbhdF m₀ y) m₀ k (LocalCover.fam m₀ y)
set_option hygiene false in
local notation "𝒴B" => polyDom (GB) (LocalCover.nbhdF m₀ (bm y)) m₀ k (LocalCover.fam m₀ (bm y))

/-- **The terms of the site functional at corresponding parameters.**  `siteEv_twoTorus` for
parameters `θ`, `θ'` whose raw data lie in the charts and agree on the box: for every domain `Y` of
the box and hat variables of norm `≤ c_ψ` agreeing at corresponding unit points of the box,
`Ev' (bm '' Y) (θ'.1, ψ̂') = Ev Y (θ.1, ψ̂)`. -/
theorem siteEvParam_twoTorus (hN2 : 2 ≤ N) (hk : 1 ≤ k) (νS β p₁ δ : ℝ)
    {c BG κ eps Kc Cx c₂ BG₂ δ₁ : ℝ}
    (hC : FlCore N (GA) (HA) 1 νS c BG κ eps Kc Cx c₂ BG₂ δ₁)
    (hC' : FlCore N (GB) (HB) 1 νS c BG κ eps Kc Cx c₂ BG₂ δ₁)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δc : ℝ}
    (hmar : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hαK : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    {m₀ R : ℕ} (hN : L ^ m₀ ∣ N₁) (hN' : L ^ m₀ ∣ N₁')
    (hn : 4 * R + 12 * L ^ (k + 1 + m₁) + 7 * L ^ (k + 1) + 5 < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hn' : 4 * R + 12 * L ^ (k + 1 + m₁) + 7 * L ^ (k + 1) + 5 < (N₁' * L ^ m₁) * L ^ (k + 1))
    (hnS : 2 * (ρ₁) + 5 * (L * cellSide L 0 m₁ (k + 1)) < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hnS' : 2 * (ρ₁) + 5 * (L * cellSide L 0 m₁ (k + 1)) < (N₁' * L ^ m₁) * L ^ (k + 1))
    (hnF : 2 * R + 5 * (L * aK) < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hnF' : 2 * R + 5 * (L * aK) < (N₁' * L ^ m₁) * L ^ (k + 1))
    (y : CTorus d L N₁ m₁ (k + 1)) (iy : Fin N)
    (hX₁R : ∀ x ∈ LocalCover.nbhd m₀ y, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x)
    (cc : ℂ) {cψ : ℝ} (hcψ : 0 < cψ)
    (hrad : markedRad d L N k 1 κ cψ cc < δ₁)
    {F₁ : DecParams (GA) × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      ((GA).Ω 1 × Fin N → ℂ) × ((GA).Ω 1 → ℂ)}
    {F₁' : DecParams (GB) × RawData d L (N₁' * L ^ m₁) (k + 1) N →
      ((GB).Ω 1 × Fin N → ℂ) × ((GB).Ω 1 → ℂ)}
    (hF₁ : ∀ (s : DecParams (GA)) (D : BgData (GA) N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC (GA) (bgC0 d L N) (c7 d L N BG κ) νS D → ∀ (φ : (GA).Ω 1 × Fin N → ℂ)
        (α : (GA).Ω 1 → ℂ), IsDecBg (GA) (compWeight L 1) νS (rho4 d L N BG κ) s D φ α →
        F₁ (s, rawOf D) = (φ, α))
    (hF₁' : ∀ (s : DecParams (GB)) (D : BgData (GB) N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC (GB) (bgC0 d L N) (c7 d L N BG κ) νS D → ∀ (φ : (GB).Ω 1 × Fin N → ℂ)
        (α : (GB).Ω 1 → ℂ), IsDecBg (GB) (compWeight L 1) νS (rho4 d L N BG κ) s D φ α →
        F₁' (s, rawOf D) = (φ, α))
    {Sol : Dec2.DecParams (coverOf (GA)) × Edat (HA) N → ((HA).Ω 1 × Fin N → ℂ) × ((HA).Ω 1 → ℂ)}
    {Sol' : Dec2.DecParams (coverOf (GB)) × Edat (HB) N →
      ((HB).Ω 1 × Fin N → ℂ) × ((HB).Ω 1 → ℂ)}
    (hSol : ∀ p : Dec2.DecParams (coverOf (GA)) × Edat (HA) N, (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM (HA) N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2 →
        (Sol p).1 = dphi (HA) (Dec2.decG (coverOf (GA)) (HA) (compWeight L 1) νS p.1) p.2.2.1
          p.2.1 (pertSource (HA) (compWeight L 1) p.2.2.2.1 p.2.2.2.2) (Sol p).2 ∧
        Dec2.DecFixed (coverOf (GA)) (HA) (compWeight L 1) νS p.1 false p.2.2.1 p.2.1
          (pertSource (HA) (compWeight L 1) p.2.2.2.1 p.2.2.2.2) (Sol p).2 ∧
        Small (HA) (Sol p).2 (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
        Small (HA) (Sol p).2 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        SupBounds (HA) (Sol p).1 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        (∀ δα' : (HA).Ω 1 → ℂ, Small (HA) δα' (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf (GA)) (HA) (compWeight L 1) νS p.1 false p.2.2.1 p.2.1
            (pertSource (HA) (compWeight L 1) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol p).2))
    (hSol' : ∀ p : Dec2.DecParams (coverOf (GB)) × Edat (HB) N, (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM (HB) N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2 →
        (Sol' p).1 = dphi (HB) (Dec2.decG (coverOf (GB)) (HB) (compWeight L 1) νS p.1) p.2.2.1
          p.2.1 (pertSource (HB) (compWeight L 1) p.2.2.2.1 p.2.2.2.2) (Sol' p).2 ∧
        Dec2.DecFixed (coverOf (GB)) (HB) (compWeight L 1) νS p.1 false p.2.2.1 p.2.1
          (pertSource (HB) (compWeight L 1) p.2.2.2.1 p.2.2.2.2) (Sol' p).2 ∧
        Small (HB) (Sol' p).2 (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
        Small (HB) (Sol' p).2 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        SupBounds (HB) (Sol' p).1 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        (∀ δα' : (HB).Ω 1 → ℂ, Small (HB) δα' (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf (GB)) (HB) (compWeight L 1) νS p.1 false p.2.2.1 p.2.1
            (pertSource (HB) (compWeight L 1) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol' p).2))
    {Ev : Set (CTorus d L N₁ m₁ (k + 1)) →
      RawData d L (N₁ * L ^ m₁) (k + 1) N × ((SA).U × Fin N → ℂ) → ℂ}
    {Ev' : Set (CTorus d L N₁' m₁ (k + 1)) →
      RawData d L (N₁' * L ^ m₁) (k + 1) N × ((SB).U × Fin N → ℂ) → ℂ}
    (hEv : Ev = evTerm (fun i : ParIdx (GA) (XA) => i.1.1) (GA) m₀
        (X1 (GA) m₀ k (LocalCover.fam m₀ y))
        (fun u s => siteFun (GA) (HA) y iy (F₁ (extParams (GA) (XA) s, u.1))
          (Sol (extParams (GA) (XA) s,
            flEdat (GA) (HA) (F₁ (extParams (GA) (XA) s, u.1))
              u.1.1 (hatPsiF (GA) 1 νS (SA).hG' cc F₁
                (extParams (GA) (XA) s) u.1 u.2))).1
          (u.1, hatPsiF (GA) 1 νS (SA).hG' cc F₁
            (extParams (GA) (XA) s) u.1 u.2)))
    (hEv' : Ev' = evTerm (fun i : ParIdx (GB) (XB) => i.1.1) (GB)
        m₀ (X1 (GB) m₀ k (LocalCover.fam m₀ (bm y)))
        (fun u s => siteFun (GB) (HB) (bm y) iy
          (F₁' (extParams (GB) (XB) s, u.1))
          (Sol' (extParams (GB) (XB) s,
            flEdat (GB) (HB) (F₁' (extParams (GB)
              (XB) s, u.1)) u.1.1
              (hatPsiF (GB) 1 νS (SB).hG' cc F₁'
                (extParams (GB) (XB) s) u.1 u.2))).1
          (u.1, hatPsiF (GB) 1 νS (SB).hG' cc F₁'
            (extParams (GB) (XB) s) u.1 u.2)))
    (θ : physParam N (SA)) (θ' : physParam N (SB))
    (hθ : (θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) ∈
      XiCRaw (GA) (compWeight L 1) νS (k + 1) 1 eps)
    (hθ' : (θ'.1 : RawData d L (N₁' * L ^ m₁) (k + 1) N) ∈
      XiCRaw (GB) (compWeight L 1) νS (k + 1) 1 eps)
    (hraw : RawBoxAgree {z | InBox d (R + 3 * L ^ (k + 1)) ((N₁ * L ^ m₁) * L ^ (k + 1)) z}
      (θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) (θ'.1 : RawData d L (N₁' * L ^ m₁) (k + 1) N)) :
    ∀ Y : Set (CTorus d L N₁ m₁ (k + 1)),
      (∀ x ∈ Y, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x) →
      ∀ (ψh : (SA).U × Fin N → ℂ) (ψh' : (SB).U × Fin N → ℂ), (∀ q, ‖ψh q‖ ≤ cψ) →
        (∀ q, ‖ψh' q‖ ≤ cψ) →
        (∀ x, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x →
          ∀ i, ψh' (unitPt (SB).hG' (bm x), i) = ψh (unitPt (SA).hG' x, i)) →
        Ev' (bm '' Y) ((θ'.1 : RawData d L (N₁' * L ^ m₁) (k + 1) N), ψh') =
          Ev Y ((θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N), ψh) := by
  obtain ⟨D, hD, hDe⟩ := hθ
  obtain ⟨D', hD', hDe'⟩ := hθ'
  intro Y hYR ψh ψh' hψh hψh' hhat
  rw [hEv, hEv', hDe, hDe']
  exact siteEv_twoTorus hC hC' hk (SA).hG' (SB).hG' cc hcψ.le hMX hmar hαK hsm hF₁ hF₁' hSol
    hSol' hN hN' y iy hX₁R hYR hn hn' hnS hnS' hnF hnF' hD hD'
    (by rw [← hDe, ← hDe']; exact hraw) hψh hψh' hhat hrad

/-- **The correspondence of the first-order marks.**  For a set `T` of cubes of the box, the map
`(u, a) ↦ (ιu u, a)` on the marks whose first-order labels have blocks in `T` carries the blocks
of the labels along `cubeMap`, is injective, and reaches every mark of the second step whose label
has blocks in `cubeMap '' T`.  Margins: `2 R + 3 L^(k+1) + 5 < N₁ L^m₁ L^(k+1), N₁′ L^m₁ L^(k+1)`
and `2 R + L a_K < N₁ L^m₁ L^(k+1), N₁′ L^m₁ L^(k+1)`. -/
theorem obsMarkLabels_twoTorus (hN2 : 2 ≤ N) (hk : 1 ≤ k) (νS β p₁ δ : ℝ) {m₀ R : ℕ}
    (hN : L ^ m₀ ∣ N₁) (hN' : L ^ m₀ ∣ N₁')
    (hn2 : 2 * R + 3 * L ^ (k + 1) + 5 < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hn2' : 2 * R + 3 * L ^ (k + 1) + 5 < (N₁' * L ^ m₁) * L ^ (k + 1))
    (hnL : 2 * R + L * aK < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hnL' : 2 * R + L * aK < (N₁' * L ^ m₁) * L ^ (k + 1))
    {T : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) m₀ (k + 1)
      Set.univ)}
    (hT : ∀ b ∈ T, ∀ x ∈ box b.1 aK, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x)
    {Lb₀ Lb₀' : Type}
    (Lab₀ : CubeLabels (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) m₀ (k + 1)
      Set.univ Lb₀)
    (Lab₀' : CubeLabels (d := d) (L := L) (N₁ := N₁') (m₁ := m₁) (K := k + 1) m₀ (k + 1)
      Set.univ Lb₀')
    {𝒴 : Finset (Set (CTorus d L N₁ m₁ (k + 1)))} {𝒴' : Finset (Set (CTorus d L N₁' m₁ (k + 1)))}
    (hdj : ∀ Y ∈ 𝒴, IsDj m₀ (k + 1) Y) (hdj' : ∀ Y ∈ 𝒴', IsDj m₀ (k + 1) Y) :
    (∀ (i : ObsMarkIdx (SA))
      (_ : blocksOf m₀ (k + 1) Set.univ ((obsLab Lab₀ hdj).ysite (obsY1 m₀ (SA) Lb₀ 𝒴 i)) ⊆ T),
      blocksOf m₀ (k + 1) Set.univ
          ((obsLab Lab₀' hdj').ysite (obsY1 m₀ (SB) Lb₀' 𝒴' ((ιu i.1), i.2))) =
        (blocksOf m₀ (k + 1) Set.univ
          ((obsLab Lab₀ hdj).ysite (obsY1 m₀ (SA) Lb₀ 𝒴 i))).image (σc)) ∧
    (∀ (i₁ : ObsMarkIdx (SA))
      (_ : blocksOf m₀ (k + 1) Set.univ ((obsLab Lab₀ hdj).ysite (obsY1 m₀ (SA) Lb₀ 𝒴 i₁)) ⊆ T)
      (i₂ : ObsMarkIdx (SA))
      (_ : blocksOf m₀ (k + 1) Set.univ ((obsLab Lab₀ hdj).ysite (obsY1 m₀ (SA) Lb₀ 𝒴 i₂)) ⊆ T),
      (((ιu i₁.1), i₁.2) : ObsMarkIdx (SB)) = ((ιu i₂.1), i₂.2) → i₁ = i₂) ∧
    (∀ i' : ObsMarkIdx (SB),
      blocksOf m₀ (k + 1) Set.univ ((obsLab Lab₀' hdj').ysite (obsY1 m₀ (SB) Lb₀' 𝒴' i')) ⊆
        T.image (σc) →
      ∃ (i : ObsMarkIdx (SA))
        (_ : blocksOf m₀ (k + 1) Set.univ ((obsLab Lab₀ hdj).ysite (obsY1 m₀ (SA) Lb₀ 𝒴 i)) ⊆ T),
        (((ιu i.1), i.2) : ObsMarkIdx (SB)) = i') := by
  refine ⟨fun i hi => ?_, fun i₁ hi₁ i₂ hi₂ h => ?_, fun i' hi' => ?_⟩
  · obtain ⟨hbox, -⟩ := obsY1_label_inBox hN2 hk νS β p₁ δ hN hT Lab₀ hdj i hi
    exact blocksOf_obsY1_unitImage hN2 hk νS β p₁ δ hN hN' hn2 hnL hnL' Lab₀ Lab₀' hdj hdj' i hbox
  · obtain ⟨-, x₁, hx₁R, hx₁⟩ := obsY1_label_inBox hN2 hk νS β p₁ δ hN hT Lab₀ hdj i₁ hi₁
    obtain ⟨-, x₂, hx₂R, hx₂⟩ := obsY1_label_inBox hN2 hk νS β p₁ δ hN hT Lab₀ hdj i₂ hi₂
    rw [Prod.mk.injEq] at h
    refine Prod.ext ?_ h.2
    have h1 : ιu (unitPt (SA).hG' x₁) = ιu (unitPt (SA).hG' x₂) := by rw [hx₁, hx₂]; exact h.1
    rw [← hx₁, ← hx₂]
    exact unitPt_eq_of_unitImage_eq hn2 hn2' (SA).hG' (SB).hG' hx₁R hx₂R h1
  · obtain ⟨x₀, -, hu, hi⟩ := obsY1_unitImage_surj hN2 hk νS β p₁ δ hN hN' hn2 hnL hnL' hT Lab₀
      Lab₀' hdj hdj' i' hi'
    exact ⟨(unitPt (SA).hG' x₀, i'.2), hi, Prod.ext hu rfl⟩

/-- **The first-order marks and the kernel at corresponding marks.**  For a mark `i` whose
first-order label has blocks in `T` (cubes of the box): the clamped first-order marks of
`(ιu i.1, i.2)` and `i` agree at block variables agreeing at corresponding unit points of the box,
and, if the terms `Ev'`, `Ev` take equal values at corresponding parameters (`hEvT`), the kernels
of the domains of the local covers of `bm y` and `y` along the unit vectors of these marks agree
at `cubeMap '' T₁` and `T₁`, for every `T₁ ⊆ T`. -/
theorem obsMarkValues_twoTorus (hN2 : 2 ≤ N) (hk : 1 ≤ k) (νS β p₁ δ : ℝ) {m₀ R : ℕ}
    (hN : L ^ m₀ ∣ N₁) (hN' : L ^ m₀ ∣ N₁')
    (hn2 : 2 * R + 3 * L ^ (k + 1) + 5 < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hn2' : 2 * R + 3 * L ^ (k + 1) + 5 < (N₁' * L ^ m₁) * L ^ (k + 1))
    (hnF : 2 * R + 5 * (L * aK) < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hnF' : 2 * R + 5 * (L * aK) < (N₁' * L ^ m₁) * L ^ (k + 1))
    (y : CTorus d L N₁ m₁ (k + 1))
    (hX₁R : ∀ x ∈ LocalCover.nbhd m₀ y, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x)
    (hdj : ∀ Y ∈ 𝒴A, IsDj m₀ (k + 1) Y) (hdj' : ∀ Y ∈ 𝒴B, IsDj m₀ (k + 1) Y)
    {T : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) m₀ (k + 1)
      Set.univ)}
    (hT : ∀ b ∈ T, ∀ x ∈ box b.1 aK, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x)
    {Lb₀ : Type}
    (Lab₀ : CubeLabels (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) m₀ (k + 1)
      Set.univ Lb₀)
    (hp : 0 < (SA).p₁) (hp' : 0 < (SB).p₁)
    {Ev : Set (CTorus d L N₁ m₁ (k + 1)) →
      RawData d L (N₁ * L ^ m₁) (k + 1) N × ((SA).U × Fin N → ℂ) → ℂ}
    {Ev' : Set (CTorus d L N₁' m₁ (k + 1)) →
      RawData d L (N₁' * L ^ m₁) (k + 1) N × ((SB).U × Fin N → ℂ) → ℂ}
    {r : RawData d L (N₁ * L ^ m₁) (k + 1) N} {r' : RawData d L (N₁' * L ^ m₁) (k + 1) N}
    {cψ : ℝ} (hcψ : 0 < cψ)
    (hEvT : ∀ Y : Set (CTorus d L N₁ m₁ (k + 1)),
      (∀ x ∈ Y, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x) →
      ∀ (ψh : (SA).U × Fin N → ℂ) (ψh' : (SB).U × Fin N → ℂ), (∀ q, ‖ψh q‖ ≤ cψ) →
        (∀ q, ‖ψh' q‖ ≤ cψ) →
        (∀ x, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x →
          ∀ i, ψh' (unitPt (SB).hG' (bm x), i) = ψh (unitPt (SA).hG' x, i)) →
        Ev' (bm '' Y) (r', ψh') = Ev Y (r, ψh)) :
    (∀ (i : ObsMarkIdx (SA))
      (_ : blocksOf m₀ (k + 1) Set.univ ((obsLab Lab₀ hdj).ysite (obsY1 m₀ (SA) Lb₀ (𝒴A) i)) ⊆ T),
      ∀ Φ Φ', (∀ x, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x →
        Φ' ((SB).cellOf m₀ (unitPt (SB).hG' (bm x))) ⟨unitPt (SB).hG' (bm x), rfl⟩ =
          Φ ((SA).cellOf m₀ (unitPt (SA).hG' x)) ⟨unitPt (SA).hG' x, rfl⟩) →
      blockMarkC (SB) m₀ hp' (ιu i.1) i.2 Φ' = blockMarkC (SA) m₀ hp i.1 i.2 Φ) ∧
    (∀ (i : ObsMarkIdx (SA))
      (_ : blocksOf m₀ (k + 1) Set.univ ((obsLab Lab₀ hdj).ysite (obsY1 m₀ (SA) Lb₀ (𝒴A) i)) ⊆ T),
      ∀ T₁ ⊆ T, obsHker (𝒴B) (fun Y => hatCoeff (Ev' Y) r' (obsUnitVec (SB) ((ιu i.1), i.2)))
          m₀ (T₁.image (σc)) =
        obsHker (𝒴A) (fun Y => hatCoeff (Ev Y) r (obsUnitVec (SA) i)) m₀ T₁) := by
  refine ⟨fun i hi Φ Φ' hΦ => ?_, fun i hi T₁ hT₁ => ?_⟩
  · obtain ⟨-, x₀, hx₀R, hx₀⟩ := obsY1_label_inBox hN2 hk νS β p₁ δ hN hT Lab₀ hdj i hi
    obtain ⟨u, a⟩ := i
    simp only at hx₀
    subst hx₀
    exact blockMarkC_twoTorus hN2 hk νS β p₁ δ hn2 hp hp' hΦ hx₀R a
  · obtain ⟨-, x₀, hx₀R, hx₀⟩ := obsY1_label_inBox hN2 hk νS β p₁ δ hN hT Lab₀ hdj i hi
    obtain ⟨u, a⟩ := i
    simp only at hx₀
    subst hx₀
    exact obsHker_twoTorus (ϱ := ϱ) hN hN' hnF hnF' y hX₁R hdj hdj' _ _
      (fun Y _ hYR => hatCoeff_obsUnitVec_twoTorus hN2 hk νS β p₁ δ hn2 hn2' hcψ
        (hEvT Y hYR) hx₀R a) T₁ (fun b hb => hT b (hT₁ hb))

/-- **The correspondence of the remainder marks.**  For a set `T` of cubes of the box, the domains
of the local cover of `y` with blocks in `T` correspond to the domains of the local cover of `bm y`
with blocks in `cubeMap '' T` (`Y ↦ bm '' Y`): the map on the non-dummy remainder indices carries
the blocks of the labels along `cubeMap`, is injective and surjective, and the remainder marks
agree at block variables agreeing at corresponding unit points of the box, if the terms `Ev'`,
`Ev` take equal values at corresponding parameters (`hEvT`).  The labels are any label systems
with `ysite (lab Y) = Y`. -/
theorem obsRemIdx_twoTorus (hN2 : 2 ≤ N) (hk : 1 ≤ k) (νS β p₁ δ : ℝ) {m₀ R : ℕ}
    (hN : L ^ m₀ ∣ N₁) (hN' : L ^ m₀ ∣ N₁')
    (hnF : 2 * R + 5 * (L * aK) < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hnF' : 2 * R + 5 * (L * aK) < (N₁' * L ^ m₁) * L ^ (k + 1))
    {𝒴 : Finset (Set (CTorus d L N₁ m₁ (k + 1)))} {𝒴' : Finset (Set (CTorus d L N₁' m₁ (k + 1)))}
    (hdj : ∀ Y ∈ 𝒴, IsDj m₀ (k + 1) Y) (hdj' : ∀ Y ∈ 𝒴', IsDj m₀ (k + 1) Y)
    (hmem : ∀ Y : Set (CTorus d L N₁ m₁ (k + 1)),
      (∀ x ∈ Y, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x) → (bm '' Y ∈ 𝒴' ↔ Y ∈ 𝒴))
    {T : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) m₀ (k + 1)
      Set.univ)}
    (hT : ∀ b ∈ T, ∀ x ∈ box b.1 aK, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x)
    {Lb Lb' : Type*}
    (Lab : CubeLabels (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) m₀ (k + 1)
      Set.univ Lb)
    (Lab' : CubeLabels (d := d) (L := L) (N₁ := N₁') (m₁ := m₁) (K := k + 1) m₀ (k + 1)
      Set.univ Lb')
    (lab : {Y // Y ∈ 𝒴} → Lb) (lab' : {Y // Y ∈ 𝒴'} → Lb') (y₀ : Lb) (y₀' : Lb')
    (hlab : ∀ Y, Lab.ysite (lab Y) = Y.1) (hlab' : ∀ Y, Lab'.ysite (lab' Y) = Y.1)
    (hp : 0 < (SA).p₁) (hp' : 0 < (SB).p₁)
    {Ev : Set (CTorus d L N₁ m₁ (k + 1)) →
      RawData d L (N₁ * L ^ m₁) (k + 1) N × ((SA).U × Fin N → ℂ) → ℂ}
    {Ev' : Set (CTorus d L N₁' m₁ (k + 1)) →
      RawData d L (N₁' * L ^ m₁) (k + 1) N × ((SB).U × Fin N → ℂ) → ℂ}
    {A : Set (RawData d L (N₁ * L ^ m₁) (k + 1) N)}
    {A' : Set (RawData d L (N₁' * L ^ m₁) (k + 1) N)}
    (θ : physParam N (SA)) (θ' : physParam N (SB))
    (hθ : (θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) ∈ A)
    (hθ' : (θ'.1 : RawData d L (N₁' * L ^ m₁) (k + 1) N) ∈ A')
    {cψ : ℝ} (hcψ : 0 < cψ) (hq : p₁ / cψ ≤ 1 / 4)
    (hEvT : ∀ Y : Set (CTorus d L N₁ m₁ (k + 1)),
      (∀ x ∈ Y, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x) →
      ∀ (ψh : (SA).U × Fin N → ℂ) (ψh' : (SB).U × Fin N → ℂ), (∀ q, ‖ψh q‖ ≤ cψ) →
        (∀ q, ‖ψh' q‖ ≤ cψ) →
        (∀ x, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x →
          ∀ i, ψh' (unitPt (SB).hG' (bm x), i) = ψh (unitPt (SA).hG' x, i)) →
        Ev' (bm '' Y) ((θ'.1 : RawData d L (N₁' * L ^ m₁) (k + 1) N), ψh') =
          Ev Y ((θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N), ψh)) :
    ∃ κr : ∀ i : RemIdx (𝒴), i ≠ none →
        blocksOf m₀ (k + 1) Set.univ (Lab.ysite (obsRemLab (𝒴) lab y₀ i)) ⊆ T → RemIdx (𝒴'),
      (∀ i hQ hi, κr i hQ hi ≠ none) ∧
      (∀ i hQ hi, blocksOf m₀ (k + 1) Set.univ (Lab'.ysite (obsRemLab (𝒴') lab' y₀' (κr i hQ hi))) =
        (blocksOf m₀ (k + 1) Set.univ (Lab.ysite (obsRemLab (𝒴) lab y₀ i))).image (σc)) ∧
      (∀ i₁ hQ₁ hi₁ i₂ hQ₂ hi₂, κr i₁ hQ₁ hi₁ = κr i₂ hQ₂ hi₂ → i₁ = i₂) ∧
      (∀ i' : RemIdx (𝒴'), i' ≠ none →
        blocksOf m₀ (k + 1) Set.univ (Lab'.ysite (obsRemLab (𝒴') lab' y₀' i')) ⊆ T.image (σc) →
        ∃ i hQ hi, κr i hQ hi = i') ∧
      (∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ i hQ hi, ∀ Φ Φ',
        (∀ x, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x →
          Φ' ((SB).cellOf m₀ (unitPt (SB).hG' (bm x))) ⟨unitPt (SB).hG' (bm x), rfl⟩ =
            Φ ((SA).cellOf m₀ (unitPt (SA).hG' x)) ⟨unitPt (SA).hG' x, rfl⟩) →
        obsGrFam (SB) m₀ hp' Ev' (𝒴') A' θ' (κr i hQ hi) (s : ℂ) Φ' =
          obsGrFam (SA) m₀ hp Ev (𝒴) A θ i (s : ℂ) Φ) := by
  classical
  have ha := cellSide_pos (L := L) m₀ m₁ (k + 1)
  have hcs : aK ≤ L * aK := cellSide_le_mul
  have hnL : 2 * R + L * aK < (N₁ * L ^ m₁) * L ^ (k + 1) := by omega
  have hnL' : 2 * R + L * aK < (N₁' * L ^ m₁) * L ^ (k + 1) := by omega
  have hnc : 2 * R + aK < (N₁ * L ^ m₁) * L ^ (k + 1) := by omega
  have hnc' : 2 * R + aK < (N₁' * L ^ m₁) * L ^ (k + 1) := by omega
  have hm' : 2 * R + 1 < (N₁' * L ^ m₁) * L ^ (k + 1) := by omega
  -- the blocks of the label of a domain
  have hlabT : ∀ Y : {Y // Y ∈ 𝒴},
      blocksOf m₀ (k + 1) Set.univ (Lab.ysite (obsRemLab (𝒴) lab y₀ (some Y))) ⊆ T →
        blocksOf m₀ (k + 1) Set.univ Y.1 ⊆ T := fun Y h => by
    rw [show obsRemLab (𝒴) lab y₀ (some Y) = lab Y from rfl, hlab] at h
    exact h
  have hYR : ∀ Y : {Y // Y ∈ 𝒴},
      blocksOf m₀ (k + 1) Set.univ (Lab.ysite (obsRemLab (𝒴) lab y₀ (some Y))) ⊆ T →
        ∀ x ∈ Y.1, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x :=
    fun Y h => inBox_of_blocksOf_subset hN hT (hdj Y.1 Y.2) (hlabT Y h)
  have hmemB : ∀ Y : {Y // Y ∈ 𝒴},
      blocksOf m₀ (k + 1) Set.univ (Lab.ysite (obsRemLab (𝒴) lab y₀ (some Y))) ⊆ T →
        bm '' Y.1 ∈ 𝒴' :=
    fun Y h => (hmem Y.1 (hYR Y h)).2 Y.2
  refine ⟨fun i => Option.rec (fun hQ _ => absurd rfl hQ)
    (fun Y _ hY => some ⟨bm '' Y.1, hmemB Y hY⟩) i, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hQ hi
    rcases i with _ | Y
    · exact absurd rfl hQ
    · exact Option.some_ne_none _
  · intro i hQ hi
    rcases i with _ | Y
    · exact absurd rfl hQ
    · have e1 : Lab'.ysite (obsRemLab (𝒴') lab' y₀' (some ⟨bm '' Y.1, hmemB Y hi⟩)) =
          bm '' Y.1 := hlab' _
      have e2 : Lab.ysite (obsRemLab (𝒴) lab y₀ (some Y)) = Y.1 := hlab Y
      change blocksOf m₀ (k + 1) Set.univ
          (Lab'.ysite (obsRemLab (𝒴') lab' y₀' (some ⟨bm '' Y.1, hmemB Y hi⟩))) = _
      rw [e1, e2]
      exact blocksOf_image_boxMap hN hN' hnc hnc' (hYR Y hi)
  · intro i₁ hQ₁ hi₁ i₂ hQ₂ hi₂ h
    rcases i₁ with _ | Y₁
    · exact absurd rfl hQ₁
    rcases i₂ with _ | Y₂
    · exact absurd rfl hQ₂
    injection h with h'
    injection h' with h1
    exact congrArg some (Subtype.ext (image_boxMap_inj (N₁' := N₁') hm' (hYR Y₁ hi₁)
      (hYR Y₂ hi₂) h1))
  · intro i' hQ' hi'
    rcases i' with _ | Y'
    · exact absurd rfl hQ'
    have e1 : Lab'.ysite (obsRemLab (𝒴') lab' y₀' (some Y')) = Y'.1 := hlab' Y'
    rw [e1] at hi'
    obtain ⟨-, hZR, hZimg, hZT⟩ := preimage_of_blocksOf_subset_image hN hN' hnL hnL' hT
      (hdj' Y'.1 Y'.2) hi'
    have hZmem : bm' '' Y'.1 ∈ 𝒴 := (hmem _ hZR).1 (by rw [hZimg]; exact Y'.2)
    have hZT' : blocksOf m₀ (k + 1) Set.univ
        (Lab.ysite (obsRemLab (𝒴) lab y₀ (some ⟨_, hZmem⟩))) ⊆ T := by
      rw [show obsRemLab (𝒴) lab y₀ (some ⟨_, hZmem⟩) = lab ⟨_, hZmem⟩ from rfl, hlab]
      exact hZT
    exact ⟨some ⟨_, hZmem⟩, Option.some_ne_none _, hZT', congrArg some (Subtype.ext hZimg)⟩
  · intro s _ i hQ hi Φ Φ' hΦ
    rcases i with _ | Y
    · exact absurd rfl hQ
    have e1 := obsGrFam_of_mem (S := SB) (m₀ := m₀) (hp := hp') (Ev := Ev') (𝒴 := 𝒴') hθ'
    have e2 := obsGrFam_of_mem (S := SA) (m₀ := m₀) (hp := hp) (Ev := Ev) (𝒴 := 𝒴) hθ
    rw [e1, e2]
    refine obsGrRawC_twoTorus hN2 hk νS β p₁ δ hp hp' Y _ hcψ hq ?_ hΦ s
    exact hEvT Y.1 (hYR Y hi)

/-- **D3: the coefficient of the observable on two tori, given the correspondence of the
activities.**  For the steps `SA = hatStepKG … N₁ …`, `SB = hatStepKG … N₁′ …` (`FlCore` on both
tori), the local covers of a site `y` (its neighbourhood in the box of radius `R`) and of `bm y`,
the terms `Ev`, `Ev'` of the site functionals `δφ(y, iy)`, `δφ(bm y, iy)` in the explicit form
`evTerm … (siteFun …)` for decoupled pairs `(F₁, Sol)`, `(F₁', Sol')` (with the locality of `Ev`),
parameters `θ`, `θ'` whose raw data lie in the charts and agree on the box, and a set `T` of cubes
of the box: if the activities `Aact`, `Aact'` on the observable labels satisfy the hypotheses of
`obsCoeffParam_blockSplit_twoTorus` (inactive labels, the correspondence `ψ` of the active labels
with image blocks, equal activities at block variables agreeing at corresponding unit points of the
box), the coefficients of the observable agree:
`obsCoeffParam … θ' (cubeMap '' T) = obsCoeffParam … θ T`.  The first-order labels and marks, the
kernel and the remainder marks are carried along `cubeMap` in the proof.  Margins: those of
`Ev_localCover_twoTorus`. -/
theorem obsCoeffParam_twoTorus_of_activities (hN2 : 2 ≤ N) (hk : 1 ≤ k) (νS β p₁ δ : ℝ)
    {c BG κ eps Kc Cx c₂ BG₂ δ₁ : ℝ}
    (hC : FlCore N (GA) (HA) 1 νS c BG κ eps Kc Cx c₂ BG₂ δ₁)
    (hC' : FlCore N (GB) (HB) 1 νS c BG κ eps Kc Cx c₂ BG₂ δ₁)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δc : ℝ}
    (hmar : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hαK : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    {m₀ R : ℕ} (hN : L ^ m₀ ∣ N₁) (hN' : L ^ m₀ ∣ N₁')
    (hn : 4 * R + 12 * L ^ (k + 1 + m₁) + 7 * L ^ (k + 1) + 5 < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hn' : 4 * R + 12 * L ^ (k + 1 + m₁) + 7 * L ^ (k + 1) + 5 < (N₁' * L ^ m₁) * L ^ (k + 1))
    (hnS : 2 * (ρ₁) + 5 * (L * cellSide L 0 m₁ (k + 1)) < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hnS' : 2 * (ρ₁) + 5 * (L * cellSide L 0 m₁ (k + 1)) < (N₁' * L ^ m₁) * L ^ (k + 1))
    (hnF : 2 * R + 5 * (L * aK) < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hnF' : 2 * R + 5 * (L * aK) < (N₁' * L ^ m₁) * L ^ (k + 1))
    -- the site and the terms of its expansion
    (y : CTorus d L N₁ m₁ (k + 1)) (iy : Fin N)
    (hX₁R : ∀ x ∈ LocalCover.nbhd m₀ y, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x)
    (cc : ℂ) {cψ : ℝ} (hcψ : 0 < cψ) (hq : p₁ / cψ ≤ 1 / 4)
    (hrad : markedRad d L N k 1 κ cψ cc < δ₁)
    {F₁ : DecParams (GA) × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      ((GA).Ω 1 × Fin N → ℂ) × ((GA).Ω 1 → ℂ)}
    {F₁' : DecParams (GB) × RawData d L (N₁' * L ^ m₁) (k + 1) N →
      ((GB).Ω 1 × Fin N → ℂ) × ((GB).Ω 1 → ℂ)}
    (hF₁ : ∀ (s : DecParams (GA)) (D : BgData (GA) N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC (GA) (bgC0 d L N) (c7 d L N BG κ) νS D → ∀ (φ : (GA).Ω 1 × Fin N → ℂ)
        (α : (GA).Ω 1 → ℂ), IsDecBg (GA) (compWeight L 1) νS (rho4 d L N BG κ) s D φ α →
        F₁ (s, rawOf D) = (φ, α))
    (hF₁' : ∀ (s : DecParams (GB)) (D : BgData (GB) N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC (GB) (bgC0 d L N) (c7 d L N BG κ) νS D → ∀ (φ : (GB).Ω 1 × Fin N → ℂ)
        (α : (GB).Ω 1 → ℂ), IsDecBg (GB) (compWeight L 1) νS (rho4 d L N BG κ) s D φ α →
        F₁' (s, rawOf D) = (φ, α))
    {Sol : Dec2.DecParams (coverOf (GA)) × Edat (HA) N → ((HA).Ω 1 × Fin N → ℂ) × ((HA).Ω 1 → ℂ)}
    {Sol' : Dec2.DecParams (coverOf (GB)) × Edat (HB) N →
      ((HB).Ω 1 × Fin N → ℂ) × ((HB).Ω 1 → ℂ)}
    (hSol : ∀ p : Dec2.DecParams (coverOf (GA)) × Edat (HA) N, (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM (HA) N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2 →
        (Sol p).1 = dphi (HA) (Dec2.decG (coverOf (GA)) (HA) (compWeight L 1) νS p.1) p.2.2.1
          p.2.1 (pertSource (HA) (compWeight L 1) p.2.2.2.1 p.2.2.2.2) (Sol p).2 ∧
        Dec2.DecFixed (coverOf (GA)) (HA) (compWeight L 1) νS p.1 false p.2.2.1 p.2.1
          (pertSource (HA) (compWeight L 1) p.2.2.2.1 p.2.2.2.2) (Sol p).2 ∧
        Small (HA) (Sol p).2 (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
        Small (HA) (Sol p).2 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        SupBounds (HA) (Sol p).1 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        (∀ δα' : (HA).Ω 1 → ℂ, Small (HA) δα' (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf (GA)) (HA) (compWeight L 1) νS p.1 false p.2.2.1 p.2.1
            (pertSource (HA) (compWeight L 1) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol p).2))
    (hSol' : ∀ p : Dec2.DecParams (coverOf (GB)) × Edat (HB) N, (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM (HB) N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2 →
        (Sol' p).1 = dphi (HB) (Dec2.decG (coverOf (GB)) (HB) (compWeight L 1) νS p.1) p.2.2.1
          p.2.1 (pertSource (HB) (compWeight L 1) p.2.2.2.1 p.2.2.2.2) (Sol' p).2 ∧
        Dec2.DecFixed (coverOf (GB)) (HB) (compWeight L 1) νS p.1 false p.2.2.1 p.2.1
          (pertSource (HB) (compWeight L 1) p.2.2.2.1 p.2.2.2.2) (Sol' p).2 ∧
        Small (HB) (Sol' p).2 (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
        Small (HB) (Sol' p).2 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        SupBounds (HB) (Sol' p).1 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        (∀ δα' : (HB).Ω 1 → ℂ, Small (HB) δα' (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf (GB)) (HB) (compWeight L 1) νS p.1 false p.2.2.1 p.2.1
            (pertSource (HB) (compWeight L 1) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol' p).2))
    {Ev : Set (CTorus d L N₁ m₁ (k + 1)) →
      RawData d L (N₁ * L ^ m₁) (k + 1) N × ((SA).U × Fin N → ℂ) → ℂ}
    {Ev' : Set (CTorus d L N₁' m₁ (k + 1)) →
      RawData d L (N₁' * L ^ m₁) (k + 1) N × ((SB).U × Fin N → ℂ) → ℂ}
    (hEv : Ev = evTerm (fun i : ParIdx (GA) (XA) => i.1.1) (GA) m₀
        (X1 (GA) m₀ k (LocalCover.fam m₀ y))
        (fun u s => siteFun (GA) (HA) y iy (F₁ (extParams (GA) (XA) s, u.1))
          (Sol (extParams (GA) (XA) s,
            flEdat (GA) (HA) (F₁ (extParams (GA) (XA) s, u.1))
              u.1.1 (hatPsiF (GA) 1 νS (SA).hG' cc F₁
                (extParams (GA) (XA) s) u.1 u.2))).1
          (u.1, hatPsiF (GA) 1 νS (SA).hG' cc F₁
            (extParams (GA) (XA) s) u.1 u.2)))
    (hEv' : Ev' = evTerm (fun i : ParIdx (GB) (XB) => i.1.1) (GB)
        m₀ (X1 (GB) m₀ k (LocalCover.fam m₀ (bm y)))
        (fun u s => siteFun (GB) (HB) (bm y) iy
          (F₁' (extParams (GB) (XB) s, u.1))
          (Sol' (extParams (GB) (XB) s,
            flEdat (GB) (HB) (F₁' (extParams (GB)
              (XB) s, u.1)) u.1.1
              (hatPsiF (GB) 1 νS (SB).hG' cc F₁'
                (extParams (GB) (XB) s) u.1 u.2))).1
          (u.1, hatPsiF (GB) 1 νS (SB).hG' cc F₁'
            (extParams (GB) (XB) s) u.1 u.2)))
    (hdEv : ∀ Y ∈ 𝒴A, ∀ u ∈ XiCRaw (GA) (compWeight L 1) νS (k + 1) 1 eps ×ˢ
        {ψh : (SA).U × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ},
      ∀ u' ∈ XiCRaw (GA) (compWeight L 1) νS (k + 1) 1 eps ×ˢ
        {ψh : (SA).U × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ},
      AgHatDir (SA).hG' Y u u' → Ev Y u = Ev Y u')
    (hdj : ∀ Y ∈ 𝒴A, IsDj m₀ (k + 1) Y) (hdj' : ∀ Y ∈ 𝒴B, IsDj m₀ (k + 1) Y)
    -- the parameters
    (θ : physParam N (SA)) (θ' : physParam N (SB))
    (hθ : (θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) ∈
      XiCRaw (GA) (compWeight L 1) νS (k + 1) 1 eps)
    (hθ' : (θ'.1 : RawData d L (N₁' * L ^ m₁) (k + 1) N) ∈
      XiCRaw (GB) (compWeight L 1) νS (k + 1) 1 eps)
    (hraw : RawBoxAgree {z | InBox d (R + 3 * L ^ (k + 1)) ((N₁ * L ^ m₁) * L ^ (k + 1)) z}
      (θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) (θ'.1 : RawData d L (N₁' * L ^ m₁) (k + 1) N))
    (hp : 0 < (SA).p₁) (hp' : 0 < (SB).p₁)
    (T : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) m₀ (k + 1)
      Set.univ))
    (hT : ∀ b ∈ T, ∀ x ∈ box b.1 aK, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x)
    -- the activities
    {Lb₀ Lb₀' : Type} [Fintype Lb₀] [Fintype Lb₀']
    (Lab₀ : CubeLabels (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) m₀ (k + 1)
      Set.univ Lb₀)
    (Lab₀' : CubeLabels (d := d) (L := L) (N₁ := N₁') (m₁ := m₁) (K := k + 1) m₀ (k + 1)
      Set.univ Lb₀')
    {εH κH κ0 Kco εH' κH' κ0' Kco' : ℝ}
    (Aact : physParam N (SA) → ℂ → ℂ →
      LabelAct (obsLab Lab₀ hdj) ((SA).blockSplit m₀ hp).Ωb εH κH κ0 Kco)
    (Aact' : physParam N (SB) → ℂ → ℂ →
      LabelAct (obsLab Lab₀' hdj') ((SB).blockSplit m₀ hp').Ωb εH' κH' κ0' Kco')
    (P : ObsLb Lb₀ m₀ (𝒴A) → Prop) (P' : ObsLb Lb₀' m₀ (𝒴B) → Prop)
    (hA0 : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ l, ¬ P l → ∀ Φ, (Aact θ (s : ℂ) 1).H l Φ = 0)
    (hA0' : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ l', ¬ P' l' → ∀ Φ',
      (Aact' θ' (s : ℂ) 1).H l' Φ' = 0)
    (ψ : ∀ l, P l → blocksOf m₀ (k + 1) Set.univ ((obsLab Lab₀ hdj).ysite l) ⊆ T →
      ObsLb Lb₀' m₀ (𝒴B))
    (hψP : ∀ l hP hl, P' (ψ l hP hl))
    (hψb : ∀ l hP hl, blocksOf m₀ (k + 1) Set.univ ((obsLab Lab₀' hdj').ysite (ψ l hP hl)) =
      (blocksOf m₀ (k + 1) Set.univ ((obsLab Lab₀ hdj).ysite l)).image (σc))
    (hψinj : ∀ l₁ hP₁ hl₁ l₂ hP₂ hl₂, ψ l₁ hP₁ hl₁ = ψ l₂ hP₂ hl₂ → l₁ = l₂)
    (hψsurj : ∀ l', P' l' → blocksOf m₀ (k + 1) Set.univ ((obsLab Lab₀' hdj').ysite l') ⊆
      T.image (σc) → ∃ l hP hl, ψ l hP hl = l')
    (hA : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ l hP hl, ∀ Φ Φ',
      (∀ x, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x →
        Φ' ((SB).cellOf m₀ (unitPt (SB).hG' (bm x))) ⟨unitPt (SB).hG' (bm x), rfl⟩ =
          Φ ((SA).cellOf m₀ (unitPt (SA).hG' x)) ⟨unitPt (SA).hG' x, rfl⟩) →
      (Aact' θ' (s : ℂ) 1).H (ψ l hP hl) Φ' = (Aact θ (s : ℂ) 1).H l Φ) :
    obsCoeffParam ((SB).blockSplit m₀ hp').μ Aact' (fun m => obsY1 m₀ (SB) Lb₀' (𝒴B) m)
        (fun m => blockMarkC (SB) m₀ hp' m.1 m.2)
        (fun θ m T'' => obsHker (𝒴B) (fun Y => hatCoeff (Ev' Y)
          (θ.1 : RawData d L (N₁' * L ^ m₁) (k + 1) N) (obsUnitVec (SB) m)) m₀ T'')
        (obsRemLab (𝒴B) (fun Y => Sum.inl (Sum.inr Y))
          (obsY0 m₀ Lb₀' (𝒴B) (rootCube (m₀ := m₀) (blockIndex (bm y)))))
        (fun θ => obsGrFam (SB) m₀ hp' Ev' (𝒴B)
          (XiCRaw (GB) (compWeight L 1) νS (k + 1) 1 eps) θ) θ' (T.image (σc)) =
      obsCoeffParam ((SA).blockSplit m₀ hp).μ Aact (fun m => obsY1 m₀ (SA) Lb₀ (𝒴A) m)
        (fun m => blockMarkC (SA) m₀ hp m.1 m.2)
        (fun θ m T'' => obsHker (𝒴A) (fun Y => hatCoeff (Ev Y)
          (θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) (obsUnitVec (SA) m)) m₀ T'')
        (obsRemLab (𝒴A) (fun Y => Sum.inl (Sum.inr Y))
          (obsY0 m₀ Lb₀ (𝒴A) (rootCube (m₀ := m₀) (blockIndex y))))
        (fun θ => obsGrFam (SA) m₀ hp Ev (𝒴A)
          (XiCRaw (GA) (compWeight L 1) νS (k + 1) 1 eps) θ) θ T := by
  classical
  -- margins
  have hcs : aK ≤ L * aK := cellSide_le_mul
  have hn2 : 2 * R + 3 * L ^ (k + 1) + 5 < (N₁ * L ^ m₁) * L ^ (k + 1) := by omega
  have hn2' : 2 * R + 3 * L ^ (k + 1) + 5 < (N₁' * L ^ m₁) * L ^ (k + 1) := by omega
  have hnL : 2 * R + L * aK < (N₁ * L ^ m₁) * L ^ (k + 1) := by omega
  have hnL' : 2 * R + L * aK < (N₁' * L ^ m₁) * L ^ (k + 1) := by omega
  -- the terms of the site functional at the two parameters
  have hEvT := siteEvParam_twoTorus hN2 hk νS β p₁ δ hC hC' hMX hmar hαK hsm hN hN' hn hn' hnS hnS'
    hnF hnF' y iy hX₁R cc hcψ hrad hF₁ hF₁' hSol hSol' hEv hEv' θ θ' hθ hθ' hraw
  -- the first-order marks and the kernel
  obtain ⟨hκ1b, hκ1inj, hκ1surj⟩ := obsMarkLabels_twoTorus hN2 hk νS β p₁ δ hN hN' hn2 hn2' hnL
    hnL' hT Lab₀ Lab₀' hdj hdj'
  obtain ⟨hG1, hkerT⟩ := obsMarkValues_twoTorus hN2 hk νS β p₁ δ hN hN' hn2 hn2' hnF hnF' y hX₁R
    hdj hdj' hT Lab₀ hp hp' hcψ hEvT
  -- the remainder marks
  obtain ⟨κr, hκrQ, hκrb, hκrinj, hκrsurj, hGr⟩ := obsRemIdx_twoTorus hN2 hk νS β p₁ δ hN hN' hnF
    hnF' hdj hdj' (fun Y hY => mem_polyDom_site_boxMap_iff (ϱ := ϱ) hN hN' hnF hnF' y hX₁R hY)
    hT (obsLab Lab₀ hdj) (obsLab Lab₀' hdj') (fun Y => Sum.inl (Sum.inr Y))
    (fun Y => Sum.inl (Sum.inr Y)) (obsY0 m₀ Lb₀ (𝒴A) (rootCube (m₀ := m₀) (blockIndex y)))
    (obsY0 m₀ Lb₀' (𝒴B) (rootCube (m₀ := m₀) (blockIndex (bm y)))) (fun _ => rfl) (fun _ => rfl)
    hp hp' θ θ' hθ hθ' hcψ hq hEvT
  refine obsCoeffParam_blockSplit_twoTorus hN2 hk νS β p₁ δ hN hN' hn2 hn2' (SA).hG' (SB).hG' hp hp'
    Aact Aact' _ _ _ _ _ _ _ _ _ _ θ θ' T hT P P' hA0 hA0' ψ hψP hψb hψinj hψsurj hA
    (fun i => depOn_blockMarkC i.1 i.2 (obsCubeLab_mem m₀ ((SA).cellOf m₀ i.1)))
    (fun i _ => (ιu i.1, i.2)) hκ1b hκ1inj hκ1surj hG1 hkerT (fun i => i ≠ none) (fun i => i ≠ none)
    ?_ ?_ (fun i u => depOn_obsGrFam_all hN hcψ hq hdj hdEv (obsLab Lab₀ hdj)
      (fun Y => Sum.inl (Sum.inr Y)) _ (fun _ => rfl) θ i u) κr hκrQ hκrb hκrinj hκrsurj hGr
  · -- the dummy remainder index
    intro i hi s _
    have hi' : i = none := not_not.1 hi
    subst hi'
    funext Φ
    rw [obsGrFam_of_mem hθ]
    rfl
  · intro i hi s _
    have hi' : i = none := not_not.1 hi
    subst hi'
    funext Φ
    rw [obsGrFam_of_mem hθ']
    rfl

end Assembly

end Balaban.Polymer.TwoTorusStep
