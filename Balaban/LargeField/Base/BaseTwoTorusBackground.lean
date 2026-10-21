/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Base.BaseBackgroundLocal
public import Balaban.Polymer.TwoTorusDecBg
public import Balaban.Inhabited.LevelLemmasGeneral
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The first step's decoupled background on two tori

The first step's background is the decoupled background of the whole-lattice generating set of
level one, `lvTopG d L N₁ m₁ 0 ϱ = levelGS 1` on the first-step torus `CTorus d L N₁ m₁ 1`, with
its self cover (`BaseBackgroundLocal`, `baseBackground_analytic_whole`).  The two-torus comparison
`decBg_value_twoTorus_of_box` of `Balaban.Polymer.TwoTorusDecBg` is stated for `levelGS j` on a
torus of level `K` with `1 ≤ j ≤ K`, and none of its hypotheses reads `1 < K` or `j < K`; at
`j = K = 1` it applies as it stands.  `baseBackground_twoTorus` is that statement at `j = K = 1`,
with the defining property of the maps `F₁` read in the cover form `Dec2.IsDecBg (coverOf G) G`
(the form of `baseBackground_analytic_whole`) and `HatConn` supplied by `hatConn_lvTopG`.  Its
conclusions: the multipliers correspond on the block set `S_Y`, the corrections `φ - φ₀` on the
component `Y`, and the fields where the raw data agree on `approxDep`, in particular at the rows of
`H_D(0)` at `S_Y`.
-/

@[expose] public section

noncomputable section

open scoped Classical

namespace Balaban.LargeField.Base

open Balaban Balaban.Localization Balaban.Fluctuation Balaban.SmallField.Def6 Balaban.Polymer
  Balaban.Multiscale Balaban.Background Balaban.Polymer.TwoTorusStep

section Level1

variable {d L N₁ N₁' m₁ N : ℕ} [NeZero N₁] [NeZero N₁'] [NeZero L] {ϱ : ℝ}

set_option hygiene false in
local notation "bm" => boxMap ((N₁ * L ^ m₁) * L ^ 1) ((N₁' * L ^ m₁) * L ^ 1)
set_option hygiene false in
local notation "GA" => levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := 1) (ϱ := ϱ) 1 le_rfl
set_option hygiene false in
local notation "GB" => levelGS (d := d) (L := L) (N₁ := N₁') (m₁ := m₁) (k := 1) (ϱ := ϱ) 1 le_rfl
set_option hygiene false in
local notation "ιb" x:max => Subtype.mk (bm (x : Balaban.Localization.CTorus d L N₁ m₁ 1))
  (levelGS_mem_Ω_one (d := d) (L := L) (N₁ := N₁') (m₁ := m₁) (K := 1) (ϱ := ϱ)
    (le_refl 1) le_rfl _)

/-- **The first step's decoupled background on two tori** (`decBg_value_twoTorus_of_box` at
`j = K = 1`).  Let `F₁`, `F₁'` be maps with the defining property of the decoupled background of
the covers of `levelGS 1` of the two first-step tori (as in `baseBackground_analytic_whole`), `Y` a
component of the cut with block set `S_Y` (for the images `bm '' X₁`, `bm '' 𝒞`, `bm '' Y` on the
second torus), all in the box of radius `R`.  If the cut parameters correspond on the cubes of the
box of radius `R₁ = R + (3 L^(1+m₁) + 3 L^3) + L^(1+m₁)` and the raw data agree under `bm` on the
set `RowsDep (S_Y)` read by the rows, then the multipliers correspond on `S_Y`, the corrections
`φ - φ₀` on `Y`, and the fields where the data agree on `approxDep`, in particular at the sites
`RowSite` of the rows of `H_D(0)` at `S_Y`.  Margins:
`4 R + 12 L^(1+m₁) + 7 L + 5 < N₁ L^m₁ L` and
`2 R₁ + 5 L · cellSide L 0 m₁ 1 < N₁ L^m₁ L` (and for `N₁'`). -/
theorem baseBackground_twoTorus {c BG : ℝ}
    (hS : Dec2.DecSpecs d L (Dec2.selfKc d L) (Cchi d L) c BG) {a : ℕ → ℝ} {ν : ℝ}
    (SA : DGSetting (GA) a ν) (SB : DGSetting (GB) a ν) (HB : BgHyp d L 1 ϱ a ν) {κ : ℝ}
    (hκ : 0 ≤ κ) (hM : c * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    {F₁ : Dec2.DecParams (coverOf (GA)) × RawData d L (N₁ * L ^ m₁) 1 N →
      ((GA).Ω 1 × Fin N → ℂ) × ((GA).Ω 1 → ℂ)}
    {F₁' : Dec2.DecParams (coverOf (GB)) × RawData d L (N₁' * L ^ m₁) 1 N →
      ((GB).Ω 1 × Fin N → ℂ) × ((GB).Ω 1 → ℂ)}
    (hF₁ : ∀ (s : Dec2.DecParams (coverOf (GA))) (D : BgData (GA) N),
      (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC (GA) (bgC0 d L N) (c7 d L N BG κ) ν D → ∀ (φ : (GA).Ω 1 × Fin N → ℂ)
        (α : (GA).Ω 1 → ℂ), Dec2.IsDecBg (coverOf (GA)) (GA) a ν (rho4 d L N BG κ) s D φ α →
          F₁ (s, rawOf D) = (φ, α))
    (hF₁' : ∀ (s : Dec2.DecParams (coverOf (GB))) (D : BgData (GB) N),
      (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC (GB) (bgC0 d L N) (c7 d L N BG κ) ν D → ∀ (φ : (GB).Ω 1 × Fin N → ℂ)
        (α : (GB).Ω 1 → ℂ), Dec2.IsDecBg (coverOf (GB)) (GB) a ν (rho4 d L N BG κ) s D φ α →
          F₁' (s, rawOf D) = (φ, α))
    {s : DecParams (GA)} {s' : DecParams (GB)} (hs : ∀ P, ‖s P‖ < Real.exp κ)
    (hs' : ∀ P, ‖s' P‖ < Real.exp κ)
    {D : BgData (GA) N} {D' : BgData (GB) N}
    (hDd : InUnionDomainC (GA) (bgC0 d L N) (c7 d L N BG κ) ν D)
    (hDd' : InUnionDomainC (GB) (bgC0 d L N) (c7 d L N BG κ) ν D')
    {𝒞 : Finset (ℕ × Balaban.Localization.CTorus d L N₁ m₁ 1)}
    {X₁ Y : Finset (Balaban.Localization.CTorus d L N₁ m₁ 1)}
    (hY : IsNnComp ((Vset X₁ 𝒞).filter fun x => x ∈ (GA).Ω 1) Y)
    (hYc : IsNnComp ((Vset (X₁.image bm) (𝒞.image (Prod.map id bm))).filter
      fun x => x ∈ (GB).Ω 1) (Y.image bm))
    (hs0 : ∀ P ∈ parCubes (GA) X₁, P ∉ 𝒞 → extS (GA) s P = 0)
    (hs0' : ∀ P ∈ parCubes (GB) (X₁.image bm), P ∉ 𝒞.image (Prod.map id bm) →
      extS (GB) s' P = 0)
    {R : ℕ} (hXR : ∀ x ∈ X₁, InBox d R ((N₁ * L ^ m₁) * L ^ 1) x)
    (hCR : ∀ P ∈ 𝒞, InBox d R ((N₁ * L ^ m₁) * L ^ 1) P.2)
    (hYR : ∀ x ∈ Y, InBox d R ((N₁ * L ^ m₁) * L ^ 1) x)
    (hsP : ∀ P ∈ cubeIdx (GA),
      InBox d (R + (3 * L ^ (1 + m₁) + 3 * L ^ (1 + 2)) + L ^ (1 + m₁))
        ((N₁ * L ^ m₁) * L ^ 1) P.2 → extS (GB) s' (Prod.map id bm P) = extS (GA) s P)
    (hn : 4 * R + 12 * L ^ (1 + m₁) + 7 * L ^ 1 + 5 < (N₁ * L ^ m₁) * L ^ 1)
    (hn' : 4 * R + 12 * L ^ (1 + m₁) + 7 * L ^ 1 + 5 < (N₁' * L ^ m₁) * L ^ 1)
    (hnS : 2 * (R + (3 * L ^ (1 + m₁) + 3 * L ^ (1 + 2)) + L ^ (1 + m₁)) +
      5 * (L * cellSide L 0 m₁ 1) < (N₁ * L ^ m₁) * L ^ 1)
    (hnS' : 2 * (R + (3 * L ^ (1 + m₁) + 3 * L ^ (1 + 2)) + L ^ (1 + m₁)) +
      5 * (L * cellSide L 0 m₁ 1) < (N₁' * L ^ m₁) * L ^ 1)
    (hD : RawBoxAgree {z | RowsDep (GA) a ν (SY (GA) X₁ 𝒞 Y) z} (rawOf D) (rawOf D')) :
    (∀ x : (GA).Ω 1, (x : Balaban.Localization.CTorus d L N₁ m₁ 1) ∈ SY (GA) X₁ 𝒞 Y →
      (F₁' (s', rawOf D')).2 (ιb x) = (F₁ (s, rawOf D)).2 x) ∧
    (∀ y : (GA).Ω 1, (y : Balaban.Localization.CTorus d L N₁ m₁ 1) ∈ Y → ∀ i : Fin N,
      (F₁' (s', rawOf D')).1 (ιb y, i) -
          approxField (GB) a ν D'.Ψ D'.h (bm (y : Balaban.Localization.CTorus d L N₁ m₁ 1)) i =
        (F₁ (s, rawOf D)).1 (y, i) -
          approxField (GA) a ν D.Ψ D.h (y : Balaban.Localization.CTorus d L N₁ m₁ 1) i) ∧
    (∀ y : (GA).Ω 1, (y : Balaban.Localization.CTorus d L N₁ m₁ 1) ∈ Y →
      (∀ z ∈ approxDep (GA) (y : Balaban.Localization.CTorus d L N₁ m₁ 1),
        D.Ψ z = D'.Ψ (bm z) ∧ D.h z = D'.h (bm z)) →
      ∀ i : Fin N, (F₁' (s', rawOf D')).1 (ιb y, i) = (F₁ (s, rawOf D)).1 (y, i)) ∧
    (∀ y : (GA).Ω 1, RowSite (GA) a ν (0 : (GA).Ω 1 → ℂ) (SY (GA) X₁ 𝒞 Y) y → ∀ i : Fin N,
      (F₁' (s', rawOf D')).1 (ιb y, i) = (F₁ (s, rawOf D)).1 (y, i)) := by
  have hL : 3 ≤ L := SA.hL
  have hconn : HatConn (GA) := Inhabited.LevelStep.hatConn_lvTopG (k := 0) hL
  have hconn' : HatConn (GB) := Inhabited.LevelStep.hatConn_lvTopG (k := 0) hL
  refine decBg_value_twoTorus_of_box (j := 1) (K := 1) (le_refl 1) le_rfl
    (Dec2.decSpecs_of_dec2 hS) SA SB hconn hconn' HB hκ hM (F₁ := F₁) (F₁' := F₁')
    (fun s D hs hD φ α h => hF₁ s D hs hD φ α ⟨h.small, h.fixed, h.field⟩)
    (fun s D hs hD φ α h => hF₁' s D hs hD φ α ⟨h.small, h.fixed, h.field⟩) hs hs' hDd hDd' hY hYc
    hs0 hs0' hXR hCR hYR hsP hn hn' hnS hnS' hD

end Level1

end Balaban.LargeField.Base
