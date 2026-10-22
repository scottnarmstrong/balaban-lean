/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.LocalPairDecBg
public import Balaban.Fluctuation.LocalPairDepth
public import Balaban.Localization.Decoupled2Background

/-!
# The decoupled background of one pair at two vectors: the core of the hull lemmas

`decBg_agree_core`: for an arbitrary set `T ⊆ Y` of sites satisfying the dichotomy, row, inner-centre and
residue hypotheses of `Dec2.decBg_component_cross` for the pair `(coverOf G, G)` compared with itself, the
multipliers at two vectors agree on `T` and the fields on `Y`.  The hull lemmas
`HoleStep.decBg_agree_of_hull` (`T` the block hull of the active closure) and
`Base.decBg_agree_of_seedHull` (`T` the hull together with the neighbourhood of the seed) are its
instances.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.Fluctuation

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization Balaban.LargeField
  Balaban.SmallField

section Core

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}
  (G : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ) (a : ℕ → ℝ) (ν : ℝ) (D' : BgData G N)

/-- **Core with two data: the decoupled backgrounds and multipliers of one pair at two vectors and two
data agree on `T`/`Y`.**
For an arbitrary set `T ⊆ Y` satisfying the dichotomy, row, inner-centre and residue hypotheses of
`Dec2.decBg_component_cross` for the pair compared with itself, the multipliers at `v` and `v'`
agree on `T` and the fields on `Y`.  The raw data agree on `approxDep` of the sites of `Y` (`hdat`). -/
theorem decBg_agree_core_data (D₁ D₂ : BgData G N) {Kc Cx c BG : ℝ} (hS : Dec2.DecSpecs d L Kc Cx c BG)
    (Sb : Dec2.CoverBase (coverOf G) G a ν Kc Cx)
    (HB : BgHyp d L (k + 1) ϱ a ν) {κ : ℝ} (hκ : 0 ≤ κ)
    (hM : c * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    {v v' : Dec2.DecParams (coverOf G)}
    (hv : ∀ P, ‖v P‖ ≤ Real.exp κ) (hv' : ∀ P, ‖v' P‖ ≤ Real.exp κ)
    {δ ε : ℝ} (hδ0 : 0 < δ) (hδε : δ ≤ ε) (hε : ε ≤ bgC0 d L N) (hδ : δ ≤ c7 d L N BG κ)
    (hνε : ν * ((L : ℝ) ^ (k + 1)) ^ 2 * ε ^ 2 ≤ δ ^ 2) (hD₁ : InDomainC G ν δ ε D₁)
    {δ₂ ε₂ : ℝ} (hδ0' : 0 < δ₂) (hδε' : δ₂ ≤ ε₂) (hε' : ε₂ ≤ bgC0 d L N) (hδ' : δ₂ ≤ c7 d L N BG κ)
    (hνε' : ν * ((L : ℝ) ^ (k + 1)) ^ 2 * ε₂ ^ 2 ≤ δ₂ ^ 2) (hD₂ : InDomainC G ν δ₂ ε₂ D₂)
    {T Y : Finset (CTorus d L N₁ m₁ (k + 1))} (hTY : T ⊆ Y)
    (hdich : ∀ q ∈ (coverOf G).cubeIdx, (coverOf G).sProd (Dec2.extS _ v) q ≠ 0 →
      SubI G (intBox q) T ∨ DisjI G (intBox q) T)
    (hdich' : ∀ q ∈ (coverOf G).cubeIdx, (coverOf G).sProd (Dec2.extS _ v') q ≠ 0 →
      SubI G (intBox q) T ∨ DisjI G (intBox q) T)
    (hrow : ∀ q ∈ (coverOf G).cubeIdx, (coverOf G).sProd (Dec2.extS _ v) q ≠ 0 →
      ∀ x ∈ Y, x ∈ intBox q → x ∈ T)
    (hrow' : ∀ q ∈ (coverOf G).cubeIdx, (coverOf G).sProd (Dec2.extS _ v') q ≠ 0 →
      ∀ x ∈ Y, x ∈ intBox q → x ∈ T)
    (hin : ∀ q ∈ Dec2.innerCentres (coverOf G) G T, (coverOf G).sProd (Dec2.extS _ v) q ≠ 0 →
      q ∈ Dec2.innerCentres (coverOf G) G T ∧
        (coverOf G).sProd (Dec2.extS _ v') q = (coverOf G).sProd (Dec2.extS _ v) q ∧
        (∀ x ∈ intBox q, ∀ y : CTorus d L N₁ m₁ (k + 1),
          (y = x ∨ ∃ μ : Fin d, y = x + Pi.single μ 1 ∨ y = x - Pi.single μ 1) →
            ∀ n, 1 ≤ n → n ≤ k + 1 → (y ∈ G.layer n ↔ y ∈ G.layer n)) ∧
        (∀ x ∈ intBox q, (coverOf G).chi q x = (coverOf G).chi q x))
    (hin' : ∀ q ∈ Dec2.innerCentres (coverOf G) G T, (coverOf G).sProd (Dec2.extS _ v') q ≠ 0 →
      q ∈ Dec2.innerCentres (coverOf G) G T ∧ (coverOf G).sProd (Dec2.extS _ v) q ≠ 0)
    (hres : ∀ x ∈ T, x ∈ G.Ω 1 → ∀ y ∈ resSites G x, y ∈ G.Ω 1 ∧ y ∈ Y)
    (hdat : ∀ y ∈ Y, y ∈ G.Ω 1 → ∀ z ∈ approxDep G y, D₁.Ψ z = D₂.Ψ z ∧ D₁.h z = D₂.h z) :
    (∀ (x : CTorus d L N₁ m₁ (k + 1)) (hx : x ∈ G.Ω 1), x ∈ T →
        Dec2.decBgMult (coverOf G) G a ν (rho4 d L N BG κ) v' D₂ ⟨x, hx⟩ =
          Dec2.decBgMult (coverOf G) G a ν (rho4 d L N BG κ) v D₁ ⟨x, hx⟩) ∧
      ∀ (y : CTorus d L N₁ m₁ (k + 1)) (hy : y ∈ G.Ω 1), y ∈ Y → ∀ i : Fin N,
        Dec2.decBgField (coverOf G) G a ν (rho4 d L N BG κ) v' D₂ (⟨y, hy⟩, i) =
          Dec2.decBgField (coverOf G) G a ν (rho4 d L N BG κ) v D₁ (⟨y, hy⟩, i) := by
  classical
  obtain ⟨φ, α, hsol, huniq, -⟩ := Dec2.i4b_exists_unique hS Sb HB hκ hM hv hδ0 hδε hε hδ hνε hD₁
  obtain ⟨φ', α', hsol', huniq', -⟩ :=
    Dec2.i4b_exists_unique hS Sb HB hκ hM hv' hδ0' hδε' hε' hδ' hνε' hD₂
  obtain ⟨hφ, hα⟩ := Dec2.decBg_eq hsol huniq
  obtain ⟨hφ', hα'⟩ := Dec2.decBg_eq hsol' huniq'
  rw [hφ, hα, hφ', hα']
  have h := Dec2.decBg_component_cross (C := coverOf G) (C' := coverOf G) (H := G)
    (H' := G) (s := v) (s' := v') (D := D₁) (D' := D₂) (T := T) (Y := Y)
    hS Sb Sb HB HB hκ hM hv hv' hδ0 hδε hε hδ hνε hδ0' hδε' hε' hδ' hνε' hD₁ hD₂ hTY
    (fun _ _ _ _ _ => Iff.rfl) hdich hdich' hrow hrow' hin hin' hres
    (fun _ _ _ _ _ _ _ _ _ _ => Iff.rfl) hdat hsol hsol'
  exact ⟨fun x hx hxT => h.1 x hx hx hxT, fun y hy hyY i => h.2 y hy hy hyY i⟩

/-- **Core: the decoupled backgrounds and multipliers of one pair at two vectors agree on `T`/`Y`.**
For an arbitrary set `T ⊆ Y` satisfying the dichotomy, row, inner-centre and residue hypotheses of
`Dec2.decBg_component_cross` for the pair compared with itself, the multipliers at `v` and `v'`
agree on `T` and the fields on `Y`.  `decBg_agree_of_seedHull` is the instance `T = seedHull`. -/
theorem decBg_agree_core {Kc Cx c BG : ℝ} (hS : Dec2.DecSpecs d L Kc Cx c BG)
    (Sb : Dec2.CoverBase (coverOf G) G a ν Kc Cx)
    (HB : BgHyp d L (k + 1) ϱ a ν) {κ : ℝ} (hκ : 0 ≤ κ)
    (hM : c * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    {v v' : Dec2.DecParams (coverOf G)}
    (hv : ∀ P, ‖v P‖ ≤ Real.exp κ) (hv' : ∀ P, ‖v' P‖ ≤ Real.exp κ)
    {δ ε : ℝ} (hδ0 : 0 < δ) (hδε : δ ≤ ε) (hε : ε ≤ bgC0 d L N) (hδ : δ ≤ c7 d L N BG κ)
    (hνε : ν * ((L : ℝ) ^ (k + 1)) ^ 2 * ε ^ 2 ≤ δ ^ 2) (hD' : InDomainC G ν δ ε D')
    {T Y : Finset (CTorus d L N₁ m₁ (k + 1))} (hTY : T ⊆ Y)
    (hdich : ∀ q ∈ (coverOf G).cubeIdx, (coverOf G).sProd (Dec2.extS _ v) q ≠ 0 →
      SubI G (intBox q) T ∨ DisjI G (intBox q) T)
    (hdich' : ∀ q ∈ (coverOf G).cubeIdx, (coverOf G).sProd (Dec2.extS _ v') q ≠ 0 →
      SubI G (intBox q) T ∨ DisjI G (intBox q) T)
    (hrow : ∀ q ∈ (coverOf G).cubeIdx, (coverOf G).sProd (Dec2.extS _ v) q ≠ 0 →
      ∀ x ∈ Y, x ∈ intBox q → x ∈ T)
    (hrow' : ∀ q ∈ (coverOf G).cubeIdx, (coverOf G).sProd (Dec2.extS _ v') q ≠ 0 →
      ∀ x ∈ Y, x ∈ intBox q → x ∈ T)
    (hin : ∀ q ∈ Dec2.innerCentres (coverOf G) G T, (coverOf G).sProd (Dec2.extS _ v) q ≠ 0 →
      q ∈ Dec2.innerCentres (coverOf G) G T ∧
        (coverOf G).sProd (Dec2.extS _ v') q = (coverOf G).sProd (Dec2.extS _ v) q ∧
        (∀ x ∈ intBox q, ∀ y : CTorus d L N₁ m₁ (k + 1),
          (y = x ∨ ∃ μ : Fin d, y = x + Pi.single μ 1 ∨ y = x - Pi.single μ 1) →
            ∀ n, 1 ≤ n → n ≤ k + 1 → (y ∈ G.layer n ↔ y ∈ G.layer n)) ∧
        (∀ x ∈ intBox q, (coverOf G).chi q x = (coverOf G).chi q x))
    (hin' : ∀ q ∈ Dec2.innerCentres (coverOf G) G T, (coverOf G).sProd (Dec2.extS _ v') q ≠ 0 →
      q ∈ Dec2.innerCentres (coverOf G) G T ∧ (coverOf G).sProd (Dec2.extS _ v) q ≠ 0)
    (hres : ∀ x ∈ T, x ∈ G.Ω 1 → ∀ y ∈ resSites G x, y ∈ G.Ω 1 ∧ y ∈ Y) :
    (∀ (x : CTorus d L N₁ m₁ (k + 1)) (hx : x ∈ G.Ω 1), x ∈ T →
        Dec2.decBgMult (coverOf G) G a ν (rho4 d L N BG κ) v' D' ⟨x, hx⟩ =
          Dec2.decBgMult (coverOf G) G a ν (rho4 d L N BG κ) v D' ⟨x, hx⟩) ∧
      ∀ (y : CTorus d L N₁ m₁ (k + 1)) (hy : y ∈ G.Ω 1), y ∈ Y → ∀ i : Fin N,
        Dec2.decBgField (coverOf G) G a ν (rho4 d L N BG κ) v' D' (⟨y, hy⟩, i) =
          Dec2.decBgField (coverOf G) G a ν (rho4 d L N BG κ) v D' (⟨y, hy⟩, i) := by
  exact decBg_agree_core_data G a ν D' D' hS Sb HB hκ hM hv hv' hδ0 hδε hε hδ hνε hD' hδ0 hδε hε hδ hνε
    hD' hTY hdich hdich' hrow hrow' hin hin' hres (fun _ _ _ _ _ => ⟨rfl, rfl⟩)

end Core

end Balaban.Fluctuation
