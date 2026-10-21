/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Base.BaseBgAgree
public import Balaban.LargeField.Base.BaseBgLocalityAlg
public import Balaban.LargeField.Base.BaseBgExpansion
public import Balaban.LargeField.Base.BaseBackgroundLocal

/-!
# A functional of the decoupled background that reads the seed forgets the unrooted cells

For the background map `F (s, θ) = (φ(s), α(s))` of `baseBackground_analytic_whole` (the decoupled
background of a datum `θ` at the parameters `s`, on the polydisc `|s_P| < e^κ`), a function `Fe` of
`(φ, α)` that reads the field and the multiplier only at the sites of a seed satisfies, for
parameters `s` vanishing off a family `Cs` of cells,
`Fe (F (s, θ)) = Fe (F (cutTo (rootComp P seed Cs) s, θ))` (`bgFunctional_cutTo_invariant`), with
the patches `P = cellPatch` of the level-1 cover.  This is the locality hypothesis of the rooted
Lemma AE (`rootedExpansion_of_cutTo`).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField.Base

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization Balaban.Fluctuation
  Balaban.LargeField Balaban.SmallField Balaban.Green

section Functional

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}
  (G : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ) (a : ℕ → ℝ) (ν : ℝ)

/-- A function of the decoupled background `(φ, α)` that reads the field and the multiplier only at
the sites of `seed`. -/
def ReadsSeed (seed : Finset (Balaban.Localization.CTorus d L N₁ m₁ (k + 1)))
    (Fe : ((G.Ω 1 × Fin N → ℂ) × (G.Ω 1 → ℂ)) → ℂ) : Prop :=
  ∀ u u' : (G.Ω 1 × Fin N → ℂ) × (G.Ω 1 → ℂ),
    (∀ y : G.Ω 1, (y : Balaban.Localization.CTorus d L N₁ m₁ (k + 1)) ∈ seed → ∀ i, u.1 (y, i) = u'.1 (y, i)) →
    (∀ x : G.Ω 1, (x : Balaban.Localization.CTorus d L N₁ m₁ (k + 1)) ∈ seed → u.2 x = u'.2 x) →
    Fe u = Fe u'

/-- **The background map is the decoupled background**: `F (s, θ) = (decBgField, decBgMult)`. -/
theorem F_eq_decBg {Kc Cx c BG : ℝ} (hS : Dec2.DecSpecs d L Kc Cx c BG)
    (Sb : Dec2.CoverBase (coverOf G) G a ν Kc Cx) (HB : BgHyp d L (k + 1) ϱ a ν) {κ : ℝ}
    (hκ : 0 ≤ κ) (hM : c * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    {F : Dec2.DecParams (coverOf G) × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      (G.Ω 1 × Fin N → ℂ) × (G.Ω 1 → ℂ)}
    (hF : ∀ (s : Dec2.DecParams (coverOf G)) (D : BgData G N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC G (bgC0 d L N) (c7 d L N BG κ) ν D → ∀ (φ : G.Ω 1 × Fin N → ℂ)
        (α : G.Ω 1 → ℂ), Dec2.IsDecBg (coverOf G) G a ν (rho4 d L N BG κ) s D φ α →
          F (s, (D.Ψ, D.h)) = (φ, α))
    {s : Dec2.DecParams (coverOf G)} (hs : ∀ P, ‖s P‖ < Real.exp κ) {Dd : BgData G N}
    (hDu : InUnionDomainC G (bgC0 d L N) (c7 d L N BG κ) ν Dd) :
    F (s, (Dd.Ψ, Dd.h)) = (Dec2.decBgField (coverOf G) G a ν (rho4 d L N BG κ) s Dd,
      Dec2.decBgMult (coverOf G) G a ν (rho4 d L N BG κ) s Dd) := by
  obtain ⟨δ, ε, hδ0, hδε, hε, hδ, hνε, hD⟩ := hDu
  obtain ⟨φ, α, hsol, huniq, -⟩ := Dec2.i4b_exists_unique hS Sb HB hκ hM
    (fun P => (hs P).le) hδ0 hδε hε hδ hνε hD
  obtain ⟨hφ, hα⟩ := Dec2.decBg_eq hsol huniq
  rw [hφ, hα]
  exact hF s Dd hs ⟨δ, ε, hδ0, hδε, hε, hδ, hνε, hD⟩ φ α hsol

omit [NeZero L] [NeZero N₁] in
theorem norm_cutTo_lt {ι : Type*} [DecidableEq ι] (A : Finset ι) (s : ι → ℂ) {r : ℝ}
    (hs : ∀ P, ‖s P‖ < r) (P : ι) : ‖cutTo A s P‖ < r := by
  unfold cutTo
  split_ifs
  · exact hs P
  · rw [norm_zero]; exact lt_of_le_of_lt (norm_nonneg _) (hs P)

/-- **(AE2) for a functional of the decoupled background.**  For parameters `s` of the open polydisc
vanishing off a family `Cs` of cells, a function `Fe` of the decoupled background that reads the
seed only takes the same value at `s` and at the parameters `cutTo A s`, `A` the rooted component
of `Cs` at the seed (patches `cellPatch`, radius `Dr ≥ 3 L^{k+1}`).  The torus is the whole of `Ω₁`. -/
theorem bgFunctional_cutTo_invariant {Kc Cx c BG : ℝ} (hS : Dec2.DecSpecs d L Kc Cx c BG)
    (Sb : Dec2.CoverBase (coverOf G) G a ν Kc Cx) (HB : BgHyp d L (k + 1) ϱ a ν) {κ : ℝ}
    (hκ : 0 ≤ κ) (hM : c * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    {F : Dec2.DecParams (coverOf G) × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      (G.Ω 1 × Fin N → ℂ) × (G.Ω 1 → ℂ)}
    (hF : ∀ (s : Dec2.DecParams (coverOf G)) (D : BgData G N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC G (bgC0 d L N) (c7 d L N BG κ) ν D → ∀ (φ : G.Ω 1 × Fin N → ℂ)
        (α : G.Ω 1 → ℂ), Dec2.IsDecBg (coverOf G) G a ν (rho4 d L N BG κ) s D φ α →
          F (s, (D.Ψ, D.h)) = (φ, α))
    {Dd : BgData G N} (hDu : InUnionDomainC G (bgC0 d L N) (c7 d L N BG κ) ν Dd)
    (hΩ : ∀ z, z ∈ G.Ω 1) {Dr : ℕ} (hDD : L ^ (k + 1) + 2 * L ^ (k + 1) ≤ Dr)
    {seed : Finset (Balaban.Localization.CTorus d L N₁ m₁ (k + 1))}
    {Fe : ((G.Ω 1 × Fin N → ℂ) × (G.Ω 1 → ℂ)) → ℂ} (hFe : ReadsSeed G seed Fe)
    {Cs : Finset ↥(coverOf G).cubeIdx} {s : Dec2.DecParams (coverOf G)} (hsC : s ∈ supportedOn Cs)
    (hs : ∀ P, ‖s P‖ < Real.exp κ) :
    Fe (F (s, (Dd.Ψ, Dd.h))) =
      Fe (F (cutTo (rootComp (cellPatch (coverOf G) Dr) (seed : Set _) Cs) s, (Dd.Ψ, Dd.h))) := by
  classical
  set A := rootComp (cellPatch (coverOf G) Dr) (seed : Set _) Cs with hA
  set s' := cutTo A s with hs'
  have hs'lt : ∀ P, ‖s' P‖ < Real.exp κ := norm_cutTo_lt A s hs
  obtain ⟨δ, ε, hδ0, hδε, hε, hδ, hνε, hD⟩ := hDu
  have hDu : InUnionDomainC G (bgC0 d L N) (c7 d L N BG κ) ν Dd :=
    ⟨δ, ε, hδ0, hδε, hε, hδ, hνε, hD⟩
  have hsup' : ∀ q, ActC (coverOf G) (Dec2.extS _ s') q → ActC (coverOf G) (Dec2.extS _ s) q :=
    fun q hq => ⟨hq.1, by rw [← sProd_cutTo_eq_of_active A s hq.2]; exact hq.2⟩
  have hcomp : ∀ q ∈ actComp (coverOf G) Dr (Dec2.extS _ s) seed,
      (coverOf G).sProd (Dec2.extS _ s) q = (coverOf G).sProd (Dec2.extS _ s') q := by
    intro q hq
    exact (sProd_cutTo_eq_of_footprint A s fun i hi hiC =>
      footprint_subset_rootComp hsC hq hi hiC).symm
  have key := decBg_agree_of_seedHull G a ν Dd hS Sb HB hκ hM (v := s) (v' := s') (smax := s)
    (fun P => (hs P).le) (fun P => (hs'lt P).le) hδ0 hδε hε hδ hνε hD hDD seed (fun q hq => hq)
    hsup' hcomp (fun _ _ z _ => hΩ z)
  rw [F_eq_decBg G a ν hS Sb HB hκ hM hF hs hDu, F_eq_decBg G a ν hS Sb HB hκ hM hF hs'lt hDu]
  refine hFe _ _ (fun y hy i => ?_) (fun x hx => ?_)
  · have hyT := seed_subset_seedHull (coverOf G) Dr (Dec2.extS _ s) seed hy
    exact (key.2 y.1 y.2 (subset_nbhdSup _ _ hyT) i).symm
  · exact (key.1 x.1 x.2 (seed_subset_seedHull (coverOf G) Dr (Dec2.extS _ s) seed hx)).symm

end Functional

end Balaban.LargeField.Base
