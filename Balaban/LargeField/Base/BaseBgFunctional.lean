/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Base.BaseBgAgree
public import Balaban.LargeField.Base.BaseBgLocalityAlg
public import Balaban.Green.FinalBoxLocCore
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
  Balaban.LargeField Balaban.SmallField Balaban.Green Balaban.Analysis

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

open Classical in
/-- **Lemma AE through the decoupled background (item 3).**  Let `F` be the background map, analytic
on the open polydisc of parameters for the data of `Dd`, `Fe` a function of the decoupled background
that reads the seed and is analytic and bounded by `B` on a set `U` containing the backgrounds of the
polydisc.  Then `Fe (F (1, θ)) = Fe (F (0, θ)) + ∑_{C ≠ ∅ rooted} coef_C`, the coefficients of the
non-rooted families vanish and `‖coef_C‖ ≤ 2B e^{-(κ-1)|C|}` (`κ ≥ 1`). -/
theorem bgFunctional_expansion {Kc Cx c BG : ℝ} (hS : Dec2.DecSpecs d L Kc Cx c BG)
    (Sb : Dec2.CoverBase (coverOf G) G a ν Kc Cx) (HB : BgHyp d L (k + 1) ϱ a ν) {κ : ℝ}
    (hκ : 1 ≤ κ) (hM : c * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    {F : Dec2.DecParams (coverOf G) × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      (G.Ω 1 × Fin N → ℂ) × (G.Ω 1 → ℂ)}
    (hF : ∀ (s : Dec2.DecParams (coverOf G)) (D : BgData G N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC G (bgC0 d L N) (c7 d L N BG κ) ν D → ∀ (φ : G.Ω 1 × Fin N → ℂ)
        (α : G.Ω 1 → ℂ), Dec2.IsDecBg (coverOf G) G a ν (rho4 d L N BG κ) s D φ α →
          F (s, (D.Ψ, D.h)) = (φ, α))
    {Dd : BgData G N} (hDu : InUnionDomainC G (bgC0 d L N) (c7 d L N BG κ) ν Dd)
    (hFan : AnalyticOnNhd ℂ F {q | (∀ P, ‖q.1 P‖ < Real.exp κ) ∧
      ∃ D : BgData G N, InUnionDomainC G (bgC0 d L N) (c7 d L N BG κ) ν D ∧ q.2 = (D.Ψ, D.h)})
    (hΩ : ∀ z, z ∈ G.Ω 1) {Dr : ℕ} (hDD : L ^ (k + 1) + 2 * L ^ (k + 1) ≤ Dr)
    {seed : Finset (Balaban.Localization.CTorus d L N₁ m₁ (k + 1))}
    {Fe : ((G.Ω 1 × Fin N → ℂ) × (G.Ω 1 → ℂ)) → ℂ} (hFe : ReadsSeed G seed Fe)
    {U : Set ((G.Ω 1 × Fin N → ℂ) × (G.Ω 1 → ℂ))} (hFeU : AnalyticOnNhd ℂ Fe U) {B : ℝ}
    (hB : ∀ u ∈ U, ‖Fe u‖ ≤ B)
    (hmem : ∀ s : Dec2.DecParams (coverOf G), (∀ P, ‖s P‖ < Real.exp κ) →
      F (s, (Dd.Ψ, Dd.h)) ∈ U) :
    Fe (F (fun _ => 1, (Dd.Ψ, Dd.h))) = Fe (F (0, (Dd.Ψ, Dd.h))) +
        ∑ C ∈ Finset.univ.filter (fun C : Finset ↥(coverOf G).cubeIdx =>
          C.Nonempty ∧ IsRootedFamily (cellPatch (coverOf G) Dr) (seed : Set _) C),
          coef (fun s => Fe (F (s, (Dd.Ψ, Dd.h)))) C ∧
      (∀ C : Finset ↥(coverOf G).cubeIdx,
        ¬ IsRootedFamily (cellPatch (coverOf G) Dr) (seed : Set _) C →
        coef (fun s => Fe (F (s, (Dd.Ψ, Dd.h)))) C = 0) ∧
      (∀ C : Finset ↥(coverOf G).cubeIdx, C.Nonempty →
        ‖coef (fun s => Fe (F (s, (Dd.Ψ, Dd.h)))) C‖ ≤ 2 * B * Real.exp (-(κ - 1) * C.card)) := by
  classical
  have hpoly : ∀ s ∈ polydisc (0 : Dec2.DecParams (coverOf G)) (fun _ => Real.exp κ),
      ∀ P, ‖s P‖ < Real.exp κ := fun s hs P => by simpa using hs P
  have hfan : AnalyticOnNhd ℂ (fun s => Fe (F (s, (Dd.Ψ, Dd.h))))
      (polydisc (0 : Dec2.DecParams (coverOf G)) (fun _ => Real.exp κ)) := by
    intro s hs
    have hq : AnalyticAt ℂ (fun s : Dec2.DecParams (coverOf G) => (s, (Dd.Ψ, Dd.h))) s := by
      fun_prop
    have h1 : AnalyticAt ℂ F (s, (Dd.Ψ, Dd.h)) := hFan _ ⟨hpoly s hs, Dd, hDu, rfl⟩
    exact AnalyticAt.comp (g := Fe) (f := fun s => F (s, (Dd.Ψ, Dd.h)))
      (hFeU _ (hmem s (hpoly s hs))) (AnalyticAt.comp (g := F) (f := fun s => (s, (Dd.Ψ, Dd.h))) h1 hq)
  have hcut : ∀ (Cs : Finset ↥(coverOf G).cubeIdx) (s : Dec2.DecParams (coverOf G)),
      s ∈ polydisc (0 : Dec2.DecParams (coverOf G)) (fun _ => Real.exp κ) → s ∈ supportedOn Cs →
      Fe (F (s, (Dd.Ψ, Dd.h))) =
        Fe (F (cutTo (rootComp (cellPatch (coverOf G) Dr) (seed : Set _) Cs) s, (Dd.Ψ, Dd.h))) :=
    fun Cs s hs hsC => bgFunctional_cutTo_invariant G a ν hS Sb HB (by linarith) hM hF hDu hΩ hDD hFe
      hsC (hpoly s hs)
  have h0 : (0 : Dec2.DecParams (coverOf G)) ∈
      polydisc (0 : Dec2.DecParams (coverOf G)) (fun _ => Real.exp κ) := fun P => by
    simpa using Real.exp_pos κ
  have hb : ∀ s ∈ polydisc (0 : Dec2.DecParams (coverOf G)) (fun _ => Real.exp κ),
      ‖Fe (F (s, (Dd.Ψ, Dd.h))) - Fe (F (0, (Dd.Ψ, Dd.h)))‖ ≤ 2 * B := by
    intro s hs
    refine (norm_sub_le _ _).trans ?_
    have h1 := hB _ (hmem s (hpoly s hs))
    have h2 := hB _ (hmem 0 (hpoly 0 h0))
    linarith
  exact rootedExpansion_of_cutTo hκ hfan hcut hb

theorem nbhdSup_mono {r : ℕ} {T T' : Finset (Balaban.Localization.CTorus d L N₁ m₁ (k + 1))}
    (h : T ⊆ T') : nbhdSup r T ⊆ nbhdSup r T' := fun x hx => by
  obtain ⟨y, hy, hyx⟩ := mem_nbhdSup.1 hx
  exact mem_nbhdSup.2 ⟨y, h hy, hyx⟩

theorem seedHull_mono {C : DecCover d L N₁ m₁ (k + 1)} {Dr : ℕ}
    {s s' : ℕ × Balaban.Localization.CTorus d L N₁ m₁ (k + 1) → ℂ}
    (hss : ∀ q, ActC C s q → ActC C s' q)
    (seed : Finset (Balaban.Localization.CTorus d L N₁ m₁ (k + 1))) :
    seedHull C Dr s seed ⊆ seedHull C Dr s' seed :=
  Finset.union_subset_union (actHull_mono hss seed) (Finset.Subset.refl _)

/-- The indicator vector of a family of cells: `1` on the cells of `A`, `0` elsewhere. -/
def indVec (A : Finset ↥(coverOf G).cubeIdx) : Dec2.DecParams (coverOf G) :=
  fun i => if i ∈ A then 1 else 0

open Classical in
/-- A centre active for `cutTo A s` is active for the indicator vector of `A`. -/
theorem actC_indVec_of_cutTo (A : Finset ↥(coverOf G).cubeIdx) (s : Dec2.DecParams (coverOf G))
    {q : ℕ × Balaban.Localization.CTorus d L N₁ m₁ (k + 1)}
    (hq : ActC (coverOf G) (Dec2.extS _ (cutTo A s)) q) :
    ActC (coverOf G) (Dec2.extS _ (indVec G A)) q := by
  refine ⟨hq.1, ?_⟩
  have : (coverOf G).sProd (Dec2.extS _ (indVec G A)) q = 1 := by
    unfold DecCover.sProd
    refine Finset.prod_eq_one fun i hi => ?_
    have hiC : i ∈ (coverOf G).cubeIdx := (((coverOf G).mem_Qset).1 hi).1
    have hn : Dec2.extS (coverOf G) (cutTo A s) i ≠ 0 := fun h0 =>
      hq.2 (Finset.prod_eq_zero hi h0)
    rw [extS_cutTo_apply A s hiC] at hn
    have hA : (⟨i, hiC⟩ : ↥(coverOf G).cubeIdx) ∈ A := by
      by_contra hna
      exact hn (by simp [hna])
    simp [Dec2.extS, hiC, indVec, hA]
  rw [this]; exact one_ne_zero

open Classical in
/-- **Locality of the coefficients in the data.**  Two data of the union domain whose raw data agree on
`approxDep` of the sites of the `L^{k+1}`-neighbourhood of the seed hull of the indicator vector of the
rooted component of `Cs` give the same coefficient `coef_{Cs}` of a functional `Fe` that reads the seed
(radius `Dr ≥ 3 L^{k+1}`, whole torus). -/
theorem bgFunctional_coef_data_congr {Kc Cx c BG : ℝ} (hS : Dec2.DecSpecs d L Kc Cx c BG)
    (Sb : Dec2.CoverBase (coverOf G) G a ν Kc Cx) (HB : BgHyp d L (k + 1) ϱ a ν) {κ : ℝ}
    (hκ : 1 ≤ κ) (hM : c * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    {F : Dec2.DecParams (coverOf G) × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      (G.Ω 1 × Fin N → ℂ) × (G.Ω 1 → ℂ)}
    (hF : ∀ (s : Dec2.DecParams (coverOf G)) (D : BgData G N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC G (bgC0 d L N) (c7 d L N BG κ) ν D → ∀ (φ : G.Ω 1 × Fin N → ℂ)
        (α : G.Ω 1 → ℂ), Dec2.IsDecBg (coverOf G) G a ν (rho4 d L N BG κ) s D φ α →
          F (s, (D.Ψ, D.h)) = (φ, α))
    {Dd Dd' : BgData G N} (hDu : InUnionDomainC G (bgC0 d L N) (c7 d L N BG κ) ν Dd)
    (hDu' : InUnionDomainC G (bgC0 d L N) (c7 d L N BG κ) ν Dd')
    (hΩ : ∀ z, z ∈ G.Ω 1) {Dr : ℕ} (hDD : L ^ (k + 1) + 2 * L ^ (k + 1) ≤ Dr)
    {seed : Finset (Balaban.Localization.CTorus d L N₁ m₁ (k + 1))}
    {Fe : ((G.Ω 1 × Fin N → ℂ) × (G.Ω 1 → ℂ)) → ℂ} (hFe : ReadsSeed G seed Fe)
    (Cs : Finset ↥(coverOf G).cubeIdx)
    (hdat : ∀ y ∈ nbhdSup (L ^ (k + 1)) (seedHull (coverOf G) Dr (Dec2.extS _
        (indVec G (rootComp (cellPatch (coverOf G) Dr) (seed : Set _) Cs))) seed),
      y ∈ G.Ω 1 → ∀ z ∈ approxDep G y, Dd.Ψ z = Dd'.Ψ z ∧ Dd.h z = Dd'.h z) :
    coef (fun s => Fe (F (s, (Dd.Ψ, Dd.h)))) Cs = coef (fun s => Fe (F (s, (Dd'.Ψ, Dd'.h)))) Cs := by
  classical
  have hR : 1 < Real.exp κ := Real.one_lt_exp_iff.2 (by linarith)
  refine coef_congr_supported hR fun s hs hsC => ?_
  have hsb : ∀ P, ‖s P‖ < Real.exp κ := fun P => by simpa using hs P
  set A := rootComp (cellPatch (coverOf G) Dr) (seed : Set _) Cs with hA
  set s' := cutTo A s with hs'
  have hs'lt : ∀ P, ‖s' P‖ < Real.exp κ := norm_cutTo_lt A s hsb
  have e1 := bgFunctional_cutTo_invariant G a ν hS Sb HB (by linarith : 0 ≤ κ) hM hF hDu hΩ hDD hFe hsC hsb
  have e2 := bgFunctional_cutTo_invariant G a ν hS Sb HB (by linarith : 0 ≤ κ) hM hF hDu' hΩ hDD hFe hsC hsb
  rw [e1, e2]
  obtain ⟨δ, ε, hδ0, hδε, hε, hδ, hνε, hD⟩ := hDu
  obtain ⟨δ₂, ε₂, hδ0', hδε', hε', hδ', hνε', hD₂⟩ := hDu'
  have hDu : InUnionDomainC G (bgC0 d L N) (c7 d L N BG κ) ν Dd := ⟨δ, ε, hδ0, hδε, hε, hδ, hνε, hD⟩
  have hDu' : InUnionDomainC G (bgC0 d L N) (c7 d L N BG κ) ν Dd' :=
    ⟨δ₂, ε₂, hδ0', hδε', hε', hδ', hνε', hD₂⟩
  have hdat' : ∀ y ∈ nbhdSup (L ^ (k + 1)) (seedHull (coverOf G) Dr (Dec2.extS _ s') seed),
      y ∈ G.Ω 1 → ∀ z ∈ approxDep G y, Dd.Ψ z = Dd'.Ψ z ∧ Dd.h z = Dd'.h z := fun y hy =>
    hdat y (nbhdSup_mono (seedHull_mono (fun q hq => actC_indVec_of_cutTo G A s hq) seed) hy)
  have key := decBg_agree_of_seedHull_data G a ν Dd Dd' hS Sb HB (by linarith : 0 ≤ κ) hM
    (v := s') (v' := s') (smax := s') (fun P => (hs'lt P).le) (fun P => (hs'lt P).le) hδ0 hδε hε hδ
    hνε hD hδ0' hδε' hε' hδ' hνε' hD₂ hDD seed (fun q hq => hq) (fun q hq => hq)
    (fun q _ => rfl) (fun _ _ z _ => hΩ z) hdat'
  rw [F_eq_decBg G a ν hS Sb HB (by linarith : 0 ≤ κ) hM hF hs'lt hDu,
    F_eq_decBg G a ν hS Sb HB (by linarith : 0 ≤ κ) hM hF hs'lt hDu']
  refine hFe _ _ (fun y hy i => ?_) (fun x hx => ?_)
  · have hyT := seed_subset_seedHull (coverOf G) Dr (Dec2.extS _ s') seed hy
    exact (key.2 y.1 y.2 (subset_nbhdSup _ _ hyT) i).symm
  · exact (key.1 x.1 x.2 (seed_subset_seedHull (coverOf G) Dr (Dec2.extS _ s') seed hx)).symm

end Functional

end Balaban.LargeField.Base
