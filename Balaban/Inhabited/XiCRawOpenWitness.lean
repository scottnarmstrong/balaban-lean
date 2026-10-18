/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.XiCRawOpen
public import Balaban.SmallField.XiDomOpen
public import Balaban.Fluctuation.ParamActivityPhysical
public import Balaban.Fluctuation.ParamDatumFamily
public import Balaban.Fluctuation.GeneralClassMatch
import Mathlib.Tactic.Linarith

/-!
# Consequences of the shape of the chart, and the landed chart points

The chart `XiCRaw` is not open in `RawData`; it is open relative to the linear subspace `rawSub`
of data (`Balaban/Localization/XiCRawOpen.lean`).  Consequences proved here:

* `physSΛ` (the chart times the `ℓ¹` ball of sources) has empty interior, and is open relative to
  `rawSub × univ` (`physSΛ_interior_eq_empty`, `physSΛ_eventually`).
* Hence **every open set `V ⊆ physSΛ` is empty**, and `DirectTermsFamily` (whose field `isOpen`
  asks `V` open in `RawData × sources`) has no nonempty instance over the physical set
  (`DirectTermsFamily.eq_empty_of_interior_eq_empty`, `physical_directTermsFamily_eq_empty`).
* The field domain `XiDom` of the landed class is a cylinder over the same subspace: not open in
  the space of fields, open relative to the layer-constant fields (`xiDom_eventually`).
* At the landed chart points (a real and a nonreal datum of `Ξ^c_2`), the chart contains a
  neighbourhood of the point in the subspace of data, and is not open in `RawData`
  (`xiCRaw_witness`).
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Localization Balaban.Multiscale Balaban.Background Balaban.SmallField
  Balaban.SmallField.Def6 Filter Topology

section Physical

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}

/-- The physical parameter set has empty interior as soon as the subspace of data is proper. -/
theorem physSΛ_interior_eq_empty (S : StepSetting d L N₁ m₁ k N ϱ) (a₁ ν eps : ℝ)
    (hproper : ∃ q : RawData d L (N₁ * L ^ m₁) (k + 1) N, q ∉ rawSub N S.G') :
    interior (physSΛ S a₁ ν eps) = ∅ := by
  unfold physSΛ
  rw [interior_prod_eq, interior_xiCRaw_eq_empty S.G' (compWeight L a₁) ν 1 eps (k + 1) hproper]
  simp

/-- Under the standing hypothesis `BgHyp` the data subspace of a step is proper (`N ≥ 1`), so
`physSΛ` has empty interior. -/
theorem physSΛ_interior_eq_empty_of_bgHyp [NeZero N] (S : StepSetting d L N₁ m₁ k N ϱ)
    (a₁ ν eps : ℝ) (H : BgHyp d L (k + 1) ϱ (compWeight L a₁) ν) :
    interior (physSΛ S a₁ ν eps) = ∅ :=
  physSΛ_interior_eq_empty S a₁ ν eps
    (exists_not_mem_rawSub_of_bgHyp N S.G' H ⟨0, (S.hG' 0).1⟩)

/-- **A family over an open set of a set with empty interior is empty.** -/
theorem DirectTermsFamily.eq_empty_of_interior_eq_empty
    {Λ F' : Type} [NormedAddCommGroup Λ] [NormedSpace ℂ Λ]
    (S : StepSetting d L N₁ m₁ k N ϱ) (m₀ : ℕ) {hp : 0 < S.p₁} {emb : (S.U × Fin N → ℂ) → F'}
    {ρ Rσ εU a : ℝ} {Θ₀ : Λ} {SΛ : Set Λ} {XW : Set (F' × F')} {val : F' → F' → ℂ → Λ → ℂ}
    {AgΘ : Set (CTorus d L N₁ m₁ (k + 1)) → Λ → Λ → Prop}
    {AgF : Set (CTorus d L N₁ m₁ (k + 1)) → F' → F' → Prop}
    {I : DirectTerms S m₀ hp emb ρ Rσ εU a Θ₀ SΛ XW val AgΘ AgF} {V : Set Λ}
    (hF : DirectTermsFamily S m₀ I V) (hint : interior SΛ = ∅) : V = ∅ := by
  have := interior_maximal hF.sub hF.isOpen
  rw [hint] at this
  exact Set.subset_eq_empty this rfl

/-- **No nonempty open `V ⊆ physSΛ`**: the physical `DirectTermsFamily` is a family over the empty
set unless the subspace of data is the whole of `RawData`. -/
theorem eq_empty_of_isOpen_subset_physSΛ (S : StepSetting d L N₁ m₁ k N ϱ) (a₁ ν eps : ℝ)
    (hproper : ∃ q : RawData d L (N₁ * L ^ m₁) (k + 1) N, q ∉ rawSub N S.G')
    {V : Set (RawData d L (N₁ * L ^ m₁) (k + 1) N ×
      (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ))}
    (hV : IsOpen V) (hsub : V ⊆ physSΛ S a₁ ν eps) : V = ∅ := by
  have := interior_maximal hsub hV
  rw [physSΛ_interior_eq_empty S a₁ ν eps hproper] at this
  exact Set.subset_eq_empty this rfl

/-- **`physSΛ` is open relative to `rawSub × univ`**: near each of its points, the points of
`rawSub × univ` lie in `physSΛ`. -/
theorem physSΛ_eventually (S : StepSetting d L N₁ m₁ k N ϱ) (a₁ ν eps : ℝ)
    (H : BgHyp d L (k + 1) ϱ (compWeight L a₁) ν)
    {Θ : RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ)}
    (hΘ : Θ ∈ physSΛ S a₁ ν eps) :
    ∀ᶠ Θ' in 𝓝[((rawSub N S.G' : Set _) ×ˢ (Set.univ : Set _))] Θ, Θ' ∈ physSΛ S a₁ ν eps := by
  obtain ⟨hX, hg⟩ := hΘ
  obtain ⟨D, hD, hDp⟩ := hX
  rw [nhdsWithin_prod_eq]
  have e1 : ∀ᶠ q in 𝓝[(rawSub N S.G' : Set _)] Θ.1, q ∈ XiCRaw S.G' (compWeight L a₁) ν (k + 1) 1 eps := by
    rw [hDp]; exact xiCRaw_eventually H hD
  have e2 : ∀ᶠ g in 𝓝[(Set.univ : Set (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ))] Θ.2,
      g ∈ l1Ball d L N₁ m₁ (k + 1) N :=
    nhdsWithin_le_nhds ((isOpen_l1Ball (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1)
      (N := N)).mem_nhds hg)
  exact e1.prod_mk e2

end Physical

section Witness

open Balaban.Inhabited Balaban.Localization.I5Inhabited

/-- **The landed chart points have a neighbourhood in the chart, relative to the data subspace,
and the chart is not open in `RawData`.**  For the chart `Ξ^c_2` of the generating set `GP` (all of
the torus in layer 2; `d = L = 3`, `N = 2`): a real datum `D` and a nonreal datum `Dn` realize
members of the chart; the chart contains the raw data of `rawSub` in a neighbourhood of each of
them; the subspace is proper and the chart is not open in `RawData`. -/
theorem xiCRaw_witness :
    ∃ (m₁ : ℕ) (t : ℝ) (D Dn : BgData (GP m₁ (rhoSep m₁)) 2), 0 < t ∧ D.IsReal ∧ ¬ Dn.IsReal ∧
      XiCData (GP m₁ (rhoSep m₁)) (compWeight 3 1) 0 2 1 t D ∧
      XiCData (GP m₁ (rhoSep m₁)) (compWeight 3 1) 0 2 1 t Dn ∧
      (∀ᶠ q in 𝓝[(rawSub 2 (GP m₁ (rhoSep m₁)) : Set _)] (rawOf D),
        q ∈ XiCRaw (GP m₁ (rhoSep m₁)) (compWeight 3 1) 0 2 1 t) ∧
      (∀ᶠ q in 𝓝[(rawSub 2 (GP m₁ (rhoSep m₁)) : Set _)] (rawOf Dn),
        q ∈ XiCRaw (GP m₁ (rhoSep m₁)) (compWeight 3 1) 0 2 1 t) ∧
      (∃ q : RawData 3 3 (6 * 3 ^ m₁) 2 2, q ∉ rawSub 2 (GP m₁ (rhoSep m₁))) ∧
      ¬ IsOpen (XiCRaw (N := 2) (GP m₁ (rhoSep m₁)) (compWeight 3 1) 0 2 1 t) := by
  obtain ⟨m₁, c, BG, κ, t, c₂, BG₂, δc, ht0, -⟩ := exists_chart_params
  obtain ⟨Dn, hXn, hDn, hnr⟩ := exists_nonreal_xiCData (bgHyp_rho m₁) (GP m₁ (rhoSep m₁))
    (fun x => (isLevel_GP m₁ x).1) (by norm_num : 1 < 2) (by simp) ht0
  have hX := exists_xiC (bgHyp_rho m₁) (GP m₁ (rhoSep m₁)) hN2 (by simp) ht0
  have hΩ : ∀ x, x ∈ (GP m₁ (rhoSep m₁)).Ω 1 := fun x => (isLevel_GP m₁ x).1
  have hDh : ∀ x i, (witnessD m₁).h x i = (unitVec hN2 i : ℂ) := fun x i =>
    unitBg_h_of_mem (GP m₁ (rhoSep m₁)) hN2 (unitVec hN2) (hΩ x) i
  have hXr : XiCData (GP m₁ (rhoSep m₁)) (compWeight 3 1) 0 2 1 t (witnessD m₁) :=
    ⟨_, _, 0, 0, hX, fun x hx i => by
      rw [show (witnessD m₁).Ψ x i = (unitVec hN2 i : ℂ) from
        unitBg_Ψ_of_mem (GP m₁ (rhoSep m₁)) hN2 (unitVec hN2) hx i]
      simp, fun x hx i => by rw [hDh x i]; simp⟩
  have hreal : (witnessD m₁).IsReal :=
    isReal_of_inDomainR (witnessData_domain (m₁ := m₁) (β := 1) (δ := 1) (δ' := 1) one_pos)
  have hprop : ∃ q : RawData 3 3 (6 * 3 ^ m₁) 2 2, q ∉ rawSub 2 (GP m₁ (rhoSep m₁)) :=
    exists_not_mem_rawSub_of_bgHyp 2 (GP m₁ (rhoSep m₁)) (bgHyp_rho m₁) ⟨0, hΩ 0⟩
  exact ⟨m₁, t, witnessD m₁, Dn, ht0, hreal, hnr, hXr, hXn, xiCRaw_eventually (bgHyp_rho m₁) hXr,
    xiCRaw_eventually (bgHyp_rho m₁) hXn, hprop,
    not_isOpen_xiCRaw 2 _ _ _ _ _ _ hprop ⟨_, _, hXr, rfl⟩⟩

end Witness

end Balaban.Fluctuation
