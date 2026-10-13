/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.ObsSourceLocal
public import Balaban.Inhabited.ActivityFamilyAnalytic
public import Balaban.Fluctuation.MarkedCommonLabels
public import Balaban.Fluctuation.ParamCarrierLocal
public import Balaban.Fluctuation.ParamActivityPhysical
public import Balaban.Fluctuation.DecMarkCorrCount
public import Balaban.Inhabited.DecMarkCorrFamilyFromTower

/-!
# Locality of the energy activity and marks in the raw datum

The energy coefficients of the renormalization step are indexed by finite sets `T` of cubes.  The
coefficient at `T` should depend on the raw datum only through its restriction to a neighbourhood
of `T`.  `paramMarked_analytic_local_bound` derives this from two agreement premises, one for the
label activities and one for the marks.  This file proves both premises.

* `commonAct_zeroSourceAct_H_local_raw`: the zero-source activity on the common labels.  The
  activity of a label `inl z` of the family `labelActFamilyOn` reads the raw datum only on
  `thickSet z.1`; the labels `inr _` added by the roots have zero activity and read nothing.
* `decMarkG_raw_congr`, `decMarkCorr_raw_congr`: the decoupled and the corrected marks of a label
  `Y` read the raw datum only on `thickSet Y`.
* `markedOutDec_decMarkCorrTerm_raw_congr`: the rooted corrected output at a bridge label `Y'`
  reads the raw datum only on `thickSet Y'`.
* `commonAct_zeroSourceAct_hA`, `markedOutDec_decMarkCorrTerm_hG`: the two premises of
  `paramMarked_analytic_local_bound` for a restriction map `π` that determines the raw datum on
  the thickening of every set inside the enlarged region.
* `physRestrict_thickSet_agree`: the map `θ ↦ physRestrict (thickSet Ẑ) (physIncl θ)` has this
  property.
-/

@[expose] public section

namespace Balaban.Inhabited

open MeasureTheory Metric Balaban Balaban.Fluctuation Balaban.Localization Balaban.Polymer
  Balaban.SmallField Balaban.Multiscale Balaban.Background Balaban.Analysis

section Activity

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}
  (S : StepSetting d L N₁ m₁ k N ϱ) (m₀ : ℕ) {F' : Type} {hp : 0 < S.p₁}
  {emb : (S.U × Fin N → ℂ) → F'} {ρ Rσ εU a a₁ ν eps q : ℝ}
  {Θ₀ : RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ)}
  {SΛ : Set (RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ))}
  {XW : Set (F' × F')}
  {val : F' → F' → ℂ → RawData d L (N₁ * L ^ m₁) (k + 1) N ×
    (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) → ℂ}
  {AgF : Set (CTorus d L N₁ m₁ (k + 1)) → F' → F' → Prop}
  (c : ℂ)
  {I : DirectTerms S m₀ hp emb ρ Rσ εU a Θ₀ SΛ XW val (physAgΘ S) AgF}
  (hF : DirectTermsFamilyOn S m₀ (physInclScaled N S c) I (physVq S a₁ ν eps q))
  (hN : L ^ m₀ ∣ N₁) (hρ : 0 < ρ) (hRσ : 0 ≤ Rσ) (hεU : 0 ≤ εU)
  {κ0 Kc : ℝ} (hκ0 : aEnt d L + 1 ≤ κ0) (hKc : K0 d L κ0 ≤ Kc)

/-- Dropping the source of an admissible parameter keeps it admissible, for a positive source
radius `q`. -/
theorem zeroSource_mem_physVq (hq : 0 < q) {θ : physParam N S}
    (hθ : θ ∈ physV S a₁ ν eps) :
    ((θ.1, 0) : physParam N S) ∈ physVq S a₁ ν eps q := by
  refine ⟨⟨hθ.1, ?_⟩, ?_⟩
  · show (0 : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) ∈ l1Ball d L N₁ m₁ (k + 1) N
    simp [l1Ball]
  · simpa using hq

variable {β : Type*} [Fintype β]
  (reads : β → Set (CTorus d L N₁ m₁ (k + 1)))
  (dom : β → Finset (Set (CTorus d L N₁ m₁ (k + 1))))
  (hdom : ∀ b, ∀ Y ∈ dom b, IsDj m₀ (k + 1) Y) (hL : 2 ≤ L)
  (hεH : 0 ≤ (2 : ℝ) ^ 2 * (Rσ * εU)) (hκ0' : aEnt d L + 2 ≤ κ0)

/-- **Raw locality of the zero-source activity on the common labels.**  Let `A0` be the extension by
zero to the labels of the roots of the zero-source family `u ↦ u² A((θ.1, 0), u)` built from
`labelActFamilyOn`.  For admissible `θ, θ'` whose raw data agree on `thickSet z.1`, the activities
of the label `inl z` of the family agree, for every `u`; the labels `inr _` of the roots have
activity `0` at every parameter. -/
theorem commonAct_zeroSourceAct_H_local_raw (hq : 0 < q)
    {θ θ' : physParam N S} (hθ : θ ∈ physV S a₁ ν eps) (hθ' : θ' ∈ physV S a₁ ν eps) (u : ℂ)
    (y : {Y // Y ∈ I.𝒴} ⊕ RootUnionLb m₀ reads dom)
    (hy : ∀ z : {Y // Y ∈ I.𝒴}, y = Sum.inl z →
      agreeOn (thickSet S.G' z.1) (θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N)
        (θ'.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N)) :
    (commonAct (zeroSourceAct
      (labelActFamilyOn S m₀ (physInclScaled N S c) I hF hN hρ hRσ hεU hκ0 hKc) 2 zero_le_two)
      hN hL reads dom hdom hεH hκ0' θ u).H y =
    (commonAct (zeroSourceAct
      (labelActFamilyOn S m₀ (physInclScaled N S c) I hF hN hρ hRσ hεU hκ0 hKc) 2 zero_le_two)
      hN hL reads dom hdom hεH hκ0' θ' u).H y := by
  rcases y with z | z
  · have hz := hy z rfl
    have h := labelActFamilyOn_local_scaled S m₀ c hF hN hρ hRσ hεU hκ0 hKc
      (zeroSource_mem_physVq S hq hθ) (zeroSource_mem_physVq S hq hθ') z hz
      (fun _ _ => rfl) u
    rw [commonAct_H_inl, commonAct_H_inl]
    funext Φ
    simp only [zeroSourceAct_H]
    rw [h]
  · funext Φ
    rw [commonAct_H_inr, commonAct_H_inr]

end Activity

section Marks

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ ϱm : ℝ}
  (S : StepSetting d L N₁ m₁ k N ϱ) {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}
variable {a₁ ν BG BG₂ κ eps δ₁ κdec cψ : ℝ} {X₁f : Finset (CTorus d L N₁ m₁ (k + 1))}
variable {m₀ j : ℕ} {𝒦X : Set (CTorus d L N₁ m₁ (k + 1))}
variable {cc : ℂ} {Zm : Finset (unitPts S.G')}
  {z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1)))}
variable {F₁ : DecParams S.G' × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      (S.G'.Ω 1 × Fin N → ℂ) × (S.G'.Ω 1 → ℂ)}
variable {Sol : Dec2.DecParams (coverOf S.G') × Edat Hm N → (Hm.Ω 1 × Fin N → ℂ) × (Hm.Ω 1 → ℂ)}

/-- **Raw locality of the decoupled mark.**  Two admissible raw data that agree on `thickSet Y`
give the same decoupled mark of the label `Y` (clause 2 of the pair, `AgHatDir`, with equal hat
fields). -/
theorem decMarkG_raw_congr
    (hP : MarkedBlockExpansionDecPair N Hm S.hG' cc a₁ ν BG BG₂ κ eps δ₁ κdec cψ Zm X₁f m₀ j 𝒦X z
      F₁ Sol)
    {ρ : ℝ} (hρ : 0 < ρ) (hρc : ρ ≤ cψ) (hp : 0 < S.p₁)
    {Θ Θ' : RawData d L (N₁ * L ^ m₁) (k + 1) N}
    (hΘ : Θ ∈ XiCRaw S.G' (compWeight L a₁) ν (k + 1) 1 eps)
    (hΘ' : Θ' ∈ XiCRaw S.G' (compWeight L a₁) ν (k + 1) 1 eps)
    {um : ℂ} (hum : (‖um‖ + ‖(0 : ℂ)‖) * markedRad d L N k a₁ κ cψ cc < δ₁)
    {Y : Set (CTorus d L N₁ m₁ (k + 1))} (hag : agreeOn (thickSet S.G' Y) Θ Θ') :
    decMarkG S X₁f m₀ j 𝒦X a₁ ν cc F₁ Sol (blockEnergyFun S.G' Hm (compWeight L a₁) ν k z) Zm
      Y ρ hp Θ um =
    decMarkG S X₁f m₀ j 𝒦X a₁ ν cc F₁ Sol (blockEnergyFun S.G' Hm (compWeight L a₁) ν k z) Zm
      Y ρ hp Θ' um := by
  funext Φ
  exact deriv_evDec_congr hP hum Y
    ⟨hΘ, fun p => (S.hatOf_mem m₀ hρ hp Φ p).trans hρc⟩
    ⟨hΘ', fun p => (S.hatOf_mem m₀ hρ hp Φ p).trans hρc⟩ ⟨hag, fun _ _ _ => rfl⟩

/-- **Raw locality of the corrected decoupled mark.**  The first-order Taylor remainder in the
first mark preserves the agreement of `decMarkG_raw_congr`. -/
theorem decMarkCorr_raw_congr
    (hP : MarkedBlockExpansionDecPair N Hm S.hG' cc a₁ ν BG BG₂ κ eps δ₁ κdec cψ Zm X₁f m₀ j 𝒦X z
      F₁ Sol)
    {ρ : ℝ} (hρ : 0 < ρ) (hρc : ρ ≤ cψ) (hp : 0 < S.p₁) (hδ : 0 < δ₁)
    {Θ Θ' : RawData d L (N₁ * L ^ m₁) (k + 1) N}
    (hΘ : Θ ∈ XiCRaw S.G' (compWeight L a₁) ν (k + 1) 1 eps)
    (hΘ' : Θ' ∈ XiCRaw S.G' (compWeight L a₁) ν (k + 1) 1 eps)
    {um : ℂ} (hum : (‖um‖ + ‖(0 : ℂ)‖) * markedRad d L N k a₁ κ cψ cc < δ₁)
    {Y : Set (CTorus d L N₁ m₁ (k + 1))} (hag : agreeOn (thickSet S.G' Y) Θ Θ') :
    decMarkCorr S X₁f m₀ j 𝒦X a₁ ν cc F₁ Sol (blockEnergyFun S.G' Hm (compWeight L a₁) ν k z)
        Zm Y ρ hp Θ um =
    decMarkCorr S X₁f m₀ j 𝒦X a₁ ν cc F₁ Sol (blockEnergyFun S.G' Hm (compWeight L a₁) ν k z)
        Zm Y ρ hp Θ' um := by
  funext Φ
  have h0 : (‖(0 : ℂ)‖ + ‖(0 : ℂ)‖) * markedRad d L N k a₁ κ cψ cc < δ₁ := by simpa using hδ
  have hopen : IsOpen {t : ℂ | (‖t‖ + ‖(0 : ℂ)‖) * markedRad d L N k a₁ κ cψ cc < δ₁} :=
    isOpen_lt (by fun_prop) continuous_const
  have e3 : deriv (fun v : ℂ => decMarkG S X₁f m₀ j 𝒦X a₁ ν cc F₁ Sol
      (blockEnergyFun S.G' Hm (compWeight L a₁) ν k z) Zm Y ρ hp Θ v Φ) 0 =
      deriv (fun v : ℂ => decMarkG S X₁f m₀ j 𝒦X a₁ ν cc F₁ Sol
      (blockEnergyFun S.G' Hm (compWeight L a₁) ν k z) Zm Y ρ hp Θ' v Φ) 0 := by
    refine Filter.EventuallyEq.deriv_eq ?_
    filter_upwards [hopen.mem_nhds h0] with v hv
    rw [decMarkG_raw_congr S hP hρ hρc hp hΘ hΘ' hv hag]
  unfold decMarkCorr
  rw [decMarkG_raw_congr S hP hρ hρc hp hΘ hΘ' hum hag,
    decMarkG_raw_congr S hP hρ hρc hp hΘ hΘ' h0 hag, e3]

end Marks

section Rooted

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ ϱm : ℝ}
  (S : StepSetting d L N₁ m₁ k N ϱ) {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}
variable {a₁ ν BG BG₂ κ eps δ₁ κdec cψ : ℝ} {m₀ : ℕ} {cc : ℂ} {Zm : Finset (unitPts S.G')}
variable {jV : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) → ℕ}
  {XV 𝒦XV : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) → Set (CTorus d L N₁ m₁ (k + 1))}
  {X₁V : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) → Finset (CTorus d L N₁ m₁ (k + 1))}

open Classical in
/-- **Raw locality of the rooted corrected output.**  For admissible raw data `Θ, Θ'` that agree on
`thickSet Y'`, the rooted output of the corrected marks at the bridge label `Y'` is the same: it is
a finite sum of corrected marks of labels `Y ⊆ Y'` (`subset_bridge`), each of which reads the raw
datum on `thickSet Y ⊆ thickSet Y'`. -/
theorem markedOutDec_decMarkCorrTerm_raw_congr
    (F₁ : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) →
      DecParams S.G' × RawData d L (N₁ * L ^ m₁) (k + 1) N →
        (S.G'.Ω 1 × Fin N → ℂ) × (S.G'.Ω 1 → ℂ))
    (Sol : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) →
      Dec2.DecParams (coverOf S.G') × Edat Hm N → (Hm.Ω 1 × Fin N → ℂ) × (Hm.Ω 1 → ℂ))
    (hP : ∀ b, MarkedBlockExpansionDecPair N Hm S.hG' cc a₁ ν BG BG₂ κ eps δ₁ κdec cψ Zm (X₁V b)
      m₀ (jV b) (𝒦XV b) b (F₁ b) (Sol b))
    {ρ : ℝ} (hρ : 0 < ρ) (hρc : ρ ≤ cψ) (hp : 0 < S.p₁) (hδ : 0 < δ₁) (β : ℂ)
    {Θ Θ' : RawData d L (N₁ * L ^ m₁) (k + 1) N}
    (hΘ : Θ ∈ XiCRaw S.G' (compWeight L a₁) ν (k + 1) 1 eps)
    (hΘ' : Θ' ∈ XiCRaw S.G' (compWeight L a₁) ν (k + 1) 1 eps)
    {um : ℂ} (hum : (‖um‖ + ‖(0 : ℂ)‖) * markedRad d L N k a₁ κ cψ cc < δ₁)
    (zr : RootIdx d L N₁ m₁ (k + 1)) (Φ : ∀ b, (S.blockSplit m₀ hp).Ωb b)
    {Y' : Set (CTorus d L N₁ m₁ (k + 1))} (hag : agreeOn (thickSet S.G' Y') Θ Θ') :
    markedOutDec m₀ (fun _ => Set.univ) (fun b => polyDom S.G' (X₁V b) m₀ (jV b) (𝒦XV b)) zr
        (decMarkCorrTerm S X₁V jV 𝒦XV m₀ a₁ ν cc F₁ Sol Zm ρ hp β Θ um Φ) Y' =
    markedOutDec m₀ (fun _ => Set.univ) (fun b => polyDom S.G' (X₁V b) m₀ (jV b) (𝒦XV b)) zr
        (decMarkCorrTerm S X₁V jV 𝒦XV m₀ a₁ ν cc F₁ Sol Zm ρ hp β Θ' um Φ) Y' := by
  rw [markedOutDec_decMarkCorrTerm_eq S F₁ Sol ρ hp β Θ um Φ zr Y',
    markedOutDec_decMarkCorrTerm_eq S F₁ Sol ρ hp β Θ' um Φ zr Y']
  refine Finset.sum_congr rfl fun q hq => ?_
  obtain ⟨-, hq2⟩ := Finset.mem_filter.1 hq
  have hsub : q.2 ⊆ Y' := hq2 ▸ subset_bridge zr q.2
  have h := congrFun (decMarkCorr_raw_congr S (hP q.1) hρ hρc hp hδ hΘ hΘ' hum
    (agreeOn_mono (thickSet_mono hsub) hag)) Φ
  rw [h]

end Rooted

section Premises

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ ϱm : ℝ}
  (S : StepSetting d L N₁ m₁ k N ϱ)

/-- **A restriction map that determines the thickenings.**  For a set `Z` of sites, two parameters
whose data restricted to `thickSet S.G' Z` coincide (`physRestrict`, raw datum and source) have raw
data agreeing on `thickSet S.G' Y` for every `Y ⊆ Z`. -/
theorem physRestrict_thickSet_agree (Z : Set (CTorus d L N₁ m₁ (k + 1))) {θ θ' : physParam N S}
    (h : physRestrict (N := N) (thickSet S.G' Z) (physIncl N S θ) =
      physRestrict (thickSet S.G' Z) (physIncl N S θ'))
    {Y : Set (CTorus d L N₁ m₁ (k + 1))} (hY : Y ⊆ Z) :
    agreeOn (thickSet S.G' Y) (θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N)
      (θ'.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) :=
  (physAgΘ_of_restrict S (thickSet_mono hY) h).1

variable (m₀ : ℕ) {F' : Type} {hp : 0 < S.p₁}
  {emb : (S.U × Fin N → ℂ) → F'} {ρ Rσ εU a a₁ ν eps q : ℝ}
  {Θ₀ : RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ)}
  {SΛ : Set (RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ))}
  {XW : Set (F' × F')}
  {val : F' → F' → ℂ → RawData d L (N₁ * L ^ m₁) (k + 1) N ×
    (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) → ℂ}
  {AgF : Set (CTorus d L N₁ m₁ (k + 1)) → F' → F' → Prop}
  (c : ℂ)
  {I : DirectTerms S m₀ hp emb ρ Rσ εU a Θ₀ SΛ XW val (physAgΘ S) AgF}
  (hF : DirectTermsFamilyOn S m₀ (physInclScaled N S c) I (physVq S a₁ ν eps q))
  (hN : L ^ m₀ ∣ N₁) (hρ : 0 < ρ) (hRσ : 0 ≤ Rσ) (hεU : 0 ≤ εU)
  {κ0 Kc : ℝ} (hκ0 : aEnt d L + 1 ≤ κ0) (hKc : K0 d L κ0 ≤ Kc)
  {β : Type*} [Fintype β]
  (reads : β → Set (CTorus d L N₁ m₁ (k + 1)))
  (dom : β → Finset (Set (CTorus d L N₁ m₁ (k + 1))))
  (hdom : ∀ b, ∀ Y ∈ dom b, IsDj m₀ (k + 1) Y) (hL : 2 ≤ L)
  (hεH : 0 ≤ (2 : ℝ) ^ 2 * (Rσ * εU)) (hκ0' : aEnt d L + 2 ≤ κ0)

/-- **The premise `hA` of `paramMarked_analytic_local_bound`** for the zero-source activity on the
common labels.  Let `π` be a restriction map such that `π θ = π θ'` forces raw agreement on the
thickening of every set inside `Ŷ(sitesOf T)`.  Then the label activities at `θ, θ' ∈ physV` agree
on every label whose sites lie in `Ŷ(sitesOf T)`. -/
theorem commonAct_zeroSourceAct_hA (hq : 0 < q) {P : Type*} (π : physParam N S → P)
    (T : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) m₀ (k + 1)
      Set.univ))
    (hπ : ∀ θ ∈ physV S a₁ ν eps, ∀ θ' ∈ physV S a₁ ν eps, π θ = π θ' →
      ∀ Y ⊆ Yhat Set.univ (sitesOf T),
        agreeOn (thickSet S.G' Y) (θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N)
          (θ'.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N)) :
    ∀ θ ∈ physV S a₁ ν eps, ∀ θ' ∈ physV S a₁ ν eps, π θ = π θ' →
      ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 →
      ∀ y, (commonLabels (thickLabels I.𝒴 I.dom) hN hL reads dom hdom).ysite y ⊆
          Yhat Set.univ (sitesOf T) →
        (commonAct (zeroSourceAct
          (labelActFamilyOn S m₀ (physInclScaled N S c) I hF hN hρ hRσ hεU hκ0 hKc) 2
          zero_le_two) hN hL reads dom hdom hεH hκ0' θ (s : ℂ)).H y =
        (commonAct (zeroSourceAct
          (labelActFamilyOn S m₀ (physInclScaled N S c) I hF hN hρ hRσ hεU hκ0 hKc) 2
          zero_le_two) hN hL reads dom hdom hεH hκ0' θ' (s : ℂ)).H y := by
  intro θ hθ θ' hθ' hπθ s _ y hy
  refine commonAct_zeroSourceAct_H_local_raw S m₀ c hF hN hρ hRσ hεU hκ0 hKc reads dom hdom hL
    hεH hκ0' hq hθ hθ' _ y ?_
  rintro z rfl
  exact hπ θ hθ θ' hθ' hπθ z.1 hy

end Premises

section MarkPremise

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ ϱm : ℝ}
  (S : StepSetting d L N₁ m₁ k N ϱ) {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}
variable {a₁ ν BG BG₂ κ eps δ₁ κdec cψ : ℝ} {m₀ : ℕ} {cc : ℂ} {Zm : Finset (unitPts S.G')}
variable {jV : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) → ℕ}
  {XV 𝒦XV : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) → Set (CTorus d L N₁ m₁ (k + 1))}
  {X₁V : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) → Finset (CTorus d L N₁ m₁ (k + 1))}

open Classical in
/-- **The premise `hG` of `paramMarked_analytic_local_bound`** for the rooted corrected marks.  The
marks are the rooted outputs `markedOutDec … (decMarkCorrTerm … Θ u Φ) Y'` at the raw datum
`Θ = θ.1` of the parameter, cut off outside `physV` and outside `‖u‖ < U`.  For `π` as in
`commonAct_zeroSourceAct_hA`, the marks at `θ, θ' ∈ physV` with `π θ = π θ'` agree for every real
`s ∈ [0, 1]` and every anchor whose site set lies in `Ŷ(sitesOf T)`. -/
theorem markedOutDec_decMarkCorrTerm_hG {Lb : Type*}
    (Lab : CubeLabels (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) m₀ (k + 1)
      Set.univ Lb) (hN : L ^ m₀ ∣ N₁) (hL : 2 ≤ L)
    (hdomR : ∀ b : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))), ∀ Y ∈ polyDom S.G' (X₁V b) m₀
      (jV b) (𝒦XV b), IsDj m₀ (k + 1) Y)
    (F₁ : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) →
      DecParams S.G' × RawData d L (N₁ * L ^ m₁) (k + 1) N →
        (S.G'.Ω 1 × Fin N → ℂ) × (S.G'.Ω 1 → ℂ))
    (Sol : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) →
      Dec2.DecParams (coverOf S.G') × Edat Hm N → (Hm.Ω 1 × Fin N → ℂ) × (Hm.Ω 1 → ℂ))
    (hP : ∀ b, MarkedBlockExpansionDecPair N Hm S.hG' cc a₁ ν BG BG₂ κ eps δ₁ κdec cψ Zm (X₁V b)
      m₀ (jV b) (𝒦XV b) b (F₁ b) (Sol b))
    {ρ : ℝ} (hρ : 0 < ρ) (hρc : ρ ≤ cψ) (hp : 0 < S.p₁) (hδ : 0 < δ₁) (β : ℂ) (U : ℝ)
    (hum : ∀ u : ℂ, ‖u‖ < U → (‖u‖ + ‖(0 : ℂ)‖) * markedRad d L N k a₁ κ cψ cc < δ₁)
    (zr : RootIdx d L N₁ m₁ (k + 1)) {P : Type*} (π : physParam N S → P)
    (T : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) m₀ (k + 1)
      Set.univ))
    (hπ : ∀ θ ∈ physV S a₁ ν eps, ∀ θ' ∈ physV S a₁ ν eps, π θ = π θ' →
      ∀ Y ⊆ Yhat Set.univ (sitesOf T),
        agreeOn (thickSet S.G' Y) (θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N)
          (θ'.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N)) :
    ∀ θ ∈ physV S a₁ ν eps, ∀ θ' ∈ physV S a₁ ν eps, π θ = π θ' →
      ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 →
      ∀ i : {Y' // Y' ∈ bridgeFamily m₀ (fun _ => Set.univ)
          (fun b => polyDom S.G' (X₁V b) m₀ (jV b) (𝒦XV b)) zr},
        (commonLabels Lab hN hL (fun _ => Set.univ)
          (fun b => polyDom S.G' (X₁V b) m₀ (jV b) (𝒦XV b)) hdomR).ysite
          (commonAnchor Lb (fun _ => Set.univ)
            (fun b => polyDom S.G' (X₁V b) m₀ (jV b) (𝒦XV b)) zr i) ⊆
          Yhat Set.univ (sitesOf T) →
        (fun Φ => if θ ∈ physV S a₁ ν eps ∧ ‖(s : ℂ)‖ < U then
          markedOutDec m₀ (fun _ => Set.univ)
            (fun b => polyDom S.G' (X₁V b) m₀ (jV b) (𝒦XV b)) zr
            (decMarkCorrTerm S X₁V jV 𝒦XV m₀ a₁ ν cc F₁ Sol Zm ρ hp β
              (θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) (s : ℂ) Φ) i.1 else 0) =
        (fun Φ => if θ' ∈ physV S a₁ ν eps ∧ ‖(s : ℂ)‖ < U then
          markedOutDec m₀ (fun _ => Set.univ)
            (fun b => polyDom S.G' (X₁V b) m₀ (jV b) (𝒦XV b)) zr
            (decMarkCorrTerm S X₁V jV 𝒦XV m₀ a₁ ν cc F₁ Sol Zm ρ hp β
              (θ'.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) (s : ℂ) Φ) i.1 else 0) := by
  intro θ hθ θ' hθ' hπθ s _ i hi
  funext Φ
  split_ifs with h1 h2 h2
  · exact markedOutDec_decMarkCorrTerm_raw_congr S F₁ Sol hP hρ hρc hp hδ β hθ.1 hθ'.1
      (hum _ h1.2) zr Φ (hπ θ hθ θ' hθ' hπθ _ hi)
  · exact absurd ⟨hθ', h1.2⟩ h2
  · exact absurd ⟨hθ, h2.2⟩ h1
  · rfl

end MarkPremise

end Balaban.Inhabited
