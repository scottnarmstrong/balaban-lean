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
public import Balaban.Fluctuation.MarkedVRawY
public import Balaban.Fluctuation.RawAgreeSites

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

/-- **The decoupled mark from locality of `evDec`.**  If the coefficient `evDec` of the label `Y`
takes the same value at `(Θ, ψ̂)` and `(Θ', ψ̂)` for every pair of marks of the radius set and every
hat field `ψ̂ = S.hatOf m₀ ρ hp Φ` of a block configuration, then the decoupled marks of `Y` at `Θ`
and `Θ'` coincide.  The agreement relation that gives the hypothesis is not part of the statement. -/
theorem decMarkG_congr_of_evDec {ρ : ℝ} (hp : 0 < S.p₁)
    {En : ((S.G'.Ω 1 × Fin N → ℂ) × (S.G'.Ω 1 → ℂ)) → (Hm.Ω 1 × Fin N → ℂ) →
      RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) → ℂ}
    {Θ Θ' : RawData d L (N₁ * L ^ m₁) (k + 1) N} {um : ℂ}
    (hum : (‖um‖ + ‖(0 : ℂ)‖) * markedRad d L N k a₁ κ cψ cc < δ₁)
    {Y : Set (CTorus d L N₁ m₁ (k + 1))}
    (hloc : ∀ tm : ℂ, (‖um‖ + ‖tm‖) * markedRad d L N k a₁ κ cψ cc < δ₁ →
      ∀ Φ : ∀ b, (S.blockSplit m₀ hp).Ωb b,
        evDec X₁f m₀ j 𝒦X a₁ ν S.hG' cc F₁ Sol En Zm um tm Y (Θ, S.hatOf m₀ ρ hp Φ) =
        evDec X₁f m₀ j 𝒦X a₁ ν S.hG' cc F₁ Sol En Zm um tm Y (Θ', S.hatOf m₀ ρ hp Φ)) :
    decMarkG S X₁f m₀ j 𝒦X a₁ ν cc F₁ Sol En Zm Y ρ hp Θ um =
    decMarkG S X₁f m₀ j 𝒦X a₁ ν cc F₁ Sol En Zm Y ρ hp Θ' um := by
  funext Φ
  unfold decMarkG
  refine Filter.EventuallyEq.deriv_eq ?_
  have hopen : IsOpen {t : ℂ | (‖um‖ + ‖t‖) * markedRad d L N k a₁ κ cψ cc < δ₁} :=
    isOpen_lt (by fun_prop) continuous_const
  filter_upwards [hopen.mem_nhds hum] with t ht
  exact hloc t ht Φ

/-- **The corrected decoupled mark from locality of `evDec`.**  If `evDec` of the label `Y` is
unchanged under `Θ ↦ Θ'` for all marks `(um', tm)` of the radius set with `um'` and `um`, `0` as
first mark, then the corrected decoupled marks of `Y` at `Θ` and `Θ'` coincide. -/
theorem decMarkCorr_congr_of_evDec {ρ : ℝ} (hp : 0 < S.p₁) (hδ : 0 < δ₁)
    {En : ((S.G'.Ω 1 × Fin N → ℂ) × (S.G'.Ω 1 → ℂ)) → (Hm.Ω 1 × Fin N → ℂ) →
      RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) → ℂ}
    {Θ Θ' : RawData d L (N₁ * L ^ m₁) (k + 1) N} {um : ℂ}
    (hum : (‖um‖ + ‖(0 : ℂ)‖) * markedRad d L N k a₁ κ cψ cc < δ₁)
    {Y : Set (CTorus d L N₁ m₁ (k + 1))}
    (hloc : ∀ um' tm : ℂ, (‖um'‖ + ‖tm‖) * markedRad d L N k a₁ κ cψ cc < δ₁ →
      ∀ Φ : ∀ b, (S.blockSplit m₀ hp).Ωb b,
        evDec X₁f m₀ j 𝒦X a₁ ν S.hG' cc F₁ Sol En Zm um' tm Y (Θ, S.hatOf m₀ ρ hp Φ) =
        evDec X₁f m₀ j 𝒦X a₁ ν S.hG' cc F₁ Sol En Zm um' tm Y (Θ', S.hatOf m₀ ρ hp Φ)) :
    decMarkCorr S X₁f m₀ j 𝒦X a₁ ν cc F₁ Sol En Zm Y ρ hp Θ um =
    decMarkCorr S X₁f m₀ j 𝒦X a₁ ν cc F₁ Sol En Zm Y ρ hp Θ' um := by
  funext Φ
  have h0 : (‖(0 : ℂ)‖ + ‖(0 : ℂ)‖) * markedRad d L N k a₁ κ cψ cc < δ₁ := by simpa using hδ
  have hopen : IsOpen {t : ℂ | (‖t‖ + ‖(0 : ℂ)‖) * markedRad d L N k a₁ κ cψ cc < δ₁} :=
    isOpen_lt (by fun_prop) continuous_const
  have e3 : deriv (fun v : ℂ => decMarkG S X₁f m₀ j 𝒦X a₁ ν cc F₁ Sol En Zm Y ρ hp Θ v Φ) 0 =
      deriv (fun v : ℂ => decMarkG S X₁f m₀ j 𝒦X a₁ ν cc F₁ Sol En Zm Y ρ hp Θ' v Φ) 0 := by
    refine Filter.EventuallyEq.deriv_eq ?_
    filter_upwards [hopen.mem_nhds h0] with v hv
    rw [decMarkG_congr_of_evDec S hp hv fun tm ht => hloc v tm ht]
  unfold decMarkCorr
  rw [decMarkG_congr_of_evDec S hp hum fun tm ht => hloc um tm ht,
    decMarkG_congr_of_evDec S hp h0 fun tm ht => hloc 0 tm ht, e3]

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
  refine decMarkG_congr_of_evDec S hp hum fun tm ht Φ => ?_
  exact hP.2.1 um tm ht Y _
    ⟨hΘ, fun p => (S.hatOf_mem m₀ hρ hp Φ p).trans hρc⟩
    _ ⟨hΘ', fun p => (S.hatOf_mem m₀ hρ hp Φ p).trans hρc⟩ ⟨hag, fun _ _ _ => rfl⟩

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
  refine decMarkCorr_congr_of_evDec S hp hδ hum fun um' tm ht Φ => ?_
  exact hP.2.1 um' tm ht Y _
    ⟨hΘ, fun p => (S.hatOf_mem m₀ hρ hp Φ p).trans hρc⟩
    _ ⟨hΘ', fun p => (S.hatOf_mem m₀ hρ hp Φ p).trans hρc⟩ ⟨hag, fun _ _ _ => rfl⟩

end Marks

section Rooted

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ ϱm : ℝ}
  (S : StepSetting d L N₁ m₁ k N ϱ) {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}
variable {a₁ ν BG BG₂ κ eps δ₁ κdec cψ : ℝ} {m₀ : ℕ} {cc : ℂ} {Zm : Finset (unitPts S.G')}
variable {jV : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) → ℕ}
  {XV 𝒦XV : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) → Set (CTorus d L N₁ m₁ (k + 1))}
  {X₁V : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) → Finset (CTorus d L N₁ m₁ (k + 1))}

open Classical in
/-- **The rooted corrected output from locality of `evDec`.**  The rooted output at the bridge label
`Y'` is a finite sum of corrected marks of labels `Y ⊆ Y'` (`subset_bridge`).  If `evDec` of every
label `Y ⊆ Y'` of every block `b` is unchanged under `Θ ↦ Θ'` (all marks of the radius set, all
hat fields of block configurations), the rooted outputs at `Θ` and `Θ'` coincide. -/
theorem markedOutDec_decMarkCorrTerm_congr_of_evDec
    (F₁ : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) →
      DecParams S.G' × RawData d L (N₁ * L ^ m₁) (k + 1) N →
        (S.G'.Ω 1 × Fin N → ℂ) × (S.G'.Ω 1 → ℂ))
    (Sol : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) →
      Dec2.DecParams (coverOf S.G') × Edat Hm N → (Hm.Ω 1 × Fin N → ℂ) × (Hm.Ω 1 → ℂ))
    {ρ : ℝ} (hp : 0 < S.p₁) (hδ : 0 < δ₁) (β : ℂ)
    {Θ Θ' : RawData d L (N₁ * L ^ m₁) (k + 1) N}
    {um : ℂ} (hum : (‖um‖ + ‖(0 : ℂ)‖) * markedRad d L N k a₁ κ cψ cc < δ₁)
    (zr : RootIdx d L N₁ m₁ (k + 1)) (Φ : ∀ b, (S.blockSplit m₀ hp).Ωb b)
    {Y' : Set (CTorus d L N₁ m₁ (k + 1))}
    (hloc : ∀ b, ∀ Y ⊆ Y', ∀ um' tm : ℂ,
      (‖um'‖ + ‖tm‖) * markedRad d L N k a₁ κ cψ cc < δ₁ →
      ∀ Φ : ∀ b, (S.blockSplit m₀ hp).Ωb b,
        evDec (X₁V b) m₀ (jV b) (𝒦XV b) a₁ ν S.hG' cc (F₁ b) (Sol b)
          (blockEnergyFun S.G' Hm (compWeight L a₁) ν k b) Zm um' tm Y (Θ, S.hatOf m₀ ρ hp Φ) =
        evDec (X₁V b) m₀ (jV b) (𝒦XV b) a₁ ν S.hG' cc (F₁ b) (Sol b)
          (blockEnergyFun S.G' Hm (compWeight L a₁) ν k b) Zm um' tm Y
          (Θ', S.hatOf m₀ ρ hp Φ)) :
    markedOutDec m₀ (fun _ => Set.univ) (fun b => polyDom S.G' (X₁V b) m₀ (jV b) (𝒦XV b)) zr
        (decMarkCorrTerm S X₁V jV 𝒦XV m₀ a₁ ν cc F₁ Sol Zm ρ hp β Θ um Φ) Y' =
    markedOutDec m₀ (fun _ => Set.univ) (fun b => polyDom S.G' (X₁V b) m₀ (jV b) (𝒦XV b)) zr
        (decMarkCorrTerm S X₁V jV 𝒦XV m₀ a₁ ν cc F₁ Sol Zm ρ hp β Θ' um Φ) Y' := by
  rw [markedOutDec_decMarkCorrTerm_eq S F₁ Sol ρ hp β Θ um Φ zr Y',
    markedOutDec_decMarkCorrTerm_eq S F₁ Sol ρ hp β Θ' um Φ zr Y']
  refine Finset.sum_congr rfl fun q hq => ?_
  obtain ⟨-, hq2⟩ := Finset.mem_filter.1 hq
  have hsub : q.2 ⊆ Y' := hq2 ▸ subset_bridge zr q.2
  have h := congrFun (decMarkCorr_congr_of_evDec S hp hδ hum
    fun um' tm ht Φ => hloc q.1 q.2 hsub um' tm ht Φ) Φ
  rw [h]

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
  refine markedOutDec_decMarkCorrTerm_congr_of_evDec S F₁ Sol hp hδ β hum zr Φ ?_
  intro b Y hY um' tm ht Φ
  exact hP b |>.2.1 um' tm ht Y _
    ⟨hΘ, fun p => (S.hatOf_mem m₀ hρ hp Φ p).trans hρc⟩
    _ ⟨hΘ', fun p => (S.hatOf_mem m₀ hρ hp Φ p).trans hρc⟩
    ⟨agreeOn_mono (thickSet_mono hY) hag, fun _ _ _ => rfl⟩

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
  (physAgΘThick_of_restrict S (thickSet_mono hY) h).1

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


section MarksSharp

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ ϱm : ℝ}
  (S : StepSetting d L N₁ m₁ k N ϱ) {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}
variable {a₁ ν c BG BG₂ κ eps Kc Cx c₂ δ₁ cψ δc : ℝ} {X₁f : Finset (CTorus d L N₁ m₁ (k + 1))}
variable {m₀ j : ℕ} {X 𝒦X : Set (CTorus d L N₁ m₁ (k + 1))}
variable {cc : ℂ} {Zm : Finset (unitPts S.G')}
  {z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1)))}
variable {F₁ : DecParams S.G' × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      (S.G'.Ω 1 × Fin N → ℂ) × (S.G'.Ω 1 → ℂ)}
variable {Sol : Dec2.DecParams (coverOf S.G') × Edat Hm N → (Hm.Ω 1 × Fin N → ℂ) × (Hm.Ω 1 → ℂ)}
variable
  (hC : FlCore N S.G' Hm a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
  (hk : 1 ≤ k) (hG : IsLevel Hm k) (hcψ : 0 ≤ cψ)
  (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
  (hdm : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
  (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
  (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
  (hconn : HatConn S.G') (hrow : RowInHat (coverOf S.G') Hm (compWeight L a₁) ν)
  (hcov : CovSetup S.G' m₀ j X 𝒦X)
  (hX₁ : (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) = X1 S.G' m₀ j 𝒦X)
  (hF₁ : ∀ (s : DecParams S.G') (D : BgData S.G' N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC S.G' (bgC0 d L N) (c7 d L N BG κ) ν D → ∀ (φ : S.G'.Ω 1 × Fin N → ℂ)
        (α : S.G'.Ω 1 → ℂ), IsDecBg S.G' (compWeight L a₁) ν (rho4 d L N BG κ) s D φ α →
        F₁ (s, rawOf D) = (φ, α))
  (hSol : ∀ p : Dec2.DecParams (coverOf S.G') × Edat Hm N, (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM Hm N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2 →
        (Sol p).1 = dphi Hm (Dec2.decG (coverOf S.G') Hm (compWeight L a₁) ν p.1) p.2.2.1 p.2.1
          (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol p).2 ∧
        Dec2.DecFixed (coverOf S.G') Hm (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
          (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol p).2 ∧
        Small Hm (Sol p).2 (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
        Small Hm (Sol p).2 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        SupBounds Hm (Sol p).1 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        (∀ δα' : Hm.Ω 1 → ℂ, Small Hm δα' (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf S.G') Hm (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
            (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol p).2))
  (hZ : readSites Hm k z ⊆ ↑X₁f)
  (hBM : BlockMargin S.G' X₁f
    (↑(blockSites d L N₁ m₁ (k + 1) k z) : Set (CTorus d L N₁ m₁ (k + 1))))

include hC hk hG hcψ hMX hdm hα hsm hconn hrow hcov hX₁ hF₁ hSol hZ hBM

/-- **Exact raw locality of the decoupled mark.**  Two admissible raw data that agree on `Y` itself
(`agreeOn Y`) give the same decoupled mark of the label `Y`.  The pair `(F₁, Sol)` enters through its
defining properties `hF₁`, `hSol` (`evDec_local_rawY`), not through clause 2 of
`MarkedBlockExpansionDecPair`; the hat fields are equal. -/
theorem decMarkG_rawY_congr {ρ : ℝ} (hρ : 0 < ρ) (hρc : ρ ≤ cψ) (hp : 0 < S.p₁)
    {Θ Θ' : RawData d L (N₁ * L ^ m₁) (k + 1) N}
    (hΘ : Θ ∈ XiCRaw S.G' (compWeight L a₁) ν (k + 1) 1 eps)
    (hΘ' : Θ' ∈ XiCRaw S.G' (compWeight L a₁) ν (k + 1) 1 eps)
    {um : ℂ} (hum : (‖um‖ + ‖(0 : ℂ)‖) * markedRad d L N k a₁ κ cψ cc < δ₁)
    {Y : Set (CTorus d L N₁ m₁ (k + 1))} (hag : agreeOn Y Θ Θ') :
    decMarkG S X₁f m₀ j 𝒦X a₁ ν cc F₁ Sol (blockEnergyFun S.G' Hm (compWeight L a₁) ν k z) Zm
      Y ρ hp Θ um =
    decMarkG S X₁f m₀ j 𝒦X a₁ ν cc F₁ Sol (blockEnergyFun S.G' Hm (compWeight L a₁) ν k z) Zm
      Y ρ hp Θ' um := by
  refine decMarkG_congr_of_evDec S hp hum fun tm ht Φ => ?_
  exact evDec_local_rawY hC hk hG S.hG' cc hcψ Zm um tm hMX hdm hα hsm ht hcov hX₁ hconn hrow
    hF₁ hSol z hZ hBM Y
    ⟨hΘ, fun p => (S.hatOf_mem m₀ hρ hp Φ p).trans hρc⟩
    ⟨hΘ', fun p => (S.hatOf_mem m₀ hρ hp Φ p).trans hρc⟩ hag (fun _ _ _ => rfl)

/-- **Exact raw locality of the corrected decoupled mark.**  The first-order Taylor remainder in the
first mark preserves the agreement of `decMarkG_rawY_congr`. -/
theorem decMarkCorr_rawY_congr {ρ : ℝ} (hρ : 0 < ρ) (hρc : ρ ≤ cψ) (hp : 0 < S.p₁) (hδ : 0 < δ₁)
    {Θ Θ' : RawData d L (N₁ * L ^ m₁) (k + 1) N}
    (hΘ : Θ ∈ XiCRaw S.G' (compWeight L a₁) ν (k + 1) 1 eps)
    (hΘ' : Θ' ∈ XiCRaw S.G' (compWeight L a₁) ν (k + 1) 1 eps)
    {um : ℂ} (hum : (‖um‖ + ‖(0 : ℂ)‖) * markedRad d L N k a₁ κ cψ cc < δ₁)
    {Y : Set (CTorus d L N₁ m₁ (k + 1))} (hag : agreeOn Y Θ Θ') :
    decMarkCorr S X₁f m₀ j 𝒦X a₁ ν cc F₁ Sol (blockEnergyFun S.G' Hm (compWeight L a₁) ν k z)
        Zm Y ρ hp Θ um =
    decMarkCorr S X₁f m₀ j 𝒦X a₁ ν cc F₁ Sol (blockEnergyFun S.G' Hm (compWeight L a₁) ν k z)
        Zm Y ρ hp Θ' um := by
  refine decMarkCorr_congr_of_evDec S hp hδ hum fun um' tm ht Φ => ?_
  exact evDec_local_rawY hC hk hG S.hG' cc hcψ Zm um' tm hMX hdm hα hsm ht hcov hX₁ hconn hrow
    hF₁ hSol z hZ hBM Y
    ⟨hΘ, fun p => (S.hatOf_mem m₀ hρ hp Φ p).trans hρc⟩
    ⟨hΘ', fun p => (S.hatOf_mem m₀ hρ hp Φ p).trans hρc⟩ hag (fun _ _ _ => rfl)

end MarksSharp

section RootedSharp

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ ϱm : ℝ}
  (S : StepSetting d L N₁ m₁ k N ϱ) {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}
variable {a₁ ν c BG BG₂ κ eps Kc Cx c₂ δ₁ cψ δc : ℝ} {m₀ : ℕ} {cc : ℂ}
  {Zm : Finset (unitPts S.G')}
variable {jV : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) → ℕ}
  {XV 𝒦XV : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) → Set (CTorus d L N₁ m₁ (k + 1))}
  {X₁V : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) → Finset (CTorus d L N₁ m₁ (k + 1))}
variable
  (hC : FlCore N S.G' Hm a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
  (hk : 1 ≤ k) (hG : IsLevel Hm k) (hcψ : 0 ≤ cψ)
  (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
  (hdm : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
  (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
  (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
  (hconn : HatConn S.G') (hrow : RowInHat (coverOf S.G') Hm (compWeight L a₁) ν)
  (F₁ : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) →
      DecParams S.G' × RawData d L (N₁ * L ^ m₁) (k + 1) N →
        (S.G'.Ω 1 × Fin N → ℂ) × (S.G'.Ω 1 → ℂ))
  (Sol : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) →
      Dec2.DecParams (coverOf S.G') × Edat Hm N → (Hm.Ω 1 × Fin N → ℂ) × (Hm.Ω 1 → ℂ))
  (hcov : ∀ b, CovSetup S.G' m₀ (jV b) (XV b) (𝒦XV b))
  (hX₁ : ∀ b, (↑(X₁V b) : Set (CTorus d L N₁ m₁ (k + 1))) = X1 S.G' m₀ (jV b) (𝒦XV b))
  (hF₁ : ∀ b, ∀ (s : DecParams S.G') (D : BgData S.G' N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC S.G' (bgC0 d L N) (c7 d L N BG κ) ν D → ∀ (φ : S.G'.Ω 1 × Fin N → ℂ)
        (α : S.G'.Ω 1 → ℂ), IsDecBg S.G' (compWeight L a₁) ν (rho4 d L N BG κ) s D φ α →
        F₁ b (s, rawOf D) = (φ, α))
  (hSol : ∀ b, ∀ p : Dec2.DecParams (coverOf S.G') × Edat Hm N,
      (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM Hm N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2 →
        (Sol b p).1 = dphi Hm (Dec2.decG (coverOf S.G') Hm (compWeight L a₁) ν p.1) p.2.2.1 p.2.1
          (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol b p).2 ∧
        Dec2.DecFixed (coverOf S.G') Hm (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
          (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol b p).2 ∧
        Small Hm (Sol b p).2 (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
        Small Hm (Sol b p).2 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        SupBounds Hm (Sol b p).1 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        (∀ δα' : Hm.Ω 1 → ℂ, Small Hm δα' (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf S.G') Hm (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
            (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol b p).2))
  (hZ : ∀ b, readSites Hm k b ⊆ ↑(X₁V b))
  (hBM : ∀ b, BlockMargin S.G' (X₁V b)
    (↑(blockSites d L N₁ m₁ (k + 1) k b) : Set (CTorus d L N₁ m₁ (k + 1))))

include hC hk hG hcψ hMX hdm hα hsm hconn hrow hcov hX₁ hF₁ hSol hZ hBM

open Classical in
/-- **Exact raw locality of the rooted corrected output.**  For admissible raw data `Θ, Θ'` that
agree on the bridge label `Y'` itself (`agreeOn Y'`), the rooted output of the corrected marks at
`Y'` is the same: it is a finite sum of corrected marks of labels `Y ⊆ Y'`, and `evDec_local_rawY`
applies to each, since `agreeOn Y'` restricts to `agreeOn Y`. -/
theorem markedOutDec_decMarkCorrTerm_rawY_congr {ρ : ℝ} (hρ : 0 < ρ) (hρc : ρ ≤ cψ)
    (hp : 0 < S.p₁) (hδ : 0 < δ₁) (β : ℂ)
    {Θ Θ' : RawData d L (N₁ * L ^ m₁) (k + 1) N}
    (hΘ : Θ ∈ XiCRaw S.G' (compWeight L a₁) ν (k + 1) 1 eps)
    (hΘ' : Θ' ∈ XiCRaw S.G' (compWeight L a₁) ν (k + 1) 1 eps)
    {um : ℂ} (hum : (‖um‖ + ‖(0 : ℂ)‖) * markedRad d L N k a₁ κ cψ cc < δ₁)
    (zr : RootIdx d L N₁ m₁ (k + 1)) (Φ : ∀ b, (S.blockSplit m₀ hp).Ωb b)
    {Y' : Set (CTorus d L N₁ m₁ (k + 1))} (hag : agreeOn Y' Θ Θ') :
    markedOutDec m₀ (fun _ => Set.univ) (fun b => polyDom S.G' (X₁V b) m₀ (jV b) (𝒦XV b)) zr
        (decMarkCorrTerm S X₁V jV 𝒦XV m₀ a₁ ν cc F₁ Sol Zm ρ hp β Θ um Φ) Y' =
    markedOutDec m₀ (fun _ => Set.univ) (fun b => polyDom S.G' (X₁V b) m₀ (jV b) (𝒦XV b)) zr
        (decMarkCorrTerm S X₁V jV 𝒦XV m₀ a₁ ν cc F₁ Sol Zm ρ hp β Θ' um Φ) Y' := by
  refine markedOutDec_decMarkCorrTerm_congr_of_evDec S F₁ Sol hp hδ β hum zr Φ ?_
  intro b Y hY um' tm ht Φ
  exact evDec_local_rawY hC hk hG S.hG' cc hcψ Zm um' tm hMX hdm hα hsm ht (hcov b) (hX₁ b)
    hconn hrow (hF₁ b) (hSol b) b (hZ b) (hBM b) Y
    ⟨hΘ, fun p => (S.hatOf_mem m₀ hρ hp Φ p).trans hρc⟩
    ⟨hΘ', fun p => (S.hatOf_mem m₀ hρ hp Φ p).trans hρc⟩ (agreeOn_mono hY hag)
    (fun _ _ _ => rfl)

open Classical in
/-- **The premise `hG` of `paramMarked_analytic_local_bound`, exact form.**  The marks are the
rooted outputs of `markedOutDec_decMarkCorrTerm_hG`, for the restriction map
`π θ = physRestrict (sitesOf T) (physIncl N S θ)`.  Equal `π` gives agreement of the raw data on
`sitesOf T` (`physRestrict_physIncl_eq_iff`), hence on every anchor whose site set lies in
`Ŷ(sitesOf T) = sitesOf T` (`Yhat_univ`). -/
theorem markedOutDec_decMarkCorrTerm_hG_rawY {Lb : Type*}
    (Lab : CubeLabels (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) m₀ (k + 1)
      Set.univ Lb) (hN : L ^ m₀ ∣ N₁) (hL : 2 ≤ L)
    (hdomR : ∀ b : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))), ∀ Y ∈ polyDom S.G' (X₁V b) m₀
      (jV b) (𝒦XV b), IsDj m₀ (k + 1) Y)
    {ρ : ℝ} (hρ : 0 < ρ) (hρc : ρ ≤ cψ) (hp : 0 < S.p₁) (hδ : 0 < δ₁) (β : ℂ) (U : ℝ)
    (hum : ∀ u : ℂ, ‖u‖ < U → (‖u‖ + ‖(0 : ℂ)‖) * markedRad d L N k a₁ κ cψ cc < δ₁)
    (zr : RootIdx d L N₁ m₁ (k + 1))
    (T : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) m₀ (k + 1)
      Set.univ)) :
    ∀ θ ∈ physV S a₁ ν eps, ∀ θ' ∈ physV S a₁ ν eps,
      physRestrict (N := N) (sitesOf T) (physIncl N S θ) =
        physRestrict (sitesOf T) (physIncl N S θ') →
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
  have hagT := ((physRestrict_physIncl_eq_iff S (sitesOf T) θ θ').1 hπθ).1
  rw [Yhat_univ] at hi
  split_ifs with h1 h2 h2
  · exact markedOutDec_decMarkCorrTerm_rawY_congr S hC hk hG hcψ hMX hdm hα hsm hconn hrow F₁ Sol
      hcov hX₁ hF₁ hSol hZ hBM hρ hρc hp hδ β hθ.1 hθ'.1 (hum _ h1.2) zr Φ (agreeOn_mono hi hagT)
  · exact absurd ⟨hθ', h1.2⟩ h2
  · exact absurd ⟨hθ, h2.2⟩ h1
  · rfl

end RootedSharp

end Balaban.Inhabited
