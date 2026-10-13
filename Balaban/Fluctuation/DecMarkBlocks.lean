/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.MarkedEvJoint
public import Balaban.Fluctuation.HatLabelsDirect
public import Balaban.Fluctuation.PhysicalTerms
public import Balaban.Fluctuation.ParamActivityPhysical

/-!
# Block locality of the decoupled marks (`decMarkHatToBlocks`)

The decoupled marked terms `evDec … um tm Y (Θ, ψ̂)` are local in the hat field under `AgHatDir Y`
(clause 2 of `MarkedBlockExpansionDecPair`).  This file transfers that locality to the block
configuration `Φ`, through the clamped hat field `S.hatOf m₀ ρ hp Φ`, as
`HatLabelsDirect.labelAct_of_directTerms` does for the activities.

* `decMarkG`: the block-level mark `Φ ↦ ∂_t evDec … um t Y (Θ, ψ̂(Φ))|_{t=0}`.
* `deriv_evDec_congr`: the mark derivative inherits the `AgHatDir` locality in `(Θ, ψ̂)`.
* `decMarkG_dep`: for a label `Y′ ⊇ Y` that is a union of `m₀`-cells, `decMarkG` depends only on the
  blocks inside `Y′`.
* `continuous_decMarkG`, `measurable_decMarkG`, `norm_decMarkG_le`: continuity, measurability and the
  bound for all block configurations (the clamp keeps `ψ̂` in the ball of radius `cψ`, so
  `ρ ≤ cψ` is needed).
* `analyticOnNhd_decMarkG`, `decMarkG_fields`: the analytic fields in `(e, u)` for every `Φ`, and
  the bundle for the pair of `MarkedEvJointPhysV`.

The physical total identity, the numerical budget and `E1MarksC` are not treated here.
-/

@[expose] public section

namespace Balaban.Fluctuation

open MeasureTheory Balaban Balaban.Localization Balaban.Multiscale Balaban.Background
  Balaban.SmallField Balaban.Analysis Balaban.Polymer

section Def

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ ϱm : ℝ}
  (S : StepSetting d L N₁ m₁ k N ϱ) {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}

/-- **The block-level decoupled mark.**  The `t`-derivative at `0` of the decoupled term `evDec`
of the label `Y`, at the datum `Θ`, the first mark `um`, and the clamped hat field
`S.hatOf m₀ ρ hp Φ` of the block configuration `Φ`. -/
noncomputable def decMarkG (X₁f : Finset (CTorus d L N₁ m₁ (k + 1))) (m₀ j : ℕ)
    (𝒦X : Set (CTorus d L N₁ m₁ (k + 1))) (a₁ ν : ℝ) (cc : ℂ)
    (F₁ : DecParams S.G' × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      (S.G'.Ω 1 × Fin N → ℂ) × (S.G'.Ω 1 → ℂ))
    (Sol : Dec2.DecParams (coverOf S.G') × Edat Hm N → (Hm.Ω 1 × Fin N → ℂ) × (Hm.Ω 1 → ℂ))
    (En : ((S.G'.Ω 1 × Fin N → ℂ) × (S.G'.Ω 1 → ℂ)) → (Hm.Ω 1 × Fin N → ℂ) →
      RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) → ℂ)
    (Zm : Finset (unitPts S.G')) (Y : Set (CTorus d L N₁ m₁ (k + 1)))
    (ρ : ℝ) (hp : 0 < S.p₁) (Θ : RawData d L (N₁ * L ^ m₁) (k + 1) N) (um : ℂ)
    (Φ : ∀ b, (S.blockSplit m₀ hp).Ωb b) : ℂ :=
  deriv (fun t : ℂ => evDec X₁f m₀ j 𝒦X a₁ ν S.hG' cc F₁ Sol En Zm um t Y
    (Θ, S.hatOf m₀ ρ hp Φ)) 0

end Def

section Locality

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ ϱm : ℝ}
variable {Gp : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
variable {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}
variable {a₁ ν BG BG₂ κ eps δ₁ κdec cψ : ℝ} {X₁f : Finset (CTorus d L N₁ m₁ (k + 1))}
variable {m₀ j : ℕ} {𝒦X : Set (CTorus d L N₁ m₁ (k + 1))} {hG' : IsLevel Gp (k + 1)}
variable {cc : ℂ} {Zm : Finset (unitPts Gp)}
  {z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1)))}
variable {F₁ : DecParams Gp × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      (Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)}
variable {Sol : Dec2.DecParams (coverOf Gp) × Edat Hm N → (Hm.Ω 1 × Fin N → ℂ) × (Hm.Ω 1 → ℂ)}

/-- **T1.  Hat locality of the mark derivative.**  By clause 2 of `MarkedBlockExpansionDecPair`
(for every `(um, tm)` of the radius set, `u, u'` in `Ξ^c × B̂(cψ)` with `AgHatDir hG' Y u u'`:
`evDec … um tm Y u = evDec … um tm Y u'`), the `t`-derivative at `0` is the same at `u` and `u'`. -/
theorem deriv_evDec_congr
    (hP : MarkedBlockExpansionDecPair N Hm hG' cc a₁ ν BG BG₂ κ eps δ₁ κdec cψ Zm X₁f m₀ j 𝒦X z
      F₁ Sol)
    {um : ℂ} (hum : (‖um‖ + ‖(0 : ℂ)‖) * markedRad d L N k a₁ κ cψ cc < δ₁)
    (Y : Set (CTorus d L N₁ m₁ (k + 1)))
    {u u' : RawData d L (N₁ * L ^ m₁) (k + 1) N × (unitPts Gp × Fin N → ℂ)}
    (hu : u ∈ XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
        {ψh : unitPts Gp × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ})
    (hu' : u' ∈ XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
        {ψh : unitPts Gp × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ})
    (hag : AgHatDir hG' Y u u') :
    deriv (fun t : ℂ => evDec X₁f m₀ j 𝒦X a₁ ν hG' cc F₁ Sol
        (blockEnergyFun Gp Hm (compWeight L a₁) ν k z) Zm um t Y u) 0 =
      deriv (fun t : ℂ => evDec X₁f m₀ j 𝒦X a₁ ν hG' cc F₁ Sol
        (blockEnergyFun Gp Hm (compWeight L a₁) ν k z) Zm um t Y u') 0 := by
  refine Filter.EventuallyEq.deriv_eq ?_
  have hopen : IsOpen {t : ℂ | (‖um‖ + ‖t‖) * markedRad d L N k a₁ κ cψ cc < δ₁} :=
    isOpen_lt (by fun_prop) continuous_const
  have h0 : (0 : ℂ) ∈ {t : ℂ | (‖um‖ + ‖t‖) * markedRad d L N k a₁ κ cψ cc < δ₁} := hum
  filter_upwards [hopen.mem_nhds h0] with t ht
  exact hP.2.1 um t ht Y u hu u' hu' hag

end Locality

section Blocks

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ ϱm : ℝ}
  (S : StepSetting d L N₁ m₁ k N ϱ) {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}
variable {a₁ ν BG BG₂ κ eps δ₁ κdec cψ : ℝ} {X₁f : Finset (CTorus d L N₁ m₁ (k + 1))}
variable {m₀ j : ℕ} {𝒦X : Set (CTorus d L N₁ m₁ (k + 1))}
variable {cc : ℂ} {Zm : Finset (unitPts S.G')}
  {z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1)))}
variable {F₁ : DecParams S.G' × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      (S.G'.Ω 1 × Fin N → ℂ) × (S.G'.Ω 1 → ℂ)}
variable {Sol : Dec2.DecParams (coverOf S.G') × Edat Hm N → (Hm.Ω 1 × Fin N → ℂ) × (Hm.Ω 1 → ℂ)}

/-- **T2.  The block-level decoupled mark depends only on the blocks of its label.**  Let `Y′` be a
label that is a union of `m₀`-cells (every `m₀`-cell containing a site of `Y′` lies in `Y′`, which
holds for domains of `𝒟_{k+1}` by `cell_subset_of_isDj`) and contains the domain `Y` of the term.
Then `decMarkG … Y …` depends on `Φ` only through the blocks inside `Y′` (`Y′ = Y` allowed).  The
radius `ρ` of the clamp is at most `cψ`, so that the clamped hat field lies in the ball of
clause 2. -/
theorem decMarkG_dep
    (hP : MarkedBlockExpansionDecPair N Hm S.hG' cc a₁ ν BG BG₂ κ eps δ₁ κdec cψ Zm X₁f m₀ j 𝒦X z
      F₁ Sol)
    {ρ : ℝ} (hρ : 0 < ρ) (hρc : ρ ≤ cψ) (hp : 0 < S.p₁)
    {Θ : RawData d L (N₁ * L ^ m₁) (k + 1) N}
    (hΘ : Θ ∈ XiCRaw S.G' (compWeight L a₁) ν (k + 1) 1 eps)
    {um : ℂ} (hum : (‖um‖ + ‖(0 : ℂ)‖) * markedRad d L N k a₁ κ cψ cc < δ₁)
    {Y Y' : Set (CTorus d L N₁ m₁ (k + 1))} (hYY : Y ⊆ Y')
    (hY' : ∀ y ∈ Y', box (cbase (cellSide L m₀ m₁ (k + 1)) y) (cellSide L m₀ m₁ (k + 1)) ⊆ Y') :
    DepOn (blocksOf m₀ (k + 1) Set.univ Y')
      (decMarkG S X₁f m₀ j 𝒦X a₁ ν cc F₁ Sol (blockEnergyFun S.G' Hm (compWeight L a₁) ν k z) Zm
        Y ρ hp Θ um) := by
  intro Φ Φ' h
  have hmem : ∀ Ψ : ∀ b, (S.blockSplit m₀ hp).Ωb b, (Θ, S.hatOf m₀ ρ hp Ψ) ∈
      XiCRaw S.G' (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
        {ψh : unitPts S.G' × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ} :=
    fun Ψ => ⟨hΘ, fun p => (S.hatOf_mem m₀ hρ hp Ψ p).trans hρc⟩
  have hhat := S.agHatFDir_hatOf m₀ hY' ρ hp Φ Φ' h
  exact deriv_evDec_congr hP hum Y (hmem Φ) (hmem Φ')
    ⟨agreeOn_refl _ _, fun y hy i => hhat y (hYY hy) i⟩

/-- **The bound for all block configurations.**  By clause 5 of `MarkedBlockExpansionDecPair` (the
Cauchy estimate), since the clamped hat field stays in the ball of radius `cψ`:
`‖decMarkG … Φ‖ ≤ E_* e^{-2 κ_dec d^cov(Y)} / t₀` for every `Φ`. -/
theorem norm_decMarkG_le
    (hP : MarkedBlockExpansionDecPair N Hm S.hG' cc a₁ ν BG BG₂ κ eps δ₁ κdec cψ Zm X₁f m₀ j 𝒦X z
      F₁ Sol)
    {ρ : ℝ} (hρ : 0 < ρ) (hρc : ρ ≤ cψ) (hp : 0 < S.p₁)
    {Θ : RawData d L (N₁ * L ^ m₁) (k + 1) N}
    (hΘ : Θ ∈ XiCRaw S.G' (compWeight L a₁) ν (k + 1) 1 eps)
    {a b t₀ : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (ht : 0 < t₀) (htb : t₀ ≤ b)
    (hab : (a + b) * markedRad d L N k a₁ κ cψ cc < δ₁) {um : ℂ} (hum : ‖um‖ ≤ a)
    (Y : Set (CTorus d L N₁ m₁ (k + 1))) (Φ : ∀ b, (S.blockSplit m₀ hp).Ωb b) :
    ‖decMarkG S X₁f m₀ j 𝒦X a₁ ν cc F₁ Sol (blockEnergyFun S.G' Hm (compWeight L a₁) ν k z) Zm
        Y ρ hp Θ um Φ‖ ≤
      energyBdScaled d L N (compWeight L a₁) k
        (cK2' d L N (famConst d L BG₂ κ) * δ₁) δ₁ (rho4 d L N BG κ) *
        Real.exp (-2 * κdec * treeLenCov S.G' m₀ Y) / t₀ :=
  hP.2.2.2.2.1 a b t₀ ha hb ht htb hab um hum Y _
    ⟨hΘ, fun p => (S.hatOf_mem m₀ hρ hp Φ p).trans hρc⟩

/-- **The fields of a mark family for the decoupled marks, for a given pair.**  The four field
conclusions of `decMarkG_fields` for an explicitly given pair `(F₁, Sol)` with its eight clauses
`hP`, joint analyticity on the chart (`hJ2`) and the derivative marks on `physV` (`hJ4`), exactly
as `MarkedEvJointPhysV` provides them.  Later statements about the same pair can refer to it. -/
theorem decMarkG_fields_of_pair
    (F₁ : DecParams S.G' × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      (S.G'.Ω 1 × Fin N → ℂ) × (S.G'.Ω 1 → ℂ))
    (Sol : Dec2.DecParams (coverOf S.G') × Edat Hm N → (Hm.Ω 1 × Fin N → ℂ) × (Hm.Ω 1 → ℂ))
    (hP : MarkedBlockExpansionDecPair N Hm S.hG' cc a₁ ν BG BG₂ κ eps δ₁ κdec cψ Zm X₁f m₀ j 𝒦X z
      F₁ Sol)
    (hJ2 : ∀ Y, AnalyticOnNhd ℂ
        (fun p : (RawData d L (N₁ * L ^ m₁) (k + 1) N × (unitPts S.G' × Fin N → ℂ)) × (ℂ × ℂ) =>
          evDec X₁f m₀ j 𝒦X a₁ ν S.hG' cc F₁ Sol
            (blockEnergyFun S.G' Hm (compWeight L a₁) ν k z) Zm p.2.1 p.2.2 Y p.1)
        ((XiCRaw S.G' (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
          {ψh : unitPts S.G' × Fin N → ℂ | ∀ q, ‖ψh q‖ ≤ cψ}) ×ˢ
          {w : ℂ × ℂ | (‖w.1‖ + ‖w.2‖) * markedRad d L N k a₁ κ cψ cc < δ₁}))
    (hJ4 : ∀ Y, ∀ ψh : unitPts S.G' × Fin N → ℂ, (∀ q, ‖ψh q‖ ≤ cψ) →
        ∀ a b : ℝ, 0 ≤ a → 0 < b → (a + b) * markedRad d L N k a₁ κ cψ cc < δ₁ →
        AnalyticOnNhd ℂ (fun p : physParam N S × ℂ => deriv (fun t : ℂ =>
          evDec X₁f m₀ j 𝒦X a₁ ν S.hG' cc F₁ Sol
            (blockEnergyFun S.G' Hm (compWeight L a₁) ν k z) Zm p.2 t Y
            ((p.1.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N), ψh)) 0)
          (physV S a₁ ν eps ×ˢ Metric.ball (0 : ℂ) a))
    {ρ : ℝ} (hρ : 0 < ρ) (hρc : ρ ≤ cψ) (hp : 0 < S.p₁) :
      (∀ (Y Y' : Set (CTorus d L N₁ m₁ (k + 1))), Y ⊆ Y' →
        (∀ y ∈ Y', box (cbase (cellSide L m₀ m₁ (k + 1)) y) (cellSide L m₀ m₁ (k + 1)) ⊆ Y') →
        ∀ Θ ∈ XiCRaw S.G' (compWeight L a₁) ν (k + 1) 1 eps, ∀ um : ℂ,
        (‖um‖ + ‖(0 : ℂ)‖) * markedRad d L N k a₁ κ cψ cc < δ₁ →
        DepOn (blocksOf m₀ (k + 1) Set.univ Y')
          (decMarkG S X₁f m₀ j 𝒦X a₁ ν cc F₁ Sol (blockEnergyFun S.G' Hm (compWeight L a₁) ν k z)
            Zm Y ρ hp Θ um)) ∧
      (∀ Y, ∀ Θ ∈ XiCRaw S.G' (compWeight L a₁) ν (k + 1) 1 eps, ∀ um : ℂ,
        (‖um‖ + ‖(0 : ℂ)‖) * markedRad d L N k a₁ κ cψ cc < δ₁ →
        Continuous (decMarkG S X₁f m₀ j 𝒦X a₁ ν cc F₁ Sol
          (blockEnergyFun S.G' Hm (compWeight L a₁) ν k z) Zm Y ρ hp Θ um) ∧
        Measurable (decMarkG S X₁f m₀ j 𝒦X a₁ ν cc F₁ Sol
          (blockEnergyFun S.G' Hm (compWeight L a₁) ν k z) Zm Y ρ hp Θ um)) ∧
      (∀ Y, ∀ Θ ∈ XiCRaw S.G' (compWeight L a₁) ν (k + 1) 1 eps, ∀ a b t₀ : ℝ, 0 ≤ a → 0 ≤ b →
        0 < t₀ → t₀ ≤ b → (a + b) * markedRad d L N k a₁ κ cψ cc < δ₁ → ∀ um : ℂ, ‖um‖ ≤ a →
        ∀ Φ : (∀ b, (S.blockSplit m₀ hp).Ωb b),
        ‖decMarkG S X₁f m₀ j 𝒦X a₁ ν cc F₁ Sol (blockEnergyFun S.G' Hm (compWeight L a₁) ν k z)
            Zm Y ρ hp Θ um Φ‖ ≤
          energyBdScaled d L N (compWeight L a₁) k
            (cK2' d L N (famConst d L BG₂ κ) * δ₁) δ₁ (rho4 d L N BG κ) *
            Real.exp (-2 * κdec * treeLenCov S.G' m₀ Y) / t₀) ∧
      (∀ Y, ∀ Φ : (∀ b, (S.blockSplit m₀ hp).Ωb b), ∀ a b : ℝ, 0 ≤ a → 0 < b →
        (a + b) * markedRad d L N k a₁ κ cψ cc < δ₁ →
        AnalyticOnNhd ℂ (fun p : physParam N S × ℂ =>
          decMarkG S X₁f m₀ j 𝒦X a₁ ν cc F₁ Sol (blockEnergyFun S.G' Hm (compWeight L a₁) ν k z)
            Zm Y ρ hp (p.1.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) p.2 Φ)
          (physV S a₁ ν eps ×ˢ Metric.ball (0 : ℂ) a)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro Y Y' hYY hY' Θ hΘ um hum
    exact decMarkG_dep S hP hρ hρc hp hΘ hum hYY hY'
  · intro Y Θ hΘ um hum
    have hW : (um, (0 : ℂ)) ∈ {w : ℂ × ℂ |
        (‖w.1‖ + ‖w.2‖) * markedRad d L N k a₁ κ cψ cc < δ₁} := hum
    have hana := analyticOnNhd_deriv_mark (hJ2 Y)
    have hc : ContinuousOn (fun ψ : unitPts S.G' × Fin N → ℂ => deriv (fun t : ℂ =>
        evDec X₁f m₀ j 𝒦X a₁ ν S.hG' cc F₁ Sol (blockEnergyFun S.G' Hm (compWeight L a₁) ν k z)
          Zm um t Y (Θ, ψ)) 0)
        {ψh : unitPts S.G' × Fin N → ℂ | ∀ q, ‖ψh q‖ ≤ cψ} := by
      have h1 := hana.continuousOn.comp (f := fun ψ : unitPts S.G' × Fin N → ℂ => ((Θ, ψ), um))
        (by fun_prop) (fun ψ hψ => ⟨⟨hΘ, hψ⟩, hW⟩)
      exact h1
    have hcont : Continuous (decMarkG S X₁f m₀ j 𝒦X a₁ ν cc F₁ Sol
        (blockEnergyFun S.G' Hm (compWeight L a₁) ν k z) Zm Y ρ hp Θ um) :=
      hc.comp_continuous (S.continuous_hatOf m₀ ρ hp)
        (fun Φ q => (S.hatOf_mem m₀ hρ hp Φ q).trans hρc)
    exact ⟨hcont, hcont.measurable⟩
  · intro Y Θ hΘ a b t₀ ha hb ht htb hab um hum Φ
    exact norm_decMarkG_le S hP hρ hρc hp hΘ ha hb ht htb hab hum Y Φ
  · intro Y Φ a b ha hb hab
    exact hJ4 Y (S.hatOf m₀ ρ hp Φ) (fun q => (S.hatOf_mem m₀ hρ hp Φ q).trans hρc) a b ha hb hab

/-- **T2/T3.  The fields of a mark family for the decoupled marks.**  From `MarkedEvJointPhysV`,
there is one pair `(F₁, Sol)` such that, for every label `Y`, with the clamp radius
`0 < ρ ≤ cψ` (the margin) and the energy `blockEnergyFun`:

* `dep`: `DepOn (blocksOf m₀ (k+1) univ Y′)` for every cell-union `Y′ ⊇ Y`;
* `meas`, `contG`: the mark is continuous, hence measurable, on all block configurations;
* `bound`: the bound `E_* e^{-2 κ_dec d^cov(Y)}/t₀` for all `Φ`;
* `holG`: for each `Φ`, `(e, u) ↦ decMarkG … e.1 u Φ` is analytic on `physV × {‖u‖ < a}`. -/
theorem decMarkG_fields
    (hM : MarkedEvJointPhysV S Hm cc a₁ ν BG BG₂ κ eps δ₁ κdec cψ Zm X₁f m₀ j 𝒦X z)
    {ρ : ℝ} (hρ : 0 < ρ) (hρc : ρ ≤ cψ) (hp : 0 < S.p₁) :
    ∃ (F₁ : DecParams S.G' × RawData d L (N₁ * L ^ m₁) (k + 1) N →
        (S.G'.Ω 1 × Fin N → ℂ) × (S.G'.Ω 1 → ℂ))
      (Sol : Dec2.DecParams (coverOf S.G') × Edat Hm N → (Hm.Ω 1 × Fin N → ℂ) × (Hm.Ω 1 → ℂ)),
      (∀ (Y Y' : Set (CTorus d L N₁ m₁ (k + 1))), Y ⊆ Y' →
        (∀ y ∈ Y', box (cbase (cellSide L m₀ m₁ (k + 1)) y) (cellSide L m₀ m₁ (k + 1)) ⊆ Y') →
        ∀ Θ ∈ XiCRaw S.G' (compWeight L a₁) ν (k + 1) 1 eps, ∀ um : ℂ,
        (‖um‖ + ‖(0 : ℂ)‖) * markedRad d L N k a₁ κ cψ cc < δ₁ →
        DepOn (blocksOf m₀ (k + 1) Set.univ Y')
          (decMarkG S X₁f m₀ j 𝒦X a₁ ν cc F₁ Sol (blockEnergyFun S.G' Hm (compWeight L a₁) ν k z)
            Zm Y ρ hp Θ um)) ∧
      (∀ Y, ∀ Θ ∈ XiCRaw S.G' (compWeight L a₁) ν (k + 1) 1 eps, ∀ um : ℂ,
        (‖um‖ + ‖(0 : ℂ)‖) * markedRad d L N k a₁ κ cψ cc < δ₁ →
        Continuous (decMarkG S X₁f m₀ j 𝒦X a₁ ν cc F₁ Sol
          (blockEnergyFun S.G' Hm (compWeight L a₁) ν k z) Zm Y ρ hp Θ um) ∧
        Measurable (decMarkG S X₁f m₀ j 𝒦X a₁ ν cc F₁ Sol
          (blockEnergyFun S.G' Hm (compWeight L a₁) ν k z) Zm Y ρ hp Θ um)) ∧
      (∀ Y, ∀ Θ ∈ XiCRaw S.G' (compWeight L a₁) ν (k + 1) 1 eps, ∀ a b t₀ : ℝ, 0 ≤ a → 0 ≤ b →
        0 < t₀ → t₀ ≤ b → (a + b) * markedRad d L N k a₁ κ cψ cc < δ₁ → ∀ um : ℂ, ‖um‖ ≤ a →
        ∀ Φ : (∀ b, (S.blockSplit m₀ hp).Ωb b),
        ‖decMarkG S X₁f m₀ j 𝒦X a₁ ν cc F₁ Sol (blockEnergyFun S.G' Hm (compWeight L a₁) ν k z)
            Zm Y ρ hp Θ um Φ‖ ≤
          energyBdScaled d L N (compWeight L a₁) k
            (cK2' d L N (famConst d L BG₂ κ) * δ₁) δ₁ (rho4 d L N BG κ) *
            Real.exp (-2 * κdec * treeLenCov S.G' m₀ Y) / t₀) ∧
      (∀ Y, ∀ Φ : (∀ b, (S.blockSplit m₀ hp).Ωb b), ∀ a b : ℝ, 0 ≤ a → 0 < b →
        (a + b) * markedRad d L N k a₁ κ cψ cc < δ₁ →
        AnalyticOnNhd ℂ (fun p : physParam N S × ℂ =>
          decMarkG S X₁f m₀ j 𝒦X a₁ ν cc F₁ Sol (blockEnergyFun S.G' Hm (compWeight L a₁) ν k z)
            Zm Y ρ hp (p.1.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) p.2 Φ)
          (physV S a₁ ν eps ×ˢ Metric.ball (0 : ℂ) a)) := by
  obtain ⟨F₁, Sol, hP, hJ2, -, hJ4, -, -⟩ := hM
  exact ⟨F₁, Sol, decMarkG_fields_of_pair S F₁ Sol hP hJ2 hJ4 hρ hρc hp⟩

end Blocks
end Balaban.Fluctuation
