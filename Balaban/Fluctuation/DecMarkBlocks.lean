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

**Background generating sets (ruling R8).**  P3 pp. 78-79, (4.44)-(4.47), computes the terms of
the new level with the local generating set of their polymer.  `decMarkGBg S Gb T …` is the mark
with the term `evDecBg` computed on a background generating set `Gb` with a transport `T`
(`BgTransport`), the hat variable being the restriction `T.res` of the step's clamped hat field;
`decMarkG` is its instance `Gb = S.G'`, `T = BgTransport.self S.hG'` (definitionally,
`decMarkG_eq_deriv_evDec`).  The locality, bound and field theorems are proved once on a general
`Gb` (`deriv_evDecBg_congr_of`, `deriv_evDecBg_hatOf_dep`, `norm_deriv_evDecBg_hatOf_le`,
`deriv_evDecBg_hatOf_fields`, `decMarkGBg_dep`, `norm_decMarkGBg_le`); the theorems at `S.G'` are
their instances.

The physical total identity, the numerical budget and `E1MarksC` are not treated here.
-/

@[expose] public section

namespace Balaban.Fluctuation

open MeasureTheory Balaban Balaban.Localization Balaban.Multiscale Balaban.Background
  Balaban.SmallField Balaban.Analysis Balaban.Polymer

section LocalityCoreBg

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ ϱb ϱm : ℝ}
variable {Gp : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
variable {Gb : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱb}
variable {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}
variable {a₁ ν κ δ₁ cψ : ℝ} {X₁f : Finset (CTorus d L N₁ m₁ (k + 1))}
variable {m₀ j : ℕ} {𝒦X : Set (CTorus d L N₁ m₁ (k + 1))} {T : BgTransport Gp Gb N}
variable {cc : ℂ} {Zm : Finset (unitPts Gb)}
variable {F₁ : DecParams Gb × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      (Gb.Ω 1 × Fin N → ℂ) × (Gb.Ω 1 → ℂ)}
variable {Sol : Dec2.DecParams (coverOf Gb) × Edat Hm N → (Hm.Ω 1 × Fin N → ℂ) × (Hm.Ω 1 → ℂ)}

/-- **The mark derivative of a term on a background generating set depends only on the term near
the second mark `0`.**  If the terms `evDecBg` at `u` and `u'` agree at every second mark `tm` of
the radius set (first mark `um` fixed), their `t`-derivatives at `0` agree. -/
theorem deriv_evDecBg_congr_of
    {En : ((Gb.Ω 1 × Fin N → ℂ) × (Gb.Ω 1 → ℂ)) → (Hm.Ω 1 × Fin N → ℂ) →
      RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) → ℂ}
    {um : ℂ} {Y : Set (CTorus d L N₁ m₁ (k + 1))}
    {u u' : RawData d L (N₁ * L ^ m₁) (k + 1) N × (unitPts Gb × Fin N → ℂ)}
    (hloc : ∀ tm : ℂ, (‖um‖ + ‖tm‖) * markedRad d L N k a₁ κ cψ cc < δ₁ →
      evDecBg Gp X₁f m₀ j 𝒦X Gb a₁ ν T cc F₁ Sol En Zm um tm Y u =
        evDecBg Gp X₁f m₀ j 𝒦X Gb a₁ ν T cc F₁ Sol En Zm um tm Y u')
    (hum : (‖um‖ + ‖(0 : ℂ)‖) * markedRad d L N k a₁ κ cψ cc < δ₁) :
    deriv (fun t : ℂ => evDecBg Gp X₁f m₀ j 𝒦X Gb a₁ ν T cc F₁ Sol En Zm um t Y u) 0 =
      deriv (fun t : ℂ => evDecBg Gp X₁f m₀ j 𝒦X Gb a₁ ν T cc F₁ Sol En Zm um t Y u') 0 := by
  refine Filter.EventuallyEq.deriv_eq ?_
  have hopen : IsOpen {t : ℂ | (‖um‖ + ‖t‖) * markedRad d L N k a₁ κ cψ cc < δ₁} :=
    isOpen_lt (by fun_prop) continuous_const
  filter_upwards [hopen.mem_nhds hum] with t ht
  exact hloc t ht

end LocalityCoreBg

section LocalityCore

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ ϱm : ℝ}
variable {Gp : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
variable {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}
variable {a₁ ν κ eps δ₁ cψ : ℝ} {X₁f : Finset (CTorus d L N₁ m₁ (k + 1))}
variable {m₀ j : ℕ} {𝒦X : Set (CTorus d L N₁ m₁ (k + 1))} {hG' : IsLevel Gp (k + 1)}
variable {cc : ℂ} {Zm : Finset (unitPts Gp)}
variable {F₁ : DecParams Gp × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      (Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)}
variable {Sol : Dec2.DecParams (coverOf Gp) × Edat Hm N → (Hm.Ω 1 × Fin N → ℂ) × (Hm.Ω 1 → ℂ)}

/-- **Core of `deriv_evDec_congr`, for any functional `En`.**  If the marked terms of `En` are local
in the sense of `AgHatDir Y` at every mark of the radius set (`hloc`, the form of clause 2 of
`MarkedBlockExpansionDecPair`), the `t`-derivative at `0` is the same at `u` and `u'`. -/
theorem deriv_evDec_congr_of
    {En : ((Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)) → (Hm.Ω 1 × Fin N → ℂ) →
      RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) → ℂ}
    (hloc : ∀ um tm : ℂ, (‖um‖ + ‖tm‖) * markedRad d L N k a₁ κ cψ cc < δ₁ →
      ∀ Y, ∀ u ∈ XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
        {ψh : unitPts Gp × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ},
      ∀ u' ∈ XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
        {ψh : unitPts Gp × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ},
      AgHatDir hG' Y u u' →
        evDec X₁f m₀ j 𝒦X a₁ ν hG' cc F₁ Sol En Zm um tm Y u =
        evDec X₁f m₀ j 𝒦X a₁ ν hG' cc F₁ Sol En Zm um tm Y u')
    {um : ℂ} (hum : (‖um‖ + ‖(0 : ℂ)‖) * markedRad d L N k a₁ κ cψ cc < δ₁)
    (Y : Set (CTorus d L N₁ m₁ (k + 1)))
    {u u' : RawData d L (N₁ * L ^ m₁) (k + 1) N × (unitPts Gp × Fin N → ℂ)}
    (hu : u ∈ XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
        {ψh : unitPts Gp × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ})
    (hu' : u' ∈ XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
        {ψh : unitPts Gp × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ})
    (hag : AgHatDir hG' Y u u') :
    deriv (fun t : ℂ => evDec X₁f m₀ j 𝒦X a₁ ν hG' cc F₁ Sol En Zm um t Y u) 0 =
      deriv (fun t : ℂ => evDec X₁f m₀ j 𝒦X a₁ ν hG' cc F₁ Sol En Zm um t Y u') 0 :=
  deriv_evDecBg_congr_of (T := BgTransport.self hG')
    (fun tm htm => hloc um tm htm Y u hu u' hu' hag) hum

end LocalityCore

section Def

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ ϱm : ℝ}
  (S : StepSetting d L N₁ m₁ k N ϱ) {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}

/-- **The block-level decoupled mark on a background generating set `Gb`** (P3 pp. 78-79,
(4.44)-(4.47)).  The `t`-derivative at `0` of the term `evDecBg` of the label `Y` of the step's
expansion, computed on `Gb` with the transport `T`, at the datum `Θ` (a datum of `Gb`), the first
mark `um`, and the restriction `T.res` of the clamped hat field `S.hatOf m₀ ρ hp Φ` of the block
configuration `Φ`.  The fluctuation blocks and their measure are those of the step `S`. -/
noncomputable def decMarkGBg {ϱb : ℝ} (Gb : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱb)
    (T : BgTransport S.G' Gb N) (X₁f : Finset (CTorus d L N₁ m₁ (k + 1))) (m₀ j : ℕ)
    (𝒦X : Set (CTorus d L N₁ m₁ (k + 1))) (a₁ ν : ℝ) (cc : ℂ)
    (F₁ : DecParams Gb × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      (Gb.Ω 1 × Fin N → ℂ) × (Gb.Ω 1 → ℂ))
    (Sol : Dec2.DecParams (coverOf Gb) × Edat Hm N → (Hm.Ω 1 × Fin N → ℂ) × (Hm.Ω 1 → ℂ))
    (En : ((Gb.Ω 1 × Fin N → ℂ) × (Gb.Ω 1 → ℂ)) → (Hm.Ω 1 × Fin N → ℂ) →
      RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) → ℂ)
    (Zm : Finset (unitPts Gb)) (Y : Set (CTorus d L N₁ m₁ (k + 1)))
    (ρ : ℝ) (hp : 0 < S.p₁) (Θ : RawData d L (N₁ * L ^ m₁) (k + 1) N) (um : ℂ)
    (Φ : ∀ b, (S.blockSplit m₀ hp).Ωb b) : ℂ :=
  deriv (fun t : ℂ => evDecBg S.G' X₁f m₀ j 𝒦X Gb a₁ ν T cc F₁ Sol En Zm um t Y
    (Θ, T.res (S.hatOf m₀ ρ hp Φ))) 0

/-- **The block-level decoupled mark.**  The `t`-derivative at `0` of the decoupled term `evDec`
of the label `Y`, at the datum `Θ`, the first mark `um`, and the clamped hat field
`S.hatOf m₀ ρ hp Φ` of the block configuration `Φ` (`decMarkGBg` at `Gb = S.G'` with the transport
`BgTransport.self`). -/
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
  decMarkGBg S S.G' (BgTransport.self S.hG') X₁f m₀ j 𝒦X a₁ ν cc F₁ Sol En Zm Y ρ hp Θ um Φ

/-- **Instance lemma.**  The step's block-level decoupled mark is `decMarkGBg` at `Gb = S.G'` with
the transport `BgTransport.self S.hG'`. -/
theorem decMarkG_eq_decMarkGBg_self (X₁f : Finset (CTorus d L N₁ m₁ (k + 1))) (m₀ j : ℕ)
    (𝒦X : Set (CTorus d L N₁ m₁ (k + 1))) (a₁ ν : ℝ) (cc : ℂ)
    (F₁ : DecParams S.G' × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      (S.G'.Ω 1 × Fin N → ℂ) × (S.G'.Ω 1 → ℂ))
    (Sol : Dec2.DecParams (coverOf S.G') × Edat Hm N → (Hm.Ω 1 × Fin N → ℂ) × (Hm.Ω 1 → ℂ))
    (En : ((S.G'.Ω 1 × Fin N → ℂ) × (S.G'.Ω 1 → ℂ)) → (Hm.Ω 1 × Fin N → ℂ) →
      RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) → ℂ)
    (Zm : Finset (unitPts S.G')) (Y : Set (CTorus d L N₁ m₁ (k + 1)))
    (ρ : ℝ) (hp : 0 < S.p₁) (Θ : RawData d L (N₁ * L ^ m₁) (k + 1) N) (um : ℂ)
    (Φ : ∀ b, (S.blockSplit m₀ hp).Ωb b) :
    decMarkG S X₁f m₀ j 𝒦X a₁ ν cc F₁ Sol En Zm Y ρ hp Θ um Φ =
      decMarkGBg S S.G' (BgTransport.self S.hG') X₁f m₀ j 𝒦X a₁ ν cc F₁ Sol En Zm Y ρ hp Θ um
        Φ := rfl

/-- The block-level decoupled mark is the `t`-derivative at `0` of `evDec` at the clamped hat
field. -/
theorem decMarkG_eq_deriv_evDec (X₁f : Finset (CTorus d L N₁ m₁ (k + 1))) (m₀ j : ℕ)
    (𝒦X : Set (CTorus d L N₁ m₁ (k + 1))) (a₁ ν : ℝ) (cc : ℂ)
    (F₁ : DecParams S.G' × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      (S.G'.Ω 1 × Fin N → ℂ) × (S.G'.Ω 1 → ℂ))
    (Sol : Dec2.DecParams (coverOf S.G') × Edat Hm N → (Hm.Ω 1 × Fin N → ℂ) × (Hm.Ω 1 → ℂ))
    (En : ((S.G'.Ω 1 × Fin N → ℂ) × (S.G'.Ω 1 → ℂ)) → (Hm.Ω 1 × Fin N → ℂ) →
      RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) → ℂ)
    (Zm : Finset (unitPts S.G')) (Y : Set (CTorus d L N₁ m₁ (k + 1)))
    (ρ : ℝ) (hp : 0 < S.p₁) (Θ : RawData d L (N₁ * L ^ m₁) (k + 1) N) (um : ℂ)
    (Φ : ∀ b, (S.blockSplit m₀ hp).Ωb b) :
    decMarkG S X₁f m₀ j 𝒦X a₁ ν cc F₁ Sol En Zm Y ρ hp Θ um Φ =
      deriv (fun t : ℂ => evDec X₁f m₀ j 𝒦X a₁ ν S.hG' cc F₁ Sol En Zm um t Y
        (Θ, S.hatOf m₀ ρ hp Φ)) 0 := rfl

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
        (blockEnergyFun Gp Hm (compWeight L a₁) ν k z) Zm um t Y u') 0 :=
  deriv_evDec_congr_of hP.2.1 hum Y hu hu' hag

end Locality

section BlocksBg

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ ϱb ϱm : ℝ}
  (S : StepSetting d L N₁ m₁ k N ϱ) {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}
  {Gb : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱb} {T : BgTransport S.G' Gb N}
variable {a₁ ν κ eps δ₁ cψ : ℝ} {X₁f : Finset (CTorus d L N₁ m₁ (k + 1))}
variable {m₀ j : ℕ} {𝒦X : Set (CTorus d L N₁ m₁ (k + 1))}
variable {cc : ℂ} {Zm : Finset (unitPts Gb)}
variable {F₁ : DecParams Gb × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      (Gb.Ω 1 × Fin N → ℂ) × (Gb.Ω 1 → ℂ)}
variable {Sol : Dec2.DecParams (coverOf Gb) × Edat Hm N → (Hm.Ω 1 × Fin N → ℂ) × (Hm.Ω 1 → ℂ)}

/-- **Block locality of the mark derivative on a background generating set.**  If the terms
`evDecBg` on `Gb` are local in the step's hat variable (`hloc`: for `u, u'` of the chart of `Gb`
times the box `|ψ̂| ≤ cψ` with `AgHatDir S.hG' Y u u'`, the terms at `(u.1, T.res u.2)` and
`(u'.1, T.res u'.2)` agree), then for a label `Y′ ⊇ Y` that is a union of `mb`-cells the mark
derivative at the restricted clamped hat field of the `mb`-block configuration,
`Φ ↦ ∂_t evDecBg … um t Y (Θ, T.res (S.hatOf mb ρ hp Φ))|_{t=0}`, depends only on the blocks inside
`Y′`. -/
theorem deriv_evDecBg_hatOf_dep (mb : ℕ)
    {En : ((Gb.Ω 1 × Fin N → ℂ) × (Gb.Ω 1 → ℂ)) → (Hm.Ω 1 × Fin N → ℂ) →
      RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) → ℂ}
    (hloc : ∀ um tm : ℂ, (‖um‖ + ‖tm‖) * markedRad d L N k a₁ κ cψ cc < δ₁ →
      ∀ Y, ∀ u ∈ XiCRaw Gb (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
        {ψh : unitPts S.G' × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ},
      ∀ u' ∈ XiCRaw Gb (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
        {ψh : unitPts S.G' × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ},
      AgHatDir S.hG' Y u u' →
        evDecBg S.G' X₁f m₀ j 𝒦X Gb a₁ ν T cc F₁ Sol En Zm um tm Y (u.1, T.res u.2) =
        evDecBg S.G' X₁f m₀ j 𝒦X Gb a₁ ν T cc F₁ Sol En Zm um tm Y (u'.1, T.res u'.2))
    {ρ : ℝ} (hρ : 0 < ρ) (hρc : ρ ≤ cψ) (hp : 0 < S.p₁)
    {Θ : RawData d L (N₁ * L ^ m₁) (k + 1) N}
    (hΘ : Θ ∈ XiCRaw Gb (compWeight L a₁) ν (k + 1) 1 eps)
    {um : ℂ} (hum : (‖um‖ + ‖(0 : ℂ)‖) * markedRad d L N k a₁ κ cψ cc < δ₁)
    {Y Y' : Set (CTorus d L N₁ m₁ (k + 1))} (hYY : Y ⊆ Y')
    (hY' : ∀ y ∈ Y', box (cbase (cellSide L mb m₁ (k + 1)) y) (cellSide L mb m₁ (k + 1)) ⊆ Y') :
    DepOn (blocksOf mb (k + 1) Set.univ Y')
      (fun Φ : ∀ b, (S.blockSplit mb hp).Ωb b =>
        deriv (fun t : ℂ => evDecBg S.G' X₁f m₀ j 𝒦X Gb a₁ ν T cc F₁ Sol En Zm um t Y
            (Θ, T.res (S.hatOf mb ρ hp Φ))) 0) := by
  intro Φ Φ' h
  have hmem : ∀ Ψ : ∀ b, (S.blockSplit mb hp).Ωb b, (Θ, S.hatOf mb ρ hp Ψ) ∈
      XiCRaw Gb (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
        {ψh : unitPts S.G' × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ} :=
    fun Ψ => ⟨hΘ, fun p => (S.hatOf_mem mb hρ hp Ψ p).trans hρc⟩
  have hhat := S.agHatFDir_hatOf mb hY' ρ hp Φ Φ' h
  have key : ∀ tm : ℂ, (‖um‖ + ‖tm‖) * markedRad d L N k a₁ κ cψ cc < δ₁ →
      evDecBg S.G' X₁f m₀ j 𝒦X Gb a₁ ν T cc F₁ Sol En Zm um tm Y
          (Θ, T.res (S.hatOf mb ρ hp Φ)) =
        evDecBg S.G' X₁f m₀ j 𝒦X Gb a₁ ν T cc F₁ Sol En Zm um tm Y
          (Θ, T.res (S.hatOf mb ρ hp Φ')) :=
    fun tm htm => hloc um tm htm Y (Θ, S.hatOf mb ρ hp Φ) (hmem Φ) (Θ, S.hatOf mb ρ hp Φ')
      (hmem Φ') ⟨agreeOn_refl _ _, fun y hy i => hhat y (hYY hy) i⟩
  exact deriv_evDecBg_congr_of key hum

/-- **The bound of the mark derivative on a background generating set.**  From a Cauchy estimate
`hcau` of the mark derivatives of the terms `evDecBg` on `Gb` with a bound `B Y`, at the points of
the chart of `Gb` times the box `|ψ̂| ≤ cψ`: the mark derivative at the restricted clamped hat field
of every `mb`-block configuration `Φ` is bounded by `B Y / t₀`. -/
theorem norm_deriv_evDecBg_hatOf_le (mb : ℕ)
    {En : ((Gb.Ω 1 × Fin N → ℂ) × (Gb.Ω 1 → ℂ)) → (Hm.Ω 1 × Fin N → ℂ) →
      RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) → ℂ}
    {B : Set (CTorus d L N₁ m₁ (k + 1)) → ℝ}
    (hcau : ∀ a b t₀ : ℝ, 0 ≤ a → 0 ≤ b → 0 < t₀ → t₀ ≤ b →
      (a + b) * markedRad d L N k a₁ κ cψ cc < δ₁ →
      ∀ um : ℂ, ‖um‖ ≤ a →
      ∀ Y, ∀ u ∈ XiCRaw Gb (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
        {ψh : unitPts S.G' × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ},
      ‖deriv (fun t : ℂ => evDecBg S.G' X₁f m₀ j 𝒦X Gb a₁ ν T cc F₁ Sol En Zm um t Y
          (u.1, T.res u.2)) 0‖ ≤ B Y / t₀)
    {ρ : ℝ} (hρ : 0 < ρ) (hρc : ρ ≤ cψ) (hp : 0 < S.p₁)
    {Θ : RawData d L (N₁ * L ^ m₁) (k + 1) N}
    (hΘ : Θ ∈ XiCRaw Gb (compWeight L a₁) ν (k + 1) 1 eps)
    {a b t₀ : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (ht : 0 < t₀) (htb : t₀ ≤ b)
    (hab : (a + b) * markedRad d L N k a₁ κ cψ cc < δ₁) {um : ℂ} (hum : ‖um‖ ≤ a)
    (Y : Set (CTorus d L N₁ m₁ (k + 1))) (Φ : ∀ b, (S.blockSplit mb hp).Ωb b) :
    ‖deriv (fun t : ℂ => evDecBg S.G' X₁f m₀ j 𝒦X Gb a₁ ν T cc F₁ Sol En Zm um t Y
        (Θ, T.res (S.hatOf mb ρ hp Φ))) 0‖ ≤ B Y / t₀ :=
  hcau a b t₀ ha hb ht htb hab um hum Y (Θ, S.hatOf mb ρ hp Φ)
    ⟨hΘ, fun p => (S.hatOf_mem mb hρ hp Φ p).trans hρc⟩

/-- **The fields of the mark derivative on a background generating set**: block locality,
continuity and measurability, the bound `B Y / t₀`, and analyticity in `(e, u)` on the admissible
parameters `physVBg` of `Gb`, for the mark derivative at the restricted clamped hat field of the
`mb`-block configuration, from the locality `hloc`, the Cauchy estimate `hcau`, the joint
analyticity `hJ2` of the terms on the chart of `Gb` and the analyticity `hJ4` of the derivative
marks on `physVBg`. -/
theorem deriv_evDecBg_hatOf_fields (mb : ℕ)
    {En : ((Gb.Ω 1 × Fin N → ℂ) × (Gb.Ω 1 → ℂ)) → (Hm.Ω 1 × Fin N → ℂ) →
      RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) → ℂ}
    {B : Set (CTorus d L N₁ m₁ (k + 1)) → ℝ}
    (hloc : ∀ um tm : ℂ, (‖um‖ + ‖tm‖) * markedRad d L N k a₁ κ cψ cc < δ₁ →
      ∀ Y, ∀ u ∈ XiCRaw Gb (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
        {ψh : unitPts S.G' × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ},
      ∀ u' ∈ XiCRaw Gb (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
        {ψh : unitPts S.G' × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ},
      AgHatDir S.hG' Y u u' →
        evDecBg S.G' X₁f m₀ j 𝒦X Gb a₁ ν T cc F₁ Sol En Zm um tm Y (u.1, T.res u.2) =
        evDecBg S.G' X₁f m₀ j 𝒦X Gb a₁ ν T cc F₁ Sol En Zm um tm Y (u'.1, T.res u'.2))
    (hcau : ∀ a b t₀ : ℝ, 0 ≤ a → 0 ≤ b → 0 < t₀ → t₀ ≤ b →
      (a + b) * markedRad d L N k a₁ κ cψ cc < δ₁ →
      ∀ um : ℂ, ‖um‖ ≤ a →
      ∀ Y, ∀ u ∈ XiCRaw Gb (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
        {ψh : unitPts S.G' × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ},
      ‖deriv (fun t : ℂ => evDecBg S.G' X₁f m₀ j 𝒦X Gb a₁ ν T cc F₁ Sol En Zm um t Y
          (u.1, T.res u.2)) 0‖ ≤ B Y / t₀)
    (hJ2 : ∀ Y, AnalyticOnNhd ℂ
        (fun p : (RawData d L (N₁ * L ^ m₁) (k + 1) N × (unitPts S.G' × Fin N → ℂ)) × (ℂ × ℂ) =>
          evDecBg S.G' X₁f m₀ j 𝒦X Gb a₁ ν T cc F₁ Sol En Zm p.2.1 p.2.2 Y (p.1.1, T.res p.1.2))
        ((XiCRaw Gb (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
          {ψh : unitPts S.G' × Fin N → ℂ | ∀ q, ‖ψh q‖ ≤ cψ}) ×ˢ
          {w : ℂ × ℂ | (‖w.1‖ + ‖w.2‖) * markedRad d L N k a₁ κ cψ cc < δ₁}))
    (hJ4 : ∀ Y, ∀ ψh : unitPts S.G' × Fin N → ℂ, (∀ q, ‖ψh q‖ ≤ cψ) →
        ∀ a b : ℝ, 0 ≤ a → 0 < b → (a + b) * markedRad d L N k a₁ κ cψ cc < δ₁ →
        AnalyticOnNhd ℂ (fun p : physParamBg N Gb × ℂ => deriv (fun t : ℂ =>
          evDecBg S.G' X₁f m₀ j 𝒦X Gb a₁ ν T cc F₁ Sol En Zm p.2 t Y
            ((p.1.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N), T.res ψh)) 0)
          (physVBg N Gb a₁ ν eps ×ˢ Metric.ball (0 : ℂ) a))
    {ρ : ℝ} (hρ : 0 < ρ) (hρc : ρ ≤ cψ) (hp : 0 < S.p₁) :
      (∀ (Y Y' : Set (CTorus d L N₁ m₁ (k + 1))), Y ⊆ Y' →
        (∀ y ∈ Y', box (cbase (cellSide L mb m₁ (k + 1)) y) (cellSide L mb m₁ (k + 1)) ⊆ Y') →
        ∀ Θ ∈ XiCRaw Gb (compWeight L a₁) ν (k + 1) 1 eps, ∀ um : ℂ,
        (‖um‖ + ‖(0 : ℂ)‖) * markedRad d L N k a₁ κ cψ cc < δ₁ →
        DepOn (blocksOf mb (k + 1) Set.univ Y')
          (fun Φ : ∀ b, (S.blockSplit mb hp).Ωb b =>
            deriv (fun t : ℂ => evDecBg S.G' X₁f m₀ j 𝒦X Gb a₁ ν T cc F₁ Sol En Zm um t Y
                (Θ, T.res (S.hatOf mb ρ hp Φ))) 0)) ∧
      (∀ Y, ∀ Θ ∈ XiCRaw Gb (compWeight L a₁) ν (k + 1) 1 eps, ∀ um : ℂ,
        (‖um‖ + ‖(0 : ℂ)‖) * markedRad d L N k a₁ κ cψ cc < δ₁ →
        Continuous (fun Φ : ∀ b, (S.blockSplit mb hp).Ωb b =>
          deriv (fun t : ℂ => evDecBg S.G' X₁f m₀ j 𝒦X Gb a₁ ν T cc F₁ Sol En Zm um t Y
              (Θ, T.res (S.hatOf mb ρ hp Φ))) 0) ∧
        Measurable (fun Φ : ∀ b, (S.blockSplit mb hp).Ωb b =>
          deriv (fun t : ℂ => evDecBg S.G' X₁f m₀ j 𝒦X Gb a₁ ν T cc F₁ Sol En Zm um t Y
              (Θ, T.res (S.hatOf mb ρ hp Φ))) 0)) ∧
      (∀ Y, ∀ Θ ∈ XiCRaw Gb (compWeight L a₁) ν (k + 1) 1 eps, ∀ a b t₀ : ℝ, 0 ≤ a → 0 ≤ b →
        0 < t₀ → t₀ ≤ b → (a + b) * markedRad d L N k a₁ κ cψ cc < δ₁ → ∀ um : ℂ, ‖um‖ ≤ a →
        ∀ Φ : (∀ b, (S.blockSplit mb hp).Ωb b),
        ‖deriv (fun t : ℂ => evDecBg S.G' X₁f m₀ j 𝒦X Gb a₁ ν T cc F₁ Sol En Zm um t Y
            (Θ, T.res (S.hatOf mb ρ hp Φ))) 0‖ ≤ B Y / t₀) ∧
      (∀ Y, ∀ Φ : (∀ b, (S.blockSplit mb hp).Ωb b), ∀ a b : ℝ, 0 ≤ a → 0 < b →
        (a + b) * markedRad d L N k a₁ κ cψ cc < δ₁ →
        AnalyticOnNhd ℂ (fun p : physParamBg N Gb × ℂ =>
          deriv (fun t : ℂ => evDecBg S.G' X₁f m₀ j 𝒦X Gb a₁ ν T cc F₁ Sol En Zm p.2 t Y
            ((p.1.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N), T.res (S.hatOf mb ρ hp Φ))) 0)
          (physVBg N Gb a₁ ν eps ×ˢ Metric.ball (0 : ℂ) a)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro Y Y' hYY hY' Θ hΘ um hum
    exact deriv_evDecBg_hatOf_dep S mb hloc hρ hρc hp hΘ hum hYY hY'
  · intro Y Θ hΘ um hum
    have hW : (um, (0 : ℂ)) ∈ {w : ℂ × ℂ |
        (‖w.1‖ + ‖w.2‖) * markedRad d L N k a₁ κ cψ cc < δ₁} := hum
    have hana := analyticOnNhd_deriv_mark (hJ2 Y)
    have hc : ContinuousOn (fun ψ : unitPts S.G' × Fin N → ℂ => deriv (fun t : ℂ =>
        evDecBg S.G' X₁f m₀ j 𝒦X Gb a₁ ν T cc F₁ Sol En Zm um t Y (Θ, T.res ψ)) 0)
        {ψh : unitPts S.G' × Fin N → ℂ | ∀ q, ‖ψh q‖ ≤ cψ} :=
      hana.continuousOn.comp (f := fun ψ : unitPts S.G' × Fin N → ℂ => ((Θ, ψ), um))
        (by fun_prop) (fun ψ hψ => ⟨⟨hΘ, hψ⟩, hW⟩)
    have hcont : Continuous (fun Φ : ∀ b, (S.blockSplit mb hp).Ωb b =>
        deriv (fun t : ℂ => evDecBg S.G' X₁f m₀ j 𝒦X Gb a₁ ν T cc F₁ Sol En Zm um t Y
            (Θ, T.res (S.hatOf mb ρ hp Φ))) 0) :=
      hc.comp_continuous (S.continuous_hatOf mb ρ hp)
        (fun Φ q => (S.hatOf_mem mb hρ hp Φ q).trans hρc)
    exact ⟨hcont, hcont.measurable⟩
  · intro Y Θ hΘ a b t₀ ha hb ht htb hab um hum Φ
    exact norm_deriv_evDecBg_hatOf_le S mb hcau hρ hρc hp hΘ ha hb ht htb hab hum Y Φ
  · intro Y Φ a b ha hb hab
    exact hJ4 Y (S.hatOf mb ρ hp Φ) (fun q => (S.hatOf_mem mb hρ hp Φ q).trans hρc) a b ha hb hab

/-- **Block locality of the mark on a background generating set** (`deriv_evDecBg_hatOf_dep` at
the block index `m₀` of the expansion). -/
theorem decMarkGBg_dep
    {En : ((Gb.Ω 1 × Fin N → ℂ) × (Gb.Ω 1 → ℂ)) → (Hm.Ω 1 × Fin N → ℂ) →
      RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) → ℂ}
    (hloc : ∀ um tm : ℂ, (‖um‖ + ‖tm‖) * markedRad d L N k a₁ κ cψ cc < δ₁ →
      ∀ Y, ∀ u ∈ XiCRaw Gb (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
        {ψh : unitPts S.G' × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ},
      ∀ u' ∈ XiCRaw Gb (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
        {ψh : unitPts S.G' × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ},
      AgHatDir S.hG' Y u u' →
        evDecBg S.G' X₁f m₀ j 𝒦X Gb a₁ ν T cc F₁ Sol En Zm um tm Y (u.1, T.res u.2) =
        evDecBg S.G' X₁f m₀ j 𝒦X Gb a₁ ν T cc F₁ Sol En Zm um tm Y (u'.1, T.res u'.2))
    {ρ : ℝ} (hρ : 0 < ρ) (hρc : ρ ≤ cψ) (hp : 0 < S.p₁)
    {Θ : RawData d L (N₁ * L ^ m₁) (k + 1) N}
    (hΘ : Θ ∈ XiCRaw Gb (compWeight L a₁) ν (k + 1) 1 eps)
    {um : ℂ} (hum : (‖um‖ + ‖(0 : ℂ)‖) * markedRad d L N k a₁ κ cψ cc < δ₁)
    {Y Y' : Set (CTorus d L N₁ m₁ (k + 1))} (hYY : Y ⊆ Y')
    (hY' : ∀ y ∈ Y', box (cbase (cellSide L m₀ m₁ (k + 1)) y) (cellSide L m₀ m₁ (k + 1)) ⊆ Y') :
    DepOn (blocksOf m₀ (k + 1) Set.univ Y')
      (decMarkGBg S Gb T X₁f m₀ j 𝒦X a₁ ν cc F₁ Sol En Zm Y ρ hp Θ um) :=
  deriv_evDecBg_hatOf_dep S m₀ hloc hρ hρc hp hΘ hum hYY hY'

/-- **The bound of the mark on a background generating set** (`norm_deriv_evDecBg_hatOf_le` at the
block index `m₀` of the expansion). -/
theorem norm_decMarkGBg_le
    {En : ((Gb.Ω 1 × Fin N → ℂ) × (Gb.Ω 1 → ℂ)) → (Hm.Ω 1 × Fin N → ℂ) →
      RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) → ℂ}
    {B : Set (CTorus d L N₁ m₁ (k + 1)) → ℝ}
    (hcau : ∀ a b t₀ : ℝ, 0 ≤ a → 0 ≤ b → 0 < t₀ → t₀ ≤ b →
      (a + b) * markedRad d L N k a₁ κ cψ cc < δ₁ →
      ∀ um : ℂ, ‖um‖ ≤ a →
      ∀ Y, ∀ u ∈ XiCRaw Gb (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
        {ψh : unitPts S.G' × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ},
      ‖deriv (fun t : ℂ => evDecBg S.G' X₁f m₀ j 𝒦X Gb a₁ ν T cc F₁ Sol En Zm um t Y
          (u.1, T.res u.2)) 0‖ ≤ B Y / t₀)
    {ρ : ℝ} (hρ : 0 < ρ) (hρc : ρ ≤ cψ) (hp : 0 < S.p₁)
    {Θ : RawData d L (N₁ * L ^ m₁) (k + 1) N}
    (hΘ : Θ ∈ XiCRaw Gb (compWeight L a₁) ν (k + 1) 1 eps)
    {a b t₀ : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (ht : 0 < t₀) (htb : t₀ ≤ b)
    (hab : (a + b) * markedRad d L N k a₁ κ cψ cc < δ₁) {um : ℂ} (hum : ‖um‖ ≤ a)
    (Y : Set (CTorus d L N₁ m₁ (k + 1))) (Φ : ∀ b, (S.blockSplit m₀ hp).Ωb b) :
    ‖decMarkGBg S Gb T X₁f m₀ j 𝒦X a₁ ν cc F₁ Sol En Zm Y ρ hp Θ um Φ‖ ≤ B Y / t₀ :=
  norm_deriv_evDecBg_hatOf_le S m₀ hcau hρ hρc hp hΘ ha hb ht htb hab hum Y Φ

end BlocksBg

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

/-- **Core of `decMarkG_dep`, for any functional `En` and any block index `mb`.**  From the locality
`hloc` of the marked terms of `En` (the form of clause 2 of `MarkedBlockExpansionDecPair`): for a
label `Y′ ⊇ Y` that is a union of `mb`-cells, the mark derivative at the clamped hat field of the
`mb`-block configuration, `Φ ↦ ∂_t evDec … En … um t Y (Θ, S.hatOf mb ρ hp Φ)|_{t=0}`, depends only
on the blocks inside `Y′`.  (`decMarkG` is the case `mb = m₀`.) -/
theorem deriv_evDec_hatOf_dep (mb : ℕ)
    {En : ((S.G'.Ω 1 × Fin N → ℂ) × (S.G'.Ω 1 → ℂ)) → (Hm.Ω 1 × Fin N → ℂ) →
      RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) → ℂ}
    (hloc : ∀ um tm : ℂ, (‖um‖ + ‖tm‖) * markedRad d L N k a₁ κ cψ cc < δ₁ →
      ∀ Y, ∀ u ∈ XiCRaw S.G' (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
        {ψh : unitPts S.G' × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ},
      ∀ u' ∈ XiCRaw S.G' (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
        {ψh : unitPts S.G' × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ},
      AgHatDir S.hG' Y u u' →
        evDec X₁f m₀ j 𝒦X a₁ ν S.hG' cc F₁ Sol En Zm um tm Y u =
        evDec X₁f m₀ j 𝒦X a₁ ν S.hG' cc F₁ Sol En Zm um tm Y u')
    {ρ : ℝ} (hρ : 0 < ρ) (hρc : ρ ≤ cψ) (hp : 0 < S.p₁)
    {Θ : RawData d L (N₁ * L ^ m₁) (k + 1) N}
    (hΘ : Θ ∈ XiCRaw S.G' (compWeight L a₁) ν (k + 1) 1 eps)
    {um : ℂ} (hum : (‖um‖ + ‖(0 : ℂ)‖) * markedRad d L N k a₁ κ cψ cc < δ₁)
    {Y Y' : Set (CTorus d L N₁ m₁ (k + 1))} (hYY : Y ⊆ Y')
    (hY' : ∀ y ∈ Y', box (cbase (cellSide L mb m₁ (k + 1)) y) (cellSide L mb m₁ (k + 1)) ⊆ Y') :
    DepOn (blocksOf mb (k + 1) Set.univ Y')
      (fun Φ : ∀ b, (S.blockSplit mb hp).Ωb b =>
        deriv (fun t : ℂ => evDec X₁f m₀ j 𝒦X a₁ ν S.hG' cc F₁ Sol En Zm um t Y
            (Θ, S.hatOf mb ρ hp Φ)) 0) :=
  deriv_evDecBg_hatOf_dep S mb (T := BgTransport.self S.hG') hloc hρ hρc hp hΘ hum hYY hY'

/-- **Core of `norm_decMarkG_le`, for any functional `En` and any block index `mb`.**  From a Cauchy
estimate `hcau` of the mark derivatives of `En` with a bound `B Y` (the form of clause 5 of
`MarkedBlockExpansionDecPair`): the mark derivative at the clamped hat field of every
`mb`-block configuration `Φ` is bounded by `B Y / t₀`. -/
theorem norm_deriv_evDec_hatOf_le (mb : ℕ)
    {En : ((S.G'.Ω 1 × Fin N → ℂ) × (S.G'.Ω 1 → ℂ)) → (Hm.Ω 1 × Fin N → ℂ) →
      RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) → ℂ}
    {B : Set (CTorus d L N₁ m₁ (k + 1)) → ℝ}
    (hcau : ∀ a b t₀ : ℝ, 0 ≤ a → 0 ≤ b → 0 < t₀ → t₀ ≤ b →
      (a + b) * markedRad d L N k a₁ κ cψ cc < δ₁ →
      ∀ um : ℂ, ‖um‖ ≤ a →
      ∀ Y, ∀ u ∈ XiCRaw S.G' (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
        {ψh : unitPts S.G' × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ},
      ‖deriv (fun t : ℂ => evDec X₁f m₀ j 𝒦X a₁ ν S.hG' cc F₁ Sol En Zm um t Y u) 0‖ ≤
        B Y / t₀)
    {ρ : ℝ} (hρ : 0 < ρ) (hρc : ρ ≤ cψ) (hp : 0 < S.p₁)
    {Θ : RawData d L (N₁ * L ^ m₁) (k + 1) N}
    (hΘ : Θ ∈ XiCRaw S.G' (compWeight L a₁) ν (k + 1) 1 eps)
    {a b t₀ : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (ht : 0 < t₀) (htb : t₀ ≤ b)
    (hab : (a + b) * markedRad d L N k a₁ κ cψ cc < δ₁) {um : ℂ} (hum : ‖um‖ ≤ a)
    (Y : Set (CTorus d L N₁ m₁ (k + 1))) (Φ : ∀ b, (S.blockSplit mb hp).Ωb b) :
    ‖deriv (fun t : ℂ => evDec X₁f m₀ j 𝒦X a₁ ν S.hG' cc F₁ Sol En Zm um t Y
        (Θ, S.hatOf mb ρ hp Φ)) 0‖ ≤ B Y / t₀ :=
  norm_deriv_evDecBg_hatOf_le S mb (T := BgTransport.self S.hG') hcau hρ hρc hp hΘ ha hb ht htb
    hab hum Y Φ

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
        Y ρ hp Θ um) :=
  deriv_evDec_hatOf_dep S m₀ hP.2.1 hρ hρc hp hΘ hum hYY hY'

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
  norm_deriv_evDec_hatOf_le S m₀ (B := fun Y => energyBdScaled d L N (compWeight L a₁) k
      (cK2' d L N (famConst d L BG₂ κ) * δ₁) δ₁ (rho4 d L N BG κ) *
      Real.exp (-2 * κdec * treeLenCov S.G' m₀ Y)) hP.2.2.2.2.1 hρ hρc hp hΘ ha hb ht htb hab
    hum Y Φ

/-- **Core of `decMarkG_fields_of_pair`, for any functional `En` and any block index `mb`.**  The
four field conclusions (block locality, continuity and measurability, the bound `B Y / t₀`,
analyticity in `(e, u)`) for the mark derivative at the clamped hat field of the `mb`-block configuration,
`Φ ↦ ∂_t evDec … En … um t Y (Θ, S.hatOf mb ρ hp Φ)|_{t=0}`, for a pair `(F₁, Sol)` and a functional
`En` whose marked terms are local (`hloc`, the form of clause 2 of `MarkedBlockExpansionDecPair`),
satisfy a Cauchy estimate with the bound `B` (`hcau`, the form of clause 5), are jointly analytic on
the chart (`hJ2`) and have analytic derivative marks on `physV` (`hJ4`).  (`decMarkG` is the case
`mb = m₀`.) -/
theorem deriv_evDec_hatOf_fields (mb : ℕ)
    (F₁ : DecParams S.G' × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      (S.G'.Ω 1 × Fin N → ℂ) × (S.G'.Ω 1 → ℂ))
    (Sol : Dec2.DecParams (coverOf S.G') × Edat Hm N → (Hm.Ω 1 × Fin N → ℂ) × (Hm.Ω 1 → ℂ))
    {En : ((S.G'.Ω 1 × Fin N → ℂ) × (S.G'.Ω 1 → ℂ)) → (Hm.Ω 1 × Fin N → ℂ) →
      RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) → ℂ}
    {B : Set (CTorus d L N₁ m₁ (k + 1)) → ℝ}
    (hloc : ∀ um tm : ℂ, (‖um‖ + ‖tm‖) * markedRad d L N k a₁ κ cψ cc < δ₁ →
      ∀ Y, ∀ u ∈ XiCRaw S.G' (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
        {ψh : unitPts S.G' × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ},
      ∀ u' ∈ XiCRaw S.G' (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
        {ψh : unitPts S.G' × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ},
      AgHatDir S.hG' Y u u' →
        evDec X₁f m₀ j 𝒦X a₁ ν S.hG' cc F₁ Sol En Zm um tm Y u =
        evDec X₁f m₀ j 𝒦X a₁ ν S.hG' cc F₁ Sol En Zm um tm Y u')
    (hcau : ∀ a b t₀ : ℝ, 0 ≤ a → 0 ≤ b → 0 < t₀ → t₀ ≤ b →
      (a + b) * markedRad d L N k a₁ κ cψ cc < δ₁ →
      ∀ um : ℂ, ‖um‖ ≤ a →
      ∀ Y, ∀ u ∈ XiCRaw S.G' (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
        {ψh : unitPts S.G' × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ},
      ‖deriv (fun t : ℂ => evDec X₁f m₀ j 𝒦X a₁ ν S.hG' cc F₁ Sol En Zm um t Y u) 0‖ ≤
        B Y / t₀)
    (hJ2 : ∀ Y, AnalyticOnNhd ℂ
        (fun p : (RawData d L (N₁ * L ^ m₁) (k + 1) N × (unitPts S.G' × Fin N → ℂ)) × (ℂ × ℂ) =>
          evDec X₁f m₀ j 𝒦X a₁ ν S.hG' cc F₁ Sol
            En Zm p.2.1 p.2.2 Y p.1)
        ((XiCRaw S.G' (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
          {ψh : unitPts S.G' × Fin N → ℂ | ∀ q, ‖ψh q‖ ≤ cψ}) ×ˢ
          {w : ℂ × ℂ | (‖w.1‖ + ‖w.2‖) * markedRad d L N k a₁ κ cψ cc < δ₁}))
    (hJ4 : ∀ Y, ∀ ψh : unitPts S.G' × Fin N → ℂ, (∀ q, ‖ψh q‖ ≤ cψ) →
        ∀ a b : ℝ, 0 ≤ a → 0 < b → (a + b) * markedRad d L N k a₁ κ cψ cc < δ₁ →
        AnalyticOnNhd ℂ (fun p : physParam N S × ℂ => deriv (fun t : ℂ =>
          evDec X₁f m₀ j 𝒦X a₁ ν S.hG' cc F₁ Sol
            En Zm p.2 t Y
            ((p.1.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N), ψh)) 0)
          (physV S a₁ ν eps ×ˢ Metric.ball (0 : ℂ) a))
    {ρ : ℝ} (hρ : 0 < ρ) (hρc : ρ ≤ cψ) (hp : 0 < S.p₁) :
      (∀ (Y Y' : Set (CTorus d L N₁ m₁ (k + 1))), Y ⊆ Y' →
        (∀ y ∈ Y', box (cbase (cellSide L mb m₁ (k + 1)) y) (cellSide L mb m₁ (k + 1)) ⊆ Y') →
        ∀ Θ ∈ XiCRaw S.G' (compWeight L a₁) ν (k + 1) 1 eps, ∀ um : ℂ,
        (‖um‖ + ‖(0 : ℂ)‖) * markedRad d L N k a₁ κ cψ cc < δ₁ →
        DepOn (blocksOf mb (k + 1) Set.univ Y')
          (fun Φ : ∀ b, (S.blockSplit mb hp).Ωb b =>
            deriv (fun t : ℂ => evDec X₁f m₀ j 𝒦X a₁ ν S.hG' cc F₁ Sol En Zm um t Y
                (Θ, S.hatOf mb ρ hp Φ)) 0)) ∧
      (∀ Y, ∀ Θ ∈ XiCRaw S.G' (compWeight L a₁) ν (k + 1) 1 eps, ∀ um : ℂ,
        (‖um‖ + ‖(0 : ℂ)‖) * markedRad d L N k a₁ κ cψ cc < δ₁ →
        Continuous (fun Φ : ∀ b, (S.blockSplit mb hp).Ωb b =>
          deriv (fun t : ℂ => evDec X₁f m₀ j 𝒦X a₁ ν S.hG' cc F₁ Sol En Zm um t Y
              (Θ, S.hatOf mb ρ hp Φ)) 0) ∧
        Measurable (fun Φ : ∀ b, (S.blockSplit mb hp).Ωb b =>
          deriv (fun t : ℂ => evDec X₁f m₀ j 𝒦X a₁ ν S.hG' cc F₁ Sol En Zm um t Y
              (Θ, S.hatOf mb ρ hp Φ)) 0)) ∧
      (∀ Y, ∀ Θ ∈ XiCRaw S.G' (compWeight L a₁) ν (k + 1) 1 eps, ∀ a b t₀ : ℝ, 0 ≤ a → 0 ≤ b →
        0 < t₀ → t₀ ≤ b → (a + b) * markedRad d L N k a₁ κ cψ cc < δ₁ → ∀ um : ℂ, ‖um‖ ≤ a →
        ∀ Φ : (∀ b, (S.blockSplit mb hp).Ωb b),
        ‖deriv (fun t : ℂ => evDec X₁f m₀ j 𝒦X a₁ ν S.hG' cc F₁ Sol En Zm um t Y
            (Θ, S.hatOf mb ρ hp Φ)) 0‖ ≤ B Y / t₀) ∧
      (∀ Y, ∀ Φ : (∀ b, (S.blockSplit mb hp).Ωb b), ∀ a b : ℝ, 0 ≤ a → 0 < b →
        (a + b) * markedRad d L N k a₁ κ cψ cc < δ₁ →
        AnalyticOnNhd ℂ (fun p : physParam N S × ℂ =>
          deriv (fun t : ℂ => evDec X₁f m₀ j 𝒦X a₁ ν S.hG' cc F₁ Sol En Zm p.2 t Y
            ((p.1.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N), S.hatOf mb ρ hp Φ)) 0)
          (physV S a₁ ν eps ×ˢ Metric.ball (0 : ℂ) a)) :=
  deriv_evDecBg_hatOf_fields S mb (T := BgTransport.self S.hG') hloc hcau hJ2 hJ4 hρ hρc hp

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
          (physV S a₁ ν eps ×ˢ Metric.ball (0 : ℂ) a)) :=
  deriv_evDec_hatOf_fields S m₀ F₁ Sol (B := fun Y => energyBdScaled d L N (compWeight L a₁) k
      (cK2' d L N (famConst d L BG₂ κ) * δ₁) δ₁ (rho4 d L N BG κ) *
      Real.exp (-2 * κdec * treeLenCov S.G' m₀ Y)) hP.2.1 hP.2.2.2.2.1 hJ2 hJ4 hρ hρc hp

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
