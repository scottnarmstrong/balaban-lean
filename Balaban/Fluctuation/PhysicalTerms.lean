/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.HatLabelsDm
public import Balaban.Fluctuation.HatLabelsDirect
public import Balaban.Fluctuation.SharpAE

/-!
# The physical expansion as `HatTerms` and (conditionally) as `DirectTerms`

`notes/phase1/SPLIT.md` §1 observes that no landed theorem packages the hypotheses of
`interaction_expansion_hat` as label terms.  This file does it.

* `PhysExpansion 𝒴 T` is the conclusion of `interaction_expansion_hat_dm` for the witnesses `𝒴`,
  `T`; `physExpansion_exists` says that witnesses exist under the hypotheses of
  `labelAct_of_interaction_expansion_hat`.
* `physical_hatTerms` (unconditional): the physical expansion is a `HatTerms`, for the landed
  thick-label route.  `labelAct_of_physical_hatTerms` is `labelAct_of_hatTerms` applied to it.
* `AgFDirPair` is the sharp agreement of both coordinates of a pair of rays: equality of the hat
  variables at the unit points of the sites of `Y` itself.
* `physAgΘ` is the agreement relation of the data of the direct terms: the raw datum and the source
  agree on `Y` itself.  `physAgΘThick` (raw datum on the thickening `thickSet Y`) is the relation of
  the thick legacy route (`PhysExpansion`, `physicalHatTerms`, `physical_hatTerms`);
  `physAgΘ_of_thick` says that thick agreement implies agreement on `Y`.
* `PhysicalSharpLoc 𝒴 T` is the sharp locality of the terms `T`: the `LocInt.loc` field for
  `physAgΘ` and `AgFDirPair`.  Nothing in this file proves sharp locality of the physical terms; it
  is an explicit hypothesis here, and the declarations that use it carry `of_sharpLoc` in their
  names.  It is proved in `SharpAssembly` (`interaction_expansion_hat_dm_dir`).
* `physicalDirectTerms_of_sharpLoc`: given `PhysicalSharpLoc 𝒴 T` for a physical witness, a
  `DirectTerms` instance.  The field `ag` is proved here (the cell-union property of a label is
  derived from `IsDj`), and `labelAct_of_physical_directTerms_of_sharpLoc` feeds it to
  `labelAct_of_directTerms`.

Since the witnesses `𝒴`, `T` of the landed expansion are obtained existentially, the sharp
locality hypothesis is stated for a given physical witness `(𝒴, T)`.
-/

@[expose] public section

namespace Balaban.Fluctuation

open MeasureTheory Balaban Balaban.Localization Balaban.Multiscale Balaban.Polymer
  Balaban.Background Balaban.SmallField Balaban.Analysis Finset Matrix Set Metric

section PhysicalTerms

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱm : ℝ}
variable {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}
variable {a₁ ν c BG κ eps : ℝ}

/-- The set of admissible parameters of the physical expansion. -/
def physSΛ (S : StepSetting d L N₁ m₁ k N ϱ) (a₁ ν eps : ℝ) :
    Set (RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ)) :=
  XiCRaw S.G' (compWeight L a₁) ν (k + 1) 1 eps ×ˢ l1Ball d L N₁ m₁ (k + 1) N

/-- The admissible pairs of rays of the physical expansion. -/
def physXW (S : StepSetting d L N₁ m₁ k N ϱ) (cψ R₁ Rσ r : ℝ) :
    Set (((unitPts S.G' × Fin N → ℂ) × (unitPts S.G' × Fin N → ℂ)) ×
      ((unitPts S.G' × Fin N → ℂ) × (unitPts S.G' × Fin N → ℂ))) :=
  {xw | (xw.1.1, xw.2.1) ∈ HatRaysO S.G' cψ R₁ Rσ r ∧ (xw.1.2, xw.2.2) ∈ HatRaysO S.G' cψ R₁ Rσ r}

/-- The agreement relation of the source data in the physical expansion: the raw datum and the
source agree on `Y` itself.  (The terms of the direct expansion with domain `Y` read the raw datum
and the source only at the sites of `Y`; the weaker statement with the raw datum on the thickening
`thickSet Y` is `physAgΘThick`.) -/
def physAgΘ (_S : StepSetting d L N₁ m₁ k N ϱ) (Y : Set (CTorus d L N₁ m₁ (k + 1)))
    (p p' : RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ)) : Prop :=
  agreeOn Y p.1 p'.1 ∧ ∀ x ∈ Y, p.2 x = p'.2 x

/-- The thick agreement relation of the source data: raw data agreeing on the thickening
`thickSet Y` of `Y`, sources agreeing on `Y`.  It is the relation of the landed thick-label route
(`PhysExpansion`, `physicalHatTerms`); the relation of the direct terms is `physAgΘ`. -/
def physAgΘThick (S : StepSetting d L N₁ m₁ k N ϱ) (Y : Set (CTorus d L N₁ m₁ (k + 1)))
    (p p' : RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ)) : Prop :=
  agreeOn (thickSet S.G' Y) p.1 p'.1 ∧ ∀ x ∈ Y, p.2 x = p'.2 x

/-- Thick agreement implies agreement on `Y` itself (`Y ⊆ thickSet Y`). -/
theorem physAgΘ_of_thick (S : StepSetting d L N₁ m₁ k N ϱ) {Y : Set (CTorus d L N₁ m₁ (k + 1))}
    {p p' : RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ)}
    (h : physAgΘThick S Y p p') : physAgΘ S Y p p' :=
  ⟨agreeOn_mono (fun _ hx => Or.inl hx) h.1, h.2⟩

/-- The landed paired agreement relation of the terms: `AgHatF` (thickened agreement) in both
coordinates of the pair. -/
def AgFPair (S : StepSetting d L N₁ m₁ k N ϱ) (Y : Set (CTorus d L N₁ m₁ (k + 1)))
    (a a' : (unitPts S.G' × Fin N → ℂ) × (unitPts S.G' × Fin N → ℂ)) : Prop :=
  AgHatF S.G' S.hG' Y a.1 a'.1 ∧ AgHatF S.G' S.hG' Y a.2 a'.2

/-- **The paired sharp agreement relation** (`AgF_dir` of `SPLIT.md` §1): equality of the hat
variables at the unit points of the sites of `Y` itself, in both coordinates of the pair. -/
def AgFDirPair (S : StepSetting d L N₁ m₁ k N ϱ) (Y : Set (CTorus d L N₁ m₁ (k + 1)))
    (a a' : (unitPts S.G' × Fin N → ℂ) × (unitPts S.G' × Fin N → ℂ)) : Prop :=
  AgHatFDir S.hG' Y a.1 a'.1 ∧ AgHatFDir S.hG' Y a.2 a'.2

theorem agFDirPair_mono (S : StepSetting d L N₁ m₁ k N ϱ) {Y Y' : Set (CTorus d L N₁ m₁ (k + 1))}
    (h : Y ⊆ Y') {a a' : (unitPts S.G' × Fin N → ℂ) × (unitPts S.G' × Fin N → ℂ)}
    (ha : AgFDirPair S Y' a a') : AgFDirPair S Y a a' :=
  ⟨agHatFDir_mono S.hG' h ha.1, agHatFDir_mono S.hG' h ha.2⟩

/-- The landed paired agreement implies the sharp one. -/
theorem agFDirPair_of_agFPair (S : StepSetting d L N₁ m₁ k N ϱ)
    {Y : Set (CTorus d L N₁ m₁ (k + 1))}
    {a a' : (unitPts S.G' × Fin N → ℂ) × (unitPts S.G' × Fin N → ℂ)}
    (ha : AgFPair S Y a a') : AgFDirPair S Y a a' :=
  ⟨fun y hy i => ha.1 y (psiThick_subset_blockThick Y (Or.inl hy)) i,
   fun y hy i => ha.2 y (psiThick_subset_blockThick Y (Or.inl hy)) i⟩

/-- The terms of the physical expansion are local for the sharp relations: the `LocInt.loc` field
for `physAgΘ` (raw datum and source on `Y` itself) and `AgFDirPair` (hat variables at the unit points
of `Y`), for arbitrary admissible pairs of rays and two source data.  It is proved for the assembled
terms in `interaction_expansion_hat_dm_dir`. -/
def PhysicalSharpLoc (S : StepSetting d L N₁ m₁ k N ϱ) (cψ R₁ Rσ r a₁ ν eps : ℝ)
    (𝒴 : Finset (Set (CTorus d L N₁ m₁ (k + 1))))
    (T : Set (CTorus d L N₁ m₁ (k + 1)) →
      ((unitPts S.G' × Fin N → ℂ) × (unitPts S.G' × Fin N → ℂ)) →
      ((unitPts S.G' × Fin N → ℂ) × (unitPts S.G' × Fin N → ℂ)) → ℂ →
      RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) → ℂ) :
    Prop :=
  ∀ Y ∈ 𝒴, ∀ xw ∈ physXW S cψ R₁ Rσ r, ∀ xw' ∈ physXW S cψ R₁ Rσ r, ∀ σ : ℂ, ‖σ‖ < Rσ →
    ∀ Θ ∈ physSΛ S a₁ ν eps, ∀ Θ' ∈ physSΛ S a₁ ν eps, physAgΘ S Y Θ Θ' →
    AgFDirPair S Y xw.1 xw'.1 → AgFDirPair S Y xw.2 xw'.2 →
    T Y xw.1 xw.2 σ Θ = T Y xw'.1 xw'.2 σ Θ'

/-- `PhysicalSharpLoc` holds for the empty family of labels (so the hypothesis is not
contradictory). -/
theorem physicalSharpLoc_empty (S : StepSetting d L N₁ m₁ k N ϱ) (cψ R₁ Rσ r a₁ ν eps : ℝ)
    (T : Set (CTorus d L N₁ m₁ (k + 1)) →
      ((unitPts S.G' × Fin N → ℂ) × (unitPts S.G' × Fin N → ℂ)) →
      ((unitPts S.G' × Fin N → ℂ) × (unitPts S.G' × Fin N → ℂ)) → ℂ →
      RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) → ℂ) :
    PhysicalSharpLoc S cψ R₁ Rσ r a₁ ν eps ∅ T :=
  fun _ hY => absurd hY (Finset.notMem_empty _)

/-- **Cell-union property of a label.**  For a domain `Y ∈ 𝒟_{k+1}` and `L ^ m₀ ∣ N₁`, every
`m₀`-cell containing a site of `Y` lies in `Y`. -/
theorem cell_subset_of_isDj {m₀ : ℕ} (hN : L ^ m₀ ∣ N₁) {Y : Set (CTorus d L N₁ m₁ (k + 1))}
    (hY : IsDj m₀ (k + 1) Y) :
    ∀ y ∈ Y, box (cbase (cellSide L m₀ m₁ (k + 1)) y) (cellSide L m₀ m₁ (k + 1)) ⊆ Y := by
  intro y hy
  obtain ⟨b, hb, hyb, hbY⟩ := hY.2.1 y hy
  exact (cell_subset_cube (cellSide_dvd (K := k + 1) (m₁ := m₁) hN le_rfl)
    (cellSide_pos (L := L) m₀ m₁ (k + 1)) hb hyb).trans hbY

/-- **The hat variable of block variables is sharply local.**  If every `m₀`-cell containing a
site of `Y` lies in `Y`, block configurations that agree on the blocks inside `Y` have hat
variables that agree at the unit points of the sites of `Y` (`AgHatFDir`). -/
theorem StepSetting.agHatFDir_hatOf (S : StepSetting d L N₁ m₁ k N ϱ) (m₀ : ℕ)
    {Y : Set (CTorus d L N₁ m₁ (k + 1))}
    (hY : ∀ y ∈ Y, box (cbase (cellSide L m₀ m₁ (k + 1)) y) (cellSide L m₀ m₁ (k + 1)) ⊆ Y)
    (ρ : ℝ) (hp : 0 < S.p₁) (Φ Φ' : ∀ b, (S.blockSplit m₀ hp).Ωb b)
    (h : ∀ b ∈ blocksOf m₀ (k + 1) Set.univ Y, Φ b = Φ' b) :
    AgHatFDir S.hG' Y (S.hatOf m₀ ρ hp Φ) (S.hatOf m₀ ρ hp Φ') := by
  intro y hy i
  have hcube : S.cellOf m₀ (unitPt S.hG' y) ∈ blocksOf m₀ (k + 1) Set.univ Y := by
    rw [S.cellOf_unitPt]
    exact mem_blocksOf.2 (hY y hy)
  have := h _ hcube
  simp only [StepSetting.hatOf]
  rw [this]

variable (S : StepSetting d L N₁ m₁ k N ϱ)
    {ρ εU : ℝ} {Kc Cx c₂ BG₂ δ₁ : ℝ}
    (hC : FlCore N S.G' Hm a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁) (cβ : ℂ)
    (hconn : HatConn S.G') (hrow : RowInHat (coverOf S.G') Hm (compWeight L a₁) ν)
    {κdec κ₀ : ℝ} (hκ₀ : 0 ≤ κ₀) (hκdec : 3 * κ₀ + 3 ≤ κdec)
    (hκ : 4 * d * (((2 * L + 1) ^ d : ℕ) : ℝ) * κdec ≤ κ) (h1 : 1 ≤ (κ / 2 - 1) / 2)
    {R₁ : ℝ} (hR₁ : 1 < R₁) {r Rσ : ℝ} (hr : 0 < r)
    -- the hat variable
    (hk : 1 ≤ k) (hG : IsLevel Hm k) (cc : ℂ)
    {cψ : ℝ} (hcψ : 0 ≤ cψ)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δc : ℝ}
    (hdm : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsmX : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    (hδ₁ : Real.sqrt N * (‖cc‖ * (covSupConstC d L N (compWeight L a₁ k) κ * cψ)) < δ₁)
    -- the potential part
    (ha₁ : 0 < a₁)
    (H : BgHyp d L (k + 1) ϱm (compWeight L a₁) ν) (hc7 : c7 d L N BG κ ≤ thm73C3 d L N)
    {R : ℝ} (hR : 2 ≤ R) (hRs : R * δ₁ ≤ deltaStar d L N)
    (hsmall : cK2 d L N * (R * δ₁) < bgC0 d L N / 2)
    (hnum : cK2 d L N * δ₁ ≤ c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8))
    (hnum' : cK2' d L N (famConst d L BG₂ κ) * δ₁ ≤
      c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8))
    (hsm : 2 * (compC4 d * (bgK1 d L N * (xiC1 d * eps))) + 5 * (R * δ₁) ≤ bgC1 d L N)
    {m₀ : ℕ} {jV : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) → ℕ}
    {XV 𝒦XV : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) → Set (CTorus d L N₁ m₁ (k + 1))}
    {X₁V : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) → Finset (CTorus d L N₁ m₁ (k + 1))}
    (hcovV : ∀ z, CovSetup S.G' (m₀) (jV z) (XV z) (𝒦XV z))
    (hX₁V : ∀ z, (↑(X₁V z) : Set (CTorus d L N₁ m₁ (k + 1))) = X1 S.G' (m₀) (jV z) (𝒦XV z))
    (hoptV : ∀ z, ∃ (W₀ : Finset (CTorus d L N₁ m₁ (k + 1)))
      (E₀ : Finset (CTorus d L N₁ m₁ (k + 1) × CTorus d L N₁ m₁ (k + 1))),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ XV z) ∧ MeetsOne (m₀) (jV z) (𝒦XV z) W₀ ∧
        bondCost (scaleW L (m₀) m₁ (jV z)) E₀ = treeLenCovOne (m₀) (jV z) (XV z))
    (hΔV : ∀ z, treeLenCovOne (m₀) (jV z) (XV z) = 0)
    (hlogV : ∀ _z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))), Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) * (((L ^ m₀) ^ d : ℕ) : ℝ)) ≤
      (κ / 2 - 1) / 2)
    (hZV : ∀ z, readSites Hm k z ⊆ ↑(X₁V z))
    (hmarV : ∀ z, BlockMargin S.G' (X₁V z)
      (↑(blockSites d L N₁ m₁ (k + 1) k z) : Set (CTorus d L N₁ m₁ (k + 1))))
    -- the old terms
    {τι : Type*} [DecidableEq τι] (𝒯E : Finset τι) {ϱ₁ ϱ₂ : τι → ℝ}
    {GkE : ∀ τ, GeneratingSet d L (N₁ * L ^ m₁) (k + 1) (ϱ₁ τ)}
    {GjE : ∀ τ, GeneratingSet d L (N₁ * L ^ m₁) (k + 1) (ϱ₂ τ)} {r₀ δ₃ δfl : ℝ}
    {X₀E X₁E : τι → Finset (CTorus d L N₁ m₁ (k + 1))} {jE : τι → ℕ}
    {XE 𝒦XE : τι → Set (CTorus d L N₁ m₁ (k + 1))} {EbE : τι → ℝ}
    (hBE : ∀ τ ∈ 𝒯E, BgSetting N S.G' (GkE τ) (GjE τ) a₁ ν c BG κ r₀ eps δ₃ (X₀E τ) (X₁E τ) (jE τ))
    (hFE : ∀ τ ∈ 𝒯E, FlSetting N S.G' (GkE τ) Hm a₁ ν κ BG eps δ₃ Kc Cx c₂ BG₂ δ₁ δfl (X₁E τ))
    (hcovE : ∀ τ ∈ 𝒯E, CovSetup S.G' (m₀) (jE τ) (XE τ) (𝒦XE τ))
    (hX₁E : ∀ τ ∈ 𝒯E, (↑(X₁E τ) : Set (CTorus d L N₁ m₁ (k + 1))) = X1 S.G' (m₀) (jE τ) (𝒦XE τ))
    (hoptE : ∀ τ ∈ 𝒯E, ∃ (W₀ : Finset (CTorus d L N₁ m₁ (k + 1)))
      (E₀ : Finset (CTorus d L N₁ m₁ (k + 1) × CTorus d L N₁ m₁ (k + 1))),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ XE τ) ∧ MeetsOne (m₀) (jE τ) (𝒦XE τ) W₀ ∧
        bondCost (scaleW L (m₀) m₁ (jE τ)) E₀ = treeLenCovOne (m₀) (jE τ) (XE τ))
    (hlogE : ∀ τ ∈ 𝒯E, Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) *
      (((L ^ m₀) ^ d : ℕ) : ℝ)) ≤ (κ / 2 - 1) / 2)
    (hEbE : ∀ τ ∈ 𝒯E, 0 ≤ EbE τ) {EE : τι → RawData d L (N₁ * L ^ m₁) (k + 1) N → ℂ}
    (hEanE : ∀ τ ∈ 𝒯E, AnalyticOnNhd ℂ (EE τ) (XiCRaw (GjE τ) (compWeight L a₁) ν (jE τ)
      (scaledC0 d) (scaledC0 d ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl)))
    (hEbdE : ∀ τ ∈ 𝒯E, ∀ r ∈ XiCRaw (GjE τ) (compWeight L a₁) ν (jE τ) (scaledC0 d)
      (scaledC0 d ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl),
      ‖EE τ r‖ ≤ EbE τ * Real.exp (-(κdec - 1) * treeLenCovOne (m₀) (jE τ) (XE τ)))
    -- the sites of the source
    {jF : CTorus d L N₁ m₁ (k + 1) × Fin N → ℕ}
    {XF 𝒦XF : CTorus d L N₁ m₁ (k + 1) × Fin N → Set (CTorus d L N₁ m₁ (k + 1))}
    {X₁F : CTorus d L N₁ m₁ (k + 1) × Fin N → Finset (CTorus d L N₁ m₁ (k + 1))}
    (hcovF : ∀ s, CovSetup S.G' (m₀) (jF s) (XF s) (𝒦XF s))
    (hX₁F : ∀ s, (↑(X₁F s) : Set (CTorus d L N₁ m₁ (k + 1))) = X1 S.G' (m₀) (jF s) (𝒦XF s))
    (hoptF : ∀ s, ∃ (W₀ : Finset (CTorus d L N₁ m₁ (k + 1)))
      (E₀ : Finset (CTorus d L N₁ m₁ (k + 1) × CTorus d L N₁ m₁ (k + 1))),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ XF s) ∧ MeetsOne (m₀) (jF s) (𝒦XF s) W₀ ∧
        bondCost (scaleW L (m₀) m₁ (jF s)) E₀ = treeLenCovOne (m₀) (jF s) (XF s))
    (hΔF : ∀ s, treeLenCovOne (m₀) (jF s) (XF s) = 0)
    (hlogF : ∀ _s : CTorus d L N₁ m₁ (k + 1) × Fin N, Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) * (((L ^ m₀) ^ d : ℕ) : ℝ)) ≤
      (κ / 2 - 1) / 2)
    (hyF : ∀ s : CTorus d L N₁ m₁ (k + 1) × Fin N, s.1 ∈ X₁F s)
    -- the observable terms
    {μι : Type*} [DecidableEq μι] (𝒯M : Finset μι) {ϱ₁M ϱ₂M : μι → ℝ}
    {GkM : ∀ τ, GeneratingSet d L (N₁ * L ^ m₁) (k + 1) (ϱ₁M τ)}
    {GjM : ∀ τ, GeneratingSet d L (N₁ * L ^ m₁) (k + 1) (ϱ₂M τ)}
    {X₀M X₁M : μι → Finset (CTorus d L N₁ m₁ (k + 1))} {jM : μι → ℕ}
    {XM 𝒦XM : μι → Set (CTorus d L N₁ m₁ (k + 1))} {EbM : μι → ℝ}
    (ys : μι → CTorus d L N₁ m₁ (k + 1)) (is : μι → Fin N) (hys : ∀ τ ∈ 𝒯M, ys τ ∈ X₁M τ)
    (hBM : ∀ τ ∈ 𝒯M, BgSetting N S.G' (GkM τ) (GjM τ) a₁ ν c BG κ r₀ eps δ₃ (X₀M τ) (X₁M τ) (jM τ))
    (hFM : ∀ τ ∈ 𝒯M, FlSetting N S.G' (GkM τ) Hm a₁ ν κ BG eps δ₃ Kc Cx c₂ BG₂ δ₁ δfl (X₁M τ))
    (hcovM : ∀ τ ∈ 𝒯M, CovSetup S.G' (m₀) (jM τ) (XM τ) (𝒦XM τ))
    (hX₁M : ∀ τ ∈ 𝒯M, (↑(X₁M τ) : Set (CTorus d L N₁ m₁ (k + 1))) = X1 S.G' (m₀) (jM τ) (𝒦XM τ))
    (hoptM : ∀ τ ∈ 𝒯M, ∃ (W₀ : Finset (CTorus d L N₁ m₁ (k + 1)))
      (E₀ : Finset (CTorus d L N₁ m₁ (k + 1) × CTorus d L N₁ m₁ (k + 1))),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ XM τ) ∧ MeetsOne (m₀) (jM τ) (𝒦XM τ) W₀ ∧
        bondCost (scaleW L (m₀) m₁ (jM τ)) E₀ = treeLenCovOne (m₀) (jM τ) (XM τ))
    (hlogM : ∀ τ ∈ 𝒯M, Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) *
      (((L ^ m₀) ^ d : ℕ) : ℝ)) ≤ (κ / 2 - 1) / 2)
    (hEbM : ∀ τ ∈ 𝒯M, 0 ≤ EbM τ) {EM : μι → RawData d L (N₁ * L ^ m₁) (k + 1) N → ℂ}
    (hEanM : ∀ τ ∈ 𝒯M, AnalyticOnNhd ℂ (EM τ) (XiCRaw (GjM τ) (compWeight L a₁) ν (jM τ)
      (scaledC0 d) (scaledC0 d ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl)))
    (hEbdM : ∀ τ ∈ 𝒯M, ∀ r ∈ XiCRaw (GjM τ) (compWeight L a₁) ν (jM τ) (scaledC0 d)
      (scaledC0 d ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl),
      ‖EM τ r‖ ≤ EbM τ * Real.exp (-(κdec - 1) * treeLenCovOne (m₀) (jM τ) (XM τ)))
    -- the sizes of the old terms and of the observable terms (the source bounds of (3.2)-(3.4)):
    -- the bounds of the terms rooted at one site (resp. at one source site) add up to `ρ`
    (rE : τι → CTorus d L N₁ m₁ (k + 1)) (hrE : ∀ τ ∈ 𝒯E, rE τ ∈ X₁E τ) {ρE : ℝ} (hρE0 : 0 ≤ ρE)
    (hρE : ∀ x : CTorus d L N₁ m₁ (k + 1), ∑ τ ∈ 𝒯E.filter (fun τ => rE τ = x),
      EbE τ * Real.exp (-κ₀ * treeLenCovOne m₀ (jE τ) (XE τ)) ≤ ρE)
    {ρM : ℝ} (hρM0 : 0 ≤ ρM)
    (hρM : ∀ p : CTorus d L N₁ m₁ (k + 1) × Fin N, ∑ τ ∈ 𝒯M.filter (fun τ => (ys τ, is τ) = p),
      EbM τ * Real.exp (-κ₀ * treeLenCovOne m₀ (jM τ) (XM τ)) ≤ ρM)
    -- the `ν`-part: the bound on the external field and the block margin of the blocks
    {Bh : ℝ} (hBh0 : 0 ≤ Bh)
    (hBh : ∀ D : BgData S.G' N, XiCData S.G' (compWeight L a₁) ν (k + 1) 1 eps D →
      ∀ x i, ‖D.h x i‖ ≤ Bh) (cν : ℂ)
    (hZν : ∀ z, (↑(blockSites d L N₁ m₁ (k + 1) k z) : Set (CTorus d L N₁ m₁ (k + 1))) ⊆ ↑(X₁V z))
    (hRσ : 0 < Rσ) (hc : (Rσ * R₁ + r) * ρ < cψ)
    {Θ₀ : RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ)}
    (hΘ₀ : Θ₀ ∈ XiCRaw S.G' (compWeight L a₁) ν (k + 1) 1 eps ×ˢ l1Ball d L N₁ m₁ (k + 1) N)
    (hεb : prop33Eps d L N m₁ k m₀ a₁ ν BG BG₂ κ δ₁ r ρE ρM * ‖cβ‖ +
      ‖cν‖ * (1 * (c1 d L * ((L : ℝ) ^ (m₀ + m₁)) ^ d *
        nuBd d L N k (cK2' d L N (famConst d L BG₂ κ) * δ₁)
          (K4 d L N BG κ * (xiC1 d * eps) + (1 + 3 * (xiC1 d * eps)) + Bh) / r)) ≤ εU)


/-- The expanded function of Proposition 3.3 in the hat variable: the five parts (the interaction,
the old terms, the source terms, the observable terms and the `ν`-part). -/
noncomputable def physVal :
    (unitPts S.G' × Fin N → ℂ) × (unitPts S.G' × Fin N → ℂ) → 
    (unitPts S.G' × Fin N → ℂ) × (unitPts S.G' × Fin N → ℂ) → ℂ →
      RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) → ℂ :=
  fun x w σ p =>
          (-cβ) * raySrc3 (hatFun S.G' a₁ ν eps S.hG' cc (interactionOne hG S.hG' le_rfl a₁ ν eps))
            taylorWeight x.1 w.1 σ p.1 +
          cβ * (∑ τ ∈ 𝒯E, if h : τ ∈ 𝒯E then
            dirTermSrc (hatFun S.G' a₁ ν eps S.hG' cc (flComp (hBE τ h) (hFE τ h) (EE τ)))
              (fun _ => (1 : ℂ)) x.1 w.1 σ p.1 else 0) +
          cβ * (∑ s : CTorus d L N₁ m₁ (k + 1) × Fin N, p.2 s.1 s.2 *
            dirTermSrc (hatFun S.G' a₁ ν eps S.hG' cc (onXi S.G' a₁ ν eps
              (fun D ψ' => svec Hm (flFieldOne S.G' Hm BG₂ κ a₁ ν D ψ') s.1 s.2)))
              (fun _ => (1 : ℂ)) x.2 w.2 σ p.1) +
          cβ * (∑ τ ∈ 𝒯M, if h : τ ∈ 𝒯M then
            p.2 (ys τ) (is τ) * dirTermSrc (hatFun S.G' a₁ ν eps S.hG' cc
              (flComp (hBM τ h) (hFM τ h) (EM τ))) (fun _ => (1 : ℂ)) x.2 w.2 σ p.1 else 0) +
          cν * dirTermSrc (hatFun S.G' a₁ ν eps S.hG' cc (onXi S.G' a₁ ν eps
            (fun D ψ' => nuTotal S.G' Hm a₁ ν BG₂ κ D ψ'))) (fun _ => (1 : ℂ)) x.1 w.1 σ p.1

/-- The bounds of the terms of the physical expansion. -/
noncomputable def physB (Y : Set (CTorus d L N₁ m₁ (k + 1))) : ℝ :=
  prop33Eps d L N m₁ k m₀ a₁ ν BG BG₂ κ δ₁ r ρE ρM * ‖cβ‖ *
          Real.exp (-(2 * κdec - 1) * treeLenCovOne m₀ (k + 1) Y) +
          ‖cν‖ * (1 * (c1 d L * ((L : ℝ) ^ (m₀ + m₁)) ^ d *
            nuBd d L N k (cK2' d L N (famConst d L BG₂ κ) * δ₁)
              (K4 d L N BG κ * (xiC1 d * eps) + (1 + 3 * (xiC1 d * eps)) + Bh) / r) *
            Real.exp (-(2 * κdec - 1) * treeLenCovOne m₀ (k + 1) Y))


/-- **The conclusion of `interaction_expansion_hat_dm`** for the witnesses `𝒴`, `T`: a localized
expansion (`LocInt` for the landed paired relation `AgFPair`) with labels in `𝒟_{k+1}` and
continuous diagonal terms.  This is the thick legacy record: its locality is stated for the thick
relations (raw datum on `thickSet Y`, `physAgΘThick`; hat variables on the block thickening,
`AgFPair`).  The exact locality of the same terms is `PhysicalSharpLoc`. -/
def PhysExpansion (𝒴 : Finset (Set (CTorus d L N₁ m₁ (k + 1))))
    (T : Set (CTorus d L N₁ m₁ (k + 1)) →
      ((unitPts S.G' × Fin N → ℂ) × (unitPts S.G' × Fin N → ℂ)) →
      ((unitPts S.G' × Fin N → ℂ) × (unitPts S.G' × Fin N → ℂ)) → ℂ →
      RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) → ℂ) :
    Prop :=
  LocIntDm (IsDj m₀ (k + 1)) (fun ψ : unitPts S.G' × Fin N → ℂ => (ψ, ψ))
    (physSΛ S a₁ ν eps) (physXW S cψ R₁ Rσ r) Rσ 𝒴 T
    (physVal (EE := EE) (EM := EM) S cβ hG cc 𝒯E hBE hFE 𝒯M ys is hBM hFM cν) (physB (N := N) (a₁ := a₁) (ν := ν) (BG := BG) (κ := κ) (eps := eps) (BG₂ := BG₂) (δ₁ := δ₁) (κdec := κdec) (r := r) (m₀ := m₀) (ρE := ρE) (ρM := ρM) (Bh := Bh) cβ cν) (physAgΘThick S) (AgFPair S)

section Bound

include hεb

omit [NeZero N₁] [NeZero L] in
/-- The bound `b_Y` of the physical expansion is at most `ε_U e^{-a 𝗱(Y)}`, `a = 2κ_dec - 1`. -/
theorem physB_le (Y : Set (CTorus d L N₁ m₁ (k + 1))) :
    physB (N := N) (a₁ := a₁) (ν := ν) (BG := BG) (κ := κ) (eps := eps) (BG₂ := BG₂) (δ₁ := δ₁) (κdec := κdec) (r := r) (m₀ := m₀) (ρE := ρE) (ρM := ρM) (Bh := Bh) cβ cν Y ≤ εU * Real.exp (-(2 * κdec - 1) * treeLenCovOne m₀ (k + 1) Y) := by
  have hexp := (Real.exp_pos (-(2 * κdec - 1) * treeLenCovOne m₀ (k + 1) Y)).le
  unfold physB
  calc _ = (prop33Eps d L N m₁ k m₀ a₁ ν BG BG₂ κ δ₁ r ρE ρM * ‖cβ‖ +
      ‖cν‖ * (1 * (c1 d L * ((L : ℝ) ^ (m₀ + m₁)) ^ d *
        nuBd d L N k (cK2' d L N (famConst d L BG₂ κ) * δ₁)
          (K4 d L N BG κ * (xiC1 d * eps) + (1 + 3 * (xiC1 d * eps)) + Bh) / r))) *
          Real.exp (-(2 * κdec - 1) * treeLenCovOne m₀ (k + 1) Y) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hεb hexp

end Bound

section HatPackaging

include hR₁ hr hRσ hc hΘ₀ hεb

/-- **The physical expansion as `HatTerms`** (the landed thick-label route): the witnesses
`𝒴`, `T` of a physical expansion, the bound `b = physB`, the diagonal embedding `ψ̂ ↦ (ψ̂, ψ̂)`, the
thick relation `physAgΘThick` of the data and the paired relation `AgFPair`.  This is the first half
of the proof of `labelAct_of_interaction_expansion_hat`. -/
noncomputable def physicalHatTerms (𝒴 : Finset (Set (CTorus d L N₁ m₁ (k + 1))))
    (T : Set (CTorus d L N₁ m₁ (k + 1)) →
      ((unitPts S.G' × Fin N → ℂ) × (unitPts S.G' × Fin N → ℂ)) →
      ((unitPts S.G' × Fin N → ℂ) × (unitPts S.G' × Fin N → ℂ)) → ℂ →
      RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) → ℂ)
    (hD : PhysExpansion (EE := EE) (EM := EM) (κdec := κdec) (r := r) (m₀ := m₀) (ρE := ρE) (ρM := ρM) (Bh := Bh) (cψ := cψ) (R₁ := R₁) (Rσ := Rσ) S cβ hG cc 𝒯E hBE hFE 𝒯M ys is hBM hFM cν 𝒴 T) :
    HatTerms S m₀ (fun ψ => (ψ, ψ)) ρ Rσ εU (2 * κdec - 1) Θ₀ (physSΛ S a₁ ν eps)
      (physXW S cψ R₁ Rσ r) (physVal (EE := EE) (EM := EM) S cβ hG cc 𝒯E hBE hFE 𝒯M ys is hBM hFM cν) (physAgΘThick S) (AgFPair S) :=
  hatTerms_of_expansion S m₀ hRσ.le (by linarith) hr.le hc (SΛ := physSΛ S a₁ ν eps)
    (val := physVal (EE := EE) (EM := EM) S cβ hG cc 𝒯E hBE hFE 𝒯M ys is hBM hFM cν) (AgΘ := physAgΘThick S) 𝒴 T (physB (N := N) (a₁ := a₁) (ν := ν) (BG := BG) (κ := κ) (eps := eps) (BG₂ := BG₂) (δ₁ := δ₁) (κdec := κdec) (r := r) (m₀ := m₀) (ρE := ρE) (ρM := ρM) (Bh := Bh) cβ cν) hD.loc hD.dom
    (fun Y _ => physB_le cβ cν hεb Y) hΘ₀ (fun Y => ⟨fun x _ => ⟨rfl, rfl⟩, fun x _ => rfl⟩)
    (fun Y _ σ hσ => by
      have hcont := hD.cont Y ‹_› σ hσ Θ₀ hΘ₀
      refine (continuousOn_iff_continuous_domRestrict.1 (hcont.mono ?_)).measurable
      intro ψ hψ
      exact ⟨hatRaysO_pair S hψ hRσ.le (by linarith) hr.le hc,
        hatRaysO_pair S hψ hRσ.le (by linarith) hr.le hc⟩)

end HatPackaging


section Existence

include hC hconn hrow hκ₀ hκdec hκ h1 hR₁ hr hk hG hcψ hMX hdm hα hsmX hδ₁ ha₁ H hc7 hR hRs hsmall hnum hnum' hsm hcovV hX₁V hoptV hΔV hlogV hZV hmarV hBE hFE hcovE hX₁E hoptE hlogE hEbE hEanE hEbdE hcovF hX₁F hoptF hΔF hlogF hyF hys hBM hFM hcovM hX₁M hoptM hlogM hEbM hEanM hEbdM hrE hρE0 hρE hρM0 hρM hBh0 hBh hZν

/-- **The physical witnesses exist** (`interaction_expansion_hat_dm`): under the hypotheses of
`labelAct_of_interaction_expansion_hat` there are `𝒴` and `T` with ``PhysExpansion``.  (This
shows that the bundled hypothesis `PhysExpansion` is inhabited.) -/
theorem physExpansion_exists :
    ∃ (𝒴 : Finset (Set (CTorus d L N₁ m₁ (k + 1))))
      (T : Set (CTorus d L N₁ m₁ (k + 1)) →
        ((unitPts S.G' × Fin N → ℂ) × (unitPts S.G' × Fin N → ℂ)) →
        ((unitPts S.G' × Fin N → ℂ) × (unitPts S.G' × Fin N → ℂ)) → ℂ →
        RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) → ℂ),
      PhysExpansion (EE := EE) (EM := EM) (κdec := κdec) (r := r) (m₀ := m₀) (ρE := ρE) (ρM := ρM) (Bh := Bh) (cψ := cψ) (R₁ := R₁) (Rσ := Rσ) S cβ hG cc 𝒯E hBE hFE 𝒯M ys is hBM hFM cν 𝒴 T := by
  obtain ⟨𝒴, T, hD⟩ := interaction_expansion_hat_dm (Kc := Kc) (Cx := Cx) (c₂ := c₂) (BG₂ := BG₂) (δ₁ := δ₁) hC cβ hconn hrow (κdec := κdec) (κ₀ := κ₀) hκ₀ hκdec hκ h1 (R₁ := R₁) hR₁ (r := r) (Rσ := Rσ) hr hk hG S.hG' cc (cψ := cψ) hcψ hMX (δc := δc) hdm hα hsmX hδ₁ ha₁ H hc7 (R := R) hR hRs hsmall hnum hnum' hsm (m₀ := m₀) (jV := jV) (XV := XV) (𝒦XV := 𝒦XV) (X₁V := X₁V) hcovV hX₁V hoptV hΔV hlogV hZV hmarV (τι := τι) 𝒯E (ϱ₁ := ϱ₁) (ϱ₂ := ϱ₂) (GkE := GkE) (GjE := GjE) (r₀ := r₀) (δ₃ := δ₃) (δfl := δfl) (X₀E := X₀E) (X₁E := X₁E) (jE := jE) (XE := XE) (𝒦XE := 𝒦XE) (EbE := EbE) hBE hFE hcovE hX₁E hoptE hlogE hEbE (EE := EE) hEanE hEbdE (jF := jF) (XF := XF) (𝒦XF := 𝒦XF) (X₁F := X₁F) hcovF hX₁F hoptF hΔF hlogF hyF (μι := μι) 𝒯M (ϱ₁M := ϱ₁M) (ϱ₂M := ϱ₂M) (GkM := GkM) (GjM := GjM) (X₀M := X₀M) (X₁M := X₁M) (jM := jM) (XM := XM) (𝒦XM := 𝒦XM) (EbM := EbM) ys is hys hBM hFM hcovM hX₁M hoptM hlogM hEbM (EM := EM) hEanM hEbdM rE hrE (ρE := ρE) hρE0 hρE (ρM := ρM) hρM0 hρM (Bh := Bh) hBh0 hBh cν hZν
  exact ⟨𝒴, T, hD⟩

include hRσ hc hΘ₀ hεb

/-- **`physical_hatTerms` (unconditional).**  Under exactly the hypotheses of
`labelAct_of_interaction_expansion_hat` that concern the expansion (those of
`interaction_expansion_hat_dm`, which the landed step assemblers use, together with `hRσ`, `hc`,
`hΘ₀` and the bound `hεb`), the physical expansion is a `HatTerms` instance whose terms are
those of `interaction_expansion_hat_dm` and whose bounds are `physB`. -/
theorem physical_hatTerms :
    ∃ I : HatTerms S m₀ (fun ψ => (ψ, ψ)) ρ Rσ εU (2 * κdec - 1) Θ₀ (physSΛ S a₁ ν eps)
      (physXW S cψ R₁ Rσ r) (physVal (EE := EE) (EM := EM) S cβ hG cc 𝒯E hBE hFE 𝒯M ys is hBM hFM cν) (physAgΘThick S) (AgFPair S),
      PhysExpansion (EE := EE) (EM := EM) (κdec := κdec) (r := r) (m₀ := m₀) (ρE := ρE) (ρM := ρM) (Bh := Bh) (cψ := cψ) (R₁ := R₁) (Rσ := Rσ) S cβ hG cc 𝒯E hBE hFE 𝒯M ys is hBM hFM cν I.𝒴 I.T ∧
        I.b = physB (N := N) (a₁ := a₁) (ν := ν) (BG := BG) (κ := κ) (eps := eps) (BG₂ := BG₂) (δ₁ := δ₁) (κdec := κdec) (r := r) (m₀ := m₀) (ρE := ρE) (ρM := ρM) (Bh := Bh) cβ cν := by
  obtain ⟨𝒴, T, hD⟩ := physExpansion_exists (S := S) (hC := hC) (cβ := cβ) (hconn := hconn) (hrow := hrow) (hκ₀ := hκ₀) (hκdec := hκdec) (hκ := hκ) (h1 := h1) (hR₁ := hR₁) (hr := hr) (hk := hk) (hG := hG) (cc := cc) (hcψ := hcψ) (hMX := hMX) (hdm := hdm) (hα := hα) (hsmX := hsmX) (hδ₁ := hδ₁) (ha₁ := ha₁) (H := H) (hc7 := hc7) (hR := hR) (hRs := hRs) (hsmall := hsmall) (hnum := hnum) (hnum' := hnum') (hsm := hsm) (hcovV := hcovV) (hX₁V := hX₁V) (hoptV := hoptV) (hΔV := hΔV) (hlogV := hlogV) (hZV := hZV) (hmarV := hmarV) (𝒯E := 𝒯E) (hBE := hBE) (hFE := hFE) (hcovE := hcovE) (hX₁E := hX₁E) (hoptE := hoptE) (hlogE := hlogE) (hEbE := hEbE) (hEanE := hEanE) (hEbdE := hEbdE) (hcovF := hcovF) (hX₁F := hX₁F) (hoptF := hoptF) (hΔF := hΔF) (hlogF := hlogF) (hyF := hyF) (𝒯M := 𝒯M) (ys := ys) (is := is) (hys := hys) (hBM := hBM) (hFM := hFM) (hcovM := hcovM) (hX₁M := hX₁M) (hoptM := hoptM) (hlogM := hlogM) (hEbM := hEbM) (hEanM := hEanM) (hEbdM := hEbdM) (rE := rE) (hrE := hrE) (hρE0 := hρE0) (hρE := hρE) (hρM0 := hρM0) (hρM := hρM) (hBh0 := hBh0) (hBh := hBh) (cν := cν) (hZν := hZν)
  exact ⟨physicalHatTerms (S := S) (cβ := cβ) (hG := hG) (cc := cc) (𝒯E := 𝒯E) (hBE := hBE) (hFE := hFE) (𝒯M := 𝒯M) (ys := ys) (is := is) (hBM := hBM) (hFM := hFM) (cν := cν) (hR₁ := hR₁) (hr := hr) (hRσ := hRσ) (hc := hc) (hΘ₀ := hΘ₀) (hεb := hεb) 𝒴 T hD, hD, rfl⟩

end Existence


section Corollaries

variable (hN : L ^ m₀ ∣ N₁) (hp : 0 < S.p₁) (hpρ : S.p₁ ≤ ρ) (hεpos : 0 < εU)

include hR₁ hr hRσ hc hΘ₀ hεb hN hp hpρ hεpos hκ₀ hκdec

/-- **Check of the packaging (thick route).**  `labelAct_of_hatTerms` applied to
`physicalHatTerms` gives the label activities of `labelAct_of_interaction_expansion_hat`
(before its numerics), for a physical witness `(𝒴, T)`. -/
theorem labelAct_of_physical_hatTerms (hL2 : 2 ≤ L)
    (𝒴 : Finset (Set (CTorus d L N₁ m₁ (k + 1))))
    (T : Set (CTorus d L N₁ m₁ (k + 1)) →
      ((unitPts S.G' × Fin N → ℂ) × (unitPts S.G' × Fin N → ℂ)) →
      ((unitPts S.G' × Fin N → ℂ) × (unitPts S.G' × Fin N → ℂ)) → ℂ →
      RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) → ℂ)
    (hD : PhysExpansion (EE := EE) (EM := EM) (κdec := κdec) (r := r) (m₀ := m₀) (ρE := ρE) (ρM := ρM) (Bh := Bh) (cψ := cψ) (R₁ := R₁) (Rσ := Rσ) S cβ hG cc 𝒯E hBE hFE 𝒯M ys is hBM hFM cν 𝒴 T) {κ0 Kc' : ℝ}
    (hκ0 : aEnt d L + 1 ≤ κ0) (hKc : K0 d L κ0 ≤ Kc') :
    ∃ (Lb : Type) (_ : Fintype Lb)
      (Lab : CubeLabels (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) m₀ (k + 1)
        Set.univ Lb)
      (A : ℂ → LabelAct Lab (S.blockSplit m₀ hp).Ωb
        (hatEpsH d L Rσ εU (2 * κdec - 1)) (hatKappaH d L (2 * κdec - 1)) κ0 Kc'),
      (∀ y Φ, DifferentiableOn ℂ (fun u => (A u).H y Φ) (Metric.ball 0 Rσ)) ∧
      (∀ u : ℂ, ‖u‖ < Rσ → ∀ Φ, ∑ y, (A u).H y Φ =
        physVal (EE := EE) (EM := EM) S cβ hG cc 𝒯E hBE hFE 𝒯M ys is hBM hFM cν (S.hatOf m₀ ρ hp Φ, S.hatOf m₀ ρ hp Φ) (S.hatOf m₀ ρ hp Φ, S.hatOf m₀ ρ hp Φ) u Θ₀) :=
  labelAct_of_hatTerms S m₀ (physicalHatTerms (S := S) (cβ := cβ) (hG := hG) (cc := cc) (𝒯E := 𝒯E) (hBE := hBE) (hFE := hFE) (𝒯M := 𝒯M) (ys := ys) (is := is) (hBM := hBM) (hFM := hFM) (cν := cν) (hR₁ := hR₁) (hr := hr) (hRσ := hRσ) (hc := hc) (hΘ₀ := hΘ₀) (hεb := hεb) 𝒴 T hD) hN hL2 hp
    (lt_of_lt_of_le hp hpρ) hRσ.le hεpos.le
    (by linarith) hκ0 hKc


/-- **`DirectTerms` for the physical expansion, conditional on `PhysicalSharpLoc`.**  The domains,
terms, bounds, source set, ray set and expanded function are those of `physicalHatTerms`; the four
fields `sum`, `analytic`, `bound`, `zero` of `LocInt` are unchanged; the field `loc` for the sharp
relations (`physAgΘ`: raw datum and source on `Y`; `AgFDirPair`: hat variables at the unit points of
`Y`) is the hypothesis `hsharp`; the field `ag` is proved from the cell-union property of the labels
(a consequence of `IsDj` and `L ^ m₀ ∣ N₁`). -/
noncomputable def physicalDirectTerms_of_sharpLoc
    (𝒴 : Finset (Set (CTorus d L N₁ m₁ (k + 1))))
    (T : Set (CTorus d L N₁ m₁ (k + 1)) →
      ((unitPts S.G' × Fin N → ℂ) × (unitPts S.G' × Fin N → ℂ)) →
      ((unitPts S.G' × Fin N → ℂ) × (unitPts S.G' × Fin N → ℂ)) → ℂ →
      RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) → ℂ)
    (hD : PhysExpansion (EE := EE) (EM := EM) (κdec := κdec) (r := r) (m₀ := m₀) (ρE := ρE) (ρM := ρM) (Bh := Bh) (cψ := cψ) (R₁ := R₁) (Rσ := Rσ) S cβ hG cc 𝒯E hBE hFE 𝒯M ys is hBM hFM cν 𝒴 T)
    (hsharp : PhysicalSharpLoc S cψ R₁ Rσ r a₁ ν eps 𝒴 T) :
    DirectTerms S m₀ hp (fun ψ => (ψ, ψ)) ρ Rσ εU (2 * κdec - 1) Θ₀ (physSΛ S a₁ ν eps) (physXW S cψ R₁ Rσ r) (physVal (EE := EE) (EM := EM) S cβ hG cc 𝒯E hBE hFE 𝒯M ys is hBM hFM cν) (physAgΘ S) (AgFDirPair S) :=
  let I0 := physicalHatTerms (S := S) (cβ := cβ) (hG := hG) (cc := cc) (𝒯E := 𝒯E) (hBE := hBE) (hFE := hFE) (𝒯M := 𝒯M) (ys := ys) (is := is) (hBM := hBM) (hFM := hFM) (cν := cν) (hR₁ := hR₁) (hr := hr) (hRσ := hRσ) (hc := hc) (hΘ₀ := hΘ₀) (hεb := hεb) 𝒴 T hD
  { 𝒴 := 𝒴
    T := T
    b := physB (N := N) (a₁ := a₁) (ν := ν) (BG := BG) (κ := κ) (eps := eps) (BG₂ := BG₂) (δ₁ := δ₁) (κdec := κdec) (r := r) (m₀ := m₀) (ρE := ρE) (ρM := ρM) (Bh := Bh) cβ cν
    loc := { I0.loc with loc := hsharp }
    dom := I0.dom
    bd := I0.bd
    mem := I0.mem
    agΘ := fun Y => physAgΘ_of_thick S (I0.agΘ Y)
    xw := I0.xw
    ag := fun Y hY Φ Φ' h => by
      have h' := S.agHatFDir_hatOf m₀ (cell_subset_of_isDj hN (I0.dom Y hY)) ρ hp Φ Φ' h
      exact ⟨h', h'⟩
    meas := I0.meas }

omit hκ₀ hκdec in
/-- **The chain (conditional on `PhysicalSharpLoc`).**  `labelAct_of_directTerms` applied to
`physicalDirectTerms_of_sharpLoc`: label activities with rate `a = 2κ_dec - 1` and prefactor
`R_σ ε_U` for the physical expansion, on the labels `thickLabels I.𝒴 I.dom` of the `DirectTerms`
instance `I`. -/
theorem labelAct_of_physical_directTerms_of_sharpLoc
    (𝒴 : Finset (Set (CTorus d L N₁ m₁ (k + 1))))
    (T : Set (CTorus d L N₁ m₁ (k + 1)) →
      ((unitPts S.G' × Fin N → ℂ) × (unitPts S.G' × Fin N → ℂ)) →
      ((unitPts S.G' × Fin N → ℂ) × (unitPts S.G' × Fin N → ℂ)) → ℂ →
      RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) → ℂ)
    (hD : PhysExpansion (EE := EE) (EM := EM) (κdec := κdec) (r := r) (m₀ := m₀) (ρE := ρE) (ρM := ρM) (Bh := Bh) (cψ := cψ) (R₁ := R₁) (Rσ := Rσ) S cβ hG cc 𝒯E hBE hFE 𝒯M ys is hBM hFM cν 𝒴 T)
    (hsharp : PhysicalSharpLoc S cψ R₁ Rσ r a₁ ν eps 𝒴 T) {κ0 Kc' : ℝ}
    (hκ0 : aEnt d L + 1 ≤ κ0) (hKc : K0 d L κ0 ≤ Kc') :
    ∃ A : ℂ → LabelAct (thickLabels
        (physicalDirectTerms_of_sharpLoc (S := S) (cβ := cβ) (hG := hG) (cc := cc) (𝒯E := 𝒯E) (hBE := hBE) (hFE := hFE) (𝒯M := 𝒯M) (ys := ys) (is := is) (hBM := hBM) (hFM := hFM) (cν := cν) (hR₁ := hR₁) (hr := hr) (hRσ := hRσ) (hc := hc) (hΘ₀ := hΘ₀) (hεb := hεb) hN hp 𝒴 T hD hsharp).𝒴
        (physicalDirectTerms_of_sharpLoc (S := S) (cβ := cβ) (hG := hG) (cc := cc) (𝒯E := 𝒯E) (hBE := hBE) (hFE := hFE) (𝒯M := 𝒯M) (ys := ys) (is := is) (hBM := hBM) (hFM := hFM) (cν := cν) (hR₁ := hR₁) (hr := hr) (hRσ := hRσ) (hc := hc) (hΘ₀ := hΘ₀) (hεb := hεb) hN hp 𝒴 T hD hsharp).dom)
        (S.blockSplit m₀ hp).Ωb (Rσ * εU) (2 * κdec - 1) κ0 Kc',
      (∀ y Φ, DifferentiableOn ℂ (fun u => (A u).H y Φ) (Metric.ball 0 Rσ)) ∧
      (∀ u : ℂ, ‖u‖ < Rσ → ∀ Φ, ∑ y, (A u).H y Φ =
        physVal (EE := EE) (EM := EM) S cβ hG cc 𝒯E hBE hFE 𝒯M ys is hBM hFM cν (S.hatOf m₀ ρ hp Φ, S.hatOf m₀ ρ hp Φ) (S.hatOf m₀ ρ hp Φ, S.hatOf m₀ ρ hp Φ) u Θ₀) :=
  labelAct_of_directTerms S m₀
    (physicalDirectTerms_of_sharpLoc (S := S) (cβ := cβ) (hG := hG) (cc := cc) (𝒯E := 𝒯E) (hBE := hBE) (hFE := hFE) (𝒯M := 𝒯M) (ys := ys) (is := is) (hBM := hBM) (hFM := hFM) (cν := cν) (hR₁ := hR₁) (hr := hr) (hRσ := hRσ) (hc := hc) (hΘ₀ := hΘ₀) (hεb := hεb) hN hp 𝒴 T hD hsharp) hN
    (lt_of_lt_of_le hp hpρ) hRσ.le hεpos.le hκ0 hKc

end Corollaries

end PhysicalTerms

end Balaban.Fluctuation
