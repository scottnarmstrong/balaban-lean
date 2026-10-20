/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.DecMarkOfPair
public import Balaban.Fluctuation.MarkedScaledCountDec

/-!
# The rooted count of the corrected decoupled marks

The corrected mark `decMarkCorr` of a pair `(F₁, Sol)` is the first-order Taylor remainder, in the
first mark, of the decoupled mark `decMarkG`.  Put `T_{b,Y}(t) = t · (−β · decMarkCorr … Y …)`, so
that `∂_t T_{b,Y}|_{t=0} = −β · decMarkCorr … Y …`.  This file feeds these terms to the generic
rooted sum `markedOutDec` of `MarkedScaledCountDec.lean` and obtains, for a family of pairs
with one pair for each block:

* `decMarkCorr_eq_zero_of_mask_miss`: if no site of `Y` has its unit point in the mask, the
  corrected mark of `Y` vanishes (clause 8 of `MarkedBlockExpansionDecPair`, applied to the
  decoupled mark at every first mark of the disc);
* `corrected_markedOutDec_count`: the rooted outputs satisfy the bound
  `F₀ e^{−(2κ_dec−1) d(Y′)}` with `F₀ = |β| · 4 ‖E_*‖ U² / R³ · J`, the weighted sum of the outputs
  over the bridge family is at most `F₀ K₀`, a nonzero output has the root cube among its cubes,
  and the sum of the outputs is the sum of `−β · decMarkCorr` over the blocks and the labels.

Here `J = c₁ M^d · n_Fibre · e^{(2κ_dec−1) c_Br}`, `M = L^{m₀+m₁}`, are the constants of the
count of the uncorrected marks.

On a background generating set `Gb` (ruling R8): `decMarkGBg_eq_zero_of`, `decMarkCorrBg_eq_zero_of`
(vanishing from the vanishing of the term derivatives), `decMarkCorrTermBg`,
`deriv_decMarkCorrTermBg`, and `corrected_markedOutDecBg_count_of_bounds` (the rooted count from
the cubic bound and the vanishing of the corrected marks).  `decMarkCorrTerm` is the instance
`Gb = S.G'`, `BgTransport.self` (definitionally, `decMarkCorrTerm_apply`), and the statements at
`S.G'` are instances.
-/

@[expose] public section

namespace Balaban.Fluctuation

open MeasureTheory Filter Balaban Balaban.Localization Balaban.Multiscale Balaban.Background
  Balaban.SmallField Balaban.Analysis Balaban.Polymer Balaban.SmallField.Def6 Set

section VanishingBg

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ ϱb ϱm : ℝ}
  (S : StepSetting d L N₁ m₁ k N ϱ) {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}
  {Gb : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱb} {T : BgTransport S.G' Gb N}
  {ϱg : ℝ} {Gg : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱg}
variable {a₁ ν κ eps δ₁ cψ : ℝ} {X₁f : Finset (CTorus d L N₁ m₁ (k + 1))}
variable {m₀ j : ℕ} {𝒦X : Set (CTorus d L N₁ m₁ (k + 1))}
variable {cc : ℂ} {Zm : Finset (unitPts Gb)}
variable {F₁ : DecParams Gb × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      (Gb.Ω 1 × Fin N → ℂ) × (Gb.Ω 1 → ℂ)}
variable {Sol : Dec2.DecParams (coverOf Gb) × Edat Hm N → (Hm.Ω 1 × Fin N → ℂ) × (Hm.Ω 1 → ℂ)}

/-- **Core of `decMarkGBg_eq_zero_of` on a chart of a generating set `Gg`**: the statement of
`decMarkGBg_eq_zero_of` with the data in the chart `XiCRaw Gg` and the parameters in `physVBg
Gg` in place of the step's chart; `decMarkGBg_eq_zero_of` is its instance `Gg = S.G'`. -/
theorem decMarkGBg_eq_zero_of_gen
    {En : ((Gb.Ω 1 × Fin N → ℂ) × (Gb.Ω 1 → ℂ)) → (Hm.Ω 1 × Fin N → ℂ) →
      RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) → ℂ}
    {um : ℂ} {Y : Set (CTorus d L N₁ m₁ (k + 1))}
    (hmiss : ∀ u ∈ XiCRaw Gg (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
        {ψh : unitPts S.G' × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ},
      deriv (fun t : ℂ => evDecBg S.G' X₁f m₀ j 𝒦X Gb a₁ ν T cc F₁ Sol En Zm um t Y
        (u.1, T.res u.2)) 0 = 0)
    {ρ : ℝ} (hρ : 0 < ρ) (hρc : ρ ≤ cψ) (hp : 0 < S.p₁)
    {Θ : RawData d L (N₁ * L ^ m₁) (k + 1) N}
    (hΘ : Θ ∈ XiCRaw Gg (compWeight L a₁) ν (k + 1) 1 eps)
    (Φ : ∀ b, (S.blockSplit m₀ hp).Ωb b) :
    decMarkGBg S Gb T X₁f m₀ j 𝒦X a₁ ν cc F₁ Sol En Zm Y ρ hp Θ um Φ = 0 :=
  hmiss (Θ, S.hatOf m₀ ρ hp Φ) ⟨hΘ, fun p => (S.hatOf_mem m₀ hρ hp Φ p).trans hρc⟩

/-- **The mark on a background generating set vanishes where its term derivative vanishes.**  If
the mark derivative of the term of `Y` vanishes at every point of the chart of the step (the datum read on `Gb` is `T.dat` of it) times the box
`|ψ̂| ≤ cψ` (`hmiss`), then `decMarkGBg … um Φ = 0` for every block configuration. -/
theorem decMarkGBg_eq_zero_of
    {En : ((Gb.Ω 1 × Fin N → ℂ) × (Gb.Ω 1 → ℂ)) → (Hm.Ω 1 × Fin N → ℂ) →
      RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) → ℂ}
    {um : ℂ} {Y : Set (CTorus d L N₁ m₁ (k + 1))}
    (hmiss : ∀ u ∈ XiCRaw S.G' (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
        {ψh : unitPts S.G' × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ},
      deriv (fun t : ℂ => evDecBg S.G' X₁f m₀ j 𝒦X Gb a₁ ν T cc F₁ Sol En Zm um t Y
        (u.1, T.res u.2)) 0 = 0)
    {ρ : ℝ} (hρ : 0 < ρ) (hρc : ρ ≤ cψ) (hp : 0 < S.p₁)
    {Θ : RawData d L (N₁ * L ^ m₁) (k + 1) N}
    (hΘ : Θ ∈ XiCRaw S.G' (compWeight L a₁) ν (k + 1) 1 eps)
    (Φ : ∀ b, (S.blockSplit m₀ hp).Ωb b) :
    decMarkGBg S Gb T X₁f m₀ j 𝒦X a₁ ν cc F₁ Sol En Zm Y ρ hp Θ um Φ = 0 :=
  decMarkGBg_eq_zero_of_gen (Gg := S.G') S hmiss hρ hρc hp hΘ Φ

/-- **Core of `decMarkCorrBg_eq_zero_of` on a chart of a generating set `Gg`**: the statement of
`decMarkCorrBg_eq_zero_of` with the data in the chart `XiCRaw Gg` and the parameters in `physVBg
Gg` in place of the step's chart; `decMarkCorrBg_eq_zero_of` is its instance `Gg = S.G'`. -/
theorem decMarkCorrBg_eq_zero_of_gen
    {En : ((Gb.Ω 1 × Fin N → ℂ) × (Gb.Ω 1 → ℂ)) → (Hm.Ω 1 × Fin N → ℂ) →
      RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) → ℂ}
    {Y : Set (CTorus d L N₁ m₁ (k + 1))}
    (hmiss : ∀ um : ℂ, (‖um‖ + ‖(0 : ℂ)‖) * markedRad d L N k a₁ κ cψ cc < δ₁ →
      ∀ u ∈ XiCRaw Gg (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
        {ψh : unitPts S.G' × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ},
      deriv (fun t : ℂ => evDecBg S.G' X₁f m₀ j 𝒦X Gb a₁ ν T cc F₁ Sol En Zm um t Y
        (u.1, T.res u.2)) 0 = 0)
    {ρ : ℝ} (hρ : 0 < ρ) (hρc : ρ ≤ cψ) (hp : 0 < S.p₁) (hδ : 0 < δ₁)
    {Θ : RawData d L (N₁ * L ^ m₁) (k + 1) N}
    (hΘ : Θ ∈ XiCRaw Gg (compWeight L a₁) ν (k + 1) 1 eps)
    {um : ℂ} (hum : (‖um‖ + ‖(0 : ℂ)‖) * markedRad d L N k a₁ κ cψ cc < δ₁)
    (Φ : ∀ b, (S.blockSplit m₀ hp).Ωb b) :
    decMarkCorrBg S Gb T X₁f m₀ j 𝒦X a₁ ν cc F₁ Sol En Zm Y ρ hp Θ um Φ = 0 := by
  have h0 : (‖(0 : ℂ)‖ + ‖(0 : ℂ)‖) * markedRad d L N k a₁ κ cψ cc < δ₁ := by simpa using hδ
  have hopen : IsOpen {t : ℂ | (‖t‖ + ‖(0 : ℂ)‖) * markedRad d L N k a₁ κ cψ cc < δ₁} :=
    isOpen_lt (by fun_prop) continuous_const
  have hev : (fun v : ℂ => decMarkGBg S Gb T X₁f m₀ j 𝒦X a₁ ν cc F₁ Sol En Zm Y ρ hp Θ v Φ)
      =ᶠ[nhds (0 : ℂ)] fun _ => 0 := by
    filter_upwards [hopen.mem_nhds h0] with v hv
    exact decMarkGBg_eq_zero_of_gen S (hmiss v hv) hρ hρc hp hΘ Φ
  unfold decMarkCorrBg
  rw [decMarkGBg_eq_zero_of_gen S (hmiss um hum) hρ hρc hp hΘ Φ,
    decMarkGBg_eq_zero_of_gen S (hmiss 0 h0) hρ hρc hp hΘ Φ, hev.deriv_eq]
  simp

/-- **The corrected mark on a background generating set vanishes where the term derivatives
vanish.**  If, for every first mark `um` of the disc, the mark derivative of the term of `Y`
vanishes on the chart of the step (the datum read on `Gb` is `T.dat` of it) times the box, then `decMarkCorrBg … um Φ = 0`: the mark is zero
on a neighbourhood of `0` in the first mark, so are its value at `0` and its derivative at `0`. -/
theorem decMarkCorrBg_eq_zero_of
    {En : ((Gb.Ω 1 × Fin N → ℂ) × (Gb.Ω 1 → ℂ)) → (Hm.Ω 1 × Fin N → ℂ) →
      RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) → ℂ}
    {Y : Set (CTorus d L N₁ m₁ (k + 1))}
    (hmiss : ∀ um : ℂ, (‖um‖ + ‖(0 : ℂ)‖) * markedRad d L N k a₁ κ cψ cc < δ₁ →
      ∀ u ∈ XiCRaw S.G' (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
        {ψh : unitPts S.G' × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ},
      deriv (fun t : ℂ => evDecBg S.G' X₁f m₀ j 𝒦X Gb a₁ ν T cc F₁ Sol En Zm um t Y
        (u.1, T.res u.2)) 0 = 0)
    {ρ : ℝ} (hρ : 0 < ρ) (hρc : ρ ≤ cψ) (hp : 0 < S.p₁) (hδ : 0 < δ₁)
    {Θ : RawData d L (N₁ * L ^ m₁) (k + 1) N}
    (hΘ : Θ ∈ XiCRaw S.G' (compWeight L a₁) ν (k + 1) 1 eps)
    {um : ℂ} (hum : (‖um‖ + ‖(0 : ℂ)‖) * markedRad d L N k a₁ κ cψ cc < δ₁)
    (Φ : ∀ b, (S.blockSplit m₀ hp).Ωb b) :
    decMarkCorrBg S Gb T X₁f m₀ j 𝒦X a₁ ν cc F₁ Sol En Zm Y ρ hp Θ um Φ = 0 :=
  decMarkCorrBg_eq_zero_of_gen (Gg := S.G') S hmiss hρ hρc hp hδ hΘ hum Φ

end VanishingBg

section OnClass

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {β : Type*} [Fintype β] {m₀ : ℕ}

open Classical in
/-- **The count on a class of domains closed under subsets.**  The statement of
`norm_markedOutDec_le_of_term_bounds` for the rooted domains `Y'` of a class `P` closed under
subsets, from the bounds of the terms of the pairs whose domain is in `P`: the domains of the pairs
attached to `Y'` lie in `Y'`, and the terms off `P` are cut off. -/
theorem norm_markedOutDec_le_of_term_bounds_on (hN : L ^ m₀ ∣ N₁)
    (reads : β → Set (CTorus d L N₁ m₁ K))
    (dom : β → Finset (Set (CTorus d L N₁ m₁ K)))
    (hdom : ∀ b, ∀ Y ∈ dom b, IsDj m₀ K Y) (z : RootIdx d L N₁ m₁ K)
    (T : β → Set (CTorus d L N₁ m₁ K) → ℂ → ℂ)
    {C₀ M κdec : ℝ} (hC₀ : 0 ≤ C₀) (hM : 0 ≤ M) (hκ : 1 ≤ 2 * κdec)
    (P : Set (CTorus d L N₁ m₁ K) → Prop) (hP : ∀ Y Y', Y ⊆ Y' → P Y' → P Y)
    (hbd : ∀ q ∈ markedIdx reads dom z, P q.2 → ‖deriv (T q.1 q.2) 0‖ ≤
      C₀ * Real.exp (-(2 * κdec) * treeLenCovOne m₀ K q.2))
    (hcount : ∀ Y, (((markedIdx reads dom z).filter (fun q => q.2 = Y)).card : ℝ) ≤
      M * (1 + treeLenCovOne m₀ K Y))
    {Y' : Set (CTorus d L N₁ m₁ K)} (hY' : P Y') :
    ‖markedOutDec m₀ reads dom z T Y'‖ ≤ C₀ * M * ((nFibre d L : ℝ) *
      (Real.exp ((2 * κdec - 1) * cBr d L) *
        Real.exp (-(2 * κdec - 1) * treeLenCovOne m₀ K Y'))) := by
  have e : markedOutDec m₀ reads dom z T Y' =
      markedOutDec m₀ reads dom z (fun b Y => if P Y then T b Y else fun _ => 0) Y' := by
    unfold markedOutDec
    refine Finset.sum_congr rfl fun q hq => ?_
    have hPq : P q.2 := hP _ _ ((Finset.mem_filter.1 hq).2 ▸ subset_bridge z q.2) hY'
    simp only [hPq, ↓reduceIte]
  rw [e]
  refine norm_markedOutDec_le_of_term_bounds hN reads dom hdom z _ hC₀ hM hκ (fun q hq => ?_)
    hcount Y'
  by_cases hPq : P q.2
  · simp only [hPq, ↓reduceIte]
    exact hbd q hq hPq
  · simp only [hPq, ↓reduceIte, deriv_const, norm_zero]
    exact mul_nonneg hC₀ (Real.exp_pos _).le

end OnClass

section CountBg

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ ϱb ϱm : ℝ}
  (S : StepSetting d L N₁ m₁ k N ϱ) {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}
  {Gb : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱb} {T : BgTransport S.G' Gb N}
variable {a₁ ν κdec : ℝ} {m₀ : ℕ} {cc : ℂ} {Zm : Finset (unitPts Gb)}
variable {jV : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) → ℕ}
  {XV 𝒦XV : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) → Set (CTorus d L N₁ m₁ (k + 1))}
  {X₁V : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) → Finset (CTorus d L N₁ m₁ (k + 1))}

/-- **The terms of the corrected marks on a background generating set `Gb`.**  For the block `b`,
the label `Y`, and the pair `(F₁ b, Sol b)` of `Gb`, the function `t ↦ t · (−β · decMarkCorrBg … Y …
u Φ)` of the mark `t`, the energy being the block energy `blockEnergyFun Gb Hm … b` of `Gb`; its
derivative at `0` is `−β · decMarkCorrBg … Y … u Φ` (`deriv_decMarkCorrTermBg`). -/
noncomputable def decMarkCorrTermBg (Gb : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱb)
    (T : BgTransport S.G' Gb N)
    (X₁V : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) → Finset (CTorus d L N₁ m₁ (k + 1)))
    (jV : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) → ℕ)
    (𝒦XV : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) → Set (CTorus d L N₁ m₁ (k + 1)))
    (m₀ : ℕ) (a₁ ν : ℝ) (cc : ℂ)
    (F₁ : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) →
      DecParams Gb × RawData d L (N₁ * L ^ m₁) (k + 1) N →
        (Gb.Ω 1 × Fin N → ℂ) × (Gb.Ω 1 → ℂ))
    (Sol : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) →
      Dec2.DecParams (coverOf Gb) × Edat Hm N → (Hm.Ω 1 × Fin N → ℂ) × (Hm.Ω 1 → ℂ))
    (Zm : Finset (unitPts Gb)) (ρ : ℝ) (hp : 0 < S.p₁) (β : ℂ)
    (Θ : RawData d L (N₁ * L ^ m₁) (k + 1) N) (um : ℂ)
    (Φ : ∀ b, (S.blockSplit m₀ hp).Ωb b) :
    Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) → Set (CTorus d L N₁ m₁ (k + 1)) → ℂ → ℂ :=
  fun b Y t => t * (-β * decMarkCorrBg S Gb T (X₁V b) m₀ (jV b) (𝒦XV b) a₁ ν cc (F₁ b) (Sol b)
    (blockEnergyFun Gb Hm (compWeight L a₁) ν k b) Zm Y ρ hp Θ um Φ)

/-- The derivative at `0` of the term of the corrected mark on `Gb` is `−β · decMarkCorrBg`. -/
theorem deriv_decMarkCorrTermBg
    (F₁ : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) →
      DecParams Gb × RawData d L (N₁ * L ^ m₁) (k + 1) N →
        (Gb.Ω 1 × Fin N → ℂ) × (Gb.Ω 1 → ℂ))
    (Sol : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) →
      Dec2.DecParams (coverOf Gb) × Edat Hm N → (Hm.Ω 1 × Fin N → ℂ) × (Hm.Ω 1 → ℂ))
    (ρ : ℝ) (hp : 0 < S.p₁) (β : ℂ) (Θ : RawData d L (N₁ * L ^ m₁) (k + 1) N) (um : ℂ)
    (Φ : ∀ b, (S.blockSplit m₀ hp).Ωb b) (b : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))))
    (Y : Set (CTorus d L N₁ m₁ (k + 1))) :
    deriv (decMarkCorrTermBg S Gb T X₁V jV 𝒦XV m₀ a₁ ν cc F₁ Sol Zm ρ hp β Θ um Φ b Y) 0 =
      -β * decMarkCorrBg S Gb T (X₁V b) m₀ (jV b) (𝒦XV b) a₁ ν cc (F₁ b) (Sol b)
        (blockEnergyFun Gb Hm (compWeight L a₁) ν k b) Zm Y ρ hp Θ um Φ := by
  have h := (hasDerivAt_id (0 : ℂ)).mul_const (-β * decMarkCorrBg S Gb T (X₁V b) m₀ (jV b)
    (𝒦XV b) a₁ ν cc (F₁ b) (Sol b) (blockEnergyFun Gb Hm (compWeight L a₁) ν k b) Zm Y ρ hp Θ
    um Φ)
  have e : decMarkCorrTermBg S Gb T X₁V jV 𝒦XV m₀ a₁ ν cc F₁ Sol Zm ρ hp β Θ um Φ b Y =
      fun t : ℂ => id t * (-β * decMarkCorrBg S Gb T (X₁V b) m₀ (jV b) (𝒦XV b) a₁ ν cc (F₁ b)
        (Sol b) (blockEnergyFun Gb Hm (compWeight L a₁) ν k b) Zm Y ρ hp Θ um Φ) := rfl
  rw [e, h.deriv]
  simp

open Classical in
/-- **The bound of the rooted outputs of the corrected marks on a background generating set, on a
class of domains closed under subsets** (conclusion 1 of `corrected_markedOutDecBg_count_of_bounds`,
which is the case of all domains): from the cubic bound of the corrected marks of the labels of a
class `P` closed under subsets, `‖O Y′‖ ≤ F₀ e^{−(2κ_dec−1) d(Y′)}` for every rooted domain `Y′` of
`P` (the labels of the pairs attached to `Y′` lie in `Y′`). -/
theorem corrected_markedOutDecBg_bound_on
    (hG' : IsLevel S.G' (k + 1)) (hd : 3 ≤ d)
    (hcovV : ∀ b, CovSetup S.G' m₀ (jV b) (XV b) (𝒦XV b))
    (hX₁V : ∀ b, (↑(X₁V b) : Set (CTorus d L N₁ m₁ (k + 1))) = X1 S.G' m₀ (jV b) (𝒦XV b))
    (hoptV : ∀ b, ∃ (W₀ : Finset (CTorus d L N₁ m₁ (k + 1)))
      (E₀ : Finset (CTorus d L N₁ m₁ (k + 1) × CTorus d L N₁ m₁ (k + 1))),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ XV b) ∧ MeetsOne m₀ (jV b) (𝒦XV b) W₀ ∧
        bondCost (scaleW L m₀ m₁ (jV b)) E₀ = treeLenCovOne m₀ (jV b) (XV b))
    (hZV : ∀ b, readSites Hm k b ⊆ ↑(X₁V b))
    (hκ1 : 1 ≤ 2 * κdec)
    (zr : RootIdx d L N₁ m₁ (k + 1))
    (F₁ : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) →
      DecParams Gb × RawData d L (N₁ * L ^ m₁) (k + 1) N →
        (Gb.Ω 1 × Fin N → ℂ) × (Gb.Ω 1 → ℂ))
    (Sol : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) →
      Dec2.DecParams (coverOf Gb) × Edat Hm N → (Hm.Ω 1 × Fin N → ℂ) × (Hm.Ω 1 → ℂ))
    {ρ : ℝ} (hp : 0 < S.p₁) (β : ℂ) (Θ : RawData d L (N₁ * L ^ m₁) (k + 1) N)
    {R U Est : ℝ} (hR : 0 < R) {um : ℂ} (Φ : ∀ b, (S.blockSplit m₀ hp).Ωb b)
    (P : Set (CTorus d L N₁ m₁ (k + 1)) → Prop) (hP : ∀ Y Y', Y ⊆ Y' → P Y' → P Y)
    (hbd : ∀ b, ∀ Y, P Y → ‖decMarkCorrBg S Gb T (X₁V b) m₀ (jV b) (𝒦XV b) a₁ ν cc (F₁ b)
        (Sol b) (blockEnergyFun Gb Hm (compWeight L a₁) ν k b) Zm Y ρ hp Θ um Φ‖ ≤
      4 * (Est * Real.exp (-2 * κdec * treeLenCov S.G' m₀ Y) / R) * (U / R) ^ 2) :
    ∀ Y', P Y' → ‖markedOutDec m₀ (fun _ => Set.univ)
          (fun b => polyDom S.G' (X₁V b) m₀ (jV b) (𝒦XV b)) zr
          (decMarkCorrTermBg S Gb T X₁V jV 𝒦XV m₀ a₁ ν cc F₁ Sol Zm ρ hp β Θ um Φ) Y'‖ ≤
        ‖β‖ * 4 * ‖Est‖ * U ^ 2 / R ^ 3 *
          (c1 d L * ((L : ℝ) ^ (m₀ + m₁)) ^ d) *
          ((nFibre d L : ℝ) * Real.exp ((2 * κdec - 1) * cBr d L)) *
          Real.exp (-(2 * κdec - 1) * treeLenCovOne m₀ (k + 1) Y') := by
  classical
  set E : ℝ := ‖Est‖ with hE
  have hN : L ^ m₀ ∣ N₁ := (hcovV zr).hN
  have hdom : ∀ b, ∀ Y ∈ polyDom S.G' (X₁V b) m₀ (jV b) (𝒦XV b), IsDj m₀ (k + 1) Y :=
    fun b Y hY => isDj_of_polymerDomains (fun i : ParIdx S.G' (↑(X₁V b) :
      Set (CTorus d L N₁ m₁ (k + 1))) => i.1.1) hG' (hcovV b) hd (fun i => i.1.2) (hoptV b) hY
  -- the terms
  have hterm : ∀ b, ∀ Y, P Y → ‖deriv (decMarkCorrTermBg S Gb T X₁V jV 𝒦XV m₀ a₁ ν cc F₁ Sol Zm
      ρ hp β Θ um Φ b Y) 0‖ ≤ (‖β‖ * 4 * E * U ^ 2 / R ^ 3) *
      Real.exp (-(2 * κdec) * treeLenCovOne m₀ (k + 1) Y) := by
    intro b Y hY
    rw [deriv_decMarkCorrTermBg, norm_mul, norm_neg]
    have h3 := hbd b Y hY
    rw [treeLenCov_eq_treeLenCovOne hG' m₀ Y] at h3
    have hex : Real.exp (-2 * κdec * treeLenCovOne m₀ (k + 1) Y) =
        Real.exp (-(2 * κdec) * treeLenCovOne m₀ (k + 1) Y) := by congr 1; ring
    rw [hex] at h3
    have hee := Real.exp_pos (-(2 * κdec) * treeLenCovOne m₀ (k + 1) Y)
    have hEle : Est ≤ E := Real.le_norm_self _
    have h4 : 4 * (Est * Real.exp (-(2 * κdec) * treeLenCovOne m₀ (k + 1) Y) / R) * (U / R) ^ 2 ≤
        4 * E * U ^ 2 / R ^ 3 * Real.exp (-(2 * κdec) * treeLenCovOne m₀ (k + 1) Y) := by
      have e : 4 * E * U ^ 2 / R ^ 3 * Real.exp (-(2 * κdec) * treeLenCovOne m₀ (k + 1) Y) =
          4 * (E * Real.exp (-(2 * κdec) * treeLenCovOne m₀ (k + 1) Y) / R) * (U / R) ^ 2 := by
        field_simp
      rw [e]
      gcongr
    calc ‖β‖ * ‖decMarkCorrBg S Gb T (X₁V b) m₀ (jV b) (𝒦XV b) a₁ ν cc (F₁ b) (Sol b)
          (blockEnergyFun Gb Hm (compWeight L a₁) ν k b) Zm Y ρ hp Θ um Φ‖
        ≤ ‖β‖ * (4 * E * U ^ 2 / R ^ 3 *
            Real.exp (-(2 * κdec) * treeLenCovOne m₀ (k + 1) Y)) :=
          mul_le_mul_of_nonneg_left (h3.trans h4) (norm_nonneg _)
      _ = _ := by ring
  have hC₀ : 0 ≤ ‖β‖ * 4 * E * U ^ 2 / R ^ 3 := by positivity
  have hcount := card_markedIdx_fibre_le_dec hG' hd zr hcovV hX₁V hoptV hZV (Hm := Hm)
  have hM : 0 ≤ c1 d L * ((L : ℝ) ^ (m₀ + m₁)) ^ d := by
    have hc1 : 0 ≤ c1 d L := by unfold c1; positivity
    positivity
  intro Y' hY'
  refine (norm_markedOutDec_le_of_term_bounds_on hN (fun _ => Set.univ)
    (fun b => polyDom S.G' (X₁V b) m₀ (jV b) (𝒦XV b)) hdom zr
    (decMarkCorrTermBg S Gb T X₁V jV 𝒦XV m₀ a₁ ν cc F₁ Sol Zm ρ hp β Θ um Φ)
    hC₀ hM hκ1 P hP (fun q _ hq => hterm q.1 q.2 hq) hcount hY').trans (le_of_eq ?_)
  ring

/-- **The rooted count of the corrected marks on a background generating set, from the term
bounds.**  Let the covers of the blocks be as in `marked_count_scaled_dec` (on the step's set
`S.G'`), let the corrected marks of the pairs `(F₁ b, Sol b)` of `Gb` at `(Θ, um, Φ)` satisfy the
cubic bound `4 (E_* e^{−2κ_dec d^cov(Y)} / R) (U / R)²` (`hbd`) and vanish on the labels whose
thickening misses the fine block of the root `zr` (`hmiss`).  Then the rooted outputs
`O Y′ = markedOutDec … (decMarkCorrTermBg …) Y′` satisfy, with
`J = c₁ M^d · n_Fibre · e^{(2κ_dec−1) c_Br}`, `M = L^{m₀+m₁}`, `F₀ = ‖β‖ · 4 ‖E_*‖ U² / R³ · J`:

1. `‖O Y′‖ ≤ F₀ e^{−(2κ_dec−1) d(Y′)}`;
2. `∑_{Y′ ∈ 𝒴_zr} ‖O Y′‖ e^{a'' d(Y′)} ≤ F₀ K₀(2κ_dec−1−a'')` when `a_Ent + 1 ≤ 2κ_dec−1−a''`;
3. if `O Y′ ≠ 0` then `Y′` is a union of cells and the root cube is one of its cubes;
4. `∑_{Y′ ∈ 𝒴_zr} O Y′ = ∑_b ∑_{Y ∈ 𝒟_b} (−β · decMarkCorrBg … Y …)`. -/
theorem corrected_markedOutDecBg_count_of_bounds
    (hG' : IsLevel S.G' (k + 1)) (hd : 3 ≤ d) (hL : 2 ≤ L)
    (hcovV : ∀ b, CovSetup S.G' m₀ (jV b) (XV b) (𝒦XV b))
    (hX₁V : ∀ b, (↑(X₁V b) : Set (CTorus d L N₁ m₁ (k + 1))) = X1 S.G' m₀ (jV b) (𝒦XV b))
    (hoptV : ∀ b, ∃ (W₀ : Finset (CTorus d L N₁ m₁ (k + 1)))
      (E₀ : Finset (CTorus d L N₁ m₁ (k + 1) × CTorus d L N₁ m₁ (k + 1))),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ XV b) ∧ MeetsOne m₀ (jV b) (𝒦XV b) W₀ ∧
        bondCost (scaleW L m₀ m₁ (jV b)) E₀ = treeLenCovOne m₀ (jV b) (XV b))
    (hZV : ∀ b, readSites Hm k b ⊆ ↑(X₁V b))
    (hκ1 : 1 ≤ 2 * κdec)
    (zr : RootIdx d L N₁ m₁ (k + 1))
    (F₁ : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) →
      DecParams Gb × RawData d L (N₁ * L ^ m₁) (k + 1) N →
        (Gb.Ω 1 × Fin N → ℂ) × (Gb.Ω 1 → ℂ))
    (Sol : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) →
      Dec2.DecParams (coverOf Gb) × Edat Hm N → (Hm.Ω 1 × Fin N → ℂ) × (Hm.Ω 1 → ℂ))
    {ρ : ℝ} (hp : 0 < S.p₁) (β : ℂ) (Θ : RawData d L (N₁ * L ^ m₁) (k + 1) N)
    {R U Est : ℝ} (hR : 0 < R) {um : ℂ} (Φ : ∀ b, (S.blockSplit m₀ hp).Ωb b)
    (hbd : ∀ b, ∀ Y, ‖decMarkCorrBg S Gb T (X₁V b) m₀ (jV b) (𝒦XV b) a₁ ν cc (F₁ b) (Sol b)
        (blockEnergyFun Gb Hm (compWeight L a₁) ν k b) Zm Y ρ hp Θ um Φ‖ ≤
      4 * (Est * Real.exp (-2 * κdec * treeLenCov S.G' m₀ Y) / R) * (U / R) ^ 2)
    (hmiss : ∀ b, ∀ Y ∈ polyDom S.G' (X₁V b) m₀ (jV b) (𝒦XV b), psiThick Y ∩ fineBlock zr = ∅ →
      decMarkCorrBg S Gb T (X₁V b) m₀ (jV b) (𝒦XV b) a₁ ν cc (F₁ b) (Sol b)
        (blockEnergyFun Gb Hm (compWeight L a₁) ν k b) Zm Y ρ hp Θ um Φ = 0) :
    (∀ Y', ‖markedOutDec m₀ (fun _ => Set.univ)
          (fun b => polyDom S.G' (X₁V b) m₀ (jV b) (𝒦XV b)) zr
          (decMarkCorrTermBg S Gb T X₁V jV 𝒦XV m₀ a₁ ν cc F₁ Sol Zm ρ hp β Θ um Φ) Y'‖ ≤
        ‖β‖ * 4 * ‖Est‖ * U ^ 2 / R ^ 3 *
          (c1 d L * ((L : ℝ) ^ (m₀ + m₁)) ^ d) *
          ((nFibre d L : ℝ) * Real.exp ((2 * κdec - 1) * cBr d L)) *
          Real.exp (-(2 * κdec - 1) * treeLenCovOne m₀ (k + 1) Y')) ∧
    (∀ {a'' : ℝ}, aEnt d L + 1 ≤ 2 * κdec - 1 - a'' →
      ∑ Y' : {Y' // Y' ∈ bridgeFamily m₀ (fun _ => Set.univ)
          (fun b => polyDom S.G' (X₁V b) m₀ (jV b) (𝒦XV b)) zr},
        ‖markedOutDec m₀ (fun _ => Set.univ)
            (fun b => polyDom S.G' (X₁V b) m₀ (jV b) (𝒦XV b)) zr
            (decMarkCorrTermBg S Gb T X₁V jV 𝒦XV m₀ a₁ ν cc F₁ Sol Zm ρ hp β Θ um Φ) Y'.1‖ *
          Real.exp (a'' * treeLenCovOne m₀ (k + 1) Y'.1) ≤
        ‖β‖ * 4 * ‖Est‖ * U ^ 2 / R ^ 3 *
          (c1 d L * ((L : ℝ) ^ (m₀ + m₁)) ^ d) *
          ((nFibre d L : ℝ) * Real.exp ((2 * κdec - 1) * cBr d L)) *
          K0 d L (2 * κdec - 1 - a'')) ∧
    (∀ Y', markedOutDec m₀ (fun _ => Set.univ)
          (fun b => polyDom S.G' (X₁V b) m₀ (jV b) (𝒦XV b)) zr
          (decMarkCorrTermBg S Gb T X₁V jV 𝒦XV m₀ a₁ ν cc F₁ Sol Zm ρ hp β Θ um Φ) Y' ≠ 0 →
        IsDj m₀ (k + 1) Y' ∧ rootCube (m₀ := m₀) zr ∈ blocksOf m₀ (k + 1) Set.univ Y') ∧
    ∑ Y' ∈ bridgeFamily m₀ (fun _ => Set.univ)
        (fun b => polyDom S.G' (X₁V b) m₀ (jV b) (𝒦XV b)) zr,
      markedOutDec m₀ (fun _ => Set.univ)
        (fun b => polyDom S.G' (X₁V b) m₀ (jV b) (𝒦XV b)) zr
        (decMarkCorrTermBg S Gb T X₁V jV 𝒦XV m₀ a₁ ν cc F₁ Sol Zm ρ hp β Θ um Φ) Y' =
      ∑ b, ∑ Y ∈ polyDom S.G' (X₁V b) m₀ (jV b) (𝒦XV b),
        -β * decMarkCorrBg S Gb T (X₁V b) m₀ (jV b) (𝒦XV b) a₁ ν cc (F₁ b) (Sol b)
          (blockEnergyFun Gb Hm (compWeight L a₁) ν k b) Zm Y ρ hp Θ um Φ := by
  classical
  set E : ℝ := ‖Est‖ with hE
  have hN : L ^ m₀ ∣ N₁ := (hcovV zr).hN
  have hdom : ∀ b, ∀ Y ∈ polyDom S.G' (X₁V b) m₀ (jV b) (𝒦XV b), IsDj m₀ (k + 1) Y :=
    fun b Y hY => isDj_of_polymerDomains (fun i : ParIdx S.G' (↑(X₁V b) :
      Set (CTorus d L N₁ m₁ (k + 1))) => i.1.1) hG' (hcovV b) hd (fun i => i.1.2) (hoptV b) hY
  have hB : ∀ Y', ‖markedOutDec m₀ (fun _ => Set.univ)
          (fun b => polyDom S.G' (X₁V b) m₀ (jV b) (𝒦XV b)) zr
          (decMarkCorrTermBg S Gb T X₁V jV 𝒦XV m₀ a₁ ν cc F₁ Sol Zm ρ hp β Θ um Φ) Y'‖ ≤
        ‖β‖ * 4 * E * U ^ 2 / R ^ 3 * (c1 d L * ((L : ℝ) ^ (m₀ + m₁)) ^ d) *
          ((nFibre d L : ℝ) * Real.exp ((2 * κdec - 1) * cBr d L)) *
          Real.exp (-(2 * κdec - 1) * treeLenCovOne m₀ (k + 1) Y') := fun Y' =>
    corrected_markedOutDecBg_bound_on S hG' hd hcovV hX₁V hoptV hZV hκ1 zr F₁ Sol hp β Θ hR Φ
      (fun _ => True) (fun _ _ _ _ => trivial) (fun b Y _ => hbd b Y) Y' trivial
  have hM : 0 ≤ c1 d L * ((L : ℝ) ^ (m₀ + m₁)) ^ d := by
    have hc1 : 0 ≤ c1 d L := by unfold c1; positivity
    positivity
  have hF₀ : 0 ≤ ‖β‖ * 4 * E * U ^ 2 / R ^ 3 * (c1 d L * ((L : ℝ) ^ (m₀ + m₁)) ^ d) *
      ((nFibre d L : ℝ) * Real.exp ((2 * κdec - 1) * cBr d L)) := by
    have : (0 : ℝ) ≤ (nFibre d L : ℝ) := by unfold nFibre; positivity
    positivity
  have hres : ∑ Y' ∈ bridgeFamily m₀ (fun _ => Set.univ)
      (fun b => polyDom S.G' (X₁V b) m₀ (jV b) (𝒦XV b)) zr,
      markedOutDec m₀ (fun _ => Set.univ)
        (fun b => polyDom S.G' (X₁V b) m₀ (jV b) (𝒦XV b)) zr
        (decMarkCorrTermBg S Gb T X₁V jV 𝒦XV m₀ a₁ ν cc F₁ Sol Zm ρ hp β Θ um Φ) Y' =
      ∑ b, ∑ Y ∈ polyDom S.G' (X₁V b) m₀ (jV b) (𝒦XV b),
        deriv (decMarkCorrTermBg S Gb T X₁V jV 𝒦XV m₀ a₁ ν cc F₁ Sol Zm ρ hp β Θ um Φ b Y) 0 := by
    refine sum_markedOutDec_eq_sum_of_vanishing _ _ zr _ fun b Y hY hnot => ?_
    have hmissY : psiThick Y ∩ fineBlock zr = ∅ := by
      by_contra hne
      obtain ⟨y, hy⟩ := Set.nonempty_iff_ne_empty.2 hne
      exact hnot (mem_markedIdx.2 ⟨hY, ⟨rootSite zr, trivial, rootSite_mem_fineBlock zr⟩, ⟨y, hy⟩⟩)
    rw [deriv_decMarkCorrTermBg, hmiss b Y hY hmissY]
    simp
  refine ⟨hB, fun {a''} ha => sum_norm_markedOutDec_le_of_bound hN hL (fun _ => Set.univ)
      (fun b => polyDom S.G' (X₁V b) m₀ (jV b) (𝒦XV b)) hdom zr _ hF₀ hB ha,
    fun Y' h => rootCube_mem_of_markedOutDec_ne_zero hN hL hdom zr _ h, ?_⟩
  rw [hres]
  exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun Y _ =>
    deriv_decMarkCorrTermBg S F₁ Sol ρ hp β Θ um Φ b Y

end CountBg

section Vanishing

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ ϱm : ℝ}
  (S : StepSetting d L N₁ m₁ k N ϱ) {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}
variable {a₁ ν BG BG₂ κ eps δ₁ κdec cψ : ℝ} {X₁f : Finset (CTorus d L N₁ m₁ (k + 1))}
variable {m₀ j : ℕ} {𝒦X : Set (CTorus d L N₁ m₁ (k + 1))}
variable {cc : ℂ} {Zm : Finset (unitPts S.G')}
  {z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1)))}
variable {F₁ : DecParams S.G' × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      (S.G'.Ω 1 × Fin N → ℂ) × (S.G'.Ω 1 → ℂ)}
variable {Sol : Dec2.DecParams (coverOf S.G') × Edat Hm N → (Hm.Ω 1 × Fin N → ℂ) × (Hm.Ω 1 → ℂ)}

/-- **The decoupled mark vanishes where the mask misses the label.**  By clause 8 of
`MarkedBlockExpansionDecPair`, if no site of `Y` has its unit point in the mask `Zm`, the
`t`-derivative at `0` of the localized term vanishes at every first mark of the disc; this is
`decMarkG … um Φ = 0`. -/
theorem decMarkG_eq_zero_of_mask_miss
    (hP : MarkedBlockExpansionDecPair N Hm S.hG' cc a₁ ν BG BG₂ κ eps δ₁ κdec cψ Zm X₁f m₀ j 𝒦X z
      F₁ Sol)
    {ρ : ℝ} (hρ : 0 < ρ) (hρc : ρ ≤ cψ) (hp : 0 < S.p₁)
    {Θ : RawData d L (N₁ * L ^ m₁) (k + 1) N}
    (hΘ : Θ ∈ XiCRaw S.G' (compWeight L a₁) ν (k + 1) 1 eps)
    {um : ℂ} (hum : (‖um‖ + ‖(0 : ℂ)‖) * markedRad d L N k a₁ κ cψ cc < δ₁)
    {Y : Set (CTorus d L N₁ m₁ (k + 1))} (hY : ∀ y ∈ Y, unitPt S.hG' y ∉ Zm)
    (Φ : ∀ b, (S.blockSplit m₀ hp).Ωb b) :
    decMarkG S X₁f m₀ j 𝒦X a₁ ν cc F₁ Sol (blockEnergyFun S.G' Hm (compWeight L a₁) ν k z) Zm
      Y ρ hp Θ um Φ = 0 :=
  decMarkGBg_eq_zero_of S (T := BgTransport.self S.hG')
    (fun u hu => hP.2.2.2.2.2.2.2 um hum Y hY u hu) hρ hρc hp hΘ Φ

/-- **The corrected mark vanishes where the mask misses the label.**  If no site of `Y` has its
unit point in the mask, then `decMarkCorr … Y … um Φ = 0` for every first mark `um` of the disc:
the decoupled mark is zero on a neighbourhood of `0` in the first mark, so are its value at `0`
and its derivative at `0`. -/
theorem decMarkCorr_eq_zero_of_mask_miss
    (hP : MarkedBlockExpansionDecPair N Hm S.hG' cc a₁ ν BG BG₂ κ eps δ₁ κdec cψ Zm X₁f m₀ j 𝒦X z
      F₁ Sol)
    {ρ : ℝ} (hρ : 0 < ρ) (hρc : ρ ≤ cψ) (hp : 0 < S.p₁) (hδ : 0 < δ₁)
    {Θ : RawData d L (N₁ * L ^ m₁) (k + 1) N}
    (hΘ : Θ ∈ XiCRaw S.G' (compWeight L a₁) ν (k + 1) 1 eps)
    {um : ℂ} (hum : (‖um‖ + ‖(0 : ℂ)‖) * markedRad d L N k a₁ κ cψ cc < δ₁)
    {Y : Set (CTorus d L N₁ m₁ (k + 1))} (hY : ∀ y ∈ Y, unitPt S.hG' y ∉ Zm)
    (Φ : ∀ b, (S.blockSplit m₀ hp).Ωb b) :
    decMarkCorr S X₁f m₀ j 𝒦X a₁ ν cc F₁ Sol (blockEnergyFun S.G' Hm (compWeight L a₁) ν k z)
      Zm Y ρ hp Θ um Φ = 0 :=
  decMarkCorrBg_eq_zero_of S (T := BgTransport.self S.hG')
    (fun v hv u hu => hP.2.2.2.2.2.2.2 v hv Y hY u hu) hρ hρc hp hδ hΘ hum Φ

end Vanishing

section Count

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ ϱm : ℝ}
  (S : StepSetting d L N₁ m₁ k N ϱ) {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}
variable {a₁ ν BG BG₂ κ eps δ₁ κdec cψ : ℝ} {m₀ : ℕ} {cc : ℂ} {Zm : Finset (unitPts S.G')}
variable {jV : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) → ℕ}
  {XV 𝒦XV : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) → Set (CTorus d L N₁ m₁ (k + 1))}
  {X₁V : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) → Finset (CTorus d L N₁ m₁ (k + 1))}

/-- **The terms of the corrected marks.**  For the block `b`, the label `Y`, and the pair
`(F₁ b, Sol b)`, the function `t ↦ t · (−β · decMarkCorr … Y … u Φ)` of the mark `t`; its
derivative at `0` is `−β · decMarkCorr … Y … u Φ` (`deriv_decMarkCorrTerm`) (`decMarkCorrTermBg`
at `Gb = S.G'` with the transport `BgTransport.self`). -/
noncomputable def decMarkCorrTerm
    (X₁V : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) → Finset (CTorus d L N₁ m₁ (k + 1)))
    (jV : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) → ℕ)
    (𝒦XV : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) → Set (CTorus d L N₁ m₁ (k + 1)))
    (m₀ : ℕ) (a₁ ν : ℝ) (cc : ℂ)
    (F₁ : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) →
      DecParams S.G' × RawData d L (N₁ * L ^ m₁) (k + 1) N →
        (S.G'.Ω 1 × Fin N → ℂ) × (S.G'.Ω 1 → ℂ))
    (Sol : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) →
      Dec2.DecParams (coverOf S.G') × Edat Hm N → (Hm.Ω 1 × Fin N → ℂ) × (Hm.Ω 1 → ℂ))
    (Zm : Finset (unitPts S.G')) (ρ : ℝ) (hp : 0 < S.p₁) (β : ℂ)
    (Θ : RawData d L (N₁ * L ^ m₁) (k + 1) N) (um : ℂ)
    (Φ : ∀ b, (S.blockSplit m₀ hp).Ωb b) :
    Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) → Set (CTorus d L N₁ m₁ (k + 1)) → ℂ → ℂ :=
  decMarkCorrTermBg S S.G' (BgTransport.self S.hG') X₁V jV 𝒦XV m₀ a₁ ν cc F₁ Sol Zm ρ hp β Θ um Φ

/-- The term of the corrected mark at `(b, Y, t)` is `t · (−β · decMarkCorr … Y …)`. -/
theorem decMarkCorrTerm_apply
    (X₁V : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) → Finset (CTorus d L N₁ m₁ (k + 1)))
    (jV : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) → ℕ)
    (𝒦XV : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) → Set (CTorus d L N₁ m₁ (k + 1)))
    (m₀ : ℕ) (a₁ ν : ℝ) (cc : ℂ)
    (F₁ : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) →
      DecParams S.G' × RawData d L (N₁ * L ^ m₁) (k + 1) N →
        (S.G'.Ω 1 × Fin N → ℂ) × (S.G'.Ω 1 → ℂ))
    (Sol : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) →
      Dec2.DecParams (coverOf S.G') × Edat Hm N → (Hm.Ω 1 × Fin N → ℂ) × (Hm.Ω 1 → ℂ))
    (Zm : Finset (unitPts S.G')) (ρ : ℝ) (hp : 0 < S.p₁) (β : ℂ)
    (Θ : RawData d L (N₁ * L ^ m₁) (k + 1) N) (um : ℂ)
    (Φ : ∀ b, (S.blockSplit m₀ hp).Ωb b) (b : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))))
    (Y : Set (CTorus d L N₁ m₁ (k + 1))) (t : ℂ) :
    decMarkCorrTerm S X₁V jV 𝒦XV m₀ a₁ ν cc F₁ Sol Zm ρ hp β Θ um Φ b Y t =
      t * (-β * decMarkCorr S (X₁V b) m₀ (jV b) (𝒦XV b) a₁ ν cc (F₁ b) (Sol b)
        (blockEnergyFun S.G' Hm (compWeight L a₁) ν k b) Zm Y ρ hp Θ um Φ) := rfl

/-- The derivative at `0` of the term of the corrected mark is `−β · decMarkCorr`. -/
theorem deriv_decMarkCorrTerm
    (F₁ : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) →
      DecParams S.G' × RawData d L (N₁ * L ^ m₁) (k + 1) N →
        (S.G'.Ω 1 × Fin N → ℂ) × (S.G'.Ω 1 → ℂ))
    (Sol : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) →
      Dec2.DecParams (coverOf S.G') × Edat Hm N → (Hm.Ω 1 × Fin N → ℂ) × (Hm.Ω 1 → ℂ))
    (ρ : ℝ) (hp : 0 < S.p₁) (β : ℂ) (Θ : RawData d L (N₁ * L ^ m₁) (k + 1) N) (um : ℂ)
    (Φ : ∀ b, (S.blockSplit m₀ hp).Ωb b) (b : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))))
    (Y : Set (CTorus d L N₁ m₁ (k + 1))) :
    deriv (decMarkCorrTerm S X₁V jV 𝒦XV m₀ a₁ ν cc F₁ Sol Zm ρ hp β Θ um Φ b Y) 0 =
      -β * decMarkCorr S (X₁V b) m₀ (jV b) (𝒦XV b) a₁ ν cc (F₁ b) (Sol b)
        (blockEnergyFun S.G' Hm (compWeight L a₁) ν k b) Zm Y ρ hp Θ um Φ :=
  deriv_decMarkCorrTermBg S (T := BgTransport.self S.hG') F₁ Sol ρ hp β Θ um Φ b Y

/-- **The rooted count of the corrected marks.**  Let `(F₁ b, Sol b)` be a pair with the eight
clauses and the joint analyticity statements for every block `b`, let the covers of the blocks
be as in `marked_count_scaled_dec`, and let the mask `Zm` be supported in the fine block of the
root `zr`.  For `Θ` in the chart, a block configuration `Φ`, a first mark `um` with `‖um‖ ≤ U`,
and radii `0 < R`, `2 U ≤ R`, `(R + R) · markedRad < δ₁`, the rooted outputs
`O Y′ = markedOutDec … (decMarkCorrTerm …) Y′` satisfy, with `E_* = energyBdScaled …`,
`J = c₁ M^d · n_Fibre · e^{(2κ_dec−1) c_Br}`, `M = L^{m₀+m₁}`, `F₀ = ‖β‖ · 4 ‖E_*‖ U² / R³ · J`:

1. `‖O Y′‖ ≤ F₀ e^{−(2κ_dec−1) d(Y′)}`;
2. `∑_{Y′ ∈ 𝒴_zr} ‖O Y′‖ e^{a'' d(Y′)} ≤ F₀ K₀(2κ_dec−1−a'')` when `a_Ent + 1 ≤ 2κ_dec−1−a''`;
3. if `O Y′ ≠ 0` then `Y′` is a union of cells and the root cube is one of its cubes;
4. `∑_{Y′ ∈ 𝒴_zr} O Y′ = ∑_b ∑_{Y ∈ 𝒟_b} (−β · decMarkCorr … Y …)`. -/
theorem corrected_markedOutDec_count
    (hG' : IsLevel S.G' (k + 1)) (hd : 3 ≤ d) (hL : 2 ≤ L)
    (hcovV : ∀ b, CovSetup S.G' m₀ (jV b) (XV b) (𝒦XV b))
    (hX₁V : ∀ b, (↑(X₁V b) : Set (CTorus d L N₁ m₁ (k + 1))) = X1 S.G' m₀ (jV b) (𝒦XV b))
    (hoptV : ∀ b, ∃ (W₀ : Finset (CTorus d L N₁ m₁ (k + 1)))
      (E₀ : Finset (CTorus d L N₁ m₁ (k + 1) × CTorus d L N₁ m₁ (k + 1))),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ XV b) ∧ MeetsOne m₀ (jV b) (𝒦XV b) W₀ ∧
        bondCost (scaleW L m₀ m₁ (jV b)) E₀ = treeLenCovOne m₀ (jV b) (XV b))
    (hZV : ∀ b, readSites Hm k b ⊆ ↑(X₁V b))
    (hκ1 : 1 ≤ 2 * κdec)
    (zr : RootIdx d L N₁ m₁ (k + 1))
    (hZm : ∀ p ∈ Zm, ∀ y, unitPt S.hG' y = p → y ∈ fineBlock zr)
    (F₁ : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) →
      DecParams S.G' × RawData d L (N₁ * L ^ m₁) (k + 1) N →
        (S.G'.Ω 1 × Fin N → ℂ) × (S.G'.Ω 1 → ℂ))
    (Sol : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) →
      Dec2.DecParams (coverOf S.G') × Edat Hm N → (Hm.Ω 1 × Fin N → ℂ) × (Hm.Ω 1 → ℂ))
    (hP : ∀ b, MarkedBlockExpansionDecPair N Hm S.hG' cc a₁ ν BG BG₂ κ eps δ₁ κdec cψ Zm (X₁V b)
      m₀ (jV b) (𝒦XV b) b (F₁ b) (Sol b))
    (hJ2 : ∀ b, ∀ Y, AnalyticOnNhd ℂ
        (fun p : (RawData d L (N₁ * L ^ m₁) (k + 1) N × (unitPts S.G' × Fin N → ℂ)) × (ℂ × ℂ) =>
          evDec (X₁V b) m₀ (jV b) (𝒦XV b) a₁ ν S.hG' cc (F₁ b) (Sol b)
            (blockEnergyFun S.G' Hm (compWeight L a₁) ν k b) Zm p.2.1 p.2.2 Y p.1)
        ((XiCRaw S.G' (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
          {ψh : unitPts S.G' × Fin N → ℂ | ∀ q, ‖ψh q‖ ≤ cψ}) ×ˢ
          {w : ℂ × ℂ | (‖w.1‖ + ‖w.2‖) * markedRad d L N k a₁ κ cψ cc < δ₁}))
    (hJ4 : ∀ b, ∀ Y, ∀ ψh : unitPts S.G' × Fin N → ℂ, (∀ q, ‖ψh q‖ ≤ cψ) →
        ∀ a b' : ℝ, 0 ≤ a → 0 < b' → (a + b') * markedRad d L N k a₁ κ cψ cc < δ₁ →
        AnalyticOnNhd ℂ (fun p : physParam N S × ℂ => deriv (fun t : ℂ =>
          evDec (X₁V b) m₀ (jV b) (𝒦XV b) a₁ ν S.hG' cc (F₁ b) (Sol b)
            (blockEnergyFun S.G' Hm (compWeight L a₁) ν k b) Zm p.2 t Y
            ((p.1.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N), ψh)) 0)
          (physV S a₁ ν eps ×ˢ Metric.ball (0 : ℂ) a))
    {ρ : ℝ} (hρ : 0 < ρ) (hρc : ρ ≤ cψ) (hp : 0 < S.p₁) (hδ : 0 < δ₁)
    (β : ℂ) {Θ : RawData d L (N₁ * L ^ m₁) (k + 1) N}
    (hΘ : Θ ∈ XiCRaw S.G' (compWeight L a₁) ν (k + 1) 1 eps)
    {R U : ℝ} (hR : 0 < R) (hRR : (R + R) * markedRad d L N k a₁ κ cψ cc < δ₁) (hUR : 2 * U ≤ R)
    {um : ℂ} (hum : ‖um‖ ≤ U) (Φ : ∀ b, (S.blockSplit m₀ hp).Ωb b) :
    (∀ Y', ‖markedOutDec m₀ (fun _ => Set.univ)
          (fun b => polyDom S.G' (X₁V b) m₀ (jV b) (𝒦XV b)) zr
          (decMarkCorrTerm S X₁V jV 𝒦XV m₀ a₁ ν cc F₁ Sol Zm ρ hp β Θ um Φ) Y'‖ ≤
        ‖β‖ * 4 * ‖energyBdScaled d L N (compWeight L a₁) k
          (cK2' d L N (famConst d L BG₂ κ) * δ₁) δ₁ (rho4 d L N BG κ)‖ * U ^ 2 / R ^ 3 *
          (c1 d L * ((L : ℝ) ^ (m₀ + m₁)) ^ d) *
          ((nFibre d L : ℝ) * Real.exp ((2 * κdec - 1) * cBr d L)) *
          Real.exp (-(2 * κdec - 1) * treeLenCovOne m₀ (k + 1) Y')) ∧
    (∀ {a'' : ℝ}, aEnt d L + 1 ≤ 2 * κdec - 1 - a'' →
      ∑ Y' : {Y' // Y' ∈ bridgeFamily m₀ (fun _ => Set.univ)
          (fun b => polyDom S.G' (X₁V b) m₀ (jV b) (𝒦XV b)) zr},
        ‖markedOutDec m₀ (fun _ => Set.univ)
            (fun b => polyDom S.G' (X₁V b) m₀ (jV b) (𝒦XV b)) zr
            (decMarkCorrTerm S X₁V jV 𝒦XV m₀ a₁ ν cc F₁ Sol Zm ρ hp β Θ um Φ) Y'.1‖ *
          Real.exp (a'' * treeLenCovOne m₀ (k + 1) Y'.1) ≤
        ‖β‖ * 4 * ‖energyBdScaled d L N (compWeight L a₁) k
          (cK2' d L N (famConst d L BG₂ κ) * δ₁) δ₁ (rho4 d L N BG κ)‖ * U ^ 2 / R ^ 3 *
          (c1 d L * ((L : ℝ) ^ (m₀ + m₁)) ^ d) *
          ((nFibre d L : ℝ) * Real.exp ((2 * κdec - 1) * cBr d L)) *
          K0 d L (2 * κdec - 1 - a'')) ∧
    (∀ Y', markedOutDec m₀ (fun _ => Set.univ)
          (fun b => polyDom S.G' (X₁V b) m₀ (jV b) (𝒦XV b)) zr
          (decMarkCorrTerm S X₁V jV 𝒦XV m₀ a₁ ν cc F₁ Sol Zm ρ hp β Θ um Φ) Y' ≠ 0 →
        IsDj m₀ (k + 1) Y' ∧ rootCube (m₀ := m₀) zr ∈ blocksOf m₀ (k + 1) Set.univ Y') ∧
    ∑ Y' ∈ bridgeFamily m₀ (fun _ => Set.univ)
        (fun b => polyDom S.G' (X₁V b) m₀ (jV b) (𝒦XV b)) zr,
      markedOutDec m₀ (fun _ => Set.univ)
        (fun b => polyDom S.G' (X₁V b) m₀ (jV b) (𝒦XV b)) zr
        (decMarkCorrTerm S X₁V jV 𝒦XV m₀ a₁ ν cc F₁ Sol Zm ρ hp β Θ um Φ) Y' =
      ∑ b, ∑ Y ∈ polyDom S.G' (X₁V b) m₀ (jV b) (𝒦XV b),
        -β * decMarkCorr S (X₁V b) m₀ (jV b) (𝒦XV b) a₁ ν cc (F₁ b) (Sol b)
          (blockEnergyFun S.G' Hm (compWeight L a₁) ν k b) Zm Y ρ hp Θ um Φ := by
  have hU0 : 0 ≤ U := (norm_nonneg _).trans hum
  have hum' : (‖um‖ + ‖(0 : ℂ)‖) * markedRad d L N k a₁ κ cψ cc < δ₁ :=
    mem_markedRadiusSet_of_pos hδ hRR (show ‖um‖ ≤ R by linarith) (by simpa using hR.le)
  exact corrected_markedOutDecBg_count_of_bounds S (T := BgTransport.self S.hG') hG' hd hL hcovV
    hX₁V hoptV hZV hκ1 zr F₁ Sol hp β Θ
    (Est := energyBdScaled d L N (compWeight L a₁) k
      (cK2' d L N (famConst d L BG₂ κ) * δ₁) δ₁ (rho4 d L N BG κ)) hR Φ
    (fun b Y => (decMarkCorr_fields_of_pair S (F₁ b) (Sol b) (hP b) (hJ2 b) (hJ4 b) hρ hρc hp
      hδ).2.2.1 Y Θ hΘ R U hR hRR hUR um hum Φ)
    (fun b Y _ hmissY => decMarkCorr_eq_zero_of_mask_miss S (hP b) hρ hρc hp hδ hΘ hum'
      (fun y hy hmem => by
        have h2 : y ∈ psiThick Y ∩ fineBlock zr := ⟨Or.inl hy, hZm _ hmem y rfl⟩
        rw [hmissY] at h2
        exact h2) Φ)

end Count

end Balaban.Fluctuation
