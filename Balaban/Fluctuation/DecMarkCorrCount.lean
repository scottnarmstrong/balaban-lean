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
-/

@[expose] public section

namespace Balaban.Fluctuation

open MeasureTheory Filter Balaban Balaban.Localization Balaban.Multiscale Balaban.Background
  Balaban.SmallField Balaban.Analysis Balaban.Polymer Balaban.SmallField.Def6 Set

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
  hP.2.2.2.2.2.2.2 um hum Y hY _
    ⟨hΘ, fun p => (S.hatOf_mem m₀ hρ hp Φ p).trans hρc⟩

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
      Zm Y ρ hp Θ um Φ = 0 := by
  have h0 : (‖(0 : ℂ)‖ + ‖(0 : ℂ)‖) * markedRad d L N k a₁ κ cψ cc < δ₁ := by simpa using hδ
  have hopen : IsOpen {t : ℂ | (‖t‖ + ‖(0 : ℂ)‖) * markedRad d L N k a₁ κ cψ cc < δ₁} :=
    isOpen_lt (by fun_prop) continuous_const
  have hev : (fun v : ℂ => decMarkG S X₁f m₀ j 𝒦X a₁ ν cc F₁ Sol
      (blockEnergyFun S.G' Hm (compWeight L a₁) ν k z) Zm Y ρ hp Θ v Φ) =ᶠ[nhds (0 : ℂ)]
      fun _ => 0 := by
    filter_upwards [hopen.mem_nhds h0] with v hv
    exact decMarkG_eq_zero_of_mask_miss S hP hρ hρc hp hΘ hv hY Φ
  unfold decMarkCorr
  rw [decMarkG_eq_zero_of_mask_miss S hP hρ hρc hp hΘ hum hY Φ,
    decMarkG_eq_zero_of_mask_miss S hP hρ hρc hp hΘ h0 hY Φ, hev.deriv_eq]
  simp

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
derivative at `0` is `−β · decMarkCorr … Y … u Φ` (`deriv_decMarkCorrTerm`). -/
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
  fun b Y t => t * (-β * decMarkCorr S (X₁V b) m₀ (jV b) (𝒦XV b) a₁ ν cc (F₁ b) (Sol b)
    (blockEnergyFun S.G' Hm (compWeight L a₁) ν k b) Zm Y ρ hp Θ um Φ)

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
        (blockEnergyFun S.G' Hm (compWeight L a₁) ν k b) Zm Y ρ hp Θ um Φ := by
  have h := (hasDerivAt_id (0 : ℂ)).mul_const (-β * decMarkCorr S (X₁V b) m₀ (jV b) (𝒦XV b) a₁ ν
    cc (F₁ b) (Sol b) (blockEnergyFun S.G' Hm (compWeight L a₁) ν k b) Zm Y ρ hp Θ um Φ)
  have e : decMarkCorrTerm S X₁V jV 𝒦XV m₀ a₁ ν cc F₁ Sol Zm ρ hp β Θ um Φ b Y =
      fun t : ℂ => id t * (-β * decMarkCorr S (X₁V b) m₀ (jV b) (𝒦XV b) a₁ ν cc (F₁ b) (Sol b)
        (blockEnergyFun S.G' Hm (compWeight L a₁) ν k b) Zm Y ρ hp Θ um Φ) := rfl
  rw [e, h.deriv]
  simp

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
  classical
  set E : ℝ := ‖energyBdScaled d L N (compWeight L a₁) k
    (cK2' d L N (famConst d L BG₂ κ) * δ₁) δ₁ (rho4 d L N BG κ)‖ with hE
  have hN : L ^ m₀ ∣ N₁ := (hcovV zr).hN
  have hdom : ∀ b, ∀ Y ∈ polyDom S.G' (X₁V b) m₀ (jV b) (𝒦XV b), IsDj m₀ (k + 1) Y :=
    fun b Y hY => isDj_of_polymerDomains (fun i : ParIdx S.G' (↑(X₁V b) :
      Set (CTorus d L N₁ m₁ (k + 1))) => i.1.1) hG' (hcovV b) hd (fun i => i.1.2) (hoptV b) hY
  have hU0 : 0 ≤ U := (norm_nonneg _).trans hum
  have hum' : (‖um‖ + ‖(0 : ℂ)‖) * markedRad d L N k a₁ κ cψ cc < δ₁ :=
    mem_markedRadiusSet_of_pos hδ hRR (show ‖um‖ ≤ R by linarith) (by simpa using hR.le)
  -- the terms
  have hterm : ∀ b, ∀ Y, ‖deriv (decMarkCorrTerm S X₁V jV 𝒦XV m₀ a₁ ν cc F₁ Sol Zm ρ hp β Θ
      um Φ b Y) 0‖ ≤ (‖β‖ * 4 * E * U ^ 2 / R ^ 3) *
      Real.exp (-(2 * κdec) * treeLenCovOne m₀ (k + 1) Y) := by
    intro b Y
    rw [deriv_decMarkCorrTerm, norm_mul, norm_neg]
    have h3 := (decMarkCorr_fields_of_pair S (F₁ b) (Sol b) (hP b) (hJ2 b) (hJ4 b) hρ hρc hp
      hδ).2.2.1 Y Θ hΘ R U hR hRR hUR um hum Φ
    rw [treeLenCov_eq_treeLenCovOne hG' m₀ Y] at h3
    have hex : Real.exp (-2 * κdec * treeLenCovOne m₀ (k + 1) Y) =
        Real.exp (-(2 * κdec) * treeLenCovOne m₀ (k + 1) Y) := by congr 1; ring
    rw [hex] at h3
    have hee := Real.exp_pos (-(2 * κdec) * treeLenCovOne m₀ (k + 1) Y)
    have hEle : energyBdScaled d L N (compWeight L a₁) k
        (cK2' d L N (famConst d L BG₂ κ) * δ₁) δ₁ (rho4 d L N BG κ) ≤ E :=
      Real.le_norm_self _
    have h4 : 4 * (energyBdScaled d L N (compWeight L a₁) k
        (cK2' d L N (famConst d L BG₂ κ) * δ₁) δ₁ (rho4 d L N BG κ) *
        Real.exp (-(2 * κdec) * treeLenCovOne m₀ (k + 1) Y) / R) * (U / R) ^ 2 ≤
        4 * E * U ^ 2 / R ^ 3 * Real.exp (-(2 * κdec) * treeLenCovOne m₀ (k + 1) Y) := by
      have e : 4 * E * U ^ 2 / R ^ 3 * Real.exp (-(2 * κdec) * treeLenCovOne m₀ (k + 1) Y) =
          4 * (E * Real.exp (-(2 * κdec) * treeLenCovOne m₀ (k + 1) Y) / R) * (U / R) ^ 2 := by
        field_simp
      rw [e]
      gcongr
    calc ‖β‖ * ‖decMarkCorr S (X₁V b) m₀ (jV b) (𝒦XV b) a₁ ν cc (F₁ b) (Sol b)
          (blockEnergyFun S.G' Hm (compWeight L a₁) ν k b) Zm Y ρ hp Θ um Φ‖
        ≤ ‖β‖ * (4 * E * U ^ 2 / R ^ 3 *
            Real.exp (-(2 * κdec) * treeLenCovOne m₀ (k + 1) Y)) :=
          mul_le_mul_of_nonneg_left (h3.trans h4) (norm_nonneg _)
      _ = _ := by ring
  have hC₀ : 0 ≤ ‖β‖ * 4 * E * U ^ 2 / R ^ 3 := by positivity
  have hcount := card_markedIdx_fibre_le_dec hG' hd zr hcovV hX₁V hoptV hZV (Hm := Hm)
  have hM : 0 ≤ c1 d L * ((L : ℝ) ^ (m₀ + m₁)) ^ d := by
    have hc1 : 0 ≤ c1 d L := by unfold c1; positivity
    positivity
  have hbound := fun Y' => norm_markedOutDec_le_of_term_bounds hN (fun _ => Set.univ)
    (fun b => polyDom S.G' (X₁V b) m₀ (jV b) (𝒦XV b)) hdom zr
    (decMarkCorrTerm S X₁V jV 𝒦XV m₀ a₁ ν cc F₁ Sol Zm ρ hp β Θ um Φ)
    hC₀ hM hκ1 (fun q _ => hterm q.1 q.2) hcount Y'
  have hB : ∀ Y', ‖markedOutDec m₀ (fun _ => Set.univ)
          (fun b => polyDom S.G' (X₁V b) m₀ (jV b) (𝒦XV b)) zr
          (decMarkCorrTerm S X₁V jV 𝒦XV m₀ a₁ ν cc F₁ Sol Zm ρ hp β Θ um Φ) Y'‖ ≤
        ‖β‖ * 4 * E * U ^ 2 / R ^ 3 * (c1 d L * ((L : ℝ) ^ (m₀ + m₁)) ^ d) *
          ((nFibre d L : ℝ) * Real.exp ((2 * κdec - 1) * cBr d L)) *
          Real.exp (-(2 * κdec - 1) * treeLenCovOne m₀ (k + 1) Y') := by
    intro Y'
    refine (hbound Y').trans (le_of_eq ?_)
    ring
  have hF₀ : 0 ≤ ‖β‖ * 4 * E * U ^ 2 / R ^ 3 * (c1 d L * ((L : ℝ) ^ (m₀ + m₁)) ^ d) *
      ((nFibre d L : ℝ) * Real.exp ((2 * κdec - 1) * cBr d L)) := by
    have : (0 : ℝ) ≤ (nFibre d L : ℝ) := by unfold nFibre; positivity
    positivity
  have hres : ∑ Y' ∈ bridgeFamily m₀ (fun _ => Set.univ)
      (fun b => polyDom S.G' (X₁V b) m₀ (jV b) (𝒦XV b)) zr,
      markedOutDec m₀ (fun _ => Set.univ)
        (fun b => polyDom S.G' (X₁V b) m₀ (jV b) (𝒦XV b)) zr
        (decMarkCorrTerm S X₁V jV 𝒦XV m₀ a₁ ν cc F₁ Sol Zm ρ hp β Θ um Φ) Y' =
      ∑ b, ∑ Y ∈ polyDom S.G' (X₁V b) m₀ (jV b) (𝒦XV b),
        deriv (decMarkCorrTerm S X₁V jV 𝒦XV m₀ a₁ ν cc F₁ Sol Zm ρ hp β Θ um Φ b Y) 0 := by
    refine sum_markedOutDec_eq_sum_of_vanishing _ _ zr _ fun b Y hY hnot => ?_
    have hmiss : psiThick Y ∩ fineBlock zr = ∅ := by
      by_contra hne
      obtain ⟨y, hy⟩ := Set.nonempty_iff_ne_empty.2 hne
      exact hnot (mem_markedIdx.2 ⟨hY, ⟨rootSite zr, trivial, rootSite_mem_fineBlock zr⟩, ⟨y, hy⟩⟩)
    have hY' : ∀ y ∈ Y, unitPt S.hG' y ∉ Zm := fun y hy hmem => by
      have hfb := hZm _ hmem y rfl
      have h2 : y ∈ psiThick Y ∩ fineBlock zr := ⟨Or.inl hy, hfb⟩
      rw [hmiss] at h2
      exact h2
    rw [deriv_decMarkCorrTerm, decMarkCorr_eq_zero_of_mask_miss S (hP b) hρ hρc hp hδ hΘ hum' hY'
      Φ]
    simp
  refine ⟨hB, fun {a''} ha => sum_norm_markedOutDec_le_of_bound hN hL (fun _ => Set.univ)
      (fun b => polyDom S.G' (X₁V b) m₀ (jV b) (𝒦XV b)) hdom zr _ hF₀ hB ha,
    fun Y' h => rootCube_mem_of_markedOutDec_ne_zero hN hL hdom zr _ h, ?_⟩
  rw [hres]
  exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun Y _ =>
    deriv_decMarkCorrTerm S F₁ Sol ρ hp β Θ um Φ b Y

end Count

end Balaban.Fluctuation
