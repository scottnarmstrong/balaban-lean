/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.DecMarkCorrSum
public import Balaban.Fluctuation.DecMarkCorrCount
public import Balaban.Fluctuation.HatLabelsTerms

/-!
# The rooted sum of the corrected decoupled marks

The rooted outputs `markedOutDec` of `MarkedScaledCountDec.lean` are sums of the derivatives at
`0` of a family of terms `T b Y : ℂ → ℂ`.  For the corrected marks the term of the block `b` and
the label `Y` is `decMarkCorrTerm … b Y`, the function `t ↦ t · (−β · decMarkCorr_b … Y … u Φ)`,
whose derivative at `0` is `−β · decMarkCorr_b … Y … u Φ` (`DecMarkCorrCount.lean`).  This file
sums the rooted outputs over the bridge family of a root `z` (mask `blockU z`) for a family of
pairs, one pair for every block.

* `StepSetting.noUnitPt_blockU_of_not_mem_markedIdx`: a label of a pair left out of `markedIdx`
  (trivial read sets) has no site whose unit point lies in the mask `blockU z` of the root.
* `StepSetting.sum_markedOutDec_eq_sum_decMarkCorr`: for every family of terms with
  `∂_t T_{b,Y}|_{t=0} = c · decMarkCorr_b … Y …`, the sum of the rooted outputs over the bridge
  family is the sum of `c · decMarkCorr` over the blocks and the labels (the eight clauses of the
  pairs are the only hypothesis on the pairs).
* `StepSetting.sum_markedOutDec_decMarkCorr_physical_of_total`: under the hypotheses of
  `sum_decMarkCorr_physical_of_total`, the sum of the rooted outputs of the terms
  `decMarkCorrTerm` is the masked derivative `DΦ₁(s ψ')[M_z ψ']` of the zero class, for real
  `s ∈ [0,1]` and a hat field of the physical ball.
* `StepSetting.ae_fderiv_mask_eq_sum_markedOutDec_decMarkCorr`: the same identity for almost
  every hat field of the fluctuation measure.

The pair of a block is an explicit argument of every statement, with its clauses.
-/

@[expose] public section

namespace Balaban.Fluctuation

open MeasureTheory Balaban Balaban.Localization Balaban.Multiscale Balaban.Background
  Balaban.SmallField Balaban.SmallField.Def6 Balaban.Analysis Balaban.Polymer Set Metric Matrix
  Filter Topology

namespace StepSetting

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}
  (S : StepSetting d L N₁ m₁ k N ϱ) (z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))))
variable {BG BG₂ κ eps δ₁ κdec cψ : ℝ} {m₀ : ℕ}
variable {jV : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) → ℕ}
  {𝒦XV : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) → Set (CTorus d L N₁ m₁ (k + 1))}
  {X₁V : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) → Finset (CTorus d L N₁ m₁ (k + 1))}

/-- **A label left out of `markedIdx` misses the mask of the root.**  With the trivial read sets,
a pair `(b, Y)`, `Y ∈ dom b`, is left out of `markedIdx … z` only if the nearest-neighbour
thickening of `Y` does not meet the fine block of the root `z`; the mask `blockU z` is supported
in that fine block (`blockU_supported`), so no site of `Y` has its unit point in the mask. -/
theorem noUnitPt_blockU_of_not_mem_markedIdx
    (dom : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) →
      Finset (Set (CTorus d L N₁ m₁ (k + 1))))
    {b : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1)))} {Y : Set (CTorus d L N₁ m₁ (k + 1))}
    (hY : Y ∈ dom b)
    (hnot : (b, Y) ∉ markedIdx (fun _ => (Set.univ : Set (CTorus d L N₁ m₁ (k + 1)))) dom z) :
    ∀ y ∈ Y, unitPt S.hG' y ∉ S.blockU z := by
  have hmiss : psiThick Y ∩ fineBlock z = ∅ := by
    by_contra hne
    obtain ⟨y, hy⟩ := Set.nonempty_iff_ne_empty.2 hne
    exact hnot (mem_markedIdx.2 ⟨hY, ⟨rootSite z, trivial, rootSite_mem_fineBlock z⟩, ⟨y, hy⟩⟩)
  intro y hy hmem
  have h2 : y ∈ psiThick Y ∩ fineBlock z := ⟨Or.inl hy, S.blockU_supported z hmem y rfl⟩
  rw [hmiss] at h2
  exact h2

/-- **Resummation of the rooted outputs of the corrected marks.**  Let `(F₁ b, Sol b)` be a pair
with the eight clauses for every block `b` at the step `S` (`cc = β_k^{-1/2}`, mask `blockU z`),
`Θ` a datum of the chart, `Φ` a block configuration and `um` a first mark with
`(‖um‖ + 0) · markedRad < δ₁`.  For every family of terms `T b Y : ℂ → ℂ` with
`∂_t T_{b,Y}|_{t=0} = c · decMarkCorr_b … Y … um Φ`, the sum over the bridge family of the root
`z` of the rooted outputs `markedOutDec … T Y′` is `∑_b ∑_{Y ∈ 𝒟_b} c · decMarkCorr_b … Y … um Φ`
(the pairs left out of `markedIdx` contribute zero by `decMarkCorr_eq_zero_of_mask_miss`). -/
theorem sum_markedOutDec_eq_sum_decMarkCorr
    (F₁ : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) →
      DecParams S.G' × RawData d L (N₁ * L ^ m₁) (k + 1) N →
        (S.G'.Ω 1 × Fin N → ℂ) × (S.G'.Ω 1 → ℂ))
    (Sol : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) →
      Dec2.DecParams (coverOf S.G') × Edat (stepG d L N₁ m₁ k ϱ) N →
        ((stepG d L N₁ m₁ k ϱ).Ω 1 × Fin N → ℂ) × ((stepG d L N₁ m₁ k ϱ).Ω 1 → ℂ))
    (hP : ∀ b, MarkedBlockExpansionDecPair N (stepG d L N₁ m₁ k ϱ) S.hG'
      ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) S.a₁ S.ν BG BG₂ κ eps δ₁ κdec cψ (S.blockU z) (X₁V b)
      m₀ (jV b) (𝒦XV b) b (F₁ b) (Sol b))
    {ρ : ℝ} (hρ : 0 < ρ) (hρc : ρ ≤ cψ) (hp : 0 < S.p₁) (hδ : 0 < δ₁)
    {Θ : RawData d L (N₁ * L ^ m₁) (k + 1) N}
    (hΘ : Θ ∈ XiCRaw S.G' (compWeight L S.a₁) S.ν (k + 1) 1 eps)
    {um : ℂ} (hum : (‖um‖ + ‖(0 : ℂ)‖) *
      markedRad d L N k S.a₁ κ cψ ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) < δ₁)
    (Φ : ∀ b, (S.blockSplit m₀ hp).Ωb b) (c : ℂ)
    (T : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) → Set (CTorus d L N₁ m₁ (k + 1)) → ℂ → ℂ)
    (hT : ∀ b Y, deriv (T b Y) 0 = c * decMarkCorr S (X₁V b) m₀ (jV b) (𝒦XV b) S.a₁ S.ν
      ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) (F₁ b) (Sol b)
      (blockEnergyFun S.G' (stepG d L N₁ m₁ k ϱ) (compWeight L S.a₁) S.ν k b) (S.blockU z)
      Y ρ hp Θ um Φ) :
    ∑ Y' ∈ bridgeFamily m₀ (fun _ => Set.univ)
        (fun b => polyDom S.G' (X₁V b) m₀ (jV b) (𝒦XV b)) z,
      markedOutDec m₀ (fun _ => Set.univ)
        (fun b => polyDom S.G' (X₁V b) m₀ (jV b) (𝒦XV b)) z T Y' =
      ∑ b, ∑ Y ∈ polyDom S.G' (X₁V b) m₀ (jV b) (𝒦XV b),
        c * decMarkCorr S (X₁V b) m₀ (jV b) (𝒦XV b) S.a₁ S.ν
          ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) (F₁ b) (Sol b)
          (blockEnergyFun S.G' (stepG d L N₁ m₁ k ϱ) (compWeight L S.a₁) S.ν k b) (S.blockU z)
          Y ρ hp Θ um Φ := by
  have hz : ∀ b, ∀ Y ∈ polyDom S.G' (X₁V b) m₀ (jV b) (𝒦XV b),
      (b, Y) ∉ markedIdx (fun _ => (Set.univ : Set (CTorus d L N₁ m₁ (k + 1))))
        (fun b => polyDom S.G' (X₁V b) m₀ (jV b) (𝒦XV b)) z → deriv (T b Y) 0 = 0 := by
    intro b Y hY hnot
    have hmiss := S.noUnitPt_blockU_of_not_mem_markedIdx z
      (fun b => polyDom S.G' (X₁V b) m₀ (jV b) (𝒦XV b)) (b := b) hY hnot
    rw [hT b Y, decMarkCorr_eq_zero_of_mask_miss S (hP b) hρ hρc hp hδ hΘ hum hmiss Φ, mul_zero]
  rw [sum_markedOutDec_eq_sum_of_vanishing _ _ z T hz]
  exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun Y _ => hT b Y

/-- **The rooted physical identity for the corrected marks** (zero class, real `s ∈ [0,1]`, a hat
field of the physical ball).  With the terms `decMarkCorrTerm`, `T_{b,Y}(t) = t · (−β ·
decMarkCorr_b … Y … s (restr x))`, of the pairs `(F₁ b, Sol b)`, under the hypotheses of
`sum_decMarkCorr_physical_of_total` (one pair with its clauses for every block;
`‖x‖ ≤ p₁ ≤ ρ ≤ cψ`; the hypotheses of `fderiv_mask_eq_neg_beta_taylor1_corrected_total`; the
identity `hE` of the marks of `V^{(k)} + ½⟨ψ', Δ^{(k)} ψ'⟩` and of the block-energy total on the
disc `‖u‖ < U`, `U > 1`):
`∑_{Y′ ∈ 𝒴_z} markedOutDec … T Y′ = DΦ₁(s ψ')[M_z ψ']`. -/
theorem sum_markedOutDec_decMarkCorr_physical_of_total
    (F₁ : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) →
      DecParams S.G' × RawData d L (N₁ * L ^ m₁) (k + 1) N →
        (S.G'.Ω 1 × Fin N → ℂ) × (S.G'.Ω 1 → ℂ))
    (Sol : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) →
      Dec2.DecParams (coverOf S.G') × Edat (stepG d L N₁ m₁ k ϱ) N →
        ((stepG d L N₁ m₁ k ϱ).Ω 1 × Fin N → ℂ) × ((stepG d L N₁ m₁ k ϱ).Ω 1 → ℂ))
    (hP : ∀ b, MarkedBlockExpansionDecPair N (stepG d L N₁ m₁ k ϱ) S.hG'
      ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) S.a₁ S.ν BG BG₂ κ eps δ₁ κdec cψ (S.blockU z) (X₁V b)
      m₀ (jV b) (𝒦XV b) b (F₁ b) (Sol b))
    {ρ : ℝ} (hρ : 0 < ρ) (hρc : ρ ≤ cψ) (hp : 0 < S.p₁) (hpρ : S.p₁ ≤ ρ) (hδ : 0 < δ₁)
    (hD : XiCData S.G' S.a S.ν (k + 1) 1 eps S.D') (x : S.E) (hx : ‖x‖ ≤ S.p₁)
    (ha₁ : 0 < S.a₁) (H : BgHyp d L (k + 1) ϱ S.a S.ν)
    (hD2 : InUnionDomainC S.G' (bgC0 d L N) (thm73C2 d L N) S.ν S.D')
    (hbase : InUnionDomainC (stepG d L N₁ m₁ k ϱ) (bgC0 d L N) (bgC2 d L N) S.ν
      (S.dataUC S.psi0C))
    (hAn : AnalyticAt ℂ (fun y : S.EC => S.VkC (S.psi0C + y)) 0)
    (hray0 : ∀ u t : ℂ, ∀ᶠ r : ℝ in 𝓝 0, InUnionDomainC (stepG d L N₁ m₁ k ϱ) (bgC0 d L N)
      (bgC1 d L N) S.ν
      (S.dataUC (S.psiAtV ((r : ℝ) : ℂ) (u • S.shiftUC x + t • S.maskUC z (S.shiftUC x)))))
    (hβ : 0 < S.β) {U : ℝ} (hU : 1 < U)
    (hE : ∀ u : ℂ, ‖u‖ < U →
      deriv (fun t : ℂ => S.VkC (S.psi0C + S.markedTangentC z u t x) +
        (1 / 2) * deltaForm (S.hG.precedes S.hG' (le_refl (k + 1))) (compWeight L S.a₁) S.ν
          (bgMultC S.G' (compWeight L S.a₁) S.ν (bgC0 d L N) S.D')
          (bgFieldC S.G' (compWeight L S.a₁) S.ν (bgC0 d L N) S.D')
          (liftC S.hG' (S.markedTangentC z u t x))) 0 =
      deriv (fun t : ℂ => ∑ b : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))),
        blockEnergyOne S.G' (stepG d L N₁ m₁ k ϱ) S.a₁ S.ν BG₂ κ eps k b
          (rawOf S.D', liftC S.hG' (S.markedTangentC z u t x))) 0)
    {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1)
    (hrad : (‖(s : ℂ)‖ + ‖(0 : ℂ)‖) *
      markedRad d L N k S.a₁ κ cψ ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) < δ₁)
    (hd : DifferentiableAt ℂ (S.Phi1C (zeroClass d L N₁ m₁ k N ϱ)) ((s : ℂ) • S.shiftUC x)) :
    ∑ Y' ∈ bridgeFamily m₀ (fun _ => Set.univ)
        (fun b => polyDom S.G' (X₁V b) m₀ (jV b) (𝒦XV b)) z,
      markedOutDec m₀ (fun _ => Set.univ)
        (fun b => polyDom S.G' (X₁V b) m₀ (jV b) (𝒦XV b)) z
        (decMarkCorrTerm S X₁V jV 𝒦XV m₀ S.a₁ S.ν ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) F₁ Sol
          (S.blockU z) ρ hp (S.β : ℂ) (rawOf S.D') (s : ℂ) ((S.blockSplit m₀ hp).restr x)) Y' =
      (fderiv ℂ (S.Phi1C (zeroClass d L N₁ m₁ k N ϱ)) ((s : ℂ) • S.shiftUC x))
        (S.maskUC z (S.shiftUC x)) := by
  rw [S.sum_markedOutDec_eq_sum_decMarkCorr z F₁ Sol hP hρ hρc hp hδ ⟨S.D', hD, rfl⟩ hrad
    ((S.blockSplit m₀ hp).restr x) (-(S.β : ℂ)) _
    (fun b Y => deriv_decMarkCorrTerm S F₁ Sol ρ hp (S.β : ℂ) (rawOf S.D') (s : ℂ) _ b Y)]
  exact S.sum_decMarkCorr_physical_of_total z F₁ Sol hP hρ hρc hp hpρ hδ hD x hx ha₁ H hD2 hbase
    hAn hray0 hβ hU hE hs hrad hd

/-- **The rooted physical identity for the corrected marks, almost everywhere** (zero class, real
`s ∈ [0,1]`).  Let the hypotheses of `sum_markedOutDec_decMarkCorr_physical_of_total` that depend
on the hat field (`hray0`, `hE`, `hd`) hold for every `x` with `‖x‖ ≤ p₁`.  Then for almost every
`x` of the fluctuation measure `ν_{p₁}` (which is carried by `‖x u‖ < p₁`, `ae_norm_nuFl`),
`DΦ₁(s ψ')[M_z ψ'] = ∑_{Y′ ∈ 𝒴_z} markedOutDec … T Y′`, with the terms `decMarkCorrTerm`,
`T_{b,Y}(t) = t · (−β · decMarkCorr_b … Y … s (restr x))`. -/
theorem ae_fderiv_mask_eq_sum_markedOutDec_decMarkCorr
    (F₁ : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) →
      DecParams S.G' × RawData d L (N₁ * L ^ m₁) (k + 1) N →
        (S.G'.Ω 1 × Fin N → ℂ) × (S.G'.Ω 1 → ℂ))
    (Sol : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) →
      Dec2.DecParams (coverOf S.G') × Edat (stepG d L N₁ m₁ k ϱ) N →
        ((stepG d L N₁ m₁ k ϱ).Ω 1 × Fin N → ℂ) × ((stepG d L N₁ m₁ k ϱ).Ω 1 → ℂ))
    (hP : ∀ b, MarkedBlockExpansionDecPair N (stepG d L N₁ m₁ k ϱ) S.hG'
      ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) S.a₁ S.ν BG BG₂ κ eps δ₁ κdec cψ (S.blockU z) (X₁V b)
      m₀ (jV b) (𝒦XV b) b (F₁ b) (Sol b))
    {ρ : ℝ} (hρ : 0 < ρ) (hρc : ρ ≤ cψ) (hp : 0 < S.p₁) (hpρ : S.p₁ ≤ ρ) (hδ : 0 < δ₁)
    (hD : XiCData S.G' S.a S.ν (k + 1) 1 eps S.D')
    (ha₁ : 0 < S.a₁) (H : BgHyp d L (k + 1) ϱ S.a S.ν)
    (hD2 : InUnionDomainC S.G' (bgC0 d L N) (thm73C2 d L N) S.ν S.D')
    (hbase : InUnionDomainC (stepG d L N₁ m₁ k ϱ) (bgC0 d L N) (bgC2 d L N) S.ν
      (S.dataUC S.psi0C))
    (hAn : AnalyticAt ℂ (fun y : S.EC => S.VkC (S.psi0C + y)) 0)
    (hray0 : ∀ x : S.E, ‖x‖ ≤ S.p₁ → ∀ u t : ℂ, ∀ᶠ r : ℝ in 𝓝 0,
      InUnionDomainC (stepG d L N₁ m₁ k ϱ) (bgC0 d L N) (bgC1 d L N) S.ν
      (S.dataUC (S.psiAtV ((r : ℝ) : ℂ) (u • S.shiftUC x + t • S.maskUC z (S.shiftUC x)))))
    (hβ : 0 < S.β) {U : ℝ} (hU : 1 < U)
    (hE : ∀ x : S.E, ‖x‖ ≤ S.p₁ → ∀ u : ℂ, ‖u‖ < U →
      deriv (fun t : ℂ => S.VkC (S.psi0C + S.markedTangentC z u t x) +
        (1 / 2) * deltaForm (S.hG.precedes S.hG' (le_refl (k + 1))) (compWeight L S.a₁) S.ν
          (bgMultC S.G' (compWeight L S.a₁) S.ν (bgC0 d L N) S.D')
          (bgFieldC S.G' (compWeight L S.a₁) S.ν (bgC0 d L N) S.D')
          (liftC S.hG' (S.markedTangentC z u t x))) 0 =
      deriv (fun t : ℂ => ∑ b : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))),
        blockEnergyOne S.G' (stepG d L N₁ m₁ k ϱ) S.a₁ S.ν BG₂ κ eps k b
          (rawOf S.D', liftC S.hG' (S.markedTangentC z u t x))) 0)
    {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1)
    (hrad : (‖(s : ℂ)‖ + ‖(0 : ℂ)‖) *
      markedRad d L N k S.a₁ κ cψ ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) < δ₁)
    (hd : ∀ x : S.E, ‖x‖ ≤ S.p₁ →
      DifferentiableAt ℂ (S.Phi1C (zeroClass d L N₁ m₁ k N ϱ)) ((s : ℂ) • S.shiftUC x)) :
    ∀ᵐ x ∂S.nuFl,
      (fderiv ℂ (S.Phi1C (zeroClass d L N₁ m₁ k N ϱ)) ((s : ℂ) • S.shiftUC x))
          (S.maskUC z (S.shiftUC x)) =
        ∑ Y' ∈ bridgeFamily m₀ (fun _ => Set.univ)
            (fun b => polyDom S.G' (X₁V b) m₀ (jV b) (𝒦XV b)) z,
          markedOutDec m₀ (fun _ => Set.univ)
            (fun b => polyDom S.G' (X₁V b) m₀ (jV b) (𝒦XV b)) z
            (decMarkCorrTerm S X₁V jV 𝒦XV m₀ S.a₁ S.ν ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) F₁
              Sol (S.blockU z) ρ hp (S.β : ℂ) (rawOf S.D') (s : ℂ)
              ((S.blockSplit m₀ hp).restr x)) Y' := by
  filter_upwards [S.ae_norm_nuFl hp] with x hx
  have hxn : ‖x‖ ≤ S.p₁ := (pi_norm_le_iff_of_nonneg hp.le).2 fun u => (hx u).le
  exact (S.sum_markedOutDec_decMarkCorr_physical_of_total z F₁ Sol hP hρ hρc hp hpρ hδ hD x hxn
    ha₁ H hD2 hbase hAn (hray0 x hxn) hβ hU (hE x hxn) hs hrad (hd x hxn)).symm

end StepSetting

end Balaban.Fluctuation
