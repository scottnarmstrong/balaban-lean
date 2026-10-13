/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.DecMarkOfPair
public import Balaban.Fluctuation.DecMarkCorrectedTotal

/-!
# The sum of the corrected decoupled marks

For every block `b` let `(F₁ b, Sol b)` be one decoupling pair with the eight clauses of
`MarkedBlockExpansionDecPair`.  The corrected mark `decMarkCorr` of the pair of `b` and a label
`Y` is the first-order Taylor remainder, in the first mark, of the decoupled mark `decMarkG`.
This file sums these marks over the blocks and the labels of the chosen family.

* `sum_taylor1_remainder`, `analyticAt_deriv_mark_fst`: the first-order Taylor remainder commutes
  with finite sums; the derivative in the second mark at `0` of a jointly analytic function of
  two marks is analytic in the first mark.
* `analyticAt_decMarkG_mark`: the decoupled mark is analytic in the first mark on the slice
  `{u : (‖u‖ + 0) · markedRad < δ₁}` of the bidisc of the pair (clause 4).
* `sum_decMarkCorr_eq_taylor1`: the sum over the blocks and the labels of the corrected marks is
  the first-order Taylor remainder of the sum of the decoupled marks.
* `sum_decMarkG_eq_deriv_markedFunDec`, `differentiableAt_markedFunDec_mark`: for one block, the
  sum over the labels of the decoupled marks is the derivative at `0`, in the second mark, of the
  block functional along the masked decoupled tangent at the clamped hat field (clause 6); the
  block functional is differentiable there (clauses 1 and 4).
* `StepSetting.sum_decMarkG_eq_deriv_blockEnergyOne`: at the datum of the step and a hat field
  `x` whose clamp is `x` itself, the sum over the blocks and the labels of the decoupled marks is
  the derivative at `0` of the block-energy total along the marked tangent.
* `StepSetting.sum_decMarkCorr_eq_taylor1_of_mark`: the sum over the blocks and the labels of the
  corrected marks is the first-order Taylor remainder of every function that agrees, on a disc
  around `0`, with the mark of the block-energy total.
* `StepSetting.sum_decMarkCorr_physical_of_total`: if the mark of `V^{(k)} + ½⟨ψ', Δ^{(k)} ψ'⟩` is
  the mark of the block-energy total for every first mark of a disc of radius `U > 1`, then for
  real `s ∈ [0,1]` the sum over the blocks and the labels of `−β · decMarkCorr` at the first mark
  `s` is the masked derivative `DΦ₁(s ψ')[M_z ψ']` of the zero class.

The pair of a block enters every statement as an explicit argument together with its clauses;
no statement chooses a pair.
-/

@[expose] public section

namespace Balaban.Fluctuation

open MeasureTheory Balaban Balaban.Localization Balaban.Multiscale Balaban.Background
  Balaban.SmallField Balaban.SmallField.Def6 Balaban.Analysis Balaban.Polymer Set Metric Matrix
  Filter Topology

section Generic

/-- **The first-order Taylor remainder commutes with finite sums.**  For functions `g i` that are
differentiable at `0`, the sum of the remainders `g i u − g i 0 − u (g i)′(0)` is the remainder
of the sum. -/
theorem sum_taylor1_remainder {ι : Type*} (s : Finset ι) (g : ι → ℂ → ℂ)
    (hg : ∀ i ∈ s, DifferentiableAt ℂ (g i) 0) (u : ℂ) :
    ∑ i ∈ s, (g i u - g i 0 - u * deriv (g i) 0) =
      (∑ i ∈ s, g i u) - (∑ i ∈ s, g i 0) - u * deriv (fun v : ℂ => ∑ i ∈ s, g i v) 0 := by
  rw [deriv_fun_sum hg, Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_sub_distrib]

/-- **The first-order Taylor remainder depends on the function only near `0` and at the point.**
If `f = F` on a neighbourhood of `0` and `f u = F u`, then
`f u − f 0 − u f′(0) = F u − F 0 − u F′(0)`. -/
theorem taylor1_remainder_congr {f F : ℂ → ℂ} (h0 : f =ᶠ[𝓝 (0 : ℂ)] F) {u : ℂ}
    (hu : f u = F u) : f u - f 0 - u * deriv f 0 = F u - F 0 - u * deriv F 0 := by
  rw [hu, h0.eq_of_nhds, h0.deriv_eq]

/-- **The derivative in the second mark is analytic in the first mark.**  If `g (u, t)` is
analytic at every point of `W` and `(um, 0) ∈ W`, then `u ↦ ∂_t g (u, t)|_{t=0}` is analytic at
`um`. -/
theorem analyticAt_deriv_mark_fst {g : ℂ × ℂ → ℂ} {W : Set (ℂ × ℂ)}
    (hg : AnalyticOnNhd ℂ g W) {um : ℂ} (hum : (um, (0 : ℂ)) ∈ W) :
    AnalyticAt ℂ (fun v : ℂ => deriv (fun t : ℂ => g (v, t)) 0) um := by
  have hf : AnalyticOnNhd ℂ (fun x : ℂ × (ℂ × ℂ) => g x.2) ((Set.univ : Set ℂ) ×ˢ W) :=
    fun x hx => (hg x.2 hx.2).comp_of_eq analyticAt_snd rfl
  have h := analyticOnNhd_deriv_mark hf ((0 : ℂ), um) ⟨Set.mem_univ _, hum⟩
  exact h.comp_of_eq (f := fun v : ℂ => ((0 : ℂ), v)) (analyticAt_const.prod analyticAt_id) rfl

end Generic

section Pair

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ ϱm : ℝ}
  (S : StepSetting d L N₁ m₁ k N ϱ) {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}
variable {a₁ ν BG BG₂ κ eps δ₁ κdec cψ : ℝ} {X₁f : Finset (CTorus d L N₁ m₁ (k + 1))}
variable {m₀ j : ℕ} {𝒦X : Set (CTorus d L N₁ m₁ (k + 1))}
variable {cc : ℂ} {Zm : Finset (unitPts S.G')}
  {z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1)))}
variable {F₁ : DecParams S.G' × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      (S.G'.Ω 1 × Fin N → ℂ) × (S.G'.Ω 1 → ℂ)}
variable {Sol : Dec2.DecParams (coverOf S.G') × Edat Hm N → (Hm.Ω 1 × Fin N → ℂ) × (Hm.Ω 1 → ℂ)}

/-- **The decoupled mark is analytic in the first mark.**  By clause 4 of
`MarkedBlockExpansionDecPair` (analyticity of the localized term in the two marks on the bidisc
`(‖u‖ + ‖t‖) · markedRad < δ₁`), the mark `u ↦ decMarkG … u Φ` is analytic at every `um` with
`(‖um‖ + 0) · markedRad < δ₁`, for a datum of the chart and every block configuration. -/
theorem analyticAt_decMarkG_mark
    (hP : MarkedBlockExpansionDecPair N Hm S.hG' cc a₁ ν BG BG₂ κ eps δ₁ κdec cψ Zm X₁f m₀ j 𝒦X z
      F₁ Sol)
    {ρ : ℝ} (hρ : 0 < ρ) (hρc : ρ ≤ cψ) (hp : 0 < S.p₁)
    {Θ : RawData d L (N₁ * L ^ m₁) (k + 1) N}
    (hΘ : Θ ∈ XiCRaw S.G' (compWeight L a₁) ν (k + 1) 1 eps)
    {um : ℂ} (hum : (‖um‖ + ‖(0 : ℂ)‖) * markedRad d L N k a₁ κ cψ cc < δ₁)
    (Y : Set (CTorus d L N₁ m₁ (k + 1))) (Φ : ∀ b, (S.blockSplit m₀ hp).Ωb b) :
    AnalyticAt ℂ (fun v : ℂ => decMarkG S X₁f m₀ j 𝒦X a₁ ν cc F₁ Sol
      (blockEnergyFun S.G' Hm (compWeight L a₁) ν k z) Zm Y ρ hp Θ v Φ) um :=
  analyticAt_deriv_mark_fst
    (hP.2.2.2.1 Y (Θ, S.hatOf m₀ ρ hp Φ)
      ⟨hΘ, fun p => (S.hatOf_mem m₀ hρ hp Φ p).trans hρc⟩) hum

/-- **The sum over the labels of the decoupled marks of one block.**  By clause 6 of
`MarkedBlockExpansionDecPair`, for a datum `D` of the chart, a first mark `um` with
`(‖um‖ + 0) · markedRad < δ₁` and every block configuration `Φ` (the clamp of radius `ρ ≤ cψ`
keeps the hat field in the ball of the clause): the sum over the labels `Y` of
`decMarkG … Y … um Φ` is the derivative at `0`, in the second mark, of the block functional along
the masked decoupled tangent at the clamped hat field. -/
theorem sum_decMarkG_eq_deriv_markedFunDec
    (hP : MarkedBlockExpansionDecPair N Hm S.hG' cc a₁ ν BG BG₂ κ eps δ₁ κdec cψ Zm X₁f m₀ j 𝒦X z
      F₁ Sol)
    {ρ : ℝ} (hρ : 0 < ρ) (hρc : ρ ≤ cψ) (hp : 0 < S.p₁)
    {D : BgData S.G' N} (hD : XiCData S.G' (compWeight L a₁) ν (k + 1) 1 eps D)
    {um : ℂ} (hum : (‖um‖ + ‖(0 : ℂ)‖) * markedRad d L N k a₁ κ cψ cc < δ₁)
    (Φ : ∀ b, (S.blockSplit m₀ hp).Ωb b) :
    ∑ Y ∈ polyDom S.G' X₁f m₀ j 𝒦X, decMarkG S X₁f m₀ j 𝒦X a₁ ν cc F₁ Sol
        (blockEnergyFun S.G' Hm (compWeight L a₁) ν k z) Zm Y ρ hp (rawOf D) um Φ =
      deriv (fun t : ℂ => markedFunDec S.hG' cc a₁ ν BG₂ κ Zm um t
        (blockEnergyFun S.G' Hm (compWeight L a₁) ν k z) D (S.hatOf m₀ ρ hp Φ)) 0 :=
  (hP.2.2.2.2.2.1 um hum D hD (S.hatOf m₀ ρ hp Φ)
    fun p => (S.hatOf_mem m₀ hρ hp Φ p).trans hρc).symm

/-- **The block functional is differentiable in the second mark at `0`.**  By clauses 1 and 4 of
`MarkedBlockExpansionDecPair`: near `t = 0` the block functional along the masked decoupled
tangent is the finite sum of the localized terms, each analytic in the marks. -/
theorem differentiableAt_markedFunDec_mark
    (hP : MarkedBlockExpansionDecPair N Hm S.hG' cc a₁ ν BG BG₂ κ eps δ₁ κdec cψ Zm X₁f m₀ j 𝒦X z
      F₁ Sol)
    {D : BgData S.G' N} (hD : XiCData S.G' (compWeight L a₁) ν (k + 1) 1 eps D)
    {ψh : unitPts S.G' × Fin N → ℂ} (hψ : ∀ p, ‖ψh p‖ ≤ cψ)
    {um : ℂ} (hum : (‖um‖ + ‖(0 : ℂ)‖) * markedRad d L N k a₁ κ cψ cc < δ₁) :
    DifferentiableAt ℂ (fun t : ℂ => markedFunDec S.hG' cc a₁ ν BG₂ κ Zm um t
      (blockEnergyFun S.G' Hm (compWeight L a₁) ν k z) D ψh) 0 := by
  have hu : (rawOf D, ψh) ∈ XiCRaw S.G' (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
      {ψh : unitPts S.G' × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ} := ⟨⟨D, hD, rfl⟩, hψ⟩
  have hmem0 : (um, (0 : ℂ)) ∈ {w : ℂ × ℂ |
      (‖w.1‖ + ‖w.2‖) * markedRad d L N k a₁ κ cψ cc < δ₁} := hum
  have hnhds : {t : ℂ | (um, t) ∈ {w : ℂ × ℂ |
      (‖w.1‖ + ‖w.2‖) * markedRad d L N k a₁ κ cψ cc < δ₁}} ∈ 𝓝 (0 : ℂ) :=
    ((isOpen_markedRadiusSet (markedRad d L N k a₁ κ cψ cc) δ₁).preimage
      (continuous_const.prodMk continuous_id)).mem_nhds hmem0
  have hev : (fun t : ℂ => markedFunDec S.hG' cc a₁ ν BG₂ κ Zm um t
      (blockEnergyFun S.G' Hm (compWeight L a₁) ν k z) D ψh) =ᶠ[𝓝 (0 : ℂ)]
      fun t => ∑ Y ∈ polyDom S.G' X₁f m₀ j 𝒦X, evDec X₁f m₀ j 𝒦X a₁ ν S.hG' cc F₁ Sol
        (blockEnergyFun S.G' Hm (compWeight L a₁) ν k z) Zm um t Y (rawOf D, ψh) := by
    filter_upwards [hnhds] with t ht using hP.1 um t ht D hD ψh hψ
  refine (hev.differentiableAt_iff).2 (DifferentiableAt.fun_sum fun Y _ => ?_)
  exact differentiableAt_mark_slice (um := um)
    (g := fun w : ℂ × ℂ => evDec X₁f m₀ j 𝒦X a₁ ν S.hG' cc F₁ Sol
      (blockEnergyFun S.G' Hm (compWeight L a₁) ν k z) Zm w.1 w.2 Y (rawOf D, ψh))
    (hP.2.2.2.1 Y _ hu (um, 0) hmem0)

end Pair

section Family

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ ϱm : ℝ}
  (S : StepSetting d L N₁ m₁ k N ϱ) {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}
variable {a₁ ν BG BG₂ κ eps δ₁ κdec cψ : ℝ} {m₀ : ℕ} {cc : ℂ} {Zm : Finset (unitPts S.G')}
variable {jV : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) → ℕ}
  {𝒦XV : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) → Set (CTorus d L N₁ m₁ (k + 1))}
  {X₁V : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) → Finset (CTorus d L N₁ m₁ (k + 1))}

/-- **The sum of the corrected marks is the first-order Taylor remainder of the sum of the
decoupled marks.**  Let `(F₁ b, Sol b)` be a pair with the eight clauses for every block `b`.
For a datum `Θ` of the chart, every block configuration `Φ` and every first mark `um : ℂ`, with
`G(v) = ∑_b ∑_{Y ∈ 𝒟_b} decMarkG_b … Y … v Φ`:
`∑_b ∑_{Y ∈ 𝒟_b} decMarkCorr_b … Y … um Φ = G(um) − G(0) − um · G′(0)`.
(Each `decMarkG_b … Y … · Φ` is differentiable at `0` by `analyticAt_decMarkG_mark`, and `0` lies
in the slice of the bidisc because `0 < δ₁`.) -/
theorem sum_decMarkCorr_eq_taylor1
    (F₁ : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) →
      DecParams S.G' × RawData d L (N₁ * L ^ m₁) (k + 1) N →
        (S.G'.Ω 1 × Fin N → ℂ) × (S.G'.Ω 1 → ℂ))
    (Sol : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) →
      Dec2.DecParams (coverOf S.G') × Edat Hm N → (Hm.Ω 1 × Fin N → ℂ) × (Hm.Ω 1 → ℂ))
    (hP : ∀ b, MarkedBlockExpansionDecPair N Hm S.hG' cc a₁ ν BG BG₂ κ eps δ₁ κdec cψ Zm (X₁V b)
      m₀ (jV b) (𝒦XV b) b (F₁ b) (Sol b))
    {ρ : ℝ} (hρ : 0 < ρ) (hρc : ρ ≤ cψ) (hp : 0 < S.p₁) (hδ : 0 < δ₁)
    {Θ : RawData d L (N₁ * L ^ m₁) (k + 1) N}
    (hΘ : Θ ∈ XiCRaw S.G' (compWeight L a₁) ν (k + 1) 1 eps) (um : ℂ)
    (Φ : ∀ b, (S.blockSplit m₀ hp).Ωb b) :
    ∑ b, ∑ Y ∈ polyDom S.G' (X₁V b) m₀ (jV b) (𝒦XV b),
        decMarkCorr S (X₁V b) m₀ (jV b) (𝒦XV b) a₁ ν cc (F₁ b) (Sol b)
          (blockEnergyFun S.G' Hm (compWeight L a₁) ν k b) Zm Y ρ hp Θ um Φ =
      (∑ b, ∑ Y ∈ polyDom S.G' (X₁V b) m₀ (jV b) (𝒦XV b),
        decMarkG S (X₁V b) m₀ (jV b) (𝒦XV b) a₁ ν cc (F₁ b) (Sol b)
          (blockEnergyFun S.G' Hm (compWeight L a₁) ν k b) Zm Y ρ hp Θ um Φ) -
      (∑ b, ∑ Y ∈ polyDom S.G' (X₁V b) m₀ (jV b) (𝒦XV b),
        decMarkG S (X₁V b) m₀ (jV b) (𝒦XV b) a₁ ν cc (F₁ b) (Sol b)
          (blockEnergyFun S.G' Hm (compWeight L a₁) ν k b) Zm Y ρ hp Θ 0 Φ) -
      um * deriv (fun v : ℂ => ∑ b, ∑ Y ∈ polyDom S.G' (X₁V b) m₀ (jV b) (𝒦XV b),
        decMarkG S (X₁V b) m₀ (jV b) (𝒦XV b) a₁ ν cc (F₁ b) (Sol b)
          (blockEnergyFun S.G' Hm (compWeight L a₁) ν k b) Zm Y ρ hp Θ v Φ) 0 := by
  have h0 : (‖(0 : ℂ)‖ + ‖(0 : ℂ)‖) * markedRad d L N k a₁ κ cψ cc < δ₁ := by simpa using hδ
  have hd : ∀ b Y, DifferentiableAt ℂ (fun v : ℂ =>
      decMarkG S (X₁V b) m₀ (jV b) (𝒦XV b) a₁ ν cc (F₁ b) (Sol b)
        (blockEnergyFun S.G' Hm (compWeight L a₁) ν k b) Zm Y ρ hp Θ v Φ) 0 := fun b Y =>
    (analyticAt_decMarkG_mark S (hP b) hρ hρc hp hΘ h0 Y Φ).differentiableAt
  have hin : ∀ b, ∑ Y ∈ polyDom S.G' (X₁V b) m₀ (jV b) (𝒦XV b),
      decMarkCorr S (X₁V b) m₀ (jV b) (𝒦XV b) a₁ ν cc (F₁ b) (Sol b)
        (blockEnergyFun S.G' Hm (compWeight L a₁) ν k b) Zm Y ρ hp Θ um Φ =
      (∑ Y ∈ polyDom S.G' (X₁V b) m₀ (jV b) (𝒦XV b),
        decMarkG S (X₁V b) m₀ (jV b) (𝒦XV b) a₁ ν cc (F₁ b) (Sol b)
          (blockEnergyFun S.G' Hm (compWeight L a₁) ν k b) Zm Y ρ hp Θ um Φ) -
      (∑ Y ∈ polyDom S.G' (X₁V b) m₀ (jV b) (𝒦XV b),
        decMarkG S (X₁V b) m₀ (jV b) (𝒦XV b) a₁ ν cc (F₁ b) (Sol b)
          (blockEnergyFun S.G' Hm (compWeight L a₁) ν k b) Zm Y ρ hp Θ 0 Φ) -
      um * deriv (fun v : ℂ => ∑ Y ∈ polyDom S.G' (X₁V b) m₀ (jV b) (𝒦XV b),
        decMarkG S (X₁V b) m₀ (jV b) (𝒦XV b) a₁ ν cc (F₁ b) (Sol b)
          (blockEnergyFun S.G' Hm (compWeight L a₁) ν k b) Zm Y ρ hp Θ v Φ) 0 := fun b =>
    sum_taylor1_remainder _ (fun Y (v : ℂ) =>
      decMarkG S (X₁V b) m₀ (jV b) (𝒦XV b) a₁ ν cc (F₁ b) (Sol b)
        (blockEnergyFun S.G' Hm (compWeight L a₁) ν k b) Zm Y ρ hp Θ v Φ) (fun Y _ => hd b Y) um
  rw [Finset.sum_congr rfl fun b _ => hin b]
  exact sum_taylor1_remainder Finset.univ
    (fun b (v : ℂ) => ∑ Y ∈ polyDom S.G' (X₁V b) m₀ (jV b) (𝒦XV b),
      decMarkG S (X₁V b) m₀ (jV b) (𝒦XV b) a₁ ν cc (F₁ b) (Sol b)
        (blockEnergyFun S.G' Hm (compWeight L a₁) ν k b) Zm Y ρ hp Θ v Φ)
    (fun b _ => DifferentiableAt.fun_sum fun Y _ => hd b Y) um

end Family

namespace StepSetting

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}
  (S : StepSetting d L N₁ m₁ k N ϱ) (z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))))
variable {BG BG₂ κ eps δ₁ κdec cψ : ℝ} {m₀ : ℕ}
variable {jV : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) → ℕ}
  {𝒦XV : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) → Set (CTorus d L N₁ m₁ (k + 1))}
  {X₁V : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) → Finset (CTorus d L N₁ m₁ (k + 1))}

/-- **The sum of the decoupled marks is the mark of the block-energy total.**  Let
`(F₁ b, Sol b)` be a pair with the eight clauses for every block `b`, at the step `S`
(`cc = β_k^{-1/2}`, mask `blockU z`).  Let `x` be a hat field with `‖x u‖ ≤ ρ` for every unit
point `u`, so that the clamp of radius `ρ` of the block configuration of `x` is `x` itself
(`hatOf_restr`; this holds when `‖x‖ ≤ p₁ ≤ ρ`).  For every first mark `um` in the slice
`(‖um‖ + 0) · markedRad < δ₁` of the bidisc of clause 1,
`∑_b ∑_{Y ∈ 𝒟_b} decMarkG_b … Y … um (restr x) = ∂_t [∑_b E_b(rawOf θ, lift v_{um,t})]_{t=0}`,
`v_{u,t} = u ψ' + t M_z ψ'` the marked tangent (clause 6 and `markedFunDec_eq_blockEnergyOne`). -/
theorem sum_decMarkG_eq_deriv_blockEnergyOne
    (F₁ : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) →
      DecParams S.G' × RawData d L (N₁ * L ^ m₁) (k + 1) N →
        (S.G'.Ω 1 × Fin N → ℂ) × (S.G'.Ω 1 → ℂ))
    (Sol : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) →
      Dec2.DecParams (coverOf S.G') × Edat (stepG d L N₁ m₁ k ϱ) N →
        ((stepG d L N₁ m₁ k ϱ).Ω 1 × Fin N → ℂ) × ((stepG d L N₁ m₁ k ϱ).Ω 1 → ℂ))
    (hP : ∀ b, MarkedBlockExpansionDecPair N (stepG d L N₁ m₁ k ϱ) S.hG'
      ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) S.a₁ S.ν BG BG₂ κ eps δ₁ κdec cψ (S.blockU z) (X₁V b)
      m₀ (jV b) (𝒦XV b) b (F₁ b) (Sol b))
    {ρ : ℝ} (hρ : 0 < ρ) (hρc : ρ ≤ cψ) (hp : 0 < S.p₁)
    (hD : XiCData S.G' S.a S.ν (k + 1) 1 eps S.D') (x : S.E) (hx : ∀ u, ‖x u‖ ≤ ρ)
    {um : ℂ} (hum : (‖um‖ + ‖(0 : ℂ)‖) *
      markedRad d L N k S.a₁ κ cψ ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) < δ₁) :
    ∑ b, ∑ Y ∈ polyDom S.G' (X₁V b) m₀ (jV b) (𝒦XV b),
        decMarkG S (X₁V b) m₀ (jV b) (𝒦XV b) S.a₁ S.ν ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)
          (F₁ b) (Sol b)
          (blockEnergyFun S.G' (stepG d L N₁ m₁ k ϱ) (compWeight L S.a₁) S.ν k b) (S.blockU z)
          Y ρ hp (rawOf S.D') um ((S.blockSplit m₀ hp).restr x) =
      deriv (fun t : ℂ => ∑ b : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))),
        blockEnergyOne S.G' (stepG d L N₁ m₁ k ϱ) S.a₁ S.ν BG₂ κ eps k b
          (rawOf S.D', liftC S.hG' (S.markedTangentC z um t x))) 0 := by
  have hhat : S.hatOf m₀ ρ hp ((S.blockSplit m₀ hp).restr x) = yhat x :=
    S.hatOf_restr m₀ hρ hp x hx
  have hψ : ∀ p, ‖yhat x p‖ ≤ cψ := fun p => by
    rw [← hhat]; exact (S.hatOf_mem m₀ hρ hp _ p).trans hρc
  have hfun : (fun t : ℂ => ∑ b : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))),
      blockEnergyOne S.G' (stepG d L N₁ m₁ k ϱ) S.a₁ S.ν BG₂ κ eps k b
        (rawOf S.D', liftC S.hG' (S.markedTangentC z um t x))) =
      fun t : ℂ => ∑ b : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))),
        markedFunDec S.hG' ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) S.a₁ S.ν BG₂ κ (S.blockU z) um t
          (blockEnergyFun S.G' (stepG d L N₁ m₁ k ϱ) (compWeight L S.a₁) S.ν k b) S.D'
          (yhat x) :=
    funext fun t => Finset.sum_congr rfl fun b _ =>
      (S.markedFunDec_eq_blockEnergyOne z hD um t x b).symm
  rw [hfun, deriv_fun_sum fun b _ => differentiableAt_markedFunDec_mark S (hP b) hD hψ hum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [sum_decMarkG_eq_deriv_markedFunDec S (hP b) hρ hρc hp hD hum, hhat]

/-- **The sum of the corrected marks is the first-order Taylor remainder of the mark of the
block-energy total.**  Let `(F₁ b, Sol b)` be a pair with the eight clauses for every block `b`
at the step `S` (`cc = β_k^{-1/2}`, mask `blockU z`), and `x` a hat field with `‖x u‖ ≤ ρ ≤ cψ`
for every unit point `u`.  Let `f : ℂ → ℂ` agree on a disc `‖u‖ < U`, `U > 0`, with the mark of
the block-energy total: `f u = ∂_t [∑_b E_b(rawOf θ, lift v_{u,t})]_{t=0}`,
`v_{u,t} = u ψ' + t M_z ψ'`.  Then for every first mark `um` with `‖um‖ < U` in the slice
`(‖um‖ + 0) · markedRad < δ₁`,
`∑_b ∑_{Y ∈ 𝒟_b} decMarkCorr_b … Y … um (restr x) = f um − f 0 − um · f′(0)`. -/
theorem sum_decMarkCorr_eq_taylor1_of_mark
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
    (hD : XiCData S.G' S.a S.ν (k + 1) 1 eps S.D') (x : S.E) (hx : ∀ u, ‖x u‖ ≤ ρ)
    {U : ℝ} (hU : 0 < U) (f : ℂ → ℂ)
    (hE : ∀ u : ℂ, ‖u‖ < U →
      f u = deriv (fun t : ℂ => ∑ b : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))),
        blockEnergyOne S.G' (stepG d L N₁ m₁ k ϱ) S.a₁ S.ν BG₂ κ eps k b
          (rawOf S.D', liftC S.hG' (S.markedTangentC z u t x))) 0)
    {um : ℂ} (hum : (‖um‖ + ‖(0 : ℂ)‖) *
      markedRad d L N k S.a₁ κ cψ ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) < δ₁)
    (humU : ‖um‖ < U) :
    ∑ b, ∑ Y ∈ polyDom S.G' (X₁V b) m₀ (jV b) (𝒦XV b),
        decMarkCorr S (X₁V b) m₀ (jV b) (𝒦XV b) S.a₁ S.ν
          ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) (F₁ b) (Sol b)
          (blockEnergyFun S.G' (stepG d L N₁ m₁ k ϱ) (compWeight L S.a₁) S.ν k b) (S.blockU z)
          Y ρ hp (rawOf S.D') um ((S.blockSplit m₀ hp).restr x) =
      f um - f 0 - um * deriv f 0 := by
  have hΘ : rawOf S.D' ∈ XiCRaw S.G' (compWeight L S.a₁) S.ν (k + 1) 1 eps := ⟨S.D', hD, rfl⟩
  have h0 : (‖(0 : ℂ)‖ + ‖(0 : ℂ)‖) *
      markedRad d L N k S.a₁ κ cψ ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) < δ₁ := by simpa using hδ
  have hopen : IsOpen {v : ℂ | (‖v‖ + ‖(0 : ℂ)‖) *
      markedRad d L N k S.a₁ κ cψ ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) < δ₁} :=
    isOpen_lt (by fun_prop) continuous_const
  -- the sum of the decoupled marks is `f` on the slice inside the disc
  have hFf : ∀ v : ℂ, (‖v‖ + ‖(0 : ℂ)‖) *
      markedRad d L N k S.a₁ κ cψ ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) < δ₁ → ‖v‖ < U →
      (∑ b, ∑ Y ∈ polyDom S.G' (X₁V b) m₀ (jV b) (𝒦XV b),
        decMarkG S (X₁V b) m₀ (jV b) (𝒦XV b) S.a₁ S.ν ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)
          (F₁ b) (Sol b)
          (blockEnergyFun S.G' (stepG d L N₁ m₁ k ϱ) (compWeight L S.a₁) S.ν k b) (S.blockU z)
          Y ρ hp (rawOf S.D') v ((S.blockSplit m₀ hp).restr x)) = f v := fun v hv hvU => by
    rw [S.sum_decMarkG_eq_deriv_blockEnergyOne z F₁ Sol hP hρ hρc hp hD x hx hv]
    exact (hE v hvU).symm
  have hev : (fun v : ℂ => ∑ b, ∑ Y ∈ polyDom S.G' (X₁V b) m₀ (jV b) (𝒦XV b),
        decMarkG S (X₁V b) m₀ (jV b) (𝒦XV b) S.a₁ S.ν ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)
          (F₁ b) (Sol b)
          (blockEnergyFun S.G' (stepG d L N₁ m₁ k ϱ) (compWeight L S.a₁) S.ν k b) (S.blockU z)
          Y ρ hp (rawOf S.D') v ((S.blockSplit m₀ hp).restr x)) =ᶠ[𝓝 (0 : ℂ)] f := by
    filter_upwards [hopen.mem_nhds h0, Metric.ball_mem_nhds (0 : ℂ) hU] with v hv hvU
    exact hFf v hv (by simpa using hvU)
  rw [sum_decMarkCorr_eq_taylor1 S F₁ Sol hP hρ hρc hp hδ hΘ um ((S.blockSplit m₀ hp).restr x)]
  exact taylor1_remainder_congr hev (hFf um hum humU)

/-- **The physical sum identity for the corrected marks of a family of pairs** (zero class,
real `s ∈ [0,1]`).  Let `(F₁ b, Sol b)` be a pair with the eight clauses for every block `b` at
the step `S` (`cc = β_k^{-1/2}`, mask `blockU z`), and let `x` be a hat field of the physical
ball, `‖x‖ ≤ p₁ ≤ ρ ≤ cψ`.  Assume the hypotheses of
`fderiv_mask_eq_neg_beta_taylor1_corrected_total` (`ha₁`, `H`, `hD2`, `hbase`, `hAn`, `hray0`,
`hβ`, `hd`), and the identity `hE`: for every first mark `u` with `‖u‖ < U`, `U > 1`, the mark
of `V^{(k)} + ½⟨ψ', Δ^{(k)} ψ'⟩` along the marked tangent `v_{u,t} = u ψ' + t M_z ψ'` is the mark
of the block-energy total,
`∂_t [V^{(k)}(ψ^{(k)} + v_{u,t}) + ½ δ(v_{u,t})]_{t=0} = ∂_t [∑_b E_b(rawOf θ, lift v_{u,t})]_{t=0}`
(`δ` the quadratic form `⟨ψ', Δ^{(k)} ψ'⟩` at the lift).
Then for `s ∈ [0,1]` with `(‖s‖ + 0) · markedRad < δ₁`,
`∑_b ∑_{Y ∈ 𝒟_b} −β · decMarkCorr_b … Y … s (restr x) = DΦ₁(s ψ')[M_z ψ']`. -/
theorem sum_decMarkCorr_physical_of_total
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
    ∑ b, ∑ Y ∈ polyDom S.G' (X₁V b) m₀ (jV b) (𝒦XV b),
        -(S.β : ℂ) * decMarkCorr S (X₁V b) m₀ (jV b) (𝒦XV b) S.a₁ S.ν
          ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) (F₁ b) (Sol b)
          (blockEnergyFun S.G' (stepG d L N₁ m₁ k ϱ) (compWeight L S.a₁) S.ν k b) (S.blockU z)
          Y ρ hp (rawOf S.D') (s : ℂ) ((S.blockSplit m₀ hp).restr x) =
      (fderiv ℂ (S.Phi1C (zeroClass d L N₁ m₁ k N ϱ)) ((s : ℂ) • S.shiftUC x))
        (S.maskUC z (S.shiftUC x)) := by
  have hxρ : ∀ u, ‖x u‖ ≤ ρ := fun u => (norm_le_pi_norm x u).trans (hx.trans hpρ)
  have hsU : ‖(s : ℂ)‖ < U := by
    rw [Complex.norm_real, Real.norm_of_nonneg hs.1]; linarith [hs.2]
  have hT := S.sum_decMarkCorr_eq_taylor1_of_mark z F₁ Sol hP hρ hρc hp hδ hD x hxρ
    (zero_lt_one.trans hU) _ hE hrad hsU
  rw [S.fderiv_mask_eq_neg_beta_taylor1_corrected_total z ha₁ H hD2 hbase x hAn hray0 _
    (fun _ => rfl) hβ s hd]
  refine Eq.trans ?_ (congrArg (fun w : ℂ => -(S.β : ℂ) * w) hT)
  simp only [Finset.mul_sum]

end StepSetting

end Balaban.Fluctuation
