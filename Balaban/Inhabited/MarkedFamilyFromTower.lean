/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.MarkRealSlice
public import Balaban.Inhabited.LevelStepSetting
public import Balaban.Fluctuation.MarkedCubicJoint

/-!
# The common marked family at the shared tower

At a scale of the shared tower `T` (`d = L = 3`, `N = 2`):

* `blockEnergyOne_eq_sum_of_energyBlock_sum` (T1 (i)): the block energy `blockEnergyOne` of
  `Fluctuation` equals `energyBlock … (bgMultC …) (flFieldOne …) ψ' z` at every raw datum
  `rawOf D`, `D` a chart datum (`blockEnergyOne_rawOf`), so a sum identity for `energyBlock` over
  the chart data is the same sum identity for `blockEnergyOne` over `XiCRaw`.
* `StepTower.hatConn_step`, `rowInHat_step` (T1 (ii)): `HatConn` and `RowInHat` of the step.
* `markedFamily_fromTower` (T2): one family `𝒴, Ev` for all old blocks with analyticity and block
  sum in the forms of `markReal_slice_of_count`, with locality and bound for the same `Ev`.
* `markReal_slice` (T3): the unconditional marked derivative identity on the whole slice.
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Fluctuation Balaban.Multiscale Balaban.Background Balaban.Localization
  Balaban.Localization.I5Inhabited Balaban.Inhabited.LevelStep Balaban.SmallField Set

section T1

variable {d L N₁ m₁ K N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱm : ℝ}

/-- **T1 (i).**  A sum identity for the block energy `energyBlock` of the chart data
(as in `vblock_expansion_scaled`) is the sum identity for `blockEnergyOne` on `XiCRaw`. -/
theorem blockEnergyOne_eq_sum_of_energyBlock_sum
    {Gp : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {Hm : GeneratingSet d L (N₁ * L ^ m₁) K ϱm}
    {a₁ ν BG₂ κ eps δ₁ : ℝ} {n : ℕ} (z : Torus d (N₁ * L ^ m₁ * L ^ (K - (n + 1))))
    {ι : Type*} (s : Finset ι)
    (Ev : ι → RawData d L (N₁ * L ^ m₁) K N × (CTorus d L N₁ m₁ K → Fin N → ℂ) → ℂ)
    (h : ∀ D : BgData Gp N, XiCData Gp (compWeight L a₁) ν K 1 eps D →
        ∀ ψ' ∈ FlBall Hm δ₁,
        energyBlock Gp Hm (compWeight L a₁) ν n (bgMultC Gp (compWeight L a₁) ν (bgC0 d L N) D)
          (flFieldOne Gp Hm BG₂ κ a₁ ν D ψ') ψ' z = ∑ Y ∈ s, Ev Y (rawOf D, ψ')) :
    ∀ Θ ∈ XiCRaw Gp (compWeight L a₁) ν K 1 eps, ∀ ψ' ∈ FlBall Hm δ₁,
      blockEnergyOne Gp Hm a₁ ν BG₂ κ eps n z (Θ, ψ') = ∑ Y ∈ s, Ev Y (Θ, ψ') := by
  intro Θ hΘ ψ' hψ
  obtain ⟨D, hD, rfl⟩ := hΘ
  rw [blockEnergyOne_rawOf hD n z ψ']
  exact h D hD ψ' hψ

end T1

namespace StepTower

variable {κmin : ℝ} (T : StepTower κmin) {k : ℕ} (hk : 1 ≤ k) {N₁ : ℕ} [NeZero N₁] {ν β p₁ : ℝ}

/-- **T1 (ii), `HatConn`**: at every scale of the tower (`hatConn_lvTop`). -/
theorem hatConn_step : HatConn (T.step k hk N₁ ν β p₁).G' := hatConn_lvTop

/-- **T1 (ii), `RowInHat`**: at every admissible scale of the tower (`rowInHat_lv`). -/
theorem rowInHat_step (hN : 5 < N₁) (hν0 : 0 ≤ ν) (hν : ν * 3 ^ (2 * (k + 1)) ≤ 1) :
    RowInHat (coverOf (T.step k hk N₁ ν β p₁).G') (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁))
      (compWeight 3 (T.step k hk N₁ ν β p₁).a₁) (T.step k hk N₁ ν β p₁).ν :=
  rowInHat_lv hk T.m₁_four hN hν0 hν

end StepTower

/-- **T2.  The common marked family at the shared tower.**  At an admissible scale
(`5 < N₁`, `0 ≤ ν`, `ν 3^{2(k+1)} ≤ 1`) with the per-scale package `hS`, there are the finite
domains `𝒴 zb` and terms `Ev zb Y` such that, for the base step of the scale, `han`
(analyticity on `Ξ^c × FlBall`) and `hsum` (block-energy sum, in terms of `blockEnergyOne`) hold in
the forms of `markReal_slice_of_count`, together with the locality and the bound
`E* e^{-2 κ_dec d(Y)}` of the same `Ev`.  Built from `markedCubic_joint_param` (that is,
`vblock_expansion_scaled`) with the covers of `hS.covers` (`m₀ = 1`, `j = k`). -/
theorem markedFamily_fromTower {κmin : ℝ} (T : StepTower κmin) {k : ℕ}
    {hk : 1 ≤ k} {N₁ : ℕ} [NeZero N₁] {ν β p₁ : ℝ}
    (hS : StepScaleData T k hk N₁ ν β p₁) (hN : 5 < N₁) (hν0 : 0 ≤ ν)
    (hν : ν * 3 ^ (2 * (k + 1)) ≤ 1) :
    ∃ (𝒴 : Torus 3 (N₁ * 3 ^ T.m₁ * 3 ^ (k + 1 - (k + 1))) →
      Finset (Set (CTorus 3 3 N₁ T.m₁ (k + 1))))
    (Ev : Torus 3 (N₁ * 3 ^ T.m₁ * 3 ^ (k + 1 - (k + 1))) → Set (CTorus 3 3 N₁ T.m₁ (k + 1)) →
      RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2 × (CTorus 3 3 N₁ T.m₁ (k + 1) → Fin 2 → ℂ) → ℂ),
    (∀ zb Y, AnalyticOnNhd ℂ (Ev zb Y)
      (XiCRaw (T.step k hk N₁ ν β p₁).G' (T.step k hk N₁ ν β p₁).a (T.step k hk N₁ ν β p₁).ν
        (k + 1) 1 T.t ×ˢ FlBall (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) T.t)) ∧
    (∀ zb, ∀ Θ ∈ XiCRaw (T.step k hk N₁ ν β p₁).G' (T.step k hk N₁ ν β p₁).a
        (T.step k hk N₁ ν β p₁).ν (k + 1) 1 T.t,
      ∀ ψ' ∈ FlBall (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) T.t,
      blockEnergyOne (T.step k hk N₁ ν β p₁).G' (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁))
        (T.step k hk N₁ ν β p₁).a₁ (T.step k hk N₁ ν β p₁).ν T.BG₂ T.κ T.t k zb (Θ, ψ') =
        ∑ Y ∈ 𝒴 zb, Ev zb Y (Θ, ψ')) ∧
    (∀ zb Y, ∀ u ∈ XiCRaw (T.step k hk N₁ ν β p₁).G' (compWeight 3 (T.step k hk N₁ ν β p₁).a₁)
        (T.step k hk N₁ ν β p₁).ν (k + 1) 1 T.t ×ˢ
        FlBall (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) T.t,
      ∀ u' ∈ XiCRaw (T.step k hk N₁ ν β p₁).G' (compWeight 3 (T.step k hk N₁ ν β p₁).a₁)
        (T.step k hk N₁ ν β p₁).ν (k + 1) 1 T.t ×ˢ
        FlBall (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) T.t,
      agreeOn (thickSet (T.step k hk N₁ ν β p₁).G' Y) u.1 u'.1 →
        (∀ y ∈ psiThick Y, u.2 y = u'.2 y) → Ev zb Y u = Ev zb Y u') ∧
    (∀ zb Y, ∀ u ∈ XiCRaw (T.step k hk N₁ ν β p₁).G' (compWeight 3 (T.step k hk N₁ ν β p₁).a₁)
        (T.step k hk N₁ ν β p₁).ν (k + 1) 1 T.t ×ˢ
        FlBall (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) T.t,
      ‖Ev zb Y u‖ ≤ energyBdScaled 3 3 2 (compWeight 3 (T.step k hk N₁ ν β p₁).a₁) k
        (cK2' 3 3 2 (famConst 3 3 T.BG₂ T.κ) * T.t) T.t (rho4 3 3 2 T.BG T.κ) *
        Real.exp (-2 * T.κdec * treeLenCov (T.step k hk N₁ ν β p₁).G' 1 Y)) := by
  classical
  have key : ∀ zb : Torus 3 (N₁ * 3 ^ T.m₁ * 3 ^ (k + 1 - (k + 1))), ∃ Ev : Set (CTorus 3 3 N₁ T.m₁ (k + 1)) →
      RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2 × (CTorus 3 3 N₁ T.m₁ (k + 1) → Fin 2 → ℂ) → ℂ,
      (∀ D : BgData (T.step k hk N₁ ν β p₁).G' 2,
        XiCData (T.step k hk N₁ ν β p₁).G' (compWeight 3 1) ν (k + 1) 1 T.t D →
        ∀ ψ' ∈ FlBall (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) T.t,
        energyBlock (T.step k hk N₁ ν β p₁).G' (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁))
          (compWeight 3 1) ν k
          (bgMultC (T.step k hk N₁ ν β p₁).G' (compWeight 3 1) ν (bgC0 3 3 2) D)
          (flFieldOne (T.step k hk N₁ ν β p₁).G' (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁))
            T.BG₂ T.κ 1 ν D ψ') ψ' zb =
        ∑ Y ∈ polymerDomains (fun i : ParIdx (T.step k hk N₁ ν β p₁).G'
          (↑(LocalCover.nbhdF 1 (LocalCover.blockSite k zb)) : Set (CTorus 3 3 N₁ T.m₁ (k + 1))) =>
          i.1.1) (T.step k hk N₁ ν β p₁).G' 1
          (X1 (T.step k hk N₁ ν β p₁).G' 1 k (LocalCover.fam 1 (LocalCover.blockSite k zb))),
          Ev Y (rawOf D, ψ')) ∧
      (∀ Y, ∀ u ∈ XiCRaw (T.step k hk N₁ ν β p₁).G' (compWeight 3 1) ν (k + 1) 1 T.t ×ˢ
          FlBall (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) T.t,
        ∀ u' ∈ XiCRaw (T.step k hk N₁ ν β p₁).G' (compWeight 3 1) ν (k + 1) 1 T.t ×ˢ
          FlBall (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) T.t,
        agreeOn (thickSet (T.step k hk N₁ ν β p₁).G' Y) u.1 u'.1 →
          (∀ y ∈ psiThick Y, u.2 y = u'.2 y) → Ev Y u = Ev Y u') ∧
      (∀ Y, ∀ u ∈ XiCRaw (T.step k hk N₁ ν β p₁).G' (compWeight 3 1) ν (k + 1) 1 T.t ×ˢ
          FlBall (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) T.t,
        ‖Ev Y u‖ ≤ energyBdScaled 3 3 2 (compWeight 3 1) k
          (cK2' 3 3 2 (famConst 3 3 T.BG₂ T.κ) * T.t) T.t (rho4 3 3 2 T.BG T.κ) *
          Real.exp (-2 * T.κdec * treeLenCov (T.step k hk N₁ ν β p₁).G' 1 Y)) ∧
      (∀ Y, AnalyticOnNhd ℂ (Ev Y)
        (XiCRaw (T.step k hk N₁ ν β p₁).G' (compWeight 3 1) ν (k + 1) 1 T.t ×ˢ
          FlBall (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) T.t)) := by
    intro zb
    obtain ⟨hz1, hz2, hz3, hz4, hz5, hz6, -⟩ := hS.covers.1 zb
    obtain ⟨Ev, h1, h2, h3, h4, -⟩ := (T.step k hk N₁ ν β p₁).markedCubic_joint_param zb
      (Hm := stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) hS.core hz1 hz2 (T.hatConn_step hk)
      (T.rowInHat_step hk hN hν0 hν) hz3 hz4 (κdec := T.κdec) (κ₀ := T.κ0) T.κ0_nonneg
      T.κdec_lower T.κ_lower T.κ_one T.κ_log (isLevel_lvLow hk) zb hz5 hz6
    exact ⟨Ev, h1, h2, h3, h4⟩
  choose Ev hEv using key
  refine ⟨fun zb => polymerDomains (fun i : ParIdx (T.step k hk N₁ ν β p₁).G'
    (↑(LocalCover.nbhdF 1 (LocalCover.blockSite k zb)) : Set (CTorus 3 3 N₁ T.m₁ (k + 1))) =>
    i.1.1) (T.step k hk N₁ ν β p₁).G' 1
    (X1 (T.step k hk N₁ ν β p₁).G' 1 k (LocalCover.fam 1 (LocalCover.blockSite k zb))), Ev,
    fun zb Y => (hEv zb).2.2.2 Y, fun zb => ?_, fun zb Y => (hEv zb).2.1 Y,
    fun zb Y => (hEv zb).2.2.1 Y⟩
  exact blockEnergyOne_eq_sum_of_energyBlock_sum zb _ (Ev zb) (hEv zb).1

/-- **T3.  MARK-REAL on the whole slice, unconditional.**  At an admissible scale of the shared
tower there is one family `𝒴, Ev` (that of `markedFamily_fromTower`) such that for every slice
datum `D`, every hat field `‖x‖ ≤ p₁`, every root `z` and every real `s ∈ [0,1]` the
one-dimensional marked identity and the ambient `fderiv` identity hold. -/
theorem markReal_slice {κmin : ℝ} (T : StepTower κmin) {k : ℕ}
    {hk : 1 ≤ k} {N₁ : ℕ} [NeZero N₁] {ν β p₁ : ℝ}
    (hS : StepScaleData T k hk N₁ ν β p₁) (hN : 5 < N₁) (hp₁ : 0 < p₁) (hν0 : 0 ≤ ν)
    (hν : ν * 3 ^ (2 * (k + 1)) ≤ 1) :
    ∃ (𝒴 : Torus 3 (N₁ * 3 ^ T.m₁ * 3 ^ (k + 1 - (k + 1))) →
      Finset (Set (CTorus 3 3 N₁ T.m₁ (k + 1))))
    (Ev : Torus 3 (N₁ * 3 ^ T.m₁ * 3 ^ (k + 1 - (k + 1))) → Set (CTorus 3 3 N₁ T.m₁ (k + 1)) →
      RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2 × (CTorus 3 3 N₁ T.m₁ (k + 1) → Fin 2 → ℂ) → ℂ),
    (∀ zb Y, AnalyticOnNhd ℂ (Ev zb Y)
      (XiCRaw (T.step k hk N₁ ν β p₁).G' (T.step k hk N₁ ν β p₁).a (T.step k hk N₁ ν β p₁).ν
        (k + 1) 1 T.t ×ˢ FlBall (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) T.t)) ∧
    (∀ zb, ∀ Θ ∈ XiCRaw (T.step k hk N₁ ν β p₁).G' (T.step k hk N₁ ν β p₁).a
        (T.step k hk N₁ ν β p₁).ν (k + 1) 1 T.t,
      ∀ ψ' ∈ FlBall (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) T.t,
      blockEnergyOne (T.step k hk N₁ ν β p₁).G' (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁))
        (T.step k hk N₁ ν β p₁).a₁ (T.step k hk N₁ ν β p₁).ν T.BG₂ T.κ T.t k zb (Θ, ψ') =
        ∑ Y ∈ 𝒴 zb, Ev zb Y (Θ, ψ')) ∧
    ∀ (D : BgData (T.step k hk N₁ ν β p₁).G' 2)
    (hDh : ∀ y i, D.h y i = ((T.step k hk N₁ ν β p₁).h₀ i : ℂ))
    (_hD : XiCData (T.step k hk N₁ ν β p₁).G' (compWeight 3 1) ν (k + 1) 1 T.t D)
    {x : ((T.step k hk N₁ ν β p₁).withDatum D hDh).E} (_hx : ‖x‖ ≤ p₁)
    (z : Torus 3 (N₁ * 3 ^ T.m₁ * 3 ^ (k + 1 - (k + 1)))) {s : ℝ} (_hs : s ∈ Icc (0 : ℝ) 1),
    HasDerivAt (fun t : ℂ => ((T.step k hk N₁ ν β p₁).withDatum D hDh).Phi1C
        (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁))
        (((T.step k hk N₁ ν β p₁).withDatum D hDh).markedTangentC z (s : ℂ) t x))
      (-(((T.step k hk N₁ ν β p₁).withDatum D hDh).β : ℂ) * ∑ zb, ∑ Y ∈ 𝒴 zb,
        deriv (markedBlockTerm (Ev zb Y) taylorWeight
          (liftC ((T.step k hk N₁ ν β p₁).withDatum D hDh).hG'
            ((s : ℂ) • ((T.step k hk N₁ ν β p₁).withDatum D hDh).shiftUC x))
          (liftC ((T.step k hk N₁ ν β p₁).withDatum D hDh).hG'
            (((T.step k hk N₁ ν β p₁).withDatum D hDh).maskUC z
              (((T.step k hk N₁ ν β p₁).withDatum D hDh).shiftUC x)))
          (rawOf ((T.step k hk N₁ ν β p₁).withDatum D hDh).D')) 0) 0 ∧
    (fderiv ℂ (((T.step k hk N₁ ν β p₁).withDatum D hDh).Phi1C
        (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)))
        ((s : ℂ) • ((T.step k hk N₁ ν β p₁).withDatum D hDh).shiftUC x))
      (((T.step k hk N₁ ν β p₁).withDatum D hDh).maskUC z
        (((T.step k hk N₁ ν β p₁).withDatum D hDh).shiftUC x)) =
      -(((T.step k hk N₁ ν β p₁).withDatum D hDh).β : ℂ) * ∑ zb, ∑ Y ∈ 𝒴 zb,
        deriv (markedBlockTerm (Ev zb Y) taylorWeight
          (liftC ((T.step k hk N₁ ν β p₁).withDatum D hDh).hG'
            ((s : ℂ) • ((T.step k hk N₁ ν β p₁).withDatum D hDh).shiftUC x))
          (liftC ((T.step k hk N₁ ν β p₁).withDatum D hDh).hG'
            (((T.step k hk N₁ ν β p₁).withDatum D hDh).maskUC z
              (((T.step k hk N₁ ν β p₁).withDatum D hDh).shiftUC x)))
          (rawOf ((T.step k hk N₁ ν β p₁).withDatum D hDh).D')) 0 := by
  obtain ⟨𝒴, Ev, han, hsum, -, -⟩ := markedFamily_fromTower T hS hN hν0 hν
  exact ⟨𝒴, Ev, han, hsum, fun D hDh hD x hx z s hs =>
    markReal_slice_of_count T hS hp₁ hν0 hν 𝒴 Ev han hsum D hDh hD hx z hs⟩

/-- **Instance of `markReal_slice`** at the scale of `StepTower.scale_instance` (`k = 1`,
`N₁ = 6`, `ν = 0`, `p₁ = 1`): the family and the identity at `x = 0`, `s = 1/2`, for the step's own
datum. -/
theorem markReal_slice_instance {κmin : ℝ} (T : StepTower κmin) :
    ∃ βray : ℝ, 2 ≤ βray ∧ Nonempty (StepScaleData T 1 le_rfl 6 0 βray 1) ∧
      ∃ (𝒴 : Torus 3 (6 * 3 ^ T.m₁ * 3 ^ (1 + 1 - (1 + 1))) →
          Finset (Set (CTorus 3 3 6 T.m₁ (1 + 1))))
        (Ev : Torus 3 (6 * 3 ^ T.m₁ * 3 ^ (1 + 1 - (1 + 1))) → Set (CTorus 3 3 6 T.m₁ (1 + 1)) →
          RawData 3 3 (6 * 3 ^ T.m₁) (1 + 1) 2 × (CTorus 3 3 6 T.m₁ (1 + 1) → Fin 2 → ℂ) → ℂ),
        (∀ zb Y, AnalyticOnNhd ℂ (Ev zb Y)
          (XiCRaw (T.step 1 le_rfl 6 0 βray 1).G' (T.step 1 le_rfl 6 0 βray 1).a
            (T.step 1 le_rfl 6 0 βray 1).ν (1 + 1) 1 T.t ×ˢ
            FlBall (stepG 3 3 6 T.m₁ 1 (rhoSep T.m₁)) T.t)) ∧
        ∀ z : Torus 3 (6 * 3 ^ T.m₁ * 3 ^ (1 + 1 - (1 + 1))),
        HasDerivAt (fun t : ℂ => (T.step 1 le_rfl 6 0 βray 1).Phi1C
            (zeroClass 3 3 6 T.m₁ 1 2 (rhoSep T.m₁))
            ((T.step 1 le_rfl 6 0 βray 1).markedTangentC z (((1 / 2 : ℝ) : ℂ)) t 0))
          (-((T.step 1 le_rfl 6 0 βray 1).β : ℂ) * ∑ zb, ∑ Y ∈ 𝒴 zb,
            deriv (markedBlockTerm (Ev zb Y) taylorWeight
              (liftC (T.step 1 le_rfl 6 0 βray 1).hG'
                (((1 / 2 : ℝ) : ℂ) • (T.step 1 le_rfl 6 0 βray 1).shiftUC 0))
              (liftC (T.step 1 le_rfl 6 0 βray 1).hG'
                ((T.step 1 le_rfl 6 0 βray 1).maskUC z
                  ((T.step 1 le_rfl 6 0 βray 1).shiftUC 0)))
              (rawOf (T.step 1 le_rfl 6 0 βray 1).D')) 0) 0 := by
  obtain ⟨βray, h2, ⟨hS⟩⟩ := T.scale_instance
  obtain ⟨𝒴, Ev, han, -, h⟩ := markReal_slice T hS (by norm_num) one_pos le_rfl (by norm_num)
  refine ⟨βray, h2, ⟨hS⟩, 𝒴, Ev, han, fun z => ?_⟩
  exact (h (T.step 1 le_rfl 6 0 βray 1).D' (T.step 1 le_rfl 6 0 βray 1).hh₀ hS.xi (x := 0)
    (by simp) z (s := 1 / 2) ⟨by norm_num, by norm_num⟩).1

end Balaban.Inhabited
