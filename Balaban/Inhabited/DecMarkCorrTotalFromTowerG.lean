/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.OffFibreBlockEnergyCore
public import Balaban.Inhabited.MarkRealDiscSliceG
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The corrected mark of the total at the general tower, and its tie to the block-energy total

* `StepSetting.sum_blockEnergyOne_eq_VkC_add_delta`: for complex mark variables `(u, t)` with
  `lift(u ψ' + t M_z ψ')` in the fluctuation ball, the sum of the block energies at the lifted
  marked tangent is `V^{(k)}(ψ^{(k)} + v_{u,t}) + ½ ⟨ψ', Δ^{(k)} ψ'⟩(v_{u,t})`.
* `fderiv_mask_corrected_total_fromTowerG`: the identity
  `DΦ₁(s ψ')[M_z ψ'] = -β (f s - f 0 - s f'(0))` at a scale of the general tower, every hypothesis
  of `fderiv_mask_eq_neg_beta_taylor1_corrected_total` discharged.
* `sum_blockEnergy_eq_VkC_add_delta_fromTowerG`: the identity of the first bullet at the tower, on
  the whole polydisc `‖u‖ < 17/16`, `‖t‖ < 1/16`.
* `mark_eq_deriv_blockEnergy_fromTowerG`: `f(u)` is the derivative at `t = 0` of the block-energy
  total, for every complex `u` with `‖u‖ < 17/16`.

The steps are stated over any `ϱ = rhoSepG d L T.m₁` (`hϱ`), with the base step `S₀` given by
`hS₀ : S₀ = hatStepKG … ϱ …`.
-/

@[expose] public section



namespace Balaban.Inhabited

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation
  Balaban.Localization Balaban.Localization.LevelPair Balaban.Localization.I5Inhabited
  Balaban.Polymer Balaban.SmallField.Def6 Balaban.Inhabited.LevelStep Matrix Metric Set Filter
  Topology

/-- **The corrected mark of the total at every scale of the tower.**  The hypotheses of
`StepSetting.fderiv_mask_eq_neg_beta_taylor1_corrected_total` (`hAn`, `ha₁`, `H`, `hD2`, `hbase`,
`hray0` for every mixed direction `(u, t)`, `hd`, `hβ`) hold at the step
`S₀.withDatum D' hDh` of a scale of a shared tower: `f` is the mark
`u ↦ ∂ₜ [V + ½δ](v_{u,t})|ₜ₌₀` and `DΦ₁(s ψ')[M_z ψ'] = -β (f s - f 0 - s f'(0))` for real
`s ∈ [0,1]`, `‖x‖ ≤ p₁`. -/
theorem fderiv_mask_corrected_total_fromTowerG {d L N : ℕ} [NeZero L] {κmin : ℝ} (T : StepTowerG d L N κmin) {k : ℕ}
    {hk : 1 ≤ k} {N₁ : ℕ} [NeZero N₁] {ν β p₁ : ℝ} (D : StepScaleDataG T k hk N₁ ν β p₁)
    (hβ : 0 < β) (hp : 0 < p₁) {ϱ : ℝ}
    (hϱ : ϱ = rhoSepG d L T.m₁) {S₀ : StepSetting d L N₁ T.m₁ k N ϱ}
    (hS₀ : S₀ = hatStepKG T.hN k T.m₁ ϱ hk ν β p₁ T.δ)
    (D' : BgData S₀.G' N)
    (hDh : ∀ y i, D'.h y i = (S₀.h₀ i : ℂ))
    (hD : XiCData S₀.G' (compWeight L 1) ν (k + 1) 1 T.t D')
    {S : StepSetting d L N₁ T.m₁ k N ϱ}
    (hS : S = S₀.withDatum D' hDh)
    (x : S.E) (hx : ‖x‖ ≤ p₁) (z : Torus d (N₁ * L ^ T.m₁ * L ^ (k + 1 - (k + 1)))) {s : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) (f : ℂ → ℂ)
    (hf : ∀ u : ℂ, f u = deriv (fun t : ℂ => S.VkC (S.psi0C + S.markedTangentC z u t x) +
      (1 / 2) * deltaForm (S.hG.precedes S.hG' (le_refl (k + 1))) (compWeight L S.a₁) S.ν
        (bgMultC S.G' (compWeight L S.a₁) S.ν (bgC0 d L N) S.D')
        (bgFieldC S.G' (compWeight L S.a₁) S.ν (bgC0 d L N) S.D')
        (liftC S.hG' (S.markedTangentC z u t x))) 0) :
    (fderiv ℂ (S.Phi1C (zeroClass d L N₁ T.m₁ k N ϱ)) ((s : ℂ) • S.shiftUC x))
        (S.maskUC z (S.shiftUC x)) = -(S.β : ℂ) * (f s - f 0 - (s : ℂ) * deriv f 0) := by
  subst hϱ
  obtain rfl : S₀ = T.step k hk N₁ ν β p₁ := hS₀
  have hr0 := D.r_pos
  have hlt : p₁ < lvCpsiG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2))) := by
    have h := mul_le_mul_of_nonneg_right
      (show (1 : ℝ) ≤ 2 * 2 + lvRG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2))) p₁ by linarith) hp.le
    linarith [D.ray_margin]
  have hδ₁ : Real.sqrt (N : ℝ) * ((T.step k hk N₁ ν β p₁).betaU ^ (-(1 / 2 : ℝ)) *
      (covSupConstC d L N (compWeight L (1 : ℝ) k) T.κ * lvCpsiG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2))))) < T.t := by
    rw [← (T.step k hk N₁ ν β p₁).norm_betaU_rpow hβ.le]
    exact D.fl_radius
  have hMR : S.MarkRealAt T.t 2 x := by
    subst hS
    exact ((T.step k hk N₁ ν β p₁).withDatum D' hDh).markRealAt_of_chart D.core T.large_block
      T.dom_margin T.coer_margin T.δc_small one_pos T.c7_cap (R := 2) (by norm_num) T.bg1_cap hβ
      D.cψ_pos hδ₁ hlt hD hx
  have hAn : AnalyticAt ℂ (fun y : S.EC => S.VkC (S.psi0C + y)) 0 := by
    subst hS
    have h0 : (0 : ((T.step k hk N₁ ν β p₁).withDatum D' hDh).EC) ∈
        ((T.step k hk N₁ ν β p₁).withDatum D' hDh).shiftDomC (lvCpsiG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2)))) :=
      fun p => by simpa [StepSetting.hatOfShift] using D.cψ_pos
    exact ((T.step k hk N₁ ν β p₁).withDatum D' hDh).analyticAt_VkC_shift D.core T.large_block
      T.dom_margin T.coer_margin T.δc_small one_pos T.c7_cap (R := 2) (by norm_num) T.bg1_cap hβ
      D.cψ_pos hδ₁ hD h0
  have hray0 : ∀ u t : ℂ, ∀ᶠ r : ℝ in 𝓝 0, InUnionDomainC (stepG d L N₁ T.m₁ k (rhoSepG d L T.m₁))
      (bgC0 d L N) (bgC1 d L N) S.ν
      (S.dataUC (S.psiAtV ((r : ℝ) : ℂ) (u • S.shiftUC x + t • S.maskUC z (S.shiftUC x)))) := by
    subst hS
    intro u t
    have h0 : (0 : ((T.step k hk N₁ ν β p₁).withDatum D' hDh).EC) ∈
        ((T.step k hk N₁ ν β p₁).withDatum D' hDh).shiftDomC (lvCpsiG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2)))) :=
      fun p => by simpa [StepSetting.hatOfShift] using D.cψ_pos
    have hc : Continuous (fun r : ℝ => (r : ℂ) •
        (u • ((T.step k hk N₁ ν β p₁).withDatum D' hDh).shiftUC x +
          t • ((T.step k hk N₁ ν β p₁).withDatum D' hDh).maskUC z
            (((T.step k hk N₁ ν β p₁).withDatum D' hDh).shiftUC x))) :=
      Complex.continuous_ofReal.smul continuous_const
    filter_upwards [hc.continuousAt.eventually
      ((((T.step k hk N₁ ν β p₁).withDatum D' hDh).isOpen_shiftDomC _).mem_nhds
        (by simpa using h0))] with r hr
    exact ((T.step k hk N₁ ν β p₁).withDatum D' hDh).dataUC_inUnionDomainC_of_shiftDomC D.core
      T.large_block T.dom_margin T.coer_margin T.δc_small one_pos T.c7_cap (R := 2)
      (by norm_num) T.bg1_cap hβ D.cψ_pos hδ₁ hD hr
  have hD2 : InUnionDomainC S.G' (bgC0 d L N) (thm73C2 d L N) S.ν S.D' := hMR.1
  have hH : BgHyp d L (k + 1) (rhoSepG d L T.m₁) S.a S.ν := by subst hS; exact D.core.HBp
  have hbase : InUnionDomainC (stepG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) (bgC0 d L N) (bgC2 d L N) S.ν
      (S.dataUC S.psi0C) := S.baseDomainC_of_chart (by subst hS; exact one_pos) hH hD2
  have hd : DifferentiableAt ℂ (S.Phi1C (zeroClass d L N₁ T.m₁ k N (rhoSepG d L T.m₁)))
      ((s : ℂ) • S.shiftUC x) := hMR.2.2 s hs
  have hβS : 0 < S.β := by subst hS; exact hβ
  exact S.fderiv_mask_eq_neg_beta_taylor1_corrected_total z (by subst hS; exact one_pos) hH hD2
    hbase x hAn hray0 f hf hβS s hd

/-- **The block-energy total is `V + ½δ` in the two complex mark variables, at every scale of the
tower** (zero class).  For every `(u, t)` in the polydisc `‖u‖ < 17/16`, `‖t‖ < 1/16`, which is
an open connected set containing `{0} × {0}` and `[0,1] × {0}`,
`∑_b E_b(rawOf θ, lift v_{u,t}) = V^{(k)}(ψ^{(k)} + v_{u,t}) + ½ ⟨ψ', Δ^{(k)} ψ'⟩(v_{u,t})`. -/
theorem sum_blockEnergy_eq_VkC_add_delta_fromTowerG {d L N : ℕ} [NeZero L] {κmin : ℝ} (T : StepTowerG d L N κmin) {k : ℕ}
    {hk : 1 ≤ k} {N₁ : ℕ} [NeZero N₁] {ν β p₁ : ℝ} (D : StepScaleDataG T k hk N₁ ν β p₁)
    (hβ : 0 < β) (hp : 0 < p₁) {ϱ : ℝ}
    (hϱ : ϱ = rhoSepG d L T.m₁) {S₀ : StepSetting d L N₁ T.m₁ k N ϱ}
    (hS₀ : S₀ = hatStepKG T.hN k T.m₁ ϱ hk ν β p₁ T.δ)
    (D' : BgData S₀.G' N)
    (hDh : ∀ y i, D'.h y i = (S₀.h₀ i : ℂ))
    (hD : XiCData S₀.G' (compWeight L 1) ν (k + 1) 1 T.t D')
    {S : StepSetting d L N₁ T.m₁ k N ϱ}
    (hS : S = S₀.withDatum D' hDh)
    (x : S.E) (hx : ‖x‖ ≤ p₁) (z : Torus d (N₁ * L ^ T.m₁ * L ^ (k + 1 - (k + 1))))
    {u t : ℂ} (hu : ‖u‖ < 17 / 16) (ht : ‖t‖ < 1 / 16) :
    (∑ b : Torus d (N₁ * L ^ T.m₁ * L ^ (k + 1 - (k + 1))),
      blockEnergyOne S.G' (stepG d L N₁ T.m₁ k ϱ) S.a₁ S.ν T.BG₂ T.κ T.t k b
        (rawOf S.D', liftC S.hG' (S.markedTangentC z u t x))) =
      S.VkC (S.psi0C + S.markedTangentC z u t x) +
        (1 / 2) * deltaForm (S.hG.precedes S.hG' (le_refl (k + 1))) (compWeight L S.a₁) S.ν
          (bgMultC S.G' (compWeight L S.a₁) S.ν (bgC0 d L N) S.D')
          (bgFieldC S.G' (compWeight L S.a₁) S.ν (bgC0 d L N) S.D')
          (liftC S.hG' (S.markedTangentC z u t x)) := by
  subst hϱ
  obtain rfl : S₀ = T.step k hk N₁ ν β p₁ := hS₀
  subst hS
  have hr0 := D.r_pos
  have hlt : p₁ < lvCpsiG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2))) := by
    have h := mul_le_mul_of_nonneg_right
      (show (1 : ℝ) ≤ 2 * 2 + lvRG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2))) p₁ by linarith) hp.le
    linarith [D.ray_margin]
  have hδ₁ : Real.sqrt (N : ℝ) * ((T.step k hk N₁ ν β p₁).betaU ^ (-(1 / 2 : ℝ)) *
      (covSupConstC d L N (compWeight L (1 : ℝ) k) T.κ * lvCpsiG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2))))) < T.t := by
    rw [← (T.step k hk N₁ ν β p₁).norm_betaU_rpow hβ.le]
    exact D.fl_radius
  have hMR := ((T.step k hk N₁ ν β p₁).withDatum D' hDh).markRealAt_of_chart D.core T.large_block
    T.dom_margin T.coer_margin T.δc_small one_pos T.c7_cap (R := 2) (by norm_num) T.bg1_cap hβ
    D.cψ_pos hδ₁ hlt hD hx
  have hdisc := markReal_disc_sliceG T D hp rfl (S₀ := T.step k hk N₁ ν β p₁) rfl D' hDh hD hx z hu t ht 1 (by
    rw [norm_one]; linarith)
  have hball : liftC ((T.step k hk N₁ ν β p₁).withDatum D' hDh).hG'
      (((T.step k hk N₁ ν β p₁).withDatum D' hDh).markedTangentC z u t x) ∈
      FlBall (stepG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) T.t := by
    rw [StepSetting.liftC_markedTangentC]
    simpa only [map_smul, one_smul] using hdisc
  exact ((T.step k hk N₁ ν β p₁).withDatum D' hDh).sum_blockEnergyOne_eq_VkC_add_delta z D.core
    one_pos T.c7_cap (R := 2) le_rfl T.t_cap T.bg0_cap T.cK2_cap T.cK2'_cap hD x hMR hball

/-- **The mark `f(u)` of `V + ½δ` is the mark of the block-energy total, for every complex `u`
with `‖u‖ < 17/16`** (zero class, tower).  This set contains `0`, the segment `[0,1]` and a
neighbourhood of each of its points; no analytic continuation in `u` is needed. -/
theorem mark_eq_deriv_blockEnergy_fromTowerG {d L N : ℕ} [NeZero L] {κmin : ℝ} (T : StepTowerG d L N κmin) {k : ℕ}
    {hk : 1 ≤ k} {N₁ : ℕ} [NeZero N₁] {ν β p₁ : ℝ} (D : StepScaleDataG T k hk N₁ ν β p₁)
    (hβ : 0 < β) (hp : 0 < p₁) {ϱ : ℝ}
    (hϱ : ϱ = rhoSepG d L T.m₁) {S₀ : StepSetting d L N₁ T.m₁ k N ϱ}
    (hS₀ : S₀ = hatStepKG T.hN k T.m₁ ϱ hk ν β p₁ T.δ)
    (D' : BgData S₀.G' N)
    (hDh : ∀ y i, D'.h y i = (S₀.h₀ i : ℂ))
    (hD : XiCData S₀.G' (compWeight L 1) ν (k + 1) 1 T.t D')
    {S : StepSetting d L N₁ T.m₁ k N ϱ}
    (hS : S = S₀.withDatum D' hDh)
    (x : S.E) (hx : ‖x‖ ≤ p₁) (z : Torus d (N₁ * L ^ T.m₁ * L ^ (k + 1 - (k + 1)))) (f : ℂ → ℂ)
    (hf : ∀ u : ℂ, f u = deriv (fun t : ℂ => S.VkC (S.psi0C + S.markedTangentC z u t x) +
      (1 / 2) * deltaForm (S.hG.precedes S.hG' (le_refl (k + 1))) (compWeight L S.a₁) S.ν
        (bgMultC S.G' (compWeight L S.a₁) S.ν (bgC0 d L N) S.D')
        (bgFieldC S.G' (compWeight L S.a₁) S.ν (bgC0 d L N) S.D')
        (liftC S.hG' (S.markedTangentC z u t x))) 0)
    {u : ℂ} (hu : ‖u‖ < 17 / 16) :
    f u = deriv (fun t : ℂ => ∑ b : Torus d (N₁ * L ^ T.m₁ * L ^ (k + 1 - (k + 1))),
      blockEnergyOne S.G' (stepG d L N₁ T.m₁ k ϱ) S.a₁ S.ν T.BG₂ T.κ T.t k b
        (rawOf S.D', liftC S.hG' (S.markedTangentC z u t x))) 0 := by
  subst hϱ
  obtain rfl : S₀ = T.step k hk N₁ ν β p₁ := hS₀
  rw [hf u]
  refine Filter.EventuallyEq.deriv_eq ?_
  filter_upwards [Metric.ball_mem_nhds (0 : ℂ) (show (0 : ℝ) < 1 / 16 by norm_num)] with t ht
  have ht' : ‖t‖ < 1 / 16 := by simpa using ht
  exact (sum_blockEnergy_eq_VkC_add_delta_fromTowerG T D hβ hp rfl (S₀ := T.step k hk N₁ ν β p₁) rfl D' hDh hD hS x hx z hu ht').symm

end Balaban.Inhabited
