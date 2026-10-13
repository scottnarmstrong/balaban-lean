/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.DecMarkCorrectedTotal
public import Balaban.Inhabited.DecMarkTotalFromTower
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The corrected mark of the total at the shared tower, and its tie to the block-energy total

* `StepSetting.sum_blockEnergyOne_eq_VkC_add_delta`: for complex mark variables `(u, t)` with
  `lift(u ψ' + t M_z ψ')` in the fluctuation ball, the sum of the block energies at the lifted
  marked tangent is `V^{(k)}(ψ^{(k)} + v_{u,t}) + ½ ⟨ψ', Δ^{(k)} ψ'⟩(v_{u,t})`
  (`interactionV_eq_energy` and `VkC_psi0C_add_eq_interactionOne`, as inside the proof of
  `fderiv_mask_eq_neg_beta_deriv_energy_add_delta`, now for complex `u, t`).
* `fderiv_mask_corrected_total_fromTower`: the identity
  `DΦ₁(s ψ')[M_z ψ'] = -β (f s - f 0 - s f'(0))` at a scale of the shared tower, every hypothesis
  of `fderiv_mask_eq_neg_beta_taylor1_corrected_total` discharged.
* `sum_blockEnergy_eq_VkC_add_delta_fromTower`: the identity of the first bullet at the tower, on
  the whole polydisc `‖u‖ < 17/16`, `‖t‖ < 1/16`.
* `mark_eq_deriv_blockEnergy_fromTower`: `f(u)` is the derivative at `t = 0` of the block-energy
  total, for every complex `u` with `‖u‖ < 17/16`.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Localization
  Balaban.Localization.I5Inhabited Balaban.Polymer Balaban.SmallField.Def6 Matrix Metric Set

namespace StepSetting

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}
  (S : StepSetting d L N₁ m₁ k N ϱ) (z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))))

/-- **The block-energy total is `V + ½δ` in the two complex mark variables.**  Under the
hypotheses of `fderiv_mask_eq_neg_beta_deriv_energy_add_delta` (`MarkRealAt` supplies the domain
and the real clause), for complex `u, t` such that the lifted marked tangent lies in the ball
`FlBall`: `∑_b E_b(rawOf θ, lift v_{u,t}) = V^{(k)}(ψ^{(k)} + v_{u,t}) + ½ ⟨ψ', Δ^{(k)} ψ'⟩(v_{u,t})`. -/
theorem sum_blockEnergyOne_eq_VkC_add_delta {c BG κ eps Kc Cx c₂ BG₂ δ₁ : ℝ}
    (hC : FlCore N S.G' (stepG d L N₁ m₁ k ϱ) S.a₁ S.ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
    (ha₁ : 0 < S.a₁) (hc7 : c7 d L N BG κ ≤ thm73C3 d L N) {R : ℝ} (hR : 2 ≤ R)
    (hRs : R * δ₁ ≤ deltaStar d L N) (hsmall : cK2 d L N * (R * δ₁) < bgC0 d L N / 2)
    (hnum : cK2 d L N * δ₁ ≤ c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8))
    (hnum' : cK2' d L N (famConst d L BG₂ κ) * δ₁ ≤
      c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8))
    (hD : XiCData S.G' S.a S.ν (k + 1) 1 eps S.D') (x : S.E) (hMR : S.MarkRealAt δ₁ R x)
    {u t : ℂ}
    (hball : liftC S.hG' (S.markedTangentC z u t x) ∈ FlBall (stepG d L N₁ m₁ k ϱ) δ₁) :
    (∑ b : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))),
      blockEnergyOne S.G' (stepG d L N₁ m₁ k ϱ) S.a₁ S.ν BG₂ κ eps k b
        (rawOf S.D', liftC S.hG' (S.markedTangentC z u t x))) =
      S.VkC (S.psi0C + S.markedTangentC z u t x) +
        (1 / 2) * deltaForm (S.hG.precedes S.hG' (le_refl (k + 1))) (compWeight L S.a₁) S.ν
          (bgMultC S.G' (compWeight L S.a₁) S.ν (bgC0 d L N) S.D')
          (bgFieldC S.G' (compWeight L S.a₁) S.ν (bgC0 d L N) S.D')
          (liftC S.hG' (S.markedTangentC z u t x)) := by
  classical
  obtain ⟨-, hreal, -⟩ := hMR
  obtain ⟨D, hh, hD3, hdisc'⟩ := hreal _ hball (isLayerConstant_liftC S.hG S.hG' _)
  have hψ : compTangent S.hG S.hG' (le_refl (k + 1)) (compWeight L S.a₁)
      (bgFieldC S.G' (compWeight L S.a₁) S.ν (bgC0 d L N) S.D') S.D' D ∈
      FlBall (stepG d L N₁ m₁ k ϱ) δ₁ := by
    rw [hD3]; exact hball
  have h1 := interactionV_eq_energy hC S.hG S.hG' (le_refl (k + 1)) ha₁ hC.HBp S.D' hD hc7 D hh
    hψ hR hdisc' hRs hsmall hnum hnum'
  have h2 := interactionOne_eq S.hG S.hG' (le_refl (k + 1)) hD hh
  rw [S.VkC_psi0C_add_eq_interactionOne hD, ← hD3, h2, h1]
  have hs : (∑ b : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))),
      blockEnergyOne S.G' (stepG d L N₁ m₁ k ϱ) S.a₁ S.ν BG₂ κ eps k b
        (rawOf S.D', compTangent S.hG S.hG' (le_refl (k + 1)) (compWeight L S.a₁)
          (bgFieldC S.G' (compWeight L S.a₁) S.ν (bgC0 d L N) S.D') S.D' D)) =
      ∑ b : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))),
        energyBlock S.G' (stepG d L N₁ m₁ k ϱ) (compWeight L S.a₁) S.ν k
          (bgMultC S.G' (compWeight L S.a₁) S.ν (bgC0 d L N) S.D')
          (flFieldOne S.G' (stepG d L N₁ m₁ k ϱ) BG₂ κ S.a₁ S.ν S.D'
            (compTangent S.hG S.hG' (le_refl (k + 1)) (compWeight L S.a₁)
              (bgFieldC S.G' (compWeight L S.a₁) S.ν (bgC0 d L N) S.D') S.D' D))
          (compTangent S.hG S.hG' (le_refl (k + 1)) (compWeight L S.a₁)
            (bgFieldC S.G' (compWeight L S.a₁) S.ν (bgC0 d L N) S.D') S.D' D) b :=
    Finset.sum_congr rfl fun b _ => blockEnergyOne_rawOf hD k b _
  rw [hs]
  ring

end StepSetting


end Balaban.Fluctuation

namespace Balaban.Inhabited

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation
  Balaban.Localization Balaban.Localization.LevelPair Balaban.Localization.I5Inhabited
  Balaban.Polymer Balaban.SmallField.Def6 Balaban.Inhabited.LevelStep Matrix Metric Set Filter
  Topology

/-- **The corrected mark of the total at every scale of the tower.**  The hypotheses of
`StepSetting.fderiv_mask_eq_neg_beta_taylor1_corrected_total` (`hAn`, `ha₁`, `H`, `hD2`, `hbase`,
`hray0` for every mixed direction `(u, t)`, `hd`, `hβ`) hold at the step
`(T.step k hk N₁ ν β p₁).withDatum D' hDh` of a scale of a shared tower: `f` is the mark
`u ↦ ∂ₜ [V + ½δ](v_{u,t})|ₜ₌₀` and `DΦ₁(s ψ')[M_z ψ'] = -β (f s - f 0 - s f'(0))` for real
`s ∈ [0,1]`, `‖x‖ ≤ p₁`. -/
theorem fderiv_mask_corrected_total_fromTower {κmin : ℝ} (T : StepTower κmin) {k : ℕ}
    {hk : 1 ≤ k} {N₁ : ℕ} [NeZero N₁] {ν β p₁ : ℝ} (D : StepScaleData T k hk N₁ ν β p₁)
    (hβ : 0 < β) (hp : 0 < p₁)
    (D' : BgData (T.step k hk N₁ ν β p₁).G' 2)
    (hDh : ∀ y i, D'.h y i = ((T.step k hk N₁ ν β p₁).h₀ i : ℂ))
    (hD : XiCData (T.step k hk N₁ ν β p₁).G' (compWeight 3 1) ν (k + 1) 1 T.t D')
    {S : StepSetting 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)}
    (hS : S = (T.step k hk N₁ ν β p₁).withDatum D' hDh)
    (x : S.E) (hx : ‖x‖ ≤ p₁) (z : Torus 3 (N₁ * 3 ^ T.m₁ * 3 ^ (k + 1 - (k + 1)))) {s : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) (f : ℂ → ℂ)
    (hf : ∀ u : ℂ, f u = deriv (fun t : ℂ => S.VkC (S.psi0C + S.markedTangentC z u t x) +
      (1 / 2) * deltaForm (S.hG.precedes S.hG' (le_refl (k + 1))) (compWeight 3 S.a₁) S.ν
        (bgMultC S.G' (compWeight 3 S.a₁) S.ν (bgC0 3 3 2) S.D')
        (bgFieldC S.G' (compWeight 3 S.a₁) S.ν (bgC0 3 3 2) S.D')
        (liftC S.hG' (S.markedTangentC z u t x))) 0) :
    (fderiv ℂ (S.Phi1C (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁))) ((s : ℂ) • S.shiftUC x))
        (S.maskUC z (S.shiftUC x)) = -(S.β : ℂ) * (f s - f 0 - (s : ℂ) * deriv f 0) := by
  have hr0 := D.r_pos
  have hlt : p₁ < lvCpsi T.κ T.t (β * 3 ^ k) := by
    have h := mul_le_mul_of_nonneg_right
      (show (1 : ℝ) ≤ 2 * 2 + lvR T.κ T.t (β * 3 ^ k) p₁ by linarith) hp.le
    linarith [D.ray_margin]
  have hδ₁ : Real.sqrt ((2 : ℕ) : ℝ) * ((T.step k hk N₁ ν β p₁).betaU ^ (-(1 / 2 : ℝ)) *
      (covSupConstC 3 3 2 (compWeight 3 (1 : ℝ) k) T.κ * lvCpsi T.κ T.t (β * 3 ^ k))) < T.t := by
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
        ((T.step k hk N₁ ν β p₁).withDatum D' hDh).shiftDomC (lvCpsi T.κ T.t (β * 3 ^ k)) :=
      fun p => by simpa [StepSetting.hatOfShift] using D.cψ_pos
    exact ((T.step k hk N₁ ν β p₁).withDatum D' hDh).analyticAt_VkC_shift D.core T.large_block
      T.dom_margin T.coer_margin T.δc_small one_pos T.c7_cap (R := 2) (by norm_num) T.bg1_cap hβ
      D.cψ_pos hδ₁ hD h0
  have hray0 : ∀ u t : ℂ, ∀ᶠ r : ℝ in 𝓝 0, InUnionDomainC (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁))
      (bgC0 3 3 2) (bgC1 3 3 2) S.ν
      (S.dataUC (S.psiAtV ((r : ℝ) : ℂ) (u • S.shiftUC x + t • S.maskUC z (S.shiftUC x)))) := by
    subst hS
    intro u t
    have h0 : (0 : ((T.step k hk N₁ ν β p₁).withDatum D' hDh).EC) ∈
        ((T.step k hk N₁ ν β p₁).withDatum D' hDh).shiftDomC (lvCpsi T.κ T.t (β * 3 ^ k)) :=
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
  have hD2 : InUnionDomainC S.G' (bgC0 3 3 2) (thm73C2 3 3 2) S.ν S.D' := hMR.1
  have hH : BgHyp 3 3 (k + 1) (rhoSep T.m₁) S.a S.ν := by subst hS; exact D.core.HBp
  have hbase : InUnionDomainC (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) (bgC0 3 3 2) (bgC2 3 3 2) S.ν
      (S.dataUC S.psi0C) := S.baseDomainC_of_chart (by subst hS; exact one_pos) hH hD2
  have hd : DifferentiableAt ℂ (S.Phi1C (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)))
      ((s : ℂ) • S.shiftUC x) := hMR.2.2 s hs
  have hβS : 0 < S.β := by subst hS; exact hβ
  exact S.fderiv_mask_eq_neg_beta_taylor1_corrected_total z (by subst hS; exact one_pos) hH hD2
    hbase x hAn hray0 f hf hβS s hd

/-- **The block-energy total is `V + ½δ` in the two complex mark variables, at every scale of the
tower** (zero class).  For every `(u, t)` in the polydisc `‖u‖ < 17/16`, `‖t‖ < 1/16`, which is
an open connected set containing `{0} × {0}` and `[0,1] × {0}`,
`∑_b E_b(rawOf θ, lift v_{u,t}) = V^{(k)}(ψ^{(k)} + v_{u,t}) + ½ ⟨ψ', Δ^{(k)} ψ'⟩(v_{u,t})`. -/
theorem sum_blockEnergy_eq_VkC_add_delta_fromTower {κmin : ℝ} (T : StepTower κmin) {k : ℕ}
    {hk : 1 ≤ k} {N₁ : ℕ} [NeZero N₁] {ν β p₁ : ℝ} (D : StepScaleData T k hk N₁ ν β p₁)
    (hβ : 0 < β) (hp : 0 < p₁)
    (D' : BgData (T.step k hk N₁ ν β p₁).G' 2)
    (hDh : ∀ y i, D'.h y i = ((T.step k hk N₁ ν β p₁).h₀ i : ℂ))
    (hD : XiCData (T.step k hk N₁ ν β p₁).G' (compWeight 3 1) ν (k + 1) 1 T.t D')
    {S : StepSetting 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)}
    (hS : S = (T.step k hk N₁ ν β p₁).withDatum D' hDh)
    (x : S.E) (hx : ‖x‖ ≤ p₁) (z : Torus 3 (N₁ * 3 ^ T.m₁ * 3 ^ (k + 1 - (k + 1))))
    {u t : ℂ} (hu : ‖u‖ < 17 / 16) (ht : ‖t‖ < 1 / 16) :
    (∑ b : Torus 3 (N₁ * 3 ^ T.m₁ * 3 ^ (k + 1 - (k + 1))),
      blockEnergyOne S.G' (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) S.a₁ S.ν T.BG₂ T.κ T.t k b
        (rawOf S.D', liftC S.hG' (S.markedTangentC z u t x))) =
      S.VkC (S.psi0C + S.markedTangentC z u t x) +
        (1 / 2) * deltaForm (S.hG.precedes S.hG' (le_refl (k + 1))) (compWeight 3 S.a₁) S.ν
          (bgMultC S.G' (compWeight 3 S.a₁) S.ν (bgC0 3 3 2) S.D')
          (bgFieldC S.G' (compWeight 3 S.a₁) S.ν (bgC0 3 3 2) S.D')
          (liftC S.hG' (S.markedTangentC z u t x)) := by
  subst hS
  have hr0 := D.r_pos
  have hlt : p₁ < lvCpsi T.κ T.t (β * 3 ^ k) := by
    have h := mul_le_mul_of_nonneg_right
      (show (1 : ℝ) ≤ 2 * 2 + lvR T.κ T.t (β * 3 ^ k) p₁ by linarith) hp.le
    linarith [D.ray_margin]
  have hδ₁ : Real.sqrt ((2 : ℕ) : ℝ) * ((T.step k hk N₁ ν β p₁).betaU ^ (-(1 / 2 : ℝ)) *
      (covSupConstC 3 3 2 (compWeight 3 (1 : ℝ) k) T.κ * lvCpsi T.κ T.t (β * 3 ^ k))) < T.t := by
    rw [← (T.step k hk N₁ ν β p₁).norm_betaU_rpow hβ.le]
    exact D.fl_radius
  have hMR := ((T.step k hk N₁ ν β p₁).withDatum D' hDh).markRealAt_of_chart D.core T.large_block
    T.dom_margin T.coer_margin T.δc_small one_pos T.c7_cap (R := 2) (by norm_num) T.bg1_cap hβ
    D.cψ_pos hδ₁ hlt hD hx
  have hdisc := markReal_disc_slice T D hp D' hDh hD hx z hu t ht 1 (by
    rw [norm_one]; linarith)
  have hball : liftC ((T.step k hk N₁ ν β p₁).withDatum D' hDh).hG'
      (((T.step k hk N₁ ν β p₁).withDatum D' hDh).markedTangentC z u t x) ∈
      FlBall (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) T.t := by
    rw [StepSetting.liftC_markedTangentC]
    simpa only [map_smul, one_smul] using hdisc
  exact ((T.step k hk N₁ ν β p₁).withDatum D' hDh).sum_blockEnergyOne_eq_VkC_add_delta z D.core
    one_pos T.c7_cap (R := 2) le_rfl T.t_cap T.bg0_cap T.cK2_cap T.cK2'_cap hD x hMR hball

/-- **The mark `f(u)` of `V + ½δ` is the mark of the block-energy total, for every complex `u`
with `‖u‖ < 17/16`** (zero class, tower).  This set contains `0`, the segment `[0,1]` and a
neighbourhood of each of its points; no analytic continuation in `u` is needed. -/
theorem mark_eq_deriv_blockEnergy_fromTower {κmin : ℝ} (T : StepTower κmin) {k : ℕ}
    {hk : 1 ≤ k} {N₁ : ℕ} [NeZero N₁] {ν β p₁ : ℝ} (D : StepScaleData T k hk N₁ ν β p₁)
    (hβ : 0 < β) (hp : 0 < p₁)
    (D' : BgData (T.step k hk N₁ ν β p₁).G' 2)
    (hDh : ∀ y i, D'.h y i = ((T.step k hk N₁ ν β p₁).h₀ i : ℂ))
    (hD : XiCData (T.step k hk N₁ ν β p₁).G' (compWeight 3 1) ν (k + 1) 1 T.t D')
    {S : StepSetting 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)}
    (hS : S = (T.step k hk N₁ ν β p₁).withDatum D' hDh)
    (x : S.E) (hx : ‖x‖ ≤ p₁) (z : Torus 3 (N₁ * 3 ^ T.m₁ * 3 ^ (k + 1 - (k + 1)))) (f : ℂ → ℂ)
    (hf : ∀ u : ℂ, f u = deriv (fun t : ℂ => S.VkC (S.psi0C + S.markedTangentC z u t x) +
      (1 / 2) * deltaForm (S.hG.precedes S.hG' (le_refl (k + 1))) (compWeight 3 S.a₁) S.ν
        (bgMultC S.G' (compWeight 3 S.a₁) S.ν (bgC0 3 3 2) S.D')
        (bgFieldC S.G' (compWeight 3 S.a₁) S.ν (bgC0 3 3 2) S.D')
        (liftC S.hG' (S.markedTangentC z u t x))) 0)
    {u : ℂ} (hu : ‖u‖ < 17 / 16) :
    f u = deriv (fun t : ℂ => ∑ b : Torus 3 (N₁ * 3 ^ T.m₁ * 3 ^ (k + 1 - (k + 1))),
      blockEnergyOne S.G' (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) S.a₁ S.ν T.BG₂ T.κ T.t k b
        (rawOf S.D', liftC S.hG' (S.markedTangentC z u t x))) 0 := by
  rw [hf u]
  refine Filter.EventuallyEq.deriv_eq ?_
  filter_upwards [Metric.ball_mem_nhds (0 : ℂ) (show (0 : ℝ) < 1 / 16 by norm_num)] with t ht
  have ht' : ‖t‖ < 1 / 16 := by simpa using ht
  exact (sum_blockEnergy_eq_VkC_add_delta_fromTower T D hβ hp D' hDh hD hS x hx z hu ht').symm

end Balaban.Inhabited
