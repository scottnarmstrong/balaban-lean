/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.DecMarkTotalFromTower
public import Balaban.Inhabited.DecMarkCorrTotalFromTowerG
public import Balaban.Inhabited.StepScaleDataGBridge
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
  exact fderiv_mask_corrected_total_fromTowerG T.toG (T.scaleDataG_of_fixed D) hβ hp
    (ϱ := rhoSep T.m₁) (rhoSepG_three _).symm (S₀ := T.step k hk N₁ ν β p₁) rfl D' hDh hD hS x hx
    z hs f hf

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
  exact sum_blockEnergy_eq_VkC_add_delta_fromTowerG T.toG (T.scaleDataG_of_fixed D) hβ hp
    (ϱ := rhoSep T.m₁) (rhoSepG_three _).symm (S₀ := T.step k hk N₁ ν β p₁) rfl D' hDh hD hS x hx
    z hu ht

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
  exact mark_eq_deriv_blockEnergy_fromTowerG T.toG (T.scaleDataG_of_fixed D) hβ hp
    (ϱ := rhoSep T.m₁) (rhoSepG_three _).symm (S₀ := T.step k hk N₁ ν β p₁) rfl D' hDh hD hS x hx
    z f hf hu

end Balaban.Inhabited
