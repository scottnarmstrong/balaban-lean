/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.MarkedTwoMarkLocal
public import Balaban.Fluctuation.MarkedRootAssembly
public import Balaban.Fluctuation.InteractionVPart
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The decoupled marks and the physical mark (`DecMarkTotal`)

The mark records of the step are built from the decoupled terms `evDec`, whose rooted sum is the
`t`-derivative at `0` of the block-energy sum along the masked decoupled tangent
(`marked_count_scaled_dec_resummed`).  This file compares that derivative with the masked Fréchet
derivative of `Φ₁` (the `E1MarksC` integrand) on the constant-`h₀` slice, zero class.

* `markedTangDec_eq_liftC_markedTangentC`: the masked decoupled tangent at the datum of the step,
  with `cc = β_k^{-1/2}`, the mask `blockU z` and the hat field `yhat x`, is the lift of the
  marked tangent `u · shiftUC x + t · maskUC z (shiftUC x)` of the step.  This is the coincidence
  at cut parameter `1` (`hatLift_eq_liftC`, `covSqrtC_eq_hatCovSqrt`).
* `markedFunDec_eq_blockEnergyOne`: the block functional along the masked decoupled tangent is the
  block energy of the step at the lifted marked tangent.
* `fderiv_mask_eq_neg_beta_deriv_energy_add_delta`: the exact relation between the two quantities.
  The block energies add up to `V^{(k)}` plus half the quadratic form
  `⟨ψ', Δ^{(k)} ψ'⟩` (`interactionV_eq_energy`), so the derivative of the block-energy sum differs
  from that of `V^{(k)}` by the derivative of the quadratic form; the relation carries that term.
* `sum_markedOutDec_physical`: the rooted sum of the decoupled marks, `marked_count_scaled_dec_resummed`
  and the relation together.

## Scope

Zero class, generator-neutral.  Block locality (another prover), the numerical budget and
`E1MarksC` are not here.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Background Balaban.Multiscale Balaban.Localization Balaban.SmallField
  Balaban.SmallField.Def6 Balaban.Polymer Set Metric Matrix Filter

namespace StepSetting

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}
  (S : StepSetting d L N₁ m₁ k N ϱ) (z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))))

/-! ### The coincidence at cut parameter `1` -/

/-- **The masked decoupled tangent at the datum of the step is the lifted marked tangent.**
With `cc = β_k^{-1/2}`, the mask `blockU z` and the hat field `yhat x`, the tangent
`lift(u · cc C^{1/2}(1) ψ̂ + t · M_z (cc C^{1/2}(1) ψ̂))` of `markedFunDec` is the lift of
`u · shiftUC x + t · maskUC z (shiftUC x)`. -/
theorem markedTangDec_eq_liftC_markedTangentC (u t : ℂ) (x : S.E) :
    markedTangDec S.hG' ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) S.a₁ S.ν (S.blockU z) u t S.D'
      (yhat x) = liftC S.hG' (S.markedTangentC z u t x) := by
  have hsh : S.shiftUC x = ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) • (S.covSqrtC *ᵥ yhat x) := rfl
  have hmask : S.maskUC z (S.shiftUC x) =
      maskBlock (S.blockU z) (((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) • (S.covSqrtC *ᵥ yhat x)) := by
    rw [hsh]; rfl
  unfold markedTangentC
  rw [hmask, hsh, S.covSqrtC_eq_hatCovSqrt]
  rfl

/-- **The block functional along the masked decoupled tangent is the block energy of the step at
the lifted marked tangent.** -/
theorem markedFunDec_eq_blockEnergyOne {κ eps BG₂ : ℝ}
    (hD : XiCData S.G' S.a S.ν (k + 1) 1 eps S.D') (u t : ℂ) (x : S.E)
    (b : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1)))) :
    markedFunDec S.hG' ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) S.a₁ S.ν BG₂ κ (S.blockU z) u t
        (blockEnergyFun S.G' (stepG d L N₁ m₁ k ϱ) (compWeight L S.a₁) S.ν k b) S.D' (yhat x) =
      blockEnergyOne S.G' (stepG d L N₁ m₁ k ϱ) S.a₁ S.ν BG₂ κ eps k b
        (rawOf S.D', liftC S.hG' (S.markedTangentC z u t x)) := by
  rw [blockEnergyOne_rawOf hD k b, ← S.markedTangDec_eq_liftC_markedTangentC z u t x]
  rfl

/-- **The relation between the derivative of the decoupled block-energy sum and the masked
Fréchet derivative of `Φ₁`** (zero class, constant-`h₀` slice, `s ∈ [0,1]`).  The block energies
add up to `V^{(k)} + ½⟨ψ', Δ^{(k)} ψ'⟩` (`interactionV_eq_energy`), so with `E(t)` the sum of the
block energies at the lifted marked tangent `v_t = s ψ' + t M_z ψ'` and `δ(t)` the quadratic form
`⟨ψ', Δ^{(k)} ψ'⟩` at `lift v_t`,
`DΦ₁(s ψ')[M_z ψ'] = -β E'(0) + (β/2) δ'(0)`.  The hypotheses are those of
`neg_beta_sum_markedOut_eq_fderiv_of_markReal` that concern the potential. -/
theorem fderiv_mask_eq_neg_beta_deriv_energy_add_delta
    {c BG κ eps Kc Cx c₂ BG₂ δ₁ : ℝ}
    (hC : FlCore N S.G' (stepG d L N₁ m₁ k ϱ) S.a₁ S.ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
    (ha₁ : 0 < S.a₁) (hc7 : c7 d L N BG κ ≤ thm73C3 d L N) {R : ℝ} (hR : 2 ≤ R)
    (hRs : R * δ₁ ≤ deltaStar d L N) (hsmall : cK2 d L N * (R * δ₁) < bgC0 d L N / 2)
    (hnum : cK2 d L N * δ₁ ≤ c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8))
    (hnum' : cK2' d L N (famConst d L BG₂ κ) * δ₁ ≤
      c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8))
    (hD : XiCData S.G' S.a S.ν (k + 1) 1 eps S.D') (hβ : 0 < S.β)
    {R₁ r t₁ : ℝ} (hR₁ : 1 < R₁) (hr : 0 < r) (ht₁ : 0 < t₁) (x : S.E) {s : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1)
    (hdisc : ∀ t : ℂ, ‖t‖ < t₁ → ∀ σ : ℂ, ‖σ‖ < R₁ + r →
      σ • (liftC S.hG' ((s : ℂ) • S.shiftUC x) + t • liftC S.hG' (S.maskUC z (S.shiftUC x))) ∈
        FlBall (stepG d L N₁ m₁ k ϱ) δ₁)
    (hMR : S.MarkRealAt δ₁ R x) :
    (fderiv ℂ (S.Phi1C (zeroClass d L N₁ m₁ k N ϱ)) ((s : ℂ) • S.shiftUC x))
        (S.maskUC z (S.shiftUC x)) =
      -(S.β : ℂ) * deriv (fun t : ℂ => ∑ b : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))),
        markedFunDec S.hG' ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) S.a₁ S.ν BG₂ κ (S.blockU z)
          (s : ℂ) t (blockEnergyFun S.G' (stepG d L N₁ m₁ k ϱ) (compWeight L S.a₁) S.ν k b)
          S.D' (yhat x)) 0 +
      ((S.β : ℂ) / 2) * deriv (fun t : ℂ =>
        deltaForm (S.hG.precedes S.hG' (le_refl (k + 1))) (compWeight L S.a₁) S.ν
          (bgMultC S.G' (compWeight L S.a₁) S.ν (bgC0 d L N) S.D')
          (bgFieldC S.G' (compWeight L S.a₁) S.ν (bgC0 d L N) S.D')
          (liftC S.hG' (S.markedTangentC z (s : ℂ) t x))) 0 := by
  classical
  obtain ⟨hD2, hreal, hray⟩ := hMR
  have hβc : (S.β : ℂ) ≠ 0 := by exact_mod_cast hβ.ne'
  set z0 := liftC S.hG' ((s : ℂ) • S.shiftUC x) with hz0
  set w := liftC S.hG' (S.maskUC z (S.shiftUC x)) with hw
  have hlift : ∀ t : ℂ, liftC S.hG' (S.markedTangentC z (s : ℂ) t x) = z0 + t • w :=
    fun t => S.liftC_markedTangentC z (s : ℂ) t x
  have hball : ∀ t : ℂ, ‖t‖ < t₁ →
      liftC S.hG' (S.markedTangentC z (s : ℂ) t x) ∈ FlBall (stepG d L N₁ m₁ k ϱ) δ₁ := by
    intro t ht
    have := hdisc t ht 1 (by rw [norm_one]; linarith)
    rwa [one_smul, ← hlift] at this
  obtain ⟨c0, c1, c2, hq⟩ := deltaForm_line (S.hG.precedes S.hG' (le_refl (k + 1)))
    (compWeight L S.a₁) S.ν (bgMultC S.G' (compWeight L S.a₁) S.ν (bgC0 d L N) S.D')
    (bgFieldC S.G' (compWeight L S.a₁) S.ν (bgC0 d L N) S.D') z0 w
  have hΔ : ∀ t : ℂ, deltaForm (S.hG.precedes S.hG' (le_refl (k + 1))) (compWeight L S.a₁) S.ν
      (bgMultC S.G' (compWeight L S.a₁) S.ν (bgC0 d L N) S.D')
      (bgFieldC S.G' (compWeight L S.a₁) S.ν (bgC0 d L N) S.D')
      (liftC S.hG' (S.markedTangentC z (s : ℂ) t x)) = c0 + c1 * t + c2 * t ^ 2 := by
    intro t
    rw [← hq t, hlift t]
    rfl
  have hΔd : HasDerivAt (fun t : ℂ => deltaForm (S.hG.precedes S.hG' (le_refl (k + 1)))
      (compWeight L S.a₁) S.ν (bgMultC S.G' (compWeight L S.a₁) S.ν (bgC0 d L N) S.D')
      (bgFieldC S.G' (compWeight L S.a₁) S.ν (bgC0 d L N) S.D')
      (liftC S.hG' (S.markedTangentC z (s : ℂ) t x))) c1 0 := by
    have h1 : HasDerivAt (fun t : ℂ => c0 + c1 * t + c2 * t ^ 2) c1 0 := by
      have h2 : HasDerivAt (fun t : ℂ => c0 + c1 * t) c1 0 := by
        simpa using ((hasDerivAt_id (0 : ℂ)).const_mul c1).const_add c0
      have h3 : HasDerivAt (fun t : ℂ => c2 * t ^ 2) 0 0 := by
        simpa using ((hasDerivAt_id (0 : ℂ)).pow 2).const_mul c2
      have h4 := h2.add h3
      rw [add_zero] at h4
      exact h4
    exact h1.congr_of_eventuallyEq (Filter.Eventually.of_forall hΔ)
  -- the heart: the interaction is the energy minus half the quadratic form near `t = 0`
  have heq : ∀ t : ℂ, ‖t‖ < t₁ →
      interactionOne S.hG S.hG' (le_refl (k + 1)) S.a₁ S.ν eps
          (rawOf S.D', liftC S.hG' (S.markedTangentC z (s : ℂ) t x)) =
        (∑ b : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))),
          blockEnergyOne S.G' (stepG d L N₁ m₁ k ϱ) S.a₁ S.ν BG₂ κ eps k b
            (rawOf S.D', liftC S.hG' (S.markedTangentC z (s : ℂ) t x))) -
        (1 / 2) * (c0 + c1 * t + c2 * t ^ 2) := by
    intro t ht
    obtain ⟨D, hh, hD3, hdisc'⟩ := hreal _ (hball t ht)
      (isLayerConstant_liftC S.hG S.hG' _)
    have hψ : compTangent S.hG S.hG' (le_refl (k + 1)) (compWeight L S.a₁)
        (bgFieldC S.G' (compWeight L S.a₁) S.ν (bgC0 d L N) S.D') S.D' D ∈
        FlBall (stepG d L N₁ m₁ k ϱ) δ₁ := by
      rw [hD3]; exact hball t ht
    rw [← hD3, interactionOne_eq S.hG S.hG' (le_refl (k + 1)) hD hh,
      interactionV_eq_energy hC S.hG S.hG' (le_refl (k + 1)) ha₁ hC.HBp S.D' hD hc7 D hh hψ hR
        hdisc' hRs hsmall hnum hnum']
    congr 1
    · exact Finset.sum_congr rfl fun b _ => by rw [blockEnergyOne_rawOf hD k b]
    · rw [← hΔ t, hD3]
  -- the physical side
  have hd := hray s hs
  have hF := S.hasDerivAt_Phi1C_marked z (zeroClass d L N₁ m₁ k N ϱ) (s : ℂ) x hd
  have hFV : ∀ t : ℂ, S.Phi1C (zeroClass d L N₁ m₁ k N ϱ) (S.markedTangentC z (s : ℂ) t x) =
      -(S.β : ℂ) * interactionOne S.hG S.hG' (le_refl (k + 1)) S.a₁ S.ν eps
        (rawOf S.D', liftC S.hG' (S.markedTangentC z (s : ℂ) t x)) := fun t => by
    rw [S.Phi1C_zeroClass, S.VkC_psi0C_add_eq_interactionOne hD]
  -- the energy sum has the derivative `-(1/β) F' + (1/2) δ'`
  have hE : HasDerivAt (fun t : ℂ => ∑ b : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))),
      blockEnergyOne S.G' (stepG d L N₁ m₁ k ϱ) S.a₁ S.ν BG₂ κ eps k b
        (rawOf S.D', liftC S.hG' (S.markedTangentC z (s : ℂ) t x)))
      ((-(S.β : ℂ))⁻¹ * (fderiv ℂ (S.Phi1C (zeroClass d L N₁ m₁ k N ϱ)) ((s : ℂ) • S.shiftUC x))
        (S.maskUC z (S.shiftUC x)) + (1 / 2) * c1) 0 := by
    have h1 := (hF.const_mul ((-(S.β : ℂ))⁻¹)).add (hΔd.const_mul ((1 : ℂ) / 2))
    refine h1.congr_of_eventuallyEq ?_
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) ht₁] with t ht
    have ht' : ‖t‖ < t₁ := by simpa using ht
    have := heq t ht'
    simp only [Pi.add_apply]
    rw [hFV t, hΔ t, ← mul_assoc, inv_mul_cancel₀ (neg_ne_zero.2 hβc), one_mul]
    linear_combination -this
  have hEu : (fun t : ℂ => ∑ b : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))),
      markedFunDec S.hG' ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) S.a₁ S.ν BG₂ κ (S.blockU z)
        (s : ℂ) t (blockEnergyFun S.G' (stepG d L N₁ m₁ k ϱ) (compWeight L S.a₁) S.ν k b)
        S.D' (yhat x)) = fun t : ℂ => ∑ b : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))),
      blockEnergyOne S.G' (stepG d L N₁ m₁ k ϱ) S.a₁ S.ν BG₂ κ eps k b
        (rawOf S.D', liftC S.hG' (S.markedTangentC z (s : ℂ) t x)) :=
    funext fun t => Finset.sum_congr rfl fun b _ => S.markedFunDec_eq_blockEnergyOne z hD _ t x b
  rw [hEu, hE.deriv, hΔd.deriv]
  field_simp
  ring

section Total

variable {c BG κ eps Kc Cx c₂ BG₂ δ₁ : ℝ} {m₀ : ℕ}
  {jV : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) → ℕ}
  {XV 𝒦XV : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) → Set (CTorus d L N₁ m₁ (k + 1))}
  {X₁V : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) → Finset (CTorus d L N₁ m₁ (k + 1))}

/-- **The decoupled marks and the physical mark on the constant-`h₀` slice.**  Let the hypotheses
of `marked_count_scaled_dec_resummed` hold for the step `S` (`Gp = S.G'`, `Hm = stepG`,
`cc = β_k^{-1/2}`, `cψ = p₁`, mask `Zm = blockU z`, root `z`), and let the hypotheses of
`fderiv_mask_eq_neg_beta_deriv_energy_add_delta` hold at the datum `S.D'` and the hat field `x`,
`‖x‖ ≤ p₁`, for a real `s ∈ [0,1]`.  There are maps `F₁, Sol` (the pair of the count) such that
the rooted sum of the decoupled marks `∑_{Y'} ∂_t evDec|₀` (`markedOutDec`, at the hat field
`yhat x` and `u = s`) is the `t`-derivative at `0` of the block-energy sum along the masked
decoupled tangent, and
`DΦ₁(s ψ')[M_z ψ'] = -β ∑_{Y'} markedOutDec + (β/2) δ'(0)`,
`δ(t) = ⟨ψ', Δ^{(k)} ψ'⟩` at `lift (s ψ' + t M_z ψ')`.  The last term is the derivative of the
quadratic form that separates the block-energy sum from `V^{(k)}`. -/
theorem sum_markedOutDec_physical
    (hC : FlCore N S.G' (stepG d L N₁ m₁ k ϱ) S.a₁ S.ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
    (hk : 1 ≤ k)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δc : ℝ}
    (hdm : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    (hcovV : ∀ b, CovSetup S.G' m₀ (jV b) (XV b) (𝒦XV b))
    (hX₁V : ∀ b, (↑(X₁V b) : Set (CTorus d L N₁ m₁ (k + 1))) = X1 S.G' m₀ (jV b) (𝒦XV b))
    (hconn : HatConn S.G') (hrow : RowInHat (coverOf S.G') (stepG d L N₁ m₁ k ϱ) (compWeight L S.a₁) S.ν)
    (hoptV : ∀ b, ∃ (W₀ : Finset (CTorus d L N₁ m₁ (k + 1)))
      (E₀ : Finset (CTorus d L N₁ m₁ (k + 1) × CTorus d L N₁ m₁ (k + 1))),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ XV b) ∧ MeetsOne m₀ (jV b) (𝒦XV b) W₀ ∧
        bondCost (scaleW L m₀ m₁ (jV b)) E₀ = treeLenCovOne m₀ (jV b) (XV b))
    (hΔV : ∀ b, treeLenCovOne m₀ (jV b) (XV b) = 0)
    {κdec κ₀ : ℝ} (hκ₀ : 0 ≤ κ₀) (hκdec : 3 * κ₀ + 3 ≤ κdec)
    (hκ : 4 * d * (((2 * L + 1) ^ d : ℕ) : ℝ) * κdec ≤ κ) (h1 : 1 ≤ (κ / 2 - 1) / 2)
    (hlog : Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) * (((L ^ m₀) ^ d : ℕ) : ℝ)) ≤ (κ / 2 - 1) / 2)
    (hZV : ∀ b, readSites (stepG d L N₁ m₁ k ϱ) k b ⊆ ↑(X₁V b))
    (hmarV : ∀ b, BlockMargin S.G' (X₁V b)
      (↑(blockSites d L N₁ m₁ (k + 1) k b) : Set (CTorus d L N₁ m₁ (k + 1))))
    (hL : 2 ≤ L) (ha₁ : 0 < S.a₁) (hc7 : c7 d L N BG κ ≤ thm73C3 d L N) {R : ℝ} (hR : 2 ≤ R)
    (hRs : R * δ₁ ≤ deltaStar d L N) (hsmall : cK2 d L N * (R * δ₁) < bgC0 d L N / 2)
    (hnum : cK2 d L N * δ₁ ≤ c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8))
    (hnum' : cK2' d L N (famConst d L BG₂ κ) * δ₁ ≤
      c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8))
    (hD : XiCData S.G' S.a S.ν (k + 1) 1 eps S.D') (hβ : 0 < S.β) (hp₁ : 0 ≤ S.p₁)
    {R₁ r t₁ t₀ : ℝ} (hR₁ : 1 < R₁) (hr : 0 < r) (ht₁ : 0 < t₁) (ht₀ : 0 < t₀)
    (x : S.E) (hx : ‖x‖ ≤ S.p₁) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1)
    (hrad : (‖(s : ℂ)‖ + t₀) * markedRad d L N k S.a₁ κ S.p₁
      (((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) < δ₁)
    (hdisc : ∀ t : ℂ, ‖t‖ < t₁ → ∀ σ : ℂ, ‖σ‖ < R₁ + r →
      σ • (liftC S.hG' ((s : ℂ) • S.shiftUC x) + t • liftC S.hG' (S.maskUC z (S.shiftUC x))) ∈
        FlBall (stepG d L N₁ m₁ k ϱ) δ₁)
    (hMR : S.MarkRealAt δ₁ R x) :
    ∃ (F₁ : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) →
        DecParams S.G' × RawData d L (N₁ * L ^ m₁) (k + 1) N →
          (S.G'.Ω 1 × Fin N → ℂ) × (S.G'.Ω 1 → ℂ))
      (Sol : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) →
        Dec2.DecParams (coverOf S.G') × Edat (stepG d L N₁ m₁ k ϱ) N →
          ((stepG d L N₁ m₁ k ϱ).Ω 1 × Fin N → ℂ) × ((stepG d L N₁ m₁ k ϱ).Ω 1 → ℂ)),
      deriv (fun t : ℂ => ∑ b : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))),
        markedFunDec S.hG' ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) S.a₁ S.ν BG₂ κ (S.blockU z)
          (s : ℂ) t (blockEnergyFun S.G' (stepG d L N₁ m₁ k ϱ) (compWeight L S.a₁) S.ν k b)
          S.D' (yhat x)) 0 =
        ∑ Y' ∈ bridgeFamily m₀ (fun _ => Set.univ)
            (fun b => polyDom S.G' (X₁V b) m₀ (jV b) (𝒦XV b)) z,
          markedOutDec m₀ (fun _ => Set.univ)
            (fun b => polyDom S.G' (X₁V b) m₀ (jV b) (𝒦XV b)) z
            (evDecFam X₁V jV 𝒦XV m₀ S.a₁ S.ν S.hG' ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) F₁ Sol
              (S.blockU z) (s : ℂ) (rawOf S.D', yhat x)) Y' ∧
      (fderiv ℂ (S.Phi1C (zeroClass d L N₁ m₁ k N ϱ)) ((s : ℂ) • S.shiftUC x))
          (S.maskUC z (S.shiftUC x)) =
        -(S.β : ℂ) * ∑ Y' ∈ bridgeFamily m₀ (fun _ => Set.univ)
            (fun b => polyDom S.G' (X₁V b) m₀ (jV b) (𝒦XV b)) z,
          markedOutDec m₀ (fun _ => Set.univ)
            (fun b => polyDom S.G' (X₁V b) m₀ (jV b) (𝒦XV b)) z
            (evDecFam X₁V jV 𝒦XV m₀ S.a₁ S.ν S.hG' ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) F₁ Sol
              (S.blockU z) (s : ℂ) (rawOf S.D', yhat x)) Y' +
        ((S.β : ℂ) / 2) * deriv (fun t : ℂ =>
          deltaForm (S.hG.precedes S.hG' (le_refl (k + 1))) (compWeight L S.a₁) S.ν
            (bgMultC S.G' (compWeight L S.a₁) S.ν (bgC0 d L N) S.D')
            (bgFieldC S.G' (compWeight L S.a₁) S.ν (bgC0 d L N) S.D')
            (liftC S.hG' (S.markedTangentC z (s : ℂ) t x))) 0 := by
  obtain ⟨F₁, Sol, -, -, hcnt⟩ := marked_count_scaled_dec_resummed (Gp := S.G')
    (Hm := stepG d L N₁ m₁ k ϱ) hC hk S.hG S.hG' ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) hp₁
    (S.blockU z) hMX hdm hα hsm hcovV hX₁V hconn hrow hoptV hΔV hκ₀ hκdec hκ h1 hlog hZV hmarV
    hL z (fun p hp y hy => S.blockU_supported z hp y hy)
  obtain ⟨⟨hd1, hd2, hd3⟩, -⟩ := hcnt (s : ℂ) t₀ t₀ ht₀ le_rfl hrad S.D' hD (yhat x)
    (fun p => S.yhat_le_of_norm_le hx p)
  refine ⟨F₁, Sol, hd3, ?_⟩
  rw [S.fderiv_mask_eq_neg_beta_deriv_energy_add_delta z hC ha₁ hc7 hR hRs hsmall hnum hnum' hD hβ
    hR₁ hr ht₁ x hs hdisc hMR, hd3]

end Total

end StepSetting

end Balaban.Fluctuation
