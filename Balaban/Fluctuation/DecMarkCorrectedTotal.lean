/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Analysis.RayJetReal
public import Balaban.Analysis.RayJetMark
public import Balaban.Fluctuation.DecMarkTotal
public import Balaban.Fluctuation.MarkedCubicTaylor
public import Balaban.Fluctuation.InteractionPoly

/-!
# The corrected mark of the total

* `deltaForm_two`: the quadratic form `⟨ψ', Δ^{(k)} ψ'⟩` along `u a + t b` is
  `A u² + C u t + D t²`, with `A = δ(a)`, `D = δ(b)`, `C = δ(a + b) - δ(a) - δ(b)`.
* `mark_remainder_corrected_total`: let `g(u, t) = V^{(k)}(ψ^{(k)} + u ψ' + t M_z ψ')` be analytic
  at `0` with vanishing real ray jets of order one and two.  For
  `e = g + ½ ⟨ψ', Δ^{(k)} ψ'⟩` and `f(u) = ∂ₜ e(u, t)|ₜ₌₀` the first-order Taylor remainder
  `f u - f 0 - u f'(0)` equals `∂ₜ g(u, t)|ₜ₌₀`, and `DΦ₁(s ψ')[M_z ψ']` is `-β` times it.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Multiscale Balaban.Background Matrix

section Quad

variable {d L N₀ K N : ℕ} [NeZero N₀] [NeZero L] {ϱ ϱ' : ℝ}
variable {G : GeneratingSet d L N₀ K ϱ} {G' : GeneratingSet d L N₀ K ϱ'}

theorem pair_two (p q r s : G.Ω 1 × Fin N → ℂ) (u t u' t' : ℂ) :
    pair G (u • p + t • q) (u' • r + t' • s) =
      u * u' * pair G p r + u * t' * pair G p s + t * u' * pair G q r + t * t' * pair G q s := by
  unfold pair
  have h : ∀ i, (u • p + t • q) i * (u' • r + t' • s) i =
      u * u' * (p i * r i) + u * t' * (p i * s i) + t * u' * (q i * r i) + t * t' * (q i * s i) := by
    intro i; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
  simp_rw [h, Finset.sum_add_distrib, ← Finset.mul_sum]

/-- **T2.**  `⟨ψ', Δ^{(k)} ψ'⟩` along the plane `u a + t b` is `A u² + C u t + D t²`, where `A`, `D`
are its values at `a`, `b` and `C` is the associated bilinear form `δ(a + b) - δ(a) - δ(b)`. -/
theorem deltaForm_two (h : Precedes G G') (a : ℕ → ℝ) (ν : ℝ) (α₁ : G'.Ω 1 → ℂ)
    (φ₁ : G'.Ω 1 × Fin N → ℂ) (p q : Torus d (N₀ * L ^ K) → Fin N → ℂ) (u t : ℂ) :
    deltaForm h a ν α₁ φ₁ (fun x i => u * p x i + t * q x i) =
      deltaForm h a ν α₁ φ₁ p * u ^ 2 +
        (deltaForm h a ν α₁ φ₁ (fun x i => p x i + q x i) - deltaForm h a ν α₁ φ₁ p -
          deltaForm h a ν α₁ φ₁ q) * u * t + deltaForm h a ν α₁ φ₁ q * t ^ 2 := by
  classical
  set M := liftOp N (opHk h a ν α₁)⁻¹ - constrainedOp (opHk h a ν α₁)⁻¹ (fieldBase h φ₁) with hM
  have hphi : ∀ (S : G.Ω 1 × Fin N → ℂ), phiOne h a ν α₁ φ₁ S = M *ᵥ S := fun S => rfl
  have key : ∀ u t : ℂ, deltaForm h a ν α₁ φ₁ (fun x i => u * p x i + t * q x i) =
      u ^ 2 * (pair G (fun w => p w.1 w.2) (qStar G a p) - pair G (qStar G a p) (M *ᵥ qStar G a p)) +
      u * t * ((pair G (fun w => p w.1 w.2) (qStar G a q) + pair G (fun w => q w.1 w.2) (qStar G a p))
        - (pair G (qStar G a p) (M *ᵥ qStar G a q) + pair G (qStar G a q) (M *ᵥ qStar G a p))) +
      t ^ 2 * (pair G (fun w => q w.1 w.2) (qStar G a q) - pair G (qStar G a q) (M *ᵥ qStar G a q)) := by
    intro u t
    have hq : qStar G a (fun x i => u * p x i + t * q x i) = u • qStar G a p + t • qStar G a q := by
      funext w; simp only [qStar, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
    have hx : (fun w : G.Ω 1 × Fin N => (fun x i => u * p x i + t * q x i) w.1 w.2) =
        u • (fun w : G.Ω 1 × Fin N => p w.1 w.2) + t • (fun w : G.Ω 1 × Fin N => q w.1 w.2) := by
      funext w; simp
    unfold deltaForm
    rw [hx, hq, hphi, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, pair_two, pair_two]
    ring
  have h10 := key 1 0
  have h01 := key 0 1
  have h11 := key 1 1
  have e1 : (fun x i => (1 : ℂ) * p x i + 0 * q x i) = p := by funext x i; simp
  have e2 : (fun x i => (0 : ℂ) * p x i + 1 * q x i) = q := by funext x i; simp
  have e3 : (fun x i => (1 : ℂ) * p x i + 1 * q x i) = fun x i => p x i + q x i := by
    funext x i; simp
  rw [e1] at h10
  rw [e2] at h01
  rw [e3] at h11
  rw [key u t]
  generalize pair G (fun w => p w.1 w.2) (qStar G a p) - pair G (qStar G a p) (M *ᵥ qStar G a p) = A
    at *
  generalize (pair G (fun w => p w.1 w.2) (qStar G a q) + pair G (fun w => q w.1 w.2) (qStar G a p))
        - (pair G (qStar G a p) (M *ᵥ qStar G a q) + pair G (qStar G a q) (M *ᵥ qStar G a p)) = C
    at *
  generalize pair G (fun w => q w.1 w.2) (qStar G a q) - pair G (qStar G a q) (M *ᵥ qStar G a q) = D
    at *
  rw [h10, h01, h11]
  ring

end Quad


namespace StepSetting

open Filter Topology

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}
  (S : StepSetting d L N₁ m₁ k N ϱ) (z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))))

/-- **The first-order Taylor remainder of the mark of the total equals the mark of the potential.**
Let `g(u, t) = V^{(k)}(ψ^{(k)} + u ψ' + t M_z ψ')`, with `ψ' = shiftUC x`.  Suppose `g` is analytic
at `0` (`hAn`, the conclusion of `analyticAt_VkC_shift` at `0`), the base point and the real rays
`s ↦ ψ^{(k)} + s (u ψ' + t M_z ψ')` lie in the union domain (`hbase`, `hray0`).  Then for
`f(u) = ∂ₜ [g(u, t) + ½ ⟨ψ', Δ^{(k)} ψ'⟩(u, t)]|ₜ₌₀`,
`f u - f 0 - u f'(0) = ∂ₜ g(u, t)|ₜ₌₀`. -/
theorem mark_taylor1_corrected_total
    (ha₁ : 0 < S.a₁) (H : BgHyp d L (k + 1) ϱ S.a S.ν)
    (hD2 : InUnionDomainC S.G' (bgC0 d L N) (thm73C2 d L N) S.ν S.D')
    (hbase : InUnionDomainC (stepG d L N₁ m₁ k ϱ) (bgC0 d L N) (bgC2 d L N) S.ν
      (S.dataUC S.psi0C))
    (x : S.E)
    (hAn : AnalyticAt ℂ (fun y : S.EC => S.VkC (S.psi0C + y)) 0)
    (hray0 : ∀ u t : ℂ, ∀ᶠ s : ℝ in 𝓝 0, InUnionDomainC (stepG d L N₁ m₁ k ϱ) (bgC0 d L N)
      (bgC1 d L N) S.ν
      (S.dataUC (S.psiAtV ((s : ℝ) : ℂ) (u • S.shiftUC x + t • S.maskUC z (S.shiftUC x)))))
    (f : ℂ → ℂ)
    (hf : ∀ u : ℂ, f u = deriv (fun t : ℂ => S.VkC (S.psi0C + S.markedTangentC z u t x) +
      (1 / 2) * deltaForm (S.hG.precedes S.hG' (le_refl (k + 1))) (compWeight L S.a₁) S.ν
        (bgMultC S.G' (compWeight L S.a₁) S.ν (bgC0 d L N) S.D')
        (bgFieldC S.G' (compWeight L S.a₁) S.ν (bgC0 d L N) S.D')
        (liftC S.hG' (S.markedTangentC z u t x))) 0)
    (u : ℂ)
    (hu : DifferentiableAt ℂ (fun t : ℂ => S.VkC (S.psi0C + S.markedTangentC z u t x)) 0) :
    f u - f 0 - u * deriv f 0 =
      deriv (fun t : ℂ => S.VkC (S.psi0C + S.markedTangentC z u t x)) 0 := by
  set gp : ℂ × ℂ → ℂ := fun w =>
    S.VkC (S.psi0C + (w.1 • S.shiftUC x + w.2 • S.maskUC z (S.shiftUC x))) with hgp
  have hv := fun w : ℂ × ℂ => S.VkC_rayV_vanish_of_baseDomain ha₁ H hD2 hbase
    (w.1 • S.shiftUC x + w.2 • S.maskUC z (S.shiftUC x)) (hray0 w.1 w.2)
  set P := liftC S.hG' (S.shiftUC x) with hP
  set Q := liftC S.hG' (S.maskUC z (S.shiftUC x)) with hQ
  have hδ : ∀ u t : ℂ, deltaForm (S.hG.precedes S.hG' (le_refl (k + 1))) (compWeight L S.a₁) S.ν
        (bgMultC S.G' (compWeight L S.a₁) S.ν (bgC0 d L N) S.D')
        (bgFieldC S.G' (compWeight L S.a₁) S.ν (bgC0 d L N) S.D')
        (liftC S.hG' (S.markedTangentC z u t x)) =
      deltaForm (S.hG.precedes S.hG' (le_refl (k + 1))) (compWeight L S.a₁) S.ν
        (bgMultC S.G' (compWeight L S.a₁) S.ν (bgC0 d L N) S.D')
        (bgFieldC S.G' (compWeight L S.a₁) S.ν (bgC0 d L N) S.D') P * u ^ 2 +
      (deltaForm (S.hG.precedes S.hG' (le_refl (k + 1))) (compWeight L S.a₁) S.ν
        (bgMultC S.G' (compWeight L S.a₁) S.ν (bgC0 d L N) S.D')
        (bgFieldC S.G' (compWeight L S.a₁) S.ν (bgC0 d L N) S.D')
        (fun x i => P x i + Q x i) -
       deltaForm (S.hG.precedes S.hG' (le_refl (k + 1))) (compWeight L S.a₁) S.ν
        (bgMultC S.G' (compWeight L S.a₁) S.ν (bgC0 d L N) S.D')
        (bgFieldC S.G' (compWeight L S.a₁) S.ν (bgC0 d L N) S.D') P -
       deltaForm (S.hG.precedes S.hG' (le_refl (k + 1))) (compWeight L S.a₁) S.ν
        (bgMultC S.G' (compWeight L S.a₁) S.ν (bgC0 d L N) S.D')
        (bgFieldC S.G' (compWeight L S.a₁) S.ν (bgC0 d L N) S.D') Q) * u * t +
      deltaForm (S.hG.precedes S.hG' (le_refl (k + 1))) (compWeight L S.a₁) S.ν
        (bgMultC S.G' (compWeight L S.a₁) S.ν (bgC0 d L N) S.D')
        (bgFieldC S.G' (compWeight L S.a₁) S.ν (bgC0 d L N) S.D') Q * t ^ 2 := by
    intro u t
    rw [← deltaForm_two (S.hG.precedes S.hG' (le_refl (k + 1))) (compWeight L S.a₁) S.ν
      (bgMultC S.G' (compWeight L S.a₁) S.ν (bgC0 d L N) S.D')
      (bgFieldC S.G' (compWeight L S.a₁) S.ν (bgC0 d L N) S.D') P Q u t,
      S.liftC_markedTangentC z u t x]
    rfl
  set A := deltaForm (S.hG.precedes S.hG' (le_refl (k + 1))) (compWeight L S.a₁) S.ν
        (bgMultC S.G' (compWeight L S.a₁) S.ν (bgC0 d L N) S.D')
        (bgFieldC S.G' (compWeight L S.a₁) S.ν (bgC0 d L N) S.D') P with hA
  set C := (deltaForm (S.hG.precedes S.hG' (le_refl (k + 1))) (compWeight L S.a₁) S.ν
        (bgMultC S.G' (compWeight L S.a₁) S.ν (bgC0 d L N) S.D')
        (bgFieldC S.G' (compWeight L S.a₁) S.ν (bgC0 d L N) S.D')
        (fun x i => P x i + Q x i) -
       deltaForm (S.hG.precedes S.hG' (le_refl (k + 1))) (compWeight L S.a₁) S.ν
        (bgMultC S.G' (compWeight L S.a₁) S.ν (bgC0 d L N) S.D')
        (bgFieldC S.G' (compWeight L S.a₁) S.ν (bgC0 d L N) S.D') P -
       deltaForm (S.hG.precedes S.hG' (le_refl (k + 1))) (compWeight L S.a₁) S.ν
        (bgMultC S.G' (compWeight L S.a₁) S.ν (bgC0 d L N) S.D')
        (bgFieldC S.G' (compWeight L S.a₁) S.ν (bgC0 d L N) S.D') Q) with hC
  set D := deltaForm (S.hG.precedes S.hG' (le_refl (k + 1))) (compWeight L S.a₁) S.ν
        (bgMultC S.G' (compWeight L S.a₁) S.ν (bgC0 d L N) S.D')
        (bgFieldC S.G' (compWeight L S.a₁) S.ν (bgC0 d L N) S.D') Q with hD
  have hfe : f = fun u' : ℂ => deriv (fun t : ℂ => gp (u', t) +
      (A / 2 * u' ^ 2 + C / 2 * u' * t + D / 2 * t ^ 2)) 0 := by
    funext u'
    rw [hf u']
    congr 1
    funext t
    rw [hδ u' t]
    show S.VkC (S.psi0C + S.markedTangentC z u' t x) + _ = S.VkC (S.psi0C + S.markedTangentC z u' t x) + _
    ring
  have hT := mark_taylor1_add_of_real_rays (fun y : S.EC => S.VkC (S.psi0C + y))
    (S.shiftUC x) (S.maskUC z (S.shiftUC x)) hAn (fun w => (hv w).2.1) (fun w => (hv w).2.2)
    (A / 2) (C / 2) (D / 2) u hu
  rw [hfe]
  exact hT

/-- **The masked derivative of `Φ₁` is `-β` times the first-order Taylor remainder of the mark of
the total** (zero class, real `s`).  Under the hypotheses of `mark_taylor1_corrected_total`, with
`Φ₁ = Phi1C` complex differentiable at `s ψ'` and `β > 0`:
`DΦ₁(s ψ')[M_z ψ'] = -β (f s - f 0 - s f'(0))`. -/
theorem fderiv_mask_eq_neg_beta_taylor1_corrected_total
    (ha₁ : 0 < S.a₁) (H : BgHyp d L (k + 1) ϱ S.a S.ν)
    (hD2 : InUnionDomainC S.G' (bgC0 d L N) (thm73C2 d L N) S.ν S.D')
    (hbase : InUnionDomainC (stepG d L N₁ m₁ k ϱ) (bgC0 d L N) (bgC2 d L N) S.ν
      (S.dataUC S.psi0C))
    (x : S.E)
    (hAn : AnalyticAt ℂ (fun y : S.EC => S.VkC (S.psi0C + y)) 0)
    (hray0 : ∀ u t : ℂ, ∀ᶠ s : ℝ in 𝓝 0, InUnionDomainC (stepG d L N₁ m₁ k ϱ) (bgC0 d L N)
      (bgC1 d L N) S.ν
      (S.dataUC (S.psiAtV ((s : ℝ) : ℂ) (u • S.shiftUC x + t • S.maskUC z (S.shiftUC x)))))
    (f : ℂ → ℂ)
    (hf : ∀ u : ℂ, f u = deriv (fun t : ℂ => S.VkC (S.psi0C + S.markedTangentC z u t x) +
      (1 / 2) * deltaForm (S.hG.precedes S.hG' (le_refl (k + 1))) (compWeight L S.a₁) S.ν
        (bgMultC S.G' (compWeight L S.a₁) S.ν (bgC0 d L N) S.D')
        (bgFieldC S.G' (compWeight L S.a₁) S.ν (bgC0 d L N) S.D')
        (liftC S.hG' (S.markedTangentC z u t x))) 0)
    (hβ : 0 < S.β) (s : ℝ)
    (hd : DifferentiableAt ℂ (S.Phi1C (zeroClass d L N₁ m₁ k N ϱ)) ((s : ℂ) • S.shiftUC x)) :
    (fderiv ℂ (S.Phi1C (zeroClass d L N₁ m₁ k N ϱ)) ((s : ℂ) • S.shiftUC x))
        (S.maskUC z (S.shiftUC x)) = -(S.β : ℂ) * (f s - f 0 - (s : ℂ) * deriv f 0) := by
  have hβc : (S.β : ℂ) ≠ 0 := by exact_mod_cast hβ.ne'
  have hF := S.hasDerivAt_Phi1C_marked z (zeroClass d L N₁ m₁ k N ϱ) (s : ℂ) x hd
  simp_rw [S.Phi1C_zeroClass] at hF
  have hV : HasDerivAt (fun t : ℂ => S.VkC (S.psi0C + S.markedTangentC z (s : ℂ) t x))
      ((-(S.β : ℂ))⁻¹ * (fderiv ℂ (S.Phi1C (zeroClass d L N₁ m₁ k N ϱ)) ((s : ℂ) • S.shiftUC x))
        (S.maskUC z (S.shiftUC x))) 0 := by
    have := hF.const_mul ((-(S.β : ℂ))⁻¹)
    refine this.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
    simp only
    rw [← mul_assoc, inv_mul_cancel₀ (neg_ne_zero.2 hβc), one_mul]
  have hT := S.mark_taylor1_corrected_total z ha₁ H hD2 hbase x hAn hray0 f hf (s : ℂ) hV.differentiableAt
  rw [hT, hV.deriv, ← mul_assoc, mul_inv_cancel₀ (neg_ne_zero.2 hβc), one_mul]

end StepSetting

end Balaban.Fluctuation
