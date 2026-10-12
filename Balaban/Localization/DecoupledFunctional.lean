/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.DecoupledIdentMain
public import Balaban.Localization.DecoupledSpectral
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# I-4c (iv): `C^{1/2}(1) = 𝒜^{-1/2}` and `𝕃(1) = log 𝒜`

At `s ≡ 1` the decoupled covariance is `C_x(1) = (x + 𝒜)⁻¹` (`decCov_one_eq`). If `𝒜 =
a L⁻² Q*Q + Δ^{(k)}` is positive definite (GREEN.md G-1(b),(d): the positivity of the constrained
operator), the resolvent integrals of `Balaban/Localization/DecoupledSpectral.lean` identify

* `decCovSqrt = invSqrtMat 𝒜`, the positive inverse square root (`decCovSqrt_one_eq`);
* `decLog = specFun 𝒜 log`, the logarithm of `𝒜` (`decLog_one_eq`).
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background Finset Matrix MeasureTheory Set
open scoped ComplexOrder

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
variable {G : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ} {a : ℕ → ℝ} {aT ν : ℝ}
  {α : G.Ω 1 → ℂ} {δ : ℝ} {φ : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ}
  {κι : Type*} [Fintype κι] [DecidableEq κι] {Q : Matrix κι (G.Ω 1) ℂ} {P : Matrix κι κι ℂ}

/-- **I-4c (iv), the square root.** If `𝒜` is positive definite then `C^{1/2}(1) = 𝒜^{-1/2}`. -/
theorem decCovSqrt_one_eq (hfam : ∀ x, 0 ≤ x → XData G a aT ν x α 0 (fun _ => 1))
    (hφ : IsConstraintField G δ φ) (hδ : 0 ≤ δ) (hsm : δ ^ 2 * smallConstX d L 0 ≤ 1 / 4)
    (hU : IsUnitLatticeB G Q P) (hPD : (covOp G a aT ν α φ Q P).PosDef) :
    decCovSqrt G a aT ν α (fun _ => 1) φ Q P = invSqrtMat hPD := by
  rw [← resolvent_sqrt_eq hPD]
  unfold decCovSqrt
  congr 1
  ext p q
  unfold intMat
  refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
  simp only [decSqrtInt]
  rw [(decCov_one_eq hfam hφ hδ hsm hU (mem_Ioi.mp hx).le).2]

/-- **I-4c (iv), the logarithm.** If `𝒜` is positive definite then `𝕃(1) = log 𝒜`. -/
theorem decLog_one_eq (hfam : ∀ x, 0 ≤ x → XData G a aT ν x α 0 (fun _ => 1))
    (hφ : IsConstraintField G δ φ) (hδ : 0 ≤ δ) (hsm : δ ^ 2 * smallConstX d L 0 ≤ 1 / 4)
    (hU : IsUnitLatticeB G Q P) (hPD : (covOp G a aT ν α φ Q P).PosDef) :
    decLog G a aT ν α (fun _ => 1) φ Q P =
      specFun hPD.isHermitian (fun t => (Real.log t : ℂ)) := by
  have D0 := hfam 0 le_rfl
  have hak : 0 < a k := by
    have := D0.st.ha k D0.st.hk le_rfl
    linarith [this.1]
  have hb : 0 ≤ aT / (L : ℝ) ^ 2 := by
    have := D0.st.haT1
    positivity
  have hc2 : 0 < a k + aT / (L : ℝ) ^ 2 := by linarith
  have hlog := resolvent_log hPD hak hc2 (liftOp N P)
  have hcov : ∀ x : ℝ, covA (a k) (aT / (L : ℝ) ^ 2) x (liftOp N P) =
      blockFun (a k) (a k + aT / (L : ℝ) ^ 2) (liftOp N P) (fun t => ((t : ℂ) + x)⁻¹) := by
    intro x
    unfold covA blockFun
    push_cast
    ring_nf
  have hmat : intMat (volume.restrict (Ioi (0 : ℝ)))
      (fun x => decCov G a aT x ν α (fun _ => 1) φ Q P -
        covA (a k) (aT / (L : ℝ) ^ 2) x (liftOp N P)) =
      intMat (volume.restrict (Ioi (0 : ℝ)))
        (fun x => ((x : ℂ) • (1 : Matrix (κι × Fin N) (κι × Fin N) ℂ) +
          covOp G a aT ν α φ Q P)⁻¹ -
          blockFun (a k) (a k + aT / (L : ℝ) ^ 2) (liftOp N P) (fun t => ((t : ℂ) + x)⁻¹)) := by
    ext p q
    unfold intMat
    refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
    simp only []
    rw [(decCov_one_eq hfam hφ hδ hsm hU (mem_Ioi.mp hx).le).2, hcov]
  rw [← hlog]
  unfold decLog
  rw [hmat]
  rfl

end Balaban.Localization
