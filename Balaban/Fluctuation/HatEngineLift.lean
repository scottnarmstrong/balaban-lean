/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.StepObjects
public import Balaban.Localization.I5FluctFan
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The lift of a unit-lattice field to a layer-constant field

The variable of `decCovSqrt` is a field `v : unitPts G × Fin N → ℂ` on the unit lattice
`T^{(k)}_1`.  `liftC` lifts it to the fine torus, constant on the unit blocks; it is a linear map
(hence analytic), its values are layer constant on a level-`k` generating set `Hm`, a sup bound
`|v(b)| < δ₁` on the unit lattice gives membership in the ball `FlBallLC Hm δ₁`, and on real
fields it is the lift `liftU` of `StepObjects`, so that at `s ≡ 1` the fluctuation
`liftC (β_k^{-1/2} C^{1/2}(1) ψ̂)` is the step's `shiftU`.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization Finset Matrix

section Lift

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ ϱ' : ℝ}
  {G' : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ'}

/-- **The lift** of a complex field on the unit lattice to the fine torus (constant on the unit
blocks). -/
def liftC (hG' : IsLevel G' (k + 1)) :
    (unitPts G' × Fin N → ℂ) →ₗ[ℂ] (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) where
  toFun v x i := v (unitPt hG' x, i)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem liftC_apply (hG' : IsLevel G' (k + 1)) (v : unitPts G' × Fin N → ℂ)
    (x : CTorus d L N₁ m₁ (k + 1)) (i : Fin N) : liftC hG' v x i = v (unitPt hG' x, i) := rfl

/-- The lift as a continuous linear map (finite dimension). -/
noncomputable def liftCL (hG' : IsLevel G' (k + 1)) :
    (unitPts G' × Fin N → ℂ) →L[ℂ] (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) :=
  LinearMap.toContinuousLinearMap (liftC hG')

/-- **Analyticity of the lift**: it is linear, so a composition with an analytic map is analytic. -/
theorem analyticAt_liftC {Q : Type*} [NormedAddCommGroup Q] [NormedSpace ℂ Q] {q : Q}
    (hG' : IsLevel G' (k + 1)) {v : Q → unitPts G' × Fin N → ℂ}
    (hv : AnalyticAt ℂ v q) : AnalyticAt ℂ (fun p => liftC hG' (v p)) q :=
  ((liftCL hG').analyticAt (v q)).comp hv

theorem analyticOnNhd_liftC {Q : Type*} [NormedAddCommGroup Q] [NormedSpace ℂ Q] {S : Set Q}
    (hG' : IsLevel G' (k + 1)) {v : Q → unitPts G' × Fin N → ℂ}
    (hv : AnalyticOnNhd ℂ v S) : AnalyticOnNhd ℂ (fun p => liftC hG' (v p)) S :=
  fun q hq => analyticAt_liftC hG' (hv q hq)

/-- The lift is constant on the blocks of every layer of a level-`k` generating set. -/
theorem isLayerConstant_liftC {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ} (hG : IsLevel Hm k)
    (hG' : IsLevel G' (k + 1)) (v : unitPts G' × Fin N → ℂ) :
    IsLayerConstant Hm (liftC hG' v) := by
  intro n hn1 hnk x hx x' hx'
  have hnk' : n = k := by
    have h1 := Hm.layerIndex_eq hn1 hnk hx
    rw [(hG x).2] at h1
    exact h1.symm
  subst hnk'
  have hb : unitBlock x' = unitBlock x := GeneratingSet.mem_blk.1 hx'
  have hu : unitPt hG' x' = unitPt hG' x := Subtype.ext hb
  funext i
  simp only [liftC_apply, hu]

/-- **Sup bound in, ball membership out**: a field on the unit lattice with `|v(b)| < δ₁` at
every unit point lifts into `FlBallLC Hm δ₁`. -/
theorem liftC_mem_flBallLC {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ} (hG : IsLevel Hm k)
    (hG' : IsLevel G' (k + 1)) {δ₁ : ℝ} {v : unitPts G' × Fin N → ℂ}
    (hv : ∀ b : unitPts G', vn (fun i => v (b, i)) < δ₁) : liftC hG' v ∈ FlBallLC Hm δ₁ :=
  ⟨fun x _ => hv (unitPt hG' x), isLayerConstant_liftC hG hG' v⟩

/-- On real fields the lift is the real lift `liftU`. -/
theorem liftC_ofReal (hG' : IsLevel G' (k + 1)) (ψ : unitPts G' → Rn N) :
    liftC hG' (fun q => ((ψ q.1 q.2 : ℝ) : ℂ)) = fun x i => ((liftU hG' ψ x i : ℝ) : ℂ) := rfl

end Lift

section Step

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}
  (S : StepSetting d L N₁ m₁ k N ϱ)

/-- The complex fluctuation field `ψ' = β_k^{-1/2} C^{1/2} ψ̂`, on the unit lattice, for a complex
square root matrix `C` (the decoupled one at the parameters `s`). -/
noncomputable def StepSetting.hatField (C : Matrix (S.U × Fin N) (S.U × Fin N) ℂ)
    (ψh : S.U × Fin N → ℂ) : S.U × Fin N → ℂ :=
  ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) • (C *ᵥ ψh)

/-- **The composite at `s ≡ 1` is the step's `shiftU`**: if the square root matrix at `s ≡ 1`
is real (`IsRealMat S.covSqrt`, a property of the landed `S.covSqrt`), then for a real
fluctuation variable `ψ̂`, the lift of `β_k^{-1/2} C^{1/2}(1) ψ̂` is `liftU (shiftU ψ̂)`. -/
theorem liftC_hatField_covSqrt (hreal : IsRealMat S.covSqrt) (ψh : S.E) :
    liftC S.hG' (S.hatField S.covSqrt (fun q => ((ψh q.1 q.2 : ℝ) : ℂ))) =
      fun x i => ((liftU S.hG' (S.shiftU ψh) x i : ℝ) : ℂ) := by
  funext x i
  have h : S.hatField S.covSqrt (fun q => ((ψh q.1 q.2 : ℝ) : ℂ)) (unitPt S.hG' x, i) =
      (((S.shiftU ψh) (unitPt S.hG' x) i : ℝ) : ℂ) := by
    simp only [StepSetting.hatField, Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct,
      StepSetting.shiftU, StepSetting.K, matMap_apply, PiLp.smul_apply]
    push_cast
    congr 1
    refine Finset.sum_congr rfl fun q _ => ?_
    have := hreal (unitPt S.hG' x, i) q
    rw [Matrix.map_apply]
    rw [Complex.conj_eq_iff_re] at this
    rw [this]
  exact h

end Step

end Balaban.Fluctuation
