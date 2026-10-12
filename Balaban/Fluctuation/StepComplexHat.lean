/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.StepComplex
public import Balaban.Fluctuation.InteractionHatV
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The shift of the hat engine is the substitution (2.7) of the complex step (RAY-CHART (3.2))

The `ψ̂`-local expansions (`HatEngine*`, `InteractionHat*`) attach to a hat variable `ψ̂` the
fluctuation field `hatLift … cc D ψ̂ = liftC (cc • C^{1/2}(1) ψ̂)`, with `C^{1/2}(1) = hatCovSqrt`
the decoupled square root at the complex background `(bgFieldC, bgMultC)` of the datum `D`, and,
with the cover parameters `s`, `hatPsiF … F₁ s Θ ψ̂`.  For every step datum, real or complex:

* `covSqrtC_eq_hatCovSqrt`: the matrix `covSqrtC` of the complex step is `hatCovSqrt` (no
  hypothesis);
* `hatLift_eq_liftC`, `liftC_shiftUC`: with `cc = β_k^{-1/2}`, the lift of the hat engine is the
  lift of `shiftUC` (no hypothesis);
* `hatPsiF_one_eq_liftC_shiftUC`: the decoupled lift at `s ≡ 1`, for a datum of
  `Ξ^c(𝔹_{k+1}; 1, ε)` under `FlCore` (the domain of the engine);
* `liftC_shiftUC_mem_flBallLC`: the sup bound (RAY-CHART (3.5)) for the shift of the complex step.

`RAY-CHART` (3.2) (`liftC_hatField_covSqrt`) has this identification for the landed real `shiftU`
on the real chart only; `StepComplexAgree.shiftUC_eq` is the comparison of the two shifts there.
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Analysis
  Balaban.Fluctuation Finset Matrix

section One

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱm : ℝ}
variable {Gp : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
variable {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}
variable {a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁ : ℝ}

/-- **The decoupled background at `s ≡ 1` of a datum of `Ξ^c(𝔹_{k+1}; 1, ε)` is the complex small
solution** `(bgFieldC, bgMultC)` (Theorem I-4b (i) at `s = 1`), and the datum lies in the union
domain `𝒟` with `c₁ = c₇`. -/
theorem isDecBg_one_of_xiCData (hC : FlCore N Gp Hm a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
    {D : BgData Gp N} (hD : XiCData Gp (compWeight L a₁) ν (k + 1) 1 eps D) :
    IsDecBg Gp (compWeight L a₁) ν (rho4 d L N BG κ) (fun _ => 1) D
        (bgFieldC Gp (compWeight L a₁) ν (bgC0 d L N) D)
        (bgMultC Gp (compWeight L a₁) ν (bgC0 d L N) D) ∧
      InUnionDomainC Gp (bgC0 d L N) (c7 d L N BG κ) ν D := by
  have hd0 : 0 < d := by have := hC.HBp.hd; omega
  have hc1 := one_le_xiC1 d
  have hε := hC.eps_pos
  have hδ0 : 0 < xiC1 d * eps := by positivity
  have hE1 : 1 < Real.exp κ := Real.one_lt_exp_iff.2 hC.hκ
  have hs : ∀ P, ‖(fun _ : ↥(cubeIdx Gp) => (1 : ℂ)) P‖ ≤ Real.exp κ := fun P => by
    simpa using hE1.le
  have hDom := xiCData_inDomainC hC.HBp hC.small1 hD
  have hδ1 : xiC1 d * eps ≤ c7 d L N BG κ := hC.c7le
  have hδ0' : xiC1 d * eps ≤ bgC0 d L N := hδ1.trans ((c7_le_bgC1 d L N BG κ).trans
    (bgC1_le_bgC0 d L N hd0))
  have hνε : ν * ((L : ℝ) ^ (k + 1)) ^ 2 * (xiC1 d * eps) ^ 2 ≤ (xiC1 d * eps) ^ 2 := by
    have := hC.HBp.massLe; nlinarith [sq_nonneg (xiC1 d * eps)]
  obtain ⟨φ, α, hI, -⟩ := i4b_exists_unique hC.hS hC.Sp hC.HBp hC.hκ.le hC.hM hs hδ0 le_rfl hδ0'
    hδ1 hνε hDom
  obtain ⟨-, hφ1, hα1⟩ := i4b_one hC.hS hC.Sp hC.HBp hC.hκ.le hC.hM hδ0 le_rfl hδ0' hδ1
    hνε hDom hI
  rw [hφ1, hα1]
  exact ⟨hI, inUnionDomainC_of_inDomainC hC.HBp hδ0 hδ0' hδ1 hDom⟩

/-- **The decoupled lift at `s ≡ 1` is `hatLift`**: for a datum of `Ξ^c(𝔹_{k+1}; 1, ε)` and a
function `F₁` returning the decoupled background (the `F₁` of `i4b_analytic`),
`hatPsiF … F₁ 1 (rawOf D) ψ̂ = hatLift … D ψ̂`. -/
theorem hatPsiF_one_eq_hatLift (hC : FlCore N Gp Hm a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
    (hG' : IsLevel Gp (k + 1)) (cc : ℂ)
    {F₁ : DecParams Gp × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      (Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)}
    (hF₁ : ∀ (s : DecParams Gp) (D : BgData Gp N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC Gp (bgC0 d L N) (c7 d L N BG κ) ν D → ∀ (φ : Gp.Ω 1 × Fin N → ℂ)
        (α : Gp.Ω 1 → ℂ), IsDecBg Gp (compWeight L a₁) ν (rho4 d L N BG κ) s D φ α →
        F₁ (s, rawOf D) = (φ, α))
    {D : BgData Gp N} (hD : XiCData Gp (compWeight L a₁) ν (k + 1) 1 eps D)
    (ψh : unitPts Gp × Fin N → ℂ) :
    hatPsiF Gp a₁ ν hG' cc F₁ (fun _ => 1) (rawOf D) ψh = hatLift Gp a₁ ν hG' cc D ψh := by
  obtain ⟨hI, hU⟩ := isDecBg_one_of_xiCData hC hD
  have hE1 : 1 < Real.exp κ := Real.one_lt_exp_iff.2 hC.hκ
  have hs : ∀ P, ‖(fun _ : ↥(cubeIdx Gp) => (1 : ℂ)) P‖ < Real.exp κ := fun P => by simpa using hE1
  have hFeq := hF₁ _ D hs hU _ _ hI
  unfold hatPsiF hatSqrtF hatLift hatCovSqrt
  rw [hFeq, extS_one]
  rfl

end One

end Balaban.Localization

namespace Balaban.Fluctuation

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Localization
  Finset Matrix

namespace StepSetting

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ ϱm : ℝ}
  (S : StepSetting d L N₁ m₁ k N ϱ)

/-- **The square root of the complex step is the square root of the hat engine**, at every datum:
`covSqrtC = hatCovSqrt` (on the whole-lattice generating set the extension `φ̄ = barField` of the
background by the datum is the background itself). -/
theorem covSqrtC_eq_hatCovSqrt : S.covSqrtC = hatCovSqrt S.G' S.a₁ S.ν S.D' := by
  have hb : barField S.G' S.D'.Ψ (bgFieldC S.G' S.a S.ν (bgC0 d L N) S.D') =
      svec S.G' (bgFieldC S.G' S.a S.ν (bgC0 d L N) S.D') := by
    funext x i
    exact barField_eq_svec S.hG' _ _ x i
  unfold covSqrtC hatCovSqrt
  rw [hb]

/-- **The lift of the hat engine at a complex hat variable** is the lift of `cc • C^{1/2} ψ̂` with
the square root `covSqrtC` of the complex step, at every datum. -/
theorem hatLift_eq_liftC (cc : ℂ) (ψh : S.EC) :
    hatLift S.G' S.a₁ S.ν S.hG' cc S.D' ψh = liftC S.hG' (cc • (S.covSqrtC *ᵥ ψh)) := by
  unfold hatLift
  rw [S.covSqrtC_eq_hatCovSqrt]

/-- **The shift of the `ψ̂`-local expansion is `shiftUC`**, at every (real or complex) datum: with
`cc = β_k^{-1/2}` and the real fluctuation variable `ψ̂` complexified, `hatLift` is the lift of the
substitution (2.7) of the complex step.  (`RAY-CHART` (3.2), without the restriction to the real
chart.) -/
theorem liftC_shiftUC (x : S.E) :
    liftC S.hG' (S.shiftUC x) =
      hatLift S.G' S.a₁ S.ν S.hG' ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) S.D' (yhat x) :=
  (S.hatLift_eq_liftC _ _).symm

variable {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm} {c BG κ eps Kc Cx c₂ BG₂ δ₁ : ℝ}

/-- **The decoupled lift of the hat engine at `s ≡ 1` is the lift of `shiftUC`**, for a complex
datum of `Ξ^c(𝔹_{k+1}; 1, ε)` under `FlCore` (the domain of the engine), `F₁` the decoupled
background of `i4b_analytic`. -/
theorem hatPsiF_one_eq_liftC_shiftUC
    (hC : FlCore N S.G' Hm S.a₁ S.ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
    {F₁ : DecParams S.G' × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      (S.G'.Ω 1 × Fin N → ℂ) × (S.G'.Ω 1 → ℂ)}
    (hF₁ : ∀ (s : DecParams S.G') (D : BgData S.G' N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC S.G' (bgC0 d L N) (c7 d L N BG κ) S.ν D → ∀ (φ : S.G'.Ω 1 × Fin N → ℂ)
        (α : S.G'.Ω 1 → ℂ), IsDecBg S.G' (compWeight L S.a₁) S.ν (rho4 d L N BG κ) s D φ α →
        F₁ (s, rawOf D) = (φ, α))
    (hD : XiCData S.G' S.a S.ν (k + 1) 1 eps S.D') (x : S.E) :
    hatPsiF S.G' S.a₁ S.ν S.hG' ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) F₁ (fun _ => 1)
        (rawOf S.D') (yhat x) = liftC S.hG' (S.shiftUC x) := by
  rw [hatPsiF_one_eq_hatLift hC S.hG' _ hF₁ hD, S.liftC_shiftUC]

/-- **The sup bound of the shift of the complex step** (RAY-CHART (3.5)): for a complex datum of
`Ξ^c(𝔹_{k+1}; 1, ε)` under `FlCore` and the margins of the covariance chart, and a fluctuation
variable in the support of `ν_{p₁}` (`χ_fl(ψ̂) = 1`), the lift of `shiftUC ψ̂` lies in the ball
`FlBallLC Hm δ₁` as soon as `√N β_k^{-1/2} C_sup p₁ < δ₁`. -/
theorem liftC_shiftUC_mem_flBallLC
    (hC : FlCore N S.G' Hm S.a₁ S.ν c BG κ eps Kc Cx c₂ BG₂ δ₁) (hG : IsLevel Hm k)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δc : ℝ}
    (hdm : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4) (hβ : 0 ≤ S.β) (hp₁ : 0 < S.p₁)
    (hδ₁ : Real.sqrt N * (S.betaU ^ (-(1 / 2 : ℝ)) *
      (covSupConstC d L N (compWeight L S.a₁ k) κ * S.p₁)) < δ₁)
    (hD : XiCData S.G' S.a S.ν (k + 1) 1 eps S.D') {x : S.E} (hx : chiFl S.U N S.p₁ x = 1) :
    liftC S.hG' (S.shiftUC x) ∈ FlBallLC Hm δ₁ := by
  have hβU : 0 ≤ S.betaU := by unfold betaU; positivity
  have hβ0 : 0 ≤ S.betaU ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hβU _
  rw [S.liftC_shiftUC]
  refine hatLift_mem_flBallLC hC S.hk1 hG S.hG' _ hp₁.le hMX hdm hα hsm ?_ hD (ψh := yhat x)
    fun p => ?_
  · rwa [Complex.norm_real, Real.norm_of_nonneg hβ0]
  · rw [chiFl_eq_one_iff hp₁] at hx
    show ‖((x p.1 p.2 : ℝ) : ℂ)‖ ≤ S.p₁
    rw [Complex.norm_real]
    exact ((PiLp.norm_apply_le (x p.1) p.2).trans (norm_le_pi_norm x p.1)).trans hx.le

end StepSetting

end Balaban.Fluctuation
