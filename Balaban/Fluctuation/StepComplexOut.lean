/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.StepComplexNonvanish
public import Balaban.Fluctuation.StepComplexExponent
public import Balaban.Fluctuation.CovarianceComplex
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The output side of the step at a complex block datum (FLUCTUATION.md §2.6; P4 (2.36)-(2.63))

`StepComplex` defines the input side of the step at a complex block datum `θ` (the exponents
`WoneC`, `WtwoC` of the measures `μ_{s,t}` and the partition functions `ZstC`, built on the complex
small solution `(bgFieldC, bgMultC)`).  This file defines the output side, the holomorphic
counterparts of the objects of `StepObjects` that Proposition 2.6 relates, in parallel with the
landed definitions (which are the objects of a real `θ` only, and are not changed):

* `covAC` (`𝒜 = a L⁻² Q*Q + Δ^{(k)}`), `logAC` (`𝕃 = log 𝒜`), `halfLogDetCC`
  (`½ log det C^{(k)} = -½ ∑_y tr 𝕃(y,y)`, the analytic branch);
* `AnewC`, `AoldC` (the actions with the bilinear product, `actionC`), `tKernelC` (the kernel
  `∏ t_k` with the bilinear product), `rhoExpC` (the exponential of the density `ρ_k` of (H.1)),
  `TstepC` (the fluctuation integral after the substitution (2.7));
* `E1C`, `E0C`, `F0C`, `M0C` (`ℰ₁^{(k+1)}`, `ℰ₀^{(k+1)}`, `ℱ₀^{(k+1)}`, `ℳ₀^{(k+1)}` of (2.8), (2.9),
  P4 (2.53)), `Phi1C`, `maskUC`, `E1locC`, `E0locC` (the localized forms, P4 (2.56)-(2.60));
* `WoneCT`, `WtwoCT`, `dECT` (truncations to the support of `ν_{p₁}`), `PconstC`, and the
  regularity inputs `StepRegularC`, `ClassRegularC` (the forms of `StepRegular`, `ClassRegular` for
  the exponents of the complex step).

The real vacuum constants `E'_k, E''_k, E'''_k` (`Ep`, `Epp`, `Eppp`), the measure `ν_{p₁}` and the
numbers `β_k`, `|T^{(k)}_1|` do not depend on the datum and are those of `StepObjects`.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban.SmallField.Def6 Balaban.Background Balaban.Multiscale Balaban.Localization
  Balaban.SmallField Finset Matrix

namespace StepSetting

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}
  (S : StepSetting d L N₁ m₁ k N ϱ) (C : StepClass d L N₁ m₁ k N ϱ)

/-! ### The covariance operator, its logarithm, and `½ log det C^{(k)}` -/

/-- **`𝒜 = a L⁻² Q*Q + Δ^{(k)}` at a complex datum** (Lemma 2.4; P4 (2.24)-(2.25)), so that
`C^{(k)} = 𝒜⁻¹`: the operator `covOp` at the complex background
`(φ_{k+1}, α_{k+1}) = (bgFieldC, bgMultC)` of `θ`.  It is `covA` with `bgField`, `bgMult` replaced
by `bgFieldC`, `bgMultC`. -/
noncomputable def covAC : Matrix (S.U × Fin N) (S.U × Fin N) ℂ :=
  covOp S.G' S.a S.a₁ S.ν (bgMultC S.G' S.a S.ν (bgC0 d L N) S.D')
    (svec S.G' (bgFieldC S.G' S.a S.ν (bgC0 d L N) S.D')) (unitQ S.G') (unitP S.G')

/-- **`𝕃 = log (a L⁻² Q*Q + Δ^{(k)})` at a complex datum** (Lemma 2.4 (c); P4 (2.58)), as a matrix
on `T^{(k)}_1 × [N]`: the decoupled logarithm `decLog` at `s = 1` and at the complex background of
`θ`.  It is `logA` with `bgField`, `bgMult` replaced by `bgFieldC`, `bgMultC`.

`decLog` at `s = 1` is the resolvent integral `-∫₀^∞ ((x + 𝒜)⁻¹ - (1 + x)⁻¹) dx = logMat 𝒜`
(`decLog_one_eq_logMat`), the principal logarithm of `𝒜` (`decLog_one_principal`: `exp 𝕃 = 𝒜`, `𝕃`
commutes with `𝒜`, its eigenvalues have imaginary part in `(-π, π)`); its entries are analytic in
the background (`analyticOnNhd_decLog_entry`). -/
noncomputable def logAC : Matrix (S.U × Fin N) (S.U × Fin N) ℂ :=
  decLog S.G' S.a S.a₁ S.ν (bgMultC S.G' S.a S.ν (bgC0 d L N) S.D') (fun _ => 1)
    (svec S.G' (bgFieldC S.G' S.a S.ν (bgC0 d L N) S.D')) (unitQ S.G') (unitP S.G')

/-- **`½ log det C^{(k)}` at a complex datum**: the branch `-½ ∑_y tr 𝕃(y,y)` of Lemma 2.4 (c),
(2.8) and P4 (2.58), with `𝕃 = logAC` the principal logarithm of `𝒜`.

This is the holomorphic counterpart of `halfLogDetC = ½ Real.log (det C^{(k)}).re`.  It is a
logarithm of the determinant, `exp (2 · halfLogDetCC) = det C^{(k)}` and
`exp halfLogDetCC = det C^{(k)1/2}` (`det_covSqrtC`), it is analytic in the background (a finite sum
of entries of `decLog`), and for a real datum it is the real number `halfLogDetC`
(`halfLogDetCC_eq`, from `halfLogDetC_eq_trace`): it is the analytic continuation of the real
`½ log det C^{(k)}`.  No branch of `Complex.log` is chosen. -/
noncomputable def halfLogDetCC : ℂ :=
  -(1 / 2 : ℂ) * ∑ y : S.U, ∑ i : Fin N, S.logAC (y, i) (y, i)

/-! ### The actions, the Gaussian kernel and the density at complex fields -/

/-- **`A^η_{k+1}(θ, φ_{k+1}(θ))` at a complex datum**: the action of the new level with the bilinear
product (`actionC`) at the complex small solution `φ_{k+1}(θ) = bgFieldC`.  It is `Anew` with
`action`, `bgField` replaced by `actionC`, `bgFieldC`. -/
noncomputable def AnewC : ℂ :=
  actionC S.G' S.a S.ν S.D' (bgFieldC S.G' S.a S.ν (bgC0 d L N) S.D')

/-- **`A_k(ψ, φ_k(ψ))` at a complex old spin `ψ`**: the Background action with the bilinear product
at the complex small solution `φ_k(ψ) = bgFieldC (dataUC ψ)`.  It is `Aold` with `action`,
`bgField`, `dataU` replaced by `actionC`, `bgFieldC`, `dataUC`. -/
noncomputable def AoldC (ψ : S.EC) : ℂ :=
  actionC (stepG d L N₁ m₁ k ϱ) S.a S.ν (S.dataUC ψ)
    (bgFieldC (stepG d L N₁ m₁ k ϱ) S.a S.ν (bgC0 d L N) (S.dataUC ψ))

/-- **The kernel `∏_{z ∈ T^{(k+1)}_L} t_k(θ(z), (Qψ)(z))` at complex `θ`, `ψ`** (Definition 2.1:
`t_k(ϑ, w) = (c/2π)^{N/2} exp (-(c/2) (ϑ - w)·(ϑ - w))` for `ϑ, w ∈ ℂ^N`, with the bilinear
product): `(c/2π)^{N |T^{(k+1)}|/2} exp (-β ½ a₁ L^{-2(k+1)} ∑_x (θ - Q_{k+1} ψ)·(θ - Q_{k+1} ψ))`.
It is `tKernel` with `coupling`, `dataU` replaced by `couplingC`, `dataUC`. -/
noncomputable def tKernelC (ψ : S.EC) : ℂ :=
  (((S.cKernel / (2 * Real.pi)) ^ ((N : ℝ) * S.nBlocks / 2) : ℝ) : ℂ) *
    Complex.exp (-((S.β : ℂ) * couplingC S.G' S.a₁ (k + 1) S.D'.Ψ (S.dataUC ψ).Ψ))

/-- **The exponential of the density `ρ_k` of (H.1) at a complex old spin `ψ`**:
`exp [-β_k A_k(ψ, φ_k(ψ)) + ℰ_k(ψ) - E_k |T^{(k)}_1| + ℱ_k(ψ, g)]` with the complex backgrounds
(`AoldC`, `EcompAtC`, `FcompAtC`).  It is `rhoStep` without the characteristic function `χ_k`,
which is a function of real fields only (in `TstepC` it is `1`, Lemma 2.5). -/
noncomputable def rhoExpC (g : Fld d L N₁ m₁ (k + 1) N) (ψ : S.EC) : ℂ :=
  Complex.exp (-(S.β : ℂ) * S.AoldC ψ +
    EcompAtC C.m₀ C.Tm S.a S.ν (Nat.le_succ k) (S.dataUC ψ) - (C.Ek : ℂ) * (S.nU : ℂ) +
    FcompAtC C.m₀ C.Tm S.a S.ν (Nat.le_succ k) (S.dataUC ψ) g)

/-- **The fluctuation integral `(T^{(k)} χ^{(k)} ρ_k)(θ)` at a complex block datum** (Definition
2.1 after the substitution (2.7); P4 (2.36)-(2.40)): the integral of `∏ t_k · ρ_k` over the old
spin `ψ` along the contour `ψ = ψ^{(k)}(θ) + β_k^{-1/2} C^{(k)1/2}(θ) ψ̂`, `ψ̂ ∈ (ℝ^N)^{T^{(k)}_1}`,
with the holomorphic volume element `dψ = β_k^{-N|T^{(k)}_1|/2} det C^{(k)1/2} dψ̂` of (2.7), and
with `χ_fl(ψ̂)` for the product `χ^{(k)} χ_k` of the characteristic functions (Lemma 2.5: on
`{χ_{k+1,u} = 1}` the two are equal; `χ_{(2.2)}`, `χ_k` are functions of real fields only, and the
continuation in `θ` is taken at fixed `ψ̂`).

For a real `θ` the contour is `(ℝ^N)^{T^{(k)}_1}` and this is `Tstep` (`TstepC_eq`: the change of
variables (2.7) and Lemma 2.5). -/
noncomputable def TstepC (g : Fld d L N₁ m₁ (k + 1) N) : ℂ :=
  ((S.betaU ^ (-((N * Fintype.card S.U : ℕ) : ℝ) / 2) : ℝ) : ℂ) * S.covSqrtC.det *
    ∫ x : S.E, ((chiFl S.U N S.p₁ x : ℝ) : ℂ) *
      (S.tKernelC (S.psiAtC 1 x) * S.rhoExpC C g (S.psiAtC 1 x))

/-! ### The new terms `ℰ₀^{(k+1)}`, `ℱ₀^{(k+1)}`, `ℳ₀^{(k+1)}` at a complex datum -/

/-- **`ℰ₁^{(k+1)}` of (2.8) at a complex datum**:
`∫₀¹ ds ∫ dμ_{s,0} ∂_s[-β_k V^{(k)}(s ψ') + δℰ_k(s ψ')]` with the exponent `WoneC` of the complex
step; the expectation in `μ_{s,0}` is `avgFun` (the quotient by `Z_{s,0}`, no real parts).  It is
`E1` with `Wone` replaced by `WoneC`. -/
noncomputable def E1C : ℂ :=
  ∫ s in (0 : ℝ)..1, avgFun S.nuFl (S.WoneC C) (fun x => deriv (fun r => S.WoneC C r x) s) s

/-- **`ℰ₀^{(k+1)} = ½ log det C^{(k)} + ℰ₁^{(k+1)}`** (2.8) at a complex datum, with the analytic
`½ log det C^{(k)}` (`halfLogDetCC`). -/
noncomputable def E0C : ℂ := S.halfLogDetCC + S.E1C C

/-- **`ℱ₀^{(k+1)}(g)` of (2.9) at a complex datum**: `∫₀¹ dt ∫ dμ_{1,t} ∂_t δℱ_k(t ψ', g)` with the
exponents `WoneC`, `WtwoC` of the complex step.  It is `F0` with `Wone`, `Wtwo` replaced by `WoneC`,
`WtwoC`. -/
noncomputable def F0C (g : Fld d L N₁ m₁ (k + 1) N) : ℂ :=
  ∫ t in (0 : ℝ)..1, avgFun₂ S.nuFl (S.WoneC C) (S.WtwoC C g)
    (fun x => deriv (fun r => S.WtwoC C g r x) t) 1 t

/-- **`ℳ₀^{(k+1)}(y; g)` (P4 (2.53)) at a complex datum**:
`β_k^{1/2} ∫₀¹ dt ∫ dμ_{1,t} ∂_t ℳ_k(y; ψ^{(k)} + t ψ', g)` with the composite `ℳ_k` of the complex
backgrounds (`McompAtC`) on the path `psiAtC`.  It is `M0` with `Wone`, `Wtwo`, `McompAt`, `dataU`,
`psiAt` replaced by `WoneC`, `WtwoC`, `McompAtC`, `dataUC`, `psiAtC`. -/
noncomputable def M0C (g : Fld d L N₁ m₁ (k + 1) N) (y : CTorus d L N₁ m₁ (k + 1)) (i : Fin N) :
    ℂ :=
  ((S.betaU ^ (1 / 2 : ℝ) : ℝ) : ℂ) *
    ∫ t in (0 : ℝ)..1, avgFun₂ S.nuFl (S.WoneC C) (S.WtwoC C g)
      (fun x => deriv (fun r => McompAtC C.m₀ C.Tm S.a S.ν (Nat.le_succ k)
        (S.dataUC (S.psiAtC r x)) g y i) t) 1 t

/-! ### Localized forms (P4 (2.56)-(2.60)) at a complex datum -/

/-- Restriction of a complex field of the unit lattice to the block `B_{k+1}(z)` (`maskU` for
complex fields). -/
noncomputable def maskUC (z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1)))) (v : S.EC) : S.EC :=
  open Classical in fun q => if q.1 ∈ S.blockU z then v q else 0

/-- The exponent `W₁(1, ·)` of the complex step as a function of the complex shift `ψ'` of the unit
lattice (`Phi1` for complex shifts): `Φ₁(ψ') = -β_k V^{(k)}(ψ') + δℰ_k(ψ')`. -/
noncomputable def Phi1C (y : S.EC) : ℂ :=
  -(S.β : ℂ) * S.VkC (S.psi0C + y) + S.dEC C (S.psi0C + y)

/-- **`ℰ₁^{(k+1)}(z)` (P4 (2.56)-(2.60)) at a complex datum**: the formula (2.8) with the scalar
product restricted to `y ∈ B_{k+1}(z)`, `∫₀¹ ds ∫ dμ_{s,0} DΦ₁(s ψ')[1_{B(z)} ψ']`, with the complex
shift `ψ' = shiftUC ψ̂` and the complex derivative of `Φ₁ = Phi1C` (`Φ₁` is a function of the complex
shift; (H.2), Lemma 2.3 (d)).  It is `E1loc` for the objects of the complex step. -/
noncomputable def E1locC (z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1)))) : ℂ :=
  ∫ s in (0 : ℝ)..1, avgFun S.nuFl (S.WoneC C)
    (fun x => (fderiv ℂ (S.Phi1C C) ((s : ℂ) • S.shiftUC x)) (S.maskUC z (S.shiftUC x))) s

/-- **`ℰ₀^{(k+1)}(z) = -½ ∑_{y ∈ B(z)} tr 𝕃(y,y) + ℰ₁^{(k+1)}(z)`** (P4 (2.56)) at a complex datum,
`𝕃 = logAC`. -/
noncomputable def E0locC (z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1)))) : ℂ :=
  -(1 / 2 : ℂ) * ∑ y ∈ S.blockU z, ∑ i, S.logAC (y, i) (y, i) + S.E1locC C z

/-- The blocks `B_{k+1}(z)` partition the unit lattice: the localized traces of `𝕃 = logAC` add up
to the total (the complex form of `sum_blockU_trace`). -/
theorem sum_blockU_traceC :
    ∑ z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))),
      ∑ y ∈ S.blockU z, ∑ i : Fin N, S.logAC (y, i) (y, i) =
        ∑ y : S.U, ∑ i : Fin N, S.logAC (y, i) (y, i) := by
  classical
  unfold blockU
  exact Finset.sum_fiberwise (Finset.univ : Finset S.U)
    (fun b : S.U => unitBlock1 (b : UnitTorus d L N₁ m₁ k))
    (fun y => ∑ i : Fin N, S.logAC (y, i) (y, i))

/-- **`∑_z (-½ ∑_{y ∈ B(z)} tr 𝕃(y,y)) = ½ log det C^{(k)}`** at a complex datum: the trace parts of
`E0locC` add up to `halfLogDetCC` (for every datum; the definition of the analytic branch). -/
theorem sum_trace_E0locC :
    ∑ z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))),
      -(1 / 2 : ℂ) * ∑ y ∈ S.blockU z, ∑ i : Fin N, S.logAC (y, i) (y, i) = S.halfLogDetCC := by
  unfold halfLogDetCC
  rw [← Finset.mul_sum, S.sum_blockU_traceC]

/-! ### Truncations to the support of `ν_{p₁}`, the prefactor, the regularity inputs -/

/-- The truncation of `W₁` of the complex step to the support of `χ_fl` (where `ν_{p₁}` lives). -/
noncomputable def WoneCT (s : ℝ) (x : S.E) : ℂ :=
  open Classical in if chiFl S.U N S.p₁ x = 1 then S.WoneC C s x else 0

/-- The truncation of `W₂` of the complex step to the support of `χ_fl`. -/
noncomputable def WtwoCT (g : Fld d L N₁ m₁ (k + 1) N) (t : ℝ) (x : S.E) : ℂ :=
  open Classical in if chiFl S.U N S.p₁ x = 1 then S.WtwoC C g t x else 0

/-- The class exponent `δℰ_k(s ψ')` of `W₁` of the complex step, truncated to the support of
`ν_{p₁}`. -/
noncomputable def dECT (s : ℝ) (x : S.E) : ℂ :=
  open Classical in if chiFl S.U N S.p₁ x = 1 then S.dEC C (S.psiAtC s x) else 0

/-- The potential exponent `-β_k V^{(k)}(s ψ')` of `W₁` of the complex step, truncated to the
support of `ν_{p₁}`. -/
noncomputable def WVCT (s : ℝ) (x : S.E) : ℂ :=
  open Classical in if chiFl S.U N S.p₁ x = 1 then -(S.β : ℂ) * S.VkC (S.psiAtC s x) else 0

/-- The constant prefactor of (2.6)-(2.7) at a complex datum: the normalisation of `t_k` and the
background values of the exponent (`Pconst` for the complex objects). -/
noncomputable def PconstC (g : Fld d L N₁ m₁ (k + 1) N) : ℂ :=
  (((S.cKernel / (2 * Real.pi)) ^ ((N : ℝ) * S.nBlocks / 2) : ℝ) : ℂ) *
    Complex.exp (-(S.β : ℂ) * S.AnewC +
      EcompAtC C.m₀ C.Tm S.a S.ν (Nat.le_succ k) S.psiKdC - (C.Ek : ℂ) * (S.nU : ℂ) +
      FcompAtC C.m₀ C.Tm S.a S.ν (Nat.le_succ k) S.psiKdC g)

/-- **Regularity of the interpolation of the complex step along the ray** (`StepRegular` for the
exponents `WoneC`, `WtwoC`): the exponents of `μ_{s,t}`, truncated to the support `{χ_fl = 1}` of
`ν_{p₁}`, are `C¹` families on an open neighbourhood of `[0,1]`, bounded together with their
derivatives.  (The analyticity (H.2), (H.7) of the class terms on `Ξ^c`, and of the complex small
solution on `𝒟`, along the path `s ↦ ψ^{(k)}(θ) + s ψ'`.) -/
structure StepRegularC (g : Fld d L N₁ m₁ (k + 1) N) : Prop where
  c1 : ∃ (U : Set ℝ) (W₁' W₂' : ℝ → S.E → ℂ),
    IsC1Family U (S.WoneCT C) W₁' ∧ IsC1Family U (S.WtwoCT C g) W₂'

/-- **Regularity of the class terms of the complex step along the ray** (`ClassRegular` for the
complex step: the analyticity (H.2), (H.7) of `ℰ_k` and `ℱ_k` on `Ξ^c`, and the inclusion of the
composed data of the complex path in it): the exponents `δℰ_k(s ψ')` and `δℱ_k(t ψ', g)` with the
complex backgrounds, truncated to the support of `ν_{p₁}`, are `C¹` families on an open neighbourhood
of `[0,1]`, bounded with their derivatives.  This is the only analytic input on the class; the
interaction `V^{(k)}` and the complex small solution are treated in `isC1Family_WVCT`. -/
structure ClassRegularC (g : Fld d L N₁ m₁ (k + 1) N) : Prop where
  c1 : ∃ (U : Set ℝ) (E' F' : ℝ → S.E → ℂ),
    IsC1Family U (S.dECT C) E' ∧ IsC1Family U (S.WtwoCT C g) F'

theorem WoneCT_of_chi (s : ℝ) (x : S.E) (hx : chiFl S.U N S.p₁ x = 1) :
    S.WoneCT C s x = S.WoneC C s x := by
  simp [WoneCT, hx]

theorem WtwoCT_of_chi (g : Fld d L N₁ m₁ (k + 1) N) (s : ℝ) (x : S.E)
    (hx : chiFl S.U N S.p₁ x = 1) : S.WtwoCT C g s x = S.WtwoC C g s x := by
  simp [WtwoCT, hx]

theorem WtwoCT_zero (g : Fld d L N₁ m₁ (k + 1) N) (x : S.E) : S.WtwoCT C g 0 x = 0 := by
  unfold WtwoCT
  rw [S.WtwoC_zero]
  simp

theorem WoneCT_zero (x : S.E) (hV : S.VkC S.psi0C = 0) : S.WoneCT C 0 x = 0 := by
  unfold WoneCT WoneC dEC
  rw [S.psiAtC_zero, hV]
  simp

theorem WoneCT_eq_add (s : ℝ) (x : S.E) : S.WoneCT C s x = S.WVCT s x + S.dECT C s x := by
  by_cases hx : chiFl S.U N S.p₁ x = 1
  · simp [WoneCT, WVCT, dECT, WoneC, hx]
  · simp [WoneCT, WVCT, dECT, hx]

/-- `ℱ_k = ⟨g, ℳ_k⟩₁` on the path of the complex step: `W₂(t, ψ̂) = ⟨g, ℳ_k(ψ^{(k)} + t ψ')⟩₁ -
ℱ_k(ψ^{(k)}, g)` (the complex form of `Wtwo_eq_sum`). -/
theorem WtwoC_eq_sum (g : Fld d L N₁ m₁ (k + 1) N) (r : ℝ) (x : S.E) :
    S.WtwoC C g r x = ∑ y : CTorus d L N₁ m₁ (k + 1), ∑ i : Fin N,
      g y i * McompAtC C.m₀ C.Tm S.a S.ν (Nat.le_succ k) (S.dataUC (S.psiAtC r x)) g y i -
      FcompAtC C.m₀ C.Tm S.a S.ν (Nat.le_succ k) (S.dataUC S.psi0C) g := by
  unfold WtwoC dFC
  rw [FcompAtC_eq_pair]

end StepSetting

end Balaban.Fluctuation
