/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.RenormExpBounds
public import Balaban.Fluctuation.DetCollarHull
public import Balaban.Fluctuation.RootDetChart
public import Balaban.Fluctuation.CovarianceComplexPath
public import Balaban.Localization.XiCRawOpen
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The renormalized datum and the determinant part of the new energy function

In the renormalization map (P4 (4.17)-(4.18)) the new step terms are evaluated at the renormalized
field `θ = (1 + ζ(ξ)) Ψ`, with `ζ(ξ) = ε ξ₀` (`renZeta`), and the same `h`.

## Main definitions

* `renThetaDatum ε D ξ`: the datum `((1 + ζ(ξ)) D.Ψ, D.h)`.
* `renE0θ_det εren E z D ξ`: the sum over all finite sets `T` of cubes (at `m₀ = 1`) of the terms
  `(E z).term (renThetaDatum εren D ξ) T`.

## Main results

* `renThetaRaw_mem_rawSub`, `renThetaDatum_zero`, `renThetaDatum_agree`,
  `renThetaRaw_rawAgree`, `analyticOnNhd_renThetaRaw`: membership in the relative subspace, the
  value at `ξ = 0`, locality, and analyticity of the map `((Ψ, h), ξ) ↦ ((1 + ζ(ξ)) Ψ, h)`.
* `renTheta_zero_chart`: at `ξ = 0` the datum of `XiCOneReal` lies in `XiCData` at level `k + 1`.
* `renTheta_realizesC`, `renTheta_collarBond_le`, `renTheta_norm_le`: the clauses of the class
  preserved by the scaling (same real centre, displacement `Ψ'' + ζ Ψ`).
* `renE0θ_det_eq_sum_collar`: reindexing over collar hulls.
* `renE0θ_det_zero`: at `ξ = 0` the value is the determinant term `-(1/2) ∑ log A_C` of the step.

## What is not asserted

This file is the **determinant part only**: the physical new energy function also contains the
marked terms of `E1`; they are not here.  There is no `expE0` field, **no chart inclusion for
`ξ ≠ 0`** (that the scaled datum lies in `XiCData` at some radius) and no substitution of the
renormalized mass `ν_u` in the step terms (the mass shift is carried by the `C₂` term).  The
assertions about the scaled datum for `ξ ≠ 0` proved below are the elementary ones; the others are
listed in the docstring of `renTheta_realizesC` and are not proved.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Localization

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}
variable (S : StepSetting d L N₁ m₁ k N ϱ)

/-! ### The elementary map -/

theorem renThetaRaw_mem_rawSub (ε : ℝ) (D : BgData S.G' N) (ξ : Fin 3 → ℂ) :
    ((fun x i => (1 + renZeta ε ξ) * D.Ψ x i), D.h) ∈ rawSub N S.G' := by
  refine ⟨fun n hn hk x hx x' hx' => ?_, D.h_layerConst, fun x hx => ?_, D.h_zero⟩
  · funext i
    show (1 + renZeta ε ξ) * D.Ψ x' i = (1 + renZeta ε ξ) * D.Ψ x i
    rw [D.Ψ_layerConst n hn hk x hx x' hx']
  · funext i
    show (1 + renZeta ε ξ) * D.Ψ x i = 0
    rw [D.Ψ_zero x hx]; simp

/-- **The renormalized datum** `θ(D, ξ) = ((1 + ζ(ξ)) D.Ψ, D.h)`: only `Ψ` is rescaled. -/
noncomputable def renThetaDatum (ε : ℝ) (D : BgData S.G' N) (ξ : Fin 3 → ℂ) :
    BgData S.G' N :=
  bgOfRaw ((fun x i => (1 + renZeta ε ξ) * D.Ψ x i), D.h) (renThetaRaw_mem_rawSub S ε D ξ)

variable {S}

theorem renThetaDatum_Ψ (ε : ℝ) (D : BgData S.G' N) (ξ : Fin 3 → ℂ) (x i) :
    (renThetaDatum S ε D ξ).Ψ x i = (1 + renZeta ε ξ) * D.Ψ x i := rfl

theorem renThetaDatum_h (ε : ℝ) (D : BgData S.G' N) (ξ : Fin 3 → ℂ) :
    (renThetaDatum S ε D ξ).h = D.h := rfl

theorem rawOf_renThetaDatum (ε : ℝ) (D : BgData S.G' N) (ξ : Fin 3 → ℂ) :
    rawOf (renThetaDatum S ε D ξ) = ((fun x i => (1 + renZeta ε ξ) * D.Ψ x i), D.h) := rfl

theorem renZeta_zero (ε : ℝ) : renZeta ε (0 : Fin 3 → ℂ) = 0 := by
  simp [renZeta]

/-- At `ξ = 0` the renormalized datum is the datum. -/
theorem renThetaDatum_zero (ε : ℝ) (D : BgData S.G' N) : renThetaDatum S ε D 0 = D := by
  obtain ⟨Ψ, h, a, b, c, e⟩ := D
  simp only [renThetaDatum, bgOfRaw, renZeta_zero, add_zero, one_mul]

/-- Raw locality: data agreeing at a site have renormalized data agreeing there (equal `ξ`). -/
theorem renThetaDatum_agree (ε : ℝ) {D D₂ : BgData S.G' N} (ξ : Fin 3 → ℂ)
    {x : Torus d (N₁ * L ^ m₁ * L ^ (k + 1))} (hΨ : D.Ψ x = D₂.Ψ x) (hh : D.h x = D₂.h x) :
    (renThetaDatum S ε D ξ).Ψ x = (renThetaDatum S ε D₂ ξ).Ψ x ∧
      (renThetaDatum S ε D ξ).h x = (renThetaDatum S ε D₂ ξ).h x := by
  refine ⟨?_, hh⟩
  funext i
  simp only [renThetaDatum_Ψ, hΨ]

omit [NeZero L] [NeZero N₁] in
/-- Raw locality in `RawAgree` form. -/
theorem renThetaRaw_rawAgree (ε : ℝ) (ξ : Fin 3 → ℂ)
    (Y : Finset (Torus d (N₁ * L ^ m₁ * L ^ (k + 1))))
    {p p' : RawData d L (N₁ * L ^ m₁) (k + 1) N} (h : RawAgree Y p p') :
    RawAgree Y ((fun x i => (1 + renZeta ε ξ) * p.1 x i), p.2)
      ((fun x i => (1 + renZeta ε ξ) * p'.1 x i), p'.2) := by
  intro x hx
  obtain ⟨h1, h2⟩ := h x hx
  refine ⟨?_, h2⟩
  show (fun i => (1 + renZeta ε ξ) * p.1 x i) = fun i => (1 + renZeta ε ξ) * p'.1 x i
  rw [h1]

/-- The map `((Ψ, h), ξ) ↦ ((1 + ζ(ξ)) Ψ, h)` is analytic on the whole space (it is bilinear in
`(ξ₀, Ψ)` plus the identity on `h`). -/
theorem analyticOnNhd_renThetaRaw (ε : ℝ) (s : Set (RawData d L (N₁ * L ^ m₁) (k + 1) N ×
      (Fin 3 → ℂ))) :
    AnalyticOnNhd ℂ (fun q : RawData d L (N₁ * L ^ m₁) (k + 1) N × (Fin 3 → ℂ) =>
      ((fun x i => (1 + renZeta ε q.2) * q.1.1 x i), q.1.2)) s := by
  intro q _
  have hz : AnalyticAt ℂ (fun q' : RawData d L (N₁ * L ^ m₁) (k + 1) N × (Fin 3 → ℂ) =>
      renZeta ε q'.2) q := by
    unfold renZeta
    exact analyticAt_const.mul (by fun_prop)
  refine AnalyticAt.prod ?_ (by fun_prop)
  refine analyticAt_pi_iff.2 fun x => analyticAt_pi_iff.2 fun i => ?_
  exact (analyticAt_const.add hz).mul (by fun_prop)

/-! ### The chart: the base case and the clauses preserved by the scaling -/

section Chart

variable {a : ℕ → ℝ} {ν ε εr : ℝ}

/-- **The base case.**  A datum of `XiCOneReal` lies in the chart `XiCData` at level `k + 1`
(and `ξ = 0`, where the renormalized datum is the datum, `renThetaDatum_zero`). -/
theorem renTheta_zero_chart (D : BgData S.G' N) (hD : XiCOneReal S.G' S.a S.ν ε D) :
    XiCData S.G' S.a S.ν (k + 1) 1 ε D :=
  hD.xiCOne

/-- **Clauses of `XiC` under `Ψ ↦ (1 + ζ) Ψ`: the same real centre `(Ψ₀, h₀)`.**
Write `D = (Ψ₀ + Ψ'', h₀ + h'')` and `θ = (1 + ζ(ξ))·` applied to `Ψ`.  With the *same* real
centre the scaled datum realizes the displacements `(Ψ'' + ζ Ψ, h'')`.  Then:

Preserved exactly, hence proved or immediate: the real part of `XiC` (`0 < σ`, `0 < ε`, the
real datum `D^r`, `XiAt`: it does not involve the complex datum); the clauses `hAbs` and `hDot`
of `XiCBounds` (they involve only `h''` and the real solution `φ^r`); `RealizesC`
(`renTheta_realizesC`).

Preserved with loss, proved here: the `collarBond` displacement difference
(`renTheta_collarBond_le`: loss `|ζ| vn (Ψ z - Ψ z')`), the norms (`renTheta_norm_le`).

Not elementary and **not proved**: (i) `InUnionDomainC` for the scaled complex datum `Dᶜ_θ`
(it is a condition on the solution of the complex variational problem with datum `Dᶜ_θ`);
(ii) the clauses `grad`, `lap`, `mult`, `val`, `close` of `XiCBounds` for
`(φ^c_θ - φ^r, α^c_θ - α^r)`, where `(φ^c_θ, α^c_θ) = (bgFieldC, bgMultC)` of the scaled datum:
these involve the solution of the variational problem, which is not linear in `Ψ`, so the
scaling changes them by the Lipschitz dependence of the solution on the datum, with the loss
of P4 (4.19); (iii) any version of the above with a *real* centre for the scaled datum when
`ζ(ξ)` is not real: the displacement `ζ Ψ` is then complex and must be absorbed in `Ψ''`
(this is what the same-centre choice does), at the price of the loss in (ii). -/
theorem renTheta_realizesC {D : BgData S.G' N}
    {Ψ₀ : Torus d (N₁ * L ^ m₁ * L ^ (k + 1)) → Fin N → ℝ} {h₀ : Fin N → ℝ}
    {Ψ'' h'' : Torus d (N₁ * L ^ m₁ * L ^ (k + 1)) → Fin N → ℂ}
    (hR : RealizesC D Ψ₀ h₀ Ψ'' h'') (εr : ℝ) (ξ : Fin 3 → ℂ) :
    RealizesC (renThetaDatum S εr D ξ) Ψ₀ h₀
      (fun x i => Ψ'' x i + renZeta εr ξ * D.Ψ x i) h'' := by
  refine ⟨fun x hx i => ?_, fun x hx i => ?_⟩
  · simp only [renThetaDatum_Ψ, hR.1 x hx i]; ring
  · rw [renThetaDatum_h]; exact hR.2 x hx i

omit [NeZero L] [NeZero N₁] in
/-- The collar bond of the new displacement: it changes by at most `|ζ|` times the collar
difference of `Ψ`. -/
theorem renTheta_collarBond_le (Ψ'' Ψ : Torus d (N₁ * L ^ m₁ * L ^ (k + 1)) → Fin N → ℂ)
    (ζ : ℂ) (z z' : Torus d (N₁ * L ^ m₁ * L ^ (k + 1))) :
    vn (fun i => (Ψ'' z i + ζ * Ψ z i) - (Ψ'' z' i + ζ * Ψ z' i)) ≤
      vn (fun i => Ψ'' z i - Ψ'' z' i) + ‖ζ‖ * vn (fun i => Ψ z i - Ψ z' i) := by
  have e : (fun i => (Ψ'' z i + ζ * Ψ z i) - (Ψ'' z' i + ζ * Ψ z' i)) =
      (fun i => Ψ'' z i - Ψ'' z' i) + ζ • (fun i => Ψ z i - Ψ z' i) := by
    funext i; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
  rw [e]
  exact vn_add_smul_le _ _ _

/-- Norm bound for the scaled field: `vn((1 + ζ)Ψ(x)) ≤ (1 + ε‖ξ‖) vn(Ψ(x))` for `ε ≥ 0`. -/
theorem renTheta_norm_le {εr : ℝ} (hε : 0 ≤ εr) (D : BgData S.G' N) (ξ : Fin 3 → ℂ)
    (x : Torus d (N₁ * L ^ m₁ * L ^ (k + 1))) :
    vn ((renThetaDatum S εr D ξ).Ψ x) ≤ (1 + εr * ‖ξ‖) * vn (D.Ψ x) := by
  have e : (renThetaDatum S εr D ξ).Ψ x = (1 + renZeta εr ξ) • D.Ψ x := by
    funext i; simp [renThetaDatum_Ψ]
  rw [e, vn_smul]
  have h1 : ‖1 + renZeta εr ξ‖ ≤ 1 + εr * ‖ξ‖ :=
    (norm_add_le _ _).trans (by simpa using norm_renZeta_le hε ξ)
  exact mul_le_mul_of_nonneg_right h1 (vn_nonneg _)

end Chart

/-! ### The determinant part of the new energy function -/

section Det

variable {εstep κdet cdet : ℝ}

/-- **The determinant part of the new energy function** at the root `z`: the sum over all finite
sets of cubes `T` (at `m₀ = 1`) of the terms of `E z` at the renormalized datum.  This is only the
determinant part; the marked terms of `E1` are not included. -/
noncomputable def renE0θ_det
    (εren : ℝ)
    (E : ∀ z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))),
      DetExpansionLocC S 1 z εstep κdet cdet)
    (z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))))
    (D : BgData S.G' N) (ξ : Fin 3 → ℂ) : ℂ :=
  ∑ T : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
      (K := k + 1) 1 (k + 1) Set.univ), (E z).term (renThetaDatum S εren D ξ) T

/-- Reindexing over collar hulls (`sum_detCollarGrouped`); no chart hypothesis is needed. -/
theorem renE0θ_det_eq_sum_collar (εren : ℝ)
    (E : ∀ z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))),
      DetExpansionLocC S 1 z εstep κdet cdet)
    (z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1)))) (D : BgData S.G' N)
    (ξ : Fin 3 → ℂ) :
    ∑ X ∈ (Finset.univ : Finset (Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
        (K := k + 1) 1 (k + 1) Set.univ))).image detCollarHull,
      (E z).detGrouped (renThetaDatum S εren D ξ) X =
      renE0θ_det εren E z D ξ := by
  unfold renE0θ_det
  exact sum_detCollarGrouped (fun T => (E z).term (renThetaDatum S εren D ξ) T)

/-- **Zero parameter.**  If `S.D'` lies in the chart, at `ξ = 0` the determinant part is the
determinant term of the step. -/
theorem renE0θ_det_zero (εren : ℝ)
    (E : ∀ z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))),
      DetExpansionLocC S 1 z εstep κdet cdet)
    (z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))))
    (hD : XiCData S.G' S.a S.ν (k + 1) 1 εstep S.D') :
    renE0θ_det εren E z S.D' 0 =
      -(1 / 2 : ℂ) * ∑ y ∈ S.blockU z, ∑ i : Fin N, S.logAC (y, i) (y, i) := by
  unfold renE0θ_det
  rw [renThetaDatum_zero, ← (E z).sum_eq S.D' hD]
  exact rootTrace_one_eq_logAC S z

end Det

end Balaban.Fluctuation
