/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.DetPrefactor
public import Balaban.Fluctuation.ParamDatumFamily
public import Balaban.Fluctuation.StepComplexProp26
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The step theorems with the localized determinant family

## How the determinant enters the landed step theorems

* **Theorem 3.1 (a)** (`thm31aC_of_input`, `thm31aC_coeff`, `thm31aC_coeff_withDatum`) takes an
  arbitrary element of `DetExpansionC S m₀ z κ'' c_det` and an arbitrary `E1MarksC`; the constant
  of its conclusion is `c_mark + c_det`, and the rate hypothesis is `κ' ≤ κ''`.  The only element
  of `DetExpansionC` used before `DetCauchyBgActivity` was `nonempty_detExpansionC`: one term at
  `T = ∅` carrying the whole trace, with `c_det = ‖trace‖ e^{κ'' M}`, `M` the size of the torus.
  With the element of `DetExpansionLocC` of `DetOutputTerms`, `c_det` is
  `L^d · ½ N covBLogMax d L κ / (1 - z)` (`DetPrefactor`): it involves neither the torus, nor the
  scale, nor `z`, nor the datum.  This is the constant of Theorem 3.1 (a) that becomes
  volume-independent; the mark constant `c_mark` is not affected.
* **The activity bounds** (`StepActivityBound`, `StepActivityBoundC`, and the general-scale theorem
  `stepActivityBound_zeroClass_direct_physical_scale`) concern the exponent `W₁ + W₂` of the
  interaction only.  Their statements do not mention the determinant.
* **Proposition 2.6** (`prop26C_step`, `prop26C_class`, `prop26C_class_of_activity`): the
  determinant enters the step identity through the Jacobian `det C^{(k)1/2} = exp(½ log det C^{(k)})`
  of the substitution (2.7), that is through the summand `halfLogDetCC` of `ℰ₀ = E0C`.

## Contents

* `thm31aC_coeff_detLoc_withDatum`, `thm31aC_coeff_detLoc`: Theorem 3.1 (a) with the terms
  `term D T + interpCoeff I T`, at every datum `D` of the chart with the constant field of the
  step (the determinant part is the value at `D` of one function of the datum).
* `rootCube_mem_of_coeff_ne_zero_of_anchor`: if the mark part is anchored at the root cube, so is
  the whole coefficient.
* `thm31aC_of_chart`: Theorem 3.1 (a) for a step on the chart with the determinant terms
  `∑_{y ∈ B(z)} detActivityBg y T` and the scale-uniform constant.
* `sum_term_eq_halfLogDetCC`, `sum_term_withDatum_eq_halfLogDetCC`,
  `det_covSqrtC_eq_exp_sum_term`: the terms of all roots add up to `halfLogDetCC`.
* `prop26C_class_of_activity_detLoc`: Proposition 2.6 with `halfLogDetCC` replaced by the sum of
  the localized terms.

## What is not proved

`E1MarksC` is an input of Theorem 3.1 (a) here exactly as in the landed statements; it is not
constructed.  The determinant terms are not shown to satisfy the bound of the class with its energy
constant (the constant `c_det` is not small, `half_le_detConst`), their part which is independent
of the field is not moved to the vacuum energy, and the output density of the step is not
identified with a density of the class.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization Balaban.Analysis
  Balaban.SmallField Balaban.SmallField.Def6 Balaban.Polymer Finset Matrix MeasureTheory

/-! ### Theorem 3.1 (a) -/

section Coeff

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}
  {S : StepSetting d L N₁ m₁ k N ϱ} {m₀ : ℕ}
  {z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1)))} {eps κ'' cdet : ℝ}

open Classical in
/-- **Theorem 3.1 (a) at a datum of the family, with the localized determinant terms.**  Let `E`
be a localized determinant family of the step `S`, `D` a datum of the chart with the constant
field `h ≡ h₀`, and `I` marks of the step `S.withDatum D` with rate `κ' ≤ κ''`.  Then
`ℰ₀^{(k+1)}(z) = ∑_T (term D T + interpCoeff I T)` at the datum `D`, and each summand is bounded
by `(c_mark + c_det) e^{-κ' d(T)}`.  The determinant part `term D T` is the value at `D` of one
function of the datum. -/
theorem thm31aC_coeff_detLoc_withDatum (E : DetExpansionLocC S m₀ z eps κ'' cdet)
    (D : BgData S.G' N) (hDh : ∀ y i, D.h y i = (S.h₀ i : ℂ))
    (hX : XiCData S.G' S.a S.ν (k + 1) 1 eps D) (C : StepClass d L N₁ m₁ k N ϱ)
    {BS : BlockSplit (S.withDatum D hDh) m₀} (I : E1MarksC (S.withDatum D hDh) C BS z)
    (hκ'' : I.κ' ≤ κ'') :
    (S.withDatum D hDh).E1locC C z = ∑ T, interpCoeff I T ∧
    (S.withDatum D hDh).E0locC C z = ∑ T, (E.term D T + interpCoeff I T) ∧
    ∀ T, ‖E.term D T + interpCoeff I T‖ ≤ (CPE d L I.Kc I.κH I.κ0 I.κ' *
          (∑ i, I.F0 i * Real.exp (-I.κ0 * I.Lab.dl (I.y0 i))) + cdet) *
        Real.exp (-I.κ' * dExt T) :=
  thm31aC_coeff I hκ'' (E.atDatum D hDh hX)

open Classical in
/-- **Theorem 3.1 (a) with the localized determinant terms**, at the datum of the step. -/
theorem thm31aC_coeff_detLoc (E : DetExpansionLocC S m₀ z eps κ'' cdet)
    (hD : XiCData S.G' S.a S.ν (k + 1) 1 eps S.D') {C : StepClass d L N₁ m₁ k N ϱ}
    {BS : BlockSplit S m₀} (I : E1MarksC S C BS z) (hκ'' : I.κ' ≤ κ'') :
    S.E1locC C z = ∑ T, interpCoeff I T ∧
    S.E0locC C z = ∑ T, (E.term S.D' T + interpCoeff I T) ∧
    ∀ T, ‖E.term S.D' T + interpCoeff I T‖ ≤ (CPE d L I.Kc I.κH I.κ0 I.κ' *
          (∑ i, I.F0 i * Real.exp (-I.κ0 * I.Lab.dl (I.y0 i))) + cdet) *
        Real.exp (-I.κ' * dExt T) :=
  thm31aC_coeff I hκ'' (E.toDetExpansionC hD)

/-- **Anchor of the whole coefficient.**  If the mark part is anchored at the root cube of `z`
(`interpCoeff I T ≠ 0` implies `rootCube z ∈ T`; for instance by `anchor_of_meets`), then a
non-zero coefficient `term D T + interpCoeff I T` has the root cube of `z` in `T`. -/
theorem rootCube_mem_of_coeff_ne_zero_of_anchor (E : DetExpansionLocC S m₀ z eps κ'' cdet)
    {D : BgData S.G' N} (hD : XiCData S.G' S.a S.ν (k + 1) 1 eps D)
    {e : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) m₀ (k + 1)
      Set.univ) → ℂ}
    (he : ∀ T, e T ≠ 0 → rootCube (m₀ := m₀) (K := k + 1) z ∈ T)
    {T : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) m₀ (k + 1)
      Set.univ)} (h : E.term D T + e T ≠ 0) : rootCube (m₀ := m₀) (K := k + 1) z ∈ T := by
  by_contra hT
  have h1 := E.term_eq_zero_of_not_mem hD hT
  have h2 : e T = 0 := by
    by_contra h2
    exact hT (he T h2)
  exact h (by rw [h1, h2, add_zero])

end Coeff

/-! ### The sum over the roots -/

section Sum

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ ϱm : ℝ}
  {S : StepSetting d L N₁ m₁ k N ϱ} {m₀ : ℕ} {eps κ'' cdet : ℝ}

/-- **The terms of all roots add up to `½ log det C^{(k)}`**: for a localized determinant family
at every root `z` and the datum of the step in the chart,
`∑_z ∑_T term_z D' T = halfLogDetCC`. -/
theorem sum_term_eq_halfLogDetCC
    (E : ∀ z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))),
      DetExpansionLocC S m₀ z eps κ'' cdet)
    (hD : XiCData S.G' S.a S.ν (k + 1) 1 eps S.D') :
    ∑ z, ∑ T, (E z).term S.D' T = S.halfLogDetCC := by
  rw [← sum_rootTrace_one_eq_halfLogDetCC S]
  exact Finset.sum_congr rfl fun z _ => ((E z).sum_eq S.D' hD).symm

/-- The same at a datum `D` of the chart with the constant field of the step: the terms at `D`
add up to `halfLogDetCC` of the step `S.withDatum D`. -/
theorem sum_term_withDatum_eq_halfLogDetCC
    (E : ∀ z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))),
      DetExpansionLocC S m₀ z eps κ'' cdet)
    (D : BgData S.G' N) (hDh : ∀ y i, D.h y i = (S.h₀ i : ℂ))
    (hX : XiCData S.G' S.a S.ν (k + 1) 1 eps D) :
    ∑ z, ∑ T, (E z).term D T = (S.withDatum D hDh).halfLogDetCC :=
  sum_term_eq_halfLogDetCC (S := S.withDatum D hDh) (fun z => (E z).withDatum D hDh) hX

variable {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm} {c BG κ Kc Cx c₂ BG₂ δ₁ δc : ℝ}

/-- **The Jacobian of the step is the exponential of the sum of the localized terms**: on the
chart, `det C^{(k)1/2} = exp(∑_z ∑_T term_z D' T)`. -/
theorem det_covSqrtC_eq_exp_sum_term
    (E : ∀ z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))),
      DetExpansionLocC S m₀ z eps κ'' cdet)
    (hC : FlCore N S.G' Hm S.a₁ S.ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    (hdm : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    (hD : XiCData S.G' S.a S.ν (k + 1) 1 eps S.D') :
    S.covSqrtC.det = Complex.exp (∑ z, ∑ T, (E z).term S.D' T) := by
  rw [sum_term_eq_halfLogDetCC E hD]
  exact S.det_covSqrtC_of_chart hC hMX hdm hα hsm hD

end Sum

/-! ### Theorem 3.1 (a) for a step on the chart -/

section Chart

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ ϱm : ℝ} {m₀ : ℕ}
variable (S : StepSetting d L N₁ m₁ k N ϱ)
  {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}
  {c BG κ eps Kc Cx c₂ BG₂ δ₁ δc : ℝ}

open Classical in
/-- **Theorem 3.1 (a) for a step on the chart, with the genuine determinant terms and a
volume-independent determinant constant.**  Under `FlCore`, the cap and the margins of the
covariance chart, `HatConn`, `L^{m₀} ∣ N₁` and the rate condition `e^κ > 2 (detDeg d L + 1)²`,
for marks `I` whose rate `κ'` is at most the rate
`(κ - log 2 - 2 log (detDeg d L + 1)) / (2 d L)` of the determinant terms:

* `ℰ₀^{(k+1)}(z) = ∑_T (∑_{y ∈ B(z)} detActivityBg y T + interpCoeff I T)`;
* each summand is at most
  `(c_mark + L^d · ½ N covBLogMax d L κ / (1 - (detDeg d L + 1)² 2/e^κ)) e^{-κ' d(T)}`;
* the determinant part of a summand vanishes unless the root cube of `z` belongs to `T` and `T`
  is a polymer.

The determinant constant involves neither the torus, nor the scale `k`, nor `z`. -/
theorem thm31aC_of_chart
    (hC : FlCore N S.G' Hm S.a₁ S.ν c BG κ eps Kc Cx c₂ BG₂ δ₁) (hδc : 0 ≤ δc)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    (hdm : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4) (hconn : HatConn S.G')
    (hD : XiCData S.G' S.a S.ν (k + 1) 1 eps S.D') (hN : L ^ m₀ ∣ N₁)
    (hz : ((detDeg d L + 1 : ℕ) : ℝ) ^ 2 * (2 / Real.exp κ) < 1)
    (z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1)))) {C : StepClass d L N₁ m₁ k N ϱ}
    {BS : BlockSplit S m₀} (I : E1MarksC S C BS z)
    (hκ' : I.κ' ≤ (κ - Real.log 2 - 2 * Real.log ((detDeg d L + 1 : ℕ) : ℝ)) / (2 * d * L)) :
    S.E0locC C z = ∑ T, (∑ y ∈ S.blockU z,
        detActivityBg m₀ S.a S.a₁ S.ν (rho4 d L N BG κ) S.D' y T + interpCoeff I T) ∧
    (∀ T, ‖∑ y ∈ S.blockU z,
        detActivityBg m₀ S.a S.a₁ S.ν (rho4 d L N BG κ) S.D' y T + interpCoeff I T‖ ≤
      (CPE d L I.Kc I.κH I.κ0 I.κ' * (∑ i, I.F0 i * Real.exp (-I.κ0 * I.Lab.dl (I.y0 i))) +
        (L : ℝ) ^ d * ((1 / 2 : ℝ) * N * covBLogMax d L κ /
          (1 - ((detDeg d L + 1 : ℕ) : ℝ) ^ 2 * (2 / Real.exp κ)))) *
        Real.exp (-I.κ' * dExt T)) ∧
    ∀ T, ∑ y ∈ S.blockU z,
        detActivityBg m₀ S.a S.a₁ S.ν (rho4 d L N BG κ) S.D' y T ≠ 0 →
      rootCube (m₀ := m₀) (K := k + 1) z ∈ T ∧ IsPolyDom m₀ (k + 1) (sitesOf T) := by
  obtain ⟨E, hE⟩ := exists_detExpansionLocC_of_chart_uniform (m₀ := m₀) S hC hδc hMX hdm hα hsm
    hconn hN hz z
  obtain ⟨-, h2, h3⟩ := thm31aC_coeff_detLoc E hD I hκ'
  simp only [hE] at h2 h3
  refine ⟨h2, h3, fun T hT => ?_⟩
  rw [← hE] at hT
  exact E.anchor S.D' hD T hT

end Chart

/-! ### Proposition 2.6 -/

section Prop26

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}
  (S : StepSetting d L N₁ m₁ k N ϱ) (C : StepClass d L N₁ m₁ k N ϱ) {m₀ : ℕ}
  {c BG κ eps Kc Cx c₂ BG₂ δ₁ δc κ'' cdet : ℝ}

/-- **Proposition 2.6 with the localized determinant terms.**  Under the hypotheses of
`prop26C_class_of_activity` (the step on the chart, the class regularity and the activity bound of
the complex step) and for a localized determinant family at every root,

`T(g) = exp [-β_k A^η_{k+1} + ℰ_k(ψ^{(k)}) - E'''_k |T^{(k)}_1| + ℱ_k(ψ^{(k)}, g)
  + ∑_z ∑_T term_z(T) + ℰ₁ + ℱ₀]`:

the summand `½ log det C^{(k)}` of `ℰ₀`, the Jacobian of the substitution (2.7), is the sum of the
localized determinant terms. -/
theorem prop26C_class_of_activity_detLoc
    (hC : FlCore N S.G' (stepG d L N₁ m₁ k ϱ) S.a₁ S.ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    (hdm : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    (ha₁ : 0 < S.a₁) (hc7 : c7 d L N BG κ ≤ thm73C3 d L N) {R : ℝ} (hR : 1 < R)
    (hsmR : 2 * (compC4 d * (bgK1 d L N * (xiC1 d * eps))) + 5 * (R * δ₁) ≤ bgC1 d L N)
    (hβ : 0 < S.β) (hp₁ : 0 < S.p₁) {pp : ℝ} (hlt : S.p₁ < pp)
    (hδ₁ : Real.sqrt N * (S.betaU ^ (-(1 / 2 : ℝ)) *
      (covSupConstC d L N (compWeight L S.a₁ k) κ * pp)) < δ₁)
    (hD : XiCData S.G' S.a S.ν (k + 1) 1 eps S.D')
    (E : ∀ z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))),
      DetExpansionLocC S m₀ z eps κ'' cdet)
    (g : Fld d L N₁ m₁ (k + 1) N) (hc : S.ClassRegularC C g)
    (hact : StepActivityBoundC S C g) :
    S.TstepC C g = Complex.exp (-(S.β : ℂ) * S.AnewC +
      EcompAtC C.m₀ C.Tm S.a S.ν (Nat.le_succ k) S.psiKdC - (S.Eppp C : ℂ) * (S.nU : ℂ) +
      FcompAtC C.m₀ C.Tm S.a S.ν (Nat.le_succ k) S.psiKdC g +
      (∑ z, ∑ T, (E z).term S.D' T + S.E1C C) + S.F0C C g) := by
  have h := S.prop26C_class_of_activity C hC hMX hdm hα hsm ha₁ hc7 hR hsmR hβ hp₁ hlt hδ₁ hD g
    hc hact
  rw [h, sum_term_eq_halfLogDetCC E hD]
  rfl

end Prop26

end Balaban.Fluctuation
