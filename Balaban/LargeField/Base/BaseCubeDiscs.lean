/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Base.BaseComponentIdentity
public import Balaban.LargeField.Base.BaseComponentCovariance

/-!
# The first-step operator with one parameter per first-level cube

The bond from `x` to `x + e_μ` joining two different first blocks carries the product
`t(Q(x)) · t(Q(x + e_μ))` of the parameters of the two first-level cubes it touches
(`Q = jBlock d L N₀ 1 1`).  Thus `t Q = 0` cuts every bond leaving the cube `Q`, and `t ≡ 1` is the
physical operator.

The coercivity margin of BASE-KERNEL-3 (1.6) is a perturbation statement about the edge parameters:
it needs every `s_b` within `η ≤ c/(8d)`, `c = 1/(4L²)`, of a real point of `[0,1]`.  For the cube
family this gives the following polydiscs, and no larger one is obtained from the margin:

* `|t_Q| ≤ ρ` with `ρ² ≤ c/(8d) = 1/(32 d L²)`, centred at the cut point `t = 0`;
* `|t_Q - r_Q| ≤ ε` with `r_Q ∈ [0,1]` and `3 ε ≤ c/(8d)`, which contains the physical point `t = 1`.

The disc `|t_Q| < e^{κ₁}` with `κ₁ ≥ 0` contains `t_Q = 1` and the pairs `t_Q = -t_{Q'}`; the bond
parameter `t_Q t_{Q'}` then reaches `-1`, where `Re ⟨u, H(s) u⟩ ≥ (c/2) ‖u‖²` is not available.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField.Base

open Balaban Balaban.Multiscale Balaban.Green Matrix Finset
open Balaban.Localization (RectAt ResOK sqrtMat logMat)
open scoped Matrix.Norms.L2Operator

variable {d L N₀ : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ} (G : GeneratingSet d L N₀ 1 ϱ) {N : ℕ}

theorem baseCutBonds_endpoints_mem {b : FineBond d L N₀} (hb : b ∈ baseCutBonds G) :
    b.1 ∈ G.Ω 1 ∧ bondTip b ∈ G.Ω 1 := by
  have := Finset.mem_filter.1 hb
  exact ⟨this.2.1, this.2.2.1⟩

/-- The cube parameters of norm at most `ρ` give edge parameters in the `η`-neighbourhood of
`[0,1]^𝓔` when `ρ² ≤ η`: every bond parameter is within `ρ²` of `0`. -/
theorem baseCube_param_mem_of_norm_le {ρ η : ℝ} (hρη : ρ ^ 2 ≤ η)
    {t : Torus d (N₀ * L ^ (1 - 1)) → ℂ}
    (ht : ∀ x ∈ G.Ω 1, ‖t (jBlock d L N₀ 1 1 x)‖ ≤ ρ) :
    (fun b : FineBond d L N₀ => t (jBlock d L N₀ 1 1 b.1) *
      t (jBlock d L N₀ 1 1 (bondTip b))) ∈ baseParamNbhd G η := by
  intro b hb
  obtain ⟨h1, h2⟩ := baseCutBonds_endpoints_mem G hb
  refine ⟨0, le_rfl, zero_le_one, ?_⟩
  have e1 := ht _ h1
  have e2 := ht _ h2
  simp only [Complex.ofReal_zero, sub_zero, norm_mul]
  calc _ ≤ ρ * ρ := mul_le_mul e1 e2 (norm_nonneg _) ((norm_nonneg _).trans e1)
    _ = ρ ^ 2 := (sq ρ).symm
    _ ≤ η := hρη

/-- Cube parameters within `ε ≤ 1` of reals `r ∈ [0,1]` give edge parameters within `3 ε` of
reals in `[0,1]`: `|t t' - r r'| ≤ ε (r' + ε) + r ε ≤ 2 ε + ε²`. -/
theorem baseCube_param_mem_of_close {ε η : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (hεη : 3 * ε ≤ η)
    {t : Torus d (N₀ * L ^ (1 - 1)) → ℂ}
    (ht : ∀ x ∈ G.Ω 1, ∃ r : ℝ, 0 ≤ r ∧ r ≤ 1 ∧ ‖t (jBlock d L N₀ 1 1 x) - (r : ℂ)‖ ≤ ε) :
    (fun b : FineBond d L N₀ => t (jBlock d L N₀ 1 1 b.1) *
      t (jBlock d L N₀ 1 1 (bondTip b))) ∈ baseParamNbhd G η := by
  intro b hb
  obtain ⟨h1, h2⟩ := baseCutBonds_endpoints_mem G hb
  obtain ⟨r, hr0, hr1, hr⟩ := ht _ h1
  obtain ⟨r', hr0', hr1', hr'⟩ := ht _ h2
  refine ⟨r * r', mul_nonneg hr0 hr0', by nlinarith, ?_⟩
  set u := t (jBlock d L N₀ 1 1 b.1)
  set u' := t (jBlock d L N₀ 1 1 (bondTip b))
  have hu' : ‖u'‖ ≤ 1 + ε := by
    have : ‖u'‖ ≤ ‖u' - (r' : ℂ)‖ + ‖(r' : ℂ)‖ := by
      simpa using norm_add_le (u' - (r' : ℂ)) (r' : ℂ)
    rw [Complex.norm_real, Real.norm_of_nonneg hr0'] at this
    linarith
  have key : u * u' - ((r * r' : ℝ) : ℂ) = (u - r) * u' + (r : ℂ) * (u' - r') := by
    push_cast; ring
  rw [key]
  calc ‖(u - (r : ℂ)) * u' + (r : ℂ) * (u' - (r' : ℂ))‖
      ≤ ‖(u - (r : ℂ)) * u'‖ + ‖(r : ℂ) * (u' - (r' : ℂ))‖ := norm_add_le _ _
    _ ≤ ε * (1 + ε) + 1 * ε := by
        rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg hr0]
        gcongr
    _ ≤ 3 * ε := by nlinarith
    _ ≤ η := hεη

section Family

variable (a : ℕ → ℝ) (ν : ℝ) (α : G.Ω 1 → ℂ)

/-- The Hamiltonian is entrywise analytic along any family of edge parameters that is analytic
in a complex variable. -/
theorem rectAt_baseHamiltonian_family {P : ℂ → FineBond d L N₀ → ℂ}
    (hP : ∀ b z0, AnalyticAt ℂ (fun z => P z b) z0) (z0 : ℂ) :
    RectAt (fun z => baseHamiltonian G a ν α (P z)) z0 := by
  intro p q
  simp only [baseHamiltonian, Matrix.add_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  exact analyticAt_const.add
    (Finset.analyticAt_fun_sum _ fun b _ => (hP b z0).mul analyticAt_const)

theorem rectAt_baseOp_family (e : G.Ω 1 → Fin N → ℂ) {P : ℂ → FineBond d L N₀ → ℂ}
    (hP : ∀ b z0, AnalyticAt ℂ (fun z => P z b) z0) (z0 : ℂ) :
    RectAt (fun z => baseOp N e (baseHamiltonian G a ν α (P z))) z0 := by
  have hH := rectAt_baseHamiltonian_family G a ν α hP z0
  unfold baseOp
  exact (((RectAt.const _ _).mul (RectAt.liftOp hH)).mul (RectAt.const _ _)).add
    (RectAt.const _ _)

variable {a ν α}

/-- Holomorphy of the resolvent along a family of edge parameters that stays in the
`η`-neighbourhood of `[0,1]^𝓔` on an open set. -/
theorem baseFamily_resolvent_analyticOn (hν : 0 ≤ ν) (ha : IsAdmissibleWeights 1 a)
    (hα : ∀ z, ‖α z‖ ≤ 1 / (8 * (L : ℝ) ^ 2)) {η : ℝ} (hη0 : 0 ≤ η)
    (hη : η ≤ baseCoercivity L / (8 * d)) (e : G.Ω 1 → Fin N → ℝ)
    (he : ∀ z, ∑ i, e z i ^ 2 = 1) {P : ℂ → FineBond d L N₀ → ℂ}
    (hP : ∀ b z0, AnalyticAt ℂ (fun z => P z b) z0) {D : Set ℂ}
    (hPD : ∀ z ∈ D, P z ∈ baseParamNbhd G η) {x : ℝ} (hx : 0 ≤ x) (p q : G.Ω 1 × Fin N) :
    AnalyticOnNhd ℂ (fun z : ℂ => baseResolvent N (fun z i => (e z i : ℂ))
      (baseHamiltonian G a ν α (P z)) x p q) D := by
  intro z0 hz0
  have hU := (baseResolvent_norm_le G hν ha hα hη0 hη (hPD z0 hz0) e he hx).1
  have hdet := ((Matrix.isUnit_iff_isUnit_det _).1 hU).ne_zero
  have hR : RectAt (fun z : ℂ => (baseOp N (fun z i => (e z i : ℂ))
      (baseHamiltonian G a ν α (P z)) +
      (x : ℂ) • (1 : Matrix (G.Ω 1 × Fin N) (G.Ω 1 × Fin N) ℂ))⁻¹) z0 :=
    RectAt.inv ((rectAt_baseOp_family G a ν α _ hP z0).add (RectAt.const _ _)) hdet
  exact hR p q

variable [Nonempty (G.Ω 1)] [NeZero N]

/-- Holomorphy of the principal inverse square root along such a family, on an open set. -/
theorem baseFamily_sqrt_analyticOn (hν : 0 ≤ ν) (ha : IsAdmissibleWeights 1 a)
    (hα : ∀ z, ‖α z‖ ≤ 1 / (8 * (L : ℝ) ^ 2)) {η : ℝ} (hη0 : 0 ≤ η)
    (hη : η ≤ baseCoercivity L / (8 * d)) (e : G.Ω 1 → Fin N → ℝ)
    (he : ∀ z, ∑ i, e z i ^ 2 = 1) {P : ℂ → FineBond d L N₀ → ℂ}
    (hP : ∀ b z0, AnalyticAt ℂ (fun z => P z b) z0) {D : Set ℂ} (hD : IsOpen D)
    (hPD : ∀ z ∈ D, P z ∈ baseParamNbhd G η) (p q : G.Ω 1 × Fin N) :
    AnalyticOnNhd ℂ (fun z : ℂ => sqrtMat (baseOp N (fun z i => (e z i : ℂ))
      (baseHamiltonian G a ν α (P z))) p q) D :=
  Balaban.Localization.analyticOnNhd_sqrtMat_fam hD
    (fun z hz => resOK_baseOp G hν ha hα hη0 hη (hPD z hz) e he)
    (fun z _ => rectAt_baseOp_family G a ν α _ hP z) p q

/-- Holomorphy of the principal logarithm along such a family, on an open set. -/
theorem baseFamily_log_analyticOn (hν : 0 ≤ ν) (ha : IsAdmissibleWeights 1 a)
    (hα : ∀ z, ‖α z‖ ≤ 1 / (8 * (L : ℝ) ^ 2)) {η : ℝ} (hη0 : 0 ≤ η)
    (hη : η ≤ baseCoercivity L / (8 * d)) (e : G.Ω 1 → Fin N → ℝ)
    (he : ∀ z, ∑ i, e z i ^ 2 = 1) {P : ℂ → FineBond d L N₀ → ℂ}
    (hP : ∀ b z0, AnalyticAt ℂ (fun z => P z b) z0) {D : Set ℂ} (hD : IsOpen D)
    (hPD : ∀ z ∈ D, P z ∈ baseParamNbhd G η) (p q : G.Ω 1 × Fin N) :
    AnalyticOnNhd ℂ (fun z : ℂ => logMat (baseOp N (fun z i => (e z i : ℂ))
      (baseHamiltonian G a ν α (P z))) p q) D :=
  Balaban.Localization.analyticOnNhd_logMat_fam hD
    (fun z hz => resOK_baseOp G hν ha hα hη0 hη (hPD z hz) e he)
    (fun z _ => rectAt_baseOp_family G a ν α _ hP z) p q

end Family

section Lines

/-- The bond parameter of the cube line `t₀ + z v` is a polynomial in `z`. -/
theorem analyticAt_cubeLine_param (t₀ v : Torus d (N₀ * L ^ (1 - 1)) → ℂ) (b : FineBond d L N₀)
    (z0 : ℂ) :
    AnalyticAt ℂ (fun z : ℂ => (t₀ (jBlock d L N₀ 1 1 b.1) + z * v (jBlock d L N₀ 1 1 b.1)) *
      (t₀ (jBlock d L N₀ 1 1 (bondTip b)) + z * v (jBlock d L N₀ 1 1 (bondTip b)))) z0 :=
  (analyticAt_const.add (analyticAt_id.mul analyticAt_const)).mul
    (analyticAt_const.add (analyticAt_id.mul analyticAt_const))

/-- The set of `z` for which the cube line `t₀ + z v` lies in the open polydisc of radius `ρ`
about `0` (at the sites of the chart domain) is open. -/
theorem isOpen_cubeLine_disc (ρ : ℝ) (t₀ v : Torus d (N₀ * L ^ (1 - 1)) → ℂ) :
    IsOpen {z : ℂ | ∀ x ∈ G.Ω 1,
      ‖t₀ (jBlock d L N₀ 1 1 x) + z * v (jBlock d L N₀ 1 1 x)‖ < ρ} := by
  have : {z : ℂ | ∀ x ∈ G.Ω 1,
      ‖t₀ (jBlock d L N₀ 1 1 x) + z * v (jBlock d L N₀ 1 1 x)‖ < ρ} =
      ⋂ x ∈ G.Ω 1, {z : ℂ | ‖t₀ (jBlock d L N₀ 1 1 x) + z * v (jBlock d L N₀ 1 1 x)‖ < ρ} := by
    ext z; simp
  rw [this]
  exact isOpen_biInter_finset fun x _ =>
    isOpen_lt (by fun_prop) continuous_const

/-- The set of `z` for which the cube line `t₀ + z v` lies in the open polydisc of radius `ε`
about the real point `r` is open. -/
theorem isOpen_cubeLine_close (ε : ℝ) (r : Torus d (N₀ * L ^ (1 - 1)) → ℝ)
    (t₀ v : Torus d (N₀ * L ^ (1 - 1)) → ℂ) :
    IsOpen {z : ℂ | ∀ x ∈ G.Ω 1,
      ‖t₀ (jBlock d L N₀ 1 1 x) + z * v (jBlock d L N₀ 1 1 x) - (r (jBlock d L N₀ 1 1 x) : ℂ)‖ <
        ε} := by
  have : {z : ℂ | ∀ x ∈ G.Ω 1,
      ‖t₀ (jBlock d L N₀ 1 1 x) + z * v (jBlock d L N₀ 1 1 x) - (r (jBlock d L N₀ 1 1 x) : ℂ)‖ <
        ε} = ⋂ x ∈ G.Ω 1, {z : ℂ |
      ‖t₀ (jBlock d L N₀ 1 1 x) + z * v (jBlock d L N₀ 1 1 x) - (r (jBlock d L N₀ 1 1 x) : ℂ)‖ <
        ε} := by
    ext z; simp
  rw [this]
  exact isOpen_biInter_finset fun x _ =>
    isOpen_lt (by fun_prop) continuous_const

end Lines

section Discs

variable {a : ℕ → ℝ} {ν : ℝ} {α : G.Ω 1 → ℂ} (hν : 0 ≤ ν) (ha : IsAdmissibleWeights 1 a)
  (hα : ∀ z, ‖α z‖ ≤ 1 / (8 * (L : ℝ) ^ 2)) {η : ℝ} (hη0 : 0 ≤ η)
  (hη : η ≤ baseCoercivity L / (8 * d)) (e : G.Ω 1 → Fin N → ℝ) (he : ∀ z, ∑ i, e z i ^ 2 = 1)

include hν ha hα hη0 hη he

/-- **Coercivity margin on the cube discs about the cut point.**  If `|t_Q| ≤ ρ` with `ρ² ≤ η ≤
c/(8d)`, then `Re ⟨u, A_e(s) u⟩ ≥ (c/2) ‖u‖²` for the cube family `s_b = t_Q t_{Q'}`. -/
theorem baseCube_isCoercive_disc {ρ : ℝ} (hρη : ρ ^ 2 ≤ η)
    {t : Torus d (N₀ * L ^ (1 - 1)) → ℂ}
    (ht : ∀ x ∈ G.Ω 1, ‖t (jBlock d L N₀ 1 1 x)‖ ≤ ρ) :
    IsCoercive (baseOp N (fun z i => (e z i : ℂ)) (baseHamiltonian G a ν α
      (fun b : FineBond d L N₀ => t (jBlock d L N₀ 1 1 b.1) *
        t (jBlock d L N₀ 1 1 (bondTip b))))) (baseCoercivity L / 2) :=
  baseOp_isCoercive_of_close G hν ha hα hη0 hη (baseCube_param_mem_of_norm_le G hρη ht) e he

/-- **Coercivity margin on the cube polydiscs about a real point of `[0,1]^cubes`**, which
contain the physical point `t ≡ 1` (take `r ≡ 1`) and the cut point `t ≡ 0` (take `r ≡ 0`). -/
theorem baseCube_isCoercive_close {ε : ℝ} (hε0 : 0 ≤ ε) (hεη : 3 * ε ≤ η)
    {t : Torus d (N₀ * L ^ (1 - 1)) → ℂ}
    (ht : ∀ x ∈ G.Ω 1, ∃ r : ℝ, 0 ≤ r ∧ r ≤ 1 ∧
      ‖t (jBlock d L N₀ 1 1 x) - (r : ℂ)‖ ≤ ε) :
    IsCoercive (baseOp N (fun z i => (e z i : ℂ)) (baseHamiltonian G a ν α
      (fun b : FineBond d L N₀ => t (jBlock d L N₀ 1 1 b.1) *
        t (jBlock d L N₀ 1 1 (bondTip b))))) (baseCoercivity L / 2) :=
  baseOp_isCoercive_of_close G hν ha hα hη0 hη
    (baseCube_param_mem_of_close G hε0 (by linarith [eta_le_one hη]) hεη ht) e he

/-- **Resolvent on the cube discs about the cut point:** `A_e(s) + x` is invertible and
`‖𝒞_{e,x}(s)‖ ≤ (c/2 + x)⁻¹`. -/
theorem baseCube_resolvent_disc {ρ : ℝ} (hρη : ρ ^ 2 ≤ η)
    {t : Torus d (N₀ * L ^ (1 - 1)) → ℂ}
    (ht : ∀ x ∈ G.Ω 1, ‖t (jBlock d L N₀ 1 1 x)‖ ≤ ρ) {x : ℝ} (hx : 0 ≤ x) :
    IsUnit (baseOp N (fun z i => (e z i : ℂ)) (baseHamiltonian G a ν α
        (fun b : FineBond d L N₀ => t (jBlock d L N₀ 1 1 b.1) *
          t (jBlock d L N₀ 1 1 (bondTip b)))) +
        (x : ℂ) • (1 : Matrix (G.Ω 1 × Fin N) (G.Ω 1 × Fin N) ℂ)) ∧
      ‖baseResolvent N (fun z i => (e z i : ℂ)) (baseHamiltonian G a ν α
        (fun b : FineBond d L N₀ => t (jBlock d L N₀ 1 1 b.1) *
          t (jBlock d L N₀ 1 1 (bondTip b)))) x‖ ≤ (baseCoercivity L / 2 + x)⁻¹ :=
  baseResolvent_norm_le G hν ha hα hη0 hη (baseCube_param_mem_of_norm_le G hρη ht) e he hx

/-- **Resolvent on the cube polydiscs about a real point.** -/
theorem baseCube_resolvent_close {ε : ℝ} (hε0 : 0 ≤ ε) (hεη : 3 * ε ≤ η)
    {t : Torus d (N₀ * L ^ (1 - 1)) → ℂ}
    (ht : ∀ x ∈ G.Ω 1, ∃ r : ℝ, 0 ≤ r ∧ r ≤ 1 ∧
      ‖t (jBlock d L N₀ 1 1 x) - (r : ℂ)‖ ≤ ε) {x : ℝ} (hx : 0 ≤ x) :
    IsUnit (baseOp N (fun z i => (e z i : ℂ)) (baseHamiltonian G a ν α
        (fun b : FineBond d L N₀ => t (jBlock d L N₀ 1 1 b.1) *
          t (jBlock d L N₀ 1 1 (bondTip b)))) +
        (x : ℂ) • (1 : Matrix (G.Ω 1 × Fin N) (G.Ω 1 × Fin N) ℂ)) ∧
      ‖baseResolvent N (fun z i => (e z i : ℂ)) (baseHamiltonian G a ν α
        (fun b : FineBond d L N₀ => t (jBlock d L N₀ 1 1 b.1) *
          t (jBlock d L N₀ 1 1 (bondTip b)))) x‖ ≤ (baseCoercivity L / 2 + x)⁻¹ :=
  baseResolvent_norm_le G hν ha hα hη0 hη
    (baseCube_param_mem_of_close G hε0 (by linarith [eta_le_one hη]) hεη ht) e he hx

variable [Nonempty (G.Ω 1)] [NeZero N]

/-- The Stieltjes matrix is a square root of the inverse and `exp (log A) = A`, on the cube discs
about the cut point. -/
theorem baseCube_sqrt_log_principal_disc {ρ : ℝ} (hρη : ρ ^ 2 ≤ η)
    {t : Torus d (N₀ * L ^ (1 - 1)) → ℂ}
    (ht : ∀ x ∈ G.Ω 1, ‖t (jBlock d L N₀ 1 1 x)‖ ≤ ρ) :
    sqrtMat (baseOp N (fun z i => (e z i : ℂ)) (baseHamiltonian G a ν α
        (fun b : FineBond d L N₀ => t (jBlock d L N₀ 1 1 b.1) *
          t (jBlock d L N₀ 1 1 (bondTip b))))) *
      sqrtMat (baseOp N (fun z i => (e z i : ℂ)) (baseHamiltonian G a ν α
        (fun b : FineBond d L N₀ => t (jBlock d L N₀ 1 1 b.1) *
          t (jBlock d L N₀ 1 1 (bondTip b))))) =
      (baseOp N (fun z i => (e z i : ℂ)) (baseHamiltonian G a ν α
        (fun b : FineBond d L N₀ => t (jBlock d L N₀ 1 1 b.1) *
          t (jBlock d L N₀ 1 1 (bondTip b)))))⁻¹ ∧
    NormedSpace.exp (logMat (baseOp N (fun z i => (e z i : ℂ)) (baseHamiltonian G a ν α
        (fun b : FineBond d L N₀ => t (jBlock d L N₀ 1 1 b.1) *
          t (jBlock d L N₀ 1 1 (bondTip b)))))) =
      baseOp N (fun z i => (e z i : ℂ)) (baseHamiltonian G a ν α
        (fun b : FineBond d L N₀ => t (jBlock d L N₀ 1 1 b.1) *
          t (jBlock d L N₀ 1 1 (bondTip b)))) :=
  baseSqrt_log_principal G hν ha hα hη0 hη (baseCube_param_mem_of_norm_le G hρη ht) e he

/-- The same on the cube polydiscs about a real point. -/
theorem baseCube_sqrt_log_principal_close {ε : ℝ} (hε0 : 0 ≤ ε) (hεη : 3 * ε ≤ η)
    {t : Torus d (N₀ * L ^ (1 - 1)) → ℂ}
    (ht : ∀ x ∈ G.Ω 1, ∃ r : ℝ, 0 ≤ r ∧ r ≤ 1 ∧
      ‖t (jBlock d L N₀ 1 1 x) - (r : ℂ)‖ ≤ ε) :
    sqrtMat (baseOp N (fun z i => (e z i : ℂ)) (baseHamiltonian G a ν α
        (fun b : FineBond d L N₀ => t (jBlock d L N₀ 1 1 b.1) *
          t (jBlock d L N₀ 1 1 (bondTip b))))) *
      sqrtMat (baseOp N (fun z i => (e z i : ℂ)) (baseHamiltonian G a ν α
        (fun b : FineBond d L N₀ => t (jBlock d L N₀ 1 1 b.1) *
          t (jBlock d L N₀ 1 1 (bondTip b))))) =
      (baseOp N (fun z i => (e z i : ℂ)) (baseHamiltonian G a ν α
        (fun b : FineBond d L N₀ => t (jBlock d L N₀ 1 1 b.1) *
          t (jBlock d L N₀ 1 1 (bondTip b)))))⁻¹ ∧
    NormedSpace.exp (logMat (baseOp N (fun z i => (e z i : ℂ)) (baseHamiltonian G a ν α
        (fun b : FineBond d L N₀ => t (jBlock d L N₀ 1 1 b.1) *
          t (jBlock d L N₀ 1 1 (bondTip b)))))) =
      baseOp N (fun z i => (e z i : ℂ)) (baseHamiltonian G a ν α
        (fun b : FineBond d L N₀ => t (jBlock d L N₀ 1 1 b.1) *
          t (jBlock d L N₀ 1 1 (bondTip b)))) :=
  baseSqrt_log_principal G hν ha hα hη0 hη
    (baseCube_param_mem_of_close G hε0 (by linarith [eta_le_one hη]) hεη ht) e he

/-- **Exponential decay on the cube discs** (BASE-KERNEL-3 (1.7)): the rate
`baseDecayRate d L ν` does not depend on the volume, the cube parameters, `α` or `e`. -/
theorem baseCube_decay_disc {ρ : ℝ} (hρη : ρ ^ 2 ≤ η)
    {t : Torus d (N₀ * L ^ (1 - 1)) → ℂ}
    (ht : ∀ x ∈ G.Ω 1, ‖t (jBlock d L N₀ 1 1 x)‖ ≤ ρ) (z w : G.Ω 1) :
    (∀ x : ℝ, 0 ≤ x →
      ‖blockOf (baseResolvent N (fun z i => (e z i : ℂ)) (baseHamiltonian G a ν α
        (fun b : FineBond d L N₀ => t (jBlock d L N₀ 1 1 b.1) *
          t (jBlock d L N₀ 1 1 (bondTip b)))) x) z w‖ ≤
        (baseCoercivity L / 4 + x)⁻¹ * Real.exp (-baseDecayRate d L ν * siteDist G z w)) ∧
    ‖blockOf (sqrtMat (baseOp N (fun z i => (e z i : ℂ)) (baseHamiltonian G a ν α
        (fun b : FineBond d L N₀ => t (jBlock d L N₀ 1 1 b.1) *
          t (jBlock d L N₀ 1 1 (bondTip b)))))) z w‖ ≤
      Real.sqrt (4 / baseCoercivity L) * Real.exp (-baseDecayRate d L ν * siteDist G z w) :=
  ⟨fun _ hx => baseResolvent_decay G hν ha hα hη0 hη (baseCube_param_mem_of_norm_le G hρη ht)
      e he hx z w,
   baseSqrt_decay G hν ha hα hη0 hη (baseCube_param_mem_of_norm_le G hρη ht) e he z w⟩

/-- Exponential decay on the cube polydiscs about a real point. -/
theorem baseCube_decay_close {ε : ℝ} (hε0 : 0 ≤ ε) (hεη : 3 * ε ≤ η)
    {t : Torus d (N₀ * L ^ (1 - 1)) → ℂ}
    (ht : ∀ x ∈ G.Ω 1, ∃ r : ℝ, 0 ≤ r ∧ r ≤ 1 ∧
      ‖t (jBlock d L N₀ 1 1 x) - (r : ℂ)‖ ≤ ε) (z w : G.Ω 1) :
    (∀ x : ℝ, 0 ≤ x →
      ‖blockOf (baseResolvent N (fun z i => (e z i : ℂ)) (baseHamiltonian G a ν α
        (fun b : FineBond d L N₀ => t (jBlock d L N₀ 1 1 b.1) *
          t (jBlock d L N₀ 1 1 (bondTip b)))) x) z w‖ ≤
        (baseCoercivity L / 4 + x)⁻¹ * Real.exp (-baseDecayRate d L ν * siteDist G z w)) ∧
    ‖blockOf (sqrtMat (baseOp N (fun z i => (e z i : ℂ)) (baseHamiltonian G a ν α
        (fun b : FineBond d L N₀ => t (jBlock d L N₀ 1 1 b.1) *
          t (jBlock d L N₀ 1 1 (bondTip b)))))) z w‖ ≤
      Real.sqrt (4 / baseCoercivity L) * Real.exp (-baseDecayRate d L ν * siteDist G z w) := by
  have hs := baseCube_param_mem_of_close G hε0 (by linarith [eta_le_one hη]) hεη ht
  exact ⟨fun _ hx => baseResolvent_decay G hν ha hα hη0 hη hs e he hx z w,
    baseSqrt_decay G hν ha hα hη0 hη hs e he z w⟩

end Discs

section Holomorphy

variable {a : ℕ → ℝ} {ν : ℝ} {α : G.Ω 1 → ℂ} (hν : 0 ≤ ν) (ha : IsAdmissibleWeights 1 a)
  (hα : ∀ z, ‖α z‖ ≤ 1 / (8 * (L : ℝ) ^ 2)) {η : ℝ} (hη0 : 0 ≤ η)
  (hη : η ≤ baseCoercivity L / (8 * d)) (e : G.Ω 1 → Fin N → ℝ) (he : ∀ z, ∑ i, e z i ^ 2 = 1)
  (t₀ v : Torus d (N₀ * L ^ (1 - 1)) → ℂ)

include hν ha hα hη0 hη he

/-- **Holomorphy of the resolvent on the cube discs about the cut point.**  Along every complex
line `z ↦ t₀ + z v` of cube parameters, the entries of `𝒞_{e,x}` are analytic on the open set
where all cube parameters of the chart domain have norm `< ρ`, `ρ² ≤ η ≤ c/(8d)`. -/
theorem baseCube_resolvent_analyticOn_disc {ρ : ℝ} (hρη : ρ ^ 2 ≤ η) {x : ℝ} (hx : 0 ≤ x)
    (p q : G.Ω 1 × Fin N) :
    AnalyticOnNhd ℂ (fun z : ℂ => baseResolvent N (fun z i => (e z i : ℂ))
      (baseHamiltonian G a ν α (fun b : FineBond d L N₀ =>
        (t₀ (jBlock d L N₀ 1 1 b.1) + z * v (jBlock d L N₀ 1 1 b.1)) *
          (t₀ (jBlock d L N₀ 1 1 (bondTip b)) + z * v (jBlock d L N₀ 1 1 (bondTip b))))) x p q)
      {z : ℂ | ∀ y ∈ G.Ω 1,
        ‖t₀ (jBlock d L N₀ 1 1 y) + z * v (jBlock d L N₀ 1 1 y)‖ < ρ} :=
  baseFamily_resolvent_analyticOn G hν ha hα hη0 hη e he
    (fun b z0 => analyticAt_cubeLine_param t₀ v b z0)
    (fun z hz => baseCube_param_mem_of_norm_le G hρη
      (t := fun Q => t₀ Q + z * v Q) (fun y hy => (hz y hy).le)) hx p q

/-- Holomorphy of the resolvent on the cube polydiscs about a real point `r ∈ [0,1]^cubes`. -/
theorem baseCube_resolvent_analyticOn_close {ε : ℝ} (hε0 : 0 ≤ ε) (hεη : 3 * ε ≤ η)
    (r : Torus d (N₀ * L ^ (1 - 1)) → ℝ) (hr : ∀ y ∈ G.Ω 1, 0 ≤ r (jBlock d L N₀ 1 1 y) ∧
      r (jBlock d L N₀ 1 1 y) ≤ 1) {x : ℝ} (hx : 0 ≤ x) (p q : G.Ω 1 × Fin N) :
    AnalyticOnNhd ℂ (fun z : ℂ => baseResolvent N (fun z i => (e z i : ℂ))
      (baseHamiltonian G a ν α (fun b : FineBond d L N₀ =>
        (t₀ (jBlock d L N₀ 1 1 b.1) + z * v (jBlock d L N₀ 1 1 b.1)) *
          (t₀ (jBlock d L N₀ 1 1 (bondTip b)) + z * v (jBlock d L N₀ 1 1 (bondTip b))))) x p q)
      {z : ℂ | ∀ y ∈ G.Ω 1,
        ‖t₀ (jBlock d L N₀ 1 1 y) + z * v (jBlock d L N₀ 1 1 y) -
          (r (jBlock d L N₀ 1 1 y) : ℂ)‖ < ε} :=
  baseFamily_resolvent_analyticOn G hν ha hα hη0 hη e he
    (fun b z0 => analyticAt_cubeLine_param t₀ v b z0)
    (fun z hz => baseCube_param_mem_of_close G hε0 (by linarith [eta_le_one hη]) hεη
      (t := fun Q => t₀ Q + z * v Q)
      (fun y hy => ⟨r (jBlock d L N₀ 1 1 y), (hr y hy).1, (hr y hy).2, (hz y hy).le⟩)) hx p q

variable [Nonempty (G.Ω 1)] [NeZero N]

/-- **Holomorphy of the principal inverse square root on the cube discs about the cut point.** -/
theorem baseCube_sqrt_analyticOn_disc {ρ : ℝ} (hρη : ρ ^ 2 ≤ η) (p q : G.Ω 1 × Fin N) :
    AnalyticOnNhd ℂ (fun z : ℂ => sqrtMat (baseOp N (fun z i => (e z i : ℂ))
      (baseHamiltonian G a ν α (fun b : FineBond d L N₀ =>
        (t₀ (jBlock d L N₀ 1 1 b.1) + z * v (jBlock d L N₀ 1 1 b.1)) *
          (t₀ (jBlock d L N₀ 1 1 (bondTip b)) + z * v (jBlock d L N₀ 1 1 (bondTip b)))))) p q)
      {z : ℂ | ∀ y ∈ G.Ω 1,
        ‖t₀ (jBlock d L N₀ 1 1 y) + z * v (jBlock d L N₀ 1 1 y)‖ < ρ} :=
  baseFamily_sqrt_analyticOn G hν ha hα hη0 hη e he
    (fun b z0 => analyticAt_cubeLine_param t₀ v b z0) (isOpen_cubeLine_disc G ρ t₀ v)
    (fun z hz => baseCube_param_mem_of_norm_le G hρη
      (t := fun Q => t₀ Q + z * v Q) (fun y hy => (hz y hy).le)) p q

/-- **Holomorphy of the principal logarithm on the cube discs about the cut point.** -/
theorem baseCube_log_analyticOn_disc {ρ : ℝ} (hρη : ρ ^ 2 ≤ η) (p q : G.Ω 1 × Fin N) :
    AnalyticOnNhd ℂ (fun z : ℂ => logMat (baseOp N (fun z i => (e z i : ℂ))
      (baseHamiltonian G a ν α (fun b : FineBond d L N₀ =>
        (t₀ (jBlock d L N₀ 1 1 b.1) + z * v (jBlock d L N₀ 1 1 b.1)) *
          (t₀ (jBlock d L N₀ 1 1 (bondTip b)) + z * v (jBlock d L N₀ 1 1 (bondTip b)))))) p q)
      {z : ℂ | ∀ y ∈ G.Ω 1,
        ‖t₀ (jBlock d L N₀ 1 1 y) + z * v (jBlock d L N₀ 1 1 y)‖ < ρ} :=
  baseFamily_log_analyticOn G hν ha hα hη0 hη e he
    (fun b z0 => analyticAt_cubeLine_param t₀ v b z0) (isOpen_cubeLine_disc G ρ t₀ v)
    (fun z hz => baseCube_param_mem_of_norm_le G hρη
      (t := fun Q => t₀ Q + z * v Q) (fun y hy => (hz y hy).le)) p q

/-- Holomorphy of the principal inverse square root on the polydiscs about a real point. -/
theorem baseCube_sqrt_analyticOn_close {ε : ℝ} (hε0 : 0 ≤ ε) (hεη : 3 * ε ≤ η)
    (r : Torus d (N₀ * L ^ (1 - 1)) → ℝ) (hr : ∀ y ∈ G.Ω 1, 0 ≤ r (jBlock d L N₀ 1 1 y) ∧
      r (jBlock d L N₀ 1 1 y) ≤ 1) (p q : G.Ω 1 × Fin N) :
    AnalyticOnNhd ℂ (fun z : ℂ => sqrtMat (baseOp N (fun z i => (e z i : ℂ))
      (baseHamiltonian G a ν α (fun b : FineBond d L N₀ =>
        (t₀ (jBlock d L N₀ 1 1 b.1) + z * v (jBlock d L N₀ 1 1 b.1)) *
          (t₀ (jBlock d L N₀ 1 1 (bondTip b)) + z * v (jBlock d L N₀ 1 1 (bondTip b)))))) p q)
      {z : ℂ | ∀ y ∈ G.Ω 1,
        ‖t₀ (jBlock d L N₀ 1 1 y) + z * v (jBlock d L N₀ 1 1 y) -
          (r (jBlock d L N₀ 1 1 y) : ℂ)‖ < ε} :=
  baseFamily_sqrt_analyticOn G hν ha hα hη0 hη e he
    (fun b z0 => analyticAt_cubeLine_param t₀ v b z0) (isOpen_cubeLine_close G ε r t₀ v)
    (fun z hz => baseCube_param_mem_of_close G hε0 (by linarith [eta_le_one hη]) hεη
      (t := fun Q => t₀ Q + z * v Q)
      (fun y hy => ⟨r (jBlock d L N₀ 1 1 y), (hr y hy).1, (hr y hy).2, (hz y hy).le⟩)) p q

/-- Holomorphy of the principal logarithm on the polydiscs about a real point. -/
theorem baseCube_log_analyticOn_close {ε : ℝ} (hε0 : 0 ≤ ε) (hεη : 3 * ε ≤ η)
    (r : Torus d (N₀ * L ^ (1 - 1)) → ℝ) (hr : ∀ y ∈ G.Ω 1, 0 ≤ r (jBlock d L N₀ 1 1 y) ∧
      r (jBlock d L N₀ 1 1 y) ≤ 1) (p q : G.Ω 1 × Fin N) :
    AnalyticOnNhd ℂ (fun z : ℂ => logMat (baseOp N (fun z i => (e z i : ℂ))
      (baseHamiltonian G a ν α (fun b : FineBond d L N₀ =>
        (t₀ (jBlock d L N₀ 1 1 b.1) + z * v (jBlock d L N₀ 1 1 b.1)) *
          (t₀ (jBlock d L N₀ 1 1 (bondTip b)) + z * v (jBlock d L N₀ 1 1 (bondTip b)))))) p q)
      {z : ℂ | ∀ y ∈ G.Ω 1,
        ‖t₀ (jBlock d L N₀ 1 1 y) + z * v (jBlock d L N₀ 1 1 y) -
          (r (jBlock d L N₀ 1 1 y) : ℂ)‖ < ε} :=
  baseFamily_log_analyticOn G hν ha hα hη0 hη e he
    (fun b z0 => analyticAt_cubeLine_param t₀ v b z0) (isOpen_cubeLine_close G ε r t₀ v)
    (fun z hz => baseCube_param_mem_of_close G hε0 (by linarith [eta_le_one hη]) hεη
      (t := fun Q => t₀ Q + z * v Q)
      (fun y hy => ⟨r (jBlock d L N₀ 1 1 y), (hr y hy).1, (hr y hy).2, (hz y hy).le⟩)) p q

end Holomorphy

section Cut

open Classical Balaban.Localization

/-- The principal logarithm respects a block compression (as `sqrtMat_submatrix_block`). -/
theorem logMat_submatrix_block {κ : Type*} [Fintype κ] [DecidableEq κ] (P : κ → Prop)
    [Nonempty κ] [Nonempty {p : κ // P p}] {M : Matrix κ κ ℂ} (hM : BlockDiag P M)
    (hR : ResOK M) (hRI : ResOK (M.submatrix
      (Subtype.val : {p : κ // P p} → κ) (Subtype.val : {p : κ // P p} → κ)))
    (p q : {p : κ // P p}) :
    logMat M p.1 q.1 = logMat (M.submatrix
      (Subtype.val : {p : κ // P p} → κ) (Subtype.val : {p : κ // P p} → κ)) p q := by
  simp only [logMat, intMat, Matrix.neg_apply]
  congr 1
  refine MeasureTheory.integral_congr_ae ?_
  refine (MeasureTheory.ae_restrict_iff' measurableSet_Ioi).2
    (Filter.Eventually.of_forall fun y hy => ?_)
  have hy0 : 0 ≤ y := le_of_lt hy
  beta_reduce
  have hsub : ((y : ℂ) • (1 : Matrix κ κ ℂ) + M).submatrix
      (Subtype.val : {p : κ // P p} → κ) Subtype.val =
      (y : ℂ) • (1 : Matrix {p : κ // P p} {p : κ // P p} ℂ) +
        M.submatrix Subtype.val Subtype.val := by
    ext a b
    simp only [Matrix.submatrix_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply]
    congr 1
    simp only [Subtype.ext_iff]
  have hinv := inv_submatrix_block P (blockDiag_add_smul_one hM y) (hR y hy0)
    (hsub.symm ▸ hRI y hy0) p q
  rw [hsub] at hinv
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, hinv, Subtype.ext_iff]

variable {a : ℕ → ℝ} {ν : ℝ} {α α' : G.Ω 1 → ℂ} {U : Set (Torus d (N₀ * L ^ 1))}

/-- **Cutting the cubes outside `U`.**  If the parameters of all cubes outside `U` vanish, every
bond joining `U` to its complement carries the parameter `0`. -/
theorem baseCube_crossZero {t : Torus d (N₀ * L ^ (1 - 1)) → ℂ}
    (hout : ∀ x ∈ G.Ω 1, x ∉ U → t (jBlock d L N₀ 1 1 x) = 0) :
    CrossZero G U (fun b : FineBond d L N₀ => t (jBlock d L N₀ 1 1 b.1) *
      t (jBlock d L N₀ 1 1 (bondTip b))) := by
  intro b hb hcross
  obtain ⟨h1, h2⟩ := baseCutBonds_endpoints_mem G hb
  beta_reduce
  by_cases hu : b.1 ∈ U
  · rw [hout _ h2 (hcross.1 hu), mul_zero]
  · rw [hout _ h1 hu, zero_mul]

/-- With the parameters of the cubes outside `U` equal to `0`, `A_e(s)` is a direct sum over `U`
and its complement (`U` a union of first blocks). -/
theorem baseCube_blockDiag (hU : IsFirstBlockUnion G U)
    {t : Torus d (N₀ * L ^ (1 - 1)) → ℂ}
    (hout : ∀ x ∈ G.Ω 1, x ∉ U → t (jBlock d L N₀ 1 1 x) = 0) (e : G.Ω 1 → Fin N → ℝ) :
    BlockDiag (fun p : G.Ω 1 × Fin N => (p.1 : Torus d (N₀ * L ^ 1)) ∈ U)
      (baseOp N (fun z i => (e z i : ℂ)) (baseHamiltonian G a ν α
        (fun b : FineBond d L N₀ => t (jBlock d L N₀ 1 1 b.1) *
          t (jBlock d L N₀ 1 1 (bondTip b))))) :=
  baseOp_blockDiag G hU a ν α (baseCube_crossZero G hout) e

theorem baseCube_agreeOn {t t' : Torus d (N₀ * L ^ (1 - 1)) → ℂ} {e e' : G.Ω 1 → Fin N → ℝ}
    (hα : ∀ z : G.Ω 1, (z : Torus d (N₀ * L ^ 1)) ∈ U → α z = α' z)
    (he : ∀ z : G.Ω 1, (z : Torus d (N₀ * L ^ 1)) ∈ U → e z = e' z)
    (ht : ∀ x ∈ G.Ω 1, x ∈ U → t (jBlock d L N₀ 1 1 x) = t' (jBlock d L N₀ 1 1 x)) :
    AgreeOn G U (fun b : FineBond d L N₀ => t (jBlock d L N₀ 1 1 b.1) *
        t (jBlock d L N₀ 1 1 (bondTip b)))
      (fun b : FineBond d L N₀ => t' (jBlock d L N₀ 1 1 b.1) *
        t' (jBlock d L N₀ 1 1 (bondTip b))) α α' e e' where
  alpha := hα
  bg := he
  param b hb h1 h2 := by
    obtain ⟨g1, g2⟩ := baseCutBonds_endpoints_mem G hb
    rw [ht _ g1 h1, ht _ g2 h2]

variable [Nonempty (G.Ω 1)] [NeZero N]
variable (hU : IsFirstBlockUnion G U) (hν : 0 ≤ ν) (ha : IsAdmissibleWeights 1 a)
  (hα : ∀ z, ‖α z‖ ≤ 1 / (8 * (L : ℝ) ^ 2)) (hα' : ∀ z, ‖α' z‖ ≤ 1 / (8 * (L : ℝ) ^ 2))
  {η : ℝ} (hη0 : 0 ≤ η) (hη : η ≤ baseCoercivity L / (8 * d))
  {t t' : Torus d (N₀ * L ^ (1 - 1)) → ℂ}
  (hs : (fun b : FineBond d L N₀ => t (jBlock d L N₀ 1 1 b.1) *
      t (jBlock d L N₀ 1 1 (bondTip b))) ∈ baseParamNbhd G η)
  (hs' : (fun b : FineBond d L N₀ => t' (jBlock d L N₀ 1 1 b.1) *
      t' (jBlock d L N₀ 1 1 (bondTip b))) ∈ baseParamNbhd G η)
  (hout : ∀ x ∈ G.Ω 1, x ∉ U → t (jBlock d L N₀ 1 1 x) = 0)
  (hout' : ∀ x ∈ G.Ω 1, x ∉ U → t' (jBlock d L N₀ 1 1 x) = 0)
  {e e' : G.Ω 1 → Fin N → ℝ} (he : ∀ z, ∑ i, e z i ^ 2 = 1) (he' : ∀ z, ∑ i, e' z i ^ 2 = 1)
  (hαU : ∀ z : G.Ω 1, (z : Torus d (N₀ * L ^ 1)) ∈ U → α z = α' z)
  (heU : ∀ z : G.Ω 1, (z : Torus d (N₀ * L ^ 1)) ∈ U → e z = e' z)
  (htU : ∀ x ∈ G.Ω 1, x ∈ U → t (jBlock d L N₀ 1 1 x) = t' (jBlock d L N₀ 1 1 x))
  (p q : G.Ω 1 × Fin N) (hp : (p.1 : Torus d (N₀ * L ^ 1)) ∈ U)
  (hq : (q.1 : Torus d (N₀ * L ^ 1)) ∈ U)

include hU hν ha hα hα' hη0 hη hs hs' hout hout' he he' hαU heU htU hp hq

/-- **Exact component locality of the cube family: resolvent.**  For parameters vanishing on the
cubes outside the union of first blocks `U`, the `U × U` entries of `𝒞_{e,x}(s)` depend only on
the data `(α, e, t)` on `U`. -/
theorem baseCube_resolvent_local {x : ℝ} (hx : 0 ≤ x) :
    baseResolvent N (fun z i => (e z i : ℂ)) (baseHamiltonian G a ν α
      (fun b : FineBond d L N₀ => t (jBlock d L N₀ 1 1 b.1) *
        t (jBlock d L N₀ 1 1 (bondTip b)))) x p q =
    baseResolvent N (fun z i => (e' z i : ℂ)) (baseHamiltonian G a ν α'
      (fun b : FineBond d L N₀ => t' (jBlock d L N₀ 1 1 b.1) *
        t' (jBlock d L N₀ 1 1 (bondTip b)))) x p q :=
  baseResolvent_local G hU hν ha hα hα' hη0 hη hs hs' (baseCube_crossZero G hout)
    (baseCube_crossZero G hout') he he' (baseCube_agreeOn G hαU heU htU) hx p q hp hq

/-- Exact component locality of the cube family: principal inverse square root. -/
theorem baseCube_sqrt_local :
    sqrtMat (baseOp N (fun z i => (e z i : ℂ)) (baseHamiltonian G a ν α
      (fun b : FineBond d L N₀ => t (jBlock d L N₀ 1 1 b.1) *
        t (jBlock d L N₀ 1 1 (bondTip b))))) p q =
    sqrtMat (baseOp N (fun z i => (e' z i : ℂ)) (baseHamiltonian G a ν α'
      (fun b : FineBond d L N₀ => t' (jBlock d L N₀ 1 1 b.1) *
        t' (jBlock d L N₀ 1 1 (bondTip b))))) p q :=
  baseSqrt_local G hU hν ha hα hα' hη0 hη hs hs' (baseCube_crossZero G hout)
    (baseCube_crossZero G hout') he he' (baseCube_agreeOn G hαU heU htU) p q hp hq

/-- Exact component locality of the cube family: principal logarithm. -/
theorem baseCube_log_local :
    logMat (baseOp N (fun z i => (e z i : ℂ)) (baseHamiltonian G a ν α
      (fun b : FineBond d L N₀ => t (jBlock d L N₀ 1 1 b.1) *
        t (jBlock d L N₀ 1 1 (bondTip b))))) p q =
    logMat (baseOp N (fun z i => (e' z i : ℂ)) (baseHamiltonian G a ν α'
      (fun b : FineBond d L N₀ => t' (jBlock d L N₀ 1 1 b.1) *
        t' (jBlock d L N₀ 1 1 (bondTip b))))) p q :=
  baseLog_local G hU hν ha hα hα' hη0 hη hs hs' (baseCube_crossZero G hout)
    (baseCube_crossZero G hout') he he' (baseCube_agreeOn G hαU heU htU) p q hp hq

end Cut

section Component

open Classical Balaban.Localization

variable {a : ℕ → ℝ} {ν : ℝ} {α : G.Ω 1 → ℂ} {U : Set (Torus d (N₀ * L ^ 1))}
  [Nonempty (G.Ω 1)] [NeZero N]
variable (hU : IsFirstBlockUnion G U) (hU0 : ∃ z : G.Ω 1, (z : Torus d (N₀ * L ^ 1)) ∈ U)
  (hν : 0 ≤ ν) (ha : IsAdmissibleWeights 1 a)
  (hα : ∀ z, ‖α z‖ ≤ 1 / (8 * (L : ℝ) ^ 2)) {η : ℝ} (hη0 : 0 ≤ η)
  (hη : η ≤ baseCoercivity L / (8 * d)) {t : Torus d (N₀ * L ^ (1 - 1)) → ℂ}
  (hs : (fun b : FineBond d L N₀ => t (jBlock d L N₀ 1 1 b.1) *
      t (jBlock d L N₀ 1 1 (bondTip b))) ∈ baseParamNbhd G η)
  (hout : ∀ x ∈ G.Ω 1, x ∉ U → t (jBlock d L N₀ 1 1 x) = 0)
  (e : G.Ω 1 → Fin N → ℝ) (he : ∀ z, ∑ i, e z i ^ 2 = 1)

include hU hU0 hν ha hα hη0 hη hs hout he

/-- **The cut component operator of the cube family.**  With the parameters of the cubes outside
the union of first blocks `U` equal to `0`, the principal submatrix `A_U` of `A_e(s)` on `U` is
coercive with margin `c/2`, has the Stieltjes inverse square root and the principal logarithm,
and `A_e(s)` is block diagonal for `U`. -/
theorem baseCube_component_covariance :
    let A := baseOp N (fun z i => (e z i : ℂ)) (baseHamiltonian G a ν α
      (fun b : FineBond d L N₀ => t (jBlock d L N₀ 1 1 b.1) *
        t (jBlock d L N₀ 1 1 (bondTip b))))
    let P : G.Ω 1 × Fin N → Prop := fun p => (p.1 : Torus d (N₀ * L ^ 1)) ∈ U
    let I := {p : G.Ω 1 × Fin N // P p}
    let A_U : Matrix I I ℂ := A.submatrix Subtype.val Subtype.val
    BlockDiag P A ∧ IsCoercive A_U (baseCoercivity L / 2) ∧ ResOK A_U ∧
      sqrtMat A_U * sqrtMat A_U = A_U⁻¹ ∧ NormedSpace.exp (logMat A_U) = A_U := by
  intro A P I A_U
  have hcoer : IsCoercive A (baseCoercivity L / 2) :=
    baseOp_isCoercive_of_close G hν ha hα hη0 hη hs e he
  have hcomp : IsCoercive A_U (baseCoercivity L / 2) :=
    isCoercive_submatrix hcoer Subtype.val Subtype.val_injective
  have hc : 0 < baseCoercivity L / 2 :=
    half_pos (baseCoercivity_pos (Nat.pos_of_ne_zero (NeZero.ne L)))
  have hres : ResOK A_U := by
    intro x hx
    have hcx : 0 < baseCoercivity L / 2 + x := by linarith
    rw [add_comm]
    exact isUnit_of_isCoercive hcx (hcomp.add_smul_one x)
  have : Nonempty I := by
    obtain ⟨z, hzU⟩ := hU0
    exact ⟨⟨(z, 0), hzU⟩⟩
  exact ⟨baseCube_blockDiag G hU hout e, hcomp, hres, sqrtMat_mul_self hres, exp_logMat hres⟩

/-- **Exact agreement with the cut component operator** (the cube analogue of
`baseSector_component_entries`): the `U × U` entries of `A_e(s)⁻¹`, of its principal inverse square
root and of its principal logarithm are those of the component operator `A_U`. -/
theorem baseCube_component_entries :
    let A := baseOp N (fun z i => (e z i : ℂ)) (baseHamiltonian G a ν α
      (fun b : FineBond d L N₀ => t (jBlock d L N₀ 1 1 b.1) *
        t (jBlock d L N₀ 1 1 (bondTip b))))
    let P : G.Ω 1 × Fin N → Prop := fun p => (p.1 : Torus d (N₀ * L ^ 1)) ∈ U
    let I := {p : G.Ω 1 × Fin N // P p}
    let A_U : Matrix I I ℂ := A.submatrix Subtype.val Subtype.val
    ∀ p q : I, A⁻¹ p.1 q.1 = A_U⁻¹ p q ∧ sqrtMat A p.1 q.1 = sqrtMat A_U p q ∧
      logMat A p.1 q.1 = logMat A_U p q := by
  intro A P I A_U
  obtain ⟨hblock, _, hRI, _, _⟩ := baseCube_component_covariance G hU hU0 hν ha hα hη0 hη hs hout e he
  have hR : ResOK A := resOK_baseOp G hν ha hα hη0 hη hs e he
  have : Nonempty I := by
    obtain ⟨z, hzU⟩ := hU0
    exact ⟨⟨(z, 0), hzU⟩⟩
  intro p q
  refine ⟨?_, sqrtMat_submatrix_block P hblock hR hRI p q,
    logMat_submatrix_block P hblock hR hRI p q⟩
  apply inv_submatrix_block P hblock
  · simpa using hR 0 le_rfl
  · simpa using hRI 0 le_rfl

end Component

end Balaban.LargeField.Base
