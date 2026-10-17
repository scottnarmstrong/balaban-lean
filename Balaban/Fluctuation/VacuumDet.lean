/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.DetOutputTerms
public import Balaban.Fluctuation.StepComplexProp26Agree
public import Balaban.Localization.DecoupledCovReal
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The vacuum value of the determinant terms (OPEN-VACUUM of `notes/phase1/DETFIT.md` §1)

The determinant part of the new terms of a step is a family `t_z(D, T)` of localized terms, one
record `DetExpansionLocC S m₀ z ε κ'' c_det` for each root `z` of `T^{(k+1)}_1`.  At a real datum
`D₀` of the chart (the vacuum datum is one), their total is `½ log det C^{(k)}` at `D₀`, a real
number, so the vacuum part absorbed into `E_{k+1}` (P4 (4.21)) is real, and so is the value of
every root separately:

* `specFun_real_diag_im`: a diagonal entry of `f(A)` for a Hermitian `A` and real `f` is real;
* `sum_detExpansionLocC_term_eq`: `∑_{z,T} t_z(D', T) = ½ log det C^{(k)}` (the analytic branch
  `halfLogDetCC`) at the datum `D'` of the step, for every datum of the chart;
* `sum_detExpansionLocC_term_eq_real`: for real data (the premises of Lemma 2.4 (c),
  `halfLogDetCC_eq`) the total is the real number `halfLogDetC = ½ log det C^{(k)}`;
* `vacuum_det_density`: `∑_{z,T} t_z(D', T) = c_vac |T^{(k+1)}_1|` with the real number
  `c_vac = ½ log det C^{(k)} / |T^{(k+1)}_1|`;
* `sum_detExpansionLocC_term_root_im`: for real data each root contributes a real number,
  `Im ∑_T t_z(D', T) = 0` (the diagonal of the real logarithm of `𝒜`).

Not proved here: that the value of a root at the vacuum datum is independent of the root (only the
covariance under cell-aligned translations is landed, `rootTrace_unitAct`), its independence of the
torus, and its independence of the unit vector of the vacuum for an arbitrary record (for the record
of `exists_detExpansionLocC_rot_real` the terms themselves are invariant).
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization Balaban.SmallField
  Finset Matrix

section Spectral

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {A : Matrix ι ι ℂ}

/-- **The diagonal of a real function of a Hermitian matrix is real**:
`(U diag(f(λ)) U*)_{pp} = ∑_j f(λ_j) |U_{pj}|²`. -/
theorem specFun_real_diag_im (hH : A.IsHermitian) (f : ℝ → ℝ) (p : ι) :
    (specFun hH (fun t => (f t : ℂ)) p p).im = 0 := by
  unfold specFun
  rw [Matrix.mul_apply, Complex.im_sum]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [Matrix.mul_diagonal, Matrix.star_apply]
  set u : ℂ := (hH.eigenvectorUnitary : Matrix ι ι ℂ) p j
  have h : u * (f (hH.eigenvalues j) : ℂ) * star u =
      ((f (hH.eigenvalues j) * Complex.normSq u : ℝ) : ℂ) := by
    rw [mul_comm u, mul_assoc, Complex.star_def, Complex.mul_conj]
    push_cast
    ring
  rw [h, Complex.ofReal_im]

end Spectral

namespace StepSetting

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}
  (S : StepSetting d L N₁ m₁ k N ϱ) {m₀ : ℕ} {eps κ'' cdet : ℝ}

/-- **The total of the determinant terms at the datum of the step**: for a family of records, one
for each root, `∑_z ∑_T t_z(D', T) = ½ log det C^{(k)}` (the analytic branch `halfLogDetCC`
`= -½ ∑_y tr 𝕃(y, y)`), for every datum `D'` of the chart. -/
theorem sum_detExpansionLocC_term_eq
    (E : ∀ z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))), DetExpansionLocC S m₀ z eps κ'' cdet)
    (hD : XiCData S.G' S.a S.ν (k + 1) 1 eps S.D') :
    ∑ z, ∑ T, (E z).term S.D' T = S.halfLogDetCC := by
  rw [← sum_rootTrace_one_eq_halfLogDetCC S]
  exact Finset.sum_congr rfl fun z _ => ((E z).sum_eq S.D' hD).symm

section Real

variable (H : BgHyp d L (k + 1) ϱ S.a S.ν) {δ' : ℝ} (hδ'0 : 0 < δ')
  (hδ' : δ' ≤ thm73C3 d L N / 2) (hD'R : InDomainR S.G' S.ν δ' S.D')
  (hδ0 : 0 < S.δ)
  (hχ : ChiUBounds S.G' S.ν S.δ S.D' (bgField S.G' S.a S.ν S.D') (bgMult S.G' S.a S.ν S.D'))
  (hfam : ∀ x, 0 ≤ x → XData S.G' S.a S.a₁ S.ν x (bgMult S.G' S.a S.ν S.D') 0 (fun _ => 1))
  (hsm : S.δ ^ 2 * smallConstX d L 0 ≤ 1 / 4)

include H hδ'0 hδ' hD'R hδ0 hχ hfam hsm in
/-- **Real data: the vacuum value of the determinant terms is the real `½ log det C^{(k)}`**:
`∑_z ∑_T t_z(D', T) = halfLogDetC` for a real datum `D'` of the chart (Lemma 2.4 (c)). -/
theorem sum_detExpansionLocC_term_eq_real
    (E : ∀ z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))), DetExpansionLocC S m₀ z eps κ'' cdet)
    (hD : XiCData S.G' S.a S.ν (k + 1) 1 eps S.D') :
    ∑ z, ∑ T, (E z).term S.D' T = (S.halfLogDetC : ℂ) := by
  rw [S.sum_detExpansionLocC_term_eq E hD,
    S.halfLogDetCC_eq H hδ'0 hδ' hD'R hδ0 hχ hfam hsm]

include H hδ'0 hδ' hD'R hδ0 hχ hfam hsm in
/-- **The vacuum density of the determinant terms (OPEN-VACUUM, total and reality)**: for a real
datum `D'` of the chart, `∑_z ∑_T t_z(D', T) = c_vac |T^{(k+1)}_1|` with the real number
`c_vac = ½ log det C^{(k)} / |T^{(k+1)}_1|`. -/
theorem vacuum_det_density
    (E : ∀ z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))), DetExpansionLocC S m₀ z eps κ'' cdet)
    (hD : XiCData S.G' S.a S.ν (k + 1) 1 eps S.D') :
    ∑ z, ∑ T, (E z).term S.D' T =
      ((S.halfLogDetC / (Fintype.card (Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1)))) : ℝ) : ℝ) :
          ℂ) *
        ((Fintype.card (Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1)))) : ℝ) : ℂ) := by
  rw [S.sum_detExpansionLocC_term_eq_real H hδ'0 hδ' hD'R hδ0 hχ hfam hsm E hD,
    ← Complex.ofReal_mul]
  have hc : (Fintype.card (Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1)))) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.2 Fintype.card_ne_zero
  rw [div_mul_cancel₀ _ hc]

include H hδ'0 hδ' hD'R hδ0 hχ hfam hsm in
/-- **Real data: each root contributes a real number**: `Im ∑_T t_z(D', T) = 0`.  The sum over
`T` is the trace `-½ ∑_{y ∈ B(z)} tr 𝕃(y, y)` over the block of the root, and the diagonal of the
real logarithm `log 𝒜` of the positive definite `𝒜` is real. -/
theorem sum_detExpansionLocC_term_root_im
    {z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1)))} (E : DetExpansionLocC S m₀ z eps κ'' cdet)
    (hD : XiCData S.G' S.a S.ν (k + 1) 1 eps S.D') :
    (∑ T, E.term S.D' T).im = 0 := by
  rw [← E.sum_eq S.D' hD, rootTrace_one_eq_logAC S z, S.logAC_eq H hδ'0 hδ' hD'R]
  unfold logA
  rw [decLog_one_eq_real hfam (S.constraintField_bg H hδ'0 hδ' hD'R hδ0 hχ) hδ0.le hsm
    (isUnitLatticeB_unit (G := S.G')) (fun w => S.bgMult_real_S H hδ'0 hδ' hD'R w)
    (fun b y => unitQ_real S.G' b y) (fun y i => S.svec_bg_real H hδ'0 hδ' hD'R y i)]
  rw [Complex.mul_im, Complex.im_sum]
  simp only [Complex.im_sum, specFun_real_diag_im, Finset.sum_const_zero, mul_zero, zero_add]
  norm_num

end Real

end StepSetting

end Balaban.Fluctuation
