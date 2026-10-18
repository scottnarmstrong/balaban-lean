/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.LocalSetDetConn
public import Balaban.Localization.DecCovCross
public import Balaban.Fluctuation.LocalPairDecBg
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The determinant of two generating sets on a common region: `decLog` and the rooted trace

P3 p. 78: the term of a localization domain is unchanged when the generating set is replaced by one
agreeing with it on the domain, the cut parameters being `0` off the domain.  For the determinant
of the step this is a statement about the decoupled logarithm `𝕃(s)` and the rooted trace of a
unit block, for two generating sets `H` (the step) and `H'` (a local generating set) whose cut
operators, backgrounds and unit lattices agree on a set `T` of sites (at a cut point, `T` is the
region `Yreg` of the active centres).

* `decLog_block_cross`: the entries of `𝕃(s) = log a_k (1 - P) + log (a_k + b) P -
  ∫₀^∞ (C_x(s) - A_{k,x}) dx` at coarse indices matched by injections `e`, `e'` agree, under the
  hypotheses of the landed `Dec2.decCov_block_cross` for every `x > 0` (no integrability is
  needed: the integrands agree pointwise);
* `rootTrace_cross`: the rooted traces of matched sets of coarse indices agree.

The hypotheses are those of `Dec2.decCov_block_cross` for the self covers `coverOf H`,
`coverOf H'` (the landed objects of one generating set are those of its self cover,
`Dec2.decCov_self`).
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization Balaban.Analysis
  Balaban.SmallField Finset Matrix MeasureTheory

/-! ### The decoupled logarithm of two generating sets -/

section LogCross

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱ' : ℝ}
variable {H : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
  {H' : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ'}
variable {a : ℕ → ℝ} {aT ν Cx Cx' : ℝ} {α : H.Ω 1 → ℂ} {α' : H'.Ω 1 → ℂ}
  {s s' : ℕ × CTorus d L N₁ m₁ (k + 1) → ℂ} {T : Finset (CTorus d L N₁ m₁ (k + 1))}
  {φ φ' : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ}

omit [NeZero N₁] [NeZero L] in
/-- The entries of `liftOp N P` at matched coarse indices agree when those of `P` do. -/
theorem liftOp_apply_cross {κι κι' UK : Type*} {P : Matrix κι κι ℂ} {P' : Matrix κι' κι' ℂ}
    (e : UK → κι) (e' : UK → κι') (hPP : ∀ v w : UK, P' (e' v) (e' w) = P (e v) (e w))
    (v w : UK) (i j : Fin N) :
    liftOp N P' (e' v, i) (e' w, j) = liftOp N P (e v, i) (e w, j) := by
  unfold liftOp
  simp only [hPP v w]

omit [NeZero N₁] [NeZero L] in
/-- The entries of the identity at matched coarse indices agree (`e`, `e'` injective). -/
theorem one_apply_cross {κι κι' UK : Type*} [DecidableEq κι] [DecidableEq κι']
    (e : UK → κι) (e' : UK → κι') (hei : Function.Injective e) (hei' : Function.Injective e')
    (v w : UK) (i j : Fin N) :
    (1 : Matrix (κι' × Fin N) (κι' × Fin N) ℂ) (e' v, i) (e' w, j) =
      (1 : Matrix (κι × Fin N) (κι × Fin N) ℂ) (e v, i) (e w, j) := by
  rw [Matrix.one_apply, Matrix.one_apply]
  have h : (e' v, i) = (e' w, j) ↔ (e v, i) = (e w, j) := by
    simp only [Prod.mk.injEq, hei.eq_iff, hei'.eq_iff]
  split_ifs with h1 h2 h2
  · rfl
  · exact absurd (h.1 h1) h2
  · exact absurd (h.2 h2) h1
  · rfl

omit [NeZero N₁] [NeZero L] in
/-- The entries of the baseline `A_{k,x}` at matched coarse indices agree. -/
theorem covA_apply_cross {κι κι' UK : Type*} [DecidableEq κι] [DecidableEq κι']
    {P : Matrix κι κι ℂ} {P' : Matrix κι' κι' ℂ} (e : UK → κι) (e' : UK → κι')
    (hei : Function.Injective e) (hei' : Function.Injective e')
    (hPP : ∀ v w : UK, P' (e' v) (e' w) = P (e v) (e w)) (c b x : ℝ) (v w : UK) (i j : Fin N) :
    covA c b x (liftOp N P') (e' v, i) (e' w, j) = covA c b x (liftOp N P) (e v, i) (e w, j) := by
  unfold covA
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul,
    one_apply_cross (N := N) e e' hei hei' v w i j, liftOp_apply_cross (N := N) e e' hPP v w i j]

/-- **The entries of the decoupled logarithm of two generating sets agree** at matched coarse
indices, under the hypotheses of `Dec2.decCov_block_cross` (for the self covers `coverOf H`,
`coverOf H'`) for every `x > 0`. -/
theorem decLog_block_cross {κι κι' UK : Type*} [Fintype κι] [DecidableEq κι] [Fintype κι']
    [DecidableEq κι'] [Fintype UK]
    (S : Dec2.XCover (coverOf H) H a aT ν Cx) (S' : Dec2.XCover (coverOf H') H' a aT ν Cx')
    (hF : Dec2.FootLocalGeom (coverOf H)) (hF' : Dec2.FootLocalGeom (coverOf H'))
    (hαA : AdmPot H α) (hαB : AdmPot H' α')
    (hlay : ∀ y ∈ T, ∀ n, 1 ≤ n → n ≤ k + 1 → (y ∈ H.layer n ↔ y ∈ H'.layer n))
    (hU : ∀ x : ℝ, 0 < x → IsUnit (1 - Dec2.Kcalx (coverOf H) H a aT x ν α s))
    (hU' : ∀ x : ℝ, 0 < x → IsUnit (1 - Dec2.Kcalx (coverOf H') H' a aT x ν α' s'))
    (hdich : ∀ q ∈ (coverOf H).cubeIdx, (coverOf H).sProd s q ≠ 0 →
      SubI H (intBox q) T ∨ DisjI H (intBox q) T)
    (hdich' : ∀ q ∈ (coverOf H').cubeIdx, (coverOf H').sProd s' q ≠ 0 →
      SubI H' (intBox q) T ∨ DisjI H' (intBox q) T)
    (hin : ∀ q ∈ Dec2.innerCentres (coverOf H) H T, (coverOf H).sProd s q ≠ 0 →
      q ∈ Dec2.innerCentres (coverOf H') H' T ∧
      (coverOf H').sProd s' q = (coverOf H).sProd s q ∧
      (∀ x₀ ∈ intBox q, ∀ y : CTorus d L N₁ m₁ (k + 1),
        (y = x₀ ∨ ∃ μ : Fin d, y = x₀ + Pi.single μ 1 ∨ y = x₀ - Pi.single μ 1) →
          ∀ n, 1 ≤ n → n ≤ k + 1 → (y ∈ H.layer n ↔ y ∈ H'.layer n)) ∧
      (∀ x₀ ∈ intBox q, (coverOf H).chi q x₀ = (coverOf H').chi q x₀))
    (hin' : ∀ q ∈ Dec2.innerCentres (coverOf H') H' T, (coverOf H').sProd s' q ≠ 0 →
      q ∈ Dec2.innerCentres (coverOf H) H T ∧ (coverOf H).sProd s q ≠ 0)
    (hα : ∀ (x₀ : CTorus d L N₁ m₁ (k + 1)) (hx : x₀ ∈ H.Ω 1) (hx' : x₀ ∈ H'.Ω 1), x₀ ∈ T →
      α ⟨x₀, hx⟩ = α' ⟨x₀, hx'⟩)
    (hφ : ∀ y ∈ T, φ' y = φ y)
    (hH : ∀ x : ℝ, 0 < x → Dec2.HRespects (coverOf H) H a aT x ν α s T)
    (hH' : ∀ x : ℝ, 0 < x → Dec2.HRespects (coverOf H') H' a aT x ν α' s' T)
    (hM : ∀ x : ℝ, 0 < x → IsUnit (Dec2.decM (coverOf H) H a aT x ν α s φ))
    (hM' : ∀ x : ℝ, 0 < x → IsUnit (Dec2.decM (coverOf H') H' a aT x ν α' s' φ'))
    (cκ : κι → Prop) (cκ' : κι' → Prop) (Q : Matrix κι (H.Ω 1) ℂ) (Q' : Matrix κι' (H'.Ω 1) ℂ)
    (P : Matrix κι κι ℂ) (P' : Matrix κι' κι' ℂ) (e : UK → κι) (e' : UK → κι')
    (hei : Function.Injective e) (hei' : Function.Injective e')
    (hes : ∀ κ, cκ κ → ∃ v, e v = κ) (hes' : ∀ κ, cκ' κ → ∃ v, e' v = κ)
    (hec : ∀ v, cκ (e v)) (hec' : ∀ v, cκ' (e' v))
    (hQ : BD cκ (fun y : H.Ω 1 => (y : CTorus d L N₁ m₁ (k + 1)) ∈ T) Q)
    (hQ' : BD cκ' (fun y : H'.Ω 1 => (y : CTorus d L N₁ m₁ (k + 1)) ∈ T) Q')
    (hP : BD cκ cκ P) (hP' : BD cκ' cκ' P')
    (hQQ : ∀ (v : UK) (y : CTorus d L N₁ m₁ (k + 1)) (hy : y ∈ H.Ω 1) (hy' : y ∈ H'.Ω 1),
      y ∈ T → Q' (e' v) ⟨y, hy'⟩ = Q (e v) ⟨y, hy⟩)
    (hPP : ∀ v w : UK, P' (e' v) (e' w) = P (e v) (e w)) (v w : UK) (i j : Fin N) :
    decLog H' a aT ν α' s' φ' Q' P' (e' v, i) (e' w, j) =
      decLog H a aT ν α s φ Q P (e v, i) (e w, j) := by
  unfold decLog
  simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
    one_apply_cross (N := N) e e' hei hei' v w i j, liftOp_apply_cross (N := N) e e' hPP v w i j]
  congr 1
  unfold intMat
  refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
  have hx0 : 0 < x := hx
  simp only [Matrix.sub_apply]
  rw [covA_apply_cross (N := N) e e' hei hei' hPP]
  congr 1
  exact Dec2.decCov_block_cross S S' hF hF' hαA hαB hx0.le hlay (hU x hx0) (hU' x hx0) hdich
    hdich' hin hin' hα hφ (hH x hx0) (hH' x hx0) (hM x hx0) (hM' x hx0) cκ cκ' Q Q' P P' e e'
    hei hei' hes hes' hec hec' hQ hQ' hP hP' hQQ hPP v w i j

end LogCross

end Balaban.Fluctuation
