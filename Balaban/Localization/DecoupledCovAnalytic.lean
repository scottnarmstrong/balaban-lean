/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.DecoupledSqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# I-4c (iii), the integrand: analyticity of `C_x(s)` in `(s, α₀)` for fixed `x`

For every `x ≥ 0` the entries of `C_x(s)` are analytic in the decoupling parameters `s` and the
potential `α₀` on the polydisc of (DG4) (`matAt_decCov`): `Ĝ_{k,x,s}` is analytic by
`dg4x_analytic`'s calculus (`matAt_Gsx`), `H_{k,x}(α₀)` is affine in `α₀`, `M_{x,s}` is invertible
there (`decM_isUnit`), and `C_x(s)` is a finite sum of products of these.
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background Finset Matrix

/-- Analyticity at a point of a rectangular matrix-valued function. -/
def RectAt {E m n : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (M : E → Matrix m n ℂ)
    (e : E) : Prop :=
  ∀ i j, AnalyticAt ℂ (fun e' => M e' i j) e

section Rect

variable {E m n o : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem RectAt.const (C : Matrix m n ℂ) (e : E) : RectAt (fun _ => C) e :=
  fun _ _ => analyticAt_const

theorem RectAt.add {M N : E → Matrix m n ℂ} {e : E} (hM : RectAt M e) (hN : RectAt N e) :
    RectAt (fun e' => M e' + N e') e := fun i j => (hM i j).add (hN i j)

theorem RectAt.sub {M N : E → Matrix m n ℂ} {e : E} (hM : RectAt M e) (hN : RectAt N e) :
    RectAt (fun e' => M e' - N e') e := fun i j => (hM i j).sub (hN i j)

theorem RectAt.mul [Fintype n] {M : E → Matrix m n ℂ} {N : E → Matrix n o ℂ} {e : E}
    (hM : RectAt M e) (hN : RectAt N e) : RectAt (fun e' => M e' * N e') e := by
  intro i j
  simp_rw [Matrix.mul_apply]
  exact Finset.analyticAt_fun_sum _ fun k _ => (hM i k).mul (hN k j)

theorem RectAt.smul_const {M : E → Matrix m n ℂ} {e : E} (c : ℂ) (hM : RectAt M e) :
    RectAt (fun e' => c • M e') e := by
  intro i j
  simp only [Matrix.smul_apply, smul_eq_mul]
  exact analyticAt_const.mul (hM i j)

theorem RectAt.inv [Fintype n] [DecidableEq n] {M : E → Matrix n n ℂ} {e : E}
    (hM : RectAt M e) (hdet : (M e).det ≠ 0) : RectAt (fun e' => (M e')⁻¹) e :=
  fun i j => analyticAt_inv_apply hM hdet i j

theorem RectAt.liftOp {N : ℕ} {ι : Type*} [DecidableEq ι] {M : E → Matrix ι ι ℂ} {e : E}
    (hM : RectAt M e) : RectAt (fun e' => liftOp N (M e')) e := by
  intro p q
  by_cases h : p.2 = q.2
  · simp only [Balaban.Multiscale.liftOp, h, ↓reduceIte]
    exact hM p.1 q.1
  · simp only [Balaban.Multiscale.liftOp, h, ↓reduceIte]
    exact analyticAt_const

end Rect

section Integrand

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
variable {G : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ} {a : ℕ → ℝ} {aT x ν : ℝ}
  {δ : ℝ} {φ : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ}
  {κι : Type*} [Fintype κι] [DecidableEq κι] {Q : Matrix κι (G.Ω 1) ℂ} {P : Matrix κι κι ℂ}

theorem rectAt_diagonal (e : DecParams G × (G.Ω 1 → ℂ)) :
    RectAt (fun p : DecParams G × (G.Ω 1 → ℂ) => Matrix.diagonal p.2) e := by
  intro i j
  by_cases hij : i = j
  · subst hij
    simp only [Matrix.diagonal_apply_eq]
    exact ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : G.Ω 1 => ℂ) i).analyticAt _).comp
      analyticAt_snd
  · simp only [Matrix.diagonal_apply_ne _ hij]
    exact analyticAt_const

theorem rectAt_xDirichlet (a : ℕ → ℝ) (aT x ν : ℝ) (e : DecParams G × (G.Ω 1 → ℂ)) :
    RectAt (fun p : DecParams G × (G.Ω 1 → ℂ) => xDirichletOperator G a aT x ν p.2) e := by
  have : (fun p : DecParams G × (G.Ω 1 → ℂ) => xDirichletOperator G a aT x ν p.2) =
      fun p => xDirichletOperator G a aT x ν 0 + Matrix.diagonal p.2 := by
    funext p
    rw [← cutXOperator_empty, cutXOperator_eq_add, cutXOperator_empty]
  rw [this]
  exact (RectAt.const _ e).add (rectAt_diagonal e)

/-- **I-4c (iii) for the integrand**: for fixed `x ≥ 0` the entries of `C_x(s)` are analytic in
`(s, α₀)` on the polydisc of (DG4). -/
theorem rectAt_decCov (S : XSetting G a aT ν) (hx : 0 ≤ x) {κ : ℝ} (hκ : 0 ≤ κ)
    (hM : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    (hφ : IsConstraintField G δ φ) (hδ : 0 ≤ δ)
    (hsm : δ ^ 2 * smallConstX d L κ ≤ 1 / 4)
    {e : DecParams G × (G.Ω 1 → ℂ)}
    (he : e ∈ {p : DecParams G × (G.Ω 1 → ℂ) | (∀ P, ‖p.1 P‖ < Real.exp κ) ∧
        ∀ w, ‖p.2 w‖ < coerciveConst d / (2 * (G.spacing (w : CTorus d L N₁ m₁ (k + 1))) ^ 2)}) :
    RectAt (fun p : DecParams G × (G.Ω 1 → ℂ) =>
      decCov G a aT x ν p.2 (extS G p.1) φ Q P) e := by
  have hα : AdmPot G e.2 := fun w => (he.2 w).le
  have hs : ∀ P, ‖extS G e.1 P‖ ≤ Real.exp κ := by
    intro P
    unfold extS
    split_ifs with h
    · exact (he.1 ⟨P, h⟩).le
    · simpa using Real.one_le_exp hκ
  have D : XData G a aT ν x e.2 κ (extS G e.1) := ⟨S, hα, hx, hκ, hM, hs⟩
  have hHx := rectAt_xDirichlet (G := G) a aT x ν e
  have hGs : RectAt (fun p : DecParams G × (G.Ω 1 → ℂ) => Gsx G a aT x ν p.2 (extS G p.1)) e :=
    matAt_Gsx S hx hα D.isUnit_one_sub
  have hGl := hGs.liftOp (N := N)
  have hHl := hHx.liftOp (N := N)
  set F := fieldMul (restrictField G φ) with hF
  have hK : RectAt (fun p : DecParams G × (G.Ω 1 → ℂ) =>
      commK (xDirichletOperator G a aT x ν p.2) (restrictField G φ)) e := by
    unfold commK
    exact ((RectAt.const _ e).mul hHl).sub (hHx.mul (RectAt.const _ e))
  have hMa : RectAt (fun p : DecParams G × (G.Ω 1 → ℂ) =>
      decM G a aT x ν p.2 (extS G p.1) φ) e := by
    unfold decM constraintM
    exact (RectAt.const _ e).sub ((hK.mul hGl).mul (RectAt.const _ e))
  have hNa : RectAt (fun p : DecParams G × (G.Ω 1 → ℂ) =>
      decN G a aT x ν p.2 (extS G p.1) φ) e := by
    unfold decN constraintN
    exact (RectAt.const _ e).sub (hK.mul hGl)
  have hdet : (decM G a aT x ν e.2 (extS G e.1) φ).det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).1 (decM_isUnit D hφ hδ hsm)).ne_zero
  have hMi := hMa.inv hdet
  have hPi : RectAt (fun p : DecParams G × (G.Ω 1 → ℂ) =>
      decPi G a aT x ν p.2 (extS G p.1) φ) e := by
    unfold decPi
    exact (((hGl.mul (RectAt.const _ e)).mul hMi).mul hNa)
  unfold decCov
  have hA := RectAt.const (E := DecParams G × (G.Ω 1 → ℂ))
    (covA (a k) (aT / (L : ℝ) ^ 2) x (liftOp N P)) e
  refine hA.add (RectAt.smul_const _ ?_)
  exact (((hA.mul (RectAt.const _ e)).mul (hGl.sub hPi)).mul (RectAt.const _ e)).mul hA

end Integrand

end Balaban.Localization
