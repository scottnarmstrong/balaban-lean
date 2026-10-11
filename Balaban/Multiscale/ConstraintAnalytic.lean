/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Multiscale.ConstraintSandwich
public import Balaban.Multiscale.Analyticity
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Analytic.Linear

/-!
# Analyticity of the constrained sandwich `Π` in `(α, φ₀)` (GREEN.md G-2(vi′))

`Π = Ĝ φ₀ [φ₀ · Ĝ φ₀]⁻¹ φ₀ · Ĝ` with `Ĝ = H_D(α)⁻¹` is a rational function of the finitely many
complex variables `α(x)`, `φ₀(x)ᵢ` (`x ∈ Ω₁`), with denominators `det H_D(α)` and
`det (φ₀ · Ĝ φ₀)`.  Both are nonzero under the hypotheses of G-2(v)
(`Balaban.Multiscale.dirichletOperator_isUnit`, `Balaban.Multiscale.constraintForm_isUnit`), so
`Π` is analytic at every such point, in particular on a neighbourhood of the (strict) hypotheses.
-/

@[expose] public section

namespace Balaban.Multiscale

open Matrix Finset

variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}

section Ana

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable {ι κ μ : Type*}

/-- All entries of a matrix-valued map are analytic at `p₀`. -/
def AnaMat (M : E → Matrix ι κ ℂ) (p₀ : E) : Prop := ∀ i j, AnalyticAt ℂ (fun p => M p i j) p₀

theorem AnaMat.mul [Fintype κ] {M : E → Matrix ι κ ℂ} {M' : E → Matrix κ μ ℂ} {p₀ : E}
    (h : AnaMat M p₀) (h' : AnaMat M' p₀) : AnaMat (fun p => M p * M' p) p₀ := by
  intro i j
  simp only [Matrix.mul_apply]
  exact Finset.analyticAt_fun_sum _ fun l _ => (h i l).mul (h' l j)

theorem AnaMat.sub {M M' : E → Matrix ι κ ℂ} {p₀ : E} (h : AnaMat M p₀) (h' : AnaMat M' p₀) :
    AnaMat (fun p => M p - M' p) p₀ := fun i j => by
  simp only [Matrix.sub_apply]; exact (h i j).sub (h' i j)

theorem AnaMat.transpose {M : E → Matrix ι κ ℂ} {p₀ : E} (h : AnaMat M p₀) :
    AnaMat (fun p => (M p)ᵀ) p₀ := fun i j => by
  simp only [Matrix.transpose_apply]; exact h j i

theorem AnaMat.inv [Fintype ι] [DecidableEq ι] {M : E → Matrix ι ι ℂ} {p₀ : E} (h : AnaMat M p₀)
    (hdet : (M p₀).det ≠ 0) : AnaMat (fun p => (M p)⁻¹) p₀ :=
  fun i j => analyticAt_inv_apply h hdet i j

theorem AnaMat.const (A : Matrix ι κ ℂ) (p₀ : E) : AnaMat (fun _ => A) p₀ :=
  fun _ _ => analyticAt_const

end Ana

section Concrete

variable (G : GeneratingSet d L N₀ k ϱ) (a : ℕ → ℝ) (ν : ℝ)

/-- The parameter space `(α, φ₀)`: the values on `Ω₁` of the diagonal and of the field. -/
abbrev ParamSpace (G : GeneratingSet d L N₀ k ϱ) (N : ℕ) : Type :=
  (G.Ω 1 → ℂ) × (G.Ω 1 → Fin N → ℂ)

theorem anaMat_dirichlet (p₀ : ParamSpace G N) :
    AnaMat (fun p : ParamSpace G N => dirichletOperator G a ν p.1) p₀ := fun i j =>
  (analyticAt_dirichletOperator_apply G a ν p₀.1 i j).comp
    ((ContinuousLinearMap.fst ℂ (G.Ω 1 → ℂ) (G.Ω 1 → Fin N → ℂ)).analyticAt p₀)

theorem anaMat_liftOp {A : ParamSpace G N → Matrix (G.Ω 1) (G.Ω 1) ℂ} {p₀ : ParamSpace G N}
    (h : AnaMat A p₀) : AnaMat (fun p => liftOp N (A p)) p₀ := by
  intro x y
  by_cases hxy : x.2 = y.2
  · simp only [liftOp, hxy, ↓reduceIte]; exact h _ _
  · simp only [liftOp, hxy, ↓reduceIte]; exact analyticAt_const

theorem anaMat_fieldMul (p₀ : ParamSpace G N) :
    AnaMat (fun p : ParamSpace G N => fieldMul p.2) p₀ := by
  intro x y
  by_cases hxy : x.1 = y
  · simp only [fieldMul, hxy, ↓reduceIte]
    exact ((ContinuousLinearMap.proj x.2).comp ((ContinuousLinearMap.proj y).comp
      (ContinuousLinearMap.snd ℂ (G.Ω 1 → ℂ) (G.Ω 1 → Fin N → ℂ)))).analyticAt p₀
  · simp only [fieldMul, hxy, ↓reduceIte]; exact analyticAt_const

/-- **Analyticity of `Π` in `(α, φ₀)`** (G-2(vi′), third part): every entry of
`Π = Ĝ φ₀ [φ₀ · Ĝ φ₀]⁻¹ φ₀ · Ĝ`, `Ĝ = H_D(α)⁻¹`, is analytic at every point where
`det H_D(α) ≠ 0` and `det (φ₀ · Ĝ φ₀) ≠ 0`. -/
theorem analyticAt_constrainedOp (p₀ : ParamSpace G N)
    (hH : (dirichletOperator G a ν p₀.1).det ≠ 0)
    (hF : (constraintForm (dirichletOperator G a ν p₀.1)⁻¹ p₀.2).det ≠ 0) (q q' : G.Ω 1 × Fin N) :
    AnalyticAt ℂ (fun p : ParamSpace G N =>
      constrainedOp (dirichletOperator G a ν p.1)⁻¹ p.2 q q') p₀ := by
  have hG := (anaMat_dirichlet G a ν p₀).inv hH
  have hL := anaMat_liftOp G hG
  have hP := anaMat_fieldMul G (N := N) p₀
  have hF' : AnaMat (fun p : ParamSpace G N =>
      constraintForm (dirichletOperator G a ν p.1)⁻¹ p.2) p₀ := by
    unfold constraintForm
    exact (hP.transpose.mul hL).mul hP
  have hFi := hF'.inv hF
  have hall := ((((hL.mul hP).mul hFi).mul hP.transpose).mul hL)
  exact hall q q'

/-- The set of parameters where the two denominators of `Π` are nonzero. -/
def PiDomain : Set (ParamSpace G N) :=
  {p | (dirichletOperator G a ν p.1).det ≠ 0 ∧
    (constraintForm (dirichletOperator G a ν p.1)⁻¹ p.2).det ≠ 0}

theorem analyticOnNhd_constrainedOp (q q' : G.Ω 1 × Fin N) :
    AnalyticOnNhd ℂ (fun p : ParamSpace G N =>
      constrainedOp (dirichletOperator G a ν p.1)⁻¹ p.2 q q') (PiDomain G a ν) :=
  fun _ hp => analyticAt_constrainedOp G a ν _ hp.1 hp.2 q q'

/-- Under the hypotheses of G-2(v), `(α, φ₀|_{Ω₁})` lies in the domain of analyticity. -/
theorem standing_mem_PiDomain {α : G.Ω 1 → ℂ} {δ : ℝ}
    {φ : Torus d (N₀ * L ^ k) → Fin N → ℂ} (St : Standing G a ν α δ φ) :
    (α, restrictField G φ) ∈ PiDomain G a ν := by
  refine ⟨?_, ?_⟩
  · exact ((Matrix.isUnit_iff_isUnit_det _).1 (dirichletOperator_isUnit G St.pos St.mass St.weights
      α St.alpha)).ne_zero
  · exact ((Matrix.isUnit_iff_isUnit_det _).1 (constraintForm_isUnit St)).ne_zero

end Concrete

end Balaban.Multiscale
