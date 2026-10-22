/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Green.FinalBoxLocCubic
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The Taylor polynomial of order 2 along a line, as a function of a parameter and of the field

PHYS-CUBIC (A6-3), the analytic core.  For a function `f(g, ψ)` of a parameter `g` (the source)
and a field `ψ`, analytic at `(g, φ₀)`, the Taylor polynomial of order `n` of `ψ ↦ f(g, ψ)` at the
centre `φ₀`, in the direction `ψ - φ₀` (`Green.taylorLine`, the line derivatives of
`l ↦ f(g, φ₀ + l (ψ - φ₀))` at `0`), is expressed through the Fréchet derivatives of `f` at
`(g, φ₀)`:

* `deriv_line_eq_fderiv`, `iteratedDeriv_two_line_eq_fderiv`: the first and second line derivatives
  are `Df(g, φ₀)(0, v)` and `D²f(g, φ₀)(0, v)(0, v)`;
* `taylorLine_three_eq`: `taylorLine 3 = f(g, φ₀) + Df(0, v) + ½ D²f((0, v), (0, v))`;
* `analyticAt_taylorLine_three`: hence `(g, ψ) ↦ taylorLine 3 (f(g, ·)) φ₀ (ψ - φ₀)` is analytic at
  every `(g, ψ)` with `f` analytic at `(g, φ₀)`;
* `taylorLine_sum`: the Taylor polynomial of a finite sum is the sum of the Taylor polynomials;
* `taylorLine_congr`: it reads the function on the line only.
-/

@[expose] public section

namespace Balaban.RootFSpine

open Filter Topology Balaban.Green

section Line

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- **The Taylor polynomial reads the function on the line only.** -/
theorem taylorLine_congr {n : ℕ} {τ τ' : E → ℂ} {φ₀ φ₀' v v' : E}
    (h : ∀ l : ℂ, τ (φ₀ + l • v) = τ' (φ₀' + l • v')) :
    taylorLine n τ φ₀ v = taylorLine n τ' φ₀' v' := by
  unfold taylorLine
  have e : (fun l : ℂ => τ (φ₀ + l • v)) = fun l : ℂ => τ' (φ₀' + l • v') := funext h
  rw [e]

/-- `taylorLine 3` is the constant, the first and half the second line derivative. -/
theorem taylorLine_three (τ : E → ℂ) (φ₀ v : E) :
    taylorLine 3 τ φ₀ v = τ φ₀ + deriv (fun l : ℂ => τ (φ₀ + l • v)) 0 +
      (1 / 2 : ℂ) * iteratedDeriv 2 (fun l : ℂ => τ (φ₀ + l • v)) 0 := by
  unfold taylorLine
  simp [Finset.sum_range_succ, iteratedDeriv_one]

/-- **The Taylor polynomial of a finite sum is the sum of the Taylor polynomials**, when the line
functions are analytic at `0`. -/
theorem taylorLine_sum {ι : Type*} (s : Finset ι) (n : ℕ) (τ : ι → E → ℂ) (φ₀ v : E)
    (hτ : ∀ a ∈ s, AnalyticAt ℂ (fun l : ℂ => τ a (φ₀ + l • v)) 0) :
    taylorLine n (fun ψ => ∑ a ∈ s, τ a ψ) φ₀ v = ∑ a ∈ s, taylorLine n (τ a) φ₀ v := by
  unfold taylorLine
  have e : ∀ j ∈ Finset.range n, iteratedDeriv j (fun l : ℂ => ∑ a ∈ s, τ a (φ₀ + l • v)) 0 =
      ∑ a ∈ s, iteratedDeriv j (fun l : ℂ => τ a (φ₀ + l • v)) 0 := by
    intro j _
    have h1 : (fun l : ℂ => ∑ a ∈ s, τ a (φ₀ + l • v)) =
        ∑ a ∈ s, fun l : ℂ => τ a (φ₀ + l • v) := by
      funext l; rw [Finset.sum_apply]
    rw [h1]
    exact iteratedDeriv_sum fun a ha => (hτ a ha).contDiffAt
  rw [Finset.sum_congr rfl fun j hj => by rw [e j hj], Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ => by rw [Finset.mul_sum]

end Line

section Param

variable {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℂ P] [NormedAddCommGroup E]
  [NormedSpace ℂ E]

/-- The application of an analytic family of continuous linear maps to an analytic family of
vectors is analytic. -/
theorem analyticAt_clm_apply {Q V W : Type*} [NormedAddCommGroup Q] [NormedSpace ℂ Q]
    [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W] [NormedSpace ℂ W]
    {A : Q → V →L[ℂ] W} {w : Q → V} {q : Q} (hA : AnalyticAt ℂ A q) (hw : AnalyticAt ℂ w q) :
    AnalyticAt ℂ (fun y => A y (w y)) q := by
  have hB := ContinuousLinearMap.analyticAt_bilinear (ContinuousLinearMap.apply ℂ W) (w q, A q)
  have h := AnalyticAt.comp (g := fun x : V × (V →L[ℂ] W) => ContinuousLinearMap.apply ℂ W x.1 x.2)
    (f := fun y => (w y, A y)) hB (hw.prod hA)
  simpa [Function.comp_def] using h

theorem hasDerivAt_line (g : P) (φ₀ v : E) (l : ℂ) :
    HasDerivAt (fun l : ℂ => ((g, φ₀ + l • v) : P × E)) ((0 : P), v) l := by
  have h2 : HasDerivAt (fun l : ℂ => φ₀ + l • v) v l := by
    simpa using ((hasDerivAt_id l).smul_const v).const_add φ₀
  exact HasDerivAt.prodMk (f₁ := fun _ : ℂ => g) (hasDerivAt_const l g) h2

/-- **The first line derivative is the Fréchet derivative in the field direction.** -/
theorem deriv_line_eq_fderiv {f : P × E → ℂ} {g : P} {φ₀ : E} (hf : AnalyticAt ℂ f (g, φ₀))
    (v : E) :
    deriv (fun l : ℂ => f (g, φ₀ + l • v)) 0 = fderiv ℂ f (g, φ₀) ((0 : P), v) := by
  have hf0 : HasFDerivAt f (fderiv ℂ f (g, φ₀)) ((fun l : ℂ => ((g, φ₀ + l • v) : P × E)) 0) := by
    simpa using hf.differentiableAt.hasFDerivAt
  exact (hf0.comp_hasDerivAt (0 : ℂ) (hasDerivAt_line g φ₀ v 0)).deriv

/-- **The second line derivative is the second Fréchet derivative in the field direction.** -/
theorem iteratedDeriv_two_line_eq_fderiv {f : P × E → ℂ} {g : P} {φ₀ : E}
    (hf : AnalyticAt ℂ f (g, φ₀)) (v : E) :
    iteratedDeriv 2 (fun l : ℂ => f (g, φ₀ + l • v)) 0 =
      fderiv ℂ (fderiv ℂ f) (g, φ₀) ((0 : P), v) ((0 : P), v) := by
  -- `f` is analytic at the points of the line near `0`
  have hev : ∀ᶠ l in 𝓝 (0 : ℂ), AnalyticAt ℂ f (g, φ₀ + l • v) := by
    have ht : Tendsto (fun l : ℂ => ((g, φ₀ + l • v) : P × E)) (𝓝 0) (𝓝 (g, φ₀)) := by
      have := ((hasDerivAt_line g φ₀ v 0).continuousAt).tendsto
      simpa using this
    exact ht.eventually hf.eventually_analyticAt
  have hd : (deriv fun l : ℂ => f (g, φ₀ + l • v)) =ᶠ[𝓝 (0 : ℂ)]
      fun l => fderiv ℂ f (g, φ₀ + l • v) ((0 : P), v) := by
    filter_upwards [hev] with l hl
    exact ((hl.differentiableAt.hasFDerivAt).comp_hasDerivAt l (hasDerivAt_line g φ₀ v l)).deriv
  rw [iteratedDeriv_succ, iteratedDeriv_one, hd.deriv_eq]
  have hf' : HasFDerivAt (fderiv ℂ f) (fderiv ℂ (fderiv ℂ f) (g, φ₀))
      ((fun l : ℂ => ((g, φ₀ + l • v) : P × E)) 0) := by
    simpa using hf.fderiv.differentiableAt.hasFDerivAt
  have h1 : HasDerivAt (fun l : ℂ => fderiv ℂ f (g, φ₀ + l • v))
      (fderiv ℂ (fderiv ℂ f) (g, φ₀) ((0 : P), v)) 0 :=
    hf'.comp_hasDerivAt (0 : ℂ) (hasDerivAt_line g φ₀ v 0)
  have h2 : HasDerivAt (fun l : ℂ => fderiv ℂ f (g, φ₀ + l • v) ((0 : P), v))
      (fderiv ℂ (fderiv ℂ f) (g, φ₀) ((0 : P), v) ((0 : P), v)) 0 :=
    ((ContinuousLinearMap.apply ℂ ℂ ((0 : P), v)).hasFDerivAt).comp_hasDerivAt (0 : ℂ) h1
  exact h2.deriv

/-- **`taylorLine 3` through the Fréchet derivatives.** -/
theorem taylorLine_three_eq {f : P × E → ℂ} {g : P} {φ₀ : E} (hf : AnalyticAt ℂ f (g, φ₀))
    (v : E) :
    taylorLine 3 (fun u => f (g, u)) φ₀ v = f (g, φ₀) + fderiv ℂ f (g, φ₀) ((0 : P), v) +
      (1 / 2 : ℂ) * fderiv ℂ (fderiv ℂ f) (g, φ₀) ((0 : P), v) ((0 : P), v) := by
  rw [taylorLine_three, deriv_line_eq_fderiv hf v, iteratedDeriv_two_line_eq_fderiv hf v]

/-- **The Taylor polynomial of order 2 is analytic in the parameter and the field**: at every
`(g, ψ)` with `f` analytic at `(g, φ₀)`. -/
theorem analyticAt_taylorLine_three {f : P × E → ℂ} {φ₀ : E} {p : P × E}
    (hf : AnalyticAt ℂ f (p.1, φ₀)) :
    AnalyticAt ℂ (fun q : P × E => taylorLine 3 (fun u => f (q.1, u)) φ₀ (q.2 - φ₀)) p := by
  -- the Fréchet form is analytic at `p`
  have hc : AnalyticAt ℂ (fun q : P × E => (q.1, φ₀)) p :=
    analyticAt_fst.prod analyticAt_const
  have hw : AnalyticAt ℂ (fun q : P × E => ((0 : P), q.2 - φ₀)) p :=
    analyticAt_const.prod (analyticAt_snd.sub analyticAt_const)
  have h1 : AnalyticAt ℂ (fun q : P × E => f (q.1, φ₀)) p :=
    AnalyticAt.comp (g := f) (f := fun q : P × E => (q.1, φ₀)) hf hc
  have hD1 : AnalyticAt ℂ (fun q : P × E => fderiv ℂ f (q.1, φ₀)) p :=
    AnalyticAt.comp (g := fderiv ℂ f) (f := fun q : P × E => (q.1, φ₀)) hf.fderiv hc
  have hD2 : AnalyticAt ℂ (fun q : P × E => fderiv ℂ (fderiv ℂ f) (q.1, φ₀)) p :=
    AnalyticAt.comp (g := fderiv ℂ (fderiv ℂ f)) (f := fun q : P × E => (q.1, φ₀))
      hf.fderiv.fderiv hc
  have h2 : AnalyticAt ℂ (fun q : P × E => fderiv ℂ f (q.1, φ₀) ((0 : P), q.2 - φ₀)) p :=
    analyticAt_clm_apply hD1 hw
  have h3 : AnalyticAt ℂ (fun q : P × E =>
      fderiv ℂ (fderiv ℂ f) (q.1, φ₀) ((0 : P), q.2 - φ₀) ((0 : P), q.2 - φ₀)) p :=
    analyticAt_clm_apply (analyticAt_clm_apply hD2 hw) hw
  have hF := (h1.add h2).add ((analyticAt_const (v := (1 / 2 : ℂ))).mul h3)
  refine hF.congr ?_
  -- near `p`, `f` is analytic at `(q.1, φ₀)` and the two forms agree
  have hev : ∀ᶠ q in 𝓝 p, AnalyticAt ℂ f (q.1, φ₀) :=
    (hc.continuousAt.tendsto).eventually hf.eventually_analyticAt
  filter_upwards [hev] with q hq
  exact (taylorLine_three_eq hq (q.2 - φ₀)).symm

end Param

end Balaban.RootFSpine
