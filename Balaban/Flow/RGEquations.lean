/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Analysis.Contraction
public import Balaban.Analysis.Cauchy

/-!
# The renormalization-group equations: one step by analytic contraction

Balaban, *A low temperature expansion for classical `N`-vector models. II. Renormalization group
equations*, Commun. Math. Phys. 182 (1996), Section 5 (pp. 707-718), in the hard-spin case.

The three renormalization conditions are a system for `ξ = (ξ₁, ξ₂, ξ₃) ∈ ℂ³`
(`ξ₁ = ζ/ε_{k+1}`, `ξ₂ = β⁻¹ e`, `ξ₃ = β⁻¹ b`, P4 (5.2), (5.23)).  Here `Fin 3 → ℂ` carries the
sup norm, the norm `|ξ|_∞` of P4.  The system is
`ξ + c(ξ) = f(ξ)` (P4 (5.23)), after Gauss elimination of the triangular linear part (5.21); the
elimination is `exists_rg_solution_triangular` below.

Hypotheses of `exists_rg_solution` and the display each one transcribes:

* `hc`, `hf`: analyticity of `c`, `f` on the polydisc `|ξ|_∞ < c₁₀` (text after (5.24)-(5.25)),
  here with an arbitrary analytic parameter `p` in an open set `P` (the data of the step);
* `hcb` : `|c(ξ)|_∞ ≤ κ ε²` for `|ξ|_∞ ≤ ε ≤ c₁₀`, with `κ = K₅ C₄` (P4 (5.24));
* `hfb` : `|f(ξ)|_∞ ≤ η` on the polydisc, with `η = B₆ K₅ β_{k+1}⁻¹ ε_{k+1}⁻²` (P4 (5.25));
* `hcond` : `16 η max {2κ, 1/c₁₀} ≤ 1` (P4 (5.27)).

The radius is `r₀ = min {(16κ)⁻¹, c₁₀/2}` (P4 after (5.26)).  The derivative bounds (5.26) are not
hypotheses: they are derived from (5.24), (5.25) by Cauchy estimates (the text derives them the
same way).  Conclusions: the solution exists, is unique in the closed polydisc of radius `r₀`
(P4 Proposition 5.1), analytic in the parameter, and `|ξ⁰|_∞ ≤ 2|f(0)|_∞ ≤ 2η` (Prop 5.1; the
first half of (5.31)).
-/

@[expose] public section

open Metric Set

namespace Balaban.Flow

section Lipschitz

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- Cauchy estimate for increments: a function analytic and bounded by `M` on `ball 0 R` is
`M/(R - ρ)`-Lipschitz on `closedBall 0 ρ`, `ρ < R`. -/
theorem lipschitz_closedBall_of_bound {g : E → F} {R M ρ : ℝ} (hρR : ρ < R)
    (hg : DifferentiableOn ℂ g (ball 0 R)) (hM : ∀ z ∈ ball 0 R, ‖g z‖ ≤ M)
    {x y : E} (hx : x ∈ closedBall (0 : E) ρ) (hy : y ∈ closedBall (0 : E) ρ) :
    ‖g x - g y‖ ≤ M / (R - ρ) * ‖x - y‖ := by
  have hρ0 : 0 ≤ ρ := le_trans (norm_nonneg _) (mem_closedBall_zero_iff.mp hx)
  have hsub : closedBall (0 : E) ρ ⊆ ball 0 R := closedBall_subset_ball hρR
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (hM 0 (mem_ball_self (by linarith)))
  have hRρ : 0 < R - ρ := by linarith
  have := Convex.norm_image_sub_le_of_norm_fderiv_le (f := g) (s := closedBall (0 : E) ρ)
    (C := M / (R - ρ))
    (fun z hz => hg.differentiableAt (isOpen_ball.mem_nhds (hsub hz)))
    (fun z hz => by
      refine (Balaban.Analysis.norm_fderiv_le_of_ball hg hM (hsub hz)).trans ?_
      have hz' : dist z 0 ≤ ρ := mem_closedBall.mp hz
      exact div_le_div_of_nonneg_left hM0 hRρ (by linarith))
    (convex_closedBall _ _) hy hx
  exact this

end Lipschitz

section Core

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℂ G]

/-- The radius `r₀ = min {(16 κ)⁻¹, c₁₀/2}` of the polydisc in which (5.23) is solved. -/
noncomputable def rgRadius (κ c₁₀ : ℝ) : ℝ := min (1 / (16 * κ)) (c₁₀ / 2)

theorem rgRadius_pos {κ c₁₀ : ℝ} (hκ : 0 < κ) (hc : 0 < c₁₀) : 0 < rgRadius κ c₁₀ :=
  lt_min (by positivity) (by positivity)

theorem sixteen_mul_rgRadius_le {κ c₁₀ : ℝ} (hκ : 0 < κ) : 16 * κ * rgRadius κ c₁₀ ≤ 1 := by
  have h : rgRadius κ c₁₀ ≤ 1 / (16 * κ) := min_le_left _ _
  rwa [le_div_iff₀ (by positivity), mul_comm] at h

theorem rgRadius_le_half {κ c₁₀ : ℝ} : rgRadius κ c₁₀ ≤ c₁₀ / 2 := min_le_right _ _

/-- **One step of the renormalization-group equations** (P4 Proposition 5.1, hard-spin case):
the system `ξ + c(ξ, p) = f(ξ, p)` (P4 (5.23)) on the polydisc `|ξ|_∞ ≤ r₀` has exactly one
solution `ξ⁰(p)`; it is analytic in the parameter `p` and `|ξ⁰|_∞ ≤ 2|f(0)|_∞ ≤ 2 η`. -/
theorem exists_rg_solution {c f : (Fin 3 → ℂ) × G → (Fin 3 → ℂ)} {P : Set G} (hP : IsOpen P)
    {κ η c₁₀ : ℝ} (hκ : 0 < κ) (hη : 0 ≤ η) (hc₁₀ : 0 < c₁₀)
    (hcond : 16 * η * max (2 * κ) (1 / c₁₀) ≤ 1)
    (hc : AnalyticOnNhd ℂ c (closedBall (0 : Fin 3 → ℂ) c₁₀ ×ˢ P))
    (hf : AnalyticOnNhd ℂ f (closedBall (0 : Fin 3 → ℂ) c₁₀ ×ˢ P))
    (hcb : ∀ p ∈ P, ∀ ε : ℝ, 0 ≤ ε → ε ≤ c₁₀ → ∀ ξ : Fin 3 → ℂ, ‖ξ‖ ≤ ε →
      ‖c (ξ, p)‖ ≤ κ * ε ^ 2)
    (hfb : ∀ p ∈ P, ∀ ξ : Fin 3 → ℂ, ‖ξ‖ ≤ c₁₀ → ‖f (ξ, p)‖ ≤ η) :
    ∃ ξs : G → (Fin 3 → ℂ),
      (∀ p ∈ P, ‖ξs p‖ ≤ rgRadius κ c₁₀ ∧ ξs p + c (ξs p, p) = f (ξs p, p) ∧
        (∀ ξ : Fin 3 → ℂ, ‖ξ‖ ≤ rgRadius κ c₁₀ → ξ + c (ξ, p) = f (ξ, p) → ξ = ξs p) ∧
        ‖ξs p‖ ≤ 2 * ‖f (0, p)‖ ∧ ‖ξs p‖ ≤ 2 * η) ∧
      AnalyticOnNhd ℂ ξs P := by
  set r₀ := rgRadius κ c₁₀ with hr₀
  have hr₀pos : 0 < r₀ := rgRadius_pos hκ hc₁₀
  have h16 : 16 * κ * r₀ ≤ 1 := sixteen_mul_rgRadius_le hκ
  have hr₀c : r₀ ≤ c₁₀ / 2 := rgRadius_le_half
  have hmax1 : 16 * η * (2 * κ) ≤ 1 :=
    le_trans (mul_le_mul_of_nonneg_left (le_max_left _ _) (by positivity)) hcond
  have hmax2 : 16 * η * (1 / c₁₀) ≤ 1 :=
    le_trans (mul_le_mul_of_nonneg_left (le_max_right _ _) (by positivity)) hcond
  have hη2 : 16 * η ≤ c₁₀ := by
    have : 16 * η * (1 / c₁₀) = 16 * η / c₁₀ := by ring
    rw [this, div_le_one hc₁₀] at hmax2
    exact hmax2
  have hηr : 2 * η ≤ r₀ := by
    refine le_min ?_ (by linarith)
    rw [le_div_iff₀ (by positivity)]
    linarith
  have hκr : κ * r₀ ^ 2 ≤ r₀ / 16 := by nlinarith
  -- differentiability in the first variable
  have hanc : ∀ p ∈ P, AnalyticOnNhd ℂ (fun ξ => c (ξ, p)) (closedBall (0 : Fin 3 → ℂ) c₁₀) :=
    fun p hp => AnalyticOnNhd.comp₂ hc analyticOnNhd_id analyticOnNhd_const
      (fun ξ hξ => ⟨hξ, hp⟩)
  have hanf : ∀ p ∈ P, AnalyticOnNhd ℂ (fun ξ => f (ξ, p)) (closedBall (0 : Fin 3 → ℂ) c₁₀) :=
    fun p hp => AnalyticOnNhd.comp₂ hf analyticOnNhd_id analyticOnNhd_const
      (fun ξ hξ => ⟨hξ, hp⟩)
  have hc0 : ∀ p ∈ P, c (0, p) = 0 := fun p hp => by
    have := hcb p hp 0 le_rfl hc₁₀.le 0 (by simp)
    simpa using this
  -- Lipschitz estimates
  have hlipc : ∀ p ∈ P, ∀ x ∈ closedBall (0 : Fin 3 → ℂ) r₀, ∀ y ∈ closedBall (0 : Fin 3 → ℂ) r₀,
      ‖c (x, p) - c (y, p)‖ ≤ 4 * κ * r₀ * ‖x - y‖ := by
    intro p hp x hx y hy
    have hsub : ball (0 : Fin 3 → ℂ) (2 * r₀) ⊆ closedBall 0 c₁₀ := fun z hz =>
      mem_closedBall_zero_iff.mpr (by rw [mem_ball_zero_iff] at hz; linarith)
    have := lipschitz_closedBall_of_bound (g := fun ξ => c (ξ, p)) (R := 2 * r₀)
      (M := κ * (2 * r₀) ^ 2) (ρ := r₀) (by linarith)
      ((hanc p hp).differentiableOn.mono hsub)
      (fun z hz => hcb p hp (2 * r₀) (by linarith) (by linarith) z
        (by rw [mem_ball_zero_iff] at hz; exact hz.le)) hx hy
    have e : κ * (2 * r₀) ^ 2 / (2 * r₀ - r₀) = 4 * κ * r₀ := by field_simp; ring
    rwa [e] at this
  have hlipf : ∀ p ∈ P, ∀ x ∈ closedBall (0 : Fin 3 → ℂ) r₀, ∀ y ∈ closedBall (0 : Fin 3 → ℂ) r₀,
      ‖f (x, p) - f (y, p)‖ ≤ (1 / 8) * ‖x - y‖ := by
    intro p hp x hx y hy
    have hsub : ball (0 : Fin 3 → ℂ) c₁₀ ⊆ closedBall 0 c₁₀ := ball_subset_closedBall
    have := lipschitz_closedBall_of_bound (g := fun ξ => f (ξ, p)) (R := c₁₀) (M := η) (ρ := r₀)
      (by linarith) ((hanf p hp).differentiableOn.mono hsub)
      (fun z hz => hfb p hp z (by rw [mem_ball_zero_iff] at hz; exact hz.le)) hx hy
    refine this.trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  have hT : AnalyticOnNhd ℂ (fun q : (Fin 3 → ℂ) × G => f q - c q)
      (closedBall (0 : Fin 3 → ℂ) r₀ ×ˢ P) :=
    (hf.sub hc).mono (prod_mono (closedBall_subset_closedBall (by linarith)) subset_rfl)
  obtain ⟨ξs, hξs, hanal, hbd⟩ := Balaban.Analysis.exists_analytic_fixedPoint
    (T := fun q : (Fin 3 → ℂ) × G => f q - c q) (P := P) (r := r₀) (θ := 1 / 2) hP hr₀pos.le
    (by norm_num) (by norm_num) hT
    (fun p hp ξ hξ => by
      rw [mem_closedBall_zero_iff] at hξ ⊢
      calc ‖f (ξ, p) - c (ξ, p)‖ ≤ ‖f (ξ, p)‖ + ‖c (ξ, p)‖ := norm_sub_le _ _
        _ ≤ η + κ * r₀ ^ 2 := add_le_add (hfb p hp ξ (by linarith))
            (hcb p hp r₀ hr₀pos.le (by linarith) ξ hξ)
        _ ≤ r₀ := by linarith)
    (fun p hp x hx y hy => by
      have h1 := hlipf p hp x hx y hy
      have h2 := hlipc p hp x hx y hy
      have h3 : 4 * κ * r₀ ≤ 1 / 4 := by nlinarith
      calc ‖(f (x, p) - c (x, p)) - (f (y, p) - c (y, p))‖
          = ‖(f (x, p) - f (y, p)) - (c (x, p) - c (y, p))‖ := by congr 1; abel
        _ ≤ ‖f (x, p) - f (y, p)‖ + ‖c (x, p) - c (y, p)‖ := norm_sub_le _ _
        _ ≤ 1 / 2 * ‖x - y‖ := by nlinarith [norm_nonneg (x - y)])
  refine ⟨ξs, fun p hp => ?_, hanal⟩
  obtain ⟨hmem, hfix, huniq⟩ := hξs p hp
  obtain ⟨-, hnorm⟩ := hbd p hp
  have hT0 : f (0, p) - c (0, p) = f (0, p) := by rw [hc0 p hp, sub_zero]
  have hn : ‖ξs p‖ ≤ 2 * ‖f (0, p)‖ := by
    rw [hT0] at hnorm
    have e : ‖f (0, p)‖ / (1 - 1 / 2) = 2 * ‖f (0, p)‖ := by ring
    linarith
  refine ⟨mem_closedBall_zero_iff.mp hmem, ?_, fun ξ hξ h => huniq ξ (mem_closedBall_zero_iff.mpr hξ) ?_,
    hn, ?_⟩
  · have := sub_eq_iff_eq_add.mp hfix
    exact this.symm
  · exact sub_eq_iff_eq_add.mpr h.symm
  · have := hfb p hp 0 (by simp; exact hc₁₀.le)
    linarith

end Core

section Triangular

/-- Hypotheses on the linear part of the system (5.21), lower triangular with the bounds (5.22):
`1/2 < |a₁₁|`, `a₂₂ = 1`, `1/4 < |a₃₃|`, `|a₂₁| < ε`, `|a₃₁| < 5ε/2` (P4: `13/6 ε`),
`|a₃₂| < 3/2`.  Only the lower bounds on the diagonal and the upper bounds below it are used. -/
structure TriangularBounds (A : Matrix (Fin 3) (Fin 3) ℂ) (ε : ℝ) : Prop where
  upper01 : A 0 1 = 0
  upper02 : A 0 2 = 0
  upper12 : A 1 2 = 0
  d0 : 1 / 2 ≤ ‖A 0 0‖
  d1 : 1 ≤ ‖A 1 1‖
  d2 : 1 / 4 ≤ ‖A 2 2‖
  l10 : ‖A 1 0‖ ≤ ε
  l20 : ‖A 2 0‖ ≤ 5 / 2 * ε
  l21 : ‖A 2 1‖ ≤ 3 / 2

/-- Gauss elimination for the triangular system: a solution of `A y = z` has `|y|_∞ ≤ 42 |z|_∞`
(for `ε ≤ 1`). -/
theorem TriangularBounds.norm_le {A : Matrix (Fin 3) (Fin 3) ℂ} {ε : ℝ}
    (hA : TriangularBounds A ε) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) {y z : Fin 3 → ℂ}
    (h : A.mulVec y = z) : ‖y‖ ≤ 42 * ‖z‖ := by
  have e : ∀ i, ∑ j, A i j * y j = z i := fun i => by
    have := congrFun h i
    simpa [Matrix.mulVec, dotProduct] using this
  have e0 : A 0 0 * y 0 = z 0 := by simpa [Fin.sum_univ_three, hA.upper01, hA.upper02] using e 0
  have e1 : A 1 0 * y 0 + A 1 1 * y 1 = z 1 := by
    simpa [Fin.sum_univ_three, hA.upper12] using e 1
  have e2 : A 2 0 * y 0 + A 2 1 * y 1 + A 2 2 * y 2 = z 2 := by
    simpa [Fin.sum_univ_three] using e 2
  have hz0 : ‖z 0‖ ≤ ‖z‖ := norm_le_pi_norm z 0
  have hz1 : ‖z 1‖ ≤ ‖z‖ := norm_le_pi_norm z 1
  have hz2 : ‖z 2‖ ≤ ‖z‖ := norm_le_pi_norm z 2
  have hZ : 0 ≤ ‖z‖ := norm_nonneg _
  have y0 : ‖y 0‖ ≤ 2 * ‖z‖ := by
    have : ‖A 0 0‖ * ‖y 0‖ = ‖z 0‖ := by rw [← norm_mul, e0]
    nlinarith [hA.d0, norm_nonneg (y 0)]
  have y1 : ‖y 1‖ ≤ 3 * ‖z‖ := by
    have h1 : A 1 1 * y 1 = z 1 - A 1 0 * y 0 := by rw [← e1]; ring
    have h2 : ‖A 1 1‖ * ‖y 1‖ ≤ ‖z 1‖ + ‖A 1 0‖ * ‖y 0‖ := by
      rw [← norm_mul, h1]
      exact (norm_sub_le _ _).trans (by rw [norm_mul])
    have h3 : ‖A 1 0‖ * ‖y 0‖ ≤ ε * (2 * ‖z‖) :=
      mul_le_mul hA.l10 y0 (norm_nonneg _) hε0
    nlinarith [hA.d1, norm_nonneg (y 1)]
  have y2 : ‖y 2‖ ≤ 42 * ‖z‖ := by
    have h1 : A 2 2 * y 2 = z 2 - A 2 0 * y 0 - A 2 1 * y 1 := by rw [← e2]; ring
    have h2 : ‖A 2 2‖ * ‖y 2‖ ≤ ‖z 2‖ + ‖A 2 0‖ * ‖y 0‖ + ‖A 2 1‖ * ‖y 1‖ := by
      rw [← norm_mul, h1]
      refine (norm_sub_le _ _).trans ?_
      have := norm_sub_le (z 2) (A 2 0 * y 0)
      simp only [norm_mul] at this ⊢
      linarith
    have h3 : ‖A 2 0‖ * ‖y 0‖ ≤ 5 / 2 * ε * (2 * ‖z‖) :=
      mul_le_mul hA.l20 y0 (norm_nonneg _) (by positivity)
    have h4 : ‖A 2 1‖ * ‖y 1‖ ≤ 3 / 2 * (3 * ‖z‖) :=
      mul_le_mul hA.l21 y1 (norm_nonneg _) (by norm_num)
    nlinarith [hA.d2, norm_nonneg (y 2)]
  refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun i => ?_
  fin_cases i
  · simp only [Fin.zero_eta]; linarith
  · simp only [Fin.mk_one]; linarith
  · simpa using y2

/-- The inverse of the triangular linear part as a continuous linear map, with `A (B z) = z` and
`|B z|_∞ ≤ 42 |z|_∞`. -/
theorem TriangularBounds.exists_inverse {A : Matrix (Fin 3) (Fin 3) ℂ} {ε : ℝ}
    (hA : TriangularBounds A ε) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    ∃ B : (Fin 3 → ℂ) →L[ℂ] (Fin 3 → ℂ),
      (∀ z, A.mulVec (B z) = z) ∧ ∀ z, ‖B z‖ ≤ 42 * ‖z‖ := by
  have hinj : Function.Injective (Matrix.mulVecLin A) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro y hy
    have := hA.norm_le hε0 hε1 (z := 0) (by simpa using hy)
    simpa using this
  let e := LinearEquiv.ofInjectiveEndo (Matrix.mulVecLin A) hinj
  refine ⟨LinearMap.toContinuousLinearMap (e.symm : (Fin 3 → ℂ) →ₗ[ℂ] (Fin 3 → ℂ)), fun z => ?_,
    fun z => ?_⟩
  · exact e.apply_symm_apply z
  · refine hA.norm_le hε0 hε1 (y := LinearMap.toContinuousLinearMap
      (e.symm : (Fin 3 → ℂ) →ₗ[ℂ] (Fin 3 → ℂ)) z) (z := z) ?_
    exact e.apply_symm_apply z

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℂ G]

/-- **The system (5.21) with its triangular linear part** (P4 Proposition 5.1).  The system
`A ξ + c̃(ξ, p) = f̃(ξ, p)`, `A` lower triangular with the bounds (5.22), `c̃` of second order
(`|c̃| ≤ κ̃ ε²` on `|ξ|_∞ ≤ ε`) and `|f̃| ≤ η̃`, has exactly one solution in the polydisc of radius
`r₀ = min {(16 · 42 κ̃)⁻¹, c₁₀/2}`, analytic in `p`, with `|ξ⁰|_∞ ≤ 84 η̃`, provided
`16 · 42 η̃ max {2 · 42 κ̃, 1/c₁₀} ≤ 1`.  (The constant `42` bounds the Gauss elimination,
`TriangularBounds.norm_le`; in P4 it is absorbed into `K₅`, (5.24)-(5.25).) -/
theorem exists_rg_solution_triangular {A : Matrix (Fin 3) (Fin 3) ℂ} {ε : ℝ}
    (hA : TriangularBounds A ε) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    {c f : (Fin 3 → ℂ) × G → (Fin 3 → ℂ)} {P : Set G} (hP : IsOpen P)
    {κ η c₁₀ : ℝ} (hκ : 0 < κ) (hη : 0 ≤ η) (hc₁₀ : 0 < c₁₀)
    (hcond : 16 * (42 * η) * max (2 * (42 * κ)) (1 / c₁₀) ≤ 1)
    (hc : AnalyticOnNhd ℂ c (closedBall (0 : Fin 3 → ℂ) c₁₀ ×ˢ P))
    (hf : AnalyticOnNhd ℂ f (closedBall (0 : Fin 3 → ℂ) c₁₀ ×ˢ P))
    (hcb : ∀ p ∈ P, ∀ ε' : ℝ, 0 ≤ ε' → ε' ≤ c₁₀ → ∀ ξ : Fin 3 → ℂ, ‖ξ‖ ≤ ε' →
      ‖c (ξ, p)‖ ≤ κ * ε' ^ 2)
    (hfb : ∀ p ∈ P, ∀ ξ : Fin 3 → ℂ, ‖ξ‖ ≤ c₁₀ → ‖f (ξ, p)‖ ≤ η) :
    ∃ ξs : G → (Fin 3 → ℂ),
      (∀ p ∈ P, ‖ξs p‖ ≤ rgRadius (42 * κ) c₁₀ ∧
        A.mulVec (ξs p) + c (ξs p, p) = f (ξs p, p) ∧
        (∀ ξ : Fin 3 → ℂ, ‖ξ‖ ≤ rgRadius (42 * κ) c₁₀ →
          A.mulVec ξ + c (ξ, p) = f (ξ, p) → ξ = ξs p) ∧ ‖ξs p‖ ≤ 84 * η) ∧
      AnalyticOnNhd ℂ ξs P := by
  obtain ⟨B, hAB, hB⟩ := hA.exists_inverse hε0 hε1
  have hBA : ∀ y, B (A.mulVec y) = y := fun y => by
    have h := hA.norm_le hε0 hε1 (y := B (A.mulVec y) - y) (z := 0)
      (by rw [Matrix.mulVec_sub, hAB, sub_self])
    have : ‖B (A.mulVec y) - y‖ = 0 := le_antisymm (by simpa using h) (norm_nonneg _)
    exact sub_eq_zero.mp (norm_eq_zero.mp this)
  have hBan : ∀ g : (Fin 3 → ℂ) × G → (Fin 3 → ℂ),
      AnalyticOnNhd ℂ g (closedBall (0 : Fin 3 → ℂ) c₁₀ ×ˢ P) →
      AnalyticOnNhd ℂ (fun q => B (g q)) (closedBall (0 : Fin 3 → ℂ) c₁₀ ×ˢ P) :=
    fun g hg => B.comp_analyticOnNhd hg
  have h42κ : 0 < 42 * κ := by positivity
  obtain ⟨ξs, hξs, hanal⟩ := exists_rg_solution (c := fun q => B (c q)) (f := fun q => B (f q))
    hP (κ := 42 * κ) (η := 42 * η) (c₁₀ := c₁₀) h42κ (by positivity) hc₁₀ hcond (hBan c hc)
    (hBan f hf)
    (fun p hp ε' h0 h1 ξ hξ => (hB _).trans (by
      have := hcb p hp ε' h0 h1 ξ hξ
      nlinarith))
    (fun p hp ξ hξ => (hB _).trans (by
      have := hfb p hp ξ hξ
      nlinarith))
  refine ⟨ξs, fun p hp => ?_, hanal⟩
  obtain ⟨h1, h2, h3, -, h5⟩ := hξs p hp
  refine ⟨h1, ?_, ?_, by linarith⟩
  · have := congrArg A.mulVec h2
    rw [Matrix.mulVec_add, hAB, hAB] at this
    exact this
  · intro ξ hξ h
    refine h3 ξ hξ ?_
    have := congrArg B h
    rwa [map_add, hBA] at this

end Triangular

end Balaban.Flow
