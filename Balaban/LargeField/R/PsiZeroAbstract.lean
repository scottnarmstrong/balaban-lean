module

public import Balaban.Analysis.Contraction
public import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The contraction behind Lemma III.3.3 (abstract part)

Lemma III.3.3 (P7 Lemma 2.1) solves the variational problem (2.34) for the block field on `Z₀` by a
contraction: the Hessian of the effective action is bounded below by `½γ₀ c_{D₀}` (coercivity on the box
`Z₀`, `dirichlet_box_coercive`), the gradient at the constant configuration is `O(δ_k)`, and the gradient map
is Lipschitz.  This file proves the abstract statements:

* `exists_unique_zero_ball`: a strongly monotone Lipschitz map `g` on a ball with small residual at the centre
  has a unique zero in the ball, at distance `≤ ε/c` from the centre;
* `zero_equivariant`: the zero is equivariant under any isometry that commutes with `g` and fixes the centre;
* `exists_analytic_zero`: with complex parameters, the zero is analytic in the parameters
  (the landed analytic contraction `Balaban.Analysis.exists_analytic_fixedPoint` for `T = ξ - A⁻¹ g`).

The effective action of the window (`A_k(𝔹_k(U_k); ψ̃_k, φ_k)`) and its Hessian bounds (P7 (2.35)–(2.38),
P4 (2.24)) are not in the library; they are the hypotheses to verify to obtain `ψ⁰_k`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

open Metric Set

namespace Balaban.LargeField

section Real

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- A strongly monotone, Lipschitz map on a ball with a small residual at the centre has a unique zero in
the ball. -/
theorem exists_unique_zero_ball {g : E → E} {x0 : E} {r c Λ ε : ℝ} (hc : 0 < c) (hcΛ : c ≤ Λ)
    (hr : 0 ≤ r)
    (hlip : ∀ x ∈ closedBall x0 r, ∀ y ∈ closedBall x0 r, ‖g x - g y‖ ≤ Λ * ‖x - y‖)
    (hmono : ∀ x ∈ closedBall x0 r, ∀ y ∈ closedBall x0 r,
      c * ‖x - y‖ ^ 2 ≤ inner ℝ (g x - g y) (x - y))
    (hres : ‖g x0‖ ≤ ε) (hε : ε ≤ c * r / 2) :
    ∃ x ∈ closedBall x0 r, g x = 0 ∧ (∀ y ∈ closedBall x0 r, g y = 0 → y = x) ∧
      ‖x - x0‖ ≤ ε / c := by
  have hΛ : 0 < Λ := by linarith
  set t : ℝ := c / Λ ^ 2 with ht
  have ht0 : 0 < t := by positivity
  set s : ℝ := c ^ 2 / Λ ^ 2 with hs
  have hs0 : 0 < s := by positivity
  have hs1 : s ≤ 1 := by
    rw [hs, div_le_one (by positivity)]; nlinarith
  set θ : ℝ := Real.sqrt (1 - s) with hθ
  have hθ0 : 0 ≤ θ := Real.sqrt_nonneg _
  have hθ1 : θ < 1 := by
    rw [hθ, Real.sqrt_lt' one_pos]; linarith
  have hθs : θ ≤ 1 - s / 2 := by
    rw [hθ]
    refine Real.sqrt_le_iff.mpr ⟨by linarith, ?_⟩
    nlinarith
  -- the contraction `T y = y - t g y`
  set T : E → E := fun y => y - t • g y with hT
  have hTlip : ∀ x ∈ closedBall x0 r, ∀ y ∈ closedBall x0 r, ‖T x - T y‖ ≤ θ * ‖x - y‖ := by
    intro x hx y hy
    have h1 : ‖T x - T y‖ ^ 2 ≤ (1 - s) * ‖x - y‖ ^ 2 := by
      have e : T x - T y = (x - y) - t • (g x - g y) := by
        simp only [hT, smul_sub]; abel
      rw [e, norm_sub_sq_real, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, inner_smul_right]
      have h2 := hmono x hx y hy
      rw [real_inner_comm] at h2
      have h3 := hlip x hx y hy
      have h4 : ‖g x - g y‖ ^ 2 ≤ Λ ^ 2 * ‖x - y‖ ^ 2 := by
        rw [← mul_pow]; exact pow_le_pow_left₀ (norm_nonneg _) h3 2
      have h5 : t ^ 2 * Λ ^ 2 = s := by rw [ht, hs]; field_simp
      have h6 : 2 * t * c = 2 * s := by rw [ht, hs]; field_simp
      nlinarith [mul_le_mul_of_nonneg_left h2 ht0.le, mul_le_mul_of_nonneg_left h4 (sq_nonneg t)]
    have : ‖T x - T y‖ ≤ θ * ‖x - y‖ := by
      rw [hθ, ← Real.sqrt_sq (norm_nonneg (T x - T y)), ← Real.sqrt_sq (norm_nonneg (x - y)),
        ← Real.sqrt_mul (by linarith)]
      exact Real.sqrt_le_sqrt (by simpa using h1)
    exact this
  have htε : t * ε ≤ (s / 2) * r := by
    calc t * ε ≤ t * (c * r / 2) := mul_le_mul_of_nonneg_left hε ht0.le
      _ = (s / 2) * r := by rw [ht, hs]; field_simp
  have hmaps : ∀ x ∈ closedBall x0 r, T x ∈ closedBall x0 r := by
    intro x hxm
    have hx := hxm
    rw [mem_closedBall, dist_eq_norm] at hx ⊢
    have hTx0 : ‖T x0 - x0‖ ≤ t * ε := by
      have : T x0 - x0 = -(t • g x0) := by simp [hT]
      rw [this, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos ht0]
      exact mul_le_mul_of_nonneg_left hres ht0.le
    calc ‖T x - x0‖ = ‖(T x - T x0) + (T x0 - x0)‖ := by rw [sub_add_sub_cancel]
      _ ≤ ‖T x - T x0‖ + ‖T x0 - x0‖ := norm_add_le _ _
      _ ≤ θ * ‖x - x0‖ + t * ε := add_le_add (hTlip x hxm x0 (mem_closedBall_self hr)) hTx0
      _ ≤ θ * r + (s / 2) * r := add_le_add (mul_le_mul_of_nonneg_left hx hθ0) htε
      _ ≤ r := by nlinarith
  -- translate to the ball about `0`
  obtain ⟨ξ, hξ, hfix, hu, -⟩ := Balaban.Analysis.exists_unique_fixedPoint_closedBall
    (S := fun ξ => T (x0 + ξ) - x0) hr hθ0 hθ1
    (fun ξ hξ => by
      have := hmaps (x0 + ξ) (by simpa [mem_closedBall, dist_eq_norm] using hξ)
      simpa [mem_closedBall, dist_eq_norm] using this)
    (fun ξ hξ ξ' hξ' => by
      have := hTlip (x0 + ξ) (by simpa [mem_closedBall, dist_eq_norm] using hξ) (x0 + ξ')
        (by simpa [mem_closedBall, dist_eq_norm] using hξ')
      simpa using this)
  have hxball : x0 + ξ ∈ closedBall x0 r := by simpa [mem_closedBall, dist_eq_norm] using hξ
  have hgx : g (x0 + ξ) = 0 := by
    have : T (x0 + ξ) = x0 + ξ := by
      have h' := sub_eq_iff_eq_add.mp hfix
      rw [h', add_comm]
    have h2 : t • g (x0 + ξ) = 0 := by
      have : (x0 + ξ) - t • g (x0 + ξ) = x0 + ξ := this
      simpa using this
    exact (smul_eq_zero.mp h2).resolve_left ht0.ne'
  have huniq : ∀ y ∈ closedBall x0 r, g y = 0 → y = x0 + ξ := by
    intro y hy hgy
    have h := hmono y hy (x0 + ξ) hxball
    rw [hgy, hgx, sub_zero, inner_zero_left] at h
    have : ‖y - (x0 + ξ)‖ ^ 2 ≤ 0 := by nlinarith
    have : ‖y - (x0 + ξ)‖ = 0 := by nlinarith [norm_nonneg (y - (x0 + ξ))]
    exact sub_eq_zero.mp (norm_eq_zero.mp this)
  refine ⟨x0 + ξ, hxball, hgx, huniq, ?_⟩
  -- distance bound
  have h := hmono (x0 + ξ) hxball x0 (mem_closedBall_self hr)
  rw [hgx, zero_sub, add_sub_cancel_left] at h
  have h2 : inner ℝ (-g x0) ξ ≤ ε * ‖ξ‖ := by
    calc inner ℝ (-g x0) ξ ≤ ‖-g x0‖ * ‖ξ‖ := real_inner_le_norm _ _
      _ ≤ ε * ‖ξ‖ := by rw [norm_neg]; exact mul_le_mul_of_nonneg_right hres (norm_nonneg _)
  rw [add_sub_cancel_left, le_div_iff₀ hc]
  have hn := norm_nonneg ξ
  by_cases h0 : ‖ξ‖ = 0
  · rw [h0, zero_mul]; exact (norm_nonneg _).trans hres
  · have hpos : 0 < ‖ξ‖ := lt_of_le_of_ne hn (Ne.symm h0)
    have : ‖ξ‖ * (c * ‖ξ‖) ≤ ‖ξ‖ * ε := by nlinarith
    nlinarith

/-- Equivariance: an isometry `σ` with `g' ∘ σ = σ ∘ g` and `x₀' = σ x₀` maps the zero of `g` in the ball about
`x₀` to a zero of `g'` in the ball about `x₀'`; by uniqueness it is the zero of `g'`. -/
theorem zero_equivariant {g g' : E → E} {x0 x0' : E} {r : ℝ} (σ : E ≃ₗᵢ[ℝ] E)
    (hg : ∀ x, g' (σ x) = σ (g x)) (hx0 : x0' = σ x0) {x : E} (hx : x ∈ closedBall x0 r)
    (hgx : g x = 0) : σ x ∈ closedBall x0' r ∧ g' (σ x) = 0 := by
  refine ⟨?_, by rw [hg, hgx, map_zero]⟩
  rw [mem_closedBall, hx0, σ.dist_map]
  exact mem_closedBall.mp hx

end Real

section Analytic

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup G] [NormedSpace ℂ G]

/-- **Analytic dependence of the zero on complex parameters.**  If `T(ξ, p) = ξ - B g(ξ, p)` (`B` injective) maps the
ball into itself and is a `θ`-contraction for each `p` in the open set `P`, and `g` is analytic, then the zero
`ξ*(p)` of `g(·, p)` in the ball is unique and analytic in `p`. -/
theorem exists_analytic_zero {g : E × G → E} (B : E →L[ℂ] E) (hB : Function.Injective B) {P : Set G}
    (hP : IsOpen P) {r θ : ℝ} (hr : 0 ≤ r) (hθ0 : 0 ≤ θ) (hθ1 : θ < 1)
    (hg : AnalyticOnNhd ℂ g (closedBall (0 : E) r ×ˢ P))
    (hmaps : ∀ p ∈ P, ∀ ξ ∈ closedBall (0 : E) r, ξ - B (g (ξ, p)) ∈ closedBall (0 : E) r)
    (hlip : ∀ p ∈ P, ∀ ξ ∈ closedBall (0 : E) r, ∀ ξ' ∈ closedBall (0 : E) r,
      ‖(ξ - B (g (ξ, p))) - (ξ' - B (g (ξ', p)))‖ ≤ θ * ‖ξ - ξ'‖) :
    ∃ ξs : G → E,
      (∀ p ∈ P, ξs p ∈ closedBall (0 : E) r ∧ g (ξs p, p) = 0 ∧
        ∀ ξ ∈ closedBall (0 : E) r, g (ξ, p) = 0 → ξ = ξs p) ∧ AnalyticOnNhd ℂ ξs P := by
  have hT : AnalyticOnNhd ℂ (fun q : E × G => q.1 - B (g q)) (closedBall (0 : E) r ×ˢ P) := by
    intro q hq
    exact (analyticAt_fst).sub (B.analyticAt _ |>.comp (hg q hq))
  obtain ⟨ξs, h1, h2, -⟩ := Balaban.Analysis.exists_analytic_fixedPoint (T := fun q : E × G => q.1 - B (g q))
    hP hr hθ0 hθ1 hT hmaps hlip
  refine ⟨ξs, fun p hp => ?_, h2⟩
  obtain ⟨hb, hfix, huniq⟩ := h1 p hp
  refine ⟨hb, ?_, fun ξ hξ hz => huniq ξ hξ ?_⟩
  · have : B (g (ξs p, p)) = 0 := by
      have := hfix; simp only at this
      exact sub_eq_self.mp this
    exact hB (by rw [this, map_zero])
  · simp [hz]

end Analytic

end Balaban.LargeField
