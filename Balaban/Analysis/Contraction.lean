/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Analysis.AnalyticLimit
public import Mathlib.Topology.MetricSpace.Contracting


/-!
# Analytic contraction with parameters

`exists_analytic_fixedPoint`: for `T : E × G → E` analytic on `closedBall 0 r ×ˢ P` (`P` open),
a `θ`-contraction in the first variable mapping the ball to itself, the unique fixed point
`ξ*(p)` in the ball is analytic on `P`, with `‖ξ*(p) - T(0,p)‖ ≤ θ r` and
`‖ξ*(p)‖ ≤ ‖T(0,p)‖/(1-θ)`.  The proof: Picard iterates `T^n(0, ·)` are analytic, converge
uniformly on `P` at rate `θ^n r`, and uniform limits are analytic
(`Balaban.Analysis.analyticOnNhd_of_tendstoUniformlyOn`).  `analyticOnNhd_real_comp` gives the
real-analytic restriction to real parameters.

The fixed-point step follows `banachFixedPointOnCompleteSubset` in
`AVRegularity/External/Standard.lean` of `AVAnomalousRegularization-dev` (commit `98750e3b`).
-/

@[expose] public section

open Metric Set Filter Topology

namespace Balaban.Analysis

section FixedPoint

variable {E : Type*} [NormedAddCommGroup E] [CompleteSpace E]

/-- Banach fixed point theorem on a closed ball centred at `0`, with iterate estimates.
(The argument follows `banachFixedPointOnCompleteSubset` of `AVAnomalousRegularization-dev`,
`AVRegularity/External/Standard.lean`.) -/
theorem exists_unique_fixedPoint_closedBall {S : E → E} {r θ : ℝ} (hr : 0 ≤ r)
    (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) (hmaps : ∀ ξ ∈ closedBall (0 : E) r, S ξ ∈ closedBall (0 : E) r)
    (hlip : ∀ ξ ∈ closedBall (0 : E) r, ∀ ξ' ∈ closedBall (0 : E) r, ‖S ξ - S ξ'‖ ≤ θ * ‖ξ - ξ'‖) :
    ∃ ξ ∈ closedBall (0 : E) r, S ξ = ξ ∧ (∀ ξ' ∈ closedBall (0 : E) r, S ξ' = ξ' → ξ' = ξ) ∧
      ∀ n : ℕ, S^[n] 0 ∈ closedBall (0 : E) r ∧ ‖S^[n] 0 - ξ‖ ≤ θ ^ n * r := by
  have : CompleteSpace (closedBall (0 : E) r) := isClosed_closedBall.completeSpace_coe
  have : Nonempty (closedBall (0 : E) r) := ⟨⟨0, by simpa using hr⟩⟩
  let f : closedBall (0 : E) r → closedBall (0 : E) r := fun x => ⟨S x, hmaps x x.2⟩
  have hf : ContractingWith ⟨θ, hθ0⟩ f := by
    refine ⟨hθ1, LipschitzWith.of_dist_le_mul fun x y => ?_⟩
    simp only [Subtype.dist_eq, dist_eq_norm, f]
    exact hlip x x.2 y y.2
  set x := ContractingWith.fixedPoint f hf with hx
  have hfix : f x = x := ContractingWith.fixedPoint_isFixedPt (hf := hf)
  have hSx : S x = x := congrArg Subtype.val hfix
  have hxr : (x : E) ∈ closedBall (0 : E) r := x.2
  refine ⟨x, x.2, hSx, ?_, ?_⟩
  · intro ξ' hξ' hS
    have : Function.IsFixedPt f ⟨ξ', hξ'⟩ := Subtype.ext hS
    exact congrArg Subtype.val (hf.fixedPoint_unique' this hfix)
  · have hxn : ‖(x : E)‖ ≤ r := mem_closedBall_zero_iff.mp x.2
    intro n
    induction n with
    | zero => exact ⟨by simpa using hr, by simpa using hxn⟩
    | succ n ih =>
      rw [Function.iterate_succ_apply']
      refine ⟨hmaps _ ih.1, ?_⟩
      have := hlip _ ih.1 _ hxr
      rw [hSx] at this
      calc ‖S (S^[n] 0) - x‖ ≤ θ * ‖S^[n] 0 - x‖ := this
        _ ≤ θ * (θ ^ n * r) := mul_le_mul_of_nonneg_left ih.2 hθ0
        _ = θ ^ (n + 1) * r := by ring

end FixedPoint


section Parameters

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup G] [NormedSpace ℂ G]

/-- **Analytic contraction with parameters.**  Let `P` be open, `B` the closed ball of radius `r`,
`T : E × G → E` analytic on `B × P`, mapping `B` into `B` for each `p ∈ P`, and a `θ`-contraction
(`θ < 1`) on `B` for each `p ∈ P`.  Then the fixed point `ξ* (p)` in `B` exists, is unique in `B`,
and is analytic in `p ∈ P`; moreover `‖ξ*(p) - T(0,p)‖ ≤ θ r` and
`‖ξ*(p)‖ ≤ ‖T(0,p)‖ / (1 - θ)`. -/
theorem exists_analytic_fixedPoint {T : E × G → E} {P : Set G} (hP : IsOpen P) {r θ : ℝ}
    (hr : 0 ≤ r) (hθ0 : 0 ≤ θ) (hθ1 : θ < 1)
    (hT : AnalyticOnNhd ℂ T (closedBall (0 : E) r ×ˢ P))
    (hmaps : ∀ p ∈ P, ∀ ξ ∈ closedBall (0 : E) r, T (ξ, p) ∈ closedBall (0 : E) r)
    (hlip : ∀ p ∈ P, ∀ ξ ∈ closedBall (0 : E) r, ∀ ξ' ∈ closedBall (0 : E) r,
      ‖T (ξ, p) - T (ξ', p)‖ ≤ θ * ‖ξ - ξ'‖) :
    ∃ ξs : G → E,
      (∀ p ∈ P, ξs p ∈ closedBall (0 : E) r ∧ T (ξs p, p) = ξs p ∧
        ∀ ξ ∈ closedBall (0 : E) r, T (ξ, p) = ξ → ξ = ξs p) ∧
      AnalyticOnNhd ℂ ξs P ∧
      ∀ p ∈ P, ‖ξs p - T (0, p)‖ ≤ θ * r ∧ ‖ξs p‖ ≤ ‖T (0, p)‖ / (1 - θ) := by
  classical
  have hex : ∀ p ∈ P, ∃ ξ ∈ closedBall (0 : E) r, T (ξ, p) = ξ ∧
      (∀ ξ' ∈ closedBall (0 : E) r, T (ξ', p) = ξ' → ξ' = ξ) ∧
      ∀ n : ℕ, (fun x => T (x, p))^[n] 0 ∈ closedBall (0 : E) r ∧
        ‖(fun x => T (x, p))^[n] 0 - ξ‖ ≤ θ ^ n * r :=
    fun p hp => exists_unique_fixedPoint_closedBall (S := fun x => T (x, p)) hr hθ0 hθ1
      (hmaps p hp) (hlip p hp)
  let ξs : G → E := fun p => if h : p ∈ P then Classical.choose (hex p h) else 0
  have hξs : ∀ p (h : p ∈ P), ξs p = Classical.choose (hex p h) := fun p h => by simp [ξs, h]
  have hspec := fun p (h : p ∈ P) => Classical.choose_spec (hex p h)
  -- iterates
  let it : ℕ → G → E := fun n p => (fun x => T (x, p))^[n] 0
  have hit_anal : ∀ n, AnalyticOnNhd ℂ (it n) P := by
    intro n
    induction n with
    | zero => exact analyticOnNhd_const
    | succ n ih =>
      have : it (n + 1) = fun p => T (it n p, p) := by
        funext p; simp only [it]; rw [Function.iterate_succ_apply']
      rw [this]
      exact AnalyticOnNhd.comp₂ hT ih analyticOnNhd_id (fun p hp =>
        ⟨(hspec p hp |>.2.2.2 n).1, hp⟩)
  refine ⟨ξs, fun p hp => ?_, ?_, fun p hp => ?_⟩
  · rw [hξs p hp]
    obtain ⟨h1, h2, h3, -⟩ := hspec p hp
    exact ⟨h1, h2, h3⟩
  · refine analyticOnNhd_of_tendstoUniformlyOn hP (f := it) (M := r) hit_anal
      (fun n p hp => by simpa using (hspec p hp).2.2.2 n |>.1) ?_
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    have ht : Tendsto (fun n : ℕ => θ ^ n * r) atTop (𝓝 0) := by
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hθ0 hθ1).mul_const r
    filter_upwards [ht.eventually (gt_mem_nhds hε)] with n hn p hp
    rw [dist_comm, dist_eq_norm, hξs p hp]
    exact lt_of_le_of_lt ((hspec p hp).2.2.2 n).2 hn
  · have h := hspec p hp
    rw [hξs p hp]
    obtain ⟨h1, h2, -, -⟩ := h
    have h0 : (0 : E) ∈ closedBall (0 : E) r := by simpa using hr
    have hn : ‖Classical.choose (hex p hp)‖ ≤ r := mem_closedBall_zero_iff.mp h1
    have hl := hlip p hp _ h1 0 h0
    rw [h2, sub_zero] at hl
    refine ⟨?_, ?_⟩
    · calc ‖Classical.choose (hex p hp) - T (0, p)‖ ≤ θ * ‖Classical.choose (hex p hp)‖ := hl
        _ ≤ θ * r := mul_le_mul_of_nonneg_left hn hθ0
    · rw [le_div_iff₀ (by linarith)]
      have := norm_sub_norm_le (Classical.choose (hex p hp)) (T (0, p))
      nlinarith [norm_nonneg (T (0, p))]

end Parameters

section RealRestriction

variable {E G H : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E]
  [IsScalarTower ℝ ℂ E] [NormedAddCommGroup G] [NormedSpace ℂ G] [NormedSpace ℝ G]
  [IsScalarTower ℝ ℂ G] [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- Real-analytic restriction: if `ξs` is complex-analytic on `P` and `γ : H →L[ℝ] G` is a
continuous real-linear map (for instance the inclusion of the real parameters `ℝ^ι ⊂ ℂ^ι`), then
`ξs ∘ γ` is real-analytic on `γ ⁻¹' P`. -/
theorem analyticOnNhd_real_comp {ξs : G → E} {P : Set G} (h : AnalyticOnNhd ℂ ξs P)
    (γ : H →L[ℝ] G) : AnalyticOnNhd ℝ (ξs ∘ γ) (γ ⁻¹' P) :=
  h.restrictScalars.compContinuousLinearMap

end RealRestriction

end Balaban.Analysis
