/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Spine.FinalValueAlg
public import Balaban.Background.Def5Response
public import Balaban.LargeField.Background.CubeUnitBg
public import Balaban.LargeField.R.PsiZeroHessLine
public import Balaban.Background.Contraction

/-!
# The second variation of the variational function at the constant configuration

A6-3 (a), step (P1b). Let `D₀ = (e, e)` be the constant unit datum of a generating set `G`. Along a
real tangent datum `E` (vanishing off `Ω₁`, `h̃ = 0`) the value of the action at the background field,
`V(t) = A(D₀ + tE, φ(t))`, satisfies `V(t)/t² → ½ (∑ w |E|² − Ṡ · (G − Π) Ṡ)` where `Ṡ = source E`,
`G = H⁻¹`, `Π` the constrained operator at `φ₀ = e`. The proof uses the exact expansion
`actionC_line_pair` (no differentiation of the minimizer) and the linear response
`theorem72_linearResponse`.
-/

@[expose] public section

open Filter Topology Matrix Balaban.Multiscale Balaban.Background Balaban.LargeField

namespace Balaban.RootFSpine

variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ} {G : GeneratingSet d L N₀ k ϱ}
  {a : ℕ → ℝ} {ν : ℝ}

theorem bgC2_pos (hd : 0 < d) : 0 < bgC2 d L N := by
  have h1 := bgC1_pos_of (d := d) (L := L) (N := N) hd
  have hK := bgK1_pos d L N
  have hS := smallnessConst_nonneg (d := d) hd
  have hSw := sandwichConst_nonneg d L N
  unfold bgC2
  exact lt_min h1 (by positivity)

/-- **The constant unit datum lies in the complex union domain with `δ ≤ c₂`.** -/
theorem constUnitBg_inUnionDomainC (H : BgHyp d L k ϱ a ν) {e : Fin N → ℝ}
    (he : ∑ i, e i ^ 2 = 1) :
    InUnionDomainC G (bgC0 d L N) (bgC2 d L N) ν (constUnitBg G e) := by
  have hd : 0 < d := by have := H.hd; omega
  set r := min (bgC0 d L N) (bgC2 d L N) with hr
  have hr0 : 0 < r := lt_min (bgC0_pos d L N hd) (bgC2_pos hd)
  refine ⟨r, r, hr0, le_rfl, min_le_left _ _, min_le_right _ _, ?_, ?_⟩
  · have h1 := H.massLe
    have : ν * ((L : ℝ) ^ k) ^ 2 * r ^ 2 ≤ 1 * r ^ 2 :=
      mul_le_mul_of_nonneg_right h1 (by positivity)
    linarith
  · refine ⟨fun _ => e, e, 0, 0, ?_, fun _ hx i => by simpa using constUnitBg_Ψ hx i, fun _ hx i => ?_⟩
    · exact
        { toInPsiTilde := constUnitBg_inPsiTilde he ν hr0
          eps_pos := hr0
          layerConst' := fun _ _ _ _ _ _ _ => rfl
          hLayerConst' := fun _ _ _ _ _ _ _ => rfl
          c1 := fun _ _ _ => by simpa [vn] using hr0
          c2a := fun _ _ => by simpa [vn] using add_pos hr0 hr0
          c2b := fun _ _ => by simpa using hr0
          c3a := fun _ _ => by simpa [vn] using div_pos (pow_pos hr0 2) hr0
          c3b := fun _ _ => by simpa using pow_pos hr0 2 }
    · simpa using constUnitBg_h hx i

section Expansion

variable (E : BgData G N) (hE : ∀ x, x ∉ G.Ω 1 → E.Ψ x = 0) (hEh : ∀ x, E.h x = 0)

include hE hEh

/-- The block term of the quadratic form at the field `0`: `A(tE, 0) = t² A(E, 0)`. -/
theorem actionC_zero_line_scale (t : ℂ) :
    actionC G a ν ((bgZero G N).lineAt E t) 0 = t ^ 2 * actionC G a ν ((bgZero G N).lineAt E 1) 0 := by
  have hz : ∀ s : ℂ, ∀ x, x ∉ G.Ω 1 → ((bgZero G N).lineAt E s).Ψ x = 0 := fun s x hx => by
    simp [BgData.lineAt, bgZero, hE x hx]
  have hb : ∀ s : ℂ, barField G ((bgZero G N).lineAt E s).Ψ (0 : G.Ω 1 × Fin N → ℂ) = 0 :=
    fun s => by
      rw [barField_line (bgZero G N) E hE s]
      exact barField_zero _ (fun x _ => rfl)
  have key : ∀ s : ℂ, actionC G a ν ((bgZero G N).lineAt E s) 0 =
      (1 / 2) * ∑ x : G.Ω 1, ((a (G.layerIndex (x : Torus d (N₀ * L ^ k))) /
        ((L : ℝ) ^ G.layerIndex (x : Torus d (N₀ * L ^ k))) ^ 2 : ℝ) : ℂ) *
        ∑ i, (s * E.Ψ x i) * (s * E.Ψ x i) := by
    intro s
    unfold actionC
    rw [hb s, blockAvg_zero]
    simp [BgData.lineAt, bgZero, hEh]
  rw [key t, key 1]
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

/-- **The quadratic form along the zero-datum line**: with `W = A(E, 0)`,
`A(tE, τ) = t² W + ½ ⟨τ, H₀ τ⟩ − t ⟨τ, Ṡ⟩`, `Ṡ = source E`, `H₀ = H(0)`. -/
theorem actionC_zero_line_quad (t : ℂ) (τ : G.Ω 1 × Fin N → ℂ) :
    actionC G a ν ((bgZero G N).lineAt E t) τ =
      t ^ 2 * actionC G a ν ((bgZero G N).lineAt E 1) 0 +
        (1 / 2) * pair G τ (liftOp N (dirichletOperator G a ν 0) *ᵥ τ) -
          t * pair G τ (source G a ν E) := by
  have h := actionC_add (a := a) (ν := ν) ((bgZero G N).lineAt E t) 0 τ
  rw [zero_add, Matrix.mulVec_zero, source_zero_line, zero_sub, actionC_zero_line_scale E hE hEh t] at h
  have e : pair G τ (-(t • source G a ν E)) = -(t * pair G τ (source G a ν E)) := by
    have := pair_smul_right (G := G) τ (source G a ν E) (-t)
    have e2 : (-(t • source G a ν E)) = fun p => -t * source G a ν E p := by
      funext p; simp
    rw [e2, this]; ring
  rw [e] at h
  linear_combination h

end Expansion

section Pair

theorem pair_smul_left (u v : G.Ω 1 × Fin N → ℂ) (c : ℂ) :
    pair G (c • u) v = c * pair G u v := by
  unfold pair
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun p _ => by simp [mul_assoc]

theorem pair_smul_right' (u v : G.Ω 1 × Fin N → ℂ) (c : ℂ) :
    pair G u (c • v) = c * pair G u v := by
  unfold pair
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun p _ => by simp [mul_left_comm]

theorem continuous_pair_left (v : G.Ω 1 × Fin N → ℂ) :
    Continuous fun u : G.Ω 1 × Fin N → ℂ => pair G u v := by
  unfold pair
  fun_prop

theorem pair_comm' (u v : G.Ω 1 × Fin N → ℂ) : pair G u v = pair G v u := by
  unfold pair
  exact Finset.sum_congr rfl fun p _ => mul_comm _ _

end Pair

section Const

variable (E : BgData G N) (hE : ∀ x, x ∉ G.Ω 1 → E.Ψ x = 0) (hEh : ∀ x, E.h x = 0)

include hE hEh

/-- **The action along the line from the constant datum, at any field** (exact, no minimizer):
`A(D₀ + tE, φ) = A(tE, φ − φ₀)` for the constant unit datum `D₀ = (e, e)`, `φ₀ ≡ e`. -/
theorem actionC_const_line (e : Fin N → ℝ) (t : ℂ) (φ : G.Ω 1 × Fin N → ℂ) :
    actionC G a ν ((constUnitBg G e).lineAt E t) φ =
      actionC G a ν ((bgZero G N).lineAt E t) (φ - constUnitPhi G e) := by
  have hEL : ∀ p, (liftOp N (dirichletOperator G a ν 0) *ᵥ constUnitPhi G e) p -
      source G a ν (constUnitBg G e) p = -((fun _ : G.Ω 1 => (0 : ℂ)) p.1 * constUnitPhi G e p) := by
    rintro ⟨x, i⟩
    rw [dirichlet_const_eq_source]
    simp
  have h := actionC_line_pair (a := a) (ν := ν) (constUnitBg G e) E hE hEh t (constUnitPhi G e)
    (φ - constUnitPhi G e) (fun _ => 0) hEL
  rw [add_sub_cancel] at h
  have hfv : firstVar a (constUnitBg G e) E (constUnitPhi G e) = 0 := by
    unfold firstVar
    refine Finset.sum_eq_zero fun x _ => ?_
    refine mul_eq_zero_of_right _ ?_
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [constUnitBg_Ψ ((mem_dataSites G).2 (Or.inl x.2)), blockAvg_constUnitPhi e x.2, sub_self,
      mul_zero]
  have hp : pair G (φ - constUnitPhi G e) (fun p => (fun _ : G.Ω 1 => (0 : ℂ)) p.1 * constUnitPhi G e p)
      = 0 := by
    simp [pair]
  have h0 : actionC G a ν (constUnitBg G e) (constUnitPhi G e) = 0 := by
    have := action_cast (a := a) (ν := ν) (constUnitBg G e) (constUnitBg_isReal e)
      (φ := constUnitPhi G e) (fun x i => by simp [constUnitPhi])
    rw [← this, action_constUnitBg_eq_zero]
    simp
  rw [h, hfv, hp, h0]
  ring

/-- The constant field `e` as a field on `Ω₁` with values in `ℂ^N`. -/
def constVec (G : GeneratingSet d L N₀ k ϱ) (e : Fin N → ℝ) : G.Ω 1 → Fin N → ℂ :=
  fun _ i => (e i : ℂ)

omit hE hEh in
/-- **The response data at the constant configuration**: the difference quotient of the background
field converges to `φ̇ = (H⁻¹ − Π) Ṡ`, and `⟨φ̇, H φ̇⟩ = ⟨φ̇, Ṡ⟩`. -/
theorem const_response (H : BgHyp d L k ϱ a ν) {e : Fin N → ℝ} (he : ∑ i, e i ^ 2 = 1) :
    ∃ φd : G.Ω 1 × Fin N → ℂ,
      φd = (liftOp N (dirichletOperator G a ν 0)⁻¹ -
          constrainedOp (dirichletOperator G a ν 0)⁻¹ (constVec G e)) *ᵥ source G a ν E ∧
      Tendsto (fun t : ℂ => t⁻¹ • (bgFieldC G a ν (bgC0 d L N)
        ((constUnitBg G e).lineAt E t) - constUnitPhi G e)) (𝓝[≠] 0) (𝓝 φd) ∧
      pair G φd (liftOp N (dirichletOperator G a ν 0) *ᵥ φd) = pair G φd (source G a ν E) := by
  classical
  set D₀ := constUnitBg G e with hD₀
  have hD := constUnitBg_inUnionDomainC (G := G) (a := a) H he
  have hf0 : bgFieldC G a ν (bgC0 d L N) D₀ = constUnitPhi G e := bgFieldC_constUnitBg H he
  have hα0 : bgMultC G a ν (bgC0 d L N) D₀ = 0 := bgMultC_constUnitBg H he
  obtain ⟨φd, αd, h1, h2, hα, hφ, -⟩ := theorem72_linearResponse H hD E
  have hbgOp : bgOp a ν D₀ = dirichletOperator G a ν 0 := by unfold bgOp; rw [hα0]
  have hvec : bgVec a ν D₀ = constVec G e := by
    funext x i; simp [bgVec, hf0, constUnitPhi, constVec]
  rw [hbgOp, hvec] at hφ hα
  obtain ⟨δ, ε, hδ0, hδε, hε, hδc, hνε, hDC⟩ := hD
  have St := standing_bgFieldC H hδ0 hδε hε hδc hνε hDC
  have hrestrict : restrictField G (fun y i => barField G D₀.Ψ
      (bgFieldC G a ν (bgC0 d L N) D₀) y i) = constVec G e := by
    rw [← hvec]
    funext z i
    simp [restrictField, barField, bgVec]
  have hMu := constraintForm_isUnit St
  have hHu := dirichletOperator_isUnit G St.pos St.mass St.weights _ St.alpha
  rw [hrestrict, hα0] at hMu
  rw [hα0] at hHu
  obtain ⟨hs1, hs2⟩ := response_formula_solves hHu hMu (source G a ν E)
  have E1 : liftOp N (dirichletOperator G a ν 0) *ᵥ φd +
      fieldMul (constVec G e) *ᵥ αd = source G a ν E := by rw [hφ, hα]; exact hs1
  have E2 : (fieldMul (constVec G e))ᵀ *ᵥ φd = 0 := by rw [hφ]; exact hs2
  have hpT : pair G φd (fieldMul (constVec G e) *ᵥ αd) = 0 := by
    unfold pair
    have : ∀ p : G.Ω 1 × Fin N, φd p * (fieldMul (constVec G e) *ᵥ αd) p =
        αd p.1 * (constVec G e p.1 p.2 * φd p) := by
      rintro ⟨x, i⟩
      rw [fieldMul_mulVec]; ring
    simp only [this, Fintype.sum_prod_type]
    refine Finset.sum_eq_zero fun x _ => ?_
    rw [← Finset.mul_sum]
    have := congrFun E2 x
    rw [fieldMul_transpose_mulVec] at this
    rw [this]; simp
  have hH0 : pair G φd (liftOp N (dirichletOperator G a ν 0) *ᵥ φd) = pair G φd (source G a ν E) := by
    have : liftOp N (dirichletOperator G a ν 0) *ᵥ φd = source G a ν E -
        fieldMul (constVec G e) *ᵥ αd := by rw [← E1]; abel
    rw [this, pair_sub_right, hpT, sub_zero]
  set u : ℂ → G.Ω 1 × Fin N → ℂ := fun t => t⁻¹ • (bgFieldC G a ν (bgC0 d L N)
    (D₀.lineAt E t) - constUnitPhi G e) with hu
  have h1' : HasDerivAt (fun t : ℂ => bgFieldC G a ν (bgC0 d L N) (D₀.lineAt E t) -
      constUnitPhi G e) φd 0 := h1.sub_const _
  have hlim : Tendsto u (𝓝[≠] 0) (𝓝 φd) := by
    have := (hasDerivAt_iff_tendsto_slope_zero.1 h1')
    refine this.congr fun t => ?_
    simp only [hu, zero_add, BgData.lineAt_zero, hf0, sub_self, sub_zero]
  exact ⟨φd, hφ, hlim, hH0⟩

/-- **The second variation of the variational function at the constant configuration.**
For `D₀ = (e, e)`, `|e| = 1`, and a real tangent datum `E` vanishing off `Ω₁` with `h̃ = 0`, the value
of the action at the background field of `D₀ + tE` is, to second order,
`t² (A(E, 0) − ½ ⟨φ̇, Ṡ⟩)`, with `Ṡ = source E` and `φ̇ = (H⁻¹ − Π) Ṡ`, `H = H_{D₀}(0)`,
`Π = constrainedOp H⁻¹ e`. -/
theorem value_quadratic_limit (H : BgHyp d L k ϱ a ν) {e : Fin N → ℝ} (he : ∑ i, e i ^ 2 = 1) :
    Tendsto (fun t : ℂ => actionC G a ν ((constUnitBg G e).lineAt E t)
        (bgFieldC G a ν (bgC0 d L N) ((constUnitBg G e).lineAt E t)) / t ^ 2) (𝓝[≠] 0)
      (𝓝 (actionC G a ν ((bgZero G N).lineAt E 1) 0 -
        (1 / 2) * pair G ((liftOp N (dirichletOperator G a ν 0)⁻¹ -
          constrainedOp (dirichletOperator G a ν 0)⁻¹ (constVec G e)) *ᵥ source G a ν E)
          (source G a ν E))) := by
  classical
  obtain ⟨φd, hφ, hlim, hH0⟩ := const_response E H he
  set D₀ := constUnitBg G e with hD₀
  have hf0 : bgFieldC G a ν (bgC0 d L N) D₀ = constUnitPhi G e := bgFieldC_constUnitBg H he
  set u : ℂ → G.Ω 1 × Fin N → ℂ := fun t => t⁻¹ • (bgFieldC G a ν (bgC0 d L N)
    (D₀.lineAt E t) - constUnitPhi G e) with hu
  set W := actionC G a ν ((bgZero G N).lineAt E 1) 0 with hW
  set g : (G.Ω 1 × Fin N → ℂ) → ℂ := fun w => W +
    (1 / 2) * pair G w (liftOp N (dirichletOperator G a ν 0) *ᵥ w) - pair G w (source G a ν E)
    with hg
  have hgc : Continuous g := by
    have c1 : Continuous fun w : G.Ω 1 × Fin N → ℂ =>
        pair G w (liftOp N (dirichletOperator G a ν 0) *ᵥ w) := by
      unfold pair
      fun_prop
    exact (continuous_const.add (continuous_const.mul c1)).sub (continuous_pair_left _)
  have hlim2 : Tendsto (fun t => g (u t)) (𝓝[≠] 0) (𝓝 (g φd)) :=
    (hgc.tendsto φd).comp hlim
  have hgφ : g φd = W - (1 / 2) * pair G φd (source G a ν E) := by
    simp only [hg]; rw [hH0]; ring
  have hev : (fun t : ℂ => actionC G a ν (D₀.lineAt E t)
      (bgFieldC G a ν (bgC0 d L N) (D₀.lineAt E t)) / t ^ 2) =ᶠ[𝓝[≠] 0] fun t => g (u t) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    have ht0 : t ≠ 0 := ht
    have hτu : bgFieldC G a ν (bgC0 d L N) (D₀.lineAt E t) - constUnitPhi G e = t • u t := by
      simp only [hu]; rw [smul_inv_smul₀ ht0]
    rw [actionC_const_line E hE hEh e t, actionC_zero_line_quad E hE hEh t]
    simp only [hg, hτu, Matrix.mulVec_smul, pair_smul_left, pair_smul_right']
    field_simp
    ring
  have hfin := hlim2.congr' hev.symm
  rw [hgφ] at hfin
  rw [hφ] at hfin
  exact hfin

omit hE hEh in
/-- Changing the mass in the action only changes the last summand. -/
theorem actionC_mass_change (ν' : ℝ) (D : BgData G N) (φ : G.Ω 1 × Fin N → ℂ) :
    actionC G a ν' D φ = actionC G a ν D φ +
      (((ν' - ν : ℝ) : ℂ) / 2) * ∑ x : G.Ω 1, ∑ i, (φ (x, i) - D.h x i) * (φ (x, i) - D.h x i) := by
  unfold actionC
  push_cast
  ring

/-- **The second variation with a different action mass** (`ν'` in the action, `ν` in the
background): the limit of `value_quadratic_limit` plus `½ (ν' − ν) ⟨φ̇, φ̇⟩`. -/
theorem value_quadratic_limit_mass (H : BgHyp d L k ϱ a ν) {e : Fin N → ℝ}
    (he : ∑ i, e i ^ 2 = 1) (ν' : ℝ) :
    Tendsto (fun t : ℂ => actionC G a ν' ((constUnitBg G e).lineAt E t)
        (bgFieldC G a ν (bgC0 d L N) ((constUnitBg G e).lineAt E t)) / t ^ 2) (𝓝[≠] 0)
      (𝓝 (actionC G a ν ((bgZero G N).lineAt E 1) 0 -
        (1 / 2) * pair G ((liftOp N (dirichletOperator G a ν 0)⁻¹ -
          constrainedOp (dirichletOperator G a ν 0)⁻¹ (constVec G e)) *ᵥ source G a ν E)
          (source G a ν E) +
        (((ν' - ν : ℝ) : ℂ) / 2) * pair G ((liftOp N (dirichletOperator G a ν 0)⁻¹ -
          constrainedOp (dirichletOperator G a ν 0)⁻¹ (constVec G e)) *ᵥ source G a ν E)
          ((liftOp N (dirichletOperator G a ν 0)⁻¹ -
          constrainedOp (dirichletOperator G a ν 0)⁻¹ (constVec G e)) *ᵥ source G a ν E))) := by
  classical
  obtain ⟨φd, hφ, hlim, -⟩ := const_response E H he
  have main := value_quadratic_limit E hE hEh H he
  set u : ℂ → G.Ω 1 × Fin N → ℂ := fun t => t⁻¹ • (bgFieldC G a ν (bgC0 d L N)
    ((constUnitBg G e).lineAt E t) - constUnitPhi G e) with hu
  have hpc : Continuous fun w : G.Ω 1 × Fin N → ℂ => pair G w w := by
    unfold pair; fun_prop
  have hlim2 : Tendsto (fun t => (((ν' - ν : ℝ) : ℂ) / 2) * pair G (u t) (u t)) (𝓝[≠] 0)
      (𝓝 ((((ν' - ν : ℝ) : ℂ) / 2) * pair G φd φd)) :=
    (((hpc.tendsto φd).comp hlim).const_mul _)
  have hsum := main.add hlim2
  rw [← hφ] at hsum ⊢
  refine hsum.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  have ht0 : t ≠ 0 := ht
  have hh : ∀ x : G.Ω 1, ∀ i, ((constUnitBg G e).lineAt E t).h x i = (e i : ℂ) := fun x i => by
    simp [BgData.lineAt, constUnitBg_h x.2, hEh]
  rw [actionC_mass_change (ν := ν) ν']
  have hτ : ∑ x : G.Ω 1, ∑ i, (bgFieldC G a ν (bgC0 d L N) ((constUnitBg G e).lineAt E t) (x, i) -
      ((constUnitBg G e).lineAt E t).h x i) *
      (bgFieldC G a ν (bgC0 d L N) ((constUnitBg G e).lineAt E t) (x, i) -
        ((constUnitBg G e).lineAt E t).h x i) = t ^ 2 * pair G (u t) (u t) := by
    have hτu : bgFieldC G a ν (bgC0 d L N) ((constUnitBg G e).lineAt E t) - constUnitPhi G e =
        t • u t := by simp only [hu]; rw [smul_inv_smul₀ ht0]
    set τ := bgFieldC G a ν (bgC0 d L N) ((constUnitBg G e).lineAt E t) - constUnitPhi G e with hτdef
    have e1 : ∑ x : G.Ω 1, ∑ i, (bgFieldC G a ν (bgC0 d L N) ((constUnitBg G e).lineAt E t) (x, i) -
        ((constUnitBg G e).lineAt E t).h x i) *
        (bgFieldC G a ν (bgC0 d L N) ((constUnitBg G e).lineAt E t) (x, i) -
          ((constUnitBg G e).lineAt E t).h x i) = pair G τ τ := by
      unfold pair
      rw [Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun i _ => ?_
      simp only [hτdef, Pi.sub_apply, hh x i, constUnitPhi]
    rw [e1, hτu, pair_smul_left, pair_smul_right']
    ring
  rw [hτ]
  field_simp

end Const

end Balaban.RootFSpine
