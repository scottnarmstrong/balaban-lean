/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.DecoupledIdent
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

/-!
# The Dirichlet operator `H₀` of `𝔹_k` as the limit `x → ∞` of the x-variant

`H₀ = H̃ + a_k L^{-2k} Q*Q|_{Ω_{k+1}}` is the limit of `H_{k,x}` as `x → ∞` (`s₁, s₂ → a_k`). The
uniform coercivity of the x-variant and the uniform lower bound for `M_{x,1}`
(`Balaban/Localization/DecoupledCovariance.lean`) pass to the limit, so that `H₀` and
`M₀ = φ₀² - K(φ₀) G₀ φ₀` are invertible, `G₀ = H₀⁻¹` (G-1(a) and G-2(v) for `H₀`).
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background Finset Matrix Filter Topology

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}

/-! ### Limits of the symbols -/

theorem tendsto_xS1 {ak : ℝ} (hak : 0 < ak) : Tendsto (xS1 ak) atTop (𝓝 ak) := by
  have h : Tendsto (fun x : ℝ => ak - ak ^ 2 / (ak + x)) atTop (𝓝 (ak - 0)) := by
    refine tendsto_const_nhds.sub ?_
    exact tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_left _ _ tendsto_id)
  rw [sub_zero] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with x hx
  unfold xS1
  have : ak + x ≠ 0 := by linarith
  field_simp
  ring

theorem tendsto_xS2 {ak b : ℝ} (hak : 0 < ak) (hb : 0 ≤ b) :
    Tendsto (xS2 ak b) atTop (𝓝 ak) := by
  have h : Tendsto (fun x : ℝ => ak - ak ^ 2 / (ak + x + b)) atTop (𝓝 (ak - 0)) := by
    refine tendsto_const_nhds.sub ?_
    refine tendsto_const_nhds.div_atTop ?_
    have : Tendsto (fun x : ℝ => x + (ak + b)) atTop atTop :=
      tendsto_atTop_add_const_right _ _ tendsto_id
    refine this.congr fun x => ?_
    ring
  rw [sub_zero] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with x hx
  unfold xS2
  have : ak + x + b ≠ 0 := by linarith
  field_simp
  ring

/-! ### Limits of matrices -/

section MatrixLimits

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem tendsto_matrix_inv {F : ℝ → Matrix ι ι ℂ} {A : Matrix ι ι ℂ}
    (hF : Tendsto F atTop (𝓝 A)) (hA : IsUnit A) :
    Tendsto (fun x => (F x)⁻¹) atTop (𝓝 A⁻¹) := by
  have hdet : Tendsto (fun x => (F x).det) atTop (𝓝 A.det) :=
    ((continuous_id.matrix_det).tendsto A).comp hF
  have hadj : Tendsto (fun x => (F x).adjugate) atTop (𝓝 A.adjugate) :=
    ((continuous_id.matrix_adjugate).tendsto A).comp hF
  have hne : A.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det _).1 hA).ne_zero
  have := (hdet.inv₀ hne).smul hadj
  rw [Matrix.inv_def, Ring.inverse_eq_inv']
  refine this.congr fun x => ?_
  rw [Matrix.inv_def, Ring.inverse_eq_inv']

omit [Fintype ι] [DecidableEq ι] in
theorem continuous_liftOp : Continuous (fun A : Matrix ι ι ℂ => liftOp N A) := by
  refine continuous_pi fun p => continuous_pi fun q => ?_
  by_cases hpq : p.2 = q.2
  · simp only [liftOp, hpq, ↓reduceIte]
    exact (continuous_apply q.1).comp (continuous_apply p.1)
  · simp only [liftOp, hpq, ↓reduceIte]
    exact continuous_const

omit [DecidableEq ι] in
theorem continuous_reQuad (u : ι → ℂ) : Continuous (fun A : Matrix ι ι ℂ => Green.reQuad A u) := by
  unfold Green.reQuad
  refine Complex.continuous_re.comp (continuous_finsetSum _ fun i _ => continuous_const.mul ?_)
  simp only [Matrix.mulVec, dotProduct]
  exact continuous_finsetSum _ fun j _ =>
    (continuous_id.matrix_elem i j).mul continuous_const

end MatrixLimits

/-! ### The Dirichlet operator `H₀` -/

section H0

variable (G : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ)

/-- **The Dirichlet operator of `𝔹_k`**: `H₀ = H̃ + a_k L^{-2k} Q*Q|_{Ω_{k+1}}`, the limit
`x → ∞` of `H_{k,x}`. -/
noncomputable def xH0 (a : ℕ → ℝ) (ν : ℝ) (α : G.Ω 1 → ℂ) : Matrix (G.Ω 1) (G.Ω 1) ℂ :=
  xHt G a ν α + ((a k / ((L : ℝ) ^ k) ^ 2 : ℝ) : ℂ) • Pk G

variable {G}

theorem tendsto_xDirichlet {a : ℕ → ℝ} {aT ν : ℝ} (hak : 0 < a k) (hb : 0 ≤ aT / (L : ℝ) ^ 2)
    (α : G.Ω 1 → ℂ) :
    Tendsto (fun x => xDirichletOperator G a aT x ν α) atTop (𝓝 (xH0 G a ν α)) := by
  have hL : (0 : ℝ) < ((L : ℝ) ^ k) ^ 2 := by
    have : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
    positivity
  have h1 : Tendsto (fun x => ((xS1 (a k) x / ((L : ℝ) ^ k) ^ 2 : ℝ) : ℂ)) atTop
      (𝓝 ((a k / ((L : ℝ) ^ k) ^ 2 : ℝ) : ℂ)) :=
    (Complex.continuous_ofReal.tendsto _).comp ((tendsto_xS1 hak).div_const _)
  have h2 : Tendsto (fun x => (((xS2 (a k) (aT / (L : ℝ) ^ 2) x - xS1 (a k) x) /
      ((L : ℝ) ^ k) ^ 2 : ℝ) : ℂ)) atTop (𝓝 ((0 : ℝ) : ℂ)) := by
    refine (Complex.continuous_ofReal.tendsto _).comp ?_
    have := (((tendsto_xS2 hak hb).sub (tendsto_xS1 hak)).div_const (((L : ℝ) ^ k) ^ 2))
    simpa using this
  have := (tendsto_const_nhds (x := xHt G a ν α)).add (h1.smul_const (Pk G)) |>.add
    (h2.smul_const (Pk1 G))
  simp only [Complex.ofReal_zero, zero_smul, add_zero] at this
  refine this.congr fun x => ?_
  rw [xDirichlet_eq_blocks]

theorem reQuad_xH0_ge {a : ℕ → ℝ} {aT ν : ℝ} {γ : ℝ} {α : G.Ω 1 → ℂ} (hak : 0 < a k)
    (hb : 0 ≤ aT / (L : ℝ) ^ 2)
    (hγ : ∀ x : ℝ, 0 ≤ x → Green.IsCoercive (xDirichletOperator G a aT x ν α) γ)
    (u : G.Ω 1 → ℂ) : γ * Green.sqNorm u ≤ Green.reQuad (xH0 G a ν α) u := by
  have h := ((continuous_reQuad u).tendsto _).comp (tendsto_xDirichlet (aT := aT) (ν := ν) hak hb α)
  refine ge_of_tendsto h ?_
  filter_upwards [eventually_ge_atTop 0] with x hx
  exact hγ x hx u

end H0

/-! ### `H₀` and `M₀` are invertible -/

section Units

variable {G : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ} {a : ℕ → ℝ} {aT ν : ℝ}
  {α : G.Ω 1 → ℂ} {δ : ℝ} {φ : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ}

theorem continuous_constraintM (φ' : G.Ω 1 → Fin N → ℂ) :
    Continuous (fun p : Matrix (G.Ω 1) (G.Ω 1) ℂ × Matrix (G.Ω 1) (G.Ω 1) ℂ =>
      constraintM p.1 p.2 φ') := by
  unfold constraintM commK
  refine continuous_const.sub ?_
  refine Continuous.matrix_mul (Continuous.matrix_mul ?_ (continuous_liftOp.comp continuous_snd))
    continuous_const
  exact (continuous_const.matrix_mul (continuous_liftOp.comp continuous_fst)).sub
    (continuous_fst.matrix_mul continuous_const)

/-- `H₀` is coercive, hence invertible (the limit of the uniform coercivity of the x-variant). -/
theorem xH0_isUnit (hfam : ∀ x, 0 ≤ x → XData G a aT ν x α 0 (fun _ => 1)) :
    IsUnit (xH0 G a ν α) := by
  have D0 := hfam 0 le_rfl
  have hL0 : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hak : 0 < a k := by
    have := (⟨D0.st.hak1, D0.st.hak2⟩ : _ ∧ _)
    linarith [this.1]
  have hb : 0 ≤ aT / (L : ℝ) ^ 2 := by
    have := D0.st.haT1
    positivity
  have hγ : ∀ x : ℝ, 0 ≤ x → Green.IsCoercive (xDirichletOperator G a aT x ν α)
      ((1 / 4 - 1 / 8) * (((L : ℝ) ^ (k + 1)) ^ 2)⁻¹) := by
    intro x hx
    have D := hfam x hx
    exact xDirichletOperator_isCoercive_sharp_of_ak G D.st.dg.hL D.st.dg.mass D.st.ha ⟨D.st.hak1, D.st.hak2⟩
      D.st.haT1 D.st.haT2 hx (θ := 1 / 8) (by norm_num) (by norm_num) α
      (AdmPot.le_eighth D.st.dg D.pot) (γ := (((L : ℝ) ^ (k + 1)) ^ 2)⁻¹) fun y => by
        have hp : 0 < G.spacing y := spacing_pos G
        exact inv_anti₀ (by positivity) (pow_le_pow_left₀ hp.le (spacing_le G y.2) 2)
  refine Green.isUnit_of_isCoercive (γ := (1 / 4 - 1 / 8) * (((L : ℝ) ^ (k + 1)) ^ 2)⁻¹)
    (by positivity) ?_
  intro u
  exact reQuad_xH0_ge hak hb hγ u

theorem decM_one_eq (hfam : ∀ x, 0 ≤ x → XData G a aT ν x α 0 (fun _ => 1)) {x : ℝ} (hx : 0 ≤ x)
    (φ : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) :
    decM G a aT x ν α (fun _ => 1) φ =
      constraintM (xDirichletOperator G a aT x ν α) (xDirichletOperator G a aT x ν α)⁻¹
        (restrictField G φ) := by
  have D := hfam x hx
  unfold decM
  rw [Gsx_one D.st D.pot hx D.isUnit_one_sub]

/-- **`M₀ = φ₀² - K(φ₀) G₀ φ₀` is invertible** (G-2(v) for `H₀`): the lower bound for `M_{x,1}`
is uniform in `x ≥ 0` and passes to the limit `x → ∞`. -/
theorem xM0_isUnit (hfam : ∀ x, 0 ≤ x → XData G a aT ν x α 0 (fun _ => 1))
    (hφ : IsConstraintField G δ φ) (hδ : 0 ≤ δ)
    (hsm : δ ^ 2 * smallConstX d L 0 ≤ 1 / 4) :
    IsUnit (constraintM (xH0 G a ν α) (xH0 G a ν α)⁻¹ (restrictField G φ)) := by
  have D0 := hfam 0 le_rfl
  have hak : 0 < a k := by
    have := (⟨D0.st.hak1, D0.st.hak2⟩ : _ ∧ _)
    linarith [this.1]
  have hb : 0 ≤ aT / (L : ℝ) ^ 2 := by
    have := D0.st.haT1
    positivity
  have hH0 := xH0_isUnit hfam
  have hHx := tendsto_xDirichlet (aT := aT) (ν := ν) hak hb α
  have hGx := tendsto_matrix_inv hHx hH0
  have hM : Tendsto (fun x => decM G a aT x ν α (fun _ => 1) φ) atTop
      (𝓝 (constraintM (xH0 G a ν α) (xH0 G a ν α)⁻¹ (restrictField G φ))) := by
    have := ((continuous_constraintM (restrictField G φ)).tendsto _).comp (hHx.prodMk_nhds hGx)
    refine this.congr' ?_
    filter_upwards [eventually_ge_atTop 0] with x hx
    rw [decM_one_eq hfam hx]
    rfl
  set M0 := constraintM (xH0 G a ν α) (xH0 G a ν α)⁻¹ (restrictField G φ) with hM0
  rw [← Matrix.mulVec_injective_iff_isUnit]
  intro f f' hff
  have hlin : M0 *ᵥ (f - f') = 0 := by rw [Matrix.mulVec_sub, hff, sub_self]
  have hlow : agmonSource G 0 (fun _ => 0) (f - f') ≤
      4 * agmonSource G 0 (fun _ => 0) (M0 *ᵥ (f - f')) := by
    have hc : Continuous (fun v : G.Ω 1 → ℂ => agmonSource G 0 (fun _ => 0) v) := by
      simp only [agmonSource_zero_eq]
      exact continuous_finsetSum _ fun y _ => continuous_const.mul
        ((continuous_norm.comp (continuous_apply y)).pow 2)
    have h1 : Tendsto (fun x => decM G a aT x ν α (fun _ => 1) φ *ᵥ (f - f')) atTop
        (𝓝 (M0 *ᵥ (f - f'))) :=
      ((continuous_id.matrix_mulVec (continuous_const (y := f - f'))).tendsto M0).comp hM
    have h2 := (hc.tendsto _).comp h1
    refine le_of_tendsto_of_tendsto tendsto_const_nhds (h2.const_mul 4) ?_
    filter_upwards [eventually_ge_atTop 0] with x hx
    have D := hfam x hx
    exact decM_lower D D.weight_zero hφ hδ hsm (f - f')
  rw [hlin] at hlow
  have h0 : agmonSource G 0 (fun _ => 0) (0 : G.Ω 1 → ℂ) = 0 := by
    rw [agmonSource_zero_eq]; simp
  rw [h0, mul_zero] at hlow
  exact sub_eq_zero.1 (eq_zero_of_agmonSource_zero hlow)

end Units

end Balaban.Localization
