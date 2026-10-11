/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Multiscale.ConstraintSandwich
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Block-to-block decay of the constrained operator (GREEN.md G-2(v), G-1(d)(3))

For a vector field `f` supported in the block `Δ_{j'}(y')` and `u = Π f`, the weighted bounds of
`Balaban.Multiscale.constrained_weighted_bounds` with the weight exponent `r = d(·, y')` (truncated
path distance) give the decay of the block norms of `u` in the path metric.
-/

@[expose] public section

namespace Balaban.Multiscale

open Matrix Finset

variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}

section Blocks

variable (G : GeneratingSet d L N₀ k ϱ)

/-- `∑_{x ∈ Δ_j(y)} |ũ(x)|²` for a vector field. -/
noncomputable def blkNormSq (u : G.Ω 1 × Fin N → ℂ) (j : ℕ) (y : Torus d (N₀ * L ^ k)) : ℝ :=
  ∑ x ∈ G.blk j y, ∑ i, ‖zeroExt (G.Ω 1) (comp G u i) x‖ ^ 2

/-- `∑_{x ∈ Δ_j(y)} ∑_μ |ũ(x + e_μ) - ũ(x)|²` for a vector field. -/
noncomputable def blkGradSq (u : G.Ω 1 × Fin N → ℂ) (j : ℕ) (y : Torus d (N₀ * L ^ k)) : ℝ :=
  ∑ x ∈ G.blk j y, ∑ μ : Fin d, ∑ i,
    ‖zeroExt (G.Ω 1) (comp G u i) (x + Pi.single μ 1) - zeroExt (G.Ω 1) (comp G u i) x‖ ^ 2

theorem blkNormSq_nonneg (u : G.Ω 1 × Fin N → ℂ) (j : ℕ) (y : Torus d (N₀ * L ^ k)) :
    0 ≤ blkNormSq G u j y := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem blkGradSq_nonneg (u : G.Ω 1 × Fin N → ℂ) (j : ℕ) (y : Torus d (N₀ * L ^ k)) :
    0 ≤ blkGradSq G u j y :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- The block norm is controlled by the weighted norm `vecM`. -/
theorem blkNormSq_le_vecM {r : Torus d (N₀ * L ^ k) → ℝ} (hr : IsAgmonWeight G r) {ε : ℝ}
    (hε0 : 0 ≤ ε) {j : ℕ} (hj1 : 1 ≤ j) (hjk : j ≤ k) {y : Torus d (N₀ * L ^ k)}
    (hy : y ∈ G.layer j) (u : G.Ω 1 × Fin N → ℂ) :
    (((L : ℝ) ^ j) ^ 2)⁻¹ * Real.exp (2 * ε * (r y - 2 * d)) * blkNormSq G u j y ≤
      vecM G ε r u := by
  rw [vecM_eq, blkNormSq, Finset.sum_comm, Finset.mul_sum]
  exact Finset.sum_le_sum fun i _ => blk_lower G hr hε0 hj1 hjk hy (comp G u i)

/-- The block gradient is controlled by the weighted gradient `vecGrad`. -/
theorem blkGradSq_le_vecGrad {r : Torus d (N₀ * L ^ k) → ℝ} (hr : IsAgmonWeight G r) {ε : ℝ}
    (hε0 : 0 ≤ ε) {j : ℕ} (hj1 : 1 ≤ j) (hjk : j ≤ k) {y : Torus d (N₀ * L ^ k)}
    (hy : y ∈ G.layer j) (u : G.Ω 1 × Fin N → ℂ) :
    Real.exp (2 * ε * (r y - 2 * d)) * blkGradSq G u j y ≤ vecGrad G ε r u := by
  unfold blkGradSq vecGrad
  rw [Finset.mul_sum]
  have hsub : G.blk j y ⊆ G.Ω 1 := fun x hx =>
    G.layer_subset hj1 hjk ((G.mem_layer_iff hj1 hjk (G.mem_blk.1 hx)).2 hy)
  refine le_trans ?_ (Finset.sum_le_sum_of_subset_of_nonneg hsub fun x _ _ =>
    Finset.sum_nonneg fun μ _ => by positivity)
  refine Finset.sum_le_sum fun x hx => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun μ _ => ?_
  have hw := blk_weight_ge G hr hε0 hj1 hjk hy hx
  have hv : ∑ i, ‖zeroExt (G.Ω 1) (comp G u i) (x + Pi.single μ 1) -
      zeroExt (G.Ω 1) (comp G u i) x‖ ^ 2 =
      vn (svec G u (x + Pi.single μ 1) - svec G u x) ^ 2 := by
    rw [vn_sq]; rfl
  rw [hv]
  calc _ ≤ Real.exp (ε * r x) ^ 2 * vn (svec G u (x + Pi.single μ 1) - svec G u x) ^ 2 :=
        mul_le_mul_of_nonneg_right hw (sq_nonneg _)
    _ ≤ _ := by
        have := sq_nonneg (vn (svec G u (x - Pi.single μ 1) - svec G u x))
        nlinarith [Real.exp_pos (ε * r x)]

end Blocks

section Decay

variable {G : GeneratingSet d L N₀ k ϱ} {a : ℕ → ℝ} {ν : ℝ} {α : G.Ω 1 → ℂ} {δ : ℝ}
  {φ : Torus d (N₀ * L ^ k) → Fin N → ℂ}

/-- The weighted source norm of a vector field supported in one block. -/
theorem vecSrc_le {r : Torus d (N₀ * L ^ k) → ℝ} (hr : IsAgmonWeight G r) {ε : ℝ}
    (hε0 : 0 ≤ ε) {j' : ℕ} (hj'1 : 1 ≤ j') (hj'k : j' ≤ k) {y' : Torus d (N₀ * L ^ k)}
    (hy' : y' ∈ G.layer j') (hry' : r y' = 0) {f : G.Ω 1 × Fin N → ℂ}
    (hsupp : ∀ (x : G.Ω 1) (i : Fin N), f (x, i) ≠ 0 →
      jBlock d L N₀ k j' x = jBlock d L N₀ k j' y') :
    vecSrc G ε r f ≤ ((L : ℝ) ^ j') ^ 2 * Real.exp (4 * ε * d) *
      ∑ i, Green.sqNorm (comp G f i) := by
  unfold vecSrc
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun i _ =>
    agmonSource_le G hr hε0 hj'1 hj'k hy' hry' (fun x hx => hsupp x i hx)

variable (St : Standing G a ν α δ φ)

include St

/-- **G-2(v), block form (squared).**  For `f` supported in the block `Δ_{j'}(y')` and
`0 ≤ t ≤ d(y, y')`, `0 ≤ ε ≤ ε₀`, the block norms of `Π f` on `Δ_j(y)` decay like `e^{-εt}`. -/
theorem constrained_block {j j' : ℕ} (hj1 : 1 ≤ j) (hjk : j ≤ k) (hj'1 : 1 ≤ j') (hj'k : j' ≤ k)
    {y y' : Torus d (N₀ * L ^ k)} (hy : y ∈ G.layer j) (hy' : y' ∈ G.layer j')
    {f : G.Ω 1 × Fin N → ℂ}
    (hsupp : ∀ (x : G.Ω 1) (i : Fin N), f (x, i) ≠ 0 →
      jBlock d L N₀ k j' x = jBlock d L N₀ k j' y')
    {t : ℝ} (ht0 : 0 ≤ t) (ht : ENNReal.ofReal t ≤ G.pathDist y y') {ε : ℝ} (hε0 : 0 ≤ ε)
    (hε1 : ε ≤ agmonRate d) :
    blkNormSq G (constrainedOp (dirichletOperator G a ν α)⁻¹ (restrictField G φ) *ᵥ f) j y ≤
        360 / poincareConst d ^ 2 * ((L : ℝ) ^ j) ^ 2 * ((L : ℝ) ^ j') ^ 2 *
          Real.exp (-(2 * ε * t)) * ∑ i, Green.sqNorm (comp G f i) ∧
      blkGradSq G (constrainedOp (dirichletOperator G a ν α)⁻¹ (restrictField G φ) *ᵥ f) j y ≤
        900 / poincareConst d * ((L : ℝ) ^ j') ^ 2 * Real.exp (-(2 * ε * t)) *
          ∑ i, Green.sqNorm (comp G f i) := by
  have hp0 := poincareConst_pos St.pos
  have hεd := rate_mul_le St.pos hε1
  have h8 : Real.exp (8 * (ε * d)) ≤ 2 := exp_eight_mul_le_two (by positivity) hεd
  have hr : IsAgmonWeight G (G.truncDist y' t) := G.isAgmonWeight_truncDist y' t
  have hry : G.truncDist y' t y = t := G.truncDist_eq_of_le ht0 ht
  have hry' : G.truncDist y' t y' = 0 := G.truncDist_self (G.layer_subset hj'1 hj'k hy') t
  obtain ⟨hM, hGr⟩ := constrained_weighted_bounds St hr hε0 hε1 f
  have hsrc := vecSrc_le hr hε0 hj'1 hj'k hy' hry' hsupp
  have hlow := blkNormSq_le_vecM G hr hε0 hj1 hjk hy
    (constrainedOp (dirichletOperator G a ν α)⁻¹ (restrictField G φ) *ᵥ f)
  have hgrad := blkGradSq_le_vecGrad G hr hε0 hj1 hjk hy
    (constrainedOp (dirichletOperator G a ν α)⁻¹ (restrictField G φ) *ᵥ f)
  rw [hry] at hlow hgrad
  have hFv : 0 ≤ ∑ i, Green.sqNorm (comp G f i) :=
    Finset.sum_nonneg fun i _ => Green.sqNorm_nonneg _
  have hE10 : 0 < Real.exp (2 * ε * (t - 2 * d)) := Real.exp_pos _
  have hA0 : 0 < ((L : ℝ) ^ j) ^ 2 := by
    have : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
    positivity
  have hLj : ((L : ℝ) ^ j) ≠ 0 := by
    have : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
    positivity
  have hE2inv : (Real.exp (2 * ε * (t - 2 * d)))⁻¹ =
      Real.exp (-(2 * ε * t)) * Real.exp (4 * ε * d) := by
    rw [← Real.exp_neg, ← Real.exp_add]; congr 1; ring
  have e8 : Real.exp (4 * ε * d) * Real.exp (4 * ε * d) ≤ 2 := by
    rw [← Real.exp_add]
    have : 4 * ε * d + 4 * ε * d = 8 * (ε * d) := by ring
    rw [this]; exact h8
  have hExp0 := Real.exp_pos (-(2 * ε * t))
  have hE40 := Real.exp_pos (4 * ε * d)
  have hsrc' := mul_le_mul_of_nonneg_left hsrc (by positivity : (0 : ℝ) ≤ 180 / poincareConst d ^ 2)
  refine ⟨?_, ?_⟩
  · have hX : blkNormSq G (constrainedOp (dirichletOperator G a ν α)⁻¹ (restrictField G φ) *ᵥ f) j y
        ≤ ((L : ℝ) ^ j) ^ 2 * (Real.exp (-(2 * ε * t)) * Real.exp (4 * ε * d)) *
          (180 / poincareConst d ^ 2 * ((L : ℝ) ^ j') ^ 2 * Real.exp (4 * ε * d) *
            ∑ i, Green.sqNorm (comp G f i)) := by
      have h1 := hlow.trans (hM.trans hsrc')
      rw [← hE2inv]
      have := mul_le_mul_of_nonneg_left h1 (mul_nonneg hA0.le (inv_nonneg.2 hE10.le))
      calc _ = (((L : ℝ) ^ j) ^ 2 * (Real.exp (2 * ε * (t - 2 * d)))⁻¹) *
            ((((L : ℝ) ^ j) ^ 2)⁻¹ * Real.exp (2 * ε * (t - 2 * d)) *
              blkNormSq G (constrainedOp (dirichletOperator G a ν α)⁻¹ (restrictField G φ) *ᵥ f)
                j y) := by field_simp
        _ ≤ _ := this
        _ = _ := by ring
    calc _ ≤ _ := hX
      _ = 180 / poincareConst d ^ 2 * ((L : ℝ) ^ j) ^ 2 * ((L : ℝ) ^ j') ^ 2 *
            Real.exp (-(2 * ε * t)) * (Real.exp (4 * ε * d) * Real.exp (4 * ε * d)) *
              ∑ i, Green.sqNorm (comp G f i) := by ring
      _ ≤ 180 / poincareConst d ^ 2 * ((L : ℝ) ^ j) ^ 2 * ((L : ℝ) ^ j') ^ 2 *
            Real.exp (-(2 * ε * t)) * 2 * ∑ i, Green.sqNorm (comp G f i) := by gcongr
      _ = _ := by ring
  · have hY : blkGradSq G (constrainedOp (dirichletOperator G a ν α)⁻¹ (restrictField G φ) *ᵥ f) j y
        ≤ (Real.exp (-(2 * ε * t)) * Real.exp (4 * ε * d)) *
          (450 / poincareConst d * ((L : ℝ) ^ j') ^ 2 * Real.exp (4 * ε * d) *
            ∑ i, Green.sqNorm (comp G f i)) := by
      have hsrc'' := mul_le_mul_of_nonneg_left hsrc (by positivity : (0 : ℝ) ≤ 450 / poincareConst d)
      have h1 := hgrad.trans (hGr.trans hsrc'')
      rw [← hE2inv, ← div_eq_inv_mul, le_div_iff₀ hE10]
      linarith
    calc _ ≤ _ := hY
      _ = 450 / poincareConst d * ((L : ℝ) ^ j') ^ 2 * Real.exp (-(2 * ε * t)) *
            (Real.exp (4 * ε * d) * Real.exp (4 * ε * d)) *
              ∑ i, Green.sqNorm (comp G f i) := by ring
      _ ≤ 450 / poincareConst d * ((L : ℝ) ^ j') ^ 2 * Real.exp (-(2 * ε * t)) * 2 *
              ∑ i, Green.sqNorm (comp G f i) := by gcongr
      _ = _ := by ring

/-- **G-2(v), block-to-block decay of the constrained operator** (GREEN.md §3): for `f` supported
in the block `Δ_{j'}(y')`, `y` in layer `j`, `ϱ ≥ 1` with `L ≤ exp ((ε/2)(ϱ - 1))`, `0 ≤ ε ≤ ε₀`
and every `t ≥ 0` with `t ≤ d(y, y')`:
`ℓ_j ‖χ_{Δ_j(y)} ∂ Π f‖ + ‖χ_{Δ_j(y)} Π f‖ ≤ (50 L / c) e^{-(ε/2) t} ℓ_{j'}² ‖f‖`. -/
theorem constrained_G2v {j j' : ℕ} (hj1 : 1 ≤ j) (hjk : j ≤ k) (hj'1 : 1 ≤ j') (hj'k : j' ≤ k)
    {y y' : Torus d (N₀ * L ^ k)} (hy : y ∈ G.layer j) (hy' : y' ∈ G.layer j')
    {f : G.Ω 1 × Fin N → ℂ}
    (hsupp : ∀ (x : G.Ω 1) (i : Fin N), f (x, i) ≠ 0 →
      jBlock d L N₀ k j' x = jBlock d L N₀ k j' y')
    {t : ℝ} (ht0 : 0 ≤ t) (ht : ENNReal.ofReal t ≤ G.pathDist y y') {ε : ℝ} (hε0 : 0 ≤ ε)
    (hε1 : ε ≤ agmonRate d) (hϱ : 1 ≤ ϱ) (hsep : (L : ℝ) ≤ Real.exp (ε / 2 * (ϱ - 1))) :
    (L : ℝ) ^ j * Real.sqrt (blkGradSq G
        (constrainedOp (dirichletOperator G a ν α)⁻¹ (restrictField G φ) *ᵥ f) j y) +
      Real.sqrt (blkNormSq G
        (constrainedOp (dirichletOperator G a ν α)⁻¹ (restrictField G φ) *ᵥ f) j y) ≤
    50 * L / poincareConst d * Real.exp (-(ε / 2 * t)) * ((L : ℝ) ^ j') ^ 2 *
      Real.sqrt (∑ i, Green.sqNorm (comp G f i)) := by
  have hp0 := poincareConst_pos St.pos
  have hph := poincareConst_le_half d
  have hL : (1 : ℝ) ≤ L := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne L)
  have hL0 : (0 : ℝ) < L := by linarith
  have hyΩ : y ∈ G.Ω j := (G.mem_layer.1 hy).1
  have hsep0 := G.pathDist_separation_le hϱ hj'1 hjk hy' hyΩ
  rw [GeneratingSet.pathDist_comm] at hsep0
  set s₀ : ℝ := (ϱ - 1) * ((j - j' - 1 : ℕ) : ℝ) with hs₀
  have hs₀0 : 0 ≤ s₀ := mul_nonneg (by linarith) (Nat.cast_nonneg _)
  set t₂ := max t s₀ with ht₂
  have ht₂0 : 0 ≤ t₂ := ht0.trans (le_max_left _ _)
  have ht₂d : ENNReal.ofReal t₂ ≤ G.pathDist y y' := by
    rcases le_total t s₀ with h | h
    · rw [ht₂, max_eq_right h]; exact hsep0
    · rw [ht₂, max_eq_left h]; exact ht
  obtain ⟨hA, hB⟩ := constrained_block St hj1 hjk hj'1 hj'k hy hy' hsupp ht₂0 ht₂d hε0 hε1
  have hmis := scale_mismatch (L := L) (ε := ε) (t := t) (t₂ := t₂) hε0 j j' hsep
    (le_max_left _ _) (le_max_right _ _)
  set F := ∑ i, Green.sqNorm (comp G f i) with hF
  have hF0 : 0 ≤ F := Finset.sum_nonneg fun i _ => Green.sqNorm_nonneg _
  set P : ℝ := (L : ℝ) ^ j * (L : ℝ) ^ j' * Real.exp (-(ε * t₂)) * Real.sqrt F with hP
  have hP0 : 0 ≤ P := by positivity
  have hP2 : P ^ 2 = ((L : ℝ) ^ j) ^ 2 * ((L : ℝ) ^ j') ^ 2 * Real.exp (-(2 * ε * t₂)) * F := by
    rw [hP, mul_pow, mul_pow, mul_pow, Real.sq_sqrt hF0, ← Real.exp_nat_mul]
    congr 2
    · push_cast; ring_nf
  have hPle : P ≤ L * ((L : ℝ) ^ j') ^ 2 * Real.exp (-(ε / 2 * t)) * Real.sqrt F := by
    rw [hP]
    exact mul_le_mul_of_nonneg_right hmis (Real.sqrt_nonneg _)
  clear_value P
  set Pf := constrainedOp (dirichletOperator G a ν α)⁻¹ (restrictField G φ) *ᵥ f with hPf
  set Nn := blkNormSq G Pf j y with hNn
  set Yy := blkGradSq G Pf j y with hYy
  have hY0 : 0 ≤ Yy := blkGradSq_nonneg G _ j y
  have hN0 : 0 ≤ Nn := blkNormSq_nonneg G _ j y
  have hc1 : 1 / poincareConst d ≤ (1 / poincareConst d) ^ 2 := by
    have : 1 ≤ 1 / poincareConst d := by
      rw [le_div_iff₀ hp0]; linarith
    nlinarith
  have h1 : Real.sqrt Nn ≤ 20 / poincareConst d * P := by
    rw [Real.sqrt_le_iff]
    refine ⟨by positivity, ?_⟩
    calc Nn ≤ 360 / poincareConst d ^ 2 * P ^ 2 := by rw [hP2]; convert hA using 1; ring
      _ ≤ (20 / poincareConst d * P) ^ 2 := by
        rw [mul_pow, div_pow]
        have : 360 / poincareConst d ^ 2 ≤ 20 ^ 2 / poincareConst d ^ 2 :=
          div_le_div_of_nonneg_right (by norm_num) (by positivity)
        exact mul_le_mul_of_nonneg_right this (sq_nonneg _)
  have h2 : (L : ℝ) ^ j * Real.sqrt Yy ≤ 30 / poincareConst d * P := by
    have hsq : ((L : ℝ) ^ j * Real.sqrt Yy) ^ 2 ≤ (30 / poincareConst d * P) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hY0, mul_pow]
      have hB' : ((L : ℝ) ^ j) ^ 2 * Yy ≤ 900 / poincareConst d * P ^ 2 := by
        rw [hP2]
        calc ((L : ℝ) ^ j) ^ 2 * Yy ≤ ((L : ℝ) ^ j) ^ 2 *
              (900 / poincareConst d * ((L : ℝ) ^ j') ^ 2 * Real.exp (-(2 * ε * t₂)) * F) :=
            mul_le_mul_of_nonneg_left hB (by positivity)
          _ = _ := by ring
      have h30 : 900 / poincareConst d ≤ (30 / poincareConst d) ^ 2 := by
        rw [div_pow, div_le_div_iff₀ hp0 (by positivity)]
        nlinarith
      calc _ ≤ 900 / poincareConst d * P ^ 2 := hB'
        _ ≤ (30 / poincareConst d) ^ 2 * P ^ 2 := mul_le_mul_of_nonneg_right h30 (sq_nonneg _)
    exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).1 hsq
  calc (L : ℝ) ^ j * Real.sqrt Yy + Real.sqrt Nn ≤ 30 / poincareConst d * P + 20 / poincareConst d * P :=
        add_le_add h2 h1
    _ = 50 / poincareConst d * P := by ring
    _ ≤ 50 / poincareConst d * (L * ((L : ℝ) ^ j') ^ 2 * Real.exp (-(ε / 2 * t)) * Real.sqrt F) :=
        mul_le_mul_of_nonneg_left hPle (by positivity)
    _ = _ := by ring

end Decay

end Balaban.Multiscale
