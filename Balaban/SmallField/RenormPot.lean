/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.SmallField.RenormTail

/-!
# The potential `𝓥` (Step 3 of SMALLFIELD.md §2.3)

`Ctx.potential_bound`: `‖𝓥^{(j)}(ψ(0), b)‖ ≤ 2 E₀ K₀ (Z₀/ρ)²` where `Z₀ = (160 N + 1) σ² ε` bounds the
distance of the rotated constant configuration to the reference point.  The first-order terms
cancel by (H.5)(1)–(3).
-/

@[expose] public section

open Metric Set Matrix

namespace Balaban.SmallField

variable {d N : ℕ}

theorem wt_ge {κ : ℝ} (X : Finset (Site d)) {dj : ℝ} (hd : 0 ≤ dj) (hcard : 1 ≤ X.card) (a k : ℕ)
    (ha : a ≤ 2) (hk : k ≤ 6) :
    (X.card : ℝ) ^ a * (1 + dj) ^ k * Real.exp (-κ * dj) ≤ wt κ X dj := by
  unfold wt
  have hP : (1 : ℝ) ≤ X.card := by exact_mod_cast hcard
  have ht : (1 : ℝ) ≤ 1 + dj := by linarith
  have h1 : (X.card : ℝ) ^ a ≤ (X.card : ℝ) ^ 2 := pow_le_pow_right₀ hP ha
  have h2 : (1 + dj) ^ k ≤ (1 + dj) ^ 6 := pow_le_pow_right₀ ht hk
  have h3 : Real.exp (-κ * dj) ≤ Real.exp (-(κ - 1) * dj) := by
    apply Real.exp_le_exp.mpr; nlinarith
  have hE : 0 ≤ Real.exp (-κ * dj) := (Real.exp_pos _).le
  calc (X.card : ℝ) ^ a * (1 + dj) ^ k * Real.exp (-κ * dj)
      ≤ (X.card : ℝ) ^ 2 * (1 + dj) ^ 6 * Real.exp (-(κ - 1) * dj) := by
        gcongr
    _ = _ := rfl

variable {T : TermFamily d N} {i₀ i₁ : Fin N} {ν ρ E₀ κ A K₀ : ℝ}
  {Dom : Set ((Site d → Spin N) × Spin N)} {ψ : Site d → Spin N} {b : Spin N}
  {σ ε K₂ : ℝ} {u : ℂ} {R : Matrix (Fin N) (Fin N) ℂ}

theorem Ctx.card_pos (c : Ctx T i₀ i₁ ν ρ E₀ κ A K₀ Dom ψ b σ ε K₂ u R) {X : Finset (Site d)}
    (hX : X ∈ T.polys) : 1 ≤ X.card :=
  Finset.card_pos.mpr ⟨0, c.hyp.zero_mem X hX⟩

/-- The expansion of the term at the constant configuration around the reference point. -/
theorem Ctx.potential_term (c : Ctx T i₀ i₁ ν ρ E₀ κ A K₀ Dom ψ b σ ε K₂ u R)
    {X : Finset (Site d)} (hX : X ∈ T.polys) (hZ0 : sZ0 N σ ε ≤ ρ / 2) :
    ‖T.term X (pack X (fun _ => ψ 0) b) - T.term X (refPt i₀ ν X) -
        ((∑ x : ↥X, tensA i₀ ν X (T.term X) x) * ((R.mulVec (ψ 0) - Pi.single i₀ 1 : Spin N) i₀) +
          ((R.mulVec b - (ν : ℂ) • Pi.single i₀ 1 : Spin N) i₀) *
            fderiv ℂ (T.term X) (refPt i₀ ν X) (Pi.single (Sum.inr i₀) 1))‖ ≤
      2 * (E₀ * Real.exp (-κ * T.dist X)) * (sZ0 N σ ε / ρ) ^ 2 := by
  have hok := c.termOK hX
  have hM := c.hM hX
  have hzc : ‖zcfg X i₀ ν ψ b R‖ ≤ sZ0 N σ ε := by unfold sZ0 cC1; exact c.zc_le X
  have hball : rotCfgL R X (pack X (fun _ => ψ 0) b) ∈ ball (refPt i₀ ν X) ρ := by
    rw [rotCfgL_pack, pack_const_rot_eq, mem_ball, dist_eq_norm, add_sub_cancel_left]
    have := c.ρpos; linarith
  rw [c.term_rot hX hball, rotCfgL_pack, pack_const_rot_eq]
  have h := taylor_first c.ρpos hok.analytic_ball hM (z := zcfg X i₀ ν ψ b R) (hzc.trans hZ0)
  have hlin : fderiv ℂ (T.term X) (refPt i₀ ν X) (zcfg X i₀ ν ψ b R) =
      (∑ x : ↥X, tensA i₀ ν X (T.term X) x) * ((R.mulVec (ψ 0) - Pi.single i₀ 1 : Spin N) i₀) +
        ((R.mulVec b - (ν : ℂ) • Pi.single i₀ 1 : Spin N) i₀) *
          fderiv ℂ (T.term X) (refPt i₀ ν X) (Pi.single (Sum.inr i₀) 1) := by
    unfold zcfg
    rw [hok.lin_pack_b, Finset.sum_mul]
  rw [hlin] at h
  refine h.trans ?_
  have hM0 : 0 ≤ E₀ * Real.exp (-κ * T.dist X) := by have := c.E0nn; positivity
  have : (‖zcfg X i₀ ν ψ b R‖ / ρ) ^ 2 ≤ (sZ0 N σ ε / ρ) ^ 2 :=
    pow_le_pow_left₀ (by positivity [c.ρpos]) (div_le_div_of_nonneg_right hzc c.ρpos.le) 2
  nlinarith

end Balaban.SmallField
