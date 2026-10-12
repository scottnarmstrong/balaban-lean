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

theorem Ctx.potential_bound (c : Ctx T i₀ i₁ ν ρ E₀ κ A K₀ Dom ψ b σ ε K₂ u R)
    (hZ0 : sZ0 N σ ε ≤ ρ / 2) :
    ‖potential T (ψ 0) b‖ ≤ 2 * E₀ * K₀ * (sZ0 N σ ε / ρ) ^ 2 := by
  classical
  set α : ℂ := ((R.mulVec (ψ 0) - Pi.single i₀ 1 : Spin N) i₀) with hα
  set β : ℂ := ((R.mulVec b - (ν : ℂ) • Pi.single i₀ 1 : Spin N) i₀) with hβ
  set v0 : T.polys → ℂ := fun X => T.term X.1 (refPt i₀ ν X.1) with hv0
  set s : T.polys → ℂ := fun X => ∑ x : ↥X.1, tensA i₀ ν X.1 (T.term X.1) x with hs
  set dd : T.polys → ℂ := fun X =>
    fderiv ℂ (T.term X.1) (refPt i₀ ν X.1) (Pi.single (Sum.inr i₀) 1) with hdd
  set g : T.polys → ℂ := fun X => T.term X.1 (pack X.1 (fun _ => ψ 0) b) with hg
  set r : T.polys → ℂ := fun X => g X - (v0 X + α * s X + β * dd X) with hr
  have hρ := c.ρpos
  have hE0 := c.E0nn
  have hwt : ∀ X : T.polys, 0 ≤ wt κ X.1 (T.dist X.1) := fun X => by
    unfold wt; have := c.hyp.dist_nonneg X.1 X.2; positivity
  -- bounds
  have hMle : ∀ (X : T.polys) (a k : ℕ), a ≤ 2 → k ≤ 6 →
      (X.1.card : ℝ) ^ a * (1 + T.dist X.1) ^ k * (E₀ * Real.exp (-κ * T.dist X.1)) ≤
        E₀ * wt κ X.1 (T.dist X.1) := by
    intro X a k ha hk
    have := wt_ge (κ := κ) X.1 (c.hyp.dist_nonneg X.1 X.2) (c.card_pos X.2) a k ha hk
    calc _ = E₀ * ((X.1.card : ℝ) ^ a * (1 + T.dist X.1) ^ k * Real.exp (-κ * T.dist X.1)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left this hE0
  have hok := fun X : T.polys => c.termOK X.2
  have hMb := fun X : T.polys => c.hM X.2
  have b_v0 : ∀ X : T.polys, ‖v0 X‖ ≤ E₀ * wt κ X.1 (T.dist X.1) := by
    intro X
    have h1 := hMb X (refPt i₀ ν X.1) (mem_ball_self hρ)
    have := hMle X 0 0 (by norm_num) (by norm_num)
    simp only [pow_zero, one_mul] at this
    exact h1.trans this
  have b_s : ∀ X : T.polys, ‖s X‖ ≤ E₀ / ρ * wt κ X.1 (T.dist X.1) := by
    intro X
    have h1 : ‖s X‖ ≤ (Fintype.card ↥X.1 : ℝ) * (E₀ * Real.exp (-κ * T.dist X.1) / ρ) :=
      norm_sum_le_card _ fun x => (hok X).norm_tensA_le (hMb X) x
    have := hMle X 1 0 (by norm_num) (by norm_num)
    simp only [pow_one, pow_zero, mul_one] at this
    rw [Fintype.card_coe] at h1
    refine h1.trans ?_
    calc (X.1.card : ℝ) * (E₀ * Real.exp (-κ * T.dist X.1) / ρ)
        = ((X.1.card : ℝ) * (E₀ * Real.exp (-κ * T.dist X.1))) / ρ := by ring
      _ ≤ (E₀ * wt κ X.1 (T.dist X.1)) / ρ := div_le_div_of_nonneg_right this hρ.le
      _ = _ := by ring
  have b_d : ∀ X : T.polys, ‖dd X‖ ≤ E₀ / ρ * wt κ X.1 (T.dist X.1) := by
    intro X
    have h1 := norm_fderiv_apply_le hρ (hok X).analytic_ball (hMb X)
      (Pi.single (Sum.inr i₀) (1 : ℂ) : Cfg d N X.1)
    have h2 := norm_single_one_le (Sum.inr i₀ : Idx d N X.1)
    have hM0 : 0 ≤ E₀ * Real.exp (-κ * T.dist X.1) := by positivity
    have := hMle X 0 0 (by norm_num) (by norm_num)
    simp only [pow_zero, one_mul] at this
    refine h1.trans ?_
    calc E₀ * Real.exp (-κ * T.dist X.1) * ‖(Pi.single (Sum.inr i₀) (1 : ℂ) : Cfg d N X.1)‖ / ρ
        ≤ (E₀ * Real.exp (-κ * T.dist X.1)) * 1 / ρ :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left h2 hM0) hρ.le
      _ ≤ (E₀ * wt κ X.1 (T.dist X.1)) / ρ := by
          rw [mul_one]; exact div_le_div_of_nonneg_right this hρ.le
      _ = _ := by ring
  have b_r : ∀ X : T.polys, ‖r X‖ ≤ 2 * E₀ * (sZ0 N σ ε / ρ) ^ 2 * wt κ X.1 (T.dist X.1) := by
    intro X
    have h1 := c.potential_term X.2 hZ0
    have e : r X = T.term X.1 (pack X.1 (fun _ => ψ 0) b) - T.term X.1 (refPt i₀ ν X.1) -
        ((∑ x : ↥X.1, tensA i₀ ν X.1 (T.term X.1) x) * α +
          β * fderiv ℂ (T.term X.1) (refPt i₀ ν X.1) (Pi.single (Sum.inr i₀) 1)) := by
      simp only [hr, hg, hv0, hs, hdd]; ring
    rw [e]
    have := hMle X 0 0 (by norm_num) (by norm_num)
    simp only [pow_zero, one_mul] at this
    have hsq : 0 ≤ (sZ0 N σ ε / ρ) ^ 2 := by positivity
    refine h1.trans ?_
    calc 2 * (E₀ * Real.exp (-κ * T.dist X.1)) * (sZ0 N σ ε / ρ) ^ 2
        ≤ 2 * (E₀ * wt κ X.1 (T.dist X.1)) * (sZ0 N σ ε / ρ) ^ 2 := by
          gcongr
      _ = _ := by ring
  have b_g : ∀ X : T.polys, ‖g X‖ ≤ E₀ * wt κ X.1 (T.dist X.1) := by
    intro X
    have h1 := c.hyp.bdd_dom X.1 X.2 ((fun _ => ψ 0), b) c.dat.mem_const
    have := hMle X 0 0 (by norm_num) (by norm_num)
    simp only [pow_zero, one_mul] at this
    exact h1.trans this
  have hsum : Summable fun X : T.polys => wt κ X.1 (T.dist X.1) := c.hyp.count_summable
  have S_v0 : Summable v0 := Summable.of_norm_bounded (hsum.mul_left E₀) b_v0
  have S_s : Summable s := Summable.of_norm_bounded (hsum.mul_left (E₀ / ρ)) b_s
  have S_d : Summable dd := Summable.of_norm_bounded (hsum.mul_left (E₀ / ρ)) b_d
  have S_r : Summable r :=
    Summable.of_norm_bounded (hsum.mul_left (2 * E₀ * (sZ0 N σ ε / ρ) ^ 2)) b_r
  have hdec : g = fun X => r X + (v0 X + α * s X + β * dd X) := by
    ext X; simp [hr]
  have h0 : ∑' X, (v0 X + α * s X + β * dd X) = 0 := by
    rw [Summable.tsum_add ((S_v0.add (S_s.mul_left α))) (S_d.mul_left β),
      Summable.tsum_add S_v0 (S_s.mul_left α), tsum_mul_left, tsum_mul_left]
    have e1 : ∑' X, v0 X = 0 := c.hyp.ren_val
    have e2 : ∑' X, s X = 0 := c.hyp.ren_psi
    have e3 : ∑' X, dd X = 0 := c.hyp.ren_b
    rw [e1, e2, e3]; ring
  have hpot : potential T (ψ 0) b = ∑' X, r X := by
    unfold potential
    show ∑' X, g X = _
    rw [hdec, Summable.tsum_add S_r ((S_v0.add (S_s.mul_left α)).add (S_d.mul_left β)), h0, add_zero]
  rw [hpot]
  have hb := tsum_of_norm_bounded (hsum.mul_left (2 * E₀ * (sZ0 N σ ε / ρ) ^ 2)).hasSum b_r
  refine hb.trans ?_
  rw [tsum_mul_left]
  have := c.hyp.count_le
  have hC : 0 ≤ 2 * E₀ * (sZ0 N σ ε / ρ) ^ 2 := by positivity
  nlinarith

end Balaban.SmallField
