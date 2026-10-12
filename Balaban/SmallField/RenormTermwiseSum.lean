/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.SmallField.RenormTermwiseIrrel

/-!
# Lemma 3.2 (i): the cancellations

Under `PremisesTerm` and the renormalization conditions `SumConds` on the sum:

* `Ttw_tsum_zero`: `Σ_{X∋y} T_X ≡ 0`, by (H.5)(1)–(3);
* `Phitw_tsum_zero`: `Σ_{X∋y} Φ_{y,X} ≡ 0`, by (H.5)(4) and the point-group isotropy (H.3);
* `Ax_tsum_eq`: `Σ_{X∋y} A_{y,X} = A_y` of the landed theorem;
* `Aterm_torus_sum_tw`: `Σ_y A_y = 0` on every torus.
-/

@[expose] public section

open Metric Set Matrix

namespace Balaban.SmallField

variable {d N : ℕ}

section Sums

variable {T : TermFamily d N} {i₀ i₁ : Fin N} {ν ρ E₀ κ A K₀ : ℝ}
  {Dom : Set ((Site d → Spin N) × Spin N)}

theorem PremisesTerm.termOK (hP : PremisesTerm T i₀ i₁ ν ρ E₀ κ A K₀ Dom) (hρ : 0 < ρ)
    {X : Finset (Site d)} (hX : X ∈ T.polys) : TermOK i₀ ν ρ X (T.term X) :=
  ⟨hρ, hP.analytic X hX, fun c' hc' R' hR' hbd hmem => hP.rot_inv X hX c' hc' R' hR' hbd hmem⟩

/-- The three tensor families at the reference point are summable over the polymers. -/
theorem PremisesTerm.summable_tensors (hP : PremisesTerm T i₀ i₁ ν ρ E₀ κ A K₀ Dom) (hρ : 0 < ρ)
    (hE0 : 0 ≤ E₀) :
    Summable (fun X : T.polys => T.term X.1 (refPt i₀ ν X.1)) ∧
    Summable (fun X : T.polys => ∑ x : ↥X.1, tensA i₀ ν X.1 (T.term X.1) x) ∧
    Summable (fun X : T.polys =>
      fderiv ℂ (T.term X.1) (refPt i₀ ν X.1) (Pi.single (Sum.inr i₀) 1)) := by
  have hMle : ∀ (X : T.polys) (a k : ℕ), a ≤ 2 → k ≤ 6 →
      (X.1.card : ℝ) ^ a * (1 + T.dist X.1) ^ k * (E₀ * Real.exp (-κ * T.dist X.1)) ≤
        E₀ * wt κ X.1 (T.dist X.1) := by
    intro X a k ha hk
    have := wt_ge (κ := κ) X.1 (hP.dist_nonneg X.1 X.2)
      (Finset.card_pos.mpr ⟨0, hP.zero_mem X.1 X.2⟩) a k ha hk
    calc _ = E₀ * ((X.1.card : ℝ) ^ a * (1 + T.dist X.1) ^ k * Real.exp (-κ * T.dist X.1)) := by
          ring
      _ ≤ _ := mul_le_mul_of_nonneg_left this hE0
  have hok := fun X : T.polys => hP.termOK hρ X.2
  have hMb : ∀ X : T.polys, ∀ y ∈ ball (refPt i₀ ν X.1) ρ,
      ‖T.term X.1 y‖ ≤ E₀ * Real.exp (-κ * T.dist X.1) := fun X y hy =>
    hP.bdd_tube X.1 X.2 y (ball_subset_tube i₀ ν ρ X.1 hy)
  have hsum : Summable fun X : T.polys => wt κ X.1 (T.dist X.1) := hP.count_summable
  refine ⟨?_, ?_, ?_⟩
  · refine Summable.of_norm_bounded (hsum.mul_left E₀) fun X => ?_
    have h1 := hMb X (refPt i₀ ν X.1) (mem_ball_self hρ)
    have := hMle X 0 0 (by norm_num) (by norm_num)
    simp only [pow_zero, one_mul] at this
    exact h1.trans this
  · refine Summable.of_norm_bounded (hsum.mul_left (E₀ / ρ)) fun X => ?_
    have h1 : ‖∑ x : ↥X.1, tensA i₀ ν X.1 (T.term X.1) x‖ ≤
        (Fintype.card ↥X.1 : ℝ) * (E₀ * Real.exp (-κ * T.dist X.1) / ρ) :=
      norm_sum_le_card _ fun x => (hok X).norm_tensA_le (hMb X) x
    have := hMle X 1 0 (by norm_num) (by norm_num)
    simp only [pow_one, pow_zero, mul_one] at this
    rw [Fintype.card_coe] at h1
    refine h1.trans ?_
    calc (X.1.card : ℝ) * (E₀ * Real.exp (-κ * T.dist X.1) / ρ)
        = ((X.1.card : ℝ) * (E₀ * Real.exp (-κ * T.dist X.1))) / ρ := by ring
      _ ≤ (E₀ * wt κ X.1 (T.dist X.1)) / ρ := div_le_div_of_nonneg_right this hρ.le
      _ = _ := by ring
  · refine Summable.of_norm_bounded (hsum.mul_left (E₀ / ρ)) fun X => ?_
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

/-- **(i), first part**: `Σ_{X∋y} T_X ≡ 0`, for all data. -/
theorem Ttw_tsum_zero (hP : PremisesTerm T i₀ i₁ ν ρ E₀ κ A K₀ Dom) (hS : SumConds T i₀ i₁ ν)
    (hρ : 0 < ρ) (hE0 : 0 ≤ E₀) (ψ : Site d → Spin N) (b : Spin N) :
    ∑' X : T.polys, Ttw T i₀ ν X.1 ψ b = 0 := by
  obtain ⟨S_v0, S_s, S_d⟩ := hP.summable_tensors hρ hE0
  unfold Ttw
  rw [Summable.tsum_add (S_v0.add (S_s.mul_left (uInv ψ - 1))) (S_d.mul_left (vInv ψ b - ν)),
    Summable.tsum_add S_v0 (S_s.mul_left (uInv ψ - 1)), tsum_mul_left, tsum_mul_left,
    hS.ren_val, hS.ren_psi, hS.ren_b]
  ring

/-- **(i), second part**: `Σ_{X∋y} Φ_{y,X} ≡ 0`, for all data. -/
theorem Phitw_tsum_zero (hP : PremisesTerm T i₀ i₁ ν ρ E₀ κ A K₀ Dom) (hS : SumConds T i₀ i₁ ν)
    (hρ : 0 < ρ) (hE0 : 0 ≤ E₀) (hA : 0 ≤ A) (ψ : Site d → Spin N) :
    ∑' X : T.polys, Phitw T i₀ i₁ ν X.1 ψ = 0 := by
  have hP' := hP.toPremises hS
  unfold Phitw
  rw [tsum_mul_left]
  have : ∑' X : T.polys, ∑ μ, ∑ μ', gradInv ψ μ μ' * Sx T i₀ i₁ ν X.1 μ μ' = 0 := by
    rw [Summable.tsum_finsetSum (fun μ _ => summable_sum fun μ' _ =>
      (Sx_summable hP' hρ hE0 hA μ μ').mul_left _)]
    refine Finset.sum_eq_zero fun μ _ => ?_
    rw [Summable.tsum_finsetSum (fun μ' _ => (Sx_summable hP' hρ hE0 hA μ μ').mul_left _)]
    refine Finset.sum_eq_zero fun μ' _ => ?_
    rw [tsum_mul_left, moment_tensor hP' hρ hE0 hA μ μ', mul_zero]
  rw [this, mul_zero]

/-- **(i), third part**: `Σ_{X∋y} A_{y,X} = A_y` of the landed theorem. -/
theorem Ax_tsum_eq (i₀ : Fin N) (ν : ℝ) (T : TermFamily d N) (ψ : Site d → Spin N) :
    ∑' X : T.polys, Ax T i₀ ν ψ X.1 = Aterm T i₀ ν ψ :=
  (Aterm_eq T i₀ ν ψ).symm

/-- **(i), fourth part**: on every torus the terms `A_y` sum to zero. -/
theorem Aterm_torus_sum_tw (hP : PremisesTerm T i₀ i₁ ν ρ E₀ κ A K₀ Dom)
    (hS : SumConds T i₀ i₁ ν) (hρ : 0 < ρ) (hE0 : 0 ≤ E₀) (ℓ : ℕ) [NeZero ℓ]
    (ψT : Torus d ℓ → Spin N) :
    ∑ y : Torus d ℓ, (1 / 2 : ℂ) * ∑' z : Site d, aCoef T i₀ ν z *
      (dot (ψT (y + liftSite ℓ z)) (ψT (y + liftSite ℓ z)) - dot (ψT y) (ψT y)) = 0 :=
  Aterm_torus_sum (hP.toPremises hS) hρ hE0 ℓ ψT

end Sums

end Balaban.SmallField
