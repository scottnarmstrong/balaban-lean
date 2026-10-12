/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.StepActivityWitnessMin
public import Balaban.Fluctuation.StepActivityWitnessNe
public import Balaban.Fluctuation.StepActivityWitnessRay
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The background moves along the ray, for a positive mass

`StepActivityWitnessMin` / `StepActivityWitnessNe` show, for mass `ν = 0`, that if the data
`Ψ` have a nonzero perpendicular mean then `e₀ = (1, 0)` is not the minimizer.  With a mass
`ν ≥ 0` and `h ≡ e₀` the same comparison with the rotated constants gives
`Q sin θ ≤ (P + ν |Ω₁| / w)(1 - cos θ)`, hence again `Q = 0` (`sum_perp_eq_zero_nu`), and
`RayData.bgField_ne_nu` follows.  This is the non-degeneracy of the potential `V_k` along the ray
at the hat witness (`ν = 1/81`).
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization Balaban.Inhabited Finset

section Const

variable {d L N₀ K : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ} {G : GeneratingSet d L N₀ K ϱ}

/-- **If `e₀` is a minimizer for real data with `h ≡ e₀` and any mass `ν`, the perpendicular
component of the data sums to zero.** -/
theorem sum_perp_eq_zero_nu {n : ℕ} (hG : IsLevel G n) (a : ℕ → ℝ) {ν : ℝ}
    (D : BgData G 2) (hreal : ∀ x i, (D.Ψ x i).im = 0)
    (hh : ∀ x ∈ G.Ω 1, ∀ i, D.h x i = (unitVec hN2 i : ℂ))
    (hw : 0 < a n / ((L : ℝ) ^ n) ^ 2)
    (hmin : ∀ σ, IsRealUnitField G σ →
      action G a ν D (constPhi G (N := 2) ![1, 0]) ≤ action G a ν D σ) :
    ∑ x : G.Ω 1, (D.Ψ x 1).re = 0 := by
  set P : ℝ := ∑ x : G.Ω 1, (D.Ψ x 0).re with hP
  set Q : ℝ := ∑ x : G.Ω 1, (D.Ψ x 1).re with hQ
  set w : ℝ := a n / ((L : ℝ) ^ n) ^ 2 with hwdef
  set M : ℝ := ν * (Fintype.card (G.Ω 1) : ℝ) / w with hM
  refine perp_zero_of_forall (P + M) Q fun θ => ?_
  have h := hmin _ (isRealUnitField_rot (G := G) θ)
  have hsplit : ∀ σ, action G a ν D σ = action G a 0 D σ +
      ν / 2 * ∑ x : G.Ω 1, ∑ i, ‖σ (x, i) - D.h x i‖ ^ 2 := by
    intro σ; unfold action; ring
  rw [hsplit, hsplit, action_constPhi hG, action_constPhi hG] at h
  have hm0 : ∑ x : G.Ω 1, ∑ i, ‖constPhi G (N := 2) ![1, 0] (x, i) - D.h x i‖ ^ 2 = 0 := by
    apply Finset.sum_eq_zero; intro x _
    apply Finset.sum_eq_zero; intro i _
    rw [hh x x.2 i]
    fin_cases i <;> simp [constPhi, unitVec]
  have hm1 : ∑ x : G.Ω 1, ∑ i, ‖constPhi G (N := 2) ![Real.cos θ, Real.sin θ] (x, i) - D.h x i‖ ^ 2
      = (Fintype.card (G.Ω 1) : ℝ) * (2 - 2 * Real.cos θ) := by
    have : ∀ x : G.Ω 1, ∑ i, ‖constPhi G (N := 2) ![Real.cos θ, Real.sin θ] (x, i) - D.h x i‖ ^ 2
        = 2 - 2 * Real.cos θ := by
      intro x
      simp only [Fin.sum_univ_two, hh x x.2, constPhi, unitVec]
      simp only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one]
      simp only [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, sq_abs]
      simp
      nlinarith [Real.sin_sq_add_cos_sq θ]
    rw [Finset.sum_congr rfl fun x _ => this x]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [hm0, hm1] at h
  simp only [Fin.sum_univ_two] at h
  have hx : ∀ (r0 r1 : ℝ) (x : G.Ω 1),
      ‖D.Ψ x 0 - (( ![r0, r1] 0 : ℝ) : ℂ)‖ ^ 2 + ‖D.Ψ x 1 - (( ![r0, r1] 1 : ℝ) : ℂ)‖ ^ 2 =
        ((D.Ψ x 0).re - r0) ^ 2 + ((D.Ψ x 1).re - r1) ^ 2 := by
    intro r0 r1 x
    rw [norm_sub_real_sq (hreal x 0), norm_sub_real_sq (hreal x 1)]
    simp
  simp only [hx] at h
  rw [← Finset.mul_sum, ← Finset.mul_sum] at h
  have hdiff : ∑ x : G.Ω 1, (((D.Ψ x 0).re - Real.cos θ) ^ 2 + ((D.Ψ x 1).re - Real.sin θ) ^ 2) -
      ∑ x : G.Ω 1, (((D.Ψ x 0).re - 1) ^ 2 + ((D.Ψ x 1).re - 0) ^ 2) =
      2 * (P * (1 - Real.cos θ) - Q * Real.sin θ) := by
    rw [← Finset.sum_sub_distrib]
    have : ∀ x : G.Ω 1, ((D.Ψ x 0).re - Real.cos θ) ^ 2 + ((D.Ψ x 1).re - Real.sin θ) ^ 2 -
        (((D.Ψ x 0).re - 1) ^ 2 + ((D.Ψ x 1).re - 0) ^ 2) =
        2 * ((D.Ψ x 0).re * (1 - Real.cos θ)) - 2 * ((D.Ψ x 1).re * Real.sin θ) := by
      intro x
      linear_combination Real.sin_sq_add_cos_sq θ
    rw [Finset.sum_congr rfl fun x _ => this x, Finset.sum_sub_distrib, ← Finset.mul_sum,
      ← Finset.mul_sum, ← Finset.sum_mul, ← Finset.sum_mul]
    ring
  have hc : 0 ≤ 1 - Real.cos θ := by linarith [Real.cos_le_one θ]
  have hMw : M * w = ν * (Fintype.card (G.Ω 1) : ℝ) := by
    rw [hM]; field_simp
  -- `h : (1/2) w S₀ + 0 ≤ (1/2) w S_θ + ν/2 card (2 - 2 cos θ)`
  have key : 0 ≤ w * (P * (1 - Real.cos θ) - Q * Real.sin θ) +
      ν * (Fintype.card (G.Ω 1) : ℝ) * (1 - Real.cos θ) := by
    nlinarith [hdiff, h]
  have key2 : 0 ≤ w * (P * (1 - Real.cos θ) - Q * Real.sin θ + M * (1 - Real.cos θ)) := by
    nlinarith [key, hMw]
  have := (mul_nonneg_iff_of_pos_left hw).1 key2
  nlinarith [this]

end Const

namespace StepSetting

variable {d L N₁ m₁ k : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ} {S : StepSetting d L N₁ m₁ k 2 ϱ}
  {pp : ℝ}

/-- **The background field moves along the ray** (any mass `ν`, `h₀ = e₀`): a shift of the
perpendicular component of the datum changes `φ_k`. -/
theorem RayData.bgField_ne_nu (R : S.RayData pp)
    (hh₀ : S.h₀ = unitVec hN2)
    (hbg0 : bgField S.G' S.a S.ν S.D' = unitPhi S.G' hN2) {ψ : S.E}
    (hdom : InUnionDomainR (stepG d L N₁ m₁ k ϱ) (bgC1 d L 2) S.ν (S.dataU ψ)) {η : ℝ}
    (hη : η ≠ 0) (hψ : ∀ x, liftU S.hG' ψ x 1 = liftU S.hG' S.psi0 x 1 + η) :
    bgField (stepG d L N₁ m₁ k ϱ) S.a S.ν (S.dataU ψ) ≠
      bgField (stepG d L N₁ m₁ k ϱ) S.a S.ν (S.dataU S.psi0) := by
  intro heq
  have hdom0 : InUnionDomainR (stepG d L N₁ m₁ k ϱ) (bgC1 d L 2) S.ν (S.dataU S.psi0) := by
    have := R.dom (q := (0, 0)) (by simp [R.hpp])
    simpa [psiAt_zero] using this
  have hreal : ∀ ψ' : S.E, ∀ x i, ((S.dataU ψ').Ψ x i).im = 0 := by
    intro ψ' x i; rw [S.dataU_Ψ]; simp
  have hmin : ∀ ψ' : S.E, InUnionDomainR (stepG d L N₁ m₁ k ϱ) (bgC1 d L 2) S.ν (S.dataU ψ') →
      IsMinimizer (stepG d L N₁ m₁ k ϱ) S.a S.ν (S.dataU ψ')
        (bgField (stepG d L N₁ m₁ k ϱ) S.a S.ν (S.dataU ψ')) := by
    intro ψ' hd
    obtain ⟨φ, hφ, hu⟩ := (theorem71 R.H hd).1
    rw [bgField_eq hφ hu]; exact hφ
  have hc0 := R.bgField_psi0 hbg0
  have key : ∀ ψ' : S.E, InUnionDomainR (stepG d L N₁ m₁ k ϱ) (bgC1 d L 2) S.ν (S.dataU ψ') →
      bgField (stepG d L N₁ m₁ k ϱ) S.a S.ν (S.dataU ψ') =
        constPhi (stepG d L N₁ m₁ k ϱ) (N := 2) ![1, 0] →
      ∑ x : (stepG d L N₁ m₁ k ϱ).Ω 1, (liftU S.hG' ψ' x 1) = 0 := by
    intro ψ' hd hb
    have := sum_perp_eq_zero_nu S.hG S.a (S.dataU ψ') (hreal ψ') (by
      intro x hx i
      rw [S.dataU_h, hh₀]) R.weight_pos (by
      intro σ hσ
      have h1 := (hmin ψ' hd).2.2 σ hσ
      rw [hb] at h1
      exact h1)
    simpa [S.dataU_Ψ] using this
  have h1 := key S.psi0 hdom0 hc0
  have h2 := key ψ hdom (heq.trans hc0)
  have hsum : ∑ x : (stepG d L N₁ m₁ k ϱ).Ω 1, liftU S.hG' ψ x 1 =
      ∑ x : (stepG d L N₁ m₁ k ϱ).Ω 1, liftU S.hG' S.psi0 x 1 +
        η * (Fintype.card ((stepG d L N₁ m₁ k ϱ).Ω 1) : ℝ) := by
    rw [Finset.sum_congr rfl fun x _ => hψ x.1, Finset.sum_add_distrib]
    simp [mul_comm]
  have hcard : (0 : ℝ) < (Fintype.card ((stepG d L N₁ m₁ k ϱ).Ω 1) : ℝ) := by
    have : Nonempty ((stepG d L N₁ m₁ k ϱ).Ω 1) := ⟨⟨0, (S.hG 0).1⟩⟩
    exact_mod_cast Fintype.card_pos
  rw [h1, h2] at hsum
  have : η * (Fintype.card ((stepG d L N₁ m₁ k ϱ).Ω 1) : ℝ) = 0 := by linarith
  rcases mul_eq_zero.1 this with h | h
  · exact hη h
  · exact hcard.ne' h

/-- **A point of the ball `‖x₀‖ < p₁` where the background moves along the ray**: some component
of `ℳ_k` differs between `s = 1` and `s = 0`. -/
theorem RayData.exists_move (R : S.RayData pp) (hh₀ : S.h₀ = unitVec hN2)
    (hbg0 : bgField S.G' S.a S.ν S.D' = unitPhi S.G' hN2) (hp : 0 < S.p₁) (hlt : S.p₁ < pp) :
    ∃ x₀ : S.E, ‖x₀‖ < S.p₁ ∧ ∃ (y : CTorus d L N₁ m₁ (k + 1)) (i : Fin 2),
      S.bgComp y i (1, x₀) ≠ S.bgComp y i (0, x₀) := by
  classical
  set u : S.E := S.unshiftU S.cvec with hu
  set τ : ℝ := S.p₁ / (2 * (‖u‖ + 1)) with hτ
  have hτ0 : 0 < τ := by positivity
  set x₀ : S.E := τ • u with hx₀
  have hx₀n : ‖x₀‖ < S.p₁ := by
    rw [hx₀, norm_smul, Real.norm_eq_abs, abs_of_pos hτ0, hτ]
    have : S.p₁ / (2 * (‖u‖ + 1)) * ‖u‖ < S.p₁ := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
      nlinarith [norm_nonneg u]
    exact this
  have hsh : S.shiftU x₀ = τ • S.cvec := by
    rw [hx₀, shiftU_smul, hu, R.shiftU_unshiftU]
  have hdom := R.dom (q := ((1 : ℝ), x₀)) (by
    simp only [abs_one, one_mul]
    exact hx₀n.trans hlt)
  have hψ : ∀ x, liftU S.hG' (S.psiAt 1 x₀) x 1 = liftU S.hG' S.psi0 x 1 + τ := by
    intro x
    have : S.psiAt 1 x₀ = S.psi0 + τ • S.cvec := by
      unfold psiAt; rw [one_smul, hsh]
    rw [this, liftU_add, liftU_smul]
    have h1 : liftU S.hG' S.cvec x 1 = 1 := by
      show (S.cvec (unitPt S.hG' x)) 1 = 1
      simp [cvec]
    rw [h1, mul_one]
  have hne := R.bgField_ne_nu hh₀ hbg0 hdom hτ0.ne' hψ
  refine ⟨x₀, hx₀n, ?_⟩
  by_contra hcon
  push Not at hcon
  apply hne
  funext pq
  obtain ⟨⟨z, hz⟩, i⟩ := pq
  have h := hcon z i
  unfold bgComp at h
  rw [svec_of_mem _ _ ⟨z, hz⟩ i, svec_of_mem _ _ ⟨z, hz⟩ i] at h
  simpa [psiAt_zero] using h

end StepSetting

end Balaban.Fluctuation
