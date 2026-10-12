/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.SmallField.RenormData

/-!
# Estimates of the rotated data

* `norm_dotT_le`: `‖dotT u v‖ ≤ N ‖u‖ ‖v‖`;
* `Frame.dotT_diff_bound`: the transverse second-order expansion of `φ(x) - φ(x')` in the
  frozen gradients (Step 5), with the second differences bounded by `K₂`.
-/

@[expose] public section

open Matrix

namespace Balaban.SmallField

variable {d N : ℕ} {i₀ : Fin N}

theorem norm_dotT_le (i₀ : Fin N) (u v : Spin N) : ‖dotT i₀ u v‖ ≤ N * (‖u‖ * ‖v‖) := by
  unfold dotT
  calc ‖∑ i ∈ Finset.univ.erase i₀, u i * v i‖ ≤ ∑ i ∈ Finset.univ.erase i₀, ‖u i * v i‖ :=
        norm_sum_le _ _
    _ ≤ ∑ _i ∈ Finset.univ.erase i₀, ‖u‖ * ‖v‖ := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [norm_mul]
        exact mul_le_mul (norm_le_pi_norm u i) (norm_le_pi_norm v i) (norm_nonneg _)
          (norm_nonneg _)
    _ = ((Finset.univ.erase i₀).card : ℝ) * (‖u‖ * ‖v‖) := by simp
    _ ≤ N * (‖u‖ * ‖v‖) := by
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        exact_mod_cast (Finset.card_erase_le).trans (by simp)

theorem dotT_add_left (i₀ : Fin N) (u v w : Spin N) :
    dotT i₀ (u + v) w = dotT i₀ u w + dotT i₀ v w := by
  simp [dotT, add_mul, Finset.sum_add_distrib]

theorem dotT_add_right (i₀ : Fin N) (u v w : Spin N) :
    dotT i₀ u (v + w) = dotT i₀ u v + dotT i₀ u w := by
  simp [dotT, mul_add, Finset.sum_add_distrib]

theorem dotT_smul_left (i₀ : Fin N) (t : ℂ) (v w : Spin N) :
    dotT i₀ (t • v) w = t * dotT i₀ v w := by
  simp only [dotT, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem dotT_smul_right (i₀ : Fin N) (t : ℂ) (v w : Spin N) :
    dotT i₀ v (t • w) = t * dotT i₀ v w := by
  rw [dotT_comm i₀ v, dotT_smul_left, dotT_comm i₀ v]

theorem dotT_sum_left (i₀ : Fin N) {ι : Type*} (s : Finset ι) (v : ι → Spin N) (w : Spin N) :
    dotT i₀ (∑ i ∈ s, v i) w = ∑ i ∈ s, dotT i₀ (v i) w := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [dotT]
  | insert a s ha ih => rw [Finset.sum_insert ha, dotT_add_left, ih, Finset.sum_insert ha]

theorem dotT_sum_right (i₀ : Fin N) {ι : Type*} (s : Finset ι) (v : Spin N) (w : ι → Spin N) :
    dotT i₀ v (∑ i ∈ s, w i) = ∑ i ∈ s, dotT i₀ v (w i) := by
  rw [dotT_comm i₀ v, dotT_sum_left]
  exact Finset.sum_congr rfl fun i _ => dotT_comm i₀ _ _

theorem l1_sub_le (x x' : Site d) : l1 (x - x') ≤ l1 x + l1 x' := by
  unfold l1
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun μ _ => ?_
  simp only [Pi.sub_apply]
  omega

theorem norm_sum_smul_le (z : Site d) (v : Fin d → Spin N) {C : ℝ} (hC : ∀ μ, ‖v μ‖ ≤ C) :
    ‖∑ μ, ((z μ : ℤ) : ℂ) • v μ‖ ≤ (l1 z : ℝ) * C := by
  have hC0 : 0 ≤ C ∨ d = 0 := by
    by_cases hd : d = 0
    · exact Or.inr hd
    · exact Or.inl (le_trans (norm_nonneg _) (hC ⟨0, Nat.pos_of_ne_zero hd⟩))
  calc ‖∑ μ, ((z μ : ℤ) : ℂ) • v μ‖ ≤ ∑ μ, ‖((z μ : ℤ) : ℂ) • v μ‖ := norm_sum_le _ _
    _ ≤ ∑ μ, ((z μ).natAbs : ℝ) * C := by
        refine Finset.sum_le_sum fun μ _ => ?_
        rw [norm_smul]
        have : ‖((z μ : ℤ) : ℂ)‖ = ((z μ).natAbs : ℝ) := by
          rw [Complex.norm_intCast]; simp
        rw [this]
        exact mul_le_mul_of_nonneg_left (hC μ) (Nat.cast_nonneg _)
    _ = (l1 z : ℝ) * C := by
        unfold l1; push_cast; rw [Finset.sum_mul]

/-- The rotated differences. -/
def rotDiff (R : Matrix (Fin N) (Fin N) ℂ) (ψ : Site d → Spin N) (y : Site d) : Spin N :=
  R.mulVec (ψ y - ψ 0)

/-- The tensor of the frozen gradients `G_{μμ'} = ∂_μ ψ̃_⊥(0) · ∂_{μ'} ψ̃_⊥(0)`. -/
def gradTensor (i₀ : Fin N) (R : Matrix (Fin N) (Fin N) ℂ) (ψ : Site d → Spin N) :
    Fin d → Fin d → ℂ := fun μ μ' => dotT i₀ (rotDiff R ψ (eU μ)) (rotDiff R ψ (eU μ'))

theorem dotT_diff_bound {R : Matrix (Fin N) (Fin N) ℂ} (hR : ∀ i k, ‖R i k‖ ≤ 40)
    {ψ : Site d → Spin N} {σ ε K₂ : ℝ}
    (hadj : ∀ x μ, ‖ψ (x + Pi.single μ 1) - ψ x‖ ≤ σ * ε)
    (hsec : ∀ x μ μ', ‖ψ (x + Pi.single μ 1 + Pi.single μ' 1) - ψ (x + Pi.single μ 1)
      - ψ (x + Pi.single μ' 1) + ψ x‖ ≤ K₂)
    (x x' : Site d) {L : ℝ} (hx : (l1 x : ℝ) ≤ L) (hx' : (l1 x' : ℝ) ≤ L) (hL : 0 ≤ L)
    (i₀ : Fin N) (hε : 0 ≤ σ * ε) (hK0 : 0 ≤ K₂) :
    ‖dotT i₀ (rotDiff R ψ x - rotDiff R ψ x') (rotDiff R ψ x - rotDiff R ψ x') -
        wquad (gradTensor i₀ R ψ) x x'‖ ≤
      2 * N * (2 * L * (N * 40 * (σ * ε))) * (N * 40 * (6 * L ^ 2 * K₂)) +
        N * (N * 40 * (6 * L ^ 2 * K₂)) ^ 2 := by
  classical
  set w : Site d := x - x' with hw
  have hlw : (l1 w : ℝ) ≤ 2 * L := by
    have := l1_sub_le x x'
    have : (l1 w : ℝ) ≤ l1 x + l1 x' := by exact_mod_cast this
    linarith
  have h2 : ∀ y μ ν, ‖fdiff ψ ν (y + eU μ) - fdiff ψ ν y‖ ≤ K₂ := by
    intro y μ ν
    have := hsec y μ ν
    have e : fdiff ψ ν (y + eU μ) - fdiff ψ ν y = ψ (y + Pi.single μ 1 + Pi.single ν 1) -
        ψ (y + Pi.single μ 1) - ψ (y + Pi.single ν 1) + ψ y := by
      simp only [fdiff, eU, add_assoc]; abel_nf
    rw [e]; exact this
  -- Taylor expansion at `x'`
  have hT := norm_taylor_le h2 x' w
  have hxw : x' + w = x := by rw [hw]; abel
  rw [hxw] at hT
  -- frozen gradient
  have hgr : ∀ μ, ‖fdiff ψ μ x' - fdiff ψ μ 0‖ ≤ (l1 x' : ℝ) * K₂ := by
    intro μ
    have := norm_sub_le_l1 (ψ := fdiff ψ μ) (δ := K₂) (fun y ν => h2 y ν μ) 0 x'
    simpa using this
  set r1 : Spin N := ψ x - ψ x' - ∑ μ, ((w μ : ℤ) : ℂ) • fdiff ψ μ x' with hr1
  set r2 : Spin N := ∑ μ, ((w μ : ℤ) : ℂ) • (fdiff ψ μ x' - fdiff ψ μ 0) with hr2
  have hr2b : ‖r2‖ ≤ (l1 w : ℝ) * ((l1 x' : ℝ) * K₂) :=
    norm_sum_smul_le w (fun μ => fdiff ψ μ x' - fdiff ψ μ 0) hgr
  set r : Spin N := r1 + r2 with hr
  have hrb : ‖r‖ ≤ ((l1 w : ℝ) ^ 2 + (l1 w : ℝ) * (l1 x' : ℝ)) * K₂ := by
    refine (norm_add_le _ _).trans ?_
    have := hT
    nlinarith
  have hdecomp : ψ x - ψ x' = (∑ μ, ((w μ : ℤ) : ℂ) • fdiff ψ μ 0) + r := by
    simp only [hr, hr1, hr2, smul_sub, Finset.sum_sub_distrib]; abel
  set a : Spin N := ∑ μ, ((w μ : ℤ) : ℂ) • rotDiff R ψ (eU μ) with ha
  set b : Spin N := R.mulVec r with hb
  have hΔ : rotDiff R ψ x - rotDiff R ψ x' = a + b := by
    have e1 : rotDiff R ψ x - rotDiff R ψ x' = R.mulVec (ψ x - ψ x') := by
      simp only [rotDiff, ← Matrix.mulVec_sub]; congr 1; abel
    rw [e1, hdecomp, Matrix.mulVec_add]
    congr 1
    have e2 : R.mulVec (∑ μ, ((w μ : ℤ) : ℂ) • fdiff ψ μ 0) = a := by
      have := map_sum (Matrix.mulVecLin R) (fun μ => ((w μ : ℤ) : ℂ) • fdiff ψ μ 0) Finset.univ
      simp only [Matrix.mulVecLin_apply, map_smul] at this
      rw [this, ha]
      refine Finset.sum_congr rfl fun μ _ => ?_
      simp [rotDiff, fdiff, eU, Matrix.mulVec_sub]
    exact e2
  have hq : dotT i₀ a a = wquad (gradTensor i₀ R ψ) x x' := by
    have h1 : dotT i₀ a a = ∑ μ, ∑ μ', ((w μ : ℤ) : ℂ) * ((w μ' : ℤ) : ℂ) *
        dotT i₀ (rotDiff R ψ (eU μ)) (rotDiff R ψ (eU μ')) := by
      rw [ha, dotT_sum_left]
      refine Finset.sum_congr rfl fun μ _ => ?_
      rw [dotT_smul_left, dotT_sum_right, Finset.mul_sum]
      refine Finset.sum_congr rfl fun μ' _ => ?_
      rw [dotT_smul_right]; ring
    rw [h1]
    simp [wquad, gradTensor, hw]
  have haN : ‖a‖ ≤ 2 * L * (N * 40 * (σ * ε)) := by
    have h1 : ‖a‖ ≤ (l1 w : ℝ) * (N * 40 * (σ * ε)) := by
      refine norm_sum_smul_le w (fun μ => rotDiff R ψ (eU μ)) fun μ => ?_
      have := norm_mulVec_le (R := R) (B := 40) (by norm_num) hR (ψ (eU μ) - ψ 0)
      have h3 := hadj 0 μ
      simp only [zero_add] at h3
      calc ‖rotDiff R ψ (eU μ)‖ ≤ N * 40 * ‖ψ (eU μ) - ψ 0‖ := this
        _ ≤ N * 40 * (σ * ε) := by
          exact mul_le_mul_of_nonneg_left (by simpa [eU] using h3) (by positivity)
    refine h1.trans ?_
    have : 0 ≤ (N : ℝ) * 40 * (σ * ε) := by positivity
    nlinarith
  have hbN : ‖b‖ ≤ N * 40 * (6 * L ^ 2 * K₂) := by
    have h1 := norm_mulVec_le (R := R) (B := 40) (by norm_num) hR r
    refine h1.trans ?_
    have hl0 : (0 : ℝ) ≤ l1 w := Nat.cast_nonneg _
    have hl1 : (0 : ℝ) ≤ l1 x' := Nat.cast_nonneg _
    have : ((l1 w : ℝ) ^ 2 + (l1 w : ℝ) * (l1 x' : ℝ)) ≤ 6 * L ^ 2 := by nlinarith
    have h2 : ‖r‖ ≤ 6 * L ^ 2 * K₂ := hrb.trans (mul_le_mul_of_nonneg_right this hK0)
    exact mul_le_mul_of_nonneg_left h2 (by positivity)
  rw [hΔ, ← hq]
  have e : dotT i₀ (a + b) (a + b) - dotT i₀ a a = 2 * dotT i₀ a b + dotT i₀ b b := by
    simp only [dotT_add_left, dotT_add_right, dotT_comm i₀ b a]; ring
  rw [e]
  have t1 := norm_dotT_le i₀ a b
  have t2 := norm_dotT_le i₀ b b
  have ha0 := norm_nonneg a
  have hb0 := norm_nonneg b
  calc ‖2 * dotT i₀ a b + dotT i₀ b b‖ ≤ ‖2 * dotT i₀ a b‖ + ‖dotT i₀ b b‖ := norm_add_le _ _
    _ ≤ 2 * (N * (‖a‖ * ‖b‖)) + N * (‖b‖ * ‖b‖) := by
        rw [norm_mul]; simp; linarith
    _ ≤ 2 * N * (2 * L * (N * 40 * (σ * ε))) * (N * 40 * (6 * L ^ 2 * K₂)) +
          N * (N * 40 * (6 * L ^ 2 * K₂)) ^ 2 := by
        have h1 : ‖a‖ * ‖b‖ ≤ (2 * L * (N * 40 * (σ * ε))) * (N * 40 * (6 * L ^ 2 * K₂)) :=
          mul_le_mul haN hbN hb0 (by positivity)
        have h2 : ‖b‖ * ‖b‖ ≤ (N * 40 * (6 * L ^ 2 * K₂)) ^ 2 := by
          rw [sq]; exact mul_le_mul hbN hbN hb0 (by positivity)
        have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg _
        nlinarith [mul_le_mul_of_nonneg_left h1 hN0, mul_le_mul_of_nonneg_left h2 hN0]

end Balaban.SmallField
