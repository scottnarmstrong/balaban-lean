/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Green.Lattice.ThirdDiff
public import Balaban.Green.Lattice.LocCutoff

/-!
# Differences of the lattice Green's function along a translation

Let `F_ν(y) = C(y + e_ν) - C(y)`.  Telescoping the second and third difference bounds along a
lattice path from `0` to `a` (of `ℓ¹` length `≤ d ‖a‖`) gives, for `2 ‖a‖ ≤ 1 + ‖y‖`,

* `|F_ν(y + a) - F_ν(y)| ≤ c ‖a‖ ⟨y⟩^{-d}`,
* `|K(y ± e_μ) - K(y)| ≤ c ‖a‖ ⟨y⟩^{-d-1}` for `K(y) = F_ν(y + a) - F_ν(y)`.
-/

@[expose] public section

noncomputable section

namespace Balaban.LatticeGreen

variable {d : ℕ}

/-- The forward first difference `C(y + e_ν) - C(y)`. -/
def greenDiff (d : ℕ) (ν : Fin d) (y : Fin d → ℤ) : ℝ :=
  latticeGreen d (y + Pi.single ν 1) - latticeGreen d y

/-- The unit difference `F_ν(y + σ e_μ) - F_ν(y)` of `F_ν`. -/
def greenDiff2 (d : ℕ) (ν μ : Fin d) (σ : ℤ) (y : Fin d → ℤ) : ℝ :=
  greenDiff d ν (y + σ • Pi.single μ 1) - greenDiff d ν y

theorem sum_natAbs_le_card_mul (z : Fin d → ℤ) : ((∑ i, (z i).natAbs : ℕ) : ℝ) ≤ d * ‖z‖ := by
  push_cast
  calc ∑ i, ((z i).natAbs : ℝ) ≤ ∑ _i : Fin d, ‖z‖ := Finset.sum_le_sum fun i _ => by
        have := norm_le_pi_norm z i
        rw [Int.norm_eq_abs] at this
        rwa [Nat.cast_natAbs, Int.cast_abs]
    _ = d * ‖z‖ := by simp

theorem abs_cast_le_of_natAbs_le' {a b : ℤ} (h : a.natAbs ≤ b.natAbs) : |(a : ℝ)| ≤ |(b : ℝ)| := by
  have := (Nat.cast_le (α := ℝ)).2 h
  rwa [Nat.cast_natAbs, Nat.cast_natAbs, Int.cast_abs, Int.cast_abs] at this

/-- A nonzero lattice vector can be reduced by one unit step without increasing the sup norm. -/
theorem lattice_descent (z : Fin d → ℤ) (μ : Fin d) (hz : z μ ≠ 0) :
    ∃ z' : Fin d → ℤ, ∑ i, (z' i).natAbs + 1 = ∑ i, (z i).natAbs ∧ ‖z'‖ ≤ ‖z‖ ∧
      (z' = z - Pi.single μ 1 ∨ z' = z + Pi.single μ 1) := by
  have key : ∀ (ε : ℤ), (z μ + ε).natAbs + 1 = (z μ).natAbs →
      (∑ i, ((z + (Pi.single μ ε : Fin d → ℤ)) i).natAbs + 1 = ∑ i, (z i).natAbs ∧
        ‖z + (Pi.single μ ε : Fin d → ℤ)‖ ≤ ‖z‖) := by
    intro ε hε
    constructor
    · have e1 : ∑ i, (z i).natAbs = (z μ).natAbs + ∑ i ∈ Finset.univ.erase μ, (z i).natAbs :=
        (Finset.add_sum_erase _ _ (Finset.mem_univ μ)).symm
      have e2 : ∑ i, ((z + (Pi.single μ ε : Fin d → ℤ)) i).natAbs =
          ((z + (Pi.single μ ε : Fin d → ℤ)) μ).natAbs +
          ∑ i ∈ Finset.univ.erase μ, ((z + (Pi.single μ ε : Fin d → ℤ)) i).natAbs :=
        (Finset.add_sum_erase _ _ (Finset.mem_univ μ)).symm
      have e3 : ∑ i ∈ Finset.univ.erase μ, ((z + (Pi.single μ ε : Fin d → ℤ)) i).natAbs =
          ∑ i ∈ Finset.univ.erase μ, (z i).natAbs :=
        Finset.sum_congr rfl fun i hi => by
          simp [Pi.single_eq_of_ne (Finset.ne_of_mem_erase hi)]
      have e4 : ((z + (Pi.single μ ε : Fin d → ℤ)) μ).natAbs = (z μ + ε).natAbs := by simp
      omega
    · rw [pi_norm_le_iff_of_nonneg (norm_nonneg _)]
      intro i
      by_cases hi : i = μ
      · subst hi
        simp only [Pi.add_apply, Pi.single_eq_same, Int.norm_eq_abs]
        have h1 : (z i + ε).natAbs ≤ (z i).natAbs := by omega
        have h2 := norm_le_pi_norm z i
        rw [Int.norm_eq_abs] at h2
        exact (abs_cast_le_of_natAbs_le' h1).trans h2
      · simpa [Pi.single_eq_of_ne hi] using norm_le_pi_norm z i
  rcases lt_or_gt_of_ne hz with hneg | hpos
  · obtain ⟨h1, h2⟩ := key 1 (by omega)
    exact ⟨z + Pi.single μ 1, h1, h2, Or.inr rfl⟩
  · obtain ⟨h1, h2⟩ := key (-1) (by omega)
    refine ⟨z + Pi.single μ (-1), h1, h2, Or.inl ?_⟩
    rw [Pi.single_neg, sub_eq_add_neg]

/-- Telescoping a unit-step bound along a lattice path from `0` to `a`. -/
theorem telescope_le (F : (Fin d → ℤ) → ℝ) {c : ℝ} (hc : 0 ≤ c) {k : ℕ}
    (hF : ∀ (y : Fin d → ℤ) (μ : Fin d) (σ : ℤ), (σ = 1 ∨ σ = -1) →
      |F (y + σ • Pi.single μ 1) - F y| ≤ c / (1 + ‖y‖) ^ k) {r : ℝ} :
    ∀ (N : ℕ) (a : Fin d → ℤ) (w : Fin d → ℤ), ∑ i, (a i).natAbs = N → ‖a‖ ≤ r →
      2 * r ≤ 1 + ‖w‖ → |F (w + a) - F w| ≤ N * (2 ^ k * c) / (1 + ‖w‖) ^ k := by
  intro N
  induction N with
  | zero =>
      intro a w ha _ _
      have h0 : a = 0 := by
        funext i
        have := (Finset.sum_eq_zero_iff.1 ha) i (Finset.mem_univ i)
        simpa using this
      subst h0
      simp
  | succ N ih =>
      intro a w ha har hw
      obtain ⟨μ, -, hμ⟩ := Finset.exists_ne_zero_of_sum_ne_zero (s := Finset.univ)
        (f := fun i => (a i).natAbs) (by rw [ha]; omega)
      have haμ : a μ ≠ 0 := by
        intro h; apply hμ; simp [h]
      obtain ⟨a', hsum, hnorm, ha'⟩ := lattice_descent a μ haμ
      have ih' := ih a' w (by omega) (hnorm.trans har) hw
      have hr0 : 0 ≤ r := (norm_nonneg _).trans har
      -- the last step
      obtain ⟨σ, hσ, hstep⟩ : ∃ σ : ℤ, (σ = 1 ∨ σ = -1) ∧ w + a = (w + a') + σ • Pi.single μ 1 := by
        rcases ha' with rfl | rfl
        · exact ⟨1, Or.inl rfl, by rw [one_smul]; abel⟩
        · exact ⟨-1, Or.inr rfl, by rw [neg_one_smul]; abel⟩
      have hy : (1 + ‖w‖) / 2 ≤ 1 + ‖w + a'‖ := by
        have h1 : ‖w‖ ≤ ‖w + a'‖ + ‖a'‖ := by
          have := norm_sub_le (w + a') a'
          simpa using this
        have := hnorm.trans har
        linarith [norm_nonneg w]
      have hpos : 0 < 1 + ‖w‖ := by linarith [norm_nonneg w]
      have hpos' : 0 < (1 + ‖w‖) / 2 := by linarith
      have hb : |F (w + a' + σ • Pi.single μ 1) - F (w + a')| ≤ 2 ^ k * c / (1 + ‖w‖) ^ k := by
        refine (hF _ μ σ hσ).trans ?_
        have h1 : ((1 + ‖w‖) / 2) ^ k ≤ (1 + ‖w + a'‖) ^ k := pow_le_pow_left₀ hpos'.le hy k
        have h2 : c / (1 + ‖w + a'‖) ^ k ≤ c / ((1 + ‖w‖) / 2) ^ k :=
          div_le_div_of_nonneg_left hc (by positivity) h1
        refine h2.trans (le_of_eq ?_)
        rw [div_pow]
        field_simp
      have e : F (w + a) - F w = (F (w + a' + σ • Pi.single μ 1) - F (w + a')) +
          (F (w + a') - F w) := by rw [hstep]; ring
      rw [e]
      refine (abs_add_le _ _).trans ?_
      calc _ ≤ 2 ^ k * c / (1 + ‖w‖) ^ k + N * (2 ^ k * c) / (1 + ‖w‖) ^ k := add_le_add hb ih'
        _ = ((N + 1 : ℕ) : ℝ) * (2 ^ k * c) / (1 + ‖w‖) ^ k := by push_cast; ring

/-- Bounds for `K(y) = F_ν(y + a) - F_ν(y)` and its unit differences, for `2 ‖a‖ ≤ ⟨y⟩`. -/
theorem greenDiff_translate_bounds (hd : 3 ≤ d) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ (ν : Fin d) (a : Fin d → ℤ) (r : ℝ), ‖a‖ ≤ r → ∀ y : Fin d → ℤ,
      2 * r ≤ 1 + ‖y‖ →
      |greenDiff d ν (y + a) - greenDiff d ν y| ≤ c * r / (1 + ‖y‖) ^ d ∧
      ∀ μ : Fin d, |(greenDiff d ν (y + Pi.single μ 1 + a) - greenDiff d ν (y + Pi.single μ 1)) -
          (greenDiff d ν (y + a) - greenDiff d ν y)| ≤ c * r / (1 + ‖y‖) ^ (d + 1) ∧
        |(greenDiff d ν (y - Pi.single μ 1 + a) - greenDiff d ν (y - Pi.single μ 1)) -
          (greenDiff d ν (y + a) - greenDiff d ν y)| ≤ c * r / (1 + ‖y‖) ^ (d + 1) := by
  obtain ⟨c2, hc2, h2⟩ := latticeGreen_diff2_signs_le hd
  obtain ⟨c3, hc3, h3⟩ := latticeGreen_diff3_signs_le hd
  refine ⟨d * 2 ^ (d + 1) * (c2 + c3), by positivity, fun ν a r har y hy => ?_⟩
  have hr0 : 0 ≤ r := (norm_nonneg _).trans har
  have hNr : ((∑ i, (a i).natAbs : ℕ) : ℝ) ≤ d * r :=
    (sum_natAbs_le_card_mul a).trans (mul_le_mul_of_nonneg_left har (Nat.cast_nonneg d))
  have hpos : 0 < (1 + ‖y‖) ^ d := by positivity
  have hpos1 : 0 < (1 + ‖y‖) ^ (d + 1) := by positivity
  -- first-order bound
  have hF1 : ∀ (y' : Fin d → ℤ) (μ : Fin d) (σ : ℤ), (σ = 1 ∨ σ = -1) →
      |greenDiff d ν (y' + σ • Pi.single μ 1) - greenDiff d ν y'| ≤ c2 / (1 + ‖y'‖) ^ d := by
    intro y' μ σ hσ
    have e : greenDiff d ν (y' + σ • Pi.single μ 1) - greenDiff d ν y' =
        secondDiff (latticeGreen d) (σ • Pi.single μ 1) ((1 : ℤ) • Pi.single ν 1) y' := by
      simp only [secondDiff, greenDiff, one_smul]
      ring
    rw [e]
    exact h2 y' μ ν σ 1 hσ (Or.inl rfl)
  have hT1 := telescope_le (fun y' => greenDiff d ν y') hc2 hF1 (r := r)
    (∑ i, (a i).natAbs) a y rfl har hy
  refine ⟨?_, fun μ => ?_⟩
  · refine hT1.trans ?_
    calc _ ≤ (d * r) * (2 ^ d * c2) / (1 + ‖y‖) ^ d := by
          apply div_le_div_of_nonneg_right _ hpos.le
          exact mul_le_mul_of_nonneg_right hNr (by positivity)
      _ ≤ _ := by
          rw [div_le_div_iff_of_pos_right hpos]
          have h5 : (2 : ℝ) ^ d ≤ 2 ^ (d + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
          have h4 : 0 ≤ (d : ℝ) * r := by positivity
          have h6 : (2 : ℝ) ^ d * c2 ≤ 2 ^ (d + 1) * (c2 + c3) := by
            nlinarith [mul_nonneg (sub_nonneg.2 h5) hc2, mul_nonneg (by positivity : (0 : ℝ) ≤ 2 ^ (d + 1)) hc3]
          calc (d : ℝ) * r * (2 ^ d * c2) ≤ (d : ℝ) * r * (2 ^ (d + 1) * (c2 + c3)) :=
                mul_le_mul_of_nonneg_left h6 h4
            _ = _ := by ring
  · -- second-order bounds: telescope the function `G_σ(y) = F(y + σ e_μ) - F(y)`
    have hG : ∀ σ : ℤ, (σ = 1 ∨ σ = -1) →
        |(greenDiff d ν (y + σ • Pi.single μ 1 + a) - greenDiff d ν (y + σ • Pi.single μ 1)) -
          (greenDiff d ν (y + a) - greenDiff d ν y)| ≤
          (d * r) * (2 ^ (d + 1) * c3) / (1 + ‖y‖) ^ (d + 1) := by
      intro σ hσ
      have hF2 : ∀ (y' : Fin d → ℤ) (lam : Fin d) (τ : ℤ), (τ = 1 ∨ τ = -1) →
          |greenDiff2 d ν μ σ (y' + τ • Pi.single lam 1) - greenDiff2 d ν μ σ y'| ≤
            c3 / (1 + ‖y'‖) ^ (d + 1) := by
        intro y' lam τ hτ
        have e : greenDiff2 d ν μ σ (y' + τ • Pi.single lam 1) - greenDiff2 d ν μ σ y' =
            thirdDiff (latticeGreen d) (σ • Pi.single μ 1) ((1 : ℤ) • Pi.single ν 1)
              (τ • Pi.single lam 1) y' := by
          simp only [greenDiff2, thirdDiff, secondDiff, greenDiff, one_smul]
          ring
        rw [e]
        exact h3 y' μ ν lam σ 1 τ hσ (Or.inl rfl) hτ
      have hT2 := telescope_le (greenDiff2 d ν μ σ) hc3 hF2 (r := r) (∑ i, (a i).natAbs) a y rfl
        har hy
      have e : (greenDiff d ν (y + σ • Pi.single μ 1 + a) - greenDiff d ν (y + σ • Pi.single μ 1)) -
          (greenDiff d ν (y + a) - greenDiff d ν y) =
          (greenDiff d ν (y + a + σ • Pi.single μ 1) - greenDiff d ν (y + a)) -
          (greenDiff d ν (y + σ • Pi.single μ 1) - greenDiff d ν y) := by
        have hc : y + σ • Pi.single μ 1 + a = y + a + σ • Pi.single μ 1 := by abel
        rw [hc]; ring
      rw [e]
      unfold greenDiff2 at hT2
      refine hT2.trans ?_
      apply div_le_div_of_nonneg_right _ hpos1.le
      exact mul_le_mul_of_nonneg_right hNr (by positivity)
    have hfin : (d * r) * (2 ^ (d + 1) * c3) / (1 + ‖y‖) ^ (d + 1) ≤
        d * 2 ^ (d + 1) * (c2 + c3) * r / (1 + ‖y‖) ^ (d + 1) := by
      apply div_le_div_of_nonneg_right _ hpos1.le
      have h4 : 0 ≤ (d : ℝ) * 2 ^ (d + 1) * r := by positivity
      nlinarith [mul_nonneg h4 hc2]
    refine ⟨?_, ?_⟩
    · have := hG 1 (Or.inl rfl)
      rw [one_smul] at this
      exact this.trans hfin
    · have := hG (-1) (Or.inr rfl)
      rw [neg_one_smul, ← sub_eq_add_neg] at this
      exact this.trans hfin

end Balaban.LatticeGreen
