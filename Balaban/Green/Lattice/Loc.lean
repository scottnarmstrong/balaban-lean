/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Green.Lattice.LocCore

/-!
# Lemma Loc (a), (b): interior estimates for the discrete Poisson equation on `ℤ^d`

Unit lattice, `ℓ^∞` balls `B_r(x₀) = {z : ‖z - x₀‖ ≤ r}`, `d ≥ 3`.  If `-Δ¹ u = g` at all `z`
with `‖z - x₀‖ ≤ 2ρ - 1` (the interior points of `B_{2ρ}`), `ρ ≥ 8`, and `‖x - x₀‖ ≤ ρ/2`:

* `lemma_loc_a`:
  `|u(x)| ≤ C ρ^{-d/2} ‖u‖_{ℓ²(B_{2ρ})} + ∑_{z ∈ B_{2ρ}} C(x - z) |g(z)|`;
* `lemma_loc_b`:
  `|u(x + e_ν) - u(x)| ≤ C ρ^{-1-d/2} ‖u‖_{ℓ²(B_{2ρ})}
      + ∑_{z ∈ B_{2ρ}} |C(x + e_ν - z) - C(x - z)| |g(z)|`,

with `C` the lattice Green's function and a constant `C = C(d)`.
-/

@[expose] public section

noncomputable section

namespace Balaban.LatticeGreen

variable {d : ℕ}

theorem sum_le_sqrt_card_mul (T : Finset (Fin d → ℤ)) (f : (Fin d → ℤ) → ℝ) :
    ∑ z ∈ T, f z ≤ Real.sqrt (T.card : ℝ) * Real.sqrt (∑ z ∈ T, f z ^ 2) := by
  rw [← Real.sqrt_mul (Nat.cast_nonneg _)]
  exact (le_abs_self _).trans (Real.abs_le_sqrt sq_sum_le_card_mul_sum_sq)

theorem inv_pow_mul_sqrt_pow {ρ : ℝ} (hρ : 0 < ρ) (j : ℕ) :
    1 / ρ ^ (d + j) * Real.sqrt (ρ ^ d) = ρ ^ (-(j : ℝ) - (d : ℝ) / 2) := by
  have h1 : Real.sqrt (ρ ^ d) = ρ ^ ((d : ℝ) / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hρ.le]
    congr 1
    ring
  have h2 : 1 / ρ ^ (d + j) = ρ ^ (-((d : ℝ) + j)) := by
    rw [Real.rpow_neg hρ.le, one_div]
    congr 1
    rw [← Real.rpow_natCast]
    push_cast
    rfl
  rw [h1, h2, ← Real.rpow_add hρ]
  congr 1
  ring

/-- Reduction of an `ℓ¹` sum over the ball `B_{2ρ}` to the `ℓ²` norm. -/
theorem l1_ball_le {ρ : ℝ} (hρ : 1 ≤ ρ) (x₀ : Fin d → ℤ) (u : (Fin d → ℤ) → ℂ) (j : ℕ) :
    1 / ρ ^ (d + j) * ∑ w ∈ latticeBall x₀ (2 * ρ), ‖u w‖ ≤
      Real.sqrt (5 ^ d) * ρ ^ (-(j : ℝ) - (d : ℝ) / 2) *
        Real.sqrt (∑ w ∈ latticeBall x₀ (2 * ρ), ‖u w‖ ^ 2) := by
  have hρ0 : 0 < ρ := by linarith
  have hcard : ((latticeBall x₀ (2 * ρ)).card : ℝ) ≤ 5 ^ d * ρ ^ d := by
    refine (card_latticeBall_le x₀ (by linarith)).trans ?_
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by linarith) (by linarith) d
  have h1 := sum_le_sqrt_card_mul (latticeBall x₀ (2 * ρ)) (fun w => ‖u w‖)
  have h2 : Real.sqrt ((latticeBall x₀ (2 * ρ)).card : ℝ) ≤ Real.sqrt (5 ^ d) * Real.sqrt (ρ ^ d) := by
    rw [← Real.sqrt_mul (by positivity)]
    exact Real.sqrt_le_sqrt hcard
  have hpos : 0 ≤ 1 / ρ ^ (d + j) := by positivity
  calc 1 / ρ ^ (d + j) * ∑ w ∈ latticeBall x₀ (2 * ρ), ‖u w‖
      ≤ 1 / ρ ^ (d + j) * (Real.sqrt (5 ^ d) * Real.sqrt (ρ ^ d) *
          Real.sqrt (∑ w ∈ latticeBall x₀ (2 * ρ), ‖u w‖ ^ 2)) := by
        refine mul_le_mul_of_nonneg_left (h1.trans ?_) hpos
        exact mul_le_mul_of_nonneg_right h2 (Real.sqrt_nonneg _)
    _ = Real.sqrt (5 ^ d) * (1 / ρ ^ (d + j) * Real.sqrt (ρ ^ d)) *
          Real.sqrt (∑ w ∈ latticeBall x₀ (2 * ρ), ‖u w‖ ^ 2) := by ring
    _ = _ := by rw [inv_pow_mul_sqrt_pow hρ0 j]

theorem cutoff_mul_vanish {ρ : ℝ} (hρ : 4 ≤ ρ) (x₀ : Fin d → ℤ) (u : (Fin d → ℤ) → ℂ)
    (y : Fin d → ℤ) (hy : y ∉ latticeBall x₀ (2 * ρ)) :
    ((latticeCutoff ρ x₀ y : ℝ) : ℂ) * u y = 0 := by
  rw [(cutoff_zero_outside hρ x₀ hy).1]; simp

/-- **Lemma Loc (a)**, unit lattice. -/
theorem lemma_loc_a (hd : 3 ≤ d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (ρ : ℝ), 8 ≤ ρ → ∀ (x₀ x : Fin d → ℤ), ‖x - x₀‖ ≤ ρ / 2 →
      ∀ (u g : (Fin d → ℤ) → ℂ), (∀ z, ‖z - x₀‖ ≤ 2 * ρ - 1 → negLap u z = g z) →
        ‖u x‖ ≤ C * ρ ^ (-(d : ℝ) / 2) * Real.sqrt (∑ w ∈ latticeBall x₀ (2 * ρ), ‖u w‖ ^ 2) +
          ∑ z ∈ latticeBall x₀ (2 * ρ), latticeGreen d (x - z) * ‖g z‖ := by
  obtain ⟨c0, hc0, h0⟩ := latticeGreen_le hd
  obtain ⟨c1, hc1, h1⟩ := latticeGreen_diff1_le hd
  obtain ⟨c1', hc1', h1'⟩ := latticeGreen_bwd1_le hd
  have hk : d - 2 + 2 = d := by omega
  have hk1 : d - 2 + 1 = d - 1 := by omega
  have hm : 0 ≤ max c1 c1' := le_max_of_le_left hc1
  have hB : 0 ≤ (d : ℝ) * ((c0 * 2 ^ (d - 2) * cutoffProfile.M₂ + max c1 c1' * 2 ^ d *
      cutoffProfile.M₁)) := by
    have := cutoffProfile.M₁_nonneg
    have := cutoffProfile.M₂_nonneg
    positivity
  refine ⟨d * ((c0 * 2 ^ (d - 2) * cutoffProfile.M₂ + max c1 c1' * 2 ^ d *
    cutoffProfile.M₁)) * Real.sqrt (5 ^ d), by positivity, ?_⟩
  intro ρ hρ x₀ x hx u g hg
  have hρ0 : 0 < ρ := by linarith
  have hTS := ball_subset_succ x₀ hρ0.le
  have hTe : ∀ y ∈ latticeBall x₀ (2 * ρ), ∀ μ : Fin d, y + Pi.single μ 1 ∈
      latticeBall x₀ (2 * ρ + 1) ∧ y - Pi.single μ 1 ∈ latticeBall x₀ (2 * ρ + 1) :=
    fun y hy μ => ball_shift_mem x₀ hρ0.le hy μ
  have hxS : x ∈ latticeBall x₀ (2 * ρ + 1) :=
    (mem_latticeBall (by linarith)).2 (by linarith)
  have hxχ : latticeCutoff ρ x₀ x = 1 := latticeCutoff_eq_one hρ0 (by linarith)
  have hrep := green_representation hd (S := latticeBall x₀ (2 * ρ + 1))
    (T := latticeBall x₀ (2 * ρ)) (fun w => ((latticeCutoff ρ x₀ w : ℝ) : ℂ) * u w)
    (cutoff_mul_vanish (by linarith) x₀ u) hTS hTe x hxS
  have hux : u x = ∑ z ∈ latticeBall x₀ (2 * ρ + 1), ((latticeGreen d (x - z) : ℝ) : ℂ) *
      negLap (fun w => ((latticeCutoff ρ x₀ w : ℝ) : ℂ) * u w) z := by
    rw [hrep, hxχ]; simp
  have core := loc_core (latticeGreen d) (A := c0) (A' := max c1 c1') (k := d - 2) hc0 hm
    (fun y _ => by rw [abs_of_nonneg (latticeGreen_nonneg y)]; exact h0 y)
    (fun y μ _ => by
      rw [hk1]
      exact (h1 y μ).trans (div_le_div_of_nonneg_right (le_max_left _ _) (by positivity)))
    (fun y μ _ => by
      rw [hk1, abs_sub_comm]
      exact (h1' y μ).trans (div_le_div_of_nonneg_right (le_max_right _ _) (by positivity)))
    hρ x₀ x hx u g hg
  rw [hk] at core
  rw [hux]
  refine core.trans ?_
  have hl1 : 1 / ρ ^ d * ∑ w ∈ latticeBall x₀ (2 * ρ), ‖u w‖ ≤
      Real.sqrt (5 ^ d) * ρ ^ (-(d : ℝ) / 2) *
        Real.sqrt (∑ w ∈ latticeBall x₀ (2 * ρ), ‖u w‖ ^ 2) := by
    have h := l1_ball_le (d := d) (ρ := ρ) (by linarith) x₀ u 0
    have e : (-((0 : ℕ) : ℝ) - (d : ℝ) / 2) = -(d : ℝ) / 2 := by push_cast; ring
    rw [e, add_zero] at h
    exact h
  have e := mul_le_mul_of_nonneg_left hl1 hB
  have e2 : (d : ℝ) * ((c0 * 2 ^ (d - 2) * cutoffProfile.M₂ + max c1 c1' * 2 ^ d *
      cutoffProfile.M₁) / ρ ^ d) * ∑ w ∈ latticeBall x₀ (2 * ρ), ‖u w‖ =
      (d : ℝ) * ((c0 * 2 ^ (d - 2) * cutoffProfile.M₂ + max c1 c1' * 2 ^ d *
      cutoffProfile.M₁)) * (1 / ρ ^ d * ∑ w ∈ latticeBall x₀ (2 * ρ), ‖u w‖) := by ring
  have e3 : ∑ z ∈ latticeBall x₀ (2 * ρ), |latticeGreen d (x - z)| * ‖g z‖ =
      ∑ z ∈ latticeBall x₀ (2 * ρ), latticeGreen d (x - z) * ‖g z‖ :=
    Finset.sum_congr rfl fun z _ => by rw [abs_of_nonneg (latticeGreen_nonneg (x - z))]
  rw [e3, e2]
  nlinarith [e]

/-- **Lemma Loc (b)**, unit lattice: the discrete gradient. -/
theorem lemma_loc_b (hd : 3 ≤ d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (ρ : ℝ), 8 ≤ ρ → ∀ (x₀ x : Fin d → ℤ), ‖x - x₀‖ ≤ ρ / 2 →
      ∀ (ν : Fin d) (u g : (Fin d → ℤ) → ℂ),
        (∀ z, ‖z - x₀‖ ≤ 2 * ρ - 1 → negLap u z = g z) →
        ‖u (x + Pi.single ν 1) - u x‖ ≤
          C * ρ ^ (-1 - (d : ℝ) / 2) * Real.sqrt (∑ w ∈ latticeBall x₀ (2 * ρ), ‖u w‖ ^ 2) +
          ∑ z ∈ latticeBall x₀ (2 * ρ),
            |latticeGreen d (x - z + Pi.single ν 1) - latticeGreen d (x - z)| * ‖g z‖ := by
  obtain ⟨c1, hc1, h1⟩ := latticeGreen_diff1_le hd
  obtain ⟨c2, hc2, h2⟩ := latticeGreen_diff2_signs_le hd
  have hk : d - 1 + 1 = d := by omega
  have hk2 : d - 1 + 2 = d + 1 := by omega
  have hB : 0 ≤ (d : ℝ) * ((c1 * 2 ^ (d - 1) * cutoffProfile.M₂ + c2 * 2 ^ (d + 1) *
      cutoffProfile.M₁)) := by
    have := cutoffProfile.M₁_nonneg
    have := cutoffProfile.M₂_nonneg
    positivity
  refine ⟨d * ((c1 * 2 ^ (d - 1) * cutoffProfile.M₂ + c2 * 2 ^ (d + 1) *
    cutoffProfile.M₁)) * Real.sqrt (5 ^ d), by positivity, ?_⟩
  intro ρ hρ x₀ x hx ν u g hg
  have hρ0 : 0 < ρ := by linarith
  have hTS := ball_subset_succ x₀ hρ0.le
  have hTe : ∀ y ∈ latticeBall x₀ (2 * ρ), ∀ μ : Fin d, y + Pi.single μ 1 ∈
      latticeBall x₀ (2 * ρ + 1) ∧ y - Pi.single μ 1 ∈ latticeBall x₀ (2 * ρ + 1) :=
    fun y hy μ => ball_shift_mem x₀ hρ0.le hy μ
  have hxS : x ∈ latticeBall x₀ (2 * ρ + 1) :=
    (mem_latticeBall (by linarith)).2 (by linarith)
  have hxS' : x + Pi.single ν 1 ∈ latticeBall x₀ (2 * ρ + 1) := by
    rw [mem_latticeBall (by linarith)]
    have : x + Pi.single ν 1 - x₀ = (x - x₀) + Pi.single ν 1 := by abel
    rw [this]
    exact (norm_add_single_le _ ν).trans (by linarith)
  have hxχ : latticeCutoff ρ x₀ x = 1 := latticeCutoff_eq_one hρ0 (by linarith)
  have hxχ' : latticeCutoff ρ x₀ (x + Pi.single ν 1) = 1 := by
    refine latticeCutoff_eq_one hρ0 ?_
    have : x + Pi.single ν 1 - x₀ = (x - x₀) + Pi.single ν 1 := by abel
    rw [this]
    exact (norm_add_single_le _ ν).trans (by linarith)
  have hrep := green_diff_representation hd (S := latticeBall x₀ (2 * ρ + 1))
    (T := latticeBall x₀ (2 * ρ)) (fun w => ((latticeCutoff ρ x₀ w : ℝ) : ℂ) * u w)
    (cutoff_mul_vanish (by linarith) x₀ u) hTS hTe x ν hxS hxS'
  have hux : u (x + Pi.single ν 1) - u x = ∑ z ∈ latticeBall x₀ (2 * ρ + 1),
      (((latticeGreen d (x - z + Pi.single ν 1) - latticeGreen d (x - z) : ℝ)) : ℂ) *
      negLap (fun w => ((latticeCutoff ρ x₀ w : ℝ) : ℂ) * u w) z := by
    rw [hrep, hxχ, hxχ']; simp
  have core := loc_core (fun y => latticeGreen d (y + Pi.single ν 1) - latticeGreen d y)
    (A := c1) (A' := c2) (k := d - 1) hc1 hc2
    (fun y _ => h1 y ν)
    (fun y μ _ => by
      rw [hk]
      have e : latticeGreen d (y + Pi.single μ 1 + Pi.single ν 1) -
          latticeGreen d (y + Pi.single μ 1) -
          (latticeGreen d (y + Pi.single ν 1) - latticeGreen d y) =
          secondDiff (latticeGreen d) ((1 : ℤ) • Pi.single μ 1) ((1 : ℤ) • Pi.single ν 1) y := by
        unfold secondDiff; simp only [one_smul]; ring
      have := h2 y μ ν 1 1 (Or.inl rfl) (Or.inl rfl)
      rw [← e] at this
      exact this)
    (fun y μ _ => by
      rw [hk]
      have e : latticeGreen d (y - Pi.single μ 1 + Pi.single ν 1) -
          latticeGreen d (y - Pi.single μ 1) -
          (latticeGreen d (y + Pi.single ν 1) - latticeGreen d y) =
          secondDiff (latticeGreen d) ((-1 : ℤ) • Pi.single μ 1) ((1 : ℤ) • Pi.single ν 1) y := by
        unfold secondDiff; simp only [one_smul, neg_smul, ← sub_eq_add_neg]; ring
      have := h2 y μ ν (-1) 1 (Or.inr rfl) (Or.inl rfl)
      rw [← e] at this
      exact this)
    hρ x₀ x hx u g hg
  rw [hk2] at core
  rw [hux]
  refine core.trans ?_
  have hl1 : 1 / ρ ^ (d + 1) * ∑ w ∈ latticeBall x₀ (2 * ρ), ‖u w‖ ≤
      Real.sqrt (5 ^ d) * ρ ^ (-1 - (d : ℝ) / 2) *
        Real.sqrt (∑ w ∈ latticeBall x₀ (2 * ρ), ‖u w‖ ^ 2) := by
    have h := l1_ball_le (d := d) (ρ := ρ) (by linarith) x₀ u 1
    have e : (-((1 : ℕ) : ℝ) - (d : ℝ) / 2) = -1 - (d : ℝ) / 2 := by push_cast; ring
    rw [e] at h
    exact h
  have e := mul_le_mul_of_nonneg_left hl1 hB
  have e2 : (d : ℝ) * ((c1 * 2 ^ (d - 1) * cutoffProfile.M₂ + c2 * 2 ^ (d + 1) *
      cutoffProfile.M₁) / ρ ^ (d + 1)) * ∑ w ∈ latticeBall x₀ (2 * ρ), ‖u w‖ =
      (d : ℝ) * ((c1 * 2 ^ (d - 1) * cutoffProfile.M₂ + c2 * 2 ^ (d + 1) *
      cutoffProfile.M₁)) * (1 / ρ ^ (d + 1) * ∑ w ∈ latticeBall x₀ (2 * ρ), ‖u w‖) := by ring
  rw [e2]
  nlinarith [e]

end Balaban.LatticeGreen
