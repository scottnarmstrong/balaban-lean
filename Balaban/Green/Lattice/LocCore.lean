/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Green.Lattice.LocAlgebra

/-!
# Lemma Loc: the core estimate

For a kernel `K` on `ℤ^d` with `|K(y)| ≤ A ⟨y⟩^{-k}` and `|K(y ± e_μ) - K(y)| ≤ A' ⟨y⟩^{-(k+1)}`,
a cutoff `χ` as in `Balaban.LatticeGreen.latticeCutoff`, and `-Δ u = g` on the ball `B_{2ρ-1}`,
we bound `∑_z K(x - z) (-Δ(χ u))(z)` for `x ∈ B_{ρ/2}` by

`∑_{z ∈ B_{2ρ}} |K(x-z)| |g(z)| + C ρ^{-(k+2)} ∑_{w ∈ B_{2ρ}} |u(w)|`.
-/

@[expose] public section

noncomputable section

namespace Balaban.LatticeGreen

variable {d : ℕ}

theorem div_pow_le_of_half {a ρ t : ℝ} (ha : 0 ≤ a) (hρ : 0 < ρ) (ht : ρ / 2 ≤ t) (k : ℕ) :
    a / t ^ k ≤ a * 2 ^ k / ρ ^ k := by
  have h1 : (ρ / 2) ^ k ≤ t ^ k := pow_le_pow_left₀ (by positivity) ht k
  have h2 : 0 < (ρ / 2) ^ k := by positivity
  calc a / t ^ k ≤ a / (ρ / 2) ^ k := div_le_div_of_nonneg_left ha h2 h1
    _ = a * 2 ^ k / ρ ^ k := by rw [div_pow]; field_simp

theorem norm_add_single_le (z : Fin d → ℤ) (μ : Fin d) : ‖z + Pi.single μ 1‖ ≤ ‖z‖ + 1 :=
  (norm_add_le _ _).trans (by linarith [norm_pi_single_le μ])

theorem norm_sub_single_le (z : Fin d → ℤ) (μ : Fin d) : ‖z - Pi.single μ 1‖ ≤ ‖z‖ + 1 :=
  (norm_sub_le _ _).trans (by linarith [norm_pi_single_le μ])

theorem coef_term_le (K : (Fin d → ℤ) → ℝ) {A A' : ℝ} {k : ℕ} (hA : 0 ≤ A) (hA' : 0 ≤ A')
    (hK0 : ∀ y, |K y| ≤ A / (1 + ‖y‖) ^ k)
    (hKf : ∀ y μ, |K (y + Pi.single μ 1) - K y| ≤ A' / (1 + ‖y‖) ^ (k + 1))
    (hKb : ∀ y μ, |K (y - Pi.single μ 1) - K y| ≤ A' / (1 + ‖y‖) ^ (k + 1))
    {ρ M₁ M₂ : ℝ} (hρ : 0 < ρ) (χ : (Fin d → ℤ) → ℝ)
    (h1f : ∀ z μ, |χ (z + Pi.single μ 1) - χ z| ≤ M₁ / ρ)
    (h1b : ∀ z μ, |χ (z - Pi.single μ 1) - χ z| ≤ M₁ / ρ)
    (h2 : ∀ z μ, |χ (z + Pi.single μ 1) + χ (z - Pi.single μ 1) - 2 * χ z| ≤ M₂ / ρ ^ 2)
    (y w : Fin d → ℤ) (hy : ρ / 2 ≤ 1 + ‖y‖) (μ : Fin d) :
    |K (y + Pi.single μ 1) * (χ (w - Pi.single μ 1) - χ w) +
        K (y - Pi.single μ 1) * (χ (w + Pi.single μ 1) - χ w)| ≤
      (A * 2 ^ k * M₂ + A' * 2 ^ (k + 2) * M₁) / ρ ^ (k + 2) := by
  have key : K (y + Pi.single μ 1) * (χ (w - Pi.single μ 1) - χ w) +
      K (y - Pi.single μ 1) * (χ (w + Pi.single μ 1) - χ w) =
      K y * (χ (w + Pi.single μ 1) + χ (w - Pi.single μ 1) - 2 * χ w) +
      (K (y + Pi.single μ 1) - K y) * (χ (w - Pi.single μ 1) - χ w) +
      (K (y - Pi.single μ 1) - K y) * (χ (w + Pi.single μ 1) - χ w) := by ring
  rw [key]
  have b0 : |K y| ≤ A * 2 ^ k / ρ ^ k := (hK0 y).trans (div_pow_le_of_half hA hρ hy k)
  have bf : |K (y + Pi.single μ 1) - K y| ≤ A' * 2 ^ (k + 1) / ρ ^ (k + 1) :=
    (hKf y μ).trans (div_pow_le_of_half hA' hρ hy (k + 1))
  have bb : |K (y - Pi.single μ 1) - K y| ≤ A' * 2 ^ (k + 1) / ρ ^ (k + 1) :=
    (hKb y μ).trans (div_pow_le_of_half hA' hρ hy (k + 1))
  have t1 : |K y * (χ (w + Pi.single μ 1) + χ (w - Pi.single μ 1) - 2 * χ w)| ≤
      A * 2 ^ k / ρ ^ k * (M₂ / ρ ^ 2) := by
    rw [abs_mul]
    exact mul_le_mul b0 (h2 w μ) (abs_nonneg _) (by positivity)
  have t2 : |(K (y + Pi.single μ 1) - K y) * (χ (w - Pi.single μ 1) - χ w)| ≤
      A' * 2 ^ (k + 1) / ρ ^ (k + 1) * (M₁ / ρ) := by
    rw [abs_mul]
    exact mul_le_mul bf (h1b w μ) (abs_nonneg _) (by positivity)
  have t3 : |(K (y - Pi.single μ 1) - K y) * (χ (w + Pi.single μ 1) - χ w)| ≤
      A' * 2 ^ (k + 1) / ρ ^ (k + 1) * (M₁ / ρ) := by
    rw [abs_mul]
    exact mul_le_mul bb (h1f w μ) (abs_nonneg _) (by positivity)
  calc _ ≤ |K y * (χ (w + Pi.single μ 1) + χ (w - Pi.single μ 1) - 2 * χ w)| +
        |(K (y + Pi.single μ 1) - K y) * (χ (w - Pi.single μ 1) - χ w)| +
        |(K (y - Pi.single μ 1) - K y) * (χ (w + Pi.single μ 1) - χ w)| := abs_add_three _ _ _
    _ ≤ A * 2 ^ k / ρ ^ k * (M₂ / ρ ^ 2) + A' * 2 ^ (k + 1) / ρ ^ (k + 1) * (M₁ / ρ) +
        A' * 2 ^ (k + 1) / ρ ^ (k + 1) * (M₁ / ρ) := by linarith
    _ = _ := by field_simp; ring

theorem coef_le (K : (Fin d → ℤ) → ℝ) {A A' : ℝ} {k : ℕ} (hA : 0 ≤ A) (hA' : 0 ≤ A')
    (hK0 : ∀ y, |K y| ≤ A / (1 + ‖y‖) ^ k)
    (hKf : ∀ y μ, |K (y + Pi.single μ 1) - K y| ≤ A' / (1 + ‖y‖) ^ (k + 1))
    (hKb : ∀ y μ, |K (y - Pi.single μ 1) - K y| ≤ A' / (1 + ‖y‖) ^ (k + 1))
    {ρ M₁ M₂ : ℝ} (hρ : 0 < ρ) (hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂) (χ : (Fin d → ℤ) → ℝ)
    (h1f : ∀ z μ, |χ (z + Pi.single μ 1) - χ z| ≤ M₁ / ρ)
    (h1b : ∀ z μ, |χ (z - Pi.single μ 1) - χ z| ≤ M₁ / ρ)
    (h2 : ∀ z μ, |χ (z + Pi.single μ 1) + χ (z - Pi.single μ 1) - 2 * χ z| ≤ M₂ / ρ ^ 2)
    (x₀ : Fin d → ℤ) (hone : ∀ z, ‖z - x₀‖ ≤ ρ → χ z = 1)
    (x w : Fin d → ℤ) (hx : ‖x - x₀‖ ≤ ρ / 2) :
    |∑ μ : Fin d, (K (x - w + Pi.single μ 1) * (χ (w - Pi.single μ 1) - χ w) +
        K (x - w - Pi.single μ 1) * (χ (w + Pi.single μ 1) - χ w))| ≤
      d * ((A * 2 ^ k * M₂ + A' * 2 ^ (k + 2) * M₁) / ρ ^ (k + 2)) := by
  by_cases hw : ‖w - x₀‖ ≤ ρ - 1
  · have hz : ∀ μ : Fin d, K (x - w + Pi.single μ 1) * (χ (w - Pi.single μ 1) - χ w) +
        K (x - w - Pi.single μ 1) * (χ (w + Pi.single μ 1) - χ w) = 0 := by
      intro μ
      have e1 : χ (w - Pi.single μ 1) = 1 := hone _ (by
        have : w - Pi.single μ 1 - x₀ = (w - x₀) - Pi.single μ 1 := by abel
        rw [this]
        exact (norm_sub_single_le _ μ).trans (by linarith))
      have e2 : χ (w + Pi.single μ 1) = 1 := hone _ (by
        have : w + Pi.single μ 1 - x₀ = (w - x₀) + Pi.single μ 1 := by abel
        rw [this]
        exact (norm_add_single_le _ μ).trans (by linarith))
      have e3 : χ w = 1 := hone _ (by linarith)
      rw [e1, e2, e3]; ring
    rw [Finset.sum_eq_zero fun μ _ => hz μ, abs_zero]
    have := hM₁; have := hM₂
    positivity
  · push Not at hw
    have hy : ρ / 2 ≤ 1 + ‖x - w‖ := by
      have h1 : ‖w - x₀‖ ≤ ‖x - w‖ + ‖x - x₀‖ := by
        have : w - x₀ = (x - x₀) - (x - w) := by abel
        rw [this]
        exact (norm_sub_le _ _).trans (le_of_eq (add_comm _ _))
      linarith
    calc _ ≤ ∑ μ : Fin d, |K (x - w + Pi.single μ 1) * (χ (w - Pi.single μ 1) - χ w) +
        K (x - w - Pi.single μ 1) * (χ (w + Pi.single μ 1) - χ w)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _μ : Fin d, (A * 2 ^ k * M₂ + A' * 2 ^ (k + 2) * M₁) / ρ ^ (k + 2) :=
          Finset.sum_le_sum fun μ _ =>
            coef_term_le K hA hA' hK0 hKf hKb hρ χ h1f h1b h2 (x - w) w hy μ
      _ = _ := by simp

theorem ball_subset_succ (x₀ : Fin d → ℤ) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    latticeBall x₀ (2 * ρ) ⊆ latticeBall x₀ (2 * ρ + 1) := fun z hz =>
  (mem_latticeBall (by linarith)).2 (by linarith [(mem_latticeBall (by linarith)).1 hz])

theorem ball_shift_mem (x₀ : Fin d → ℤ) {ρ : ℝ} (hρ : 0 ≤ ρ) {y : Fin d → ℤ}
    (hy : y ∈ latticeBall x₀ (2 * ρ)) (μ : Fin d) :
    y + Pi.single μ 1 ∈ latticeBall x₀ (2 * ρ + 1) ∧
      y - Pi.single μ 1 ∈ latticeBall x₀ (2 * ρ + 1) := by
  have hy' := (mem_latticeBall (by linarith)).1 hy
  constructor
  · rw [mem_latticeBall (by linarith)]
    have : y + Pi.single μ 1 - x₀ = (y - x₀) + Pi.single μ 1 := by abel
    rw [this]
    exact (norm_add_single_le _ μ).trans (by linarith)
  · rw [mem_latticeBall (by linarith)]
    have : y - Pi.single μ 1 - x₀ = (y - x₀) - Pi.single μ 1 := by abel
    rw [this]
    exact (norm_sub_single_le _ μ).trans (by linarith)

theorem cutoff_zero_outside {ρ : ℝ} (hρ : 4 ≤ ρ) (x₀ : Fin d → ℤ) {w : Fin d → ℤ}
    (hw : w ∉ latticeBall x₀ (2 * ρ)) :
    latticeCutoff ρ x₀ w = 0 ∧ ∀ μ : Fin d, latticeCutoff ρ x₀ (w + Pi.single μ 1) = 0 ∧
      latticeCutoff ρ x₀ (w - Pi.single μ 1) = 0 := by
  have hρ0 : 0 < ρ := by linarith
  have hw' : 2 * ρ < ‖w - x₀‖ := by
    by_contra h
    exact hw ((mem_latticeBall (by linarith)).2 (not_lt.1 h))
  refine ⟨latticeCutoff_eq_zero hρ0 (by linarith), fun μ => ⟨latticeCutoff_eq_zero hρ0 ?_,
    latticeCutoff_eq_zero hρ0 ?_⟩⟩
  · have : w - x₀ = (w + Pi.single μ 1 - x₀) - Pi.single μ 1 := by abel
    have h2 := norm_sub_single_le (w + Pi.single μ 1 - x₀) μ
    rw [← this] at h2
    linarith
  · have : w - x₀ = (w - Pi.single μ 1 - x₀) + Pi.single μ 1 := by abel
    have h2 := norm_add_single_le (w - Pi.single μ 1 - x₀) μ
    rw [← this] at h2
    linarith

/-- The core estimate of Lemma Loc: for `x ∈ B_{ρ/2}` and `-Δ u = g` on `B_{2ρ-1}`,
`‖∑_z K(x-z) (-Δ(χ u))(z)‖ ≤ ∑_{B_{2ρ}} |K(x-z)| |g(z)| + C ρ^{-(k+2)} ∑_{B_{2ρ}} |u|`. -/
theorem loc_core (K : (Fin d → ℤ) → ℝ) {A A' : ℝ} {k : ℕ} (hA : 0 ≤ A) (hA' : 0 ≤ A')
    (hK0 : ∀ y, |K y| ≤ A / (1 + ‖y‖) ^ k)
    (hKf : ∀ y μ, |K (y + Pi.single μ 1) - K y| ≤ A' / (1 + ‖y‖) ^ (k + 1))
    (hKb : ∀ y μ, |K (y - Pi.single μ 1) - K y| ≤ A' / (1 + ‖y‖) ^ (k + 1))
    {ρ : ℝ} (hρ : 8 ≤ ρ) (x₀ x : Fin d → ℤ) (hx : ‖x - x₀‖ ≤ ρ / 2)
    (u g : (Fin d → ℤ) → ℂ) (hg : ∀ z, ‖z - x₀‖ ≤ 2 * ρ - 1 → negLap u z = g z) :
    ‖∑ z ∈ latticeBall x₀ (2 * ρ + 1), ((K (x - z) : ℝ) : ℂ) *
        negLap (fun w => ((latticeCutoff ρ x₀ w : ℝ) : ℂ) * u w) z‖ ≤
      ∑ z ∈ latticeBall x₀ (2 * ρ), |K (x - z)| * ‖g z‖ +
        d * ((A * 2 ^ k * cutoffProfile.M₂ + A' * 2 ^ (k + 2) * cutoffProfile.M₁) / ρ ^ (k + 2)) *
          ∑ w ∈ latticeBall x₀ (2 * ρ), ‖u w‖ := by
  have hρ0 : 0 < ρ := by linarith
  set χ := latticeCutoff ρ x₀ with hχdef
  set S := latticeBall x₀ (2 * ρ + 1) with hS
  set T := latticeBall x₀ (2 * ρ) with hT
  have memS : ∀ z, z ∈ S ↔ ‖z - x₀‖ ≤ 2 * ρ + 1 := fun z => mem_latticeBall (by linarith)
  have memT : ∀ z, z ∈ T ↔ ‖z - x₀‖ ≤ 2 * ρ := fun z => mem_latticeBall (by linarith)
  have hzero : ∀ z, 2 * ρ - 1 < ‖z - x₀‖ → χ z = 0 := fun z hz =>
    latticeCutoff_eq_zero hρ0 (by linarith)
  have hone : ∀ z, ‖z - x₀‖ ≤ ρ → χ z = 1 := fun z hz => latticeCutoff_eq_one hρ0 hz
  have hTS : T ⊆ S := ball_subset_succ x₀ hρ0.le
  have hTe : ∀ y ∈ T, ∀ μ : Fin d, y + Pi.single μ 1 ∈ S ∧ y - Pi.single μ 1 ∈ S :=
    fun y hy μ => ball_shift_mem x₀ hρ0.le hy μ
  have hχT : ∀ w, w ∉ T → χ w = 0 ∧ ∀ μ : Fin d,
      χ (w + Pi.single μ 1) = 0 ∧ χ (w - Pi.single μ 1) = 0 :=
    fun w hw => cutoff_zero_outside (by linarith) x₀ hw
  have hv : ∀ y, y ∉ T → ((χ y : ℝ) : ℂ) * u y = 0 := fun y hy => by
    rw [(hχT y hy).1]; simp
  have hexp : ∑ z ∈ S, ((K (x - z) : ℝ) : ℂ) * negLap (fun w => ((χ w : ℝ) : ℂ) * u w) z =
      ∑ z ∈ S, ((K (x - z) : ℝ) : ℂ) * (((χ z : ℝ) : ℂ) * g z) +
      ∑ z ∈ S, ((K (x - z) : ℝ) : ℂ) * cutoffRemainder χ u z := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [negLap_cutoff_mul]
    by_cases h : χ z = 0
    · simp [h]
    · have hz : negLap u z = g z := hg z (by
        by_contra hc
        exact h (hzero z (by linarith [not_le.1 hc])))
      rw [hz]; ring
  have hrem := sum_kernel_remainder (S := S) (T := T) K x χ u hχT hTS hTe
  simp only [← Complex.ofReal_sum] at hrem
  rw [hexp, hrem]
  -- the two pieces
  have hT1 : ‖∑ z ∈ S, ((K (x - z) : ℝ) : ℂ) * (((χ z : ℝ) : ℂ) * g z)‖ ≤
      ∑ z ∈ T, |K (x - z)| * ‖g z‖ := by
    calc _ ≤ ∑ z ∈ S, ‖((K (x - z) : ℝ) : ℂ) * (((χ z : ℝ) : ℂ) * g z)‖ := norm_sum_le _ _
      _ = ∑ z ∈ T, ‖((K (x - z) : ℝ) : ℂ) * (((χ z : ℝ) : ℂ) * g z)‖ := by
          symm
          refine Finset.sum_subset hTS fun z _ hz => ?_
          rw [(hχT z hz).1]; simp
      _ ≤ _ := by
          refine Finset.sum_le_sum fun z _ => ?_
          rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
            Real.norm_eq_abs, abs_of_nonneg (latticeCutoff_nonneg ρ x₀ z)]
          have := latticeCutoff_le_one ρ x₀ z
          have h0 := latticeCutoff_nonneg ρ x₀ z
          have : |K (x - z)| * (χ z * ‖g z‖) ≤ |K (x - z)| * (1 * ‖g z‖) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right this (norm_nonneg _))
              (abs_nonneg _)
          linarith
  have hcoef : ∀ w, |∑ μ : Fin d, (K (x - w + Pi.single μ 1) * (χ (w - Pi.single μ 1) - χ w) +
        K (x - w - Pi.single μ 1) * (χ (w + Pi.single μ 1) - χ w))| ≤
      d * ((A * 2 ^ k * cutoffProfile.M₂ + A' * 2 ^ (k + 2) * cutoffProfile.M₁) / ρ ^ (k + 2)) :=
    fun w => coef_le K hA hA' hK0 hKf hKb hρ0 cutoffProfile.M₁_nonneg cutoffProfile.M₂_nonneg χ
      (fun z μ => latticeCutoff_diff1_add_le hρ0 x₀ z μ)
      (fun z μ => latticeCutoff_diff1_sub_le hρ0 x₀ z μ)
      (fun z μ => latticeCutoff_diff2_le hρ0 x₀ z μ) x₀ hone x w hx
  have hcoef0 : ∀ w, w ∉ T → ∑ μ : Fin d, (K (x - w + Pi.single μ 1) *
      (χ (w - Pi.single μ 1) - χ w) + K (x - w - Pi.single μ 1) *
      (χ (w + Pi.single μ 1) - χ w)) = 0 := by
    intro w hw
    refine Finset.sum_eq_zero fun μ _ => ?_
    obtain ⟨h0, h1⟩ := hχT w hw
    rw [h0, (h1 μ).1, (h1 μ).2]; ring
  have hT2 : ‖∑ w ∈ S, u w * ((∑ μ : Fin d, (K (x - w + Pi.single μ 1) *
      (χ (w - Pi.single μ 1) - χ w) + K (x - w - Pi.single μ 1) *
      (χ (w + Pi.single μ 1) - χ w)) : ℝ) : ℂ)‖ ≤
      d * ((A * 2 ^ k * cutoffProfile.M₂ + A' * 2 ^ (k + 2) * cutoffProfile.M₁) / ρ ^ (k + 2)) *
        ∑ w ∈ T, ‖u w‖ := by
    calc _ ≤ ∑ w ∈ S, ‖u w * ((∑ μ : Fin d, (K (x - w + Pi.single μ 1) *
          (χ (w - Pi.single μ 1) - χ w) + K (x - w - Pi.single μ 1) *
          (χ (w + Pi.single μ 1) - χ w)) : ℝ) : ℂ)‖ := norm_sum_le _ _
      _ = ∑ w ∈ T, ‖u w * ((∑ μ : Fin d, (K (x - w + Pi.single μ 1) *
          (χ (w - Pi.single μ 1) - χ w) + K (x - w - Pi.single μ 1) *
          (χ (w + Pi.single μ 1) - χ w)) : ℝ) : ℂ)‖ := by
          symm
          refine Finset.sum_subset hTS fun w _ hw => ?_
          rw [hcoef0 w hw]; simp
      _ ≤ ∑ w ∈ T, ‖u w‖ * (d * ((A * 2 ^ k * cutoffProfile.M₂ +
            A' * 2 ^ (k + 2) * cutoffProfile.M₁) / ρ ^ (k + 2))) := by
          refine Finset.sum_le_sum fun w _ => ?_
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
          exact mul_le_mul_of_nonneg_left (hcoef w) (norm_nonneg _)
      _ = _ := by rw [← Finset.sum_mul, mul_comm]
  exact (norm_add_le _ _).trans (add_le_add hT1 hT2)

end Balaban.LatticeGreen
