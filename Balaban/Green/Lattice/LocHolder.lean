/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Green.Lattice.Loc
public import Balaban.Green.Lattice.HolderKernel

/-!
# Lemma Loc (c): the Hölder estimate for the discrete gradient

Unit lattice, `ℓ^∞` balls.  If `-Δ¹ u = g` on `B_{2ρ-1}(x₀)`, `ρ ≥ 8`, `x, x' ∈ B_{ρ/2}(x₀)`,
`‖x - x'‖ ≤ r ≤ ρ/4` and `ν` is a direction, then with `F_ν(y) = C(y + e_ν) - C(y)`

`|(u(x + e_ν) - u(x)) - (u(x' + e_ν) - u(x'))| ≤
   C r ρ^{-2-d/2} ‖u‖_{ℓ²(B_{2ρ})} + ∑_{z ∈ B_{2ρ}} |F_ν(x - z) - F_ν(x' - z)| |g(z)|`.
-/

@[expose] public section

noncomputable section

namespace Balaban.LatticeGreen

variable {d : ℕ}

/-- The gradient of the Green representation of the cutoff function. -/
theorem diff_repr_cutoff (hd : 3 ≤ d) {ρ : ℝ} (hρ : 8 ≤ ρ) (x₀ x : Fin d → ℤ)
    (hx : ‖x - x₀‖ ≤ ρ / 2) (ν : Fin d) (u : (Fin d → ℤ) → ℂ) :
    u (x + Pi.single ν 1) - u x = ∑ z ∈ latticeBall x₀ (2 * ρ + 1),
      ((greenDiff d ν (x - z) : ℝ) : ℂ) *
        negLap (fun w => ((latticeCutoff ρ x₀ w : ℝ) : ℂ) * u w) z := by
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
  rw [hxχ, hxχ'] at hrep
  simp only [Complex.ofReal_one, one_mul] at hrep
  rw [← hrep]
  rfl

/-- **Lemma Loc (c)**, unit lattice. -/
theorem lemma_loc_c (hd : 3 ≤ d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (ρ : ℝ), 8 ≤ ρ → ∀ (x₀ x x' : Fin d → ℤ), ‖x - x₀‖ ≤ ρ / 2 →
      ‖x' - x₀‖ ≤ ρ / 2 → ∀ (r : ℝ), ‖x - x'‖ ≤ r → r ≤ ρ / 4 →
      ∀ (ν : Fin d) (u g : (Fin d → ℤ) → ℂ),
        (∀ z, ‖z - x₀‖ ≤ 2 * ρ - 1 → negLap u z = g z) →
        ‖(u (x + Pi.single ν 1) - u x) - (u (x' + Pi.single ν 1) - u x')‖ ≤
          C * r * ρ ^ (-2 - (d : ℝ) / 2) *
            Real.sqrt (∑ w ∈ latticeBall x₀ (2 * ρ), ‖u w‖ ^ 2) +
          ∑ z ∈ latticeBall x₀ (2 * ρ), |greenDiff d ν (x - z) - greenDiff d ν (x' - z)| *
            ‖g z‖ := by
  obtain ⟨c, hc0, hc⟩ := greenDiff_translate_bounds hd
  have hB : 0 ≤ (d : ℝ) * ((c * 2 ^ d * cutoffProfile.M₂ + c * 2 ^ (d + 2) *
      cutoffProfile.M₁)) := by
    have := cutoffProfile.M₁_nonneg
    have := cutoffProfile.M₂_nonneg
    positivity
  refine ⟨d * ((c * 2 ^ d * cutoffProfile.M₂ + c * 2 ^ (d + 2) * cutoffProfile.M₁)) *
    Real.sqrt (5 ^ d), by positivity, ?_⟩
  intro ρ hρ x₀ x x' hx hx' r hr hrρ ν u g hg
  have hρ0 : 0 < ρ := by linarith
  have hr0 : 0 ≤ r := (norm_nonneg _).trans hr
  set a : Fin d → ℤ := x - x' with ha
  set K : (Fin d → ℤ) → ℝ := fun y => greenDiff d ν (y + a) - greenDiff d ν y with hK
  have hKb : ∀ y, ρ / 2 ≤ 1 + ‖y‖ →
      |K y| ≤ (c * r) / (1 + ‖y‖) ^ d ∧
      ∀ μ : Fin d, |K (y + Pi.single μ 1) - K y| ≤ (c * r) / (1 + ‖y‖) ^ (d + 1) ∧
        |K (y - Pi.single μ 1) - K y| ≤ (c * r) / (1 + ‖y‖) ^ (d + 1) := by
    intro y hy
    obtain ⟨h1, h2⟩ := hc ν a r hr y (by linarith)
    exact ⟨h1, fun μ => h2 μ⟩
  have core := loc_core K (A := c * r) (A' := c * r) (k := d) (by positivity) (by positivity)
    (fun y hy => (hKb y hy).1) (fun y μ hy => ((hKb y hy).2 μ).1)
    (fun y μ hy => ((hKb y hy).2 μ).2) hρ x₀ x' hx' u g hg
  have hrepx := diff_repr_cutoff hd hρ x₀ x hx ν u
  have hrepx' := diff_repr_cutoff hd hρ x₀ x' hx' ν u
  have hdiff : (u (x + Pi.single ν 1) - u x) - (u (x' + Pi.single ν 1) - u x') =
      ∑ z ∈ latticeBall x₀ (2 * ρ + 1), ((K (x' - z) : ℝ) : ℂ) *
        negLap (fun w => ((latticeCutoff ρ x₀ w : ℝ) : ℂ) * u w) z := by
    rw [hrepx, hrepx', ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun z _ => ?_
    have e : x' - z + a = x - z := by rw [ha]; abel
    simp only [hK, e]
    push_cast
    ring
  rw [hdiff]
  refine core.trans ?_
  have hl1 : 1 / ρ ^ (d + 2) * ∑ w ∈ latticeBall x₀ (2 * ρ), ‖u w‖ ≤
      Real.sqrt (5 ^ d) * ρ ^ (-2 - (d : ℝ) / 2) *
        Real.sqrt (∑ w ∈ latticeBall x₀ (2 * ρ), ‖u w‖ ^ 2) := by
    have h := l1_ball_le (d := d) (ρ := ρ) (by linarith) x₀ u 2
    have e : (-((2 : ℕ) : ℝ) - (d : ℝ) / 2) = -2 - (d : ℝ) / 2 := by push_cast; ring
    rw [e] at h
    exact h
  have hM1 := cutoffProfile.M₁_nonneg
  have hM2 := cutoffProfile.M₂_nonneg
  have e := mul_le_mul_of_nonneg_left hl1 (by positivity :
    (0 : ℝ) ≤ (d : ℝ) * ((c * r * 2 ^ d * cutoffProfile.M₂ + c * r * 2 ^ (d + 2) *
      cutoffProfile.M₁)))
  have e2 : (d : ℝ) * ((c * r * 2 ^ d * cutoffProfile.M₂ + c * r * 2 ^ (d + 2) *
      cutoffProfile.M₁) / ρ ^ (d + 2)) * ∑ w ∈ latticeBall x₀ (2 * ρ), ‖u w‖ =
      (d : ℝ) * ((c * r * 2 ^ d * cutoffProfile.M₂ + c * r * 2 ^ (d + 2) *
      cutoffProfile.M₁)) * (1 / ρ ^ (d + 2) * ∑ w ∈ latticeBall x₀ (2 * ρ), ‖u w‖) := by ring
  have e3 : ∑ z ∈ latticeBall x₀ (2 * ρ), |K (x' - z)| * ‖g z‖ =
      ∑ z ∈ latticeBall x₀ (2 * ρ), |greenDiff d ν (x - z) - greenDiff d ν (x' - z)| * ‖g z‖ := by
    refine Finset.sum_congr rfl fun z _ => ?_
    have e : x' - z + a = x - z := by rw [ha]; abel
    simp only [hK, e]
  have e4 : (c * r) * 2 ^ d * cutoffProfile.M₂ + (c * r) * 2 ^ (d + 2) * cutoffProfile.M₁ =
      c * r * 2 ^ d * cutoffProfile.M₂ + c * r * 2 ^ (d + 2) * cutoffProfile.M₁ := rfl
  rw [e3]
  have e5 : ((c * r) * 2 ^ d * cutoffProfile.M₂ + (c * r) * 2 ^ (d + 2) * cutoffProfile.M₁) /
      ρ ^ (d + 2) = (c * r * 2 ^ d * cutoffProfile.M₂ + c * r * 2 ^ (d + 2) *
      cutoffProfile.M₁) / ρ ^ (d + 2) := rfl
  have e6 : (d : ℝ) * (((c * r) * 2 ^ d * cutoffProfile.M₂ + (c * r) * 2 ^ (d + 2) *
      cutoffProfile.M₁) / ρ ^ (d + 2)) * ∑ w ∈ latticeBall x₀ (2 * ρ), ‖u w‖ ≤
      (d * ((c * 2 ^ d * cutoffProfile.M₂ + c * 2 ^ (d + 2) * cutoffProfile.M₁)) *
        Real.sqrt (5 ^ d)) * r * ρ ^ (-2 - (d : ℝ) / 2) *
        Real.sqrt (∑ w ∈ latticeBall x₀ (2 * ρ), ‖u w‖ ^ 2) := by
    rw [e5, e2]
    have : (d : ℝ) * (c * r * 2 ^ d * cutoffProfile.M₂ + c * r * 2 ^ (d + 2) *
        cutoffProfile.M₁) * (Real.sqrt (5 ^ d) * ρ ^ (-2 - (d : ℝ) / 2) *
        Real.sqrt (∑ w ∈ latticeBall x₀ (2 * ρ), ‖u w‖ ^ 2)) =
        (d * ((c * 2 ^ d * cutoffProfile.M₂ + c * 2 ^ (d + 2) * cutoffProfile.M₁)) *
        Real.sqrt (5 ^ d)) * r * ρ ^ (-2 - (d : ℝ) / 2) *
        Real.sqrt (∑ w ∈ latticeBall x₀ (2 * ρ), ‖u w‖ ^ 2) := by ring
    rw [← this]
    exact e
  linarith

end Balaban.LatticeGreen
