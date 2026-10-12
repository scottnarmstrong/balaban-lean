/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.SmallField.RenormTorus

/-!
# Corollary 2.2 (I-6, global form)

* `level_energy_bound`: on a torus, the sum over the centres `y` of the energies of one scale is
  bounded by `|Λ_j|` times the bounds of Theorem 2.1 (the terms `A_y` cancel, `Aterm_torus_sum`);
* `crude_energy_bound`: the crude bound `‖𝓔(0;ψ,b)‖ ≤ E₀ K₀` (P1 (2.29));
* `global_bound`: summation over the scales: `‖Σ_j 𝓔^{(j)}‖ ≤ C₆ E₀ |T₁^{(k)}|`.
-/

@[expose] public section

open Metric Set Matrix

namespace Balaban.SmallField

variable {d N : ℕ}

variable {T : TermFamily d N} {i₀ i₁ : Fin N} {ν ρ E₀ κ A K₀ : ℝ}
  {Dom : Set ((Site d → Spin N) × Spin N)}

/-- The crude bound `‖𝓔(0;ψ,b)‖ ≤ E₀ K₀` for `(ψ, b)` in the data domain. -/
theorem crude_energy_bound (hP : Premises T i₀ i₁ ν ρ E₀ κ A K₀ Dom) (hE0 : 0 ≤ E₀)
    (ψ : Site d → Spin N) (b : Spin N) (hψ : (ψ, b) ∈ Dom) :
    ‖energy T ψ b‖ ≤ E₀ * K₀ := by
  have hwt : ∀ X : T.polys, ‖T.term X.1 (pack X.1 ψ b)‖ ≤ E₀ * wt κ X.1 (T.dist X.1) := by
    intro X
    have h1 := hP.bdd_dom X.1 X.2 (ψ, b) hψ
    have hd0 := hP.dist_nonneg X.1 X.2
    have h2 := wt_ge (κ := κ) X.1 hd0 (Finset.card_pos.mpr ⟨0, hP.zero_mem X.1 X.2⟩) 0 0
      (by norm_num) (by norm_num)
    simp only [pow_zero, one_mul] at h2
    exact h1.trans (mul_le_mul_of_nonneg_left h2 hE0)
  have hb := tsum_of_norm_bounded (hP.count_summable.mul_left E₀).hasSum hwt
  unfold energy
  refine hb.trans ?_
  rw [tsum_mul_left]
  exact mul_le_mul_of_nonneg_left hP.count_le hE0

theorem Aterm_shift_torus (hP : Premises T i₀ i₁ ν ρ E₀ κ A K₀ Dom) (hρ : 0 < ρ) (hE0 : 0 ≤ E₀)
    (ℓ : ℕ) [NeZero ℓ] (ψT : Torus d ℓ → Spin N) (y : Torus d ℓ) :
    Aterm T i₀ ν (fun x => ψT (y + liftSite ℓ x)) =
      (1 / 2 : ℂ) * ∑' z : Site d, aCoef T i₀ ν z *
        (dot (ψT (y + liftSite ℓ z)) (ψT (y + liftSite ℓ z)) - dot (ψT y) (ψT y)) := by
  classical
  set g : Torus d ℓ → ℂ := fun y => dot (ψT y) (ψT y) with hg
  set B : ℝ := ∑ y, ‖g y‖ with hB
  have hbd : ∀ y, ‖g y‖ ≤ B := fun y =>
    Finset.single_le_sum (f := fun y => ‖g y‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ y)
  have := Aterm_eq_sum hP hρ hE0 (fun x => ψT (y + liftSite ℓ x)) (H := 2 * B) (fun x => by
    have h0 : liftSite ℓ (0 : Site d) = 0 := by ext μ; simp [liftSite]
    simp only [h0, add_zero]
    calc ‖dot (ψT (y + liftSite ℓ x)) (ψT (y + liftSite ℓ x)) - dot (ψT y) (ψT y)‖
        ≤ ‖g (y + liftSite ℓ x)‖ + ‖g y‖ := norm_sub_le _ _
      _ ≤ 2 * B := by linarith [hbd (y + liftSite ℓ x), hbd y])
  have h0 : liftSite ℓ (0 : Site d) = 0 := by ext μ; simp [liftSite]
  simpa [h0] using this

theorem renormalization_level (N : ℕ) (A Λ Ksig α₁ K₀ : ℝ) (hA : 0 ≤ A) (hΛ : 1 ≤ Λ)
    (hKsig : 0 ≤ Ksig) (hK₀ : 0 ≤ K₀) (hα0 : 0 < α₁) (hα1 : α₁ < 1) :
    ∃ C σ₁ : ℝ, 0 ≤ C ∧ 0 < σ₁ ∧ ∀ {d : ℕ} (T : TermFamily d N) (i₀ i₁ : Fin N)
      (ν ρ E₀ κ : ℝ) (Dom : Set ((Site d → Spin N) × Spin N))
      (_ : Premises T i₀ i₁ ν ρ E₀ κ A K₀ Dom) (ℓ : ℕ) [NeZero ℓ] (ψT : Torus d ℓ → Spin N)
      (b : Spin N) (σ ε K₂ : ℝ),
      (∀ y : Torus d ℓ, DataHyp Dom ν σ ε K₂ (fun x => ψT (y + liftSite ℓ x)) b) →
      0 < ρ → ρ ≤ 1 → 0 < ε → ε ≤ Λ * ρ → 0 < σ → σ ≤ σ₁ → 0 ≤ ν → ν ≤ σ ^ 2 → 0 ≤ E₀ →
      K₂ ≤ Ksig * σ ^ (2 - α₁) * ε →
      ‖∑ y : Torus d ℓ, energy T (fun x => ψT (y + liftSite ℓ x)) b‖ ≤
        (Fintype.card (Torus d ℓ) : ℝ) *
          (C * E₀ * σ ^ 4 * (ε / ρ) ^ 2 + C * E₀ * σ ^ (3 - α₁) * (ε / ρ) ^ 2) := by
  obtain ⟨C, σ₁, hC0, hσ₁, hloc⟩ := renormalization_local N A Λ Ksig α₁ K₀ hA hΛ hKsig hK₀ hα0 hα1
  refine ⟨C, σ₁, hC0, hσ₁, ?_⟩
  intro d T i₀ i₁ ν ρ E₀ κ Dom hP ℓ _ ψT b σ ε K₂ hdat hρ hρ1 hε hεΛ hσ hσσ₁ hν hνσ hE0 hK
  classical
  have hy : ∀ y : Torus d ℓ, ‖potential T (ψT y) b‖ ≤ C * E₀ * σ ^ 4 * (ε / ρ) ^ 2 ∧
      ‖energy T (fun x => ψT (y + liftSite ℓ x)) b - potential T (ψT y) b -
        Aterm T i₀ ν (fun x => ψT (y + liftSite ℓ x))‖ ≤
        C * E₀ * σ ^ (3 - α₁) * (ε / ρ) ^ 2 := by
    intro y
    have h0 : liftSite ℓ (0 : Site d) = 0 := by ext μ; simp [liftSite]
    have := hloc T i₀ i₁ ν ρ E₀ κ Dom hP (fun x => ψT (y + liftSite ℓ x)) b σ ε K₂ (hdat y)
      hρ hρ1 hε hεΛ hσ hσσ₁ hν hνσ hE0 hK
    simpa [h0] using this
  have hsplit : ∑ y : Torus d ℓ, energy T (fun x => ψT (y + liftSite ℓ x)) b =
      ∑ y : Torus d ℓ, potential T (ψT y) b +
      ∑ y : Torus d ℓ, (energy T (fun x => ψT (y + liftSite ℓ x)) b - potential T (ψT y) b -
        Aterm T i₀ ν (fun x => ψT (y + liftSite ℓ x))) +
      ∑ y : Torus d ℓ, Aterm T i₀ ν (fun x => ψT (y + liftSite ℓ x)) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun y _ => ?_
    ring
  have hA0 : ∑ y : Torus d ℓ, Aterm T i₀ ν (fun x => ψT (y + liftSite ℓ x)) = 0 := by
    simp only [Aterm_shift_torus hP hρ hE0]
    exact Aterm_torus_sum hP hρ hE0 ℓ ψT
  rw [hsplit, hA0, add_zero]
  have b1 : ‖∑ y : Torus d ℓ, potential T (ψT y) b‖ ≤
      (Fintype.card (Torus d ℓ) : ℝ) * (C * E₀ * σ ^ 4 * (ε / ρ) ^ 2) :=
    norm_sum_le_card _ fun y => (hy y).1
  have b2 : ‖∑ y : Torus d ℓ, (energy T (fun x => ψT (y + liftSite ℓ x)) b - potential T (ψT y) b -
        Aterm T i₀ ν (fun x => ψT (y + liftSite ℓ x)))‖ ≤
      (Fintype.card (Torus d ℓ) : ℝ) * (C * E₀ * σ ^ (3 - α₁) * (ε / ρ) ^ 2) :=
    norm_sum_le_card _ fun y => (hy y).2
  calc _ ≤ _ := norm_add_le _ _
    _ ≤ _ := add_le_add b1 b2
    _ = _ := by ring

/-- **Summation over the scales** (the end of the proof of Corollary 2.2).  `e j` is the total
energy of the scale `j`, `L^{(k-j) D} t₁` the number of its sites, and `q = L^{-α₃}`.  The last
`n₁` scales are bounded crudely, the others by the decay of Theorem 2.1. -/
theorem global_bound (k n₁ D : ℕ) {L t₁ E₀ K₀ Cθ q : ℝ} (hL : 1 ≤ L) (ht₁ : 0 ≤ t₁)
    (hE0 : 0 ≤ E₀) (hK0 : 0 ≤ K₀) (hCθ : 0 ≤ Cθ) (hq0 : 0 ≤ q) (hq1 : q < 1) (e : ℕ → ℂ)
    (hnear : ∀ j ≤ k, k - j < n₁ → ‖e j‖ ≤ L ^ ((k - j) * D) * t₁ * (E₀ * K₀))
    (hfar : ∀ j ≤ k, n₁ ≤ k - j → ‖e j‖ ≤ t₁ * E₀ * Cθ * q ^ (k - j)) :
    ‖∑ j ∈ Finset.range (k + 1), e j‖ ≤
      (K₀ * n₁ * L ^ (n₁ * D) + Cθ / (1 - q)) * E₀ * t₁ := by
  have hrefl : ∑ j ∈ Finset.range (k + 1), e j = ∑ n ∈ Finset.range (k + 1), e (k - n) := by
    rw [← Finset.sum_range_reflect]
    refine Finset.sum_congr rfl fun n hn => ?_
    simp only [Finset.mem_range] at hn
    congr 1
  rw [hrefl]
  have hL0 : 0 < L := by linarith
  set f : ℕ → ℝ := fun n => (if n < n₁ then L ^ (n * D) * t₁ * (E₀ * K₀) else 0) +
    t₁ * E₀ * Cθ * q ^ n with hf
  have hbd : ∀ n ∈ Finset.range (k + 1), ‖e (k - n)‖ ≤
      (if n < n₁ then L ^ (n * D) * t₁ * (E₀ * K₀) else 0) +
        (if n₁ ≤ n then t₁ * E₀ * Cθ * q ^ n else 0) := by
    intro n hn
    simp only [Finset.mem_range] at hn
    have hjk : k - n ≤ k := Nat.sub_le _ _
    have hkn : k - (k - n) = n := by omega
    by_cases h : n < n₁
    · have := hnear (k - n) hjk (by rw [hkn]; exact h)
      rw [hkn] at this
      have h2 : ¬ n₁ ≤ n := by omega
      simp only [h, h2, ite_true, ite_false, add_zero]
      exact this
    · have h2 : n₁ ≤ n := by omega
      have := hfar (k - n) hjk (by rw [hkn]; exact h2)
      rw [hkn] at this
      simp only [h, h2, ite_true, ite_false, zero_add]
      exact this
  refine (norm_sum_le _ _).trans ((Finset.sum_le_sum hbd).trans ?_)
  rw [Finset.sum_add_distrib]
  have s1 : ∑ n ∈ Finset.range (k + 1), (if n < n₁ then L ^ (n * D) * t₁ * (E₀ * K₀) else 0) ≤
      K₀ * n₁ * L ^ (n₁ * D) * E₀ * t₁ := by
    calc _ ≤ ∑ n ∈ Finset.range n₁, L ^ (n₁ * D) * t₁ * (E₀ * K₀) := by
          calc ∑ n ∈ Finset.range (k + 1), (if n < n₁ then L ^ (n * D) * t₁ * (E₀ * K₀) else 0)
              ≤ ∑ n ∈ Finset.range (k + 1), (if n < n₁ then L ^ (n₁ * D) * t₁ * (E₀ * K₀) else 0) := by
                refine Finset.sum_le_sum fun n _ => ?_
                split_ifs with h
                · have : L ^ (n * D) ≤ L ^ (n₁ * D) :=
                    pow_le_pow_right₀ hL (Nat.mul_le_mul_right D h.le)
                  have : 0 ≤ t₁ * (E₀ * K₀) := by positivity
                  nlinarith
                · exact le_rfl
            _ ≤ ∑ n ∈ Finset.range n₁, L ^ (n₁ * D) * t₁ * (E₀ * K₀) := by
                rw [← Finset.sum_filter]
                refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => by positivity)
                intro n hn
                simp only [Finset.mem_filter, Finset.mem_range] at hn ⊢
                exact hn.2
      _ = _ := by simp; ring
  have s2 : ∑ n ∈ Finset.range (k + 1), (if n₁ ≤ n then t₁ * E₀ * Cθ * q ^ n else 0) ≤
      Cθ / (1 - q) * E₀ * t₁ := by
    calc _ ≤ ∑ n ∈ Finset.range (k + 1), t₁ * E₀ * Cθ * q ^ n := by
          refine Finset.sum_le_sum fun n _ => ?_
          split_ifs
          · exact le_rfl
          · positivity
      _ ≤ t₁ * E₀ * Cθ * (1 / (1 - q)) := by
          rw [← Finset.mul_sum]
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          have h1 := Summable.sum_le_tsum (Finset.range (k + 1)) (fun i _ => pow_nonneg hq0 i)
            (summable_geometric_of_lt_one hq0 hq1)
          rw [tsum_geometric_of_lt_one hq0 hq1] at h1
          simpa [one_div] using h1
      _ = _ := by ring
  nlinarith

end Balaban.SmallField
