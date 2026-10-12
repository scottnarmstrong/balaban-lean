/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.SmallField.RenormSmall

/-!
# The contribution of a polymer with large `d_j(X)` and the potential (Steps 1 and 3 of §2.3)

* `Ctx.tail_case`: the crude bound for `𝓔(0,X;ψ,b) - 𝓔(0,X;ψ(0),b) - A_X + ¼ Σ B wquad`;
* `Ctx.potential_term`: the expansion of `𝓔(0,X;ψ(0),b)` to first order at the reference point.
-/

@[expose] public section

open Metric Set Matrix

namespace Balaban.SmallField

variable {d N : ℕ}

theorem norm_wquad_le (G : Fin d → Fin d → ℂ) {Gm : ℝ} (hG : ∀ μ μ', ‖G μ μ'‖ ≤ Gm)
    (x x' : Site d) : ‖wquad G x x'‖ ≤ (l1 (x - x') : ℝ) ^ 2 * Gm := by
  have hGm : 0 ≤ Gm ∨ d = 0 := by
    by_cases hd : d = 0
    · exact Or.inr hd
    · exact Or.inl (le_trans (norm_nonneg _) (hG ⟨0, Nat.pos_of_ne_zero hd⟩ ⟨0, Nat.pos_of_ne_zero hd⟩))
  have hw : ∀ μ, ‖(((x μ - x' μ : ℤ)) : ℂ)‖ = (((x - x') μ).natAbs : ℝ) := by
    intro μ
    rw [Complex.norm_intCast]; simp
  calc ‖wquad G x x'‖ ≤ ∑ μ, ∑ μ', ‖(((x μ - x' μ : ℤ)) : ℂ) * (((x μ' - x' μ' : ℤ)) : ℂ) * G μ μ'‖ := by
        unfold wquad
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun μ _ => norm_sum_le _ _)
    _ ≤ ∑ μ, ∑ μ', (((x - x') μ).natAbs : ℝ) * (((x - x') μ').natAbs : ℝ) * Gm := by
        refine Finset.sum_le_sum fun μ _ => Finset.sum_le_sum fun μ' _ => ?_
        rw [norm_mul, norm_mul, hw, hw]
        exact mul_le_mul_of_nonneg_left (hG μ μ') (by positivity)
    _ = (l1 (x - x') : ℝ) ^ 2 * Gm := by
        unfold l1; push_cast
        rw [sq, Finset.sum_mul_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun μ _ => ?_
        rw [Finset.sum_mul]

/-- The explicit bound of the tail estimate. -/
noncomputable def tailBnd (N : ℕ) (A M ρ σ ε t P : ℝ) : ℝ :=
  M * (2 + P * (σ ^ 2 * ε / ρ) + 6400 * N ^ 3 * A ^ 2 * P ^ 2 * t ^ 2 * (σ * ε / ρ) ^ 2)

variable {T : TermFamily d N} {i₀ i₁ : Fin N} {ν ρ E₀ κ A K₀ : ℝ}
  {Dom : Set ((Site d → Spin N) × Spin N)} {ψ : Site d → Spin N} {b : Spin N}
  {σ ε K₂ : ℝ} {u : ℂ} {R : Matrix (Fin N) (Fin N) ℂ}

theorem l1_eU (μ : Fin d) : l1 (eU μ : Site d) = 1 := by
  unfold l1 eU
  rw [Finset.sum_eq_single μ]
  · simp
  · intro ν _ hν; simp [hν]
  · simp

/-- Bound for the first-order term `A_X`. -/
theorem Ctx.A_le (c : Ctx T i₀ i₁ ν ρ E₀ κ A K₀ Dom ψ b σ ε K₂ u R) {X : Finset (Site d)}
    (hX : X ∈ T.polys) :
    ‖(1 / 2 : ℂ) * ∑ x : ↥X, tensA i₀ ν X (T.term X) x *
      (dot (ψ x.1) (ψ x.1) - dot (ψ 0) (ψ 0))‖ ≤
      X.card * (E₀ * Real.exp (-κ * T.dist X) / ρ * (σ ^ 2 * ε)) := by
  have hok := c.termOK hX
  have hM := c.hM hX
  set M : ℝ := E₀ * Real.exp (-κ * T.dist X) with hMdef
  have hM0 : 0 ≤ M := by have := c.E0nn; positivity
  have hρ := c.ρpos
  have hcard : (Fintype.card ↥X : ℝ) = X.card := by simp
  have hcρ : 0 ≤ M / ρ := by positivity
  rw [norm_mul]
  have h1 : ‖∑ x : ↥X, tensA i₀ ν X (T.term X) x * (dot (ψ x.1) (ψ x.1) - dot (ψ 0) (ψ 0))‖ ≤
      (Fintype.card ↥X : ℝ) * (M / ρ * (2 * (σ ^ 2 * ε))) := by
    refine norm_sum_le_card _ fun x => ?_
    rw [norm_mul]
    exact mul_le_mul (hok.norm_tensA_le hM x) (c.ga_le x.1) (norm_nonneg _) hcρ
  have h2 : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by simp
  rw [h2, hcard] at *
  calc 1 / 2 * ‖∑ x : ↥X, tensA i₀ ν X (T.term X) x * (dot (ψ x.1) (ψ x.1) - dot (ψ 0) (ψ 0))‖
      ≤ 1 / 2 * ((X.card : ℝ) * (M / ρ * (2 * (σ ^ 2 * ε)))) :=
        mul_le_mul_of_nonneg_left h1 (by norm_num)
    _ = _ := by ring

/-- Bound for the quadratic term `L_X`. -/
theorem Ctx.Lq_le (c : Ctx T i₀ i₁ ν ρ E₀ κ A K₀ Dom ψ b σ ε K₂ u R) {X : Finset (Site d)}
    (hX : X ∈ T.polys) :
    ‖(1 / 4 : ℂ) * ∑ x : ↥X, ∑ x' : ↥X, tensB i₀ i₁ ν X (T.term X) x x' *
      wquad (gradTensor i₀ R ψ) x.1 x'.1‖ ≤
      (X.card : ℝ) ^ 2 * (E₀ * Real.exp (-κ * T.dist X) / ρ ^ 2) *
        ((2 * (A * (1 + T.dist X))) ^ 2 * (N * (N * 40 * (σ * ε)) ^ 2)) := by
  have hok := c.termOK hX
  have hM := c.hM hX
  have hd0 : 0 ≤ T.dist X := c.hyp.dist_nonneg X hX
  set t : ℝ := 1 + T.dist X with ht
  have ht1 : 1 ≤ t := by rw [ht]; linarith
  set M : ℝ := E₀ * Real.exp (-κ * T.dist X) with hMdef
  have hM0 : 0 ≤ M := by have := c.E0nn; positivity
  have hρ := c.ρpos
  have hσ := c.σpos
  have hε := c.εpos
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hcard : (Fintype.card ↥X : ℝ) = X.card := by simp
  have hcρ2 : 0 ≤ 4 * M / ρ ^ 2 := by positivity
  have hGm : ∀ μ μ', ‖gradTensor i₀ R ψ μ μ'‖ ≤ N * (N * 40 * (σ * ε)) ^ 2 := by
    intro μ μ'
    have hφ : ∀ ν', ‖rotDiff R ψ (eU ν')‖ ≤ N * 40 * (σ * ε) := fun ν' => by
      have := c.rotDiff_le (eU ν')
      rwa [l1_eU, Nat.cast_one, one_mul] at this
    refine (norm_dotT_le i₀ _ _).trans ?_
    rw [sq]
    exact mul_le_mul_of_nonneg_left (mul_le_mul (hφ μ) (hφ μ') (norm_nonneg _) (by positivity)) hN
  rw [norm_mul]
  have h1 : ‖∑ x : ↥X, ∑ x' : ↥X, tensB i₀ i₁ ν X (T.term X) x x' *
      wquad (gradTensor i₀ R ψ) x.1 x'.1‖ ≤ (Fintype.card ↥X : ℝ) * ((Fintype.card ↥X : ℝ) *
        (4 * M / ρ ^ 2 * ((2 * (A * t)) ^ 2 * (N * (N * 40 * (σ * ε)) ^ 2)))) := by
    refine norm_sum_le_card _ fun x => ?_
    refine norm_sum_le_card _ fun x' => ?_
    rw [norm_mul]
    refine mul_le_mul (hok.norm_D2_basis_le hM _ _) ?_ (norm_nonneg _) (by positivity)
    refine (norm_wquad_le _ hGm x.1 x'.1).trans ?_
    have hl : (l1 (x.1 - x'.1) : ℝ) ≤ 2 * (A * t) := by
      have := l1_sub_le x.1 x'.1
      have h3 : (l1 (x.1 - x'.1) : ℝ) ≤ l1 x.1 + l1 x'.1 := by exact_mod_cast this
      have h4 := c.l1_le hX x.2
      have h5 := c.l1_le hX x'.2
      simp only [ht] at *
      linarith
    have hl0 : (0 : ℝ) ≤ l1 (x.1 - x'.1) := Nat.cast_nonneg _
    have : 0 ≤ (N : ℝ) * (N * 40 * (σ * ε)) ^ 2 := by positivity
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hl0 hl 2) this
  have h2 : ‖(1 / 4 : ℂ)‖ = 1 / 4 := by simp
  rw [h2, hcard] at *
  calc 1 / 4 * ‖∑ x : ↥X, ∑ x' : ↥X, tensB i₀ i₁ ν X (T.term X) x x' *
        wquad (gradTensor i₀ R ψ) x.1 x'.1‖
      ≤ 1 / 4 * ((X.card : ℝ) * ((X.card : ℝ) *
        (4 * M / ρ ^ 2 * ((2 * (A * t)) ^ 2 * (N * (N * 40 * (σ * ε)) ^ 2))))) :=
        mul_le_mul_of_nonneg_left h1 (by norm_num)
    _ = _ := by ring

theorem Ctx.tail_case (c : Ctx T i₀ i₁ ν ρ E₀ κ A K₀ Dom ψ b σ ε K₂ u R) {X : Finset (Site d)}
    (hX : X ∈ T.polys) :
    ‖T.term X (pack X ψ b) - T.term X (pack X (fun _ => ψ 0) b)
        - (1 / 2 : ℂ) * ∑ x : ↥X, tensA i₀ ν X (T.term X) x *
            (dot (ψ x.1) (ψ x.1) - dot (ψ 0) (ψ 0))
        + (1 / 4 : ℂ) * ∑ x : ↥X, ∑ x' : ↥X, tensB i₀ i₁ ν X (T.term X) x x' *
            wquad (gradTensor i₀ R ψ) x.1 x'.1‖ ≤
      tailBnd N A (E₀ * Real.exp (-κ * T.dist X)) ρ σ ε (1 + T.dist X) X.card := by
  have hd0 : 0 ≤ T.dist X := c.hyp.dist_nonneg X hX
  set t : ℝ := 1 + T.dist X with ht
  set M : ℝ := E₀ * Real.exp (-κ * T.dist X) with hMdef
  have hM0 : 0 ≤ M := by have := c.E0nn; positivity
  have hρ := c.ρpos
  have a1 : ‖T.term X (pack X ψ b)‖ ≤ M := c.hyp.bdd_dom X hX (ψ, b) c.dat.mem
  have a2 : ‖T.term X (pack X (fun _ => ψ 0) b)‖ ≤ M :=
    c.hyp.bdd_dom X hX ((fun _ => ψ 0), b) c.dat.mem_const
  have a3 := c.A_le hX
  have a4 := c.Lq_le hX
  have tri : ∀ a b c e : ℂ, ‖a - b - c + e‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ + ‖e‖ := by
    intro a b c e
    have h1 := norm_add_le (a - b - c) e
    have h2 := norm_sub_le (a - b) c
    have h3 := norm_sub_le a b
    linarith
  refine (tri _ _ _ _).trans ?_
  unfold tailBnd
  have e : (X.card : ℝ) * (M / ρ * (σ ^ 2 * ε)) + (X.card : ℝ) ^ 2 * (M / ρ ^ 2) *
      ((2 * (A * t)) ^ 2 * (N * (N * 40 * (σ * ε)) ^ 2)) =
      M * ((X.card : ℝ) * (σ ^ 2 * ε / ρ) + 6400 * N ^ 3 * A ^ 2 * (X.card : ℝ) ^ 2 * t ^ 2 *
        (σ * ε / ρ) ^ 2) := by
    field_simp
    ring
  linarith [a1, a2, a3, a4, e]

end Balaban.SmallField
