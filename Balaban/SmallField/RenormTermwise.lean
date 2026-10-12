/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.SmallField.RenormTermwiseAnalytic

/-!
# Lemma 3.2 (termwise irrelevance): the decomposition of the energy

`energy_sub_Aterm_eq_tsum_Itw`: under `PremisesTerm`, `SumConds` and the data (Σ1),
`𝓔(y; ψ, b) - A_y(ψ) = Σ_{X∋y} I(y,X; ψ, b)`, with all the series summable.  This is the sum of
the definition `I = 𝓔 - T - A - Φ` with the cancellations (i).

Index of the statements of Lemma 3.2 (FLUCTUATION.md §3.2):

* the premises: `PremisesTerm`, `SumConds` (`RenormTermwiseDefs`);
* the objects: `Ttw` (`T_X`), `Ax` (`A_{y,X}`), `Phitw` (`Φ_{y,X}`), `Itw` (`I(y,X)`);
* (i): `Ttw_tsum_zero`, `Phitw_tsum_zero`, `Ax_tsum_eq`, `Aterm_torus_sum_tw` (`RenormTermwiseSum`);
* (ii): `Itw_congr`, `Ttw_congr`, `Ax_congr`, `Phitw_congr` (locality), `Itw_rot` and its
  relatives (`O(N)`), `Itw_analytic` and its relatives (`RenormTermwiseProps`,
  `RenormTermwiseAnalytic`);
* (iii): `termwise_irrelevant`, `termwise_irrelevant_scaled` (`RenormTermwiseIrrel`).
-/

@[expose] public section

open Metric Set Matrix

namespace Balaban.SmallField

variable {d N : ℕ}

section Decomp

variable {T : TermFamily d N} {i₀ i₁ : Fin N} {ν ρ E₀ κ A K₀ : ℝ}
  {Dom : Set ((Site d → Spin N) × Spin N)}

theorem Ax_summable (hP : PremisesTerm T i₀ i₁ ν ρ E₀ κ A K₀ Dom) (hρ : 0 < ρ) (hE0 : 0 ≤ E₀)
    {ψ : Site d → Spin N} {b : Spin N} {σ ε K₂ : ℝ} (dat : DataHyp Dom ν σ ε K₂ ψ b) :
    Summable fun X : T.polys => Ax T i₀ ν ψ X.1 := by
  have hsum : Summable fun X : T.polys => wt κ X.1 (T.dist X.1) := hP.count_summable
  have hga : ∀ x, ‖dot (ψ x) (ψ x) - dot (ψ 0) (ψ 0)‖ ≤ 2 * (σ ^ 2 * ε) := by
    intro x
    have h1 := dat.sq x
    have h2 := dat.sq 0
    calc ‖dot (ψ x) (ψ x) - dot (ψ 0) (ψ 0)‖
        = ‖(dot (ψ x) (ψ x) - 1) - (dot (ψ 0) (ψ 0) - 1)‖ := by ring_nf
      _ ≤ ‖dot (ψ x) (ψ x) - 1‖ + ‖dot (ψ 0) (ψ 0) - 1‖ := norm_sub_le _ _
      _ ≤ 2 * (σ ^ 2 * ε) := by linarith
  refine Summable.of_norm_bounded (hsum.mul_left (E₀ / ρ * (σ ^ 2 * ε))) fun X => ?_
  have hok := hP.termOK hρ X.2
  have hM : ∀ y ∈ ball (refPt i₀ ν X.1) ρ, ‖T.term X.1 y‖ ≤ E₀ * Real.exp (-κ * T.dist X.1) :=
    fun y hy => hP.bdd_tube X.1 X.2 y (ball_subset_tube i₀ ν ρ X.1 hy)
  have hw := wt_ge (κ := κ) X.1 (hP.dist_nonneg X.1 X.2)
    (Finset.card_pos.mpr ⟨0, hP.zero_mem X.1 X.2⟩) 1 0 (by norm_num) (by norm_num)
  simp only [pow_one, pow_zero, mul_one] at hw
  set M : ℝ := E₀ * Real.exp (-κ * T.dist X.1) with hMdef
  have hM0 : 0 ≤ M := by positivity
  unfold Ax
  rw [norm_mul]
  have h1 : ‖∑ x : ↥X.1, tensA i₀ ν X.1 (T.term X.1) x *
      (dot (ψ x.1) (ψ x.1) - dot (ψ 0) (ψ 0))‖ ≤
      (Fintype.card ↥X.1 : ℝ) * (M / ρ * (2 * (σ ^ 2 * ε))) := by
    refine norm_sum_le_card _ fun x => ?_
    rw [norm_mul]
    exact mul_le_mul (hok.norm_tensA_le hM x) (hga x.1) (norm_nonneg _) (by positivity)
  have h2 : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by simp
  rw [h2, Fintype.card_coe] at *
  have hτ : 0 ≤ σ ^ 2 * ε := by
    have := dat.sq 0
    exact le_trans (norm_nonneg _) this
  calc 1 / 2 * ‖∑ x : ↥X.1, tensA i₀ ν X.1 (T.term X.1) x *
        (dot (ψ x.1) (ψ x.1) - dot (ψ 0) (ψ 0))‖
      ≤ 1 / 2 * ((X.1.card : ℝ) * (M / ρ * (2 * (σ ^ 2 * ε)))) :=
        mul_le_mul_of_nonneg_left h1 (by norm_num)
    _ = ((X.1.card : ℝ) * M) / ρ * (σ ^ 2 * ε) := by ring
    _ ≤ (E₀ * wt κ X.1 (T.dist X.1)) / ρ * (σ ^ 2 * ε) := by
        have : (X.1.card : ℝ) * M ≤ E₀ * wt κ X.1 (T.dist X.1) := by
          calc (X.1.card : ℝ) * M = E₀ * ((X.1.card : ℝ) * Real.exp (-κ * T.dist X.1)) := by
                rw [hMdef]; ring
            _ ≤ _ := mul_le_mul_of_nonneg_left hw hE0
        gcongr
    _ = _ := by ring

/-- **Lemma 3.2, the sum of the termwise decomposition**: `𝓔(y;ψ,b) - A_y(ψ) = Σ_X I(y,X;ψ,b)`. -/
theorem energy_sub_Aterm_eq_tsum_Itw (hP : PremisesTerm T i₀ i₁ ν ρ E₀ κ A K₀ Dom)
    (hS : SumConds T i₀ i₁ ν) (hρ : 0 < ρ) (hE0 : 0 ≤ E₀) (hA : 0 ≤ A)
    {ψ : Site d → Spin N} {b : Spin N} {σ ε K₂ : ℝ} (dat : DataHyp Dom ν σ ε K₂ ψ b) :
    energy T ψ b - Aterm T i₀ ν ψ = ∑' X : T.polys, Itw T i₀ i₁ ν X.1 ψ b := by
  have hP' := hP.toPremises hS
  have hsum : Summable fun X : T.polys => wt κ X.1 (T.dist X.1) := hP.count_summable
  have hMle : ∀ X : T.polys, ‖T.term X.1 (pack X.1 ψ b)‖ ≤ E₀ * wt κ X.1 (T.dist X.1) := fun X => by
    have h1 := hP.bdd_dom X.1 X.2 (ψ, b) dat.mem
    have := wt_ge (κ := κ) X.1 (hP.dist_nonneg X.1 X.2)
      (Finset.card_pos.mpr ⟨0, hP.zero_mem X.1 X.2⟩) 0 0 (by norm_num) (by norm_num)
    simp only [pow_zero, one_mul] at this
    exact h1.trans ((mul_le_mul_of_nonneg_left this hE0))
  have S_e : Summable fun X : T.polys => T.term X.1 (pack X.1 ψ b) :=
    Summable.of_norm_bounded (hsum.mul_left E₀) hMle
  obtain ⟨S_v0, S_s, S_d⟩ := hP.summable_tensors hρ hE0
  have S_T : Summable fun X : T.polys => Ttw T i₀ ν X.1 ψ b :=
    (S_v0.add (S_s.mul_left (uInv ψ - 1))).add (S_d.mul_left (vInv ψ b - ν))
  have S_A := Ax_summable hP hρ hE0 dat
  have S_Φ : Summable fun X : T.polys => Phitw T i₀ i₁ ν X.1 ψ := by
    unfold Phitw
    exact (summable_sum fun μ _ => summable_sum fun μ' _ =>
      (Sx_summable hP' hρ hE0 hA μ μ').mul_left _).mul_left _
  have h : ∑' X : T.polys, Itw T i₀ i₁ ν X.1 ψ b =
      ∑' X : T.polys, T.term X.1 (pack X.1 ψ b) - ∑' X : T.polys, Ttw T i₀ ν X.1 ψ b -
        ∑' X : T.polys, Ax T i₀ ν ψ X.1 - ∑' X : T.polys, Phitw T i₀ i₁ ν X.1 ψ := by
    unfold Itw
    rw [Summable.tsum_sub ((S_e.sub S_T).sub S_A) S_Φ, Summable.tsum_sub (S_e.sub S_T) S_A,
      Summable.tsum_sub S_e S_T]
  rw [h, Ttw_tsum_zero hP hS hρ hE0, Phitw_tsum_zero hP hS hρ hE0 hA, Ax_tsum_eq]
  unfold energy
  ring

end Decomp

end Balaban.SmallField
