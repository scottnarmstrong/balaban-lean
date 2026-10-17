/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.LocalClassInherit
public import Balaban.Fluctuation.GeneralClassMatch
public import Balaban.Flow.RunningCoefficients
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Birth-mass domains of the old terms: the cumulated mass factor and the reduction

The old terms of the successor class keep the domain `Ξ^c_j(𝔹_j(X); 1, ε_j)` at the mass `μ_j` of
their birth (decision D2(b)).  The chart points of a later step lie in `Ξ^c_j(𝔹_j(X); C₀, ·)` at
the step mass `ν_k`.  This file proves the parts of the passage that follow from landed results.

* `physMass_birth_eq_prod`: the fine mass at step `j + i` is the fine mass at step `j` times the
  product of the factors `(1 + ξ₃)/(1 + ξ₂)` (P4 (5.28)), by `physMass_succ_renorm`.
* `norm_ratio_prod_sub_one_le`, `norm_ratio_prod_sub_one_le_geom`: under the landed form
  `‖ξ_n‖ ≤ (c₈/4) q^{n+1}` of P4 (5.31), the cumulated factor over `n ∈ [j, k)` is within
  `exp (3 c₈ q^{j+1} / (4 (1 - q))) - 1 = O(β⁻¹ q^{j+1})` of `1`.
* `xiDom_birth_of_massResponse`: the chart point of scale `C₀` lies in the birth-mass domain once
  the level-`j` mass response of `Ξ^c_j(·; 1, ·)` is available.  The mass response is **not**
  proved here: it is the hypothesis `hresp`, and it is the missing estimate (see
  `notes/phase1/D2B.md`).
-/

@[expose] public section

namespace Balaban.Fluctuation

open Finset Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Flow

/-! ### The cumulated mass factor -/

section Factor

/-- **The fine mass along the renormalized flow** (P4 (5.28)): if
`ν_{n+1} = ν_n L² (1 + x_n)/(1 + y_n)` then
`physMass (j + i) ν_{j+i} = physMass j ν_j · ∏_{n < i} (1 + x_{j+n})/(1 + y_{j+n})`. -/
theorem physMass_birth_eq_prod {L : ℕ} [NeZero L] (νs x y : ℕ → ℝ) (j : ℕ)
    (h : ∀ n, νs (n + 1) = νs n * (L : ℝ) ^ 2 * (1 + x n) / (1 + y n)) (i : ℕ) :
    Def6v2.physMass L (j + i) (νs (j + i)) =
      Def6v2.physMass L j (νs j) * ∏ n ∈ range i, ((1 + x (j + n)) / (1 + y (j + n))) := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [← add_assoc, h, Def6v2.physMass_succ_renorm, ih, prod_range_succ]
    ring

theorem norm_one_sub_div_le {u v : ℂ} {w : ℝ} (hu : ‖u‖ ≤ w) (hv : ‖v‖ ≤ w) (hw : w ≤ 1 / 4) :
    ‖(1 + u) / (1 + v) - 1‖ ≤ 3 * w := by
  have h1 : 1 - ‖v‖ ≤ ‖1 + v‖ := by
    have := norm_sub_norm_le (1 : ℂ) (-v)
    simpa [sub_neg_eq_add] using this
  have hw0 : 0 ≤ w := (norm_nonneg u).trans hu
  have hpos : 0 < ‖1 + v‖ := by linarith
  have hne : (1 + v) ≠ 0 := norm_pos_iff.1 hpos
  have e : (1 + u) / (1 + v) - 1 = (u - v) / (1 + v) := by field_simp; ring
  rw [e, norm_div, div_le_iff₀ hpos]
  have : ‖u - v‖ ≤ 2 * w := (norm_sub_le _ _).trans (by linarith)
  nlinarith

theorem norm_prod_sub_one_le_prod {ι : Type*} [DecidableEq ι] (s : Finset ι) (a : ι → ℂ)
    (x : ι → ℝ) (hx0 : ∀ i, 0 ≤ x i) (h : ∀ i ∈ s, ‖a i - 1‖ ≤ x i) :
    ‖∏ i ∈ s, a i - 1‖ ≤ ∏ i ∈ s, (1 + x i) - 1 := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [prod_insert hi, prod_insert hi]
    have ih' := ih (fun k hk => h k (mem_insert_of_mem hk))
    have hQ : 1 ≤ ∏ i ∈ s, (1 + x i) := by
      have := Finset.prod_le_prod₀ (s := s) (f := fun _ => (1 : ℝ)) (g := fun i => 1 + x i)
        (fun _ _ => zero_le_one) (fun k _ => by linarith [hx0 k])
      simpa using this
    have hP : ‖∏ i ∈ s, a i‖ ≤ ∏ i ∈ s, (1 + x i) := by
      have := norm_le_norm_add_norm_sub' (∏ i ∈ s, a i) 1
      have h2 := norm_sub_norm_le (∏ i ∈ s, a i) 1
      simp only [norm_one] at h2
      linarith
    have hai := h i (mem_insert_self i s)
    have e : a i * ∏ k ∈ s, a k - 1 = (a i - 1) * ∏ k ∈ s, a k + (∏ k ∈ s, a k - 1) := by ring
    rw [e]
    calc ‖(a i - 1) * ∏ k ∈ s, a k + (∏ k ∈ s, a k - 1)‖
        ≤ ‖a i - 1‖ * ‖∏ k ∈ s, a k‖ + ‖∏ k ∈ s, a k - 1‖ :=
          (norm_add_le _ _).trans (by rw [norm_mul])
      _ ≤ x i * ∏ k ∈ s, (1 + x k) + (∏ k ∈ s, (1 + x k) - 1) := by
          exact add_le_add (mul_le_mul hai hP (norm_nonneg _) (hx0 i)) ih'
      _ = (1 + x i) * ∏ k ∈ s, (1 + x k) - 1 := by ring

variable {ξ : ℕ → Fin 3 → ℂ} {q c₈ : ℝ}

/-- **The cumulated factor `∏_{n=j}^{k-1} (1 + ξ₃^{(n)})/(1 + ξ₂^{(n)})`** (`= δ_k/δ_j`) is close to
`1`: `‖· - 1‖ ≤ exp (3 Σ_{n ∈ [j,k)} ‖ξ_n‖) - 1`, when `‖ξ_n‖ ≤ 1/4`. -/
theorem norm_ratio_prod_sub_one_le (j k : ℕ) (hξ : ∀ n, ‖ξ n‖ ≤ 1 / 4) :
    ‖∏ n ∈ Ico j k, ((1 + ξ n 2) / (1 + ξ n 1)) - 1‖ ≤
      Real.exp (3 * ∑ n ∈ Ico j k, ‖ξ n‖) - 1 := by
  refine (norm_prod_sub_one_le_prod (Ico j k) _ (fun n => 3 * ‖ξ n‖)
    (fun n => by positivity) (fun n _ => ?_)).trans ?_
  · exact norm_one_sub_div_le ((norm_le_pi_norm (ξ n) 2)) ((norm_le_pi_norm (ξ n) 1)) (hξ n)
  · have : ∏ n ∈ Ico j k, (1 + 3 * ‖ξ n‖) ≤ ∏ n ∈ Ico j k, Real.exp (3 * ‖ξ n‖) :=
      Finset.prod_le_prod₀ (fun n _ => by positivity) (fun n _ => by
        linarith [Real.add_one_le_exp (3 * ‖ξ n‖)])
    rw [← Real.exp_sum, ← mul_sum] at this
    linarith

/-- The cumulated factor under the landed form `‖ξ_n‖ ≤ (c₈/4) q^{n+1}` of P4 (5.31):
`‖∏_{n=j}^{k-1} (1 + ξ₃)/(1 + ξ₂) - 1‖ ≤ exp (3 c₈ q^{j+1}/(4 (1-q))) - 1`. -/
theorem norm_ratio_prod_sub_one_le_geom (hq0 : 0 ≤ q) (hq1 : q < 1) (hc : 0 ≤ c₈)
    (hs : c₈ * q ≤ 1 - q) (hξ : ∀ n, ‖ξ n‖ ≤ c₈ / 4 * q ^ (n + 1)) (j k : ℕ) :
    ‖∏ n ∈ Ico j k, ((1 + ξ n 2) / (1 + ξ n 1)) - 1‖ ≤
      Real.exp (3 * (c₈ / 4 * (q ^ (j + 1) / (1 - q)))) - 1 := by
  refine (norm_ratio_prod_sub_one_le j k (norm_le_quarter hq0 hq1 hc hs hξ)).trans ?_
  have hq : 0 < 1 - q := by linarith
  have hgeo : ∑ n ∈ Ico j k, q ^ (n + 1) ≤ q ^ (j + 1) / (1 - q) := by
    rw [sum_Ico_eq_sum_range]
    have hsum := (summable_geometric_of_lt_one hq0 hq1).sum_le_tsum (range (k - j))
      (fun i _ => by positivity)
    rw [tsum_geometric_of_lt_one hq0 hq1] at hsum
    have : ∑ i ∈ range (k - j), q ^ (j + i + 1) = q ^ (j + 1) * ∑ i ∈ range (k - j), q ^ i := by
      rw [mul_sum]; exact sum_congr rfl fun i _ => by ring
    rw [this, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left hsum (by positivity)
  have : ∑ n ∈ Ico j k, ‖ξ n‖ ≤ c₈ / 4 * (q ^ (j + 1) / (1 - q)) := by
    calc ∑ n ∈ Ico j k, ‖ξ n‖ ≤ ∑ n ∈ Ico j k, c₈ / 4 * q ^ (n + 1) := sum_le_sum fun n _ => hξ n
      _ = c₈ / 4 * ∑ n ∈ Ico j k, q ^ (n + 1) := by rw [mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left hgeo (by positivity)
  have := Real.exp_le_exp.mpr (by linarith : 3 * ∑ n ∈ Ico j k, ‖ξ n‖ ≤
    3 * (c₈ / 4 * (q ^ (j + 1) / (1 - q))))
  linarith

/-- The mass of the running flow: `ν_k L^{-2k} = ν δ_k` and `δ_k = δ_j · ∏_{n ∈ [j,k)} …`. -/
theorem deltaSeq_eq_mul_prod_Ico {j k : ℕ} (hjk : j ≤ k) :
    deltaSeq ξ k = deltaSeq ξ j * ∏ n ∈ Ico j k, ((1 + ξ n 2) / (1 + ξ n 1)) := by
  unfold deltaSeq
  rw [prod_range_mul_prod_Ico _ hjk]

end Factor

/-! ### The reduction to the mass response -/

section Reduction

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}

/-- **Core of the birth-mass inclusion**: as `xiDom_birth_of_massResponse`, with the response
hypothesis `hresp` required only for the data that realize `D`. -/
theorem xiDom_birth_core {G : GeneratingSet d L (N₁ * L ^ m₁) k ϱ} {A : ℕ → ℝ}
    {ν μ C₀ e e₁ e' εj : ℝ} {j : ℕ} (hσ : 1 ≤ C₀) (hrad : C₀ ^ 2 * e ≤ e₁) (hee : e' ≤ εj)
    {D : BgData G N}
    (hresp : ∀ (Ψ₀ : Localization.CTorus d L N₁ m₁ k → Fin N → ℝ) (h₀ : Fin N → ℝ)
      (Ψ'' h'' : Localization.CTorus d L N₁ m₁ k → Fin N → ℂ),
      XiC G A ν j 1 e₁ Ψ₀ h₀ Ψ'' h'' → RealizesC D Ψ₀ h₀ Ψ'' h'' →
      XiC G A μ j 1 e' Ψ₀ h₀ Ψ'' h'')
    (hD : Localization.XiCData G A ν j C₀ e D) :
    Def6.XiDom G A μ j εj D.Ψ D.h := by
  obtain ⟨Ψ₀, h₀, Ψ'', h'', hxc, hR⟩ := hD
  have hR' : RealizesC D Ψ₀ h₀ (fun x i => D.Ψ x i - Ψ₀ x i) (fun x i => D.h x i - h₀ i) :=
    ⟨fun x hx i => by simp [hR.1 x hx i], fun x hx i => by simp [hR.2 x hx i]⟩
  refine ⟨Ψ₀, h₀, fun x i => D.Ψ x i - Ψ₀ x i, fun x i => D.h x i - h₀ i,
    fun x i => by ring, fun x i => by ring,
    Def6v2.xiC_mono_eps zero_le_one hee
      (hresp _ _ _ _ (xiC_rescale_of_agree hσ hrad (fun x hx i => ?_) (fun x hx i => ?_) hxc) hR')⟩
  · rw [hR.1 x hx i]; ring
  · rw [hR.2 x hx i]; ring

/-- **The chart points of scale `C₀` lie in the birth-mass domain, given the level-`j` mass
response** (decision D2(b)).  `hresp` is the missing estimate: the passage of `Ξ^c_j(·; 1, e)` from
the step mass `ν` to the birth mass `μ` at the cost `e ↦ e'`.  Hypotheses `hσ`, `hrad`, `hε` are the
scale `C₀ ≥ 1`, the radius `C₀² e ≤ e₁` and the room `e' ≤ ε_j` (DL-gap with the factor of the mass
response).  The conclusion is `XiDom` at the birth mass for the raw data of `D`. -/
theorem xiDom_birth_of_massResponse {G : GeneratingSet d L (N₁ * L ^ m₁) k ϱ} {A : ℕ → ℝ}
    {ν μ C₀ e e₁ e' εj : ℝ} {j : ℕ} (hσ : 1 ≤ C₀) (hrad : C₀ ^ 2 * e ≤ e₁) (hee : e' ≤ εj)
    (hresp : ∀ (Ψ₀ : Localization.CTorus d L N₁ m₁ k → Fin N → ℝ) (h₀ : Fin N → ℝ)
      (Ψ'' h'' : Localization.CTorus d L N₁ m₁ k → Fin N → ℂ),
      XiC G A ν j 1 e₁ Ψ₀ h₀ Ψ'' h'' → XiC G A μ j 1 e' Ψ₀ h₀ Ψ'' h'')
    {D : BgData G N} (hD : Localization.XiCData G A ν j C₀ e D) :
    Def6.XiDom G A μ j εj D.Ψ D.h :=
  xiDom_birth_core hσ hrad hee (fun _ _ _ _ hx _ => hresp _ _ _ _ hx) hD

end Reduction

end Balaban.Fluctuation
