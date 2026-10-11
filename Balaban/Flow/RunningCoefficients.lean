/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Analysis.InfiniteProduct
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The running coefficients `β_k`, `ν_k` and their limits `γ_∞`, `δ_∞`

Balaban P4 Section 5, (5.28)-(5.33), (H.6), and P9 (4.18) (p. 519).  The unknown `ξ^{(k)} ∈ ℂ³`
(`Fin 3 → ℂ`, components `ξ₁ = 0`, `ξ₂ = 1`, `ξ₃ = 2`) is the solution of step `k → k + 1`
(P4 Prop 5.1).  The running coefficients obey P4 (5.28):

* `betaSeq`: `β_{k+1} = β_k L^{d-2}/(1 + ξ₃^{(k)})`;
* `nuSeq`: `ν_{k+1} = ν_k L² (1 + ξ₃^{(k)})/(1 + ξ₂^{(k)})` (`ν = v` of P4).

Hypothesis (the second half of P4 (5.31)): `|ξ^{(k)}|_∞ ≤ (c₈/4) q^{k+1}`, `q = L^{-2γ}`
(`rate L γ`).  We assume `c₈ q ≤ 1 - q` (that is `c₈ ≤ L^{2γ} - 1`; `c₈` is arbitrarily small).

* `betaSeq_eq`, `nuSeq_eq`: `β_k = β L^{k(d-2)} γ_k`, `ν_k = ν L^{2k} δ_k` (P4 (H.6)), with
  `γ_k = ∏_{j<k} (1 + ξ₃^{(j)})⁻¹`, `δ_k = ∏_{j<k} (1 + ξ₃^{(j)})/(1 + ξ₂^{(j)})`;
* `norm_gammaSeq_le` etc.: `γ_k^{±1}, δ_k^{±1} ≤ exp (c₈ Σ_{1 ≤ j ≤ k} q^j)` (P4 (H.6), (5.32));
* `exists_gamma_infty`: the limits `γ_∞`, `δ_∞` exist, `|γ_∞ - 1| ≤ c₈ q/(2(1-q))` (P4 (5.33): the
  constant `C = q/(2(1-q))`), and satisfy the bounds (5.32) with `k + 1` replaced by `∞`;
* `norm_inv_betaSeq_sub_le`: `β_j⁻¹ = (β γ_∞)⁻¹ L^{-j(d-2)} + O(β⁻¹) L^{-j(d-2+2γ)}` (P9 (4.18)),
  the error being bounded by `C' c₈ ‖β⁻¹‖ L^{-j(d-2+2γ)}` with `C'` depending only on `L, γ`.
-/

@[expose] public section

open Finset Filter Topology

namespace Balaban.Flow

/-- The rate `q = L^{-2γ}`. -/
noncomputable def rate (L γ : ℝ) : ℝ := L ^ (-(2 * γ))

theorem rate_pos {L : ℝ} (hL : 0 < L) (γ : ℝ) : 0 < rate L γ := Real.rpow_pos_of_pos hL _

theorem rate_lt_one {L γ : ℝ} (hL : 1 < L) (hγ : 0 < γ) : rate L γ < 1 :=
  Real.rpow_lt_one_of_one_lt_of_neg hL (by linarith)

theorem rate_pow {L : ℝ} (hL : 0 < L) (γ : ℝ) (j : ℕ) : rate L γ ^ j = L ^ (-(2 * γ * j)) := by
  rw [rate, ← Real.rpow_natCast, ← Real.rpow_mul hL.le]
  congr 1; ring

/-- `(L^{j(d-2)})⁻¹ q^j = L^{-j(d-2+2γ)}`. -/
theorem inv_pow_mul_rate_pow {L : ℝ} (hL : 0 < L) (γ : ℝ) (d j : ℕ) :
    (L ^ (j * (d - 2)))⁻¹ * rate L γ ^ j = L ^ (-(j * (((d - 2 : ℕ) : ℝ) + 2 * γ))) := by
  rw [rate_pow hL, ← Real.rpow_natCast, ← Real.rpow_neg hL.le, ← Real.rpow_add hL]
  congr 1
  push_cast
  ring

section Sequences

variable (L : ℝ) (d : ℕ) (ξ : ℕ → Fin 3 → ℂ)

/-- `β_{k+1} = β_k L^{d-2}/(1 + ξ₃^{(k)})` (P4 (5.28)). -/
noncomputable def betaSeq (β : ℂ) : ℕ → ℂ
  | 0 => β
  | k + 1 => betaSeq β k * (L : ℂ) ^ (d - 2) / (1 + ξ k 2)

/-- `ν_{k+1} = ν_k L² (1 + ξ₃^{(k)})/(1 + ξ₂^{(k)})` (P4 (5.28)). -/
noncomputable def nuSeq (ν : ℂ) : ℕ → ℂ
  | 0 => ν
  | k + 1 => nuSeq ν k * (L : ℂ) ^ 2 * (1 + ξ k 2) / (1 + ξ k 1)

/-- `γ_k = ∏_{j<k} (1 + ξ₃^{(j)})⁻¹`. -/
noncomputable def gammaSeq (k : ℕ) : ℂ := ∏ j ∈ range k, (1 + ξ j 2)⁻¹

/-- `δ_k = ∏_{j<k} (1 + ξ₃^{(j)})/(1 + ξ₂^{(j)})`. -/
noncomputable def deltaSeq (k : ℕ) : ℂ := ∏ j ∈ range k, ((1 + ξ j 2) / (1 + ξ j 1))

/-- `β_k = β L^{k(d-2)} γ_k` (P4 (H.6)). -/
theorem betaSeq_eq (β : ℂ) (k : ℕ) :
    betaSeq L d ξ β k = β * (L : ℂ) ^ (k * (d - 2)) * gammaSeq ξ k := by
  induction k with
  | zero => simp [betaSeq, gammaSeq]
  | succ k ih =>
    rw [betaSeq, ih]
    simp only [gammaSeq, prod_range_succ, Nat.succ_mul, pow_add]
    ring

/-- `ν_k = ν L^{2k} δ_k` (P4 (H.6)). -/
theorem nuSeq_eq (ν : ℂ) (k : ℕ) :
    nuSeq L ξ ν k = ν * (L : ℂ) ^ (2 * k) * deltaSeq ξ k := by
  induction k with
  | zero => simp [nuSeq, deltaSeq]
  | succ k ih =>
    rw [nuSeq, ih]
    simp only [deltaSeq, prod_range_succ, Nat.mul_succ, pow_add]
    ring

end Sequences

section Bounds

variable {ξ : ℕ → Fin 3 → ℂ} {q c₈ : ℝ}

/-- The partial sums `Σ_{1 ≤ j ≤ k} q^j`. -/
noncomputable def ratePartialSum (q : ℝ) (k : ℕ) : ℝ := ∑ j ∈ range k, q ^ (j + 1)

theorem ratePartialSum_le (hq0 : 0 ≤ q) (hq1 : q < 1) (k : ℕ) :
    ratePartialSum q k ≤ q / (1 - q) := by
  have hs := (summable_geometric_of_lt_one hq0 hq1).sum_le_tsum (range k) (fun j _ => by positivity)
  rw [tsum_geometric_of_lt_one hq0 hq1] at hs
  have : ratePartialSum q k = q * ∑ j ∈ range k, q ^ j := by
    rw [ratePartialSum, mul_sum]; exact sum_congr rfl fun j _ => by ring
  rw [this, div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_left hs hq0

theorem norm_one_add_le {x : ℂ} : ‖1 + x‖ ≤ Real.exp (2 * ‖x‖) := by
  calc ‖1 + x‖ ≤ ‖(1 : ℂ)‖ + ‖x‖ := norm_add_le _ _
    _ ≤ Real.exp ‖x‖ := by rw [norm_one]; exact Real.add_one_le_exp _ |>.trans_eq' (by ring)
    _ ≤ Real.exp (2 * ‖x‖) := Real.exp_le_exp.mpr (by linarith [norm_nonneg x])

theorem norm_inv_one_add_le {x : ℂ} (hx : ‖x‖ ≤ 1 / 2) :
    ‖(1 + x)⁻¹‖ ≤ Real.exp (2 * ‖x‖) := by
  have h1 : 1 - ‖x‖ ≤ ‖1 + x‖ := by
    have := norm_sub_norm_le (1 : ℂ) (-x)
    simpa [sub_neg_eq_add] using this
  have hpos : 0 < 1 - ‖x‖ := by linarith
  rw [norm_inv]
  refine (inv_anti₀ hpos h1).trans ?_
  rw [inv_eq_one_div, div_le_iff₀ hpos]
  have := Real.add_one_le_exp (2 * ‖x‖)
  nlinarith [mul_nonneg (sub_nonneg.mpr this) hpos.le,
    mul_nonneg (norm_nonneg x) (by linarith : (0 : ℝ) ≤ 1 - 2 * ‖x‖)]

theorem norm_div_one_add_le {x y : ℂ} {w : ℝ} (hx : ‖x‖ ≤ w) (hy : ‖y‖ ≤ w) (hw : w ≤ 1 / 2) :
    ‖(1 + x) / (1 + y)‖ ≤ Real.exp (4 * w) := by
  rw [div_eq_mul_inv, norm_mul]
  have h1 := norm_one_add_le (x := x)
  have h2 := norm_inv_one_add_le (x := y) (by linarith)
  calc ‖1 + x‖ * ‖(1 + y)⁻¹‖ ≤ Real.exp (2 * w) * Real.exp (2 * w) :=
        mul_le_mul (h1.trans (Real.exp_le_exp.mpr (by linarith)))
          (h2.trans (Real.exp_le_exp.mpr (by linarith))) (norm_nonneg _) (Real.exp_pos _).le
    _ = Real.exp (4 * w) := by rw [← Real.exp_add]; ring_nf

theorem norm_prod_le_exp_sum {a : ℕ → ℂ} {b : ℕ → ℝ} (h : ∀ j, ‖a j‖ ≤ Real.exp (b j)) (k : ℕ) :
    ‖∏ j ∈ range k, a j‖ ≤ Real.exp (∑ j ∈ range k, b j) := by
  rw [Real.exp_sum]
  exact (Finset.norm_prod_le _ _).trans (Finset.prod_le_prod₀ (fun j _ => norm_nonneg (a j)) (fun j _ => h j))

/-- Standing hypotheses: `q ∈ [0,1)`, `c₈ ≥ 0`, `c₈ q ≤ 1 - q`, `|ξ^{(k)}| ≤ (c₈/4) q^{k+1}`. -/
theorem norm_comp_le (hξ : ∀ k, ‖ξ k‖ ≤ c₈ / 4 * q ^ (k + 1)) (k : ℕ) (i : Fin 3) :
    ‖ξ k i‖ ≤ c₈ / 4 * q ^ (k + 1) := (norm_le_pi_norm (ξ k) i).trans (hξ k)

theorem norm_le_quarter (hq0 : 0 ≤ q) (hq1 : q < 1) (hc : 0 ≤ c₈) (hs : c₈ * q ≤ 1 - q)
    (hξ : ∀ k, ‖ξ k‖ ≤ c₈ / 4 * q ^ (k + 1)) (k : ℕ) : ‖ξ k‖ ≤ 1 / 4 := by
  refine (hξ k).trans ?_
  have : q ^ (k + 1) ≤ q := by
    rw [pow_succ']
    exact mul_le_of_le_one_right hq0 (pow_le_one₀ hq0 hq1.le)
  have h2 : c₈ * q ^ (k + 1) ≤ 1 := by nlinarith [mul_le_mul_of_nonneg_left this hc]
  linarith

theorem sum_four_norm_le (hξ : ∀ k, ‖ξ k‖ ≤ c₈ / 4 * q ^ (k + 1)) (k : ℕ) :
    ∑ j ∈ range k, 4 * ‖ξ j‖ ≤ c₈ * ratePartialSum q k := by
  rw [ratePartialSum, mul_sum]
  refine sum_le_sum fun j _ => ?_
  have := hξ j
  linarith

/-- **(H.6), (5.32)**: `γ_k^{±1}, δ_k^{±1} ≤ exp (c₈ Σ_{1≤j≤k} q^j)`. -/
theorem norm_gammaSeq_le (hq0 : 0 ≤ q) (hq1 : q < 1) (hc : 0 ≤ c₈) (hs : c₈ * q ≤ 1 - q)
    (hξ : ∀ k, ‖ξ k‖ ≤ c₈ / 4 * q ^ (k + 1)) (k : ℕ) :
    ‖gammaSeq ξ k‖ ≤ Real.exp (c₈ * ratePartialSum q k) ∧
    ‖(gammaSeq ξ k)⁻¹‖ ≤ Real.exp (c₈ * ratePartialSum q k) ∧
    ‖deltaSeq ξ k‖ ≤ Real.exp (c₈ * ratePartialSum q k) ∧
    ‖(deltaSeq ξ k)⁻¹‖ ≤ Real.exp (c₈ * ratePartialSum q k) := by
  have hq4 := norm_le_quarter hq0 hq1 hc hs hξ
  have hsum := sum_four_norm_le hξ k
  have hnn : ∀ j, 0 ≤ ‖ξ j‖ := fun j => norm_nonneg _
  have c2 : ∀ j, ‖ξ j 2‖ ≤ ‖ξ j‖ := fun j => norm_le_pi_norm _ 2
  have c1 : ∀ j, ‖ξ j 1‖ ≤ ‖ξ j‖ := fun j => norm_le_pi_norm _ 1
  have mono : ∀ b : ℝ, b ≤ ∑ j ∈ range k, 4 * ‖ξ j‖ → Real.exp b ≤ Real.exp (c₈ * ratePartialSum q k) :=
    fun b hb => Real.exp_le_exp.mpr (hb.trans hsum)
  have sum2 : ∑ j ∈ range k, 2 * ‖ξ j‖ ≤ ∑ j ∈ range k, 4 * ‖ξ j‖ :=
    sum_le_sum fun j _ => by linarith [hnn j]
  have hw : ∀ j, ‖ξ j‖ ≤ 1 / 2 := fun j => (hq4 j).trans (by norm_num)
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine (norm_prod_le_exp_sum (b := fun j => 2 * ‖ξ j‖) (fun j => ?_) k).trans (mono _ sum2)
    exact (norm_inv_one_add_le ((c2 j).trans (hw j))).trans
      (Real.exp_le_exp.mpr (by linarith [c2 j]))
  · rw [gammaSeq, ← Finset.prod_inv_distrib]
    simp only [inv_inv]
    refine (norm_prod_le_exp_sum (b := fun j => 2 * ‖ξ j‖) (fun j => ?_) k).trans (mono _ sum2)
    exact (norm_one_add_le).trans
      (Real.exp_le_exp.mpr (by linarith [c2 j]))
  · refine (norm_prod_le_exp_sum (b := fun j => 4 * ‖ξ j‖) (fun j => ?_) k).trans (mono _ le_rfl)
    exact norm_div_one_add_le (c2 j) (c1 j) (hw j)
  · rw [deltaSeq, ← Finset.prod_inv_distrib]
    simp only [inv_div]
    refine (norm_prod_le_exp_sum (b := fun j => 4 * ‖ξ j‖) (fun j => ?_) k).trans (mono _ le_rfl)
    exact norm_div_one_add_le (c1 j) (c2 j) (hw j)

end Bounds

section Limits

variable {ξ : ℕ → Fin 3 → ℂ} {q c₈ : ℝ}

theorem ne_zero_of_norm_sub_one_le {x : ℂ} (h : ‖x - 1‖ ≤ 1 / 2) : x ≠ 0 := by
  rintro rfl
  simp at h
  linarith

theorem gammaSeq_ne_zero (hq0 : 0 ≤ q) (hq1 : q < 1) (hc : 0 ≤ c₈) (hs : c₈ * q ≤ 1 - q)
    (hξ : ∀ k, ‖ξ k‖ ≤ c₈ / 4 * q ^ (k + 1)) (k : ℕ) : gammaSeq ξ k ≠ 0 := by
  rw [gammaSeq, Finset.prod_ne_zero_iff]
  intro j _
  refine inv_ne_zero ?_
  intro h
  have h1 : ‖ξ j 2‖ ≤ 1 / 4 := (norm_le_pi_norm (ξ j) 2).trans (norm_le_quarter hq0 hq1 hc hs hξ j)
  have : ξ j 2 = -1 := by linear_combination h
  rw [this] at h1
  simp at h1
  linarith

theorem deltaSeq_eq (k : ℕ) :
    deltaSeq ξ k = (gammaSeq ξ k)⁻¹ * ∏ j ∈ range k, (1 + ξ j 1)⁻¹ := by
  rw [deltaSeq, gammaSeq, ← Finset.prod_inv_distrib]
  simp only [inv_inv]
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun j _ => by rw [div_eq_mul_inv]

/-- **Limits `γ_∞`, `δ_∞`** (P4 (5.33)): `γ_k → γ_∞`, `δ_k → δ_∞`, `|γ_∞ - 1| ≤ c₈ q/(2(1-q))`,
`|γ_k - γ_∞| ≤ c₈ q^{k+1}/(2(1-q))`, and the bounds (5.32) at `k = ∞`. -/
theorem exists_gamma_infty (hq0 : 0 ≤ q) (hq1 : q < 1) (hc : 0 ≤ c₈) (hs : c₈ * q ≤ 1 - q)
    (hξ : ∀ k, ‖ξ k‖ ≤ c₈ / 4 * q ^ (k + 1)) :
    ∃ γ δ : ℂ, Tendsto (gammaSeq ξ) atTop (𝓝 γ) ∧ Tendsto (deltaSeq ξ) atTop (𝓝 δ) ∧
      ‖γ - 1‖ ≤ c₈ * q / (2 * (1 - q)) ∧
      (∀ j, ‖gammaSeq ξ j - γ‖ ≤ c₈ * q ^ (j + 1) / (2 * (1 - q))) ∧ γ ≠ 0 ∧
      ‖γ‖ ≤ Real.exp (c₈ * (q / (1 - q))) ∧ ‖γ⁻¹‖ ≤ Real.exp (c₈ * (q / (1 - q))) ∧
      ‖δ‖ ≤ Real.exp (c₈ * (q / (1 - q))) ∧ ‖δ⁻¹‖ ≤ Real.exp (c₈ * (q / (1 - q))) := by
  have hq : 0 < 1 - q := by linarith
  set c := c₈ * q / 4 with hcdef
  have hc0 : 0 ≤ c := by positivity
  have hcs : c ≤ (1 - q) / 4 := by rw [hcdef]; linarith
  have hξ' : ∀ i : Fin 3, ∀ k, ‖ξ k i‖ ≤ c * q ^ k := fun i k =>
    (norm_comp_le hξ k i).trans (le_of_eq (by rw [hcdef, pow_succ]; ring))
  obtain ⟨γ, hT, h1, h2⟩ := Balaban.Analysis.exists_tendsto_prod_inv_one_add
    (ξ := fun k => ξ k 2) hq0 hq1 hc0 (hξ' 2) hcs
  obtain ⟨γ', hT', h1', -⟩ := Balaban.Analysis.exists_tendsto_prod_inv_one_add
    (ξ := fun k => ξ k 1) hq0 hq1 hc0 (hξ' 1) hcs
  have hTγ : Tendsto (gammaSeq ξ) atTop (𝓝 γ) := (tendsto_add_atTop_iff_nat 1).mp hT
  have hTγ' : Tendsto (fun k => ∏ j ∈ range k, (1 + ξ j 1)⁻¹) atTop (𝓝 γ') :=
    (tendsto_add_atTop_iff_nat 1).mp hT'
  have e2c : 2 * c / (1 - q) = c₈ * q / (2 * (1 - q)) := by rw [hcdef]; field_simp; ring
  have hγ1 : ‖γ - 1‖ ≤ c₈ * q / (2 * (1 - q)) := by rw [← e2c]; exact h1
  have hhalf : c₈ * q / (2 * (1 - q)) ≤ 1 / 2 := by
    rw [div_le_iff₀ (by positivity)]; linarith
  have hγne : γ ≠ 0 := ne_zero_of_norm_sub_one_le (hγ1.trans hhalf)
  have hγ'ne : γ' ≠ 0 :=
    ne_zero_of_norm_sub_one_le ((show ‖γ' - 1‖ ≤ c₈ * q / (2 * (1 - q)) by
      rw [← e2c]; exact h1').trans hhalf)
  have hTδ : Tendsto (deltaSeq ξ) atTop (𝓝 (γ⁻¹ * γ')) := by
    have := (hTγ.inv₀ hγne).mul hTγ'
    refine this.congr fun k => ?_
    rw [deltaSeq_eq]
  have hδne : γ⁻¹ * γ' ≠ 0 := mul_ne_zero (inv_ne_zero hγne) hγ'ne
  have hB : ∀ k, c₈ * ratePartialSum q k ≤ c₈ * (q / (1 - q)) := fun k =>
    mul_le_mul_of_nonneg_left (ratePartialSum_le hq0 hq1 k) hc
  have hb := fun k => norm_gammaSeq_le hq0 hq1 hc hs hξ k
  have lim : ∀ {u : ℕ → ℂ} {x : ℂ}, Tendsto u atTop (𝓝 x) →
      (∀ k, ‖u k‖ ≤ Real.exp (c₈ * (q / (1 - q)))) → ‖x‖ ≤ Real.exp (c₈ * (q / (1 - q))) :=
    fun hu hbd => le_of_tendsto hu.norm (Eventually.of_forall hbd)
  refine ⟨γ, γ⁻¹ * γ', hTγ, hTδ, hγ1, fun j => ?_, hγne, ?_, ?_, ?_, ?_⟩
  · rcases j with _ | k
    · simpa [gammaSeq, norm_sub_rev] using hγ1
    · have := h2 k
      have e : 2 * c * q ^ (k + 1) / (1 - q) = c₈ * q ^ (k + 1 + 1) / (2 * (1 - q)) := by
        rw [hcdef]; field_simp; ring
      rw [e] at this
      exact this
  · exact lim hTγ fun k => (hb k).1.trans (Real.exp_le_exp.mpr (hB k))
  · exact lim (hTγ.inv₀ hγne) fun k => (hb k).2.1.trans (Real.exp_le_exp.mpr (hB k))
  · exact lim hTδ fun k => (hb k).2.2.1.trans (Real.exp_le_exp.mpr (hB k))
  · exact lim (hTδ.inv₀ hδne) fun k => (hb k).2.2.2.trans (Real.exp_le_exp.mpr (hB k))

/-- **Asymptotics of the inverse coupling** (P9 (4.18), p. 519):
`β_j⁻¹ = (β γ_∞)⁻¹ L^{-j(d-2)} + O(β⁻¹) L^{-j(d-2)} q^j`; here `q = L^{-2γ}` in the application
(`inv_pow_mul_rate_pow`), and the implied constant is `e² c₈ q/(2(1-q))`, independent of `β`. -/
theorem exists_inv_betaSeq_asymptotics {L : ℝ} (hL : 0 < L) (d : ℕ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hc : 0 ≤ c₈) (hs : c₈ * q ≤ 1 - q) (hξ : ∀ k, ‖ξ k‖ ≤ c₈ / 4 * q ^ (k + 1)) :
    ∃ γ : ℂ, Tendsto (gammaSeq ξ) atTop (𝓝 γ) ∧ ‖γ - 1‖ ≤ c₈ * q / (2 * (1 - q)) ∧
      ∀ (β : ℂ) (j : ℕ),
        ‖(betaSeq L d ξ β j)⁻¹ - (β * γ)⁻¹ * ((L : ℂ) ^ (j * (d - 2)))⁻¹‖ ≤
          Real.exp 2 * (c₈ * q / (2 * (1 - q))) * ‖β⁻¹‖ * ((L ^ (j * (d - 2)))⁻¹ * q ^ j) := by
  have hq : 0 < 1 - q := by linarith
  obtain ⟨γ, -, hT, -, h1, h2, hne, -, hinv, -, -⟩ := exists_gamma_infty hq0 hq1 hc hs hξ
  refine ⟨γ, hT, h1, fun β j => ?_⟩
  have hgj := gammaSeq_ne_zero hq0 hq1 hc hs hξ j
  have hb := (norm_gammaSeq_le hq0 hq1 hc hs hξ j).2.1
  have h3 : c₈ * (q / (1 - q)) ≤ 1 := by
    rw [← mul_div_assoc, div_le_one hq]; linarith
  have hB : c₈ * ratePartialSum q j ≤ 1 :=
    (mul_le_mul_of_nonneg_left (ratePartialSum_le hq0 hq1 j) hc).trans h3
  have hb' : ‖(gammaSeq ξ j)⁻¹‖ ≤ Real.exp 1 := hb.trans (Real.exp_le_exp.mpr hB)
  have hinv' : ‖γ⁻¹‖ ≤ Real.exp 1 := hinv.trans (Real.exp_le_exp.mpr h3)
  have hLn : ‖((L : ℂ) ^ (j * (d - 2)))⁻¹‖ = (L ^ (j * (d - 2)))⁻¹ := by
    rw [norm_inv, norm_pow, Complex.norm_of_nonneg hL.le]
  have key : (betaSeq L d ξ β j)⁻¹ - (β * γ)⁻¹ * ((L : ℂ) ^ (j * (d - 2)))⁻¹ =
      β⁻¹ * ((L : ℂ) ^ (j * (d - 2)))⁻¹ * ((gammaSeq ξ j)⁻¹ - γ⁻¹) := by
    rw [betaSeq_eq, mul_inv, mul_inv, mul_inv]; ring
  have hdiff : (gammaSeq ξ j)⁻¹ - γ⁻¹ = (γ - gammaSeq ξ j) * ((gammaSeq ξ j)⁻¹ * γ⁻¹) := by
    field_simp
  have hE := h2 j
  rw [key, hdiff, norm_mul, norm_mul, norm_mul, norm_mul, hLn, norm_sub_rev]
  have hE' : ‖gammaSeq ξ j - γ‖ ≤ c₈ * q / (2 * (1 - q)) * q ^ j := by
    refine hE.trans (le_of_eq ?_); rw [pow_succ]; ring
  have hprod : ‖(gammaSeq ξ j)⁻¹‖ * ‖γ⁻¹‖ ≤ Real.exp 2 := by
    calc _ ≤ Real.exp 1 * Real.exp 1 :=
          mul_le_mul hb' hinv' (norm_nonneg _) (Real.exp_pos _).le
      _ = Real.exp 2 := by rw [← Real.exp_add]; norm_num
  have h0 : 0 ≤ (L ^ (j * (d - 2)))⁻¹ := by positivity
  calc ‖β⁻¹‖ * (L ^ (j * (d - 2)))⁻¹ * (‖gammaSeq ξ j - γ‖ * (‖(gammaSeq ξ j)⁻¹‖ * ‖γ⁻¹‖))
      ≤ ‖β⁻¹‖ * (L ^ (j * (d - 2)))⁻¹ *
        ((c₈ * q / (2 * (1 - q)) * q ^ j) * Real.exp 2) :=
        mul_le_mul_of_nonneg_left (mul_le_mul hE' hprod (by positivity) (by positivity))
          (by positivity)
    _ = _ := by ring

end Limits

end Balaban.Flow
