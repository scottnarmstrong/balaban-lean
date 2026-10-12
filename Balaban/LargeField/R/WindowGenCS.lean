module

public import Balaban.Background.Composition
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The Cauchy-Schwarz step of Lemma III.2.3

* `weighted_cs`: `‖t₀ + ∑ w_s τ_s‖² ≤ (1/c₀ + ∑ w_s²/c_s)(c₀‖t₀‖² + ∑ c_s‖τ_s‖²)`;
* `block_dominates`: for a `k`-block `z` with leaf layers `n_s ∈ [1, k-1]` (`s` ranging over the
  `V = L^{kd}` sites of `z`) and the ideal composed weight `a_z⁻¹ = V⁻¹ ∑_s u_{k-n_s}`,
  `u_r = 1/a_r`, `a_r = compWeight L a₁ r`, the composed term plus the block terms of the leaves
  dominate the block term of the single-scale action, by (C1) (`compWeight_C1`).
-/

@[expose] public section

namespace Balaban.LargeField

open Balaban.Background Finset

section CS

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {ι : Type*}

/-- The weighted Cauchy-Schwarz inequality for a vector sum. -/
theorem weighted_cs (s : Finset ι) {c0 : ℝ} (hc0 : 0 < c0) (c w : ι → ℝ) (hc : ∀ i ∈ s, 0 < c i)
    (t0 : E) (τ : ι → E) :
    ‖t0 + ∑ i ∈ s, w i • τ i‖ ^ 2 ≤
      (1 / c0 + ∑ i ∈ s, w i ^ 2 / c i) * (c0 * ‖t0‖ ^ 2 + ∑ i ∈ s, c i * ‖τ i‖ ^ 2) := by
  set A := ‖t0‖ with hA
  set B := ∑ i ∈ s, |w i| * ‖τ i‖ with hB
  set W := ∑ i ∈ s, w i ^ 2 / c i with hW
  set C := ∑ i ∈ s, c i * ‖τ i‖ ^ 2 with hC
  have hA0 : 0 ≤ A := norm_nonneg _
  have hB0 : 0 ≤ B := Finset.sum_nonneg fun i _ => by positivity
  have hW0 : 0 ≤ W := Finset.sum_nonneg fun i hi => by have := hc i hi; positivity
  have hC0 : 0 ≤ C := Finset.sum_nonneg fun i hi => by have := hc i hi; positivity
  have h1 : ‖t0 + ∑ i ∈ s, w i • τ i‖ ≤ A + B := by
    refine (norm_add_le _ _).trans ?_
    gcongr
    refine (norm_sum_le _ _).trans ?_
    refine Finset.sum_le_sum fun i _ => ?_
    rw [norm_smul, Real.norm_eq_abs]
  have h2 : B ^ 2 ≤ W * C := by
    have := Finset.sum_mul_sq_le_sq_mul_sq s (fun i => |w i| / Real.sqrt (c i))
      (fun i => Real.sqrt (c i) * ‖τ i‖)
    have e1 : ∀ i ∈ s, |w i| / Real.sqrt (c i) * (Real.sqrt (c i) * ‖τ i‖) = |w i| * ‖τ i‖ := by
      intro i hi
      have := Real.sqrt_pos.2 (hc i hi)
      field_simp
    have e2 : ∀ i ∈ s, (|w i| / Real.sqrt (c i)) ^ 2 = w i ^ 2 / c i := by
      intro i hi
      rw [div_pow, Real.sq_sqrt (hc i hi).le, sq_abs]
    have e3 : ∀ i ∈ s, (Real.sqrt (c i) * ‖τ i‖) ^ 2 = c i * ‖τ i‖ ^ 2 := by
      intro i hi
      rw [mul_pow, Real.sq_sqrt (hc i hi).le]
    rw [Finset.sum_congr rfl e1, Finset.sum_congr rfl e2, Finset.sum_congr rfl e3] at this
    exact this
  have h3 : 2 * A * B ≤ C / c0 + c0 * W * A ^ 2 := by
    have hsq : (2 * A * B) ^ 2 ≤ (C / c0 + c0 * W * A ^ 2) ^ 2 := by
      have e : (C / c0 + c0 * W * A ^ 2) ^ 2 - (2 * A * B) ^ 2 =
          (C / c0 - c0 * W * A ^ 2) ^ 2 + 4 * A ^ 2 * (W * C - B ^ 2) := by
        field_simp
        ring
      have : 0 ≤ 4 * A ^ 2 * (W * C - B ^ 2) := by
        have := sub_nonneg.2 h2
        positivity
      nlinarith [sq_nonneg (C / c0 - c0 * W * A ^ 2)]
    have hr : 0 ≤ C / c0 + c0 * W * A ^ 2 := by positivity
    exact abs_le_of_sq_le_sq' hsq hr |>.2
  have h4 : (A + B) ^ 2 ≤ (1 / c0 + W) * (c0 * A ^ 2 + C) := by
    have e : (1 / c0 + W) * (c0 * A ^ 2 + C) = A ^ 2 + C / c0 + c0 * W * A ^ 2 + W * C := by
      field_simp
      ring
    rw [e]
    nlinarith
  calc ‖t0 + ∑ i ∈ s, w i • τ i‖ ^ 2 ≤ (A + B) ^ 2 := by gcongr
    _ ≤ _ := h4

end CS

section Block

variable {α : Type*} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem compWeight_pos {L : ℕ} (hL : 2 ≤ L) {a₁ : ℝ} (ha : 0 < a₁) {r : ℕ} (hr : 1 ≤ r) :
    0 < compWeight L a₁ r := by
  unfold compWeight
  have h2 : (2 : ℝ) ≤ L := by exact_mod_cast hL
  have h4 : (4 : ℝ) ≤ (L : ℝ) ^ 2 := by nlinarith
  have hr' : (L : ℝ) ^ 2 ≤ ((L : ℝ) ^ r) ^ 2 := by
    have : (L : ℝ) ≤ (L : ℝ) ^ r := by
      calc (L : ℝ) = (L : ℝ) ^ 1 := (pow_one _).symm
        _ ≤ (L : ℝ) ^ r := pow_le_pow_right₀ (by linarith) hr
    exact pow_le_pow_left₀ (by linarith) this 2
  have hn : 0 < 1 - (((L : ℝ) ^ 2)⁻¹) := by
    have : ((L : ℝ) ^ 2)⁻¹ ≤ 1 / 4 := by
      rw [inv_eq_one_div]; exact one_div_le_one_div_of_le (by norm_num) h4
    linarith
  have hd : 0 < 1 - ((((L : ℝ) ^ r) ^ 2)⁻¹) := by
    have : ((((L : ℝ) ^ r) ^ 2)⁻¹) ≤ 1 / 4 := by
      rw [inv_eq_one_div]; exact one_div_le_one_div_of_le (by norm_num) (h4.trans hr')
    linarith
  positivity

/-- **The block inequality of Lemma III.2.3** (ideal weights).  `S` is the set of the `V = L^{kd}`
sites of a `k`-block, `n_s ∈ [1, k - 1]` the layer of `s`, `τ_s` the deviation `t_x` of the leaf
containing `s` and `t₀ = ψ_k(z) - mean`; `aZ` is the ideal composed weight,
`aZ⁻¹ = V⁻¹ ∑_s u_{k - n_s}`, `u_r = (compWeight L a₁ r)⁻¹`. -/
theorem block_dominates {k d L : ℕ} (hL : 2 ≤ L) (hd : 2 ≤ d) {a₁ : ℝ} (ha₁ : 0 < a₁)
    (S : Finset α) (nS : α → ℕ) {V : ℝ} (hV : (S.card : ℝ) = V) (hVd : V = ((L : ℝ) ^ k) ^ d)
    (hn : ∀ s ∈ S, 1 ≤ nS s ∧ nS s < k) {aZ : ℝ}
    (haZ : aZ⁻¹ = V⁻¹ * ∑ s ∈ S, (compWeight L a₁ (k - nS s))⁻¹) (t0 : E) (τ : α → E) :
    compWeight L a₁ k * (L : ℝ) ^ (k * (d - 2)) * ‖t0 + V⁻¹ • ∑ s ∈ S, τ s‖ ^ 2 ≤
      aZ * (L : ℝ) ^ (k * (d - 2)) * ‖t0‖ ^ 2 +
        ∑ s ∈ S, compWeight L a₁ (nS s) / ((L : ℝ) ^ nS s) ^ 2 * ‖τ s‖ ^ 2 := by
  have : NeZero L := ⟨by omega⟩
  have hLpos : (0 : ℝ) < L := by exact_mod_cast (by omega : 0 < L)
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast (by omega : 1 ≤ L)
  have hVpos : 0 < V := by rw [hVd]; positivity
  have hSne : S.Nonempty := by
    rw [← Finset.card_pos]
    have : (0 : ℝ) < S.card := by rw [hV]; exact hVpos
    exact_mod_cast this
  have hk1 : 1 ≤ k := by
    obtain ⟨s, hs⟩ := hSne
    have := hn s hs
    omega
  have hapos : ∀ r, 1 ≤ r → 0 < compWeight L a₁ r := fun r hr => compWeight_pos hL ha₁ hr
  have hupos : ∀ r, 1 ≤ r → 0 < (compWeight L a₁ r)⁻¹ := fun r hr => inv_pos.2 (hapos r hr)
  have hsum_pos : 0 < ∑ s ∈ S, (compWeight L a₁ (k - nS s))⁻¹ :=
    Finset.sum_pos (fun s hs => hupos _ (by have := hn s hs; omega)) hSne
  have haZpos : 0 < aZ := by
    have : 0 < aZ⁻¹ := by rw [haZ]; positivity
    exact inv_pos.1 this
  set Lk : ℝ := (L : ℝ) ^ (k * (d - 2)) with hLk
  have hLkpos : 0 < Lk := by positivity
  have hc0 : 0 < aZ * Lk := by positivity
  have hc : ∀ s ∈ S, 0 < compWeight L a₁ (nS s) / ((L : ℝ) ^ nS s) ^ 2 := fun s hs =>
    div_pos (hapos _ (hn s hs).1) (by positivity)
  have hcs := weighted_cs S hc0 (fun s => compWeight L a₁ (nS s) / ((L : ℝ) ^ nS s) ^ 2)
    (fun _ => V⁻¹) hc t0 τ
  rw [← Finset.smul_sum] at hcs
  -- the key identity
  have hVLk : V = Lk * ((L : ℝ) ^ k) ^ 2 := by
    rw [hVd, hLk, pow_mul]
    have : d = (d - 2) + 2 := by omega
    conv_lhs => rw [this, pow_add]
  have hkey : 1 / (aZ * Lk) + ∑ s ∈ S, V⁻¹ ^ 2 / (compWeight L a₁ (nS s) / ((L : ℝ) ^ nS s) ^ 2) =
      (compWeight L a₁ k)⁻¹ / Lk := by
    have e1 : 1 / (aZ * Lk) = (V⁻¹ * ∑ s ∈ S, (compWeight L a₁ (k - nS s))⁻¹) / Lk := by
      rw [← haZ]; field_simp
    have e2 : ∀ s ∈ S, V⁻¹ ^ 2 / (compWeight L a₁ (nS s) / ((L : ℝ) ^ nS s) ^ 2) =
        V⁻¹ / Lk * (((L : ℝ) ^ nS s) ^ 2 / ((L : ℝ) ^ k) ^ 2 * (compWeight L a₁ (nS s))⁻¹) := by
      intro s hs
      have := (hapos _ (hn s hs).1).ne'
      rw [hVLk]
      field_simp
    rw [e1, Finset.sum_congr rfl e2, ← Finset.mul_sum]
    have e3 : ∀ s ∈ S, ((L : ℝ) ^ nS s) ^ 2 / ((L : ℝ) ^ k) ^ 2 * (compWeight L a₁ (nS s))⁻¹ =
        (compWeight L a₁ k)⁻¹ - (compWeight L a₁ (k - nS s))⁻¹ := fun s hs =>
      compWeight_C1 a₁ (n := nS s) (p := k) (hn s hs).2.le
    rw [Finset.sum_congr rfl e3, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, hV]
    field_simp
    ring
  rw [hkey] at hcs
  have hak := hapos k hk1
  calc compWeight L a₁ k * Lk * ‖t0 + V⁻¹ • ∑ s ∈ S, τ s‖ ^ 2
      ≤ compWeight L a₁ k * Lk * ((compWeight L a₁ k)⁻¹ / Lk *
        (aZ * Lk * ‖t0‖ ^ 2 + ∑ s ∈ S, compWeight L a₁ (nS s) / ((L : ℝ) ^ nS s) ^ 2 *
          ‖τ s‖ ^ 2)) := by gcongr
    _ = _ := by field_simp

end Block

end Balaban.LargeField
