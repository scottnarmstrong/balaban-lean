/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# The Peierls count (GM3) and the exponent inequality (GM4)

Model-free parts of `notes/phase1/LOCALIZATION.md` §4.2 (P3 (4.44)–(4.50)).

* `Balaban.Localization.peierls_count`: if every admissible family `𝒞` lies in a set `T` with
  `|T| ≤ A' N` and has `N ≤ G₀ |𝒞|`, then `∑ 𝒞, exp (-κ₂ |𝒞|) ≤ 1` as soon as
  `κ₂ / 2 ≥ max 1 (log (G₀ A'))`.
* `Balaban.Localization.peierls_count_layers`: the layered form (families `𝒞_n ⊂ 𝔓_n(Y)` with
  `|𝒞_n| ≥ N_n / G₀`, `|𝔓_n(Y)| = A' N_n`).
* `Balaban.Localization.exponent_inequality`: (GM4), a real-number lemma.
-/

@[expose] public section

namespace Balaban.Localization

open Finset Real

/-- The Peierls count (GM3), aggregate form. -/
theorem peierls_count {α : Type*} [DecidableEq α] (T : Finset α) (𝔖 : Finset (Finset α))
    (N : ℕ) (G₀ A' κ₂ : ℝ) (hG₀ : 0 < G₀) (hA' : 0 ≤ A')
    (hT : (T.card : ℝ) ≤ A' * N)
    (hS : ∀ 𝒞 ∈ 𝔖, 𝒞 ⊆ T ∧ (N : ℝ) ≤ G₀ * 𝒞.card)
    (h1 : 1 ≤ κ₂ / 2) (hlog : Real.log (G₀ * A') ≤ κ₂ / 2) :
    ∑ 𝒞 ∈ 𝔖, Real.exp (-κ₂ * 𝒞.card) ≤ 1 := by
  set x := κ₂ / 2 with hx
  have hκ : κ₂ = 2 * x := by rw [hx]; ring
  have hex : 0 < Real.exp (-x) := Real.exp_pos _
  -- termwise bound
  have hterm : ∀ 𝒞 ∈ 𝔖, Real.exp (-κ₂ * 𝒞.card) ≤
      Real.exp (-x * N / G₀) * ∏ _i ∈ 𝒞, Real.exp (-x) := by
    intro 𝒞 h𝒞
    obtain ⟨_, hc⟩ := hS 𝒞 h𝒞
    rw [Finset.prod_const, ← Real.exp_nat_mul, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hx0 : 0 ≤ x := by linarith
    have : (N : ℝ) / G₀ ≤ 𝒞.card := by rw [div_le_iff₀ hG₀]; linarith
    have h2 : -x * N / G₀ = -x * ((N : ℝ) / G₀) := by ring
    rw [h2, hκ]
    nlinarith [mul_le_mul_of_nonneg_left this hx0]
  have hsub : ∑ 𝒞 ∈ 𝔖, Real.exp (-κ₂ * 𝒞.card) ≤
      Real.exp (-x * N / G₀) * ∑ 𝒞 ∈ 𝔖, ∏ _i ∈ 𝒞, Real.exp (-x) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum hterm
  have hpow : ∑ 𝒞 ∈ 𝔖, ∏ _i ∈ 𝒞, Real.exp (-x) ≤ ∏ _i ∈ T, (1 + Real.exp (-x)) := by
    rw [Finset.prod_one_add]
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_) le_rfl
    · intro 𝒞 h𝒞; exact Finset.mem_powerset.mpr (hS 𝒞 h𝒞).1
    · intro i _ _; positivity
  have hprod : ∏ _i ∈ T, (1 + Real.exp (-x)) ≤ Real.exp (Real.exp (-x) * (A' * N)) := by
    rw [Finset.prod_const]
    calc (1 + Real.exp (-x)) ^ T.card ≤ (Real.exp (Real.exp (-x))) ^ T.card := by
          apply pow_le_pow_left₀ (by positivity)
          have := Real.add_one_le_exp (Real.exp (-x)); linarith
      _ = Real.exp (T.card * Real.exp (-x)) := by rw [← Real.exp_nat_mul]
      _ ≤ _ := by
          apply Real.exp_le_exp.mpr
          nlinarith
  have hAe : G₀ * A' * Real.exp (-x) ≤ 1 := by
    rcases (mul_nonneg hG₀.le hA').eq_or_lt with h0 | hpos
    · rw [← h0]; simp
    · have : G₀ * A' ≤ Real.exp x := by
        calc G₀ * A' = Real.exp (Real.log (G₀ * A')) := (Real.exp_log hpos).symm
          _ ≤ Real.exp x := Real.exp_le_exp.mpr hlog
      calc G₀ * A' * Real.exp (-x) ≤ Real.exp x * Real.exp (-x) :=
            mul_le_mul_of_nonneg_right this hex.le
        _ = 1 := by rw [← Real.exp_add]; simp
  have hfin : Real.exp (-x * N / G₀) * Real.exp (Real.exp (-x) * (A' * N)) ≤ 1 := by
    rw [← Real.exp_add]
    rw [← Real.exp_zero]
    apply Real.exp_le_exp.mpr
    have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg _
    have key : Real.exp (-x) * (A' * N) ≤ x * N / G₀ := by
      rw [le_div_iff₀ hG₀]
      have : Real.exp (-x) * (A' * N) * G₀ = (G₀ * A' * Real.exp (-x)) * N := by ring
      rw [this]
      nlinarith
    have : -x * N / G₀ = -(x * N / G₀) := by ring
    linarith
  calc _ ≤ _ := hsub
    _ ≤ Real.exp (-x * N / G₀) * Real.exp (Real.exp (-x) * (A' * N)) :=
        mul_le_mul_of_nonneg_left (hpow.trans hprod) (Real.exp_pos _).le
    _ ≤ 1 := hfin

/-- The Peierls count (GM3), layered form: layers `n ∈ ν`, disjoint sets `𝔓 n` with
`|𝔓 n| = A' N n`, and admissible families `𝒞` with `𝒞 ⊆ ⋃ₙ 𝔓 n`, `N n ≤ G₀ |𝒞 ∩ 𝔓 n|`. -/
theorem peierls_count_layers {α ν : Type*} [DecidableEq α] [DecidableEq ν] (s : Finset ν)
    (𝔓 : ν → Finset α) (hdisj : (s : Set ν).PairwiseDisjoint 𝔓) (N : ν → ℕ)
    (𝔖 : Finset (Finset α)) (G₀ A' κ₂ : ℝ) (hG₀ : 0 < G₀) (hA' : 0 ≤ A')
    (hcard : ∀ n ∈ s, ((𝔓 n).card : ℝ) = A' * N n)
    (hS : ∀ 𝒞 ∈ 𝔖, 𝒞 ⊆ s.biUnion 𝔓 ∧ ∀ n ∈ s, (N n : ℝ) ≤ G₀ * (𝒞 ∩ 𝔓 n).card)
    (h1 : 1 ≤ κ₂ / 2) (hlog : Real.log (G₀ * A') ≤ κ₂ / 2) :
    ∑ 𝒞 ∈ 𝔖, Real.exp (-κ₂ * 𝒞.card) ≤ 1 := by
  refine peierls_count (s.biUnion 𝔓) 𝔖 (∑ n ∈ s, N n) G₀ A' κ₂ hG₀ hA' ?_ ?_ h1 hlog
  · rw [Finset.card_biUnion hdisj]
    push_cast
    rw [Finset.mul_sum]
    exact (Finset.sum_congr rfl hcard).le
  · intro 𝒞 h𝒞
    obtain ⟨hsub, hn⟩ := hS 𝒞 h𝒞
    refine ⟨hsub, ?_⟩
    have hc : 𝒞.card = ∑ n ∈ s, (𝒞 ∩ 𝔓 n).card := by
      have : 𝒞 = s.biUnion (fun n => 𝒞 ∩ 𝔓 n) := by
        ext a; constructor
        · intro ha
          obtain ⟨n, hn, han⟩ := Finset.mem_biUnion.mp (hsub ha)
          exact Finset.mem_biUnion.mpr ⟨n, hn, Finset.mem_inter.mpr ⟨ha, han⟩⟩
        · intro ha
          obtain ⟨n, _, han⟩ := Finset.mem_biUnion.mp ha
          exact (Finset.mem_inter.mp han).1
      conv_lhs => rw [this]
      rw [Finset.card_biUnion]
      intro n hn m hm hnm
      exact Finset.disjoint_of_subset_left Finset.inter_subset_right
        (Finset.disjoint_of_subset_right Finset.inter_subset_right (hdisj hn hm hnm))
    rw [hc]; push_cast
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum hn

/-- The exponent inequality (GM4).  Here `c = |𝒞|`, `Δ = d_j(X)`, `D = d̃_{k+1}(Y[𝒞])`, `G` is
`(2L+1)^d`, and `κ₂ = κ₁/2 - 1`; the hypothesis `hD` is (GM2). -/
theorem exponent_inequality (d L G κ κ₀ κ₁ c Δ D : ℝ) (hL : 3 ≤ L)
    (hκ₀ : 0 ≤ κ₀) (hκ : 3 * κ₀ + 3 ≤ κ) (hκ₁ : 4 * d * G * κ ≤ κ₁) (hc : 0 ≤ c)
    (hΔ : 0 ≤ Δ) (hD : D ≤ Δ / L + d * G * c) :
    (κ₁ - 1) * c + (κ - 1) * Δ ≥ (κ₁ / 2 - 1) * c + κ₀ * Δ + 2 * κ * D := by
  have hκ0 : 0 ≤ κ := by linarith
  have hL0 : 0 < L := by linarith
  have h1 : 2 * κ * D ≤ 2 * κ * (Δ / L + d * G * c) :=
    mul_le_mul_of_nonneg_left hD (by linarith)
  have h2 : Δ / L ≤ Δ / 3 := div_le_div_of_nonneg_left hΔ (by norm_num) hL
  have h3 : 2 * κ * (d * G * c) ≤ κ₁ / 2 * c := by
    have : 2 * κ * (d * G) ≤ κ₁ / 2 := by nlinarith
    nlinarith
  have h4 : 2 * κ * (Δ / L) ≤ 2 * κ * (Δ / 3) :=
    mul_le_mul_of_nonneg_left h2 (by linarith)
  nlinarith [mul_nonneg hκ0 hΔ]

end Balaban.Localization
