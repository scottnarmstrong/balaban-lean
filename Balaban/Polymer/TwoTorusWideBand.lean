/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Polymer.TwoTorusEdgeChain
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Wide supports: the redistribution with an absolute rate (item 24, wide part)

A connected set of cells (a polymer of the block torus `Torus d K`) that contains two cells at
cyclic distance at least `D` in some coordinate has at least `D + 1` cells (`card_ge_of_spread`:
the distance to a fixed cell takes every value up to `D` along a path in the set, since adjacent
cells change it by at most one, `natAbs_vma_step`).  Consequently, if `K ≤ 21 (D + 1)` and the
chain to the wrapping region has at most `K / 4` cells, the chain is paid by the support:
`|Φ Y| ≤ 7 |Y|` (`chain_card_le_of_wide`).  In that regime the crude bound `c e^{-κ' |Y|}` with
`κ' ≥ 7 (κ + log 2)` sums over the polymers enlarged to `Z` to `c e^{-κ |Z|}`, with no prefactor
(`wideBand_fiber_bound`): the number of preimages is at most `2 ^ |Z|` and each term is at most
`c e^{-κ' |Z| / 7}`.  The rate does not depend on `K`, hence not on `L`
(`wideBand_fiber_bound_rate`: `κ' = 7 κ + 5`).  This replaces `edgeBand_fiber_bound` for chains
of length proportional to the size of the torus.
-/

@[expose] public section

noncomputable section

open scoped Classical

open Finset

namespace Balaban.Polymer

theorem natAbs_vma_add_one {K : ℕ} [NeZero K] (a : ZMod K) :
    (a + 1).valMinAbs.natAbs ≤ a.valMinAbs.natAbs + 1 ∧
      a.valMinAbs.natAbs ≤ (a + 1).valMinAbs.natAbs + 1 := by
  set v := a.valMinAbs with hv
  set v' := (a + 1).valMinAbs with hv'
  have h1 : v.natAbs ≤ K / 2 := ZMod.natAbs_valMinAbs_le a
  have h2 : v'.natAbs ≤ K / 2 := ZMod.natAbs_valMinAbs_le (a + 1)
  have hc : ((v' : ℤ) : ZMod K) = ((v + 1 : ℤ) : ZMod K) := by
    rw [hv', ZMod.coe_valMinAbs]; push_cast; rw [hv, ZMod.coe_valMinAbs]
  obtain ⟨m, hm⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).1 hc
  have hKpos : 0 < K := Nat.pos_of_ne_zero (NeZero.ne K)
  rcases Nat.lt_or_ge K 2 with hK | hK
  · have : K = 1 := by omega
    omega
  · have hKi : (2 : ℤ) ≤ K := by exact_mod_cast hK
    have b1 : v + 1 - v' ≤ K + 1 := by omega
    have b2 : -(K + 1 : ℤ) ≤ v + 1 - v' := by omega
    have hm' : -1 ≤ m ∧ m ≤ 1 := by constructor <;> nlinarith
    obtain ⟨hm1, hm2⟩ := hm'
    have : m = -1 ∨ m = 0 ∨ m = 1 := by omega
    rcases this with rfl | rfl | rfl <;> omega

section Spread

variable {d K : ℕ} [NeZero K]

theorem natAbs_vma_step (μ : Fin d) (b0 : Balaban.Torus d K) (x y : Balaban.Torus d K) (μ' : Fin d)
    (h : y = x + Pi.single μ' 1) :
    ((y μ - b0 μ).valMinAbs).natAbs ≤ ((x μ - b0 μ).valMinAbs).natAbs + 1 ∧
      ((x μ - b0 μ).valMinAbs).natAbs ≤ ((y μ - b0 μ).valMinAbs).natAbs + 1 := by
  by_cases hμ : μ' = μ
  · subst hμ
    have : y μ' - b0 μ' = (x μ' - b0 μ') + 1 := by rw [h]; simp; ring
    rw [this]
    exact natAbs_vma_add_one _
  · have : y μ - b0 μ = x μ - b0 μ := by rw [h]; simp [Ne.symm hμ]
    rw [this]; omega

theorem card_ge_of_spread (Y : Finset (Balaban.Torus d K))
    (hA : IsAnimal (blockGraph d K) Y)
    {b0 y : Balaban.Torus d K} (hb : b0 ∈ Y) (hy : y ∈ Y) (μ : Fin d) :
    ((y μ - b0 μ).valMinAbs).natAbs + 1 ≤ Y.card := by
  classical
  have hY := ((isAnimal_iff _ _).1 hA).2
  set f : (Balaban.Torus d K) → ℕ := fun z => ((z μ - b0 μ).valMinAbs).natAbs with hf
  have key : ∀ x, Relation.ReflTransGen
      (fun a b => a ∈ Y ∧ b ∈ Y ∧ (blockGraph d K).Adj a b) b0 x →
      ∀ j ≤ f x, ∃ z ∈ Y, f z = j := by
    intro x hx
    induction hx with
    | refl =>
      intro j hj
      have : f b0 = 0 := by simp [hf]
      exact ⟨b0, hb, by omega⟩
    | @tail u w _ hab ih =>
      obtain ⟨hu, hw, -, μ', h | h⟩ := hab
      · have := natAbs_vma_step μ b0 u w μ' h
        intro j hj
        by_cases hj' : j ≤ f u
        · exact ih j hj'
        · exact ⟨w, hw, by simp only [hf] at *; omega⟩
      · have := natAbs_vma_step μ b0 w u μ' h
        intro j hj
        by_cases hj' : j ≤ f u
        · exact ih j hj'
        · exact ⟨w, hw, by simp only [hf] at *; omega⟩
  have hsub : Finset.range (f y + 1) ⊆ Y.image f := by
    intro j hj
    obtain ⟨z, hz, hzj⟩ := key y (hY b0 hb y hy) j (by have := Finset.mem_range.1 hj; omega)
    exact Finset.mem_image.2 ⟨z, hz, hzj⟩
  have := (Finset.card_le_card hsub).trans Finset.card_image_le
  simpa using this
end Spread

section Band

/-- **Wide band.**  The terms `T Y` of the polymers of a class `P` have the crude bound
`‖T Y‖ ≤ c e^{-κ' |Y|}`, and `Φ` enlarges each `Y` of the class (`Y ⊆ Φ Y`) to at most `7 |Y|`
cells.  If `7 (κ + log 2) ≤ κ'`, then the sum of the terms over the polymers enlarged to `Z` is at
most `c e^{-κ |Z|}`, with no prefactor. -/
theorem wideBand_fiber_bound {B : Type*} [Fintype B] [DecidableEq B] (P : Finset B → Prop)
    (Φ : Finset B → Finset B) (T : Finset B → ℂ) {c κ κ' : ℝ} (hc : 0 ≤ c) (hκ0 : 0 ≤ κ)
    (hκ : 7 * (κ + Real.log 2) ≤ κ') (hsub : ∀ Y, P Y → Y ⊆ Φ Y)
    (hcard : ∀ Y, P Y → (Φ Y).card ≤ 7 * Y.card)
    (hT : ∀ Y, P Y → ‖T Y‖ ≤ c * Real.exp (-κ' * (Y.card : ℝ))) (Z : Finset B) :
    ‖∑ Y ∈ (Finset.univ : Finset (Finset B)).filter (fun Y => P Y ∧ Φ Y = Z), T Y‖ ≤
      c * Real.exp (-κ * (Z.card : ℝ)) := by
  have hl2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hk0 : 0 ≤ κ' := by linarith
  have hterm : ∀ Y ∈ (Finset.univ : Finset (Finset B)).filter (fun Y => P Y ∧ Φ Y = Z),
      ‖T Y‖ ≤ c * Real.exp (-(κ' / 7) * (Z.card : ℝ)) := by
    intro Y hY
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hY
    obtain ⟨hP, rfl⟩ := hY
    have h1 : ((Φ Y).card : ℝ) ≤ 7 * (Y.card : ℝ) := by exact_mod_cast hcard Y hP
    refine (hT Y hP).trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hc)
    nlinarith
  have hcnt := card_fiber_le_two_pow P Φ hsub Z
  have h2 : ((2 : ℝ) ^ Z.card) = Real.exp ((Z.card : ℝ) * Real.log 2) := by
    rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]
  calc ‖∑ Y ∈ (Finset.univ : Finset (Finset B)).filter (fun Y => P Y ∧ Φ Y = Z), T Y‖
      ≤ ∑ Y ∈ (Finset.univ : Finset (Finset B)).filter (fun Y => P Y ∧ Φ Y = Z), ‖T Y‖ :=
        norm_sum_le _ _
    _ ≤ ∑ Y ∈ (Finset.univ : Finset (Finset B)).filter (fun Y => P Y ∧ Φ Y = Z),
          c * Real.exp (-(κ' / 7) * (Z.card : ℝ)) := Finset.sum_le_sum hterm
    _ = (((Finset.univ : Finset (Finset B)).filter (fun Y => P Y ∧ Φ Y = Z)).card : ℝ) *
          (c * Real.exp (-(κ' / 7) * (Z.card : ℝ))) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ((2 : ℝ) ^ Z.card) * (c * Real.exp (-(κ' / 7) * (Z.card : ℝ))) := by
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        exact_mod_cast hcnt
    _ = c * Real.exp ((Z.card : ℝ) * Real.log 2 + -(κ' / 7) * (Z.card : ℝ)) := by
        rw [h2, Real.exp_add]; ring
    _ ≤ c * Real.exp (-κ * (Z.card : ℝ)) := by
        refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hc
        have : (0 : ℝ) ≤ Z.card := Nat.cast_nonneg _
        nlinarith

/-- The wide band at the rate `κ' = 7 κ + 5` (`7 log 2 < 5`). -/
theorem wideBand_fiber_bound_rate {B : Type*} [Fintype B] [DecidableEq B] (P : Finset B → Prop)
    (Φ : Finset B → Finset B) (T : Finset B → ℂ) {c κ : ℝ} (hc : 0 ≤ c) (hκ : 0 ≤ κ)
    (hsub : ∀ Y, P Y → Y ⊆ Φ Y) (hcard : ∀ Y, P Y → (Φ Y).card ≤ 7 * Y.card)
    (hT : ∀ Y, P Y → ‖T Y‖ ≤ c * Real.exp (-(7 * κ + 5) * (Y.card : ℝ))) (Z : Finset B) :
    ‖∑ Y ∈ (Finset.univ : Finset (Finset B)).filter (fun Y => P Y ∧ Φ Y = Z), T Y‖ ≤
      c * Real.exp (-κ * (Z.card : ℝ)) := by
  refine wideBand_fiber_bound P Φ T hc hκ ?_ hsub hcard hT Z
  have := Real.log_two_lt_d9
  linarith

/-- **The chain is paid by a wide support.**  If `Y` is a polymer of the torus with two cells at
cyclic distance at least `D` in a coordinate, `K ≤ 21 (D + 1)`, and the chain `Φ Y ⊇ Y` adds at
most `t + 1 ≤ K / 4` cells, then `|Φ Y| ≤ 7 |Y|`. -/
theorem chain_card_le_of_wide {d K D t : ℕ} [NeZero K] (hKD : K ≤ 21 * (D + 1))
    (ht : 4 * (t + 1) ≤ K) {Y Z : Finset (Balaban.Torus d K)}
    (hA : IsAnimal (blockGraph d K) Y)
    (hw : ∃ b0 ∈ Y, ∃ y ∈ Y, ∃ μ, D ≤ ((y μ - b0 μ).valMinAbs).natAbs)
    (hZ : Z.card ≤ Y.card + (t + 1)) : Z.card ≤ 7 * Y.card := by
  obtain ⟨b0, hb, y, hy, μ, hD⟩ := hw
  have := card_ge_of_spread Y hA hb hy μ
  omega

end Band

end Balaban.Polymer
