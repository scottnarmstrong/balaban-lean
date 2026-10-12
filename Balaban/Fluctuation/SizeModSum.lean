/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# From a counting bound to an exponentially weighted sum

If at most `exp (aent (ℓ + 1))` elements of a finite family have size `< ℓ + 1`, then
`∑ exp (-κ size) ≤ exp aent / (1 - exp (-1))` for `κ ≥ aent + 1`.
-/

@[expose] public section

namespace Balaban.Fluctuation

theorem sum_exp_le {β : Type*} (F : Finset β) (dd : β → ℝ) (hdd : ∀ x ∈ F, 0 ≤ dd x)
    {aent κ : ℝ} (ha : 0 ≤ aent) (hκ : aent + 1 ≤ κ)
    (hcard : ∀ ℓ : ℕ, ((F.filter fun x => dd x < ℓ + 1).card : ℝ) ≤ Real.exp (aent * (ℓ + 1))) :
    ∑ x ∈ F, Real.exp (-κ * dd x) ≤ Real.exp aent / (1 - Real.exp (-1)) := by
  classical
  have hκ0 : 0 ≤ κ := by linarith
  set R : ℕ := F.sup (fun x => ⌊dd x⌋₊) + 1 with hR
  have h1 : ∑ x ∈ F, Real.exp (-κ * dd x) ≤ ∑ x ∈ F, Real.exp (-κ * (⌊dd x⌋₊ : ℝ)) := by
    refine Finset.sum_le_sum fun x hx => Real.exp_le_exp.2 ?_
    have := Nat.floor_le (hdd x hx)
    nlinarith
  have hmaps : ∀ x ∈ F, ⌊dd x⌋₊ ∈ Finset.range R := fun x hx => by
    rw [Finset.mem_range, hR]
    have := Finset.le_sup (f := fun x => ⌊dd x⌋₊) hx
    omega
  have h2 : ∑ x ∈ F, Real.exp (-κ * (⌊dd x⌋₊ : ℝ)) =
      ∑ ℓ ∈ Finset.range R, ((F.filter fun x => ⌊dd x⌋₊ = ℓ).card : ℝ) * Real.exp (-κ * ℓ) := by
    rw [← Finset.sum_fiberwise_of_maps_to hmaps]
    refine Finset.sum_congr rfl fun ℓ _ => ?_
    rw [Finset.sum_congr rfl (g := fun _ => Real.exp (-κ * ℓ))
      (fun x hx => by rw [(Finset.mem_filter.1 hx).2]), Finset.sum_const, nsmul_eq_mul]
  have h3 : ∀ ℓ ∈ Finset.range R, ((F.filter fun x => ⌊dd x⌋₊ = ℓ).card : ℝ) * Real.exp (-κ * ℓ) ≤
      Real.exp aent * Real.exp (-1) ^ ℓ := by
    intro ℓ _
    have hsub : (F.filter fun x => ⌊dd x⌋₊ = ℓ) ⊆ F.filter fun x => dd x < ℓ + 1 := by
      intro x hx
      obtain ⟨hxF, hxl⟩ := Finset.mem_filter.1 hx
      refine Finset.mem_filter.2 ⟨hxF, ?_⟩
      have := Nat.lt_floor_add_one (dd x)
      rw [hxl] at this
      exact this
    have hc : ((F.filter fun x => ⌊dd x⌋₊ = ℓ).card : ℝ) ≤ Real.exp (aent * (ℓ + 1)) :=
      (by exact_mod_cast Finset.card_le_card hsub : ((F.filter fun x => ⌊dd x⌋₊ = ℓ).card : ℝ) ≤
        ((F.filter fun x => dd x < ℓ + 1).card : ℝ)).trans (hcard ℓ)
    calc _ ≤ Real.exp (aent * (ℓ + 1)) * Real.exp (-κ * ℓ) :=
          mul_le_mul_of_nonneg_right hc (Real.exp_nonneg _)
      _ = Real.exp (aent * (ℓ + 1) + -κ * ℓ) := (Real.exp_add _ _).symm
      _ ≤ Real.exp (aent + (-1) * ℓ) := Real.exp_le_exp.2 (by
          have : (0 : ℝ) ≤ ℓ := Nat.cast_nonneg _
          nlinarith)
      _ = _ := by rw [Real.exp_add, ← Real.exp_nat_mul]; ring_nf
  have hr0 : Real.exp (-1) < 1 := by rw [Real.exp_lt_one_iff]; norm_num
  have hgeom : ∑ ℓ ∈ Finset.range R, Real.exp (-1) ^ ℓ ≤ 1 / (1 - Real.exp (-1)) := by
    have := mul_neg_geom_sum (Real.exp (-1)) R
    have hpos : 0 < 1 - Real.exp (-1) := by linarith
    rw [le_div_iff₀ hpos, mul_comm, this]
    have : 0 ≤ Real.exp (-1) ^ R := by positivity
    linarith
  calc ∑ x ∈ F, Real.exp (-κ * dd x) ≤ _ := h1
    _ = _ := h2
    _ ≤ ∑ ℓ ∈ Finset.range R, Real.exp aent * Real.exp (-1) ^ ℓ := Finset.sum_le_sum h3
    _ = Real.exp aent * ∑ ℓ ∈ Finset.range R, Real.exp (-1) ^ ℓ := by rw [Finset.mul_sum]
    _ ≤ Real.exp aent * (1 / (1 - Real.exp (-1))) :=
        mul_le_mul_of_nonneg_left hgeom (Real.exp_nonneg _)
    _ = _ := by ring

end Balaban.Fluctuation
