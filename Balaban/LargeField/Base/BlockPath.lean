/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Multiscale.PathMetricBounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Nearest-neighbour paths inside a block of Manhattan length (the sharp block diameter)

For two sites `x, y` of one `j`-block of layer `j` there is a nearest-neighbour path inside the
block (through the coordinatewise minimum) with at most `d (L^j - 1)` bonds, i.e. of
`PathCost` at most `d (L^j - 1) / L^j`.  (`Balaban.Multiscale.GeneratingSet.pathDist_block_le`
goes through the corner of the block and loses a factor `2`; the source constant is `d`.)
-/

@[expose] public section

namespace Balaban.LargeField

open Balaban.Multiscale Balaban.Multiscale.GeneratingSet Finset

variable {d L N₀ k : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}

/-- Two natural numbers in one block of length `N` differ by less than `N`. -/
theorem nat_block_aux (N a b : ℕ) (hN : 0 < N) (hab : a / N = b / N) :
    (a - min a b) + (b - min a b) ≤ N - 1 := by
  have h1 := Nat.div_add_mod a N
  have h2 := Nat.div_add_mod b N
  have h3 := Nat.mod_lt a hN
  have h4 := Nat.mod_lt b hN
  rw [hab] at h1
  generalize N * (b / N) = t at h1 h2
  generalize a % N = ra at *
  generalize b % N = rb at *
  rcases le_total a b with h5 | h5
  · rw [min_eq_left h5]; omega
  · rw [min_eq_right h5]; omega

/-- Equal `j`-blocks have equal block coordinates. -/
theorem jBlock_val_div_eq {j : ℕ} (hjk : j ≤ k) {x y : Torus d (N₀ * L ^ k)}
    (h : jBlock d L N₀ k j y = jBlock d L N₀ k j x) (μ : Fin d) :
    (y μ).val / L ^ j = (x μ).val / L ^ j := by
  have hμ := congrFun h μ
  unfold jBlock at hμ
  rw [blockMap_apply, blockMap_apply] at hμ
  have hv := congrArg ZMod.val hμ
  rwa [blockCoord_val (side_eq hjk), blockCoord_val (side_eq hjk)] at hv

variable (G : GeneratingSet d L N₀ k ϱ)

/-- A monotone descent path inside a block. -/
theorem pathCost_descend {j : ℕ} (hj : 1 ≤ j) (hjk : j ≤ k) :
    ∀ n : ℕ, ∀ x z : Torus d (N₀ * L ^ k), x ∈ G.layer j →
      jBlock d L N₀ k j z = jBlock d L N₀ k j x → (∀ μ, (z μ).val ≤ (x μ).val) →
      ∑ μ, ((x μ).val - (z μ).val) = n → G.PathCost x z ((n : ℝ) / (L : ℝ) ^ j) := by
  intro n
  induction n with
  | zero =>
      intro x z hx hzb hle hs
      have hxz : x = z := by
        funext μ
        apply ZMod.val_injective
        have := (Finset.sum_eq_zero_iff.1 hs) μ (mem_univ μ)
        have := hle μ
        omega
      subst hxz
      simpa using PathCost.refl x (G.layer_subset hj hjk hx)
  | succ n ih =>
      intro x z hx hzb hle hs
      obtain ⟨μ, -, hμ⟩ := Finset.exists_ne_zero_of_sum_ne_zero (s := univ)
        (f := fun μ => (x μ).val - (z μ).val) (by rw [hs]; omega)
      have hlt : (z μ).val < (x μ).val := by
        have := hle μ; omega
      have hNpos : 0 < L ^ j := Nat.pos_of_ne_zero (pow_ne_zero j (NeZero.ne L))
      set N := L ^ j with hN
      set x₁ : Torus d (N₀ * L ^ k) := x - Pi.single μ 1 with hx₁
      have hxx₁ : x = x₁ + Pi.single μ 1 := by rw [hx₁]; abel
      have hvpos : 0 < (x μ).val := by omega
      have hℓ2 : 1 < N₀ * L ^ k := by
        have := ZMod.val_lt (x μ)
        omega
      have hone : (1 : ZMod (N₀ * L ^ k)).val = 1 := by
        rw [ZMod.val_one_eq_one_mod, Nat.mod_eq_of_lt hℓ2]
      have hv1 : (x₁ μ).val = (x μ).val - 1 := by
        have : x₁ μ = x μ - 1 := by simp [hx₁]
        rw [this, ZMod.val_sub (by rw [hone]; omega), hone]
      have hother : ∀ ν, ν ≠ μ → x₁ ν = x ν := by
        intro ν hν; simp [hx₁, hν]
      have hdiv : (z μ).val / N = (x μ).val / N := jBlock_val_div_eq hjk hzb μ
      have hpos : 0 < (x μ).val % N := by
        have h1 := Nat.div_add_mod (x μ).val N
        have h2 := Nat.div_add_mod (z μ).val N
        have h3 : (z μ).val % N < N := Nat.mod_lt _ hNpos
        rw [hdiv] at h2
        omega
      have hrem1 : (x₁ μ).val % N = (x μ).val % N - 1 := by
        rw [hv1]; exact mod_pred hNpos hpos
      have hlt' : (x₁ μ).val % N + 1 < N := by
        have := Nat.mod_lt (x μ).val hNpos
        omega
      have hblock : jBlock d L N₀ k j x = jBlock d L N₀ k j x₁ := by
        unfold jBlock
        conv_lhs => rw [hxx₁]
        exact blockMap_add_single_of_inner (side_eq hjk) hlt'
      have hx₁l : x₁ ∈ G.layer j := (G.mem_layer_iff hj hjk hblock).1 hx
      have hzb' : jBlock d L N₀ k j z = jBlock d L N₀ k j x₁ := hzb.trans hblock
      have hle' : ∀ ν, (z ν).val ≤ (x₁ ν).val := by
        intro ν
        by_cases hν : ν = μ
        · subst hν; rw [hv1]; omega
        · rw [hother ν hν]; exact hle ν
      have hsum : ∑ ν, ((x₁ ν).val - (z ν).val) = n := by
        have e1 : ∑ ν, ((x ν).val - (z ν).val) =
            ((x μ).val - (z μ).val) + ∑ ν ∈ univ.erase μ, ((x ν).val - (z ν).val) :=
          (Finset.add_sum_erase _ _ (mem_univ μ)).symm
        have e2 : ∑ ν, ((x₁ ν).val - (z ν).val) =
            ((x₁ μ).val - (z μ).val) + ∑ ν ∈ univ.erase μ, ((x₁ ν).val - (z ν).val) :=
          (Finset.add_sum_erase _ _ (mem_univ μ)).symm
        have e3 : ∑ ν ∈ univ.erase μ, ((x₁ ν).val - (z ν).val) =
            ∑ ν ∈ univ.erase μ, ((x ν).val - (z ν).val) :=
          Finset.sum_congr rfl fun ν hν => by rw [hother ν (Finset.ne_of_mem_erase hν)]
        omega
      have hp := ih x₁ z hx₁l hzb' hle' hsum
      have hadj : Adj x x₁ := ⟨μ, Or.inr hxx₁⟩
      have hbc : G.bondCost x x₁ = 1 / (L : ℝ) ^ j := by
        unfold bondCost
        rw [G.spacing_eq hj hjk hx, G.spacing_eq hj hjk hx₁l, max_self]
      refine (PathCost.step x x₁ z _ (G.layer_subset hj hjk hx) hadj hp).congr_cost ?_
      rw [hbc]
      push_cast
      ring


/-- **Sharp oscillation path inside a block**: two points of one `j`-block of layer `j` are joined
by a nearest-neighbour path inside the block (through the coordinatewise minimum) of total cost
at most `d (L^j - 1) / L^j`, i.e. of at most `d (L^j - 1)` bonds. -/
theorem exists_pathCost_block {j : ℕ} (hj : 1 ≤ j) (hjk : j ≤ k) {x y : Torus d (N₀ * L ^ k)}
    (hx : x ∈ G.layer j) (h : jBlock d L N₀ k j y = jBlock d L N₀ k j x) :
    ∃ c : ℝ, c ≤ d * ((L : ℝ) ^ j - 1) / (L : ℝ) ^ j ∧ G.PathCost x y c := by
  have hy : y ∈ G.layer j := (G.mem_layer_iff hj hjk h).2 hx
  have hNpos : 0 < L ^ j := Nat.pos_of_ne_zero (pow_ne_zero j (NeZero.ne L))
  have hdiv : ∀ μ, (y μ).val / L ^ j = (x μ).val / L ^ j := jBlock_val_div_eq hjk h
  set m : Torus d (N₀ * L ^ k) := fun μ => (((min (x μ).val (y μ).val : ℕ)) : ZMod (N₀ * L ^ k))
    with hm
  have hmval : ∀ μ, (m μ).val = min (x μ).val (y μ).val := fun μ => by
    simp only [hm]
    exact ZMod.val_natCast_of_lt (lt_of_le_of_lt (min_le_left _ _) (ZMod.val_lt (x μ)))
  have hmdiv : ∀ μ, (m μ).val / L ^ j = (x μ).val / L ^ j := fun μ => by
    rw [hmval]
    rcases le_total (x μ).val (y μ).val with h1 | h1
    · rw [min_eq_left h1]
    · rw [min_eq_right h1, hdiv]
  have hmx : jBlock d L N₀ k j m = jBlock d L N₀ k j x := by
    funext μ
    unfold jBlock
    rw [blockMap_apply, blockMap_apply]
    unfold blockCoord
    rw [hmdiv μ]
  have hmy : jBlock d L N₀ k j m = jBlock d L N₀ k j y := hmx.trans h.symm
  have hp1 := pathCost_descend G hj hjk _ x m hx hmx (fun μ => by rw [hmval]; exact min_le_left _ _) rfl
  have hp2 := pathCost_descend G hj hjk _ y m hy hmy (fun μ => by rw [hmval]; exact min_le_right _ _) rfl
  refine ⟨_, ?_, hp1.trans hp2.symm⟩
  have hN : (0 : ℝ) < (L : ℝ) ^ j := by exact_mod_cast hNpos
  rw [← add_div, div_le_div_iff_of_pos_right hN]
  have hsum : (∑ μ, ((x μ).val - (m μ).val)) + ∑ μ, ((y μ).val - (m μ).val) ≤ d * (L ^ j - 1) := by
    rw [← Finset.sum_add_distrib]
    calc ∑ μ, (((x μ).val - (m μ).val) + ((y μ).val - (m μ).val)) ≤ ∑ _μ : Fin d, (L ^ j - 1) := by
          refine Finset.sum_le_sum fun μ _ => ?_
          rw [hmval]
          exact nat_block_aux (L ^ j) _ _ hNpos (hdiv μ).symm
      _ = d * (L ^ j - 1) := by simp
  have hcast : (((∑ μ, ((x μ).val - (m μ).val) : ℕ) : ℝ) + ((∑ μ, ((y μ).val - (m μ).val) : ℕ) : ℝ)) ≤
      ((d * (L ^ j - 1) : ℕ) : ℝ) := by
    exact_mod_cast hsum
  have hL1 : 1 ≤ L ^ j := hNpos
  rw [Nat.cast_mul, Nat.cast_sub hL1] at hcast
  push_cast at hcast ⊢
  exact hcast

end Balaban.LargeField
