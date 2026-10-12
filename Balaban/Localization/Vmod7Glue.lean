/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.TreeLength
public import Balaban.Localization.Peierls

/-!
# The abstract gluing lemma and the conditional exponent arithmetic (VMOD-7 §2, §4)

* `glue_charges` (VMOD-7 (2.4), abstract form): a retained connected structure `Γ₀` of cost
  `c₀` and, for each charge `i < n` in a given order, an admissible connected structure
  `(W i, E i)` inside the region `R` that meets the preceding structure and has cost `≤ c`, are
  glued by induction over the charges into one connected structure inside `R` containing `Γ₀` and
  every `W i`, of cost `≤ c₀ + n c` (subadditivity of the bond cost; nonnegative weights).
  Any monotone incidence property of the pieces (meeting a chosen cube) passes to the union.
* `glue_charges_cover`: the same conclusion in the form `Covers`.
* `exponent_arith_graph` (VMOD-7 (4.4)–(4.5)): the exponent arithmetic with a graph constant
  `Cgraph`.
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Finset

section Glue

variable {d n : ℕ}

/-- **Abstract gluing lemma (VMOD-7 (2.4))**: induction over the charges. -/
theorem glue_charges {ω : Torus d n → Torus d n → ℝ} (hω : ∀ x y, 0 ≤ ω x y)
    {R : Set (Torus d n)} {W₀ : Finset (Torus d n)} {E₀ : Finset (Torus d n × Torus d n)}
    (h₀ : ConnStruct W₀ E₀) (h₀R : ↑W₀ ⊆ R) (N : ℕ) (c : ℝ)
    (W : ℕ → Finset (Torus d n)) (E : ℕ → Finset (Torus d n × Torus d n))
    (hW : ∀ i < N, ConnStruct (W i) (E i)) (hWR : ∀ i < N, ↑(W i) ⊆ R)
    (hcost : ∀ i < N, bondCost ω (E i) ≤ c)
    (hjoin : ∀ i < N, ∃ z ∈ W i, z ∈ W₀ ∨ ∃ j < i, z ∈ W j) :
    ∃ (V : Finset (Torus d n)) (F : Finset (Torus d n × Torus d n)),
      ConnStruct V F ∧ ↑V ⊆ R ∧ W₀ ⊆ V ∧ (∀ i < N, W i ⊆ V) ∧
        bondCost ω F ≤ bondCost ω E₀ + N * c := by
  classical
  have key : ∀ m ≤ N, ∃ (V : Finset (Torus d n)) (F : Finset (Torus d n × Torus d n)),
      ConnStruct V F ∧ ↑V ⊆ R ∧ W₀ ⊆ V ∧ (∀ i < m, W i ⊆ V) ∧
        bondCost ω F ≤ bondCost ω E₀ + m * c := by
    intro m
    induction m with
    | zero =>
      intro _
      exact ⟨W₀, E₀, h₀, h₀R, Finset.Subset.refl _, fun i hi => absurd hi (by omega), by simp⟩
    | succ m ih =>
      intro hm
      obtain ⟨V, F, hVF, hVR, hW₀V, hWV, hcF⟩ := ih (by omega)
      have hmN : m < N := by omega
      obtain ⟨z, hzW, hz⟩ := hjoin m hmN
      have hzV : z ∈ V := by
        rcases hz with hz | ⟨j, hj, hz⟩
        · exact hW₀V hz
        · exact hWV j hj hz
      refine ⟨V ∪ W m, F ∪ E m, hVF.union (hW m hmN) ⟨z, hzV, hzW⟩, ?_, ?_, ?_, ?_⟩
      · intro x hx
        rcases Finset.mem_union.1 (Finset.mem_coe.1 hx) with hx | hx
        · exact hVR hx
        · exact hWR m hmN hx
      · exact hW₀V.trans Finset.subset_union_left
      · intro i hi
        rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
        · exact (hWV i hi).trans Finset.subset_union_left
        · exact Finset.subset_union_right
      · have := bondCost_union_le hω F (E m)
        have h2 := hcost m hmN
        push_cast
        linarith
  exact key N le_rfl

/-- The conclusion of `glue_charges` in the form `Covers`: the region `R` contains a connected
structure containing `Γ₀` and all pieces, of cost `≤ cost(Γ₀) + N c`. -/
theorem glue_charges_covers {ω : Torus d n → Torus d n → ℝ} (hω : ∀ x y, 0 ≤ ω x y)
    {R : Set (Torus d n)} {W₀ : Finset (Torus d n)} {E₀ : Finset (Torus d n × Torus d n)}
    (h₀ : ConnStruct W₀ E₀) (h₀R : ↑W₀ ⊆ R) (N : ℕ) (c : ℝ)
    (W : ℕ → Finset (Torus d n)) (E : ℕ → Finset (Torus d n × Torus d n))
    (hW : ∀ i < N, ConnStruct (W i) (E i)) (hWR : ∀ i < N, ↑(W i) ⊆ R)
    (hcost : ∀ i < N, bondCost ω (E i) ≤ c)
    (hjoin : ∀ i < N, ∃ z ∈ W i, z ∈ W₀ ∨ ∃ j < i, z ∈ W j)
    (A : Finset (Torus d n)) (hA : A ⊆ W₀ ∨ ∀ x ∈ A, x ∈ W₀ ∨ ∃ i < N, x ∈ W i) :
    Covers R ω (bondCost ω E₀ + N * c) A := by
  obtain ⟨V, F, hVF, hVR, hW₀V, hWV, hcF⟩ := glue_charges hω h₀ h₀R N c W E hW hWR hcost hjoin
  refine ⟨V, F, hVF, hVR, ?_, hcF⟩
  intro x hx
  rcases hA with hA | hA
  · exact hW₀V (hA hx)
  · rcases hA x hx with h | ⟨i, hi, h⟩
    · exact hW₀V h
    · exact hWV i hi h

end Glue

section Exponents

/-- **Conditional exponent arithmetic (VMOD-7 (4.4)–(4.5))**, with an arbitrary graph constant
`Cgraph`: if `D ≤ L⁻¹ Δ + Cgraph · c` (this is (4.1)), then
`(κ₁ - 1) c + (κ - 1) Δ ≥ (κ₁/2 - 1) c + κ₀ Δ + 2 κ D`. -/
theorem exponent_arith_graph (L Cgraph κ κ₀ κ₁ c Δ D : ℝ) (hL : 3 ≤ L) (hκ₀ : 0 ≤ κ₀)
    (hκ : 3 * κ₀ + 3 ≤ κ) (hκ₁ : 4 * Cgraph * κ ≤ κ₁) (hc : 0 ≤ c) (hΔ : 0 ≤ Δ)
    (hD : D ≤ Δ / L + Cgraph * c) :
    (κ₁ - 1) * c + (κ - 1) * Δ ≥ (κ₁ / 2 - 1) * c + κ₀ * Δ + 2 * κ * D :=
  exponent_inequality 1 L Cgraph κ κ₀ κ₁ c Δ D hL hκ₀ hκ (by linarith) hc hΔ (by linarith)

end Exponents

end Balaban.Localization
