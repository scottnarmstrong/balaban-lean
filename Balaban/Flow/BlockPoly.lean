/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Flow.CellGreen

/-!
# The block Hamiltonian on cell polynomials

The one-dimensional model of the first-step operators: on `ℤ` with blocks of `M` consecutive sites,
`H = −Δ + w P + ν`, `P` the block average.  On the functions
`u(k) = F₂(k mod M) x² + F₁(k mod M) x + F₀(k mod M)`, `x = ⌊k/M⌋`, with cell functions `F_j : ZMod M → ℂ`
(`polyZ`), `H` acts as `polyZ` of a triple of cell functions (`polyZ_H`):

* `A₂ = H_per F₂`;
* `A₁ = H_per F₁ − 2δ_{−1} F₂(·+1) + 2δ_0 F₂(·−1)`;
* `A₀ = H_per F₀ − δ_{−1}(F₂+F₁)(·+1) − δ_0(F₂−F₁)(·−1)`,

with `H_per F = −ΔF + w avg(F) + ν F` the cell Hamiltonian (periodic Laplacian, `avg` the cell mean).
This is the Bloch expansion of `H` at second order in the block momentum.
-/

@[expose] public section

namespace Balaban.Flow

open Finset

variable {M : ℕ} [NeZero M]

/-- The cell mean `(1/M) ∑_r F(r)`. -/
noncomputable def cellAvg (F : ZMod M → ℂ) : ℂ := (1 / (M : ℂ)) * ∑ r, F r

/-- The cell Hamiltonian `H_per F = −ΔF + w avg(F) + ν F` (periodic Laplacian on `ZMod M`). -/
noncomputable def cellH (w ν : ℝ) (F : ZMod M → ℂ) (r : ZMod M) : ℂ :=
  2 * F r - F (r + 1) - F (r - 1) + (w : ℂ) * cellAvg F + (ν : ℂ) * F r

/-- The indicator of the last cell position `r = −1`. -/
noncomputable def cellLast (r : ZMod M) : ℂ := if r = -1 then 1 else 0

/-- The indicator of the first cell position `r = 0`. -/
noncomputable def cellFirst (r : ZMod M) : ℂ := if r = 0 then 1 else 0

/-- The cell polynomial `F₂ x² + F₁ x + F₀` evaluated at the lattice site `k`, `x = ⌊k/M⌋`. -/
noncomputable def polyZ (F₂ F₁ F₀ : ZMod M → ℂ) (k : ℤ) : ℂ :=
  F₂ (k : ZMod M) * ((k / M : ℤ) : ℂ) ^ 2 + F₁ (k : ZMod M) * ((k / M : ℤ) : ℂ) + F₀ (k : ZMod M)

/-- The block average of a function on `ℤ`. -/
noncomputable def blockAvgZ (M : ℕ) (f : ℤ → ℂ) (k : ℤ) : ℂ :=
  (1 / (M : ℂ)) * ∑ j : Fin M, f (M * (k / M) + j)

/-- The block Hamiltonian on `ℤ`: `H f = −Δ f + w P f + ν f`. -/
noncomputable def HZ (M : ℕ) (w ν : ℝ) (f : ℤ → ℂ) (k : ℤ) : ℂ :=
  2 * f k - f (k + 1) - f (k - 1) + (w : ℂ) * blockAvgZ M f k + (ν : ℂ) * f k

theorem int_ediv_succ (k : ℤ) :
    (k + 1) / M = k / M + (if ((k : ZMod M)) = -1 then 1 else 0) := by
  have hM : (0 : ℤ) < M := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne M)
  have h1 : (M : ℤ) * (k / M) + k % M = k := Int.mul_ediv_add_emod k M
  have h2 : 0 ≤ k % M := Int.emod_nonneg _ hM.ne'
  have h3 : k % M < M := Int.emod_lt_of_pos _ hM
  have hcast : ((k % M + 1 : ℤ) : ZMod M) = (k : ZMod M) + 1 := by
    rw [Int.cast_add, ZMod.intCast_mod]; push_cast; rfl
  have hiff : (k : ZMod M) = -1 ↔ k % M + 1 = M := by
    constructor
    · intro h
      have h0 : ((k % M + 1 : ℤ) : ZMod M) = 0 := by rw [hcast, h]; ring
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h0
      obtain ⟨c, hc⟩ := h0
      have hc1 : 0 < c := by
        by_contra hc'; push Not at hc'; nlinarith
      have hc2 : c < 2 := by
        by_contra hc'; push Not at hc'; nlinarith
      have : c = 1 := by omega
      subst this; omega
    · intro h
      have h0 : ((k % M + 1 : ℤ) : ZMod M) = 0 := by
        rw [h]; exact_mod_cast ZMod.natCast_self M
      rw [hcast] at h0
      exact eq_neg_of_add_eq_zero_left h0
  have hk : k + 1 = M * (k / M) + (k % M + 1) := by omega
  by_cases h : (k : ZMod M) = -1
  · have hr := hiff.1 h
    simp only [h, ↓reduceIte]
    have : k + 1 = M * (k / M + 1) := by rw [hk, hr]; ring
    rw [this, Int.mul_ediv_cancel_left _ hM.ne']
  · have hr : k % M + 1 ≠ M := fun e => h (hiff.2 e)
    simp only [h, ↓reduceIte]
    rw [hk, Int.mul_add_ediv_left _ _ hM.ne',
      Int.ediv_eq_zero_of_lt (by omega : 0 ≤ k % M + 1) (by omega : k % M + 1 < M)]

theorem int_ediv_pred (k : ℤ) :
    (k - 1) / M = k / M - (if ((k : ZMod M)) = 0 then 1 else 0) := by
  have h := int_ediv_succ (M := M) (k - 1)
  rw [sub_add_cancel] at h
  have hc : (((k - 1 : ℤ) : ZMod M) = -1) ↔ ((k : ZMod M) = 0) := by
    push_cast
    constructor <;> intro h <;> linear_combination h
  simp only [hc] at h
  linarith

theorem sum_fin_zmod (g : ZMod M → ℂ) : ∑ j : Fin M, g (j : ℕ) = ∑ r, g r := by
  refine Fintype.sum_bijective (fun j : Fin M => ((j : ℕ) : ZMod M)) ?_ _ _ fun _ => rfl
  have hinj : Function.Injective (fun j : Fin M => ((j : ℕ) : ZMod M)) := by
    intro a b hab
    apply Fin.ext
    have := (ZMod.natCast_eq_natCast_iff' a b M).1 hab
    rwa [Nat.mod_eq_of_lt a.2, Nat.mod_eq_of_lt b.2] at this
  refine hinj.bijective_of_nat_card_le ?_
  simp [ZMod.card]

theorem polyZ_succ (F₂ F₁ F₀ : ZMod M → ℂ) (k : ℤ) :
    polyZ F₂ F₁ F₀ (k + 1) =
      F₂ ((k : ZMod M) + 1) * (((k / M : ℤ) : ℂ) + cellLast (k : ZMod M)) ^ 2
        + F₁ ((k : ZMod M) + 1) * (((k / M : ℤ) : ℂ) + cellLast (k : ZMod M))
        + F₀ ((k : ZMod M) + 1) := by
  have h := int_ediv_succ (M := M) k
  unfold polyZ cellLast
  have hq : (((k + 1) / M : ℤ) : ℂ) = ((k / M : ℤ) : ℂ) + (if (k : ZMod M) = -1 then 1 else 0) := by
    rw [h]; split_ifs <;> simp
  rw [hq]; push_cast; rfl

theorem polyZ_pred (F₂ F₁ F₀ : ZMod M → ℂ) (k : ℤ) :
    polyZ F₂ F₁ F₀ (k - 1) =
      F₂ ((k : ZMod M) - 1) * (((k / M : ℤ) : ℂ) - cellFirst (k : ZMod M)) ^ 2
        + F₁ ((k : ZMod M) - 1) * (((k / M : ℤ) : ℂ) - cellFirst (k : ZMod M))
        + F₀ ((k : ZMod M) - 1) := by
  have h := int_ediv_pred (M := M) k
  unfold polyZ cellFirst
  have hq : (((k - 1) / M : ℤ) : ℂ) = ((k / M : ℤ) : ℂ) - (if (k : ZMod M) = 0 then 1 else 0) := by
    rw [h]; split_ifs <;> simp
  rw [hq]; push_cast; rfl

theorem blockAvgZ_polyZ (F₂ F₁ F₀ : ZMod M → ℂ) (k : ℤ) :
    blockAvgZ M (polyZ F₂ F₁ F₀) k =
      cellAvg F₂ * ((k / M : ℤ) : ℂ) ^ 2 + cellAvg F₁ * ((k / M : ℤ) : ℂ) + cellAvg F₀ := by
  have hM : (M : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne M
  have key : ∀ j : Fin M, polyZ F₂ F₁ F₀ ((M : ℤ) * (k / M) + (j : ℕ)) =
      F₂ (j : ℕ) * ((k / M : ℤ) : ℂ) ^ 2 + F₁ (j : ℕ) * ((k / M : ℤ) : ℂ) + F₀ (j : ℕ) := by
    intro j
    have h1 : (((M : ℤ) * (k / M) + (j : ℕ) : ℤ) : ZMod M) = ((j : ℕ) : ZMod M) := by
      push_cast; simp
    have h2 : ((M : ℤ) * (k / M) + (j : ℕ)) / M = k / M := by
      rw [add_comm, mul_comm, Int.add_mul_ediv_right _ _ hM,
        Int.ediv_eq_zero_of_lt (by positivity) (by exact_mod_cast j.2), zero_add]
    unfold polyZ; rw [h1, h2]
  unfold blockAvgZ cellAvg
  simp only [key]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul,
    sum_fin_zmod F₂, sum_fin_zmod F₁, sum_fin_zmod F₀]
  ring

/-- The block Hamiltonian acts on cell polynomials by the three cell operators. -/
theorem polyZ_H (w ν : ℝ) (F₂ F₁ F₀ : ZMod M → ℂ) (k : ℤ) :
    HZ M w ν (polyZ F₂ F₁ F₀) k =
      polyZ (cellH w ν F₂)
        (fun r => cellH w ν F₁ r - 2 * cellLast r * F₂ (r + 1) + 2 * cellFirst r * F₂ (r - 1))
        (fun r => cellH w ν F₀ r - cellLast r * (F₂ (r + 1) + F₁ (r + 1))
          - cellFirst r * (F₂ (r - 1) - F₁ (r - 1))) k := by
  have hl : cellLast (k : ZMod M) * cellLast (k : ZMod M) = cellLast (k : ZMod M) := by
    unfold cellLast; split_ifs <;> simp
  have hf : cellFirst (k : ZMod M) * cellFirst (k : ZMod M) = cellFirst (k : ZMod M) := by
    unfold cellFirst; split_ifs <;> simp
  unfold HZ
  rw [blockAvgZ_polyZ, polyZ_succ, polyZ_pred]
  unfold polyZ cellH
  linear_combination (-(F₂ ((k : ZMod M) + 1))) * hl + (-(F₂ ((k : ZMod M) - 1))) * hf

end Balaban.Flow
