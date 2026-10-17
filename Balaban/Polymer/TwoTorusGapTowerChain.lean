/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Polymer.TwoTorusGapTowerStep

/-!
# The induction over the gap scales (item 24, blocker 7)

The resummed terms `Tn` of a scale are the inherited terms `Tinh` of the next.  The conclusions of
`resum_gapScale_torus_step` on `Tn` (equality on the common quarter box, support, locality, analyticity,
bound) are the hypotheses `hIH`, `hsuppI`, `hlocI`, `hanI`, `hbdI` on the inherited terms of the next
step (`gapScale_bound_lower_rate` for the rate).  `gapScale_chain` is the induction over
the scales: if the property `Good j` of the inherited terms of scale `j` is reproduced by the step
(`hstep`) and holds for the zero terms at the first gap scale (`h0`), the steps can be chained.
-/

@[expose] public section

namespace Balaban.Polymer.TwoTorusStep

section Chain

variable {ι G : Type*} {d : ℕ}

/-- **The rate of the bound on the resummed terms may be lowered**, as the next step needs: the
bound `C e^{-κr |X|}` of the fifth conclusion of `resum_gapScale_torus_step` gives the hypothesis
`hbdI` of the next step with any rate `κ'' ≤ κr`; the other conclusions (`hIH` from the fourth,
`hsuppI`, `hlocI`, `hanI` from the sixth to eighth) are the hypotheses on the inherited terms as
they stand. -/
theorem gapScale_bound_lower_rate (P : ι → Finset (Finset (Fin d → ℤ)))
    (sz : Finset (Fin d → ℤ) → ℕ) (Dset : Set G) (Tn : ι → G → Finset (Fin d → ℤ) → ℂ)
    {C κr κ'' : ℝ} (hC : 0 ≤ C) (hκ : κ'' ≤ κr)
    (hbd : ∀ ℓ X, X ∈ P ℓ → ∀ g ∈ Dset, ‖Tn ℓ g X‖ ≤ C * Real.exp (-κr * (sz X : ℝ))) :
    ∀ ℓ X, X ∈ P ℓ → ∀ g ∈ Dset, ‖Tn ℓ g X‖ ≤ C * Real.exp (-κ'' * (sz X : ℝ)) := by
  intro ℓ X hX g hg
  refine (hbd ℓ X hX g hg).trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hC)
  have : (0 : ℝ) ≤ (sz X : ℝ) := Nat.cast_nonneg _
  nlinarith

/-- **The induction over the gap scales.**  `Good j T` is the property of the inherited terms `T` of the
scale `j` that the step needs; the step produces resummed terms with the property `Good (j + 1)`, and
at the first gap scale the inherited terms are zero.  Then the steps chain: there are inherited terms
`Ts j` with `Good j (Ts j)` for all `j ≤ J`, `Ts 0 = 0`, and `Out j (Ts j) (Ts (j + 1))` for `j < J`,
where `Out j T Tn` is the conclusion of the step (`Tn` the resummed terms from the inherited `T`). -/
theorem gapScale_chain (Good : ℕ → (ι → G → Finset (Fin d → ℤ) → ℂ) → Prop)
    (Out : ℕ → (ι → G → Finset (Fin d → ℤ) → ℂ) → (ι → G → Finset (Fin d → ℤ) → ℂ) → Prop)
    (h0 : Good 0 0)
    (hstep : ∀ j T, Good j T → ∃ Tn, Out j T Tn ∧ Good (j + 1) Tn) (J : ℕ) :
    ∃ Ts : ℕ → ι → G → Finset (Fin d → ℤ) → ℂ, Ts 0 = 0 ∧ (∀ j ≤ J, Good j (Ts j)) ∧
      ∀ j < J, Out j (Ts j) (Ts (j + 1)) := by
  classical
  choose! F hF using hstep
  let Ts : ℕ → ι → G → Finset (Fin d → ℤ) → ℂ := fun n =>
    Nat.rec (0 : ι → G → Finset (Fin d → ℤ) → ℂ) (fun j T => if Good j T then F j T else 0) n
  have hs : ∀ j, Ts (j + 1) = if Good j (Ts j) then F j (Ts j) else 0 := fun j => rfl
  have hgood : ∀ j, Good j (Ts j) := by
    intro j
    induction j with
    | zero => exact h0
    | succ j ih => rw [hs]; simp only [ih, ↓reduceIte]; exact (hF j _ ih).2
  refine ⟨Ts, rfl, fun j _ => hgood j, fun j _ => ?_⟩
  rw [hs]; simp only [hgood j, ↓reduceIte]
  exact (hF j _ (hgood j)).1

/-- **`hKL` of `hob_of_obsSum` from the size of the torus**: `K ≥ 25 L + 1` cells give
`L ≤ (K - 26) / 25 + 1`. -/
theorem hKL_of_large {L K : ℕ} (h : 25 * L + 1 ≤ K) : L ≤ (K - 26) / 25 + 1 := by omega

end Chain

end Balaban.Polymer.TwoTorusStep
