/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Spine.AgreeTransportSpine
public import Balaban.LargeField.Budget.Exponents
public import Balaban.LargeField.Operators.LocOp

/-!
# Exponents and kept events along `HAgr`

For region histories that agree up to the scale `m`, the kept events and the exponents
`κ_j(Z, 𝔸 ∩ Z)` of the non-removed components at the scales `j ≤ m` correspond under `HAgr.cequiv`,
as soon as the kept exponents `κK` correspond at the non-removed kept events (`kappa_eq`).
-/

@[expose] public section

namespace Balaban.RootFSpine

open Balaban Balaban.LargeField Balaban.LargeField.Def7 RegionHistory

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K : ℕ}

namespace HAgr

variable {m : ℕ} {H₁ H₂ : RegionHistory S n R k0 K} (h : HAgr m H₁ H₂)
include h

theorem isKeptEvent_iff {j : ℕ} (hj : j ≤ m) (c : H₁.Comp j) :
    H₂.IsKeptEvent j (h.cmap hj c) ↔ H₁.IsKeptEvent j c := by
  unfold RegionHistory.IsKeptEvent
  rw [h.bk_eq j hj c]

theorem isKept_iff {j : ℕ} (hj : j ≤ m) (c : H₁.Comp j) :
    IsKept H₂ j (h.cmap hj c) ↔ IsKept H₁ j c := by
  unfold IsKept
  rw [h.bk_eq j hj c]

theorem rem_iff {j : ℕ} (hj : j ≤ m) (c : H₁.Comp j) :
    (h.cmap hj c).1 ∉ H₂.rem j ↔ c.1 ∉ H₁.rem j := by
  rw [h.cmap_val, h.rem j hj]

theorem kappa_eq (P : BudgetConsts) (κ₁ : ∀ k, H₁.Comp k → ℝ) (κ₂ : ∀ k, H₂.Comp k → ℝ)
    (hκ : ∀ i (hi : i ≤ m) (c : H₁.Comp i), c.1 ∉ H₁.rem i → H₁.IsKeptEvent i c →
      κ₂ i (h.cmap hi c) = κ₁ i c) :
    ∀ (j : ℕ) (hj : j ≤ m) (c : H₁.Comp j), c.1 ∉ H₁.rem j →
      H₂.kappa P κ₂ j (h.cmap hj c) = H₁.kappa P κ₁ j c
  | 0, _, c, _ => (H₁.F.isEmpty_comp_zero.false c).elim
  | j + 1, hj, c, hc => by
    classical
    unfold RegionHistory.kappa
    by_cases hk : H₁.IsKeptEvent (j + 1) c
    · simp only [hk, (h.isKeptEvent_iff hj c).2 hk, ite_true]
      exact hκ (j + 1) hj c hc hk
    · have hk2 : ¬ H₂.IsKeptEvent (j + 1) (h.cmap hj c) :=
        fun h' => hk ((h.isKeptEvent_iff hj c).1 h')
      simp only [hk, hk2, ite_false]
      unfold RegionHistory.kappaPre
      rw [h.parts_eq hj c, Finset.sum_map, h.outCubes_eq hj c, h.cmap_val,
        ← h.newCubes_eq (show j < m by omega)]
      congr 1
      refine Finset.sum_congr rfl fun c' hc' => ?_
      simp only [Equiv.coe_toEmbedding]
      exact kappa_eq P κ₁ κ₂ hκ j (by omega) c' ((H₁.mem_parts j c' c).1 hc').1

end HAgr

end Balaban.RootFSpine
