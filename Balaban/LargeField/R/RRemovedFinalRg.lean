/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.RRemovedFinalRip
public import Balaban.LargeField.Counter.InstantiationFlow

/-!
# The (Rg) rules of the budget of a region history and the counter conclusion (W948)

`notes/phase1/LF4R-PLAN.md`, item 7.  With vanishing decoration `δ = 0`:

* `budgetPost_eq_budgetPre_of_not_kept`, `rg_nonripe_zero`, `rg_frozen_zero`: off the kept events `G_k = G^pre_k`;
* `rg_ripe_of_kappaK`: on a kept ripe component (`kappa k c = κK k c`) (Rg) is exactly the kept-data inequality
  `κ^pre − C_R λ_k^{2d+1} + A₃' λ_k^{p_R} ≤ κK_k(c)`, the exponent of the kept outcome (Theorem III.8.9 (a));
  `κK` is a free parameter of the history (the exponent of the kept operators, `KeptData`);
* `hcount_of_flow`: the conclusion of LF-2 (`flow_counter`) for `toLF2HypBudget` (Lemma B for (B)).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open Balaban RegionHistory

section Rg

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K : ℕ}
  (H : RegionHistory S n R k0 K) (P : BudgetConsts)

theorem budgetPost_eq_budgetPre_of_not_kept (κK δ : ∀ k, H.Comp k → ℝ) {k : ℕ} (c : H.Comp k)
    (hn : ¬ H.IsKeptEvent k c) : H.budgetPost P κK δ k c = H.budgetPre P κK δ k c := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := by
    rcases k with _ | j
    · exact (H.F.isEmpty_comp_zero.false c).elim
    · exact ⟨j, rfl⟩
  simp [RegionHistory.budgetPost, RegionHistory.budgetPre, RegionHistory.Gpost, RegionHistory.Gpre,
    RegionHistory.kappa, RegionHistory.logC, hn, RegionHistory.kappaPre, RegionHistory.logCPre]

theorem rg_nonripe_zero (κK : ∀ k, H.Comp k → ℝ) :
    ∀ k, 1 ≤ k → k ≤ k0 → ∀ c : H.Comp k, c.1 ∉ H.rem k → ¬ S.Ripe k (H.bk k c) →
      H.budgetPost P κK (fun _ _ => 0) k c = H.budgetPre P κK (fun _ _ => 0) k c :=
  fun _ _ _ c _ hn =>
    budgetPost_eq_budgetPre_of_not_kept H P κK _ c (fun h => hn h.2.2)

theorem rg_frozen_zero (κK : ∀ k, H.Comp k → ℝ) :
    ∀ k, k0 < k → ∀ c : H.Comp k,
      H.budgetPost P κK (fun _ _ => 0) k c = H.budgetPre P κK (fun _ _ => 0) k c :=
  fun k hk c => budgetPost_eq_budgetPre_of_not_kept H P κK _ c (fun h => by have := h.2.1; omega)

/-- **(Rg) at a ripe component from the kept-data inequality**: if the kept exponent satisfies
`κ^pre_{j+1}(c) − C_R λ^{2d+1} + A₃' λ^{p_R} ≤ κK_{j+1}(c)` for the components with a kept event, then
`G^pre − C_R λ^{2d+1} + A₃' λ^{p_R} ≤ G` (decoration `0`). -/
theorem rg_ripe_of_kappaK (κK : ∀ k, H.Comp k → ℝ)
    (hκ : ∀ j, j + 1 ≤ k0 → ∀ c : H.Comp (j + 1), c.1 ∉ H.rem (j + 1) → S.Ripe (j + 1) (H.bk (j + 1) c) →
      H.kappaPre P j (H.kappa P κK j) c - S.CR * S.lam (j + 1) ^ (2 * S.d + 1) +
        S.A3' * S.lam (j + 1) ^ S.pR ≤ κK (j + 1) c) :
    ∀ k, 1 ≤ k → k ≤ k0 → ∀ c : H.Comp k, c.1 ∉ H.rem k → S.Ripe k (H.bk k c) →
      H.budgetPre P κK (fun _ _ => 0) k c - S.CR * S.lam k ^ (2 * S.d + 1) + S.A3' * S.lam k ^ S.pR ≤
        H.budgetPost P κK (fun _ _ => 0) k c := by
  intro k hk1 hk0 c hrem hripe
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have hkept : H.IsKeptEvent (j + 1) c := ⟨hk1, hk0, hripe⟩
  have h := hκ j hk0 c hrem hripe
  simp only [RegionHistory.budgetPre, RegionHistory.budgetPost, RegionHistory.Gpre,
    RegionHistory.Gpost, RegionHistory.kappa, RegionHistory.logC, hkept, ite_true, add_zero]
  unfold BudgetConsts.budgetG
  linarith

end Rg

section Count

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {P : BudgetConsts}

/-- **The conclusion of LF-2 for the budget of the flow's region history** (`flow_counter`): (B) is Lemma B for the
recursive exponents with kept data `κK`, (Rg) are `rg_nonripe_zero`, `rg_frozen_zero` and, for the ripe components, the
kept-data inequality `hκ` (`rg_ripe_of_kappaK`).  The flow hypotheses `hS`, `hkf`, `hΛ12`, `hgen` stay named. -/
theorem hcount_of_flow (G : S.Good) (F : FlowSeq) (hS : F.Matches S)
    (H : RegionHistory S n R F.k0 F.kf) (hadm : H.Admissible) (hkf : 1 ≤ F.kf)
    (hΛ12 : ((F.d : ℝ) + 3) / 2 ≤ S.lam F.k0 * (1 - 1 / (2 * Real.log F.L)))
    (hgen : F.beta F.k0 * F.nu F.k0 ≤ 1 → 2 * (F.L : ℝ) ^ 2 ≤ F.beta F.k0)
    (B : BudgetSetup S P) (κK : ∀ k, H.Comp k → ℝ)
    (hκ : ∀ j, j + 1 ≤ F.k0 → ∀ c : H.Comp (j + 1), c.1 ∉ H.rem (j + 1) →
      S.Ripe (j + 1) (H.bk (j + 1) c) →
        H.kappaPre P j (H.kappa P κK j) c - S.CR * S.lam (j + 1) ^ (2 * S.d + 1) +
          S.A3' * S.lam (j + 1) ^ S.pR ≤ κK (j + 1) c) :
    CounterConclusion
      ((H.toLF2HypBudget B G.ok hadm κK (fun _ _ => 0) (rg_ripe_of_kappaK H P κK hκ)
        (rg_nonripe_zero H P κK) (rg_frozen_zero H P κK)).toCounterHist G.ok) F.kfhat :=
  flow_counter G F hS H hadm hkf hΛ12 hgen _ _ (H.lemmaB_recursive B G.ok κK (fun _ _ => 0))
    (rg_ripe_of_kappaK H P κK hκ) (rg_nonripe_zero H P κK) (rg_frozen_zero H P κK)

end Count

end Balaban.LargeField
