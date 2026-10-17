/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.RRemovedFinal
public import Balaban.LargeField.Budget.LemmaB
public import Balaban.LargeField.Budget.LogC
public import Balaban.LargeField.Budget.Counts

/-!
# The ripeness lower bound `hrip` for the budget of a region history (W947)

`notes/phase1/LF4R-PLAN.md`, item 7.  `logC_localHistory_eq`: the combinatoric factor read off the localized history
(`LocalHistory.logC`) is the recursive `H.logC` of Definition II.5.11 with vanishing decoration.
`hrip_of_counter`: for a ripe component `c` of `Z^pre_k` the ripeness bound `G^pre_k ≥ 2 A₂ λ_k^{p₂} + 1` in the form
`hrip` of `lf4R_removed`, from the conclusion `CounterConclusion` of LF-2 for the abstract history of the region
history with the budget of Lemma B (`toLF2HypBudget`); the instantiation is the landed `flow_counter`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open Balaban RegionHistory

section Rip

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K : ℕ}
  (H : RegionHistory S n R k0 K) {M : ℕ} [NeZero M]

theorem logC_localHistory_eq : ∀ k, k ≤ K → ∀ c : H.Comp k,
    (localHistory H M K k c).logC k = H.logC (fun _ _ => 0) k c := by
  intro k
  induction k with
  | zero =>
    intro _ c
    simp [LocalHistory.logC, RegionHistory.logC]
  | succ j ih =>
    intro hjK c
    rw [H.logC_succ hjK c]
    simp only [RegionHistory.logC, logCPre, add_zero, ite_self]
    have hc := H.card_oldCubes_add_outCubes (by omega : j < K) c
    have hc' : ((H.oldCubes j c).card : ℝ) + (H.outCubes j c).card = (S.L : ℝ) ^ S.d * c.1.card := by
      exact_mod_cast hc
    rw [Finset.sum_congr rfl (fun p _ => ih (by omega) p)]
    linarith

/-- **`hrip` for the budget of a region history.**  If the abstract history `toLF2HypBudget` (Lemma B for (B), the
hypotheses (Rg) for the post budget) satisfies the conclusion of LF-2 (`flow_counter`), then a ripe component `c`
at scale `j + 1` has `G^pre ≥ 2 A₂ λ^{p₂} + 1`, with `G^pre = budgetG (j+1) (κ^pre) (log C(𝔞)) |c|`
(`log C(𝔞) = LocalHistory.logC` of the localized history, `logC_localHistory_eq`). -/
theorem hrip_of_counter {P : BudgetConsts} (B : BudgetSetup S P) (ok : S.Ok) (hadm : H.Admissible)
    (κK : ∀ k, H.Comp k → ℝ)
    (rg_ripe : ∀ k, 1 ≤ k → k ≤ k0 → ∀ c : H.Comp k, c.1 ∉ H.rem k → S.Ripe k (H.bk k c) →
      H.budgetPre P κK (fun _ _ => 0) k c - S.CR * S.lam k ^ (2 * S.d + 1) + S.A3' * S.lam k ^ S.pR ≤
        H.budgetPost P κK (fun _ _ => 0) k c)
    (rg_nonripe : ∀ k, 1 ≤ k → k ≤ k0 → ∀ c : H.Comp k, c.1 ∉ H.rem k → ¬ S.Ripe k (H.bk k c) →
      H.budgetPost P κK (fun _ _ => 0) k c = H.budgetPre P κK (fun _ _ => 0) k c)
    (rg_frozen : ∀ k, k0 < k → ∀ c : H.Comp k,
      H.budgetPost P κK (fun _ _ => 0) k c = H.budgetPre P κK (fun _ _ => 0) k c)
    {khat : ℕ}
    (hcount : CounterConclusion
      ((H.toLF2HypBudget B ok hadm κK (fun _ _ => 0) rg_ripe rg_nonripe rg_frozen).toCounterHist ok) khat)
    {j : ℕ} (hk0 : j + 1 ≤ k0) (hkK : j + 1 ≤ K) (c : H.Comp (j + 1))
    (hripe : S.Ripe (j + 1) (H.bk (j + 1) c)) :
    2 * S.A2 * S.lam (j + 1) ^ S.p2 + 1 ≤
      P.budgetG S (j + 1) (H.kappaPre P j (H.kappa P κK j) c)
        ((localHistory H M K (j + 1) c).logC (j + 1)) c.1.card := by
  have h := hcount.Gp_ripe (j + 1) (by omega) hk0 hkK c hripe
  rw [logC_localHistory_eq H (j + 1) hkK c]
  refine h.trans (le_of_eq ?_)
  simp only [RegionHistory.logC, ite_self, add_zero]
  rfl

end Rip

end Balaban.LargeField
