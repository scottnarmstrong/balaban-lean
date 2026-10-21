/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Spine.FinalRepRemoval

/-!
# Removal records in the post-`R` representation (audit, `notes/phase1/REMOVAL-HIST.md`)

Evidence for the audit of the removal histories in `D1Form2`:

* `exists_mem_agree_rem`: a complete set of histories (`IsComplete k (k + 1)`) contains, for every
  admissible history, a history with the same removal records `Rem_j`, `j ≤ k`; so the set cannot be
  restricted to histories without removals;
* `exists_mem_rem_ne_empty`: if some admissible history removes a component at the scale `k`, a
  complete set contains a history that removes a component at the scale `k`;
* `postTerm2Raw_eq_of_region_empty`: two histories of a representation with empty region at the scale
  `k` have the same term before the case split of R12 (no operator, no boundary term), whatever their removal records are.
-/

@[expose] public section

namespace Balaban.RootFSpine

open Balaban Balaban.LargeField Balaban.LargeField.Def7 Balaban.LargeField.Def7v2 RegionHistory

section Removal

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K : ℕ}

theorem exists_mem_agree_rem {k : ℕ} {hist : Finset (LabHist S n R k0 K)}
    (hc : IsComplete k (k + 1) hist) (A : LabHist S n R k0 K) :
    ∃ B ∈ hist, ∀ j, j ≤ k → B.H.rem j = A.H.rem j := by
  obtain ⟨B, ⟨hB, hAB⟩, -⟩ := hc A
  exact ⟨B, hB, fun j hj => ((hAB.2 j (by omega)).1).symm⟩

theorem exists_mem_rem_ne_empty {k : ℕ} {hist : Finset (LabHist S n R k0 K)}
    (hc : IsComplete k (k + 1) hist) (A : LabHist S n R k0 K) (hA : A.H.rem k ≠ ∅) :
    ∃ B ∈ hist, B.H.rem k ≠ ∅ := by
  obtain ⟨B, hB, h⟩ := exists_mem_agree_rem hc A
  exact ⟨B, hB, by rw [h k le_rfl]; exact hA⟩

end Removal

section Term

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K : ℕ} {M : ℕ} [NeZero M]
  [NeZero S.L] {N : ℕ} {geo : Geo S n R M} {cs : OpConsts} {P : BudgetConsts} {k : ℕ}

theorem postTerm2Raw_eq_of_region_empty {m₁ : ℕ} {ϱ : ℝ} (C : SFCtx S n R M K N k m₁ ϱ)
    (vc : CorrCoef S.d) (rep : Rep S n R k0 K M N geo cs P k) {A B : LabHist S n R k0 K}
    (hA : (A.H.step k).Z = ∅) (hB : (B.H.step k).Z = ∅)
    (ψk : BlockAt S n M K k → EuclideanSpace ℝ (Fin N)) (hv : EuclideanSpace ℝ (Fin N))
    (g : GIdx S n M K N → ℂ) : postTerm2Raw C vc rep A ψk hv g = postTerm2Raw C vc rep B ψk hv g := by
  rw [postTerm2Raw_of_region_empty C vc rep A hA, postTerm2Raw_of_region_empty C vc rep B hB]

end Term

end Balaban.RootFSpine
