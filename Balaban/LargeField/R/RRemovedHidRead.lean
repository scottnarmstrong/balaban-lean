/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Operators.Variables
public import Balaban.LargeField.Operators.Setup

/-!
# Reading a large-field variable (W929)

`notes/phase1/LF4R-PLAN.md`, leaf 6, blocker 4, obstruction (2).  The field `subVarField x s y` at a variable of
`A` is the value of that variable (`subVarField_var`), and it does not depend on the coordinates of `x` at the
variables that are not read (`subVarField_congr`).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open MeasureTheory Balaban Balaban.Multiscale RegionHistory

section Read

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {M K : ℕ} [NeZero M] [NeZero S.L] {N : ℕ}
  {a : LocalHistory S n M K} {k : ℕ} {A : Set (InternalVars a k)}

/-- The field at a large-field variable of `A` is its value. -/
theorem subVarField_var (x : SubCfg N a k A) (p : ↥A) (hp : p.1.1.2.1 = VarKind.large) :
    subVarField N x (p.1.1.1 : ℕ) p.1.1.2.2 = VarVal.toEuc (x p) := by
  classical
  obtain ⟨⟨⟨⟨s, hs⟩, κ, y⟩, hmem⟩, hA⟩ := p
  have hκ : κ = VarKind.large := hp
  subst hκ
  have hex : ∃ hj : s < k, ∃ hb : BlockSub (S := S) (n := n) (M := M) (K := K) s y
      (varSet a s .large), mkVar a k s .large y hj hb ∈ A := ⟨hs, hmem, hA⟩
  simp only [subVarField, hex, dite_true]
  rfl

/-- The field at a block does not depend on the coordinates of the variables of `A` that are not
at that block. -/
theorem subVarField_congr (x x' : SubCfg N a k A) (s : ℕ) (y : BlockAt S n M K s)
    (hag : ∀ p : ↥A, p.1.1.2.1 = VarKind.large → (p.1.1.1 : ℕ) = s → HEq p.1.1.2.2 y →
      VarVal.toEuc (x p) = VarVal.toEuc (x' p)) :
    subVarField N x s y = subVarField N x' s y := by
  classical
  unfold subVarField
  by_cases h : ∃ hj : s < k, ∃ hb : BlockSub (S := S) (n := n) (M := M) (K := K) s y
      (varSet a s .large), mkVar a k s .large y hj hb ∈ A
  · simp only [h, dite_true]
    exact hag ⟨mkVar a k s .large y h.1 h.2.1, h.2.2⟩ rfl rfl HEq.rfl
  · simp only [h, dite_false]

end Read

end Balaban.LargeField
