/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.SmallField.LocalGeneratorTyping
public import Balaban.Fluctuation.StepActivityClassChart

/-!
# The class chart on a local generating set

At the low separation index `bgR0 d L`, the generating set `localB j hj X hsep` can be used
in the small-field class. A datum in its complex solution chart at the expansion radius
realizes a point of the class field domain when the class radius is large enough. The
statement keeps the local datum and the radius inequality explicit.
-/

@[expose] public section

namespace Balaban.SmallField.GsSpec

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization Balaban.LargeField
  Balaban.SmallField Balaban.SmallField.Def6 Balaban.SmallField.Def6v2 Balaban.Fluctuation

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁]
  {j : ℕ} {hj : j ≤ k} {X : Set (CTorus d L N₁ m₁ k)}
  {hsep : bgR0 d L ≤ minSep L (L ^ m₁)}
  {A : ℕ → ℝ} {μ ε ε' : ℝ}

/-- A complex background datum on the local generator belongs to its class chart when
the expansion radius fits inside the class radius. -/
theorem localB_xiDom_of_xiCData
    (hε : scaledC0 d ^ 2 * ε ≤ ε')
    {D : BgData (localB j hj X hsep) N}
    (hD : XiCData (localB j hj X hsep) A μ j (scaledC0 d) ε D) :
    XiDom (localB j hj X hsep) A μ j ε' D.Ψ D.h :=
  xiDom_of_xiCData hε hD

/-- The same local datum lies in the `dom` field of the low-index class domain. -/
theorem localB_xiFieldDom_of_xiCData {εseq : ℕ → ℝ}
    (hε : scaledC0 d ^ 2 * ε ≤ εseq j)
    {D : BgData (localB j hj X hsep) N}
    (hD : XiCData (localB j hj X hsep) A μ j (scaledC0 d) ε D) :
    (xiFieldDom A μ εseq : FieldDom d L N₁ m₁ k N (bgR0 d L)).dom j
      (localB j hj X hsep) D.Ψ D.h :=
  localB_xiDom_of_xiCData hε hD

/-- A specified pair of fields is in the local class domain if it is the raw pair of a
local complex background datum at the smaller radius. -/
theorem localB_xiFieldDom_pair_of_xiCData {εseq : ℕ → ℝ}
    (hε : scaledC0 d ^ 2 * ε ≤ εseq j)
    {Ψ h : Fld d L N₁ m₁ k N}
    (hD : ∃ D : BgData (localB j hj X hsep) N,
      D.Ψ = Ψ ∧ D.h = h ∧ XiCData (localB j hj X hsep) A μ j (scaledC0 d) ε D) :
    (xiFieldDom A μ εseq : FieldDom d L N₁ m₁ k N (bgR0 d L)).dom j
      (localB j hj X hsep) Ψ h := by
  obtain ⟨D, rfl, rfl, hX⟩ := hD
  exact localB_xiFieldDom_of_xiCData hε hX

end Balaban.SmallField.GsSpec
