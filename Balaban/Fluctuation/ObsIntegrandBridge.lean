/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.Thm31b

/-!
# Transport of an `ObsMarks` record along an almost-everywhere equal integrand

Only the field `hF` of `ObsMarks` mentions the integrand `f`.  If `f' s x = f s x` for almost every
`x`, for every `s ∈ [0,1]`, the record for `f` gives the record for `f'` with every other field
unchanged.  The tilt family and the unconditional record are not treated here.
-/

@[expose] public section

namespace Balaban.Fluctuation

open MeasureTheory

section Transport

variable {d L N₁ m₁ K : ℕ} [NeZero L] [NeZero N₁] {X : Type*} [MeasurableSpace X]
  {ν : Measure X} {m₀ : ℕ} {BS : ProdSplit ν d L N₁ m₁ K m₀} {W : ℝ → X → ℂ} {f f' : ℝ → X → ℂ}
  {bx : CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ K Set.univ}

/-- The record for an almost-everywhere equal integrand `f'`: all fields except `hF` are those of
`I`. -/
def ObsMarks.congr_f (I : ObsMarks ν BS W f bx)
    (h : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ᵐ x ∂ν, f s x = f' s x) :
    ObsMarks ν BS W f' bx :=
  { I with
    hF := fun s hs => by
      filter_upwards [I.hF s hs, h s hs] with x hx hx'
      rw [← hx', hx] }

end Transport

end Balaban.Fluctuation
