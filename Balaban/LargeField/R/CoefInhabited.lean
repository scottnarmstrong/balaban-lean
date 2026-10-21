/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.CoefBirth
public import Balaban.LargeField.Def7v2Inhabited

/-!
# `CoefFam` and `CoefCtx` are inhabited

The second-version witness of `Def7v2Inhabited` (`d = L = 3`, `k = 1`, `N = 2`, zero terms,
`κ = a_ent + 4`) satisfies (D2), hence gives a `CoefFam` at the level `j = 1` on the birth domains
and a `CoefCtx` on every torus of the sequence.
-/

@[expose] public section

namespace Balaban.LargeField.Def7v2

open Balaban Balaban.SmallField Balaban.SmallField.Def6 Balaban.SmallField.Def6v2
  Balaban.LargeField.Def7 Balaban.LargeField.Def7.Wit Wit

/-- **`CoefFam` is inhabited** (rule 10). -/
theorem coefFam_nonempty (m₁ k0 : ℕ) :
    Nonempty (∃ ρ, CoefFam (witnessConsts 1) ((wSF2 wν₀ m₁).ν 1)
      (sfDom (witnessConsts 1) k0 (wSF2 wν₀ m₁)) (wSF2 wν₀ m₁).Tm 1 ρ) := by
  refine ⟨_, coefFam_of_d2sf2 (wSF2_D2 wν₀ wν₀_pos wν₀_nine k0 m₁ (fun _ => 1) (fun _ => zero_le_one))
    le_rfl le_rfl le_rfl ?_ le_rfl le_rfl ?_⟩
  · show Balaban.Fluctuation.aEnt 3 3 + 1 < Balaban.Fluctuation.aEnt 3 3 + 4
    linarith
  · simp only [wSF2, wνs]; have := wν₀_pos; positivity

/-- **`CoefCtx` is inhabited** (rule 10): at the first torus of the sequence. -/
theorem coefCtx_nonempty (m₁ k0 : ℕ) :
    ∃ ρ, Nonempty (haveI : NeZero (torusSeq 3 (witnessConsts 1).m₀ 0) :=
      ⟨torusSeq_ne_zero _ 0⟩
      CoefCtx (witnessConsts 1) ((wSF2 wν₀ m₁).ν 1)
        (sfDom (witnessConsts 1) k0 (wSF2 wν₀ m₁) (torusSeq 3 (witnessConsts 1).m₀ 0))
        ((wSF2 wν₀ m₁).Tm (torusSeq 3 (witnessConsts 1).m₀ 0)) 1 ρ) := by
  obtain ⟨ρ, fam⟩ := (coefFam_nonempty m₁ k0).some
  exact ⟨ρ, ⟨fam.ctx 0⟩⟩

end Balaban.LargeField.Def7v2
