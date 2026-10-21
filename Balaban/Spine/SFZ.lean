/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Spine.SFStep

/-!
# The field renormalization of the small-field step (part of A4-1c)

P4 p. 698 and (5.2) define the new field renormalization as `z_{k+1} = 1 + ζ` with `ξ₁ = ζ / ε_{k+1}`
and `|ξ₁| < ε ≤ c₁₀`, so `|z_{k+1} − 1| ≤ c₁₀ ε_{k+1}` is part of the output of the renormalization
(P4 (4.1), (5.2); A4-1c, `SFRenormInput`), not a step of a proof.  The landed inputs carry only
`z_{k+1} > 0` (A4-1a, `SFInheritInput`).  This file adds the bound as a spine-local named input of the
form `SFImageInput`; it joins A4-1c when the renormalization provider is built (`SPINE.md`).

* `SFZQ`, `SFZInput` (**open**, named input): the image of the small-field data has
  `|z_{k+1} − 1| ≤ c₁₀ ε_{k+1}`, with `ε_j = (P6 κ c₉).eps d L j` the sequence of the class;
* `sfZInput_of_z_eq_one`, `exists_sfZInput` (rule 10): a step map whose new field renormalization is
  `1` satisfies it for every `c₁₀ ≥ 0`, and such maps exist.
-/

@[expose] public section

open MeasureTheory Balaban Balaban.LargeField Balaban.LargeField.Def7 Balaban.LargeField.Def7v2 Balaban.SmallField

namespace Balaban.RootFSpine

section Z

variable (d N : ℕ) (T : ℝ → ℝ → Typing) (P6 : ℝ → ℝ → Def6.Consts)
  (C7 : ℝ → ℝ → Consts7) (cs₀ : ℝ → ℝ → OpConsts) (ϱ : ℝ → ℝ → ℝ)

/-- The property `SFZQ` asserts of the image of the small-field data (see `SFZInput`):
`|z_{k+1} − 1| ≤ c₁₀ ε_{k+1}`. -/
def SFZQ (c₁₀ : ℝ → ℝ → ℝ) :
    ∀ (κ c₉ _ _ : ℝ) (k : ℕ) [NeZero (T κ c₉).L],
      SFData d (T κ c₉).L (C7 κ c₉).m₁ k N (ϱ κ c₉) →
        SFData d (T κ c₉).L (C7 κ c₉).m₁ (k + 1) N (ϱ κ c₉) → Prop :=
  fun κ c₉ _ _ k _ _ sf' => |sf'.z (k + 1) - 1| ≤ c₁₀ κ c₉ * (P6 κ c₉).eps d (T κ c₉).L (k + 1)

variable (Φ : ∀ (κ c₉ _ _ : ℝ) (k : ℕ) [NeZero (T κ c₉).L],
    SFData d (T κ c₉).L (C7 κ c₉).m₁ k N (ϱ κ c₉) →
      SFData d (T κ c₉).L (C7 κ c₉).m₁ (k + 1) N (ϱ κ c₉))

/-- **The field renormalization of the image (part of A4-1c; named input, open; P4 (4.1), (5.2), p.
698).** For every member of `ℛ_k`, `1 ≤ k < k₀`, the new field renormalization of the image of the
small-field data is `z_{k+1} = 1 + ζ` with `|ζ| ≤ c₁₀ ε_{k+1}` (`ζ = ε_{k+1} ξ₁`, `|ξ₁| < ε ≤ c₁₀`). -/
def SFZInput (c₁₀ : ℝ → ℝ → ℝ) : Prop :=
  SFImageInput d N T P6 C7 cs₀ ϱ Φ (SFZQ d N T P6 C7 ϱ c₁₀)

/-- **A step map with `z_{k+1} = 1` satisfies `SFZInput`** for every `c₁₀ ≥ 0` (rule 10). -/
theorem sfZInput_of_z_eq_one {c₁₀ : ℝ → ℝ → ℝ} (hc : ∀ κ c₉, 0 ≤ c₁₀ κ c₉)
    (hε : ∀ κ c₉ (j : ℕ), 0 ≤ (P6 κ c₉).eps d (T κ c₉).L j)
    (hz : ∀ (κ c₉ β ν : ℝ) (k : ℕ) [NeZero (T κ c₉).L]
      (sf : SFData d (T κ c₉).L (C7 κ c₉).m₁ k N (ϱ κ c₉)), (Φ κ c₉ β ν k sf).z (k + 1) = 1) :
    SFZInput d N T P6 C7 cs₀ ϱ Φ c₁₀ := by
  intro κ _ c₉ _
  refine ⟨0, fun β _ ν _ _ _ k _ _ sf _ => ?_⟩
  show |(Φ κ c₉ β ν k sf).z (k + 1) - 1| ≤ c₁₀ κ c₉ * (P6 κ c₉).eps d (T κ c₉).L (k + 1)
  rw [hz, sub_self, abs_zero]
  exact mul_nonneg (hc κ c₉) (hε κ c₉ (k + 1))

include Φ in
/-- **`SFZInput` is satisfiable** (rule 10): any step map with its new field renormalization set to
`1` satisfies it (`c₁₀ = 0`). -/
theorem exists_sfZInput :
    ∃ Φ' : ∀ (κ c₉ _ _ : ℝ) (k : ℕ) [NeZero (T κ c₉).L],
      SFData d (T κ c₉).L (C7 κ c₉).m₁ k N (ϱ κ c₉) →
        SFData d (T κ c₉).L (C7 κ c₉).m₁ (k + 1) N (ϱ κ c₉),
      SFZInput d N T P6 C7 cs₀ ϱ Φ' (fun _ _ => 0) := by
  refine ⟨fun κ c₉ β ν k _ sf => { Φ κ c₉ β ν k sf with z := fun _ => 1 }, ?_⟩
  intro κ _ c₉ _
  refine ⟨0, fun β _ ν _ _ _ k _ _ sf _ => ?_⟩
  show |(1 : ℝ) - 1| ≤ 0 * (P6 κ c₉).eps d (T κ c₉).L (k + 1)
  simp

end Z

end Balaban.RootFSpine
