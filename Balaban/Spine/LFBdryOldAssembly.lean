/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Spine.LFBdry

/-!
# The old part of the step's boundary terms: the conditional assembly (blocker 3, closing ladder item 7)

`LFBdryOldInput Λ Sb Bo` asks (D7) of the pre-`R` class of scale `k + 1` for the old part `Sb.old` of
the boundary terms of the step map `Λ`.  The closing ladder of blocker 3 (`notes/phase1/PLAN-B.md`,
W1154e) produces explicit boundary terms `O` (the re-expanded old terms `oldB2` of reading HS-2 at the
step's data) with their (D7) clauses.  This file reduces `LFBdryOldInput` to the two named pieces:

* `OldPartEq Λ Sb O`: **the identity** — the old part of the step's boundary terms is `O` (ladder item 6:
  P5 (2.48), (3.2), FLUCTUATION Theorem 3.1 (c) on the region);
* `LFBdryPart … Φ Λ O Bo`: (D7) of the pre-`R` class for `O` (ladder items 1–5 and W1164's clauses
  `loc_hist`, `euclid`);
* `lfBdryOldInput_of_old_eq`: `LFBdryOldInput Λ Sb Bo` from the two.
-/

@[expose] public section

open MeasureTheory Balaban Balaban.LargeField Balaban.LargeField.Def7 Balaban.LargeField.Def7v2
  Balaban.SmallField

namespace Balaban.RootFSpine

section OldAssembly

variable (d N : ℕ) (T : ℝ → ℝ → Typing) (P6 : ℝ → ℝ → Def6.Consts)
  (C7 : ℝ → ℝ → Consts7) (PB : ℝ → ℝ → BudgetConsts) (cs₀ : ℝ → ℝ → OpConsts)
  (M1 c : ℝ → ℝ → ℕ) (rH ϱ : ℝ → ℝ → ℝ)
  (Φ : ∀ (κ c₉ _ _ : ℝ) (k : ℕ) [NeZero (T κ c₉).L],
    SFData d (T κ c₉).L (C7 κ c₉).m₁ k N (ϱ κ c₉) →
      SFData d (T κ c₉).L (C7 κ c₉).m₁ (k + 1) N (ϱ κ c₉))

/-- **The identity for the old part of the step's boundary terms** (named piece; ladder item 6): for
every record and every torus of the family, the old part `Sb.old` of the boundary terms of the step
map `Λ` is the family `O` (in the closing ladder, the re-expanded old terms `oldB2` at the step's
data: P5 (2.48), (3.2), FLUCTUATION Theorem 3.1 (c) on the region, `h₀ = Re h = hv`). -/
def OldPartEq (Λ : LFStepMap d N T P6 C7 PB cs₀ M1 c rH ϱ)
    (Sb : LFBdrySplit d N T P6 C7 PB cs₀ M1 c rH ϱ Λ)
    (O : ∀ (κ c₉ β ν : ℝ) (h : EuclideanSpace ℝ (Fin N)) (kf : ℕ) [NeZero (T κ c₉).L]
      [NeZero (T κ c₉).M] (k : ℕ) (ρ : 𝒟[d, N, T κ c₉, β, (cs₀ κ c₉).aKer, kf + 1, k]) (νk : ℝ)
      (rec : RepRec d N (T κ c₉) (P6 κ c₉) (C7 κ c₉) (PB κ c₉) (cs₀ κ c₉) (M1 κ c₉) (c κ c₉)
        (rH κ c₉) (ϱ κ c₉) β ν h kf k ρ νk) (nK : ℕ) [NeZero nK],
      BTerms 𝒮[d, T κ c₉, β, (cs₀ κ c₉).aKer] (sides (T κ c₉).L (kf + 1) nK) rec.R
        (kZero d (T κ c₉).L β ν) (kf + 1) (T κ c₉).M N (k + 1)) : Prop :=
  ∀ (κ c₉ β ν : ℝ) (h : EuclideanSpace ℝ (Fin N)) (kf : ℕ) [NeZero (T κ c₉).L]
    [NeZero (T κ c₉).M] (k : ℕ) (ρ : 𝒟[d, N, T κ c₉, β, (cs₀ κ c₉).aKer, kf + 1, k]) (νk : ℝ)
    (rec : RepRec d N (T κ c₉) (P6 κ c₉) (C7 κ c₉) (PB κ c₉) (cs₀ κ c₉) (M1 κ c₉) (c κ c₉)
      (rH κ c₉) (ϱ κ c₉) β ν h kf k ρ νk) (nK : ℕ) [NeZero nK],
    (Sb κ c₉ β ν h kf k ρ νk rec).old nK = O κ c₉ β ν h kf k ρ νk rec nK

/-- `OldPartEq` is satisfiable (rule 10): at `O = Sb.old`. -/
theorem oldPartEq_self (Λ : LFStepMap d N T P6 C7 PB cs₀ M1 c rH ϱ)
    (Sb : LFBdrySplit d N T P6 C7 PB cs₀ M1 c rH ϱ Λ) :
    OldPartEq d N T P6 C7 PB cs₀ M1 c rH ϱ Λ Sb
      (fun κ c₉ β ν h kf _ _ k ρ νk rec nK _ => (Sb κ c₉ β ν h kf k ρ νk rec).old nK) :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ => rfl

/-- **The old part of the step's boundary terms satisfies (D7)** (blocker 3, `LFBdryOldInput`) once it is
identified with a family `O` (`OldPartEq`, ladder item 6) for which (D7) of the pre-`R` class holds with
the constant `Bo` (`LFBdryPart … O Bo`, ladder items 1–5 with W1164's `loc_hist`, `euclid`). -/
theorem lfBdryOldInput_of_old_eq (Λ : LFStepMap d N T P6 C7 PB cs₀ M1 c rH ϱ)
    (Sb : LFBdrySplit d N T P6 C7 PB cs₀ M1 c rH ϱ Λ) (Bo : ℝ → ℝ → ℝ)
    (O : ∀ (κ c₉ β ν : ℝ) (h : EuclideanSpace ℝ (Fin N)) (kf : ℕ) [NeZero (T κ c₉).L]
      [NeZero (T κ c₉).M] (k : ℕ) (ρ : 𝒟[d, N, T κ c₉, β, (cs₀ κ c₉).aKer, kf + 1, k]) (νk : ℝ)
      (rec : RepRec d N (T κ c₉) (P6 κ c₉) (C7 κ c₉) (PB κ c₉) (cs₀ κ c₉) (M1 κ c₉) (c κ c₉)
        (rH κ c₉) (ϱ κ c₉) β ν h kf k ρ νk) (nK : ℕ) [NeZero nK],
      BTerms 𝒮[d, T κ c₉, β, (cs₀ κ c₉).aKer] (sides (T κ c₉).L (kf + 1) nK) rec.R
        (kZero d (T κ c₉).L β ν) (kf + 1) (T κ c₉).M N (k + 1))
    (hEq : OldPartEq d N T P6 C7 PB cs₀ M1 c rH ϱ Λ Sb O)
    (hO : LFBdryPart d N T P6 C7 PB cs₀ M1 c rH ϱ Φ Λ O Bo) :
    LFBdryOldInput d N T P6 C7 PB cs₀ M1 c rH ϱ Φ Λ Sb Bo := by
  have e : (fun κ c₉ β ν h kf (_ : NeZero (T κ c₉).L) (_ : NeZero (T κ c₉).M) k ρ νk rec =>
      (Sb κ c₉ β ν h kf k ρ νk rec).old) =
      (fun κ c₉ β ν h kf (_ : NeZero (T κ c₉).L) (_ : NeZero (T κ c₉).M) k ρ νk rec nK
        (_ : NeZero nK) => O κ c₉ β ν h kf k ρ νk rec nK) := by
    funext κ c₉ β ν h kf i₁ i₂ k ρ νk rec nK i₃
    exact hEq κ c₉ β ν h kf k ρ νk rec nK
  unfold LFBdryOldInput
  rw [e]
  exact hO

end OldAssembly

end Balaban.RootFSpine
