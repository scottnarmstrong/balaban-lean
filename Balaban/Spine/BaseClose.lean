/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Spine.BaseSF
public import Balaban.Spine.BaseConsts
public import Balaban.Spine.BaseVacuum

/-!
# The final assembly of the base step from its named rows (blocker 1, F0)

`baseSteps_of_named`: `BasePreStepInput ∧ BaseFlatStepInput` from the prefix `PrefixInput`, a
first-step map `Γ : BaseMapC` (the named record of the first-step data: `z₁`, `R`, `geo`, `cs`, `P`,
`sf`, `κK`, `SD`, `KD`, `KDgam`, `B`, `St`, `vc`, `Ev` with the canonical constants of `BaseConsts`),
the typing fact `3 ≤ d`, and the named open rows `BaseOpenRows`.  No mathematics is added: the proof is
`basePreStepInput_of_canonical` and `baseFlatStepInput_of_canonical` with `baseSFInput_of_parts`,
`baseFlatSFInput_of_parts` and `baseVacuumInput_of_constants`.  The gap to the blocker is exactly the
fields of `BaseOpenRows`, one per row of the ladder (`notes`: CLOSING-C):

* T4 `newLevel`, T5 `renorm`, T6 `density`, T7 `remainder`, T8 `coherenceSF`, T9 `bare`: the six
  sub-inputs of the small-field part (`SFNewLevelQ`, `SFRenormQ`, `SFDensityQ`, `SFRemainderQ`,
  `SFCoherenceQ` at `k = 0`, and the facts of the bare density), in both regimes;
* K4 `form`: `BaseFormInput` / `BaseFlatFormInput` (`D1PreForm2`, the first density as the sum over
  histories);
* K5 `bdry`: `BaseBdryInput` / `BaseFlatBdryInput` (the boundary terms `ℬ^{(1)}`);
* K6 `corr`: `BaseCorrInput` (the coefficient limit `D1CorrLim`);
* K7 `coherence`: `BaseCoherenceInput` (torus independence of the large-field half);
* K8 `vacuum`: the hypothesis of `baseVacuumInput_of_constants` (regime (A) only).
-/

@[expose] public section

open MeasureTheory Balaban Balaban.LargeField Balaban.LargeField.Def7 Balaban.LargeField.Def7v2
  Balaban.SmallField Balaban.SmallField.Def6 Balaban.SmallField.Def6v2 Balaban.Fluctuation
  Balaban.Localization Balaban.Background Balaban.Multiscale RegionHistory

namespace Balaban.RootFSpine

section Close

variable (d N : ℕ) (T : ℝ → ℝ → Typing) (P6 : ℝ → ℝ → Def6.Consts)
  (C7 : ℝ → ℝ → Consts7) (PB : ℝ → ℝ → BudgetConsts) (cs₀ : ℝ → ℝ → OpConsts)
  (M1 c : ℝ → ℝ → ℕ) (rH ϱ : ℝ → ℝ → ℝ)

/-- **The named open rows of the base step** for a first-step map `Γ` (see the file docstring for
the ladder identifiers).  A `Prop` structure: each field is a source statement of one row, in the form
of the landed sub-input it is consumed by. -/
structure BaseOpenRows (Γ : BaseMapC d N T C7 PB cs₀ M1 c ϱ) : Prop where
  /-- T4, regime (A): the new level of the small-field data -/
  newLevelA : BaseSFNewLevelInput d N T P6 C7 cs₀ ϱ (fun k => 1 ≤ k) Γ.toMap
  /-- T5, regime (A): the renormalization conditions and coefficient bounds -/
  renormA : BaseSFRenormInput d N T P6 C7 cs₀ ϱ P6 (fun k => 1 ≤ k) Γ.toMap
  /-- T6, regime (A): the density identity on the small-field region -/
  densityA : BaseSFDensityInput d N T P6 C7 cs₀ ϱ (fun k => 1 ≤ k) Γ.toMap
  /-- T7, regime (A): the remainder bound -/
  remainderA : BaseSFRemainderInput d N T P6 C7 cs₀ ϱ
    (fun κ c₉ => preFac ((P6 κ c₉).m₀ + (C7 κ c₉).m₁)) (fun k => 1 ≤ k) Γ.toMap
  /-- T8, regime (A): the torus coherence of the small-field half -/
  coherenceSFA : BaseSFCoherenceInput d N T P6 C7 cs₀ ϱ (fun k => 1 ≤ k) Γ.toMap
  /-- T9, regime (A): the facts of the bare density -/
  bareA : BaseSFBareInput d N T C7 cs₀ ϱ (fun k => 1 ≤ k) Γ.toMap
  /-- T4, regime (B) -/
  newLevelB : BaseSFNewLevelInput d N T P6 C7 cs₀ ϱ (fun k => k = 0) Γ.toMap
  /-- T5, regime (B), at the constants `massOne P6` -/
  renormB : BaseSFRenormInput d N T P6 C7 cs₀ ϱ (fun κ c₉ => massOne (P6 κ c₉)) (fun k => k = 0)
    Γ.toMap
  /-- T6, regime (B) -/
  densityB : BaseSFDensityInput d N T P6 C7 cs₀ ϱ (fun k => k = 0) Γ.toMap
  /-- T7, regime (B), with the allowance `1` -/
  remainderB : BaseSFRemainderInput d N T P6 C7 cs₀ ϱ (fun _ _ _ => 1) (fun k => k = 0) Γ.toMap
  /-- T8, regime (B) -/
  coherenceSFB : BaseSFCoherenceInput d N T P6 C7 cs₀ ϱ (fun k => k = 0) Γ.toMap
  /-- T9, regime (B) -/
  bareB : BaseSFBareInput d N T C7 cs₀ ϱ (fun k => k = 0) Γ.toMap
  /-- K4, regime (A): the first density as the sum over histories (`D1PreForm2`) -/
  formA : BaseFormInput d N T P6 C7 cs₀ ϱ (fun k => 1 ≤ k) Γ.toMap
  /-- K4, regime (B) -/
  formB : BaseFlatFormInput d N T P6 C7 cs₀ ϱ Γ.toMap
  /-- K5, regime (A): the boundary terms of rate `3κ/2` -/
  bdryA : BaseBdryInput d N T P6 C7 cs₀ rH ϱ (fun k => 1 ≤ k) Γ.toMap
  /-- K5, regime (B): the boundary terms of rate `κ` -/
  bdryB : BaseFlatBdryInput d N T P6 C7 cs₀ rH ϱ Γ.toMap
  /-- K6, regime (A): the coefficient limit (`D1CorrLim`) -/
  corrA : BaseCorrInput d N T P6 C7 cs₀ ϱ (fun k => 1 ≤ k) Γ.toMap
  /-- K6, regime (B) -/
  corrB : BaseCorrInput d N T P6 C7 cs₀ ϱ (fun k => k = 0) Γ.toMap
  /-- K7, regime (A): torus independence of the large-field half, at the scale `1` -/
  coherenceA : BaseCoherenceInput d N T C7 cs₀ ϱ 1 (fun k => 1 ≤ k) Γ.toMap
  /-- K7, regime (B), at the scale `2` -/
  coherenceB : BaseCoherenceInput d N T C7 cs₀ ϱ 2 (fun k => k = 0) Γ.toMap
  /-- K8, regime (A): the flow bound of the vacuum constant `|e| ≤ C_b (log β_0 + 1)` and the
  vacuum constants of the step data (the hypothesis of `baseVacuumInput_of_constants`) -/
  vacuum : BaseImageInput d N T C7 cs₀ ϱ (fun k => 1 ≤ k) Γ.toMap fun κ c₉ _ _ _ _ _ _ Γ =>
      ∃ e : ℝ, (∀ k, Γ.Ev k = if k = 0 then e else 0) ∧
        |e| ≤ (cs₀ κ c₉).Cb * (Real.log (Γ.sf.β 0) + 1) ∧
        0 ≤ (cs₀ κ c₉).Cb * (Real.log (Γ.sf.β 1) + 1) ∧
        ∀ (nK : ℕ) [NeZero nK], ∃ ep epp : ℝ,
          (∀ a, (Γ.SD nK).vacE 0 a = e ∧ (Γ.SD nK).vacEpp 0 a = e + ep ∧
            (Γ.SD nK).vacEppp 0 a = e + epp) ∧
          ∀ k a, (Γ.SD nK).vacE (k + 1) a = 0 ∧ (Γ.SD nK).vacEpp (k + 1) a = 0 ∧
            (Γ.SD nK).vacEppp (k + 1) a = 0

variable {d N T P6 C7 PB cs₀ M1 c rH ϱ}

/-- **The base steps from the named rows (F0).**  Given the prefix, a first-step map with the
canonical constants and the named open rows, both `BasePreStepInput` (regime (A)) and
`BaseFlatStepInput` (regime (B)) hold. -/
theorem baseSteps_of_named {δ : ℝ} (hd : 3 ≤ d) (hP : PrefixInput d δ T P6 C7 PB cs₀ M1 c ϱ)
    (Γ : BaseMapC d N T C7 PB cs₀ M1 c ϱ) (rows : BaseOpenRows d N T P6 C7 PB cs₀ M1 c rH ϱ Γ) :
    BasePreStepInput d N T P6 C7 PB cs₀ M1 c rH ϱ ∧
      BaseFlatStepInput d N T P6 C7 PB cs₀ M1 c rH ϱ := by
  have hL : ∀ κ, 0 < κ → ∀ c₉, 0 < c₉ → 3 ≤ (T κ c₉).L := fun κ hκ c₉ hc₉ => (hP κ hκ c₉ hc₉).1
  have ha1 : ∀ κ, 0 < κ → ∀ c₉, 0 < c₉ → 1 < (cs₀ κ c₉).aKer :=
    fun κ hκ c₉ hc₉ => (hP κ hκ c₉ hc₉).2.1
  have ha2 : ∀ κ, 0 < κ → ∀ c₉, 0 < c₉ → (cs₀ κ c₉).aKer < 3 / 2 :=
    fun κ hκ c₉ hc₉ => (hP κ hκ c₉ hc₉).2.2.1
  have hadm : ∀ κ, 0 < κ → ∀ c₉, 0 < c₉ → (P6 κ c₉).Admissible d (T κ c₉).L :=
    fun κ hκ c₉ hc₉ => (hP κ hκ c₉ hc₉).2.2.2.2.2.2.2.2.1
  refine ⟨basePreStepInput_of_canonical hP Γ
    (baseSFInput_of_parts (fun k hk => hk) hd hL ha1 ha2 hadm Γ.toMap rows.newLevelA rows.renormA
      rows.densityA rows.remainderA rows.coherenceSFA rows.bareA)
    rows.corrA rows.formA rows.bdryA rows.coherenceA
    (baseVacuumInput_of_constants d N T C7 cs₀ ϱ (fun k => 1 ≤ k) Γ.toMap rows.vacuum),
    baseFlatStepInput_of_canonical hP Γ
    (baseFlatSFInput_of_parts hd hL ha1 ha2 hadm Γ.toMap rows.newLevelB rows.renormB rows.densityB
      rows.remainderB rows.coherenceSFB rows.bareB)
    rows.corrB rows.formB rows.bdryB rows.coherenceB⟩

end Close

end Balaban.RootFSpine
