/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Spine.RVacuumTie
public import Balaban.LargeField.Operators.StepVacuumVolume

/-!
# What the retie of a record costs (A4-2v)

For step data `SD` with its own vacuum constants `E^SD_k, E^SD″_k, E^SD‴_k`, `b⁰_k = b_k + stepVacuumTerm(E^SD)`
obeys `b0_bound`. Replacing the constants by those of a flow `E_k, E_k + δ″_k, E_k + δ‴_k`
(`StepData.retie`) changes `b⁰_k` by the vacuum term of the differences. This file proves the exact
cost: `‖b_k + stepVacuumTerm(flow)‖ ≤ (C_b log β_k + C_b B₀)|Z_{k+1} ∖ Z_k| + D V`, where `D` bounds
the three differences and `V = stepVacuumVolume`. The extra term `D V` is not absorbed by the
constant of `VacuumB0Bound`; see `notes/phase1/SPINE.md`, A4-2v.
For step data already tied to the flow (`PreRec.vacTie`) the differences vanish, `D = 0`
(`vacuumB0Bound_of_tie`), which proves `RVacuumB0Input` (`rVacuumB0Input`).
-/

@[expose] public section

namespace Balaban.RootFSpine

open MeasureTheory Balaban Balaban.LargeField Balaban.LargeField.Def7 Balaban.LargeField.Def7v2
  Balaban.SmallField Balaban.SmallField.Def6v2 Balaban.Multiscale RegionHistory

section Cost

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 : ℕ} {M K : ℕ} [NeZero M]
  [NeZero S.L] {N : ℕ} {geo : Geo S n R M} {cs : OpConsts}
  {κs : ℕ → LocalHistory S n M K → ℝ}

omit [∀ k, NeZero (n k)] [NeZero M] [NeZero S.L] in
/-- The vacuum term is linear in the three constants. -/
theorem stepVacuumTerm_sub (a : LocalHistory S n M K) (k : ℕ) (E₁ E₂ E₃ F₁ F₂ F₃ : ℝ) :
    stepVacuumTerm a k E₁ E₂ E₃ - stepVacuumTerm a k F₁ F₂ F₃ =
      stepVacuumTerm a k (E₁ - F₁) (E₂ - F₂) (E₃ - F₃) := by
  unfold stepVacuumTerm; ring

/-- **The cost of the retie.**  If the flow constants differ from the constants of the step data by
at most `D`, then `‖b_k + stepVacuumTerm(flow)‖ ≤ (C_b log β_k + C_b B₀)|Z_{k+1} ∖ Z_k| + D V`. -/
theorem norm_b_add_flowVacuumTerm_le (SD : StepData k0 geo cs N κs) (H : RegionHistory S n R k0 K)
    (hH : H.Admissible) (k : ℕ) (Z' : H.Comp (k + 1))
    (o : OutT N R (H.localHistory M K (k + 1) Z') (k + 1))
    (x : NewCfg N (H.localHistory M K (k + 1) Z') k) (hv : EuclideanSpace ℝ (Fin N))
    (g : GIdx S n M K N → ℂ) (hg : g ∈ l1Ball (GIdx S n M K N))
    (hchi : ChiNewAt geo cs H k Z' o x) (E dpp dppp D : ℝ)
    (h1 : |E - SD.vacE k (H.localHistory M K (k + 1) Z')| ≤ D)
    (h2 : |E + dpp - SD.vacEpp k (H.localHistory M K (k + 1) Z')| ≤ D)
    (h3 : |E + dppp - SD.vacEppp k (H.localHistory M K (k + 1) Z')| ≤ D) :
    ‖(SD.ker k (H.localHistory M K (k + 1) Z')).b o x hv g +
        (stepVacuumTerm (H.localHistory M K (k + 1) Z') k E (E + dpp) (E + dppp) : ℂ)‖ ≤
      (cs.Cb * Real.log (cs.beta k) + cs.Cb * cs.B0) *
        volScale S (k + 1) {z | z ∈ (H.localHistory M K (k + 1) Z').Z (k + 1) ∧
          z ∉ (H.localHistory M K (k + 1) Z').Z k} +
        D * stepVacuumVolume (H.localHistory M K (k + 1) Z') k := by
  have hid : (SD.ker k (H.localHistory M K (k + 1) Z')).b o x hv g + (stepVacuumTerm (H.localHistory M K (k + 1) Z') k E (E + dpp) (E + dppp) : ℂ) =
      SD.b0 k (H.localHistory M K (k + 1) Z') o x hv g + (stepVacuumTerm (H.localHistory M K (k + 1) Z') k (E - SD.vacE k (H.localHistory M K (k + 1) Z'))
        (E + dpp - SD.vacEpp k (H.localHistory M K (k + 1) Z')) (E + dppp - SD.vacEppp k (H.localHistory M K (k + 1) Z')) : ℂ) := by
    rw [← SD.b_add_vac k (H.localHistory M K (k + 1) Z') o x hv g]
    have h := congrArg Complex.ofReal (stepVacuumTerm_sub (H.localHistory M K (k + 1) Z') k E (E + dpp) (E + dppp)
      (SD.vacE k (H.localHistory M K (k + 1) Z')) (SD.vacEpp k (H.localHistory M K (k + 1) Z')) (SD.vacEppp k (H.localHistory M K (k + 1) Z')))
    push_cast at h
    linear_combination h
  rw [hid]
  have hb := norm_stepVacuumTerm_ref_sub_le (H.localHistory M K (k + 1) Z') k (-(E - SD.vacE k (H.localHistory M K (k + 1) Z')))
    (-(E + dpp - SD.vacEpp k (H.localHistory M K (k + 1) Z'))) (-(E + dppp - SD.vacEppp k (H.localHistory M K (k + 1) Z'))) 0 D (by simpa using h1)
    (by simpa using h2) (by simpa using h3)
  simp only [zero_sub, neg_neg] at hb
  exact (norm_add_le _ _).trans (add_le_add (SD.b0_bound H hH k Z' o x hv g hg hchi) hb)

/-- **`VacuumB0Bound` for step data tied to the flow.**  If the vacuum constants of `SD` are those of
the flow, the differences vanish (`D = 0`) and the cost of the retie is zero: `b⁰_k` of the retied data
is `b⁰_k` of `SD`, bounded by `b0_bound`. -/
theorem vacuumB0Bound_of_tie (SD : StepData k0 geo cs N κs) {E dpp dppp : ℕ → ℝ}
    (hT : SD.VacuumTie Set.univ E dpp dppp) : VacuumB0Bound SD E dpp dppp := by
  intro H hH k Z' o x hv g hg hchi
  have := norm_b_add_flowVacuumTerm_le SD H hH k Z' o x hv g hg hchi (E k) (dpp k) (dppp k) 0
    (by rw [hT.E_eq k _ (Set.mem_univ _)]; simp)
    (by rw [hT.Epp_eq k _ (Set.mem_univ _)]; simp)
    (by rw [hT.Eppp_eq k _ (Set.mem_univ _)]; simp)
  simpa using this

end Cost

section Record

variable (d N : ℕ) (T : ℝ → ℝ → Typing) (P6 : ℝ → ℝ → Def6.Consts)
  (C7 : ℝ → ℝ → Consts7) (PB : ℝ → ℝ → BudgetConsts) (cs₀ : ℝ → ℝ → OpConsts)
  (M1 c : ℝ → ℝ → ℕ) (rH ϱ : ℝ → ℝ → ℝ)

/-- **A4-2v′ is proved** (ruling: the vacuum tie is a field of `PreRec`): the estimate of `b⁰_k` for
the flow of every record, from `PreRec.vacTie` and `vacuumB0Bound_of_tie`. -/
theorem rVacuumB0Input : RVacuumB0Input d N T P6 C7 PB cs₀ M1 c rH ϱ := by
  intro κ _ c₉ _
  refine ⟨0, fun β _ ν _ _ h _ kf _ _ _ k _ _ ρ νk rec nK _ => ?_⟩
  obtain ⟨dpp, dppp, hT⟩ := rec.vacTie nK
  exact ⟨dpp, dppp, vacuumB0Bound_of_tie _ hT⟩

end Record

end Balaban.RootFSpine
