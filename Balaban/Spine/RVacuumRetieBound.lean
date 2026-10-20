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
-/

@[expose] public section

namespace Balaban.RootFSpine

open Balaban Balaban.LargeField Balaban.LargeField.Def7 RegionHistory

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

end Cost

end Balaban.RootFSpine
