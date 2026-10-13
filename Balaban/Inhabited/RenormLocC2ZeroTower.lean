/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.StepTowerRenEnd
public import Balaban.Fluctuation.RenormLocC2Zero

/-!
# `locC2` and `locDφ` at every scale of the shared tower

For `R : StepTowerRenEnd κmin`, at the step `lvTop` of every scale `k ≥ 1`, every torus with
`3 ∣ N₁`, `5 < N₁`, every mass `0 ≤ ν` with `ν · 3^{2(k+1)} ≤ 1`, every solution map `F` of
`IsRenSol` with radius `r_F ≥ r₀`: the principle `locC2` at a block root and the principle `locDφ`
at a site root of the record `RenormExpInput`, at the shared constants `c_K = renCK`, `B = 8 t`,
`ε = t`, `r₀`, `K_loc = 1`, and the same cover (`m₀ = 1`).
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation
  Balaban.Localization Balaban.Localization.LevelPair Balaban.Localization.I5Inhabited
  Balaban.Polymer Balaban.SmallField.Def6 Balaban.Analysis Balaban.Inhabited.LevelStep LocalCover

/-- The two constant inequalities at the shared class constant: `1 ≤ renCK` and (CB) with
`B = 8 t`. -/
theorem StepTowerRen.renCK_facts {κmin : ℝ} (R : StepTowerRen κmin) :
    1 ≤ renCK 3 3 2 R.BG R.κ ∧
    cK2' 3 3 2 (famConst 3 3 R.BG R.κ) *
      ((3 / 2 + 32 / 15 * (3 + (K4 3 3 2 R.BG R.κ + bgK1 3 3 2) * xiC1 3)) * R.t) ≤
      renCK 3 3 2 R.BG R.κ * cK2 3 3 2 * (8 * R.t) := by
  obtain ⟨hC₀⟩ := R.core
  have hK4 := K4_pos (L := 3) (N := 2) (κ := R.κ) hC₀.hS.fam.2.1 (by norm_num : 0 < 3)
  have hX : 0 ≤ xiC1 3 := by unfold xiC1; positivity
  refine ⟨?_, ?_⟩
  · have := renCK_ge (d := 3) (L := 3) (N := 2) (BG := R.BG) (κ := R.κ)
    have := mul_nonneg hK4.le hX
    linarith
  · have h := renCK_mul_ge (d := 3) (L := 3) (N := 2) (BG := R.BG) (κ := R.κ)
    have := mul_le_mul_of_nonneg_right h R.t_pos.le
    nlinarith

end Balaban.Inhabited
