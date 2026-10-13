/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.StepTowerOfG
public import Balaban.Inhabited.StepTowerRen
public import Balaban.Inhabited.StepTowerRenG
public import Balaban.Inhabited.DetOutputTermsWitnessG
public import Balaban.Fluctuation.RenormEndpointSharp
public import Balaban.Fluctuation.RenormPertClass
public import Balaban.Fluctuation.RenormSharedClass
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The shared tower with the endpoint margin

`StepTowerRenEnd κmin` extends `StepTowerRen κmin` by the margin
`K₂'(B_fam) (b_* t r₀) ≤ c₆` (the sharp bound at radius `r₀` fits in the ball `c₆`).
`StepTowerRenG.shrink` (general) shows that all landed margins persist when `r₀` decreases.

At every scale of such a tower, `renDec_one_unique_sharp_scale_of_tower` gives the endpoint
`s = 1` and `renDec_pertClass_scale_of_tower` the class bound at `c_K = renCK`, `B = 8 t`, with no
margin hypothesis.  The radius `r_F` of the renormalized solution is not a field of the record:
`exists_isRenSol` needs, besides the scale (`BgHyp`, `hsm`, `hc1`, all given by `FlCore` at each
scale), the numeric margins `K₁ ξ₁ t + 3 r_F ≤ δ_*` and `8 t r_F ≤ δ_*`, and the first is not
implied by the fields of `StepTower` (`bg1_cap` bounds `K₁ ξ₁ t` by `c₁`, not by `δ_*`).  So the
endpoint theorem takes `IsRenSol … r_F …` and `r₀ ≤ r_F` as scale hypotheses.

Not here: locality and the fields `locC2`, `locDφ`.
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation
  Balaban.Localization Balaban.Localization.LevelPair Balaban.Localization.I5Inhabited
  Balaban.Polymer Balaban.SmallField.Def6 Balaban.Analysis Balaban.Inhabited.LevelStep LocalCover Filter Topology

/-- **The coefficient `b_* t` of the sharp bound is nonnegative, general tower.** -/
theorem StepTowerRenG.coef_nonneg {d L N : ℕ} [NeZero L] {κmin : ℝ}
    (R : StepTowerRenG d L N κmin) :
    0 ≤ (3 / 2 + 32 / 15 * (3 + (K4 d L N R.BG R.κ + bgK1 d L N) * xiC1 d)) * R.t := by
  obtain ⟨hC₀⟩ := R.core
  have hd : 0 < d := by have := R.hd; omega
  have hK4 := K4_pos (L := L) (N := N) (κ := R.κ) hC₀.hS.fam.2.1 hd
  have hK1 := bgK1_pos d L N
  have hX : 0 ≤ xiC1 d := by unfold xiC1; positivity
  have := R.t_pos
  positivity

/-- The coefficient `b_* t` of the sharp bound is nonnegative at the tower constants. -/
theorem StepTowerRen.coef_nonneg {κmin : ℝ} (R : StepTowerRen κmin) :
    0 ≤ (3 / 2 + 32 / 15 * (3 + (K4 3 3 2 R.BG R.κ + bgK1 3 3 2) * xiC1 3)) * R.t :=
  R.toG.coef_nonneg

/-- The shared tower with the renormalization margins and the endpoint margin. -/
structure StepTowerRenEnd (κmin : ℝ) extends StepTowerRen κmin where
  end_margin : cK2' 3 3 2 (famConst 3 3 BG κ) *
    ((3 / 2 + 32 / 15 * (3 + (K4 3 3 2 BG κ + bgK1 3 3 2) * xiC1 3)) * t * r₀) ≤ c6 3 3 2

/-- **The `FlCore` of the general tower at a scale.** -/
theorem StepTowerG.flCore_scale {d L N : ℕ} [NeZero L] {κmin : ℝ}
    (T : StepTowerG d L N κmin) (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁] (hN : 5 < N₁)
    {ν : ℝ} (hν0 : 0 ≤ ν) (hν : ν * (L : ℝ) ^ (2 * (k + 1)) ≤ 1) :
    FlCore N (lvTopG d L N₁ T.m₁ k (rhoSepG d L T.m₁))
      (lvLowG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) 1 ν T.c T.BG T.κ T.t (levelKc d L)
      (Cchi d L) T.c₂ T.BG₂ T.t :=
  flCore_stepG T.hd T.hL T.m₁_four (Classical.choice T.core) hk hN hν0 hν

/-- The `FlCore` of the tower at a scale. -/
theorem StepTowerRen.flCore_scale {κmin : ℝ} (R : StepTowerRen κmin) (k : ℕ) (hk : 1 ≤ k)
    (N₁ : ℕ) [NeZero N₁] (hN : 5 < N₁) {ν : ℝ} (hν0 : 0 ≤ ν)
    (hν : ν * 3 ^ (2 * (k + 1)) ≤ 1) :
    FlCore 2 (lvTop N₁ R.m₁ k (rhoSep R.m₁)) (lvLow N₁ R.m₁ k (rhoSep R.m₁)) 1 ν R.c
      R.BG R.κ R.t (levelKc 3 3) (Cchi 3 3) R.c₂ R.BG₂ R.t := by
  have h := R.toG.toStepTowerG.flCore_scale k hk N₁ hN hν0 (by simpa using hν)
  rw [rhoSepG_three] at h
  exact h

end Balaban.Inhabited
