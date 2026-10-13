/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.ClassOldCover
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# An obstruction to the decoupled expansion of inherited labels over the whole step set

The per-label expansions `classOldDec_expansion_cover` and `classOldDecObs_expansion_cover` take
`BgSetting N Gp Gk (C.Tm.gs j X) … X₀ X₁f j` and an `X₁f` with underlying set
`X1 Gp C.m₀ j 𝒦X`.  The landed endpoint identities take `Gk = stepG`, the whole step set.  For
`Gk = stepG` (and `1 ≤ k`) the fields `dsX₀` and `hN` of `BgSetting` force `X₁f` to be the whole
torus: every site is a data site of `stepG`, so it lies in `X₀`, and then lies in the ball of
radius `r₀ L^{m₁} · spacing` about itself, which `hN` puts inside `X₁f`.

* `bgSetting_stepG_X₁f_eq_univ`: this statement.
* `bgSetting_stepG_X1_eq_univ`: hence `X1 Gp m₀ j 𝒦X` is the whole torus whenever the hypotheses of
  the cover expansions hold with `Gk = stepG`.

So the setting hypotheses `hB` of the cover expansions with `Gk = stepG` cannot be produced from a
step tower unless `X1 Gp m₀ j 𝒦X` is the whole torus.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Localization Balaban.Multiscale Balaban.Background Balaban.SmallField Finset

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}

/-- **`BgSetting` with `Gk = stepG` forces `X₁f` to be the whole torus** (for `1 ≤ k` and a level
generating set `Gp`). -/
theorem bgSetting_stepG_X₁f_eq_univ
    {Gp : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ} (hG' : IsLevel Gp (k + 1)) (hk : 1 ≤ k)
    {Gj : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ} {a₁ ν c BG κ r₀ eps δ₃ : ℝ}
    {X₀ X₁f : Finset (CTorus d L N₁ m₁ (k + 1))} {j₁ : ℕ}
    (hB : BgSetting N Gp (stepG d L N₁ m₁ k ϱ) Gj a₁ ν c BG κ r₀ eps δ₃ X₀ X₁f j₁) :
    X₁f = Finset.univ := by
  refine Finset.eq_univ_of_forall fun y => ?_
  have hy0 : y ∈ X₀ := hB.dsX₀ y ((mem_dataSites _).2 (Or.inl (by simp [stepG, Def6.levelGS, hk])))
  have hd : (3 : ℝ) ≤ d := by exact_mod_cast hB.Sp.hd
  have hL0 : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hr : 0 < r₀ := lt_of_lt_of_le (by positivity) hB.hr₀
  have hsp : 0 < Gp.spacing y := by
    rw [hG'.spacing_eq]; positivity
  refine hB.hN y hy0 (by rw [hG'.Ω_one]; exact Finset.mem_univ _) y ?_
  rw [Green.torusDist_self_eq_zero]
  positivity

/-- **The cover expansions with `Gk = stepG` force `X1 Gp m₀ j 𝒦X` to be the whole torus.** -/
theorem bgSetting_stepG_X1_eq_univ
    {Gp : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ} (hG' : IsLevel Gp (k + 1)) (hk : 1 ≤ k)
    {Gj : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ} {a₁ ν c BG κ r₀ eps δ₃ : ℝ}
    {X₀ X₁f : Finset (CTorus d L N₁ m₁ (k + 1))} {j₁ m₀ : ℕ}
    {𝒦X : Set (CTorus d L N₁ m₁ (k + 1))}
    (hB : BgSetting N Gp (stepG d L N₁ m₁ k ϱ) Gj a₁ ν c BG κ r₀ eps δ₃ X₀ X₁f j₁)
    (hX₁ : (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) = X1 Gp m₀ j₁ 𝒦X) :
    X1 Gp m₀ j₁ 𝒦X = Set.univ := by
  rw [← hX₁, bgSetting_stepG_X₁f_eq_univ hG' hk hB]
  simp

end Balaban.Fluctuation
