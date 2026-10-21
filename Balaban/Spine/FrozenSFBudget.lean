/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Spine.BudgetSetupOfRun
public import Balaban.Spine.PrefixBudget
public import Balaban.LargeField.Def7Basic

/-!
# The budget (H6♭) of the frozen successor (A4f-1, part 4)

`frozenBudget_of_pin`: the large-field data of the frozen successor at the scale `k + 1` (no hull,
no operation `R`) satisfy (H6♭) at the horizon `k̂_f` as soon as their pins are those of the pre-`R`
exponents (`D4Pin (k + 2)`): `Rep.budgetFlat_of_LF2_trunc` (LF-2 (ii), the counter history truncated at
`k + 1`) on the budget setup `budgetSetupToOfRun` built from (I.2) up to `k + 1`, the identification of
the budget constants with the running couplings, and the facts of the prefix
(`PrefixBudgetFacts`).
-/

@[expose] public section

namespace Balaban.RootFSpine

open Balaban Balaban.LargeField Balaban.LargeField.Def7 Balaban.Multiscale

/-- **(H6♭) of the frozen successor** (LFR Theorem IV.2.2 (c), LF-2 (ii)): for `k₀ ≤ k + 1`,
`1 ≤ k + 1`, `k + 1 ≤ K`, `k < k̂_f`, a representation at the scale `k + 1` whose pins are those of the
pre-`R` exponents, whose budget constants are tied to the running couplings `sf.β` up to `k + 1`
and to the outer constants `PB`, with (I.2) up to `k + 1`, satisfies (H6♭). -/
theorem frozenBudget_of_pin {d N : ℕ} {T : Typing} {PB P : BudgetConsts} {a β ν : ℝ}
    {kf k : ℕ} {R : ℕ → ℝ} [NeZero T.M] [NeZero T.L] {nK : ℕ} [NeZero nK]
    {geo : Geo (Setting.mk { T with d := d } (lamHat d T.L β a)) (sides T.L (kf + 1) nK) R T.M}
    {cs : OpConsts} {betas nus : ℕ → ℝ}
    (rep : Rep (Setting.mk { T with d := d } (lamHat d T.L β a)) (sides T.L (kf + 1) nK) R
      (kZero d T.L β ν) (kf + 1) T.M N geo cs P (k + 1))
    (facts : PrefixBudgetFacts d T PB a β ν kf) (hP1 : P.c1 = PB.c1) (hP2 : P.c2 = PB.c2)
    (hP3 : P.H0 = PB.H0) (hbeta : ∀ j ≤ k + 1, P.beta j = betas j)
    (hrun : RunningHypTo d T.L β ν a (1 / 20) betas nus (k + 1))
    (hpin : D4Pin (k + 2) rep) (hk0 : kZero d T.L β ν ≤ k + 1) (hk : k < kf) :
    D6Flat kf rep :=
  rep.budgetFlat_of_LF2_trunc facts.good
    (budgetSetupToOfRun T PB P β ν a (k + 1) betas nus hP1 hP2 hP3 hbeta hrun facts.lam
      facts.H0_pos.le facts.c1_nonneg facts.L_le_M facts.cv_ge)
    hpin facts.H1 facts.H2 hk0 (by omega) (by omega) (by omega) (by omega)

end Balaban.RootFSpine
