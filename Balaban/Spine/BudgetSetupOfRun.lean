/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Spine.RootFInputs
public import Balaban.Spine.TransferAnalysis

/-!
# The budget setup of a class member from its running constants

`budgetSetupToOfRun`: the hypotheses of Lemma II.5.12 up to the scale `c` (`BudgetSetupTo`), on the
a priori setting `Setting.mk {T with d := d} (lamHat d T.L β a)`, from (I.2) up to `c` for the running
couplings, the identification of the budget constants `P.beta j` with them, and the analytic
conditions of the prefix. It is the construction used by the transfer at `k₀`
(`Spine/Transfer.lean`) and by the frozen steps (`Spine/FrozenSFBudget.lean`).
-/

@[expose] public section

namespace Balaban.RootFSpine

open Balaban Balaban.LargeField Balaban.LargeField.Def7 Balaban.Multiscale

/-- **The budget setup up to the scale `c`** from (I.2) up to `c` for `betas`, `nus`, with
`P.beta j = betas j` for `j ≤ c`, the ties `P.c1 = PB.c1`, `P.c2 = PB.c2`, `P.H0 = PB.H0`, and the
analytic conditions on `λ̂_j`. -/
noncomputable def budgetSetupToOfRun {d : ℕ} (T : Typing) (PB P : BudgetConsts) (β ν a : ℝ) (c : ℕ)
    (betas nus : ℕ → ℝ) (hP1 : P.c1 = PB.c1) (hP2 : P.c2 = PB.c2) (hP3 : P.H0 = PB.H0)
    (hbeta : ∀ j ≤ c, P.beta j = betas j) (hrun : RunningHypTo d T.L β ν a (1 / 20) betas nus c)
    (hK : ∀ j, AnalyticLamAt (analyticK d T.L T.p0 PB.H0 PB.c2) (lamHat d T.L β a j))
    (hH0 : 0 ≤ PB.H0) (hc1 : 0 ≤ PB.c1) (hLM : T.L ≤ T.M)
    (hcv : (T.M : ℝ) ^ d * (PB.H0 + PB.c1 + 3) ≤ T.cv) :
    BudgetSetupTo (Setting.mk { T with d := d } (lamHat d T.L β a)) P c :=
  { β := β
    ν := ν
    a := a
    ε := 1 / 20
    nuRun := nus
    K := analyticK d T.L T.p0 PB.H0 PB.c2
    lam_eq := fun _ => rfl
    Kd := rfl
    KL := rfl
    Kp0 := rfl
    KH0 := hP3.symm
    Kc2 := hP2.symm
    lam_cond := hK
    H0_nonneg := hP3 ▸ hH0
    c1_nonneg := hP1 ▸ hc1
    L_le_M := hLM
    cv_ge := by rw [hP3, hP1]; exact hcv
    run :=
      { hd := hrun.hd
        hL := hrun.hL
        hβ := hrun.hβ
        hν := hrun.hν
        ha1 := hrun.ha1
        ha2 := hrun.ha2
        hε0 := hrun.hε0
        hε := hrun.hε
        beta_eq := fun j hj => by rw [hbeta j hj]; exact hrun.beta_eq j hj
        nu_eq := hrun.nu_eq } }

end Balaban.RootFSpine
