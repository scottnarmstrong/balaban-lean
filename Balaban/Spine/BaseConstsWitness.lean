/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Spine.BaseConsts
public import Balaban.Spine.Witness

/-!
# The kept data of the first step, and `BaseRawC` is inhabited (rule 10)

* `baseKD`: the kept data of the first step. No component is ripe, hence none is kept, at the scale
  `1` (LFR Lemma II.7.2 (c), Lemma II.7.7 (c)), so the kept kernels are those of the empty kept
  set (zero kernels), with `C_dec ≡ 5` and the kept costs `γ_i = log 5 + A'_3 λ̂_i^{p_R}`
  (LFR Definition III.5.2, `GamConst`). The kept exponent `κ` is not forced: with zero kernels the
  bound (1.26) of `KeptData` holds for every `κ`, so `baseKD` takes it as a parameter.
* `baseKD_gam`: the `KDgam` field of `BaseRaw`/`BaseRawC` for `baseKD`.
* `baseRawC_nonempty`: `BaseRawC` is inhabited at the witness configuration of `Spine/Witness.lean`
  (`d = L = 3`, `N = 2`, `M = 27 = c M₁`, `c = 27`, `M₁ = 1`, horizon `kf = 0`, the witness
  small-field data, zero step data, zero boundary terms). The horizon `kf ≥ 1` is not covered: the
  zero step data have `K ≤ 1` (the field `quiet` of `StepData` forces the quiet kernel at the
  quiet steps `k ≥ 1` of the history, which is not zero), so `kf ≥ 1` needs step data for the quiet
  steps, which is the provider's work.
-/

@[expose] public section

open MeasureTheory Balaban Balaban.LargeField Balaban.LargeField.Def7 Balaban.LargeField.Def7.Wit
  Balaban.LargeField.Def7v2 Balaban.LargeField.Def7v2.Wit Balaban.SmallField Balaban.Background
  RegionHistory

namespace Balaban.RootFSpine

section Kept

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K M : ℕ} [NeZero M]
  [NeZero S.L] {N : ℕ}

/-- **The kept data of the first step** (LFR Lemma II.7.2 (c), Lemma II.7.7 (c), Definition
III.5.2): the kept kernels are zero, `C_dec ≡ 5`, `γ_i = log 5 + A'_3 λ_i^{p_R}`; `κ` is the kept
exponent. -/
noncomputable def baseKD (geo : Geo S n R M) (cs : OpConsts)
    (κ : ℕ → LocalHistory S n M K → ℝ) : KeptData k0 geo cs N κ S.lam :=
  zeroKeptData geo cs κ S.lam

/-- The kept costs of `baseKD` are the constants `γ_i` of LFR Definition III.5.2 (`GamConst`). -/
theorem baseKD_gam (geo : Geo S n R M) (cs : OpConsts) (κ : ℕ → LocalHistory S n M K → ℝ)
    (i : ℕ) (l : Fin 5) :
    (baseKD (k0 := k0) (N := N) geo cs κ).gam i l = Real.log 5 + S.A3' * S.lam i ^ S.pR :=
  add_comm _ _

end Kept

/-- **`BaseRawC` is inhabited** (rule 10), at the witness configuration: `d = L = 3`, `N = 2`,
`M = 27 = 27 · 1`, horizon `kf = 0`, the witness small-field data, the zero step data
(`zeroStepData`, `C_b = 0`), `baseKD`, zero boundary terms. -/
theorem baseRawC_nonempty [NeZero typing.L] [NeZero typing.M] :
    Nonempty (BaseRawC 3 2 typing wC7 (bgR0 3 3) wβ wν₀ 0 (wCs wν₀ (kZero 3 3 wβ wν₀))
      (budgetConsts wβ) 1 27) :=
  ⟨{ ok := spineSetting_eq_wS ▸ wS_ok
     hM := by norm_num [typing, typing0]
     hc := by norm_num
     z₁ := 1
     sf := wSF2 wν₀ wC7.m₁
     κK := fun _ _ => kappaStepLoc (K := 0 + 1) _ (baseBudgetConsts (budgetConsts wβ)
       (wSF2 wν₀ wC7.m₁)) typing.M
     SD := fun _ _ => zeroStepData _ _ le_rfl rfl _
     KD := fun _ _ => baseKD _ _ _
     KDgam := fun _ _ i l => baseKD_gam _ _ _ i l
     B := fun _ _ _ _ _ _ _ => 0
     St := wSt wν₀
     vc := wVc
     Ev := fun _ => 0 }⟩

end Balaban.RootFSpine
