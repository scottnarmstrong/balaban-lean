/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Spine.BaseStepDataSplice
public import Balaban.Spine.BasePre

/-!
# The vacuum flow of the first step (rulings R5, R5′; P4 (2.1), (2.41), (2.63))

For the step data `StepData.ofZeroSliceQuiet` (the scale-`0` slice spliced with the quiet step data
of the scales `k ≥ 1`) the vacuum constants of the step `k → k + 1` are those of the slice at
`k = 0` and those of the quiet input at `k ≥ 1`
(`ofZeroSliceQuiet_vacE_zero`, `ofZeroSliceQuiet_vacE_succ`). The flow `E` of the first step is the
constant `e` of the slice at the scale `0` and `0` at the scales `k ≥ 1`, where the quiet input has
no vacuum constants (the steps `k ≥ 1` are not reached by the histories up to the scale `1`).
`baseVacuumInput_of_constants` is `BaseVacuumInput` for a first-step map whose step data have these
constants; the only open physical clause is the flow bound `|e| ≤ C_b (log β_0 + 1)`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open MeasureTheory Balaban Balaban.Multiscale Balaban.Background RegionHistory ENNReal
  Balaban.LargeField.Def7

section Constants

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 : ℕ} {M K : ℕ} [NeZero M]
  [NeZero S.L] {N : ℕ} {geo : Geo S n R M} {cs : OpConsts}

/-- The vacuum constants of the splice at the scale `0` are the slice's. -/
theorem StepData.spliceZero_vac_zero {κ1 κs : ℕ → LocalHistory S n M K → ℝ}
    (sl : StepSlice0 k0 geo cs N (κs 0)) (SD₁ : StepData k0 geo cs N κ1) (hg)
    (a : LocalHistory S n M K) :
    (StepData.spliceZero sl SD₁ hg).vacE 0 a = sl.vacE a ∧
      (StepData.spliceZero sl SD₁ hg).vacEpp 0 a = sl.vacEpp a ∧
      (StepData.spliceZero sl SD₁ hg).vacEppp 0 a = sl.vacEppp a := ⟨rfl, rfl, rfl⟩

/-- The vacuum constants of the splice at the scales `k + 1` are those of `SD₁`. -/
theorem StepData.spliceZero_vac_succ {κ1 κs : ℕ → LocalHistory S n M K → ℝ}
    (sl : StepSlice0 k0 geo cs N (κs 0)) (SD₁ : StepData k0 geo cs N κ1) (hg) (k : ℕ)
    (a : LocalHistory S n M K) :
    (StepData.spliceZero sl SD₁ hg).vacE (k + 1) a = SD₁.vacE (k + 1) a ∧
      (StepData.spliceZero sl SD₁ hg).vacEpp (k + 1) a = SD₁.vacEpp (k + 1) a ∧
      (StepData.spliceZero sl SD₁ hg).vacEppp (k + 1) a = SD₁.vacEppp (k + 1) a := ⟨rfl, rfl, rfl⟩

end Constants

section OfSlice

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 : ℕ} {M K : ℕ} [NeZero M]
  [NeZero S.L] {N : ℕ} {geo : Geo S n R M} {cs : OpConsts} [NeZero N]
  (P : BudgetConsts) (c1 c2 : ℝ) (hM : M = S.M)
  (hP1 : c1 ≤ P.c1) (hP2 : c2 ≤ P.c2) (hbeta : ∀ k, cs.beta k = P.beta k)
  (hPlog : ∀ k, 0 ≤ Real.log (P.beta k))
  (sl : StepSlice0 k0 geo cs N (kappaStepLoc (K := K) S P M 0))
  (inp : QuietStepInput' K k0 geo cs N)
  (hz : ∀ k, 0 ≤ cs.z (k + 1)) (hc : ∀ k, 0 ≤ cs.beta k * cs.aKer * (S.L : ℝ) ^ (S.d - 2))
  (hβ : ∀ k, 0 ≤ cs.beta (k + 1)) (haw : ∀ n, 0 ≤ cs.aw n) (hμ : ∀ k, 0 ≤ cs.muAct (k + 1))
  (hbg : ∀ q, BgHyp S.d S.L q (minSep S.L geo.M1) cs.aw (cs.mu q))
  (hbgB : ∀ q, BgHyp S.d S.L q (minSep S.L geo.M1) cs.aw (cs.muBg q))
  (hN : 2 ≤ N) (hc1 : cs.Cb ≤ c1) (hc2 : cs.Cb * cs.B0 ≤ c2)
  (hcpos : ∀ k, 0 < cs.beta k * cs.aKer * (S.L : ℝ) ^ (S.d - 2))
  (hδ : ∀ k, 0 < cs.delta k) (hδ1 : ∀ k, 3 * S.d * S.L * cs.delta k ≤ 1 / 2)
  (hΛ : ∀ k, 3 * S.d * S.L * cShell N * cs.delta k ≤ 1 / 2)
  (hCb : 0 ≤ cs.Cb) (hB0 : 0 ≤ cs.B0)

include hP1 hP2 hbeta hPlog hz hc hβ haw hμ hbg hbgB hN hc1 hc2 hcpos hδ hδ1 hΛ hCb hB0 hM in
/-- **The vacuum constants of the first step's step data**: at the scale `0` those of the slice, at
the scales `k + 1` zero when the quiet input has no vacuum constants (its constants are used on the
quiet-realized histories and are `0` elsewhere). -/
theorem ofZeroSliceQuiet_vac
    (hq : ∀ k a, inp.vacE k a = 0 ∧ inp.vacEpp k a = 0 ∧ inp.vacEppp k a = 0)
    (k : ℕ) (a : LocalHistory S n M K) :
    let SD := StepData.ofZeroSliceQuiet P c1 c2 hM hP1 hP2 hbeta hPlog sl inp hz hc hβ haw hμ hbg
      hbgB hN hc1 hc2 hcpos hδ hδ1 hΛ hCb hB0
    (SD.vacE 0 a = sl.vacE a ∧ SD.vacEpp 0 a = sl.vacEpp a ∧ SD.vacEppp 0 a = sl.vacEppp a) ∧
      (SD.vacE (k + 1) a = 0 ∧ SD.vacEpp (k + 1) a = 0 ∧ SD.vacEppp (k + 1) a = 0) := by
  classical
  refine ⟨⟨rfl, rfl, rfl⟩, ?_⟩
  show (if QuietRealized R k0 (k + 1) a then inp.vacE (k + 1) a else 0) = 0 ∧
    (if QuietRealized R k0 (k + 1) a then inp.vacEpp (k + 1) a else 0) = 0 ∧
    (if QuietRealized R k0 (k + 1) a then inp.vacEppp (k + 1) a else 0) = 0
  refine ⟨?_, ?_, ?_⟩ <;> split_ifs
  · exact (hq _ _).1
  · rfl
  · exact (hq _ _).2.1
  · rfl
  · exact (hq _ _).2.2
  · rfl

end OfSlice

end Balaban.LargeField

namespace Balaban.RootFSpine

open Balaban.LargeField Balaban.LargeField.Def7 Balaban.LargeField.Def7v2 Balaban.SmallField

section Input

variable (d N : ℕ) (T : ℝ → ℝ → Typing) (C7 : ℝ → ℝ → Consts7) (cs₀ : ℝ → ℝ → OpConsts)
  (ϱ : ℝ → ℝ → ℝ)

/-- **`BaseVacuumInput` from the constants of the step data** (rulings R5, R5′; P4 (2.1), (2.41),
(2.63)): the flow `E` of the record is `e` at the scale `0` and `0` at the scales `k ≥ 1`; the
vacuum constants of the step data at the scale `0` are `e`, `e + δ″`, `e + δ‴` (the constants of the
slice, independent of the localized history) and `0` at the scales `k ≥ 1` (`ofZeroSliceQuiet_vac`:
the steps `k ≥ 1` are not reached by the histories up to the scale `1`). The open physical clause
is the flow bound at the scale `0`, `|e| ≤ C_b (log β_0 + 1)` (P4 (2.41); LFR Lemma II.7.7 (b)),
and `C_b (log β_1 + 1) ≥ 0` for the scale `1`. -/
theorem baseVacuumInput_of_constants (Reg : ℕ → Prop) (Γ : BaseMap d N T C7 cs₀ ϱ)
    (h : BaseImageInput d N T C7 cs₀ ϱ Reg Γ fun κ c₉ _ _ _ _ _ _ Γ =>
      ∃ e : ℝ, (∀ k, Γ.Ev k = if k = 0 then e else 0) ∧
        |e| ≤ (cs₀ κ c₉).Cb * (Real.log (Γ.sf.β 0) + 1) ∧
        0 ≤ (cs₀ κ c₉).Cb * (Real.log (Γ.sf.β 1) + 1) ∧
        ∀ (nK : ℕ) [NeZero nK], ∃ ep epp : ℝ,
          (∀ a, (Γ.SD nK).vacE 0 a = e ∧ (Γ.SD nK).vacEpp 0 a = e + ep ∧
            (Γ.SD nK).vacEppp 0 a = e + epp) ∧
          ∀ k a, (Γ.SD nK).vacE (k + 1) a = 0 ∧ (Γ.SD nK).vacEpp (k + 1) a = 0 ∧
            (Γ.SD nK).vacEppp (k + 1) a = 0) :
    BaseVacuumInput d N T C7 cs₀ ϱ Reg Γ := by
  intro κ hκ c₉ hc₉
  obtain ⟨b, hb⟩ := h κ hκ c₉ hc₉
  refine ⟨b, fun β hβ ν hν hνL hh hh1 kf hkf _ _ hreg => ?_⟩
  obtain ⟨e, hE, he, h1, hSD⟩ := hb β hβ ν hν hνL hh hh1 kf hkf hreg
  refine ⟨?_, fun nK _ => ?_⟩
  · intro j hj
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hj with rfl | rfl
    · rw [hE]; simpa using he
    · rw [hE]; simpa using h1
  · obtain ⟨ep, epp, h0, hs⟩ := hSD nK
    refine ⟨fun k => if k = 0 then ep else 0, fun k => if k = 0 then epp else 0, ?_⟩
    refine ⟨fun k a _ => ?_, fun k a _ => ?_, fun k a _ => ?_⟩
    · cases k with
      | zero => rw [(h0 a).1, hE]; simp
      | succ k => rw [(hs k a).1, hE]; simp
    · cases k with
      | zero => rw [(h0 a).2.1, hE]; simp
      | succ k => rw [(hs k a).2.1, hE]; simp
    · cases k with
      | zero => rw [(h0 a).2.2, hE]; simp
      | succ k => rw [(hs k a).2.2, hE]; simp

end Input

end Balaban.RootFSpine
