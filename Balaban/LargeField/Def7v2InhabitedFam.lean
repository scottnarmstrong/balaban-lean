/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Def7v2Inhabited
public import Balaban.LargeField.Def7v2Basic
import Mathlib.Tactic.Linarith

/-!
# Def-7 v2: inhabitation of the flat and family classes, `Nonempty` theorems -- DRAFT

`wIsRepFlat2` (at `ν₀ = 1/(27β)`, `k₀ = k̂_f = 1`), `wIsRepFam2`, `wIsRepFamPre2`, and the
`Nonempty` theorems (hard rule 10) for every new structure of `Def7v2Form`, `Def7v2Class`,
`Def7v2Variants`.  `IsRep2WithInterface` is not inhabited (see `Def7v2Inhabited`).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField.Def7v2.Wit

open MeasureTheory Balaban RegionHistory Balaban.SmallField Balaban.SmallField.Def6
  Balaban.SmallField.Def6v2 Balaban.Background Balaban.LargeField.Def7
  Balaban.LargeField.Def7.Wit Filter Topology

/-- **`IsRep^♭2_1` is inhabited**: at `ν₀ = 1/(27β)` (`k₀ = 1`) with `k̂_f = 1`. -/
theorem wIsRepFlat2 (rH : ℝ) :
    IsRepFlat2 wS wR (kZero wS.d wS.L wβ wν₀) 1 27 2 wGeoF (wCs wν₀ (kZero wS.d wS.L wβ wν₀))
      (budgetConsts wβ) wP6 wC7 wβ wν₀ whv rH 1 1 wM6 le_rfl
      (wFam2 wν₀ (kZero wS.d wS.L wβ wν₀) (1 + 1))
      (wRho2 wν₀ (kZero wS.d wS.L wβ wν₀) (1 + 1)) (wSt wν₀) wVc where
  range := kZero_le_one wν₀_pos (by nlinarith [wν₀_mul])
  coh := wCoh2 wν₀
  field := wField2 wν₀ _
  complete := fun nK _ => wHist_complete _ _ nK
  form := fun nK _ => wForm2 wν₀ _ _ nK
  corr := wD1CorrLim wν₀ 3 whv
  sfData := (wSF2_D2 wν₀ wν₀_pos wν₀_nine _ 3 (fun _ => 1) (fun _ => zero_le_one)).toFlat2
  pin := fun nK _ => wPin wν₀ _ _ (1 + 1) le_rfl nK
  opBound := fun nK _ => wOpBound wν₀ _ _ (1 + 1) nK
  budget := fun nK _ => by
    have hk : kZero wS.d wS.L wβ wν₀ = 1 := kZero_wν₀
    have hl := wS_lam_one_le 1
    have hcH : 0 ≤ wS.cH := wS_ok.cH_nonneg
    refine (wRep wν₀ _ (1 + 1) nK).budgetFlat_of_LF2 wS_good
      (budgetSetup wβ wν₀ wβ_gt wν₀_pos wβ_spec.2.2) (wPin wν₀ _ _ (1 + 1) le_rfl nK)
      (by norm_num) (by rw [hk]) le_rfl ?_ ?_ (by rw [hk]) le_rfl le_rfl (by norm_num)
    · rw [hk]; push_cast; linarith
    · rw [hk]
      have : ((wS.d : ℕ) : ℝ) = 3 := by norm_num [wS, setting, typing, typing0]
      rw [this]
      linarith
  bdry := fun nK _ => wBdry2 wν₀ _ _ nK _ _ _ _ _ _ _ _ one_pos rH
  coherent := wSF2_D8 wν₀ 3
  coeff := (wSF2_D9 wν₀ wν₀_pos wν₀_nine 3 _ (one_le_kZero wν₀_pos wν₀_mul.le)).toFlat
    (witnessConsts_admissible one_pos)

theorem wFamCont2 (r : ℕ) :
    FamCont wP6 (fun ν => (wFam2 ν (kZero wS.d wS.L wβ ν) r).sf) where
  runLim := fun j _ =>
    ⟨⟨_, tendsto_const_nhds⟩,
      ⟨0 * 9 ^ j, (((continuous_id.mul continuous_const).tendsto (0 : ℝ)).mono_left
        nhdsWithin_le_nhds)⟩,
      ⟨_, tendsto_const_nhds⟩, ⟨_, tendsto_const_nhds⟩⟩
  vacLim := fun _ => ⟨0, tendsto_const_nhds⟩
  sfLim := fun N₁ _ =>
    { limE := fun _ _ _ => Eventually.of_forall fun _ _ =>
        ⟨0, by simp only [wFam2, wSF2, wTm, pinTerms]; exact tendsto_const_nhds⟩
      limM := fun _ _ _ _ _ => Eventually.of_forall fun _ _ =>
        ⟨0, by simp [wFam2, wSF2, wTm, pinTerms, wCoef_zero]⟩
      limR := fun _ _ _ _ => Eventually.of_forall fun _ _ =>
        ⟨0, by simp only [wFam2, wSF2]; exact tendsto_const_nhds⟩ }

/-- **`IsRepFam2_1` is inhabited** (Definition IV.3.1, second version): the family
`ν ↦ (wFam2 ν, wRho2 ν)`, `0 < ν ≤ ν_*(1)`, horizon `K(ν) = 1`, `k₀(ν) = kZero(β, ν) ≥ 1`. -/
theorem wIsRepFam2 (rH : ℝ) :
    IsRepFam2 wS wR 27 2 (fun _ => 1) (fun _ => wGeoF) (fun ν => wCs ν (kZero wS.d wS.L wβ ν))
      (fun _ => budgetConsts wβ) wP6 wC7 wβ whv rH 1 wM6 (fun _ => le_rfl)
      (fun ν => wFam2 ν (kZero wS.d wS.L wβ ν) (1 + 1))
      (fun ν => wRho2 ν (kZero wS.d wS.L wβ ν) (1 + 1)) (fun ν => wSt ν) (fun _ => wVc) where
  member := fun ν hν0 hν => wIsRep2 ν hν0 (mul_le_of_nuStar hν) rH
  cont := wFamCont2 (1 + 1)

/-- **`IsRepFam2^pre_1` is inhabited.** -/
theorem wIsRepFamPre2 (rH : ℝ) :
    IsRepFamPre2 wS wR 27 2 (fun _ => 1) (fun _ => wGeoF) (fun ν => wCs ν (kZero wS.d wS.L wβ ν))
      (fun _ => budgetConsts wβ) wP6 wC7 wβ whv rH 1 wM6 (fun _ => le_rfl)
      (fun ν => wFam2 ν (kZero wS.d wS.L wβ ν) 1)
      (fun ν => wRhoPre2 ν (kZero wS.d wS.L wβ ν) 1) (fun ν => wSt ν) (fun _ => wVc) where
  member := fun ν hν0 hν => wIsRepPre2 ν hν0 (mul_le_of_nuStar hν) rH
  cont := wFamCont2 1

end Balaban.LargeField.Def7v2.Wit

/-! ### `Nonempty` theorems (hard rule 10) -/

namespace Balaban.LargeField.Def7v2

open Wit Balaban.SmallField Balaban.SmallField.Def6 Balaban.SmallField.Def6v2 Balaban.Background
  Balaban.LargeField.Def7 Balaban.LargeField.Def7.Wit

theorem nonempty_corrCoef : Nonempty (CorrCoef 3) := ⟨wVc⟩

theorem nonempty_d1CorrLim : Nonempty (D1CorrLim (witnessConsts 1).m₀ (wSF2 wν₀ 3) (wSt wν₀) whv
    wVc) := ⟨wD1CorrLim wν₀ 3 whv⟩

theorem nonempty_sfData2 : Nonempty (SFData 3 3 3 1 2 (bgR0 3 3)) := ⟨wSF2 wν₀ 3⟩

theorem nonempty_d2SF2 : Nonempty (D2SF2 wP6 (kZero wS.d wS.L wβ wν₀) (wSF2 wν₀ 3)
    (fun _ => 1)) :=
  ⟨wSF2_D2 wν₀ wν₀_pos wν₀_nine _ 3 (fun _ => 1) (fun _ => zero_le_one)⟩

theorem nonempty_sfFlat2 : Nonempty (SFFlat2 wP6 (kZero wS.d wS.L wβ wν₀) (wSF2 wν₀ 3)) :=
  ⟨(wSF2_D2 wν₀ wν₀_pos wν₀_nine _ 3 (fun _ => 1) (fun _ => zero_le_one)).toFlat2⟩

theorem nonempty_d7Bdry2 (rH : ℝ) : Nonempty (D7Bdry2 (sides_hnn wS.L 1 1) le_rfl
    (wRep wν₀ (kZero wS.d wS.L wβ wν₀) 2 1) (fun A => (A.H.step 1).Z)
    (wFam2 wν₀ (kZero wS.d wS.L wβ wν₀) 2).weights (wCs wν₀ (kZero wS.d wS.L wβ wν₀)).mu
    (wP6.eps wS.d wS.L) (epsOne wS wP6 wC7) (wCs wν₀ (kZero wS.d wS.L wβ wν₀)).nu wC7.B0 wP6.κ
    whv rH) :=
  ⟨wBdry2 wν₀ _ _ 1 _ _ _ _ _ _ _ _ one_pos rH⟩

theorem nonempty_d7Bdry2Post (rH : ℝ) : Nonempty (D7Bdry2Post (wFrame 1) (sides_hnn wS.L 1 1)
    le_rfl (wRep wν₀ (kZero wS.d wS.L wβ wν₀) 2 1) (fun A => (A.H.step 1).Z)
    (wFam2 wν₀ (kZero wS.d wS.L wβ wν₀) 2).weights (wCs wν₀ (kZero wS.d wS.L wβ wν₀)).mu
    (wP6.eps wS.d wS.L) (epsOne wS wP6 wC7) (wCs wν₀ (kZero wS.d wS.L wβ wν₀)).nu wC7.B0 wP6.κ
    whv rH) :=
  ⟨wBdry2Post wν₀ _ _ 1 _ _ _ _ _ _ _ _ _ one_pos rH⟩

/-- **`IsRep2_k` is inhabited** (hard rule 10), at `k₀ = 1`, positive small-field mass and
zero large-field mass (`wIsRep2_mass_split`). -/
theorem nonempty_isRep2 (rH : ℝ) : Nonempty (IsRep2 wS wR (kZero wS.d wS.L wβ wν₀) 1 27 2 wGeoF
    (wCs wν₀ (kZero wS.d wS.L wβ wν₀)) (budgetConsts wβ) wP6 wC7 wβ wν₀ whv rH 1 wM6 le_rfl
    (wFam2 wν₀ (kZero wS.d wS.L wβ wν₀) (1 + 1)) (wRho2 wν₀ (kZero wS.d wS.L wβ wν₀) (1 + 1))
    (wSt wν₀) wVc) :=
  ⟨wIsRep2 wν₀ wν₀_pos wν₀_mul.le rH⟩

/-- **`IsRepPre2_k` is inhabited.** -/
theorem nonempty_isRepPre2 (rH : ℝ) : Nonempty (IsRepPre2 wS wR (kZero wS.d wS.L wβ wν₀) 1 27 2
    wGeoF (wCs wν₀ (kZero wS.d wS.L wβ wν₀)) (budgetConsts wβ) wP6 wC7 wβ wν₀ whv rH 1 wM6
    le_rfl (wFam2 wν₀ (kZero wS.d wS.L wβ wν₀) 1) (wRhoPre2 wν₀ (kZero wS.d wS.L wβ wν₀) 1)
    (wSt wν₀) wVc) :=
  ⟨wIsRepPre2 wν₀ wν₀_pos wν₀_mul.le rH⟩

/-- **`IsRepFlat2_k` is inhabited.** -/
theorem nonempty_isRepFlat2 (rH : ℝ) : Nonempty (IsRepFlat2 wS wR (kZero wS.d wS.L wβ wν₀) 1 27 2
    wGeoF (wCs wν₀ (kZero wS.d wS.L wβ wν₀)) (budgetConsts wβ) wP6 wC7 wβ wν₀ whv rH 1 1 wM6
    le_rfl (wFam2 wν₀ (kZero wS.d wS.L wβ wν₀) (1 + 1))
    (wRho2 wν₀ (kZero wS.d wS.L wβ wν₀) (1 + 1)) (wSt wν₀) wVc) :=
  ⟨wIsRepFlat2 rH⟩

/-- **`IsRepFam2_k` is inhabited.** -/
theorem nonempty_isRepFam2 (rH : ℝ) : Nonempty (IsRepFam2 wS wR 27 2 (fun _ => 1)
    (fun _ => wGeoF) (fun ν => wCs ν (kZero wS.d wS.L wβ ν)) (fun _ => budgetConsts wβ) wP6 wC7
    wβ whv rH 1 wM6 (fun _ => le_rfl) (fun ν => wFam2 ν (kZero wS.d wS.L wβ ν) (1 + 1))
    (fun ν => wRho2 ν (kZero wS.d wS.L wβ ν) (1 + 1)) (fun ν => wSt ν) (fun _ => wVc)) :=
  ⟨wIsRepFam2 rH⟩

/-- **`IsRepFamPre2_k` is inhabited.** -/
theorem nonempty_isRepFamPre2 (rH : ℝ) : Nonempty (IsRepFamPre2 wS wR 27 2 (fun _ => 1)
    (fun _ => wGeoF) (fun ν => wCs ν (kZero wS.d wS.L wβ ν)) (fun _ => budgetConsts wβ) wP6 wC7
    wβ whv rH 1 wM6 (fun _ => le_rfl) (fun ν => wFam2 ν (kZero wS.d wS.L wβ ν) 1)
    (fun ν => wRhoPre2 ν (kZero wS.d wS.L wβ ν) 1) (fun ν => wSt ν) (fun _ => wVc)) :=
  ⟨wIsRepFamPre2 rH⟩

/-- The class `𝓡2_k(𝖼)` is nonempty. -/
theorem repClass2_nonempty (rH : ℝ) : (RepClass2 wS wR (kZero wS.d wS.L wβ wν₀) 1 27 2 wGeoF
    (wCs wν₀ (kZero wS.d wS.L wβ wν₀)) (budgetConsts wβ) wP6 wC7 wβ wν₀ whv rH 1 (bgR0 3 3)
    wM6 le_rfl).Nonempty :=
  ⟨_, (wIsRep2 wν₀ wν₀_pos wν₀_mul.le rH).mem_repClass2⟩

end Balaban.LargeField.Def7v2
