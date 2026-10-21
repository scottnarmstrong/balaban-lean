/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Spine.RootFInputs
public import Balaban.LargeField.Def7v2InhabitedFam

/-!
# The class predicates of the spine are inhabited

Rule 10 for the helper predicates of `Balaban/Spine/RootFInputs.lean`:

* `repClassAt_witness`: `RepClassAt` holds for the landed witness of `IsRep2` (`Def7v2.Wit.wIsRep2`:
  `d = L = 3`, `N = 2`, `M = 27`, `K = k = 1`, zero terms) at `ν = 1/(27β)`, with the running mass
  `ν_0 = ν`; the a priori setting `𝒮[3, typing, β, 5/4]` of the spine is the setting `wS` of the
  witness (`spineSetting_eq_wS`);
* `observableActivities_zero`, `exists_isHorizon` (`Spine/RootF.lean`): the activity clauses hold
  for zero activities, and the horizon exists.

The frozen-regime class `FlatClassAt` (horizon of the family `K = k̂ + 1`) is not covered by the
landed witness `wIsRepFlat2`, which has `K = k̂ = 1` (`notes/phase1/SPINE.md`, non-vacuity). -/

@[expose] public section

namespace Balaban.RootFSpine

open Balaban Balaban.LargeField Balaban.LargeField.Def7 Balaban.LargeField.Def7.Wit
  Balaban.LargeField.Def7v2 Balaban.LargeField.Def7v2.Wit Balaban.SmallField

/-- The a priori setting of the spine at the witness constants is the setting of the witness. -/
theorem spineSetting_eq_wS :
    (Setting.mk { typing with d := 3 }
      (lamHat 3 typing.L wβ (wCs wν₀ (kZero 3 3 wβ wν₀)).aKer) : Setting) = wS := by
  show Setting.mk { typing with d := 3 } (lamHat 3 typing.L wβ (5 / 4)) = setting wβ
  unfold setting
  congr 1
  funext j
  simp only [lamHat, thetaOf]
  have h3 : ((typing.L : ℕ) : ℝ) = 3 := by norm_num [typing, typing0]
  rw [h3]
  norm_num

/-- The large-field data of the witness family are torus coherent: its step and kept kernels, kept
exponents and boundary terms vanish identically. -/
theorem wFam2_lfCoherent (ν : ℝ) (k0 r : ℕ) : LFCoherent (wFam2 ν k0 r) := by
  intro nK₁ nK₂ _ _ c
  refine ⟨?_, ?_, ?_⟩
  · intros
    exact ⟨rfl, rfl⟩
  · intros
    refine ⟨rfl, fun _ => ⟨fun _ _ _ => ⟨fun _ => Set.mem_univ _, fun _ => Set.mem_univ _⟩, ?_⟩⟩
    intros
    exact ⟨rfl, rfl⟩
  · intros
    rfl

/-- The running coefficients of the witness satisfy (I.2) up to the scale `1` (with `γ_j = δ_j = 1`:
`β_j = β 3^j`, `ν_j = ν 9^j`). -/
theorem witness_runningHypTo :
    RunningHypTo 3 3 wβ wν₀ (5 / 4) (1 / 20) wβs (wνs wν₀) 1 := by
  have hβ : 0 < wβ := by have := wβ_gt; linarith
  refine ⟨le_of_lt (by norm_num), by norm_num, hβ, wν₀_pos, by norm_num, by norm_num, by norm_num,
    le_rfl, fun j _ => ⟨1, one_pos, by simp, ?_⟩, fun j _ => ⟨1, one_pos, by simp, ?_⟩⟩
  · simp only [wβs, mul_one]
    norm_num
  · simp only [wνs, mul_one]
    rw [pow_mul]
    norm_num

/-- The body of `RepClassAt` at the witness constants, for any setting equal to the witness setting
`wS` (the setting is generalized so that it can be substituted). -/
theorem repClassAt_witness_aux (rH : ℝ) (S : Setting) (hS : S = wS) [NeZero S.L] :
    ∃ (ρ : ∀ (nK : ℕ) [NeZero nK], (BlockAt S (sides S.L 1 nK) 27 1 1 → EuclideanSpace ℝ (Fin 2)) →
        (GIdx S (sides S.L 1 nK) 27 1 2 → ℂ) → ℂ) (νk : ℝ)
      (hM6 : (27 : ℕ) = S.L ^ (wP6.m₀ + wC7.m₁)) (hkK : 1 ≤ 1) (R : ℕ → ℝ)
      (geo : ∀ (nK : ℕ) [NeZero nK], Geo S (sides S.L 1 nK) R 27) (cs : OpConsts)
      (P : BudgetConsts) (F : RepFam S R (kZero S.d S.L wβ wν₀) 1 27 2 geo cs P 1 wC7.m₁
        (Background.bgR0 3 3))
      (St : ∀ (N₁ : ℕ) [NeZero N₁], Def6v2.SourceTerms S.d S.L N₁ wC7.m₁ 1 2) (vc : CorrCoef S.d),
      (∀ (nK : ℕ) [NeZero nK], (geo nK).M1 = 1 ∧ (geo nK).c = 27) ∧
      cs.aKer = (wCs wν₀ (kZero 3 3 wβ wν₀)).aKer ∧ cs.Cpsi = (wCs wν₀ (kZero 3 3 wβ wν₀)).Cpsi ∧
      cs.Cb = (wCs wν₀ (kZero 3 3 wβ wν₀)).Cb ∧ cs.aw = (wCs wν₀ (kZero 3 3 wβ wν₀)).aw ∧
      P.c1 = (budgetConsts wβ).c1 ∧ P.c2 = (budgetConsts wβ).c2 ∧ P.H0 = (budgetConsts wβ).H0 ∧
      IsRep2 S R (kZero S.d S.L wβ wν₀) 1 27 2 geo cs P wP6 wC7 wβ wν₀ whv rH 1 hM6 hkK F ρ St vc ∧
      F.sf.β 0 = wβ ∧ F.sf.ν 0 = wν₀ ∧ F.sf.ν 1 = νk ∧
      RunningHypTo S.d S.L wβ wν₀ (wCs wν₀ (kZero 3 3 wβ wν₀)).aKer (1 / 20) F.sf.β F.sf.ν 1 ∧
      LFCoherent F ∧ (∃ Ev : ℕ → ℝ, VacuumFlowTo (wCs wν₀ (kZero 3 3 wβ wν₀)).Cb Ev F.sf.β 1) ∧
      (∀ j, 1 ≤ j → j ≤ 1 → 0 < F.sf.z j) ∧ ∀ (nK : ℕ) [NeZero nK], GamConst (F.lf nK) := by
  subst hS
  exact ⟨wRho2 wν₀ (kZero 3 3 wβ wν₀) (1 + 1), wνs wν₀ 1, wM6, le_rfl, wR, wGeoF,
    wCs wν₀ (kZero 3 3 wβ wν₀), budgetConsts wβ, wFam2 wν₀ (kZero 3 3 wβ wν₀) (1 + 1), wSt wν₀,
    wVc, fun _ _ => ⟨rfl, rfl⟩, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    wIsRep2 wν₀ wν₀_pos wν₀_mul.le rH, by simp [wFam2, wSF2, wβs], by simp [wFam2, wSF2, wνs],
    rfl, witness_runningHypTo, wFam2_lfCoherent _ _ _,
    ⟨fun _ => 0, vacuumFlowTo_zero fun _ _ => by
      rw [show (wCs wν₀ (kZero 3 3 wβ wν₀)).Cb = 0 from rfl, zero_mul]⟩, fun _ _ _ => one_pos,
    fun nK _ i l => add_comm _ _⟩

/-- **`RepClassAt` is inhabited**: the witness of `IsRep2` at `ν = 1/(27β)`, horizon `kf = 0`, scale
`k = 1`, with the outer constants of the witness. -/
theorem repClassAt_witness (rH : ℝ) :
    ∃ (ρ : 𝒟[3, 2, typing, wβ, (wCs wν₀ (kZero 3 3 wβ wν₀)).aKer, 0 + 1, 1]) (νk : ℝ),
      @RepClassAt 3 2 typing wP6 wC7 (budgetConsts wβ) (wCs wν₀ (kZero 3 3 wβ wν₀)) 1 27 rH
        (Background.bgR0 3 3) wβ wν₀ whv 0 1 ⟨by norm_num [typing, typing0]⟩
        ⟨by norm_num [typing, typing0]⟩ ρ νk := by
  have : NeZero typing.L := ⟨by norm_num [typing, typing0]⟩
  have : NeZero typing.M := ⟨by norm_num [typing, typing0]⟩
  obtain ⟨ρ, νk, hM6, hkK, R, geo, cs, P, F, St, vc, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, ⟨Ev, hEv⟩, hz, hg⟩ := @repClassAt_witness_aux rH _ spineSetting_eq_wS
      ⟨by norm_num [typing, typing0]⟩
  exact ⟨ρ, νk, ⟨hM6, hkK, R, geo, cs, P, F, St, vc, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, Ev, hEv, hz, hg⟩⟩

/-- The landed witness of `IsRepFlat2` (`wIsRepFlat2`, horizon `k̂ = 1`) with the horizon `k̂ = 0`:
at the scale `k = 1` the two budget clauses (H6♭) coincide, since `W(2, 0) = W(2, 1) = 0`. -/
theorem wIsRepFlat2_khat_zero (rH : ℝ) :
    IsRepFlat2 wS wR (kZero wS.d wS.L wβ wν₀) 1 27 2 wGeoF (wCs wν₀ (kZero wS.d wS.L wβ wν₀))
      (budgetConsts wβ) wP6 wC7 wβ wν₀ whv rH 1 0 wM6 le_rfl
      (wFam2 wν₀ (kZero wS.d wS.L wβ wν₀) (1 + 1))
      (wRho2 wν₀ (kZero wS.d wS.L wβ wν₀) (1 + 1)) (wSt wν₀) wVc := by
  have h := wIsRepFlat2 rH
  refine ⟨h.range, h.coh, h.field, h.complete, h.form, h.corr, h.sfData, h.pin, h.opBound,
    fun nK _ => ?_, h.bdry, h.coherent, h.coeff⟩
  intro A hA c
  have hb := h.budget nK A hA c
  have hW : wS.W (1 + 1) 0 = wS.W (1 + 1) 1 := by simp [Setting.W]
  rw [hW]
  exact hb

/-- The running mass of the witness at the scale `1`: `ν₁ = 9 ν₀ = 1/(3β) ≤ 9/10`. -/
theorem wνs_one_le : wνs wν₀ 1 ≤ 9 / 10 := by
  have h1 := wν₀_mul
  have h2 : 10 < wβ := wβ_spec.1
  have h3 : 0 < wν₀ := wν₀_pos
  unfold wνs
  nlinarith

/-- The body of `FlatClassAt` at the witness constants, for any setting equal to `wS`. -/
theorem flatClassAt_witness_aux (rH : ℝ) (S : Setting) (hS : S = wS) [NeZero S.L] :
    ∃ (ρ : ∀ (nK : ℕ) [NeZero nK], (BlockAt S (sides S.L 1 nK) 27 1 1 → EuclideanSpace ℝ (Fin 2)) →
        (GIdx S (sides S.L 1 nK) 27 1 2 → ℂ) → ℂ) (νk : ℝ)
      (hM6 : (27 : ℕ) = S.L ^ (wP6.m₀ + wC7.m₁)) (hkK : 1 ≤ 1) (R : ℕ → ℝ)
      (geo : ∀ (nK : ℕ) [NeZero nK], Geo S (sides S.L 1 nK) R 27) (cs : OpConsts)
      (P : BudgetConsts) (F : RepFam S R (kZero S.d S.L wβ wν₀) 1 27 2 geo cs P 1 wC7.m₁
        (Background.bgR0 3 3))
      (St : ∀ (N₁ : ℕ) [NeZero N₁], Def6v2.SourceTerms S.d S.L N₁ wC7.m₁ 1 2) (vc : CorrCoef S.d),
      (∀ (nK : ℕ) [NeZero nK], (geo nK).M1 = 1 ∧ (geo nK).c = 27) ∧
      cs.aKer = (wCs wν₀ (kZero 3 3 wβ wν₀)).aKer ∧ cs.Cpsi = (wCs wν₀ (kZero 3 3 wβ wν₀)).Cpsi ∧
      cs.Cb = (wCs wν₀ (kZero 3 3 wβ wν₀)).Cb ∧ cs.aw = (wCs wν₀ (kZero 3 3 wβ wν₀)).aw ∧
      P.c1 = (budgetConsts wβ).c1 ∧ P.c2 = (budgetConsts wβ).c2 ∧ P.H0 = (budgetConsts wβ).H0 ∧
      IsRepFlat2 S R (kZero S.d S.L wβ wν₀) 1 27 2 geo cs P wP6 wC7 wβ wν₀ whv rH 1 0 hM6 hkK F
        ρ St vc ∧
      F.sf.β 0 = wβ ∧ F.sf.ν 0 = wν₀ ∧ F.sf.ν 1 = νk ∧
      RunningHypTo S.d S.L wβ wν₀ (wCs wν₀ (kZero 3 3 wβ wν₀)).aKer (1 / 20) F.sf.β F.sf.ν 1 ∧
      LFCoherent F ∧ νk ≤ 9 / 10 := by
  subst hS
  exact ⟨wRho2 wν₀ (kZero 3 3 wβ wν₀) (1 + 1), wνs wν₀ 1, wM6, le_rfl, wR, wGeoF,
    wCs wν₀ (kZero 3 3 wβ wν₀), budgetConsts wβ, wFam2 wν₀ (kZero 3 3 wβ wν₀) (1 + 1), wSt wν₀,
    wVc, fun _ _ => ⟨rfl, rfl⟩, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    wIsRepFlat2_khat_zero rH, by simp [wFam2, wSF2, wβs], by simp [wFam2, wSF2, wνs],
    rfl, witness_runningHypTo, wFam2_lfCoherent _ _ _, wνs_one_le⟩

/-- **`FlatClassAt` is inhabited**: the witness of `IsRepFlat2` at `ν = 1/(27β)`, horizon `kf = 0`,
scale `k = 1`, with the outer constants of the witness. -/
theorem flatClassAt_witness (rH : ℝ) :
    ∃ (ρ : 𝒟[3, 2, typing, wβ, (wCs wν₀ (kZero 3 3 wβ wν₀)).aKer, 0 + 1, 1]) (νk : ℝ),
      @FlatClassAt 3 2 typing wP6 wC7 (budgetConsts wβ) (wCs wν₀ (kZero 3 3 wβ wν₀)) 1 27 rH
        (Background.bgR0 3 3) wβ wν₀ whv 0 1 ⟨by norm_num [typing, typing0]⟩
        ⟨by norm_num [typing, typing0]⟩ ρ νk :=
  @flatClassAt_witness_aux rH _ spineSetting_eq_wS ⟨by norm_num [typing, typing0]⟩

/-- **`ObservableActivities` is inhabited**: zero activities satisfy all its clauses. -/
theorem observableActivities_zero (d N L M : ℕ) (κ c₉ δ : ℝ) (hc₉ : 0 < c₉) (J kf : ℕ) :
    ObservableActivities d N L M κ c₉ δ J kf (fun _ _ _ _ => 0) := by
  refine ⟨fun _ _ _ => ⟨fun _ _ _ _ => rfl, fun _ _ => analyticOnNhd_const, fun _ _ _ _ _ => rfl,
    fun j _ X _ _ => ?_⟩, fun _ _ _ _ _ _ _ _ _ _ _ _ => rfl⟩
  rw [sub_self, norm_zero]
  have hL : 0 ≤ (L : ℝ) ^ (-((j : ℝ) * (((d : ℝ) - 2) / 2 + δ))) :=
    Real.rpow_nonneg (Nat.cast_nonneg _) _
  have := Real.exp_pos (-κ * (X.card : ℝ) / ((M : ℝ) * (L : ℝ) ^ j) ^ d)
  positivity

end Balaban.RootFSpine
