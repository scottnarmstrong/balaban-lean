/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.StepRegWitness
public import Balaban.SmallField.Def6ContInhabited
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# A witness of the composition-domain inclusion `RayInDomain`

For the step `k = 1` the composed data `ψ_1^{(1)}` of the datum of `ψ^{(1)} + s ψ'` is the datum
itself (`pairRay_one`: the composition of a level with itself is the identity, `κ = 1`).  In the
witness of `StepRegWitness` the datum is `e₀` plus the perturbation `s β_k^{-1/2} C^{1/2} ψ̂`, whose
size is `≤ 2 ‖C^{1/2}‖ / β_k^{1/2}` for `|s| ‖ψ̂‖ < 2`, so for `β_k` large it lies in the ball
around the constant `e₀` of `xiDom_ball_witness`: this puts the pair `(ψ_1^{(1)}, h)` into the
analyticity domain `Ξ^c_1(𝔹_1; 1, ε)` for every polymer.  So `RayInDomain` is inhabited for the
zero class, at `N = 2`, `β > 0`.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization Balaban.Inhabited
  Balaban.Localization.I5Inhabited Balaban.SmallField.Def6 Balaban.SmallField Finset

theorem composeField_self {d L N₀ K N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}
    {G : GeneratingSet d L N₀ K ϱ} {n : ℕ} (hG : IsLevel G n) (a : ℕ → ℝ) (ha : a n ≠ 0)
    (φ' : G.Ω 1 × Fin N → ℂ) (Ψ' : Torus d (N₀ * L ^ K) → Fin N → ℂ)
    (x : Torus d (N₀ * L ^ K)) (i : Fin N) : composeField G G a φ' Ψ' x i = Ψ' x i := by
  rw [composeField_of_mem a φ' Ψ' (hG x).1 i, (hG x).2]
  have hL : ((L : ℝ) ^ n) ^ 2 ≠ 0 := by
    have : (L : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne L
    positivity
  have : a n / a n * (((L : ℝ) ^ n) ^ 2 / ((L : ℝ) ^ n) ^ 2) = 1 := by
    rw [div_self ha, div_self hL, one_mul]
  rw [this]
  simp

namespace StepSetting

variable {d L N₁ m₁ N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}

/-- For `k = 1` the composed pair of the datum of `ψ` is the datum itself. -/
theorem pairRay_one (S : StepSetting d L N₁ m₁ 1 N ϱ) (hL : 2 ≤ L) (ha₁ : S.a₁ ≠ 0)
    (q : ℝ × S.E) :
    (S.pairRay (N := N) 1 q).1 = (fun x i => ((liftU S.hG' (S.psiAt q.1 q.2) x i : ℝ) : ℂ)) ∧
    (S.pairRay (N := N) 1 q).2 = (fun _ i => (S.h₀ i : ℂ)) := by
  have hn : S.a 1 ≠ 0 := by
    show compWeight L S.a₁ 1 ≠ 0
    rw [compWeight_one hL]; exact ha₁
  unfold pairRay composedPairAt
  simp only [le_refl, dite_true]
  refine ⟨funext fun x => funext fun i => ?_, funext fun x => funext fun i => ?_⟩
  · show composeField _ _ S.a _ (S.dataU (S.psiAt q.1 q.2)).Ψ x i = _
    rw [composeField_self (S.hG) S.a hn, S.dataU_Ψ]
  · show (if x ∈ _ then (S.dataU (S.psiAt q.1 q.2)).h x i else 0) = _
    rw [S.dataU_h]
    simp only [ite_eq_left_iff]
    intro hx
    exact absurd ((S.hG x).1) hx

end StepSetting

section WitnessDomain

variable {m₁ : ℕ}

theorem witness_bgField {β δ pp : ℝ} (R : (witnessSetting m₁ β δ).RayData pp) :
    bgField (GP m₁ (rhoSep m₁)) (compWeight 3 1) 0 (witnessD m₁) =
      unitPhi (GP m₁ (rhoSep m₁)) hN2 := by
  have hcons := theta_consts (d := 3) (L := 3) (N := 2) (by norm_num) R.hδ'0 R.hδ'
  have hDU : InUnionDomainR (GP m₁ (rhoSep m₁)) (bgC1 3 3 2) 0 (witnessD m₁) :=
    ⟨R.δ', R.hδ'0, hcons.2.2.1, R.hD'R⟩
  have ha : ∀ n, 0 ≤ compWeight 3 (1 : ℝ) n := fun n => compWeight_nonneg_three 1 zero_le_one n
  exact bgField_unitBg (isLevel_GP m₁) hN2 (a := compWeight 3 1) ha (unitVec hN2) R.H hDU

theorem witness_liftU_psi0 {β δ pp : ℝ} (R : (witnessSetting m₁ β δ).RayData pp)
    (x : CTorus 3 3 6 m₁ (1 + 1)) (i : Fin 2) :
    liftU (witnessSetting m₁ β δ).hG' (witnessSetting m₁ β δ).psi0 x i = unitVec hN2 i := by
  set S := witnessSetting m₁ β δ with hS
  rw [S.liftU_psi0]
  have hbg : bgField S.G' S.a S.ν S.D' = unitPhi S.G' hN2 := witness_bgField R
  have hpsi : S.psiKd.Ψ x i = (unitVec hN2 i : ℂ) := by
    show composeField (stepG 3 3 6 m₁ 1 (rhoSep m₁)) S.G' S.a
      (bgField S.G' S.a S.ν S.D') S.D'.Ψ x i = _
    rw [composeField_of_mem S.a _ _ (S.hG x).1 i, hbg]
    have hc1 : ∀ (H : GeneratingSet 3 3 (6 * 3 ^ m₁) (1 + 1) (rhoSep m₁)) (n : ℕ) (hn : n ≤ 1 + 1),
        blockMean H n (fun y => svec S.G' (unitPhi S.G' hN2) y i) x = (unitVec hN2 i : ℂ) := by
      intro H n hn
      have : (fun y => svec S.G' (unitPhi S.G' hN2) y i) =
          fun _ => (unitVec hN2 i : ℂ) := funext fun y => svec_unitPhi S.hG' hN2 y i
      rw [this]
      exact blockMean_const H hn _ x
    have e1 := hc1 (stepG 3 3 6 m₁ 1 (rhoSep m₁)) ((stepG 3 3 6 m₁ 1 (rhoSep m₁)).layerIndex x)
      (by rw [(S.hG x).2]; omega)
    have e2 := hc1 S.G' (S.G'.layerIndex x) (by rw [(S.hG' x).2])
    rw [e1, e2]
    show _ + _ * ((witnessD m₁).Ψ x i - _) = _
    have hD : (witnessD m₁).Ψ x i = (unitVec hN2 i : ℂ) :=
      unitBg_Ψ_of_mem (GP m₁ (rhoSep m₁)) hN2 (unitVec hN2)
        ((mem_dataSites _).2 (Or.inl (isLevel_GP m₁ x).1)) i
    rw [hD]
    simp
  rw [hpsi]
  simp


theorem witness_ray_close {β δ pp : ℝ} (R : (witnessSetting m₁ β δ).RayData pp) {T C0 ρ : ℝ}
    (hβ : β = T ^ 2 / 3) (hT : 0 < T) (hC0 : 0 ≤ C0) (hρT : 2 * C0 ≤ ρ * T)
    (hC : ∀ y : (witnessSetting m₁ β δ).E, ‖(witnessSetting m₁ β δ).K y‖ ≤ C0 * ‖y‖)
    (q : ℝ × (witnessSetting m₁ β δ).E) (hq : |q.1| * ‖q.2‖ < 2)
    (x : CTorus 3 3 6 m₁ (1 + 1)) (i : Fin 2) :
    |liftU (witnessSetting m₁ β δ).hG' ((witnessSetting m₁ β δ).psiAt q.1 q.2) x i -
      unitVec hN2 i| ≤ ρ := by
  have hbetaU : (witnessSetting m₁ β δ).betaU = T ^ 2 := by
    rw [witnessSetting_betaU, hβ]; ring
  have h0 := witness_liftU_psi0 R
  generalize witnessSetting m₁ β δ = S at *
  have hc : S.betaU ^ (-(1 / 2 : ℝ)) = T⁻¹ := by
    rw [hbetaU, Real.rpow_neg (by positivity), ← Real.sqrt_eq_rpow, Real.sqrt_sq hT.le]
  rw [S.liftU_psiAt, ← S.liftU_psi0, h0, hc]
  rw [add_sub_cancel_left, abs_mul, abs_mul, abs_inv, abs_of_pos hT]
  have h1 : |liftU S.hG' (S.K q.2) x i| ≤ C0 * ‖q.2‖ := by
    have e : liftU S.hG' (S.K q.2) x i = (S.K q.2 (unitPt S.hG' x)) i := rfl
    rw [e]
    calc |(S.K q.2 (unitPt S.hG' x)) i| = ‖(S.K q.2 (unitPt S.hG' x)) i‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖S.K q.2 (unitPt S.hG' x)‖ := PiLp.norm_apply_le _ i
      _ ≤ ‖S.K q.2‖ := norm_le_pi_norm (S.K q.2) _
      _ ≤ C0 * ‖q.2‖ := hC q.2
  have h2 : |q.1| * (T⁻¹ * |liftU S.hG' (S.K q.2) x i|) ≤ |q.1| * (T⁻¹ * (C0 * ‖q.2‖)) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h1 (by positivity)) (abs_nonneg _)
  refine h2.trans ?_
  have e : |q.1| * (T⁻¹ * (C0 * ‖q.2‖)) = (C0 / T) * (|q.1| * ‖q.2‖) := by field_simp
  rw [e]
  calc (C0 / T) * (|q.1| * ‖q.2‖) ≤ (C0 / T) * 2 :=
        mul_le_mul_of_nonneg_left hq.le (by positivity)
    _ = 2 * C0 / T := by ring
    _ ≤ ρ := by rw [div_le_iff₀ hT]; exact hρT


/-- The radius of the ball around `e₀` of `xiDom_ball_witness` (level `1`, `ε = 1`). -/
theorem exists_ball_rho (m₁ : ℕ) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ (Ψ c : Fld 3 3 6 m₁ 2 2),
      (∀ x i, ‖Ψ x i - (Pi.single (0 : Fin 2) 1 : Fin 2 → ℂ) i‖ ≤ ρ) →
      (∀ x i, ‖c x i - (Pi.single (0 : Fin 2) 1 : Fin 2 → ℂ) i‖ ≤ ρ) →
      IsBlockConstFld 1 Ψ → IsBlockConstFld 1 c →
      XiDom (levelGS 1 (by norm_num) : GeneratingSet 3 3 (6 * 3 ^ m₁) 2 (rhoSep m₁))
        (aIdeal 3 2 (witnessa 2)) (bgMass 3 2 (witnessβ 2) (witnessν 2 2)) 1 1 Ψ c :=
  xiDom_ball_witness (k := 2) (N₁ := 6) (m₁ := m₁) (ϱ := rhoSep m₁) (α₀ := 1) one_pos
    (bgHyp_rho m₁).hϱ (j := 1) (by norm_num) 1 one_pos

/-- The operator-norm constant of `C^{(k)1/2}` of the witness (independent of `β`, `δ`). -/
noncomputable def witnessKnorm (m₁ : ℕ) : ℝ :=
  ‖LinearMap.toContinuousLinearMap (witnessSetting m₁ 1 1).K‖

theorem witnessK_bound (m₁ : ℕ) (β δ : ℝ) (y : (witnessSetting m₁ β δ).E) :
    ‖(witnessSetting m₁ β δ).K y‖ ≤ witnessKnorm m₁ * ‖y‖ :=
  (LinearMap.toContinuousLinearMap (witnessSetting m₁ 1 1).K).le_opNorm y

/-- **`RayInDomain` is inhabited** (together with `StepTermsAnalytic` and `RayData`): the step of
`StepRegWitness` (`N = 2`, `β > 0`, `p₁ = 1 < p⁺ = 2`), zero class, `g = 0`; the composed pair of
the datum of `ψ^{(1)} + s ψ'` lies in the analyticity domain `Ξ^c_1(𝔹_1; 1, 1)` for
`|s| ‖ψ̂‖ < 2`. -/
theorem nonempty_rayInDomain :
    ∃ (m₁ : ℕ) (S : StepSetting 3 3 6 m₁ 1 2 (rhoSep m₁)), 0 < S.β ∧ 0 < S.p₁ ∧ S.p₁ < 2 ∧
      Nonempty (S.RayData 2) ∧
      ∃ (A : ℕ → ℝ) (μ : ℝ) (ε : ℕ → ℝ),
        Nonempty (StepTermsAnalytic (zeroClass 3 3 6 m₁ 1 2 (rhoSep m₁)) A μ ε) ∧
        S.RayInDomain (zeroClass 3 3 6 m₁ 1 2 (rhoSep m₁)) 0 A μ ε 2 := by
  classical
  let ρf : ℕ → ℝ := fun m => (exists_ball_rho m).choose
  have hρf : ∀ m, 0 < ρf m := fun m => (exists_ball_rho m).choose_spec.1
  obtain ⟨m₁, δ, δ', T, hm, hbig, hδ, hsm, hδ'0, hδ'a, hδ'b, hδ'c, hT, hT0, hT1, hT2⟩ :=
    exists_witness_params (fun m => 2 * witnessKnorm m / ρf m)
  obtain ⟨R⟩ := rayData_witness hm hbig hδ hsm hδ'0 hδ'a hδ'b hδ'c hT hT1 hT2
  have hρ := hρf m₁
  have hCn : 0 ≤ witnessKnorm m₁ := norm_nonneg _
  have hρT : 2 * witnessKnorm m₁ ≤ ρf m₁ * T := by
    have := (div_le_iff₀ hρ).1 hT0
    linarith
  refine ⟨m₁, witnessSetting m₁ (T ^ 2 / 3) δ, ?_, one_pos, (by show (1 : ℝ) < 2; norm_num),
    ⟨R⟩, aIdeal 3 2 (witnessa 2), bgMass 3 2 (witnessβ 2) (witnessν 2 2), fun _ => 1,
    nonempty_stepTermsAnalytic _ _ _, ?_, ?_⟩
  · show 0 < T ^ 2 / 3
    positivity
  · have hl : Def6.l1 (0 : Fld 3 3 6 m₁ (1 + 1) 2) = 0 := by
      simp [Def6.l1, vn]
    show Def6.l1 (0 : Fld 3 3 6 m₁ (1 + 1) 2) < 1
    rw [hl]; exact one_pos
  · intro q hq j hj1 hjk X hX
    have hj : j = 1 := le_antisymm hjk hj1
    subst hj
    obtain ⟨hρ0, hball⟩ := (exists_ball_rho m₁).choose_spec
    have hpair := (witnessSetting m₁ (T ^ 2 / 3) δ).pairRay_one (N := 2) (by norm_num)
      (one_ne_zero) q
    show XiDom ((zeroTerms 3 3 6 m₁ (1 + 1) 2 (rhoSep m₁)).gs 1 X) _ _ 1 1
      ((witnessSetting m₁ (T ^ 2 / 3) δ).pairRay (N := 2) 1 q).1
      ((witnessSetting m₁ (T ^ 2 / 3) δ).pairRay (N := 2) 1 q).2
    rw [zeroTerms_gs (by norm_num)]
    have hsingle : ∀ i : Fin 2, (Pi.single (0 : Fin 2) 1 : Fin 2 → ℂ) i = ((unitVec hN2 i : ℝ) : ℂ) := by
      intro i
      by_cases h : i = 0
      · subst h; simp [unitVec]
      · simp [h, unitVec]
    refine hball _ _ ?_ ?_ ?_ ?_
    · intro x i
      rw [hpair.1, hsingle, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
      exact witness_ray_close R rfl hT hCn hρT (witnessK_bound m₁ _ _) q hq x i
    · intro x i
      rw [hpair.2, hsingle]
      have : (witnessSetting m₁ (T ^ 2 / 3) δ).h₀ i = unitVec hN2 i := rfl
      have h0 : ‖(((witnessSetting m₁ (T ^ 2 / 3) δ).h₀ i : ℝ) : ℂ) -
          ((unitVec hN2 i : ℝ) : ℂ)‖ = 0 := by rw [this]; simp
      exact h0.le.trans hρ0.le
    · intro x x' h
      rw [hpair.1]
      have hu : unitPt (witnessSetting m₁ (T ^ 2 / 3) δ).hG' x =
          unitPt (witnessSetting m₁ (T ^ 2 / 3) δ).hG' x' := Subtype.ext h
      funext i
      simp only [liftU, hu]
    · intro x x' _
      rw [hpair.2]


/-- The route through `RayInDomain` is also non-degenerate: at the witness, `ClassRegularObs` (hence
`ClassRegularLoc`, `ClassRegular`) of the zero class follow from `RayData`, `StepTermsAnalytic` and
`RayInDomain` by `classRegularObs_of_analytic`. -/
theorem nonempty_classRegularObs_via_domain :
    ∃ (m₁ : ℕ) (S : StepSetting 3 3 6 m₁ 1 2 (rhoSep m₁)), 0 < S.β ∧
      Nonempty (S.ClassRegularObs (zeroClass 3 3 6 m₁ 1 2 (rhoSep m₁)) 0) := by
  obtain ⟨m₁, S, hβ, hp₁, hlt, ⟨R⟩, A, μ, ε, ⟨hT⟩, hD⟩ := nonempty_rayInDomain
  exact ⟨m₁, S, hβ, ⟨StepSetting.classRegularObs_of_analytic _ R hT hD hp₁ hlt⟩⟩

end WitnessDomain

end Balaban.Fluctuation
