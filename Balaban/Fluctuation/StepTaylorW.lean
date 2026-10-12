/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.StepTaylor
public import Balaban.Fluctuation.StepRegDomain
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Non-vacuity of the ray Taylor identities (HAT-RATE §2)

For the non-degenerate step datum `witnessSetting` of `StepRegWitness` (`d = L = 3`, `N₁ = 6`,
`k = 1`, `N = 2`, `ν = 0`, `θ ≡ h ≡ e₀`, `p₁ = 1 < p⁺ = 2`, `β` large) every premise of
`Vk_ray_taylor_of_baseDomain` and `completeW_taylor_of_baseDomain` holds: `RayData`,
`StepTermsAnalytic`, `RayInDomain` (landed in `StepRegDomain`) and the base-domain witness of
`theorem72_linearResponse` (radius `bgC2`), which is proved here: the critical datum is the constant
unit datum, which lies in every complex data domain.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization Balaban.Inhabited
  Balaban.Localization.I5Inhabited Balaban.SmallField.Def6 Balaban.SmallField Finset Set

theorem bgC2_pos_three : 0 < bgC2 3 3 2 := by
  have h1 := bgC1_pos' (d := 3) (L := 3) (N := 2) (by norm_num)
  have h2 := bgK1_pos (d := 3) (L := 3) (N := 2)
  have h3 := smallnessConst_nonneg (d := 3) (by norm_num)
  have h4 := sandwichConst_nonneg 3 3 2
  unfold bgC2
  exact lt_min h1 (by positivity)

/-- **The base-domain witness of `theorem72_linearResponse` holds for the witness step**: the datum
`dataU ψ^{(1)}` is the constant unit datum, in `𝒟(𝔹_1)` with radius `bgC2`. -/
theorem witness_baseDomain {m₁ : ℕ} {β δ pp : ℝ} (R : (witnessSetting m₁ β δ).RayData pp) :
    InUnionDomainC (stepG 3 3 6 m₁ 1 (rhoSep m₁)) (bgC0 3 3 2) (bgC2 3 3 2)
      (witnessSetting m₁ β δ).ν
      ((witnessSetting m₁ β δ).dataU (witnessSetting m₁ β δ).psi0) := by
  set S := witnessSetting m₁ β δ with hS
  have hc := bgC2_pos_three
  have hle : bgC2 3 3 2 ≤ bgC0 3 3 2 :=
    (bgC2_le_bgC1 3 3 2).trans (bgC1_le_bgC0 3 3 2 (by norm_num))
  refine ⟨bgC2 3 3 2, bgC2 3 3 2, hc, le_rfl, hle, le_rfl, ?_, ?_⟩
  · have h0 : S.ν = 0 := rfl
    rw [h0]
    simp only [zero_mul]
    positivity
  · refine ⟨fun _ => unitVec hN2, unitVec hN2, 0, 0, exists_inPsiTildeC (stepG 3 3 6 m₁ 1 (rhoSep m₁)) hN2 S.ν hc hc, ?_, ?_⟩
    · intro x _ i
      rw [S.dataU_Ψ, witness_liftU_psi0 R]
      simp
    · intro x _ i
      rw [S.dataU_h]
      simp [hS, witnessSetting]

/-- **`RayData`, `StepTermsAnalytic` and `RayInDomain` hold for an explicit witness step** (the
content of `nonempty_rayInDomain`, with the step exhibited as `witnessSetting m₁ β δ`). -/
theorem exists_witness_rayInDomain :
    ∃ (m₁ : ℕ) (β δ : ℝ), 0 < β ∧ 0 < (witnessSetting m₁ β δ).p₁ ∧
      (witnessSetting m₁ β δ).p₁ < 2 ∧ Nonempty ((witnessSetting m₁ β δ).RayData 2) ∧
      ∃ (A : ℕ → ℝ) (μ : ℝ) (ε : ℕ → ℝ),
        Nonempty (StepTermsAnalytic (zeroClass 3 3 6 m₁ 1 2 (rhoSep m₁)) A μ ε) ∧
        (witnessSetting m₁ β δ).RayInDomain (zeroClass 3 3 6 m₁ 1 2 (rhoSep m₁)) 0 A μ ε 2 := by
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
  refine ⟨m₁, T ^ 2 / 3, δ, ?_, one_pos, (by show (1 : ℝ) < 2; norm_num),
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


/-- **Non-vacuity (HAT-RATE §2).**  For the witness step (zero class, source `g = 0`) all premises of
the ray identities hold, and so do their conclusions: `V` vanishes to second order along every
ray with `‖ψ̂‖ ≤ p₁ = 1 < p⁺ = 2`, the Taylor remainder formula (2.3) holds on `[0,1]`, and the exact
identity (2.6) holds on both segments. -/
theorem Vk_ray_taylor_witness :
    ∃ (m₁ : ℕ) (β δ : ℝ), 0 < β ∧ Nonempty ((witnessSetting m₁ β δ).RayData 2) ∧
      0 < (witnessSetting m₁ β δ).p₁ ∧ (witnessSetting m₁ β δ).p₁ < 2 ∧
      InUnionDomainC (stepG 3 3 6 m₁ 1 (rhoSep m₁)) (bgC0 3 3 2) (bgC2 3 3 2)
        (witnessSetting m₁ β δ).ν
        ((witnessSetting m₁ β δ).dataU (witnessSetting m₁ β δ).psi0) ∧
      ∀ x : (witnessSetting m₁ β δ).E, ‖x‖ ≤ (witnessSetting m₁ β δ).p₁ →
        deriv (fun s : ℝ => (witnessSetting m₁ β δ).Vk ((witnessSetting m₁ β δ).psiAt s x)) 0 = 0 ∧
        deriv (deriv (fun s : ℝ =>
          (witnessSetting m₁ β δ).Vk ((witnessSetting m₁ β δ).psiAt s x))) 0 = 0 ∧
        (∀ s ∈ Icc (0 : ℝ) 1, (witnessSetting m₁ β δ).Vk ((witnessSetting m₁ β δ).psiAt s x) =
          ∫ u in (0 : ℝ)..1, taylorWeight (u : ℂ) * ((s : ℂ) ^ 3 *
            iteratedDeriv 3 (fun r : ℝ =>
              (witnessSetting m₁ β δ).Vk ((witnessSetting m₁ β δ).psiAt r x)) (u * s))) ∧
        ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
          StepSetting.completeW (zeroClass 3 3 6 m₁ 1 2 (rhoSep m₁)) 0 s t x =
            (witnessSetting m₁ β δ).Wone (zeroClass 3 3 6 m₁ 1 2 (rhoSep m₁)) s x +
              (witnessSetting m₁ β δ).Wtwo (zeroClass 3 3 6 m₁ 1 2 (rhoSep m₁)) 0 t x := by
  obtain ⟨m₁, β, δ, hβ, hp, hp2, ⟨R⟩, A, μ, ε, ⟨hT⟩, hD⟩ := exists_witness_rayInDomain
  have hbase := witness_baseDomain R
  refine ⟨m₁, β, δ, hβ, ⟨R⟩, hp, hp2, hbase, fun x hx => ?_⟩
  refine ⟨StepSetting.Vk_ray_deriv_zero_of_baseDomain R hbase x,
    StepSetting.Vk_ray_deriv2_zero_of_baseDomain R hbase x,
    fun s hs => StepSetting.Vk_ray_taylor_of_baseDomain R hp2 hbase hx hs, fun s hs t ht => ?_⟩
  exact StepSetting.completeW_taylor_of_baseDomain _ R hT hD hp2 hbase hx hs ht

end Balaban.Fluctuation
