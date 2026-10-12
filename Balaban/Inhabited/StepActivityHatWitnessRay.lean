/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.HatExpansionWitnessLabels
public import Balaban.Fluctuation.StepRegWitness
public import Balaban.Fluctuation.StepRegUnit
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# `RayData` for the step of the hat witness (constant unit block field, mass `ν = 1/81`)

The step `hatStep` lives on the whole-lattice level-two set `Gp` of the hat witness
(`d = L = 3`, `N₁ = 9`, `k = 1`, `N = 2`, mass `ν = 1/81`); the block datum `θ ≡ h ≡ e₀` is the
constant unit datum.  The background of `θ` is the constant unit field also for `ν ≠ 0` (the
action is `0`, hence minimal; `bgField_unitBg_nu`), and the five tests of `χ_u` reduce to the bound
on the multiplier (`chiUBounds_unitBg_nu`).  `rayData_hatStep` is the analogue of
`rayData_witness`: for `β = T²/3` with `T` large, `S.RayData 2`.
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation
  Balaban.Localization Balaban.Localization.LevelPair Balaban.Localization.I5Inhabited
  Balaban.Polymer Balaban.SmallField.Def6 Finset

section Unit

variable {d L N₀ K N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ} {G : GeneratingSet d L N₀ K ϱ}

theorem action_unitBg_eq_zero_nu {n : ℕ} (hG : IsLevel G n) (hN : 0 < N) (a : ℕ → ℝ) (ν : ℝ) :
    action G a ν (unitBg G hN (unitVec hN)) (unitPhi G hN) = 0 := by
  unfold action
  have h1 : ∀ x : G.Ω 1, ∀ i, (unitBg G hN (unitVec hN)).Ψ x i - blockAvg G (unitPhi G hN) x i = 0 := by
    intro x i
    rw [blockAvg_unit hG hN, unitBg_Ψ_of_mem G hN _ ((mem_dataSites G).2 (Or.inl x.2)), sub_self]
  have h2 : ∀ (y : Torus d (N₀ * L ^ K)) (μ : Fin d) (i : Fin N),
      barField G (unitBg G hN (unitVec hN)).Ψ (unitPhi G hN) (y + Pi.single μ 1) i -
        barField G (unitBg G hN (unitVec hN)).Ψ (unitPhi G hN) y i = 0 := by
    intro y μ i
    rw [barField_unit hG hN, barField_unit hG hN, sub_self]
  have h3 : ∀ (x : G.Ω 1) (i : Fin N),
      unitPhi G hN (x, i) - (unitBg G hN (unitVec hN)).h x i = 0 := by
    intro x i
    rw [unitBg_h_of_mem G hN _ x.2 i]
    simp [unitPhi]
  simp [h1, h2, h3]

theorem isMinimizer_unitBg_nu {n : ℕ} (hG : IsLevel G n) (hN : 0 < N) {a : ℕ → ℝ}
    (ha : ∀ n, 0 ≤ a n) {ν : ℝ} (hν : 0 ≤ ν) :
    IsMinimizer G a ν (unitBg G hN (unitVec hN)) (unitPhi G hN) := by
  refine ⟨fun x i => ?_, isRealUnitField_unitPhi hN, fun σ _ => ?_⟩
  · refine ⟨?_, ?_⟩
    · by_cases hx : x ∈ dataSites G
      · rw [unitBg_Ψ_of_mem G hN _ hx]; simp
      · simp [unitBg, BgData.clip, hx]
    · by_cases hx : x ∈ G.Ω 1
      · rw [unitBg_h_of_mem G hN _ hx]; simp
      · simp [unitBg, BgData.clip, hx]
  · rw [action_unitBg_eq_zero_nu hG hN a ν]
    exact action_nonneg_of ha hν _ _

/-- The background field of the constant unit datum is the constant unit field, for every mass. -/
theorem bgField_unitBg_nu {n : ℕ} (hG : IsLevel G n) (hN : 0 < N) {a : ℕ → ℝ}
    (ha : ∀ n, 0 ≤ a n) {ν : ℝ} (H : BgHyp d L K ϱ a ν)
    (hD : InUnionDomainR G (bgC1 d L N) ν (unitBg G hN (unitVec hN))) :
    bgField G a ν (unitBg G hN (unitVec hN)) = unitPhi G hN := by
  have hmin := isMinimizer_unitBg_nu hG hN ha H.mass
  exact bgField_eq hmin fun φ' hφ' => ((theorem71 H hD).1.unique hφ' hmin)

theorem chiUBounds_unitBg_nu {n : ℕ} (hG : IsLevel G n) (hN : 0 < N) {δ : ℝ}
    (hδ : 0 < δ) {ν : ℝ} {φ₁ : G.Ω 1 × Fin N → ℂ} (hφ : φ₁ = unitPhi G hN) {α : G.Ω 1 → ℂ}
    (hα : ∀ x : G.Ω 1, G.spacing (x : Torus d (N₀ * L ^ K)) ^ 2 * ‖α x‖ < δ / 2) :
    ChiUBounds G ν δ (unitBg G hN (unitVec hN)) φ₁ α := by
  have h0 := chiUBounds_unitBg hG hN (unitVec hN) hδ hφ hα
  subst hφ
  refine ⟨h0.close, h0.grad, h0.lap, h0.mult, fun z => ?_⟩
  have hv0 : vn (fun _ : Fin N => (0 : ℂ)) = 0 := by
    simp only [vn]
    simp [EuclideanSpace.norm_eq]
  have e : (fun i => unitPhi G hN (z, i) - (unitBg G hN (unitVec hN)).h z i) =
      fun _ => (0 : ℂ) := by
    funext i
    rw [unitBg_h_of_mem G hN _ z.2 i]
    simp [unitPhi]
  rw [e, hv0]
  simp only [mul_zero]
  positivity

end Unit

/-- The step datum of the hat-activity witness: `G' = Gp` (the whole-lattice level-two set of the
hat witness), the constant unit block datum, mass `ν = 1/81`, `a₁ = 1`. -/
noncomputable def hatStep (m₁ : ℕ) (β p₁ δ : ℝ) : StepSetting 3 3 9 m₁ 1 2 (rhoSep m₁) where
  G' := Gp m₁ (rhoSep m₁)
  hk1 := le_rfl
  hG' := isLevel_Gp
  D' := unitBg (Gp m₁ (rhoSep m₁)) hN2 (unitVec hN2)
  h₀ := unitVec hN2
  hh₀ := fun x i => unitBg_h_of_mem (Gp m₁ (rhoSep m₁)) hN2 (unitVec hN2)
    ((isLevel_Gp (m₁ := m₁) (ϱ := rhoSep m₁)).Ω_one ▸ Finset.mem_univ x) i
  a₁ := 1
  ν := nuW
  β := β
  p₁ := p₁
  δ := δ

theorem hatStep_betaU (m₁ : ℕ) (β p₁ δ : ℝ) : (hatStep m₁ β p₁ δ).betaU = 3 * β := by
  unfold StepSetting.betaU
  show β * (((3 : ℕ) : ℝ) ^ 1) ^ 3 / (((3 : ℕ) : ℝ) ^ 1) ^ 2 = 3 * β
  norm_num
  ring

theorem hatStep_domain (m₁ : ℕ) (β p₁ δ : ℝ) {δ' : ℝ} (hδ'0 : 0 < δ') :
    InDomainR (hatStep m₁ β p₁ δ).G' (hatStep m₁ β p₁ δ).ν δ' (hatStep m₁ β p₁ δ).D' := by
  refine ⟨fun _ => unitVec hN2, unitVec hN2,
    (exists_inPsiTildeC (G := Gp m₁ (rhoSep m₁)) hN2 nuW hδ'0 hδ'0).toInPsiTilde, ?_, ?_⟩
  · intro x hx i
    exact unitBg_Ψ_of_mem (Gp m₁ (rhoSep m₁)) hN2 (unitVec hN2) hx i
  · intro x hx i
    exact unitBg_h_of_mem (Gp m₁ (rhoSep m₁)) hN2 (unitVec hN2) hx i

/-- **`RayData` for the hat witness step**: `β = T²/3` with `T` large (`3 B₅ K₂ p⁺ ≤ T δ`,
`B₅ p⁺ ≤ T r`), `p⁺ = 2`, for every `p₁`. -/
theorem rayData_hatStep (m₁ : ℕ) (p₁ : ℝ) (hm : 4 ≤ m₁) (hbig : cstarX 3 3 ≤ (3 : ℝ) ^ m₁)
    {δ δ' T : ℝ} (hδ : 0 < δ) (hsm : δ ^ 2 * smallConstX 3 3 0 ≤ 1 / 4) (hδ'0 : 0 < δ')
    (hδ'a : δ' ≤ thm73C3 3 3 2 / 2) (hδ'b : bgK1 3 3 2 * δ' ≤ δ / 4)
    (hδ'c : bgK1 3 3 2 * δ' ≤ coerciveConst 3 / 4) (hT : 0 < T)
    (hT1 : 3 * witB5 * witK2 * 2 ≤ T * δ) (hT2 : witB5 * 2 ≤ T * fluctRadius 3 3 2) :
    Nonempty ((hatStep m₁ (T ^ 2 / 3) p₁ δ).RayData 2) := by
  set S := hatStep m₁ (T ^ 2 / 3) p₁ δ with hS
  have hbetaU : S.betaU = T ^ 2 := by
    rw [hS, hatStep_betaU]; ring
  have hHg : BgHyp 3 3 2 (rhoSep m₁) (compWeight 3 1) nuW := bgHypNu m₁
  have hcons := theta_consts (d := 3) (L := 3) (N := 2) (by norm_num) hδ'0 hδ'a
  have hDR : InDomainR S.G' S.ν δ' S.D' := hatStep_domain m₁ _ p₁ δ hδ'0
  have hDU : InUnionDomainR S.G' (bgC1 3 3 2) S.ν S.D' := ⟨δ', hδ'0, hcons.2.2.1, hDR⟩
  have ha : ∀ n, 0 ≤ compWeight 3 (1 : ℝ) n := fun n => compWeight_nonneg_three 1 zero_le_one n
  have hbg : bgField S.G' S.a S.ν S.D' = unitPhi S.G' hN2 :=
    bgField_unitBg_nu (isLevel_Gp (m₁ := m₁) (ϱ := rhoSep m₁)) hN2 (a := compWeight 3 1) ha hHg hDU
  have hbd := (theorem71 hHg hDU).2.2.2.2 δ' hδ'0 hcons.2.2.1 hDR
  have hα : ∀ x : S.G'.Ω 1, S.G'.spacing (x : Torus 3 (9 * 3 ^ m₁ * 3 ^ 2)) ^ 2 *
      ‖bgMult S.G' S.a S.ν S.D' x‖ ≤ bgK1 3 3 2 * δ' := hbd.alpha
  have hsp : ∀ x : Torus 3 (9 * 3 ^ m₁ * 3 ^ 2), 0 < S.G'.spacing x := fun x => spacing_pos _
  refine ⟨{ ha₁ := one_pos, H := hHg, δ' := δ', hδ'0 := hδ'0, hδ' := hδ'a, hD'R := hDR,
            hδ0 := hδ, hfam := ?_, hsm := hsm, hχu := ?_, hnorm := ?_, hβ := ?_,
            hpp := by norm_num, B₅ := witB5, K₂ := witK2, hB5 := le_rfl, hK2 := le_rfl,
            hp40 := ?_, hrad := ?_ }⟩
  · intro x hx
    refine ⟨⟨(dgSettingNu hm), le_rfl, by show (1 / 2 : ℝ) ≤ 1; norm_num,
      by show (1 : ℝ) ≤ 2; norm_num⟩, ?_, hx, le_rfl, ?_, ?_⟩
    · intro y
      have hs2 : 0 < S.G'.spacing (y : Torus 3 (9 * 3 ^ m₁ * 3 ^ 2)) ^ 2 := by
        have := hsp y; positivity
      have h1 := hα y
      have h2 : coerciveConst 3 ≥ 0 := (coerciveConst_pos (by norm_num)).le
      rw [le_div_iff₀ (by positivity)]
      nlinarith
    · simpa using hbig
    · intro P; simp
  · rw [chiU_eq_one_iff]
    refine chiUBounds_unitBg_nu (isLevel_Gp (m₁ := m₁) (ϱ := rhoSep m₁)) hN2 hδ hbg fun y => ?_
    exact lt_of_le_of_lt (hα y) (by linarith)
  · have hh : ∑ i, S.h₀ i ^ 2 = 1 := sum_sq_unitVec hN2
    rw [hh, sub_self, abs_zero, mul_zero]
    have hd : S.δ = δ := rfl
    rw [hd]
    positivity
  · show 0 < T ^ 2 / 3
    positivity
  · have hd : S.δ = δ := rfl
    rw [hbetaU, hd]
    have e : (T ^ 2) ^ (1 / 2 : ℝ) = T := by
      rw [← Real.sqrt_eq_rpow, Real.sqrt_sq hT.le]
    rw [e, div_le_iff₀ (by positivity)]
    have hB : 0 < witB5 := lt_of_lt_of_le one_pos (le_max_left _ _)
    have hK : 0 < witK2 := lt_of_lt_of_le one_pos ((le_max_left _ _).trans (le_max_left _ _))
    rw [inv_mul_eq_div, le_div_iff₀ (by positivity)]
    nlinarith
  · rw [hbetaU]
    have e : (T ^ 2) ^ (-(1 / 2) : ℝ) = T⁻¹ := by
      rw [Real.rpow_neg (by positivity), ← Real.sqrt_eq_rpow, Real.sqrt_sq hT.le]
    rw [e]
    have : witB5 * T⁻¹ * 2 = witB5 * 2 / T := by field_simp
    rw [this, div_le_iff₀ hT]
    linarith

end Balaban.Inhabited
