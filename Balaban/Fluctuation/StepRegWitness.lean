/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.StepRegClass
public import Balaban.Fluctuation.StepRegUnit
public import Balaban.Fluctuation.StepIdentityInhabited
public import Balaban.Localization.I5Inhabited
public import Balaban.Fluctuation.Prop33CloseC7
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# A non-degenerate witness of `RayData`

The step datum `d = L = 3`, `N₁ = 6`, `k = 1`, `N = 2`, `a₁ = 1`, `ν = 0`, `G' = 𝔹_2` (the
whole-lattice set of level two of `I5Inhabited`), `θ ≡ h ≡ e₀` the constant unit datum, with `β > 0`
chosen large; `p₁ = 1 < p⁺ = 2`.  The background of `θ` is the constant unit field
(`bgField_unitBg`), so all tests of `χ_u` hold with the bound on the multiplier coming from
Theorem 7.1 (`BgBounds`).
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization Balaban.Inhabited
  Balaban.Localization.I5Inhabited Balaban.SmallField.Def6 Balaban.SmallField Finset

theorem compWeight_nonneg_three (a₁ : ℝ) (ha : 0 ≤ a₁) (r : ℕ) : 0 ≤ compWeight 3 a₁ r := by
  unfold compWeight
  refine div_nonneg (mul_nonneg ha ?_) ?_
  · have : ((((3 : ℕ) : ℝ) ^ 2)⁻¹) ≤ 1 :=
      inv_le_one_of_one_le₀ (by norm_num)
    linarith
  · have h1 : (1 : ℝ) ≤ (((3 : ℕ) : ℝ) ^ r) ^ 2 := by
      have : (1 : ℝ) ≤ ((3 : ℕ) : ℝ) ^ r := one_le_pow₀ (by norm_num)
      nlinarith
    have : ((((3 : ℕ) : ℝ) ^ r) ^ 2)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ h1
    linarith

theorem exists_large_T {B₅ K₂ pp δ r : ℝ} (hδ : 0 < δ) (hr : 0 < r) :
    ∃ T : ℝ, 0 < T ∧ 3 * B₅ * K₂ * pp ≤ T * δ ∧ B₅ * pp ≤ T * r := by
  refine ⟨max (3 * B₅ * K₂ * pp / δ) (B₅ * pp / r) + 1 + |3 * B₅ * K₂ * pp / δ| +
    |B₅ * pp / r|, ?_, ?_, ?_⟩
  · have := abs_nonneg (3 * B₅ * K₂ * pp / δ)
    have := abs_nonneg (B₅ * pp / r)
    have h1 : 0 ≤ max (3 * B₅ * K₂ * pp / δ) (B₅ * pp / r) + |3 * B₅ * K₂ * pp / δ| := by
      have := le_max_left (3 * B₅ * K₂ * pp / δ) (B₅ * pp / r)
      have := neg_abs_le (3 * B₅ * K₂ * pp / δ)
      linarith [le_abs_self (3 * B₅ * K₂ * pp / δ)]
    linarith
  · have h1 := le_max_left (3 * B₅ * K₂ * pp / δ) (B₅ * pp / r)
    have h2 := abs_nonneg (3 * B₅ * K₂ * pp / δ)
    have h3 := abs_nonneg (B₅ * pp / r)
    rw [← div_le_iff₀ hδ]
    linarith
  · have h1 := le_max_right (3 * B₅ * K₂ * pp / δ) (B₅ * pp / r)
    have h2 := abs_nonneg (3 * B₅ * K₂ * pp / δ)
    have h3 := abs_nonneg (B₅ * pp / r)
    rw [← div_le_iff₀ hr]
    linarith


section Setting

variable (m₁ : ℕ)

theorem hN2 : 0 < (2 : ℕ) := by norm_num

theorem isLevel_GP : IsLevel (GP m₁ (rhoSep m₁)) 2 :=
  isLevel_levelGS (N₁ := 6) (m₁ := m₁) (ϱ := rhoSep m₁) (k := 2) (by omega) le_rfl

/-- The constant unit datum on `𝔹_2`. -/
noncomputable def witnessD : BgData (GP m₁ (rhoSep m₁)) 2 :=
  unitBg (GP m₁ (rhoSep m₁)) hN2 (unitVec hN2)

/-- The witness step datum: constant unit `θ`, mass `0`, `a₁ = 1`, radius `p₁ = 1`; `β`, `δ` free. -/
noncomputable def witnessSetting (β δ : ℝ) :
    StepSetting 3 3 6 m₁ 1 2 (rhoSep m₁) where
  G' := GP m₁ (rhoSep m₁)
  hk1 := le_rfl
  hG' := isLevel_GP m₁
  D' := witnessD m₁
  h₀ := unitVec hN2
  hh₀ := fun x i => unitBg_h_of_mem (GP m₁ (rhoSep m₁)) hN2 (unitVec hN2)
    ((isLevel_GP m₁).Ω_one ▸ Finset.mem_univ x) i
  a₁ := 1
  ν := 0
  β := β
  p₁ := 1
  δ := δ

theorem witnessSetting_betaU (β δ : ℝ) : (witnessSetting m₁ β δ).betaU = 3 * β := by
  unfold StepSetting.betaU
  show β * (((3 : ℕ) : ℝ) ^ 1) ^ 3 / (((3 : ℕ) : ℝ) ^ 1) ^ 2 = 3 * β
  norm_num
  ring


end Setting

section Witness

variable {m₁ : ℕ}

/-- The constant `B₅` of the witness. -/
noncomputable def witB5 : ℝ := max 1 (Real.sqrt ((2 : ℕ) : ℝ) * covSupConst 3 3 2 (compWeight 3 1 1))

/-- The constant `K₂` of the witness. -/
noncomputable def witK2 : ℝ :=
  max (max 1 (cK2 3 3 2)) (Real.sqrt ((2 : ℕ) : ℝ) * cK2 3 3 2)

theorem witnessData_domain {β δ δ' : ℝ} (hδ'0 : 0 < δ') :
    InDomainR (witnessSetting m₁ β δ).G' (witnessSetting m₁ β δ).ν δ'
      (witnessSetting m₁ β δ).D' := by
  refine ⟨fun _ => unitVec hN2, unitVec hN2,
    (exists_inPsiTildeC (G := GP m₁ (rhoSep m₁)) hN2 0 hδ'0 hδ'0).toInPsiTilde, ?_, ?_⟩
  · intro x hx i
    exact unitBg_Ψ_of_mem (GP m₁ (rhoSep m₁)) hN2 (unitVec hN2) hx i
  · intro x hx i
    exact unitBg_h_of_mem (GP m₁ (rhoSep m₁)) hN2 (unitVec hN2) hx i


open Balaban.Fluctuation.StepSetting in
/-- **`RayData` is inhabited by a non-degenerate step datum**: `d = L = 3`, `N₁ = 6`, `k = 1`,
`N = 2`, `a₁ = 1`, `ν = 0`, `θ ≡ h ≡ e₀`, `p₁ = 1 < p⁺ = 2`, `β > 0` large (`T = β_k^{1/2}` with
`3 B₅ K₂ p⁺ ≤ T δ`, `B₅ p⁺ ≤ T r`). -/
theorem rayData_witness (hm : 4 ≤ m₁) (hbig : cstarX 3 3 ≤ (3 : ℝ) ^ m₁) {δ δ' T : ℝ}
    (hδ : 0 < δ) (hsm : δ ^ 2 * smallConstX 3 3 0 ≤ 1 / 4) (hδ'0 : 0 < δ')
    (hδ'a : δ' ≤ thm73C3 3 3 2 / 2) (hδ'b : bgK1 3 3 2 * δ' ≤ δ / 4)
    (hδ'c : bgK1 3 3 2 * δ' ≤ coerciveConst 3 / 4) (hT : 0 < T)
    (hT1 : 3 * witB5 * witK2 * 2 ≤ T * δ) (hT2 : witB5 * 2 ≤ T * fluctRadius 3 3 2) :
    Nonempty ((witnessSetting m₁ (T ^ 2 / 3) δ).RayData 2) := by
  set S := witnessSetting m₁ (T ^ 2 / 3) δ with hS
  have hbetaU : S.betaU = T ^ 2 := by
    rw [hS, witnessSetting_betaU]; ring
  have hHg : BgHyp 3 3 2 (rhoSep m₁) (compWeight 3 1) 0 := bgHyp_rho m₁
  have hcons := theta_consts (d := 3) (L := 3) (N := 2) (by norm_num) hδ'0 hδ'a
  have hDR : InDomainR S.G' S.ν δ' S.D' := witnessData_domain hδ'0
  have hDU : InUnionDomainR S.G' (bgC1 3 3 2) S.ν S.D' := ⟨δ', hδ'0, hcons.2.2.1, hDR⟩
  have ha : ∀ n, 0 ≤ compWeight 3 (1 : ℝ) n := fun n => compWeight_nonneg_three 1 zero_le_one n
  have hbg : bgField S.G' S.a S.ν S.D' = unitPhi S.G' hN2 :=
    bgField_unitBg (isLevel_GP m₁) hN2 (a := compWeight 3 1) ha (unitVec hN2) hHg hDU
  have hbd := (theorem71 hHg hDU).2.2.2.2 δ' hδ'0 hcons.2.2.1 hDR
  have hα : ∀ x : S.G'.Ω 1, S.G'.spacing (x : Torus 3 (6 * 3 ^ m₁ * 3 ^ 2)) ^ 2 *
      ‖bgMult S.G' S.a S.ν S.D' x‖ ≤ bgK1 3 3 2 * δ' := hbd.alpha
  have hsp : ∀ x : Torus 3 (6 * 3 ^ m₁ * 3 ^ 2), 0 < S.G'.spacing x := fun x => spacing_pos _
  refine ⟨{ ha₁ := one_pos, H := hHg, δ' := δ', hδ'0 := hδ'0, hδ' := hδ'a, hD'R := hDR,
            hδ0 := hδ, hfam := ?_, hsm := hsm, hχu := ?_, hnorm := ?_, hβ := ?_,
            hpp := by norm_num, B₅ := witB5, K₂ := witK2, hB5 := le_rfl, hK2 := le_rfl,
            hp40 := ?_, hrad := ?_ }⟩
  · intro x hx
    refine ⟨⟨(dgSetting_rho hm), le_rfl, by show (1 / 2 : ℝ) ≤ 1; norm_num, by show (1 : ℝ) ≤ 2; norm_num⟩, ?_, hx, le_rfl, ?_, ?_⟩
    · intro y
      have hs2 : 0 < S.G'.spacing (y : Torus 3 (6 * 3 ^ m₁ * 3 ^ 2)) ^ 2 := by
        have := hsp y; positivity
      have h1 := hα y
      have h2 : coerciveConst 3 ≥ 0 := (coerciveConst_pos (by norm_num)).le
      rw [le_div_iff₀ (by positivity)]
      nlinarith
    · simpa using hbig
    · intro P; simp
  · rw [chiU_eq_one_iff]
    refine chiUBounds_unitBg (isLevel_GP m₁) hN2 (unitVec hN2) hδ hbg fun y => ?_
    exact lt_of_le_of_lt (hα y) (by linarith)
  · have h0 : S.ν = 0 := rfl
    have hd : S.δ = δ := rfl
    rw [h0, hd, zero_mul, zero_mul]
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


theorem fluctRadius_pos_three : 0 < fluctRadius 3 3 2 := by
  have h1 := deltaStar_pos (d := 3) (L := 3) (N := 2) (by norm_num)
  have h2 := bgC0_pos 3 3 2 (by norm_num)
  have h3 := cK2_pos 3 3 2
  have h4 := bgC1_pos' (d := 3) (L := 3) (N := 2) (by norm_num)
  unfold fluctRadius
  refine lt_min (lt_min (by positivity) (by positivity)) (lt_min (by positivity) (by positivity))

/-- Parameters of the witness: all the numerical conditions are satisfiable, with the lower bound
`T₀` on `T = β_k^{1/2}` arbitrary. -/
theorem exists_witness_params (T₀ : ℝ) :
    ∃ (m₁ : ℕ) (δ δ' T : ℝ), 4 ≤ m₁ ∧ cstarX 3 3 ≤ (3 : ℝ) ^ m₁ ∧ 0 < δ ∧
      δ ^ 2 * smallConstX 3 3 0 ≤ 1 / 4 ∧ 0 < δ' ∧ δ' ≤ thm73C3 3 3 2 / 2 ∧
      bgK1 3 3 2 * δ' ≤ δ / 4 ∧ bgK1 3 3 2 * δ' ≤ coerciveConst 3 / 4 ∧ 0 < T ∧ T₀ ≤ T ∧
      3 * witB5 * witK2 * 2 ≤ T * δ ∧ witB5 * 2 ≤ T * fluctRadius 3 3 2 := by
  obtain ⟨m₁, hm, hbig⟩ := exists_m₁ (cstarX 3 3)
  obtain ⟨δs, hδs, hδs'⟩ := exists_deltaStar 3 3 0
  have hsm : δs ^ 2 * smallConstX 3 3 0 ≤ 1 / 4 := by
    rcases hδs' δs le_rfl with h | h
    · exact h
    · exact absurd hδs h.not_gt
  have hK := bgK1_pos (d := 3) (L := 3) (N := 2)
  have hc := coerciveConst_pos (d := 3) (by norm_num)
  have hC3 := thm73C3_pos (d := 3) (L := 3) (N := 2) (by norm_num)
  set δ' : ℝ := min (thm73C3 3 3 2 / 2) (min (δs / (4 * bgK1 3 3 2))
    (coerciveConst 3 / (4 * bgK1 3 3 2))) with hδ'
  have hδ'0 : 0 < δ' := lt_min (by positivity) (lt_min (by positivity) (by positivity))
  have hb1 : δ' ≤ δs / (4 * bgK1 3 3 2) := (min_le_right _ _).trans (min_le_left _ _)
  have hb2 : δ' ≤ coerciveConst 3 / (4 * bgK1 3 3 2) := (min_le_right _ _).trans (min_le_right _ _)
  obtain ⟨T, hT, hT1, hT2⟩ := exists_large_T (B₅ := witB5) (K₂ := witK2) (pp := 2) hδs
    fluctRadius_pos_three
  refine ⟨m₁, δs, δ', max T (T₀ + 1) , hm, hbig, hδs, hsm, hδ'0, min_le_left _ _, ?_, ?_,
    lt_of_lt_of_le hT (le_max_left _ _), (le_trans (by linarith) (le_max_right _ _)), ?_, ?_⟩
  · calc bgK1 3 3 2 * δ' ≤ bgK1 3 3 2 * (δs / (4 * bgK1 3 3 2)) :=
          mul_le_mul_of_nonneg_left hb1 hK.le
      _ = δs / 4 := by field_simp
  · calc bgK1 3 3 2 * δ' ≤ bgK1 3 3 2 * (coerciveConst 3 / (4 * bgK1 3 3 2)) :=
          mul_le_mul_of_nonneg_left hb2 hK.le
      _ = coerciveConst 3 / 4 := by field_simp
  · exact hT1.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hδs.le)
  · exact hT2.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) fluctRadius_pos_three.le)

/-- **`RayData` is inhabited** (non-degenerate: `N = 2`, `β > 0`, `p₁ = 1 < p⁺ = 2`, `θ ≡ e₀`). -/
theorem nonempty_rayData :
    ∃ (m₁ : ℕ) (S : StepSetting 3 3 6 m₁ 1 2 (rhoSep m₁)),
      0 < S.β ∧ 0 < S.p₁ ∧ S.p₁ < 2 ∧ Nonempty (S.RayData 2) := by
  obtain ⟨m₁, δ, δ', T, hm, hbig, hδ, hsm, hδ'0, hδ'a, hδ'b, hδ'c, hT, -, hT1, hT2⟩ :=
    exists_witness_params 0
  refine ⟨m₁, witnessSetting m₁ (T ^ 2 / 3) δ, ?_, one_pos, (by show (1 : ℝ) < 2; norm_num),
    rayData_witness hm hbig hδ hsm hδ'0 hδ'a hδ'b hδ'c hT hT1 hT2⟩
  show 0 < T ^ 2 / 3
  positivity

/-- **`ClassRegularObs` has a non-degenerate witness** (replacing the `N = 0` witness): `N = 2`,
`β > 0`, `d = L = 3`, the class with zero old terms but the actual background-dependent leading
terms `ℳ_k = svec φ_k`, `ℰ₁ = -β V^{(k)}`, every source `g`. -/
theorem nonempty_classRegularObs_nondegenerate :
    ∃ (m₁ : ℕ) (S : StepSetting 3 3 6 m₁ 1 2 (rhoSep m₁)), 0 < S.β ∧
      ∀ g, Nonempty (S.ClassRegularObs (zeroClass 3 3 6 m₁ 1 2 (rhoSep m₁)) g) := by
  obtain ⟨m₁, S, hβ, hp₁, hlt, ⟨R⟩⟩ := nonempty_rayData
  exact ⟨m₁, S, hβ, fun g => ⟨classRegularObs_zeroClass R hp₁ hlt g⟩⟩

theorem nonempty_classRegularLoc_nondegenerate :
    ∃ (m₁ : ℕ) (S : StepSetting 3 3 6 m₁ 1 2 (rhoSep m₁)), 0 < S.β ∧
      ∀ g, Nonempty (S.ClassRegularLoc (zeroClass 3 3 6 m₁ 1 2 (rhoSep m₁)) g) := by
  obtain ⟨m₁, S, hβ, hp₁, hlt, ⟨R⟩⟩ := nonempty_rayData
  exact ⟨m₁, S, hβ, fun g => ⟨classRegularLoc_zeroClass R hp₁ hlt g⟩⟩

theorem nonempty_classRegular_nondegenerate :
    ∃ (m₁ : ℕ) (S : StepSetting 3 3 6 m₁ 1 2 (rhoSep m₁)), 0 < S.β ∧
      ∀ g, Nonempty (S.ClassRegular (zeroClass 3 3 6 m₁ 1 2 (rhoSep m₁)) g) := by
  obtain ⟨m₁, S, hβ, hp₁, hlt, ⟨R⟩⟩ := nonempty_rayData
  exact ⟨m₁, S, hβ, fun g => ⟨classRegular_zeroClass R hp₁ hlt g⟩⟩

end Witness

end Balaban.Fluctuation
