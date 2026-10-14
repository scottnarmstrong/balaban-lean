/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.LevelStepSetting
public import Balaban.Inhabited.StepActivityDirectPhysicalRates
public import Balaban.Fluctuation.ScaleUniform
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

/-!
# The radius tower of the fluctuation step at a general scale

`DAPhysicalRadii` proves the cutoff and radius hypotheses of the zero-class activity theorem for the
witness step `hatStep` (`k = 1`, `N₁ = 9`, `ν = 1/81`, `β_1 = 3β`).  This file proves them for the
step `hatStepK k m₁ hk ν β p₁ δ` at every scale `k ≥ 1`, on every torus parameter `N₁ > 5` and for
every mass `0 ≤ ν`, `ν · 3^{2(k+1)} ≤ 1`, with a threshold on `β` that does not depend on `k`,
`N₁`, `ν`.  Write `β_k = β · 3^k` (`hatStepK_betaU`).

* `flCore_level_transfer`: `FlCore` of a pair of consecutive whole-lattice levels consists of
  numerical inequalities, which contain neither the torus nor the scale nor the mass, and of four
  fields about the pair (`DGSetting`, `BgHyp`, `FootLocal`, `Precedes`).  Hence the numerical data of
  one pair serve every pair with the same `d`, `L`, `m₁`.
* `lvCpsi κ t b = t √b / (2 √N (C_max + 1))`, `N = 2`, with `C_max = covSupMaxC 3 3 2 κ` the maximum
  of the covariance constant over the weights `a_k ∈ [1/2, 2]`; `lvR κ t b p₁ = c_ψ/(2 p₁) - 4`.
  The radii are functions of `β_k`; the constants `t`, `κ` are fixed before `β`.
* `rayData_hatStepK_pp`: `RayData p⁺` for `hatStepK`, with the weight-uniform constants
  `B₅ = B5Max`, `K₂ = K2Max`, under `3 B₅ K₂ p⁺ ≤ √β_k δ` and `B₅ p⁺ ≤ √β_k · fluctRadius`.
* `scale_C_items`: for every cutoff `0 < p₁ ≤ A₁ (log β_k)^p` (in particular the cutoff of the
  papers at the scale, `p₁ = A₁ (log β_k)^p`), with `ρ = p₁`, `p⁺ = 2 p₁`,
  `c_ψ = lvCpsi κ t β_k`, `r = lvR κ t β_k p₁`: for all `β ≥ β₀`, every `k ≥ 1`, `N₁ > 5` and
  admissible `ν`, the hypotheses `0 < c_ψ`, `0 < r`, `hδ₁`, `hc` (`R_σ = R₁ = 2`), `p₁ < p⁺` and
  `RayData (2 p₁)` hold.  `β₀` depends on `A₁, p, t, κ, δ` only: every condition is an inequality
  `p₁ ≤ c √β_k`, and `β_k ≥ β`.
* `scale_amp_le`, `scale_amp_exists`: the amplitude `β_k P / r³ + K / (β r)` is at most
  `C (log β_k)^{3p} / √β_k` for `β_k ≥ β₁`, `β ≥ 1`.  The source allowance `K/(β r)` has the bare
  `β` in the denominator; `β ≥ 1` and `1/r ≤ 4 A₁ (log β_k)^p/(κ₁ √β_k)` suffice.

What is proved: the cutoff, radius and `RayData` hypotheses at every scale with `ν · 3^{2(k+1)} ≤ 1`
(mass `ν ≥ 0`), with constants independent of the scale, the torus and the mass.  What is not
proved here: scales with a larger mass, and the datum bound `hBh` (it needs `ν > 0`, see
`ScaleActivityFinal`).
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation

section Transfer

variable {d L N₁ N₁' m₁ K K' N : ℕ} [NeZero N₁] [NeZero N₁'] [NeZero L] {ϱ ϱm ϱ₀ ϱm₀ : ℝ}

/-- **`FlCore` passes from one pair of consecutive levels to another.**  The numerical fields of
`FlCore` contain neither the torus, nor the level, nor the mass; the remaining fields follow from
`DGSetting`, `OpSetting`, the levels and `BgHyp` of the new pair (`footLocal_level`). -/
theorem flCore_level_transfer {Gp₀ : GeneratingSet d L (N₁' * L ^ m₁) K' ϱ₀}
    {Hm₀ : GeneratingSet d L (N₁' * L ^ m₁) K' ϱm₀}
    {Gp : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {Hm : GeneratingSet d L (N₁ * L ^ m₁) K ϱm}
    {n : ℕ} {a₁ ν₀ ν c BG κ eps c₂ BG₂ δ₁ : ℝ}
    (hC : FlCore N Gp₀ Hm₀ a₁ ν₀ c BG κ eps (levelKc d L) (Cchi d L) c₂ BG₂ δ₁)
    (S : DGSetting Gp (compWeight L a₁) ν) (SH : Dec2.OpSetting Hm (compWeight L a₁) ν)
    (hG : IsLevel Hm n) (hG' : IsLevel Gp (n + 1)) (HBp : BgHyp d L K ϱ (compWeight L a₁) ν) :
    FlCore N Gp Hm a₁ ν c BG κ eps (levelKc d L) (Cchi d L) c₂ BG₂ δ₁ :=
  { hS := hC.hS, Sp := S, HBp := HBp, hκ := hC.hκ, hM := hC.hM, eps_pos := hC.eps_pos,
    small1 := hC.small1, c7le := hC.c7le, hS2 := hC.hS2, SM := footLocal_level S SH hG hG',
    hM2 := hC.hM2, hPmp := hG.precedes hG' hG'.bounds.2, δ₁_pos := hC.δ₁_pos,
    δ₁_le := hC.δ₁_le, B_le := hC.B_le, B_one := hC.B_one, phi_lt := hC.phi_lt }

end Transfer

end Balaban.Localization

namespace Balaban.Inhabited

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation
  Balaban.Localization Balaban.Localization.LevelPair Balaban.Localization.I5Inhabited
  Balaban.Polymer Balaban.SmallField.Def6 Filter Topology

namespace LevelStep

/-! ### The radii -/

theorem covSupMaxC_nonneg (κ : ℝ) : 0 ≤ covSupMaxC 3 3 2 κ := by
  have ha : (1 : ℝ) ∈ Set.Icc (1 / 2 : ℝ) 2 := ⟨by norm_num, by norm_num⟩
  exact (covSupConstC_nonneg (N := 2) (d := 3) (L := 3) (by norm_num) (by norm_num) one_pos κ).trans
    (covSupConstC_le_covSupMaxC (by norm_num) (by norm_num) κ ha)

/-- The weight `a_k` of the step lies in `[1/2, 2]` at every scale `k ≥ 1`. -/
theorem compWeight_three_mem {k : ℕ} (hk : 1 ≤ k) :
    compWeight 3 (1 : ℝ) k ∈ Set.Icc (1 / 2 : ℝ) 2 :=
  compWeight_mem_Icc le_rfl (by norm_num) (by norm_num) hk

/-- **The radius `c_ψ` at the scale**: `t √β_k / (2 √N (C_max + 1))`, `N = 2`, as a function of
`b = β_k`. -/
noncomputable def lvCpsi (κ t b : ℝ) : ℝ :=
  t * Real.sqrt b / (2 * Real.sqrt ((2 : ℕ) : ℝ) * (covSupMaxC 3 3 2 κ + 1))

/-- **The source radius `r` at the scale**: `c_ψ/(2 p₁) - 4`. -/
noncomputable def lvR (κ t b p₁ : ℝ) : ℝ := lvCpsi κ t b / (2 * p₁) - 4

/-- The constant `κ₁ = t / (2 √N (C_max + 1))` of the radii. -/
noncomputable def lvKappa (κ t : ℝ) : ℝ :=
  t / (2 * Real.sqrt ((2 : ℕ) : ℝ) * (covSupMaxC 3 3 2 κ + 1))

theorem lvKappa_pos (κ : ℝ) {t : ℝ} (ht : 0 < t) : 0 < lvKappa κ t := by
  have := covSupMaxC_nonneg κ
  unfold lvKappa
  positivity

theorem lvCpsi_eq (κ t b : ℝ) : lvCpsi κ t b = lvKappa κ t * Real.sqrt b := by
  unfold lvCpsi lvKappa
  ring

/-! ### `RayData` at a general scale -/

section Ray

variable {N₁ : ℕ} [NeZero N₁]

theorem hatStepK_domain (k m₁ : ℕ) (hk : 1 ≤ k) (ν β p₁ δ : ℝ) {δ' : ℝ} (hδ'0 : 0 < δ') :
    InDomainR (hatStepK (N₁ := N₁) k m₁ hk ν β p₁ δ).G' (hatStepK (N₁ := N₁) k m₁ hk ν β p₁ δ).ν δ'
      (hatStepK (N₁ := N₁) k m₁ hk ν β p₁ δ).D' := by
  refine ⟨fun _ => unitVec hN2, unitVec hN2,
    (exists_inPsiTildeC (G := lvTop N₁ m₁ k (rhoSep m₁)) hN2 ν hδ'0 hδ'0).toInPsiTilde, ?_, ?_⟩
  · intro x hx i
    exact unitBg_Ψ_of_mem (lvTop N₁ m₁ k (rhoSep m₁)) hN2 (unitVec hN2) hx i
  · intro x hx i
    exact unitBg_h_of_mem (lvTop N₁ m₁ k (rhoSep m₁)) hN2 (unitVec hN2) hx i

/-- **`RayData` for the step at scale `k`**, with the weight-uniform constants `B5Max`, `K2Max`:
for `β_k = β · 3^k = T²`, `3 B₅ K₂ p⁺ ≤ T δ` and `B₅ p⁺ ≤ T · fluctRadius`. -/
theorem rayData_hatStepK_pp (k m₁ : ℕ) (hk : 1 ≤ k) (p₁ pp : ℝ) (hm : 4 ≤ m₁) (hN : 5 < N₁)
    (hbig : cstarX 3 3 ≤ (3 : ℝ) ^ m₁) {ν : ℝ} (hν0 : 0 ≤ ν) (hν : ν * 3 ^ (2 * (k + 1)) ≤ 1)
    {δ δ' T β : ℝ} (hpp : 0 < pp) (hδ : 0 < δ) (hsm : δ ^ 2 * smallConstX 3 3 0 ≤ 1 / 4)
    (hδ'0 : 0 < δ')
    (hδ'a : δ' ≤ thm73C3 3 3 2 / 2) (hδ'b : bgK1 3 3 2 * δ' ≤ δ / 4)
    (hδ'c : bgK1 3 3 2 * δ' ≤ coerciveConst 3 / 4) (hT : 0 < T) (hβ : β * 3 ^ k = T ^ 2)
    (hT1 : 3 * B5Max 3 3 2 * K2Max 3 3 2 * pp ≤ T * δ)
    (hT2 : B5Max 3 3 2 * pp ≤ T * fluctRadius 3 3 2) :
    Nonempty ((hatStepK (N₁ := N₁) k m₁ hk ν β p₁ δ).RayData pp) := by
  set S := hatStepK (N₁ := N₁) k m₁ hk ν β p₁ δ with hS
  have hbetaU : S.betaU = T ^ 2 := by
    rw [hS, hatStepK_betaU, hβ]
  have hβ0 : 0 < β := by
    have h3 : (0 : ℝ) < 3 ^ k := by positivity
    have : 0 < β * 3 ^ k := by rw [hβ]; positivity
    exact pos_of_mul_pos_left this h3.le
  have hHg : BgHyp 3 3 (k + 1) (rhoSep m₁) (compWeight 3 1) ν := bgHyp_lv m₁ hν0 hν
  have hcons := theta_consts (d := 3) (L := 3) (N := 2) (by norm_num) hδ'0 hδ'a
  have hDR : InDomainR S.G' S.ν δ' S.D' := hatStepK_domain k m₁ hk ν β p₁ δ hδ'0
  have hDU : InUnionDomainR S.G' (bgC1 3 3 2) S.ν S.D' := ⟨δ', hδ'0, hcons.2.2.1, hDR⟩
  have hbg : bgField S.G' S.a S.ν S.D' = unitPhi S.G' hN2 := bgField_unit_lv hHg hDU
  have hbd := (theorem71 hHg hDU).2.2.2.2 δ' hδ'0 hcons.2.2.1 hDR
  have hα : ∀ x : S.G'.Ω 1, S.G'.spacing (x : CTorus 3 3 N₁ m₁ (k + 1)) ^ 2 *
      ‖bgMult S.G' S.a S.ν S.D' x‖ ≤ bgK1 3 3 2 * δ' := hbd.alpha
  have hsp : ∀ x : CTorus 3 3 N₁ m₁ (k + 1), 0 < S.G'.spacing x := fun x => spacing_pos _
  have hB : 0 < B5Max 3 3 2 := lt_of_lt_of_le one_pos (le_max_left _ _)
  have hK : 0 < K2Max 3 3 2 :=
    lt_of_lt_of_le one_pos ((le_max_left _ _).trans (le_max_left _ _))
  refine ⟨{ ha₁ := one_pos, H := hHg, δ' := δ', hδ'0 := hδ'0, hδ' := hδ'a, hD'R := hDR,
            hδ0 := hδ, hfam := ?_, hsm := hsm, hχu := ?_, hnorm := ?_, hβ := hβ0,
            hpp := hpp, B₅ := B5Max 3 3 2, K₂ := K2Max 3 3 2,
            hB5 := B5_le_B5Max (by norm_num) le_rfl (compWeight_three_mem hk),
            hK2 := K2_le_K2Max, hp40 := ?_, hrad := ?_ }⟩
  · intro x hx
    refine ⟨⟨dgSetting_lv hm hN hν0 hν, ((dgSetting_lv hm hN hν0 hν).weights k hk (by omega)).1,
      ((dgSetting_lv hm hN hν0 hν).weights k hk (by omega)).2, by show (1 / 2 : ℝ) ≤ 1; norm_num,
      by show (1 : ℝ) ≤ 2; norm_num⟩, ?_, hx, le_rfl, ?_, ?_⟩
    · intro y
      have hs2 : 0 < S.G'.spacing (y : CTorus 3 3 N₁ m₁ (k + 1)) ^ 2 := by
        have := hsp y; positivity
      have h1 := hα y
      have h2 : coerciveConst 3 ≥ 0 := (coerciveConst_pos (by norm_num)).le
      rw [le_div_iff₀ (by positivity)]
      nlinarith
    · simpa using hbig
    · intro P; simp
  · rw [chiU_eq_one_iff]
    refine chiUBounds_unitBg_nu (isLevel_lvTop (N₁ := N₁) (m₁ := m₁) (k := k) (ϱ := rhoSep m₁))
      hN2 hδ hbg fun y => ?_
    exact lt_of_le_of_lt (hα y) (by linarith)
  · have hh : ∑ i, S.h₀ i ^ 2 = 1 := sum_sq_unitVec hN2
    rw [hh, sub_self, abs_zero, mul_zero]
    have hd : S.δ = δ := rfl
    rw [hd]
    positivity
  · have hd : S.δ = δ := rfl
    rw [hbetaU, hd]
    have e : (T ^ 2) ^ (1 / 2 : ℝ) = T := by
      rw [← Real.sqrt_eq_rpow, Real.sqrt_sq hT.le]
    rw [e, div_le_iff₀ (by positivity)]
    rw [inv_mul_eq_div, le_div_iff₀ (by positivity)]
    nlinarith
  · rw [hbetaU]
    have e : (T ^ 2) ^ (-(1 / 2) : ℝ) = T⁻¹ := by
      rw [Real.rpow_neg (by positivity), ← Real.sqrt_eq_rpow, Real.sqrt_sq hT.le]
    rw [e]
    have : B5Max 3 3 2 * T⁻¹ * pp = B5Max 3 3 2 * pp / T := by field_simp
    rw [this, div_le_iff₀ hT]
    linarith

end Ray

/-! ### The cutoff and radius hypotheses at every scale -/

/-- **The cutoff and radius hypotheses at every scale.**  For the fixed data (`m₁`, the radii
`t = δ₁ = ε`, `δ`, `δ'`, the rate `κ`) there is `β₀ ≥ 2`, depending on `A₁, p, t, κ, δ` only, such
that for every scale `k ≥ 1`, every torus parameter `N₁ > 5`, every mass `0 ≤ ν`,
`ν · 3^{2(k+1)} ≤ 1`, every `β ≥ β₀` and every cutoff `0 < p₁ ≤ A₁ (log β_k)^p`, `β_k = β · 3^k`
(in particular the cutoff of the papers at the scale, `p₁ = A₁ (log β_k)^p`), with `ρ = p₁`,
`p⁺ = 2 p₁`, `c_ψ = lvCpsi κ t β_k`, `r = lvR κ t β_k p₁`: `0 < c_ψ`, `0 < r`, `hδ₁`, `hc` (with
`R_σ = R₁ = 2`), `p₁ < p⁺`, and `RayData (2 p₁)` for `hatStepK k m₁ hk ν β p₁ δ`. -/
theorem scale_C_items {A₁ : ℝ} (hA : 0 < A₁) (p : ℕ) (m₁ : ℕ) (hm : 4 ≤ m₁)
    (hbig : cstarX 3 3 ≤ (3 : ℝ) ^ m₁) {δ δ' t : ℝ} (κ : ℝ) (ht : 0 < t) (hδ : 0 < δ)
    (hsm : δ ^ 2 * smallConstX 3 3 0 ≤ 1 / 4) (hδ'0 : 0 < δ')
    (hδ'a : δ' ≤ thm73C3 3 3 2 / 2) (hδ'b : bgK1 3 3 2 * δ' ≤ δ / 4)
    (hδ'c : bgK1 3 3 2 * δ' ≤ coerciveConst 3 / 4) :
    ∃ β₀ : ℝ, 2 ≤ β₀ ∧ ∀ (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁], 5 < N₁ →
      ∀ ν : ℝ, 0 ≤ ν → ν * 3 ^ (2 * (k + 1)) ≤ 1 → ∀ β : ℝ, β₀ ≤ β →
      ∀ p₁ : ℝ, 0 < p₁ → p₁ ≤ pLog A₁ p (β * 3 ^ k) →
      0 < lvCpsi κ t (β * 3 ^ k) ∧ 0 < lvR κ t (β * 3 ^ k) p₁ ∧
      Real.sqrt ((2 : ℕ) : ℝ) *
        (‖(((hatStepK (N₁ := N₁) k m₁ hk ν β p₁ δ).betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)‖ *
          (covSupConstC 3 3 2 (compWeight 3 (1 : ℝ) k) κ * lvCpsi κ t (β * 3 ^ k))) < t ∧
      ((2 : ℝ) * 2 + lvR κ t (β * 3 ^ k) p₁) * p₁ < lvCpsi κ t (β * 3 ^ k) ∧
      p₁ < 2 * p₁ ∧
      Nonempty ((hatStepK (N₁ := N₁) k m₁ hk ν β p₁ δ).RayData (2 * p₁)) := by
  have hB : 0 < B5Max 3 3 2 := lt_of_lt_of_le one_pos (le_max_left _ _)
  have hK : 0 < K2Max 3 3 2 :=
    lt_of_lt_of_le one_pos ((le_max_left _ _).trans (le_max_left _ _))
  have hfR := fluctRadius_pos_three
  have hs : 0 < Real.sqrt ((2 : ℕ) : ℝ) := by positivity
  have hCm := covSupMaxC_nonneg κ
  set κ₁ : ℝ := lvKappa κ t with hκ₁
  have hκ₁0 : 0 < κ₁ := lvKappa_pos κ ht
  set c₀ : ℝ := min (δ / (6 * B5Max 3 3 2 * K2Max 3 3 2))
    (min (fluctRadius 3 3 2 / (2 * B5Max 3 3 2)) (κ₁ / 16)) with hc₀
  have hc₀0 : 0 < c₀ := lt_min (by positivity) (lt_min (by positivity) (by positivity))
  have hc₀1 : c₀ ≤ δ / (6 * B5Max 3 3 2 * K2Max 3 3 2) := min_le_left _ _
  have hc₀2 : c₀ ≤ fluctRadius 3 3 2 / (2 * B5Max 3 3 2) :=
    (min_le_right _ _).trans (min_le_left _ _)
  have hc₀3 : c₀ ≤ κ₁ / 16 := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨max 2 (pLogThreshold A₁ p c₀), le_max_left _ _, ?_⟩
  intro k hk N₁ _ hN ν hν0 hν β hβ p₁ hp0 hp₁
  have hβ2 : 2 ≤ β := (le_max_left _ _).trans hβ
  have h3k : (1 : ℝ) ≤ 3 ^ k := one_le_pow₀ (by norm_num)
  set b : ℝ := β * 3 ^ k with hb
  have hbβ : β ≤ b := by rw [hb]; nlinarith
  have hb1 : (1 : ℝ) < b := by linarith
  have hb0 : 0 < b := by linarith
  have hle : p₁ ≤ c₀ * Real.sqrt b :=
    hp₁.trans (pLog_le_mul_sqrt hA.le p hc₀0 hb1.le (((le_max_right _ _).trans hβ).trans hbβ))
  set T : ℝ := Real.sqrt b with hT
  have hT0 : 0 < T := Real.sqrt_pos.2 hb0
  have hcψ : lvCpsi κ t b = κ₁ * T := lvCpsi_eq κ t b
  have hcψ0 : 0 < lvCpsi κ t b := by rw [hcψ]; positivity
  have h8 : 8 * p₁ < lvCpsi κ t b := by
    rw [hcψ]
    have h2 : c₀ * T ≤ κ₁ / 16 * T := mul_le_mul_of_nonneg_right hc₀3 hT0.le
    have h4 : 0 < κ₁ * T := by positivity
    nlinarith
  have hr0 : 0 < lvR κ t b p₁ := by
    unfold lvR
    have : 4 < lvCpsi κ t b / (2 * p₁) := by
      rw [lt_div_iff₀ (by positivity)]; linarith
    linarith
  refine ⟨hcψ0, hr0, ?_, ?_, by linarith, ?_⟩
  · -- hδ₁
    rw [hatStepK_betaU, Complex.norm_real, Real.norm_of_nonneg (by positivity), hcψ]
    have e : b ^ (-(1 / 2 : ℝ)) = T⁻¹ := by
      rw [Real.rpow_neg hb0.le, ← Real.sqrt_eq_rpow]
    show Real.sqrt ((2 : ℕ) : ℝ) * (b ^ (-(1 / 2 : ℝ)) *
      (covSupConstC 3 3 2 (compWeight 3 (1 : ℝ) k) κ * (κ₁ * T))) < t
    rw [e]
    have hmem := compWeight_three_mem hk
    have hC0 : 0 ≤ covSupConstC 3 3 2 (compWeight 3 (1 : ℝ) k) κ :=
      covSupConstC_nonneg (by norm_num) (by norm_num) (by linarith [hmem.1]) κ
    have hCle : covSupConstC 3 3 2 (compWeight 3 (1 : ℝ) k) κ ≤ covSupMaxC 3 3 2 κ :=
      covSupConstC_le_covSupMaxC (by norm_num) (by norm_num) κ hmem
    have e2 : Real.sqrt ((2 : ℕ) : ℝ) * (T⁻¹ *
        (covSupConstC 3 3 2 (compWeight 3 (1 : ℝ) k) κ * (κ₁ * T))) =
        covSupConstC 3 3 2 (compWeight 3 (1 : ℝ) k) κ * t / (2 * (covSupMaxC 3 3 2 κ + 1)) := by
      rw [hκ₁]; unfold lvKappa; field_simp
    rw [e2, div_lt_iff₀ (by positivity)]
    nlinarith
  · unfold lvR
    have : (2 * 2 + (lvCpsi κ t b / (2 * p₁) - 4)) * p₁ = lvCpsi κ t b / 2 := by
      field_simp; ring
    rw [this]
    linarith
  · have hT1 : 3 * B5Max 3 3 2 * K2Max 3 3 2 * (2 * p₁) ≤ T * δ := by
      have a1 : c₀ * (6 * B5Max 3 3 2 * K2Max 3 3 2) ≤ δ :=
        (le_div_iff₀ (by positivity)).1 hc₀1
      have a2 : 3 * B5Max 3 3 2 * K2Max 3 3 2 * (2 * p₁) ≤
          3 * B5Max 3 3 2 * K2Max 3 3 2 * (2 * (c₀ * T)) := by gcongr
      have a4 : (c₀ * (6 * B5Max 3 3 2 * K2Max 3 3 2)) * T ≤ δ * T :=
        mul_le_mul_of_nonneg_right a1 hT0.le
      calc _ ≤ 3 * B5Max 3 3 2 * K2Max 3 3 2 * (2 * (c₀ * T)) := a2
        _ = (c₀ * (6 * B5Max 3 3 2 * K2Max 3 3 2)) * T := by ring
        _ ≤ δ * T := a4
        _ = T * δ := mul_comm _ _
    have hT2 : B5Max 3 3 2 * (2 * p₁) ≤ T * fluctRadius 3 3 2 := by
      have a1 : c₀ * (2 * B5Max 3 3 2) ≤ fluctRadius 3 3 2 :=
        (le_div_iff₀ (by positivity)).1 hc₀2
      have a2 : B5Max 3 3 2 * (2 * p₁) ≤ B5Max 3 3 2 * (2 * (c₀ * T)) := by gcongr
      have a4 : (c₀ * (2 * B5Max 3 3 2)) * T ≤ fluctRadius 3 3 2 * T :=
        mul_le_mul_of_nonneg_right a1 hT0.le
      calc _ ≤ B5Max 3 3 2 * (2 * (c₀ * T)) := a2
        _ = (c₀ * (2 * B5Max 3 3 2)) * T := by ring
        _ ≤ fluctRadius 3 3 2 * T := a4
        _ = T * fluctRadius 3 3 2 := mul_comm _ _
    have hTsq : β * 3 ^ k = T ^ 2 := by
      rw [hT, Real.sq_sqrt hb0.le]
    exact rayData_hatStepK_pp k m₁ hk p₁ (2 * p₁) hm hN hbig hν0 hν
      (by positivity) hδ hsm hδ'0 hδ'a hδ'b hδ'c hT0 hTsq hT1 hT2

/-! ### The amplitude -/

/-- **The elementary estimate of the amplitude at a scale.**  For `x = √β_k ≥ 1`,
`w = (log β_k)^p ≥ 1`, a radius `r` with `κ₁ x ≤ 4 A w r`, and `β ≥ 1`,
`x² (P / r³) + K / (β r) ≤ (P (4A/κ₁)³ + 4 A K / κ₁) w³ / x`. -/
theorem scale_amp_le {x w r P K A κ₁ β : ℝ} (hx : 1 ≤ x) (hw : 1 ≤ w) (hA : 0 < A) (hκ : 0 < κ₁)
    (hP : 0 ≤ P) (hK : 0 ≤ K) (hr : κ₁ * x ≤ 4 * A * w * r) (hβ : 1 ≤ β) :
    x ^ 2 * (P / r ^ 3) + K / (β * r) ≤
      (P * (4 * A / κ₁) ^ 3 + 4 * A * K / κ₁) * w ^ 3 / x := by
  have hx0 : 0 < x := by linarith
  have hw0 : 0 < w := by linarith
  have hr0 : 0 < r := by
    by_contra h
    have h := not_lt.1 h
    have : 4 * A * w * r ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by positivity) h
    nlinarith [mul_pos hκ hx0]
  set ρ0 : ℝ := κ₁ * x / (4 * A * w) with hρ0
  have hρ0pos : 0 < ρ0 := by positivity
  have hrρ : ρ0 ≤ r := by
    rw [hρ0, div_le_iff₀ (by positivity)]; linarith
  have h1 : x ^ 2 * (P / r ^ 3) ≤ x ^ 2 * (P / ρ0 ^ 3) := by
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    exact div_le_div_of_nonneg_left hP (by positivity) (pow_le_pow_left₀ hρ0pos.le hrρ 3)
  have h2 : K / (β * r) ≤ K / ρ0 := by
    refine div_le_div_of_nonneg_left hK hρ0pos ?_
    calc ρ0 ≤ r := hrρ
      _ = 1 * r := (one_mul r).symm
      _ ≤ β * r := mul_le_mul_of_nonneg_right hβ hr0.le
  have e1 : x ^ 2 * (P / ρ0 ^ 3) = P * (4 * A / κ₁) ^ 3 * w ^ 3 / x := by
    rw [hρ0]; field_simp
  have e2 : K / ρ0 = (4 * A * K / κ₁) * (w / x) := by
    rw [hρ0]; field_simp
  have h3 : w / x ≤ w ^ 3 / x := by
    have a1 : w ≤ w ^ 3 := by nlinarith [mul_nonneg hw0.le hw0.le]
    exact div_le_div_of_nonneg_right a1 hx0.le
  have h4 : K / ρ0 ≤ (4 * A * K / κ₁) * (w ^ 3 / x) := by
    rw [e2]; exact mul_le_mul_of_nonneg_left h3 (by positivity)
  calc _ ≤ P * (4 * A / κ₁) ^ 3 * w ^ 3 / x + (4 * A * K / κ₁) * (w ^ 3 / x) := by
        rw [← e1]; exact add_le_add h1 (h2.trans h4)
    _ = _ := by ring

/-- **The amplitude at every scale is at most `C (log β_k)^{3p}/√β_k`.**  For `A₁ > 0` there are
`β₁ ≥ e` and `C > 0` (depending on `A₁, p, κ, t, P, K`) such that for `b = β_k ≥ β₁`, `β ≥ 1` and
every cutoff `0 < p₁ ≤ A₁ (log b)^p` the radius `r = lvR κ t b p₁` satisfies
`b (P / r³) + K / (β r) ≤ C (log b)^{3p} / √b`. -/
theorem scale_amp_exists {A₁ κ t P K : ℝ} (hA : 0 < A₁) (p : ℕ) (ht : 0 < t) (hP : 0 ≤ P)
    (hK : 0 ≤ K) :
    ∃ β₁ C : ℝ, Real.exp 1 ≤ β₁ ∧ 0 < C ∧ ∀ b : ℝ, β₁ ≤ b → ∀ β : ℝ, 1 ≤ β →
      ∀ p₁ : ℝ, 0 < p₁ → p₁ ≤ pLog A₁ p b →
      b * (P / (lvR κ t b p₁) ^ 3) + K / (β * lvR κ t b p₁) ≤
        C * (Real.log b) ^ (3 * p) / Real.sqrt b := by
  set κ₁ : ℝ := lvKappa κ t with hκ₁def
  have hκ₁ : 0 < κ₁ := lvKappa_pos κ ht
  have hthr : 0 < κ₁ / 16 := by positivity
  refine ⟨max (Real.exp 1) (pLogThreshold A₁ p (κ₁ / 16)),
    P * (4 * A₁ / κ₁) ^ 3 + 4 * A₁ * K / κ₁ + 1, le_max_left _ _, by positivity, ?_⟩
  intro b hb β hβ p₁ hp0 hp₁
  have hexp : Real.exp 1 ≤ b := le_trans (le_max_left _ _) hb
  have hbp : pLogThreshold A₁ p (κ₁ / 16) ≤ b := le_trans (le_max_right _ _) hb
  have hb1 : 1 ≤ b := le_trans (Real.one_le_exp (by norm_num)) hexp
  have hb0 : 0 < b := by linarith
  have hℓ : 1 ≤ Real.log b := (Real.le_log_iff_exp_le hb0).2 hexp
  have hx1 : 1 ≤ Real.sqrt b := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt hb1
  have hw1 : 1 ≤ (Real.log b) ^ p := one_le_pow₀ hℓ
  have hpL : pLog A₁ p b = A₁ * (Real.log b) ^ p := rfl
  have hp16 : pLog A₁ p b ≤ κ₁ / 16 * Real.sqrt b := pLog_le_mul_sqrt hA.le p hthr hb1 hbp
  have hcψeq : lvCpsi κ t b = κ₁ * Real.sqrt b := lvCpsi_eq κ t b
  have hc16 : 16 * p₁ ≤ lvCpsi κ t b := by rw [hcψeq]; linarith
  have e : 4 * p₁ * lvR κ t b p₁ = 2 * lvCpsi κ t b - 16 * p₁ := by
    unfold lvR; field_simp; ring
  have hcψ0 : 0 < lvCpsi κ t b := by rw [hcψeq]; positivity
  have hr0 : 0 < lvR κ t b p₁ := by
    by_contra h
    have h := not_lt.1 h
    have : 4 * p₁ * lvR κ t b p₁ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by positivity) h
    linarith
  have hrbound : κ₁ * Real.sqrt b ≤ 4 * A₁ * (Real.log b) ^ p * lvR κ t b p₁ := by
    calc κ₁ * Real.sqrt b = lvCpsi κ t b := hcψeq.symm
      _ ≤ 2 * lvCpsi κ t b - 16 * p₁ := by linarith
      _ = 4 * p₁ * lvR κ t b p₁ := e.symm
      _ ≤ 4 * pLog A₁ p b * lvR κ t b p₁ :=
        mul_le_mul_of_nonneg_right (by linarith) hr0.le
      _ = _ := by rw [hpL]; ring
  have hamp := scale_amp_le (x := Real.sqrt b) (w := (Real.log b) ^ p)
    (r := lvR κ t b p₁) (P := P) (K := K) (A := A₁) (κ₁ := κ₁) (β := β) hx1 hw1 hA hκ₁
    hP hK hrbound hβ
  rw [Real.sq_sqrt hb0.le, ← pow_mul, show p * 3 = 3 * p by ring] at hamp
  refine hamp.trans ?_
  have : 0 ≤ (Real.log b) ^ (3 * p) / Real.sqrt b := by positivity
  calc _ = (P * (4 * A₁ / κ₁) ^ 3 + 4 * A₁ * K / κ₁) *
        ((Real.log b) ^ (3 * p) / Real.sqrt b) := by ring
    _ ≤ (P * (4 * A₁ / κ₁) ^ 3 + 4 * A₁ * K / κ₁ + 1) *
        ((Real.log b) ^ (3 * p) / Real.sqrt b) :=
      mul_le_mul_of_nonneg_right (by linarith) this
    _ = _ := by ring

end LevelStep

end Balaban.Inhabited
