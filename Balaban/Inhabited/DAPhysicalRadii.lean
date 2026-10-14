/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.StepActivityDirectWitness
public import Balaban.Inhabited.DAPhysicalCutoff
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The radius tower of the direct activity bound

Package 3 (`DAPhysicalRadii`) of `notes/phase1/DAPHYS.md` section 4.

## Inventory of the hypotheses of `stepActivityBound_zeroClass_direct` (T1)

Classes: (S) structural/typing, (G) geometric (independent of beta), (N) numeric relations among
fixed radii and constants (independent of beta), (C) cutoff/radius conditions involving beta and
`p₁`, (A) amplitude and smallness.  Write `βU = β L^{k(d-2)}` (`3 β` for `hatStep`, `k = 1`),
`C = covSupConstC d L N (a_k) κ`.

* (S): `S`, `N₁, L` nonzero, all types and decidable-equality instances, the index/cover/function
  families, `hC : FlCore ..` (its inequalities are (N)), `hconn`, `hrow`, `hk`, `hG`, `H : BgHyp`,
  `ha₁`, `hX₁*`, `hopt*`, `hcov*`, `h𝒯E`, `h𝒯M`, `hRσ`, `hRσ1`, `hR₁`, `hD`, `hbase`, `hN`.
* (G): `hZV, hmarV, hΔV, hΔF, hyF, hlogV, hlogF` (and the `E, M` families, vacuous), `hZν`;
  `BgSetting` margins (`hN`, `hr₀`, `hr`), the cover scale `m₀, m₁`.
* (N): `hκ₀, hκdec, hκ, h1, hMX, hdm, hα, hsmX, hc7, hR, hRs, hsmall, hnum, hnum', hsm`,
  `hκE, hKc, hκ', hκa`, `FlCore`, `ChainNum`, `FlNum`, `hBh0, hBh`, `hρE0, hρM0`.
* (C), with their dependence:
  1. `hδ₁ : √N · βU^{-1/2} · C · c_ψ < δ₁`, that is `c_ψ < δ₁ √βU / (√N C)`;
  2. `hc : (R_σ R₁ + r) ρ < c_ψ`;
  3. `hpρ : p₁ ≤ ρ`, `hp : 0 < p₁`;
  4. `hlt : p₁ < pp`, `R0 : RayData pp`, i.e. `hp40 : pp/(√βU δ) ≤ (3 B₅ K₂)⁻¹`,
     `hrad : B₅ pp/√βU ≤ fluctRadius`, `0 < β`, `0 < pp`;
  5. `hr : 0 < r`.
* (A): `hεb` (`β · prop33Eps(.., δ₁, r, ρ_E, ρ_M) ≤ ε_U`), `hεpos`, `hDA`.

## What is proved

`pLog A₁ p β = A₁ (log β)^p` is the cutoff of the papers (`DAPhysicalCutoff`).  The tower, for the
step family `hatStep m₁ β p₁ δ` (`d = L = 3`, `N = 2`, `k = 1`, `βU = 3β`), with the chart radii and
all (G), (N) data fixed before `β`:

* `p₁ = pLog A₁ p β`, `ρ = p₁`, `pp = 2 p₁`;
* `c_ψ = towerCpsi κ t β = t √(3β) / (2 √N (|C| + 1))`;
* `r = towerR κ t β p₁ = c_ψ/(2 p₁) - 4`, so that `(R_σ R₁ + r) ρ = c_ψ/2 < c_ψ`
  (with `R_σ = R₁ = 2`); `r(β)` is of order `√β/(log β)^p`.

`tower_C_items` proves every (C) item for `β ≥ β₀` with an explicit `β₀`.

## What is NOT proved

The amplitude and smallness hypotheses `hεb`, `hDA` are not discharged.  With the landed
amplitude they cannot hold for large `β`: the source allowance `V/r` forces
`ε_U ≥ const · p₁ √β` (`tower_prop33_lower`, DAPHYS (B)).  The missing estimate is the
scale-uniform cubic bound of the potential remainder (DAPHYS PHYS-CUBIC).
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation
  Balaban.Localization Balaban.Localization.LevelPair Balaban.Localization.I5Inhabited
  Balaban.Polymer Balaban.SmallField.Def6 Filter Topology

/-- The constant `C = covSupConstC 3 3 2 (a_1) κ` of the condition `hδ₁` for `hatStep`. -/
noncomputable def towerC (κ : ℝ) : ℝ := covSupConstC 3 3 2 (compWeight 3 (1 : ℝ) 1) κ

/-- **The radius `c_ψ` of the tower**: `t √(3β) / (2 √N (|C| + 1))`, `N = 2`. -/
noncomputable def towerCpsi (κ t β : ℝ) : ℝ :=
  t * Real.sqrt (3 * β) / (2 * Real.sqrt ((2 : ℕ) : ℝ) * (|towerC κ| + 1))

/-- **The source radius `r` of the tower**: `c_ψ/(2 p₁) - 4`. -/
noncomputable def towerR (κ t β p₁ : ℝ) : ℝ := towerCpsi κ t β / (2 * p₁) - 4

/-- The radius condition of `RayData pp` for `hatStep` at general `pp`. -/
theorem rayData_hatStep_pp (m₁ : ℕ) (p₁ pp : ℝ) (hm : 4 ≤ m₁) (hbig : cstarX 3 3 ≤ (3 : ℝ) ^ m₁)
    {δ δ' T : ℝ} (hpp : 0 < pp) (hδ : 0 < δ) (hsm : δ ^ 2 * smallConstX 3 3 0 ≤ 1 / 4)
    (hδ'0 : 0 < δ')
    (hδ'a : δ' ≤ thm73C3 3 3 2 / 2) (hδ'b : bgK1 3 3 2 * δ' ≤ δ / 4)
    (hδ'c : bgK1 3 3 2 * δ' ≤ coerciveConst 3 / 4) (hT : 0 < T)
    (hT1 : 3 * witB5 * witK2 * pp ≤ T * δ) (hT2 : witB5 * pp ≤ T * fluctRadius 3 3 2) :
    Nonempty ((hatStep m₁ (T ^ 2 / 3) p₁ δ).RayData pp) := by
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
            hpp := hpp, B₅ := witB5, K₂ := witK2, hB5 := le_rfl, hK2 := le_rfl,
            hp40 := ?_, hrad := ?_ }⟩
  · intro x hx
    refine ⟨⟨(dgSettingNu hm), by show (1 / 2 : ℝ) ≤ compWeight 3 1 1; rw [compWeight_one (by norm_num)]; norm_num,
      by show compWeight 3 1 1 ≤ (2 : ℝ); rw [compWeight_one (by norm_num)]; norm_num, by show (1 / 2 : ℝ) ≤ 1; norm_num,
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
    have : witB5 * T⁻¹ * pp = witB5 * pp / T := by field_simp
    rw [this, div_le_iff₀ hT]
    linarith


theorem towerC_abs_pos (κ : ℝ) : 0 < |towerC κ| + 1 := by positivity

theorem towerCpsi_eq (κ t β : ℝ) :
    towerCpsi κ t β = t / (2 * Real.sqrt ((2 : ℕ) : ℝ) * (|towerC κ| + 1)) * Real.sqrt (3 * β) := by
  unfold towerCpsi; ring

/-- **The (C) items of the tower** (T3).  For the fixed data of the landed witness (`m₁`, the radii
`t = δ₁ = ε`, `δ`, `δ'` of `rayData_hatStep`, the rate `κ`) there is an explicit `β₀` such that,
for all `β ≥ β₀` and `p₁ = pLog A₁ p β`, `ρ = p₁`, `pp = 2 p₁`, `c_ψ = towerCpsi κ t β`,
`r = towerR κ t β p₁`: `0 < p₁`, `0 < c_ψ`, `0 < r`, `hδ₁`, `hc` (with `R_σ = R₁ = 2`), `hlt`, and
`RayData (2 p₁)` for `hatStep m₁ β p₁ δ`. -/
theorem tower_C_items {A₁ : ℝ} (hA : 0 < A₁) (p : ℕ) (m₁ : ℕ) (hm : 4 ≤ m₁)
    (hbig : cstarX 3 3 ≤ (3 : ℝ) ^ m₁) {δ δ' t : ℝ} (κ : ℝ) (ht : 0 < t) (hδ : 0 < δ)
    (hsm : δ ^ 2 * smallConstX 3 3 0 ≤ 1 / 4) (hδ'0 : 0 < δ')
    (hδ'a : δ' ≤ thm73C3 3 3 2 / 2) (hδ'b : bgK1 3 3 2 * δ' ≤ δ / 4)
    (hδ'c : bgK1 3 3 2 * δ' ≤ coerciveConst 3 / 4) :
    ∃ β₀ : ℝ, 2 ≤ β₀ ∧ ∀ β : ℝ, β₀ ≤ β →
      0 < pLog A₁ p β ∧ 0 < towerCpsi κ t β ∧ 0 < towerR κ t β (pLog A₁ p β) ∧
      Real.sqrt ((2 : ℕ) : ℝ) * (‖(((hatStep m₁ β (pLog A₁ p β) δ).betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)‖ *
        (covSupConstC 3 3 2 (compWeight 3 (1 : ℝ) 1) κ * towerCpsi κ t β)) < t ∧
      ((2 : ℝ) * 2 + towerR κ t β (pLog A₁ p β)) * pLog A₁ p β < towerCpsi κ t β ∧
      pLog A₁ p β < 2 * pLog A₁ p β ∧
      Nonempty ((hatStep m₁ β (pLog A₁ p β) δ).RayData (2 * pLog A₁ p β)) := by
  have hB : 0 < witB5 := lt_of_lt_of_le one_pos (le_max_left _ _)
  have hK : 0 < witK2 := lt_of_lt_of_le one_pos ((le_max_left _ _).trans (le_max_left _ _))
  have hfR := fluctRadius_pos_three
  have hs : 0 < Real.sqrt ((2 : ℕ) : ℝ) := by positivity
  set κ₁ : ℝ := t / (2 * Real.sqrt ((2 : ℕ) : ℝ) * (|towerC κ| + 1)) with hκ₁
  have hκ₁0 : 0 < κ₁ := by
    have := towerC_abs_pos κ
    rw [hκ₁]; positivity
  set c₀ : ℝ := min (δ / (6 * witB5 * witK2)) (min (fluctRadius 3 3 2 / (2 * witB5)) (κ₁ / 16))
    with hc₀
  have hc₀0 : 0 < c₀ := lt_min (by positivity) (lt_min (by positivity) (by positivity))
  have hc₀1 : c₀ ≤ δ / (6 * witB5 * witK2) := min_le_left _ _
  have hc₀2 : c₀ ≤ fluctRadius 3 3 2 / (2 * witB5) := (min_le_right _ _).trans (min_le_left _ _)
  have hc₀3 : c₀ ≤ κ₁ / 16 := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨max 2 (pLogThreshold A₁ p c₀), le_max_left _ _, fun β hβ => ?_⟩
  have hβ2 : 2 ≤ β := (le_max_left _ _).trans hβ
  have hβ1 : (1 : ℝ) < β := by linarith
  have hp0 : 0 < pLog A₁ p β := pLog_pos hA p hβ1
  have hle : pLog A₁ p β ≤ c₀ * Real.sqrt β :=
    pLog_le_mul_sqrt hA.le p hc₀0 (by linarith) ((le_max_right _ _).trans hβ)
  set x : ℝ := Real.sqrt β with hx
  have hx0 : 0 < x := Real.sqrt_pos.2 (by linarith)
  set T : ℝ := Real.sqrt (3 * β) with hT
  have hxT : x ≤ T := Real.sqrt_le_sqrt (by linarith)
  have hT0 : 0 < T := lt_of_lt_of_le hx0 hxT
  have hcψ : towerCpsi κ t β = κ₁ * T := by rw [towerCpsi_eq]
  have hcψ0 : 0 < towerCpsi κ t β := by rw [hcψ]; positivity
  have h8 : 8 * pLog A₁ p β < towerCpsi κ t β := by
    rw [hcψ]
    have h1 : 8 * pLog A₁ p β ≤ 8 * (c₀ * x) := by linarith
    have h2 : 8 * (c₀ * x) ≤ 8 * (κ₁ / 16 * x) := by
      have := mul_le_mul_of_nonneg_right hc₀3 hx0.le; linarith
    have h3 : κ₁ * x ≤ κ₁ * T := mul_le_mul_of_nonneg_left hxT hκ₁0.le
    have h4 : 0 < κ₁ * x := by positivity
    nlinarith
  have hr0 : 0 < towerR κ t β (pLog A₁ p β) := by
    unfold towerR
    have : 4 < towerCpsi κ t β / (2 * pLog A₁ p β) := by
      rw [lt_div_iff₀ (by positivity)]; linarith
    linarith
  refine ⟨hp0, hcψ0, hr0, ?_, ?_, by linarith, ?_⟩
  · -- hδ₁
    rw [hatStep_betaU, Complex.norm_real, Real.norm_of_nonneg (by positivity), hcψ]
    have e : (3 * β) ^ (-(1 / 2 : ℝ)) = T⁻¹ := by
      rw [Real.rpow_neg (by positivity), ← Real.sqrt_eq_rpow]
    rw [e]
    have e2 : Real.sqrt ((2 : ℕ) : ℝ) * (T⁻¹ * (towerC κ * (κ₁ * T))) =
        towerC κ * t / (2 * (|towerC κ| + 1)) := by
      rw [hκ₁]; have := towerC_abs_pos κ; field_simp
    show Real.sqrt ((2 : ℕ) : ℝ) * (T⁻¹ * (towerC κ * (κ₁ * T))) < t
    rw [e2, div_lt_iff₀ (by have := towerC_abs_pos κ; positivity)]
    nlinarith [le_abs_self (towerC κ), abs_nonneg (towerC κ)]
  · unfold towerR
    have : (2 * 2 + (towerCpsi κ t β / (2 * pLog A₁ p β) - 4)) * pLog A₁ p β =
        towerCpsi κ t β / 2 := by field_simp; ring
    rw [show ((2 : ℝ) * 2) = 2 * 2 from rfl, this]
    linarith
  · have hT1 : 3 * witB5 * witK2 * (2 * pLog A₁ p β) ≤ T * δ := by
      have a1 : c₀ * (6 * witB5 * witK2) ≤ δ := by
        have := (le_div_iff₀ (by positivity)).1 hc₀1; exact this
      have a2 : 3 * witB5 * witK2 * (2 * pLog A₁ p β) ≤ 3 * witB5 * witK2 * (2 * (c₀ * x)) :=
        by gcongr
      have a3 : 3 * witB5 * witK2 * (2 * (c₀ * x)) = (c₀ * (6 * witB5 * witK2)) * x := by ring
      have a4 : (c₀ * (6 * witB5 * witK2)) * x ≤ δ * x := mul_le_mul_of_nonneg_right a1 hx0.le
      nlinarith
    have hT2 : witB5 * (2 * pLog A₁ p β) ≤ T * fluctRadius 3 3 2 := by
      have a1 : c₀ * (2 * witB5) ≤ fluctRadius 3 3 2 := (le_div_iff₀ (by positivity)).1 hc₀2
      have a2 : witB5 * (2 * pLog A₁ p β) ≤ witB5 * (2 * (c₀ * x)) := by gcongr
      have a3 : witB5 * (2 * (c₀ * x)) = (c₀ * (2 * witB5)) * x := by ring
      have a4 : (c₀ * (2 * witB5)) * x ≤ fluctRadius 3 3 2 * x :=
        mul_le_mul_of_nonneg_right a1 hx0.le
      nlinarith
    have hTsq : β = T ^ 2 / 3 := by
      rw [hT, Real.sq_sqrt (by linarith)]; ring
    have := rayData_hatStep_pp m₁ (pLog A₁ p β) (2 * pLog A₁ p β) hm hbig (by positivity) hδ hsm
      hδ'0 hδ'a hδ'b hδ'c hT0 hT1 hT2
    rw [← hTsq] at this
    exact this

end Balaban.Inhabited
