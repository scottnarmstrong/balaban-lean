/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.DAPhysicalTower
public import Balaban.Fluctuation.StepActivityDirectScaled
public import Balaban.Fluctuation.DARateNumerics
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

/-!
# The zero-class activity bound at the witness step, for all large `β`

Package 3 ("scaled propagation") of `notes/phase1/PHYSCUBIC.md` §4, targets T5 and T6.

`stepActivityBound_zeroClass_direct_at_tower` has the unscaled amplitude hypothesis, which cannot
hold for large `β` at the tower radius (`tower_lower_unbounded`).  With the potential term in
physical units (`StepActivityDirectScaled`) the amplitude is
`β_k · 3 c₁ M^d · energyConstScaled / r³ + (cK2' δ₁)/(β r)` with `β_k = 3β` and
`r ≍ √β / (log β)^p`, which is at most `C (log β)^{3p} / √β`, a quantity that tends to `0`.

* `tower_amp_le`: the elementary estimate.
* `stepActivityBound_zeroClass_direct_physical` (T5): at `hatStep m₁ β (pLog A₁ p β) δ`, with the
  logarithmic cutoff `p₁ = A₁ (log β)^p` and the radii `towerR`, `towerCpsi` fixed before `β`, for
  all `β ≥ β₀` there is a step activity bound of the zero class with the rate `2 κ_dec - 1` and
  prefactor at most `C (log β)^{3p}/√β`.  There is no amplitude or smallness hypothesis.
* `tendsto_physical_prefactor` (T6): `C (log β)^q/√β → 0` as `β → ∞`.

What is proved: for the zero class at the witness step (`d = L = 3`, `N = 2`, `k = 1`), the
label-activity bound with preserved rate holds for all large `β`, with the papers' logarithmic cutoff
and radii fixed before `β`.  What is not proved: other scales `k`, other classes, and the output
terms.
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation
  Balaban.Localization Balaban.Localization.LevelPair Balaban.Localization.I5Inhabited
  Balaban.Polymer Balaban.SmallField.Def6 Filter Topology

/-- **The elementary estimate of the tower.**  For `x = √β ≥ 1`, `w = (log β)^p ≥ 1`, and a radius
`r` with `κ₁ x ≤ 4 A w r`,
`3 x² (P / r³) + K / (x² r) ≤ (3 P (4A/κ₁)³ + 4 A K / κ₁) w³ / x`. -/
theorem tower_amp_le {x w r P K A κ₁ : ℝ} (hx : 1 ≤ x) (hw : 1 ≤ w) (hA : 0 < A) (hκ : 0 < κ₁)
    (hP : 0 ≤ P) (hK : 0 ≤ K) (hr : κ₁ * x ≤ 4 * A * w * r) :
    3 * x ^ 2 * (P / r ^ 3) + K / (x ^ 2 * r) ≤
      (3 * P * (4 * A / κ₁) ^ 3 + 4 * A * K / κ₁) * w ^ 3 / x := by
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
  have h1 : 3 * x ^ 2 * (P / r ^ 3) ≤ 3 * x ^ 2 * (P / ρ0 ^ 3) := by
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    exact div_le_div_of_nonneg_left hP (by positivity) (pow_le_pow_left₀ hρ0pos.le hrρ 3)
  have h2 : K / (x ^ 2 * r) ≤ K / (x ^ 2 * ρ0) :=
    div_le_div_of_nonneg_left hK (by positivity) (mul_le_mul_of_nonneg_left hrρ (by positivity))
  have e1 : 3 * x ^ 2 * (P / ρ0 ^ 3) = 3 * P * (4 * A / κ₁) ^ 3 * w ^ 3 / x := by
    rw [hρ0]; field_simp
  have e2 : K / (x ^ 2 * ρ0) = (4 * A * K / κ₁) * (w / x ^ 3) := by
    rw [hρ0]; field_simp
  have h3 : w / x ^ 3 ≤ w ^ 3 / x := by
    have a1 : w ≤ w ^ 3 := by nlinarith [mul_nonneg hw0.le hw0.le]
    have a2 : 1 / x ^ 3 ≤ 1 / x := one_div_le_one_div_of_le hx0 (by nlinarith [sq_nonneg x])
    calc w / x ^ 3 = w * (1 / x ^ 3) := by ring
      _ ≤ w ^ 3 * (1 / x) := mul_le_mul a1 a2 (by positivity) (by positivity)
      _ = w ^ 3 / x := by ring
  have h4 : K / (x ^ 2 * ρ0) ≤ (4 * A * K / κ₁) * (w ^ 3 / x) := by
    rw [e2]; exact mul_le_mul_of_nonneg_left h3 (by positivity)
  calc _ ≤ 3 * P * (4 * A / κ₁) ^ 3 * w ^ 3 / x + (4 * A * K / κ₁) * (w ^ 3 / x) := by
        rw [← e1]; exact add_le_add h1 (h2.trans h4)
    _ = _ := by ring

/-- **The amplitude at the tower is at most `C (log β)^{3p}/√β`.**  For `A₁ > 0` there are
`β₁ ≥ e` and `C > 0` (depending on `A₁, p, κ, t, P, K`) such that for `β ≥ β₁` the radius
`r = towerR κ t β (pLog A₁ p β)` satisfies
`3 β (P / r³) + K / (β r) ≤ C (log β)^{3p} / √β`, and `0 < r`. -/
theorem tower_amp_exists {A₁ κ t P K : ℝ} (hA : 0 < A₁) (p : ℕ) (ht : 0 < t) (hP : 0 ≤ P)
    (hK : 0 ≤ K) :
    ∃ β₁ C : ℝ, Real.exp 1 ≤ β₁ ∧ 0 < C ∧ ∀ β : ℝ, β₁ ≤ β →
      3 * β * (P / (towerR κ t β (pLog A₁ p β)) ^ 3) + K / (β * towerR κ t β (pLog A₁ p β)) ≤
        C * (Real.log β) ^ (3 * p) / Real.sqrt β := by
  have hκ₁ : 0 < t / (2 * Real.sqrt ((2 : ℕ) : ℝ) * (|towerC κ| + 1)) := by
    have := towerC_abs_pos κ
    positivity
  set κ₁ : ℝ := t / (2 * Real.sqrt ((2 : ℕ) : ℝ) * (|towerC κ| + 1)) with hκ₁def
  have hthr : 0 < κ₁ / 16 := by positivity
  refine ⟨max (Real.exp 1) (pLogThreshold A₁ p (κ₁ / 16)),
    3 * P * (4 * A₁ / κ₁) ^ 3 + 4 * A₁ * K / κ₁ + 1, le_max_left _ _, by positivity, ?_⟩
  intro β hβ
  have hexp : Real.exp 1 ≤ β := le_trans (le_max_left _ _) hβ
  have hβp : pLogThreshold A₁ p (κ₁ / 16) ≤ β := le_trans (le_max_right _ _) hβ
  have hβ1 : 1 ≤ β := le_trans (Real.one_le_exp (by norm_num)) hexp
  have hβ0 : 0 < β := by linarith
  have hℓ : 1 ≤ Real.log β := (Real.le_log_iff_exp_le hβ0).2 hexp
  have hx1 : 1 ≤ Real.sqrt β := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt hβ1
  have hw1 : 1 ≤ (Real.log β) ^ p := one_le_pow₀ hℓ
  have hpL : pLog A₁ p β = A₁ * (Real.log β) ^ p := rfl
  have hp16 : pLog A₁ p β ≤ κ₁ / 16 * Real.sqrt β := pLog_le_mul_sqrt hA.le p hthr hβ1 hβp
  have hcψeq : towerCpsi κ t β = κ₁ * Real.sqrt (3 * β) := towerCpsi_eq κ t β
  have hs3 : Real.sqrt β ≤ Real.sqrt (3 * β) := Real.sqrt_le_sqrt (by linarith)
  have hκs : κ₁ * Real.sqrt β ≤ towerCpsi κ t β := by
    rw [hcψeq]; exact mul_le_mul_of_nonneg_left hs3 hκ₁.le
  have hc16 : 16 * pLog A₁ p β ≤ towerCpsi κ t β := by nlinarith
  have hp0 : 0 < pLog A₁ p β := by
    rw [hpL]; exact mul_pos hA (by linarith)
  have hrbound : κ₁ * Real.sqrt β ≤ 4 * A₁ * (Real.log β) ^ p * towerR κ t β (pLog A₁ p β) := by
    have e : 4 * pLog A₁ p β * towerR κ t β (pLog A₁ p β) =
        2 * towerCpsi κ t β - 16 * pLog A₁ p β := by
      unfold towerR; field_simp; ring
    calc κ₁ * Real.sqrt β ≤ towerCpsi κ t β := hκs
      _ ≤ 2 * towerCpsi κ t β - 16 * pLog A₁ p β := by linarith
      _ = 4 * pLog A₁ p β * towerR κ t β (pLog A₁ p β) := e.symm
      _ = _ := by rw [hpL]; ring
  have hamp := tower_amp_le (x := Real.sqrt β) (w := (Real.log β) ^ p)
    (r := towerR κ t β (pLog A₁ p β)) (P := P) (K := K) (A := A₁) (κ₁ := κ₁) hx1 hw1 hA hκ₁ hP hK
    hrbound
  rw [Real.sq_sqrt hβ0.le, ← pow_mul, show p * 3 = 3 * p by ring] at hamp
  refine hamp.trans ?_
  have : 0 ≤ (Real.log β) ^ (3 * p) / Real.sqrt β := by positivity
  calc _ = (3 * P * (4 * A₁ / κ₁) ^ 3 + 4 * A₁ * K / κ₁) *
        ((Real.log β) ^ (3 * p) / Real.sqrt β) := by ring
    _ ≤ (3 * P * (4 * A₁ / κ₁) ^ 3 + 4 * A₁ * K / κ₁ + 1) *
        ((Real.log β) ^ (3 * p) / Real.sqrt β) :=
      mul_le_mul_of_nonneg_right (by linarith) this
    _ = _ := by ring

open Classical in
/-- **The zero-class activity bound at the witness step for all large `β` (T5).**  For `A₁ > 0` and
`p : ℕ` there are fixed data (`m₁`, `t = δ₁`, `δ`, `κ_dec`, `κ₀`; the background constants `BG`, `BG₂`, `κ` are chosen inside), constants
`β₀ ≥ 2` and `C > 0`, such that for every `β ≥ β₀`, at the step
`hatStep m₁ β (pLog A₁ p β) δ` (cutoff `p₁ = A₁ (log β)^p`, radii `towerR`, `towerCpsi`,
`R_σ = R₁ = 2`), the zero class has a step activity bound of rate `2 κ_dec - 1` and prefactor
at most `C (log β)^{3p} / √β`.  No amplitude or smallness hypothesis remains: the potential
amplitude is that of `stepActivityBound_zeroClass_direct_scaled_beta`. -/
theorem stepActivityBound_zeroClass_direct_physical {A₁ : ℝ} (hA : 0 < A₁) (p : ℕ) :
    ∃ (m₁ : ℕ) (t δ κdec κ0 β₀ C : ℝ), 2 ≤ β₀ ∧ 0 < C ∧ 0 < t ∧ 0 < δ ∧
      aEnt 3 3 + 1 ≤ κ0 ∧ 0 + 3 * κ0 + c1 3 3 + 3 / 2 ≤ 2 * κdec - 1 ∧
      ∀ β : ℝ, β₀ ≤ β →
        ∃ B : StepActivityBound (hatStep m₁ β (pLog A₁ p β) δ)
            (zeroClass 3 3 9 m₁ 1 2 (rhoSep m₁)) 0,
          B.κH = 2 * κdec - 1 ∧ B.εH ≤ C * (Real.log β) ^ (3 * p) / Real.sqrt β := by
  classical
  obtain ⟨-, δ, δ', T, -, -, hδ, hsm, hδ'0, hδ'a, hδ'b, hδ'c, hT, -, hT1, hT2⟩ :=
    exists_witness_params (fun _ => 0)
  obtain ⟨m₁, c, BG, κ, t, c₂, BG₂, κdec, κ0, δc, h4, ht0, ⟨hC⟩, hκ0, hκdec, hκ, h1, hlog, hc7,
    hMX, hdm, hα, hsmX, g1, g2, g3, g4, g5, hκE, hκa, hB0⟩ := tower_core_fixed 2
  have hκdec0 : 0 ≤ κdec := by linarith
  have hbig : cstarX 3 3 ≤ (3 : ℝ) ^ m₁ := by
    have hκ_nn : 0 ≤ κ := le_trans (by positivity) hκ
    have h := Localization.cstarX_pos 3 3
    have h2 : cstarX 3 3 ≤ cstarX 3 3 * Real.exp ((N0 3 3 : ℝ) * κ) :=
      le_mul_of_one_le_right h.le (Real.one_le_exp (by positivity))
    have h3 : ((3 : ℕ) : ℝ) ^ m₁ = (3 : ℝ) ^ m₁ := by norm_num
    linarith
  obtain ⟨β₀t, hβ₀t, hitems⟩ := tower_C_items hA p m₁ h4 hbig κ ht0 hδ hsm hδ'0 hδ'a hδ'b hδ'c
  set ECS : ℝ := energyConstScaled 3 3 2 (compWeight 3 (1 : ℝ)) 1
    (cK2' 3 3 2 (famConst 3 3 BG₂ κ) * t) t (rho4 3 3 2 BG κ) with hECS
  have hECS0 : 0 ≤ ECS := by
    have hd0 : 0 < 3 := by norm_num
    have hV : 0 ≤ cK2' 3 3 2 (famConst 3 3 BG₂ κ) * t :=
      mul_nonneg (cK2'_pos' hB0).le ht0.le
    have hρ : 0 ≤ rho4 3 3 2 BG κ := by
      have hBG := hC.hS.fam.2.1
      have hB1 : 0 ≤ famConst 3 3 BG κ := by
        have := famConst_ge_one (L := 3) hBG κ hd0; linarith
      unfold rho4
      exact (c6'_pos hB1 (by have := gamma1_pos hd0; positivity)).le
    have ha : 0 ≤ compWeight 3 (1 : ℝ) 1 :=
      (hC.HBp.weights 1 le_rfl (by norm_num)).1.trans' (by norm_num)
    have h := energyBdScaled_nonneg (d := 3) (L := 3) (N := 2) ha hV ht0.le hρ
    rw [energyBdScaled_eq (by norm_num) _ _ _ _ _ (by norm_num)] at h
    exact nonneg_of_mul_nonneg_right h (by positivity)
  set P : ℝ := 3 * c1 3 3 * (((3 : ℕ) : ℝ) ^ (1 + m₁)) ^ 3 * ECS with hPdef
  have hP0 : 0 ≤ P := by
    have := one_le_c1 3 3
    rw [hPdef]; positivity
  set K : ℝ := cK2' 3 3 2 (famConst 3 3 BG₂ κ) * t with hKdef
  have hK0' : 0 ≤ K := mul_nonneg (cK2'_pos' hB0).le ht0.le
  obtain ⟨β₁, C0, hexpβ₁, hC0, hA'⟩ := tower_amp_exists (A₁ := A₁) (κ := κ) (t := t) hA p ht0
    hP0 hK0'
  set Kc'' : ℝ := K0 3 3 κ0 + 1 with hKc''
  have hKc''pos : 0 < Kc'' := by have := K0_pos 3 3 κ0; rw [hKc'']; linarith
  refine ⟨m₁, t, δ, κdec, κ0,
    max (max β₀t β₁) (daThreshold C0 (daT 3 3 2 Kc'' κdec κ0 0) (3 * p)), 2 * C0,
    le_trans hβ₀t ((le_max_left _ _).trans (le_max_left _ _)), by positivity, ht0, hδ, hκE, hκa, ?_⟩
  intro β hβ
  have hβt : β₀t ≤ β := le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hβ)
  have hβ₁ : β₁ ≤ β := le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hβ)
  have hβd : daThreshold C0 (daT 3 3 2 Kc'' κdec κ0 0) (3 * p) ≤ β := le_trans (le_max_right _ _) hβ
  obtain ⟨hp, hcψ0, hr0, hδ₁, hc, hlt, ⟨R0⟩⟩ := hitems β hβt
  have hβ2 : 2 ≤ β := le_trans hβ₀t hβt
  have hβ0 : 0 < β := by linarith
  have hβ1 : 1 ≤ β := by linarith
  have hexp : Real.exp 1 ≤ β := le_trans hexpβ₁ hβ₁
  have hℓ : 1 ≤ Real.log β := (Real.le_log_iff_exp_le hβ0).2 hexp
  have hamp2 := hA' β hβ₁
  set εU : ℝ := C0 * (Real.log β) ^ (3 * p) / Real.sqrt β with hεU
  have hεpos : 0 < εU := by
    have : 0 < (Real.log β) ^ (3 * p) := by positivity
    rw [hεU]; positivity
  have hκa' : 0 + 3 * κ0 + c1 3 3 + 3 / 2 ≤ 2 * κdec - 1 := hκa
  set S := hatStep m₁ β (pLog A₁ p β) δ with hS
  have hxi1 : xiC1 3 * t ≤ 1 := by
    have h1 := hC.c7le
    have h2 := c7_le_bgC1 3 3 2 BG κ
    have h3 := bgC1_le_small 3 3 2 (by norm_num)
    linarith
  have hBh := hBh_of_xi (N := 2) (Gp := Gp m₁ (rhoSep m₁)) (bgHypNu m₁) nuW_pos hC.small1
    hC.eps_pos hxi1
  have hD : XiCData S.G' (compWeight 3 1) nuW (1 + 1) 1 t S.D' := by
    refine ⟨fun _ => unitVec hN2, unitVec hN2, 0, 0,
      exists_xiC (bgHypNu m₁) (Gp m₁ (rhoSep m₁)) hN2 (by unfold nuW; norm_num) ht0, ?_, ?_⟩
    · intro x hx i
      have := unitBg_Ψ_of_mem (Gp m₁ (rhoSep m₁)) hN2 (unitVec hN2) hx i
      show (unitBg (Gp m₁ (rhoSep m₁)) hN2 (unitVec hN2)).Ψ x i = _
      rw [this]; simp
    · intro x hx i
      have := unitBg_h_of_mem (Gp m₁ (rhoSep m₁)) hN2 (unitVec hN2) hx i
      show (unitBg (Gp m₁ (rhoSep m₁)) hN2 (unitVec hN2)).h x i = _
      rw [this]; simp
  have hK0 : 0 ≤ K0 3 3 κ0 := by
    unfold K0
    apply div_nonneg (Real.exp_pos _).le
    have : Real.exp (-1) < 1 := by simp
    linarith
  have hDA0 : 2 * εU ≤ 1 / (8 * (K0 3 3 κ0 + 1) ^ 3 * c1 3 3 *
          Real.exp ((2 * κdec - 1 - 2 * κ0) * cG 3 3 + c1 3 3 + 0 * cG 3 3)) :=
    (hDA_iff 3 3 (by norm_num) hKc''pos κdec κ0 0 εU).2 (amplitude_le hC0 (daT_pos 3 3 (by norm_num) hKc''pos κdec κ0 0) (3 * p) hβd)
  obtain ⟨B, hB1, hB2⟩ : ∃ B : StepActivityBound S (zeroClass 3 3 9 m₁ 1 2 (rhoSep m₁)) 0,
      B.κH = 2 * κdec - 1 ∧ B.εH = 2 * εU := by
    refine stepActivityBound_zeroClass_direct_scaled_beta S
      (ρ := pLog A₁ p β) (εU := εU) (κ0 := κ0) (κ' := 0) (Kc' := Kc'')
      (Rσ := 2) (R₁ := 2) (r := towerR κ t β (pLog A₁ p β)) (R := 2) (m₀ := 1) (κdec := κdec)
      (κ₀ := κ0) (ρE := 0)
      (ρM := 0) (Bh := 1 + 2 / nuW) (δc := δc) (cψ := towerCpsi κ t β)
      (jV := fun _ => 1) (XV := fun _ => Xr) (𝒦XV := fun _ => {0})
      (X₁V := fun _ => Finset.univ) (jF := fun _ => 1) (XF := fun _ => Xr)
      (𝒦XF := fun _ => {0}) (X₁F := fun _ => Finset.univ)
      (τι := PEmpty.{1}) (μι := PEmpty.{1}) (ϱ₁ := fun _ => 0) (ϱ₂ := fun _ => 0)
      (GkE := fun τ => PEmpty.elim τ) (GjE := fun τ => PEmpty.elim τ) (r₀ := 0) (δ₃ := 0)
      (δfl := 0) (X₀E := fun _ => ∅) (X₁E := fun _ => ∅) (jE := fun _ => 0) (XE := fun _ => ∅)
      (𝒦XE := fun _ => ∅) (EbE := fun _ => 0) (EE := fun _ _ => 0)
      (ϱ₁M := fun _ => 0) (ϱ₂M := fun _ => 0)
      (GkM := fun τ => PEmpty.elim τ) (GjM := fun τ => PEmpty.elim τ)
      (X₀M := fun _ => ∅) (X₁M := fun _ => ∅) (jM := fun _ => 0) (XM := fun _ => ∅)
      (𝒦XM := fun _ => ∅) (EbM := fun _ => 0) (EM := fun _ _ => 0)
      hC hatConn (rowInHat_level (dgSettingNu h4) isLevel_Hm isLevel_Gp) hκ0
      hκdec (by exact_mod_cast hκ) h1 (by norm_num) hr0 hβ1 le_rfl isLevel_Hm
      hcψ0.le hMX hdm hα hsmX hδ₁ one_pos (bgHypNu m₁) hc7 le_rfl g1 g2 g3 g4 g5
      (fun _ => covSetup)
      (fun _ => by rw [Finset.coe_univ]; exact X1_eq_univ.symm) (fun _ => hopt)
      (fun _ => treeLen_zero) (fun _ => hlog)
      (fun z _ _ => Finset.mem_coe.2 (Finset.mem_univ _))
      (fun z => blockMargin_univ fun x _ _ => mem_some_intBox h4 x)
      (∅ : Finset PEmpty.{1}) (fun τ hτ => absurd hτ (by simp)) (fun τ hτ => absurd hτ (by simp))
      (fun τ hτ => absurd hτ (by simp)) (fun τ hτ => absurd hτ (by simp))
      (fun τ hτ => absurd hτ (by simp)) (fun τ hτ => absurd hτ (by simp))
      (fun τ hτ => absurd hτ (by simp)) (fun τ hτ => absurd hτ (by simp))
      (fun τ hτ => absurd hτ (by simp))
      (fun _ => covSetup) (fun _ => by rw [Finset.coe_univ]; exact X1_eq_univ.symm) (fun _ => hopt)
      (fun _ => treeLen_zero) (fun _ => hlog) (fun s => Finset.mem_univ _)
      (∅ : Finset PEmpty.{1}) (fun τ => PEmpty.elim τ) (fun τ => PEmpty.elim τ)
      (fun τ hτ => absurd hτ (by simp)) (fun τ hτ => absurd hτ (by simp))
      (fun τ hτ => absurd hτ (by simp)) (fun τ hτ => absurd hτ (by simp))
      (fun τ hτ => absurd hτ (by simp)) (fun τ hτ => absurd hτ (by simp))
      (fun τ hτ => absurd hτ (by simp)) (fun τ hτ => absurd hτ (by simp))
      (fun τ hτ => absurd hτ (by simp)) (fun τ hτ => absurd hτ (by simp))
      (fun τ => PEmpty.elim τ) (fun τ hτ => absurd hτ (by simp)) le_rfl (fun x => by simp) le_rfl
      (fun p => by simp) (by unfold nuW; norm_num) hBh
      (fun z x _ => Finset.mem_coe.2 (Finset.mem_univ _)) (by norm_num) hc hD
      (by norm_num) hp le_rfl hεpos ?hεb hκE le_rfl le_rfl hκa' hDA0 R0 hlt
      (StepSetting.baseDomain_of_rayData R0) (by norm_num) rfl rfl


    case hεb =>
      have e1 : S.betaU = 3 * β := hatStep_betaU m₁ β (pLog A₁ p β) δ
      rw [e1]
      simp only [hPdef, hKdef, hECS] at hamp2
      simp only [norm_zero, zero_mul, add_zero, zero_div, mul_zero]
      exact hamp2
  refine ⟨B, hB1, ?_⟩
  rw [hB2, hεU]
  have : 2 * (C0 * (Real.log β) ^ (3 * p) / Real.sqrt β) = 2 * C0 * (Real.log β) ^ (3 * p) / Real.sqrt β := by ring
  rw [this]

/-- **The prefactor tends to zero (T6).**  For every `C` and `q`, `C (log β)^q / √β → 0` as
`β → ∞`: the bound of `stepActivityBound_zeroClass_direct_physical` is a small prefactor, in contrast
with `tower_lower_unbounded`, where the unscaled amplitude is forced to be at least `K p₁ √β`. -/
theorem tendsto_physical_prefactor (C : ℝ) (q : ℕ) :
    Tendsto (fun β : ℝ => C * (Real.log β) ^ q / Real.sqrt β) atTop (nhds 0) := by
  have h0 : Tendsto (fun β : ℝ => |C| * H q * β ^ (-(1 / 4 : ℝ))) atTop (nhds 0) := by
    simpa using (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 4)).const_mul (|C| * H q)
  refine squeeze_zero_norm' ?_ h0
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with β hβ
  have hβ0 : 0 < β := by linarith
  have hl : 0 ≤ Real.log β := Real.log_nonneg hβ
  have h := log_pow_div_sqrt_le (q := q) hβ
  rw [Real.norm_eq_abs, abs_div, abs_mul, abs_of_nonneg (pow_nonneg hl q),
    abs_of_nonneg (Real.sqrt_nonneg β), mul_div_assoc]
  calc |C| * ((Real.log β) ^ q / Real.sqrt β) ≤ |C| * (H q * β ^ (-(1 / 4 : ℝ))) :=
        mul_le_mul_of_nonneg_left h (abs_nonneg C)
    _ = _ := by ring

end Balaban.Inhabited
