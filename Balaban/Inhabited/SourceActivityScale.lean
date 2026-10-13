/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.SourceAmpScale
public import Balaban.Inhabited.SourceAmpRadius
public import Balaban.Fluctuation.SourceDirectTermsScale
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

/-!
# The zero-class activity bound at every scale and at every source of the strict `ℓ¹` ball

`stepActivityBound_zeroClass_direct_physical_scale` bounds the activity of the fluctuation step
`hatStepK k m₁ hk ν β p₁ δ` (`d = L = 3`, `N = 2`, constant unit block datum) for the zero class at
the source `g = 0`.  This file proves the bound at every source `g` of the strict `ℓ¹` ball
`l1Ball` (`∑_{y,i} |g(y,i)| < 1`, complex `g`), with the same order of quantifiers: the constants
`m₁`, `t = δ₁ = ε`, `δ`, `β₀`, `C_E`, `C_F` and the rates are fixed first; then the scale `k ≥ 1`,
the torus parameter `N₁` (`3 ∣ N₁`, `5 < N₁`), the mass `0 < ν`, `ν · 3^{2(k+1)} ≤ 1`, `β ≥ β₀`
and the source `g`.  Write `β_k = β · 3^k`, `κ₀ = a_Ent + 1`, `κ_dec = 100 (κ₀ + c₁ + 10)`,
`κ' = (3/2) κ_dec + κ₀ + 1`.

* `stepActivityBound_zeroClass_source_scale_cutoff`: for every cutoff `0 < p₁ ≤ A₁ (log β_k)^p`,
  every `q ≤ 1` and every source with `∑ |g| < q`: a `StepActivityBound` at the source `g` with
  `κ_H = 2 κ_dec - 1`, `K_c = 2 (K₀ + 1)` and
  `ε_H ≤ C_E (log β_k)^{3p}/√β_k + q C_F (log β_k)^p/√β_k`, and a `StepActivityBoundC` (the
  complex activity at the central real datum) with the same rate, prefactor and entropy constant.
* `stepActivityBound_zeroClass_source_scale` (R): the cutoff of the papers `p₁ = A₁ (log β_k)^p`
  and the whole ball (`q = 1`).
* `sourceActivityC_scale` (C): the same for `StepActivityBoundC`;
  `stepNonvanishingC_zeroClass_source_scale`: the complex partition functions do not vanish on the
  two segments.
* `stepActivityBound_zeroClass_source_scale_restricted`, `sourceActivityC_scale_restricted`: on the
  ball `∑ |g| < q ≤ 1` the source part of the prefactor has the factor `q`.
* `sourceActivityC_scale_instance`: the statement at `k = 1`, `N₁ = 6`, `ν = 1/81` and the nonzero
  source `g = ½ δ_{(0, 0)}`.

The constants.  With the tower data `κ`, `t`, `BG`, `BG₂`, `m₁` of `tower_core_rates`,
`Q = cK2' 3 3 2 (famConst 3 3 BG₂ κ)`, `ρ₄ = rho4 3 3 2 BG κ`, `κ₁ = lvKappa κ t`,
`P = 3 c₁ (3^{1+m₁})³ · 3³ · (2(1+Q)² + (4+ρ₄) Q²) t²` and `K = Q t`:
`C_E = 4 (P (4A₁/κ₁)³ + 1)` (`srcCE`), `C_F = 16 A₁ K/κ₁` (`srcCF`), and
`β₀ = max (max β₀' β₁) (daThreshold ((C_E + C_F)/4) (daT 3 3 4 (2(K₀+1)) κ_dec κ₀ κ') (3p))`, with
`β₀'` of `scale_C_items` and `β₁` of `sourceAmp_scale`.  None depends on `k`, `N₁`, `ν`, `β`, `g`,
`q`.

How it is proved.  The source `g/β` lies on the slice `η = q/β` of the assembler
(`sourceSlice_mem_restricted`); `sourceDirectTerms_slice` (at the step of a scale:
`sourceDirectTerms_scale`) gives the two `DirectTerms` instances at the sources `0` and `g/β` with
one family of labels and terms, and `stepActivityBound_zeroClass_source_scaled` the activity bound
with
`ε_H = 4 (β E_sc/r³ + q K/r)`.  The amplitude is bounded by `sourceAmp_scale` and the doubled
smallness holds by `sourceAmp_doubled_hDA`.  The other hypotheses are met as in
`ScaleActivityFinal` (covers by `LocalCover.levelLocalCover`, `FlCore` by `flCore_level_transfer`,
radii and `RayData` by `scale_C_items`).  The complex bound is the real one transported by
`stepActivityBoundC_of_activityBound` (the two exponents agree almost everywhere at real data).

What is proved: zero class; the central real datum `rawOf S.D'` only.  What is NOT proved: the
family of activities over the relative complex chart of data (leaves 5, 9, 10 of
`notes/phase1/SRCACT.md`) and the uniform chart (STEPOUT package 1); general classes; the output
terms.  The zero class has no terms, so nothing depends on a choice of generating sets for class
terms.
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation
  Balaban.Localization Balaban.Localization.LevelPair Balaban.Localization.I5Inhabited
  Balaban.Polymer Balaban.SmallField.Def6 Balaban.Inhabited.LevelStep Filter Topology

open Classical in
/-- **The zero-class activity bound at every scale, every cutoff up to the cutoff of the papers
and every source of a ball `∑ |g| < q ≤ ρ`: real and complex activity.**  As
`stepActivityBound_zeroClass_source_scale_cutoff`, for a source radius `ρ > 0`.  The constants
`m₁, t, δ, C_E, C_F` are fixed first and do not depend on `ρ`; then `ρ`; then the threshold
`β₀ ≥ max 2 ρ`, which depends on `ρ` through the amplitude threshold
`daThreshold ((C_E + ρ C_F)/4) …` of `sourceAmp_doubled_hDA_rho`.  The factor `q` stands in the
source part of the prefactor, as in the landed statement (the case `ρ = 1`). -/
theorem stepActivityBound_zeroClass_source_scale_cutoff_rho {A₁ : ℝ} (hA : 0 < A₁) (p : ℕ)
    {κ0 κdec κ' : ℝ} (hκ0def : κ0 = aEnt 3 3 + 1) (hκdecdef : κdec = 100 * (κ0 + c1 3 3 + 10))
    (hκ'def : κ' = 3 / 2 * κdec + κ0 + 1) :
    ∃ (m₁ : ℕ) (t δ CE CF : ℝ), 0 < CE ∧ 0 < CF ∧ 0 < t ∧ 0 < δ ∧
      ∀ ρ : ℝ, 0 < ρ → ∃ β₀ : ℝ, 2 ≤ β₀ ∧ ρ ≤ β₀ ∧
      ∀ (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁], 3 ∣ N₁ → 5 < N₁ →
      ∀ ν : ℝ, 0 < ν → ν * 3 ^ (2 * (k + 1)) ≤ 1 → ∀ β : ℝ, β₀ ≤ β →
      ∀ p₁ : ℝ, 0 < p₁ → p₁ ≤ pLog A₁ p (β * 3 ^ k) →
      ∀ q : ℝ, q ≤ ρ → ∀ g : Fld 3 3 N₁ m₁ (k + 1) 2, ∑ x, ∑ i, ‖g x i‖ < q →
        ∃ B : StepActivityBound (hatStepK (N₁ := N₁) k m₁ hk ν β p₁ δ)
            (zeroClass 3 3 N₁ m₁ k 2 (rhoSep m₁)) g,
          B.κH = 2 * κdec - 1 ∧ B.Kc = 2 * (K0 3 3 κ0 + 1) ∧
          B.εH ≤ CE * (Real.log (β * 3 ^ k)) ^ (3 * p) / Real.sqrt (β * 3 ^ k) +
            q * CF * (Real.log (β * 3 ^ k)) ^ p / Real.sqrt (β * 3 ^ k) ∧
          ∃ BC : StepActivityBoundC (hatStepK (N₁ := N₁) k m₁ hk ν β p₁ δ)
              (zeroClass 3 3 N₁ m₁ k 2 (rhoSep m₁)) g,
            BC.κH = B.κH ∧ BC.εH = B.εH ∧ BC.Kc = B.Kc := by
  classical
  obtain ⟨-, δ, δ', T, -, -, hδ, hsm, hδ'0, hδ'a, hδ'b, hδ'c, hT, -, hT1, hT2⟩ :=
    exists_witness_params (fun _ => 0)
  have hc1 := one_le_c1 3 3
  have hent := aEnt_nonneg 3 3
  obtain ⟨m₁, c, BG, κ, t, c₂, BG₂, δc, h4, ht0, ⟨hC₀⟩, hκ0, hκdec, hκ, h1, hlog, hc7,
    hMX, hdm, hα, hsmX, g1, g2, g3, g4, g5, hκE, hκa, hB0⟩ :=
    tower_core_rates 2 (κ0 := κ0) (κdec := κdec) (by rw [hκ0def]) (by rw [hκdecdef]; linarith)
  have hκdec0 : 0 ≤ κdec := by linarith
  have hbig : cstarX 3 3 ≤ (3 : ℝ) ^ m₁ := by
    have hκ_nn : 0 ≤ κ := le_trans (by positivity) hκ
    have h := Localization.cstarX_pos 3 3
    have h2 : cstarX 3 3 ≤ cstarX 3 3 * Real.exp ((N0 3 3 : ℝ) * κ) :=
      le_mul_of_one_le_right h.le (Real.one_le_exp (by positivity))
    have h3 : ((3 : ℕ) : ℝ) ^ m₁ = (3 : ℝ) ^ m₁ := by norm_num
    linarith
  obtain ⟨β₀t, hβ₀t, hitems⟩ := scale_C_items hA p m₁ h4 hbig κ ht0 hδ hsm hδ'0 hδ'a hδ'b hδ'c
  have hρ4 : 0 ≤ rho4 3 3 2 BG κ := by
    have hd0 : 0 < 3 := by norm_num
    have hBG := hC₀.hS.fam.2.1
    have hB1 : 0 ≤ famConst 3 3 BG κ := by
      have := famConst_ge_one (L := 3) hBG κ hd0; linarith
    unfold rho4
    exact (c6'_pos hB1 (by have := gamma1_pos hd0; positivity)).le
  obtain ⟨Q, hQdef⟩ : ∃ Q : ℝ, Q = cK2' 3 3 2 (famConst 3 3 BG₂ κ) := ⟨_, rfl⟩
  have hQ0 : 0 < Q := by rw [hQdef]; exact cK2'_pos' hB0
  obtain ⟨P, hPdef⟩ : ∃ P : ℝ, P = 3 * c1 3 3 * (((3 : ℕ) : ℝ) ^ (1 + m₁)) ^ 3 *
    (((3 : ℕ) : ℝ) ^ 3 * ((((2 : ℕ) : ℝ) / 2) * (2 * (1 + Q) ^ 2 +
      (((3 : ℕ) : ℝ) + 1 + rho4 3 3 2 BG κ) * Q ^ 2) * t ^ 2)) := ⟨_, rfl⟩
  have hP0 : 0 ≤ P := by
    rw [hPdef]; positivity
  have hK0 : 0 < Q * t := mul_pos hQ0 ht0
  obtain ⟨β₁, hexpβ₁, hA'⟩ := sourceAmp_scale (A₁ := A₁) (κ := κ) (t := t) hA p ht0
  obtain ⟨Kc'', hKc''⟩ : ∃ x : ℝ, x = K0 3 3 κ0 + 1 := ⟨_, rfl⟩
  have hKc''pos : 0 < Kc'' := by have := K0_pos 3 3 κ0; rw [hKc'']; linarith
  have hκ'0 : 0 ≤ κ' := by rw [hκ'def]; linarith
  have hκa' : κ' + 3 * κ0 + c1 3 3 + 3 / 2 ≤ 2 * κdec - 1 := by
    rw [hκ'def, hκdecdef]; linarith
  have hxi1 : xiC1 3 * t ≤ 1 := by
    have h1 := hC₀.c7le
    have h2 := c7_le_bgC1 3 3 2 BG κ
    have h3 := bgC1_le_small 3 3 2 (by norm_num)
    linarith
  refine ⟨m₁, t, δ, srcCE A₁ κ t P, srcCF A₁ κ t (Q * t), srcCE_pos hA ht0 hP0,
    srcCF_pos hA ht0 hK0, ht0, hδ, ?_⟩
  intro ρ hρ
  refine ⟨max (max (max β₀t β₁) (daThreshold ((srcCE A₁ κ t P + ρ * srcCF A₁ κ t (Q * t)) / 4)
      (daT 3 3 4 (2 * Kc'') κdec κ0 κ') (3 * p))) ρ,
    le_trans hβ₀t (((le_max_left _ _).trans (le_max_left _ _)).trans (le_max_left _ _)),
    le_max_right _ _, ?_⟩
  intro k hk N₁ _ h3N hN ν hνpos hν β hβ p₁ hp0 hp₁ q hq g hg
  obtain ⟨⟨⟨hβt, hβ₁⟩, hβd⟩, hβρ⟩ : ((β₀t ≤ β ∧ β₁ ≤ β) ∧ daThreshold
      ((srcCE A₁ κ t P + ρ * srcCF A₁ κ t (Q * t)) / 4) (daT 3 3 4 (2 * Kc'') κdec κ0 κ')
        (3 * p) ≤ β) ∧ ρ ≤ β := by simpa only [max_le_iff] using hβ
  have hν0 : 0 ≤ ν := hνpos.le
  have hβ2 : 2 ≤ β := le_trans hβ₀t hβt
  have hβ0 : 0 < β := by linarith
  have hβ1 : 1 ≤ β := by linarith
  have h3k : (1 : ℝ) ≤ 3 ^ k := one_le_pow₀ (by norm_num)
  have hbβ : β ≤ β * 3 ^ k := le_mul_of_one_le_right hβ0.le h3k
  have hb0 : 0 < β * 3 ^ k := by positivity
  obtain ⟨hcψ0, hr0, hδ₁, hc, hlt, ⟨R0⟩⟩ := hitems k hk N₁ hN ν hν0 hν β hβt p₁ hp0 hp₁
  have hexp : Real.exp 1 ≤ β * 3 ^ k := le_trans hexpβ₁ (hβ₁.trans hbβ)
  have hℓ : 1 ≤ Real.log (β * 3 ^ k) := (Real.le_log_iff_exp_le hb0).2 hexp
  have hq0 : 0 < q := lt_of_le_of_lt
    (Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun i _ => norm_nonneg _) hg
  have hamp := (hA' (β * 3 ^ k) (hβ₁.trans hbβ) p₁ hp0 hp₁).2 P (Q * t) q hP0 hK0.le hq0.le
  have hSD := dgSetting_lv (N₁ := N₁) (k := k) h4 hN hν0 hν
  have hHB := bgHyp_lv (k := k) m₁ hν0 hν
  have hC : FlCore 2 (lvTop N₁ m₁ k (rhoSep m₁)) (lvLow N₁ m₁ k (rhoSep m₁)) 1 ν c BG κ t
      (levelKc 3 3) (Cchi 3 3) c₂ BG₂ t :=
    flCore_level_transfer hC₀ hSD (opSetting_lv h4 hN hν0 hν) (isLevel_lvLow hk) isLevel_lvTop hHB
  have hBh := hBh_of_xi (N := 2) (Gp := lvTop N₁ m₁ k (rhoSep m₁)) hHB hνpos hC.small1
    hC.eps_pos hxi1
  have hD : XiCData (hatStepK (N₁ := N₁) k m₁ hk ν β p₁ δ).G' (compWeight 3 1) ν (k + 1) 1 t
      (hatStepK (N₁ := N₁) k m₁ hk ν β p₁ δ).D' := by
    refine ⟨fun _ => unitVec hN2, unitVec hN2, 0, 0,
      exists_xiC hHB (lvTop N₁ m₁ k (rhoSep m₁)) hN2 (massLe_lv hν) ht0, ?_, ?_⟩
    · intro x hx i
      have := unitBg_Ψ_of_mem (lvTop N₁ m₁ k (rhoSep m₁)) hN2 (unitVec hN2) hx i
      show (unitBg (lvTop N₁ m₁ k (rhoSep m₁)) hN2 (unitVec hN2)).Ψ x i = _
      rw [this]; simp
    · intro x hx i
      have := unitBg_h_of_mem (lvTop N₁ m₁ k (rhoSep m₁)) hN2 (unitVec hN2) hx i
      show (unitBg (lvTop N₁ m₁ k (rhoSep m₁)) hN2 (unitVec hN2)).h x i = _
      rw [this]; simp
  have hN3 : 3 ^ 1 ∣ N₁ := by simpa using h3N
  obtain ⟨hV, hF⟩ := LocalCover.levelLocalCover (N := 2) (lvLow N₁ m₁ k (rhoSep m₁)) hSD
    (isLevel_lvTop (N₁ := N₁) (m₁ := m₁) (k := k) (ϱ := rhoSep m₁)) (m₀ := 1) le_rfl hN3
  have hBh0 : (0 : ℝ) ≤ 1 + 2 / ν := by positivity
  -- the physical amplitude on the slice `η = q/β`
  obtain ⟨εU, hεU⟩ : ∃ εU : ℝ, εU = β * prop33EpsEtaScaled 3 3 2 m₁ k 1 1 BG BG₂ κ t
      (lvR κ t (β * 3 ^ k) p₁) 0 0 (q / β) := ⟨_, rfl⟩
  have hid := sourceEta_scaled_identity 3 3 2 m₁ k 1 1 BG BG₂ κ t (lvR κ t (β * 3 ^ k) p₁) q β
    hβ0.ne'
  rw [← hεU, ← hQdef] at hid
  have hmem := compWeight_three_mem hk
  have hpot : β * (3 * c1 3 3 * (((3 : ℕ) : ℝ) ^ (1 + m₁)) ^ 3 *
      ‖energyBdScaled 3 3 2 (compWeight 3 1) k (Q * t) t (rho4 3 3 2 BG κ)‖ /
        lvR κ t (β * 3 ^ k) p₁ ^ 3) ≤ β * 3 ^ k * (P / lvR κ t (β * 3 ^ k) p₁ ^ 3) := by
    have h := beta_mul_potentialAmp_le (N := 2) (hatStepK (N₁ := N₁) k m₁ hk ν β p₁ δ)
      (by norm_num) le_rfl hmem.2 (le_trans (by norm_num) hmem.1) hβ0.le hQ0.le ht0.le hρ4 hr0
      (1 + m₁)
    rw [hatStepK_betaU, ← hPdef] at h
    exact h
  have hterm0 : 0 ≤ β * (3 * c1 3 3 * (((3 : ℕ) : ℝ) ^ (1 + m₁)) ^ 3 *
      ‖energyBdScaled 3 3 2 (compWeight 3 1) k (Q * t) t (rho4 3 3 2 BG κ)‖ /
        lvR κ t (β * 3 ^ k) p₁ ^ 3) := by
    have h3 : (0 : ℝ) ≤ 3 * c1 3 3 := by linarith
    positivity
  have hεle : εU ≤ P * (4 * A₁ / lvKappa κ t) ^ 3 * (Real.log (β * 3 ^ k)) ^ (3 * p) /
        Real.sqrt (β * 3 ^ k) +
      q * (4 * A₁ * (Q * t) / lvKappa κ t) * (Real.log (β * 3 ^ k)) ^ p /
        Real.sqrt (β * 3 ^ k) := by
    rw [hid]
    linarith
  have hεpos : 0 < εU := by
    rw [hid]
    have : 0 < q * (Q * t) / lvR κ t (β * 3 ^ k) p₁ := div_pos (mul_pos hq0 hK0) hr0
    linarith
  have hDA0 := sourceAmp_doubled_hDA_rho 3 3 (A₁ := A₁) (κ := κ) (t := t) (P := P) (K := Q * t)
    (q := q) (ρ := ρ)
    (b := β * 3 ^ k) (ε := εU) (Kc' := Kc'') p hA ht0 hP0 hK0.le hρ.le hq hℓ hb0 hKc''pos κdec κ0 κ'
    (hβd.trans hbβ) hεle
  obtain ⟨B, hB1, hB2, hB3⟩ := stepActivityBound_zeroClass_source_scaled_rho
    (hatStepK (N₁ := N₁) k m₁ hk ν β p₁ δ)
    (ρ := p₁) (εU := εU) (κ0 := κ0) (κ' := κ') (Kc' := Kc'')
    (R₁ := 2) (r := lvR κ t (β * 3 ^ k) p₁) (R := 2) (m₀ := 1) (κdec := κdec)
    (κ₀ := κ0) (Bh := 1 + 2 / ν) (δc := δc) (cψ := lvCpsi κ t (β * 3 ^ k))
    (jV := fun _ => k) (XV := fun z => LocalCover.cube 1 k (LocalCover.blockSite k z))
    (𝒦XV := fun z => LocalCover.fam 1 (LocalCover.blockSite k z))
    (X₁V := fun z => LocalCover.nbhdF 1 (LocalCover.blockSite k z))
    (jF := fun _ => k) (XF := fun s => LocalCover.cube 1 k s.1)
    (𝒦XF := fun s => LocalCover.fam 1 s.1) (X₁F := fun s => LocalCover.nbhdF 1 s.1)
    (hC := hC) (hconn := hatConn_lvTop) (hrow := rowInHat_lv hk h4 hN hν0 hν)
    (hκ₀ := hκ0) (hκdec := hκdec) (hκ := by exact_mod_cast hκ) (h1 := h1)
    (hR₁ := by norm_num) (hr := hr0) (hcψ := hcψ0.le) (hMX := hMX) (hdm := hdm) (hα := hα)
    (hsmX := hsmX) (hδ₁ := hδ₁) (ha₁ := one_pos) (H := hHB) (hc7 := hc7) (hR := le_rfl)
    (hRs := g1) (hsmall := g2) (hnum := g3) (hnum' := g4) (hsm := g5)
    (hcovV := fun z => (hV z).1) (hX₁V := fun z => (hV z).2.1)
    (hoptV := fun z => (hV z).2.2.1) (hΔV := fun z => (hV z).2.2.2.1)
    (hlogV := fun _ => hlog) (hZV := fun z => (hV z).2.2.2.2.1)
    (hmarV := fun z => (hV z).2.2.2.2.2.1)
    (hcovF := fun s => (hF s).1) (hX₁F := fun s => (hF s).2.1)
    (hoptF := fun s => (hF s).2.2.1) (hΔF := fun s => (hF s).2.2.2.1)
    (hlogF := fun _ => hlog) (hyF := fun s => (hF s).2.2.2.2)
    (hBh0 := hBh0) (hBh := hBh) (hZν := fun z => (hV z).2.2.2.2.2.2)
    (hN := hN3) (hp := hp0) (hD := hD) (hpρ := le_rfl) (hεpos := hεpos) (hκE := hκE)
    (hKc := hKc''.ge) (hκ' := hκ'0) (hκa := hκa') (hDA := hDA0) (R0 := R0) (hlt := hlt)
    (g := g) (q := q) (hg := hg) (ρs := ρ) (hq := hq) (hβ := max_le hβ1 hβρ) (hc := hc) (hεU := hεU)
  have hBε : B.εH = 4 * εU := by
    rw [hB3, hid, hQdef]
    rfl
  obtain ⟨BC, hBCκ, hBCε, hBCK, -⟩ := stepActivityBoundC_of_activityBound R0 hp0 hlt B
  refine ⟨B, hB1, by rw [hB2, hKc''], ?_, BC, hBCκ, hBCε, hBCK⟩
  rw [hBε]
  exact sourceAmp_scale_four p hb0 (by linarith) hεle

open Classical in
/-- **The zero-class activity bound at every scale, every cutoff up to the cutoff of the papers
and every source of a ball `∑ |g| < q ≤ 1`: real and complex activity.**  With `κ₀ = a_Ent + 1`,
`κ_dec = 100 (κ₀ + c₁ + 10)`, `κ' = (3/2) κ_dec + κ₀ + 1`: there are `m₁, t, δ, β₀, C_E, C_F`
(`β₀ ≥ 2`, `C_E, C_F > 0`) such that for every scale `k ≥ 1`, every torus parameter `N₁` with
`3 ∣ N₁`, `5 < N₁`, every mass `0 < ν` with `ν · 3^{2(k+1)} ≤ 1`, every `β ≥ β₀`, every cutoff
`0 < p₁ ≤ A₁ (log β_k)^p` (`β_k = β · 3^k`), every `q ≤ 1` and every complex source `g` with
`∑_{y,i} |g(y,i)| < q`, the zero class at `hatStepK k m₁ hk ν β p₁ δ` has a step activity bound at
the source `g` with `κ_H = 2 κ_dec - 1`, `K_c = 2 (K₀(κ₀) + 1)` and prefactor
`ε_H ≤ C_E (log β_k)^{3p}/√β_k + q C_F (log β_k)^p/√β_k`, and a complex step activity bound at the
central real datum with the same rate, prefactor and entropy constant.  The constants do not
depend on `k`, `N₁`, `ν`, `β`, `p₁`, `q`, `g`. -/
theorem stepActivityBound_zeroClass_source_scale_cutoff {A₁ : ℝ} (hA : 0 < A₁) (p : ℕ)
    {κ0 κdec κ' : ℝ} (hκ0def : κ0 = aEnt 3 3 + 1) (hκdecdef : κdec = 100 * (κ0 + c1 3 3 + 10))
    (hκ'def : κ' = 3 / 2 * κdec + κ0 + 1) :
    ∃ (m₁ : ℕ) (t δ β₀ CE CF : ℝ), 2 ≤ β₀ ∧ 0 < CE ∧ 0 < CF ∧ 0 < t ∧ 0 < δ ∧
      ∀ (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁], 3 ∣ N₁ → 5 < N₁ →
      ∀ ν : ℝ, 0 < ν → ν * 3 ^ (2 * (k + 1)) ≤ 1 → ∀ β : ℝ, β₀ ≤ β →
      ∀ p₁ : ℝ, 0 < p₁ → p₁ ≤ pLog A₁ p (β * 3 ^ k) →
      ∀ q : ℝ, q ≤ 1 → ∀ g : Fld 3 3 N₁ m₁ (k + 1) 2, ∑ x, ∑ i, ‖g x i‖ < q →
        ∃ B : StepActivityBound (hatStepK (N₁ := N₁) k m₁ hk ν β p₁ δ)
            (zeroClass 3 3 N₁ m₁ k 2 (rhoSep m₁)) g,
          B.κH = 2 * κdec - 1 ∧ B.Kc = 2 * (K0 3 3 κ0 + 1) ∧
          B.εH ≤ CE * (Real.log (β * 3 ^ k)) ^ (3 * p) / Real.sqrt (β * 3 ^ k) +
            q * CF * (Real.log (β * 3 ^ k)) ^ p / Real.sqrt (β * 3 ^ k) ∧
          ∃ BC : StepActivityBoundC (hatStepK (N₁ := N₁) k m₁ hk ν β p₁ δ)
              (zeroClass 3 3 N₁ m₁ k 2 (rhoSep m₁)) g,
            BC.κH = B.κH ∧ BC.εH = B.εH ∧ BC.Kc = B.Kc := by
  obtain ⟨m₁, t, δ, CE, CF, hCE, hCF, ht, hδ, H⟩ :=
    stepActivityBound_zeroClass_source_scale_cutoff_rho hA p hκ0def hκdecdef hκ'def
  obtain ⟨β₀, hβ₀, -, h⟩ := H 1 one_pos
  exact ⟨m₁, t, δ, β₀, CE, CF, hβ₀, hCE, hCF, ht, hδ, h⟩

/-- **(R) The zero-class activity bound at every scale and every source of the strict `ℓ¹` ball,
with the cutoff of the papers.**  With `κ₀ = a_Ent + 1`, `κ_dec = 100 (κ₀ + c₁ + 10)`,
`κ' = (3/2) κ_dec + κ₀ + 1`: there are `m₁, t, δ, β₀, C_E, C_F` (`β₀ ≥ 2`, `C_E, C_F > 0`) such
that for every scale `k ≥ 1`, every torus parameter `N₁` with `3 ∣ N₁`, `5 < N₁`, every mass
`0 < ν` with `ν · 3^{2(k+1)} ≤ 1`, every `β ≥ β₀` and every complex source `g` with
`∑_{y,i} |g(y,i)| < 1` (`l1Ball`), at the step `hatStepK k m₁ hk ν β p₁ δ` with the cutoff
`p₁ = A₁ (log β_k)^p`, `β_k = β · 3^k`, the zero class has a step activity bound at the source
`g` with `κ_H = 2 κ_dec - 1` and prefactor at most
`C_E (log β_k)^{3p}/√β_k + C_F (log β_k)^p/√β_k`; the rate relation
`κ' + 3κ₀ + c₁ + 3/2 ≤ 2 κ_dec - 1` holds, and the output rate `κ_out = (3/2) κ_dec` satisfies
`κ_dec ≤ κ_out ≤ min κ' κ' - κ₀ - 1`.  The constants and the rates do not depend on `k`, `N₁`,
`ν`, `β`, `g`. -/
theorem stepActivityBound_zeroClass_source_scale {A₁ : ℝ} (hA : 0 < A₁) (p : ℕ)
    {κ0 κdec κ' : ℝ} (hκ0def : κ0 = aEnt 3 3 + 1) (hκdecdef : κdec = 100 * (κ0 + c1 3 3 + 10))
    (hκ'def : κ' = 3 / 2 * κdec + κ0 + 1) :
    ∃ (m₁ : ℕ) (t δ β₀ CE CF : ℝ), 2 ≤ β₀ ∧ 0 < CE ∧ 0 < CF ∧ 0 < t ∧ 0 < δ ∧
      ∀ (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁], 3 ∣ N₁ → 5 < N₁ →
      ∀ ν : ℝ, 0 < ν → ν * 3 ^ (2 * (k + 1)) ≤ 1 → ∀ β : ℝ, β₀ ≤ β →
      ∀ g : Fld 3 3 N₁ m₁ (k + 1) 2, g ∈ l1Ball 3 3 N₁ m₁ (k + 1) 2 →
        ∃ B : StepActivityBound (hatStepK (N₁ := N₁) k m₁ hk ν β (pLog A₁ p (β * 3 ^ k)) δ)
            (zeroClass 3 3 N₁ m₁ k 2 (rhoSep m₁)) g,
          B.κH = 2 * κdec - 1 ∧
          B.εH ≤ CE * (Real.log (β * 3 ^ k)) ^ (3 * p) / Real.sqrt (β * 3 ^ k) +
            CF * (Real.log (β * 3 ^ k)) ^ p / Real.sqrt (β * 3 ^ k) ∧
          κ' + 3 * κ0 + c1 3 3 + 3 / 2 ≤ 2 * κdec - 1 ∧
          ∃ κout : ℝ, κout = 3 / 2 * κdec ∧ κdec ≤ κout ∧ κout ≤ min κ' κ' - κ0 - 1 := by
  obtain ⟨m₁, t, δ, β₀, CE, CF, hβ₀, hCE, hCF, ht, hδ, h⟩ :=
    stepActivityBound_zeroClass_source_scale_cutoff hA p hκ0def hκdecdef hκ'def
  have hc1 := one_le_c1 3 3
  have hent := aEnt_nonneg 3 3
  refine ⟨m₁, t, δ, β₀, CE, CF, hβ₀, hCE, hCF, ht, hδ, ?_⟩
  intro k hk N₁ _ h3 hN ν hν0 hν β hβ g hg
  have h3k : (1 : ℝ) ≤ 3 ^ k := one_le_pow₀ (by norm_num)
  have hβ2 : 2 ≤ β := hβ₀.trans hβ
  have hb : 1 < β * 3 ^ k :=
    lt_of_lt_of_le (by linarith) (le_mul_of_one_le_right (by linarith) h3k)
  obtain ⟨B, hB1, -, hB3, -⟩ := h k hk N₁ h3 hN ν hν0 hν β hβ _ (pLog_pos hA p hb) le_rfl 1
    le_rfl g hg
  refine ⟨B, hB1, ?_, by rw [hκ'def, hκdecdef]; linarith, 3 / 2 * κdec, rfl,
    by rw [hκdecdef]; linarith, by rw [hκ'def, min_self]; linarith⟩
  rwa [one_mul] at hB3

/-- **(C) The complex zero-class activity bound at every scale and every source of the strict
`ℓ¹` ball, at the central real datum** (the endpoint `sourceActivityC_scale` of
`notes/phase1/SRCACT.md`).  The statement of `stepActivityBound_zeroClass_source_scale` for
`StepActivityBoundC`: the complex exponents `WoneC + WtwoC` of the step at the real datum of
`hatStepK`, for every complex source `g` with `∑ |g| < 1`, are a sum of label activities with
`κ_H = 2 κ_dec - 1` and prefactor at most `C_E (log β_k)^{3p}/√β_k + C_F (log β_k)^p/√β_k`.  The
family over the relative complex chart of data is not part of this statement. -/
theorem sourceActivityC_scale {A₁ : ℝ} (hA : 0 < A₁) (p : ℕ)
    {κ0 κdec κ' : ℝ} (hκ0def : κ0 = aEnt 3 3 + 1) (hκdecdef : κdec = 100 * (κ0 + c1 3 3 + 10))
    (hκ'def : κ' = 3 / 2 * κdec + κ0 + 1) :
    ∃ (m₁ : ℕ) (t δ β₀ CE CF : ℝ), 2 ≤ β₀ ∧ 0 < CE ∧ 0 < CF ∧ 0 < t ∧ 0 < δ ∧
      ∀ (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁], 3 ∣ N₁ → 5 < N₁ →
      ∀ ν : ℝ, 0 < ν → ν * 3 ^ (2 * (k + 1)) ≤ 1 → ∀ β : ℝ, β₀ ≤ β →
      ∀ g : Fld 3 3 N₁ m₁ (k + 1) 2, g ∈ l1Ball 3 3 N₁ m₁ (k + 1) 2 →
        ∃ B : StepActivityBoundC (hatStepK (N₁ := N₁) k m₁ hk ν β (pLog A₁ p (β * 3 ^ k)) δ)
            (zeroClass 3 3 N₁ m₁ k 2 (rhoSep m₁)) g,
          B.κH = 2 * κdec - 1 ∧
          B.εH ≤ CE * (Real.log (β * 3 ^ k)) ^ (3 * p) / Real.sqrt (β * 3 ^ k) +
            CF * (Real.log (β * 3 ^ k)) ^ p / Real.sqrt (β * 3 ^ k) ∧
          κ' + 3 * κ0 + c1 3 3 + 3 / 2 ≤ 2 * κdec - 1 ∧
          ∃ κout : ℝ, κout = 3 / 2 * κdec ∧ κdec ≤ κout ∧ κout ≤ min κ' κ' - κ0 - 1 := by
  obtain ⟨m₁, t, δ, β₀, CE, CF, hβ₀, hCE, hCF, ht, hδ, h⟩ :=
    stepActivityBound_zeroClass_source_scale_cutoff hA p hκ0def hκdecdef hκ'def
  have hc1 := one_le_c1 3 3
  have hent := aEnt_nonneg 3 3
  refine ⟨m₁, t, δ, β₀, CE, CF, hβ₀, hCE, hCF, ht, hδ, ?_⟩
  intro k hk N₁ _ h3 hN ν hν0 hν β hβ g hg
  have h3k : (1 : ℝ) ≤ 3 ^ k := one_le_pow₀ (by norm_num)
  have hβ2 : 2 ≤ β := hβ₀.trans hβ
  have hb : 1 < β * 3 ^ k :=
    lt_of_lt_of_le (by linarith) (le_mul_of_one_le_right (by linarith) h3k)
  obtain ⟨B, hB1, -, hB3, BC, hC1, hC2, -⟩ := h k hk N₁ h3 hN ν hν0 hν β hβ _
    (pLog_pos hA p hb) le_rfl 1 le_rfl g hg
  refine ⟨BC, hC1.trans hB1, ?_, by rw [hκ'def, hκdecdef]; linarith, 3 / 2 * κdec, rfl,
    by rw [hκdecdef]; linarith, by rw [hκ'def, min_self]; linarith⟩
  rw [hC2]
  rwa [one_mul] at hB3

/-- **Nonvanishing of the complex partition functions at every scale and every source of the
strict `ℓ¹` ball.**  There are `m₁, t, δ, β₀` such that for every scale `k ≥ 1`, torus parameter
`3 ∣ N₁ > 5`, mass `0 < ν`, `ν · 3^{2(k+1)} ≤ 1`, `β ≥ β₀` and complex source `g` with
`∑ |g| < 1`, the complex partition functions `Z^C_{s,0}`, `Z^C_{1,t}` (`s, t ∈ [0,1]`) of the zero
class at `hatStepK k m₁ hk ν β (A₁ (log β_k)^p) δ` do not vanish (`StepNonvanishingC`). -/
theorem stepNonvanishingC_zeroClass_source_scale {A₁ : ℝ} (hA : 0 < A₁) (p : ℕ) :
    ∃ (m₁ : ℕ) (t δ β₀ : ℝ), 2 ≤ β₀ ∧ 0 < t ∧ 0 < δ ∧
      ∀ (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁], 3 ∣ N₁ → 5 < N₁ →
      ∀ ν : ℝ, 0 < ν → ν * 3 ^ (2 * (k + 1)) ≤ 1 → ∀ β : ℝ, β₀ ≤ β →
      ∀ g : Fld 3 3 N₁ m₁ (k + 1) 2, g ∈ l1Ball 3 3 N₁ m₁ (k + 1) 2 →
        (hatStepK (N₁ := N₁) k m₁ hk ν β (pLog A₁ p (β * 3 ^ k)) δ).StepNonvanishingC
          (zeroClass 3 3 N₁ m₁ k 2 (rhoSep m₁)) g := by
  obtain ⟨m₁, t, δ, β₀, CE, CF, hβ₀, -, -, ht, hδ, h⟩ :=
    sourceActivityC_scale hA p (κ0 := aEnt 3 3 + 1) rfl rfl rfl
  refine ⟨m₁, t, δ, β₀, hβ₀, ht, hδ, ?_⟩
  intro k hk N₁ _ h3 hN ν hν0 hν β hβ g hg
  obtain ⟨B, -⟩ := h k hk N₁ h3 hN ν hν0 hν β hβ g hg
  exact stepNonvanishingC_of_activityBoundC B

/-- **The restricted ball (real activity).**  The statement of
`stepActivityBound_zeroClass_source_scale` on the ball `∑ |g| < q`, `q ≤ 1`: the source part of
the prefactor has the factor `q`,
`ε_H ≤ C_E (log β_k)^{3p}/√β_k + q C_F (log β_k)^p/√β_k`.  The constants do not depend on `q`. -/
theorem stepActivityBound_zeroClass_source_scale_restricted {A₁ : ℝ} (hA : 0 < A₁) (p : ℕ)
    {κ0 κdec κ' : ℝ} (hκ0def : κ0 = aEnt 3 3 + 1) (hκdecdef : κdec = 100 * (κ0 + c1 3 3 + 10))
    (hκ'def : κ' = 3 / 2 * κdec + κ0 + 1) :
    ∃ (m₁ : ℕ) (t δ β₀ CE CF : ℝ), 2 ≤ β₀ ∧ 0 < CE ∧ 0 < CF ∧ 0 < t ∧ 0 < δ ∧
      ∀ (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁], 3 ∣ N₁ → 5 < N₁ →
      ∀ ν : ℝ, 0 < ν → ν * 3 ^ (2 * (k + 1)) ≤ 1 → ∀ β : ℝ, β₀ ≤ β →
      ∀ q : ℝ, q ≤ 1 → ∀ g : Fld 3 3 N₁ m₁ (k + 1) 2, ∑ x, ∑ i, ‖g x i‖ < q →
        ∃ B : StepActivityBound (hatStepK (N₁ := N₁) k m₁ hk ν β (pLog A₁ p (β * 3 ^ k)) δ)
            (zeroClass 3 3 N₁ m₁ k 2 (rhoSep m₁)) g,
          B.κH = 2 * κdec - 1 ∧
          B.εH ≤ CE * (Real.log (β * 3 ^ k)) ^ (3 * p) / Real.sqrt (β * 3 ^ k) +
            q * CF * (Real.log (β * 3 ^ k)) ^ p / Real.sqrt (β * 3 ^ k) := by
  obtain ⟨m₁, t, δ, β₀, CE, CF, hβ₀, hCE, hCF, ht, hδ, h⟩ :=
    stepActivityBound_zeroClass_source_scale_cutoff hA p hκ0def hκdecdef hκ'def
  refine ⟨m₁, t, δ, β₀, CE, CF, hβ₀, hCE, hCF, ht, hδ, ?_⟩
  intro k hk N₁ _ h3 hN ν hν0 hν β hβ q hq g hg
  have h3k : (1 : ℝ) ≤ 3 ^ k := one_le_pow₀ (by norm_num)
  have hβ2 : 2 ≤ β := hβ₀.trans hβ
  have hb : 1 < β * 3 ^ k :=
    lt_of_lt_of_le (by linarith) (le_mul_of_one_le_right (by linarith) h3k)
  obtain ⟨B, hB1, -, hB3, -⟩ := h k hk N₁ h3 hN ν hν0 hν β hβ _ (pLog_pos hA p hb) le_rfl q
    hq g hg
  exact ⟨B, hB1, hB3⟩

/-- **The restricted ball (complex activity at the central real datum).**  The statement of
`sourceActivityC_scale` on the ball `∑ |g| < q`, `q ≤ 1`, with
`ε_H ≤ C_E (log β_k)^{3p}/√β_k + q C_F (log β_k)^p/√β_k`. -/
theorem sourceActivityC_scale_restricted {A₁ : ℝ} (hA : 0 < A₁) (p : ℕ)
    {κ0 κdec κ' : ℝ} (hκ0def : κ0 = aEnt 3 3 + 1) (hκdecdef : κdec = 100 * (κ0 + c1 3 3 + 10))
    (hκ'def : κ' = 3 / 2 * κdec + κ0 + 1) :
    ∃ (m₁ : ℕ) (t δ β₀ CE CF : ℝ), 2 ≤ β₀ ∧ 0 < CE ∧ 0 < CF ∧ 0 < t ∧ 0 < δ ∧
      ∀ (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁], 3 ∣ N₁ → 5 < N₁ →
      ∀ ν : ℝ, 0 < ν → ν * 3 ^ (2 * (k + 1)) ≤ 1 → ∀ β : ℝ, β₀ ≤ β →
      ∀ q : ℝ, q ≤ 1 → ∀ g : Fld 3 3 N₁ m₁ (k + 1) 2, ∑ x, ∑ i, ‖g x i‖ < q →
        ∃ B : StepActivityBoundC (hatStepK (N₁ := N₁) k m₁ hk ν β (pLog A₁ p (β * 3 ^ k)) δ)
            (zeroClass 3 3 N₁ m₁ k 2 (rhoSep m₁)) g,
          B.κH = 2 * κdec - 1 ∧
          B.εH ≤ CE * (Real.log (β * 3 ^ k)) ^ (3 * p) / Real.sqrt (β * 3 ^ k) +
            q * CF * (Real.log (β * 3 ^ k)) ^ p / Real.sqrt (β * 3 ^ k) := by
  obtain ⟨m₁, t, δ, β₀, CE, CF, hβ₀, hCE, hCF, ht, hδ, h⟩ :=
    stepActivityBound_zeroClass_source_scale_cutoff hA p hκ0def hκdecdef hκ'def
  refine ⟨m₁, t, δ, β₀, CE, CF, hβ₀, hCE, hCF, ht, hδ, ?_⟩
  intro k hk N₁ _ h3 hN ν hν0 hν β hβ q hq g hg
  have h3k : (1 : ℝ) ≤ 3 ^ k := one_le_pow₀ (by norm_num)
  have hβ2 : 2 ≤ β := hβ₀.trans hβ
  have hb : 1 < β * 3 ^ k :=
    lt_of_lt_of_le (by linarith) (le_mul_of_one_le_right (by linarith) h3k)
  obtain ⟨B, hB1, -, hB3, BC, hC1, hC2, -⟩ := h k hk N₁ h3 hN ν hν0 hν β hβ _
    (pLog_pos hA p hb) le_rfl q hq g hg
  exact ⟨BC, hC1.trans hB1, by rw [hC2]; exact hB3⟩

/-- The `ℓ¹` size of a source supported at one site and one component. -/
theorem l1_single_eq {X : Type*} [Fintype X] [DecidableEq X] {N : ℕ} (x₀ : X) (i₀ : Fin N)
    (c : ℂ) :
    ∑ x, ∑ i, ‖(Pi.single x₀ (Pi.single i₀ c) : X → Fin N → ℂ) x i‖ = ‖c‖ := by
  rw [Finset.sum_eq_single x₀ (fun x _ hx => by simp [Pi.single_eq_of_ne hx])
    (fun h => absurd (Finset.mem_univ _) h)]
  rw [Finset.sum_eq_single i₀ (fun i _ hi => by simp [Pi.single_eq_of_ne hi])
    (fun h => absurd (Finset.mem_univ _) h)]
  simp

/-- **An explicit instance with a nonzero source.**  At the scale `k = 1`, on the torus with
`N₁ = 6`, at the mass `ν = 1/81`, for the source `g = ½ δ_{(0,0)}` (value `1/2` at the site `0`
and the component `0`, zero elsewhere): `g ≠ 0`, `g` lies in the strict `ℓ¹` ball, and for all
`β ≥ β₀` the zero class at `hatStepK 1 m₁ _ (1/81) β (A₁ (log 3β)^p) δ` has a complex step activity
bound at the source `g` with `κ_H = 2 κ_dec - 1` and prefactor at most
`C_E (log 3β)^{3p}/√(3β) + C_F (log 3β)^p/√(3β)`. -/
theorem sourceActivityC_scale_instance {A₁ : ℝ} (hA : 0 < A₁) (p : ℕ)
    {κ0 κdec κ' : ℝ} (hκ0def : κ0 = aEnt 3 3 + 1) (hκdecdef : κdec = 100 * (κ0 + c1 3 3 + 10))
    (hκ'def : κ' = 3 / 2 * κdec + κ0 + 1) :
    ∃ (m₁ : ℕ) (t δ β₀ CE CF : ℝ), 2 ≤ β₀ ∧ 0 < CE ∧ 0 < CF ∧ 0 < t ∧ 0 < δ ∧
      (Pi.single 0 (Pi.single 0 (1 / 2)) : Fld 3 3 6 m₁ (1 + 1) 2) ≠ 0 ∧
      (Pi.single 0 (Pi.single 0 (1 / 2)) : Fld 3 3 6 m₁ (1 + 1) 2) ∈ l1Ball 3 3 6 m₁ (1 + 1) 2 ∧
      ∀ β : ℝ, β₀ ≤ β →
        ∃ B : StepActivityBoundC (hatStepK (N₁ := 6) 1 m₁ le_rfl nuW β (pLog A₁ p (β * 3 ^ 1)) δ)
            (zeroClass 3 3 6 m₁ 1 2 (rhoSep m₁)) (Pi.single 0 (Pi.single 0 (1 / 2))),
          B.κH = 2 * κdec - 1 ∧
          B.εH ≤ CE * (Real.log (β * 3 ^ 1)) ^ (3 * p) / Real.sqrt (β * 3 ^ 1) +
            CF * (Real.log (β * 3 ^ 1)) ^ p / Real.sqrt (β * 3 ^ 1) := by
  obtain ⟨m₁, t, δ, β₀, CE, CF, hβ₀, hCE, hCF, ht, hδ, h⟩ :=
    sourceActivityC_scale hA p hκ0def hκdecdef hκ'def
  have hmem : (Pi.single 0 (Pi.single 0 (1 / 2)) : Fld 3 3 6 m₁ (1 + 1) 2) ∈
      l1Ball 3 3 6 m₁ (1 + 1) 2 := by
    show ∑ x, ∑ i, ‖(Pi.single 0 (Pi.single 0 (1 / 2)) : Fld 3 3 6 m₁ (1 + 1) 2) x i‖ < 1
    rw [l1_single_eq]
    norm_num
  refine ⟨m₁, t, δ, β₀, CE, CF, hβ₀, hCE, hCF, ht, hδ, ?_, hmem, ?_⟩
  · intro h0
    have := congrFun (congrFun h0 0) 0
    simp at this
  · intro β hβ
    obtain ⟨B, hB1, hB2, -⟩ := h 1 le_rfl 6 (by norm_num) (by norm_num) nuW nuW_pos
      (by unfold nuW; norm_num) β hβ _ hmem
    exact ⟨B, hB1, hB2⟩

end Balaban.Inhabited
