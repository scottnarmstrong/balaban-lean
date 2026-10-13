/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module
public import Balaban.Inhabited.LevelPairGeneral
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
/-!
# The variants of the numerical core for general `d`, `L`, `N`
`tower_core_rates_two_general_of_pair` proves, for every `d ≥ 3`, `L ≥ 3`, `N` and a family of level
pairs, the twenty-one clauses of `tower_core_rates_general_of_pair` and `κmin ≤ κ` together with
the three margins of the landed variants: `2 K₄ ξ₁ t < δ_*′(B, γ₁/8)` (`ren`), `K₁ ξ₁ t < δ_*`
(`renSol`) and the step core, the domain margin and the coercivity margin at the radius `2 t`
(`two`).  The proof is the proof of `tower_core_rates_general_of_pair` with `t` taken in further
neighbourhoods of `0⁺`.  The numeral `40000` of the landed variants is replaced by `2 + 4 A`,
`A = (2L+1)^d L^d` (so that `log A ≤ A - 1 ≤ (κ/2 - 1)/2`).  The variants `…_renSol_general`,
`…_ren_general` follow from it, with and without the pair hypothesis; `ren` is the first variant
that is used downstream.
-/
@[expose] public section
namespace Balaban.Inhabited
open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation
  Balaban.Localization Balaban.Localization.LevelPair Balaban.Localization.I5Inhabited
  Balaban.Polymer Balaban.SmallField.Def6 Filter Topology
open LevelStep

/-- **Two-radius core rates at general `(d, L, N)`**, given a family of level pairs: the core
rates of `tower_core_rates_general_of_pair` with the margins `2 K₄ ξ₁ t < δ_*′(B, γ₁/8)` at
`B = famConst BG κ` and `K₁ ξ₁ t < δ_*`, and the step core, the domain margin and the coercivity
margin at the radius `2 t`. -/
theorem tower_core_rates_two_general_of_pair
    {d L : ℕ} [NeZero L] (N : ℕ) (hd : 3 ≤ d) (hL : 3 ≤ L)
    {N₁ K : ℕ} [NeZero N₁] {ϱ ϱm : ℕ → ℝ} {a₁ ν : ℝ}
    (Gp : ∀ m₁ : ℕ, GeneratingSet d L (N₁ * L ^ m₁) K (ϱ m₁))
    (Hm : ∀ m₁ : ℕ, GeneratingSet d L (N₁ * L ^ m₁) K (ϱm m₁))
    (hpair : ∀ m₁ : ℕ, 4 ≤ m₁ → ∃ n : ℕ,
      Nonempty (Localization.DGSetting (Gp m₁) (compWeight L a₁) ν) ∧
      Nonempty (Localization.Dec2.OpSetting (Hm m₁) (compWeight L a₁) ν) ∧
      IsLevel (Hm m₁) n ∧ IsLevel (Gp m₁) (n + 1) ∧
      BgHyp d L K (ϱ m₁) (compWeight L a₁) ν)
    {κ0 κdec : ℝ} (κmin : ℝ) (hκ0 : aEnt d L + 1 ≤ κ0)
    (hκdec : 3 * κ0 + c1 d L + 5 ≤ κdec) :
    ∃ (m₁ : ℕ) (c BG κ t c₂ BG₂ δc : ℝ),
      4 ≤ m₁ ∧ 0 < t ∧
      Nonempty (FlCore N (Gp m₁) (Hm m₁) a₁ ν c BG κ t (levelKc d L)
        (Cchi d L) c₂ BG₂ t) ∧
      0 ≤ κ0 ∧ 3 * κ0 + 3 ≤ κdec ∧
      4 * ((d : ℕ) : ℝ) * (((2 * L + 1) ^ d : ℕ) : ℝ) * κdec ≤ κ ∧ 1 ≤ (κ / 2 - 1) / 2 ∧
      Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) * (((L ^ 1) ^ d : ℕ) : ℝ)) ≤ (κ / 2 - 1) / 2 ∧
      c7 d L N BG κ ≤ thm73C3 d L N ∧
      cstarX d L * Real.exp (N0 d L * κ) ≤ ((L : ℕ) : ℝ) ^ m₁ ∧
      decDomMargin d L N BG κ (xiC1 d * t) < δc ∧
      K4 d L N BG κ * (xiC1 d * t) < coerciveConst d / 2 ∧
      δc ^ 2 * smallConstX d L κ ≤ 1 / 4 ∧
      2 * t ≤ deltaStar d L N ∧ cK2 d L N * (2 * t) < bgC0 d L N / 2 ∧
      cK2 d L N * t ≤ c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8) ∧
      cK2' d L N (famConst d L BG₂ κ) * t ≤ c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8) ∧
      2 * (compC4 d * (bgK1 d L N * (xiC1 d * t))) + 5 * (2 * t) ≤ bgC1 d L N ∧
      aEnt d L + 1 ≤ κ0 ∧
      0 + 3 * κ0 + c1 d L + 3 / 2 ≤ 2 * κdec - 1 ∧ 0 ≤ famConst d L BG₂ κ ∧ κmin ≤ κ ∧
      2 * (K4 d L N BG κ * (xiC1 d * t)) <
        deltaStar' d L N (famConst d L BG κ) (gamma1 d / 8) ∧
      bgK1 d L N * (xiC1 d * t) < deltaStar d L N ∧
      Nonempty (FlCore N (Gp m₁) (Hm m₁) a₁ ν c BG κ (2 * t)
        (levelKc d L) (Cchi d L) c₂ BG₂ (2 * t)) ∧
      decDomMargin d L N BG κ (xiC1 d * (2 * t)) < δc ∧
      K4 d L N BG κ * (xiC1 d * (2 * t)) < coerciveConst d / 2 := by
  have hd0 : 0 < d := by omega
  obtain ⟨c, BG0, hS0⟩ := decSpecs_exists (d := d) (L := L) hd hL
  set BG := max BG0 1 with hBGdef
  have hS : DecSpecs d L c BG := hS0.mono_BG (le_max_left _ _)
  have hBG1 : 1 ≤ BG := le_max_right _ _
  obtain ⟨c₂, BG₂, hS2⟩ := Dec2.decSpecs_exists (d := d) (L := L) (Kc := levelKc d L)
    (Cx := Cchi d L) hd hL (levelKc_nonneg d L) (Cchi_nonneg d L)
  have hT3 := thm73C3_pos (d := d) (L := L) (N := N) hd0
  have hc1 := one_le_c1 d L
  have hent := aEnt_nonneg d L
  have hκ00 : 0 ≤ κ0 := by linarith
  have hκdec0 : 0 ≤ κdec := by linarith
  set A : ℝ := (((2 * L + 1) ^ d : ℕ) : ℝ) * (((L ^ 1) ^ d : ℕ) : ℝ) with hAdef
  have hA1 : 1 ≤ A := by
    have h1 : (1 : ℝ) ≤ (((2 * L + 1) ^ d : ℕ) : ℝ) := by
      exact_mod_cast Nat.one_le_pow _ _ (by omega)
    have h2 : (1 : ℝ) ≤ (((L ^ 1) ^ d : ℕ) : ℝ) := by
      exact_mod_cast Nat.one_le_pow _ _ (by simp; omega)
    rw [hAdef]; nlinarith
  set κ0' : ℝ := 4 * ((d : ℕ) : ℝ) * (((2 * L + 1) ^ d : ℕ) : ℝ) * κdec + 2 + 4 * A +
    1 / thm73C3 d L N with hκ0'def
  set κ : ℝ := max κ0' κmin with hκdef
  have hinv : 0 ≤ 1 / thm73C3 d L N := by positivity
  have hcoef : (0 : ℝ) ≤ 4 * ((d : ℕ) : ℝ) * (((2 * L + 1) ^ d : ℕ) : ℝ) := by positivity
  have hcd := mul_nonneg hcoef hκdec0
  have hκ1 : 4 * ((d : ℕ) : ℝ) * (((2 * L + 1) ^ d : ℕ) : ℝ) * κdec ≤ κ :=
    le_trans (by rw [hκ0'def]; linarith) (le_max_left _ _)
  have hκ2 : 1 / thm73C3 d L N ≤ κ :=
    le_trans (by rw [hκ0'def]; linarith) (le_max_left _ _)
  have hκ3 : 2 + 4 * A ≤ κ :=
    le_trans (by rw [hκ0'def]; linarith) (le_max_left _ _)
  have hLr : (1 : ℝ) < (L : ℝ) := by exact_mod_cast (by omega : 1 < L)
  obtain ⟨m₀, hm₀⟩ := pow_unbounded_of_one_lt (max (max (c * Real.exp ((N0 d L : ℝ) * κ))
    (c₂ * Real.exp ((N0 d L : ℝ) * κ))) (cstarX d L * Real.exp ((N0 d L : ℝ) * κ))) hLr
  set m₁ : ℕ := max m₀ 4 with hm₁def
  have h4 : 4 ≤ m₁ := le_max_right _ _
  have hm : max (max (c * Real.exp ((N0 d L : ℝ) * κ))
    (c₂ * Real.exp ((N0 d L : ℝ) * κ))) (cstarX d L * Real.exp ((N0 d L : ℝ) * κ))
      ≤ (L : ℝ) ^ m₁ :=
    hm₀.le.trans (pow_le_pow_right₀ hLr.le (le_max_left _ _))
  have hm1 : c * Real.exp ((N0 d L : ℝ) * κ) ≤ ((L : ℕ) : ℝ) ^ m₁ :=
    (le_max_left _ _).trans ((le_max_left _ _).trans hm)
  have hm2 : c₂ * Real.exp ((N0 d L : ℝ) * κ) ≤ ((L : ℕ) : ℝ) ^ m₁ :=
    (le_max_right _ _).trans ((le_max_left _ _).trans hm)
  have hm3 : cstarX d L * Real.exp ((N0 d L : ℝ) * κ) ≤ ((L : ℕ) : ℝ) ^ m₁ :=
    (le_max_right _ _).trans hm
  obtain ⟨n, ⟨S⟩, ⟨SH⟩, hG, hG', HBp⟩ := hpair m₁ h4
  have hev := flCore_level_eventually (N := N) S SH hG hG' HBp
    hS (κ := κ) (by have := hent; have : 0 ≤ A := by linarith
                    linarith) hm1 hS2 hm2
  have hB0 : 0 ≤ famConst d L BG₂ κ := by
    have := famConst_ge_one (L := L) hS2.fam.2.1 κ hd0; linarith
  have hc6 : 0 < c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8) :=
    c6'_pos hB0 (by have := gamma1_pos hd0; positivity)
  have hDs : 0 < deltaStar d L N := deltaStar_pos (d := d) (L := L) (N := N) hd0
  have hC0 : 0 < bgC0 d L N := bgC0_pos d L N hd0
  have hC1 : 0 < bgC1 d L N := bgC1_pos' (d := d) (L := L) (N := N) hd0
  have hSX := smallConstX_pos d L κ
  set SX := smallConstX d L κ with hSXdef
  set δc : ℝ := 1 / (2 * (SX + 1)) with hδcdef
  have hδc0 : 0 < δc := by positivity
  have hδc1 : δc * (2 * (SX + 1)) = 1 := by rw [hδcdef]; field_simp
  have hδcSX : δc ^ 2 * SX ≤ 1 / 4 := by
    have h1 : δc * SX ≤ 1 / 2 := by nlinarith
    have h2 : δc ≤ 1 / 2 := by nlinarith
    nlinarith
  have hK4 : 0 < K4 d L N BG κ := K4_pos (by linarith) hd0
  have hcoer : 0 < coerciveConst d := coerciveConst_pos hd0
  have wk : ∀ {p : ℝ → Prop}, (∀ᶠ t in 𝓝 (0 : ℝ), p t) → ∀ᶠ t in 𝓝[>] (0 : ℝ), p t :=
    fun h => eventually_nhdsWithin_of_eventually_nhds h
  have e1 := ev_lt (f := fun t : ℝ => 2 * t) (by fun_prop) (c := deltaStar d L N) (by simpa using hDs)
  have e2 := ev_lt (f := fun t : ℝ => cK2 d L N * (2 * t)) (by fun_prop) (c := bgC0 d L N / 2)
    (by simp; positivity)
  have e3 := ev_lt (f := fun t : ℝ => cK2 d L N * t) (by fun_prop)
    (c := c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) (by simpa using hc6)
  have e4 := ev_lt (f := fun t : ℝ => cK2' d L N (famConst d L BG₂ κ) * t) (by fun_prop)
    (c := c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) (by simpa using hc6)
  have e5 := ev_lt (f := fun t : ℝ => 2 * (compC4 d * (bgK1 d L N * (xiC1 d * t))) + 5 * (2 * t))
    (by fun_prop) (c := bgC1 d L N) (by simpa using hC1)
  have e6 := ev_lt (f := fun t : ℝ => decDomMargin d L N BG κ (xiC1 d * t))
    (by unfold decDomMargin; fun_prop) (c := δc) (by simp [decDomMargin]; exact hδc0)
  have e7 := ev_lt (f := fun t : ℝ => K4 d L N BG κ * (xiC1 d * t)) (by fun_prop)
    (c := coerciveConst d / 2) (by simp; positivity)
  have hB1 : 0 ≤ famConst d L BG κ := by
    have := famConst_ge_one (L := L) hS.fam.2.1 κ hd0; linarith
  have hDs' : 0 < deltaStar' d L N (famConst d L BG κ) (gamma1 d / 8) :=
    deltaStar'_pos hB1 (by have := gamma1_pos (d := d) hd0; positivity)
  have e8 := ev_lt (f := fun t : ℝ => 2 * (K4 d L N BG κ * (xiC1 d * t))) (by fun_prop)
    (c := deltaStar' d L N (famConst d L BG κ) (gamma1 d / 8)) (by simpa using hDs')
  have e9 := ev_lt (f := fun t : ℝ => bgK1 d L N * (xiC1 d * t)) (by fun_prop)
    (c := deltaStar d L N) (by simpa using hDs)
  have e6' := ev_lt (f := fun t : ℝ => decDomMargin d L N BG κ (xiC1 d * (2 * t)))
    (by unfold decDomMargin; fun_prop) (c := δc) (by simp [decDomMargin]; exact hδc0)
  have e7' := ev_lt (f := fun t : ℝ => K4 d L N BG κ * (xiC1 d * (2 * t))) (by fun_prop)
    (c := coerciveConst d / 2) (by simp; positivity)
  have hT : Tendsto (fun t : ℝ => 2 * t) (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have : Tendsto (fun t : ℝ => 2 * t) (𝓝 0) (𝓝 (2 * 0)) :=
        (continuous_const.mul continuous_id).tendsto 0
      rw [mul_zero] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with t ht
      simp only [Set.mem_Ioi] at ht ⊢
      positivity
  have hev2 := hT.eventually hev
  have hpos : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < t := self_mem_nhdsWithin
  obtain ⟨t, hC, g1, g2, g3, g4, g5, g6, g7, g8, g9, hC2, g6', g7', ht0⟩ := (hev.and ((wk e1).and ((wk e2).and
    ((wk e3).and ((wk e4).and ((wk e5).and ((wk e6).and ((wk e7).and ((wk e8).and ((wk e9).and (hev2.and ((wk e6').and ((wk e7').and hpos))))))))))))).exists
  have hlogA : Real.log A ≤ A - 1 := Real.log_le_sub_one_of_pos (by linarith)
  have hlogκ : Real.log A ≤ (κ / 2 - 1) / 2 := by linarith
  have hκdec3 : 3 * κ0 + 3 ≤ κdec := by linarith
  refine ⟨m₁, c, BG, κ, t, c₂, BG₂, δc, h4, ht0, hC, hκ00, hκdec3, hκ1, by linarith, hlogκ,
    c7_le_thm73C3_of_large hd0 hBG1 hκ2, hm3, g6, g7,
    hδcSX, g1.le, g2, g3.le, g4.le, g5.le, hκ0, by linarith, hB0, le_max_right _ _, g8, g9, hC2, g6', g7'⟩



/-- The `renSol` variant: `tower_core_rates_two_general_of_pair` without the three conjuncts at the radius `2 t`. -/
theorem tower_core_rates_renSol_general_of_pair
    {d L : ℕ} [NeZero L] (N : ℕ) (hd : 3 ≤ d) (hL : 3 ≤ L)
    {N₁ K : ℕ} [NeZero N₁] {ϱ ϱm : ℕ → ℝ} {a₁ ν : ℝ}
    (Gp : ∀ m₁ : ℕ, GeneratingSet d L (N₁ * L ^ m₁) K (ϱ m₁))
    (Hm : ∀ m₁ : ℕ, GeneratingSet d L (N₁ * L ^ m₁) K (ϱm m₁))
    (hpair : ∀ m₁ : ℕ, 4 ≤ m₁ → ∃ n : ℕ,
      Nonempty (Localization.DGSetting (Gp m₁) (compWeight L a₁) ν) ∧
      Nonempty (Localization.Dec2.OpSetting (Hm m₁) (compWeight L a₁) ν) ∧
      IsLevel (Hm m₁) n ∧ IsLevel (Gp m₁) (n + 1) ∧
      BgHyp d L K (ϱ m₁) (compWeight L a₁) ν)
    {κ0 κdec : ℝ} (κmin : ℝ) (hκ0 : aEnt d L + 1 ≤ κ0)
    (hκdec : 3 * κ0 + c1 d L + 5 ≤ κdec) :
    ∃ (m₁ : ℕ) (c BG κ t c₂ BG₂ δc : ℝ),
      4 ≤ m₁ ∧ 0 < t ∧
      Nonempty (FlCore N (Gp m₁) (Hm m₁) a₁ ν c BG κ t (levelKc d L)
        (Cchi d L) c₂ BG₂ t) ∧
      0 ≤ κ0 ∧ 3 * κ0 + 3 ≤ κdec ∧
      4 * ((d : ℕ) : ℝ) * (((2 * L + 1) ^ d : ℕ) : ℝ) * κdec ≤ κ ∧ 1 ≤ (κ / 2 - 1) / 2 ∧
      Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) * (((L ^ 1) ^ d : ℕ) : ℝ)) ≤ (κ / 2 - 1) / 2 ∧
      c7 d L N BG κ ≤ thm73C3 d L N ∧
      cstarX d L * Real.exp (N0 d L * κ) ≤ ((L : ℕ) : ℝ) ^ m₁ ∧
      decDomMargin d L N BG κ (xiC1 d * t) < δc ∧
      K4 d L N BG κ * (xiC1 d * t) < coerciveConst d / 2 ∧
      δc ^ 2 * smallConstX d L κ ≤ 1 / 4 ∧
      2 * t ≤ deltaStar d L N ∧ cK2 d L N * (2 * t) < bgC0 d L N / 2 ∧
      cK2 d L N * t ≤ c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8) ∧
      cK2' d L N (famConst d L BG₂ κ) * t ≤ c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8) ∧
      2 * (compC4 d * (bgK1 d L N * (xiC1 d * t))) + 5 * (2 * t) ≤ bgC1 d L N ∧
      aEnt d L + 1 ≤ κ0 ∧
      0 + 3 * κ0 + c1 d L + 3 / 2 ≤ 2 * κdec - 1 ∧ 0 ≤ famConst d L BG₂ κ ∧ κmin ≤ κ ∧
      2 * (K4 d L N BG κ * (xiC1 d * t)) <
        deltaStar' d L N (famConst d L BG κ) (gamma1 d / 8) ∧
      bgK1 d L N * (xiC1 d * t) < deltaStar d L N :=
  by
  obtain ⟨m₁, c, BG, κ, t, c₂, BG₂, δc, h4, ht, hC, h1, h2, h3, h4', h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, -, -, -⟩ :=
    tower_core_rates_two_general_of_pair N hd hL Gp Hm hpair κmin hκ0 hκdec
  exact ⟨m₁, c, BG, κ, t, c₂, BG₂, δc, h4, ht, hC, h1, h2, h3, h4', h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21⟩

/-- The `ren` variant: `tower_core_rates_renSol_general_of_pair` without the margin `K₁ ξ₁ t < δ_*`. -/
theorem tower_core_rates_ren_general_of_pair
    {d L : ℕ} [NeZero L] (N : ℕ) (hd : 3 ≤ d) (hL : 3 ≤ L)
    {N₁ K : ℕ} [NeZero N₁] {ϱ ϱm : ℕ → ℝ} {a₁ ν : ℝ}
    (Gp : ∀ m₁ : ℕ, GeneratingSet d L (N₁ * L ^ m₁) K (ϱ m₁))
    (Hm : ∀ m₁ : ℕ, GeneratingSet d L (N₁ * L ^ m₁) K (ϱm m₁))
    (hpair : ∀ m₁ : ℕ, 4 ≤ m₁ → ∃ n : ℕ,
      Nonempty (Localization.DGSetting (Gp m₁) (compWeight L a₁) ν) ∧
      Nonempty (Localization.Dec2.OpSetting (Hm m₁) (compWeight L a₁) ν) ∧
      IsLevel (Hm m₁) n ∧ IsLevel (Gp m₁) (n + 1) ∧
      BgHyp d L K (ϱ m₁) (compWeight L a₁) ν)
    {κ0 κdec : ℝ} (κmin : ℝ) (hκ0 : aEnt d L + 1 ≤ κ0)
    (hκdec : 3 * κ0 + c1 d L + 5 ≤ κdec) :
    ∃ (m₁ : ℕ) (c BG κ t c₂ BG₂ δc : ℝ),
      4 ≤ m₁ ∧ 0 < t ∧
      Nonempty (FlCore N (Gp m₁) (Hm m₁) a₁ ν c BG κ t (levelKc d L)
        (Cchi d L) c₂ BG₂ t) ∧
      0 ≤ κ0 ∧ 3 * κ0 + 3 ≤ κdec ∧
      4 * ((d : ℕ) : ℝ) * (((2 * L + 1) ^ d : ℕ) : ℝ) * κdec ≤ κ ∧ 1 ≤ (κ / 2 - 1) / 2 ∧
      Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) * (((L ^ 1) ^ d : ℕ) : ℝ)) ≤ (κ / 2 - 1) / 2 ∧
      c7 d L N BG κ ≤ thm73C3 d L N ∧
      cstarX d L * Real.exp (N0 d L * κ) ≤ ((L : ℕ) : ℝ) ^ m₁ ∧
      decDomMargin d L N BG κ (xiC1 d * t) < δc ∧
      K4 d L N BG κ * (xiC1 d * t) < coerciveConst d / 2 ∧
      δc ^ 2 * smallConstX d L κ ≤ 1 / 4 ∧
      2 * t ≤ deltaStar d L N ∧ cK2 d L N * (2 * t) < bgC0 d L N / 2 ∧
      cK2 d L N * t ≤ c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8) ∧
      cK2' d L N (famConst d L BG₂ κ) * t ≤ c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8) ∧
      2 * (compC4 d * (bgK1 d L N * (xiC1 d * t))) + 5 * (2 * t) ≤ bgC1 d L N ∧
      aEnt d L + 1 ≤ κ0 ∧
      0 + 3 * κ0 + c1 d L + 3 / 2 ≤ 2 * κdec - 1 ∧ 0 ≤ famConst d L BG₂ κ ∧ κmin ≤ κ ∧
      2 * (K4 d L N BG κ * (xiC1 d * t)) <
        deltaStar' d L N (famConst d L BG κ) (gamma1 d / 8) :=
  by
  obtain ⟨m₁, c, BG, κ, t, c₂, BG₂, δc, h4, ht, hC, h1, h2, h3, h4', h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, -⟩ :=
    tower_core_rates_renSol_general_of_pair N hd hL Gp Hm hpair κmin hκ0 hκdec
  exact ⟨m₁, c, BG, κ, t, c₂, BG₂, δc, h4, ht, hC, h1, h2, h3, h4', h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩

/-- **Two-radius core rates at general `(d, L, N)`**, unconditional: the level pair is
`GpG d L 9 m₁ 1`, `HmG d L 9 m₁ 1`, as in `tower_core_rates_general`. -/
theorem tower_core_rates_two_general
    {d L : ℕ} [NeZero L] (N : ℕ) (hd : 3 ≤ d) (hL : 3 ≤ L)
    {ν : ℝ} (hν0 : 0 ≤ ν) (hν : ν * (L : ℝ) ^ (2 * (1 + 1)) ≤ 1)
    {κ0 κdec : ℝ} (κmin : ℝ) (hκ0 : aEnt d L + 1 ≤ κ0)
    (hκdec : 3 * κ0 + c1 d L + 5 ≤ κdec) :
    ∃ (m₁ : ℕ) (c BG κ t c₂ BG₂ δc : ℝ),
      4 ≤ m₁ ∧ 0 < t ∧
      Nonempty (FlCore N (GpG d L 9 m₁ 1) (HmG d L 9 m₁ 1) 1 ν c BG κ t (levelKc d L)
        (Cchi d L) c₂ BG₂ t) ∧
      0 ≤ κ0 ∧ 3 * κ0 + 3 ≤ κdec ∧
      4 * ((d : ℕ) : ℝ) * (((2 * L + 1) ^ d : ℕ) : ℝ) * κdec ≤ κ ∧ 1 ≤ (κ / 2 - 1) / 2 ∧
      Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) * (((L ^ 1) ^ d : ℕ) : ℝ)) ≤ (κ / 2 - 1) / 2 ∧
      c7 d L N BG κ ≤ thm73C3 d L N ∧
      cstarX d L * Real.exp (N0 d L * κ) ≤ ((L : ℕ) : ℝ) ^ m₁ ∧
      decDomMargin d L N BG κ (xiC1 d * t) < δc ∧
      K4 d L N BG κ * (xiC1 d * t) < coerciveConst d / 2 ∧
      δc ^ 2 * smallConstX d L κ ≤ 1 / 4 ∧
      2 * t ≤ deltaStar d L N ∧ cK2 d L N * (2 * t) < bgC0 d L N / 2 ∧
      cK2 d L N * t ≤ c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8) ∧
      cK2' d L N (famConst d L BG₂ κ) * t ≤ c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8) ∧
      2 * (compC4 d * (bgK1 d L N * (xiC1 d * t))) + 5 * (2 * t) ≤ bgC1 d L N ∧
      aEnt d L + 1 ≤ κ0 ∧
      0 + 3 * κ0 + c1 d L + 3 / 2 ≤ 2 * κdec - 1 ∧ 0 ≤ famConst d L BG₂ κ ∧ κmin ≤ κ ∧
      2 * (K4 d L N BG κ * (xiC1 d * t)) <
        deltaStar' d L N (famConst d L BG κ) (gamma1 d / 8) ∧
      bgK1 d L N * (xiC1 d * t) < deltaStar d L N ∧
      Nonempty (FlCore N (GpG d L 9 m₁ 1) (HmG d L 9 m₁ 1) 1 ν c BG κ (2 * t)
        (levelKc d L) (Cchi d L) c₂ BG₂ (2 * t)) ∧
      decDomMargin d L N BG κ (xiC1 d * (2 * t)) < δc ∧
      K4 d L N BG κ * (xiC1 d * (2 * t)) < coerciveConst d / 2 :=
  tower_core_rates_two_general_of_pair (N₁ := 9) (K := 1 + 1) N hd hL
    (fun m₁ => GpG d L 9 m₁ 1) (fun m₁ => HmG d L 9 m₁ 1) (a₁ := 1) (ν := ν)
    (hpair_lvG hd hL hν0 hν) κmin hκ0 hκdec

/-- The `renSol` variant: `tower_core_rates_two_general` without the three conjuncts at the radius `2 t`. -/
theorem tower_core_rates_renSol_general
    {d L : ℕ} [NeZero L] (N : ℕ) (hd : 3 ≤ d) (hL : 3 ≤ L)
    {ν : ℝ} (hν0 : 0 ≤ ν) (hν : ν * (L : ℝ) ^ (2 * (1 + 1)) ≤ 1)
    {κ0 κdec : ℝ} (κmin : ℝ) (hκ0 : aEnt d L + 1 ≤ κ0)
    (hκdec : 3 * κ0 + c1 d L + 5 ≤ κdec) :
    ∃ (m₁ : ℕ) (c BG κ t c₂ BG₂ δc : ℝ),
      4 ≤ m₁ ∧ 0 < t ∧
      Nonempty (FlCore N (GpG d L 9 m₁ 1) (HmG d L 9 m₁ 1) 1 ν c BG κ t (levelKc d L)
        (Cchi d L) c₂ BG₂ t) ∧
      0 ≤ κ0 ∧ 3 * κ0 + 3 ≤ κdec ∧
      4 * ((d : ℕ) : ℝ) * (((2 * L + 1) ^ d : ℕ) : ℝ) * κdec ≤ κ ∧ 1 ≤ (κ / 2 - 1) / 2 ∧
      Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) * (((L ^ 1) ^ d : ℕ) : ℝ)) ≤ (κ / 2 - 1) / 2 ∧
      c7 d L N BG κ ≤ thm73C3 d L N ∧
      cstarX d L * Real.exp (N0 d L * κ) ≤ ((L : ℕ) : ℝ) ^ m₁ ∧
      decDomMargin d L N BG κ (xiC1 d * t) < δc ∧
      K4 d L N BG κ * (xiC1 d * t) < coerciveConst d / 2 ∧
      δc ^ 2 * smallConstX d L κ ≤ 1 / 4 ∧
      2 * t ≤ deltaStar d L N ∧ cK2 d L N * (2 * t) < bgC0 d L N / 2 ∧
      cK2 d L N * t ≤ c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8) ∧
      cK2' d L N (famConst d L BG₂ κ) * t ≤ c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8) ∧
      2 * (compC4 d * (bgK1 d L N * (xiC1 d * t))) + 5 * (2 * t) ≤ bgC1 d L N ∧
      aEnt d L + 1 ≤ κ0 ∧
      0 + 3 * κ0 + c1 d L + 3 / 2 ≤ 2 * κdec - 1 ∧ 0 ≤ famConst d L BG₂ κ ∧ κmin ≤ κ ∧
      2 * (K4 d L N BG κ * (xiC1 d * t)) <
        deltaStar' d L N (famConst d L BG κ) (gamma1 d / 8) ∧
      bgK1 d L N * (xiC1 d * t) < deltaStar d L N :=
  by
  obtain ⟨m₁, c, BG, κ, t, c₂, BG₂, δc, h4, ht, hC, h1, h2, h3, h4', h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, -, -, -⟩ :=
    tower_core_rates_two_general N hd hL hν0 hν κmin hκ0 hκdec
  exact ⟨m₁, c, BG, κ, t, c₂, BG₂, δc, h4, ht, hC, h1, h2, h3, h4', h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21⟩

/-- The `ren` variant: `tower_core_rates_renSol_general` without the margin `K₁ ξ₁ t < δ_*`. -/
theorem tower_core_rates_ren_general
    {d L : ℕ} [NeZero L] (N : ℕ) (hd : 3 ≤ d) (hL : 3 ≤ L)
    {ν : ℝ} (hν0 : 0 ≤ ν) (hν : ν * (L : ℝ) ^ (2 * (1 + 1)) ≤ 1)
    {κ0 κdec : ℝ} (κmin : ℝ) (hκ0 : aEnt d L + 1 ≤ κ0)
    (hκdec : 3 * κ0 + c1 d L + 5 ≤ κdec) :
    ∃ (m₁ : ℕ) (c BG κ t c₂ BG₂ δc : ℝ),
      4 ≤ m₁ ∧ 0 < t ∧
      Nonempty (FlCore N (GpG d L 9 m₁ 1) (HmG d L 9 m₁ 1) 1 ν c BG κ t (levelKc d L)
        (Cchi d L) c₂ BG₂ t) ∧
      0 ≤ κ0 ∧ 3 * κ0 + 3 ≤ κdec ∧
      4 * ((d : ℕ) : ℝ) * (((2 * L + 1) ^ d : ℕ) : ℝ) * κdec ≤ κ ∧ 1 ≤ (κ / 2 - 1) / 2 ∧
      Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) * (((L ^ 1) ^ d : ℕ) : ℝ)) ≤ (κ / 2 - 1) / 2 ∧
      c7 d L N BG κ ≤ thm73C3 d L N ∧
      cstarX d L * Real.exp (N0 d L * κ) ≤ ((L : ℕ) : ℝ) ^ m₁ ∧
      decDomMargin d L N BG κ (xiC1 d * t) < δc ∧
      K4 d L N BG κ * (xiC1 d * t) < coerciveConst d / 2 ∧
      δc ^ 2 * smallConstX d L κ ≤ 1 / 4 ∧
      2 * t ≤ deltaStar d L N ∧ cK2 d L N * (2 * t) < bgC0 d L N / 2 ∧
      cK2 d L N * t ≤ c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8) ∧
      cK2' d L N (famConst d L BG₂ κ) * t ≤ c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8) ∧
      2 * (compC4 d * (bgK1 d L N * (xiC1 d * t))) + 5 * (2 * t) ≤ bgC1 d L N ∧
      aEnt d L + 1 ≤ κ0 ∧
      0 + 3 * κ0 + c1 d L + 3 / 2 ≤ 2 * κdec - 1 ∧ 0 ≤ famConst d L BG₂ κ ∧ κmin ≤ κ ∧
      2 * (K4 d L N BG κ * (xiC1 d * t)) <
        deltaStar' d L N (famConst d L BG κ) (gamma1 d / 8) :=
  by
  obtain ⟨m₁, c, BG, κ, t, c₂, BG₂, δc, h4, ht, hC, h1, h2, h3, h4', h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, -⟩ :=
    tower_core_rates_renSol_general N hd hL hν0 hν κmin hκ0 hκdec
  exact ⟨m₁, c, BG, κ, t, c₂, BG₂, δc, h4, ht, hC, h1, h2, h3, h4', h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
end Balaban.Inhabited
