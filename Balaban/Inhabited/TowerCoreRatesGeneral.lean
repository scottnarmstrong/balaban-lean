/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.TowerCoreRatesAtLeast
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp

/-!
# The core rates of the tower in dimension `d`, block size `L`, `N` spin components

`tower_core_rates_at_least` fixes `d = L = 3`.  Here the same twenty-one clauses (plus `κmin ≤ κ`)
are proved for every `d ≥ 3`, `L ≥ 3`, `N`, with every numeral replaced by its general expression:
the entropy count is `4 d (2L+1)^d`, the logarithmic certificate `log 9261 ≤ 9260` is replaced by
`log A ≤ A - 1` for `A = (2L+1)^d (L^1)^d`, and the fixed lower bound `40000` is not needed.

The one clause that is not a real-number inequality is the `FlCore` clause.  It needs, for every
`m₁ ≥ 4`, a pair of consecutive levels of generating sets on the torus of side `N₁ L^{m₁}`, with the
decoupled setting, the operator setting and the background hypotheses.  The landed pair
(`InteractionLevelPair.Gp`, `Hm`) is such a family at `d = L = 3`, `N₁ = 9`, `K = 2`.  In
`tower_core_rates_general_of_pair` this family is a hypothesis; everything else is proved.
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation
  Balaban.Localization Balaban.Localization.LevelPair Balaban.Localization.I5Inhabited
  Balaban.Polymer Balaban.SmallField.Def6 Filter Topology

/-- **The core rates of the tower at general `(d, L, N)`**, given a family of level pairs.

The family `(Gp m₁, Hm m₁)` of generating sets on the torus of side `N₁ L^{m₁}` must provide, for
every `m₁ ≥ 4`, a level `n` with `Hm m₁` of level `n` and `Gp m₁` of level `n + 1`, the decoupled
setting of `Gp m₁`, the operator setting of `Hm m₁` (both for the weight `compWeight L a₁` and
the mass `ν`) and the background hypotheses for `Gp m₁`. -/
theorem tower_core_rates_general_of_pair {d L : ℕ} [NeZero L] (N : ℕ) (hd : 3 ≤ d) (hL : 3 ≤ L)
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
      0 + 3 * κ0 + c1 d L + 3 / 2 ≤ 2 * κdec - 1 ∧ 0 ≤ famConst d L BG₂ κ ∧ κmin ≤ κ := by
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
  have hpos : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < t := self_mem_nhdsWithin
  obtain ⟨t, hC, g1, g2, g3, g4, g5, g6, g7, ht0⟩ := (hev.and ((wk e1).and ((wk e2).and
    ((wk e3).and ((wk e4).and ((wk e5).and ((wk e6).and ((wk e7).and hpos)))))))).exists
  have hlogA : Real.log A ≤ A - 1 := Real.log_le_sub_one_of_pos (by linarith)
  have hlogκ : Real.log A ≤ (κ / 2 - 1) / 2 := by linarith
  have hκdec3 : 3 * κ0 + 3 ≤ κdec := by linarith
  refine ⟨m₁, c, BG, κ, t, c₂, BG₂, δc, h4, ht0, hC, hκ00, hκdec3, hκ1, by linarith, hlogκ,
    c7_le_thm73C3_of_large hd0 hBG1 hκ2, hm3, g6, g7,
    hδcSX, g1.le, g2, g3.le, g4.le, g5.le, hκ0, by linarith, hB0, le_max_right _ _⟩

/-- **Recovery of `tower_core_rates_at_least`** from the general theorem at `d = L = 3`, with the
landed pair `Gp`, `Hm` (`N₁ = 9`, `K = 2`, `ϱ = rhoSep m₁`, `a₁ = 1`, `ν = nuW`). -/
theorem tower_core_rates_at_least_of_general (N : ℕ) {κ0 κdec : ℝ} (κmin : ℝ)
    (hκ0 : aEnt 3 3 + 1 ≤ κ0) (hκdec : 3 * κ0 + c1 3 3 + 5 ≤ κdec) :
    ∃ (m₁ : ℕ) (c BG κ t c₂ BG₂ δc : ℝ),
      4 ≤ m₁ ∧ 0 < t ∧
      Nonempty (FlCore N (Gp m₁ (rhoSep m₁)) (Hm m₁ (rhoSep m₁)) 1 nuW c BG κ t (levelKc 3 3)
        (Cchi 3 3) c₂ BG₂ t) ∧
      0 ≤ κ0 ∧ 3 * κ0 + 3 ≤ κdec ∧
      4 * ((3 : ℕ) : ℝ) * (((2 * 3 + 1) ^ 3 : ℕ) : ℝ) * κdec ≤ κ ∧ 1 ≤ (κ / 2 - 1) / 2 ∧
      Real.log ((((2 * 3 + 1) ^ 3 : ℕ) : ℝ) * (((3 ^ 1) ^ 3 : ℕ) : ℝ)) ≤ (κ / 2 - 1) / 2 ∧
      c7 3 3 N BG κ ≤ thm73C3 3 3 N ∧
      cstarX 3 3 * Real.exp (N0 3 3 * κ) ≤ ((3 : ℕ) : ℝ) ^ m₁ ∧
      decDomMargin 3 3 N BG κ (xiC1 3 * t) < δc ∧
      K4 3 3 N BG κ * (xiC1 3 * t) < coerciveConst 3 / 2 ∧
      δc ^ 2 * smallConstX 3 3 κ ≤ 1 / 4 ∧
      2 * t ≤ deltaStar 3 3 N ∧ cK2 3 3 N * (2 * t) < bgC0 3 3 N / 2 ∧
      cK2 3 3 N * t ≤ c6' 3 3 N (famConst 3 3 BG₂ κ) (gamma1 3 / 8) ∧
      cK2' 3 3 N (famConst 3 3 BG₂ κ) * t ≤ c6' 3 3 N (famConst 3 3 BG₂ κ) (gamma1 3 / 8) ∧
      2 * (compC4 3 * (bgK1 3 3 N * (xiC1 3 * t))) + 5 * (2 * t) ≤ bgC1 3 3 N ∧
      aEnt 3 3 + 1 ≤ κ0 ∧
      0 + 3 * κ0 + c1 3 3 + 3 / 2 ≤ 2 * κdec - 1 ∧ 0 ≤ famConst 3 3 BG₂ κ ∧ κmin ≤ κ :=
  tower_core_rates_general_of_pair (d := 3) (L := 3) (N₁ := 9) (K := 2) N (by norm_num)
    (by norm_num) (fun m₁ => Gp m₁ (rhoSep m₁)) (fun m₁ => Hm m₁ (rhoSep m₁))
    (fun _ h4 => ⟨1, ⟨dgSettingNu h4⟩, ⟨opSettingNu h4⟩, isLevel_Hm, isLevel_Gp, bgHypNu _⟩)
    κmin hκ0 hκdec

end Balaban.Inhabited
