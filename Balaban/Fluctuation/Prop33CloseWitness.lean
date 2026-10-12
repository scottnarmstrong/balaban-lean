/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.Prop33CloseBh
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FunProp

/-!
# Proposition 3.3 applied at the mixed-pair witness (W136b)

`prop33_nu_witness`: at `d = L = 3`, `K = 2`, `n = 1`, `N₁ = 9`, `a₁ = 1`, `ν = 1/81`, `m₀ = 1`,
the combined bound `interaction_expansion_bound_nu_closed` applies with every premise discharged
(`FlCore`, `IsLevel`, `BgHyp`, `HatConn`, `RowInHat`, the cover data of the potential part and of the
source sites, `hc7 : c₇ ≤ thm73C3`, the smallness `δ₀ + 5 R δ₁ ≤ c₁` that gives the domain premise
`hreal`, the bound `‖h̃‖ ≤ 1 + 2/ν`, the κ-inequalities, the smallness of `δ₁`, empty sets of old
terms and of observable terms), so its conclusion is not vacuous.
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation Finset
  Matrix Set Metric Filter Topology

/-- The set of admissible pairs of directions of `LocInt` in Proposition 3.3. -/
def prop33XW {d L N₁ m₁ K N : ℕ} [NeZero N₁] [NeZero L] {ϱm : ℝ}
    (Hm : GeneratingSet d L (N₁ * L ^ m₁) K ϱm) (δ₁ Rσ R₁ r : ℝ) :
    Set (((CTorus d L N₁ m₁ K → Fin N → ℂ) × (CTorus d L N₁ m₁ K → Fin N → ℂ)) ×
      ((CTorus d L N₁ m₁ K → Fin N → ℂ) × (CTorus d L N₁ m₁ K → Fin N → ℂ))) :=
  {xw | ((xw.1.1, xw.2.1) ∈ {xw : (CTorus d L N₁ m₁ K → Fin N → ℂ) ×
              (CTorus d L N₁ m₁ K → Fin N → ℂ) |
            (∀ σ : ℂ, ‖σ‖ < Rσ → ∀ t : ℂ, ‖t‖ < R₁ → ∀ τ : ℂ, ‖τ‖ ≤ r →
              (σ * t) • xw.1 + τ • xw.2 ∈ FlBall Hm δ₁) ∧
            IsLayerConstant Hm xw.1 ∧ IsLayerConstant Hm xw.2}) ∧
          (xw.1.1, xw.2.1) ∈ {xw : (CTorus d L N₁ m₁ K → Fin N → ℂ) ×
              (CTorus d L N₁ m₁ K → Fin N → ℂ) |
            ∀ σ : ℂ, ‖σ‖ < Rσ → ∀ t : ℂ, ‖t‖ < R₁ → ∀ τ : ℂ, ‖τ‖ ≤ r →
              (σ * t) • xw.1 + τ • xw.2 ∈ FlBall Hm δ₁} ∧
          (xw.1.2, xw.2.2) ∈ {xw : (CTorus d L N₁ m₁ K → Fin N → ℂ) ×
              (CTorus d L N₁ m₁ K → Fin N → ℂ) |
            ∀ σ : ℂ, ‖σ‖ < Rσ → ∀ t : ℂ, ‖t‖ < R₁ → ∀ τ : ℂ, ‖τ‖ ≤ r →
              (σ * t) • xw.1 + τ • xw.2 ∈ FlBall Hm δ₁} ∧
          (xw.1.2, xw.2.2) ∈ {xw : (CTorus d L N₁ m₁ K → Fin N → ℂ) ×
              (CTorus d L N₁ m₁ K → Fin N → ℂ) |
            (∀ σ : ℂ, ‖σ‖ < Rσ → ∀ t : ℂ, ‖t‖ < R₁ → ∀ τ : ℂ, ‖τ‖ ≤ r →
              (σ * t) • xw.1 + τ • xw.2 ∈ FlBall Hm δ₁) ∧
            IsLayerConstant Hm xw.1 ∧ IsLayerConstant Hm xw.2}}

theorem DecSpecs.mono_BG {d L : ℕ} [NeZero L] {c BG BG' : ℝ} (h : DecSpecs d L c BG)
    (hB : BG ≤ BG') : DecSpecs d L c BG' :=
  ⟨h.fam.mono_BG hB, h.dg2.mono le_rfl hB, h.close.mono le_rfl hB, h.one, h.an⟩

namespace LevelPair

open I5Inhabited

/-- The mass of the witness. -/
noncomputable def nuW : ℝ := 1 / 81

theorem nuW_pos : 0 < nuW := by unfold nuW; norm_num

theorem dgSettingNu {m₁ : ℕ} (h4 : 4 ≤ m₁) :
    DGSetting (Gp m₁ (rhoSep m₁)) (compWeight 3 1) nuW :=
  { dgSetting h4 with
    mass := nuW_pos.le
    massLe := by unfold nuW; norm_num }

theorem opSettingNu {m₁ : ℕ} (h4 : 4 ≤ m₁) :
    Dec2.OpSetting (Hm m₁ (rhoSep m₁)) (compWeight 3 1) nuW :=
  { hd := (dgSettingNu h4).hd, hL := (dgSettingNu h4).hL, mass := (dgSettingNu h4).mass,
    massLe := (dgSettingNu h4).massLe, weights := (dgSettingNu h4).weights,
    sep := (dgSettingNu h4).sep }

theorem bgHypNu (m₁ : ℕ) : BgHyp 3 3 2 (rhoSep m₁) (compWeight 3 1) nuW :=
  { bgHyp_rho m₁ with
    mass := nuW_pos.le
    massLe := by unfold nuW; norm_num }


open Classical in
/-- **Proposition 3.3 (merged bound with the `ν`-part) at the mixed-pair witness**: for every `N`
there are constants (`m₁`, `ϱ`, `c`, `B_G`, `κ`, `ε`, `c₂`, `B_{G,2}`, `δ₁`) and `FlCore` for the
pair of consecutive levels `(levelGS 1, levelGS 2)` on the torus `ℤ_{9·3^{m₁}·3²}^3` with
`a₁ = 1`, `ν = 1/81`, with `c₇ ≤ thm73C3`, such that for all `c_β`, `c_ν` the localized expansion
of `interaction_expansion_bound_nu_closed` (no old terms, no observable terms) holds with
`κ_dec = 3`, `R_σ = 1`, `R₁ = 2`, `r = 1`, `m₀ = 1`. -/
theorem prop33_nu_witness (N : ℕ) :
    ∃ (m₁ : ℕ) (ϱ c BG κ eps c₂ BG₂ δ₁ : ℝ)
      (_ : FlCore N (Gp m₁ ϱ) (Hm m₁ ϱ) 1 nuW c BG κ eps (levelKc 3 3) (Cchi 3 3) c₂ BG₂ δ₁),
      0 < δ₁ ∧ c7 3 3 N BG κ ≤ thm73C3 3 3 N ∧
      ∀ cβ cν : ℂ, ∃ (𝒴 : Finset (Set (CTorus 3 3 9 m₁ 2)))
        (T : Set (CTorus 3 3 9 m₁ 2) →
          ((CTorus 3 3 9 m₁ 2 → Fin N → ℂ) × (CTorus 3 3 9 m₁ 2 → Fin N → ℂ)) →
          ((CTorus 3 3 9 m₁ 2 → Fin N → ℂ) × (CTorus 3 3 9 m₁ 2 → Fin N → ℂ)) → ℂ →
          RawData 3 3 (9 * 3 ^ m₁) 2 N × (CTorus 3 3 9 m₁ 2 → Fin N → ℂ) → ℂ),
        LocInt (XiCRaw (Gp m₁ ϱ) (compWeight 3 1) nuW 2 1 eps ×ˢ l1Ball 3 3 9 m₁ 2 N)
          (prop33XW (N := N) (Hm m₁ ϱ) δ₁ 1 2 1) 1 𝒴 T
          (fun x w σ p =>
            (-cβ) * raySrc3 (interactionOne (isLevel_Hm (m₁ := m₁) (ϱ := ϱ))
                (isLevel_Gp (m₁ := m₁) (ϱ := ϱ)) (by norm_num) 1 nuW eps)
              taylorWeight x.1 w.1 σ p.1 +
            cβ * (∑ s : CTorus 3 3 9 m₁ 2 × Fin N, p.2 s.1 s.2 * dirTermSrc
              (onXi (Gp m₁ ϱ) 1 nuW eps
                (fun D ψ' => svec (Hm m₁ ϱ) (flFieldOne (Gp m₁ ϱ) (Hm m₁ ϱ) BG₂ κ 1 nuW D ψ')
                  s.1 s.2)) (fun _ => (1 : ℂ)) x.2 w.2 σ p.1) +
            cν * dirTermSrc (onXi (Gp m₁ ϱ) 1 nuW eps
              (fun D ψ' => nuTotal (Gp m₁ ϱ) (Hm m₁ ϱ) 1 nuW BG₂ κ D ψ'))
              (fun _ => (1 : ℂ)) x.1 w.1 σ p.1)
          (fun Y => prop33Eps 3 3 N m₁ 1 1 1 nuW BG BG₂ κ δ₁ 1 0 0 * ‖cβ‖ *
              Real.exp (-(2 * 3 - 1) * treeLenCovOne 1 (1 + 1) Y) +
            ‖cν‖ * (1 * (c1 3 3 * (((3 : ℕ) : ℝ) ^ (1 + m₁)) ^ 3 *
              nuBd 3 3 N 1 (cK2' 3 3 N (famConst 3 3 BG₂ κ) * δ₁)
                (K4 3 3 N BG κ * (xiC1 3 * eps) + (1 + 3 * (xiC1 3 * eps)) + (1 + 2 / nuW)) / 1) *
              Real.exp (-(2 * 3 - 1) * treeLenCovOne 1 (1 + 1) Y)))
          (fun Y p p' => agreeOn (thickSet (Gp m₁ ϱ) Y) p.1 p'.1 ∧ ∀ x ∈ Y, p.2 x = p'.2 x)
          (fun Y a a' => (∀ y ∈ psiThick Y, a.1 y = a'.1 y) ∧ (∀ y ∈ psiThick Y, a.2 y = a'.2 y)) := by
  obtain ⟨c, BG0, hS0⟩ := decSpecs_exists (d := 3) (L := 3) (by norm_num) (by norm_num)
  set BG := max BG0 1 with hBGdef
  have hS : DecSpecs 3 3 c BG := hS0.mono_BG (le_max_left _ _)
  have hBG1 : 1 ≤ BG := le_max_right _ _
  obtain ⟨c₂, BG₂, hS2⟩ := Dec2.decSpecs_exists (d := 3) (L := 3) (Kc := levelKc 3 3)
    (Cx := Cchi 3 3) (by norm_num) (by norm_num) (levelKc_nonneg 3 3) (Cchi_nonneg 3 3)
  have hT3 := thm73C3_pos (d := 3) (L := 3) (N := N) (by norm_num)
  set κ : ℝ := max 100000 (1 / thm73C3 3 3 N) with hκdef
  have hκ1 : 100000 ≤ κ := le_max_left _ _
  have hκ2 : 1 / thm73C3 3 3 N ≤ κ := le_max_right _ _
  obtain ⟨m₁, h4, hm⟩ := exists_m₁ (max (c * Real.exp ((N0 3 3 : ℝ) * κ))
    (c₂ * Real.exp ((N0 3 3 : ℝ) * κ)))
  have S := dgSettingNu h4
  have SH := opSettingNu h4
  have hev := flCore_level_eventually (N := N) S SH isLevel_Hm isLevel_Gp (bgHypNu m₁)
    hS (κ := κ) (by linarith) ((le_max_left _ _).trans (by exact_mod_cast hm)) hS2
    ((le_max_right _ _).trans (by exact_mod_cast hm))
  have hB0 : 0 ≤ famConst 3 3 BG₂ κ := by
    have := famConst_ge_one (L := 3) hS2.fam.2.1 κ (d := 3) (by norm_num); linarith
  have hc6 : 0 < c6' 3 3 N (famConst 3 3 BG₂ κ) (gamma1 3 / 8) :=
    c6'_pos hB0 (by have := gamma1_pos (d := 3) (by norm_num); positivity)
  have hDs : 0 < deltaStar 3 3 N := deltaStar_pos (d := 3) (L := 3) (N := N) (by norm_num)
  have hC0 : 0 < bgC0 3 3 N := bgC0_pos 3 3 N (by norm_num)
  have hC1 : 0 < bgC1 3 3 N := bgC1_pos' (d := 3) (L := 3) (N := N) (by norm_num)
  have wk : ∀ {p : ℝ → Prop}, (∀ᶠ t in 𝓝 (0 : ℝ), p t) → ∀ᶠ t in 𝓝[>] (0 : ℝ), p t :=
    fun h => eventually_nhdsWithin_of_eventually_nhds h
  have e1 := ev_lt (f := fun t : ℝ => 2 * t) (by fun_prop) (c := deltaStar 3 3 N) (by simpa using hDs)
  have e2 := ev_lt (f := fun t : ℝ => cK2 3 3 N * (2 * t)) (by fun_prop) (c := bgC0 3 3 N / 2)
    (by simp; positivity)
  have e3 := ev_lt (f := fun t : ℝ => cK2 3 3 N * t) (by fun_prop)
    (c := c6' 3 3 N (famConst 3 3 BG₂ κ) (gamma1 3 / 8)) (by simpa using hc6)
  have e4 := ev_lt (f := fun t : ℝ => cK2' 3 3 N (famConst 3 3 BG₂ κ) * t) (by fun_prop)
    (c := c6' 3 3 N (famConst 3 3 BG₂ κ) (gamma1 3 / 8)) (by simpa using hc6)
  have e5 := ev_lt (f := fun t : ℝ => 2 * (compC4 3 * (bgK1 3 3 N * (xiC1 3 * t))) + 5 * (2 * t))
    (by fun_prop) (c := bgC1 3 3 N) (by simpa using hC1)
  have hpos : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < t := self_mem_nhdsWithin
  obtain ⟨t, ⟨hC⟩, g1, g2, g3, g4, g5, ht0⟩ := (hev.and ((wk e1).and ((wk e2).and ((wk e3).and
    ((wk e4).and ((wk e5).and hpos)))))).exists
  have hc7 : c7 3 3 N BG κ ≤ thm73C3 3 3 N :=
    c7_le_thm73C3_of_large (by norm_num) hBG1 hκ2
  refine ⟨m₁, rhoSep m₁, c, BG, κ, t, c₂, BG₂, t, hC, ht0, hc7, fun cβ cν => ?_⟩
  have hxi1 : xiC1 3 * t ≤ 1 := by
    have h1 := hC.c7le
    have h2 := c7_le_bgC1 3 3 N BG κ
    have h3 := bgC1_le_small 3 3 N (by norm_num)
    linarith
  have hBh := hBh_of_xi (N := N) (Gp := Gp m₁ (rhoSep m₁)) (bgHypNu m₁) nuW_pos hC.small1 hC.eps_pos hxi1
  have h343 : Real.log (9261 : ℝ) ≤ 9261 - 1 := Real.log_le_sub_one_of_pos (by norm_num)
  have hlogκ : Real.log ((((2 * 3 + 1) ^ 3 : ℕ) : ℝ) * (((3 ^ 1) ^ 3 : ℕ) : ℝ)) ≤ (κ / 2 - 1) / 2 := by
    norm_num at h343 ⊢
    linarith
  have key := interaction_expansion_bound_nu_closed (Rσ := 1) (R₁ := 2) (r := 1) (R := 2)
    (m₀ := 1) (κdec := 3) (κ₀ := 0) (ρE := 0) (ρM := 0) (Bh := 1 + 2 / nuW)
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
    hC cβ hatConn (rowInHat_level S isLevel_Hm isLevel_Gp) le_rfl (by norm_num) (by norm_num; linarith)
    (by linarith) (by norm_num) (by norm_num) isLevel_Hm isLevel_Gp (by norm_num) one_pos
    (bgHypNu m₁) hc7 le_rfl g1.le g2 g3.le g4.le (by linarith) (fun _ => covSetup)
    (fun _ => by rw [Finset.coe_univ, X1_eq_univ]) (fun _ => hopt)
    (fun _ => treeLen_zero) (fun _ => hlogκ) le_rfl (fun z _ _ => Finset.mem_coe.2 (Finset.mem_univ _))
    (fun z => blockMargin_univ fun x _ _ => mem_some_intBox h4 x)
    (∅ : Finset PEmpty.{1}) (fun τ hτ => absurd hτ (by simp)) (fun τ hτ => absurd hτ (by simp))
    (fun τ hτ => absurd hτ (by simp)) (fun τ hτ => absurd hτ (by simp))
    (fun τ hτ => absurd hτ (by simp)) (fun τ hτ => absurd hτ (by simp))
    (fun τ hτ => absurd hτ (by simp)) (fun τ hτ => absurd hτ (by simp))
    (fun τ hτ => absurd hτ (by simp))
    (fun _ => covSetup) (fun _ => by rw [Finset.coe_univ, X1_eq_univ]) (fun _ => hopt)
    (fun _ => treeLen_zero) (fun _ => hlogκ) (fun s => Finset.mem_univ _)
    (∅ : Finset PEmpty.{1}) (fun τ => PEmpty.elim τ) (fun τ => PEmpty.elim τ)
    (fun τ hτ => absurd hτ (by simp)) (fun τ hτ => absurd hτ (by simp))
    (fun τ hτ => absurd hτ (by simp)) (fun τ hτ => absurd hτ (by simp))
    (fun τ hτ => absurd hτ (by simp)) (fun τ hτ => absurd hτ (by simp))
    (fun τ hτ => absurd hτ (by simp)) (fun τ hτ => absurd hτ (by simp))
    (fun τ hτ => absurd hτ (by simp)) (fun τ hτ => absurd hτ (by simp))
    (fun τ => PEmpty.elim τ) (fun τ hτ => absurd hτ (by simp)) le_rfl (fun x => by simp) le_rfl
    (fun p => by simp) (by unfold nuW; norm_num) hBh cν
    (fun z x _ => Finset.mem_coe.2 (Finset.mem_univ _))
  obtain ⟨𝒴, T, hL⟩ := key
  exact ⟨𝒴, T, hL.congr_val (fun xw hxw σ hσ p hp => by simp)⟩

end LevelPair

end Balaban.Localization
