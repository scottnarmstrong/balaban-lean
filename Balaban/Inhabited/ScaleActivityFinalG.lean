/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.LevelRayTower
public import Balaban.Inhabited.DAPhysicalTower
public import Balaban.Inhabited.StepTowerG
public import Balaban.Inhabited.LevelRayDataGeneral
public import Balaban.Inhabited.LevelAmpGeneral
public import Balaban.Inhabited.LevelLemmasGeneral
public import Balaban.Inhabited.LevelPairGeneral
public import Balaban.Fluctuation.LevelLocalCover
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

/-!
# The zero-class activity bound at every scale, general `d`, `L`, `N`

This is `ScaleActivityFinal` with `3, 3, 2` replaced by `d, L, N` (`d, L ≥ 3`, `N ≥ 2`).  For the
step `hatStepKG` at the separation `rhoSepG d L m₁` (constant unit block datum, coordinate unit
external field), the zero class has a step activity bound

* at every scale `k ≥ 1`,
* on every torus `CTorus d L N₁ m₁ (k + 1)` with `L ∣ N₁` and `5 < N₁`,
* for every mass `0 < ν` with `ν · L^{2(k+1)} ≤ 1`,
* for every `β ≥ β₀`,

with the rates `κ₀ = a_Ent + 1`, `κ_dec = 100 (κ₀ + c₁ + 10)`, `κ' = (3/2) κ_dec + κ₀ + 1`, with
`κ_H = 2 κ_dec - 1` and prefactor at most `C (log b)^{3p}/√b`, `b = β L^{k(d-2)}` the block
coupling (`hatStepKG_betaU`).  The constants `m₁, t, δ, β₀, C` do not depend on `k`, `N₁`, `ν`.
The proof is the proof of the fixed theorem with the general pieces `tower_core_rates_general`,
`scale_C_items_general`, `scale_amp_exists_general`, `dgSetting_lvG`, `opSetting_lvG`,
`bgHyp_lvG`, `rowInHat_lvG`, `hatConn_lvTopG`; the engine
`stepActivityBound_zeroClass_direct_scaled_uniform` and `LocalCover.levelLocalCover` are stated
for general `d, L, N`.  `ScaleActivityFinal` states the fixed `d = L = 3`, `N = 2` theorems as
corollaries.
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation
  Balaban.Localization Balaban.Localization.LevelPair Balaban.Localization.I5Inhabited
  Balaban.Polymer Balaban.SmallField.Def6 Balaban.Inhabited.LevelStep Filter Topology

open Classical in
/-- **The zero-class activity bound at every scale, general `d`, `L`, `N`, together with the
numerical tower it is proved from.**  This is
`stepActivityBound_zeroClass_direct_physical_scale_cutoff_general` with the output of
`tower_core_rates_general` (at the reference mass `νref L = L⁻⁴`, rate floor `κ_min`) exposed:
the constants `c, BG, κ, c₂, BG₂, δc` with `4 ≤ m₁`, the core `FlCore` of the pair at the
reference level, `κ_min ≤ κ`, the large-block, decoupling-margin, coercivity and smallness
conditions.  The determinant theorem uses the same tower. -/
theorem stepActivityBound_zeroClass_direct_physical_scale_cutoff_tower_general {d L N : ℕ}
    [NeZero L] (hd : 3 ≤ d) (hL : 3 ≤ L) (hN : 2 ≤ N) (κmin : ℝ) {A₁ : ℝ} (hA : 0 < A₁) (p : ℕ)
    {κ0 κdec κ' : ℝ} (hκ0def : κ0 = aEnt d L + 1) (hκdecdef : κdec = 100 * (κ0 + c1 d L + 10))
    (hκ'def : κ' = 3 / 2 * κdec + κ0 + 1) :
    ∃ (m₁ : ℕ) (t δ β₀ C c BG κ c₂ BG₂ δc : ℝ), 2 ≤ β₀ ∧ 0 < C ∧ 0 < t ∧ 0 < δ ∧ 4 ≤ m₁ ∧
      Nonempty (FlCore N (GpG d L 9 m₁ 1) (HmG d L 9 m₁ 1) 1 (νref L) c BG κ t (levelKc d L)
        (Cchi d L) c₂ BG₂ t) ∧
      κmin ≤ κ ∧ cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁ ∧
      decDomMargin d L N BG κ (xiC1 d * t) < δc ∧
      K4 d L N BG κ * (xiC1 d * t) < coerciveConst d / 2 ∧
      δc ^ 2 * smallConstX d L κ ≤ 1 / 4 ∧
      ∀ (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁], L ∣ N₁ → 5 < N₁ →
      ∀ ν : ℝ, 0 < ν → ν * (L : ℝ) ^ (2 * (k + 1)) ≤ 1 → ∀ β : ℝ, β₀ ≤ β →
      ∀ p₁ : ℝ, 0 < p₁ → p₁ ≤ pLog A₁ p (β * (L : ℝ) ^ (k * (d - 2))) →
        ∃ B : StepActivityBound
            (hatStepKG (d := d) (L := L) (N₁ := N₁) hN k m₁ (rhoSepG d L m₁) hk ν β p₁ δ)
            (zeroClass d L N₁ m₁ k N (rhoSepG d L m₁)) 0,
          B.κH = 2 * κdec - 1 ∧
          B.εH ≤ C * (Real.log (β * (L : ℝ) ^ (k * (d - 2)))) ^ (3 * p) /
            Real.sqrt (β * (L : ℝ) ^ (k * (d - 2))) ∧
          κ' + 3 * κ0 + c1 d L + 3 / 2 ≤ 2 * κdec - 1 ∧
          ∃ κout : ℝ, κout = 3 / 2 * κdec ∧ κdec ≤ κout ∧ κout ≤ min κ' κ' - κ0 - 1 := by
  classical
  have hN2 : 0 < N := by omega
  obtain ⟨-, δ, δ', T, -, -, hδ, hsm, hδ'0, hδ'a, hδ'b, hδ'c, -, -, -, -⟩ :=
    exists_witness_params_general d L N (by omega) (by omega) (fun _ => 0)
  have hc1 := one_le_c1 d L
  have hent := aEnt_nonneg d L
  obtain ⟨m₁, c, BG, κ, t, c₂, BG₂, δc, h4, ht0, ⟨hC₀⟩, hκ0, hκdec, hκ, h1, hlog, hc7,
    hMX, hdm, hα, hsmX, g1, g2, g3, g4, g5, hκE, hκa, hB0, hmin⟩ :=
    tower_core_rates_general N hd hL (ν := νref L) (by unfold νref; positivity)
      (by
        unfold νref
        have h0 : (0 : ℝ) < (L : ℝ) ^ 4 := by positivity
        rw [one_div, inv_mul_eq_div, div_le_one h0])
      (κ0 := κ0) (κdec := κdec) κmin (by rw [hκ0def]) (by rw [hκdecdef]; linarith)
  have hκdec0 : 0 ≤ κdec := by linarith
  have hbig : cstarX d L ≤ (L : ℝ) ^ m₁ := by
    have hκ_nn : 0 ≤ κ := le_trans (by positivity) hκ
    have h := Localization.cstarX_pos d L
    have h2 : cstarX d L ≤ cstarX d L * Real.exp ((N0 d L : ℝ) * κ) :=
      le_mul_of_one_le_right h.le (Real.one_le_exp (by positivity))
    linarith
  obtain ⟨β₀t, hβ₀t, hitems⟩ := scale_C_items_general hd hL hN hA p m₁ h4 hbig κ ht0 hδ hsm
    hδ'0 hδ'a hδ'b hδ'c
  have hρ4 : 0 ≤ rho4 d L N BG κ := by
    have hd0 : 0 < d := by omega
    have hBG := hC₀.hS.fam.2.1
    have hB1 : 0 ≤ famConst d L BG κ := by
      have := famConst_ge_one (L := L) hBG κ hd0; linarith
    unfold rho4
    exact (c6'_pos hB1 (by have := gamma1_pos hd0; positivity)).le
  set Q : ℝ := cK2' d L N (famConst d L BG₂ κ) with hQdef
  have hQ0 : 0 ≤ Q := (cK2'_pos_general hB0).le
  set P : ℝ := 3 * c1 d L * (((L : ℕ) : ℝ) ^ (1 + m₁)) ^ d *
    (((L : ℕ) : ℝ) ^ d * ((((N : ℕ) : ℝ) / 2) * (2 * (1 + Q) ^ 2 +
      (((d : ℕ) : ℝ) + 1 + rho4 d L N BG κ) * Q ^ 2) * t ^ 2)) with hPdef
  have hP0 : 0 ≤ P := by
    rw [hPdef]; positivity
  set K : ℝ := Q * t with hKdef
  have hK0' : 0 ≤ K := mul_nonneg hQ0 ht0.le
  obtain ⟨β₁, C0, hexpβ₁, hC0, hA'⟩ := scale_amp_exists_general (d := d) (L := L) (N := N)
    (by omega) hL (by omega) (A₁ := A₁) (κ := κ) (t := t) hA p ht0 hP0 hK0'
  set Kc'' : ℝ := K0 d L κ0 + 1 with hKc''
  have hKc''pos : 0 < Kc'' := by have := K0_pos d L κ0; rw [hKc'']; linarith
  have hκ'0 : 0 ≤ κ' := by rw [hκ'def]; linarith
  have hκa' : κ' + 3 * κ0 + c1 d L + 3 / 2 ≤ 2 * κdec - 1 := by
    rw [hκ'def, hκdecdef]; linarith
  have hxi1 : xiC1 d * t ≤ 1 := by
    have h1 := hC₀.c7le
    have h2 := c7_le_bgC1 d L N BG κ
    have h3 := bgC1_le_small d L N (by omega)
    linarith
  refine ⟨m₁, t, δ,
    max (max β₀t β₁) (daThreshold C0 (daT d L 2 Kc'' κdec κ0 κ') (3 * p)), 2 * C0, c, BG, κ,
    c₂, BG₂, δc, le_trans hβ₀t ((le_max_left _ _).trans (le_max_left _ _)), by positivity, ht0,
    hδ, h4, ⟨hC₀⟩, hmin, hMX, hdm, hα, hsmX, ?_⟩
  intro k hk N₁ _ hLN hN₁ ν hνpos hν β hβ p₁ hp0 hp₁
  have hν0 : 0 ≤ ν := hνpos.le
  have hβt : β₀t ≤ β := le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hβ)
  have hβ₁ : β₁ ≤ β := le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hβ)
  have hβd : daThreshold C0 (daT d L 2 Kc'' κdec κ0 κ') (3 * p) ≤ β :=
    le_trans (le_max_right _ _) hβ
  have hβ2 : 2 ≤ β := le_trans hβ₀t hβt
  have hβ0 : 0 < β := by linarith
  have hβ1 : 1 ≤ β := by linarith
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast (by omega : 1 ≤ L)
  have h3k : (1 : ℝ) ≤ (L : ℝ) ^ (k * (d - 2)) := one_le_pow₀ hL1
  have hbβ : β ≤ β * (L : ℝ) ^ (k * (d - 2)) := le_mul_of_one_le_right hβ0.le h3k
  have hb0 : 0 < β * (L : ℝ) ^ (k * (d - 2)) := by positivity
  obtain ⟨⟨hcψ0, hr0, hδ₁, hc⟩, hlt, ⟨R0⟩⟩ :=
    hitems k hk N₁ hN₁ ν hν0 hν β hβt p₁ hp0 hp₁
  have hexp : Real.exp 1 ≤ β * (L : ℝ) ^ (k * (d - 2)) := le_trans hexpβ₁ (hβ₁.trans hbβ)
  have hℓ : 1 ≤ Real.log (β * (L : ℝ) ^ (k * (d - 2))) :=
    (Real.le_log_iff_exp_le hb0).2 hexp
  have hamp2 := hA' (β * (L : ℝ) ^ (k * (d - 2))) (hβ₁.trans hbβ) β hβ1 p₁ hp0 hp₁
  set εU : ℝ := C0 * (Real.log (β * (L : ℝ) ^ (k * (d - 2)))) ^ (3 * p) /
    Real.sqrt (β * (L : ℝ) ^ (k * (d - 2))) with hεU
  have hεpos : 0 < εU := by
    have : 0 < (Real.log (β * (L : ℝ) ^ (k * (d - 2)))) ^ (3 * p) := by positivity
    have : 0 < Real.sqrt (β * (L : ℝ) ^ (k * (d - 2))) := Real.sqrt_pos.2 hb0
    rw [hεU]; positivity
  set S := hatStepKG (d := d) (L := L) (N₁ := N₁) hN k m₁ (rhoSepG d L m₁) hk ν β p₁ δ with hS
  have hSD := dgSetting_lvG (d := d) (L := L) (N₁ := N₁) (k := k) hd hL h4 hN₁ hν0 hν
  have hHB := bgHyp_lvG (k := k) hd hL (bgR0_le_rhoSepG m₁ hd hL) hν0 hν
  have hC : FlCore N (lvTopG d L N₁ m₁ k (rhoSepG d L m₁)) (lvLowG d L N₁ m₁ k (rhoSepG d L m₁))
      1 ν c BG κ t (levelKc d L) (Cchi d L) c₂ BG₂ t :=
    flCore_level_transfer hC₀ hSD (opSetting_lvG hd hL h4 hN₁ hν0 hν) (isLevel_lvLowG hk)
      isLevel_lvTopG hHB
  have hBh := hBh_of_xi (N := N) (Gp := lvTopG d L N₁ m₁ k (rhoSepG d L m₁)) hHB hνpos
    hC.small1 hC.eps_pos hxi1
  have hD : XiCData S.G' (compWeight L 1) ν (k + 1) 1 t S.D' := by
    refine ⟨fun _ => unitVec hN2, unitVec hN2, 0, 0,
      exists_xiC hHB (lvTopG d L N₁ m₁ k (rhoSepG d L m₁)) hN2 (massLe_lvG hν) ht0, ?_, ?_⟩
    · intro x hx i
      have := unitBg_Ψ_of_mem (lvTopG d L N₁ m₁ k (rhoSepG d L m₁)) hN2 (unitVec hN2) hx i
      show (unitBg (lvTopG d L N₁ m₁ k (rhoSepG d L m₁)) hN2 (unitVec hN2)).Ψ x i = _
      rw [this]; simp
    · intro x hx i
      have := unitBg_h_of_mem (lvTopG d L N₁ m₁ k (rhoSepG d L m₁)) hN2 (unitVec hN2) hx i
      show (unitBg (lvTopG d L N₁ m₁ k (rhoSepG d L m₁)) hN2 (unitVec hN2)).h x i = _
      rw [this]; simp
  have hDA0 : 2 * εU ≤ 1 / (8 * (K0 d L κ0 + 1) ^ 3 * c1 d L *
          Real.exp ((2 * κdec - 1 - 2 * κ0) * cG d L + c1 d L + κ' * cG d L)) :=
    (hDA_iff d L (by norm_num) hKc''pos κdec κ0 κ' εU).2
      (amplitude_le hC0 (daT_pos d L (by norm_num) hKc''pos κdec κ0 κ') (3 * p)
        (hβd.trans hbβ))
  have hN3 : L ^ 1 ∣ N₁ := by simpa using hLN
  obtain ⟨hV, hF⟩ := LocalCover.levelLocalCover (N := N) (lvLowG d L N₁ m₁ k (rhoSepG d L m₁))
    hSD (isLevel_lvTopG (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k)
      (ϱ := rhoSepG d L m₁)) (m₀ := 1) le_rfl hN3
  have hBh0 : (0 : ℝ) ≤ 1 + 2 / ν := by positivity
  have e1 : S.betaU = β * (L : ℝ) ^ (k * (d - 2)) :=
    hatStepKG_betaU hN (by omega) k m₁ (rhoSepG d L m₁) hk ν β p₁ δ
  have hδ₁' : Real.sqrt N * (‖((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)‖ *
      (covSupConstC d L N (compWeight L S.a₁ k) κ *
        lvCpsiG d L N κ t (β * (L : ℝ) ^ (k * (d - 2))))) < t := by
    rw [e1]; exact hδ₁
  obtain ⟨B, hB1, hB2⟩ : ∃ B : StepActivityBound S
      (zeroClass d L N₁ m₁ k N (rhoSepG d L m₁)) 0, B.κH = 2 * κdec - 1 ∧ B.εH = 2 * εU := by
    refine stepActivityBound_zeroClass_direct_scaled_uniform S
      (ρ := p₁) (εU := εU) (κ0 := κ0) (κ' := κ') (Kc' := Kc'')
      (Rσ := 2) (R₁ := 2) (r := lvRG d L N κ t (β * (L : ℝ) ^ (k * (d - 2))) p₁) (R := 2)
      (m₀ := 1) (κdec := κdec)
      (κ₀ := κ0) (ρE := 0) (ρM := 0) (Bh := 1 + 2 / ν) (δc := δc)
      (cψ := lvCpsiG d L N κ t (β * (L : ℝ) ^ (k * (d - 2))))
      (jV := fun _ => k) (XV := fun z => LocalCover.cube 1 k (LocalCover.blockSite k z))
      (𝒦XV := fun z => LocalCover.fam 1 (LocalCover.blockSite k z))
      (X₁V := fun z => LocalCover.nbhdF 1 (LocalCover.blockSite k z))
      (jF := fun _ => k) (XF := fun s => LocalCover.cube 1 k s.1)
      (𝒦XF := fun s => LocalCover.fam 1 s.1) (X₁F := fun s => LocalCover.nbhdF 1 s.1)
      (τι := PEmpty.{1}) (μι := PEmpty.{1}) (ϱ₁ := fun _ => 0) (ϱ₂ := fun _ => 0)
      (GkE := fun τ => PEmpty.elim τ) (GjE := fun τ => PEmpty.elim τ) (r₀ := 0) (δ₃ := 0)
      (δfl := 0) (X₀E := fun _ => ∅) (X₁E := fun _ => ∅) (jE := fun _ => 0) (XE := fun _ => ∅)
      (𝒦XE := fun _ => ∅) (EbE := fun _ => 0) (EE := fun _ _ => 0)
      (ϱ₁M := fun _ => 0) (ϱ₂M := fun _ => 0)
      (GkM := fun τ => PEmpty.elim τ) (GjM := fun τ => PEmpty.elim τ)
      (X₀M := fun _ => ∅) (X₁M := fun _ => ∅) (jM := fun _ => 0) (XM := fun _ => ∅)
      (𝒦XM := fun _ => ∅) (EbM := fun _ => 0) (EM := fun _ _ => 0)
      (hC := hC) (hconn := hatConn_lvTopG hL) (hrow := rowInHat_lvG hk hSD)
      (hκ₀ := hκ0) (hκdec := hκdec) (hκ := by exact_mod_cast hκ) (h1 := h1)
      (hR₁ := by norm_num) (hr := hr0) (hβ := hβ1) (hL3 := hL)
      (hak := (compWeight_one_mem hL hk).2) (hk := hk) (hG := isLevel_lvLowG hk)
      (hcψ := hcψ0.le) (hMX := hMX) (hdm := hdm) (hα := hα) (hsmX := hsmX) (hδ₁ := hδ₁')
      (ha₁ := one_pos) (H := hHB) (hc7 := hc7) (hR := le_rfl) (hRs := g1) (hsmall := g2)
      (hnum := g3) (hnum' := g4) (hsm := g5)
      (hcovV := fun z => (hV z).1) (hX₁V := fun z => (hV z).2.1)
      (hoptV := fun z => (hV z).2.2.1) (hΔV := fun z => (hV z).2.2.2.1)
      (hlogV := fun _ => hlog) (hZV := fun z => (hV z).2.2.2.2.1)
      (hmarV := fun z => (hV z).2.2.2.2.2.1)
      (𝒯E := (∅ : Finset PEmpty.{1}))
      (hBE := fun τ hτ => absurd hτ (by simp)) (hFE := fun τ hτ => absurd hτ (by simp))
      (hcovE := fun τ hτ => absurd hτ (by simp)) (hX₁E := fun τ hτ => absurd hτ (by simp))
      (hoptE := fun τ hτ => absurd hτ (by simp)) (hlogE := fun τ hτ => absurd hτ (by simp))
      (hEbE := fun τ hτ => absurd hτ (by simp)) (hEanE := fun τ hτ => absurd hτ (by simp))
      (hEbdE := fun τ hτ => absurd hτ (by simp))
      (hcovF := fun s => (hF s).1) (hX₁F := fun s => (hF s).2.1)
      (hoptF := fun s => (hF s).2.2.1) (hΔF := fun s => (hF s).2.2.2.1)
      (hlogF := fun _ => hlog) (hyF := fun s => (hF s).2.2.2.2)
      (𝒯M := (∅ : Finset PEmpty.{1})) (ys := fun τ => PEmpty.elim τ)
      (is := fun τ => PEmpty.elim τ)
      (hys := fun τ hτ => absurd hτ (by simp))
      (hBM := fun τ hτ => absurd hτ (by simp)) (hFM := fun τ hτ => absurd hτ (by simp))
      (hcovM := fun τ hτ => absurd hτ (by simp)) (hX₁M := fun τ hτ => absurd hτ (by simp))
      (hoptM := fun τ hτ => absurd hτ (by simp)) (hlogM := fun τ hτ => absurd hτ (by simp))
      (hEbM := fun τ hτ => absurd hτ (by simp)) (hEanM := fun τ hτ => absurd hτ (by simp))
      (hEbdM := fun τ hτ => absurd hτ (by simp))
      (rE := fun τ => PEmpty.elim τ) (hrE := fun τ hτ => absurd hτ (by simp))
      (hρE0 := le_rfl) (hρE := fun x => by simp) (hρM0 := le_rfl) (hρM := fun p => by simp)
      (hBh0 := hBh0) (hBh := hBh) (hZν := fun z => (hV z).2.2.2.2.2.2)
      (hRσ := by norm_num) (hc := hc) (hD := hD) (hN := hN3) (hp := hp0) (hpρ := le_rfl)
      (hεpos := hεpos) (hεb := ?hεb) (hκE := hκE) (hKc := le_rfl) (hκ' := hκ'0) (hκa := hκa')
      (hDA := hDA0) (R0 := R0) (hlt := hlt)
      (hbase := StepSetting.baseDomain_of_rayData R0) (hRσ1 := by norm_num)
      (h𝒯E := rfl) (h𝒯M := rfl)
    case hεb =>
      rw [e1]
      simp only [hPdef, hKdef, hQdef] at hamp2
      simp only [norm_zero, zero_mul, add_zero, zero_div, mul_zero]
      exact hamp2
  refine ⟨B, hB1, ?_, hκa', 3 / 2 * κdec, rfl, by linarith, by rw [hκ'def, min_self]; linarith⟩
  rw [hB2, hεU]
  have : 2 * (C0 * (Real.log (β * (L : ℝ) ^ (k * (d - 2)))) ^ (3 * p) /
      Real.sqrt (β * (L : ℝ) ^ (k * (d - 2)))) =
      2 * C0 * (Real.log (β * (L : ℝ) ^ (k * (d - 2)))) ^ (3 * p) /
        Real.sqrt (β * (L : ℝ) ^ (k * (d - 2))) := by ring
  rw [this]

/-- **The zero-class activity bound at every scale and on every torus, general `d`, `L`, `N`, for
every cutoff up to the cutoff of the papers.**  With `κ₀ = a_Ent + 1`,
`κ_dec = 100 (κ₀ + c₁ + 10)`, `κ' = (3/2) κ_dec + κ₀ + 1`: there are `m₁, t, δ, β₀, C`
(`β₀ ≥ 2`, `C > 0`) such that for every scale `k ≥ 1`, every torus parameter `N₁` with `L ∣ N₁`,
`5 < N₁`, every mass `0 < ν` with `ν · L^{2(k+1)} ≤ 1`, every `β ≥ β₀` and every cutoff
`0 < p₁ ≤ A₁ (log b)^p`, `b = β L^{k(d-2)}`, the zero class at
`hatStepKG k m₁ (rhoSepG d L m₁) hk ν β p₁ δ` has a step activity bound with `κ_H = 2 κ_dec - 1`
and prefactor at most `C (log b)^{3p}/√b`; the rate relation `κ' + 3κ₀ + c₁ + 3/2 ≤ 2 κ_dec - 1`
holds, and the output rate `κ_out = (3/2) κ_dec` satisfies `κ_dec ≤ κ_out ≤ min κ' κ' - κ₀ - 1`.
The constants do not depend on `k`, `N₁`, `ν`. -/
theorem stepActivityBound_zeroClass_direct_physical_scale_cutoff_general {d L N : ℕ} [NeZero L]
    (hd : 3 ≤ d) (hL : 3 ≤ L) (hN : 2 ≤ N) {A₁ : ℝ} (hA : 0 < A₁) (p : ℕ)
    {κ0 κdec κ' : ℝ} (hκ0def : κ0 = aEnt d L + 1) (hκdecdef : κdec = 100 * (κ0 + c1 d L + 10))
    (hκ'def : κ' = 3 / 2 * κdec + κ0 + 1) :
    ∃ (m₁ : ℕ) (t δ β₀ C : ℝ), 2 ≤ β₀ ∧ 0 < C ∧ 0 < t ∧ 0 < δ ∧
      ∀ (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁], L ∣ N₁ → 5 < N₁ →
      ∀ ν : ℝ, 0 < ν → ν * (L : ℝ) ^ (2 * (k + 1)) ≤ 1 → ∀ β : ℝ, β₀ ≤ β →
      ∀ p₁ : ℝ, 0 < p₁ → p₁ ≤ pLog A₁ p (β * (L : ℝ) ^ (k * (d - 2))) →
        ∃ B : StepActivityBound
            (hatStepKG (d := d) (L := L) (N₁ := N₁) hN k m₁ (rhoSepG d L m₁) hk ν β p₁ δ)
            (zeroClass d L N₁ m₁ k N (rhoSepG d L m₁)) 0,
          B.κH = 2 * κdec - 1 ∧
          B.εH ≤ C * (Real.log (β * (L : ℝ) ^ (k * (d - 2)))) ^ (3 * p) /
            Real.sqrt (β * (L : ℝ) ^ (k * (d - 2))) ∧
          κ' + 3 * κ0 + c1 d L + 3 / 2 ≤ 2 * κdec - 1 ∧
          ∃ κout : ℝ, κout = 3 / 2 * κdec ∧ κdec ≤ κout ∧ κout ≤ min κ' κ' - κ0 - 1 := by
  obtain ⟨m₁, t, δ, β₀, C, -, -, -, -, -, -, hβ₀, hC, ht, hδ, -, -, -, -, -, -, -, h⟩ :=
    stepActivityBound_zeroClass_direct_physical_scale_cutoff_tower_general hd hL hN 0 hA p hκ0def
      hκdecdef hκ'def
  exact ⟨m₁, t, δ, β₀, C, hβ₀, hC, ht, hδ, h⟩

/-- **The zero-class activity bound at every scale and on every torus, general `d`, `L`, `N`, with
the cutoff of the papers** `p₁ = A₁ (log b)^p`, `b = β L^{k(d-2)}`. -/
theorem stepActivityBound_zeroClass_direct_physical_scale_general {d L N : ℕ} [NeZero L]
    (hd : 3 ≤ d) (hL : 3 ≤ L) (hN : 2 ≤ N) {A₁ : ℝ} (hA : 0 < A₁) (p : ℕ)
    {κ0 κdec κ' : ℝ} (hκ0def : κ0 = aEnt d L + 1) (hκdecdef : κdec = 100 * (κ0 + c1 d L + 10))
    (hκ'def : κ' = 3 / 2 * κdec + κ0 + 1) :
    ∃ (m₁ : ℕ) (t δ β₀ C : ℝ), 2 ≤ β₀ ∧ 0 < C ∧ 0 < t ∧ 0 < δ ∧
      ∀ (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁], L ∣ N₁ → 5 < N₁ →
      ∀ ν : ℝ, 0 < ν → ν * (L : ℝ) ^ (2 * (k + 1)) ≤ 1 → ∀ β : ℝ, β₀ ≤ β →
        ∃ B : StepActivityBound
            (hatStepKG (d := d) (L := L) (N₁ := N₁) hN k m₁ (rhoSepG d L m₁) hk ν β
              (pLog A₁ p (β * (L : ℝ) ^ (k * (d - 2)))) δ)
            (zeroClass d L N₁ m₁ k N (rhoSepG d L m₁)) 0,
          B.κH = 2 * κdec - 1 ∧
          B.εH ≤ C * (Real.log (β * (L : ℝ) ^ (k * (d - 2)))) ^ (3 * p) /
            Real.sqrt (β * (L : ℝ) ^ (k * (d - 2))) ∧
          κ' + 3 * κ0 + c1 d L + 3 / 2 ≤ 2 * κdec - 1 ∧
          ∃ κout : ℝ, κout = 3 / 2 * κdec ∧ κdec ≤ κout ∧ κout ≤ min κ' κ' - κ0 - 1 := by
  obtain ⟨m₁, t, δ, β₀, C, hβ₀, hC, ht, hδ, h⟩ :=
    stepActivityBound_zeroClass_direct_physical_scale_cutoff_general hd hL hN hA p hκ0def
      hκdecdef hκ'def
  refine ⟨m₁, t, δ, β₀, C, hβ₀, hC, ht, hδ, ?_⟩
  intro k hk N₁ _ h3 hN₁ ν hν0 hν β hβ
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast (by omega : 1 ≤ L)
  have h3k : (1 : ℝ) ≤ (L : ℝ) ^ (k * (d - 2)) := one_le_pow₀ hL1
  have hβ2 : 2 ≤ β := hβ₀.trans hβ
  have hb : 1 < β * (L : ℝ) ^ (k * (d - 2)) :=
    lt_of_lt_of_le (by linarith) (le_mul_of_one_le_right (by linarith) h3k)
  exact h k hk N₁ h3 hN₁ ν hν0 hν β hβ _ (pLog_pos hA p hb) le_rfl

/-- **The same in terms of the running mass**, general `d`, `L`, `N`: for the physical mass
`ν = ν_k L^{-2k}` of a running mass `0 < ν_k ≤ L^{-2}`. -/
theorem stepActivityBound_zeroClass_direct_physical_scale_running_general {d L N : ℕ} [NeZero L]
    (hd : 3 ≤ d) (hL : 3 ≤ L) (hN : 2 ≤ N) {A₁ : ℝ} (hA : 0 < A₁) (p : ℕ)
    {κ0 κdec κ' : ℝ} (hκ0def : κ0 = aEnt d L + 1) (hκdecdef : κdec = 100 * (κ0 + c1 d L + 10))
    (hκ'def : κ' = 3 / 2 * κdec + κ0 + 1) :
    ∃ (m₁ : ℕ) (t δ β₀ C : ℝ), 2 ≤ β₀ ∧ 0 < C ∧ 0 < t ∧ 0 < δ ∧
      ∀ (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁], L ∣ N₁ → 5 < N₁ →
      ∀ νk : ℝ, 0 < νk → νk ≤ (((L : ℕ) : ℝ) ^ 2)⁻¹ → ∀ β : ℝ, β₀ ≤ β →
        ∃ B : StepActivityBound
            (hatStepKG (d := d) (L := L) (N₁ := N₁) hN k m₁ (rhoSepG d L m₁) hk
              (Balaban.SmallField.Def6v2.sfBgMassAt L k νk) β
              (pLog A₁ p (β * (L : ℝ) ^ (k * (d - 2)))) δ)
            (zeroClass d L N₁ m₁ k N (rhoSepG d L m₁)) 0,
          B.κH = 2 * κdec - 1 ∧
          B.εH ≤ C * (Real.log (β * (L : ℝ) ^ (k * (d - 2)))) ^ (3 * p) /
            Real.sqrt (β * (L : ℝ) ^ (k * (d - 2))) ∧
          κ' + 3 * κ0 + c1 d L + 3 / 2 ≤ 2 * κdec - 1 ∧
          ∃ κout : ℝ, κout = 3 / 2 * κdec ∧ κdec ≤ κout ∧ κout ≤ min κ' κ' - κ0 - 1 := by
  obtain ⟨m₁, t, δ, β₀, C, hβ₀, hC, ht, hδ, h⟩ :=
    stepActivityBound_zeroClass_direct_physical_scale_general hd hL hN hA p hκ0def hκdecdef
      hκ'def
  refine ⟨m₁, t, δ, β₀, C, hβ₀, hC, ht, hδ, ?_⟩
  intro k hk N₁ _ h3 hN₁ νk hνk0 hνk β hβ
  have hm := (massLe_iff (L := L) k νk).2 hνk
  have hmass : Balaban.SmallField.Def6v2.sfBgMassAt L k νk * (L : ℝ) ^ (2 * (k + 1)) ≤ 1 := by
    rw [← pow_mul, mul_comm (k + 1) 2] at hm
    simpa using hm
  exact h k hk N₁ h3 hN₁ _ (Balaban.SmallField.Def6v2.physMass_pos (L := L) k hνk0) hmass β hβ

end Balaban.Inhabited
