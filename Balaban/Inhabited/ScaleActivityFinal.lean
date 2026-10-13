/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.LevelRayTower
public import Balaban.Fluctuation.LevelLocalCover
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

/-!
# The zero-class activity bound at every scale and on every torus

`stepActivityBound_zeroClass_direct_physical_rate` is the label-activity bound of the zero class at
the witness step (`k = 1`, `N₁ = 9`, `ν = 1/81`) for all large `β`.  This file proves the same
bound for the step `hatStepK k m₁ hk ν β p₁ δ` (`d = L = 3`, `N = 2`, constant unit block datum)

* at every scale `k ≥ 1`,
* on every torus `CTorus 3 3 N₁ m₁ (k + 1)` with `3 ∣ N₁` and `5 < N₁`,
* for every mass `0 < ν` with `ν · 3^{2(k+1)} ≤ 1` (for the physical mass `ν = ν_k 3^{-2k}` this is
  `ν_k ≤ L^{-2}`, `massLe_iff`),
* for every `β ≥ β₀`,

with `m₁`, `t = δ₁ = ε`, `δ`, `β₀`, `C` and the rates fixed before, and independent of, `k`, `N₁`,
`ν`.  The rates are those of `stepActivityBound_zeroClass_direct_physical_rate`: `κ₀ = a_Ent + 1`,
`κ_dec = 100 (κ₀ + c₁ + 10)`, `κ' = (3/2) κ_dec + κ₀ + 1`.  Write `β_k = β · 3^k`.

* `stepActivityBound_zeroClass_direct_physical_scale_cutoff`: for every cutoff
  `0 < p₁ ≤ A₁ (log β_k)^p`, a step activity bound with `κ_H = 2 κ_dec - 1` and prefactor
  `ε_H ≤ C (log β_k)^{3p}/√β_k`.
* `stepActivityBound_zeroClass_direct_physical_scale`: the case `p₁ = A₁ (log β_k)^p`, the cutoff of
  the papers at the scale.
* `stepActivityBound_zeroClass_direct_physical_scale_running`: the same for the physical mass
  `ν = ν_k 3^{-2k}` of a running mass `0 < ν_k ≤ L^{-2}`.
* `stepActivityBound_zeroClass_direct_physical_rate_of_scale`: at `k = 1`, `N₁ = 9`, `ν = 1/81`
  the step is the landed `hatStep` (`hatStepK_one_nine`, by `rfl`), and the cutoff
  `A₁ (log β)^p ≤ A₁ (log 3β)^p` of the landed theorem is admissible; the general theorem gives the
  statement of `stepActivityBound_zeroClass_direct_physical_rate` word for word (with
  `(log 3β)^{3p}/√(3β) ≤ 2^{3p} (log β)^{3p}/√β` for `β ≥ 3`).

How the hypotheses of `stepActivityBound_zeroClass_direct_scaled_uniform` are met:
the cover hypotheses of the potential and source parts by `LocalCover.levelLocalCover` at the cover
scale `m₀ = 1` (`X₁` is the `5 × 5 × 5` cells of `π_{k+1}` around the cell of the block);
`FlCore` by `flCore_level_transfer` from the numerical tower `tower_core_rates`; `HatConn`,
`RowInHat`, `BgHyp`, the levels by `LevelStepSetting`; the cutoff, radii and `RayData` by
`scale_C_items`; the amplitude by `scale_amp_exists`, with the scale-free bound
`energyConstScaled ≤ L^d C_E` (weights `a_k ≤ 2`); the smallness by `amplitude_le` at `β_k ≥ β`.

Dependence on the scale, the torus and the mass.  No constant of the conclusion depends on `k`,
`N₁` or `ν`.  Inside the proof one constant does: the bound `Bh = 1 + 2/ν` of the datum field
(`hBh_of_xi`).  It multiplies the coefficient `‖c_ν‖ = 0` of the zero class, so it does not enter
the amplitude; but the hypothesis `hBh` of the engine (a bound on the datum field over the data
domain) has to be supplied, and the landed bound `hBh_of_xi` needs `ν > 0`: every condition on the
datum field in the data domains (`InPsiTilde`, `XiBounds`, `XiCBounds`) carries a factor `ν`.  This
is why the mass premise here is `0 < ν` and not `0 ≤ ν`; the cutoff, radius and `RayData`
hypotheses (`scale_C_items`) and the cover hypotheses hold for `0 ≤ ν`.

What is proved: zero class, every scale with `0 < ν`, `ν · 3^{2(k+1)} ≤ 1`, every torus with
`3 ∣ N₁`, `5 < N₁`, constants independent of the scale, the torus and the mass.  What is not
proved: scales with `ν · 3^{2(k+1)} > 1` (massive backgrounds), the mass `ν = 0`, general classes
(nonempty old-energy and observable families), and the output terms of the step.
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation
  Balaban.Localization Balaban.Localization.LevelPair Balaban.Localization.I5Inhabited
  Balaban.Polymer Balaban.SmallField.Def6 Balaban.Inhabited.LevelStep Filter Topology

open Classical in
/-- **The zero-class activity bound at every scale and on every torus, for every cutoff up to the
cutoff of the papers.**  With `κ₀ = a_Ent + 1`, `κ_dec = 100 (κ₀ + c₁ + 10)`,
`κ' = (3/2) κ_dec + κ₀ + 1`: there are `m₁, t, δ, β₀, C` (`β₀ ≥ 2`, `C > 0`) such that for every
scale `k ≥ 1`, every torus parameter `N₁` with `3 ∣ N₁`, `5 < N₁`, every mass `0 < ν` with
`ν · 3^{2(k+1)} ≤ 1`, every `β ≥ β₀` and every cutoff `0 < p₁ ≤ A₁ (log β_k)^p`, `β_k = β · 3^k`,
the zero class at `hatStepK k m₁ hk ν β p₁ δ` has a step activity bound with `κ_H = 2 κ_dec - 1`
and prefactor at most `C (log β_k)^{3p}/√β_k`; the rate relation
`κ' + 3κ₀ + c₁ + 3/2 ≤ 2 κ_dec - 1` holds, and the output rate `κ_out = (3/2) κ_dec` satisfies
`κ_dec ≤ κ_out ≤ min κ' κ' - κ₀ - 1`.  The constants do not depend on `k`, `N₁`, `ν`. -/
theorem stepActivityBound_zeroClass_direct_physical_scale_cutoff {A₁ : ℝ} (hA : 0 < A₁) (p : ℕ)
    {κ0 κdec κ' : ℝ} (hκ0def : κ0 = aEnt 3 3 + 1) (hκdecdef : κdec = 100 * (κ0 + c1 3 3 + 10))
    (hκ'def : κ' = 3 / 2 * κdec + κ0 + 1) :
    ∃ (m₁ : ℕ) (t δ β₀ C : ℝ), 2 ≤ β₀ ∧ 0 < C ∧ 0 < t ∧ 0 < δ ∧
      ∀ (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁], 3 ∣ N₁ → 5 < N₁ →
      ∀ ν : ℝ, 0 < ν → ν * 3 ^ (2 * (k + 1)) ≤ 1 → ∀ β : ℝ, β₀ ≤ β →
      ∀ p₁ : ℝ, 0 < p₁ → p₁ ≤ pLog A₁ p (β * 3 ^ k) →
        ∃ B : StepActivityBound (hatStepK (N₁ := N₁) k m₁ hk ν β p₁ δ)
            (zeroClass 3 3 N₁ m₁ k 2 (rhoSep m₁)) 0,
          B.κH = 2 * κdec - 1 ∧
          B.εH ≤ C * (Real.log (β * 3 ^ k)) ^ (3 * p) / Real.sqrt (β * 3 ^ k) ∧
          κ' + 3 * κ0 + c1 3 3 + 3 / 2 ≤ 2 * κdec - 1 ∧
          ∃ κout : ℝ, κout = 3 / 2 * κdec ∧ κdec ≤ κout ∧ κout ≤ min κ' κ' - κ0 - 1 := by
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
  set Q : ℝ := cK2' 3 3 2 (famConst 3 3 BG₂ κ) with hQdef
  have hQ0 : 0 ≤ Q := (cK2'_pos' hB0).le
  set P : ℝ := 3 * c1 3 3 * (((3 : ℕ) : ℝ) ^ (1 + m₁)) ^ 3 *
    (((3 : ℕ) : ℝ) ^ 3 * ((((2 : ℕ) : ℝ) / 2) * (2 * (1 + Q) ^ 2 +
      (((3 : ℕ) : ℝ) + 1 + rho4 3 3 2 BG κ) * Q ^ 2) * t ^ 2)) with hPdef
  have hP0 : 0 ≤ P := by
    rw [hPdef]; positivity
  set K : ℝ := Q * t with hKdef
  have hK0' : 0 ≤ K := mul_nonneg hQ0 ht0.le
  obtain ⟨β₁, C0, hexpβ₁, hC0, hA'⟩ := scale_amp_exists (A₁ := A₁) (κ := κ) (t := t) hA p ht0
    hP0 hK0'
  set Kc'' : ℝ := K0 3 3 κ0 + 1 with hKc''
  have hKc''pos : 0 < Kc'' := by have := K0_pos 3 3 κ0; rw [hKc'']; linarith
  have hκ'0 : 0 ≤ κ' := by rw [hκ'def]; linarith
  have hκa' : κ' + 3 * κ0 + c1 3 3 + 3 / 2 ≤ 2 * κdec - 1 := by
    rw [hκ'def, hκdecdef]; linarith
  have hxi1 : xiC1 3 * t ≤ 1 := by
    have h1 := hC₀.c7le
    have h2 := c7_le_bgC1 3 3 2 BG κ
    have h3 := bgC1_le_small 3 3 2 (by norm_num)
    linarith
  refine ⟨m₁, t, δ,
    max (max β₀t β₁) (daThreshold C0 (daT 3 3 2 Kc'' κdec κ0 κ') (3 * p)), 2 * C0,
    le_trans hβ₀t ((le_max_left _ _).trans (le_max_left _ _)), by positivity, ht0, hδ, ?_⟩
  intro k hk N₁ _ h3N hN ν hνpos hν β hβ p₁ hp0 hp₁
  have hν0 : 0 ≤ ν := hνpos.le
  have hβt : β₀t ≤ β := le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hβ)
  have hβ₁ : β₁ ≤ β := le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hβ)
  have hβd : daThreshold C0 (daT 3 3 2 Kc'' κdec κ0 κ') (3 * p) ≤ β :=
    le_trans (le_max_right _ _) hβ
  have hβ2 : 2 ≤ β := le_trans hβ₀t hβt
  have hβ0 : 0 < β := by linarith
  have hβ1 : 1 ≤ β := by linarith
  have h3k : (1 : ℝ) ≤ 3 ^ k := one_le_pow₀ (by norm_num)
  have hbβ : β ≤ β * 3 ^ k := le_mul_of_one_le_right hβ0.le h3k
  have hb0 : 0 < β * 3 ^ k := by positivity
  obtain ⟨hcψ0, hr0, hδ₁, hc, hlt, ⟨R0⟩⟩ := hitems k hk N₁ hN ν hν0 hν β hβt p₁ hp0 hp₁
  have hexp : Real.exp 1 ≤ β * 3 ^ k := le_trans hexpβ₁ (hβ₁.trans hbβ)
  have hℓ : 1 ≤ Real.log (β * 3 ^ k) := (Real.le_log_iff_exp_le hb0).2 hexp
  have hamp2 := hA' (β * 3 ^ k) (hβ₁.trans hbβ) β hβ1 p₁ hp0 hp₁
  set εU : ℝ := C0 * (Real.log (β * 3 ^ k)) ^ (3 * p) / Real.sqrt (β * 3 ^ k) with hεU
  have hεpos : 0 < εU := by
    have : 0 < (Real.log (β * 3 ^ k)) ^ (3 * p) := by positivity
    have : 0 < Real.sqrt (β * 3 ^ k) := Real.sqrt_pos.2 hb0
    rw [hεU]; positivity
  set S := hatStepK (N₁ := N₁) k m₁ hk ν β p₁ δ with hS
  have hSD := dgSetting_lv (N₁ := N₁) (k := k) h4 hN hν0 hν
  have hHB := bgHyp_lv (k := k) m₁ hν0 hν
  have hC : FlCore 2 (lvTop N₁ m₁ k (rhoSep m₁)) (lvLow N₁ m₁ k (rhoSep m₁)) 1 ν c BG κ t
      (levelKc 3 3) (Cchi 3 3) c₂ BG₂ t :=
    flCore_level_transfer hC₀ hSD (opSetting_lv h4 hN hν0 hν) (isLevel_lvLow hk) isLevel_lvTop hHB
  have hBh := hBh_of_xi (N := 2) (Gp := lvTop N₁ m₁ k (rhoSep m₁)) hHB hνpos hC.small1
    hC.eps_pos hxi1
  have hD : XiCData S.G' (compWeight 3 1) ν (k + 1) 1 t S.D' := by
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
  have hDA0 : 2 * εU ≤ 1 / (8 * (K0 3 3 κ0 + 1) ^ 3 * c1 3 3 *
          Real.exp ((2 * κdec - 1 - 2 * κ0) * cG 3 3 + c1 3 3 + κ' * cG 3 3)) :=
    (hDA_iff 3 3 (by norm_num) hKc''pos κdec κ0 κ' εU).2
      (amplitude_le hC0 (daT_pos 3 3 (by norm_num) hKc''pos κdec κ0 κ') (3 * p) (hβd.trans hbβ))
  have hN3 : 3 ^ 1 ∣ N₁ := by simpa using h3N
  obtain ⟨hV, hF⟩ := LocalCover.levelLocalCover (N := 2) (lvLow N₁ m₁ k (rhoSep m₁)) hSD
    (isLevel_lvTop (N₁ := N₁) (m₁ := m₁) (k := k) (ϱ := rhoSep m₁)) (m₀ := 1) le_rfl hN3
  have hBh0 : (0 : ℝ) ≤ 1 + 2 / ν := by positivity
  obtain ⟨B, hB1, hB2⟩ : ∃ B : StepActivityBound S (zeroClass 3 3 N₁ m₁ k 2 (rhoSep m₁)) 0,
      B.κH = 2 * κdec - 1 ∧ B.εH = 2 * εU := by
    refine stepActivityBound_zeroClass_direct_scaled_uniform S
      (ρ := p₁) (εU := εU) (κ0 := κ0) (κ' := κ') (Kc' := Kc'')
      (Rσ := 2) (R₁ := 2) (r := lvR κ t (β * 3 ^ k) p₁) (R := 2) (m₀ := 1) (κdec := κdec)
      (κ₀ := κ0) (ρE := 0) (ρM := 0) (Bh := 1 + 2 / ν) (δc := δc) (cψ := lvCpsi κ t (β * 3 ^ k))
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
      (hC := hC) (hconn := hatConn_lvTop) (hrow := rowInHat_lv hk h4 hN hν0 hν)
      (hκ₀ := hκ0) (hκdec := hκdec) (hκ := by exact_mod_cast hκ) (h1 := h1)
      (hR₁ := by norm_num) (hr := hr0) (hβ := hβ1) (hL3 := le_rfl)
      (hak := (compWeight_three_mem hk).2) (hk := hk) (hG := isLevel_lvLow hk)
      (hcψ := hcψ0.le) (hMX := hMX) (hdm := hdm) (hα := hα) (hsmX := hsmX) (hδ₁ := hδ₁)
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
      have e1 : S.betaU = β * 3 ^ k := hatStepK_betaU k m₁ hk ν β p₁ δ
      rw [e1]
      simp only [hPdef, hKdef, hQdef] at hamp2
      simp only [norm_zero, zero_mul, add_zero, zero_div, mul_zero]
      exact hamp2
  refine ⟨B, hB1, ?_, hκa', 3 / 2 * κdec, rfl, by linarith, by rw [hκ'def, min_self]; linarith⟩
  rw [hB2, hεU]
  have : 2 * (C0 * (Real.log (β * 3 ^ k)) ^ (3 * p) / Real.sqrt (β * 3 ^ k)) =
      2 * C0 * (Real.log (β * 3 ^ k)) ^ (3 * p) / Real.sqrt (β * 3 ^ k) := by ring
  rw [this]

/-- **The zero-class activity bound at every scale and on every torus, with the cutoff of the
papers.**  With `κ₀ = a_Ent + 1`, `κ_dec = 100 (κ₀ + c₁ + 10)`, `κ' = (3/2) κ_dec + κ₀ + 1`: there
are `m₁, t, δ, β₀, C` (`β₀ ≥ 2`, `C > 0`) such that for every scale `k ≥ 1`, every torus parameter
`N₁` with `3 ∣ N₁`, `5 < N₁`, every mass `0 < ν` with `ν · 3^{2(k+1)} ≤ 1` and every `β ≥ β₀`, at
the step `hatStepK k m₁ hk ν β p₁ δ` with the cutoff `p₁ = A₁ (log β_k)^p`, `β_k = β · 3^k`, the
zero class has a step activity bound with `κ_H = 2 κ_dec - 1` and prefactor at most
`C (log β_k)^{3p}/√β_k`; the rate relation `κ' + 3κ₀ + c₁ + 3/2 ≤ 2 κ_dec - 1` holds, and the
output rate `κ_out = (3/2) κ_dec` satisfies `κ_dec ≤ κ_out ≤ min κ' κ' - κ₀ - 1`.  The constants
`m₁, t, δ, β₀, C` and the rates do not depend on `k`, `N₁`, `ν`.  The only hypotheses are the size
conditions on `N₁`, the mass premise and `β ≥ β₀`. -/
theorem stepActivityBound_zeroClass_direct_physical_scale {A₁ : ℝ} (hA : 0 < A₁) (p : ℕ)
    {κ0 κdec κ' : ℝ} (hκ0def : κ0 = aEnt 3 3 + 1) (hκdecdef : κdec = 100 * (κ0 + c1 3 3 + 10))
    (hκ'def : κ' = 3 / 2 * κdec + κ0 + 1) :
    ∃ (m₁ : ℕ) (t δ β₀ C : ℝ), 2 ≤ β₀ ∧ 0 < C ∧ 0 < t ∧ 0 < δ ∧
      ∀ (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁], 3 ∣ N₁ → 5 < N₁ →
      ∀ ν : ℝ, 0 < ν → ν * 3 ^ (2 * (k + 1)) ≤ 1 → ∀ β : ℝ, β₀ ≤ β →
        ∃ B : StepActivityBound (hatStepK (N₁ := N₁) k m₁ hk ν β (pLog A₁ p (β * 3 ^ k)) δ)
            (zeroClass 3 3 N₁ m₁ k 2 (rhoSep m₁)) 0,
          B.κH = 2 * κdec - 1 ∧
          B.εH ≤ C * (Real.log (β * 3 ^ k)) ^ (3 * p) / Real.sqrt (β * 3 ^ k) ∧
          κ' + 3 * κ0 + c1 3 3 + 3 / 2 ≤ 2 * κdec - 1 ∧
          ∃ κout : ℝ, κout = 3 / 2 * κdec ∧ κdec ≤ κout ∧ κout ≤ min κ' κ' - κ0 - 1 := by
  obtain ⟨m₁, t, δ, β₀, C, hβ₀, hC, ht, hδ, h⟩ :=
    stepActivityBound_zeroClass_direct_physical_scale_cutoff hA p hκ0def hκdecdef hκ'def
  refine ⟨m₁, t, δ, β₀, C, hβ₀, hC, ht, hδ, ?_⟩
  intro k hk N₁ _ h3 hN ν hν0 hν β hβ
  have h3k : (1 : ℝ) ≤ 3 ^ k := one_le_pow₀ (by norm_num)
  have hβ2 : 2 ≤ β := hβ₀.trans hβ
  have hb : 1 < β * 3 ^ k :=
    lt_of_lt_of_le (by linarith) (le_mul_of_one_le_right (by linarith) h3k)
  exact h k hk N₁ h3 hN ν hν0 hν β hβ _ (pLog_pos hA p hb) le_rfl

/-- **The same in terms of the running mass.**  For the physical mass `ν = ν_k 3^{-2k}` of a running
mass `0 < ν_k ≤ L^{-2} = 1/9`, the mass premise of `stepActivityBound_zeroClass_direct_physical_scale`
holds (`massLe_iff`): the bound holds at every scale `k ≥ 1` with `ν_k ≤ L^{-2}`. -/
theorem stepActivityBound_zeroClass_direct_physical_scale_running {A₁ : ℝ} (hA : 0 < A₁) (p : ℕ)
    {κ0 κdec κ' : ℝ} (hκ0def : κ0 = aEnt 3 3 + 1) (hκdecdef : κdec = 100 * (κ0 + c1 3 3 + 10))
    (hκ'def : κ' = 3 / 2 * κdec + κ0 + 1) :
    ∃ (m₁ : ℕ) (t δ β₀ C : ℝ), 2 ≤ β₀ ∧ 0 < C ∧ 0 < t ∧ 0 < δ ∧
      ∀ (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁], 3 ∣ N₁ → 5 < N₁ →
      ∀ νk : ℝ, 0 < νk → νk ≤ (((3 : ℕ) : ℝ) ^ 2)⁻¹ → ∀ β : ℝ, β₀ ≤ β →
        ∃ B : StepActivityBound (hatStepK (N₁ := N₁) k m₁ hk
              (Balaban.SmallField.Def6v2.sfBgMassAt 3 k νk) β (pLog A₁ p (β * 3 ^ k)) δ)
            (zeroClass 3 3 N₁ m₁ k 2 (rhoSep m₁)) 0,
          B.κH = 2 * κdec - 1 ∧
          B.εH ≤ C * (Real.log (β * 3 ^ k)) ^ (3 * p) / Real.sqrt (β * 3 ^ k) ∧
          κ' + 3 * κ0 + c1 3 3 + 3 / 2 ≤ 2 * κdec - 1 ∧
          ∃ κout : ℝ, κout = 3 / 2 * κdec ∧ κdec ≤ κout ∧ κout ≤ min κ' κ' - κ0 - 1 := by
  obtain ⟨m₁, t, δ, β₀, C, hβ₀, hC, ht, hδ, h⟩ :=
    stepActivityBound_zeroClass_direct_physical_scale hA p hκ0def hκdecdef hκ'def
  refine ⟨m₁, t, δ, β₀, C, hβ₀, hC, ht, hδ, ?_⟩
  intro k hk N₁ _ h3 hN νk hνk0 hνk β hβ
  have hm := (massLe_iff (L := 3) k νk).2 hνk
  have hmass : Balaban.SmallField.Def6v2.sfBgMassAt 3 k νk * 3 ^ (2 * (k + 1)) ≤ 1 := by
    rw [← pow_mul, mul_comm (k + 1) 2] at hm
    simpa using hm
  exact h k hk N₁ h3 hN _ (Balaban.SmallField.Def6v2.physMass_pos (L := 3) k hνk0) hmass β hβ

/-- **Consistency with the landed witness theorem.**  At `k = 1`, `N₁ = 9`, `ν = 1/81` the step
`hatStepK` is the landed `hatStep` (`hatStepK_one_nine`), the cutoff `A₁ (log β)^p` of the landed
theorem is at most `A₁ (log β_1)^p`, `β_1 = 3β`, and `(log 3β)^{3p}/√(3β) ≤ 2^{3p} (log β)^{3p}/√β`
for `β ≥ 3`.  Hence the general theorem implies the statement of
`stepActivityBound_zeroClass_direct_physical_rate`. -/
theorem stepActivityBound_zeroClass_direct_physical_rate_of_scale {A₁ : ℝ} (hA : 0 < A₁) (p : ℕ)
    {κ0 κdec κ' : ℝ} (hκ0def : κ0 = aEnt 3 3 + 1) (hκdecdef : κdec = 100 * (κ0 + c1 3 3 + 10))
    (hκ'def : κ' = 3 / 2 * κdec + κ0 + 1) :
    ∃ (m₁ : ℕ) (t δ β₀ C : ℝ), 2 ≤ β₀ ∧ 0 < C ∧ 0 < t ∧ 0 < δ ∧
      ∀ β : ℝ, β₀ ≤ β →
        ∃ B : StepActivityBound (hatStep m₁ β (pLog A₁ p β) δ)
            (zeroClass 3 3 9 m₁ 1 2 (rhoSep m₁)) 0,
          B.κH = 2 * κdec - 1 ∧ B.εH ≤ C * (Real.log β) ^ (3 * p) / Real.sqrt β ∧
          κ' + 3 * κ0 + c1 3 3 + 3 / 2 ≤ 2 * κdec - 1 ∧
          ∃ κout : ℝ, κout = 3 / 2 * κdec ∧ κdec ≤ κout ∧ κout ≤ min κ' κ' - κ0 - 1 := by
  obtain ⟨m₁, t, δ, β₀, C, hβ₀, hC, ht, hδ, h⟩ :=
    stepActivityBound_zeroClass_direct_physical_scale_cutoff hA p hκ0def hκdecdef hκ'def
  refine ⟨m₁, t, δ, max β₀ 3, 2 ^ (3 * p) * C, le_trans hβ₀ (le_max_left _ _), by positivity,
    ht, hδ, ?_⟩
  intro β hβ
  have hβ3 : 3 ≤ β := (le_max_right _ _).trans hβ
  have hβ0 : 0 < β := by linarith
  have hlog0 : 0 ≤ Real.log β := Real.log_nonneg (by linarith)
  have hlogle : Real.log β ≤ Real.log (β * 3 ^ 1) := Real.log_le_log hβ0 (by linarith)
  have hp₁ : pLog A₁ p β ≤ pLog A₁ p (β * 3 ^ 1) := by
    unfold pLog
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hlog0 hlogle p) hA.le
  obtain ⟨B, hB1, hB2, hB3, hB4⟩ := h 1 le_rfl 9 (by norm_num) (by norm_num) nuW nuW_pos
    (by unfold nuW; norm_num) β ((le_max_left _ _).trans hβ) (pLog A₁ p β)
    (pLog_pos hA p (by linarith)) hp₁
  refine ⟨B, hB1, hB2.trans ?_, hB3, hB4⟩
  have hlog3 : Real.log (β * 3 ^ 1) ≤ 2 * Real.log β := by
    rw [pow_one, Real.log_mul hβ0.ne' (by norm_num)]
    have : Real.log 3 ≤ Real.log β := Real.log_le_log (by norm_num) hβ3
    linarith
  have hsqrt : Real.sqrt β ≤ Real.sqrt (β * 3 ^ 1) := Real.sqrt_le_sqrt (by linarith)
  have hsβ : 0 < Real.sqrt β := Real.sqrt_pos.2 hβ0
  have h1 : (Real.log (β * 3 ^ 1)) ^ (3 * p) ≤ 2 ^ (3 * p) * (Real.log β) ^ (3 * p) := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (hlog0.trans hlogle) hlog3 _
  have hnum0 : 0 ≤ C * (Real.log (β * 3 ^ 1)) ^ (3 * p) :=
    mul_nonneg hC.le (pow_nonneg (hlog0.trans hlogle) _)
  calc C * (Real.log (β * 3 ^ 1)) ^ (3 * p) / Real.sqrt (β * 3 ^ 1)
      ≤ C * (Real.log (β * 3 ^ 1)) ^ (3 * p) / Real.sqrt β :=
        div_le_div_of_nonneg_left hnum0 hsβ hsqrt
    _ ≤ C * (2 ^ (3 * p) * (Real.log β) ^ (3 * p)) / Real.sqrt β :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left h1 hC.le) hsβ.le
    _ = 2 ^ (3 * p) * C * (Real.log β) ^ (3 * p) / Real.sqrt β := by ring

end Balaban.Inhabited
