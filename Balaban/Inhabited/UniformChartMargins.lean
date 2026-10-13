/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.UniformChartRelative
public import Balaban.Inhabited.DetStepScale
public import Balaban.Fluctuation.MarkedDecBall
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

/-!
# The chart ball and the fixed margins of the discs at every scale

At the step `hatStepK k m₁ hk ν β p₁ δ` of every scale `k ≥ 1`, every torus and every mass
`0 ≤ ν` with `ν · 3^{2(k+1)} ≤ 1`:

* `hatStepK_chartBall`: a radius `r_D > 0`, the same for all `β, p₁, δ`, such that every point of
  the subspace `rawSub` within `r_D` of the raw datum of the step lies in `XiCRaw`, and such that
  the mixed neighbourhood (raw sup norm below `r_D`, source within the remaining `ℓ¹` margin of a
  source of the strict `ℓ¹` ball) lies in `physV`;
* `source_supBall_not_subset_l1Ball`: the obstruction to a product sup-norm radius for the source;
* `scale_markedDisc_margin`: the fixed margins `B < t/2` of the fluctuation disc and
  `(9/8)² B ≤ 81 t/128 < t` of the marked disc;
* `scale_markedDisc_mem_flBallLC`: `markedDisc_hatPsiF_mem_flBallLC` at the step with these radii;
* `scale_chart_det_joint`: the chart ball, the margins, the determinant record and the zero-class
  activity bound with the same tower constants.

No scale-uniform datum radius is proved: the radius `r_D` depends on `(k, N₁, m₁, ν, t)`
(`OPEN-RESPONSE-UNIFORM`).  The families over the chart are not constructed here.
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation
  Balaban.Localization Balaban.Localization.LevelPair Balaban.Localization.I5Inhabited
  Balaban.Polymer Balaban.SmallField.Def6 Balaban.Inhabited.LevelStep

section Ball

variable {N₁ : ℕ} [NeZero N₁]

/-- **The chart ball at the general-scale step.**  There is `r_D > 0`, independent of
`β, p₁, δ`, such that (a) every point `q` of `rawSub` with `‖q - rawOf S.D'‖ < r_D` lies in
`XiCRaw`, and (b) for every source `g₀` of the strict `ℓ¹` ball, every `(q, g)` with
`‖q - rawOf S.D'‖ < r_D` and `∑ ‖g - g₀‖₁ < 1 - ‖g₀‖₁` lies in `physV`.  No lower bound uniform in
`k`, `N₁` is claimed. -/
theorem hatStepK_chartBall (k m₁ : ℕ) (hk : 1 ≤ k) {ν : ℝ} (hν0 : 0 ≤ ν)
    (hν : ν * 3 ^ (2 * (k + 1)) ≤ 1) {t : ℝ} (ht0 : 0 < t) :
    ∃ r : ℝ, 0 < r ∧ ∀ β p₁ δ : ℝ,
      (∀ q : ↥(rawSub 2 (hatStepK (N₁ := N₁) k m₁ hk ν β p₁ δ).G'),
        ‖(q : RawData 3 3 (N₁ * 3 ^ m₁) (k + 1) 2) -
            rawOf (hatStepK (N₁ := N₁) k m₁ hk ν β p₁ δ).D'‖ < r →
          (q : RawData 3 3 (N₁ * 3 ^ m₁) (k + 1) 2) ∈
            XiCRaw (hatStepK (N₁ := N₁) k m₁ hk ν β p₁ δ).G' (compWeight 3 1) ν (k + 1) 1 t) ∧
      (∀ g₀ ∈ l1Ball 3 3 N₁ m₁ (k + 1) 2,
        ∀ (q : ↥(rawSub 2 (hatStepK (N₁ := N₁) k m₁ hk ν β p₁ δ).G'))
          (g : CTorus 3 3 N₁ m₁ (k + 1) → Fin 2 → ℂ),
        ‖(q : RawData 3 3 (N₁ * 3 ^ m₁) (k + 1) 2) -
            rawOf (hatStepK (N₁ := N₁) k m₁ hk ν β p₁ δ).D'‖ < r →
        ∑ x, ∑ i, ‖g x i - g₀ x i‖ < 1 - ∑ x, ∑ i, ‖g₀ x i‖ →
          (q, g) ∈ physV (N := 2) (hatStepK (N₁ := N₁) k m₁ hk ν β p₁ δ) 1 ν t) := by
  have hopen := isOpen_preimage_xiCRaw (G := lvTop N₁ m₁ k (rhoSep m₁)) (N := 2)
    (n := k + 1) (σ := 1) (ε := t) (bgHyp_lv (k := k) (ν := ν) m₁ hν0 hν)
  have hmem : (⟨rawOf (unitBg (lvTop N₁ m₁ k (rhoSep m₁)) hN2 (unitVec hN2)),
      rawOf_mem_rawSub _⟩ : ↥(rawSub 2 (lvTop N₁ m₁ k (rhoSep m₁)))) ∈
      (((↑) : ↥(rawSub 2 (lvTop N₁ m₁ k (rhoSep m₁))) →
        RawData 3 3 (N₁ * 3 ^ m₁) (k + 1) 2) ⁻¹'
        XiCRaw (lvTop N₁ m₁ k (rhoSep m₁)) (compWeight 3 1) ν (k + 1) 1 t) :=
    hatStepK_rawOf_mem_xiCRaw k m₁ hk hν0 hν 0 0 0 ht0
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hopen _ hmem
  have key : ∀ q : ↥(rawSub 2 (lvTop N₁ m₁ k (rhoSep m₁))),
        ‖(q : RawData 3 3 (N₁ * 3 ^ m₁) (k + 1) 2) -
            rawOf (unitBg (lvTop N₁ m₁ k (rhoSep m₁)) hN2 (unitVec hN2))‖ < r →
          (q : RawData 3 3 (N₁ * 3 ^ m₁) (k + 1) 2) ∈
            XiCRaw (lvTop N₁ m₁ k (rhoSep m₁)) (compWeight 3 1) ν (k + 1) 1 t := by
    intro q hq
    have : q ∈ Metric.ball
        (⟨rawOf (unitBg (lvTop N₁ m₁ k (rhoSep m₁)) hN2 (unitVec hN2)), rawOf_mem_rawSub _⟩ :
          ↥(rawSub 2 (lvTop N₁ m₁ k (rhoSep m₁)))) r := by
      rw [Metric.mem_ball, dist_eq_norm]
      exact hq
    exact hball this
  refine ⟨r, hr, fun β p₁ δ => ⟨fun q hq => key q hq, ?_⟩⟩
  intro g₀ hg₀ q g hq hg
  refine ⟨key q hq, ?_⟩
  show ∑ x, ∑ i, ‖g x i‖ < 1
  have h1 : ∀ x i, ‖g x i‖ ≤ ‖g x i - g₀ x i‖ + ‖g₀ x i‖ := fun x i => by
    simpa using norm_add_le (g x i - g₀ x i) (g₀ x i)
  calc ∑ x, ∑ i, ‖g x i‖ ≤ ∑ x, ∑ i, (‖g x i - g₀ x i‖ + ‖g₀ x i‖) :=
        Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun i _ => h1 x i
    _ = ∑ x, ∑ i, ‖g x i - g₀ x i‖ + ∑ x, ∑ i, ‖g₀ x i‖ := by
        simp [Finset.sum_add_distrib]
    _ < 1 := by linarith

end Ball

section Source

variable (d L N₁ m₁ K N : ℕ) [NeZero N₁] [NeZero L]

/-- **The product sup-norm obstruction for the source.**  Let `M` be the number of source
coordinates.  The point with all coordinates equal to a real `r ≥ 1/M` has sup norm `r` and is not
in `l1Ball`; hence no sup-norm ball about `0` of radius `> 1/M` lies in `l1Ball`. -/
theorem source_const_not_mem_l1Ball (hN : 0 < N) {r : ℝ} (hr0 : 0 ≤ r)
    (hr : 1 ≤ (Fintype.card (CTorus d L N₁ m₁ K) * N : ℕ) * r) :
    ‖(fun (_ : CTorus d L N₁ m₁ K) (_ : Fin N) => (r : ℂ))‖ = r ∧
      (fun (_ : CTorus d L N₁ m₁ K) (_ : Fin N) => (r : ℂ)) ∉ l1Ball d L N₁ m₁ K N := by
  have hne : Nonempty (CTorus d L N₁ m₁ K) := inferInstance
  have hNf : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  constructor
  · rw [pi_norm_const]
    simp [Real.norm_of_nonneg hr0]
  · intro h
    have : ∑ _x : CTorus d L N₁ m₁ K, ∑ _i : Fin N, ‖(r : ℂ)‖ =
        (Fintype.card (CTorus d L N₁ m₁ K) * N : ℕ) * r := by
      simp [Real.norm_of_nonneg hr0, Finset.sum_const, Finset.card_univ]
      ring
    have h' : ∑ _x : CTorus d L N₁ m₁ K, ∑ _i : Fin N, ‖(r : ℂ)‖ < 1 := h
    linarith

theorem source_supBall_not_subset_l1Ball (hN : 0 < N) {ρ : ℝ}
    (hρ : 1 / ((Fintype.card (CTorus d L N₁ m₁ K) * N : ℕ) : ℝ) < ρ) :
    ¬ Metric.ball (0 : CTorus d L N₁ m₁ K → Fin N → ℂ) ρ ⊆ l1Ball d L N₁ m₁ K N := by
  intro hsub
  set M : ℝ := ((Fintype.card (CTorus d L N₁ m₁ K) * N : ℕ) : ℝ) with hM
  have hM0 : 0 < M := by
    rw [hM]
    have : 0 < Fintype.card (CTorus d L N₁ m₁ K) * N :=
      Nat.mul_pos Fintype.card_pos hN
    exact_mod_cast this
  set r : ℝ := (1 / M + ρ) / 2 with hr
  have hr1 : 1 / M < r := by rw [hr]; linarith
  have hr2 : r < ρ := by rw [hr]; linarith
  have hr0 : 0 ≤ r := by have : 0 < 1 / M := by positivity
                         linarith
  have hMr : 1 ≤ M * r := by
    have := (div_lt_iff₀ hM0).1 hr1
    linarith
  obtain ⟨hnorm, hnot⟩ := source_const_not_mem_l1Ball d L N₁ m₁ K N hN hr0 hMr
  exact hnot (hsub (by rw [mem_ball_zero_iff, hnorm]; exact hr2))

end Source

section Margins

/-- **The fixed margins of the fluctuation disc and of the marked disc, at every scale.**  With
`b = β_k > 0`, `c_ψ = lvCpsi κ t b` and `B = √2 · (|b^{-1/2}| · (C_k · c_ψ))` the quantity of
`scale_C_items` (and of `markedDisc_hatPsiF_mem_flBallLC` with `cc = b^{-1/2}`, `N = 2`):
`B = C_k t / (2 (C_max + 1)) ≤ t C_max / (2 (C_max + 1)) < t / 2`, and with the radii
`R₁ = R_σ = 17/16`, `r = t₁ = 1/16`: `(R₁ + r)(R_σ + t₁) B = (9/8)² B ≤ 81 t / 128 < t`. -/
theorem scale_markedDisc_margin (κ : ℝ) {t : ℝ} (ht : 0 < t) {k : ℕ} (hk : 1 ≤ k) {b : ℝ}
    (hb : 0 < b) :
    Real.sqrt ((2 : ℕ) : ℝ) * (‖((b ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)‖ *
        (covSupConstC 3 3 2 (compWeight 3 (1 : ℝ) k) κ * lvCpsi κ t b)) =
        covSupConstC 3 3 2 (compWeight 3 (1 : ℝ) k) κ * t / (2 * (covSupMaxC 3 3 2 κ + 1)) ∧
    covSupConstC 3 3 2 (compWeight 3 (1 : ℝ) k) κ * t / (2 * (covSupMaxC 3 3 2 κ + 1)) ≤
      t * covSupMaxC 3 3 2 κ / (2 * (covSupMaxC 3 3 2 κ + 1)) ∧
    t * covSupMaxC 3 3 2 κ / (2 * (covSupMaxC 3 3 2 κ + 1)) < t / 2 ∧
    ((17 / 16 : ℝ) + 1 / 16) * ((17 / 16 : ℝ) + 1 / 16) *
      (Real.sqrt ((2 : ℕ) : ℝ) * (‖((b ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)‖ *
        (covSupConstC 3 3 2 (compWeight 3 (1 : ℝ) k) κ * lvCpsi κ t b))) ≤ 81 * t / 128 ∧
    81 * t / 128 < t := by
  have hCm := covSupMaxC_nonneg κ
  have hmem := compWeight_three_mem hk
  have hC0 : 0 ≤ covSupConstC 3 3 2 (compWeight 3 (1 : ℝ) k) κ :=
    covSupConstC_nonneg (by norm_num) (by norm_num) (by linarith [hmem.1]) κ
  have hCle : covSupConstC 3 3 2 (compWeight 3 (1 : ℝ) k) κ ≤ covSupMaxC 3 3 2 κ :=
    covSupConstC_le_covSupMaxC (by norm_num) (by norm_num) κ hmem
  have hT0 : 0 < Real.sqrt b := Real.sqrt_pos.2 hb
  have e : b ^ (-(1 / 2 : ℝ)) = (Real.sqrt b)⁻¹ := by
    rw [Real.rpow_neg hb.le, ← Real.sqrt_eq_rpow]
  have hn : ‖((b ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)‖ = (Real.sqrt b)⁻¹ := by
    rw [Complex.norm_real, Real.norm_of_nonneg (by positivity), e]
  have h1 : Real.sqrt ((2 : ℕ) : ℝ) * (‖((b ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)‖ *
        (covSupConstC 3 3 2 (compWeight 3 (1 : ℝ) k) κ * lvCpsi κ t b)) =
        covSupConstC 3 3 2 (compWeight 3 (1 : ℝ) k) κ * t / (2 * (covSupMaxC 3 3 2 κ + 1)) := by
    rw [hn]
    unfold lvCpsi
    have : Real.sqrt ((2 : ℕ) : ℝ) ≠ 0 := by positivity
    field_simp
  have hD : 0 < 2 * (covSupMaxC 3 3 2 κ + 1) := by positivity
  have h2 : covSupConstC 3 3 2 (compWeight 3 (1 : ℝ) k) κ * t / (2 * (covSupMaxC 3 3 2 κ + 1)) ≤
      t * covSupMaxC 3 3 2 κ / (2 * (covSupMaxC 3 3 2 κ + 1)) := by
    apply div_le_div_of_nonneg_right _ hD.le
    nlinarith
  have h3 : t * covSupMaxC 3 3 2 κ / (2 * (covSupMaxC 3 3 2 κ + 1)) < t / 2 := by
    rw [div_lt_div_iff₀ hD (by norm_num)]
    nlinarith
  have h4 : 81 * t / 128 < t := by linarith
  refine ⟨h1, h2, h3, ?_, h4⟩
  rw [h1]
  have : ((17 / 16 : ℝ) + 1 / 16) * ((17 / 16 : ℝ) + 1 / 16) = 81 / 64 := by norm_num
  rw [this]
  have hq : covSupConstC 3 3 2 (compWeight 3 (1 : ℝ) k) κ * t / (2 * (covSupMaxC 3 3 2 κ + 1)) ≤
      t / 2 := (h2.trans h3.le)
  linarith

end Margins

section Marked

/-- **`markedDisc_hatPsiF_mem_flBallLC` at every scale with the fixed radii.**  With the tower
constants `m₁, BG, κ, t` of `tower_core_rates` (`N = 2`), for every scale, torus, mass and `β > 0`
the masked tangent `(ρ + τ) • markedHatPsiF …` lies in `FlBallLC (lvLow …) t` for `|u| < 17/16`,
`|w| < 1/16`, `|ρ| < 17/16`, `|τ| ≤ 1/16`, `cc = β_k^{-1/2}`, every chart datum `D` of `Ξ^c(·;1,t)`,
every `ψ̂` with `|ψ̂| ≤ c_ψ`, and every `F₁` identifying the decoupled background.  The hypotheses
that stay explicit are the datum premises: the identification `hF₁` of `F₁` (the definition of the
decoupled-background map), the bound on `s`, `XiCData`, and `|ψ̂| ≤ c_ψ`; `FlCore`, the radius
premise and the numerical premises are discharged. -/
theorem scale_markedDisc_mem_flBallLC :
    ∃ (m₁ : ℕ) (BG κ t : ℝ), 4 ≤ m₁ ∧ 0 < t ∧
      ∀ (k : ℕ), 1 ≤ k → ∀ (N₁ : ℕ) [NeZero N₁], 5 < N₁ →
      ∀ ν : ℝ, 0 ≤ ν → ν * 3 ^ (2 * (k + 1)) ≤ 1 → ∀ β : ℝ, 0 < β →
      ∀ F₁ : DecParams (lvTop N₁ m₁ k (rhoSep m₁)) × RawData 3 3 (N₁ * 3 ^ m₁) (k + 1) 2 →
          ((lvTop N₁ m₁ k (rhoSep m₁)).Ω 1 × Fin 2 → ℂ) × ((lvTop N₁ m₁ k (rhoSep m₁)).Ω 1 → ℂ),
      (∀ (s : DecParams (lvTop N₁ m₁ k (rhoSep m₁))) (D : BgData (lvTop N₁ m₁ k (rhoSep m₁)) 2),
        (∀ P, ‖s P‖ < Real.exp κ) →
        InUnionDomainC (lvTop N₁ m₁ k (rhoSep m₁)) (bgC0 3 3 2) (c7 3 3 2 BG κ) ν D →
        ∀ (φ : (lvTop N₁ m₁ k (rhoSep m₁)).Ω 1 × Fin 2 → ℂ)
          (α : (lvTop N₁ m₁ k (rhoSep m₁)).Ω 1 → ℂ),
        IsDecBg (lvTop N₁ m₁ k (rhoSep m₁)) (compWeight 3 1) ν (rho4 3 3 2 BG κ) s D φ α →
          F₁ (s, rawOf D) = (φ, α)) →
      ∀ (s : DecParams (lvTop N₁ m₁ k (rhoSep m₁))), (∀ P, ‖s P‖ < Real.exp κ) →
      ∀ D : BgData (lvTop N₁ m₁ k (rhoSep m₁)) 2,
        XiCData (lvTop N₁ m₁ k (rhoSep m₁)) (compWeight 3 1) ν (k + 1) 1 t D →
      ∀ ψh : unitPts (lvTop N₁ m₁ k (rhoSep m₁)) × Fin 2 → ℂ,
        (∀ p, ‖ψh p‖ ≤ lvCpsi κ t (β * 3 ^ k)) →
      ∀ (Z : Finset (unitPts (lvTop N₁ m₁ k (rhoSep m₁)))) (u w ρ τ : ℂ),
        ‖u‖ < 17 / 16 → ‖w‖ < 1 / 16 → ‖ρ‖ < 17 / 16 → ‖τ‖ ≤ 1 / 16 →
        (ρ + τ) • markedHatPsiF 1 ν (isLevel_lvTop (N₁ := N₁) (m₁ := m₁) (k := k) (ϱ := rhoSep m₁))
          (((β * 3 ^ k) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) F₁ Z u w s (rawOf D) ψh ∈
          FlBallLC (lvLow N₁ m₁ k (rhoSep m₁)) t := by
  classical
  have hc1 := one_le_c1 3 3
  have hent := aEnt_nonneg 3 3
  obtain ⟨m₁, c, BG, κ, t, c₂, BG₂, δc, h4, ht0, ⟨hC₀⟩, hκ0, hκdec, hκ, h1, hlog, hc7,
    hMX, hdm, hα, hsmX, -⟩ :=
    tower_core_rates 2 (κ0 := aEnt 3 3 + 1) (κdec := 3 * (aEnt 3 3 + 1) + c1 3 3 + 5) le_rfl
      le_rfl
  refine ⟨m₁, BG, κ, t, h4, ht0, ?_⟩
  intro k hk N₁ _ hN ν hν0 hν β hβ F₁ hF₁ s hs D hD ψh hψh Z u w ρ τ hu hw hρ hτ
  have hHB := bgHyp_lv (k := k) (ν := ν) m₁ hν0 hν
  have hC : FlCore 2 (lvTop N₁ m₁ k (rhoSep m₁)) (lvLow N₁ m₁ k (rhoSep m₁)) 1 ν c BG κ t
      (levelKc 3 3) (Cchi 3 3) c₂ BG₂ t :=
    flCore_level_transfer hC₀ (dgSetting_lv h4 hN hν0 hν) (opSetting_lv h4 hN hν0 hν)
      (isLevel_lvLow hk) isLevel_lvTop hHB
  have hb : 0 < β * 3 ^ k := by positivity
  obtain ⟨h1', -, -, h4', -⟩ := scale_markedDisc_margin κ ht0 hk hb
  have hcψ : 0 ≤ lvCpsi κ t (β * 3 ^ k) := by
    unfold lvCpsi
    have := covSupMaxC_nonneg κ
    positivity
  have hB : 0 ≤ Real.sqrt ((2 : ℕ) : ℝ) * (‖(((β * 3 ^ k) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)‖ *
      (covSupConstC 3 3 2 (compWeight 3 (1 : ℝ) k) κ * lvCpsi κ t (β * 3 ^ k))) := by
    have hmem := compWeight_three_mem hk
    have hC0 : 0 ≤ covSupConstC 3 3 2 (compWeight 3 (1 : ℝ) k) κ :=
      covSupConstC_nonneg (by norm_num) (by norm_num) (by linarith [hmem.1]) κ
    positivity
  have hrad : ((17 / 16 : ℝ) + 1 / 16) * ((17 / 16 : ℝ) + 1 / 16) *
      (Real.sqrt ((2 : ℕ) : ℝ) * (‖(((β * 3 ^ k) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)‖ *
        (covSupConstC 3 3 2 (compWeight 3 (1 : ℝ) k) κ * lvCpsi κ t (β * 3 ^ k)))) < t :=
    lt_of_le_of_lt h4' (scale_markedDisc_margin κ ht0 hk hb).2.2.2.2
  exact markedDisc_hatPsiF_mem_flBallLC hC hk (isLevel_lvLow hk) isLevel_lvTop _ hcψ hMX hdm hα
    hsmX hF₁ hs hD hψh Z hB hrad hu hw hρ hτ

end Marked

section Joint

open Classical in
/-- **The chart ball, the fixed margins, the determinant record and the zero-class activity bound
with the same tower constants.**  With `κ₀ = a_Ent + 1`, `κ_dec = 100 (κ₀ + c₁ + 10)`,
`κ' = (3/2) κ_dec + κ₀ + 1`: there are `m₁, t, δ, β₀, C, BG, κ` (chosen before the scale) with
`(detDeg 3 3 + 1)² · 2 e^{-κ} < 1` such that for every scale, torus `3 ∣ N₁`, `5 < N₁`, mass
`0 < ν`, `ν 3^{2(k+1)} ≤ 1`, `β ≥ β₀` and `0 < p₁ ≤ A₁ (log β_k)^p`, at `hatStepK k m₁ hk ν β p₁ δ`:

* the chart ball of `hatStepK_chartBall` (the radius `r_D` depends on `(k, N₁, ν)` only, among
  the data after `m₁, t`);
* the margins of `scale_markedDisc_margin`, for the quantity `B` with `b = S.betaU`;
* the conclusions of `stepActivityBound_detExpansionLocC_scale`, word for word.

`FlCore` and the other premises of `scale_markedDisc_mem_flBallLC` are not shared: that theorem
runs `tower_core_rates` on its own (the witnesses of an existential theorem cannot be compared). -/
theorem scale_chart_det_joint {A₁ : ℝ} (hA : 0 < A₁) (p : ℕ)
    {κ0 κdec κ' : ℝ} (hκ0def : κ0 = aEnt 3 3 + 1) (hκdecdef : κdec = 100 * (κ0 + c1 3 3 + 10))
    (hκ'def : κ' = 3 / 2 * κdec + κ0 + 1) :
    ∃ (m₁ : ℕ) (t δ β₀ C BG κ : ℝ), 2 ≤ β₀ ∧ 0 < C ∧ 0 < t ∧ 0 < δ ∧
      ((detDeg 3 3 + 1 : ℕ) : ℝ) ^ 2 * (2 / Real.exp κ) < 1 ∧
      κ' ≤ (κ - Real.log 2 - 2 * Real.log ((detDeg 3 3 + 1 : ℕ) : ℝ)) /
        (2 * ((3 : ℕ) : ℝ) * ((3 : ℕ) : ℝ)) ∧
      ∀ (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁], 3 ∣ N₁ → 5 < N₁ →
      ∀ ν : ℝ, 0 < ν → ν * 3 ^ (2 * (k + 1)) ≤ 1 → ∀ β : ℝ, β₀ ≤ β →
      ∀ p₁ : ℝ, 0 < p₁ → p₁ ≤ pLog A₁ p (β * 3 ^ k) →
        (∃ r : ℝ, 0 < r ∧
          (∀ q : ↥(rawSub 2 (hatStepK (N₁ := N₁) k m₁ hk ν β p₁ δ).G'),
            ‖(q : RawData 3 3 (N₁ * 3 ^ m₁) (k + 1) 2) -
                rawOf (hatStepK (N₁ := N₁) k m₁ hk ν β p₁ δ).D'‖ < r →
              (q : RawData 3 3 (N₁ * 3 ^ m₁) (k + 1) 2) ∈
                XiCRaw (hatStepK (N₁ := N₁) k m₁ hk ν β p₁ δ).G' (compWeight 3 1) ν (k + 1) 1
                  t) ∧
          (∀ g₀ ∈ l1Ball 3 3 N₁ m₁ (k + 1) 2,
            ∀ (q : ↥(rawSub 2 (hatStepK (N₁ := N₁) k m₁ hk ν β p₁ δ).G'))
              (g : CTorus 3 3 N₁ m₁ (k + 1) → Fin 2 → ℂ),
            ‖(q : RawData 3 3 (N₁ * 3 ^ m₁) (k + 1) 2) -
                rawOf (hatStepK (N₁ := N₁) k m₁ hk ν β p₁ δ).D'‖ < r →
            ∑ x, ∑ i, ‖g x i - g₀ x i‖ < 1 - ∑ x, ∑ i, ‖g₀ x i‖ →
              (q, g) ∈ physV (N := 2) (hatStepK (N₁ := N₁) k m₁ hk ν β p₁ δ) 1 ν t)) ∧
        (Real.sqrt ((2 : ℕ) : ℝ) *
            (‖(((hatStepK (N₁ := N₁) k m₁ hk ν β p₁ δ).betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)‖ *
              (covSupConstC 3 3 2 (compWeight 3 (1 : ℝ) k) κ * lvCpsi κ t (β * 3 ^ k))) ≤
            t * covSupMaxC 3 3 2 κ / (2 * (covSupMaxC 3 3 2 κ + 1)) ∧
          t * covSupMaxC 3 3 2 κ / (2 * (covSupMaxC 3 3 2 κ + 1)) < t / 2 ∧
          ((17 / 16 : ℝ) + 1 / 16) * ((17 / 16 : ℝ) + 1 / 16) *
            (Real.sqrt ((2 : ℕ) : ℝ) *
              (‖(((hatStepK (N₁ := N₁) k m₁ hk ν β p₁ δ).betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)‖ *
                (covSupConstC 3 3 2 (compWeight 3 (1 : ℝ) k) κ *
                  lvCpsi κ t (β * 3 ^ k)))) ≤ 81 * t / 128 ∧
          81 * t / 128 < t) ∧
        (∃ B : StepActivityBound (hatStepK (N₁ := N₁) k m₁ hk ν β p₁ δ)
            (zeroClass 3 3 N₁ m₁ k 2 (rhoSep m₁)) 0,
          B.κH = 2 * κdec - 1 ∧
          B.εH ≤ C * (Real.log (β * 3 ^ k)) ^ (3 * p) / Real.sqrt (β * 3 ^ k) ∧
          κ' + 3 * κ0 + c1 3 3 + 3 / 2 ≤ 2 * κdec - 1 ∧
          ∃ κout : ℝ, κout = 3 / 2 * κdec ∧ κdec ≤ κout ∧ κout ≤ min κ' κ' - κ0 - 1) ∧
        XiCData (hatStepK (N₁ := N₁) k m₁ hk ν β p₁ δ).G' (compWeight 3 1) ν (k + 1) 1 t
            (hatStepK (N₁ := N₁) k m₁ hk ν β p₁ δ).D' ∧
          ∀ z, ∃ E : DetExpansionLocC (hatStepK (N₁ := N₁) k m₁ hk ν β p₁ δ) 1 z t
              ((κ - Real.log 2 - 2 * Real.log ((detDeg 3 3 + 1 : ℕ) : ℝ)) /
                (2 * ((3 : ℕ) : ℝ) * ((3 : ℕ) : ℝ)))
              (((3 : ℕ) : ℝ) ^ 3 * ((1 / 2 : ℝ) * (2 : ℕ) * covBLogMax 3 3 κ /
                (1 - ((detDeg 3 3 + 1 : ℕ) : ℝ) ^ 2 * (2 / Real.exp κ)))),
            ∀ D T, E.term D T = ∑ y ∈ (hatStepK (N₁ := N₁) k m₁ hk ν β p₁ δ).blockU z,
              detActivityBg 1 (compWeight 3 1) 1 ν (rho4 3 3 2 BG κ) D y T := by
  obtain ⟨m₁, t, δ, β₀, C, BG, κ, h2, hC, ht, hδ, hz, hκ', H⟩ :=
    stepActivityBound_detExpansionLocC_scale hA p hκ0def hκdecdef hκ'def
  refine ⟨m₁, t, δ, β₀, C, BG, κ, h2, hC, ht, hδ, hz, hκ', ?_⟩
  intro k hk N₁ _ h3N hN ν hν0 hν β hβ p₁ hp0 hp₁
  obtain ⟨hact, hXi, hdet⟩ := H k hk N₁ h3N hN ν hν0 hν β hβ p₁ hp0 hp₁
  have hβpos : 0 < β := by linarith
  have hb : 0 < β * 3 ^ k := by positivity
  obtain ⟨r, hr, hr'⟩ := hatStepK_chartBall (N₁ := N₁) k m₁ hk hν0.le hν ht
  obtain ⟨-, hm2, hm3, hm4, hm5⟩ := scale_markedDisc_margin κ ht hk hb
  have hm1 := (scale_markedDisc_margin κ ht hk hb).1
  refine ⟨⟨r, hr, (hr' β p₁ δ).1, (hr' β p₁ δ).2⟩, ⟨?_, hm3, ?_, hm5⟩, hact, hXi, hdet⟩
  · rw [hatStepK_betaU, hm1]; exact hm2
  · rw [hatStepK_betaU]; exact hm4

end Joint

section Instance

/-- **The scale hypotheses are satisfiable.**  At `k = 1`, `N₁ = 6`, `ν = 1/81`, `β = β₀ ≥ 2` and
`p₁ = 1` (with `A₁ = 1`, `p = 0`, so the cutoff is `1`) the quantified hypotheses of
`scale_chart_det_joint` hold. -/
theorem scale_hypotheses_k1_N6 {β₀ : ℝ} (_h : 2 ≤ β₀) :
    3 ∣ 6 ∧ 5 < 6 ∧ (0 : ℝ) < 1 / 81 ∧ (1 / 81 : ℝ) * 3 ^ (2 * (1 + 1)) ≤ 1 ∧ β₀ ≤ β₀ ∧
      (0 : ℝ) < 1 ∧ (1 : ℝ) ≤ pLog 1 0 (β₀ * 3 ^ 1) := by
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, le_rfl, one_pos, ?_⟩
  simp [pLog]

/-- **Non-vacuity at `k = 1`, `N₁ = 6`.**  The constants of `scale_chart_det_joint` exist, and at
the step `hatStepK 1 m₁ _ (1/81) β₀ 1 δ` the chart ball has a positive radius and the zero class has
a step activity bound with `κ_H = 2 κ_dec - 1`. -/
theorem scale_chart_det_joint_instance :
    ∃ (m₁ : ℕ) (t δ β₀ : ℝ), 2 ≤ β₀ ∧ 0 < t ∧ ∃ r : ℝ, 0 < r ∧
      (∀ q : ↥(rawSub 2 (hatStepK (N₁ := 6) 1 m₁ le_rfl (1 / 81) β₀ 1 δ).G'),
        ‖(q : RawData 3 3 (6 * 3 ^ m₁) (1 + 1) 2) -
            rawOf (hatStepK (N₁ := 6) 1 m₁ le_rfl (1 / 81) β₀ 1 δ).D'‖ < r →
          (q : RawData 3 3 (6 * 3 ^ m₁) (1 + 1) 2) ∈
            XiCRaw (hatStepK (N₁ := 6) 1 m₁ le_rfl (1 / 81) β₀ 1 δ).G' (compWeight 3 1) (1 / 81)
              (1 + 1) 1 t) ∧
      ∃ B : StepActivityBound (hatStepK (N₁ := 6) 1 m₁ le_rfl (1 / 81) β₀ 1 δ)
          (zeroClass 3 3 6 m₁ 1 2 (rhoSep m₁)) 0,
        B.κH = 2 * (100 * ((aEnt 3 3 + 1) + c1 3 3 + 10)) - 1 := by
  obtain ⟨m₁, t, δ, β₀, C, BG, κ, h2, -, ht, -, -, -, H⟩ :=
    scale_chart_det_joint (A₁ := 1) one_pos 0 (κ0 := aEnt 3 3 + 1)
      (κdec := 100 * ((aEnt 3 3 + 1) + c1 3 3 + 10))
      (κ' := 3 / 2 * (100 * ((aEnt 3 3 + 1) + c1 3 3 + 10)) + (aEnt 3 3 + 1) + 1)
      rfl rfl rfl
  obtain ⟨h3, h5, hν0, hν, hβ, hp0, hp⟩ := scale_hypotheses_k1_N6 h2
  obtain ⟨⟨r, hr, hball, -⟩, -, ⟨B, hB, -⟩, -⟩ :=
    H 1 le_rfl 6 h3 h5 (1 / 81) hν0 hν β₀ hβ 1 hp0 hp
  exact ⟨m₁, t, δ, β₀, h2, ht, r, hr, hball, B, hB⟩

/-- The obstruction at `d = L = 3`, `N₁ = 6`, `K = 2`, `N = 2`: the sup-norm ball of radius `1`
about `0` is not contained in `l1Ball` (the number of source coordinates is at least `2`). -/
theorem source_supBall_not_subset_l1Ball_instance (m₁ : ℕ) :
    ¬ Metric.ball (0 : CTorus 3 3 6 m₁ 2 → Fin 2 → ℂ) 1 ⊆ l1Ball 3 3 6 m₁ 2 2 := by
  refine source_supBall_not_subset_l1Ball 3 3 6 m₁ 2 2 (by norm_num) ?_
  have hc : 0 < Fintype.card (CTorus 3 3 6 m₁ 2) := Fintype.card_pos
  have : (2 : ℝ) ≤ ((Fintype.card (CTorus 3 3 6 m₁ 2) * 2 : ℕ) : ℝ) := by
    exact_mod_cast (by omega : 2 ≤ Fintype.card (CTorus 3 3 6 m₁ 2) * 2)
  rw [div_lt_one (by linarith)]
  linarith

end Instance

end Balaban.Inhabited
