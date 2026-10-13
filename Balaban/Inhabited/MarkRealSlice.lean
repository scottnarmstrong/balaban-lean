/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.MarkRealDiscSlice
public import Balaban.Inhabited.StepTowerScaleLemmas
public import Balaban.Fluctuation.MarkRealDomain
public import Balaban.Fluctuation.MarkRealRegular
public import Balaban.Fluctuation.StepComplexHat
import Mathlib.Tactic.Linarith

/-!
# MARK-REAL on the whole constant-`h₀` slice (leaf 4)

At a scale of the shared tower `T` (`d = L = 3`, `N = 2`), with `R = 2`, `δ₁ = ε = T.t`,
`R₁ = 17/16`, `t₁ = 1/16`, `r = lvR/4`:

* `StepTower.markReal_hRs`, `markReal_hsmall`, `markReal_hnum`, `markReal_hnum'`, `markReal_hsm`,
  `markReal_hc7`: the numeric premises of the marked derivative identity, read off the fields
  `t_cap`, `bg0_cap`, `cK2_cap`, `cK2'_cap`, `bg1_cap`, `c7_cap` of the tower.
* `StepScaleData.markReal_hD2`, `markReal_ha₁`, `markReal_H`: the datum premises, for every datum
  of the slice.
* `markReal_slice_of_count`: for every datum of the slice, every hat field `‖x‖ ≤ p₁`, every root
  and every real `s ∈ [0,1]`, the one-dimensional identity and the ambient `fderiv` identity in
  the form `E1MarksC.hF` needs.  The only premises left are the common family `𝒴, Ev` with its
  analyticity and block-sum clauses.

The rooted finite sums, the global marks and `E1MarksC` are NOT here.
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Fluctuation Balaban.Multiscale Balaban.Background Balaban.Localization
  Balaban.Localization.I5Inhabited Balaban.Inhabited.LevelStep Balaban.SmallField Set

namespace StepTower

variable {κmin : ℝ} (T : StepTower κmin)

/-- `hRs` at `R = 2`, `δ₁ = T.t`: field `t_cap`. -/
theorem markReal_hRs : (2 : ℝ) * T.t ≤ deltaStar 3 3 2 := T.t_cap

/-- `hsmall` at `R = 2`, `δ₁ = T.t`: field `bg0_cap`. -/
theorem markReal_hsmall : cK2 3 3 2 * ((2 : ℝ) * T.t) < bgC0 3 3 2 / 2 := T.bg0_cap

/-- `hnum` at `δ₁ = T.t`: field `cK2_cap`. -/
theorem markReal_hnum :
    cK2 3 3 2 * T.t ≤ c6' 3 3 2 (famConst 3 3 T.BG₂ T.κ) (gamma1 3 / 8) := T.cK2_cap

/-- `hnum'` at `δ₁ = T.t`: field `cK2'_cap`. -/
theorem markReal_hnum' :
    cK2' 3 3 2 (famConst 3 3 T.BG₂ T.κ) * T.t ≤
      c6' 3 3 2 (famConst 3 3 T.BG₂ T.κ) (gamma1 3 / 8) := T.cK2'_cap

/-- The margin `hsm` of `hreal_level` at `R = 2`, `δ₁ = ε = T.t`: field `bg1_cap`. -/
theorem markReal_hsm :
    2 * (compC4 3 * (bgK1 3 3 2 * (xiC1 3 * T.t))) + 5 * ((2 : ℝ) * T.t) ≤ bgC1 3 3 2 :=
  T.bg1_cap

/-- `hc7`: field `c7_cap`. -/
theorem markReal_hc7 : c7 3 3 2 T.BG T.κ ≤ thm73C3 3 3 2 := T.c7_cap

end StepTower

namespace StepScaleData

variable {κmin : ℝ} {T : StepTower κmin} {k : ℕ} {hk : 1 ≤ k} {N₁ : ℕ} [NeZero N₁]
  {ν β p₁ : ℝ}

/-- `hD2` for every slice datum: `InUnionDomainC` of the datum at radii `(c₀, thm73C2)`, from
`isDecBg_one_of_xiCData` and `c7 ≤ thm73C3 ≤ thm73C2`. -/
theorem markReal_hD2 (hS : StepScaleData T k hk N₁ ν β p₁)
    (D : BgData (T.step k hk N₁ ν β p₁).G' 2)
    (hDh : ∀ y i, D.h y i = ((T.step k hk N₁ ν β p₁).h₀ i : ℂ))
    (hD : XiCData (T.step k hk N₁ ν β p₁).G' (compWeight 3 1) ν (k + 1) 1 T.t D) :
    InUnionDomainC ((T.step k hk N₁ ν β p₁).withDatum D hDh).G' (bgC0 3 3 2) (thm73C2 3 3 2)
      ((T.step k hk N₁ ν β p₁).withDatum D hDh).ν ((T.step k hk N₁ ν β p₁).withDatum D hDh).D' :=
  (isDecBg_one_of_xiCData hS.core hD).2.mono (T.markReal_hc7.trans (thm73C3_le_thm73C2 3 3 2))

/-- `ha₁` for every slice datum. -/
theorem markReal_ha₁ (D : BgData (T.step k hk N₁ ν β p₁).G' 2)
    (hDh : ∀ y i, D.h y i = ((T.step k hk N₁ ν β p₁).h₀ i : ℂ)) :
    0 < ((T.step k hk N₁ ν β p₁).withDatum D hDh).a₁ := one_pos

/-- `H` for every slice datum, for an admissible mass `ν`. -/
theorem markReal_H (hν0 : 0 ≤ ν) (hν : ν * 3 ^ (2 * (k + 1)) ≤ 1)
    (D : BgData (T.step k hk N₁ ν β p₁).G' 2)
    (hDh : ∀ y i, D.h y i = ((T.step k hk N₁ ν β p₁).h₀ i : ℂ)) :
    BgHyp 3 3 (k + 1) (rhoSep T.m₁) ((T.step k hk N₁ ν β p₁).withDatum D hDh).a
      ((T.step k hk N₁ ν β p₁).withDatum D hDh).ν :=
  bgHyp_lv (k := k) T.m₁ hν0 hν

end StepScaleData

/-- **MARK-REAL on the whole slice, conditional on the common family `𝒴, Ev`.**  For a scale of
the shared tower, one family `𝒴, Ev` with analyticity `han` and block sum `hsum` (on the base step;
they do not depend on the datum), every slice datum `D`, every hat field `‖x‖ ≤ p₁`, every root
`z` and every real `s ∈ [0,1]`:
(i) the one-dimensional marked identity at `u = s`, and
(ii) the ambient identity `fderiv Φ₁ (s • shiftUC x) (maskUC z (shiftUC x)) = -β ∑ ∑ deriv …`. -/
theorem markReal_slice_of_count {κmin : ℝ} (T : StepTower κmin) {k : ℕ}
    {hk : 1 ≤ k} {N₁ : ℕ} [NeZero N₁] {ν β p₁ : ℝ}
    (hS : StepScaleData T k hk N₁ ν β p₁) (hp₁ : 0 < p₁) (hν0 : 0 ≤ ν)
    (hν : ν * 3 ^ (2 * (k + 1)) ≤ 1)
    (𝒴 : Torus 3 (N₁ * 3 ^ T.m₁ * 3 ^ (k + 1 - (k + 1))) →
      Finset (Set (CTorus 3 3 N₁ T.m₁ (k + 1))))
    (Ev : Torus 3 (N₁ * 3 ^ T.m₁ * 3 ^ (k + 1 - (k + 1))) → Set (CTorus 3 3 N₁ T.m₁ (k + 1)) →
      RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2 × (CTorus 3 3 N₁ T.m₁ (k + 1) → Fin 2 → ℂ) → ℂ)
    (han : ∀ zb Y, AnalyticOnNhd ℂ (Ev zb Y)
      (XiCRaw (T.step k hk N₁ ν β p₁).G' (T.step k hk N₁ ν β p₁).a (T.step k hk N₁ ν β p₁).ν
        (k + 1) 1 T.t ×ˢ FlBall (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) T.t))
    (hsum : ∀ zb, ∀ Θ ∈ XiCRaw (T.step k hk N₁ ν β p₁).G' (T.step k hk N₁ ν β p₁).a
        (T.step k hk N₁ ν β p₁).ν (k + 1) 1 T.t,
      ∀ ψ' ∈ FlBall (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) T.t,
      blockEnergyOne (T.step k hk N₁ ν β p₁).G' (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁))
        (T.step k hk N₁ ν β p₁).a₁ (T.step k hk N₁ ν β p₁).ν T.BG₂ T.κ T.t k zb (Θ, ψ') =
        ∑ Y ∈ 𝒴 zb, Ev zb Y (Θ, ψ'))
    (D : BgData (T.step k hk N₁ ν β p₁).G' 2)
    (hDh : ∀ y i, D.h y i = ((T.step k hk N₁ ν β p₁).h₀ i : ℂ))
    (hD : XiCData (T.step k hk N₁ ν β p₁).G' (compWeight 3 1) ν (k + 1) 1 T.t D)
    {x : ((T.step k hk N₁ ν β p₁).withDatum D hDh).E} (hx : ‖x‖ ≤ p₁)
    (z : Torus 3 (N₁ * 3 ^ T.m₁ * 3 ^ (k + 1 - (k + 1)))) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    HasDerivAt (fun t : ℂ => ((T.step k hk N₁ ν β p₁).withDatum D hDh).Phi1C
        (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁))
        (((T.step k hk N₁ ν β p₁).withDatum D hDh).markedTangentC z (s : ℂ) t x))
      (-(((T.step k hk N₁ ν β p₁).withDatum D hDh).β : ℂ) * ∑ zb, ∑ Y ∈ 𝒴 zb,
        deriv (markedBlockTerm (Ev zb Y) taylorWeight
          (liftC ((T.step k hk N₁ ν β p₁).withDatum D hDh).hG'
            ((s : ℂ) • ((T.step k hk N₁ ν β p₁).withDatum D hDh).shiftUC x))
          (liftC ((T.step k hk N₁ ν β p₁).withDatum D hDh).hG'
            (((T.step k hk N₁ ν β p₁).withDatum D hDh).maskUC z
              (((T.step k hk N₁ ν β p₁).withDatum D hDh).shiftUC x)))
          (rawOf ((T.step k hk N₁ ν β p₁).withDatum D hDh).D')) 0) 0 ∧
    (fderiv ℂ (((T.step k hk N₁ ν β p₁).withDatum D hDh).Phi1C
        (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)))
        ((s : ℂ) • ((T.step k hk N₁ ν β p₁).withDatum D hDh).shiftUC x))
      (((T.step k hk N₁ ν β p₁).withDatum D hDh).maskUC z
        (((T.step k hk N₁ ν β p₁).withDatum D hDh).shiftUC x)) =
      -(((T.step k hk N₁ ν β p₁).withDatum D hDh).β : ℂ) * ∑ zb, ∑ Y ∈ 𝒴 zb,
        deriv (markedBlockTerm (Ev zb Y) taylorWeight
          (liftC ((T.step k hk N₁ ν β p₁).withDatum D hDh).hG'
            ((s : ℂ) • ((T.step k hk N₁ ν β p₁).withDatum D hDh).shiftUC x))
          (liftC ((T.step k hk N₁ ν β p₁).withDatum D hDh).hG'
            (((T.step k hk N₁ ν β p₁).withDatum D hDh).maskUC z
              (((T.step k hk N₁ ν β p₁).withDatum D hDh).shiftUC x)))
          (rawOf ((T.step k hk N₁ ν β p₁).withDatum D hDh).D')) 0 := by
  have hsn : ‖(s : ℂ)‖ < 17 / 16 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs.1]; linarith [hs.2]
  have hdisc := markReal_disc_slice T hS hp₁ D hDh hD hx z hsn
  have hline := ((T.step k hk N₁ ν β p₁).withDatum D hDh).hasDerivAt_Phi1C_marked_eq_neg_beta_sum_of_disc
    z (c := T.c) (BG := T.BG) (κ := T.κ) (eps := T.t) (Kc := levelKc 3 3) (Cx := Cchi 3 3)
    (c₂ := T.c₂) (BG₂ := T.BG₂) (δ₁ := T.t)
    (StepScaleData.markReal_ha₁ (T := T) D hDh) (StepScaleData.markReal_H (T := T) hν0 hν D hDh) (hS.markReal_hD2 D hDh hD) hS.core
    T.markReal_hc7 (R := 2) le_rfl T.markReal_hRs T.markReal_hsmall T.markReal_hnum
    T.markReal_hnum' hD
    (fun ψ' h1 h2 => hreal_level (Gp := (T.step k hk N₁ ν β p₁).G')
      (Hm := stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) hS.core
      ((T.step k hk N₁ ν β p₁).withDatum D hDh).hG ((T.step k hk N₁ ν β p₁).withDatum D hDh).hG'
      (le_refl (k + 1)) (StepScaleData.markReal_ha₁ (T := T) D hDh) (StepScaleData.markReal_H (T := T) hν0 hν D hDh) T.markReal_hc7
      (by norm_num) T.markReal_hsm D hD ψ' h1 h2)
    𝒴 Ev han hsum (R₁ := 17 / 16) (r := lvR T.κ T.t (β * 3 ^ k) p₁ / 4) (t₁ := 1 / 16)
    (by norm_num) (by have := hS.r_pos; positivity) (by norm_num) x (s : ℂ) hdisc
  refine ⟨hline, ?_⟩
  exact ((T.step k hk N₁ ν β p₁).withDatum D hDh).markReal_fderiv_mask_eq_of_hasDerivAt z _ (s : ℂ) x
    (markReal_differentiableAt_Phi1C_scale' T hS hp₁ D hDh hD hx hs) hline

/-- **Instance of `markReal_slice_of_count`**: at the scale of `StepTower.scale_instance`
(`k = 1`, `N₁ = 6`, `ν = 0`, `p₁ = 1`, `β = βray`), every premise other than the common family
`𝒴, Ev, han, hsum` is satisfied by the step's own datum, so for every such family the identity holds
at `x = 0`, `s = 1/2`. -/
theorem markReal_slice_of_count_instance {κmin : ℝ} (T : StepTower κmin) :
    ∃ βray : ℝ, 2 ≤ βray ∧ Nonempty (StepScaleData T 1 le_rfl 6 0 βray 1) ∧
      ∀ (𝒴 : Torus 3 (6 * 3 ^ T.m₁ * 3 ^ (1 + 1 - (1 + 1))) →
          Finset (Set (CTorus 3 3 6 T.m₁ (1 + 1))))
        (Ev : Torus 3 (6 * 3 ^ T.m₁ * 3 ^ (1 + 1 - (1 + 1))) → Set (CTorus 3 3 6 T.m₁ (1 + 1)) →
          RawData 3 3 (6 * 3 ^ T.m₁) (1 + 1) 2 × (CTorus 3 3 6 T.m₁ (1 + 1) → Fin 2 → ℂ) → ℂ)
        (_han : ∀ zb Y, AnalyticOnNhd ℂ (Ev zb Y)
          (XiCRaw (T.step 1 le_rfl 6 0 βray 1).G' (T.step 1 le_rfl 6 0 βray 1).a
            (T.step 1 le_rfl 6 0 βray 1).ν (1 + 1) 1 T.t ×ˢ
            FlBall (stepG 3 3 6 T.m₁ 1 (rhoSep T.m₁)) T.t))
        (_hsum : ∀ zb, ∀ Θ ∈ XiCRaw (T.step 1 le_rfl 6 0 βray 1).G' (T.step 1 le_rfl 6 0 βray 1).a
            (T.step 1 le_rfl 6 0 βray 1).ν (1 + 1) 1 T.t,
          ∀ ψ' ∈ FlBall (stepG 3 3 6 T.m₁ 1 (rhoSep T.m₁)) T.t,
          blockEnergyOne (T.step 1 le_rfl 6 0 βray 1).G' (stepG 3 3 6 T.m₁ 1 (rhoSep T.m₁))
            (T.step 1 le_rfl 6 0 βray 1).a₁ (T.step 1 le_rfl 6 0 βray 1).ν T.BG₂ T.κ T.t 1
            zb (Θ, ψ') = ∑ Y ∈ 𝒴 zb, Ev zb Y (Θ, ψ'))
        (z : Torus 3 (6 * 3 ^ T.m₁ * 3 ^ (1 + 1 - (1 + 1)))),
        HasDerivAt (fun t : ℂ => (T.step 1 le_rfl 6 0 βray 1).Phi1C
            (zeroClass 3 3 6 T.m₁ 1 2 (rhoSep T.m₁))
            ((T.step 1 le_rfl 6 0 βray 1).markedTangentC z (((1 / 2 : ℝ) : ℂ)) t 0))
          (-((T.step 1 le_rfl 6 0 βray 1).β : ℂ) * ∑ zb, ∑ Y ∈ 𝒴 zb,
            deriv (markedBlockTerm (Ev zb Y) taylorWeight
              (liftC (T.step 1 le_rfl 6 0 βray 1).hG'
                (((1 / 2 : ℝ) : ℂ) • (T.step 1 le_rfl 6 0 βray 1).shiftUC 0))
              (liftC (T.step 1 le_rfl 6 0 βray 1).hG'
                ((T.step 1 le_rfl 6 0 βray 1).maskUC z
                  ((T.step 1 le_rfl 6 0 βray 1).shiftUC 0)))
              (rawOf (T.step 1 le_rfl 6 0 βray 1).D')) 0) 0 := by
  obtain ⟨βray, h2, ⟨hS⟩⟩ := T.scale_instance
  refine ⟨βray, h2, ⟨hS⟩, fun 𝒴 Ev han hsum z => ?_⟩
  exact (markReal_slice_of_count T hS one_pos le_rfl (by norm_num) 𝒴 Ev han hsum
    (T.step 1 le_rfl 6 0 βray 1).D' (T.step 1 le_rfl 6 0 βray 1).hh₀ hS.xi (x := 0) (by simp) z
    (s := 1 / 2) ⟨by norm_num, by norm_num⟩).1

end Balaban.Inhabited
