/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.StepComplexLocal
public import Balaban.Fluctuation.MarkedCubicTaylor
public import Balaban.Inhabited.StepTowerScale
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# MARK-REAL, ambient differentiability of `Φ₁` on the ray (leaf 3)

`E1MarksC` integrates the ambient Fréchet derivative
`(fderiv ℂ (S.Phi1C C) ((s : ℂ) • S.shiftUC x)) (S.maskUC z (S.shiftUC x))`, while the marked
identity gives only the derivative of `Φ₁` along the complex line `t ↦ u • shiftUC x + t • mask`.

* `markReal_differentiableAt_Phi1C`: `Φ₁` of the class with zero old terms is complex
  differentiable at `(s : ℂ) • shiftUC x`, `s ∈ [0,1]`, `‖x‖ ≤ p₁`, for a complex step with
  `p₁ < p⁺` and the numerical premises of `classRegularLocC_zeroClass`, all explicit.
* `markReal_fderiv_mask_eq_of_hasDerivAt`, `markReal_fderiv_mask_eq_neg_beta_sum`: the ambient
  derivative in the mask direction equals the value of the line derivative.
* `markReal_differentiableAt_Phi1C_scale`: the same for every datum `D` of the constant-`h₀` slice
  of the step of a scale of the shared tower, with the numerical premises read off `StepTower` and
  `StepScaleData`.

The slice statement `markReal_slice` and the record `E1MarksC` are not here.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.SmallField.Def6 Balaban.Background Balaban.Multiscale Balaban.Localization
  Balaban.SmallField Set

namespace StepSetting

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}
  (S : StepSetting d L N₁ m₁ k N ϱ)

section Reg

variable {c BG κ eps Kc Cx c₂ BG₂ δ₁ δc : ℝ}

/-- **Ambient differentiability of `Φ₁` at the ray points** (class with zero old terms).  Under the
premises of `classRegularLocC_zeroClass` (`FlCore`, the four chart margins, `a₁ > 0`, `c7 ≤ thm73C3`,
`R > 1` with the radius inequality, `β > 0`, `0 < p⁺`, the covariance bound `δ₁`, `XiCData` of the
datum) and `p₁ < p⁺`, `Φ₁` is complex differentiable at `s • shiftUC x` for `s ∈ [0,1]`,
`‖x‖ ≤ p₁`. -/
theorem markReal_differentiableAt_Phi1C
    (hC : FlCore N S.G' (stepG d L N₁ m₁ k ϱ) S.a₁ S.ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    (hdm : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    (ha₁ : 0 < S.a₁) (hc7 : c7 d L N BG κ ≤ thm73C3 d L N) {R : ℝ} (hR : 1 < R)
    (hsmR : 2 * (compC4 d * (bgK1 d L N * (xiC1 d * eps))) + 5 * (R * δ₁) ≤ bgC1 d L N)
    (hβ : 0 < S.β) {pp : ℝ} (hpp : 0 < pp)
    (hδ₁ : Real.sqrt N * (S.betaU ^ (-(1 / 2 : ℝ)) *
      (covSupConstC d L N (compWeight L S.a₁ k) κ * pp)) < δ₁)
    (hD : XiCData S.G' S.a S.ν (k + 1) 1 eps S.D')
    (hlt : S.p₁ < pp) {x : S.E} (hx : ‖x‖ ≤ S.p₁) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    DifferentiableAt ℂ (S.Phi1C (zeroClass d L N₁ m₁ k N ϱ)) ((s : ℂ) • S.shiftUC x) :=
  S.differentiableAt_Phi1C_of_classRegularLocC _
    (S.classRegularLocC_zeroClass hC hMX hdm hα hsm ha₁ hc7 hR hsmR hβ hpp hδ₁ hD hlt) hx hs

end Reg

section Ident

variable (z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))))
  (C : StepClass d L N₁ m₁ k N ϱ)

/-- **The ambient derivative in the mask direction is the line derivative.**  If `Φ₁` is complex
differentiable at `u • shiftUC x` and the line `t ↦ Φ₁(u • shiftUC x + t • mask)` has derivative
`w` at `0`, then `DΦ₁(u • shiftUC x)[maskUC z (shiftUC x)] = w`. -/
theorem markReal_fderiv_mask_eq_of_hasDerivAt (u : ℂ) (x : S.E)
    (hd : DifferentiableAt ℂ (S.Phi1C C) (u • S.shiftUC x)) {w : ℂ}
    (hline : HasDerivAt (fun t : ℂ => S.Phi1C C (S.markedTangentC z u t x)) w 0) :
    (fderiv ℂ (S.Phi1C C) (u • S.shiftUC x)) (S.maskUC z (S.shiftUC x)) = w :=
  (S.hasDerivAt_Phi1C_marked z C u x hd).unique hline

/-- **The identity in the form `E1MarksC.hF` needs** (zero class): at real `s ∈ [0,1]`, `‖x‖ ≤ p₁`,
the integrand `fderiv ℂ (Φ₁) (s • shiftUC x) (maskUC z (shiftUC x))` equals
`-β ∑_{b,Y} ∂_t markedBlockTerm …|₀`, given the one-dimensional identity (landed conclusion of
`hasDerivAt_Phi1C_marked_eq_neg_beta_sum_of_hdom`, taken as a hypothesis in its exact form) and the
`ClassRegularLocC` premises of `markReal_differentiableAt_Phi1C`. -/
theorem markReal_fderiv_mask_eq_neg_beta_sum
    {c BG κ eps Kc Cx c₂ BG₂ δ₁ δc : ℝ}
    (hC : FlCore N S.G' (stepG d L N₁ m₁ k ϱ) S.a₁ S.ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    (hdm : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    (ha₁ : 0 < S.a₁) (hc7 : c7 d L N BG κ ≤ thm73C3 d L N) {R : ℝ} (hR : 1 < R)
    (hsmR : 2 * (compC4 d * (bgK1 d L N * (xiC1 d * eps))) + 5 * (R * δ₁) ≤ bgC1 d L N)
    (hβ : 0 < S.β) {pp : ℝ} (hpp : 0 < pp)
    (hδ₁ : Real.sqrt N * (S.betaU ^ (-(1 / 2 : ℝ)) *
      (covSupConstC d L N (compWeight L S.a₁ k) κ * pp)) < δ₁)
    (hD : XiCData S.G' S.a S.ν (k + 1) 1 eps S.D')
    (hlt : S.p₁ < pp) {x : S.E} (hx : ‖x‖ ≤ S.p₁) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1)
    (𝒴 : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) →
      Finset (Set (CTorus d L N₁ m₁ (k + 1))))
    (Ev : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) → Set (CTorus d L N₁ m₁ (k + 1)) →
      RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) → ℂ)
    (hline : HasDerivAt
      (fun t : ℂ => S.Phi1C (zeroClass d L N₁ m₁ k N ϱ) (S.markedTangentC z (s : ℂ) t x))
      (-(S.β : ℂ) * ∑ zb, ∑ Y ∈ 𝒴 zb, deriv (markedBlockTerm (Ev zb Y) taylorWeight
        (liftC S.hG' ((s : ℂ) • S.shiftUC x)) (liftC S.hG' (S.maskUC z (S.shiftUC x)))
        (rawOf S.D')) 0) 0) :
    (fderiv ℂ (S.Phi1C (zeroClass d L N₁ m₁ k N ϱ)) ((s : ℂ) • S.shiftUC x))
        (S.maskUC z (S.shiftUC x)) =
      -(S.β : ℂ) * ∑ zb, ∑ Y ∈ 𝒴 zb, deriv (markedBlockTerm (Ev zb Y) taylorWeight
        (liftC S.hG' ((s : ℂ) • S.shiftUC x)) (liftC S.hG' (S.maskUC z (S.shiftUC x)))
        (rawOf S.D')) 0 :=
  S.markReal_fderiv_mask_eq_of_hasDerivAt z _ (s : ℂ) x
    (S.markReal_differentiableAt_Phi1C hC hMX hdm hα hsm ha₁ hc7 hR hsmR hβ hpp hδ₁ hD hlt hx hs)
    hline

end Ident

end StepSetting

end Balaban.Fluctuation

namespace Balaban.Inhabited

open Balaban Balaban.Fluctuation Balaban.Multiscale Balaban.Background Balaban.Localization
  Balaban.Localization.I5Inhabited Balaban.Inhabited.LevelStep Balaban.SmallField Set

/-- **Ambient differentiability of `Φ₁` for every datum of the constant-`h₀` slice at a scale of
the general tower** (`d`, `L`, `N` general).  The numerical premises of
`classRegularLocC_zeroClass` are supplied by `StepTowerG` (`large_block`, `dom_margin`,
`coer_margin`, `δc_small`, `c7_cap`, `bg1_cap`) and `StepScaleDataG` (`core`, `fl_radius`,
`ray_margin`, `r_pos`, `cψ_pos`), with `R = 2`, `pp = lvCpsiG`, `δ₁ = ε = T.t`.  Explicit: `0 < β`,
`0 < p₁`, and `XiCData` of the datum `D` itself. -/
theorem markReal_differentiableAt_Phi1C_scaleG {d L N : ℕ} [NeZero L] {κmin : ℝ}
    (T : StepTowerG d L N κmin) {k : ℕ}
    {hk : 1 ≤ k} {N₁ : ℕ} [NeZero N₁] {ν β p₁ : ℝ}
    (hS : StepScaleDataG T k hk N₁ ν β p₁) (hβ : 0 < β) (hp₁ : 0 < p₁)
    (D : BgData (T.step k hk N₁ ν β p₁).G' N)
    (hDh : ∀ y i, D.h y i = ((T.step k hk N₁ ν β p₁).h₀ i : ℂ))
    (hD : XiCData (T.step k hk N₁ ν β p₁).G' (compWeight L 1) ν (k + 1) 1 T.t D)
    {x : ((T.step k hk N₁ ν β p₁).withDatum D hDh).E} (hx : ‖x‖ ≤ p₁) {s : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) :
    DifferentiableAt ℂ (((T.step k hk N₁ ν β p₁).withDatum D hDh).Phi1C
        (zeroClass d L N₁ T.m₁ k N (rhoSepG d L T.m₁)))
      ((s : ℂ) • ((T.step k hk N₁ ν β p₁).withDatum D hDh).shiftUC x) := by
  have hbU : (T.step k hk N₁ ν β p₁).betaU = β * (L : ℝ) ^ (k * (d - 2)) :=
    hatStepKG_betaU T.hN (by have := T.hd; omega) k T.m₁ (rhoSepG d L T.m₁) hk ν β p₁ T.δ
  have hL : (0 : ℝ) < (L : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hbU0 : 0 < β * (L : ℝ) ^ (k * (d - 2)) := by positivity
  refine StepSetting.markReal_differentiableAt_Phi1C
    ((T.step k hk N₁ ν β p₁).withDatum D hDh) (δc := T.δc) (R := 2)
    (pp := lvCpsiG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2))))
    hS.core T.large_block T.dom_margin T.coer_margin T.δc_small one_pos T.c7_cap (by norm_num)
    T.bg1_cap hβ hS.cψ_pos ?_ hD ?_ hx hs
  · have h := hS.fl_radius
    have hn : ‖(((T.step k hk N₁ ν β p₁).betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)‖ =
        (T.step k hk N₁ ν β p₁).betaU ^ (-(1 / 2 : ℝ)) := by
      rw [Complex.norm_real, Real.norm_of_nonneg]
      rw [hbU]; exact Real.rpow_nonneg hbU0.le _
    rw [hn] at h
    exact h
  · have h := hS.ray_margin
    have hl := hS.r_pos
    show p₁ < _
    nlinarith

/-- **Ambient differentiability of `Φ₁` for every datum of the constant-`h₀` slice at a scale of
the shared tower** (`d = L = 3`, `N = 2`): the case of `markReal_differentiableAt_Phi1C_scaleG` at
`T.toG`.  Explicit: `0 < β`, `0 < p₁`, and `XiCData` of the datum `D` itself. -/
theorem markReal_differentiableAt_Phi1C_scale {κmin : ℝ} (T : StepTower κmin) {k : ℕ}
    {hk : 1 ≤ k} {N₁ : ℕ} [NeZero N₁] {ν β p₁ : ℝ}
    (hS : StepScaleData T k hk N₁ ν β p₁) (hβ : 0 < β) (hp₁ : 0 < p₁)
    (D : BgData (T.step k hk N₁ ν β p₁).G' 2)
    (hDh : ∀ y i, D.h y i = ((T.step k hk N₁ ν β p₁).h₀ i : ℂ))
    (hD : XiCData (T.step k hk N₁ ν β p₁).G' (compWeight 3 1) ν (k + 1) 1 T.t D)
    {x : ((T.step k hk N₁ ν β p₁).withDatum D hDh).E} (hx : ‖x‖ ≤ p₁) {s : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) :
    DifferentiableAt ℂ (((T.step k hk N₁ ν β p₁).withDatum D hDh).Phi1C
        (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)))
      ((s : ℂ) • ((T.step k hk N₁ ν β p₁).withDatum D hDh).shiftUC x) := by
  have key : ∀ ϱ : ℝ, ϱ = rhoSep T.m₁ →
      (∀ (D : BgData (hatStepKG (d := 3) (L := 3) (N := 2) (N₁ := N₁) le_rfl k T.m₁ ϱ hk ν β
          p₁ T.δ).G' 2)
        (hDh : ∀ y i, D.h y i = ((hatStepKG (d := 3) (L := 3) (N := 2) (N₁ := N₁) le_rfl k T.m₁
          ϱ hk ν β p₁ T.δ).h₀ i : ℂ))
        (hD : XiCData (hatStepKG (d := 3) (L := 3) (N := 2) (N₁ := N₁) le_rfl k T.m₁ ϱ hk ν β
          p₁ T.δ).G' (compWeight 3 1) ν (k + 1) 1 T.t D)
        {x : ((hatStepKG (d := 3) (L := 3) (N := 2) (N₁ := N₁) le_rfl k T.m₁ ϱ hk ν β p₁
          T.δ).withDatum D hDh).E} (_ : ‖x‖ ≤ p₁) {s : ℝ} (_ : s ∈ Icc (0 : ℝ) 1),
        DifferentiableAt ℂ (((hatStepKG (d := 3) (L := 3) (N := 2) (N₁ := N₁) le_rfl k T.m₁ ϱ hk
            ν β p₁ T.δ).withDatum D hDh).Phi1C (zeroClass 3 3 N₁ T.m₁ k 2 ϱ))
          ((s : ℂ) • ((hatStepKG (d := 3) (L := 3) (N := 2) (N₁ := N₁) le_rfl k T.m₁ ϱ hk ν β
            p₁ T.δ).withDatum D hDh).shiftUC x)) →
      ∀ (D : BgData (T.step k hk N₁ ν β p₁).G' 2)
        (hDh : ∀ y i, D.h y i = ((T.step k hk N₁ ν β p₁).h₀ i : ℂ))
        (hD : XiCData (T.step k hk N₁ ν β p₁).G' (compWeight 3 1) ν (k + 1) 1 T.t D)
        {x : ((T.step k hk N₁ ν β p₁).withDatum D hDh).E} (_ : ‖x‖ ≤ p₁) {s : ℝ}
        (_ : s ∈ Icc (0 : ℝ) 1),
        DifferentiableAt ℂ (((T.step k hk N₁ ν β p₁).withDatum D hDh).Phi1C
            (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)))
          ((s : ℂ) • ((T.step k hk N₁ ν β p₁).withDatum D hDh).shiftUC x) := by
    intro ϱ hϱ; subst hϱ; exact id
  have hG := T.scaleDataG_of_fixed hS
  exact key _ (rhoSepG_three _)
    (fun D hDh hD x hx s hs =>
      markReal_differentiableAt_Phi1C_scaleG T.toG hG hβ hp₁ D hDh hD hx hs) D hDh hD hx hs

/-- **Non-vacuity of `markReal_differentiableAt_Phi1C_scale`**: for every tower there are a scale
and a parameter point (`k = 1`, `N₁ = 6`, `ν = 0`, `p₁ = 1`, `β = βray`) at which the step's own
datum satisfies all premises and the conclusion holds at `s = 1/2`, `x = 0`. -/
theorem markReal_differentiableAt_Phi1C_scale_nonempty {κmin : ℝ} (T : StepTower κmin) :
    ∃ βray : ℝ, 2 ≤ βray ∧
      DifferentiableAt ℂ ((T.step 1 le_rfl 6 0 βray 1).Phi1C
          (zeroClass 3 3 6 T.m₁ 1 2 (rhoSep T.m₁)))
        (((1 / 2 : ℝ) : ℂ) • (T.step 1 le_rfl 6 0 βray 1).shiftUC 0) := by
  obtain ⟨βray, h2, ⟨hS⟩⟩ := T.scale_instance
  refine ⟨βray, h2, ?_⟩
  have := markReal_differentiableAt_Phi1C_scale T hS (by linarith) one_pos
    (T.step 1 le_rfl 6 0 βray 1).D' (T.step 1 le_rfl 6 0 βray 1).hh₀ hS.xi (x := 0)
    (by simp) (s := 1 / 2) ⟨by norm_num, by norm_num⟩
  exact this

end Balaban.Inhabited
