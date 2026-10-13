/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.MarkedFamilyFromTower
public import Balaban.Inhabited.MarkRealDiscSlice

/-!
# One marked family for all roots at the shared tower

* `markedFamily_fromTower_allRoots` (T1): one family `𝒴, Ev` carrying the four block-expansion
  clauses of `markedFamily_fromTower` and, for the chart-wide tangent `Q` of
  `exists_analytic_shiftUC_chart` of every hat field `‖x‖ ≤ p₁`, every marked root `z`, every block
  `zb` and every label `Y`, the three marked clauses of `markedCubic_joint_physV` at the tower radii
  `R₁ = R_σ = 17/16`, `t₁ = 1/16`, `r = lvR/4`.
* `markReal_slice_allRoots` (T2): the same family together with the slice identity of
  `markReal_slice`.
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Fluctuation Balaban.Multiscale Balaban.Background Balaban.Localization
  Balaban.Localization.I5Inhabited Balaban.Inhabited.LevelStep Balaban.SmallField Set

/-- **T1.  One family of marked block terms for all roots at the tower.**  At an admissible scale
there are `𝒴, Ev` with the four clauses of `markedFamily_fromTower` (`han`, `hsum`, locality, the
bound `E* e^{-2 κ_dec d(Y)}`) and, for every hat field `‖x‖ ≤ p₁` with its chart-wide tangent `Q`
of `exists_analytic_shiftUC_chart`, every marked root `z`, every block `zb` and every label `Y`, the
three clauses of `markedCubic_joint_physV` at `R₁ = R_σ = 17/16`, `t₁ = 1/16`, `r = lvR/4`: joint
analyticity on `physV × ball 0 (17/16) × ball 0 (1/16)`, analytic derivative mark at `t = 0`, and the
Cauchy bound `3 E* e^{-2 κ_dec d(Y)} / (r³ t₀)` for `0 < t₀ < 1/16`. -/
theorem markedFamily_fromTower_allRoots {κmin : ℝ} (T : StepTower κmin) {k : ℕ}
    {hk : 1 ≤ k} {N₁ : ℕ} [NeZero N₁] {ν β p₁ : ℝ}
    (hS : StepScaleData T k hk N₁ ν β p₁) (hN : 5 < N₁) (hp₁ : 0 < p₁) (hν0 : 0 ≤ ν)
    (hν : ν * 3 ^ (2 * (k + 1)) ≤ 1) :
    ∃ (𝒴 : Torus 3 (N₁ * 3 ^ T.m₁ * 3 ^ (k + 1 - (k + 1))) →
      Finset (Set (CTorus 3 3 N₁ T.m₁ (k + 1))))
    (Ev : Torus 3 (N₁ * 3 ^ T.m₁ * 3 ^ (k + 1 - (k + 1))) → Set (CTorus 3 3 N₁ T.m₁ (k + 1)) →
      RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2 × (CTorus 3 3 N₁ T.m₁ (k + 1) → Fin 2 → ℂ) → ℂ),
    (∀ zb Y, AnalyticOnNhd ℂ (Ev zb Y)
      (XiCRaw (T.step k hk N₁ ν β p₁).G' (T.step k hk N₁ ν β p₁).a (T.step k hk N₁ ν β p₁).ν (k + 1) 1 T.t ×ˢ FlBall (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) T.t)) ∧
    (∀ zb, ∀ Θ ∈ XiCRaw (T.step k hk N₁ ν β p₁).G' (T.step k hk N₁ ν β p₁).a (T.step k hk N₁ ν β p₁).ν (k + 1) 1 T.t,
      ∀ ψ' ∈ FlBall (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) T.t,
      blockEnergyOne (T.step k hk N₁ ν β p₁).G' (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) (T.step k hk N₁ ν β p₁).a₁ (T.step k hk N₁ ν β p₁).ν T.BG₂ T.κ T.t k zb
        (Θ, ψ') = ∑ Y ∈ 𝒴 zb, Ev zb Y (Θ, ψ')) ∧
    (∀ zb Y, ∀ u ∈ XiCRaw (T.step k hk N₁ ν β p₁).G' (compWeight 3 (T.step k hk N₁ ν β p₁).a₁) (T.step k hk N₁ ν β p₁).ν (k + 1) 1 T.t ×ˢ
        FlBall (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) T.t,
      ∀ u' ∈ XiCRaw (T.step k hk N₁ ν β p₁).G' (compWeight 3 (T.step k hk N₁ ν β p₁).a₁) (T.step k hk N₁ ν β p₁).ν (k + 1) 1 T.t ×ˢ
        FlBall (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) T.t,
      agreeOn (thickSet (T.step k hk N₁ ν β p₁).G' Y) u.1 u'.1 →
        (∀ y ∈ psiThick Y, u.2 y = u'.2 y) → Ev zb Y u = Ev zb Y u') ∧
    (∀ zb Y, ∀ u ∈ XiCRaw (T.step k hk N₁ ν β p₁).G' (compWeight 3 (T.step k hk N₁ ν β p₁).a₁) (T.step k hk N₁ ν β p₁).ν (k + 1) 1 T.t ×ˢ
        FlBall (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) T.t,
      ‖Ev zb Y u‖ ≤ energyBdScaled 3 3 2 (compWeight 3 (T.step k hk N₁ ν β p₁).a₁) k
        (cK2' 3 3 2 (famConst 3 3 T.BG₂ T.κ) * T.t) T.t (rho4 3 3 2 T.BG T.κ) *
        Real.exp (-2 * T.κdec * treeLenCov (T.step k hk N₁ ν β p₁).G' 1 Y)) ∧
    (∀ x : (T.step k hk N₁ ν β p₁).E, ‖x‖ ≤ p₁ →
      ∃ Q : RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2 → (T.step k hk N₁ ν β p₁).EC,
        AnalyticOnNhd ℂ Q (XiCRaw (T.step k hk N₁ ν β p₁).G' (compWeight 3 (T.step k hk N₁ ν β p₁).a₁) (T.step k hk N₁ ν β p₁).ν (k + 1) 1 T.t) ∧
        (∀ (D : BgData (T.step k hk N₁ ν β p₁).G' 2) (hDh : ∀ y i, D.h y i = ((T.step k hk N₁ ν β p₁).h₀ i : ℂ)),
          XiCData (T.step k hk N₁ ν β p₁).G' (compWeight 3 (T.step k hk N₁ ν β p₁).a₁) (T.step k hk N₁ ν β p₁).ν (k + 1) 1 T.t D →
          Q (rawOf D) = ((T.step k hk N₁ ν β p₁).withDatum D hDh).shiftUC x) ∧
        (∀ Θ ∈ XiCRaw (T.step k hk N₁ ν β p₁).G' (compWeight 3 (T.step k hk N₁ ν β p₁).a₁) (T.step k hk N₁ ν β p₁).ν (k + 1) 1 T.t, ∀ b : (T.step k hk N₁ ν β p₁).U,
          vn (fun i => Q Θ (b, i)) ≤
            markedRad 3 3 2 k (T.step k hk N₁ ν β p₁).a₁ T.κ p₁ ((((T.step k hk N₁ ν β p₁).betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ))) ∧
        ∀ (z : Torus 3 (N₁ * 3 ^ T.m₁ * 3 ^ (k + 1 - (k + 1))))
          (zb : Torus 3 (N₁ * 3 ^ T.m₁ * 3 ^ (k + 1 - (k + 1)))) (Y : Set (CTorus 3 3 N₁ T.m₁ (k + 1))),
        AnalyticOnNhd ℂ (fun w : (physParam 2 (T.step k hk N₁ ν β p₁) × ℂ) × ℂ =>
            markedBlockTerm (Ev zb Y) taylorWeight
              (liftC (T.step k hk N₁ ν β p₁).hG' (w.1.2 • Q (w.1.1.1 : RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2)))
              (liftC (T.step k hk N₁ ν β p₁).hG' ((T.step k hk N₁ ν β p₁).maskUC z (Q (w.1.1.1 : RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2))))
              (w.1.1.1 : RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2) w.2)
          ((physV (T.step k hk N₁ ν β p₁) (T.step k hk N₁ ν β p₁).a₁ (T.step k hk N₁ ν β p₁).ν T.t ×ˢ Metric.ball (0 : ℂ) (17 / 16)) ×ˢ Metric.ball (0 : ℂ) (1 / 16)) ∧
        AnalyticOnNhd ℂ (fun w : physParam 2 (T.step k hk N₁ ν β p₁) × ℂ => deriv (markedBlockTerm (Ev zb Y) taylorWeight
            (liftC (T.step k hk N₁ ν β p₁).hG' (w.2 • Q (w.1.1 : RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2)))
            (liftC (T.step k hk N₁ ν β p₁).hG' ((T.step k hk N₁ ν β p₁).maskUC z (Q (w.1.1 : RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2))))
            (w.1.1 : RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2)) 0)
          (physV (T.step k hk N₁ ν β p₁) (T.step k hk N₁ ν β p₁).a₁ (T.step k hk N₁ ν β p₁).ν T.t ×ˢ Metric.ball (0 : ℂ) (17 / 16)) ∧
        ∀ {t₀ : ℝ}, 0 < t₀ → t₀ < 1 / 16 → ∀ e ∈ physV (T.step k hk N₁ ν β p₁) (T.step k hk N₁ ν β p₁).a₁ (T.step k hk N₁ ν β p₁).ν T.t, ∀ u : ℂ,
          ‖u‖ < 17 / 16 →
          ‖deriv (markedBlockTerm (Ev zb Y) taylorWeight
            (liftC (T.step k hk N₁ ν β p₁).hG' (u • Q (e.1 : RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2)))
            (liftC (T.step k hk N₁ ν β p₁).hG' ((T.step k hk N₁ ν β p₁).maskUC z (Q (e.1 : RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2))))
            (e.1 : RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2)) 0‖ ≤
            3 * (energyBdScaled 3 3 2 (compWeight 3 (T.step k hk N₁ ν β p₁).a₁) k
              (cK2' 3 3 2 (famConst 3 3 T.BG₂ T.κ) * T.t) T.t (rho4 3 3 2 T.BG T.κ) *
              Real.exp (-2 * T.κdec * treeLenCov (T.step k hk N₁ ν β p₁).G' 1 Y)) /
              ((lvR T.κ T.t (β * 3 ^ k) p₁ / 4) ^ 3 * t₀)) := by
  obtain ⟨𝒴, Ev, han, hsum, loc, bd⟩ := markedFamily_fromTower T hS hN hν0 hν
  refine ⟨𝒴, Ev, han, hsum, loc, bd, fun x hx => ?_⟩
  obtain ⟨Q, hQan, hQfib, hQb⟩ := (T.step k hk N₁ ν β p₁).exists_analytic_shiftUC_chart
    (δc := T.δc) hS.core T.large_block T.dom_margin T.coer_margin T.δc_small x
    (cψ := p₁) hp₁.le (fun p => (T.step k hk N₁ ν β p₁).yhat_le_of_norm_le hx p)
  refine ⟨Q, hQan, hQfib, hQb, fun z zb Y => ?_⟩
  obtain ⟨j1, j2, j3⟩ := (T.step k hk N₁ ν β p₁).markedCubic_joint_physV z (isLevel_lvLow hk)
    hS.core.HBp (hS.marked_radius_lt hp₁) (by norm_num) (by have := hS.r_pos; positivity)
    (by norm_num) (han zb Y) hQan hQb
  exact ⟨j1, j2, fun ht₀ ht₀₁ => j3 (fun w hw => bd zb Y w hw) ht₀ ht₀₁⟩

/-- **T2.  The slice identity for the one family of `markedFamily_fromTower_allRoots`.**  One
existential statement: the family `𝒴, Ev` carries T1 (i), T1 (ii) and, for every datum, hat field,
root and real `s ∈ [0,1]`, the marked derivative identity and the ambient `fderiv` identity of
`markReal_slice`. -/
theorem markReal_slice_allRoots {κmin : ℝ} (T : StepTower κmin) {k : ℕ}
    {hk : 1 ≤ k} {N₁ : ℕ} [NeZero N₁] {ν β p₁ : ℝ}
    (hS : StepScaleData T k hk N₁ ν β p₁) (hN : 5 < N₁) (hp₁ : 0 < p₁) (hν0 : 0 ≤ ν)
    (hν : ν * 3 ^ (2 * (k + 1)) ≤ 1) :
    ∃ (𝒴 : Torus 3 (N₁ * 3 ^ T.m₁ * 3 ^ (k + 1 - (k + 1))) →
      Finset (Set (CTorus 3 3 N₁ T.m₁ (k + 1))))
    (Ev : Torus 3 (N₁ * 3 ^ T.m₁ * 3 ^ (k + 1 - (k + 1))) → Set (CTorus 3 3 N₁ T.m₁ (k + 1)) →
      RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2 × (CTorus 3 3 N₁ T.m₁ (k + 1) → Fin 2 → ℂ) → ℂ),
    (∀ zb Y, AnalyticOnNhd ℂ (Ev zb Y)
      (XiCRaw (T.step k hk N₁ ν β p₁).G' (T.step k hk N₁ ν β p₁).a (T.step k hk N₁ ν β p₁).ν (k + 1) 1 T.t ×ˢ FlBall (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) T.t)) ∧
    (∀ zb, ∀ Θ ∈ XiCRaw (T.step k hk N₁ ν β p₁).G' (T.step k hk N₁ ν β p₁).a (T.step k hk N₁ ν β p₁).ν (k + 1) 1 T.t,
      ∀ ψ' ∈ FlBall (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) T.t,
      blockEnergyOne (T.step k hk N₁ ν β p₁).G' (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) (T.step k hk N₁ ν β p₁).a₁ (T.step k hk N₁ ν β p₁).ν T.BG₂ T.κ T.t k zb
        (Θ, ψ') = ∑ Y ∈ 𝒴 zb, Ev zb Y (Θ, ψ')) ∧
    (∀ zb Y, ∀ u ∈ XiCRaw (T.step k hk N₁ ν β p₁).G' (compWeight 3 (T.step k hk N₁ ν β p₁).a₁) (T.step k hk N₁ ν β p₁).ν (k + 1) 1 T.t ×ˢ
        FlBall (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) T.t,
      ∀ u' ∈ XiCRaw (T.step k hk N₁ ν β p₁).G' (compWeight 3 (T.step k hk N₁ ν β p₁).a₁) (T.step k hk N₁ ν β p₁).ν (k + 1) 1 T.t ×ˢ
        FlBall (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) T.t,
      agreeOn (thickSet (T.step k hk N₁ ν β p₁).G' Y) u.1 u'.1 →
        (∀ y ∈ psiThick Y, u.2 y = u'.2 y) → Ev zb Y u = Ev zb Y u') ∧
    (∀ zb Y, ∀ u ∈ XiCRaw (T.step k hk N₁ ν β p₁).G' (compWeight 3 (T.step k hk N₁ ν β p₁).a₁) (T.step k hk N₁ ν β p₁).ν (k + 1) 1 T.t ×ˢ
        FlBall (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) T.t,
      ‖Ev zb Y u‖ ≤ energyBdScaled 3 3 2 (compWeight 3 (T.step k hk N₁ ν β p₁).a₁) k
        (cK2' 3 3 2 (famConst 3 3 T.BG₂ T.κ) * T.t) T.t (rho4 3 3 2 T.BG T.κ) *
        Real.exp (-2 * T.κdec * treeLenCov (T.step k hk N₁ ν β p₁).G' 1 Y)) ∧
    (∀ x : (T.step k hk N₁ ν β p₁).E, ‖x‖ ≤ p₁ →
      ∃ Q : RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2 → (T.step k hk N₁ ν β p₁).EC,
        AnalyticOnNhd ℂ Q (XiCRaw (T.step k hk N₁ ν β p₁).G' (compWeight 3 (T.step k hk N₁ ν β p₁).a₁) (T.step k hk N₁ ν β p₁).ν (k + 1) 1 T.t) ∧
        (∀ (D : BgData (T.step k hk N₁ ν β p₁).G' 2) (hDh : ∀ y i, D.h y i = ((T.step k hk N₁ ν β p₁).h₀ i : ℂ)),
          XiCData (T.step k hk N₁ ν β p₁).G' (compWeight 3 (T.step k hk N₁ ν β p₁).a₁) (T.step k hk N₁ ν β p₁).ν (k + 1) 1 T.t D →
          Q (rawOf D) = ((T.step k hk N₁ ν β p₁).withDatum D hDh).shiftUC x) ∧
        (∀ Θ ∈ XiCRaw (T.step k hk N₁ ν β p₁).G' (compWeight 3 (T.step k hk N₁ ν β p₁).a₁) (T.step k hk N₁ ν β p₁).ν (k + 1) 1 T.t, ∀ b : (T.step k hk N₁ ν β p₁).U,
          vn (fun i => Q Θ (b, i)) ≤
            markedRad 3 3 2 k (T.step k hk N₁ ν β p₁).a₁ T.κ p₁ ((((T.step k hk N₁ ν β p₁).betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ))) ∧
        ∀ (z : Torus 3 (N₁ * 3 ^ T.m₁ * 3 ^ (k + 1 - (k + 1))))
          (zb : Torus 3 (N₁ * 3 ^ T.m₁ * 3 ^ (k + 1 - (k + 1)))) (Y : Set (CTorus 3 3 N₁ T.m₁ (k + 1))),
        AnalyticOnNhd ℂ (fun w : (physParam 2 (T.step k hk N₁ ν β p₁) × ℂ) × ℂ =>
            markedBlockTerm (Ev zb Y) taylorWeight
              (liftC (T.step k hk N₁ ν β p₁).hG' (w.1.2 • Q (w.1.1.1 : RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2)))
              (liftC (T.step k hk N₁ ν β p₁).hG' ((T.step k hk N₁ ν β p₁).maskUC z (Q (w.1.1.1 : RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2))))
              (w.1.1.1 : RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2) w.2)
          ((physV (T.step k hk N₁ ν β p₁) (T.step k hk N₁ ν β p₁).a₁ (T.step k hk N₁ ν β p₁).ν T.t ×ˢ Metric.ball (0 : ℂ) (17 / 16)) ×ˢ Metric.ball (0 : ℂ) (1 / 16)) ∧
        AnalyticOnNhd ℂ (fun w : physParam 2 (T.step k hk N₁ ν β p₁) × ℂ => deriv (markedBlockTerm (Ev zb Y) taylorWeight
            (liftC (T.step k hk N₁ ν β p₁).hG' (w.2 • Q (w.1.1 : RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2)))
            (liftC (T.step k hk N₁ ν β p₁).hG' ((T.step k hk N₁ ν β p₁).maskUC z (Q (w.1.1 : RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2))))
            (w.1.1 : RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2)) 0)
          (physV (T.step k hk N₁ ν β p₁) (T.step k hk N₁ ν β p₁).a₁ (T.step k hk N₁ ν β p₁).ν T.t ×ˢ Metric.ball (0 : ℂ) (17 / 16)) ∧
        ∀ {t₀ : ℝ}, 0 < t₀ → t₀ < 1 / 16 → ∀ e ∈ physV (T.step k hk N₁ ν β p₁) (T.step k hk N₁ ν β p₁).a₁ (T.step k hk N₁ ν β p₁).ν T.t, ∀ u : ℂ,
          ‖u‖ < 17 / 16 →
          ‖deriv (markedBlockTerm (Ev zb Y) taylorWeight
            (liftC (T.step k hk N₁ ν β p₁).hG' (u • Q (e.1 : RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2)))
            (liftC (T.step k hk N₁ ν β p₁).hG' ((T.step k hk N₁ ν β p₁).maskUC z (Q (e.1 : RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2))))
            (e.1 : RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2)) 0‖ ≤
            3 * (energyBdScaled 3 3 2 (compWeight 3 (T.step k hk N₁ ν β p₁).a₁) k
              (cK2' 3 3 2 (famConst 3 3 T.BG₂ T.κ) * T.t) T.t (rho4 3 3 2 T.BG T.κ) *
              Real.exp (-2 * T.κdec * treeLenCov (T.step k hk N₁ ν β p₁).G' 1 Y)) /
              ((lvR T.κ T.t (β * 3 ^ k) p₁ / 4) ^ 3 * t₀)) ∧
    ∀ (D : BgData (T.step k hk N₁ ν β p₁).G' 2)
    (hDh : ∀ y i, D.h y i = ((T.step k hk N₁ ν β p₁).h₀ i : ℂ))
    (_hD : XiCData (T.step k hk N₁ ν β p₁).G' (compWeight 3 1) ν (k + 1) 1 T.t D)
    {x : ((T.step k hk N₁ ν β p₁).withDatum D hDh).E} (_hx : ‖x‖ ≤ p₁)
    (z : Torus 3 (N₁ * 3 ^ T.m₁ * 3 ^ (k + 1 - (k + 1)))) {s : ℝ} (_hs : s ∈ Icc (0 : ℝ) 1),
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
        ((s : ℂ) • ((T.step k hk N₁ ν β p₁).withDatum D hDh).shiftUC x)
      (((T.step k hk N₁ ν β p₁).withDatum D hDh).maskUC z
        (((T.step k hk N₁ ν β p₁).withDatum D hDh).shiftUC x)) =
      -(((T.step k hk N₁ ν β p₁).withDatum D hDh).β : ℂ) * ∑ zb, ∑ Y ∈ 𝒴 zb,
        deriv (markedBlockTerm (Ev zb Y) taylorWeight
          (liftC ((T.step k hk N₁ ν β p₁).withDatum D hDh).hG'
            ((s : ℂ) • ((T.step k hk N₁ ν β p₁).withDatum D hDh).shiftUC x))
          (liftC ((T.step k hk N₁ ν β p₁).withDatum D hDh).hG'
            (((T.step k hk N₁ ν β p₁).withDatum D hDh).maskUC z
              (((T.step k hk N₁ ν β p₁).withDatum D hDh).shiftUC x)))
          (rawOf ((T.step k hk N₁ ν β p₁).withDatum D hDh).D')) 0) := by
  obtain ⟨𝒴, Ev, h1, h2, h3, h4, hB⟩ := markedFamily_fromTower_allRoots T hS hN hp₁ hν0 hν
  exact ⟨𝒴, Ev, h1, h2, h3, h4, hB, fun D hDh hD x hx z s hs =>
    markReal_slice_of_count T hS hp₁ hν0 hν 𝒴 Ev h1 h2 D hDh hD hx z hs⟩

end Balaban.Inhabited
