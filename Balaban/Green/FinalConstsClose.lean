/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Green.FinalLevelCountBound
public import Balaban.Green.FinalPolydiscLocal
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

/-!
# The numerical premises of the last integral for the run's constants (blocker 5)

The composed theorems of the last integral (`norm_coef_cutoff_class_le_levels`,
`cutoffInteraction_final_class_polydisc_local`) carry thirteen numerical premises in the radius
`ε_K = epsSeq L α α₀ K`, the radius `c ε_K` of the polydisc, the block radius `ε₀` and the size
of `β₀`.  Here they are discharged from explicit thresholds: `ε_K ≤ 3 α₀`, `ε₀` small against
`ε_K`, `c` small, `α₀` small, `β₀` large.

* `final_consts_of_large`: all the premises at once;
* `size_of_beta_large`: the size condition from `β₀` large;
* `norm_coef_cutoff_class_le_levels_of_large`: the volume-uniform coefficient bound with the
  numerical premises replaced by the thresholds.

The block datum `θ = S.D'` has no field of `StepSetting` placing it in the class chart; the
membership `XiCData S.G' S.a S.ν (k + 1) 1 ε₀ S.D'` is the typing data of a step whose block
field is the critical-point datum (it is proved for the concrete step in
`Inhabited/DetOutputTermsWitnessG.lean` with `ε₀ = t`), and stays a hypothesis here.
-/

@[expose] public section

open Finset Set MeasureTheory Metric Balaban Balaban.Multiscale Balaban.Background
  Balaban.Localization Balaban.Analysis Balaban.SmallField Balaban.SmallField.Def6
  Balaban.SmallField.Def6v2 Balaban.SmallField.GsSpec Balaban.Fluctuation Balaban.Inhabited
  Balaban.LargeField Balaban.LargeField.ActionConv

namespace Balaban.Green

/-- **The size condition from `β₀` large**: `B A₁ (4p)^p < c α₀ β₀^{1/4}` as soon as
`(B A₁ (4p)^p / (c α₀))^4 < β₀`. -/
theorem size_of_beta_large {B A₁ c α₀ β₀ : ℝ} {p : ℕ} (hB : 0 ≤ B) (hA : 0 ≤ A₁) (hc : 0 < c)
    (hα₀ : 0 < α₀)
    (hβ : (B * A₁ * (4 * (p : ℝ)) ^ p / (c * α₀)) ^ 4 < β₀) :
    B * A₁ * (4 * (p : ℝ)) ^ p < c * α₀ * β₀ ^ (1 / 4 : ℝ) := by
  have hcα : 0 < c * α₀ := mul_pos hc hα₀
  set q : ℝ := B * A₁ * (4 * (p : ℝ)) ^ p / (c * α₀) with hq
  have hq0 : 0 ≤ q := by rw [hq]; positivity
  have h1 : q = (q ^ 4) ^ (1 / 4 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hq0]; norm_num
  have h2 : q < β₀ ^ (1 / 4 : ℝ) := by
    rw [h1]
    exact Real.rpow_lt_rpow (by positivity) hβ (by norm_num)
  have h3 : B * A₁ * (4 * (p : ℝ)) ^ p = q * (c * α₀) := by
    rw [hq]; field_simp
  rw [h3]
  nlinarith

theorem three_alpha_le_one_of_small {d' : ℕ} {α₀ : ℝ} (hα₀ : 0 ≤ α₀)
    (h : (4 * d' + 6) * ((2 * d' + 1) * (3 * α₀)) ≤ 1) : 3 * α₀ ≤ 1 := by
  have hd0 : (0 : ℝ) ≤ d' := Nat.cast_nonneg d'
  have hP1 : (1 : ℝ) ≤ (4 * d' + 6) * (2 * d' + 1) := by nlinarith
  have e2 : (4 * (d' : ℝ) + 6) * ((2 * d' + 1) * (3 * α₀)) =
    ((4 * d' + 6) * (2 * d' + 1)) * (3 * α₀) := by ring
  rw [e2] at h
  have h3 : 0 ≤ 3 * α₀ := by linarith
  calc 3 * α₀ = 1 * (3 * α₀) := (one_mul _).symm
    _ ≤ ((4 * d' + 6) * (2 * d' + 1)) * (3 * α₀) := mul_le_mul_of_nonneg_right hP1 h3
    _ ≤ 1 := h

theorem epsSeq_le_three_alpha (L : ℕ) [NeZero L] {α α₀ : ℝ} (hα₀ : 0 < α₀) (hα0 : 0 ≤ α)
    (K : ℕ) : epsSeq L α α₀ K ≤ 3 * α₀ := by
  have h1 := epsSeq_le_tail_zero L α α₀ hα₀.le hα0 K
  have h2 := epsTail_lt_three 0
  have h3 := mul_le_mul_of_nonneg_left h2.le hα₀.le
  linarith

section Consts

variable {L : ℕ} [NeZero L] {d' N : ℕ}

/-- **All the numerical premises of the last integral for the run's constants.**  Let
`E = ε_K = epsSeq L α α₀ K`, `X = ε₀ + K₂' N · 2 c E` the radius of the composed data and
`K_loc = (2 K₁ + 2) C₁`.  If `ε₀ ≥ 0` is small against `ε_K` (`2 K_loc ε₀ ≤ ε_K`), `c` is small
(`4 K_loc K₂' N c ≤ 1`, `N c ≤ 1`), and `α₀` is small (the nine conditions with `3 α₀` in place of
`ε_K ≤ 3 α₀`), then the thirteen premises of `norm_coef_cutoff_class_le_levels` (with `δw` the
constant it provides) hold at once. -/
theorem final_consts_of_large {c α α₀ ε₀ δw : ℝ} {K : ℕ} (hc : 0 < c) (hα₀ : 0 < α₀)
    (hα0 : 0 ≤ α) (hε₀ : 0 ≤ ε₀)
    (hεR : 2 * ((2 * bgK1 d' L N + 2) * xiC1 d') * ε₀ ≤ epsSeq L α α₀ K)
    (hcs : 4 * ((2 * bgK1 d' L N + 2) * xiC1 d') * xiK2 d' L N * (N : ℝ) * c ≤ 1)
    (hNc : (N : ℝ) * c ≤ 1)
    (hA1 : (4 * d' + 6) * ((2 * d' + 1) * (3 * α₀)) ≤ 1)
    (hA2 : xiC1 d' * (3 * α₀) ≤ thm73C1 d' L N)
    (hA3 : xiC1 d' * (3 * α₀) ≤ bgC0 d' L N)
    (hA4 : (xiC1 d' + 5) * (3 * α₀) ≤ bgC1 d' L N)
    (hA5 : 2 * (3 * α₀) ≤ deltaStar d' L N)
    (hA6 : bgK1 d' L N * xiC1 d' * (3 * α₀) ≤ deltaStar d' L N)
    (hA7 : (bgK1 d' L N * xiC1 d' + cK2 d' L N) * (3 * α₀) < bgC0 d' L N)
    (hA8 : bgK1 d' L N * xiC1 d' * (3 * α₀) ≤ δw)
    (hA9 : 2 * (3 * α₀) ≤ δw) :
    (2 * bgK1 d' L N + 2) * (xiC1 d' * (ε₀ + xiK2 d' L N *
          ((N : ℝ) * (2 * (c * epsSeq L α α₀ K))))) ≤ epsSeq L α α₀ K ∧
    xiC1 d' * (ε₀ + xiK2 d' L N * ((N : ℝ) * (2 * (c * epsSeq L α α₀ K)))) ≤
          bgC0 d' L N ∧
    xiC1 d' * (ε₀ + xiK2 d' L N * ((N : ℝ) * (2 * (c * epsSeq L α α₀ K)))) ≤
          bgC1 d' L N ∧
    (4 * d' + 6) * ((2 * d' + 1) * epsSeq L α α₀ K) ≤ 1 ∧
    xiC1 d' * epsSeq L α α₀ K ≤ thm73C1 d' L N ∧
    (N : ℝ) * (c * epsSeq L α α₀ K) ≤ 1 ∧
    xiC1 d' * (ε₀ + xiK2 d' L N * ((N : ℝ) * (2 * (c * epsSeq L α α₀ K)))) +
          5 * ((N : ℝ) * (c * epsSeq L α α₀ K)) ≤ bgC1 d' L N ∧
    (N : ℝ) * (2 * (c * epsSeq L α α₀ K)) ≤ deltaStar d' L N ∧
    bgK1 d' L N * (xiC1 d' * (ε₀ + xiK2 d' L N *
          ((N : ℝ) * (2 * (c * epsSeq L α α₀ K))))) ≤ deltaStar d' L N ∧
    bgK1 d' L N * (xiC1 d' * (ε₀ + xiK2 d' L N *
          ((N : ℝ) * (2 * (c * epsSeq L α α₀ K))))) +
          cK2 d' L N * ((N : ℝ) * (c * epsSeq L α α₀ K)) < bgC0 d' L N ∧
    bgK1 d' L N * (xiC1 d' * (ε₀ + xiK2 d' L N *
          ((N : ℝ) * (2 * (c * epsSeq L α α₀ K))))) ≤ δw ∧
    (N : ℝ) * (2 * (c * epsSeq L α α₀ K)) ≤ δw := by
  set E := epsSeq L α α₀ K with hE
  have hE0 : 0 ≤ E := epsSeq_nonneg' L α α₀ hα₀.le K
  have hE3 : E ≤ 3 * α₀ := epsSeq_le_three_alpha L hα₀ hα0 K
  have hb1 := bgK1_pos d' L N
  have hx1 := one_le_xiC1 d'
  have hk2 := cK2_pos d' L N
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hxk : 0 ≤ xiK2 d' L N := by unfold xiK2; positivity
  set Kl := (2 * bgK1 d' L N + 2) * xiC1 d' with hKl
  have hKl1 : 1 ≤ Kl := by rw [hKl]; nlinarith
  set X := ε₀ + xiK2 d' L N * ((N : ℝ) * (2 * (c * E))) with hX
  have hX0 : 0 ≤ X := by rw [hX]; positivity
  have hxe : xiK2 d' L N * ((N : ℝ) * (2 * (c * E))) * (2 * Kl) ≤ E := by
    have : 4 * Kl * xiK2 d' L N * (N : ℝ) * c * E ≤ 1 * E :=
      mul_le_mul_of_nonneg_right hcs hE0
    nlinarith
  have hroom : Kl * X ≤ E := by
    rw [hX]; nlinarith
  have hXE : X ≤ E := by nlinarith
  have hrm : (2 * bgK1 d' L N + 2) * (xiC1 d' * X) ≤ E := by
    have : (2 * bgK1 d' L N + 2) * (xiC1 d' * X) = Kl * X := by rw [hKl]; ring
    rw [this]; exact hroom
  have hxX : xiC1 d' * X ≤ xiC1 d' * (3 * α₀) :=
    mul_le_mul_of_nonneg_left (hXE.trans hE3) (by linarith)
  have hNcE : (N : ℝ) * (c * E) ≤ E := by
    have := mul_le_mul_of_nonneg_right hNc hE0
    nlinarith
  have hNcE3 : (N : ℝ) * (c * E) ≤ 3 * α₀ := hNcE.trans hE3
  have hN2 : (N : ℝ) * (2 * (c * E)) ≤ 2 * (3 * α₀) := by nlinarith
  have h3a : 0 ≤ 3 * α₀ := by linarith
  refine ⟨hrm, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hxX.trans hA3
  · linarith
  · have hP : (0 : ℝ) ≤ (4 * d' + 6) * (2 * d' + 1) := by positivity
    have := mul_le_mul_of_nonneg_left hE3 hP
    have e : (4 * (d' : ℝ) + 6) * ((2 * d' + 1) * E) = ((4 * d' + 6) * (2 * d' + 1)) * E := by ring
    rw [e]
    have e2 : (4 * (d' : ℝ) + 6) * ((2 * d' + 1) * (3 * α₀)) =
      ((4 * d' + 6) * (2 * d' + 1)) * (3 * α₀) := by ring
    rw [e2] at hA1
    exact (mul_le_mul_of_nonneg_left hE3 hP).trans hA1
  · exact (mul_le_mul_of_nonneg_left hE3 (by linarith)).trans hA2
  · have h13 := three_alpha_le_one_of_small hα₀.le hA1
    exact hNcE.trans (hE3.trans h13)
  · linarith
  · exact hN2.trans hA5
  · have := mul_le_mul_of_nonneg_left hxX hb1.le
    have e : bgK1 d' L N * (xiC1 d' * (3 * α₀)) = bgK1 d' L N * xiC1 d' * (3 * α₀) := by ring
    linarith
  · have h1 := mul_le_mul_of_nonneg_left hxX hb1.le
    have h2 := mul_le_mul_of_nonneg_left hNcE3 hk2.le
    have e : bgK1 d' L N * (xiC1 d' * (3 * α₀)) = bgK1 d' L N * xiC1 d' * (3 * α₀) := by ring
    have e2 : (bgK1 d' L N * xiC1 d' + cK2 d' L N) * (3 * α₀) =
      bgK1 d' L N * xiC1 d' * (3 * α₀) + cK2 d' L N * (3 * α₀) := by ring
    linarith
  · have := mul_le_mul_of_nonneg_left hxX hb1.le
    have e : bgK1 d' L N * (xiC1 d' * (3 * α₀)) = bgK1 d' L N * xiC1 d' * (3 * α₀) := by ring
    linarith
  · exact hN2.trans hA9

end Consts

section Composed

variable {d N₀ M : ℕ} [NeZero N₀] {L k : ℕ} [NeZero L] {v a : ℝ} {d' N : ℕ}

open Classical in
/-- **The volume-uniform coefficient bound of the last integral with only the setting data and the
thresholds as hypotheses.**  As `norm_coef_cutoff_class_le_levels`, with its thirteen numerical
premises replaced by the thresholds of `final_consts_of_large` (`ε₀` small against `ε_K`, `c`
small, `α₀` small, with `δw` the constant of the bound) and by `β₀` large
(`(B A₁ (4p)^p / (c α₀))^4 < β₀` for the row constant `B`).  The block datum in the class chart
(`hθ`) and `Dec2.OpSetting` are setting data. -/
theorem norm_coef_cutoff_class_le_levels_of_large (hd3 : 3 ≤ d') (hL3 : 3 ≤ L) :
    ∃ Kw δw : ℝ, 0 < Kw ∧ 0 < δw ∧
      ∀ {c α α₀ : ℝ} {N₁ m₁ kS : ℕ} [NeZero N₁] {ϱ : ℝ}
        (S : StepSetting d' L N₁ m₁ kS N ϱ) (e : L1Torus d N₀ ≃ S.U × Fin N)
        {P : Consts} {Tm : Terms d' L N₁ m₁ (kS + 1) N ϱ}
        (_ : SFTermClauses P
          (xiFieldDom S.a S.ν (epsSeq L α α₀) : FieldDom d' L N₁ m₁ (kS + 1) N ϱ) Tm)
        {K : ℕ} (_ : K ≤ kS) {hsep : ϱ ≤ minSep L (L ^ m₁)}
        (_ : ∀ j (hjk : j ≤ kS + 1), 1 ≤ j → j ≤ K → ∀ X, IsPolyDom P.m₀ j X →
          Tm.gs j X = localB j hjk X hsep)
        (_ : BgHyp d' L (kS + 1) ϱ S.a S.ν) (_ : 0 < S.a₁) {ε₀ : ℝ}
        (_ : XiCData S.G' S.a S.ν (kS + 1) 1 ε₀ S.D')
        (_ : Dec2.OpSetting (stepG d' L N₁ m₁ kS ϱ) S.a S.ν)
        (_ : 0 < N) (_ : 0 < c) (_ : 0 < α₀) (_ : 0 ≤ α)
        (_ : 2 * ((2 * bgK1 d' L N + 2) * xiC1 d') * ε₀ ≤ epsSeq L α α₀ K)
        (_ : 4 * ((2 * bgK1 d' L N + 2) * xiC1 d') * xiK2 d' L N * (N : ℝ) * c ≤ 1)
        (_ : (N : ℝ) * c ≤ 1)
        (_ : (4 * d' + 6) * ((2 * d' + 1) * (3 * α₀)) ≤ 1)
        (_ : xiC1 d' * (3 * α₀) ≤ thm73C1 d' L N)
        (_ : xiC1 d' * (3 * α₀) ≤ bgC0 d' L N)
        (_ : (xiC1 d' + 5) * (3 * α₀) ≤ bgC1 d' L N)
        (_ : 2 * (3 * α₀) ≤ deltaStar d' L N)
        (_ : bgK1 d' L N * xiC1 d' * (3 * α₀) ≤ deltaStar d' L N)
        (_ : (bgK1 d' L N * xiC1 d' + cK2 d' L N) * (3 * α₀) < bgC0 d' L N)
        (_ : bgK1 d' L N * xiC1 d' * (3 * α₀) ≤ δw)
        (_ : 2 * (3 * α₀) ≤ δw)
        (_ : 0 < d) (_ : 1 ≤ k) (_ : 0 ≤ v) (_ : v ≤ 1) (_ : 1 / 2 ≤ a) (_ : a ≤ 2)
        (_ : 7 / 8 * ((L : ℝ) ^ 2)⁻¹ < v) (_ : 0 < M) {κ : ℝ} (_ : 1 ≤ κ)
        (_ : 4 * (pdB d L * Real.exp (pdH d * κ)) ≤ M) (_ : 8 * κ * 7 ^ d ≤ pdEps d L * M)
        {A₁ β₀ : ℝ} {p : ℕ} {γ : Measure (L1Torus d N₀ → ℝ)}
        (_ : γ {ψ : L1Torus d N₀ → ℝ | ∀ y, |ψ y| ≤ pLog A₁ p (betaK d' L K β₀)} < ⊤)
        (_ : 1 ≤ p) (_ : 0 ≤ A₁) (_ : α ≤ ((d' : ℝ) - 2) * (1 / 4))
        (_ : (4 / 3 * (2 * Real.exp (pdH d * κ) * ballConst d (pdEps d L / 2)) /
          Real.sqrt (finalGap d L) * A₁ * (4 * (p : ℝ)) ^ p / (c * α₀)) ^ 4 < β₀) (_ : 1 < β₀)
        (_ : 0 ≤ P.E₀) (_ : L ^ P.m₀ ∣ N₁) (_ : aEnt d' L + 2 ≤ P.κ)
        (C : Finset (MacIdx d N₀ M)) (_ : C.Nonempty),
        ‖coef (fun s : MacIdx d N₀ M → ℂ =>
          ∫ ψ in {ψ : L1Torus d N₀ → ℝ | ∀ y, |ψ y| ≤ pLog A₁ p (betaK d' L K β₀)},
            (fun w : L1Torus d N₀ → ℂ => ∑ j ∈ Finset.Icc 1 K,
                Edens P.m₀ Tm j
                  (composedPairAtC S.a S.ν (Nat.le_succ kS) j (S.dataUC (fun q => w (e.symm q)))).1
                  (composedPairAtC S.a S.ν (Nat.le_succ kS) j (S.dataUC (fun q => w (e.symm q)))).2)
              (fun x => (fun q => S.psi0C (e q)) x +
                (((betaK d' L K β₀) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
                ∑ y, taggedCfin d L N₀ k M v a s x y * ((ψ y : ℝ) : ℂ)) ∂γ) C‖ ≤
          (γ {ψ : L1Torus d N₀ → ℝ | ∀ y, |ψ y| ≤ pLog A₁ p (betaK d' L K β₀)}).toReal *
            Real.exp (-(κ - 1) * C.card) *
           ((K : ℝ) * ((L : ℝ) ^ ((P.m₀ + m₁) * d') * c1 d' L * K0 d' L (P.κ - 1)) * P.E₀ *
              (((C.card * (8 * M + 1) ^ d * (L ^ kS) ^ d' *
                (2 * L ^ (kS + 1) + 2 * d' * L ^ (kS + 1) + 3) ^ d' : ℕ) : ℝ) *
                (1 + 20 * (N : ℝ) * Real.exp (gammaW d' * (2 * d')) * (Kw * cF d' L) *
                  ∑' m : ℕ, Real.exp (-(gammaW d' * m)) * ((m : ℝ) + 2) ^ d'))) := by
  obtain ⟨Kw, δw, hK, hδw, H⟩ := norm_coef_cutoff_class_le_levels (d := d) (N₀ := N₀) (M := M)
    (L := L) (k := k) (v := v) (a := a) (d' := d') (N := N) hd3 hL3
  refine ⟨Kw, δw, hK, hδw, ?_⟩
  intro c α α₀ N₁ m₁ kS _ ϱ S e P Tm hT K hKk hsep hgs HB ha₁ ε₀ hθ hOp hN hc hα₀ hα0 hεR hcs hNc
    hA1 hA2 hA3 hA4 hA5 hA6 hA7 hA8 hA9 hd hk hv0 hv1 ha1 ha2 hmass hM κ hκ hMB hMκ A₁ β₀ p γ hγ
    hp hA hα hβ hβ₁ hE₀ hNd hκP C hC
  have hε₀ : 0 ≤ ε₀ := by
    obtain ⟨_, _, _, _, ⟨_, h, _⟩, _⟩ := hθ
    exact h.le
  obtain ⟨hroom, hc0, hc1, hsmall, hth, hm1, hδ₂, hstar, hK1s, hsm, hKw, hδw'⟩ :=
    final_consts_of_large (d' := d') (N := N) (L := L) (K := K) hc hα₀ hα0 hε₀ hεR hcs hNc hA1 hA2
      hA3 hA4 hA5 hA6 hA7 hA8 hA9
  have hBnn : 0 ≤ 4 / 3 * (2 * Real.exp (pdH d * κ) * ballConst d (pdEps d L / 2)) /
      Real.sqrt (finalGap d L) := by
    have := ballConst_nonneg (d := d) (r := pdEps d L / 2) (by have := pdEps_pos (L := L) hd; positivity)
    positivity
  have hsize := size_of_beta_large hBnn hA hc hα₀ hβ
  exact H S e hT hKk hgs HB ha₁ hθ hOp hN hc hα₀ hα0 hroom hc0 hc1 hsmall hth hm1 hδ₂ hstar hK1s
    hsm hKw hδw' hd hk hv0 hv1 ha1 ha2 hmass hM hκ hMB hMκ hγ hp hA hα hβ₁ hsize hE₀ hNd hκP C hC

end Composed

end Balaban.Green
