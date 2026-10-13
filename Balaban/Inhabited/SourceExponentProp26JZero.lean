/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.SourceExponentFamily
public import Balaban.Fluctuation.StepComplexProp26JZero
public import Balaban.Fluctuation.StepComplexNonvanish

/-!
# The zero-class joint step at a free block datum

The physical source activity controls the two interpolation integrals at every datum in the
complex chart.  The numerical amplitude hypotheses are independent of the datum.
-/

@[expose] public section

namespace Balaban.Fluctuation.StepSetting.JointRep

open Balaban Balaban.Fluctuation Balaban.Inhabited Balaban.LargeField Balaban.Multiscale Balaban.Background
  Balaban.SmallField Balaban.SmallField.Def6 Balaban.Localization Balaban.Localization.LevelPair
  Balaban.Localization.I5Inhabited
  Balaban.Polymer
  Balaban.Inhabited.LevelStep MeasureTheory Set

variable {κmin : ℝ} (T : StepTower κmin)
  (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁] (h3N : 3 ∣ N₁) (hN : 5 < N₁)
  (ν : ℝ) (hνpos : 0 < ν) (hν : ν * 3 ^ (2 * (k + 1)) ≤ 1)
  (ρ : ℝ) (hρ : 0 < ρ) (β : ℝ) (hβρ : max 1 ρ ≤ β)
  (p₁ : ℝ) (hp0 : 0 < p₁) (D₀ : StepScaleData T k hk N₁ ν β p₁)
  (S : StepSetting 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) (hS : S = T.step k hk N₁ ν β p₁)
  (hp : 0 < S.p₁) (Jr : S.JointRep T.t (2 * p₁))
  (D : BgData S.G' 2) (hX : XiCData S.G' S.a S.ν (k + 1) 1 T.t D)
  (g : Fld 3 3 N₁ T.m₁ (k + 1) 2)
  (hg : g ∈ l1BallRho 3 3 N₁ T.m₁ (k + 1) 2 ρ)

include T k hk N₁ h3N hN ν hνpos hν ρ hρ β hβρ p₁ hp0 D₀ S hS hp Jr D hX g hg in
/-- The two joint interpolation integrals do not vanish at a free chart datum. -/
theorem nonvanishing_zeroClass_fromTower_freeDatum_rho
    (hεpos : 0 < 4 * (β * prop33EpsEtaScaled 3 3 2 T.m₁ k 1 1 T.BG T.BG₂ T.κ T.t
      (lvR T.κ T.t (β * 3 ^ k) p₁) 0 0 (ρ / β)))
    (hε : 4 * (β * prop33EpsEtaScaled 3 3 2 T.m₁ k 1 1 T.BG T.BG₂ T.κ T.t
      (lvR T.κ T.t (β * 3 ^ k) p₁) 0 0 (ρ / β)) ≤
      1 / (8 * (2 * (K0 3 3 T.κ0 + 1)) ^ 3 * c1 3 3 *
        Real.exp (((2 * T.κdec - 1) - 2 * T.κ0) * cG 3 3 +
          c1 3 3 + (0 : ℝ) * cG 3 3))) :
    (∀ s ∈ Icc (0 : ℝ) 1,
      (∫ x : S.E, Complex.exp
        (Jr.W1 (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁))
          (rawOf D, (s : ℂ) • yhat x)) ∂S.nuFl) ≠ 0) ∧
    (∀ t ∈ Icc (0 : ℝ) 1,
      (∫ x : S.E, Complex.exp
        (Jr.W1 (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) (rawOf D, yhat x) +
          Jr.W2 (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) g
            (rawOf D, (t : ℂ) • yhat x)) ∂S.nuFl) ≠ 0) := by
  classical
  obtain ⟨𝒴, hdom, εU, hεU, -, A, hA⟩ :=
    sourceExponentFamily_freeDatum_slice_rho T k hk N₁ h3N hN ν hνpos hν
      ρ hρ β hβρ p₁ hp0 D₀ S hS hp D hX g hg Jr
  have hN3 : 3 ^ 1 ∣ N₁ := by simpa using h3N
  have hKc : K0 3 3 T.κ0 + 1 ≤ 2 * (K0 3 3 T.κ0 + 1) := by
    have := K0_pos 3 3 T.κ0
    linarith
  have hZ : ∀ p ∈ stepSegments,
      (∫ x : S.E, Complex.exp
        (Jr.W1 (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁))
          (rawOf D, (p.1 : ℂ) • yhat x) +
        Jr.W2 (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) g
          (rawOf D, (p.2 : ℂ) • yhat x)) ∂S.nuFl) ≠ 0 := by
    intro p hpseg
    have hnum := labelAct_integral_eq_exp (S.blockSplit 1 hp).μ hN3 (A p)
      T.κ0_ent hKc (by rw [hεU]; exact hεpos) (le_refl 0)
      T.rate_rel (by rw [hεU]; exact hε)
    obtain ⟨Lg, hLg, -⟩ := hnum
    have hmeas : Measurable (fun Φ => Complex.exp (∑ y, (A p).H y Φ)) :=
      Complex.measurable_exp.comp (Finset.measurable_sum _ fun y _ => (A p).meas y)
    have hEq : (∫ x : S.E, Complex.exp
        (Jr.W1 (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁))
          (rawOf D, (p.1 : ℂ) • yhat x) +
        Jr.W2 (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) g
          (rawOf D, (p.2 : ℂ) • yhat x)) ∂S.nuFl) =
        ∫ Φ, Complex.exp (∑ y, (A p).H y Φ) ∂(Measure.pi (S.blockSplit 1 hp).μ) := by
      rw [← (S.blockSplit 1 hp).map_eq,
        integral_map (S.blockSplit 1 hp).meas.aemeasurable hmeas.aestronglyMeasurable]
      refine integral_congr_ae ?_
      filter_upwards [hA p hpseg] with x hx
      have hhat : S.hatC x = yhat x := rfl
      simpa only [hhat] using congrArg Complex.exp hx
    rw [hEq, hLg]
    exact Complex.exp_ne_zero _
  constructor
  · intro s hs
    have hz := hZ (s, 0) (Or.inl ⟨hs, rfl⟩)
    simpa only [Complex.ofReal_zero, zero_smul, StepSetting.JointRep.W2,
      sub_self, add_zero] using hz
  · intro t ht
    simpa only [Complex.ofReal_one, one_smul] using
      (hZ (1, t) (Or.inr ⟨rfl, ht⟩))

include T k hk N₁ h3N hN ν hνpos hν ρ hρ β hβρ p₁ hp0 D₀ S hS hp Jr D hX g hg in
/-- Proposition 2.6 for the zero class at every datum in the complex chart.  The numerical
amplitude margin is the one used by the label cluster expansion. -/
theorem prop26J_step_zeroClass
    (hεpos : 0 < 4 * (β * prop33EpsEtaScaled 3 3 2 T.m₁ k 1 1 T.BG T.BG₂ T.κ T.t
      (lvR T.κ T.t (β * 3 ^ k) p₁) 0 0 (ρ / β)))
    (hε : 4 * (β * prop33EpsEtaScaled 3 3 2 T.m₁ k 1 1 T.BG T.BG₂ T.κ T.t
      (lvR T.κ T.t (β * 3 ^ k) p₁) 0 0 (ρ / β)) ≤
      1 / (8 * (2 * (K0 3 3 T.κ0 + 1)) ^ 3 * c1 3 3 *
        Real.exp (((2 * T.κdec - 1) - 2 * T.κ0) * cG 3 3 +
          c1 3 3 + (0 : ℝ) * cG 3 3))) :
    Jr.TstepJ (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) g (rawOf D) =
      Complex.exp (
        -(S.β : ℂ) * actionRawC S.G' S.a S.ν D.Ψ D.h (Jr.F₀ (rawOf D)).1 +
        Jr.EJ (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) (rawOf D, 0) -
        (S.Eppp (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) : ℂ) * (S.nU : ℂ) +
        Jr.FcJ (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) g (rawOf D, 0) -
        (1 / 2 : ℂ) * ∑ y : S.U, ∑ i : Fin 2,
          (decLog S.G' S.a S.a₁ S.ν (Jr.F₀ (rawOf D)).2 (fun _ => 1)
            (svec S.G' (Jr.F₀ (rawOf D)).1) (unitQ S.G') (unitP S.G'))
              (y, i) (y, i) +
        S.avgJ (fun _ => 0)
          (Jr.W1 (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)))
          (Jr.W1 (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁))) (rawOf D) +
        S.avgJ (Jr.W1 (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)))
          (Jr.W2 (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) g)
          (Jr.W2 (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) g) (rawOf D)) := by
  subst hS
  let S := T.step k hk N₁ ν β p₁
  have hβ0 : 0 < β := lt_of_lt_of_le zero_lt_one (le_trans (le_max_left _ _) hβρ)
  have hβ : 0 < S.β := hβ0
  have hpp : S.p₁ < 2 * p₁ := D₀.p_lt
  have hX' : XiCData S.G' S.a S.ν (k + 1) 1 T.t D := hX
  have hreg := Jr.isC1Family_zeroClass_freeDatum hp hpp D hX' g
  obtain ⟨hnv1, hnv2⟩ := Jr.nonvanishing_zeroClass_fromTower_freeDatum_rho
    T k hk N₁ h3N hN ν hνpos hν ρ hρ β hβρ p₁ hp0 D₀ S rfl hp D hX' g hg
    hεpos hε
  have hcψ : p₁ ≤ lvCpsi T.κ T.t (β * 3 ^ k) := by
    have hpos : 0 < lvR T.κ T.t (β * 3 ^ k) p₁ * p₁ :=
      mul_pos D₀.r_pos hp0
    nlinarith [D₀.ray_margin]
  have hCsup : 0 ≤ covSupConstC 3 3 2 (compWeight 3 S.a₁ k) T.κ := by
    have hmem := compWeight_three_mem hk
    have hcomp : 0 < compWeight 3 S.a₁ k := by
      have ha₁ : S.a₁ = 1 := rfl
      rw [ha₁]
      linarith [hmem.1]
    exact covSupConstC_nonneg (by norm_num) (by norm_num) hcomp T.κ
  obtain ⟨R0⟩ := D₀.ray
  have hpow : 0 ≤ S.betaU ^ (-(1 / 2 : ℝ)) :=
    Real.rpow_nonneg R0.betaU_pos.le _
  have hδ : Real.sqrt 2 * (S.betaU ^ (-(1 / 2 : ℝ)) *
      (covSupConstC 3 3 2 (compWeight 3 S.a₁ k) T.κ * S.p₁)) < T.t := by
    refine lt_of_le_of_lt ?_ D₀.fl_radius
    rw [S.norm_betaU_rpow hβ0.le]
    have hsp : S.p₁ ≤ lvCpsi T.κ T.t (β * 3 ^ k) := by
      exact hcψ
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hsp hCsup) hpow)
      (Real.sqrt_nonneg _)
  exact Jr.prop26J_step_unbounded (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁))
    D₀.core T.large_block T.dom_margin T.coer_margin T.δc_small one_pos T.c7_cap
    (R := 2) (by norm_num) T.bg1_cap hβ hp hδ D hX' g hreg hnv1 hnv2

end Balaban.Fluctuation.StepSetting.JointRep
