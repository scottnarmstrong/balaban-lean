/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.StepComplexOutAnalytic
public import Balaban.Fluctuation.StepComplexWitness
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The complex step with all premises discharged at a nonreal block datum (non-vacuity)

The local identities of `StepComplexLocal`, `StepComplexObs`, Proposition 2.6 with a source
(`StepComplexSource`) and the analyticity of the outputs in the block datum
(`StepComplexOutAnalytic`) have the hypothesis bundle of the complex chart of RAY-CHART §1 and the
inputs `ClassRegularLocC`, `ClassRegularObsC`, `ClassRegularC`, `StepNonvanishingC`
(`StepActivityBoundC`), `EdensAnalyticOnPath`, `FlocAnalyticOnPath`, `MlocAnalyticOnPath`, and use
the bundle `JointRep`.  This file shows that all of them hold together, at the chart constants of
`exists_chart_params` (`d = L = 3`, `N₁ = 6`, `k = 1`, `N = 2`), for the class with zero old terms
and every source `g` with `|g| ≤ γ` for some `γ > 0` (in particular for nonzero sources):

* `exists_complexStep_cert_of_xiCData`: for every block datum `D` of the chart with `h ≡ e₀` (real
  or complex) there are `β > 0`, a radius `p > 0` and `γ > 0` such that at the step datum
  `chartSetting` with `θ = D`: all the bundles hold; `∑_z ℰ₀(z) = ℰ₀`; `ℱ₀ = ⟨g, β^{-1/2} ℳ₀⟩`;
  Proposition 2.6 holds for the holomorphic objects; the fluctuation integral is the value at `D` of
  a function analytic on the whole chart; and `ℰ₀ + ℱ₀(g)`, `ℳ₀(y; g)_i` are the values at `D` of
  functions analytic at `D`;
* `exists_complexStep_nonreal_datum`: the same at a block datum which is **not real**
  (`θ ≡ e₀ + i τ e₁`, `τ > 0`);
* `exists_complexStep_real_datum`: the same at the real datum `θ ≡ h ≡ e₀`.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization Balaban.Inhabited
  Balaban.Localization.I5Inhabited Balaban.SmallField.Def6 Balaban.SmallField Finset Filter
  Topology

/-- **The complex step with all premises discharged, at a given block datum of the chart**
(`d = L = 3`, `N₁ = 6`, `k = 1`, `N = 2`, `a₁ = 1`, `ν = 0`): for the constants of
`exists_chart_params` and every block datum `D` of `Ξ^c(𝔹_2; 1, t)` with `h ≡ e₀` (real or complex),
there are `β > 0`, a radius `p > 0` and a size `γ > 0` such that the step datum
`S = chartSetting m₁ D hDh β p` satisfies, for the class with zero old terms: `ClassRegularLocC`,
`EdensAnalyticOnPath`, `JointRep`, and for every source `g` with `|g(y,i)| ≤ γ`: `ClassRegularC`,
`ClassRegularObsC`, `FlocAnalyticOnPath`, `MlocAnalyticOnPath`, `StepActivityBoundC`; the identities
`∑_z ℰ₀^{(k+1)}(z) = ℰ₀^{(k+1)}` (`sum_E0locC`), `ℱ₀^{(k+1)}(g) = ⟨g, β_k^{-1/2} ℳ₀^{(k+1)}(g)⟩₁`
(`F0C_eq_pair`) and (2.6) (`prop26C_zeroClass`); `TstepC` is the value at `D` of a function
analytic on the whole chart, and `ℰ₀ + ℱ₀(g)`, `ℳ₀(y; g)_i` are the values at `D` of functions
analytic at `D`. -/
theorem exists_complexStep_cert_of_xiCData {m₁ : ℕ} {c BG κ t c₂ BG₂ δc : ℝ}
    (hFl : FlCore 2 (GP m₁ (rhoSep m₁)) (stepG 3 3 6 m₁ 1 (rhoSep m₁)) 1 0 c BG κ t
      (levelKc 3 3) (Cchi 3 3) c₂ BG₂ t)
    (hMX : cstarX 3 3 * Real.exp ((N0 3 3 : ℝ) * κ) ≤ ((3 : ℕ) : ℝ) ^ m₁)
    (hdm : decDomMargin 3 3 2 BG κ (xiC1 3 * t) < δc)
    (hα : K4 3 3 2 BG κ * (xiC1 3 * t) < coerciveConst 3 / 2)
    (hsm : δc ^ 2 * smallConstX 3 3 κ ≤ 1 / 4)
    (hc7 : c7 3 3 2 BG κ ≤ thm73C3 3 3 2)
    (hsmR : 2 * (compC4 3 * (bgK1 3 3 2 * (xiC1 3 * t))) + 5 * (2 * t) ≤ bgC1 3 3 2)
    (D : BgData (GP m₁ (rhoSep m₁)) 2)
    (hXi : XiCData (GP m₁ (rhoSep m₁)) (compWeight 3 1) 0 2 1 t D)
    (hDh : ∀ x i, D.h x i = (unitVec hN2 i : ℂ)) :
    ∃ β p γ : ℝ, 0 < β ∧ 0 < p ∧ 0 < γ ∧
      ∀ S : StepSetting 3 3 6 m₁ 1 2 (rhoSep m₁), S = chartSetting m₁ D hDh β p →
        S.ClassRegularLocC (zeroClass 3 3 6 m₁ 1 2 (rhoSep m₁)) ∧
        S.EdensAnalyticOnPath (zeroClass 3 3 6 m₁ 1 2 (rhoSep m₁)) ∧
        Nonempty (S.JointRep t 2) ∧
        ∀ g : Fld 3 3 6 m₁ 2 2, (∀ y i, ‖g y i‖ ≤ γ) →
          S.ClassRegularC (zeroClass 3 3 6 m₁ 1 2 (rhoSep m₁)) g ∧
          S.ClassRegularObsC (zeroClass 3 3 6 m₁ 1 2 (rhoSep m₁)) g ∧
          S.FlocAnalyticOnPath (zeroClass 3 3 6 m₁ 1 2 (rhoSep m₁)) g ∧
          (∀ y i, S.MlocAnalyticOnPath (zeroClass 3 3 6 m₁ 1 2 (rhoSep m₁)) g y i) ∧
          Nonempty (StepActivityBoundC S (zeroClass 3 3 6 m₁ 1 2 (rhoSep m₁)) g) ∧
          (∑ z : Torus 3 (6 * 3 ^ m₁ * 3 ^ (1 + 1 - (1 + 1))),
            S.E0locC (zeroClass 3 3 6 m₁ 1 2 (rhoSep m₁)) z =
              S.E0C (zeroClass 3 3 6 m₁ 1 2 (rhoSep m₁))) ∧
          S.F0C (zeroClass 3 3 6 m₁ 1 2 (rhoSep m₁)) g = ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
            ∑ y : CTorus 3 3 6 m₁ 2, ∑ i : Fin 2,
              g y i * S.M0C (zeroClass 3 3 6 m₁ 1 2 (rhoSep m₁)) g y i ∧
          S.TstepC (zeroClass 3 3 6 m₁ 1 2 (rhoSep m₁)) g = Complex.exp (-(S.β : ℂ) * S.AnewC +
            EcompAtC (zeroClass 3 3 6 m₁ 1 2 (rhoSep m₁)).m₀
              (zeroClass 3 3 6 m₁ 1 2 (rhoSep m₁)).Tm S.a S.ν (Nat.le_succ 1) S.psiKdC -
            (S.Eppp (zeroClass 3 3 6 m₁ 1 2 (rhoSep m₁)) : ℂ) * (S.nU : ℂ) +
            FcompAtC (zeroClass 3 3 6 m₁ 1 2 (rhoSep m₁)).m₀
              (zeroClass 3 3 6 m₁ 1 2 (rhoSep m₁)).Tm S.a S.ν (Nat.le_succ 1) S.psiKdC g +
            S.E0C (zeroClass 3 3 6 m₁ 1 2 (rhoSep m₁)) +
            S.F0C (zeroClass 3 3 6 m₁ 1 2 (rhoSep m₁)) g) ∧
          (∃ F : RawData 3 3 (6 * 3 ^ m₁) 2 2 → ℂ,
            AnalyticOnNhd ℂ F (XiCRaw S.G' S.a S.ν 2 1 t) ∧
            F (rawOf S.D') = S.TstepC (zeroClass 3 3 6 m₁ 1 2 (rhoSep m₁)) g) ∧
          (∃ F : RawData 3 3 (6 * 3 ^ m₁) 2 2 → ℂ, AnalyticAt ℂ F (rawOf S.D') ∧
            F (rawOf S.D') = S.E0C (zeroClass 3 3 6 m₁ 1 2 (rhoSep m₁)) +
              S.F0C (zeroClass 3 3 6 m₁ 1 2 (rhoSep m₁)) g) ∧
          (∀ (y : CTorus 3 3 6 m₁ 2) (i : Fin 2), ∃ F : RawData 3 3 (6 * 3 ^ m₁) 2 2 → ℂ,
            AnalyticAt ℂ F (rawOf S.D') ∧
            F (rawOf S.D') = S.M0C (zeroClass 3 3 6 m₁ 1 2 (rhoSep m₁)) g y i) := by
  classical
  have ht0 : 0 < t := hFl.eps_pos
  set cS : ℝ := covSupConstC 3 3 2 (compWeight 3 1 1) κ with hcS
  set s2 : ℝ := Real.sqrt ((2 : ℕ) : ℝ) with hs2
  have hs20 : 0 ≤ s2 := Real.sqrt_nonneg _
  set A : ℝ := s2 * (|cS| * 2) with hA
  have hA0 : 0 ≤ A := by positivity
  set T : ℝ := A / t + 1 with hTdef
  have hT : 0 < T := by positivity
  set S₀ : StepSetting 3 3 6 m₁ 1 2 (rhoSep m₁) := chartSetting m₁ D hDh (T ^ 2 / 3) 1 with hS₀
  have hβ : 0 < S₀.β := by
    show 0 < T ^ 2 / 3
    positivity
  have hbetaU : S₀.betaU = T ^ 2 := by
    unfold StepSetting.betaU
    show T ^ 2 / 3 * (((3 : ℕ) : ℝ) ^ 1) ^ 3 / (((3 : ℕ) : ℝ) ^ 1) ^ 2 = T ^ 2
    norm_num
    ring
  have hδ₁ : Real.sqrt ((2 : ℕ) : ℝ) * (S₀.betaU ^ (-(1 / 2 : ℝ)) *
      (covSupConstC 3 3 2 (compWeight 3 S₀.a₁ 1) κ * 2)) < t := by
    rw [hbetaU]
    have e : (T ^ 2) ^ (-(1 / 2) : ℝ) = T⁻¹ := by
      rw [Real.rpow_neg (by positivity), ← Real.sqrt_eq_rpow, Real.sqrt_sq hT.le]
    rw [e]
    show s2 * (T⁻¹ * (cS * 2)) < t
    have hTi : 0 ≤ T⁻¹ := inv_nonneg.2 hT.le
    have h1 : s2 * (T⁻¹ * (cS * 2)) ≤ A / T := by
      have hle : cS * 2 ≤ |cS| * 2 := by nlinarith [le_abs_self cS]
      have h2 : s2 * (T⁻¹ * (cS * 2)) ≤ s2 * (T⁻¹ * (|cS| * 2)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hle hTi) hs20
      have h3 : s2 * (T⁻¹ * (|cS| * 2)) = A / T := by rw [hA]; field_simp
      linarith
    have h4 : A / T < t := by
      rw [div_lt_iff₀ hT]
      have : t * T = A + t := by rw [hTdef]; field_simp
      linarith
    linarith
  have ha₁ : 0 < S₀.a₁ := one_pos
  have h2 : (0 : ℝ) < 2 := by norm_num
  have hR : (1 : ℝ) < 2 := by norm_num
  obtain ⟨p, γ, hp0, hpp, hγ, hact⟩ := S₀.exists_activityBoundC_zeroClass_source (pp := 2) hFl
    hMX hdm hα hsm ha₁ hc7 (R := 2) hR hsmR hβ h2 hδ₁ hXi
  refine ⟨T ^ 2 / 3, p, γ, hβ, hp0, hγ, ?_⟩
  rintro S rfl
  set S₁ : StepSetting 3 3 6 m₁ 1 2 (rhoSep m₁) := S₀.withRadius p with hS₁
  have hp1 : 0 < S₁.p₁ := hp0
  have hlt : S₁.p₁ < 2 := hpp
  have hβ1 : 0 < S₁.β := hβ
  refine ⟨S₁.classRegularLocC_zeroClass hFl hMX hdm hα hsm ha₁ hc7 hR hsmR hβ1 h2 hδ₁ hXi hlt,
    S₁.edensAnalyticOnPath_zeroClass,
    S₁.nonempty_jointRep (eps := t) hFl hMX hdm hα hsm ha₁ hc7 hR hsmR hβ1.le h2 hδ₁, ?_⟩
  intro g hg
  obtain ⟨I⟩ := hact g hg
  have hnv : S₁.StepNonvanishingC (zeroClass 3 3 6 m₁ 1 2 (rhoSep m₁)) g :=
    stepNonvanishingC_of_activityBoundC I
  refine ⟨S₁.classRegularC_zeroClass hFl hMX hdm hα hsm ha₁ hc7 hR hsmR hβ1.le h2 hδ₁ hXi hp1 hlt
      g,
    S₁.classRegularObsC_zeroClass hFl hMX hdm hα hsm ha₁ hc7 hR hsmR hβ1 hp1 hlt hδ₁ hXi g,
    S₁.flocAnalyticOnPath_zeroClass g, fun y i => S₁.mlocAnalyticOnPath_zeroClass g y i, ⟨I⟩,
    S₁.sum_E0locC_zeroClass hFl hMX hdm hα hsm ha₁ hc7 hR hsmR hβ1 hp1 hlt hδ₁ hXi g hnv,
    S₁.F0C_eq_pair_zeroClass hFl hMX hdm hα hsm ha₁ hc7 hR hsmR hβ1 hp1 hlt hδ₁ hXi g hnv,
    S₁.prop26C_zeroClass hFl hMX hdm hα hsm ha₁ hc7 hR hsmR hβ1 hp1 hlt hδ₁ hXi g hnv, ?_, ?_, ?_⟩
  · obtain ⟨F, hFan, hF⟩ := S₁.exists_analytic_TstepC_zeroClass (eps := t) hFl hMX hdm hα hsm ha₁
      hc7 hR hsmR hβ1.le hp1 hlt hδ₁ g
    exact ⟨F, hFan, hF S₁.D' S₁.hh₀ hXi⟩
  · obtain ⟨F, hF⟩ := S₁.exists_analyticAt_E0C_add_F0C_zeroClass (eps := t) hFl hMX hdm hα hsm ha₁
      hc7 hR hsmR hβ1.le hp1 hlt hδ₁ g
    exact ⟨F, (hF S₁.D' S₁.hh₀ hXi).2 hnv, (hF S₁.D' S₁.hh₀ hXi).1⟩
  · intro y i
    obtain ⟨F, hF⟩ := S₁.exists_analyticAt_M0C_zeroClass (eps := t) hFl hMX hdm hα hsm ha₁
      hc7 hR hsmR hβ1.le hp1 hlt hδ₁ g y i
    exact ⟨F, (hF S₁.D' S₁.hh₀ hXi).2 hnv, (hF S₁.D' S₁.hh₀ hXi).1⟩

/-- **The complex step at a nonreal block datum, with all premises discharged** (`d = L = 3`,
`N₁ = 6`, `k = 1`, `N = 2`): there are a step datum `S` whose block datum `θ` is **not real**
(`θ ≡ e₀ + i τ e₁`, `τ > 0`; `h ≡ e₀`), `β > 0`, `p₁ > 0`, lying in the chart `Ξ^c(𝔹_2; 1, t)`
under `FlCore`, and a size `γ > 0`, such that for the class with zero old terms and every source
`g` with `|g(y,i)| ≤ γ` (there are nonzero ones): every hypothesis bundle of the complex step holds
(`ClassRegularLocC`, `ClassRegularObsC`, `ClassRegularC`, `StepActivityBoundC`,
`EdensAnalyticOnPath`, `FlocAnalyticOnPath`, `MlocAnalyticOnPath`, `JointRep`), and

* `∑_z ℰ₀^{(k+1)}(z) = ℰ₀^{(k+1)}` (T1), `ℱ₀^{(k+1)}(g) = ⟨g, β_k^{-1/2} ℳ₀^{(k+1)}(g)⟩₁` (T2),
* the identity (2.6) of Proposition 2.6 for the holomorphic objects, with the source `g`,
* `TstepC` is the value at `θ` of a function of the raw datum analytic on the whole chart, and
  `ℰ₀^{(k+1)} + ℱ₀^{(k+1)}(g)`, `ℳ₀^{(k+1)}(y; g)_i` are the values at `θ` of functions analytic at
  `θ` (T5).

In particular none of the hypothesis bundles is vacuous off the real chart. -/
theorem exists_complexStep_nonreal_datum :
    ∃ (m₁ : ℕ) (S : StepSetting 3 3 6 m₁ 1 2 (rhoSep m₁)) (t γ : ℝ),
      ¬ S.D'.IsReal ∧ 0 < S.β ∧ 0 < S.p₁ ∧ 0 < γ ∧
      (∃ c BG κ c₂ BG₂ : ℝ,
        FlCore 2 S.G' (stepG 3 3 6 m₁ 1 (rhoSep m₁)) S.a₁ S.ν c BG κ t (levelKc 3 3) (Cchi 3 3)
          c₂ BG₂ t) ∧
      XiCData S.G' S.a S.ν 2 1 t S.D' ∧
      (∃ g : Fld 3 3 6 m₁ 2 2, g ≠ 0 ∧ ∀ y i, ‖g y i‖ ≤ γ) ∧
      S.ClassRegularLocC (zeroClass 3 3 6 m₁ 1 2 (rhoSep m₁)) ∧
      S.EdensAnalyticOnPath (zeroClass 3 3 6 m₁ 1 2 (rhoSep m₁)) ∧
      Nonempty (S.JointRep t 2) ∧
      ∀ g : Fld 3 3 6 m₁ 2 2, (∀ y i, ‖g y i‖ ≤ γ) →
        S.ClassRegularC (zeroClass 3 3 6 m₁ 1 2 (rhoSep m₁)) g ∧
        S.ClassRegularObsC (zeroClass 3 3 6 m₁ 1 2 (rhoSep m₁)) g ∧
        S.FlocAnalyticOnPath (zeroClass 3 3 6 m₁ 1 2 (rhoSep m₁)) g ∧
        (∀ y i, S.MlocAnalyticOnPath (zeroClass 3 3 6 m₁ 1 2 (rhoSep m₁)) g y i) ∧
        Nonempty (StepActivityBoundC S (zeroClass 3 3 6 m₁ 1 2 (rhoSep m₁)) g) ∧
        (∑ z : Torus 3 (6 * 3 ^ m₁ * 3 ^ (1 + 1 - (1 + 1))),
          S.E0locC (zeroClass 3 3 6 m₁ 1 2 (rhoSep m₁)) z =
            S.E0C (zeroClass 3 3 6 m₁ 1 2 (rhoSep m₁))) ∧
        S.F0C (zeroClass 3 3 6 m₁ 1 2 (rhoSep m₁)) g = ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
          ∑ y : CTorus 3 3 6 m₁ 2, ∑ i : Fin 2,
            g y i * S.M0C (zeroClass 3 3 6 m₁ 1 2 (rhoSep m₁)) g y i ∧
        S.TstepC (zeroClass 3 3 6 m₁ 1 2 (rhoSep m₁)) g = Complex.exp (-(S.β : ℂ) * S.AnewC +
          EcompAtC (zeroClass 3 3 6 m₁ 1 2 (rhoSep m₁)).m₀
            (zeroClass 3 3 6 m₁ 1 2 (rhoSep m₁)).Tm S.a S.ν (Nat.le_succ 1) S.psiKdC -
          (S.Eppp (zeroClass 3 3 6 m₁ 1 2 (rhoSep m₁)) : ℂ) * (S.nU : ℂ) +
          FcompAtC (zeroClass 3 3 6 m₁ 1 2 (rhoSep m₁)).m₀
            (zeroClass 3 3 6 m₁ 1 2 (rhoSep m₁)).Tm S.a S.ν (Nat.le_succ 1) S.psiKdC g +
          S.E0C (zeroClass 3 3 6 m₁ 1 2 (rhoSep m₁)) +
          S.F0C (zeroClass 3 3 6 m₁ 1 2 (rhoSep m₁)) g) ∧
        (∃ F : RawData 3 3 (6 * 3 ^ m₁) 2 2 → ℂ,
          AnalyticOnNhd ℂ F (XiCRaw S.G' S.a S.ν 2 1 t) ∧
          F (rawOf S.D') = S.TstepC (zeroClass 3 3 6 m₁ 1 2 (rhoSep m₁)) g) ∧
        (∃ F : RawData 3 3 (6 * 3 ^ m₁) 2 2 → ℂ, AnalyticAt ℂ F (rawOf S.D') ∧
          F (rawOf S.D') = S.E0C (zeroClass 3 3 6 m₁ 1 2 (rhoSep m₁)) +
            S.F0C (zeroClass 3 3 6 m₁ 1 2 (rhoSep m₁)) g) ∧
        (∀ (y : CTorus 3 3 6 m₁ 2) (i : Fin 2), ∃ F : RawData 3 3 (6 * 3 ^ m₁) 2 2 → ℂ,
          AnalyticAt ℂ F (rawOf S.D') ∧
          F (rawOf S.D') = S.M0C (zeroClass 3 3 6 m₁ 1 2 (rhoSep m₁)) g y i) := by
  obtain ⟨m₁, c, BG, κ, t, c₂, BG₂, δc, ht0, hFl, hMX, hdm, hα, hsm, hc7, hsmR⟩ :=
    exists_chart_params
  obtain ⟨D, hXi, hDh, hnr⟩ := exists_nonreal_xiCData (bgHyp_rho m₁) (GP m₁ (rhoSep m₁))
    (fun x => (isLevel_GP m₁ x).1) (by norm_num : 1 < 2) (by simp) ht0
  obtain ⟨β, p, γ, hβ, hp, hγ, hcert⟩ := exists_complexStep_cert_of_xiCData hFl hMX hdm hα hsm
    hc7 hsmR D hXi hDh
  refine ⟨m₁, chartSetting m₁ D hDh β p, t, γ, hnr, hβ, hp, hγ, ⟨c, BG, κ, c₂, BG₂, hFl⟩, hXi,
    ⟨fun _ _ => (γ : ℂ), ?_, fun y i => ?_⟩, hcert _ rfl⟩
  · intro h0
    have := congrFun (congrFun h0 0) 0
    simp only [Pi.zero_apply, Complex.ofReal_eq_zero] at this
    exact hγ.ne' this
  · rw [Complex.norm_real, Real.norm_of_nonneg hγ.le]

/-- **The complex step at the real block datum `θ ≡ h ≡ e₀`, with all premises discharged** (the
block datum `witnessD` of the landed witnesses): the statement of `exists_complexStep_nonreal_datum`
at a real datum. -/
theorem exists_complexStep_real_datum :
    ∃ (m₁ : ℕ) (S : StepSetting 3 3 6 m₁ 1 2 (rhoSep m₁)) (t γ : ℝ),
      S.D'.IsReal ∧ 0 < S.β ∧ 0 < S.p₁ ∧ 0 < γ ∧
      (∃ c BG κ c₂ BG₂ : ℝ,
        FlCore 2 S.G' (stepG 3 3 6 m₁ 1 (rhoSep m₁)) S.a₁ S.ν c BG κ t (levelKc 3 3) (Cchi 3 3)
          c₂ BG₂ t) ∧
      XiCData S.G' S.a S.ν 2 1 t S.D' ∧
      S.ClassRegularLocC (zeroClass 3 3 6 m₁ 1 2 (rhoSep m₁)) ∧
      S.EdensAnalyticOnPath (zeroClass 3 3 6 m₁ 1 2 (rhoSep m₁)) ∧
      Nonempty (S.JointRep t 2) ∧
      ∀ g : Fld 3 3 6 m₁ 2 2, (∀ y i, ‖g y i‖ ≤ γ) →
        S.ClassRegularC (zeroClass 3 3 6 m₁ 1 2 (rhoSep m₁)) g ∧
        S.ClassRegularObsC (zeroClass 3 3 6 m₁ 1 2 (rhoSep m₁)) g ∧
        S.FlocAnalyticOnPath (zeroClass 3 3 6 m₁ 1 2 (rhoSep m₁)) g ∧
        (∀ y i, S.MlocAnalyticOnPath (zeroClass 3 3 6 m₁ 1 2 (rhoSep m₁)) g y i) ∧
        Nonempty (StepActivityBoundC S (zeroClass 3 3 6 m₁ 1 2 (rhoSep m₁)) g) ∧
        (∑ z : Torus 3 (6 * 3 ^ m₁ * 3 ^ (1 + 1 - (1 + 1))),
          S.E0locC (zeroClass 3 3 6 m₁ 1 2 (rhoSep m₁)) z =
            S.E0C (zeroClass 3 3 6 m₁ 1 2 (rhoSep m₁))) ∧
        S.F0C (zeroClass 3 3 6 m₁ 1 2 (rhoSep m₁)) g = ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
          ∑ y : CTorus 3 3 6 m₁ 2, ∑ i : Fin 2,
            g y i * S.M0C (zeroClass 3 3 6 m₁ 1 2 (rhoSep m₁)) g y i ∧
        S.TstepC (zeroClass 3 3 6 m₁ 1 2 (rhoSep m₁)) g = Complex.exp (-(S.β : ℂ) * S.AnewC +
          EcompAtC (zeroClass 3 3 6 m₁ 1 2 (rhoSep m₁)).m₀
            (zeroClass 3 3 6 m₁ 1 2 (rhoSep m₁)).Tm S.a S.ν (Nat.le_succ 1) S.psiKdC -
          (S.Eppp (zeroClass 3 3 6 m₁ 1 2 (rhoSep m₁)) : ℂ) * (S.nU : ℂ) +
          FcompAtC (zeroClass 3 3 6 m₁ 1 2 (rhoSep m₁)).m₀
            (zeroClass 3 3 6 m₁ 1 2 (rhoSep m₁)).Tm S.a S.ν (Nat.le_succ 1) S.psiKdC g +
          S.E0C (zeroClass 3 3 6 m₁ 1 2 (rhoSep m₁)) +
          S.F0C (zeroClass 3 3 6 m₁ 1 2 (rhoSep m₁)) g) ∧
        (∃ F : RawData 3 3 (6 * 3 ^ m₁) 2 2 → ℂ,
          AnalyticOnNhd ℂ F (XiCRaw S.G' S.a S.ν 2 1 t) ∧
          F (rawOf S.D') = S.TstepC (zeroClass 3 3 6 m₁ 1 2 (rhoSep m₁)) g) ∧
        (∃ F : RawData 3 3 (6 * 3 ^ m₁) 2 2 → ℂ, AnalyticAt ℂ F (rawOf S.D') ∧
          F (rawOf S.D') = S.E0C (zeroClass 3 3 6 m₁ 1 2 (rhoSep m₁)) +
            S.F0C (zeroClass 3 3 6 m₁ 1 2 (rhoSep m₁)) g) ∧
        (∀ (y : CTorus 3 3 6 m₁ 2) (i : Fin 2), ∃ F : RawData 3 3 (6 * 3 ^ m₁) 2 2 → ℂ,
          AnalyticAt ℂ F (rawOf S.D') ∧
          F (rawOf S.D') = S.M0C (zeroClass 3 3 6 m₁ 1 2 (rhoSep m₁)) g y i) := by
  obtain ⟨m₁, c, BG, κ, t, c₂, BG₂, δc, ht0, hFl, hMX, hdm, hα, hsm, hc7, hsmR⟩ :=
    exists_chart_params
  have hX := exists_xiC (bgHyp_rho m₁) (GP m₁ (rhoSep m₁)) hN2 (by simp) ht0
  have hΩ : ∀ x, x ∈ (GP m₁ (rhoSep m₁)).Ω 1 := fun x => (isLevel_GP m₁ x).1
  have hDh : ∀ x i, (witnessD m₁).h x i = (unitVec hN2 i : ℂ) := fun x i =>
    unitBg_h_of_mem (GP m₁ (rhoSep m₁)) hN2 (unitVec hN2) (hΩ x) i
  have hXi : XiCData (GP m₁ (rhoSep m₁)) (compWeight 3 1) 0 2 1 t (witnessD m₁) :=
    ⟨_, _, 0, 0, hX, fun x hx i => by
      rw [show (witnessD m₁).Ψ x i = (unitVec hN2 i : ℂ) from
        unitBg_Ψ_of_mem (GP m₁ (rhoSep m₁)) hN2 (unitVec hN2) hx i]
      simp, fun x hx i => by rw [hDh x i]; simp⟩
  obtain ⟨β, p, γ, hβ, hp, hγ, hcert⟩ := exists_complexStep_cert_of_xiCData hFl hMX hdm hα hsm
    hc7 hsmR (witnessD m₁) hXi hDh
  exact ⟨m₁, chartSetting m₁ (witnessD m₁) hDh β p, t, γ,
    isReal_of_inDomainR (witnessData_domain (m₁ := m₁) (β := 1) (δ := 1) (δ' := 1) one_pos),
    hβ, hp, hγ, ⟨c, BG, κ, c₂, BG₂, hFl⟩, hXi, hcert _ rfl⟩

end Balaban.Fluctuation
