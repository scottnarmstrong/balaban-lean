/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.MarkedRootFamily
public import Balaban.Fluctuation.Prop33CloseReal
public import Balaban.Fluctuation.StepComplexOutAnalytic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The root assembly of the marked terms of the zero class (`MarkedRootAssembly`)

For the zero class `Φ₁ = -β V^{(k)}`, and the marks of the first-order term at the root `z` are
`G_{z,Y'}(e, u) = -β · markedOut z Y'`, `Y' ∈ 𝒴_z = bridgeFamily`, built with the tangent `Q(e.1)` of
the family (`MarkedRootFamily`).  This file assembles the four clauses of the leaf
`markedRoot_zero_family` of the note `MARKPARAM`.

* `MarkRealAt`: the hypotheses `MARK-REAL` of the landed
  `hasDerivAt_Phi1C_marked_eq_neg_beta_sum_of_hdom` at the datum of a step, in one statement: the
  datum lies in the base domain; every layer-constant fluctuation of the ball is the tangent of an
  old spin whose disc lies in the domain of the small solution (`hreal`, Lemma 2.3 (d)); the
  marked segments have complex neighbourhoods in that domain; `Φ₁` is complex differentiable at
  the ray points `s ψ'`, `s ∈ [0,1]`.
* `inUnionDomainC_psiAtV_of_hreal`: the third clause follows from the second for every direction
  whose lift lies in the ball.
* `markRealAt_of_chart`: `MarkRealAt` holds at every datum of the chart with `h = h₀`, under the
  numerical hypotheses of the landed `hreal_level` and `classRegularLocC_zeroClass` (none of them
  depends on the datum).  So `MARK-REAL` is supplied on the whole constant-`h₀` slice.
* `neg_beta_sum_markedOut_eq_fderiv_of_markReal`: at the datum of the step, the finite sum of the
  marks is the integrand of `E1MarksC`:
  `∑_{Y' ∈ 𝒴_z} -β · markedOut z Y' = DΦ₁(s ψ')[1_{B(z)} ψ']`, `s ∈ [0,1]`.
* `MarkedRootAssembly`, `markedRootAssembly_zero_of_markReal`: the four clauses (analyticity in
  `(e, u)` on `physV × {|u| < R_σ}`; the bound, the root and domain clause and the anchored sum at
  every point of that set; the finite-sum identity on the constant-`h₀` slice at the datum
  `S.withDatum D hD`), for given block terms and a given tangent `Q`, with `MARK-REAL` on the slice
  as the single premise `hMR`.
* `markedRootAssembly_zero`: the same with `MARK-REAL` supplied by `markRealAt_of_chart`, for the
  terms of `vblock_expansion_scaled` and the tangent `Q(Θ) = β_k^{-1/2} M(Θ) ψ̂` built from one
  matrix function `M` of the raw data that serves every hat field `‖ψ̂‖ ≤ p₁`
  (`exists_analytic_hatCovSqrt_bdd`).

## Scope

Zero class, undecoupled level, generator-neutral.  NOT proved here: continuity and measurability
in the configuration, the clamped extension of the marks to all parameters and configurations
(the leaf `markedGlobalFields_zero`); one label system for all roots; the `E1MarksC` inhabitant.
The marks are not local in the configuration `ψ̂` (the tangent `C^{1/2}(Θ) ψ̂` is not), so no `DepOn`
statement is made.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Background Balaban.Multiscale Balaban.Localization Balaban.SmallField
  Balaban.SmallField.Def6 Balaban.Polymer Set Metric Matrix

/-- The norm of `-b · m` for a real `b`. -/
theorem norm_neg_ofReal_mul (b : ℝ) (m : ℂ) : ‖-(b : ℂ) * m‖ = |b| * ‖m‖ := by
  rw [norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs]

namespace StepSetting

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}
  (S : StepSetting d L N₁ m₁ k N ϱ) (z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))))

/-! ### `MARK-REAL` at the datum of a step -/

/-- **`MARK-REAL` at the datum of the step** (the hypotheses on the datum and on the marked
tangent of `hasDerivAt_Phi1C_marked_eq_neg_beta_sum_of_hdom`, and the differentiability used by
`hasDerivAt_Phi1C_marked`), for the marked block `z`, the ball radius `δ₁`, the disc radius `R`,
the mark radius `t₁` and the hat field `ψ̂ = x`:

1. the datum `θ` lies in the base domain `𝒟(c₀, C₂)` (`hD2`);
2. every layer-constant fluctuation `ψ'` with `|ψ'| < δ₁` is the tangent of an old spin with the
   same `h`, whose disc of radius `R` through `ψ^{(k)}(θ)` lies in the domain of the small solution
   (`hreal`, FLUCTUATION Lemma 2.3 (d));
3. for every `s ∈ [0,1]` and `|t| < t₁`, the segment `ψ^{(k)}(θ) + ζ v_t`, `ζ ∈ [0,1]`, of the marked
   tangent `v_t = s ψ' + t M_z ψ'`, `ψ' = shiftUC ψ̂`, has complex neighbourhoods in the domain of
   the small solution (`hdomT`);
4. for every `s ∈ [0,1]` the exponent `Φ₁` of the zero class is complex differentiable at `s ψ'`. -/
def MarkRealAt (δ₁ R t₁ : ℝ) (x : S.E) : Prop :=
  InUnionDomainC S.G' (bgC0 d L N) (thm73C2 d L N) S.ν S.D' ∧
  (∀ ψ' ∈ FlBall (stepG d L N₁ m₁ k ϱ) δ₁, IsLayerConstant (stepG d L N₁ m₁ k ϱ) ψ' →
    ∃ D : BgData (stepG d L N₁ m₁ k ϱ) N, (∀ y i, D.h y i = S.D'.h y i) ∧
    compTangent S.hG S.hG' (le_refl (k + 1)) S.a
      (bgFieldC S.G' S.a S.ν (bgC0 d L N) S.D') S.D' D = ψ' ∧
    ∀ t : ℂ, ‖t‖ < R → InUnionDomainC (stepG d L N₁ m₁ k ϱ) (bgC0 d L N) (bgC1 d L N) S.ν
      ((composeData (S.hG.precedes S.hG' (le_refl (k + 1))) S.a
        (bgFieldC S.G' S.a S.ν (bgC0 d L N) S.D') S.D').lineAt
        (tangentData D (composeData (S.hG.precedes S.hG' (le_refl (k + 1))) S.a
          (bgFieldC S.G' S.a S.ν (bgC0 d L N) S.D') S.D')) t)) ∧
  ∀ s ∈ Icc (0 : ℝ) 1,
    (∀ t : ℂ, ‖t‖ < t₁ → ∀ s' ∈ Icc (0 : ℝ) 1, ∀ᶠ ζ : ℂ in nhds (s' : ℂ),
      InUnionDomainC (stepG d L N₁ m₁ k ϱ) (bgC0 d L N) (bgC1 d L N) S.ν
        (S.dataUC (S.psiAtV ζ (S.markedTangentC z (s : ℂ) t x)))) ∧
    DifferentiableAt ℂ (S.Phi1C (zeroClass d L N₁ m₁ k N ϱ)) ((s : ℂ) • S.shiftUC x)

/-- **The domain premise along a complex line from `hreal`.**  If every layer-constant fluctuation
of the ball is the tangent of an old spin whose disc of radius `R` lies in the domain of the small
solution (`hreal`), then for every complex direction `v` of the unit lattice whose lift lies in the
ball and every `|ζ| < R` the old spin `ψ^{(k)}(θ) + ζ v` lies in that domain. -/
theorem inUnionDomainC_psiAtV_of_hreal {δ₁ R : ℝ}
    (hreal : ∀ ψ' ∈ FlBall (stepG d L N₁ m₁ k ϱ) δ₁, IsLayerConstant (stepG d L N₁ m₁ k ϱ) ψ' →
      ∃ D : BgData (stepG d L N₁ m₁ k ϱ) N, (∀ y i, D.h y i = S.D'.h y i) ∧
      compTangent S.hG S.hG' (le_refl (k + 1)) S.a
        (bgFieldC S.G' S.a S.ν (bgC0 d L N) S.D') S.D' D = ψ' ∧
      ∀ t : ℂ, ‖t‖ < R → InUnionDomainC (stepG d L N₁ m₁ k ϱ) (bgC0 d L N) (bgC1 d L N) S.ν
        ((composeData (S.hG.precedes S.hG' (le_refl (k + 1))) S.a
          (bgFieldC S.G' S.a S.ν (bgC0 d L N) S.D') S.D').lineAt
          (tangentData D (composeData (S.hG.precedes S.hG' (le_refl (k + 1))) S.a
            (bgFieldC S.G' S.a S.ν (bgC0 d L N) S.D') S.D')) t))
    {v : S.EC} (hv : liftC S.hG' v ∈ FlBall (stepG d L N₁ m₁ k ϱ) δ₁) {ζ : ℂ} (hζ : ‖ζ‖ < R) :
    InUnionDomainC (stepG d L N₁ m₁ k ϱ) (bgC0 d L N) (bgC1 d L N) S.ν
      (S.dataUC (S.psiAtV ζ v)) := by
  obtain ⟨D₀, -, hDt, hDdisc⟩ := hreal _ hv (isLayerConstant_liftC S.hG S.hG' v)
  have e : tangentData D₀ S.psiKdC = S.rayDatumV v := by
    refine bgData_ext' ?_ ?_
    · rw [S.rayDatumV_Ψ_eq]
      exact hDt
    · funext y i
      rw [S.rayDatumV_h]
      rfl
  rw [S.dataUC_psiAtV_eq_lineAt, S.dataUC_psi0C, ← e]
  exact hDdisc ζ hζ

/-- **The lift of the marked tangent lies in the ball under the radial margin.**  If the shift
`ψ' = shiftUC ψ̂` has Euclidean norm at most `Y₀` at the unit points and
`(R₁ + r)(R_σ + t₁) Y₀ < δ₁` with `R₁ > 1`, `r > 0`, then for `|u| < R_σ`, `|t| < t₁` the lift of
`v_t = u ψ' + t M_z ψ'` lies in `FlBall Hm δ₁` (the point `σ = 1` of the discs of
`markedDisc_field_mem_flBall`). -/
theorem liftC_markedTangentC_mem_flBall_of_margin {ϱm : ℝ}
    {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm} (hG : IsLevel Hm k)
    {δ₁ Y₀ R₁ r Rσ t₁ : ℝ} {x : S.E} (hY : ∀ b : S.U, vn (fun i => S.shiftUC x (b, i)) ≤ Y₀)
    (hrad : (R₁ + r) * (Rσ + t₁) * Y₀ < δ₁) (hR₁ : 1 < R₁) (hr : 0 < r) {u t : ℂ}
    (hu : ‖u‖ < Rσ) (ht : ‖t‖ < t₁) :
    liftC S.hG' (S.markedTangentC z u t x) ∈ FlBall Hm δ₁ := by
  have h := S.markedDisc_field_mem_flBall z hG hY hrad hu ht (σ := 1)
    (by rw [norm_one]; linarith)
  rw [one_smul, map_smul] at h
  rw [S.liftC_markedTangentC]
  exact h

section Producer

variable {c BG κ eps Kc Cx c₂ BG₂ δ₁ δc : ℝ}

/-- **`MARK-REAL` holds at every datum of the chart.**  Let the datum `θ` of the step lie in the
chart `Ξ^c(𝔹_{k+1}; 1, ε)`, with the numerical hypotheses of `hreal_level` (`hsmR`, the source
condition `δ_b + 5 R δ₁ ≤ c₁` of Lemma 2.3 (d)) and of `classRegularLocC_zeroClass` (the covariance
chart `hMX`, `hdm`, `hα`, `hsm`; `β > 0`; `p₁ < p⁺` with `√N β_k^{-1/2} C_sup p⁺ < δ₁`).  Let
`‖ψ̂‖ ≤ p₁`, and let the lifts of the marked tangents `s ψ' + t M_z ψ'`, `s ∈ [0,1]`, `|t| < t₁`,
lie in the ball `FlBall δ₁`.  Then `MarkRealAt` holds.  None of the numerical hypotheses depends on
the datum, so this applies to `S.withDatum D hD` for every datum `D` of the chart with `h = h₀`. -/
theorem markRealAt_of_chart
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
    (hlt : S.p₁ < pp)
    (hD : XiCData S.G' S.a S.ν (k + 1) 1 eps S.D') {t₁ : ℝ} {x : S.E} (hx : ‖x‖ ≤ S.p₁)
    (hball : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t : ℂ, ‖t‖ < t₁ →
      liftC S.hG' (S.markedTangentC z (s : ℂ) t x) ∈ FlBall (stepG d L N₁ m₁ k ϱ) δ₁) :
    S.MarkRealAt z δ₁ R t₁ x := by
  have hreal := hreal_level hC S.hG S.hG' (le_refl (k + 1)) ha₁ hC.HBp hc7
    (by linarith : (0 : ℝ) ≤ R) hsmR S.D' hD
  refine ⟨(isDecBg_one_of_xiCData hC hD).2.mono (hc7.trans (thm73C3_le_thm73C2 d L N)), hreal,
    fun s hs => ⟨fun t ht s' hs' => ?_, ?_⟩⟩
  · have hs'1 : ‖(s' : ℂ)‖ < R := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs'.1]
      linarith [hs'.2]
    have hopen : {ζ : ℂ | ‖ζ‖ < R} ∈ nhds (s' : ℂ) :=
      (isOpen_lt continuous_norm continuous_const).mem_nhds hs'1
    filter_upwards [hopen] with ζ hζ
    exact S.inUnionDomainC_psiAtV_of_hreal hreal (hball s hs t ht) hζ
  · exact S.differentiableAt_Phi1C_of_classRegularLocC _
      (S.classRegularLocC_zeroClass hC hMX hdm hα hsm ha₁ hc7 hR hsmR hβ hpp hδ₁ hD hlt) hx hs

end Producer

/-! ### The finite sum of the marks is the integrand of `E1MarksC` -/

section Identity

variable {c BG κ eps Kc Cx c₂ BG₂ δ₁ : ℝ} {m₀ : ℕ}

/-- **The finite sum of the marks at the datum of the step.**  Let `E_{b,Y}` (`Ev b Y`, `Y ∈ dom b`)
be analytic terms summing to the block energy on `Ξ^c × FlBall` (the output of
`vblock_expansion_scaled`), let the discs of the marked tangent `v_t = s ψ' + t M_z ψ'`,
`ψ' = shiftUC ψ̂`, lie in the ball, and let `MARK-REAL` hold at the datum (`MarkRealAt`).  If the
rooted sums add up to the sum of all the derivatives (clause 1 of the count), then for
`s ∈ [0,1]`
`∑_{Y' ∈ 𝒴_z} -β · markedOut z Y' = DΦ₁(s ψ')[1_{B(z)} ψ']`,
the integrand of `E1MarksC` for the zero class.  Both sides are the `t`-derivative at `0` of
`Φ₁(v_t)` (`hasDerivAt_Phi1C_marked_eq_neg_beta_sum_of_hdom`, `hasDerivAt_Phi1C_marked`). -/
theorem neg_beta_sum_markedOut_eq_fderiv_of_markReal (ha₁ : 0 < S.a₁)
    (hC : FlCore N S.G' (stepG d L N₁ m₁ k ϱ) S.a₁ S.ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
    (hc7 : c7 d L N BG κ ≤ thm73C3 d L N) {R : ℝ} (hR : 2 ≤ R) (hRs : R * δ₁ ≤ deltaStar d L N)
    (hsmall : cK2 d L N * (R * δ₁) < bgC0 d L N / 2)
    (hnum : cK2 d L N * δ₁ ≤ c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8))
    (hnum' : cK2' d L N (famConst d L BG₂ κ) * δ₁ ≤
      c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8))
    (hD : XiCData S.G' S.a S.ν (k + 1) 1 eps S.D')
    (dom : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) →
      Finset (Set (CTorus d L N₁ m₁ (k + 1))))
    (Ev : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) → Set (CTorus d L N₁ m₁ (k + 1)) →
      RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) → ℂ)
    (han : ∀ b Y, AnalyticOnNhd ℂ (Ev b Y)
      (XiCRaw S.G' S.a S.ν (k + 1) 1 eps ×ˢ FlBall (stepG d L N₁ m₁ k ϱ) δ₁))
    (hsum : ∀ b, ∀ D : BgData S.G' N, XiCData S.G' S.a S.ν (k + 1) 1 eps D →
      ∀ ψ' ∈ FlBall (stepG d L N₁ m₁ k ϱ) δ₁,
      energyBlock S.G' (stepG d L N₁ m₁ k ϱ) S.a S.ν k (bgMultC S.G' S.a S.ν (bgC0 d L N) D)
        (flFieldOne S.G' (stepG d L N₁ m₁ k ϱ) BG₂ κ S.a₁ S.ν D ψ') ψ' b =
      ∑ Y ∈ dom b, Ev b Y (rawOf D, ψ'))
    {R₁ r t₁ : ℝ} (hR₁ : 1 < R₁) (hr : 0 < r) (ht₁ : 0 < t₁) (x : S.E) {s : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1)
    (hdisc : ∀ t : ℂ, ‖t‖ < t₁ → ∀ σ : ℂ, ‖σ‖ < R₁ + r →
      σ • (liftC S.hG' ((s : ℂ) • S.shiftUC x) + t • liftC S.hG' (S.maskUC z (S.shiftUC x))) ∈
        FlBall (stepG d L N₁ m₁ k ϱ) δ₁)
    (hMR : S.MarkRealAt z δ₁ R t₁ x)
    (hid : ∑ Y' ∈ bridgeFamily m₀ (fun _ => Set.univ) dom z,
        markedOut m₀ (fun _ => Set.univ) dom z Ev taylorWeight
          (liftC S.hG' ((s : ℂ) • S.shiftUC x)) (liftC S.hG' (S.maskUC z (S.shiftUC x)))
          (rawOf S.D') Y' =
      ∑ b, ∑ Y ∈ dom b, deriv (markedBlockTerm (Ev b Y) taylorWeight
        (liftC S.hG' ((s : ℂ) • S.shiftUC x)) (liftC S.hG' (S.maskUC z (S.shiftUC x)))
        (rawOf S.D')) 0) :
    ∑ Y' ∈ bridgeFamily m₀ (fun _ => Set.univ) dom z,
        -(S.β : ℂ) * markedOut m₀ (fun _ => Set.univ) dom z Ev taylorWeight
          (liftC S.hG' ((s : ℂ) • S.shiftUC x)) (liftC S.hG' (S.maskUC z (S.shiftUC x)))
          (rawOf S.D') Y' =
      (fderiv ℂ (S.Phi1C (zeroClass d L N₁ m₁ k N ϱ)) ((s : ℂ) • S.shiftUC x))
        (S.maskUC z (S.shiftUC x)) := by
  obtain ⟨hD2, hreal, hray⟩ := hMR
  obtain ⟨hdomT, hdiff⟩ := hray s hs
  have hsum' : ∀ b, ∀ Θ ∈ XiCRaw S.G' S.a S.ν (k + 1) 1 eps,
      ∀ ψ' ∈ FlBall (stepG d L N₁ m₁ k ϱ) δ₁,
      blockEnergyOne S.G' (stepG d L N₁ m₁ k ϱ) S.a₁ S.ν BG₂ κ eps k b (Θ, ψ') =
        ∑ Y ∈ dom b, Ev b Y (Θ, ψ') := by
    rintro b _ ⟨D, hDX, rfl⟩ ψ' hψ'
    rw [blockEnergyOne_rawOf hDX]
    exact hsum b D hDX ψ' hψ'
  have h1 := S.hasDerivAt_Phi1C_marked_eq_neg_beta_sum_of_hdom z ha₁ hC.HBp hD2 hC hc7 hR hRs
    hsmall hnum hnum' hD hreal dom Ev han hsum' hR₁ hr ht₁ x (s : ℂ) hdisc hdomT
  have h2 := S.hasDerivAt_Phi1C_marked z (zeroClass d L N₁ m₁ k N ϱ) (s : ℂ) x hdiff
  rw [← Finset.mul_sum, hid]
  exact h1.unique h2

end Identity

/-! ### The assembly -/

section Assembly

variable {c BG κ eps Kc Cx c₂ BG₂ δ₁ : ℝ} {m₀ : ℕ}
  {jV : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) → ℕ}
  {XV 𝒦XV : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) → Set (CTorus d L N₁ m₁ (k + 1))}
  {X₁V : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) → Finset (CTorus d L N₁ m₁ (k + 1))}

/-- **The clauses of the marked root assembly** (zero class) for the marks
`G_{z,Y'}(e, u) = -β · markedOut z Y'`, `Y' ∈ 𝒴_z = bridgeFamily`, built with the block terms
`Ev b Y`, `Y ∈ dom b`, and the tangent `u Q(e.1) + t M_z Q(e.1)` at the datum `e.1`; `V = physV`
is the parameter set of the chart `Ξ^c(𝔹_{k+1}; 1, ε)` of the step, `R_σ` the radius of the radial
mark, `F₀` the prefactor and `a₀` the rate:

* (analyticity) for every `Y'`, `(e, u) ↦ G_{z,Y'}(e, u)` is analytic on `V × {|u| < R_σ}`;
* (bound) at every point of `V × {|u| < R_σ}`: `|G_{z,Y'}| ≤ F₀ e^{-a₀ d(Y')}`, and for
  `aEnt + 1 ≤ a₀ - a''`, `∑_{Y' ∈ 𝒴_z} |G_{z,Y'}| e^{a'' d(Y')} ≤ F₀ K₀(d, L, a₀ - a'')`;
* (root and domain) at every point of `V × {|u| < R_σ}`: `G_{z,Y'} ≠ 0` implies `Y' ∈ 𝒟_{k+1}` and
  the root cube of `z` is a cube of `Y'`;
* (finite sum) on the constant-`h₀` slice: for every datum `D` of the chart with `D.h = h₀`, every
  hat field `‖ψ̂‖ ≤ p₁` such that `Q (rawOf D)` is the shift `ψ' = shiftUC ψ̂` of the step with the
  datum `D`, and every real `s ∈ [0,1]`,
  `∑_{Y' ∈ 𝒴_z} G_{z,Y'}(rawOf D, s) = DΦ₁(s ψ')[1_{B(z)} ψ']`,
  the integrand of `E1MarksC (S.withDatum D hD) (zeroClass …) BS z` at `(s, ψ̂)`.

The conjunction lists analyticity first, then the three pointwise clauses (bound, root and domain,
anchored sum), then the finite sum. -/
def MarkedRootAssembly (m₀ : ℕ)
    (dom : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) →
      Finset (Set (CTorus d L N₁ m₁ (k + 1))))
    (Ev : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) → Set (CTorus d L N₁ m₁ (k + 1)) →
      RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) → ℂ)
    (eps Rσ : ℝ) (Q : RawData d L (N₁ * L ^ m₁) (k + 1) N → S.EC) (F₀ a₀ : ℝ) : Prop :=
  (∀ Y', AnalyticOnNhd ℂ (fun p : physParam N S × ℂ =>
        -(S.β : ℂ) * markedOut m₀ (fun _ => Set.univ) dom z Ev taylorWeight
          (liftC S.hG' (p.2 • Q (p.1.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N)))
          (liftC S.hG' (S.maskUC z (Q (p.1.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N))))
          (p.1.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) Y')
      (physV S S.a₁ S.ν eps ×ˢ ball (0 : ℂ) Rσ)) ∧
  (∀ e ∈ physV S S.a₁ S.ν eps, ∀ u : ℂ, ‖u‖ < Rσ →
    (∀ Y', ‖-(S.β : ℂ) * markedOut m₀ (fun _ => Set.univ) dom z Ev taylorWeight
          (liftC S.hG' (u • Q (e.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N)))
          (liftC S.hG' (S.maskUC z (Q (e.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N))))
          (e.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) Y'‖ ≤
        F₀ * Real.exp (-a₀ * treeLenCovOne m₀ (k + 1) Y')) ∧
    (∀ Y', -(S.β : ℂ) * markedOut m₀ (fun _ => Set.univ) dom z Ev taylorWeight
          (liftC S.hG' (u • Q (e.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N)))
          (liftC S.hG' (S.maskUC z (Q (e.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N))))
          (e.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) Y' ≠ 0 →
        IsDj m₀ (k + 1) Y' ∧ rootCube (m₀ := m₀) z ∈ blocksOf m₀ (k + 1) Set.univ Y') ∧
    (∀ {a'' : ℝ}, aEnt d L + 1 ≤ a₀ - a'' →
      ∑ Y' : {Y' // Y' ∈ bridgeFamily m₀ (fun _ => Set.univ) dom z},
          ‖-(S.β : ℂ) * markedOut m₀ (fun _ => Set.univ) dom z Ev taylorWeight
            (liftC S.hG' (u • Q (e.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N)))
            (liftC S.hG' (S.maskUC z (Q (e.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N))))
            (e.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) Y'.1‖ *
            Real.exp (a'' * treeLenCovOne m₀ (k + 1) Y'.1) ≤
        F₀ * K0 d L (a₀ - a''))) ∧
  ∀ (D : BgData S.G' N) (hD : ∀ y i, D.h y i = (S.h₀ i : ℂ)) (x : S.E),
    XiCData S.G' S.a S.ν (k + 1) 1 eps D → ‖x‖ ≤ S.p₁ →
    Q (rawOf D) = (S.withDatum D hD).shiftUC x → ∀ s ∈ Icc (0 : ℝ) 1,
    ∑ Y' ∈ bridgeFamily m₀ (fun _ => Set.univ) dom z,
        -(S.β : ℂ) * markedOut m₀ (fun _ => Set.univ) dom z Ev taylorWeight
          (liftC S.hG' ((s : ℂ) • Q (rawOf D))) (liftC S.hG' (S.maskUC z (Q (rawOf D))))
          (rawOf D) Y' =
      (fderiv ℂ ((S.withDatum D hD).Phi1C (zeroClass d L N₁ m₁ k N ϱ))
        ((s : ℂ) • (S.withDatum D hD).shiftUC x))
        ((S.withDatum D hD).maskUC z ((S.withDatum D hD).shiftUC x))

/-- **`markedRootAssembly_zero_of_markReal`: the root assembly of the marked terms of the zero
class, conditional on `MARK-REAL` on the constant-`h₀` slice.**  Let `E_{b,Y}` (`Ev`) be one family
of block terms with the four clauses of `vblock_expansion_scaled` for `Hm = 𝔹_k` (sum identity
`hsum`, locality `hloc`, bound `E e^{-2κ_dec d(Y)}` `hbd`, analyticity `han`), on the cover data of
`marked_count_scaled`.  Let `Q` be a function of the raw data, analytic on the chart, with values
unit fields of Euclidean norm at most `Y₀` there, and let the strict radial margin
`(R₁ + r)(R_σ + t₁) Y₀ < δ₁` hold with `R₁ > 1`, `r > 0`, `0 < t₀ < t₁`, `R_σ > 1`.  Assume
`MARK-REAL` (`hMR`): at every datum `D` of the chart with `D.h = h₀` and every hat field
`‖ψ̂‖ ≤ p₁` for which `Q (rawOf D)` is the shift of the step with the datum `D`, `MarkRealAt` holds
for that step.  Then the clauses of `MarkedRootAssembly` hold for the marks
`G_{z,Y'}(e, u) = -β · markedOut z Y'`, with
`F₀ = |β| · 3 ‖E‖/(r³ t₀) · c₁ M^d · nFibre · e^{(2κ_dec-1) cBr}` and the rate `2κ_dec - 1`. -/
theorem markedRootAssembly_zero_of_markReal (ha₁ : 0 < S.a₁)
    (hC : FlCore N S.G' (stepG d L N₁ m₁ k ϱ) S.a₁ S.ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
    (hcovV : ∀ b, CovSetup S.G' m₀ (jV b) (XV b) (𝒦XV b))
    (hX₁V : ∀ b, (↑(X₁V b) : Set (CTorus d L N₁ m₁ (k + 1))) = X1 S.G' m₀ (jV b) (𝒦XV b))
    (hoptV : ∀ b, ∃ (W₀ : Finset (CTorus d L N₁ m₁ (k + 1)))
      (E₀ : Finset (CTorus d L N₁ m₁ (k + 1) × CTorus d L N₁ m₁ (k + 1))),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ XV b) ∧ MeetsOne m₀ (jV b) (𝒦XV b) W₀ ∧
        bondCost (scaleW L m₀ m₁ (jV b)) E₀ = treeLenCovOne m₀ (jV b) (XV b))
    {κdec : ℝ} (hκ1 : 1 ≤ 2 * κdec)
    (hZV : ∀ b, readSites (stepG d L N₁ m₁ k ϱ) k b ⊆ ↑(X₁V b)) (hL : 2 ≤ L)
    (hc7 : c7 d L N BG κ ≤ thm73C3 d L N) {R : ℝ} (hR : 2 ≤ R) (hRs : R * δ₁ ≤ deltaStar d L N)
    (hsmall : cK2 d L N * (R * δ₁) < bgC0 d L N / 2)
    (hnum : cK2 d L N * δ₁ ≤ c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8))
    (hnum' : cK2' d L N (famConst d L BG₂ κ) * δ₁ ≤
      c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8))
    (Ev : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) → Set (CTorus d L N₁ m₁ (k + 1)) →
      RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) → ℂ)
    {E : ℝ}
    (hsum : ∀ b, ∀ D : BgData S.G' N, XiCData S.G' S.a S.ν (k + 1) 1 eps D →
      ∀ ψ' ∈ FlBall (stepG d L N₁ m₁ k ϱ) δ₁,
      energyBlock S.G' (stepG d L N₁ m₁ k ϱ) S.a S.ν k (bgMultC S.G' S.a S.ν (bgC0 d L N) D)
        (flFieldOne S.G' (stepG d L N₁ m₁ k ϱ) BG₂ κ S.a₁ S.ν D ψ') ψ' b =
      ∑ Y ∈ polyDom S.G' (X₁V b) m₀ (jV b) (𝒦XV b), Ev b Y (rawOf D, ψ'))
    (hloc : ∀ b, ∀ Y, ∀ w ∈ XiCRaw S.G' S.a S.ν (k + 1) 1 eps ×ˢ FlBall (stepG d L N₁ m₁ k ϱ) δ₁,
        ∀ w' ∈ XiCRaw S.G' S.a S.ν (k + 1) 1 eps ×ˢ FlBall (stepG d L N₁ m₁ k ϱ) δ₁,
        agreeOn (thickSet S.G' Y) w.1 w'.1 → (∀ x ∈ psiThick Y, w.2 x = w'.2 x) →
        Ev b Y w = Ev b Y w')
    (hbd : ∀ b, ∀ Y, ∀ w ∈ XiCRaw S.G' S.a S.ν (k + 1) 1 eps ×ˢ FlBall (stepG d L N₁ m₁ k ϱ) δ₁,
        ‖Ev b Y w‖ ≤ E * Real.exp (-2 * κdec * treeLenCov S.G' m₀ Y))
    (han : ∀ b, ∀ Y, AnalyticOnNhd ℂ (Ev b Y)
        (XiCRaw S.G' S.a S.ν (k + 1) 1 eps ×ˢ FlBall (stepG d L N₁ m₁ k ϱ) δ₁))
    {Q : RawData d L (N₁ * L ^ m₁) (k + 1) N → S.EC}
    (hQ : AnalyticOnNhd ℂ Q (XiCRaw S.G' S.a S.ν (k + 1) 1 eps))
    {Y₀ R₁ r Rσ t₁ t₀ : ℝ}
    (hQb : ∀ Θ ∈ XiCRaw S.G' S.a S.ν (k + 1) 1 eps, ∀ b : S.U, vn (fun i => Q Θ (b, i)) ≤ Y₀)
    (hrad : (R₁ + r) * (Rσ + t₁) * Y₀ < δ₁) (hR₁ : 1 < R₁) (hr : 0 < r) (ht₀ : 0 < t₀)
    (ht₀₁ : t₀ < t₁) (hRσ : 1 < Rσ)
    (hMR : ∀ (D : BgData S.G' N) (hD : ∀ y i, D.h y i = (S.h₀ i : ℂ)) (x : S.E),
      XiCData S.G' S.a S.ν (k + 1) 1 eps D → ‖x‖ ≤ S.p₁ →
      Q (rawOf D) = (S.withDatum D hD).shiftUC x → (S.withDatum D hD).MarkRealAt z δ₁ R t₁ x) :
    S.MarkedRootAssembly z m₀ (fun b => polyDom S.G' (X₁V b) m₀ (jV b) (𝒦XV b)) Ev eps Rσ Q
      (|S.β| * (3 * ‖E‖ / (r ^ 3 * t₀) * (c1 d L * ((L : ℝ) ^ (m₀ + m₁)) ^ d) *
        ((nFibre d L : ℝ) * Real.exp ((2 * κdec - 1) * cBr d L)))) (2 * κdec - 1) := by
  obtain ⟨hA, hCl, -⟩ := S.markedRoot_family_of_vblock z hC.HBp.hd hcovV hX₁V hoptV hκ1 S.hG hZV
    hL hC.HBp Ev hloc hbd han hQ hQb hrad hR₁ hr ht₀ ht₀₁
  refine ⟨fun Y' => analyticOnNhd_const.mul (hA Y'), fun e he u hu => ?_,
    fun D hD x hDX hx hQx s hs => ?_⟩
  · obtain ⟨-, hB, hroot, hsumB⟩ := hCl e he u hu
    refine ⟨fun Y' => ?_, fun Y' h => hroot Y' fun h0 => h (by rw [h0, mul_zero]),
      fun {a''} ha => ?_⟩
    · rw [norm_neg_ofReal_mul]
      exact (mul_le_mul_of_nonneg_left (hB Y') (abs_nonneg S.β)).trans (le_of_eq (by ring))
    · simp only [norm_neg_ofReal_mul]
      have h := mul_le_mul_of_nonneg_left (hsumB ha) (abs_nonneg S.β)
      rw [Finset.mul_sum] at h
      refine le_trans (le_of_eq (Finset.sum_congr rfl fun Y' _ => ?_)) (h.trans (le_of_eq ?_))
      · ring
      · ring
  · have hΘ : rawOf D ∈ XiCRaw S.G' S.a S.ν (k + 1) 1 eps := ⟨D, hDX, rfl⟩
    have hY : ∀ b : S.U, vn (fun i => (S.withDatum D hD).shiftUC x (b, i)) ≤ Y₀ := by
      intro b
      rw [← hQx]
      exact hQb _ hΘ b
    have hu : ‖((s : ℝ) : ℂ)‖ < Rσ := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs.1]
      linarith [hs.2]
    have hcl := S.marked_count_field_of_vblock z hC.HBp.hd hcovV hX₁V hoptV hκ1 S.hG hZV hL Ev
      hloc hbd han hY hrad hR₁ hr ht₀ ht₀₁ hu hΘ
    rw [hQx]
    exact (S.withDatum D hD).neg_beta_sum_markedOut_eq_fderiv_of_markReal z ha₁ hC hc7 hR hRs
      hsmall hnum hnum' hDX _ Ev han hsum hR₁ hr (ht₀.trans ht₀₁) x hs
      (fun t ht σ hσ => S.markedDisc_field_mem_flBall z S.hG hY hrad hu ht hσ)
      (hMR D hD x hDX hx hQx) hcl.1.1

end Assembly

/-! ### The assembly with `MARK-REAL` supplied on the slice -/

section Unconditional

variable {c BG κ eps Kc Cx c₂ BG₂ δ₁ δc : ℝ} {m₀ : ℕ}
  {jV : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) → ℕ}
  {XV 𝒦XV : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) → Set (CTorus d L N₁ m₁ (k + 1))}
  {X₁V : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) → Finset (CTorus d L N₁ m₁ (k + 1))}

/-- **`markedRootAssembly_zero`: the root assembly of the marked terms of the zero class on the
physical chart.**  The hypotheses are those of `marked_count_scaled` for `Hm = 𝔹_k` (the cover data
and `FlCore`), of the covariance chart (`hMX`, `hdm`, `hα`, `hsm`), the numerical hypotheses of the
cubic identity (`hc7`, `hR`, `hRs`, `hsmall`, `hnum`, `hnum'`) and of `MARK-REAL` (`hsmR`, `β > 0`,
`p₁ < p⁺` with `√N β_k^{-1/2} C_sup p⁺ < δ₁`), and the strict radial margin
`(R₁ + r)(R_σ + t₁) · markedRad < δ₁` with `markedRad = √N β_k^{-1/2} C_sup p₁`, `R₁ > 1`, `r > 0`,
`0 < t₀ < t₁`, `R_σ > 1`.  None of them depends on the datum of the step.

There are one family `Ev` of block terms (summing to the block energies) and one matrix function
`M` of the raw data, with entries analytic on the chart, such that
`β_k^{-1/2} M(rawOf D) ψ̂` is the shift `shiftUC ψ̂` of the step with the datum `D` for every datum of
the chart with `D.h = h₀`, and such that for **every** marked block `z` and every hat field
`‖ψ̂‖ ≤ p₁` the clauses of `MarkedRootAssembly` hold for the marks
`G_{z,Y'}(e, u) = -β · markedOut z Y'` built with the tangent `Q(Θ) = β_k^{-1/2} M(Θ) ψ̂`, with
`F₀ = |β| · 3‖E*‖/(r³ t₀) · c₁ M^d · nFibre · e^{(2κ_dec-1) cBr}` and the rate `2κ_dec - 1`.  The
terms `Ev` and the matrix `M` do not depend on `z` or on `ψ̂`; `MARK-REAL` is not a hypothesis (it
is supplied at every datum of the slice by `markRealAt_of_chart`). -/
theorem markedRootAssembly_zero
    (hC : FlCore N S.G' (stepG d L N₁ m₁ k ϱ) S.a₁ S.ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
    (hcovV : ∀ b, CovSetup S.G' m₀ (jV b) (XV b) (𝒦XV b))
    (hX₁V : ∀ b, (↑(X₁V b) : Set (CTorus d L N₁ m₁ (k + 1))) = X1 S.G' m₀ (jV b) (𝒦XV b))
    (hconn : HatConn S.G')
    (hrow : RowInHat (coverOf S.G') (stepG d L N₁ m₁ k ϱ) S.a S.ν)
    (hoptV : ∀ b, ∃ (W₀ : Finset (CTorus d L N₁ m₁ (k + 1)))
      (E₀ : Finset (CTorus d L N₁ m₁ (k + 1) × CTorus d L N₁ m₁ (k + 1))),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ XV b) ∧ MeetsOne m₀ (jV b) (𝒦XV b) W₀ ∧
        bondCost (scaleW L m₀ m₁ (jV b)) E₀ = treeLenCovOne m₀ (jV b) (XV b))
    (hΔV : ∀ b, treeLenCovOne m₀ (jV b) (XV b) = 0)
    {κdec κ₀ : ℝ} (hκ₀ : 0 ≤ κ₀) (hκdec : 3 * κ₀ + 3 ≤ κdec)
    (hκ : 4 * d * (((2 * L + 1) ^ d : ℕ) : ℝ) * κdec ≤ κ) (h1 : 1 ≤ (κ / 2 - 1) / 2)
    (hlog : Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) * (((L ^ m₀) ^ d : ℕ) : ℝ)) ≤ (κ / 2 - 1) / 2)
    (hZV : ∀ b, readSites (stepG d L N₁ m₁ k ϱ) k b ⊆ ↑(X₁V b))
    (hmarV : ∀ b, BlockMargin S.G' (X₁V b)
      (↑(blockSites d L N₁ m₁ (k + 1) k b) : Set (CTorus d L N₁ m₁ (k + 1))))
    (hL : 2 ≤ L)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    (hdm : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    (ha₁ : 0 < S.a₁) (hc7 : c7 d L N BG κ ≤ thm73C3 d L N) {R : ℝ} (hR : 2 ≤ R)
    (hRs : R * δ₁ ≤ deltaStar d L N) (hsmall : cK2 d L N * (R * δ₁) < bgC0 d L N / 2)
    (hnum : cK2 d L N * δ₁ ≤ c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8))
    (hnum' : cK2' d L N (famConst d L BG₂ κ) * δ₁ ≤
      c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8))
    (hsmR : 2 * (compC4 d * (bgK1 d L N * (xiC1 d * eps))) + 5 * (R * δ₁) ≤ bgC1 d L N)
    (hβ : 0 < S.β) {pp : ℝ}
    (hδ₁ : Real.sqrt N * (S.betaU ^ (-(1 / 2 : ℝ)) *
      (covSupConstC d L N (compWeight L S.a₁ k) κ * pp)) < δ₁)
    (hlt : S.p₁ < pp) (hp₁ : 0 ≤ S.p₁) {R₁ r Rσ t₁ t₀ : ℝ}
    (hrad : (R₁ + r) * (Rσ + t₁) *
      markedRad d L N k S.a₁ κ S.p₁ (((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) < δ₁)
    (hR₁ : 1 < R₁) (hr : 0 < r) (ht₀ : 0 < t₀) (ht₀₁ : t₀ < t₁) (hRσ : 1 < Rσ) :
    ∃ (Ev : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) → Set (CTorus d L N₁ m₁ (k + 1)) →
        RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) → ℂ)
      (M : RawData d L (N₁ * L ^ m₁) (k + 1) N → Matrix (S.U × Fin N) (S.U × Fin N) ℂ),
      (∀ b, ∀ D : BgData S.G' N, XiCData S.G' S.a S.ν (k + 1) 1 eps D →
        ∀ ψ' ∈ FlBall (stepG d L N₁ m₁ k ϱ) δ₁,
        energyBlock S.G' (stepG d L N₁ m₁ k ϱ) S.a S.ν k (bgMultC S.G' S.a S.ν (bgC0 d L N) D)
          (flFieldOne S.G' (stepG d L N₁ m₁ k ϱ) BG₂ κ S.a₁ S.ν D ψ') ψ' b =
        ∑ Y ∈ polyDom S.G' (X₁V b) m₀ (jV b) (𝒦XV b), Ev b Y (rawOf D, ψ')) ∧
      (∀ p q, AnalyticOnNhd ℂ (fun Θ => M Θ p q) (XiCRaw S.G' S.a S.ν (k + 1) 1 eps)) ∧
      (∀ (D : BgData S.G' N) (hD : ∀ y i, D.h y i = (S.h₀ i : ℂ)),
        XiCData S.G' S.a S.ν (k + 1) 1 eps D → ∀ x : S.E,
        (((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) • (M (rawOf D) *ᵥ yhat x) =
          (S.withDatum D hD).shiftUC x) ∧
      ∀ (z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1)))) (x : S.E), ‖x‖ ≤ S.p₁ →
        S.MarkedRootAssembly z m₀ (fun b => polyDom S.G' (X₁V b) m₀ (jV b) (𝒦XV b)) Ev eps Rσ
          (fun Θ => (((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) • (M Θ *ᵥ yhat x))
          (|S.β| * (3 * ‖energyBdScaled d L N (compWeight L S.a₁) k
              (cK2' d L N (famConst d L BG₂ κ) * δ₁) δ₁ (rho4 d L N BG κ)‖ / (r ^ 3 * t₀) *
            (c1 d L * ((L : ℝ) ^ (m₀ + m₁)) ^ d) *
            ((nFibre d L : ℝ) * Real.exp ((2 * κdec - 1) * cBr d L)))) (2 * κdec - 1) := by
  obtain ⟨Ev, hsum, hloc, hbd, han, -⟩ := S.marked_count_field hC hcovV hX₁V hconn hrow hoptV hΔV
    hκ₀ hκdec hκ h1 hlog S.hG hZV hmarV hL
  obtain ⟨M, hMan, hM, hMb⟩ := exists_analytic_hatCovSqrt_bdd hC S.hk1 hMX hdm hα hsm
  have hfib : ∀ (D : BgData S.G' N) (hD : ∀ y i, D.h y i = (S.h₀ i : ℂ)),
      XiCData S.G' S.a S.ν (k + 1) 1 eps D → ∀ x : S.E,
      (((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) • (M (rawOf D) *ᵥ yhat x) =
        (S.withDatum D hD).shiftUC x := by
    intro D hD hDX x
    have e : (S.withDatum D hD).covSqrtC = hatCovSqrt S.G' S.a₁ S.ν D :=
      (S.withDatum D hD).covSqrtC_eq_hatCovSqrt
    rw [hM D hDX, ← e]
    rfl
  refine ⟨Ev, M, hsum, hMan, hfib, fun z x hx => ?_⟩
  have hyh : ∀ p, ‖yhat x p‖ ≤ S.p₁ := fun p => S.yhat_le_of_norm_le hx p
  have hQ : AnalyticOnNhd ℂ (fun Θ : RawData d L (N₁ * L ^ m₁) (k + 1) N =>
      (((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) • (M Θ *ᵥ yhat x))
      (XiCRaw S.G' S.a S.ν (k + 1) 1 eps) := fun Θ hΘ =>
    (analyticOnNhd_smul_mulVec hMan _ (Θ, yhat x) ⟨hΘ, Set.mem_univ _⟩).comp_of_eq
      (analyticAt_id.prod analyticAt_const) rfl
  have hQb : ∀ Θ ∈ XiCRaw S.G' S.a S.ν (k + 1) 1 eps, ∀ b : S.U,
      vn (fun i => ((((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) • (M Θ *ᵥ yhat x)) (b, i)) ≤
        markedRad d L N k S.a₁ κ S.p₁ (((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) :=
    fun Θ hΘ b => hMb _ hp₁ hyh Θ hΘ b
  refine S.markedRootAssembly_zero_of_markReal z ha₁ hC hcovV hX₁V hoptV (by linarith) hZV hL hc7
    hR hRs hsmall hnum hnum' Ev hsum hloc hbd han hQ hQb hrad hR₁ hr ht₀ ht₀₁ hRσ ?_
  intro D hD x' hDX hx' hQx'
  have hY : ∀ b : S.U, vn (fun i => (S.withDatum D hD).shiftUC x' (b, i)) ≤
      markedRad d L N k S.a₁ κ S.p₁ (((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) := by
    intro b
    rw [← hQx']
    exact hQb _ ⟨D, hDX, rfl⟩ b
  refine (S.withDatum D hD).markRealAt_of_chart z hC hMX hdm hα hsm ha₁ hc7 (by linarith) hsmR hβ
    (lt_of_le_of_lt hp₁ hlt) hδ₁ hlt hDX hx' fun s hs t ht => ?_
  have hu : ‖((s : ℝ) : ℂ)‖ < Rσ := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs.1]
    linarith [hs.2]
  exact (S.withDatum D hD).liftC_markedTangentC_mem_flBall_of_margin z S.hG hY hrad hR₁ hr hu ht

end Unconditional

end StepSetting

end Balaban.Fluctuation
