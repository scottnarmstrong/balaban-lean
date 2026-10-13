/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.StepComplexJoint
public import Balaban.Fluctuation.StepActivityHatSource
public import Balaban.Inhabited.SourceActivityScale
public import Balaban.Inhabited.UniformChartRelative
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

/-!
# The source part of the exponent of the zero-class step at complex chart data

For the zero class, a `JointRep` `Jr` and a datum `D` of the chart `Ξ^c(𝔹_{k+1}; 1, ε)` (any
complex datum, with any complex site-dependent `h̃`), the source exponent
`Jr.W2 C g (rawOf D, z)` is

* (`W2_zeroClass`) the pairing of `g` with `svec (Jr.FJ (rawOf D, z)).1 - svec (Jr.FJ (rawOf D, 0)).1`;
* (`FJ_sub_eq_flFieldOne`) the difference of the lower small solutions at `z` and at `0`, which
  equals `flFieldOne D (hatLift z) - flFieldOne D (hatLift 0)`, for every hat variable `z` with
  `|z(b)_i| ≤ p⁺`: the lower datum is the one given by `Jr.dom`, and
  `bgFieldC_sub_eq_flFieldOne_hatLift` applies at the datum `D` itself (no real structure used);
* (`W2_eq_val_sub`) the difference of two values of the expanded function `val` of
  `sourceDirectTerms_slice`, at the source parameters `g/β` and `0`, along the ray `t ↦ t x`,
  `t ∈ [0,1]`, of a complex hat variable `x` (`dirTermSrc_ray` and `analyticAt_flFieldOne_hatRay`);
* (`W2_eq_val_sub_physical`) the same at the datum `D = S.D'` of the step, where `Jr.W2` is the
  complex exponent `S.WtwoC` (`W2_path`).
* (`Balaban.Inhabited.expSourceChart_scale`) all premises hold together at the step `hatStepK` of
  every scale, with the ray bound `p⁺ = 2 p₁`, for every source and every admissible hat variable.

This file proves only the source side of the identity of the exponents.  The interaction side
(`W1`), the family `sourceExponent_family` and the complex activity bound off the central datum are
NOT proved here.  Everything is for the zero class and does not depend on the choice of generating
sets for class terms.
-/

@[expose] public section

namespace Balaban.Fluctuation

open MeasureTheory Balaban Balaban.Localization Balaban.Multiscale Balaban.Polymer
  Balaban.Background Balaban.SmallField Balaban.SmallField.Def6 Balaban.Analysis Finset Matrix Set
  Filter Topology

namespace StepSetting

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}
variable (S : StepSetting d L N₁ m₁ k N ϱ)
variable {c BG κ eps Kc Cx c₂ BG₂ δ₁ δc pp : ℝ}

namespace JointRep

variable {S} (Jr : S.JointRep eps pp)

/-- **T1.** At the zero class `W₂` is the pairing of `g` with the difference of the lower small
solutions at `z` and at `0` (the old `Floc` terms vanish). -/
theorem W2_zeroClass (g : Fld d L N₁ m₁ (k + 1) N)
    (q : RawData d L (N₁ * L ^ m₁) (k + 1) N × S.EC) :
    Jr.W2 (zeroClass d L N₁ m₁ k N ϱ) g q =
      ∑ y : CTorus d L N₁ m₁ (k + 1), ∑ i : Fin N, g y i *
        (svec (stepG d L N₁ m₁ k ϱ) (Jr.FJ q).1 y i -
          svec (stepG d L N₁ m₁ k ϱ) (Jr.FJ (q.1, 0)).1 y i) := by
  have hz : ∀ q' : RawData d L (N₁ * L ^ m₁) (k + 1) N × S.EC,
      Jr.FcJ (zeroClass d L N₁ m₁ k N ϱ) g q' = ∑ y : CTorus d L N₁ m₁ (k + 1), ∑ i : Fin N,
        g y i * svec (stepG d L N₁ m₁ k ϱ) (Jr.FJ q').1 y i := by
    intro q'
    show (∑ y : CTorus d L N₁ m₁ (k + 1), ∑ i, g y i * svec (stepG d L N₁ m₁ k ϱ) (Jr.FJ q').1 y i) +
      ∑ j ∈ Finset.Icc 1 k, Floc 0 (zeroTerms d L N₁ m₁ (k + 1) N ϱ) j (Jr.PJ j q').1
        (Jr.PJ j q').2 g = _
    simp [Floc_zero]
  unfold W2
  rw [hz, hz, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

section Chart

variable (hC : FlCore N S.G' (stepG d L N₁ m₁ k ϱ) S.a₁ S.ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
  (ha₁ : 0 < S.a₁) (H : BgHyp d L (k + 1) ϱ (compWeight L S.a₁) S.ν)
  (hc7 : c7 d L N BG κ ≤ thm73C3 d L N) {R : ℝ} (hR : 2 ≤ R)
  (hsmR : 2 * (compC4 d * (bgK1 d L N * (xiC1 d * eps))) + 5 * (R * δ₁) ≤ bgC1 d L N)
  (hRs : R * δ₁ ≤ deltaStar d L N) (hsmall : cK2 d L N * (R * δ₁) < bgC0 d L N / 2)
  (hnum : cK2 d L N * δ₁ ≤ c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8))
  (hnum' : cK2' d L N (famConst d L BG₂ κ) * δ₁ ≤
    c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8))
  (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
  (hdm : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
  (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
  (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4) {cψ : ℝ} (hcψ : 0 ≤ cψ)
  (hδ₁ : Real.sqrt N * (‖((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)‖ *
    (covSupConstC d L N (compWeight L S.a₁ k) κ * cψ)) < δ₁)

include hC ha₁ H hc7 hR hsmR hRs hsmall hnum hnum' hMX hdm hα hsm hcψ hδ₁ in
/-- **T2, one point.**  For a datum `D` of the chart (complex, any `h̃`) and a hat variable `z`
with `|z(b)_i| ≤ p⁺ ≤ c_ψ`, the lower small solution of the old spin with raw data
`Jr.gJ (rawOf D, z)` minus the restriction of `φ_{k+1}(D)` is `flFieldOne D (hatLift z)`. -/
theorem FJ_sub_restrict_eq_flFieldOne (hpc : pp ≤ cψ) {D : BgData S.G' N}
    (hD : XiCData S.G' S.a S.ν (k + 1) 1 eps D) {z : S.EC} (hz : ∀ p, ‖z p‖ ≤ pp) :
    (Jr.FJ (rawOf D, z)).1 -
        (S.hG.precedes S.hG' (le_refl (k + 1))).restrictφ
          (bgFieldC S.G' S.a S.ν (bgC0 d L N) D) =
      flFieldOne S.G' (stepG d L N₁ m₁ k ϱ) BG₂ κ S.a₁ S.ν D
        (hatLift S.G' S.a₁ S.ν S.hG' ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) D z) := by
  obtain ⟨D₀, hdom, hraw⟩ := Jr.dom D hD z hz
  have hg : Jr.gJ (rawOf D, z) = (D₀.Ψ, D₀.h) := hraw.symm
  have hF : Jr.FJ (rawOf D, z) = (bgFieldC (stepG d L N₁ m₁ k ϱ) S.a S.ν (bgC0 d L N) D₀,
      bgMultC (stepG d L N₁ m₁ k ϱ) S.a S.ν (bgC0 d L N) D₀) := by
    unfold FJ
    rw [hg]
    exact Jr.Fb_eq D₀ hdom
  rw [hF]
  refine bgFieldC_sub_eq_flFieldOne_hatLift hC S.hk1 S.hG S.hG' ha₁ H hc7 hR hsmR hRs hsmall hnum
    hnum' hMX hdm hα hsm _ hcψ hδ₁ hD (D := D₀) (fun x i => ?_) (fun p => (hz p).trans hpc) ?_
  · exact (congrFun (congrFun (congrArg Prod.snd hraw) x) i)
  · funext x i
    have h1 := congrFun (congrFun (congrArg Prod.fst hraw) x) i
    simp only [compTangent]
    have h2 := congrFun (congrFun (Jr.Pc_eq D hD) x) i
    have h3 := Jr.Mx_eq D hD
    have h1' : D₀.Ψ x i = Jr.Pc (rawOf D) x i +
        liftC S.hG' (((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) • (Jr.Mx (rawOf D) *ᵥ z)) x i := h1
    show D₀.Ψ x i - (composeData _ S.a (bgFieldC S.G' S.a S.ν (bgC0 d L N) D) D).Ψ x i =
      liftC S.hG' (((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) • (hatCovSqrt S.G' S.a₁ S.ν D *ᵥ z)) x i
    rw [← h2, h1', h3]
    ring

include hC ha₁ H hc7 hR hsmR hRs hsmall hnum hnum' hMX hdm hα hsm hcψ hδ₁ in
/-- **T2.**  The difference of the lower small solutions at the hat variables `z` and `z'`, both
bounded by `p⁺ ≤ c_ψ`, at a chart datum `D`, is `flFieldOne D (hatLift z) - flFieldOne D (hatLift z')`.
With `z' = 0` this is the field difference of the source. -/
theorem FJ_sub_eq_flFieldOne (hpc : pp ≤ cψ) {D : BgData S.G' N}
    (hD : XiCData S.G' S.a S.ν (k + 1) 1 eps D) {z z' : S.EC} (hz : ∀ p, ‖z p‖ ≤ pp)
    (hz' : ∀ p, ‖z' p‖ ≤ pp) :
    (Jr.FJ (rawOf D, z)).1 - (Jr.FJ (rawOf D, z')).1 =
      flFieldOne S.G' (stepG d L N₁ m₁ k ϱ) BG₂ κ S.a₁ S.ν D
        (hatLift S.G' S.a₁ S.ν S.hG' ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) D z) -
      flFieldOne S.G' (stepG d L N₁ m₁ k ϱ) BG₂ κ S.a₁ S.ν D
        (hatLift S.G' S.a₁ S.ν S.hG' ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) D z') := by
  rw [← Jr.FJ_sub_restrict_eq_flFieldOne hC ha₁ H hc7 hR hsmR hRs hsmall hnum hnum' hMX hdm hα
    hsm hcψ hδ₁ hpc hD hz, ← Jr.FJ_sub_restrict_eq_flFieldOne hC ha₁ H hc7 hR hsmR hRs hsmall hnum
    hnum' hMX hdm hα hsm hcψ hδ₁ hpc hD hz']
  abel

include hC ha₁ H hc7 hR hsmR hRs hsmall hnum hnum' hMX hdm hα hsm hcψ hδ₁ in
/-- **T3.**  The source exponent at a chart datum is a difference of two values of the expanded
function `val` of `sourceDirectTerms_slice` (given by its formula `hval`, with `η = 1/β`, any
fixed `Rσ`, `ε_U`): for the zero class, `D` in the chart, a complex hat variable `x` whose ray
`r x`, `r ∈ [0,1]`, stays within `p⁺ < c_ψ` (`hxb`), and `t ∈ [0,1]`,

`Jr.W2 C g (rawOf D, t • x) = val (x,x) (x,x) t (rawOf D, g/β) - val (x,x) (x,x) t (rawOf D, 0)`.

The potential parts of the two values cancel; the source part is `β ∑_s (g_s/β) dirTermSrc …`,
which `dirTermSrc_ray` turns into the value at `t` minus the value at `0` of
`l ↦ svec (flFieldOne D (hatLift (l x)))`. -/
theorem W2_eq_val_sub (hpc : pp < cψ) {D : BgData S.G' N}
    (hD : XiCData S.G' S.a S.ν (k + 1) 1 eps D) (g : Fld d L N₁ m₁ (k + 1) N)
    (hβ : (S.β : ℂ) ≠ 0) (x : S.EC)
    (hxb : ∀ r : ℝ, r ∈ Icc (0 : ℝ) 1 → ∀ p, ‖((r : ℂ) • x) p‖ ≤ pp)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1)
    (val : ((S.U × Fin N → ℂ) × (S.U × Fin N → ℂ)) → ((S.U × Fin N → ℂ) × (S.U × Fin N → ℂ)) →
        ℂ → (RawData d L (N₁ * L ^ m₁) (k + 1) N ×
          (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ)) → ℂ)
    (hval : ∀ x w σ p, val x w σ p =
        (-(S.β : ℂ)) * raySrc3 (hatFun S.G' S.a₁ S.ν eps S.hG' ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)
          (interactionOne S.hG S.hG' (le_refl (k + 1)) S.a₁ S.ν eps)) taylorWeight x.1 w.1 σ p.1 +
        (S.β : ℂ) * (∑ s : CTorus d L N₁ m₁ (k + 1) × Fin N, p.2 s.1 s.2 *
          dirTermSrc (hatFun S.G' S.a₁ S.ν eps S.hG' ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)
            (onXi S.G' S.a₁ S.ν eps
              (fun D ψ' => svec (stepG d L N₁ m₁ k ϱ)
                (flFieldOne S.G' (stepG d L N₁ m₁ k ϱ) BG₂ κ S.a₁ S.ν D ψ') s.1 s.2)))
            (fun _ => (1 : ℂ)) x.2 w.2 σ p.1)) :
    Jr.W2 (zeroClass d L N₁ m₁ k N ϱ) g (rawOf D, (t : ℂ) • x) =
      val (x, x) (x, x) (t : ℂ) (rawOf D, fun y i => g y i / (S.β : ℂ)) -
        val (x, x) (x, x) (t : ℂ) (rawOf D, 0) := by
  classical
  set cc : ℂ := ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) with hcc
  let Gs : CTorus d L N₁ m₁ (k + 1) × Fin N → ℂ → ℂ := fun s l =>
    hatFun S.G' S.a₁ S.ν eps S.hG' cc
      (onXi S.G' S.a₁ S.ν eps
        (fun D ψ' => svec (stepG d L N₁ m₁ k ϱ)
          (flFieldOne S.G' (stepG d L N₁ m₁ k ϱ) BG₂ κ S.a₁ S.ν D ψ') s.1 s.2))
      (rawOf D, l • x)
  have hGs : ∀ s l, Gs s l = svec (stepG d L N₁ m₁ k ϱ)
      (flFieldOne S.G' (stepG d L N₁ m₁ k ϱ) BG₂ κ S.a₁ S.ν D
        (hatLift S.G' S.a₁ S.ν S.hG' cc D (l • x))) s.1 s.2 := by
    intro s l
    show hatFun S.G' S.a₁ S.ν eps S.hG' cc _ (rawOf D, l • x) = _
    rw [hatFun_rawOf S.hG' cc _ hD, onXi_rawOf hD]
  have hAn : ∀ s, ∀ r : ℝ, r ∈ Icc (0 : ℝ) 1 → AnalyticAt ℂ (Gs s) (r : ℂ) := by
    intro s r hr
    have hb : ∀ p, ‖(r : ℂ) * x p‖ < cψ := fun p =>
      lt_of_le_of_lt (hxb r hr p) hpc
    have hfun : Gs s = fun l => svec (stepG d L N₁ m₁ k ϱ)
        (flFieldOne S.G' (stepG d L N₁ m₁ k ϱ) BG₂ κ S.a₁ S.ν D
          (hatLift S.G' S.a₁ S.ν S.hG' cc D (l • x))) s.1 s.2 := funext (hGs s)
    rw [hfun]
    by_cases hm : s.1 ∈ (stepG d L N₁ m₁ k ϱ).Ω 1
    · have e : (fun l : ℂ => svec (stepG d L N₁ m₁ k ϱ)
          (flFieldOne S.G' (stepG d L N₁ m₁ k ϱ) BG₂ κ S.a₁ S.ν D
            (hatLift S.G' S.a₁ S.ν S.hG' cc D (l • x))) s.1 s.2) =
          fun l => flFieldOne S.G' (stepG d L N₁ m₁ k ϱ) BG₂ κ S.a₁ S.ν D
            (hatLift S.G' S.a₁ S.ν S.hG' cc D (l • x)) (⟨s.1, hm⟩, s.2) := by
        funext l; exact svec_of_mem (stepG d L N₁ m₁ k ϱ) _ ⟨s.1, hm⟩ s.2
      rw [e]
      exact analyticAt_flFieldOne_hatRay hC S.hk1 S.hG S.hG' ha₁ H hc7 hR hsmR hRs hsmall
        hnum hnum' hMX hdm hα hsm cc hcψ hδ₁ hD x hb (⟨s.1, hm⟩, s.2)
    · have e : (fun l : ℂ => svec (stepG d L N₁ m₁ k ϱ)
          (flFieldOne S.G' (stepG d L N₁ m₁ k ϱ) BG₂ κ S.a₁ S.ν D
            (hatLift S.G' S.a₁ S.ν S.hG' cc D (l • x))) s.1 s.2) = fun _ => 0 := by
        funext l; exact svec_of_not_mem (stepG d L N₁ m₁ k ϱ) _ hm s.2
      rw [e]
      exact analyticAt_const
  have hsrc : ∀ s : CTorus d L N₁ m₁ (k + 1) × Fin N,
      dirTermSrc (hatFun S.G' S.a₁ S.ν eps S.hG' cc
        (onXi S.G' S.a₁ S.ν eps
          (fun D ψ' => svec (stepG d L N₁ m₁ k ϱ)
            (flFieldOne S.G' (stepG d L N₁ m₁ k ϱ) BG₂ κ S.a₁ S.ν D ψ') s.1 s.2)))
        (fun _ => (1 : ℂ)) x x (t : ℂ) (rawOf D) = Gs s (t : ℂ) - Gs s 0 :=
    fun s => dirTermSrc_ray _ (rawOf D) x (Gs s) (fun l => rfl) (hAn s) ht
  have hdiff : val (x, x) (x, x) (t : ℂ) (rawOf D, fun y i => g y i / (S.β : ℂ)) -
      val (x, x) (x, x) (t : ℂ) (rawOf D, 0) =
      (S.β : ℂ) * ∑ s : CTorus d L N₁ m₁ (k + 1) × Fin N, (g s.1 s.2 / (S.β : ℂ)) *
        (Gs s (t : ℂ) - Gs s 0) := by
    rw [hval, hval]
    simp only [Pi.zero_apply, zero_mul, Finset.sum_const_zero, mul_zero, add_zero,
      hsrc]
    rw [add_sub_cancel_left]
  rw [hdiff, W2_zeroClass]
  rw [Fintype.sum_prod_type, Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hz0 : ∀ p, ‖(0 : S.EC) p‖ ≤ pp := Jr.zero_le_pp
  have hT := Jr.FJ_sub_eq_flFieldOne hC ha₁ H hc7 hR hsmR hRs hsmall hnum hnum' hMX hdm hα hsm
    hcψ hδ₁ hpc.le hD (z := (t : ℂ) • x) (z' := 0) (hxb t ht) hz0
  have hsub : ∀ (A B : (stepG d L N₁ m₁ k ϱ).Ω 1 × Fin N → ℂ),
      svec (stepG d L N₁ m₁ k ϱ) (A - B) y i =
        svec (stepG d L N₁ m₁ k ϱ) A y i - svec (stepG d L N₁ m₁ k ϱ) B y i := by
    intro A B
    by_cases hm : y ∈ (stepG d L N₁ m₁ k ϱ).Ω 1
    · rw [svec_of_mem (stepG d L N₁ m₁ k ϱ) _ ⟨y, hm⟩ i,
        svec_of_mem (stepG d L N₁ m₁ k ϱ) _ ⟨y, hm⟩ i,
        svec_of_mem (stepG d L N₁ m₁ k ϱ) _ ⟨y, hm⟩ i]
      rfl
    · rw [svec_of_not_mem (stepG d L N₁ m₁ k ϱ) _ hm i, svec_of_not_mem (stepG d L N₁ m₁ k ϱ) _ hm i,
        svec_of_not_mem (stepG d L N₁ m₁ k ϱ) _ hm i]
      simp
  have hS := hsub (Jr.FJ (rawOf D, (t : ℂ) • x)).1 (Jr.FJ (rawOf D, 0)).1
  rw [hT, hsub] at hS
  rw [← hS, hGs, hGs, zero_smul]
  field_simp
  rfl

include Jr hC ha₁ H hc7 hR hsmR hRs hsmall hnum hnum' hMX hdm hα hsm hcψ hδ₁ in
/-- **T4.**  At the datum `D = S.D'` of the step itself and the real hat variable `x`, the
chart statement `W2_eq_val_sub` reads: the complex exponent `S.WtwoC` of the zero class is the
difference of the two values of `val` at `(rawOf S.D', g/β)` and `(rawOf S.D', 0)`
(`‖x‖ ≤ p⁺ < c_ψ`, `t ∈ [0,1]`). -/
theorem WtwoC_eq_val_sub (hpc : pp < cψ) (hX : XiCData S.G' S.a S.ν (k + 1) 1 eps S.D')
    (g : Fld d L N₁ m₁ (k + 1) N) (hβ : (S.β : ℂ) ≠ 0) (x : S.E) (hxn : ‖x‖ ≤ pp)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1)
    (val : ((S.U × Fin N → ℂ) × (S.U × Fin N → ℂ)) → ((S.U × Fin N → ℂ) × (S.U × Fin N → ℂ)) →
        ℂ → (RawData d L (N₁ * L ^ m₁) (k + 1) N ×
          (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ)) → ℂ)
    (hval : ∀ x w σ p, val x w σ p =
        (-(S.β : ℂ)) * raySrc3 (hatFun S.G' S.a₁ S.ν eps S.hG' ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)
          (interactionOne S.hG S.hG' (le_refl (k + 1)) S.a₁ S.ν eps)) taylorWeight x.1 w.1 σ p.1 +
        (S.β : ℂ) * (∑ s : CTorus d L N₁ m₁ (k + 1) × Fin N, p.2 s.1 s.2 *
          dirTermSrc (hatFun S.G' S.a₁ S.ν eps S.hG' ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)
            (onXi S.G' S.a₁ S.ν eps
              (fun D ψ' => svec (stepG d L N₁ m₁ k ϱ)
                (flFieldOne S.G' (stepG d L N₁ m₁ k ϱ) BG₂ κ S.a₁ S.ν D ψ') s.1 s.2)))
            (fun _ => (1 : ℂ)) x.2 w.2 σ p.1)) :
    S.WtwoC (zeroClass d L N₁ m₁ k N ϱ) g t x =
      val (S.hatC x, S.hatC x) (S.hatC x, S.hatC x) (t : ℂ)
          (rawOf S.D', fun y i => g y i / (S.β : ℂ)) -
        val (S.hatC x, S.hatC x) (S.hatC x, S.hatC x) (t : ℂ) (rawOf S.D', 0) := by
  have hxb : ∀ r : ℝ, r ∈ Icc (0 : ℝ) 1 → ∀ p, ‖((r : ℂ) • S.hatC x) p‖ ≤ pp := by
    intro r hr
    refine smul_yhat_le (S := S) (pp := pp) (s := r) (x := x) ?_
    rw [abs_of_nonneg hr.1]
    exact (mul_le_of_le_one_left (norm_nonneg _) hr.2).trans hxn
  rw [← Jr.W2_path (zeroClass d L N₁ m₁ k N ϱ) hX g (x := x)
    (by rw [abs_of_nonneg ht.1]; exact (mul_le_of_le_one_left (norm_nonneg _) ht.2).trans hxn)]
  exact Jr.W2_eq_val_sub hC ha₁ H hc7 hR hsmR hRs hsmall hnum hnum' hMX hdm hα hsm hcψ hδ₁ hpc hX
    g hβ (S.hatC x) hxb ht val hval

include Jr hC hc7 hR hsmR hRs hsmall hnum hnum' hMX hdm hα hsm hcψ hδ₁ in
/-- **T4, real form.**  With the ray data of the step (`R0`, `p₁ < p⁺`) and `χ_fl(x) = 1`, the real
exponent `S.Wtwo` of the zero class (the one of `Wtwo_zeroClass_eq_hat`) is the same difference of
values of `val`: the chart identity `W2_eq_val_sub` at the central datum recovers the landed
real-step statement. -/
theorem Wtwo_eq_val_sub (R0 : S.RayData pp) (hlt : S.p₁ < pp) (hp₁ : 0 < S.p₁) (hpc : pp < cψ)
    (hX : XiCData S.G' S.a S.ν (k + 1) 1 eps S.D')
    (g : Fld d L N₁ m₁ (k + 1) N) (hβ : (S.β : ℂ) ≠ 0) (x : S.E) (hxn : ‖x‖ ≤ pp)
    (hx : chiFl S.U N S.p₁ x = 1) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1)
    (val : ((S.U × Fin N → ℂ) × (S.U × Fin N → ℂ)) → ((S.U × Fin N → ℂ) × (S.U × Fin N → ℂ)) →
        ℂ → (RawData d L (N₁ * L ^ m₁) (k + 1) N ×
          (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ)) → ℂ)
    (hval : ∀ x w σ p, val x w σ p =
        (-(S.β : ℂ)) * raySrc3 (hatFun S.G' S.a₁ S.ν eps S.hG' ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)
          (interactionOne S.hG S.hG' (le_refl (k + 1)) S.a₁ S.ν eps)) taylorWeight x.1 w.1 σ p.1 +
        (S.β : ℂ) * (∑ s : CTorus d L N₁ m₁ (k + 1) × Fin N, p.2 s.1 s.2 *
          dirTermSrc (hatFun S.G' S.a₁ S.ν eps S.hG' ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)
            (onXi S.G' S.a₁ S.ν eps
              (fun D ψ' => svec (stepG d L N₁ m₁ k ϱ)
                (flFieldOne S.G' (stepG d L N₁ m₁ k ϱ) BG₂ κ S.a₁ S.ν D ψ') s.1 s.2)))
            (fun _ => (1 : ℂ)) x.2 w.2 σ p.1)) :
    S.Wtwo (zeroClass d L N₁ m₁ k N ϱ) g t x =
      val (S.hatC x, S.hatC x) (S.hatC x, S.hatC x) (t : ℂ)
          (rawOf S.D', fun y i => g y i / (S.β : ℂ)) -
        val (S.hatC x, S.hatC x) (S.hatC x, S.hatC x) (t : ℂ) (rawOf S.D', 0) := by
  have hp40' : S.p₁ / (S.betaU ^ (1 / 2 : ℝ) * S.δ) ≤ (3 * R0.B₅ * R0.K₂)⁻¹ :=
    (div_le_div_of_nonneg_right hlt.le (by have := R0.hδ0; have := R0.betaU_pos; positivity)).trans
      R0.hp40
  have hbpos := R0.betaU_pos
  have hB5pos : 0 ≤ R0.B₅ := le_trans (by norm_num) (le_trans (le_max_left _ _) R0.hB5)
  have hrad' : R0.B₅ * S.betaU ^ (-(1 / 2 : ℝ)) * S.p₁ ≤ fluctRadius d L N :=
    le_trans (mul_le_mul_of_nonneg_left hlt.le (by positivity)) R0.hrad
  rw [← S.WtwoC_eq (zeroClass d L N₁ m₁ k N ϱ) R0.ha₁ R0.H R0.hδ'0 R0.hδ' R0.hD'R R0.hδ0 R0.hfam
    R0.hsm R0.hχu R0.hnorm R0.hβ hp₁ R0.hB5 R0.hK2 hp40' hrad' g ht x hx]
  exact Jr.WtwoC_eq_val_sub hC R0.ha₁ R0.H hc7 hR hsmR hRs hsmall hnum hnum' hMX hdm hα hsm hcψ
    hδ₁ hpc hX g hβ x hxn ht val hval

end Chart

end JointRep

end StepSetting

end Balaban.Fluctuation

namespace Balaban.Inhabited

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation
  Balaban.Localization Balaban.Localization.LevelPair Balaban.Localization.I5Inhabited
  Balaban.Polymer Balaban.SmallField.Def6 Balaban.Inhabited.LevelStep Filter Topology

open Classical in
/-- **T5 (non-vacuity), every scale.**  At the physical step `hatStepK k m₁ hk ν β p₁ δ`
(`d = L = 3`, `N = 2`; every scale `k ≥ 1`, `β ≥ β₀`, cutoff `p₁ ≤ A₁ (log β_k)^p`) all
premises of `JointRep.W2_eq_val_sub` hold together at the central datum `S.D'` and the ray bound
`p⁺ = 2 p₁`: there is a `JointRep` and an expanded function `val` (the formula of
`sourceDirectTerms_slice`) such that for every source `g` and every hat variable `x` whose ray stays
within `2 p₁`, the chart identity holds.  Here `κ₀ = a_Ent + 1`, `κ_dec = 100 (κ₀ + c₁ + 10)`. -/
theorem expSourceChart_scale {A₁ : ℝ} (hA : 0 < A₁) (p : ℕ) :
    ∃ (m₁ : ℕ) (t δ β₀ BG₂ κ : ℝ), 2 ≤ β₀ ∧ 0 < t ∧ 0 < δ ∧
      ∀ (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁], 3 ∣ N₁ → 5 < N₁ →
      ∀ ν : ℝ, 0 < ν → ν * 3 ^ (2 * (k + 1)) ≤ 1 → ∀ β : ℝ, β₀ ≤ β →
      ∀ p₁ : ℝ, 0 < p₁ → p₁ ≤ pLog A₁ p (β * 3 ^ k) →
      ∀ S : StepSetting 3 3 N₁ m₁ k 2 (rhoSep m₁),
        S = hatStepK (N₁ := N₁) k m₁ hk ν β p₁ δ →
      ∃ Jr : S.JointRep t (2 * p₁),
      ∃ val : ((S.U × Fin 2 → ℂ) × (S.U × Fin 2 → ℂ)) → ((S.U × Fin 2 → ℂ) × (S.U × Fin 2 → ℂ)) →
            ℂ → (RawData 3 3 (N₁ * 3 ^ m₁) (k + 1) 2 × (CTorus 3 3 N₁ m₁ (k + 1) → Fin 2 → ℂ)) → ℂ,
        (∀ x w σ Θ, val x w σ Θ =
          (-(S.β : ℂ)) * raySrc3 (hatFun S.G' S.a₁ S.ν t S.hG'
            ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)
            (interactionOne S.hG S.hG' (le_refl (k + 1)) S.a₁ S.ν t)) taylorWeight x.1 w.1 σ Θ.1 +
          (S.β : ℂ) * (∑ s : CTorus 3 3 N₁ m₁ (k + 1) × Fin 2, Θ.2 s.1 s.2 *
            dirTermSrc (hatFun S.G' S.a₁ S.ν t S.hG' ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)
              (onXi S.G' S.a₁ S.ν t
                (fun D ψ' => svec (stepG 3 3 N₁ m₁ k (rhoSep m₁))
                  (flFieldOne S.G' (stepG 3 3 N₁ m₁ k (rhoSep m₁)) BG₂ κ S.a₁ S.ν D ψ')
                  s.1 s.2)))
              (fun _ => (1 : ℂ)) x.2 w.2 σ Θ.1)) ∧
        ∀ (g : Fld 3 3 N₁ m₁ (k + 1) 2) (x : S.EC),
          (∀ r : ℝ, r ∈ Set.Icc (0 : ℝ) 1 → ∀ q, ‖((r : ℂ) • x) q‖ ≤ 2 * p₁) →
          ∀ τ : ℝ, τ ∈ Set.Icc (0 : ℝ) 1 →
            Jr.W2 (zeroClass 3 3 N₁ m₁ k 2 (rhoSep m₁)) g (rawOf S.D', (τ : ℂ) • x) =
              val (x, x) (x, x) (τ : ℂ) (rawOf S.D', fun y i => g y i / (S.β : ℂ)) -
                val (x, x) (x, x) (τ : ℂ) (rawOf S.D', 0) := by
  classical
  set κ0 : ℝ := aEnt 3 3 + 1 with hκ0def
  set κdec : ℝ := 100 * (κ0 + c1 3 3 + 10) with hκdecdef
  obtain ⟨-, δ, δ', T, -, -, hδ, hsm, hδ'0, hδ'a, hδ'b, hδ'c, hT, -, hT1, hT2⟩ :=
    exists_witness_params (fun _ => 0)
  have hc1 := one_le_c1 3 3
  have hent := aEnt_nonneg 3 3
  obtain ⟨m₁, c, BG, κ, t, c₂, BG₂, δc, h4, ht0, ⟨hC₀⟩, hκ0, hκdec, hκ, h1, hlog, hc7,
    hMX, hdm, hα, hsmX, g1, g2, g3, g4, g5, hκE, hκa, hB0⟩ :=
    tower_core_rates 2 (κ0 := κ0) (κdec := κdec) (by rw [hκ0def]) (by rw [hκdecdef]; linarith)
  have hbig : cstarX 3 3 ≤ (3 : ℝ) ^ m₁ := by
    have hκdec0 : 0 ≤ κdec := by linarith
    have hκ_nn : 0 ≤ κ := le_trans (by positivity) hκ
    have h := Localization.cstarX_pos 3 3
    have h2 : cstarX 3 3 ≤ cstarX 3 3 * Real.exp ((N0 3 3 : ℝ) * κ) :=
      le_mul_of_one_le_right h.le (Real.one_le_exp (by positivity))
    have h3 : ((3 : ℕ) : ℝ) ^ m₁ = (3 : ℝ) ^ m₁ := by norm_num
    linarith
  obtain ⟨β₀t, hβ₀t, hitems⟩ := scale_C_items hA p m₁ h4 hbig κ ht0 hδ hsm hδ'0 hδ'a hδ'b hδ'c
  refine ⟨m₁, t, δ, β₀t, BG₂, κ, hβ₀t, ht0, hδ, ?_⟩
  intro k hk N₁ _ h3N hN ν hνpos hν β hβ p₁ hp0 hp₁ S hS
  subst hS
  have hν0 : 0 ≤ ν := hνpos.le
  obtain ⟨hcψ0, hr0, hδ₁, hc, hlt, ⟨R0⟩⟩ := hitems k hk N₁ hN ν hν0 hν β hβ p₁ hp0 hp₁
  have hSD := dgSetting_lv (N₁ := N₁) (k := k) h4 hN hν0 hν
  have hHB := bgHyp_lv (k := k) m₁ hν0 hν
  have hC : FlCore 2 (lvTop N₁ m₁ k (rhoSep m₁)) (lvLow N₁ m₁ k (rhoSep m₁)) 1 ν c BG κ t
      (levelKc 3 3) (Cchi 3 3) c₂ BG₂ t :=
    flCore_level_transfer hC₀ hSD (opSetting_lv h4 hN hν0 hν) (isLevel_lvLow hk) isLevel_lvTop hHB
  have hD := hatStepK_xiCData (N₁ := N₁) k m₁ hk hν0 hν β p₁ δ ht0
  have hβ0 : 0 < β := by linarith
  have hmem := compWeight_three_mem hk
  have hCs : 0 ≤ covSupConstC 3 3 2 (compWeight 3 (1 : ℝ) k) κ :=
    covSupConstC_nonneg (by norm_num) (by norm_num) (by linarith [hmem.1]) κ
  have hpc : 2 * p₁ < lvCpsi κ t (β * 3 ^ k) := by
    have : 0 < lvR κ t (β * 3 ^ k) p₁ * p₁ := mul_pos hr0 hp0
    nlinarith
  have hbU : 0 ≤ (hatStepK (N₁ := N₁) k m₁ hk ν β p₁ δ).betaU := by
    have := R0.betaU_pos
    exact this.le
  have hδp : Real.sqrt ((2 : ℕ) : ℝ) *
      ((hatStepK (N₁ := N₁) k m₁ hk ν β p₁ δ).betaU ^ (-(1 / 2 : ℝ)) *
        (covSupConstC 3 3 2 (compWeight 3 (1 : ℝ) k) κ * (2 * p₁))) < t := by
    refine lt_of_le_of_lt ?_ hδ₁
    rw [(hatStepK (N₁ := N₁) k m₁ hk ν β p₁ δ).norm_betaU_rpow (show 0 ≤ β by linarith)]
    have hb := Real.rpow_nonneg hbU (-(1 / 2 : ℝ))
    have hs := Real.sqrt_nonneg ((2 : ℕ) : ℝ)
    refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hpc.le hCs) hb) hs
  obtain ⟨Jr⟩ := (hatStepK (N₁ := N₁) k m₁ hk ν β p₁ δ).nonempty_jointRep (pp := 2 * p₁)
    hC hMX hdm hα hsmX one_pos hc7 (R := 2) (by norm_num) g5 (by
      show 0 ≤ β
      linarith) (by linarith) hδp
  refine ⟨Jr, _, fun x w σ Θ => rfl, ?_⟩
  intro g x hx τ hτ
  refine Jr.W2_eq_val_sub hC one_pos hHB hc7 (R := 2) le_rfl g5 g1 g2 g3 g4 hMX hdm hα hsmX
    hcψ0.le hδ₁ hpc hD g ?_ x hx hτ _ (fun x w σ Θ => rfl)
  have : (hatStepK (N₁ := N₁) k m₁ hk ν β p₁ δ).β ≠ 0 := by
    show β ≠ 0
    exact hβ0.ne'
  exact_mod_cast this

end Balaban.Inhabited
