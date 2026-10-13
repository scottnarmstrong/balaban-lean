/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.SourcePhysValBridge
public import Balaban.Fluctuation.StepActivityHat
public import Balaban.Fluctuation.StepBaseDomain
import Mathlib.Tactic.Linarith

/-!
# The interaction half of the exponent value bridge at a chart datum

For the zero class the exponent of the step is `W₁ + W₂`.  The source half `W₂` is identified with
a difference of values of `physVal` at every chart datum in `SourcePhysValBridge.lean`; the
interaction half `W₁` was identified with the value of the hat expansion only at the datum of the
step itself (`Wone_zeroClass_eq_hat`).  This file carries that identification to every datum `D`
of `Ξ^c(𝔹_{k+1}; 1, ε)` whose field `h` is the constant `h₀` of the step, that is, to every datum
for which the step `S.withDatum D hD` is defined.

* `vkC_ray_vanish_chart`, `vkC_ray_taylor_chart`: the value, the first and the second derivative of
  the complex ray potential `s ↦ V^{(k)}(ψ^{(k)}(D) + s ψ')` vanish at `s = 0`, and the cubic
  integral remainder holds for `s ∈ [0,1]` (the landed complex lemmas applied to the step
  `S.withDatum D hD`; the base-domain and ray-domain witnesses come from `XiCData D`, `FlCore` and
  `Jr.dom`);
* `W1_zeroClass_eq_hat_chart`: `Jr.W1` at `(rawOf D, s ψ̂)` is `s² · (−β) · raySrc3 …` at the
  datum `rawOf D`;
* `W1_eq_physVal`, `sourcePhysVal_jointRep_zero`: the same in terms of `physVal`, and the two
  segment sum of `W₁` at `s` and `W₂` at `τ`.

No label, activity or almost-everywhere statement is asserted.
-/

@[expose] public section

namespace Balaban.Fluctuation

open MeasureTheory Balaban Balaban.Localization Balaban.Multiscale Balaban.Polymer
  Balaban.Background Balaban.SmallField Balaban.Analysis Finset Matrix Set Filter Topology

namespace StepSetting.JointRep

section Chart

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}
variable {S : StepSetting d L N₁ m₁ k N ϱ}
variable {c BG κ eps Kc Cx c₂ BG₂ δ₁ δc pp : ℝ}
variable (Jr : S.JointRep eps pp)
variable (D : BgData S.G' N) (hD : ∀ y i, D.h y i = (S.h₀ i : ℂ))
  (hX : XiCData S.G' S.a S.ν (k + 1) 1 eps D)

include Jr hX in
/-- The ray of a real hat variable `ψ̂` with `‖ψ̂‖ < pp` stays, near every `t ∈ [0,1]`, in the
domain `𝒟(𝔹_k)` (radius `bgC1`): the ray-domain witness of the complex Taylor formula for the
step `S.withDatum D hD`. -/
theorem eventually_inUnionDomainC_ray_chart (x : S.E) (hxn : ‖x‖ < pp) :
    ∀ t ∈ Icc (0 : ℝ) 1, ∀ᶠ s : ℝ in 𝓝 t,
      InUnionDomainC (stepG d L N₁ m₁ k ϱ) (bgC0 d L N) (bgC1 d L N) S.ν
        ((S.withDatum D hD).dataUC ((S.withDatum D hD).psiAtC s x)) := by
  intro t ht
  have hopen : IsOpen {s : ℝ | |s| * ‖x‖ < pp} := isOpen_lt (by fun_prop) continuous_const
  have htm : t ∈ {s : ℝ | |s| * ‖x‖ < pp} := by
    show |t| * ‖x‖ < pp
    rw [abs_of_nonneg ht.1]
    exact lt_of_le_of_lt (mul_le_of_le_one_left (norm_nonneg _) ht.2) hxn
  filter_upwards [hopen.mem_nhds htm] with s hs
  have key := (Jr.withDatum D hD).dataUC_psiHat_dom (S := S.withDatum D hD) hX
    (smul_yhat_le (S := S.withDatum D hD) (pp := pp) (s := s) (x := x) hs.le)
  exact Eq.mpr (congrArg (fun z => InUnionDomainC (stepG d L N₁ m₁ k ϱ) (bgC0 d L N)
    (bgC1 d L N) S.ν ((S.withDatum D hD).dataUC z))
    ((S.withDatum D hD).psiAtC_eq_psiHat s x)) key

variable {τι μι : Type*}
variable (hC : FlCore N S.G' (stepG d L N₁ m₁ k ϱ) S.a₁ S.ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
  (ha₁ : 0 < S.a₁) (H : BgHyp d L (k + 1) ϱ S.a S.ν)
  (hc7 : c7 d L N BG κ ≤ thm73C3 d L N)

include hC hc7 hX in
/-- The datum `D` of the chart lies in `𝒟(𝔹'_k)` with radius `thm73C2`. -/
theorem chart_dom2 : InUnionDomainC S.G' (bgC0 d L N) (thm73C2 d L N) S.ν D :=
  (isDecBg_one_of_xiCData hC hX).2.mono (hc7.trans (thm73C3_le_thm73C2 d L N))

include Jr hC ha₁ H hc7 hX in
/-- **T1: the jets of the ray potential vanish at every chart datum.**  For a datum `D` of
`Ξ^c(𝔹_{k+1}; 1, ε)` with `h ≡ h₀` and a real hat variable `ψ̂` with `‖ψ̂‖ < pp`, the complex
ray potential `s ↦ V^{(k)}(ψ^{(k)}(D) + s ψ')` of the step with the datum `D` has value, first
derivative and second derivative zero at `s = 0`.  It is the landed `VkC_ray_vanish` (critical
point `criticalPoint_complex`, linear response `theorem72_linearResponse`) applied to
`S.withDatum D hD`. -/
theorem vkC_ray_vanish_chart (x : S.E) (hxn : ‖x‖ < pp) :
    (S.withDatum D hD).VkC ((S.withDatum D hD).psiAtC 0 x) = 0 ∧
      deriv (fun s : ℝ => (S.withDatum D hD).VkC ((S.withDatum D hD).psiAtC s x)) 0 = 0 ∧
      deriv (deriv (fun s : ℝ => (S.withDatum D hD).VkC ((S.withDatum D hD).psiAtC s x))) 0 = 0 :=
  (S.withDatum D hD).VkC_ray_vanish ha₁ H (chart_dom2 D hX hC hc7) x
    (Jr.eventually_inUnionDomainC_ray_chart D hD hX x hxn 0 ⟨le_rfl, zero_le_one⟩)

include Jr hC ha₁ H hc7 hX in
/-- **T1, Taylor form.**  The cubic integral remainder of the complex ray potential of the step
with the datum `D`, for `s ∈ [0,1]`. -/
theorem vkC_ray_taylor_chart (x : S.E) (hxn : ‖x‖ < pp) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    (S.withDatum D hD).VkC ((S.withDatum D hD).psiAtC s x) = ∫ u in (0 : ℝ)..1,
      taylorWeight (u : ℂ) * ((s : ℂ) ^ 3 *
        iteratedDeriv 3 (fun r : ℝ => (S.withDatum D hD).VkC
          ((S.withDatum D hD).psiAtC r x)) (u * s)) :=
  (S.withDatum D hD).VkC_ray_taylor ha₁ H (chart_dom2 D hX hC hc7) x
    (Jr.eventually_inUnionDomainC_ray_chart D hD hX x hxn) hs

variable (hk : 1 ≤ k) {R : ℝ} (hR : 1 < R)
  (hsmR : 2 * (compC4 d * (bgK1 d L N * (xiC1 d * eps))) + 5 * (R * δ₁) ≤ bgC1 d L N)
  (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
  (hdm : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
  (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
  (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4) {cψ : ℝ} (hcψ : 0 ≤ cψ)
  (hδ₁ : Real.sqrt N * (‖((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)‖ *
    (covSupConstC d L N (compWeight L S.a₁ k) κ * cψ)) < δ₁)

include Jr hC ha₁ H hc7 hk hR hsmR hMX hdm hα hsm hcψ hδ₁ hX hD in
/-- **T2: the interaction half of the exponent at a chart datum.**  For the zero class, a datum
`D` of `Ξ^c(𝔹_{k+1}; 1, ε)` with `h ≡ h₀`, a real hat variable `ψ̂` with `‖ψ̂‖ < pp < c_ψ` and
`s ∈ [0,1]`:
`Jr.W1 (rawOf D, s ψ̂) = s² · ((−β) · raySrc3 (hatFun … interactionOne) taylorWeight ψ̂ ψ̂ s (rawOf D))`.
This is `Wone_zeroClass_eq_hat` with `rawOf S.D'` replaced by the raw datum of the chart. -/
theorem W1_zeroClass_eq_hat_chart (hpc : pp < cψ) (x : S.E) (hxn : ‖x‖ < pp) {s : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) :
    Jr.W1 (zeroClass d L N₁ m₁ k N ϱ) (rawOf D, (s : ℂ) • S.hatC x) =
      (s : ℂ) ^ 2 * ((-(S.β : ℂ)) * raySrc3 (hatFun S.G' S.a₁ S.ν eps S.hG'
        ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)
        (interactionOne S.hG S.hG' (le_refl (k + 1)) S.a₁ S.ν eps)) taylorWeight (S.hatC x)
        (S.hatC x) (s : ℂ) (rawOf D)) := by
  classical
  set cc : ℂ := ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) with hcc
  set f := interactionOne S.hG S.hG' (le_refl (k + 1)) S.a₁ S.ν eps with hf
  set S' := S.withDatum D hD with hS'
  let Gc : ℂ → ℂ := fun l => hatFun S.G' S.a₁ S.ν eps S.hG' cc f (rawOf D, l • yhat x)
  have hxle : ∀ r : ℝ, r ∈ Icc (0 : ℝ) 1 → |r| * ‖x‖ ≤ pp := fun r hr => by
    rw [abs_of_nonneg hr.1]
    exact (mul_le_of_le_one_left (norm_nonneg _) hr.2).trans hxn.le
  have hreal : ∀ r : ℝ, Gc (r : ℂ) = S'.VkC (S'.psiAtC r x) := fun r => by
    show hatFun S.G' S.a₁ S.ν eps S.hG' cc f (rawOf D, (r : ℂ) • yhat x) = _
    exact (S'.VkC_psiAtC_eq_hatFun hX r x).symm
  have hAn : ∀ r : ℝ, r ∈ Icc (0 : ℝ) 1 → AnalyticAt ℂ Gc (r : ℂ) := by
    intro r hr
    have hb : ∀ p, ‖(r : ℂ) * yhat x p‖ < cψ := fun p => by
      have := S.norm_smul_yhat_le_mul r x p
      have e : ((r : ℂ) • yhat x) p = (r : ℂ) * yhat x p := rfl
      rw [e] at this
      exact lt_of_le_of_lt this (lt_of_le_of_lt (hxle r hr) hpc)
    have := analyticAt_interactionOne_hatRay hC hk S.hG S.hG' ha₁ H hc7 hR hsmR hMX hdm
      hα hsm cc hcψ hδ₁ hX (yhat x) (s := (r : ℂ)) hb
    refine this.congr (Filter.Eventually.of_forall fun l => ?_)
    exact (hatFun_rawOf S.hG' cc f hX _).symm
  have hd3 : ∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 →
      dirS3 (hatFun S.G' S.a₁ S.ν eps S.hG' cc f) (S.hatC x) (rawOf D)
        (((s : ℂ) * (t : ℂ)) • S.hatC x) =
        iteratedDeriv 3 (fun r : ℝ => S'.VkC (S'.psiAtC r x)) (s * t) := by
    intro t ht
    have hst : s * t ∈ Icc (0 : ℝ) 1 :=
      ⟨mul_nonneg hs.1 ht.1, by nlinarith [hs.1, hs.2, ht.1, ht.2]⟩
    unfold dirS3
    have e : (fun τ : ℂ => hatFun S.G' S.a₁ S.ν eps S.hG' cc f
        (rawOf D, ((s : ℂ) * (t : ℂ)) • S.hatC x + τ • S.hatC x)) =
        fun τ : ℂ => Gc (((s * t : ℝ) : ℂ) + τ) := by
      funext τ
      show _ = hatFun S.G' S.a₁ S.ν eps S.hG' cc f (rawOf D, (((s * t : ℝ) : ℂ) + τ) • yhat x)
      rw [add_smul]
      push_cast
      rfl
    rw [e]
    have h1 := congrFun (iteratedDeriv_comp_const_add 3 Gc (((s * t : ℝ)) : ℂ)) 0
    rw [h1, add_zero, ← iteratedDeriv_comp_ofReal 3 Gc (s * t) (hAn _ hst)]
    congr 1
    funext r
    exact hreal r
  have hrs : raySrc3 (hatFun S.G' S.a₁ S.ν eps S.hG' cc f) taylorWeight (S.hatC x) (S.hatC x)
      (s : ℂ) (rawOf D) = (s : ℂ) * ∫ t in (0 : ℝ)..1, taylorWeight (t : ℂ) *
        iteratedDeriv 3 (fun r : ℝ => S'.VkC (S'.psiAtC r x)) (s * t) := by
    unfold raySrc3
    congr 1
    refine intervalIntegral.integral_congr fun t ht => ?_
    rw [Set.uIcc_of_le zero_le_one] at ht
    rw [hd3 t ht]
  have hT := Jr.vkC_ray_taylor_chart D hD hX hC ha₁ H hc7 x hxn hs
  have hI : ∫ u in (0 : ℝ)..1, taylorWeight (u : ℂ) * ((s : ℂ) ^ 3 *
      iteratedDeriv 3 (fun r : ℝ => S'.VkC (S'.psiAtC r x)) (u * s)) =
      (s : ℂ) ^ 3 * ∫ t in (0 : ℝ)..1, taylorWeight (t : ℂ) *
        iteratedDeriv 3 (fun r : ℝ => S'.VkC (S'.psiAtC r x)) (s * t) := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun u _ => ?_
    rw [mul_comm u s]
    ring
  have h1 : Jr.W1 (zeroClass d L N₁ m₁ k N ϱ) (rawOf D, (s : ℂ) • yhat x) =
      -(S.β : ℂ) * S'.VkC (S'.psiAtC s x) := by
    rw [Jr.W1_withDatum (zeroClass d L N₁ m₁ k N ϱ) D hD hX (hxle s hs)]
    exact WoneC_zeroClass (S.withDatum D hD) s x
  show Jr.W1 (zeroClass d L N₁ m₁ k N ϱ) (rawOf D, (s : ℂ) • yhat x) = _
  rw [h1, hrs, hT, hI]
  ring

end Chart

end StepSetting.JointRep

end Balaban.Fluctuation
