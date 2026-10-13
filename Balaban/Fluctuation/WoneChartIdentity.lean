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

section Phys

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}
variable {S : StepSetting d L N₁ m₁ k N ϱ}
variable {c BG κ eps Kc Cx c₂ BG₂ δ₁ δc pp r₀ δ₃ δfl : ℝ}
variable {τι μι : Type*} [DecidableEq τι] [DecidableEq μι]
variable {ϱ₁ ϱ₂ : τι → ℝ} {ϱ₁M ϱ₂M : μι → ℝ}
variable {GkE : ∀ τ, GeneratingSet d L (N₁ * L ^ m₁) (k + 1) (ϱ₁ τ)}
  {GjE : ∀ τ, GeneratingSet d L (N₁ * L ^ m₁) (k + 1) (ϱ₂ τ)}
  {X₀E X₁E : τι → Finset (CTorus d L N₁ m₁ (k + 1))} {jE : τι → ℕ}
  {GkM : ∀ τ, GeneratingSet d L (N₁ * L ^ m₁) (k + 1) (ϱ₁M τ)}
  {GjM : ∀ τ, GeneratingSet d L (N₁ * L ^ m₁) (k + 1) (ϱ₂M τ)}
  {X₀M X₁M : μι → Finset (CTorus d L N₁ m₁ (k + 1))} {jM : μι → ℕ}
  {EE : τι → RawData d L (N₁ * L ^ m₁) (k + 1) N → ℂ}
  {EM : μι → RawData d L (N₁ * L ^ m₁) (k + 1) N → ℂ}
variable (Jr : S.JointRep eps pp)
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

include Jr hC ha₁ H hc7 hR hsmR hMX hdm hα hsm hcψ hδ₁ in
/-- **T3a.**  The interaction half of the exponent at a chart point `e ∈ physV` of the fibre
`h ≡ h₀` is `s²` times the value of `physVal` at the scaled point `(e.1, 0)` (no source). -/
theorem W1_eq_physVal (hpc : pp < cψ) (e : physParam N S)
    (he : e ∈ physV S S.a₁ S.ν eps)
    (hh : ∀ y i, (e.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N).2 y i = (S.h₀ i : ℂ))
    (x : S.E) (hxn : ‖x‖ < pp) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1)
    (𝒯E : Finset τι) (𝒯M : Finset μι)
    (hBE : ∀ τ ∈ 𝒯E, BgSetting N S.G' (GkE τ) (GjE τ) S.a₁ S.ν c BG κ r₀ eps δ₃ (X₀E τ)
      (X₁E τ) (jE τ))
    (hFE : ∀ τ ∈ 𝒯E, FlSetting N S.G' (GkE τ) (stepG d L N₁ m₁ k ϱ) S.a₁ S.ν κ BG eps δ₃ Kc Cx c₂
      BG₂ δ₁ δfl (X₁E τ))
    (ys : μι → CTorus d L N₁ m₁ (k + 1)) (is : μι → Fin N)
    (hBM : ∀ τ ∈ 𝒯M, BgSetting N S.G' (GkM τ) (GjM τ) S.a₁ S.ν c BG κ r₀ eps δ₃ (X₀M τ)
      (X₁M τ) (jM τ))
    (hFM : ∀ τ ∈ 𝒯M, FlSetting N S.G' (GkM τ) (stepG d L N₁ m₁ k ϱ) S.a₁ S.ν κ BG eps δ₃ Kc Cx c₂
      BG₂ δ₁ δfl (X₁M τ))
    (cν : ℂ) (h𝒯E : 𝒯E = ∅) (h𝒯M : 𝒯M = ∅) (hcν : cν = 0) :
    Jr.W1 (zeroClass d L N₁ m₁ k N ϱ)
        ((e.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N), (s : ℂ) • S.hatC x) =
      (s : ℂ) ^ 2 * physVal (EE := EE) (EM := EM) S (S.β : ℂ) S.hG
          ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)
          𝒯E hBE hFE 𝒯M ys is hBM hFM cν (S.hatC x, S.hatC x) (S.hatC x, S.hatC x) (s : ℂ)
          (physInclScaled N S (((1 / S.β : ℝ)) : ℂ) (e.1, 0)) := by
  obtain ⟨D, hX, hq⟩ := he.1
  have hq' : (e.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) = rawOf D := hq
  have hDh : ∀ y i, D.h y i = (S.h₀ i : ℂ) := fun y i => by
    have := hh y i
    rw [hq'] at this
    exact this
  rw [hq', physVal_zeroClass_eq S 𝒯E 𝒯M hBE hFE ys is hBM hFM cν h𝒯E h𝒯M hcν,
    physInclScaled_zeroClass_eq, W1_zeroClass_eq_hat_chart Jr D hDh hX hC ha₁ H hc7 S.hk1
      (lt_of_lt_of_le one_lt_two hR) hsmR hMX hdm hα hsm hcψ hδ₁ hpc x hxn hs]
  simp only [hq', Pi.zero_apply, zero_div, zero_mul, Finset.sum_const_zero, mul_zero, add_zero]

include Jr hC ha₁ H hc7 hR hsmR hRs hsmall hnum hnum' hMX hdm hα hsm hcψ hδ₁ in
/-- **T3: the two-segment sum.**  For the zero class, a chart point `e ∈ physV` of the fibre
`h ≡ h₀`, a real hat variable `ψ̂` with `‖ψ̂‖ < pp < c_ψ` and `s, τ ∈ [0,1]`, the sum of the
interaction exponent `Jr.W1` on the ray at `s` and the source exponent `Jr.W2` on the ray at `τ`
is `s²` times the value of `physVal` at `(e.1, 0)` and the parameter `s`, plus the difference of the
values of `physVal` at `e` and at `(e.1, 0)` at the parameter `τ` (all at the scaled sources
`physInclScaled (1/β)`).  A single value of `physVal` does not equal the sum. -/
theorem sourcePhysVal_jointRep_zero (hpc : pp < cψ) (e : physParam N S)
    (he : e ∈ physV S S.a₁ S.ν eps)
    (hh : ∀ y i, (e.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N).2 y i = (S.h₀ i : ℂ))
    (hβ : (S.β : ℂ) ≠ 0) (x : S.E) (hxn : ‖x‖ < pp) {s τ : ℝ} (hs : s ∈ Icc (0 : ℝ) 1)
    (hτ : τ ∈ Icc (0 : ℝ) 1)
    (𝒯E : Finset τι) (𝒯M : Finset μι)
    (hBE : ∀ τ ∈ 𝒯E, BgSetting N S.G' (GkE τ) (GjE τ) S.a₁ S.ν c BG κ r₀ eps δ₃ (X₀E τ)
      (X₁E τ) (jE τ))
    (hFE : ∀ τ ∈ 𝒯E, FlSetting N S.G' (GkE τ) (stepG d L N₁ m₁ k ϱ) S.a₁ S.ν κ BG eps δ₃ Kc Cx c₂
      BG₂ δ₁ δfl (X₁E τ))
    (ys : μι → CTorus d L N₁ m₁ (k + 1)) (is : μι → Fin N)
    (hBM : ∀ τ ∈ 𝒯M, BgSetting N S.G' (GkM τ) (GjM τ) S.a₁ S.ν c BG κ r₀ eps δ₃ (X₀M τ)
      (X₁M τ) (jM τ))
    (hFM : ∀ τ ∈ 𝒯M, FlSetting N S.G' (GkM τ) (stepG d L N₁ m₁ k ϱ) S.a₁ S.ν κ BG eps δ₃ Kc Cx c₂
      BG₂ δ₁ δfl (X₁M τ))
    (cν : ℂ) (h𝒯E : 𝒯E = ∅) (h𝒯M : 𝒯M = ∅) (hcν : cν = 0) :
    Jr.W1 (zeroClass d L N₁ m₁ k N ϱ)
        ((e.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N), (s : ℂ) • S.hatC x) +
      Jr.W2 (zeroClass d L N₁ m₁ k N ϱ) e.2
        ((e.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N), (τ : ℂ) • S.hatC x) =
      (s : ℂ) ^ 2 * physVal (EE := EE) (EM := EM) S (S.β : ℂ) S.hG
          ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)
          𝒯E hBE hFE 𝒯M ys is hBM hFM cν (S.hatC x, S.hatC x) (S.hatC x, S.hatC x) (s : ℂ)
          (physInclScaled N S (((1 / S.β : ℝ)) : ℂ) (e.1, 0)) +
        (physVal (EE := EE) (EM := EM) S (S.β : ℂ) S.hG ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)
          𝒯E hBE hFE 𝒯M ys is hBM hFM cν (S.hatC x, S.hatC x) (S.hatC x, S.hatC x) (τ : ℂ)
          (physInclScaled N S (((1 / S.β : ℝ)) : ℂ) e) -
        physVal (EE := EE) (EM := EM) S (S.β : ℂ) S.hG ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)
          𝒯E hBE hFE 𝒯M ys is hBM hFM cν (S.hatC x, S.hatC x) (S.hatC x, S.hatC x) (τ : ℂ)
          (physInclScaled N S (((1 / S.β : ℝ)) : ℂ) (e.1, 0))) := by
  have hxb : ∀ r : ℝ, r ∈ Icc (0 : ℝ) 1 → ∀ p, ‖((r : ℂ) • S.hatC x) p‖ ≤ pp := fun r hr p =>
    (S.norm_smul_yhat_le_mul r x p).trans (by
      rw [abs_of_nonneg hr.1]
      exact (mul_le_of_le_one_left (norm_nonneg _) hr.2).trans hxn.le)
  rw [Jr.W1_eq_physVal hC ha₁ H hc7 hR hsmR hMX hdm hα hsm hcψ hδ₁ hpc e he hh x hxn hs
    𝒯E 𝒯M hBE hFE ys is hBM hFM cν h𝒯E h𝒯M hcν,
    Jr.W2_eq_physVal_sub hC ha₁ H hc7 hR hsmR hRs hsmall hnum hnum' hMX hdm hα hsm hcψ hδ₁
      hpc e he hβ (S.hatC x) hxb hτ 𝒯E 𝒯M hBE hFE ys is hBM hFM cν h𝒯E h𝒯M hcν]

end Phys

end StepSetting.JointRep

end Balaban.Fluctuation
