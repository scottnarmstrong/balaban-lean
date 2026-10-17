/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.LocalClassDensityHRep
public import Balaban.Fluctuation.LocalClassChart
public import Balaban.Fluctuation.RootPavingMap

/-!
# Analyticity of the new local densities in the raw datum, and the densities on the class domain

(blocker 6, item (2).)  For the representatives `E1locJ`, `rootTraceJ`, `E0locJ`, `M0J` of
`LocalClassDensityHRep` (functions of the raw block datum `Θ = (Ψ, h̃)`, complex spin and complex
field, not necessarily constant):

* `analyticAt_rootTraceJ`: `-½ Σ_{y ∈ B(z)} tr 𝕃(y,y)` is analytic at every point of the chart
  `Ξ^c(𝔹_{k+1}; 1, ε)` (`analyticOnNhd_rootTrace` composed with the background representative);
* `analyticAt_E1locJ_of_ne_zero`: `ℰ₁^{(k+1)}(z)` is analytic at every point `rawOf D` of the chart
  at which the class densities `ℰ^{(j)}` are analytic at the composed pairs of the path (`hE`) and
  the partition functions `∫ e^{W₁(Θ, s ψ̂)} dν_{p₁}`, `s ∈ [0,1]`, do not vanish (`hZ`);
* `analyticAt_E0locJ_of_ne_zero`, `analyticAt_M0J_of_ne_zero`: the same for `ℰ₀^{(k+1)}(z)` and
  `ℳ₀^{(k+1)}(y; g)_i` (for `M0J`: `ℱ^{(j)}`, `ℳ^{(j)}` analytic at the composed pairs, and
  `∫ e^{W₁(Θ, ψ̂) + W₂(Θ, t ψ̂)} dν_{p₁} ≠ 0`).

**The densities on the class domain** (`Fld × Fld`, the pairs `(Ψ, h)` of fields on the fine torus
of the new level): `densE0 y q = E0locJ (blockIndex y) (clipRaw 𝔹 q)` and
`densM0 x (q, g) i = M0J g x i (clipRaw 𝔹 q)`, `𝔹 = S.G'`.  On a pair `q` of the class domain
`Ξ^c_{k+1}(𝔹; 1, ε)` (`XiDom`) with `ε ≤ eps` the cut-off `clipRaw 𝔹 q` is the raw datum of a
datum `D` of the chart (`clipRaw_mem_xiCRaw_of_xiDom`), and the densities are the new local
densities of the block datum `D` (`densE0_eq`, `densM0_eq`), the landed `E0locC`, `M0C` when
`D.h ≡ h₀`.  They depend on the centre only through its block of level `k + 1`
(`densE0_block`, `densM0`'s centre is the site itself), and they are analytic on the class domain
(`analyticOnNhd_densE0_of_ne_zero`, `analyticOnNhd_densM0_of_ne_zero`).
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Background Balaban.Multiscale Balaban.Localization Balaban.SmallField
  Balaban.SmallField.Def6 Balaban.Analysis Matrix Filter Topology MeasureTheory

namespace StepSetting.JointRep

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ eps pp : ℝ}
  {S : StepSetting d L N₁ m₁ k N ϱ} (Jr : S.JointRep eps pp) (C : StepClass d L N₁ m₁ k N ϱ)
  {c BG κ Kc Cx c₂ BG₂ δ₁ δc : ℝ}

section Analytic

variable (hC : FlCore N S.G' (stepG d L N₁ m₁ k ϱ) S.a₁ S.ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
  (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
  (hdm : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
  (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
  (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)

include hC hMX hdm hα hsm in
/-- **`-½ Σ_{y ∈ B(z)} tr 𝕃(y,y)` is analytic in the raw block datum at every point of the
chart** (spin and field). -/
theorem analyticAt_rootTraceJ {D : BgData S.G' N} (hX : XiCData S.G' S.a S.ν (k + 1) 1 eps D)
    (z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1)))) :
    AnalyticAt ℂ (Jr.rootTraceJ z) (rawOf D) := by
  have hδc : 0 ≤ δc := ((S.withDatumH D).covData_of_chart hC hMX hdm hα hsm hX).2.2.1
  obtain ⟨hI, -⟩ := isDecBg_one_of_xiCData hC hX
  have hs : ∀ P, ‖(fun _ : ↥(cubeIdx S.G') => (1 : ℂ)) P‖ < Real.exp κ := fun P => by
    simpa using Real.one_lt_exp_iff.2 hC.hκ
  have hmem := decDom_of_isDecBg hC hs hX hI hdm hα
  have hb : barField S.G' D.Ψ (bgFieldC S.G' S.a S.ν (bgC0 d L N) D) =
      svec S.G' (bgFieldC S.G' S.a S.ν (bgC0 d L N) D) :=
    funext fun x => funext fun i => barField_eq_svec S.hG' _ _ x i
  have hF₀ : AnalyticAt ℂ Jr.F₀ (rawOf D) := Jr.F₀_an _ ⟨D, hX, rfl⟩
  have hpt : ((fun _ => (1 : ℂ)), (svec S.G' (Jr.F₀ (rawOf D)).1, (Jr.F₀ (rawOf D)).2)) ∈
      DecDom S.G' N κ δc := by
    rw [Jr.F₀_eq D hX, ← hb]
    exact hmem
  have hg := analyticOnNhd_rootTrace (N := N) (xSetting_of_flCore hC S.hk1) hC.hκ.le hMX hδc hsm
    (isUnitLatticeB_unit (G := S.G')).toIsUnitLattice (S.blockU z) _ hpt
  have he : AnalyticAt ℂ (fun Θ : RawData d L (N₁ * L ^ m₁) (k + 1) N =>
      (((fun _ => (1 : ℂ)), (svec S.G' (Jr.F₀ Θ).1, (Jr.F₀ Θ).2)) : DecData S.G' N)) (rawOf D) :=
    analyticAt_const.prod ((analyticAt_pi_iff.2 fun y => analyticAt_pi_iff.2 fun i =>
      analyticAt_svec (G := S.G') (analyticAt_fst.comp hF₀) y i).prod (analyticAt_snd.comp hF₀))
  have hc := AnalyticAt.comp (g := fun e : DecData S.G' N =>
      rootTrace S.G' S.a S.a₁ S.ν (unitQ S.G') (unitP S.G') (S.blockU z) e.1 e.2.1 e.2.2)
    (f := fun Θ : RawData d L (N₁ * L ^ m₁) (k + 1) N =>
      (((fun _ => (1 : ℂ)), (svec S.G' (Jr.F₀ Θ).1, (Jr.F₀ Θ).2)) : DecData S.G' N)) hg he
  unfold rootTraceJ
  exact hc

include hC hMX hdm hα hsm in
/-- **`ℰ₁^{(k+1)}(z)` is analytic in the raw block datum** at every point `rawOf D` of the chart
at which the class densities `ℰ^{(j)}` are analytic at the composed pairs of the path (`hE`) and
the partition functions `∫ e^{W₁(Θ, s ψ̂)} dν_{p₁}`, `s ∈ [0,1]`, do not vanish (`hZ`): a parameter
integral of a jointly analytic integrand (`analyticAt_intervalIntegral_avg`). -/
theorem analyticAt_E1locJ_of_ne_zero (hp₁ : 0 < S.p₁) (hle : S.p₁ ≤ pp)
    {D : BgData S.G' N} (hX : XiCData S.G' S.a S.ν (k + 1) 1 eps D)
    (hE : ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ x : S.E, ‖x‖ ≤ S.p₁ → ∀ j ∈ Finset.Icc 1 k,
      AnalyticAt ℂ
        (fun p : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N => Edens C.m₀ C.Tm j p.1 p.2)
        (Jr.PJ j (rawOf D, (s : ℂ) • yhat x)))
    (hZ : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      ∫ x, Complex.exp (Jr.W1 C (rawOf D, (s : ℂ) • yhat x)) ∂S.nuFl ≠ 0)
    (z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1)))) :
    AnalyticAt ℂ (Jr.E1locJ C z) (rawOf D) := by
  classical
  have hΘ₀ : rawOf D ∈ XiCRaw S.G' S.a S.ν (k + 1) 1 eps := ⟨D, hX, rfl⟩
  have : IsProbabilityMeasure S.nuFl := isProbabilityMeasure_fluctMeasure S.U N hp₁
  have hK : IsCompact (Metric.closedBall (0 : S.E) S.p₁) := isCompact_closedBall _ _
  have hcy : Continuous (fun x : S.E => yhat x) := S.continuous_yhat
  set Kc : Set S.EC := (fun p : ℝ × S.E => (p.1 : ℂ) • yhat p.2) ''
    (Set.Icc (0 : ℝ) 1 ×ˢ Metric.closedBall (0 : S.E) S.p₁) with hKcdef
  have hKc : IsCompact Kc :=
    (isCompact_Icc.prod hK).image ((Complex.continuous_ofReal.comp continuous_fst).smul
      (hcy.comp continuous_snd))
  have hmemKc : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ x ∈ Metric.closedBall (0 : S.E) S.p₁,
      (t : ℂ) • yhat x ∈ Kc := fun t ht x hx => ⟨(t, x), ⟨ht, hx⟩, rfl⟩
  have hE0 : ∀ j ∈ Finset.Icc 1 k, AnalyticAt ℂ
      (fun p : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N => Edens C.m₀ C.Tm j p.1 p.2)
      (Jr.PJ j (rawOf D, 0)) := by
    intro j hj
    have h := hE 0 ⟨le_rfl, zero_le_one⟩ 0 (by rw [norm_zero]; exact hp₁.le) j hj
    rwa [Complex.ofReal_zero, zero_smul] at h
  have hW0 : ∀ v ∈ Kc, AnalyticAt ℂ (Jr.W1 C) (rawOf D, v) := by
    rintro _ ⟨⟨t, x⟩, ⟨ht, hx⟩, rfl⟩
    have hxn : ‖x‖ ≤ S.p₁ := by simpa using hx
    exact Jr.analyticAt_W1 C hΘ₀ (smul_yhat_le (S := S) (S.abs_mul_le_of_mem hle ht hxn))
      (hE t ht x hxn) hE0
  obtain ⟨u₁, hu₁, hΘu₁, hW⟩ := exists_open_nhds_analyticAt hKc hW0
  have hMx0 : ∀ p q, AnalyticAt ℂ (fun Θ => Jr.Mx Θ p q) (rawOf D) := fun p q =>
    Jr.Mx_an p q _ hΘ₀
  have hdet0 : (Jr.Mx (rawOf D)).det ≠ 0 := by
    have h1 : (Jr.Mx (rawOf D)).det = _ :=
      Jr.det_Mx_eq_trace (S.withDatumH D) hC hMX hdm hα hsm hX
    rw [h1]
    exact Complex.exp_ne_zero _
  have hev : ∀ᶠ Θ in 𝓝 (rawOf D),
      (∀ p q, AnalyticAt ℂ (fun Θ => Jr.Mx Θ p q) Θ) ∧ (Jr.Mx Θ).det ≠ 0 :=
    (Filter.eventually_all.2 fun p => Filter.eventually_all.2 fun q =>
      (hMx0 p q).eventually_analyticAt).and
      ((analyticAt_det hMx0).continuousAt.eventually_ne hdet0)
  obtain ⟨u₂, hu₂P, hu₂, hΘu₂⟩ := eventually_nhds_iff.1 hev
  set u := u₁ ∩ u₂ with hudef
  have huo : IsOpen u := hu₁.inter hu₂
  have hΘu : rawOf D ∈ u := ⟨hΘu₁, hΘu₂⟩
  -- the hat direction of the masked shift, as a function of the datum and a hat variable
  set Pd : RawData d L (N₁ * L ^ m₁) (k + 1) N × (S.EC × S.EC) → S.EC := fun p =>
    (Jr.Mx p.1)⁻¹ *ᵥ S.maskUC z (Jr.Mx p.1 *ᵥ p.2.2) with hPddef
  have hPd : ∀ p : RawData d L (N₁ * L ^ m₁) (k + 1) N × (S.EC × S.EC), p.1 ∈ u₂ →
      AnalyticAt ℂ Pd p := by
    intro p hp
    obtain ⟨hMa, hd⟩ := hu₂P p.1 hp
    have hM : ∀ a b, AnalyticAt ℂ
        (fun p : RawData d L (N₁ * L ^ m₁) (k + 1) N × (S.EC × S.EC) => Jr.Mx p.1 a b) p :=
      fun a b => (hMa a b).comp analyticAt_fst
    have hMi : ∀ a b, AnalyticAt ℂ
        (fun p : RawData d L (N₁ * L ^ m₁) (k + 1) N × (S.EC × S.EC) => (Jr.Mx p.1)⁻¹ a b) p :=
      analyticAt_inv_apply hM hd
    refine analyticAt_pi_iff.2 fun q => ?_
    simp only [Matrix.mulVec, dotProduct]
    refine Finset.analyticAt_fun_sum _ fun r _ => (hMi q r).mul ?_
    unfold StepSetting.maskUC
    by_cases hr : r.1 ∈ S.blockU z
    · simp only [hr, ↓reduceIte]
      refine Finset.analyticAt_fun_sum _ fun s _ => (hM r s).mul ?_
      exact ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : S.U × Fin N => ℂ) s).analyticAt
        _).comp (analyticAt_snd.comp analyticAt_snd)
    · simp only [hr, ↓reduceIte]
      exact analyticAt_const
  -- the joint integrand
  set Fd : RawData d L (N₁ * L ^ m₁) (k + 1) N × (S.EC × S.EC) → ℂ := fun p =>
    (fderiv ℂ (Jr.W1 C) (p.1, p.2.1)) ((0 : RawData d L (N₁ * L ^ m₁) (k + 1) N), Pd p) *
      Complex.exp (Jr.W1 C (p.1, p.2.1)) with hFddef
  have hFd : ∀ p : RawData d L (N₁ * L ^ m₁) (k + 1) N × (S.EC × S.EC), p.1 ∈ u → p.2.1 ∈ Kc →
      AnalyticAt ℂ Fd p := by
    intro p hp hv
    have hWp : AnalyticAt ℂ (Jr.W1 C) (p.1, p.2.1) := hW p.1 hp.1 p.2.1 hv
    have hproj : AnalyticAt ℂ
        (fun p : RawData d L (N₁ * L ^ m₁) (k + 1) N × (S.EC × S.EC) => (p.1, p.2.1)) p :=
      analyticAt_fst.prod (analyticAt_fst.comp analyticAt_snd)
    have h1 : AnalyticAt ℂ (fun p : RawData d L (N₁ * L ^ m₁) (k + 1) N × (S.EC × S.EC) =>
        fderiv ℂ (Jr.W1 C) (p.1, p.2.1)) p := hWp.fderiv.comp_of_eq hproj rfl
    have h2 : AnalyticAt ℂ (fun p : RawData d L (N₁ * L ^ m₁) (k + 1) N × (S.EC × S.EC) =>
        ((0 : RawData d L (N₁ * L ^ m₁) (k + 1) N), Pd p)) p :=
      analyticAt_const.prod (hPd p hp.2)
    have h3 : AnalyticAt ℂ (fun p : RawData d L (N₁ * L ^ m₁) (k + 1) N × (S.EC × S.EC) =>
        (fderiv ℂ (Jr.W1 C) (p.1, p.2.1)) ((0 : RawData d L (N₁ * L ^ m₁) (k + 1) N), Pd p))
        p :=
      ((ContinuousLinearMap.id ℂ ((RawData d L (N₁ * L ^ m₁) (k + 1) N × S.EC) →L[ℂ] ℂ)
        ).analyticAt_bilinear _).comp (h1.prod h2)
    exact h3.mul (hWp.comp_of_eq hproj rfl).cexp
  -- the two integrands of the average
  set Nf : RawData d L (N₁ * L ^ m₁) (k + 1) N → ℝ → S.E → ℂ := fun Θ t x =>
    Fd (Θ, ((t : ℂ) • yhat x, yhat x)) with hNfdef
  set Zf : RawData d L (N₁ * L ^ m₁) (k + 1) N → ℝ → S.E → ℂ := fun Θ t x =>
    Complex.exp (Jr.W1 C (Θ, (t : ℂ) • yhat x)) with hZfdef
  have hmap : Continuous (fun q : (RawData d L (N₁ * L ^ m₁) (k + 1) N × ℝ) × S.E =>
      ((q.1.1, ((q.1.2 : ℂ) • yhat q.2, yhat q.2)) :
        RawData d L (N₁ * L ^ m₁) (k + 1) N × (S.EC × S.EC))) :=
    continuous_fst.fst.prodMk ((((Complex.continuous_ofReal.comp continuous_fst.snd).smul
      (hcy.comp continuous_snd))).prodMk (hcy.comp continuous_snd))
  have hmapW : Continuous (fun q : (RawData d L (N₁ * L ^ m₁) (k + 1) N × ℝ) × S.E =>
      ((q.1.1, (q.1.2 : ℂ) • yhat q.2) : RawData d L (N₁ * L ^ m₁) (k + 1) N × S.EC)) :=
    continuous_fst.fst.prodMk ((Complex.continuous_ofReal.comp continuous_fst.snd).smul
      (hcy.comp continuous_snd))
  have hNa : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ x ∈ Metric.closedBall (0 : S.E) S.p₁,
      AnalyticOnNhd ℂ (fun Θ => Nf Θ t x) u := fun t ht x hx Θ hΘ =>
    analyticAt_slice (hFd (Θ, ((t : ℂ) • yhat x, yhat x)) hΘ (hmemKc t ht x hx))
  have hZa : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ x ∈ Metric.closedBall (0 : S.E) S.p₁,
      AnalyticOnNhd ℂ (fun Θ => Zf Θ t x) u := fun t ht x hx Θ hΘ =>
    (analyticAt_slice (hW Θ hΘ.1 _ (hmemKc t ht x hx))).cexp
  have hNc : ContinuousOn (fun q : (RawData d L (N₁ * L ^ m₁) (k + 1) N × ℝ) × S.E =>
      Nf q.1.1 q.1.2 q.2) ((u ×ˢ Set.Icc (0 : ℝ) 1) ×ˢ Metric.closedBall (0 : S.E) S.p₁) := by
    intro q hq
    exact ContinuousAt.comp_continuousWithinAt (g := Fd)
      (f := fun q : (RawData d L (N₁ * L ^ m₁) (k + 1) N × ℝ) × S.E =>
        ((q.1.1, ((q.1.2 : ℂ) • yhat q.2, yhat q.2)) :
          RawData d L (N₁ * L ^ m₁) (k + 1) N × (S.EC × S.EC)))
      (hFd _ hq.1.1 (hmemKc q.1.2 hq.1.2 q.2 hq.2)).continuousAt hmap.continuousWithinAt
  have hZc : ContinuousOn (fun q : (RawData d L (N₁ * L ^ m₁) (k + 1) N × ℝ) × S.E =>
      Zf q.1.1 q.1.2 q.2) ((u ×ˢ Set.Icc (0 : ℝ) 1) ×ˢ Metric.closedBall (0 : S.E) S.p₁) := by
    intro q hq
    exact (ContinuousAt.comp_continuousWithinAt (g := Jr.W1 C)
      (f := fun q : (RawData d L (N₁ * L ^ m₁) (k + 1) N × ℝ) × S.E =>
        ((q.1.1, (q.1.2 : ℂ) • yhat q.2) : RawData d L (N₁ * L ^ m₁) (k + 1) N × S.EC))
      (hW _ hq.1.1.1 _ (hmemKc q.1.2 hq.1.2 q.2 hq.2)).continuousAt
      hmapW.continuousWithinAt).cexp
  have hmain := analyticAt_intervalIntegral_avg (μ := S.nuFl) hK measurableSet_closedBall
    (S.ae_mem_closedBall hp₁) huo hΘu hNa hZa hNc hZc hZ
  refine hmain.congr ?_
  filter_upwards [huo.mem_nhds hΘu] with Θ hΘ
  unfold E1locJ avgFun partFun
  refine intervalIntegral.integral_congr fun t ht => ?_
  rw [Set.uIcc_of_le zero_le_one] at ht
  refine congrArg (fun w : ℂ => w / ∫ x, Zf Θ t x ∂S.nuFl) ?_
  refine integral_congr_ae ((S.ae_mem_closedBall hp₁).mono fun x hx => ?_)
  have hWd : DifferentiableAt ℂ (Jr.W1 C) (Θ, (t : ℂ) • yhat x) :=
    (hW Θ hΘ.1 _ (hmemKc t ht x hx)).differentiableAt
  have hpart : fderiv ℂ (fun w : S.EC => Jr.W1 C (Θ, w)) ((t : ℂ) • yhat x) =
      (fderiv ℂ (Jr.W1 C) (Θ, (t : ℂ) • yhat x)).comp
        (ContinuousLinearMap.inr ℂ (RawData d L (N₁ * L ^ m₁) (k + 1) N) S.EC) :=
    (hWd.hasFDerivAt.comp ((t : ℂ) • yhat x)
      (hasFDerivAt_prodMk_right Θ ((t : ℂ) • yhat x))).fderiv
  show Fd (Θ, ((t : ℂ) • yhat x, yhat x)) =
    (fderiv ℂ (fun w : S.EC => Jr.W1 C (Θ, w)) ((t : ℂ) • yhat x))
      ((Jr.Mx Θ)⁻¹ *ᵥ S.maskUC z (Jr.Mx Θ *ᵥ yhat x)) *
      Complex.exp (Jr.W1 C (Θ, (t : ℂ) • yhat x))
  rw [hpart]
  rfl

include hC hMX hdm hα hsm in
/-- **`ℰ₀^{(k+1)}(z)` is analytic in the raw block datum** under the hypotheses of
`analyticAt_E1locJ_of_ne_zero`. -/
theorem analyticAt_E0locJ_of_ne_zero (hp₁ : 0 < S.p₁) (hle : S.p₁ ≤ pp)
    {D : BgData S.G' N} (hX : XiCData S.G' S.a S.ν (k + 1) 1 eps D)
    (hE : ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ x : S.E, ‖x‖ ≤ S.p₁ → ∀ j ∈ Finset.Icc 1 k,
      AnalyticAt ℂ
        (fun p : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N => Edens C.m₀ C.Tm j p.1 p.2)
        (Jr.PJ j (rawOf D, (s : ℂ) • yhat x)))
    (hZ : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      ∫ x, Complex.exp (Jr.W1 C (rawOf D, (s : ℂ) • yhat x)) ∂S.nuFl ≠ 0)
    (z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1)))) :
    AnalyticAt ℂ (Jr.E0locJ C z) (rawOf D) :=
  (Jr.analyticAt_rootTraceJ hC hMX hdm hα hsm hX z).add
    (Jr.analyticAt_E1locJ_of_ne_zero C hC hMX hdm hα hsm hp₁ hle hX hE hZ z)

end Analytic

/-- **`ℳ₀^{(k+1)}(y; g)_i` is analytic in the raw block datum** at every point `Θ` of the chart
at which the class terms `ℰ^{(j)}`, `ℱ^{(j)}(·, ·, g)`, `ℳ^{(j)}(y; ·, ·, g)_i` are analytic at
the composed pairs of the path and the partition functions
`∫ e^{W₁(Θ, ψ̂) + W₂(Θ, t ψ̂)} dν_{p₁}`, `t ∈ [0,1]`, do not vanish (`analyticAt_avgJ`). -/
theorem analyticAt_M0J_of_ne_zero (hp₁ : 0 < S.p₁) (hle : S.p₁ ≤ pp)
    {Θ : RawData d L (N₁ * L ^ m₁) (k + 1) N} (hΘ : Θ ∈ XiCRaw S.G' S.a S.ν (k + 1) 1 eps)
    (g : Fld d L N₁ m₁ (k + 1) N) (y : CTorus d L N₁ m₁ (k + 1)) (i : Fin N)
    (hE : ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ x : S.E, ‖x‖ ≤ S.p₁ → ∀ j ∈ Finset.Icc 1 k,
      AnalyticAt ℂ
        (fun p : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N => Edens C.m₀ C.Tm j p.1 p.2)
        (Jr.PJ j (Θ, (s : ℂ) • yhat x)))
    (hF : ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ x : S.E, ‖x‖ ≤ S.p₁ → ∀ j ∈ Finset.Icc 1 k,
      AnalyticAt ℂ
        (fun p : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N => Floc C.m₀ C.Tm j p.1 p.2 g)
        (Jr.PJ j (Θ, (s : ℂ) • yhat x)))
    (hM : ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ x : S.E, ‖x‖ ≤ S.p₁ → ∀ j ∈ Finset.Icc 1 k,
      AnalyticAt ℂ
        (fun p : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N =>
          Mloc C.m₀ C.Tm j y p.1 p.2 g i)
        (Jr.PJ j (Θ, (s : ℂ) • yhat x)))
    (hZ : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ∫ x, Complex.exp (Jr.W1 C (Θ, yhat x) + Jr.W2 C g (Θ, (t : ℂ) • yhat x)) ∂S.nuFl ≠ 0) :
    AnalyticAt ℂ (Jr.M0J C g y i) Θ := by
  have h0 : ∀ (j : ℕ) {P : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N → Prop},
      (∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ x : S.E, ‖x‖ ≤ S.p₁ → P (Jr.PJ j (Θ, (s : ℂ) • yhat x))) →
      P (Jr.PJ j (Θ, 0)) := by
    intro j P h
    have h1 := h 0 ⟨le_rfl, zero_le_one⟩ 0 (by rw [norm_zero]; exact hp₁.le)
    rwa [Complex.ofReal_zero, zero_smul] at h1
  have hb : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ x : S.E, ‖x‖ ≤ S.p₁ →
      ∀ p, ‖((t : ℂ) • yhat x) p‖ ≤ pp := fun t ht x hx =>
    smul_yhat_le (S := S) (S.abs_mul_le_of_mem hle ht hx)
  refine analyticAt_const.mul (S.analyticAt_avgJ hp₁ (fun x hx => ?_)
    (fun t ht x hx => ?_) (fun t ht x hx => ?_) hZ)
  · have h1 := hb 1 ⟨zero_le_one, le_rfl⟩ x hx
    simp only [Complex.ofReal_one, one_smul] at h1
    have hE1 := hE 1 ⟨zero_le_one, le_rfl⟩ x hx
    simp only [Complex.ofReal_one, one_smul] at hE1
    exact Jr.analyticAt_W1 C hΘ h1 hE1 fun j hj => h0 j fun s hs x hx => hE s hs x hx j hj
  · exact Jr.analyticAt_W2 C hΘ (hb t ht x hx) g (hF t ht x hx)
      fun j hj => h0 j fun s hs x hx => hF s hs x hx j hj
  · exact Jr.analyticAt_McJ C hΘ (hb t ht x hx) g y i (hM t ht x hx)

/-! ### The densities on the class domain -/

section Class

/-- **The energy density of the new level on pairs of fields** (the density `𝒟(y)(Ψ, h)` of the
expansion identity `hDz`, P4 (2.57), (4.22)): `ℰ₀^{(k+1)}` of the block of `y`, evaluated at the
cut-off `clipRaw 𝔹 (Ψ, h)` of the pair to the data sites of `𝔹 = S.G'`. -/
noncomputable def densE0 (y : CTorus d L N₁ m₁ (k + 1))
    (q : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N) : ℂ :=
  Jr.E0locJ C (blockIndex y) (clipRaw S.G' q)

/-- **The source density of the new level on pairs of fields and sources** (the density
`𝒟_M(x)((Ψ, h), g)_i` of the expansion identity `hDM`, P4 (2.53)): `ℳ₀^{(k+1)}(x; g)_i` at the
cut-off of the pair. -/
noncomputable def densM0 (x : CTorus d L N₁ m₁ (k + 1))
    (qg : (Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N) × Fld d L N₁ m₁ (k + 1) N)
    (i : Fin N) : ℂ :=
  Jr.M0J C qg.2 x i (clipRaw S.G' qg.1)

/-- **The energy density depends on the centre only through its block** of level `k + 1` (the
input `hDzblock`). -/
theorem densE0_block {y y' : CTorus d L N₁ m₁ (k + 1)}
    (h : blockBase (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L (k + 1) y =
      blockBase (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L (k + 1) y')
    (q : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N) :
    Jr.densE0 C y q = Jr.densE0 C y' q := by
  have hb : blockIndex y = blockIndex y' :=
    rootSite_injective (by rw [rootSite_blockIndex, rootSite_blockIndex, h])
  unfold densE0
  rw [hb]

/-- **On a pair whose cut-off is the raw datum of a datum `D` of the chart, the energy density is
`ℰ₀^{(k+1)}` of the block datum `D`** (any field, `E0locH`), where the class densities are analytic
at the composed pairs of the path. -/
theorem densE0_eq
    (hC : FlCore N S.G' (stepG d L N₁ m₁ k ϱ) S.a₁ S.ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    (hdm : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    (hβ : 0 < S.β) (hp₁ : 0 < S.p₁) (hle : S.p₁ ≤ pp)
    {D : BgData S.G' N} (hX : XiCData S.G' S.a S.ν (k + 1) 1 eps D)
    (hE : ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ x : S.E, ‖x‖ ≤ S.p₁ → ∀ j ∈ Finset.Icc 1 k,
      AnalyticAt ℂ
        (fun p : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N => Edens C.m₀ C.Tm j p.1 p.2)
        (Jr.PJ j (rawOf D, (s : ℂ) • yhat x)))
    {q : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N} (hq : clipRaw S.G' q = rawOf D)
    (y : CTorus d L N₁ m₁ (k + 1)) :
    Jr.densE0 C y q = (S.withDatumH D).E0locH C (blockIndex y) := by
  unfold densE0
  rw [hq]
  exact Jr.E0locJ_datum C (S.withDatumH D) hX hC hMX hdm hα hsm hβ hp₁ hle hE _

/-- **On a pair whose cut-off is the raw datum of a datum `D` of the chart, the source density is
`ℳ₀^{(k+1)}` of the block datum `D`** (any field, `M0H`). -/
theorem densM0_eq (hp₁ : 0 < S.p₁) (hle : S.p₁ ≤ pp)
    {D : BgData S.G' N} (hX : XiCData S.G' S.a S.ν (k + 1) 1 eps D)
    {q : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N} (hq : clipRaw S.G' q = rawOf D)
    (g : Fld d L N₁ m₁ (k + 1) N) (x : CTorus d L N₁ m₁ (k + 1)) (i : Fin N) :
    Jr.densM0 C x (q, g) i = (S.withDatumH D).M0H C g x i := by
  unfold densM0
  rw [hq]
  exact Jr.M0J_datum C (S.withDatumH D) hX hp₁ hle g x i

/-- **The energy density is analytic on the class domain** `Ξ^c_{k+1}(𝔹; 1, ε)` (`XiDom`,
`ε ≤ eps`), where at every datum of the chart the class densities are analytic at the composed
pairs of the path and the partition functions of `μ_{s,0}` do not vanish. -/
theorem analyticOnNhd_densE0_of_ne_zero
    (hC : FlCore N S.G' (stepG d L N₁ m₁ k ϱ) S.a₁ S.ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    (hdm : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4) (hp₁ : 0 < S.p₁) (hle : S.p₁ ≤ pp)
    (hE : ∀ D : BgData S.G' N, XiCData S.G' S.a S.ν (k + 1) 1 eps D →
      ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ x : S.E, ‖x‖ ≤ S.p₁ → ∀ j ∈ Finset.Icc 1 k,
      AnalyticAt ℂ
        (fun p : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N => Edens C.m₀ C.Tm j p.1 p.2)
        (Jr.PJ j (rawOf D, (s : ℂ) • yhat x)))
    (hZ : ∀ D : BgData S.G' N, XiCData S.G' S.a S.ν (k + 1) 1 eps D →
      ∀ s ∈ Set.Icc (0 : ℝ) 1,
      ∫ x, Complex.exp (Jr.W1 C (rawOf D, (s : ℂ) • yhat x)) ∂S.nuFl ≠ 0)
    {ε : ℝ} (hε : ε ≤ eps) (y : CTorus d L N₁ m₁ (k + 1)) :
    AnalyticOnNhd ℂ (Jr.densE0 C y) {q | XiDom S.G' S.a S.ν (k + 1) ε q.1 q.2} := by
  intro q hq
  obtain ⟨D, hD, hcl⟩ := clipRaw_mem_xiCRaw_of_xiDom hε hq
  have h := Jr.analyticAt_E0locJ_of_ne_zero C hC hMX hdm hα hsm hp₁ hle hD (hE D hD) (hZ D hD)
    (blockIndex y)
  rw [← hcl] at h
  exact h.comp (analyticAt_clipRaw q)

/-- **The source density is analytic on the class domain** `Ξ^c_{k+1}(𝔹; 1, ε)` (`ε ≤ eps`),
where at every datum of the chart the class terms are analytic at the composed pairs of the path
and the partition functions of `μ_{1,t}` do not vanish. -/
theorem analyticOnNhd_densM0_of_ne_zero (hp₁ : 0 < S.p₁) (hle : S.p₁ ≤ pp)
    (g : Fld d L N₁ m₁ (k + 1) N) (x : CTorus d L N₁ m₁ (k + 1)) (i : Fin N)
    (hE : ∀ D : BgData S.G' N, XiCData S.G' S.a S.ν (k + 1) 1 eps D →
      ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ x : S.E, ‖x‖ ≤ S.p₁ → ∀ j ∈ Finset.Icc 1 k,
      AnalyticAt ℂ
        (fun p : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N => Edens C.m₀ C.Tm j p.1 p.2)
        (Jr.PJ j (rawOf D, (s : ℂ) • yhat x)))
    (hF : ∀ D : BgData S.G' N, XiCData S.G' S.a S.ν (k + 1) 1 eps D →
      ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ x : S.E, ‖x‖ ≤ S.p₁ → ∀ j ∈ Finset.Icc 1 k,
      AnalyticAt ℂ
        (fun p : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N => Floc C.m₀ C.Tm j p.1 p.2 g)
        (Jr.PJ j (rawOf D, (s : ℂ) • yhat x)))
    (hM : ∀ D : BgData S.G' N, XiCData S.G' S.a S.ν (k + 1) 1 eps D →
      ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ x' : S.E, ‖x'‖ ≤ S.p₁ → ∀ j ∈ Finset.Icc 1 k,
      AnalyticAt ℂ
        (fun p : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N =>
          Mloc C.m₀ C.Tm j x p.1 p.2 g i)
        (Jr.PJ j (rawOf D, (s : ℂ) • yhat x')))
    (hZ : ∀ D : BgData S.G' N, XiCData S.G' S.a S.ν (k + 1) 1 eps D →
      ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ∫ x, Complex.exp (Jr.W1 C (rawOf D, yhat x) + Jr.W2 C g (rawOf D, (t : ℂ) • yhat x))
        ∂S.nuFl ≠ 0)
    {ε : ℝ} (hε : ε ≤ eps) :
    AnalyticOnNhd ℂ (fun q : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N =>
      Jr.densM0 C x (q, g) i) {q | XiDom S.G' S.a S.ν (k + 1) ε q.1 q.2} := by
  intro q hq
  obtain ⟨D, hD, hcl⟩ := clipRaw_mem_xiCRaw_of_xiDom hε hq
  have h := Jr.analyticAt_M0J_of_ne_zero C hp₁ hle ⟨D, hD, rfl⟩ g x i (hE D hD) (hF D hD)
    (hM D hD) (hZ D hD)
  rw [← hcl] at h
  exact h.comp (analyticAt_clipRaw q)

end Class

end StepSetting.JointRep

end Balaban.Fluctuation
