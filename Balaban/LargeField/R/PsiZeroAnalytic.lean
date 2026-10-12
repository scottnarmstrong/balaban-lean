/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.PsiZeroAnalyticAction
public import Balaban.LargeField.R.PsiZeroAnalyticIFT
public import Balaban.LargeField.R.PsiZeroAnalyticLocal
public import Balaban.LargeField.R.PsiZeroInput
import Mathlib

/-!
# Lemma III.3.3: analyticity of the solution `ψ⁰_k` in `ψ_k` (from the cited expansion estimate)

The complex variational function `FC (ξ, q) = effC (mergeFieldC q ξ)` is complex-analytic at the real points of the
tube and equals the real variational function `effOn` there (`PsiZeroAnalyticAction`).  At a real nondegenerate
critical point it has an analytic zero of the gradient (`PsiZeroAnalyticIFT`).  Combined with the local structure of
the solution (`PsiZeroAnalyticLocal`: the solution is the merge of the unique critical point in the ball):

* `analytic_zero_effOn`: the critical point of `effOn ψ_k` near `u₀` is the restriction of a holomorphic function of
  the complex block field `q`, real for real `q`;
* `psiZero_analytic_of_input`: the solution of (2.34) is the restriction to real block fields of a holomorphic map of
  the complex block field near every real point of `Ψ̃(X ∖ Z₀; δ)`, equal to `q` off `Z₀`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open Balaban Balaban.Multiscale Balaban.Background Filter Topology Metric RealCrit

section Embed

variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L]

/-- The embedding `ℝ^N`-valued block fields into `ℂ^N`-valued ones. -/
noncomputable def ofRealField : BlockField d L N₀ k N →L[ℝ] BlockFieldC d L N₀ k N :=
  LinearMap.toContinuousLinearMap
    { toFun := fun p z i => (p z i : ℂ)
      map_add' := fun p q => by funext z i; simp
      map_smul' := fun c p => by funext z i; simp }

theorem ofRealField_apply (p : BlockField d L N₀ k N) (z : Torus d (N₀ * L ^ (k - k))) (i : Fin N) :
    ofRealField p z i = (p z i : ℂ) := rfl

theorem norm_ofRealField (p : BlockField d L N₀ k N) : ‖ofRealField p‖ = ‖p‖ := by
  apply le_antisymm
  · refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun z => ?_
    refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => ?_
    rw [ofRealField_apply, Complex.norm_real]
    exact (norm_le_pi_norm (p z) i).trans (norm_le_pi_norm p z)
  · refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun z => ?_
    refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => ?_
    have h1 : ‖ofRealField p z i‖ ≤ ‖ofRealField p z‖ := norm_le_pi_norm (ofRealField p z) i
    have h2 : ‖ofRealField p z‖ ≤ ‖ofRealField p‖ := norm_le_pi_norm (ofRealField p) z
    rw [ofRealField_apply, Complex.norm_real] at h1
    exact h1.trans h2

variable (Zf : Finset (Torus d (N₀ * L ^ (k - k))))

/-- The complex merge: `u` on `Zf`, `ψ_k` off `Zf`. -/
def mergeFieldC (ψk : BlockFieldC d L N₀ k N) (u : ↥Zf × Fin N → ℂ) : BlockFieldC d L N₀ k N :=
  fun z i => if h : z ∈ Zf then u (⟨z, h⟩, i) else ψk z i

theorem mergeFieldC_real (p : BlockField d L N₀ k N) (u : SuppSpace Zf N) :
    mergeFieldC Zf (ofRealField p) (jEL u) = ofRealField (mergeField Zf p u) := by
  funext z i
  by_cases h : z ∈ Zf
  · simp [mergeFieldC, mergeField, h, jEL_apply, ofRealField_apply]
  · simp [mergeFieldC, mergeField, h, ofRealField_apply]

theorem analyticAt_mergeFieldC (w : (↥Zf × Fin N → ℂ) × BlockFieldC d L N₀ k N) :
    AnalyticAt ℂ (fun w : (↥Zf × Fin N → ℂ) × BlockFieldC d L N₀ k N => mergeFieldC Zf w.2 w.1) w := by
  refine AnalyticAt.pi fun z => AnalyticAt.pi fun i => ?_
  by_cases h : z ∈ Zf
  · have : (fun w : (↥Zf × Fin N → ℂ) × BlockFieldC d L N₀ k N => mergeFieldC Zf w.2 w.1 z i) =
        fun w => w.1 ((⟨z, h⟩ : ↥Zf), i) := by funext w; simp [mergeFieldC, h]
    rw [this]
    exact analyticAt_apply analyticAt_fst _
  · have : (fun w : (↥Zf × Fin N → ℂ) × BlockFieldC d L N₀ k N => mergeFieldC Zf w.2 w.1 z i) =
        fun w => w.2 z i := by funext w; simp [mergeFieldC, h]
    rw [this]
    exact analyticAt_apply (analyticAt_apply analyticAt_snd z) i

theorem continuous_mergeField :
    Continuous (fun w : SuppSpace Zf N × BlockField d L N₀ k N => mergeField Zf w.2 w.1) := by
  refine continuous_pi fun z => continuous_pi fun i => ?_
  by_cases h : z ∈ Zf
  · have : (fun w : SuppSpace Zf N × BlockField d L N₀ k N => mergeField Zf w.2 w.1 z i) =
        fun w => w.1 ((⟨z, h⟩ : ↥Zf), i) := by funext w; simp [mergeField, h]
    rw [this]
    exact (EuclideanSpace.proj (((⟨z, h⟩ : ↥Zf), i) : ↥Zf × Fin N)).continuous.comp continuous_fst
  · have : (fun w : SuppSpace Zf N × BlockField d L N₀ k N => mergeField Zf w.2 w.1 z i) =
        fun w => w.2 z i := by funext w; simp [mergeField, h]
    rw [this]
    fun_prop

end Embed

section Partial

variable {E1 E2 : Type*} [NormedAddCommGroup E1] [NormedSpace ℝ E1] [NormedAddCommGroup E2]
  [NormedSpace ℝ E2]

theorem hasFDerivAt_slice (p : E2) (u : E1) :
    HasFDerivAt (fun u' : E1 => ((u', p) : E1 × E2)) (ContinuousLinearMap.inl ℝ E1 E2) u := by
  have := (hasFDerivAt_id (𝕜 := ℝ) u).prodMk (hasFDerivAt_const (𝕜 := ℝ) p u)
  exact this

/-- The partial derivative of a jointly differentiable function. -/
theorem fderiv_partial {f : E1 × E2 → ℝ} {u : E1} {p : E2} (hf : DifferentiableAt ℝ f (u, p)) (v : E1) :
    fderiv ℝ (fun u' : E1 => f (u', p)) u v = fderiv ℝ f (u, p) (v, 0) := by
  have h := HasFDerivAt.comp u (g := f) (f := fun u' : E1 => ((u', p) : E1 × E2)) hf.hasFDerivAt
    (hasFDerivAt_slice p u)
  have h' : HasFDerivAt (fun u' : E1 => f (u', p))
      ((fderiv ℝ f (u, p)).comp (ContinuousLinearMap.inl ℝ E1 E2)) u := h
  rw [h'.fderiv]
  rfl

/-- The second partial derivative of a jointly `C²` function. -/
theorem fderiv2_partial {f : E1 × E2 → ℝ} {u0 : E1} {p0 : E2} (hf : ContDiffAt ℝ 2 f (u0, p0)) (v : E1) :
    fderiv ℝ (fderiv ℝ (fun u : E1 => f (u, p0))) u0 v v =
      fderiv ℝ (fderiv ℝ f) (u0, p0) (v, 0) (v, 0) := by
  have hg : ContDiffAt ℝ 2 (fun u : E1 => f (u, p0)) u0 :=
    ContDiffAt.comp u0 (g := f) (f := fun u : E1 => ((u, p0) : E1 × E2)) hf
      (contDiffAt_id.prodMk contDiffAt_const)
  have hgd : DifferentiableAt ℝ (fderiv ℝ (fun u : E1 => f (u, p0))) u0 :=
    (hg.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hf1 : ContDiffAt ℝ 1 (fderiv ℝ f) (u0, p0) := hf.fderiv_right (m := 1) (by norm_num)
  have hfd : DifferentiableAt ℝ (fderiv ℝ f) (u0, p0) := hf1.differentiableAt (by norm_num)
  -- eventually differentiable
  have hev : ∀ᶠ u in 𝓝 u0, DifferentiableAt ℝ f (u, p0) := by
    have h0 : ∀ᶠ w in 𝓝 (u0, p0), ContDiffAt ℝ 2 f w := hf.eventually (by simp)
    have hc : Continuous (fun u : E1 => ((u, p0) : E1 × E2)) := continuous_id.prodMk continuous_const
    filter_upwards [hc.continuousAt.eventually h0] with u hu using hu.differentiableAt (by norm_num)
  have heq : (fun u => fderiv ℝ (fun u' : E1 => f (u', p0)) u v) =ᶠ[𝓝 u0]
      fun u => fderiv ℝ f (u, p0) (v, 0) := by
    filter_upwards [hev] with u hu using fderiv_partial hu v
  have hL : HasFDerivAt (fun u => fderiv ℝ (fun u' : E1 => f (u', p0)) u v)
      ((ContinuousLinearMap.apply ℝ ℝ v).comp (fderiv ℝ (fderiv ℝ (fun u : E1 => f (u, p0))) u0)) u0 :=
    (ContinuousLinearMap.apply ℝ ℝ v).hasFDerivAt.comp u0 hgd.hasFDerivAt
  have hR : HasFDerivAt (fun u => fderiv ℝ f (u, p0) (v, 0))
      ((ContinuousLinearMap.apply ℝ ℝ ((v, 0) : E1 × E2)).comp
        ((fderiv ℝ (fderiv ℝ f) (u0, p0)).comp (ContinuousLinearMap.inl ℝ E1 E2))) u0 := by
    have h1 : HasFDerivAt (fun u : E1 => fderiv ℝ f (u, p0))
        ((fderiv ℝ (fderiv ℝ f) (u0, p0)).comp (ContinuousLinearMap.inl ℝ E1 E2)) u0 :=
      HasFDerivAt.comp u0 (g := fderiv ℝ f) (f := fun u' : E1 => ((u', p0) : E1 × E2)) hfd.hasFDerivAt
        (hasFDerivAt_slice p0 u0)
    exact (ContinuousLinearMap.apply ℝ ℝ ((v, 0) : E1 × E2)).hasFDerivAt.comp u0 h1
  have e := (heq.hasFDerivAt_iff.mp hL).unique hR
  have := congrArg (fun f => f v) e
  simpa using this

end Partial

section Link

variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ} (G : GeneratingSet d L N₀ k ϱ) {a : ℕ → ℝ}
  (H : BgHyp d L k ϱ a 0) (Zf : Finset (Torus d (N₀ * L ^ (k - k))))

/-- **The complex variational function** `(ξ, q) ↦ A^C_k(𝔹; ψ̃, φ^C_k)` for the complex block field equal to `ξ` on
`Zf` and to `q` off `Zf`. -/
noncomputable def FC (z : (↥Zf × Fin N → ℂ) × BlockFieldC d L N₀ k N) : ℂ :=
  effC G H (mergeFieldC Zf z.2 z.1)

theorem FC_kP (p : BlockField d L N₀ k N) (u : SuppSpace Zf N) :
    FC G H Zf (kP (ofRealField (d := d) (L := L) (N₀ := N₀) (k := k) (N := N)) (u, p)) =
      effC G H (ofRealField (mergeField Zf p u)) := by
  simp only [FC, kP_apply]
  rw [mergeFieldC_real]

theorem FC_analyticAt {δ : ℝ} (hδ : 0 < δ) (hδ0 : δ ≤ bgC0 d L N) (hδ1 : δ ≤ bgC1 d L N)
    {p : BlockField d L N₀ k N} {u : SuppSpace Zf N} (ht : TubeOn G Set.univ δ (mergeField Zf p u)) :
    AnalyticAt ℂ (FC G H Zf) (kP (ofRealField (d := d) (L := L) (N₀ := N₀) (k := k) (N := N)) (u, p)) := by
  have h1 : AnalyticAt ℂ (effC G H) (mergeFieldC Zf (ofRealField p) (jEL u)) := by
    rw [mergeFieldC_real]
    exact effC_analyticAt G H hδ hδ0 hδ1 ht
  have h2 := analyticAt_mergeFieldC (N := N) Zf (jEL u, ofRealField p)
  exact AnalyticAt.comp (g := effC G H) (f := fun w : (↥Zf × Fin N → ℂ) × BlockFieldC d L N₀ k N =>
    mergeFieldC Zf w.2 w.1) h1 h2

theorem FC_eq {δ : ℝ} (hδ : 0 < δ) (hδ0 : δ ≤ bgC0 d L N) (hδ1 : δ ≤ bgC1 d L N)
    {p : BlockField d L N₀ k N} {u : SuppSpace Zf N} (ht : TubeOn G Set.univ δ (mergeField Zf p u)) :
    FC G H Zf (kP (ofRealField (d := d) (L := L) (N₀ := N₀) (k := k) (N := N)) (u, p)) =
      ((effOn G a Zf p u : ℝ) : ℂ) := by
  rw [FC_kP]
  exact effC_ofReal G H hδ hδ0 hδ1 ht

/-- Near a real tube point, `FC` is real and its real part is the variational function `effOn`. -/
theorem eventually_FC {δ : ℝ} (hδ : 0 < δ) (hδ0 : δ ≤ bgC0 d L N) (hδ1 : δ ≤ bgC1 d L N)
    {p0 : BlockField d L N₀ k N} {u0 : SuppSpace Zf N} (ht : TubeOn G Set.univ δ (mergeField Zf p0 u0)) :
    ∀ᶠ w in 𝓝 (u0, p0), TubeOn G Set.univ δ (mergeField Zf w.2 w.1) ∧
      Fre (ofRealField (d := d) (L := L) (N₀ := N₀) (k := k) (N := N)) (FC G H Zf) w =
        effOn G a Zf w.2 w.1 ∧
      (FC G H Zf (kP (ofRealField (d := d) (L := L) (N₀ := N₀) (k := k) (N := N)) w)).im = 0 := by
  have hev : ∀ᶠ w in 𝓝 (u0, p0), TubeOn G Set.univ δ (mergeField Zf w.2 w.1) :=
    (continuous_mergeField (N := N) Zf).continuousAt.eventually (eventually_tubeOn G ht)
  filter_upwards [hev] with w hw
  have e := FC_eq G H Zf hδ hδ0 hδ1 hw
  refine ⟨hw, ?_, ?_⟩
  · simp only [Fre, e, Complex.ofReal_re]
  · simp [e]

end Link

section IFT

variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ} (G : GeneratingSet d L N₀ k ϱ) {a : ℕ → ℝ}
  (H : BgHyp d L k ϱ a 0) (Zf : Finset (Torus d (N₀ * L ^ (k - k))))

/-- **Analytic continuation of the critical point of `effOn`**: at a real nondegenerate critical point `u₀` of
`effOn ψ_{k,0}` in the tube, the critical point of `effOn ψ_k` near `u₀` extends to a holomorphic function `ξ(q)` of the
complex block field `q` near `ψ_{k,0}`, and for real `q = ψ_k` it is `u₀ + x` with `x` real and small. -/
theorem analytic_zero_effOn (H : BgHyp d L k ϱ a 0) {δ : ℝ} (hδ : 0 < δ) (hδ0 : δ ≤ bgC0 d L N) (hδ1 : δ ≤ bgC1 d L N)
    {p0 : BlockField d L N₀ k N} {u0 : SuppSpace Zf N}
    (ht : TubeOn G Set.univ δ (mergeField Zf p0 u0)) {c : ℝ} (hc : 0 < c)
    (hcrit : fderiv ℝ (effOn G a Zf p0) u0 = 0)
    (hpos : ∀ v : SuppSpace Zf N, c * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ (effOn G a Zf p0)) u0 v v)
    {r0 : ℝ} (hr0 : 0 < r0) :
    ∃ ρ > 0, ∃ ξ : BlockFieldC d L N₀ k N → (↥Zf × Fin N → ℂ),
      AnalyticOnNhd ℂ ξ (ball (ofRealField p0) ρ) ∧ ξ (ofRealField p0) = 0 ∧
      ∀ p : BlockField d L N₀ k N, ‖p - p0‖ < ρ → ∃ x : SuppSpace Zf N,
        ξ (ofRealField p) = jEL x ∧ ‖x‖ ≤ r0 ∧ fderiv ℝ (effOn G a Zf p) (u0 + x) = 0 := by
  set jP : BlockField d L N₀ k N →L[ℝ] BlockFieldC d L N₀ k N := ofRealField with hjP
  have hev := eventually_FC G H Zf hδ hδ0 hδ1 ht
  obtain ⟨ε, hε, hεb⟩ := Metric.eventually_nhds_iff_ball.mp hev
  have hAn : AnalyticAt ℂ (FC G H Zf) (kP jP (u0, p0)) := FC_analyticAt G H Zf hδ hδ0 hδ1 ht
  have him : ∀ᶠ w in 𝓝 (u0, p0), (FC G H Zf (kP jP w)).im = 0 := hev.mono fun w hw => hw.2.2
  have hFE : Fre jP (FC G H Zf) =ᶠ[𝓝 (u0, p0)] fun w => effOn G a Zf w.2 w.1 := hev.mono fun w hw => hw.2.1
  -- the slice u ↦ (u, p0)
  have hslice : Continuous (fun u : SuppSpace Zf N => ((u, p0) : SuppSpace Zf N × BlockField d L N₀ k N)) :=
    continuous_id.prodMk continuous_const
  have hg : (fun u => Fre jP (FC G H Zf) (u, p0)) =ᶠ[𝓝 u0] effOn G a Zf p0 :=
    hslice.continuousAt.eventually hFE
  have hcrit' : ∀ v : SuppSpace Zf N, fderiv ℝ (Fre jP (FC G H Zf)) (u0, p0) (v, 0) = 0 := by
    intro v
    rw [← fderiv_partial ((contDiffAt_Fre jP hAn 1).differentiableAt (by norm_num)) v,
      hg.fderiv_eq, hcrit]
    rfl
  have hpos' : ∀ v : SuppSpace Zf N,
      c * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ (Fre jP (FC G H Zf))) (u0, p0) (v, 0) (v, 0) := by
    intro v
    rw [← fderiv2_partial (contDiffAt_Fre jP hAn 2) v, hg.fderiv.fderiv_eq]
    exact hpos v
  obtain ⟨ρ0, hρ0, r, hr, ξ, hξA, hξ0, -, hξR⟩ := analytic_zero_of_real_critical jP hAn him
    (norm_ofRealField) hcrit' hc hpos' (r0 := min r0 (ε / 2)) (lt_min hr0 (by positivity))
  refine ⟨min ρ0 (ε / 2), lt_min hρ0 (by positivity), ξ, hξA.mono (ball_subset_ball (min_le_left _ _)),
    hξ0, fun p hp => ?_⟩
  obtain ⟨x, hx, hxr, hxc⟩ := hξR p (lt_of_lt_of_le hp (min_le_left _ _))
  refine ⟨x, hx, hxr.trans (min_le_left _ _), ?_⟩
  have hw' : (u0 + x, p) ∈ ball (u0, p0) ε := by
    rw [mem_ball, Prod.dist_eq, max_lt_iff]
    refine ⟨?_, ?_⟩
    · rw [dist_eq_norm]; simp only [add_sub_cancel_left]
      exact lt_of_le_of_lt (hxr.trans (min_le_right _ _)) (by linarith)
    · rw [dist_eq_norm]; exact lt_of_lt_of_le hp ((min_le_right _ _).trans (by linarith))
  obtain ⟨hwT, hwE, -⟩ := hεb _ hw'
  have hAn' : AnalyticAt ℂ (FC G H Zf) (kP jP (u0 + x, p)) := FC_analyticAt G H Zf hδ hδ0 hδ1 hwT
  have hnb : ball (u0, p0) ε ∈ 𝓝 (u0 + x, p) := isOpen_ball.mem_nhds hw'
  have hFE' : Fre jP (FC G H Zf) =ᶠ[𝓝 (u0 + x, p)] fun w => effOn G a Zf w.2 w.1 :=
    Filter.eventually_of_mem hnb fun w hw => (hεb w hw).2.1
  have hslice' : Continuous (fun u : SuppSpace Zf N => ((u, p) : SuppSpace Zf N × BlockField d L N₀ k N)) :=
    continuous_id.prodMk continuous_const
  have hg' : (fun u => Fre jP (FC G H Zf) (u, p)) =ᶠ[𝓝 (u0 + x)] effOn G a Zf p :=
    hslice'.continuousAt.eventually hFE'
  ext v
  rw [← hg'.fderiv_eq, fderiv_partial ((contDiffAt_Fre jP hAn' 1).differentiableAt (by norm_num)) v]
  exact hxc v

end IFT

section Main

variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ} (G : GeneratingSet d L N₀ k ϱ) (a : ℕ → ℝ)
  [NeZero N]

/-- **Lemma III.3.3, analyticity of `ψ⁰_k` in `ψ_k` (from the cited expansion estimate `PsiZeroInput`).**  With the
constants `K₆ = K`, `c₁₁` of `psiZero_exists_unique_of_input`: for `δ ≤ c₁₁` and a real `ψ_{k,0} ∈ Ψ̃(X ∖ Z₀; δ)` there
is a holomorphic map `S` of the complex block field `q`, defined on a complex ball about `ψ_{k,0}`, equal to `q` off
`Z₀`, whose restriction to the real block fields `ψ_k ∈ Ψ̃(X ∖ Z₀; δ)` near `ψ_{k,0}` is the solution of (2.34):
`S(ψ_k) = ψ⁰_k(ψ_k)`.  That is, `ψ_k ↦ ψ⁰_k` is analytic (extends holomorphically to a complex neighbourhood of every
real point).  The statement that the extension maps the complex tube into the complex tube is not proved (it needs a
quantitative radius for the complex contraction). -/
theorem psiZero_analytic_of_input {D : ℕ} (hd : 2 ≤ d) (hk : 1 ≤ k) (b0 : Torus d (N₀ * L ^ (k - k)))
    (w : Fin d → ℕ) (hw1 : ∀ i, 1 ≤ w i) (hwD : ∀ i, w i ≤ D) (hm : D + 2 ≤ N₀ * L ^ (k - k))
    {X : Set (Torus d (N₀ * L ^ (k - k)))} (hXreg : box b0 w ∪ shellOut (box b0 w) ⊆ X)
    (hΩ : OverTop G (box b0 w ∪ shellOut (box b0 w)))
    (hdata : ∀ x ∈ dataSites G, jBlock d L N₀ k k x ∈ X) (H : BgHyp d L k ϱ a 0)
    (inp : PsiZeroInput (N := N) G a b0 w X) :
    ∃ K c11 : ℝ, 0 < K ∧ 0 < c11 ∧ ∀ δ : ℝ, 0 < δ → δ ≤ c11 → ∀ ψk0 : BlockField d L N₀ k N,
      TubeOn G (X \ box b0 w) δ ψk0 →
      ∃ ρ > 0, ∃ S : BlockFieldC d L N₀ k N → BlockFieldC d L N₀ k N,
        AnalyticOnNhd ℂ S (ball (ofRealField ψk0) ρ) ∧
        (∀ q z, z ∉ box b0 w → S q z = q z) ∧
        ∀ ψk : BlockField d L N₀ k N, ‖ψk - ψk0‖ < ρ → TubeOn G (X \ box b0 w) δ ψk →
          ∀ ψ : BlockField d L N₀ k N, PsiZeroSol G a b0 w X (K * δ) ψk ψ →
            S (ofRealField ψk) = ofRealField ψ := by
  obtain ⟨K, c11, hK, hc11, hloc⟩ := psiZero_local_of_input G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H inp
  set Zf := boxFinset (L := L) (N₀ := N₀) (k := k) b0 w with hZf
  refine ⟨K, c11, hK, hc11, fun δ hδ hδc ψk0 hψk0 => ?_⟩
  obtain ⟨r, τ, hr, hτ, hτ0, hτ1, hTube, hFsm, hHess, x0, hx0B, hx0crit, hsol0, -, -, -⟩ :=
    hloc δ hδ hδc ψk0 hψk0
  have ht0 : TubeOn G Set.univ τ (mergeField Zf ψk0 x0) := hTube x0 hx0B
  -- the solution lies in the open tube `Ψ̃(X; K δ)`, hence so do nearby merges
  have hevX : ∀ᶠ w' in 𝓝 (x0, ψk0), TubeOn G X (K * δ) (mergeField Zf w'.2 w'.1) :=
    (continuous_mergeField (N := N) Zf).continuousAt.eventually (eventually_tubeOn G hsol0.1)
  obtain ⟨ε1, hε1, hε1b⟩ := Metric.eventually_nhds_iff_ball.mp hevX
  obtain ⟨ρ0, hρ0, ξ, hξA, hξ0, hξR⟩ := analytic_zero_effOn G Zf H hτ hτ0 hτ1 ht0 inp.c_pos hx0crit
    (fun v => hHess x0 hx0B v) (r0 := ε1 / 2) (by positivity)
  refine ⟨min ρ0 (ε1 / 2), lt_min hρ0 (by positivity),
    fun q => mergeFieldC Zf q (jEL x0 + ξ q), ?_, ?_, ?_⟩
  · intro q hq
    have hq' : q ∈ ball (ofRealField ψk0) ρ0 := ball_subset_ball (min_le_left _ _) hq
    have h1 : AnalyticAt ℂ ξ q := hξA q hq'
    have h2 : AnalyticAt ℂ (fun q => (jEL x0 + ξ q, q)) q :=
      AnalyticAt.prod (analyticAt_const.fun_add h1) analyticAt_id
    exact AnalyticAt.comp (g := fun w : (↥Zf × Fin N → ℂ) × BlockFieldC d L N₀ k N => mergeFieldC Zf w.2 w.1)
      (f := fun q => (jEL x0 + ξ q, q)) (analyticAt_mergeFieldC Zf _) h2
  · intro q z hz
    have : z ∉ Zf := fun h => hz (mem_boxFinset.1 h)
    funext i
    simp [mergeFieldC, this]
  · intro ψk hψk hψkT ψ hψ
    obtain ⟨x, hx, hxr, hxc⟩ := hξR ψk (lt_of_lt_of_le hψk (min_le_left _ _))
    -- the merge of the real critical point
    have hmem : (x0 + x, ψk) ∈ ball (x0, ψk0) ε1 := by
      rw [mem_ball, Prod.dist_eq, max_lt_iff]
      refine ⟨?_, ?_⟩
      · rw [dist_eq_norm]; simp only [add_sub_cancel_left]; linarith
      · rw [dist_eq_norm]; exact lt_of_lt_of_le hψk ((min_le_right _ _).trans (by linarith))
    have hyT := hε1b (x0 + x, ψk) hmem
    simp only at hyT
    have hyag : ∀ z, z ∉ box b0 w → mergeField Zf ψk (x0 + x) z = ψk z := fun z hz =>
      mergeField_of_not_mem (fun h => hz (mem_boxFinset.1 h))
    obtain ⟨r', τ', hr', hτ', -, -, -, -, -, x', hx'B, -, hsol', hclose', huniq', hsolu'⟩ :=
      hloc δ hδ hδc ψk hψkT
    have hres : restrictSupp Zf (mergeField Zf ψk (x0 + x)) = x0 + x := restrict_mergeField ψk (x0 + x)
    have hball := hclose' _ hyT hyag
    rw [hres] at hball
    have hxx : x0 + x = x' := huniq' _ hball hxc
    have hψeq : ψ = mergeField Zf ψk x' := hsolu' ψ hψ
    show mergeFieldC Zf (ofRealField ψk) (jEL x0 + ξ (ofRealField ψk)) = ofRealField ψ
    rw [hx, ← map_add, mergeFieldC_real, hψeq, ← hxx]

end Main

end Balaban.LargeField
