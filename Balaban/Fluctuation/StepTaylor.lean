/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.StepRegClass
public import Balaban.Background.Def5Response
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.Taylor

/-!
# The lower background along the ray: derivative at the critical point (HAT-RATE §2, (2.1))

Along the ray `ψ_s = ψ^{(k)} + s ψ'(ψ̂)` the datum `dataU ψ_s` is affine in `s`, the tangent
`compTangent (dataU ψ_s)` equals `s • rayTangent ψ̂`, and (Proposition 5.4,
`theorem72_linearResponse` at the base datum) the lower background has derivative
`phiOne (qStar (rayTangent ψ̂))` at `s = 0`.  The base-domain witness of radius `bgC2` is an explicit
premise (HAT-RATE §2); the critical-point identification of the lower field and multiplier with the
restrictions of the upper ones is derived from the `RayData`-style premises as in `Vk_psi0`.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban.SmallField.Def6 Balaban.Background Balaban.Multiscale Balaban.Localization
  Balaban.SmallField Finset MeasureTheory Set Matrix Filter Topology Asymptotics

/-! ### Scalar calculus: second-order vanishing -/

open Filter Topology Asymptotics Set

/-- A quadratic polynomial that is `o(x²)` at `0` has zero coefficients. -/
theorem coeffs_eq_zero_of_isLittleO_sq {c₀ c₁ c₂ : ℂ}
    (h : (fun x : ℝ => c₀ + c₁ * x + c₂ * x ^ 2) =o[𝓝 0] fun x : ℝ => x ^ 2) :
    c₀ = 0 ∧ c₁ = 0 ∧ c₂ = 0 := by
  have hfr : ∃ᶠ x in 𝓝 (0 : ℝ), x ≠ 0 :=
    ((eventually_mem_nhdsWithin : ∀ᶠ x in 𝓝[≠] (0 : ℝ), x ∈ ({0}ᶜ : Set ℝ)).frequently).filter_mono
      nhdsWithin_le_nhds
  have hc₀ : c₀ = 0 := by
    have := (h.def (show (0 : ℝ) < 1 by norm_num)).self_of_nhds
    simpa using this
  subst hc₀
  have h' : (fun x : ℝ => c₁ * x + c₂ * x ^ 2) =o[𝓝 0] fun x : ℝ => x ^ 2 := by simpa using h
  have hx2 : (fun x : ℝ => c₂ * (x : ℂ) ^ 2) =O[𝓝 0] fun x : ℝ => x ^ 2 := by
    refine IsBigO.of_bound ‖c₂‖ (Eventually.of_forall fun x => ?_)
    simp
  have hlin : (fun x : ℝ => c₁ * (x : ℂ)) =O[𝓝 0] fun x : ℝ => x ^ 2 := by
    have := h'.isBigO.sub hx2
    simpa using this
  have hlin' : (fun x : ℝ => c₁ * (x : ℂ)) =o[𝓝 0] fun x : ℝ => x :=
    hlin.trans_isLittleO (isLittleO_pow_id (by norm_num))
  have hc₁ : c₁ = 0 := by
    by_contra hne
    have h2 := (isLittleO_const_mul_left_iff hne).1 hlin'
    obtain ⟨x, hx1, hx2⟩ := ((h2.def (show (0 : ℝ) < 1 / 2 by norm_num)).and_frequently hfr).exists
    have : 0 < ‖(x : ℂ)‖ := by simpa using hx2
    simp only [Complex.norm_real, Real.norm_eq_abs] at hx1 this
    linarith
  subst hc₁
  have hc₂ : c₂ = 0 := by
    by_contra hne
    have h2 := (isLittleO_const_mul_left_iff hne).1 (by simpa using h' :
      (fun x : ℝ => c₂ * (x : ℂ) ^ 2) =o[𝓝 0] fun x : ℝ => x ^ 2)
    obtain ⟨x, hx1, hx2⟩ := ((h2.def (show (0 : ℝ) < 1 / 2 by norm_num)).and_frequently hfr).exists
    have hpos : 0 < x ^ 2 := lt_of_le_of_ne (sq_nonneg x) (Ne.symm (pow_ne_zero 2 hx2))
    simp only [norm_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs] at hx1
    linarith
  exact ⟨rfl, rfl, hc₂⟩

theorem isLittleO_sum_fn {ι : Type*} (A : Finset ι) {f : ι → ℝ → ℂ} {g : ℝ → ℝ}
    (h : ∀ i ∈ A, f i =o[𝓝 0] g) : (fun x => ∑ i ∈ A, f i x) =o[𝓝 0] g := by
  have := IsLittleO.sum h
  simpa [Finset.sum_fn] using this

theorem isBigO_sum_fn {ι : Type*} (A : Finset ι) {f : ι → ℝ → ℂ} {g : ℝ → ℝ}
    (h : ∀ i ∈ A, f i =O[𝓝 0] g) : (fun x => ∑ i ∈ A, f i x) =O[𝓝 0] g := by
  have := IsBigO.sum h
  simpa [Finset.sum_fn] using this

/-- A `C²` function that is `o(x²)` at `0` vanishes to second order. -/
theorem derivs_zero_of_isLittleO_sq {f : ℝ → ℂ} (hf : ContDiffAt ℝ 2 f 0)
    (h : f =o[𝓝 0] fun x : ℝ => x ^ 2) :
    f 0 = 0 ∧ deriv f 0 = 0 ∧ deriv (deriv f) 0 = 0 := by
  obtain ⟨u, hu, hfu⟩ := hf.contDiffOn (m := 2) le_rfl (by simp)
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.1 hu
  have hT := taylor_isLittleO (n := 2) (convex_ball (0 : ℝ) r) (Metric.mem_ball_self hr)
    (by simpa using hfu.mono hball)
  rw [nhdsWithin_eq_nhds.2 (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hr))] at hT
  have hpoly : ∀ x : ℝ, taylorWithinEval f 2 (Metric.ball (0 : ℝ) r) 0 x =
      f 0 + deriv f 0 * x + (deriv (deriv f) 0 / 2) * x ^ 2 := by
    intro x
    rw [taylor_within_apply]
    simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty]
    rw [iteratedDerivWithin_of_isOpen Metric.isOpen_ball (Metric.mem_ball_self hr),
      iteratedDerivWithin_of_isOpen Metric.isOpen_ball (Metric.mem_ball_self hr),
      iteratedDerivWithin_of_isOpen Metric.isOpen_ball (Metric.mem_ball_self hr)]
    simp [iteratedDeriv_succ, Complex.real_smul]
    ring
  have hP : (fun x : ℝ => f 0 + deriv f 0 * x + (deriv (deriv f) 0 / 2) * x ^ 2) =o[𝓝 0]
      fun x : ℝ => x ^ 2 := by
    simp only [sub_zero] at hT
    refine (h.sub hT).congr_left (fun x => ?_)
    simp only [hpoly]
    ring
  obtain ⟨h0, h1, h2⟩ := coeffs_eq_zero_of_isLittleO_sq hP
  exact ⟨h0, h1, by simpa using h2⟩



namespace StepSetting

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}
  (S : StepSetting d L N₁ m₁ k N ϱ)

/-- The tangent `ψ'` of the ray (the lift of `shiftU x`) as a complex field. -/
noncomputable def rayTangent (x : S.E) : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ :=
  fun z i => ((liftU S.hG' (S.shiftU x) z i : ℝ) : ℂ)

/-- The tangent datum `(lift of shiftU x, 0)` of the ray, a datum of `𝔹_k`. -/
noncomputable def rayDatum (x : S.E) : BgData (stepG d L N₁ m₁ k ϱ) N :=
  realData (stepG d L N₁ m₁ k ϱ) (liftU S.hG' (S.shiftU x)) 0
    (isLayerConstant_liftU S.hG S.hG' (S.shiftU x))

theorem rayDatum_Ψ (x : S.E) : (S.rayDatum x).Ψ = S.rayTangent x := by
  funext z i
  exact (realData_realizes (G := stepG d L N₁ m₁ k ϱ) (h₀ := (0 : Fin N → ℝ))
    (isLayerConstant_liftU S.hG S.hG' (S.shiftU x))).1 z (S.dataSites_stepG z) i

theorem rayDatum_h (x : S.E) : (S.rayDatum x).h = fun _ _ => 0 := by
  funext z i
  have := (realData_realizes (G := stepG d L N₁ m₁ k ϱ) (h₀ := (0 : Fin N → ℝ))
    (isLayerConstant_liftU S.hG S.hG' (S.shiftU x))).2 z (S.hG z).1 i
  unfold rayDatum
  simpa using this

/-- **The datum is affine along the ray**: `dataU ψ_s = dataU ψ_0 + s • rayDatum`. -/
theorem dataU_psiAt_eq_lineAt (s : ℝ) (x : S.E) :
    S.dataU (S.psiAt s x) = (S.dataU S.psi0).lineAt (S.rayDatum x) (s : ℂ) := by
  refine bgData_ext' ?_ ?_
  · funext z i
    show _ = (S.dataU S.psi0).Ψ z i + (s : ℂ) * (S.rayDatum x).Ψ z i
    rw [S.dataU_Ψ, S.dataU_Ψ, S.rayDatum_Ψ]
    unfold rayTangent psiAt liftU
    simp
  · funext z i
    show _ = (S.dataU S.psi0).h z i + (s : ℂ) * (S.rayDatum x).h z i
    rw [S.dataU_h, S.dataU_h, S.rayDatum_h]
    simp

include S in
theorem boundaryTerm_stepG (Ψ : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ)
    (p : (stepG d L N₁ m₁ k ϱ).Ω 1 × Fin N) :
    boundaryTerm (stepG d L N₁ m₁ k ϱ) Ψ p = 0 := by
  unfold boundaryTerm
  refine Finset.sum_eq_zero fun μ _ => ?_
  have h : ∀ y, y ∉ collar (stepG d L N₁ m₁ k ϱ) := fun y hy =>
    ((mem_collar _).1 hy).1 (S.hG y).1
  simp [h]

theorem source_rayDatum (x : S.E) :
    source (stepG d L N₁ m₁ k ϱ) S.a S.ν (S.rayDatum x) =
      qStar (stepG d L N₁ m₁ k ϱ) S.a (S.rayTangent x) := by
  funext p
  unfold source
  rw [S.boundaryTerm_stepG, S.rayDatum_h, S.rayDatum_Ψ]
  simp

section Crit

variable (ha₁ : 0 < S.a₁) (H : BgHyp d L (k + 1) ϱ S.a S.ν)
  {δ' : ℝ} (hδ'0 : 0 < δ') (hδ' : δ' ≤ thm73C3 d L N / 2) (hD'R : InDomainR S.G' S.ν δ' S.D')

include S ha₁ H hδ'0 hδ' hD'R in
/-- **The critical-point identification** (as in `Vk_psi0`): the lower background field and
multiplier at the critical datum `ψ^{(k)}` are the restrictions of the upper ones. -/
theorem lower_bg_psi0 :
    bgFieldC (stepG d L N₁ m₁ k ϱ) S.a S.ν (bgC0 d L N) (S.dataU S.psi0) =
        (S.hG.precedes S.hG' (le_refl (k + 1))).restrictφ
          (bgFieldC S.G' S.a S.ν (bgC0 d L N) S.D') ∧
      bgMultC (stepG d L N₁ m₁ k ϱ) S.a S.ν (bgC0 d L N) (S.dataU S.psi0) =
        (S.hG.precedes S.hG' (le_refl (k + 1))).restrictα
          (bgMultC S.G' S.a S.ν (bgC0 d L N) S.D') := by
  have hd0 : 0 < d := by have := H.hd; omega
  obtain ⟨hDU', -⟩ := S.D'_domains H hδ'0 hδ' hD'R
  obtain ⟨hr, hdom, -, -, -, -, hfield, hmult⟩ :=
    criticalPoint_real ha₁ S.hG S.hG' (le_refl (k + 1)) H H S.D' hDU'
  obtain ⟨-, -, hδ'c1, -⟩ := theta_consts hd0 hδ'0 hδ'
  have hDU1 : InUnionDomainR S.G' (bgC1 d L N) S.ν S.D' := ⟨δ', hδ'0, hδ'c1, hD'R⟩
  obtain ⟨hf, hm⟩ := theorem72_real H hDU1
  have hdp := S.dataU_psi0 ha₁ H hδ'0 hδ' hD'R
  have hdom' : InUnionDomainR (stepG d L N₁ m₁ k ϱ) (bgC1 d L N) S.ν S.psiKd := hdom
  have hfield' : bgField (stepG d L N₁ m₁ k ϱ) S.a S.ν S.psiKd =
      (S.hG.precedes S.hG' (le_refl (k + 1))).restrictφ (bgField S.G' S.a S.ν S.D') := hfield
  have hmult' : bgMult (stepG d L N₁ m₁ k ϱ) S.a S.ν S.psiKd =
      (S.hG.precedes S.hG' (le_refl (k + 1))).restrictα (bgMult S.G' S.a S.ν S.D') := hmult
  obtain ⟨hf2, hm2⟩ := theorem72_real H hdom'
  rw [hdp]
  exact ⟨by rw [hf2, hfield', hf], by rw [hm2, hmult', hm]⟩

include S ha₁ H hδ'0 hδ' hD'R in
/-- **The tangent is affine along the ray**: `compTangent (dataU ψ_s) = s • rayTangent ψ̂`
(HAT-RATE §2, `S_s = s S'_0`). -/
theorem compTangent_ray (s : ℝ) (x : S.E) :
    compTangent S.hG S.hG' (le_refl (k + 1)) S.a
      (bgFieldC S.G' S.a S.ν (bgC0 d L N) S.D') S.D' (S.dataU (S.psiAt s x)) =
      (s : ℂ) • S.rayTangent x := by
  have hd0 : 0 < d := by have := H.hd; omega
  obtain ⟨hDU', -⟩ := S.D'_domains H hδ'0 hδ' hD'R
  obtain ⟨-, -, hδ'c1, -⟩ := theta_consts hd0 hδ'0 hδ'
  have hDU1 : InUnionDomainR S.G' (bgC1 d L N) S.ν S.D' := ⟨δ', hδ'0, hδ'c1, hD'R⟩
  obtain ⟨hf, -⟩ := theorem72_real H hDU1
  have hdp := S.dataU_psi0 ha₁ H hδ'0 hδ' hD'R
  funext z i
  unfold compTangent
  rw [hf, S.dataU_Ψ]
  have hc : (composeData (S.hG.precedes S.hG' (le_refl (k + 1))) S.a
      (bgField S.G' S.a S.ν S.D') S.D').Ψ z i = ((liftU S.hG' S.psi0 z i : ℝ) : ℂ) :=
    (congrArg (fun D => D.Ψ z i) hdp).symm.trans (S.dataU_Ψ S.psi0 z i)
  show ((liftU S.hG' (S.psiAt s x) z i : ℝ) : ℂ) - _ = _
  rw [hc]
  unfold rayTangent psiAt liftU
  simp

include S ha₁ H hδ'0 hδ' hD'R in
/-- The affine identity gives the derivative `S'_0` of `compTangent (dataU ψ_s)` at `s = 0`. -/
theorem hasDerivAt_compTangent_ray (x : S.E) :
    HasDerivAt (fun s : ℝ => compTangent S.hG S.hG' (le_refl (k + 1)) S.a
      (bgFieldC S.G' S.a S.ν (bgC0 d L N) S.D') S.D' (S.dataU (S.psiAt s x)))
      (S.rayTangent x) 0 := by
  have : (fun s : ℝ => compTangent S.hG S.hG' (le_refl (k + 1)) S.a
      (bgFieldC S.G' S.a S.ν (bgC0 d L N) S.D') S.D' (S.dataU (S.psiAt s x))) =
      fun s : ℝ => (s : ℂ) • S.rayTangent x :=
    funext fun s => S.compTangent_ray ha₁ H hδ'0 hδ' hD'R s x
  rw [this]
  simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (S.rayTangent x)).congr_deriv (by simp)

include S ha₁ H hδ'0 hδ' hD'R in
/-- **HAT-RATE §2 (2.1).**  Along the ray the lower background, minus the restriction of the upper
one, is differentiable at `s = 0` with derivative `phiOne h a ν α₀ φ₀ (qStar S'₀)`
(Proposition 5.4, `theorem72_linearResponse`, at the base datum).  The base-domain witness `hbase`
(radius `bgC2`) is the explicit premise of HAT-RATE §2; the critical-point identification is derived
(`lower_bg_psi0`). -/
theorem hasDerivAt_bg_ray_eq_phiOne
    (hbase : InUnionDomainC (stepG d L N₁ m₁ k ϱ) (bgC0 d L N) (bgC2 d L N) S.ν
      (S.dataU S.psi0)) (x : S.E) :
    HasDerivAt (fun s : ℝ =>
      bgFieldC (stepG d L N₁ m₁ k ϱ) S.a S.ν (bgC0 d L N) (S.dataU (S.psiAt s x)) -
        (S.hG.precedes S.hG' (le_refl (k + 1))).restrictφ
          (bgFieldC S.G' S.a S.ν (bgC0 d L N) S.D'))
      (phiOne (S.hG.precedes S.hG' (le_refl (k + 1))) S.a S.ν
        (bgMultC S.G' S.a S.ν (bgC0 d L N) S.D') (bgFieldC S.G' S.a S.ν (bgC0 d L N) S.D')
        (qStar (stepG d L N₁ m₁ k ϱ) S.a (S.rayTangent x))) 0 := by
  obtain ⟨hF, hM⟩ := S.lower_bg_psi0 ha₁ H hδ'0 hδ' hD'R
  obtain ⟨φd, αd, h1, -, -, h4, -⟩ := theorem72_linearResponse H hbase (S.rayDatum x)
  have hh : HasDerivAt (fun r : ℝ => (r : ℂ)) (1 : ℂ) (0 : ℝ) := by
    exact (Complex.ofRealCLM.hasDerivAt (x := (0 : ℝ))).congr_deriv (by simp)
  have h1' : HasDerivAt (fun t : ℂ => bgFieldC (stepG d L N₁ m₁ k ϱ) S.a S.ν (bgC0 d L N)
      ((S.dataU S.psi0).lineAt (S.rayDatum x) t)) φd (((0 : ℝ) : ℂ)) := by
    rwa [Complex.ofReal_zero]
  have h2 := h1'.scomp (0 : ℝ) hh
  have h3 : HasDerivAt (fun s : ℝ =>
      bgFieldC (stepG d L N₁ m₁ k ϱ) S.a S.ν (bgC0 d L N) (S.dataU (S.psiAt s x))) φd 0 := by
    have e : (fun s : ℝ =>
      bgFieldC (stepG d L N₁ m₁ k ϱ) S.a S.ν (bgC0 d L N) (S.dataU (S.psiAt s x))) =
        (fun t : ℂ => bgFieldC (stepG d L N₁ m₁ k ϱ) S.a S.ν (bgC0 d L N)
          ((S.dataU S.psi0).lineAt (S.rayDatum x) t)) ∘ (fun r : ℝ => (r : ℂ)) :=
      funext fun s => by simp [S.dataU_psiAt_eq_lineAt]
    rw [e]
    simpa using h2
  convert h3.sub_const _ using 1
  rw [h4, S.source_rayDatum]
  unfold phiOne opHk fieldBase bgOp bgVec
  rw [hM]
  congr 3
  funext x i
  exact (congrFun hF _).symm

end Crit

/-! ### The expansion (2.2) of the interaction along the ray -/

end StepSetting

theorem alphaOne_smul {d L N₀ K N : ℕ} {ϱ ϱ' : ℝ} [NeZero N₀] [NeZero L]
    {G : GeneratingSet d L N₀ K ϱ} {G' : GeneratingSet d L N₀ K ϱ'}
    (h : Precedes G G') (a : ℕ → ℝ) (ν : ℝ) (α₁ : G'.Ω 1 → ℂ) (φ₁ : G'.Ω 1 × Fin N → ℂ)
    (c : ℂ) (S : G.Ω 1 × Fin N → ℂ) :
    alphaOne h a ν α₁ φ₁ (c • S) = c • alphaOne h a ν α₁ φ₁ S := by
  simp only [alphaOne, Matrix.mulVec_smul]

theorem phiOne_smul {d L N₀ K N : ℕ} {ϱ ϱ' : ℝ} [NeZero N₀] [NeZero L]
    {G : GeneratingSet d L N₀ K ϱ} {G' : GeneratingSet d L N₀ K ϱ'}
    (h : Precedes G G') (a : ℕ → ℝ) (ν : ℝ) (α₁ : G'.Ω 1 → ℂ) (φ₁ : G'.Ω 1 × Fin N → ℂ)
    (c : ℂ) (S : G.Ω 1 × Fin N → ℂ) :
    phiOne h a ν α₁ φ₁ (c • S) = c • phiOne h a ν α₁ φ₁ S := by
  simp only [phiOne, Matrix.mulVec_smul]

namespace StepSetting

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}
  (S : StepSetting d L N₁ m₁ k N ϱ)

/-- `P_s = φ(ψ_s) - φ₀|_{Ω₁}` of HAT-RATE §2 (the lower background minus the restricted upper
one), as a function of the ray parameter. -/
noncomputable def rayDiff (x : S.E) (s : ℝ) : (stepG d L N₁ m₁ k ϱ).Ω 1 × Fin N → ℂ :=
  bgFieldC (stepG d L N₁ m₁ k ϱ) S.a S.ν (bgC0 d L N) (S.dataU (S.psiAt s x)) -
    (S.hG.precedes S.hG' (le_refl (k + 1))).restrictφ
      (bgFieldC S.G' S.a S.ν (bgC0 d L N) S.D')

/-- `A_1 = alphaOne (qStar S'_0)` of HAT-RATE §2. -/
noncomputable def rayA1 (x : S.E) : (stepG d L N₁ m₁ k ϱ).Ω 1 → ℂ :=
  alphaOne (S.hG.precedes S.hG' (le_refl (k + 1))) S.a S.ν
    (bgMultC S.G' S.a S.ν (bgC0 d L N) S.D') (bgFieldC S.G' S.a S.ν (bgC0 d L N) S.D')
    (qStar (stepG d L N₁ m₁ k ϱ) S.a (S.rayTangent x))

/-- `P_1 = phiOne (qStar S'_0)` of HAT-RATE §2. -/
noncomputable def rayP1 (x : S.E) : (stepG d L N₁ m₁ k ϱ).Ω 1 × Fin N → ℂ :=
  phiOne (S.hG.precedes S.hG' (le_refl (k + 1))) S.a S.ν
    (bgMultC S.G' S.a S.ν (bgC0 d L N) S.D') (bgFieldC S.G' S.a S.ν (bgC0 d L N) S.D')
    (qStar (stepG d L N₁ m₁ k ϱ) S.a (S.rayTangent x))

/-- The Hessian operator `H_k` of the potential. -/
noncomputable def rayHk : Matrix ((stepG d L N₁ m₁ k ϱ).Ω 1 × Fin N)
    ((stepG d L N₁ m₁ k ϱ).Ω 1 × Fin N) ℂ :=
  liftOp N (opHk (S.hG.precedes S.hG' (le_refl (k + 1))) S.a S.ν
    (bgMultC S.G' S.a S.ν (bgC0 d L N) S.D'))

section Expand

variable (ha₁ : 0 < S.a₁) (H : BgHyp d L (k + 1) ϱ S.a S.ν)
  {δ' : ℝ} (hδ'0 : 0 < δ') (hδ' : δ' ≤ thm73C3 d L N / 2) (hD'R : InDomainR S.G' S.ν δ' S.D')

include S ha₁ H hδ'0 hδ' hD'R in
/-- **HAT-RATE §2 (2.2).**  Exactly, for every `s`,
`V(s) = (s/2) ∑_z A₁(z) P_s(z)·P_s(z) + ½ ⟨R_s, H_k R_s⟩`, `R_s = P_s - s P_1`. -/
theorem Vk_ray_eq (s : ℝ) (x : S.E) :
    S.Vk (S.psiAt s x) =
      (1 / 2) * ∑ z, ((s : ℂ) * S.rayA1 x z) * ∑ i, S.rayDiff x s (z, i) * S.rayDiff x s (z, i) +
        (1 / 2) * pair (stepG d L N₁ m₁ k ϱ) (S.rayDiff x s - (s : ℂ) • S.rayP1 x)
          (S.rayHk *ᵥ (S.rayDiff x s - (s : ℂ) • S.rayP1 x)) := by
  unfold Vk interactionV
  rw [S.compTangent_ray ha₁ H hδ'0 hδ' hD'R]
  have h1 : qStar (stepG d L N₁ m₁ k ϱ) S.a ((s : ℂ) • S.rayTangent x) =
      (s : ℂ) • qStar (stepG d L N₁ m₁ k ϱ) S.a (S.rayTangent x) := by
    funext p
    simp only [qStar, Pi.smul_apply, smul_eq_mul, rayTangent]
    ring
  rw [h1]
  simp only [alphaOne_smul, phiOne_smul]
  rfl

end Expand

section Order

variable (ha₁ : 0 < S.a₁) (H : BgHyp d L (k + 1) ϱ S.a S.ν)
  {δ' : ℝ} (hδ'0 : 0 < δ') (hδ' : δ' ≤ thm73C3 d L N / 2) (hD'R : InDomainR S.G' S.ν δ' S.D')

include S ha₁ H hδ'0 hδ' hD'R in
theorem rayDiff_zero (x : S.E) : S.rayDiff x 0 = 0 := by
  obtain ⟨hF, -⟩ := S.lower_bg_psi0 ha₁ H hδ'0 hδ' hD'R
  unfold rayDiff psiAt
  simp only [zero_smul, add_zero]
  rw [hF]
  exact sub_self _

include S ha₁ H hδ'0 hδ' hD'R in
/-- **HAT-RATE §2 (2.2)-(2.4).**  The interaction along the ray is `o(s²)` at `s = 0`
(under the base-domain witness of `theorem72_linearResponse`): `P_s = O(s)`, `R_s = o(s)`. -/
theorem isLittleO_Vk_ray_of_baseDomain
    (hbase : InUnionDomainC (stepG d L N₁ m₁ k ϱ) (bgC0 d L N) (bgC2 d L N) S.ν
      (S.dataU S.psi0)) (x : S.E) :
    (fun s : ℝ => S.Vk (S.psiAt s x)) =o[𝓝 0] fun s : ℝ => s ^ 2 := by
  have hD := S.hasDerivAt_bg_ray_eq_phiOne ha₁ H hδ'0 hδ' hD'R hbase x
  have hP : ∀ p, HasDerivAt (fun s : ℝ => S.rayDiff x s p) (S.rayP1 x p) 0 := fun p =>
    hasDerivAt_pi.1 hD p
  have h0 := S.rayDiff_zero ha₁ H hδ'0 hδ' hD'R x
  have hbig : ∀ p, (fun s : ℝ => S.rayDiff x s p) =O[𝓝 0] fun s : ℝ => s := by
    intro p
    have := (hP p).hasFDerivAt.isBigO_sub
    simpa [h0] using this
  have hlit : ∀ p, (fun s : ℝ => S.rayDiff x s p - (s : ℂ) * S.rayP1 x p) =o[𝓝 0]
      fun s : ℝ => s := by
    intro p
    have := (hasDerivAt_iff_isLittleO.1 (hP p))
    simpa [h0, Complex.real_smul] using this
  have hs : (fun s : ℝ => (s : ℂ)) =O[𝓝 0] fun s : ℝ => s :=
    IsBigO.of_bound 1 (Eventually.of_forall fun s => by simp)
  have hcube : (fun s : ℝ => s * (s * s)) =o[𝓝 0] fun s : ℝ => s ^ 2 := by
    refine (isLittleO_pow_pow (𝕜 := ℝ) (show 2 < 3 by norm_num)).congr_left (fun s => ?_)
    ring
  have hsq : (fun s : ℝ => s * s) = fun s : ℝ => s ^ 2 := funext fun s => by ring
  have hT1 : (fun s : ℝ => ∑ z, ((s : ℂ) * S.rayA1 x z) *
      ∑ i, S.rayDiff x s (z, i) * S.rayDiff x s (z, i)) =o[𝓝 0] fun s : ℝ => s ^ 2 := by
    refine isLittleO_sum_fn _ fun z _ => ?_
    have e1 : (fun s : ℝ => (s : ℂ) * S.rayA1 x z) =O[𝓝 0] fun s : ℝ => s := by
      have := hs.const_mul_left (S.rayA1 x z)
      simpa [mul_comm] using this
    have e2 : (fun s : ℝ => ∑ i, S.rayDiff x s (z, i) * S.rayDiff x s (z, i)) =O[𝓝 0]
        fun s : ℝ => s * s :=
      isBigO_sum_fn _ fun i _ => (hbig (z, i)).mul (hbig (z, i))
    exact (e1.mul e2).trans_isLittleO hcube
  have hT2 : (fun s : ℝ => pair (stepG d L N₁ m₁ k ϱ) (S.rayDiff x s - (s : ℂ) • S.rayP1 x)
      (S.rayHk *ᵥ (S.rayDiff x s - (s : ℂ) • S.rayP1 x))) =o[𝓝 0] fun s : ℝ => s ^ 2 := by
    unfold pair
    refine isLittleO_sum_fn _ fun p _ => ?_
    have e1 : (fun s : ℝ => (S.rayDiff x s - (s : ℂ) • S.rayP1 x) p) =o[𝓝 0] fun s : ℝ => s := by
      simpa [Complex.real_smul] using hlit p
    have e2 : (fun s : ℝ => (S.rayHk *ᵥ (S.rayDiff x s - (s : ℂ) • S.rayP1 x)) p) =o[𝓝 0]
        fun s : ℝ => s := by
      simp only [Matrix.mulVec, dotProduct]
      refine isLittleO_sum_fn _ fun q _ => ?_
      have := (hlit q).const_mul_left (S.rayHk p q)
      simpa [Complex.real_smul] using this
    have := e1.mul e2
    rwa [hsq] at this
  have := (hT1.const_mul_left (1 / 2 : ℂ)).add (hT2.const_mul_left (1 / 2 : ℂ))
  refine this.congr_left (fun s => ?_)
  rw [S.Vk_ray_eq ha₁ H hδ'0 hδ' hD'R s x]

end Order

section Vanish

variable {S} {pp : ℝ}

/-- The ray function `V(s) = Vk (ψ_s)` is `C^∞` at `s = 0` (landed `contDiffAt_Vray`). -/
theorem RayData.contDiffAt_Vk_line (R : S.RayData pp) (x : S.E) :
    ContDiffAt ℝ ⊤ (fun s : ℝ => S.Vk (S.psiAt s x)) 0 := by
  have hg := R.contDiffAt_Vray (q := ((0 : ℝ), x)) (by simpa using R.hpp)
  have hf : ContDiffAt ℝ ⊤ (fun s : ℝ => (s, x)) 0 :=
    (contDiff_id.prodMk contDiff_const).contDiffAt
  exact hg.comp 0 hf

/-- **HAT-RATE §2, order of vanishing.**  `V(0) = V'(0) = V''(0) = 0` along the ray, where
`V(s) = Vk (ψ_s)`; the only premise beyond `RayData` is the base-domain witness of
`theorem72_linearResponse` (radius `bgC2`), as HAT-RATE §2 requires. -/
theorem Vk_ray_vanish_of_baseDomain (R : S.RayData pp)
    (hbase : InUnionDomainC (stepG d L N₁ m₁ k ϱ) (bgC0 d L N) (bgC2 d L N) S.ν
      (S.dataU S.psi0)) (x : S.E) :
    S.Vk (S.psiAt 0 x) = 0 ∧ deriv (fun s : ℝ => S.Vk (S.psiAt s x)) 0 = 0 ∧
      deriv (deriv (fun s : ℝ => S.Vk (S.psiAt s x))) 0 = 0 :=
  derivs_zero_of_isLittleO_sq ((R.contDiffAt_Vk_line x).of_le (by exact_mod_cast le_top))
    (isLittleO_Vk_ray_of_baseDomain S R.ha₁ R.H R.hδ'0 R.hδ' R.hD'R hbase x)

/-- `V(0) = 0` (landed `Vk_psi0`). -/
theorem Vk_ray_zero (R : S.RayData pp) (x : S.E) : S.Vk (S.psiAt 0 x) = 0 := by
  unfold psiAt
  simpa using Vk_psi0 S R.ha₁ R.H R.hδ'0 R.hδ' R.hD'R

/-- `V'(0) = 0`. -/
theorem Vk_ray_deriv_zero_of_baseDomain (R : S.RayData pp)
    (hbase : InUnionDomainC (stepG d L N₁ m₁ k ϱ) (bgC0 d L N) (bgC2 d L N) S.ν
      (S.dataU S.psi0)) (x : S.E) :
    deriv (fun s : ℝ => S.Vk (S.psiAt s x)) 0 = 0 :=
  (Vk_ray_vanish_of_baseDomain R hbase x).2.1

/-- `V''(0) = 0`. -/
theorem Vk_ray_deriv2_zero_of_baseDomain (R : S.RayData pp)
    (hbase : InUnionDomainC (stepG d L N₁ m₁ k ϱ) (bgC0 d L N) (bgC2 d L N) S.ν
      (S.dataU S.psi0)) (x : S.E) :
    deriv (deriv (fun s : ℝ => S.Vk (S.psiAt s x))) 0 = 0 :=
  (Vk_ray_vanish_of_baseDomain R hbase x).2.2

end Vanish

end StepSetting

end Balaban.Fluctuation
