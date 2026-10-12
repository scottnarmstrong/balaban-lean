/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.StepComplexCov
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Proposition 2.6 for the step at a complex block datum (FLUCTUATION.md §2.6; P4 (2.36)-(2.63))

The identity (2.6) for the holomorphic objects of `StepComplexOut`, at every (complex) block datum
`θ` of the chart `Ξ^c(𝔹_{k+1}; 1, ε)` of RAY-CHART §1 (`XiCData`, under `FlCore` and the margins of
the covariance chart), with no realness of `θ`.  The proof is the proof of the landed
`prop26_complex`, step by step, with the complex objects; it is a direct computation (no analytic
continuation in the datum is used, and no connectedness of the chart):

* `quad_identityC`: the quadratic part of the exact expansion is `½ L^{k(d-2)} ⟨ψ', 𝒜 ψ'⟩` for a
  *complex* field `ψ'` of the unit lattice (both sides are quadratic forms; from the landed
  `quad_identity` for real fields by the identity theorem in one complex variable);
* `JbgC_expansion`: `J_k = A^η_{k+1} + ‖ψ̂‖²/(2β) + V^{(k)}` on the complex path (Lemma 2.3 (b) for
  complex data, `expansion_quadratic`; `C^{1/2 ᵀ} 𝒜 C^{1/2} = 1`, `covSqrtC_T_mul`);
* `integrandC_eq`: `∏ t_k · ρ_k (ψ^{(k)} + ψ') = P e^{-‖ψ̂‖²/2} e^{W₁(1) + W₂(1)}`;
* `dataUC_psiAtC_inUnionDomainC_plus`, `contDiffAt_VjointC`, `isC1Family_WVCT`,
  `stepRegularC_of_class`: the interaction `V^{(k)}` of the complex step is smooth along the ray, so
  that the regularity `StepRegularC` follows from that of the class terms (`ClassRegularC`);
* `prop26C_step` (with `StepRegularC`, `StepNonvanishingC`), `prop26C_class` (with `ClassRegularC`,
  `StepNonvanishingC`), `prop26C_class_of_activity` (with `ClassRegularC`, `StepActivityBoundC`):
  `TstepC = exp [-β_k A^η_{k+1} + ℰ_k(ψ^{(k)}) - E'''_k |T^{(k)}_1| + ℱ_k(ψ^{(k)}, g) + ℰ₀ + ℱ₀]`.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.SmallField.Def6 Balaban.Background Balaban.Multiscale Balaban.Localization
  Balaban.SmallField Finset Matrix

/-! ### The forms of the exact expansion are analytic -/

section AnalyticForms

variable {d L N₀ K N : ℕ} [NeZero N₀] [NeZero L] {ϱ ϱ' : ℝ}
  {G : GeneratingSet d L N₀ K ϱ} {G' : GeneratingSet d L N₀ K ϱ'}
  {Q : Type*} [NormedAddCommGroup Q] [NormedSpace ℂ Q] {q₀ : Q}

/-- The bilinear coupling term `couplingC` is analytic in its two fields. -/
theorem analyticAt_couplingC (a₁ : ℝ) (p : ℕ) {θF ψF : Q → Torus d (N₀ * L ^ K) → Fin N → ℂ}
    (hθ : ∀ y i, AnalyticAt ℂ (fun q => θF q y i) q₀)
    (hψ : ∀ y i, AnalyticAt ℂ (fun q => ψF q y i) q₀) :
    AnalyticAt ℂ (fun q => couplingC G' a₁ p (θF q) (ψF q)) q₀ := by
  unfold couplingC blockMean
  refine analyticAt_const.mul (Finset.analyticAt_fun_sum _ fun x _ =>
    Finset.analyticAt_fun_sum _ fun i _ => ?_)
  have h : AnalyticAt ℂ (fun q => θF q x i -
      ((((((L : ℝ) ^ p) ^ d)⁻¹ : ℝ) : ℂ)) * ∑ y ∈ G'.blk p x, ψF q y i) q₀ :=
    (hθ x i).sub (analyticAt_const.mul (Finset.analyticAt_fun_sum _ fun y _ => hψ y i))
  exact h.mul h

/-- The quadratic form `deltaForm` of (2.4) is analytic in the tangent `ψ'`. -/
theorem analyticAt_deltaForm (h : Precedes G G') (a : ℕ → ℝ) (ν : ℝ) (α₁ : G'.Ω 1 → ℂ)
    (φ₁ : G'.Ω 1 × Fin N → ℂ) {ψF : Q → Torus d (N₀ * L ^ K) → Fin N → ℂ}
    (hψ : ∀ y i, AnalyticAt ℂ (fun q => ψF q y i) q₀) :
    AnalyticAt ℂ (fun q => deltaForm h a ν α₁ φ₁ (ψF q)) q₀ := by
  have hS : ∀ p, AnalyticAt ℂ (fun q => qStar G a (ψF q) p) q₀ := fun p => by
    unfold qStar
    exact analyticAt_const.mul (hψ _ _)
  unfold deltaForm pair phiOne
  refine (Finset.analyticAt_fun_sum _ fun p _ => (hψ _ _).mul (hS p)).sub
    (Finset.analyticAt_fun_sum _ fun p _ => (hS p).mul ?_)
  simp only [Matrix.mulVec, dotProduct]
  exact Finset.analyticAt_fun_sum _ fun r _ => analyticAt_const.mul (hS r)

end AnalyticForms

/-! ### The quadratic part of the exact expansion at a complex field of the unit lattice -/

section QuadC

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
  {G G' : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}

/-- **The quadratic part of the exact expansion is `½ L^{k(d-2)} ⟨ψ', 𝒜 ψ'⟩` for a complex field
`ψ'` of the unit lattice** (Lemma 2.3 (b) with Lemma 2.4, bilinear products):
`couplingC (0, ψ') + ½ deltaForm(ψ') = ½ L^{k(d-2)} ⟨ψ', 𝒜 ψ'⟩`, `𝒜 = covOp`, for every
`ψ' ∈ (ℂ^N)^{T^{(k)}_1}` lifted to the fine torus.  The landed `quad_identity` is this identity for
real `ψ'`; both sides are quadratic forms in `ψ'`, so the complex case follows by the identity
theorem on the complex line through the real and imaginary parts of `ψ'`. -/
theorem quad_identityC (hG : IsLevel G k) (hG' : IsLevel G' (k + 1)) (a : ℕ → ℝ) (a₁ ν : ℝ)
    (α₁ : G'.Ω 1 → ℂ) (φ₁ : G'.Ω 1 × Fin N → ℂ) (v : unitPts G' × Fin N → ℂ) :
    couplingC G' a₁ (k + 1) (fun _ _ => 0) (liftC hG' v) +
        (1 / 2 : ℂ) * Balaban.Fluctuation.deltaForm (hG.precedes hG' (le_refl (k + 1))) a ν α₁ φ₁
          (liftC hG' v) =
      (((1 / 2) * (((L : ℝ) ^ k) ^ d / ((L : ℝ) ^ k) ^ 2) : ℝ) : ℂ) *
        (v ⬝ᵥ (covOp G' a a₁ ν α₁ (svec G' φ₁) (unitQ G') (unitP G') *ᵥ v)) := by
  classical
  set u : unitPts G' → Rn N := fun b => WithLp.toLp 2 (fun i => (v (b, i)).re) with hu
  set w : unitPts G' → Rn N := fun b => WithLp.toLp 2 (fun i => (v (b, i)).im) with hw
  have hv : v = yhat u + Complex.I • yhat w := by
    funext q
    obtain ⟨b, i⟩ := q
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, yhat, hu, hw]
    rw [mul_comm]
    exact (Complex.re_add_im _).symm
  have hlin : ∀ (z₀ : ℂ) (r : unitPts G' × Fin N),
      AnalyticAt ℂ (fun z : ℂ => (yhat u + z • yhat w) r) z₀ := by
    intro z₀ r
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact analyticAt_const.add (analyticAt_id.mul analyticAt_const)
  have hlift : ∀ (z₀ : ℂ) x i,
      AnalyticAt ℂ (fun z : ℂ => liftC hG' (yhat u + z • yhat w) x i) z₀ := fun z₀ x i => by
    simp only [liftC_apply]
    exact hlin z₀ _
  have han : AnalyticOnNhd ℂ (fun z : ℂ =>
      couplingC G' a₁ (k + 1) (fun _ _ => 0) (liftC hG' (yhat u + z • yhat w)) +
        (1 / 2 : ℂ) * Balaban.Fluctuation.deltaForm (hG.precedes hG' (le_refl (k + 1))) a ν α₁ φ₁
          (liftC hG' (yhat u + z • yhat w)) -
        (((1 / 2) * (((L : ℝ) ^ k) ^ d / ((L : ℝ) ^ k) ^ 2) : ℝ) : ℂ) *
          ((yhat u + z • yhat w) ⬝ᵥ
            (covOp G' a a₁ ν α₁ (svec G' φ₁) (unitQ G') (unitP G') *ᵥ (yhat u + z • yhat w))))
      Set.univ := by
    intro z₀ _
    refine ((analyticAt_couplingC a₁ (k + 1) (fun _ _ => analyticAt_const) (hlift z₀)).add
      (analyticAt_const.mul (analyticAt_deltaForm _ a ν α₁ φ₁ (hlift z₀)))).sub
      (analyticAt_const.mul ?_)
    simp only [dotProduct, Matrix.mulVec]
    exact Finset.analyticAt_fun_sum _ fun r _ => (hlin z₀ r).mul
      (Finset.analyticAt_fun_sum _ fun s _ => analyticAt_const.mul (hlin z₀ s))
  have hreal : ∀ t : ℝ,
      couplingC G' a₁ (k + 1) (fun _ _ => 0) (liftC hG' (yhat u + (t : ℂ) • yhat w)) +
        (1 / 2 : ℂ) * Balaban.Fluctuation.deltaForm (hG.precedes hG' (le_refl (k + 1))) a ν α₁ φ₁
          (liftC hG' (yhat u + (t : ℂ) • yhat w)) -
        (((1 / 2) * (((L : ℝ) ^ k) ^ d / ((L : ℝ) ^ k) ^ 2) : ℝ) : ℂ) *
          ((yhat u + (t : ℂ) • yhat w) ⬝ᵥ
            (covOp G' a a₁ ν α₁ (svec G' φ₁) (unitQ G') (unitP G') *ᵥ
              (yhat u + (t : ℂ) • yhat w))) = 0 := by
    intro t
    have e : yhat u + (t : ℂ) • yhat w = yhat (u + t • w) := by
      funext q
      simp [yhat]
    rw [e]
    exact sub_eq_zero.2 (quad_identity hG hG' a a₁ ν α₁ φ₁ (u + t • w))
  have hzero := eqOn_zero_of_real_zeros han isPreconnected_univ (Set.mem_univ 0)
    (fun ε hε => ⟨ε / 2, by positivity, by linarith, hreal _⟩)
  have hI := hzero Complex.I (Set.mem_univ _)
  rw [hv]
  exact sub_eq_zero.1 hI

end QuadC

/-! ### The integral of the fluctuation weight -/

section Weight

open MeasureTheory

variable {T : Type*} [Fintype T] {N : ℕ}

/-- **The integral of `P χ_fl e^{-‖ψ̂‖²/2} e^{W₁(1) + W₂(1)}` against Lebesgue measure is
`P Z₁^{|T|} Z_{1,1}`** (the product measure (2.5) as a density, `integral_fluctMeasure`). -/
theorem integral_fluct_weight_eq {p : ℝ} (hp : 0 < p) (P : ℂ) (W₁ W₂ : ℝ → (T → Rn N) → ℂ) :
    ∫ x, P * ((chiFl T N p x * gaussWeight T N x : ℝ) : ℂ) * Complex.exp (W₁ 1 x + W₂ 1 x) =
      P * ((fluctNorm N p ^ Fintype.card T : ℝ) : ℂ) *
        partFun₂ (fluctMeasure T N p) W₁ W₂ 1 1 := by
  have hZ : 0 < fluctNorm N p := fluctNorm_pos N hp
  have := integral_fluctMeasure (T := T) (N := N) p (fun x => Complex.exp (W₁ 1 x + W₂ 1 x))
  have hc : fluctNorm N p ^ Fintype.card T * (fluctNorm N p)⁻¹ ^ Fintype.card T = 1 := by
    rw [← mul_pow, mul_inv_cancel₀ hZ.ne', one_pow]
  unfold partFun₂
  have hI : ∫ x, ((chiFl T N p x * gaussWeight T N x : ℝ) : ℂ) *
        Complex.exp (W₁ 1 x + W₂ 1 x) =
      ((fluctNorm N p ^ Fintype.card T : ℝ) : ℂ) *
        ∫ x, Complex.exp (W₁ 1 x + W₂ 1 x) ∂fluctMeasure T N p := by
    rw [this]
    simp only [Complex.real_smul]
    rw [← mul_assoc, ← Complex.ofReal_mul, hc, Complex.ofReal_one, one_mul]
  have : ∀ x : T → Rn N, P * ((chiFl T N p x * gaussWeight T N x : ℝ) : ℂ) *
      Complex.exp (W₁ 1 x + W₂ 1 x) =
      P * (((chiFl T N p x * gaussWeight T N x : ℝ) : ℂ) * Complex.exp (W₁ 1 x + W₂ 1 x)) :=
    fun x => by ring
  simp only [this]
  rw [integral_const_mul, hI]
  ring

end Weight

namespace StepSetting

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}
  (S : StepSetting d L N₁ m₁ k N ϱ) (C : StepClass d L N₁ m₁ k N ϱ)

/-! ### The raw data of a complex old spin, and smoothness of the path -/

/-- The raw data `(Ψ, h̃)` of a complex field of the unit lattice (with the field `h₀`); `rawU` for
complex fields. -/
def rawUC (ψ : S.EC) : RawData d L (N₁ * L ^ m₁) (k + 1) N :=
  (liftC S.hG' ψ, fun _ i => (S.h₀ i : ℂ))

theorem dataUC_raw (ψ : S.EC) : ((S.dataUC ψ).Ψ, (S.dataUC ψ).h) = S.rawUC ψ := by
  refine Prod.ext ?_ ?_
  · funext z i
    show (S.dataUC ψ).Ψ z i = liftC S.hG' ψ z i
    rw [S.dataUC_Ψ, liftC_apply]
  · funext z i
    exact S.dataUC_h ψ z i

/-- The path `(s, ψ̂) ↦ ψ^{(k)}(θ) + s β_k^{-1/2} C^{(k)1/2}(θ) ψ̂` of the complex step is smooth
(real-linear in `ψ̂`, affine in `s`). -/
theorem contDiff_psiAtC : ContDiff ℝ ⊤ (fun q : ℝ × S.E => S.psiAtC q.1 q.2) := by
  refine contDiff_pi.2 fun p => ?_
  have e : (fun q : ℝ × S.E => S.psiAtC q.1 q.2 p) = fun q =>
      S.psi0C p + ((q.1 : ℝ) : ℂ) * (((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
        ∑ r : S.U × Fin N, S.covSqrtC p r * ((q.2 r.1 r.2 : ℝ) : ℂ)) := by
    funext q
    simp only [psiAtC, Pi.add_apply, Pi.smul_apply, smul_eq_mul, S.shiftUC_apply]
  rw [e]
  have h1 : ContDiff ℝ ⊤ (fun q : ℝ × S.E => ((q.1 : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp contDiff_fst
  have h2 : ∀ r : S.U × Fin N, ContDiff ℝ ⊤ (fun q : ℝ × S.E => ((q.2 r.1 r.2 : ℝ) : ℂ)) :=
    fun r => by
      have h : ContDiff ℝ ⊤ (fun q : ℝ × S.E => q.2 r.1 r.2) := by fun_prop
      exact Complex.ofRealCLM.contDiff.comp h
  exact contDiff_const.add (h1.mul (contDiff_const.mul
    (ContDiff.sum fun r _ => contDiff_const.mul (h2 r))))

theorem contDiff_rawUC_psiAtC :
    ContDiff ℝ ⊤ (fun q : ℝ × S.E => S.rawUC (S.psiAtC q.1 q.2)) := by
  unfold rawUC
  refine ContDiff.prodMk (contDiff_pi.2 fun z => contDiff_pi.2 fun i => ?_) contDiff_const
  simp only [liftC_apply]
  exact (contDiff_pi.1 S.contDiff_psiAtC) _

theorem psiAtC_one_sub (x : S.E) : S.psiAtC 1 x - S.psi0C = S.shiftUC x := by
  unfold psiAtC
  rw [Complex.ofReal_one, one_smul]
  abel

variable {c BG κ eps Kc Cx c₂ BG₂ δ₁ δc : ℝ}

/-! ### The complex path with the margin `p⁺`, and the regularity of `V^{(k)}` -/

section Plus

variable (hC : FlCore N S.G' (stepG d L N₁ m₁ k ϱ) S.a₁ S.ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
  (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
  (hdm : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
  (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
  (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
  (ha₁ : 0 < S.a₁) (hc7 : c7 d L N BG κ ≤ thm73C3 d L N) {R : ℝ} (hR : 1 < R)
  (hsmR : 2 * (compC4 d * (bgK1 d L N * (xiC1 d * eps))) + 5 * (R * δ₁) ≤ bgC1 d L N)
  (hβ : 0 ≤ S.β) {pp : ℝ} (hpp : 0 < pp)
  (hδ₁ : Real.sqrt N * (S.betaU ^ (-(1 / 2 : ℝ)) *
    (covSupConstC d L N (compWeight L S.a₁ k) κ * pp)) < δ₁)
  (hD : XiCData S.G' S.a S.ν (k + 1) 1 eps S.D')

include hC hMX hdm hα hsm ha₁ hc7 hR hsmR hβ hpp hδ₁ hD in
/-- **The complex old spin of the ray lies in the domain `𝒟` of the small solution, with margin**
(the complex form of `dataU_inDomainR_plus`): if `|s| ‖ψ̂‖ < p⁺` then the datum of
`ψ^{(k)}(θ) + s β_k^{-1/2} C^{(k)1/2}(θ) ψ̂` is in `𝒟(𝔹_k)`, for a complex block datum of the chart
(`√N β_k^{-1/2} C_sup p⁺ < δ₁`). -/
theorem dataUC_psiAtC_inUnionDomainC_plus {q : ℝ × S.E} (hq : |q.1| * ‖q.2‖ < pp) :
    InUnionDomainC (stepG d L N₁ m₁ k ϱ) (bgC0 d L N) (bgC1 d L N) S.ν
      (S.dataUC (S.psiAtC q.1 q.2)) := by
  refine inUnionDomainC_of_tangent_hatLift hC S.hk1 S.hG S.hG' ha₁ hC.HBp hc7 hR hsmR hMX hdm hα
    hsm _ hpp.le (by rwa [S.norm_betaU_rpow hβ]) (ψh := (q.1 : ℂ) • yhat q.2) (fun p => ?_) hD
    (fun z i => by rw [S.dataUC_h, S.hh₀]) (S.compTangent_psiAtC q.1 q.2)
  have h1 : ‖((q.2 p.1 p.2 : ℝ) : ℂ)‖ ≤ ‖q.2‖ := by
    rw [Complex.norm_real]
    exact (PiLp.norm_apply_le (q.2 p.1) p.2).trans (norm_le_pi_norm q.2 p.1)
  show ‖(q.1 : ℂ) * ((q.2 p.1 p.2 : ℝ) : ℂ)‖ ≤ pp
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  exact (mul_le_mul_of_nonneg_left h1 (abs_nonneg _)).trans hq.le

include hC hMX hdm hα hsm ha₁ hc7 hR hsmR hβ hpp hδ₁ hD in
/-- **The interaction of the complex step is smooth along the ray** (the complex form of
`contDiffAt_Vjoint`): `(s, ψ̂) ↦ V^{(k)}(ψ^{(k)}(θ) + s ψ')` is `C^∞` on `{|s| ‖ψ̂‖ < p⁺}`, for a
complex block datum of the chart.  (`V^{(k)}` is a polynomial in the tangent and in the field
`φ_k(ψ) - φ_{k+1}`, and the complex small solution `φ_k(ψ)` is the analytic function of the raw data
of Theorem 7.2.) -/
theorem contDiffAt_VjointC {q : ℝ × S.E} (hq : |q.1| * ‖q.2‖ < pp) :
    ContDiffAt ℝ ⊤ (fun q : ℝ × S.E => S.VkC (S.psiAtC q.1 q.2)) q := by
  obtain ⟨F, hF, hFe⟩ := theorem72_analytic (G := stepG d L N₁ m₁ k ϱ) (a := S.a) (ν := S.ν)
    (N := N) hC.HBp
  have hdomC := S.dataUC_psiAtC_inUnionDomainC_plus hC hMX hdm hα hsm ha₁ hc7 hR hsmR hβ hpp hδ₁
    hD hq
  have hFat : AnalyticAt ℂ F (S.rawUC (S.psiAtC q.1 q.2)) :=
    hF _ ⟨S.dataUC (S.psiAtC q.1 q.2), hdomC, (S.dataUC_raw _).symm⟩
  have hFc : ContDiffAt ℝ ⊤ F (S.rawUC (S.psiAtC q.1 q.2)) :=
    (hFat.contDiffAt (n := ⊤)).restrict_scalars ℝ
  have hraw := S.contDiff_rawUC_psiAtC
  have hG1 : ContDiffAt ℝ ⊤ (fun q : ℝ × S.E => F (S.rawUC (S.psiAtC q.1 q.2))) q :=
    hFc.comp q hraw.contDiffAt
  have hφ : ContDiffAt ℝ ⊤ (fun q : ℝ × S.E => (F (S.rawUC (S.psiAtC q.1 q.2))).1 -
      (S.hG.precedes S.hG' (le_refl (k + 1))).restrictφ
        (bgFieldC S.G' S.a S.ν (bgC0 d L N) S.D')) q :=
    (contDiff_fst.contDiffAt.comp q hG1).sub contDiffAt_const
  have hT : ContDiffAt ℝ ⊤
      (fun q : ℝ × S.E => liftC S.hG' (S.psiAtC q.1 q.2 - S.psi0C)) q := by
    refine ContDiff.contDiffAt (contDiff_pi.2 fun z => contDiff_pi.2 fun i => ?_)
    simp only [liftC_apply, Pi.sub_apply]
    exact ((contDiff_pi.1 S.contDiff_psiAtC) _).sub contDiff_const
  have hmodel : ContDiffAt ℝ ⊤ (fun q : ℝ × S.E =>
      S.Vpoly (liftC S.hG' (S.psiAtC q.1 q.2 - S.psi0C),
        (F (S.rawUC (S.psiAtC q.1 q.2))).1 -
          (S.hG.precedes S.hG' (le_refl (k + 1))).restrictφ
            (bgFieldC S.G' S.a S.ν (bgC0 d L N) S.D'))) q :=
    S.contDiff_Vpoly.contDiffAt.comp q (hT.prodMk hφ)
  refine hmodel.congr_of_eventuallyEq ?_
  have hopen : IsOpen {q : ℝ × S.E | |q.1| * ‖q.2‖ < pp} :=
    isOpen_lt (by fun_prop) continuous_const
  filter_upwards [hopen.mem_nhds hq] with q' hq'
  have hdomC' := S.dataUC_psiAtC_inUnionDomainC_plus hC hMX hdm hα hsm ha₁ hc7 hR hsmR hβ hpp
    hδ₁ hD hq'
  have hFq := hFe (S.dataUC (S.psiAtC q'.1 q'.2)) hdomC'
  rw [S.dataUC_raw] at hFq
  unfold VkC Vpoly
  rw [S.compTangent_dataUC, hFq]

include hC hMX hdm hα hsm ha₁ hc7 hR hsmR hβ hpp hδ₁ hD in
/-- **The interaction exponent of the complex step is a `C¹` family on a neighbourhood of `[0,1]`,
bounded with its derivative, on the support of `ν_{p₁}`** (the complex form of `isC1Family_WVT`;
needs `p₁ < p⁺`). -/
theorem isC1Family_WVCT (hp₁ : 0 < S.p₁) (hlt : S.p₁ < pp) :
    ∃ (U : Set ℝ) (V' : ℝ → S.E → ℂ), IsC1Family U S.WVCT V' := by
  obtain ⟨U, hU⟩ := S.isC1Family_trunc
    (f := fun q : ℝ × S.E => -(S.β : ℂ) * S.VkC (S.psiAtC q.1 q.2)) hp₁ hlt
    (fun q hq => contDiffAt_const.mul
      ((S.contDiffAt_VjointC hC hMX hdm hα hsm ha₁ hc7 hR hsmR hβ hpp hδ₁ hD hq).of_le
        (by exact_mod_cast le_top)))
  exact ⟨U, _, hU⟩

include hC hMX hdm hα hsm ha₁ hc7 hR hsmR hβ hpp hδ₁ hD in
/-- **The exponents of the complex step are regular, given the regularity of the class terms**
(the complex form of `stepRegular_of_class`): the interaction part is derived
(`isC1Family_WVCT`). -/
theorem stepRegularC_of_class (hp₁ : 0 < S.p₁) (hlt : S.p₁ < pp)
    (g : Fld d L N₁ m₁ (k + 1) N) (hc : S.ClassRegularC C g) : S.StepRegularC C g := by
  obtain ⟨U₁, V', hV⟩ := S.isC1Family_WVCT hC hMX hdm hα hsm ha₁ hc7 hR hsmR hβ hpp hδ₁ hD hp₁ hlt
  obtain ⟨U₂, E', F', hE, hF⟩ := hc.c1
  have hopen : IsOpen (U₁ ∩ U₂) := hV.isOpen.inter hE.isOpen
  have hIcc : Set.Icc (0 : ℝ) 1 ⊆ U₁ ∩ U₂ := fun s hs => ⟨hV.Icc_subset hs, hE.Icc_subset hs⟩
  have hV' := hV.restrict hopen Set.inter_subset_left hIcc
  have hE' := hE.restrict hopen Set.inter_subset_right hIcc
  have hF' := hF.restrict hopen Set.inter_subset_right hIcc
  refine ⟨⟨U₁ ∩ U₂, fun s x => V' s x + E' s x, F', ?_, hF'⟩⟩
  have : S.WoneCT C = fun s x => S.WVCT s x + S.dECT C s x := by
    funext s x
    exact S.WoneCT_eq_add C s x
  rw [this]
  exact hV'.add' hE'

end Plus

/-! ### The exact expansion and the integrand on the complex path -/

section Main

variable (hC : FlCore N S.G' (stepG d L N₁ m₁ k ϱ) S.a₁ S.ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
  (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
  (hdm : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
  (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
  (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
  (ha₁ : 0 < S.a₁) (hc7 : c7 d L N BG κ ≤ thm73C3 d L N) {R : ℝ} (hR : 1 < R)
  (hsmR : 2 * (compC4 d * (bgK1 d L N * (xiC1 d * eps))) + 5 * (R * δ₁) ≤ bgC1 d L N)
  (hβ : 0 < S.β) (hp₁ : 0 < S.p₁)
  (hδ₁ : Real.sqrt N * (S.betaU ^ (-(1 / 2 : ℝ)) *
    (covSupConstC d L N (compWeight L S.a₁ k) κ * S.p₁)) < δ₁)
  (hD : XiCData S.G' S.a S.ν (k + 1) 1 eps S.D')

include hC hMX hdm hα hsm hD in
/-- **`β ⟨ψ', 𝒜 ψ'⟩ = |ψ̂|²` for `ψ' = β^{-1/2} C^{1/2} ψ̂` at a complex datum** (the Gaussian part
of (2.6); the complex form of `quad_K`), with the bilinear product. -/
theorem quad_shiftUC (x : S.E) :
    S.shiftUC x ⬝ᵥ (S.covAC *ᵥ S.shiftUC x) =
      (((S.betaU ^ (-(1 / 2 : ℝ))) ^ 2 * ∑ b : S.U, ‖x b‖ ^ 2 : ℝ) : ℂ) := by
  have hT := S.covSqrtC_T_mul_of_chart hC hMX hdm hα hsm hD
  have key : (S.covSqrtC *ᵥ yhat x) ⬝ᵥ (S.covAC *ᵥ (S.covSqrtC *ᵥ yhat x)) =
      yhat x ⬝ᵥ yhat x := by
    calc (S.covSqrtC *ᵥ yhat x) ⬝ᵥ (S.covAC *ᵥ (S.covSqrtC *ᵥ yhat x))
        = (S.covSqrtCᵀ *ᵥ (S.covAC *ᵥ (S.covSqrtC *ᵥ yhat x))) ⬝ᵥ yhat x := by
          rw [dotProduct_comm, Matrix.dotProduct_mulVec, Matrix.mulVec_transpose]
      _ = ((S.covSqrtCᵀ * S.covAC * S.covSqrtC) *ᵥ yhat x) ⬝ᵥ yhat x := by
          simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]
      _ = yhat x ⬝ᵥ yhat x := by rw [hT, Matrix.one_mulVec]
  have hsh : S.shiftUC x = ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) • (S.covSqrtC *ᵥ yhat x) := rfl
  rw [hsh, Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul, key, S.yhat_dot]
  simp only [smul_eq_mul]
  push_cast
  ring

include hC hMX hdm hα hsm ha₁ hc7 hR hsmR hβ hp₁ hδ₁ hD in
/-- **The exact expansion (Lemma 2.3 (b)) on the complex path, at `s = 1`** (the complex form of
`Jbg_expansion`): with the bilinear products,
`½ a L⁻² (θ - Qψ)² + A_k(ψ, φ_k(ψ)) = A^η_{k+1}(θ, φ_{k+1}) + ‖ψ̂‖²/(2β) + V^{(k)}(ψ')` for
`ψ = ψ^{(k)}(θ) + β_k^{-1/2} C^{(k)1/2}(θ) ψ̂`, `χ_fl(ψ̂) = 1`, at a complex block datum of the
chart. -/
theorem JbgC_expansion (x : S.E) (hx : chiFl S.U N S.p₁ x = 1) :
    couplingC S.G' S.a₁ (k + 1) S.D'.Ψ (S.dataUC (S.psiAtC 1 x)).Ψ + S.AoldC (S.psiAtC 1 x) =
      S.AnewC + ((1 / (2 * S.β) * ∑ b : S.U, ‖x b‖ ^ 2 : ℝ) : ℂ) + S.VkC (S.psiAtC 1 x) := by
  have hL : 0 < L := Nat.pos_of_ne_zero (NeZero.ne L)
  have hβU := S.betaU_pos' hL hβ
  have h1 : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := Set.right_mem_Icc.2 zero_le_one
  have hDC := S.dataUC_psiAtC_inUnionDomainC hC hMX hdm hα hsm ha₁ hc7 hR hsmR hβ.le hp₁ hδ₁ hD
    h1 hx
  have hDC' : InUnionDomainC S.G' (bgC0 d L N) (thm73C2 d L N) S.ν S.D' :=
    (isDecBg_one_of_xiCData hC hD).2.mono (hc7.trans (thm73C3_le_thm73C2 d L N))
  have hh : ∀ z i, (S.dataUC (S.psiAtC 1 x)).h z i = S.D'.h z i := fun z i => by
    rw [S.dataUC_h, S.hh₀]
  have hexp := expansion_quadratic ha₁ S.hG S.hG' (le_refl (k + 1)) hC.HBp hC.HBp S.D' hDC'
    (S.dataUC (S.psiAtC 1 x)) hh hDC
  have htan : compTangent S.hG S.hG' (le_refl (k + 1)) S.a
      (bgFieldC S.G' S.a S.ν (bgC0 d L N) S.D') S.D' (S.dataUC (S.psiAtC 1 x)) =
      liftC S.hG' (S.shiftUC x) := by
    rw [S.compTangent_dataUC, S.psiAtC_one_sub]
  have hq := quad_identityC S.hG S.hG' S.a S.a₁ S.ν (bgMultC S.G' S.a S.ν (bgC0 d L N) S.D')
    (bgFieldC S.G' S.a S.ν (bgC0 d L N) S.D') (S.shiftUC x)
  have hK := S.quad_shiftUC hC hMX hdm hα hsm hD x
  have hcov : covOp S.G' S.a S.a₁ S.ν (bgMultC S.G' S.a S.ν (bgC0 d L N) S.D')
      (svec S.G' (bgFieldC S.G' S.a S.ν (bgC0 d L N) S.D')) (unitQ S.G') (unitP S.G') =
      S.covAC := rfl
  rw [hcov, hK, ← htan] at hq
  have hc2 : (S.betaU ^ (-(1 / 2 : ℝ))) ^ 2 = S.betaU⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hβU.le]
    norm_num
    exact Real.rpow_neg_one S.betaU
  have hL' : (0 : ℝ) < L := by exact_mod_cast hL
  have hLk : (0 : ℝ) < (L : ℝ) ^ k := by positivity
  have hbeta : S.betaU = S.β * (((L : ℝ) ^ k) ^ d / ((L : ℝ) ^ k) ^ 2) := by
    unfold betaU; ring
  have key : (((1 / 2) * (((L : ℝ) ^ k) ^ d / ((L : ℝ) ^ k) ^ 2) : ℝ)) *
      ((S.betaU ^ (-(1 / 2 : ℝ))) ^ 2 * ∑ b : S.U, ‖x b‖ ^ 2) =
      1 / (2 * S.β) * ∑ b : S.U, ‖x b‖ ^ 2 := by
    rw [hc2, hbeta]
    have : 0 < ((L : ℝ) ^ k) ^ d := by positivity
    field_simp
  have hqq : couplingC S.G' S.a₁ (k + 1) (fun _ _ => 0)
        (compTangent S.hG S.hG' (le_refl (k + 1)) S.a (bgFieldC S.G' S.a S.ν (bgC0 d L N) S.D')
          S.D' (S.dataUC (S.psiAtC 1 x))) +
      (1 / 2 : ℂ) * deltaForm (S.hG.precedes S.hG' (le_refl (k + 1))) S.a S.ν
        (bgMultC S.G' S.a S.ν (bgC0 d L N) S.D') (bgFieldC S.G' S.a S.ν (bgC0 d L N) S.D')
        (compTangent S.hG S.hG' (le_refl (k + 1)) S.a (bgFieldC S.G' S.a S.ν (bgC0 d L N) S.D')
          S.D' (S.dataUC (S.psiAtC 1 x))) =
      ((1 / (2 * S.β) * ∑ b : S.U, ‖x b‖ ^ 2 : ℝ) : ℂ) := by
    rw [hq, ← key]
    push_cast
    ring
  unfold AoldC AnewC VkC
  linear_combination hexp + hqq

include hC hMX hdm hα hsm ha₁ hc7 hR hsmR hβ hp₁ hδ₁ hD in
/-- **The integrand of the fluctuation integral on the complex path** (the complex form of
`integrand_eq`): for `χ_fl(ψ̂) = 1`,
`∏ t_k · ρ_k (ψ^{(k)} + ψ') = P e^{-‖ψ̂‖²/2} e^{W₁(1, ψ̂) + W₂(1, ψ̂)}`. -/
theorem integrandC_eq (g : Fld d L N₁ m₁ (k + 1) N) (x : S.E) (hx : chiFl S.U N S.p₁ x = 1) :
    S.tKernelC (S.psiAtC 1 x) * S.rhoExpC C g (S.psiAtC 1 x) =
      S.PconstC C g * ((gaussWeight S.U N x : ℝ) : ℂ) *
        Complex.exp (S.WoneC C 1 x + S.WtwoC C g 1 x) := by
  have hJ := S.JbgC_expansion hC hMX hdm hα hsm ha₁ hc7 hR hsmR hβ hp₁ hδ₁ hD x hx
  have hβc : (S.β : ℂ) ≠ 0 := by exact_mod_cast hβ.ne'
  have hJ2 : (S.β : ℂ) * (couplingC S.G' S.a₁ (k + 1) S.D'.Ψ (S.dataUC (S.psiAtC 1 x)).Ψ +
      S.AoldC (S.psiAtC 1 x)) =
      (S.β : ℂ) * S.AnewC + ((∑ b : S.U, ‖x b‖ ^ 2 : ℝ) : ℂ) / 2 +
        (S.β : ℂ) * S.VkC (S.psiAtC 1 x) := by
    rw [hJ]
    push_cast
    field_simp
  unfold tKernelC rhoExpC PconstC WoneC WtwoC gaussWeight
  rw [S.dEC_eq, S.dFC_eq, Complex.ofReal_exp, mul_assoc, mul_assoc, mul_assoc]
  congr 1
  rw [← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  push_cast at hJ2 ⊢
  linear_combination (-1 : ℂ) * hJ2

/-! ### Proposition 2.6 at a complex datum -/

include hC hMX hdm hα hsm ha₁ hc7 hR hsmR hβ hp₁ hδ₁ hD in
/-- **Proposition 2.6, (2.6)-(2.9), at a complex block datum** (whole lattice, `λ = ∞`, complete
convention; the complex form of `prop26_complex`).  For every block datum `θ` of the chart
`Ξ^c(𝔹_{k+1}; 1, ε)` (`XiCData`; complex `θ`, real constant `h`), under `FlCore` and the margins of
the covariance chart and of the ray (`hreal_level`),
`(T^{(k)} χ^{(k)} ρ_k)(θ) = exp [-β_k A^η_{k+1}(θ, φ_{k+1}) + ℰ_k(ψ^{(k)}(θ)) - E'''_k |T^{(k)}_1|
+ ℱ_k(ψ^{(k)}(θ), g) + ℰ₀^{(k+1)} + ℱ₀^{(k+1)}(g)]` for the holomorphic objects `TstepC`, `AnewC`,
`EcompAtC`, `FcompAtC`, `E0C`, `F0C`.  Premises: the regularity of the exponents of the complex
step along the ray (`StepRegularC`) and the nonvanishing `Z_{s,0}, Z_{1,t} ≠ 0`
(`StepNonvanishingC`). -/
theorem prop26C_step (g : Fld d L N₁ m₁ (k + 1) N) (hreg : S.StepRegularC C g)
    (hnv : S.StepNonvanishingC C g) :
    S.TstepC C g = Complex.exp (-(S.β : ℂ) * S.AnewC +
      EcompAtC C.m₀ C.Tm S.a S.ν (Nat.le_succ k) S.psiKdC - (S.Eppp C : ℂ) * (S.nU : ℂ) +
      FcompAtC C.m₀ C.Tm S.a S.ν (Nat.le_succ k) S.psiKdC g + S.E0C C + S.F0C C g) := by
  classical
  have hL : 0 < L := Nat.pos_of_ne_zero (NeZero.ne L)
  obtain ⟨U, W₁', W₂', h₁, h₂⟩ := hreg.c1
  have hprob := isProbabilityMeasure_fluctMeasure S.U N hp₁
  have hD1 : InUnionDomainC S.G' (bgC0 d L N) (thm73C1 d L N) S.ν S.D' :=
    (isDecBg_one_of_xiCData hC hD).2.mono
      ((hc7.trans (thm73C3_le_thm73C2 d L N)).trans (thm73C2_le_thm73C1 d L N))
  have hV0 := S.VkC_psi0C ha₁ hC.HBp hD1
  -- the integrand
  have hint : ∀ x : S.E, ((chiFl S.U N S.p₁ x : ℝ) : ℂ) *
        (S.tKernelC (S.psiAtC 1 x) * S.rhoExpC C g (S.psiAtC 1 x)) =
      S.PconstC C g * ((chiFl S.U N S.p₁ x * gaussWeight S.U N x : ℝ) : ℂ) *
        Complex.exp (S.WoneCT C 1 x + S.WtwoCT C g 1 x) := by
    intro x
    by_cases hx : chiFl S.U N S.p₁ x = 1
    · rw [S.integrandC_eq C hC hMX hdm hα hsm ha₁ hc7 hR hsmR hβ hp₁ hδ₁ hD g x hx,
        S.WoneCT_of_chi C 1 x hx, S.WtwoCT_of_chi C g 1 x hx, hx]
      push_cast
      ring
    · have h0 : chiFl S.U N S.p₁ x = 0 := (chiFl_eq_zero_or_one S.p₁ x).resolve_right hx
      rw [h0]
      simp
  have e2 := integral_fluct_weight_eq (T := S.U) (N := N) hp₁ (S.PconstC C g) (S.WoneCT C)
    (S.WtwoCT C g)
  have hZ00 : partFun₂ (fluctMeasure S.U N S.p₁) (S.WoneCT C) (S.WtwoCT C g) 0 0 = 1 := by
    unfold partFun₂
    simp [S.WoneCT_zero C _ hV0, S.WtwoCT_zero C g]
  have hexp := partFun₂_one_one_eq (ν := fluctMeasure S.U N S.p₁) h₁ h₂
    (fun s hs => by
      have h := hnv.seg1 s hs
      unfold ZstC at h
      rw [← partFun₂_congr_ae (ν := S.nuFl) (W₁ := S.WoneCT C) (W₁' := S.WoneC C)
        (W₂ := S.WtwoCT C g) (W₂' := S.WtwoC C g)
        ((S.ae_ball hp₁).mono fun x hx => S.WoneCT_of_chi C s x hx)
        ((S.ae_ball hp₁).mono fun x hx => S.WtwoCT_of_chi C g 0 x hx)] at h
      exact h)
    (fun t ht => by
      have h := hnv.seg2 t ht
      unfold ZstC at h
      rw [← partFun₂_congr_ae (ν := S.nuFl) (W₁ := S.WoneCT C) (W₁' := S.WoneC C)
        (W₂ := S.WtwoCT C g) (W₂' := S.WtwoC C g)
        ((S.ae_ball hp₁).mono fun x hx => S.WoneCT_of_chi C 1 x hx)
        ((S.ae_ball hp₁).mono fun x hx => S.WtwoCT_of_chi C g t x hx)] at h
      exact h)
  rw [hZ00, one_mul] at hexp
  have hI1 : (∫ s in (0 : ℝ)..1, avgFun₂ (fluctMeasure S.U N S.p₁) (S.WoneCT C) (S.WtwoCT C g)
      (W₁' s) s 0) = S.E1C C := by
    unfold E1C
    refine intervalIntegral.integral_congr (fun s hs => ?_)
    have hsU : s ∈ U := h₁.Icc_subset (by rwa [Set.uIcc_of_le zero_le_one] at hs)
    show avgFun₂ S.nuFl (S.WoneCT C) (S.WtwoCT C g) (W₁' s) s 0 = _
    rw [avgFun_eq_avgFun₂ (W₂ := S.WtwoC C g) (fun x => S.WtwoC_zero C g x)]
    refine avgFun₂_congr_ae ?_ ?_ ?_
    · exact (S.ae_ball hp₁).mono fun x hx => S.WoneCT_of_chi C s x hx
    · exact (S.ae_ball hp₁).mono fun x hx => S.WtwoCT_of_chi C g 0 x hx
    · filter_upwards [S.ae_ball hp₁] with x hx
      have hd := h₁.hasDerivAt x s hsU
      have hfun : (fun r => S.WoneCT C r x) = fun r => S.WoneC C r x :=
        funext fun r => S.WoneCT_of_chi C r x hx
      rw [hfun] at hd
      exact hd.deriv.symm
  have hI2 : (∫ t in (0 : ℝ)..1, avgFun₂ (fluctMeasure S.U N S.p₁) (S.WoneCT C) (S.WtwoCT C g)
      (W₂' t) 1 t) = S.F0C C g := by
    unfold F0C
    refine intervalIntegral.integral_congr (fun t ht => ?_)
    have htU : t ∈ U := h₂.Icc_subset (by rwa [Set.uIcc_of_le zero_le_one] at ht)
    show avgFun₂ S.nuFl (S.WoneCT C) (S.WtwoCT C g) (W₂' t) 1 t = _
    refine avgFun₂_congr_ae ?_ ?_ ?_
    · exact (S.ae_ball hp₁).mono fun x hx => S.WoneCT_of_chi C 1 x hx
    · exact (S.ae_ball hp₁).mono fun x hx => S.WtwoCT_of_chi C g t x hx
    · filter_upwards [S.ae_ball hp₁] with x hx
      have hd := h₂.hasDerivAt x t htU
      have hfun : (fun r => S.WtwoCT C g r x) = fun r => S.WtwoC C g r x :=
        funext fun r => S.WtwoCT_of_chi C g r x hx
      rw [hfun] at hd
      exact hd.deriv.symm
  have hconst := S.const_identity C hL ha₁ hβ hp₁
  have hdet := S.det_covSqrtC_of_chart hC hMX hdm hα hsm hD
  unfold TstepC
  rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hint), e2, hexp, hI1, hI2, hdet]
  unfold PconstC E0C
  set K0 : ℝ := (S.cKernel / (2 * Real.pi)) ^ ((N : ℝ) * S.nBlocks / 2) with hK0
  set bp : ℝ := S.betaU ^ (-((N * Fintype.card S.U : ℕ) : ℝ) / 2) with hbp
  set Zc : ℝ := fluctNorm N S.p₁ ^ Fintype.card S.U with hZc
  set Y : ℂ := -(S.β : ℂ) * S.AnewC +
      EcompAtC C.m₀ C.Tm S.a S.ν (Nat.le_succ k) S.psiKdC - (C.Ek : ℂ) * (S.nU : ℂ) +
      FcompAtC C.m₀ C.Tm S.a S.ν (Nat.le_succ k) S.psiKdC g with hY
  have hX : -(S.β : ℂ) * S.AnewC +
      EcompAtC C.m₀ C.Tm S.a S.ν (Nat.le_succ k) S.psiKdC - (S.Eppp C : ℂ) * (S.nU : ℂ) +
      FcompAtC C.m₀ C.Tm S.a S.ν (Nat.le_succ k) S.psiKdC g +
      (S.halfLogDetCC + S.E1C C) + S.F0C C g =
      Y + ((-((S.Eppp C - C.Ek) * S.nU) : ℝ) : ℂ) + S.halfLogDetCC + (S.E1C C + S.F0C C g) := by
    rw [hY]; push_cast; ring
  have hexpc : Complex.exp (((-((S.Eppp C - C.Ek) * S.nU) : ℝ) : ℂ)) =
      (K0 : ℂ) * ((bp : ℂ) * (Zc : ℂ)) := by
    rw [← Complex.ofReal_exp, ← hconst]
    push_cast
    ring
  have hE : Complex.exp (Y + ((-((S.Eppp C - C.Ek) * S.nU) : ℝ) : ℂ) + S.halfLogDetCC +
      (S.E1C C + S.F0C C g)) =
      Complex.exp Y * ((K0 : ℂ) * ((bp : ℂ) * (Zc : ℂ))) * Complex.exp S.halfLogDetCC *
        Complex.exp (S.E1C C + S.F0C C g) := by
    rw [Complex.exp_add _ (S.E1C C + S.F0C C g), Complex.exp_add _ S.halfLogDetCC,
      Complex.exp_add Y, hexpc]
  rw [hX, hE]
  ring

end Main

/-! ### With the class regularity, and with the activity bound -/

section Public

variable (hC : FlCore N S.G' (stepG d L N₁ m₁ k ϱ) S.a₁ S.ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
  (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
  (hdm : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
  (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
  (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
  (ha₁ : 0 < S.a₁) (hc7 : c7 d L N BG κ ≤ thm73C3 d L N) {R : ℝ} (hR : 1 < R)
  (hsmR : 2 * (compC4 d * (bgK1 d L N * (xiC1 d * eps))) + 5 * (R * δ₁) ≤ bgC1 d L N)
  (hβ : 0 < S.β) (hp₁ : 0 < S.p₁) {pp : ℝ} (hlt : S.p₁ < pp)
  (hδ₁ : Real.sqrt N * (S.betaU ^ (-(1 / 2 : ℝ)) *
    (covSupConstC d L N (compWeight L S.a₁ k) κ * pp)) < δ₁)
  (hD : XiCData S.G' S.a S.ν (k + 1) 1 eps S.D')

include hC hβ hp₁ hlt hδ₁ in
/-- The margin `√N β_k^{-1/2} C_sup p⁺ < δ₁` implies the one for `p₁ < p⁺`. -/
theorem margin_smallC : Real.sqrt N * (S.betaU ^ (-(1 / 2 : ℝ)) *
    (covSupConstC d L N (compWeight L S.a₁ k) κ * S.p₁)) < δ₁ := by
  have hL : 0 < L := Nat.pos_of_ne_zero (NeZero.ne L)
  have hb : 0 ≤ S.betaU ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg (S.betaU_pos' hL hβ).le _
  have hN := Real.sqrt_nonneg (N : ℝ)
  rcases le_or_gt 0 (covSupConstC d L N (compWeight L S.a₁ k) κ) with hc | hc
  · refine lt_of_le_of_lt ?_ hδ₁
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hlt.le hc) hb) hN
  · refine lt_of_le_of_lt ?_ hC.δ₁_pos
    exact mul_nonpos_of_nonneg_of_nonpos hN (mul_nonpos_of_nonneg_of_nonpos hb
      (mul_nonpos_of_nonpos_of_nonneg hc.le hp₁.le))

include hC hMX hdm hα hsm ha₁ hc7 hR hsmR hβ hp₁ hlt hδ₁ hD in
/-- **Proposition 2.6 at a complex block datum, with the class regularity** (the complex form of
`prop26_complex_class`): for every block datum of the chart `Ξ^c(𝔹_{k+1}; 1, ε)`, with the class
regularity `ClassRegularC` as the analytic input and the nonvanishing of `Z_{s,0}, Z_{1,t}`
(`StepNonvanishingC`).  The margin `p₁ < p⁺` in `√N β_k^{-1/2} C_sup p⁺ < δ₁` ("`β` large"). -/
theorem prop26C_class (g : Fld d L N₁ m₁ (k + 1) N) (hc : S.ClassRegularC C g)
    (hnv : S.StepNonvanishingC C g) :
    S.TstepC C g = Complex.exp (-(S.β : ℂ) * S.AnewC +
      EcompAtC C.m₀ C.Tm S.a S.ν (Nat.le_succ k) S.psiKdC - (S.Eppp C : ℂ) * (S.nU : ℂ) +
      FcompAtC C.m₀ C.Tm S.a S.ν (Nat.le_succ k) S.psiKdC g + S.E0C C + S.F0C C g) :=
  S.prop26C_step C hC hMX hdm hα hsm ha₁ hc7 hR hsmR hβ hp₁
    (S.margin_smallC hC hβ hp₁ hlt hδ₁) hD g
    (S.stepRegularC_of_class C hC hMX hdm hα hsm ha₁ hc7 hR hsmR hβ.le (hp₁.trans hlt) hδ₁ hD
      hp₁ hlt g hc) hnv

include hC hMX hdm hα hsm ha₁ hc7 hR hsmR hβ hp₁ hlt hδ₁ hD in
/-- **Proposition 2.6 at a complex block datum, with the activity bound of the complex step** (the
complex form of `prop26_complex_class_of_activity`): the class regularity `ClassRegularC` and the
physical complex activity bound `StepActivityBoundC` are the inputs. -/
theorem prop26C_class_of_activity (g : Fld d L N₁ m₁ (k + 1) N) (hc : S.ClassRegularC C g)
    (hact : StepActivityBoundC S C g) :
    S.TstepC C g = Complex.exp (-(S.β : ℂ) * S.AnewC +
      EcompAtC C.m₀ C.Tm S.a S.ν (Nat.le_succ k) S.psiKdC - (S.Eppp C : ℂ) * (S.nU : ℂ) +
      FcompAtC C.m₀ C.Tm S.a S.ν (Nat.le_succ k) S.psiKdC g + S.E0C C + S.F0C C g) :=
  S.prop26C_class C hC hMX hdm hα hsm ha₁ hc7 hR hsmR hβ hp₁ hlt hδ₁ hD g hc
    (stepNonvanishingC_of_activityBoundC hact)

end Public

end StepSetting

end Balaban.Fluctuation
