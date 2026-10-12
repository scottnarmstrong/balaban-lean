/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.StepActivityHat
public import Balaban.Fluctuation.StepActivityHatFlRay
public import Balaban.Fluctuation.StepComplexAgree
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The source part of the step exponent is the value of the hat expansion

The source part of the expansion `val` of `interaction_expansion_hat` is
`c_β ∑_s p₂(s) · dirTermSrc (hatFun … (svec (flFieldOne …) s)) 1 ψ̂ ψ̂ u Θ`, and
`dirTermSrc f 1 ψ̂ ψ̂ u Θ = u ∫₀¹ ∂_ψ̂ f(Θ, u t ψ̂) dt = F(u) - F(0)` for `F(l) = f(Θ, l ψ̂)`
(`dirTermSrc_ray`: the fundamental theorem of calculus along the real ray).  For the zero class
and the source `g` (with `p₂ = g/β`, `c_β = β`) it is therefore
`∑_s g_s (δφ_s(u ψ̂) - δφ_s(0))` with `δφ(ψ̂) = flFieldOne D' (hatLift ψ̂)`, which is
`W₂(u, ψ̂; g)` of the step, since `φ_k(ψ^{(k)} + u ψ') - φ_{k+1}| = δφ(u ψ̂)`
(`bgFieldC_sub_eq_flFieldOne_hatLift`).  There is no `u²` factor.
-/

@[expose] public section

namespace Balaban.Fluctuation

open MeasureTheory Balaban Balaban.Localization Balaban.Multiscale
  Balaban.Background Balaban.SmallField Balaban.SmallField.Def6 Balaban.Analysis Finset Matrix Set
  Filter Topology

section Ftc

variable {Λ : Type*}
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- **The directional term along the real ray is a difference of values**: if `G` is analytic at
the real points of `[0,1]` and `f(Θ, l ψ) = G l`, then for real `t ∈ [0,1]`
`dirTermSrc f 1 ψ ψ t Θ = G t - G 0`. -/
theorem dirTermSrc_ray (f : Λ × F → ℂ) (Θ : Λ) (ψ : F) (G : ℂ → ℂ)
    (hG : ∀ l : ℂ, f (Θ, l • ψ) = G l)
    (han : ∀ r : ℝ, r ∈ Icc (0 : ℝ) 1 → AnalyticAt ℂ G (r : ℂ)) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) :
    dirTermSrc f (fun _ => (1 : ℂ)) ψ ψ (t : ℂ) Θ = G (t : ℂ) - G 0 := by
  have hmem : ∀ u : ℝ, u ∈ Icc (0 : ℝ) 1 → t * u ∈ Icc (0 : ℝ) 1 := fun u hu =>
    ⟨mul_nonneg ht.1 hu.1, by nlinarith [ht.1, ht.2, hu.1, hu.2]⟩
  have hline : ∀ u : ℝ, u ∈ Icc (0 : ℝ) 1 →
      lineD ψ (fun z => f (Θ, z)) (((t : ℂ) * (u : ℂ)) • ψ) = deriv G ((t * u : ℝ) : ℂ) := by
    intro u hu
    unfold lineD
    have e : (fun τ : ℂ => f (Θ, ((t : ℂ) * (u : ℂ)) • ψ + τ • ψ)) =
        fun τ : ℂ => G (((t * u : ℝ) : ℂ) + τ) := by
      funext τ
      rw [← add_smul, hG]
      push_cast
      rfl
    rw [e]
    have h1 := deriv_comp_const_add G ((t * u : ℝ) : ℂ) 0
    simpa using h1
  have hcont : ContinuousOn (fun u : ℝ => (t : ℂ) * deriv G ((t * u : ℝ) : ℂ)) (Icc 0 1) := by
    intro u hu
    refine ContinuousAt.continuousWithinAt ?_
    have h1 : ContinuousAt (deriv G) ((t * u : ℝ) : ℂ) := (han _ (hmem u hu)).deriv.continuousAt
    have h2 : ContinuousAt (fun u : ℝ => ((t * u : ℝ) : ℂ)) u := by fun_prop
    exact continuousAt_const.mul (ContinuousAt.comp (g := deriv G) (f := fun u : ℝ => ((t * u : ℝ) : ℂ)) h1 h2)
  have hderiv : ∀ u ∈ uIcc (0 : ℝ) 1, HasDerivAt (fun u : ℝ => G ((t * u : ℝ) : ℂ))
      ((t : ℂ) * deriv G ((t * u : ℝ) : ℂ)) u := by
    intro u hu
    rw [Set.uIcc_of_le zero_le_one] at hu
    have h1 : HasDerivAt (fun r : ℝ => G (r : ℂ)) (deriv G ((t * u : ℝ) : ℂ)) (t * u) :=
      ((han _ (hmem u hu)).differentiableAt.hasDerivAt).comp_ofReal
    have h2 : HasDerivAt (fun u : ℝ => t * u) t u := by
      simpa using (hasDerivAt_id u).const_mul t
    have h3 : HasDerivAt ((fun r : ℝ => G (r : ℂ)) ∘ fun u : ℝ => t * u)
        (t • deriv G ((t * u : ℝ) : ℂ)) u := h1.scomp u h2
    rw [Complex.real_smul] at h3
    exact h3
  unfold dirTermSrc
  have hint : ∫ u in (0 : ℝ)..1, (fun _ : ℂ => (1 : ℂ)) (u : ℂ) *
      lineD ψ (fun z => f (Θ, z)) (((t : ℂ) * (u : ℂ)) • ψ) =
      ∫ u in (0 : ℝ)..1, deriv G ((t * u : ℝ) : ℂ) := by
    refine intervalIntegral.integral_congr fun u hu => ?_
    rw [Set.uIcc_of_le zero_le_one] at hu
    simp only [one_mul]
    exact hline u hu
  rw [hint, ← intervalIntegral.integral_const_mul]
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    (hcont.intervalIntegrable_of_Icc zero_le_one)]
  simp

end Ftc

section Step

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}

namespace StepSetting

variable (S : StepSetting d L N₁ m₁ k N ϱ)
variable {c BG κ eps Kc Cx c₂ BG₂ δ₁ δc : ℝ} {pp : ℝ}

/-- The zero class: `W₂(t, ψ̂; g)` is the pairing of `g` with `φ_k(ψ_t) - φ_k(ψ_0)`. -/
theorem WtwoC_zeroClass_eq (g : Fld d L N₁ m₁ (k + 1) N) (t : ℝ) (x : S.E) :
    S.WtwoC (zeroClass d L N₁ m₁ k N ϱ) g t x =
      ∑ y : CTorus d L N₁ m₁ (k + 1), ∑ i : Fin N, g y i *
        (svec (stepG d L N₁ m₁ k ϱ) (bgFieldC (stepG d L N₁ m₁ k ϱ) S.a S.ν (bgC0 d L N)
          (S.dataUC (S.psiAtC t x))) y i -
        svec (stepG d L N₁ m₁ k ϱ) (bgFieldC (stepG d L N₁ m₁ k ϱ) S.a S.ν (bgC0 d L N)
          (S.dataUC (S.psiAtC 0 x))) y i) := by
  have hz : ∀ D, FcompAtC (zeroClass d L N₁ m₁ k N ϱ).m₀ (zeroClass d L N₁ m₁ k N ϱ).Tm S.a S.ν
      (Nat.le_succ k) D g = ∑ y : CTorus d L N₁ m₁ (k + 1), ∑ i : Fin N, g y i *
        svec (stepG d L N₁ m₁ k ϱ) (bgFieldC (stepG d L N₁ m₁ k ϱ) S.a S.ν (bgC0 d L N) D) y i := by
    intro D
    show FcompAtC 0 (zeroTerms d L N₁ m₁ (k + 1) N ϱ) S.a S.ν (Nat.le_succ k) D g = _
    simp [FcompAtC, Floc_zero]
  unfold WtwoC dFC
  rw [hz, hz, S.psiAtC_zero, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

variable (hC : FlCore N S.G' (stepG d L N₁ m₁ k ϱ) S.a₁ S.ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
  (R0 : S.RayData pp) (hlt : S.p₁ < pp)
  (hD : XiCData S.G' S.a S.ν (k + 1) 1 eps S.D')
  (hc7 : c7 d L N BG κ ≤ thm73C3 d L N) {R : ℝ} (hR : 2 ≤ R)
  (hsmR : 2 * (compC4 d * (bgK1 d L N * (xiC1 d * eps))) + 5 * (R * δ₁) ≤ bgC1 d L N)
  (hRs : R * δ₁ ≤ deltaStar d L N) (hsmall : cK2 d L N * (R * δ₁) < bgC0 d L N / 2)
  (hnum : cK2 d L N * δ₁ ≤ c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8))
  (hnum' : cK2' d L N (famConst d L BG₂ κ) * δ₁ ≤
    c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8))
  (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
  (hdm : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
  (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
  (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4) (hp₁ : 0 < S.p₁) {cψ : ℝ} (hcψ : 0 ≤ cψ)
  (hpc : S.p₁ < cψ)
  (hδ₁ : Real.sqrt N * (‖((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)‖ *
    (covSupConstC d L N (compWeight L S.a₁ k) κ * cψ)) < δ₁)

include hC R0 hD hc7 hR hsmR hRs hsmall hnum hnum' hMX hdm hα hsm hp₁ hcψ hpc hδ₁ in
/-- **The ray of the source functional**: for `r ∈ [0,1]` and `χ_fl(ψ̂) = 1`,
`δφ(r ψ̂) = flFieldOne D' (hatLift (r ψ̂))` is `φ_k(ψ^{(k)} + r ψ') - φ_{k+1}|`. -/
theorem flFieldOne_ray_eq {r : ℝ} (hr : r ∈ Icc (0 : ℝ) 1) {x : S.E}
    (hx : chiFl S.U N S.p₁ x = 1) :
    flFieldOne S.G' (stepG d L N₁ m₁ k ϱ) BG₂ κ S.a₁ S.ν S.D'
        (hatLift S.G' S.a₁ S.ν S.hG' ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) S.D'
          ((r : ℂ) • yhat x)) =
      bgFieldC (stepG d L N₁ m₁ k ϱ) S.a S.ν (bgC0 d L N) (S.dataUC (S.psiAtC r x)) -
        (S.hG.precedes S.hG' (le_refl (k + 1))).restrictφ
          (bgFieldC S.G' S.a S.ν (bgC0 d L N) S.D') := by
  have hb : ∀ p, ‖((r : ℂ) • yhat x) p‖ ≤ cψ := fun p =>
    (S.norm_smul_yhat_le hp₁ hr hx p).trans hpc.le
  exact (bgFieldC_sub_eq_flFieldOne_hatLift hC S.hk1 S.hG S.hG' R0.ha₁ R0.H hc7 hR hsmR hRs hsmall
    hnum hnum' hMX hdm hα hsm _ hcψ hδ₁ hD (D := S.dataUC (S.psiAtC r x))
    (fun z i => by rw [S.dataUC_h, S.hh₀]) hb (S.compTangent_psiAtC r x)).symm

include hC R0 hlt hD hc7 hR hsmR hRs hsmall hnum hnum' hMX hdm hα hsm hp₁ hcψ hpc hδ₁ in
/-- **T3: the source part of the step exponent is the value of the hat expansion.**  For the zero
class, a source `g`, `t ∈ [0,1]` and `ψ̂` in the support of `ν_{p₁}` (`χ_fl(ψ̂) = 1`),
`β ∑_s (g_s/β) · dirTermSrc (hatFun … (svec (flFieldOne …) s)) 1 ψ̂ ψ̂ t Θ = W₂(t, ψ̂; g)`.
The source part of `val` (with `c_β = β`, `p₂ = g/β`) is the exponent `W₂` itself, with no `t²`
factor: `∑_s g_s (δφ_s(t ψ̂) - δφ_s(0)) = ∑_s g_s (φ_k(ψ_t) - φ_k(ψ_0))_s`. -/
theorem Wtwo_zeroClass_eq_hat (g : Fld d L N₁ m₁ (k + 1) N) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1)
    {x : S.E} (hx : chiFl S.U N S.p₁ x = 1) :
    (S.β : ℂ) * (∑ s : CTorus d L N₁ m₁ (k + 1) × Fin N, (g s.1 s.2 / (S.β : ℂ)) *
      dirTermSrc (hatFun S.G' S.a₁ S.ν eps S.hG' ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)
        (onXi S.G' S.a₁ S.ν eps
          (fun D ψ' => svec (stepG d L N₁ m₁ k ϱ)
            (flFieldOne S.G' (stepG d L N₁ m₁ k ϱ) BG₂ κ S.a₁ S.ν D ψ') s.1 s.2)))
        (fun _ => (1 : ℂ)) (S.hatC x) (S.hatC x) (t : ℂ) (rawOf S.D')) =
      S.Wtwo (zeroClass d L N₁ m₁ k N ϱ) g t x := by
  have hχ := (chiU_eq_one_iff _ _ _ _).1 R0.hχu
  set cc : ℂ := ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) with hcc
  have hβ : (S.β : ℂ) ≠ 0 := by exact_mod_cast R0.hβ.ne'
  -- the coordinate functions along the ray
  let Gs : CTorus d L N₁ m₁ (k + 1) × Fin N → ℂ → ℂ := fun s l =>
    hatFun S.G' S.a₁ S.ν eps S.hG' cc
      (onXi S.G' S.a₁ S.ν eps
        (fun D ψ' => svec (stepG d L N₁ m₁ k ϱ)
          (flFieldOne S.G' (stepG d L N₁ m₁ k ϱ) BG₂ κ S.a₁ S.ν D ψ') s.1 s.2))
      (rawOf S.D', l • yhat x)
  have hGs : ∀ s l, Gs s l = svec (stepG d L N₁ m₁ k ϱ)
      (flFieldOne S.G' (stepG d L N₁ m₁ k ϱ) BG₂ κ S.a₁ S.ν S.D'
        (hatLift S.G' S.a₁ S.ν S.hG' cc S.D' (l • yhat x))) s.1 s.2 := by
    intro s l
    show hatFun S.G' S.a₁ S.ν eps S.hG' cc _ (rawOf S.D', l • yhat x) = _
    rw [hatFun_rawOf S.hG' cc _ hD, onXi_rawOf hD]
  have hAn : ∀ s, ∀ r : ℝ, r ∈ Icc (0 : ℝ) 1 → AnalyticAt ℂ (Gs s) (r : ℂ) := by
    intro s r hr
    have hb : ∀ p, ‖(r : ℂ) * yhat x p‖ < cψ := fun p => by
      have := S.norm_smul_yhat_le hp₁ hr hx p
      have e : ((r : ℂ) • yhat x) p = (r : ℂ) * yhat x p := rfl
      rw [e] at this
      exact lt_of_le_of_lt this hpc
    have hfun : Gs s = fun l => svec (stepG d L N₁ m₁ k ϱ)
        (flFieldOne S.G' (stepG d L N₁ m₁ k ϱ) BG₂ κ S.a₁ S.ν S.D'
          (hatLift S.G' S.a₁ S.ν S.hG' cc S.D' (l • yhat x))) s.1 s.2 := funext (hGs s)
    rw [hfun]
    by_cases hm : s.1 ∈ (stepG d L N₁ m₁ k ϱ).Ω 1
    · have e : (fun l : ℂ => svec (stepG d L N₁ m₁ k ϱ)
          (flFieldOne S.G' (stepG d L N₁ m₁ k ϱ) BG₂ κ S.a₁ S.ν S.D'
            (hatLift S.G' S.a₁ S.ν S.hG' cc S.D' (l • yhat x))) s.1 s.2) =
          fun l => flFieldOne S.G' (stepG d L N₁ m₁ k ϱ) BG₂ κ S.a₁ S.ν S.D'
            (hatLift S.G' S.a₁ S.ν S.hG' cc S.D' (l • yhat x)) (⟨s.1, hm⟩, s.2) := by
        funext l; exact svec_of_mem (stepG d L N₁ m₁ k ϱ) _ ⟨s.1, hm⟩ s.2
      rw [e]
      exact analyticAt_flFieldOne_hatRay hC S.hk1 S.hG S.hG' R0.ha₁ R0.H hc7 hR hsmR hRs hsmall
        hnum hnum' hMX hdm hα hsm cc hcψ hδ₁ hD (yhat x) hb (⟨s.1, hm⟩, s.2)
    · have e : (fun l : ℂ => svec (stepG d L N₁ m₁ k ϱ)
          (flFieldOne S.G' (stepG d L N₁ m₁ k ϱ) BG₂ κ S.a₁ S.ν S.D'
            (hatLift S.G' S.a₁ S.ν S.hG' cc S.D' (l • yhat x))) s.1 s.2) = fun _ => 0 := by
        funext l; exact svec_of_not_mem (stepG d L N₁ m₁ k ϱ) _ hm s.2
      rw [e]
      exact analyticAt_const
  have hsrc : ∀ s, dirTermSrc (hatFun S.G' S.a₁ S.ν eps S.hG' cc
        (onXi S.G' S.a₁ S.ν eps
          (fun D ψ' => svec (stepG d L N₁ m₁ k ϱ)
            (flFieldOne S.G' (stepG d L N₁ m₁ k ϱ) BG₂ κ S.a₁ S.ν D ψ') s.1 s.2)))
        (fun _ => (1 : ℂ)) (S.hatC x) (S.hatC x) (t : ℂ) (rawOf S.D') = Gs s (t : ℂ) - Gs s 0 :=
    fun s => dirTermSrc_ray _ (rawOf S.D') (S.hatC x) (Gs s) (fun l => rfl) (hAn s) ht
  -- the radius conditions at `p₁ < pp`
  have hbpos := R0.betaU_pos
  have hp40' : S.p₁ / (S.betaU ^ (1 / 2 : ℝ) * S.δ) ≤ (3 * R0.B₅ * R0.K₂)⁻¹ :=
    (div_le_div_of_nonneg_right hlt.le (by have := R0.hδ0; positivity)).trans R0.hp40
  have hB5pos : 0 ≤ R0.B₅ := le_trans (by norm_num) (le_trans (le_max_left _ _) R0.hB5)
  have hrad' : R0.B₅ * S.betaU ^ (-(1 / 2 : ℝ)) * S.p₁ ≤ fluctRadius d L N :=
    le_trans (mul_le_mul_of_nonneg_left hlt.le (by positivity)) R0.hrad
  -- the real side
  have hxe : S.Wtwo (zeroClass d L N₁ m₁ k N ϱ) g t x =
      S.WtwoC (zeroClass d L N₁ m₁ k N ϱ) g t x :=
    (S.WtwoC_eq (zeroClass d L N₁ m₁ k N ϱ) R0.ha₁ R0.H R0.hδ'0 R0.hδ' R0.hD'R R0.hδ0 R0.hfam
      R0.hsm R0.hχu R0.hnorm R0.hβ hp₁ R0.hB5 R0.hK2 hp40' hrad' g ht x hx).symm
  rw [hxe, S.WtwoC_zeroClass_eq]
  simp only [hsrc]
  rw [Fintype.sum_prod_type, Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h1 := S.flFieldOne_ray_eq hC R0 hD hc7 hR hsmR hRs hsmall hnum hnum' hMX hdm hα hsm hp₁ hcψ
    hpc hδ₁ ht hx
  have h0 := S.flFieldOne_ray_eq hC R0 hD hc7 hR hsmR hRs hsmall hnum hnum' hMX hdm hα hsm hp₁ hcψ
    hpc hδ₁ (r := 0) ⟨le_rfl, zero_le_one⟩ hx
  have hsub : ∀ (A B : (stepG d L N₁ m₁ k ϱ).Ω 1 × Fin N → ℂ),
      svec (stepG d L N₁ m₁ k ϱ) (A - B) y i =
        svec (stepG d L N₁ m₁ k ϱ) A y i - svec (stepG d L N₁ m₁ k ϱ) B y i := by
    intro A B
    by_cases hm : y ∈ (stepG d L N₁ m₁ k ϱ).Ω 1
    · rw [svec_of_mem (stepG d L N₁ m₁ k ϱ) _ ⟨y, hm⟩ i, svec_of_mem (stepG d L N₁ m₁ k ϱ) _ ⟨y, hm⟩ i,
        svec_of_mem (stepG d L N₁ m₁ k ϱ) _ ⟨y, hm⟩ i]
      rfl
    · rw [svec_of_not_mem (stepG d L N₁ m₁ k ϱ) _ hm i, svec_of_not_mem (stepG d L N₁ m₁ k ϱ) _ hm i,
        svec_of_not_mem (stepG d L N₁ m₁ k ϱ) _ hm i]
      simp
  rw [hGs, hGs, h1, show (0 : ℂ) = ((0 : ℝ) : ℂ) by simp, h0, hsub, hsub]
  field_simp
  ring

end StepSetting

end Step

end Balaban.Fluctuation
