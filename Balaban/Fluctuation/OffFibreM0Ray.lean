/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.ObsIntegrandBridge
public import Balaban.Fluctuation.ExpSourceChart
public import Balaban.Fluctuation.StepComplexJointH
public import Balaban.Fluctuation.StepComplexOutAnalytic
public import Balaban.Fluctuation.Thm31CoeffB

/-!
# The observable ray at a free incoming datum

The zero-class composed observable along a free-datum ray is the old small solution's
site value. The incoming field is inherited at every point of the ray.
-/

@[expose] public section

namespace Balaban.Fluctuation.StepSetting.JointRep

open Balaban Balaban.Background Balaban.Multiscale Balaban.Localization
  Balaban.SmallField Balaban.SmallField.Def6 Filter Topology Matrix

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ eps pp : ℝ}
  {S : StepSetting d L N₁ m₁ k N ϱ} (Jr : S.JointRep eps pp)
  (H : StepSettingH S)
  {c BG κ Kc Cx c₂ BG₂ δ₁ δc : ℝ}

include Jr in
/-- At a free datum, the zero-class composed observable is the constant inherited field
plus the fluctuation response along the hat ray. -/
theorem McompAtC_zero_path_raw
    (hC : FlCore N S.G' (stepG d L N₁ m₁ k ϱ) S.a₁ S.ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
    (ha₁ : 0 < S.a₁) (HB : BgHyp d L (k + 1) ϱ (compWeight L S.a₁) S.ν)
    (hc7 : c7 d L N BG κ ≤ thm73C3 d L N) {R : ℝ} (hR : 2 ≤ R)
    (hsmR : 2 * (compC4 d * (bgK1 d L N * (xiC1 d * eps))) +
      5 * (R * δ₁) ≤ bgC1 d L N)
    (hRs : R * δ₁ ≤ deltaStar d L N)
    (hsmall : cK2 d L N * (R * δ₁) < bgC0 d L N / 2)
    (hnum : cK2 d L N * δ₁ ≤ c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8))
    (hnum' : cK2' d L N (famConst d L BG₂ κ) * δ₁ ≤
      c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8))
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    (hdm : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    {cψ : ℝ} (hcψ : 0 ≤ cψ)
    (hδ₁ : Real.sqrt N * (‖((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)‖ *
      (covSupConstC d L N (compWeight L S.a₁ k) κ * cψ)) < δ₁)
    (hpc : pp ≤ cψ) (hX : XiCData S.G' S.a S.ν (k + 1) 1 eps H.D')
    (g : Fld d L N₁ m₁ (k + 1) N) (y : CTorus d L N₁ m₁ (k + 1)) (i : Fin N)
    (x : S.E) {t : ℝ} (ht : |t| * ‖x‖ ≤ pp) :
    let ψ : ℝ → S.E → S.EC := fun t x =>
      (fun q =>
        (composeData (S.hG.precedes S.hG' (le_refl (k + 1))) S.a
          (bgFieldC S.G' S.a S.ν (bgC0 d L N) H.D') H.D').Ψ
            (unitRep (G' := S.G') q.1) q.2) +
        S.hatField (hatCovSqrt S.G' S.a₁ S.ν H.D') ((t : ℂ) • yhat x)
    McompAtC (zeroClass d L N₁ m₁ k N ϱ).m₀ (zeroClass d L N₁ m₁ k N ϱ).Tm
        S.a S.ν (Nat.le_succ k) (H.dataUCH (ψ t x)) g y i =
      svec (stepG d L N₁ m₁ k ϱ)
        ((S.hG.precedes S.hG' (le_refl (k + 1))).restrictφ
          (bgFieldC S.G' S.a S.ν (bgC0 d L N) H.D')) y i +
      svec (stepG d L N₁ m₁ k ϱ)
        (flFieldOne S.G' (stepG d L N₁ m₁ k ϱ) BG₂ κ S.a₁ S.ν H.D'
          (hatLift S.G' S.a₁ S.ν S.hG'
            ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) H.D'
              ((t : ℂ) • yhat x))) y i := by
  dsimp only
  have hz : ∀ p, ‖((t : ℂ) • yhat x) p‖ ≤ pp := smul_yhat_le ht
  have h1 := Balaban.Fluctuation.StepSetting.JointRep.FJ_sub_restrict_eq_flFieldOne Jr hC ha₁ HB hc7 hR hsmR hRs hsmall hnum hnum'
    hMX hdm hα hsm hcψ hδ₁ hpc hX hz
  have h2 := Jr.FJ_dataUCH H hX hz
  have hsub : ∀ (A B : (stepG d L N₁ m₁ k ϱ).Ω 1 × Fin N → ℂ),
      svec (stepG d L N₁ m₁ k ϱ) (A - B) y i =
        svec (stepG d L N₁ m₁ k ϱ) A y i - svec (stepG d L N₁ m₁ k ϱ) B y i := by
    intro A B
    by_cases hm : y ∈ (stepG d L N₁ m₁ k ϱ).Ω 1
    · rw [svec_of_mem (stepG d L N₁ m₁ k ϱ) _ ⟨y, hm⟩ i,
        svec_of_mem (stepG d L N₁ m₁ k ϱ) _ ⟨y, hm⟩ i,
        svec_of_mem (stepG d L N₁ m₁ k ϱ) _ ⟨y, hm⟩ i]
      rfl
    · rw [svec_of_not_mem (stepG d L N₁ m₁ k ϱ) _ hm i,
        svec_of_not_mem (stepG d L N₁ m₁ k ϱ) _ hm i,
        svec_of_not_mem (stepG d L N₁ m₁ k ϱ) _ hm i]
      simp
  have h3 := hsub (Jr.FJ (rawOf H.D', (t : ℂ) • yhat x)).1
    ((S.hG.precedes S.hG' (le_refl (k + 1))).restrictφ
      (bgFieldC S.G' S.a S.ν (bgC0 d L N) H.D'))
  rw [h1] at h3
  have h4 := McompAtC_zero_eq (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (N := N)
    (ϱ := ϱ) (zeroClass d L N₁ m₁ k N ϱ).m₀ S.a S.ν (K := k + 1) (j := k)
    (Nat.le_succ k) (H.dataUCH
      ((fun q =>
        (composeData (S.hG.precedes S.hG' (le_refl (k + 1))) S.a
          (bgFieldC S.G' S.a S.ν (bgC0 d L N) H.D') H.D').Ψ
            (unitRep (G' := S.G') q.1) q.2) +
        S.hatField (hatCovSqrt S.G' S.a₁ S.ν H.D') ((t : ℂ) • yhat x))) g y i
  refine h4.trans ?_
  rw [h2] at h3
  simp only at h3
  rw [h3]
  ring


include Jr in
/-- The observable ray derivative at a free incoming datum agrees with the derivative
of the zero-class composed observable. -/
theorem deriv_McompAtC_zero_raw     (hC : FlCore N S.G' (stepG d L N₁ m₁ k ϱ) S.a₁ S.ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
    (ha₁ : 0 < S.a₁) (HB : BgHyp d L (k + 1) ϱ (compWeight L S.a₁) S.ν)
    (hc7 : c7 d L N BG κ ≤ thm73C3 d L N) {R : ℝ} (hR : 2 ≤ R)
    (hsmR : 2 * (compC4 d * (bgK1 d L N * (xiC1 d * eps))) +
      5 * (R * δ₁) ≤ bgC1 d L N)
    (hRs : R * δ₁ ≤ deltaStar d L N)
    (hsmall : cK2 d L N * (R * δ₁) < bgC0 d L N / 2)
    (hnum : cK2 d L N * δ₁ ≤ c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8))
    (hnum' : cK2' d L N (famConst d L BG₂ κ) * δ₁ ≤
      c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8))
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    (hdm : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    {cψ : ℝ} (hcψ : 0 ≤ cψ)
    (hδ₁ : Real.sqrt N * (‖((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)‖ *
      (covSupConstC d L N (compWeight L S.a₁ k) κ * cψ)) < δ₁)
    (hpc : pp < cψ) (hX : XiCData S.G' S.a S.ν (k + 1) 1 eps H.D')

    (g : Fld d L N₁ m₁ (k + 1) N) (y : CTorus d L N₁ m₁ (k + 1)) (i : Fin N) (x : S.E)
    (hx : ‖x‖ < pp) {r : ℝ} (hr : r ∈ Set.Icc (0 : ℝ) 1) :
    let ψ : ℝ → S.E → S.EC := fun t x =>
      (fun q =>
        (composeData (S.hG.precedes S.hG' (le_refl (k + 1))) S.a
          (bgFieldC S.G' S.a S.ν (bgC0 d L N) H.D') H.D').Ψ
            (unitRep (G' := S.G') q.1) q.2) +
        S.hatField (hatCovSqrt S.G' S.a₁ S.ν H.D') ((t : ℂ) • yhat x)
    deriv (fun t : ℝ => McompAtC (zeroClass d L N₁ m₁ k N ϱ).m₀
        (zeroClass d L N₁ m₁ k N ϱ).Tm S.a S.ν (Nat.le_succ k) (H.dataUCH (ψ t x)) g y i) r =
      obsRayFun S (fun ψh => svec (stepG d L N₁ m₁ k ϱ)
        (flFieldOne S.G' (stepG d L N₁ m₁ k ϱ) BG₂ κ S.a₁ S.ν H.D'
          (hatLift S.G' S.a₁ S.ν S.hG' ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) H.D' ψh)) y i) x r := by
  dsimp only
  classical
  let ψ : ℝ → S.E → S.EC := fun t x =>
    (fun q =>
      (composeData (S.hG.precedes S.hG' (le_refl (k + 1))) S.a
        (bgFieldC S.G' S.a S.ν (bgC0 d L N) H.D') H.D').Ψ
          (unitRep (G' := S.G') q.1) q.2) +
      S.hatField (hatCovSqrt S.G' S.a₁ S.ν H.D') ((t : ℂ) • yhat x)
  set cc : ℂ := ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) with hcc
  set F : (S.U × Fin N → ℂ) → ℂ := fun ψh => svec (stepG d L N₁ m₁ k ϱ)
    (flFieldOne S.G' (stepG d L N₁ m₁ k ϱ) BG₂ κ S.a₁ S.ν H.D'
      (hatLift S.G' S.a₁ S.ν S.hG' cc H.D' ψh)) y i with hF
  set c0 : ℂ := svec (stepG d L N₁ m₁ k ϱ)
        ((S.hG.precedes S.hG' (le_refl (k + 1))).restrictφ
          (bgFieldC S.G' S.a S.ν (bgC0 d L N) H.D')) y i with hc0
  have hrx : |r| * ‖x‖ < pp := by
    rw [abs_of_nonneg hr.1]
    exact lt_of_le_of_lt (mul_le_of_le_one_left (norm_nonneg _) hr.2) hx
  have hev : ∀ᶠ t : ℝ in 𝓝 r, c0 + F ((t : ℂ) • yhat x) =
      McompAtC (zeroClass d L N₁ m₁ k N ϱ).m₀ (zeroClass d L N₁ m₁ k N ϱ).Tm S.a S.ν
        (Nat.le_succ k) (H.dataUCH (ψ t x)) g y i := by
    have hcont : ContinuousAt (fun t : ℝ => |t| * ‖x‖) r := by fun_prop
    filter_upwards [hcont.eventually_lt continuousAt_const hrx] with t ht
    exact (Jr.McompAtC_zero_path_raw H hC ha₁ HB hc7 hR hsmR hRs hsmall hnum hnum' hMX hdm hα hsm hcψ
      hδ₁ hpc.le hX g y i x ht.le).symm
  have hb : ∀ p, ‖((r : ℂ) * yhat x p)‖ < cψ := fun p => by
    have := smul_yhat_le (S := S) (pp := pp) (s := r) (x := x) hrx.le p
    simpa using lt_of_le_of_lt this hpc
  have hAn : AnalyticAt ℂ (fun l : ℂ => F (l • yhat x)) (r : ℂ) := by
    by_cases hm : y ∈ (stepG d L N₁ m₁ k ϱ).Ω 1
    · have e : (fun l : ℂ => F (l • yhat x)) = fun l : ℂ =>
          flFieldOne S.G' (stepG d L N₁ m₁ k ϱ) BG₂ κ S.a₁ S.ν H.D'
            (hatLift S.G' S.a₁ S.ν S.hG' cc H.D' (l • yhat x)) (⟨y, hm⟩, i) := by
        funext l; exact svec_of_mem (stepG d L N₁ m₁ k ϱ) _ ⟨y, hm⟩ i
      rw [e]
      exact analyticAt_flFieldOne_hatRay hC S.hk1 S.hG S.hG' ha₁ HB hc7 hR hsmR hRs hsmall
        hnum hnum' hMX hdm hα hsm cc hcψ hδ₁ hX (yhat x) hb (⟨y, hm⟩, i)
    · have e : (fun l : ℂ => F (l • yhat x)) = fun _ => 0 := by
        funext l; exact svec_of_not_mem (stepG d L N₁ m₁ k ϱ) _ hm i
      rw [e]
      exact analyticAt_const
  have hd : HasDerivAt (fun t : ℝ => c0 + F ((t : ℂ) • yhat x))
      (deriv (fun l : ℂ => F (l • yhat x)) (r : ℂ)) r :=
    (hAn.differentiableAt.hasDerivAt.const_add c0).comp_ofReal
  rw [← Filter.EventuallyEq.deriv_eq hev]
  exact hd.deriv


include Jr in
/-- The free-datum observable ray and the composed observable have the same integrand
on the fluctuation support. -/
theorem ae_deriv_McompAtC_zero_eq_obsRayFun_raw     (hC : FlCore N S.G' (stepG d L N₁ m₁ k ϱ) S.a₁ S.ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
    (ha₁ : 0 < S.a₁) (HB : BgHyp d L (k + 1) ϱ (compWeight L S.a₁) S.ν)
    (hc7 : c7 d L N BG κ ≤ thm73C3 d L N) {R : ℝ} (hR : 2 ≤ R)
    (hsmR : 2 * (compC4 d * (bgK1 d L N * (xiC1 d * eps))) +
      5 * (R * δ₁) ≤ bgC1 d L N)
    (hRs : R * δ₁ ≤ deltaStar d L N)
    (hsmall : cK2 d L N * (R * δ₁) < bgC0 d L N / 2)
    (hnum : cK2 d L N * δ₁ ≤ c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8))
    (hnum' : cK2' d L N (famConst d L BG₂ κ) * δ₁ ≤
      c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8))
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    (hdm : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    {cψ : ℝ} (hcψ : 0 ≤ cψ)
    (hδ₁ : Real.sqrt N * (‖((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)‖ *
      (covSupConstC d L N (compWeight L S.a₁ k) κ * cψ)) < δ₁)
    (hpc : pp < cψ) (hX : XiCData S.G' S.a S.ν (k + 1) 1 eps H.D')

    (hp₁ : 0 < S.p₁) (hlt : S.p₁ < pp)
    (g : Fld d L N₁ m₁ (k + 1) N) (y : CTorus d L N₁ m₁ (k + 1)) (i : Fin N) {r : ℝ}
    (hr : r ∈ Set.Icc (0 : ℝ) 1) :
    let ψ : ℝ → S.E → S.EC := fun t x =>
      (fun q =>
        (composeData (S.hG.precedes S.hG' (le_refl (k + 1))) S.a
          (bgFieldC S.G' S.a S.ν (bgC0 d L N) H.D') H.D').Ψ
            (unitRep (G' := S.G') q.1) q.2) +
        S.hatField (hatCovSqrt S.G' S.a₁ S.ν H.D') ((t : ℂ) • yhat x)
    ∀ᵐ x ∂S.nuFl,
      obsRayFun S (fun ψh => svec (stepG d L N₁ m₁ k ϱ)
        (flFieldOne S.G' (stepG d L N₁ m₁ k ϱ) BG₂ κ S.a₁ S.ν H.D'
          (hatLift S.G' S.a₁ S.ν S.hG' ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) H.D' ψh)) y i) x r =
      deriv (fun t : ℝ => McompAtC (zeroClass d L N₁ m₁ k N ϱ).m₀
        (zeroClass d L N₁ m₁ k N ϱ).Tm S.a S.ν (Nat.le_succ k) (H.dataUCH (ψ t x)) g y i) r := by
  dsimp only
  filter_upwards [S.ae_norm_nuFl hp₁] with x hx
  have hxn : ‖x‖ < pp := lt_of_le_of_lt
    ((pi_norm_le_iff_of_nonneg hp₁.le).2 fun u => (hx u).le) hlt
  exact (Jr.deriv_McompAtC_zero_raw H hC ha₁ HB hc7 hR hsmR hRs hsmall hnum hnum' hMX hdm hα hsm hcψ
    hδ₁ hpc hX g y i x hxn hr).symm

/-- The coefficient sum of an observable marks record at a free datum has the raw
joint-representation value, once its ray integrand is identified. -/
theorem obsCoeff_sum_eq_raw_M0J_of_ray
    (C : StepClass d L N₁ m₁ k N ϱ)
    (hp₁ : 0 < S.p₁) (hle : S.p₁ ≤ pp)
    (hX : XiCData S.G' S.a S.ν (k + 1) 1 eps H.D')
    (g : Fld d L N₁ m₁ (k + 1) N)
    (y : CTorus d L N₁ m₁ (k + 1)) (i : Fin N)
    {m₀ : ℕ} (BS : BlockSplit S m₀)
    {bx : CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) m₀ (k + 1) Set.univ}
    (I : ObsMarks S.nuFl BS
      (fun t x => Jr.W1 C (rawOf H.D', yhat x) +
        Jr.W2 C g (rawOf H.D', (t : ℂ) • yhat x))
      (fun t x => obsRayFun S (fun ψh =>
        svec (stepG d L N₁ m₁ k ϱ)
          (flFieldOne S.G' (stepG d L N₁ m₁ k ϱ) BG₂ κ S.a₁ S.ν H.D'
            (hatLift S.G' S.a₁ S.ν S.hG'
              ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) H.D' ψh)) y i) x t) bx)
    (hRay : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 → ∀ᵐ x ∂S.nuFl,
      obsRayFun S (fun ψh =>
        svec (stepG d L N₁ m₁ k ϱ)
          (flFieldOne S.G' (stepG d L N₁ m₁ k ϱ) BG₂ κ S.a₁ S.ν H.D'
            (hatLift S.G' S.a₁ S.ν S.hG'
              ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) H.D' ψh)) y i) x t =
      deriv (fun r : ℝ => McompAtC C.m₀ C.Tm S.a S.ν (Nat.le_succ k)
        (H.dataUCH
          ((fun q =>
            (composeData (S.hG.precedes S.hG' (le_refl (k + 1))) S.a
              (bgFieldC S.G' S.a S.ν (bgC0 d L N) H.D') H.D').Ψ
                (unitRep (G' := S.G') q.1) q.2) +
            S.hatField (hatCovSqrt S.G' S.a₁ S.ν H.D') ((r : ℂ) • yhat x))) g y i) t) :
    ((S.betaU ^ (1 / 2 : ℝ) : ℝ) : ℂ) * ∑ T, obsCoeff I T =
      ((S.betaU ^ (1 / 2 : ℝ) : ℝ) : ℂ) *
        S.avgJ (Jr.W1 C) (Jr.W2 C g) (Jr.McJ C g y i) (rawOf H.D') := by
  have hval := (thm31b_coeff I (κb := min I.κh I.κ' - I.κ0 - 1) le_rfl).1
  have hM := Jr.M0J_dataUCH (C := C) hp₁ hle H hX g y i
  dsimp only at hM
  rw [← hval]
  rw [hM]
  unfold interpAvg avgFun partFun avgFun₂ partFun₂
  congr 1
  apply intervalIntegral.integral_congr
  intro t ht
  dsimp only
  congr 1
  apply MeasureTheory.integral_congr_ae
  filter_upwards [hRay t (by simpa only [Set.uIcc_of_le zero_le_one] using ht)] with x hx
  rw [hx]


/-- At any chart datum, an observable marks record for the zero class has the raw
M0 coefficient sum. Its activity clause is the free-datum activity identity. -/
theorem obsCoeff_sum_eq_raw_M0J_zeroClass
    (hC : FlCore N S.G' (stepG d L N₁ m₁ k ϱ) S.a₁ S.ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
    (ha₁ : 0 < S.a₁) (HB : BgHyp d L (k + 1) ϱ (compWeight L S.a₁) S.ν)
    (hc7 : c7 d L N BG κ ≤ thm73C3 d L N) {R : ℝ} (hR : 2 ≤ R)
    (hsmR : 2 * (compC4 d * (bgK1 d L N * (xiC1 d * eps))) +
      5 * (R * δ₁) ≤ bgC1 d L N)
    (hRs : R * δ₁ ≤ deltaStar d L N)
    (hsmall : cK2 d L N * (R * δ₁) < bgC0 d L N / 2)
    (hnum : cK2 d L N * δ₁ ≤ c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8))
    (hnum' : cK2' d L N (famConst d L BG₂ κ) * δ₁ ≤
      c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8))
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    (hdm : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    {cψ : ℝ} (hcψ : 0 ≤ cψ)
    (hδ₁ : Real.sqrt N * (‖((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)‖ *
      (covSupConstC d L N (compWeight L S.a₁ k) κ * cψ)) < δ₁)
    (hpc : pp < cψ) (hX : XiCData S.G' S.a S.ν (k + 1) 1 eps H.D')
    (hp₁ : 0 < S.p₁) (hlt : S.p₁ < pp)
    (g : Fld d L N₁ m₁ (k + 1) N)
    (y : CTorus d L N₁ m₁ (k + 1)) (i : Fin N)
    {m₀ : ℕ} (BS : BlockSplit S m₀)
    {bx : CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) m₀ (k + 1) Set.univ}
    (I : ObsMarks S.nuFl BS
      (fun t x => Jr.W1 (zeroClass d L N₁ m₁ k N ϱ) (rawOf H.D', yhat x) +
        Jr.W2 (zeroClass d L N₁ m₁ k N ϱ) g (rawOf H.D', (t : ℂ) • yhat x))
      (fun t x => obsRayFun S (fun ψh =>
        svec (stepG d L N₁ m₁ k ϱ)
          (flFieldOne S.G' (stepG d L N₁ m₁ k ϱ) BG₂ κ S.a₁ S.ν H.D'
            (hatLift S.G' S.a₁ S.ν S.hG'
              ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) H.D' ψh)) y i) x t) bx) :
    ((S.betaU ^ (1 / 2 : ℝ) : ℝ) : ℂ) * ∑ T, obsCoeff I T =
      ((S.betaU ^ (1 / 2 : ℝ) : ℝ) : ℂ) *
        S.avgJ (Jr.W1 (zeroClass d L N₁ m₁ k N ϱ))
          (Jr.W2 (zeroClass d L N₁ m₁ k N ϱ) g)
          (Jr.McJ (zeroClass d L N₁ m₁ k N ϱ) g y i) (rawOf H.D') := by
  exact Jr.obsCoeff_sum_eq_raw_M0J_of_ray H (zeroClass d L N₁ m₁ k N ϱ)
    hp₁ hlt.le hX g y i BS I
    (fun t ht => Jr.ae_deriv_McompAtC_zero_eq_obsRayFun_raw H hC ha₁ HB hc7 hR hsmR
      hRs hsmall hnum hnum' hMX hdm hα hsm hcψ hδ₁ hpc hX hp₁ hlt g y i ht)

end Balaban.Fluctuation.StepSetting.JointRep
