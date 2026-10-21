/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.HoleStepAnalytic

/-!
# The composed field is analytic in the datum of the step too (clause `analytic` of (D7))

`Fluctuation.HoleStepAnalytic` proves the composed field analytic in the localization vectors and the
fluctuation field for a fixed datum `D'` of the step.  Here the datum varies analytically with a
parameter `e` (`HoleStep.withD`; for the local step of the history the datum is the mixed lift of the
multiscale field, which is linear in the field): `Dec2.analyticAt_decBg_family`,
`HoleStep.analyticAt_composed_family`, `HoleStep.analyticOnNhd_oldInterp_family`, and the parameter
dependence of the coefficient of Lemma AE, `HoleStep.analyticOnNhd_oldCoef_family`.
-/

@[expose] public section

namespace Balaban.Localization.Dec2

open Balaban Balaban.Multiscale Balaban.Background

variable {d L N₁ m₁ K N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
  {C : DecCover d L N₁ m₁ K} {H : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {a : ℕ → ℝ} {ν Kc Cx : ℝ}

/-- **The decoupled background is analytic in the datum and the parameters** (Theorem I-4b (i)). -/
theorem analyticAt_decBg_family {c BG : ℝ} (hS : DecSpecs d L Kc Cx c BG)
    (S : CoverBase C H a ν Kc Cx) (HB : BgHyp d L K ϱ a ν) {κ : ℝ} (hκ : 0 ≤ κ)
    (hM : c * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δ : ℝ} (hδ0 : 0 < δ)
    (hε : δ ≤ bgC0 d L N) (hδ : δ ≤ c7 d L N BG κ)
    (hνε : ν * ((L : ℝ) ^ K) ^ 2 * δ ^ 2 ≤ δ ^ 2)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {e₀ : E} {Uo : Set E}
    (hUo : Uo ∈ nhds e₀) {D : E → BgData H N} (hD : ∀ e ∈ Uo, InDomainC H ν δ δ (D e))
    {f : E → DecParams C} (hf : ∀ P, AnalyticAt ℂ (fun e => f e P) e₀)
    (hfv : ∀ e ∈ Uo, ∀ P, ‖f e P‖ < Real.exp κ) (hΨ : ∀ x i, AnalyticAt ℂ (fun e => (D e).Ψ x i) e₀)
    (hh : ∀ x i, AnalyticAt ℂ (fun e => (D e).h x i) e₀) :
    AnalyticAt ℂ (fun e => (decBgField C H a ν (rho4 d L N BG κ) (f e) (D e),
      decBgMult C H a ν (rho4 d L N BG κ) (f e) (D e))) e₀ := by
  obtain ⟨F, hFan, hF⟩ := i4b_analytic hS S HB hκ hM
  have hU : ∀ e ∈ Uo, InUnionDomainC H (bgC0 d L N) (c7 d L N BG κ) ν (D e) :=
    fun e he => ⟨δ, δ, hδ0, le_rfl, hε, hδ, hνε, hD e he⟩
  have hv : AnalyticAt ℂ (fun e => (f e, ((D e).Ψ, (D e).h))) e₀ := by
    refine AnalyticAt.prod (analyticAt_pi_iff.2 hf) (AnalyticAt.prod ?_ ?_)
    · exact analyticAt_pi_iff.2 fun x => analyticAt_pi_iff.2 fun i => hΨ x i
    · exact analyticAt_pi_iff.2 fun x => analyticAt_pi_iff.2 fun i => hh x i
  have hA : AnalyticAt ℂ (fun e => F (f e, ((D e).Ψ, (D e).h))) e₀ :=
    (hFan _ ⟨hfv e₀ (mem_of_mem_nhds hUo), D e₀, hU e₀ (mem_of_mem_nhds hUo), rfl⟩).comp_of_eq hv rfl
  refine hA.congr ?_
  filter_upwards [hUo] with e he
  obtain ⟨φ, α, hI, hu, -⟩ := i4b_exists_unique hS S HB hκ hM (fun P => (hfv e he P).le) hδ0
    le_rfl hε hδ hνε (hD e he)
  obtain ⟨h1, h2⟩ := decBg_eq hI hu
  rw [h1, h2, hF (f e) (D e) (hfv e he) (hU e he) φ α hI]

end Balaban.Localization.Dec2

namespace Balaban.Fluctuation

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization Balaban.LargeField
  Balaban.SmallField

namespace HoleStep

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ ϱ' : ℝ}
  (S : HoleStep d L N₁ m₁ k N ϱ ϱ')

/-- **The step with the datum replaced** (the field `h₀` of the step fixed). -/
abbrev withD (D : BgData S.G' N) (hh : ∀ x ∈ S.G'.Ω 1, ∀ i, D.h x i = (S.h₀ i : ℂ)) :
    HoleStep d L N₁ m₁ k N ϱ ϱ' :=
  { S with D' := D, hh₀ := hh }

/-- **The composed field is analytic in the datum, the localization vectors and the fluctuation
field** (Theorems I-4b (i), I-4c (iii)): as `analyticAt_composed` with the datum `D'` of the step
replaced by a family `D e` with analytic values, in `Ψ̃^c(δ, δ)` on a neighbourhood of `e₀`. -/
theorem analyticAt_composed_family {Kc Cx Cx₂ c BG δ δc : ℝ} (hS : Dec2.DecSpecs d L Kc Cx c BG)
    (Sb : Dec2.CoverBase (coverOf S.G') S.G' (compWeight L S.a₁) S.ν Kc Cx)
    (SX : Dec2.XCover (coverOf S.G') S.G' (compWeight L S.a₁) S.a₁ S.ν Cx₂) (hCx₂ : 0 ≤ Cx₂)
    (HB : BgHyp d L (k + 1) ϱ' (compWeight L S.a₁) S.ν) {κ : ℝ} (hκ : 0 ≤ κ)
    (hM : c * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    (hMX : Dec2.cstarX d L Cx₂ * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    (hδ0 : 0 < δ) (hε : δ ≤ bgC0 d L N) (hδ : δ ≤ c7 d L N BG κ)
    (hνε : S.ν * ((L : ℝ) ^ (k + 1)) ^ 2 * δ ^ 2 ≤ δ ^ 2)
    (hphi : 3 * δ + K4 d L N BG κ * δ < 1 / 2)
    (hmarD : K4 d L N BG κ * δ + 2 * δ + K4 d L N BG κ * δ * (K4 d L N BG κ * δ + 2 * (1 + 3 * δ))
      < δc)
    (hαD : K4 d L N BG κ * δ < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {e₀ : E} {Uo : Set E}
    (hUo : Uo ∈ nhds e₀) {D : E → BgData S.G' N}
    (hh : ∀ e, ∀ x ∈ S.G'.Ω 1, ∀ i, (D e).h x i = (S.h₀ i : ℂ))
    (hD : ∀ e ∈ Uo, InDomainC S.G' S.ν δ δ (D e))
    (hΨ : ∀ x i, AnalyticAt ℂ (fun e => (D e).Ψ x i) e₀)
    (hH : ∀ x i, AnalyticAt ℂ (fun e => (D e).h x i) e₀)
    {f : E → S.U → Dec2.DecParams (coverOf S.G')}
    (hf : ∀ b P, AnalyticAt ℂ (fun e => f e b P) e₀)
    (hfv : ∀ e ∈ Uo, ∀ b P, ‖f e b P‖ < Real.exp κ)
    {ψhat : E → S.U → Fin N → ℂ} (hψ : ∀ b i, AnalyticAt ℂ (fun e => ψhat e b i) e₀)
    (b : S.U) (i : Fin N) :
    AnalyticAt ℂ (fun e => (S.withD (D e) (hh e)).composed (coverOf S.G')
      (rho4 d L N BG κ) (f e) (ψhat e) b i) e₀ := by
  have hv : AnalyticAt ℂ (fun e => f e b) e₀ := analyticAt_pi_iff.2 (hf b)
  have hdec := Dec2.analyticAt_decBg_family hS Sb HB hκ hM hδ0 hε hδ hνε hUo hD
    (f := fun e => f e b) (hf b) (fun e he P => hfv e he b P) hΨ hH
  have hφ : ∀ (y : S.G'.Ω 1) (j : Fin N), AnalyticAt ℂ
      (fun e => Dec2.decBgField (coverOf S.G') S.G' S.a S.ν (rho4 d L N BG κ) (f e b) (D e)
        (y, j)) e₀ :=
    fun y j => analyticAt_pi_iff.1 (analyticAt_fst.comp hdec) (y, j)
  have hα : ∀ w : S.G'.Ω 1, AnalyticAt ℂ
      (fun e => Dec2.decBgMult (coverOf S.G') S.G' S.a S.ν (rho4 d L N BG κ) (f e b) (D e) w) e₀ :=
    fun w => analyticAt_pi_iff.1 (analyticAt_snd.comp hdec) w
  have hpsi : AnalyticAt ℂ (fun e => (S.withD (D e) (hh e)).psiLoc (coverOf S.G')
      (rho4 d L N BG κ) (f e) b i) e₀ :=
    an_composeField S.G S.G' S.a
      (fun e => Dec2.decBgField (coverOf S.G') S.G' S.a S.ν (rho4 d L N BG κ) (f e b) (D e))
      (fun e => (D e).Ψ) hφ hΨ (unitRep b) i
  obtain ⟨φ₀, α₀, hI, hu, -, -, hbb⟩ := Dec2.i4b_exists_unique hS Sb HB hκ hM
    (fun P => (hfv e₀ (mem_of_mem_nhds hUo) b P).le) hδ0 le_rfl hε hδ hνε
    (hD e₀ (mem_of_mem_nhds hUo))
  obtain ⟨hφe, hαe⟩ := Dec2.decBg_eq hI hu
  have hd0 : 0 < d := by have := HB.hd; omega
  have hK4 : 0 < K4 d L N BG κ := K4_pos hS.fam.2.1 hd0
  have hB4 : 0 < K4 d L N BG κ * δ := mul_pos hK4 hδ0
  have hdom : (f e₀ b, (barField S.G' (D e₀).Ψ
      (Dec2.decBgField (coverOf S.G') S.G' S.a S.ν (rho4 d L N BG κ) (f e₀ b) (D e₀)),
      Dec2.decBgMult (coverOf S.G') S.G' S.a S.ν (rho4 d L N BG κ) (f e₀ b) (D e₀))) ∈
        DecDom S.G' N κ δc := by
    rw [hφe, hαe]
    exact decDom_of_bgBounds (c := K4 d L N BG κ * δ) hδ0.le hB4.le (hD e₀ (mem_of_mem_nhds hUo))
      hbb (by linarith) hmarD hαD (hfv e₀ (mem_of_mem_nhds hUo) b)
  have hδc : 0 ≤ δc := by nlinarith
  have hU : IsUnitLattice S.G' (unitQ S.G') (unitP S.G') :=
    (isUnitLatticeB_unit (G := S.G')).toIsUnitLattice
  have hdata : AnalyticAt ℂ (fun e => (f e b,
      (barField S.G' (D e).Ψ
        (Dec2.decBgField (coverOf S.G') S.G' S.a S.ν (rho4 d L N BG κ) (f e b) (D e)),
        Dec2.decBgMult (coverOf S.G') S.G' S.a S.ν (rho4 d L N BG κ) (f e b) (D e)))) e₀ := by
    refine hv.prod (AnalyticAt.prod ?_ (analyticAt_pi_iff.2 hα))
    exact analyticAt_pi_iff.2 fun x => analyticAt_pi_iff.2 fun j =>
      an_barField (fun e => (D e).Ψ) _ hΨ hφ x j
  have hcov : ∀ q : S.U × Fin N, AnalyticAt ℂ
      (fun e => (S.withD (D e) (hh e)).covSqrtAt (coverOf S.G') (rho4 d L N BG κ) (f e b) (b, i)
        q) e₀ := by
    intro q
    have h1 := (analyticOnNhd_decCovSqrt_entry_cover SX hCx₂ hκ hMX hδc hsm hU (b, i) q _
      hdom).comp_of_eq hdata rfl
    refine h1.congr (Filter.Eventually.of_forall fun e => ?_)
    simp only [covSqrtAt]
    rw [decCovSqrt_svec_eq_barField (coverOf S.G') S.a S.a₁ S.ν _ _ (D e).Ψ]
    rfl
  have hshift : AnalyticAt ℂ
      (fun e => (S.withD (D e) (hh e)).shiftLoc (coverOf S.G') (rho4 d L N BG κ) (f e) (ψhat e)
        b i) e₀ := by
    unfold shiftLoc
    have hsum : AnalyticAt ℂ (fun e => ∑ q : S.U × Fin N,
        (S.withD (D e) (hh e)).covSqrtAt (coverOf S.G') (rho4 d L N BG κ) (f e b) (b, i) q *
          ψhat e q.1 q.2) e₀ :=
      Finset.analyticAt_fun_sum _ fun q _ => (hcov q).mul (hψ q.1 q.2)
    exact (analyticAt_const (v := ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ))).mul hsum
  exact hpsi.add hshift

end HoleStep

end Balaban.Fluctuation
