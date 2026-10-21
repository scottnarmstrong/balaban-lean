/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.HoleStepStanding
public import Balaban.Fluctuation.RenormExpDiff
public import Balaban.Localization.DecoupledCovAnalyticFull
public import Balaban.Localization.Decoupled2SolveAnalytic

/-!
# The composed field of the step on a region is analytic in the parameters (I-4b, I-4c)

For the step on a region with the pair `(coverOf G′, G′)` (reading HS-1, and HS-1′ for a restricted
step), the datum in the domain `Ψ̃^c(δ, δ)` of Theorem I-4b and the numerical conditions of
Theorems I-4b and I-4c (those of `standing_of_inDomainC`):

* `Dec2.analyticOnNhd_decBg`: the decoupled background `(φ_k(s), α_k(s))` is analytic in `s` on the
  open polydisc `|s_P| < e^κ` (Theorem I-4b (i), `Dec2.i4b_analytic`, with the uniqueness of
  `Dec2.i4b_exists_unique`);
* `decCovSqrt_svec_eq_barField`: the decoupled covariance root sees the field only on `Ω₁`;
* `HoleStep.analyticAt_composed`: **the composed field of P5 (2.39) is analytic** in any analytic
  family of localization vectors with entries in the open polydisc (Theorem I-4c (iii),
  `analyticOnNhd_decCovSqrt_entry_cover`, for the covariance root; `an_composeField` for the
  composition with `G`);
* `HoleStep.analyticOnNhd_oldInterp_out`, `HoleStep.analyticOnNhd_oldInterp`: **the interpolated old
  term `F_X(s)` is analytic**, jointly in the fixed fluctuation field and the parameters on
  `U × polydisc` (radius `e^{κ₁}`, `κ₁ ≤ κ`, `κ > 0`), and in the parameters alone (the hypothesis
  `hana` of `sum_oldCoef_eq_of_analytic`), when the old term is analytic at the values of the
  composed field there.
-/

@[expose] public section

namespace Balaban.Localization.Dec2

open Balaban Balaban.Multiscale Balaban.Background

variable {d L N₁ m₁ K N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
  {C : DecCover d L N₁ m₁ K} {H : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {a : ℕ → ℝ} {ν Kc Cx : ℝ}

/-- **The decoupled background is analytic in the parameters** (Theorem I-4b (i)): for a datum in
`Ψ̃^c(δ, δ)`, `s ↦ (φ_k(s), α_k(s))` is analytic on the open polydisc `|s_P| < e^κ`. -/
theorem analyticOnNhd_decBg {c BG : ℝ} (hS : DecSpecs d L Kc Cx c BG) (S : CoverBase C H a ν Kc Cx)
    (HB : BgHyp d L K ϱ a ν) {κ : ℝ} (hκ : 0 ≤ κ) (hM : c * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    {δ : ℝ} (hδ0 : 0 < δ) (hε : δ ≤ bgC0 d L N) (hδ : δ ≤ c7 d L N BG κ)
    (hνε : ν * ((L : ℝ) ^ K) ^ 2 * δ ^ 2 ≤ δ ^ 2) {D : BgData H N} (hD : InDomainC H ν δ δ D) :
    AnalyticOnNhd ℂ (fun s : DecParams C => (decBgField C H a ν (rho4 d L N BG κ) s D,
      decBgMult C H a ν (rho4 d L N BG κ) s D)) {s | ∀ P, ‖s P‖ < Real.exp κ} := by
  obtain ⟨F, hFan, hF⟩ := i4b_analytic hS S HB hκ hM
  have hU : InUnionDomainC H (bgC0 d L N) (c7 d L N BG κ) ν D :=
    ⟨δ, δ, hδ0, le_rfl, hε, hδ, hνε, hD⟩
  have heq : ∀ s : DecParams C, (∀ P, ‖s P‖ < Real.exp κ) →
      (decBgField C H a ν (rho4 d L N BG κ) s D, decBgMult C H a ν (rho4 d L N BG κ) s D) =
        F (s, (D.Ψ, D.h)) := by
    intro s hs
    obtain ⟨φ, α, hI, hu, -⟩ := i4b_exists_unique hS S HB hκ hM (fun P => (hs P).le) hδ0 le_rfl
      hε hδ hνε hD
    obtain ⟨h1, h2⟩ := decBg_eq hI hu
    rw [h1, h2, hF s D hs hU φ α hI]
  intro s hs
  have hA : AnalyticAt ℂ (fun s' : DecParams C => F (s', (D.Ψ, D.h))) s :=
    (hFan (s, (D.Ψ, D.h)) ⟨hs, D, hU, rfl⟩).comp_of_eq (analyticAt_id.prod analyticAt_const) rfl
  refine hA.congr ?_
  filter_upwards [isOpen_param_lt.mem_nhds hs] with s' hs'
  exact (heq s' hs').symm

end Balaban.Localization.Dec2

namespace Balaban.Fluctuation

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization Balaban.LargeField
  Balaban.SmallField

section Field

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}
  {G : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}

/-- The decoupled covariance root sees the field only on `Ω₁`: the zero extension and the extension
by the data give the same matrix. -/
theorem decCovSqrt_svec_eq_barField (C : DecCover d L N₁ m₁ (k + 1)) (a : ℕ → ℝ) (aT ν : ℝ)
    (α : G.Ω 1 → ℂ) (s : ℕ × CTorus d L N₁ m₁ (k + 1) → ℂ)
    (Ψ : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) (φ : G.Ω 1 × Fin N → ℂ)
    {κι : Type*} [Fintype κι] [DecidableEq κι] (Q : Matrix κι (G.Ω 1) ℂ) (P : Matrix κι κι ℂ) :
    Dec2.decCovSqrt C G a aT ν α s (svec G φ) Q P =
      Dec2.decCovSqrt C G a aT ν α s (barField G Ψ φ) Q P := by
  have h : restrictField G (svec G φ) = restrictField G (barField G Ψ φ) := by
    funext y i
    simp only [restrictField]
    rw [svec_of_mem G φ y i]
    simp [barField, y.2]
  have h2 : Dec2.decSqrtInt C G a aT ν α s (svec G φ) Q P =
      Dec2.decSqrtInt C G a aT ν α s (barField G Ψ φ) Q P := by
    funext x
    simp only [Dec2.decSqrtInt, Dec2.decCov, Dec2.decPi, Dec2.decM, Dec2.decN, h]
  unfold Dec2.decCovSqrt
  rw [h2]

end Field

namespace HoleStep

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ ϱ' : ℝ}
  (S : HoleStep d L N₁ m₁ k N ϱ ϱ')

/-- **The composed field of P5 (2.39) is analytic in the localization vectors** (Theorems I-4b (i),
I-4c (iii)): for the pair `(coverOf G′, G′)` with the standing conditions of
`standing_of_inDomainC`, the datum in `Ψ̃^c(δ, δ)`, and a family `f` of localization vectors
analytic at `e₀` with entries in the open polydisc `|s_P| < e^κ` there, and a family of fluctuation
fields analytic at `e₀`, every coordinate of the composed field is analytic at `e₀`. -/
theorem analyticAt_composed {Kc Cx Cx₂ c BG δ δc : ℝ} (hS : Dec2.DecSpecs d L Kc Cx c BG)
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
    (hD : InDomainC S.G' S.ν δ δ S.D')
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {f : E → S.U → Dec2.DecParams (coverOf S.G')} {e₀ : E}
    (hf : ∀ b P, AnalyticAt ℂ (fun e => f e b P) e₀) (hfv : ∀ b P, ‖f e₀ b P‖ < Real.exp κ)
    {ψhat : E → S.U → Fin N → ℂ} (hψ : ∀ b i, AnalyticAt ℂ (fun e => ψhat e b i) e₀)
    (b : S.U) (i : Fin N) :
    AnalyticAt ℂ (fun e => S.composed (coverOf S.G') (rho4 d L N BG κ) (f e) (ψhat e) b i) e₀ := by
  have hv : AnalyticAt ℂ (fun e => f e b) e₀ := analyticAt_pi_iff.2 (hf b)
  have hdec := (Dec2.analyticOnNhd_decBg hS Sb HB hκ hM hδ0 hε hδ hνε hD (f e₀ b) (hfv b)).comp_of_eq
    hv rfl
  have hφ : ∀ (y : S.G'.Ω 1) (j : Fin N), AnalyticAt ℂ
      (fun e => Dec2.decBgField (coverOf S.G') S.G' S.a S.ν (rho4 d L N BG κ) (f e b) S.D' (y, j)) e₀ :=
    fun y j => analyticAt_pi_iff.1 (analyticAt_fst.comp hdec) (y, j)
  have hα : ∀ w : S.G'.Ω 1, AnalyticAt ℂ
      (fun e => Dec2.decBgMult (coverOf S.G') S.G' S.a S.ν (rho4 d L N BG κ) (f e b) S.D' w) e₀ :=
    fun w => analyticAt_pi_iff.1 (analyticAt_snd.comp hdec) w
  -- the localized approximate minimum
  have hpsi : AnalyticAt ℂ (fun e => S.psiLoc (coverOf S.G') (rho4 d L N BG κ) (f e) b i) e₀ :=
    an_composeField S.G S.G' S.a (fun e => Dec2.decBgField (coverOf S.G') S.G' S.a S.ν (rho4 d L N BG κ) (f e b) S.D')
      (fun _ => S.D'.Ψ) hφ (fun _ _ => analyticAt_const) (unitRep b) i
  -- the covariance root
  obtain ⟨φ₀, α₀, hI, hu, -, -, hbb⟩ := Dec2.i4b_exists_unique hS Sb HB hκ hM
    (fun P => (hfv b P).le) hδ0 le_rfl hε hδ hνε hD
  obtain ⟨hφe, hαe⟩ := Dec2.decBg_eq hI hu
  have hd0 : 0 < d := by have := HB.hd; omega
  have hK4 : 0 < K4 d L N BG κ := K4_pos hS.fam.2.1 hd0
  have hB4 : 0 < K4 d L N BG κ * δ := mul_pos hK4 hδ0
  have hdom : (f e₀ b, (barField S.G' S.D'.Ψ (Dec2.decBgField (coverOf S.G') S.G' S.a S.ν (rho4 d L N BG κ) (f e₀ b) S.D'),
      Dec2.decBgMult (coverOf S.G') S.G' S.a S.ν (rho4 d L N BG κ) (f e₀ b) S.D')) ∈ DecDom S.G' N κ δc := by
    rw [hφe, hαe]
    exact decDom_of_bgBounds (c := K4 d L N BG κ * δ) hδ0.le hB4.le hD hbb (by linarith) hmarD hαD
      (hfv b)
  have hδc : 0 ≤ δc := by nlinarith
  have hU : IsUnitLattice S.G' (unitQ S.G') (unitP S.G') := (isUnitLatticeB_unit (G := S.G')).toIsUnitLattice
  have hdata : AnalyticAt ℂ (fun e => (f e b,
      (barField S.G' S.D'.Ψ (Dec2.decBgField (coverOf S.G') S.G' S.a S.ν (rho4 d L N BG κ) (f e b) S.D'),
        Dec2.decBgMult (coverOf S.G') S.G' S.a S.ν (rho4 d L N BG κ) (f e b) S.D'))) e₀ := by
    refine hv.prod (AnalyticAt.prod ?_ (analyticAt_pi_iff.2 hα))
    exact analyticAt_pi_iff.2 fun x => analyticAt_pi_iff.2 fun j =>
      an_barField (fun _ => S.D'.Ψ) _ (fun _ _ => analyticAt_const) hφ x j
  have hcov : ∀ q : S.U × Fin N, AnalyticAt ℂ
      (fun e => S.covSqrtAt (coverOf S.G') (rho4 d L N BG κ) (f e b) (b, i) q) e₀ := by
    intro q
    have h1 := (analyticOnNhd_decCovSqrt_entry_cover SX hCx₂ hκ hMX hδc hsm hU (b, i) q _
      hdom).comp_of_eq hdata rfl
    refine h1.congr (Filter.Eventually.of_forall fun e => ?_)
    simp only [covSqrtAt]
    rw [decCovSqrt_svec_eq_barField (coverOf S.G') S.a S.a₁ S.ν _ _ S.D'.Ψ]
    rfl
  have hshift : AnalyticAt ℂ
      (fun e => S.shiftLoc (coverOf S.G') (rho4 d L N BG κ) (f e) (ψhat e) b i) e₀ := by
    unfold shiftLoc
    exact analyticAt_const.mul (Finset.analyticAt_fun_sum _ fun q _ => (hcov q).mul (hψ q.1 q.2))
  exact hpsi.add hshift

/-- **The interpolated old term is jointly analytic in the fluctuation field and the parameters**
(Theorems I-4b (i), I-4c (iii)): with the standing conditions of `analyticAt_composed`, `κ > 0` and
`κ₁ ≤ κ`, if the old term `B` is analytic at the composed field for every fixed field `ψout ∈ U` and
every localization vector of the polydisc of radius `e^{κ₁}`, then `(ψout, s) ↦ F_X(s)` is analytic
on `U × polydisc`. -/
theorem analyticOnNhd_oldInterp_out {Kc Cx Cx₂ c BG δ δc : ℝ} (hS : Dec2.DecSpecs d L Kc Cx c BG)
    (Sb : Dec2.CoverBase (coverOf S.G') S.G' (compWeight L S.a₁) S.ν Kc Cx)
    (SX : Dec2.XCover (coverOf S.G') S.G' (compWeight L S.a₁) S.a₁ S.ν Cx₂) (hCx₂ : 0 ≤ Cx₂)
    (HB : BgHyp d L (k + 1) ϱ' (compWeight L S.a₁) S.ν) {κ : ℝ} (hκ : 0 < κ)
    (hM : c * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    (hMX : Dec2.cstarX d L Cx₂ * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    (hδ0 : 0 < δ) (hε : δ ≤ bgC0 d L N) (hδ : δ ≤ c7 d L N BG κ)
    (hνε : S.ν * ((L : ℝ) ^ (k + 1)) ^ 2 * δ ^ 2 ≤ δ ^ 2)
    (hphi : 3 * δ + K4 d L N BG κ * δ < 1 / 2)
    (hmarD : K4 d L N BG κ * δ + 2 * δ + K4 d L N BG κ * δ * (K4 d L N BG κ * δ + 2 * (1 + 3 * δ))
      < δc)
    (hαD : K4 d L N BG κ * δ < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    (hD : InDomainC S.G' S.ν δ δ S.D') {κ₁ : ℝ} (hκ₁ : κ₁ ≤ κ)
    (X₁loc : S.U → Finset (CTorus d L N₁ m₁ (k + 1))) (X₁ : Finset (CTorus d L N₁ m₁ (k + 1)))
    (inner : Finset S.U) (B : (S.U → Fin N → ℂ) → ℂ) (ψin : inner → Rn N)
    (U : Set (S.U → Fin N → ℂ))
    (hB : ∀ ψout ∈ U, ∀ s ∈ Analysis.polydisc (0 : Dec2.DecParams (coverOf S.G'))
      (fun _ => Real.exp κ₁), AnalyticAt ℂ B (S.composed (coverOf S.G') (rho4 d L N BG κ)
        (S.slocOf (coverOf S.G') X₁loc (coreExt (coverOf S.G') X₁ s)) (S.fill inner ψin ψout))) :
    AnalyticOnNhd ℂ (fun q : (S.U → Fin N → ℂ) × Dec2.DecParams (coverOf S.G') =>
        S.oldInterp (coverOf S.G') (rho4 d L N BG κ) X₁loc X₁ inner q.1 B ψin q.2)
      (U ×ˢ Analysis.polydisc 0 fun _ => Real.exp κ₁) := by
  classical
  rintro ⟨ψo, s⟩ ⟨hψo, hs⟩
  have hf : ∀ b P, AnalyticAt ℂ (fun q : (S.U → Fin N → ℂ) × Dec2.DecParams (coverOf S.G') =>
      S.slocOf (coverOf S.G') X₁loc (coreExt (coverOf S.G') X₁ q.2) b P) (ψo, s) := by
    intro b P
    have hproj : AnalyticAt ℂ (fun q : (S.U → Fin N → ℂ) × Dec2.DecParams (coverOf S.G') => q.2 P)
        (ψo, s) :=
      ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : (coverOf S.G').cubeIdx => ℂ) P).analyticAt
        _).comp analyticAt_snd
    simp only [slocOf, coreExt]
    split_ifs <;> first
      | exact analyticAt_const.mul analyticAt_const
      | exact hproj.mul analyticAt_const
  have hfv : ∀ b P, ‖S.slocOf (coverOf S.G') X₁loc (coreExt (coverOf S.G') X₁ s) b P‖ <
      Real.exp κ := by
    intro b P
    have h1 : 1 < Real.exp κ := Real.one_lt_exp_iff.2 hκ
    have hsP : ‖s P‖ < Real.exp κ :=
      lt_of_lt_of_le (by simpa using hs P) (Real.exp_le_exp.2 hκ₁)
    simp only [slocOf, coreExt]
    split_ifs <;> simp <;> linarith
  have hψ : ∀ b i, AnalyticAt ℂ (fun q : (S.U → Fin N → ℂ) × Dec2.DecParams (coverOf S.G') =>
      S.fill inner ψin q.1 b i) (ψo, s) := by
    intro b i
    simp only [fill]
    split_ifs
    · exact analyticAt_const
    · exact ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin N => ℂ) i).comp
        (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : S.U => Fin N → ℂ) b)).analyticAt _ |>.comp
          analyticAt_fst
  have hΓ : AnalyticAt ℂ (fun q : (S.U → Fin N → ℂ) × Dec2.DecParams (coverOf S.G') =>
      S.composed (coverOf S.G') (rho4 d L N BG κ)
        (S.slocOf (coverOf S.G') X₁loc (coreExt (coverOf S.G') X₁ q.2)) (S.fill inner ψin q.1))
      (ψo, s) :=
    analyticAt_pi_iff.2 fun b => analyticAt_pi_iff.2 fun i =>
      S.analyticAt_composed hS Sb SX hCx₂ HB hκ.le hM hMX hδ0 hε hδ hνε hphi hmarD hαD hsm hD
        (f := fun q : (S.U → Fin N → ℂ) × Dec2.DecParams (coverOf S.G') =>
          S.slocOf (coverOf S.G') X₁loc (coreExt (coverOf S.G') X₁ q.2)) hf hfv
        (ψhat := fun q => S.fill inner ψin q.1) hψ b i
  exact (hB ψo hψo s hs).comp_of_eq hΓ rfl

/-- **The interpolated old term is analytic on the polydisc** (the hypothesis `hana` of
`sum_oldCoef_eq_of_analytic`; Theorems I-4b (i), I-4c (iii)): with the standing conditions of
`analyticAt_composed`, `κ > 0` and `κ₁ ≤ κ`, if the old term `B` is analytic at the composed field of
every localization vector of the polydisc of radius `e^{κ₁}`, then `F_X(s)` is analytic there (the
instance of `analyticOnNhd_oldInterp_out` at one fluctuation field). -/
theorem analyticOnNhd_oldInterp {Kc Cx Cx₂ c BG δ δc : ℝ} (hS : Dec2.DecSpecs d L Kc Cx c BG)
    (Sb : Dec2.CoverBase (coverOf S.G') S.G' (compWeight L S.a₁) S.ν Kc Cx)
    (SX : Dec2.XCover (coverOf S.G') S.G' (compWeight L S.a₁) S.a₁ S.ν Cx₂) (hCx₂ : 0 ≤ Cx₂)
    (HB : BgHyp d L (k + 1) ϱ' (compWeight L S.a₁) S.ν) {κ : ℝ} (hκ : 0 < κ)
    (hM : c * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    (hMX : Dec2.cstarX d L Cx₂ * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    (hδ0 : 0 < δ) (hε : δ ≤ bgC0 d L N) (hδ : δ ≤ c7 d L N BG κ)
    (hνε : S.ν * ((L : ℝ) ^ (k + 1)) ^ 2 * δ ^ 2 ≤ δ ^ 2)
    (hphi : 3 * δ + K4 d L N BG κ * δ < 1 / 2)
    (hmarD : K4 d L N BG κ * δ + 2 * δ + K4 d L N BG κ * δ * (K4 d L N BG κ * δ + 2 * (1 + 3 * δ))
      < δc)
    (hαD : K4 d L N BG κ * δ < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    (hD : InDomainC S.G' S.ν δ δ S.D') {κ₁ : ℝ} (hκ₁ : κ₁ ≤ κ)
    (X₁loc : S.U → Finset (CTorus d L N₁ m₁ (k + 1))) (X₁ : Finset (CTorus d L N₁ m₁ (k + 1)))
    (inner : Finset S.U) (ψout : S.U → Fin N → ℂ) (B : (S.U → Fin N → ℂ) → ℂ)
    (ψin : inner → Rn N)
    (hB : ∀ s ∈ Analysis.polydisc (0 : Dec2.DecParams (coverOf S.G')) (fun _ => Real.exp κ₁),
      AnalyticAt ℂ B (S.composed (coverOf S.G') (rho4 d L N BG κ)
        (S.slocOf (coverOf S.G') X₁loc (coreExt (coverOf S.G') X₁ s)) (S.fill inner ψin ψout))) :
    AnalyticOnNhd ℂ (S.oldInterp (coverOf S.G') (rho4 d L N BG κ) X₁loc X₁ inner ψout B ψin)
      (Analysis.polydisc 0 fun _ => Real.exp κ₁) := by
  intro s hs
  have h := S.analyticOnNhd_oldInterp_out hS Sb SX hCx₂ HB hκ hM hMX hδ0 hε hδ hνε hphi hmarD hαD
    hsm hD hκ₁ X₁loc X₁ inner B ψin {ψout}
    (fun ψo hψo => by obtain rfl := Set.mem_singleton_iff.1 hψo; exact hB) (ψout, s) ⟨rfl, hs⟩
  have hg : AnalyticAt ℂ (fun s' : Dec2.DecParams (coverOf S.G') => (ψout, s')) s :=
    analyticAt_const.prod analyticAt_id
  exact h.comp hg

end HoleStep

end Balaban.Fluctuation
