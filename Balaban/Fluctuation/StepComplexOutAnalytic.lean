/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.StepComplexJoint
public import Balaban.Fluctuation.StepComplexJointH
public import Balaban.Analysis.ParamIntegralAnalytic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The outputs of the complex step are analytic in the block datum (FLUCTUATION §2.6; Def-6 (H.2), (H.7))

The class of effective actions requires the new terms produced by a step to be analytic functions
of the block datum on the complex domain.  In the family form of `StepComplexAnalytic` (one function
`F` of the raw datum `(θ, h̃)` which returns the object of the step `S.withDatum D hD` at every datum
`D` of the chart `Ξ^c(𝔹_{k+1}; 1, ε)` with `h = h₀`), this file proves, under the hypotheses of the
complex chart of RAY-CHART §1:

* `exists_analytic_hatLog`, `exists_analytic_halfLogDetCC`: the logarithm `𝕃 = log 𝒜` of Lemma
  2.4 (c) and `½ log det C^{(k)} = -½ ∑ tr 𝕃(y,y)` are analytic on the whole chart;
* `EdensAnalyticOnPath`, `FlocAnalyticOnPath`, `MlocAnalyticOnPath`: the analyticity (H.2), (H.7)
  of the class terms `ℰ^{(j)}`, `ℱ^{(j)}`, `ℳ^{(j)}` at the composed data of the path (they hold for
  the class with zero old terms: `edensAnalyticOnPath_zeroClass`, …);
* `exists_analyticAt_TstepC_of_analyticAt_class`, `exists_analytic_TstepC_zeroClass`: the
  fluctuation integral `TstepC` (P4 (2.36)-(2.40)) is analytic at every datum at which the class
  terms are analytic on the path; for the zero class, on the whole chart;
* `exists_analyticAt_E1C_of_analyticAt_Edens`, `exists_analyticAt_E0C_of_analyticAt_Edens`,
  `exists_analyticAt_F0C_of_analyticAt_Floc`, `exists_analyticAt_M0C_of_analyticAt_Mloc`: the new
  terms `ℰ₁^{(k+1)}`, `ℰ₀^{(k+1)}`, `ℱ₀^{(k+1)}(g)`, `ℳ₀^{(k+1)}(y; g)` of (2.8), (2.9), P4 (2.53)
  are analytic at every datum of the chart at which the class terms are analytic on the path and
  the partition functions do not vanish (`StepNonvanishingC`); the zero-class forms
  (`exists_analyticAt_E1C_zeroClass`, …, `exists_analyticAt_E0C_add_F0C_zeroClass`) need
  `StepNonvanishingC` only.

The integrals over the fluctuation variable are parameter integrals of jointly analytic integrands
(`StepComplexJoint`) over a fixed real domain; their analyticity is
`Balaban.Analysis.analyticAt_integral_comp` and `analyticAt_interpAvg_comp`.  The nonvanishing of
`Z_{s,0}`, `Z_{1,t}` is needed at the datum only: by compactness of `[0,1]` it then holds for all
nearby raw data.
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Analysis
  Balaban.Fluctuation Finset Matrix

section Log

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱm : ℝ}
variable {Gp : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
variable {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}
variable {a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁ : ℝ}

/-- **The logarithm `𝕃 = log (a L⁻² Q*Q + Δ^{(k)})` is analytic in the datum on the chart**
(Lemma 2.4 (c); RAY-CHART §1 at `λ ≡ 1`): one matrix-valued function of the raw data, with entries
analytic at every point of `Ξ^c(𝔹_{k+1}; 1, ε)`, returns the decoupled logarithm `decLog` at `s ≡ 1`
and at the complex background `(φ̄, α) = (barField, bgMultC)` of every datum of the chart.  (The
analogue of `exists_analytic_hatCovSqrt`, from `analyticOnNhd_decLog_entry`.) -/
theorem exists_analytic_hatLog (hC : FlCore N Gp Hm a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
    (hk : 1 ≤ k) (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δc : ℝ}
    (hdm : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4) :
    ∃ F : RawData d L (N₁ * L ^ m₁) (k + 1) N →
        Matrix (unitPts Gp × Fin N) (unitPts Gp × Fin N) ℂ,
      (∀ p q, AnalyticOnNhd ℂ (fun Θ => F Θ p q) (XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps)) ∧
      ∀ D : BgData Gp N, XiCData Gp (compWeight L a₁) ν (k + 1) 1 eps D →
        F (rawOf D) = decLog Gp (compWeight L a₁) a₁ ν
          (bgMultC Gp (compWeight L a₁) ν (bgC0 d L N) D) (fun _ => 1)
          (barField Gp D.Ψ (bgFieldC Gp (compWeight L a₁) ν (bgC0 d L N) D))
          (unitQ Gp) (unitP Gp) := by
  classical
  obtain ⟨F₀, hF₀an, hF₀⟩ := exists_analytic_bgC hC
  have hd0 : 0 < d := by have := hC.HBp.hd; omega
  have hδc : 0 ≤ δc := by
    have : 0 ≤ decDomMargin d L N BG κ (xiC1 d * eps) := by
      have hε := hC.eps_pos
      have hc1 := one_le_xiC1 d
      have hδ0 : 0 < xiC1 d * eps := by positivity
      have : 0 < K4 d L N BG κ := K4_pos hC.hS.fam.2.1 hd0
      unfold decDomMargin; positivity
    linarith
  have hX : XSetting Gp (compWeight L a₁) a₁ ν := xSetting_of_flCore hC hk
  have hU := (isUnitLatticeB_unit (G := Gp)).toIsUnitLattice
  refine ⟨fun Θ => decLog Gp (compWeight L a₁) a₁ ν (F₀ Θ).2 (fun _ => 1)
    (barField Gp Θ.1 (F₀ Θ).1) (unitQ Gp) (unitP Gp), fun p q => ?_, fun D hD => ?_⟩
  · rintro Θ ⟨D, hD, rfl⟩
    obtain ⟨hI, -⟩ := isDecBg_one_of_xiCData hC hD
    have hE1 : 1 < Real.exp κ := Real.one_lt_exp_iff.2 hC.hκ
    have hs : ∀ P, ‖(fun _ : ↥(cubeIdx Gp) => (1 : ℂ)) P‖ < Real.exp κ := fun P => by
      simpa using hE1
    have hmem := decDom_of_isDecBg hC hs hD hI hdm hα
    have hF₀at : AnalyticAt ℂ F₀ (rawOf D) := hF₀an _ ⟨D, hD, rfl⟩
    have hφ : ∀ r, AnalyticAt ℂ (fun Θ : RawData d L (N₁ * L ^ m₁) (k + 1) N => (F₀ Θ).1 r)
        (rawOf D) := fun r => analyticAt_pi_iff.1 (analyticAt_fst.comp hF₀at) r
    have hαa : AnalyticAt ℂ (fun Θ : RawData d L (N₁ * L ^ m₁) (k + 1) N => (F₀ Θ).2)
        (rawOf D) := analyticAt_snd.comp hF₀at
    have hbar := analyticAt_barField (Gp := Gp) (q := rawOf D)
      (fun Θ : RawData d L (N₁ * L ^ m₁) (k + 1) N => (F₀ Θ).1)
      (fun Θ : RawData d L (N₁ * L ^ m₁) (k + 1) N => Θ.1) hφ
      (fun y j => analyticAt_rawΨ y j (rawOf D))
    have he : AnalyticAt ℂ (fun Θ : RawData d L (N₁ * L ^ m₁) (k + 1) N =>
        ((fun _ : ↥(cubeIdx Gp) => (1 : ℂ)), (barField Gp Θ.1 (F₀ Θ).1, (F₀ Θ).2))) (rawOf D) :=
      AnalyticAt.prod analyticAt_const (hbar.prod hαa)
    have hpt : ((fun _ : ↥(cubeIdx Gp) => (1 : ℂ)),
        (barField Gp (rawOf D).1 (F₀ (rawOf D)).1, (F₀ (rawOf D)).2)) ∈ DecDom Gp N κ δc := by
      rw [hF₀ D hD]; exact hmem
    have hg : AnalyticAt ℂ (fun e : DecData Gp N =>
        decLog Gp (compWeight L a₁) a₁ ν e.2.2 (extS Gp e.1) e.2.1 (unitQ Gp) (unitP Gp) p q)
        ((fun _ : ↥(cubeIdx Gp) => (1 : ℂ)),
          (barField Gp (rawOf D).1 (F₀ (rawOf D)).1, (F₀ (rawOf D)).2)) :=
      analyticOnNhd_decLog_entry (N := N) hX hC.hκ.le hMX hδc hsm hU p q _ hpt
    have hcomp := AnalyticAt.comp (f := fun Θ : RawData d L (N₁ * L ^ m₁) (k + 1) N =>
        ((fun _ : ↥(cubeIdx Gp) => (1 : ℂ)), (barField Gp Θ.1 (F₀ Θ).1, (F₀ Θ).2))) hg he
    refine hcomp.congr (Filter.Eventually.of_forall fun Θ => ?_)
    show decLog Gp (compWeight L a₁) a₁ ν (F₀ Θ).2 (extS Gp (fun _ => (1 : ℂ)))
      (barField Gp Θ.1 (F₀ Θ).1) (unitQ Gp) (unitP Gp) p q = _
    rw [extS_one]
  · show decLog Gp (compWeight L a₁) a₁ ν (F₀ (rawOf D)).2 (fun _ => 1)
      (barField Gp D.Ψ (F₀ (rawOf D)).1) (unitQ Gp) (unitP Gp) = _
    rw [hF₀ D hD]

end Log

end Balaban.Localization

namespace Balaban.Fluctuation

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.SmallField.Def6
  Balaban.Localization Balaban.Analysis Finset Matrix MeasureTheory

namespace StepSetting

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}
  (S : StepSetting d L N₁ m₁ k N ϱ) (C : StepClass d L N₁ m₁ k N ϱ)

/-! ### `½ log det C^{(k)}` -/

section HalfLogDet

variable {ϱm : ℝ} {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}
  {c BG κ eps Kc Cx c₂ BG₂ δ₁ δc : ℝ}
  (hC : FlCore N S.G' Hm S.a₁ S.ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
  (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
  (hdm : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
  (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
  (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)

include hC hMX hdm hα hsm in
/-- **`𝕃 = log 𝒜` of the complex step is analytic in the block datum** on the chart: one
matrix-valued function of the raw data with analytic entries on `Ξ^c(𝔹_{k+1}; 1, ε)` returns
`logAC` of the step with the datum `D`, for every datum `D` of the chart with `h = h₀`. -/
theorem exists_analytic_logAC :
    ∃ F : RawData d L (N₁ * L ^ m₁) (k + 1) N → Matrix (S.U × Fin N) (S.U × Fin N) ℂ,
      (∀ p q, AnalyticOnNhd ℂ (fun Θ => F Θ p q) (XiCRaw S.G' S.a S.ν (k + 1) 1 eps)) ∧
      ∀ (D : BgData S.G' N) (hD : ∀ y i, D.h y i = (S.h₀ i : ℂ)),
        XiCData S.G' S.a S.ν (k + 1) 1 eps D → F (rawOf D) = (S.withDatum D hD).logAC := by
  obtain ⟨F, hFan, hF⟩ := exists_analytic_hatLog hC S.hk1 hMX hdm hα hsm
  refine ⟨F, hFan, fun D hD hX => ?_⟩
  have hb : barField S.G' D.Ψ (bgFieldC S.G' S.a S.ν (bgC0 d L N) D) =
      svec S.G' (bgFieldC S.G' S.a S.ν (bgC0 d L N) D) := by
    funext x i
    exact barField_eq_svec S.hG' _ _ x i
  rw [hF D hX, hb]
  rfl

include hC hMX hdm hα hsm in
/-- **`½ log det C^{(k)}` of the complex step is analytic in the block datum** on the whole chart
(Lemma 2.4 (c), (2.8); the analytic branch `halfLogDetCC = -½ ∑_y tr 𝕃(y,y)`): one function of the
raw data, analytic on `Ξ^c(𝔹_{k+1}; 1, ε)`, returns `halfLogDetCC` of the step with the datum `D`,
for every datum `D` of the chart with `h = h₀`. -/
theorem exists_analytic_halfLogDetCC :
    ∃ F : RawData d L (N₁ * L ^ m₁) (k + 1) N → ℂ,
      AnalyticOnNhd ℂ F (XiCRaw S.G' S.a S.ν (k + 1) 1 eps) ∧
      ∀ (D : BgData S.G' N) (hD : ∀ y i, D.h y i = (S.h₀ i : ℂ)),
        XiCData S.G' S.a S.ν (k + 1) 1 eps D → F (rawOf D) = (S.withDatum D hD).halfLogDetCC := by
  obtain ⟨Lg, hLan, hL⟩ := S.exists_analytic_logAC hC hMX hdm hα hsm
  refine ⟨fun Θ => -(1 / 2 : ℂ) * ∑ y : S.U, ∑ i : Fin N, Lg Θ (y, i) (y, i), fun Θ hΘ => ?_,
    fun D hD hX => ?_⟩
  · exact analyticAt_const.mul (Finset.analyticAt_fun_sum _ fun y _ =>
      Finset.analyticAt_fun_sum _ fun i _ => hLan (y, i) (y, i) Θ hΘ)
  · show -(1 / 2 : ℂ) * ∑ y : S.U, ∑ i : Fin N, Lg (rawOf D) (y, i) (y, i) = _
    rw [hL D hD hX]
    rfl

end HalfLogDet

/-! ### The analyticity of the class terms on the path -/

/-- **The densities `ℰ^{(j)}` of the class are analytic at the composed data of the path** ((H.2)
with the inclusion of the composed data `(ψ_k^{(j)}, h)` of the complex old spins
`ψ^{(k)}(θ) + s ψ'(ψ̂)`, `s ∈ [0,1]`, `‖ψ̂‖ ≤ p₁`, in the domains of analyticity; `s = 0` is the
critical point). -/
def EdensAnalyticOnPath : Prop :=
  ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ x : S.E, ‖x‖ ≤ S.p₁ → ∀ j ∈ Finset.Icc 1 k,
    AnalyticAt ℂ
      (fun p : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N => Edens C.m₀ C.Tm j p.1 p.2)
      (composedPairAtC S.a S.ν (Nat.le_succ k) j (S.dataUC (S.psiAtC s x)))

/-- **The terms `ℱ^{(j)}(·, ·, g)` of the class are analytic at the composed data of the path**
((H.7)). -/
def FlocAnalyticOnPath (g : Fld d L N₁ m₁ (k + 1) N) : Prop :=
  ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ x : S.E, ‖x‖ ≤ S.p₁ → ∀ j ∈ Finset.Icc 1 k,
    AnalyticAt ℂ
      (fun p : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N => Floc C.m₀ C.Tm j p.1 p.2 g)
      (composedPairAtC S.a S.ν (Nat.le_succ k) j (S.dataUC (S.psiAtC s x)))

/-- **The components `ℳ^{(j)}(y; ·, ·, g)_i` of the class are analytic at the composed data of the
path** ((H.7)). -/
def MlocAnalyticOnPath (g : Fld d L N₁ m₁ (k + 1) N) (y : CTorus d L N₁ m₁ (k + 1)) (i : Fin N) :
    Prop :=
  ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ x : S.E, ‖x‖ ≤ S.p₁ → ∀ j ∈ Finset.Icc 1 k,
    AnalyticAt ℂ
      (fun p : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N =>
        Mloc C.m₀ C.Tm j y p.1 p.2 g i)
      (composedPairAtC S.a S.ν (Nat.le_succ k) j (S.dataUC (S.psiAtC s x)))

theorem analyticAt_Edens_zeroClass (j : ℕ)
    (p₀ : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N) :
    AnalyticAt ℂ (fun p : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N =>
      Edens (zeroClass d L N₁ m₁ k N ϱ).m₀ (zeroClass d L N₁ m₁ k N ϱ).Tm j p.1 p.2) p₀ := by
  have h : (fun p : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N =>
      Edens (zeroClass d L N₁ m₁ k N ϱ).m₀ (zeroClass d L N₁ m₁ k N ϱ).Tm j p.1 p.2) =
      fun _ => 0 := funext fun p => Edens_zero _ _ _ _
  rw [h]
  exact analyticAt_const

theorem analyticAt_Floc_zeroClass (g : Fld d L N₁ m₁ (k + 1) N) (j : ℕ)
    (p₀ : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N) :
    AnalyticAt ℂ (fun p : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N =>
      Floc (zeroClass d L N₁ m₁ k N ϱ).m₀ (zeroClass d L N₁ m₁ k N ϱ).Tm j p.1 p.2 g) p₀ := by
  have h : (fun p : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N =>
      Floc (zeroClass d L N₁ m₁ k N ϱ).m₀ (zeroClass d L N₁ m₁ k N ϱ).Tm j p.1 p.2 g) =
      fun _ => 0 := funext fun p => Floc_zero _ _ _ _ _
  rw [h]
  exact analyticAt_const

theorem analyticAt_Mloc_zeroClass (g : Fld d L N₁ m₁ (k + 1) N) (y : CTorus d L N₁ m₁ (k + 1))
    (i : Fin N) (j : ℕ) (p₀ : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N) :
    AnalyticAt ℂ (fun p : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N =>
      Mloc (zeroClass d L N₁ m₁ k N ϱ).m₀ (zeroClass d L N₁ m₁ k N ϱ).Tm j y p.1 p.2 g i) p₀ := by
  have h : (fun p : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N =>
      Mloc (zeroClass d L N₁ m₁ k N ϱ).m₀ (zeroClass d L N₁ m₁ k N ϱ).Tm j y p.1 p.2 g i) =
      fun _ => 0 := funext fun p => by
    have := Mloc_zero (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (N := N) (ϱ := ϱ)
      (zeroClass d L N₁ m₁ k N ϱ).m₀ j y p.1 p.2 g
    exact congrFun this i
  rw [h]
  exact analyticAt_const

/-- `EdensAnalyticOnPath` holds for the class with zero old terms, at every step datum (rule 10). -/
theorem edensAnalyticOnPath_zeroClass : S.EdensAnalyticOnPath (zeroClass d L N₁ m₁ k N ϱ) :=
  fun _ _ _ _ j _ => analyticAt_Edens_zeroClass j _

/-- `FlocAnalyticOnPath` holds for the class with zero old terms, at every step datum and every
source (rule 10). -/
theorem flocAnalyticOnPath_zeroClass (g : Fld d L N₁ m₁ (k + 1) N) :
    S.FlocAnalyticOnPath (zeroClass d L N₁ m₁ k N ϱ) g :=
  fun _ _ _ _ j _ => analyticAt_Floc_zeroClass g j _

/-- `MlocAnalyticOnPath` holds for the class with zero old terms, at every step datum and every
source (rule 10). -/
theorem mlocAnalyticOnPath_zeroClass (g : Fld d L N₁ m₁ (k + 1) N)
    (y : CTorus d L N₁ m₁ (k + 1)) (i : Fin N) :
    S.MlocAnalyticOnPath (zeroClass d L N₁ m₁ k N ϱ) g y i :=
  fun _ _ _ _ j _ => analyticAt_Mloc_zeroClass g y i j _

/-! ### The integrals over the fluctuation variable -/

theorem continuous_yhat : Continuous (fun x : S.E => yhat x) := by
  refine continuous_pi fun q => ?_
  have h : Continuous (fun x : S.E => x q.1 q.2) := by fun_prop
  exact Complex.continuous_ofReal.comp h

/-- The Lebesgue integral with the weight `χ_fl` is the integral over the ball `‖ψ̂‖ < p₁`. -/
theorem integral_chiFl_mul (hp₁ : 0 < S.p₁) (f : S.E → ℂ) :
    ∫ x : S.E, ((chiFl S.U N S.p₁ x : ℝ) : ℂ) * f x =
      ∫ x in Metric.ball (0 : S.E) S.p₁, f x := by
  rw [← integral_indicator Metric.isOpen_ball.measurableSet]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  by_cases hx : x ∈ Metric.ball (0 : S.E) S.p₁
  · have h1 : chiFl S.U N S.p₁ x = 1 := (chiFl_eq_one_iff hp₁ x).2 (by simpa using hx)
    simp [h1, Set.indicator_of_mem hx]
  · have h0 : chiFl S.U N S.p₁ x = 0 :=
      (chiFl_eq_zero_or_one S.p₁ x).resolve_right
        (fun h => hx (by simpa using (chiFl_eq_one_iff hp₁ x).1 h))
    simp [h0, Set.indicator_of_notMem hx]

/-- On the hat variable of a real fluctuation variable, each coordinate is bounded by `‖ψ̂‖`. -/
theorem yhat_le_of_norm_le {pp : ℝ} {x : S.E} (h : ‖x‖ ≤ pp) (p : S.U × Fin N) :
    ‖yhat x p‖ ≤ pp := by
  have := S.norm_smul_yhat_le_mul 1 x p
  rw [Complex.ofReal_one, one_smul, abs_one, one_mul] at this
  exact this.trans h

/-- For `t ∈ [0,1]` and `‖ψ̂‖ < p₁ ≤ p⁺`, the ray parameter stays below `p⁺` near `t`. -/
theorem eventually_abs_mul_le {pp : ℝ} (hle : S.p₁ ≤ pp) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1)
    {x : S.E} (hx : ‖x‖ < S.p₁) : ∀ᶠ r in nhds t, |r| * ‖x‖ ≤ pp := by
  have h0 : |t| * ‖x‖ < pp := by
    have ht1 : |t| ≤ 1 := by rw [abs_of_nonneg ht.1]; exact ht.2
    calc |t| * ‖x‖ ≤ 1 * ‖x‖ := mul_le_mul_of_nonneg_right ht1 (norm_nonneg _)
      _ < pp := by rw [one_mul]; exact hx.trans_le hle
  have hc : Continuous fun r : ℝ => |r| * ‖x‖ := by fun_prop
  exact (hc.continuousAt.eventually (eventually_lt_nhds h0)).mono fun r hr => hr.le

theorem abs_mul_le_of_mem {pp : ℝ} (hle : S.p₁ ≤ pp) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1)
    {x : S.E} (hx : ‖x‖ ≤ S.p₁) : |t| * ‖x‖ ≤ pp := by
  have ht1 : |t| ≤ 1 := by rw [abs_of_nonneg ht.1]; exact ht.2
  calc |t| * ‖x‖ ≤ 1 * S.p₁ := mul_le_mul ht1 hx (norm_nonneg _) zero_le_one
    _ ≤ pp := by rw [one_mul]; exact hle

/-- **The interpolation average of joint exponents**: for functions `A`, `B`, `C` of the raw block
datum and the hat variable,
`Θ ↦ ∫₀¹ (∫ ∂_t C(Θ, t ψ̂) e^{A(Θ, ψ̂) + B(Θ, t ψ̂)} dν_{p₁}) / (∫ e^{A(Θ, ψ̂) + B(Θ, t ψ̂)} dν_{p₁}) dt`.
With `A = 0`, `B = C = W₁` it is `ℰ₁^{(k+1)}`; with `A = W₁`, `B = C = W₂` it is `ℱ₀^{(k+1)}`. -/
noncomputable def avgJ (A B Cm : RawData d L (N₁ * L ^ m₁) (k + 1) N × S.EC → ℂ)
    (Θ : RawData d L (N₁ * L ^ m₁) (k + 1) N) : ℂ :=
  ∫ t in (0 : ℝ)..1,
    (∫ x, deriv (fun r : ℝ => Cm (Θ, (r : ℂ) • yhat x)) t *
      Complex.exp (A (Θ, yhat x) + B (Θ, (t : ℂ) • yhat x)) ∂S.nuFl) /
    (∫ x, Complex.exp (A (Θ, yhat x) + B (Θ, (t : ℂ) • yhat x)) ∂S.nuFl)

/-- **The interpolation average is analytic in the raw block datum** at every `Θ₀` at which the
exponents are jointly analytic on the path and the partition functions do not vanish on `[0,1]`
(`Balaban.Analysis.analyticAt_interpAvg_comp` for the measure `ν_{p₁}`, carried by the closed ball
of radius `p₁`). -/
theorem analyticAt_avgJ (hp₁ : 0 < S.p₁)
    {A B Cm : RawData d L (N₁ * L ^ m₁) (k + 1) N × S.EC → ℂ}
    {Θ₀ : RawData d L (N₁ * L ^ m₁) (k + 1) N}
    (hA : ∀ x : S.E, ‖x‖ ≤ S.p₁ → AnalyticAt ℂ A (Θ₀, yhat x))
    (hB : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ x : S.E, ‖x‖ ≤ S.p₁ →
      AnalyticAt ℂ B (Θ₀, (t : ℂ) • yhat x))
    (hCm : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ x : S.E, ‖x‖ ≤ S.p₁ →
      AnalyticAt ℂ Cm (Θ₀, (t : ℂ) • yhat x))
    (hZ : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ∫ x, Complex.exp (A (Θ₀, yhat x) + B (Θ₀, (t : ℂ) • yhat x)) ∂S.nuFl ≠ 0) :
    AnalyticAt ℂ (S.avgJ A B Cm) Θ₀ := by
  have : IsProbabilityMeasure S.nuFl := isProbabilityMeasure_fluctMeasure S.U N hp₁
  exact analyticAt_interpAvg_comp (μ := S.nuFl) (K := Metric.closedBall (0 : S.E) S.p₁)
    (isCompact_closedBall _ _) measurableSet_closedBall (S.ae_mem_closedBall hp₁)
    (ι := fun x : S.E => yhat x) S.continuous_yhat.continuousOn
    (fun x hx => hA x (by simpa using hx)) (fun t ht x hx => hB t ht x (by simpa using hx))
    (fun t ht x hx => hCm t ht x (by simpa using hx)) hZ

/-- The interpolation average at a raw datum, when the joint exponents are known there
`ν_{p₁}`-almost everywhere. -/
theorem avgJ_congr {A B Cm : RawData d L (N₁ * L ^ m₁) (k + 1) N × S.EC → ℂ}
    {Θ : RawData d L (N₁ * L ^ m₁) (k + 1) N} {a : S.E → ℂ} {b c : ℝ → S.E → ℂ}
    (ha : ∀ᵐ x ∂S.nuFl, A (Θ, yhat x) = a x)
    (hb : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ᵐ x ∂S.nuFl, B (Θ, (t : ℂ) • yhat x) = b t x)
    (hc : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ᵐ x ∂S.nuFl,
      (fun r : ℝ => Cm (Θ, (r : ℂ) • yhat x)) =ᶠ[nhds t] fun r => c r x) :
    S.avgJ A B Cm Θ = ∫ t in (0 : ℝ)..1,
      (∫ x, deriv (fun r => c r x) t * Complex.exp (a x + b t x) ∂S.nuFl) /
      (∫ x, Complex.exp (a x + b t x) ∂S.nuFl) := by
  unfold avgJ
  refine intervalIntegral.integral_congr fun t ht => ?_
  rw [Set.uIcc_of_le zero_le_one] at ht
  show (∫ x, deriv (fun r : ℝ => Cm (Θ, (r : ℂ) • yhat x)) t *
      Complex.exp (A (Θ, yhat x) + B (Θ, (t : ℂ) • yhat x)) ∂S.nuFl) /
    (∫ x, Complex.exp (A (Θ, yhat x) + B (Θ, (t : ℂ) • yhat x)) ∂S.nuFl) = _
  congr 1
  · refine integral_congr_ae ?_
    filter_upwards [ha, hb t ht, hc t ht] with x h1 h2 h3
    rw [h1, h2, h3.deriv_eq]
  · refine integral_congr_ae ?_
    filter_upwards [ha, hb t ht] with x h1 h2
    rw [h1, h2]


/-! ### The joint forms of the fluctuation integral and of the new terms -/

namespace JointRep

variable {S} {eps pp : ℝ} (Jr : S.JointRep eps pp)

/-- The fluctuation integral `TstepC` as a function of the raw block datum: the prefactor of (2.7)
with the determinant of the analytic square root, and the integral over `ψ̂` of the joint kernel and
density. -/
noncomputable def TstepJ (g : Fld d L N₁ m₁ (k + 1) N)
    (Θ : RawData d L (N₁ * L ^ m₁) (k + 1) N) : ℂ :=
  ((S.betaU ^ (-((N * Fintype.card S.U : ℕ) : ℝ) / 2) : ℝ) : ℂ) * (Jr.Mx Θ).det *
    ∫ x : S.E, ((chiFl S.U N S.p₁ x : ℝ) : ℂ) *
      (Jr.tKJ (Θ, yhat x) * Jr.rhoJ C g (Θ, yhat x))

/-- **`TstepJ` returns the fluctuation integral of the step with the datum `D`.** -/
theorem TstepJ_withDatum (hp₁ : 0 < S.p₁) (hle : S.p₁ ≤ pp) (g : Fld d L N₁ m₁ (k + 1) N)
    (D : BgData S.G' N) (hD : ∀ y i, D.h y i = (S.h₀ i : ℂ))
    (hX : XiCData S.G' S.a S.ν (k + 1) 1 eps D) :
    Jr.TstepJ C g (rawOf D) = (S.withDatum D hD).TstepC C g := by
  unfold TstepJ
  rw [Jr.Mx_withDatum D hD hX]
  show _ = ((S.betaU ^ (-((N * Fintype.card S.U : ℕ) : ℝ) / 2) : ℝ) : ℂ) *
    (S.withDatum D hD).covSqrtC.det *
    ∫ x : S.E, ((chiFl S.U N S.p₁ x : ℝ) : ℂ) *
      ((S.withDatum D hD).tKernelC ((S.withDatum D hD).psiAtC 1 x) *
        (S.withDatum D hD).rhoExpC C g ((S.withDatum D hD).psiAtC 1 x))
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  by_cases hx : chiFl S.U N S.p₁ x = 1
  · have hxn : ‖x‖ ≤ pp := ((chiFl_eq_one_iff hp₁ x).1 hx).le.trans hle
    show _ * (Jr.tKJ (rawOf D, yhat x) * Jr.rhoJ C g (rawOf D, yhat x)) = _
    rw [Jr.tKJ_withDatum D hD hX x, Jr.rhoJ_withDatum C D hD hX g hxn]
  · have h0 : chiFl S.U N S.p₁ x = 0 := (chiFl_eq_zero_or_one S.p₁ x).resolve_right hx
    simp [h0]

/-- **`TstepJ` is analytic at every raw datum of the chart at which the class terms are analytic
at the composed pairs of the contour** (a parameter integral over the ball `‖ψ̂‖ < p₁` of a jointly
analytic integrand, `analyticAt_integral_comp`). -/
theorem analyticAt_TstepJ (hp₁ : 0 < S.p₁) (hle : S.p₁ ≤ pp) (g : Fld d L N₁ m₁ (k + 1) N)
    {Θ : RawData d L (N₁ * L ^ m₁) (k + 1) N} (hΘ : Θ ∈ XiCRaw S.G' S.a S.ν (k + 1) 1 eps)
    (hE : ∀ x : S.E, ‖x‖ ≤ S.p₁ → ∀ j ∈ Finset.Icc 1 k, AnalyticAt ℂ
      (fun p : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N => Edens C.m₀ C.Tm j p.1 p.2)
      (Jr.PJ j (Θ, yhat x)))
    (hF : ∀ x : S.E, ‖x‖ ≤ S.p₁ → ∀ j ∈ Finset.Icc 1 k, AnalyticAt ℂ
      (fun p : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N => Floc C.m₀ C.Tm j p.1 p.2 g)
      (Jr.PJ j (Θ, yhat x))) :
    AnalyticAt ℂ (Jr.TstepJ C g) Θ := by
  have hdet : AnalyticAt ℂ (fun Θ : RawData d L (N₁ * L ^ m₁) (k + 1) N => (Jr.Mx Θ).det) Θ :=
    analyticAt_det fun i j => Jr.Mx_an i j Θ hΘ
  have hfin : IsFiniteMeasure ((volume : Measure S.E).restrict (Metric.ball 0 S.p₁)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact measure_ball_lt_top⟩
  have hint : AnalyticAt ℂ (fun Θ : RawData d L (N₁ * L ^ m₁) (k + 1) N =>
      ∫ x in Metric.ball (0 : S.E) S.p₁, Jr.tKJ (Θ, yhat x) * Jr.rhoJ C g (Θ, yhat x)) Θ := by
    refine analyticAt_integral_comp (μ := (volume : Measure S.E).restrict (Metric.ball 0 S.p₁))
      (K := Metric.closedBall (0 : S.E) S.p₁) (isCompact_closedBall _ _) measurableSet_closedBall
      (ae_restrict_of_forall_mem Metric.isOpen_ball.measurableSet
        fun x hx => Metric.ball_subset_closedBall hx)
      (ι := fun x : S.E => yhat x) S.continuous_yhat.continuousOn
      (G := fun q => Jr.tKJ q * Jr.rhoJ C g q) (fun x hx => ?_)
    have hxn : ‖x‖ ≤ S.p₁ := by simpa using hx
    exact (Jr.analyticAt_tKJ hΘ _).mul
      (Jr.analyticAt_rhoJ C hΘ (S.yhat_le_of_norm_le (hxn.trans hle)) g (hE x hxn) (hF x hxn))
  have hfun : Jr.TstepJ C g = fun Θ : RawData d L (N₁ * L ^ m₁) (k + 1) N =>
      ((S.betaU ^ (-((N * Fintype.card S.U : ℕ) : ℝ) / 2) : ℝ) : ℂ) * (Jr.Mx Θ).det *
        ∫ x in Metric.ball (0 : S.E) S.p₁, Jr.tKJ (Θ, yhat x) * Jr.rhoJ C g (Θ, yhat x) := by
    funext Θ'
    unfold TstepJ
    rw [S.integral_chiFl_mul hp₁]
  rw [hfun]
  exact (analyticAt_const.mul hdet).mul hint

include Jr in
/-- The raw marked interpolation value uses the composed old datum carrying any incoming
external field. -/
theorem M0J_dataUCH (hp₁ : 0 < S.p₁) (hle : S.p₁ ≤ pp)
    (H : StepSettingH S) (hX : XiCData S.G' S.a S.ν (k + 1) 1 eps H.D')
    (g : Fld d L N₁ m₁ (k + 1) N) (y : CTorus d L N₁ m₁ (k + 1)) (i : Fin N) :
    let ψ : ℝ → S.E → S.EC := fun t x =>
      (fun q =>
        (composeData (S.hG.precedes S.hG' (le_refl (k + 1))) S.a
          (bgFieldC S.G' S.a S.ν (bgC0 d L N) H.D') H.D').Ψ
            (unitRep (G' := S.G') q.1) q.2) +
        S.hatField (hatCovSqrt S.G' S.a₁ S.ν H.D') ((t : ℂ) • yhat x)
    ((S.betaU ^ (1 / 2 : ℝ) : ℝ) : ℂ) *
        S.avgJ (Jr.W1 C) (Jr.W2 C g) (Jr.McJ C g y i) (rawOf H.D') =
      ((S.betaU ^ (1 / 2 : ℝ) : ℝ) : ℂ) *
        ∫ t in (0 : ℝ)..1,
          avgFun₂ S.nuFl
            (fun _ x => Jr.W1 C (rawOf H.D', yhat x))
            (fun t x => Jr.W2 C g (rawOf H.D', (t : ℂ) • yhat x))
            (fun x => deriv (fun r => McompAtC C.m₀ C.Tm S.a S.ν (Nat.le_succ k)
              (H.dataUCH (ψ r x)) g y i) t) 1 t := by
  dsimp only
  rw [S.avgJ_congr
    (a := fun x => Jr.W1 C (rawOf H.D', yhat x))
    (b := fun t x => Jr.W2 C g (rawOf H.D', (t : ℂ) • yhat x))
    (c := fun t x => McompAtC C.m₀ C.Tm S.a S.ν (Nat.le_succ k)
      (H.dataUCH ((fun q =>
        (composeData (S.hG.precedes S.hG' (le_refl (k + 1))) S.a
          (bgFieldC S.G' S.a S.ν (bgC0 d L N) H.D') H.D').Ψ
            (unitRep (G' := S.G') q.1) q.2) +
        S.hatField (hatCovSqrt S.G' S.a₁ S.ν H.D') ((t : ℂ) • yhat x))) g y i)
    (Filter.Eventually.of_forall fun _ => rfl)
    (fun _ _ => Filter.Eventually.of_forall fun _ => rfl)
    (fun t ht => by
      filter_upwards [S.ae_ball hp₁] with x hx
      have hxn : ‖x‖ < S.p₁ := (chiFl_eq_one_iff hp₁ x).1 hx
      filter_upwards [S.eventually_abs_mul_le hle ht hxn] with r hr
      exact Jr.McJ_dataUCH H C hX (fun p => smul_yhat_le (S := S) (pp := pp) hr p) g y i)]
  unfold avgFun₂ partFun₂
  rfl

section Slice

variable (hp₁ : 0 < S.p₁) (hle : S.p₁ ≤ pp) (D : BgData S.G' N)
  (hD : ∀ y i, D.h y i = (S.h₀ i : ℂ)) (hX : XiCData S.G' S.a S.ν (k + 1) 1 eps D)

include hp₁ hle hX in
/-- On the slice, the joint exponent `W₁` at the hat variable `ψ̂` is `W₁(1, ψ̂)`, almost
everywhere. -/
theorem ae_W1_one : ∀ᵐ x ∂S.nuFl,
    Jr.W1 C (rawOf D, yhat x) = (S.withDatum D hD).WoneC C 1 x := by
  filter_upwards [S.ae_ball hp₁] with x hx
  have hxn : ‖x‖ < S.p₁ := (chiFl_eq_one_iff hp₁ x).1 hx
  have h := Jr.W1_withDatum C D hD hX (s := 1) (x := x) (by simpa using hxn.le.trans hle)
  rwa [Complex.ofReal_one, one_smul] at h

include hp₁ hle hX in
theorem ae_W1_path {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) : ∀ᵐ x ∂S.nuFl,
    Jr.W1 C (rawOf D, (t : ℂ) • yhat x) = (S.withDatum D hD).WoneC C t x := by
  filter_upwards [S.ae_ball hp₁] with x hx
  have hxn : ‖x‖ < S.p₁ := (chiFl_eq_one_iff hp₁ x).1 hx
  exact Jr.W1_withDatum C D hD hX (S.abs_mul_le_of_mem hle ht hxn.le)

include hp₁ hle hX in
theorem ae_W2_path (g : Fld d L N₁ m₁ (k + 1) N) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ∀ᵐ x ∂S.nuFl,
      Jr.W2 C g (rawOf D, (t : ℂ) • yhat x) = (S.withDatum D hD).WtwoC C g t x := by
  filter_upwards [S.ae_ball hp₁] with x hx
  have hxn : ‖x‖ < S.p₁ := (chiFl_eq_one_iff hp₁ x).1 hx
  exact Jr.W2_withDatum C D hD hX g (S.abs_mul_le_of_mem hle ht hxn.le)

include hp₁ hle hX in
/-- **The joint average with `A = 0`, `B = C = W₁` returns `ℰ₁^{(k+1)}` of the step with the datum
`D`.** -/
theorem E1J_withDatum :
    S.avgJ (fun _ => 0) (Jr.W1 C) (Jr.W1 C) (rawOf D) = (S.withDatum D hD).E1C C := by
  rw [S.avgJ_congr (a := fun _ => 0) (b := fun t x => (S.withDatum D hD).WoneC C t x)
    (c := fun t x => (S.withDatum D hD).WoneC C t x) (Filter.Eventually.of_forall fun _ => rfl)
    (fun t ht => Jr.ae_W1_path C hp₁ hle D hD hX ht)
    (fun t ht => by
      filter_upwards [S.ae_ball hp₁] with x hx
      have hxn : ‖x‖ < S.p₁ := (chiFl_eq_one_iff hp₁ x).1 hx
      filter_upwards [S.eventually_abs_mul_le hle ht hxn] with r hr
      exact Jr.W1_withDatum C D hD hX hr)]
  unfold E1C avgFun partFun
  refine intervalIntegral.integral_congr fun t _ => ?_
  simp only [zero_add]
  rfl

include hp₁ hle hX in
/-- **The joint average with `A = W₁`, `B = C = W₂` returns `ℱ₀^{(k+1)}(g)` of the step with the
datum `D`.** -/
theorem F0J_withDatum (g : Fld d L N₁ m₁ (k + 1) N) :
    S.avgJ (Jr.W1 C) (Jr.W2 C g) (Jr.W2 C g) (rawOf D) = (S.withDatum D hD).F0C C g := by
  rw [S.avgJ_congr (a := fun x => (S.withDatum D hD).WoneC C 1 x)
    (b := fun t x => (S.withDatum D hD).WtwoC C g t x)
    (c := fun t x => (S.withDatum D hD).WtwoC C g t x) (Jr.ae_W1_one C hp₁ hle D hD hX)
    (fun t ht => Jr.ae_W2_path C hp₁ hle D hD hX g ht)
    (fun t ht => by
      filter_upwards [S.ae_ball hp₁] with x hx
      have hxn : ‖x‖ < S.p₁ := (chiFl_eq_one_iff hp₁ x).1 hx
      filter_upwards [S.eventually_abs_mul_le hle ht hxn] with r hr
      exact Jr.W2_withDatum C D hD hX g hr)]
  rfl

include hp₁ hle hX in
/-- **The joint average with `A = W₁`, `B = W₂`, `C = ℳ_k(y)_i` returns
`β_k^{-1/2} ℳ₀^{(k+1)}(y; g)_i` of the step with the datum `D`.** -/
theorem M0J_withDatum (g : Fld d L N₁ m₁ (k + 1) N) (y : CTorus d L N₁ m₁ (k + 1)) (i : Fin N) :
    ((S.betaU ^ (1 / 2 : ℝ) : ℝ) : ℂ) *
        S.avgJ (Jr.W1 C) (Jr.W2 C g) (Jr.McJ C g y i) (rawOf D) =
      (S.withDatum D hD).M0C C g y i := by
  apply Eq.trans (Jr.M0J_dataUCH C hp₁ hle (S.withDatumH D) hX g y i)
  unfold StepSetting.M0C
  apply congrArg (fun z : ℂ => ((S.betaU ^ (1 / 2 : ℝ) : ℝ) : ℂ) * z)
  refine intervalIntegral.integral_congr fun t ht => ?_
  rw [Set.uIcc_of_le zero_le_one] at ht
  apply avgFun₂_congr_ae (Jr.ae_W1_one C hp₁ hle D hD hX)
    (Jr.ae_W2_path C hp₁ hle D hD hX g ht)
  refine Filter.Eventually.of_forall fun x => ?_
  congr 1
  funext r
  rw [StepSettingH.dataUCH_fibre (S := S) D hD]
  apply congrArg (fun ψ : S.EC => McompAtC C.m₀ C.Tm S.a S.ν (Nat.le_succ k)
    ((S.withDatum D hD).dataUC ψ) g y i)
  dsimp only [StepSetting.withDatumH]
  change (S.withDatum D hD).psi0C +
      (S.withDatum D hD).hatField (hatCovSqrt S.G' S.a₁ S.ν D) ((r : ℂ) • yhat x) =
    (S.withDatum D hD).psiAtC r x
  have hcov : hatCovSqrt S.G' S.a₁ S.ν D = (S.withDatum D hD).covSqrtC :=
    (Jr.Mx_eq D hX).symm.trans (Jr.Mx_withDatum D hD hX)
  rw [hcov]
  exact ((S.withDatum D hD).psiAtC_eq_psiHat r x).symm

include hp₁ hle hX in
/-- On the slice, the joint exponent `W₁` is analytic at the hat variables of the path, where the
densities `ℰ^{(j)}` are analytic at the composed data of the path. -/
theorem analyticAt_W1_withDatum (hEd : (S.withDatum D hD).EdensAnalyticOnPath C) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) {x : S.E} (hx : ‖x‖ ≤ S.p₁) :
    AnalyticAt ℂ (Jr.W1 C) (rawOf D, (t : ℂ) • yhat x) := by
  have hb := S.abs_mul_le_of_mem hle ht hx
  refine Jr.analyticAt_W1 C ⟨D, hX, rfl⟩ (smul_yhat_le hb) (fun j hj => ?_) (fun j hj => ?_)
  · rw [Jr.PJ_withDatum D hD hX j hb]
    exact hEd t ht x hx j hj
  · have h0 := Jr.PJ_withDatum D hD hX j (s := 0) (x := 0) (by simpa using Jr.hpp)
    rw [Complex.ofReal_zero, zero_smul] at h0
    rw [h0]
    exact hEd 0 ⟨le_rfl, zero_le_one⟩ 0 (by rw [norm_zero]; exact hp₁.le) j hj

include hp₁ hle hX in
/-- On the slice, the joint exponent `W₂` is analytic at the hat variables of the path, where the
terms `ℱ^{(j)}(·, ·, g)` are analytic at the composed data of the path. -/
theorem analyticAt_W2_withDatum (g : Fld d L N₁ m₁ (k + 1) N)
    (hFd : (S.withDatum D hD).FlocAnalyticOnPath C g) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1)
    {x : S.E} (hx : ‖x‖ ≤ S.p₁) : AnalyticAt ℂ (Jr.W2 C g) (rawOf D, (t : ℂ) • yhat x) := by
  have hb := S.abs_mul_le_of_mem hle ht hx
  refine Jr.analyticAt_W2 C ⟨D, hX, rfl⟩ (smul_yhat_le hb) g (fun j hj => ?_) (fun j hj => ?_)
  · rw [Jr.PJ_withDatum D hD hX j hb]
    exact hFd t ht x hx j hj
  · have h0 := Jr.PJ_withDatum D hD hX j (s := 0) (x := 0) (by simpa using Jr.hpp)
    rw [Complex.ofReal_zero, zero_smul] at h0
    rw [h0]
    exact hFd 0 ⟨le_rfl, zero_le_one⟩ 0 (by rw [norm_zero]; exact hp₁.le) j hj

include hle hX in
/-- On the slice, the joint component of `ℳ_k` is analytic at the hat variables of the path, where
the terms `ℳ^{(j)}(y; ·, ·, g)_i` are analytic at the composed data of the path. -/
theorem analyticAt_McJ_withDatum (g : Fld d L N₁ m₁ (k + 1) N) (y : CTorus d L N₁ m₁ (k + 1))
    (i : Fin N) (hMd : (S.withDatum D hD).MlocAnalyticOnPath C g y i) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) {x : S.E} (hx : ‖x‖ ≤ S.p₁) :
    AnalyticAt ℂ (Jr.McJ C g y i) (rawOf D, (t : ℂ) • yhat x) := by
  have hb := S.abs_mul_le_of_mem hle ht hx
  refine Jr.analyticAt_McJ C ⟨D, hX, rfl⟩ (smul_yhat_le hb) g y i (fun j hj => ?_)
  rw [Jr.PJ_withDatum D hD hX j hb]
  exact hMd t ht x hx j hj

include hp₁ hle hX in
/-- On the slice, at the hat variable `ψ̂` itself (`t = 1`). -/
theorem analyticAt_W1_one_withDatum (hEd : (S.withDatum D hD).EdensAnalyticOnPath C) {x : S.E}
    (hx : ‖x‖ ≤ S.p₁) : AnalyticAt ℂ (Jr.W1 C) (rawOf D, yhat x) := by
  have h := Jr.analyticAt_W1_withDatum C hp₁ hle D hD hX hEd (t := 1)
    ⟨zero_le_one, le_rfl⟩ hx
  rwa [Complex.ofReal_one, one_smul] at h

include hp₁ hle hX in
/-- On the slice, the partition function of the joint exponent `W₁` is `Z_{s,0}`. -/
theorem integral_exp_W1_eq (g : Fld d L N₁ m₁ (k + 1) N) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ∫ x, Complex.exp ((fun _ : RawData d L (N₁ * L ^ m₁) (k + 1) N × S.EC => (0 : ℂ))
        (rawOf D, yhat x) + Jr.W1 C (rawOf D, (t : ℂ) • yhat x)) ∂S.nuFl =
      (S.withDatum D hD).ZstC C g t 0 := by
  show _ = ∫ x, Complex.exp ((S.withDatum D hD).WoneC C t x +
    (S.withDatum D hD).WtwoC C g 0 x) ∂S.nuFl
  refine integral_congr_ae ?_
  filter_upwards [Jr.ae_W1_path C hp₁ hle D hD hX ht] with x h1
  rw [h1, (S.withDatum D hD).WtwoC_zero C g x, zero_add, add_zero]

include hp₁ hle hX in
/-- On the slice, the partition function of the joint exponents `W₁`, `W₂` is `Z_{1,t}`. -/
theorem integral_exp_W1_W2_eq (g : Fld d L N₁ m₁ (k + 1) N) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ∫ x, Complex.exp (Jr.W1 C (rawOf D, yhat x) + Jr.W2 C g (rawOf D, (t : ℂ) • yhat x))
        ∂S.nuFl = (S.withDatum D hD).ZstC C g 1 t := by
  show _ = ∫ x, Complex.exp ((S.withDatum D hD).WoneC C 1 x +
    (S.withDatum D hD).WtwoC C g t x) ∂S.nuFl
  refine integral_congr_ae ?_
  filter_upwards [Jr.ae_W1_one C hp₁ hle D hD hX, Jr.ae_W2_path C hp₁ hle D hD hX g ht]
    with x h1 h2
  rw [h1, h2]

end Slice

end JointRep


/-! ### The outputs of the step as analytic functions of the block datum -/

section Public

variable {c BG κ eps Kc Cx c₂ BG₂ δ₁ δc : ℝ}
  (hC : FlCore N S.G' (stepG d L N₁ m₁ k ϱ) S.a₁ S.ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
  (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
  (hdm : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
  (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
  (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
  (ha₁ : 0 < S.a₁) (hc7 : c7 d L N BG κ ≤ thm73C3 d L N) {R : ℝ} (hR : 1 < R)
  (hsmR : 2 * (compC4 d * (bgK1 d L N * (xiC1 d * eps))) + 5 * (R * δ₁) ≤ bgC1 d L N)
  (hβ : 0 ≤ S.β) (hp₁ : 0 < S.p₁) {pp : ℝ} (hlt : S.p₁ < pp)
  (hδ₁ : Real.sqrt N * (S.betaU ^ (-(1 / 2 : ℝ)) *
    (covSupConstC d L N (compWeight L S.a₁ k) κ * pp)) < δ₁)

include hC hMX hdm hα hsm ha₁ hc7 hR hsmR hβ hp₁ hlt hδ₁ in
/-- **The fluctuation integral `TstepC` as a function of the block datum** (Definition 2.1 after
the substitution (2.7); P4 (2.36)-(2.40)): one function of the raw data returns `TstepC C g` of the
step with the datum `D`, for every datum `D` of the chart with `h = h₀`, and it is analytic at
`rawOf D` if the class terms `ℰ^{(j)}`, `ℱ^{(j)}(·, ·, g)` are analytic at the composed data of the
path (`EdensAnalyticOnPath`, `FlocAnalyticOnPath`).  The integral over `ψ̂` is a parameter integral
over the fixed ball `‖ψ̂‖ < p₁`. -/
theorem exists_analyticAt_TstepC_of_analyticAt_class (g : Fld d L N₁ m₁ (k + 1) N) :
    ∃ F : RawData d L (N₁ * L ^ m₁) (k + 1) N → ℂ,
      ∀ (D : BgData S.G' N) (hD : ∀ y i, D.h y i = (S.h₀ i : ℂ)),
        XiCData S.G' S.a S.ν (k + 1) 1 eps D →
        F (rawOf D) = (S.withDatum D hD).TstepC C g ∧
        ((S.withDatum D hD).EdensAnalyticOnPath C → (S.withDatum D hD).FlocAnalyticOnPath C g →
          AnalyticAt ℂ F (rawOf D)) := by
  obtain ⟨Jr⟩ := S.nonempty_jointRep (eps := eps) hC hMX hdm hα hsm ha₁ hc7 hR hsmR hβ
    (hp₁.trans hlt) hδ₁
  refine ⟨Jr.TstepJ C g, fun D hD hX =>
    ⟨Jr.TstepJ_withDatum C hp₁ hlt.le g D hD hX, fun hEd hFd => ?_⟩⟩
  have h1 : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  have hPJ : ∀ (x : S.E), ‖x‖ ≤ S.p₁ → ∀ j, Jr.PJ j (rawOf D, yhat x) =
      composedPairAtC S.a S.ν (Nat.le_succ k) j
        ((S.withDatum D hD).dataUC ((S.withDatum D hD).psiAtC 1 x)) := by
    intro x hx j
    have h := Jr.PJ_withDatum D hD hX j (s := 1) (x := x) (S.abs_mul_le_of_mem hlt.le h1 hx)
    rwa [Complex.ofReal_one, one_smul] at h
  refine Jr.analyticAt_TstepJ C hp₁ hlt.le g ⟨D, hX, rfl⟩ (fun x hx j hj => ?_)
    (fun x hx j hj => ?_)
  · rw [hPJ x hx j]
    exact hEd 1 h1 x hx j hj
  · rw [hPJ x hx j]
    exact hFd 1 h1 x hx j hj

include hC hMX hdm hα hsm ha₁ hc7 hR hsmR hβ hp₁ hlt hδ₁ in
/-- **The fluctuation integral `TstepC` is analytic in the block datum on the whole chart, for the
class with zero old terms and every source `g`**: one function of the raw data, analytic at every
point of `Ξ^c(𝔹_{k+1}; 1, ε)`, returns `TstepC` of the step with the datum `D`, for every datum `D`
of the chart with `h = h₀`.  No nonvanishing is needed. -/
theorem exists_analytic_TstepC_zeroClass (g : Fld d L N₁ m₁ (k + 1) N) :
    ∃ F : RawData d L (N₁ * L ^ m₁) (k + 1) N → ℂ,
      AnalyticOnNhd ℂ F (XiCRaw S.G' S.a S.ν (k + 1) 1 eps) ∧
      ∀ (D : BgData S.G' N) (hD : ∀ y i, D.h y i = (S.h₀ i : ℂ)),
        XiCData S.G' S.a S.ν (k + 1) 1 eps D →
        F (rawOf D) = (S.withDatum D hD).TstepC (zeroClass d L N₁ m₁ k N ϱ) g := by
  obtain ⟨Jr⟩ := S.nonempty_jointRep (eps := eps) hC hMX hdm hα hsm ha₁ hc7 hR hsmR hβ
    (hp₁.trans hlt) hδ₁
  refine ⟨Jr.TstepJ (zeroClass d L N₁ m₁ k N ϱ) g, fun Θ hΘ => ?_, fun D hD hX =>
    Jr.TstepJ_withDatum _ hp₁ hlt.le g D hD hX⟩
  exact Jr.analyticAt_TstepJ _ hp₁ hlt.le g hΘ (fun _ _ j _ => analyticAt_Edens_zeroClass j _)
    (fun _ _ j _ => analyticAt_Floc_zeroClass g j _)

include hC hMX hdm hα hsm ha₁ hc7 hR hsmR hβ hp₁ hlt hδ₁ in
/-- **`ℰ₁^{(k+1)}` of (2.8) as a function of the block datum**: one function of the raw data
returns `E1C C` of the step with the datum `D`, for every datum `D` of the chart with `h = h₀`, and
it is analytic at `rawOf D` if the densities `ℰ^{(j)}` are analytic at the composed data of the
path (`EdensAnalyticOnPath`) and `Z_{s,0} ≠ 0` on `[0,1]` at the datum `D`
(`StepNonvanishingC`). -/
theorem exists_analyticAt_E1C_of_analyticAt_Edens (g : Fld d L N₁ m₁ (k + 1) N) :
    ∃ F : RawData d L (N₁ * L ^ m₁) (k + 1) N → ℂ,
      ∀ (D : BgData S.G' N) (hD : ∀ y i, D.h y i = (S.h₀ i : ℂ)),
        XiCData S.G' S.a S.ν (k + 1) 1 eps D →
        F (rawOf D) = (S.withDatum D hD).E1C C ∧
        ((S.withDatum D hD).EdensAnalyticOnPath C → (S.withDatum D hD).StepNonvanishingC C g →
          AnalyticAt ℂ F (rawOf D)) := by
  obtain ⟨Jr⟩ := S.nonempty_jointRep (eps := eps) hC hMX hdm hα hsm ha₁ hc7 hR hsmR hβ
    (hp₁.trans hlt) hδ₁
  refine ⟨S.avgJ (fun _ => 0) (Jr.W1 C) (Jr.W1 C), fun D hD hX =>
    ⟨Jr.E1J_withDatum C hp₁ hlt.le D hD hX, fun hEd hnv => ?_⟩⟩
  refine S.analyticAt_avgJ hp₁ (fun _ _ => analyticAt_const)
    (fun t ht x hx => Jr.analyticAt_W1_withDatum C hp₁ hlt.le D hD hX hEd ht hx)
    (fun t ht x hx => Jr.analyticAt_W1_withDatum C hp₁ hlt.le D hD hX hEd ht hx) (fun t ht => ?_)
  rw [Jr.integral_exp_W1_eq C hp₁ hlt.le D hD hX g ht]
  exact hnv.seg1 t ht


include hC hMX hdm hα hsm ha₁ hc7 hR hsmR hβ hp₁ hlt hδ₁ in
/-- **`ℰ₀^{(k+1)} = ½ log det C^{(k)} + ℰ₁^{(k+1)}` of (2.8) as a function of the block datum**: one
function of the raw data returns `E0C C` of the step with the datum `D`, for every datum `D` of the
chart with `h = h₀`, and it is analytic at `rawOf D` under `EdensAnalyticOnPath` and
`StepNonvanishingC` at `D`. -/
theorem exists_analyticAt_E0C_of_analyticAt_Edens (g : Fld d L N₁ m₁ (k + 1) N) :
    ∃ F : RawData d L (N₁ * L ^ m₁) (k + 1) N → ℂ,
      ∀ (D : BgData S.G' N) (hD : ∀ y i, D.h y i = (S.h₀ i : ℂ)),
        XiCData S.G' S.a S.ν (k + 1) 1 eps D →
        F (rawOf D) = (S.withDatum D hD).E0C C ∧
        ((S.withDatum D hD).EdensAnalyticOnPath C → (S.withDatum D hD).StepNonvanishingC C g →
          AnalyticAt ℂ F (rawOf D)) := by
  obtain ⟨Fh, hFhan, hFh⟩ := S.exists_analytic_halfLogDetCC hC hMX hdm hα hsm
  obtain ⟨F1, hF1⟩ := S.exists_analyticAt_E1C_of_analyticAt_Edens C hC hMX hdm hα hsm ha₁ hc7 hR
    hsmR hβ hp₁ hlt hδ₁ g
  refine ⟨fun Θ => Fh Θ + F1 Θ, fun D hD hX => ⟨?_, fun hEd hnv => ?_⟩⟩
  · show Fh (rawOf D) + F1 (rawOf D) = (S.withDatum D hD).halfLogDetCC + (S.withDatum D hD).E1C C
    rw [hFh D hD hX, (hF1 D hD hX).1]
  · exact (hFhan _ ⟨D, hX, rfl⟩).add ((hF1 D hD hX).2 hEd hnv)

include hC hMX hdm hα hsm ha₁ hc7 hR hsmR hβ hp₁ hlt hδ₁ in
/-- **`ℱ₀^{(k+1)}(g)` of (2.9) as a function of the block datum**: one function of the raw data
returns `F0C C g` of the step with the datum `D`, for every datum `D` of the chart with `h = h₀`,
and it is analytic at `rawOf D` if the terms `ℰ^{(j)}`, `ℱ^{(j)}(·, ·, g)` are analytic at the
composed data of the path and `Z_{1,t} ≠ 0` on `[0,1]` at the datum `D`
(`StepNonvanishingC`). -/
theorem exists_analyticAt_F0C_of_analyticAt_Floc (g : Fld d L N₁ m₁ (k + 1) N) :
    ∃ F : RawData d L (N₁ * L ^ m₁) (k + 1) N → ℂ,
      ∀ (D : BgData S.G' N) (hD : ∀ y i, D.h y i = (S.h₀ i : ℂ)),
        XiCData S.G' S.a S.ν (k + 1) 1 eps D →
        F (rawOf D) = (S.withDatum D hD).F0C C g ∧
        ((S.withDatum D hD).EdensAnalyticOnPath C → (S.withDatum D hD).FlocAnalyticOnPath C g →
          (S.withDatum D hD).StepNonvanishingC C g → AnalyticAt ℂ F (rawOf D)) := by
  obtain ⟨Jr⟩ := S.nonempty_jointRep (eps := eps) hC hMX hdm hα hsm ha₁ hc7 hR hsmR hβ
    (hp₁.trans hlt) hδ₁
  refine ⟨S.avgJ (Jr.W1 C) (Jr.W2 C g) (Jr.W2 C g), fun D hD hX =>
    ⟨Jr.F0J_withDatum C hp₁ hlt.le D hD hX g, fun hEd hFd hnv => ?_⟩⟩
  refine S.analyticAt_avgJ hp₁
    (fun x hx => Jr.analyticAt_W1_one_withDatum C hp₁ hlt.le D hD hX hEd hx)
    (fun t ht x hx => Jr.analyticAt_W2_withDatum C hp₁ hlt.le D hD hX g hFd ht hx)
    (fun t ht x hx => Jr.analyticAt_W2_withDatum C hp₁ hlt.le D hD hX g hFd ht hx)
    (fun t ht => ?_)
  rw [Jr.integral_exp_W1_W2_eq C hp₁ hlt.le D hD hX g ht]
  exact hnv.seg2 t ht

include hC hMX hdm hα hsm ha₁ hc7 hR hsmR hβ hp₁ hlt hδ₁ in
/-- **`ℳ₀^{(k+1)}(y; g)_i` of P4 (2.53) as a function of the block datum**: one function of the raw
data returns `M0C C g y i` of the step with the datum `D`, for every datum `D` of the chart with
`h = h₀`, and it is analytic at `rawOf D` if the terms `ℰ^{(j)}`, `ℱ^{(j)}(·, ·, g)`,
`ℳ^{(j)}(y; ·, ·, g)_i` are analytic at the composed data of the path and `Z_{1,t} ≠ 0` on `[0,1]`
at the datum `D` (`StepNonvanishingC`). -/
theorem exists_analyticAt_M0C_of_analyticAt_Mloc (g : Fld d L N₁ m₁ (k + 1) N)
    (y : CTorus d L N₁ m₁ (k + 1)) (i : Fin N) :
    ∃ F : RawData d L (N₁ * L ^ m₁) (k + 1) N → ℂ,
      ∀ (D : BgData S.G' N) (hD : ∀ y i, D.h y i = (S.h₀ i : ℂ)),
        XiCData S.G' S.a S.ν (k + 1) 1 eps D →
        F (rawOf D) = (S.withDatum D hD).M0C C g y i ∧
        ((S.withDatum D hD).EdensAnalyticOnPath C → (S.withDatum D hD).FlocAnalyticOnPath C g →
          (S.withDatum D hD).MlocAnalyticOnPath C g y i →
          (S.withDatum D hD).StepNonvanishingC C g → AnalyticAt ℂ F (rawOf D)) := by
  obtain ⟨Jr⟩ := S.nonempty_jointRep (eps := eps) hC hMX hdm hα hsm ha₁ hc7 hR hsmR hβ
    (hp₁.trans hlt) hδ₁
  refine ⟨fun Θ => ((S.betaU ^ (1 / 2 : ℝ) : ℝ) : ℂ) *
      S.avgJ (Jr.W1 C) (Jr.W2 C g) (Jr.McJ C g y i) Θ, fun D hD hX =>
    ⟨Jr.M0J_withDatum C hp₁ hlt.le D hD hX g y i, fun hEd hFd hMd hnv => ?_⟩⟩
  refine analyticAt_const.mul (S.analyticAt_avgJ hp₁
    (fun x hx => Jr.analyticAt_W1_one_withDatum C hp₁ hlt.le D hD hX hEd hx)
    (fun t ht x hx => Jr.analyticAt_W2_withDatum C hp₁ hlt.le D hD hX g hFd ht hx)
    (fun t ht x hx => Jr.analyticAt_McJ_withDatum C hlt.le D hD hX g y i hMd ht hx)
    (fun t ht => ?_))
  rw [Jr.integral_exp_W1_W2_eq C hp₁ hlt.le D hD hX g ht]
  exact hnv.seg2 t ht

/-! ### The class with zero old terms -/

include hC hMX hdm hα hsm ha₁ hc7 hR hsmR hβ hp₁ hlt hδ₁ in
/-- **`ℰ₁^{(k+1)}` of the step for the zero class is analytic in the block datum** at every datum
of the chart (with `h = h₀`) at which `Z_{s,0} ≠ 0` on `[0,1]` (`StepNonvanishingC`). -/
theorem exists_analyticAt_E1C_zeroClass (g : Fld d L N₁ m₁ (k + 1) N) :
    ∃ F : RawData d L (N₁ * L ^ m₁) (k + 1) N → ℂ,
      ∀ (D : BgData S.G' N) (hD : ∀ y i, D.h y i = (S.h₀ i : ℂ)),
        XiCData S.G' S.a S.ν (k + 1) 1 eps D →
        F (rawOf D) = (S.withDatum D hD).E1C (zeroClass d L N₁ m₁ k N ϱ) ∧
        ((S.withDatum D hD).StepNonvanishingC (zeroClass d L N₁ m₁ k N ϱ) g →
          AnalyticAt ℂ F (rawOf D)) := by
  obtain ⟨F, hF⟩ := S.exists_analyticAt_E1C_of_analyticAt_Edens (zeroClass d L N₁ m₁ k N ϱ) hC
    hMX hdm hα hsm ha₁ hc7 hR hsmR hβ hp₁ hlt hδ₁ g
  exact ⟨F, fun D hD hX => ⟨(hF D hD hX).1, fun hnv =>
    (hF D hD hX).2 ((S.withDatum D hD).edensAnalyticOnPath_zeroClass) hnv⟩⟩

include hC hMX hdm hα hsm ha₁ hc7 hR hsmR hβ hp₁ hlt hδ₁ in
/-- **`ℰ₀^{(k+1)}` of the step for the zero class is analytic in the block datum** at every datum
of the chart (with `h = h₀`) at which `StepNonvanishingC` holds. -/
theorem exists_analyticAt_E0C_zeroClass (g : Fld d L N₁ m₁ (k + 1) N) :
    ∃ F : RawData d L (N₁ * L ^ m₁) (k + 1) N → ℂ,
      ∀ (D : BgData S.G' N) (hD : ∀ y i, D.h y i = (S.h₀ i : ℂ)),
        XiCData S.G' S.a S.ν (k + 1) 1 eps D →
        F (rawOf D) = (S.withDatum D hD).E0C (zeroClass d L N₁ m₁ k N ϱ) ∧
        ((S.withDatum D hD).StepNonvanishingC (zeroClass d L N₁ m₁ k N ϱ) g →
          AnalyticAt ℂ F (rawOf D)) := by
  obtain ⟨F, hF⟩ := S.exists_analyticAt_E0C_of_analyticAt_Edens (zeroClass d L N₁ m₁ k N ϱ) hC
    hMX hdm hα hsm ha₁ hc7 hR hsmR hβ hp₁ hlt hδ₁ g
  exact ⟨F, fun D hD hX => ⟨(hF D hD hX).1, fun hnv =>
    (hF D hD hX).2 ((S.withDatum D hD).edensAnalyticOnPath_zeroClass) hnv⟩⟩

include hC hMX hdm hα hsm ha₁ hc7 hR hsmR hβ hp₁ hlt hδ₁ in
/-- **`ℱ₀^{(k+1)}(g)` of the step for the zero class is analytic in the block datum**, for every
source `g`, at every datum of the chart (with `h = h₀`) at which `StepNonvanishingC` holds. -/
theorem exists_analyticAt_F0C_zeroClass (g : Fld d L N₁ m₁ (k + 1) N) :
    ∃ F : RawData d L (N₁ * L ^ m₁) (k + 1) N → ℂ,
      ∀ (D : BgData S.G' N) (hD : ∀ y i, D.h y i = (S.h₀ i : ℂ)),
        XiCData S.G' S.a S.ν (k + 1) 1 eps D →
        F (rawOf D) = (S.withDatum D hD).F0C (zeroClass d L N₁ m₁ k N ϱ) g ∧
        ((S.withDatum D hD).StepNonvanishingC (zeroClass d L N₁ m₁ k N ϱ) g →
          AnalyticAt ℂ F (rawOf D)) := by
  obtain ⟨F, hF⟩ := S.exists_analyticAt_F0C_of_analyticAt_Floc (zeroClass d L N₁ m₁ k N ϱ) hC
    hMX hdm hα hsm ha₁ hc7 hR hsmR hβ hp₁ hlt hδ₁ g
  exact ⟨F, fun D hD hX => ⟨(hF D hD hX).1, fun hnv =>
    (hF D hD hX).2 ((S.withDatum D hD).edensAnalyticOnPath_zeroClass)
      ((S.withDatum D hD).flocAnalyticOnPath_zeroClass g) hnv⟩⟩

include hC hMX hdm hα hsm ha₁ hc7 hR hsmR hβ hp₁ hlt hδ₁ in
/-- **`ℳ₀^{(k+1)}(y; g)_i` of the step for the zero class is analytic in the block datum**, for
every source `g`, at every datum of the chart (with `h = h₀`) at which `StepNonvanishingC`
holds. -/
theorem exists_analyticAt_M0C_zeroClass (g : Fld d L N₁ m₁ (k + 1) N)
    (y : CTorus d L N₁ m₁ (k + 1)) (i : Fin N) :
    ∃ F : RawData d L (N₁ * L ^ m₁) (k + 1) N → ℂ,
      ∀ (D : BgData S.G' N) (hD : ∀ y i, D.h y i = (S.h₀ i : ℂ)),
        XiCData S.G' S.a S.ν (k + 1) 1 eps D →
        F (rawOf D) = (S.withDatum D hD).M0C (zeroClass d L N₁ m₁ k N ϱ) g y i ∧
        ((S.withDatum D hD).StepNonvanishingC (zeroClass d L N₁ m₁ k N ϱ) g →
          AnalyticAt ℂ F (rawOf D)) := by
  obtain ⟨F, hF⟩ := S.exists_analyticAt_M0C_of_analyticAt_Mloc (zeroClass d L N₁ m₁ k N ϱ) hC
    hMX hdm hα hsm ha₁ hc7 hR hsmR hβ hp₁ hlt hδ₁ g y i
  exact ⟨F, fun D hD hX => ⟨(hF D hD hX).1, fun hnv =>
    (hF D hD hX).2 ((S.withDatum D hD).edensAnalyticOnPath_zeroClass)
      ((S.withDatum D hD).flocAnalyticOnPath_zeroClass g)
      ((S.withDatum D hD).mlocAnalyticOnPath_zeroClass g y i) hnv⟩⟩

include hC hMX hdm hα hsm ha₁ hc7 hR hsmR hβ hp₁ hlt hδ₁ in
/-- **`ℰ₀^{(k+1)} + ℱ₀^{(k+1)}(g)`, the exponent produced by the step (Proposition 2.6, (2.6)), is
analytic in the block datum for the zero class**: one function of the raw data returns
`E0C + F0C g` of the step with the datum `D`, for every datum `D` of the chart with `h = h₀`, and
it is analytic at `rawOf D` when `StepNonvanishingC` holds at `D`. -/
theorem exists_analyticAt_E0C_add_F0C_zeroClass (g : Fld d L N₁ m₁ (k + 1) N) :
    ∃ F : RawData d L (N₁ * L ^ m₁) (k + 1) N → ℂ,
      ∀ (D : BgData S.G' N) (hD : ∀ y i, D.h y i = (S.h₀ i : ℂ)),
        XiCData S.G' S.a S.ν (k + 1) 1 eps D →
        F (rawOf D) = (S.withDatum D hD).E0C (zeroClass d L N₁ m₁ k N ϱ) +
          (S.withDatum D hD).F0C (zeroClass d L N₁ m₁ k N ϱ) g ∧
        ((S.withDatum D hD).StepNonvanishingC (zeroClass d L N₁ m₁ k N ϱ) g →
          AnalyticAt ℂ F (rawOf D)) := by
  obtain ⟨FE, hFE⟩ := S.exists_analyticAt_E0C_zeroClass hC hMX hdm hα hsm ha₁ hc7 hR hsmR hβ hp₁
    hlt hδ₁ g
  obtain ⟨FF, hFF⟩ := S.exists_analyticAt_F0C_zeroClass hC hMX hdm hα hsm ha₁ hc7 hR hsmR hβ hp₁
    hlt hδ₁ g
  refine ⟨fun Θ => FE Θ + FF Θ, fun D hD hX => ⟨?_, fun hnv => ?_⟩⟩
  · show FE (rawOf D) + FF (rawOf D) = _
    rw [(hFE D hD hX).1, (hFF D hD hX).1]
  · exact ((hFE D hD hX).2 hnv).add ((hFF D hD hX).2 hnv)

end Public

/-! ### Proposition 2.6 as an identity between analytic functions of the block datum -/

section Prop26

variable {c BG κ eps Kc Cx c₂ BG₂ δ₁ δc : ℝ}
  (hC : FlCore N S.G' (stepG d L N₁ m₁ k ϱ) S.a₁ S.ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
  (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
  (hdm : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
  (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
  (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
  (ha₁ : 0 < S.a₁) (hc7 : c7 d L N BG κ ≤ thm73C3 d L N) {R : ℝ} (hR : 1 < R)
  (hsmR : 2 * (compC4 d * (bgK1 d L N * (xiC1 d * eps))) + 5 * (R * δ₁) ≤ bgC1 d L N)
  (hβ : 0 < S.β) (hp₁ : 0 < S.p₁) {pp : ℝ} (hlt : S.p₁ < pp)
  (hδ₁ : Real.sqrt N * (S.betaU ^ (-(1 / 2 : ℝ)) *
    (covSupConstC d L N (compWeight L S.a₁ k) κ * pp)) < δ₁)

include hC hMX hdm hα hsm ha₁ hc7 hR hsmR hβ hp₁ hlt hδ₁ in
/-- **Proposition 2.6 at complex data as an identity between analytic functions of the block
datum, for the class with zero old terms**: there are two functions of the raw datum, `F_T`
analytic on the whole chart `Ξ^c(𝔹_{k+1}; 1, ε)` and `F_E`, which return the fluctuation integral
`TstepC` and the new exponent `ℰ₀^{(k+1)} + ℱ₀^{(k+1)}(g)` of the step with the datum `D`, for
every datum `D` of the chart with `h = h₀`; at every such datum with `Z_{s,0}, Z_{1,t} ≠ 0`
(`StepNonvanishingC`), `F_E` is analytic and
`F_T = exp [-β_k A^η_{k+1} + ℰ_k(ψ^{(k)}) - E'''_k |T^{(k)}_1| + ℱ_k(ψ^{(k)}, g) + F_E]` (2.6). -/
theorem exists_analytic_prop26C_zeroClass (g : Fld d L N₁ m₁ (k + 1) N) :
    ∃ FT FE : RawData d L (N₁ * L ^ m₁) (k + 1) N → ℂ,
      AnalyticOnNhd ℂ FT (XiCRaw S.G' S.a S.ν (k + 1) 1 eps) ∧
      ∀ (D : BgData S.G' N) (hD : ∀ y i, D.h y i = (S.h₀ i : ℂ)),
        XiCData S.G' S.a S.ν (k + 1) 1 eps D →
        FT (rawOf D) = (S.withDatum D hD).TstepC (zeroClass d L N₁ m₁ k N ϱ) g ∧
        FE (rawOf D) = (S.withDatum D hD).E0C (zeroClass d L N₁ m₁ k N ϱ) +
          (S.withDatum D hD).F0C (zeroClass d L N₁ m₁ k N ϱ) g ∧
        ((S.withDatum D hD).StepNonvanishingC (zeroClass d L N₁ m₁ k N ϱ) g →
          AnalyticAt ℂ FE (rawOf D) ∧
          FT (rawOf D) = Complex.exp (-(S.β : ℂ) * (S.withDatum D hD).AnewC +
            EcompAtC (zeroClass d L N₁ m₁ k N ϱ).m₀ (zeroClass d L N₁ m₁ k N ϱ).Tm S.a S.ν
              (Nat.le_succ k) (S.withDatum D hD).psiKdC -
            ((S.withDatum D hD).Eppp (zeroClass d L N₁ m₁ k N ϱ) : ℂ) *
              ((S.withDatum D hD).nU : ℂ) +
            FcompAtC (zeroClass d L N₁ m₁ k N ϱ).m₀ (zeroClass d L N₁ m₁ k N ϱ).Tm S.a S.ν
              (Nat.le_succ k) (S.withDatum D hD).psiKdC g + FE (rawOf D))) := by
  obtain ⟨FT, hFTan, hFT⟩ := S.exists_analytic_TstepC_zeroClass (eps := eps) hC hMX hdm hα hsm ha₁
    hc7 hR hsmR hβ.le hp₁ hlt hδ₁ g
  obtain ⟨FE, hFE⟩ := S.exists_analyticAt_E0C_add_F0C_zeroClass (eps := eps) hC hMX hdm hα hsm ha₁
    hc7 hR hsmR hβ.le hp₁ hlt hδ₁ g
  refine ⟨FT, FE, hFTan, fun D hD hX => ⟨hFT D hD hX, (hFE D hD hX).1, fun hnv =>
    ⟨(hFE D hD hX).2 hnv, ?_⟩⟩⟩
  rw [hFT D hD hX, (hFE D hD hX).1]
  have h := (S.withDatum D hD).prop26C_zeroClass hC hMX hdm hα hsm ha₁ hc7 hR hsmR hβ hp₁ hlt
    hδ₁ hX g hnv
  rw [h, add_assoc]
  rfl

end Prop26

end StepSetting

end Balaban.Fluctuation
