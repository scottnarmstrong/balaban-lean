/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.ClassOldEndpointE
public import Balaban.Fluctuation.MarkedTwoMarkLocal
public import Balaban.Fluctuation.MarkedFanAnalytic
public import Balaban.Fluctuation.InteractionHatLC
public import Balaban.Fluctuation.MarkedCubicTaylor
public import Balaban.Fluctuation.DecMarkTotal
public import Balaban.Fluctuation.GeneralEnergyMarksAssembly
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The Y-marks of the inherited energy labels of a class member

Third leaf of `notes/phase1/GENCLASS-OLD.md`, marks part.  The mark of a label `τ = (j, y, X)` of the
old energy is the derivative of the label term at the shift `s ψ'` in the direction `M_z ψ'`.  Here it
is written as the sum, over the decoupled domains `Y`, of the `t`-derivatives at `0` of the localized
terms of the expansion of `Eτ` along the masked tangent `s ψ' + t M_z ψ'`, whose locality in `ψ̂` is
that of the expansion itself.

* `flDatumOne_stepG_liftC`, `classOldEndpoint_liftC`: the endpoint identity of `ClassOldEndpointE` at
  an arbitrary complex tangent `liftC v` of the unit lattice.
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Analysis
  Balaban.Fluctuation Balaban.Polymer Finset Matrix

section LCEngine

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱm : ℝ}
variable {Gp : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
variable {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}
variable {a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁ : ℝ} {X₁f : Finset (CTorus d L N₁ m₁ (k + 1))} {j : ℕ}
variable {m₀ : ℕ} {X 𝒦X : Set (CTorus d L N₁ m₁ (k + 1))}
variable (hC : FlCore N Gp Hm a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
include hC


/-- **The masked tangent at the physical cut point lies in the ball of block fluctuations.**  For a
datum of the chart and a bounded hat variable, `markedTangDec` (the lift of
`um · cc C^{1/2}(1) ψ̂ + tm · M_Zm (cc C^{1/2}(1) ψ̂)`) lies in `FlBallLC Hm δ₁` when
`(‖um‖ + ‖tm‖) · B < δ₁`.  It is `markedHatPsiF_mem_flBallLC` at the cut `s ≡ 1`, with the
identification of the decoupled tangent there with the lift of the physical square root
(`i4b_one`). -/
theorem markedTangDec_mem_flBallLC (hk : 1 ≤ k) (hG : IsLevel Hm k) (hG' : IsLevel Gp (k + 1))
    (cc : ℂ) {cψ : ℝ} (hcψ : 0 ≤ cψ) (Zm : Finset (unitPts Gp)) {um tm : ℂ}
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δc : ℝ}
    (hdm : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    (hδ : (‖um‖ + ‖tm‖) *
      (Real.sqrt N * (‖cc‖ * (covSupConstC d L N (compWeight L a₁ k) κ * cψ))) < δ₁)
    {D : BgData Gp N} (hD : XiCData Gp (compWeight L a₁) ν (k + 1) 1 eps D)
    {ψh : unitPts Gp × Fin N → ℂ} (hψh : ∀ p, ‖ψh p‖ ≤ cψ) :
    markedTangDec hG' cc a₁ ν Zm um tm D ψh ∈ FlBallLC Hm δ₁ := by
  classical
  have hd0 : 0 < d := by have := hC.HBp.hd; omega
  have hc1 := one_le_xiC1 d
  have hε := hC.eps_pos
  have hδ0 : 0 < xiC1 d * eps := by positivity
  obtain ⟨F₁, -, hF₁⟩ := i4b_analytic hC.hS hC.Sp hC.HBp hC.hκ.le hC.hM
  have hE1 : 1 < Real.exp κ := Real.one_lt_exp_iff.2 hC.hκ
  have hsx : ∀ P : ↥(cubeIdx Gp), ‖(fun _ : ↥(cubeIdx Gp) => (1 : ℂ)) P‖ < Real.exp κ :=
    fun P => by simpa using hE1
  have hψ1 := markedHatPsiF_mem_flBallLC hC hk hG hG' cc hcψ hMX hdm hα hsm hF₁ hsx hD hψh
    Zm hδ
  have hδ1 : xiC1 d * eps ≤ c7 d L N BG κ := hC.c7le
  have hδ0' : xiC1 d * eps ≤ bgC0 d L N := hδ1.trans ((c7_le_bgC1 d L N BG κ).trans
    (bgC1_le_bgC0 d L N hd0))
  have hνε : ν * ((L : ℝ) ^ (k + 1)) ^ 2 * (xiC1 d * eps) ^ 2 ≤ (xiC1 d * eps) ^ 2 := by
    have := hC.HBp.massLe; nlinarith [sq_nonneg (xiC1 d * eps)]
  have hDom := xiCData_inDomainC hC.HBp hC.small1 hD
  have hU : InUnionDomainC Gp (bgC0 d L N) (c7 d L N BG κ) ν D :=
    inUnionDomainC_of_inDomainC hC.HBp hδ0 hδ0' hδ1 hDom
  obtain ⟨φ, α, hI, -⟩ := i4b_exists_unique hC.hS hC.Sp hC.HBp hC.hκ.le hC.hM
    (fun P => (hsx P).le) hδ0 le_rfl hδ0' hδ1 hνε hDom
  have hFeq : F₁ ((fun _ : ↥(cubeIdx Gp) => (1 : ℂ)), rawOf D) = (φ, α) :=
    hF₁ (fun _ => 1) D hsx hU φ α hI
  obtain ⟨-, hφ1, hα1⟩ := i4b_one hC.hS hC.Sp hC.HBp hC.hκ.le hC.hM hδ0 le_rfl hδ0' hδ1
    hνε hDom hI
  have hψeq : markedHatPsiF a₁ ν hG' cc F₁ Zm um tm (fun _ => 1) (rawOf D) ψh =
      markedTangDec hG' cc a₁ ν Zm um tm D ψh := by
    rw [markedHatPsiF_eq_liftC]
    unfold hatSqrtF markedTangDec
    rw [hFeq, extS_one, hφ1, hα1]
    rfl
  rw [← hψeq]
  exact hψ1


end LCEngine

end Balaban.Localization

namespace Balaban.Fluctuation

open MeasureTheory Balaban Balaban.Localization Balaban.Multiscale
  Balaban.Background Balaban.SmallField Balaban.SmallField.Def6 Balaban.SmallField.Def6v2
  Balaban.SmallField.GsSpec Balaban.Analysis Balaban.Polymer Finset Matrix

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}

namespace StepSetting

variable (S : StepSetting d L N₁ m₁ k N ϱ)

/-- **The datum of an old-term functional on `𝔹_k` at an arbitrary complex tangent.**  For a complex
field `v` of the unit lattice, `flDatumOne` of the lifted tangent `liftC v` is the datum of the
complex old spin `ψ^{(k)} + v` (`flDatumOne_stepG` is the case of the tangent of a real hat
variable). -/
theorem flDatumOne_stepG_liftC (ha : S.a k ≠ 0) (BG₂ κ : ℝ)
    (hP : Precedes (stepG d L N₁ m₁ k ϱ) S.G')
    (hPm : Precedes (stepG d L N₁ m₁ k ϱ) (stepG d L N₁ m₁ k ϱ)) (v : S.EC)
    (hz : IsLayerConstant (stepG d L N₁ m₁ k ϱ) (liftC S.hG' v)) :
    flDatumOne (stepG d L N₁ m₁ k ϱ) BG₂ κ hP hPm S.a₁ S.ν S.D' (liftC S.hG' v) hz =
      S.dataUC (S.psi0C + v) := by
  refine BgData.eq_of_raw (Prod.ext ?_ ?_)
  · funext x i
    have ht := congrFun (congrFun (S.compTangent_dataUC (S.psi0C + v)) x) i
    simp only [compTangent] at ht
    rw [add_sub_cancel_left] at ht
    have e : (composeData (S.hG.precedes S.hG' (le_refl (k + 1))) S.a
        (bgFieldC S.G' S.a S.ν (bgC0 d L N) S.D') S.D').Ψ x i =
        composeField (stepG d L N₁ m₁ k ϱ) S.G' S.a (bgFieldC S.G' S.a S.ν (bgC0 d L N) S.D')
          S.D'.Ψ x i := rfl
    rw [e] at ht
    show (flDatumOne (stepG d L N₁ m₁ k ϱ) BG₂ κ hP hPm S.a₁ S.ν S.D' _ hz).Ψ x i =
      (S.dataUC (S.psi0C + v)).Ψ x i
    unfold flDatumOne
    rw [flDatum_Ψ, composeField_self S.hG S.a ha]
    linear_combination -ht
  · funext x i
    show (flDatumOne (stepG d L N₁ m₁ k ϱ) BG₂ κ hP hPm S.a₁ S.ν S.D' _ hz).h x i =
      (S.dataUC (S.psi0C + v)).h x i
    rw [S.dataUC_h]
    unfold flDatumOne
    rw [flDatum_h]
    show (if x ∈ (stepG d L N₁ m₁ k ϱ).Ω 1 then S.D'.h x i else 0) = _
    rw [ite_eq_left (S.hG x).1, S.hh₀]

/-- **The endpoint identity at an arbitrary complex tangent.**  For a label `(j, y, X)` of a class
member whose term generator `Gj` has the strong specification, the functional `flComp` of the
decoupled expansion at the raw data of the step and the tangent `liftC v` of an arbitrary complex
field `v` of the unit lattice is the term `β⁻¹ ℰ^{(j)}(y, X; ·)` at the composed pair of the datum
`dataUC (ψ^{(k)} + v)`.  `classOldEndpoint_complex` is the case `v = shiftUC z`. -/
theorem classOldEndpoint_liftC
    {P : Consts} {Dom : FieldDom d L N₁ m₁ (k + 1) N ϱ} {Tm : Terms d L N₁ m₁ (k + 1) N ϱ}
    (hcl : SFTermClauses P Dom Tm) {j : ℕ} (hj1 : 1 ≤ j) (hjk : j ≤ k) {y : CTorus d L N₁ m₁ (k + 1)}
    {X : Set (CTorus d L N₁ m₁ (k + 1))} {Gj : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
    (hS : GsSpecStrong j (hjk.trans (Nat.le_succ k)) X Gj)
    {c BG κ eps Kc Cx c₂ BG₂ δ₁ r₀ δ₃ δfl : ℝ}
    {X₀ X₁f : Finset (CTorus d L N₁ m₁ (k + 1))} {j₁ : ℕ}
    (hB : BgSetting N S.G' (stepG d L N₁ m₁ k ϱ) Gj S.a₁ S.ν c BG κ r₀ eps δ₃ X₀ X₁f j₁)
    (hF : FlSetting N S.G' (stepG d L N₁ m₁ k ϱ) (stepG d L N₁ m₁ k ϱ) S.a₁ S.ν κ BG eps δ₃ Kc Cx
      c₂ BG₂ δ₁ δfl X₁f)
    (hD : XiCData S.G' S.a S.ν (k + 1) 1 eps S.D') (v : S.EC) :
    flComp hB hF (fun raw => (S.β : ℂ)⁻¹ * Tm.E j y X raw.1 raw.2) (rawOf S.D', liftC S.hG' v) =
      (S.β : ℂ)⁻¹ * Tm.E j y X
        (composedPairAtC S.a S.ν (Nat.le_succ k) j (S.dataUC (S.psi0C + v))).1
        (composedPairAtC S.a S.ν (Nat.le_succ k) j (S.dataUC (S.psi0C + v))).2 := by
  have ha : S.a k ≠ 0 :=
    (compWeight_pos (by have := hB.HBp.hL; omega) hB.ha₁ S.hk1).ne'
  have hzl : IsLayerConstant (stepG d L N₁ m₁ k ϱ) (liftC S.hG' v) :=
    isLayerConstant_liftC S.hG S.hG' v
  rw [flComp_rawOf hB hF _ hD hzl,
    S.flDatumOne_stepG_liftC ha BG₂ κ hB.hP hF.hPm v hzl]
  unfold composedPairAtC
  simp only [hjk, ↓reduceDIte]
  congr 1
  refine hcl.localE j y X _ _ _ _ fun x hx => ?_
  exact composeData_agree_on_X (N := N) (a := S.a) hj1 hjk hS
    (bgFieldC (stepG d L N₁ m₁ k ϱ) S.a S.ν (bgC0 d L N) (S.dataUC (S.psi0C + v)))
    (S.dataUC (S.psi0C + v)) hx

section StepDeriv

variable (C : StepClass d L N₁ m₁ k N ϱ) (z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))))

/-- **The `t`-derivative of the label term along the marked tangent is the sum of the `t`-derivatives
of the localized terms.**  Let `𝒴` be a finite set of domains and `Ev Y u t (Θ, ψ̂)` terms such that,
for the marks `(u, t)` of a neighbourhood of `(u, 0)`, the functional `flComp` of the label at the
raw data of the step and the masked tangent `markedTangDec … (blockU z) u t S.D' (yhat x)` is
`∑_{Y ∈ 𝒴} Ev Y u t (rawOf S.D', yhat x)`, each term being differentiable in `t` at `0`.  Then
`d/dt|₀ ℰ^{(j)}(y, X; pair_j(ψ^{(k)} + u ψ' + t M_z ψ'))`, the label term along the marked tangent
of the step, is `β ∑_Y d/dt|₀ Ev Y u t (rawOf S.D', yhat x)`.  The identification of the masked
decoupled tangent with the marked tangent of the step is `markedTangDec_eq_liftC_markedTangentC`,
and that of `flComp` with the label term is `classOldEndpoint_liftC`. -/
theorem deriv_classLabel_marked_eq_sum
    {P : Consts} {Dom : FieldDom d L N₁ m₁ (k + 1) N ϱ}
    (hcl : SFTermClauses P Dom C.Tm) {j : ℕ} (hj1 : 1 ≤ j) (hjk : j ≤ k)
    {y : CTorus d L N₁ m₁ (k + 1)} {X : Set (CTorus d L N₁ m₁ (k + 1))}
    {Gj : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
    (hS : GsSpecStrong j (hjk.trans (Nat.le_succ k)) X Gj)
    {c BG κ eps Kc Cx c₂ BG₂ δ₁ r₀ δ₃ δfl : ℝ}
    {X₀ X₁f : Finset (CTorus d L N₁ m₁ (k + 1))} {j₁ : ℕ}
    (hB : BgSetting N S.G' (stepG d L N₁ m₁ k ϱ) Gj S.a₁ S.ν c BG κ r₀ eps δ₃ X₀ X₁f j₁)
    (hF : FlSetting N S.G' (stepG d L N₁ m₁ k ϱ) (stepG d L N₁ m₁ k ϱ) S.a₁ S.ν κ BG eps δ₃ Kc Cx
      c₂ BG₂ δ₁ δfl X₁f)
    (hD : XiCData S.G' S.a S.ν (k + 1) 1 eps S.D')
    (𝒴 : Finset (Set (CTorus d L N₁ m₁ (k + 1))))
    (Ev : Set (CTorus d L N₁ m₁ (k + 1)) → ℂ → ℂ →
      RawData d L (N₁ * L ^ m₁) (k + 1) N × (unitPts S.G' × Fin N → ℂ) → ℂ)
    (u : ℂ) (x : S.E) {B : ℝ}
    (hsum : ∀ t : ℂ, (‖u‖ + ‖t‖) * B < δ₁ →
      flComp hB hF (fun r => (S.β : ℂ)⁻¹ * C.Tm.E j y X r.1 r.2)
        (rawOf S.D', markedTangDec S.hG' ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) S.a₁ S.ν
          (S.blockU z) u t S.D' (yhat x)) =
        ∑ Y ∈ 𝒴, Ev Y u t (rawOf S.D', yhat x))
    (hu0 : (‖u‖ + ‖(0 : ℂ)‖) * B < δ₁)
    (hdiff : ∀ Y ∈ 𝒴, DifferentiableAt ℂ (fun t : ℂ => Ev Y u t (rawOf S.D', yhat x)) 0)
    (hβ : (S.β : ℂ) ≠ 0) :
    deriv (fun t : ℂ => C.Tm.E j y X
        (composedPairAtC S.a S.ν (Nat.le_succ k) j
          (S.dataUC (S.psi0C + S.markedTangentC z u t x))).1
        (composedPairAtC S.a S.ν (Nat.le_succ k) j
          (S.dataUC (S.psi0C + S.markedTangentC z u t x))).2) 0 =
      (S.β : ℂ) * ∑ Y ∈ 𝒴, deriv (fun t : ℂ => Ev Y u t (rawOf S.D', yhat x)) 0 := by
  have hnhds : {t : ℂ | (‖u‖ + ‖t‖) * B < δ₁} ∈ nhds (0 : ℂ) := by
    refine (isOpen_lt (by fun_prop) continuous_const).mem_nhds ?_
    simpa using hu0
  have hev : (fun t : ℂ => C.Tm.E j y X
        (composedPairAtC S.a S.ν (Nat.le_succ k) j
          (S.dataUC (S.psi0C + S.markedTangentC z u t x))).1
        (composedPairAtC S.a S.ν (Nat.le_succ k) j
          (S.dataUC (S.psi0C + S.markedTangentC z u t x))).2) =ᶠ[nhds (0 : ℂ)]
      fun t => (S.β : ℂ) * ∑ Y ∈ 𝒴, Ev Y u t (rawOf S.D', yhat x) := by
    filter_upwards [hnhds] with t ht
    have h1 := classOldEndpoint_liftC S hcl hj1 hjk (y := y) hS hB hF hD (S.markedTangentC z u t x)
    rw [← S.markedTangDec_eq_liftC_markedTangentC z u t x, hsum t ht] at h1
    rw [h1, ← mul_assoc, mul_inv_cancel₀ hβ, one_mul]
  rw [hev.deriv_eq, deriv_const_mul _ (DifferentiableAt.fun_sum fun Y hY => hdiff Y hY),
    deriv_fun_sum fun Y hY => hdiff Y hY]

end StepDeriv


end StepSetting

section GenericMarks

/-- **Generic Y-mark identity (any generator, any expansion).**  If, for the marks `(u, t)` of a
neighbourhood of `(u, 0)`, a function `Fv t` (the functional `flComp` of the label along the
masked tangent) is both `β⁻¹ · Etil t` (the endpoint identity; `Etil t` the label term along the
marked tangent) and the finite sum `∑_{Y ∈ 𝒴} Ev Y t` of terms differentiable at `0`, then
`Etil'(0) = β ∑_Y (Ev Y)'(0)`.  Nothing here refers to the generator of the term. -/
theorem deriv_eq_sum_of_expansion {𝒴ι : Type*} (𝒴 : Finset 𝒴ι) (Ev : 𝒴ι → ℂ → ℂ)
    (Fv Etil : ℂ → ℂ) (β : ℂ) (hβ : β ≠ 0) {U : Set ℂ} (hU : U ∈ nhds (0 : ℂ))
    (hsum : ∀ t ∈ U, Fv t = ∑ Y ∈ 𝒴, Ev Y t) (hend : ∀ t ∈ U, Fv t = β⁻¹ * Etil t)
    (hdiff : ∀ Y ∈ 𝒴, DifferentiableAt ℂ (Ev Y) 0) :
    deriv Etil 0 = β * ∑ Y ∈ 𝒴, deriv (Ev Y) 0 := by
  have hev : Etil =ᶠ[nhds (0 : ℂ)] fun t => β * ∑ Y ∈ 𝒴, Ev Y t := by
    filter_upwards [hU] with t ht
    rw [← hsum t ht, hend t ht, ← mul_assoc, mul_inv_cancel₀ hβ, one_mul]
  rw [hev.deriv_eq, deriv_const_mul _ (DifferentiableAt.fun_sum fun Y hY => hdiff Y hY),
    deriv_fun_sum fun Y hY => hdiff Y hY]

/-- The mark `DEtil(u ψ')[M_z ψ']` is the `t`-derivative along the marked tangent when `Etil` is
differentiable at the base point (chain rule). -/
theorem hasDerivAt_comp_marked {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (f : E → ℂ) (p v : E) (hd : DifferentiableAt ℂ f p) :
    HasDerivAt (fun t : ℂ => f (p + t • v)) (fderiv ℂ f p v) 0 := by
  have hl : HasDerivAt (fun t : ℂ => p + t • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℂ)).smul_const v).const_add p
  have hd' : HasFDerivAt f (fderiv ℂ f p) (p + (0 : ℂ) • v) := by
    simpa using hd.hasFDerivAt
  exact hd'.comp_hasDerivAt (0 : ℂ) hl

end GenericMarks


section LabelExpansion

variable {Gp : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
  {Gk : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
  {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
  {a₁ ν c BG κ r₀ eps δ₃ : ℝ} {X₀ X₁f : Finset (CTorus d L N₁ m₁ (k + 1))}
  {Kc Cx c₂ BG₂ δ₁ δfl : ℝ} {X 𝒦X : Set (CTorus d L N₁ m₁ (k + 1))}

open Classical in
/-- **One inherited energy label expands over the decoupled domains along the masked tangent.**
For a label `(j, y, X)` of a class member `C`, `Eτ(r) = β⁻¹ ℰ^{(j)}(y, X; r.1, r.2)`, the
generator `𝔹_j(X)`, a mask `Zm` of unit points and marks `(um, tm)` of the radius set
`(‖um‖ + ‖tm‖) · √N · ‖cc‖ · C_sup · c_ψ < δ₁`, there is a family `Ev Y um tm (Θ, ψ̂)` of terms
with

1. the sum identity: `flComp Eτ` at the raw data `rawOf D` and the masked tangent
   `markedTangDec … Zm um tm D ψ̂` is `∑_{Y ∈ polymerDomains(X₁)} Ev Y um tm (rawOf D, ψ̂)`;
2. the locality of `Ev Y um tm` in `(Θ, ψ̂)` under `AgHatDir Y`, at equal marks;
3. the bound `β⁻¹ E₀ exp(-κ₀ d_j(X) - 2 κ_dec d(Y))`;
4. the analyticity of `(um, tm) ↦ Ev Y um tm u` on the radius set;
5. the Cauchy estimate of `∂_t Ev Y um t u |_{t=0}` by the bound over `t₀`;
6. the vanishing of `∂_t Ev Y um t u |_{t=0}` for every `Y` none of whose unit points lies in `Zm`.

The family is `evTerm … (FFmarked … Φ Zm um tm) Y` for `Φ` the old-term functional `eTermFun` of
`Eτ`, the pair `(F₁, Sol)` being the one of `i4b_analytic`, `Dec2.i4a_analytic`.  The hypotheses are
those of `classOldDec_expansion` with the radius condition `hδ₁` replaced by the radius set. -/
theorem classOldMarksY_expansion {P : Consts} {Dom : FieldDom d L N₁ m₁ (k + 1) N ϱ}
    (C : StepClass d L N₁ m₁ k N ϱ) (hm : P.m₀ = C.m₀) (hcl : SFTermClauses P Dom C.Tm)
    {β : ℝ} (hβ : 0 < β) (hE₀ : 0 ≤ P.E₀) {j : ℕ} (hj1 : 1 ≤ j) (hjk : j ≤ k)
    {y : CTorus d L N₁ m₁ (k + 1)} (hXp : IsPolyDom C.m₀ j X) (hy : y ∈ X)
    (hB : BgSetting N Gp Gk (C.Tm.gs j X) a₁ ν c BG κ r₀ eps δ₃ X₀ X₁f j)
    (hF : FlSetting N Gp Gk Hm a₁ ν κ BG eps δ₃ Kc Cx c₂ BG₂ δ₁ δfl X₁f)
    (hk : 1 ≤ k) (hG : IsLevel Hm k) (hG' : IsLevel Gp (k + 1)) (cc : ℂ)
    {cψ : ℝ} (hcψ : 0 ≤ cψ) (Zm : Finset (unitPts Gp))
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δc : ℝ}
    (hdm : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    (hcov : CovSetup Gp C.m₀ j X 𝒦X)
    (hX₁ : (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) = X1 Gp C.m₀ j 𝒦X)
    (hconn : HatConn Gp) (hrow : RowInHat (coverOf Gp) Hm (compWeight L a₁) ν)
    (hopt : ∃ (W₀ : Finset (CTorus d L N₁ m₁ (k + 1)))
      (E₀ : Finset (CTorus d L N₁ m₁ (k + 1) × CTorus d L N₁ m₁ (k + 1))),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ X) ∧ MeetsOne C.m₀ j 𝒦X W₀ ∧
        bondCost (scaleW L C.m₀ m₁ j) E₀ = treeLenCovOne C.m₀ j X)
    {κdec κ₀ : ℝ} (hκ₀ : 0 ≤ κ₀) (hκdec : 3 * κ₀ + 3 ≤ κdec)
    (hκ : 4 * d * (((2 * L + 1) ^ d : ℕ) : ℝ) * κdec ≤ κ) (h1 : 1 ≤ (κ / 2 - 1) / 2)
    (hlog : Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) * (((L ^ C.m₀) ^ d : ℕ) : ℝ)) ≤ (κ / 2 - 1) / 2)
    (hκP : κdec - 1 ≤ P.κ)
    (hchart : ∀ r ∈ XiCRaw (C.Tm.gs j X) (compWeight L a₁) ν j (scaledC0 d)
      (scaledC0 d ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl),
      Dom.dom j (C.Tm.gs j X) r.1 r.2) :
    ∃ Ev : Set (CTorus d L N₁ m₁ (k + 1)) → ℂ → ℂ →
        RawData d L (N₁ * L ^ m₁) (k + 1) N × (unitPts Gp × Fin N → ℂ) → ℂ,
      (∀ um tm : ℂ, (‖um‖ + ‖tm‖) *
        (Real.sqrt N * (‖cc‖ * (covSupConstC d L N (compWeight L a₁ k) κ * cψ))) < δ₁ →
        ∀ D : BgData Gp N, XiCData Gp (compWeight L a₁) ν (k + 1) 1 eps D →
        ∀ ψh : unitPts Gp × Fin N → ℂ, (∀ p, ‖ψh p‖ ≤ cψ) →
        flComp hB hF (fun r => (β : ℂ)⁻¹ * C.Tm.E j y X r.1 r.2)
          (rawOf D, markedTangDec hG' cc a₁ ν Zm um tm D ψh) =
        ∑ Y ∈ polymerDomains (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) => i.1.1)
          Gp C.m₀ (X1 Gp C.m₀ j 𝒦X), Ev Y um tm (rawOf D, ψh)) ∧
      (∀ um tm : ℂ, (‖um‖ + ‖tm‖) *
        (Real.sqrt N * (‖cc‖ * (covSupConstC d L N (compWeight L a₁ k) κ * cψ))) < δ₁ →
        ∀ Y, ∀ u ∈ XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
          {ψh : unitPts Gp × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ},
        ∀ u' ∈ XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
          {ψh : unitPts Gp × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ},
        AgHatDir hG' Y u u' → Ev Y um tm u = Ev Y um tm u') ∧
      (∀ um tm : ℂ, (‖um‖ + ‖tm‖) *
        (Real.sqrt N * (‖cc‖ * (covSupConstC d L N (compWeight L a₁ k) κ * cψ))) < δ₁ →
        ∀ Y, ∀ u ∈ XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
          {ψh : unitPts Gp × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ},
        ‖Ev Y um tm u‖ ≤ (β⁻¹ * P.E₀) *
          Real.exp (-κ₀ * treeLenCovOne C.m₀ j X - 2 * κdec * treeLenCov Gp C.m₀ Y)) ∧
      (∀ Y, ∀ u ∈ XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
          {ψh : unitPts Gp × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ},
        AnalyticOnNhd ℂ (fun w : ℂ × ℂ => Ev Y w.1 w.2 u)
          {w : ℂ × ℂ | (‖w.1‖ + ‖w.2‖) *
            (Real.sqrt N * (‖cc‖ * (covSupConstC d L N (compWeight L a₁ k) κ * cψ))) < δ₁}) ∧
      (∀ a b t₀ : ℝ, 0 ≤ a → 0 ≤ b → 0 < t₀ → t₀ ≤ b → (a + b) *
        (Real.sqrt N * (‖cc‖ * (covSupConstC d L N (compWeight L a₁ k) κ * cψ))) < δ₁ →
        ∀ um : ℂ, ‖um‖ ≤ a →
        ∀ Y, ∀ u ∈ XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
          {ψh : unitPts Gp × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ},
        ‖deriv (fun t : ℂ => Ev Y um t u) 0‖ ≤
          (β⁻¹ * P.E₀) *
            Real.exp (-κ₀ * treeLenCovOne C.m₀ j X - 2 * κdec * treeLenCov Gp C.m₀ Y) / t₀) ∧
      (∀ um : ℂ, (‖um‖ + ‖(0 : ℂ)‖) *
        (Real.sqrt N * (‖cc‖ * (covSupConstC d L N (compWeight L a₁ k) κ * cψ))) < δ₁ →
        ∀ Y : Set (CTorus d L N₁ m₁ (k + 1)), (∀ y ∈ Y, unitPt hG' y ∉ Zm) →
        ∀ u ∈ XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
          {ψh : unitPts Gp × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ},
        deriv (fun t : ℂ => Ev Y um t u) 0 = 0) ∧
      (∀ um : ℂ, (‖um‖ + ‖(0 : ℂ)‖) *
        (Real.sqrt N * (‖cc‖ * (covSupConstC d L N (compWeight L a₁ k) κ * cψ))) < δ₁ →
        ∀ Y : Set (CTorus d L N₁ m₁ (k + 1)),
        ∀ D : BgData Gp N, XiCData Gp (compWeight L a₁) ν (k + 1) 1 eps D →
        ∀ ψh ψh' : unitPts Gp × Fin N → ℂ, (∀ p, ‖ψh p‖ ≤ cψ) → (∀ p, ‖ψh' p‖ ≤ cψ) →
        (∀ y ∈ Y, ∀ i, ψh (unitPt hG' y, i) = ψh' (unitPt hG' y, i)) →
        deriv (fun t : ℂ => Ev Y um t (rawOf D, ψh)) 0 =
          deriv (fun t : ℂ => Ev Y um t (rawOf D, ψh')) 0) := by
  classical
  have hC := flCore_of hB hF
  obtain ⟨hEan, hEbd⟩ := classOldDecEnergy_chart (N := N) C hm hcl hβ hκP hE₀ a₁ ν δ₃ eps δfl hj1
    hjk hXp hy hchart
  have hEb : 0 ≤ β⁻¹ * P.E₀ := mul_nonneg (inv_nonneg.2 hβ.le) hE₀
  obtain ⟨Fk, hFkan, hFk⟩ := theorem72_analytic (G := Gk) (a := compWeight L a₁) (ν := ν) hB.HBk
  have hd0 : 0 < d := by have := hC.HBp.hd; omega
  have hB2 : 0 ≤ 2 * (K4 d L N BG κ * (xiC1 d * eps)) :=
    mul_nonneg (by norm_num) (mul_nonneg (K4_pos hC.hS.fam.2.1 hd0).le
      (by have := one_le_xiC1 d; have := hC.eps_pos; positivity))
  obtain ⟨F₁, hF₁an, hF₁⟩ := i4b_analytic hC.hS hC.Sp hC.HBp hC.hκ.le hC.hM
  obtain ⟨Sol, hSolan, hSolprop⟩ := Dec2.i4a_analytic (N := N) hC.hS2.fam hC.hS2.an
    hC.SM.toCoverBase hC.hκ.le hC.hM2 false hB2 hC.δ₁_pos.le hC.B_le hC.δ₁_le
  obtain ⟨e1, e2, e3, -, -, e6, e7, -, e9⟩ := i5_functional_hat_marked_exposed_pair_of hC hk hG
    hG' cc hcψ Zm hMX hdm hα hsm hcov hX₁ hopt hκ₀ hκdec hκ h1 hlog hEb
    (Φ := eTermFun Gp Gk (C.Tm.gs j X) Hm (compWeight L a₁) Fk
      (fun r => (β : ℂ)⁻¹ * C.Tm.E j y X r.1 r.2))
    (R := FlRealLC Gp Hm a₁ ν BG κ eps X₁f BG₂ δ₁)
    (eTermFun_analytic hB hF hFkan hFk hEan)
    (fun t ht a b s F₁' D ψh h => ⟨ht, h ▸ isLayerConstant_markedHatPsiF hG hG' cc F₁' Zm a b _ _ _⟩)
    (fun t ht => eTermFun_bound hB hF hFk hEbd ht)
    hconn hrow (Z := ↑X₁f) (Zα := ∅) subset_rfl (fun x hx => absurd hx (Set.notMem_empty x))
    (fun t _ t' _ hφ _ hδ hag hψ => eTermFun_local_dir hB hF hcov hX₁ Fk _ hφ hδ hag hψ)
    hF₁an hF₁ hSolan hSolprop
  refine ⟨fun Y um tm u => evTerm
    (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) => i.1.1) Gp C.m₀
    (X1 Gp C.m₀ j 𝒦X) (FFmarked X₁f a₁ ν hG' cc F₁ Sol
      (eTermFun Gp Gk (C.Tm.gs j X) Hm (compWeight L a₁) Fk
        (fun r => (β : ℂ)⁻¹ * C.Tm.E j y X r.1 r.2)) Zm um tm) Y u, ?_, e2, e3, e6, e7, ?_, ?_⟩
  · intro um tm hw D hD ψh hψh
    rw [← e1 um tm hw D hD ψh hψh]
    exact (eTermFun_value hB hF hFk _ hD
      (markedTangDec_mem_flBallLC hC hk hG hG' cc hcψ Zm hMX hdm hα hsm hw hD hψh)).symm
  · intro um h0 Y hY u hu
    have hnhds : {t : ℂ | (um, t) ∈ {w : ℂ × ℂ | (‖w.1‖ + ‖w.2‖) *
        (Real.sqrt N * (‖cc‖ * (covSupConstC d L N (compWeight L a₁ k) κ * cψ))) < δ₁}} ∈
        nhds (0 : ℂ) :=
      ((isOpen_markedRadiusSet _ δ₁).preimage
        (continuous_const.prodMk continuous_id)).mem_nhds h0
    have hev : (fun t : ℂ => evTerm
        (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) => i.1.1) Gp C.m₀
        (X1 Gp C.m₀ j 𝒦X) (FFmarked X₁f a₁ ν hG' cc F₁ Sol
          (eTermFun Gp Gk (C.Tm.gs j X) Hm (compWeight L a₁) Fk
            (fun r => (β : ℂ)⁻¹ * C.Tm.E j y X r.1 r.2)) Zm um t) Y u) =ᶠ[nhds (0 : ℂ)]
        fun _ => evTerm
        (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) => i.1.1) Gp C.m₀
        (X1 Gp C.m₀ j 𝒦X) (FFmarked X₁f a₁ ν hG' cc F₁ Sol
          (eTermFun Gp Gk (C.Tm.gs j X) Hm (compWeight L a₁) Fk
            (fun r => (β : ℂ)⁻¹ * C.Tm.E j y X r.1 r.2)) Zm um 0) Y u := by
      filter_upwards [hnhds] with t ht
      exact e9 um t 0 ht h0 Y hY u hu
    rw [hev.deriv_eq]
    simp
  · intro um h0 Y D hD ψh ψh' hψh hψh' hag
    have hnhds : {t : ℂ | (um, t) ∈ {w : ℂ × ℂ | (‖w.1‖ + ‖w.2‖) *
        (Real.sqrt N * (‖cc‖ * (covSupConstC d L N (compWeight L a₁ k) κ * cψ))) < δ₁}} ∈
        nhds (0 : ℂ) :=
      ((isOpen_markedRadiusSet _ δ₁).preimage
        (continuous_const.prodMk continuous_id)).mem_nhds h0
    refine Filter.EventuallyEq.deriv_eq ?_
    filter_upwards [hnhds] with t ht
    exact e2 um t ht Y (rawOf D, ψh) ⟨⟨D, hD, rfl⟩, hψh⟩ (rawOf D, ψh') ⟨⟨D, hD, rfl⟩, hψh'⟩
      ⟨agreeOn_refl _ _, hag⟩

end LabelExpansion


end Balaban.Fluctuation
