/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.GeneralClassPathAnalytic
public import Balaban.Fluctuation.StepComplexSource
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Complex regularity of a general class on an open neighbourhood (package `GeneralClassRegularC`)

The complex fluctuation step needs the step exponent `Φ₁ = -β_k V^{(k)} + δℰ_k` to be
complex-differentiable on an open neighbourhood of the shifted fluctuation ball
(`ClassRegularLocC`), and the components of the observable vector to be `C¹` families in the
interpolation parameter (`ClassRegularObsC`).  The landed producers are for the class with zero old
terms.  Here both are proved for a general class from the analyticity clauses of the class and one
named open-domain hypothesis.

* `StepSetting.OldXiDomOpenC S C Dom`: there is an open set `O` of complex shifts `ψ'` containing
  the points `s ψ'(ψ̂)`, `s ∈ [0,1]`, `‖ψ̂‖ ≤ p₁`, such that for every `ψ' ∈ O`, every scale
  `1 ≤ j ≤ k` and every old polymer `X` of scale `j`, the composed pair of old fields of the complex
  old spin `ψ^{(k)} + ψ'` lies in the complex domain `Dom.dom j (C.Tm.gs j X)` of the class.
  `oldXiDomC_of_oldXiDomOpenC`: it implies the hypothesis `OldXiDomC` at the real path points.
* `analyticAt_composedPairAtC_shift`: on the shifts of `shiftDomC p⁺` the composed pair of old
  fields is an analytic function of the shift (Theorem 7.2, analyticity, and the composition of
  fields).
* `analyticAt_dEC_shift`: the old-energy part `δℰ_k` is analytic in the shift at every point where
  the composed pair lies in the class domain.
* `classRegularLocC_of_oldXiDomOpenC`, `classRegularObsC_of_oldXiDomOpenC`: `ClassRegularLocC` and
  `ClassRegularObsC` for a member `IsSF2` of the class matched to the step (`ClassParamMatch`),
  from `OldXiDomOpenC`; the source condition `‖g‖₁ < 1` of the clause `analyticM` is a premise.
  The `_of_clauses` forms take the two analyticity clauses themselves, so that the zero class (no
  old terms) is covered without a membership in `IsSF2`.
* `oldXiDomOpenC_zeroClass`, `nonempty_oldXiDomOpenC_zeroClass`: the hypothesis holds for the zero
  class (trivially: no old terms are tested), and the zero-class producers are recovered.

Not proved here.  `OldXiDomOpenC` is not proved on the physical chart (it needs the class-radius
inequalities of `GENERAL.md` §1 and a neighbourhood version of them).  The identification of the
step exponent with the hat functionals and the activity bound for a general class are a separate
package in progress.  Nothing here depends on which generating sets the class terms use: the sets
`C.Tm.gs j X` enter only through the domain `Dom.dom j (C.Tm.gs j X)`.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization
  Balaban.SmallField Balaban.SmallField.Def6 Balaban.SmallField.Def6v2 Finset MeasureTheory Set

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}

namespace StepSetting

/-- **The open domain hypothesis of the complex step** (open-neighbourhood form of `OldXiDomC`):
there is an open set `O` of complex shifts `ψ'` of the unit lattice containing the points
`s ψ'(ψ̂)` (`s ∈ [0,1]`, `‖ψ̂‖ ≤ p₁`, `ψ'(ψ̂) = shiftUC ψ̂`) such that for every `ψ' ∈ O`, every
scale `1 ≤ j ≤ k` and every old polymer `X` of scale `j`, the composed pair of old fields of the
complex old spin `ψ^{(k)} + ψ'` lies in the complex domain `Dom.dom j (C.Tm.gs j X)` of the class. -/
def OldXiDomOpenC (S : StepSetting d L N₁ m₁ k N ϱ) (C : StepClass d L N₁ m₁ k N ϱ)
    (Dom : FieldDom d L N₁ m₁ (k + 1) N ϱ) : Prop :=
  ∃ O : Set S.EC, IsOpen O ∧
    (∀ x : S.E, ‖x‖ ≤ S.p₁ → ∀ s ∈ Icc (0 : ℝ) 1, (s : ℂ) • S.shiftUC x ∈ O) ∧
    ∀ y ∈ O, ∀ j ∈ Finset.Icc 1 k, ∀ X, IsPolyDom C.m₀ j X →
      Dom.dom j (C.Tm.gs j X)
        (composedPairAtC S.a S.ν (Nat.le_succ k) j (S.dataUC (S.psi0C + y))).1
        (composedPairAtC S.a S.ν (Nat.le_succ k) j (S.dataUC (S.psi0C + y))).2

variable (S : StepSetting d L N₁ m₁ k N ϱ) (C : StepClass d L N₁ m₁ k N ϱ)
  {Dom : FieldDom d L N₁ m₁ (k + 1) N ϱ}

/-- The open-neighbourhood hypothesis restricts to the real path points: `OldXiDomOpenC → OldXiDomC`. -/
theorem oldXiDomC_of_oldXiDomOpenC (h : S.OldXiDomOpenC C Dom) : S.OldXiDomC C Dom := by
  obtain ⟨O, -, hmem, hdom⟩ := h
  intro s hs x hx j hj X hX
  exact hdom _ (hmem x hx s hs) j hj X hX

section Chart

variable {c BG κ eps Kc Cx c₂ BG₂ δ₁ δc : ℝ}
  (hC : FlCore N S.G' (stepG d L N₁ m₁ k ϱ) S.a₁ S.ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
  (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
  (hdm : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
  (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
  (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
  (ha₁ : 0 < S.a₁) (hc7 : c7 d L N BG κ ≤ thm73C3 d L N) {R : ℝ} (hR : 1 < R)
  (hsmR : 2 * (compC4 d * (bgK1 d L N * (xiC1 d * eps))) + 5 * (R * δ₁) ≤ bgC1 d L N)
  (hβ : 0 < S.β) {pp : ℝ} (hpp : 0 < pp)
  (hδ₁ : Real.sqrt N * (S.betaU ^ (-(1 / 2 : ℝ)) *
    (covSupConstC d L N (compWeight L S.a₁ k) κ * pp)) < δ₁)
  (hD : XiCData S.G' S.a S.ν (k + 1) 1 eps S.D')

include hC hMX hdm hα hsm ha₁ hc7 hR hsmR hβ hpp hδ₁ hD in
/-- **The composed pair of old fields `(ψ_k^{(j)}, h)` is analytic in the complex shift** on
`shiftDomC p⁺` (Theorem 7.2, analyticity of the small solution, composed with the affine map
`ψ' ↦ ψ^{(k)} + ψ'` and the composition of fields), for every scale `j`. -/
theorem analyticAt_composedPairAtC_shift {y₀ : S.EC} (hy₀ : y₀ ∈ S.shiftDomC pp) (j : ℕ) :
    AnalyticAt ℂ (fun y : S.EC =>
      composedPairAtC S.a S.ν (Nat.le_succ k) j (S.dataUC (S.psi0C + y))) y₀ := by
  classical
  obtain ⟨F, hFan, hF⟩ := S.exists_analytic_bgC_shift hC hMX hdm hα hsm ha₁ hc7 hR hsmR hβ hpp
    hδ₁ hD
  have hFat := hFan y₀ hy₀
  have hraw := S.analyticAt_rawUC_shift y₀
  by_cases hj : j ≤ k
  · have hjl : j ≤ k + 1 := hj.trans (Nat.le_succ k)
    have hmodel : AnalyticAt ℂ (fun y : S.EC =>
        (((fun x i => composeField
          (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ) j hjl)
          (stepG d L N₁ m₁ k ϱ) S.a (F y).1 (S.rawUC (S.psi0C + y)).1 x i),
        (fun x i => if x ∈ (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1)
          (ϱ := ϱ) j hjl).Ω 1 then (S.rawUC (S.psi0C + y)).2 x i else 0)) :
          Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N)) y₀ := by
      refine AnalyticAt.prod (analyticAt_pi_iff.2 fun x => analyticAt_pi_iff.2 fun i => ?_)
        (analyticAt_pi_iff.2 fun x => analyticAt_pi_iff.2 fun i => ?_)
      · exact analyticAt_composeField (G := levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
          (k := k + 1) (ϱ := ϱ) j hjl) (G' := stepG d L N₁ m₁ k ϱ) S.a
          (fun y => (F y).1) (fun y => (S.rawUC (S.psi0C + y)).1)
          (fun r => analyticAt_pi_iff.1 (analyticAt_fst.comp hFat) r)
          (fun y' j' => analyticAt_pi_iff.1 (analyticAt_pi_iff.1
            (analyticAt_fst.comp hraw) y') j') x i
      · by_cases hx : x ∈ (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1)
            (ϱ := ϱ) j hjl).Ω 1
        · simp only [hx, ↓reduceIte]
          exact analyticAt_pi_iff.1 (analyticAt_pi_iff.1 (analyticAt_snd.comp hraw) x) i
        · simp only [hx, ↓reduceIte]
          exact analyticAt_const
    refine hmodel.congr ?_
    filter_upwards [(S.isOpen_shiftDomC pp).mem_nhds hy₀] with y hy
    unfold composedPairAtC
    simp only [hj, ↓reduceDIte]
    have hFy := congrArg Prod.fst (hF y hy)
    show _ = ((fun x i => composeField _ (stepG d L N₁ m₁ k ϱ) S.a
        (bgFieldC (stepG d L N₁ m₁ k ϱ) S.a S.ν (bgC0 d L N) (S.dataUC (S.psi0C + y)))
        (S.dataUC (S.psi0C + y)).Ψ x i),
      (fun x i => if x ∈ (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1)
        (ϱ := ϱ) j hjl).Ω 1 then (S.dataUC (S.psi0C + y)).h x i else 0))
    have hΨ : (S.rawUC (S.psi0C + y)).1 = (S.dataUC (S.psi0C + y)).Ψ :=
      congrArg Prod.fst (S.dataUC_raw _).symm
    have hh : (S.rawUC (S.psi0C + y)).2 = (S.dataUC (S.psi0C + y)).h :=
      congrArg Prod.snd (S.dataUC_raw _).symm
    simp only [hΨ, hh, hFy]
  · have : (fun y : S.EC => composedPairAtC S.a S.ν (Nat.le_succ k) j
        (S.dataUC (S.psi0C + y))) = fun _ => (0, 0) := by
      funext y
      unfold composedPairAtC
      simp only [hj, ↓reduceDIte]
    rw [this]
    exact analyticAt_const

end Chart

/-- A density `ℰ^{(j)}` of a class is analytic at a pair of old fields lying in the class domain of
every polymer of scale `j`, by the clause `analyticE`. -/
theorem analyticAt_Edens_of_clauses
    (hE : ∀ j, 1 ≤ j → j ≤ k + 1 → ∀ y X, IsPolyDom C.m₀ j X → y ∈ X →
      AnalyticOnNhd ℂ (fun p : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N =>
        C.Tm.E j y X p.1 p.2) {p | Dom.dom j (C.Tm.gs j X) p.1 p.2})
    {j : ℕ} (hj : j ∈ Finset.Icc 1 k)
    {p : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N}
    (hp : ∀ X, IsPolyDom C.m₀ j X → Dom.dom j (C.Tm.gs j X) p.1 p.2) :
    AnalyticAt ℂ (fun q : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N =>
      Edens C.m₀ C.Tm j q.1 q.2) p := by
  have hj' := Finset.mem_Icc.1 hj
  unfold Edens
  refine Finset.analyticAt_fun_sum _ fun y _ => ?_
  unfold Eloc
  refine analyticAt_finsum_polysAt (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) C.m₀ j y
    (fun X (q : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N) => C.Tm.E j y X q.1 q.2)
    fun X hX hy => ?_
  exact hE j hj'.1 (hj'.2.trans (Nat.le_succ k)) y X hX hy p (hp X hX)

section Chart

variable {c BG κ eps Kc Cx c₂ BG₂ δ₁ δc : ℝ}
  (hC : FlCore N S.G' (stepG d L N₁ m₁ k ϱ) S.a₁ S.ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
  (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
  (hdm : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
  (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
  (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
  (ha₁ : 0 < S.a₁) (hc7 : c7 d L N BG κ ≤ thm73C3 d L N) {R : ℝ} (hR : 1 < R)
  (hsmR : 2 * (compC4 d * (bgK1 d L N * (xiC1 d * eps))) + 5 * (R * δ₁) ≤ bgC1 d L N)
  (hβ : 0 < S.β) {pp : ℝ} (hpp : 0 < pp)
  (hδ₁ : Real.sqrt N * (S.betaU ^ (-(1 / 2 : ℝ)) *
    (covSupConstC d L N (compWeight L S.a₁ k) κ * pp)) < δ₁)
  (hD : XiCData S.G' S.a S.ν (k + 1) 1 eps S.D')

include hC hMX hdm hα hsm ha₁ hc7 hR hsmR hβ hpp hδ₁ hD in
/-- **The old-energy part `δℰ_k(ψ^{(k)} + ψ')` is analytic in the complex shift** at every shift of
`shiftDomC p⁺` at which the composed pairs lie in the class domains. -/
theorem analyticAt_dEC_shift
    (hE : ∀ j, 1 ≤ j → j ≤ k + 1 → ∀ y X, IsPolyDom C.m₀ j X → y ∈ X →
      AnalyticOnNhd ℂ (fun p : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N =>
        C.Tm.E j y X p.1 p.2) {p | Dom.dom j (C.Tm.gs j X) p.1 p.2})
    {y₀ : S.EC} (hy₀ : y₀ ∈ S.shiftDomC pp)
    (hdom : ∀ j ∈ Finset.Icc 1 k, ∀ X, IsPolyDom C.m₀ j X →
      Dom.dom j (C.Tm.gs j X)
        (composedPairAtC S.a S.ν (Nat.le_succ k) j (S.dataUC (S.psi0C + y₀))).1
        (composedPairAtC S.a S.ν (Nat.le_succ k) j (S.dataUC (S.psi0C + y₀))).2) :
    AnalyticAt ℂ (fun y : S.EC => S.dEC C (S.psi0C + y)) y₀ := by
  unfold dEC
  refine AnalyticAt.sub ?_ analyticAt_const
  unfold EcompAtC
  refine Finset.analyticAt_fun_sum _ fun j hj => ?_
  exact (analyticAt_Edens_of_clauses C hE hj (hdom j hj)).comp_of_eq
    (S.analyticAt_composedPairAtC_shift hC hMX hdm hα hsm ha₁ hc7 hR hsmR hβ hpp hδ₁ hD hy₀ j) rfl

include hC hMX hdm hα hsm ha₁ hc7 hR hsmR hβ hpp hδ₁ hD in
/-- **`ClassRegularLocC` for a general class, from the analyticity clause `analyticE` and
`OldXiDomOpenC`** (complex chart, `β > 0`, `p₁ < p⁺`): `Φ₁ = -β_k V^{(k)} + δℰ_k` is analytic on the
open set `O ∩ shiftDomC p⁺`, which contains the segments of the path. -/
theorem classRegularLocC_of_clauses
    (hE : ∀ j, 1 ≤ j → j ≤ k + 1 → ∀ y X, IsPolyDom C.m₀ j X → y ∈ X →
      AnalyticOnNhd ℂ (fun p : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N =>
        C.Tm.E j y X p.1 p.2) {p | Dom.dom j (C.Tm.gs j X) p.1 p.2})
    (hO : S.OldXiDomOpenC C Dom) (hlt : S.p₁ < pp) : S.ClassRegularLocC C := by
  obtain ⟨O, hOo, hmem, hdom⟩ := hO
  have hdet := S.isUnit_det_covSqrtC hC hMX hdm hα hsm hD
  have hcc := S.betaU_rpow_ne_zero hβ
  refine ⟨O ∩ S.shiftDomC pp, hOo.inter (S.isOpen_shiftDomC pp), ?_, fun x hx s hs => ?_⟩
  · refine AnalyticOnNhd.contDiffOn_of_completeSpace (fun y hy => ?_)
    have h1 := (analyticAt_const (v := -(S.β : ℂ))).mul
      (S.analyticAt_VkC_shift hC hMX hdm hα hsm ha₁ hc7 hR hsmR hβ hpp hδ₁ hD hy.2)
    have h2 := S.analyticAt_dEC_shift C hC hMX hdm hα hsm ha₁ hc7 hR hsmR hβ hpp hδ₁ hD hE hy.2
      (hdom y hy.1)
    exact h1.add h2
  · refine ⟨hmem x hx s hs, S.smul_shiftUC_mem_shiftDomC hdet hcc ?_⟩
    have hs' : |s| ≤ 1 := by rw [abs_of_nonneg hs.1]; exact hs.2
    calc |s| * ‖x‖ ≤ 1 * S.p₁ := mul_le_mul hs' hx (norm_nonneg _) zero_le_one
      _ < pp := by rw [one_mul]; exact hlt

end Chart

/-! ### The truncated family, on a neighbourhood of `[0,1]` given by a tube -/

section Trunc

/-- **A function `C¹` at the points `(s, ψ̂)`, `s ∈ [-ε, 1+ε]`, `‖ψ̂‖ ≤ p₁`, gives a `C¹` family on
a neighbourhood of `[0,1]`**, bounded with its derivative on the support of `ν_{p₁}`; the variant of
`isC1Family_trunc` with the smoothness region given by `ε` instead of by the radius `p⁺`. -/
theorem isC1Family_trunc_of_nhds {f : ℝ × S.E → ℂ} {ε : ℝ} (hp₁ : 0 < S.p₁) (hε0 : 0 < ε)
    (hCD : ∀ s ∈ Set.Icc (-ε) (1 + ε), ∀ x : S.E, ‖x‖ ≤ S.p₁ → ContDiffAt ℝ 1 f (s, x)) :
    ∃ U : Set ℝ, IsC1Family U (S.truncF f) (S.dtruncF f) := by
  classical
  have hball : ∀ x : S.E, chiFl S.U N S.p₁ x = 1 → ‖x‖ ≤ S.p₁ := fun x hx =>
    ((chiFl_eq_one_iff hp₁ x).1 hx).le
  have hIcc : ∀ s ∈ Set.Ioo (-ε) (1 + ε), s ∈ Set.Icc (-ε) (1 + ε) :=
    fun s hs => ⟨hs.1.le, hs.2.le⟩
  have hcont : ∀ s ∈ Set.Icc (-ε) (1 + ε), ∀ x : S.E, ‖x‖ ≤ S.p₁ →
      ContinuousAt f (s, x) := fun s hs x hx => (hCD s hs x hx).continuousAt
  have hcontd : ∀ s ∈ Set.Icc (-ε) (1 + ε), ∀ x : S.E, ‖x‖ ≤ S.p₁ →
      ContinuousAt (fun q : ℝ × S.E => (fderiv ℝ f q) (1, 0)) (s, x) := by
    intro s hs x hx
    have h1 : ContDiffAt ℝ 0 (fderiv ℝ f) (s, x) :=
      (hCD s hs x hx).fderiv_right (m := 0) (by norm_num)
    have h2 : ContinuousAt (fderiv ℝ f) (s, x) := h1.continuousAt
    exact (ContinuousLinearMap.apply ℝ ℂ ((1 : ℝ), (0 : S.E))).continuous.continuousAt.comp h2
  have hslice : ∀ s ∈ Set.Icc (-ε) (1 + ε), ∀ x : S.E, ‖x‖ ≤ S.p₁ →
      ContinuousAt (fun x : S.E => f (s, x)) x := fun s hs x hx =>
    (hcont s hs x hx).comp (Continuous.prodMk_right s).continuousAt
  have hslice' : ∀ s ∈ Set.Icc (-ε) (1 + ε), ∀ x : S.E, ‖x‖ ≤ S.p₁ →
      ContinuousAt (fun x : S.E => (fderiv ℝ f (s, x)) (1, 0)) x := fun s hs x hx =>
    (hcontd s hs x hx).comp (Continuous.prodMk_right s).continuousAt
  have hmeasB : MeasurableSet {x : S.E | chiFl S.U N S.p₁ x = 1} :=
    (measurable_chiFl S.p₁) (measurableSet_singleton 1)
  refine ⟨Set.Ioo (-ε) (1 + ε), ?_⟩
  refine
    { isOpen := isOpen_Ioo
      Icc_subset := fun s hs => ⟨by linarith [hs.1], by linarith [hs.2]⟩
      measurable := ?_
      measurable' := ?_
      hasDerivAt := ?_
      continuousOn := ?_
      bound := ?_ }
  · intro s hs
    have hs' := hIcc s hs
    have hpw : S.truncF f s = Set.piecewise {x : S.E | chiFl S.U N S.p₁ x = 1}
        (fun x => f (s, x)) 0 := by
      funext x
      by_cases hx : chiFl S.U N S.p₁ x = 1
      · simp [truncF, Set.piecewise, hx]
      · simp [truncF, Set.piecewise, hx]
    rw [hpw]
    refine ContinuousOn.measurable_piecewise (fun x hx => ?_) continuousOn_const hmeasB
    exact (hslice s hs' x (hball x hx)).continuousWithinAt
  · intro s hs
    have hs' := hIcc s hs
    have hpw : S.dtruncF f s = Set.piecewise {x : S.E | chiFl S.U N S.p₁ x = 1}
        (fun x => (fderiv ℝ f (s, x)) (1, 0)) 0 := by
      funext x
      by_cases hx : chiFl S.U N S.p₁ x = 1
      · simp [dtruncF, Set.piecewise, hx]
      · simp [dtruncF, Set.piecewise, hx]
    rw [hpw]
    refine ContinuousOn.measurable_piecewise (fun x hx => ?_) continuousOn_const hmeasB
    exact (hslice' s hs' x (hball x hx)).continuousWithinAt
  · intro x s hs
    have hs' := hIcc s hs
    by_cases hx : chiFl S.U N S.p₁ x = 1
    · have hfun : (fun r => S.truncF f r x) = fun r => f (r, x) := by
        funext r; simp [truncF, hx]
      have hd : DifferentiableAt ℝ f (s, x) := (hCD s hs' x (hball x hx)).differentiableAt
        (by simp)
      have h1 : HasDerivAt (fun r : ℝ => f (r, x)) ((fderiv ℝ f (s, x)) (1, 0)) s := by
        have hp : HasDerivAt (fun r : ℝ => ((r, x) : ℝ × S.E)) ((1 : ℝ), (0 : S.E)) s :=
          (hasDerivAt_id s).prodMk (hasDerivAt_const s x)
        exact hd.hasFDerivAt.comp_hasDerivAt s hp
      rw [hfun]
      simp only [dtruncF, hx, ↓reduceIte]
      exact h1
    · simp only [truncF, dtruncF, hx, ↓reduceIte]
      exact hasDerivAt_const s 0
  · intro x
    by_cases hx : chiFl S.U N S.p₁ x = 1
    · have hfun : (fun s => S.dtruncF f s x) = fun s => (fderiv ℝ f (s, x)) (1, 0) := by
        funext s; simp [dtruncF, hx]
      rw [hfun]
      refine fun s hs => ?_
      have hs' : s ∈ Set.Icc (-ε) (1 + ε) := ⟨by linarith [hs.1], by linarith [hs.2]⟩
      have := (hcontd s hs' x (hball x hx)).comp (f := fun s : ℝ => ((s, x) : ℝ × S.E))
        (continuous_id.prodMk continuous_const).continuousAt
      exact this.continuousWithinAt
    · have : (fun s => S.dtruncF f s x) = fun _ => 0 := by
        funext s; simp [dtruncF, hx]
      rw [this]
      exact continuousOn_const
  · have hKc : IsCompact (Set.Icc (-ε) (1 + ε) ×ˢ Metric.closedBall (0 : S.E) S.p₁) :=
      isCompact_Icc.prod (isCompact_closedBall _ _)
    have hKm : ∀ q ∈ Set.Icc (-ε) (1 + ε) ×ˢ Metric.closedBall (0 : S.E) S.p₁,
        q.1 ∈ Set.Icc (-ε) (1 + ε) ∧ ‖q.2‖ ≤ S.p₁ := fun q hq =>
      ⟨hq.1, by simpa using hq.2⟩
    obtain ⟨M₀, hM₀⟩ := hKc.exists_bound_of_continuousOn
      (f := f) (fun q hq => (hcont q.1 (hKm q hq).1 q.2 (hKm q hq).2).continuousWithinAt)
    obtain ⟨M₁, hM₁⟩ := hKc.exists_bound_of_continuousOn
      (f := fun q : ℝ × S.E => (fderiv ℝ f q) (1, 0))
      (fun q hq => (hcontd q.1 (hKm q hq).1 q.2 (hKm q hq).2).continuousWithinAt)
    refine ⟨max M₀ 0 + max M₁ 0, fun x s hs => ?_⟩
    have hs' := hIcc s hs
    by_cases hx : chiFl S.U N S.p₁ x = 1
    · have hq : (s, x) ∈ Set.Icc (-ε) (1 + ε) ×ˢ Metric.closedBall (0 : S.E) S.p₁ :=
        ⟨hs', by simpa using hball x hx⟩
      refine ⟨?_, ?_⟩
      · simp only [truncF, hx, ↓reduceIte]
        exact (hM₀ _ hq).trans ((le_max_left _ _).trans
          (le_add_of_nonneg_right (le_max_right _ _)))
      · simp only [dtruncF, hx, ↓reduceIte]
        exact (hM₁ _ hq).trans ((le_max_left _ _).trans
          (le_add_of_nonneg_left (le_max_right _ _)))
    · simp only [truncF, dtruncF, hx, ↓reduceIte, norm_zero]
      exact ⟨by positivity, by positivity⟩

end Trunc

/-- **A tube around the path**: an open set of shifts containing the points `s ψ'(ψ̂)`,
`s ∈ [0,1]`, `‖ψ̂‖ ≤ p₁`, contains them also for `s ∈ [-ε, 1+ε]`, for some `ε > 0`
(compactness of `[0,1] × {‖ψ̂‖ ≤ p₁}`). -/
theorem exists_tube {O : Set S.EC} (hO : IsOpen O)
    (hmem : ∀ x : S.E, ‖x‖ ≤ S.p₁ → ∀ s ∈ Icc (0 : ℝ) 1, (s : ℂ) • S.shiftUC x ∈ O) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ s ∈ Icc (-ε) (1 + ε), ∀ x : S.E, ‖x‖ ≤ S.p₁ →
      (s : ℂ) • S.shiftUC x ∈ O := by
  have hW : IsOpen {q : ℝ × S.E | (q.1 : ℂ) • S.shiftUC q.2 ∈ O} :=
    hO.preimage S.continuous_ray_shiftUC
  have hK : IsCompact (Icc (0 : ℝ) 1 ×ˢ Metric.closedBall (0 : S.E) S.p₁) :=
    isCompact_Icc.prod (isCompact_closedBall _ _)
  have hKW : Icc (0 : ℝ) 1 ×ˢ Metric.closedBall (0 : S.E) S.p₁ ⊆
      {q : ℝ × S.E | (q.1 : ℂ) • S.shiftUC q.2 ∈ O} := by
    rintro ⟨s, x⟩ ⟨hs, hx⟩
    exact hmem x (by simpa using hx) s hs
  obtain ⟨δ, hδ, hth⟩ := hK.exists_thickening_subset_open hW hKW
  refine ⟨δ / 2, half_pos hδ, fun s hs x hx => ?_⟩
  have hq : (s, x) ∈ Metric.thickening δ
      (Icc (0 : ℝ) 1 ×ˢ Metric.closedBall (0 : S.E) S.p₁) := by
    rw [Metric.mem_thickening_iff]
    refine ⟨(max 0 (min s 1), x), ⟨⟨le_max_left _ _, max_le zero_le_one (min_le_right _ _)⟩,
      by simpa using hx⟩, ?_⟩
    rw [Prod.dist_eq, dist_self, Real.dist_eq]
    have : |s - max 0 (min s 1)| ≤ δ / 2 := by
      rcases le_total s 0 with h0 | h0
      · rw [min_eq_left (h0.trans zero_le_one), max_eq_left h0, sub_zero,
          abs_of_nonpos h0]
        linarith [hs.1]
      · rcases le_total s 1 with h1 | h1
        · rw [min_eq_left h1, max_eq_right h0, sub_self, abs_zero]
          linarith [hδ]
        · rw [min_eq_right h1, max_eq_right zero_le_one, abs_of_nonneg (by linarith)]
          linarith [hs.2]
    rw [max_lt_iff]
    exact ⟨by linarith, hδ⟩
  exact hth hq

/-- The components `ℳ^{(j)}(x; ·, ·, g)_i` of a class are analytic at a pair of old fields lying in
the class domain of every polymer of scale `j`, for a fixed source `‖g‖₁ < 1`, by the clause
`analyticM`. -/
theorem analyticAt_Mloc_of_clauses
    (hM : ∀ j, 1 ≤ j → j ≤ k + 1 → ∀ x X, IsPolyDom C.m₀ j X → x ∈ X →
      AnalyticOnNhd ℂ (fun p : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N ×
          Fld d L N₁ m₁ (k + 1) N => C.Tm.M j x X p.1 p.2.1 p.2.2)
        {p | Dom.dom j (C.Tm.gs j X) p.1 p.2.1 ∧ Def6.l1 p.2.2 < 1})
    {g : Fld d L N₁ m₁ (k + 1) N} (hg : Def6.l1 g < 1) (x : CTorus d L N₁ m₁ (k + 1))
    {j : ℕ} (hj : j ∈ Finset.Icc 1 k)
    {p : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N}
    (hp : ∀ X, IsPolyDom C.m₀ j X → Dom.dom j (C.Tm.gs j X) p.1 p.2) :
    AnalyticAt ℂ (fun q : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N =>
      Mloc C.m₀ C.Tm j x q.1 q.2 g) p := by
  have hj' := Finset.mem_Icc.1 hj
  unfold Mloc
  refine analyticAt_finsum_polysAt (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) C.m₀ j x
    (fun X (q : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N) => C.Tm.M j x X q.1 q.2 g)
    fun X hX hx => ?_
  have h3 := hM j hj'.1 (hj'.2.trans (Nat.le_succ k)) x X hX hx (p.1, p.2, g) ⟨hp X hX, hg⟩
  have hmap : AnalyticAt ℂ (fun q : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N =>
      (q.1, q.2, g)) p :=
    AnalyticAt.prod analyticAt_fst (AnalyticAt.prod analyticAt_snd analyticAt_const)
  exact h3.comp_of_eq hmap rfl

section ChartObs

variable {c BG κ eps Kc Cx c₂ BG₂ δ₁ δc : ℝ}
  (hC : FlCore N S.G' (stepG d L N₁ m₁ k ϱ) S.a₁ S.ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
  (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
  (hdm : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
  (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
  (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
  (ha₁ : 0 < S.a₁) (hc7 : c7 d L N BG κ ≤ thm73C3 d L N) {R : ℝ} (hR : 1 < R)
  (hsmR : 2 * (compC4 d * (bgK1 d L N * (xiC1 d * eps))) + 5 * (R * δ₁) ≤ bgC1 d L N)
  (hβ : 0 < S.β) {pp : ℝ} (hpp : 0 < pp)
  (hδ₁ : Real.sqrt N * (S.betaU ^ (-(1 / 2 : ℝ)) *
    (covSupConstC d L N (compWeight L S.a₁ k) κ * pp)) < δ₁)
  (hD : XiCData S.G' S.a S.ν (k + 1) 1 eps S.D')

include hC hMX hdm hα hsm ha₁ hc7 hR hsmR hβ hpp hδ₁ hD in
/-- **The components of `ℳ_k(ψ^{(k)} + ψ'; g)` are analytic in the complex shift** at every shift of
`shiftDomC p⁺` at which the composed pairs lie in the class domains (the small solution `φ_k` and
the terms `ℳ^{(j)}`, for a source `‖g‖₁ < 1`). -/
theorem analyticAt_McompAtC_shift
    (hM : ∀ j, 1 ≤ j → j ≤ k + 1 → ∀ x X, IsPolyDom C.m₀ j X → x ∈ X →
      AnalyticOnNhd ℂ (fun p : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N ×
          Fld d L N₁ m₁ (k + 1) N => C.Tm.M j x X p.1 p.2.1 p.2.2)
        {p | Dom.dom j (C.Tm.gs j X) p.1 p.2.1 ∧ Def6.l1 p.2.2 < 1})
    {g : Fld d L N₁ m₁ (k + 1) N} (hg : Def6.l1 g < 1)
    {y₀ : S.EC} (hy₀ : y₀ ∈ S.shiftDomC pp)
    (hdom : ∀ j ∈ Finset.Icc 1 k, ∀ X, IsPolyDom C.m₀ j X →
      Dom.dom j (C.Tm.gs j X)
        (composedPairAtC S.a S.ν (Nat.le_succ k) j (S.dataUC (S.psi0C + y₀))).1
        (composedPairAtC S.a S.ν (Nat.le_succ k) j (S.dataUC (S.psi0C + y₀))).2)
    (x : CTorus d L N₁ m₁ (k + 1)) (i : Fin N) :
    AnalyticAt ℂ (fun y : S.EC =>
      McompAtC C.m₀ C.Tm S.a S.ν (Nat.le_succ k) (S.dataUC (S.psi0C + y)) g x i) y₀ := by
  obtain ⟨F, hFan, hF⟩ := S.exists_analytic_bgC_shift hC hMX hdm hα hsm ha₁ hc7 hR hsmR hβ hpp
    hδ₁ hD
  have hFat := hFan y₀ hy₀
  unfold McompAtC
  refine AnalyticAt.add ?_ ?_
  · have h1 : AnalyticAt ℂ (fun y : S.EC =>
        (F y).1 (⟨x, (S.hG x).1⟩, i)) y₀ :=
      analyticAt_pi_iff.1 (analyticAt_fst.comp hFat) _
    refine h1.congr ?_
    filter_upwards [(S.isOpen_shiftDomC pp).mem_nhds hy₀] with y hy
    show (F y).1 (⟨x, (S.hG x).1⟩, i) = svec (stepG d L N₁ m₁ k ϱ)
      (bgFieldC (stepG d L N₁ m₁ k ϱ) S.a S.ν (bgC0 d L N) (S.dataUC (S.psi0C + y))) x i
    rw [S.svec_stepG, hF y hy]
  · refine Finset.analyticAt_fun_sum _ fun j hj => ?_
    have hMat := analyticAt_Mloc_of_clauses C hM hg x hj (hdom j hj)
    have hcomp := hMat.comp_of_eq
      (S.analyticAt_composedPairAtC_shift hC hMX hdm hα hsm ha₁ hc7 hR hsmR hβ hpp hδ₁ hD hy₀ j)
      rfl
    exact analyticAt_pi_iff.1 hcomp i

end ChartObs

section ChartObs2

variable {c BG κ eps Kc Cx c₂ BG₂ δ₁ δc : ℝ}
  (hC : FlCore N S.G' (stepG d L N₁ m₁ k ϱ) S.a₁ S.ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
  (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
  (hdm : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
  (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
  (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
  (ha₁ : 0 < S.a₁) (hc7 : c7 d L N BG κ ≤ thm73C3 d L N) {R : ℝ} (hR : 1 < R)
  (hsmR : 2 * (compC4 d * (bgK1 d L N * (xiC1 d * eps))) + 5 * (R * δ₁) ≤ bgC1 d L N)
  (hβ : 0 < S.β) {pp : ℝ} (hpp : 0 < pp)
  (hδ₁ : Real.sqrt N * (S.betaU ^ (-(1 / 2 : ℝ)) *
    (covSupConstC d L N (compWeight L S.a₁ k) κ * pp)) < δ₁)
  (hD : XiCData S.G' S.a S.ν (k + 1) 1 eps S.D')

include hC hMX hdm hα hsm ha₁ hc7 hR hsmR hβ hpp hδ₁ hD in
/-- **`ClassRegularObsC` for a general class, from the clauses `analyticE`, `analyticM`,
`OldXiDomOpenC` and a source `‖g‖₁ < 1`** (complex chart, `β > 0`, `0 < p₁ < p⁺`): every component of
`ℳ_k(ψ^{(k)} + t ψ'; g)` is a `C¹` family on a neighbourhood of `[0,1]`. -/
theorem classRegularObsC_of_clauses
    (hE : ∀ j, 1 ≤ j → j ≤ k + 1 → ∀ y X, IsPolyDom C.m₀ j X → y ∈ X →
      AnalyticOnNhd ℂ (fun p : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N =>
        C.Tm.E j y X p.1 p.2) {p | Dom.dom j (C.Tm.gs j X) p.1 p.2})
    (hM : ∀ j, 1 ≤ j → j ≤ k + 1 → ∀ x X, IsPolyDom C.m₀ j X → x ∈ X →
      AnalyticOnNhd ℂ (fun p : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N ×
          Fld d L N₁ m₁ (k + 1) N => C.Tm.M j x X p.1 p.2.1 p.2.2)
        {p | Dom.dom j (C.Tm.gs j X) p.1 p.2.1 ∧ Def6.l1 p.2.2 < 1})
    (hO : S.OldXiDomOpenC C Dom) (hp₁ : 0 < S.p₁) (hlt : S.p₁ < pp)
    {g : Fld d L N₁ m₁ (k + 1) N} (hg : Def6.l1 g < 1) : S.ClassRegularObsC C g := by
  have hLoc := S.classRegularLocC_of_clauses C hC hMX hdm hα hsm ha₁ hc7 hR hsmR hβ hpp hδ₁ hD
    hE hO hlt
  refine { toClassRegularLocC := hLoc, mcomp := fun y i => ?_ }
  obtain ⟨O, hOo, hmem, hdom⟩ := hO
  have hdet := S.isUnit_det_covSqrtC hC hMX hdm hα hsm hD
  have hcc := S.betaU_rpow_ne_zero hβ
  obtain ⟨ε, hε, htube⟩ := S.exists_tube (hOo.inter (S.isOpen_shiftDomC pp))
    (fun x hx s hs => ⟨hmem x hx s hs, S.smul_shiftUC_mem_shiftDomC hdet hcc (by
      have hs' : |s| ≤ 1 := by rw [abs_of_nonneg hs.1]; exact hs.2
      calc |s| * ‖x‖ ≤ 1 * S.p₁ := mul_le_mul hs' hx (norm_nonneg _) zero_le_one
        _ < pp := by rw [one_mul]; exact hlt)⟩)
  set f : ℝ × S.E → ℂ := fun q =>
    McompAtC C.m₀ C.Tm S.a S.ν (Nat.le_succ k) (S.dataUC (S.psiAtC q.1 q.2)) g y i with hf
  have hr : ContDiff ℝ ⊤ (fun q : ℝ × S.E => ((q.1 : ℂ) • S.shiftUC q.2 : S.EC)) := by
    have : (fun q : ℝ × S.E => ((q.1 : ℂ) • S.shiftUC q.2 : S.EC)) =
        fun q => S.psiAtC q.1 q.2 - S.psi0C := by
      funext q; simp [StepSetting.psiAtC]
    rw [this]
    exact S.contDiff_psiAtC.sub contDiff_const
  have hcd : ∀ s ∈ Icc (-ε) (1 + ε), ∀ x : S.E, ‖x‖ ≤ S.p₁ → ContDiffAt ℝ 1 f (s, x) := by
    intro s hs x hx
    have hy := htube s hs x hx
    have hG := S.analyticAt_McompAtC_shift C hC hMX hdm hα hsm ha₁ hc7 hR hsmR hβ hpp hδ₁ hD hM
      hg hy.2 (hdom _ hy.1) y i
    have hGc : ContDiffAt ℝ 1 (fun y' : S.EC =>
        McompAtC C.m₀ C.Tm S.a S.ν (Nat.le_succ k) (S.dataUC (S.psi0C + y')) g y i)
        ((s : ℂ) • S.shiftUC x) := (hG.contDiffAt (n := 1)).restrict_scalars ℝ
    exact ContDiffAt.comp (g := fun y' : S.EC =>
        McompAtC C.m₀ C.Tm S.a S.ν (Nat.le_succ k) (S.dataUC (S.psi0C + y')) g y i)
      (f := fun q : ℝ × S.E => ((q.1 : ℂ) • S.shiftUC q.2 : S.EC)) (s, x) hGc
      (hr.contDiffAt.of_le (by exact_mod_cast le_top))
  obtain ⟨U, hU⟩ := S.isC1Family_trunc_of_nhds (f := f) hp₁ hε hcd
  exact ⟨U, _, hU⟩

end ChartObs2

section Class

variable {P : Consts} {Rg : Regime L} {βs aS : ℕ → ℝ} {Tm : Terms d L N₁ m₁ (k + 1) N ϱ}
  {ρ : (CTorus d L N₁ m₁ (k + 1) → Fin N → ℝ) → (Fin N → ℝ) →
    (CTorus d L N₁ m₁ (k + 1) → Fin N → ℝ) → ℝ} {Ek : ℝ}

/-- The clause `analyticE` of a member of the class, for the terms of the step class. -/
theorem analyticE_of_isSF2 (hm : ClassParamMatch S C P Rg aS Tm)
    (h : IsSF2 P Rg βs aS Dom Tm ρ Ek) :
    ∀ j, 1 ≤ j → j ≤ k + 1 → ∀ y X, IsPolyDom C.m₀ j X → y ∈ X →
      AnalyticOnNhd ℂ (fun p : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N =>
        C.Tm.E j y X p.1 p.2) {p | Dom.dom j (C.Tm.gs j X) p.1 p.2} := by
  intro j hj1 hjk y X hX hy
  have hX' : IsPolyDom P.m₀ j X := hm.m₀_eq ▸ hX
  have := h.terms.analyticE j hj1 hjk y X hX' hy
  rw [← hm.terms_eq] at this
  exact this

/-- The clause `analyticM` of a member of the class, for the terms of the step class. -/
theorem analyticM_of_isSF2 (hm : ClassParamMatch S C P Rg aS Tm)
    (h : IsSF2 P Rg βs aS Dom Tm ρ Ek) :
    ∀ j, 1 ≤ j → j ≤ k + 1 → ∀ x X, IsPolyDom C.m₀ j X → x ∈ X →
      AnalyticOnNhd ℂ (fun p : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N ×
          Fld d L N₁ m₁ (k + 1) N => C.Tm.M j x X p.1 p.2.1 p.2.2)
        {p | Dom.dom j (C.Tm.gs j X) p.1 p.2.1 ∧ Def6.l1 p.2.2 < 1} := by
  intro j hj1 hjk x X hX hx
  have hX' : IsPolyDom P.m₀ j X := hm.m₀_eq ▸ hX
  have := h.terms.analyticM j hj1 hjk x X hX' hx
  rw [← hm.terms_eq] at this
  exact this

variable {c BG κ eps Kc Cx c₂ BG₂ δ₁ δc : ℝ}
  (hC : FlCore N S.G' (stepG d L N₁ m₁ k ϱ) S.a₁ S.ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
  (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
  (hdm : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
  (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
  (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
  (ha₁ : 0 < S.a₁) (hc7 : c7 d L N BG κ ≤ thm73C3 d L N) {R : ℝ} (hR : 1 < R)
  (hsmR : 2 * (compC4 d * (bgK1 d L N * (xiC1 d * eps))) + 5 * (R * δ₁) ≤ bgC1 d L N)
  (hβ : 0 < S.β) {pp : ℝ} (hpp : 0 < pp)
  (hδ₁ : Real.sqrt N * (S.betaU ^ (-(1 / 2 : ℝ)) *
    (covSupConstC d L N (compWeight L S.a₁ k) κ * pp)) < δ₁)
  (hD : XiCData S.G' S.a S.ν (k + 1) 1 eps S.D')

include hC hMX hdm hα hsm ha₁ hc7 hR hsmR hβ hpp hδ₁ hD in
/-- **`ClassRegularLocC` for a member of the class** matched to the step: from `IsSF2`
(clause `analyticE`), `ClassParamMatch` and `OldXiDomOpenC`, on the complex chart (`β > 0`,
`p₁ < p⁺`).  The domain hypothesis is not proved on the physical chart. -/
theorem classRegularLocC_of_oldXiDomOpenC (hm : ClassParamMatch S C P Rg aS Tm)
    (h : IsSF2 P Rg βs aS Dom Tm ρ Ek) (hO : S.OldXiDomOpenC C Dom) (hlt : S.p₁ < pp) :
    S.ClassRegularLocC C :=
  S.classRegularLocC_of_clauses C hC hMX hdm hα hsm ha₁ hc7 hR hsmR hβ hpp hδ₁ hD
    (S.analyticE_of_isSF2 C hm h) hO hlt

include hC hMX hdm hα hsm ha₁ hc7 hR hsmR hβ hpp hδ₁ hD in
/-- **`ClassRegularObsC` for a member of the class** matched to the step, with a source
`‖g‖₁ < 1` (clause `analyticM`), from `OldXiDomOpenC`, on the complex chart (`β > 0`,
`0 < p₁ < p⁺`). -/
theorem classRegularObsC_of_oldXiDomOpenC (hm : ClassParamMatch S C P Rg aS Tm)
    (h : IsSF2 P Rg βs aS Dom Tm ρ Ek) (hO : S.OldXiDomOpenC C Dom) (hp₁ : 0 < S.p₁)
    (hlt : S.p₁ < pp) {g : Fld d L N₁ m₁ (k + 1) N} (hg : Def6.l1 g < 1) :
    S.ClassRegularObsC C g :=
  S.classRegularObsC_of_clauses C hC hMX hdm hα hsm ha₁ hc7 hR hsmR hβ hpp hδ₁ hD
    (S.analyticE_of_isSF2 C hm h) (S.analyticM_of_isSF2 C hm h) hO hp₁ hlt hg

end Class

/-! ### The zero class -/

/-- **`OldXiDomOpenC` holds for the zero class** (rule 10), on the field domain whose complex
domain is everything and with `O` the whole space.  This is trivial: the zero class has no old
terms, so no inclusion in a chart domain is tested. -/
theorem oldXiDomOpenC_zeroClass :
    S.OldXiDomOpenC (zeroClass d L N₁ m₁ k N ϱ)
      (⟨∅, fun _ _ _ _ => True⟩ : FieldDom d L N₁ m₁ (k + 1) N ϱ) :=
  ⟨Set.univ, isOpen_univ, fun _ _ _ _ => Set.mem_univ _, fun _ _ _ _ _ _ => trivial⟩

/-- The two analyticity clauses hold for the terms of the zero class (they vanish). -/
theorem zeroClass_clauses (Dom : FieldDom d L N₁ m₁ (k + 1) N ϱ) :
    (∀ j, 1 ≤ j → j ≤ k + 1 → ∀ y X, IsPolyDom (zeroClass d L N₁ m₁ k N ϱ).m₀ j X → y ∈ X →
      AnalyticOnNhd ℂ (fun p : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N =>
        (zeroClass d L N₁ m₁ k N ϱ).Tm.E j y X p.1 p.2)
        {p | Dom.dom j ((zeroClass d L N₁ m₁ k N ϱ).Tm.gs j X) p.1 p.2}) ∧
    (∀ j, 1 ≤ j → j ≤ k + 1 → ∀ x X, IsPolyDom (zeroClass d L N₁ m₁ k N ϱ).m₀ j X → x ∈ X →
      AnalyticOnNhd ℂ (fun p : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N ×
          Fld d L N₁ m₁ (k + 1) N => (zeroClass d L N₁ m₁ k N ϱ).Tm.M j x X p.1 p.2.1 p.2.2)
        {p | Dom.dom j ((zeroClass d L N₁ m₁ k N ϱ).Tm.gs j X) p.1 p.2.1 ∧ Def6.l1 p.2.2 < 1}) :=
  ⟨fun _ _ _ _ _ _ _ => analyticOnNhd_const, fun _ _ _ _ _ _ _ => analyticOnNhd_const⟩

section ZeroConsistency

variable {c BG κ eps Kc Cx c₂ BG₂ δ₁ δc : ℝ}
  (hC : FlCore N S.G' (stepG d L N₁ m₁ k ϱ) S.a₁ S.ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
  (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
  (hdm : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
  (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
  (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
  (ha₁ : 0 < S.a₁) (hc7 : c7 d L N BG κ ≤ thm73C3 d L N) {R : ℝ} (hR : 1 < R)
  (hsmR : 2 * (compC4 d * (bgK1 d L N * (xiC1 d * eps))) + 5 * (R * δ₁) ≤ bgC1 d L N)
  (hβ : 0 < S.β) {pp : ℝ} (hpp : 0 < pp)
  (hδ₁ : Real.sqrt N * (S.betaU ^ (-(1 / 2 : ℝ)) *
    (covSupConstC d L N (compWeight L S.a₁ k) κ * pp)) < δ₁)
  (hD : XiCData S.G' S.a S.ν (k + 1) 1 eps S.D')

include hC hMX hdm hα hsm ha₁ hc7 hR hsmR hβ hpp hδ₁ hD in
/-- **The general theorem reproduces the zero-class producer**: `ClassRegularLocC` for the zero
class, obtained through `classRegularLocC_of_clauses` and `oldXiDomOpenC_zeroClass`. -/
theorem classRegularLocC_zeroClass_via_open (hlt : S.p₁ < pp) :
    S.ClassRegularLocC (zeroClass d L N₁ m₁ k N ϱ) :=
  S.classRegularLocC_of_clauses _ hC hMX hdm hα hsm ha₁ hc7 hR hsmR hβ hpp hδ₁ hD
    (zeroClass_clauses (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) (N := N) (ϱ := ϱ)
      ⟨∅, fun _ _ _ _ => True⟩).1 S.oldXiDomOpenC_zeroClass hlt

include hC hMX hdm hα hsm ha₁ hc7 hR hsmR hβ hpp hδ₁ hD in
/-- `ClassRegularObsC` for the zero class and every source with `‖g‖₁ < 1`, through the general
theorem (the landed `classRegularObsC_zeroClass` has no condition on `g`). -/
theorem classRegularObsC_zeroClass_via_open (hp₁ : 0 < S.p₁) (hlt : S.p₁ < pp)
    {g : Fld d L N₁ m₁ (k + 1) N} (hg : Def6.l1 g < 1) :
    S.ClassRegularObsC (zeroClass d L N₁ m₁ k N ϱ) g :=
  S.classRegularObsC_of_clauses _ hC hMX hdm hα hsm ha₁ hc7 hR hsmR hβ hpp hδ₁ hD
    (zeroClass_clauses (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) (N := N) (ϱ := ϱ)
      ⟨∅, fun _ _ _ _ => True⟩).1
    (zeroClass_clauses (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) (N := N) (ϱ := ϱ)
      ⟨∅, fun _ _ _ _ => True⟩).2 S.oldXiDomOpenC_zeroClass hp₁ hlt hg

end ZeroConsistency

/-- **`OldXiDomOpenC` is inhabited** (rule 10), for the zero class at every step: on the field
domain whose complex domain is everything.  This is trivial; it shows only that the hypothesis is
satisfiable.  A non-zero class member matched to a step is not yet available. -/
theorem nonempty_oldXiDomOpenC_zeroClass :
    ∃ Dom : FieldDom d L N₁ m₁ (k + 1) N ϱ,
      S.OldXiDomOpenC (zeroClass d L N₁ m₁ k N ϱ) Dom :=
  ⟨_, S.oldXiDomOpenC_zeroClass⟩

end StepSetting

end Balaban.Fluctuation
