/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.Thm31WitnessData
public import Balaban.Fluctuation.StepActivityWitnessSplit
public import Balaban.Fluctuation.StepNonvanishInhab
public import Balaban.Fluctuation.Thm31Inhab
public import Balaban.Fluctuation.Thm31a
public import Balaban.Fluctuation.StepActivityWitnessMain
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# `E1Marks` at an actual step

For a step with `RayData` and the zero class, the exponent is `W₁(u,ψ̂) = -β V^{(k)}(ψ^{(k)} + uψ')`
and the mark of `ℰ₁(z)` is `DΦ₁(sψ')[1_{B(z)}ψ']`.  With the analytic extension `P` of
`w ↦ V^{(k)}(ψ^{(k)} + w)` (`exists_analytic_ext`), the single whole-torus label carries the activity
`u ↦ -β P(u ψ')` on `|u| < 2`, `‖ψ̂‖ ≤ p₁`, and the single mark is `-β DP(uψ')[1_{B(z)}ψ']`,
both holomorphic in `u`, with the numerical hypotheses of Theorem 3.4 in the constants of
`stepActivityBound_of_small_gen`.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization Balaban.Polymer
  Balaban.SmallField.Def6 Balaban.SmallField MeasureTheory Set Filter Finset

section Consts

variable (d L N₁ m₁ k : ℕ) [NeZero L] [NeZero N₁]

/-- The size `𝗱(𝕋)` of the whole-torus label. -/
noncomputable def wholeLen : ℝ :=
  treeLenCovOne (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) 0 (k + 1) Set.univ

/-- The admissible constants of Theorem 3.4 used by the witnesses. -/
noncomputable def wk0 : ℝ := aEnt d L + 1
noncomputable def wKc : ℝ := K0 d L (wk0 d L) + 1
noncomputable def wkH : ℝ := 3 * wk0 d L + c1 d L + 3 / 2
noncomputable def wεH : ℝ := 1 / (8 * wKc d L ^ 3 * c1 d L *
  Real.exp ((wkH d L - 2 * wk0 d L) * cG d L + c1 d L + 0 * cG d L))

/-- The bound for the first-order mark that gives `C_PE ∑ F₀ e^{-κ₀𝗱} ≤ B`. -/
noncomputable def e1Eta (B : ℝ) : ℝ :=
  B / ((CPE d L (wKc d L) (wkH d L) (wk0 d L) 0 + 1) *
    Real.exp ((wkH d L - wk0 d L) * wholeLen d L N₁ m₁ k))

omit [NeZero L] [NeZero N₁] in
theorem wholeLen_nonneg : 0 ≤ wholeLen d L N₁ m₁ k := treeLenCovOne_nonneg _ _ _

theorem wk0_pos : 1 ≤ wk0 d L := by unfold wk0; linarith [aEnt_nonneg d L]

set_option linter.unusedSectionVars false in
theorem wKc_pos : 1 ≤ wKc d L := by
  have hK0 : 0 < K0 d L (aEnt d L + 1) := by
    unfold K0
    have : Real.exp (-1) < 1 := by rw [Real.exp_lt_one_iff]; norm_num
    exact div_pos (Real.exp_pos _) (by linarith [aEnt_nonneg d L])
  unfold wKc wk0; linarith

theorem wεH_pos : 0 < wεH d L := by
  have := wKc_pos d L
  have := one_le_c1 d L
  unfold wεH
  positivity

theorem CPE_nonneg' (Kc κH κ0 κ' : ℝ) : 0 ≤ CPE d L Kc κH κ0 κ' := by
  have := one_le_c1 d L
  unfold CPE
  positivity

omit [NeZero N₁] in
theorem e1Eta_pos {B : ℝ} (hB : 0 < B) : 0 < e1Eta d L N₁ m₁ k B := by
  unfold e1Eta
  have := CPE_nonneg' d L (wKc d L) (wkH d L) (wk0 d L) 0
  positivity

theorem thr_eq : stepActivityThreshold d L N₁ m₁ (k + 1) =
    wεH d L * Real.exp (-wkH d L * wholeLen d L N₁ m₁ k) := rfl

end Consts

section Cut

open Classical in
theorem measurable_cut {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E]
    [OpensMeasurableSpace E] {p : ℝ} {f : E → ℂ} (hf : ContinuousOn f (Metric.closedBall 0 p)) :
    Measurable (fun x => if ‖x‖ ≤ p then f x else 0) := by
  have := ContinuousOn.measurable_piecewise (s := Metric.closedBall (0 : E) p) (f := f)
    (g := fun _ => (0 : ℂ)) hf continuousOn_const measurableSet_closedBall
  convert this using 1
  ext x
  simp [Set.piecewise, dist_zero_right]

end Cut

section E1

variable {d L N₁ m₁ k : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}
  (S : StepSetting d L N₁ m₁ k 2 ϱ) (P : S.EC → ℂ)

open Classical in
/-- The activity of the whole-torus label: `-β P(uψ')` for `|u| < 2`, `‖ψ̂‖ ≤ p₁`. -/
noncomputable def e1H (u : ℂ) (x : S.E) : ℂ :=
  if ‖u‖ < 2 ∧ ‖x‖ ≤ S.p₁ then -(S.β : ℂ) * P (u • S.shiftUC x) else 0

open Classical in
/-- The mark of `ℰ₁(z)`: `-β DP(uψ')[1_{B(z)}ψ']`. -/
noncomputable def e1G (z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1)))) (u : ℂ) (x : S.E) : ℂ :=
  if ‖u‖ < 2 ∧ ‖x‖ ≤ S.p₁ then -(S.β : ℂ) * (fderiv ℂ P (u • S.shiftUC x)) (S.maskL z x) else 0

variable {S P}

theorem e1H_of {u : ℂ} {x : S.E} (hc : ‖u‖ < 2 ∧ ‖x‖ ≤ S.p₁) :
    e1H S P u x = -(S.β : ℂ) * P (u • S.shiftUC x) := by
  simp only [e1H, hc.1, hc.2, and_self, ite_true]

theorem e1H_of_not {u : ℂ} {x : S.E} (hc : ¬ (‖u‖ < 2 ∧ ‖x‖ ≤ S.p₁)) : e1H S P u x = 0 := by
  simp only [e1H, hc, ite_false]

theorem e1G_of {z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1)))} {u : ℂ} {x : S.E}
    (hc : ‖u‖ < 2 ∧ ‖x‖ ≤ S.p₁) :
    e1G S P z u x = -(S.β : ℂ) * (fderiv ℂ P (u • S.shiftUC x)) (S.maskL z x) := by
  simp only [e1G, hc.1, hc.2, and_self, ite_true]

theorem e1G_of_not {z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1)))} {u : ℂ} {x : S.E}
    (hc : ¬ (‖u‖ < 2 ∧ ‖x‖ ≤ S.p₁)) : e1G S P z u x = 0 := by
  simp only [e1G, hc, ite_false]

theorem e1H_measurable (hA : ∀ u : ℂ, ‖u‖ < 2 → ∀ x : S.E, ‖x‖ ≤ S.p₁ →
    AnalyticAt ℂ P (u • S.shiftUC x)) (u : ℂ) : Measurable (e1H S P u) := by
  classical
  by_cases hu : ‖u‖ < 2
  · have : e1H S P u = fun x => if ‖x‖ ≤ S.p₁ then -(S.β : ℂ) * P (u • S.shiftUC x) else 0 := by
      funext x; simp [e1H, hu]
    rw [this]
    refine measurable_cut ?_
    intro x hx
    have hx' : ‖x‖ ≤ S.p₁ := by simpa using hx
    have h1 : ContinuousAt P (u • S.shiftUC x) := (hA u hu x hx').continuousAt
    have h2 : Continuous (fun x : S.E => u • S.shiftUC x) :=
      S.shiftL.continuous.const_smul u
    have h4 : ContinuousAt (P ∘ fun x : S.E => u • S.shiftUC x) x :=
      ContinuousAt.comp (g := P) (f := fun x : S.E => u • S.shiftUC x) h1 h2.continuousAt
    exact (continuousAt_const.mul h4).continuousWithinAt
  · have : e1H S P u = fun _ => 0 := by funext x; simp [e1H, hu]
    rw [this]; exact measurable_const

theorem e1G_measurable (z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))))
    (hA : ∀ u : ℂ, ‖u‖ < 2 → ∀ x : S.E, ‖x‖ ≤ S.p₁ → AnalyticAt ℂ P (u • S.shiftUC x))
    (u : ℂ) : Measurable (e1G S P z u) := by
  classical
  by_cases hu : ‖u‖ < 2
  · have : e1G S P z u = fun x => if ‖x‖ ≤ S.p₁ then
        -(S.β : ℂ) * (fderiv ℂ P (u • S.shiftUC x)) (S.maskL z x) else 0 := by
      funext x; simp [e1G, hu]
    rw [this]
    refine measurable_cut ?_
    intro x hx
    have hx' : ‖x‖ ≤ S.p₁ := by simpa using hx
    have h1 : ContinuousAt (fderiv ℂ P) (u • S.shiftUC x) := (hA u hu x hx').fderiv.continuousAt
    have h2 : Continuous (fun x : S.E => u • S.shiftUC x) :=
      S.shiftL.continuous.const_smul u
    have h3 : ContinuousAt (fun x : S.E => fderiv ℂ P (u • S.shiftUC x)) x :=
      (ContinuousAt.comp (g := fderiv ℂ P) (f := fun x : S.E => u • S.shiftUC x) h1
        h2.continuousAt)
    exact (continuousAt_const.mul
      (h3.clm_apply (S.maskL z).continuous.continuousAt)).continuousWithinAt
  · have : e1G S P z u = fun _ => 0 := by funext x; simp [e1G, hu]
    rw [this]; exact measurable_const

theorem e1H_differentiableOn
    (hA : ∀ u : ℂ, ‖u‖ < 2 → ∀ x : S.E, ‖x‖ ≤ S.p₁ → AnalyticAt ℂ P (u • S.shiftUC x))
    (x : S.E) : DifferentiableOn ℂ (fun u => e1H S P u x) (Metric.ball (0 : ℂ) 2) := by
  classical
  by_cases hx : ‖x‖ ≤ S.p₁
  · refine DifferentiableOn.congr (f := fun u => -(S.β : ℂ) * P (u • S.shiftUC x)) ?_ ?_
    · intro u hu
      have hu' : ‖u‖ < 2 := by simpa using hu
      have h1 : AnalyticAt ℂ (fun u : ℂ => u • S.shiftUC x) u :=
        analyticAt_id.smul analyticAt_const
      have h2 : AnalyticAt ℂ (fun u : ℂ => P (u • S.shiftUC x)) u :=
        (AnalyticAt.comp (hA u hu' x hx) h1 :
          AnalyticAt ℂ (P ∘ fun u : ℂ => u • S.shiftUC x) u)
      exact (analyticAt_const.mul h2).differentiableAt.differentiableWithinAt
    · intro u hu
      have hu' : ‖u‖ < 2 := by simpa using hu
      simp [e1H, hu', hx]
  · have : (fun u => e1H S P u x) = fun _ => 0 := by funext u; simp [e1H, hx]
    rw [this]; exact differentiableOn_const _

theorem e1G_differentiableOn (z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))))
    (hA : ∀ u : ℂ, ‖u‖ < 2 → ∀ x : S.E, ‖x‖ ≤ S.p₁ → AnalyticAt ℂ P (u • S.shiftUC x))
    (x : S.E) : DifferentiableOn ℂ (fun u => e1G S P z u x) (Metric.ball (0 : ℂ) 2) := by
  classical
  by_cases hx : ‖x‖ ≤ S.p₁
  · refine DifferentiableOn.congr (f := fun u => -(S.β : ℂ) *
      (fderiv ℂ P (u • S.shiftUC x)) (S.maskL z x)) ?_ ?_
    · intro u hu
      have hu' : ‖u‖ < 2 := by simpa using hu
      have h1 : AnalyticAt ℂ (fun u : ℂ => u • S.shiftUC x) u :=
        analyticAt_id.smul analyticAt_const
      have h2 : AnalyticAt ℂ (fun u : ℂ => fderiv ℂ P (u • S.shiftUC x)) u :=
        (AnalyticAt.comp (hA u hu' x hx).fderiv h1 :
          AnalyticAt ℂ (fderiv ℂ P ∘ fun u : ℂ => u • S.shiftUC x) u)
      have h3 : AnalyticAt ℂ (fun u : ℂ => (fderiv ℂ P (u • S.shiftUC x)) (S.maskL z x)) u := by
        have h4 : AnalyticAt ℂ ((ContinuousLinearMap.apply ℂ ℂ (S.maskL z x)) ∘
            fun u : ℂ => fderiv ℂ P (u • S.shiftUC x)) u :=
          AnalyticAt.comp ((ContinuousLinearMap.apply ℂ ℂ (S.maskL z x)).analyticAt _) h2
        exact h4
      exact (analyticAt_const.mul h3).differentiableAt.differentiableWithinAt
    · intro u hu
      have hu' : ‖u‖ < 2 := by simpa using hu
      simp [e1G, hu', hx]
  · have : (fun u => e1G S P z u x) = fun _ => 0 := by funext u; simp [e1G, hx]
    rw [this]; exact differentiableOn_const _

end E1

section Main

variable {d L N₁ m₁ k : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ} {pp : ℝ}
  {S : StepSetting d L N₁ m₁ k 2 ϱ}

theorem StepSetting.RayData.shiftUC_eq' (R : S.RayData pp) (x : S.E) :
    S.shiftUC x = yhat (S.shiftU x) :=
  S.shiftUC_eq R.H R.hδ'0 R.hδ' R.hD'R R.hδ0 ((chiU_eq_one_iff _ _ _ _).1 R.hχu) R.hfam R.hsm x

/-- On the real ray the complex potential is the landed one, and the datum is in the domain. -/
theorem StepSetting.RayData.inDom_ray (R : S.RayData pp) {s : ℝ} {x : S.E}
    (hq : |s| * ‖x‖ < pp) :
    S.InDom ((s : ℂ) • S.shiftUC x) ∧
      S.VkC (S.psi0C + (s : ℂ) • S.shiftUC x) = S.Vk (S.psiAt s x) := by
  have hχ := (chiU_eq_one_iff _ _ _ _).1 R.hχu
  have e : S.psi0C + (s : ℂ) • S.shiftUC x = yhat (S.psiAt s x) := by
    rw [← S.psiAtC_eq R.ha₁ R.H R.hδ'0 R.hδ' R.hD'R R.hδ0 hχ R.hfam R.hsm]; rfl
  refine ⟨?_, ?_⟩
  · show InUnionDomainC _ _ _ _ (S.dataUC (S.psi0C + (s : ℂ) • S.shiftUC x))
    rw [e, S.dataUC_yhat]
    exact S.inUnionDomainC_of_R' R.H (R.dom (q := (s, x)) hq)
  · rw [e]; rfl

/-- A fixed cube of the torus. -/
noncomputable def cube0 : CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) 0 (k + 1)
    Set.univ :=
  ⟨cbase (cellSide L 0 m₁ (k + 1)) 0, aligned_cbase 0, Set.subset_univ _⟩

open Classical in
/-- **The block structure of `ν_{p₁}`**: `ψ̂` in the fixed cube `cube0` and the point mass at `0` in
all other cubes. -/
noncomputable def oneBlockSplit (S : StepSetting d L N₁ m₁ k 2 ϱ) (hp₁ : 0 < S.p₁) :
    BlockSplit S 0 :=
  haveI : IsProbabilityMeasure S.nuFl := isProbabilityMeasure_fluctMeasure S.U 2 hp₁
  { Ωb := fun _ => S.E
    μ := oneBlockMeasure S.nuFl cube0
    restr := oneBlockMap cube0
    meas := measurable_oneBlockMap cube0
    map_eq := map_oneBlockMap S.nuFl cube0 }

/-- The whole-torus label. -/
noncomputable def wholeLabel :
    CubeLabels (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) 0 (k + 1) Set.univ Unit :=
  { ysite := fun _ => Set.univ
    dl := fun _ => wholeLen d L N₁ m₁ k
    isDj := fun _ => isDj_univ d L N₁ m₁ (k + 1) 0 (k + 1)
    meets := fun _ => by simp
    size := fun _ => Or.inl rfl }

theorem cube0_mem :
    cube0 (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) ∈
      blocksOf (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) 0 (k + 1) Set.univ
        ((wholeLabel (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k)).ysite ()) := by
  rw [mem_blocksOf]; exact Set.subset_univ _

open Classical in
theorem whole_entropy (b : CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) 0 (k + 1)
    Set.univ) :
    ∑ y : Unit, (if box b.1 (cellSide L 0 m₁ (k + 1)) ⊆
      (wholeLabel (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k)).ysite y then
        Real.exp (-wk0 d L * wholeLen d L N₁ m₁ k) else 0) ≤ wKc d L := by
  simp only [Finset.univ_unique, Finset.sum_singleton]
  have h0 := wholeLen_nonneg d L N₁ m₁ k
  have h1 := wk0_pos d L
  have h2 := wKc_pos d L
  split_ifs
  · have : Real.exp (-wk0 d L * wholeLen d L N₁ m₁ k) ≤ 1 :=
      Real.exp_le_one_iff.2 (by nlinarith)
    linarith
  · linarith

variable (S) in
/-- The activity of the whole-torus label at the complex interpolation parameter `u`. -/
noncomputable def e1Act (P : S.EC → ℂ) (hA : ∀ u : ℂ, ‖u‖ < 2 → ∀ x : S.E, ‖x‖ ≤ S.p₁ →
      AnalyticAt ℂ P (u • S.shiftUC x))
    (hS : ∀ u : ℂ, ‖u‖ < 2 → ∀ x : S.E, ‖x‖ ≤ S.p₁ →
      ‖(S.β : ℂ) * P (u • S.shiftUC x)‖ ≤ stepActivityThreshold d L N₁ m₁ (k + 1))
    (hp₁ : 0 < S.p₁) (u : ℂ) :
    LabelAct (wholeLabel (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k))
      (oneBlockSplit S hp₁).Ωb (wεH d L) (wkH d L) (wk0 d L) (wKc d L) where
  H := fun _ Φ => e1H S P u (Φ cube0 : S.E)
  meas := fun _ => (e1H_measurable hA u).comp (measurable_pi_apply (cube0 : _) : Measurable
    fun Φ : (∀ b, (oneBlockSplit S hp₁).Ωb b) => (Φ cube0 : S.E))
  dep := fun _ Φ Φ' h => by
    simp only [h cube0 cube0_mem]
  bound := fun _ Φ => by
    classical
    have key : ∀ x : S.E, ‖e1H S P u x‖ ≤ stepActivityThreshold d L N₁ m₁ (k + 1) := by
      intro x
      by_cases hc : ‖u‖ < 2 ∧ ‖x‖ ≤ S.p₁
      · rw [e1H_of hc, neg_mul, norm_neg]
        exact hS u hc.1 _ hc.2
      · rw [e1H_of_not hc, norm_zero]
        exact (stepActivityThreshold_pos d L N₁ m₁ (k + 1)).le
    rw [thr_eq] at key
    exact key (Φ cube0)
  entropy := whole_entropy

/-- **`E1Marks` at an actual step.** -/
theorem nonempty_e1Marks (R : S.RayData pp) (hp₁ : 0 < S.p₁) (hlt : S.p₁ < pp)
    (z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1)))) {B : ℝ} (hB : 0 < B)
    {P : S.EC → ℂ} (hP : ∀ w, S.InDom w → S.VkC (S.psi0C + w) = P w)
    (hPa : ∀ w, S.InDom w → AnalyticAt ℂ P w)
    (htube : ∀ u : ℂ, ‖u‖ < 2 → ∀ x : S.E, ‖x‖ ≤ S.p₁ →
      AnalyticAt ℂ P (u • S.shiftUC x) ∧
      ‖(S.β : ℂ) * P (u • S.shiftUC x)‖ ≤ stepActivityThreshold d L N₁ m₁ (k + 1) ∧
      ‖(S.β : ℂ) * (fderiv ℂ P (u • S.shiftUC x)) (S.maskL z x)‖ ≤ e1Eta d L N₁ m₁ k B) :
    ∃ (BS : BlockSplit S 0) (I : E1Marks S (zeroClass d L N₁ m₁ k 2 ϱ) BS z),
      CPE d L I.Kc I.κH I.κ0 I.κ' *
        (∑ i, I.F0 i * Real.exp (-I.κ0 * I.Lab.dl (I.y0 i))) ≤ B := by
  classical
  have hA : ∀ u : ℂ, ‖u‖ < 2 → ∀ x : S.E, ‖x‖ ≤ S.p₁ → AnalyticAt ℂ P (u • S.shiftUC x) :=
    fun u hu x hx => (htube u hu x hx).1
  have hS : ∀ u : ℂ, ‖u‖ < 2 → ∀ x : S.E, ‖x‖ ≤ S.p₁ →
      ‖(S.β : ℂ) * P (u • S.shiftUC x)‖ ≤ stepActivityThreshold d L N₁ m₁ (k + 1) :=
    fun u hu x hx => (htube u hu x hx).2.1
  set F0v := e1Eta d L N₁ m₁ k B * Real.exp (wkH d L * wholeLen d L N₁ m₁ k) with hF0v
  have hF0pos : 0 < F0v := mul_pos (e1Eta_pos d L N₁ m₁ k hB) (Real.exp_pos _)
  have hF0e : F0v * Real.exp (-wkH d L * wholeLen d L N₁ m₁ k) = e1Eta d L N₁ m₁ k B := by
    rw [hF0v, mul_assoc, ← Real.exp_add]; simp
  have hW' : ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ᵐ x ∂S.nuFl,
      S.Wone (zeroClass d L N₁ m₁ k 2 ϱ) s x = e1H S P (s : ℂ) x := by
    intro s hs
    filter_upwards [S.ae_mem_closedBall hp₁] with x hx
    have hx' : ‖x‖ ≤ S.p₁ := by simpa using hx
    have hq : |s| * ‖x‖ < pp := by
      rw [abs_of_nonneg hs.1]
      calc s * ‖x‖ ≤ 1 * S.p₁ := mul_le_mul hs.2 hx' (norm_nonneg _) zero_le_one
        _ < pp := by linarith
    obtain ⟨hd, hv⟩ := R.inDom_ray hq
    have hc : ‖(s : ℂ)‖ < 2 ∧ ‖x‖ ≤ S.p₁ := by
      refine ⟨?_, hx'⟩
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs.1]; linarith [hs.2]
    have e : e1H S P (s : ℂ) x = -(S.β : ℂ) * P ((s : ℂ) • S.shiftUC x) := e1H_of hc
    rw [e, StepSetting.Wone_zeroClass, ← hP _ hd, hv]
  have hF' : ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ᵐ x ∂S.nuFl,
      (fderiv ℝ (S.Phi1 (zeroClass d L N₁ m₁ k 2 ϱ)) (s • S.shiftU x))
        (S.maskU z (S.shiftU x)) = e1G S P z (s : ℂ) x := by
    intro s hs
    filter_upwards [S.ae_mem_closedBall hp₁] with x hx
    have hx' : ‖x‖ ≤ S.p₁ := by simpa using hx
    have hc : ‖(s : ℂ)‖ < 2 ∧ ‖x‖ ≤ S.p₁ := by
      refine ⟨?_, hx'⟩
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs.1]; linarith [hs.2]
    have e : e1G S P z (s : ℂ) x =
        -(S.β : ℂ) * (fderiv ℂ P ((s : ℂ) • S.shiftUC x)) (S.maskL z x) := e1G_of hc
    have hy : ‖S.unshiftU (s • S.shiftU x)‖ < pp := by
      have := R.unshift_ray hlt hx' hs
      simpa using this
    rw [e, R.fderiv_Phi1_zeroClass hP hPa hy, S.maskL_apply, R.shiftUC_eq' x, S.yhat_smul]
  refine ⟨oneBlockSplit S hp₁, ?_⟩
  have hmain : ∃ I : E1Marks S (zeroClass d L N₁ m₁ k 2 ϱ) (oneBlockSplit S hp₁) z,
      I.Kc = wKc d L ∧ I.κH = wkH d L ∧ I.κ0 = wk0 d L ∧ I.κ' = 0 ∧
      (∀ i, I.F0 i = F0v) ∧ (∀ i, I.Lab.dl (I.y0 i) = wholeLen d L N₁ m₁ k) ∧ Nonempty I.ι ∧
      Fintype.card I.ι = 1 := by
    refine ⟨{
      Lb := Unit
      Lab := wholeLabel
      ι := Unit
      nonempty := ⟨()⟩
      εH := wεH d L
      κH := wkH d L
      κG := wkH d L
      κ0 := wk0 d L
      κ' := 0
      Kc := wKc d L
      F0 := fun _ => F0v
      hN := by simp
      𝒰 := Metric.ball (0 : ℂ) 2
      isOpen := Metric.isOpen_ball
      seg := fun s hs => by
        rw [Metric.mem_ball, dist_zero_right, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg hs.1]
        linarith [hs.2]
      A := e1Act S P hA hS hp₁
      y0 := fun _ => ()
      G := fun _ u Φ => e1G S P z u (Φ cube0 : S.E)
      meas := fun _ u => (e1G_measurable z hA u).comp
        (measurable_pi_apply (cube0 : _) : Measurable
          fun Φ : (∀ b, (oneBlockSplit S hp₁).Ωb b) => (Φ cube0 : S.E))
      dep := fun _ u Φ Φ' h => by
        simp only [h cube0 cube0_mem]
      bound := fun _ u Φ => by
        have key : ∀ x : S.E, ‖e1G S P z u x‖ ≤ F0v * Real.exp (-wkH d L *
            wholeLen d L N₁ m₁ k) := by
          intro x
          rw [hF0e]
          by_cases hc : ‖u‖ < 2 ∧ ‖x‖ ≤ S.p₁
          · rw [e1G_of hc, neg_mul, norm_neg]
            exact (htube u hc.1 x hc.2).2.2
          · rw [e1G_of_not hc, norm_zero]
            exact (e1Eta_pos d L N₁ m₁ k hB).le
        exact key (Φ cube0)
      holA := fun _ Φ => e1H_differentiableOn hA (Φ cube0 : S.E)
      holG := fun _ Φ => e1G_differentiableOn z hA (Φ cube0 : S.E)
      hκ0 := le_rfl
      hKc := le_rfl
      hεpos := wεH_pos d L
      hF0 := fun _ => hF0pos
      hκ' := le_rfl
      hκG := le_rfl
      hκ := by
        have := wk0_pos d L
        show 0 + 3 * wk0 d L + c1 d L + 3 / 2 ≤ wkH d L
        unfold wkH; linarith
      hε := le_rfl
      hW := fun s hs => by
        filter_upwards [hW' s hs] with x hx
        rw [hx]
        simp [e1Act, oneBlockSplit, oneBlockMap]
      hF := fun s hs => by
        filter_upwards [hF' s hs] with x hx
        rw [hx]
        simp [oneBlockSplit, oneBlockMap] }, rfl, rfl, rfl, rfl, fun _ => rfl, fun _ => rfl, ⟨()⟩, by simp⟩
  obtain ⟨I, hKc, hκH, hκ0, hκ', hF0, hdl, -, hcard⟩ := hmain
  refine ⟨I, ?_⟩
  rw [hKc, hκH, hκ0, hκ']
  have hsum : (∑ i, I.F0 i * Real.exp (-wk0 d L * I.Lab.dl (I.y0 i))) =
      F0v * Real.exp (-wk0 d L * wholeLen d L N₁ m₁ k) := by
    obtain ⟨a, ha⟩ := Fintype.card_eq_one_iff.1 hcard
    rw [Finset.sum_eq_single a (fun b _ hb => absurd (ha b) hb)
      (fun h => absurd (Finset.mem_univ a) h), hF0, hdl]
  rw [hsum]
  have h1 : F0v * Real.exp (-wk0 d L * wholeLen d L N₁ m₁ k) =
      e1Eta d L N₁ m₁ k B * Real.exp ((wkH d L - wk0 d L) * wholeLen d L N₁ m₁ k) := by
    rw [hF0v, mul_assoc, ← Real.exp_add]; congr 2; ring
  rw [h1]
  set c := CPE d L (wKc d L) (wkH d L) (wk0 d L) 0 with hc
  set E := Real.exp ((wkH d L - wk0 d L) * wholeLen d L N₁ m₁ k) with hE
  have hc0 : 0 ≤ c := CPE_nonneg' d L _ _ _ _
  have hEpos : 0 < E := Real.exp_pos _
  have h2 : e1Eta d L N₁ m₁ k B * E = B / (c + 1) := by
    show B / ((c + 1) * E) * E = B / (c + 1)
    field_simp
  rw [h2, ← mul_div_assoc, div_le_iff₀ (by linarith)]
  nlinarith

end Main

section Datum

open Balaban.Inhabited Balaban.Localization.I5Inhabited

/-- **`E1Marks` at an actual, non-degenerate step.**  The datum of `exists_activity_datum`
(`d = L = 3`, `N₁ = 6`, `k = 1`, `N = 2`, `β = T²/3 > 0`, zero class, `RayData` with `p⁺ = 2`) with
the cutoff radius `p₁ = p` of `χ_fl` taken so small that, for `|u| < 2` and `‖ψ̂‖ ≤ p`, the exponent
`-β P(uψ')` is below the cluster threshold and the mark `-β DP(uψ')[1_{B(0)}ψ']` is below
`e1Eta`; the single whole-torus label carries them, and `C_PE ∑ F₀ e^{-κ₀𝗱} ≤ B(β)` for any
positive `B(β)`. -/
theorem exists_e1Marks_datum (Bf : ℝ → ℝ) (hBf : ∀ β, 0 < β → 0 < Bf β) :
    ∃ (m₁ : ℕ) (S : StepSetting 3 3 6 m₁ 1 2 (rhoSep m₁)) (BS : BlockSplit S 0),
      0 < S.β ∧ 0 < S.p₁ ∧ S.p₁ < 2 ∧ Nonempty (S.RayData 2) ∧
      ∃ I : E1Marks S (zeroClass 3 3 6 m₁ 1 2 (rhoSep m₁)) BS
          (0 : Torus 3 (6 * 3 ^ m₁ * 3 ^ (1 + 1 - (1 + 1)))),
        CPE 3 3 I.Kc I.κH I.κ0 I.κ' *
          (∑ i, I.F0 i * Real.exp (-I.κ0 * I.Lab.dl (I.y0 i))) ≤ Bf S.β := by
  classical
  obtain ⟨m₁, δ, δ', T, hm, hbig, hδ, hsm, hδ'0, hδ'a, hδ'b, hδ'c, hT, -, hT1, hT2⟩ :=
    exists_witness_params (fun _ => 0)
  obtain ⟨R0⟩ := rayData_witness hm hbig hδ hsm hδ'0 hδ'a hδ'b hδ'c hT hT1 hT2
  set S0 := witnessSetting m₁ (T ^ 2 / 3) δ with hS0
  have hβ : 0 < S0.β := R0.hβ
  have hThr := stepActivityThreshold_pos 3 3 6 m₁ 2
  have hη := e1Eta_pos 3 3 6 m₁ 1 (hBf S0.β hβ)
  obtain ⟨P, p, hp, hpp, hP, hPa, htube⟩ := StepSetting.exists_tube_data (S := S0) R0
    (0 : Torus 3 (6 * 3 ^ m₁ * 3 ^ (1 + 1 - (1 + 1)))) hThr hη
  let S1 : StepSetting 3 3 6 m₁ 1 2 (rhoSep m₁) := { S0 with p₁ := p }
  have R1 : S1.RayData 2 :=
    { ha₁ := R0.ha₁, H := R0.H, δ' := R0.δ', hδ'0 := R0.hδ'0, hδ' := R0.hδ', hD'R := R0.hD'R,
      hδ0 := R0.hδ0, hfam := R0.hfam, hsm := R0.hsm, hχu := R0.hχu, hnorm := R0.hnorm,
      hβ := R0.hβ, hpp := R0.hpp, B₅ := R0.B₅, K₂ := R0.K₂, hB5 := R0.hB5, hK2 := R0.hK2,
      hp40 := R0.hp40, hrad := R0.hrad }
  have hB1 : 0 < Bf S1.β := hBf _ hβ
  obtain ⟨BS, I, hI⟩ := nonempty_e1Marks (S := S1) R1 (show 0 < p from hp) (show p < 2 from hpp)
    (0 : Torus 3 (6 * 3 ^ m₁ * 3 ^ (1 + 1 - (1 + 1)))) hB1 (P := P) hP hPa htube
  exact ⟨m₁, S1, BS, hβ, hp, hpp, ⟨R1⟩, I, hI⟩

end Datum

end Balaban.Fluctuation
