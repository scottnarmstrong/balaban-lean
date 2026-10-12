/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.Thm31bWitnessData
public import Balaban.Fluctuation.Thm31Witness
public import Balaban.Fluctuation.Thm31bInhab
public import Balaban.Fluctuation.Thm31bStep
public import Balaban.Fluctuation.StepActivityWitnessRay
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# `ObsMarks` at an actual step

For the zero class and the source `g = λ 1_{(y₁,i₁)}`, the exponent of `μ_{1,t}` is
`W₁(1) + W₂(t) = -β P(ψ') + λ (B_{y₁ i₁}(tψ') - B_{y₁ i₁}(0))` with the analytic extensions `P` of the
potential and `B` of the background field (`exists_analytic_ext`), and the integrand is
`∂_t svec φ_k(ψ^{(k)} + tψ')(y)_i = DB_{yi}(tψ')[ψ']`.  The activity with the parameter `σ` is
`σ · (W₁(1) + W₂(t))`.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization Balaban.Polymer
  Balaban.SmallField.Def6 Balaban.SmallField MeasureTheory Set Filter Finset Metric

section Obs

variable {d L N₁ m₁ k : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}
  (S : StepSetting d L N₁ m₁ k 2 ϱ) (P Bc : S.EC → ℂ) (lam p : ℝ)

open Classical in
/-- The activity of the whole-torus label with the continuation parameter `σ`:
`σ (-β P(ψ') + λ (B(tψ') - B(0)))`. -/
noncomputable def obsH (t σ : ℂ) (x : S.E) : ℂ :=
  if ‖t‖ < 2 ∧ ‖σ‖ < 2 ∧ ‖x‖ ≤ p then
    σ * (-(S.β : ℂ) * P (S.shiftUC x) + (lam : ℂ) * (Bc (t • S.shiftUC x) - Bc 0)) else 0

open Classical in
/-- The remainder mark `DB(uψ')[ψ']`. -/
noncomputable def obsG (u : ℂ) (x : S.E) : ℂ :=
  if ‖u‖ < 2 ∧ ‖x‖ ≤ p then (fderiv ℂ Bc (u • S.shiftUC x)) (S.shiftUC x) else 0

variable {S P Bc lam p}

theorem obsH_of {t σ : ℂ} {x : S.E} (hc : ‖t‖ < 2 ∧ ‖σ‖ < 2 ∧ ‖x‖ ≤ p) :
    obsH S P Bc lam p t σ x =
      σ * (-(S.β : ℂ) * P (S.shiftUC x) + (lam : ℂ) * (Bc (t • S.shiftUC x) - Bc 0)) := by
  simp only [obsH, hc.1, hc.2.1, hc.2.2, and_self, ite_true]

theorem obsH_of_not {t σ : ℂ} {x : S.E} (hc : ¬ (‖t‖ < 2 ∧ ‖σ‖ < 2 ∧ ‖x‖ ≤ p)) :
    obsH S P Bc lam p t σ x = 0 := by
  simp only [obsH, hc, ite_false]

theorem obsG_of {u : ℂ} {x : S.E} (hc : ‖u‖ < 2 ∧ ‖x‖ ≤ p) :
    obsG S Bc p u x = (fderiv ℂ Bc (u • S.shiftUC x)) (S.shiftUC x) := by
  simp only [obsG, hc.1, hc.2, and_self, ite_true]

theorem obsG_of_not {u : ℂ} {x : S.E} (hc : ¬ (‖u‖ < 2 ∧ ‖x‖ ≤ p)) : obsG S Bc p u x = 0 := by
  simp only [obsG, hc, ite_false]

theorem continuous_ray (u : ℂ) : Continuous (fun x : S.E => u • S.shiftUC x) :=
  S.shiftL.continuous.const_smul u

theorem obsH_measurable {r : ℝ} (hPan : ∀ v : S.EC, ‖v‖ ≤ r → AnalyticAt ℂ P v)
    (hBan : ∀ v : S.EC, ‖v‖ ≤ r → AnalyticAt ℂ Bc v)
    (hrad : ∀ u : ℂ, ‖u‖ < 2 → ∀ x : S.E, ‖x‖ ≤ p → ‖u • S.shiftUC x‖ ≤ r) (t σ : ℂ) :
    Measurable (obsH S P Bc lam p t σ) := by
  classical
  by_cases ht : ‖t‖ < 2 ∧ ‖σ‖ < 2
  · have : obsH S P Bc lam p t σ = fun x => if ‖x‖ ≤ p then σ * (-(S.β : ℂ) * P (S.shiftUC x) +
        (lam : ℂ) * (Bc (t • S.shiftUC x) - Bc 0)) else 0 := by
      funext x
      by_cases hx : ‖x‖ ≤ p
      · rw [obsH_of ⟨ht.1, ht.2, hx⟩]; simp only [hx, ite_true]
      · rw [obsH_of_not (fun h => hx h.2.2)]; simp only [hx, ite_false]
    rw [this]
    refine measurable_cut ?_
    intro x hx
    have hx' : ‖x‖ ≤ p := by simpa using hx
    have h1 : ContinuousAt P (S.shiftUC x) := by
      have := (hPan _ (by simpa using hrad 1 (by norm_num) x hx')).continuousAt
      simpa using this
    have h2 : ContinuousAt Bc (t • S.shiftUC x) := (hBan _ (hrad t ht.1 x hx')).continuousAt
    have h3 : ContinuousAt (P ∘ fun x : S.E => S.shiftUC x) x :=
      ContinuousAt.comp (g := P) (f := fun x : S.E => S.shiftUC x) h1 S.shiftL.continuous.continuousAt
    have h4 : ContinuousAt (Bc ∘ fun x : S.E => t • S.shiftUC x) x :=
      ContinuousAt.comp (g := Bc) (f := fun x : S.E => t • S.shiftUC x) h2
        (continuous_ray t).continuousAt
    exact (continuousAt_const.mul ((continuousAt_const.mul h3).add
      (continuousAt_const.mul (h4.sub continuousAt_const)))).continuousWithinAt
  · have : obsH S P Bc lam p t σ = fun _ => 0 := by
      funext x; exact obsH_of_not (fun h => ht ⟨h.1, h.2.1⟩)
    rw [this]; exact measurable_const

theorem obsG_measurable {r : ℝ} (hBan : ∀ v : S.EC, ‖v‖ ≤ r → AnalyticAt ℂ Bc v)
    (hrad : ∀ u : ℂ, ‖u‖ < 2 → ∀ x : S.E, ‖x‖ ≤ p → ‖u • S.shiftUC x‖ ≤ r) (u : ℂ) :
    Measurable (obsG S Bc p u) := by
  classical
  by_cases hu : ‖u‖ < 2
  · have : obsG S Bc p u = fun x => if ‖x‖ ≤ p then
        (fderiv ℂ Bc (u • S.shiftUC x)) (S.shiftUC x) else 0 := by
      funext x
      by_cases hx : ‖x‖ ≤ p
      · rw [obsG_of ⟨hu, hx⟩]; simp only [hx, ite_true]
      · rw [obsG_of_not (fun h => hx h.2)]; simp only [hx, ite_false]
    rw [this]
    refine measurable_cut ?_
    intro x hx
    have hx' : ‖x‖ ≤ p := by simpa using hx
    have h1 : ContinuousAt (fderiv ℂ Bc) (u • S.shiftUC x) :=
      (hBan _ (hrad u hu x hx')).fderiv.continuousAt
    have h3 : ContinuousAt (fun x : S.E => fderiv ℂ Bc (u • S.shiftUC x)) x :=
      (ContinuousAt.comp (g := fderiv ℂ Bc) (f := fun x : S.E => u • S.shiftUC x) h1
        (continuous_ray u).continuousAt)
    exact (h3.clm_apply S.shiftL.continuous.continuousAt).continuousWithinAt
  · have : obsG S Bc p u = fun _ => 0 := by
      funext x; exact obsG_of_not (fun h => hu h.1)
    rw [this]; exact measurable_const

theorem obsH_diff_t {r : ℝ}
    (hBan : ∀ v : S.EC, ‖v‖ ≤ r → AnalyticAt ℂ Bc v)
    (hrad : ∀ u : ℂ, ‖u‖ < 2 → ∀ x : S.E, ‖x‖ ≤ p → ‖u • S.shiftUC x‖ ≤ r) (x : S.E) :
    DifferentiableOn ℂ (fun t => obsH S P Bc lam p t 1 x) (ball (0 : ℂ) 2) := by
  classical
  by_cases hx : ‖x‖ ≤ p
  · refine DifferentiableOn.congr (f := fun t => 1 * (-(S.β : ℂ) * P (S.shiftUC x) +
      (lam : ℂ) * (Bc (t • S.shiftUC x) - Bc 0))) ?_ ?_
    · intro t ht
      have ht' : ‖t‖ < 2 := by simpa using ht
      have h1 : AnalyticAt ℂ (fun t : ℂ => t • S.shiftUC x) t :=
        analyticAt_id.smul analyticAt_const
      have h2 : AnalyticAt ℂ (Bc ∘ fun t : ℂ => t • S.shiftUC x) t :=
        AnalyticAt.comp (hBan _ (hrad t ht' x hx)) h1
      exact (analyticAt_const.mul (analyticAt_const.add
        (analyticAt_const.mul (h2.sub analyticAt_const)))).differentiableAt.differentiableWithinAt
    · intro t ht
      have ht' : ‖t‖ < 2 := by simpa using ht
      exact obsH_of ⟨ht', by simp, hx⟩
  · have : (fun t => obsH S P Bc lam p t 1 x) = fun _ => 0 := by
      funext t; exact obsH_of_not (fun h => hx h.2.2)
    rw [this]; exact differentiableOn_const _

theorem obsH_diff_σ (t : ℂ) (x : S.E) :
    DifferentiableOn ℂ (fun σ => obsH S P Bc lam p t σ x) (ball (0 : ℂ) 2) := by
  classical
  by_cases hc : ‖t‖ < 2 ∧ ‖x‖ ≤ p
  · refine DifferentiableOn.congr (f := fun σ => σ * (-(S.β : ℂ) * P (S.shiftUC x) +
      (lam : ℂ) * (Bc (t • S.shiftUC x) - Bc 0))) ?_ ?_
    · exact (differentiable_id.mul_const _).differentiableOn
    · intro σ hσ
      have hσ' : ‖σ‖ < 2 := by simpa using hσ
      exact obsH_of ⟨hc.1, hσ', hc.2⟩
  · have : (fun σ => obsH S P Bc lam p t σ x) = fun _ => 0 := by
      funext σ; exact obsH_of_not (fun h => hc ⟨h.1, h.2.2⟩)
    rw [this]; exact differentiableOn_const _

theorem obsH_zero (t : ℂ) (x : S.E) : obsH S P Bc lam p t 0 x = 0 := by
  classical
  by_cases hc : ‖t‖ < 2 ∧ ‖x‖ ≤ p
  · rw [obsH_of ⟨hc.1, by simp, hc.2⟩, zero_mul]
  · exact obsH_of_not (fun h => hc ⟨h.1, h.2.2⟩)

theorem obsG_diff {r : ℝ} (hBan : ∀ v : S.EC, ‖v‖ ≤ r → AnalyticAt ℂ Bc v)
    (hrad : ∀ u : ℂ, ‖u‖ < 2 → ∀ x : S.E, ‖x‖ ≤ p → ‖u • S.shiftUC x‖ ≤ r) (x : S.E) :
    DifferentiableOn ℂ (fun u => obsG S Bc p u x) (ball (0 : ℂ) 2) := by
  classical
  by_cases hx : ‖x‖ ≤ p
  · refine DifferentiableOn.congr (f := fun u => (fderiv ℂ Bc (u • S.shiftUC x)) (S.shiftUC x))
      ?_ ?_
    · intro u hu
      have hu' : ‖u‖ < 2 := by simpa using hu
      have h1 : AnalyticAt ℂ (fun u : ℂ => u • S.shiftUC x) u :=
        analyticAt_id.smul analyticAt_const
      have h2 : AnalyticAt ℂ (fderiv ℂ Bc ∘ fun u : ℂ => u • S.shiftUC x) u :=
        AnalyticAt.comp (hBan _ (hrad u hu' x hx)).fderiv h1
      have h4 : AnalyticAt ℂ ((ContinuousLinearMap.apply ℂ ℂ (S.shiftUC x)) ∘
          (fderiv ℂ Bc ∘ fun u : ℂ => u • S.shiftUC x)) u :=
        AnalyticAt.comp ((ContinuousLinearMap.apply ℂ ℂ (S.shiftUC x)).analyticAt _) h2
      exact h4.differentiableAt.differentiableWithinAt
    · intro u hu
      have hu' : ‖u‖ < 2 := by simpa using hu
      exact obsG_of ⟨hu', hx⟩
  · have : (fun u => obsG S Bc p u x) = fun _ => 0 := by
      funext u; exact obsG_of_not (fun h => hx h.2)
    rw [this]; exact differentiableOn_const _

end Obs

section Consts

variable (d L N₁ m₁ k : ℕ) [NeZero L] [NeZero N₁]

/-- The constants of the `ObsMarks` witness: `κ' = κ₀`, `κ_H = κ' + 3κ₀ + c₁ + 3/2`. -/
noncomputable def okH : ℝ := wk0 d L + 3 * wk0 d L + c1 d L + 3 / 2
noncomputable def oεH : ℝ := 1 / (8 * wKc d L ^ 3 * c1 d L *
  Real.exp ((okH d L - 2 * wk0 d L) * cG d L + c1 d L + wk0 d L * cG d L))
/-- The cluster threshold `ε_H e^{-κ_H 𝗱(𝕋)}` of the `ObsMarks` witness. -/
noncomputable def oThr : ℝ := oεH d L * Real.exp (-okH d L * wholeLen d L N₁ m₁ k)

theorem oεH_pos : 0 < oεH d L := by
  have := wKc_pos d L
  have := one_le_c1 d L
  unfold oεH
  positivity

omit [NeZero N₁] in
theorem oThr_pos : 0 < oThr d L N₁ m₁ k := by
  have := oεH_pos d L
  unfold oThr
  positivity

end Consts

section Real

variable {d L N₁ m₁ k : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ} {pp : ℝ}
  {S : StepSetting d L N₁ m₁ k 2 ϱ}

/-- On the real ray the complex background field is the landed one. -/
theorem StepSetting.RayData.bgComp_eq (R : S.RayData pp)
    {B : S.EC → (stepG d L N₁ m₁ k ϱ).Ω 1 × Fin 2 → ℂ}
    (hB : ∀ w, S.InDom w → bgFieldC (stepG d L N₁ m₁ k ϱ) S.a S.ν (bgC0 d L 2)
      (S.dataUC (S.psi0C + w)) = B w) {s : ℝ} {x : S.E} (hq : |s| * ‖x‖ < pp)
    (y : CTorus d L N₁ m₁ (k + 1)) (i : Fin 2) :
    S.bgComp y i (s, x) = svec (stepG d L N₁ m₁ k ϱ) (B ((s : ℂ) • S.shiftUC x)) y i := by
  obtain ⟨hd, -⟩ := R.inDom_ray hq
  rw [← hB _ hd]
  have hχ := (chiU_eq_one_iff _ _ _ _).1 R.hχu
  have e : S.psi0C + (s : ℂ) • S.shiftUC x = yhat (S.psiAt s x) := by
    rw [← S.psiAtC_eq R.ha₁ R.H R.hδ'0 R.hδ' R.hD'R R.hδ0 hχ R.hfam R.hsm]; rfl
  rw [e, S.dataUC_yhat, (theorem72_real R.H (R.dom (q := (s, x)) hq)).1]
  rfl

/-- The `LabelAct` of the whole-torus label for `ObsMarks`. -/
noncomputable def obsAct (S : StepSetting d L N₁ m₁ k 2 ϱ) (hp₁ : 0 < S.p₁) (P Bc : S.EC → ℂ)
    (lam : ℝ) {r : ℝ} (hPan : ∀ v : S.EC, ‖v‖ ≤ r → AnalyticAt ℂ P v)
    (hBan : ∀ v : S.EC, ‖v‖ ≤ r → AnalyticAt ℂ Bc v)
    (hrad : ∀ u : ℂ, ‖u‖ < 2 → ∀ x : S.E, ‖x‖ ≤ S.p₁ → ‖u • S.shiftUC x‖ ≤ r)
    (hbd : ∀ t σ : ℂ, ∀ x : S.E, ‖obsH S P Bc lam S.p₁ t σ x‖ ≤ oThr d L N₁ m₁ k)
    (t σ : ℂ) :
    LabelAct (wholeLabel (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k))
      (oneBlockSplit S hp₁).Ωb (oεH d L) (okH d L) (wk0 d L) (wKc d L) where
  H := fun _ Φ => obsH S P Bc lam S.p₁ t σ (Φ cube0 : S.E)
  meas := fun _ => (obsH_measurable hPan hBan hrad t σ).comp
    (measurable_pi_apply (cube0 : _) : Measurable
      fun Φ : (∀ b, (oneBlockSplit S hp₁).Ωb b) => (Φ cube0 : S.E))
  dep := fun _ Φ Φ' h => by
    simp only [h cube0 cube0_mem]
  bound := fun _ Φ => by
    exact hbd t σ (Φ cube0 : S.E)
  entropy := whole_entropy

section Main

open Classical in
/-- **`ObsMarks` at an actual step**: the zero class, the source `g = λ 1_{(y₁,i₁)}`, the
analytic extensions `P`, `B` of the potential and the background field, and every component
`(y,i)` of the integrand `∂_t svec φ_k`. -/
theorem nonempty_obsMarks_of_tube (R : S.RayData pp) (hp₁ : 0 < S.p₁) (hlt : S.p₁ < pp)
    (y₁ : CTorus d L N₁ m₁ (k + 1)) (i₁ : Fin 2) {lam : ℝ} (hlam0 : 0 ≤ lam)
    (hlam : lam ≤ oThr d L N₁ m₁ k / 4)
    {P : S.EC → ℂ} {B : S.EC → (stepG d L N₁ m₁ k ϱ).Ω 1 × Fin 2 → ℂ} {r : ℝ}
    (hP : ∀ w, S.InDom w → S.VkC (S.psi0C + w) = P w)
    (hB : ∀ w, S.InDom w → bgFieldC (stepG d L N₁ m₁ k ϱ) S.a S.ν (bgC0 d L 2)
      (S.dataUC (S.psi0C + w)) = B w)
    (hana : ∀ v : S.EC, ‖v‖ ≤ r → AnalyticAt ℂ P v ∧ ∀ q, AnalyticAt ℂ (fun w => B w q) v)
    (hbd : ∀ v : S.EC, ‖v‖ ≤ r → ‖(S.β : ℂ) * P v‖ ≤ oThr d L N₁ m₁ k / 4 ∧
      ∀ (y : CTorus d L N₁ m₁ (k + 1)) (i : Fin 2),
        ‖svec (stepG d L N₁ m₁ k ϱ) (B v) y i - svec (stepG d L N₁ m₁ k ϱ) (B 0) y i‖ ≤ 1)
    (hrad : ∀ u : ℂ, ‖u‖ < 2 → ∀ x : S.E, ‖x‖ ≤ S.p₁ → ‖u • S.shiftUC x‖ ≤ r)
    (y : CTorus d L N₁ m₁ (k + 1)) (i : Fin 2) :
    Nonempty (ObsMarks S.nuFl (oneBlockSplit S hp₁)
      (fun t x => S.Wone (zeroClass d L N₁ m₁ k 2 ϱ) 1 x +
        S.Wtwo (zeroClass d L N₁ m₁ k 2 ϱ) (fun y i => if y = y₁ ∧ i = i₁ then (lam : ℂ) else 0) t x)
      (fun t x => deriv (fun r => McompAt (zeroClass d L N₁ m₁ k 2 ϱ).m₀
        (zeroClass d L N₁ m₁ k 2 ϱ).Tm S.a S.ν (Nat.le_succ k) (S.dataU (S.psiAt r x))
        (fun y i => if y = y₁ ∧ i = i₁ then (lam : ℂ) else 0) y i) t) cube0) := by
  set Bc1 : S.EC → ℂ := fun v => svec (stepG d L N₁ m₁ k ϱ) (B v) y₁ i₁ with hBc1
  set Bd : S.EC → ℂ := fun v => svec (stepG d L N₁ m₁ k ϱ) (B v) y i with hBd
  have hPan : ∀ v : S.EC, ‖v‖ ≤ r → AnalyticAt ℂ P v := fun v hv => (hana v hv).1
  have hBan1 : ∀ v : S.EC, ‖v‖ ≤ r → AnalyticAt ℂ Bc1 v := fun v hv =>
    analyticAt_svecFam (hana v hv).2 y₁ i₁
  have hBand : ∀ v : S.EC, ‖v‖ ≤ r → AnalyticAt ℂ Bd v := fun v hv =>
    analyticAt_svecFam (hana v hv).2 y i
  have hT := oThr_pos d L N₁ m₁ k
  -- the bound of the activity
  have hbdH : ∀ t σ : ℂ, ∀ x : S.E, ‖obsH S P Bc1 lam S.p₁ t σ x‖ ≤ oThr d L N₁ m₁ k := by
    intro t σ x
    by_cases hc : ‖t‖ < 2 ∧ ‖σ‖ < 2 ∧ ‖x‖ ≤ S.p₁
    · rw [obsH_of hc, norm_mul]
      have h1 : ‖S.shiftUC x‖ ≤ r := by simpa using hrad 1 (by norm_num) x hc.2.2
      have h2 := (hbd _ h1).1
      have h3 := (hbd _ (hrad t hc.1 x hc.2.2)).2 y₁ i₁
      have h4 : ‖-(S.β : ℂ) * P (S.shiftUC x) + (lam : ℂ) * (Bc1 (t • S.shiftUC x) - Bc1 0)‖ ≤
          oThr d L N₁ m₁ k / 2 := by
        have hn1 : ‖-(S.β : ℂ) * P (S.shiftUC x)‖ = ‖(S.β : ℂ) * P (S.shiftUC x)‖ := by
          rw [neg_mul, norm_neg]
        have hn2 : ‖(lam : ℂ) * (Bc1 (t • S.shiftUC x) - Bc1 0)‖ =
            lam * ‖Bc1 (t • S.shiftUC x) - Bc1 0‖ := by
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hlam0]
        refine (norm_add_le _ _).trans ?_
        rw [hn1, hn2]
        have : lam * ‖Bc1 (t • S.shiftUC x) - Bc1 0‖ ≤ lam * 1 :=
          mul_le_mul_of_nonneg_left h3 hlam0
        linarith
      calc ‖σ‖ * ‖-(S.β : ℂ) * P (S.shiftUC x) + (lam : ℂ) * (Bc1 (t • S.shiftUC x) - Bc1 0)‖
          ≤ 2 * (oThr d L N₁ m₁ k / 2) :=
            mul_le_mul hc.2.1.le h4 (norm_nonneg _) (by norm_num)
        _ = oThr d L N₁ m₁ k := by ring
    · rw [obsH_of_not hc, norm_zero]; exact hT.le
  -- the bound of the remainder mark
  have hcont : ContinuousOn (fderiv ℂ Bd) (closedBall (0 : S.EC) r) := fun v hv =>
    ((hBand v (by simpa using hv)).fderiv.continuousAt).continuousWithinAt
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : S.EC) r).exists_bound_of_continuousOn hcont
  set Cs := ‖S.shiftL‖ with hCs
  set M' := max M 0 with hM'
  have hM'0 : 0 ≤ M' := le_max_right _ _
  have hCs0 : 0 ≤ Cs := norm_nonneg _
  have hp0 : 0 ≤ S.p₁ := hp₁.le
  have hbdG : ∀ u : ℂ, ∀ x : S.E, ‖obsG S Bd S.p₁ u x‖ ≤ M' * (Cs * S.p₁) + 1 := by
    intro u x
    by_cases hc : ‖u‖ < 2 ∧ ‖x‖ ≤ S.p₁
    · rw [obsG_of hc]
      have h1 := hM (u • S.shiftUC x) (by simpa using hrad u hc.1 x hc.2)
      have h2 : ‖S.shiftUC x‖ ≤ Cs * S.p₁ :=
        (S.shiftL.le_opNorm x).trans (mul_le_mul_of_nonneg_left hc.2 hCs0)
      calc ‖(fderiv ℂ Bd (u • S.shiftUC x)) (S.shiftUC x)‖
          ≤ ‖fderiv ℂ Bd (u • S.shiftUC x)‖ * ‖S.shiftUC x‖ := ContinuousLinearMap.le_opNorm _ _
        _ ≤ M' * (Cs * S.p₁) := mul_le_mul (h1.trans (le_max_left _ _)) h2 (norm_nonneg _) hM'0
        _ ≤ M' * (Cs * S.p₁) + 1 := by linarith
    · rw [obsG_of_not hc, norm_zero]; positivity
  -- the integrand identity
  have hderiv : ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ x : S.E, ‖x‖ ≤ S.p₁ →
      deriv (fun r : ℝ => S.bgComp y i (r, x)) s =
        (fderiv ℂ Bd ((s : ℂ) • S.shiftUC x)) (S.shiftUC x) := by
    intro s hs x hx
    have hq : |s| * ‖x‖ < pp := by
      rw [abs_of_nonneg hs.1]
      calc s * ‖x‖ ≤ 1 * S.p₁ := mul_le_mul hs.2 hx (norm_nonneg _) zero_le_one
        _ < pp := by linarith
    have hopen : IsOpen {r : ℝ | |r| * ‖x‖ < pp} := isOpen_lt (by fun_prop) continuous_const
    have hev : (fun r : ℝ => S.bgComp y i (r, x)) =ᶠ[nhds s]
        fun r : ℝ => Bd ((r : ℂ) • S.shiftUC x) := by
      filter_upwards [hopen.mem_nhds hq] with r hr
      exact R.bgComp_eq hB hr y i
    rw [hev.deriv_eq]
    have hsr : ‖((s : ℂ)) • S.shiftUC x‖ ≤ r := by
      refine hrad (s : ℂ) ?_ x hx
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs.1]; linarith [hs.2]
    have hd : DifferentiableAt ℂ Bd ((s : ℂ) • S.shiftUC x) := (hBand _ hsr).differentiableAt
    have h1 : HasDerivAt (fun z : ℂ => z • S.shiftUC x) (S.shiftUC x) (s : ℂ) := by
      simpa using (hasDerivAt_id (s : ℂ)).smul_const (S.shiftUC x)
    have hz : HasDerivAt (Bd ∘ fun z : ℂ => z • S.shiftUC x)
        ((fderiv ℂ Bd ((s : ℂ) • S.shiftUC x)) (S.shiftUC x)) (s : ℂ) :=
      hd.hasFDerivAt.comp_hasDerivAt (s : ℂ) h1
    exact (hz.comp_ofReal).deriv
  have hF' : ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ᵐ x ∂S.nuFl,
      deriv (fun r => McompAt (zeroClass d L N₁ m₁ k 2 ϱ).m₀
        (zeroClass d L N₁ m₁ k 2 ϱ).Tm S.a S.ν (Nat.le_succ k) (S.dataU (S.psiAt r x))
        (fun y i => if y = y₁ ∧ i = i₁ then (lam : ℂ) else 0) y i) s =
        obsG S Bd S.p₁ (s : ℂ) x := by
    intro s hs
    filter_upwards [S.ae_mem_closedBall hp₁] with x hx
    have hx' : ‖x‖ ≤ S.p₁ := by simpa using hx
    have hc : ‖(s : ℂ)‖ < 2 ∧ ‖x‖ ≤ S.p₁ := by
      refine ⟨?_, hx'⟩
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs.1]; linarith [hs.2]
    rw [obsG_of hc, ← hderiv s hs x hx']
    congr 1
    funext r
    exact McompAt_zero_eq _ _ _ _ _ _ _ _
  have hW' : ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ᵐ x ∂S.nuFl,
      S.Wone (zeroClass d L N₁ m₁ k 2 ϱ) 1 x +
        S.Wtwo (zeroClass d L N₁ m₁ k 2 ϱ) (fun y i => if y = y₁ ∧ i = i₁ then (lam : ℂ) else 0)
          s x = obsH S P Bc1 lam S.p₁ (s : ℂ) 1 x := by
    intro s hs
    filter_upwards [S.ae_mem_closedBall hp₁] with x hx
    have hx' : ‖x‖ ≤ S.p₁ := by simpa using hx
    have hq1 : |(1 : ℝ)| * ‖x‖ < pp := by
      rw [abs_one, one_mul]; linarith
    have hqs : |s| * ‖x‖ < pp := by
      rw [abs_of_nonneg hs.1]
      calc s * ‖x‖ ≤ 1 * S.p₁ := mul_le_mul hs.2 hx' (norm_nonneg _) zero_le_one
        _ < pp := by linarith
    have hq0 : |(0 : ℝ)| * ‖x‖ < pp := by
      rw [abs_zero, zero_mul]; exact R.hpp
    have hc : ‖(s : ℂ)‖ < 2 ∧ ‖(1 : ℂ)‖ < 2 ∧ ‖x‖ ≤ S.p₁ := by
      refine ⟨?_, by simp, hx'⟩
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs.1]; linarith [hs.2]
    rw [obsH_of hc, StepSetting.Wone_zeroClass, StepSetting.Wtwo_single]
    obtain ⟨hd1, hv1⟩ := R.inDom_ray hq1
    have e1 : S.Vk (S.psiAt 1 x) = P (S.shiftUC x) := by
      rw [← hv1, hP _ hd1]; simp
    have e2 := R.bgComp_eq hB hqs y₁ i₁
    have e3 := R.bgComp_eq hB hq0 y₁ i₁
    simp only [Complex.ofReal_zero, zero_smul] at e3
    rw [e1, e2, e3]
    simp [hBc1]
  have hb0 : (cube0 : CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) 0 (k + 1)
      Set.univ) ∈ blocksOf (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) 0 (k + 1)
        Set.univ Set.univ := by
    rw [mem_blocksOf]; exact Set.subset_univ _
  have hK0 := wk0_pos d L
  have hdl0 := wholeLen_nonneg d L N₁ m₁ k
  have hex : 0 ≤ okH d L := by unfold okH; have := one_le_c1 d L; linarith
  refine ⟨{
    Lb := Unit
    Lab := wholeLabel
    εH := oεH d L
    κH := okH d L
    κG := okH d L
    κ0 := wk0 d L
    κ' := wk0 d L
    Kc := wKc d L
    hN := by simp
    Rσ := 2
    hRσ := by norm_num
    𝒰 := ball (0 : ℂ) 2
    isOpen := isOpen_ball
    seg := fun s hs => by
      rw [mem_ball, dist_zero_right, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs.1]
      linarith [hs.2]
    A := fun t σ => obsAct S hp₁ P Bc1 lam hPan hBan1 hrad hbdH t σ
    holt := fun _ Φ => obsH_diff_t hBan1 hrad (Φ cube0 : S.E)
    holσ := fun s hs _ Φ => obsH_diff_σ (S := S) (P := P) (Bc := Bc1) (lam := lam) (p := S.p₁)
      (s : ℂ) (Φ cube0 : S.E)
    zero := fun s hs _ Φ => obsH_zero (S := S) (P := P) (Bc := Bc1) (lam := lam) (p := S.p₁)
      (s : ℂ) (Φ cube0 : S.E)
    hW := fun s hs => by
      filter_upwards [hW' s hs] with x hx
      rw [hx]
      simp [obsAct, oneBlockSplit, oneBlockMap]
    ι1 := Unit
    y1 := fun _ => ()
    G1 := fun _ _ => 0
    meas1 := fun _ => measurable_const
    dep1 := fun _ _ _ _ => rfl
    F1 := fun _ => 1
    hF1 := fun _ => one_pos
    bound1 := fun i Φ => by simp only [norm_zero]; positivity
    mean1 := fun _ => by simp
    Fm := 1
    hFm := fun _ => by
      have : Real.exp (-wk0 d L * wholeLen d L N₁ m₁ k) ≤ 1 :=
        Real.exp_le_one_iff.2 (by nlinarith)
      simpa [wholeLabel] using this
    bm := fun _ => cube0
    hbm := fun _ => cube0_mem
    nmax := 1
    hnmax := zero_le_one
    hcount := fun c => by
      have : (Finset.univ.filter fun _ : Unit => cube0 = c).card ≤ 1 :=
        (Finset.card_filter_le _ _).trans (by simp)
      exact_mod_cast this
    hker := fun _ _ => 0
    Ch := 0
    κh := wk0 d L
    hCh := le_rfl
    bound_h := fun _ _ => by simp
    supp_h := fun _ _ _ => rfl
    x_h := fun _ _ _ => rfl
    hκh := le_rfl
    hFm0 := zero_le_one
    ιr := Unit
    nonemptyr := ⟨()⟩
    yr := fun _ => ()
    Gr := fun _ u Φ => obsG S Bd S.p₁ u (Φ cube0 : S.E)
    measr := fun _ u => (obsG_measurable hBand hrad u).comp
      (measurable_pi_apply (cube0 : _) : Measurable
        fun Φ : (∀ b, (oneBlockSplit S hp₁).Ωb b) => (Φ cube0 : S.E))
    depr := fun _ u Φ Φ' h => by
      simp only [h cube0 cube0_mem]
    Fr := fun _ => (M' * (Cs * S.p₁) + 1) * Real.exp (okH d L * wholeLen d L N₁ m₁ k)
    hFr := fun _ => by positivity
    boundr := fun _ u Φ => by
      have key : ∀ x : S.E, ‖obsG S Bd S.p₁ u x‖ ≤
          (M' * (Cs * S.p₁) + 1) * Real.exp (okH d L * wholeLen d L N₁ m₁ k) *
            Real.exp (-okH d L * wholeLen d L N₁ m₁ k) := by
        intro x
        rw [mul_assoc, ← Real.exp_add]
        have : okH d L * wholeLen d L N₁ m₁ k + -okH d L * wholeLen d L N₁ m₁ k = 0 := by ring
        rw [this, Real.exp_zero, mul_one]
        exact hbdG u x
      exact key (Φ cube0 : S.E)
    holGr := fun _ Φ => obsG_diff hBand hrad (Φ cube0 : S.E)
    x_r := fun _ => cube0_mem
    hκ0 := le_rfl
    hKc := le_rfl
    hεpos := oεH_pos d L
    hκ' := by linarith
    hκ0' := le_rfl
    hκG := le_rfl
    hκ := by unfold okH; linarith
    hε := le_rfl
    hF := fun s hs => by
      filter_upwards [hF' s hs] with x hx
      rw [hx]
      simp [oneBlockSplit, oneBlockMap] }⟩


end Main

/-- **The background field moves along the ray at every scale**: for every `p ∈ (0, p⁺)` there is
`ψ̂₀` with `‖ψ̂₀‖ < p` and a component of `svec φ_k` with `φ_k(ψ^{(k)} + ψ'(ψ̂₀)) ≠ φ_k(ψ^{(k)})`
(the second half of `exists_small_radius` at a prescribed `p`). -/
theorem StepSetting.RayData.exists_bgComp_ne (R : S.RayData pp) (hν : S.ν = 0)
    (hbg0 : bgField S.G' S.a S.ν S.D' = unitPhi S.G' hN2) {p : ℝ} (hp0 : 0 < p) (hppp : p < pp) :
    ∃ x₀ : S.E, ‖x₀‖ < p ∧ ∃ (y : CTorus d L N₁ m₁ (k + 1)) (i : Fin 2),
      S.bgComp y i (1, x₀) ≠ S.bgComp y i (0, x₀) := by
  classical
  set u : S.E := S.unshiftU S.cvec with hu
  set τ : ℝ := p / (2 * (‖u‖ + 1)) with hτ
  have hτ0 : 0 < τ := by positivity
  set x₀ : S.E := τ • u with hx₀
  have hx₀n : ‖x₀‖ < p := by
    rw [hx₀, norm_smul, Real.norm_eq_abs, abs_of_pos hτ0, hτ]
    have : p / (2 * (‖u‖ + 1)) * ‖u‖ < p := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
      nlinarith [norm_nonneg u]
    exact this
  have hsh : S.shiftU x₀ = τ • S.cvec := by
    rw [hx₀, StepSetting.shiftU_smul, hu, R.shiftU_unshiftU]
  have hdom := R.dom (q := ((1 : ℝ), x₀)) (by
    simp only [abs_one, one_mul]
    exact hx₀n.trans hppp)
  have hψ : ∀ x, liftU S.hG' (S.psiAt 1 x₀) x 1 = liftU S.hG' S.psi0 x 1 + τ := by
    intro x
    have : S.psiAt 1 x₀ = S.psi0 + τ • S.cvec := by
      unfold StepSetting.psiAt; rw [one_smul, hsh]
    rw [this, liftU_add, liftU_smul]
    have h1 : liftU S.hG' S.cvec x 1 = 1 := by
      show (S.cvec (unitPt S.hG' x)) 1 = 1
      simp [StepSetting.cvec]
    rw [h1, mul_one]
  have hne := R.bgField_ne hν hbg0 hdom hτ0.ne' hψ
  refine ⟨x₀, hx₀n, ?_⟩
  by_contra hcon
  push Not at hcon
  apply hne
  funext pq
  obtain ⟨⟨z, hz⟩, i⟩ := pq
  have h := hcon z i
  unfold StepSetting.bgComp at h
  rw [svec_of_mem _ _ ⟨z, hz⟩ i, svec_of_mem _ _ ⟨z, hz⟩ i] at h
  simpa [psiAt_zero] using h

end Real

section Datum

open Balaban.Inhabited Balaban.Localization.I5Inhabited

/-- **`ObsMarks` at an actual, non-degenerate step.**  The datum of `exists_activity_datum` with
the source `g = λ 1_{(y₁,i₁)}` and a small cutoff radius `p₁`: the exponent `W₁(1) + W₂(t)` is
not identically zero (it is nonzero at some `ψ̂₀` with `‖ψ̂₀‖ ≤ p₁`), and, for every component
`(y,i)` of the integrand `∂_t svec φ_k`, the structure `ObsMarks` is inhabited with the
single whole-torus label. -/
theorem exists_obsMarks_datum :
    ∃ (m₁ : ℕ) (S : StepSetting 3 3 6 m₁ 1 2 (rhoSep m₁)) (g : Fld 3 3 6 m₁ 2 2)
      (BS : BlockSplit S 0),
      0 < S.β ∧ 0 < S.p₁ ∧ S.p₁ < 2 ∧ Nonempty (S.RayData 2) ∧
      (∃ x : S.E, ‖x‖ ≤ S.p₁ ∧ S.Wone (zeroClass 3 3 6 m₁ 1 2 (rhoSep m₁)) 1 x +
        S.Wtwo (zeroClass 3 3 6 m₁ 1 2 (rhoSep m₁)) g 1 x ≠ 0) ∧
      ∀ (y : CTorus 3 3 6 m₁ 2) (i : Fin 2),
        Nonempty (ObsMarks S.nuFl BS
          (fun t x => S.Wone (zeroClass 3 3 6 m₁ 1 2 (rhoSep m₁)) 1 x +
            S.Wtwo (zeroClass 3 3 6 m₁ 1 2 (rhoSep m₁)) g t x)
          (fun t x => deriv (fun r => McompAt (zeroClass 3 3 6 m₁ 1 2 (rhoSep m₁)).m₀
            (zeroClass 3 3 6 m₁ 1 2 (rhoSep m₁)).Tm S.a S.ν (Nat.le_succ 1)
            (S.dataU (S.psiAt r x)) g y i) t) cube0) := by
  classical
  obtain ⟨m₁, δ, δ', T, hm, hbig, hδ, hsm, hδ'0, hδ'a, hδ'b, hδ'c, hT, -, hT1, hT2⟩ :=
    exists_witness_params (fun _ => 0)
  obtain ⟨R0⟩ := rayData_witness hm hbig hδ hsm hδ'0 hδ'a hδ'b hδ'c hT hT1 hT2
  set S0 := witnessSetting m₁ (T ^ 2 / 3) δ with hS0
  have hbg0 := activityWitness_bgField R0
  have hβ : 0 < S0.β := R0.hβ
  have hThr := oThr_pos 3 3 6 m₁ 1
  obtain ⟨P, B, r, p, hr, hp, hpp, hP, hB, hana, hbd, hrad⟩ :=
    StepSetting.exists_tube_obs (S := S0) R0 (show 0 < oThr 3 3 6 m₁ 1 / 4 by positivity)
  obtain ⟨x₀, hx₀, y₁, i₁, hne⟩ := R0.exists_bgComp_ne rfl hbg0 hp hpp
  have hw : S0.bgComp y₁ i₁ (1, x₀) - S0.bgComp y₁ i₁ (0, x₀) ≠ 0 := sub_ne_zero.2 hne
  obtain ⟨lam, hl0, hl1, hlne⟩ := exists_lam_ne
    (a := -(S0.β : ℂ) * S0.Vk (S0.psiAt 1 x₀)) hw (l₀ := oThr 3 3 6 m₁ 1 / 4) (by positivity)
  let S1 : StepSetting 3 3 6 m₁ 1 2 (rhoSep m₁) := { S0 with p₁ := p }
  have R1 : S1.RayData 2 :=
    { ha₁ := R0.ha₁, H := R0.H, δ' := R0.δ', hδ'0 := R0.hδ'0, hδ' := R0.hδ', hD'R := R0.hD'R,
      hδ0 := R0.hδ0, hfam := R0.hfam, hsm := R0.hsm, hχu := R0.hχu, hnorm := R0.hnorm,
      hβ := R0.hβ, hpp := R0.hpp, B₅ := R0.B₅, K₂ := R0.K₂, hB5 := R0.hB5, hK2 := R0.hK2,
      hp40 := R0.hp40, hrad := R0.hrad }
  refine ⟨m₁, S1, fun y i => if y = y₁ ∧ i = i₁ then (lam : ℂ) else 0, oneBlockSplit S1 hp, hβ,
    hp, hpp, ⟨R1⟩, ⟨x₀, hx₀.le, ?_⟩, fun y i => ?_⟩
  · have e1 : S1.Wone (zeroClass 3 3 6 m₁ 1 2 (rhoSep m₁)) 1 x₀ =
        -(S0.β : ℂ) * S0.Vk (S0.psiAt 1 x₀) := StepSetting.Wone_zeroClass S1 1 x₀
    have e2 := StepSetting.Wtwo_single S1 y₁ i₁ lam 1 x₀
    show S1.Wone _ 1 x₀ + S1.Wtwo _ _ 1 x₀ ≠ 0
    rw [e1, e2]
    exact hlne
  · exact nonempty_obsMarks_of_tube (S := S1) R1 hp hpp y₁ i₁ hl0.le hl1 (P := P) (B := B) (r := r)
      hP hB hana hbd hrad y i

/-- **Theorem 3.1 (b) at an actual step, unconditionally**: for every component `(y,i)`,
`M₀^{(2)}(y; g) = β_k^{1/2} ∑_W E(W)`, `E(W) = 0` unless `W ∋ x`, and
`|E(W)| ≤ (B₁ + B₂) e^{-κ_b d_Ω(W)}` with `κ_b = min(κ_h, κ') - κ₀ - 1`. -/
theorem thm31b_witness :
    ∃ (m₁ : ℕ) (S : StepSetting 3 3 6 m₁ 1 2 (rhoSep m₁)) (g : Fld 3 3 6 m₁ 2 2)
      (BS : BlockSplit S 0),
      0 < S.β ∧ 0 < S.p₁ ∧ Nonempty (S.RayData 2) ∧
      (∃ x : S.E, ‖x‖ ≤ S.p₁ ∧ S.Wone (zeroClass 3 3 6 m₁ 1 2 (rhoSep m₁)) 1 x +
        S.Wtwo (zeroClass 3 3 6 m₁ 1 2 (rhoSep m₁)) g 1 x ≠ 0) ∧
      ∀ (y : CTorus 3 3 6 m₁ 2) (i : Fin 2),
        ∃ I : ObsMarks S.nuFl BS
            (fun t x => S.Wone (zeroClass 3 3 6 m₁ 1 2 (rhoSep m₁)) 1 x +
              S.Wtwo (zeroClass 3 3 6 m₁ 1 2 (rhoSep m₁)) g t x)
            (fun t x => deriv (fun r => McompAt (zeroClass 3 3 6 m₁ 1 2 (rhoSep m₁)).m₀
              (zeroClass 3 3 6 m₁ 1 2 (rhoSep m₁)).Tm S.a S.ν (Nat.le_succ 1)
              (S.dataU (S.psiAt r x)) g y i) t) cube0,
          ∃ E : Finset (CubeB (d := 3) (L := 3) (N₁ := 6) (m₁ := m₁) (K := 1 + 1) 0 (1 + 1)
              Set.univ) → ℂ,
            S.M0 (zeroClass 3 3 6 m₁ 1 2 (rhoSep m₁)) g y i =
                ((S.betaU ^ (1 / 2 : ℝ) : ℝ) : ℂ) * ∑ T, E T ∧
            (∀ T, cube0 ∉ T → E T = 0) ∧
            ∀ T, ‖E T‖ ≤ (I.B1 + I.B2) *
              Real.exp (-(min I.κh I.κ' - I.κ0 - 1) * dExt T) := by
  obtain ⟨m₁, S, g, BS, hβ, hp, -, hR, hnz, hI⟩ := exists_obsMarks_datum
  refine ⟨m₁, S, g, BS, hβ, hp, hR, hnz, fun y i => ?_⟩
  obtain ⟨I⟩ := hI y i
  obtain ⟨E, h1, h2, h3⟩ := thm31b_of_input_M0 S (zeroClass 3 3 6 m₁ 1 2 (rhoSep m₁)) BS g y i I
    (κb := min I.κh I.κ' - I.κ0 - 1) le_rfl
  exact ⟨I, E, h1, h2, h3⟩

end Datum

end Balaban.Fluctuation
