/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.ParamCarrierLocal
public import Balaban.Fluctuation.HatLabelsDirect
public import Balaban.Fluctuation.PhysicalTerms
public import Balaban.Fluctuation.HatLabelsDep
public import Balaban.Fluctuation.HatDiagContBase
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Physical label activities with the datum free

The landed route `physical_directTerms` → `labelAct_of_directTerms` freezes the block datum at one
point `Θ₀`.  The point `Θ₀` enters `DirectTerms` in exactly three fields: `mem` (`Θ₀ ∈ SΛ`),
`agΘ` (reflexivity of the source agreement at `Θ₀`) and `meas` (measurability of the diagonal terms
at `Θ₀`); the domains, the terms, the bound, the locality relation and all constants do not involve
`Θ₀`.  Here the activity is rebuilt for every datum `Θ` of an open set `V ⊆ SΛ`.

* `StepSetting.continuous_hatOf`, `continuous_term_hatOf`: the hat map is continuous, and so are
  the diagonal terms composed with it (from `DiagCont`).
* `DirectTermsFamily`, `DirectTerms.atTheta`: the family hypothesis (the same terms, the same
  constants, an open set `V ⊆ SΛ`, reflexivity of the source agreement and continuity of the
  diagonal terms on `V`) and the resulting `DirectTerms` at each `Θ ∈ V`.
* `dtAct`, `labelActFamily`: the activity of `labelAct_of_directTerms` (same formula) at a given
  `DirectTerms`, and the family over the datum.
* `labelActFamily_analytic`: joint analyticity in `(Θ, u)` on `V ×ˢ ball 0 Rσ`.
* `paramMarkFamily_of_marks`, `paramMarkFamily_zero_marks`: the `ParamMarkFamily` with the
  physical activities, carrier `physCarrier`, `𝒰 = ball 0 Rσ`.
* `labelActFamily_local`, `physical_labelActFamily_local`: locality in the datum.
* `nonempty_directTermsFamily`: the family hypothesis is inhabited.

No marks are constructed (they are data satisfying their own fields, or zero), the determinant term
is not treated, and nothing depends on a choice of generating set for the class terms.
-/

@[expose] public section

namespace Balaban.Fluctuation

open MeasureTheory Balaban Balaban.Localization Balaban.Multiscale Balaban.Polymer
  Balaban.Background Metric

section Hat

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}
  (S : StepSetting d L N₁ m₁ k N ϱ) (m₀ : ℕ)

/-- **Continuity of the hat map.**  The hat variable of the block variables is continuous in the
block configuration (product topology). -/
theorem StepSetting.continuous_hatOf (ρ : ℝ) (hp : 0 < S.p₁) :
    Continuous (S.hatOf m₀ ρ hp) := by
  refine continuous_pi fun q => ?_
  have h1 : Continuous (fun Φ : (∀ b, (S.blockSplit m₀ hp).Ωb b) =>
      Φ (S.cellOf m₀ q.1) ⟨q.1, rfl⟩ q.2) :=
    (EuclideanSpace.proj q.2).continuous.comp
      ((continuous_apply (⟨q.1, rfl⟩ : {u : S.U // S.cellOf m₀ u = S.cellOf m₀ q.1})).comp
        (continuous_apply (S.cellOf m₀ q.1)))
  exact (continuous_clampC ρ).comp (Complex.continuous_ofReal.comp h1)

end Hat

section Family

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}
  (S : StepSetting d L N₁ m₁ k N ϱ) (m₀ : ℕ) {Λ F' : Type}
  [NormedAddCommGroup Λ] [NormedSpace ℂ Λ]
  {hp : 0 < S.p₁} {emb : (S.U × Fin N → ℂ) → F'} {ρ Rσ εU a : ℝ} {Θ₀ : Λ}
  {SΛ : Set Λ} {XW : Set (F' × F')} {val : F' → F' → ℂ → Λ → ℂ}
  {AgΘ : Set (CTorus d L N₁ m₁ (k + 1)) → Λ → Λ → Prop}
  {AgF : Set (CTorus d L N₁ m₁ (k + 1)) → F' → F' → Prop}

/-- **Continuity of the diagonal terms composed with the hat map.**  If the diagonal terms are
continuous on the admissible set (`DiagCont`, the field `cont` of `LocIntDm`), then for fixed
`σ` and `Θ` the map `Φ ↦ T_Y(ψ̂(Φ), ψ̂(Φ), σ, Θ)` is continuous on all block configurations, in
particular on `physCarrier`: the hat variable always lies in the disk `hatDisk`, which is admissible
by the field `xw`. -/
theorem continuous_term_hatOf
    (I : DirectTerms S m₀ hp emb ρ Rσ εU a Θ₀ SΛ XW val AgΘ AgF) (hρ : 0 < ρ) {V : Set Λ}
    (hc : DiagCont emb XW V Rσ I.𝒴 I.T) {Y : Set (CTorus d L N₁ m₁ (k + 1))} (hY : Y ∈ I.𝒴)
    {σ : ℂ} (hσ : ‖σ‖ < Rσ) {Θ : Λ} (hΘ : Θ ∈ V) :
    Continuous (fun Φ : (∀ b, (S.blockSplit m₀ hp).Ωb b) =>
      I.T Y (emb (S.hatOf m₀ ρ hp Φ)) (emb (S.hatOf m₀ ρ hp Φ)) σ Θ) := by
  have h := (hc Y hY σ hσ Θ hΘ).comp_continuous (S.continuous_hatOf m₀ ρ hp)
    (fun Φ => I.xw _ (S.hatOf_mem m₀ hρ hp Φ))
  exact h

/-- **The family hypothesis** (the datum is free).  `V ⊆ SΛ` is open; the source agreement is
reflexive on `V`; the diagonal terms `ψ ↦ T_Y(ψ, ψ, σ, Θ)` are continuous on the admissible set,
for every `Θ ∈ V` (this is the field `cont` of `LocIntDm`, for the physical expansion the field
`cont` of `PhysExpansion`).  The domains, terms, bound and locality are those of the base
`DirectTerms` `I`. -/
structure DirectTermsFamily
    (I : DirectTerms S m₀ hp emb ρ Rσ εU a Θ₀ SΛ XW val AgΘ AgF) (V : Set Λ) : Prop where
  isOpen : IsOpen V
  sub : V ⊆ SΛ
  agΘ : ∀ Θ ∈ V, ∀ Y, AgΘ Y Θ Θ
  cont : DiagCont emb XW V Rσ I.𝒴 I.T

/-- **`DirectTerms` at a datum `Θ ∈ V`**: the same domains, terms, bound, locality and constants
as the base; only `mem`, `agΘ`, `meas` (the three fields in which the base point enters) are
re-proved at `Θ`. -/
noncomputable def DirectTerms.atTheta
    (I : DirectTerms S m₀ hp emb ρ Rσ εU a Θ₀ SΛ XW val AgΘ AgF) {V : Set Λ}
    (hF : DirectTermsFamily S m₀ I V) {Θ : Λ} (hΘ : Θ ∈ V) :
    DirectTerms S m₀ hp emb ρ Rσ εU a Θ SΛ XW val AgΘ AgF :=
  { I with
    mem := hF.sub hΘ
    agΘ := hF.agΘ Θ hΘ
    meas := fun Y hY σ hσ => by
      have hc := hF.cont Y hY σ hσ Θ hΘ
      refine (continuousOn_iff_continuous_domRestrict.1 (hc.mono ?_)).measurable
      intro ψ hψ
      exact I.xw ψ hψ }

open Classical in
/-- **The activity of `labelAct_of_directTerms`** at the base point of `I`: the label `Y` has
activity `T_Y` at the hat variable of `Φ` for `‖u‖ < Rσ`, and `0` otherwise. -/
noncomputable def dtH (I : DirectTerms S m₀ hp emb ρ Rσ εU a Θ₀ SΛ XW val AgΘ AgF) (u : ℂ)
    (Y : {Y // Y ∈ I.𝒴}) (Φ : ∀ b, (S.blockSplit m₀ hp).Ωb b) : ℂ :=
  if ‖u‖ < Rσ then I.T Y.1 (emb (S.hatOf m₀ ρ hp Φ)) (emb (S.hatOf m₀ ρ hp Φ)) u Θ₀ else 0

theorem dtH_meas (I : DirectTerms S m₀ hp emb ρ Rσ εU a Θ₀ SΛ XW val AgΘ AgF) (hρ : 0 < ρ)
    (u : ℂ) (Y : {Y // Y ∈ I.𝒴}) : Measurable (dtH S m₀ I u Y) := by
  by_cases hu : ‖u‖ < Rσ
  · have : dtH S m₀ I u Y = fun Φ => I.T Y.1 (emb (S.hatOf m₀ ρ hp Φ))
        (emb (S.hatOf m₀ ρ hp Φ)) u Θ₀ := funext fun Φ => by simp [dtH, hu]
    rw [this]
    exact (I.meas Y.1 Y.2 u hu).comp (S.measurable_hatOf m₀ ρ hρ hp)
  · have : dtH S m₀ I u Y = fun _ => 0 := funext fun Φ => by simp [dtH, hu]
    rw [this]
    exact measurable_const

theorem dtH_dep (I : DirectTerms S m₀ hp emb ρ Rσ εU a Θ₀ SΛ XW val AgΘ AgF) (hρ : 0 < ρ)
    (u : ℂ) (Y : {Y // Y ∈ I.𝒴}) :
    DepOn (blocksOf m₀ (k + 1) Set.univ Y.1) (dtH S m₀ I u Y) := by
  intro Φ Φ' h
  by_cases hu : ‖u‖ < Rσ
  · simp only [dtH, hu, ite_true]
    have hAg := I.ag Y.1 Y.2 Φ Φ' h
    exact I.loc.loc Y.1 Y.2 (emb (S.hatOf m₀ ρ hp Φ), emb (S.hatOf m₀ ρ hp Φ))
      (I.xw _ (S.hatOf_mem m₀ hρ hp Φ)) (emb (S.hatOf m₀ ρ hp Φ'), emb (S.hatOf m₀ ρ hp Φ'))
      (I.xw _ (S.hatOf_mem m₀ hρ hp Φ')) u hu Θ₀ I.mem Θ₀ I.mem (I.agΘ Y.1) hAg hAg
  · simp [dtH, hu]

theorem dtH_bound (I : DirectTerms S m₀ hp emb ρ Rσ εU a Θ₀ SΛ XW val AgΘ AgF) (hρ : 0 < ρ)
    (hRσ : 0 ≤ Rσ) (hεU : 0 ≤ εU) (u : ℂ) (Y : {Y // Y ∈ I.𝒴}) (Φ) :
    ‖dtH S m₀ I u Y Φ‖ ≤ Rσ * εU * Real.exp (-a * treeLenCovOne m₀ (k + 1) Y.1) := by
  by_cases hu : ‖u‖ < Rσ
  · simp only [dtH, hu, ite_true]
    have h1 := I.loc.bound Y.1 Y.2 (emb (S.hatOf m₀ ρ hp Φ), emb (S.hatOf m₀ ρ hp Φ))
      (I.xw _ (S.hatOf_mem m₀ hρ hp Φ)) u hu Θ₀ I.mem
    have h4 : ‖u‖ * I.b Y.1 ≤ ‖u‖ * (εU * Real.exp (-a * treeLenCovOne m₀ (k + 1) Y.1)) :=
      mul_le_mul_of_nonneg_left (I.bd Y.1 Y.2) (norm_nonneg u)
    have h5 : ‖u‖ * (εU * Real.exp (-a * treeLenCovOne m₀ (k + 1) Y.1)) ≤
        Rσ * (εU * Real.exp (-a * treeLenCovOne m₀ (k + 1) Y.1)) :=
      mul_le_mul_of_nonneg_right hu.le (by positivity)
    calc _ ≤ _ := h1.trans (h4.trans h5)
      _ = _ := by ring
  · simp only [dtH, hu, ite_false, norm_zero]
    positivity

/-- **The label activity of `labelAct_of_directTerms`** (explicit form): labels are the domains
`I.𝒴`, activity `dtH`, rate `a`, size `Rσ εU`. -/
noncomputable def dtAct (I : DirectTerms S m₀ hp emb ρ Rσ εU a Θ₀ SΛ XW val AgΘ AgF)
    (hN : L ^ m₀ ∣ N₁) (hρ : 0 < ρ) (hRσ : 0 ≤ Rσ) (hεU : 0 ≤ εU)
    {κ0 Kc : ℝ} (hκ0 : aEnt d L + 1 ≤ κ0) (hKc : K0 d L κ0 ≤ Kc) (u : ℂ) :
    LabelAct (thickLabels I.𝒴 I.dom) (S.blockSplit m₀ hp).Ωb (Rσ * εU) a κ0 Kc where
  H := dtH S m₀ I u
  meas := dtH_meas S m₀ I hρ u
  dep := dtH_dep S m₀ I hρ u
  bound := fun Y Φ => dtH_bound S m₀ I hρ hRσ hεU u Y Φ
  entropy := fun b => (entropy_thick hN le_rfl I.𝒴 I.dom hκ0 b).trans hKc

/-- The conclusions of `labelAct_of_directTerms` hold for `dtAct`: holomorphic in `u` on the disk,
and summing to the expanded function. -/
theorem dtAct_spec (I : DirectTerms S m₀ hp emb ρ Rσ εU a Θ₀ SΛ XW val AgΘ AgF)
    (hN : L ^ m₀ ∣ N₁) (hρ : 0 < ρ) (hRσ : 0 ≤ Rσ) (hεU : 0 ≤ εU)
    {κ0 Kc : ℝ} (hκ0 : aEnt d L + 1 ≤ κ0) (hKc : K0 d L κ0 ≤ Kc) :
    (∀ y Φ, DifferentiableOn ℂ (fun u => (dtAct S m₀ I hN hρ hRσ hεU hκ0 hKc u).H y Φ)
      (Metric.ball 0 Rσ)) ∧
    (∀ u : ℂ, ‖u‖ < Rσ → ∀ Φ, ∑ y, (dtAct S m₀ I hN hρ hRσ hεU hκ0 hKc u).H y Φ =
      val (emb (S.hatOf m₀ ρ hp Φ)) (emb (S.hatOf m₀ ρ hp Φ)) u Θ₀) := by
  refine ⟨fun Y Φ => ?_, fun u hu Φ => ?_⟩
  · have han : AnalyticOnNhd ℂ (fun p : Λ × ℂ => I.T Y.1 (emb (S.hatOf m₀ ρ hp Φ))
        (emb (S.hatOf m₀ ρ hp Φ)) p.2 p.1) (SΛ ×ˢ Metric.ball (0 : ℂ) Rσ) :=
      I.loc.analytic Y.1 Y.2 (emb (S.hatOf m₀ ρ hp Φ), emb (S.hatOf m₀ ρ hp Φ))
        (I.xw _ (S.hatOf_mem m₀ hρ hp Φ))
    have hc : AnalyticOnNhd ℂ (fun u : ℂ => ((Θ₀, u) : Λ × ℂ)) (Metric.ball 0 Rσ) :=
      AnalyticOnNhd.prod (analyticOnNhd_const : AnalyticOnNhd ℂ (fun _ : ℂ => Θ₀)
        (Metric.ball 0 Rσ)) (analyticOnNhd_id : AnalyticOnNhd ℂ (fun u : ℂ => u)
          (Metric.ball 0 Rσ))
    have hd := (han.comp hc (fun u hu => ⟨I.mem, hu⟩)).differentiableOn
    refine hd.congr fun u hu => ?_
    have hu' : ‖u‖ < Rσ := by simpa using hu
    simp [dtAct, dtH, hu']
  · show ∑ Y : {Y // Y ∈ I.𝒴}, dtH S m₀ I u Y Φ = _
    simp only [dtH, hu, ite_true]
    rw [Finset.sum_coe_sort I.𝒴 (fun Y => I.T Y (emb (S.hatOf m₀ ρ hp Φ))
      (emb (S.hatOf m₀ ρ hp Φ)) u Θ₀)]
    exact (I.loc.sum (emb (S.hatOf m₀ ρ hp Φ), emb (S.hatOf m₀ ρ hp Φ))
      (I.xw _ (S.hatOf_mem m₀ hρ hp Φ)) u hu Θ₀ I.mem).symm

open Classical in
/-- **The family of label activities over the datum.**  For `Θ ∈ V` the activity is `dtAct` of
`I.atTheta Θ`, that is the activity of `labelAct_of_directTerms` with `Θ₀ := Θ`; for `Θ ∉ V` (not
used) it is the base activity. -/
noncomputable def labelActFamily (I : DirectTerms S m₀ hp emb ρ Rσ εU a Θ₀ SΛ XW val AgΘ AgF)
    {V : Set Λ} (hF : DirectTermsFamily S m₀ I V)
    (hN : L ^ m₀ ∣ N₁) (hρ : 0 < ρ) (hRσ : 0 ≤ Rσ) (hεU : 0 ≤ εU)
    {κ0 Kc : ℝ} (hκ0 : aEnt d L + 1 ≤ κ0) (hKc : K0 d L κ0 ≤ Kc) (Θ : Λ) (u : ℂ) :
    LabelAct (thickLabels I.𝒴 I.dom) (S.blockSplit m₀ hp).Ωb (Rσ * εU) a κ0 Kc :=
  if h : Θ ∈ V then dtAct S m₀ (I.atTheta S m₀ hF h) hN hρ hRσ hεU hκ0 hKc u
  else dtAct S m₀ I hN hρ hRσ hεU hκ0 hKc u


end Family

section Activity

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}
  (S : StepSetting d L N₁ m₁ k N ϱ) (m₀ : ℕ) {Λ F' : Type}
  [NormedAddCommGroup Λ] [NormedSpace ℂ Λ]
  {hp : 0 < S.p₁} {emb : (S.U × Fin N → ℂ) → F'} {ρ Rσ εU a : ℝ} {Θ₀ : Λ}
  {SΛ : Set Λ} {XW : Set (F' × F')} {val : F' → F' → ℂ → Λ → ℂ}
  {AgΘ : Set (CTorus d L N₁ m₁ (k + 1)) → Λ → Λ → Prop}
  {AgF : Set (CTorus d L N₁ m₁ (k + 1)) → F' → F' → Prop}
  {I : DirectTerms S m₀ hp emb ρ Rσ εU a Θ₀ SΛ XW val AgΘ AgF} {V : Set Λ}
  (hF : DirectTermsFamily S m₀ I V)
  (hN : L ^ m₀ ∣ N₁) (hρ : 0 < ρ) (hRσ : 0 ≤ Rσ) (hεU : 0 ≤ εU)
  {κ0 Kc : ℝ} (hκ0 : aEnt d L + 1 ≤ κ0) (hKc : K0 d L κ0 ≤ Kc)

include hF in
/-- **The formula for the family**: at `Θ ∈ V` and `‖u‖ < Rσ`, the activity of the label `Y` is
`T_Y` at the hat variable and the datum `Θ`. -/
theorem labelActFamily_H {Θ : Λ} (hΘ : Θ ∈ V) {u : ℂ} (hu : ‖u‖ < Rσ)
    (Y : {Y // Y ∈ I.𝒴}) (Φ : ∀ b, (S.blockSplit m₀ hp).Ωb b) :
    (labelActFamily S m₀ I hF hN hρ hRσ hεU hκ0 hKc Θ u).H Y Φ =
      I.T Y.1 (emb (S.hatOf m₀ ρ hp Φ)) (emb (S.hatOf m₀ ρ hp Φ)) u Θ := by
  simp [labelActFamily, hΘ, dtAct, dtH, hu, DirectTerms.atTheta]

include hF in
/-- At `Θ ∈ V` the family is the activity of `labelAct_of_directTerms` with `Θ₀ := Θ`
(definitionally the explicit activity `dtAct` of `I.atTheta`). -/
theorem labelActFamily_eq_dtAct {Θ : Λ} (hΘ : Θ ∈ V) (u : ℂ) :
    labelActFamily S m₀ I hF hN hρ hRσ hεU hκ0 hKc Θ u =
      dtAct S m₀ (I.atTheta S m₀ hF hΘ) hN hρ hRσ hεU hκ0 hKc u := by
  exact dite_eq_left_of_eq_true (eq_true hΘ)

/-- **Analyticity (`holA`)**: for every block configuration `Φ` and label `y`, the activity is
jointly analytic in `(Θ, u)` on `V ×ˢ ball 0 Rσ`. -/
theorem labelActFamily_analytic (y : {Y // Y ∈ I.𝒴}) (Φ : ∀ b, (S.blockSplit m₀ hp).Ωb b) :
    AnalyticOnNhd ℂ (fun p : Λ × ℂ =>
      (labelActFamily S m₀ I hF hN hρ hRσ hεU hκ0 hKc p.1 p.2).H y Φ) (V ×ˢ ball (0 : ℂ) Rσ) := by
  have han : AnalyticOnNhd ℂ (fun p : Λ × ℂ => I.T y.1 (emb (S.hatOf m₀ ρ hp Φ))
      (emb (S.hatOf m₀ ρ hp Φ)) p.2 p.1) (V ×ˢ ball (0 : ℂ) Rσ) :=
    (I.loc.analytic y.1 y.2 (emb (S.hatOf m₀ ρ hp Φ), emb (S.hatOf m₀ ρ hp Φ))
      (I.xw _ (S.hatOf_mem m₀ hρ hp Φ))).mono (Set.prod_mono hF.sub subset_rfl)
  refine han.congr (hF.isOpen.prod isOpen_ball) fun p hp' => ?_
  have hu : ‖p.2‖ < Rσ := by simpa using hp'.2
  exact (labelActFamily_H S m₀ hF hN hρ hRσ hεU hκ0 hKc hp'.1 hu y Φ).symm

/-- **Continuity in the configuration (`contA`)**: for `Θ ∈ V`, `u ∈ ball 0 Rσ`, the activity is
continuous in `Φ` on the whole configuration space, in particular on `physCarrier`. -/
theorem labelActFamily_continuous {Θ : Λ} (hΘ : Θ ∈ V) {u : ℂ} (hu : ‖u‖ < Rσ)
    (y : {Y // Y ∈ I.𝒴}) :
    Continuous ((labelActFamily S m₀ I hF hN hρ hRσ hεU hκ0 hKc Θ u).H y) := by
  have : (labelActFamily S m₀ I hF hN hρ hRσ hεU hκ0 hKc Θ u).H y =
      fun Φ => I.T y.1 (emb (S.hatOf m₀ ρ hp Φ)) (emb (S.hatOf m₀ ρ hp Φ)) u Θ :=
    funext fun Φ => labelActFamily_H S m₀ hF hN hρ hRσ hεU hκ0 hKc hΘ hu y Φ
  rw [this]
  exact continuous_term_hatOf S m₀ I hρ hF.cont y.2 hu hΘ

/-- **Locality in the datum.**  Let `Θ, Θ' ∈ V` and let `Z` be a set of sites such that the source
agreement `AgΘ Y Θ Θ'` holds for every domain `Y ∈ 𝒴` contained in `Z`.  Then the activities of
the labels inside `Z` coincide (for all `u`). -/
theorem labelActFamily_local {Θ Θ' : Λ} (hΘ : Θ ∈ V) (hΘ' : Θ' ∈ V)
    (Z : Set (CTorus d L N₁ m₁ (k + 1)))
    (hag : ∀ Y ∈ I.𝒴, Y ⊆ Z → AgΘ Y Θ Θ') (u : ℂ) (y : {Y // Y ∈ I.𝒴}) (hy : y.1 ⊆ Z) :
    (labelActFamily S m₀ I hF hN hρ hRσ hεU hκ0 hKc Θ u).H y =
      (labelActFamily S m₀ I hF hN hρ hRσ hεU hκ0 hKc Θ' u).H y := by
  funext Φ
  by_cases hu : ‖u‖ < Rσ
  · rw [labelActFamily_H S m₀ hF hN hρ hRσ hεU hκ0 hKc hΘ hu,
      labelActFamily_H S m₀ hF hN hρ hRσ hεU hκ0 hKc hΘ' hu]
    have hAg := I.ag y.1 y.2 Φ Φ (fun _ _ => rfl)
    exact I.loc.loc y.1 y.2 (emb (S.hatOf m₀ ρ hp Φ), emb (S.hatOf m₀ ρ hp Φ))
      (I.xw _ (S.hatOf_mem m₀ hρ hp Φ)) (emb (S.hatOf m₀ ρ hp Φ), emb (S.hatOf m₀ ρ hp Φ))
      (I.xw _ (S.hatOf_mem m₀ hρ hp Φ)) u hu Θ (hF.sub hΘ) Θ' (hF.sub hΘ')
      (hag y.1 y.2 hy) hAg hAg
  · simp [labelActFamily_eq_dtAct S m₀ hF hN hρ hRσ hεU hκ0 hKc hΘ,
      labelActFamily_eq_dtAct S m₀ hF hN hρ hRσ hεU hκ0 hKc hΘ', dtAct, dtH, hu]


/-- **The `ParamMarkFamily` with the physical activities and given marks.**  Let `G` be marks
satisfying the four mark fields of `ParamMarkFamily` (`meas`, `bound`, `holG`, `contG`; the last
two on `V ×ˢ ball 0 Rσ` and on `physCarrier`).  Then the physical activities `labelActFamily`
(joint analyticity, continuity on the carrier from `holA`, `contA` above), the carrier
`physCarrier`, `𝒰 = ball 0 Rσ` (with `1 < Rσ`, so that the segment `[0,1]` lies in `𝒰`) and the
open set `V` form a `ParamMarkFamily`. -/
theorem paramMarkFamily_of_marks (hRσ1 : 1 < Rσ) {ι : Type*}
    (y0 : ι → {Y // Y ∈ I.𝒴}) (G : Λ → ι → ℂ → (∀ b, (S.blockSplit m₀ hp).Ωb b) → ℂ)
    (κG : ℝ) (F0 : ι → ℝ)
    (hGmeas : ∀ θ i u, Measurable (G θ i u))
    (hGbound : ∀ θ i u Φ, ‖G θ i u Φ‖ ≤ F0 i * Real.exp (-κG * (thickLabels I.𝒴 I.dom).dl (y0 i)))
    (hGhol : ∀ i, ∀ Φ ∈ physCarrier S m₀ hp,
      AnalyticOnNhd ℂ (fun p : Λ × ℂ => G p.1 i p.2 Φ) (V ×ˢ ball (0 : ℂ) Rσ))
    (hGcont : ∀ i, ∀ θ ∈ V, ∀ u ∈ ball (0 : ℂ) Rσ, ContinuousOn (G θ i u) (physCarrier S m₀ hp)) :
    ParamMarkFamily (S.blockSplit m₀ hp).μ (thickLabels I.𝒴 I.dom)
      (labelActFamily S m₀ I hF hN hρ hRσ hεU hκ0 hKc) y0 G κG F0 V (ball (0 : ℂ) Rσ)
      (physCarrier S m₀ hp) where
  isOpenV := hF.isOpen
  isOpenU := isOpen_ball
  seg := fun s hs => by
    rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_of_nonneg hs.1]
    exact lt_of_le_of_lt hs.2 hRσ1
  compact := isCompact_physCarrier S m₀ hp
  measQ := measurableSet_physCarrier S m₀ hp
  carried := ae_mem_physCarrier S m₀ hp
  meas := hGmeas
  bound := hGbound
  holA := fun y Φ _ => labelActFamily_analytic S m₀ hF hN hρ hRσ hεU hκ0 hKc y Φ
  holG := hGhol
  contA := fun y θ hθ u hu =>
    (labelActFamily_continuous S m₀ hF hN hρ hRσ hεU hκ0 hKc hθ (by simpa using hu) y).continuousOn
  contG := hGcont

/-- **The `ParamMarkFamily` with zero marks**: the activity fields are tested on their own. -/
theorem paramMarkFamily_zero_marks (hRσ1 : 1 < Rσ) {ι : Type*}
    (y0 : ι → {Y // Y ∈ I.𝒴}) (κG : ℝ) (F0 : ι → ℝ) (hF0 : ∀ i, 0 ≤ F0 i) :
    ParamMarkFamily (S.blockSplit m₀ hp).μ (thickLabels I.𝒴 I.dom)
      (labelActFamily S m₀ I hF hN hρ hRσ hεU hκ0 hKc) y0
      (fun _ _ _ _ => (0 : ℂ)) κG F0 V (ball (0 : ℂ) Rσ) (physCarrier S m₀ hp) :=
  paramMarkFamily_of_marks S m₀ hF hN hρ hRσ hεU hκ0 hKc hRσ1 y0 _ κG F0
    (fun _ _ _ => measurable_const)
    (fun _ i _ _ => by simp only [norm_zero]; exact mul_nonneg (hF0 i) (Real.exp_pos _).le)
    (fun _ _ _ => analyticOnNhd_const) (fun _ _ _ _ _ => continuousOn_const)

end Activity

section Physical

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}
  (S : StepSetting d L N₁ m₁ k N ϱ) (m₀ : ℕ) {F' : Type}
  {hp : 0 < S.p₁} {emb : (S.U × Fin N → ℂ) → F'} {ρ Rσ εU a a₁ ν eps : ℝ}
  {Θ₀ : RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ)}
  {XW : Set (F' × F')} {val : F' → F' → ℂ →
    RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) → ℂ}
  {AgF : Set (CTorus d L N₁ m₁ (k + 1)) → F' → F' → Prop}

/-- The restriction of the datum `Θ = (Ψ, h)` to a set `R` of sites (both components of `Ψ` and
`h`). -/
def physRestrict (R : Set (CTorus d L N₁ m₁ (k + 1)))
    (Θ : RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ)) :
    R → (Fin N → ℂ) × (Fin N → ℂ) × (Fin N → ℂ) :=
  fun x => (Θ.1.1 x.1, Θ.1.2 x.1, Θ.2 x.1)

/-- The sites on which the activities of the labels inside `Z` depend: the union of the
thickenings of the domains of `𝒴` contained in `Z`. -/
def physRegion (𝒴 : Finset (Set (CTorus d L N₁ m₁ (k + 1))))
    (Z : Set (CTorus d L N₁ m₁ (k + 1))) : Set (CTorus d L N₁ m₁ (k + 1)) :=
  {x | ∃ Y ∈ 𝒴, Y ⊆ Z ∧ x ∈ thickSet S.G' Y}

omit [NeZero L] [NeZero N₁] in
/-- Equal restrictions to a set `R` give equality of the three components of the datum at every
site of `R`. -/
theorem physRestrict_eq_apply {R : Set (CTorus d L N₁ m₁ (k + 1))}
    {Θ Θ' : RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ)}
    (h : physRestrict (N := N) R Θ = physRestrict R Θ') :
    ∀ x ∈ R, Θ.1.1 x = Θ'.1.1 x ∧ Θ.1.2 x = Θ'.1.2 x ∧ Θ.2 x = Θ'.2 x := by
  intro x hx
  have := congrFun h ⟨x, hx⟩
  simpa [physRestrict, Prod.ext_iff] using this

/-- Equal restrictions to a set containing `Y` give the source agreement `physAgΘ` (the raw datum
and the source agree on `Y` itself). -/
theorem physAgΘ_of_restrict_rawY {Y R : Set (CTorus d L N₁ m₁ (k + 1))} (hR : Y ⊆ R)
    {Θ Θ' : RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ)}
    (h : physRestrict (N := N) R Θ = physRestrict R Θ') : physAgΘ S Y Θ Θ' :=
  ⟨fun x hx => ⟨(physRestrict_eq_apply h x (hR hx)).1, (physRestrict_eq_apply h x (hR hx)).2.1⟩,
    fun x hx => (physRestrict_eq_apply h x (hR hx)).2.2⟩

/-- Equal restrictions to a set containing the thickening of `Y` give the thick agreement
`physAgΘThick` (raw datum on `thickSet Y`, source on `Y`). -/
theorem physAgΘThick_of_restrict {Y R : Set (CTorus d L N₁ m₁ (k + 1))}
    (hR : thickSet S.G' Y ⊆ R)
    {Θ Θ' : RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ)}
    (h : physRestrict (N := N) R Θ = physRestrict R Θ') : physAgΘThick S Y Θ Θ' :=
  ⟨(physAgΘ_of_restrict_rawY S hR h).1,
    fun x hx => (physAgΘ_of_restrict_rawY S hR h).2 x (Or.inl hx)⟩

/-- Equal restrictions to a set containing the thickening of `Y` give the source agreement
`physAgΘ` (a fortiori: `Y ⊆ thickSet Y`). -/
theorem physAgΘ_of_restrict {Y R : Set (CTorus d L N₁ m₁ (k + 1))}
    (hR : thickSet S.G' Y ⊆ R)
    {Θ Θ' : RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ)}
    (h : physRestrict (N := N) R Θ = physRestrict R Θ') : physAgΘ S Y Θ Θ' :=
  physAgΘ_of_restrict_rawY S (fun _ hx => hR (Or.inl hx)) h

/-- **Locality of the physical activities in the datum, exact form.**  Let `Z = Ŷ(sitesOf T)` and
let `R` be a set of sites containing every domain of the family that lies in `Z` (for instance
`R = Z`).  If `Θ, Θ' ∈ V` have the same restriction to `R`, then the activities at the labels inside
`Z` coincide, for every `u`: the activity of a label reads the datum only on its own domain. -/
theorem physical_labelActFamily_local_rawY
    {I : DirectTerms S m₀ hp emb ρ Rσ εU a Θ₀ (physSΛ S a₁ ν eps) XW val (physAgΘ S) AgF}
    {V : Set (RawData d L (N₁ * L ^ m₁) (k + 1) N ×
      (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ))}
    (hF : DirectTermsFamily S m₀ I V)
    (hN : L ^ m₀ ∣ N₁) (hρ : 0 < ρ) (hRσ : 0 ≤ Rσ) (hεU : 0 ≤ εU)
    {κ0 Kc : ℝ} (hκ0 : aEnt d L + 1 ≤ κ0) (hKc : K0 d L κ0 ≤ Kc)
    (T : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) m₀ (k + 1)
      Set.univ)) {R : Set (CTorus d L N₁ m₁ (k + 1))}
    (hR : ∀ Y ∈ I.𝒴, Y ⊆ Yhat Set.univ (sitesOf T) → Y ⊆ R) :
    ∀ Θ ∈ V, ∀ Θ' ∈ V, physRestrict (N := N) R Θ = physRestrict R Θ' →
      ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ y,
        (thickLabels I.𝒴 I.dom).ysite y ⊆ Yhat Set.univ (sitesOf T) →
        (labelActFamily S m₀ I hF hN hρ hRσ hεU hκ0 hKc Θ (s : ℂ)).H y =
          (labelActFamily S m₀ I hF hN hρ hRσ hεU hκ0 hKc Θ' (s : ℂ)).H y := by
  intro Θ hΘ Θ' hΘ' h _ _ y hy
  refine labelActFamily_local S m₀ hF hN hρ hRσ hεU hκ0 hKc hΘ hΘ' _ ?_ _ y hy
  intro Y hY hYZ
  exact physAgΘ_of_restrict_rawY S (hR Y hY hYZ) h

/-- **Locality of the physical activities in the datum** (the premise `hA` of
`gsumCoeff_param_congr_of_local` for the physical activities).  If `Θ, Θ' ∈ V` have the same
restriction to the region `physRegion` of `Z = Ŷ(sitesOf T)` (the thickenings of the domains inside
`Z`), then the activities at the labels inside `Z` coincide, for every `u`.  (The thick region
contains the domains themselves: this is `physical_labelActFamily_local_rawY` at
`R = physRegion`.) -/
theorem physical_labelActFamily_local
    {I : DirectTerms S m₀ hp emb ρ Rσ εU a Θ₀ (physSΛ S a₁ ν eps) XW val (physAgΘ S) AgF}
    {V : Set (RawData d L (N₁ * L ^ m₁) (k + 1) N ×
      (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ))}
    (hF : DirectTermsFamily S m₀ I V)
    (hN : L ^ m₀ ∣ N₁) (hρ : 0 < ρ) (hRσ : 0 ≤ Rσ) (hεU : 0 ≤ εU)
    {κ0 Kc : ℝ} (hκ0 : aEnt d L + 1 ≤ κ0) (hKc : K0 d L κ0 ≤ Kc)
    (T : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) m₀ (k + 1)
      Set.univ)) :
    ∀ Θ ∈ V, ∀ Θ' ∈ V,
      physRestrict (N := N) (physRegion S I.𝒴 (Yhat Set.univ (sitesOf T))) Θ =
        physRestrict (physRegion S I.𝒴 (Yhat Set.univ (sitesOf T))) Θ' →
      ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ y,
        (thickLabels I.𝒴 I.dom).ysite y ⊆ Yhat Set.univ (sitesOf T) →
        (labelActFamily S m₀ I hF hN hρ hRσ hεU hκ0 hKc Θ (s : ℂ)).H y =
          (labelActFamily S m₀ I hF hN hρ hRσ hεU hκ0 hKc Θ' (s : ℂ)).H y :=
  physical_labelActFamily_local_rawY S m₀ hF hN hρ hRσ hεU hκ0 hKc T
    (fun Y hY hYZ _ hx => ⟨Y, hY, hYZ, Or.inl hx⟩)

/-- The source agreement `physAgΘ` is reflexive. -/
theorem physAgΘ_refl (Y : Set (CTorus d L N₁ m₁ (k + 1)))
    (Θ : RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ)) :
    physAgΘ S Y Θ Θ := ⟨fun _ _ => ⟨rfl, rfl⟩, fun _ _ => rfl⟩

/-- **The family hypothesis for the physical expansion**: for every open `V ⊆ physSΛ`, the base
`DirectTerms` `I` (for instance the output of `physical_directTerms`) together with the field
`cont` of the physical expansion (`PhysExpansion`, a `LocIntDm`) gives a `DirectTermsFamily`. -/
theorem physical_directTermsFamily
    {I : DirectTerms S m₀ hp emb ρ Rσ εU a Θ₀ (physSΛ S a₁ ν eps) XW val (physAgΘ S) AgF}
    (hcont : DiagCont emb XW (physSΛ S a₁ ν eps) Rσ I.𝒴 I.T)
    {V : Set (RawData d L (N₁ * L ^ m₁) (k + 1) N ×
      (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ))}
    (hV : IsOpen V) (hsub : V ⊆ physSΛ S a₁ ν eps) : DirectTermsFamily S m₀ I V where
  isOpen := hV
  sub := hsub
  agΘ := fun Θ _ Y => physAgΘ_refl S Y Θ
  cont := fun Y hY σ hσ Θ hΘ => hcont Y hY σ hσ Θ (hsub hΘ)

end Physical

section Inhabited

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}
  (S : StepSetting d L N₁ m₁ k N ϱ) (m₀ : ℕ)

/-- **`DirectTermsFamily` is inhabited**, with a nonempty open parameter set and a nonempty family
of domains: the whole-torus label with zero terms (the instance of `nonempty_directTerms`), on
`Λ = ℂ`, `SΛ = V = univ`. -/
theorem nonempty_directTermsFamily (hp : 0 < S.p₁) (ρ Rσ εU a : ℝ) (hεU : 0 ≤ εU) :
    ∃ (I : DirectTerms S m₀ hp (F' := Unit) (fun _ => ()) ρ Rσ εU a (0 : ℂ) Set.univ Set.univ
      (fun _ _ _ _ => (0 : ℂ)) (fun _ _ _ => True) (fun _ _ _ => True))
      (_ : DirectTermsFamily S m₀ I Set.univ), I.𝒴.Nonempty ∧ (Set.univ : Set ℂ).Nonempty := by
  have hY : IsDj m₀ (k + 1) (Set.univ : Set (CTorus d L N₁ m₁ (k + 1))) :=
    isDj_univ d L N₁ m₁ (k + 1) m₀ (k + 1)
  let I : DirectTerms S m₀ hp (F' := Unit) (fun _ => ()) ρ Rσ εU a (0 : ℂ) Set.univ Set.univ
      (fun _ _ _ _ => (0 : ℂ)) (fun _ _ _ => True) (fun _ _ _ => True) :=
    { 𝒴 := {Set.univ}
      T := fun _ _ _ _ _ => 0
      b := fun _ => 0
      loc := ⟨by simp, fun Y _ _ _ => analyticOnNhd_const, by simp,
        fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => rfl, fun _ _ _ _ _ _ => rfl⟩
      dom := fun Y hy => by rw [Finset.mem_singleton.1 hy]; exact hY
      bd := fun _ _ => by positivity
      mem := Set.mem_univ _
      agΘ := fun _ => trivial
      xw := fun _ _ => Set.mem_univ _
      ag := fun _ _ _ _ _ => trivial
      meas := fun _ _ _ _ => measurable_const }
  exact ⟨I, ⟨isOpen_univ, Set.subset_univ _, fun _ _ _ => trivial,
    fun _ _ _ _ _ _ => continuousOn_const⟩, ⟨Set.univ, Finset.mem_singleton_self _⟩, ⟨0, trivial⟩⟩

/-- **The assembled `ParamMarkFamily` is inhabited** on the actual block spaces and measures of the
step: for the whole-torus family of `nonempty_directTermsFamily` (`ρ = 1`, `Rσ = 2`), with no marks
(`ι` empty), the activities of `labelActFamily` satisfy every activity field. -/
theorem nonempty_paramMarkFamily_activityPhysical (hN : L ^ m₀ ∣ N₁) (hp : 0 < S.p₁) (a : ℝ) :
    ∃ (I : DirectTerms S m₀ hp (F' := Unit) (fun _ => ()) 1 2 0 a (0 : ℂ) Set.univ Set.univ
      (fun _ _ _ _ => (0 : ℂ)) (fun _ _ _ => True) (fun _ _ _ => True))
      (hF : DirectTermsFamily S m₀ I Set.univ),
      Nonempty (ParamMarkFamily (S.blockSplit m₀ hp).μ (thickLabels I.𝒴 I.dom)
        (labelActFamily S m₀ I hF hN one_pos (by norm_num) le_rfl
          (le_refl (aEnt d L + 1)) (le_refl (K0 d L (aEnt d L + 1))))
        (fun e : Empty => e.elim) (fun _ _ _ _ => (0 : ℂ)) 0 (fun e : Empty => e.elim) Set.univ
        (ball (0 : ℂ) 2) (physCarrier S m₀ hp)) := by
  obtain ⟨I, hF, -⟩ := nonempty_directTermsFamily S m₀ hp 1 2 0 a le_rfl
  exact ⟨I, hF, ⟨paramMarkFamily_zero_marks S m₀ hF hN one_pos (by norm_num) le_rfl
    (le_refl (aEnt d L + 1)) (le_refl (K0 d L (aEnt d L + 1))) (by norm_num) _ 0
    (fun e : Empty => e.elim) (fun e : Empty => e.elim)⟩⟩

end Inhabited

end Balaban.Fluctuation
