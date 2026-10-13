/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.XiCRawOpen
public import Balaban.Fluctuation.ParamActivityPhysical
public import Balaban.Fluctuation.SharpAssembly
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Physical label activities over the subspace of data

**The earlier open-set statements are vacuous for the physical chart.**  The chart `XiCRaw` has
empty interior in `RawData` (`Balaban/Localization/XiCRawOpen.lean`): it is open only relative to
the linear subspace `rawSub` of data that are constant on layer blocks and vanish off the data
sites.  Hence every open `V ⊆ physSΛ` is empty, and `DirectTermsFamily` (whose field `isOpen` asks
openness in the ambient space) and `physical_directTermsFamily` have no non-empty instance over the
physical parameter set.  **This file is the form to use**: the datum is parametrized by the
subspace.

* `DirectTermsFamilyOn J I V`: the relative family hypothesis for a continuous linear map
  `J : E → Λ`: the open set `V` lies in the finite-dimensional parameter space `E`, and `J` maps
  it into `SΛ`.
* `labelActFamilyOn`: the activity at the parameter `e ∈ V` is the landed activity
  (`dtAct` of `labelAct_of_directTerms`) at the datum `J e`.  Joint analyticity in `(e, u)`
  (`labelActFamilyOn_analytic`, from analyticity of the terms at the points of `SΛ` composed with
  the linear map), continuity, locality, and the `ParamMarkFamily` over `E`
  (`paramMarkFamilyOn_of_marks`).
* `physParam`, `physIncl`, `physV`: the parameter space `rawSub × sources`, its inclusion in the
  ambient space, and the open set `physIncl ⁻¹' physSΛ`, with `physIncl '' physV = physSΛ`.
* `paramMarkFamily_physical_subspace`, `physical_labelActFamilyOn_local`,
  `physical_paramMarked_analytic_local_bound`: the physical family, its locality in the restriction
  of the datum, and analyticity, locality and the uniform bound of the marked coefficient on `physV`.

* `physical_paramMarkFamily_exists` (hypotheses of `physical_directTerms`): the relative family
  over `physV`, the datum `Θ₀` of the chart as the image of a point of `physV`, and the
  `ParamMarkFamily`.  Its instance at the hat step is
  `Balaban/Inhabited/ParamActivitySubspaceWitness.lean`.

Marks and the determinant term are not constructed: the marks are data satisfying their own fields
over `physV`, or zero.
-/

@[expose] public section

namespace Balaban.Fluctuation

open MeasureTheory Balaban Balaban.Localization Balaban.Multiscale Balaban.Polymer
  Balaban.Background Metric

section Family

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}
  (S : StepSetting d L N₁ m₁ k N ϱ) (m₀ : ℕ) {Λ F' E : Type}
  [NormedAddCommGroup Λ] [NormedSpace ℂ Λ] [NormedAddCommGroup E] [NormedSpace ℂ E]
  {hp : 0 < S.p₁} {emb : (S.U × Fin N → ℂ) → F'} {ρ Rσ εU a : ℝ} {Θ₀ : Λ}
  {SΛ : Set Λ} {XW : Set (F' × F')} {val : F' → F' → ℂ → Λ → ℂ}
  {AgΘ : Set (CTorus d L N₁ m₁ (k + 1)) → Λ → Λ → Prop}
  {AgF : Set (CTorus d L N₁ m₁ (k + 1)) → F' → F' → Prop}
  (J : E →L[ℂ] Λ)

/-- **The relative family hypothesis.**  `V` is open in the parameter space `E`, the linear map
`J : E → Λ` sends it into the admissible set `SΛ`, the source agreement is reflexive at the data
`J e`, and the diagonal terms are continuous on the admissible set for every datum `J e`, `e ∈ V`.
The domains, terms, bound and locality are those of the base `DirectTerms` `I`. -/
structure DirectTermsFamilyOn
    (I : DirectTerms S m₀ hp emb ρ Rσ εU a Θ₀ SΛ XW val AgΘ AgF) (V : Set E) : Prop where
  isOpen : IsOpen V
  sub : J '' V ⊆ SΛ
  agΘ : ∀ e ∈ V, ∀ Y, AgΘ Y (J e) (J e)
  cont : DiagCont emb XW (J '' V) Rσ I.𝒴 I.T

/-- **`DirectTerms` at the datum `J e`, `e ∈ V`**: the same domains, terms, bound, locality and
constants as the base. -/
noncomputable def DirectTerms.atThetaOn
    (I : DirectTerms S m₀ hp emb ρ Rσ εU a Θ₀ SΛ XW val AgΘ AgF) {V : Set E}
    (hF : DirectTermsFamilyOn S m₀ J I V) {e : E} (he : e ∈ V) :
    DirectTerms S m₀ hp emb ρ Rσ εU a (J e) SΛ XW val AgΘ AgF :=
  { I with
    mem := hF.sub ⟨e, he, rfl⟩
    agΘ := hF.agΘ e he
    meas := fun Y hY σ hσ => by
      have hc := hF.cont Y hY σ hσ (J e) ⟨e, he, rfl⟩
      refine (continuousOn_iff_continuous_domRestrict.1 (hc.mono ?_)).measurable
      intro ψ hψ
      exact I.xw ψ hψ }

open Classical in
/-- **The family of label activities over the parameter space.**  For `e ∈ V` the activity is
`dtAct` of `I.atThetaOn e`, that is the activity of `labelAct_of_directTerms` at the datum
`J e`; for `e ∉ V` (not used) it is the base activity. -/
noncomputable def labelActFamilyOn
    (I : DirectTerms S m₀ hp emb ρ Rσ εU a Θ₀ SΛ XW val AgΘ AgF)
    {V : Set E} (hF : DirectTermsFamilyOn S m₀ J I V)
    (hN : L ^ m₀ ∣ N₁) (hρ : 0 < ρ) (hRσ : 0 ≤ Rσ) (hεU : 0 ≤ εU)
    {κ0 Kc : ℝ} (hκ0 : aEnt d L + 1 ≤ κ0) (hKc : K0 d L κ0 ≤ Kc) (e : E) (u : ℂ) :
    LabelAct (thickLabels I.𝒴 I.dom) (S.blockSplit m₀ hp).Ωb (Rσ * εU) a κ0 Kc :=
  if h : e ∈ V then dtAct S m₀ (I.atThetaOn S m₀ J hF h) hN hρ hRσ hεU hκ0 hKc u
  else dtAct S m₀ I hN hρ hRσ hεU hκ0 hKc u

variable {I : DirectTerms S m₀ hp emb ρ Rσ εU a Θ₀ SΛ XW val AgΘ AgF} {V : Set E}
  (hF : DirectTermsFamilyOn S m₀ J I V)
  (hN : L ^ m₀ ∣ N₁) (hρ : 0 < ρ) (hRσ : 0 ≤ Rσ) (hεU : 0 ≤ εU)
  {κ0 Kc : ℝ} (hκ0 : aEnt d L + 1 ≤ κ0) (hKc : K0 d L κ0 ≤ Kc)

include hF in
/-- **The formula for the family**: at `e ∈ V` and `‖u‖ < Rσ`, the activity of the label `Y` is
`T_Y` at the hat variable and the datum `J e`. -/
theorem labelActFamilyOn_H {e : E} (he : e ∈ V) {u : ℂ} (hu : ‖u‖ < Rσ)
    (Y : {Y // Y ∈ I.𝒴}) (Φ : ∀ b, (S.blockSplit m₀ hp).Ωb b) :
    (labelActFamilyOn S m₀ J I hF hN hρ hRσ hεU hκ0 hKc e u).H Y Φ =
      I.T Y.1 (emb (S.hatOf m₀ ρ hp Φ)) (emb (S.hatOf m₀ ρ hp Φ)) u (J e) := by
  simp [labelActFamilyOn, he, dtAct, dtH, hu, DirectTerms.atThetaOn]

include hF in
/-- At `e ∈ V` the family is the landed activity `dtAct` at the datum `J e`. -/
theorem labelActFamilyOn_eq_dtAct {e : E} (he : e ∈ V) (u : ℂ) :
    labelActFamilyOn S m₀ J I hF hN hρ hRσ hεU hκ0 hKc e u =
      dtAct S m₀ (I.atThetaOn S m₀ J hF he) hN hρ hRσ hεU hκ0 hKc u :=
  dite_eq_left_of_eq_true (eq_true he)

/-- **Analyticity**: for every configuration `Φ` and label `y`, the activity is jointly analytic
in `(e, u)` on `V ×ˢ ball 0 Rσ`: the terms are analytic at the points of `SΛ`, and `J` is
continuous linear. -/
theorem labelActFamilyOn_analytic (y : {Y // Y ∈ I.𝒴})
    (Φ : ∀ b, (S.blockSplit m₀ hp).Ωb b) :
    AnalyticOnNhd ℂ (fun p : E × ℂ =>
      (labelActFamilyOn S m₀ J I hF hN hρ hRσ hεU hκ0 hKc p.1 p.2).H y Φ)
      (V ×ˢ ball (0 : ℂ) Rσ) := by
  have han : AnalyticOnNhd ℂ (fun p : Λ × ℂ => I.T y.1 (emb (S.hatOf m₀ ρ hp Φ))
      (emb (S.hatOf m₀ ρ hp Φ)) p.2 p.1) (SΛ ×ˢ ball (0 : ℂ) Rσ) :=
    I.loc.analytic y.1 y.2 (emb (S.hatOf m₀ ρ hp Φ), emb (S.hatOf m₀ ρ hp Φ))
      (I.xw _ (S.hatOf_mem m₀ hρ hp Φ))
  have hc : AnalyticOnNhd ℂ (fun p : E × ℂ => ((J p.1, p.2) : Λ × ℂ)) Set.univ :=
    (J.prodMap (ContinuousLinearMap.id ℂ ℂ)).analyticOnNhd _
  have hcomp := han.comp (hc.mono (Set.subset_univ (V ×ˢ ball (0 : ℂ) Rσ)))
    (fun p hp' => ⟨hF.sub ⟨p.1, hp'.1, rfl⟩, hp'.2⟩)
  refine hcomp.congr (hF.isOpen.prod isOpen_ball) fun p hp' => ?_
  have hu : ‖p.2‖ < Rσ := by simpa using hp'.2
  exact (labelActFamilyOn_H S m₀ J hF hN hρ hRσ hεU hκ0 hKc hp'.1 hu y Φ).symm

/-- **Continuity in the configuration**: for `e ∈ V`, `u ∈ ball 0 Rσ`, the activity is continuous in
`Φ` on the whole configuration space, in particular on `physCarrier`. -/
theorem labelActFamilyOn_continuous {e : E} (he : e ∈ V) {u : ℂ} (hu : ‖u‖ < Rσ)
    (y : {Y // Y ∈ I.𝒴}) :
    Continuous ((labelActFamilyOn S m₀ J I hF hN hρ hRσ hεU hκ0 hKc e u).H y) := by
  have : (labelActFamilyOn S m₀ J I hF hN hρ hRσ hεU hκ0 hKc e u).H y =
      fun Φ => I.T y.1 (emb (S.hatOf m₀ ρ hp Φ)) (emb (S.hatOf m₀ ρ hp Φ)) u (J e) :=
    funext fun Φ => labelActFamilyOn_H S m₀ J hF hN hρ hRσ hεU hκ0 hKc he hu y Φ
  rw [this]
  exact continuous_term_hatOf S m₀ I hρ hF.cont y.2 hu ⟨e, he, rfl⟩

/-- **Locality in the parameter.**  Let `e, e' ∈ V` and let `Z` be a set of sites such that the
source agreement `AgΘ Y (J e) (J e')` holds for every domain `Y ∈ 𝒴` contained in `Z`.  Then the
activities of the labels inside `Z` coincide (for all `u`). -/
theorem labelActFamilyOn_local {e e' : E} (he : e ∈ V) (he' : e' ∈ V)
    (Z : Set (CTorus d L N₁ m₁ (k + 1)))
    (hag : ∀ Y ∈ I.𝒴, Y ⊆ Z → AgΘ Y (J e) (J e')) (u : ℂ) (y : {Y // Y ∈ I.𝒴})
    (hy : y.1 ⊆ Z) :
    (labelActFamilyOn S m₀ J I hF hN hρ hRσ hεU hκ0 hKc e u).H y =
      (labelActFamilyOn S m₀ J I hF hN hρ hRσ hεU hκ0 hKc e' u).H y := by
  funext Φ
  by_cases hu : ‖u‖ < Rσ
  · rw [labelActFamilyOn_H S m₀ J hF hN hρ hRσ hεU hκ0 hKc he hu,
      labelActFamilyOn_H S m₀ J hF hN hρ hRσ hεU hκ0 hKc he' hu]
    have hAg := I.ag y.1 y.2 Φ Φ (fun _ _ => rfl)
    exact I.loc.loc y.1 y.2 (emb (S.hatOf m₀ ρ hp Φ), emb (S.hatOf m₀ ρ hp Φ))
      (I.xw _ (S.hatOf_mem m₀ hρ hp Φ)) (emb (S.hatOf m₀ ρ hp Φ), emb (S.hatOf m₀ ρ hp Φ))
      (I.xw _ (S.hatOf_mem m₀ hρ hp Φ)) u hu (J e) (hF.sub ⟨e, he, rfl⟩) (J e')
      (hF.sub ⟨e', he', rfl⟩) (hag y.1 y.2 hy) hAg hAg
  · simp [labelActFamilyOn_eq_dtAct S m₀ J hF hN hρ hRσ hεU hκ0 hKc he,
      labelActFamilyOn_eq_dtAct S m₀ J hF hN hρ hRσ hεU hκ0 hKc he', dtAct, dtH, hu]

/-- **The `ParamMarkFamily` over the parameter space `E`, with the physical-type activities and
given marks.**  The marks `G` satisfy the four mark fields of `ParamMarkFamily` over `V`.  The
activities `labelActFamilyOn`, the carrier `physCarrier`, `𝒰 = ball 0 Rσ` (with `1 < Rσ`) and the
open set `V ⊆ E` form a `ParamMarkFamily`. -/
theorem paramMarkFamilyOn_of_marks (hRσ1 : 1 < Rσ) {ι : Type*}
    (y0 : ι → {Y // Y ∈ I.𝒴}) (G : E → ι → ℂ → (∀ b, (S.blockSplit m₀ hp).Ωb b) → ℂ)
    (κG : ℝ) (F0 : ι → ℝ)
    (hGmeas : ∀ θ i u, Measurable (G θ i u))
    (hGbound : ∀ θ i u Φ, ‖G θ i u Φ‖ ≤ F0 i * Real.exp (-κG * (thickLabels I.𝒴 I.dom).dl (y0 i)))
    (hGhol : ∀ i, ∀ Φ ∈ physCarrier S m₀ hp,
      AnalyticOnNhd ℂ (fun p : E × ℂ => G p.1 i p.2 Φ) (V ×ˢ ball (0 : ℂ) Rσ))
    (hGcont : ∀ i, ∀ θ ∈ V, ∀ u ∈ ball (0 : ℂ) Rσ, ContinuousOn (G θ i u) (physCarrier S m₀ hp)) :
    ParamMarkFamily (S.blockSplit m₀ hp).μ (thickLabels I.𝒴 I.dom)
      (labelActFamilyOn S m₀ J I hF hN hρ hRσ hεU hκ0 hKc) y0 G κG F0 V (ball (0 : ℂ) Rσ)
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
  holA := fun y Φ _ => labelActFamilyOn_analytic S m₀ J hF hN hρ hRσ hεU hκ0 hKc y Φ
  holG := hGhol
  contA := fun y θ hθ u hu =>
    (labelActFamilyOn_continuous S m₀ J hF hN hρ hRσ hεU hκ0 hKc hθ (by simpa using hu)
      y).continuousOn
  contG := hGcont

/-- **The `ParamMarkFamily` over `E` with zero marks.** -/
theorem paramMarkFamilyOn_zero_marks (hRσ1 : 1 < Rσ) {ι : Type*}
    (y0 : ι → {Y // Y ∈ I.𝒴}) (κG : ℝ) (F0 : ι → ℝ) (hF0 : ∀ i, 0 ≤ F0 i) :
    ParamMarkFamily (S.blockSplit m₀ hp).μ (thickLabels I.𝒴 I.dom)
      (labelActFamilyOn S m₀ J I hF hN hρ hRσ hεU hκ0 hKc) y0
      (fun _ _ _ _ => (0 : ℂ)) κG F0 V (ball (0 : ℂ) Rσ) (physCarrier S m₀ hp) :=
  paramMarkFamilyOn_of_marks S m₀ J hF hN hρ hRσ hεU hκ0 hKc hRσ1 y0 _ κG F0
    (fun _ _ _ => measurable_const)
    (fun _ i _ _ => by simp only [norm_zero]; exact mul_nonneg (hF0 i) (Real.exp_pos _).le)
    (fun _ _ _ => analyticOnNhd_const) (fun _ _ _ _ _ => continuousOn_const)

end Family

section Physical

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}
  (S : StepSetting d L N₁ m₁ k N ϱ) (m₀ : ℕ) {F' : Type}
  {hp : 0 < S.p₁} {emb : (S.U × Fin N → ℂ) → F'} {ρ Rσ εU a a₁ ν eps : ℝ}
  {Θ₀ : RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ)}
  {XW : Set (F' × F')} {val : F' → F' → ℂ →
    RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) → ℂ}
  {AgF : Set (CTorus d L N₁ m₁ (k + 1)) → F' → F' → Prop}

variable (N) in
/-- **The parameter space of the physical datum**: the subspace `rawSub` of raw data of data
(constant on layer blocks, zero off the data sites), times the space of sources. -/
abbrev physParam (S : StepSetting d L N₁ m₁ k N ϱ) : Type :=
  ↥(rawSub N S.G') × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ)

variable (N) in
/-- The inclusion of the parameter space in the ambient space `RawData × sources`
(continuous linear; the identity on the source factor). -/
noncomputable def physIncl (S : StepSetting d L N₁ m₁ k N ϱ) :
    physParam N S →L[ℂ] RawData d L (N₁ * L ^ m₁) (k + 1) N ×
      (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) :=
  (rawSub N S.G').subtypeL.prodMap (ContinuousLinearMap.id ℂ _)

theorem physIncl_apply (e : physParam N S) : physIncl N S e = ((e.1 : RawData d L (N₁ * L ^ m₁)
    (k + 1) N), e.2) := rfl

/-- **The admissible parameters**: the preimage of the physical parameter set `physSΛ` under the
inclusion. -/
def physV (a₁ ν eps : ℝ) : Set (physParam N S) := physIncl N S ⁻¹' physSΛ S a₁ ν eps

/-- **`physV` is open** in the parameter space (the chart is open relative to the subspace of
data, and the `ℓ¹` ball of sources is open). -/
theorem isOpen_physV (a₁ ν eps : ℝ) (H : BgHyp d L (k + 1) ϱ (compWeight L a₁) ν) :
    IsOpen (physV S a₁ ν eps) :=
  (isOpen_preimage_xiCRaw (G := S.G') (N := N) (n := k + 1) (σ := 1) (ε := eps) H).prod
    (isOpen_l1Ball (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) (N := N))

/-- Every point of `physSΛ` is the image of a point of `physV`, and the image of `physV` lies in
`physSΛ`: `physIncl '' physV = physSΛ`. -/
theorem physIncl_image_physV (a₁ ν eps : ℝ) :
    physIncl N S '' physV S a₁ ν eps = physSΛ S a₁ ν eps := by
  refine Set.Subset.antisymm ?_ ?_
  · rintro _ ⟨e, he, rfl⟩
    exact he
  · rintro ⟨p, g⟩ hΘ
    have hp : p ∈ rawSub N S.G' := XiCRaw_subset_rawSub _ _ _ _ _ _ hΘ.1
    exact ⟨(⟨p, hp⟩, g), hΘ, rfl⟩

/-- **The physical relative family.**  From the base `DirectTerms` over `physSΛ` and the
continuity field of the physical expansion, the relative family over `physV` with `J = physIncl`. -/
theorem physical_directTermsFamilyOn
    {I : DirectTerms S m₀ hp emb ρ Rσ εU a Θ₀ (physSΛ S a₁ ν eps) XW val (physAgΘ S) AgF}
    (hcont : DiagCont emb XW (physSΛ S a₁ ν eps) Rσ I.𝒴 I.T)
    (H : BgHyp d L (k + 1) ϱ (compWeight L a₁) ν) :
    DirectTermsFamilyOn S m₀ (physIncl N S) I (physV S a₁ ν eps) where
  isOpen := isOpen_physV S a₁ ν eps H
  sub := by
    rw [physIncl_image_physV]
  agΘ := fun e _ Y => physAgΘ_refl S Y _
  cont := by
    rw [physIncl_image_physV]
    exact hcont

variable {I : DirectTerms S m₀ hp emb ρ Rσ εU a Θ₀ (physSΛ S a₁ ν eps) XW val (physAgΘ S) AgF}
  (hF : DirectTermsFamilyOn S m₀ (physIncl N S) I (physV S a₁ ν eps))
  (hN : L ^ m₀ ∣ N₁) (hρ : 0 < ρ) (hRσ : 0 ≤ Rσ) (hεU : 0 ≤ εU)
  {κ0 Kc : ℝ} (hκ0 : aEnt d L + 1 ≤ κ0) (hKc : K0 d L κ0 ≤ Kc)

/-- **The `ParamMarkFamily` of physical activities over the subspace parametrization** with given
marks (the four mark fields over `physV`). -/
theorem paramMarkFamily_physical_subspace (hRσ1 : 1 < Rσ) {ι : Type*}
    (y0 : ι → {Y // Y ∈ I.𝒴}) (G : physParam N S → ι → ℂ → (∀ b, (S.blockSplit m₀ hp).Ωb b) → ℂ)
    (κG : ℝ) (F0 : ι → ℝ)
    (hGmeas : ∀ θ i u, Measurable (G θ i u))
    (hGbound : ∀ θ i u Φ, ‖G θ i u Φ‖ ≤ F0 i * Real.exp (-κG * (thickLabels I.𝒴 I.dom).dl (y0 i)))
    (hGhol : ∀ i, ∀ Φ ∈ physCarrier S m₀ hp,
      AnalyticOnNhd ℂ (fun p : physParam N S × ℂ => G p.1 i p.2 Φ)
        (physV S a₁ ν eps ×ˢ ball (0 : ℂ) Rσ))
    (hGcont : ∀ i, ∀ θ ∈ physV S a₁ ν eps, ∀ u ∈ ball (0 : ℂ) Rσ,
      ContinuousOn (G θ i u) (physCarrier S m₀ hp)) :
    ParamMarkFamily (S.blockSplit m₀ hp).μ (thickLabels I.𝒴 I.dom)
      (labelActFamilyOn S m₀ (physIncl N S) I hF hN hρ hRσ hεU hκ0 hKc) y0 G κG F0
      (physV S a₁ ν eps) (ball (0 : ℂ) Rσ) (physCarrier S m₀ hp) :=
  paramMarkFamilyOn_of_marks S m₀ (physIncl N S) hF hN hρ hRσ hεU hκ0 hKc hRσ1 y0 G κG F0
    hGmeas hGbound hGhol hGcont

/-- **Locality of the physical activities in the restriction of the datum** (parametrization by
the subspace).  If `e, e' ∈ physV` have the same restriction of `physIncl e`, `physIncl e'` to the
region `physRegion` of `Z = Ŷ(sitesOf T)`, then the activities at the labels inside `Z` coincide. -/
theorem physical_labelActFamilyOn_local
    (T : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) m₀ (k + 1)
      Set.univ)) :
    ∀ e ∈ physV S a₁ ν eps, ∀ e' ∈ physV S a₁ ν eps,
      physRestrict (N := N) (physRegion S I.𝒴 (Yhat Set.univ (sitesOf T))) (physIncl N S e) =
        physRestrict (physRegion S I.𝒴 (Yhat Set.univ (sitesOf T))) (physIncl N S e') →
      ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ y,
        (thickLabels I.𝒴 I.dom).ysite y ⊆ Yhat Set.univ (sitesOf T) →
        (labelActFamilyOn S m₀ (physIncl N S) I hF hN hρ hRσ hεU hκ0 hKc e (s : ℂ)).H y =
          (labelActFamilyOn S m₀ (physIncl N S) I hF hN hρ hRσ hεU hκ0 hKc e' (s : ℂ)).H y := by
  intro e he e' he' h _ _ y hy
  refine labelActFamilyOn_local S m₀ (physIncl N S) hF hN hρ hRσ hεU hκ0 hKc he he' _ ?_ _ y hy
  intro Y hY hYZ
  exact physAgΘ_of_restrict S (Y := Y) (R := physRegion S I.𝒴 (Yhat Set.univ (sitesOf T)))
    (fun x hx => ⟨Y, hY, hYZ, hx⟩) h

/-- **Analytic, local and bounded on `physV`.**  Let `G` be marks satisfying the four mark fields
over `physV`, each mark depending only on the blocks of its label (`hGdep`), and equal at two
parameters of `physV` with the same restriction to the region of `Ŷ(sitesOf T)` (`hGloc`).  Then the
coefficient `e ↦ gsumCoeff … T` of the physical activities and these marks is analytic on `physV`,
takes equal values at `e, e' ∈ physV` with equal restrictions of `physIncl e`, `physIncl e'` to
that region, and is bounded on `physV` by the uniform bound `CPE …`.  (For zero marks the mark
hypotheses are trivial.) -/
theorem physical_paramMarked_analytic_local_bound {ι : Type*} [Fintype ι] (hRσ1 : 1 < Rσ)
    (y0 : ι → {Y // Y ∈ I.𝒴}) (G : physParam N S → ι → ℂ → (∀ b, (S.blockSplit m₀ hp).Ωb b) → ℂ)
    (κG : ℝ) (F0 : ι → ℝ)
    (hGmeas : ∀ θ i u, Measurable (G θ i u))
    (hGbound : ∀ θ i u Φ, ‖G θ i u Φ‖ ≤ F0 i * Real.exp (-κG * (thickLabels I.𝒴 I.dom).dl (y0 i)))
    (hGhol : ∀ i, ∀ Φ ∈ physCarrier S m₀ hp,
      AnalyticOnNhd ℂ (fun p : physParam N S × ℂ => G p.1 i p.2 Φ)
        (physV S a₁ ν eps ×ˢ ball (0 : ℂ) Rσ))
    (hGcont : ∀ i, ∀ θ ∈ physV S a₁ ν eps, ∀ u ∈ ball (0 : ℂ) Rσ,
      ContinuousOn (G θ i u) (physCarrier S m₀ hp))
    (hGdep : ∀ θ i s, DepOn (blocksOf m₀ (k + 1) Set.univ
      ((thickLabels I.𝒴 I.dom).ysite (y0 i))) (G θ i s))
    (hKc1 : K0 d L κ0 + 1 ≤ Kc) (hεpos : 0 < Rσ * εU) (hι : Nonempty ι) (hF0 : ∀ i, 0 < F0 i)
    {κ' : ℝ} (hκ' : 0 ≤ κ') (hκG : a ≤ κG)
    (hκ : κ' + 3 * κ0 + c1 d L + 3 / 2 ≤ a)
    (hε : Rσ * εU ≤ 1 / (8 * Kc ^ 3 * c1 d L *
      Real.exp ((a - 2 * κ0) * cG d L + c1 d L + κ' * cG d L)))
    (T : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) m₀ (k + 1)
      Set.univ))
    (hGloc : ∀ e ∈ physV S a₁ ν eps, ∀ e' ∈ physV S a₁ ν eps,
      physRestrict (N := N) (physRegion S I.𝒴 (Yhat Set.univ (sitesOf T))) (physIncl N S e) =
        physRestrict (physRegion S I.𝒴 (Yhat Set.univ (sitesOf T))) (physIncl N S e') →
      ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ i,
        (thickLabels I.𝒴 I.dom).ysite (y0 i) ⊆ Yhat Set.univ (sitesOf T) →
        G e i (s : ℂ) = G e' i (s : ℂ)) :
    AnalyticOnNhd ℂ (fun e => gsumCoeff (S.blockSplit m₀ hp).μ (thickLabels I.𝒴 I.dom)
      (labelActFamilyOn S m₀ (physIncl N S) I hF hN hρ hRσ hεU hκ0 hKc e) y0 (G e) T)
      (physV S a₁ ν eps) ∧
    (∀ e ∈ physV S a₁ ν eps, ∀ e' ∈ physV S a₁ ν eps,
      physRestrict (N := N) (physRegion S I.𝒴 (Yhat Set.univ (sitesOf T))) (physIncl N S e) =
        physRestrict (physRegion S I.𝒴 (Yhat Set.univ (sitesOf T))) (physIncl N S e') →
      gsumCoeff (S.blockSplit m₀ hp).μ (thickLabels I.𝒴 I.dom)
        (labelActFamilyOn S m₀ (physIncl N S) I hF hN hρ hRσ hεU hκ0 hKc e) y0 (G e) T =
      gsumCoeff (S.blockSplit m₀ hp).μ (thickLabels I.𝒴 I.dom)
        (labelActFamilyOn S m₀ (physIncl N S) I hF hN hρ hRσ hεU hκ0 hKc e') y0 (G e') T) ∧
    ∀ e ∈ physV S a₁ ν eps, ‖gsumCoeff (S.blockSplit m₀ hp).μ (thickLabels I.𝒴 I.dom)
      (labelActFamilyOn S m₀ (physIncl N S) I hF hN hρ hRσ hεU hκ0 hKc e) y0 (G e) T‖ ≤
        CPE d L Kc a κ0 κ' *
          (∑ i, F0 i * Real.exp (-κ0 * (thickLabels I.𝒴 I.dom).dl (y0 i))) *
          Real.exp (-κ' * dExt T) := by
  have hfam := paramMarkFamily_physical_subspace S m₀ hF hN hρ hRσ hεU hκ0
    (le_trans (by linarith) le_rfl : K0 d L κ0 ≤ Kc) hRσ1 y0 G κG F0 hGmeas hGbound hGhol hGcont
  exact paramMarked_analytic_local_bound (m₀ := m₀) (j := k + 1) (Ω := Set.univ)
    (S.blockSplit m₀ hp).μ hN le_rfl isPiUnion_univ_aux hfam hGdep hκ0 hKc1 hεpos hι hF0 hκ' hκG hκ
    hε T (fun e => physRestrict (N := N) (physRegion S I.𝒴 (Yhat Set.univ (sitesOf T)))
      (physIncl N S e))
    (fun e he e' he' h s hs y hy =>
      physical_labelActFamilyOn_local S m₀ hF hN hρ hRσ hεU hκ0 _ T e he e' he' h s hs y hy)
    (fun e he e' he' h s hs i hi => hGloc e he e' he' h s hs i hi)

end Physical

section Instance

open Balaban.SmallField Balaban.Analysis Finset Matrix Set Metric

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱm : ℝ}
variable {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}
variable {a₁ ν c BG κ eps : ℝ}

variable (S : StepSetting d L N₁ m₁ k N ϱ)
    {ρ εU : ℝ} {Kc Cx c₂ BG₂ δ₁ : ℝ}
    (hC : FlCore N S.G' Hm a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁) (cβ : ℂ)
    (hconn : HatConn S.G') (hrow : RowInHat (coverOf S.G') Hm (compWeight L a₁) ν)
    {κdec κ₀ : ℝ} (hκ₀ : 0 ≤ κ₀) (hκdec : 3 * κ₀ + 3 ≤ κdec)
    (hκ : 4 * d * (((2 * L + 1) ^ d : ℕ) : ℝ) * κdec ≤ κ) (h1 : 1 ≤ (κ / 2 - 1) / 2)
    {R₁ : ℝ} (hR₁ : 1 < R₁) {r Rσ : ℝ} (hr : 0 < r)
    -- the hat variable
    (hk : 1 ≤ k) (hG : IsLevel Hm k) (cc : ℂ)
    {cψ : ℝ} (hcψ : 0 ≤ cψ)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δc : ℝ}
    (hdm : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsmX : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    (hδ₁ : Real.sqrt N * (‖cc‖ * (covSupConstC d L N (compWeight L a₁ k) κ * cψ)) < δ₁)
    -- the potential part
    (ha₁ : 0 < a₁)
    (H : BgHyp d L (k + 1) ϱm (compWeight L a₁) ν) (hc7 : c7 d L N BG κ ≤ thm73C3 d L N)
    {R : ℝ} (hR : 2 ≤ R) (hRs : R * δ₁ ≤ deltaStar d L N)
    (hsmall : cK2 d L N * (R * δ₁) < bgC0 d L N / 2)
    (hnum : cK2 d L N * δ₁ ≤ c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8))
    (hnum' : cK2' d L N (famConst d L BG₂ κ) * δ₁ ≤
      c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8))
    (hsm : 2 * (compC4 d * (bgK1 d L N * (xiC1 d * eps))) + 5 * (R * δ₁) ≤ bgC1 d L N)
    {m₀ : ℕ} {jV : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) → ℕ}
    {XV 𝒦XV : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) → Set (CTorus d L N₁ m₁ (k + 1))}
    {X₁V : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) → Finset (CTorus d L N₁ m₁ (k + 1))}
    (hcovV : ∀ z, CovSetup S.G' (m₀) (jV z) (XV z) (𝒦XV z))
    (hX₁V : ∀ z, (↑(X₁V z) : Set (CTorus d L N₁ m₁ (k + 1))) = X1 S.G' (m₀) (jV z) (𝒦XV z))
    (hoptV : ∀ z, ∃ (W₀ : Finset (CTorus d L N₁ m₁ (k + 1)))
      (E₀ : Finset (CTorus d L N₁ m₁ (k + 1) × CTorus d L N₁ m₁ (k + 1))),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ XV z) ∧ MeetsOne (m₀) (jV z) (𝒦XV z) W₀ ∧
        bondCost (scaleW L (m₀) m₁ (jV z)) E₀ = treeLenCovOne (m₀) (jV z) (XV z))
    (hΔV : ∀ z, treeLenCovOne (m₀) (jV z) (XV z) = 0)
    (hlogV : ∀ _z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))), Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) * (((L ^ m₀) ^ d : ℕ) : ℝ)) ≤
      (κ / 2 - 1) / 2)
    (hZV : ∀ z, readSites Hm k z ⊆ ↑(X₁V z))
    (hmarV : ∀ z, BlockMargin S.G' (X₁V z)
      (↑(blockSites d L N₁ m₁ (k + 1) k z) : Set (CTorus d L N₁ m₁ (k + 1))))
    -- the old terms
    {τι : Type*} [DecidableEq τι] (𝒯E : Finset τι) {ϱ₁ ϱ₂ : τι → ℝ}
    {GkE : ∀ τ, GeneratingSet d L (N₁ * L ^ m₁) (k + 1) (ϱ₁ τ)}
    {GjE : ∀ τ, GeneratingSet d L (N₁ * L ^ m₁) (k + 1) (ϱ₂ τ)} {r₀ δ₃ δfl : ℝ}
    {X₀E X₁E : τι → Finset (CTorus d L N₁ m₁ (k + 1))} {jE : τι → ℕ}
    {XE 𝒦XE : τι → Set (CTorus d L N₁ m₁ (k + 1))} {EbE : τι → ℝ}
    (hBE : ∀ τ ∈ 𝒯E, BgSetting N S.G' (GkE τ) (GjE τ) a₁ ν c BG κ r₀ eps δ₃ (X₀E τ) (X₁E τ) (jE τ))
    (hFE : ∀ τ ∈ 𝒯E, FlSetting N S.G' (GkE τ) Hm a₁ ν κ BG eps δ₃ Kc Cx c₂ BG₂ δ₁ δfl (X₁E τ))
    (hcovE : ∀ τ ∈ 𝒯E, CovSetup S.G' (m₀) (jE τ) (XE τ) (𝒦XE τ))
    (hX₁E : ∀ τ ∈ 𝒯E, (↑(X₁E τ) : Set (CTorus d L N₁ m₁ (k + 1))) = X1 S.G' (m₀) (jE τ) (𝒦XE τ))
    (hoptE : ∀ τ ∈ 𝒯E, ∃ (W₀ : Finset (CTorus d L N₁ m₁ (k + 1)))
      (E₀ : Finset (CTorus d L N₁ m₁ (k + 1) × CTorus d L N₁ m₁ (k + 1))),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ XE τ) ∧ MeetsOne (m₀) (jE τ) (𝒦XE τ) W₀ ∧
        bondCost (scaleW L (m₀) m₁ (jE τ)) E₀ = treeLenCovOne (m₀) (jE τ) (XE τ))
    (hlogE : ∀ τ ∈ 𝒯E, Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) *
      (((L ^ m₀) ^ d : ℕ) : ℝ)) ≤ (κ / 2 - 1) / 2)
    (hEbE : ∀ τ ∈ 𝒯E, 0 ≤ EbE τ) {EE : τι → RawData d L (N₁ * L ^ m₁) (k + 1) N → ℂ}
    (hEanE : ∀ τ ∈ 𝒯E, AnalyticOnNhd ℂ (EE τ) (XiCRaw (GjE τ) (compWeight L a₁) ν (jE τ)
      (scaledC0 d) (scaledC0 d ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl)))
    (hEbdE : ∀ τ ∈ 𝒯E, ∀ r ∈ XiCRaw (GjE τ) (compWeight L a₁) ν (jE τ) (scaledC0 d)
      (scaledC0 d ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl),
      ‖EE τ r‖ ≤ EbE τ * Real.exp (-(κdec - 1) * treeLenCovOne (m₀) (jE τ) (XE τ)))
    -- the sites of the source
    {jF : CTorus d L N₁ m₁ (k + 1) × Fin N → ℕ}
    {XF 𝒦XF : CTorus d L N₁ m₁ (k + 1) × Fin N → Set (CTorus d L N₁ m₁ (k + 1))}
    {X₁F : CTorus d L N₁ m₁ (k + 1) × Fin N → Finset (CTorus d L N₁ m₁ (k + 1))}
    (hcovF : ∀ s, CovSetup S.G' (m₀) (jF s) (XF s) (𝒦XF s))
    (hX₁F : ∀ s, (↑(X₁F s) : Set (CTorus d L N₁ m₁ (k + 1))) = X1 S.G' (m₀) (jF s) (𝒦XF s))
    (hoptF : ∀ s, ∃ (W₀ : Finset (CTorus d L N₁ m₁ (k + 1)))
      (E₀ : Finset (CTorus d L N₁ m₁ (k + 1) × CTorus d L N₁ m₁ (k + 1))),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ XF s) ∧ MeetsOne (m₀) (jF s) (𝒦XF s) W₀ ∧
        bondCost (scaleW L (m₀) m₁ (jF s)) E₀ = treeLenCovOne (m₀) (jF s) (XF s))
    (hΔF : ∀ s, treeLenCovOne (m₀) (jF s) (XF s) = 0)
    (hlogF : ∀ _s : CTorus d L N₁ m₁ (k + 1) × Fin N, Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) * (((L ^ m₀) ^ d : ℕ) : ℝ)) ≤
      (κ / 2 - 1) / 2)
    (hyF : ∀ s : CTorus d L N₁ m₁ (k + 1) × Fin N, s.1 ∈ X₁F s)
    -- the observable terms
    {μι : Type*} [DecidableEq μι] (𝒯M : Finset μι) {ϱ₁M ϱ₂M : μι → ℝ}
    {GkM : ∀ τ, GeneratingSet d L (N₁ * L ^ m₁) (k + 1) (ϱ₁M τ)}
    {GjM : ∀ τ, GeneratingSet d L (N₁ * L ^ m₁) (k + 1) (ϱ₂M τ)}
    {X₀M X₁M : μι → Finset (CTorus d L N₁ m₁ (k + 1))} {jM : μι → ℕ}
    {XM 𝒦XM : μι → Set (CTorus d L N₁ m₁ (k + 1))} {EbM : μι → ℝ}
    (ys : μι → CTorus d L N₁ m₁ (k + 1)) (is : μι → Fin N) (hys : ∀ τ ∈ 𝒯M, ys τ ∈ X₁M τ)
    (hBM : ∀ τ ∈ 𝒯M, BgSetting N S.G' (GkM τ) (GjM τ) a₁ ν c BG κ r₀ eps δ₃ (X₀M τ) (X₁M τ) (jM τ))
    (hFM : ∀ τ ∈ 𝒯M, FlSetting N S.G' (GkM τ) Hm a₁ ν κ BG eps δ₃ Kc Cx c₂ BG₂ δ₁ δfl (X₁M τ))
    (hcovM : ∀ τ ∈ 𝒯M, CovSetup S.G' (m₀) (jM τ) (XM τ) (𝒦XM τ))
    (hX₁M : ∀ τ ∈ 𝒯M, (↑(X₁M τ) : Set (CTorus d L N₁ m₁ (k + 1))) = X1 S.G' (m₀) (jM τ) (𝒦XM τ))
    (hoptM : ∀ τ ∈ 𝒯M, ∃ (W₀ : Finset (CTorus d L N₁ m₁ (k + 1)))
      (E₀ : Finset (CTorus d L N₁ m₁ (k + 1) × CTorus d L N₁ m₁ (k + 1))),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ XM τ) ∧ MeetsOne (m₀) (jM τ) (𝒦XM τ) W₀ ∧
        bondCost (scaleW L (m₀) m₁ (jM τ)) E₀ = treeLenCovOne (m₀) (jM τ) (XM τ))
    (hlogM : ∀ τ ∈ 𝒯M, Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) *
      (((L ^ m₀) ^ d : ℕ) : ℝ)) ≤ (κ / 2 - 1) / 2)
    (hEbM : ∀ τ ∈ 𝒯M, 0 ≤ EbM τ) {EM : μι → RawData d L (N₁ * L ^ m₁) (k + 1) N → ℂ}
    (hEanM : ∀ τ ∈ 𝒯M, AnalyticOnNhd ℂ (EM τ) (XiCRaw (GjM τ) (compWeight L a₁) ν (jM τ)
      (scaledC0 d) (scaledC0 d ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl)))
    (hEbdM : ∀ τ ∈ 𝒯M, ∀ r ∈ XiCRaw (GjM τ) (compWeight L a₁) ν (jM τ) (scaledC0 d)
      (scaledC0 d ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl),
      ‖EM τ r‖ ≤ EbM τ * Real.exp (-(κdec - 1) * treeLenCovOne (m₀) (jM τ) (XM τ)))
    -- the sizes of the old terms and of the observable terms (the source bounds of (3.2)-(3.4)):
    -- the bounds of the terms rooted at one site (resp. at one source site) add up to `ρ`
    (rE : τι → CTorus d L N₁ m₁ (k + 1)) (hrE : ∀ τ ∈ 𝒯E, rE τ ∈ X₁E τ) {ρE : ℝ} (hρE0 : 0 ≤ ρE)
    (hρE : ∀ x : CTorus d L N₁ m₁ (k + 1), ∑ τ ∈ 𝒯E.filter (fun τ => rE τ = x),
      EbE τ * Real.exp (-κ₀ * treeLenCovOne m₀ (jE τ) (XE τ)) ≤ ρE)
    {ρM : ℝ} (hρM0 : 0 ≤ ρM)
    (hρM : ∀ p : CTorus d L N₁ m₁ (k + 1) × Fin N, ∑ τ ∈ 𝒯M.filter (fun τ => (ys τ, is τ) = p),
      EbM τ * Real.exp (-κ₀ * treeLenCovOne m₀ (jM τ) (XM τ)) ≤ ρM)
    -- the `ν`-part: the bound on the external field and the block margin of the blocks
    {Bh : ℝ} (hBh0 : 0 ≤ Bh)
    (hBh : ∀ D : BgData S.G' N, XiCData S.G' (compWeight L a₁) ν (k + 1) 1 eps D →
      ∀ x i, ‖D.h x i‖ ≤ Bh) (cν : ℂ)
    (hZν : ∀ z, (↑(blockSites d L N₁ m₁ (k + 1) k z) : Set (CTorus d L N₁ m₁ (k + 1))) ⊆ ↑(X₁V z))
    (hRσ : 0 < Rσ) (hc : (Rσ * R₁ + r) * ρ < cψ)
    {Θ₀ : RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ)}
    (hΘ₀ : Θ₀ ∈ XiCRaw S.G' (compWeight L a₁) ν (k + 1) 1 eps ×ˢ l1Ball d L N₁ m₁ (k + 1) N)
    (hεb : prop33Eps d L N m₁ k m₀ a₁ ν BG BG₂ κ δ₁ r ρE ρM * ‖cβ‖ +
      ‖cν‖ * (1 * (c1 d L * ((L : ℝ) ^ (m₀ + m₁)) ^ d *
        nuBd d L N k (cK2' d L N (famConst d L BG₂ κ) * δ₁)
          (K4 d L N BG κ * (xiC1 d * eps) + (1 + 3 * (xiC1 d * eps)) + Bh) / r)) ≤ εU)


variable (hN : L ^ m₀ ∣ N₁) (hp : 0 < S.p₁)

include hC hconn hrow hκ₀ hκdec hκ h1 hR₁ hr hk hG hcψ hMX hdm hα hsmX hδ₁ ha₁ H hc7 hR hRs hsmall hnum hnum' hsm hcovV hX₁V hoptV hΔV hlogV hZV hmarV hBE hFE hcovE hX₁E hoptE hlogE hEbE hEanE hEbdE hcovF hX₁F hoptF hΔF hlogF hyF hys hBM hFM hcovM hX₁M hoptM hlogM hEbM hEanM hEbdM hrE hρE0 hρE hρM0 hρM hBh0 hBh hZν
include hRσ hc hΘ₀ hεb hN hp

/-- **The physical `ParamMarkFamily` over the subspace parametrization, from the physical
expansion.**  Under exactly the hypotheses of `physical_directTerms` (and `0 < ρ`, `0 ≤ ε_U`,
`1 < R_σ`, and the constants `κ₀`, `K_c` of the label activities), the `DirectTerms` produced by
`physical_directTerms` at the datum `Θ₀` of the chart carry a relative family over
`physV`, the datum `Θ₀` is the image of a point of `physV` (so `physV` is non-empty), and the
physical activities `labelActFamilyOn` form a `ParamMarkFamily` over `physParam` with carrier
`physCarrier`, `𝒰 = ball 0 R_σ` and no marks. -/
theorem physical_paramMarkFamily_exists
    (Hϱ : BgHyp d L (k + 1) ϱ (compWeight L a₁) ν) (hρ : 0 < ρ) (hεU : 0 ≤ εU) (hRσ1 : 1 < Rσ)
    {κ0 Kc' : ℝ} (hκ0 : aEnt d L + 1 ≤ κ0) (hKc : K0 d L κ0 ≤ Kc') :
    ∃ (I : DirectTerms S m₀ hp (fun ψ : unitPts S.G' × Fin N → ℂ => (ψ, ψ)) ρ Rσ εU
        (2 * κdec - 1) Θ₀ (physSΛ S a₁ ν eps) (physXW S cψ R₁ Rσ r)
        (physVal (EE := EE) (EM := EM) S cβ hG cc 𝒯E hBE hFE 𝒯M ys is hBM hFM cν)
        (physAgΘ S) (AgFDirPair S))
      (hF : DirectTermsFamilyOn S m₀ (physIncl N S) I (physV S a₁ ν eps)),
      (∃ e₀ ∈ physV S a₁ ν eps, physIncl N S e₀ = Θ₀) ∧
      Nonempty (ParamMarkFamily (S.blockSplit m₀ hp).μ (thickLabels I.𝒴 I.dom)
        (labelActFamilyOn S m₀ (physIncl N S) I hF hN hρ hRσ.le hεU hκ0 hKc)
        (fun e : Empty => e.elim) (fun _ _ _ _ => (0 : ℂ)) 0 (fun e : Empty => e.elim)
        (physV S a₁ ν eps) (ball (0 : ℂ) Rσ) (physCarrier S m₀ hp)) := by
  obtain ⟨I, hI1, hI2, hI3⟩ := physical_directTerms (S := S) (hC := hC) (cβ := cβ) (hconn := hconn) (hrow := hrow) (hκ₀ := hκ₀) (hκdec := hκdec) (hκ := hκ) (h1 := h1) (hR₁ := hR₁) (hr := hr) (hk := hk) (hG := hG) (cc := cc) (hcψ := hcψ) (hMX := hMX) (hdm := hdm) (hα := hα) (hsmX := hsmX) (hδ₁ := hδ₁) (ha₁ := ha₁) (H := H) (hc7 := hc7) (hR := hR) (hRs := hRs) (hsmall := hsmall) (hnum := hnum) (hnum' := hnum') (hsm := hsm) (hcovV := hcovV) (hX₁V := hX₁V) (hoptV := hoptV) (hΔV := hΔV) (hlogV := hlogV) (hZV := hZV) (hmarV := hmarV) (𝒯E := 𝒯E) (hBE := hBE) (hFE := hFE) (hcovE := hcovE) (hX₁E := hX₁E) (hoptE := hoptE) (hlogE := hlogE) (hEbE := hEbE) (hEanE := hEanE) (hEbdE := hEbdE) (hcovF := hcovF) (hX₁F := hX₁F) (hoptF := hoptF) (hΔF := hΔF) (hlogF := hlogF) (hyF := hyF) (𝒯M := 𝒯M) (ys := ys) (is := is) (hys := hys) (hBM := hBM) (hFM := hFM) (hcovM := hcovM) (hX₁M := hX₁M) (hoptM := hoptM) (hlogM := hlogM) (hEbM := hEbM) (hEanM := hEanM) (hEbdM := hEbdM) (rE := rE) (hrE := hrE) (hρE0 := hρE0) (hρE := hρE) (hρM0 := hρM0) (hρM := hρM) (hBh0 := hBh0) (hBh := hBh) (cν := cν) (hZν := hZν) (hRσ := hRσ) (hc := hc) (hΘ₀ := hΘ₀) (hεb := hεb) hN hp
  have hF : DirectTermsFamilyOn S m₀ (physIncl N S) I (physV S a₁ ν eps) :=
    physical_directTermsFamilyOn S m₀ hI1.cont Hϱ
  refine ⟨I, hF, ?_, ⟨paramMarkFamilyOn_zero_marks S m₀ (physIncl N S) hF hN hρ hRσ.le hεU hκ0
    hKc hRσ1 (fun e : Empty => e.elim) 0 (fun e : Empty => e.elim) (fun e : Empty => e.elim)⟩⟩
  have hp0 : Θ₀.1 ∈ rawSub N S.G' := XiCRaw_subset_rawSub _ _ _ _ _ _ hΘ₀.1
  exact ⟨(⟨Θ₀.1, hp0⟩, Θ₀.2), hΘ₀, rfl⟩

end Instance

section Inhabited

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}
  (S : StepSetting d L N₁ m₁ k N ϱ) (m₀ : ℕ)

/-- **`DirectTermsFamilyOn` is inhabited** (the whole-torus label with zero terms, parameter space
`ℂ`, `J = id`, `V = univ`; the instance of `nonempty_directTermsFamily`). -/
theorem nonempty_directTermsFamilyOn (hp : 0 < S.p₁) (ρ Rσ εU a : ℝ) (hεU : 0 ≤ εU) :
    ∃ (I : DirectTerms S m₀ hp (F' := Unit) (fun _ => ()) ρ Rσ εU a (0 : ℂ) Set.univ Set.univ
      (fun _ _ _ _ => (0 : ℂ)) (fun _ _ _ => True) (fun _ _ _ => True))
      (_ : DirectTermsFamilyOn S m₀ (ContinuousLinearMap.id ℂ ℂ) I Set.univ),
      I.𝒴.Nonempty := by
  obtain ⟨I, hF, hne, -⟩ := nonempty_directTermsFamily S m₀ hp ρ Rσ εU a hεU
  refine ⟨I, ⟨isOpen_univ, Set.subset_univ _, hF.agΘ, ?_⟩, hne⟩
  simpa using hF.cont

end Inhabited

end Balaban.Fluctuation
