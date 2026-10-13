/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.XiCRawOpen
public import Balaban.Fluctuation.ParamActivityPhysical
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

end Physical

end Balaban.Fluctuation
