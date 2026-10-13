/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.ObsTiltLabels
public import Balaban.Inhabited.ObsKernelFromTower
public import Balaban.Fluctuation.ObsFirstOrderClamp
public import Balaban.Fluctuation.ObsRemainderFamily
public import Balaban.Fluctuation.MarkIntTermAnalytic
public import Balaban.Fluctuation.Thm31CoeffB
public import Balaban.Fluctuation.ParamCarrierLocal
public import Balaban.Inhabited.StepScaleDataGBridge

/-!
# The coefficients of the observable as analytic functions of the parameter

The observable of the renormalization step is expanded with the coefficients
`kernelMarkSum (kernel) (first-order terms) + gsumCoeff (remainder)`, where the first-order
terms and the remainder are built from one activity family on the labels of the observable.

* `obsCoeffParam`: this expression, for a parameter `e`.
* `obsCoeffParam_analyticOnNhd`: when the two mark families are `ParamMarkFamily` records for the
  same activity and the kernel is analytic, the first-order terms, the kernel sum, the remainder
  coefficient and their sum are analytic on the open parameter set.
* `nonempty_paramMarkFamily_blockMarkC`, `nonempty_paramMarkFamily_obsGrFam`: the two records,
  from the fields of the landed lemmas.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Localization Balaban.Polymer MeasureTheory Metric Balaban.Multiscale
  Balaban.Background Balaban.SmallField Balaban.SmallField.Def6

section Generic

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {m₀ j : ℕ} {Ω : Set (CTorus d L N₁ m₁ K)}

local notation "𝔅" => CubeB (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ j Ω

/-- **The coefficient of the observable at the parameter `e`**: the resummed products of the
kernel with the first-order terms, plus the coefficient of the remainder marks; the activities
are those of `Aact e` (the first-order terms read them at `σ = 1`, `s ∈ [0,1]`; the remainder
reads `Aact e · 1`). -/
noncomputable def obsCoeffParam {E ι ι' Lb : Type*} [Fintype ι] [Fintype ι'] [Fintype Lb]
    {Ωb : 𝔅 → Type*} [∀ b, MeasurableSpace (Ωb b)]
    (μ : ∀ b, Measure (Ωb b)) [∀ b, IsProbabilityMeasure (μ b)] {Lab : CubeLabels m₀ j Ω Lb}
    {εH κH κ0 Kc : ℝ} (Aact : E → ℂ → ℂ → LabelAct Lab Ωb εH κH κ0 Kc)
    (y1 : ι → Lb) (G1 : ι → (∀ b, Ωb b) → ℂ) (hker : E → ι → Finset 𝔅 → ℂ)
    (yr : ι' → Lb) (Gr : E → ι' → ℂ → (∀ b, Ωb b) → ℂ) (e : E) (T : Finset 𝔅) : ℂ :=
  kernelMarkSum (hker e) (fun i S => markIntTerm μ (Aact e) (y1 i) (G1 i) S) T +
    gsumCoeff μ Lab (fun t => Aact e t 1) yr (Gr e) T

variable {Lb : Type*} [Fintype Lb] {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [FiniteDimensional ℂ E] {ι ι' : Type*} [Fintype ι] [Fintype ι']

/-- **Analyticity of the three parts of the coefficient and of their sum.**  Let the first-order
marks `G1 i` (independent of the parameter) and the remainder marks `Gr` each form a
`ParamMarkFamily` for the activity `fun θ t => Aact θ t 1` on `V × 𝒰`, and let the kernel be
analytic on `V`.  Then for every finite set `T` of cubes: each first-order term, the kernel sum,
the remainder coefficient and `obsCoeffParam` are analytic on `V`. -/
theorem obsCoeffParam_analyticOnNhd {Ωb : 𝔅 → Type*} [∀ b, MeasurableSpace (Ωb b)]
    [∀ b, TopologicalSpace (Ωb b)] [∀ b, OpensMeasurableSpace (Ωb b)]
    [∀ b, SecondCountableTopology (Ωb b)]
    (μ : ∀ b, Measure (Ωb b)) [∀ b, IsProbabilityMeasure (μ b)]
    (hN : L ^ m₀ ∣ N₁) (hj : j ≤ K) (hΩ : IsPiUnion m₀ j Ω)
    {Lab : CubeLabels m₀ j Ω Lb} {εH κH κG κ0 κ' Kc : ℝ}
    {Aact : E → ℂ → ℂ → LabelAct Lab Ωb εH κH κ0 Kc}
    {V : Set E} {𝒰 : Set ℂ} {Q : Set (∀ b, Ωb b)}
    (y1 : ι → Lb) (G1 : ι → (∀ b, Ωb b) → ℂ) (F1 : ι → ℝ)
    (hfam1 : ∀ i, ParamMarkFamily μ Lab (fun θ t => Aact θ t 1) (fun _ : Unit => y1 i)
      (fun _ _ _ => G1 i) κG (fun _ => F1 i) V 𝒰 Q)
    (yr : ι' → Lb) (Gr : E → ι' → ℂ → (∀ b, Ωb b) → ℂ) (Fr : ι' → ℝ)
    (hfamr : ParamMarkFamily μ Lab (fun θ t => Aact θ t 1) yr Gr κG Fr V 𝒰 Q)
    (hker : E → ι → Finset 𝔅 → ℂ) (hh : ∀ i T, AnalyticOnNhd ℂ (fun e => hker e i T) V)
    (hκ0 : aEnt d L + 1 ≤ κ0) (hKc : K0 d L κ0 + 1 ≤ Kc) (hεpos : 0 < εH)
    (hF1 : ∀ i, 0 < F1 i) (hFr : ∀ i, 0 < Fr i) (hκ' : 0 ≤ κ') (hκG : κH ≤ κG)
    (hκ : κ' + 3 * κ0 + c1 d L + 3 / 2 ≤ κH)
    (hε : εH ≤ 1 / (8 * Kc ^ 3 * c1 d L *
      Real.exp ((κH - 2 * κ0) * cG d L + c1 d L + κ' * cG d L)))
    (T : Finset 𝔅) :
    (∀ i S, AnalyticOnNhd ℂ (fun e => markIntTerm μ (Aact e) (y1 i) (G1 i) S) V) ∧
    AnalyticOnNhd ℂ (fun e => kernelMarkSum (hker e)
      (fun i S => markIntTerm μ (Aact e) (y1 i) (G1 i) S) T) V ∧
    AnalyticOnNhd ℂ (fun e => gsumCoeff μ Lab (fun t => Aact e t 1) yr (Gr e) T) V ∧
    AnalyticOnNhd ℂ (fun e => obsCoeffParam μ Aact y1 G1 hker yr Gr e T) V := by
  have h1 : ∀ i S, AnalyticOnNhd ℂ (fun e => markIntTerm μ (Aact e) (y1 i) (G1 i) S) V :=
    fun i S => markIntTerm_analyticOnNhd_const μ hN hj hΩ (hfam1 i) hκ0 hKc hεpos (hF1 i) hκ'
      hκG hκ hε S
  have h2 : AnalyticOnNhd ℂ (fun e => kernelMarkSum (hker e)
      (fun i S => markIntTerm μ (Aact e) (y1 i) (G1 i) S) T) V :=
    kernelMarkSum_analyticOnNhd (hker) (fun e i S => markIntTerm μ (Aact e) (y1 i) (G1 i) S)
      hh h1 T
  have h3 : AnalyticOnNhd ℂ (fun e => gsumCoeff μ Lab (fun t => Aact e t 1) yr (Gr e) T) V :=
    gsumCoeff_analyticOnNhd μ hN hj hΩ hfamr hκ0 hKc hεpos hFr hκ' hκG hκ hε T
  exact ⟨h1, h2, h3, h2.add h3⟩

end Generic

section Families

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
  (S : StepSetting d L N₁ m₁ k N ϱ) (m₀ : ℕ) (hp : 0 < S.p₁)
  {Lb : Type} [Fintype Lb]
  (Lab : CubeLabels (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) m₀ (k + 1)
    Set.univ Lb) {εH κH κ0 Kc : ℝ}
  (Act : physParam N S → ℂ → LabelAct Lab (S.blockSplit m₀ hp).Ωb εH κH κ0 Kc)

/-- The points `s ∈ [0,1]` lie in the disc of radius `3/2`. -/
theorem seg_mem_ball_three_halves (s : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    (s : ℂ) ∈ ball (0 : ℂ) (3 / 2) := by
  rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs.1]
  linarith [hs.2]

variable {S m₀ hp Lab Act}

/-- **The family of the first-order mark `(u, a)`** (`ParamMarkFamily` for the constant family
`blockMarkC`), for an activity whose coefficients are analytic in `(θ, t)` and continuous in the
configuration: all fields from the landed lemmas on the clamped mark and the carrier. -/
theorem nonempty_paramMarkFamily_blockMarkC {V : Set (physParam N S)} (hV : IsOpen V)
    (hholA : ∀ y, ∀ Φ ∈ physCarrier S m₀ hp,
      AnalyticOnNhd ℂ (fun r : physParam N S × ℂ => (Act r.1 r.2).H y Φ)
        (V ×ˢ ball (0 : ℂ) (3 / 2)))
    (hcontA : ∀ y, ∀ θ ∈ V, ∀ u ∈ ball (0 : ℂ) (3 / 2),
      ContinuousOn ((Act θ u).H y) (physCarrier S m₀ hp))
    (u : S.U) (a : Fin N) (y0 : Lb) (κG : ℝ) :
    Nonempty (ParamMarkFamily (S.blockSplit m₀ hp).μ Lab Act (fun _ : Unit => y0)
      (fun _ _ _ => blockMarkC S m₀ hp u a) κG
      (fun _ => S.p₁ * Real.exp (κG * Lab.dl y0)) V (ball (0 : ℂ) (3 / 2))
      (physCarrier S m₀ hp)) :=
  ⟨{ isOpenV := hV
     isOpenU := isOpen_ball
     seg := fun s hs => seg_mem_ball_three_halves s hs
     compact := isCompact_physCarrier S m₀ hp
     measQ := measurableSet_physCarrier S m₀ hp
     carried := ae_mem_physCarrier S m₀ hp
     meas := fun _ _ _ => measurable_blockMarkC u a
     bound := fun θ i t Φ => blockMarkC_family_bound u a Lab y0 κG θ i t Φ
     holA := hholA
     holG := fun _ Φ _ => blockMarkC_family_holG u a V (ball (0 : ℂ) (3 / 2)) Φ
     contA := hcontA
     contG := fun _ θ _ t _ => blockMarkC_family_contG u a _ θ t }⟩

variable {a₁ ν eps cψ C0 κd κG : ℝ}
  {Ev : Set (CTorus d L N₁ m₁ (k + 1)) →
    RawData d L (N₁ * L ^ m₁) (k + 1) N × (S.U × Fin N → ℂ) → ℂ}
  {𝒴 : Finset (Set (CTorus d L N₁ m₁ (k + 1)))}

/-- **The family of the remainder marks** (`ParamMarkFamily` for `obsGrFam`, indices `RemIdx 𝒴`),
on any open `V ⊆ physV` and the disc of radius `3/2`, with the bound `8 C0 (p₁/cψ)²`. -/
theorem nonempty_paramMarkFamily_obsGrFam (H : BgHyp d L (k + 1) ϱ (compWeight L a₁) ν)
    {V : Set (physParam N S)} (hV : IsOpen V) (hVsub : V ⊆ physV S a₁ ν eps)
    (hcψ : 0 < cψ) (hq : S.p₁ / cψ ≤ 1 / 4)
    (ha : ∀ Y ∈ 𝒴, AnalyticOnNhd ℂ (Ev Y)
      (XiCRaw S.G' (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
        {ψ : S.U × Fin N → ℂ | ∀ p, ‖ψ p‖ ≤ cψ}))
    (hC0 : 0 < C0)
    (hb : ∀ Y ∈ 𝒴, ∀ x ∈ XiCRaw S.G' (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
        {ψ : S.U × Fin N → ℂ | ∀ p, ‖ψ p‖ ≤ cψ},
      ‖Ev Y x‖ ≤ C0 * Real.exp (-κd * treeLenCovOne m₀ (k + 1) Y))
    (lab : {Y // Y ∈ 𝒴} → Lb) (y₀ : Lb)
    (hdl : ∀ Y, Lab.dl (lab Y) = treeLenCovOne m₀ (k + 1) Y.1) (hκG : κG ≤ κd)
    (hholA : ∀ y, ∀ Φ ∈ physCarrier S m₀ hp,
      AnalyticOnNhd ℂ (fun r : physParam N S × ℂ => (Act r.1 r.2).H y Φ)
        (V ×ˢ ball (0 : ℂ) (3 / 2)))
    (hcontA : ∀ y, ∀ θ ∈ V, ∀ u ∈ ball (0 : ℂ) (3 / 2),
      ContinuousOn ((Act θ u).H y) (physCarrier S m₀ hp)) :
    Nonempty (ParamMarkFamily (S.blockSplit m₀ hp).μ Lab Act (obsRemLab 𝒴 lab y₀)
      (obsGrFam S m₀ hp Ev 𝒴 (XiCRaw S.G' (compWeight L a₁) ν (k + 1) 1 eps)) κG
      (fun _ => 8 * C0 * (S.p₁ / cψ) ^ 2) V (ball (0 : ℂ) (3 / 2)) (physCarrier S m₀ hp)) :=
  ⟨{ isOpenV := hV
     isOpenU := isOpen_ball
     seg := fun s hs => seg_mem_ball_three_halves s hs
     compact := isCompact_physCarrier S m₀ hp
     measQ := measurableSet_physCarrier S m₀ hp
     carried := ae_mem_physCarrier S m₀ hp
     meas := fun θ i t => measurable_obsGrFam hcψ hq ha θ i t
     bound := fun θ i t Φ => norm_obsGrFam_le hcψ hq ha hC0 hb Lab lab y₀ hdl hκG θ i t Φ
     holA := hholA
     holG := fun i Φ _ => (analyticOnNhd_obsGrFam (hp := hp) (m₀ := m₀) H subset_rfl hcψ hq ha i
       Φ).mono (Set.prod_mono hVsub subset_rfl)
     contA := hcontA
     contG := fun i _ hθ t _ => (continuous_obsGrFam (hp := hp) (m₀ := m₀) subset_rfl hcψ hq ha
       (hVsub hθ) i t).continuousOn }⟩

end Families

section Dep

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
  {S : StepSetting d L N₁ m₁ k N ϱ} {m₀ : ℕ} {hp : 0 < S.p₁}
  {Ev : Set (CTorus d L N₁ m₁ (k + 1)) →
    RawData d L (N₁ * L ^ m₁) (k + 1) N × (S.U × Fin N → ℂ) → ℂ}
  {𝒴 : Finset (Set (CTorus d L N₁ m₁ (k + 1)))} {cψ : ℝ}
  {A : Set (RawData d L (N₁ * L ^ m₁) (k + 1) N)}

/-- **Block locality of the remainder marks for every parameter**: the mark of the index `idx`
depends on the configuration only through the blocks of its label; for a parameter whose raw datum
is not in `A`, and for the dummy index, the mark is zero. -/
theorem depOn_obsGrFam_all {Lb : Type*}
    (hN : L ^ m₀ ∣ N₁) (hcψ : 0 < cψ) (hq : S.p₁ / cψ ≤ 1 / 4)
    (hdj : ∀ Y ∈ 𝒴, IsDj m₀ (k + 1) Y)
    (hd : ∀ Y ∈ 𝒴, ∀ u ∈ A ×ˢ {ψ : S.U × Fin N → ℂ | ∀ p, ‖ψ p‖ ≤ cψ},
      ∀ u' ∈ A ×ˢ {ψ : S.U × Fin N → ℂ | ∀ p, ‖ψ p‖ ≤ cψ},
        AgHatDir S.hG' Y u u' → Ev Y u = Ev Y u')
    (Lab : CubeLabels (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) m₀ (k + 1)
      Set.univ Lb) (lab : {Y // Y ∈ 𝒴} → Lb) (y₀ : Lb)
    (hysite : ∀ Y, Lab.ysite (lab Y) = Y.1) (θ : physParam N S) (idx : RemIdx 𝒴) (u : ℂ) :
    DepOn (Ω := (S.blockSplit m₀ hp).Ωb) (blocksOf (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
      (K := k + 1) m₀ (k + 1) Set.univ (Lab.ysite (obsRemLab 𝒴 lab y₀ idx)))
      (obsGrFam S m₀ hp Ev 𝒴 A θ idx u) := by
  by_cases hθ : (θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) ∈ A
  · rw [obsGrFam_of_mem hθ]
    rcases idx with _ | Y
    · intro Φ Φ' _
      rfl
    · have := depOn_obsGrRawC (hp := hp) (m₀ := m₀) hN hcψ hq hdj hd hθ Y u
      rw [obsRemLab]
      simp only [hysite]
      exact this
  · rw [obsGrFam_of_not_mem hθ]
    intro Φ Φ' _
    rfl

end Dep

section Raw

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
  {S : StepSetting d L N₁ m₁ k N ϱ}

/-- A function of the raw datum that is analytic on a set `A` is analytic, as a function of the
parameter `θ`, on every set of parameters whose raw data lie in `A`. -/
theorem analyticOnNhd_comp_rawFst {f : RawData d L (N₁ * L ^ m₁) (k + 1) N → ℂ}
    {A : Set (RawData d L (N₁ * L ^ m₁) (k + 1) N)} (h : AnalyticOnNhd ℂ f A)
    {V : Set (physParam N S)}
    (hV : ∀ θ ∈ V, (θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) ∈ A) :
    AnalyticOnNhd ℂ (fun θ : physParam N S => f (θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N))
      V := by
  have hlin : AnalyticOnNhd ℂ (fun θ : physParam N S =>
      (θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N)) Set.univ :=
    ((ContinuousLinearMap.fst ℂ _ _).comp (physIncl N S)).analyticOnNhd _
  exact h.comp (hlin.mono (Set.subset_univ _)) hV

end Raw

end Balaban.Fluctuation

namespace Balaban.Inhabited

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation
  Balaban.Localization Balaban.Localization.LevelPair Balaban.Localization.I5Inhabited
  Balaban.Polymer Balaban.SmallField.Def6 Balaban.Inhabited.LevelStep MeasureTheory Metric

section EvG

/-- General tower `T : StepTowerG d L N κmin` (block scale `T.m₀`, `b = β L^{k (d-2)}`); the fixed theorem `obsEv_fromTower_rawY` is its corollary.  **The one sharp-hat expansion at the tower, exact locality.**  The statement of
`obsEv_fromTower` with the locality clause for raw data agreeing on `Y` itself and hat variables
agreeing at the unit points of `Y`; `obsEv_fromTower` is its corollary.  The family `Ev` of
`obsMarkHalves_of_sharpHat_param_rawY` at the shared tower (the call of `obsHker_param_fromTower`),
with its three clauses (analyticity, locality, decay with `treeLenCovOne`) and, for every datum of
`Ξ`, `ObsMarkHalf` and `ObsRayIdentity`.  The same `Ev` serves the kernel and the remainder.
The last conjunct exhibits the terms: `Ev = evTerm … (siteFun …)` for a pair `(F₁, Sol)` of
decoupled background and fluctuation maps with their defining properties. -/
theorem obsEv_fromTower_rawYG {d L N : ℕ} [NeZero L] {κmin : ℝ} (T : StepTowerG d L N κmin)
    (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁] (ν β p₁ : ℝ) (hN : 5 < N₁)
    (hνpos : 0 < ν) (hν : ν * (L : ℝ) ^ (2 * (k + 1)) ≤ 1)
    (Dsc : StepScaleDataG T k hk N₁ ν β p₁)
    {ϱ : ℝ} (hϱ : ϱ = rhoSepG d L T.m₁) {S : StepSetting d L N₁ T.m₁ k N ϱ}
    (hS : S = hatStepKG T.hN k T.m₁ ϱ hk ν β p₁ T.δ)
    (hp : 0 < S.p₁) (y : CTorus d L N₁ T.m₁ (k + 1)) (i : Fin N)
    {Lb₀ : Type} (Lab₀ : CubeLabels (d := d) (L := L) (N₁ := N₁) (m₁ := T.m₁) (K := k + 1) T.m₀
      (k + 1) Set.univ Lb₀) :
    ∃ Ev : Set (CTorus d L N₁ T.m₁ (k + 1)) →
        RawData d L (N₁ * L ^ T.m₁) (k + 1) N × (unitPts S.G' × Fin N → ℂ) → ℂ,
      (∀ Y, AnalyticOnNhd ℂ (Ev Y) (XiCRaw S.G' (compWeight L 1) ν (k + 1) 1 T.t ×ˢ
          {ψh : unitPts S.G' × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ lvCpsiG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2)))})) ∧
      (∀ Y, ∀ u ∈ XiCRaw S.G' (compWeight L 1) ν (k + 1) 1 T.t ×ˢ
          {ψh : unitPts S.G' × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ lvCpsiG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2)))},
        ∀ u' ∈ XiCRaw S.G' (compWeight L 1) ν (k + 1) 1 T.t ×ˢ
          {ψh : unitPts S.G' × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ lvCpsiG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2)))},
        agreeOn Y u.1 u'.1 → (∀ y ∈ Y, ∀ i, u.2 (unitPt S.hG' y, i) = u'.2 (unitPt S.hG' y, i)) →
        Ev Y u = Ev Y u') ∧
      (∀ Y, ∀ u ∈ XiCRaw S.G' (compWeight L 1) ν (k + 1) 1 T.t ×ˢ
          {ψh : unitPts S.G' × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ lvCpsiG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2)))},
        ‖Ev Y u‖ ≤ (cK2' d L N (famConst d L T.BG₂ T.κ) * T.t) *
          Real.exp (-(2 * T.κdec) * treeLenCovOne T.m₀ (k + 1) Y)) ∧
      (∀ D : BgData S.G' N, XiCData S.G' (compWeight L 1) ν (k + 1) 1 T.t D →
        ObsMarkHalf S T.m₀ hp Ev D (obsDomains S (LocalCover.nbhdF T.m₀ y) T.m₀ k (LocalCover.fam T.m₀ y))
          (obsLab Lab₀ (Dsc.isDj_obsDomains hϱ hS y i))
          (lvCpsiG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2))))
          (cK2' d L N (famConst d L T.BG₂ T.κ) * T.t) (2 * T.κdec - 1) T.κ0
          (cK2' d L N (famConst d L T.BG₂ T.κ) * T.t / (lvCpsiG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2)))))
          (2 * T.κdec) (rootCube (m₀ := T.m₀) (blockIndex y)) ∧
        ObsRayIdentity S T.m₀ hp
          (fun ψh => svec (lvLowG d L N₁ T.m₁ k ϱ)
            (flFieldOne S.G' (lvLowG d L N₁ T.m₁ k ϱ) T.BG₂ T.κ 1 ν D
              (hatLift S.G' 1 ν S.hG' ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) D ψh)) y i) Ev D
          (obsDomains S (LocalCover.nbhdF T.m₀ y) T.m₀ k (LocalCover.fam T.m₀ y))) ∧
      ∃ (F₁ : DecParams S.G' × RawData d L (N₁ * L ^ T.m₁) (k + 1) N →
          (S.G'.Ω 1 × Fin N → ℂ) × (S.G'.Ω 1 → ℂ))
        (Sol : Dec2.DecParams (coverOf S.G') × Edat (lvLowG d L N₁ T.m₁ k ϱ) N → ((lvLowG d L N₁ T.m₁ k ϱ).Ω 1 × Fin N → ℂ) × ((lvLowG d L N₁ T.m₁ k ϱ).Ω 1 → ℂ)),
        (∀ (s : DecParams S.G') (D : BgData S.G' N), (∀ P, ‖s P‖ < Real.exp T.κ) →
          InUnionDomainC S.G' (bgC0 d L N) (c7 d L N T.BG T.κ) ν D → ∀ (φ : S.G'.Ω 1 × Fin N → ℂ)
            (α : S.G'.Ω 1 → ℂ), IsDecBg S.G' (compWeight L 1) ν (rho4 d L N T.BG T.κ) s D φ α →
            F₁ (s, rawOf D) = (φ, α)) ∧
        (∀ p : Dec2.DecParams (coverOf S.G') × Edat (lvLowG d L N₁ T.m₁ k ϱ) N, (∀ P, ‖p.1 P‖ < Real.exp T.κ) →
          StrictDataM (lvLowG d L N₁ T.m₁ k ϱ) N false (2 * (K4 d L N T.BG T.κ * (xiC1 d * T.t))) T.t p.2 →
            (Sol p).1 = dphi (lvLowG d L N₁ T.m₁ k ϱ) (Dec2.decG (coverOf S.G') (lvLowG d L N₁ T.m₁ k ϱ) (compWeight L 1) ν p.1) p.2.2.1 p.2.1
              (pertSource (lvLowG d L N₁ T.m₁ k ϱ) (compWeight L 1) p.2.2.2.1 p.2.2.2.2) (Sol p).2 ∧
            Dec2.DecFixed (coverOf S.G') (lvLowG d L N₁ T.m₁ k ϱ) (compWeight L 1) ν p.1 false p.2.2.1 p.2.1
              (pertSource (lvLowG d L N₁ T.m₁ k ϱ) (compWeight L 1) p.2.2.2.1 p.2.2.2.2) (Sol p).2 ∧
            Small (lvLowG d L N₁ T.m₁ k ϱ) (Sol p).2 (c6' d L N (famConst d L T.BG₂ T.κ) (gamma1 d / 8)) ∧
            Small (lvLowG d L N₁ T.m₁ k ϱ) (Sol p).2 (cK2' d L N (famConst d L T.BG₂ T.κ) * T.t) ∧
            SupBounds (lvLowG d L N₁ T.m₁ k ϱ) (Sol p).1 (cK2' d L N (famConst d L T.BG₂ T.κ) * T.t) ∧
            (∀ δα' : (lvLowG d L N₁ T.m₁ k ϱ).Ω 1 → ℂ, Small (lvLowG d L N₁ T.m₁ k ϱ) δα' (c6' d L N (famConst d L T.BG₂ T.κ) (gamma1 d / 8)) →
              Dec2.DecFixed (coverOf S.G') (lvLowG d L N₁ T.m₁ k ϱ) (compWeight L 1) ν p.1 false p.2.2.1 p.2.1
                (pertSource (lvLowG d L N₁ T.m₁ k ϱ) (compWeight L 1) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol p).2)) ∧
        Ev = evTerm (fun i : ParIdx S.G' (↑(LocalCover.nbhdF T.m₀ y) : Set (CTorus d L N₁ T.m₁ (k + 1))) => i.1.1) S.G' T.m₀
          (X1 S.G' T.m₀ k (LocalCover.fam T.m₀ y))
          (fun u s => siteFun S.G' (lvLowG d L N₁ T.m₁ k ϱ) y i
            (F₁ (extParams S.G' (↑(LocalCover.nbhdF T.m₀ y) : Set (CTorus d L N₁ T.m₁ (k + 1))) s, u.1))
            (Sol (extParams S.G' (↑(LocalCover.nbhdF T.m₀ y) : Set (CTorus d L N₁ T.m₁ (k + 1))) s,
              flEdat S.G' (lvLowG d L N₁ T.m₁ k ϱ) (F₁ (extParams S.G' (↑(LocalCover.nbhdF T.m₀ y) : Set (CTorus d L N₁ T.m₁ (k + 1))) s, u.1))
                u.1.1 (hatPsiF S.G' 1 ν S.hG' ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) F₁
                  (extParams S.G' (↑(LocalCover.nbhdF T.m₀ y) : Set (CTorus d L N₁ T.m₁ (k + 1))) s) u.1 u.2))).1
            (u.1, hatPsiF S.G' 1 ν S.hG' ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) F₁
              (extParams S.G' (↑(LocalCover.nbhdF T.m₀ y) : Set (CTorus d L N₁ T.m₁ (k + 1))) s) u.1 u.2)) := by
  subst hϱ
  have hS' : S = T.step k hk N₁ ν β p₁ := hS
  subst hS'
  have hν0 : 0 ≤ ν := hνpos.le
  have hr0 := Dsc.r_pos
  have hcψ0 := Dsc.cψ_pos
  have hq : p₁ / lvCpsiG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2))) ≤ 1 / 4 := by
    rw [div_le_iff₀ hcψ0]
    have : 0 < lvRG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2))) p₁ * p₁ := mul_pos hr0 hp
    nlinarith [Dsc.ray_margin]
  obtain ⟨hcov, hX₁, hopt, hΔ, hy⟩ := Dsc.covers.2 (y, i)
  obtain ⟨Ev, ha, hd, hb, hEv, hex⟩ := obsMarkHalves_of_sharpHat_param_rawY (T.step k hk N₁ ν β p₁) Dsc.core hk
    (isLevel_lvLowG hk) ((_ ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) hcψ0 T.large_block T.dom_margin
    T.coer_margin T.δc_small Dsc.fl_radius hcov hX₁ (hatConn_lvTopG T.hL)
    (rowInHat_lvG hk (dgSetting_lvG T.hd T.hL T.m₁_four hN hν0 hν)) hopt hΔ T.κ0_nonneg T.κdec_lower
    (by exact_mod_cast T.κ_lower) T.κ_one T.κ_log y hy i hp hq Lab₀ T.marks_κG_le T.κ0_ent
  refine ⟨Ev, ha, hd, fun Y u hu => ?_, hEv, hex⟩
  have := hb Y u hu
  rwa [treeLenCov_eq_treeLenCovOne (T.step k hk N₁ ν β p₁).hG' T.m₀ Y, show -2 * T.κdec = -(2 * T.κdec) by ring] at this


/-- General tower `T : StepTowerG d L N κmin` (block scale `T.m₀`, `b = β L^{k (d-2)}`); the fixed theorem `obsEv_fromTower` is its corollary.  **The one sharp-hat expansion at the tower.**  The family `Ev` of
`obsMarkHalves_of_sharpHat_param` at the shared tower (the call of `obsHker_param_fromTower`),
with its three clauses (analyticity, locality, decay with `treeLenCovOne`) and, for every datum of
`Ξ`, `ObsMarkHalf` and `ObsRayIdentity`.  The same `Ev` serves the kernel and the remainder. -/
theorem obsEv_fromTowerG {d L N : ℕ} [NeZero L] {κmin : ℝ} (T : StepTowerG d L N κmin)
    (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁] (ν β p₁ : ℝ) (hN : 5 < N₁)
    (hνpos : 0 < ν) (hν : ν * (L : ℝ) ^ (2 * (k + 1)) ≤ 1)
    (Dsc : StepScaleDataG T k hk N₁ ν β p₁)
    {ϱ : ℝ} (hϱ : ϱ = rhoSepG d L T.m₁) {S : StepSetting d L N₁ T.m₁ k N ϱ}
    (hS : S = hatStepKG T.hN k T.m₁ ϱ hk ν β p₁ T.δ)
    (hp : 0 < S.p₁) (y : CTorus d L N₁ T.m₁ (k + 1)) (i : Fin N)
    {Lb₀ : Type} (Lab₀ : CubeLabels (d := d) (L := L) (N₁ := N₁) (m₁ := T.m₁) (K := k + 1) T.m₀
      (k + 1) Set.univ Lb₀) :
    ∃ Ev : Set (CTorus d L N₁ T.m₁ (k + 1)) →
        RawData d L (N₁ * L ^ T.m₁) (k + 1) N × (unitPts S.G' × Fin N → ℂ) → ℂ,
      (∀ Y, AnalyticOnNhd ℂ (Ev Y) (XiCRaw S.G' (compWeight L 1) ν (k + 1) 1 T.t ×ˢ
          {ψh : unitPts S.G' × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ lvCpsiG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2)))})) ∧
      (∀ Y, ∀ u ∈ XiCRaw S.G' (compWeight L 1) ν (k + 1) 1 T.t ×ˢ
          {ψh : unitPts S.G' × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ lvCpsiG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2)))},
        ∀ u' ∈ XiCRaw S.G' (compWeight L 1) ν (k + 1) 1 T.t ×ˢ
          {ψh : unitPts S.G' × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ lvCpsiG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2)))},
        AgHatDir S.hG' Y u u' → Ev Y u = Ev Y u') ∧
      (∀ Y, ∀ u ∈ XiCRaw S.G' (compWeight L 1) ν (k + 1) 1 T.t ×ˢ
          {ψh : unitPts S.G' × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ lvCpsiG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2)))},
        ‖Ev Y u‖ ≤ (cK2' d L N (famConst d L T.BG₂ T.κ) * T.t) *
          Real.exp (-(2 * T.κdec) * treeLenCovOne T.m₀ (k + 1) Y)) ∧
      (∀ D : BgData S.G' N, XiCData S.G' (compWeight L 1) ν (k + 1) 1 T.t D →
        ObsMarkHalf S T.m₀ hp Ev D (obsDomains S (LocalCover.nbhdF T.m₀ y) T.m₀ k (LocalCover.fam T.m₀ y))
          (obsLab Lab₀ (Dsc.isDj_obsDomains hϱ hS y i))
          (lvCpsiG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2))))
          (cK2' d L N (famConst d L T.BG₂ T.κ) * T.t) (2 * T.κdec - 1) T.κ0
          (cK2' d L N (famConst d L T.BG₂ T.κ) * T.t / (lvCpsiG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2)))))
          (2 * T.κdec) (rootCube (m₀ := T.m₀) (blockIndex y)) ∧
        ObsRayIdentity S T.m₀ hp
          (fun ψh => svec (lvLowG d L N₁ T.m₁ k ϱ)
            (flFieldOne S.G' (lvLowG d L N₁ T.m₁ k ϱ) T.BG₂ T.κ 1 ν D
              (hatLift S.G' 1 ν S.hG' ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) D ψh)) y i) Ev D
          (obsDomains S (LocalCover.nbhdF T.m₀ y) T.m₀ k (LocalCover.fam T.m₀ y))) := by
  obtain ⟨Ev, ha, hd, hb, hEv, -⟩ := obsEv_fromTower_rawYG T k hk N₁ ν β p₁ hN hνpos hν Dsc hϱ hS hp y i Lab₀
  exact ⟨Ev, ha, fun Y u hu u' hu' h => hd Y u hu u' hu' (agreeOn_mono (fun x hx => Or.inl hx) h.1) h.2,
    hb, hEv⟩

end EvG

/-- **The one sharp-hat expansion at the tower, exact locality.**  The statement of
`obsEv_fromTower` with the locality clause for raw data agreeing on `Y` itself and hat variables
agreeing at the unit points of `Y`; `obsEv_fromTower` is its corollary.  The family `Ev` of
`obsMarkHalves_of_sharpHat_param_rawY` at the shared tower (the call of `obsHker_param_fromTower`),
with its three clauses (analyticity, locality, decay with `treeLenCovOne`) and, for every datum of
`Ξ`, `ObsMarkHalf` and `ObsRayIdentity`.  The same `Ev` serves the kernel and the remainder. -/
theorem obsEv_fromTower_rawY {κmin : ℝ} (T : StepTower κmin)
    (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁] (ν β p₁ : ℝ) (hN : 5 < N₁)
    (hνpos : 0 < ν) (hν : ν * 3 ^ (2 * (k + 1)) ≤ 1)
    (Dsc : StepScaleData T k hk N₁ ν β p₁)
    (hp : 0 < (T.step k hk N₁ ν β p₁).p₁) (y : CTorus 3 3 N₁ T.m₁ (k + 1)) (i : Fin 2)
    {Lb₀ : Type} (Lab₀ : CubeLabels (d := 3) (L := 3) (N₁ := N₁) (m₁ := T.m₁) (K := k + 1) 1
      (k + 1) Set.univ Lb₀) :
    let S := T.step k hk N₁ ν β p₁;
    ∃ Ev : Set (CTorus 3 3 N₁ T.m₁ (k + 1)) →
        RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2 × (unitPts S.G' × Fin 2 → ℂ) → ℂ,
      (∀ Y, AnalyticOnNhd ℂ (Ev Y) (XiCRaw S.G' (compWeight 3 1) ν (k + 1) 1 T.t ×ˢ
          {ψh : unitPts S.G' × Fin 2 → ℂ | ∀ p, ‖ψh p‖ ≤ lvCpsi T.κ T.t (β * 3 ^ k)})) ∧
      (∀ Y, ∀ u ∈ XiCRaw S.G' (compWeight 3 1) ν (k + 1) 1 T.t ×ˢ
          {ψh : unitPts S.G' × Fin 2 → ℂ | ∀ p, ‖ψh p‖ ≤ lvCpsi T.κ T.t (β * 3 ^ k)},
        ∀ u' ∈ XiCRaw S.G' (compWeight 3 1) ν (k + 1) 1 T.t ×ˢ
          {ψh : unitPts S.G' × Fin 2 → ℂ | ∀ p, ‖ψh p‖ ≤ lvCpsi T.κ T.t (β * 3 ^ k)},
        agreeOn Y u.1 u'.1 → (∀ y ∈ Y, ∀ i, u.2 (unitPt S.hG' y, i) = u'.2 (unitPt S.hG' y, i)) →
        Ev Y u = Ev Y u') ∧
      (∀ Y, ∀ u ∈ XiCRaw S.G' (compWeight 3 1) ν (k + 1) 1 T.t ×ˢ
          {ψh : unitPts S.G' × Fin 2 → ℂ | ∀ p, ‖ψh p‖ ≤ lvCpsi T.κ T.t (β * 3 ^ k)},
        ‖Ev Y u‖ ≤ (cK2' 3 3 2 (famConst 3 3 T.BG₂ T.κ) * T.t) *
          Real.exp (-(2 * T.κdec) * treeLenCovOne 1 (k + 1) Y)) ∧
      (∀ D : BgData S.G' 2, XiCData S.G' (compWeight 3 1) ν (k + 1) 1 T.t D →
        ObsMarkHalf S 1 hp Ev D (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y))
          (obsLab Lab₀ (obsDomains_isDj (X₁f := LocalCover.nbhdF 1 y) S le_rfl
            (Dsc.covers.2 (y, i)).1 (Dsc.covers.2 (y, i)).2.2.1))
          (lvCpsi T.κ T.t (β * 3 ^ k))
          (cK2' 3 3 2 (famConst 3 3 T.BG₂ T.κ) * T.t) (2 * T.κdec - 1) T.κ0
          (cK2' 3 3 2 (famConst 3 3 T.BG₂ T.κ) * T.t / (lvCpsi T.κ T.t (β * 3 ^ k)))
          (2 * T.κdec) (rootCube (m₀ := 1) (blockIndex y)) ∧
        ObsRayIdentity S 1 hp
          (fun ψh => svec (lvLow N₁ T.m₁ k (rhoSep T.m₁))
            (flFieldOne S.G' (lvLow N₁ T.m₁ k (rhoSep T.m₁)) T.BG₂ T.κ 1 ν D
              (hatLift S.G' 1 ν S.hG' ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) D ψh)) y i) Ev D
          (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y))) := by
  intro S
  have e : β * ((3 : ℕ) : ℝ) ^ (k * (3 - 2)) = β * 3 ^ k := by norm_num
  have G := obsEv_fromTower_rawYG T.toG k hk N₁ ν β p₁ hN hνpos (by simpa using hν)
    (T.scaleDataG_of_fixed Dsc) (ϱ := rhoSep T.m₁) (rhoSepG_three _).symm
    (S := T.step k hk N₁ ν β p₁) rfl hp y i Lab₀
  rw [e] at G
  obtain ⟨Ev, ha, hd, hb, hEv, -⟩ := G
  exact ⟨Ev, ha, hd, hb, hEv⟩


/-- **The one sharp-hat expansion at the tower.**  The family `Ev` of
`obsMarkHalves_of_sharpHat_param` at the shared tower (the call of `obsHker_param_fromTower`),
with its three clauses (analyticity, locality, decay with `treeLenCovOne`) and, for every datum of
`Ξ`, `ObsMarkHalf` and `ObsRayIdentity`.  The same `Ev` serves the kernel and the remainder. -/
theorem obsEv_fromTower {κmin : ℝ} (T : StepTower κmin)
    (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁] (ν β p₁ : ℝ) (hN : 5 < N₁)
    (hνpos : 0 < ν) (hν : ν * 3 ^ (2 * (k + 1)) ≤ 1)
    (Dsc : StepScaleData T k hk N₁ ν β p₁)
    (hp : 0 < (T.step k hk N₁ ν β p₁).p₁) (y : CTorus 3 3 N₁ T.m₁ (k + 1)) (i : Fin 2)
    {Lb₀ : Type} (Lab₀ : CubeLabels (d := 3) (L := 3) (N₁ := N₁) (m₁ := T.m₁) (K := k + 1) 1
      (k + 1) Set.univ Lb₀) :
    let S := T.step k hk N₁ ν β p₁;
    ∃ Ev : Set (CTorus 3 3 N₁ T.m₁ (k + 1)) →
        RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2 × (unitPts S.G' × Fin 2 → ℂ) → ℂ,
      (∀ Y, AnalyticOnNhd ℂ (Ev Y) (XiCRaw S.G' (compWeight 3 1) ν (k + 1) 1 T.t ×ˢ
          {ψh : unitPts S.G' × Fin 2 → ℂ | ∀ p, ‖ψh p‖ ≤ lvCpsi T.κ T.t (β * 3 ^ k)})) ∧
      (∀ Y, ∀ u ∈ XiCRaw S.G' (compWeight 3 1) ν (k + 1) 1 T.t ×ˢ
          {ψh : unitPts S.G' × Fin 2 → ℂ | ∀ p, ‖ψh p‖ ≤ lvCpsi T.κ T.t (β * 3 ^ k)},
        ∀ u' ∈ XiCRaw S.G' (compWeight 3 1) ν (k + 1) 1 T.t ×ˢ
          {ψh : unitPts S.G' × Fin 2 → ℂ | ∀ p, ‖ψh p‖ ≤ lvCpsi T.κ T.t (β * 3 ^ k)},
        AgHatDir S.hG' Y u u' → Ev Y u = Ev Y u') ∧
      (∀ Y, ∀ u ∈ XiCRaw S.G' (compWeight 3 1) ν (k + 1) 1 T.t ×ˢ
          {ψh : unitPts S.G' × Fin 2 → ℂ | ∀ p, ‖ψh p‖ ≤ lvCpsi T.κ T.t (β * 3 ^ k)},
        ‖Ev Y u‖ ≤ (cK2' 3 3 2 (famConst 3 3 T.BG₂ T.κ) * T.t) *
          Real.exp (-(2 * T.κdec) * treeLenCovOne 1 (k + 1) Y)) ∧
      (∀ D : BgData S.G' 2, XiCData S.G' (compWeight 3 1) ν (k + 1) 1 T.t D →
        ObsMarkHalf S 1 hp Ev D (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y))
          (obsLab Lab₀ (obsDomains_isDj (X₁f := LocalCover.nbhdF 1 y) S le_rfl
            (Dsc.covers.2 (y, i)).1 (Dsc.covers.2 (y, i)).2.2.1))
          (lvCpsi T.κ T.t (β * 3 ^ k))
          (cK2' 3 3 2 (famConst 3 3 T.BG₂ T.κ) * T.t) (2 * T.κdec - 1) T.κ0
          (cK2' 3 3 2 (famConst 3 3 T.BG₂ T.κ) * T.t / (lvCpsi T.κ T.t (β * 3 ^ k)))
          (2 * T.κdec) (rootCube (m₀ := 1) (blockIndex y)) ∧
        ObsRayIdentity S 1 hp
          (fun ψh => svec (lvLow N₁ T.m₁ k (rhoSep T.m₁))
            (flFieldOne S.G' (lvLow N₁ T.m₁ k (rhoSep T.m₁)) T.BG₂ T.κ 1 ν D
              (hatLift S.G' 1 ν S.hG' ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) D ψh)) y i) Ev D
          (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y))) := by
  obtain ⟨Ev, ha, hd, hb, hEv⟩ := obsEv_fromTower_rawY T k hk N₁ ν β p₁ hN hνpos hν Dsc hp y i Lab₀
  exact ⟨Ev, ha, fun Y u hu u' hu' h => hd Y u hu u' hu' (agreeOn_mono (fun x hx => Or.inl hx) h.1) h.2,
    hb, hEv⟩

/-- The constant `Q · t` of the decay of the sharp-hat terms is positive (general tower). -/
theorem cK2'_famConst_mul_t_posG {d L N : ℕ} [NeZero L] {κmin : ℝ} (T : StepTowerG d L N κmin) :
    0 < cK2' d L N (famConst d L T.BG₂ T.κ) * T.t :=
  mul_pos (cK2'_pos_of T.fam_nonneg) T.t_pos

/-- The constant `Q · t` of the decay of the sharp-hat terms is positive. -/
theorem cK2'_famConst_mul_t_pos {κmin : ℝ} (T : StepTower κmin) (k : ℕ) (hk : 1 ≤ k)
    (N₁ : ℕ) [NeZero N₁] (ν β p₁ : ℝ) (Dsc : StepScaleData T k hk N₁ ν β p₁) :
    0 < cK2' 3 3 2 (famConst 3 3 T.BG₂ T.κ) * T.t :=
  (fun _ => cK2'_famConst_mul_t_posG T.toG) Dsc

section TowerG

variable {d L N : ℕ} [NeZero L] {κmin : ℝ} (T : StepTowerG d L N κmin) (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁]
  (ν β p₁ : ℝ) (Dsc : StepScaleDataG T k hk N₁ ν β p₁)
  {ϱ : ℝ} (S : StepSetting d L N₁ T.m₁ k N ϱ) (hS : S = hatStepKG T.hN k T.m₁ ϱ hk ν β p₁ T.δ)
  (hp : 0 < S.p₁) (y : CTorus d L N₁ T.m₁ (k + 1)) (h3N : L ^ T.m₀ ∣ N₁)
  {Lb : Type} [Fintype Lb]
  (Lab : CubeLabels (d := d) (L := L) (N₁ := N₁) (m₁ := T.m₁) (K := k + 1) T.m₀ (k + 1)
    Set.univ Lb) {εH : ℝ} (hεH : 0 < εH) {Kc : ℝ}
  (Aact : physParam N S → ℂ → LabelAct Lab (S.blockSplit T.m₀ hp).Ωb εH (2 * T.κdec - 1) T.κ0 Kc)
  (hdj : ∀ Y ∈ obsDomains S (LocalCover.nbhdF T.m₀ y) T.m₀ k (LocalCover.fam T.m₀ y), IsDj T.m₀ (k + 1) Y)
  {Kobs : ℝ} (hK : Kc + Kc + K0 d L T.κ0 + K0 d L T.κ0 ≤ Kobs) (Rg : ℝ) (hR : 0 ≤ Rg)

include Dsc hS in
/-- General tower `T : StepTowerG d L N κmin` (block scale `T.m₀`, `b = β L^{k (d-2)}`); the fixed theorem `obsFamilies_of_Ev` is its corollary.  **The first-order and remainder families, and the analyticity of the coefficient, for any
sharp-hat family `Ev`** (its three clauses as in `obsEv_fromTower`).  The activity is
`tiltActObs … (e, t, σ)` on the labels `obsLab (Lab.sum Lab) hdj`, `V = physVq … q`,
`𝒰 = ball 0 (3/2)`, carrier `physCarrier S T.m₀ hp`.

Numerical hypothesis carried: `hε`, the amplitude of the tilted extension is at most
`stepTheta d L Kobs (2 κdec - 1) κ0 κ'`; the other rates are the tower fields
(`marks_hκ0`, `marks_hκ'`, `marks_hκ`, `marks_κG_le`, `marks_K0_pos`). -/
theorem obsFamilies_of_EvG (hϱ : ϱ = rhoSepG d L T.m₁) (hνpos : 0 < ν) (hν : ν * (L : ℝ) ^ (2 * (k + 1)) ≤ 1) {q : ℝ}
    (hhol : ∀ y', ∀ Φ ∈ physCarrier S T.m₀ hp, AnalyticOnNhd ℂ (fun r : physParam N S × ℂ =>
      (tiltActObs Aact (show L ^ T.m₀ ∣ N₁ by simpa using h3N) T.κ0_ent hεH.le hdj hK Rg hR
        (ball (0 : ℂ) (3 / 2)) r.1 r.2 1).H y' Φ)
      (physVq S S.a₁ S.ν T.t q ×ˢ ball (0 : ℂ) (3 / 2)))
    (hcont : ∀ y', ∀ θ ∈ physVq S S.a₁ S.ν T.t q, ∀ u ∈ ball (0 : ℂ) (3 / 2),
      ContinuousOn ((tiltActObs Aact (show L ^ T.m₀ ∣ N₁ by simpa using h3N) T.κ0_ent hεH.le hdj hK
        Rg hR (ball (0 : ℂ) (3 / 2)) θ u 1).H y') (physCarrier S T.m₀ hp))
    (Ev : Set (CTorus d L N₁ T.m₁ (k + 1)) →
        RawData d L (N₁ * L ^ T.m₁) (k + 1) N × (unitPts S.G' × Fin N → ℂ) → ℂ)
    (ha : ∀ Y, AnalyticOnNhd ℂ (Ev Y) (XiCRaw S.G' (compWeight L 1) ν (k + 1) 1 T.t ×ˢ
          {ψh : unitPts S.G' × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ lvCpsiG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2)))}))
    (hb : ∀ Y, ∀ u ∈ XiCRaw S.G' (compWeight L 1) ν (k + 1) 1 T.t ×ˢ
          {ψh : unitPts S.G' × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ lvCpsiG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2)))},
        ‖Ev Y u‖ ≤ (cK2' d L N (famConst d L T.BG₂ T.κ) * T.t) *
          Real.exp (-(2 * T.κdec) * treeLenCovOne T.m₀ (k + 1) Y)) :
    (∀ m : ObsMarkIdx S, Nonempty (ParamMarkFamily (S.blockSplit T.m₀ hp).μ
      (obsLab (Lab.sum Lab) hdj)
      (fun θ t => tiltActObs Aact (show L ^ T.m₀ ∣ N₁ by simpa using h3N) T.κ0_ent hεH.le hdj hK
        Rg hR (ball (0 : ℂ) (3 / 2)) θ t 1)
      (fun _ : Unit => obsY1 T.m₀ S (Lb ⊕ Lb) (obsDomains S (LocalCover.nbhdF T.m₀ y) T.m₀ k
        (LocalCover.fam T.m₀ y)) m)
      (fun _ _ _ => blockMarkC S T.m₀ hp m.1 m.2) (2 * T.κdec - 1)
      (fun _ => S.p₁ * Real.exp ((2 * T.κdec - 1) * (obsLab (Lab.sum Lab) hdj).dl
        (obsY1 T.m₀ S (Lb ⊕ Lb) (obsDomains S (LocalCover.nbhdF T.m₀ y) T.m₀ k (LocalCover.fam T.m₀ y)) m)))
      (physVq S S.a₁ S.ν T.t q) (ball (0 : ℂ) (3 / 2)) (physCarrier S T.m₀ hp))) ∧
    Nonempty (ParamMarkFamily (S.blockSplit T.m₀ hp).μ (obsLab (Lab.sum Lab) hdj)
      (fun θ t => tiltActObs Aact (show L ^ T.m₀ ∣ N₁ by simpa using h3N) T.κ0_ent hεH.le hdj hK
        Rg hR (ball (0 : ℂ) (3 / 2)) θ t 1)
      (obsRemLab (obsDomains S (LocalCover.nbhdF T.m₀ y) T.m₀ k (LocalCover.fam T.m₀ y))
        (fun Y => Sum.inl (Sum.inr Y))
        (obsY0 T.m₀ (Lb ⊕ Lb) (obsDomains S (LocalCover.nbhdF T.m₀ y) T.m₀ k (LocalCover.fam T.m₀ y))
          (rootCube (m₀ := T.m₀) (blockIndex y))))
      (obsGrFam S T.m₀ hp Ev (obsDomains S (LocalCover.nbhdF T.m₀ y) T.m₀ k (LocalCover.fam T.m₀ y))
        (XiCRaw S.G' (compWeight L 1) ν (k + 1) 1 T.t)) (2 * T.κdec - 1)
      (fun _ => 8 * (cK2' d L N (famConst d L T.BG₂ T.κ) * T.t) *
        (S.p₁ / lvCpsiG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2)))) ^ 2)
      (physVq S S.a₁ S.ν T.t q) (ball (0 : ℂ) (3 / 2)) (physCarrier S T.m₀ hp)) := by
  subst hS
  have hH : BgHyp d L (k + 1) ϱ (compWeight L (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ).a₁)
      (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ).ν := by
    subst hϱ
    exact bgHyp_lvG (k := k) T.hd T.hL (bgR0_le_rhoSepG T.m₁ T.hd T.hL) hνpos.le hν
  have hV := isOpen_physVq (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ) (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ).a₁
    (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ).ν T.t q hH
  have hcψ := Dsc.cψ_pos
  have hq : p₁ / lvCpsiG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2))) ≤ 1 / 4 := by
    rw [div_le_iff₀ hcψ]
    have : 0 < lvRG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2))) p₁ * p₁ := mul_pos Dsc.r_pos hp
    nlinarith [Dsc.ray_margin]
  have hC0 := cK2'_famConst_mul_t_posG T
  refine ⟨fun m => ?_, ?_⟩
  · exact nonempty_paramMarkFamily_blockMarkC hV hhol hcont m.1 m.2 _ _
  · have hH' : BgHyp d L (k + 1) ϱ (compWeight L 1) ν := hH
    have hsub : physVq (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ) (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ).a₁
        (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ).ν T.t q ⊆ physV (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ) 1 ν T.t :=
      physVq_subset _ _ _ _ _
    exact nonempty_paramMarkFamily_obsGrFam (a₁ := 1) (ν := ν) (eps := T.t) hH' hV hsub hcψ hq
      (fun Y _ => ha Y) hC0 (fun Y _ => hb Y) _ _ (fun Y => rfl) T.marks_κG_le hhol hcont

set_option quotPrecheck false in
local notation "𝒴ₒ" => obsDomains S (LocalCover.nbhdF T.m₀ y) T.m₀ k (LocalCover.fam T.m₀ y)
set_option quotPrecheck false in
local notation "Actₒ" => fun (θ : physParam N S) (t σ : ℂ) =>
  tiltActObs Aact (show L ^ T.m₀ ∣ N₁ by simpa using h3N) T.κ0_ent hεH.le hdj hK Rg hR
    (ball (0 : ℂ) (3 / 2)) θ t σ

include Dsc hS in
/-- General tower `T : StepTowerG d L N κmin` (block scale `T.m₀`, `b = β L^{k (d-2)}`); the fixed theorem `obsCoeffParam_analytic_of_Ev` is its corollary.  **The three parts of the coefficient of the observable and their sum are analytic on
`physVq`**, for the one sharp-hat family `Ev` of the kernel and the remainder: for every finite
set `T'` of cubes, with `μ = (S.blockSplit T.m₀ hp).μ`, the kernel `θ ↦ obsHker 𝒴 (hatCoeff (Ev ·)
(θ.1) e_m) 1`,

* each first-order term `θ ↦ markIntTerm μ (Act θ) (obsY1 m) (blockMarkC m) S'` is analytic,
* `θ ↦ kernelMarkSum (kernel at θ.1) (first-order terms) T'` is analytic,
* `θ ↦ gsumCoeff μ _ (Act θ · 1) _ (obsGrFam θ) T'` (the remainder) is analytic,
* `θ ↦ obsCoeffParam … θ T'` (their sum) is analytic.

Numerical hypothesis carried: `hε`, the amplitude of the tilted extension is below
`stepTheta d L Kobs (2 κdec - 1) κ0 κ'`. -/
theorem obsCoeffParam_analytic_of_EvG (hϱ : ϱ = rhoSepG d L T.m₁) (hνpos : 0 < ν) (hν : ν * (L : ℝ) ^ (2 * (k + 1)) ≤ 1)
    {q : ℝ} (hRg : 1 < Rg) (hKc : K0 d L T.κ0 + 1 ≤ Kc)
    (hhol : ∀ y', ∀ Φ ∈ physCarrier S T.m₀ hp, AnalyticOnNhd ℂ (fun r : physParam N S × ℂ =>
      (tiltActObs Aact (show L ^ T.m₀ ∣ N₁ by simpa using h3N) T.κ0_ent hεH.le hdj hK Rg hR
        (ball (0 : ℂ) (3 / 2)) r.1 r.2 1).H y' Φ)
      (physVq S S.a₁ S.ν T.t q ×ˢ ball (0 : ℂ) (3 / 2)))
    (hcont : ∀ y', ∀ θ ∈ physVq S S.a₁ S.ν T.t q, ∀ u ∈ ball (0 : ℂ) (3 / 2),
      ContinuousOn ((tiltActObs Aact (show L ^ T.m₀ ∣ N₁ by simpa using h3N) T.κ0_ent hεH.le hdj hK
        Rg hR (ball (0 : ℂ) (3 / 2)) θ u 1).H y') (physCarrier S T.m₀ hp))
    (hε : Rg * max (εH + εH) εH ≤ stepTheta d L Kobs (2 * T.κdec - 1) T.κ0 T.κ')
    (Ev : Set (CTorus d L N₁ T.m₁ (k + 1)) →
        RawData d L (N₁ * L ^ T.m₁) (k + 1) N × (unitPts S.G' × Fin N → ℂ) → ℂ)
    (ha : ∀ Y, AnalyticOnNhd ℂ (Ev Y) (XiCRaw S.G' (compWeight L 1) ν (k + 1) 1 T.t ×ˢ
          {ψh : unitPts S.G' × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ lvCpsiG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2)))}))
    (hd : ∀ Y, ∀ u ∈ XiCRaw S.G' (compWeight L 1) ν (k + 1) 1 T.t ×ˢ
          {ψh : unitPts S.G' × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ lvCpsiG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2)))},
        ∀ u' ∈ XiCRaw S.G' (compWeight L 1) ν (k + 1) 1 T.t ×ˢ
          {ψh : unitPts S.G' × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ lvCpsiG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2)))},
        AgHatDir S.hG' Y u u' → Ev Y u = Ev Y u')
    (hb : ∀ Y, ∀ u ∈ XiCRaw S.G' (compWeight L 1) ν (k + 1) 1 T.t ×ˢ
          {ψh : unitPts S.G' × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ lvCpsiG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2)))},
        ‖Ev Y u‖ ≤ (cK2' d L N (famConst d L T.BG₂ T.κ) * T.t) *
          Real.exp (-(2 * T.κdec) * treeLenCovOne T.m₀ (k + 1) Y))
    (T' : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := T.m₁) (K := k + 1) T.m₀ (k + 1)
      Set.univ)) :
    (∀ (m : ObsMarkIdx S) (S' : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := T.m₁)
        (K := k + 1) T.m₀ (k + 1) Set.univ)),
      AnalyticOnNhd ℂ (fun θ => markIntTerm (S.blockSplit T.m₀ hp).μ (Actₒ θ)
        (obsY1 T.m₀ S (Lb ⊕ Lb) 𝒴ₒ m) (blockMarkC S T.m₀ hp m.1 m.2) S')
        (physVq S S.a₁ S.ν T.t q)) ∧
    AnalyticOnNhd ℂ (fun θ => kernelMarkSum
      (fun m T'' => obsHker 𝒴ₒ (fun Y => hatCoeff (Ev Y)
        (θ.1 : RawData d L (N₁ * L ^ T.m₁) (k + 1) N) (obsUnitVec S m)) T.m₀ T'')
      (fun m S' => markIntTerm (S.blockSplit T.m₀ hp).μ (Actₒ θ) (obsY1 T.m₀ S (Lb ⊕ Lb) 𝒴ₒ m)
        (blockMarkC S T.m₀ hp m.1 m.2) S') T') (physVq S S.a₁ S.ν T.t q) ∧
    AnalyticOnNhd ℂ (fun θ => gsumCoeff (S.blockSplit T.m₀ hp).μ (obsLab (Lab.sum Lab) hdj)
      (fun t => Actₒ θ t 1)
      (obsRemLab 𝒴ₒ (fun Y => Sum.inl (Sum.inr Y))
        (obsY0 T.m₀ (Lb ⊕ Lb) 𝒴ₒ (rootCube (m₀ := T.m₀) (blockIndex y))))
      (obsGrFam S T.m₀ hp Ev 𝒴ₒ (XiCRaw S.G' (compWeight L 1) ν (k + 1) 1 T.t) θ) T')
      (physVq S S.a₁ S.ν T.t q) ∧
    AnalyticOnNhd ℂ (fun θ => obsCoeffParam (S.blockSplit T.m₀ hp).μ Actₒ
      (fun m => obsY1 T.m₀ S (Lb ⊕ Lb) 𝒴ₒ m) (fun m => blockMarkC S T.m₀ hp m.1 m.2)
      (fun θ m T'' => obsHker 𝒴ₒ (fun Y => hatCoeff (Ev Y)
        (θ.1 : RawData d L (N₁ * L ^ T.m₁) (k + 1) N) (obsUnitVec S m)) T.m₀ T'')
      (obsRemLab 𝒴ₒ (fun Y => Sum.inl (Sum.inr Y))
        (obsY0 T.m₀ (Lb ⊕ Lb) 𝒴ₒ (rootCube (m₀ := T.m₀) (blockIndex y))))
      (fun θ => obsGrFam S T.m₀ hp Ev 𝒴ₒ (XiCRaw S.G' (compWeight L 1) ν (k + 1) 1 T.t) θ) θ T')
      (physVq S S.a₁ S.ν T.t q) := by
  obtain ⟨hfam1, hfamr⟩ := obsFamilies_of_EvG T k hk N₁ ν β p₁ Dsc S hS hp y h3N Lab hεH Aact hdj
    hK Rg hR hϱ hνpos hν hhol hcont Ev ha hb
  subst hS
  have hcψ := Dsc.cψ_pos
  have hC0 := cK2'_famConst_mul_t_posG T
  have hq : p₁ / lvCpsiG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2))) ≤ 1 / 4 := by
    rw [div_le_iff₀ hcψ]
    have : 0 < lvRG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2))) p₁ * p₁ := mul_pos Dsc.r_pos hp
    nlinarith [Dsc.ray_margin]
  have hN3 : L ^ T.m₀ ∣ N₁ := by simpa using h3N
  have hkernel : ∀ (m : ObsMarkIdx (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ))
      (T'' : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := T.m₁) (K := k + 1) T.m₀ (k + 1)
        Set.univ)),
      AnalyticOnNhd ℂ (fun θ : physParam N (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ) => obsHker
        (obsDomains (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ) (LocalCover.nbhdF T.m₀ y) T.m₀ k (LocalCover.fam T.m₀ y))
        (fun Y => hatCoeff (Ev Y) (θ.1 : RawData d L (N₁ * L ^ T.m₁) (k + 1) N)
          (obsUnitVec (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ) m)) T.m₀ T'')
        (physVq (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ) (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ).a₁
          (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ).ν T.t q) := by
    intro m T''
    have hk1 := obsHker_param_of_Ev (S := T.step k hk N₁ ν β p₁) (m₀ := T.m₀)
      (A := XiCRaw (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ).G' (compWeight L 1) ν (k + 1) 1 T.t)
      (cψ := lvCpsiG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2)))) (B := cK2' d L N (famConst d L T.BG₂ T.κ) * T.t)
      (κdec := T.κdec) hcψ hC0.le (by linarith [T.marks_κdec_nonneg]) Ev hd
      (fun Y u hu => by
        have := hb Y u hu
        rwa [← treeLenCov_eq_treeLenCovOne (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ).hG' T.m₀ Y,
          show -(2 * T.κdec) = -2 * T.κdec by ring] at this)
      ha _ hN3 hdj m T''
    exact analyticOnNhd_comp_rawFst hk1.1 (fun θ hθ => hθ.1.1)
  have hK0 := T.marks_K0_pos
  have hεpos : 0 < Rg * max (εH + εH) εH :=
    mul_pos (by linarith) (lt_of_lt_of_le (by linarith) (le_max_left _ _))
  have hpc : 0 < p₁ / lvCpsiG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2))) := div_pos hp hcψ
  have hall := obsCoeffParam_analyticOnNhd (E := physParam N (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ))
    ((hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ).blockSplit T.m₀ hp).μ hN3 (le_refl (k + 1)) isPiUnion_univ_K
    (Lab := obsLab (Lab.sum Lab) hdj)
    (Aact := fun θ t σ => tiltActObs Aact hN3 T.κ0_ent hεH.le hdj hK Rg hR
      (ball (0 : ℂ) (3 / 2)) θ t σ)
    (V := physVq (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ) (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ).a₁
      (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ).ν T.t q)
    (𝒰 := ball (0 : ℂ) (3 / 2)) (Q := physCarrier (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ) T.m₀ hp)
    (fun m => obsY1 T.m₀ (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ) (Lb ⊕ Lb)
      (obsDomains (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ) (LocalCover.nbhdF T.m₀ y) T.m₀ k (LocalCover.fam T.m₀ y)) m)
    (fun m => blockMarkC (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ) T.m₀ hp m.1 m.2)
    (fun m => (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ).p₁ * Real.exp ((2 * T.κdec - 1) *
      (obsLab (Lab.sum Lab) hdj).dl (obsY1 T.m₀ (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ) (Lb ⊕ Lb)
        (obsDomains (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ) (LocalCover.nbhdF T.m₀ y) T.m₀ k (LocalCover.fam T.m₀ y)) m)))
    (fun m => (hfam1 m).some)
    (obsRemLab (obsDomains (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ) (LocalCover.nbhdF T.m₀ y) T.m₀ k
        (LocalCover.fam T.m₀ y)) (fun Y => Sum.inl (Sum.inr Y))
      (obsY0 T.m₀ (Lb ⊕ Lb) (obsDomains (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ) (LocalCover.nbhdF T.m₀ y) T.m₀ k
        (LocalCover.fam T.m₀ y)) (rootCube (m₀ := T.m₀) (blockIndex y))))
    (fun θ => obsGrFam (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ) T.m₀ hp Ev (obsDomains (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ)
      (LocalCover.nbhdF T.m₀ y) T.m₀ k (LocalCover.fam T.m₀ y))
      (XiCRaw (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ).G' (compWeight L 1) ν (k + 1) 1 T.t) θ)
    (fun _ => 8 * (cK2' d L N (famConst d L T.BG₂ T.κ) * T.t) *
        (p₁ / lvCpsiG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2)))) ^ 2) hfamr.some
    (fun θ m T'' => obsHker (obsDomains (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ) (LocalCover.nbhdF T.m₀ y) T.m₀ k
      (LocalCover.fam T.m₀ y)) (fun Y => hatCoeff (Ev Y)
        (θ.1 : RawData d L (N₁ * L ^ T.m₁) (k + 1) N)
        (obsUnitVec (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ) m)) T.m₀ T'') (fun m T'' => hkernel m T'')
    T.marks_hκ0 (by linarith)
    hεpos (fun m => mul_pos hp (Real.exp_pos _)) (fun _ => by positivity) T.marks_hκ'
    T.marks_hκG T.marks_hκ (by unfold stepTheta at hε; exact hε) T'
  exact hall

include Dsc hS in
/-- General tower `T : StepTowerG d L N κmin` (block scale `T.m₀`, `b = β L^{k (d-2)}`); the fixed theorem `obsCoeffParam_norm_le_of_Ev` is its corollary.  **The uniform bounds of the three parts and of their sum on `physVq`**, with the constants of
the fixed-parameter bounds (`norm_markIntTerm_le`, `norm_gsumCoeff_le`, `norm_kernelMarkSum_le`),
for the sharp-hat family `Ev` (the clauses and `hD` as given by `obsEv_fromTower`).  With
`C₀ = Q t`, `c_ψ = lvCpsi`, `F_r = 8 C₀ (p₁/c_ψ)²`, `κ' = T.κ'`, `n_* = 2 · 3^{3(1+m₁+1)}`:

* the first-order term: `≤ CPE · p₁ · e^{-κ' dExt S'} / R_g`;
* the remainder coefficient: `≤ CPE · (∑_r F_r e^{-κ₀ 𝗱(y_r)}) · e^{-κ' dExt T'}`;
* the kernel sum, with `C_h = C₀ / c_ψ`, `κ_h = 2 κ_dec`, `C_g = CPE p₁ / R_g`,
  `κ = min κ_h κ'`: `≤ C_h C_g (n_* c₁) K_obs² e^{(κ-κ₀) c_G} e^{-(κ-κ₀-1) dExt W}`;
* `obsCoeffParam` is bounded by the sum of the last two.

Carried: the same numerical hypotheses as `obsCoeffParam_fromTower`; the activity fields `hσ`
(holomorphy in `σ` on the disc of radius `R_g`) and `hzero` (vanishing at `σ = 0`) of
`obsTiltLabels_fromTower`. -/
theorem obsCoeffParam_norm_le_of_EvG {q : ℝ} (hRg : 1 < Rg) (hKc : K0 d L T.κ0 + 1 ≤ Kc)
    (hσ : ∀ e ∈ physVq S S.a₁ S.ν T.t q, ∀ t ∈ ball (0 : ℂ) (3 / 2), ∀ y' Φ, DifferentiableOn ℂ
      (fun σ => (tiltActObs Aact (show L ^ T.m₀ ∣ N₁ by simpa using h3N) T.κ0_ent hεH.le hdj hK Rg
        hR (ball (0 : ℂ) (3 / 2)) e t σ).H y' Φ) (ball (0 : ℂ) Rg))
    (hzero : ∀ e ∈ physVq S S.a₁ S.ν T.t q, ∀ t y' Φ,
      (tiltActObs Aact (show L ^ T.m₀ ∣ N₁ by simpa using h3N) T.κ0_ent hεH.le hdj hK Rg hR
        (ball (0 : ℂ) (3 / 2)) e t 0).H y' Φ = 0)
    (hε : Rg * max (εH + εH) εH ≤ stepTheta d L Kobs (2 * T.κdec - 1) T.κ0 T.κ')
    (Ev : Set (CTorus d L N₁ T.m₁ (k + 1)) →
        RawData d L (N₁ * L ^ T.m₁) (k + 1) N × (unitPts S.G' × Fin N → ℂ) → ℂ)
    (ha : ∀ Y, AnalyticOnNhd ℂ (Ev Y) (XiCRaw S.G' (compWeight L 1) ν (k + 1) 1 T.t ×ˢ
          {ψh : unitPts S.G' × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ lvCpsiG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2)))}))
    (hd : ∀ Y, ∀ u ∈ XiCRaw S.G' (compWeight L 1) ν (k + 1) 1 T.t ×ˢ
          {ψh : unitPts S.G' × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ lvCpsiG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2)))},
        ∀ u' ∈ XiCRaw S.G' (compWeight L 1) ν (k + 1) 1 T.t ×ˢ
          {ψh : unitPts S.G' × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ lvCpsiG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2)))},
        AgHatDir S.hG' Y u u' → Ev Y u = Ev Y u')
    (hb : ∀ Y, ∀ u ∈ XiCRaw S.G' (compWeight L 1) ν (k + 1) 1 T.t ×ˢ
          {ψh : unitPts S.G' × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ lvCpsiG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2)))},
        ‖Ev Y u‖ ≤ (cK2' d L N (famConst d L T.BG₂ T.κ) * T.t) *
          Real.exp (-(2 * T.κdec) * treeLenCovOne T.m₀ (k + 1) Y))
    (hD : ∀ D : BgData S.G' N, XiCData S.G' (compWeight L 1) ν (k + 1) 1 T.t D →
        ObsMarkHalf S T.m₀ hp Ev D (obsDomains S (LocalCover.nbhdF T.m₀ y) T.m₀ k (LocalCover.fam T.m₀ y))
          (obsLab (Lab.sum Lab) hdj) (lvCpsiG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2))))
          (cK2' d L N (famConst d L T.BG₂ T.κ) * T.t) (2 * T.κdec - 1) T.κ0
          (cK2' d L N (famConst d L T.BG₂ T.κ) * T.t / (lvCpsiG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2)))))
          (2 * T.κdec) (rootCube (m₀ := T.m₀) (blockIndex y)))
    (W : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := T.m₁) (K := k + 1) T.m₀ (k + 1)
      Set.univ)) :
    (∀ θ ∈ physVq S S.a₁ S.ν T.t q, ∀ (m : ObsMarkIdx S) (S' : Finset (CubeB (d := d) (L := L)
        (N₁ := N₁) (m₁ := T.m₁) (K := k + 1) T.m₀ (k + 1) Set.univ)),
      ‖markIntTerm (S.blockSplit T.m₀ hp).μ (Actₒ θ) (obsY1 T.m₀ S (Lb ⊕ Lb) 𝒴ₒ m)
        (blockMarkC S T.m₀ hp m.1 m.2) S'‖ ≤
        CPE d L Kobs (2 * T.κdec - 1) T.κ0 T.κ' * S.p₁ * Real.exp (-T.κ' * dExt S') / Rg) ∧
    (∀ θ ∈ physVq S S.a₁ S.ν T.t q,
      ‖gsumCoeff (S.blockSplit T.m₀ hp).μ (obsLab (Lab.sum Lab) hdj) (fun t => Actₒ θ t 1)
        (obsRemLab 𝒴ₒ (fun Y => Sum.inl (Sum.inr Y))
          (obsY0 T.m₀ (Lb ⊕ Lb) 𝒴ₒ (rootCube (m₀ := T.m₀) (blockIndex y))))
        (obsGrFam S T.m₀ hp Ev 𝒴ₒ (XiCRaw S.G' (compWeight L 1) ν (k + 1) 1 T.t) θ) W‖ ≤
        CPE d L Kobs (2 * T.κdec - 1) T.κ0 T.κ' *
          (∑ r, 8 * (cK2' d L N (famConst d L T.BG₂ T.κ) * T.t) *
            (S.p₁ / lvCpsiG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2)))) ^ 2 * Real.exp (-T.κ0 *
            (obsLab (Lab.sum Lab) hdj).dl (obsRemLab 𝒴ₒ (fun Y => Sum.inl (Sum.inr Y))
              (obsY0 T.m₀ (Lb ⊕ Lb) 𝒴ₒ (rootCube (m₀ := T.m₀) (blockIndex y))) r))) *
          Real.exp (-T.κ' * dExt W)) ∧
    (∀ θ ∈ physVq S S.a₁ S.ν T.t q,
      ‖kernelMarkSum
        (fun m T'' => obsHker 𝒴ₒ (fun Y => hatCoeff (Ev Y)
          (θ.1 : RawData d L (N₁ * L ^ T.m₁) (k + 1) N) (obsUnitVec S m)) T.m₀ T'')
        (fun m S' => markIntTerm (S.blockSplit T.m₀ hp).μ (Actₒ θ) (obsY1 T.m₀ S (Lb ⊕ Lb) 𝒴ₒ m)
          (blockMarkC S T.m₀ hp m.1 m.2) S') W‖ ≤
        (cK2' d L N (famConst d L T.BG₂ T.κ) * T.t / lvCpsiG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2)))) *
          (CPE d L Kobs (2 * T.κdec - 1) T.κ0 T.κ' * S.p₁ / Rg) *
          (((N * L ^ (d * (T.m₀ + T.m₁ + 1)) : ℕ) : ℝ) * c1 d L) * Kobs ^ 2 *
          Real.exp ((min (2 * T.κdec) T.κ' - T.κ0) * cG d L) *
          Real.exp (-(min (2 * T.κdec) T.κ' - T.κ0 - 1) * dExt W)) := by
  subst hS
  have hcψ := Dsc.cψ_pos
  have hC0 := cK2'_famConst_mul_t_posG T
  have hq : p₁ / lvCpsiG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2))) ≤ 1 / 4 := by
    rw [div_le_iff₀ hcψ]
    have : 0 < lvRG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2))) p₁ * p₁ := mul_pos Dsc.r_pos hp
    nlinarith [Dsc.ray_margin]
  have hN3 : L ^ T.m₀ ∣ N₁ := by simpa using h3N
  have hK0 := T.marks_K0_pos
  have hKobs : K0 d L T.κ0 + 1 ≤ Kobs := by linarith
  have hεpos : 0 < Rg * max (εH + εH) εH :=
    mul_pos (by linarith) (lt_of_lt_of_le (by linarith) (le_max_left _ _))
  have hε' : Rg * max (εH + εH) εH ≤ 1 / (8 * Kobs ^ 3 * c1 d L *
      Real.exp ((2 * T.κdec - 1 - 2 * T.κ0) * cG d L + c1 d L + T.κ' * cG d L)) := by
    unfold stepTheta at hε; exact hε
  have hdl0 : ∀ m : ObsMarkIdx (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ),
      (obsLab (Lab.sum Lab) hdj).dl (obsY1 T.m₀ (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ) (Lb ⊕ Lb)
        (obsDomains (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ) (LocalCover.nbhdF T.m₀ y) T.m₀ k (LocalCover.fam T.m₀ y)) m)
        = 0 := fun m => obsCubeLab_dl T.m₀ _
  have hcell : ∀ m : ObsMarkIdx (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ),
      obsMarkCube (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ) T.m₀ m ∈ blocksOf (d := d) (L := L) (N₁ := N₁)
        (m₁ := T.m₁) (K := k + 1) T.m₀ (k + 1) Set.univ ((obsLab (Lab.sum Lab) hdj).ysite
          (obsY1 T.m₀ (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ) (Lb ⊕ Lb) (obsDomains (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ)
            (LocalCover.nbhdF T.m₀ y) T.m₀ k (LocalCover.fam T.m₀ y)) m)) :=
    fun m => obsCubeLab_mem T.m₀ (obsMarkCube (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ) T.m₀ m)
  have hfirst : ∀ θ ∈ physVq (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ) (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ).a₁
      (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ).ν T.t q, ∀ (m : ObsMarkIdx (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ))
      (S' : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := T.m₁) (K := k + 1) T.m₀ (k + 1)
        Set.univ)),
      ‖markIntTerm ((hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ).blockSplit T.m₀ hp).μ
        (fun t σ => tiltActObs Aact hN3 T.κ0_ent hεH.le hdj hK Rg hR
          (ball (0 : ℂ) (3 / 2)) θ t σ)
        (obsY1 T.m₀ (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ) (Lb ⊕ Lb) (obsDomains (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ)
          (LocalCover.nbhdF T.m₀ y) T.m₀ k (LocalCover.fam T.m₀ y)) m)
        (blockMarkC (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ) T.m₀ hp m.1 m.2) S'‖ ≤
        CPE d L Kobs (2 * T.κdec - 1) T.κ0 T.κ' * (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ).p₁ * Real.exp (-T.κ' * dExt S') / Rg := by
    intro θ hθ m S'
    have h := norm_markIntTerm_le (E := physParam N (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ))
      ((hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ).blockSplit T.m₀ hp).μ hN3 (le_refl (k + 1)) isPiUnion_univ_K
      (Lab := obsLab (Lab.sum Lab) hdj) (κG := 2 * T.κdec - 1) (κ' := T.κ') (F0 := (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ).p₁) (R := Rg)
      (fun θ t σ => tiltActObs Aact hN3 T.κ0_ent hεH.le hdj hK Rg hR (ball (0 : ℂ) (3 / 2)) θ t σ)
      (obsY1 T.m₀ (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ) (Lb ⊕ Lb) (obsDomains (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ)
          (LocalCover.nbhdF T.m₀ y) T.m₀ k (LocalCover.fam T.m₀ y)) m)
      (fun _ => blockMarkC (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ) T.m₀ hp m.1 m.2)
      (physVq (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ) (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ).a₁ (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ).ν T.t q)
      (fun _ => measurable_blockMarkC m.1 m.2)
      (fun _ => depOn_blockMarkC m.1 m.2 (hcell m))
      (fun _ Φ => by rw [hdl0 m]; simpa using norm_blockMarkC_le m.1 m.2 Φ)
      T.marks_hκ0 (by linarith) hεpos hp T.marks_hκ' T.marks_hκG T.marks_hκ hε' hRg
      (fun e he s hs y' Φ => hσ e he (s : ℂ) (seg_mem_ball_three_halves s hs) y' Φ)
      (fun e he s _ y' Φ => hzero e he (s : ℂ) y' Φ)
      (fun _ _ => integral_blockMarkC m.1 m.2) S' θ hθ
    rw [hdl0 m] at h
    simpa using h
  have hrem : ∀ θ ∈ physVq (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ) (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ).a₁
      (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ).ν T.t q,
      ‖gsumCoeff ((hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ).blockSplit T.m₀ hp).μ (obsLab (Lab.sum Lab) hdj)
        (fun t => tiltActObs Aact hN3 T.κ0_ent hεH.le hdj hK Rg hR (ball (0 : ℂ) (3 / 2)) θ t 1)
        (obsRemLab (obsDomains (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ) (LocalCover.nbhdF T.m₀ y) T.m₀ k
            (LocalCover.fam T.m₀ y)) (fun Y => Sum.inl (Sum.inr Y))
          (obsY0 T.m₀ (Lb ⊕ Lb) (obsDomains (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ) (LocalCover.nbhdF T.m₀ y) T.m₀ k
            (LocalCover.fam T.m₀ y)) (rootCube (m₀ := T.m₀) (blockIndex y))))
        (obsGrFam (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ) T.m₀ hp Ev (obsDomains (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ)
          (LocalCover.nbhdF T.m₀ y) T.m₀ k (LocalCover.fam T.m₀ y))
          (XiCRaw (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ).G' (compWeight L 1) ν (k + 1) 1 T.t) θ) W‖ ≤
        CPE d L Kobs (2 * T.κdec - 1) T.κ0 T.κ' *
          (∑ r, 8 * (cK2' d L N (famConst d L T.BG₂ T.κ) * T.t) *
            (p₁ / lvCpsiG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2)))) ^ 2 * Real.exp (-T.κ0 *
            (obsLab (Lab.sum Lab) hdj).dl (obsRemLab (obsDomains (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ)
              (LocalCover.nbhdF T.m₀ y) T.m₀ k (LocalCover.fam T.m₀ y)) (fun Y => Sum.inl (Sum.inr Y))
              (obsY0 T.m₀ (Lb ⊕ Lb) (obsDomains (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ) (LocalCover.nbhdF T.m₀ y) T.m₀ k
                (LocalCover.fam T.m₀ y)) (rootCube (m₀ := T.m₀) (blockIndex y))) r))) *
          Real.exp (-T.κ' * dExt W) := by
    intro θ hθ
    exact norm_gsumCoeff_le (E := physParam N (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ))
      ((hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ).blockSplit T.m₀ hp).μ hN3 (le_refl (k + 1)) isPiUnion_univ_K
      (Lab := obsLab (Lab.sum Lab) hdj) (κG := 2 * T.κdec - 1) (κ' := T.κ')
      (F0 := fun _ => 8 * (cK2' d L N (famConst d L T.BG₂ T.κ) * T.t) *
        (p₁ / lvCpsiG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2)))) ^ 2)
      (fun θ t => tiltActObs Aact hN3 T.κ0_ent hεH.le hdj hK Rg hR (ball (0 : ℂ) (3 / 2)) θ t 1)
      _ (fun θ => obsGrFam (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ) T.m₀ hp Ev (obsDomains (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ)
          (LocalCover.nbhdF T.m₀ y) T.m₀ k (LocalCover.fam T.m₀ y))
          (XiCRaw (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ).G' (compWeight L 1) ν (k + 1) 1 T.t) θ)
      (physVq (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ) (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ).a₁ (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ).ν T.t q)
      (fun θ i u => measurable_obsGrFam hcψ hq (fun Y _ => ha Y) θ i u)
      (fun θ i u => depOn_obsGrFam_all (hp := hp) hN3 hcψ hq hdj (fun Y _ => hd Y) _
        (fun Y => Sum.inl (Sum.inr Y)) _ (fun Y => rfl) θ i u)
      (fun θ i u Φ => norm_obsGrFam_le hcψ hq (fun Y _ => ha Y) hC0 (fun Y _ => hb Y) _
        (fun Y => Sum.inl (Sum.inr Y)) _ (fun Y => rfl) T.marks_κG_le θ i u Φ)
      T.marks_hκ0 (by linarith) hεpos ⟨none⟩ (fun _ => by positivity) T.marks_hκ' T.marks_hκG
      T.marks_hκ hε' W θ hθ
  have hkey : ∀ θ ∈ physVq (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ) (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ).a₁
      (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ).ν T.t q, ∃ D : BgData (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ).G' N,
      XiCData (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ).G' (compWeight L 1) ν (k + 1) 1 T.t D ∧
      ∀ (m : ObsMarkIdx (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ))
        (T'' : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := T.m₁) (K := k + 1) T.m₀ (k + 1)
          Set.univ)),
        obsHker (obsDomains (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ) (LocalCover.nbhdF T.m₀ y) T.m₀ k
          (LocalCover.fam T.m₀ y)) (fun Y => hatCoeff (Ev Y)
            (θ.1 : RawData d L (N₁ * L ^ T.m₁) (k + 1) N)
            (obsUnitVec (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ) m)) T.m₀ T'' =
        obsHker (obsDomains (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ) (LocalCover.nbhdF T.m₀ y) T.m₀ k
          (LocalCover.fam T.m₀ y)) (obsRowCoeff (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ) Ev D m) T.m₀ T'' := by
    intro θ hθ
    obtain ⟨D, hDx, hDr⟩ := hθ.1.1
    have hDr' : (θ.1 : RawData d L (N₁ * L ^ T.m₁) (k + 1) N) = rawOf D := hDr
    exact ⟨D, hDx, fun m T'' => by rw [hDr']; rfl⟩
  have hkern : ∀ θ ∈ physVq (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ) (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ).a₁
      (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ).ν T.t q,
      ‖kernelMarkSum
        (fun m T'' => obsHker (obsDomains (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ) (LocalCover.nbhdF T.m₀ y) T.m₀ k
          (LocalCover.fam T.m₀ y)) (fun Y => hatCoeff (Ev Y)
          (θ.1 : RawData d L (N₁ * L ^ T.m₁) (k + 1) N)
          (obsUnitVec (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ) m)) T.m₀ T'')
        (fun m S' => markIntTerm ((hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ).blockSplit T.m₀ hp).μ
          (fun t σ => tiltActObs Aact hN3 T.κ0_ent hεH.le hdj hK Rg hR
            (ball (0 : ℂ) (3 / 2)) θ t σ)
          (obsY1 T.m₀ (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ) (Lb ⊕ Lb) (obsDomains (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ)
            (LocalCover.nbhdF T.m₀ y) T.m₀ k (LocalCover.fam T.m₀ y)) m)
          (blockMarkC (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ) T.m₀ hp m.1 m.2) S') W‖ ≤
        (cK2' d L N (famConst d L T.BG₂ T.κ) * T.t / lvCpsiG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2)))) *
          (CPE d L Kobs (2 * T.κdec - 1) T.κ0 T.κ' * (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ).p₁ / Rg) *
          (((N * L ^ (d * (T.m₀ + T.m₁ + 1)) : ℕ) : ℝ) * c1 d L) * Kobs ^ 2 *
          Real.exp ((min (2 * T.κdec) T.κ' - T.κ0) * cG d L) *
          Real.exp (-(min (2 * T.κdec) T.κ' - T.κ0 - 1) * dExt W) := by
    have hCPE := CPE_nonneg' (d := d) (L := L) Kobs (2 * T.κdec - 1) T.κ0 T.κ'
    have hCg : 0 ≤ CPE d L Kobs (2 * T.κdec - 1) T.κ0 T.κ' * (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ).p₁ / Rg :=
      div_nonneg (mul_nonneg hCPE hp.le) (by linarith)
    have hmain := norm_kernelMarkSum_le (E := physParam N (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ))
      (ι := ObsMarkIdx (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ)) hN3 (le_refl (k + 1))
      (V := physVq (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ) (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ).a₁
        (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ).ν T.t q)
      (fun m => obsMarkCube (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ) T.m₀ m)
      (nmax := (((N * L ^ (d * (T.m₀ + T.m₁ + 1)) : ℕ)) : ℝ)) (Nat.cast_nonneg _)
      (fun c => by
        have := card_markIdx_cell_le_pow (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ) c
        exact_mod_cast this)
      (fun θ m T'' => obsHker (obsDomains (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ) (LocalCover.nbhdF T.m₀ y) T.m₀ k
          (LocalCover.fam T.m₀ y)) (fun Y => hatCoeff (Ev Y)
          (θ.1 : RawData d L (N₁ * L ^ T.m₁) (k + 1) N)
          (obsUnitVec (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ) m)) T.m₀ T'')
      (fun θ m S' => markIntTerm ((hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ).blockSplit T.m₀ hp).μ
          (fun t σ => tiltActObs Aact hN3 T.κ0_ent hεH.le hdj hK Rg hR
            (ball (0 : ℂ) (3 / 2)) θ t σ)
          (obsY1 T.m₀ (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ) (Lb ⊕ Lb) (obsDomains (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ)
            (LocalCover.nbhdF T.m₀ y) T.m₀ k (LocalCover.fam T.m₀ y)) m)
          (blockMarkC (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ) T.m₀ hp m.1 m.2) S')
      (Ch := cK2' d L N (famConst d L T.BG₂ T.κ) * T.t / lvCpsiG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2))))
      (Cg := CPE d L Kobs (2 * T.κdec - 1) T.κ0 T.κ' * (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ).p₁ / Rg)
      (κh := 2 * T.κdec) (κg := T.κ')
      (div_nonneg hC0.le hcψ.le) hCg
      (fun θ hθ m T'' => by
        obtain ⟨D, hDx, hDe⟩ := hkey θ hθ
        rw [hDe m T'']
        obtain ⟨_, _, _, _, _, _, _, _, hbd, _⟩ := hD D hDx
        exact hbd m T'')
      (fun θ hθ m T'' hT => by
        obtain ⟨D, hDx, hDe⟩ := hkey θ hθ
        rw [hDe m T'']
        obtain ⟨_, _, _, _, _, _, _, _, _, hsp, _⟩ := hD D hDx
        exact hsp m T'' hT)
      (fun θ hθ m S' => by
        calc _ ≤ _ := hfirst θ hθ m S'
          _ = _ := by ring)
      (fun θ hθ m S' hS' => markIntTerm_support
        ((hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ).blockSplit T.m₀ hp).μ hN3 (le_refl (k + 1)) isPiUnion_univ_K
        (fun t σ => tiltActObs Aact hN3 T.κ0_ent hεH.le hdj hK Rg hR
          (ball (0 : ℂ) (3 / 2)) θ t σ)
        (obsY1 T.m₀ (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ) (Lb ⊕ Lb) (obsDomains (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ)
          (LocalCover.nbhdF T.m₀ y) T.m₀ k (LocalCover.fam T.m₀ y)) m)
        (blockMarkC (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ) T.m₀ hp m.1 m.2)
        (measurable_blockMarkC m.1 m.2) (depOn_blockMarkC m.1 m.2 (hcell m))
        (fun Φ => by rw [hdl0 m]; simpa using norm_blockMarkC_le m.1 m.2 Φ)
        T.marks_hκ0 (by linarith) hεpos hp T.marks_hκ' T.marks_hκG T.marks_hκ hε' S'
        (fun hsub => hS' (hsub (hcell m))))
      T.marks_hκ0 hKobs (by linarith [T.marks_κ0_le_κH]) T.marks_κ0_le_κ' W
    exact fun θ hθ => hmain θ hθ
  exact ⟨hfirst, hrem, hkern⟩

include Dsc hS in
/-- General tower `T : StepTowerG d L N κmin` (block scale `T.m₀`, `b = β L^{k (d-2)}`); the fixed theorem `obsCoeffParam_fromTower` is its corollary.
**The two families and the analyticity of the coefficient, for the one sharp-hat family.**
There is one family `Ev` (that of `obsMarkHalves_of_sharpHat_param`, with `ObsMarkHalf` and
`ObsRayIdentity` at every datum of `Ξ`) such that both `ParamMarkFamily` records exist and, for
every finite set of cubes, the first-order terms, the kernel sum, the remainder coefficient and
`obsCoeffParam` are analytic on `physVq … q`.  The numerical hypotheses carried are `hKc`
(`K₀ + 1 ≤ K_c`, any `K_c ≥ K₀ + 1`), `hε` (the amplitude of the tilted extension is at most
`stepTheta d L Kobs (2 κdec - 1) κ0 κ'`) and `1 < Rg`; the activity fields `hhol`, `hcont` are
those of `obsTiltLabels_fromTower`.  This statement is conditional on them; they are discharged
at the tower, by a compatible instantiation of `obsTiltLabels_fromTower`, in
`obsCoeffFamily_fromTower`. -/
theorem obsCoeffParam_fromTowerG (hϱ : ϱ = rhoSepG d L T.m₁) (hN : 5 < N₁) (hνpos : 0 < ν) (hν : ν * (L : ℝ) ^ (2 * (k + 1)) ≤ 1)
    {q : ℝ} (hRg : 1 < Rg) (hKc : K0 d L T.κ0 + 1 ≤ Kc)
    (hhol : ∀ y', ∀ Φ ∈ physCarrier S T.m₀ hp, AnalyticOnNhd ℂ (fun r : physParam N S × ℂ =>
      (tiltActObs Aact (show L ^ T.m₀ ∣ N₁ by simpa using h3N) T.κ0_ent hεH.le hdj hK Rg hR
        (ball (0 : ℂ) (3 / 2)) r.1 r.2 1).H y' Φ)
      (physVq S S.a₁ S.ν T.t q ×ˢ ball (0 : ℂ) (3 / 2)))
    (hcont : ∀ y', ∀ θ ∈ physVq S S.a₁ S.ν T.t q, ∀ u ∈ ball (0 : ℂ) (3 / 2),
      ContinuousOn ((tiltActObs Aact (show L ^ T.m₀ ∣ N₁ by simpa using h3N) T.κ0_ent hεH.le hdj hK
        Rg hR (ball (0 : ℂ) (3 / 2)) θ u 1).H y') (physCarrier S T.m₀ hp))
    (hε : Rg * max (εH + εH) εH ≤ stepTheta d L Kobs (2 * T.κdec - 1) T.κ0 T.κ')
    (i : Fin N) :
    ∃ Ev : Set (CTorus d L N₁ T.m₁ (k + 1)) →
        RawData d L (N₁ * L ^ T.m₁) (k + 1) N × (unitPts S.G' × Fin N → ℂ) → ℂ,
      (∀ Y, AnalyticOnNhd ℂ (Ev Y) (XiCRaw S.G' (compWeight L 1) ν (k + 1) 1 T.t ×ˢ
          {ψh : unitPts S.G' × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ lvCpsiG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2)))})) ∧
      (∀ Y, ∀ u ∈ XiCRaw S.G' (compWeight L 1) ν (k + 1) 1 T.t ×ˢ
          {ψh : unitPts S.G' × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ lvCpsiG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2)))},
        ∀ u' ∈ XiCRaw S.G' (compWeight L 1) ν (k + 1) 1 T.t ×ˢ
          {ψh : unitPts S.G' × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ lvCpsiG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2)))},
        AgHatDir S.hG' Y u u' → Ev Y u = Ev Y u') ∧
      (∀ Y, ∀ u ∈ XiCRaw S.G' (compWeight L 1) ν (k + 1) 1 T.t ×ˢ
          {ψh : unitPts S.G' × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ lvCpsiG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2)))},
        ‖Ev Y u‖ ≤ (cK2' d L N (famConst d L T.BG₂ T.κ) * T.t) *
          Real.exp (-(2 * T.κdec) * treeLenCovOne T.m₀ (k + 1) Y)) ∧
      (∀ D : BgData S.G' N, XiCData S.G' (compWeight L 1) ν (k + 1) 1 T.t D →
        ObsMarkHalf S T.m₀ hp Ev D (obsDomains S (LocalCover.nbhdF T.m₀ y) T.m₀ k (LocalCover.fam T.m₀ y))
          (obsLab (Lab.sum Lab) hdj) (lvCpsiG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2))))
          (cK2' d L N (famConst d L T.BG₂ T.κ) * T.t) (2 * T.κdec - 1) T.κ0
          (cK2' d L N (famConst d L T.BG₂ T.κ) * T.t / (lvCpsiG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2)))))
          (2 * T.κdec) (rootCube (m₀ := T.m₀) (blockIndex y)) ∧
        ObsRayIdentity S T.m₀ hp
          (fun ψh => svec (lvLowG d L N₁ T.m₁ k ϱ)
            (flFieldOne S.G' (lvLowG d L N₁ T.m₁ k ϱ) T.BG₂ T.κ 1 ν D
              (hatLift S.G' 1 ν S.hG' ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) D ψh)) y i) Ev D
          (obsDomains S (LocalCover.nbhdF T.m₀ y) T.m₀ k (LocalCover.fam T.m₀ y))) ∧
      ((∀ m : ObsMarkIdx S, Nonempty (ParamMarkFamily (S.blockSplit T.m₀ hp).μ
        (obsLab (Lab.sum Lab) hdj)
        (fun θ t => tiltActObs Aact (show L ^ T.m₀ ∣ N₁ by simpa using h3N) T.κ0_ent hεH.le hdj hK
          Rg hR (ball (0 : ℂ) (3 / 2)) θ t 1)
        (fun _ : Unit => obsY1 T.m₀ S (Lb ⊕ Lb) (obsDomains S (LocalCover.nbhdF T.m₀ y) T.m₀ k
          (LocalCover.fam T.m₀ y)) m)
        (fun _ _ _ => blockMarkC S T.m₀ hp m.1 m.2) (2 * T.κdec - 1)
        (fun _ => S.p₁ * Real.exp ((2 * T.κdec - 1) * (obsLab (Lab.sum Lab) hdj).dl
          (obsY1 T.m₀ S (Lb ⊕ Lb) (obsDomains S (LocalCover.nbhdF T.m₀ y) T.m₀ k (LocalCover.fam T.m₀ y)) m)))
        (physVq S S.a₁ S.ν T.t q) (ball (0 : ℂ) (3 / 2)) (physCarrier S T.m₀ hp))) ∧
      Nonempty (ParamMarkFamily (S.blockSplit T.m₀ hp).μ (obsLab (Lab.sum Lab) hdj)
        (fun θ t => tiltActObs Aact (show L ^ T.m₀ ∣ N₁ by simpa using h3N) T.κ0_ent hεH.le hdj hK
          Rg hR (ball (0 : ℂ) (3 / 2)) θ t 1)
        (obsRemLab (obsDomains S (LocalCover.nbhdF T.m₀ y) T.m₀ k (LocalCover.fam T.m₀ y))
          (fun Y => Sum.inl (Sum.inr Y))
          (obsY0 T.m₀ (Lb ⊕ Lb) (obsDomains S (LocalCover.nbhdF T.m₀ y) T.m₀ k (LocalCover.fam T.m₀ y))
            (rootCube (m₀ := T.m₀) (blockIndex y))))
        (obsGrFam S T.m₀ hp Ev (obsDomains S (LocalCover.nbhdF T.m₀ y) T.m₀ k (LocalCover.fam T.m₀ y))
          (XiCRaw S.G' (compWeight L 1) ν (k + 1) 1 T.t)) (2 * T.κdec - 1)
        (fun _ => 8 * (cK2' d L N (famConst d L T.BG₂ T.κ) * T.t) *
          (S.p₁ / lvCpsiG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2)))) ^ 2)
        (physVq S S.a₁ S.ν T.t q) (ball (0 : ℂ) (3 / 2)) (physCarrier S T.m₀ hp))) ∧
      ∀ T' : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := T.m₁) (K := k + 1) T.m₀ (k + 1)
        Set.univ),
      ((∀ (m : ObsMarkIdx S) (S' : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := T.m₁)
        (K := k + 1) T.m₀ (k + 1) Set.univ)),
      AnalyticOnNhd ℂ (fun θ => markIntTerm (S.blockSplit T.m₀ hp).μ (Actₒ θ)
        (obsY1 T.m₀ S (Lb ⊕ Lb) 𝒴ₒ m) (blockMarkC S T.m₀ hp m.1 m.2) S')
        (physVq S S.a₁ S.ν T.t q)) ∧
    AnalyticOnNhd ℂ (fun θ => kernelMarkSum
      (fun m T'' => obsHker 𝒴ₒ (fun Y => hatCoeff (Ev Y)
        (θ.1 : RawData d L (N₁ * L ^ T.m₁) (k + 1) N) (obsUnitVec S m)) T.m₀ T'')
      (fun m S' => markIntTerm (S.blockSplit T.m₀ hp).μ (Actₒ θ) (obsY1 T.m₀ S (Lb ⊕ Lb) 𝒴ₒ m)
        (blockMarkC S T.m₀ hp m.1 m.2) S') T') (physVq S S.a₁ S.ν T.t q) ∧
    AnalyticOnNhd ℂ (fun θ => gsumCoeff (S.blockSplit T.m₀ hp).μ (obsLab (Lab.sum Lab) hdj)
      (fun t => Actₒ θ t 1)
      (obsRemLab 𝒴ₒ (fun Y => Sum.inl (Sum.inr Y))
        (obsY0 T.m₀ (Lb ⊕ Lb) 𝒴ₒ (rootCube (m₀ := T.m₀) (blockIndex y))))
      (obsGrFam S T.m₀ hp Ev 𝒴ₒ (XiCRaw S.G' (compWeight L 1) ν (k + 1) 1 T.t) θ) T')
      (physVq S S.a₁ S.ν T.t q) ∧
    AnalyticOnNhd ℂ (fun θ => obsCoeffParam (S.blockSplit T.m₀ hp).μ Actₒ
      (fun m => obsY1 T.m₀ S (Lb ⊕ Lb) 𝒴ₒ m) (fun m => blockMarkC S T.m₀ hp m.1 m.2)
      (fun θ m T'' => obsHker 𝒴ₒ (fun Y => hatCoeff (Ev Y)
        (θ.1 : RawData d L (N₁ * L ^ T.m₁) (k + 1) N) (obsUnitVec S m)) T.m₀ T'')
      (obsRemLab 𝒴ₒ (fun Y => Sum.inl (Sum.inr Y))
        (obsY0 T.m₀ (Lb ⊕ Lb) 𝒴ₒ (rootCube (m₀ := T.m₀) (blockIndex y))))
      (fun θ => obsGrFam S T.m₀ hp Ev 𝒴ₒ (XiCRaw S.G' (compWeight L 1) ν (k + 1) 1 T.t) θ) θ T')
      (physVq S S.a₁ S.ν T.t q)) := by
  obtain ⟨Ev, ha, hd, hb, hD⟩ := obsEv_fromTowerG T k hk N₁ ν β p₁ hN hνpos hν Dsc hϱ hS hp y i
    (Lab.sum Lab)
  exact ⟨Ev, ha, hd, hb, hD, obsFamilies_of_EvG T k hk N₁ ν β p₁ Dsc S hS hp y h3N Lab hεH Aact
    hdj hK Rg hR hϱ hνpos hν hhol hcont Ev ha hb, fun T' => obsCoeffParam_analytic_of_EvG T k hk N₁
    ν β p₁ Dsc S hS hp y h3N Lab hεH Aact hdj hK Rg hR hϱ hνpos hν hRg hKc hhol hcont hε Ev ha hd hb
    T'⟩


end TowerG

section Tower

variable {κmin : ℝ} (T : StepTower κmin) (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁]
  (ν β p₁ : ℝ) (Dsc : StepScaleData T k hk N₁ ν β p₁)
  (S : StepSetting 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) (hS : S = T.step k hk N₁ ν β p₁)
  (hp : 0 < S.p₁) (y : CTorus 3 3 N₁ T.m₁ (k + 1)) (h3N : 3 ∣ N₁)
  {Lb : Type} [Fintype Lb]
  (Lab : CubeLabels (d := 3) (L := 3) (N₁ := N₁) (m₁ := T.m₁) (K := k + 1) 1 (k + 1)
    Set.univ Lb) {εH : ℝ} (hεH : 0 < εH) {Kc : ℝ}
  (Aact : physParam 2 S → ℂ → LabelAct Lab (S.blockSplit 1 hp).Ωb εH (2 * T.κdec - 1) T.κ0 Kc)
  (hdj : ∀ Y ∈ obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y), IsDj 1 (k + 1) Y)
  {Kobs : ℝ} (hK : Kc + Kc + K0 3 3 T.κ0 + K0 3 3 T.κ0 ≤ Kobs) (Rg : ℝ) (hR : 0 ≤ Rg)

include Dsc hS in
/-- **The first-order and remainder families, and the analyticity of the coefficient, for any
sharp-hat family `Ev`** (its three clauses as in `obsEv_fromTower`).  The activity is
`tiltActObs … (e, t, σ)` on the labels `obsLab (Lab.sum Lab) hdj`, `V = physVq … q`,
`𝒰 = ball 0 (3/2)`, carrier `physCarrier S 1 hp`.

Numerical hypothesis carried: `hε`, the amplitude of the tilted extension is at most
`stepTheta 3 3 Kobs (2 κdec - 1) κ0 κ'`; the other rates are the tower fields
(`marks_hκ0`, `marks_hκ'`, `marks_hκ`, `marks_κG_le`, `marks_K0_pos`). -/
theorem obsFamilies_of_Ev (hνpos : 0 < ν) (hν : ν * 3 ^ (2 * (k + 1)) ≤ 1) {q : ℝ}
    (hhol : ∀ y', ∀ Φ ∈ physCarrier S 1 hp, AnalyticOnNhd ℂ (fun r : physParam 2 S × ℂ =>
      (tiltActObs Aact (show 3 ^ 1 ∣ N₁ by simpa using h3N) T.κ0_ent hεH.le hdj hK Rg hR
        (ball (0 : ℂ) (3 / 2)) r.1 r.2 1).H y' Φ)
      (physVq S S.a₁ S.ν T.t q ×ˢ ball (0 : ℂ) (3 / 2)))
    (hcont : ∀ y', ∀ θ ∈ physVq S S.a₁ S.ν T.t q, ∀ u ∈ ball (0 : ℂ) (3 / 2),
      ContinuousOn ((tiltActObs Aact (show 3 ^ 1 ∣ N₁ by simpa using h3N) T.κ0_ent hεH.le hdj hK
        Rg hR (ball (0 : ℂ) (3 / 2)) θ u 1).H y') (physCarrier S 1 hp))
    (Ev : Set (CTorus 3 3 N₁ T.m₁ (k + 1)) →
        RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2 × (unitPts S.G' × Fin 2 → ℂ) → ℂ)
    (ha : ∀ Y, AnalyticOnNhd ℂ (Ev Y) (XiCRaw S.G' (compWeight 3 1) ν (k + 1) 1 T.t ×ˢ
          {ψh : unitPts S.G' × Fin 2 → ℂ | ∀ p, ‖ψh p‖ ≤ lvCpsi T.κ T.t (β * 3 ^ k)}))
    (hb : ∀ Y, ∀ u ∈ XiCRaw S.G' (compWeight 3 1) ν (k + 1) 1 T.t ×ˢ
          {ψh : unitPts S.G' × Fin 2 → ℂ | ∀ p, ‖ψh p‖ ≤ lvCpsi T.κ T.t (β * 3 ^ k)},
        ‖Ev Y u‖ ≤ (cK2' 3 3 2 (famConst 3 3 T.BG₂ T.κ) * T.t) *
          Real.exp (-(2 * T.κdec) * treeLenCovOne 1 (k + 1) Y)) :
    (∀ m : ObsMarkIdx S, Nonempty (ParamMarkFamily (S.blockSplit 1 hp).μ
      (obsLab (Lab.sum Lab) hdj)
      (fun θ t => tiltActObs Aact (show 3 ^ 1 ∣ N₁ by simpa using h3N) T.κ0_ent hεH.le hdj hK
        Rg hR (ball (0 : ℂ) (3 / 2)) θ t 1)
      (fun _ : Unit => obsY1 1 S (Lb ⊕ Lb) (obsDomains S (LocalCover.nbhdF 1 y) 1 k
        (LocalCover.fam 1 y)) m)
      (fun _ _ _ => blockMarkC S 1 hp m.1 m.2) (2 * T.κdec - 1)
      (fun _ => S.p₁ * Real.exp ((2 * T.κdec - 1) * (obsLab (Lab.sum Lab) hdj).dl
        (obsY1 1 S (Lb ⊕ Lb) (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y)) m)))
      (physVq S S.a₁ S.ν T.t q) (ball (0 : ℂ) (3 / 2)) (physCarrier S 1 hp))) ∧
    Nonempty (ParamMarkFamily (S.blockSplit 1 hp).μ (obsLab (Lab.sum Lab) hdj)
      (fun θ t => tiltActObs Aact (show 3 ^ 1 ∣ N₁ by simpa using h3N) T.κ0_ent hεH.le hdj hK
        Rg hR (ball (0 : ℂ) (3 / 2)) θ t 1)
      (obsRemLab (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y))
        (fun Y => Sum.inl (Sum.inr Y))
        (obsY0 1 (Lb ⊕ Lb) (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y))
          (rootCube (m₀ := 1) (blockIndex y))))
      (obsGrFam S 1 hp Ev (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y))
        (XiCRaw S.G' (compWeight 3 1) ν (k + 1) 1 T.t)) (2 * T.κdec - 1)
      (fun _ => 8 * (cK2' 3 3 2 (famConst 3 3 T.BG₂ T.κ) * T.t) *
        (S.p₁ / lvCpsi T.κ T.t (β * 3 ^ k)) ^ 2)
      (physVq S S.a₁ S.ν T.t q) (ball (0 : ℂ) (3 / 2)) (physCarrier S 1 hp)) := by
  have hb' : β * ((3 : ℕ) : ℝ) ^ (k * (3 - 2)) = β * 3 ^ k := by norm_num
  have h := obsFamilies_of_EvG T.toG k hk N₁ ν β p₁ (T.scaleDataG_of_fixed Dsc) S hS hp y h3N Lab
    hεH Aact hdj hK Rg hR (rhoSepG_three _).symm hνpos (by simpa using hν) hhol hcont Ev
    (by rw [hb']; exact ha) (by rw [hb']; exact hb)
  rw [hb'] at h
  exact h

set_option quotPrecheck false in
local notation "𝒴ₒ" => obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y)
set_option quotPrecheck false in
local notation "Actₒ" => fun (θ : physParam 2 S) (t σ : ℂ) =>
  tiltActObs Aact (show 3 ^ 1 ∣ N₁ by simpa using h3N) T.κ0_ent hεH.le hdj hK Rg hR
    (ball (0 : ℂ) (3 / 2)) θ t σ

include Dsc hS in
/-- **The three parts of the coefficient of the observable and their sum are analytic on
`physVq`**, for the one sharp-hat family `Ev` of the kernel and the remainder: for every finite
set `T'` of cubes, with `μ = (S.blockSplit 1 hp).μ`, the kernel `θ ↦ obsHker 𝒴 (hatCoeff (Ev ·)
(θ.1) e_m) 1`,

* each first-order term `θ ↦ markIntTerm μ (Act θ) (obsY1 m) (blockMarkC m) S'` is analytic,
* `θ ↦ kernelMarkSum (kernel at θ.1) (first-order terms) T'` is analytic,
* `θ ↦ gsumCoeff μ _ (Act θ · 1) _ (obsGrFam θ) T'` (the remainder) is analytic,
* `θ ↦ obsCoeffParam … θ T'` (their sum) is analytic.

Numerical hypothesis carried: `hε`, the amplitude of the tilted extension is below
`stepTheta 3 3 Kobs (2 κdec - 1) κ0 κ'`. -/
theorem obsCoeffParam_analytic_of_Ev (hνpos : 0 < ν) (hν : ν * 3 ^ (2 * (k + 1)) ≤ 1)
    {q : ℝ} (hRg : 1 < Rg) (hKc : K0 3 3 T.κ0 + 1 ≤ Kc)
    (hhol : ∀ y', ∀ Φ ∈ physCarrier S 1 hp, AnalyticOnNhd ℂ (fun r : physParam 2 S × ℂ =>
      (tiltActObs Aact (show 3 ^ 1 ∣ N₁ by simpa using h3N) T.κ0_ent hεH.le hdj hK Rg hR
        (ball (0 : ℂ) (3 / 2)) r.1 r.2 1).H y' Φ)
      (physVq S S.a₁ S.ν T.t q ×ˢ ball (0 : ℂ) (3 / 2)))
    (hcont : ∀ y', ∀ θ ∈ physVq S S.a₁ S.ν T.t q, ∀ u ∈ ball (0 : ℂ) (3 / 2),
      ContinuousOn ((tiltActObs Aact (show 3 ^ 1 ∣ N₁ by simpa using h3N) T.κ0_ent hεH.le hdj hK
        Rg hR (ball (0 : ℂ) (3 / 2)) θ u 1).H y') (physCarrier S 1 hp))
    (hε : Rg * max (εH + εH) εH ≤ stepTheta 3 3 Kobs (2 * T.κdec - 1) T.κ0 T.κ')
    (Ev : Set (CTorus 3 3 N₁ T.m₁ (k + 1)) →
        RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2 × (unitPts S.G' × Fin 2 → ℂ) → ℂ)
    (ha : ∀ Y, AnalyticOnNhd ℂ (Ev Y) (XiCRaw S.G' (compWeight 3 1) ν (k + 1) 1 T.t ×ˢ
          {ψh : unitPts S.G' × Fin 2 → ℂ | ∀ p, ‖ψh p‖ ≤ lvCpsi T.κ T.t (β * 3 ^ k)}))
    (hd : ∀ Y, ∀ u ∈ XiCRaw S.G' (compWeight 3 1) ν (k + 1) 1 T.t ×ˢ
          {ψh : unitPts S.G' × Fin 2 → ℂ | ∀ p, ‖ψh p‖ ≤ lvCpsi T.κ T.t (β * 3 ^ k)},
        ∀ u' ∈ XiCRaw S.G' (compWeight 3 1) ν (k + 1) 1 T.t ×ˢ
          {ψh : unitPts S.G' × Fin 2 → ℂ | ∀ p, ‖ψh p‖ ≤ lvCpsi T.κ T.t (β * 3 ^ k)},
        AgHatDir S.hG' Y u u' → Ev Y u = Ev Y u')
    (hb : ∀ Y, ∀ u ∈ XiCRaw S.G' (compWeight 3 1) ν (k + 1) 1 T.t ×ˢ
          {ψh : unitPts S.G' × Fin 2 → ℂ | ∀ p, ‖ψh p‖ ≤ lvCpsi T.κ T.t (β * 3 ^ k)},
        ‖Ev Y u‖ ≤ (cK2' 3 3 2 (famConst 3 3 T.BG₂ T.κ) * T.t) *
          Real.exp (-(2 * T.κdec) * treeLenCovOne 1 (k + 1) Y))
    (T' : Finset (CubeB (d := 3) (L := 3) (N₁ := N₁) (m₁ := T.m₁) (K := k + 1) 1 (k + 1)
      Set.univ)) :
    (∀ (m : ObsMarkIdx S) (S' : Finset (CubeB (d := 3) (L := 3) (N₁ := N₁) (m₁ := T.m₁)
        (K := k + 1) 1 (k + 1) Set.univ)),
      AnalyticOnNhd ℂ (fun θ => markIntTerm (S.blockSplit 1 hp).μ (Actₒ θ)
        (obsY1 1 S (Lb ⊕ Lb) 𝒴ₒ m) (blockMarkC S 1 hp m.1 m.2) S')
        (physVq S S.a₁ S.ν T.t q)) ∧
    AnalyticOnNhd ℂ (fun θ => kernelMarkSum
      (fun m T'' => obsHker 𝒴ₒ (fun Y => hatCoeff (Ev Y)
        (θ.1 : RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2) (obsUnitVec S m)) 1 T'')
      (fun m S' => markIntTerm (S.blockSplit 1 hp).μ (Actₒ θ) (obsY1 1 S (Lb ⊕ Lb) 𝒴ₒ m)
        (blockMarkC S 1 hp m.1 m.2) S') T') (physVq S S.a₁ S.ν T.t q) ∧
    AnalyticOnNhd ℂ (fun θ => gsumCoeff (S.blockSplit 1 hp).μ (obsLab (Lab.sum Lab) hdj)
      (fun t => Actₒ θ t 1)
      (obsRemLab 𝒴ₒ (fun Y => Sum.inl (Sum.inr Y))
        (obsY0 1 (Lb ⊕ Lb) 𝒴ₒ (rootCube (m₀ := 1) (blockIndex y))))
      (obsGrFam S 1 hp Ev 𝒴ₒ (XiCRaw S.G' (compWeight 3 1) ν (k + 1) 1 T.t) θ) T')
      (physVq S S.a₁ S.ν T.t q) ∧
    AnalyticOnNhd ℂ (fun θ => obsCoeffParam (S.blockSplit 1 hp).μ Actₒ
      (fun m => obsY1 1 S (Lb ⊕ Lb) 𝒴ₒ m) (fun m => blockMarkC S 1 hp m.1 m.2)
      (fun θ m T'' => obsHker 𝒴ₒ (fun Y => hatCoeff (Ev Y)
        (θ.1 : RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2) (obsUnitVec S m)) 1 T'')
      (obsRemLab 𝒴ₒ (fun Y => Sum.inl (Sum.inr Y))
        (obsY0 1 (Lb ⊕ Lb) 𝒴ₒ (rootCube (m₀ := 1) (blockIndex y))))
      (fun θ => obsGrFam S 1 hp Ev 𝒴ₒ (XiCRaw S.G' (compWeight 3 1) ν (k + 1) 1 T.t) θ) θ T')
      (physVq S S.a₁ S.ν T.t q) := by
  have hb' : β * ((3 : ℕ) : ℝ) ^ (k * (3 - 2)) = β * 3 ^ k := by norm_num
  exact obsCoeffParam_analytic_of_EvG T.toG k hk N₁ ν β p₁ (T.scaleDataG_of_fixed Dsc) S hS hp y
    h3N Lab hεH Aact hdj hK Rg hR (rhoSepG_three _).symm hνpos (by simpa using hν) hRg hKc hhol
    hcont hε Ev (by rw [hb']; exact ha) (by rw [hb']; exact hd) (by rw [hb']; exact hb) T'

include Dsc hS in
/-- **The two families and the analyticity of the coefficient, for the one sharp-hat family.**
There is one family `Ev` (that of `obsMarkHalves_of_sharpHat_param`, with `ObsMarkHalf` and
`ObsRayIdentity` at every datum of `Ξ`) such that both `ParamMarkFamily` records exist and, for
every finite set of cubes, the first-order terms, the kernel sum, the remainder coefficient and
`obsCoeffParam` are analytic on `physVq … q`.  The numerical hypotheses carried are `hKc`
(`K₀ + 1 ≤ K_c`, any `K_c ≥ K₀ + 1`), `hε` (the amplitude of the tilted extension is at most
`stepTheta 3 3 Kobs (2 κdec - 1) κ0 κ'`) and `1 < Rg`; the activity fields `hhol`, `hcont` are
those of `obsTiltLabels_fromTower`.  This statement is conditional on them; they are discharged
at the tower, by a compatible instantiation of `obsTiltLabels_fromTower`, in
`obsCoeffFamily_fromTower`. -/
theorem obsCoeffParam_fromTower (hN : 5 < N₁) (hνpos : 0 < ν) (hν : ν * 3 ^ (2 * (k + 1)) ≤ 1)
    {q : ℝ} (hRg : 1 < Rg) (hKc : K0 3 3 T.κ0 + 1 ≤ Kc)
    (hhol : ∀ y', ∀ Φ ∈ physCarrier S 1 hp, AnalyticOnNhd ℂ (fun r : physParam 2 S × ℂ =>
      (tiltActObs Aact (show 3 ^ 1 ∣ N₁ by simpa using h3N) T.κ0_ent hεH.le hdj hK Rg hR
        (ball (0 : ℂ) (3 / 2)) r.1 r.2 1).H y' Φ)
      (physVq S S.a₁ S.ν T.t q ×ˢ ball (0 : ℂ) (3 / 2)))
    (hcont : ∀ y', ∀ θ ∈ physVq S S.a₁ S.ν T.t q, ∀ u ∈ ball (0 : ℂ) (3 / 2),
      ContinuousOn ((tiltActObs Aact (show 3 ^ 1 ∣ N₁ by simpa using h3N) T.κ0_ent hεH.le hdj hK
        Rg hR (ball (0 : ℂ) (3 / 2)) θ u 1).H y') (physCarrier S 1 hp))
    (hε : Rg * max (εH + εH) εH ≤ stepTheta 3 3 Kobs (2 * T.κdec - 1) T.κ0 T.κ')
    (i : Fin 2) :
    ∃ Ev : Set (CTorus 3 3 N₁ T.m₁ (k + 1)) →
        RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2 × (unitPts S.G' × Fin 2 → ℂ) → ℂ,
      (∀ Y, AnalyticOnNhd ℂ (Ev Y) (XiCRaw S.G' (compWeight 3 1) ν (k + 1) 1 T.t ×ˢ
          {ψh : unitPts S.G' × Fin 2 → ℂ | ∀ p, ‖ψh p‖ ≤ lvCpsi T.κ T.t (β * 3 ^ k)})) ∧
      (∀ Y, ∀ u ∈ XiCRaw S.G' (compWeight 3 1) ν (k + 1) 1 T.t ×ˢ
          {ψh : unitPts S.G' × Fin 2 → ℂ | ∀ p, ‖ψh p‖ ≤ lvCpsi T.κ T.t (β * 3 ^ k)},
        ∀ u' ∈ XiCRaw S.G' (compWeight 3 1) ν (k + 1) 1 T.t ×ˢ
          {ψh : unitPts S.G' × Fin 2 → ℂ | ∀ p, ‖ψh p‖ ≤ lvCpsi T.κ T.t (β * 3 ^ k)},
        AgHatDir S.hG' Y u u' → Ev Y u = Ev Y u') ∧
      (∀ Y, ∀ u ∈ XiCRaw S.G' (compWeight 3 1) ν (k + 1) 1 T.t ×ˢ
          {ψh : unitPts S.G' × Fin 2 → ℂ | ∀ p, ‖ψh p‖ ≤ lvCpsi T.κ T.t (β * 3 ^ k)},
        ‖Ev Y u‖ ≤ (cK2' 3 3 2 (famConst 3 3 T.BG₂ T.κ) * T.t) *
          Real.exp (-(2 * T.κdec) * treeLenCovOne 1 (k + 1) Y)) ∧
      (∀ D : BgData S.G' 2, XiCData S.G' (compWeight 3 1) ν (k + 1) 1 T.t D →
        ObsMarkHalf S 1 hp Ev D (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y))
          (obsLab (Lab.sum Lab) hdj) (lvCpsi T.κ T.t (β * 3 ^ k))
          (cK2' 3 3 2 (famConst 3 3 T.BG₂ T.κ) * T.t) (2 * T.κdec - 1) T.κ0
          (cK2' 3 3 2 (famConst 3 3 T.BG₂ T.κ) * T.t / (lvCpsi T.κ T.t (β * 3 ^ k)))
          (2 * T.κdec) (rootCube (m₀ := 1) (blockIndex y)) ∧
        ObsRayIdentity S 1 hp
          (fun ψh => svec (lvLow N₁ T.m₁ k (rhoSep T.m₁))
            (flFieldOne S.G' (lvLow N₁ T.m₁ k (rhoSep T.m₁)) T.BG₂ T.κ 1 ν D
              (hatLift S.G' 1 ν S.hG' ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) D ψh)) y i) Ev D
          (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y))) ∧
      ((∀ m : ObsMarkIdx S, Nonempty (ParamMarkFamily (S.blockSplit 1 hp).μ
        (obsLab (Lab.sum Lab) hdj)
        (fun θ t => tiltActObs Aact (show 3 ^ 1 ∣ N₁ by simpa using h3N) T.κ0_ent hεH.le hdj hK
          Rg hR (ball (0 : ℂ) (3 / 2)) θ t 1)
        (fun _ : Unit => obsY1 1 S (Lb ⊕ Lb) (obsDomains S (LocalCover.nbhdF 1 y) 1 k
          (LocalCover.fam 1 y)) m)
        (fun _ _ _ => blockMarkC S 1 hp m.1 m.2) (2 * T.κdec - 1)
        (fun _ => S.p₁ * Real.exp ((2 * T.κdec - 1) * (obsLab (Lab.sum Lab) hdj).dl
          (obsY1 1 S (Lb ⊕ Lb) (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y)) m)))
        (physVq S S.a₁ S.ν T.t q) (ball (0 : ℂ) (3 / 2)) (physCarrier S 1 hp))) ∧
      Nonempty (ParamMarkFamily (S.blockSplit 1 hp).μ (obsLab (Lab.sum Lab) hdj)
        (fun θ t => tiltActObs Aact (show 3 ^ 1 ∣ N₁ by simpa using h3N) T.κ0_ent hεH.le hdj hK
          Rg hR (ball (0 : ℂ) (3 / 2)) θ t 1)
        (obsRemLab (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y))
          (fun Y => Sum.inl (Sum.inr Y))
          (obsY0 1 (Lb ⊕ Lb) (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y))
            (rootCube (m₀ := 1) (blockIndex y))))
        (obsGrFam S 1 hp Ev (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y))
          (XiCRaw S.G' (compWeight 3 1) ν (k + 1) 1 T.t)) (2 * T.κdec - 1)
        (fun _ => 8 * (cK2' 3 3 2 (famConst 3 3 T.BG₂ T.κ) * T.t) *
          (S.p₁ / lvCpsi T.κ T.t (β * 3 ^ k)) ^ 2)
        (physVq S S.a₁ S.ν T.t q) (ball (0 : ℂ) (3 / 2)) (physCarrier S 1 hp))) ∧
      ∀ T' : Finset (CubeB (d := 3) (L := 3) (N₁ := N₁) (m₁ := T.m₁) (K := k + 1) 1 (k + 1)
        Set.univ),
      ((∀ (m : ObsMarkIdx S) (S' : Finset (CubeB (d := 3) (L := 3) (N₁ := N₁) (m₁ := T.m₁)
        (K := k + 1) 1 (k + 1) Set.univ)),
      AnalyticOnNhd ℂ (fun θ => markIntTerm (S.blockSplit 1 hp).μ (Actₒ θ)
        (obsY1 1 S (Lb ⊕ Lb) 𝒴ₒ m) (blockMarkC S 1 hp m.1 m.2) S')
        (physVq S S.a₁ S.ν T.t q)) ∧
    AnalyticOnNhd ℂ (fun θ => kernelMarkSum
      (fun m T'' => obsHker 𝒴ₒ (fun Y => hatCoeff (Ev Y)
        (θ.1 : RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2) (obsUnitVec S m)) 1 T'')
      (fun m S' => markIntTerm (S.blockSplit 1 hp).μ (Actₒ θ) (obsY1 1 S (Lb ⊕ Lb) 𝒴ₒ m)
        (blockMarkC S 1 hp m.1 m.2) S') T') (physVq S S.a₁ S.ν T.t q) ∧
    AnalyticOnNhd ℂ (fun θ => gsumCoeff (S.blockSplit 1 hp).μ (obsLab (Lab.sum Lab) hdj)
      (fun t => Actₒ θ t 1)
      (obsRemLab 𝒴ₒ (fun Y => Sum.inl (Sum.inr Y))
        (obsY0 1 (Lb ⊕ Lb) 𝒴ₒ (rootCube (m₀ := 1) (blockIndex y))))
      (obsGrFam S 1 hp Ev 𝒴ₒ (XiCRaw S.G' (compWeight 3 1) ν (k + 1) 1 T.t) θ) T')
      (physVq S S.a₁ S.ν T.t q) ∧
    AnalyticOnNhd ℂ (fun θ => obsCoeffParam (S.blockSplit 1 hp).μ Actₒ
      (fun m => obsY1 1 S (Lb ⊕ Lb) 𝒴ₒ m) (fun m => blockMarkC S 1 hp m.1 m.2)
      (fun θ m T'' => obsHker 𝒴ₒ (fun Y => hatCoeff (Ev Y)
        (θ.1 : RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2) (obsUnitVec S m)) 1 T'')
      (obsRemLab 𝒴ₒ (fun Y => Sum.inl (Sum.inr Y))
        (obsY0 1 (Lb ⊕ Lb) 𝒴ₒ (rootCube (m₀ := 1) (blockIndex y))))
      (fun θ => obsGrFam S 1 hp Ev 𝒴ₒ (XiCRaw S.G' (compWeight 3 1) ν (k + 1) 1 T.t) θ) θ T')
      (physVq S S.a₁ S.ν T.t q)) := by
  have hb' : β * ((3 : ℕ) : ℝ) ^ (k * (3 - 2)) = β * 3 ^ k := by norm_num
  have h := obsCoeffParam_fromTowerG T.toG k hk N₁ ν β p₁ (T.scaleDataG_of_fixed Dsc) S hS hp y
    h3N Lab hεH Aact hdj hK Rg hR (rhoSepG_three _).symm hN hνpos (by simpa using hν) hRg hKc hhol
    hcont hε i
  rw [hb'] at h
  exact h

include Dsc hS in
/-- **The uniform bounds of the three parts and of their sum on `physVq`**, with the constants of
the fixed-parameter bounds (`norm_markIntTerm_le`, `norm_gsumCoeff_le`, `norm_kernelMarkSum_le`),
for the sharp-hat family `Ev` (the clauses and `hD` as given by `obsEv_fromTower`).  With
`C₀ = Q t`, `c_ψ = lvCpsi`, `F_r = 8 C₀ (p₁/c_ψ)²`, `κ' = T.κ'`, `n_* = 2 · 3^{3(1+m₁+1)}`:

* the first-order term: `≤ CPE · p₁ · e^{-κ' dExt S'} / R_g`;
* the remainder coefficient: `≤ CPE · (∑_r F_r e^{-κ₀ 𝗱(y_r)}) · e^{-κ' dExt T'}`;
* the kernel sum, with `C_h = C₀ / c_ψ`, `κ_h = 2 κ_dec`, `C_g = CPE p₁ / R_g`,
  `κ = min κ_h κ'`: `≤ C_h C_g (n_* c₁) K_obs² e^{(κ-κ₀) c_G} e^{-(κ-κ₀-1) dExt W}`;
* `obsCoeffParam` is bounded by the sum of the last two.

Carried: the same numerical hypotheses as `obsCoeffParam_fromTower`; the activity fields `hσ`
(holomorphy in `σ` on the disc of radius `R_g`) and `hzero` (vanishing at `σ = 0`) of
`obsTiltLabels_fromTower`. -/
theorem obsCoeffParam_norm_le_of_Ev {q : ℝ} (hRg : 1 < Rg) (hKc : K0 3 3 T.κ0 + 1 ≤ Kc)
    (hσ : ∀ e ∈ physVq S S.a₁ S.ν T.t q, ∀ t ∈ ball (0 : ℂ) (3 / 2), ∀ y' Φ, DifferentiableOn ℂ
      (fun σ => (tiltActObs Aact (show 3 ^ 1 ∣ N₁ by simpa using h3N) T.κ0_ent hεH.le hdj hK Rg
        hR (ball (0 : ℂ) (3 / 2)) e t σ).H y' Φ) (ball (0 : ℂ) Rg))
    (hzero : ∀ e ∈ physVq S S.a₁ S.ν T.t q, ∀ t y' Φ,
      (tiltActObs Aact (show 3 ^ 1 ∣ N₁ by simpa using h3N) T.κ0_ent hεH.le hdj hK Rg hR
        (ball (0 : ℂ) (3 / 2)) e t 0).H y' Φ = 0)
    (hε : Rg * max (εH + εH) εH ≤ stepTheta 3 3 Kobs (2 * T.κdec - 1) T.κ0 T.κ')
    (Ev : Set (CTorus 3 3 N₁ T.m₁ (k + 1)) →
        RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2 × (unitPts S.G' × Fin 2 → ℂ) → ℂ)
    (ha : ∀ Y, AnalyticOnNhd ℂ (Ev Y) (XiCRaw S.G' (compWeight 3 1) ν (k + 1) 1 T.t ×ˢ
          {ψh : unitPts S.G' × Fin 2 → ℂ | ∀ p, ‖ψh p‖ ≤ lvCpsi T.κ T.t (β * 3 ^ k)}))
    (hd : ∀ Y, ∀ u ∈ XiCRaw S.G' (compWeight 3 1) ν (k + 1) 1 T.t ×ˢ
          {ψh : unitPts S.G' × Fin 2 → ℂ | ∀ p, ‖ψh p‖ ≤ lvCpsi T.κ T.t (β * 3 ^ k)},
        ∀ u' ∈ XiCRaw S.G' (compWeight 3 1) ν (k + 1) 1 T.t ×ˢ
          {ψh : unitPts S.G' × Fin 2 → ℂ | ∀ p, ‖ψh p‖ ≤ lvCpsi T.κ T.t (β * 3 ^ k)},
        AgHatDir S.hG' Y u u' → Ev Y u = Ev Y u')
    (hb : ∀ Y, ∀ u ∈ XiCRaw S.G' (compWeight 3 1) ν (k + 1) 1 T.t ×ˢ
          {ψh : unitPts S.G' × Fin 2 → ℂ | ∀ p, ‖ψh p‖ ≤ lvCpsi T.κ T.t (β * 3 ^ k)},
        ‖Ev Y u‖ ≤ (cK2' 3 3 2 (famConst 3 3 T.BG₂ T.κ) * T.t) *
          Real.exp (-(2 * T.κdec) * treeLenCovOne 1 (k + 1) Y))
    (hD : ∀ D : BgData S.G' 2, XiCData S.G' (compWeight 3 1) ν (k + 1) 1 T.t D →
        ObsMarkHalf S 1 hp Ev D (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y))
          (obsLab (Lab.sum Lab) hdj) (lvCpsi T.κ T.t (β * 3 ^ k))
          (cK2' 3 3 2 (famConst 3 3 T.BG₂ T.κ) * T.t) (2 * T.κdec - 1) T.κ0
          (cK2' 3 3 2 (famConst 3 3 T.BG₂ T.κ) * T.t / (lvCpsi T.κ T.t (β * 3 ^ k)))
          (2 * T.κdec) (rootCube (m₀ := 1) (blockIndex y)))
    (W : Finset (CubeB (d := 3) (L := 3) (N₁ := N₁) (m₁ := T.m₁) (K := k + 1) 1 (k + 1)
      Set.univ)) :
    (∀ θ ∈ physVq S S.a₁ S.ν T.t q, ∀ (m : ObsMarkIdx S) (S' : Finset (CubeB (d := 3) (L := 3)
        (N₁ := N₁) (m₁ := T.m₁) (K := k + 1) 1 (k + 1) Set.univ)),
      ‖markIntTerm (S.blockSplit 1 hp).μ (Actₒ θ) (obsY1 1 S (Lb ⊕ Lb) 𝒴ₒ m)
        (blockMarkC S 1 hp m.1 m.2) S'‖ ≤
        CPE 3 3 Kobs (2 * T.κdec - 1) T.κ0 T.κ' * S.p₁ * Real.exp (-T.κ' * dExt S') / Rg) ∧
    (∀ θ ∈ physVq S S.a₁ S.ν T.t q,
      ‖gsumCoeff (S.blockSplit 1 hp).μ (obsLab (Lab.sum Lab) hdj) (fun t => Actₒ θ t 1)
        (obsRemLab 𝒴ₒ (fun Y => Sum.inl (Sum.inr Y))
          (obsY0 1 (Lb ⊕ Lb) 𝒴ₒ (rootCube (m₀ := 1) (blockIndex y))))
        (obsGrFam S 1 hp Ev 𝒴ₒ (XiCRaw S.G' (compWeight 3 1) ν (k + 1) 1 T.t) θ) W‖ ≤
        CPE 3 3 Kobs (2 * T.κdec - 1) T.κ0 T.κ' *
          (∑ r, 8 * (cK2' 3 3 2 (famConst 3 3 T.BG₂ T.κ) * T.t) *
            (S.p₁ / lvCpsi T.κ T.t (β * 3 ^ k)) ^ 2 * Real.exp (-T.κ0 *
            (obsLab (Lab.sum Lab) hdj).dl (obsRemLab 𝒴ₒ (fun Y => Sum.inl (Sum.inr Y))
              (obsY0 1 (Lb ⊕ Lb) 𝒴ₒ (rootCube (m₀ := 1) (blockIndex y))) r))) *
          Real.exp (-T.κ' * dExt W)) ∧
    (∀ θ ∈ physVq S S.a₁ S.ν T.t q,
      ‖kernelMarkSum
        (fun m T'' => obsHker 𝒴ₒ (fun Y => hatCoeff (Ev Y)
          (θ.1 : RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2) (obsUnitVec S m)) 1 T'')
        (fun m S' => markIntTerm (S.blockSplit 1 hp).μ (Actₒ θ) (obsY1 1 S (Lb ⊕ Lb) 𝒴ₒ m)
          (blockMarkC S 1 hp m.1 m.2) S') W‖ ≤
        (cK2' 3 3 2 (famConst 3 3 T.BG₂ T.κ) * T.t / lvCpsi T.κ T.t (β * 3 ^ k)) *
          (CPE 3 3 Kobs (2 * T.κdec - 1) T.κ0 T.κ' * S.p₁ / Rg) *
          (((2 * 3 ^ (3 * (1 + T.m₁ + 1)) : ℕ) : ℝ) * c1 3 3) * Kobs ^ 2 *
          Real.exp ((min (2 * T.κdec) T.κ' - T.κ0) * cG 3 3) *
          Real.exp (-(min (2 * T.κdec) T.κ' - T.κ0 - 1) * dExt W)) := by
  have hb' : β * ((3 : ℕ) : ℝ) ^ (k * (3 - 2)) = β * 3 ^ k := by norm_num
  have h := obsCoeffParam_norm_le_of_EvG T.toG k hk N₁ ν β p₁ (T.scaleDataG_of_fixed Dsc) S hS hp
    y h3N Lab hεH Aact hdj hK Rg hR hRg hKc hσ hzero hε Ev (by rw [hb']; exact ha)
    (by rw [hb']; exact hd) (by rw [hb']; exact hb) (by rw [hb']; exact hD) W
  rw [hb'] at h
  exact h

end Tower

end Balaban.Inhabited
