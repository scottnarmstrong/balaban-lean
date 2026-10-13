/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.Thm31CoeffAnalytic
public import Balaban.Fluctuation.HatLabelsTerms
public import Balaban.Fluctuation.HatLabelsSplit
public import Balaban.Fluctuation.MeasureProduct
public import Balaban.Fluctuation.Thm31Witness
public import Balaban.Fluctuation.Thm31b
import Mathlib.Tactic.Linarith

/-!
# A compact carrier for the block measures of a step, and locality of `gsumCoeff` in a parameter

The single-site fluctuation measure `ν₁` has the sharp cutoff `‖ψ̂(u)‖ < p₁`, so the block measure
`ν_b = ⨂_{u ∈ b} ν₁` of `StepSetting.blockSplit` is carried by the product of closed balls
`{‖ψ̂(u)‖ ≤ p₁}`, which is compact.  Hence the compact carrier `Q` asked for by
`ParamMarkFamily` exists for the actual step measure.

* `physCarrier`: the set of block configurations all of whose site components have norm `≤ p₁`;
  it is compact, measurable and carries `Measure.pi BS.μ` almost everywhere
  (`isCompact_physCarrier`, `measurableSet_physCarrier`, `ae_mem_physCarrier`).  The block spaces
  `{u // cellOf u = b} → ℝ^N` carry the product topology, are second countable and have the Borel
  structure (instances below).
* `gsumCoeff_param_congr_of_local`: two parameters whose activities and marks agree on every label
  inside the enlarged region `Ŷ(sitesOf T)` give the same `gsumCoeff` at `T`.
* `paramMarked_analytic_local_bound`: for a `ParamMarkFamily` whose activities and marks on the
  enlarged region depend on `θ` only through `π θ`, the coefficient is analytic, factors through
  `π` and is bounded by the uniform bound of `norm_gsumCoeff_le`.
* `nonempty_paramMarkFamily_physical_const`, `nonempty_paramMarkFamily_physical_scaled`: the
  family structure is inhabited on the block spaces and measures of an actual step (whole-torus
  label, constant activity, zero marks, carrier `physCarrier`), and `physical_const_analytic_bound`,
  `physical_scaled_analytic_bound` apply the theorem above to them.

No physical family of marks is constructed here (that is `ParamMarksPhysical`), the determinant
term is not treated, and nothing depends on a choice of generating set for the class terms.
-/

@[expose] public section

namespace Balaban.Fluctuation

open MeasureTheory Balaban Balaban.Localization Balaban.Polymer Balaban.Multiscale

section Carrier

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}
  (S : StepSetting d L N₁ m₁ k N ϱ) (m₀ : ℕ) (hp : 0 < S.p₁)

instance instTopBlock (b) : TopologicalSpace ((S.blockSplit m₀ hp).Ωb b) :=
  inferInstanceAs (TopologicalSpace ({u : S.U // S.cellOf m₀ u = b} → Rn N))

instance instSecondCountableBlock (b) :
    SecondCountableTopology ((S.blockSplit m₀ hp).Ωb b) :=
  inferInstanceAs (SecondCountableTopology ({u : S.U // S.cellOf m₀ u = b} → Rn N))

instance instOpensMeasBlock (b) : OpensMeasurableSpace ((S.blockSplit m₀ hp).Ωb b) :=
  inferInstanceAs (OpensMeasurableSpace ({u : S.U // S.cellOf m₀ u = b} → Rn N))

/-- **The carrier of the step measure**: the block configurations all of whose site components
have norm at most `p₁`. -/
def physCarrier : Set (∀ b, (S.blockSplit m₀ hp).Ωb b) :=
  {Φ | ∀ b u, ‖Φ b u‖ ≤ S.p₁}

theorem physCarrier_eq_pi : physCarrier S m₀ hp =
    Set.pi Set.univ (fun b => Set.pi Set.univ
      (fun _ : {u : S.U // S.cellOf m₀ u = b} => Metric.closedBall (0 : Rn N) S.p₁)) := by
  ext Φ
  constructor
  · intro h b _ u _
    exact mem_closedBall_zero_iff.2 (h b u)
  · intro h b u
    exact mem_closedBall_zero_iff.1 (h b (Set.mem_univ _) u (Set.mem_univ _))

theorem isCompact_physCarrier : IsCompact (physCarrier S m₀ hp) := by
  rw [physCarrier_eq_pi]
  exact isCompact_univ_pi fun b => isCompact_univ_pi fun _ => isCompact_closedBall _ _

theorem measurableSet_physCarrier : MeasurableSet (physCarrier S m₀ hp) := by
  rw [physCarrier_eq_pi]
  exact MeasurableSet.univ_pi fun b => MeasurableSet.univ_pi fun _ => measurableSet_closedBall

theorem ae_mem_physCarrier :
    ∀ᵐ Φ ∂(Measure.pi (S.blockSplit m₀ hp).μ), Φ ∈ physCarrier S m₀ hp := by
  have := isProbabilityMeasure_fluctMeasure1 N hp
  have hb : ∀ b, ∀ᵐ Φ ∂((S.blockSplit m₀ hp).μ b), ∀ u, ‖Φ u‖ ≤ S.p₁ := fun b => by
    show ∀ᵐ Φ ∂(Measure.pi fun _ : {u : S.U // S.cellOf m₀ u = b} => fluctMeasure1 N S.p₁),
      ∀ u, ‖Φ u‖ ≤ S.p₁
    rw [ae_all_iff]
    intro u
    filter_upwards [(measurePreserving_eval
      (fun _ : {u : S.U // S.cellOf m₀ u = b} => fluctMeasure1 N S.p₁) u).quasiMeasurePreserving.ae
      (ae_norm_lt_fluctMeasure1 N S.p₁)] with x hx using hx.le
  rw [show (∀ᵐ Φ ∂(Measure.pi (S.blockSplit m₀ hp).μ), Φ ∈ physCarrier S m₀ hp) ↔
    ∀ᵐ Φ ∂(Measure.pi (S.blockSplit m₀ hp).μ), ∀ b, ∀ u, ‖Φ b u‖ ≤ S.p₁ from Iff.rfl,
    ae_all_iff]
  intro b
  exact (measurePreserving_eval (S.blockSplit m₀ hp).μ b).quasiMeasurePreserving.ae (hb b)

end Carrier

section Local

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {m₀ j : ℕ} {Ω : Set (CTorus d L N₁ m₁ K)}
  {Lb : Type*} [Fintype Lb] {ι : Type*} [Fintype ι]

local notation "𝔅" => CubeB (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ j Ω

/-- **Locality of `gsumCoeff` in a parameter** (the family form of `gsumCoeff_ext_congr`).  If the
activities and the marks at two parameters `θ, θ'` agree, for `s ∈ [0,1]`, on every label whose
sites lie in the enlarged region `Ŷ(sitesOf T)`, then the coefficients at `T` agree. -/
theorem gsumCoeff_param_congr_of_local {E : Type*} {Ωb : 𝔅 → Type*}
    [∀ b, MeasurableSpace (Ωb b)] (μ : ∀ b, Measure (Ωb b)) [∀ b, IsProbabilityMeasure (μ b)]
    (hN : L ^ m₀ ∣ N₁) (hj : j ≤ K) (hΩ : IsPiUnion m₀ j Ω)
    {Lab : CubeLabels m₀ j Ω Lb} {εH κH κ0 Kc : ℝ}
    (A : E → ℂ → LabelAct Lab Ωb εH κH κ0 Kc) (y0 : ι → Lb)
    (G : E → ι → ℂ → (∀ b, Ωb b) → ℂ)
    (hGdep : ∀ θ i s, DepOn (blocksOf m₀ j Ω (Lab.ysite (y0 i))) (G θ i s))
    (T : Finset 𝔅) {θ θ' : E}
    (hA : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ y, Lab.ysite y ⊆ Yhat Ω (sitesOf T) →
      (A θ (s : ℂ)).H y = (A θ' (s : ℂ)).H y)
    (hG : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ i, Lab.ysite (y0 i) ⊆ Yhat Ω (sitesOf T) →
      G θ i (s : ℂ) = G θ' i (s : ℂ)) :
    gsumCoeff μ Lab (A θ) y0 (G θ) T = gsumCoeff μ Lab (A θ') y0 (G θ') T :=
  gsumCoeff_congr μ (A θ) (A θ') y0 (G θ) (G θ') T (hGdep θ)
    (fun s hs y hy => hA s hs y (ysite_subset_Yhat hN hj hΩ Lab y hy))
    (fun s hs i hi => hG s hs i (ysite_subset_Yhat hN hj hΩ Lab (y0 i) hi))

/-- **Analytic, local and bounded: one statement about a parameter family.**  Let
`ParamMarkFamily` hold on the open set `V`, and suppose the activities and marks at the labels
inside the enlarged region `Ŷ(sitesOf T)` depend on `θ ∈ V` only through `π θ`.  Then the
coefficient `θ ↦ gsumCoeff … T` is analytic on `V`, takes equal values at parameters of `V` with
equal `π`, and is bounded on `V` by the uniform bound of `norm_gsumCoeff_le`. -/
theorem paramMarked_analytic_local_bound {E P : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [FiniteDimensional ℂ E] {Ωb : 𝔅 → Type*} [∀ b, MeasurableSpace (Ωb b)]
    [∀ b, TopologicalSpace (Ωb b)] [∀ b, OpensMeasurableSpace (Ωb b)]
    [∀ b, SecondCountableTopology (Ωb b)]
    (μ : ∀ b, Measure (Ωb b)) [∀ b, IsProbabilityMeasure (μ b)]
    (hN : L ^ m₀ ∣ N₁) (hj : j ≤ K) (hΩ : IsPiUnion m₀ j Ω)
    {Lab : CubeLabels m₀ j Ω Lb} {εH κH κG κ0 κ' Kc : ℝ} {F0 : ι → ℝ}
    {A : E → ℂ → LabelAct Lab Ωb εH κH κ0 Kc} {y0 : ι → Lb}
    {G : E → ι → ℂ → (∀ b, Ωb b) → ℂ} {V : Set E} {𝒰 : Set ℂ} {Q : Set (∀ b, Ωb b)}
    (hfam : ParamMarkFamily μ Lab A y0 G κG F0 V 𝒰 Q)
    (hGdep : ∀ θ i s, DepOn (blocksOf m₀ j Ω (Lab.ysite (y0 i))) (G θ i s))
    (hκ0 : aEnt d L + 1 ≤ κ0) (hKc : K0 d L κ0 + 1 ≤ Kc) (hεpos : 0 < εH)
    (hι : Nonempty ι) (hF0 : ∀ i, 0 < F0 i) (hκ' : 0 ≤ κ') (hκG : κH ≤ κG)
    (hκ : κ' + 3 * κ0 + c1 d L + 3 / 2 ≤ κH)
    (hε : εH ≤ 1 / (8 * Kc ^ 3 * c1 d L *
      Real.exp ((κH - 2 * κ0) * cG d L + c1 d L + κ' * cG d L)))
    (T : Finset 𝔅) (π : E → P)
    (hA : ∀ θ ∈ V, ∀ θ' ∈ V, π θ = π θ' → ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 →
      ∀ y, Lab.ysite y ⊆ Yhat Ω (sitesOf T) → (A θ (s : ℂ)).H y = (A θ' (s : ℂ)).H y)
    (hG : ∀ θ ∈ V, ∀ θ' ∈ V, π θ = π θ' → ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 →
      ∀ i, Lab.ysite (y0 i) ⊆ Yhat Ω (sitesOf T) → G θ i (s : ℂ) = G θ' i (s : ℂ)) :
    AnalyticOnNhd ℂ (fun θ => gsumCoeff μ Lab (A θ) y0 (G θ) T) V ∧
      (∀ θ ∈ V, ∀ θ' ∈ V, π θ = π θ' →
        gsumCoeff μ Lab (A θ) y0 (G θ) T = gsumCoeff μ Lab (A θ') y0 (G θ') T) ∧
      ∀ θ ∈ V, ‖gsumCoeff μ Lab (A θ) y0 (G θ) T‖ ≤ CPE d L Kc κH κ0 κ' *
        (∑ i, F0 i * Real.exp (-κ0 * Lab.dl (y0 i))) * Real.exp (-κ' * dExt T) :=
  ⟨gsumCoeff_analyticOnNhd μ hN hj hΩ hfam hκ0 hKc hεpos hF0 hκ' hκG hκ hε T,
    fun θ hθ θ' hθ' h => gsumCoeff_param_congr_of_local μ hN hj hΩ A y0 G hGdep T
      (hA θ hθ θ' hθ' h) (hG θ hθ θ' hθ' h),
    norm_gsumCoeff_le μ hN hj hΩ A y0 G V hfam.meas hGdep hfam.bound hκ0 hKc hεpos hι hF0 hκ'
      hκG hκ hε T⟩

end Local

section Physical

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}
  (S : StepSetting d L N₁ m₁ k N ϱ) (hp : 0 < S.p₁)

/-- The whole-torus label activity on the block spaces of the actual step, constant in the
configuration, equal to `½ ε_H e^{-κ_H 𝗱(𝕋)}` (witness constants `wεH`, `wkH`, `wk0`, `wKc`). -/
noncomputable def physAct :
    LabelAct (wholeLabel (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k))
      (S.blockSplit 0 hp).Ωb (wεH d L / 2) (wkH d L) (wk0 d L) (wKc d L) where
  H := fun _ _ => ((wεH d L / 2 * Real.exp (-wkH d L * wholeLen d L N₁ m₁ k) : ℝ) : ℂ)
  meas := fun _ => measurable_const
  dep := fun _ _ _ _ => rfl
  bound := fun _ _ => by
    have h := wεH_pos d L
    rw [Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    rfl
  entropy := whole_entropy

/-- **The constant family on the physical block spaces**: constant activity `physAct`, zero
marks, carrier `physCarrier`, any open parameter set `V` of any normed space. -/
theorem nonempty_paramMarkFamily_physical_const {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] (V : Set E) (hV : IsOpen V) :
    Nonempty (ParamMarkFamily (S.blockSplit 0 hp).μ
      (wholeLabel (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k))
      (fun (_ : E) (_ : ℂ) => physAct S hp) (fun _ : Unit => ())
      (fun _ _ _ _ => (0 : ℂ)) (wkH d L) (fun _ => 1) V Set.univ (physCarrier S 0 hp)) := by
  have := isProbabilityMeasure_fluctMeasure1 N hp
  exact ⟨{ isOpenV := hV
           isOpenU := isOpen_univ
           seg := fun _ _ => Set.mem_univ _
           compact := isCompact_physCarrier S 0 hp
           measQ := measurableSet_physCarrier S 0 hp
           carried := ae_mem_physCarrier S 0 hp
           meas := fun _ _ _ => measurable_const
           bound := fun _ _ _ _ => by simp only [norm_zero]; positivity
           holA := fun _ _ _ => analyticOnNhd_const
           holG := fun _ _ _ => analyticOnNhd_const
           contA := fun _ _ _ _ _ => continuousOn_const
           contG := fun _ _ _ _ _ => continuousOn_const }⟩

/-- The activity `(1 + θ) · physAct` for `‖θ‖ < 1/2` (and `physAct` otherwise); size constant
`2 · (ε_H / 2) = ε_H`. -/
noncomputable def physActScaled (θ : ℂ) :
    LabelAct (wholeLabel (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k))
      (S.blockSplit 0 hp).Ωb (2 * (wεH d L / 2)) (wkH d L) (wk0 d L) (wKc d L) :=
  (physAct S hp).scale (if ‖θ‖ < 2⁻¹ then 1 + θ else 1) (by
    by_cases h : ‖θ‖ < 2⁻¹
    · simp only [h, ite_true]
      calc ‖(1 + θ : ℂ)‖ ≤ ‖(1 : ℂ)‖ + ‖θ‖ := norm_add_le _ _
        _ ≤ 2 := by simp; linarith
    · simp [h])

/-- **A genuinely parameter-dependent family on the physical block spaces**: activities
`(1 + θ) · physAct` for `θ ∈ ℂ`, `‖θ‖ < 1/2`, zero marks, carrier `physCarrier`. -/
theorem nonempty_paramMarkFamily_physical_scaled :
    Nonempty (ParamMarkFamily (S.blockSplit 0 hp).μ
      (wholeLabel (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k))
      (fun (θ : ℂ) (_ : ℂ) => physActScaled S hp θ) (fun _ : Unit => ())
      (fun _ _ _ _ => (0 : ℂ)) (wkH d L) (fun _ => 1) (Metric.ball (0 : ℂ) (2⁻¹)) Set.univ
      (physCarrier S 0 hp)) := by
  have := isProbabilityMeasure_fluctMeasure1 N hp
  refine ⟨{ isOpenV := Metric.isOpen_ball
            isOpenU := isOpen_univ
            seg := fun _ _ => Set.mem_univ _
            compact := isCompact_physCarrier S 0 hp
            measQ := measurableSet_physCarrier S 0 hp
            carried := ae_mem_physCarrier S 0 hp
            meas := fun _ _ _ => measurable_const
            bound := fun _ _ _ _ => by simp only [norm_zero]; positivity
            holA := fun y Φ _ => ?_
            holG := fun _ _ _ => analyticOnNhd_const
            contA := fun _ _ _ _ _ => by
              simp only [physActScaled, LabelAct.scale, physAct]
              exact continuousOn_const
            contG := fun _ _ _ _ _ => continuousOn_const }⟩
  have h1 : AnalyticOnNhd ℂ (fun p : ℂ × ℂ => (1 + p.1) * ((wεH d L / 2 *
      Real.exp (-wkH d L * wholeLen d L N₁ m₁ k) : ℝ) : ℂ))
      (Metric.ball (0 : ℂ) (2⁻¹) ×ˢ (Set.univ : Set ℂ)) :=
    (analyticOnNhd_const.add analyticOnNhd_fst).mul analyticOnNhd_const
  refine h1.congr (Metric.isOpen_ball.prod isOpen_univ) (fun p hp' => ?_)
  have : ‖p.1‖ < 2⁻¹ := by simpa using hp'.1
  simp [physActScaled, LabelAct.scale, physAct, this]

/-- **`paramMarked_analytic_local_bound` on the physical block spaces, constant family**: for
every `T`, the coefficient is analytic on `V` and bounded by the uniform bound (the locality
premise holds with `π` constant, as the family does not depend on `θ`). -/
theorem physical_const_analytic_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [FiniteDimensional ℂ E] (V : Set E) (hV : IsOpen V)
    (T : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) 0 (k + 1)
      Set.univ)) :
    AnalyticOnNhd ℂ (fun _ : E => gsumCoeff (S.blockSplit 0 hp).μ
      (wholeLabel (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k))
      (fun _ : ℂ => physAct S hp) (fun _ : Unit => ()) (fun _ _ _ => (0 : ℂ)) T) V ∧
    ∀ θ ∈ V, ‖gsumCoeff (S.blockSplit 0 hp).μ
      (wholeLabel (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k))
      (fun _ : ℂ => physAct S hp) (fun _ : Unit => ()) (fun _ _ _ => (0 : ℂ)) T‖ ≤
        CPE d L (wKc d L) (wkH d L) (wk0 d L) 0 * (∑ _ : Unit, (1 : ℝ) *
          Real.exp (-wk0 d L * wholeLen d L N₁ m₁ k)) * Real.exp (-0 * dExt T) := by
  obtain ⟨hfam⟩ := nonempty_paramMarkFamily_physical_const S hp V hV
  have := isProbabilityMeasure_fluctMeasure1 N hp
  have h := paramMarked_analytic_local_bound (m₀ := 0) (j := k + 1) (Ω := Set.univ)
    (S.blockSplit 0 hp).μ (by simp) le_rfl isPiUnion_univ_aux hfam
    (fun _ _ _ _ _ _ => rfl) le_rfl le_rfl (half_pos (wεH_pos d L)) ⟨()⟩ (fun _ => one_pos) le_rfl le_rfl
    (by unfold wkH; linarith)
    (le_trans (b := wεH d L) (by linarith [wεH_pos d L]) le_rfl) T (fun _ => ()) (fun _ _ _ _ _ _ _ _ _ => rfl)
    (fun _ _ _ _ _ _ _ _ _ => rfl)
  exact ⟨h.1, h.2.2⟩

/-- **`paramMarked_analytic_local_bound` on the physical block spaces, scaled family**: the
coefficient of the family `(1 + θ) · physAct` is analytic in `θ` on the disk `‖θ‖ < 1/2`, and
bounded there by the uniform bound. -/
theorem physical_scaled_analytic_bound
    (T : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) 0 (k + 1)
      Set.univ)) :
    AnalyticOnNhd ℂ (fun θ : ℂ => gsumCoeff (S.blockSplit 0 hp).μ
      (wholeLabel (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k))
      (fun _ : ℂ => physActScaled S hp θ) (fun _ : Unit => ()) (fun _ _ _ => (0 : ℂ)) T)
      (Metric.ball (0 : ℂ) (2⁻¹)) ∧
    ∀ θ ∈ Metric.ball (0 : ℂ) (2⁻¹), ‖gsumCoeff (S.blockSplit 0 hp).μ
      (wholeLabel (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k))
      (fun _ : ℂ => physActScaled S hp θ) (fun _ : Unit => ()) (fun _ _ _ => (0 : ℂ)) T‖ ≤
        CPE d L (wKc d L) (wkH d L) (wk0 d L) 0 * (∑ _ : Unit, (1 : ℝ) *
          Real.exp (-wk0 d L * wholeLen d L N₁ m₁ k)) * Real.exp (-0 * dExt T) := by
  obtain ⟨hfam⟩ := nonempty_paramMarkFamily_physical_scaled S hp
  have := isProbabilityMeasure_fluctMeasure1 N hp
  have h := paramMarked_analytic_local_bound (m₀ := 0) (j := k + 1) (Ω := Set.univ)
    (S.blockSplit 0 hp).μ (by simp) le_rfl isPiUnion_univ_aux hfam
    (fun _ _ _ _ _ _ => rfl) le_rfl le_rfl (by linarith [wεH_pos d L]) ⟨()⟩ (fun _ => one_pos)
    le_rfl le_rfl (by unfold wkH; linarith)
    (le_trans (b := wεH d L) (by linarith) le_rfl) T id
    (fun θ _ θ' _ h _ _ y _ => by subst h; rfl) (fun _ _ _ _ _ _ _ _ _ => rfl)
  exact ⟨h.1, h.2.2⟩

end Physical

end Balaban.Fluctuation
