/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.ObsRemainderFamily
public import Balaban.Fluctuation.ObsRemainderMarks
public import Balaban.Fluctuation.Thm31CoeffB
public import Balaban.Fluctuation.Thm31bResum

/-!
# The first-order observable marks with the continuous clamp

`blockMarkC` is the first-order mark `blockMark` with the clipping (the coordinate if the fluctuation
vector has norm `< p₁`, else `0`) replaced by the radial projection onto the disk of radius `p₁`,
that is, the coordinate `(u, a)` of `StepSetting.hatOf`.  The projection is continuous, so the mark
is continuous on all block configurations; it is bounded by `p₁`, local to the block of `u`, has
mean zero, and equals `blockMark` for almost every block configuration.  The first-order term
`markIntTerm` reads the mark only under the block product integral, hence does not change when the
mark is replaced by an almost-everywhere equal one.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Localization Balaban.Polymer Balaban.SmallField.Def6 Balaban.Multiscale
  Balaban.Background Balaban.SmallField Metric MeasureTheory

section Mark

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
  (S : StepSetting d L N₁ m₁ k N ϱ) (m₀ : ℕ) (hp : 0 < S.p₁)

/-- **The first-order mark with the continuous clamp**: the coordinate `(u, a)` of the clamped hat
field `S.hatOf m₀ S.p₁ hp Φ`. -/
noncomputable def blockMarkC (u : S.U) (a : Fin N)
    (Φ : ∀ b, (S.blockSplit m₀ hp).Ωb b) : ℂ :=
  S.hatOf m₀ S.p₁ hp Φ (u, a)

variable {S m₀ hp}

theorem norm_blockMarkC_le (u : S.U) (a : Fin N) (Φ : ∀ b, (S.blockSplit m₀ hp).Ωb b) :
    ‖blockMarkC S m₀ hp u a Φ‖ ≤ S.p₁ :=
  norm_hatOf_p₁_le Φ (u, a)

theorem continuous_blockMarkC (u : S.U) (a : Fin N) :
    Continuous (blockMarkC S m₀ hp u a) :=
  (continuous_apply (u, a)).comp (S.continuous_hatOf m₀ S.p₁ hp)

theorem measurable_blockMarkC (u : S.U) (a : Fin N) :
    Measurable (blockMarkC S m₀ hp u a) :=
  (continuous_blockMarkC u a).measurable

/-- **Block locality**: the mark depends only on the block of `u`. -/
theorem depOn_blockMarkC (u : S.U) (a : Fin N)
    {T : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) m₀ (k + 1)
      Set.univ)} (hT : S.cellOf m₀ u ∈ T) :
    DepOn (Ω := (S.blockSplit m₀ hp).Ωb) T (blockMarkC S m₀ hp u a) := by
  intro Φ Φ' h
  unfold blockMarkC StepSetting.hatOf
  rw [h _ hT]

/-- **The clamp is invisible almost everywhere**: `blockMarkC = blockMark` for the block product
measure. -/
theorem ae_blockMarkC_eq (u : S.U) (a : Fin N) :
    ∀ᵐ Φ ∂(Measure.pi (S.blockSplit m₀ hp).μ),
      blockMarkC S m₀ hp u a Φ = blockMark S m₀ hp u a Φ := by
  filter_upwards [ae_obsHat_eq_true S m₀ hp] with Φ h
  have h1 : obsHat S m₀ hp Φ (u, a) = obsHatTrue S m₀ hp Φ (u, a) := congrFun h (u, a)
  have h2 : ‖obsHatTrue S m₀ hp Φ (u, a)‖ ≤ S.p₁ := h1 ▸ norm_obsHat_le S m₀ hp Φ (u, a)
  have h3 : blockMarkC S m₀ hp u a Φ = obsHatTrue S m₀ hp Φ (u, a) :=
    clampC_of_le hp h2
  rw [h3, ← h1]
  rfl

/-- **Mean zero** of the clamped mark. -/
theorem integral_blockMarkC (u : S.U) (a : Fin N) :
    ∫ Φ, blockMarkC S m₀ hp u a Φ ∂Measure.pi (S.blockSplit m₀ hp).μ = 0 := by
  rw [integral_congr_ae (ae_blockMarkC_eq u a)]
  exact integral_blockMark S m₀ hp u a

/-- The fields of a first-order mark, for the clamped mark with the bound `p₁ e^{-κG dl y}`. -/
theorem blockMarkC_fields (u : S.U) (a : Fin N) {Lb : Type*}
    (Lab : CubeLabels (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) m₀ (k + 1)
      Set.univ Lb) {κG : ℝ} (hκG : κG ≤ 0) (y : Lb)
    (hy : S.cellOf m₀ u ∈ blocksOf (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
      (K := k + 1) m₀ (k + 1) Set.univ (Lab.ysite y)) :
    Continuous (blockMarkC S m₀ hp u a) ∧ Measurable (blockMarkC S m₀ hp u a) ∧
    DepOn (Ω := (S.blockSplit m₀ hp).Ωb) (blocksOf (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
      (K := k + 1) m₀ (k + 1) Set.univ (Lab.ysite y)) (blockMarkC S m₀ hp u a) ∧
    (∀ Φ, ‖blockMarkC S m₀ hp u a Φ‖ ≤ S.p₁ * Real.exp (-κG * Lab.dl y)) ∧
    ∫ Φ, blockMarkC S m₀ hp u a Φ ∂Measure.pi (S.blockSplit m₀ hp).μ = 0 := by
  refine ⟨continuous_blockMarkC u a, measurable_blockMarkC u a, depOn_blockMarkC u a hy,
    fun Φ => ?_, integral_blockMarkC u a⟩
  have h1 : 1 ≤ Real.exp (-κG * Lab.dl y) := by
    rw [Real.one_le_exp_iff]
    have := Lab.dl_nonneg y
    nlinarith
  calc ‖blockMarkC S m₀ hp u a Φ‖ ≤ S.p₁ := norm_blockMarkC_le u a Φ
    _ = S.p₁ * 1 := (mul_one _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left h1 hp.le

end Mark

section Congr

variable {d L N₁ m₁ K : ℕ} [NeZero L] [NeZero N₁] {m₀ j : ℕ} {Ω : Set (CTorus d L N₁ m₁ K)}
  {Lb : Type*} [Fintype Lb]

local notation "𝔅" => CubeB (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ j Ω

open Classical in
/-- **Almost-everywhere congruence of the first-order term in the mark**: with the same activities,
`markIntTerm` is unchanged when the mark is replaced by a mark that is equal to it for almost every
block configuration. -/
theorem markIntTerm_congr_ae {Ωb : 𝔅 → Type*} [∀ b, MeasurableSpace (Ωb b)]
    (μ : ∀ b, Measure (Ωb b)) [∀ b, IsProbabilityMeasure (μ b)] {Lab : CubeLabels m₀ j Ω Lb}
    {εH κH κ0 Kc : ℝ} (A : ℂ → ℂ → LabelAct Lab Ωb εH κH κ0 Kc) (y0 : Lb)
    {G G' : (∀ b, Ωb b) → ℂ} (S : Finset 𝔅) (hG : ∀ᵐ Φ ∂(Measure.pi μ), G Φ = G' Φ) :
    markIntTerm μ A y0 G S = markIntTerm μ A y0 G' S := by
  unfold markIntTerm
  exact intervalIntegral.integral_congr fun s _ => Gst_congr_ae μ Lab _ _ S hG

open Classical in
/-- **The resummed first-order sum does not see null sets of the marks**: with the same kernel,
the sums built from two families of marks that agree almost everywhere agree. -/
theorem kernelMarkSum_markIntTerm_congr_ae {Ωb : 𝔅 → Type*} [∀ b, MeasurableSpace (Ωb b)]
    (μ : ∀ b, Measure (Ωb b)) [∀ b, IsProbabilityMeasure (μ b)] {Lab : CubeLabels m₀ j Ω Lb}
    {εH κH κ0 Kc : ℝ} (A : ℂ → ℂ → LabelAct Lab Ωb εH κH κ0 Kc) {ι : Type*} [Fintype ι]
    (y0 : ι → Lb) (h : ι → Finset 𝔅 → ℂ) {G G' : ι → (∀ b, Ωb b) → ℂ}
    (hG : ∀ i, ∀ᵐ Φ ∂(Measure.pi μ), G i Φ = G' i Φ) (W : Finset 𝔅) :
    kernelMarkSum h (fun i S => markIntTerm μ A (y0 i) (G i) S) W =
      kernelMarkSum h (fun i S => markIntTerm μ A (y0 i) (G' i) S) W := by
  unfold kernelMarkSum
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun T _ =>
    Finset.sum_congr rfl fun S _ => ?_
  dsimp only
  rw [markIntTerm_congr_ae μ A (y0 i) S (hG i)]

end Congr

section Family

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
  {S : StepSetting d L N₁ m₁ k N ϱ} {m₀ : ℕ} {hp : 0 < S.p₁}

/-- Mark hypothesis `meas` of `ParamMarkFamily` for the constant family `blockMarkC`. -/
theorem blockMarkC_family_meas {E : Type*} (u : S.U) (a : Fin N) :
    ∀ (_ : E) (_ : Unit) (_ : ℂ), Measurable (blockMarkC S m₀ hp u a) :=
  fun _ _ _ => measurable_blockMarkC u a

/-- Mark hypothesis `bound` of `ParamMarkFamily` for the constant family `blockMarkC`, with
`F0 = p₁ e^{κG dl y0}`. -/
theorem blockMarkC_family_bound {E : Type*} (u : S.U) (a : Fin N) {Lb : Type*} [Fintype Lb]
    {Ω : Set (CTorus d L N₁ m₁ (k + 1))} {j : ℕ}
    (Lab : CubeLabels (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) m₀ j Ω Lb)
    (y0 : Lb) (κG : ℝ) :
    ∀ (_ : E) (_ : Unit) (_ : ℂ) (Φ : ∀ b, (S.blockSplit m₀ hp).Ωb b),
      ‖blockMarkC S m₀ hp u a Φ‖ ≤ (S.p₁ * Real.exp (κG * Lab.dl y0)) * Real.exp (-κG * Lab.dl y0) := by
  intro _ _ _ Φ
  rw [mul_assoc, ← Real.exp_add]
  simp only [neg_mul, add_neg_cancel, Real.exp_zero, mul_one]
  exact norm_blockMarkC_le u a Φ

/-- Mark hypothesis `holG` of `ParamMarkFamily`: the constant family is analytic in `(θ, u)`. -/
theorem blockMarkC_family_holG {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (u : S.U) (a : Fin N) (V : Set E) (𝒰 : Set ℂ) :
    ∀ Φ : (∀ b, (S.blockSplit m₀ hp).Ωb b),
      AnalyticOnNhd ℂ (fun _ : E × ℂ => blockMarkC S m₀ hp u a Φ) (V ×ˢ 𝒰) :=
  fun _ => analyticOnNhd_const

/-- Mark hypothesis `contG` of `ParamMarkFamily`: continuity on every set of configurations
(in particular the closed carrier). -/
theorem blockMarkC_family_contG {E : Type*} (u : S.U) (a : Fin N)
    (Q : Set (∀ b, (S.blockSplit m₀ hp).Ωb b)) :
    ∀ (_ : E) (_ : ℂ), ContinuousOn (blockMarkC S m₀ hp u a) Q :=
  fun _ _ => (continuous_blockMarkC u a).continuousOn

end Family

end Balaban.Fluctuation
