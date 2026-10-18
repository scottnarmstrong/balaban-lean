/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.ParamCarrierLocal
public import Balaban.Fluctuation.MeasureProduct
public import Balaban.Background.EquivarianceDomain
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Spin invariance of the block product measure and of the hat variable of a block configuration

For a real orthogonal matrix `Q` the sitewise rotation `Φ ↦ (b, u) ↦ Q Φ(b)(u)` of the block
configurations of a step preserves the product measure `⊗_b ν_b` (`integral_blockSplit_rot`) and the
carrier of the step measure, and on the carrier the clamped hat variable of the rotated
configuration is the rotation `(1 ⊗ Q)` of the hat variable (`hatOf_rot`).
-/

@[expose] public section

namespace Balaban.Fluctuation

open MeasureTheory Balaban Balaban.Multiscale Balaban.Background Matrix

section Iso

/-- A real orthogonal matrix acts on `ℝ^N` as a linear isometry equivalence. -/
theorem exists_linearIsometryEquiv_of_orth (N : ℕ) {Q : Matrix (Fin N) (Fin N) ℝ}
    (hQ : Qᵀ * Q = 1) :
    ∃ e : Rn N ≃ₗᵢ[ℝ] Rn N, ∀ x : Rn N, e x = WithLp.toLp 2 (Q *ᵥ x.ofLp) := by
  have hQ' : Q * Qᵀ = 1 := mul_eq_one_comm.1 hQ
  let f : Rn N →ₗ[ℝ] Rn N :=
    { toFun := fun x => WithLp.toLp 2 (Q *ᵥ x.ofLp)
      map_add' := fun x y => by ext i; simp [Matrix.mulVec_add]
      map_smul' := fun c x => by ext i; simp [Matrix.mulVec_smul] }
  have hn : ∀ x, ‖f x‖ = ‖x‖ := by
    intro x
    have h : (Q *ᵥ x.ofLp) ⬝ᵥ (Q *ᵥ x.ofLp) = x.ofLp ⬝ᵥ x.ofLp := by
      rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, Matrix.mulVec_mulVec, hQ,
        Matrix.one_mulVec]
    simp only [dotProduct, ← sq] at h
    simp only [f, LinearMap.coe_mk, AddHom.coe_mk, EuclideanSpace.norm_eq, Real.norm_eq_abs,
      sq_abs]
    congr 1
  exact ⟨LinearIsometryEquiv.ofSurjective ⟨f, hn⟩ (fun y => ⟨WithLp.toLp 2 (Qᵀ *ᵥ y.ofLp), by
    ext i
    simp [f, Matrix.mulVec_mulVec, hQ']⟩), fun x => rfl⟩

/-- The single-site fluctuation measure is invariant under linear isometries. -/
theorem map_fluctMeasure1_isometry (N : ℕ) (p : ℝ) (e : Rn N ≃ₗᵢ[ℝ] Rn N) :
    (fluctMeasure1 N p).map e = fluctMeasure1 N p := by
  have hmp : MeasurePreserving (e.toHomeomorph.toMeasurableEquiv) (volume : Measure (Rn N))
      volume := e.measurePreserving
  have hg : ∀ x, fluctDensity N p (e x) = fluctDensity N p x := by
    intro x; simp [fluctDensity, e.norm_map]
  ext s hs
  unfold fluctMeasure1
  rw [Measure.map_apply e.continuous.measurable hs, Measure.smul_apply, Measure.smul_apply,
    withDensity_apply _ (e.continuous.measurable hs), withDensity_apply _ hs]
  congr 1
  rw [← lintegral_indicator (e.continuous.measurable hs), ← lintegral_indicator hs]
  have : (Set.indicator (e ⁻¹' s) (fun x => ENNReal.ofReal (fluctDensity N p x))) =
      fun x => Set.indicator s (fun y => ENNReal.ofReal (fluctDensity N p y)) (e x) := by
    funext x
    by_cases hx : e x ∈ s
    · simp [Set.indicator, hx, hg]
    · simp [Set.indicator, hx]
  rw [this]
  exact (hmp.lintegral_comp_emb e.toHomeomorph.toMeasurableEquiv.measurableEmbedding _)

/-- Integrals over a finite product of spaces are transported by a coordinatewise
measure-preserving equivalence, for functions related on an almost-sure set. -/
theorem integral_comp_of_pi_equiv {ι : Type*} [Fintype ι] {β : ι → Type*}
    [∀ i, MeasurableSpace (β i)] (μ : ∀ i, Measure (β i)) [∀ i, SigmaFinite (μ i)]
    (E : ∀ i, β i ≃ᵐ β i) (hE : ∀ i, MeasurePreserving (E i) (μ i) (μ i))
    {Q : Set (∀ i, β i)} (hQ : ∀ᵐ Φ ∂(Measure.pi μ), Φ ∈ Q) {F F' : (∀ i, β i) → ℂ}
    (h : ∀ Φ ∈ Q, F' (fun i => E i (Φ i)) = F Φ) :
    ∫ Φ, F' Φ ∂(Measure.pi μ) = ∫ Φ, F Φ ∂(Measure.pi μ) := by
  have hmp := measurePreserving_pi μ μ (f := fun i => E i) hE
  have hme : MeasurableEmbedding (fun (a : ∀ i, β i) i => E i (a i)) :=
    (MeasurableEquiv.piCongrRight E).measurableEmbedding
  calc ∫ Φ, F' Φ ∂(Measure.pi μ) = ∫ Φ, F' Φ ∂(Measure.map (fun (a : ∀ i, β i) i => E i (a i))
        (Measure.pi μ)) := by rw [hmp.map_eq]
    _ = ∫ Φ, F' (fun i => E i (Φ i)) ∂(Measure.pi μ) := hme.integral_map _
    _ = ∫ Φ, F Φ ∂(Measure.pi μ) := by
      refine integral_congr_ae ?_
      filter_upwards [hQ] with Φ hΦ using h Φ hΦ

end Iso

section Block

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}
  (S : StepSetting d L N₁ m₁ k N ϱ) (m₀ : ℕ) (hp : 0 < S.p₁)

/-- **Transport of block integrals under a sitewise isometry.** -/
theorem integral_blockSplit_rot (e : Rn N ≃ₗᵢ[ℝ] Rn N)
    {F F' : (∀ b, (S.blockSplit m₀ hp).Ωb b) → ℂ}
    (h : ∀ Φ ∈ physCarrier S m₀ hp, F' (fun b u => e (Φ b u)) = F Φ) :
    ∫ Φ, F' Φ ∂(Measure.pi (S.blockSplit m₀ hp).μ) =
      ∫ Φ, F Φ ∂(Measure.pi (S.blockSplit m₀ hp).μ) := by
  have := isProbabilityMeasure_fluctMeasure1 N hp
  let ee : Rn N ≃ᵐ Rn N := e.toHomeomorph.toMeasurableEquiv
  have hee : MeasurePreserving ee (fluctMeasure1 N S.p₁) (fluctMeasure1 N S.p₁) :=
    ⟨ee.measurable, map_fluctMeasure1_isometry N S.p₁ e⟩
  let E : ∀ b, (S.blockSplit m₀ hp).Ωb b ≃ᵐ (S.blockSplit m₀ hp).Ωb b := fun b =>
    MeasurableEquiv.piCongrRight (fun _ : {u : S.U // S.cellOf m₀ u = b} => ee)
  have hE : ∀ b, MeasurePreserving (E b) ((S.blockSplit m₀ hp).μ b) ((S.blockSplit m₀ hp).μ b) :=
    fun b => measurePreserving_pi (fun _ : {u : S.U // S.cellOf m₀ u = b} => fluctMeasure1 N S.p₁)
      (fun _ => fluctMeasure1 N S.p₁) (fun _ => hee)
  exact integral_comp_of_pi_equiv (S.blockSplit m₀ hp).μ E hE (ae_mem_physCarrier S m₀ hp) h

/-- The sitewise isometry preserves the carrier of the step measure. -/
theorem rot_mem_physCarrier (e : Rn N ≃ₗᵢ[ℝ] Rn N) {Φ : ∀ b, (S.blockSplit m₀ hp).Ωb b}
    (hΦ : Φ ∈ physCarrier S m₀ hp) :
    (fun b u => e (Φ b u) : ∀ b, (S.blockSplit m₀ hp).Ωb b) ∈ physCarrier S m₀ hp := by
  intro b u
  rw [e.norm_map]
  exact hΦ b u

/-- **The hat variable of the rotated configuration is the rotated hat variable**, on the carrier
(where the radial clamp of radius `ρ ≥ p₁` is inactive). -/
theorem hatOf_rot (e : Rn N ≃ₗᵢ[ℝ] Rn N) {Q : Matrix (Fin N) (Fin N) ℝ}
    (he : ∀ x : Rn N, e x = WithLp.toLp 2 (Q *ᵥ x.ofLp)) {ρ : ℝ} (hρ : S.p₁ ≤ ρ)
    {Φ : ∀ b, (S.blockSplit m₀ hp).Ωb b} (hΦ : Φ ∈ physCarrier S m₀ hp) :
    S.hatOf m₀ ρ hp (fun b u => e (Φ b u)) = rotFld (cmat Q) (S.hatOf m₀ ρ hp Φ) := by
  have hρ0 : 0 < ρ := lt_of_lt_of_le hp hρ
  have hΦ' := rot_mem_physCarrier S m₀ hp e hΦ
  funext q
  have hcl : ∀ (x : Rn N) (i : Fin N), ‖x‖ ≤ S.p₁ →
      clampC ρ ((x i : ℝ) : ℂ) = ((x i : ℝ) : ℂ) := by
    intro x i hx
    refine clampC_of_le hρ0 ?_
    rw [Complex.norm_real]
    exact (PiLp.norm_apply_le x i).trans (hx.trans hρ)
  simp only [StepSetting.hatOf, rotFld]
  rw [hcl _ _ (hΦ' _ _)]
  have : ∀ j, clampC ρ ((Φ (S.cellOf m₀ q.1) ⟨q.1, rfl⟩ j : ℝ) : ℂ) =
      ((Φ (S.cellOf m₀ q.1) ⟨q.1, rfl⟩ j : ℝ) : ℂ) := fun j => hcl _ j (hΦ _ _)
  simp only [this]
  rw [he]
  simp only [Matrix.mulVec, dotProduct, Complex.ofReal_sum, Complex.ofReal_mul, cmat,
    Matrix.map_apply]

end Block

end Balaban.Fluctuation
