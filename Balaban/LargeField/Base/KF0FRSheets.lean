/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Base.BaseChartIdentity
public import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Tactic.Linarith

/-!
# `KF0FRSheets`: the two-sheet chart of the product of spheres (route FR, (R1))

`notes/phase1/KF0-FR.md` (R1); LF-BASE-KF0 (F.1). For a unit vector `h` let `ρ` be the orthogonal
reflection across `h^⊥` (`ρ v = v - 2⟨h,v⟩h`), restricted to the unit sphere (`reflS`). It preserves
the surface measure (`measurePreserving_reflS`), the equator `⟨h, φ⟩ = 0` is a null set
(`toSphere_equator`), and every non-equatorial spin is in exactly one of the two open hemispheres.
Hence, for every integrable `F` on `(S^{N-1})^ι`,

`∫ F dσ^ι = ∑_{σ : ι → Bool} ∫ ∏_x w(ξ_x) F(Φ_σ(ξ)) dξ` (`integral_sphere_pi_sheets`),

with `w(ξ) = (1 - |ξ|²)^{-1/2} 1[|ξ| < 1]` (`chartWeight`), `ξ_x ∈ h^⊥` with Lebesgue measure, and
`Φ_σ(ξ)_x` the graph point `ξ_x + √(1-|ξ_x|²) h` on the sheet `σ_x = true` and its reflection
`ξ_x - √(1-|ξ_x|²) h` on the sheet `σ_x = false` (`sheetPt`). No normalization constant appears.
-/

@[expose] public section

open MeasureTheory Set Metric
open scoped ENNReal Pointwise

namespace Balaban.LargeField.KF0FR

open SphereChart

noncomputable section

variable {N : ℕ} (h : EuclideanSpace ℝ (Fin N))

local notation "E" => EuclideanSpace ℝ (Fin N)
local notation "Sph" => Metric.sphere (0 : EuclideanSpace ℝ (Fin N)) 1

/-- The orthogonal reflection across `h^⊥`. -/
abbrev reflE : E ≃ₗᵢ[ℝ] E := (perp h).reflection

theorem reflE_h : reflE h h = -h := by
  have := Submodule.reflection_orthogonalComplement_singleton_eq_neg (𝕜 := ℝ) h
  simpa [perp] using this

theorem inner_reflE (v : E) : inner ℝ h (reflE h v) = -inner ℝ h v := by
  have h1 : inner ℝ (reflE h h) (reflE h v) = inner ℝ h v :=
    (reflE h).inner_map_map h v
  rw [reflE_h h, inner_neg_left] at h1
  linarith

/-- The reflection on the unit sphere. -/
def reflS (φ : Sph) : Sph := ⟨reflE h φ, by simp⟩

theorem coe_reflS (φ : Sph) : (reflS h φ : E) = reflE h φ := rfl

theorem reflS_reflS (φ : Sph) : reflS h (reflS h φ) = φ := by
  apply Subtype.ext
  simp only [coe_reflS]
  exact Submodule.reflection_reflection _ _

theorem measurable_reflS : Measurable (reflS h) :=
  Measurable.subtype_mk ((reflE h).continuous.measurable.comp measurable_subtype_coe)

/-- **The reflection preserves the surface measure.** -/
theorem measurePreserving_reflS :
    MeasurePreserving (reflS h) ((volume : Measure E).toSphere) ((volume : Measure E).toSphere) := by
  refine ⟨measurable_reflS h, ?_⟩
  ext s hs
  rw [Measure.map_apply (measurable_reflS h) hs,
    Measure.toSphere_apply' _ (measurable_reflS h hs), Measure.toSphere_apply' _ hs]
  congr 1
  have himg : ((↑) : Sph → E) '' (reflS h ⁻¹' s) = reflE h ⁻¹' (((↑) : Sph → E) '' s) := by
    ext v
    constructor
    · rintro ⟨φ, hφ, rfl⟩
      exact ⟨reflS h φ, hφ, rfl⟩
    · rintro ⟨φ, hφ, hv⟩
      refine ⟨reflS h φ, by simpa [reflS_reflS] using hφ, ?_⟩
      rw [coe_reflS, hv]
      exact Submodule.reflection_reflection _ _
  rw [himg]
  have hsm : Ioo (0 : ℝ) 1 • (reflE h ⁻¹' (((↑) : Sph → E) '' s)) =
      reflE h ⁻¹' (Ioo (0 : ℝ) 1 • (((↑) : Sph → E) '' s)) := by
    ext v
    simp only [Set.mem_smul, Set.mem_preimage]
    constructor
    · rintro ⟨t, ht, w, hw, rfl⟩
      exact ⟨t, ht, reflE h w, hw, by simp⟩
    · rintro ⟨t, ht, w, hw, hv⟩
      refine ⟨t, ht, reflE h w, ?_, ?_⟩
      · simpa [Submodule.reflection_reflection] using hw
      · calc t • reflE h w = reflE h (t • w) := (map_smul (reflE h) t w).symm
          _ = reflE h (reflE h v) := by rw [hv]
          _ = v := Submodule.reflection_reflection _ _
  rw [hsm]
  have hmp : MeasurePreserving (reflE h).toMeasurableEquiv (volume : Measure E) volume :=
    (reflE h).measurePreserving
  exact hmp.measure_preimage_equiv _

/-! ### The equator -/

/-- **The equator `⟨h, φ⟩ = 0` is a null set of the surface measure.** -/
theorem toSphere_equator (hh : ‖h‖ = 1) :
    (volume : Measure E).toSphere {φ : Sph | inner ℝ h (φ : E) = 0} = 0 := by
  have hmeas : MeasurableSet {φ : Sph | inner ℝ h (φ : E) = 0} :=
    measurableSet_eq_fun (measurable_const.inner measurable_subtype_coe) measurable_const
  rw [Measure.toSphere_apply' _ hmeas]
  have hsub : Ioo (0 : ℝ) 1 • (((↑) : Sph → E) '' {φ : Sph | inner ℝ h (φ : E) = 0}) ⊆
      ((perp h : Submodule ℝ E) : Set E) := by
    rintro v ⟨t, -, w, ⟨φ, hφ, rfl⟩, rfl⟩
    simp only [SetLike.mem_coe]
    rw [Submodule.mem_orthogonal_singleton_iff_inner_right]
    simp only [Set.mem_ofPred_eq] at hφ
    rw [inner_smul_right, hφ, mul_zero]
  have hne : (perp h : Submodule ℝ E) ≠ ⊤ := by
    intro htop
    have hmem : h ∈ (perp h : Submodule ℝ E) := by rw [htop]; trivial
    rw [Submodule.mem_orthogonal_singleton_iff_inner_right, real_inner_self_eq_norm_sq, hh] at hmem
    norm_num at hmem
  rw [measure_mono_null hsub (Measure.addHaar_submodule _ _ hne), mul_zero]

variable {ι : Type*}

/-- **Some site on the equator: a null set of the product measure.** -/
theorem pi_equator_null [Fintype ι] (hh : ‖h‖ = 1) :
    (Measure.pi fun _ : ι => (volume : Measure E).toSphere)
      {φ : ι → Sph | ∃ x, inner ℝ h (φ x : E) = 0} = 0 := by
  have : {φ : ι → Sph | ∃ x, inner ℝ h (φ x : E) = 0} =
      ⋃ x, Function.eval x ⁻¹' {v : Sph | inner ℝ h (v : E) = 0} := by
    ext φ; simp
  rw [this]
  exact measure_iUnion_null fun x => Measure.pi_eval_preimage_null _ (toSphere_equator h hh)

/-! ### The sheets -/

/-- The spins on the sheet `σ_x` of each site: `⟨h, φ_x⟩ > 0` for `σ_x = true`, `< 0` otherwise. -/
def OnSheets (σ : ι → Bool) (φ : ι → Sph) : Prop :=
  ∀ x, if σ x then 0 < inner ℝ h (φ x : E) else inner ℝ h (φ x : E) < 0

instance (σ : ι → Bool) (φ : ι → Sph) : Decidable (OnSheets h σ φ) := Classical.dec _

theorem measurableSet_onSheets [Countable ι] (σ : ι → Bool) : MeasurableSet {φ : ι → Sph | OnSheets h σ φ} := by
  have : {φ : ι → Sph | OnSheets h σ φ} = ⋂ x, Function.eval x ⁻¹'
      (if σ x then {v : Sph | 0 < inner ℝ h (v : E)} else {v : Sph | inner ℝ h (v : E) < 0}) := by
    ext φ
    simp only [OnSheets, Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_preimage, Function.eval]
    refine forall_congr' fun x => ?_
    split_ifs <;> rfl
  rw [this]
  refine MeasurableSet.iInter fun x => measurable_pi_apply x ?_
  have hm : Measurable fun v : Sph => inner ℝ h (v : E) := measurable_const.inner measurable_subtype_coe
  split_ifs
  · exact measurableSet_lt measurable_const hm
  · exact measurableSet_lt hm measurable_const

/-- Off the equator, the sheet indicators sum to one. -/
theorem sum_onSheets_indicator [Fintype ι] [DecidableEq ι] {φ : ι → Sph} (hφ : ∀ x, inner ℝ h (φ x : E) ≠ 0) :
    ∑ σ : ι → Bool, (if OnSheets h σ φ then (1 : ℂ) else 0) = 1 := by
  classical
  set σ₀ : ι → Bool := fun x => decide (0 < inner ℝ h (φ x : E)) with hσ₀
  have h0 : OnSheets h σ₀ φ := by
    intro x
    by_cases hx : 0 < inner ℝ h (φ x : E)
    · simp [hσ₀, hx]
    · have : inner ℝ h (φ x : E) < 0 := lt_of_le_of_ne (not_lt.1 hx) (hφ x)
      simp [hσ₀, hx, this]
  have huniq : ∀ σ, OnSheets h σ φ → σ = σ₀ := by
    intro σ hσ
    funext x
    have := hσ x
    by_cases hx : 0 < inner ℝ h (φ x : E)
    · cases hb : σ x
      · rw [hb] at this; simp only [Bool.false_eq_true, ↓reduceIte] at this; linarith
      · simp [hσ₀, hx]
    · cases hb : σ x
      · simp [hσ₀, hx]
      · rw [hb] at this; simp only [↓reduceIte] at this; exact absurd this hx
  rw [Finset.sum_eq_single σ₀ (fun σ _ hσ => by rw [ite_eq_right (fun h' => hσ (huniq σ h'))])
    (fun h' => absurd (Finset.mem_univ σ₀) h'), ite_eq_left h0]

/-- The reflection of the sites of the sheet `false`. -/
def reflSheets (σ : ι → Bool) (φ : ι → Sph) : ι → Sph := fun x => if σ x then φ x else reflS h (φ x)

theorem reflSheets_involutive (σ : ι → Bool) : Function.Involutive (reflSheets h σ) := by
  intro φ
  funext x
  unfold reflSheets
  split_ifs <;> simp [reflS_reflS]

theorem measurePreserving_reflSheets [Fintype ι] (σ : ι → Bool) :
    MeasurePreserving (reflSheets h σ) (Measure.pi fun _ : ι => (volume : Measure E).toSphere)
      (Measure.pi fun _ : ι => (volume : Measure E).toSphere) := by
  have : reflSheets h σ = fun φ x => (if σ x then id else reflS h) (φ x) := by
    funext φ x; unfold reflSheets; split_ifs <;> rfl
  rw [this]
  refine measurePreserving_pi _ _ fun x => ?_
  split_ifs
  · exact MeasurePreserving.id _
  · exact measurePreserving_reflS h

theorem measurable_reflSheets [Fintype ι] (σ : ι → Bool) : Measurable (reflSheets h σ) :=
  (measurePreserving_reflSheets h σ).measurable

/-- The measurable involution `reflSheets`. -/
def reflSheetsEquiv [Fintype ι] (σ : ι → Bool) : (ι → Sph) ≃ᵐ (ι → Sph) :=
  MeasurableEquiv.ofInvolutive _ (reflSheets_involutive h σ) (measurable_reflSheets h σ)

theorem onSheets_reflSheets_iff (σ : ι → Bool) (φ : ι → Sph) :
    OnSheets h σ (reflSheets h σ φ) ↔ ∀ x, 0 < inner ℝ h (φ x : E) := by
  refine forall_congr' fun x => ?_
  unfold reflSheets
  cases σ x
  · simp only [Bool.false_eq_true, ↓reduceIte, coe_reflS, inner_reflE]
    constructor <;> intro hx <;> linarith
  · simp

/-- The point of the sheet `b` above `ξ ∈ h^⊥`. -/
def sheetPt (hh : ‖h‖ = 1) (b : Bool) (ξ : perp h) : Sph :=
  if b then hemiPt h hh ξ else reflS h (hemiPt h hh ξ)

/-- **The two-sheet chart of the product of spheres (R1).** -/
theorem integral_sphere_pi_sheets [Fintype ι] [DecidableEq ι] (hh : ‖h‖ = 1) (F : (ι → Sph) → ℂ) (hF : Measurable F)
    (hint : Integrable F (Measure.pi fun _ : ι => (volume : Measure E).toSphere)) :
    ∫ φ, F φ ∂(Measure.pi fun _ : ι => (volume : Measure E).toSphere) =
      ∑ σ : ι → Bool, ∫ ξ : ι → perp h,
        (∏ x, ((chartWeight h (ξ x) : ℝ) : ℂ)) * F (fun x => sheetPt h hh (σ x) (ξ x))
          ∂(Measure.pi fun _ : ι => (volume : Measure (perp h))) := by
  classical
  set μ := Measure.pi fun _ : ι => (volume : Measure E).toSphere with hμ
  -- the sheets cover almost everything
  have hae : ∀ᵐ φ ∂μ, F φ = ∑ σ : ι → Bool, (if OnSheets h σ φ then (1 : ℂ) else 0) * F φ := by
    have hnull := pi_equator_null (ι := ι) h hh
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 hnull] with φ hφ
    have hφ' : ∀ x, inner ℝ h (φ x : E) ≠ 0 := fun x hx => hφ ⟨x, hx⟩
    rw [← Finset.sum_mul, sum_onSheets_indicator h hφ', one_mul]
  rw [integral_congr_ae hae, integral_finsetSum _ (fun σ _ => ?_)]
  · refine Finset.sum_congr rfl fun σ _ => ?_
    -- reflect the sites of the sheet `false`
    have hmp : MeasurePreserving (reflSheetsEquiv h σ) μ μ := measurePreserving_reflSheets h σ
    rw [← hmp.integral_comp' (fun φ => (if OnSheets h σ φ then (1 : ℂ) else 0) * F φ)]
    have hrefl : ∀ φ, (reflSheetsEquiv h σ φ) = reflSheets h σ φ := fun _ => rfl
    simp_rw [hrefl, onSheets_reflSheets_iff]
    -- the chart of the upper hemispheres
    set G : (ι → Sph) → ℂ := fun φ =>
      (if ∀ x, 0 < inner ℝ h (φ x : E) then (1 : ℂ) else 0) * F (reflSheets h σ φ) with hG
    have hGm : Measurable G := by
      refine Measurable.mul ?_ (hF.comp (measurable_reflSheets h σ))
      refine Measurable.ite ?_ measurable_const measurable_const
      have : {φ : ι → Sph | ∀ x, 0 < inner ℝ h (φ x : E)} =
          ⋂ x, Function.eval x ⁻¹' {v : Sph | 0 < inner ℝ h (v : E)} := by ext φ; simp
      rw [this]
      exact MeasurableSet.iInter fun x => measurable_pi_apply x
        (measurableSet_lt measurable_const (measurable_const.inner measurable_subtype_coe))
    have hGi : Integrable G μ := by
      have hFr : Integrable (fun φ => F (reflSheets h σ φ)) μ := by
        have := (hmp.integrable_comp_emb (reflSheetsEquiv h σ).measurableEmbedding).2 hint
        exact this
      refine hFr.mono hGm.aestronglyMeasurable (Filter.Eventually.of_forall fun φ => ?_)
      simp only [hG, norm_mul]
      split_ifs <;> simp
    have hGs : ∀ φ, (∃ x, ¬ 0 < inner ℝ h (φ x : E)) → G φ = 0 := by
      intro φ ⟨x, hx⟩
      simp only [hG]
      rw [ite_eq_right (fun hall => hx (hall x)), zero_mul]
    have hchart := integral_sphere_pi_hemisphere_complex (fun _ : ι => h) (fun _ => hh) G hGm hGi hGs
    change ∫ φ, G φ ∂μ = _ at hchart
    refine hchart.trans (integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_))
    simp only [hG]
    by_cases hall : ∀ x, ‖ξ x‖ < 1
    · have hup : ∀ x, 0 < inner ℝ h ((chartMapPi (fun _ : ι => h) (fun _ => hh) ξ x : Sph) : E) :=
        fun x => inner_hemiPt_pos h hh (hall x)
      rw [ite_eq_left hup, one_mul]
      congr 2
    · push Not at hall
      obtain ⟨x, hx⟩ := hall
      have hw : chartWeight h (ξ x) = 0 := by unfold chartWeight; rw [ite_eq_right (not_lt.2 hx)]
      rw [Finset.prod_eq_zero (Finset.mem_univ x) (by simp [hw]), zero_mul, zero_mul]
  · refine hint.mono ?_ (Filter.Eventually.of_forall fun φ => ?_)
    · refine Measurable.aestronglyMeasurable (Measurable.mul ?_ hF)
      exact Measurable.ite (measurableSet_onSheets h σ) measurable_const measurable_const
    · simp only [norm_mul]
      split_ifs <;> simp

end

end Balaban.LargeField.KF0FR
