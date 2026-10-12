/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Base.ConeVolume
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# The hemisphere graph chart and the surface measure (LF-RECONSTRUCTION Lemma II.7.4 (a))

Let `E` be a finite-dimensional real inner product space (e.g. `EuclideanSpace ℝ (Fin N)`) and
`e ∈ E` a unit vector, `K = e^⊥`.  The graph chart is
`hemiE e ξ = √(1 - |ξ|²) e + ξ`, `ξ ∈ K`, `|ξ| < 1`.

* `hemiPt_injOn`, `hemiPt_image`, `perpK_hemiE`, `hemiE_perpK`, `contDiffOn_hemiE`: the chart is
  a smooth bijection of the open unit ball of `K` onto the open hemisphere `⟨e, φ⟩ > 0`, with
  inverse the orthogonal projection onto `e^⊥`;
* `toSphere_eq_graph` (`toSphere_hemisphere_apply`): Mathlib's surface measure `Measure.toSphere`
  of Lebesgue measure, restricted to the open hemisphere, equals
  `(1 - |ξ|²)^{-1/2} dξ` in the chart.  The proof computes the volume of the cone over a
  hemisphere patch (`ConeVolume.lean`) and uses `toSphere s = dim E • vol (Ioo 0 1 • s)`; it needs
  no uniqueness theorem for invariant measures;
* `lintegral_hemisphere`, `integral_hemisphere`: the corresponding integral formulas.
-/

@[expose] public section

open MeasureTheory Set Metric
open scoped ENNReal Pointwise

namespace Balaban.LargeField.SphereChart

noncomputable section Geometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable (e : E)

/-- The tangent space `e^⊥`. -/
abbrev perp : Submodule ℝ E := (ℝ ∙ e)ᗮ

/-- The orthogonal projection `x ↦ x - ⟨e, x⟩ e` onto `e^⊥`, as an element of `E`. -/
def perpProj (x : E) : E := x - inner ℝ e x • e

theorem perpProj_mem (he : ‖e‖ = 1) (x : E) : perpProj e x ∈ perp e := by
  rw [Submodule.mem_orthogonal_singleton_iff_inner_right]
  simp [perpProj, inner_sub_right, inner_smul_right, he]

/-- The projection onto `e^⊥` as an element of the subspace. -/
def perpK (he : ‖e‖ = 1) (x : E) : perp e := ⟨perpProj e x, perpProj_mem e he x⟩

theorem inner_eq_of_mem_perp {η : E} (h : η ∈ perp e) : inner ℝ e η = 0 :=
  (Submodule.mem_orthogonal_singleton_iff_inner_right.1 h)

theorem norm_coe_perp (ξ : perp e) : ‖(ξ : E)‖ = ‖ξ‖ := rfl

theorem norm_sq_eq_inner_sq_add (he : ‖e‖ = 1) (x : E) :
    ‖x‖ ^ 2 = inner ℝ e x ^ 2 + ‖perpProj e x‖ ^ 2 := by
  have hx : x = inner ℝ e x • e + perpProj e x := by simp [perpProj]
  conv_lhs => rw [hx]
  rw [norm_add_sq_real, real_inner_smul_left, real_inner_comm, inner_eq_of_mem_perp e (perpProj_mem e he x),
    norm_smul, he]
  simp only [mul_zero, mul_one, Real.norm_eq_abs, sq_abs]
  ring

/-- The hemisphere graph chart `ξ ↦ √(1 - |ξ|²) e + ξ`. -/
def hemiE (ξ : perp e) : E := Real.sqrt (1 - ‖ξ‖ ^ 2) • e + (ξ : E)

theorem inner_hemiE (he : ‖e‖ = 1) (ξ : perp e) :
    inner ℝ e (hemiE e ξ) = Real.sqrt (1 - ‖ξ‖ ^ 2) := by
  rw [hemiE, inner_add_right, inner_eq_of_mem_perp e ξ.2, inner_smul_right,
    real_inner_self_eq_norm_sq, he]; simp

theorem perpProj_hemiE (he : ‖e‖ = 1) (ξ : perp e) : perpProj e (hemiE e ξ) = ξ := by
  have h := inner_hemiE e he ξ
  show hemiE e ξ - inner ℝ e (hemiE e ξ) • e = ξ
  rw [h]; unfold hemiE; abel

theorem norm_hemiE (he : ‖e‖ = 1) {ξ : perp e} (hξ : ‖ξ‖ ≤ 1) : ‖hemiE e ξ‖ = 1 := by
  have h := norm_sq_eq_inner_sq_add e he (hemiE e ξ)
  rw [inner_hemiE e he, perpProj_hemiE e he, Real.sq_sqrt (by nlinarith [norm_nonneg ξ]),
    norm_coe_perp] at h
  nlinarith [norm_nonneg (hemiE e ξ)]

theorem continuous_perpK (he : ‖e‖ = 1) : Continuous (perpK e he) := by
  refine Continuous.subtype_mk ?_ _
  unfold perpProj
  fun_prop

/-- The hemisphere-chart preimage of a set of the sphere. -/
def hemiSet (s : Set (Metric.sphere (0 : E) 1)) : Set (perp e) :=
  {ξ | ‖ξ‖ < 1 ∧ ∃ φ ∈ s, (φ : E) = hemiE e ξ}

/-- The open cone over the chart image of `T`. -/
def coneE (he : ‖e‖ = 1) (T : Set (perp e)) : Set E :=
  {x | 0 < inner ℝ e x ∧ ‖x‖ < 1 ∧ ‖x‖⁻¹ • perpK e he x ∈ T}

theorem norm_perpK_lt (he : ‖e‖ = 1) {φ : E} (hφ : ‖φ‖ = 1) (h : 0 < inner ℝ e φ) :
    ‖perpK e he φ‖ < 1 := by
  have h1 := norm_sq_eq_inner_sq_add e he φ
  rw [hφ] at h1
  have h2 : ‖perpK e he φ‖ ^ 2 < 1 := by
    have : ‖perpK e he φ‖ = ‖perpProj e φ‖ := rfl
    rw [this]; nlinarith [sq_pos_of_pos h]
  nlinarith [norm_nonneg (perpK e he φ)]

theorem hemiE_perpK (he : ‖e‖ = 1) {φ : E} (hφ : ‖φ‖ = 1) (h : 0 < inner ℝ e φ) :
    hemiE e (perpK e he φ) = φ := by
  have h1 := norm_sq_eq_inner_sq_add e he φ
  rw [hφ] at h1
  have h2 : Real.sqrt (1 - ‖perpK e he φ‖ ^ 2) = inner ℝ e φ := by
    have : ‖perpK e he φ‖ = ‖perpProj e φ‖ := rfl
    rw [this, show 1 - ‖perpProj e φ‖ ^ 2 = inner ℝ e φ ^ 2 by nlinarith]
    exact Real.sqrt_sq h.le
  unfold hemiE
  rw [h2]
  show inner ℝ e φ • e + perpProj e φ = φ
  simp [perpProj]

theorem perpK_smul (he : ‖e‖ = 1) (t : ℝ) (x : E) : perpK e he (t • x) = t • perpK e he x := by
  apply Subtype.ext
  simp [perpK, perpProj, inner_smul_right, smul_sub, smul_smul]

theorem cone_eq (he : ‖e‖ = 1) (s : Set (Metric.sphere (0 : E) 1)) :
    Ioo (0 : ℝ) 1 • (Subtype.val '' (s ∩ {φ | 0 < inner ℝ e (φ : E)})) =
      coneE e he (hemiSet e s) := by
  ext x
  rw [Set.mem_smul]
  constructor
  · rintro ⟨t, ht, _, ⟨φ, ⟨hφs, hφH⟩, rfl⟩, rfl⟩
    have hφ1 : ‖(φ : E)‖ = 1 := by simp
    have hH : 0 < inner ℝ e (φ : E) := hφH
    refine ⟨?_, ?_, ?_⟩
    · rw [inner_smul_right]; exact mul_pos ht.1 hH
    · rw [norm_smul, hφ1, Real.norm_of_nonneg ht.1.le]; simpa using ht.2
    · rw [perpK_smul, norm_smul, hφ1, Real.norm_of_nonneg ht.1.le]
      rw [smul_smul, mul_one, inv_mul_cancel₀ ht.1.ne', one_smul]
      refine ⟨norm_perpK_lt e he hφ1 hH, φ, hφs, ?_⟩
      exact (hemiE_perpK e he hφ1 hH).symm
  · rintro ⟨hx1, hx2, hx3⟩
    obtain ⟨hξ, ψ, hψs, hψ⟩ := hx3
    set t := ‖x‖ with ht
    have ht0 : 0 < t := by
      rcases (norm_nonneg x).lt_or_eq with h | h
      · exact h
      · exfalso
        have : x = 0 := norm_eq_zero.1 h.symm
        rw [this] at hx1; simp at hx1
    set ξ : perp e := t⁻¹ • perpK e he x with hξdef
    have hr : 0 < Real.sqrt (1 - ‖ξ‖ ^ 2) := Real.sqrt_pos.2 (by nlinarith [norm_nonneg ξ])
    have hdec := norm_sq_eq_inner_sq_add e he x
    have hPx : ‖perpProj e x‖ = t * ‖ξ‖ := by
      rw [hξdef, norm_smul, norm_inv, Real.norm_of_nonneg ht0.le]
      have : ‖perpK e he x‖ = ‖perpProj e x‖ := rfl
      rw [this]; field_simp
    have hin : inner ℝ e x = t * Real.sqrt (1 - ‖ξ‖ ^ 2) := by
      have h2 : inner ℝ e x ^ 2 = (t * Real.sqrt (1 - ‖ξ‖ ^ 2)) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt (by nlinarith [norm_nonneg ξ])]
        rw [hPx] at hdec
        nlinarith
      exact (sq_eq_sq₀ hx1.le (by positivity)).1 h2
    refine ⟨t, ⟨ht0, hx2⟩, _, ⟨ψ, ⟨hψs, ?_⟩, rfl⟩, ?_⟩
    · show 0 < inner ℝ e (ψ : E)
      rw [hψ, inner_hemiE e he]; exact hr
    · rw [hψ]
      have hxe : x = inner ℝ e x • e + perpProj e x := by simp [perpProj]
      have hPx' : ((t • ξ : perp e) : E) = perpProj e x := by
        rw [hξdef, smul_smul, mul_inv_cancel₀ ht0.ne', one_smul]; rfl
      unfold hemiE
      rw [smul_add, smul_smul, ← Submodule.coe_smul, hPx', ← hin]
      exact hxe.symm

theorem continuous_hemiE : Continuous (hemiE e) := by
  unfold hemiE; fun_prop

theorem hemiSet_subset_ball (s : Set (Metric.sphere (0 : E) 1)) :
    hemiSet e s ⊆ Metric.ball 0 1 := fun ξ hξ => by simpa using hξ.1

theorem hemiE_ne_zero (he : ‖e‖ = 1) (ξ : perp e) : hemiE e ξ ≠ 0 := by
  intro h0
  have h1 : ξ = 0 := by
    have := perpProj_hemiE e he ξ
    rw [h0] at this
    apply Subtype.ext
    simpa [perpProj] using this.symm
  have h2 := inner_hemiE e he ξ
  rw [h0, h1] at h2
  simp at h2

/-- The chart as a point of the unit sphere (total: the radial normalization of the graph point,
which is the graph point itself on the open unit ball). -/
def hemiPt (he : ‖e‖ = 1) (ξ : perp e) : Metric.sphere (0 : E) 1 :=
  ⟨‖hemiE e ξ‖⁻¹ • hemiE e ξ, by
    simp [norm_smul, (norm_ne_zero_iff.2 (hemiE_ne_zero e he ξ))]⟩

theorem coe_hemiPt_of_lt (he : ‖e‖ = 1) {ξ : perp e} (hξ : ‖ξ‖ < 1) :
    (hemiPt e he ξ : E) = hemiE e ξ := by
  simp [hemiPt, norm_hemiE e he hξ.le]

theorem continuous_hemiPt (he : ‖e‖ = 1) : Continuous (hemiPt e he) := by
  refine Continuous.subtype_mk ?_ _
  exact ((continuous_hemiE e).norm.inv₀ fun ξ => norm_ne_zero_iff.2 (hemiE_ne_zero e he ξ)).smul
    (continuous_hemiE e)

theorem inner_hemiPt_pos (he : ‖e‖ = 1) {ξ : perp e} (hξ : ‖ξ‖ < 1) :
    0 < inner ℝ e (hemiPt e he ξ : E) := by
  rw [coe_hemiPt_of_lt e he hξ, inner_hemiE e he]
  exact Real.sqrt_pos.2 (by nlinarith [norm_nonneg ξ])

theorem perpK_hemiE (he : ‖e‖ = 1) (ξ : perp e) : perpK e he (hemiE e ξ) = ξ :=
  Subtype.ext (perpProj_hemiE e he ξ)

/-- The chart is injective on the open unit ball of `e^⊥`. -/
theorem hemiPt_injOn (he : ‖e‖ = 1) : InjOn (hemiPt e he) (Metric.ball 0 1) := by
  intro ξ hξ ζ hζ h
  have h1 : ‖ξ‖ < 1 := by simpa using hξ
  have h2 : ‖ζ‖ < 1 := by simpa using hζ
  have h3 : hemiE e ξ = hemiE e ζ := by
    rw [← coe_hemiPt_of_lt e he h1, ← coe_hemiPt_of_lt e he h2, h]
  rw [← perpK_hemiE e he ξ, h3, perpK_hemiE]

/-- The chart maps the open unit ball of `e^⊥` onto the open hemisphere `⟨e, φ⟩ > 0`. -/
theorem hemiPt_image (he : ‖e‖ = 1) :
    hemiPt e he '' Metric.ball 0 1 = {φ : Metric.sphere (0 : E) 1 | 0 < inner ℝ e (φ : E)} := by
  ext φ
  constructor
  · rintro ⟨ξ, hξ, rfl⟩
    exact inner_hemiPt_pos e he (by simpa using hξ)
  · intro hφ
    have hφ1 : ‖(φ : E)‖ = 1 := by simp
    have h1 := norm_perpK_lt e he hφ1 hφ
    refine ⟨perpK e he φ, by simpa using h1, ?_⟩
    apply Subtype.ext
    rw [coe_hemiPt_of_lt e he h1, hemiE_perpK e he hφ1 hφ]

/-- The chart is smooth on the open unit ball. -/
theorem contDiffOn_hemiE (n : WithTop ℕ∞) : ContDiffOn ℝ n (hemiE e) (Metric.ball 0 1) := by
  unfold hemiE
  refine ContDiffOn.add (ContDiffOn.smul ?_ contDiffOn_const) (Submodule.subtypeL (perp e)).contDiff.contDiffOn
  refine ContDiffOn.sqrt (contDiffOn_const.sub (contDiff_norm_sq ℝ).contDiffOn) fun ξ hξ => ?_
  have : ‖ξ‖ < 1 := by simpa using hξ
  nlinarith [norm_nonneg ξ]

/-- The map `(η, a) ↦ η + a e` from `e^⊥ × ℝ` to `E`. -/
noncomputable def splitMap (he : ‖e‖ = 1) : perp e × ℝ → E :=
  fun p => ((ℝ ∙ e).orthogonalDecomposition).symm
    (WithLp.toLp 2 (LinearIsometryEquiv.toSpanUnitSingleton e he p.2, p.1))

theorem splitMap_apply (he : ‖e‖ = 1) (p : perp e × ℝ) : splitMap e he p = (p.1 : E) + p.2 • e := by
  simp [splitMap, add_comm]

theorem inner_splitMap (he : ‖e‖ = 1) (p : perp e × ℝ) : inner ℝ e (splitMap e he p) = p.2 := by
  rw [splitMap_apply, inner_add_right, inner_eq_of_mem_perp e p.1.2, inner_smul_right,
    real_inner_self_eq_norm_sq, he]; simp

theorem norm_sq_splitMap (he : ‖e‖ = 1) (p : perp e × ℝ) :
    ‖splitMap e he p‖ ^ 2 = p.2 ^ 2 + ‖(p.1 : E)‖ ^ 2 := by
  rw [splitMap_apply, norm_add_sq_real, real_inner_smul_right, real_inner_comm,
    inner_eq_of_mem_perp e p.1.2, norm_smul, he]
  simp; ring

theorem perpK_splitMap (he : ‖e‖ = 1) (p : perp e × ℝ) : perpK e he (splitMap e he p) = p.1 := by
  apply Subtype.ext
  have h := inner_splitMap e he p
  rw [splitMap_apply] at h
  simp only [perpK, perpProj, splitMap_apply]
  rw [h]; simp

theorem norm_splitMap (he : ‖e‖ = 1) (p : perp e × ℝ) :
    ‖splitMap e he p‖ = Real.sqrt (p.2 ^ 2 + ‖p.1‖ ^ 2) := by
  rw [← Real.sqrt_sq (norm_nonneg (splitMap e he p)), norm_sq_splitMap, norm_coe_perp]

theorem splitMap_preimage_coneE (he : ‖e‖ = 1) (T : Set (perp e)) :
    splitMap e he ⁻¹' coneE e he T = coneSet T := by
  ext p
  simp only [coneE, coneSet, mem_preimage, mem_ofPred_eq, inner_splitMap, norm_splitMap,
    perpK_splitMap]

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem measurePreserving_splitMap (he : ‖e‖ = 1) :
    MeasurePreserving (splitMap e he) volume volume := by
  have h1 : MeasurePreserving (fun p : perp e × ℝ => (LinearIsometryEquiv.toSpanUnitSingleton e he p.2, p.1))
      volume volume := by
    have := (LinearIsometryEquiv.toSpanUnitSingleton e he).measurePreserving.prod
      (MeasurePreserving.id (volume : Measure (perp e)))
    exact this.comp (Measure.measurePreserving_swap)
  have h2 := (WithLp.volume_preserving_toLp (ℝ ∙ e) (perp e))
  have h3 := ((ℝ ∙ e).orthogonalDecomposition).symm.measurePreserving
  exact h3.comp (h2.comp h1)

theorem measurableSet_coneE (he : ‖e‖ = 1) {T : Set (perp e)} (hT : MeasurableSet T) :
    MeasurableSet (coneE e he T) := by
  have hp : Measurable (perpK e he) := (continuous_perpK e he).measurable
  have hin : Continuous fun x : E => inner ℝ e x := continuous_const.inner continuous_id
  refine (measurableSet_lt measurable_const hin.measurable).inter
    ((measurableSet_lt measurable_norm measurable_const).inter
      (hT.preimage (measurable_norm.inv.smul hp)))

theorem volume_coneE (he : ‖e‖ = 1) {T : Set (perp e)} (hT : MeasurableSet T) :
    volume (coneE e he T) = volume (coneSet T) := by
  rw [← splitMap_preimage_coneE e he T]
  exact ((measurePreserving_splitMap e he).measure_preimage
    (measurableSet_coneE e he hT).nullMeasurableSet).symm

omit [FiniteDimensional ℝ E] in
theorem measurableSet_hemiSet {s : Set (Metric.sphere (0 : E) 1)} (hs : MeasurableSet s) :
    MeasurableSet (hemiSet e s) := by
  have h1 : MeasurableSet (Subtype.val '' s : Set E) :=
    MeasurableSet.subtype_image (Metric.isClosed_sphere.measurableSet) hs
  have : hemiSet e s = {ξ : perp e | ‖ξ‖ < 1} ∩ hemiE e ⁻¹' (Subtype.val '' s) := by
    ext ξ; simp only [hemiSet, mem_ofPred_eq, mem_inter_iff, mem_preimage, mem_image]
  rw [this]
  exact (measurableSet_lt measurable_norm measurable_const).inter
    ((continuous_hemiE e).measurable h1)

/-- **The sphere measure on the open hemisphere is the graph measure of the chart**
(`toSphere_eq_graph`): for measurable `s` on the unit sphere of `E`, the surface measure of the part
of `s` in the open hemisphere `⟨e, φ⟩ > 0` is the integral of `(1 - |ξ|²)^{-1/2}` over the
chart coordinates `ξ ∈ e^⊥` of that part. -/
theorem toSphere_hemisphere_apply (he : ‖e‖ = 1) {s : Set (Metric.sphere (0 : E) 1)}
    (hs : MeasurableSet s) :
    (volume : Measure E).toSphere (s ∩ {φ | 0 < inner ℝ e (φ : E)}) =
      ∫⁻ ξ in hemiSet e s, ENNReal.ofReal (1 / Real.sqrt (1 - ‖ξ‖ ^ 2)) := by
  have hin : Continuous fun x : E => inner ℝ e x := continuous_const.inner continuous_id
  have hH : MeasurableSet {φ : Metric.sphere (0 : E) 1 | 0 < inner ℝ e (φ : E)} :=
    measurableSet_lt measurable_const (hin.measurable.comp measurable_subtype_coe)
  rw [Measure.toSphere_apply' _ (hs.inter hH), cone_eq e he s,
    volume_coneE e he (measurableSet_hemiSet e hs), volume_coneSet_eq (measurableSet_hemiSet e hs),
    inter_eq_left.2 (hemiSet_subset_ball e s)]
  have hdim : Module.finrank ℝ E = Module.finrank ℝ (perp e) + 1 := by
    have h0 : 1 + Module.finrank ℝ (perp e) = Module.finrank ℝ E := by
      have := Submodule.finrank_add_finrank_orthogonal (ℝ ∙ e)
      rwa [finrank_span_singleton (by rintro rfl; simp at he)] at this
    omega
  rw [hdim, ← mul_assoc]
  convert one_mul _
  rw [show ((Module.finrank ℝ (perp e) + 1 : ℕ) : ℝ≥0∞) =
    ENNReal.ofReal ((Module.finrank ℝ (perp e) : ℝ) + 1) by
      rw [ENNReal.ofReal_add (by positivity) zero_le_one]; simp, ← ENNReal.ofReal_mul (by positivity)]
  rw [mul_one_div_cancel (by positivity)]; simp

/-- The surface measure restricted to the open hemisphere is the image of the weighted Lebesgue
measure of the unit ball of `e^⊥` under the chart. -/
theorem toSphere_restrict_hemisphere (he : ‖e‖ = 1) :
    ((volume : Measure E).toSphere).restrict {φ | 0 < inner ℝ e (φ : E)} =
      Measure.map (hemiPt e he)
        (((volume : Measure (perp e)).restrict (Metric.ball 0 1)).withDensity
          fun ξ => ENNReal.ofReal (1 / Real.sqrt (1 - ‖ξ‖ ^ 2))) := by
  have hin : Continuous fun x : E => inner ℝ e x := continuous_const.inner continuous_id
  have hH : MeasurableSet {φ : Metric.sphere (0 : E) 1 | 0 < inner ℝ e (φ : E)} :=
    measurableSet_lt measurable_const (hin.measurable.comp measurable_subtype_coe)
  ext s hs
  have hm := (continuous_hemiPt e he).measurable hs
  rw [Measure.restrict_apply hs, Measure.map_apply (continuous_hemiPt e he).measurable hs,
    withDensity_apply _ hm, Measure.restrict_restrict hm, toSphere_hemisphere_apply e he hs]
  congr 2
  ext ξ
  simp only [hemiSet, mem_ofPred_eq, mem_inter_iff, mem_preimage, mem_ball, dist_zero_right]
  symm
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h2, hemiPt e he ξ, h1, (coe_hemiPt_of_lt e he h2)⟩
  · rintro ⟨h2, φ, h3, h4⟩
    refine ⟨?_, h2⟩
    have : hemiPt e he ξ = φ := Subtype.ext ((coe_hemiPt_of_lt e he h2).trans h4.symm)
    rwa [this]

/-- The sphere integral over the open hemisphere in the chart (nonnegative form). -/
theorem lintegral_hemisphere (he : ‖e‖ = 1) {f : Metric.sphere (0 : E) 1 → ℝ≥0∞}
    (hf : Measurable f) :
    ∫⁻ φ in {φ : Metric.sphere (0 : E) 1 | 0 < inner ℝ e (φ : E)}, f φ ∂(volume : Measure E).toSphere =
      ∫⁻ ξ in Metric.ball (0 : perp e) 1,
        ENNReal.ofReal (1 / Real.sqrt (1 - ‖ξ‖ ^ 2)) * f (hemiPt e he ξ) := by
  rw [toSphere_restrict_hemisphere e he, lintegral_map hf (continuous_hemiPt e he).measurable,
    lintegral_withDensity_eq_lintegral_mul _ (by fun_prop)
      (show Measurable fun a => f (hemiPt e he a) from hf.comp (continuous_hemiPt e he).measurable)]
  rfl

/-- The sphere integral over the open hemisphere in the chart (real form). -/
theorem integral_hemisphere (he : ‖e‖ = 1) {f : Metric.sphere (0 : E) 1 → ℝ}
    (hf : Measurable f) :
    ∫ φ in {φ : Metric.sphere (0 : E) 1 | 0 < inner ℝ e (φ : E)}, f φ ∂(volume : Measure E).toSphere =
      ∫ ξ in Metric.ball (0 : perp e) 1, (1 / Real.sqrt (1 - ‖ξ‖ ^ 2)) * f (hemiPt e he ξ) := by
  rw [toSphere_restrict_hemisphere e he,
    integral_map (continuous_hemiPt e he).measurable.aemeasurable hf.aestronglyMeasurable]
  have hw : Measurable fun ξ : perp e => Real.toNNReal (1 / Real.sqrt (1 - ‖ξ‖ ^ 2)) := by fun_prop
  have := integral_withDensity_eq_integral_smul (μ := (volume : Measure (perp e)).restrict
    (Metric.ball 0 1)) hw (fun ξ => f (hemiPt e he ξ))
  rw [show (fun ξ : perp e => ENNReal.ofReal (1 / Real.sqrt (1 - ‖ξ‖ ^ 2))) =
    fun ξ => ((Real.toNNReal (1 / Real.sqrt (1 - ‖ξ‖ ^ 2)) : NNReal) : ℝ≥0∞) from rfl, this]
  refine setIntegral_congr_fun Metric.isOpen_ball.measurableSet fun ξ hξ => ?_
  have h1 : ‖ξ‖ < 1 := by simpa using hξ
  have : 0 ≤ 1 / Real.sqrt (1 - ‖ξ‖ ^ 2) := by positivity
  simp [NNReal.smul_def]

end Geometry

end Balaban.LargeField.SphereChart

namespace Balaban.LargeField

open SphereChart

/-- **`toSphere_eq_graph`** (LF-RECONSTRUCTION Lemma II.7.4 (a), Lean item Q2).  For a unit vector
`e ∈ ℝ^N` and a measurable set `s` of the unit sphere, the surface measure `Measure.toSphere` of
Lebesgue measure (the one-site factor of the frozen `aprioriMeasure`) of the part of `s` in the open
hemisphere `{φ · e > 0}` is `∫ (1 - |ξ|²)^{-1/2} dξ` over the chart coordinates
`ξ ∈ e^⊥`, `|ξ| < 1`, `√(1 - |ξ|²) e + ξ ∈ s`. -/
theorem toSphere_eq_graph {N : ℕ} (e : EuclideanSpace ℝ (Fin N)) (he : ‖e‖ = 1)
    {s : Set (Metric.sphere (0 : EuclideanSpace ℝ (Fin N)) 1)} (hs : MeasurableSet s) :
    (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin N))).toSphere
        (s ∩ {φ | 0 < inner ℝ e (φ : EuclideanSpace ℝ (Fin N))}) =
      ∫⁻ ξ in hemiSet e s, ENNReal.ofReal (1 / Real.sqrt (1 - ‖ξ‖ ^ 2)) :=
  toSphere_hemisphere_apply e he hs

end Balaban.LargeField
