/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Base.KF0GoodGaussian
public import Balaban.LargeField.Base.BaseChartMeasure
import Mathlib.Tactic.Linarith

/-!
# The hemisphere chart on the good sites of a fixed bad set (package W388)

Fixed bad set `D` of sites of the torus of side `ℓ`, good sites `G = Dᶜ` (the subtype `Good D`),
bad spins `q` fixed.  This file gives the lemmas (i) and (ii) listed in the module doc of
`KF0GoodGaussian.lean` and the resulting form of the inner good-spin integral of
`kf0Sector_iterated`.

* `lintegral_sphere_pi_chart` (T1): the hemisphere chart measure formula on an arbitrary finite set
  `ι` of sites.  The landed full-torus `lintegral_restrictedIntegrand` is the case `ι = Torus d ℓ`
  with the integrand `restrictedIntegrand`.
* `goodExt`, `goodNormal`, `badExt`, `goodBdryLin`, `goodBdryNormal`, `goodBdryConst`,
  `goodRemainder` (T2): the named terms.  `goodEnergy_chart` is the exact identity, for good spins
  `p_x = hemiPt h ((√β)⁻¹ v_x)` with `‖v_x‖² < β` and bad spins `q`,
  `β goodEnergy(glue q p) = ½ goodQuad(v) + goodBdryLin + goodBdryNormal + goodBdryConst
  + goodRemainder`.
* `inner_pos_of_goodWeight_ne_zero`: if `goodWeight ≠ 0` and `r ≤ 1` every good spin lies in the
  open upper hemisphere.
* `lintegral_goodInner_gaussian` (T3): the inner integral as `β^{-|G|(N-1)/2} N_G ∫ dγ_G(ψ)` of the
  chart Jacobian, `goodWeight` and the exponential of minus the boundary, normal and remainder
  terms plus the sources, evaluated at `v = C_G ψ`.
* `goodChart_instance` (T4).

Everything is for a FIXED bad set.  The sum over sectors with one common reference measure (H37.6),
the linked expansion and the one-scale theorem are NOT proved here.
-/

@[expose] public section

set_option linter.unusedSectionVars false

open MeasureTheory Matrix

namespace Balaban.LargeField

open SphereChart

open scoped Classical

/-! ### T1: the chart measure on an arbitrary finite set of sites -/

section ChartMeasure

variable {ι : Type*} [Fintype ι] {N : ℕ}

/-- The configuration of the sites `ι` with chart coordinates `ξ` around `h`. -/
noncomputable def chartCfgOn (h : EuclideanSpace ℝ (Fin N)) (hh : ‖h‖ = 1) (ξ : ι → perp h) :
    ι → SpinSphere N := fun x => hemiPt h hh (ξ x)

theorem prod_chartWeight_scaled {β : ℝ} (hβ : 0 < β) {h : EuclideanSpace ℝ (Fin N)}
    (v : ι → perp h) :
    (∏ x : ι, ENNReal.ofReal (chartWeight h (((Real.sqrt β)⁻¹ • v) x))) =
      ENNReal.ofReal (chartJac β (fun x => (v x : EuclideanSpace ℝ (Fin N)))) := by
  by_cases hb : ∀ x, ‖v x‖ < Real.sqrt β
  · rw [chartJac_of_lt (w := fun x => (v x : EuclideanSpace ℝ (Fin N))) hb,
      ENNReal.ofReal_prod_of_nonneg (fun x _ => by positivity)]
    refine Finset.prod_congr rfl fun x _ => ?_
    rw [Pi.smul_apply, chartWeight_inv_sqrt_smul hβ]
    have hx : ‖(v x : EuclideanSpace ℝ (Fin N))‖ < Real.sqrt β := hb x
    simp only [hx, ↓reduceIte]
  · push Not at hb
    obtain ⟨x₀, hx₀⟩ := hb
    rw [chartJac_eq_zero (w := fun x => (v x : EuclideanSpace ℝ (Fin N))) (x₀ := x₀) (not_lt.2 hx₀),
      ENNReal.ofReal_zero]
    refine Finset.prod_eq_zero (Finset.mem_univ x₀) ?_
    rw [Pi.smul_apply, chartWeight_inv_sqrt_smul hβ]
    have hx : ¬ ‖(v x₀ : EuclideanSpace ℝ (Fin N))‖ < Real.sqrt β := not_lt.2 hx₀
    simp only [hx, ↓reduceIte, ENNReal.ofReal_zero]

/-- **The chart measure formula on a finite set of sites** (T1).  For `β > 0`, `|h| = 1` and a
measurable `f ≥ 0` on `ι → S^{N-1}` vanishing unless every spin lies in the open hemisphere
`⟨h, φ_x⟩ > 0`,
`∫ f d(⊗_{x∈ι} σ) = ((√β)⁻¹)^{|ι|(N-1)} ∫ J_β(v) f(chart((√β)⁻¹ v)) dv`,
`J_β(v) = ∏_x 1[‖v_x‖ < √β](1 - ‖v_x‖²/β)^{-1/2}` (`chartJac`), `dv` Lebesgue measure on
`ι → h^⊥`.  The landed full-torus `lintegral_restrictedIntegrand` is the case `ι = Torus d ℓ`. -/
theorem lintegral_sphere_pi_chart {β : ℝ} (hβ : 0 < β) {h : EuclideanSpace ℝ (Fin N)}
    (hh : ‖h‖ = 1) (f : (ι → SpinSphere N) → ENNReal) (hf : Measurable f)
    (hsupp : ∀ φ : ι → SpinSphere N,
      (∃ x, ¬ 0 < inner ℝ h (φ x : EuclideanSpace ℝ (Fin N))) → f φ = 0) :
    ∫⁻ φ, f φ ∂(Measure.pi fun _ : ι => (volume : Measure (EuclideanSpace ℝ (Fin N))).toSphere) =
      ENNReal.ofReal (((Real.sqrt β)⁻¹) ^ (Fintype.card ι * (N - 1))) *
        ∫⁻ v : ι → perp h,
          ENNReal.ofReal (chartJac β (fun x => (v x : EuclideanSpace ℝ (Fin N)))) *
            f (chartCfgOn h hh ((Real.sqrt β)⁻¹ • v))
          ∂(Measure.pi fun _ => (volume : Measure (perp h))) := by
  have hspos : 0 < (Real.sqrt β)⁻¹ := inv_pos.2 (Real.sqrt_pos.2 hβ)
  have hA := lintegral_sphere_pi_hemisphere (ι := ι) (fun _ => h) (fun _ => hh) f hf hsupp
  rw [hA]
  set Φ : (ι → perp h) → ENNReal := fun ξ =>
    (∏ x, ENNReal.ofReal (chartWeight h (ξ x))) * f (chartMapPi (fun _ => h) (fun _ => hh) ξ)
    with hΦ
  have hΦm : Measurable Φ :=
    (Finset.measurable_prod _ fun x _ => ENNReal.measurable_ofReal.comp
      ((measurable_chartWeight h).comp (measurable_pi_apply x))).mul
      (hf.comp (measurable_chartMapPi (fun _ => h) (fun _ => hh)))
  have hB := lintegral_eq_pow_mul_lintegral_smul
    (Measure.pi fun _ : ι => (volume : Measure (perp h))) hspos hΦm
  rw [show Module.finrank ℝ (ι → perp h) = Fintype.card ι * (N - 1) from
    finrank_pi_perp (fun _ : ι => h) (fun _ => hh)] at hB
  refine hB.trans ?_
  congr 1
  refine lintegral_congr fun v => ?_
  simp only [hΦ]
  rw [prod_chartWeight_scaled hβ v]
  rfl

end ChartMeasure

/-! ### T2: the good energy in chart coordinates -/

section Terms

variable {d N ℓ : ℕ} [NeZero ℓ] (D : Finset (Torus d ℓ)) {h : EuclideanSpace ℝ (Fin N)}

/-- A tangent field on the good sites extended by zero to the whole torus. -/
noncomputable def goodExt (v : Good D → perp h) : Torus d ℓ → perp h :=
  fun x => if hx : x ∈ D then 0 else v ⟨x, hx⟩

/-- The normal coordinates `w_x = √β(√(1 - ‖v_x‖²/β) - 1)` of the good sites, zero on `D`. -/
noncomputable def goodNormal (β : ℝ) (v : Good D → perp h) : Torus d ℓ → ℝ :=
  fun x => normalCoord β ‖goodExt D v x‖

/-- The bad spins extended to the whole torus by the background `h` off `D`. -/
noncomputable def badExt (h : EuclideanSpace ℝ (Fin N)) (q : ↥D → SpinSphere N) :
    Torus d ℓ → EuclideanSpace ℝ (Fin N) :=
  fun x => if hx : x ∈ D then (q ⟨x, hx⟩ : EuclideanSpace ℝ (Fin N)) else h

/-- The boundary linear term `√β ∑_{crossing (x,μ)} ⟨h - q_y, v_z⟩`, `y` the endpoint in `D`,
`z` the endpoint in `G`.  (Each bond `(x,μ)` is counted once, as in the frozen energy.) -/
noncomputable def goodBdryLin (β : ℝ) (q : ↥D → SpinSphere N) (v : Good D → perp h) : ℝ :=
  Real.sqrt β * ∑ x : Torus d ℓ, ∑ μ : Fin d,
    (if IsCrossing D x μ then
      inner ℝ (h - badExt D h q (blockEnd D x μ))
        (goodExt D v (goodEnd D x μ) : EuclideanSpace ℝ (Fin N)) else 0)

/-- The boundary normal term `√β ∑_{crossing (x,μ)} w_z ⟨h - q_y, h⟩`. -/
noncomputable def goodBdryNormal (β : ℝ) (q : ↥D → SpinSphere N) (v : Good D → perp h) : ℝ :=
  Real.sqrt β * ∑ x : Torus d ℓ, ∑ μ : Fin d,
    (if IsCrossing D x μ then
      goodNormal D β v (goodEnd D x μ) * inner ℝ (h - badExt D h q (blockEnd D x μ)) h else 0)

/-- The boundary constant `(β/2) ∑_{crossing (x,μ)} ‖h - q_y‖²`. -/
noncomputable def goodBdryConst (h : EuclideanSpace ℝ (Fin N)) (β : ℝ) (q : ↥D → SpinSphere N) : ℝ :=
  (β / 2) * ∑ x : Torus d ℓ, ∑ μ : Fin d,
    (if IsCrossing D x μ then ‖h - badExt D h q (blockEnd D x μ)‖ ^ 2 else 0)

/-- The remainder of the good energy: the quadratic energy of the normal coordinates
`½ ∑ (w_{x+e_μ} - w_x)² + (ν/2) ∑ w_x²` (with `w = 0` on `D`, so the crossing bonds contribute
`½ w_z²`). -/
noncomputable def goodRemainder (β ν : ℝ) (v : Good D → perp h) : ℝ :=
  (1 / 2) * ∑ x : Torus d ℓ, ∑ μ : Fin d,
      (goodNormal D β v (x + Pi.single μ 1) - goodNormal D β v x) ^ 2
    + (ν / 2) * ∑ x : Torus d ℓ, goodNormal D β v x ^ 2

theorem goodExt_of_mem (v : Good D → perp h) {x : Torus d ℓ} (hx : x ∈ D) :
    goodExt D v x = 0 := by simp [goodExt, hx]

theorem goodExt_of_not_mem (v : Good D → perp h) {x : Torus d ℓ} (hx : x ∉ D) :
    goodExt D v x = v ⟨x, hx⟩ := by simp [goodExt, hx]

theorem goodNormal_of_mem (β : ℝ) (v : Good D → perp h) {x : Torus d ℓ} (hx : x ∈ D) :
    goodNormal D β v x = 0 := by
  simp [goodNormal, goodExt_of_mem D v hx, normalCoord]

theorem badExt_of_mem (q : ↥D → SpinSphere N) {x : Torus d ℓ} (hx : x ∈ D) :
    badExt D h q x = (q ⟨x, hx⟩ : EuclideanSpace ℝ (Fin N)) := by simp [badExt, hx]

/-- The one-site chart point: `hemiPt h ((√β)⁻¹ w) = h + (√β)⁻¹ (w + w_N h)` for `‖w‖² < β`. -/
theorem coe_hemiPt_scaled {β : ℝ} (hβ : 0 < β) (hh : ‖h‖ = 1) (w : perp h)
    (hw : ‖w‖ ^ 2 < β) :
    (hemiPt h hh ((Real.sqrt β)⁻¹ • w) : EuclideanSpace ℝ (Fin N)) =
      h + (Real.sqrt β)⁻¹ • ((w : EuclideanSpace ℝ (Fin N)) + normalCoord β ‖w‖ • h) := by
  have hlt : ‖(Real.sqrt β)⁻¹ • w‖ < 1 :=
    (norm_inv_sqrt_smul_lt_one_iff hβ w).2 (Real.lt_sqrt (norm_nonneg _) |>.2 hw)
  rw [coe_hemiPt_of_lt h hh hlt, chartPoint_eq β hβ h w]
  rfl

/-- Sums over the torus of functions vanishing on `D` are sums over `G`. -/
theorem sum_good_eq (F : Torus d ℓ → ℝ) (hF : ∀ x ∈ D, F x = 0) :
    ∑ x : Torus d ℓ, F x = ∑ x : Good D, F x.1 := by
  rw [← Fintype.sum_subtype_add_sum_subtype (fun x : Torus d ℓ => x ∉ D) F]
  have : ∑ x : {x : Torus d ℓ // ¬ (x ∉ D)}, F x.1 = 0 :=
    Finset.sum_eq_zero fun x _ => hF x.1 (by simpa using x.2)
  rw [this, add_zero]

/-- The quadratic form of the principal submatrix `K_G` is that of `-Δ + ν` on the extension by
zero. -/
theorem goodQuad_eq_tangentQuad (ν : ℝ) (v : Good D → perp h) :
    goodQuad D ν v = tangentQuad ν (goodExt D v) := by
  unfold goodQuad tangentQuad
  refine Finset.sum_congr rfl fun i _ => ?_
  have h0 : ∀ x ∈ D, ((goodExt D v x : perp h) : EuclideanSpace ℝ (Fin N)) i = 0 := fun x hx => by
    simp [goodExt_of_mem D v hx]
  have hae : ∀ x : Good D, ((goodExt D v x.1 : perp h) : EuclideanSpace ℝ (Fin N)) i =
      ((v x : perp h) : EuclideanSpace ℝ (Fin N)) i := fun x => by
    rw [goodExt_of_not_mem D v x.2]
  simp only [dotProduct, Matrix.mulVec]
  rw [sum_good_eq D (fun x => ((goodExt D v x : perp h) : EuclideanSpace ℝ (Fin N)) i *
    ∑ y, latticeLaplacian d ℓ ν x y * ((goodExt D v y : perp h) : EuclideanSpace ℝ (Fin N)) i)
    (fun x hx => by simp [h0 x hx])]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [hae x]
  congr 1
  rw [sum_good_eq D (fun y => latticeLaplacian d ℓ ν x.1 y *
    ((goodExt D v y : perp h) : EuclideanSpace ℝ (Fin N)) i) (fun y hy => by simp [h0 y hy])]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [hae y]
  rfl

theorem cross_alg {r U Wg I J B : ℝ} (hr : 0 < r) :
    r ^ 2 * ((1 / 2) * ((r⁻¹) ^ 2 * (U + Wg ^ 2)) + r⁻¹ * (I + Wg * J) + (1 / 2) * B) =
      (1 / 2) * (U + Wg ^ 2) + r * I + r * (Wg * J) + r ^ 2 / 2 * B := by
  field_simp
  ring

theorem bond_norm_sq (hh : ‖h‖ = 1) (a b : perp h) (wa wb t : ℝ) :
    ‖t • ((wb - wa) • h + ((b - a : perp h) : EuclideanSpace ℝ (Fin N)))‖ ^ 2 =
      t ^ 2 * ((wb - wa) ^ 2 + ‖b - a‖ ^ 2) := by
  rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, norm_sq_smul_add_perp hh]

/-- **The good energy in chart coordinates** (T2).  For `β > 0`, `|h| = 1`, bad spins `q`,
tangent variables `v` on the good sites with `‖v_x‖² < β`, and the good spins
`p_x = hemiPt h ((√β)⁻¹ v_x)`:
`β H_G(q ∪ p) = ½ ⟨v, K_G v⟩ + (boundary linear) + (boundary normal) + (boundary constant)
  + (remainder)`.  For `D = ∅` there are no boundary terms and this is the landed
`energy_chartCfg`. -/
theorem goodEnergy_chart {β ν : ℝ} (hβ : 0 < β) (hh : ‖h‖ = 1) (q : ↥D → SpinSphere N)
    (v : Good D → perp h) (hv : ∀ x, ‖v x‖ ^ 2 < β) :
    β * goodEnergy ν h D (glue D q (chartCfgOn h hh ((Real.sqrt β)⁻¹ • v))) =
      (1 / 2) * goodQuad D ν v + goodBdryLin D β q v + goodBdryNormal D β q v
        + goodBdryConst D h β q + goodRemainder D β ν v := by
  have hr : 0 < Real.sqrt β := Real.sqrt_pos.2 hβ
  have hsq : Real.sqrt β ^ 2 = β := Real.sq_sqrt hβ.le
  set s := (Real.sqrt β)⁻¹ with hs
  set φ := glue D q (chartCfgOn h hh (s • v)) with hφ
  set u := goodExt D v with hu
  set W := goodNormal D β v with hW
  have hgood : ∀ x (hx : x ∉ D), (φ x : EuclideanSpace ℝ (Fin N)) - h =
      s • (W x • h + (u x : EuclideanSpace ℝ (Fin N))) := by
    intro x hx
    have h1 : φ x = hemiPt h hh (s • v ⟨x, hx⟩) := by
      rw [hφ, glue_of_not_mem D q _ x hx]; rfl
    rw [h1, coe_hemiPt_scaled hβ hh _ (hv _)]
    have e1 : u x = v ⟨x, hx⟩ := goodExt_of_not_mem D v hx
    have e2 : W x = normalCoord β ‖v ⟨x, hx⟩‖ := by
      show normalCoord β ‖goodExt D v x‖ = _
      rw [goodExt_of_not_mem D v hx]
    rw [e1, e2]
    module
  have hbad : ∀ x (hx : x ∈ D), h - (φ x : EuclideanSpace ℝ (Fin N)) = h - badExt D h q x := by
    intro x hx
    rw [hφ, glue_of_mem D q _ x hx, badExt_of_mem D q hx]
  have hu0 : ∀ x ∈ D, u x = 0 := fun x hx => goodExt_of_mem D v hx
  have hW0 : ∀ x ∈ D, W x = 0 := fun x hx => goodNormal_of_mem D β v hx
  have hnorm : ∀ x (hx : x ∉ D), ‖(φ x : EuclideanSpace ℝ (Fin N)) - h‖ ^ 2 =
      s ^ 2 * (W x ^ 2 + ‖u x‖ ^ 2) := by
    intro x hx
    rw [hgood x hx, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, norm_sq_smul_add_perp hh]
  have hinn : ∀ x (hx : x ∉ D) (c : EuclideanSpace ℝ (Fin N)),
      inner ℝ c ((φ x : EuclideanSpace ℝ (Fin N)) - h) =
        s * (inner ℝ c (u x : EuclideanSpace ℝ (Fin N)) + W x * inner ℝ c h) := by
    intro x hx c
    rw [hgood x hx, inner_smul_right, inner_add_right, inner_smul_right]
    ring
  have hbond : ∀ (x : Torus d ℓ) (μ : Fin d),
      β * ((1 / 2) * (if x ∉ D ∧ x + Pi.single μ 1 ∉ D then
          ‖((φ (x + Pi.single μ 1) : EuclideanSpace ℝ (Fin N)) - h) -
            ((φ x : EuclideanSpace ℝ (Fin N)) - h)‖ ^ 2 else 0)
        + (1 / 2) * (if IsCrossing D x μ then
          ‖(φ (goodEnd D x μ) : EuclideanSpace ℝ (Fin N)) - h‖ ^ 2 else 0)
        + (if IsCrossing D x μ then
          inner ℝ (h - (φ (blockEnd D x μ) : EuclideanSpace ℝ (Fin N)))
            ((φ (goodEnd D x μ) : EuclideanSpace ℝ (Fin N)) - h) else 0)
        + (1 / 2) * (if IsCrossing D x μ then
          ‖h - (φ (blockEnd D x μ) : EuclideanSpace ℝ (Fin N))‖ ^ 2 else 0)) =
      (1 / 2) * ‖u (x + Pi.single μ 1) - u x‖ ^ 2
        + (1 / 2) * (W (x + Pi.single μ 1) - W x) ^ 2
        + Real.sqrt β * (if IsCrossing D x μ then
          inner ℝ (h - badExt D h q (blockEnd D x μ))
            (u (goodEnd D x μ) : EuclideanSpace ℝ (Fin N)) else 0)
        + Real.sqrt β * (if IsCrossing D x μ then
          W (goodEnd D x μ) * inner ℝ (h - badExt D h q (blockEnd D x μ)) h else 0)
        + (β / 2) * (if IsCrossing D x μ then
          ‖h - badExt D h q (blockEnd D x μ)‖ ^ 2 else 0) := by
    intro x μ
    generalize hy : x + Pi.single μ 1 = y
    by_cases hx : x ∈ D <;> by_cases hy' : y ∈ D
    · simp [IsCrossing, hy, hx, hy', hu0 x hx, hu0 y hy', hW0 x hx, hW0 y hy']
    · -- x ∈ D, y ∉ D : crossing, goodEnd = y, blockEnd = x
      have hc : IsCrossing D x μ := by simp [IsCrossing, hy, hx, hy']
      have hge : goodEnd D x μ = y := by simp [goodEnd, hy, hx]
      have hbe : blockEnd D x μ = x := by simp [blockEnd, hx]
      simp only [hc, hge, hbe, hx, hy', ↓reduceIte, not_true_eq_false, false_and, mul_zero,
        zero_add, hbad x hx, hnorm y hy', hinn y hy', hu0 x hx, hW0 x hx, sub_zero,
        hs]
      have := cross_alg (r := Real.sqrt β) (U := ‖u y‖ ^ 2) (Wg := W y)
        (I := inner ℝ (h - badExt D h q x) (u y : EuclideanSpace ℝ (Fin N)))
        (J := inner ℝ (h - badExt D h q x) h) (B := ‖h - badExt D h q x‖ ^ 2) hr
      rw [hsq] at this
      linarith
    · -- x ∉ D, y ∈ D
      have hc : IsCrossing D x μ := by simp [IsCrossing, hy, hx, hy']
      have hge : goodEnd D x μ = x := by simp [goodEnd, hx]
      have hbe : blockEnd D x μ = y := by simp [blockEnd, hy, hx]
      simp only [hc, hge, hbe, hx, hy', ↓reduceIte, not_true_eq_false, and_false, mul_zero,
        zero_add, hbad y hy', hnorm x hx, hinn x hx, hu0 y hy', hW0 y hy', zero_sub,
        norm_neg, hs, not_false_eq_true]
      have := cross_alg (r := Real.sqrt β) (U := ‖u x‖ ^ 2) (Wg := W x)
        (I := inner ℝ (h - badExt D h q y) (u x : EuclideanSpace ℝ (Fin N)))
        (J := inner ℝ (h - badExt D h q y) h) (B := ‖h - badExt D h q y‖ ^ 2) hr
      rw [hsq] at this
      linarith
    · -- both good
      have hc : ¬ IsCrossing D x μ := by simp [IsCrossing, hy, hx, hy']
      have e : (φ y : EuclideanSpace ℝ (Fin N)) - h - ((φ x : EuclideanSpace ℝ (Fin N)) - h) =
          s • ((W y - W x) • h + ((u y - u x : perp h) : EuclideanSpace ℝ (Fin N))) := by
        rw [hgood y hy', hgood x hx, Submodule.coe_sub]; module
      simp only [hc, hx, hy', not_false_eq_true, and_self, ↓reduceIte, mul_zero, add_zero, e,
        bond_norm_sq hh]
      rw [hs, inv_pow, hsq]
      field_simp
      ring
  have hsite : ∀ x : Torus d ℓ, β * ((ν / 2) * (if x ∈ D then 0 else
      ‖(φ x : EuclideanSpace ℝ (Fin N)) - h‖ ^ 2)) =
      (ν / 2) * ‖u x‖ ^ 2 + (ν / 2) * W x ^ 2 := by
    intro x
    by_cases hx : x ∈ D
    · simp [hx, hu0 x hx, hW0 x hx]
    · simp only [hx, ↓reduceIte, hnorm x hx, hs, inv_pow, hsq]
      field_simp
      ring
  have hL : β * goodEnergy ν h D φ =
      ∑ x : Torus d ℓ, ∑ μ : Fin d, β * ((1 / 2) * (if x ∉ D ∧ x + Pi.single μ 1 ∉ D then
          ‖((φ (x + Pi.single μ 1) : EuclideanSpace ℝ (Fin N)) - h) -
            ((φ x : EuclideanSpace ℝ (Fin N)) - h)‖ ^ 2 else 0)
        + (1 / 2) * (if IsCrossing D x μ then
          ‖(φ (goodEnd D x μ) : EuclideanSpace ℝ (Fin N)) - h‖ ^ 2 else 0)
        + (if IsCrossing D x μ then
          inner ℝ (h - (φ (blockEnd D x μ) : EuclideanSpace ℝ (Fin N)))
            ((φ (goodEnd D x μ) : EuclideanSpace ℝ (Fin N)) - h) else 0)
        + (1 / 2) * (if IsCrossing D x μ then
          ‖h - (φ (blockEnd D x μ) : EuclideanSpace ℝ (Fin N))‖ ^ 2 else 0))
      + ∑ x : Torus d ℓ, β * ((ν / 2) * (if x ∈ D then 0 else
          ‖(φ x : EuclideanSpace ℝ (Fin N)) - h‖ ^ 2)) := by
    rw [goodEnergy_expand]
    simp only [mul_add, Finset.mul_sum, Finset.sum_add_distrib]
    ring
  rw [hL, goodQuad_eq_tangentQuad, ← tangentEnergy_eq]
  simp only [Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun μ _ => hbond x μ,
    Finset.sum_congr rfl fun x _ => hsite x]
  unfold tangentEnergy goodRemainder goodBdryLin goodBdryNormal goodBdryConst
  simp only [Finset.mul_sum, Finset.sum_add_distrib]
  ring

/-! ### The source in chart coordinates -/

/-- The pairing `⟨g_G, h⟩ = ∑_{x∈G} ∑_i g_x(i) h_i` of the good sites. -/
noncomputable def goodSourceConst (g : Torus d ℓ → Fin N → ℝ) (h : EuclideanSpace ℝ (Fin N)) : ℝ :=
  ∑ x : Good D, ∑ i : Fin N, g x i * h i

/-- The pairing `⟨g_G, v⟩ = ∑_{x∈G} ∑_i g_x(i) v_x(i)` with the tangent field. -/
noncomputable def goodSourceTangent (g : Torus d ℓ → Fin N → ℝ) (v : Good D → perp h) : ℝ :=
  ∑ x : Good D, ∑ i : Fin N, g x i * ((v x : EuclideanSpace ℝ (Fin N)) i)

/-- The normal part `∑_{x∈G} (g_x · h) w_x`, `w_x = normalCoord β ‖v_x‖`. -/
noncomputable def goodSourceNormal (g : Torus d ℓ → Fin N → ℝ) (β : ℝ) (v : Good D → perp h) : ℝ :=
  ∑ x : Good D, (∑ i : Fin N, g x i * h i) * normalCoord β ‖v x‖

/-- The source of the good spins in chart coordinates:
`⟨g_G, φ_G⟩ = ⟨g_G, h⟩ + (√β)⁻¹ ⟨g_G, v⟩ + (√β)⁻¹ ∑ (g_x · h) w_x`. -/
theorem sourceOut_chart {β : ℝ} (hβ : 0 < β) (hh : ‖h‖ = 1) (g : Torus d ℓ → Fin N → ℝ)
    (v : Good D → perp h) (hv : ∀ x, ‖v x‖ ^ 2 < β) :
    sourceOut D g (chartCfgOn h hh ((Real.sqrt β)⁻¹ • v)) =
      goodSourceConst D g h + (Real.sqrt β)⁻¹ * goodSourceTangent D g v
        + (Real.sqrt β)⁻¹ * goodSourceNormal D g β v := by
  unfold sourceOut goodSourceConst goodSourceTangent goodSourceNormal
  have hsite : ∀ x : Good D, ∑ i : Fin N, g x i *
      ((chartCfgOn h hh ((Real.sqrt β)⁻¹ • v) x : EuclideanSpace ℝ (Fin N)) i) =
      ∑ i : Fin N, g x i * h i + (Real.sqrt β)⁻¹ * ∑ i : Fin N, g x i *
        ((v x : EuclideanSpace ℝ (Fin N)) i)
      + (Real.sqrt β)⁻¹ * ((∑ i : Fin N, g x i * h i) * normalCoord β ‖v x‖) := by
    intro x
    have hc : ((chartCfgOn h hh ((Real.sqrt β)⁻¹ • v) x : SpinSphere N) :
        EuclideanSpace ℝ (Fin N)) =
        h + (Real.sqrt β)⁻¹ • ((v x : EuclideanSpace ℝ (Fin N)) + normalCoord β ‖v x‖ • h) :=
      coe_hemiPt_scaled hβ hh (v x) (hv x)
    rw [hc]
    have e : ∀ i : Fin N, g x i * ((h + (Real.sqrt β)⁻¹ • ((v x : EuclideanSpace ℝ (Fin N)) +
        normalCoord β ‖v x‖ • h) : EuclideanSpace ℝ (Fin N)) i) =
        g x i * h i + (Real.sqrt β)⁻¹ * (g x i * ((v x : EuclideanSpace ℝ (Fin N)) i))
          + (Real.sqrt β)⁻¹ * (normalCoord β ‖v x‖ * (g x i * h i)) := by
      intro i
      simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
      ring
    simp only [e, Finset.sum_add_distrib, ← Finset.mul_sum]
    ring
  simp only [hsite, Finset.sum_add_distrib, ← Finset.mul_sum]

/-- The exponent left after the Gaussian part `-½⟨v, K_G v⟩` has been taken out:
`-(boundary linear + boundary normal + boundary constant + remainder) + sources`. -/
noncomputable def goodChartExponent (β ν : ℝ) (g : Torus d ℓ → Fin N → ℝ)
    (h : EuclideanSpace ℝ (Fin N)) (q : ↥D → SpinSphere N) (v : Good D → perp h) : ℝ :=
  -(goodBdryLin D β q v + goodBdryNormal D β q v + goodBdryConst D h β q
      + goodRemainder D β ν v)
    + (goodSourceConst D g h + (Real.sqrt β)⁻¹ * goodSourceTangent D g v
      + (Real.sqrt β)⁻¹ * goodSourceNormal D g β v)

/-! ### Good spins lie in the upper hemisphere -/

theorem inner_pos_of_norm_sub_lt {a h : EuclideanSpace ℝ (Fin N)} (ha : ‖a‖ = 1) (hh : ‖h‖ = 1)
    {r : ℝ} (hr : r ≤ 1) (hlt : ‖a - h‖ < r) : 0 < inner ℝ h a := by
  have h1 : ‖a - h‖ ^ 2 < 1 := by nlinarith [norm_nonneg (a - h)]
  rw [norm_sub_sq_real, ha, hh, real_inner_comm] at h1
  linarith

theorem measurable_goodWeight {m : ℕ} [NeZero m] (s : ℕ) (r : ℝ) (B : Finset (Torus d m)) :
    Measurable (goodWeight D h s m r B) := by
  unfold goodWeight
  refine Finset.measurable_prod _ fun Q _ => ?_
  unfold chiOut
  refine Measurable.ite ?_ measurable_const measurable_const
  have : {p : Good D → SpinSphere N | ∀ x : Good D, blockMap s m x.1 = Q →
        ‖(p x : EuclideanSpace ℝ (Fin N)) - h‖ < r} =
      ⋂ x : Good D, {p | blockMap s m x.1 = Q → ‖(p x : EuclideanSpace ℝ (Fin N)) - h‖ < r} := by
    ext p; simp
  rw [show {p : Good D → SpinSphere N | ∀ x : Good D, blockMap s m x.1 = Q →
        ‖(p x : EuclideanSpace ℝ (Fin N)) - h‖ < r} = _ from this]
  refine MeasurableSet.iInter fun x => ?_
  by_cases hQ : blockMap s m x.1 = Q
  · simp only [hQ, true_imp_iff]
    exact measurableSet_lt ((continuous_subtype_val.comp (continuous_apply x)).sub
      continuous_const).norm.measurable measurable_const
  · simp [hQ]

/-- **The good spins lie in the upper hemisphere.**  For `D = siteUnion B`, `0 ≤ r ≤ 1`, `|h| = 1`:
if `goodWeight ≠ 0` then `⟨h, p_x⟩ > 0` for every good site `x` (since `‖p_x - h‖ < r ≤ 1`). -/
theorem inner_pos_of_goodWeight_ne_zero {m : ℕ} [NeZero m] (s : ℕ) {r : ℝ} (hr : r ≤ 1)
    (hh : ‖h‖ = 1) (B : Finset (Torus d m)) (hD : D = siteUnion (ℓ := ℓ) s m B)
    (p : Good D → SpinSphere N) (hp : goodWeight D h s m r B p ≠ 0) (x : Good D) :
    0 < inner ℝ h (p x : EuclideanSpace ℝ (Fin N)) := by
  subst hD
  have hxB : blockMap s m x.1 ∉ B := fun hb => x.2 ((mem_siteUnion s m B x.1).2 hb)
  unfold goodWeight at hp
  have h1 := (Finset.prod_ne_zero_iff.1 hp) (blockMap s m x.1) (by simp [hxB])
  unfold chiOut at h1
  by_cases hc : ∀ y : Good (siteUnion (ℓ := ℓ) s m B), blockMap s m y.1 = blockMap s m x.1 →
      ‖(p y : EuclideanSpace ℝ (Fin N)) - h‖ < r
  · exact inner_pos_of_norm_sub_lt (mem_sphere_zero_iff_norm.1 (p x).2) hh hr (hc x rfl)
  · simp only [hc, ite_false, ne_eq, not_true_eq_false] at h1

/-! ### T3: the inner good-spin integral as a Gaussian integral -/

theorem measurable_glue_right (q : ↥D → SpinSphere N) : Measurable (glue D q) :=
  (MeasurableEquiv.measurable _).comp (measurable_const.prodMk measurable_id)

theorem measurable_sourceOut (g : Torus d ℓ → Fin N → ℝ) : Measurable (sourceOut D g) := by
  unfold sourceOut
  refine Finset.measurable_sum _ fun x _ => Finset.measurable_sum _ fun i _ => ?_
  exact (continuous_const.mul ((EuclideanSpace.proj i).continuous.comp
    (continuous_subtype_val.comp (continuous_apply x)))).measurable

theorem goodEnergy_glue (ν : ℝ) (q : ↥D → SpinSphere N) (p : Good D → SpinSphere N) :
    goodEnergy ν h D (glue D q p) = energy d N ℓ ν h (glue D q p) - blockEnergyIn D ν h q := by
  have := energy_split ν h D (glue D q p)
  rw [blockEnergy_glue] at this
  linarith

/-- **The inner good-spin integral as a Gaussian integral** (T3).  Let `D = siteUnion B` (a fixed
bad set), `G = Dᶜ`, bad spins `q` fixed, `β > 0`, `ν > 0`, `|h| = 1`, `r ≤ 1`.  Then the inner
integral `I_G(q, g)` of `kf0Sector_iterated` is
`((√β)⁻¹)^{|G|(N-1)} · N_G · ∫ dγ_G(ψ) J_β(v) · goodWeight(chart((√β)⁻¹ v))
  · exp(-(bdry. linear + bdry. normal + bdry. constant + remainder)(v) + sources(v))`
at `v = C_G ψ`, `N_G = kwGaussNorm`.  The hemisphere event is implied by `goodWeight ≠ 0`
(`inner_pos_of_goodWeight_ne_zero`), so no indicator of the hemisphere is needed. -/
theorem lintegral_goodInner_gaussian {m : ℕ} [NeZero m] (s : ℕ) (r : ℝ) (B : Finset (Torus d m))
    (hD : D = siteUnion (ℓ := ℓ) s m B) {β ν : ℝ} (hβ : 0 < β) (hν : 0 < ν) (hh : ‖h‖ = 1) (hr : r ≤ 1)
    (g : Torus d ℓ → Fin N → ℝ) (q : ↥D → SpinSphere N) :
    ∫⁻ p, ENNReal.ofReal (Real.exp (-(β * goodEnergy ν h D
          (glue D q p))
        + sourceOut D g p) *
        goodWeight D h s m r B p) ∂sigmaOut D =
      ENNReal.ofReal (((Real.sqrt β)⁻¹) ^
          (Fintype.card (Good D) * (N - 1))) *
        ENNReal.ofReal (kwGaussNorm d ℓ N ν D) *
        ∫⁻ ψ, ENNReal.ofReal (chartJac β (fun x =>
              ((matAct (kwSqrt ν D) ψ x : perp h) :
                EuclideanSpace ℝ (Fin N)))) *
            ENNReal.ofReal (goodWeight D h s m r B
              (chartCfgOn h hh ((Real.sqrt β)⁻¹ •
                matAct (kwSqrt ν D) ψ))) *
            ENNReal.ofReal (Real.exp (goodChartExponent D β ν g h q
              (matAct (kwSqrt ν D) ψ)))
          ∂(goodGaussian D h) := by
  set f : (Good D → SpinSphere N) → ENNReal := fun p => ENNReal.ofReal
    (Real.exp (-(β * goodEnergy ν h D (glue D q p)) + sourceOut D g p) *
      goodWeight D h s m r B p) with hf
  have hfm : Measurable f := by
    refine ENNReal.measurable_ofReal.comp ?_
    refine (Real.measurable_exp.comp ?_).mul (measurable_goodWeight D s r B)
    simp_rw [goodEnergy_glue]
    exact (measurable_const.mul (((continuous_energy ν h).measurable.comp
      (measurable_glue_right D q)).sub measurable_const)).neg.add (measurable_sourceOut D g)
  have hsupp : ∀ p : Good D → SpinSphere N,
      (∃ x, ¬ 0 < inner ℝ h (p x : EuclideanSpace ℝ (Fin N))) → f p = 0 := by
    rintro p ⟨x, hx⟩
    have : goodWeight D h s m r B p = 0 := by
      by_contra hne
      exact hx (inner_pos_of_goodWeight_ne_zero D s hr hh B hD p hne x)
    simp only [hf, this, mul_zero, ENNReal.ofReal_zero]
  rw [lintegral_sphere_pi_chart hβ hh f hfm hsupp, mul_assoc]
  congr 1
  have hG := lintegral_good_gaussian_change D hh hν (F := fun v =>
    ENNReal.ofReal (chartJac β (fun x => ((v x : perp h) : EuclideanSpace ℝ (Fin N)))) *
      ENNReal.ofReal (goodWeight D h s m r B (chartCfgOn h hh ((Real.sqrt β)⁻¹ • v))) *
      ENNReal.ofReal (Real.exp (goodChartExponent D β ν g h q v)))
  refine Eq.trans ?_ hG
  refine lintegral_congr fun v => ?_
  by_cases hb : ∀ x, ‖v x‖ ^ 2 < β
  · simp only [hf]
    rw [goodEnergy_chart D hβ hh q v hb, sourceOut_chart D hβ hh g v hb]
    have hexp : -((1 / 2) * goodQuad D ν v + goodBdryLin D β q v + goodBdryNormal D β q v
          + goodBdryConst D h β q + goodRemainder D β ν v) +
        (goodSourceConst D g h + (Real.sqrt β)⁻¹ * goodSourceTangent D g v
          + (Real.sqrt β)⁻¹ * goodSourceNormal D g β v) =
        goodChartExponent D β ν g h q v + -(1 / 2) * goodQuad D ν v := by
      unfold goodChartExponent; ring
    rw [hexp, Real.exp_add, ENNReal.ofReal_mul (mul_nonneg (Real.exp_pos _).le
      (Real.exp_pos _).le), ENNReal.ofReal_mul (Real.exp_pos _).le]
    ring
  · obtain ⟨x₀, hx₀⟩ := not_forall.1 hb
    have hle : Real.sqrt β ≤ ‖v x₀‖ :=
      calc Real.sqrt β ≤ Real.sqrt (‖v x₀‖ ^ 2) := Real.sqrt_le_sqrt (not_lt.1 hx₀)
        _ = ‖v x₀‖ := Real.sqrt_sq (norm_nonneg _)
    have h0 : chartJac β (fun x => ((v x : perp h) : EuclideanSpace ℝ (Fin N))) = 0 :=
      chartJac_eq_zero (x₀ := x₀) (not_lt.2 hle)
    simp [h0]

/-! ### T4: an instance -/

/-- The bad set of the instance: the sites of the block `0` for `d = 3`, torus side `ℓ = 4`,
blocks of side `2` (the smallest setting of `kf0_nonvacuity_instance`). -/
noncomputable def goodChartInstD : Finset (Torus 3 4) :=
  siteUnion (ℓ := 4) 2 2 ({0} : Finset (Torus 3 2))

/-- The product of the open upper hemispheres around `e₀` on the good sites of the instance. -/
def goodChartInstU : Set (Good goodChartInstD → SpinSphere 3) :=
  {φ | ∀ x, 0 < inner ℝ (EuclideanSpace.single (0 : Fin 3) (1 : ℝ))
    (φ x : EuclideanSpace ℝ (Fin 3))}

theorem isOpen_goodChartInstU : IsOpen goodChartInstU := by
  have : goodChartInstU = ⋂ x : Good goodChartInstD, {φ : Good goodChartInstD → SpinSphere 3 |
      0 < inner ℝ (EuclideanSpace.single (0 : Fin 3) (1 : ℝ)) (φ x : EuclideanSpace ℝ (Fin 3))} := by
    ext φ; simp [goodChartInstU]
  rw [this]
  refine isOpen_iInter_of_finite fun x => isOpen_lt continuous_const ?_
  exact continuous_const.inner (continuous_subtype_val.comp (continuous_apply x))

/-- **Non-vacuity** (T4): `d = 3`, `N = 3`, `ℓ = 4`, blocks of side `2`, bad set the sites of the
block `0`, `β = 1`, `h = e₀`.  The chart measure formula (T1) holds for the indicator of the product
of the upper hemispheres on the good sites, and the left side is positive. -/
theorem goodChart_instance :
    (∫⁻ φ, goodChartInstU.indicator 1 φ
        ∂(Measure.pi fun _ : Good goodChartInstD =>
          (volume : Measure (EuclideanSpace ℝ (Fin 3))).toSphere) =
      ENNReal.ofReal (((Real.sqrt 1)⁻¹) ^ (Fintype.card (Good goodChartInstD) * (3 - 1))) *
        ∫⁻ v : Good goodChartInstD → perp (EuclideanSpace.single (0 : Fin 3) (1 : ℝ)),
          ENNReal.ofReal (chartJac 1 (fun x => (v x : EuclideanSpace ℝ (Fin 3)))) *
            goodChartInstU.indicator 1
              (chartCfgOn (EuclideanSpace.single (0 : Fin 3) (1 : ℝ)) (by simp)
                ((Real.sqrt 1)⁻¹ • v))
          ∂(Measure.pi fun _ => (volume : Measure (perp
            (EuclideanSpace.single (0 : Fin 3) (1 : ℝ)))))) ∧
    0 < ∫⁻ φ, goodChartInstU.indicator 1 φ
        ∂(Measure.pi fun _ : Good goodChartInstD =>
          (volume : Measure (EuclideanSpace ℝ (Fin 3))).toSphere) := by
  have hh : ‖(EuclideanSpace.single (0 : Fin 3) (1 : ℝ))‖ = 1 := by simp
  have hm : MeasurableSet goodChartInstU := isOpen_goodChartInstU.measurableSet
  refine ⟨?_, ?_⟩
  · refine lintegral_sphere_pi_chart one_pos hh _ (measurable_one.indicator hm) ?_
    intro φ ⟨x, hx⟩
    exact Set.indicator_of_notMem (fun (hφ : φ ∈ goodChartInstU) => hx (hφ x)) _
  · rw [lintegral_indicator_one hm]
    have : (Measure.pi fun _ : Good goodChartInstD =>
        (volume : Measure (EuclideanSpace ℝ (Fin 3))).toSphere).IsOpenPosMeasure :=
      Measure.pi.isOpenPosMeasure _
    refine isOpen_goodChartInstU.measure_pos _ ⟨fun _ => ⟨EuclideanSpace.single 0 1, by simp⟩, ?_⟩
    intro x
    simp

end Terms

end Balaban.LargeField
