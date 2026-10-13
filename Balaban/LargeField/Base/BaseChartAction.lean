/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Frozen.Model.PartitionFunction
public import Balaban.Lattice.Laplacian
public import Balaban.LargeField.Base.ChartIntegral

/-!
# The action of the hard-spin model in the hemisphere chart on the full torus (BASE.md, B2)

This is the exact chart form of the action on the event that all spins lie in the open hemisphere
around the unit vector `h`; no estimate of the complementary event, no expansion and no statement
about Root-F are proved here.  Source: `notes/phase1/LF-BASE-KF0.md` §A.1 (A.1)–(A.3).

## Conventions of the frozen model (T7 (a))

* `Balaban.energy d N ℓ ν h φ = ½ ∑_x ∑_{μ : Fin d} ‖φ(x + e_μ) - φ(x)‖² + (ν/2) ∑_x ‖φ(x) - h‖²`;
  the bond sum runs over the forward bonds `(x, x + e_μ)` only (each bond once when `ℓ ≥ 3`), with
  the factor `½`, and the mass term is `(ν/2) ‖φ - h‖²` (not `ν ‖φ - h‖²`).  The matrix
  `latticeLaplacian d ℓ ν` has quadratic form `∑_x ∑_μ (u(x+e_μ) - u(x))² + ν ∑_x u(x)²`, twice the
  quadratic part of the energy of a scalar field.
* The source pairing of `Balaban.partitionFunction` is `⟨g, φ⟩ = ∑_x ∑_i g x i * φ x i` with a
  complex `g` (no factor, no normalisation).

## Inventory of (A.1) (T1)

Landed and used here:
* bijection of the chart onto the open hemisphere: `SphereChart.hemiPt_injOn` (injective on the open
  unit ball of `h^⊥`), `SphereChart.hemiPt_image` (image = `{φ | 0 < ⟨h, φ⟩}`), with inverse the
  orthogonal projection `SphereChart.perpK_hemiE`, `SphereChart.hemiE_perpK`;
  `SphereChart.coe_hemiPt_of_lt` (value `√(1-|ξ|²) h + ξ`), `SphereChart.inner_hemiPt_pos`;
* measurability: `SphereChart.continuous_hemiPt`, `SphereChart.measurableSet_hemiSet`,
  `LargeField.measurable_chartMapPi`;
* the measure identity with density `(1 - |ξ|²)^{-1/2}` and normalisation exactly that of Mathlib's
  `Measure.toSphere` of Lebesgue measure (no extra constant):
  `LargeField.toSphere_eq_graph` (= `SphereChart.toSphere_hemisphere_apply`),
  `SphereChart.toSphere_restrict_hemisphere`, `SphereChart.integral_hemisphere`,
  `SphereChart.lintegral_hemisphere`, and, for the product over the sites,
  `LargeField.lintegral_sphere_pi_hemisphere` (`HemispherePi.lean`);
* the rescaled-Jacobian form `chartJac` and `chartWeight_inv_sqrt_smul` (`ChartIntegral.lean`).
Nothing of (A.1) is missing for the full torus.  What is new in this file: the energy and source
identities in chart variables (`energy_chartCfg`, `source_chartCfg`), the remainder bounds, and the
partition-function integrand restricted to the event (`BaseChartMeasure.lean`).

## What is NOT proved here (T7 (d))

Not proved: the complement of the event `E_h` (spins in the closed lower hemisphere, large-field
spins); the conditional problem with holes and the crossing-bond term (`LF-BASE-KF0.md` (B.1));
the Gaussian change of variables `v = K_ν^{-1/2} ψ`; the expansion of `exp(-R_β(v))` and of the
Jacobian, and the `KF0OneScaleInput` theorem of BASE.md built on them.
-/

@[expose] public section

open MeasureTheory

namespace Balaban.LargeField

open SphereChart Matrix

noncomputable section

variable {d N ℓ : ℕ}

/-! ### Elementary inequalities for the normal coordinate -/

theorem sqrt_mul_div {β : ℝ} (hβ : 0 < β) (a : ℝ) : Real.sqrt β * (a / β) = a / Real.sqrt β := by
  have hs : 0 < Real.sqrt β := Real.sqrt_pos.2 hβ
  rw [eq_div_iff hs.ne']
  calc Real.sqrt β * (a / β) * Real.sqrt β = (Real.sqrt β * Real.sqrt β) * (a / β) := by ring
    _ = a := by rw [Real.mul_self_sqrt hβ.le]; field_simp

/-- `1 - √(1 - s) ≤ s` for `s ∈ [0,1]`. -/
theorem one_sub_sqrt_le {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) : 1 - Real.sqrt (1 - s) ≤ s := by
  have h1 : Real.sqrt (1 - s) ^ 2 = 1 - s := Real.sq_sqrt (by linarith)
  have h2 : 0 ≤ Real.sqrt (1 - s) := Real.sqrt_nonneg _
  have h3 : Real.sqrt (1 - s) ≤ 1 := Real.sqrt_le_one.2 (by linarith)
  nlinarith

/-- Lipschitz bound of `s ↦ √(1 - s)` on `[0, 1/2]` (constant `1`). -/
theorem abs_sqrt_sub_le {a b : ℝ} (ha1 : a ≤ 1 / 2) (hb1 : b ≤ 1 / 2) :
    |Real.sqrt (1 - a) - Real.sqrt (1 - b)| ≤ |a - b| := by
  have hp2 : Real.sqrt (1 - a) ^ 2 = 1 - a := Real.sq_sqrt (by linarith)
  have hq2 : Real.sqrt (1 - b) ^ 2 = 1 - b := Real.sq_sqrt (by linarith)
  have hp0 := Real.sqrt_nonneg (1 - a)
  have hq0 := Real.sqrt_nonneg (1 - b)
  have hp : 1 / 2 ≤ Real.sqrt (1 - a) := by nlinarith
  have hq : 1 / 2 ≤ Real.sqrt (1 - b) := by nlinarith
  have hprod : (Real.sqrt (1 - a) - Real.sqrt (1 - b)) * (Real.sqrt (1 - a) + Real.sqrt (1 - b))
      = b - a := by nlinarith
  have habs : |Real.sqrt (1 - a) - Real.sqrt (1 - b)| *
      (Real.sqrt (1 - a) + Real.sqrt (1 - b)) = |a - b| := by
    rw [← abs_of_nonneg (show 0 ≤ Real.sqrt (1 - a) + Real.sqrt (1 - b) by linarith), ← abs_mul,
      hprod, abs_sub_comm]
  nlinarith [abs_nonneg (Real.sqrt (1 - a) - Real.sqrt (1 - b))]

/-- The normal coordinate as a function of the tangent norm: `√β (√(1 - t²/β) - 1)`. -/
def normalCoord (β t : ℝ) : ℝ := Real.sqrt β * (Real.sqrt (1 - t ^ 2 / β) - 1)

theorem normalCoord_nonpos {β : ℝ} (hβ : 0 < β) (t : ℝ) : normalCoord β t ≤ 0 := by
  unfold normalCoord
  have : Real.sqrt (1 - t ^ 2 / β) ≤ 1 :=
    Real.sqrt_le_one.2 (by have : 0 ≤ t ^ 2 / β := by positivity
                           linarith)
  exact mul_nonpos_of_nonneg_of_nonpos (Real.sqrt_nonneg _) (by linarith)

theorem abs_normalCoord_le {β t : ℝ} (hβ : 0 < β) (ht : t ^ 2 ≤ β) :
    |normalCoord β t| ≤ t ^ 2 / Real.sqrt β := by
  have hs : 0 < Real.sqrt β := Real.sqrt_pos.2 hβ
  have hsq : Real.sqrt β ^ 2 = β := Real.sq_sqrt hβ.le
  rw [abs_of_nonpos (normalCoord_nonpos hβ t)]
  unfold normalCoord
  have h1 := one_sub_sqrt_le (s := t ^ 2 / β) (by positivity) ((div_le_one hβ).2 ht)
  calc -(Real.sqrt β * (Real.sqrt (1 - t ^ 2 / β) - 1))
      = Real.sqrt β * (1 - Real.sqrt (1 - t ^ 2 / β)) := by ring
    _ ≤ Real.sqrt β * (t ^ 2 / β) := mul_le_mul_of_nonneg_left h1 hs.le
    _ = t ^ 2 / Real.sqrt β := sqrt_mul_div hβ _

theorem abs_normalCoord_sub_le {β s t : ℝ} (hβ : 0 < β) (hs0 : 0 ≤ s) (ht0 : 0 ≤ t)
    (hs : s ^ 2 ≤ β / 2) (ht : t ^ 2 ≤ β / 2) :
    |normalCoord β s - normalCoord β t| ≤ (s + t) * |s - t| / Real.sqrt β := by
  have hb : 0 < Real.sqrt β := Real.sqrt_pos.2 hβ
  have hsq : Real.sqrt β ^ 2 = β := Real.sq_sqrt hβ.le
  have key := abs_sqrt_sub_le (a := s ^ 2 / β) (b := t ^ 2 / β)
    (by rw [div_le_iff₀ hβ]; linarith) (by rw [div_le_iff₀ hβ]; linarith)
  have hd : normalCoord β s - normalCoord β t =
      Real.sqrt β * (Real.sqrt (1 - s ^ 2 / β) - Real.sqrt (1 - t ^ 2 / β)) := by
    unfold normalCoord; ring
  rw [hd, abs_mul, abs_of_pos hb]
  have h2 : |s ^ 2 / β - t ^ 2 / β| = (s + t) * |s - t| / β := by
    rw [← sub_div, abs_div, abs_of_pos hβ, show s ^ 2 - t ^ 2 = (s + t) * (s - t) by ring, abs_mul,
      abs_of_nonneg (by linarith : 0 ≤ s + t)]
  rw [h2] at key
  calc Real.sqrt β * |Real.sqrt (1 - s ^ 2 / β) - Real.sqrt (1 - t ^ 2 / β)|
      ≤ Real.sqrt β * ((s + t) * |s - t| / β) := mul_le_mul_of_nonneg_left key hb.le
    _ = (s + t) * |s - t| / Real.sqrt β := sqrt_mul_div hβ _

/-! ### The chart configuration and the normal coordinate -/

section Chart

variable (h : EuclideanSpace ℝ (Fin N)) (hh : ‖h‖ = 1)

/-- The configuration with chart coordinates `ξ`: `x ↦ hemiPt h _ (ξ x)`.  For `‖ξ x‖ < 1` its value
is `√(1 - ‖ξ x‖²) h + ξ x`. -/
def chartCfg (ξ : Torus d ℓ → perp h) : Torus d ℓ → Metric.sphere (0 : EuclideanSpace ℝ (Fin N)) 1 :=
  fun x => hemiPt h hh (ξ x)

variable {h}

/-- The normal coordinate `w_x = √β (√(1 - ‖v_x‖²/β) - 1)` of the chart configuration with
`ξ = β^{-1/2} v` (so `√β φ_x = √β h + w_x h + v_x`). -/
def wN (β : ℝ) (v : Torus d ℓ → perp h) (x : Torus d ℓ) : ℝ := normalCoord β ‖v x‖

theorem wN_nonpos {β : ℝ} (hβ : 0 < β) (v : Torus d ℓ → perp h) (x : Torus d ℓ) :
    wN β v x ≤ 0 := normalCoord_nonpos hβ _

theorem abs_wN_le {β : ℝ} (hβ : 0 < β) (v : Torus d ℓ → perp h) (x : Torus d ℓ)
    (hx : ‖v x‖ ^ 2 ≤ β) : |wN β v x| ≤ ‖v x‖ ^ 2 / Real.sqrt β :=
  abs_normalCoord_le hβ hx

theorem abs_wN_sub_le {β : ℝ} (hβ : 0 < β) (v : Torus d ℓ → perp h) (x y : Torus d ℓ)
    (hx : ‖v x‖ ^ 2 ≤ β / 2) (hy : ‖v y‖ ^ 2 ≤ β / 2) :
    |wN β v x - wN β v y| ≤ (‖v x‖ + ‖v y‖) * ‖v x - v y‖ / Real.sqrt β := by
  have h1 := abs_normalCoord_sub_le hβ (norm_nonneg (v x)) (norm_nonneg (v y)) hx hy
  have h2 : |‖v x‖ - ‖v y‖| ≤ ‖v x - v y‖ := abs_norm_sub_norm_le _ _
  have hb : 0 < Real.sqrt β := Real.sqrt_pos.2 hβ
  refine h1.trans ?_
  gcongr

/-- The quadratic part of the energy in the tangent variable:
`½ ∑_x ∑_μ ‖v(x+e_μ) - v(x)‖² + (ν/2) ∑_x ‖v(x)‖²`. -/
def tangentEnergy [NeZero ℓ] (ν : ℝ) (v : Torus d ℓ → perp h) : ℝ :=
  (1 / 2) * ∑ x : Torus d ℓ, ∑ μ : Fin d, ‖v (x + Pi.single μ 1) - v x‖ ^ 2
    + (ν / 2) * ∑ x : Torus d ℓ, ‖v x‖ ^ 2

/-- The remainder `R_β(v) = ½ ∑ (w_{x+e_μ} - w_x)² + (ν/2) ∑ w_x²`. -/
def chartRemainder [NeZero ℓ] (β ν : ℝ) (v : Torus d ℓ → perp h) : ℝ :=
  (1 / 2) * ∑ x : Torus d ℓ, ∑ μ : Fin d, (wN β v (x + Pi.single μ 1) - wN β v x) ^ 2
    + (ν / 2) * ∑ x : Torus d ℓ, wN β v x ^ 2

/-- `⟨v, K_ν v⟩ = ∑_i v_iᵀ (-Δ + ν) v_i`, with `v_i x = i`-th coordinate of `v x`
(the landed `latticeLaplacian` applied to each coordinate). -/
def tangentQuad [NeZero ℓ] (ν : ℝ) (v : Torus d ℓ → perp h) : ℝ :=
  ∑ i : Fin N, (fun x => ((v x : EuclideanSpace ℝ (Fin N)) i)) ⬝ᵥ
    latticeLaplacian d ℓ ν *ᵥ (fun x => ((v x : EuclideanSpace ℝ (Fin N)) i))

theorem tangentQuad_eq [NeZero ℓ] (ν : ℝ) (v : Torus d ℓ → perp h) :
    tangentQuad ν v =
      ∑ x : Torus d ℓ, ∑ μ : Fin d, ‖v (x + Pi.single μ 1) - v x‖ ^ 2
        + ν * ∑ x : Torus d ℓ, ‖v x‖ ^ 2 := by
  have hn : ∀ u : perp h, ‖u‖ ^ 2 = ∑ i : Fin N, ((u : EuclideanSpace ℝ (Fin N)) i) ^ 2 := by
    intro u
    rw [← norm_coe_perp, EuclideanSpace.norm_sq_eq]
    simp
  simp only [tangentQuad, latticeLaplacian_quadratic]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  congr 1
  · rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun μ _ => ?_
    rw [hn]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp
  · congr 1
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [hn]

theorem tangentEnergy_eq [NeZero ℓ] (ν : ℝ) (v : Torus d ℓ → perp h) :
    tangentEnergy ν v = (1 / 2) * tangentQuad ν v := by
  rw [tangentQuad_eq, tangentEnergy]; ring

theorem tangentEnergy_nonneg [NeZero ℓ] {ν : ℝ} (hν : 0 ≤ ν) (v : Torus d ℓ → perp h) :
    0 ≤ tangentEnergy ν v := by
  unfold tangentEnergy
  have : 0 ≤ ∑ x : Torus d ℓ, ∑ μ : Fin d, ‖v (x + Pi.single μ 1) - v x‖ ^ 2 :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity
  have : 0 ≤ ∑ x : Torus d ℓ, ‖v x‖ ^ 2 := Finset.sum_nonneg fun _ _ => by positivity
  positivity

theorem chartRemainder_nonneg [NeZero ℓ] {ν : ℝ} (hν : 0 ≤ ν) (β : ℝ) (v : Torus d ℓ → perp h) :
    0 ≤ chartRemainder β ν v := by
  unfold chartRemainder
  have : 0 ≤ ∑ x : Torus d ℓ, ∑ μ : Fin d, (wN β v (x + Pi.single μ 1) - wN β v x) ^ 2 :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity
  have : 0 ≤ ∑ x : Torus d ℓ, wN β v x ^ 2 := Finset.sum_nonneg fun _ _ => by positivity
  positivity

/-! ### The energy identity -/

/-- Norm of `a h + u` with `u ⊥ h`, `|h| = 1`. -/
theorem norm_sq_smul_add_perp (hh : ‖h‖ = 1) (a : ℝ) (u : perp h) :
    ‖a • h + (u : EuclideanSpace ℝ (Fin N))‖ ^ 2 = a ^ 2 + ‖u‖ ^ 2 := by
  rw [norm_add_sq_real, real_inner_smul_left, inner_eq_of_mem_perp h u.2, norm_smul, hh,
    norm_coe_perp]
  simp

theorem lt_sqrt_of_sq_lt {β t : ℝ} (ht : 0 ≤ t) (h : t ^ 2 < β) : t < Real.sqrt β :=
  (Real.lt_sqrt ht).2 h

/-- The coordinates of the chart configuration of `ξ = β^{-1/2} v`:
`φ_x = h + β^{-1/2} (v_x + w_x h)`. -/
theorem coe_chartCfg_scaled {β : ℝ} (hβ : 0 < β) (hh : ‖h‖ = 1) (v : Torus d ℓ → perp h)
    (hv : ∀ x, ‖v x‖ ^ 2 < β) (x : Torus d ℓ) :
    ((chartCfg h hh ((Real.sqrt β)⁻¹ • v) x : Metric.sphere (0 : EuclideanSpace ℝ (Fin N)) 1) :
        EuclideanSpace ℝ (Fin N)) =
      h + (Real.sqrt β)⁻¹ • ((v x : EuclideanSpace ℝ (Fin N)) + wN β v x • h) := by
  have hlt : ‖((Real.sqrt β)⁻¹ • v) x‖ < 1 := by
    rw [Pi.smul_apply]
    exact (norm_inv_sqrt_smul_lt_one_iff hβ (v x)).2 (lt_sqrt_of_sq_lt (norm_nonneg _) (hv x))
  unfold chartCfg
  rw [coe_hemiPt_of_lt h hh hlt, Pi.smul_apply, chartPoint_eq β hβ h (v x)]
  rfl

/-- **The energy identity in chart variables** (LF-BASE-KF0 (A.2)).  For `β > 0`, `|h| = 1` and
`‖v x‖² < β` for all `x`, with `φ` the chart configuration of `ξ = β^{-1/2} v`:
`β H₀(φ) = ½ ⟨v, K_ν v⟩ + R_β(v)`, where `R_β(v)` is the exact remainder made of the normal
coordinates. -/
theorem energy_chartCfg [NeZero ℓ] {β : ℝ} (hβ : 0 < β) (hh : ‖h‖ = 1) (ν : ℝ)
    (v : Torus d ℓ → perp h) (hv : ∀ x, ‖v x‖ ^ 2 < β) :
    β * energy d N ℓ ν h (chartCfg h hh ((Real.sqrt β)⁻¹ • v)) =
      (1 / 2) * tangentQuad ν v + chartRemainder β ν v := by
  set s := (Real.sqrt β)⁻¹ with hs
  have hs2 : s ^ 2 = β⁻¹ := by
    rw [hs, inv_pow, Real.sq_sqrt hβ.le]
  have hbond : ∀ x y : Torus d ℓ,
      ‖((chartCfg h hh (s • v) y : Metric.sphere (0 : EuclideanSpace ℝ (Fin N)) 1) :
          EuclideanSpace ℝ (Fin N)) - chartCfg h hh (s • v) x‖ ^ 2 =
        β⁻¹ * (‖v y - v x‖ ^ 2 + (wN β v y - wN β v x) ^ 2) := by
    intro x y
    rw [coe_chartCfg_scaled hβ hh v hv, coe_chartCfg_scaled hβ hh v hv]
    have : h + s • ((v y : EuclideanSpace ℝ (Fin N)) + wN β v y • h) -
        (h + s • ((v x : EuclideanSpace ℝ (Fin N)) + wN β v x • h)) =
        s • ((wN β v y - wN β v x) • h + ((v y - v x : perp h) : EuclideanSpace ℝ (Fin N))) := by
      rw [Submodule.coe_sub]; module
    rw [this, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, hs2, norm_sq_smul_add_perp hh]
    ring
  have hmass : ∀ x : Torus d ℓ,
      ‖((chartCfg h hh (s • v) x : Metric.sphere (0 : EuclideanSpace ℝ (Fin N)) 1) :
          EuclideanSpace ℝ (Fin N)) - h‖ ^ 2 = β⁻¹ * (‖v x‖ ^ 2 + wN β v x ^ 2) := by
    intro x
    rw [coe_chartCfg_scaled hβ hh v hv]
    have : h + s • ((v x : EuclideanSpace ℝ (Fin N)) + wN β v x • h) - h =
        s • (wN β v x • h + (v x : EuclideanSpace ℝ (Fin N))) := by module
    rw [this, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, hs2, norm_sq_smul_add_perp hh]
    ring
  unfold energy
  simp only [hbond, hmass]
  rw [tangentQuad_eq]
  unfold chartRemainder
  simp only [mul_add, Finset.sum_add_distrib, ← Finset.mul_sum]
  field_simp
  ring

/-! ### The remainder bound -/

/-- **Remainder bound.**  If `ν ≥ 0` and `‖v x‖² ≤ m β` for all `x`, with `0 ≤ m ≤ 1/2`, then
`0 ≤ R_β(v) ≤ 4 m · (½ ⟨v, K_ν v⟩)`; i.e. the remainder is at most `4 sup_x (‖v x‖²/β)` times the
Gaussian energy `½ ⟨v, K_ν v⟩`. -/
theorem chartRemainder_le [NeZero ℓ] {β ν m : ℝ} (hβ : 0 < β) (hν : 0 ≤ ν) (hm0 : 0 ≤ m)
    (hm : m ≤ 1 / 2) (v : Torus d ℓ → perp h) (hv : ∀ x, ‖v x‖ ^ 2 ≤ m * β) :
    0 ≤ chartRemainder β ν v ∧ chartRemainder β ν v ≤ 4 * m * tangentEnergy ν v := by
  refine ⟨chartRemainder_nonneg hν β v, ?_⟩
  have hs : 0 < Real.sqrt β := Real.sqrt_pos.2 hβ
  have hsq : Real.sqrt β ^ 2 = β := Real.sq_sqrt hβ.le
  have hhalf : ∀ x, ‖v x‖ ^ 2 ≤ β / 2 := fun x => (hv x).trans (by nlinarith)
  have hbond : ∀ x : Torus d ℓ, ∀ μ : Fin d,
      (wN β v (x + Pi.single μ 1) - wN β v x) ^ 2 ≤ 4 * m * ‖v (x + Pi.single μ 1) - v x‖ ^ 2 := by
    intro x μ
    set y := x + Pi.single μ 1
    have h1 := abs_wN_sub_le hβ v y x (hhalf y) (hhalf x)
    have h2 : (wN β v y - wN β v x) ^ 2 ≤
        ((‖v y‖ + ‖v x‖) * ‖v y - v x‖ / Real.sqrt β) ^ 2 := by
      rw [← sq_abs (wN β v y - wN β v x)]
      exact pow_le_pow_left₀ (abs_nonneg _) h1 2
    refine h2.trans ?_
    rw [div_pow, mul_pow, hsq, div_le_iff₀ hβ]
    have h3 : (‖v y‖ + ‖v x‖) ^ 2 ≤ 4 * (m * β) := by
      nlinarith [hv y, hv x, sq_nonneg (‖v y‖ - ‖v x‖)]
    have h4 : 0 ≤ ‖v y - v x‖ ^ 2 := by positivity
    nlinarith
  have hmass : ∀ x : Torus d ℓ, wN β v x ^ 2 ≤ m * ‖v x‖ ^ 2 := by
    intro x
    have h1 := abs_wN_le hβ v x ((hhalf x).trans (by linarith))
    have h2 : wN β v x ^ 2 ≤ (‖v x‖ ^ 2 / Real.sqrt β) ^ 2 := by
      rw [← sq_abs (wN β v x)]
      exact pow_le_pow_left₀ (abs_nonneg _) h1 2
    refine h2.trans ?_
    rw [div_pow, hsq, div_le_iff₀ hβ]
    have h3 : 0 ≤ ‖v x‖ ^ 2 := by positivity
    nlinarith [hv x]
  unfold chartRemainder tangentEnergy
  have hA : ∑ x : Torus d ℓ, ∑ μ : Fin d, (wN β v (x + Pi.single μ 1) - wN β v x) ^ 2 ≤
      ∑ x : Torus d ℓ, ∑ μ : Fin d, 4 * m * ‖v (x + Pi.single μ 1) - v x‖ ^ 2 :=
    Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun μ _ => hbond x μ
  have hB : ∑ x : Torus d ℓ, wN β v x ^ 2 ≤ ∑ x : Torus d ℓ, m * ‖v x‖ ^ 2 :=
    Finset.sum_le_sum fun x _ => hmass x
  simp only [← Finset.mul_sum, mul_assoc] at hA hB
  have hC : 0 ≤ ∑ x : Torus d ℓ, ‖v x‖ ^ 2 := Finset.sum_nonneg fun _ _ => by positivity
  nlinarith [mul_nonneg hν hm0, mul_nonneg (mul_nonneg hν hm0) hC]

/-! ### The source term -/

/-- The source pairing `⟨g, φ⟩ = ∑_x ∑_i g x i φ x i` for real `g` (the real case of the pairing in
`Balaban.partitionFunction`). -/
def sourcePair [NeZero ℓ] (g : Torus d ℓ → Fin N → ℝ)
    (φ : Torus d ℓ → Metric.sphere (0 : EuclideanSpace ℝ (Fin N)) 1) : ℝ :=
  ∑ x : Torus d ℓ, ∑ i : Fin N, g x i * ((φ x : EuclideanSpace ℝ (Fin N)) i)

/-- The pairing with the constant background: `⟨g, h⟩ = ∑_x ∑_i g x i h i`. -/
def sourceConst [NeZero ℓ] (g : Torus d ℓ → Fin N → ℝ) (h : EuclideanSpace ℝ (Fin N)) : ℝ :=
  ∑ x : Torus d ℓ, ∑ i : Fin N, g x i * h i

/-- The pairing with the tangent field: `⟨g, v⟩ = ∑_x ∑_i g x i v x i` (only the part of `g_x`
orthogonal to `h` contributes, since `v x ⊥ h`). -/
def sourceTangent [NeZero ℓ] (g : Torus d ℓ → Fin N → ℝ) (v : Torus d ℓ → perp h) : ℝ :=
  ∑ x : Torus d ℓ, ∑ i : Fin N, g x i * ((v x : EuclideanSpace ℝ (Fin N)) i)

/-- The normal part `∑_x (g_x · h) w_x`. -/
def sourceNormal [NeZero ℓ] (g : Torus d ℓ → Fin N → ℝ) (h : EuclideanSpace ℝ (Fin N)) (β : ℝ)
    (v : Torus d ℓ → perp h) : ℝ :=
  ∑ x : Torus d ℓ, (∑ i : Fin N, g x i * h i) * wN β v x

theorem coord_chartCfg_scaled {β : ℝ} (hβ : 0 < β) (hh : ‖h‖ = 1) (v : Torus d ℓ → perp h)
    (hv : ∀ x, ‖v x‖ ^ 2 < β) (x : Torus d ℓ) (i : Fin N) :
    ((chartCfg h hh ((Real.sqrt β)⁻¹ • v) x : Metric.sphere (0 : EuclideanSpace ℝ (Fin N)) 1) :
        EuclideanSpace ℝ (Fin N)) i =
      h i + (Real.sqrt β)⁻¹ * ((v x : EuclideanSpace ℝ (Fin N)) i + wN β v x * h i) := by
  rw [coe_chartCfg_scaled hβ hh v hv]
  simp
  ring

/-- **The source term in chart variables** (real source):
`⟨g, φ⟩ = ⟨g, h⟩ + β^{-1/2} ⟨g, v⟩ + β^{-1/2} ∑_x (g_x · h) w_x`. -/
theorem source_chartCfg [NeZero ℓ] {β : ℝ} (hβ : 0 < β) (hh : ‖h‖ = 1) (g : Torus d ℓ → Fin N → ℝ)
    (v : Torus d ℓ → perp h) (hv : ∀ x, ‖v x‖ ^ 2 < β) :
    sourcePair g (chartCfg h hh ((Real.sqrt β)⁻¹ • v)) =
      sourceConst g h + (Real.sqrt β)⁻¹ * sourceTangent g v +
        (Real.sqrt β)⁻¹ * sourceNormal g h β v := by
  unfold sourcePair sourceConst sourceTangent sourceNormal
  simp only [coord_chartCfg_scaled hβ hh v hv, Finset.mul_sum, Finset.sum_mul,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun i _ => ?_
  ring

/-- **The source term in chart variables**, in the form of the frozen pairing of
`Balaban.partitionFunction` (complex source `g`). -/
theorem source_chartCfg_complex [NeZero ℓ] {β : ℝ} (hβ : 0 < β) (hh : ‖h‖ = 1)
    (g : Torus d ℓ → Fin N → ℂ) (v : Torus d ℓ → perp h) (hv : ∀ x, ‖v x‖ ^ 2 < β) :
    ∑ x : Torus d ℓ, ∑ i : Fin N, g x i *
        (((chartCfg h hh ((Real.sqrt β)⁻¹ • v) x : EuclideanSpace ℝ (Fin N)) i : ℝ) : ℂ) =
      ∑ x : Torus d ℓ, ∑ i : Fin N, g x i * ((h i : ℝ) : ℂ)
        + (((Real.sqrt β)⁻¹ : ℝ) : ℂ) *
            ∑ x : Torus d ℓ, ∑ i : Fin N, g x i * (((v x : EuclideanSpace ℝ (Fin N)) i : ℝ) : ℂ)
        + (((Real.sqrt β)⁻¹ : ℝ) : ℂ) *
            ∑ x : Torus d ℓ, (∑ i : Fin N, g x i * ((h i : ℝ) : ℂ)) * ((wN β v x : ℝ) : ℂ) := by
  simp only [coord_chartCfg_scaled hβ hh v hv, Finset.mul_sum, Finset.sum_mul,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun i _ => ?_
  push_cast
  ring

/-! ### Non-vacuity -/

/-- The chart configuration of `v = 0` is the constant configuration `h`, with energy `0`. -/
theorem chartCfg_zero_coe [NeZero ℓ] (hh : ‖h‖ = 1) (x : Torus d ℓ) :
    ((chartCfg h hh (0 : Torus d ℓ → perp h) x : Metric.sphere (0 : EuclideanSpace ℝ (Fin N)) 1) :
        EuclideanSpace ℝ (Fin N)) = h := by
  unfold chartCfg
  rw [coe_hemiPt_of_lt h hh (by simp)]
  simp [hemiE]

theorem energy_chartCfg_zero [NeZero ℓ] (ν : ℝ) (hh : ‖h‖ = 1) :
    energy d N ℓ ν h (chartCfg h hh (0 : Torus d ℓ → perp h)) = 0 := by
  simp [energy, chartCfg_zero_coe hh]

/-- **Instance (`d = 3`, `ℓ = 3`, `N = 2`, `h = e₀`, `v ≡ 0`)**: `φ ≡ h`, and both sides of the
energy identity are `0`. -/
theorem energy_chartCfg_instance_zero (β ν : ℝ) :
    let h : EuclideanSpace ℝ (Fin 2) := EuclideanSpace.single 0 1
    ∃ hh : ‖h‖ = 1,
      energy 3 2 3 ν h (chartCfg h hh ((Real.sqrt β)⁻¹ • (0 : Torus 3 3 → perp h))) = 0 ∧
        tangentQuad ν (0 : Torus 3 3 → perp h) = 0 ∧
        chartRemainder β ν (0 : Torus 3 3 → perp h) = 0 := by
  intro h
  have hh : ‖h‖ = 1 := by simp [h]
  refine ⟨hh, ?_, ?_, ?_⟩
  · rw [smul_zero]; exact energy_chartCfg_zero ν hh
  · simp [tangentQuad]
  · simp [chartRemainder, wN, normalCoord]

/-- **Instance, non-zero `v`** (`d = 3`, `ℓ = 3`, `N = 2`, `h = e₀`): `v` supported at the site
`x₀`, `v x₀ = (√β/2) e₁`, so `‖v x₀‖² = β/4 < β`.  The energy identity holds at it (the
hypotheses of `energy_chartCfg` are met) and the normal coordinate there is `√β (√3/2 - 1)`. -/
theorem energy_chartCfg_instance_support (β ν : ℝ) (hβ : 0 < β) (x₀ : Torus 3 3) :
    let h : EuclideanSpace ℝ (Fin 2) := EuclideanSpace.single 0 1
    ∃ (hh : ‖h‖ = 1) (v : Torus 3 3 → perp h),
      (∀ x, ‖v x‖ ^ 2 < β) ∧ ‖v x₀‖ ^ 2 = β / 4 ∧
        wN β v x₀ = Real.sqrt β * (Real.sqrt 3 / 2 - 1) ∧
        (∀ x, x ≠ x₀ → wN β v x = 0) ∧
        β * energy 3 2 3 ν h (chartCfg h hh ((Real.sqrt β)⁻¹ • v)) =
          (1 / 2) * tangentQuad ν v + chartRemainder β ν v := by
  intro h
  have hh : ‖h‖ = 1 := by simp [h]
  set e₁ : EuclideanSpace ℝ (Fin 2) := EuclideanSpace.single 1 1 with he₁
  have hmem : (Real.sqrt β / 2) • e₁ ∈ perp h := by
    rw [Submodule.mem_orthogonal_singleton_iff_inner_right]
    simp [h, he₁, EuclideanSpace.inner_single_left]
  set u : perp h := ⟨(Real.sqrt β / 2) • e₁, hmem⟩ with hu
  have hun : ‖u‖ ^ 2 = β / 4 := by
    have : ‖u‖ = Real.sqrt β / 2 := by
      rw [← norm_coe_perp, hu]; simp [he₁, norm_smul, abs_of_nonneg (Real.sqrt_nonneg β)]
    rw [this, div_pow, Real.sq_sqrt hβ.le]; norm_num
  classical
  set v : Torus 3 3 → perp h := fun x => if x = x₀ then u else 0 with hvdef
  have hv : ∀ x, ‖v x‖ ^ 2 < β := by
    intro x
    by_cases hx : x = x₀
    · simp only [hvdef, hx, ↓reduceIte, hun]; linarith
    · simp only [hvdef, hx, ↓reduceIte, norm_zero]; simpa using hβ
  refine ⟨hh, v, hv, ?_, ?_, ?_, energy_chartCfg hβ hh ν v hv⟩
  · simp only [hvdef, ↓reduceIte]; exact hun
  · simp only [wN, normalCoord, hvdef, ↓reduceIte, hun]
    congr 1
    congr 1
    · have : 1 - β / 4 / β = (3 / 4 : ℝ) := by field_simp; norm_num
      rw [this, show (3 / 4 : ℝ) = (Real.sqrt 3 / 2) ^ 2 by rw [div_pow, Real.sq_sqrt (by norm_num)]; norm_num]
      exact Real.sqrt_sq (by positivity)
  · intro x hx
    simp [wN, normalCoord, hvdef, hx]

end Chart

end

end Balaban.LargeField
