/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Green.KF0DetWalks
public import Balaban.Green.KF0Reference
public import Balaban.LargeField.Base.BaseChartAction
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The boundary square of the good-region integral (packages H37-1 and H37-2)

For a set `D` of bad sites with good region `G = Dᶜ`, let `K_G = kwOp d m ν D` be the unit-lattice
operator on `G`.  This file proves, for a boundary source built from the crossing bonds:

* the abstract Schur bound `J ⬝ K⁻¹ J ≤ ∑ J_x² / (c_x + ν)` when `K ≥ diag c + ν` (`schur_bound`);
* its consequence `J ⬝ K_G⁻¹ J ≤ θ S`, `θ = 2d/(2d+ν)` (`boundary_schur`), with `θ < 1` and
  `θ` bounded by the value at the gap `kf0Gap L` (`kwQ_le_gap`);
* the completed square (`completed_square`, `kwOp_boundary_square`);
* the normal-term facts: `(h - q)·h = ‖h - q‖²/2` (`inner_sub_self_unit`), the sign and size of the
  normal coordinate (`normal_term_bounds`), the cost of the normal boundary term on the good
  region (`normal_cost`), the combined exponent bound under the threshold inequality
  (`exp_combined_le`) and the existence of the threshold (`exists_threshold`);
* a numerical instance for `d = m = 3`, `ν = 1/8`, `D = {0}` (`boundary_schur_instance`).

These are estimates for a FIXED bad set only.  The linked expansion, the integrated collar potential
and the one-scale theorem are NOT proved here.
-/

@[expose] public section

set_option linter.unusedSectionVars false

open Matrix Finset Balaban Balaban.KW Filter

namespace Balaban.LargeField

section Abstract

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Core of the Schur bound: if `K u = J` and `∑ (c_x + ν) u_x² ≤ u ⬝ K u`, then
`J ⬝ u ≤ ∑ J_x²/(c_x+ν)`. -/
theorem schur_core {K : Matrix ι ι ℝ} {c : ι → ℝ} {ν : ℝ} (hc : ∀ x, 0 ≤ c x) (hν : 0 < ν)
    {u J : ι → ℝ} (hKu : K *ᵥ u = J) (hform : ∑ x, (c x + ν) * u x ^ 2 ≤ u ⬝ᵥ K *ᵥ u) :
    J ⬝ᵥ u ≤ ∑ x, J x ^ 2 / (c x + ν) := by
  have hQ : u ⬝ᵥ K *ᵥ u = J ⬝ᵥ u := by rw [hKu, dotProduct_comm]
  have pt : ∀ x, 2 * (J x * u x) - (c x + ν) * u x ^ 2 ≤ J x ^ 2 / (c x + ν) := by
    intro x
    have hw : 0 < c x + ν := by linarith [hc x]
    have e : J x ^ 2 / (c x + ν) = 2 * (J x * u x) - (c x + ν) * u x ^ 2
        + (J x - (c x + ν) * u x) ^ 2 / (c x + ν) := by
      field_simp
      ring
    rw [e]
    have : 0 ≤ (J x - (c x + ν) * u x) ^ 2 / (c x + ν) := by positivity
    linarith
  have hs := Finset.sum_le_sum (fun x (_ : x ∈ Finset.univ) => pt x)
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum] at hs
  have hJ : J ⬝ᵥ u = ∑ x, J x * u x := rfl
  rw [hQ, hJ] at hform
  linarith

/-- **Schur bound (H37.1, abstract form).**  If `K` is invertible and `K ≥ diag(c) + ν` as forms,
`c ≥ 0`, `ν > 0`, then `J ⬝ K⁻¹ J ≤ ∑ J_x²/(c_x + ν)`. -/
theorem schur_bound {K : Matrix ι ι ℝ} {c : ι → ℝ} {ν : ℝ} (hc : ∀ x, 0 ≤ c x) (hν : 0 < ν)
    (hK : IsUnit K.det) (hform : ∀ u : ι → ℝ, ∑ x, (c x + ν) * u x ^ 2 ≤ u ⬝ᵥ K *ᵥ u)
    (J : ι → ℝ) : J ⬝ᵥ K⁻¹ *ᵥ J ≤ ∑ x, J x ^ 2 / (c x + ν) := by
  refine schur_core hc hν ?_ (hform _)
  rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hK, Matrix.one_mulVec]

/-- **Completed square (abstract).**  For `K` symmetric and invertible, `w = v + √β K⁻¹ J`:
`½ v⬝Kv + √β J⬝v + (β/2) S = ½ w⬝Kw + (β/2)(S - J⬝K⁻¹J)`. -/
theorem completed_square {K : Matrix ι ι ℝ} (hsymm : Kᵀ = K) (hK : IsUnit K.det)
    (v J : ι → ℝ) {β : ℝ} (hβ : 0 ≤ β) (S : ℝ) :
    1 / 2 * (v ⬝ᵥ K *ᵥ v) + Real.sqrt β * (J ⬝ᵥ v) + β / 2 * S =
      1 / 2 * ((v + Real.sqrt β • K⁻¹ *ᵥ J) ⬝ᵥ K *ᵥ (v + Real.sqrt β • K⁻¹ *ᵥ J))
        + β / 2 * (S - J ⬝ᵥ K⁻¹ *ᵥ J) := by
  set z := K⁻¹ *ᵥ J with hz
  have hKz : K *ᵥ z = J := by
    rw [hz, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hK, Matrix.one_mulVec]
  have h1 : z ⬝ᵥ K *ᵥ v = J ⬝ᵥ v := by
    rw [Matrix.dotProduct_mulVec]
    have : z ᵥ* K = J := by
      calc z ᵥ* K = z ᵥ* Kᵀ := by rw [hsymm]
        _ = K *ᵥ z := Matrix.vecMul_transpose K z
        _ = J := hKz
    rw [this]
  have h2 : v ⬝ᵥ K *ᵥ z = J ⬝ᵥ v := by rw [hKz, dotProduct_comm]
  have h3 : z ⬝ᵥ K *ᵥ z = J ⬝ᵥ z := by rw [hKz, dotProduct_comm]
  have hr : Real.sqrt β * Real.sqrt β = β := Real.mul_self_sqrt hβ
  simp only [Matrix.mulVec_add, Matrix.mulVec_smul, dotProduct_add, add_dotProduct,
    dotProduct_smul, smul_dotProduct, smul_eq_mul, h1, h2, h3]
  linear_combination (-(1 / 2) * (J ⬝ᵥ z)) * hr

end Abstract

/-! ### The region with holes -/

section Region

variable {d m : ℕ} [NeZero m]

/-- The boundary source `J(x) = ∑_{y ∈ D} A(x,y) a_{x,y}` at the good sites `x ∉ D`
(a sum over the crossing bonds at `x`, with the adjacency multiplicity); `J = 0` on `D`. -/
noncomputable def bdryJ (D : Finset (Torus d m)) (a : Torus d m → Torus d m → ℝ)
    (x : Torus d m) : ℝ :=
  if x ∈ D then 0 else ∑ y ∈ D, kwAdj d m x y * a x y

/-- The boundary sum of squares `S = ∑_{crossing e} a_e²` (with multiplicity). -/
noncomputable def bdryS (D : Finset (Torus d m)) (a : Torus d m → Torus d m → ℝ) : ℝ :=
  ∑ x, if x ∈ D then 0 else ∑ y ∈ D, kwAdj d m x y * a x y ^ 2

theorem bdryS_nonneg (D : Finset (Torus d m)) (a : Torus d m → Torus d m → ℝ) :
    0 ≤ bdryS D a := by
  unfold bdryS
  refine Finset.sum_nonneg fun x _ => ?_
  split_ifs
  · exact le_rfl
  · exact Finset.sum_nonneg fun y _ => mul_nonneg (kwAdj_nonneg x y) (sq_nonneg _)

theorem kwBdry_nonneg (D : Finset (Torus d m)) (x : Torus d m) : 0 ≤ kwBdry d m D x :=
  Finset.sum_nonneg fun y _ => kwAdj_nonneg x y

theorem kwBdry_le (D : Finset (Torus d m)) (x : Torus d m) : kwBdry d m D x ≤ 2 * d := by
  rw [← kwAdj_rowSum x]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    (fun y _ _ => kwAdj_nonneg x y)

/-- Cauchy–Schwarz at one site: `J_x² ≤ d_∂(x) ∑_e a_e²`. -/
theorem bdryJ_sq_le (D : Finset (Torus d m)) (a : Torus d m → Torus d m → ℝ) (x : Torus d m) :
    bdryJ D a x ^ 2 ≤ kwBdry d m D x * ∑ y ∈ D, kwAdj d m x y * a x y ^ 2 := by
  unfold bdryJ
  split_ifs with hx
  · simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
    exact mul_nonneg (kwBdry_nonneg D x)
      (Finset.sum_nonneg fun y _ => mul_nonneg (kwAdj_nonneg x y) (sq_nonneg _))
  · have := Finset.sum_mul_sq_le_sq_mul_sq D (fun y => Real.sqrt (kwAdj d m x y))
      (fun y => Real.sqrt (kwAdj d m x y) * a x y)
    have e1 : ∀ y, Real.sqrt (kwAdj d m x y) * (Real.sqrt (kwAdj d m x y) * a x y)
        = kwAdj d m x y * a x y := fun y => by
      rw [← mul_assoc, Real.mul_self_sqrt (kwAdj_nonneg x y)]
    have e2 : ∀ y, Real.sqrt (kwAdj d m x y) ^ 2 = kwAdj d m x y := fun y =>
      Real.sq_sqrt (kwAdj_nonneg x y)
    have e3 : ∀ y, (Real.sqrt (kwAdj d m x y) * a x y) ^ 2 = kwAdj d m x y * a x y ^ 2 :=
      fun y => by rw [mul_pow, e2]
    simp only [e1, e2, e3] at this
    exact this

/-- The Schur weight bound: `d_∂/(d_∂ + ν) ≤ 2d/(2d + ν)`. -/
theorem bdry_ratio_le {ν : ℝ} (hν : 0 < ν) (D : Finset (Torus d m)) (x : Torus d m) :
    kwBdry d m D x / (kwBdry d m D x + ν) ≤ kwQ d ν := by
  have hb := kwBdry_nonneg D x
  have hd := kwBdry_le D x
  unfold kwQ
  rw [div_le_div_iff₀ (by linarith) (by positivity)]
  nlinarith

/-- **Boundary Schur bound (H37.1 for the region with holes).**  For the boundary source `J` built
from numbers `a_{x,y}` on the crossing bonds,
`J ⬝ K_G⁻¹ J ≤ θ S`, `θ = 2d/(2d+ν)` (`kwQ d ν`), `S = ∑_e a_e²`; `K_G` is the padded `kwOp`. -/
theorem boundary_schur {ν : ℝ} (hν : 0 < ν) (D : Finset (Torus d m))
    (a : Torus d m → Torus d m → ℝ) :
    bdryJ D a ⬝ᵥ (kwOp d m ν D)⁻¹ *ᵥ bdryJ D a ≤ kwQ d ν * bdryS D a := by
  set J := bdryJ D a with hJ
  set u := (kwOp d m ν D)⁻¹ *ᵥ J with hu
  have hunit := kwOp_det_isUnit hν D
  have hKu : kwOp d m ν D *ᵥ u = J := by
    rw [hu, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hunit, Matrix.one_mulVec]
  have hzero : ∀ x ∈ D, u x = 0 := by
    intro x hx
    have h1 := congrFun hKu x
    have h2 : J x = 0 := by simp [hJ, bdryJ, hx]
    have h3 : (kwOp d m ν D *ᵥ u) x = (2 * d + ν) * u x := by
      simp only [Matrix.mulVec, dotProduct, kwOp_apply_of_mem_left ν hx]
      simp [ite_mul]
    rw [h3, h2] at h1
    have : 0 < (2 * (d : ℝ) + ν) := by positivity
    exact (mul_eq_zero.1 h1).resolve_left this.ne'
  have hcore := schur_core (K := kwOp d m ν D) (c := kwBdry d m D) (fun x => kwBdry_nonneg D x) hν
    hKu (kwOp_form_ge ν D hzero)
  refine hcore.trans ?_
  unfold bdryS
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun x _ => ?_
  by_cases hx : x ∈ D
  · have : J x = 0 := by simp [hJ, bdryJ, hx]
    simp [this, hx]
  · simp only [hx, ite_false]
    have hpos : 0 < kwBdry d m D x + ν := by linarith [kwBdry_nonneg D x]
    set s := ∑ y ∈ D, kwAdj d m x y * a x y ^ 2
    have hs : 0 ≤ s := Finset.sum_nonneg fun y _ => mul_nonneg (kwAdj_nonneg x y) (sq_nonneg _)
    calc J x ^ 2 / (kwBdry d m D x + ν)
        ≤ (kwBdry d m D x * s) / (kwBdry d m D x + ν) :=
          div_le_div_of_nonneg_right (bdryJ_sq_le D a x) hpos.le
      _ = (kwBdry d m D x / (kwBdry d m D x + ν)) * s := by rw [div_mul_eq_mul_div]
      _ ≤ kwQ d ν * s := mul_le_mul_of_nonneg_right (bdry_ratio_le hν D x) hs

/-- `θ = 2d/(2d+ν)` is below `1` and decreases in `ν`: for `ν ≥ ν_* > 0`, `θ(ν) ≤ θ(ν_*) < 1`. -/
theorem kwQ_le_gap {ν ν₀ : ℝ} (hν₀ : 0 < ν₀) (h : ν₀ ≤ ν) :
    kwQ d ν ≤ kwQ d ν₀ ∧ kwQ d ν₀ < 1 := by
  refine ⟨?_, kwQ_lt_one hν₀⟩
  have hν : 0 < ν := hν₀.trans_le h
  unfold kwQ
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  nlinarith

/-- The same at the reference gap `ν_* = kf0Gap L`, `L ≥ 1`. -/
theorem kwQ_le_kf0Gap {L : ℕ} (hL : 0 < L) {ν : ℝ} (h : Green.kf0Gap L ≤ ν) :
    kwQ d ν ≤ kwQ d (Green.kf0Gap L) ∧ kwQ d (Green.kf0Gap L) < 1 := by
  have : 0 < Green.kf0Gap L := by
    unfold Green.kf0Gap; positivity
  exact kwQ_le_gap this h

theorem kwOp_symm (ν : ℝ) (D : Finset (Torus d m)) : (kwOp d m ν D)ᵀ = kwOp d m ν D := by
  ext x y
  simp only [Matrix.transpose_apply, kwOp_apply, kwAdjG_symm D x y]
  simp [eq_comm]

/-- **Completed square for the region with holes.**  With `w = v + √β K_G⁻¹ J`,
`½ v⬝Kv + √β J⬝v + (β/2) S ≥ ½ w⬝Kw + (β/2)(1-θ) S`. -/
theorem kwOp_boundary_square {ν : ℝ} (hν : 0 < ν) (D : Finset (Torus d m))
    (a : Torus d m → Torus d m → ℝ) (v : Torus d m → ℝ) {β : ℝ} (hβ : 0 ≤ β) :
    1 / 2 * ((v + Real.sqrt β • (kwOp d m ν D)⁻¹ *ᵥ bdryJ D a) ⬝ᵥ
        kwOp d m ν D *ᵥ (v + Real.sqrt β • (kwOp d m ν D)⁻¹ *ᵥ bdryJ D a))
      + β / 2 * (1 - kwQ d ν) * bdryS D a ≤
    1 / 2 * (v ⬝ᵥ kwOp d m ν D *ᵥ v) + Real.sqrt β * (bdryJ D a ⬝ᵥ v) + β / 2 * bdryS D a := by
  rw [completed_square (kwOp_symm ν D) (kwOp_det_isUnit hν D) v (bdryJ D a) hβ (bdryS D a)]
  have := boundary_schur hν D a
  nlinarith

/-- The exponential form: `e^{-E} ≤ e^{-β(1-θ)S/2} e^{-½ w⬝Kw}`. -/
theorem exp_boundary_square_le {ν : ℝ} (hν : 0 < ν) (D : Finset (Torus d m))
    (a : Torus d m → Torus d m → ℝ) (v : Torus d m → ℝ) {β : ℝ} (hβ : 0 ≤ β) :
    Real.exp (-(1 / 2 * (v ⬝ᵥ kwOp d m ν D *ᵥ v) + Real.sqrt β * (bdryJ D a ⬝ᵥ v)
        + β / 2 * bdryS D a)) ≤
      Real.exp (-(β * (1 - kwQ d ν) * bdryS D a / 2)) *
        Real.exp (-(1 / 2 * ((v + Real.sqrt β • (kwOp d m ν D)⁻¹ *ᵥ bdryJ D a) ⬝ᵥ
          kwOp d m ν D *ᵥ (v + Real.sqrt β • (kwOp d m ν D)⁻¹ *ᵥ bdryJ D a)))) := by
  rw [← Real.exp_add]
  apply Real.exp_le_exp.2
  have := kwOp_boundary_square hν D a v hβ
  nlinarith

end Region

/-! ### The normal term -/

section Normal

/-- `(h - q)·h = ‖h - q‖²/2` for unit vectors. -/
theorem inner_sub_self_unit {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {h q : E}
    (hh : ‖h‖ = 1) (hq : ‖q‖ = 1) : inner ℝ (h - q) h = ‖h - q‖ ^ 2 / 2 := by
  have e := norm_sub_sq_real h q
  rw [inner_sub_left, real_inner_self_eq_norm_sq, real_inner_comm]
  rw [hh, hq] at e
  rw [hh]
  linarith

theorem inner_sub_self_unit_nonneg {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {h q : E} (hh : ‖h‖ = 1) (hq : ‖q‖ = 1) : 0 ≤ inner ℝ (h - q) h := by
  rw [inner_sub_self_unit hh hq]; positivity

/-- For `0 < β` and `t² ≤ β`: `0 ≤ -(√β · n_β(t)) ≤ t²`, with `n_β = normalCoord β`. -/
theorem normal_term_bounds {β t : ℝ} (hβ : 0 < β) (ht : t ^ 2 ≤ β) :
    0 ≤ -(Real.sqrt β * normalCoord β t) ∧ -(Real.sqrt β * normalCoord β t) ≤ t ^ 2 := by
  have hs : 0 < Real.sqrt β := Real.sqrt_pos.2 hβ
  have h0 := normalCoord_nonpos hβ t
  have h1 := abs_normalCoord_le hβ ht
  rw [abs_of_nonpos h0] at h1
  refine ⟨by nlinarith, ?_⟩
  rw [le_div_iff₀ hs] at h1
  nlinarith

/-- A bound `|t| ≤ A log(βa)/√ν` gives `t² ≤ A² log²(βa)/ν`. -/
theorem sq_le_of_abs_le {t A ℓ ν : ℝ} (hν : 0 < ν) (h : |t| ≤ |A * ℓ| / Real.sqrt ν) :
    t ^ 2 ≤ A ^ 2 * ℓ ^ 2 / ν := by
  have hs : 0 < Real.sqrt ν := Real.sqrt_pos.2 hν
  have := (sq_le_sq (a := t) (b := A * ℓ / Real.sqrt ν)).2 (by
    rw [abs_div, abs_of_pos hs]; exact h)
  rw [div_pow, Real.sq_sqrt hν.le, mul_pow] at this
  exact this

/-- **Cost of the normal boundary term.**  With weights `a_e² ≥ 0` and tangent sizes `t_e² ≤ M ≤ β`,
the normal boundary term `∑_e (a_e²/2)(√β n_β(t_e))` is at least `-(M/2) ∑_e a_e²`. -/
theorem normal_cost {κ : Type*} (s : Finset κ) (w t : κ → ℝ) {β M : ℝ} (hβ : 0 < β)
    (hMβ : M ≤ β) (hw : ∀ e, 0 ≤ w e) (ht : ∀ e, t e ^ 2 ≤ M) :
    -(M / 2 * ∑ e ∈ s, w e) ≤ ∑ e ∈ s, w e / 2 * (Real.sqrt β * normalCoord β (t e)) := by
  rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_le_sum fun e _ => ?_
  have := (normal_term_bounds hβ ((ht e).trans hMβ)).2
  have h2 := ht e
  have := hw e
  nlinarith

/-- **Combined bound under the threshold inequality (H37.2).**  If the tangent boundary energy `T`
satisfies `T ≥ ½ Q + β(1-θ)S/2`, the normal boundary energy `N ≥ -(M/2) S`, `S ≥ 0` and
`M ≤ β(1-θ)/2`, then `T + N ≥ ½ Q + β(1-θ)S/4`. -/
theorem combined_ge {T N Q S M β θ : ℝ} (hS : 0 ≤ S) (hT : 1 / 2 * Q + β / 2 * (1 - θ) * S ≤ T)
    (hN : -(M / 2 * S) ≤ N) (hM : M ≤ β * (1 - θ) / 2) :
    1 / 2 * Q + β * (1 - θ) * S / 4 ≤ T + N := by
  nlinarith [mul_le_mul_of_nonneg_right hM hS]

theorem exp_combined_le {T N Q S M β θ : ℝ} (hS : 0 ≤ S)
    (hT : 1 / 2 * Q + β / 2 * (1 - θ) * S ≤ T) (hN : -(M / 2 * S) ≤ N)
    (hM : M ≤ β * (1 - θ) / 2) :
    Real.exp (-(T + N)) ≤ Real.exp (-(β * (1 - θ) * S / 4)) * Real.exp (-(1 / 2 * Q)) := by
  rw [← Real.exp_add]
  apply Real.exp_le_exp.2
  have := combined_ge hS hT hN hM
  linarith

/-- **Existence of the threshold.**  For `ν > 0`, `a > 0`, `θ < 1` and any `A` there is `β₁ ≥ 1`
with `A² log²(βa)/ν ≤ β(1-θ)/2` for all `β ≥ β₁`. -/
theorem exists_threshold (A a ν θ : ℝ) (hν : 0 < ν) (ha : 0 < a) (hθ : θ < 1) :
    ∃ β₁ : ℝ, 1 ≤ β₁ ∧ ∀ β : ℝ, β₁ ≤ β → A ^ 2 * Real.log (β * a) ^ 2 / ν ≤ β * (1 - θ) / 2 := by
  have hA : 0 < A ^ 2 + 1 := by positivity
  set c : ℝ := ν * (1 - θ) / (2 * (A ^ 2 + 1) * a) with hc
  have hcpos : 0 < c := by
    have : 0 < 1 - θ := by linarith
    positivity
  have hlo := (Real.isLittleO_pow_log_id_atTop (n := 2)).def hcpos
  have hT : Tendsto (fun β : ℝ => β * a) atTop atTop := tendsto_id.atTop_mul_const ha
  have hev := hT.eventually hlo
  obtain ⟨b, hb⟩ := Filter.eventually_atTop.1 hev
  refine ⟨max b 1, le_max_right _ _, fun β hβ => ?_⟩
  have hβ1 : 1 ≤ β := (le_max_right _ _).trans hβ
  have hbβ : b ≤ β := (le_max_left _ _).trans hβ
  have h := hb β hbβ
  have hx : 0 < β * a := by positivity
  simp only [Real.norm_eq_abs, id, abs_of_pos hx] at h
  rw [abs_of_nonneg (sq_nonneg _)] at h
  rw [div_le_iff₀ hν]
  have hl := sq_nonneg (Real.log (β * a))
  have e : c * (β * a) * (A ^ 2 + 1) = ν * (1 - θ) * β / 2 := by
    rw [hc]; field_simp
  have h1 := mul_le_mul_of_nonneg_left h hA.le
  have h2 : A ^ 2 * Real.log (β * a) ^ 2 ≤ (A ^ 2 + 1) * Real.log (β * a) ^ 2 := by nlinarith
  nlinarith

end Normal

/-! ### Instance -/

section Instance

/-- Non-vacuity: `d = m = 3`, `ν = 1/8`, `D = {0}`, `a ≡ 1`: `θ = 48/49` and `S = 6`. -/
theorem boundary_schur_instance :
    kwQ 3 (1 / 8 : ℝ) = 48 / 49 ∧
    bdryS kwInstD (fun _ _ : Torus 3 3 => (1 : ℝ)) = 6 ∧
    bdryJ kwInstD (fun _ _ : Torus 3 3 => (1 : ℝ)) ⬝ᵥ
        (kwOp 3 3 (1 / 8 : ℝ) kwInstD)⁻¹ *ᵥ bdryJ kwInstD (fun _ _ : Torus 3 3 => (1 : ℝ))
      ≤ 48 / 49 * 6 := by
  have hq : kwQ 3 (1 / 8 : ℝ) = 48 / 49 := by unfold kwQ; norm_num
  have hS : bdryS kwInstD (fun _ _ : Torus 3 3 => (1 : ℝ)) = 6 := by
    have h0 : kwAdj 3 3 (0 : Torus 3 3) 0 = 0 := by
      rw [kwAdj_apply]
      refine Finset.sum_eq_zero fun μ _ => ?_
      have hne : (0 : Torus 3 3) ≠ 0 + Pi.single μ 1 := by
        intro h
        have := congrFun h μ
        revert this
        decide +revert
      have hne' : ¬ (0 : Torus 3 3) = Pi.single μ 1 := by simpa using hne
      simp [hne']
    have hrow : ∑ x : Torus 3 3, kwAdj 3 3 x 0 = 6 := by
      simp_rw [kwAdj_symm _ (0 : Torus 3 3)]
      rw [kwAdj_rowSum]; norm_num
    unfold bdryS kwInstD
    simp only [Finset.mem_singleton, Finset.sum_singleton, one_pow, mul_one]
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ (0 : Torus 3 3))] at hrow
    rw [h0, add_zero] at hrow
    rw [← hrow, ← Finset.sum_erase_add _ _ (Finset.mem_univ (0 : Torus 3 3))]
    simp only [ite_true, add_zero]
    exact Finset.sum_congr rfl fun x hx => by simp [Finset.ne_of_mem_erase hx]
  refine ⟨hq, hS, ?_⟩
  have := boundary_schur (d := 3) (m := 3) (ν := (1 / 8 : ℝ)) (by norm_num) kwInstD
    (fun _ _ => (1 : ℝ))
  rwa [hq, hS] at this

end Instance

end Balaban.LargeField
