/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Base.BaseChartCutTangent
public import Balaban.LargeField.Base.BaseChartQuadraticPhysical
public import Balaban.LargeField.Base.BaseCutoffTransfer
public import Balaban.LargeField.Base.Prop279

/-!
# The first-step chart remainder as site-local factors, and the footprint margin

For a fixed background `e` and fixed multiplier `α` (hence a fixed Hessian with matrix entries `a`),
the remainder `F` of the normalized cut chart integral
(`baseSectorChartIntegral_eq_cut_normalized`) is a product of factors that each read the tangent
vector at one site, or at the two ends of one pair of sites, or at the two ends of one crossing
bond, with explicit majorants on the region `‖w x‖ ≤ √β / 2` (that is `|ξ| ≤ 1/2`):

* the chart shift `z_x` depends on `w x` only, `‖z_x‖ ≤ ‖w x‖² / √β`;
* the Jacobian is the product of the site factors `(1 - ‖w x‖²/β)^(-1/2) ∈ [1, 2]`;
* the interaction `⟨w, H z⟩ + ½ ⟨z, H z⟩` is the sum over pairs `(x, y)` of `a x y` times a term
  that reads `w x` and `w y`;
* the missing crossing-bond form `q 1 - q s` is a sum over the bonds of `𝓔` of
  `½ (1 - s_b) ∑_i (W (x₁, i) - W (x₀, i))²`;
* the source and the residual mass are sums over sites.

The dependence of `α` on the coarse field `θ` is nonlocal; it enters only through the fixed `a`
(blocker G4 of BASEPLAN).

The last section states the footprint-margin theorem `baseFootprint_margin_of_cutoff_of_bondCross` (BASE-KERNEL-4
(2.6), (2.8)) with the background comparison across `∂Ω''` as an explicit hypothesis.
-/

@[expose] public section

namespace Balaban.LargeField

open Balaban Balaban.Background Balaban.Multiscale Balaban.Green Matrix
open Balaban.LargeField.Base Balaban.Localization

section Chart

variable {ι : Type*} {N : ℕ}

/-- The chart shift at one site reads `w x` only. -/
theorem chartShift_congr_site {β : ℝ} {e : ι → EuclideanSpace ℝ (Fin N)}
    {w w' : Config ι N} {x : ι} (h : w x = w' x) :
    chartShift β e w x = chartShift β e w' x := by
  simp only [chartShift, h]

/-- The chart point at one site reads `w x` only. -/
theorem chartPoint_congr_site {β : ℝ} {e : ι → EuclideanSpace ℝ (Fin N)}
    {w w' : Config ι N} {x : ι} (h : w x = w' x) :
    chartPoint β e w x = chartPoint β e w' x := by
  simp only [chartPoint, chartShift, h]

/-- `|√(1 - t) - 1| ≤ t` for `t ∈ [0, 1]`. -/
theorem abs_sqrt_one_sub_sub_one_le {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    |Real.sqrt (1 - t) - 1| ≤ t := by
  have hs0 : 0 ≤ Real.sqrt (1 - t) := Real.sqrt_nonneg _
  have hs1 : Real.sqrt (1 - t) ≤ 1 := by
    rw [Real.sqrt_le_one]; linarith
  have hsq : Real.sqrt (1 - t) ^ 2 = 1 - t := Real.sq_sqrt (by linarith)
  rw [abs_of_nonpos (by linarith)]
  nlinarith

/-- **Majorant of the chart shift:** `‖z_x‖ ≤ ‖w x‖² / √β` (in the coordinate `ξ = w/√β` of
the brief, `‖z_x/√β‖ ≤ ‖ξ_x‖²`). -/
theorem norm_chartShift_le {β : ℝ} (hβ : 0 < β) {e : ι → EuclideanSpace ℝ (Fin N)}
    (he : ∀ x, ‖e x‖ = 1) {w : Config ι N} (x : ι) (hw : ‖w x‖ ^ 2 ≤ β) :
    ‖chartShift β e w x‖ ≤ ‖w x‖ ^ 2 / Real.sqrt β := by
  have hs : 0 < Real.sqrt β := Real.sqrt_pos.2 hβ
  have ht0 : 0 ≤ ‖w x‖ ^ 2 / β := by positivity
  have ht1 : ‖w x‖ ^ 2 / β ≤ 1 := (div_le_one hβ).2 hw
  have := abs_sqrt_one_sub_sub_one_le ht0 ht1
  unfold chartShift
  simp only [norm_smul, he x, mul_one, Real.norm_eq_abs, abs_mul, abs_of_pos hs]
  calc Real.sqrt β * |Real.sqrt (1 - ‖w x‖ ^ 2 / β) - 1|
      ≤ Real.sqrt β * (‖w x‖ ^ 2 / β) := mul_le_mul_of_nonneg_left this hs.le
    _ = ‖w x‖ ^ 2 / Real.sqrt β := by
      have : β = Real.sqrt β * Real.sqrt β := (Real.mul_self_sqrt hβ.le).symm
      field_simp
      nth_rewrite 2 [this]
      ring

/-- On `‖w x‖ ≤ √β / 2` the chart point is within `(3/2) ‖w x‖ / √β` of `e x`. -/
theorem norm_chartPoint_sub_le {β : ℝ} (hβ : 0 < β) {e : ι → EuclideanSpace ℝ (Fin N)}
    (he : ∀ x, ‖e x‖ = 1) {w : Config ι N} (x : ι) (hw : ‖w x‖ ≤ Real.sqrt β / 2) :
    ‖chartPoint β e w x - e x‖ ≤ 3 / 2 * (‖w x‖ / Real.sqrt β) := by
  have hs : 0 < Real.sqrt β := Real.sqrt_pos.2 hβ
  have hsq : ‖w x‖ ^ 2 ≤ β := by
    have h0 : 0 ≤ ‖w x‖ := norm_nonneg _
    have : ‖w x‖ ^ 2 ≤ (Real.sqrt β / 2) ^ 2 := by gcongr
    have h2 : (Real.sqrt β / 2) ^ 2 = β / 4 := by
      rw [div_pow, Real.sq_sqrt hβ.le]; norm_num
    linarith
  have hz := norm_chartShift_le hβ he (w := w) x hsq
  have hd : chartPoint β e w x - e x = (Real.sqrt β)⁻¹ • (w x + chartShift β e w x) := by
    simp [chartPoint]
  rw [hd, norm_smul, norm_inv, Real.norm_of_nonneg hs.le]
  have h1 : ‖w x + chartShift β e w x‖ ≤ ‖w x‖ + ‖w x‖ ^ 2 / Real.sqrt β :=
    (norm_add_le _ _).trans (by linarith)
  have h2 : ‖w x‖ ^ 2 / Real.sqrt β ≤ 1 / 2 * ‖w x‖ := by
    rw [div_le_iff₀ hs]
    have h0 : 0 ≤ ‖w x‖ := norm_nonneg _
    nlinarith
  calc (Real.sqrt β)⁻¹ * ‖w x + chartShift β e w x‖
      ≤ (Real.sqrt β)⁻¹ * (3 / 2 * ‖w x‖) :=
        mul_le_mul_of_nonneg_left (by linarith) (inv_nonneg.2 hs.le)
    _ = 3 / 2 * (‖w x‖ / Real.sqrt β) := by ring

/-- The one-site Jacobian factor lies in `[1, 2]` for `‖w x‖ ≤ √β / 2`. -/
theorem chartJac_site_bounds {β : ℝ} (hβ : 0 < β) {r : ℝ} (hr : r ≤ Real.sqrt β / 2)
    (hr0 : 0 ≤ r) :
    1 ≤ (Real.sqrt (1 - r ^ 2 / β))⁻¹ ∧ (Real.sqrt (1 - r ^ 2 / β))⁻¹ ≤ 2 := by
  have hs : 0 < Real.sqrt β := Real.sqrt_pos.2 hβ
  have hsq : r ^ 2 ≤ β / 4 := by
    have : r ^ 2 ≤ (Real.sqrt β / 2) ^ 2 := by gcongr
    rwa [div_pow, Real.sq_sqrt hβ.le, show ((2 : ℝ) ^ 2) = 4 by norm_num] at this
  have ht0 : 0 ≤ r ^ 2 / β := by positivity
  have ht1 : r ^ 2 / β ≤ 1 / 4 := by
    rw [div_le_iff₀ hβ]; linarith
  have hpos : 0 < Real.sqrt (1 - r ^ 2 / β) := Real.sqrt_pos.2 (by linarith)
  have hle1 : Real.sqrt (1 - r ^ 2 / β) ≤ 1 := by rw [Real.sqrt_le_one]; linarith
  have hge : 1 / 2 ≤ Real.sqrt (1 - r ^ 2 / β) := by
    rw [show (1 / 2 : ℝ) = Real.sqrt (1 / 4) by
      rw [show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by linarith)
  constructor
  · exact one_le_inv₀ hpos |>.2 hle1
  · rw [inv_le_comm₀ hpos (by norm_num)]; linarith

/-- **The Jacobian is a product of site factors, each in `[1, 2]`**, so it is at most
`2 ^ |ι|`, on `‖w x‖ ≤ √β / 2`. -/
theorem chartJac_eq_prod_le [Fintype ι] {β : ℝ} (hβ : 0 < β) {w : Config ι N}
    (hw : ∀ x, ‖w x‖ ≤ Real.sqrt β / 2) :
    chartJac β w = ∏ x, (Real.sqrt (1 - ‖w x‖ ^ 2 / β))⁻¹ ∧
      1 ≤ chartJac β w ∧ chartJac β w ≤ 2 ^ Fintype.card ι := by
  have hs : 0 < Real.sqrt β := Real.sqrt_pos.2 hβ
  have hlt : ∀ x, ‖w x‖ < Real.sqrt β := fun x => by linarith [hw x]
  have hb := fun x => chartJac_site_bounds hβ (hw x) (norm_nonneg (w x))
  refine ⟨chartJac_of_lt hlt, ?_⟩
  rw [chartJac_of_lt hlt]
  have h0 : ∀ x, 0 ≤ (Real.sqrt (1 - ‖w x‖ ^ 2 / β))⁻¹ := fun x => by linarith [(hb x).1]
  refine ⟨?_, ?_⟩
  · have : ∏ _x : ι, (1 : ℝ) ≤ ∏ x, (Real.sqrt (1 - ‖w x‖ ^ 2 / β))⁻¹ := by
      refine Finset.prod_le_prod₀ ?_ ?_
      · intro x _; exact zero_le_one
      · intro x _; exact (hb x).1
    simpa using this
  · have : ∏ x, (Real.sqrt (1 - ‖w x‖ ^ 2 / β))⁻¹ ≤ ∏ _x : ι, (2 : ℝ) := by
      refine Finset.prod_le_prod₀ ?_ ?_
      · intro x _; exact h0 x
      · intro x _; exact (hb x).2
    simpa using this

/-- The Hessian pairing as a double sum over pairs of sites: for a Hessian with matrix entries `a`,
`⟨u, H v⟩ = ∑_{x,y} a x y ⟨u x, v y⟩`. -/
theorem cinner_apply_pairwise [Fintype ι] (a : ι → ι → ℝ) (H : Config ι N →ₗ[ℝ] Config ι N)
    (hH : ∀ u x i, (H u x i : ℝ) = ∑ y, a x y * (u y i : ℝ)) (u v : Config ι N) :
    cinner u (H v) = ∑ x, ∑ y, a x y * inner ℝ (u x) (v y) := by
  unfold cinner
  refine Finset.sum_congr rfl fun x _ => ?_
  simp only [PiLp.inner_apply, hH, RCLike.inner_apply, conj_trivial]
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun i _ => ?_
  ring

/-- **The interaction exponent is a sum over pairs of sites.**  For a Hessian with entries `a`,
`⟨w, H z⟩ + ½ ⟨z, H z⟩ = ∑_{x,y} a x y (⟨w x, z y⟩ + ½ ⟨z x, z y⟩)` with `z = chartShift β e w`;
the `(x, y)` term reads `w x` and `w y` only (`chartShift_congr_site`). -/
theorem chart_interaction_pairwise [Fintype ι] {β : ℝ} (e : ι → EuclideanSpace ℝ (Fin N))
    (a : ι → ι → ℝ) (H : Config ι N →ₗ[ℝ] Config ι N)
    (hH : ∀ u x i, (H u x i : ℝ) = ∑ y, a x y * (u y i : ℝ)) (w : Config ι N) :
    cinner w (H (chartShift β e w)) + (1 / 2) * cinner (chartShift β e w) (H (chartShift β e w)) =
      ∑ x, ∑ y, a x y * (inner ℝ (w x) (chartShift β e w y) +
        (1 / 2) * inner ℝ (chartShift β e w x) (chartShift β e w y)) := by
  rw [cinner_apply_pairwise a H hH, cinner_apply_pairwise a H hH, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun y _ => ?_
  ring

/-- **Majorant of one pair term** for `‖w x‖, ‖w y‖ ≤ √β / 2`:
`|⟨w x, z y⟩ + ½ ⟨z x, z y⟩| ≤ ‖w x‖ ‖w y‖² / √β + ½ ‖w x‖² ‖w y‖² / β`. -/
theorem abs_chart_pair_term_le {β : ℝ} (hβ : 0 < β) {e : ι → EuclideanSpace ℝ (Fin N)}
    (he : ∀ x, ‖e x‖ = 1) {w : Config ι N} (x y : ι) (hx : ‖w x‖ ^ 2 ≤ β) (hy : ‖w y‖ ^ 2 ≤ β) :
    |inner ℝ (w x) (chartShift β e w y) + (1 / 2) * inner ℝ (chartShift β e w x)
        (chartShift β e w y)| ≤
      ‖w x‖ * (‖w y‖ ^ 2 / Real.sqrt β) +
        (1 / 2) * ((‖w x‖ ^ 2 / Real.sqrt β) * (‖w y‖ ^ 2 / Real.sqrt β)) := by
  have hzx := norm_chartShift_le hβ he (w := w) x hx
  have hzy := norm_chartShift_le hβ he (w := w) y hy
  have h1 : |inner ℝ (w x) (chartShift β e w y)| ≤ ‖w x‖ * (‖w y‖ ^ 2 / Real.sqrt β) :=
    (abs_real_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_left hzy (norm_nonneg _))
  have h2 : |inner ℝ (chartShift β e w x) (chartShift β e w y)| ≤
      (‖w x‖ ^ 2 / Real.sqrt β) * (‖w y‖ ^ 2 / Real.sqrt β) :=
    (abs_real_inner_le_norm _ _).trans
      (mul_le_mul hzx hzy (norm_nonneg _) ((norm_nonneg _).trans hzx))
  calc _ ≤ |inner ℝ (w x) (chartShift β e w y)| +
        |(1 / 2) * inner ℝ (chartShift β e w x) (chartShift β e w y)| := abs_add_le _ _
    _ ≤ _ := by
      rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
      linarith

end Chart

section Source

variable {ι : Type*} [Fintype ι] {N : ℕ}

omit [Fintype ι] in
/-- The source term at one site is bounded by the coordinate sum of `g` times `‖w x + z x‖`. -/
theorem norm_source_site_le {β : ℝ} (e : ι → EuclideanSpace ℝ (Fin N)) (g : ι → Fin N → ℂ)
    (w : Config ι N) (x : ι) :
    ‖(((Real.sqrt β)⁻¹ : ℝ) : ℂ) * ∑ i, g x i * (((w x + chartShift β e w x) i : ℝ) : ℂ)‖ ≤
      (Real.sqrt β)⁻¹ * ((∑ i, ‖g x i‖) * ‖w x + chartShift β e w x‖) := by
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_inv, abs_of_nonneg (Real.sqrt_nonneg _)]
  refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.2 (Real.sqrt_nonneg _))
  refine (norm_sum_le _ _).trans ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [norm_mul, Complex.norm_real]
  exact mul_le_mul_of_nonneg_left ((PiLp.norm_apply_le _ i).trans le_rfl) (norm_nonneg _)

/-- The source and the residual-mass terms are sums over single sites: the exponent of `F` splits
as the constant terms plus site sums plus pair sums plus the crossing-bond form. -/
theorem exp_eq_const_mul_prod_site {β : ℝ} (e : ι → EuclideanSpace ℝ (Fin N)) (a : ι → ι → ℝ)
    (H : Config ι N →ₗ[ℝ] Config ι N)
    (hH : ∀ u x i, (H u x i : ℝ) = ∑ y, a x y * (u y i : ℝ)) (g : ι → Fin N → ℂ)
    (w : Config ι N) (c : ℝ) (h : EuclideanSpace ℝ (Fin N)) (E : ℝ) (Qd : ℂ) :
    Complex.exp (-((E : ℝ) : ℂ) + (∑ x, ∑ i, g x i * (((e x) i : ℝ) : ℂ)) +
        (((Real.sqrt β)⁻¹ : ℝ) : ℂ) * (∑ x, ∑ i, g x i * (((w x + chartShift β e w x) i : ℝ) : ℂ)) -
        (((cinner w (H (chartShift β e w)) + (1 / 2) * cinner (chartShift β e w)
            (H (chartShift β e w)) + c * ∑ x, ‖chartPoint β e w x - h‖ ^ 2 : ℝ) : ℂ) + Qd)) =
      Complex.exp (-((E : ℝ) : ℂ) + (∑ x, ∑ i, g x i * (((e x) i : ℝ) : ℂ))) *
        (∏ x, Complex.exp ((((Real.sqrt β)⁻¹ : ℝ) : ℂ) *
            ∑ i, g x i * (((w x + chartShift β e w x) i : ℝ) : ℂ) -
          ((c * ‖chartPoint β e w x - h‖ ^ 2 : ℝ) : ℂ))) *
        (∏ x, ∏ y, Complex.exp (-((a x y * (inner ℝ (w x) (chartShift β e w y) +
          (1 / 2) * inner ℝ (chartShift β e w x) (chartShift β e w y)) : ℝ) : ℂ))) *
        Complex.exp (-Qd) := by
  rw [chart_interaction_pairwise e a H hH w]
  simp only [← Complex.exp_sum, ← Complex.exp_add, Complex.ofReal_add, Complex.ofReal_sum,
    Complex.ofReal_mul, Complex.ofReal_pow, Finset.mul_sum, ← Finset.sum_add_distrib,
    Finset.sum_neg_distrib]
  congr 1
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib]
  ring

end Source

section Cross

variable {d L N₀ N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ} (G : GeneratingSet d L N₀ 1 ϱ)

/-- The pairing with a lifted matrix as a triple sum. -/
theorem pair_liftOp_mulVec (M : Matrix (G.Ω 1) (G.Ω 1) ℂ) (W : G.Ω 1 × Fin N → ℂ) :
    pair G W (liftOp N M *ᵥ W) = ∑ i : Fin N, ∑ x : G.Ω 1, ∑ y : G.Ω 1, W (x, i) * M x y * W (y, i) := by
  have hmv : ∀ (x : G.Ω 1) (i : Fin N), (liftOp N M *ᵥ W) (x, i) = ∑ y, M x y * W (y, i) := by
    intro x i
    simp [Matrix.mulVec, dotProduct, liftOp, Fintype.sum_prod_type, ite_mul]
  unfold pair
  rw [Fintype.sum_prod_type_right]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun x _ => ?_
  rw [hmv, Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  ring

/-- The form of a bond matrix `T_b` is the square of the bond difference. -/
theorem pair_liftOp_baseBond (b : FineBond d L N₀) (hb0 : b.1 ∈ G.Ω 1)
    (hb1 : b.1 + Pi.single b.2 1 ∈ G.Ω 1) (W : G.Ω 1 × Fin N → ℂ)
    (W' : Torus d (N₀ * L ^ 1) → Fin N → ℂ) (hW : ∀ p, W p = W' p.1 p.2) :
    pair G W (liftOp N (baseBond G b) *ᵥ W) =
      ∑ i : Fin N, (W' (b.1 + Pi.single b.2 1) i - W' b.1 i) ^ 2 := by
  rw [pair_liftOp_mulVec]
  refine Finset.sum_congr rfl fun i _ => ?_
  have key : ∑ x : G.Ω 1, ((bondVec b x : ℝ) : ℂ) * W (x, i) =
      W' (b.1 + Pi.single b.2 1) i - W' b.1 i := by
    have h1 : ∑ x : G.Ω 1, ((bondVec b x : ℝ) : ℂ) * W (x, i) =
        ∑ x : G.Ω 1, ((bondVec b (x : Torus d (N₀ * L ^ 1)) : ℝ) : ℂ) * W' x i :=
      Finset.sum_congr rfl fun x _ => by rw [hW]
    rw [h1, Finset.sum_coe_sort (G.Ω 1) (fun x => ((bondVec b x : ℝ) : ℂ) * W' x i)]
    simp [bondVec, Pi.single_apply, sub_mul, Finset.sum_sub_distrib, hb0, hb1, apply_ite Complex.ofReal, ite_mul]
  calc ∑ x : G.Ω 1, ∑ y : G.Ω 1, W (x, i) * baseBond G b x y * W (y, i)
      = (∑ x : G.Ω 1, ((bondVec b x : ℝ) : ℂ) * W (x, i)) *
        (∑ y : G.Ω 1, ((bondVec b y : ℝ) : ℂ) * W (y, i)) := by
        rw [Finset.sum_mul_sum]
        refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
        rw [baseBond_apply]; ring
    _ = _ := by rw [key]; ring

omit [NeZero N₀] [NeZero L] in
theorem liftOp_sub_sum {ι : Type*} [Fintype ι] (A B : Matrix ι ι ℂ) :
    liftOp N (A - B) = liftOp N A - liftOp N B := by
  ext p q; simp only [liftOp, Matrix.sub_apply]; split_ifs <;> simp

omit [NeZero N₀] [NeZero L] in
theorem liftOp_finset_sum {ι κ : Type*} [Fintype ι] (S : Finset κ) (f : κ → Matrix ι ι ℂ) :
    liftOp N (∑ b ∈ S, f b) = ∑ b ∈ S, liftOp N (f b) := by
  ext p q; simp only [liftOp, Matrix.sum_apply]; split_ifs <;> simp

omit [NeZero N₀] [NeZero L] in
theorem liftOp_smul {ι : Type*} [Fintype ι] (c : ℂ) (A : Matrix ι ι ℂ) :
    liftOp N (c • A) = c • liftOp N A := by
  ext p q; simp only [liftOp, Matrix.smul_apply]; split_ifs <;> simp

/-- **The missing crossing-bond form is a sum over the bonds of `𝓔`:**
`q 1 - q s = ½ ∑_{b ∈ 𝓔} (1 - s_b) ∑_i (W (x_b + e_μ, i) - W (x_b, i))²`, where
`q t = ½ ⟨W, (H(t) ⊗ I) W⟩`.  The term of `b` reads `W` at the two ends of `b` only. -/
theorem baseCut_crossForm (a : ℕ → ℝ) (ν : ℝ) (α : G.Ω 1 → ℂ) (t s : FineBond d L N₀ → ℂ)
    (W : G.Ω 1 × Fin N → ℂ) (W' : Torus d (N₀ * L ^ 1) → Fin N → ℂ)
    (hW : ∀ p, W p = W' p.1 p.2) :
    (1 / 2) * pair G W (liftOp N (baseHamiltonian G a ν α t) *ᵥ W) -
        (1 / 2) * pair G W (liftOp N (baseHamiltonian G a ν α s) *ᵥ W) =
      (1 / 2) * ∑ b ∈ baseCutBonds G, (t b - s b) *
        ∑ i : Fin N, (W' (b.1 + Pi.single b.2 1) i - W' b.1 i) ^ 2 := by
  have hdiff : baseHamiltonian G a ν α t - baseHamiltonian G a ν α s =
      ∑ b ∈ baseCutBonds G, (t b - s b) • baseBond G b := by
    unfold baseHamiltonian
    simp only [add_sub_add_left_eq_sub, ← Finset.sum_sub_distrib, sub_smul]
  have hpair : pair G W (liftOp N (baseHamiltonian G a ν α t) *ᵥ W) -
      pair G W (liftOp N (baseHamiltonian G a ν α s) *ᵥ W) =
      ∑ b ∈ baseCutBonds G, (t b - s b) * pair G W (liftOp N (baseBond G b) *ᵥ W) := by
    have : liftOp N (baseHamiltonian G a ν α t) *ᵥ W - liftOp N (baseHamiltonian G a ν α s) *ᵥ W =
        ∑ b ∈ baseCutBonds G, (t b - s b) • (liftOp N (baseBond G b) *ᵥ W) := by
      rw [← Matrix.sub_mulVec, ← liftOp_sub_sum, hdiff, liftOp_finset_sum, Matrix.sum_mulVec]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [liftOp_smul, Matrix.smul_mulVec]
    have h2 : ∀ (u v : G.Ω 1 × Fin N → ℂ), pair G W u - pair G W v = pair G W (u - v) := by
      intro u v; unfold pair; simp [mul_sub, Finset.sum_sub_distrib]
    rw [h2, this]
    unfold pair
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun p _ => ?_
    ring
  have hb : ∀ b ∈ baseCutBonds G, pair G W (liftOp N (baseBond G b) *ᵥ W) =
      ∑ i : Fin N, (W' (b.1 + Pi.single b.2 1) i - W' b.1 i) ^ 2 := by
    intro b hb
    have hb' := Finset.mem_filter.1 hb
    exact pair_liftOp_baseBond G b hb'.2.1 hb'.2.2.1 W W' hW
  rw [← mul_sub, hpair]
  congr 1
  exact Finset.sum_congr rfl fun b hbm => by rw [hb b hbm]

/-- The crossing-bond term of the real tangent vector `w` is `½ (1 - s_b) ‖w (x_b + e_μ) - w x_b‖²`,
and `‖w x₁ - w x₀‖² ≤ (‖w x₁‖ + ‖w x₀‖)²`. -/
theorem crossTerm_real {ι : Type*} [Fintype ι] (w : Config ι N) (x₀ x₁ : ι) :
    ∑ i : Fin N, ((((w x₁) i : ℝ) : ℂ) - (((w x₀) i : ℝ) : ℂ)) ^ 2 =
        ((‖w x₁ - w x₀‖ ^ 2 : ℝ) : ℂ) ∧
      ‖w x₁ - w x₀‖ ^ 2 ≤ (‖w x₁‖ + ‖w x₀‖) ^ 2 := by
  refine ⟨?_, ?_⟩
  · rw [EuclideanSpace.norm_sq_eq]
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    have h := sq_abs ((w x₁).ofLp i - (w x₀).ofLp i)
    have h' := congrArg (fun r : ℝ => (r : ℂ)) h
    push_cast at h'
    simpa [Real.norm_eq_abs] using h'.symm
  · gcongr
    exact norm_sub_le _ _

end Cross

section Margin

variable {d N : ℕ} (nn : ℕ → ℕ) (L M K : ℕ) [∀ k, NeZero (nn k)] [NeZero M] [NeZero L]

/-- **T1, conditional form, `baseFootprint_margin_of_cutoff_of_bondCross`.** The crossing-bond margin `bondCross` (sector centre against the retained spin across ∂Ω″, P5 Lemma 2.1) is a HYPOTHESIS here and is the open content of T1; for those bonds this theorem proves nothing new. (BASE-KERNEL-4 (2.6), (2.8)).  On the support of the
fluctuation cutoff, `|φ - e| ≤ r` on the footprints of `𝒥₊` with the chart radius `r ≤ δ₀/4`
of (2.8), the strict margins (2.4) of `BaseCutoffMargins` hold on the footprints of `𝒥₊`.

The background `e` is the sector background on the set `Din` and the retained spin `φ` outside it
(`hext`).  The background comparison is split by the position of the bond:
* `bondIn`: both ends in `Din` (the interior gradient bound of the background, BgHyp);
* `bondOut`: both ends outside `Din` (the retained output test on `φ`, with margin `δ₀/2`);
* `bondCross`: **one end in `Din`, the other outside, that is a bond across `∂Ω''₁`**.  This is the
  background comparison across `∂Ω''₁` (P5 Lemma 2.1, Lemma III.7.1): it is not a consequence of the
  landed results and is exactly what remains open (BASE-KERNEL-4 §2, row 3).
The block test (`block`) and the regime-(B) site test (`site`) are the other output tests of (2.6).
The conclusion for the three first cases is `baseCutoffMargins_of_convenient`. -/
theorem baseFootprint_margin_of_cutoff_of_bondCross {regimeB : Prop} {ν δ₀ r : ℝ} {h : Fin N → ℝ}
    {P : Set (Torus d (nn 1))} {Dplus : Set (Torus d (M * nn K * L ^ K))}
    {φ e : Torus d (M * nn K * L ^ K) → Fin N → ℝ}
    {θ : Torus d (M * nn K * L ^ (K - 1)) → Fin N → ℝ}
    {a B5 A0 A1 K2 : ℝ} (hδ : 0 < δ₀) (hB5 : 0 < B5) (hA1 : 0 < A1) (hK2 : 0 < K2) (ha : 0 ≤ a)
    (hA0 : A0 = 4 * K2 * B5 * A1) (hK : 2 * Real.sqrt a ≤ K2)
    (hmass : ν ≤ 1 ∨ 2 * Real.sqrt (a * ν) ≤ K2)
    (hr : r ≤ 2 * B5 * Real.sqrt a * (A1 / A0) * δ₀) (hr0 : 0 ≤ r)
    (Din : Set (Torus d (M * nn K * L ^ K)))
    (hext : ∀ x ∉ Din, ∀ i, e x i = φ x i)
    (unit : ∀ c ∈ baseJPlus nn L M K regimeB P Dplus, ∀ x ∈ baseFootprint nn L M K regimeB c,
      ∑ i, e x i ^ 2 = 1)
    (close : ∀ c ∈ baseJPlus nn L M K regimeB P Dplus, ∀ x ∈ baseFootprint nn L M K regimeB c,
      rn (fun i => φ x i - e x i) ≤ r)
    (block : ∀ c ∈ baseJPlus nn L M K regimeB P Dplus, ∀ y : Torus d (M * nn K * L ^ (K - 1)),
      blockMap M (nn 1) y = c →
        rn (fun i => θ y i - spinAverage nn L M K e y i) < 3 / 2 * δ₀)
    (bondIn : ∀ c ∈ baseJPlus nn L M K regimeB P Dplus, ∀ (x : Torus d (M * nn K * L ^ K))
      (μ : Fin d), (cubeMap nn L M K 1 x = c ∨ cubeMap nn L M K 1 (x + Pi.single μ 1) = c) →
        x ∈ Din → x + Pi.single μ 1 ∈ Din →
        rn (fun i => e (x + Pi.single μ 1) i - e x i) < δ₀ / 2)
    (bondOut : ∀ c ∈ baseJPlus nn L M K regimeB P Dplus, ∀ (x : Torus d (M * nn K * L ^ K))
      (μ : Fin d), (cubeMap nn L M K 1 x = c ∨ cubeMap nn L M K 1 (x + Pi.single μ 1) = c) →
        x ∉ Din → x + Pi.single μ 1 ∉ Din →
        rn (fun i => φ (x + Pi.single μ 1) i - φ x i) < δ₀ / 2)
    (bondCross : ∀ c ∈ baseJPlus nn L M K regimeB P Dplus, ∀ (x : Torus d (M * nn K * L ^ K))
      (μ : Fin d), (cubeMap nn L M K 1 x = c ∨ cubeMap nn L M K 1 (x + Pi.single μ 1) = c) →
        (x ∈ Din ∧ x + Pi.single μ 1 ∉ Din) ∨ (x ∉ Din ∧ x + Pi.single μ 1 ∈ Din) →
        rn (fun i => e (x + Pi.single μ 1) i - e x i) < δ₀ / 2)
    (site : ∀ c ∈ baseJPlus nn L M K regimeB P Dplus, regimeB →
      ∀ x : Torus d (M * nn K * L ^ K), cubeMap nn L M K 1 x = c →
        Real.sqrt ν * rn (fun i => e x i - h i) < δ₀ / 2) :
    BaseCutoffMargins nn L M K regimeB ν δ₀ r h P Dplus φ e θ := by
  have hr4 : r ≤ δ₀ / 4 := chartRadius_le_quarter hδ hB5 hA1 hK2 hA0 hK hr
  have hνr : Real.sqrt ν * r ≤ δ₀ / 4 := by
    rcases hmass with h1 | h2
    · calc Real.sqrt ν * r ≤ 1 * r := by
            gcongr
            exact Real.sqrt_le_one.2 h1
        _ ≤ δ₀ / 4 := by linarith
    · exact sqrtNu_chartRadius_le_quarter hδ hB5 hA1 hK2 ha hA0 h2 hr
  refine baseCutoffMargins_of_convenient nn L M K hδ hr4 hνr unit close block ?_ site
  intro c hc x μ hx
  by_cases h1 : x ∈ Din <;> by_cases h2 : x + Pi.single μ 1 ∈ Din
  · exact bondIn c hc x μ hx h1 h2
  · exact bondCross c hc x μ hx (Or.inl ⟨h1, h2⟩)
  · exact bondCross c hc x μ hx (Or.inr ⟨h1, h2⟩)
  · have := bondOut c hc x μ hx h1 h2
    have e1 : (fun i => e (x + Pi.single μ 1) i - e x i) =
        fun i => φ (x + Pi.single μ 1) i - φ x i := by
      funext i; rw [hext _ h2 i, hext _ h1 i]
    rw [e1]; exact this

end Margin


end Balaban.LargeField
