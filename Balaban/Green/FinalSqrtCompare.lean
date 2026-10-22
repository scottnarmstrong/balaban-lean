/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Green.FinalComplexMatrix

/-!
# Comparison of the inverse square roots of two coercive matrices (shared core, A6-3, B-1″)

For two matrices `U₁, U₂` on a finite metric index set whose resolvents `(U_i + t)⁻¹`, `t ≥ 0`, have
the Combes–Thomas bound `2/(γ + t) e^{-ρ |x - y|}`, the Stieltjes representation
`sqrtMat U = π⁻¹ ∫₀^∞ t^{-1/2} (t + U)⁻¹ dt` and the resolvent identity
`(t + U₁)⁻¹ - (t + U₂)⁻¹ = (t + U₁)⁻¹ (U₂ - U₁) (t + U₂)⁻¹` give

  `|sqrtMat U₁ (x, y) - sqrtMat U₂ (x, y)| ≤ 4 / (γ √γ) ∑_{u, v} e^{-ρ |x - u|} η(u, v) e^{-ρ |v - y|}`

for every entrywise bound `|U₁(u, v) - U₂(u, v)| ≤ η(u, v)` (`norm_sqrtMat_sub_le_of_resolvent`).
With coercivity (gap `γ`) and exponentially decaying entries the resolvent bound is the landed
Combes–Thomas estimate (`norm_sqrtMat_sub_le`, rate `ctRate`).  This is shared: the local-pair
whitening of the last integral (B-1″) and the regional problems compare their operators with the
whole-torus one through it; when `U₁ = U₂` deep inside a region the double sum is exponentially
small in the depth.
-/

@[expose] public section

open MeasureTheory Set Matrix

namespace Balaban.Green

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The resolvent identity `A⁻¹ - B⁻¹ = A⁻¹ (B - A) B⁻¹` for invertible `A`, `B`. -/
theorem inv_sub_inv_eq_mul {A B : Matrix ι ι ℂ} (hA : IsUnit A) (hB : IsUnit B) :
    A⁻¹ - B⁻¹ = A⁻¹ * (B - A) * B⁻¹ := by
  have hA' : A⁻¹ * A = 1 := Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 hA)
  have hB' : B * B⁻¹ = 1 := Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hB)
  rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc, hB', Matrix.mul_one, hA', Matrix.one_mul]

omit [DecidableEq ι] in
/-- The entry of a triple product is bounded by the double sum of the entry bounds. -/
theorem norm_mul_mul_apply_le (R₁ E R₂ : Matrix ι ι ℂ) {f₁ f₂ η : ι → ι → ℝ}
    (h₁ : ∀ x u, ‖R₁ x u‖ ≤ f₁ x u) (hE : ∀ u v, ‖E u v‖ ≤ η u v)
    (h₂ : ∀ v y, ‖R₂ v y‖ ≤ f₂ v y) (x y : ι) :
    ‖(R₁ * E * R₂) x y‖ ≤ ∑ u, ∑ v, f₁ x u * η u v * f₂ v y := by
  rw [Matrix.mul_apply]
  calc ‖∑ v, (R₁ * E) x v * R₂ v y‖ ≤ ∑ v, ‖(R₁ * E) x v‖ * ‖R₂ v y‖ := by
        refine (norm_sum_le _ _).trans (le_of_eq ?_)
        exact Finset.sum_congr rfl fun v _ => norm_mul _ _
    _ ≤ ∑ v, (∑ u, f₁ x u * η u v) * f₂ v y := by
        refine Finset.sum_le_sum fun v _ => ?_
        refine mul_le_mul ?_ (h₂ v y) (norm_nonneg _) ?_
        · rw [Matrix.mul_apply]
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun u _ => ?_)
          rw [norm_mul]
          exact mul_le_mul (h₁ x u) (hE u v) (norm_nonneg _) ((norm_nonneg _).trans (h₁ x u))
        · exact Finset.sum_nonneg fun u _ => mul_nonneg ((norm_nonneg _).trans (h₁ x u))
            ((norm_nonneg _).trans (hE u v))
    _ = ∑ u, ∑ v, f₁ x u * η u v * f₂ v y := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun u _ => ?_
        rw [Finset.sum_mul]

variable [PseudoMetricSpace ι]

/-- **The comparison of the inverse square roots from resolvent bounds** (shared core): if the
resolvents of `U₁`, `U₂` are invertible with `‖(U_i + t)⁻¹ x y‖ ≤ 2/(γ + t) e^{-ρ |x - y|}` for all
`t ≥ 0`, and `‖U₁ u v - U₂ u v‖ ≤ η(u, v)`, then
`‖sqrtMat U₁ x y - sqrtMat U₂ x y‖ ≤ 4/(γ √γ) ∑_{u,v} e^{-ρ |x - u|} η(u, v) e^{-ρ |v - y|}`. -/
theorem norm_sqrtMat_sub_le_of_resolvent [Nonempty ι] {U₁ U₂ : Matrix ι ι ℂ} {γ ρ : ℝ}
    (hγ : 0 < γ)
    (hu₁ : ∀ t : ℝ, 0 ≤ t → IsUnit (U₁ + (t : ℂ) • (1 : Matrix ι ι ℂ)))
    (hu₂ : ∀ t : ℝ, 0 ≤ t → IsUnit (U₂ + (t : ℂ) • (1 : Matrix ι ι ℂ)))
    (hres₁ : ∀ t : ℝ, 0 ≤ t → ∀ x y : ι,
      ‖(U₁ + (t : ℂ) • (1 : Matrix ι ι ℂ))⁻¹ x y‖ ≤ 2 / (γ + t) * Real.exp (-ρ * dist x y))
    (hres₂ : ∀ t : ℝ, 0 ≤ t → ∀ x y : ι,
      ‖(U₂ + (t : ℂ) • (1 : Matrix ι ι ℂ))⁻¹ x y‖ ≤ 2 / (γ + t) * Real.exp (-ρ * dist x y))
    {η : ι → ι → ℝ} (hη : ∀ u v, ‖U₁ u v - U₂ u v‖ ≤ η u v) (x y : ι) :
    ‖Localization.sqrtMat U₁ x y - Localization.sqrtMat U₂ x y‖ ≤
      4 / (γ * Real.sqrt γ) *
        ∑ u, ∑ v, Real.exp (-ρ * dist x u) * η u v * Real.exp (-ρ * dist v y) := by
  set S : ℝ := ∑ u, ∑ v, Real.exp (-ρ * dist x u) * η u v * Real.exp (-ρ * dist v y) with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun u _ => Finset.sum_nonneg fun v _ =>
    mul_nonneg (mul_nonneg (Real.exp_pos _).le ((norm_nonneg _).trans (hη u v)))
      (Real.exp_pos _).le
  have hok₁ : Localization.ResOK U₁ := fun t ht => by rw [add_comm]; exact hu₁ t ht
  have hok₂ : Localization.ResOK U₂ := fun t ht => by rw [add_comm]; exact hu₂ t ht
  have hint₁ := Localization.integrable_sqrt_entry hok₁ x y
  have hint₂ := Localization.integrable_sqrt_entry hok₂ x y
  have hentry : ∀ U : Matrix ι ι ℂ, Localization.sqrtMat U x y = ((1 / Real.pi : ℝ) : ℂ) *
      ∫ t in Ioi (0 : ℝ), ((t ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
        ((t : ℂ) • (1 : Matrix ι ι ℂ) + U)⁻¹ x y := fun U => by
    simp [Localization.sqrtMat, Localization.intMat, Matrix.smul_apply]
  -- the pointwise bound of the difference of the integrands
  have hpt : ∀ t ∈ Ioi (0 : ℝ), ‖((t ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
        ((t : ℂ) • (1 : Matrix ι ι ℂ) + U₁)⁻¹ x y - ((t ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
        ((t : ℂ) • (1 : Matrix ι ι ℂ) + U₂)⁻¹ x y‖ ≤
      4 * S * (t ^ (-(1 / 2 : ℝ)) * ((γ + t)⁻¹) ^ 2) := by
    intro t ht
    have ht0 : 0 < t := mem_Ioi.1 ht
    have h3 : 0 < t ^ (-(1 / 2 : ℝ)) := Real.rpow_pos_of_pos ht0 _
    have hU1 := hu₁ t ht0.le
    have hU2 := hu₂ t ht0.le
    rw [add_comm] at hU1 hU2
    have hid := inv_sub_inv_eq_mul hU1 hU2
    have hdiff : ((t : ℂ) • (1 : Matrix ι ι ℂ) + U₂) - ((t : ℂ) • (1 : Matrix ι ι ℂ) + U₁) =
        U₂ - U₁ := by abel
    rw [hdiff] at hid
    have hb : ‖(((t : ℂ) • (1 : Matrix ι ι ℂ) + U₁)⁻¹ - ((t : ℂ) • (1 : Matrix ι ι ℂ) + U₂)⁻¹)
        x y‖ ≤ ∑ u, ∑ v, (2 / (γ + t) * Real.exp (-ρ * dist x u)) * η u v *
          (2 / (γ + t) * Real.exp (-ρ * dist v y)) := by
      rw [hid]
      refine norm_mul_mul_apply_le _ _ _
        (f₁ := fun x u => 2 / (γ + t) * Real.exp (-ρ * dist x u))
        (f₂ := fun v y => 2 / (γ + t) * Real.exp (-ρ * dist v y)) (η := η)
        (fun x u => ?_) (fun u v => ?_) (fun v y => ?_) x y
      · have := hres₁ t ht0.le x u; rwa [add_comm] at this
      · rw [Matrix.sub_apply, norm_sub_rev]; exact hη u v
      · have := hres₂ t ht0.le v y; rwa [add_comm] at this
    have hsum : ∑ u, ∑ v, (2 / (γ + t) * Real.exp (-ρ * dist x u)) * η u v *
        (2 / (γ + t) * Real.exp (-ρ * dist v y)) = 4 * ((γ + t)⁻¹) ^ 2 * S := by
      rw [hS, Finset.mul_sum]
      refine Finset.sum_congr rfl fun u _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun v _ => ?_
      rw [div_eq_mul_inv]; ring
    rw [← mul_sub, norm_mul, Complex.norm_real, Real.norm_of_nonneg h3.le, ← Matrix.sub_apply]
    calc t ^ (-(1 / 2 : ℝ)) * ‖(((t : ℂ) • (1 : Matrix ι ι ℂ) + U₁)⁻¹ -
          ((t : ℂ) • (1 : Matrix ι ι ℂ) + U₂)⁻¹) x y‖
        ≤ t ^ (-(1 / 2 : ℝ)) * (4 * ((γ + t)⁻¹) ^ 2 * S) :=
          mul_le_mul_of_nonneg_left (hb.trans (le_of_eq hsum)) h3.le
      _ = 4 * S * (t ^ (-(1 / 2 : ℝ)) * ((γ + t)⁻¹) ^ 2) := by ring
  have hgint : Integrable (fun t : ℝ => 4 * S * (t ^ (-(1 / 2 : ℝ)) * ((γ + t)⁻¹) ^ 2))
      (volume.restrict (Ioi (0 : ℝ))) :=
    (Localization.integrableOn_rpow_inv_add_sq hγ).const_mul _
  have hbound := norm_integral_le_of_norm_le hgint
    ((ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall hpt))
  rw [integral_const_mul] at hbound
  have hI := Localization.integral_rpow_inv_add_sq_le hγ
  have hpi : 0 < Real.pi := Real.pi_pos
  have hsq : 0 < Real.sqrt γ := Real.sqrt_pos.2 hγ
  rw [hentry U₁, hentry U₂, ← mul_sub, ← integral_sub hint₁ hint₂, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg (by positivity)]
  calc 1 / Real.pi * ‖∫ t in Ioi (0 : ℝ), (((t ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
        ((t : ℂ) • (1 : Matrix ι ι ℂ) + U₁)⁻¹ x y - ((t ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
        ((t : ℂ) • (1 : Matrix ι ι ℂ) + U₂)⁻¹ x y)‖
      ≤ 1 / Real.pi * (4 * S * ∫ t in Ioi (0 : ℝ), t ^ (-(1 / 2 : ℝ)) * ((γ + t)⁻¹) ^ 2) :=
        mul_le_mul_of_nonneg_left hbound (by positivity)
    _ ≤ 1 / Real.pi * (4 * S * (γ⁻¹ * (Real.pi / Real.sqrt γ))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hI (by positivity)) (by positivity)
    _ = 4 / (γ * Real.sqrt γ) * S := by
        field_simp

/-- **The comparison of the inverse square roots of two coercive matrices** (shared core): for
`U₁`, `U₂` coercive with gap `γ₀`, entries bounded by `c₀ e^{-δ₀ |x - y|}` and ball sums
`∑_y e^{-(δ₀/4)|x - y|} ≤ κ`, and `‖U₁ u v - U₂ u v‖ ≤ η(u, v)`,
`‖sqrtMat U₁ x y - sqrtMat U₂ x y‖ ≤ 4/(γ₀ √γ₀) ∑_{u,v} e^{-ρ |x - u|} η(u, v) e^{-ρ |v - y|}`,
`ρ = ctRate c₀ δ₀ γ₀ κ` (Combes–Thomas, `combesThomas`). -/
theorem norm_sqrtMat_sub_le [Nonempty ι] {U₁ U₂ : Matrix ι ι ℂ} {c₀ δ₀ γ₀ κ : ℝ}
    (hc : 0 ≤ c₀) (hδ : 0 < δ₀) (hγ : 0 < γ₀) (hκ : 0 ≤ κ)
    (hK : ∀ x : ι, ∑ y, Real.exp (-(δ₀ / 4) * dist x y) ≤ κ)
    (h₁ : ∀ x y, ‖U₁ x y‖ ≤ c₀ * Real.exp (-δ₀ * dist x y))
    (h₂ : ∀ x y, ‖U₂ x y‖ ≤ c₀ * Real.exp (-δ₀ * dist x y))
    (hc₁ : IsCoercive U₁ γ₀) (hc₂ : IsCoercive U₂ γ₀)
    {η : ι → ι → ℝ} (hη : ∀ u v, ‖U₁ u v - U₂ u v‖ ≤ η u v) (x y : ι) :
    ‖Localization.sqrtMat U₁ x y - Localization.sqrtMat U₂ x y‖ ≤
      4 / (γ₀ * Real.sqrt γ₀) * ∑ u, ∑ v, Real.exp (-(ctRate c₀ δ₀ γ₀ κ) * dist x u) * η u v *
        Real.exp (-(ctRate c₀ δ₀ γ₀ κ) * dist v y) := by
  have hres : ∀ {U : Matrix ι ι ℂ}, (∀ x y, ‖U x y‖ ≤ c₀ * Real.exp (-δ₀ * dist x y)) →
      IsCoercive U γ₀ → ∀ t : ℝ, 0 ≤ t → ∀ x y : ι,
        ‖(U + (t : ℂ) • (1 : Matrix ι ι ℂ))⁻¹ x y‖ ≤
          2 / (γ₀ + t) * Real.exp (-(ctRate c₀ δ₀ γ₀ κ) * dist x y) := by
    intro U hU hcU t ht x y
    have := (combesThomas hc hδ hγ hκ hU hK hcU ht).2 x y
    rwa [div_eq_mul_inv]
  exact norm_sqrtMat_sub_le_of_resolvent hγ
    (fun t ht => (combesThomas hc hδ hγ hκ h₁ hK hc₁ ht).1)
    (fun t ht => (combesThomas hc hδ hγ hκ h₂ hK hc₂ ht).1)
    (hres h₁ hc₁) (hres h₂ hc₂) hη x y

/-- The geometric mean of two entrywise bounds of a difference. -/
theorem le_sqrt_mul_of_le_of_le {X b₁ b₂ : ℝ} (hX : 0 ≤ X) (h₁ : X ≤ b₁) (h₂ : X ≤ b₂) :
    X ≤ Real.sqrt (b₁ * b₂) :=
  Real.le_sqrt_of_sq_le (by nlinarith)

/-- **Comparison deep inside** (shared core): if moreover `U₁ = U₂` up to
`B e^{-(δ₀/2)(τ(u) + τ(v))}` with the depth `τ(u) = max 0 (m - |x₀ - u|)` below the centre `x₀`,
then for `0 < ε ≤ min(ρ, δ₀)`,
`‖sqrtMat U₁ (x₀, y) - sqrtMat U₂ (x₀, y)‖ ≤ 4/(γ₀ √γ₀) (2 B c₀)^{1/2} κ₁ κ e^{-(ε/4) m} e^{-(ε/4)|x₀ - y|}`,
`κ₁` a ball-sum bound at the rate `ρ/4`, `ρ = ctRate c₀ δ₀ γ₀ κ`. -/
theorem norm_sqrtMat_sub_le_of_deep [Nonempty ι] {U₁ U₂ : Matrix ι ι ℂ} {c₀ δ₀ γ₀ κ κ₁ : ℝ}
    (hc : 0 ≤ c₀) (hδ : 0 < δ₀) (hγ : 0 < γ₀) (hκ : 0 ≤ κ)
    (hK : ∀ x : ι, ∑ y, Real.exp (-(δ₀ / 4) * dist x y) ≤ κ)
    (hK₁ : ∀ x : ι, ∑ y, Real.exp (-(ctRate c₀ δ₀ γ₀ κ / 4) * dist x y) ≤ κ₁)
    (h₁ : ∀ x y, ‖U₁ x y‖ ≤ c₀ * Real.exp (-δ₀ * dist x y))
    (h₂ : ∀ x y, ‖U₂ x y‖ ≤ c₀ * Real.exp (-δ₀ * dist x y))
    (hc₁ : IsCoercive U₁ γ₀) (hc₂ : IsCoercive U₂ γ₀) {B : ℝ} (hB : 0 ≤ B) (x₀ : ι) (m : ℝ)
    (hη : ∀ u v, ‖U₁ u v - U₂ u v‖ ≤
      B * Real.exp (-(δ₀ / 2 * (max 0 (m - dist x₀ u) + max 0 (m - dist x₀ v)))))
    {ε : ℝ} (hε0 : 0 < ε) (hερ : ε ≤ ctRate c₀ δ₀ γ₀ κ) (hεδ : ε ≤ δ₀) (y : ι) :
    ‖Localization.sqrtMat U₁ x₀ y - Localization.sqrtMat U₂ x₀ y‖ ≤
      4 / (γ₀ * Real.sqrt γ₀) * (Real.sqrt (2 * B * c₀) * κ₁ * κ) *
        (Real.exp (-(ε / 4 * m)) * Real.exp (-(ε / 4 * dist x₀ y))) := by
  set ρ := ctRate c₀ δ₀ γ₀ κ with hρ
  set τ : ι → ℝ := fun u => max 0 (m - dist x₀ u) with hτ
  set η : ι → ι → ℝ := fun u v => Real.sqrt (2 * B * c₀) *
    (Real.exp (-(δ₀ / 4 * (τ u + τ v))) * Real.exp (-(δ₀ / 2 * dist u v))) with hηdef
  have hη' : ∀ u v, ‖U₁ u v - U₂ u v‖ ≤ η u v := by
    intro u v
    have hb₂ : ‖U₁ u v - U₂ u v‖ ≤ 2 * c₀ * Real.exp (-δ₀ * dist u v) :=
      (norm_sub_le _ _).trans (by linarith [h₁ u v, h₂ u v])
    refine (le_sqrt_mul_of_le_of_le (norm_nonneg _) (hη u v) hb₂).trans (le_of_eq ?_)
    have e : B * Real.exp (-(δ₀ / 2 * (τ u + τ v))) * (2 * c₀ * Real.exp (-δ₀ * dist u v)) =
        (2 * B * c₀) * Real.exp (-(δ₀ / 2 * (τ u + τ v)) + -δ₀ * dist u v) := by
      rw [Real.exp_add]; ring
    rw [e, Real.sqrt_mul (by positivity), ← Real.exp_half]
    simp only [hηdef]
    rw [← Real.exp_add]
    congr 2
    ring
  have hmain := norm_sqrtMat_sub_le hc hδ hγ hκ hK h₁ h₂ hc₁ hc₂ hη' x₀ y
  rw [← hρ] at hmain
  have h4 : 0 ≤ 4 / (γ₀ * Real.sqrt γ₀) := by positivity
  rw [mul_assoc]
  refine hmain.trans (mul_le_mul_of_nonneg_left ?_ h4)
  have hterm : ∀ u v, Real.exp (-ρ * dist x₀ u) * η u v * Real.exp (-ρ * dist v y) ≤
      Real.sqrt (2 * B * c₀) * (Real.exp (-(ε / 4 * m)) * Real.exp (-(ε / 4 * dist x₀ y))) *
        (Real.exp (-(ρ / 4) * dist x₀ u) * Real.exp (-(δ₀ / 4) * dist u v)) := by
    intro u v
    have ht : dist x₀ y ≤ dist x₀ u + dist u v + dist v y := by
      linarith [dist_triangle x₀ v y, dist_triangle x₀ u v]
    have hτu : m - dist x₀ u ≤ τ u := le_max_right _ _
    have hτu0 : 0 ≤ τ u := le_max_left _ _
    have hτv0 : 0 ≤ τ v := le_max_left _ _
    have ha := dist_nonneg (x := x₀) (y := u)
    have hb := dist_nonneg (x := u) (y := v)
    have hc' := dist_nonneg (x := v) (y := y)
    have e1 : Real.exp (-ρ * dist x₀ u) * η u v * Real.exp (-ρ * dist v y) =
        Real.sqrt (2 * B * c₀) * Real.exp (-ρ * dist x₀ u + -(δ₀ / 4 * (τ u + τ v)) +
          -(δ₀ / 2 * dist u v) + -ρ * dist v y) := by
      simp only [hηdef, Real.exp_add]; ring
    have e2 : Real.sqrt (2 * B * c₀) * (Real.exp (-(ε / 4 * m)) * Real.exp (-(ε / 4 * dist x₀ y))) *
        (Real.exp (-(ρ / 4) * dist x₀ u) * Real.exp (-(δ₀ / 4) * dist u v)) =
        Real.sqrt (2 * B * c₀) * Real.exp (-(ε / 4 * m) + -(ε / 4 * dist x₀ y) +
          -(ρ / 4) * dist x₀ u + -(δ₀ / 4) * dist u v) := by
      simp only [Real.exp_add]; ring
    rw [e1, e2]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (Real.sqrt_nonneg _)
    nlinarith [mul_le_mul_of_nonneg_left ht (by linarith : (0 : ℝ) ≤ ε / 4),
      mul_le_mul_of_nonneg_left hτu (by linarith : (0 : ℝ) ≤ ε / 4),
      mul_le_mul_of_nonneg_right hερ ha, mul_le_mul_of_nonneg_right hερ hc',
      mul_le_mul_of_nonneg_right hεδ hb, mul_le_mul_of_nonneg_right hεδ hτu0,
      mul_nonneg hδ.le hτv0]
  have hC0 : 0 ≤ Real.sqrt (2 * B * c₀) * (Real.exp (-(ε / 4 * m)) *
      Real.exp (-(ε / 4 * dist x₀ y))) := by positivity
  calc ∑ u, ∑ v, Real.exp (-ρ * dist x₀ u) * η u v * Real.exp (-ρ * dist v y)
      ≤ ∑ u, ∑ v, Real.sqrt (2 * B * c₀) *
          (Real.exp (-(ε / 4 * m)) * Real.exp (-(ε / 4 * dist x₀ y))) *
          (Real.exp (-(ρ / 4) * dist x₀ u) * Real.exp (-(δ₀ / 4) * dist u v)) :=
        Finset.sum_le_sum fun u _ => Finset.sum_le_sum fun v _ => hterm u v
    _ = Real.sqrt (2 * B * c₀) * (Real.exp (-(ε / 4 * m)) * Real.exp (-(ε / 4 * dist x₀ y))) *
          ∑ u, Real.exp (-(ρ / 4) * dist x₀ u) * ∑ v, Real.exp (-(δ₀ / 4) * dist u v) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun u _ => ?_
        rw [Finset.mul_sum, Finset.mul_sum]
    _ ≤ Real.sqrt (2 * B * c₀) * (Real.exp (-(ε / 4 * m)) * Real.exp (-(ε / 4 * dist x₀ y))) *
          (κ₁ * κ) := by
        refine mul_le_mul_of_nonneg_left ?_ hC0
        calc ∑ u, Real.exp (-(ρ / 4) * dist x₀ u) * ∑ v, Real.exp (-(δ₀ / 4) * dist u v)
            ≤ ∑ u, Real.exp (-(ρ / 4) * dist x₀ u) * κ :=
              Finset.sum_le_sum fun u _ =>
                mul_le_mul_of_nonneg_left (hK u) (Real.exp_pos _).le
          _ = (∑ u, Real.exp (-(ρ / 4) * dist x₀ u)) * κ := by rw [Finset.sum_mul]
          _ ≤ κ₁ * κ := mul_le_mul_of_nonneg_right (hK₁ x₀) hκ
    _ = _ := by ring

end Balaban.Green
