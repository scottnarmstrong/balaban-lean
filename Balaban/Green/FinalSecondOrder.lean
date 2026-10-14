/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Green.FinalSourceAmplitude
public import Balaban.Inhabited.RootBoundsArith
public import Balaban.Inhabited.ObsPrefactorScale

/-!
# The second-order bound for the last integral (W812)

Leaves 1, 2 of `notes/phase1/FINALAMP2.md`.

* `norm_sub_linear_le_of_ball`: second-order Schwarz in one variable.  If `h` is analytic on
  `{|t| < T}`, `h 0 = 0` and `‖h‖ ≤ B` there, then `‖h t - t h'(0)‖ ≤ 2 B (|t|/T)^2`.
* `norm_sub_fderiv_le_of_polydisc`: the same on a polydisc: `‖F w - F c - F'(c)(w - c)‖ ≤
  2 B (R/T)^2` for `‖F - F c‖ ≤ B` on the polydisc of radius `T`.
* `betaK_inv_mul_sq_cut_le`: the arithmetic of leaf 4: for the cutoff `ρ(β) = A (log β)^q` and
  `β_k = β₀ L^{k(d-2)}`, `β_k^{-1} ρ(β_k)^2 ≤ c₉ L^{-(k+1)((d-2)/2+δ)}` for every `k`.
* `cutoffInteraction_final_phys_sub2`: the cutoff integral of `F - F(φ₀)` equals the cutoff
  integral of the second-order remainder, because the linear part is odd in `ψ` and `γ`, the box
  are symmetric; its coefficients are bounded by `2 B (R₁/Rphys)^2 γ(box) e^{-(κ-1)|C|}`.
-/

@[expose] public section

open Finset Matrix MeasureTheory Set Filter Metric

namespace Balaban.Green

open Balaban.Localization Balaban.Analysis

section Schwarz2

/-- **Second-order Schwarz in one variable.** -/
theorem norm_sub_linear_le_of_ball {h : ℂ → ℂ} {T B : ℝ} (hT : 0 < T)
    (hd : DifferentiableOn ℂ h (ball (0 : ℂ) T)) (h0 : h 0 = 0)
    (hB : ∀ t ∈ ball (0 : ℂ) T, ‖h t‖ ≤ B) {t : ℂ} (ht : ‖t‖ < T) :
    ‖h t - t * deriv h 0‖ ≤ 2 * B * (‖t‖ / T) ^ 2 := by
  have hball : ball (0 : ℂ) T ∈ nhds (0 : ℂ) := ball_mem_nhds _ hT
  have hh0 : DifferentiableAt ℂ h 0 := hd.differentiableAt hball
  have hmaps : Set.MapsTo h (ball (0 : ℂ) T) (closedBall (h 0) B) := by
    intro τ hτ
    rw [mem_closedBall, h0, dist_zero_right]
    exact hB τ hτ
  set a : ℂ := deriv h 0 with ha
  have haB : ‖a‖ ≤ B / T := Complex.norm_deriv_le_div_of_mapsTo_ball hd hmaps hT
  have hB0 : 0 ≤ B := by
    have := hB 0 (mem_ball_self hT)
    exact (norm_nonneg _).trans this
  set g : ℂ → ℂ := fun τ => h τ - τ * a with hg
  have hgd : DifferentiableOn ℂ g (ball (0 : ℂ) T) :=
    hd.sub (differentiableOn_id.mul_const a)
  have hg0 : g 0 = 0 := by simp [hg, h0]
  have hgB : ∀ τ ∈ ball (0 : ℂ) T, ‖g τ‖ ≤ 2 * B := by
    intro τ hτ
    have hτ' : ‖τ‖ < T := by simpa using hτ
    calc ‖g τ‖ ≤ ‖h τ‖ + ‖τ * a‖ := norm_sub_le _ _
      _ ≤ B + ‖τ‖ * (B / T) := by
          refine add_le_add (hB τ hτ) ?_
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_left haB (norm_nonneg _)
      _ ≤ B + 1 * B := by
          refine add_le_add le_rfl ?_
          have : ‖τ‖ * (B / T) = (‖τ‖ / T) * B := by ring
          rw [this]
          exact mul_le_mul_of_nonneg_right
            (by rw [div_le_one hT]; exact hτ'.le) hB0
      _ = 2 * B := by ring
  have hgmaps : Set.MapsTo g (ball (0 : ℂ) T) (closedBall (g 0) (2 * B)) := by
    intro τ hτ
    rw [mem_closedBall, hg0, dist_zero_right]
    exact hgB τ hτ
  have hdg0 : deriv g 0 = 0 := by
    have h1 : HasDerivAt h a 0 := hh0.hasDerivAt
    have h2 : HasDerivAt (fun τ : ℂ => τ * a) (1 * a) 0 := (hasDerivAt_id 0).mul_const a
    have h3 : HasDerivAt g (a - 1 * a) 0 := h1.sub h2
    rw [h3.deriv]; ring
  set q : ℂ → ℂ := dslope g 0 with hq
  have hqd : DifferentiableOn ℂ q (ball (0 : ℂ) T) :=
    (Complex.differentiableOn_dslope hball).2 hgd
  have hq0 : q 0 = 0 := by simp [hq, dslope_same, hdg0]
  have hqB : ∀ τ ∈ ball (0 : ℂ) T, ‖q τ‖ ≤ 2 * B / T := fun τ hτ =>
    Complex.norm_dslope_le_div_of_mapsTo_ball hgd hgmaps hτ
  have hqmaps : Set.MapsTo q (ball (0 : ℂ) T) (closedBall (q 0) (2 * B / T)) := by
    intro τ hτ
    rw [mem_closedBall, hq0, dist_zero_right]
    exact hqB τ hτ
  have htb : t ∈ ball (0 : ℂ) T := by simpa using ht
  have h2 := Complex.dist_le_div_mul_dist_of_mapsTo_ball hqd hqmaps htb
  rw [hq0, dist_zero_right, dist_zero_right] at h2
  have hgt : g t = t * q t := by
    have := sub_smul_dslope g 0 t
    simpa [hg0, smul_eq_mul] using this.symm
  have : h t - t * a = g t := rfl
  rw [this, hgt, norm_mul]
  calc ‖t‖ * ‖q t‖ ≤ ‖t‖ * (2 * B / T / T * ‖t‖) :=
        mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
    _ = 2 * B * (‖t‖ / T) ^ 2 := by field_simp

end Schwarz2

section Polydisc

variable {ι : Type*} [Fintype ι]

/-- **Second-order Schwarz on a polydisc.**  `F` analytic on the polydisc of radius `T` around
`c` with `‖F w - F c‖ ≤ B` there; then on the polydisc of radius `R`, `0 < R < T`,
`‖F w - F c - F'(c) (w - c)‖ ≤ 2 B (R/T)^2`. -/
theorem norm_sub_fderiv_le_of_polydisc {c : ι → ℂ} {T R B : ℝ} (hR : 0 < R) (hRT : R < T)
    {F : (ι → ℂ) → ℂ} (hF : AnalyticOnNhd ℂ F (polydisc c (fun _ => T)))
    (hB : ∀ w ∈ polydisc c (fun _ => T), ‖F w - F c‖ ≤ B) {w : ι → ℂ}
    (hw : w ∈ polydisc c (fun _ => R)) :
    ‖F w - F c - fderiv ℂ F c (w - c)‖ ≤ 2 * B * (R / T) ^ 2 := by
  have hT : 0 < T := hR.trans hRT
  set u : ι → ℂ := ((R : ℂ))⁻¹ • (w - c) with hu
  have hRne : (R : ℂ) ≠ 0 := by exact_mod_cast hR.ne'
  have hu1 : ∀ i, ‖u i‖ ≤ 1 := by
    intro i
    have h := hw i
    simp only [hu, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, norm_mul, norm_inv,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR]
    rw [inv_mul_le_iff₀ hR]
    simpa using h.le
  have hmem : ∀ t : ℂ, ‖t‖ < T → c + t • u ∈ polydisc c (fun _ => T) := by
    intro t ht i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_sub_cancel_left, norm_mul]
    calc ‖t‖ * ‖u i‖ ≤ ‖t‖ * 1 := mul_le_mul_of_nonneg_left (hu1 i) (norm_nonneg _)
      _ < T := by simpa using ht
  have hFc : DifferentiableAt ℂ F c :=
    (hF c (fun i => by simpa using hT)).differentiableAt
  have hline : HasDerivAt (fun t : ℂ => c + t • u) u 0 := by
    simpa using ((hasDerivAt_id (0 : ℂ)).smul_const u).const_add c
  have hFl : HasFDerivAt F (fderiv ℂ F c) (c + (0 : ℂ) • u) := by
    simpa using hFc.hasFDerivAt
  have hcomp : HasDerivAt (fun t : ℂ => F (c + t • u)) (fderiv ℂ F c u) 0 :=
    hFl.comp_hasDerivAt (0 : ℂ) hline
  have hder : deriv (fun t : ℂ => F (c + t • u) - F c) 0 = fderiv ℂ F c u :=
    (hcomp.sub_const (F c)).deriv
  have hdiff : DifferentiableOn ℂ (fun t : ℂ => F (c + t • u) - F c) (ball (0 : ℂ) T) := by
    intro t ht
    have hFt : AnalyticAt ℂ F (c + t • u) := hF _ (hmem t (by simpa using ht))
    have hc : AnalyticAt ℂ (fun t : ℂ => c + t • u) t :=
      analyticAt_const.add (analyticAt_id.smul analyticAt_const)
    exact ((AnalyticAt.comp (g := F) (f := fun t : ℂ => c + t • u) hFt hc).sub
      analyticAt_const).differentiableAt.differentiableWithinAt
  have key := norm_sub_linear_le_of_ball (h := fun t : ℂ => F (c + t • u) - F c) hT hdiff
    (by simp) (fun t ht => hB _ (hmem t (by simpa using ht)))
    (t := (R : ℂ)) (by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR]; exact hRT)
  rw [hder] at key
  have he : c + (R : ℂ) • u = w := by
    rw [hu, smul_smul, mul_inv_cancel₀ hRne, one_smul]; abel
  have he2 : w - c = (R : ℂ) • u := by rw [← he]; abel
  rw [he] at key
  rw [he2, map_smul, smul_eq_mul]
  simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR] using key

end Polydisc

section Symmetry

variable {ι : Type*} [Fintype ι]

omit [Fintype ι] in
/-- The box `{ψ | ∀ y, |ψ y| ≤ ρ}` is compact. -/
theorem isCompact_box (ρ : ℝ) [Finite ι] : IsCompact {ψ : ι → ℝ | ∀ y, |ψ y| ≤ ρ} := by
  have : {ψ : ι → ℝ | ∀ y, |ψ y| ≤ ρ} = Set.pi Set.univ (fun _ : ι => Icc (-ρ) ρ) := by
    ext ψ; simp only [Set.mem_ofPred_eq, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Icc,
      abs_le]
  rw [this]; exact isCompact_univ_pi fun _ => isCompact_Icc

/-- An odd function integrates to zero over the box against a measure symmetric under
`ψ ↦ -ψ`. -/
theorem setIntegral_box_odd_eq_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {γ : Measure (ι → ℝ)} (hsym : Measure.map Neg.neg γ = γ) {ρ : ℝ} {f : (ι → ℝ) → E}
    (hf : ∀ ψ, f (-ψ) = -f ψ) :
    ∫ ψ in {ψ : ι → ℝ | ∀ y, |ψ y| ≤ ρ}, f ψ ∂γ = 0 := by
  have : γ.IsNegInvariant := ⟨hsym⟩
  set S : Set (ι → ℝ) := {ψ : ι → ℝ | ∀ y, |ψ y| ≤ ρ} with hS
  have hSm : MeasurableSet S := (isCompact_box ρ).isClosed.measurableSet
  have hSneg : ∀ ψ, (-ψ ∈ S ↔ ψ ∈ S) := by
    intro ψ
    simp only [hS, Set.mem_ofPred_eq, Pi.neg_apply, abs_neg]
  have h1 : ∫ ψ in S, f ψ ∂γ = ∫ ψ, S.indicator f ψ ∂γ := (integral_indicator hSm).symm
  have h2 : ∀ ψ, S.indicator f (-ψ) = -S.indicator f ψ := by
    intro ψ
    by_cases h : ψ ∈ S
    · rw [Set.indicator_of_mem h, Set.indicator_of_mem ((hSneg ψ).2 h), hf]
    · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (fun h' => h ((hSneg ψ).1 h')),
        neg_zero]
  have h3 : ∫ ψ, S.indicator f (-ψ) ∂γ = ∫ ψ, S.indicator f ψ ∂γ :=
    integral_neg_eq_self (S.indicator f) γ
  simp only [h2, integral_neg] at h3
  rw [h1]
  have : (2 : ℝ) • ∫ ψ, S.indicator f ψ ∂γ = 0 := by
    rw [two_smul]; nth_rewrite 1 [← h3]; exact neg_add_cancel _
  rcases smul_eq_zero.1 this with h | h
  · norm_num at h
  · exact h

end Symmetry

section Remainder

variable {ι : Type*} [Fintype ι]

/-- The linear part of the integrand drops out: for a function `F` differentiable at `φ₀`, a
finite measure on the box, a symmetric `γ` and any matrix `K`,
`∫_{box} (F (φ₀ + c K ψ) - F φ₀) dγ = ∫_{box} (F (φ₀ + c K ψ) - F φ₀ - F'(φ₀) (c K ψ)) dγ`. -/
theorem setIntegral_sub_eq_remainder {γ : Measure (ι → ℝ)} (hsym : Measure.map Neg.neg γ = γ)
    {ρ : ℝ} (hγ : γ {ψ : ι → ℝ | ∀ y, |ψ y| ≤ ρ} < ⊤) (F : (ι → ℂ) → ℂ) (φ₀ : ι → ℂ)
    (c : ℂ) (K : ι → ι → ℂ) :
    ∫ ψ in {ψ : ι → ℝ | ∀ y, |ψ y| ≤ ρ},
        (F (fun x => φ₀ x + c * ∑ y, K x y * ((ψ y : ℝ) : ℂ)) - F φ₀) ∂γ =
      ∫ ψ in {ψ : ι → ℝ | ∀ y, |ψ y| ≤ ρ},
        (F (fun x => φ₀ x + c * ∑ y, K x y * ((ψ y : ℝ) : ℂ)) - F φ₀ -
          fderiv ℂ F φ₀ (fun x => c * ∑ y, K x y * ((ψ y : ℝ) : ℂ))) ∂γ := by
  set S : Set (ι → ℝ) := {ψ : ι → ℝ | ∀ y, |ψ y| ≤ ρ} with hS
  have hSm : MeasurableSet S := (isCompact_box ρ).isClosed.measurableSet
  set ℓ : (ι → ℝ) → ℂ := fun ψ =>
    fderiv ℂ F φ₀ (fun x => c * ∑ y, K x y * ((ψ y : ℝ) : ℂ)) with hℓ
  have hℓc : Continuous ℓ := by
    refine (fderiv ℂ F φ₀).continuous.comp ?_
    refine continuous_pi fun x => ?_
    refine continuous_const.mul (continuous_finsetSum _ fun y _ => ?_)
    exact continuous_const.mul (Complex.continuous_ofReal.comp (continuous_apply y))
  have hℓi : IntegrableOn ℓ S γ :=
    hℓc.continuousOn.integrableOn_of_subset_isCompact (isCompact_box ρ) hSm subset_rfl hγ.ne
  have hodd : ∀ ψ, ℓ (-ψ) = -ℓ ψ := by
    intro ψ
    have : (fun x => c * ∑ y, K x y * (((-ψ) y : ℝ) : ℂ)) =
        -(fun x => c * ∑ y, K x y * ((ψ y : ℝ) : ℂ)) := by
      funext x
      simp [Finset.sum_neg_distrib, mul_neg]
    simp only [hℓ, this, map_neg]
  have h0 : ∫ ψ in S, ℓ ψ ∂γ = 0 := setIntegral_box_odd_eq_zero hsym hodd
  set g : (ι → ℝ) → ℂ := fun ψ =>
    F (fun x => φ₀ x + c * ∑ y, K x y * ((ψ y : ℝ) : ℂ)) - F φ₀ -
      fderiv ℂ F φ₀ (fun x => c * ∑ y, K x y * ((ψ y : ℝ) : ℂ)) with hg
  have hsplit : ∀ ψ, F (fun x => φ₀ x + c * ∑ y, K x y * ((ψ y : ℝ) : ℂ)) - F φ₀ =
      g ψ + ℓ ψ := fun ψ => by simp [hg, hℓ]
  simp_rw [hsplit]
  by_cases hgi : IntegrableOn g S γ
  · rw [integral_add hgi hℓi, h0, add_zero]
  · have : ¬ IntegrableOn (fun ψ => g ψ + ℓ ψ) S γ := fun h => hgi (by
      refine (h.sub hℓi).congr_fun (fun ψ _ => ?_) hSm
      simp)
    rw [integral_undef hgi, integral_undef this]

end Remainder

section Cutoff2

variable {d N₀ M : ℕ} [NeZero N₀] {L k : ℕ} [NeZero L] {v a : ℝ}

/-- **The cutoff interaction of the `g`-dependent part, second order.**  As
`cutoffInteraction_final_phys_sub`, with the same hypotheses and the extra hypothesis that `γ`
is symmetric, `Measure.map Neg.neg γ = γ`.  The linear part of `F - F(φ₀)` is odd in `ψ`, so it
integrates to zero over the symmetric box, for every `s` and for the final operator, and the
cutoff integral `J` of `F - F(φ₀)` equals the cutoff integral of the second-order remainder
`F(w) - F(φ₀) - F'(φ₀)(w - φ₀)`.  Hence `J` is analytic on the polydisc of radius `e^κ`, bounded
there by `2 B (R₁/Rphys)^2 γ(box ρ)`, equals at `s = 1` the average with the square root of the
final operator, is the sum of its coefficients, and
`‖coef J C‖ ≤ 2 B (R₁/Rphys)^2 γ(box ρ) e^{-(κ-1)|C|}`. -/
theorem cutoffInteraction_final_phys_sub2 (hd : 0 < d) (hk : 1 ≤ k) (hv0 : 0 ≤ v)
    (hv1 : v ≤ 1) (ha1 : 1 / 2 ≤ a) (ha2 : a ≤ 2) (hmass : 7 / 8 * ((L : ℝ) ^ 2)⁻¹ < v)
    (hM : 0 < M) {κ : ℝ} (hκ : 1 ≤ κ)
    (hMB : 4 * (pdB d L * Real.exp (pdH d * κ)) ≤ M) (hMκ : 8 * κ * 7 ^ d ≤ pdEps d L * M)
    {γ : Measure (L1Torus d N₀ → ℝ)} (hsym : Measure.map Neg.neg γ = γ)
    {ρ R₁ Rphys B β : ℝ} (hρ : 0 ≤ ρ) (hβ : 0 < β)
    (hγ : γ {ψ : L1Torus d N₀ → ℝ | ∀ y, |ψ y| ≤ ρ} < ⊤)
    (hBR : (4 / 3 * (2 * Real.exp (pdH d * κ) * ballConst d (pdEps d L / 2)) /
      Real.sqrt (finalGap d L)) * (β ^ (-(1 / 2 : ℝ)) * ρ) < R₁) (hR₁ : R₁ < Rphys)
    {F : (L1Torus d N₀ → ℂ) → ℂ} {φ₀ : L1Torus d N₀ → ℂ}
    (hF : AnalyticOnNhd ℂ F (polydisc φ₀ (fun _ => Rphys)))
    (hFB : ∀ w ∈ polydisc φ₀ (fun _ => Rphys), ‖F w - F φ₀‖ ≤ B) :
    let J : (MacIdx d N₀ M → ℂ) → ℂ := fun s =>
      ∫ ψ in {ψ : L1Torus d N₀ → ℝ | ∀ y, |ψ y| ≤ ρ},
        (F (fun x => φ₀ x + ((β ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
          ∑ y, taggedCfin d L N₀ k M v a s x y * ((ψ y : ℝ) : ℂ)) - F φ₀) ∂γ
    AnalyticOnNhd ℂ J (polydisc (0 : MacIdx d N₀ M → ℂ) (fun _ => Real.exp κ)) ∧
    (∀ s ∈ polydisc (0 : MacIdx d N₀ M → ℂ) (fun _ => Real.exp κ),
      ‖J s‖ ≤ 2 * B * (R₁ / Rphys) ^ 2 *
        (γ {ψ : L1Torus d N₀ → ℝ | ∀ y, |ψ y| ≤ ρ}).toReal) ∧
    J (fun _ => 1) = ∫ ψ in {ψ : L1Torus d N₀ → ℝ | ∀ y, |ψ y| ≤ ρ},
        (F (fun x => φ₀ x + ((β ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
          ∑ y, Localization.sqrtMat (finalOp d L N₀ k v a) x y * ((ψ y : ℝ) : ℂ)) - F φ₀) ∂γ ∧
    J (fun _ => 1) = ∑ C : Finset (MacIdx d N₀ M), coef J C ∧
    (∀ C, ‖coef J C‖ ≤ 2 * B * (R₁ / Rphys) ^ 2 *
      (γ {ψ : L1Torus d N₀ → ℝ | ∀ y, |ψ y| ≤ ρ}).toReal * Real.exp (-(κ - 1) * C.card)) := by
  have hcut : 0 ≤ (4 / 3 * (2 * Real.exp (pdH d * κ) * ballConst d (pdEps d L / 2)) /
      Real.sqrt (finalGap d L)) * (β ^ (-(1 / 2 : ℝ)) * ρ) :=
    mul_nonneg (cutConst_pos (L := L) hd κ).le
      (mul_nonneg (Real.rpow_nonneg hβ.le _) hρ)
  have hR0 : 0 < R₁ := lt_of_le_of_lt hcut hBR
  have hsub : polydisc φ₀ (fun _ => R₁) ⊆ polydisc φ₀ (fun _ => Rphys) :=
    fun w hw i => lt_trans (hw i) hR₁
  set G : (L1Torus d N₀ → ℂ) → ℂ := fun w => F w - F φ₀ - fderiv ℂ F φ₀ (w - φ₀) with hG
  have h := cutoffInteraction_final_phys (N₀ := N₀) (M := M) (L := L) (k := k) (v := v) (a := a)
    hd hk hv0 hv1 ha1 ha2 hmass hM hκ hMB hMκ (γ := γ) (ρ := ρ) (Rphys := R₁)
    (B' := 2 * B * (R₁ / Rphys) ^ 2) (β := β) hρ hβ hγ hBR (F := G) (φ₀ := φ₀)
    (fun w hw => ((hF w (hsub hw)).sub analyticAt_const).sub
      (((fderiv ℂ F φ₀).analyticAt _).comp (analyticAt_id.sub analyticAt_const)))
    (fun w hw => norm_sub_fderiv_le_of_polydisc hR0 hR₁ hF hFB hw)
  obtain ⟨h1, h2, h3, h4, -, h6⟩ := h
  have hrem : ∀ K : L1Torus d N₀ → L1Torus d N₀ → ℂ,
      ∫ ψ in {ψ : L1Torus d N₀ → ℝ | ∀ y, |ψ y| ≤ ρ},
        (F (fun x => φ₀ x + ((β ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
          ∑ y, K x y * ((ψ y : ℝ) : ℂ)) - F φ₀) ∂γ =
      ∫ ψ in {ψ : L1Torus d N₀ → ℝ | ∀ y, |ψ y| ≤ ρ},
        G (fun x => φ₀ x + ((β ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
          ∑ y, K x y * ((ψ y : ℝ) : ℂ)) ∂γ := by
    intro K
    rw [setIntegral_sub_eq_remainder hsym hγ F φ₀ _ K]
    refine setIntegral_congr_fun ((isCompact_box ρ).isClosed.measurableSet) fun ψ _ => ?_
    simp only [hG]
    congr 2
    funext x
    simp
  intro J
  have hJ : J = fun s => ∫ ψ in {ψ : L1Torus d N₀ → ℝ | ∀ y, |ψ y| ≤ ρ},
        G (fun x => φ₀ x + ((β ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
          ∑ y, taggedCfin d L N₀ k M v a s x y * ((ψ y : ℝ) : ℂ)) ∂γ :=
    funext fun s => hrem _
  rw [hJ]
  exact ⟨h1, h2, h3.trans (hrem _).symm, h4, h6⟩

end Cutoff2

section Arith

/-- **Leaf 4: the arithmetic of the second-order amplitude.**  Let the cutoff be
`ρ(β) = A (log β)^q` with `q ≥ 0`, let `0 < p < 1`, and let `e = (d-2)/2 + δ` satisfy
`e ≤ p (d-2)`.  There is a constant `C > 0`, depending only on `A, q, p`, such that for
`β₀ ≥ 1`, `c₉ > 0`, `L^e ≤ c₉ β₀^p / C` and every `k`, with `β_k = β₀ L^{k(d-2)}`,
`β_k^{-1} ρ(β_k)^2 ≤ c₉ L^{-(k+1) e}`.  The logarithm is absorbed by the gap `1 - p`. -/
theorem betaK_inv_mul_sq_cut_le {A q p : ℝ} (hq : 0 ≤ q) (hp0 : 0 < p)
    (hp1 : p < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ {d L k : ℕ} {β0 c₉ δ : ℝ}, 3 ≤ d → 2 ≤ L → 1 ≤ β0 → 0 < c₉ →
      ((d : ℝ) - 2) / 2 + δ ≤ p * ((d : ℝ) - 2) →
      (L : ℝ) ^ (((d : ℝ) - 2) / 2 + δ) ≤ c₉ / C * β0 ^ p →
      (Balaban.LargeField.ActionConv.betaK d L k β0)⁻¹ *
          (A * Real.log (Balaban.LargeField.ActionConv.betaK d L k β0) ^ q) ^ 2 ≤
        c₉ * (L : ℝ) ^ (-(((k + 1 : ℕ) : ℝ) * (((d : ℝ) - 2) / 2 + δ))) := by
  obtain ⟨C0, hC0, hlog⟩ := Balaban.Inhabited.log_rpow_le_const_mul_rpow (m := 2 * q)
    (ε := 1 - p) (by linarith) (by linarith)
  refine ⟨A ^ 2 * C0 + 1, by positivity, ?_⟩
  intro d L k β0 c₉ δ hd hL hβ0 hc hpδ hβ
  set C : ℝ := A ^ 2 * C0 + 1 with hCdef
  have hCpos : 0 < C := by positivity
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast (by omega : 1 ≤ L)
  have hbk1 : 1 ≤ Balaban.LargeField.ActionConv.betaK d L k β0 := by
    unfold Balaban.LargeField.ActionConv.betaK
    exact one_le_mul_of_one_le_of_one_le hβ0 (one_le_pow₀ hL1)
  set b : ℝ := Balaban.LargeField.ActionConv.betaK d L k β0 with hb
  have hb0 : 0 < b := by linarith
  have hmain := Balaban.Inhabited.RootBoundsArith.betaK_inv_rpow_le (d := d) (L := L) (k := k)
    (β0 := β0) (c₉ := c₉ / C) (δ := δ) (p := p) hd hL (div_pos hc hCpos) (by linarith)
    hpδ hβ
  have h1 : (A * Real.log b ^ q) ^ 2 = A ^ 2 * Real.log b ^ (2 * q) := by
    rw [mul_pow, ← Real.rpow_natCast (Real.log b ^ q) 2, ← Real.rpow_mul
      (Real.log_nonneg hbk1)]
    congr 2; push_cast; ring
  have h2 : Real.log b ^ (2 * q) ≤ C0 * b ^ (1 - p) := hlog b hbk1
  have h3 : b⁻¹ * b ^ (1 - p) = (b ^ p)⁻¹ := by
    rw [← Real.rpow_neg_one, ← Real.rpow_add hb0, ← Real.rpow_neg hb0.le]
    congr 1; ring
  have h4 : b⁻¹ * (A * Real.log b ^ q) ^ 2 ≤ C * (b ^ p)⁻¹ := by
    rw [h1]
    calc b⁻¹ * (A ^ 2 * Real.log b ^ (2 * q)) ≤ b⁻¹ * (A ^ 2 * (C0 * b ^ (1 - p))) := by
          gcongr
      _ = (A ^ 2 * C0) * (b⁻¹ * b ^ (1 - p)) := by ring
      _ = (A ^ 2 * C0) * (b ^ p)⁻¹ := by rw [h3]
      _ ≤ C * (b ^ p)⁻¹ := by
          have : 0 ≤ (b ^ p)⁻¹ := by positivity
          exact mul_le_mul_of_nonneg_right (by rw [hCdef]; linarith) this
  calc b⁻¹ * (A * Real.log b ^ q) ^ 2 ≤ C * (b ^ p)⁻¹ := h4
    _ ≤ C * (c₉ / C * (L : ℝ) ^ (-(((k + 1 : ℕ) : ℝ) * (((d : ℝ) - 2) / 2 + δ)))) :=
        mul_le_mul_of_nonneg_left hmain hCpos.le
    _ = _ := by field_simp

end Arith

end Balaban.Green
