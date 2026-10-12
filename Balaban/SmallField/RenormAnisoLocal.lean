/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.SmallField.RenormAnisoDefs

/-!
# The local estimate for one polymer on the anisotropic polydisc

`TermOK.local_bound_aniso` is `TermOK.local_bound` with the isotropic ball of radius `ρ` replaced
by the anisotropic polydisc `polyAniso i₀ ν r X`.  The algebra (shape lemma, Ward identity,
`ward_algebra`) is unchanged and uses `TermOK` at any radius.  Only three terms change:

* the two cubic Taylor remainders, now `2 M g(z)³` in the gauge `g = anisoGauge i₀ r X`;
* the base-point term `f''(P)(z_c, δ)`, now `4 M g(z_c) g(δ)` with `g(δ) ≤ D / r`.

The tensor bounds `‖a_X‖ ≤ M/r`, `‖B_X‖, ‖A_X‖, ‖m_X‖ ≤ 4M/r²` involve only spin directions and
the transverse field direction `b_{i₁}`, all of radius `r`.
-/

@[expose] public section

open Metric Set

namespace Balaban.SmallField

variable {d N : ℕ}

variable {i₀ i₁ : Fin N} {ν ρ r : ℝ} {X : Finset (Site d)} {f : Cfg d N X → ℂ}

theorem TermOK.local_bound_aniso (hf : TermOK i₀ ν ρ X f) (hi : i₁ ≠ i₀) {M : ℝ} (hr : 0 < r)
    (han : AnalyticOnNhd ℂ f (polyAniso i₀ ν r X)) (hM : ∀ c ∈ polyAniso i₀ ν r X, ‖f c‖ ≤ M)
    (hν : 0 ≤ ν) (φ : Site d → Spin N) (ga : Site d → ℂ) (G : Fin d → Fin d → ℂ)
    (zc : Cfg d N X) {Z Z0 D F Ee Eb : ℝ} (hD0 : 0 ≤ D) (hF0 : 0 ≤ F)
    (hz : anisoGauge i₀ r X (zc + pack X φ 0) ≤ Z) (hZ : Z ≤ 1 / 2)
    (hzc : anisoGauge i₀ r X zc ≤ Z0) (hZ0 : Z0 ≤ 1 / 2)
    (hD : ∀ x ∈ X, ‖φ x‖ ≤ D) (hF : ∀ x ∈ X, ‖φ x i₀‖ ≤ F)
    (hE : ∀ x ∈ X, ‖φ x i₀ - ga x / 2 + dotT i₀ (φ x) (φ x) / 2‖ ≤ Ee)
    (hEb : ∀ x ∈ X, ∀ x' ∈ X,
      ‖dotT i₀ (φ x - φ x') (φ x - φ x') - wquad G x x'‖ ≤ Eb) :
    ‖f (refPt i₀ ν X + (zc + pack X φ 0)) - f (refPt i₀ ν X + zc)
        - (1 / 2 : ℂ) * ∑ x : ↥X, tensA i₀ ν X f x * ga x.1
        + (1 / 4 : ℂ) * ∑ x : ↥X, ∑ x' : ↥X, tensB i₀ i₁ ν X f x x' * wquad G x.1 x'.1‖ ≤
      2 * M * Z ^ 3 + 2 * M * Z0 ^ 3 + 4 * M * Z0 * (D / r)
        + (X.card : ℝ) * (M / r) * Ee + 2 * (X.card : ℝ) ^ 2 * M * F ^ 2 / r ^ 2
        + ν / 2 * (X.card : ℝ) * (4 * M / r ^ 2) * (N * D ^ 2)
        + (X.card : ℝ) ^ 2 * (M / r ^ 2) * Eb := by
  classical
  set P := refPt i₀ ν X with hP
  have hM0 : 0 ≤ M := aniso_M_nonneg hr hM
  set δ : Cfg d N X := pack X φ 0 with hδ
  have hδg : anisoGauge i₀ r X δ ≤ D / r := anisoGauge_pack_zero_le hr φ hD0 hD
  have hcard : (Fintype.card ↥X : ℝ) = X.card := by simp
  -- Taylor remainder in the gauge
  have hT := aniso_taylor_diff hr han hM (z := zc + δ) (zc := zc) (hz.trans hZ) (hzc.trans hZ0)
  rw [add_sub_cancel_left] at hT
  have hTb : ‖f (P + (zc + δ)) - f (P + zc) - fderiv ℂ f P δ - D2 f P zc δ
      - (1 / 2 : ℂ) * D2 f P δ δ‖ ≤ 2 * M * Z ^ 3 + 2 * M * Z0 ^ 3 := by
    refine hT.trans (add_le_add ?_ ?_)
    · exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (anisoGauge_nonneg _) hz 3)
        (by positivity)
    · exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (anisoGauge_nonneg _) hzc 3)
        (by positivity)
  -- shape
  have hlin := hf.lin_pack φ
  have hquad := hf.quad_pack hi φ φ
  have hward := ward_algebra i₀ (ν : ℂ) (fun x => tensA i₀ ν X f x) (fun x => tensM i₀ i₁ ν X f x)
    (fun x x' => tensB i₀ i₁ ν X f x x') (fun x x' => hf.tensB_symm x x')
    (fun x' => hf.ward hi x') (fun x : ↥X => φ x.1)
  -- exact identity
  have hs1 : ∑ x : ↥X, tensA i₀ ν X f x * (φ x.1 i₀ - ga x.1 / 2 + dotT i₀ (φ x.1) (φ x.1) / 2) =
      ∑ x : ↥X, tensA i₀ ν X f x * φ x.1 i₀ - (1 / 2 : ℂ) * ∑ x : ↥X, tensA i₀ ν X f x * ga x.1
        + (1 / 2 : ℂ) * ∑ x : ↥X, tensA i₀ ν X f x * dotT i₀ (φ x.1) (φ x.1) := by
    simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun x _ => by ring
  have hs2 : ∑ x : ↥X, ∑ x' : ↥X, tensB i₀ i₁ ν X f x x' *
        (dotT i₀ (φ x.1 - φ x'.1) (φ x.1 - φ x'.1) - wquad G x.1 x'.1) =
      ∑ x : ↥X, ∑ x' : ↥X, tensB i₀ i₁ ν X f x x' * dotT i₀ (φ x.1 - φ x'.1) (φ x.1 - φ x'.1)
        - ∑ x : ↥X, ∑ x' : ↥X, tensB i₀ i₁ ν X f x x' * wquad G x.1 x'.1 := by
    simp only [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun x' _ => by ring
  have hs3 : ∑ x : ↥X, ∑ x' : ↥X, (tensAA i₀ ν X f x x' * (φ x.1 i₀ * φ x'.1 i₀) +
        tensB i₀ i₁ ν X f x x' * dotT i₀ (φ x.1) (φ x'.1)) =
      ∑ x : ↥X, ∑ x' : ↥X, tensAA i₀ ν X f x x' * (φ x.1 i₀ * φ x'.1 i₀) +
      ∑ x : ↥X, ∑ x' : ↥X, tensB i₀ i₁ ν X f x x' * dotT i₀ (φ x.1) (φ x'.1) := by
    simp only [Finset.sum_add_distrib]
  have hid : f (P + (zc + δ)) - f (P + zc) - (1 / 2 : ℂ) * ∑ x : ↥X, tensA i₀ ν X f x * ga x.1
        + (1 / 4 : ℂ) * ∑ x : ↥X, ∑ x' : ↥X, tensB i₀ i₁ ν X f x x' * wquad G x.1 x'.1 =
      (f (P + (zc + δ)) - f (P + zc) - fderiv ℂ f P δ - D2 f P zc δ
        - (1 / 2 : ℂ) * D2 f P δ δ) + D2 f P zc δ
      + ∑ x : ↥X, tensA i₀ ν X f x * (φ x.1 i₀ - ga x.1 / 2 + dotT i₀ (φ x.1) (φ x.1) / 2)
      + (1 / 2 : ℂ) * ∑ x : ↥X, ∑ x' : ↥X, tensAA i₀ ν X f x x' * (φ x.1 i₀ * φ x'.1 i₀)
      - ((ν : ℂ) / 2) * ∑ x : ↥X, tensM i₀ i₁ ν X f x * dotT i₀ (φ x.1) (φ x.1)
      - (1 / 4 : ℂ) * ∑ x : ↥X, ∑ x' : ↥X, tensB i₀ i₁ ν X f x x' *
          (dotT i₀ (φ x.1 - φ x'.1) (φ x.1 - φ x'.1) - wquad G x.1 x'.1) := by
    rw [hs1, hs2]
    rw [hs3] at hquad
    simp only [neg_mul] at hward
    linear_combination hlin * (1 : ℂ) + (1 / 2 : ℂ) * hquad + hward
  rw [hid]
  have hcr : 0 ≤ M / r := by positivity
  have hcr2 : 0 ≤ 4 * M / r ^ 2 := by positivity
  have hbA : ∀ x : ↥X, ‖tensA i₀ ν X f x‖ ≤ M / r := fun x => aniso_norm_tensA_le hr han hM x
  have hbB : ∀ x x' : ↥X, ‖tensB i₀ i₁ ν X f x x'‖ ≤ 4 * M / r ^ 2 := fun x x' =>
    aniso_norm_D2_basis_le hr han hM (anisoWt_inl _) (anisoWt_inl _)
  have hbAA : ∀ x x' : ↥X, ‖tensAA i₀ ν X f x x'‖ ≤ 4 * M / r ^ 2 := fun x x' =>
    aniso_norm_D2_basis_le hr han hM (anisoWt_inl _) (anisoWt_inl _)
  have hbM : ∀ x : ↥X, ‖tensM i₀ i₁ ν X f x‖ ≤ 4 * M / r ^ 2 := fun x =>
    aniso_norm_D2_basis_le hr han hM (anisoWt_inr_ne hi) (anisoWt_inl _)
  have hθ : ∀ x : ↥X, ‖dotT i₀ (φ x.1) (φ x.1)‖ ≤ N * D ^ 2 := fun x =>
    (norm_dotT_self_le i₀ _).trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (norm_nonneg _) (hD x.1 x.2) 2) (by positivity))
  -- the six terms
  have t2 : ‖D2 f P zc δ‖ ≤ 4 * M * Z0 * (D / r) := by
    refine (aniso_norm_D2_le hr han hM zc δ).trans ?_
    have h4 : 0 ≤ 4 * M := by positivity
    have := mul_le_mul hzc hδg (anisoGauge_nonneg _) (le_trans (anisoGauge_nonneg _) hzc)
    calc 4 * M * anisoGauge i₀ r X zc * anisoGauge i₀ r X δ
        = 4 * M * (anisoGauge i₀ r X zc * anisoGauge i₀ r X δ) := by ring
      _ ≤ 4 * M * (Z0 * (D / r)) := mul_le_mul_of_nonneg_left this h4
      _ = 4 * M * Z0 * (D / r) := by ring
  have t3 : ‖∑ x : ↥X, tensA i₀ ν X f x * (φ x.1 i₀ - ga x.1 / 2 + dotT i₀ (φ x.1) (φ x.1) / 2)‖
      ≤ (X.card : ℝ) * (M / r) * Ee := by
    refine (norm_sum_le_card _ (c := M / r * Ee) fun x => ?_).trans (by rw [hcard]; ring_nf; rfl)
    rw [norm_mul]
    exact mul_le_mul (hbA x) (hE x.1 x.2) (norm_nonneg _) hcr
  have t4 : ‖(1 / 2 : ℂ) * ∑ x : ↥X, ∑ x' : ↥X, tensAA i₀ ν X f x x' * (φ x.1 i₀ * φ x'.1 i₀)‖
      ≤ 2 * (X.card : ℝ) ^ 2 * M * F ^ 2 / r ^ 2 := by
    rw [norm_mul]
    have h1 : ‖∑ x : ↥X, ∑ x' : ↥X, tensAA i₀ ν X f x x' * (φ x.1 i₀ * φ x'.1 i₀)‖ ≤
        (Fintype.card ↥X : ℝ) * ((Fintype.card ↥X : ℝ) * (4 * M / r ^ 2 * F ^ 2)) := by
      refine norm_sum_le_card _ fun x => ?_
      refine norm_sum_le_card _ fun x' => ?_
      rw [norm_mul, norm_mul]
      have := mul_le_mul (hF x.1 x.2) (hF x'.1 x'.2) (norm_nonneg _) hF0
      calc ‖tensAA i₀ ν X f x x'‖ * (‖φ x.1 i₀‖ * ‖φ x'.1 i₀‖)
          ≤ 4 * M / r ^ 2 * (F * F) := mul_le_mul (hbAA x x') this (by positivity) hcr2
        _ = 4 * M / r ^ 2 * F ^ 2 := by ring
    have h2 : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by simp
    rw [h2, hcard] at *
    calc 1 / 2 * ‖∑ x : ↥X, ∑ x' : ↥X, tensAA i₀ ν X f x x' * (φ x.1 i₀ * φ x'.1 i₀)‖
        ≤ 1 / 2 * ((X.card : ℝ) * ((X.card : ℝ) * (4 * M / r ^ 2 * F ^ 2))) :=
          mul_le_mul_of_nonneg_left h1 (by norm_num)
      _ = 2 * (X.card : ℝ) ^ 2 * M * F ^ 2 / r ^ 2 := by ring
  have t5 : ‖((ν : ℂ) / 2) * ∑ x : ↥X, tensM i₀ i₁ ν X f x * dotT i₀ (φ x.1) (φ x.1)‖
      ≤ ν / 2 * (X.card : ℝ) * (4 * M / r ^ 2) * (N * D ^ 2) := by
    rw [norm_mul]
    have h1 : ‖∑ x : ↥X, tensM i₀ i₁ ν X f x * dotT i₀ (φ x.1) (φ x.1)‖ ≤
        (Fintype.card ↥X : ℝ) * (4 * M / r ^ 2 * (N * D ^ 2)) := by
      refine norm_sum_le_card _ fun x => ?_
      rw [norm_mul]
      exact mul_le_mul (hbM x) (hθ x) (norm_nonneg _) hcr2
    have h2 : ‖((ν : ℂ) / 2)‖ = ν / 2 := by
      rw [norm_div]; simp [abs_of_nonneg hν]
    rw [h2, hcard] at *
    calc ν / 2 * ‖∑ x : ↥X, tensM i₀ i₁ ν X f x * dotT i₀ (φ x.1) (φ x.1)‖
        ≤ ν / 2 * ((X.card : ℝ) * (4 * M / r ^ 2 * (N * D ^ 2))) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = _ := by ring
  have t6 : ‖(1 / 4 : ℂ) * ∑ x : ↥X, ∑ x' : ↥X, tensB i₀ i₁ ν X f x x' *
        (dotT i₀ (φ x.1 - φ x'.1) (φ x.1 - φ x'.1) - wquad G x.1 x'.1)‖
      ≤ (X.card : ℝ) ^ 2 * (M / r ^ 2) * Eb := by
    rw [norm_mul]
    have h1 : ‖∑ x : ↥X, ∑ x' : ↥X, tensB i₀ i₁ ν X f x x' *
        (dotT i₀ (φ x.1 - φ x'.1) (φ x.1 - φ x'.1) - wquad G x.1 x'.1)‖ ≤
        (Fintype.card ↥X : ℝ) * ((Fintype.card ↥X : ℝ) * (4 * M / r ^ 2 * Eb)) := by
      refine norm_sum_le_card _ fun x => ?_
      refine norm_sum_le_card _ fun x' => ?_
      rw [norm_mul]
      exact mul_le_mul (hbB x x') (hEb x.1 x.2 x'.1 x'.2) (norm_nonneg _) hcr2
    have h2 : ‖(1 / 4 : ℂ)‖ = 1 / 4 := by simp
    rw [h2, hcard] at *
    calc 1 / 4 * ‖∑ x : ↥X, ∑ x' : ↥X, tensB i₀ i₁ ν X f x x' *
          (dotT i₀ (φ x.1 - φ x'.1) (φ x.1 - φ x'.1) - wquad G x.1 x'.1)‖
        ≤ 1 / 4 * ((X.card : ℝ) * ((X.card : ℝ) * (4 * M / r ^ 2 * Eb))) :=
          mul_le_mul_of_nonneg_left h1 (by norm_num)
      _ = _ := by ring
  have tri : ∀ a b c d e g : ℂ,
      ‖a + b + c + d - e - g‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ + ‖d‖ + ‖e‖ + ‖g‖ := by
    intro a b c d e g
    have h1 := norm_sub_le (a + b + c + d - e) g
    have h2 := norm_sub_le (a + b + c + d) e
    have h3 := norm_add_le (a + b + c) d
    have h4 := norm_add_le (a + b) c
    have h5 := norm_add_le a b
    linarith
  refine (tri _ _ _ _ _ _).trans ?_
  linarith [hTb, t2, t3, t4, t5, t6]

end Balaban.SmallField
