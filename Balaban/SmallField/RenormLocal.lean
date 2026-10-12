/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.SmallField.RenormExpand

/-!
# The local estimate for one polymer (Steps 2–5 of SMALLFIELD.md §2.3)

`TermOK.local_bound` expands `𝓔(0, X; ψ) - 𝓔(0, X; const ψ(0))` to second order around the
reference point in the rotated frame, uses the shape lemma, the Ward identity and Cauchy's
estimates, and bounds the difference with the explicit leading term
`½ Σ_x a_X(x) (g(x) - g(0)) - ¼ Σ_{x,x'} B_X(x,x') Σ_{μ,μ'} (x-x')_μ (x-x')_{μ'} G_{μμ'}`
by an explicit sum of products of the small quantities.
-/

@[expose] public section

open Metric Set

namespace Balaban.SmallField

variable {d N : ℕ}

/-- The quadratic form `Σ_{μ,μ'} w_μ w_{μ'} G_{μμ'}` of the lattice displacement `w = x - x'`. -/
def wquad (G : Fin d → Fin d → ℂ) (x x' : Site d) : ℂ :=
  ∑ μ, ∑ μ', (((x μ - x' μ : ℤ) : ℂ)) * (((x μ' - x' μ' : ℤ) : ℂ)) * G μ μ'

theorem norm_dotT_self_le (i₀ : Fin N) (v : Spin N) :
    ‖dotT i₀ v v‖ ≤ N * ‖v‖ ^ 2 := by
  unfold dotT
  calc ‖∑ i ∈ Finset.univ.erase i₀, v i * v i‖ ≤ ∑ i ∈ Finset.univ.erase i₀, ‖v i * v i‖ :=
        norm_sum_le _ _
    _ ≤ ∑ i ∈ Finset.univ.erase i₀, ‖v‖ ^ 2 := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [norm_mul, sq]
        exact mul_le_mul (norm_le_pi_norm v i) (norm_le_pi_norm v i) (norm_nonneg _)
          (norm_nonneg _)
    _ = ((Finset.univ.erase i₀).card : ℝ) * ‖v‖ ^ 2 := by simp
    _ ≤ N * ‖v‖ ^ 2 := by
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        exact_mod_cast (Finset.card_erase_le).trans (by simp)

theorem norm_sum_le_card {ι : Type*} [Fintype ι] (h : ι → ℂ) {c : ℝ}
    (hc : ∀ i, ‖h i‖ ≤ c) : ‖∑ i, h i‖ ≤ (Fintype.card ι : ℝ) * c := by
  calc ‖∑ i, h i‖ ≤ ∑ i, ‖h i‖ := norm_sum_le _ _
    _ ≤ ∑ _i : ι, c := Finset.sum_le_sum fun i _ => hc i
    _ = (Fintype.card ι : ℝ) * c := by simp

variable {i₀ i₁ : Fin N} {ν ρ : ℝ} {X : Finset (Site d)} {f : Cfg d N X → ℂ}

theorem TermOK.local_bound (hf : TermOK i₀ ν ρ X f) (hi : i₁ ≠ i₀) {M : ℝ}
    (hM : ∀ c ∈ ball (refPt i₀ ν X) ρ, ‖f c‖ ≤ M) (hν : 0 ≤ ν)
    (φ : Site d → Spin N) (ga : Site d → ℂ) (G : Fin d → Fin d → ℂ) (zc : Cfg d N X)
    {Z Z0 D F Ee Eb : ℝ} (hD0 : 0 ≤ D) (hF0 : 0 ≤ F)
    (hz : ‖zc + pack X φ 0‖ ≤ Z) (hZ : Z ≤ ρ / 2) (hzc : ‖zc‖ ≤ Z0) (hZ0 : Z0 ≤ ρ / 2)
    (hD : ∀ x ∈ X, ‖φ x‖ ≤ D) (hF : ∀ x ∈ X, ‖φ x i₀‖ ≤ F)
    (hE : ∀ x ∈ X, ‖φ x i₀ - ga x / 2 + dotT i₀ (φ x) (φ x) / 2‖ ≤ Ee)
    (hEb : ∀ x ∈ X, ∀ x' ∈ X,
      ‖dotT i₀ (φ x - φ x') (φ x - φ x') - wquad G x x'‖ ≤ Eb) :
    ‖f (refPt i₀ ν X + (zc + pack X φ 0)) - f (refPt i₀ ν X + zc)
        - (1 / 2 : ℂ) * ∑ x : ↥X, tensA i₀ ν X f x * ga x.1
        + (1 / 4 : ℂ) * ∑ x : ↥X, ∑ x' : ↥X, tensB i₀ i₁ ν X f x x' * wquad G x.1 x'.1‖ ≤
      2 * M * (Z / ρ) ^ 3 + 2 * M * (Z0 / ρ) ^ 3 + 4 * M * Z0 * D / ρ ^ 2
        + (X.card : ℝ) * (M / ρ) * Ee + 2 * (X.card : ℝ) ^ 2 * M * F ^ 2 / ρ ^ 2
        + ν / 2 * (X.card : ℝ) * (4 * M / ρ ^ 2) * (N * D ^ 2)
        + (X.card : ℝ) ^ 2 * (M / ρ ^ 2) * Eb := by
  classical
  set P := refPt i₀ ν X with hP
  have hρ := hf.rho_pos
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (hM _ (mem_ball_self hρ))
  set δ : Cfg d N X := pack X φ 0 with hδ
  have hδn : ‖δ‖ ≤ D := norm_pack_le X φ hD0 hD
  have hcard : (Fintype.card ↥X : ℝ) = X.card := by simp
  -- Taylor remainder
  have hT := hf.taylor_diff hM (z := zc + δ) (zc := zc) (hz.trans hZ) (hzc.trans hZ0)
  rw [add_sub_cancel_left] at hT
  have hZρ : ‖zc + δ‖ / ρ ≤ Z / ρ := div_le_div_of_nonneg_right hz hρ.le
  have hZ0ρ : ‖zc‖ / ρ ≤ Z0 / ρ := div_le_div_of_nonneg_right hzc hρ.le
  have hTb : ‖f (P + (zc + δ)) - f (P + zc) - fderiv ℂ f P δ - D2 f P zc δ
      - (1 / 2 : ℂ) * D2 f P δ δ‖ ≤ 2 * M * (Z / ρ) ^ 3 + 2 * M * (Z0 / ρ) ^ 3 := by
    refine hT.trans (add_le_add ?_ ?_)
    · exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hZρ 3) (by positivity)
    · exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hZ0ρ 3) (by positivity)
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
  have hcρ : 0 ≤ M / ρ := by positivity
  have hcρ2 : 0 ≤ 4 * M / ρ ^ 2 := by positivity
  have hbA : ∀ x : ↥X, ‖tensA i₀ ν X f x‖ ≤ M / ρ := fun x => hf.norm_tensA_le hM x
  have hbB : ∀ x x' : ↥X, ‖tensB i₀ i₁ ν X f x x'‖ ≤ 4 * M / ρ ^ 2 := fun x x' =>
    hf.norm_D2_basis_le hM _ _
  have hbAA : ∀ x x' : ↥X, ‖tensAA i₀ ν X f x x'‖ ≤ 4 * M / ρ ^ 2 := fun x x' =>
    hf.norm_D2_basis_le hM _ _
  have hbM : ∀ x : ↥X, ‖tensM i₀ i₁ ν X f x‖ ≤ 4 * M / ρ ^ 2 := fun x =>
    hf.norm_D2_basis_le hM _ _
  have hθ : ∀ x : ↥X, ‖dotT i₀ (φ x.1) (φ x.1)‖ ≤ N * D ^ 2 := fun x =>
    (norm_dotT_self_le i₀ _).trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (norm_nonneg _) (hD x.1 x.2) 2) (by positivity))
  -- the six terms
  have t2 : ‖D2 f P zc δ‖ ≤ 4 * M * Z0 * D / ρ ^ 2 := by
    refine (norm_D2_le hρ hf.analytic_ball hM zc δ).trans ?_
    rw [div_le_div_iff_of_pos_right (by positivity)]
    have := mul_le_mul hzc hδn (norm_nonneg _) (le_trans (norm_nonneg _) hzc)
    nlinarith
  have t3 : ‖∑ x : ↥X, tensA i₀ ν X f x * (φ x.1 i₀ - ga x.1 / 2 + dotT i₀ (φ x.1) (φ x.1) / 2)‖
      ≤ (X.card : ℝ) * (M / ρ) * Ee := by
    refine (norm_sum_le_card _ (c := M / ρ * Ee) fun x => ?_).trans (by rw [hcard]; ring_nf; rfl)
    rw [norm_mul]
    exact mul_le_mul (hbA x) (hE x.1 x.2) (norm_nonneg _) hcρ
  have t4 : ‖(1 / 2 : ℂ) * ∑ x : ↥X, ∑ x' : ↥X, tensAA i₀ ν X f x x' * (φ x.1 i₀ * φ x'.1 i₀)‖
      ≤ 2 * (X.card : ℝ) ^ 2 * M * F ^ 2 / ρ ^ 2 := by
    rw [norm_mul]
    have h1 : ‖∑ x : ↥X, ∑ x' : ↥X, tensAA i₀ ν X f x x' * (φ x.1 i₀ * φ x'.1 i₀)‖ ≤
        (Fintype.card ↥X : ℝ) * ((Fintype.card ↥X : ℝ) * (4 * M / ρ ^ 2 * F ^ 2)) := by
      refine norm_sum_le_card _ fun x => ?_
      refine norm_sum_le_card _ fun x' => ?_
      rw [norm_mul, norm_mul]
      have := mul_le_mul (hF x.1 x.2) (hF x'.1 x'.2) (norm_nonneg _) hF0
      calc ‖tensAA i₀ ν X f x x'‖ * (‖φ x.1 i₀‖ * ‖φ x'.1 i₀‖)
          ≤ 4 * M / ρ ^ 2 * (F * F) := mul_le_mul (hbAA x x') this (by positivity) hcρ2
        _ = 4 * M / ρ ^ 2 * F ^ 2 := by ring
    have h2 : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by simp
    rw [h2, hcard] at *
    calc 1 / 2 * ‖∑ x : ↥X, ∑ x' : ↥X, tensAA i₀ ν X f x x' * (φ x.1 i₀ * φ x'.1 i₀)‖
        ≤ 1 / 2 * ((X.card : ℝ) * ((X.card : ℝ) * (4 * M / ρ ^ 2 * F ^ 2))) :=
          mul_le_mul_of_nonneg_left h1 (by norm_num)
      _ = 2 * (X.card : ℝ) ^ 2 * M * F ^ 2 / ρ ^ 2 := by ring
  have t5 : ‖((ν : ℂ) / 2) * ∑ x : ↥X, tensM i₀ i₁ ν X f x * dotT i₀ (φ x.1) (φ x.1)‖
      ≤ ν / 2 * (X.card : ℝ) * (4 * M / ρ ^ 2) * (N * D ^ 2) := by
    rw [norm_mul]
    have h1 : ‖∑ x : ↥X, tensM i₀ i₁ ν X f x * dotT i₀ (φ x.1) (φ x.1)‖ ≤
        (Fintype.card ↥X : ℝ) * (4 * M / ρ ^ 2 * (N * D ^ 2)) := by
      refine norm_sum_le_card _ fun x => ?_
      rw [norm_mul]
      exact mul_le_mul (hbM x) (hθ x) (norm_nonneg _) hcρ2
    have h2 : ‖((ν : ℂ) / 2)‖ = ν / 2 := by
      rw [norm_div]; simp [abs_of_nonneg hν]
    rw [h2, hcard] at *
    calc ν / 2 * ‖∑ x : ↥X, tensM i₀ i₁ ν X f x * dotT i₀ (φ x.1) (φ x.1)‖
        ≤ ν / 2 * ((X.card : ℝ) * (4 * M / ρ ^ 2 * (N * D ^ 2))) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = _ := by ring
  have t6 : ‖(1 / 4 : ℂ) * ∑ x : ↥X, ∑ x' : ↥X, tensB i₀ i₁ ν X f x x' *
        (dotT i₀ (φ x.1 - φ x'.1) (φ x.1 - φ x'.1) - wquad G x.1 x'.1)‖
      ≤ (X.card : ℝ) ^ 2 * (M / ρ ^ 2) * Eb := by
    rw [norm_mul]
    have h1 : ‖∑ x : ↥X, ∑ x' : ↥X, tensB i₀ i₁ ν X f x x' *
        (dotT i₀ (φ x.1 - φ x'.1) (φ x.1 - φ x'.1) - wquad G x.1 x'.1)‖ ≤
        (Fintype.card ↥X : ℝ) * ((Fintype.card ↥X : ℝ) * (4 * M / ρ ^ 2 * Eb)) := by
      refine norm_sum_le_card _ fun x => ?_
      refine norm_sum_le_card _ fun x' => ?_
      rw [norm_mul]
      exact mul_le_mul (hbB x x') (hEb x.1 x.2 x'.1 x'.2) (norm_nonneg _) hcρ2
    have h2 : ‖(1 / 4 : ℂ)‖ = 1 / 4 := by simp
    rw [h2, hcard] at *
    calc 1 / 4 * ‖∑ x : ↥X, ∑ x' : ↥X, tensB i₀ i₁ ν X f x x' *
          (dotT i₀ (φ x.1 - φ x'.1) (φ x.1 - φ x'.1) - wquad G x.1 x'.1)‖
        ≤ 1 / 4 * ((X.card : ℝ) * ((X.card : ℝ) * (4 * M / ρ ^ 2 * Eb))) :=
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
