/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.CutPointwiseWall
public import Balaban.Multiscale.PointwiseCase2c

/-!
# The `ℓ²` mass of the folded cut solution on a ball (VMOD-9 §3, (3.4) and (3.5))

`cut_sum_bound`: the weighted Agmon bound for the cut solution on a finite set of operator sites;
`cubeFold_ball_sq_bound` (3.4); `cubeFold_ball_l2` (3.5).
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.LatticeGreen Balaban.Reflection Finset Matrix

variable {d L N₀ k : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}

/-- The weighted `ℓ²` bound of the cut solution on a finite set of operator sites. -/
theorem cut_sum_bound {G : GeneratingSet d L N₀ k ϱ}
    {cut : Finset (Torus d (N₀ * L ^ k) × Fin d)} (hcut : CutAligned G cut) (hd0 : 0 < d)
    {a : ℕ → ℝ} {ν : ℝ} (hν : 0 ≤ ν) (ha : IsAdmissibleWeights k a) (α : G.Ω 1 → ℂ)
    (hα : ∀ x, ‖α x‖ ≤ coerciveConst d / (2 * (G.spacing x) ^ 2))
    {u f : G.Ω 1 → ℂ} (hu : cutOperator G a ν cut α *ᵥ u = f) {j' : ℕ} (hj'1 : 1 ≤ j')
    (hj'k : j' ≤ k) {y' : Torus d (N₀ * L ^ k)} (hy' : y' ∈ G.layer j')
    (hsupp : ∀ z : G.Ω 1, f z ≠ 0 → jBlock d L N₀ k j' z = jBlock d L N₀ k j' y') (t : ℝ)
    (T : Finset (Torus d (N₀ * L ^ k))) (hT : ∀ p ∈ T, p ∈ G.Ω 1) :
    ∑ p ∈ T, ((G.spacing p) ^ 2)⁻¹ * (Real.exp (agmonRate d * G.truncDist y' t p) ^ 2 *
        ‖zeroExt (G.Ω 1) u p‖ ^ 2) ≤
      4 / poincareConst d ^ 2 *
        ((L : ℝ) ^ j' * Real.exp (2 * agmonRate d * d) * Real.sqrt (Green.sqNorm f)) ^ 2 := by
  have hc := poincareConst_pos hd0
  have hr := G.isAgmonWeight_truncDist y' t
  have hw := agmon_wsq_le_cut G hcut hd0 hν ha α hα hr (agmonRate_pos hd0).le le_rfl hu
  have hs := agmonSource_le G hr (agmonRate_pos hd0).le hj'1 hj'k hy'
    (G.truncDist_self (G.layer_subset hj'1 hj'k hy') t) hsupp
  have hs' : agmonSource G (agmonRate d) (G.truncDist y' t) f ≤
      ((L : ℝ) ^ j' * Real.exp (2 * agmonRate d * d) * Real.sqrt (Green.sqNorm f)) ^ 2 := by
    refine hs.trans (le_of_eq ?_)
    have h1 : Real.exp (4 * agmonRate d * d) = Real.exp (2 * agmonRate d * d) ^ 2 := by
      rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
    rw [h1, mul_pow, mul_pow, Real.sq_sqrt (Green.sqNorm_nonneg _)]
  refine le_trans ?_ (hw.trans (mul_le_mul_of_nonneg_left hs' (by positivity)))
  unfold cwsq
  calc _ = ∑ p ∈ T, invSqSpacing G p *
        ‖agmonField G (agmonRate d) (G.truncDist y' t) u p‖ ^ 2 :=
        Finset.sum_congr rfl fun p hp => by
          rw [invSqSpacing_eq G (hT p hp), norm_agmonField, mul_pow]
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun x _ _ =>
          mul_nonneg (invSqSpacing_nonneg G x) (sq_nonneg _)

/-- **VMOD-9 (3.4).** The `ℓ²` mass of the folded cut solution on a ball of radius `R`: the
multiplicity of the fold is at most `2^d`, and the weighted Agmon bound controls each lifted point. -/
theorem cubeFold_ball_sq_bound {G : GeneratingSet d L N₀ k ϱ}
    {cut : Finset (Torus d (N₀ * L ^ k) × Fin d)} (hcut : CutAligned G cut) (hd : 3 ≤ d)
    (hϱ : 1 ≤ ϱ) {a : ℕ → ℝ} {ν : ℝ} (hν : 0 ≤ ν) (ha : IsAdmissibleWeights k a)
    (α : G.Ω 1 → ℂ) (hα : ∀ x, ‖α x‖ ≤ coerciveConst d / (2 * (G.spacing x) ^ 2))
    {u f : G.Ω 1 → ℂ} (hu : cutOperator G a ν cut α *ᵥ u = f) {j j' : ℕ} (hj2 : 2 ≤ j)
    (hjk : j ≤ k) (hj'1 : 1 ≤ j') (hj'k : j' ≤ k) {x y' : Torus d (N₀ * L ^ k)}
    (hx : x ∈ G.layer j) (hy' : y' ∈ G.layer j')
    (hsupp : ∀ z : G.Ω 1, f z ≠ 0 → jBlock d L N₀ k j' z = jBlock d L N₀ k j' y')
    (S : ℕ) [NeZero S] (c : Fin d → ℕ) (p0 : Torus d (2 * S))
    (hp0 : foldMap (N₀ * L ^ k) S (2 * S) c p0 = x) (hSℓ : S < N₀ * L ^ k) {R : ℝ} (hR : 0 ≤ R)
    (hRd : (d : ℝ) * R ≤ (L : ℝ) ^ (j - 1)) (hRS : R < S) {t : ℝ} (ht0 : 0 ≤ t)
    (ht : ENNReal.ofReal t ≤ G.pathDist x y') :
    ∑ z ∈ latticeBall (0 : Fin d → ℤ) R, ‖zeroExt (G.Ω 1) u (cubeFoldPt N₀ L k S c p0 z)‖ ^ 2 ≤
      2 ^ d * (((L : ℝ) ^ (j + 1)) ^ 2 * Real.exp (-(2 * agmonRate d * (t - 1))) *
        (4 / poincareConst d ^ 2 *
          ((L : ℝ) ^ j' * Real.exp (2 * agmonRate d * d) * Real.sqrt (Green.sqNorm f)) ^ 2)) := by
  classical
  have hd0 : 0 < d := by omega
  have hc := poincareConst_pos hd0
  have hL : (1 : ℝ) ≤ L := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne L)
  have hε0 := agmonRate_pos hd0
  set T := (latticeBall (0 : Fin d → ℤ) R).image (cubeFoldPt N₀ L k S c p0) with hT
  have hsum := sum_cubeFoldPt_le S c p0 hSℓ hR hRS (fun y => ‖zeroExt (G.Ω 1) u y‖ ^ 2)
    (fun _ => sq_nonneg _)
  have hmemz : ∀ z ∈ latticeBall (0 : Fin d → ℤ) R, ‖z‖ ≤ R := fun z hz => by
    have := (mem_latticeBall hR).1 hz; rwa [sub_zero] at this
  have hlift : ∀ z ∈ latticeBall (0 : Fin d → ℤ) R, ∃ h : Fin d → ℤ,
      cubeFoldPt N₀ L k S c p0 z = liftPt x h ∧ (d : ℝ) * ‖h‖ ≤ (L : ℝ) ^ (j - 1) := by
    intro z hz
    obtain ⟨h, hh, hP⟩ := cubeFoldPt_disp (N₀ := N₀) (L := L) (k := k) S c p0 z
    rw [cubeFoldPt_zero, hp0] at hP
    exact ⟨h, hP, ((mul_le_mul_of_nonneg_left (hh.trans (hmemz z hz)) (Nat.cast_nonneg d)).trans
      hRd)⟩
  have hTΩ : ∀ p ∈ T, p ∈ G.Ω 1 := by
    intro p hp
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.1 hp
    obtain ⟨h, hP, hdh⟩ := hlift z hz
    rw [hP]
    exact (lift_mem_layers G hϱ hj2 hjk hx hdh).1
  have hsb := cut_sum_bound hcut hd0 hν ha α hα hu hj'1 hj'k hy' hsupp t T hTΩ
  have hr : G.truncDist y' t x = t := G.truncDist_eq_of_le ht0 ht
  have hterm : ∀ p ∈ T, ‖zeroExt (G.Ω 1) u p‖ ^ 2 ≤ ((L : ℝ) ^ (j + 1)) ^ 2 *
      Real.exp (-(2 * agmonRate d * (t - 1))) *
      (((G.spacing p) ^ 2)⁻¹ * (Real.exp (agmonRate d * G.truncDist y' t p) ^ 2 *
        ‖zeroExt (G.Ω 1) u p‖ ^ 2)) := by
    intro p hp
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.1 hp
    obtain ⟨h, hP, hdh⟩ := hlift z hz
    rw [hP]
    obtain ⟨hpΩ, hlo, hhi⟩ := lift_mem_layers G hϱ hj2 hjk hx hdh
    obtain ⟨-, hpd⟩ := pathDist_lift_le G hϱ hj2 hjk hx hdh
    have hpd1 : G.pathDist (liftPt x h) x ≤ ENNReal.ofReal 1 := by
      refine hpd.trans (ENNReal.ofReal_le_ofReal ?_)
      rw [div_le_one (by positivity)]
      exact hdh
    have hpd2 : G.pathDist x (liftPt x h) ≤ ENNReal.ofReal 1 := by
      rw [GeneratingSet.pathDist_comm]; exact hpd1
    have hlip := G.abs_truncDist_sub_le y' t (x := x) (x' := liftPt x h) zero_le_one
      ((G.pathDist_triangle x (liftPt x h) y').trans (by gcongr))
      ((G.pathDist_triangle (liftPt x h) x y').trans (by gcongr))
    rw [hr] at hlip
    have hrp : t - 1 ≤ G.truncDist y' t (liftPt x h) := by
      have := (abs_le.1 hlip).2
      linarith
    have hsp0 : 0 < G.spacing (liftPt x h) := spacing_pos G
    have hA : (((L : ℝ) ^ (j + 1)) ^ 2)⁻¹ ≤ ((G.spacing (liftPt x h)) ^ 2)⁻¹ := by
      apply inv_anti₀ (by positivity)
      exact pow_le_pow_left₀ hsp0.le hhi 2
    have hB : Real.exp (2 * agmonRate d * (t - 1)) ≤
        Real.exp (agmonRate d * G.truncDist y' t (liftPt x h)) ^ 2 := by
      rw [sq, ← Real.exp_add]
      apply Real.exp_le_exp.2
      nlinarith
    have hE : Real.exp (-(2 * agmonRate d * (t - 1))) * Real.exp (2 * agmonRate d * (t - 1)) = 1 := by
      rw [← Real.exp_add]; simp
    have hLpos : 0 < ((L : ℝ) ^ (j + 1)) ^ 2 := by positivity
    have hn := sq_nonneg ‖zeroExt (G.Ω 1) u (liftPt x h)‖
    set a₀ := ‖zeroExt (G.Ω 1) u (liftPt x h)‖ ^ 2 with ha₀
    set Lc := ((L : ℝ) ^ (j + 1)) ^ 2 with hLc
    set X := Real.exp (-(2 * agmonRate d * (t - 1))) with hX
    set Ex := Real.exp (2 * agmonRate d * (t - 1)) with hEx
    have hX0 : 0 < X := Real.exp_pos _
    have hEx0 : 0 < Ex := Real.exp_pos _
    calc a₀ = Lc * X * (Lc⁻¹ * (Ex * a₀)) := by
          rw [show Lc * X * (Lc⁻¹ * (Ex * a₀)) = (Lc * Lc⁻¹) * ((X * Ex) * a₀) by ring,
            mul_inv_cancel₀ hLpos.ne', hE]; ring
      _ ≤ Lc * X * (((G.spacing (liftPt x h)) ^ 2)⁻¹ *
            (Real.exp (agmonRate d * G.truncDist y' t (liftPt x h)) ^ 2 * a₀)) := by
          gcongr
  have hsum2 : ∑ p ∈ T, ‖zeroExt (G.Ω 1) u p‖ ^ 2 ≤ ∑ p ∈ T, ((L : ℝ) ^ (j + 1)) ^ 2 *
      Real.exp (-(2 * agmonRate d * (t - 1))) *
      (((G.spacing p) ^ 2)⁻¹ * (Real.exp (agmonRate d * G.truncDist y' t p) ^ 2 *
        ‖zeroExt (G.Ω 1) u p‖ ^ 2)) := Finset.sum_le_sum hterm
  rw [← Finset.mul_sum] at hsum2
  refine hsum.trans (mul_le_mul_of_nonneg_left (hsum2.trans ?_) (by positivity))
  exact mul_le_mul_of_nonneg_left hsb (by positivity)

/-- **VMOD-9 (3.5).** The normalised `ℓ²` norm of the folded cut solution on the ball of radius
`2ρ`, `ρ = c₀ L^{j-1}/d ≥ 8`, has no source-volume factor. -/
theorem cubeFold_ball_l2 {G : GeneratingSet d L N₀ k ϱ}
    {cut : Finset (Torus d (N₀ * L ^ k) × Fin d)} (hcut : CutAligned G cut) (hd : 3 ≤ d)
    (hL : 3 ≤ L) (hϱ : 1 ≤ ϱ) (hsep : (L : ℝ) ^ d ≤ Real.exp (agmonRate d / 2 * (ϱ - 1)))
    {a : ℕ → ℝ} {ν : ℝ} (hν : 0 ≤ ν) (ha : IsAdmissibleWeights k a)
    (α : G.Ω 1 → ℂ) (hα : ∀ x, ‖α x‖ ≤ coerciveConst d / (2 * (G.spacing x) ^ 2))
    {u f : G.Ω 1 → ℂ} (hu : cutOperator G a ν cut α *ᵥ u = f) {j₀ j' : ℕ}
    (hj01 : 1 ≤ j₀) (hjk : j₀ + 1 ≤ k) (hj'1 : 1 ≤ j') (hj'k : j' ≤ k)
    {x y' : Torus d (N₀ * L ^ k)} (hx : x ∈ G.layer (j₀ + 1)) (hy' : y' ∈ G.layer j')
    (hsupp : ∀ z : G.Ω 1, f z ≠ 0 → jBlock d L N₀ k j' z = jBlock d L N₀ k j' y')
    (S : ℕ) [NeZero S] (c : Fin d → ℕ) (p0 : Torus d (2 * S))
    (hp0 : foldMap (N₀ * L ^ k) S (2 * S) c p0 = x) (hSℓ : S < N₀ * L ^ k)
    (hS : L ^ (j₀ + 1) ≤ S) {c0 : ℝ} (hc0 : 0 < c0) (hc04 : c0 ≤ 1 / 4)
    (hρ : 8 ≤ c0 * (L : ℝ) ^ j₀ / d) {Mf : ℝ} (hMf0 : 0 ≤ Mf) (hMf : ∀ i, ‖f i‖ ≤ Mf)
    {t : ℝ} (ht0 : 0 ≤ t) (ht : ENNReal.ofReal t ≤ G.pathDist x y') :
    (c0 * (L : ℝ) ^ j₀ / d) ^ (-(d : ℝ) / 2) *
        Real.sqrt (∑ w ∈ latticeBall (0 : Fin d → ℤ) (2 * (c0 * (L : ℝ) ^ j₀ / d)),
          ‖zeroExt (G.Ω 1) u (cubeFoldPt N₀ L k S c p0 w)‖ ^ 2) ≤
      Real.sqrt (2 ^ d) * (2 / poincareConst d * Real.exp (agmonRate d * (1 + 2 * d)) *
        (L : ℝ) ^ 2 * bd d L ^ 2 / Real.sqrt ((c0 / d) ^ d) *
        Real.exp (-(agmonRate d / 2 * t)) * ((L : ℝ) ^ (2 * j') * Mf)) := by
  have hd0 : 0 < d := by omega
  have hc := poincareConst_pos hd0
  have hε0 := agmonRate_pos hd0
  have hd0' : (0 : ℝ) < d := by exact_mod_cast hd0
  have hL0 : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hb1 := one_le_bd (d := d) (L := L)
  have hb0 : 0 < bd d L := by linarith
  have hj1 : 1 ≤ j₀ + 1 := by omega
  set ρ := c0 * (L : ℝ) ^ j₀ / d with hρdef
  have hρ0 : 0 < ρ := by linarith
  have hLj0 : (0 : ℝ) < (L : ℝ) ^ j₀ := by positivity
  have hRd : (d : ℝ) * (2 * ρ) ≤ (L : ℝ) ^ (j₀ + 1 - 1) := by
    simp only [Nat.add_sub_cancel]
    rw [hρdef]
    field_simp
    nlinarith
  have hRS : 2 * ρ < S := by
    have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd0
    have h1 : ρ ≤ c0 * (L : ℝ) ^ j₀ := div_le_self (by positivity) hd1
    have h2 : (L : ℝ) ^ (j₀ + 1) ≤ S := by exact_mod_cast hS
    have h3 : (L : ℝ) ^ j₀ < (L : ℝ) ^ (j₀ + 1) := by
      rw [pow_succ]
      have : (3 : ℝ) ≤ L := by exact_mod_cast hL
      nlinarith
    nlinarith
  obtain ⟨t₂, htt, ht2, habs⟩ := cut_scale_abs (G := G) hd0 hϱ hsep hj1 hj'k hy' hx ht0 ht
  have ht20 : 0 ≤ t₂ := ht0.trans htt
  have hball := cubeFold_ball_sq_bound hcut hd hϱ hν ha α hα hu (j := j₀ + 1) (by omega) hjk hj'1
    hj'k hx hy' hsupp S c p0 hp0 hSℓ (R := 2 * ρ) (by linarith) hRd hRS ht20 ht2
  set Q2 := ∑ w ∈ latticeBall (0 : Fin d → ℤ) (2 * ρ),
    ‖zeroExt (G.Ω 1) u (cubeFoldPt N₀ L k S c p0 w)‖ ^ 2 with hQ2
  set amp := (L : ℝ) ^ j' * Real.exp (2 * agmonRate d * d) * Real.sqrt (Green.sqNorm f) with hamp
  have hampn : 0 ≤ amp := by positivity
  set B2 := Real.sqrt (2 ^ d) with hB2
  have hB2sq : B2 ^ 2 = 2 ^ d := Real.sq_sqrt (by positivity)
  have hB20 : 0 < B2 := Real.sqrt_pos.2 (by positivity)
  have hΛ : Real.sqrt Q2 ≤ B2 * ((L : ℝ) ^ (j₀ + 1 + 1) * Real.exp (-(agmonRate d * (t₂ - 1))) *
      (2 / poincareConst d) * amp) := by
    have h1 : Q2 ≤ (B2 * ((L : ℝ) ^ (j₀ + 1 + 1) * Real.exp (-(agmonRate d * (t₂ - 1))) *
        (2 / poincareConst d) * amp)) ^ 2 := by
      refine hball.trans (le_of_eq ?_)
      have e1 : (B2 * ((L : ℝ) ^ (j₀ + 1 + 1) * Real.exp (-(agmonRate d * (t₂ - 1))) *
          (2 / poincareConst d) * amp)) ^ 2 = 2 ^ d * (((L : ℝ) ^ (j₀ + 1 + 1)) ^ 2 *
          (Real.exp (-(agmonRate d * (t₂ - 1)))) ^ 2 * (2 / poincareConst d) ^ 2 * amp ^ 2) := by
        rw [mul_pow, hB2sq]; ring
      have e2 : Real.exp (-(2 * agmonRate d * (t₂ - 1))) =
          (Real.exp (-(agmonRate d * (t₂ - 1)))) ^ 2 := by
        rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
      rw [e1, e2, hamp]
      field_simp
      ring
    calc Real.sqrt Q2 ≤ Real.sqrt ((B2 * ((L : ℝ) ^ (j₀ + 1 + 1) *
          Real.exp (-(agmonRate d * (t₂ - 1))) * (2 / poincareConst d) * amp)) ^ 2) :=
          Real.sqrt_le_sqrt h1
      _ = _ := Real.sqrt_sq (by positivity)
  have hP : 0 < Real.sqrt ((c0 / d) ^ d) := Real.sqrt_pos.2 (by positivity)
  have hrp := rpow_neg_half_eq hρ0 d
  have hsq : Real.sqrt (ρ ^ d) = Real.sqrt ((c0 / d) ^ d) * ((L : ℝ) ^ j₀ * bd d L ^ j₀) := by
    have e : ρ ^ d = (c0 / d) ^ d * ((L : ℝ) ^ j₀) ^ d := by
      rw [← mul_pow, hρdef]; congr 1; ring
    rw [e, Real.sqrt_mul (by positivity), sqrt_L_pow_eq (by omega)]
  rw [hrp, hsq]
  have hsq' := sqrt_sqNorm_le_of_supp G hj'k hMf0 hMf hsupp
  rw [sqrt_L_pow_eq (by omega)] at hsq'
  have hamp_le : amp ≤ Real.exp (2 * agmonRate d * d) * ((L : ℝ) ^ j') ^ 2 * bd d L ^ j' * Mf := by
    calc amp ≤ (L : ℝ) ^ j' * Real.exp (2 * agmonRate d * d) *
          ((L : ℝ) ^ j' * bd d L ^ j' * Mf) := by
          rw [hamp]; exact mul_le_mul_of_nonneg_left hsq' (by positivity)
      _ = _ := by ring
  have hE1 : Real.exp (-(agmonRate d * (t₂ - 1))) =
      Real.exp (agmonRate d) * Real.exp (-(agmonRate d * t₂)) := by
    rw [← Real.exp_add]; congr 1; ring
  have hE2 : Real.exp (agmonRate d * (1 + 2 * d)) =
      Real.exp (agmonRate d) * Real.exp (2 * agmonRate d * d) := by
    rw [← Real.exp_add]; congr 1; ring
  have key : (Real.sqrt ((c0 / d) ^ d) * ((L : ℝ) ^ j₀ * bd d L ^ j₀))⁻¹ *
      ((L : ℝ) ^ (j₀ + 1 + 1) * Real.exp (-(agmonRate d * (t₂ - 1))) *
        (2 / poincareConst d) * amp) ≤
      2 / poincareConst d * Real.exp (agmonRate d * (1 + 2 * d)) * (L : ℝ) ^ 2 * bd d L ^ 2 /
        Real.sqrt ((c0 / d) ^ d) * Real.exp (-(agmonRate d / 2 * t)) *
        ((L : ℝ) ^ (2 * j') * Mf) := by
    calc (Real.sqrt ((c0 / d) ^ d) * ((L : ℝ) ^ j₀ * bd d L ^ j₀))⁻¹ *
        ((L : ℝ) ^ (j₀ + 1 + 1) * Real.exp (-(agmonRate d * (t₂ - 1))) *
          (2 / poincareConst d) * amp)
        ≤ (Real.sqrt ((c0 / d) ^ d) * ((L : ℝ) ^ j₀ * bd d L ^ j₀))⁻¹ *
        ((L : ℝ) ^ (j₀ + 1 + 1) * Real.exp (-(agmonRate d * (t₂ - 1))) *
          (2 / poincareConst d) * (Real.exp (2 * agmonRate d * d) * ((L : ℝ) ^ j') ^ 2 *
            bd d L ^ j' * Mf)) := by
          gcongr
      _ = (2 / poincareConst d * Real.exp (agmonRate d) * Real.exp (2 * agmonRate d * d) *
            (L : ℝ) ^ 2 / (Real.sqrt ((c0 / d) ^ d) * bd d L ^ j₀)) *
          ((bd d L ^ j' * Real.exp (-(agmonRate d * t₂))) * (((L : ℝ) ^ j') ^ 2 * Mf)) := by
          rw [hE1]
          field_simp
          ring
      _ ≤ (2 / poincareConst d * Real.exp (agmonRate d) * Real.exp (2 * agmonRate d * d) *
            (L : ℝ) ^ 2 / (Real.sqrt ((c0 / d) ^ d) * bd d L ^ j₀)) *
          ((bd d L ^ (j₀ + 1) * bd d L * Real.exp (-(agmonRate d / 2 * t))) *
            (((L : ℝ) ^ j') ^ 2 * Mf)) := by
          gcongr
      _ = _ := by
          rw [hE2, pow_mul', pow_succ]
          field_simp
          ring
  calc (Real.sqrt ((c0 / d) ^ d) * ((L : ℝ) ^ j₀ * bd d L ^ j₀))⁻¹ * Real.sqrt Q2
      ≤ (Real.sqrt ((c0 / d) ^ d) * ((L : ℝ) ^ j₀ * bd d L ^ j₀))⁻¹ *
        (B2 * ((L : ℝ) ^ (j₀ + 1 + 1) * Real.exp (-(agmonRate d * (t₂ - 1))) *
          (2 / poincareConst d) * amp)) := mul_le_mul_of_nonneg_left hΛ (by positivity)
    _ = B2 * ((Real.sqrt ((c0 / d) ^ d) * ((L : ℝ) ^ j₀ * bd d L ^ j₀))⁻¹ *
        ((L : ℝ) ^ (j₀ + 1 + 1) * Real.exp (-(agmonRate d * (t₂ - 1))) *
          (2 / poincareConst d) * amp)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left key hB20.le

end Balaban.Localization
