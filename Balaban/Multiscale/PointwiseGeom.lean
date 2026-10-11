/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Multiscale.PointwiseAgmon
public import Balaban.Green.Lattice.LocGreenSums

/-!
# Lemma P: geometry of the lifted ball and the `L²` mass on it

* `pathDist_lift_le`: for a layer-`j` point `x` and `d ‖z‖ ≤ L^{j-1}`, the site `x + z` lies in `Ω₁`
  and `d(x + z, x) ≤ d ‖z‖ / L^{j-1} ≤ 1`;
* `rho_large`: the separation hypothesis forces `ϱ - 1 > 2 d + 1`;
* `ball_sq_bound`: the `ℓ²` mass of `ũ` on a lifted ball is controlled by the weighted Agmon bound.
-/

@[expose] public section

noncomputable section

namespace Balaban.Multiscale

open Finset Matrix Balaban Balaban.LatticeGreen

variable {d L N₀ k : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}

theorem natAbs_sum_le_card_mul (z : Fin d → ℤ) :
    ((∑ i, (z i).natAbs : ℕ) : ℝ) ≤ d * ‖z‖ := by
  push_cast
  calc ∑ i, ((z i).natAbs : ℝ) ≤ ∑ _i : Fin d, ‖z‖ := Finset.sum_le_sum fun i _ => by
        have := norm_le_pi_norm z i
        rw [Int.norm_eq_abs] at this
        rwa [Nat.cast_natAbs, Int.cast_abs]
    _ = d * ‖z‖ := by simp

theorem pathDist_lift_le (G : GeneratingSet d L N₀ k ϱ) (hϱ : 1 ≤ ϱ) {j : ℕ} (hj2 : 2 ≤ j)
    (hjk : j ≤ k) {x : Torus d (N₀ * L ^ k)} (hx : x ∈ G.layer j) {z : Fin d → ℤ}
    (hz : (d : ℝ) * ‖z‖ ≤ (L : ℝ) ^ (j - 1)) :
    liftPt x z ∈ G.Ω 1 ∧
      G.pathDist (liftPt x z) x ≤ ENNReal.ofReal (d * ‖z‖ / (L : ℝ) ^ (j - 1)) := by
  have hLpos : (0 : ℝ) < (L : ℝ) ^ (j - 1) := by
    have : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
    positivity
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hmem : ∀ z' : Fin d → ℤ, ‖z'‖ ≤ ‖z‖ → liftPt x z' ∈ G.Ω 1 ∧
      (L : ℝ) ^ (j - 1) ≤ G.spacing (liftPt x z') := fun z' hz' => by
    obtain ⟨h1, h2, -⟩ := lift_mem_layers G hϱ hj2 hjk hx (z := z')
      ((mul_le_mul_of_nonneg_left hz' hd0).trans hz)
    exact ⟨h1, h2⟩
  obtain ⟨t, ht, hp⟩ := exists_pathCost_lift G x (R := ‖z‖) hLpos
    (fun z' hz' => (hmem z' hz').1) (fun z' hz' => (hmem z' hz').2)
    (∑ i, (z i).natAbs) z rfl le_rfl
  refine ⟨(hmem z le_rfl).1, (GeneratingSet.pathDist_le hp).trans (ENNReal.ofReal_le_ofReal ?_)⟩
  calc t ≤ _ := ht
    _ ≤ _ := by
        gcongr
        exact natAbs_sum_le_card_mul z

theorem rho_large {G : GeneratingSet d L N₀ k ϱ} (S : PtSetting G) : 2 * (d : ℝ) + 1 < ϱ - 1 := by
  have hL3 : (3 : ℝ) ≤ L := by exact_mod_cast S.hL
  have h1 : Real.exp (d : ℝ) ≤ (L : ℝ) ^ d := by
    rw [← Real.exp_one_pow]
    refine pow_le_pow_left₀ (Real.exp_pos _).le ?_ d
    have := Real.exp_one_lt_d9
    linarith
  have h2 := h1.trans S.hsep
  rw [Real.exp_le_exp] at h2
  have hε := agmonRate_le S.hd0
  have hϱ1 := S.hϱ
  have hd3 : (3 : ℝ) ≤ d := by exact_mod_cast S.hd
  by_contra hcon
  push Not at hcon
  have : agmonRate d / 2 * (ϱ - 1) ≤ 1 / 64 * (ϱ - 1) := by
    have : agmonRate d / 2 ≤ 1 / 64 := by linarith
    exact mul_le_mul_of_nonneg_right this (by linarith)
  nlinarith

omit [NeZero N₀] [NeZero L] in
theorem two_mul_lt_side (hL : 3 ≤ L) [NeZero N₀] {j : ℕ} (hj1 : 1 ≤ j) (hjk : j ≤ k) (hd : 1 ≤ d)
    {R : ℝ} (hR : 0 ≤ R) (hRd : (d : ℝ) * R ≤ (L : ℝ) ^ (j - 1)) :
    2 * R < ((N₀ * L ^ k : ℕ) : ℝ) := by
  have hL3 : (3 : ℝ) ≤ L := by exact_mod_cast hL
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have h1 : R ≤ (L : ℝ) ^ (j - 1) := by nlinarith
  have h2 : (L : ℝ) ^ j = L * (L : ℝ) ^ (j - 1) := by
    rw [← pow_succ']; congr 1; omega
  have h3 : (L : ℝ) ^ j ≤ (L : ℝ) ^ k := pow_le_pow_right₀ (by linarith) hjk
  have hN : (1 : ℝ) ≤ N₀ := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne N₀)
  have hpos : 0 < (L : ℝ) ^ (j - 1) := by positivity
  push_cast
  nlinarith [pow_nonneg (by linarith : (0 : ℝ) ≤ L) k]

/-- The `ℓ²` mass of `ũ` on a lifted ball, via the weighted Agmon bound. -/
theorem ball_sq_bound {G : GeneratingSet d L N₀ k ϱ} (S : PtSetting G) {j : ℕ} (hj2 : 2 ≤ j)
    (hjk : j ≤ k) {x : Torus d (N₀ * L ^ k)} (hx : x ∈ G.layer j) {R : ℝ} (hR : 0 ≤ R)
    (hRd : (d : ℝ) * R ≤ (L : ℝ) ^ (j - 1)) {t : ℝ} (ht0 : 0 ≤ t)
    (ht : ENNReal.ofReal t ≤ G.pathDist x S.y') :
    ∑ z ∈ latticeBall (0 : Fin d → ℤ) R, ‖S.ut (liftPt x z)‖ ^ 2 ≤
      ((L : ℝ) ^ (j + 1)) ^ 2 * Real.exp (-(2 * agmonRate d * (t - 1))) *
        (4 / poincareConst d ^ 2 * S.amp ^ 2) := by
  have hc := poincareConst_pos S.hd0
  have hL : (1 : ℝ) ≤ L := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne L)
  have hε0 := agmonRate_pos S.hd0
  have hinj : Set.InjOn (liftPt (d := d) (L := L) (N₀ := N₀) (k := k) x)
      (latticeBall (0 : Fin d → ℤ) R : Set (Fin d → ℤ)) := by
    intro z hz z' hz' h
    have a := (mem_latticeBall hR).1 hz
    have b := (mem_latticeBall hR).1 hz'
    rw [sub_zero] at a b
    exact liftPt_injOn x a b (two_mul_lt_side S.hL (by omega) hjk (by have := S.hd; omega) hR hRd) h
  set T := (latticeBall (0 : Fin d → ℤ) R).image (liftPt x) with hT
  have hsum : ∑ z ∈ latticeBall (0 : Fin d → ℤ) R, ‖S.ut (liftPt x z)‖ ^ 2 =
      ∑ p ∈ T, ‖S.ut p‖ ^ 2 := (Finset.sum_image (f := fun p => ‖S.ut p‖ ^ 2) hinj).symm
  rw [hsum]
  have hmemz : ∀ z ∈ latticeBall (0 : Fin d → ℤ) R, ‖z‖ ≤ R := fun z hz => by
    have := (mem_latticeBall hR).1 hz; rwa [sub_zero] at this
  have hTΩ : ∀ p ∈ T, p ∈ G.Ω 1 := by
    intro p hp
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.1 hp
    exact (lift_mem_layers G S.hϱ hj2 hjk hx ((mul_le_mul_of_nonneg_left (hmemz z hz)
      (Nat.cast_nonneg d)).trans hRd)).1
  have hsb := S.sum_bound t T hTΩ
  have hr : G.truncDist S.y' t x = t := G.truncDist_eq_of_le ht0 ht
  have hterm : ∀ p ∈ T, ‖S.ut p‖ ^ 2 ≤ ((L : ℝ) ^ (j + 1)) ^ 2 * Real.exp (-(2 * agmonRate d * (t - 1))) *
      (((G.spacing p) ^ 2)⁻¹ * (Real.exp (agmonRate d * G.truncDist S.y' t p) ^ 2 * ‖S.ut p‖ ^ 2)) := by
    intro p hp
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.1 hp
    have hzd : (d : ℝ) * ‖z‖ ≤ (L : ℝ) ^ (j - 1) :=
      (mul_le_mul_of_nonneg_left (hmemz z hz) (Nat.cast_nonneg d)).trans hRd
    obtain ⟨hpΩ, hlo, hhi⟩ := lift_mem_layers G S.hϱ hj2 hjk hx hzd
    obtain ⟨-, hpd⟩ := pathDist_lift_le G S.hϱ hj2 hjk hx hzd
    have hpd1 : G.pathDist (liftPt x z) x ≤ ENNReal.ofReal 1 := by
      refine hpd.trans (ENNReal.ofReal_le_ofReal ?_)
      rw [div_le_one (by positivity)]
      exact (mul_le_mul_of_nonneg_left (hmemz z hz) (Nat.cast_nonneg d)).trans hRd
    have hpd2 : G.pathDist x (liftPt x z) ≤ ENNReal.ofReal 1 := by
      rw [GeneratingSet.pathDist_comm]; exact hpd1
    have hlip := G.abs_truncDist_sub_le S.y' t (x := x) (x' := liftPt x z) zero_le_one
      ((G.pathDist_triangle x (liftPt x z) S.y').trans (by gcongr))
      ((G.pathDist_triangle (liftPt x z) x S.y').trans (by gcongr))
    rw [hr] at hlip
    have hrp : t - 1 ≤ G.truncDist S.y' t (liftPt x z) := by
      have := (abs_le.1 hlip).2
      linarith
    have hsp0 : 0 < G.spacing (liftPt x z) := spacing_pos G
    have hA : (((L : ℝ) ^ (j + 1)) ^ 2)⁻¹ ≤ ((G.spacing (liftPt x z)) ^ 2)⁻¹ := by
      apply inv_anti₀ (by positivity)
      exact pow_le_pow_left₀ hsp0.le hhi 2
    have hB : Real.exp (2 * agmonRate d * (t - 1)) ≤
        Real.exp (agmonRate d * G.truncDist S.y' t (liftPt x z)) ^ 2 := by
      rw [sq, ← Real.exp_add]
      apply Real.exp_le_exp.2
      nlinarith
    have hE : Real.exp (-(2 * agmonRate d * (t - 1))) * Real.exp (2 * agmonRate d * (t - 1)) = 1 := by
      rw [← Real.exp_add]; simp
    have hLpos : 0 < ((L : ℝ) ^ (j + 1)) ^ 2 := by positivity
    have hn := sq_nonneg ‖S.ut (liftPt x z)‖
    set a := ‖S.ut (liftPt x z)‖ ^ 2 with ha
    set Lc := ((L : ℝ) ^ (j + 1)) ^ 2 with hLc
    set X := Real.exp (-(2 * agmonRate d * (t - 1))) with hX
    set Ex := Real.exp (2 * agmonRate d * (t - 1)) with hEx
    have hX0 : 0 < X := Real.exp_pos _
    have hEx0 : 0 < Ex := Real.exp_pos _
    calc a = Lc * X * (Lc⁻¹ * (Ex * a)) := by
          rw [show Lc * X * (Lc⁻¹ * (Ex * a)) = (Lc * Lc⁻¹) * ((X * Ex) * a) by ring,
            mul_inv_cancel₀ hLpos.ne', hE]; ring
      _ ≤ Lc * X * (((G.spacing (liftPt x z)) ^ 2)⁻¹ *
            (Real.exp (agmonRate d * G.truncDist S.y' t (liftPt x z)) ^ 2 * a)) := by
          gcongr
  have hsum2 : ∑ p ∈ T, ‖S.ut p‖ ^ 2 ≤ ∑ p ∈ T, ((L : ℝ) ^ (j + 1)) ^ 2 *
      Real.exp (-(2 * agmonRate d * (t - 1))) *
      (((G.spacing p) ^ 2)⁻¹ * (Real.exp (agmonRate d * G.truncDist S.y' t p) ^ 2 *
        ‖S.ut p‖ ^ 2)) := Finset.sum_le_sum hterm
  rw [← Finset.mul_sum] at hsum2
  refine hsum2.trans ?_
  exact mul_le_mul_of_nonneg_left hsb (by positivity)

end Balaban.Multiscale
