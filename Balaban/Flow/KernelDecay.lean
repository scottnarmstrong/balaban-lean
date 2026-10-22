/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Flow.TorusLift
public import Balaban.Background.GenSetStabilityRestrict

/-!
# Exponential decay of the Green kernel of a whole-lattice level

For a whole-lattice level `n` (`IsLevel G n`) the kernel of `G = (H_D(0))⁻¹` decays exponentially in
the `ℓ¹` torus distance rescaled by `L^{-K}`:
`‖G(x, x')‖ ≤ C exp(-ε · torusDist(x, x') / L^K)`, `ε = agmonRate d` (`kernel_decay`).  It is the
single-block form of `Multiscale.agmon_block` with the source `δ_{x'}`.
-/

@[expose] public section

namespace Balaban.Flow

open Finset Balaban Balaban.Multiscale Balaban.Background Balaban.Fluctuation Matrix

variable {d L N₀ K : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}

/-- The constant of the kernel decay: `(8/p² L^{4n})^{1/2}`. -/
noncomputable def kernelConst (d L n : ℕ) : ℝ :=
  Real.sqrt (8 / poincareConst d ^ 2 * ((L : ℝ) ^ n) ^ 2 * ((L : ℝ) ^ n) ^ 2)

theorem kernel_decay {G : GeneratingSet d L N₀ K ϱ} {n : ℕ} (hG : IsLevel G n) (hd : 0 < d)
    {a : ℕ → ℝ} {ν : ℝ} (hν : 0 ≤ ν) (ha : IsAdmissibleWeights K a)
    (hU : IsUnit (dirichletOperator G a ν (0 : G.Ω 1 → ℂ))) (x x' : G.Ω 1) :
    ‖(dirichletOperator G a ν (0 : G.Ω 1 → ℂ))⁻¹ x x'‖ ≤ kernelConst d L n *
      Real.exp (-(agmonRate d) *
        (Green.torusDist d (N₀ * L ^ K) (x : Torus d (N₀ * L ^ K)) x' / (L : ℝ) ^ K)) := by
  classical
  set H := dirichletOperator G a ν (0 : G.Ω 1 → ℂ) with hH
  have hdet : IsUnit H.det := (Matrix.isUnit_iff_isUnit_det H).1 hU
  set u : G.Ω 1 → ℂ := H⁻¹ *ᵥ Pi.single x' 1 with hu
  have hHu : H *ᵥ u = Pi.single x' 1 := by
    rw [hu, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec]
  have hux : u x = H⁻¹ x x' := by
    rw [hu, Matrix.mulVec_single_one]; simp
  have hn1 := (IsLevel.bounds hG).1
  have hnK := (IsLevel.bounds hG).2
  have hLK : (0 : ℝ) < (L : ℝ) ^ K := by
    have : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
    positivity
  set t : ℝ := Green.torusDist d (N₀ * L ^ K) (x : Torus d (N₀ * L ^ K)) x' / (L : ℝ) ^ K with ht
  have ht0 : 0 ≤ t := div_nonneg (Green.torusDist_nonneg_gen _ _) hLK.le
  have hpd : ENNReal.ofReal t ≤ G.pathDist (x : Torus d (N₀ * L ^ K)) x' :=
    pathDist_ge_torusDist G _ _
  have hAg := (agmon_block G hd hν ha (0 : G.Ω 1 → ℂ)
    (fun y => by
      simp only [Pi.zero_apply, norm_zero]
      have := coerciveConst_pos hd
      positivity)
    hn1 hnK hn1 hnK (y := (x : Torus d (N₀ * L ^ K))) (y' := (x' : Torus d (N₀ * L ^ K)))
    (hG.mem_layer _) (hG.mem_layer _) (u := u) (f := Pi.single x' 1) hHu
    (fun z hz => by
      have : z = x' := by
        by_contra hne; exact hz (by simp [hne])
      rw [this])
    ht0 hpd (agmonRate_pos hd).le le_rfl).1
  have hs : Green.sqNorm (Pi.single x' (1 : ℂ) : G.Ω 1 → ℂ) = 1 := by
    unfold Green.sqNorm
    rw [Finset.sum_eq_single x']
    · simp
    · intro b _ hb; simp [hb]
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [hs, mul_one] at hAg
  have hmem : (x : Torus d (N₀ * L ^ K)) ∈ G.blk n (x : Torus d (N₀ * L ^ K)) := by
    simp [GeneratingSet.mem_blk]
  have h1 : ‖u x‖ ^ 2 ≤ ∑ z ∈ G.blk n (x : Torus d (N₀ * L ^ K)), ‖zeroExt (G.Ω 1) u z‖ ^ 2 := by
    have := Finset.single_le_sum (f := fun z => ‖zeroExt (G.Ω 1) u z‖ ^ 2)
      (fun _ _ => by positivity) hmem
    simpa [zeroExt_mem] using this
  have h2 : ‖u x‖ ^ 2 ≤ (kernelConst d L n * Real.exp (-(agmonRate d) * t)) ^ 2 := by
    refine h1.trans (hAg.trans ?_)
    unfold kernelConst
    rw [mul_pow, Real.sq_sqrt (by positivity), ← Real.exp_nat_mul]
    have : ((2 : ℕ) : ℝ) * (-(agmonRate d) * t) = -(2 * agmonRate d * t) := by push_cast; ring
    rw [this]
  rw [← hux]
  exact (sq_le_sq₀ (norm_nonneg _)
    (mul_nonneg (by unfold kernelConst; exact Real.sqrt_nonneg _) (Real.exp_pos _).le)).1 h2

end Balaban.Flow
