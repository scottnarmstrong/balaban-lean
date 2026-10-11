/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Multiscale.PointwiseHolderI

/-!
# Proposition 4.9 (G-2(iii)): the Hölder bound for the gradient

The geometry of a Hölder pair `(x, x' = x + z)` and the Case 1 / large-distance bound
(`holder_caseII`): `ℓ(x) |∂u(x') - ∂u(x)| ≤ (L + 1) M` where `M` bounds `U` near `x`.
-/

@[expose] public section

noncomputable section

namespace Balaban.Multiscale

open Finset Matrix Balaban Balaban.LatticeGreen

variable {d L N₀ k : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}

/-- Absorbing the scale: `ℓ ≤ K` or `ℓ ≤ K r` gives `ℓ ≤ K ℓ^θ r^{1-θ}`. -/
theorem le_const_rpow_mul {ℓ r K θ : ℝ} (hℓ : 1 ≤ ℓ) (hr : 1 ≤ r) (hK : 1 ≤ K) (hθ0 : 0 < θ)
    (hθ1 : θ < 1) (h : ℓ ≤ K ∨ ℓ ≤ K * r) : ℓ ≤ K * (ℓ ^ θ * r ^ (1 - θ)) := by
  have hℓ0 : 0 < ℓ := by linarith
  have hr0 : 0 < r := by linarith
  have hK0 : 0 < K := by linarith
  have h1r : 1 ≤ r ^ (1 - θ) := Real.one_le_rpow hr (by linarith)
  have hsplit : ℓ = ℓ ^ θ * ℓ ^ (1 - θ) := by
    rw [← Real.rpow_add hℓ0]; simp
  have hkey : ℓ ^ (1 - θ) ≤ K * r ^ (1 - θ) := by
    rcases h with h | h
    · calc ℓ ^ (1 - θ) ≤ ℓ ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hℓ (by linarith)
        _ = ℓ := Real.rpow_one ℓ
        _ ≤ K := h
        _ ≤ K * r ^ (1 - θ) := by nlinarith
    · calc ℓ ^ (1 - θ) ≤ (K * r) ^ (1 - θ) := Real.rpow_le_rpow hℓ0.le h (by linarith)
        _ = K ^ (1 - θ) * r ^ (1 - θ) := Real.mul_rpow hK0.le hr0.le
        _ ≤ K * r ^ (1 - θ) := by
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            calc K ^ (1 - θ) ≤ K ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hK (by linarith)
              _ = K := Real.rpow_one K
  calc ℓ = ℓ ^ θ * ℓ ^ (1 - θ) := hsplit
    _ ≤ ℓ ^ θ * (K * r ^ (1 - θ)) := mul_le_mul_of_nonneg_left hkey (by positivity)
    _ = _ := by ring

/-- The geometry of a Hölder pair: the pair is at path distance `≤ 1` and the scale of `x'` is at
least `ℓ(x)/L`. -/
theorem holder_pair_facts (G : GeneratingSet d L N₀ k ϱ) (hϱ : 1 ≤ ϱ) {x : Torus d (N₀ * L ^ k)}
    (hx : x ∈ G.Ω 1) {z : Fin d → ℤ} (hx' : liftPt x z ∈ G.Ω 1)
    (hpair : (G.layerIndex x = 1 ∧ G.pathDist x (liftPt x z) ≤ ENNReal.ofReal 1) ∨
      (2 ≤ G.layerIndex x ∧ (d : ℝ) * ‖z‖ ≤ (L : ℝ) ^ (G.layerIndex x - 1))) :
    G.pathDist (liftPt x z) x ≤ ENNReal.ofReal 1 ∧
      G.spacing x ≤ L * G.spacing (liftPt x z) := by
  obtain ⟨hj1, hjk, hxl⟩ := G.layerIndex_spec hx
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne L)
  rcases hpair with ⟨hj, hdist⟩ | ⟨hj2, hz⟩
  · refine ⟨by rw [GeneratingSet.pathDist_comm]; exact hdist, ?_⟩
    obtain ⟨hm1, hmk, -⟩ := G.layerIndex_spec hx'
    have h1 : (1 : ℝ) ≤ G.spacing (liftPt x z) := one_le_pow₀ hL1
    unfold GeneratingSet.spacing at h1 ⊢
    rw [hj, pow_one]
    nlinarith
  · obtain ⟨-, hlo, -⟩ := lift_mem_layers G hϱ hj2 hjk hxl hz
    obtain ⟨-, hpd⟩ := pathDist_lift_le G hϱ hj2 hjk hxl hz
    have hLpos : (0 : ℝ) < (L : ℝ) ^ (G.layerIndex x - 1) := by positivity
    refine ⟨hpd.trans (ENNReal.ofReal_le_ofReal ?_), ?_⟩
    · rw [div_le_one hLpos]; exact hz
    · have e : G.spacing x = L * (L : ℝ) ^ (G.layerIndex x - 1) := by
        unfold GeneratingSet.spacing
        rw [← pow_succ']; congr 1; omega
      rw [e]
      exact mul_le_mul_of_nonneg_left hlo (by linarith)

namespace PtSetting

variable {G : GeneratingSet d L N₀ k ϱ} (S : PtSetting G 1)

theorem spacing_mul_norm_le_U {y : Torus d (N₀ * L ^ k)} (ν : Fin d) :
    G.spacing y * ‖S.ut (y + Pi.single ν 1) - S.ut y‖ ≤ S.U y := by
  have hsp := spacing_pos G (x := y)
  have h1 : ‖S.ut (y + Pi.single ν 1) - S.ut y‖ ≤ ∑ μ : Fin d, ‖S.ut (y + Pi.single μ 1) - S.ut y‖ := by
    have h := Finset.sum_le_sum_of_subset_of_nonneg (f := fun μ : Fin d => ‖S.ut (y + Pi.single μ 1) - S.ut y‖)
      (Finset.subset_univ {ν}) (fun _ _ _ => norm_nonneg _)
    simpa using h
  have h2 := mul_le_mul_of_nonneg_left h1 hsp.le
  unfold PtSetting.U
  exact h2.trans (le_add_of_nonneg_left (norm_nonneg _))

/-- **Case 1 / large distance.** -/
theorem holder_caseII {x : Torus d (N₀ * L ^ k)} (hx : x ∈ G.Ω 1) {z : Fin d → ℤ}
    (hx' : liftPt x z ∈ G.Ω 1) (hd1 : G.pathDist (liftPt x z) x ≤ ENNReal.ofReal 1)
    (hsp : G.spacing x ≤ L * G.spacing (liftPt x z)) (ν : Fin d) {M : ℝ}
    (hM : ∀ q ∈ G.Ω 1, G.pathDist q x ≤ ENNReal.ofReal (2 * d + 1) → S.U q ≤ M) :
    G.spacing x * ‖(S.ut (liftPt x z + Pi.single ν 1) - S.ut (liftPt x z)) -
        (S.ut (x + Pi.single ν 1) - S.ut x)‖ ≤ (L + 1) * M := by
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hMx : S.U x ≤ M := hM x hx (by rw [GeneratingSet.pathDist_self hx]; exact bot_le)
  have hMx' : S.U (liftPt x z) ≤ M := hM _ hx' (hd1.trans (ENNReal.ofReal_le_ofReal (by
    have : (0 : ℝ) ≤ d := hd0
    linarith)))
  have h1 := S.spacing_mul_norm_le_U (y := x) ν
  have h2 := S.spacing_mul_norm_le_U (y := liftPt x z) ν
  have hsx := spacing_pos G (x := x)
  have hsx' := spacing_pos G (x := liftPt x z)
  have hn := norm_sub_le (S.ut (liftPt x z + Pi.single ν 1) - S.ut (liftPt x z))
    (S.ut (x + Pi.single ν 1) - S.ut x)
  have hL0 : (0 : ℝ) ≤ L := Nat.cast_nonneg L
  calc G.spacing x * ‖(S.ut (liftPt x z + Pi.single ν 1) - S.ut (liftPt x z)) -
        (S.ut (x + Pi.single ν 1) - S.ut x)‖ ≤ G.spacing x * (‖S.ut (liftPt x z + Pi.single ν 1) -
          S.ut (liftPt x z)‖ + ‖S.ut (x + Pi.single ν 1) - S.ut x‖) :=
        mul_le_mul_of_nonneg_left hn hsx.le
    _ = G.spacing x * ‖S.ut (liftPt x z + Pi.single ν 1) - S.ut (liftPt x z)‖ +
        G.spacing x * ‖S.ut (x + Pi.single ν 1) - S.ut x‖ := by ring
    _ ≤ L * M + M := by
        refine add_le_add ?_ (h1.trans hMx)
        calc G.spacing x * ‖S.ut (liftPt x z + Pi.single ν 1) - S.ut (liftPt x z)‖ ≤
            (L * G.spacing (liftPt x z)) * ‖S.ut (liftPt x z + Pi.single ν 1) - S.ut (liftPt x z)‖ :=
              mul_le_mul_of_nonneg_right hsp (norm_nonneg _)
          _ = L * (G.spacing (liftPt x z) * ‖S.ut (liftPt x z + Pi.single ν 1) -
              S.ut (liftPt x z)‖) := by ring
          _ ≤ L * M := mul_le_mul_of_nonneg_left (h2.trans hMx') hL0
    _ = _ := by ring

end PtSetting

end Balaban.Multiscale
