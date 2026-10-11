/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Multiscale.PointwiseCase1

/-!
# Lemma P, Case 2, step 1: Lemma Loc on the lifted ball

* `loc_lift`: Lemma Loc (a), (b) for the lift `z ↦ v(c + z)` of a torus field `v`;
* `g_bound`: (4.4) for the lifted Poisson right-hand side at the sites of the lifted ball.
-/

@[expose] public section

noncomputable section

namespace Balaban.Multiscale

open Finset Matrix Balaban Balaban.LatticeGreen

variable {d L N₀ k : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}

/-- Lemma Loc (a), (b) for a lifted torus field, centred at the lift centre. -/
theorem loc_lift (hd : 3 ≤ d) :
    ∃ Ca Cb : ℝ, 0 ≤ Ca ∧ 0 ≤ Cb ∧
      ∀ {L N₀ k : ℕ} [NeZero N₀] [NeZero L] (c : Torus d (N₀ * L ^ k))
        (v : Torus d (N₀ * L ^ k) → ℂ) {ρ : ℝ}, 8 ≤ ρ →
        (‖v c‖ ≤ Ca * ρ ^ (-(d : ℝ) / 2) *
            Real.sqrt (∑ w ∈ latticeBall (0 : Fin d → ℤ) (2 * ρ), ‖v (liftPt c w)‖ ^ 2) +
          ∑ z ∈ latticeBall (0 : Fin d → ℤ) (2 * ρ), latticeGreen d (0 - z) *
            ‖negLap (fun w => v (liftPt c w)) z‖) ∧
        (∀ ν : Fin d, ‖v (c + Pi.single ν 1) - v c‖ ≤ Cb * ρ ^ (-1 - (d : ℝ) / 2) *
            Real.sqrt (∑ w ∈ latticeBall (0 : Fin d → ℤ) (2 * ρ), ‖v (liftPt c w)‖ ^ 2) +
          ∑ z ∈ latticeBall (0 : Fin d → ℤ) (2 * ρ),
            |latticeGreen d (0 - z + Pi.single ν 1) - latticeGreen d (0 - z)| *
              ‖negLap (fun w => v (liftPt c w)) z‖) := by
  obtain ⟨Ca, hCa, ha⟩ := lemma_loc_a hd
  obtain ⟨Cb, hCb, hb⟩ := lemma_loc_b hd
  refine ⟨Ca, Cb, hCa, hCb, fun {L N₀ k} _ _ c v {ρ} hρ => ⟨?_, fun ν => ?_⟩⟩
  · have h := ha ρ hρ 0 0 (by simp; positivity) (fun w => v (liftPt c w))
      (fun w => negLap (fun w => v (liftPt c w)) w) (fun z _ => rfl)
    simpa [liftPt_zero] using h
  · have h := hb ρ hρ 0 0 (by simp; positivity) ν (fun w => v (liftPt c w))
      (fun w => negLap (fun w => v (liftPt c w)) w) (fun z _ => rfl)
    have e : liftPt c (0 + Pi.single ν 1) = c + Pi.single ν 1 := by
      rw [zero_add]
      have := liftPt_add_single c 0 ν
      rw [zero_add, liftPt_zero] at this
      exact this
    simp only [e, liftPt_zero] at h
    simpa using h

namespace PtSetting

variable {G : GeneratingSet d L N₀ k ϱ} {Λ : ℝ} (S : PtSetting G Λ)

/-- The zero extension of the source. -/
def ft : Torus d (N₀ * L ^ k) → ℂ := zeroExt (G.Ω 1) S.f

/-- **(4.4) on the lifted ball.** -/
theorem g_bound {j : ℕ} (hj2 : 2 ≤ j) (hjk : j ≤ k) {x : Torus d (N₀ * L ^ k)}
    (hx : x ∈ G.layer j) {z : Fin d → ℤ} (hz : (d : ℝ) * ‖z‖ ≤ (L : ℝ) ^ (j - 1)) {M : ℝ}
    (hM0 : 0 ≤ M)
    (hM : ∀ q ∈ G.Ω 1, G.pathDist q x ≤ ENNReal.ofReal (2 * d + 1) → ‖S.ut q‖ ≤ M) :
    ‖negLap (fun w => S.ut (liftPt x w)) z‖ ≤
      ‖S.ft (liftPt x z)‖ + (3 + Λ) * (((L : ℝ) ^ (j - 1)) ^ 2)⁻¹ * M := by
  have hLpos : (0 : ℝ) < (L : ℝ) ^ (j - 1) := by
    have : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
    positivity
  obtain ⟨hpΩ, hlo, -⟩ := lift_mem_layers G S.hϱ hj2 hjk hx hz
  obtain ⟨-, hpd⟩ := pathDist_lift_le G S.hϱ hj2 hjk hx hz
  have hpd1 : G.pathDist (liftPt x z) x ≤ ENNReal.ofReal 1 := by
    refine hpd.trans (ENNReal.ofReal_le_ofReal ?_)
    rw [div_le_one hLpos]
    exact hz
  set p := liftPt x z with hp
  rw [negLap_liftPt]
  obtain ⟨hm1, hmk, hpl⟩ := G.layerIndex_spec hpΩ
  have hM' : ∀ q, jBlock d L N₀ k (G.layerIndex p) q = jBlock d L N₀ k (G.layerIndex p) p →
      ‖zeroExt (G.Ω 1) S.u q‖ ≤ M := by
    intro q hq
    have hql : q ∈ G.layer (G.layerIndex p) := (G.mem_layer_iff hm1 hmk hq).2 hpl
    have hqΩ : q ∈ G.Ω 1 := G.layer_subset hm1 hmk hql
    have h1 := G.pathDist_block_le hm1 hmk hpl hq
    rw [GeneratingSet.pathDist_comm] at h1
    have h2 : G.pathDist q x ≤ ENNReal.ofReal (2 * d + 1) := by
      refine (G.pathDist_triangle q p x).trans ?_
      calc _ ≤ ENNReal.ofReal (2 * d) + ENNReal.ofReal 1 := add_le_add h1 hpd1
        _ = _ := by
          rw [← ENNReal.ofReal_add (by positivity) zero_le_one]
    exact hM q hqΩ h2
  have hb := laplacian_bound G S.hν0 S.hν1 S.ha S.hα S.hu hpΩ hM0 hM'
  refine hb.trans ?_
  have hsp0 : 0 < G.spacing p := spacing_pos G
  have h2 : ((G.spacing p) ^ 2)⁻¹ ≤ (((L : ℝ) ^ (j - 1)) ^ 2)⁻¹ := by
    apply inv_anti₀ (by positivity)
    exact pow_le_pow_left₀ hLpos.le hlo 2
  have hΛ0 : 0 ≤ Λ := le_trans (by have := S.hν0; positivity) S.hν1
  unfold ft
  gcongr

end PtSetting

end Balaban.Multiscale
