/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Multiscale.PointwiseCase2a

/-!
# Lemma P, Case 2, step 2: the source part

For `x` in layer `j ≥ 2` and the lifted ball `B_R(x)` with `d R ≤ L^{j-1}`, the source `f̃` contributes
to the Loc sums only through the set `A` of lifted sites in the source block.  `A` has at most
`ℓ_{j'}^d` points and, if it is nonempty, `d(x, y') ≤ 2 d + 1` and `j ≤ j' + 1`.
-/

@[expose] public section

noncomputable section

namespace Balaban.Multiscale

open Finset Matrix Balaban Balaban.LatticeGreen

variable {d L N₀ k : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}

namespace PtSetting

variable {G : GeneratingSet d L N₀ k ϱ} (S : PtSetting G)

theorem norm_ft_le {Mf : ℝ} (hMf0 : 0 ≤ Mf) (hMf : ∀ i, ‖S.f i‖ ≤ Mf) (p : Torus d (N₀ * L ^ k)) :
    ‖S.ft p‖ ≤ Mf := by
  unfold ft zeroExt
  split_ifs with h
  · exact hMf _
  · simpa using hMf0

theorem ft_ne_zero {p : Torus d (N₀ * L ^ k)} (hp : S.ft p ≠ 0) :
    p ∈ G.Ω 1 ∧ jBlock d L N₀ k S.j' p = jBlock d L N₀ k S.j' S.y' := by
  unfold ft zeroExt at hp
  split_ifs at hp with h
  · exact ⟨h, S.hsupp ⟨p, h⟩ hp⟩
  · exact absurd rfl hp

theorem fsum_data {j : ℕ} (hj2 : 2 ≤ j) (hjk : j ≤ k) {x : Torus d (N₀ * L ^ k)}
    (hx : x ∈ G.layer j) {R : ℝ} (hR : 0 ≤ R) (hRd : (d : ℝ) * R ≤ (L : ℝ) ^ (j - 1)) :
    ∃ A : Finset (Fin d → ℤ), A ⊆ latticeBall (0 : Fin d → ℤ) R ∧
      A.card ≤ (L ^ S.j') ^ d ∧
      (∀ z ∈ latticeBall (0 : Fin d → ℤ) R, z ∉ A → S.ft (liftPt x z) = 0) ∧
      (A.Nonempty → G.pathDist x S.y' ≤ ENNReal.ofReal (2 * d + 1) ∧ j ≤ S.j' + 1) := by
  classical
  have hmemz : ∀ z ∈ latticeBall (0 : Fin d → ℤ) R, ‖z‖ ≤ R := fun z hz => by
    have := (mem_latticeBall hR).1 hz; rwa [sub_zero] at this
  have hinj : Set.InjOn (liftPt (d := d) (L := L) (N₀ := N₀) (k := k) x)
      (latticeBall (0 : Fin d → ℤ) R : Set (Fin d → ℤ)) := by
    intro z hz z' hz' h
    exact liftPt_injOn x (hmemz z hz) (hmemz z' hz')
      (two_mul_lt_side S.hL (by omega) hjk (by have := S.hd; omega) hR hRd) h
  set A := (latticeBall (0 : Fin d → ℤ) R).filter (fun z => S.ft (liftPt x z) ≠ 0) with hA
  refine ⟨A, Finset.filter_subset _ _, ?_, ?_, ?_⟩
  · have h1 : A.card = (A.image (liftPt x)).card :=
      (Finset.card_image_of_injOn (hinj.mono (by
        intro z hz; exact Finset.filter_subset _ _ hz))).symm
    rw [h1, ← card_blk G S.j' S.hj'k S.y']
    apply Finset.card_le_card
    intro p hp
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.1 hp
    exact G.mem_blk.2 (S.ft_ne_zero (Finset.mem_filter.1 hz).2).2
  · intro z hz hzA
    by_contra hne
    exact hzA (Finset.mem_filter.2 ⟨hz, hne⟩)
  · rintro ⟨z, hz⟩
    obtain ⟨hzb, hzf⟩ := Finset.mem_filter.1 hz
    obtain ⟨hpΩ, hpb⟩ := S.ft_ne_zero hzf
    have hzd : (d : ℝ) * ‖z‖ ≤ (L : ℝ) ^ (j - 1) :=
      (mul_le_mul_of_nonneg_left (hmemz z hzb) (Nat.cast_nonneg d)).trans hRd
    have hLpos : (0 : ℝ) < (L : ℝ) ^ (j - 1) := by
      have : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
      positivity
    obtain ⟨-, hpd⟩ := pathDist_lift_le G S.hϱ hj2 hjk hx hzd
    have hpd1 : G.pathDist x (liftPt x z) ≤ ENNReal.ofReal 1 := by
      rw [GeneratingSet.pathDist_comm]
      refine hpd.trans (ENNReal.ofReal_le_ofReal ?_)
      rw [div_le_one hLpos]
      exact hzd
    have hpl : liftPt x z ∈ G.layer S.j' := (G.mem_layer_iff S.hj'1 S.hj'k hpb).2 S.hy'
    have hby := G.pathDist_block_le S.hj'1 S.hj'k S.hy' hpb
    have hxy : G.pathDist x S.y' ≤ ENNReal.ofReal (2 * d + 1) := by
      refine (G.pathDist_triangle x (liftPt x z) S.y').trans ?_
      rw [GeneratingSet.pathDist_comm (liftPt x z) S.y']
      calc _ ≤ ENNReal.ofReal 1 + ENNReal.ofReal (2 * d) := add_le_add hpd1 hby
        _ = _ := by
          rw [← ENNReal.ofReal_add zero_le_one (by positivity)]
          congr 1; ring
    refine ⟨hxy, ?_⟩
    by_contra hcon
    push Not at hcon
    obtain ⟨hj1, -⟩ : 1 ≤ j ∧ True := ⟨by omega, trivial⟩
    have hsep := G.pathDist_separation S.hϱ hj1 S.hj'1 hjk S.hj'k hx S.hy'
    have h1 := hsep.trans hxy
    rw [ENNReal.ofReal_le_ofReal_iff (by positivity)] at h1
    have h2 : (1 : ℝ) ≤ ((j - S.j' + (S.j' - j) - 1 : ℕ) : ℝ) := by
      have : 1 ≤ j - S.j' + (S.j' - j) - 1 := by omega
      exact_mod_cast this
    have h3 := rho_large S
    nlinarith [S.hϱ]

end PtSetting

end Balaban.Multiscale
