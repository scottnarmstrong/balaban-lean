/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.CutPointwiseWallBall
public import Balaban.Multiscale.PointwiseCase2b
public import Balaban.Green.Lattice.LocGreenSums

/-!
# The source part of the Loc sums on a folded ball (VMOD-9 §3, (3.6) and (3.7))

For a ball `B_R` of the local fold `P(z) = foldMap (p₀ + z)` around a layer-`j` point `x`, the set
`A_F = {z ∈ B_R : f̃(P z) ≠ 0}` has at most `2^d L^{d j'}` points (the fold has multiplicity `≤ 2^d`),
and, if it is nonempty, `d_H(x, y') ≤ 2d + 1` and `j ≤ j' + 1`.
`cubeFold_source_green_sum` combines this with the lattice Green sum bound.
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.LatticeGreen Balaban.Reflection Finset Matrix

variable {d L N₀ k : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}

omit [NeZero N₀] [NeZero L] in
/-- The separation hypothesis forces `2 d + 1 < ϱ - 1`. -/
theorem two_mul_add_one_lt_of_sep (hd : 3 ≤ d) (hL : 3 ≤ L) (hϱ : 1 ≤ ϱ)
    (hsep : (L : ℝ) ^ d ≤ Real.exp (agmonRate d / 2 * (ϱ - 1))) : 2 * (d : ℝ) + 1 < ϱ - 1 := by
  have hL3 : (3 : ℝ) ≤ L := by exact_mod_cast hL
  have hd0 : 0 < d := by omega
  have h1 : Real.exp (d : ℝ) ≤ (L : ℝ) ^ d := by
    rw [← Real.exp_one_pow]
    refine pow_le_pow_left₀ (Real.exp_pos _).le ?_ d
    have := Real.exp_one_lt_d9
    linarith
  have h2 := h1.trans hsep
  rw [Real.exp_le_exp] at h2
  have hε := agmonRate_le hd0
  have hd3 : (3 : ℝ) ≤ d := by exact_mod_cast hd
  by_contra hcon
  push Not at hcon
  have : agmonRate d / 2 * (ϱ - 1) ≤ 1 / 64 * (ϱ - 1) := by
    have : agmonRate d / 2 ≤ 1 / 64 := by linarith
    exact mul_le_mul_of_nonneg_right this (by linarith)
  nlinarith

/-- **The source set of a folded ball** (VMOD-9 (3.6)--(3.7), geometric part). -/
theorem cubeFold_fsum_data {G : GeneratingSet d L N₀ k ϱ} (hd : 3 ≤ d) (hL : 3 ≤ L)
    (hϱ : 1 ≤ ϱ) (hsep : (L : ℝ) ^ d ≤ Real.exp (agmonRate d / 2 * (ϱ - 1)))
    {j j' : ℕ} (hj2 : 2 ≤ j) (hjk : j ≤ k) (hj'1 : 1 ≤ j') (hj'k : j' ≤ k)
    {x y' : Torus d (N₀ * L ^ k)} (hx : x ∈ G.layer j) (hy' : y' ∈ G.layer j')
    {f : G.Ω 1 → ℂ}
    (hsupp : ∀ z : G.Ω 1, f z ≠ 0 → jBlock d L N₀ k j' z = jBlock d L N₀ k j' y')
    (S : ℕ) [NeZero S] (c : Fin d → ℕ) (p0 : Torus d (2 * S))
    (hp0 : foldMap (N₀ * L ^ k) S (2 * S) c p0 = x) (hSℓ : S < N₀ * L ^ k) {R : ℝ} (hR : 0 ≤ R)
    (hRd : (d : ℝ) * R ≤ (L : ℝ) ^ (j - 1)) (hRS : R < S) :
    ∃ A : Finset (Fin d → ℤ), A ⊆ latticeBall (0 : Fin d → ℤ) R ∧
      A.card ≤ 2 ^ d * (L ^ j') ^ d ∧
      (∀ z ∈ latticeBall (0 : Fin d → ℤ) R, z ∉ A →
        zeroExt (G.Ω 1) f (cubeFoldPt N₀ L k S c p0 z) = 0) ∧
      (A.Nonempty → G.pathDist x y' ≤ ENNReal.ofReal (2 * d + 1) ∧ j ≤ j' + 1) := by
  classical
  have hmemz : ∀ z ∈ latticeBall (0 : Fin d → ℤ) R, ‖z‖ ≤ R := fun z hz => by
    have := (mem_latticeBall hR).1 hz; rwa [sub_zero] at this
  have hne : ∀ p, zeroExt (G.Ω 1) f p ≠ 0 →
      p ∈ G.Ω 1 ∧ jBlock d L N₀ k j' p = jBlock d L N₀ k j' y' := by
    intro p hp
    unfold zeroExt at hp
    split_ifs at hp with h
    · exact ⟨h, hsupp ⟨p, h⟩ hp⟩
    · exact absurd rfl hp
  set A := (latticeBall (0 : Fin d → ℤ) R).filter
    (fun z => zeroExt (G.Ω 1) f (cubeFoldPt N₀ L k S c p0 z) ≠ 0) with hA
  refine ⟨A, Finset.filter_subset _ _, ?_, ?_, ?_⟩
  · have h1 : A.card ≤ 2 ^ d * (A.image (cubeFoldPt N₀ L k S c p0)).card := by
      refine Finset.card_le_mul_card_image A (2 ^ d) fun y _ => ?_
      refine le_trans (Finset.card_le_card ?_) (card_fibre_cubeFoldPt_le S c p0 hSℓ hR hRS y)
      intro z hz
      rw [Finset.mem_filter] at hz ⊢
      exact ⟨(Finset.mem_filter.1 hz.1).1, hz.2⟩
    refine h1.trans (Nat.mul_le_mul_left _ ?_)
    rw [← card_blk G j' hj'k y']
    apply Finset.card_le_card
    intro p hp
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.1 hp
    exact G.mem_blk.2 (hne _ (Finset.mem_filter.1 hz).2).2
  · intro z hz hzA
    by_contra hne'
    exact hzA (Finset.mem_filter.2 ⟨hz, hne'⟩)
  · rintro ⟨z, hz⟩
    obtain ⟨hzb, hzf⟩ := Finset.mem_filter.1 hz
    obtain ⟨hpΩ, hpb⟩ := hne _ hzf
    obtain ⟨h, hh, hP⟩ := cubeFoldPt_disp (N₀ := N₀) (L := L) (k := k) S c p0 z
    rw [cubeFoldPt_zero, hp0] at hP
    have hzd : (d : ℝ) * ‖h‖ ≤ (L : ℝ) ^ (j - 1) :=
      (mul_le_mul_of_nonneg_left (hh.trans (hmemz z hzb)) (Nat.cast_nonneg d)).trans hRd
    have hLpos : (0 : ℝ) < (L : ℝ) ^ (j - 1) := by
      have : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
      positivity
    obtain ⟨-, hpd⟩ := pathDist_lift_le G hϱ hj2 hjk hx hzd
    have hpd1 : G.pathDist x (liftPt x h) ≤ ENNReal.ofReal 1 := by
      rw [GeneratingSet.pathDist_comm]
      refine hpd.trans (ENNReal.ofReal_le_ofReal ?_)
      rw [div_le_one hLpos]
      exact hzd
    rw [← hP] at hpd1
    have hpl : cubeFoldPt N₀ L k S c p0 z ∈ G.layer j' := (G.mem_layer_iff hj'1 hj'k hpb).2 hy'
    have hby := G.pathDist_block_le hj'1 hj'k hy' hpb
    have hxy : G.pathDist x y' ≤ ENNReal.ofReal (2 * d + 1) := by
      refine (G.pathDist_triangle x (cubeFoldPt N₀ L k S c p0 z) y').trans ?_
      rw [GeneratingSet.pathDist_comm (cubeFoldPt N₀ L k S c p0 z) y']
      calc _ ≤ ENNReal.ofReal 1 + ENNReal.ofReal (2 * d) := add_le_add hpd1 hby
        _ = _ := by
          rw [← ENNReal.ofReal_add zero_le_one (by positivity)]
          congr 1; ring
    refine ⟨hxy, ?_⟩
    by_contra hcon
    push Not at hcon
    have hj1 : 1 ≤ j := by omega
    have hsep' := G.pathDist_separation hϱ hj1 hj'1 hjk hj'k hx hy'
    have h1 := hsep'.trans hxy
    rw [ENNReal.ofReal_le_ofReal_iff (by positivity)] at h1
    have h2 : (1 : ℝ) ≤ ((j - j' + (j' - j) - 1 : ℕ) : ℝ) := by
      have : 1 ≤ j - j' + (j' - j) - 1 := by omega
      exact_mod_cast this
    have h3 := two_mul_add_one_lt_of_sep hd hL hϱ hsep
    nlinarith

/-- **VMOD-9 (3.6), (3.7).** The source part of the Loc sums on a folded ball. -/
theorem cubeFold_source_green_sum {G : GeneratingSet d L N₀ k ϱ} (hd : 3 ≤ d) (hL : 3 ≤ L)
    (hϱ : 1 ≤ ϱ) (hsep : (L : ℝ) ^ d ≤ Real.exp (agmonRate d / 2 * (ϱ - 1)))
    {cG : ℝ} (hcG : 0 ≤ cG)
    (hG : ∀ R : ℝ, 0 ≤ R → ∀ A : Finset (Fin d → ℤ),
      A.card ≤ (latticeBall (0 : Fin d → ℤ) R).card →
      (∑ z ∈ A, latticeGreen d (0 - z) ≤ cG * (R + 1) ^ 2) ∧
      (∀ ν : Fin d, ∑ z ∈ A, |latticeGreen d (0 - z + Pi.single ν 1) - latticeGreen d (0 - z)| ≤
        cG * (R + 1)))
    {j₀ j' : ℕ} (hj01 : 1 ≤ j₀) (hjk : j₀ + 1 ≤ k) (hj'1 : 1 ≤ j') (hj'k : j' ≤ k)
    {x y' : Torus d (N₀ * L ^ k)} (hx : x ∈ G.layer (j₀ + 1)) (hy' : y' ∈ G.layer j')
    {f : G.Ω 1 → ℂ}
    (hsupp : ∀ z : G.Ω 1, f z ≠ 0 → jBlock d L N₀ k j' z = jBlock d L N₀ k j' y')
    (S : ℕ) [NeZero S] (c : Fin d → ℕ) (p0 : Torus d (2 * S))
    (hp0 : foldMap (N₀ * L ^ k) S (2 * S) c p0 = x) (hSℓ : S < N₀ * L ^ k) {R : ℝ} (hR : 0 ≤ R)
    (hRd : (d : ℝ) * R ≤ (L : ℝ) ^ j₀) (hRS : R < S) {Mf : ℝ} (hMf0 : 0 ≤ Mf)
    (hMf : ∀ i, ‖f i‖ ≤ Mf) {t : ℝ} (ht : ENNReal.ofReal t ≤ G.pathDist x y') :
    ∃ A : Finset (Fin d → ℤ),
      (∀ F : (Fin d → ℤ) → ℝ, (∀ z, 0 ≤ F z) →
        ∑ z ∈ latticeBall (0 : Fin d → ℤ) R,
            F z * ‖zeroExt (G.Ω 1) f (cubeFoldPt N₀ L k S c p0 z)‖ ≤
          Mf * ∑ z ∈ A, F z) ∧
      (Mf * ∑ z ∈ A, latticeGreen d (0 - z) + (L : ℝ) ^ (j₀ + 1) *
        ∑ ν : Fin d, (Mf * ∑ z ∈ A, |latticeGreen d (0 - z + Pi.single ν 1) -
          latticeGreen d (0 - z)|) ≤
        cG * (9 + 3 * d * L) * Real.exp (agmonRate d / 2 * (2 * d + 1)) *
          Real.exp (-(agmonRate d / 2 * t)) * ((L : ℝ) ^ (2 * j') * Mf)) := by
  have hd0 : 0 < d := by omega
  have hε0 := agmonRate_pos hd0
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd0
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne L)
  have hj2 : 2 ≤ j₀ + 1 := by omega
  obtain ⟨A, hAsub, hAcard, hAvan, hAne⟩ := cubeFold_fsum_data hd hL hϱ hsep hj2 hjk hj'1 hj'k hx
    hy' hsupp S c p0 hp0 hSℓ hR (by simpa only [Nat.add_sub_cancel] using hRd) hRS
  have hnorm : ∀ p : Torus d (N₀ * L ^ k), ‖zeroExt (G.Ω 1) f p‖ ≤ Mf := by
    intro p
    unfold zeroExt
    split_ifs with h
    · exact hMf _
    · simpa using hMf0
  refine ⟨A, ?_, ?_⟩
  · intro F hF
    have h1 : ∑ z ∈ latticeBall (0 : Fin d → ℤ) R,
        F z * ‖zeroExt (G.Ω 1) f (cubeFoldPt N₀ L k S c p0 z)‖ =
        ∑ z ∈ A, F z * ‖zeroExt (G.Ω 1) f (cubeFoldPt N₀ L k S c p0 z)‖ :=
      (Finset.sum_subset hAsub (fun z hz hnA => by rw [hAvan z hz hnA]; simp)).symm
    rw [h1, Finset.mul_sum]
    refine Finset.sum_le_sum fun z _ => ?_
    rw [mul_comm Mf]
    exact mul_le_mul_of_nonneg_left (hnorm _) (hF z)
  · set Rf : ℝ := (((2 * L ^ j' : ℕ)) : ℝ) with hRf
    have hRf0 : 0 ≤ Rf := Nat.cast_nonneg _
    have hAcard' : A.card ≤ (latticeBall (0 : Fin d → ℤ) Rf).card := by
      rw [hRf, card_latticeBall_nat]
      refine hAcard.trans ?_
      rw [← mul_pow]
      exact Nat.pow_le_pow_left (by omega) d
    obtain ⟨hGA, hGAν⟩ := hG Rf hRf0 A hAcard'
    have hnn : 0 ≤ cG * (9 + 3 * d * L) * Real.exp (agmonRate d / 2 * (2 * d + 1)) *
        Real.exp (-(agmonRate d / 2 * t)) * ((L : ℝ) ^ (2 * j') * Mf) := by positivity
    by_cases hAn : A.Nonempty
    · obtain ⟨hpd, hjj⟩ := hAne hAn
      have ht_le : t ≤ 2 * d + 1 := by
        have := ht.trans hpd
        rwa [ENNReal.ofReal_le_ofReal_iff (by positivity)] at this
      have hexpo : 1 ≤ Real.exp (agmonRate d / 2 * (2 * d + 1)) *
          Real.exp (-(agmonRate d / 2 * t)) := by
        rw [← Real.exp_add]
        apply Real.one_le_exp
        nlinarith
      have hLj1 : (1 : ℝ) ≤ (L : ℝ) ^ j' := one_le_pow₀ hL1
      have hRf1 : Rf + 1 ≤ 3 * (L : ℝ) ^ j' := by rw [hRf]; push_cast; linarith
      have hLjj : (L : ℝ) ^ (j₀ + 1) ≤ (L : ℝ) * (L : ℝ) ^ j' := by
        rw [← pow_succ']
        exact pow_le_pow_right₀ hL1 hjj
      have hsC : ∑ z ∈ A, latticeGreen d (0 - z) ≤ cG * (9 * ((L : ℝ) ^ j') ^ 2) :=
        hGA.trans (calc cG * (Rf + 1) ^ 2 ≤ cG * (3 * (L : ℝ) ^ j') ^ 2 :=
              mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hRf1 2) hcG
          _ = _ := by ring)
      have hsD : ∀ ν : Fin d, ∑ z ∈ A, |latticeGreen d (0 - z + Pi.single ν 1) -
          latticeGreen d (0 - z)| ≤ cG * (3 * (L : ℝ) ^ j') := fun ν =>
        (hGAν ν).trans (mul_le_mul_of_nonneg_left hRf1 hcG)
      have h1 : Mf * ∑ z ∈ A, latticeGreen d (0 - z) ≤ Mf * (cG * (9 * ((L : ℝ) ^ j') ^ 2)) :=
        mul_le_mul_of_nonneg_left hsC hMf0
      have h2 : ∑ ν : Fin d, (Mf * ∑ z ∈ A, |latticeGreen d (0 - z + Pi.single ν 1) -
          latticeGreen d (0 - z)|) ≤ d * (Mf * (cG * (3 * (L : ℝ) ^ j'))) := by
        calc _ ≤ ∑ _ν : Fin d, (Mf * (cG * (3 * (L : ℝ) ^ j'))) :=
              Finset.sum_le_sum fun ν _ => mul_le_mul_of_nonneg_left (hsD ν) hMf0
          _ = _ := by simp
      have h3 : (L : ℝ) ^ (j₀ + 1) * ∑ ν : Fin d, (Mf * ∑ z ∈ A, |latticeGreen d (0 - z +
          Pi.single ν 1) - latticeGreen d (0 - z)|) ≤
          ((L : ℝ) * (L : ℝ) ^ j') * (d * (Mf * (cG * (3 * (L : ℝ) ^ j')))) :=
        mul_le_mul hLjj h2 (Finset.sum_nonneg fun _ _ => by positivity) (by positivity)
      have h4 : (L : ℝ) ^ (2 * j') = ((L : ℝ) ^ j') ^ 2 := by rw [pow_mul']
      have h5 : Mf * (cG * (9 * ((L : ℝ) ^ j') ^ 2)) + ((L : ℝ) * (L : ℝ) ^ j') *
          (d * (Mf * (cG * (3 * (L : ℝ) ^ j')))) =
          cG * (9 + 3 * d * L) * ((L : ℝ) ^ (2 * j') * Mf) := by rw [h4]; ring
      calc _ ≤ Mf * (cG * (9 * ((L : ℝ) ^ j') ^ 2)) + ((L : ℝ) * (L : ℝ) ^ j') *
            (d * (Mf * (cG * (3 * (L : ℝ) ^ j')))) := add_le_add h1 h3
        _ = cG * (9 + 3 * d * L) * ((L : ℝ) ^ (2 * j') * Mf) := h5
        _ = cG * (9 + 3 * d * L) * ((L : ℝ) ^ (2 * j') * Mf) * 1 := by ring
        _ ≤ cG * (9 + 3 * d * L) * ((L : ℝ) ^ (2 * j') * Mf) *
            (Real.exp (agmonRate d / 2 * (2 * d + 1)) * Real.exp (-(agmonRate d / 2 * t))) :=
            mul_le_mul_of_nonneg_left hexpo (by positivity)
        _ = _ := by ring
    · rw [Finset.not_nonempty_iff_eq_empty.1 hAn]
      simpa using hnn

end Balaban.Localization
