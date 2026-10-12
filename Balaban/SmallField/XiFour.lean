/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.SmallField.XiComposeField
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# (Ξ4) for the composed field: the second difference

`notes/phase1/SMALLFIELD.md` v3 §1.8.  Block geometry (translation of blocks, tilde-neighbours),
the translation formula for the block mean `Q_n`, and the second-difference bound of the composed
field of a member of `Ξ^c_k(𝔹'; 1, ε)` across four cells of one layer of `𝔹`.
-/

@[expose] public section

namespace Balaban.SmallField

open Balaban Balaban.Background Balaban.Multiscale Matrix Finset

variable {d L N₀ k : ℕ} [NeZero N₀] [NeZero L] {ϱ ϱ' : ℝ}

section BlockGeometry

/-- Moving by `i ≤ N` steps in one direction changes the block coordinate by at most `1`. -/
theorem blockCoord_add_nat {ℓ N M : ℕ} [NeZero ℓ] (hℓ : ℓ = N * M) (hN : 0 < N) (a : ZMod ℓ)
    (i : ℕ) (hi : i ≤ N) :
    blockCoord N M (a + (i : ZMod ℓ)) = blockCoord N M a ∨
      blockCoord N M (a + (i : ZMod ℓ)) = blockCoord N M a + 1 := by
  subst hℓ
  have h1 : a + (i : ZMod (N * M)) = ((a.val + i : ℕ) : ZMod (N * M)) := by
    push_cast; rw [ZMod.natCast_zmod_val]
  rw [h1]
  unfold blockCoord
  rw [ZMod.val_natCast, Nat.mod_mul_right_div_self, ZMod.natCast_mod]
  have h2 : a.val / N ≤ (a.val + i) / N := Nat.div_le_div_right (by omega)
  have h3 : (a.val + i) / N ≤ a.val / N + 1 := by
    have : (a.val + i) / N ≤ (a.val + N) / N := Nat.div_le_div_right (by omega)
    rwa [Nat.add_div_right _ hN] at this
  rcases Nat.eq_or_lt_of_le h2 with h | h
  · left; rw [← h]
  · right
    have : (a.val + i) / N = a.val / N + 1 := by omega
    rw [this]; push_cast; rfl

variable {n : ℕ}

theorem jBlock_add_nat (hnk : n ≤ k) (μ : Fin d) (y : Torus d (N₀ * L ^ k)) (i : ℕ)
    (hi : i ≤ L ^ n) :
    jBlock d L N₀ k n (y + Pi.single μ (i : ZMod (N₀ * L ^ k))) = jBlock d L N₀ k n y ∨
      jBlock d L N₀ k n (y + Pi.single μ (i : ZMod (N₀ * L ^ k))) =
        jBlock d L N₀ k n y + Pi.single μ 1 := by
  have hN : 0 < L ^ n := Nat.pos_of_ne_zero (NeZero.ne _)
  rcases blockCoord_add_nat (side_eq (N₀ := N₀) (L := L) hnk) hN (y μ) i hi with h | h
  · left
    funext j
    by_cases hj : j = μ
    · subst hj; simpa [jBlock, blockMap_apply] using h
    · simp [jBlock, blockMap_apply, hj]
  · right
    funext j
    by_cases hj : j = μ
    · subst hj; simpa [jBlock, blockMap_apply] using h
    · simp [jBlock, blockMap_apply, hj]

theorem jBlock_add_shift (hnk : n ≤ k) (μ : Fin d) (y : Torus d (N₀ * L ^ k)) :
    jBlock d L N₀ k n (y + Pi.single μ ((L ^ n : ℕ) : ZMod (N₀ * L ^ k))) =
      jBlock d L N₀ k n y + Pi.single μ 1 :=
  blockMap_add_shift (side_eq (N₀ := N₀) (L := L) hnk) (Nat.pos_of_ne_zero (NeZero.ne _)) μ y

theorem sum_blk_shift (G : GeneratingSet d L N₀ k ϱ) (hnk : n ≤ k) (μ : Fin d)
    (y : Torus d (N₀ * L ^ k)) (f : Torus d (N₀ * L ^ k) → ℂ) :
    ∑ u ∈ G.blk n (y + Pi.single μ ((L ^ n : ℕ) : ZMod (N₀ * L ^ k))), f u =
      ∑ u ∈ G.blk n y, f (u + Pi.single μ ((L ^ n : ℕ) : ZMod (N₀ * L ^ k))) := by
  refine Finset.sum_nbij' (fun u' => u' - Pi.single μ ((L ^ n : ℕ) : ZMod (N₀ * L ^ k)))
    (fun u => u + Pi.single μ ((L ^ n : ℕ) : ZMod (N₀ * L ^ k))) ?_ ?_ ?_ ?_ ?_
  · intro u' hu'
    rw [GeneratingSet.mem_blk] at hu' ⊢
    have := jBlock_add_shift (d := d) (L := L) (N₀ := N₀) hnk μ
      (u' - Pi.single μ ((L ^ n : ℕ) : ZMod (N₀ * L ^ k)))
    rw [sub_add_cancel, hu', jBlock_add_shift hnk] at this
    exact (add_right_cancel this).symm
  · intro u hu
    rw [GeneratingSet.mem_blk] at hu ⊢
    rw [jBlock_add_shift hnk, hu, jBlock_add_shift hnk]
  · intro u' _; simp
  · intro u _; simp
  · intro u' _; simp

/-- The block mean at a translate by one block side in direction `μ`. -/
theorem blockMean_add_shift (G : GeneratingSet d L N₀ k ϱ) (hnk : n ≤ k) (μ : Fin d)
    (w : Torus d (N₀ * L ^ k) → ℂ) (y : Torus d (N₀ * L ^ k)) :
    blockMean G n w (y + Pi.single μ ((L ^ n : ℕ) : ZMod (N₀ * L ^ k))) =
      blockMean G n (fun u => w (u + Pi.single μ ((L ^ n : ℕ) : ZMod (N₀ * L ^ k)))) y := by
  unfold blockMean
  rw [sum_blk_shift G hnk]

/-- A site `y` and its translate `y + L^n e_ν` lie in adjacent (or equal) `n`-blocks: there are
`p ∈ B_n(y)` and `q ∈ B_n(y + L^n e_ν)` with `q = p + e_ν`, or the two blocks coincide. -/
theorem exists_adjacent_blocks (hnk : n ≤ k) (ν : Fin d) (y : Torus d (N₀ * L ^ k)) :
    ∃ p q : Torus d (N₀ * L ^ k),
      jBlock d L N₀ k n p = jBlock d L N₀ k n y ∧
      jBlock d L N₀ k n q =
        jBlock d L N₀ k n (y + Pi.single ν ((L ^ n : ℕ) : ZMod (N₀ * L ^ k))) ∧
      (q = p + Pi.single ν 1 ∨ q = p) := by
  classical
  by_cases hsame : jBlock d L N₀ k n (y + Pi.single ν ((L ^ n : ℕ) : ZMod (N₀ * L ^ k))) =
      jBlock d L N₀ k n y
  · exact ⟨y, y, rfl, hsame.symm, Or.inr rfl⟩
  · have hex : ∃ t : ℕ, jBlock d L N₀ k n (y + Pi.single ν (t : ZMod (N₀ * L ^ k))) ≠
        jBlock d L N₀ k n y := ⟨L ^ n, hsame⟩
    set t := Nat.find hex with ht
    have hts : jBlock d L N₀ k n (y + Pi.single ν (t : ZMod (N₀ * L ^ k))) ≠
        jBlock d L N₀ k n y := Nat.find_spec hex
    have ht0 : t ≠ 0 := by
      intro h0
      apply hts
      rw [h0]; simp
    obtain ⟨s, hs⟩ := Nat.exists_eq_succ_of_ne_zero ht0
    have hmin : jBlock d L N₀ k n (y + Pi.single ν (s : ZMod (N₀ * L ^ k))) =
        jBlock d L N₀ k n y := by
      have := Nat.find_min hex (m := s) (by omega)
      simpa using this
    have htle : t ≤ L ^ n := Nat.find_min' hex hsame
    have hLpos : 0 < L ^ n := Nat.pos_of_ne_zero (NeZero.ne _)
    have hstep := jBlock_add_nat (L := L) (N₀ := N₀) hnk ν
      (y + Pi.single ν (s : ZMod (N₀ * L ^ k))) 1 hLpos
    simp only [Nat.cast_one] at hstep
    have hadd : y + Pi.single ν (s : ZMod (N₀ * L ^ k)) + Pi.single ν (1 : ZMod (N₀ * L ^ k)) =
        y + Pi.single ν (t : ZMod (N₀ * L ^ k)) := by
      rw [add_assoc, ← Pi.single_add, hs]
      push_cast; rfl
    rw [hadd, hmin] at hstep
    have hq : jBlock d L N₀ k n (y + Pi.single ν (t : ZMod (N₀ * L ^ k))) =
        jBlock d L N₀ k n y + Pi.single ν 1 := hstep.resolve_left hts
    refine ⟨y + Pi.single ν (s : ZMod (N₀ * L ^ k)),
      y + Pi.single ν (s : ZMod (N₀ * L ^ k)) + Pi.single ν 1, hmin, ?_, Or.inl rfl⟩
    rw [hadd, hq, jBlock_add_shift hnk]

theorem mem_tildeDelta_shift {G : GeneratingSet d L N₀ k ϱ} {G' : GeneratingSet d L N₀ k ϱ'}
    (h : Precedes G G') (hn1 : 1 ≤ n) (hnk : n ≤ k) (ν : Fin d) {y : Torus d (N₀ * L ^ k)}
    (hy : y ∈ G.layer n)
    (hy' : y + Pi.single ν ((L ^ n : ℕ) : ZMod (N₀ * L ^ k)) ∈ G.layer n) :
    y + Pi.single ν ((L ^ n : ℕ) : ZMod (N₀ * L ^ k)) ∈ tildeDelta G' y := by
  set x' := y + Pi.single ν ((L ^ n : ℕ) : ZMod (N₀ * L ^ k)) with hx'
  have hyΩ : y ∈ G.Ω 1 := G.layer_subset hn1 hnk hy
  have hx'Ω : x' ∈ G.Ω 1 := G.layer_subset hn1 hnk hy'
  have hly : G.layerIndex y = n := G.layerIndex_eq hn1 hnk hy
  have hlx : G.layerIndex x' = n := G.layerIndex_eq hn1 hnk hy'
  obtain ⟨p, q, hp, hq, hpq⟩ := exists_adjacent_blocks (L := L) (N₀ := N₀) hnk ν y
  obtain ⟨-, hpk, -⟩ := G'.layerIndex_spec (h.mem_Ω1 hyΩ)
  obtain ⟨-, hpk', -⟩ := G'.layerIndex_spec (h.mem_Ω1 hx'Ω)
  have hn0 : n ≤ G'.layerIndex y := hly ▸ h.layerIndex_le hyΩ
  have hn1' : n ≤ G'.layerIndex x' := hlx ▸ h.layerIndex_le hx'Ω
  refine ⟨h.mem_Ω1 hx'Ω, p, q, jBlock_eq_of_le hn0 hpk hp, jBlock_eq_of_le hn1' hpk' hq, ?_⟩
  have hnorm : ∀ w : Fin d → ℤ, (∀ i, |w i| ≤ 1) → ‖w‖ ≤ 1 := fun w hw =>
    (pi_norm_le_iff_of_nonneg zero_le_one).2 fun i => by
      rw [Int.norm_eq_abs]; exact_mod_cast hw i
  rcases hpq with h1 | h1
  · refine ⟨Pi.single ν 1, hnorm _ fun i => ?_, ?_⟩
    · by_cases hi : i = ν <;> simp [hi]
    · rw [h1]; unfold liftPt; congr 1; funext i
      by_cases hi : i = ν <;> simp [hi]
  · refine ⟨0, hnorm _ fun i => by simp, ?_⟩
    rw [h1, liftPt_zero]

end BlockGeometry

section Numeric

/-- The arithmetic of one Hölder bracket: from `s^{2-θ'} ‖z‖^{-(1-θ')} X ≤ C`, `‖z‖ = m`,
`m ≤ θ s`, one gets `m X ≤ C θ^{2-θ'}`. -/
theorem holder_numeric {s m θ θh C X : ℝ} (hm : 0 < m) (hθ : 0 < θ) (hθh1 : θh < 1)
    (hs : m ≤ θ * s) (hX0 : 0 ≤ X)
    (hH : s ^ (2 - θh) * (m ^ (1 - θh))⁻¹ * X ≤ C) : m * X ≤ C * θ ^ (2 - θh) := by
  have hs0 : 0 < s := by
    by_contra hc
    push Not at hc
    nlinarith [mul_nonpos_of_nonneg_of_nonpos hθ.le hc]
  have ha : 0 < 2 - θh := by linarith
  have hsa : 0 < s ^ (2 - θh) := Real.rpow_pos_of_pos hs0 _
  have hma : 0 < m ^ (1 - θh) := Real.rpow_pos_of_pos hm _
  have hC0 : 0 ≤ C := le_trans (by positivity) hH
  have e1 : m ^ (1 - θh) * m = m ^ (2 - θh) := by
    rw [← Real.rpow_add_one hm.ne']; congr 1; ring
  have h2 : s ^ (2 - θh) * X ≤ C * m ^ (1 - θh) := by
    have := hH
    rw [mul_assoc, mul_comm (s ^ (2 - θh)), mul_assoc] at this
    calc s ^ (2 - θh) * X = m ^ (1 - θh) * ((m ^ (1 - θh))⁻¹ * (s ^ (2 - θh) * X)) := by
          field_simp
      _ ≤ m ^ (1 - θh) * C := by
          apply mul_le_mul_of_nonneg_left _ hma.le
          calc (m ^ (1 - θh))⁻¹ * (s ^ (2 - θh) * X)
              = s ^ (2 - θh) * (m ^ (1 - θh))⁻¹ * X := by ring
            _ ≤ C := hH
      _ = C * m ^ (1 - θh) := by ring
  have h3 : m ^ (2 - θh) ≤ θ ^ (2 - θh) * s ^ (2 - θh) := by
    rw [← Real.mul_rpow hθ.le hs0.le]
    exact Real.rpow_le_rpow hm.le hs ha.le
  have h4 : s ^ (2 - θh) * (m * X) ≤ s ^ (2 - θh) * (C * θ ^ (2 - θh)) := by
    calc s ^ (2 - θh) * (m * X) = m * (s ^ (2 - θh) * X) := by ring
      _ ≤ m * (C * m ^ (1 - θh)) := mul_le_mul_of_nonneg_left h2 hm.le
      _ = C * m ^ (2 - θh) := by rw [← e1]; ring
      _ ≤ C * (θ ^ (2 - θh) * s ^ (2 - θh)) := mul_le_mul_of_nonneg_left h3 hC0
      _ = s ^ (2 - θh) * (C * θ ^ (2 - θh)) := by ring
  exact le_of_mul_le_mul_left h4 hsa

end Numeric

section BlockDiff

/-- The translation by one `n`-block side in direction `μ`. -/
local notation "sh[" n ", " μ "]" =>
  (Pi.single μ ((L ^ n : ℕ) : ZMod (N₀ * L ^ k)) : Torus d (N₀ * L ^ k))

omit [NeZero N₀] [NeZero L] in
theorem telescope_shift (F : Torus d (N₀ * L ^ k) → ℂ) (μ : Fin d) (w : Torus d (N₀ * L ^ k))
    (M : ℕ) :
    F (w + Pi.single μ (M : ZMod (N₀ * L ^ k))) - F w =
      ∑ i ∈ range M, (F (w + Pi.single μ (i : ZMod (N₀ * L ^ k)) + Pi.single μ 1) -
        F (w + Pi.single μ (i : ZMod (N₀ * L ^ k)))) := by
  have := Finset.sum_range_sub (fun i : ℕ => F (w + Pi.single μ (i : ZMod (N₀ * L ^ k)))) M
  simp only [Nat.cast_zero, Pi.single_zero, add_zero] at this
  rw [← this]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 2
  rw [add_assoc, ← Pi.single_add]
  push_cast; rfl

variable {G : GeneratingSet d L N₀ k ϱ} {G' : GeneratingSet d L N₀ k ϱ'} {n : ℕ}

/-- The block mean of a Hölder function has second difference of order `θ^{2-θ'}` across four
cells of one layer. -/
theorem blockMean_second_diff (h : Precedes G G') (hn1 : 1 ≤ n) (hnk : n ≤ k) {θ θh CH : ℝ}
    (hθ : 0 < θ) (hθh1 : θh < 1) (hCH : 0 ≤ CH) (hgap : ScaleGap G G' θ)
    {F : Torus d (N₀ * L ^ k) → ℂ}
    (hF : HolderSeminormLE G' F θh (2 - θh) CH) (μ ν : Fin d) {x : Torus d (N₀ * L ^ k)}
    (h00 : x ∈ G.layer n) (h10 : x + sh[n, μ] ∈ G.layer n) (h01 : x + sh[n, ν] ∈ G.layer n)
    (h11 : x + sh[n, μ] + sh[n, ν] ∈ G.layer n) :
    ‖blockMean G n F (x + sh[n, μ] + sh[n, ν]) - blockMean G n F (x + sh[n, μ]) -
        blockMean G n F (x + sh[n, ν]) + blockMean G n F x‖ ≤ CH * θ ^ (2 - θh) := by
  classical
  have hNpos : 0 < L ^ n := Nat.pos_of_ne_zero (NeZero.ne _)
  have hNR : (0 : ℝ) < (L : ℝ) ^ n := by
    have : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
    positivity
  have hlay : ∀ y, y ∈ G.layer n → ∀ z, jBlock d L N₀ k n z = jBlock d L N₀ k n y →
      z ∈ G.layer n := fun y hy z hz =>
    mem_layer_of_mem_blk G hn1 hnk hy (GeneratingSet.mem_blk.2 hz)
  -- layer positions of the path points
  have hpos : ∀ u ∈ G.blk n x, ∀ i : ℕ, i ≤ L ^ n →
      u + Pi.single μ (i : ZMod (N₀ * L ^ k)) ∈ G.layer n ∧
        u + Pi.single μ (i : ZMod (N₀ * L ^ k)) + sh[n, ν] ∈ G.layer n := by
    intro u hu i hi
    have hux : jBlock d L N₀ k n u = jBlock d L N₀ k n x := GeneratingSet.mem_blk.1 hu
    rcases jBlock_add_nat (L := L) (N₀ := N₀) hnk μ u i hi with hc | hc
    · have e1 := hc.trans hux
      refine ⟨hlay x h00 _ e1, hlay (x + sh[n, ν]) h01 _ ?_⟩
      rw [jBlock_add_shift hnk ν, jBlock_add_shift hnk ν, e1]
    · have e2 : jBlock d L N₀ k n (u + Pi.single μ (i : ZMod (N₀ * L ^ k))) =
          jBlock d L N₀ k n (x + sh[n, μ]) := by
        rw [hc, hux, jBlock_add_shift hnk μ]
      refine ⟨hlay _ h10 _ e2, hlay (x + sh[n, μ] + sh[n, ν]) h11 _ ?_⟩
      rw [jBlock_add_shift hnk ν, jBlock_add_shift hnk ν, e2]
  have key : ∀ u ∈ G.blk n x, ‖F (u + sh[n, μ] + sh[n, ν]) - F (u + sh[n, μ]) -
      F (u + sh[n, ν]) + F u‖ ≤ CH * θ ^ (2 - θh) := by
    intro u hu
    have hT : F (u + sh[n, μ] + sh[n, ν]) - F (u + sh[n, μ]) - F (u + sh[n, ν]) + F u =
        ∑ i ∈ range (L ^ n), ((F (u + sh[n, ν] + Pi.single μ (i : ZMod (N₀ * L ^ k)) +
              Pi.single μ 1) -
            F (u + sh[n, ν] + Pi.single μ (i : ZMod (N₀ * L ^ k)))) -
          (F (u + Pi.single μ (i : ZMod (N₀ * L ^ k)) + Pi.single μ 1) -
            F (u + Pi.single μ (i : ZMod (N₀ * L ^ k))))) := by
      rw [Finset.sum_sub_distrib, ← telescope_shift F μ (u + sh[n, ν]) (L ^ n),
        ← telescope_shift F μ u (L ^ n),
        show u + sh[n, μ] + sh[n, ν] = u + sh[n, ν] + sh[n, μ] from add_right_comm _ _ _]
      ring
    have hbr : ∀ i ∈ range (L ^ n), ‖(F (u + sh[n, ν] + Pi.single μ (i : ZMod (N₀ * L ^ k)) +
              Pi.single μ 1) -
            F (u + sh[n, ν] + Pi.single μ (i : ZMod (N₀ * L ^ k)))) -
          (F (u + Pi.single μ (i : ZMod (N₀ * L ^ k)) + Pi.single μ 1) -
            F (u + Pi.single μ (i : ZMod (N₀ * L ^ k))))‖ ≤ CH * θ ^ (2 - θh) / (L : ℝ) ^ n := by
      intro i hi
      obtain ⟨hx0, hx1⟩ := hpos u hu i (Finset.mem_range.1 hi).le
      rw [add_right_comm u (sh[n, ν]), le_div_iff₀ hNR]
      by_cases hne : u + Pi.single μ (i : ZMod (N₀ * L ^ k)) =
          u + Pi.single μ (i : ZMod (N₀ * L ^ k)) + sh[n, ν]
      · rw [← hne]
        simp only [sub_self, norm_zero, zero_mul]
        positivity
      · have hmem := mem_tildeDelta_shift (G' := G') h hn1 hnk ν hx0 hx1
        have hz : liftPt (u + Pi.single μ (i : ZMod (N₀ * L ^ k)))
            (Pi.single ν ((L ^ n : ℕ) : ℤ)) =
            u + Pi.single μ (i : ZMod (N₀ * L ^ k)) + sh[n, ν] := by
          unfold liftPt; congr 1; funext j
          by_cases hj : j = ν <;> simp [hj]
        have hH := hF _ (h.mem_Ω1 (G.layer_subset hn1 hnk hx0)) _ hmem hne _ hz μ
        have hznorm : ‖(Pi.single ν ((L ^ n : ℕ) : ℤ) : Fin d → ℤ)‖ = (L : ℝ) ^ n := by
          rw [Pi.norm_single (G := fun _ : Fin d => ℤ) (i := ν)]; simp
        rw [hznorm] at hH
        have hs := hgap _ (G.layer_subset hn1 hnk hx0)
        rw [G.spacing_eq hn1 hnk hx0] at hs
        have := holder_numeric hNR hθ hθh1 hs (norm_nonneg _) hH
        linarith
    rw [hT]
    refine (norm_sum_le _ _).trans ?_
    refine (Finset.sum_le_sum hbr).trans ?_
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have : ((L ^ n : ℕ) : ℝ) = (L : ℝ) ^ n := by push_cast; rfl
    rw [this]
    field_simp
    exact le_rfl
  have e1 : blockMean G n F (x + sh[n, μ] + sh[n, ν]) =
      blockMean G n (fun u => F (u + sh[n, μ] + sh[n, ν])) x := by
    rw [blockMean_add_shift G hnk ν F (x + sh[n, μ]),
      blockMean_add_shift G hnk μ (fun u => F (u + sh[n, ν])) x]
  have e2 : blockMean G n F (x + sh[n, μ]) = blockMean G n (fun u => F (u + sh[n, μ])) x :=
    blockMean_add_shift G hnk μ F x
  have e3 : blockMean G n F (x + sh[n, ν]) = blockMean G n (fun u => F (u + sh[n, ν])) x :=
    blockMean_add_shift G hnk ν F x
  have e4 : blockMean G n (fun u => F (u + sh[n, μ] + sh[n, ν])) x -
      blockMean G n (fun u => F (u + sh[n, μ])) x - blockMean G n (fun u => F (u + sh[n, ν])) x +
      blockMean G n F x =
      ((((((L : ℝ) ^ n) ^ d)⁻¹ : ℝ) : ℂ)) * ∑ u ∈ G.blk n x,
        (F (u + sh[n, μ] + sh[n, ν]) - F (u + sh[n, μ]) - F (u + sh[n, ν]) + F u) := by
    unfold blockMean
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib]
    ring
  rw [e1, e2, e3, e4, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have hcard := card_blk_cast G n hnk x
  have hpos' : (0 : ℝ) < ((L : ℝ) ^ n) ^ d := by positivity
  rw [abs_of_pos (inv_pos.2 hpos')]
  calc (((L : ℝ) ^ n) ^ d)⁻¹ * ‖∑ u ∈ G.blk n x, (F (u + sh[n, μ] + sh[n, ν]) -
          F (u + sh[n, μ]) - F (u + sh[n, ν]) + F u)‖
      ≤ (((L : ℝ) ^ n) ^ d)⁻¹ * ∑ u ∈ G.blk n x, CH * θ ^ (2 - θh) :=
        mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans (Finset.sum_le_sum key))
          (inv_pos.2 hpos').le
    _ = CH * θ ^ (2 - θh) := by
        rw [Finset.sum_const, nsmul_eq_mul, hcard]
        field_simp

end BlockDiff

section Composed

local notation "sh[" n ", " μ "]" =>
  (Pi.single μ ((L ^ n : ℕ) : ZMod (N₀ * L ^ k)) : Torus d (N₀ * L ^ k))

variable {N : ℕ} {G : GeneratingSet d L N₀ k ϱ} {G' : GeneratingSet d L N₀ k ϱ'}
  {a₁ ν ε₀ θ : ℝ} {Ψ₀ : Torus d (N₀ * L ^ k) → Fin N → ℝ} {h₀ : Fin N → ℝ}
  {Ψ'' h'' : Torus d (N₀ * L ^ k) → Fin N → ℂ} {Dr Dc : BgData G' N}

/-- **(Ξ4) for the composed field, given the Hölder bound** of the extended background field:
across four cells `x, x + L^n e, x + L^n e', x + L^n (e + e')` of one layer `n` of `𝔹`, the second
difference of the composed field `ψ(𝔹, 𝔹'; Ψ^c)` is at most `C θ^{2-θ'} + 8 θ² ε₀`. -/
theorem composeField_second_diff (ha₁ : 0 < a₁) (hL : 2 ≤ L) (h : Precedes G G')
    (hgap : ScaleGap G G' θ) (hθ0 : 0 < θ) {θh CH : ℝ} (hθh1 : θh < 1) (hCH : 0 ≤ CH)
    (hR : Realizes Dr Ψ₀ h₀) (hC : RealizesC Dc Ψ₀ h₀ Ψ'' h'')
    (hbr : XiBounds G' ν k 1 ε₀ Dr h₀ (bgField G' (compWeight L a₁) ν Dr)
      (bgMult G' (compWeight L a₁) ν Dr))
    (hb : XiCBounds G' ν 1 ε₀ Dr Dc Ψ'' h'' (bgField G' (compWeight L a₁) ν Dr)
      (bgFieldC G' (compWeight L a₁) ν (bgC0 d L N) Dc) (bgMult G' (compWeight L a₁) ν Dr)
      (bgMultC G' (compWeight L a₁) ν (bgC0 d L N) Dc))
    (hF : ∀ i : Fin N, HolderSeminormLE G'
      (fun y => bgFieldExt G' (compWeight L a₁) ν (bgC0 d L N) Dc y i) θh (2 - θh) CH)
    {n : ℕ} (hn1 : 1 ≤ n) (hnk : n ≤ k) (e e' : Fin d) {x : Torus d (N₀ * L ^ k)}
    (h00 : x ∈ G.layer n) (h10 : x + sh[n, e] ∈ G.layer n) (h01 : x + sh[n, e'] ∈ G.layer n)
    (h11 : x + sh[n, e] + sh[n, e'] ∈ G.layer n) (i : Fin N) :
    ‖composeField G G' (compWeight L a₁) (bgFieldC G' (compWeight L a₁) ν (bgC0 d L N) Dc)
          Dc.Ψ (x + sh[n, e] + sh[n, e']) i -
        composeField G G' (compWeight L a₁) (bgFieldC G' (compWeight L a₁) ν (bgC0 d L N) Dc)
          Dc.Ψ (x + sh[n, e]) i -
        composeField G G' (compWeight L a₁) (bgFieldC G' (compWeight L a₁) ν (bgC0 d L N) Dc)
          Dc.Ψ (x + sh[n, e']) i +
        composeField G G' (compWeight L a₁) (bgFieldC G' (compWeight L a₁) ν (bgC0 d L N) Dc)
          Dc.Ψ x i‖ ≤ CH * θ ^ (2 - θh) + 8 * θ ^ 2 * ε₀ := by
  set ψ := composeField G G' (compWeight L a₁) (bgFieldC G' (compWeight L a₁) ν (bgC0 d L N) Dc)
    Dc.Ψ with hψ
  set F : Torus d (N₀ * L ^ k) → ℂ := fun y => bgFieldExt G' (compWeight L a₁) ν (bgC0 d L N) Dc y i
    with hFdef
  have hr : ∀ p, p ∈ G.layer n → ‖ψ p i - blockMean G n F p‖ ≤ 2 * θ ^ 2 * ε₀ := by
    intro p hp
    have hpΩ : p ∈ G.Ω 1 := G.layer_subset hn1 hnk hp
    have := composeField_sub_blockMean_ext_le ha₁ hL h hgap hR hC hbr hb hpΩ
    rw [G.layerIndex_eq hn1 hnk hp] at this
    exact (norm_le_vn _ i).trans this
  have hQ := blockMean_second_diff h hn1 hnk hθ0 hθh1 hCH hgap (hF i) e e' h00 h10 h01 h11
  have e1 : ψ (x + sh[n, e] + sh[n, e']) i - ψ (x + sh[n, e]) i - ψ (x + sh[n, e']) i + ψ x i =
      (blockMean G n F (x + sh[n, e] + sh[n, e']) - blockMean G n F (x + sh[n, e]) -
        blockMean G n F (x + sh[n, e']) + blockMean G n F x) +
      ((ψ (x + sh[n, e] + sh[n, e']) i - blockMean G n F (x + sh[n, e] + sh[n, e'])) -
        (ψ (x + sh[n, e]) i - blockMean G n F (x + sh[n, e])) -
        (ψ (x + sh[n, e']) i - blockMean G n F (x + sh[n, e'])) +
        (ψ x i - blockMean G n F x)) := by ring
  have r11 := hr _ h11
  have r10 := hr _ h10
  have r01 := hr _ h01
  have r00 := hr _ h00
  rw [e1]
  refine (norm_add_le _ _).trans ?_
  have := norm_add_le (a := (ψ (x + sh[n, e] + sh[n, e']) i - blockMean G n F (x + sh[n, e] + sh[n, e'])) -
        (ψ (x + sh[n, e]) i - blockMean G n F (x + sh[n, e])) -
        (ψ (x + sh[n, e']) i - blockMean G n F (x + sh[n, e'])))
    (b := ψ x i - blockMean G n F x)
  have := norm_sub_le (a := (ψ (x + sh[n, e] + sh[n, e']) i - blockMean G n F (x + sh[n, e] + sh[n, e'])) -
        (ψ (x + sh[n, e]) i - blockMean G n F (x + sh[n, e])))
    (b := ψ (x + sh[n, e']) i - blockMean G n F (x + sh[n, e']))
  have := norm_sub_le (a := ψ (x + sh[n, e] + sh[n, e']) i - blockMean G n F (x + sh[n, e] + sh[n, e']))
    (b := ψ (x + sh[n, e]) i - blockMean G n F (x + sh[n, e]))
  nlinarith

theorem cHold_nonneg (d L : ℕ) : 0 ≤ cHold d L :=
  (mul_nonneg (mul_nonneg (cMix_nonneg d L) (by positivity)) (by positivity)).trans
    (le_max_right _ _)

/-- The constant `K_Σ = B/θ'((C₃ + (3/2) K₁) C₁) + C_H C₁ + 8` of (Ξ4) for the composed field. -/
noncomputable def xiSigma (d L N : ℕ) [NeZero L] (B θh : ℝ) : ℝ :=
  B / θh * ((lemma53Const d L + 3 / 2 * bgK1 d L N) * xiC1 d) + cHold d L * xiC1 d + 8

/-- **(Ξ4) for the composed field** (`notes/phase1/SMALLFIELD.md` §1.8, (Σ2)).  For a member of
`Ξ^c_k(𝔹'; 1, ε')`, `𝔹 ≺ 𝔹'` with the scale gap `ℓ ≤ θ ℓ'` (`0 < θ ≤ 1`), a realization `D^c`
of its complex datum and four cells `x, x + L^n e, x + L^n e', x + L^n (e + e')` of one layer `n` of
`𝔹` (the level `j = n`; interface sites between different layers are excluded), the second
difference of the composed field `ψ(𝔹, 𝔹'; Ψ^c)` satisfies
`|ψ(y + e + e') - ψ(y + e) - ψ(y + e') + ψ(y)| ≤ K_Σ θ^{2-θ'} ε'`, for every fixed exponent
`θ' ∈ (0,1)`; here `θ = s = L^{j-k}` and `θ'` is `α₁` of P1 (3.107). -/
theorem xiC_second_diff (hd : 3 ≤ d) (hL : 3 ≤ L) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ {θh : ℝ}, 0 < θh → θh < 1 → ∀ {N k N₀ : ℕ} [NeZero N₀] {ϱ ϱ' : ℝ}
      (G : GeneratingSet d L N₀ k ϱ) (G' : GeneratingSet d L N₀ k ϱ') {a₁ ν θ ε' : ℝ},
      0 < a₁ → BgHyp d L k ϱ' (compWeight L a₁) ν → Precedes G G' → ScaleGap G G' θ → 0 < θ →
      θ ≤ 1 → (4 * d + 6) * ((2 * d + 1) * ε') ≤ 1 → xiC1 d * ε' ≤ bgC1 d L N →
      ∀ {Ψ₀ : Torus d (N₀ * L ^ k) → Fin N → ℝ} {h₀ : Fin N → ℝ}
        {Ψ'' h'' : Torus d (N₀ * L ^ k) → Fin N → ℂ},
      XiC G' (compWeight L a₁) ν k 1 ε' Ψ₀ h₀ Ψ'' h'' →
      ∃ Dc : BgData G' N, RealizesC Dc Ψ₀ h₀ Ψ'' h'' ∧ ∀ {n : ℕ}, 1 ≤ n → n ≤ k →
        ∀ (e e' : Fin d) {x : Torus d (N₀ * L ^ k)}, x ∈ G.layer n →
        x + Pi.single e ((L ^ n : ℕ) : ZMod (N₀ * L ^ k)) ∈ G.layer n →
        x + Pi.single e' ((L ^ n : ℕ) : ZMod (N₀ * L ^ k)) ∈ G.layer n →
        x + Pi.single e ((L ^ n : ℕ) : ZMod (N₀ * L ^ k)) +
          Pi.single e' ((L ^ n : ℕ) : ZMod (N₀ * L ^ k)) ∈ G.layer n → ∀ i : Fin N,
        ‖composeField G G' (compWeight L a₁)
              (bgFieldC G' (compWeight L a₁) ν (bgC0 d L N) Dc) Dc.Ψ
              (x + Pi.single e ((L ^ n : ℕ) : ZMod (N₀ * L ^ k)) +
                Pi.single e' ((L ^ n : ℕ) : ZMod (N₀ * L ^ k))) i -
            composeField G G' (compWeight L a₁)
              (bgFieldC G' (compWeight L a₁) ν (bgC0 d L N) Dc) Dc.Ψ
              (x + Pi.single e ((L ^ n : ℕ) : ZMod (N₀ * L ^ k))) i -
            composeField G G' (compWeight L a₁)
              (bgFieldC G' (compWeight L a₁) ν (bgC0 d L N) Dc) Dc.Ψ
              (x + Pi.single e' ((L ^ n : ℕ) : ZMod (N₀ * L ^ k))) i +
            composeField G G' (compWeight L a₁)
              (bgFieldC G' (compWeight L a₁) ν (bgC0 d L N) Dc) Dc.Ψ x i‖ ≤
          xiSigma d L N B θh * θ ^ (2 - θh) * ε' := by
  classical
  obtain ⟨B, hB0, hB⟩ := bgFieldC_holder (d := d) (L := L) hd hL
  refine ⟨B, hB0, ?_⟩
  intro θh hθh0 hθh1 N k N₀ _ ϱ ϱ' G G' a₁ ν θ ε' ha₁ H h hgap hθ0 hθ1 hsmall hc1 Ψ₀ h₀ Ψ'' h''
    hX
  have hP := xiC_one_subset H hsmall hX
  obtain ⟨-, hε, Dr, Dc, hXr, hC, hDcU, hb⟩ := hX
  have hd0 : 0 < d := by omega
  have hδ0 : 0 < xiC1 d * ε' := by have := one_le_xiC1 d; positivity
  have hDC : InDomainC G' ν (xiC1 d * ε') (xiC1 d * ε') Dc :=
    ⟨Ψ₀, h₀, Ψ'', h'', hP, hC.1, hC.2⟩
  have hHol : ∀ i : Fin N, HolderSeminormLE G'
      (fun y => bgFieldExt G' (compWeight L a₁) ν (bgC0 d L N) Dc y i) θh (2 - θh)
      (B / θh * ((lemma53Const d L + 3 / 2 * bgK1 d L N) * (xiC1 d * ε')) +
        cHold d L * (xiC1 d * ε')) := by
    intro i
    refine hB hθh0 hθh1 G' H hδ0 le_rfl (hc1.trans (bgC1_le_bgC0 d L N hd0)) hc1 ?_ hDC i
    have := H.massLe
    nlinarith [sq_nonneg (xiC1 d * ε')]
  have hCH : 0 ≤ B / θh * ((lemma53Const d L + 3 / 2 * bgK1 d L N) * (xiC1 d * ε')) +
      cHold d L * (xiC1 d * ε') := by
    have h1 := lemma53Const_pos d L
    have h2 := bgK1_pos d L N
    have h3 := cHold_nonneg d L
    positivity
  have hL2 : 2 ≤ L := by omega
  refine ⟨Dc, hC, fun {n} hn1 hnk e e' {x} h00 h10 h01 h11 i => ?_⟩
  have key := composeField_second_diff ha₁ hL2 h hgap hθ0 hθh1 hCH hXr.1 hC hXr.2.2 hb hHol hn1 hnk
    e e' h00 h10 h01 h11 i
  refine key.trans ?_
  have h2 : θ ^ 2 ≤ θ ^ (2 - θh) := by
    have : θ ^ (2 : ℝ) = θ ^ 2 := by norm_cast
    rw [← this]
    exact Real.rpow_le_rpow_of_exponent_ge hθ0 hθ1 (by linarith)
  have hε0 : 0 ≤ ε' := hε.le
  unfold xiSigma
  have e3 : B / θh * ((lemma53Const d L + 3 / 2 * bgK1 d L N) * (xiC1 d * ε')) +
      cHold d L * (xiC1 d * ε') = (B / θh * ((lemma53Const d L + 3 / 2 * bgK1 d L N) * xiC1 d) +
        cHold d L * xiC1 d) * ε' := by ring
  rw [e3]
  have hp : 0 ≤ θ ^ (2 - θh) := Real.rpow_nonneg hθ0.le _
  nlinarith [mul_le_mul_of_nonneg_right h2 hε0, mul_nonneg hp hε0]

end Composed

end Balaban.SmallField

