/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.DecoupledCovWeighted

/-!
# Geometry for the covariance decay (FLUCTUATION.md Lemma 2.4)

The path metric of the generating set bounds the `ℓ¹` torus distance of the fine lattice from
above by `L ^ K` times the path cost (`cov_torusDist_le_of_pathCost`); a unit block of side
`L ^ k` changes the `ℓ¹` distance by at most `d L ^ k` per pair of points
(`cov_unit_torusDist_le`). Together they convert decay in the path distance of the Agmon weights
into decay in the `ℓ¹` distance of the unit lattice.
-/

@[expose] public section

open Balaban Balaban.Localization Balaban.Multiscale

namespace Balaban.Fluctuation


theorem cov_block_cyc_le {ℓ N m : ℕ} [NeZero ℓ] [NeZero m] (hℓ : ℓ = N * m) (a a' : ZMod ℓ) :
    N * (Green.cycRep (blockCoord N m a - blockCoord N m a')).natAbs ≤
      (Green.cycRep (a - a')).natAbs + N := by
  have hN : 0 < N := by
    rcases Nat.eq_zero_or_pos N with h | h
    · exact absurd (by simpa [h] using hℓ) (NeZero.ne ℓ)
    · exact h
  set u := Green.cycRep (a - a') with hu
  have hcast : ((u : ℤ) : ZMod ℓ) = a - a' := Green.cast_cycRep _
  have hz : (((u - ((a.val : ℤ) - (a'.val : ℤ)) : ℤ)) : ZMod ℓ) = 0 := by
    push_cast
    rw [hcast]
    simp
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at hz
  obtain ⟨j, hj⟩ := hz
  subst hℓ
  have hA := Nat.div_add_mod a.val N
  have hA' := Nat.div_add_mod a'.val N
  have hs : a.val % N < N := Nat.mod_lt _ hN
  have hs' : a'.val % N < N := Nat.mod_lt _ hN
  set P := a.val / N with hP
  set P' := a'.val / N with hP'
  set s := a.val % N with hsdef
  set s' := a'.val % N with hsdef'
  set q : ℤ := (P : ℤ) - P' + (m : ℤ) * j with hq
  have huq : u = (N : ℤ) * q + ((s : ℤ) - s') := by
    have e1 : ((N : ℤ) * P + s) = a.val := by exact_mod_cast hA
    have e2 : ((N : ℤ) * P' + s') = a'.val := by exact_mod_cast hA'
    push_cast at hj
    rw [hq]
    linear_combination hj - e1 + e2
  have hqc : ((q : ℤ) : ZMod m) = blockCoord N m a - blockCoord N m a' := by
    rw [hq]
    unfold blockCoord
    push_cast
    simp [hP, hP']
  have h1 := Green.natAbs_cycRep_le_of_cast _ q hqc
  have h2 : (N : ℤ) * |q| ≤ |u| + N := by
    have : (N : ℤ) * q = u - ((s : ℤ) - s') := by linarith
    have h3 : |(N : ℤ) * q| = N * |q| := by
      rw [abs_mul, abs_of_nonneg (by positivity : (0:ℤ) ≤ N)]
    have h4 : |u - ((s : ℤ) - s')| ≤ |u| + |((s : ℤ) - s')| := abs_sub _ _
    have h5 : |((s : ℤ) - s')| ≤ N := by
      rw [abs_le]; constructor <;> omega
    rw [← h3, this]; linarith
  have h6 : N * (Green.cycRep (blockCoord N m a - blockCoord N m a')).natAbs ≤ N * q.natAbs :=
    Nat.mul_le_mul_left _ h1
  have h7 : (N : ℤ) * (q.natAbs : ℤ) ≤ (u.natAbs : ℤ) + N := by
    rw [Int.natCast_natAbs, Int.natCast_natAbs]; exact h2
  have h8 : N * q.natAbs ≤ u.natAbs + N := by exact_mod_cast h7
  exact h6.trans h8



section Unit

variable {d L N₁ m₁ k : ℕ} [NeZero N₁] [NeZero L]

theorem cov_unit_torusDist_le (y y' : CTorus d L N₁ m₁ (k + 1)) :
    ((L : ℝ) ^ k) * Green.torusDist d ((N₁ * L ^ m₁) * L ^ (k + 1 - k)) (unitBlock y) (unitBlock y') ≤
      Green.torusDist d ((N₁ * L ^ m₁) * L ^ (k + 1)) y y' + d * (L : ℝ) ^ k := by
  unfold Green.torusDist
  rw [Finset.mul_sum]
  calc ∑ i, (L : ℝ) ^ k * ((Green.cycRep (unitBlock y i - unitBlock y' i)).natAbs : ℝ)
      ≤ ∑ i : Fin d, (((Green.cycRep (y i - y' i)).natAbs : ℝ) + (L : ℝ) ^ k) := by
        refine Finset.sum_le_sum fun i _ => ?_
        have h := cov_block_cyc_le (ℓ := (N₁ * L ^ m₁) * L ^ (k + 1)) (N := L ^ k)
          (m := (N₁ * L ^ m₁) * L ^ (k + 1 - k)) unitBlock_side (y i) (y' i)
        have h' : ((L ^ k : ℕ) : ℝ) * ((Green.cycRep (blockCoord (L ^ k) ((N₁ * L ^ m₁) * L ^ (k + 1 - k)) (y i) - blockCoord (L ^ k) ((N₁ * L ^ m₁) * L ^ (k + 1 - k)) (y' i))).natAbs : ℝ) ≤ (Green.cycRep (y i - y' i)).natAbs + ((L ^ k : ℕ) : ℝ) := by exact_mod_cast h
        simpa [unitBlock, blockMap_apply] using h'
    _ = _ := by
        rw [Finset.sum_add_distrib]; simp

end Unit


section Path

variable {d L N₀ K : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ} {G : GeneratingSet d L N₀ K ϱ}

theorem cov_torusDist_le_of_pathCost {x y : Torus d (N₀ * L ^ K)} {c : ℝ} (h : G.PathCost x y c) :
    Green.torusDist d (N₀ * L ^ K) x y ≤ (L : ℝ) ^ K * c := by
  induction h with
  | refl x hx => rw [torusDist_self']; simp
  | step x y z c hx hadj hp ih =>
      have h1 := torusDist_triangle' x y z
      have h2 := hadj.torusDist_le
      have hL : (0 : ℝ) < (L : ℝ) ^ K := by
        have : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
        positivity
      have hmax : max (G.spacing x) (G.spacing y) ≤ (L : ℝ) ^ K :=
        max_le (spacing_le G hx) (spacing_le G hp.left_mem)
      have hb : 1 ≤ (L : ℝ) ^ K * G.bondCost x y := by
        unfold GeneratingSet.bondCost
        have hm0 : 0 < max (G.spacing x) (G.spacing y) :=
          lt_of_lt_of_le one_pos ((G.spacing_ge_one x).trans (le_max_left _ _))
        rw [mul_one_div, le_div_iff₀ hm0]
        linarith
      nlinarith

theorem cov_ofReal_le_siteSetDist {N₁ m₁ : ℕ} [NeZero N₁] {G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ}
    {W : Finset (CTorus d L N₁ m₁ K)} {y : CTorus d L N₁ m₁ K}
    {D : ℝ} (h : ∀ w ∈ W, D * (L : ℝ) ^ K ≤ Green.torusDist d ((N₁ * L ^ m₁) * L ^ K) y w) :
    ENNReal.ofReal D ≤ siteSetDist G W y := by
  have hL : (0 : ℝ) < (L : ℝ) ^ K := by
    have : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
    positivity
  unfold siteSetDist
  refine le_iInf₂ fun w hw => ?_
  unfold GeneratingSet.pathDist
  refine le_iInf₂ fun c hc => ?_
  refine ENNReal.ofReal_le_ofReal ?_
  have h1 := cov_torusDist_le_of_pathCost hc
  have h2 := h w hw
  by_contra hcon
  push Not at hcon
  nlinarith

end Path

end Balaban.Fluctuation
