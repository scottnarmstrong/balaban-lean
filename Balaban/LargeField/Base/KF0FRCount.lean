/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Base.KF0FROrd
public import Balaban.Multiscale.Counting
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# `KF0FRCount`: supports, multiplicity and the defect bound uniform in the mass (route FR, (P))

`notes/phase1/KF0-FR.md` (P).

* `card_frSupp_le`: a support has at most `(4R+3)^d` sites;
* `card_filter_mem_frSupp_le`: a site lies in at most `(1+d)(4R+3)^d` supports;
* `frQ_rowAbs_le_star`: for `7/(8L²) ≤ ν ≤ 1` the absolute row sums of `Q_R` are at most
  `θ_*(d, L, R) = 2(4d+1) ν_*^{-1/2} (2d+1)/ν_* · q_*^{R+1}`, `q_* = 2d/(2d+ν_*)`, `ν_* = 7/(8L²)`.
-/

@[expose] public section

open Balaban.Green

namespace Balaban.LargeField.KF0FR

noncomputable section

variable {d ℓ : ℕ} [NeZero ℓ]

theorem card_frSupp_le (R : ℕ) (t : FRTerm d ℓ) : (frSupp R t).card ≤ (4 * R + 3) ^ d := by
  rcases t with x | ⟨x, μ⟩
  · have := Balaban.Multiscale.card_ball_le (m := ℓ) x (2 * R + 1)
    have e : (2 * (2 * R + 1) + 1) = 4 * R + 3 := by ring
    rw [e] at this
    refine le_trans (le_of_eq ?_) this
    unfold frSupp; congr 1; ext y; simp
  · have := Balaban.Multiscale.card_ball_le (m := ℓ) x (R + 1)
    refine le_trans (le_of_eq ?_) (this.trans (Nat.pow_le_pow_left (by omega) d))
    unfold frSupp; congr 1; ext y; simp

/-- **The multiplicity of the supports.** -/
theorem card_filter_mem_frSupp_le (R : ℕ) (x : Torus d ℓ) (C : Finset (FRTerm d ℓ)) :
    (C.filter fun t => x ∈ frSupp R t).card ≤ (1 + d) * (4 * R + 3) ^ d := by
  set B1 := Finset.univ.filter fun y : Torus d ℓ => torusDist d ℓ x y ≤ (2 * R + 1 : ℕ)
  set B2 := Finset.univ.filter fun y : Torus d ℓ => torusDist d ℓ x y ≤ (R + 1 : ℕ)
  have hsub : C.filter (fun t => x ∈ frSupp R t) ⊆ B1.disjSum (B2 ×ˢ (Finset.univ : Finset (Fin d))) := by
    intro t ht
    rw [Finset.mem_filter] at ht
    rcases t with y | ⟨y, μ⟩
    · refine Finset.inl_mem_disjSum.2 (Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩)
      have := ht.2
      simp only [frSupp, Finset.mem_filter, Finset.mem_univ, true_and] at this
      rw [torusDist_comm_gen]; push_cast; exact this
    · refine Finset.inr_mem_disjSum.2 (Finset.mem_product.2 ⟨Finset.mem_filter.2
        ⟨Finset.mem_univ _, ?_⟩, Finset.mem_univ _⟩)
      have := ht.2
      simp only [frSupp, Finset.mem_filter, Finset.mem_univ, true_and] at this
      rw [torusDist_comm_gen]; push_cast; exact this
  have h1 : B1.card ≤ (4 * R + 3) ^ d := by
    have := Balaban.Multiscale.card_ball_le (m := ℓ) x (2 * R + 1)
    have e : (2 * (2 * R + 1) + 1) = 4 * R + 3 := by ring
    rw [e] at this
    exact this
  have h2 : B2.card ≤ (4 * R + 3) ^ d := by
    have := Balaban.Multiscale.card_ball_le (m := ℓ) x (R + 1)
    exact this.trans (Nat.pow_le_pow_left (by omega) d)
  calc _ ≤ _ := Finset.card_le_card hsub
    _ = B1.card + B2.card * d := by
        rw [Finset.card_disjSum, Finset.card_product, Finset.card_univ, Fintype.card_fin]
    _ ≤ (4 * R + 3) ^ d + (4 * R + 3) ^ d * d := Nat.add_le_add h1 (Nat.mul_le_mul_right _ h2)
    _ = (1 + d) * (4 * R + 3) ^ d := by ring

/-- The lower end of the masses of the case `k_f = 0`. -/
def frNuStar (L : ℕ) : ℝ := 7 / (8 * (L : ℝ) ^ 2)

/-- The bound of the absolute row sums of the defect, uniform in the mass. -/
def frThetaStar (d L R : ℕ) : ℝ :=
  2 * (4 * d + 1) * (Real.sqrt (frNuStar L))⁻¹ * ((2 * d + 1) / frNuStar L) *
    (2 * d / (2 * d + frNuStar L)) ^ (R + 1)

theorem frNuStar_pos {L : ℕ} (hL : 1 ≤ L) : 0 < frNuStar L := by
  unfold frNuStar
  have : (1 : ℝ) ≤ L := by exact_mod_cast hL
  positivity

/-- **The defect rows, uniformly in the mass.** -/
theorem frQ_rowAbs_le_star (hd : 1 ≤ d) {L : ℕ} (hL : 1 ≤ L) {ν : ℝ} (hν1 : frNuStar L ≤ ν)
    (hν : ν ≤ 1) (R : ℕ) (x : Torus d ℓ) :
    ∑ y, |frQ d ℓ ν R x y| ≤ frThetaStar d L R := by
  have hs := frNuStar_pos hL
  have hνp : 0 < ν := lt_of_lt_of_le hs hν1
  have hd0 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  refine (frQ_rowAbs_le hνp R x).trans ?_
  unfold frThetaStar frTail
  have h1 : (Real.sqrt ν)⁻¹ ≤ (Real.sqrt (frNuStar L))⁻¹ :=
    inv_anti₀ (Real.sqrt_pos.2 hs) (Real.sqrt_le_sqrt hν1)
  have h2 : (Real.sqrt (2 * d + ν))⁻¹ ≤ 1 := by
    rw [inv_le_one₀ (Real.sqrt_pos.2 (by positivity))]
    rw [Real.one_le_sqrt]; linarith
  have hq : 2 * (d : ℝ) / (2 * d + ν) ≤ 2 * d / (2 * d + frNuStar L) :=
    div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith)
  have hq0 : 0 ≤ 2 * (d : ℝ) / (2 * d + ν) := by positivity
  have h3 : (2 * (d : ℝ) / (2 * d + ν)) ^ (R + 1) ≤ (2 * d / (2 * d + frNuStar L)) ^ (R + 1) :=
    pow_le_pow_left₀ hq0 hq _
  have h4 : 1 / (1 - 2 * (d : ℝ) / (2 * d + ν)) ≤ (2 * d + 1) / frNuStar L := by
    have e : 1 - 2 * (d : ℝ) / (2 * d + ν) = ν / (2 * d + ν) := by field_simp; ring
    rw [e, one_div_div, div_le_div_iff₀ hνp hs]
    nlinarith
  have hpos1 : 0 ≤ (2 * (d : ℝ) / (2 * d + ν)) ^ (R + 1) := by positivity
  have hpos2 : 0 < 1 - 2 * (d : ℝ) / (2 * d + ν) := by
    rw [sub_pos, div_lt_one (by positivity)]; linarith
  calc 2 * (4 * d + ν) * (Real.sqrt ν)⁻¹ *
        ((Real.sqrt (2 * d + ν))⁻¹ * (2 * d / (2 * d + ν)) ^ (R + 1) /
          (1 - 2 * d / (2 * d + ν)))
      = 2 * (4 * d + ν) * (Real.sqrt ν)⁻¹ * (Real.sqrt (2 * d + ν))⁻¹ *
          (1 / (1 - 2 * d / (2 * d + ν))) * (2 * d / (2 * d + ν)) ^ (R + 1) := by ring
    _ ≤ 2 * (4 * d + 1) * (Real.sqrt (frNuStar L))⁻¹ * 1 * ((2 * d + 1) / frNuStar L) *
          (2 * d / (2 * d + frNuStar L)) ^ (R + 1) := by
        gcongr
    _ = _ := by ring

end

end Balaban.LargeField.KF0FR
