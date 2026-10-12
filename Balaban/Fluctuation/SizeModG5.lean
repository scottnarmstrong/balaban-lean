/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.SizeModG1
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# (G5): the diameter (FLUCTUATION.md Lemma 1.2)

`euclDist x y` is the Euclidean distance of the torus (cyclic coordinates).  For `X ∈ 𝒟_j` and
`x, x' ∈ X`: `|x - x'| ≤ a (d^cov_j(X) + 2 √d L)` with `a = M L^j` the side of a `π_j`-cube, i.e.
in units of scale-`j` sites `|x - x'| ≤ M (d^cov_j(X) + 2 √d L)`.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Localization

section Dist

variable {d n : ℕ}

/-- The Euclidean distance on the torus (cyclic coordinates). -/
noncomputable def euclDist (x y : Torus d n) : ℝ :=
  Real.sqrt (∑ μ, ((LargeField.cycNorm n (x μ - y μ) : ℕ) : ℝ) ^ 2)

/-- The `ℓ¹` distance on the torus, in `ℕ`. -/
def l1Dist (x y : Torus d n) : ℕ := ∑ μ, LargeField.cycNorm n (x μ - y μ)

theorem l1Dist_triangle [NeZero n] (x y z : Torus d n) : l1Dist x z ≤ l1Dist x y + l1Dist y z := by
  unfold l1Dist
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun μ _ => LargeField.cycNorm_sub_le _ _ _

theorem l1Dist_self (x : Torus d n) : l1Dist x x = 0 := by
  simp [l1Dist, LargeField.cycNorm]

theorem l1Dist_comm [NeZero n] (x y : Torus d n) : l1Dist x y = l1Dist y x := by
  unfold l1Dist
  exact Finset.sum_congr rfl fun μ _ => LargeField.cycNorm_sub_comm _ _

theorem l1Dist_nbr [NeZero n] {x y : Torus d n} (h : Nbr x y) : l1Dist x y ≤ 1 := by
  have key : ∀ x : Torus d n, ∀ μ : Fin d, l1Dist x (x + Pi.single μ 1) ≤ 1 := by
    intro x μ
    unfold l1Dist
    rw [Finset.sum_eq_single μ]
    · simp only [Pi.add_apply, Pi.single_eq_same]
      have : x μ - (x μ + 1) = -1 := by ring
      rw [this, LargeField.cycNorm_neg]
      exact Balaban.Localization.cycNorm_one_le
    · intro ν _ hν
      simp [Pi.single_eq_of_ne hν, LargeField.cycNorm]
    · simp
  obtain ⟨μ, h | h⟩ := h
  · rw [h]; exact key x μ
  · rw [h, l1Dist_comm]; exact key y μ

theorem l1Dist_le_card [NeZero n] {W : Finset (Torus d n)} {E : Finset (Torus d n × Torus d n)}
    (hc : ConnStruct W E) {x y : Torus d n} (hx : x ∈ W) (hy : y ∈ W) :
    l1Dist x y ≤ E.card := by
  classical
  obtain ⟨-, hE, hconn⟩ := hc
  have := card_edges_ge (fun z => l1Dist x z) W E hconn (fun p hp => by
    obtain ⟨-, -, hn⟩ := hE p hp
    have h1 := l1Dist_nbr hn
    have t1 := l1Dist_triangle x p.1 p.2
    have t2 := l1Dist_triangle x p.2 p.1
    rw [l1Dist_comm p.2 p.1] at t2
    exact ⟨by omega, by omega⟩) hx hy (l1Dist_self x)
    (l1Dist x y) le_rfl
  exact this.trans (Finset.card_filter_le _ _)

theorem euclDist_le_l1 (x y : Torus d n) : euclDist x y ≤ l1Dist x y := by
  unfold euclDist l1Dist
  rw [Real.sqrt_le_iff]
  refine ⟨by positivity, ?_⟩
  push_cast
  exact Finset.sum_sq_le_sq_sum_of_nonneg (fun μ _ => by positivity)

theorem cycNorm_le_of_mem_box [NeZero n] {b : Torus d n} {s : ℕ} {x y : Torus d n}
    (hx : x ∈ box b s) (hy : y ∈ box b s) (μ : Fin d) :
    LargeField.cycNorm n (x μ - y μ) ≤ s := by
  obtain ⟨wx, hwx, rfl⟩ := hx
  obtain ⟨wy, hwy, rfl⟩ := hy
  rw [LargeField.cycNorm_le_iff]
  refine ⟨(wx μ : ℤ) - wy μ, ?_, ?_⟩
  · have := hwx μ
    have := hwy μ
    rw [abs_le]
    constructor <;> omega
  · simp [natT]

theorem euclDist_le_of_mem_box [NeZero n] {b : Torus d n} {s : ℕ} {x y : Torus d n}
    (hx : x ∈ box b s) (hy : y ∈ box b s) : euclDist x y ≤ Real.sqrt d * s := by
  unfold euclDist
  rw [Real.sqrt_le_iff]
  refine ⟨by positivity, ?_⟩
  rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
  calc _ ≤ ∑ _μ : Fin d, (s : ℝ) ^ 2 := Finset.sum_le_sum fun μ _ => by
        have := cycNorm_le_of_mem_box hx hy μ
        have h : ((LargeField.cycNorm n (x μ - y μ) : ℕ) : ℝ) ≤ s := by exact_mod_cast this
        exact pow_le_pow_left₀ (by positivity) h 2
    _ = d * (s : ℝ) ^ 2 := by simp

theorem sqrt_sum_sq_le (a b c u : Fin d → ℝ) (hu : ∀ μ, 0 ≤ u μ)
    (h : ∀ μ, u μ ≤ a μ + b μ + c μ) :
    Real.sqrt (∑ μ, u μ ^ 2) ≤
      Real.sqrt (∑ μ, a μ ^ 2) + Real.sqrt (∑ μ, b μ ^ 2) + Real.sqrt (∑ μ, c μ ^ 2) := by
  let A : EuclideanSpace ℝ (Fin d) := WithLp.toLp 2 a
  let B : EuclideanSpace ℝ (Fin d) := WithLp.toLp 2 b
  let C : EuclideanSpace ℝ (Fin d) := WithLp.toLp 2 c
  have e : ∀ v : EuclideanSpace ℝ (Fin d), ‖v‖ = Real.sqrt (∑ μ, (v μ) ^ 2) := by
    intro v; rw [EuclideanSpace.norm_eq]; simp [sq_abs]
  have hA := e A
  have hB := e B
  have hC := e C
  have hABC := e (A + B + C)
  have tri := norm_add₃_le (a := A) (b := B) (c := C)
  have hle : Real.sqrt (∑ μ, u μ ^ 2) ≤ ‖A + B + C‖ := by
    rw [hABC]
    refine Real.sqrt_le_sqrt (Finset.sum_le_sum fun μ _ => ?_)
    have : (A + B + C) μ = a μ + b μ + c μ := rfl
    rw [this]
    exact pow_le_pow_left₀ (hu μ) (h μ) 2
  refine hle.trans (tri.trans ?_)
  rw [hA, hB, hC]

end Dist

section G5

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {m₀ j : ℕ}

/-- **(G5).**  Any two points of `X ∈ 𝒟_j` satisfy `|x - x'| ≤ a (d^cov_j(X) + 2 √d L)`, where
`a = M L^j` is the side of a `π_j`-cube (in units of scale-`j` sites: `M (d^cov_j(X) + 2√d L)`). -/
theorem G5 {X : Set (CTorus d L N₁ m₁ K)} (hX : IsDj m₀ j X) {x x' : CTorus d L N₁ m₁ K}
    (hx : x ∈ X) (hx' : x' ∈ X) :
    euclDist x x' ≤ ((cellSide L m₀ m₁ j : ℕ) : ℝ) *
      (treeLenCovOne m₀ j X + 2 * Real.sqrt d * L) := by
  set a := cellSide L m₀ m₁ j with ha
  have ha0 : 0 < a := cellSide_pos m₀ m₁ j
  obtain ⟨𝒦, W, E, hE⟩ := exists_admissible_of_IsDj (Ω := Set.univ) hX
  obtain ⟨h1, h2, h3, h4⟩ := (modAdmissible_iff_chosen (Set.subset_univ X)).1 hE
  obtain ⟨𝒦', W', E', h1', h2', h3', h4', hc'⟩ :=
    treeLenCovOne_attained m₀ j X ⟨𝒦, W, E, h1, h2, h3, h4⟩
  obtain ⟨q, hq, hxq⟩ := h1'.2 x hx
  obtain ⟨q', hq', hxq'⟩ := h1'.2 x' hx'
  obtain ⟨p, hpW, hpq⟩ := h4' q hq
  obtain ⟨p', hpW', hpq'⟩ := h4' q' hq'
  have e1 : euclDist x p ≤ Real.sqrt d * (L * a : ℕ) := euclDist_le_of_mem_box hxq hpq
  have e3 : euclDist p' x' ≤ Real.sqrt d * (L * a : ℕ) := euclDist_le_of_mem_box hpq' hxq'
  have e2 : euclDist p p' ≤ E'.card :=
    (euclDist_le_l1 p p').trans (by exact_mod_cast l1Dist_le_card h2' hpW hpW')
  have e0 : euclDist x x' ≤ euclDist x p + euclDist p p' + euclDist p' x' := by
    unfold euclDist
    refine sqrt_sum_sq_le _ _ _ _ (fun μ => by positivity) (fun μ => ?_)
    have t1 := LargeField.cycNorm_sub_le (x μ) (p μ) (x' μ)
    have t2 := LargeField.cycNorm_sub_le (p μ) (p' μ) (x' μ)
    exact_mod_cast (by omega : LargeField.cycNorm _ (x μ - x' μ) ≤
      LargeField.cycNorm _ (x μ - p μ) + LargeField.cycNorm _ (p μ - p' μ) +
        LargeField.cycNorm _ (p' μ - x' μ))
  have haR : (a : ℝ) = (L : ℝ) ^ (m₀ + m₁ + j) := by
    rw [ha]; unfold cellSide; push_cast; congr 1; ring
  have hapos : (0 : ℝ) < a := by exact_mod_cast ha0
  have hcostE : treeLenCovOne m₀ j X = E'.card / a := by
    rw [← hc']; unfold bondCost scaleW
    rw [Finset.sum_const, nsmul_eq_mul, ← haR]; ring
  have hE' : (E'.card : ℝ) = a * treeLenCovOne m₀ j X := by
    rw [hcostE]; field_simp
  calc euclDist x x' ≤ _ := e0
    _ ≤ Real.sqrt d * (L * a : ℕ) + E'.card + Real.sqrt d * (L * a : ℕ) := by linarith
    _ = _ := by rw [hE']; push_cast; ring

end G5

end Balaban.Fluctuation
