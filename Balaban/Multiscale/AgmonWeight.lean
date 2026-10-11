/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Multiscale.AgmonCore
import Mathlib.Tactic.Linarith

/-!
# The truncated path distance as an Agmon weight exponent (GREEN.md §4.2, Lemma 4.3 (b), (c))

`Balaban.Multiscale.GeneratingSet.truncDist G y' t x = (min (d(x, y'), t)).toReal` is finite
everywhere (the path metric is `⊤` between points of different components of `Ω₁`) and is an
admissible weight exponent (`Balaban.Multiscale.IsAgmonWeight`): it is `1/ℓ(b)`-Lipschitz along
bonds of `Ω₁` (Lemma 4.3 (c)) and has oscillation `≤ 2 d` on blocks of its layer (Lemma 4.3 (b)).
-/

@[expose] public section

namespace Balaban.Multiscale

variable {d L N₀ k : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}

namespace GeneratingSet

variable (G : GeneratingSet d L N₀ k ϱ)

/-- The path distance to `y'`, truncated at `t`, as a real number. -/
noncomputable def truncDist (y' : Torus d (N₀ * L ^ k)) (t : ℝ) (x : Torus d (N₀ * L ^ k)) : ℝ :=
  (min (G.pathDist x y') (ENNReal.ofReal t)).toReal

theorem abs_truncDist_sub_le (y' : Torus d (N₀ * L ^ k)) (t : ℝ) {x x' : Torus d (N₀ * L ^ k)}
    {c : ℝ} (hc : 0 ≤ c) (h1 : G.pathDist x y' ≤ ENNReal.ofReal c + G.pathDist x' y')
    (h2 : G.pathDist x' y' ≤ ENNReal.ofReal c + G.pathDist x y') :
    |G.truncDist y' t x - G.truncDist y' t x'| ≤ c := by
  have key : ∀ a b : ENNReal, a ≤ ENNReal.ofReal c + b →
      min a (ENNReal.ofReal t) ≤ ENNReal.ofReal c + min b (ENNReal.ofReal t) := by
    intro a b hab
    rcases le_total b (ENNReal.ofReal t) with hb | hb
    · rw [min_eq_left hb]; exact (min_le_left _ _).trans hab
    · rw [min_eq_right hb]; exact (min_le_right _ _).trans le_add_self
  exact abs_toReal_sub_le hc (key _ _ h1) (key _ _ h2)

/-- The truncated distance is an admissible weight exponent. -/
theorem isAgmonWeight_truncDist (y' : Torus d (N₀ * L ^ k)) (t : ℝ) :
    IsAgmonWeight G (G.truncDist y' t) where
  bond := by
    intro x x' hx hx' hadj
    refine G.abs_truncDist_sub_le y' t (G.bondCost_nonneg x x') ?_ ?_
    · exact (G.pathDist_triangle x x' y').trans (by
        gcongr; exact G.pathDist_le_bondCost hx hx' hadj)
    · refine (G.pathDist_triangle x' x y').trans (by
        gcongr
        rw [bondCost_comm]; exact G.pathDist_le_bondCost hx' hx hadj.symm)
  block := by
    intro j hj hjk x x' hx h
    have hd : (0 : ℝ) ≤ 2 * d := by positivity
    have h1 := G.pathDist_block_le hj hjk hx h
    have h2 : G.pathDist x' x ≤ ENNReal.ofReal (2 * d) := by
      rw [pathDist_comm]; exact h1
    refine G.abs_truncDist_sub_le y' t hd ?_ ?_
    · exact (G.pathDist_triangle x x' y').trans (by gcongr)
    · exact (G.pathDist_triangle x' x y').trans (by gcongr)

theorem truncDist_self {y' : Torus d (N₀ * L ^ k)} (hy' : y' ∈ G.Ω 1) (t : ℝ) :
    G.truncDist y' t y' = 0 := by
  simp [truncDist, G.pathDist_self hy']

theorem truncDist_eq_of_le {y y' : Torus d (N₀ * L ^ k)} {t : ℝ} (ht0 : 0 ≤ t)
    (ht : ENNReal.ofReal t ≤ G.pathDist y y') : G.truncDist y' t y = t := by
  unfold truncDist
  rw [min_eq_right ht, ENNReal.toReal_ofReal ht0]

theorem truncDist_nonneg (y' : Torus d (N₀ * L ^ k)) (t : ℝ) (x : Torus d (N₀ * L ^ k)) :
    0 ≤ G.truncDist y' t x := ENNReal.toReal_nonneg

end GeneratingSet

end Balaban.Multiscale
