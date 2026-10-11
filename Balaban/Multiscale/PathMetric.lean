/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Multiscale.GeneratingSet
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The multiscale path metric (GREEN.md §1.4, (1.9))

For a generating set `G` on the fine torus (unit spacing, `η = 1`; see
`Balaban/Multiscale/GeneratingSet.lean`), a *path* from `x` to `x'` is a nearest-neighbour path
`x = z₀, …, z_m = x'` all of whose sites lie in `Ω₁`; a bond `b = (z, z')` costs `1 / ℓ(b)` with
`ℓ(b) = max (ℓ(z), ℓ(z'))` (GREEN.md: `η / ℓ(b)`), and

`d(x, x') = inf_paths ∑ 1/ℓ(b)`.

The infimum is taken in `ℝ≥0∞`, so that `d(x, x') = ⊤` when no path inside `Ω₁` exists (in particular
when an endpoint lies outside `Ω₁`); this is the source object on its whole carrier.

* `Balaban.Multiscale.GeneratingSet.PathCost`: the inductive relation "a path from `x` to `y` of
  total cost `c` inside `Ω₁`";
* `Balaban.Multiscale.GeneratingSet.pathDist`: the metric (1.9);
* `pathDist_self`, `pathDist_comm`, `pathDist_triangle`: pseudo-metric axioms (on `ℝ≥0∞`);
* `bondCost_le_one`: each step costs at most `1` (`η / ℓ(b) ≤ 1`).
-/

@[expose] public section

namespace Balaban.Multiscale

variable {d L N₀ k : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}

/-- Nearest-neighbour adjacency on the torus. -/
def Adj (x y : Torus d (N₀ * L ^ k)) : Prop :=
  ∃ μ : Fin d, y = x + Pi.single μ 1 ∨ x = y + Pi.single μ 1

omit [NeZero N₀] [NeZero L] in
theorem Adj.symm {x y : Torus d (N₀ * L ^ k)} (h : Adj x y) : Adj y x := by
  obtain ⟨μ, h | h⟩ := h
  · exact ⟨μ, Or.inr h⟩
  · exact ⟨μ, Or.inl h⟩

namespace GeneratingSet

variable (G : GeneratingSet d L N₀ k ϱ)

/-- The cost `1 / ℓ(b)` of a bond `b = (x, y)`, `ℓ(b) = max (ℓ(x), ℓ(y))` (GREEN.md (1.9) with
`η = 1`). -/
noncomputable def bondCost (x y : Torus d (N₀ * L ^ k)) : ℝ := 1 / max (G.spacing x) (G.spacing y)

theorem bondCost_comm (x y : Torus d (N₀ * L ^ k)) : G.bondCost x y = G.bondCost y x := by
  unfold bondCost; rw [max_comm]

theorem bondCost_nonneg (x y : Torus d (N₀ * L ^ k)) : 0 ≤ G.bondCost x y := by
  unfold bondCost spacing
  positivity

/-- Each step costs at most `1`. -/
theorem bondCost_le_one {x : Torus d (N₀ * L ^ k)} (hx : x ∈ G.Ω 1) (y : Torus d (N₀ * L ^ k)) :
    G.bondCost x y ≤ 1 := by
  obtain ⟨h1, h2, _⟩ := G.layerIndex_spec hx
  have hL : (1 : ℝ) ≤ L := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne L)
  have hs : (1 : ℝ) ≤ G.spacing x := one_le_pow₀ hL
  unfold bondCost
  rw [div_le_one (lt_of_lt_of_le one_pos (hs.trans (le_max_left _ _)))]
  exact hs.trans (le_max_left _ _)

/-- `PathCost x y c`: a nearest-neighbour path from `x` to `y` inside `Ω₁` with total cost `c`. -/
inductive PathCost : Torus d (N₀ * L ^ k) → Torus d (N₀ * L ^ k) → ℝ → Prop
  | refl (x : Torus d (N₀ * L ^ k)) : x ∈ G.Ω 1 → PathCost x x 0
  | step (x y z : Torus d (N₀ * L ^ k)) (c : ℝ) :
      x ∈ G.Ω 1 → Adj x y → PathCost y z c → PathCost x z (G.bondCost x y + c)

variable {G}

theorem PathCost.congr_cost {x y : Torus d (N₀ * L ^ k)} {c c' : ℝ} (h : G.PathCost x y c)
    (e : c = c') : G.PathCost x y c' := e ▸ h

theorem PathCost.nonneg {x y : Torus d (N₀ * L ^ k)} {c : ℝ} (h : G.PathCost x y c) : 0 ≤ c := by
  induction h with
  | refl => exact le_rfl
  | step x y z c _ _ _ ih => exact add_nonneg (G.bondCost_nonneg x y) ih

theorem PathCost.left_mem {x y : Torus d (N₀ * L ^ k)} {c : ℝ} (h : G.PathCost x y c) :
    x ∈ G.Ω 1 := by
  cases h with
  | refl _ hx => exact hx
  | step _ _ _ _ hx => exact hx

theorem PathCost.right_mem {x y : Torus d (N₀ * L ^ k)} {c : ℝ} (h : G.PathCost x y c) :
    y ∈ G.Ω 1 := by
  induction h with
  | refl _ hx => exact hx
  | step _ _ _ _ _ _ _ ih => exact ih

theorem PathCost.trans {x y z : Torus d (N₀ * L ^ k)} {c c' : ℝ} (h : G.PathCost x y c)
    (h' : G.PathCost y z c') : G.PathCost x z (c + c') := by
  induction h with
  | refl x hx => exact h'.congr_cost (by ring)
  | step x w y c hx hadj _ ih =>
      exact (PathCost.step x w z _ hx hadj (ih h')).congr_cost (by ring)

theorem PathCost.snoc {x y z : Torus d (N₀ * L ^ k)} {c : ℝ} (h : G.PathCost x y c)
    (hadj : Adj y z) (hz : z ∈ G.Ω 1) : G.PathCost x z (c + G.bondCost y z) :=
  h.trans ((PathCost.step y z z _ h.right_mem hadj (PathCost.refl z hz)).congr_cost (by ring))

theorem PathCost.symm {x y : Torus d (N₀ * L ^ k)} {c : ℝ} (h : G.PathCost x y c) :
    G.PathCost y x c := by
  induction h with
  | refl x hx => exact PathCost.refl x hx
  | step x y z c hx hadj hp ih =>
      exact (ih.snoc hadj.symm hx).congr_cost (by rw [bondCost_comm]; ring)

/-- **The path metric** (1.9) of GREEN.md (fine unit spacing): the infimum over paths inside `Ω₁` of
`∑ 1/ℓ(b)`, valued in `ℝ≥0∞` (`⊤` when there is no such path). -/
noncomputable def pathDist (G : GeneratingSet d L N₀ k ϱ) (x y : Torus d (N₀ * L ^ k)) :
    ENNReal :=
  ⨅ (c : ℝ) (_ : G.PathCost x y c), ENNReal.ofReal c

theorem pathDist_le {x y : Torus d (N₀ * L ^ k)} {c : ℝ} (h : G.PathCost x y c) :
    G.pathDist x y ≤ ENNReal.ofReal c :=
  iInf₂_le c h

theorem pathDist_self {x : Torus d (N₀ * L ^ k)} (hx : x ∈ G.Ω 1) : G.pathDist x x = 0 := by
  simpa using pathDist_le (PathCost.refl x hx)

theorem pathDist_comm (x y : Torus d (N₀ * L ^ k)) : G.pathDist x y = G.pathDist y x := by
  refine le_antisymm ?_ ?_ <;>
  · refine le_iInf₂ fun c hc => ?_
    exact pathDist_le hc.symm

theorem pathDist_triangle (x y z : Torus d (N₀ * L ^ k)) :
    G.pathDist x z ≤ G.pathDist x y + G.pathDist y z := by
  unfold pathDist
  simp only [ENNReal.iInf_add, ENNReal.add_iInf]
  refine le_iInf₂ fun c hc => le_iInf₂ fun c' hc' => ?_
  calc ⨅ (c : ℝ) (_ : G.PathCost x z c), ENNReal.ofReal c ≤ ENNReal.ofReal (c' + c) :=
        iInf₂_le (c' + c) (hc'.trans hc)
    _ = ENNReal.ofReal c' + ENNReal.ofReal c := ENNReal.ofReal_add hc'.nonneg hc.nonneg

/-- A single bond between sites of `Ω₁` is a path of cost `1 / ℓ(b)`. -/
theorem pathDist_le_bondCost {x y : Torus d (N₀ * L ^ k)} (hx : x ∈ G.Ω 1) (hy : y ∈ G.Ω 1)
    (hadj : Adj x y) : G.pathDist x y ≤ ENNReal.ofReal (G.bondCost x y) :=
  pathDist_le ((PathCost.step x y y _ hx hadj (PathCost.refl y hy)).congr_cost (by ring))

end GeneratingSet

end Balaban.Multiscale
