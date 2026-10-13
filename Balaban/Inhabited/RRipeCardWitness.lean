module

public import Balaban.LargeField.R.RRipeCard
public import Balaban.LargeField.History.InhabitedRipeRemoval

/-!
# Non-vacuity of `RRipeCard`

The landed history `RipeRemoval.ripeRemHistory` (genuine radii `wS`, `k₀ = T`, `K = T + 1`) has
a removed component at scale `T`, and it is admissible.  We instantiate the statements of
`Balaban/LargeField/R/RRipeCard.lean` there: the removed component is a box with at most
`(2ρ_T + 10)^d` cubes, any two of its cubes are at distance `< 2ρ_T + 10`, and the number of
cover boxes meeting its fine lift is at most `(crit_T + 2L)^d` (for a fine frame with
`m₀ = m₁ = 0`, `M = 1`).
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.LargeField RadiiHist RipeRemoval RadiiSet

/-- The thickness inequality `4ρ_j + 21 ≤ n_j` for the history `ripeRemHistory`. -/
theorem ripeRem_thickness : ∀ k, 1 ≤ k → k ≤ Tstar wS →
    4 * wS.rho k + 21 ≤ side wS (bigN wS) (Tstar wS + 1) k := by
  intro k _ hk
  have hk' : k ∈ Finset.range (Tstar wS + 1) := Finset.mem_range.mpr (by omega)
  have h1 : 4 * wS.rho k + 21 ≤ ∑ j ∈ Finset.range (Tstar wS + 1), (4 * wS.rho j + 21) :=
    Finset.single_le_sum (f := fun j => 4 * wS.rho j + 21) (fun _ _ => Nat.zero_le _) hk'
  have h2 : bigN wS ≤ side wS (bigN wS) (Tstar wS + 1) k := by
    unfold RadiiHist.side
    exact Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero (pow_ne_zero _ (NeZero.ne _)))
  have h3 : bigN wS = 1 + ∑ j ∈ Finset.range (Tstar wS + 1), (4 * wS.rho j + 21) := rfl
  omega

/-- **Non-vacuity of `RRipeCard`**: in `ripeRemHistory` there is a removed component `c` at scale
`T`, with the box, cardinality, diameter and cover-box statements. -/
theorem rRipeCard_instance :
    ∃ c : ripeRemHistory.Comp (Tstar wS), c.1 ∈ ripeRemHistory.rem (Tstar wS) ∧
      (∃ (a : Torus wS.d (side wS (bigN wS) (Tstar wS + 1) (Tstar wS)))
          (sd : Fin wS.d → ℕ),
        (c.1 : Set _) = box a sd ∧ ∀ i, 1 ≤ sd i ∧ sd i ≤ wS.crit (Tstar wS)) ∧
      c.1.card ≤ (2 * wS.rho (Tstar wS) + 10) ^ wS.d ∧
      (∀ x ∈ c.1, ∀ y ∈ c.1, supDist x y < 2 * wS.rho (Tstar wS) + 10) ∧
      Nonempty (Def7.FineSizeFrame wS (side wS (bigN wS) (Tstar wS + 1)) 1 (Tstar wS + 1) 0 0) ∧
      ∀ F : Def7.FineSizeFrame wS (side wS (bigN wS) (Tstar wS + 1)) 1 (Tstar wS + 1) 0 0,
        (coverBoxes F (Tstar wS) (c.1 : Set _)).ncard ≤
          (wS.crit (Tstar wS) + 2 * wS.L) ^ wS.d := by
  obtain ⟨c, hc, -⟩ := ripeRemHistory_windowOfHistory_hyp
  have G := wS_good
  have hkK : Tstar wS ≤ Tstar wS + 1 := Nat.le_succ _
  refine ⟨c, hc, ?_, ?_, ?_, ?_, ?_⟩
  · exact RegionHistory.removed_eq_box G ripeRem_thickness ripeRemHistory_admissible hkK hc
  · exact RegionHistory.removed_card_le G ripeRem_thickness ripeRemHistory_admissible hkK hc
  · intro x hx y hy
    exact RegionHistory.removed_supDist_lt G ripeRem_thickness ripeRemHistory_admissible hkK hc hx hy
  · exact Def7.FineSizeFrame.nonempty (by simp)
  · intro F
    exact RegionHistory.removed_coverBoxes_ncard_le G ripeRem_thickness ripeRemHistory_admissible
      F hkK hc

end Balaban.Inhabited
