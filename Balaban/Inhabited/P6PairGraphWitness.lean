/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.P6PairGraph
public import Balaban.Inhabited.P6FsharpRootedWitness

/-!
# The joint incidence closure in the slab setting

Combinatorics only.  In the slab setting of `Inhabited/P6PairWitness.lean` (`d = L = 3`,
`k + 1 = 2`, `m₁ = 2`, `n₁ = 100`), for the P6 pair `(H_b, H_m) = (p6BoundaryC, p6OldC)` on the cover
torus of `F♯`, the seed consisting of the active fine site `ustar` and the marked set consisting of
the top patch `(2, ustar)` give a non-empty joint site set `Y_J` containing the seed, and `(Y_J, D_J)`
is an incidence union for both operators with the cell of every reached patch inside `Y_J`.  That
the patch `(2, ustar)` is itself reached (a live eligible centre with `ustar` in its footprint) is
not checked here.
-/

@[expose] public section

namespace Balaban.Inhabited

namespace P6PairGraphWitness

open Balaban Balaban.LargeField Balaban.Localization Balaban.Multiscale Balaban.Localization.Dec2
open Slab

/-- The boundary operator `H^∂` of the slab step on the cover torus. -/
noncomputable abbrev Hbd (n1 : ℕ) [NeZero n1] :
    GeneratingSet 3 3 ((15 * n1) * 3 ^ 2) (1 + 1) (minSep 3 9) :=
  p6BoundaryC (k := 1) (c := 15) (M1 := 9) (m₁ := 2) (Zp := (step n1).Omegaᶜ) (step n1)
    P6PairWitness.hM9 (by norm_num) rfl (by norm_num) P6PairWitness.hρ9 subset_rfl

/-- The old-wall operator `H^-` of the slab step on the cover torus. -/
noncomputable abbrev Hold (n1 : ℕ) [NeZero n1] :
    GeneratingSet 3 3 ((15 * n1) * 3 ^ 2) (1 + 1) (minSep 3 9) :=
  p6OldC (k := 1) (n1 := n1) (c := 15) (M1 := 9) (m₁ := 2) P6PairWitness.hM9 9 (step n1).Z

/-- **Non-vacuity of the joint closure.**  Seed `{ustar}`, `X₁ = {ustar}`, marked set
`{(2, ustar)}`: the site set is non-empty and contains the seed, `(Y_J, D_J)` is an incidence union
for both operators, and every reached patch has its cell inside `Y_J`. -/
theorem joint_instance (n1 : ℕ) [NeZero n1] (a : ℕ → ℝ) (ν : ℝ) :
    let Y := jointSites (coverOf (P6FsharpRootedWitness.Fs n1)) (Hbd n1) (Hold n1) a ν {ustar n1}
      {((1 + 1, ustar n1) : ℕ × CTorus 3 3 (15 * n1) 2 (1 + 1))} (↑({ustar n1} : Finset _) : Set _)
    let D := jointParams (coverOf (P6FsharpRootedWitness.Fs n1)) (Hbd n1) (Hold n1) a ν {ustar n1}
      {((1 + 1, ustar n1) : ℕ × CTorus 3 3 (15 * n1) 2 (1 + 1))} (↑({ustar n1} : Finset _) : Set _)
    ustar n1 ∈ Y ∧ Y.Nonempty ∧
    IsIncUnion (coverOf (P6FsharpRootedWitness.Fs n1)) (Hbd n1) a ν {ustar n1}
      {((1 + 1, ustar n1) : ℕ × CTorus 3 3 (15 * n1) 2 (1 + 1))} Y D ∧
    IsIncUnion (coverOf (P6FsharpRootedWitness.Fs n1)) (Hold n1) a ν {ustar n1}
      {((1 + 1, ustar n1) : ℕ × CTorus 3 3 (15 * n1) 2 (1 + 1))} Y D ∧
    ∀ P ∈ D, ∀ x ∈ cubeP P, x ∈ Y := by
  intro Y D
  have h : ustar n1 ∈ Y := seed_mem_jointSites (by simp)
  exact ⟨h, ⟨_, h⟩, isIncUnion_joint_b, isIncUnion_joint_m, fun _ hP => (joint_cell hP).2⟩

end P6PairGraphWitness

end Balaban.Inhabited
