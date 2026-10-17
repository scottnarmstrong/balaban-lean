/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.ZeroDomainSep
public import Balaban.LargeField.R.RRemovedGeometry
public import Balaban.LargeField.R.WindowNodeCongr
public import Balaban.LargeField.Operators.Quiet

/-!
# The Gaussian blocks of the other ancestors lie outside `V_c` (blocker 4, item S7)

`notes/phase1/LF4R-PLAN.md` §9.3, item S7, W958 finding 3.  Two different components `c ≠ c''` of the same scale
`j + 1` are at distance at least `ω_{j+1} > ⌊R_j⌋ + 5`; a Gaussian block of `c''` lies over a cube of `c''` and a
block of `V_c` over a cube within `⌊R_j⌋ + 2` of `c`, so no block is both.  Hence the output variables of an
ancestor `c` of the window, read off the blocks of `V_c` that are not Gaussian blocks of `c`, are not node
variables of the window.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open Balaban Balaban.Multiscale RegionHistory

section Geom

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K M : ℕ} [NeZero M]
  [NeZero S.L] {H : RegionHistory S n R k0 K}

/-- **A block of `V_c` is not a Gaussian block of a different component `c''` of the same scale.** -/
theorem gaussBlocks_not_mem_Vblk (hMS : M = S.M) {j : ℕ} (hjK : j + 1 ≤ K) {c c'' : H.Comp (j + 1)}
    (hne : c ≠ c'') {y : BlockAt S n M K (j + 1)}
    (hy1 : y ∈ Vblk R (H.localHistory M K (j + 1) c) (j + 1))
    (hy2 : y ∈ gaussBlocks (H.localHistory M K (j + 1) c'') j) : False := by
  subst hMS
  have h1 : blockMap S.M (n (j + 1)) y ∈ nbhd (⌊R j⌋₊ + 2) (c.1 : Set (Torus S.d (n (j + 1)))) := by
    have := (H.mem_Vblk_localHistory hjK c y).1 hy1
    rwa [H.bdryUnb_eq c] at this
  obtain ⟨x0, hx0⟩ := exists_site_in_block (S := S) (n := n) (M := S.M) hjK y
  have h2 := (hy2 x0 hx0).1.2
  have h3 : cubeMap n S.L S.M K (j + 1) x0 ∈ (c''.1 : Set (Torus S.d (n (j + 1)))) := h2
  rw [← blockCube_eq_cubeMap H.F.hnn hjK hx0] at h3
  have h4 : blockMap S.M (n (j + 1)) y ∈ nbhd 3 (c''.1 : Set (Torus S.d (n (j + 1)))) :=
    subset_nbhd 3 _ h3
  have h5 := H.omega_le_of_near hne h1 h4
  have h6 : ⌊R j⌋₊ + 2 + 3 < S.omega (j + 1) := H.radius_lt_omega (k := j + 1) (by omega)
  omega

end Geom

end Balaban.LargeField
