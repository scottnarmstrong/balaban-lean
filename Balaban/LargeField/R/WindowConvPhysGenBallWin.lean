/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.WindowConvPhysGenBallHist
public import Balaban.LargeField.R.WindowOfHistory
public import Balaban.LargeField.R.WindowRegionGeom
public import Balaban.LargeField.R.RRipeCard
public import Balaban.LargeField.R.ZeroDomainSep

/-!
# The window generating set agrees with `𝔹_k` on a ball around a piece

P7 (2.14), geometric half.  Let `x` be a site of the piece `(j, c)` of the window of a ripe
component `Z` (`k₁ ≤ j ≤ m'`, `k = m' + 1`), i.e. the `π_{j+1}`-cube of `x` is in `c` and its
`π_j`-cube is outside `Lin_j(c)`.  For `y` within `t · L^j M` of `x`, `1 ≤ m ≤ j + 1`:
`y ∈ Ω_m(window) ↔ y ∈ Ω_m(𝔹_k)`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open Balaban Balaban.Multiscale RegionHistory

namespace RegionHistory

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K M : ℕ} [NeZero M]
  [NeZero S.L] {H : RegionHistory S n R k0 K} {m' j : ℕ} {Z : H.Comp (m' + 1)} {g : Geo S n R M}

theorem supDist_ball_mono {q q' t : ℕ} (hqq : q ≤ q') {k : ℕ} {x y : Torus S.d (M * n k * S.L ^ k)}
    (h : supDist y x ≤ t * (S.L ^ q * M)) : supDist y x ≤ t * (S.L ^ q' * M) :=
  h.trans (Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (Nat.pow_le_pow_right
    (Nat.pos_of_ne_zero (NeZero.ne S.L)) hqq)))

/-- A site of the piece has its `π_j`-cube outside `Lin_j(Z)`. -/
theorem piece_not_mem_lin (hmK : m' + 1 ≤ K) (hj : j ≤ m') {c : H.Comp (j + 1)}
    (hc : c ∈ H.ancFin (j + 1) (m' + 1) Z) {x : Torus S.d (M * n (m' + 1) * S.L ^ (m' + 1))}
    (hx1 : cubeMap n S.L M (m' + 1) (j + 1) x ∈ c.1)
    (hx2 : cubeMap n S.L M (m' + 1) j x ∉ H.lin j (j + 1) c) :
    cubeMap n S.L M (m' + 1) j x ∉ ((H.lin j (m' + 1) Z : Finset (Torus S.d (n j))) : Set _) :=
  fun h => hx2 (cube_mem_lin_of_anc hmK hj hc hx1 (Finset.mem_coe.mp h))

/-- Near a site of the piece the `π_{j+1}`-cube lies in `Lin_{j+1}(Z)` only if it lies in `c`. -/
theorem cube_mem_of_ball (hmK : m' + 1 ≤ K) (hj : j ≤ m') {c : H.Comp (j + 1)}
    {x y : Torus S.d (M * n (m' + 1) * S.L ^ (m' + 1))}
    (hx1 : cubeMap n S.L M (m' + 1) (j + 1) x ∈ c.1) {t : ℕ} (htj : t ≤ ⌊R j⌋₊)
    (hxy : supDist y x ≤ t * (S.L ^ j * M))
    (hy : cubeMap n S.L M (m' + 1) (j + 1) y ∈ ((H.lin (j + 1) (m' + 1) Z : Finset (Torus S.d (n (j + 1)))) : Set _)) :
    cubeMap n S.L M (m' + 1) (j + 1) y ∈ c.1 := by
  obtain ⟨Y, hd, hyY⟩ := mem_lin.mp (Finset.mem_coe.mp hy)
  by_cases hYc : Y = c
  · subst hYc; exact hyY
  · exfalso
    have h1 := cubeMap_supDist_le_of_ball H hmK (show j + 1 ≤ m' + 1 by omega)
      (supDist_ball_mono (show j ≤ j + 1 by omega) hxy)
    have h2 := comp_sep hYc hyY hx1
    have : NeZero S.M := ⟨by have := H.F.ok.one_le_M; omega⟩
    have h3 := H.radius_lt_omega (k := j + 1) (by omega)
    simp only [Nat.add_sub_cancel] at h3
    omega

end RegionHistory

end Balaban.LargeField
