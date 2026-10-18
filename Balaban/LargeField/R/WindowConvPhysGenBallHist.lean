/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.ZeroDomainD
public import Balaban.LargeField.R.WindowRegion

/-!
# Layers of the localized history on a ball around a site outside `Z_j`

P7 (2.14), geometric half.  If the `π_j`-cube of `x` is outside `Z_j = Lin_j(Z)`, then every site
`y` within `t` cubes of side `L^j M` of `x` lies in `Ω_j` of the generating set of the localization
of `Z`, as long as `t ≤ ⌊2 R_{j-1}⌋ + 6` (the margin of `Ω_jᶜ` inside `Z_j`).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open Balaban Balaban.Multiscale RegionHistory

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K M : ℕ} [NeZero M]
  [NeZero S.L] {k : ℕ}

/-- Sites within `t · L^j M` have `π_j`-cubes within `t`. -/
theorem cubeMap_supDist_le_of_ball (H : RegionHistory S n R k0 K) (hkK : k ≤ K) {j : ℕ} (hjk : j ≤ k) {t : ℕ}
    {x y : Torus S.d (M * n k * S.L ^ k)} (h : supDist y x ≤ t * (S.L ^ j * M)) :
    supDist (cubeMap n S.L M k j y) (cubeMap n S.L M k j x) ≤ t := by
  have hpos : 0 < S.L ^ j * M := Nat.pos_of_ne_zero (by
    have := NeZero.ne S.L; have := NeZero.ne M; positivity)
  have := supDist_blockMap_le (d := S.d) (L := S.L ^ j * M) (m := n j)
    (fine_eq (hnn_k H hkK) hjk) y x
  refine this.trans ?_
  have : (supDist y x + S.L ^ j * M - 1) / (S.L ^ j * M) ≤ t := by
    rw [Nat.div_le_iff_le_mul_add_pred hpos]
    generalize S.L ^ j * M = P at hpos h ⊢
    rw [mul_comm P t] at *; omega
  exact this

/-- On the ball, `y ∈ Ω_j` of the localized generating set. -/
theorem mem_locGen_of_ball (H : RegionHistory S n R k0 K) (hkK : k ≤ K) {Z : H.Comp k} {i : ℕ} (hik : i + 1 ≤ k) {t : ℕ}
    (ht : t ≤ ⌊2 * R i⌋₊ + 6) {x y : Torus S.d (M * n k * S.L ^ k)}
    (hx : cubeMap n S.L M k (i + 1) x ∉ ((H.lin (i + 1) k Z : Finset (Torus S.d (n (i + 1)))) : Set _))
    (hxy : supDist y x ≤ t * (S.L ^ (i + 1) * M))
    (hL : 2 ≤ S.L) (hR : ∀ j, 1 ≤ j → j < k → S.Rb ≤ R j) :
    y ∈ (H.locGen Z M hkK hL hR).Ω (i + 1) := by
  have : NeZero S.M := ⟨by have := H.F.ok.one_le_M; omega⟩
  rw [mem_locGen_succ (by omega)]
  by_contra hy
  refine hx (nbhd_Omega_compl_subset_lin H hkK Z hik hy ?_)
  have := cubeMap_supDist_le_of_ball H hkK hik hxy
  rw [supDist_comm]; omega

end Balaban.LargeField
