/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.WindowConvPhysGenBall
public import Balaban.LargeField.R.WindowConvPhysSwitchLocPhys
import Mathlib.Tactic.Linarith

/-!
# The layer agreement of the switch from the geometry of the window

`piece_window_layers_switch` puts the equal layers of the piece and of the window on a ball
(`piece_window_layers_iff_ball_two_torusDist`, `piece_window_layers_empty_above_ball`) in the form
consumed by the stability of the background (`genSet_stability`) and by
`sum_mainActionLoc_eq_gen_of_flow_ballAgree`: for the window of a history
(`windowOfHistory`), a set `X` of sites of the piece region `X_{Z'}` and a site `x` of the piece
torus within `ℓ¹` distance `2 L^j M` of `X`, `x ∈ Ω_q(locGen) ↔ e⁻¹ x ∈ Ω_q(windowGenSet)` for
`1 ≤ q ≤ j + 2`, `e` the torus identification `Equiv.cast`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open Balaban Balaban.Multiscale Balaban.Fluctuation RegionHistory

/-- The `ℓ¹` distance is carried by the identification of two tori of the same side. -/
theorem torusDist_equivCast_symm {d a b : ℕ} [NeZero a] [NeZero b] (h : a = b)
    (x y : Torus d b) :
    Green.torusDist d a ((Equiv.cast (congrArg (Torus d) h)).symm x)
      ((Equiv.cast (congrArg (Torus d) h)).symm y) = Green.torusDist d b x y := by
  subst h; rfl

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K M : ℕ} [NeZero M]
  [NeZero S.L] {H : RegionHistory S n R k0 K} {m' j : ℕ} {Z : H.Comp (m' + 1)} {g : Geo S n R M}

/-- **The layer agreement of the switch** (P7 (2.14), geometric half, in the form of
`genSet_stability`): on the `ℓ¹` ball of radius `2 L^j M` around a set of sites of the piece region,
the layers `Ω_q`, `1 ≤ q ≤ j + 2`, of the piece's generating set and of the window's agree through
the identification of the tori. -/
theorem piece_window_layers_switch (hkK : m' + 1 ≤ K) (hW : H.RipeWindow (m' + 1) Z)
    (hj : j ≤ m') (hk1j : S.k1 (m' + 1) ≤ j) (hK : j + 1 ≤ K) {c : H.Comp (j + 1)}
    (hc : c ∈ H.ancFin (j + 1) (m' + 1) Z)
    (Xs : Finset (Torus S.d (g.M1 * (g.c * n (j + 1)) * S.L ^ (j + 1))))
    (hXs : ∀ z ∈ Xs, z ∈ Xfine g (H.locRH (j + 1) c) j c.1)
    (x : Torus S.d (g.M1 * (g.c * n (j + 1)) * S.L ^ (j + 1)))
    (hx : ∃ z ∈ Xs, Green.torusDist S.d (g.M1 * (g.c * n (j + 1)) * S.L ^ (j + 1)) z x ≤
      2 * ((S.L : ℝ) ^ j * M))
    (q : ℕ) (hq1 : 1 ≤ q) (hq : q ≤ j + 1 + 1) :
    x ∈ (locGen g (H.locRH (j + 1) c) j c.1 (locComp_mem H hK c) hK).Ω q ↔
      (Equiv.cast (congrArg (Torus S.d) (piece_torus_eq g H.F.hnn hkK hj))).symm x ∈
        ((windowOfHistory H Z g hkK hW).windowGenSet (windowOfHistory_hyp hkK hW)).Ω q := by
  set hT := piece_torus_eq g H.F.hnn hkK hj with hhT
  set e := Equiv.cast (congrArg (Torus S.d) hT) with he
  obtain ⟨z, hz, hzx⟩ := hx
  have hey : torusCast hT (e.symm x) = x := by
    rw [← torusCast_equivCast_apply]; exact e.apply_symm_apply x
  have hez : torusCast hT (e.symm z) = z := by
    rw [← torusCast_equivCast_apply]; exact e.apply_symm_apply z
  have hzX : torusCast hT (e.symm z) ∈ Xfine g (H.locRH (j + 1) c) j c.1 := by
    rw [hez]; exact hXs z hz
  have hd : Green.torusDist S.d (M * n (m' + 1) * S.L ^ (m' + 1)) (e.symm x) (e.symm z) ≤
      2 * ((S.L : ℝ) ^ j * M) := by
    rw [torusDist_equivCast_symm hT x z, Green.torusDist_comm_gen]; exact hzx
  by_cases hqj : q ≤ j + 1
  · have := piece_window_layers_iff_ball_two_torusDist hkK hW hj hk1j hK hc hzX hd hq1 hqj
    rwa [hey] at this
  · have hq2 : q = j + 1 + 1 := by omega
    subst hq2
    rcases lt_or_eq_of_le hj with hjm | hjm
    · have hL := H.F.ok.two_le_L
      have ht : 2 ≤ ⌊R (j + 1)⌋₊ := by
        refine Nat.le_floor ?_
        have := g.hRlow (j + 1)
        have hb : (4 * S.L + 20 : ℝ) ≤ S.Rb := H.F.RH.base
        have : (2 : ℝ) ≤ S.L := by exact_mod_cast hL
        push_cast; linarith
      have hsup : supDist (e.symm x) (e.symm z) ≤ 2 * (S.L ^ j * M) := by
        have := supDist_le_torusDist (e.symm x) (e.symm z)
        have h2 : (supDist (e.symm x) (e.symm z) : ℝ) ≤ ((2 * (S.L ^ j * M) : ℕ) : ℝ) := by
          push_cast; linarith
        exact_mod_cast h2
      obtain ⟨h1, h2⟩ := piece_window_layers_empty_above_ball hkK hW hjm hk1j hK hc hzX ht hsup
        (m := j + 1 + 1) (by omega) (by omega)
      rw [hey] at h1
      exact iff_of_false h1 h2
    · subst hjm
      have h1 : x ∉ (locGen g (H.locRH (j + 1) c) j c.1 (locComp_mem H hK c) hK).Ω (j + 1 + 1) := by
        rw [(locGen g (H.locRH (j + 1) c) j c.1 (locComp_mem H hK c) hK).top]
        exact Finset.notMem_empty _
      have h2 : e.symm x ∉
          ((windowOfHistory H Z g hkK hW).windowGenSet (windowOfHistory_hyp hkK hW)).Ω (j + 1 + 1) := by
        rw [((windowOfHistory H Z g hkK hW).windowGenSet (windowOfHistory_hyp hkK hW)).top]
        exact Finset.notMem_empty _
      exact iff_of_false h1 h2

end Balaban.LargeField
