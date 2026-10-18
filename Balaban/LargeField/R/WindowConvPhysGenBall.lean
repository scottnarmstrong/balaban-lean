/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.WindowConvPhysGenBallWin
public import Balaban.LargeField.R.WindowConvPhysGenBallPiece
public import Balaban.LargeField.R.WindowConvPhysReadPiece

/-!
# Equal layers of the piece and of the window on a ball around the piece

P7 (2.14), geometric half (blocker 4, `hswitch`).  For a piece `(j, c)` of the window of a ripe
component `Z` (`k₁ ≤ j ≤ m'`) and a site `x` of the piece (cast to the piece torus it lies in
`Xfine`), every site `y` with `supDist y x ≤ t · L^j M` satisfies, for `1 ≤ m ≤ j + 1`,
`cast y ∈ Ω_m(locGen of the piece) ↔ y ∈ Ω_m(windowGenSet)`.  The radius is admissible for
`t ≤ ⌊R_{j-1}⌋ + 2`, `t ≤ ⌊R_{m'}⌋ + 1`, `t ≤ ⌊R_j⌋`; in particular `t = 2`, and `t = ⌊R_base⌋`
if `j ≥ 2`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open Balaban Balaban.Multiscale Balaban.Fluctuation RegionHistory

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K M : ℕ} [NeZero M]
  [NeZero S.L] {H : RegionHistory S n R k0 K} {m' j : ℕ} {Z : H.Comp (m' + 1)} {g : Geo S n R M}

/-- **Equal layers on the ball** (P7 (2.14), geometric half). -/
theorem piece_window_layers_iff_ball (hkK : m' + 1 ≤ K) (hW : H.RipeWindow (m' + 1) Z)
    (hj : j ≤ m') (hk1j : S.k1 (m' + 1) ≤ j) (hK : j + 1 ≤ K) {c : H.Comp (j + 1)}
    (hc : c ∈ H.ancFin (j + 1) (m' + 1) Z)
    {x y : Torus S.d (M * n (m' + 1) * S.L ^ (m' + 1))}
    (hx : torusCast (piece_torus_eq g H.F.hnn hkK hj) x ∈ Xfine g (H.locRH (j + 1) c) j c.1)
    {t : ℕ} (ht1 : t ≤ ⌊R (j - 1)⌋₊ + 2) (ht2 : t ≤ ⌊R m'⌋₊ + 1) (htj : t ≤ ⌊R j⌋₊)
    (hxy : supDist y x ≤ t * (S.L ^ j * M)) {m : ℕ} (hm1 : 1 ≤ m) (hmj : m ≤ j + 1) :
    torusCast (piece_torus_eq g H.F.hnn hkK hj) y ∈
        (locGen g (H.locRH (j + 1) c) j c.1 (locComp_mem H hK c) hK).Ω m ↔
      y ∈ ((windowOfHistory H Z g hkK hW).windowGenSet (windowOfHistory_hyp hkK hW)).Ω m := by
  classical
  obtain ⟨hx1, hx2⟩ := (mem_Xfine_cast_iff g hkK hj c hK x).1 hx
  rw [windowGenSet_Ω_ball hkK hW hj hk1j hc hx1 hx2 ht1 ht2 hxy hm1 hmj]
  have hk1pos := hW.k1_pos hkK
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  have hL := H.F.ok.two_le_L
  have hRnn := H.F.RH.nonneg
  have hnx := piece_not_mem_lin hkK hj hc hx1 hx2
  have hfull : ∀ q, (windowOfHistory H Z g hkK hW).full.Ω q =
      (H.locGen Z M hkK H.F.ok.two_le_L (fun j _ _ => g.hRlow j)).Ω q :=
    fun q => RegionHistory.windowOfHistory_full_Ω hkK hW q
  have hcast : ∀ q (z : Torus S.d (M * n (m' + 1) * S.L ^ (m' + 1))),
      blockMap (S.L ^ q * (g.c * g.M1)) (n q) (torusCast (piece_torus_eq g H.F.hnn hkK hj) z) =
        cubeMap n S.L M (m' + 1) q z := fun q z => blockMap_castSite_cube g _ q z
  have hd1 := cubeMap_supDist_le_of_ball H hkK (show i + 1 + 1 ≤ m' + 1 by omega)
    (supDist_ball_mono (show i + 1 ≤ i + 1 + 1 by omega) hxy)
  have hd0 := cubeMap_supDist_le_of_ball H hkK (show i + 1 ≤ m' + 1 by omega) hxy
  have hyU : torusCast (piece_torus_eq g H.F.hnn hkK hj) y ∈
      stepU g.M1 g.c (n (i + 1 + 1)) S.L (i + 1) ⌊R (i + 1)⌋₊ (c.1 : Set (Torus S.d (n (i + 1 + 1)))) := by
    unfold stepU
    rw [mem_fineK1, hcast]
    unfold thick
    exact mem_nbhd.2 ⟨_, Finset.mem_coe.2 hx1, by omega⟩
  have hyW : blockMap (S.L ^ (i + 1) * (g.c * g.M1)) (n (i + 1))
      (torusCast (piece_torus_eq g H.F.hnn hkK hj) y) ∈
      nbhd (2 * (⌊R (i + 1 - 1)⌋₊ + 1)) ((((H.locRH (i + 1 + 1) c).step (i + 1)).Z)ᶜ) := by
    rw [hcast]
    refine mem_nbhd.2 ⟨cubeMap n S.L M (m' + 1) (i + 1) x, ?_, by omega⟩
    rw [Set.mem_compl_iff, locRH_Z c (Nat.le_succ _) (by omega)]
    exact fun h => hx2 (Finset.mem_coe.1 h)
  have hyΩ : y ∈ (windowOfHistory H Z g hkK hW).full.Ω (i + 1) := by
    rw [hfull]
    refine mem_locGen_of_ball H hkK (Z := Z) (i := i) (by omega) (t := t) ?_ hnx hxy hL
      (fun j _ _ => g.hRlow j)
    have : ⌊R i⌋₊ ≤ ⌊2 * R i⌋₊ := Nat.floor_le_floor (by linarith [hRnn i])
    simp only [Nat.add_sub_cancel] at ht1
    omega
  by_cases hmle : m ≤ i + 1
  · exact iff_of_true (locGen_Ω_of_near g (H.locRH (i + 1 + 1) c) (i + 1) c.1
      (locComp_mem H hK c) hK hyU hyW hm1 hmle)
      ((windowOfHistory H Z g hkK hW).full.Ω_antitone hm1 hmle (by omega) hyΩ)
  · have hm2 : m = i + 1 + 1 := by omega
    subst hm2
    rw [locGen_Ω_top_iff' g (H.locRH (i + 1 + 1) c) (i + 1) c.1 (locComp_mem H hK c) hK, hfull,
      mem_locGen_succ (by omega), mem_locOmega_iff' hkK Z (show i + 1 < m' + 1 by omega),
      mem_locOmega_iff' hK c (Nat.lt_succ_self _), hcast, lin_self]
    refine ⟨fun h => ?_, fun h => ⟨hyU, ?_⟩⟩
    · rcases h.2 with h2 | h2
      · exact Or.inl h2
      · refine Or.inr fun hl => h2 ?_
        exact Finset.mem_coe.2 (cube_mem_of_ball hkK hj hx1 htj hxy (Finset.mem_coe.1 hl))
    · rcases h with h2 | h2
      · exact Or.inl h2
      · refine Or.inr fun hc' => h2 (Finset.mem_coe.2 (mem_lin.2 ⟨c, mem_ancFin.1 hc, ?_⟩))
        exact Finset.mem_coe.1 hc'

/-- The radius `t = 2` is admissible for every piece. -/
theorem piece_window_layers_iff_ball_two (hkK : m' + 1 ≤ K) (hW : H.RipeWindow (m' + 1) Z)
    (hj : j ≤ m') (hk1j : S.k1 (m' + 1) ≤ j) (hK : j + 1 ≤ K) {c : H.Comp (j + 1)}
    (hc : c ∈ H.ancFin (j + 1) (m' + 1) Z)
    {x y : Torus S.d (M * n (m' + 1) * S.L ^ (m' + 1))}
    (hx : torusCast (piece_torus_eq g H.F.hnn hkK hj) x ∈ Xfine g (H.locRH (j + 1) c) j c.1)
    (hxy : supDist y x ≤ 2 * (S.L ^ j * M)) {m : ℕ} (hm1 : 1 ≤ m) (hmj : m ≤ j + 1) :
    torusCast (piece_torus_eq g H.F.hnn hkK hj) y ∈
        (locGen g (H.locRH (j + 1) c) j c.1 (locComp_mem H hK c) hK).Ω m ↔
      y ∈ ((windowOfHistory H Z g hkK hW).windowGenSet (windowOfHistory_hyp hkK hW)).Ω m := by
  have hk1pos := hW.k1_pos hkK
  have hb : (4 * S.L + 20 : ℝ) ≤ S.Rb := H.F.RH.base
  have hL := H.F.ok.two_le_L
  have h1 : 1 ≤ ⌊R m'⌋₊ := by
    refine Nat.le_floor ?_
    have := g.hRlow m'
    have : (2 : ℝ) ≤ S.L := by exact_mod_cast hL
    push_cast; linarith
  have h2 : 2 ≤ ⌊R j⌋₊ := by
    refine Nat.le_floor ?_
    have := g.hRlow j
    have : (2 : ℝ) ≤ S.L := by exact_mod_cast hL
    push_cast; linarith
  exact piece_window_layers_iff_ball hkK hW hj hk1j hK hc hx (t := 2) (by omega) (by omega)
    (by omega) hxy hm1 hmj

/-- The radius `t = ⌊R_base⌋` is admissible for the pieces with `j ≥ 2`. -/
theorem piece_window_layers_iff_ball_Rb (hkK : m' + 1 ≤ K) (hW : H.RipeWindow (m' + 1) Z)
    (hj : j ≤ m') (hj2 : 2 ≤ j) (hk1j : S.k1 (m' + 1) ≤ j) (hK : j + 1 ≤ K) {c : H.Comp (j + 1)}
    (hc : c ∈ H.ancFin (j + 1) (m' + 1) Z)
    {x y : Torus S.d (M * n (m' + 1) * S.L ^ (m' + 1))}
    (hx : torusCast (piece_torus_eq g H.F.hnn hkK hj) x ∈ Xfine g (H.locRH (j + 1) c) j c.1)
    (hxy : supDist y x ≤ ⌊S.Rb⌋₊ * (S.L ^ j * M)) {m : ℕ} (hm1 : 1 ≤ m) (hmj : m ≤ j + 1) :
    torusCast (piece_torus_eq g H.F.hnn hkK hj) y ∈
        (locGen g (H.locRH (j + 1) c) j c.1 (locComp_mem H hK c) hK).Ω m ↔
      y ∈ ((windowOfHistory H Z g hkK hW).windowGenSet (windowOfHistory_hyp hkK hW)).Ω m := by
  have hfl : ∀ i, 1 ≤ i → ⌊S.Rb⌋₊ ≤ ⌊R i⌋₊ := fun i _ => Nat.floor_le_floor (g.hRlow i)
  exact piece_window_layers_iff_ball hkK hW hj hk1j hK hc hx (t := ⌊S.Rb⌋₊)
    (by have := hfl (j - 1) (by omega); omega) (by have := hfl m' (by omega); omega)
    (hfl j (by omega)) hxy hm1 hmj

/-- The same statement for an `ℓ¹`-ball of radius `2 L^j M`. -/
theorem piece_window_layers_iff_ball_two_torusDist (hkK : m' + 1 ≤ K)
    (hW : H.RipeWindow (m' + 1) Z) (hj : j ≤ m') (hk1j : S.k1 (m' + 1) ≤ j) (hK : j + 1 ≤ K)
    {c : H.Comp (j + 1)} (hc : c ∈ H.ancFin (j + 1) (m' + 1) Z)
    {x y : Torus S.d (M * n (m' + 1) * S.L ^ (m' + 1))}
    (hx : torusCast (piece_torus_eq g H.F.hnn hkK hj) x ∈ Xfine g (H.locRH (j + 1) c) j c.1)
    (hxy : Green.torusDist S.d (M * n (m' + 1) * S.L ^ (m' + 1)) y x ≤
      2 * ((S.L : ℝ) ^ j * M)) {m : ℕ} (hm1 : 1 ≤ m) (hmj : m ≤ j + 1) :
    torusCast (piece_torus_eq g H.F.hnn hkK hj) y ∈
        (locGen g (H.locRH (j + 1) c) j c.1 (locComp_mem H hK c) hK).Ω m ↔
      y ∈ ((windowOfHistory H Z g hkK hW).windowGenSet (windowOfHistory_hyp hkK hW)).Ω m := by
  refine piece_window_layers_iff_ball_two hkK hW hj hk1j hK hc hx ?_ hm1 hmj
  have := supDist_le_torusDist y x
  have h2 : (supDist y x : ℝ) ≤ ((2 * (S.L ^ j * M) : ℕ) : ℝ) := by push_cast; linarith
  exact_mod_cast h2

end Balaban.LargeField
