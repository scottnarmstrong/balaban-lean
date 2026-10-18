/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.WindowOffZoneCore

/-!
# The window and the top piece outside `Z`; layers on the balls

P7 p. 500 (2.13): outside `Z = Z_k` the window generating set is `𝔹_k(U_k)`, the minimal generating
set of `U_k = Z^≈` at scale `k`, and the generating set of the top piece `(k - 1, Z)` is
`𝔹_k(U_Z) ∩ Ω_k` there (P6 (2.15)): the two coincide.

* `ext_cast_mem_Omega`, `ext_window_layers_iff`, `ext_full_layer`: outside `Z` the cast site lies in
  `Ω_k` of the step `k - 1`, the layers of the window and of the top piece agree, and the layer of
  `𝔹_k` is `k`;
* `near_ext`: a site near a site outside `Z` is outside `Z` or in the region `X_Z` of the top piece;
* `ball_layerIndex_eq`: on the ball `2 L^j M` around the region of a piece, the layer indices of the
  window and of the piece agree.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open Balaban Balaban.Multiscale Balaban.Fluctuation Balaban.Background RegionHistory

section Ext

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K M : ℕ} [NeZero M]
  [NeZero S.L] {H : RegionHistory S n R k0 K} {m' j : ℕ} {Z : H.Comp (m' + 1)} {g : Geo S n R M}

/-- Outside `Z`, the cast site lies in `Ω_{m'+1}` of the step `m'` of the top piece. -/
theorem ext_cast_mem_Omega (hkK : m' + 1 ≤ K) (hW : H.RipeWindow (m' + 1) Z)
    {y : Torus S.d (M * n (m' + 1) * S.L ^ (m' + 1))} (hyZ : y ∉ (windowOfHistory H Z g hkK hW).Z) :
    torusCast (piece_torus_eq g H.F.hnn hkK le_rfl) y ∈
      fineK1 g.M1 g.c (n (m' + 1)) S.L m' ((H.locRH (m' + 1) Z).step m').Omega := by
  have h := windowOfHistory_hOmK (g := g) hkK hW (by omega) y hyZ
  rw [RegionHistory.windowOfHistory_full_Ω, mem_locGen_succ (by omega)] at h
  rw [mem_fineK1, blockMap_castSite_cube]
  exact h

/-- Outside `Z`, `𝔹_k` is in its top layer `k`. -/
theorem ext_full_layer (hkK : m' + 1 ≤ K) (hW : H.RipeWindow (m' + 1) Z)
    {y : Torus S.d (M * n (m' + 1) * S.L ^ (m' + 1))} (hyZ : y ∉ (windowOfHistory H Z g hkK hW).Z) :
    y ∈ (windowOfHistory H Z g hkK hW).full.Ω (m' + 1) ∧
      (windowOfHistory H Z g hkK hW).full.layerIndex y = m' + 1 := by
  have h := windowOfHistory_hOmK (g := g) hkK hW (by omega) y hyZ
  refine ⟨h, (windowOfHistory H Z g hkK hW).full.layerIndex_eq (by omega) le_rfl
    ((windowOfHistory H Z g hkK hW).full.mem_layer.2 ⟨h, ?_⟩)⟩
  rw [(windowOfHistory H Z g hkK hW).full.top]
  exact Finset.notMem_empty _

/-- **The layers of the window and of the top piece agree outside `Z`** (both are the minimal
generating set of `U_k = Z^≈` at scale `k`). -/
theorem ext_window_layers_iff (hkK : m' + 1 ≤ K) (hW : H.RipeWindow (m' + 1) Z)
    {y : Torus S.d (M * n (m' + 1) * S.L ^ (m' + 1))} (hyZ : y ∉ (windowOfHistory H Z g hkK hW).Z)
    (q : ℕ) (hq : 1 ≤ q) :
    y ∈ ((windowOfHistory H Z g hkK hW).windowGenSet (windowOfHistory_hyp hkK hW)).Ω q ↔
      torusCast (piece_torus_eq g H.F.hnn hkK le_rfl) y ∈
        (locGen g (H.locRH (m' + 1) Z) m' Z.1 (locComp_mem H hkK Z) hkK).Ω q := by
  classical
  set W := windowOfHistory H Z g hkK hW with hWdef
  have hyK : y ∉ W.Zk1 := fun h => hyZ (windowOfHistory_hZ (g := g) hkK hW h)
  have hC : M * n (m' + 1) * S.L ^ (m' + 1) = g.M1 * (g.c * n (m' + 1)) * S.L ^ (m' + 1) := by
    rw [geo_base_eq g]
  have hb : y ∈ W.bdry.Ω q ↔ torusCast hC y ∈
      minLayer g.M1 (g.c * n (m' + 1)) S.L (m' + 1) (m' + 1) (fineMin g (m' + 1) (bdryU H Z)) q := by
    show y ∈ (windowBdry H Z g).Ω q ↔ _
    unfold windowBdry
    rw [castN_mem]
    exact Iff.rfl
  have hUnb : y ∈ W.bdry.Ω q → y ∈ W.Unb := by
    intro h
    by_cases hqm : q ≤ m' + 1
    · exact windowOfHistory_hsupp (g := g) hkK hW y (W.bdry.Ω_antitone le_rfl hq (by omega) h)
    · rw [hb, minLayer_of_gt _ (by omega)] at h
      exact absurd h (Finset.notMem_empty _)
  have hwin : y ∈ (W.windowGenSet (windowOfHistory_hyp hkK hW)).Ω q ↔ y ∈ W.bdry.Ω q := by
    rw [WindowPieces.windowGenSet_Ω]
    simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff, hyK, hyZ, not_false_eq_true,
      and_false, and_true, false_or]
    exact ⟨fun h => h.1, fun h => ⟨h, hUnb h⟩⟩
  have hOm := ext_cast_mem_Omega (g := g) hkK hW hyZ
  have hloc : torusCast (piece_torus_eq g H.F.hnn hkK le_rfl) y ∈
      (locGen g (H.locRH (m' + 1) Z) m' Z.1 (locComp_mem H hkK Z) hkK).Ω q ↔
      torusCast (piece_torus_eq g H.F.hnn hkK le_rfl) y ∈
        minLayer g.M1 (g.c * n (m' + 1)) S.L (m' + 1) (m' + 1)
          (stepU g.M1 g.c (n (m' + 1)) S.L m' ⌊R m'⌋₊ (Z.1 : Set (Torus S.d (n (m' + 1))))) q := by
    unfold locGen genBoundaryLocal
    rw [boundaryGenSet_Ω]
    unfold boundaryLayer
    rw [Finset.mem_union, Finset.mem_sdiff, Finset.mem_inter]
    constructor
    · rintro (⟨-, h2⟩ | ⟨h1, -⟩)
      · exact absurd hOm h2
      · exact h1
    · intro h1
      exact Or.inr ⟨h1, hOm⟩
  rw [hwin, hb, hloc]
  exact Iff.rfl

/-- **Near a site outside `Z`**: a site within `2 L^{m'+1} + 1` of a site outside `Z` is outside `Z`
or in the region `X_Z` of the top piece (`Lin_{m'}(Z)` is far from `Zᶜ ⊆ Ω_{m'+1}`). -/
theorem near_ext (hkK : m' + 1 ≤ K) (hW : H.RipeWindow (m' + 1) Z) (hM : 2 * S.L + 1 ≤ M)
    {y y' : Torus S.d (M * n (m' + 1) * S.L ^ (m' + 1))}
    (hyZ : y ∉ (windowOfHistory H Z g hkK hW).Z) (hd : supDist y y' ≤ 2 * S.L ^ (m' + 1) + 1) :
    y' ∉ (windowOfHistory H Z g hkK hW).Z ∨
      torusCast (piece_torus_eq g H.F.hnn hkK le_rfl) y' ∈ Xfine g (H.locRH (m' + 1) Z) m' Z.1 := by
  classical
  by_cases hy'Z : y' ∈ (windowOfHistory H Z g hkK hW).Z
  · right
    have hy'k : cubeMap n S.L M (m' + 1) (m' + 1) y' ∈ Z.1 := by
      rw [windowOfHistory_Z, mem_locFineFin, mem_locFine_k hkK] at hy'Z
      exact hy'Z
    refine (mem_Xfine_cast_iff g hkK le_rfl Z hkK y').2 ⟨hy'k, fun h' => ?_⟩
    have h := windowOfHistory_hOmK (g := g) hkK hW (by omega) y hyZ
    rw [RegionHistory.windowOfHistory_full_Ω, mem_locGen_succ (by omega),
      ← cubeMap_succ (hnn_k H hkK) (by omega)] at h
    have hz : cubeMap n S.L M (m' + 1) m' y' ∈ ((H.locRH (m' + 1) Z).step m').Z := by
      rw [locRH_Z Z (by omega) (by omega)]
      exact Finset.mem_coe.2 h'
    have hfar := ((H.locRH (m' + 1) Z).step m').fine_far (Nat.pos_of_ne_zero (NeZero.ne S.L))
      (hnn_k H hkK m' (by omega)) h hz
    have hd0 : supDist y y' ≤ 1 * (S.L ^ m' * M) := by
      have hp : 1 ≤ S.L ^ m' := Nat.one_le_iff_ne_zero.2 (by have := NeZero.ne S.L; positivity)
      have e : S.L ^ (m' + 1) = S.L ^ m' * S.L := pow_succ _ _
      nlinarith
    have hc := cubeMap_supDist_le_of_ball H hkK (show m' ≤ m' + 1 by omega) hd0
    have : 2 ≤ S.L := H.F.ok.two_le_L
    nlinarith
  · exact Or.inl hy'Z

/-- **Equal layer indices on the ball around a piece**: on the ball `2 L^j M` around the region
of the piece `(j, c)`, the layer index of a site in the window and of its cast in the piece are
both `j + 1` or both `j`. -/
theorem ball_layerIndex_eq (hkK : m' + 1 ≤ K) (hW : H.RipeWindow (m' + 1) Z) (hj : j ≤ m')
    (hk1j : S.k1 (m' + 1) ≤ j) (hK : j + 1 ≤ K) {c : H.Comp (j + 1)}
    (hc : c ∈ H.ancFin (j + 1) (m' + 1) Z) {x y : Torus S.d (M * n (m' + 1) * S.L ^ (m' + 1))}
    (hx : torusCast (piece_torus_eq g H.F.hnn hkK hj) x ∈ Xfine g (H.locRH (j + 1) c) j c.1)
    (hxy : supDist y x ≤ 2 * (S.L ^ j * M)) :
    ((windowOfHistory H Z g hkK hW).windowGenSet (windowOfHistory_hyp hkK hW)).layerIndex y =
      (locGen g (H.locRH (j + 1) c) j c.1 (locComp_mem H hK c) hK).layerIndex
        (torusCast (piece_torus_eq g H.F.hnn hkK hj) y) := by
  classical
  have hk1 := hW.k1_pos hkK
  set G := (windowOfHistory H Z g hkK hW).windowGenSet (windowOfHistory_hyp hkK hW) with hGdef
  set Gl := locGen g (H.locRH (j + 1) c) j c.1 (locComp_mem H hK c) hK with hGldef
  have hiff : ∀ m, 1 ≤ m → m ≤ j + 1 →
      (torusCast (piece_torus_eq g H.F.hnn hkK hj) y ∈ Gl.Ω m ↔ y ∈ G.Ω m) := fun m h1 h2 =>
    piece_window_layers_iff_ball_two hkK hW hj hk1j hK hc hx hxy h1 h2
  obtain ⟨hyj, -⟩ := full_layerIndex_ball hkK hW hj hk1j hK hc hx hxy
  obtain ⟨hx1, hx2⟩ := (mem_Xfine_cast_iff g hkK hj c hK x).1 hx
  have hRm : 1 ≤ ⌊R m'⌋₊ := by
    refine Nat.le_floor ?_
    have := g.hRlow m'
    have hb : (4 * S.L + 20 : ℝ) ≤ S.Rb := H.F.RH.base
    push_cast; linarith
  have hwj : y ∈ G.Ω j :=
    (windowGenSet_Ω_ball hkK hW hj hk1j hc hx1 hx2 (t := 2) (by omega) (by omega) hxy
      (by omega) (by omega)).2 hyj
  have hwn : y ∉ G.Ω (j + 2) := by
    rcases lt_or_eq_of_le hj with hjm | hjm
    · have hR1 : 2 ≤ ⌊R (j + 1)⌋₊ := by
        refine Nat.le_floor ?_
        have := g.hRlow (j + 1)
        have hb : (4 * S.L + 20 : ℝ) ≤ S.Rb := H.F.RH.base
        have : (2 : ℝ) ≤ S.L := by exact_mod_cast H.F.ok.two_le_L
        push_cast; linarith
      exact windowGenSet_Ω_not_mem_ball (g := g) hkK hW hjm hk1j hc hx1 (t := 2) hR1 hxy le_rfl
        (by omega)
    · subst hjm
      rw [G.top]
      exact Finset.notMem_empty _
  have hln : torusCast (piece_torus_eq g H.F.hnn hkK hj) y ∉ Gl.Ω (j + 2) :=
    locGen_Ω_not_mem_of_gt g (H.locRH (j + 1) c) j c.1 (locComp_mem H hK c) hK le_rfl
  by_cases h1 : y ∈ G.Ω (j + 1)
  · rw [G.layerIndex_eq (by omega) (by omega) (G.mem_layer.2 ⟨h1, hwn⟩),
      Gl.layerIndex_eq (by omega) le_rfl (Gl.mem_layer.2 ⟨(hiff _ (by omega) le_rfl).2 h1, hln⟩)]
  · rw [G.layerIndex_eq (by omega) (by omega) (G.mem_layer.2 ⟨hwj, h1⟩),
      Gl.layerIndex_eq (by omega) (by omega) (Gl.mem_layer.2 ⟨(hiff _ (by omega) (by omega)).2 hwj,
        fun h => h1 ((hiff _ (by omega) le_rfl).1 h)⟩)]

end Ext

end Balaban.LargeField
