/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.WindowOffBall
public import Balaban.LargeField.R.WindowOffMinLayer
public import Balaban.LargeField.Budget.Fine

/-!
# The window and the pieces of scale `k₁` on the core `Z_{k₁}`

P7 p. 500 (2.13): the window generating set is `𝔹_{k₁}(W_{k₁})` on `Z_{k₁}`, and the generating
set of a piece `(k₁, c)` is `(𝔹_{k₁}(W_{k₁} ∩ U_c) ∖ Ω_{k₁+1}) ∪ (𝔹_{k₁+1}(U_c) ∩ Ω_{k₁+1})`
(P6 (2.15)).  On the sites of `Z_{k₁}` whose `π_{k₁+1}`-cube lies in `c` the two coincide:

* `lin_mem_of_near`: a `π_{k₁}`-cube of `Lin_{k₁}(Z)` near such a site lies in `Lin_{k₁}(c)` (the
  other scale-`(k₁+1)` ancestors of `Z` are at distance `≥ ω_{k₁+1}`);
* `core_cast_not_mem_Omega`: such a site is not in `Ω_{k₁+1}` of the step `k₁` of the piece;
* `core_window_layers_iff`: its layers `Ω_q`, `q ≥ 1`, in the window and in the piece agree (both
  are layers of a minimal generating set at scale `k₁`, of sets that agree near the site);
* `core_full_layer`: a data site of the window in `Z_{k₁}` is in layer `k₁` of `𝔹_k`;
* `near_core`: a site near such a site is again such a site or a site of the region `X_c` of the
  piece.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open Balaban Balaban.Multiscale Balaban.Fluctuation Balaban.Background RegionHistory

section Core

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K M : ℕ} [NeZero M]
  [NeZero S.L] {H : RegionHistory S n R k0 K} {m' j : ℕ} {Z : H.Comp (m' + 1)} {g : Geo S n R M}

/-- The width of the components of scale `j + 1` dominates the double margin `2 (⌊R_{j-1}⌋ + 1)`
of scale `j`. -/
theorem margin_lt_omega (H : RegionHistory S n R k0 K) (hj : 1 ≤ j) :
    2 * (⌊R (j - 1)⌋₊ + 1) + S.L + 2 < S.omega (j + 1) := by
  rw [Setting.omega_eq_omegaW S (j + 1), omegaW_succ]
  have h1 : R (j - 1) ≤ S.Rb * S.lam j ^ 2 := by
    refine (H.F.RH.le (j - 1)).trans ?_
    have hb : (0 : ℝ) ≤ S.Rb := by have := H.F.RH.base; linarith
    have hm : S.lam (j - 1) ≤ S.lam j := H.F.RH.mono (by omega)
    have h0 : (0 : ℝ) ≤ S.lam (j - 1) := by have := H.F.RH.one_le (j - 1); linarith
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h0 hm 2) hb
  have h2 : ⌊R (j - 1)⌋₊ ≤ ⌊S.Rb * S.lam j ^ 2⌋₊ := Nat.floor_le_floor h1
  omega

/-- **A cube of `Lin_j(Z)` near a site whose `π_{j+1}`-cube lies in `c` lies in `Lin_j(c)`**. -/
theorem lin_mem_of_near (hkK : m' + 1 ≤ K) (hj1 : 1 ≤ j) (hj : j ≤ m') {c : H.Comp (j + 1)}
    {y : Torus S.d (M * n (m' + 1) * S.L ^ (m' + 1))}
    (hyc : cubeMap n S.L M (m' + 1) (j + 1) y ∈ c.1) {u : Torus S.d (n j)}
    (hu : u ∈ H.lin j (m' + 1) Z)
    (hd : supDist u (cubeMap n S.L M (m' + 1) j y) ≤ 2 * (⌊R (j - 1)⌋₊ + 1) + 1) :
    u ∈ H.lin j (j + 1) c := by
  obtain ⟨Y, hdY, huY⟩ := mem_lin.mp hu
  obtain ⟨W, h1, -⟩ := Desc.split (show j ≤ j + 1 by omega) (show j + 1 ≤ m' + 1 by omega) hdY
  obtain ⟨w, rfl⟩ := cubeMap_surjective (S := S) (n := n) (M := M) (K := m' + 1)
    (hnn_k H hkK) (show j ≤ m' + 1 by omega) u
  have hwW : cubeMap n S.L M (m' + 1) (j + 1) w ∈ W.1 :=
    cubeMap_mem_of_desc' (hnn_k H hkK) (show j + 1 ≤ m' + 1 by omega) h1 huY
  have hWc : W = c := by
    by_contra hne
    have hsep := comp_sep hne hwW hyc
    have hb := supDist_blockMap_le (L := S.L) (m := n (j + 1)) (hnn_k H hkK j (by omega))
      (cubeMap n S.L M (m' + 1) j w) (cubeMap n S.L M (m' + 1) j y)
    rw [cubeMap_succ (hnn_k H hkK) (by omega), cubeMap_succ (hnn_k H hkK) (by omega)] at hb
    have hdiv := Nat.div_le_self (supDist (cubeMap n S.L M (m' + 1) j w)
      (cubeMap n S.L M (m' + 1) j y) + S.L - 1) S.L
    have hω := margin_lt_omega H hj1
    omega
  subst hWc
  exact mem_lin.mpr ⟨Y, h1, huY⟩

/-- A site of `Z_{k₁}` whose `π_{k₁+1}`-cube lies in `c` is not in `Ω_{k₁+1}` of the step `k₁` of
the piece `(k₁, c)`. -/
theorem core_cast_not_mem_Omega (hkK : m' + 1 ≤ K) (hW : H.RipeWindow (m' + 1) Z) (hj : j ≤ m')
    (hjk1 : j = S.k1 (m' + 1)) {c : H.Comp (j + 1)} (hc : c ∈ H.ancFin (j + 1) (m' + 1) Z)
    {y : Torus S.d (M * n (m' + 1) * S.L ^ (m' + 1))} (hyK : y ∈ (windowOfHistory H Z g hkK hW).Zk1)
    (hyc : cubeMap n S.L M (m' + 1) (j + 1) y ∈ c.1) :
    torusCast (piece_torus_eq g H.F.hnn hkK hj) y ∉
      fineK1 g.M1 g.c (n (j + 1)) S.L j ((H.locRH (j + 1) c).step j).Omega := by
  intro h
  rw [mem_fineK1, blockMap_castSite_cube, mem_locOmega_iff' (show j + 1 ≤ K by omega) c
    (Nat.lt_succ_self j), lin_self] at h
  have h' : cubeMap n S.L M (m' + 1) (j + 1) y ∈ (H.step j).Omega := by
    rcases h with h | h
    · exact h
    · exact absurd (Finset.mem_coe.2 hyc) h
  have htop := windowOfHistory_hZk1top (g := g) hkK hW y hyK
  rw [← hjk1] at htop
  exact htop ((mem_locGen_succ_iff hkK H.F.ok.two_le_L (fun j _ _ => g.hRlow j) hc hj hyc).2 h')

/-- `Lin_j(c) ⊆ Lin_j(Z)` for an ancestor `c` of `Z`. -/
theorem lin_anc_subset {c : H.Comp (j + 1)} (hc : c ∈ H.ancFin (j + 1) (m' + 1) Z)
    {u : Torus S.d (n j)} (hu : u ∈ H.lin j (j + 1) c) : u ∈ H.lin j (m' + 1) Z := by
  obtain ⟨Y, hd, huY⟩ := mem_lin.mp hu
  exact mem_lin.mpr ⟨Y, hd.trans (mem_ancFin.mp hc), huY⟩

/-- **The layers of the window and of the piece `(k₁, c)` agree on the core** (P7 (2.13), P6
(2.15)): for a site `y` of `Z_{k₁}` whose `π_{k₁+1}`-cube lies in `c` and every `q ≥ 1`,
`y ∈ Ω_q(𝔹_{k₁,k}) ↔ cast y ∈ Ω_q(G^c_{k₁+1})`. -/
theorem core_window_layers_iff (hkK : m' + 1 ≤ K) (hW : H.RipeWindow (m' + 1) Z) (hj : j ≤ m')
    (hjk1 : j = S.k1 (m' + 1)) (hK : j + 1 ≤ K) {c : H.Comp (j + 1)}
    (hc : c ∈ H.ancFin (j + 1) (m' + 1) Z) {y : Torus S.d (M * n (m' + 1) * S.L ^ (m' + 1))}
    (hyK : y ∈ (windowOfHistory H Z g hkK hW).Zk1)
    (hyc : cubeMap n S.L M (m' + 1) (j + 1) y ∈ c.1) (q : ℕ) :
    y ∈ ((windowOfHistory H Z g hkK hW).windowGenSet (windowOfHistory_hyp hkK hW)).Ω q ↔
      torusCast (piece_torus_eq g H.F.hnn hkK hj) y ∈
        (locGen g (H.locRH (j + 1) c) j c.1 (locComp_mem H hK c) hK).Ω q := by
  classical
  have hOm := core_cast_not_mem_Omega (g := g) hkK hW hj hjk1 hc hyK hyc
  have hk1 : 1 ≤ j := hjk1 ▸ hW.k1_pos hkK
  have hL := H.F.ok.two_le_L
  set W := windowOfHistory H Z g hkK hW with hWdef
  have hyZ : y ∈ W.Z := windowOfHistory_hZ (g := g) hkK hW hyK
  -- the window side: the core piece
  have hwin : y ∈ (W.windowGenSet (windowOfHistory_hyp hkK hW)).Ω q ↔ y ∈ W.core.Ω q := by
    rw [WindowPieces.windowGenSet_Ω]
    simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff, hyK, hyZ, not_true_eq_false,
      and_false, or_false, and_true]
  have hC : M * n (m' + 1) * S.L ^ (m' + 1) = g.M1 * (g.c * n (m' + 1)) * S.L ^ (m' + 1) := by
    rw [geo_base_eq g]
  have hcore : y ∈ W.core.Ω q ↔ torusCast hC y ∈
      minLayer g.M1 (g.c * n (m' + 1)) S.L (m' + 1) j (fineMin g j (coreW H Z j)) q := by
    rw [hjk1]
    show y ∈ (windowCore H Z g _ _).Ω q ↔ _
    unfold windowCore
    rw [castN_mem]
    exact Iff.rfl
  -- the piece side: the scale-`k₁` part of the local family
  have hloc : torusCast (piece_torus_eq g H.F.hnn hkK hj) y ∈
      (locGen g (H.locRH (j + 1) c) j c.1 (locComp_mem H hK c) hK).Ω q ↔
      torusCast (piece_torus_eq g H.F.hnn hkK hj) y ∈
        minLayer g.M1 (g.c * n (j + 1)) S.L (j + 1) j
          (stepWLoc g.M1 g.c (n (j + 1)) S.L j ⌊R (j - 1)⌋₊ ⌊R j⌋₊
            ((H.locRH (j + 1) c).step j).Z (c.1 : Set (Torus S.d (n (j + 1))))) q := by
    unfold locGen genBoundaryLocal
    rw [boundaryGenSet_Ω]
    unfold boundaryLayer
    rw [Finset.mem_union, Finset.mem_sdiff, Finset.mem_inter]
    constructor
    · rintro (⟨h1, -⟩ | ⟨-, h2⟩)
      · exact h1
      · exact absurd h2 hOm
    · intro h1
      exact Or.inl ⟨h1, hOm⟩
  rw [hwin, hcore, hloc]
  -- transport to the window presentation
  have hT : g.M1 * (g.c * n (j + 1)) * S.L ^ (j + 1) =
      g.M1 * (g.c * n (m' + 1)) * S.L ^ (m' + 1) := (piece_torus_eq g H.F.hnn hkK hj).symm.trans hC
  set X' : Finset (Torus S.d (g.M1 * (g.c * n (m' + 1)) * S.L ^ (m' + 1))) :=
    Finset.univ.filter fun z => torusCast hT.symm z ∈
      stepWLoc g.M1 g.c (n (j + 1)) S.L j ⌊R (j - 1)⌋₊ ⌊R j⌋₊
        ((H.locRH (j + 1) c).step j).Z (c.1 : Set (Torus S.d (n (j + 1)))) with hX'
  have hX : ∀ x, x ∈ stepWLoc g.M1 g.c (n (j + 1)) S.L j ⌊R (j - 1)⌋₊ ⌊R j⌋₊
      ((H.locRH (j + 1) c).step j).Z (c.1 : Set (Torus S.d (n (j + 1)))) ↔
      torusCast hT x ∈ X' := fun x => by
    rw [hX', Finset.mem_filter, torusCast_symm_cast]; simp
  rw [minLayer_torusCast hT (Nat.le_succ j) (by omega : j ≤ m' + 1) hX q, winOff_torusCast_trans]
  by_cases hq : q ≤ j
  · refine minLayer_local _ hL (by omega : j ≤ m' + 1) hq fun z hz => ?_
    -- the two sets agree near `y`
    obtain ⟨z0, rfl⟩ : ∃ z0, z = torusCast hC z0 :=
      ⟨torusCast hC.symm z, (torusCast_cast_symm hC z).symm⟩
    rw [supDist_torusCast_eq] at hz
    have hd0 : supDist z0 y ≤ 1 * (S.L ^ j * M) := by
      rw [supDist_comm]
      have hM : 12 * g.M1 ≤ M := by
        have h1 := g.hM; have h2 := g.hc
        calc 12 * g.M1 ≤ g.c * g.M1 := Nat.mul_le_mul_right _ (by omega)
          _ = M := h1.symm
      calc supDist y z0 ≤ 12 * g.M1 * S.L ^ j := hz
        _ = S.L ^ j * (12 * g.M1) := by ring
        _ ≤ S.L ^ j * M := Nat.mul_le_mul_left _ hM
        _ = 1 * (S.L ^ j * M) := by ring
    have hd1 := cubeMap_supDist_le_of_ball H hkK (by omega : j ≤ m' + 1) hd0
    have hd2 := cubeMap_supDist_le_of_ball H hkK (show j + 1 ≤ m' + 1 by omega)
      (supDist_ball_mono (Nat.le_succ j) hd0)
    rw [fineMin, mem_cubePre, blockMap_castSite_cube, hX', Finset.mem_filter,
      winOff_torusCast_trans]
    simp only [Finset.mem_univ, true_and]
    unfold stepWLoc stepW stepU
    rw [Finset.mem_inter, fineK, fineK1, mem_cubePre, mem_cubePre, blockMap_castSite_cube,
      blockMap_castSite_cube]
    unfold coreW
    rw [locRH_Z Z (by omega : j ≤ m' + 1) (by omega), locRH_Z c (Nat.le_succ j) (by omega), thick2_eq,
      thick2_eq]
    have hU : cubeMap n S.L M (m' + 1) (j + 1) z0 ∈ thick ⌊R j⌋₊ (c.1 : Set _) := by
      unfold thick
      exact mem_nbhd.2 ⟨_, Finset.mem_coe.2 hyc, by omega⟩
    simp only [hU, and_true]
    constructor
    · rintro hw
      obtain ⟨u, hu, hwu⟩ := mem_nbhd.1 hw
      exact mem_nbhd.2 ⟨u, fun h => hu (Finset.mem_coe.2 (lin_anc_subset hc (Finset.mem_coe.1 h))),
        hwu⟩
    · rintro hw
      obtain ⟨u, hu, hwu⟩ := mem_nbhd.1 hw
      refine mem_nbhd.2 ⟨u, fun h => hu (Finset.mem_coe.2 (lin_mem_of_near hkK hk1 hj hyc
        (Finset.mem_coe.1 h) ?_)), hwu⟩
      have t := supDist_triangle u (cubeMap n S.L M (m' + 1) j z0) (cubeMap n S.L M (m' + 1) j y)
      have t2 := supDist_comm u (cubeMap n S.L M (m' + 1) j z0)
      omega
  · push Not at hq
    rw [minLayer_of_gt _ hq, minLayer_of_gt _ hq]

end Core

end Balaban.LargeField
