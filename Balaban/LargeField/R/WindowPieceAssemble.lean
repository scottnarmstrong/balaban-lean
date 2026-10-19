/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.WindowPieceLayers
public import Balaban.LargeField.R.WindowPieceDomain

/-!
# The real domain of a piece datum from the domain conditions (blocker 4)

Assembly of `WindowPieceTheta` and `WindowPieceLayers`.  For a piece `C` (a component of `Z^pre_{k+1}`,
`k = i + 1`) of the window, the data sites of the local family are classified by the cube of the site
and the layer of the datum:

* over `Ω_{k+1}` and over `C` (`ψ_{k+1}`, first family of `ChiDomProp`, `piece_theta_sphere`,
  `piece_theta_pair`);
* over `Ω_{k+1}` and not over `C` (outside the component: the small-field region `Y`, the hypothesis
  `hY`, to be supplied by `WindowThetaY`);
* off `Ω_{k+1}` (`ψ_k`, always over `C` and over `Ω_k`): near `Ω_{k+1}` (first family), over `Z_k`
  (first family at scale `k`), or far from `Ω_{k+1}` and not meeting `Z_k` (second family);
* mixed interface pairs (layers `k + 1`, `k`): the first family at the cube of the `ψ_k`-site.

`piece_sphere_all` and `piece_pair_all` give (R2) and (R1) at every data site and interface pair with
the radius `max (max η₁ η₂) (max η₃ η_Y)`; `piece_inDomainR` is the real domain `Ψ̃(G; ν, η)`
(`inDomainR_of_r1_r2`).
-/

@[expose] public section

namespace Balaban.LargeField

open Balaban Balaban.Multiscale Balaban.Background Balaban.LargeField.Def7 RegionHistory

section PieceAssemble

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K : ℕ} {M : ℕ} [NeZero M]
  [NeZero S.L] {N i : ℕ} (H : RegionHistory S n R k0 K) (g : Geo S n R M) (C : H.Comp (i + 1 + 1))
  (hjK : i + 1 + 1 ≤ K)

include hjK in
/-- The cube of a data site of the local family of `C` is within `⌊R_{k}⌋ + 2` cubes of `C`. -/
theorem dataSite_cube_near_comp {s : BgT g (i + 1 + 1)}
    (hs : s ∈ dataSites (locGen g (H.locRH (i + 1 + 1) C) (i + 1) C.1 (locComp_mem H hjK C) hjK)) :
    blockMap (S.L ^ (i + 1 + 1) * (g.c * g.M1)) (n (i + 1 + 1)) s ∈ nbhd (⌊R (i + 1)⌋₊ + 2) C.1 := by
  have h := genBoundaryLocal_subset_V ((H.locRH (i + 1 + 1) C).step (i + 1)) g.hc
    ((H.locRH (i + 1 + 1) C).F.hnn (i + 1) (by omega)) (H.locRH (i + 1 + 1) C).F.ok.two_le_L
    (g.three_L_le_floor (H.locRH (i + 1 + 1) C) (i + 1 - 1))
    ((H.locRH (i + 1 + 1) C).F.stepGeom (show i + 1 < K by omega)).rad.omega_rho
    (Omega_compl_subset_Zpre' (i + 1) ((H.locRH (i + 1 + 1) C).step (i + 1)) _ _)
    (locComp_mem H hjK C) hs
  unfold thick at h
  rw [nbhd_nbhd] at h
  exact h

include hjK in
/-- A cube of `Z^pre_{k+1}` within `⌊R_k⌋ + 2` cubes of the component `C` belongs to `C`
(the components are `ω_{k+1}`-separated). -/
theorem mem_comp_of_near_comp {w : Torus S.d (n (i + 1 + 1))} (hw : w ∈ H.F.Zp (i + 1 + 1))
    (hnear : w ∈ nbhd (⌊R (i + 1)⌋₊ + 2) C.1) : w ∈ C.1 := by
  obtain ⟨z, hz, hd⟩ := mem_nbhd.1 hnear
  have hω := (H.F.stepGeom (show i + 1 < K by omega)).rad.omega_rho
  have hL : 0 < S.L := NeZero.pos S.L
  exact mem_comp_of_close C.2 hz hw (by rw [supDist_comm]; omega)

include hjK in
/-- A data site of the local family of `C` whose cube is not in `C` lies over a cube outside
`Z^pre_{k+1}` (of the whole history). -/
theorem dataSite_cube_not_mem_Zp {s : BgT g (i + 1 + 1)}
    (hs : s ∈ dataSites (locGen g (H.locRH (i + 1 + 1) C) (i + 1) C.1 (locComp_mem H hjK C) hjK))
    (hq : blockMap (S.L ^ (i + 1 + 1) * (g.c * g.M1)) (n (i + 1 + 1)) s ∉ C.1) :
    blockMap (S.L ^ (i + 1 + 1) * (g.c * g.M1)) (n (i + 1 + 1)) s ∉ H.F.Zp (i + 1 + 1) :=
  fun hw => hq (mem_comp_of_near_comp H C hjK hw (dataSite_cube_near_comp H g C hjK hs))

include hjK in
/-- The fine set `Z_{k}` of the localized history is a union of `π_k`-cubes: a cube lies in it or
misses it. -/
theorem cubeSub_Z_or_avoid (q : Torus S.d (n (i + 1))) :
    CubeSub (S := S) (n := n) M K (i + 1) q ((H.localHistory M K (i + 1 + 1) C).Z (i + 1)) ∨
      ∀ z, cubeMap n S.L M K (i + 1) z = q → z ∉ (H.localHistory M K (i + 1 + 1) C).Z (i + 1) := by
  by_cases h : ∃ z0, cubeMap n S.L M K (i + 1) z0 = q ∧ z0 ∈ (H.localHistory M K (i + 1 + 1) C).Z (i + 1)
  · left
    obtain ⟨z0, hz0, hz0Z⟩ := h
    intro z hz
    obtain ⟨h1, h2⟩ := hz0Z
    refine ⟨?_, ?_⟩
    · show cubeMap n S.L M K (i + 1) z ∈ ((H.locRH (i + 1 + 1) C).step (i + 1)).Z
      rw [hz, ← hz0]; exact h1
    · show cubeMap n S.L M K (i + 1 + 1) z ∈ C.1
      rw [← cubeMap_succ H.F.hnn hjK z, hz, ← hz0, cubeMap_succ H.F.hnn hjK z0]; exact h2
  · right
    intro z hz hzZ
    exact h ⟨z, hz, hzZ⟩

include hjK in
/-- **The sphere bound at every data site of the piece** (R2). -/
theorem piece_sphere_all {η1 η2 η3 ηY : ℝ} (ψw : MultiField S n M K N)
    (o : OutT N R (H.localHistory M K (i + 1 + 1) C) (i + 1 + 1))
    (x : NewCfg N (H.localHistory M K (i + 1 + 1) C) (i + 1)) (hv : EuclideanSpace ℝ (Fin N))
    (hF1 : PieceFirstFamily H g C η1 o x) (hF2 : PieceSecondFamily H C η2 o x)
    (hFZ : PieceZkFamily H g C ψw η3)
    (hag : ∀ t : BgT g (i + 1 + 1),
      t ∈ dataSites (locGen g (H.locRH (i + 1 + 1) C) (i + 1) C.1 (locComp_mem H hjK C) hjK) →
      blockMap (S.L ^ (i + 1 + 1) * (g.c * g.M1)) (n (i + 1 + 1)) t ∉ ((H.locRH (i + 1 + 1) C).step (i + 1)).Omega →
      ψw (i + 1) (jBlock S.d S.L (M * n K) K (i + 1) (bgToFine g H.F.hnn hjK t)) =
        pieceField H C o x (i + 1) (jBlock S.d S.L (M * n K) K (i + 1) (bgToFine g H.F.hnn hjK t)))
    (hY : ∀ t : BgT g (i + 1 + 1), t ∈ dataSites (locGen g (H.locRH (i + 1 + 1) C) (i + 1) C.1 (locComp_mem H hjK C) hjK) →
      blockMap (S.L ^ (i + 1 + 1) * (g.c * g.M1)) (n (i + 1 + 1)) t ∉ C.1 →
      |∑ l, ((locData g (H.locRH (i + 1 + 1) C) (i + 1) C.1 (locComp_mem H hjK C) hjK o x hv).Ψ t l).re ^ 2 - 1| < ηY)
    {s : BgT g (i + 1 + 1)} (hs : s ∈ dataSites (locGen g (H.locRH (i + 1 + 1) C) (i + 1) C.1 (locComp_mem H hjK C) hjK)) :
    |∑ l, ((locData g (H.locRH (i + 1 + 1) C) (i + 1) C.1 (locComp_mem H hjK C) hjK o x hv).Ψ s l).re ^ 2 - 1| < max (max η1 η2) (max η3 ηY) := by
  by_cases hO : blockMap (S.L ^ (i + 1 + 1) * (g.c * g.M1)) (n (i + 1 + 1)) s ∈
      ((H.locRH (i + 1 + 1) C).step (i + 1)).Omega
  · by_cases hC : blockMap (S.L ^ (i + 1 + 1) * (g.c * g.M1)) (n (i + 1 + 1)) s ∈ C.1
    · refine lt_of_lt_of_le (piece_theta_sphere H g C hjK o x hv hF1 hs ?_ hO) ?_
      · rw [cubeMap_bgToFine_gen]; exact hC
      · exact (le_max_left _ _).trans (le_max_left _ _)
    · exact lt_of_lt_of_le (hY s hs hC) ((le_max_right _ _).trans (le_max_right _ _))
  · have hy := locGen_dataSite_cube_mem_Omega (i := i) g (H.locRH (i + 1 + 1) C) C.1
      (locComp_mem H hjK C) hjK (locRH_rem (i + 1 + 1) C) hs (by rwa [mem_fineK1])
    by_cases hsim : cubeMap n S.L M K (i + 1 + 1) (bgToFine g H.F.hnn hjK s) ∈
        lhOmegaSim (H.localHistory M K (i + 1 + 1) C) (i + 1 + 1) (i + 1 + 1)
    · exact lt_of_lt_of_le (piece_psi_sphere H g C hjK o x hv hF1 hs hO hy hsim)
        ((le_max_left _ _).trans (le_max_left _ _))
    · rcases cubeSub_Z_or_avoid (M := M) H C hjK (cubeMap n S.L M K (i + 1) (bgToFine g H.F.hnn hjK s)) with hZk | hav
      · exact lt_of_lt_of_le (piece_psi_sphere_Zk H g C hjK ψw o x hv hFZ hs hO hy hZk (hag s hs hO))
          ((le_max_left _ _).trans (le_max_right _ _))
      · refine lt_of_lt_of_le (piece_psi_sphere_far H g C hjK o x hv hF2 hs hO hy hav ?_) ?_
        · intro z hz
          rwa [show cubeMap n S.L M K (i + 1 + 1) z = cubeMap n S.L M K (i + 1 + 1) (bgToFine g H.F.hnn hjK s) by
            rw [← cubeMap_succ H.F.hnn hjK z, ← cubeMap_succ H.F.hnn hjK (bgToFine g H.F.hnn hjK s), hz]]
        · exact (le_max_right _ _).trans (le_max_left _ _)

omit [NeZero M] [NeZero S.L] in
theorem rn_sub_comm' {N : ℕ} (a b : Fin N → ℝ) :
    rn (fun l => a l - b l) = rn (fun l => b l - a l) := by
  unfold rn
  congr 1
  exact Finset.sum_congr rfl fun l _ => by ring

include hjK in
/-- **The pair bound at every interface pair of the piece** (R1). -/
theorem piece_pair_all {η1 η2 η3 ηY : ℝ} (ψw : MultiField S n M K N)
    (o : OutT N R (H.localHistory M K (i + 1 + 1) C) (i + 1 + 1))
    (x : NewCfg N (H.localHistory M K (i + 1 + 1) C) (i + 1)) (hv : EuclideanSpace ℝ (Fin N))
    (hF1 : PieceFirstFamily H g C η1 o x) (hF2 : PieceSecondFamily H C η2 o x)
    (hFZ : PieceZkFamily H g C ψw η3)
    (hag : ∀ t : BgT g (i + 1 + 1),
      t ∈ dataSites (locGen g (H.locRH (i + 1 + 1) C) (i + 1) C.1 (locComp_mem H hjK C) hjK) →
      blockMap (S.L ^ (i + 1 + 1) * (g.c * g.M1)) (n (i + 1 + 1)) t ∉ ((H.locRH (i + 1 + 1) C).step (i + 1)).Omega →
      ψw (i + 1) (jBlock S.d S.L (M * n K) K (i + 1) (bgToFine g H.F.hnn hjK t)) =
        pieceField H C o x (i + 1) (jBlock S.d S.L (M * n K) K (i + 1) (bgToFine g H.F.hnn hjK t)))
    (hY : ∀ t t' : BgT g (i + 1 + 1), t ∈ dataSites (locGen g (H.locRH (i + 1 + 1) C) (i + 1) C.1 (locComp_mem H hjK C) hjK) → t' ∈ dataSites (locGen g (H.locRH (i + 1 + 1) C) (i + 1) C.1 (locComp_mem H hjK C) hjK) →
      IsInterfacePair (locGen g (H.locRH (i + 1 + 1) C) (i + 1) C.1 (locComp_mem H hjK C) hjK) t t' →
      blockMap (S.L ^ (i + 1 + 1) * (g.c * g.M1)) (n (i + 1 + 1)) t ∉ C.1 →
      blockMap (S.L ^ (i + 1 + 1) * (g.c * g.M1)) (n (i + 1 + 1)) t' ∉ C.1 →
      blockMap (S.L ^ (i + 1 + 1) * (g.c * g.M1)) (n (i + 1 + 1)) t ∈ ((H.locRH (i + 1 + 1) C).step (i + 1)).Omega →
      blockMap (S.L ^ (i + 1 + 1) * (g.c * g.M1)) (n (i + 1 + 1)) t' ∈ ((H.locRH (i + 1 + 1) C).step (i + 1)).Omega →
      rn (fun l => ((locData g (H.locRH (i + 1 + 1) C) (i + 1) C.1 (locComp_mem H hjK C) hjK o x hv).Ψ t l).re - ((locData g (H.locRH (i + 1 + 1) C) (i + 1) C.1 (locComp_mem H hjK C) hjK o x hv).Ψ t' l).re) < ηY)
    {s s' : BgT g (i + 1 + 1)} (hs : s ∈ dataSites (locGen g (H.locRH (i + 1 + 1) C) (i + 1) C.1 (locComp_mem H hjK C) hjK)) (hs' : s' ∈ dataSites (locGen g (H.locRH (i + 1 + 1) C) (i + 1) C.1 (locComp_mem H hjK C) hjK))
    (hp : IsInterfacePair (locGen g (H.locRH (i + 1 + 1) C) (i + 1) C.1 (locComp_mem H hjK C) hjK) s s') :
    rn (fun l => ((locData g (H.locRH (i + 1 + 1) C) (i + 1) C.1 (locComp_mem H hjK C) hjK o x hv).Ψ s l).re - ((locData g (H.locRH (i + 1 + 1) C) (i + 1) C.1 (locComp_mem H hjK C) hjK o x hv).Ψ s' l).re) <
      max (max η1 η2) (max η3 ηY) := by
  have hcube := (blockAdj_of_interfacePair H g hjK hp).1
  have hcube' : supDist (cubeMap n S.L M K (i + 1 + 1) (bgToFine g H.F.hnn hjK s))
      (cubeMap n S.L M K (i + 1 + 1) (bgToFine g H.F.hnn hjK s')) ≤ 1 := by
    rw [supDist_comm]; exact hcube
  have hmax1 : η1 ≤ max (max η1 η2) (max η3 ηY) := (le_max_left _ _).trans (le_max_left _ _)
  have hmax2 : η2 ≤ max (max η1 η2) (max η3 ηY) := (le_max_right _ _).trans (le_max_left _ _)
  have hmax3 : η3 ≤ max (max η1 η2) (max η3 ηY) := (le_max_left _ _).trans (le_max_right _ _)
  have hmaxY : ηY ≤ max (max η1 η2) (max η3 ηY) := (le_max_right _ _).trans (le_max_right _ _)
  have hcm : ∀ t : BgT g (i + 1 + 1), cubeMap n S.L M K (i + 1 + 1) (bgToFine g H.F.hnn hjK t) =
      blockMap (S.L ^ (i + 1 + 1) * (g.c * g.M1)) (n (i + 1 + 1)) t := fun t => cubeMap_bgToFine_gen g H.F.hnn hjK _ t
  by_cases hOs : blockMap (S.L ^ (i + 1 + 1) * (g.c * g.M1)) (n (i + 1 + 1)) s ∈
      ((H.locRH (i + 1 + 1) C).step (i + 1)).Omega <;>
  by_cases hOs' : blockMap (S.L ^ (i + 1 + 1) * (g.c * g.M1)) (n (i + 1 + 1)) s' ∈
      ((H.locRH (i + 1 + 1) C).step (i + 1)).Omega
  · -- both over Ω
    by_cases hCs : blockMap (S.L ^ (i + 1 + 1) * (g.c * g.M1)) (n (i + 1 + 1)) s ∈ C.1
    · refine lt_of_lt_of_le (piece_theta_pair H g C hjK o x hv hF1 hs hs' hp (q := cubeMap n S.L M K (i + 1 + 1) (bgToFine g H.F.hnn hjK s))
        (by rw [hcm]; exact hCs) ((omega_loc_iff H C hjK (by rw [hcm]; exact hCs)).1 (by rw [hcm]; exact hOs))
        (by simp [supDist_self]) hcube hOs hOs') hmax1
    · by_cases hCs' : blockMap (S.L ^ (i + 1 + 1) * (g.c * g.M1)) (n (i + 1 + 1)) s' ∈ C.1
      · refine lt_of_lt_of_le (piece_theta_pair H g C hjK o x hv hF1 hs hs' hp (q := cubeMap n S.L M K (i + 1 + 1) (bgToFine g H.F.hnn hjK s'))
          (by rw [hcm]; exact hCs') ((omega_loc_iff H C hjK (by rw [hcm]; exact hCs')).1 (by rw [hcm]; exact hOs'))
          hcube' (by simp [supDist_self]) hOs hOs') hmax1
      · exact lt_of_lt_of_le (hY s s' hs hs' hp hCs hCs' hOs hOs') hmaxY
  · -- s over Ω, s' off
    have hy' := locGen_dataSite_cube_mem_Omega (i := i) g (H.locRH (i + 1 + 1) C) C.1
      (locComp_mem H hjK C) hjK (locRH_rem (i + 1 + 1) C) hs' (by rwa [mem_fineK1])
    exact lt_of_lt_of_le (piece_mixed_pair H g C hjK o x hv hF1 hs hs' (Or.inl hp) hOs hOs' hy') hmax1
  · -- s off, s' over Ω
    have hy := locGen_dataSite_cube_mem_Omega (i := i) g (H.locRH (i + 1 + 1) C) C.1
      (locComp_mem H hjK C) hjK (locRH_rem (i + 1 + 1) C) hs (by rwa [mem_fineK1])
    rw [rn_sub_comm']
    exact lt_of_lt_of_le (piece_mixed_pair H g C hjK o x hv hF1 hs' hs (Or.inr hp) hOs' hOs hy) hmax1
  · -- both off
    have hy := locGen_dataSite_cube_mem_Omega (i := i) g (H.locRH (i + 1 + 1) C) C.1
      (locComp_mem H hjK C) hjK (locRH_rem (i + 1 + 1) C) hs (by rwa [mem_fineK1])
    have hy' := locGen_dataSite_cube_mem_Omega (i := i) g (H.locRH (i + 1 + 1) C) C.1
      (locComp_mem H hjK C) hjK (locRH_rem (i + 1 + 1) C) hs' (by rwa [mem_fineK1])
    by_cases hsim : cubeMap n S.L M K (i + 1 + 1) (bgToFine g H.F.hnn hjK s) ∈
        lhOmegaSim (H.localHistory M K (i + 1 + 1) C) (i + 1 + 1) (i + 1 + 1)
    · exact lt_of_lt_of_le (piece_psi_pair H g C hjK o x hv hF1 hs hs' (Or.inl hp) hOs hOs' hy hy' hsim) hmax1
    · by_cases hsim' : cubeMap n S.L M K (i + 1 + 1) (bgToFine g H.F.hnn hjK s') ∈
          lhOmegaSim (H.localHistory M K (i + 1 + 1) C) (i + 1 + 1) (i + 1 + 1)
      · rw [rn_sub_comm']
        exact lt_of_lt_of_le (piece_psi_pair H g C hjK o x hv hF1 hs' hs (Or.inr hp) hOs' hOs hy' hy hsim') hmax1
      · rcases cubeSub_Z_or_avoid (M := M) H C hjK (cubeMap n S.L M K (i + 1) (bgToFine g H.F.hnn hjK s)) with hZk | hav
        · exact lt_of_lt_of_le (piece_psi_pair_Zk H g C hjK ψw o x hv hFZ hs hs' (Or.inl hp) hOs hOs' hy hy' hZk
            (hag s hs hOs) (hag s' hs' hOs')) hmax3
        · refine lt_of_lt_of_le (piece_psi_pair_far H g C hjK o x hv hF2 hs hs' (Or.inl hp) hOs hOs' hy hy' hav ?_) hmax2
          intro z hz
          rwa [show cubeMap n S.L M K (i + 1 + 1) z = cubeMap n S.L M K (i + 1 + 1) (bgToFine g H.F.hnn hjK s) by
            rw [← cubeMap_succ H.F.hnn hjK z, ← cubeMap_succ H.F.hnn hjK (bgToFine g H.F.hnn hjK s), hz]]

include hjK in
/-- The datum of a piece is real on the data sites. -/
theorem locData_im_eq_zero
    (o : OutT N R (H.localHistory M K (i + 1 + 1) C) (i + 1 + 1))
    (x : NewCfg N (H.localHistory M K (i + 1 + 1) C) (i + 1)) (hv : EuclideanSpace ℝ (Fin N))
    {s : BgT g (i + 1 + 1)}
    (hs : s ∈ dataSites (locGen g (H.locRH (i + 1 + 1) C) (i + 1) C.1 (locComp_mem H hjK C) hjK)) (l : Fin N) :
    ((locData g (H.locRH (i + 1 + 1) C) (i + 1) C.1 (locComp_mem H hjK C) hjK o x hv).Ψ s l).im = 0 := by
  by_cases hO : blockMap (S.L ^ (i + 1 + 1) * (g.c * g.M1)) (n (i + 1 + 1)) s ∈
      ((H.locRH (i + 1 + 1) C).step (i + 1)).Omega
  · rw [locData_Ψ_of_omega (H.locRH (i + 1 + 1) C) C.1 (locComp_mem H hjK C) hjK g o x hv hs hO]
    exact Complex.ofReal_im _
  · rw [locData_Ψ_of_not_omega H g C hjK o x hv hs hO]
    exact Complex.ofReal_im _

include hjK in
/-- The external direction of the datum of a piece is `h` on `Ω₁`. -/
theorem locData_h_eq
    (o : OutT N R (H.localHistory M K (i + 1 + 1) C) (i + 1 + 1))
    (x : NewCfg N (H.localHistory M K (i + 1 + 1) C) (i + 1)) (hv : EuclideanSpace ℝ (Fin N))
    {s : BgT g (i + 1 + 1)}
    (hs : s ∈ (locGen g (H.locRH (i + 1 + 1) C) (i + 1) C.1 (locComp_mem H hjK C) hjK).Ω 1) (l : Fin N) :
    (locData g (H.locRH (i + 1 + 1) C) (i + 1) C.1 (locComp_mem H hjK C) hjK o x hv).h s l =
      ((hv l : ℝ) : ℂ) := by
  unfold locData
  rw [liftMixed_h _ _ _ _ _ _ hs]

include hjK in
/-- **The datum of a piece lies in the real domain** `Ψ̃(G; ν, η)` for
`η = max (max η₁ η₂) (max η₃ η_Y)`, from the domain conditions of the families. -/
theorem piece_inDomainR {η1 η2 η3 ηY ν : ℝ} (ψw : MultiField S n M K N)
    (o : OutT N R (H.localHistory M K (i + 1 + 1) C) (i + 1 + 1))
    (x : NewCfg N (H.localHistory M K (i + 1 + 1) C) (i + 1)) (hv : EuclideanSpace ℝ (Fin N))
    (hν : 0 ≤ ν) (hunit : ‖hv‖ = 1) (hη : 0 < max (max η1 η2) (max η3 ηY))
    (hmass : 2 * ν * ((S.L : ℝ) ^ (i + 1 + 1)) ^ 2 < (max (max η1 η2) (max η3 ηY)) ^ 2)
    (hF1 : PieceFirstFamily H g C η1 o x) (hF2 : PieceSecondFamily H C η2 o x)
    (hFZ : PieceZkFamily H g C ψw η3)
    (hag : ∀ t : BgT g (i + 1 + 1),
      t ∈ dataSites (locGen g (H.locRH (i + 1 + 1) C) (i + 1) C.1 (locComp_mem H hjK C) hjK) →
      blockMap (S.L ^ (i + 1 + 1) * (g.c * g.M1)) (n (i + 1 + 1)) t ∉ ((H.locRH (i + 1 + 1) C).step (i + 1)).Omega →
      ψw (i + 1) (jBlock S.d S.L (M * n K) K (i + 1) (bgToFine g H.F.hnn hjK t)) =
        pieceField H C o x (i + 1) (jBlock S.d S.L (M * n K) K (i + 1) (bgToFine g H.F.hnn hjK t)))
    (hYs : ∀ t : BgT g (i + 1 + 1),
      t ∈ dataSites (locGen g (H.locRH (i + 1 + 1) C) (i + 1) C.1 (locComp_mem H hjK C) hjK) →
      blockMap (S.L ^ (i + 1 + 1) * (g.c * g.M1)) (n (i + 1 + 1)) t ∉ C.1 →
      |∑ l, ((locData g (H.locRH (i + 1 + 1) C) (i + 1) C.1 (locComp_mem H hjK C) hjK o x hv).Ψ t l).re ^ 2 - 1| < ηY)
    (hYp : ∀ t t' : BgT g (i + 1 + 1),
      t ∈ dataSites (locGen g (H.locRH (i + 1 + 1) C) (i + 1) C.1 (locComp_mem H hjK C) hjK) →
      t' ∈ dataSites (locGen g (H.locRH (i + 1 + 1) C) (i + 1) C.1 (locComp_mem H hjK C) hjK) →
      IsInterfacePair (locGen g (H.locRH (i + 1 + 1) C) (i + 1) C.1 (locComp_mem H hjK C) hjK) t t' →
      blockMap (S.L ^ (i + 1 + 1) * (g.c * g.M1)) (n (i + 1 + 1)) t ∉ C.1 →
      blockMap (S.L ^ (i + 1 + 1) * (g.c * g.M1)) (n (i + 1 + 1)) t' ∉ C.1 →
      blockMap (S.L ^ (i + 1 + 1) * (g.c * g.M1)) (n (i + 1 + 1)) t ∈ ((H.locRH (i + 1 + 1) C).step (i + 1)).Omega →
      blockMap (S.L ^ (i + 1 + 1) * (g.c * g.M1)) (n (i + 1 + 1)) t' ∈ ((H.locRH (i + 1 + 1) C).step (i + 1)).Omega →
      rn (fun l => ((locData g (H.locRH (i + 1 + 1) C) (i + 1) C.1 (locComp_mem H hjK C) hjK o x hv).Ψ t l).re -
        ((locData g (H.locRH (i + 1 + 1) C) (i + 1) C.1 (locComp_mem H hjK C) hjK o x hv).Ψ t' l).re) < ηY) :
    InDomainR (locGen g (H.locRH (i + 1 + 1) C) (i + 1) C.1 (locComp_mem H hjK C) hjK) ν
      (max (max η1 η2) (max η3 ηY))
      (locData g (H.locRH (i + 1 + 1) C) (i + 1) C.1 (locComp_mem H hjK C) hjK o x hv) := by
  refine inDomainR_of_r1_r2 _ _ (fun l => hv l) hν ?_ hη hmass
    (fun s hs l => locData_im_eq_zero H g C hjK o x hv hs l)
    (fun s hs l => locData_h_eq H g C hjK o x hv hs l) ?_ ?_
  · rw [parent_sum_sq_eq_norm_sq, hunit]; norm_num
  · intro s s' hp
    exact piece_pair_all H g C hjK ψw o x hv hF1 hF2 hFZ hag
      (fun t t' ht ht' hp' hC hC' hO hO' => hYp t t' ht ht' hp' hC hC' hO hO') hp.1 hp.2.1 hp
  · intro s hs
    exact piece_sphere_all H g C hjK ψw o x hv hF1 hF2 hFZ hag hYs hs

end PieceAssemble

end Balaban.LargeField
